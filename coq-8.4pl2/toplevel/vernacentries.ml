(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Pp
open Util
open Flags
open Names
open Entries
open Nameops
open Term
open Pfedit
open Tacmach
open Constrintern
open Prettyp
open Printer
open Tacinterp
open Command
open Goptions
open Libnames
open Nametab
open Vernacexpr
open Decl_kinds
open Topconstr
open Pretyping
open Redexpr
open Syntax_def
open Lemmas
open Declaremods

(* Pcoq hooks *)

type pcoq_hook = {
  start_proof : unit -> unit;
  solve : int -> unit;
  abort : string -> unit;
  search : searchable -> dir_path list * bool -> unit;
  print_name : reference Genarg.or_by_notation -> unit;
  print_check : Environ.env -> Environ.unsafe_judgment -> unit;
  print_eval : Reductionops.reduction_function -> Environ.env -> Evd.evar_map -> constr_expr ->
    Environ.unsafe_judgment -> unit;
  show_goal : goal_reference -> unit
}

let pcoq = ref None
let set_pcoq_hook f = pcoq := Some f

(* Misc *)

let cl_of_qualid = function
  | FunClass -> Classops.CL_FUN
  | SortClass -> Classops.CL_SORT
  | RefClass r -> Class.class_of_global (Smartlocate.smart_global r)

(*******************)
(* "Show" commands *)

let show_proof () =
  (* spiwack: this would probably be cooler with a bit of polishing. *)
  let p = Proof_global.give_me_the_proof () in
  let pprf = Proof.partial_proof p in
  msgnl (Util.prlist_with_sep Pp.fnl Printer.pr_constr pprf)

let show_node () =
  (* spiwack: I'm have little clue what this function used to do. I deactivated it, 
      could, possibly, be cleaned away. (Feb. 2010) *)
  ()

(* indentation code for Show Script, initially contributed
   by D. de Rauglaudre *)

let indent_script_item ((ng1,ngl1),nl,beginend,ppl) (cmd,ng) =
  (* ng1 : number of goals remaining at the current level (before cmd)
     ngl1 : stack of previous levels with their remaining goals
     ng : number of goals after the execution of cmd
     beginend : special indentation stack for { } *)
  let ngprev = List.fold_left (+) ng1 ngl1 in
  let new_ngl =
    if ng > ngprev then
      (* We've branched *)
      (ng - ngprev + 1, ng1 - 1 :: ngl1)
    else if ng < ngprev then
      (* A subgoal have been solved. Let's compute the new current level
	 by discarding all levels with 0 remaining goals. *)
      let _ = assert (ng = ngprev - 1) in
      let rec loop = function
	| (0, ng2::ngl2) -> loop (ng2,ngl2)
	| p -> p
      in loop (ng1-1, ngl1)
    else
      (* Standard case, same goal number as before *)
      (ng1, ngl1)
  in
  (* When a subgoal have been solved, separate this block by an empty line *)
  let new_nl = (ng < ngprev)
  in
  (* Indentation depth *)
  let ind = List.length ngl1
  in
  (* Some special handling of bullets and { }, to get a nicer display *)
  let pred n = max 0 (n-1) in
  let ind, nl, new_beginend = match cmd with
    | VernacSubproof _ -> pred ind, nl, (pred ind)::beginend
    | VernacEndSubproof -> List.hd beginend, false, List.tl beginend
    | VernacBullet _ -> pred ind, nl, beginend
    | _ -> ind, nl, beginend
  in
  let pp =
    (if nl then fnl () else mt ()) ++
    (hov (ind+1) (str (String.make ind ' ') ++ Ppvernac.pr_vernac cmd))
  in
  (new_ngl, new_nl, new_beginend, pp :: ppl)

let show_script () =
  let prf = Pfedit.get_current_proof_name () in
  let cmds = Backtrack.get_script prf in
  let _,_,_,indented_cmds =
    List.fold_left indent_script_item ((1,[]),false,[],[]) cmds
  in
  let indented_cmds = List.rev (indented_cmds) in
  msgnl (v 0 (Util.prlist_with_sep Pp.fnl (fun x -> x) indented_cmds))

let show_thesis () =
     msgnl (anomaly "TODO" )

let show_top_evars () =
  (* spiwack: new as of Feb. 2010: shows goal evars in addition to non-goal evars. *)
  let pfts = get_pftreestate () in
  let gls = Proof.V82.subgoals pfts in
  let sigma = gls.Evd.sigma in
  msg (pr_evars_int 1 (Evarutil.non_instantiated sigma))
  

let show_prooftree () =
  (* Spiwack: proof tree is currently not working *)
  ()

let enable_goal_printing = ref true

let print_subgoals () =
  if !enable_goal_printing && is_verbose ()
  then msg (pr_open_subgoals ())

let try_print_subgoals () =
  Pp.flush_all();
  try print_subgoals () with Proof_global.NoCurrentProof | UserError _ -> ()


  (* Simulate the Intro(s) tactic *)

let show_intro all =
  let pf = get_pftreestate() in
  let {Evd.it=gls ; sigma=sigma} = Proof.V82.subgoals pf in
  let gl = {Evd.it=List.hd gls ; sigma = sigma} in
  let l,_= decompose_prod_assum (strip_outer_cast (pf_concl gl)) in
  if all
  then
    let lid = Tactics.find_intro_names l gl in
    msgnl (hov 0 (prlist_with_sep  spc pr_id lid))
  else
    try
      let n = list_last l in
      msgnl (pr_id (List.hd (Tactics.find_intro_names [n] gl)))
    with Failure "list_last" -> message ""

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

let make_cases s =
  let qualified_name = Libnames.qualid_of_string s in
  let glob_ref = Nametab.locate qualified_name in
  match glob_ref with
    | Libnames.IndRef i ->
	let {Declarations.mind_nparams = np}
	    , {Declarations.mind_consnames = carr ; Declarations.mind_nf_lc = tarr }
	      = Global.lookup_inductive i in
	Util.array_fold_right2
	  (fun consname typ l ->
	     let al = List.rev (fst (Term.decompose_prod typ)) in
	     let al = Util.list_skipn np al in
	     let rec rename avoid = function
	       | [] -> []
	       | (n,_)::l ->
		   let n' = Namegen.next_name_away_in_cases_pattern n avoid in
		   string_of_id n' :: rename (n'::avoid) l in
	     let al' = rename [] al in
	     (string_of_id consname :: al') :: l)
	  carr tarr []
    | _ -> raise Not_found

(** Textual display of a generic "match" template *)

let show_match id =
  let patterns =
    try make_cases (string_of_id (snd id))
    with Not_found -> error "Unknown inductive type."
  in
  let pr_branch l =
    str "| " ++ hov 1 (prlist_with_sep spc str l) ++ str " =>"
  in
  msg (v 1 (str "match # with" ++ fnl () ++
	    prlist_with_sep fnl pr_branch patterns ++ fnl () ++ str "end" ++ fnl ()))

(* "Print" commands *)

let print_path_entry (s,l) =
  (str (string_of_dirpath l) ++ str " " ++ tbrk (0,0) ++ str s)

let print_loadpath dir =
  let l = Library.get_full_load_paths () in
  let l = match dir with
    | None -> l
    | Some dir -> List.filter (fun (s,l) -> is_dirpath_prefix_of dir l) l in
  msgnl (Pp.t (str "Logical Path:                 " ++
		 tab () ++ str "Physical path:" ++ fnl () ++
		 prlist_with_sep pr_fnl print_path_entry l))

let print_modules () =
  let opened = Library.opened_libraries ()
  and loaded = Library.loaded_libraries () in
  (* we intersect over opened to preserve the order of opened since *)
  (* non-commutative operations (e.g. visibility) are done at import time *)
  let loaded_opened = list_intersect opened loaded
  and only_loaded = list_subtract loaded opened in
  str"Loaded and imported library files: " ++
  pr_vertical_list pr_dirpath loaded_opened ++ fnl () ++
  str"Loaded and not imported library files: " ++
  pr_vertical_list pr_dirpath only_loaded


let print_module r =
  let (loc,qid) = qualid_of_reference r in
  try
    let globdir = Nametab.locate_dir qid in
      match globdir with
	  DirModule (dirpath,(mp,_)) ->
	    msgnl (Printmod.print_module (Printmod.printable_body dirpath) mp)
	| _ -> raise Not_found
  with
      Not_found -> msgnl (str"Unknown Module " ++ pr_qualid qid)

let print_modtype r =
  let (loc,qid) = qualid_of_reference r in
  try
    let kn = Nametab.locate_modtype qid in
    msgnl (Printmod.print_modtype kn)
  with Not_found ->
    (* Is there a module of this name ? If yes we display its type *)
    try
      let mp = Nametab.locate_module qid in
      msgnl (Printmod.print_module false mp)
    with Not_found ->
      msgnl (str"Unknown Module Type or Module " ++ pr_qualid qid)

let dump_universes_gen g s =
  let output = open_out s in
  let output_constraint, close =
    if Filename.check_suffix s ".dot" || Filename.check_suffix s ".gv" then begin
      (* the lazy unit is to handle errors while printing the first line *)
      let init = lazy (Printf.fprintf output "digraph universes {\n") in
      begin fun kind left right ->
        let () = Lazy.force init in
        match kind with
          | Univ.Lt ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=bold];\n" right left
          | Univ.Le ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=solid];\n" right left
          | Univ.Eq ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=dashed];\n" left right
      end, begin fun () ->
        if Lazy.lazy_is_val init then Printf.fprintf output "}\n";
        close_out output
      end
    end else begin
      begin fun kind left right ->
        let kind = match kind with
          | Univ.Lt -> "<"
          | Univ.Le -> "<="
          | Univ.Eq -> "="
        in Printf.fprintf output "%s %s %s ;\n" left kind right
      end, (fun () -> close_out output)
    end
  in
  try
    Univ.dump_universes output_constraint g;
    close ();
    msgnl (str ("Universes written to file \""^s^"\"."))
  with
      reraise -> close (); raise reraise

let dump_universes sorted s =
  let g = Global.universes () in
  let g = if sorted then Univ.sort_universes g else g in
  dump_universes_gen g s

(*********************)
(* "Locate" commands *)

let locate_file f =
  let _,file = System.find_file_in_path ~warn:false (Library.get_load_paths ()) f in
  msgnl (str file)

let msg_found_library = function
  | Library.LibLoaded, fulldir, file ->
      msgnl (hov 0
	(pr_dirpath fulldir ++ strbrk " has been loaded from file " ++
	 str file))
  | Library.LibInPath, fulldir, file ->
      msgnl (hov 0
	(pr_dirpath fulldir ++ strbrk " is bound to file " ++ str file))
let msg_notfound_library loc qid = function
  | Library.LibUnmappedDir ->
      let dir = fst (repr_qualid qid) in
      user_err_loc (loc,"locate_library",
        strbrk "Cannot find a physical path bound to logical path " ++
           pr_dirpath dir ++ str".")
  | Library.LibNotFound ->
      msgnl (hov 0
	(strbrk "Unable to locate library " ++ pr_qualid qid ++ str"."))
  | e -> assert false

let print_located_library r =
  let (loc,qid) = qualid_of_reference r in
  try msg_found_library (Library.locate_qualified_library false qid)
  with e when Errors.noncritical e -> msg_notfound_library loc qid e

let print_located_module r =
  let (loc,qid) = qualid_of_reference r in
  let msg =
    try
      let dir = Nametab.full_name_module qid in
      str "Module " ++ pr_dirpath dir
    with Not_found ->
      (if fst (repr_qualid qid) = empty_dirpath then
	str "No module is referred to by basename "
      else
	str "No module is referred to by name ") ++ pr_qualid qid
  in msgnl msg

let print_located_tactic r =
  let (loc,qid) = qualid_of_reference r in
  msgnl
    (try
      str "Ltac " ++
      pr_path (Nametab.path_of_tactic (Nametab.locate_tactic qid))
     with Not_found ->
	str "No Ltac definition is referred to by " ++ pr_qualid qid)

let smart_global r =
  let gr = Smartlocate.smart_global r in
    Dumpglob.add_glob (Genarg.loc_of_or_by_notation loc_of_reference r) gr;
    gr

let dump_global r =
  try
    let gr = Smartlocate.smart_global r in
    Dumpglob.add_glob (Genarg.loc_of_or_by_notation loc_of_reference r) gr
  with e when Errors.noncritical e -> ()
(**********)
(* Syntax *)

let vernac_syntax_extension = Metasyntax.add_syntax_extension

let vernac_delimiters = Metasyntax.add_delimiters

let vernac_bind_scope sc cll =
  List.iter (fun cl -> Metasyntax.add_class_scope sc (cl_of_qualid cl)) cll

let vernac_open_close_scope = Notation.open_close_scope

let vernac_arguments_scope local r scl =
  Notation.declare_arguments_scope local (smart_global r) scl

let vernac_infix = Metasyntax.add_infix

let vernac_notation = Metasyntax.add_notation

(***********)
(* Gallina *)

let start_proof_and_print k l hook =
  check_locality (); (* early check, cf #2975 *)
  start_proof_com k l hook;
  print_subgoals ();
  if !pcoq <> None then (Option.get !pcoq).start_proof ()

let vernac_definition (local,k) (loc,id as lid) def hook =
  if local = Local then Dumpglob.dump_definition lid true "var"
  else Dumpglob.dump_definition lid false "def";
  (match def with
    | ProveBody (bl,t) ->   (* local binders, typ *)
 	let hook _ _ = () in
 	  start_proof_and_print (local,DefinitionBody Definition)
	    [Some lid, (bl,t,None)] hook
    | DefineBody (bl,red_option,c,typ_opt) ->
 	let red_option = match red_option with
          | None -> None
          | Some r ->
	      let (evc,env)= get_current_context () in
 		Some (snd (interp_redexp env evc r)) in
	let ce,imps = interp_definition bl red_option c typ_opt in
	declare_definition id (local,k) ce imps hook)

let vernac_start_proof kind l lettop hook =
  if Dumpglob.dump () then
    List.iter (fun (id, _) ->
      match id with
	| Some lid -> Dumpglob.dump_definition lid false "prf"
	| None -> ()) l;
  if not(refining ()) then
    if lettop then
      errorlabstrm "Vernacentries.StartProof"
	(str "Let declarations can only be used in proof editing mode.");
  start_proof_and_print (Global, Proof kind) l hook

let qed_display_script = ref true

let vernac_end_proof = function
  | Admitted ->
    Backtrack.mark_unreachable [Pfedit.get_current_proof_name ()];
    admit ()
  | Proved (is_opaque,idopt) ->
    let prf = Pfedit.get_current_proof_name () in
    if is_verbose () && !qed_display_script then (show_script (); msg (fnl()));
    begin match idopt with
    | None -> save_named is_opaque
    | Some ((_,id),None) -> save_anonymous is_opaque id
    | Some ((_,id),Some kind) -> save_anonymous_with_strength kind is_opaque id
    end;
    Backtrack.mark_unreachable [prf]

  (* A stupid macro that should be replaced by ``Exact c. Save.'' all along
     the theories [??] *)

let vernac_exact_proof c =
  (* spiwack: for simplicity I do not enforce that "Proof proof_term" is
     called only at the begining of a proof. *)
  let prf = Pfedit.get_current_proof_name () in
  by (Tactics.exact_proof c);
  save_named true;
  Backtrack.mark_unreachable [prf]

let vernac_assumption kind l nl=
  let global = fst kind = Global in
    List.iter (fun (is_coe,(idl,c)) ->
      if Dumpglob.dump () then
	List.iter (fun lid ->
	  if global then Dumpglob.dump_definition lid false "ax"
	  else Dumpglob.dump_definition lid true "var") idl;
      let t,imps = interp_assumption [] c in
      declare_assumptions idl is_coe kind t imps false nl) l

let vernac_record k finite infer struc binders sort nameopt cfs =
  let const = match nameopt with
    | None -> add_prefix "Build_" (snd (snd struc))
    | Some (_,id as lid) ->
	Dumpglob.dump_definition lid false "constr"; id in
    if Dumpglob.dump () then (
      Dumpglob.dump_definition (snd struc) false "rec";
      List.iter (fun (((_, x), _), _) ->
	match x with
	| Vernacexpr.AssumExpr ((loc, Name id), _) -> Dumpglob.dump_definition (loc,id) false "proj"
	| _ -> ()) cfs);
    ignore(Record.definition_structure (k,finite,infer,struc,binders,cfs,const,sort))

let vernac_inductive finite infer indl =
  if Dumpglob.dump () then
    List.iter (fun (((coe,lid), _, _, _, cstrs), _) ->
      match cstrs with
	| Constructors cstrs ->
	    Dumpglob.dump_definition lid false "ind";
	    List.iter (fun (_, (lid, _)) ->
			 Dumpglob.dump_definition lid false "constr") cstrs
	| _ -> () (* dumping is done by vernac_record (called below) *) )
      indl;
  match indl with
  | [ ( id , bl , c , b, RecordDecl (oc,fs) ), [] ] ->
      vernac_record (match b with Class true -> Class false | _ -> b)
	finite infer id bl c oc fs
  | [ ( id , bl , c , Class true, Constructors [l]), _ ] ->
      let f =
	let (coe, ((loc, id), ce)) = l in
	let coe' = if coe then Some true else None in
	  (((coe', AssumExpr ((loc, Name id), ce)), None), [])
      in vernac_record (Class true) finite infer id bl c None [f]
  | [ ( id , bl , c , Class true, _), _ ] ->
      Util.error "Definitional classes must have a single method"
  | [ ( id , bl , c , Class false, Constructors _), _ ] ->
      Util.error "Inductive classes not supported"
  | [ ( _ , _ , _ , _, RecordDecl _ ) , _ ] ->
      Util.error "where clause not supported for (co)inductive records"
  | _ -> let unpack = function
      | ( (_, id) , bl , c , _ , Constructors l ) , ntn  -> ( id , bl , c , l ) , ntn
      | _ -> Util.error "Cannot handle mutually (co)inductive records."
    in
    let indl = List.map unpack indl in
    do_mutual_inductive indl (recursivity_flag_of_kind finite)

let vernac_fixpoint l =
  if Dumpglob.dump () then
    List.iter (fun ((lid, _, _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  do_fixpoint l

let vernac_cofixpoint l =
  if Dumpglob.dump () then
    List.iter (fun ((lid, _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  do_cofixpoint l

let vernac_scheme l =
  if Dumpglob.dump () then
    List.iter (fun (lid, s) ->
	       Option.iter (fun lid -> Dumpglob.dump_definition lid false "def") lid;
	       match s with
	       | InductionScheme (_, r, _)
	       | CaseScheme (_, r, _) 
	       | EqualityScheme r -> dump_global r) l;
  Indschemes.do_scheme l

let vernac_combined_scheme lid l =
  if Dumpglob.dump () then
    (Dumpglob.dump_definition lid false "def";
     List.iter (fun lid -> dump_global (Genarg.AN (Ident lid))) l);
 Indschemes.do_combined_scheme lid l

(**********************)
(* Modules            *)

let vernac_import export refl =
  let import ref =
    Library.import_module export (qualid_of_reference ref)
  in
    List.iter import refl;
    Lib.add_frozen_state ()

let vernac_declare_module export (loc, id) binders_ast mty_ast =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";
  let binders_ast = List.map
   (fun (export,idl,ty) ->
     if export <> None then
      error ("Arguments of a functor declaration cannot be exported. " ^
       "Remove the \"Export\" and \"Import\" keywords from every functor " ^
       "argument.")
     else (idl,ty)) binders_ast in
  let mp = Declaremods.declare_module
    Modintern.interp_modtype Modintern.interp_modexpr
    Modintern.interp_modexpr_or_modtype
    id binders_ast (Enforce mty_ast) []
  in
    Dumpglob.dump_moddef loc mp "mod";
    if_verbose message ("Module "^ string_of_id id ^" is declared");
    Option.iter (fun export -> vernac_import export [Ident (dummy_loc,id)]) export

let vernac_define_module export (loc, id) binders_ast mty_ast_o mexpr_ast_l =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";
  match mexpr_ast_l with
    | [] ->
       check_no_pending_proofs ();
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun (_,i) -> export,i)idl)@argsexport) binders_ast
             ([],[]) in
       let mp = Declaremods.start_module Modintern.interp_modtype export
	 id binders_ast mty_ast_o
       in
	 Dumpglob.dump_moddef loc mp "mod";
	 if_verbose message
	   ("Interactive Module "^ string_of_id id ^" started") ;
         List.iter
           (fun (export,id) ->
             Option.iter
               (fun export -> vernac_import export [Ident (dummy_loc,id)]) export
           ) argsexport
    | _::_ ->
       let binders_ast = List.map
        (fun (export,idl,ty) ->
          if export <> None then
           error ("Arguments of a functor definition can be imported only if" ^
                  " the definition is interactive. Remove the \"Export\" and " ^
                  "\"Import\" keywords from every functor argument.")
          else (idl,ty)) binders_ast in
       let mp =	Declaremods.declare_module
	  Modintern.interp_modtype Modintern.interp_modexpr
          Modintern.interp_modexpr_or_modtype
	  id binders_ast mty_ast_o mexpr_ast_l
       in
	 Dumpglob.dump_moddef loc mp "mod";
	 if_verbose message
	   ("Module "^ string_of_id id ^" is defined");
         Option.iter (fun export -> vernac_import export [Ident (dummy_loc,id)])
           export

let vernac_end_module export (loc,id as lid) =
  let mp = Declaremods.end_module () in
  Dumpglob.dump_modref loc mp "mod";
  if_verbose message ("Module "^ string_of_id id ^" is defined") ;
  Option.iter (fun export -> vernac_import export [Ident lid]) export

let vernac_declare_module_type (loc,id) binders_ast mty_sign mty_ast_l =
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";

  match mty_ast_l with
    | [] ->
       check_no_pending_proofs ();
       let binders_ast,argsexport =       
	 List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun (_,i) -> export,i)idl)@argsexport) binders_ast
             ([],[]) in
       
       let mp = Declaremods.start_modtype
	 Modintern.interp_modtype id binders_ast mty_sign in
        Dumpglob.dump_moddef loc mp "modtype";
	if_verbose message
	  ("Interactive Module Type "^ string_of_id id ^" started");
        List.iter
         (fun (export,id) ->
           Option.iter
            (fun export -> vernac_import export [Ident (dummy_loc,id)]) export
         ) argsexport

    | _ :: _ ->
	let binders_ast = List.map
          (fun (export,idl,ty) ->
            if export <> None then
              error ("Arguments of a functor definition can be imported only if" ^
			" the definition is interactive. Remove the \"Export\" " ^
			"and \"Import\" keywords from every functor argument.")
            else (idl,ty)) binders_ast in
	let mp = Declaremods.declare_modtype Modintern.interp_modtype
          Modintern.interp_modexpr_or_modtype
	  id binders_ast mty_sign mty_ast_l in
          Dumpglob.dump_moddef loc mp "modtype";
	  if_verbose message
	    ("Module Type "^ string_of_id id ^" is defined")

let vernac_end_modtype (loc,id) =
  let mp = Declaremods.end_modtype () in
  Dumpglob.dump_modref loc mp "modtype";
  if_verbose message ("Module Type "^ string_of_id id ^" is defined")

let vernac_include l =
  Declaremods.declare_include Modintern.interp_modexpr_or_modtype l

(**********************)
(* Gallina extensions *)

(* Sections *)

let vernac_begin_section (_, id as lid) =
  check_no_pending_proofs ();
  Dumpglob.dump_definition lid true "sec";
  Lib.open_section id

let vernac_end_section (loc,_) =
  Dumpglob.dump_reference loc
    (string_of_dirpath (Lib.current_dirpath true)) "<>" "sec";
  Lib.close_section ()

(* Dispatcher of the "End" command *)

let vernac_end_segment (_,id as lid) =
  check_no_pending_proofs ();
  match Lib.find_opening_node id with
  | Lib.OpenedModule (false,export,_,_) -> vernac_end_module export lid
  | Lib.OpenedModule (true,_,_,_) -> vernac_end_modtype lid
  | Lib.OpenedSection _ -> vernac_end_section lid
  | _ -> assert false

(* Libraries *)

let vernac_require import _ qidl =
  let qidl = List.map qualid_of_reference qidl in
  let modrefl = Flags.silently (List.map Library.try_locate_qualified_library) qidl in
  if Dumpglob.dump () then
    List.iter2 (fun (loc, _) dp -> Dumpglob.dump_libref loc dp "lib") qidl (List.map fst modrefl);
  Library.require_library_from_dirpath modrefl import

(* Coercions and canonical structures *)

let vernac_canonical r =
  Recordops.declare_canonical_structure (smart_global r)

let vernac_coercion stre ref qids qidt =
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  let ref' = smart_global ref in
  Class.try_add_new_coercion_with_target ref' stre ~source ~target;
  if_verbose msgnl (pr_global ref' ++ str " is now a coercion")

let vernac_identity_coercion stre id qids qidt =
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  Class.try_add_new_identity_coercion id stre ~source ~target

(* Type classes *)

let vernac_instance abst glob sup inst props pri =
  Dumpglob.dump_constraint inst false "inst";
  ignore(Classes.new_instance ~abstract:abst ~global:glob sup inst props pri)

let vernac_context l =
  Classes.context l

let vernac_declare_instances glob ids =
  List.iter (fun (id) -> Classes.existing_instance glob id) ids

let vernac_declare_class id =
  Classes.declare_class id

(***********)
(* Solving *)

let command_focus = Proof.new_focus_kind ()
let focus_command_cond = Proof.no_cond command_focus


let vernac_solve n tcom b =
  if not (refining ()) then
    error "Unknown command of the non proof-editing mode.";
  let p = Proof_global.give_me_the_proof () in
  Proof.transaction p begin fun () ->
    solve_nth n (Tacinterp.hide_interp tcom None) ~with_end_tac:b;
    (* in case a strict subtree was completed,
       go back to the top of the prooftree *)
    Proof_global.maximal_unfocus command_focus p;
    print_subgoals();
    if !pcoq <> None then (Option.get !pcoq).solve n
  end
 

  (* A command which should be a tactic. It has been
     added by Christine to patch an error in the design of the proof
     machine, and enables to instantiate existential variables when
     there are no more goals to solve. It cannot be a tactic since
     all tactics fail if there are no further goals to prove. *)

let vernac_solve_existential = instantiate_nth_evar_com

let vernac_set_end_tac tac =
  if not (refining ()) then
    error "Unknown command of the non proof-editing mode.";
  if tac <> (Tacexpr.TacId []) then set_end_tac (Tacinterp.interp tac) else ()
    (* TO DO verifier s'il faut pas mettre exist s | TacId s ici*)

let vernac_set_used_variables l =
  let l = List.map snd l in
  if not (list_distinct l) then error "Used variables list contains duplicates";
  let vars = Environ.named_context (Global.env ()) in
  List.iter (fun id -> 
    if not (List.exists (fun (id',_,_) -> id = id') vars) then
      error ("Unknown variable: " ^ string_of_id id))
    l;
  set_used_variables l

(*****************************)
(* Auxiliary file management *)

let vernac_require_from export spec filename =
  Library.require_library_from_file None
    (System.expand_path_macros filename)
    export

let vernac_add_loadpath isrec pdir ldiropt =
  let pdir = System.expand_path_macros pdir in
  let alias = match ldiropt with
    | None -> Nameops.default_root_prefix
    | Some ldir -> ldir in
  (if isrec then Mltop.add_rec_path else Mltop.add_path) ~unix_path:pdir ~coq_root:alias

let vernac_remove_loadpath path =
  Library.remove_load_path (System.expand_path_macros path)

  (* Coq syntax for ML or system commands *)

let vernac_add_ml_path isrec path =
  (if isrec then Mltop.add_rec_ml_dir else Mltop.add_ml_dir)
    (System.expand_path_macros path)

let vernac_declare_ml_module local l =
  Mltop.declare_ml_modules local (List.map System.expand_path_macros l)

let vernac_chdir = function
  | None -> message (Sys.getcwd())
  | Some path ->
      begin
	try Sys.chdir (System.expand_path_macros path)
	with Sys_error str -> warning ("Cd failed: " ^ str)
      end;
      if_verbose message (Sys.getcwd())


(********************)
(* State management *)

let vernac_write_state file =
  Pfedit.delete_all_proofs ();
  States.extern_state file

let vernac_restore_state file =
  Pfedit.delete_all_proofs ();
  States.intern_state file

(************)
(* Commands *)

let vernac_declare_tactic_definition (local,x,def) =
  Tacinterp.add_tacdef local x def

let vernac_create_hintdb local id b =
  Auto.create_hint_db local id full_transparent_state b

let vernac_remove_hints local dbs ids =
  Auto.remove_hints local dbs (List.map Smartlocate.global_with_alias ids)

let vernac_hints local lb h =
  Auto.add_hints local lb (Auto.interp_hints h)

let vernac_syntactic_definition lid =
  Dumpglob.dump_definition lid false "syndef";
  Metasyntax.add_syntactic_definition (snd lid)

let vernac_declare_implicits local r = function
  | [] ->
      Impargs.declare_implicits local (smart_global r)
  | _::_ as imps ->
      Impargs.declare_manual_implicits local (smart_global r) ~enriching:false
	(List.map (List.map (fun (ex,b,f) -> ex, (b,true,f))) imps)

let vernac_declare_arguments local r l nargs flags =
  let extra_scope_flag = List.mem `ExtraScopes flags in
  let names = List.map (List.map (fun (id, _,_,_,_) -> id)) l in
  let names, rest = List.hd names, List.tl names in
  let scopes = List.map (List.map (fun (_,_, s, _,_) -> s)) l in
  if List.exists ((<>) names) rest then
    error "All arguments lists must declare the same names.";
  if not (Util.list_distinct (List.filter ((<>) Anonymous) names)) then
    error "Arguments names must be distinct.";
  let sr = smart_global r in
  let inf_names =
    Impargs.compute_implicits_names (Global.env()) (Global.type_of_global sr) in
  let string_of_name = function Anonymous -> "_" | Name id -> string_of_id id in
  let rec check li ld ls = match li, ld, ls with
    | [], [], [] -> ()
    | [], Anonymous::ld, (Some _)::ls when extra_scope_flag -> check li ld ls
    | [], _::_, (Some _)::ls when extra_scope_flag ->
       error "Extra notation scopes can be set on anonymous arguments only"
    | [], x::_, _ -> error ("Extra argument " ^ string_of_name x ^ ".")
    | l, [], _ -> error ("The following arguments are not declared: " ^
       (String.concat ", " (List.map string_of_name l)) ^ ".")
    | _::li, _::ld, _::ls -> check li ld ls 
    | _ -> assert false in
  if l <> [[]] then
    List.iter2 (fun l -> check inf_names l) (names :: rest) scopes;
  (* we take extra scopes apart, and we check they are consistent *)
  let l, scopes = 
    let scopes, rest = List.hd scopes, List.tl scopes in
    if List.exists (List.exists ((<>) None)) rest then
      error "Notation scopes can be given only once";
    if not extra_scope_flag then l, scopes else
    let l, _ = List.split (List.map (list_chop (List.length inf_names)) l) in
    l, scopes in
  (* we interpret _ as the inferred names *)
  let l = if l = [[]] then l else
    let name_anons = function
      | (Anonymous, a,b,c,d), Name id -> Name id, a,b,c,d
      | x, _ -> x in
    List.map (fun ns -> List.map name_anons (List.combine ns inf_names)) l in
  let names_decl = List.map (List.map (fun (id, _,_,_,_) -> id)) l in
  let some_renaming_specified =
    try Arguments_renaming.arguments_names sr <> names_decl
    with Not_found -> false in
  let some_renaming_specified, implicits =
    if l = [[]] then false, [[]] else
    Util.list_fold_map (fun sr il ->
      let sr', impl = Util.list_fold_map (fun b -> function
        | (Anonymous, _,_, true, max), Name id -> assert false
        | (Name x, _,_, true, _), Anonymous ->
            error ("Argument "^string_of_id x^" cannot be declared implicit.")
        | (Name iid, _,_, true, max), Name id ->
           b || iid <> id, Some (ExplByName id, max, false)
        | (Name iid, _,_, _, _), Name id -> b || iid <> id, None
        | _ -> b, None)
        sr (List.combine il inf_names) in
      sr || sr', Util.list_map_filter (fun x -> x) impl)
      some_renaming_specified l in
  if some_renaming_specified then
    if not (List.mem `Rename flags) then
      error "To rename arguments the \"rename\" flag must be specified."
    else Arguments_renaming.rename_arguments local sr names_decl;
  (* All other infos are in the first item of l *)
  let l = List.hd l in
  let some_implicits_specified = implicits <> [[]] in
  let scopes = List.map (function
    | None -> None
    | Some (o, k) -> 
        try Some(ignore(Notation.find_scope k); k)
        with e when Errors.noncritical e ->
          Some (Notation.find_delimiters_scope o k)) scopes
  in
  let some_scopes_specified = List.exists ((<>) None) scopes in
  let rargs =
    Util.list_map_filter (function (n, true) -> Some n | _ -> None)
      (Util.list_map_i (fun i (_, b, _,_,_) -> i, b) 0 l) in
  if some_scopes_specified || List.mem `ClearScopes flags then
    vernac_arguments_scope local r scopes;
  if not some_implicits_specified && List.mem `DefaultImplicits flags then
    vernac_declare_implicits local r []
  else if some_implicits_specified || List.mem `ClearImplicits flags then
    vernac_declare_implicits local r implicits;
  if nargs >= 0 && nargs < List.fold_left max 0 rargs then
    error "The \"/\" option must be placed after the last \"!\".";
  let rec narrow = function
    | #Tacred.simpl_flag as x :: tl -> x :: narrow tl
    | [] -> [] | _ :: tl -> narrow tl in
  let flags = narrow flags in
  if rargs <> [] || nargs >= 0 || flags <> [] then
    match sr with
    | ConstRef _ as c ->
       Tacred.set_simpl_behaviour local c (rargs, nargs, flags)
    | _ -> errorlabstrm "" (strbrk "Modifiers of the behavior of the simpl tactic are relevant for constants only.")

let vernac_reserve bl =
  let sb_decl = (fun (idl,c) ->
    let t = Constrintern.interp_type Evd.empty (Global.env()) c in
    let t = Detyping.detype false [] [] t in
    let t = aconstr_of_glob_constr [] [] t in
    Reserve.declare_reserved_type idl t)
  in List.iter sb_decl bl

let vernac_generalizable = Implicit_quantifiers.declare_generalizable

let make_silent_if_not_pcoq b =
  if !pcoq <> None then
    error "Turning on/off silent flag is not supported in Pcoq mode."
  else make_silent b

let _ =
  declare_bool_option
    { optsync  = false;
      optdepr  = false;
      optname  = "silent";
      optkey   = ["Silent"];
      optread  = is_silent;
      optwrite = make_silent_if_not_pcoq }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit arguments";
      optkey   = ["Implicit";"Arguments"];
      optread  = Impargs.is_implicit_args;
      optwrite = Impargs.make_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "strict implicit arguments";
      optkey   = ["Strict";"Implicit"];
      optread  = Impargs.is_strict_implicit_args;
      optwrite = Impargs.make_strict_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "strong strict implicit arguments";
      optkey   = ["Strongly";"Strict";"Implicit"];
      optread  = Impargs.is_strongly_strict_implicit_args;
      optwrite = Impargs.make_strongly_strict_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "contextual implicit arguments";
      optkey   = ["Contextual";"Implicit"];
      optread  = Impargs.is_contextual_implicit_args;
      optwrite = Impargs.make_contextual_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit status of reversible patterns";
      optkey   = ["Reversible";"Pattern";"Implicit"];
      optread  = Impargs.is_reversible_pattern_implicit_args;
      optwrite = Impargs.make_reversible_pattern_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "maximal insertion of implicit";
      optkey   = ["Maximal";"Implicit";"Insertion"];
      optread  = Impargs.is_maximal_implicit_args;
      optwrite = Impargs.make_maximal_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "automatic introduction of variables";
      optkey   = ["Automatic";"Introduction"];
      optread  = Flags.is_auto_intros;
      optwrite = make_auto_intros }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "coercion printing";
      optkey   = ["Printing";"Coercions"];
      optread  = (fun () -> !Constrextern.print_coercions);
      optwrite = (fun b ->  Constrextern.print_coercions := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "printing of existential variable instances";
      optkey   = ["Printing";"Existential";"Instances"];
      optread  = (fun () -> !Constrextern.print_evar_arguments);
      optwrite = (:=) Constrextern.print_evar_arguments }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit arguments printing";
      optkey   = ["Printing";"Implicit"];
      optread  = (fun () -> !Constrextern.print_implicits);
      optwrite = (fun b ->  Constrextern.print_implicits := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit arguments defensive printing";
      optkey   = ["Printing";"Implicit";"Defensive"];
      optread  = (fun () -> !Constrextern.print_implicits_defensive);
      optwrite = (fun b ->  Constrextern.print_implicits_defensive := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "projection printing using dot notation";
      optkey   = ["Printing";"Projections"];
      optread  = (fun () -> !Constrextern.print_projections);
      optwrite = (fun b ->  Constrextern.print_projections := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "notations printing";
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "raw printing";
      optkey   = ["Printing";"All"];
      optread  = (fun () -> !Flags.raw_print);
      optwrite = (fun b -> Flags.raw_print := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "record printing";
      optkey   = ["Printing";"Records"];
      optread  = (fun () -> !Flags.record_print);
      optwrite = (fun b -> Flags.record_print := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "use of virtual machine inside the kernel";
      optkey   = ["Virtual";"Machine"];
      optread  = (fun () -> Vconv.use_vm ());
      optwrite = (fun b -> Vconv.set_use_vm b) }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "the level of inling duging functor application";
      optkey   = ["Inline";"Level"];
      optread  = (fun () -> Some (Flags.get_inline_level ()));
      optwrite = (fun o ->
	           let lev = Option.default Flags.default_inline_level o in
	           Flags.set_inline_level lev) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "use of boxed values";
      optkey   = ["Boxed";"Values"];
      optread  = (fun _ -> not (Vm.transp_values ()));
      optwrite = (fun b -> Vm.set_transp_values (not b)) }

(* No more undo limit in the new proof engine.
   The command still exists for compatibility (e.g. with ProofGeneral) *)

let _ =
  declare_int_option
    { optsync  = false;
      optdepr  = true;
      optname  = "the undo limit (OBSOLETE)";
      optkey   = ["Undo"];
      optread  = (fun _ -> None);
      optwrite = (fun _ -> ()) }

let _ =
  declare_int_option
    { optsync  = false;
      optdepr  = false;
      optname  = "the hypotheses limit";
      optkey   = ["Hyps";"Limit"];
      optread  = Flags.print_hyps_limit;
      optwrite = Flags.set_print_hyps_limit }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "the printing depth";
      optkey   = ["Printing";"Depth"];
      optread  = Pp_control.get_depth_boxes;
      optwrite = Pp_control.set_depth_boxes }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "the printing width";
      optkey   = ["Printing";"Width"];
      optread  = Pp_control.get_margin;
      optwrite = Pp_control.set_margin }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "printing of universes";
      optkey   = ["Printing";"Universes"];
      optread  = (fun () -> !Constrextern.print_universes);
      optwrite = (fun b -> Constrextern.print_universes:=b) }

let vernac_debug b =
  set_debug (if b then Tactic_debug.DebugOn 0 else Tactic_debug.DebugOff)

let _ =
  declare_bool_option
    { optsync  = false;
      optdepr  = false;
      optname  = "Ltac debug";
      optkey   = ["Ltac";"Debug"];
      optread  = (fun () -> get_debug () <> Tactic_debug.DebugOff);
      optwrite = vernac_debug }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "explicitly parsing implicit arguments";
      optkey   = ["Parsing";"Explicit"];
      optread  = (fun () -> !Constrintern.parsing_explicit);
      optwrite = (fun b ->  Constrintern.parsing_explicit := b) }

let vernac_set_opacity local str =
  let glob_ref r =
    match smart_global r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> error
          "cannot set an inductive type or a constructor as transparent" in
  let str = List.map (fun (lev,ql) -> (lev,List.map glob_ref ql)) str in
  Redexpr.set_strategy local str

let vernac_set_option locality key = function
  | StringValue s -> set_string_option_value_gen locality key s
  | IntValue n -> set_int_option_value_gen locality key n
  | BoolValue b -> set_bool_option_value_gen locality key b

let vernac_unset_option locality key =
  unset_option_value_gen locality key

let vernac_add_option key lv =
  let f = function
    | StringRefValue s -> (get_string_table key)#add s
    | QualidRefValue locqid -> (get_ref_table key)#add locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_remove_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key)#remove s
  | QualidRefValue locqid -> (get_ref_table key)#remove locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_mem_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key)#mem s
  | QualidRefValue locqid -> (get_ref_table key)#mem locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_print_option key =
  try (get_ref_table key)#print
  with Not_found ->
  try (get_string_table key)#print
  with Not_found ->
  try print_option_value key
  with Not_found -> error_undeclared_key key

let get_current_context_of_args = function
  | Some n -> get_goal_context n
  | None -> get_current_context ()

let vernac_check_may_eval redexp glopt rc =
  let module P = Pretype_errors in
  let (sigma, env) = get_current_context_of_args glopt in
  let sigma', c = interp_open_constr sigma env rc in
  let sigma' = Evarconv.consider_remaining_unif_problems env sigma' in
  let j =
    try
      Evarutil.check_evars env sigma sigma' c;
      Arguments_renaming.rename_typing env c
    with P.PretypeError (_,_,P.UnsolvableImplicit _)
      | Compat.Loc.Exc_located (_,P.PretypeError (_,_,P.UnsolvableImplicit _)) ->
      Evarutil.j_nf_evar sigma' (Retyping.get_judgment_of env sigma' c) in
  match redexp with
    | None ->
	if !pcoq <> None then (Option.get !pcoq).print_check env j
	else msg (print_judgment env j)
    | Some r ->
        Tacinterp.dump_glob_red_expr r;
        let (sigma',r_interp) = interp_redexp env sigma' r in
	let redfun = fst (reduction_of_red_expr r_interp) in
	if !pcoq <> None
	then (Option.get !pcoq).print_eval redfun env sigma' rc j
	else msg (print_eval redfun env sigma' rc j)

let vernac_declare_reduction locality s r =
  declare_red_expr locality s (snd (interp_redexp (Global.env()) Evd.empty r))

  (* The same but avoiding the current goal context if any *)
let vernac_global_check c =
  let evmap = Evd.empty in
  let env = Global.env() in
  let c = interp_constr evmap env c in
  let senv = Global.safe_env() in
  let j = Safe_typing.typing senv c in
  msg (print_safe_judgment env j)

let vernac_print = function
  | PrintTables -> print_tables ()
  | PrintFullContext-> msg (print_full_context_typ ())
  | PrintSectionContext qid -> msg (print_sec_context_typ qid)
  | PrintInspect n -> msg (inspect n)
  | PrintGrammar ent -> Metasyntax.print_grammar ent
  | PrintLoadPath dir -> (* For compatibility ? *) print_loadpath dir
  | PrintModules -> msg (print_modules ())
  | PrintModule qid -> print_module qid
  | PrintModuleType qid -> print_modtype qid
  | PrintMLLoadPath -> Mltop.print_ml_path ()
  | PrintMLModules -> Mltop.print_ml_modules ()
  | PrintName qid ->
      if !pcoq <> None then (Option.get !pcoq).print_name qid
      else msg (print_name qid)
  | PrintGraph -> ppnl (Prettyp.print_graph())
  | PrintClasses -> ppnl (Prettyp.print_classes())
  | PrintTypeClasses -> ppnl (Prettyp.print_typeclasses())
  | PrintInstances c -> ppnl (Prettyp.print_instances (smart_global c))
  | PrintLtac qid -> ppnl (Tacinterp.print_ltac (snd (qualid_of_reference qid)))
  | PrintCoercions -> ppnl (Prettyp.print_coercions())
  | PrintCoercionPaths (cls,clt) ->
      ppnl (Prettyp.print_path_between (cl_of_qualid cls) (cl_of_qualid clt))
  | PrintCanonicalConversions -> ppnl (Prettyp.print_canonical_projections ())
  | PrintUniverses (b, None) ->
    let univ = Global.universes () in
    let univ = if b then Univ.sort_universes univ else univ in
    pp (Univ.pr_universes univ)
  | PrintUniverses (b, Some s) -> dump_universes b s
  | PrintHint r -> Auto.print_hint_ref (smart_global r)
  | PrintHintGoal -> Auto.print_applicable_hint ()
  | PrintHintDbName s -> Auto.print_hint_db_by_name s
  | PrintRewriteHintDbName s -> Autorewrite.print_rewrite_hintdb s
  | PrintHintDb -> Auto.print_searchtable ()
  | PrintScopes ->
      pp (Notation.pr_scopes (Constrextern.without_symbols pr_lglob_constr))
  | PrintScope s ->
      pp (Notation.pr_scope (Constrextern.without_symbols pr_lglob_constr) s)
  | PrintVisibility s ->
      pp (Notation.pr_visibility (Constrextern.without_symbols pr_lglob_constr) s)
  | PrintAbout qid -> 
    msg (print_about qid)
  | PrintImplicit qid -> 
    dump_global qid; msg (print_impargs qid)
  | PrintAssumptions (o,r) ->
      (* Prints all the axioms and section variables used by a term *)
      let cstr = constr_of_global (smart_global r) in
      let st = Conv_oracle.get_transp_state () in
      let nassums = Assumptions.assumptions st ~add_opaque:o cstr in
      msg (Printer.pr_assumptionset (Global.env ()) nassums)

let global_module r =
  let (loc,qid) = qualid_of_reference r in
  try Nametab.full_name_module qid
  with Not_found ->
    user_err_loc (loc, "global_module",
      str "Module/section " ++ pr_qualid qid ++ str " not found.")

let interp_search_restriction = function
  | SearchOutside l -> (List.map global_module l, true)
  | SearchInside l -> (List.map global_module l, false)

open Search

let is_ident s = try ignore (check_ident s); true with UserError _ -> false

let interp_search_about_item = function
  | SearchSubPattern pat ->
      let _,pat = intern_constr_pattern Evd.empty (Global.env()) pat in
      GlobSearchSubPattern pat
  | SearchString (s,None) when is_ident s ->
      GlobSearchString s
  | SearchString (s,sc) ->
      try
	let ref =
	  Notation.interp_notation_as_global_reference dummy_loc
	    (fun _ -> true) s sc in
	GlobSearchSubPattern (Pattern.PRef ref)
      with UserError _ ->
	error ("Unable to interp \""^s^"\" either as a reference or \
          	as an identifier component")

let vernac_search s r =
  let r = interp_search_restriction r in
  if !pcoq <> None then (Option.get !pcoq).search s r else
  match s with
  | SearchPattern c ->
      let (_,c) = interp_open_constr_patvar Evd.empty (Global.env()) c in
      Search.search_pattern c r
  | SearchRewrite c ->
      let _,pat = interp_open_constr_patvar Evd.empty (Global.env()) c in
      Search.search_rewrite pat r
  | SearchHead c ->
      let _,pat = interp_open_constr_patvar Evd.empty (Global.env()) c in
      Search.search_by_head pat r
  | SearchAbout sl ->
      Search.search_about (List.map (on_snd interp_search_about_item) sl) r

let vernac_locate = function
  | LocateTerm (Genarg.AN qid) -> msgnl (print_located_qualid qid)
  | LocateTerm (Genarg.ByNotation (_,ntn,sc)) ->
      ppnl
        (Notation.locate_notation
          (Constrextern.without_symbols pr_lglob_constr) ntn sc)
  | LocateLibrary qid -> print_located_library qid
  | LocateModule qid -> print_located_module qid
  | LocateTactic qid -> print_located_tactic qid
  | LocateFile f -> locate_file f

(****************)
(* Backtracking *)

(** NB: these commands are now forbidden in non-interactive use,
    e.g. inside VernacLoad, VernacList, ... *)

let vernac_backto lbl =
  try
    let lbl' = Backtrack.backto lbl in
    if lbl <> lbl' then
      Pp.msg_warning
	(str "Actually back to state "++ Pp.int lbl' ++ str ".");
    try_print_subgoals ()
  with Backtrack.Invalid -> error "Invalid backtrack."

let vernac_back n =
  try
    let extra = Backtrack.back n in
    if extra <> 0 then
      Pp.msg_warning
	(str "Actually back by " ++ Pp.int (extra+n) ++ str " steps.");
    try_print_subgoals ()
  with Backtrack.Invalid -> error "Invalid backtrack."

let vernac_reset_name id =
  try
    let globalized =
      try
	let gr = Smartlocate.global_with_alias (Ident id) in
	Dumpglob.add_glob (fst id) gr;
	true
      with e when Errors.noncritical e -> false in

    if not globalized then begin
       try begin match Lib.find_opening_node (snd id) with
          | Lib.OpenedSection _ -> Dumpglob.dump_reference (fst id)
              (string_of_dirpath (Lib.current_dirpath true)) "<>" "sec";
          (* Might be nice to implement module cases, too.... *)
          | _ -> ()
       end with UserError _ -> ()
    end;

    if Backtrack.is_active () then
      (Backtrack.reset_name id; try_print_subgoals ())
    else
      (* When compiling files, Reset is now allowed again
	 as asked by A. Chlipala. we emulate a simple reset,
	 that discards all proofs. *)
      let lbl = Lib.label_before_name id in
      Pfedit.delete_all_proofs ();
      Pp.msg_warning (str "Reset command occurred in non-interactive mode.");
      Lib.reset_label lbl
  with Backtrack.Invalid | Not_found -> error "Invalid Reset."


let vernac_reset_initial () =
  if Backtrack.is_active () then
    Backtrack.reset_initial ()
  else begin
    Pp.msg_warning (str "Reset command occurred in non-interactive mode.");
    Lib.reset_label Lib.first_command_label
  end

(* For compatibility with ProofGeneral: *)

let vernac_backtrack snum pnum naborts =
  Backtrack.backtrack snum pnum naborts;
  try_print_subgoals ()


(********************)
(* Proof management *)

let vernac_abort = function
  | None ->
      Backtrack.mark_unreachable [Pfedit.get_current_proof_name ()];
      delete_current_proof ();
      if_verbose message "Current goal aborted";
      if !pcoq <> None then (Option.get !pcoq).abort ""
  | Some id ->
      Backtrack.mark_unreachable [snd id];
      delete_proof id;
      let s = string_of_id (snd id) in
      if_verbose message ("Goal "^s^" aborted");
      if !pcoq <> None then (Option.get !pcoq).abort s

let vernac_abort_all () =
  if refining() then begin
    Backtrack.mark_unreachable (Pfedit.get_all_proof_names ());
    delete_all_proofs ();
    message "Current goals aborted"
  end else
    error "No proof-editing in progress."

let vernac_restart () =
  Backtrack.mark_unreachable [Pfedit.get_current_proof_name ()];
  restart_proof(); print_subgoals ()

let vernac_undo n =
  let d = Pfedit.current_proof_depth () - n in
  Backtrack.mark_unreachable ~after:d [Pfedit.get_current_proof_name ()];
  Pfedit.undo n; print_subgoals ()

let vernac_undoto n =
  Backtrack.mark_unreachable ~after:n [Pfedit.get_current_proof_name ()];
  Pfedit.undo_todepth n;
  print_subgoals ()

let vernac_focus gln =
  let p = Proof_global.give_me_the_proof () in
  let n = match gln with None -> 1 | Some n -> n in
  if n = 0 then
    Util.error "Invalid goal number: 0. Goal numbering starts with 1."
  else
    Proof.focus focus_command_cond () n p; print_subgoals ()

  (* Unfocuses one step in the focus stack. *)
let vernac_unfocus () =
  let p = Proof_global.give_me_the_proof () in
  Proof.unfocus command_focus p; print_subgoals ()

(* Checks that a proof is fully unfocused. Raises an error if not. *)
let vernac_unfocused () =
  let p = Proof_global.give_me_the_proof () in
  if Proof.unfocused p then
    msg (str"The proof is indeed fully unfocused.")
  else
    error "The proof is not fully unfocused."


(* BeginSubproof / EndSubproof. 
    BeginSubproof (vernac_subproof) focuses on the first goal, or the goal
    given as argument.
    EndSubproof (vernac_end_subproof) unfocuses from a BeginSubproof, provided
    that the proof of the goal has been completed.
*)
let subproof_kind = Proof.new_focus_kind ()
let subproof_cond = Proof.done_cond subproof_kind

let vernac_subproof gln =
  let p = Proof_global.give_me_the_proof () in
  begin match gln with
  | None -> Proof.focus subproof_cond () 1 p
  | Some n -> Proof.focus subproof_cond () n p
  end ;
  print_subgoals ()

let vernac_end_subproof () =
  let p = Proof_global.give_me_the_proof () in
  Proof.unfocus subproof_kind p ; print_subgoals ()


let vernac_bullet (bullet:Proof_global.Bullet.t) =
  let p = Proof_global.give_me_the_proof () in
  Proof.transaction p 
    (fun () -> Proof_global.Bullet.put p bullet);
  (* Makes the focus visible in emacs by re-printing the goal. *)
  if !Flags.print_emacs then print_subgoals ()


let vernac_show = function
  | ShowGoal goalref ->
      if !pcoq <> None then (Option.get !pcoq).show_goal goalref
      else msg (match goalref with
	| OpenSubgoals -> pr_open_subgoals ()
	| NthGoal n -> pr_nth_open_subgoal n
        | GoalId id -> pr_goal_by_id id)
  | ShowGoalImplicitly None ->
      Constrextern.with_implicits msg (pr_open_subgoals ())
  | ShowGoalImplicitly (Some n) ->
      Constrextern.with_implicits msg (pr_nth_open_subgoal n)
  | ShowProof -> show_proof ()
  | ShowNode -> show_node ()
  | ShowScript -> show_script ()
  | ShowExistentials -> show_top_evars ()
  | ShowTree -> show_prooftree ()
  | ShowProofNames ->
      msgnl (prlist_with_sep pr_spc pr_id (Pfedit.get_all_proof_names()))
  | ShowIntros all -> show_intro all
  | ShowMatch id -> show_match id
  | ShowThesis -> show_thesis ()


let vernac_check_guard () =
  let pts = get_pftreestate () in
  let pfterm = List.hd (Proof.partial_proof pts) in
  let message =
    try
      let { Evd.it=gl ; sigma=sigma } = Proof.V82.top_goal pts in
      Inductiveops.control_only_guard (Goal.V82.env sigma gl)
	pfterm;
      (str "The condition holds up to here")
    with UserError(_,s) ->
      (str ("Condition violated: ") ++s)
  in
  msgnl message

let interp c = match c with
  (* Control (done in vernac) *)
  | (VernacTime _|VernacList _|VernacLoad _|VernacTimeout _|VernacFail _) ->
      assert false

  (* Syntax *)
  | VernacTacticNotation (n,r,e) -> Metasyntax.add_tactic_notation (n,r,e)
  | VernacSyntaxExtension (lcl,sl) -> vernac_syntax_extension lcl sl
  | VernacDelimiters (sc,lr) -> vernac_delimiters sc lr
  | VernacBindScope (sc,rl) -> vernac_bind_scope sc rl
  | VernacOpenCloseScope sc -> vernac_open_close_scope sc
  | VernacArgumentsScope (lcl,qid,scl) -> vernac_arguments_scope lcl qid scl
  | VernacInfix (local,mv,qid,sc) -> vernac_infix local mv qid sc
  | VernacNotation (local,c,infpl,sc) -> vernac_notation local c infpl sc

  (* Gallina *)
  | VernacDefinition (k,lid,d,f) -> vernac_definition k lid d f
  | VernacStartTheoremProof (k,l,top,f) -> vernac_start_proof k l top f
  | VernacEndProof e -> vernac_end_proof e
  | VernacExactProof c -> vernac_exact_proof c
  | VernacAssumption (stre,nl,l) -> vernac_assumption stre l nl
  | VernacInductive (finite,infer,l) -> vernac_inductive finite infer l
  | VernacFixpoint l -> vernac_fixpoint l
  | VernacCoFixpoint l -> vernac_cofixpoint l
  | VernacScheme l -> vernac_scheme l
  | VernacCombinedScheme (id, l) -> vernac_combined_scheme id l

  (* Modules *)
  | VernacDeclareModule (export,lid,bl,mtyo) ->
      vernac_declare_module export lid bl mtyo
  | VernacDefineModule (export,lid,bl,mtys,mexprl) ->
      vernac_define_module export lid bl mtys mexprl
  | VernacDeclareModuleType (lid,bl,mtys,mtyo) ->
      vernac_declare_module_type lid bl mtys mtyo
  | VernacInclude in_asts ->
      vernac_include in_asts
  (* Gallina extensions *)
  | VernacBeginSection lid -> vernac_begin_section lid

  | VernacEndSegment lid -> vernac_end_segment lid

  | VernacRequire (export,spec,qidl) -> vernac_require export spec qidl
  | VernacImport (export,qidl) -> vernac_import export qidl
  | VernacCanonical qid -> vernac_canonical qid
  | VernacCoercion (str,r,s,t) -> vernac_coercion str r s t
  | VernacIdentityCoercion (str,(_,id),s,t) -> vernac_identity_coercion str id s t

  (* Type classes *)
  | VernacInstance (abst, glob, sup, inst, props, pri) ->
      vernac_instance abst glob sup inst props pri
  | VernacContext sup -> vernac_context sup
  | VernacDeclareInstances (glob, ids) -> vernac_declare_instances glob ids
  | VernacDeclareClass id -> vernac_declare_class id

  (* Solving *)
  | VernacSolve (n,tac,b) -> vernac_solve n tac b
  | VernacSolveExistential (n,c) -> vernac_solve_existential n c

  (* Auxiliary file and library management *)
  | VernacRequireFrom (exp,spec,f) -> vernac_require_from exp spec f
  | VernacAddLoadPath (isrec,s,alias) -> vernac_add_loadpath isrec s alias
  | VernacRemoveLoadPath s -> vernac_remove_loadpath s
  | VernacAddMLPath (isrec,s) -> vernac_add_ml_path isrec s
  | VernacDeclareMLModule (local, l) -> vernac_declare_ml_module local l
  | VernacChdir s -> vernac_chdir s

  (* State management *)
  | VernacWriteState s -> vernac_write_state s
  | VernacRestoreState s -> vernac_restore_state s

  (* Resetting *)
  | VernacResetName id -> vernac_reset_name id
  | VernacResetInitial -> vernac_reset_initial ()
  | VernacBack n -> vernac_back n
  | VernacBackTo n -> vernac_backto n

  (* Commands *)
  | VernacDeclareTacticDefinition def -> vernac_declare_tactic_definition def
  | VernacCreateHintDb (local,dbname,b) -> vernac_create_hintdb local dbname b
  | VernacRemoveHints (local,dbnames,ids) -> vernac_remove_hints local dbnames ids
  | VernacHints (local,dbnames,hints) -> vernac_hints local dbnames hints
  | VernacSyntacticDefinition (id,c,l,b) ->vernac_syntactic_definition id c l b
  | VernacDeclareImplicits (local,qid,l) ->vernac_declare_implicits local qid l
  | VernacArguments (local, qid, l, narg, flags) -> vernac_declare_arguments local qid l narg flags 
  | VernacReserve bl -> vernac_reserve bl
  | VernacGeneralizable (local,gen) -> vernac_generalizable local gen
  | VernacSetOpacity (local,qidl) -> vernac_set_opacity local qidl
  | VernacSetOption (locality,key,v) -> vernac_set_option locality key v
  | VernacUnsetOption (locality,key) -> vernac_unset_option locality key
  | VernacRemoveOption (key,v) -> vernac_remove_option key v
  | VernacAddOption (key,v) -> vernac_add_option key v
  | VernacMemOption (key,v) -> vernac_mem_option key v
  | VernacPrintOption key -> vernac_print_option key
  | VernacCheckMayEval (r,g,c) -> vernac_check_may_eval r g c
  | VernacDeclareReduction (b,s,r) -> vernac_declare_reduction b s r
  | VernacGlobalCheck c -> vernac_global_check c
  | VernacPrint p -> vernac_print p
  | VernacSearch (s,r) -> vernac_search s r
  | VernacLocate l -> vernac_locate l
  | VernacComments l -> if_verbose message ("Comments ok\n")
  | VernacNop -> ()

  (* Proof management *)
  | VernacGoal t -> vernac_start_proof Theorem [None,([],t,None)] false (fun _ _->())
  | VernacAbort id -> vernac_abort id
  | VernacAbortAll -> vernac_abort_all ()
  | VernacRestart -> vernac_restart ()
  | VernacUndo n -> vernac_undo n
  | VernacUndoTo n -> vernac_undoto n
  | VernacBacktrack (snum,pnum,naborts) -> vernac_backtrack snum pnum naborts
  | VernacFocus n -> vernac_focus n
  | VernacUnfocus -> vernac_unfocus ()
  | VernacUnfocused -> vernac_unfocused ()
  | VernacBullet b -> vernac_bullet b
  | VernacSubproof n -> vernac_subproof n
  | VernacEndSubproof -> vernac_end_subproof ()
  | VernacShow s -> vernac_show s
  | VernacCheckGuard -> vernac_check_guard ()
  | VernacProof (None, None) -> print_subgoals ()
  | VernacProof (Some tac, None) -> vernac_set_end_tac tac ; print_subgoals ()
  | VernacProof (None, Some l) -> vernac_set_used_variables l ; print_subgoals ()
  | VernacProof (Some tac, Some l) -> 
      vernac_set_end_tac tac; vernac_set_used_variables l ; print_subgoals ()
  | VernacProofMode mn -> Proof_global.set_proof_mode mn
  (* Toplevel control *)
  | VernacToplevelControl e -> raise e

  (* Extensions *)
  | VernacExtend (opn,args) -> Vernacinterp.call (opn,args)

let interp c = interp c ; check_locality ()

