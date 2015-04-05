(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Reduction
open Proof_type
open Declarations
open Tacticals
open Tacmach
open Evar_refiner
open Tactics
open Pattern
open Clenv
open Auto
open Glob_term
open Hiddentac
open Typeclasses
open Typeclasses_errors
open Classes
open Topconstr
open Pfedit
open Command
open Libnames
open Evd
open Compat

let typeclasses_db = "typeclass_instances"
let typeclasses_debug = ref false
let typeclasses_depth = ref None

let _ = 
  Auto.add_auto_init 
    (fun () -> Auto.create_hint_db false typeclasses_db full_transparent_state true)

exception Found of evar_map

(** We transform the evars that are concerned by this resolution
    (according to predicate p) into goals.
    Invariant: function p only manipulates undefined evars *)

let evars_to_goals p evm =
  let goals, evm' =
    Evd.fold_undefined
      (fun ev evi (gls, evm') ->
	let evi', goal = p evm ev evi in
	let gls' = if goal then (ev,Goal.V82.build ev) :: gls else gls in
	(gls', Evd.add evm' ev evi'))
      evm ([], Evd.defined_evars evm)
  in
  if goals = [] then None else Some (List.rev goals, evm')

(** Typeclasses instance search tactic / eauto *)

open Auto

let e_give_exact flags c gl = 
  let t1 = (pf_type_of gl c) in
    tclTHEN (Clenvtac.unify ~flags t1) (exact_no_check c) gl

open Unification

let auto_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  modulo_delta = var_full_transparent_state;
  modulo_delta_types = full_transparent_state;
  modulo_delta_in_merge = None;
  check_applied_meta_types = false;
  resolve_evars = false;
  use_pattern_unification = true;
  use_meta_bound_pattern_unification = true;
  frozen_evars = ExistentialSet.empty;
  restrict_conv_on_strict_subterms = false; (* ? *)
  modulo_betaiota = true;
  modulo_eta = true;
  allow_K_in_toplevel_higher_order_unification = false
}

let rec eq_constr_mod_evars x y =
  match kind_of_term x, kind_of_term y with
  | Evar (e1, l1), Evar (e2, l2) when e1 <> e2 -> true
  | _, _ -> compare_constr eq_constr_mod_evars x y

let progress_evars t gl =
  let concl = pf_concl gl in
  let check gl' = 
    let newconcl = pf_concl gl' in
      if eq_constr_mod_evars concl newconcl 
      then tclFAIL 0 (str"No progress made (modulo evars)") gl'
      else tclIDTAC gl'
  in tclTHEN t check gl

TACTIC EXTEND progress_evars
  [ "progress_evars" tactic(t) ] -> [ progress_evars (Tacinterp.eval_tactic t) ]
END

let unify_e_resolve flags (c,clenv) gls =
  let clenv' = connect_clenv gls clenv in
  let clenv' = clenv_unique_resolver ~flags clenv' gls in
    Clenvtac.clenv_refine true ~with_classes:false clenv' gls

let unify_resolve flags (c,clenv) gls =
  let clenv' = connect_clenv gls clenv in
  let clenv' = clenv_unique_resolver ~flags clenv' gls in
    Clenvtac.clenv_refine false ~with_classes:false clenv' gls

let clenv_of_prods nprods (c, clenv) gls =
  if nprods = 0 then Some clenv
  else 
    let ty = pf_type_of gls c in
    let diff = nb_prod ty - nprods in
      if diff >= 0 then
	Some (mk_clenv_from_n gls (Some diff) (c,ty))
      else None

let with_prods nprods (c, clenv) f gls =
  match clenv_of_prods nprods (c, clenv) gls with
  | None -> tclFAIL 0 (str"Not enough premisses") gls
  | Some clenv' -> f (c, clenv') gls

(** Hack to properly solve dependent evars that are typeclasses *)

let flags_of_state st =
  {auto_unif_flags with
    modulo_conv_on_closed_terms = Some st; modulo_delta = st; 
     modulo_delta_types = st;
     modulo_eta = false}

let rec e_trivial_fail_db db_list local_db goal =
  let tacl =
    Eauto.registered_e_assumption ::
    (tclTHEN Tactics.intro
       (function g'->
	  let d = pf_last_hyp g' in
	  let hintl = make_resolve_hyp (pf_env g') (project g') d in
          (e_trivial_fail_db db_list
	      (Hint_db.add_list hintl local_db) g'))) ::
    (List.map (fun (x,_,_,_,_) -> x) (e_trivial_resolve db_list local_db (pf_concl goal)))
  in 
  tclFIRST (List.map tclCOMPLETE tacl) goal 

and e_my_find_search db_list local_db hdc complete concl =
  let hdc = head_of_constr_reference hdc in
  let prods, concl = decompose_prod_assum concl in
  let nprods = List.length prods in
  let hintl =
    list_map_append
      (fun db ->
	if Hint_db.use_dn db then
	  let flags = flags_of_state (Hint_db.transparent_state db) in
	    List.map (fun x -> (flags, x)) (Hint_db.map_auto (hdc,concl) db)
	else
	  let flags = flags_of_state (Hint_db.transparent_state db) in
	    List.map (fun x -> (flags, x)) (Hint_db.map_all hdc db))
      (local_db::db_list)
  in
  let tac_of_hint =
    fun (flags, {pri = b; pat = p; code = t; name = name}) ->
      let tac =
	match t with
	  | Res_pf (term,cl) -> with_prods nprods (term,cl) (unify_resolve flags)
	  | ERes_pf (term,cl) -> with_prods nprods (term,cl) (unify_e_resolve flags)
	  | Give_exact (c) -> e_give_exact flags c
	  | Res_pf_THEN_trivial_fail (term,cl) ->
              tclTHEN (with_prods nprods (term,cl) (unify_e_resolve flags))
	        (if complete then tclIDTAC else e_trivial_fail_db db_list local_db)
	  | Unfold_nth c -> tclWEAK_PROGRESS (unfold_in_concl [all_occurrences,c])
	  | Extern tacast -> 
(* 	    tclTHEN *)
(* 	      (fun gl -> Refiner.tclEVARS (mark_unresolvables (project gl)) gl) *)
	      (conclPattern concl p tacast)
      in
      let tac = if complete then tclCOMPLETE tac else tac in
	match t with
	| Extern _ -> (tac,b,true, name, lazy (pr_autotactic t))
	| _ -> 
(* 	  let tac gl = with_pattern (pf_env gl) (project gl) flags p concl tac gl in *)
	    (tac,b,false, name, lazy (pr_autotactic t))
  in List.map tac_of_hint hintl

and e_trivial_resolve db_list local_db gl =
  try
    e_my_find_search db_list local_db
    (fst (head_constr_bound gl)) true gl
  with Bound | Not_found -> []

let e_possible_resolve db_list local_db gl =
  try
    e_my_find_search db_list local_db
      (fst (head_constr_bound gl)) false gl
  with Bound | Not_found -> []

let rec catchable = function
  | Refiner.FailError _ -> true
  | Loc.Exc_located (_, e) -> catchable e
  | e -> Logic.catchable_exception e

let nb_empty_evars s =
  Evd.fold_undefined (fun ev evi acc -> succ acc) s 0

let pr_ev evs ev = Printer.pr_constr_env (Goal.V82.env evs ev) (Evarutil.nf_evar evs (Goal.V82.concl evs ev))

let pr_depth l = prlist_with_sep (fun () -> str ".") pr_int (List.rev l)

type autoinfo = { hints : Auto.hint_db; is_evar: existential_key option;
		  only_classes: bool; auto_depth: int list; auto_last_tac: std_ppcmds Lazy.t;
		  auto_path : global_reference option list;
		  auto_cut : hints_path }
type autogoal = goal * autoinfo
type 'ans fk = unit -> 'ans
type ('a,'ans) sk = 'a -> 'ans fk -> 'ans
type 'a tac = { skft : 'ans. ('a,'ans) sk -> 'ans fk -> autogoal sigma -> 'ans }

type auto_result = autogoal list sigma

type atac = auto_result tac

let make_resolve_hyp env sigma st flags only_classes pri (id, _, cty) =
  let cty = Evarutil.nf_evar sigma cty in
  let rec iscl env ty = 
    let ctx, ar = decompose_prod_assum ty in
      match kind_of_term (fst (decompose_app ar)) with
      | Const c -> is_class (ConstRef c)
      | Ind i -> is_class (IndRef i)
      | _ -> 
	  let env' = Environ.push_rel_context ctx env in
	  let ty' = whd_betadeltaiota env' ar in
	       if not (eq_constr ty' ar) then iscl env' ty'
	       else false
  in
  let is_class = iscl env cty in
  let keep = not only_classes || is_class in
    if keep then 
      let c = mkVar id in
      let name = PathHints [VarRef id] in
      let hints =
	if is_class then
	  let hints = build_subclasses ~check:false env sigma (VarRef id) None in
	    (list_map_append
	       (fun (pri, c) -> make_resolves env sigma 
		  (true,false,Flags.is_verbose()) pri c) 
	       hints)
	else []
      in
        (hints @ map_succeed 
	 (fun f -> try f (c,cty) with UserError _ -> failwith "") 
	 [make_exact_entry ~name sigma pri; make_apply_entry ~name env sigma flags pri])
    else []

let pf_filtered_hyps gls = 
  Goal.V82.hyps gls.Evd.sigma (sig_it gls)

let make_hints g st only_classes sign =
  let paths, hintlist = 
    List.fold_left 
    (fun (paths, hints) hyp ->
     if is_section_variable (pi1 hyp) then (paths, hints)
     else
       let path, hint = 		    
	 PathEmpty, pf_apply make_resolve_hyp g st (true,false,false) only_classes None hyp
       in
	 (PathOr (paths, path), hint @ hints))
    (PathEmpty, []) sign
  in Hint_db.add_list hintlist (Hint_db.empty st true)

let autogoal_hints_cache : (Environ.named_context_val * hint_db) option ref = ref None
let freeze () = !autogoal_hints_cache
let unfreeze v = autogoal_hints_cache := v
let init () = autogoal_hints_cache := None

let _ = init ()

let _ =
  Summary.declare_summary "autogoal-hints-cache"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }
    
let make_autogoal_hints = 
  fun only_classes ?(st=full_transparent_state) g ->
    let sign = pf_filtered_hyps g in
      match freeze () with
      | Some (sign', hints) when Environ.eq_named_context_val sign sign' -> hints
      | _ -> let hints = make_hints g st only_classes (Environ.named_context_of_val sign) in
	  unfreeze (Some (sign, hints)); hints
	  
let lift_tactic tac (f : goal list sigma -> autoinfo -> autogoal list sigma) : 'a tac =
  { skft = fun sk fk {it = gl,hints; sigma=s} ->
    let res = try Some (tac {it=gl; sigma=s}) with e when catchable e -> None in
      match res with
      | Some gls -> sk (f gls hints) fk
      | None -> fk () }

let intro_tac : atac =
  lift_tactic Tactics.intro
    (fun {it = gls; sigma = s} info ->
      let gls' =
	List.map (fun g' ->
	  let env = Goal.V82.env s g' in
	  let context = Environ.named_context_of_val (Goal.V82.hyps s g') in
	  let hint = make_resolve_hyp env s (Hint_db.transparent_state info.hints) 
	    (true,false,false) info.only_classes None (List.hd context) in
	  let ldb = Hint_db.add_list hint info.hints in
	    (g', { info with is_evar = None; hints = ldb; auto_last_tac = lazy (str"intro") })) gls
      in {it = gls'; sigma = s})

let normevars_tac : atac = 
  { skft = fun sk fk {it = (gl, info); sigma = s} ->
    let gl', sigma' = Goal.V82.nf_evar s gl in
    let info' = { info with auto_last_tac = lazy (str"normevars") } in
      sk {it = [gl', info']; sigma = sigma'} fk }

(* Ordering of states is lexicographic on the number of remaining goals. *)
let compare (pri, _, _, res) (pri', _, _, res') =
  let nbgoals s =
    List.length (sig_it s) + nb_empty_evars (sig_sig s)
  in
  let pri = pri - pri' in
    if pri <> 0 then pri
    else nbgoals res - nbgoals res'

let or_tac (x : 'a tac) (y : 'a tac) : 'a tac =
  { skft = fun sk fk gls -> x.skft sk (fun () -> y.skft sk fk gls) gls }

let hints_tac hints =
  { skft = fun sk fk {it = gl,info; sigma = s} ->
      let concl = Goal.V82.concl s gl in
      let tacgl = {it = gl; sigma = s} in
      let poss = e_possible_resolve hints info.hints concl in
      let rec aux i foundone = function
	| (tac, _, b, name, pp) :: tl ->
	  let derivs = path_derivate info.auto_cut name in
	  let res = 
            try
		if path_matches derivs [] then None else Some (tac tacgl)
	    with e when catchable e -> None 
	  in
	    (match res with
	       | None -> aux i foundone tl
	       | Some {it = gls; sigma = s'} ->
	    	   if !typeclasses_debug then
		     msgnl (pr_depth (i :: info.auto_depth) ++ str": " ++ Lazy.force pp
			    ++ str" on" ++ spc () ++ pr_ev s gl);
		   let fk =
		     (fun () -> if !typeclasses_debug then msgnl (str"backtracked after " ++ Lazy.force pp);
			aux (succ i) true tl)
		   in
		   let sgls =
		     evars_to_goals
		       (fun evm ev evi ->
			  if Typeclasses.is_resolvable evi &&
			    (not info.only_classes || Typeclasses.is_class_evar evm evi)
			  then Typeclasses.mark_unresolvable evi, true
			  else evi, false) s'
		   in
		   let newgls, s' =
		     let gls' = List.map (fun g -> (None, g)) gls in
		       match sgls with
		       | None -> gls', s'
		       | Some (evgls, s') ->
			 (* Reorder with dependent subgoals. *)
			 (gls' @ List.map (fun (ev, x) -> Some ev, x) evgls, s')
		   in
		   let gls' = list_map_i
		     (fun j (evar, g) ->
			let info =
			  { info with auto_depth = j :: i :: info.auto_depth; auto_last_tac = pp;
			      is_evar = evar;
			      hints =
			      if b && not (Environ.eq_named_context_val (Goal.V82.hyps s' g) (Goal.V82.hyps s' gl))
			      then make_autogoal_hints info.only_classes
				~st:(Hint_db.transparent_state info.hints) {it = g; sigma = s'}
			      else info.hints;
			      auto_cut = derivs }
			in g, info) 1 newgls in
		   let glsv = {it = gls'; sigma = s'} in
		     sk glsv fk)
	| [] ->
	  if not foundone && !typeclasses_debug then
	    msgnl (pr_depth info.auto_depth ++ str": no match for " ++
		     Printer.pr_constr_env (Goal.V82.env s gl) concl ++
		     spc () ++ int (List.length poss) ++ str" possibilities");
	  fk ()
    in aux 1 false poss }

let isProp env sigma concl = 
  let ty = Retyping.get_type_of env sigma concl in
    kind_of_term ty = Sort (Prop Null)

let needs_backtrack only_classes env evd oev concl =
  if oev = None || isProp env evd concl then
    not (Intset.is_empty (Evarutil.evars_of_term concl))
  else true

let then_list (second : atac) (sk : (auto_result, 'a) sk) : (auto_result, 'a) sk =
  let rec aux s (acc : autogoal list list) fk = function
    | (gl,info) :: gls ->
	(match info.is_evar with 
	 | Some ev when Evd.is_defined s ev -> aux s acc fk gls
	 | _ -> 
	     second.skft
	       (fun {it=gls';sigma=s'} fk' ->
		  let needs_backtrack = 
		    if gls' = [] then
 		      needs_backtrack info.only_classes
		        (Goal.V82.env s gl) s' info.is_evar (Goal.V82.concl s gl)
		    else true
		  in
		  let fk'' = 
		    if not needs_backtrack then
		      (if !typeclasses_debug then msgnl (str"no backtrack on " ++ pr_ev s gl ++ 
							 str " after " ++ Lazy.force info.auto_last_tac); fk) 
		    else fk' 
		  in aux s' (gls'::acc) fk'' gls)
	       fk {it = (gl,info); sigma = s})
    | [] -> Some (List.rev acc, s, fk)
  in fun {it = gls; sigma = s} fk ->
    let rec aux' = function
      | None -> fk ()
      | Some (res, s', fk') ->
	  let goals' = List.concat res in
	    sk {it = goals'; sigma = s'} (fun () -> aux' (fk' ()))
    in aux' (aux s [] (fun () -> None) gls)

let then_tac (first : atac) (second : atac) : atac =
  { skft = fun sk fk -> first.skft (then_list second sk) fk }

let run_tac (t : 'a tac) (gl : autogoal sigma) : auto_result option =
  t.skft (fun x _ -> Some x) (fun _ -> None) gl

type run_list_res = (auto_result * run_list_res fk) option

let run_list_tac (t : 'a tac) p goals (gl : autogoal list sigma) : run_list_res =
  (then_list t (fun x fk -> Some (x, fk)))
    gl
    (fun _ -> None)

let fail_tac : atac = 
  { skft = fun sk fk _ -> fk () }

let rec fix (t : 'a tac) : 'a tac =
  then_tac t { skft = fun sk fk -> (fix t).skft sk fk }

let rec fix_limit limit (t : 'a tac) : 'a tac =
  if limit = 0 then fail_tac 
  else then_tac t { skft = fun sk fk -> (fix_limit (pred limit) t).skft sk fk }
    
let make_autogoal ?(only_classes=true) ?(st=full_transparent_state) cut ev g =
  let hints = make_autogoal_hints only_classes ~st g in
    (g.it, { hints = hints ; is_evar = ev; 
	     only_classes = only_classes; auto_depth = []; auto_last_tac = lazy (str"none");
	     auto_path = []; auto_cut = cut })
      

let cut_of_hints h =
  List.fold_left (fun cut db -> PathOr (Hint_db.cut db, cut)) PathEmpty h

let make_autogoals ?(only_classes=true) ?(st=full_transparent_state) hints gs evm' =
  let cut = cut_of_hints hints in
  { it = list_map_i (fun i g -> 
    let (gl, auto) = make_autogoal ~only_classes ~st cut (Some (fst g)) {it = snd g; sigma = evm'} in
      (gl, { auto with auto_depth = [i]})) 1 gs; sigma = evm' }

let get_result r = 
  match r with
  | None -> None
  | Some (gls, fk) -> Some (gls.sigma,fk)
	
let run_on_evars ?(only_classes=true) ?(st=full_transparent_state) p evm hints tac =
  match evars_to_goals p evm with
  | None -> None (* This happens only because there's no evar having p *)
  | Some (goals, evm') ->
      let res = run_list_tac tac p goals (make_autogoals ~only_classes ~st hints goals evm') in
	match get_result res with
	| None -> raise Not_found
	| Some (evm', fk) -> Some (evars_reset_evd ~with_conv_pbs:true evm' evm, fk)
	    
let eauto_tac hints = 
  then_tac normevars_tac (or_tac (hints_tac hints) intro_tac)

let eauto_tac ?limit hints = 
  match limit with
  | None -> fix (eauto_tac hints)
  | Some limit -> fix_limit limit (eauto_tac hints)
      
let eauto ?(only_classes=true) ?st ?limit hints g =
  let gl = { it = make_autogoal ~only_classes ?st (cut_of_hints hints) None g; sigma = project g } in
    match run_tac (eauto_tac ?limit hints) gl with
    | None -> raise Not_found
    | Some {it = goals; sigma = s} ->
	{it = List.map fst goals; sigma = s}

let real_eauto st ?limit hints p evd =
  let rec aux evd fails =
    let res, fails =
      try run_on_evars ~st p evd hints (eauto_tac ?limit hints), fails
      with Not_found ->
	List.fold_right (fun fk (res, fails) ->
	  match res with
	  | Some r -> res, fk :: fails
	  | None -> get_result (fk ()), fails)
	  fails (None, [])
    in
      match res with
      | None -> evd
      | Some (evd', fk) -> aux evd' (fk :: fails)
  in aux evd []

let resolve_all_evars_once debug limit p evd =
  let db = searchtable_map typeclasses_db in
    real_eauto ?limit (Hint_db.transparent_state db) [db] p evd

(** We compute dependencies via a union-find algorithm.
    Beware of the imperative effects on the partition structure,
    it should not be shared, but only used locally. *)

module Intpart = Unionfind.Make(Intset)(Intmap)

let deps_of_constraints cstrs evm p =
  List.iter (fun (_, _, x, y) ->
    let evx = Evarutil.undefined_evars_of_term evm x in
    let evy = Evarutil.undefined_evars_of_term evm y in
    Intpart.union_set (Intset.union evx evy) p)
    cstrs

let evar_dependencies evm p =
  Evd.fold_undefined
    (fun ev evi _ ->
      let evars = Intset.add ev (Evarutil.undefined_evars_of_evar_info evm evi)
      in Intpart.union_set evars p)
    evm ()

let resolve_one_typeclass env ?(sigma=Evd.empty) gl =
  let nc, gl, subst, _ = Evarutil.push_rel_context_to_named_context env gl in
  let (gl,t,sigma) = 
    Goal.V82.mk_goal sigma nc gl Store.empty in
  let gls = { it = gl ; sigma = sigma } in
  let hints = searchtable_map typeclasses_db in
  let gls' = eauto ?limit:!typeclasses_depth ~st:(Hint_db.transparent_state hints) [hints] gls in
  let evd = sig_sig gls' in
  let t' = let (ev, inst) = destEvar t in
    mkEvar (ev, Array.of_list subst)
  in
  let term = Evarutil.nf_evar evd t' in
    evd, term

let _ =
  Typeclasses.solve_instanciation_problem := (fun x y z -> resolve_one_typeclass x ~sigma:y z)

(** [split_evars] returns groups of undefined evars according to dependencies *)

let split_evars evm =
  let p = Intpart.create () in
  evar_dependencies evm p;
  deps_of_constraints (snd (extract_all_conv_pbs evm)) evm p;
  Intpart.partition p

(** [evars_in_comp] filters an [evar_map], keeping only evars
    that belongs to a certain component *)

let evars_in_comp comp evm =
  try
    evars_reset_evd 
      (Intset.fold (fun ev acc -> Evd.add acc ev (Evd.find_undefined evm ev))
	 comp Evd.empty) evm
  with Not_found -> assert false

let is_inference_forced p evd ev =
  try
    let evi = Evd.find_undefined evd ev in
    if Typeclasses.is_resolvable evi && snd (p ev evi)
    then
      let (loc, k) = evar_source ev evd in
      match k with
	| ImplicitArg (_, _, b) -> b
	| QuestionMark _ -> false
	| _ -> true
    else true
  with Not_found -> assert false

let is_mandatory p comp evd =
  Intset.exists (is_inference_forced p evd) comp

(** In case of unsatisfiable constraints, build a nice error message *)

let error_unresolvable env comp do_split evd =
  let evd = Evarutil.nf_evar_map_undefined evd in
  let evm = if do_split then evars_in_comp comp evd else evd in
  let _, ev = Evd.fold_undefined
    (fun ev evi (b,acc) ->
      (* focus on one instance if only one was searched for *)
      if class_of_constr evi.evar_concl <> None then
	if not b (* || do_split *) then
	  true, Some ev
	else b, None
      else b, acc) evm (false, None)
  in
  Typeclasses_errors.unsatisfiable_constraints
    (Evarutil.nf_env_evar evm env) evm ev

(** Check if an evar is concerned by the current resolution attempt,
    (and in particular is in the current component), and also update
    its evar_info.
    Invariant : this should only be applied to undefined evars,
    and return undefined evar_info *)

let select_and_update_evars p oevd in_comp evd ev evi =
  assert (evi.evar_body = Evar_empty);
  try
    let oevi = Evd.find_undefined oevd ev in
    if Typeclasses.is_resolvable oevi then
      Typeclasses.mark_unresolvable evi,
      (in_comp ev && p evd ev evi)
    else evi, false
  with Not_found ->
    Typeclasses.mark_unresolvable evi, p evd ev evi

(** Do we still have unresolved evars that should be resolved ? *)

let has_undefined p oevd evd =
  Evd.fold_undefined (fun ev evi has -> has ||
    snd (p oevd ev evi))
    evd false

(** Revert the resolvability status of evars after resolution,
    potentially unprotecting some evars that were set unresolvable
    just for this call to resolution. *)

let revert_resolvability oevd evd = 
  Evd.fold_undefined
    (fun ev evi evm ->
     try 
       if not (Typeclasses.is_resolvable evi) then
	 let evi' = Evd.find_undefined oevd ev in
	   if Typeclasses.is_resolvable evi' then
	     Evd.add evm ev (Typeclasses.mark_resolvable evi)
	   else evm
       else evm
     with Not_found -> evm)
  evd evd

(** If [do_split] is [true], we try to separate the problem in
    several components and then solve them separately *)

exception Unresolved

let resolve_all_evars debug m env p oevd do_split fail =
  let split = if do_split then split_evars oevd else [Intset.empty] in
  let in_comp comp ev = if do_split then Intset.mem ev comp else true
  in
  let rec docomp evd = function
    | [] -> revert_resolvability oevd evd
    | comp :: comps ->
      let p = select_and_update_evars p oevd (in_comp comp) in
      try
	 let evd' = resolve_all_evars_once debug m p evd in
	 if has_undefined p oevd evd' then raise Unresolved;
	 docomp evd' comps
      with Unresolved | Not_found ->
	if fail && (not do_split || is_mandatory (p evd) comp evd)
	then (* Unable to satisfy the constraints. *)
	  error_unresolvable env comp do_split evd
	else (* Best effort: do nothing on this component *) 
	  docomp evd comps
  in docomp oevd split

let initial_select_evars filter evd ev evi =
  filter (snd evi.Evd.evar_source) &&
  Typeclasses.is_class_evar evd evi

let resolve_typeclass_evars debug m env evd filter split fail =
  let evd = 
    try Evarconv.consider_remaining_unif_problems
      ~ts:(Typeclasses.classes_transparent_state ()) env evd
    with e when Errors.noncritical e -> evd
  in
    resolve_all_evars debug m env (initial_select_evars filter) evd split fail

let solve_inst debug depth env evd filter split fail =
  resolve_typeclass_evars debug depth env evd filter split fail

let _ =
  Typeclasses.solve_instanciations_problem :=
    solve_inst false !typeclasses_depth


(** Options: depth, debug and transparency settings. *)

open Goptions

let set_typeclasses_debug d = (:=) typeclasses_debug d;
  Typeclasses.solve_instanciations_problem := solve_inst d !typeclasses_depth
    
let get_typeclasses_debug () = !typeclasses_debug

let set_typeclasses_debug =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "debug output for typeclasses proof search";
      optkey   = ["Typeclasses";"Debug"];
      optread  = get_typeclasses_debug;
      optwrite = set_typeclasses_debug; }


let set_typeclasses_depth d = (:=) typeclasses_depth d;
  Typeclasses.solve_instanciations_problem := solve_inst !typeclasses_debug !typeclasses_depth
    
let get_typeclasses_depth () = !typeclasses_depth

let set_typeclasses_depth =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "depth for typeclasses proof search";
      optkey   = ["Typeclasses";"Depth"];
      optread  = get_typeclasses_depth;
      optwrite = set_typeclasses_depth; }

let set_transparency cl b =
  List.iter (fun r -> 
    let gr = Smartlocate.global_with_alias r in
    let ev = Tacred.evaluable_of_global_reference (Global.env ()) gr in
      Classes.set_typeclass_transparency ev false b) cl

VERNAC COMMAND EXTEND Typeclasses_Unfold_Settings
| [ "Typeclasses" "Transparent" reference_list(cl) ] -> [
    set_transparency cl true ]
END

VERNAC COMMAND EXTEND Typeclasses_Rigid_Settings
| [ "Typeclasses" "Opaque" reference_list(cl) ] -> [
    set_transparency cl false ]
END

open Genarg
open Extraargs

let pr_debug _prc _prlc _prt b =
  if b then Pp.str "debug" else Pp.mt()

ARGUMENT EXTEND debug TYPED AS bool PRINTED BY pr_debug
| [ "debug" ] -> [ true ]
| [ ] -> [ false ]
END

let pr_depth _prc _prlc _prt = function
    Some i -> Util.pr_int i
  | None -> Pp.mt()

ARGUMENT EXTEND depth TYPED AS int option PRINTED BY pr_depth
| [ int_or_var_opt(v) ] -> [ match v with Some (ArgArg i) -> Some i | _ -> None ]
END

(* true = All transparent, false = Opaque if possible *)

VERNAC COMMAND EXTEND Typeclasses_Settings
 | [ "Typeclasses" "eauto" ":=" debug(d) depth(depth) ] -> [
     set_typeclasses_debug d;
     set_typeclasses_depth depth
   ]
END

let typeclasses_eauto ?(only_classes=false) ?(st=full_transparent_state) dbs gl =
  try 
    let dbs = list_map_filter
      (fun db -> try Some (Auto.searchtable_map db)
        with e when Errors.noncritical e -> None) dbs
    in
    let st = match dbs with x :: _ -> Hint_db.transparent_state x | _ -> st in
      eauto ?limit:!typeclasses_depth ~only_classes ~st dbs gl
   with Not_found -> tclFAIL 0 (str" typeclasses eauto failed on: " ++ Printer.pr_goal gl) gl
 
TACTIC EXTEND typeclasses_eauto
| [ "typeclasses" "eauto" "with" ne_preident_list(l) ] -> [ typeclasses_eauto l ]
| [ "typeclasses" "eauto" ] -> [ typeclasses_eauto ~only_classes:true [typeclasses_db] ]
END

let _ = Classes.refine_ref := Refine.refine

(** Take the head of the arity of a constr.
    Used in the partial application tactic. *)

let rec head_of_constr t =
  let t = strip_outer_cast(collapse_appl t) in
    match kind_of_term t with
    | Prod (_,_,c2)  -> head_of_constr c2
    | LetIn (_,_,_,c2) -> head_of_constr c2
    | App (f,args)  -> head_of_constr f
    | _      -> t

TACTIC EXTEND head_of_constr
  [ "head_of_constr" ident(h) constr(c) ] -> [
    let c = head_of_constr c in
      letin_tac None (Name h) c None allHyps
  ]
END

TACTIC EXTEND not_evar
  [ "not_evar" constr(ty) ] -> [
    match kind_of_term ty with
    | Evar _ -> tclFAIL 0 (str"Evar")
    | _ -> tclIDTAC ]
END

TACTIC EXTEND is_ground
  [ "is_ground" constr(ty) ] -> [ fun gl ->
    if Evarutil.is_ground_term (project gl) ty then tclIDTAC gl
    else tclFAIL 0 (str"Not ground") gl ]
END

TACTIC EXTEND autoapply
  [ "autoapply" constr(c) "using" preident(i) ] -> [ fun gl ->
    let flags = flags_of_state (Auto.Hint_db.transparent_state (Auto.searchtable_map i)) in
    let cty = pf_type_of gl c in
    let ce = mk_clenv_from gl (c,cty) in
      unify_e_resolve flags (c,ce) gl ]
END
