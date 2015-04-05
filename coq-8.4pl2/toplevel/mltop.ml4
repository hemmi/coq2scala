(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Flags
open System
open Libobject
open Library
open System
open Vernacinterp

(* Code to hook Coq into the ML toplevel -- depends on having the
   objective-caml compiler mostly visible. The functions implemented here are:
   \begin{itemize}
   \item [dir_ml_load name]: Loads the ML module fname from the current ML
     path.
   \item [dir_ml_use]: Directive #use of Ocaml toplevel
   \item [add_ml_dir]: Directive #directory of Ocaml toplevel
   \end{itemize}

   How to build an ML module interface with these functions.
   The idea is that the ML directory path is like the Coq directory
   path.  So we can maintain the two in parallel.
   In the same way, we can use the "ml_env" as a kind of ML
   environment, which we freeze, unfreeze, and add things to just like
   to the other environments.
   Finally, we can create an object which is an ML module, and require
   that the "caching" of the ML module cause the loading of the
   associated ML file, if that file has not been yet loaded.  Of
   course, the problem is how to record dependencies between ML
   modules.
   (I do not know of a solution to this problem, other than to
   put all the needed names into the ML Module object.) *)

(* This path is where we look for .cmo *)
let coq_mlpath_copy = ref ["."]
let keep_copy_mlpath path =
  let cpath = canonical_path_name path in
  let filter path' = (cpath <> canonical_path_name path') in
  coq_mlpath_copy := path :: List.filter filter !coq_mlpath_copy

(* If there is a toplevel under Coq *)
type toplevel = {
  load_obj : string -> unit;
  use_file : string -> unit;
  add_dir  : string -> unit;
  ml_loop  : unit -> unit }

(* Determines the behaviour of Coq with respect to ML files (compiled
   or not) *)
type kind_load =
  | WithTop of toplevel
  | WithoutTop

(* Must be always initialized *)
let load = ref WithoutTop

(* Are we in a native version of Coq? *)
let is_native = IFDEF Byte THEN false ELSE true END

(* Sets and initializes a toplevel (if any) *)
let set_top toplevel = load := WithTop toplevel

(* Removes the toplevel (if any) *)
let remove ()= load := WithoutTop

(* Tests if an Ocaml toplevel runs under Coq *)
let is_ocaml_top () =
  match !load with
    | WithTop _ -> true
    |_ -> false

(* Tests if we can load ML files *)
let has_dynlink = IFDEF HasDynlink THEN true ELSE false END

(* Runs the toplevel loop of Ocaml *)
let ocaml_toploop () =
  match !load with
    | WithTop t -> Printexc.catch t.ml_loop ()
    | _ -> ()

(* Dynamic loading of .cmo/.cma *)
let dir_ml_load s =
  match !load with
    | WithTop t ->
      (try t.load_obj s
       with
       | (UserError _ | Failure _ | Anomaly _ | Not_found as u) -> raise u
       | e when Errors.noncritical e ->
         errorlabstrm "Mltop.load_object"
           (str"Cannot link ml-object " ++ str s ++ str" to Coq code."))
(* TO DO: .cma loading without toplevel *)
    | WithoutTop ->
      IFDEF HasDynlink THEN
	(* WARNING
	 * if this code section starts to use a module not used elsewhere
	 * in this file, the Makefile dependency logic needs to be updated.
	 *)
        let warn = Flags.is_verbose() in
        let _,gname = find_file_in_path ~warn !coq_mlpath_copy s in
        try
          Dynlink.loadfile gname;
	with | Dynlink.Error a ->
          errorlabstrm "Mltop.load_object" (str (Dynlink.error_message a))
      ELSE
        errorlabstrm "Mltop.no_load_object"
            (str"Loading of ML object file forbidden in a native Coq.")
      END

(* Dynamic interpretation of .ml *)
let dir_ml_use s =
  match !load with
    | WithTop t -> t.use_file s
    | _ -> warning "Cannot access the ML compiler"

(* Adds a path to the ML paths *)
let add_ml_dir s =
  match !load with
    | WithTop t -> t.add_dir s; keep_copy_mlpath s
    | WithoutTop when has_dynlink -> keep_copy_mlpath s
    | _ -> ()

(* For Rec Add ML Path *)
let add_rec_ml_dir unix_path =
  List.iter (fun (lp,_) -> add_ml_dir lp) (all_subdirs ~unix_path)

(* Adding files to Coq and ML loadpath *)

let add_path ~unix_path:dir ~coq_root:coq_dirpath =
  if exists_dir dir then
    begin
      add_ml_dir dir;
      Library.add_load_path true (dir,coq_dirpath)
    end
  else
    msg_warning (str ("Cannot open " ^ dir))

let convert_string d =
  try Names.id_of_string d
  with e when Errors.noncritical e ->
    if_warn msg_warning
      (str ("Directory "^d^" cannot be used as a Coq identifier (skipped)"));
    flush_all ();
    failwith "caught"

let add_rec_path ~unix_path ~coq_root =
  if exists_dir unix_path then
    let dirs = all_subdirs ~unix_path in
    let prefix = Names.repr_dirpath coq_root in
    let convert_dirs (lp,cp) =
      (lp,Names.make_dirpath (List.map convert_string (List.rev cp)@prefix)) in
    let dirs = map_succeed convert_dirs dirs in
    List.iter (fun lpe -> add_ml_dir (fst lpe)) dirs;
    add_ml_dir unix_path;
    List.iter (Library.add_load_path false) dirs;
    Library.add_load_path true (unix_path, coq_root)
  else
    msg_warning (str ("Cannot open " ^ unix_path))

(* convertit un nom quelconque en nom de fichier ou de module *)
let mod_of_name name =
  let base =
    if Filename.check_suffix name ".cmo" then
      Filename.chop_suffix name ".cmo"
    else
      name
  in
  String.capitalize base

let get_ml_object_suffix name =
  if Filename.check_suffix name ".cmo" then
    Some ".cmo"
  else if Filename.check_suffix name ".cma" then
    Some ".cma"
  else if Filename.check_suffix name ".cmxs" then
    Some ".cmxs"
  else
    None

let file_of_name name =
  let name = String.uncapitalize name in
  let suffix = get_ml_object_suffix name in
  let fail s =
    errorlabstrm "Mltop.load_object"
      (str"File not found on loadpath : " ++ str s) in
  if is_native then
    let name = match suffix with
      | Some ((".cmo"|".cma") as suffix) ->
          (Filename.chop_suffix name suffix) ^ ".cmxs"
      | Some ".cmxs" -> name
      | _ -> name ^ ".cmxs"
    in
    if is_in_path !coq_mlpath_copy name then name else fail name
  else
    let (full, base) = match suffix with
      | Some ".cmo" | Some ".cma" -> true, name
      | Some ".cmxs" -> false, Filename.chop_suffix name ".cmxs"
      | _ -> false, name
    in
    if full then
      if is_in_path !coq_mlpath_copy base then base else fail base
    else
      let name = base ^ ".cmo" in
      if is_in_path !coq_mlpath_copy name then name else
        let name = base ^ ".cma" in
        if is_in_path !coq_mlpath_copy name then name else
          fail (base ^ ".cm[oa]")

(** Is the ML code of the standard library placed into loadable plugins
    or statically compiled into coqtop ? For the moment this choice is
    made according to the presence of native dynlink : even if bytecode
    coqtop could always load plugins, we prefer to have uniformity between
    bytecode and native versions. *)

(* [known_loaded_module] contains the names of the loaded ML modules
 * (linked or loaded with load_object). It is used not to load a
 * module twice. It is NOT the list of ML modules Coq knows. *)

let known_loaded_modules = ref Stringset.empty

let add_known_module mname =
  let mname = String.capitalize mname in
  known_loaded_modules := Stringset.add mname !known_loaded_modules

let module_is_known mname =
  Stringset.mem (String.capitalize mname) !known_loaded_modules

(** A plugin is just an ML module with an initialization function. *)

let known_loaded_plugins = ref Stringmap.empty

let add_known_plugin init name =
  let name = String.capitalize name in
  add_known_module name;
  known_loaded_plugins := Stringmap.add name init !known_loaded_plugins

let init_known_plugins () =
  Stringmap.iter (fun _ f -> f()) !known_loaded_plugins

(** ml object = ml module or plugin *)

let init_ml_object mname =
  try Stringmap.find mname !known_loaded_plugins ()
  with Not_found -> ()

let load_ml_object mname fname=
  dir_ml_load fname;
  add_known_module mname;
  init_ml_object mname

(* Summary of declared ML Modules *)

(* List and not Stringset because order is important: most recent first. *)

let loaded_modules = ref []
let get_loaded_modules () = List.rev !loaded_modules
let add_loaded_module md = loaded_modules := md :: !loaded_modules
let reset_loaded_modules () = loaded_modules := []

let if_verbose_load verb f name fname =
  if not verb then f name fname
  else
    let info = "[Loading ML file "^fname^" ..." in
    try
      f name fname;
      msgnl (str (info^" done]"));
    with reraise ->
      msgnl (str (info^" failed]"));
      raise reraise

(** Load a module for the first time (i.e. dynlink it)
    or simulate its reload (i.e. doing nothing except maybe
    an initialization function). *)

let cache_ml_object verb reinit name =
  begin
    if module_is_known name then
      (if reinit then init_ml_object name)
    else if not has_dynlink then
      error ("Dynamic link not supported (module "^name^")")
    else
      if_verbose_load (verb && is_verbose ())
	load_ml_object name (file_of_name name)
  end;
  add_loaded_module name

let unfreeze_ml_modules x =
  reset_loaded_modules ();
  List.iter (cache_ml_object false false) x

let _ =
  Summary.declare_summary "ML-MODULES"
    { Summary.freeze_function = get_loaded_modules;
      Summary.unfreeze_function = unfreeze_ml_modules;
      Summary.init_function = reset_loaded_modules }

(* Liboject entries of declared ML Modules *)

type ml_module_object = {
  mlocal : Vernacexpr.locality_flag;
  mnames : string list
}

let cache_ml_objects (_,{mnames=mnames}) =
  List.iter (cache_ml_object true true) mnames

let classify_ml_objects ({mlocal=mlocal} as o) =
  if mlocal then Dispose else Substitute o

let inMLModule : ml_module_object -> obj =
  declare_object
    {(default_object "ML-MODULE") with
      load_function = (fun _ -> cache_ml_objects);
      cache_function = cache_ml_objects;
      subst_function = (fun (_,o) -> o);
      classify_function = classify_ml_objects }

let declare_ml_modules local l =
  let l = List.map mod_of_name l in
  Lib.add_anonymous_leaf (inMLModule {mlocal=local; mnames=l})

let print_ml_path () =
  let l = !coq_mlpath_copy in
  ppnl (str"ML Load Path:" ++ fnl () ++ str"  " ++
          hv 0 (prlist_with_sep pr_fnl pr_str l))

(* Printing of loaded ML modules *)

let print_ml_modules () =
  let l = get_loaded_modules () in
  pp (str"Loaded ML Modules: " ++ pr_vertical_list pr_str l)
