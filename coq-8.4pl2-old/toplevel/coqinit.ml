(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open System
open Toplevel

let (/) = Filename.concat

let set_debug () = Flags.debug := true

(* Loading of the ressource file.
   rcfile is either $XDG_CONFIG_HOME/.coqrc.VERSION, or $XDG_CONFIG_HOME/.coqrc if the first one
  does not exist. *)

let rcdefaultname = "coqrc"
let rcfile = ref ""
let rcfile_specified = ref false
let set_rcfile s = rcfile := s; rcfile_specified := true

let load_rc = ref true
let no_load_rc () = load_rc := false

let load_rcfile() =
  if !load_rc then
    try
      if !rcfile_specified then
        if file_readable_p !rcfile then
          Vernac.load_vernac false !rcfile
        else raise (Sys_error ("Cannot read rcfile: "^ !rcfile))
      else try let inferedrc = List.find file_readable_p [
	Envars.xdg_config_home/rcdefaultname^"."^Coq_config.version;
	Envars.xdg_config_home/rcdefaultname;
	System.home/"."^rcdefaultname^"."^Coq_config.version;
	System.home/"."^rcdefaultname;
      ] in
        Vernac.load_vernac false inferedrc
	with Not_found -> ()
	(*
	Flags.if_verbose
	  mSGNL (str ("No coqrc or coqrc."^Coq_config.version^
			 " found. Skipping rcfile loading."))
	*)
    with reraise ->
      (msgnl (str"Load of rcfile failed.");
       raise reraise)
  else
    Flags.if_verbose msgnl (str"Skipping rcfile loading.")

(* Puts dir in the path of ML and in the LoadPath *)
let coq_add_path unix_path s =
  Mltop.add_path ~unix_path ~coq_root:(Names.make_dirpath [Nameops.coq_root;Names.id_of_string s])
let coq_add_rec_path unix_path = Mltop.add_rec_path ~unix_path ~coq_root:(Names.make_dirpath [Nameops.coq_root])

(* By the option -include -I or -R of the command line *)
let includes = ref []
let push_include (s, alias) = includes := (s,alias,false) :: !includes
let push_rec_include (s, alias) = includes := (s,alias,true) :: !includes

(* The list of all theories in the standard library /!\ order does matter *)
let theories_dirs_map = [
    "theories/Unicode", "Unicode" ;
    "theories/Classes", "Classes" ;
    "theories/Program", "Program" ;
    "theories/MSets", "MSets" ;
    "theories/FSets", "FSets" ;
    "theories/Reals", "Reals" ;
    "theories/Strings", "Strings" ;
    "theories/Sorting", "Sorting" ;
    "theories/Setoids", "Setoids" ;
    "theories/Sets", "Sets" ;
    "theories/Structures", "Structures" ;
    "theories/Lists", "Lists" ;
    "theories/Vectors", "Vectors" ;
    "theories/Wellfounded", "Wellfounded" ;
    "theories/Relations", "Relations" ;
    "theories/Numbers", "Numbers" ;
    "theories/QArith", "QArith" ;
    "theories/PArith", "PArith" ;
    "theories/NArith", "NArith" ;
    "theories/ZArith", "ZArith" ;
    "theories/Arith", "Arith" ;
    "theories/Bool", "Bool" ;
    "theories/Logic", "Logic" ;
    "theories/Init", "Init"
  ]

(* Initializes the LoadPath *)
let init_load_path () =
  let coqlib = Envars.coqlib () in
  let user_contrib = coqlib/"user-contrib" in
  let xdg_dirs = Envars.xdg_dirs in
  let coqpath = Envars.coqpath in
  let dirs = ["states";"plugins"] in
    (* NOTE: These directories are searched from last to first *)
    (* first, developer specific directory to open *)
    if Coq_config.local then coq_add_path (coqlib/"dev") "dev";
    (* then standard library *)
    List.iter
      (fun (s,alias) -> Mltop.add_rec_path ~unix_path:(coqlib/s) ~coq_root:(Names.make_dirpath [Names.id_of_string alias; Nameops.coq_root]))
      theories_dirs_map;
    (* then states and plugins *)
    List.iter (fun s -> coq_add_rec_path (coqlib/s)) dirs;
    (* then user-contrib *)
    if Sys.file_exists user_contrib then
      Mltop.add_rec_path ~unix_path:user_contrib ~coq_root:Nameops.default_root_prefix;
    (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME *)
    List.iter (fun s -> Mltop.add_rec_path ~unix_path:s ~coq_root:Nameops.default_root_prefix) xdg_dirs;
    (* then directories in COQPATH *)
    List.iter (fun s -> Mltop.add_rec_path ~unix_path:s ~coq_root:Nameops.default_root_prefix) coqpath;
    (* then current directory *)
    Mltop.add_path ~unix_path:"." ~coq_root:Nameops.default_root_prefix;
    (* additional loadpath, given with -I -include -R options *)
    List.iter
      (fun (unix_path, coq_root, reci) ->
	if reci then Mltop.add_rec_path ~unix_path ~coq_root else Mltop.add_path ~unix_path ~coq_root)
      (List.rev !includes)

let init_library_roots () =
  includes := []

(* Initialises the Ocaml toplevel before launching it, so that it can
   find the "include" file in the *source* directory *)
let init_ocaml_path () =
  let add_subdir dl =
    Mltop.add_ml_dir (List.fold_left (/) Envars.coqroot dl)
  in
    Mltop.add_ml_dir (Envars.coqlib ());
    List.iter add_subdir
      [ [ "config" ]; [ "dev" ]; [ "lib" ]; [ "kernel" ]; [ "library" ];
	[ "pretyping" ]; [ "interp" ]; [ "parsing" ]; [ "proofs" ];
	[ "tactics" ]; [ "toplevel" ]; [ "translate" ]; [ "ide" ] ]

let get_compat_version = function
  | "8.3" -> Flags.V8_3
  | "8.2" -> Flags.V8_2
  | ("8.1" | "8.0") as s ->
    warning ("Compatibility with version "^s^" not supported.");
    Flags.V8_2
  | s -> Util.error ("Unknown compatibility version \""^s^"\".")
