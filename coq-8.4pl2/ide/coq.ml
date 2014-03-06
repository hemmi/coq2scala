(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ideutils

(** * Version and date *)

let get_version_date () =
  let date =
    if Glib.Utf8.validate Coq_config.date
    then Coq_config.date
    else "<date not printable>" in
  try
    (* the following makes sense only when running with local layout *)
    let coqroot = Filename.concat
      (Filename.dirname Sys.executable_name)
      Filename.parent_dir_name
    in
    let ch = open_in (Filename.concat coqroot "revision") in
    let ver = input_line ch in
    let rev = input_line ch in
    (ver,rev)
  with _ -> (Coq_config.version,date)

let short_version () =
  let (ver,date) = get_version_date () in
  Printf.sprintf "The Coq Proof Assistant, version %s (%s)\n" ver date

let version () =
  let (ver,date) = get_version_date () in
    Printf.sprintf
      "The Coq Proof Assistant, version %s (%s)\
       \nArchitecture %s running %s operating system\
       \nGtk version is %s\
       \nThis is %s (%s is the best one for this architecture and OS)\
       \n"
      ver date
      Coq_config.arch Sys.os_type
      (let x,y,z = GMain.Main.version in Printf.sprintf "%d.%d.%d" x y z)
      (Filename.basename Sys.executable_name)
      Coq_config.best


(** * Initial checks by launching test coqtop processes *)

let rec read_all_lines in_chan =
  try
    let arg = input_line in_chan in
    arg::(read_all_lines in_chan)
  with End_of_file -> []

let fatal_error_popup msg =
  let popup = GWindow.message_dialog ~buttons:GWindow.Buttons.ok
    ~message_type:`ERROR ~message:msg ()
  in ignore (popup#run ()); exit 1

let final_info_popup small msg =
  if small then
    let popup = GWindow.message_dialog ~buttons:GWindow.Buttons.ok
      ~message_type:`INFO ~message:msg ()
    in
    let _ = popup#run () in
    exit 0
  else
    let popup = GWindow.dialog () in
    let button = GButton.button ~label:"ok" ~packing:popup#action_area#add ()
    in
    let scroll = GBin.scrolled_window ~hpolicy:`NEVER ~vpolicy:`AUTOMATIC
      ~packing:popup#vbox#add ~height:500 ()
    in
    let _ = GMisc.label ~text:msg ~packing:scroll#add_with_viewport () in
    let _ = popup#connect#destroy ~callback:(fun _ -> exit 0) in
    let _ = button#connect#clicked ~callback:(fun _ -> exit 0) in
    let _ = popup#run () in
    exit 0

let connection_error cmd lines exn =
  fatal_error_popup
    ("Connection with coqtop failed!\n"^
     "Command was: "^cmd^"\n"^
     "Answer was: "^(String.concat "\n  " lines)^"\n"^
     "Exception was: "^Printexc.to_string exn)

let display_coqtop_answer cmd lines =
  final_info_popup (List.length lines < 30)
    ("Coqtop exited\n"^
     "Command was: "^cmd^"\n"^
     "Answer was: "^(String.concat "\n  " lines))

let check_remaining_opt arg =
  if arg <> "" && arg.[0] = '-' then fatal_error_popup ("Illegal option: "^arg)

let rec filter_coq_opts args =
  let argstr = String.concat " " (List.map Filename.quote args) in
  let cmd = Filename.quote (coqtop_path ()) ^" -nois -filteropts " ^ argstr in
  let cmd = requote cmd in
  let filtered_args = ref [] in
  let errlines = ref [] in
  try
    let oc,ic,ec = Unix.open_process_full cmd (Unix.environment ()) in
    filtered_args := read_all_lines oc;
    errlines := read_all_lines ec;
    match Unix.close_process_full (oc,ic,ec) with
      | Unix.WEXITED 0 ->
	List.iter check_remaining_opt !filtered_args; !filtered_args
      | Unix.WEXITED 127 -> asks_for_coqtop args
      | _ -> display_coqtop_answer cmd (!filtered_args @ !errlines)
  with Sys_error _ -> asks_for_coqtop args
    | e -> connection_error cmd (!filtered_args @ !errlines) e

and asks_for_coqtop args =
  let pb_mes = GWindow.message_dialog
    ~message:"Failed to load coqtop. Reset the preference to default ?"
    ~message_type:`QUESTION ~buttons:GWindow.Buttons.yes_no () in
  match pb_mes#run () with
    | `YES ->
      let () = !Preferences.current.Preferences.cmd_coqtop  <- None in
      let () = custom_coqtop := None in
      let () = pb_mes#destroy () in
      filter_coq_opts args
    | `DELETE_EVENT | `NO ->
      let () = pb_mes#destroy () in
      let cmd_sel = GWindow.file_selection
	~title:"Coqtop to execute (edit your preference then)"
	~filename:(coqtop_path ()) ~urgency_hint:true () in
      match cmd_sel#run () with
	| `OK ->
	  let () = custom_coqtop := (Some cmd_sel#filename) in
	  let () = cmd_sel#destroy () in
	  filter_coq_opts args
	| `CANCEL | `DELETE_EVENT | `HELP -> exit 0

exception WrongExitStatus of string

let print_status = function
  | Unix.WEXITED n -> "WEXITED "^string_of_int n
  | Unix.WSIGNALED n -> "WSIGNALED "^string_of_int n
  | Unix.WSTOPPED n -> "WSTOPPED "^string_of_int n

let check_connection args =
  let lines = ref [] in
  let argstr = String.concat " " (List.map Filename.quote args) in
  let cmd = Filename.quote (coqtop_path ()) ^ " -batch " ^ argstr in
  let cmd = requote cmd in
  try
    let ic = Unix.open_process_in cmd in
    lines := read_all_lines ic;
    match Unix.close_process_in ic with
    | Unix.WEXITED 0 -> () (* coqtop seems ok *)
    | st -> raise (WrongExitStatus (print_status st))
  with e -> connection_error cmd !lines e

(** * The structure describing a coqtop sub-process *)

type coqtop = {
  pid : int; (* Unix process id *)
  cout : in_channel ;
  cin : out_channel ;
  sup_args : string list;
}

(** * Count of all active coqtops *)

let toplvl_ctr = ref 0

let toplvl_ctr_mtx = Mutex.create ()

let coqtop_zombies () =
  Mutex.lock toplvl_ctr_mtx;
  let res = !toplvl_ctr in
  Mutex.unlock toplvl_ctr_mtx;
  res


(** * Starting / signaling / ending a real coqtop sub-process *)

(** We simulate a Unix.open_process that also returns the pid of
    the created process. Note: this uses Unix.create_process, which
    doesn't call bin/sh, so args shouldn't be quoted. The process
    cannot be terminated by a Unix.close_process, but rather by a
    kill of the pid.

           >--ide2top_w--[pipe]--ide2top_r-->
    coqide                                   coqtop
           <--top2ide_r--[pipe]--top2ide_w--<

    Note: we use Unix.stderr in Unix.create_process to get debug
    messages from the coqtop's Ide_slave loop.

    NB: it's important to close coqide's descriptors (ide2top_w and top2ide_r)
    in coqtop. We do this indirectly via [Unix.set_close_on_exec].
    This way, coqide has the only remaining copies of these descriptors,
    and closing them later will have visible effects in coqtop. Cf man 7 pipe :

    - If  all file descriptors referring to the write end of a pipe have been
      closed, then an attempt to read(2) from the pipe will see end-of-file
      (read(2) will return 0).
    - If all file descriptors referring to the read end of a pipe have been
      closed, then a write(2) will cause a SIGPIPE signal to be generated for
      the calling process. If the calling process is ignoring this signal,
      then write(2) fails with the error EPIPE.

    Symmetrically, coqtop's descriptors (ide2top_r and top2ide_w) should be
    closed in coqide.
*)

let open_process_pid prog args =
  let (ide2top_r,ide2top_w) = Unix.pipe () in
  let (top2ide_r,top2ide_w) = Unix.pipe () in
  Unix.set_close_on_exec ide2top_w;
  Unix.set_close_on_exec top2ide_r;
  let pid = Unix.create_process prog args ide2top_r top2ide_w Unix.stderr in
  assert (pid <> 0);
  Unix.close ide2top_r;
  Unix.close top2ide_w;
  let oc = Unix.out_channel_of_descr ide2top_w in
  let ic = Unix.in_channel_of_descr top2ide_r in
  set_binary_mode_out oc true;
  set_binary_mode_in ic true;
  (pid,ic,oc)

let spawn_coqtop sup_args =
  Mutex.lock toplvl_ctr_mtx;
  try
    let prog = coqtop_path () in
    let args = Array.of_list (prog :: "-ideslave" :: sup_args) in
    let (pid,ic,oc) = open_process_pid prog args in
    incr toplvl_ctr;
    Mutex.unlock toplvl_ctr_mtx;
    { pid = pid; cin = oc; cout = ic ; sup_args = sup_args }
  with e ->
    Mutex.unlock toplvl_ctr_mtx;
    raise e

let respawn_coqtop coqtop = spawn_coqtop coqtop.sup_args

let interrupter = ref (fun pid -> Unix.kill pid Sys.sigint)
let killer = ref (fun pid -> Unix.kill pid Sys.sigkill)

let break_coqtop coqtop =
  try !interrupter coqtop.pid
  with _ -> prerr_endline "Error while sending Ctrl-C"

let kill_coqtop coqtop =
  let pid = coqtop.pid in
  begin
    try !killer pid
    with _ -> prerr_endline "Kill -9 failed. Process already terminated ?"
  end;
  try
    ignore (Unix.waitpid [] pid);
    Mutex.lock toplvl_ctr_mtx; decr toplvl_ctr; Mutex.unlock toplvl_ctr_mtx
  with _ -> prerr_endline "Error while waiting for child"

(** * Calls to coqtop *)

(** Cf [Ide_intf] for more details *)

let p = Xml_parser.make ()
let () = Xml_parser.check_eof p false

let eval_call coqtop (c:'a Ide_intf.call) =
  Xml_utils.print_xml coqtop.cin (Ide_intf.of_call c);
  flush coqtop.cin;
  let xml = Xml_parser.parse p (Xml_parser.SChannel coqtop.cout) in
  (Ide_intf.to_answer xml c : 'a Interface.value)

let interp coqtop ?(raw=false) ?(verbose=true) s =
  eval_call coqtop (Ide_intf.interp (raw,verbose,s))
let rewind coqtop i = eval_call coqtop (Ide_intf.rewind i)
let inloadpath coqtop s = eval_call coqtop (Ide_intf.inloadpath s)
let mkcases coqtop s = eval_call coqtop (Ide_intf.mkcases s)
let status coqtop = eval_call coqtop Ide_intf.status
let hints coqtop = eval_call coqtop Ide_intf.hints

module PrintOpt =
struct
  type t = string list
  let implicit = ["Printing"; "Implicit"]
  let coercions = ["Printing"; "Coercions"]
  let raw_matching = ["Printing"; "Matching"; "Synth"]
  let notations = ["Printing"; "Notations"]
  let all_basic = ["Printing"; "All"]
  let existential = ["Printing"; "Existential"; "Instances"]
  let universes = ["Printing"; "Universes"]

  let state_hack = Hashtbl.create 11
  let _ = List.iter (fun opt -> Hashtbl.add state_hack opt false)
            [ implicit; coercions; raw_matching; notations; all_basic; existential; universes ]

  let set coqtop options =
    let () = List.iter (fun (name, v) -> Hashtbl.replace state_hack name v) options in
    let options = List.map (fun (name, v) -> (name, Interface.BoolValue v)) options in
    match eval_call coqtop (Ide_intf.set_options options) with
    | Interface.Good () -> ()
    | _ -> raise (Failure "Cannot set options.")

  let enforce_hack coqtop =
    let elements = Hashtbl.fold (fun opt v acc -> (opt, v) :: acc) state_hack [] in
    set coqtop elements

end

let goals coqtop =
  let () = PrintOpt.enforce_hack coqtop in
  eval_call coqtop Ide_intf.goals

let evars coqtop =
  let () = PrintOpt.enforce_hack coqtop in
  eval_call coqtop Ide_intf.evars
