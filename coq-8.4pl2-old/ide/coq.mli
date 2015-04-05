(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Coq : Interaction with the Coq toplevel *)

(** * Version and date *)

val short_version : unit -> string
val version : unit -> string

(** * Launch a test coqtop processes, ask for a correct coqtop if it fails.
    @return the list of arguments that coqtop did not understand
    (the files probably ..). This command may terminate coqide in
    case of trouble.  *)
val filter_coq_opts : string list -> string list

(** Launch a coqtop with the user args in order to be sure that it works,
    checking in particular that initial.coq is found. This command
    may terminate coqide in case of trouble *)
val check_connection : string list -> unit

(** * The structure describing a coqtop sub-process *)

type coqtop

(** * Count of all active coqtops *)

val coqtop_zombies : unit -> int

(** * Starting / signaling / ending a real coqtop sub-process *)

val spawn_coqtop : string list -> coqtop
val respawn_coqtop : coqtop -> coqtop
val kill_coqtop : coqtop -> unit
val break_coqtop : coqtop -> unit

(** In win32, we'll use a different kill function than Unix.kill *)

val killer : (int -> unit) ref
val interrupter : (int -> unit) ref

(** * Calls to Coqtop, cf [Ide_intf] for more details *)

val interp :
  coqtop -> ?raw:bool -> ?verbose:bool -> string -> string Interface.value
val rewind : coqtop -> int -> int Interface.value
val status : coqtop -> Interface.status Interface.value
val goals : coqtop -> Interface.goals option Interface.value
val evars : coqtop -> Interface.evar list option Interface.value
val hints : coqtop -> (Interface.hint list * Interface.hint) option Interface.value
val inloadpath : coqtop -> string -> bool Interface.value
val mkcases : coqtop -> string -> string list list Interface.value

(** A specialized version of [raw_interp] dedicated to
    set/unset options. *)

module PrintOpt :
sig
  type t
  val implicit : t
  val coercions : t
  val raw_matching : t
  val notations : t
  val all_basic : t
  val existential : t
  val universes : t

  val set : coqtop -> (t * bool) list -> unit
end
