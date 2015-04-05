(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: csymtable.mli 15714 2012-08-08 18:54:37Z herbelin $ *)

open Names
open Term
open Pre_env

val val_of_constr : env -> constr -> values

val set_opaque_const      : constant -> unit
val set_transparent_const : constant -> unit
