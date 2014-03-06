(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* File created around Apr 1994 for CiC V5.10.5 by Chet Murthy collecting
   parts of file initial.ml from CoC V4.8, Dec 1988, by Gérard Huet,
   Thierry Coquand and Christine Paulin *)
(* Hash-consing by Bruno Barras in Feb 1998 *)
(* Extra functions for splitting/generation of identifiers by Hugo Herbelin *)
(* Restructuration by Jacek Chrzaszcz as part of the implementation of
   the module system, Aug 2002 *)
(* Abstraction over the type of constant for module inlining by Claudio
   Sacerdoti, Nov 2004 *)
(* Miscellaneous features or improvements by Hugo Herbelin, 
   Élie Soubiran, ... *)

open Pp
open Util

(** {6 Identifiers } *)

type identifier = string

let id_of_string s = check_ident_soft s; String.copy s
let string_of_id id = String.copy id

let id_ord = Pervasives.compare

module IdOrdered =
  struct
    type t = identifier
    let compare = id_ord
  end

module Idset = Set.Make(IdOrdered)
module Idmap =
struct
  include Map.Make(IdOrdered)
  exception Finded
  let exists f m =
    try iter (fun a b -> if f a b then raise Finded) m ; false
    with |Finded -> true
  let singleton k v = add k v empty
end
module Idpred = Predicate.Make(IdOrdered)

(** {6 Various types based on identifiers } *)

type name = Name of identifier | Anonymous
type variable = identifier

(** {6 Directory paths = section names paths } *)

(** Dirpaths are lists of module identifiers.
    The actual representation is reversed to optimise sharing:
    Coq.A.B is ["B";"A";"Coq"] *)

type module_ident = identifier
type dir_path = module_ident list

module ModIdmap = Idmap

let make_dirpath x = x
let repr_dirpath x = x

let empty_dirpath = []

(** Printing of directory paths as ["coq_root.module.submodule"] *)

let string_of_dirpath = function
  | [] -> "<>"
  | sl -> String.concat "." (List.map string_of_id (List.rev sl))

(** {6 Unique names for bound modules } *)

let u_number = ref 0
type uniq_ident = int * identifier * dir_path
let make_uid dir s = incr u_number;(!u_number,s,dir)
 let debug_string_of_uid (i,s,p) =
 "<"(*^string_of_dirpath p ^"#"^*) ^ s ^"#"^ string_of_int i^">"
let string_of_uid (i,s,p) =
  string_of_dirpath p ^"."^s

module Umap = Map.Make(struct
			 type t = uniq_ident
			 let compare = Pervasives.compare
		       end)

type mod_bound_id = uniq_ident
let make_mbid = make_uid
let repr_mbid (n, id, dp) = (n, id, dp)
let debug_string_of_mbid = debug_string_of_uid
let string_of_mbid = string_of_uid
let id_of_mbid (_,s,_) = s

(** {6 Names of structure elements } *)

type label = identifier

let mk_label = id_of_string
let string_of_label = string_of_id
let pr_label l = str (string_of_label l)
let id_of_label l = l
let label_of_id id = id

module Labset = Idset
module Labmap = Idmap

(** {6 The module part of the kernel name } *)

type module_path =
  | MPfile of dir_path
  | MPbound of mod_bound_id
  | MPdot of module_path * label

let rec check_bound_mp = function
  | MPbound _ -> true
  | MPdot(mp,_) ->check_bound_mp mp
  | _ -> false

let rec string_of_mp = function
  | MPfile sl -> string_of_dirpath sl
  | MPbound uid -> string_of_uid uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

(** we compare labels first if both are MPdots *)
let rec mp_ord mp1 mp2 = match (mp1,mp2) with
    MPdot(mp1,l1), MPdot(mp2,l2) ->
      let c = Pervasives.compare l1 l2 in
	if c<>0 then
	  c
	else
	  mp_ord mp1 mp2
  |  _,_ -> Pervasives.compare mp1 mp2

module MPord = struct
  type t = module_path
  let compare = mp_ord
end

module MPset = Set.Make(MPord)
module MPmap = Map.Make(MPord)

let default_module_name = "If you see this, it's a bug"

let initial_dir = make_dirpath [default_module_name]
let initial_path = MPfile initial_dir

(** {6 Kernel names } *)

type kernel_name = module_path * dir_path * label

let make_kn mp dir l = (mp,dir,l)
let repr_kn kn = kn

let modpath kn =
  let mp,_,_ = repr_kn kn in mp

let label kn =
  let _,_,l = repr_kn kn in l

let string_of_kn (mp,dir,l) =
  let str_dir = if dir = [] then "." else "#" ^ string_of_dirpath dir ^ "#"
  in
  string_of_mp mp ^ str_dir ^ string_of_label l

let pr_kn kn = str (string_of_kn kn)

let kn_ord kn1 kn2 =
    let mp1,dir1,l1 = kn1 in
    let mp2,dir2,l2 = kn2 in
    let c = Pervasives.compare l1 l2 in
      if c <> 0 then
	c
      else
	let c = Pervasives.compare dir1 dir2 in
	  if c<>0 then
	    c
	  else
	    MPord.compare mp1 mp2

module KNord = struct
  type t = kernel_name
  let compare = kn_ord
end

module KNmap = Map.Make(KNord)
module KNpred = Predicate.Make(KNord)
module KNset = Set.Make(KNord)

(** {6 Constant names } *)

(** a constant name is a kernel name couple (kn1,kn2)
   where kn1 corresponds to the name used at toplevel
   (i.e. what the user see)
   and kn2 corresponds to the canonical kernel name
   i.e. in the environment we have
   kn1 \rhd_{\delta}^* kn2 \rhd_{\delta} t *)
type constant = kernel_name*kernel_name

let constant_of_kn kn = (kn,kn)
let constant_of_kn_equiv kn1 kn2 = (kn1,kn2)
let make_con mp dir l = constant_of_kn (mp,dir,l)
let make_con_equiv mp1 mp2 dir l =
  if mp1 == mp2 then make_con mp1 dir l
  else ((mp1,dir,l),(mp2,dir,l))
let canonical_con con = snd con
let user_con con = fst con
let repr_con con = fst con

let eq_constant (_,kn1) (_,kn2) = kn1=kn2

let con_label con = label (fst con)
let con_modpath con = modpath (fst con)

let string_of_con con = string_of_kn (fst con)
let pr_con con = str (string_of_con con)
let debug_string_of_con con =
  "(" ^ string_of_kn (fst con) ^ "," ^ string_of_kn (snd con) ^ ")"
let debug_pr_con con = str (debug_string_of_con con)

let con_with_label ((mp1,dp1,l1),(mp2,dp2,l2) as con) lbl =
  if lbl = l1 && lbl = l2 then con
  else ((mp1,dp1,lbl),(mp2,dp2,lbl))

(** For the environment we distinguish constants by their user part*)
module User_ord = struct
  type t = kernel_name*kernel_name
  let compare x y= kn_ord (fst x) (fst y)
end

(** For other uses (ex: non-logical things) it is enough
    to deal with the canonical part *)
module Canonical_ord = struct
  type t = kernel_name*kernel_name
  let compare x y= kn_ord (snd x) (snd y)
end

module Cmap = Map.Make(Canonical_ord)
module Cmap_env = Map.Make(User_ord)
module Cpred = Predicate.Make(Canonical_ord)
module Cset = Set.Make(Canonical_ord)
module Cset_env = Set.Make(User_ord)


(** {6 Names of mutual inductive types } *)

(** The same thing is done for mutual inductive names
    it replaces also the old mind_equiv field of mutual
    inductive types *)
(** Beware: first inductive has index 0 *)
(** Beware: first constructor has index 1 *)

type mutual_inductive = kernel_name*kernel_name
type inductive = mutual_inductive * int
type constructor = inductive * int

let mind_modpath mind = modpath (fst mind)
let ind_modpath ind = mind_modpath (fst ind)
let constr_modpath c = ind_modpath (fst c)

let mind_of_kn kn = (kn,kn)
let mind_of_kn_equiv kn1 kn2 = (kn1,kn2)
let make_mind mp dir l = mind_of_kn (mp,dir,l)
let make_mind_equiv mp1 mp2 dir l =
  if mp1 == mp2 then make_mind mp1 dir l
  else ((mp1,dir,l),(mp2,dir,l))
let canonical_mind mind = snd mind
let user_mind mind = fst mind
let repr_mind mind = fst mind
let mind_label mind= label (fst mind)

let eq_mind (_,kn1) (_,kn2) = kn1=kn2

let string_of_mind mind = string_of_kn (fst mind)
let pr_mind mind = str (string_of_mind mind)
let debug_string_of_mind mind =
  "(" ^ string_of_kn (fst mind) ^ "," ^ string_of_kn (snd mind) ^ ")"
let debug_pr_mind con = str (debug_string_of_mind con)

let ith_mutual_inductive (kn,_) i = (kn,i)
let ith_constructor_of_inductive ind i = (ind,i)
let inductive_of_constructor (ind,i) = ind
let index_of_constructor (ind,i) = i
let eq_ind (kn1,i1) (kn2,i2) = i1=i2&&eq_mind kn1 kn2
let eq_constructor (kn1,i1) (kn2,i2) = i1=i2&&eq_ind kn1 kn2

module Mindmap = Map.Make(Canonical_ord)
module Mindset = Set.Make(Canonical_ord)
module Mindmap_env = Map.Make(User_ord)

module InductiveOrdered = struct
  type t = inductive
  let compare (spx,ix) (spy,iy) =
    let c = ix - iy in if c = 0 then Canonical_ord.compare spx spy else c
end

module InductiveOrdered_env = struct
  type t = inductive
  let compare (spx,ix) (spy,iy) =
    let c = ix - iy in if c = 0 then User_ord.compare spx spy else c
end

module Indmap = Map.Make(InductiveOrdered)
module Indmap_env = Map.Make(InductiveOrdered_env)

module ConstructorOrdered = struct
  type t = constructor
  let compare (indx,ix) (indy,iy) =
    let c = ix - iy in if c = 0 then InductiveOrdered.compare indx indy else c
end

module ConstructorOrdered_env = struct
  type t = constructor
  let compare (indx,ix) (indy,iy) =
    let c = ix - iy in if c = 0 then InductiveOrdered_env.compare indx indy else c
end

module Constrmap = Map.Make(ConstructorOrdered)
module Constrmap_env = Map.Make(ConstructorOrdered_env)

(* Better to have it here that in closure, since used in grammar.cma *)
type evaluable_global_reference =
  | EvalVarRef of identifier
  | EvalConstRef of constant

let eq_egr e1 e2 = match e1,e2 with
    EvalConstRef con1, EvalConstRef con2 -> eq_constant con1 con2
  | _,_ -> e1 = e2

(** {6 Hash-consing of name objects } *)

module Hname = Hashcons.Make(
  struct
    type t = name
    type u = identifier -> identifier
    let hash_sub hident = function
      | Name id -> Name (hident id)
      | n -> n
    let equal n1 n2 =
      match (n1,n2) with
	| (Name id1, Name id2) -> id1 == id2
        | (Anonymous,Anonymous) -> true
        | _ -> false
    let hash = Hashtbl.hash
  end)

module Hdir = Hashcons.Make(
  struct
    type t = dir_path
    type u = identifier -> identifier
    let hash_sub hident d = list_smartmap hident d
    let rec equal d1 d2 = match (d1,d2) with
      | [],[] -> true
      | id1::d1,id2::d2 -> id1 == id2 & equal d1 d2
      | _ -> false
    let hash = Hashtbl.hash
  end)

module Huniqid = Hashcons.Make(
  struct
    type t = uniq_ident
    type u = (identifier -> identifier) * (dir_path -> dir_path)
    let hash_sub (hid,hdir) (n,s,dir) = (n,hid s,hdir dir)
    let equal (n1,s1,dir1) (n2,s2,dir2) = n1 = n2 && s1 == s2 && dir1 == dir2
    let hash = Hashtbl.hash
  end)

module Hmod = Hashcons.Make(
  struct
    type t = module_path
    type u = (dir_path -> dir_path) * (uniq_ident -> uniq_ident) *
	(string -> string)
    let rec hash_sub (hdir,huniqid,hstr as hfuns) = function
      | MPfile dir -> MPfile (hdir dir)
      | MPbound m -> MPbound (huniqid m)
      | MPdot (md,l) -> MPdot (hash_sub hfuns md, hstr l)
    let rec equal d1 d2 = match (d1,d2) with
      | MPfile dir1, MPfile dir2 -> dir1 == dir2
      | MPbound m1, MPbound m2 -> m1 == m2
      | MPdot (mod1,l1), MPdot (mod2,l2) -> l1 == l2 && equal mod1 mod2
      | _ -> false
    let hash = Hashtbl.hash
  end)

module Hkn = Hashcons.Make(
  struct
    type t = kernel_name
    type u = (module_path -> module_path)
	* (dir_path -> dir_path) * (string -> string)
    let hash_sub (hmod,hdir,hstr) (md,dir,l) =
      (hmod md, hdir dir, hstr l)
    let equal (mod1,dir1,l1) (mod2,dir2,l2) =
      mod1 == mod2 && dir1 == dir2 && l1 == l2
    let hash = Hashtbl.hash
  end)

(** For [constant] and [mutual_inductive], we discriminate only on
    the user part : having the same user part implies having the
    same canonical part (invariant of the system). *)

module Hcn = Hashcons.Make(
  struct
    type t = kernel_name*kernel_name
    type u = kernel_name -> kernel_name
    let hash_sub hkn (user,can) = (hkn user, hkn can)
    let equal (user1,_) (user2,_) = user1 == user2
    let hash (user,_) = Hashtbl.hash user
  end)

module Hind = Hashcons.Make(
  struct
    type t = inductive
    type u = mutual_inductive -> mutual_inductive
    let hash_sub hmind (mind, i) = (hmind mind, i)
    let equal (mind1,i1) (mind2,i2) = mind1 == mind2 && i1 = i2
    let hash = Hashtbl.hash
  end)

module Hconstruct = Hashcons.Make(
  struct
    type t = constructor
    type u = inductive -> inductive
    let hash_sub hind (ind, j) = (hind ind, j)
    let equal (ind1,j1) (ind2,j2) = ind1 == ind2 && j1 = j2
    let hash = Hashtbl.hash
  end)

let hcons_string = Hashcons.simple_hcons Hashcons.Hstring.f ()
let hcons_ident = hcons_string
let hcons_name = Hashcons.simple_hcons Hname.f hcons_ident
let hcons_dirpath = Hashcons.simple_hcons Hdir.f hcons_ident
let hcons_uid = Hashcons.simple_hcons Huniqid.f (hcons_ident,hcons_dirpath)
let hcons_mp =
  Hashcons.simple_hcons Hmod.f (hcons_dirpath,hcons_uid,hcons_string)
let hcons_kn = Hashcons.simple_hcons Hkn.f (hcons_mp,hcons_dirpath,hcons_string)
let hcons_con = Hashcons.simple_hcons Hcn.f hcons_kn
let hcons_mind = Hashcons.simple_hcons Hcn.f hcons_kn
let hcons_ind = Hashcons.simple_hcons Hind.f hcons_mind
let hcons_construct = Hashcons.simple_hcons Hconstruct.f hcons_ind


(*******)

type transparent_state = Idpred.t * Cpred.t

let empty_transparent_state = (Idpred.empty, Cpred.empty)
let full_transparent_state = (Idpred.full, Cpred.full)
let var_full_transparent_state = (Idpred.full, Cpred.empty)
let cst_full_transparent_state = (Idpred.empty, Cpred.full)

type 'a tableKey =
  | ConstKey of constant
  | VarKey of identifier
  | RelKey of 'a


type inv_rel_key = int (* index in the [rel_context] part of environment
			  starting by the end, {\em inverse}
			  of de Bruijn indice *)

type id_key = inv_rel_key tableKey

let eq_id_key ik1 ik2 =
  match ik1,ik2 with
    ConstKey (_,kn1),
      ConstKey (_,kn2) -> kn1=kn2
    | a,b -> a=b

let eq_con_chk (kn1,_) (kn2,_) = kn1=kn2
let eq_mind_chk (kn1,_) (kn2,_) = kn1=kn2
let eq_ind_chk (kn1,i1) (kn2,i2) = i1=i2&&eq_mind_chk kn1 kn2
