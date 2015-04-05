
open Pp
open Util
open Names
open Nameops
open Libnames

open Table
open Miniml
open Mlutil
open Modutil
open Common

type ml_branch' = ml_ident list * ml_pattern * ml_ast'

and ml_ast' =
  | MLrel'    of int * ml_type list
  | MLapp'    of ml_ast' * ml_ast' list
  | MLlam'    of ml_ident * ml_type * ml_ast'
  | MLletin'  of ml_ident * ml_schema * ml_ast' * ml_ast'
  | MLglob'   of global_reference * ml_type list
  | MLcons'   of ml_type * global_reference * ml_ast' list
  | MLtuple'  of ml_ast' list
  | MLcase'   of ml_type * ml_ast' * ml_branch' array
  | MLfix'    of int * (identifier * ml_type) array * ml_ast' array
  | MLexn'    of string
  | MLdummy'
  | MLaxiom'
  | MLmagic'  of ml_ast' * ml_type

let refenv = ref []
let reset_refenv () = refenv := []
let set_refenv sts = 
  let sgs = signature_of_structure sts in
  let rec set_refenv_aux = function 
    | [] -> []
    | (_, Spec spc) :: sgs' -> spc :: (set_refenv_aux sgs')
    | _ :: sgs' -> set_refenv_aux sgs'
  in
  refenv := List.flatten (List.map (fun (_, sg) -> set_refenv_aux sg) sgs)
let add_refenv new_ev = refenv := new_ev @ !refenv

let add_var e c = e :: c

let collect_lams' =
  let rec collect acc = function
    | MLlam' (id,ty,t) -> collect ((id,ty)::acc) t
    | x           -> acc,x
  in collect []

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl tl'))


let free_type_vars typ =
  let module S = Set.Make(struct type t = int let compare = compare end) in
  let rec iter = function
    | Tmeta _ | Tvar' _ -> S.empty
    | Tvar (i:int) ->  S.singleton i
    | Tglob ((r: global_reference), (l: ml_type list)) ->
	List.fold_left (fun store typ ->
	  S.union store (iter typ)) S.empty l
    | Tarr (t1,t2) ->
	S.union (iter t1) (iter t2)
    | Tdummy _
    | Tunknown
    | Taxiom -> S.empty
  in
  S.elements (iter typ)

let rec subst_mlt_one s = function
  | Tarr (t1, t2) -> Tarr (subst_mlt_one s t1, subst_mlt_one s t2)
  | Tglob (r, ts) -> Tglob (r, List.map (subst_mlt_one s) ts)
  | Tmeta m when m.id = fst s -> snd s
  | t -> t
let rec subst_mlt ss ty = 
  match ss with
  | [] -> ty
  | h :: ss' -> subst_mlt ss' (subst_mlt_one h ty)

let subst_mlt_all ss ty = subst_mlt (List.flatten ss) ty

let subst_constrs s cs = 
  List.map (fun (t1, t2) -> (subst_mlt s t1, subst_mlt s t2)) cs

let rec alias_of r = 
  let rec alias_of_iter = function
  | [] -> None 
  | Stype (r', _, Some ty) :: _ when eq_gr r r' -> Some ty
  | _ :: tl -> alias_of_iter tl
  in alias_of_iter !refenv

let is_singleton mi = 
  let rec is_singleton_iter = function
    | [] -> false
    | Sind (mi', mind) :: tl when eq_mind mi mi' ->
        (match mind.ind_kind with 
        | Singleton -> true
        | _ -> false)
    | _ :: tl -> is_singleton_iter tl
  in is_singleton_iter !refenv

let rec elim_singleton = function
  | Tarr (s, t) -> 
      Tarr (elim_singleton s, elim_singleton t)
  | Tglob (IndRef (mi, _), [t]) when is_singleton mi ->
      elim_singleton t
  | Tglob (r, ts) -> 
      let ts' = List.map elim_singleton ts in
      (match alias_of r with 
      | None | Some Taxiom -> Tglob (r, ts')
      | Some t -> elim_singleton (type_subst_list ts' t))
  | t -> t

let rec unify = function
  | [] -> []
  | (a, b) :: cs' ->
     match elim_singleton a, elim_singleton b with
     | Tmeta m, Tmeta m' when m.id = m'.id -> unify cs'
     | Tmeta m, t | t, Tmeta m ->
         let s = (m.id, t) in
         s :: unify (subst_constrs [s] cs')
     | Tarr(a, b), Tarr(a', b') ->
         unify ((a, a') :: (b, b') :: cs')
     | Tglob (r,l), Tglob (r',l') when r = r' ->
         unify ((combine l l') @ cs')
     | Tdummy _, Tdummy _ | Tunknown, Tunknown | Taxiom, Taxiom -> unify cs'
     | Tvar i, Tvar j | Tvar i, Tvar' j | Tvar' i, Tvar j | Tvar' i, Tvar' j -> 
         if i=j then unify cs' 
         else assert false
     | t, u -> assert false

let rec type_of_ref r = function
  | [] -> None
  | (Sval (r', ty)) :: tl when eq_gr r r'-> Some ty
  | _ :: tl -> type_of_ref r tl

let rec mind_of_cons mi = function
  | [] -> None
  | (Sind (mi', mind)) :: _ when eq_mind mi mi' -> Some mind
  | _ :: tl -> mind_of_cons mi tl

let type_of_cons mind i j = 
  mind.ind_packets.(i).ip_types.(j-1)

(* ---------------------------------------------------------------------------------------- *)

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, y) -> x

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| y :: l' -> Pervasives.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val pred : int -> int **)

let pred = fun n -> Pervasives.max 0 (n-1)

(** val plus : int -> int -> int **)

let rec plus = (+)

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    match l with
    | [] -> default
    | x :: l' -> x)
    (fun m ->
    match l with
    | [] -> default
    | x :: t -> nth m t default)
    n

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

type 'a set = 'a list

(** val empty_set : 'a1 set **)

let empty_set =
  []

(** val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| [] -> a :: []
| a1 :: x1 -> if aeq_dec a a1 then a1 :: x1 else a1 :: (set_add aeq_dec a x1)

(** val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
| [] -> false
| a1 :: x1 -> if aeq_dec a a1 then true else set_mem aeq_dec a x1

(** val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x = function
| [] -> x
| a1 :: y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)

(** val set_diff : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_diff aeq_dec x y =
  match x with
  | [] -> []
  | a1 :: x1 ->
    if set_mem aeq_dec a1 y
    then set_diff aeq_dec x1 y
    else set_add aeq_dec a1 (set_diff aeq_dec x1 y)

(** val ind_nparams : ml_ind -> int **)

let ind_nparams x = x.ind_nparams

(** val mk_meta : int -> ml_type **)

let mk_meta m =
  Tmeta {id=m; contents=None}

(** val mk_meta_list : int list -> ml_type list **)

let mk_meta_list ms =
  map mk_meta ms

(** val get_meta : ml_meta -> int **)

let get_meta m =
  m

(** val beq_id : identifier -> identifier -> bool **)

let beq_id =
  (=)

(** val beq_kn : kernel_name -> kernel_name -> bool **)

let beq_kn =
  beq_id

(** val beq_var : variable -> variable -> bool **)

let beq_var =
  beq_id

(** val beq_const : constant -> constant -> bool **)

let beq_const =
  beq_kn

(** val beq_mind : mutual_inductive -> mutual_inductive -> bool **)

let beq_mind =
  beq_kn

(** val beq_ind : inductive -> inductive -> bool **)

let beq_ind i1 i2 =
  let (mi1, n1) = i1 in
  let (mi2, n2) = i2 in (&&) (beq_mind mi1 mi2) ((=) n1 n2)

(** val beq_construct : constructor -> constructor -> bool **)

let beq_construct c1 c2 =
  let (i1, n1) = c1 in let (i2, n2) = c2 in (&&) (beq_ind i1 i2) ((=) n1 n2)

(** val beq_ref : global_reference -> global_reference -> bool **)

let beq_ref gr1 gr2 =
  match gr1 with
  | VarRef v1 ->
    (match gr2 with
     | VarRef v2 -> beq_var v1 v2
     | _ -> false)
  | ConstRef c1 ->
    (match gr2 with
     | ConstRef c2 -> beq_const c1 c2
     | _ -> false)
  | IndRef i1 ->
    (match gr2 with
     | IndRef i2 -> beq_ind i1 i2
     | _ -> false)
  | ConstructRef c1 ->
    (match gr2 with
     | ConstructRef c2 -> beq_construct c1 c2
     | _ -> false)

type inf_env = ml_type list

type subst = (int * ml_type) list

(** val subst_env : subst -> inf_env -> inf_env **)

let subst_env s e =
  map (subst_mlt s) e

(** val add_env : ml_type -> inf_env -> inf_env **)

let add_env mlt e =
  mlt :: e

(** val opt_max : int option -> int option -> int option **)

let opt_max o o' =
  match o with
  | Some n ->
    (match o' with
     | Some n' -> Some (Pervasives.max n n')
     | None -> Some n)
  | None -> o'

(** val max_tyvar : ml_type -> int option **)

let rec max_tyvar = function
| Tarr (t1, t2) -> opt_max (max_tyvar t1) (max_tyvar t2)
| Tglob (g, tys) -> fold_right opt_max None (map max_tyvar tys)
| Tvar i -> Some i
| _ -> None

(** val free_vars : ml_type -> int set **)

let rec free_vars = function
| Tarr (t1, t2) -> set_union (=) (free_vars t1) (free_vars t2)
| Tglob (r, ts) -> fold_right (set_union (=)) empty_set (map free_vars ts)
| Tmeta m -> set_add (=) (get_meta m.id) empty_set
| _ -> empty_set

(** val mk_subst : int list -> int -> (int * ml_type) list **)

let rec mk_subst l n =
  match l with
  | [] -> []
  | h :: t -> (h, (Tvar n)) :: (mk_subst t (Pervasives.succ n))

(** val gen : inf_env -> ml_type -> ml_type **)
let gen c mlt =
  let vs =
    fold_right (fun a b -> set_diff (=) b a) (free_vars mlt)
      (map free_vars c)
  in
  subst_mlt (mk_subst vs 0) mlt

(** val instantiation : ml_type list -> ml_type -> ml_type **)

let rec instantiation l ty = match ty with
| Tarr (ty1, ty2) -> Tarr ((instantiation l ty1), (instantiation l ty2))
| Tglob (r, tys) -> Tglob (r, (map (instantiation l) tys))
| Tvar i -> nth (i-1) l ty
| _ -> ty

(** val inst_with_meta : int list -> ml_type -> ml_type **)

let inst_with_meta l ty =
  instantiation (mk_meta_list l) ty

(** val lookup : int -> inf_env -> ml_type option **)

let rec lookup n = function
| [] -> None
| ty :: c' ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> Some
     ty)
     (fun m ->
     lookup m c')
     n)

type global_env = ml_spec list

(** val type_recomp_aux : ml_type list -> ml_type -> ml_type **)

let rec type_recomp_aux l t =
  match l with
  | [] -> t
  | a :: b -> Tarr (a, (type_recomp_aux b t))

(** val type_recomp : (ml_type list * ml_type) -> ml_type **)

let type_recomp = function
| (l, t) -> type_recomp_aux l t

(** val ge : global_env **)
(*
let ge =
  failwith "AXIOM TO BE REALIZED"
*)
(** val add_env_all : ml_type list -> ml_type list -> inf_env **)

let rec add_env_all c ps = 
  List.rev_append ps c

(** val unify : (ml_type * ml_type) list -> subst **)
(*
let unify =
  failwith "AXIOM TO BE REALIZED"
*)
(** val new_meta : int -> int * int **)

let new_meta m =
  ((plus m (Pervasives.succ 0)),
    (plus m (Pervasives.succ (Pervasives.succ 0))))

(** val new_meta_list_aux : int -> int -> int list **)

let rec new_meta_list_aux l m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    [])
    (fun l' ->
    (plus m (Pervasives.succ 0)) :: (new_meta_list_aux l'
                                      (plus m (Pervasives.succ 0))))
    l

(** val new_meta_list : int -> int -> int list * int **)

let new_meta_list l m =
  ((new_meta_list_aux l m), (plus (plus m l) (Pervasives.succ 0)))

(** val infer_list :
    (ml_ast * ml_type) list -> (ml_ast -> __ -> ml_type -> int -> inf_env ->
    __ -> __ -> __ -> ((int * subst) * ml_ast')) -> int -> (ml_ast * ml_type)
    list -> int -> inf_env -> ((int * subst) * (ml_ast' * ml_type) list) **)

let rec infer_list etys0 f l etys m c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    match etys with
    | [] -> (((Pervasives.succ m), []), [])
    | p :: etys1 -> assert false (* absurd case *))
    (fun n ->
    match etys with
    | [] -> assert false (* absurd case *)
    | p :: x ->
      let (e, ty) = p in
      let s = f e __ ty m c __ __ __ in
      let (p0, x0) = s in
      let (m1, s1) = p0 in
      let etys2 =
        map (fun p1 -> let (e0, ty0) = p1 in (e0, (subst_mlt s1 ty0))) x
      in
      let s0 = infer_list etys0 f n etys2 m1 (subst_env s1 c) in
      let (p1, x1) = s0 in
      let (m2, s2) = p1 in ((m2, (app s1 s2)), ((x0, ty) :: x1)))
    l

(** val infer_branch :
    ml_ast -> (ml_ident list * (ml_pattern * ml_ast)) array -> ml_type list
    -> mutual_inductive -> int -> (ml_ident list * (ml_pattern * ml_ast))
    list -> ml_type -> inf_env -> ml_type list -> int -> (ml_ast -> __ ->
    ml_type -> int -> inf_env -> __ -> __ -> __ -> ((int * subst) * ml_ast'))
    -> ((int * subst) * (ml_ident list * (ml_pattern * ml_ast')) list) **)

let rec infer_branch z0 bs0 tys0 mi k bs ty c tvars m f =
  match bs with
  | [] -> (((Pervasives.succ m), []), [])
  | y :: l ->
    let (xs, p) = y in
    let (p0, e) = p in
    let c' =
      match p0 with
      | Prel n ->
        ((fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           c)
           (fun n0 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ ->
             add_env (Tglob ((IndRef (mi, k)), tvars)) c)
             (fun n1 ->
             c)
             n0)
           n)
      | Pusual g ->
        (match g with
         | ConstructRef c0 ->
           let (i, j) = c0 in
           let (mi0, k0) = i in
           (match mind_of_cons mi0 !refenv with
            | Some mind ->
              add_env_all c
                (map (instantiation tvars) (type_of_cons mind k0 j))
            | None -> c)
         | _ -> c)
      | _ -> c
    in
    let s = f e __ ty m c' __ __ __ in
    let (p1, x) = s in
    let (m1, s1) = p1 in
    let s0 =
      infer_branch z0 bs0 tys0 mi k l (subst_mlt s1 ty) (subst_env s1 c)
        (map (subst_mlt s1) tvars) m1 f
    in
    let (p2, x0) = s0 in
    let (m2, s2) = p2 in ((m2, (app s1 s2)), ((xs, (p0, x)) :: x0))

(** val infer :
    ml_ast -> ml_type -> int -> inf_env -> ((int * subst) * ml_ast') **)

let infer mle mlt curr_m c =
  let rec f x =
    let h = fun y -> f y in
    (fun mlt0 curr_m0 c0 _ _ _ ->
    match x with
    | MLrel i ->
      let tx = lookup (pred i) c0 in
      (match tx with
       | Some tx0 ->
         let n =
           match max_tyvar tx0 with
           | Some n -> n
           | None -> 0
         in
         let p = new_meta_list n curr_m0 in
         let (ms, next_m) = p in
         let u = unify ((mlt0, (inst_with_meta ms tx0)) :: []) in
         let tvars' = map (fun m -> subst_mlt u (mk_meta m)) ms in
         ((next_m, u), (MLrel' (i, tvars')))
       | None -> assert false (* absurd case *))
    | MLapp (mle1, mle2) ->
      let l = length mle2 in
      let p = new_meta_list l curr_m0 in
      let (ms, next_m) = p in
      let tya = type_recomp ((mk_meta_list ms), mlt0) in
      let ret1 = h mle1 tya next_m c0 __ __ __ in
      let (p0, x0) = ret1 in
      let (m1, s1) = p0 in
      let tybs = map (subst_mlt s1) (mk_meta_list ms) in
      let etys = combine mle2 tybs in
      let f0 = fun mle0 -> h mle0 in
      let s =
        infer_list etys (fun mle0 _ -> f0 mle0) l etys m1 (subst_env s1 c0)
      in
      let (p1, x1) = s in
      let (m2, s2) = p1 in
      ((m2, (app s1 s2)), (MLapp' (x0, (map (fun p2 -> fst p2) x1))))
    | MLlam (x0, e) ->
      let pa = new_meta curr_m0 in
      let (ta, ma) = pa in
      let pb = new_meta ma in
      let (tb, mb) = pb in
      let u = unify ((mlt0, (Tarr ((mk_meta ta), (mk_meta tb)))) :: []) in
      let s =
        h e (subst_mlt u (mk_meta tb)) mb
          (subst_env u (add_env (mk_meta ta) c0)) __ __ __
      in
      let (p, x1) = s in
      let (m', s') = p in
      ((m', (app u s')), (MLlam' (x0, (subst_mlt (app u s') (mk_meta ta)),
      x1)))
    | MLletin (x0, mle1, mle2) ->
      let p = new_meta curr_m0 in
      let (ta, next_m) = p in
      let s = h mle1 (mk_meta ta) next_m c0 __ __ __ in
      let (p0, x1) = s in
      let (m1, s1) = p0 in
      let s0 =
        h mle2 (subst_mlt s1 mlt0) m1
          (add_env (gen (subst_env s1 c0) (subst_mlt s1 (mk_meta ta)))
            (subst_env s1 c0)) __ __ __
      in
      let (p1, x2) = s0 in
      let (m2, s2) = p1 in
      let ty = subst_mlt s2 (gen (subst_env s1 c0) (subst_mlt s1 (mk_meta ta))) in
      ((m2, (app s1 s2)), (MLletin' (x0, (length (free_vars ty), ty), x1, x2)))
    | MLglob r ->
      let tx = type_of_ref r !refenv in
      (match tx with
       | Some tx0 ->
         let n =
           match max_tyvar tx0 with
           | Some n -> n
           | None -> 0
         in
         let p = new_meta_list n curr_m0 in
         let (ms, next_m) = p in
         let u = unify ((mlt0, (inst_with_meta ms tx0)) :: []) in
         let tvars' = map (fun m -> subst_mlt u (mk_meta m)) ms in
         ((next_m, u), (MLglob' (r, tvars')))
       | None -> assert false (* absurd case *))
    | MLcons (ty, r, es) ->
      (match r with
       | ConstructRef c1 ->
         let (i, x0) = c1 in
         let (mi, i0) = i in
         let mind = mind_of_cons mi !refenv in
         (match mind with
          | Some mind0 ->
            let l = length es in
            let p = new_meta_list mind0.ind_nparams curr_m0 in
            let (ms, next_m) = p in
            let tys = type_of_cons mind0 i0 x0 in
            let etys = combine es (map (instantiation (map mk_meta ms)) tys)
            in
            let f0 = fun mle0 -> h mle0 in
            let s = infer_list etys (fun mle0 _ -> f0 mle0) l etys next_m c0
            in
            let (p0, x1) = s in
            let (m1, s1) = p0 in
            let s2 = unify ((subst_mlt s1 mlt0, subst_mlt s1 (Tglob ((IndRef (mi, i0)), (mk_meta_list ms)))) :: []) in
            ((m1, app s1 s2), (MLcons' ((Tglob ((IndRef (mi, i0)), (mk_meta_list ms))),
            (ConstructRef ((mi, i0), x0)), (map (fun p1 -> fst p1) x1))))
          | None -> assert false (* absurd case *))
       | _ -> assert false (* absurd case *))
    | MLcase (ty, a, bs') ->
      let bs = map (fun (xs,p,e) -> (xs,(p,e))) (Array.to_list bs') in
      (match ty with
       | Tglob (r, tys) ->
         (match r with
          | IndRef i ->
            let (mi, k) = i in
            let p = new_meta_list (length tys) curr_m0 in
            let (ms, next_m) = p in
            let s =
              h a (Tglob ((IndRef (mi, k)), (mk_meta_list ms))) next_m c0 __
                __ __
            in
            let (p0, x0) = s in
            let (m1, s1) = p0 in
            let s0 =
              infer_branch a bs tys mi k bs (subst_mlt s1 mlt0)
                (subst_env s1 c0) (map (subst_mlt s1) (mk_meta_list ms)) m1
                (fun y _ -> h y)
            in
            let (p1, x1) = s0 in
            let (m2, s2) = p1 in
            ((m2, (app s1 s2)), (MLcase' ((Tglob ((IndRef (mi, k)), tys)),
            x0, Array.of_list (map (fun (xs,(p,e)) -> (xs,p,e)) x1))))
          | _ -> assert false (* absurd case *))
       | _ -> assert false (* absurd case *))
    | MLfix (k, xs', es') ->
      let xs = Array.to_list xs' in
      let es = Array.to_list es' in
      let l = length es in
      let p = new_meta_list l curr_m0 in
      let (ms, next_m) = p in
      let etys = combine es (map mk_meta ms) in
      let f0 = fun mle0 -> h mle0 in
      let s = infer_list etys (fun mle0 _ -> f0 mle0) l etys next_m (add_env_all c0 (map mk_meta ms)) in
      let (p0, x0) = s in
      let es' = map (fun p1 -> fst p1) x0 in
      (p0, (MLfix' (k, Array.of_list (combine xs (map mk_meta ms)), Array.of_list es')))
    | MLexn i -> (((Pervasives.succ curr_m0), []), (MLexn' i))
    | MLdummy -> (((Pervasives.succ curr_m0), []), MLdummy')
    | MLaxiom -> (((Pervasives.succ curr_m0), []), MLaxiom')
    | MLmagic e ->
      let p = new_meta curr_m0 in
      let (ta, next_m) = p in
      let s = h e (mk_meta ta) next_m c0 __ __ __ in
      let (p0, x0) = s in
      let (m', s') = p0 in ((m', s'), (MLmagic' (x0, (subst_mlt s' mlt0))))
    | _ -> assert false)
  in f mle mlt curr_m c __ __ __


(* ---------------------------------------------------------------------------------------- *)
let rec var'2var = function
  | Tvar' i -> Tvar i
  | Tarr (a,b) -> Tarr (var'2var a, var'2var b)
  | Tglob (r,l) -> Tglob (r, List.map var'2var l)
  | a -> a

let rec ast_tmap' f = function
  | MLrel' (x, ts) -> MLrel' (x, List.map f ts)
  | MLapp' (a, b) -> MLapp' (ast_tmap' f a, List.map (ast_tmap' f) b)
  | MLlam' (x, t, a) -> MLlam' (x, f t, ast_tmap' f a)
  | MLglob' (r, ts) -> MLglob' (r, List.map f ts)
  | MLletin' (x, (i,t), a, b) -> MLletin' (x, (i,f t), ast_tmap' f a, ast_tmap' f b)
  | MLcons' (t, x, bs) -> MLcons' (f t, x, List.map (ast_tmap' f) bs)
  | MLtuple' bs -> MLtuple' (List.map (ast_tmap' f) bs)
  | MLcase' (t, a, bs) -> MLcase' (f t, ast_tmap' f a, Array.map (fun (ids,p,b) -> (ids,p,ast_tmap' f b)) bs)
  | MLfix' (i, idts, bs) -> MLfix' (i, Array.map (fun (id,t) -> (id, f t)) idts, Array.map (ast_tmap' f) bs)
  | MLmagic' (a, t) -> MLmagic' (ast_tmap' f a, f t)
  | t -> t

let infer_ml mlt mle = 
  let ((_, s), mle') = infer mle (var2var' mlt) 0 [] in
  ast_tmap' (fun ty -> subst_mlt s (var'2var ty)) mle'

(* ---------------------------------------------------------------------------------------- *)
let (!%) = Printf.sprintf
let ($) g f x = g (f x)
let pendl = print_endline
let slist f xs = String.concat ";" (List.map f xs)
let sarray f xs = slist f (Array.to_list xs)
let id x = x
let list_mapi f = Array.to_list $ Array.mapi f $ Array.of_list
let tryo f x = try Some (f x) with _ -> None
let string1 = String.make 1
let (|>) x f = f x
let (--) a b = 
  let rec iter store a bi =
    if a = bi then bi::store
    else iter (bi::store) a (bi - 1)
  in
  if a <= b then iter [] a b
  else List.rev (iter [] b a)

let keywords =
  List.fold_right (fun s -> Idset.add (id_of_string s))
  [ "abstract"; "do"; "finally"; "import"; "object"; "return"; "trait"; "var";
    "_"; "case"; "else"; "for"; "lazy"; "override"; "sealed"; "try"; "while";
    "catch"; "extends"; "forSome"; "match"; "package"; "super"; "true"; "with";
    "class"; "false"; "if"; "new"; "private"; "this"; "type"; "yield"; "def";
    "final"; "implicit"; "null"; "protected"; "throwA"; "val"; "unit" ]
  Idset.empty

let preamble _ _ _ = str ""

let prarray_with_sep msg f xs = prlist_with_sep msg f (Array.to_list xs)
let prlist_with_comma f xs = prlist_with_sep (fun () -> str ", ") f xs
let prlist_with_space f xs = prlist_with_sep (fun () -> str " ") f xs

let pp_global k r =
  if is_inline_custom r then str (find_custom r)
  else str (Common.pp_global k r)

let pr_id id =
  let s = string_of_id id in
  let ss = List.map (function | "\'" -> "$prime" | c -> c) (explode s) in
  str (String.concat "" ss)

let name_of_tvar i =
  "T" ^ string_of_int i

let name_of_tvar' i =
  if 1 <= i && i <= 26 then
    string1 (char_of_int (int_of_char 'A' + i - 1))
  else
    "A" ^ string_of_int i

let rec pp_type (tvs:identifier list) = function
    | Tmeta m -> begin match m.contents with
      | Some t -> pp_type tvs t
      | None -> str "Any"
    end
    | Tvar' i -> str (name_of_tvar' i)
    | Tvar i ->
	begin match tryo (List.nth tvs) (i-1) with
	| Some v -> pr_id v
        | None -> str (name_of_tvar i) (*"Any"*)
	end
    | Tglob ((r: global_reference), (l: ml_type list)) ->
	pp_global Type r
	  ++ if l = [] then mt ()
	     else str "[" ++ prlist_with_comma (pp_type tvs) l ++ str "]"
    | Tarr (t1,t2) ->
	str "(" ++ pp_type tvs t1 ++ str " => " ++ pp_type tvs t2 ++ str")"
    | Tdummy _ -> str "Unit"
    | Tunknown -> str "Any"
    | Taxiom -> str "Unit // AXIOM TO BE REALIZED" ++ fnl()

let spl = ["";"  ";"    ";"      ";"        ";"          ";"            ";"              "]

let rec nspaces n = 
  try 
    str (List.nth spl n) 
  with
  | Failure _ -> str "  " ++ nspaces (n-1)
  | Invalid_argument _ -> str ""

let rec pp_expr b n (tvs: identifier list) (env: env) (t: ml_ast') : 'a =
    (if b then nspaces n else str "") ++
    match t with
    | MLrel' (i, ts) ->
	let id = get_db_name i env in
        let type_annot = if ts = [] then mt()
            else str "[" ++ prlist_with_comma (pp_type tvs) ts ++ str "]"
        in
	pr_id id ++ type_annot
    | MLapp' (f, args) ->
	pp_expr false (n+1) tvs env f ++ str "("
	  ++ prlist_with_sep (fun () -> str ")(") (pp_expr false (n+1) tvs env) args ++ str ")"
    | MLlam' (_, _, _) as a ->
      	let fl,a' = collect_lams' a in
        let (ids,tys) = List.split fl in
	let ids',env' = push_vars (List.map id_of_mlid ids) env in
        let fl' = combine ids' tys in
        let pp_arg (id,ty) = str "(" ++ pr_id id ++ str ":"
            ++ pp_type tvs ty ++ str ") =>"
        in
	str"{" ++ fnl()
          ++ nspaces n ++ prlist_with_space pp_arg (List.rev fl') ++ fnl()
          ++ pp_expr true n tvs env' a' ++ fnl()
          ++ nspaces (n-1) ++ str "}"
    | MLletin' (mlid, (i,mlty), a1, a2) ->
	let id = id_of_mlid mlid in
	let (ids', env2) = push_vars [id] env in
	str "{" ++ fnl()
          ++ local_def' n tvs env (List.hd ids') i mlty a1 ++ fnl()
	  ++ pp_expr true n tvs env2 a2 ++ fnl() ++ nspaces n ++ str "}" ++ fnl()
    | MLglob' (r, ty_args) ->
        let type_annot = if ty_args = [] then mt()
          else str"[" ++ prlist_with_comma (pp_type tvs) ty_args ++ str "]"
        in
        pp_global Term r ++ type_annot
    | MLcons' (Tglob (_, ty_args), r, args) ->
        let type_annot = if ty_args = [] then mt()
          else str"[" ++ prlist_with_comma (pp_type tvs) ty_args ++ str "]"
        in
	pp_global Cons r ++ type_annot ++ str "("
	  ++ prlist_with_comma (pp_expr false 0 tvs env) args ++ str ")"
    | MLcons' (_, r, args) ->
	pp_global Cons r ++ str "("
	  ++ prlist_with_comma (pp_expr false 0 tvs env) args ++ str ")"
    | MLtuple' _ -> assert false
    | MLcase' (_, t, pv)  ->
	pp_expr false (n+1) tvs env t ++ str " match {" ++ fnl()
	  ++ prarray_with_sep fnl (pp_case (n+1) tvs env) pv
	  ++ fnl() ++ nspaces n ++ str "}"
    | MLfix' (i, idtys ,defs) ->
        let ids,tys = Array.to_list idtys |> List.split in
	let ids',env' = push_vars (List.rev ids) env in
	let ids'' = List.rev ids' in
	let local_defs =
	  prlist_with_sep fnl id
	    (list_map3 (fun id ty def -> local_def' (n+1) tvs env' id 0 ty def)
	       ids'' tys (Array.to_list defs))
	in
	let body = pr_id (List.nth ids'' i) in
	str"{" ++fnl()++ local_defs ++fnl()++ nspaces n ++ body ++ str"}" ++fnl()
    | MLexn' s -> str ("throw new Exception(\"" ^s^ "\")")
    | MLdummy' -> str "()"
    | MLmagic' (a, ty) ->
	str "(" ++ pp_expr false 0 tvs env a ++ str ").asInstanceOf[" ++ pp_type tvs ty ++ str"]"
    | MLaxiom' -> str "() // AXIOM TO BE REALIZED" ++ fnl()

and pp_case n tvs env (ids,p,t) =
  let (ids, env') = push_vars (List.rev_map id_of_mlid ids) env in
  let name = match p with
             | Prel 1 -> str ""
             | Pusual r -> pp_global Cons r
             | Pcons (r,_) -> pp_global Cons r
             | Pwild -> str "_"
             | _ -> assert false
  in let args = match p with
                | Pwild -> str ""
                | _ -> str "(" ++ prlist_with_comma pr_id (List.rev ids) ++ str ")"
  in
  nspaces n ++ str "case " ++ name ++ args ++ str " => " ++ fnl()
    ++ pp_expr true (n+1) tvs env' t

and local_def tvs env (id: identifier) (def: ml_ast') =
  str "def " ++ pr_id id ++ str " = " ++ pp_expr false 0 tvs env def ++ str ";"

and local_def' n tvs env (id: identifier) i (ty: ml_type) (def: ml_ast') =
  let new_tvars =
    let m = List.length tvs in
    if i=0 then []
    else (m+1)--(m+i)
    |> List.map (id_of_string $ name_of_tvar)
  in
  let tvs' = List.rev new_tvars @ tvs in
  let pp_tvars = if new_tvars = [] then mt() else
    str "[" ++ prlist_with_comma pr_id new_tvars ++ str "]"
  in
  nspaces n ++ str "def " ++ pr_id id ++ pp_tvars ++ str ": " ++ pp_type tvs' ty
    ++ str " = " ++ pp_expr false (n+1) tvs' env def ++ str ";"

let pp_def glob body typ =
  let ftvs = free_type_vars typ in
  let tvars = if ftvs = [] then mt() else
    str "[" ++ prlist_with_comma (str $ name_of_tvar') ftvs ++ str "]"
  in
  let tvs = List.map (fun i -> id_of_string (name_of_tvar' i)) ftvs in
  let pbody =
    if is_custom glob then str (find_custom glob)
    else pp_expr false 1 tvs (empty_env()) body
  in
  str "def " ++ pp_global Term glob ++ tvars ++ str " : " ++ pp_type tvs typ
    ++ str " = " ++ pbody ++ fnl()

let pp_singleton kn packet =
  let l = packet.ip_vars in
  let l' = List.rev l in
  let params = if l = [] then mt ()
      else str "[" ++ prlist_with_comma pr_id l ++ str "]"
  in
  str "type " ++ pp_global Type (IndRef (kn, 0)) ++ params 
    ++ str " = " ++ pp_type l' (List.hd packet.ip_types.(0)) ++ fnl()

let pp_one_ind (ip: inductive) (tvars: identifier list)
    (cv: ml_type list array) =
  let tname = pp_global Type (IndRef ip) in
  let pp_tvars vs =
    if vs = [] then mt()
    else str "[" ++ prlist_with_comma pr_id vs ++ str "]"
  in
  let pp_constructor (r,typs) =
    str "case class " ++ pp_global Cons r ++ pp_tvars tvars ++ str "("
      ++ prlist_with_comma
        (fun (i, typ) ->
	  let vname = str "x" ++ int i in
	  vname ++ str ": " ++ pp_type tvars typ)
        (list_mapi (fun i typ -> (i+1,typ)) typs)
      ++ str ") extends " ++ tname ++ pp_tvars tvars
  in
  str "sealed abstract class " ++ tname ++ pp_tvars tvars ++ fnl()
    ++ prvect_with_sep fnl pp_constructor
      (Array.mapi (fun j typ -> (ConstructRef(ip,j+1), typ)) cv)
    

let pp_decl b sts d = 
  if b then set_refenv sts else ();
  match d with
  | Dind (mind,i) when i.ind_kind = Singleton ->
      pp_singleton mind i.ind_packets.(0) ++ fnl ()
  | Dind (mind, (ind: ml_ind)) ->
      let rec iter i =
	if i >= Array.length ind.ind_packets then mt()
	else
	  let packet = ind.ind_packets.(i) in
	  let ip = (mind,i) in
	  pp_one_ind ip packet.ip_vars packet.ip_types ++ fnl ()
	    ++ iter (i+1)
      in
      iter 0
  | Dtype ((r:global_reference), (l: identifier list), (t: ml_type)) ->
      if is_inline_custom r then mt()
      else
        let name = pp_global Type r in
	let l = rename_tvars keywords l in
        let ty_args, def = match tryo find_type_custom r with
          | Some (ids,s) -> List.map str ids, str s
          | None -> List.map pr_id l, pp_type l t
        in
        let tparams = if ty_args = [] then mt()
            else str "[" ++ prlist_with_comma id ty_args ++ str "]"
        in
        str "type " ++ name ++ tparams ++ str " = " ++ def ++ fnl()
  | Dfix ((rv: global_reference array), (defs: ml_ast array), (typs: ml_type array)) ->
      (try
      let max = Array.length rv in
      let fix_ev = List.map2 (fun rf -> fun tf -> Sval (rf, tf)) (Array.to_list rv) (Array.to_list typs) in
      let _ = add_refenv fix_ev in
      let rec iter i =
	if i = max then mt ()
	else (
          let def = infer_ml typs.(i) defs.(i) in
	  pp_def rv.(i) def typs.(i) ++ iter (i+1))
      in
      iter 0
      with Invalid_argument st -> 
        print_string (st ^ " when processing Dfix\n"); assert false)
  | Dterm ((r: global_reference), (a: ml_ast), (t: ml_type)) ->
      let a' = infer_ml t a in
      if is_inline_custom r then mt ()
      else pp_def r a' t

let rec pp_structure_elem = function
  | (l,SEdecl d) -> pp_decl false [] d
  | (l,SEmodule m) -> pp_module_expr m.ml_mod_expr
  | (l,SEmodtype m) -> mt ()
and pp_module_expr = function
  | MEstruct (mp,sel) -> str "object CoqModule {" ++ fnl()
	++ prlist_strict pp_structure_elem sel
	++ str "}" ++ fnl()
  | MEfunctor _ -> mt ()
  | MEident _ | MEapply _ -> assert false

let pp_struct (sts: ml_structure) =
  set_refenv sts;
  let pp_sel (mp,sel) =
    push_visible mp [];
    let p =
      prlist_strict pp_structure_elem sel
    in
    pop_visible (); p
  in
  str "object CoqMain {" ++ fnl()
    ++ prlist_strict pp_sel sts
    ++ str "}" ++ fnl()


let scala_descr = {
  keywords = keywords;
  file_suffix = ".scala";
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl true;
}

