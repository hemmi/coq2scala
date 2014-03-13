
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

let rec new_meta_list n =
  if n<=0 then []
  else new_meta() :: (new_meta_list (n-1))

let rec var'2var = function
  | Tvar' i -> Tvar i
  | Tarr (a,b) -> Tarr (var'2var a, var'2var b)
  | Tglob (r,l) -> Tglob (r, List.map var'2var l)
  | a -> a

let generalization t =
  let c = ref 0 in
  let map = ref (Intmap.empty : int Intmap.t) in
  let add_new i = incr c; map := Intmap.add i !c !map; !c in
  let rec meta2var t = match t with
    | Tmeta ({id=i}) ->
       (try Tvar (Intmap.find i !map)
        with Not_found ->
          Tvar (add_new i))
    | Tarr (t1,t2) -> Tarr (meta2var t1, meta2var t2)
    | Tglob (r,l) -> Tglob (r, List.map meta2var l)
    | t -> t
  in meta2var t

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

let unify t1 t2 = 
  let rec unify_iter = function
  | [] -> []
  | (a, b) :: cs' ->
     match elim_singleton a, elim_singleton b with
     | Tmeta m, Tmeta m' when m.id = m'.id -> unify_iter cs'
     | Tmeta m, t | t, Tmeta m ->
         let s = (m.id, t) in
         s :: unify_iter (subst_constrs [s] cs')
     | Tarr(a, b), Tarr(a', b') ->
         unify_iter ((a, a') :: (b, b') :: cs')
     | Tglob (r,l), Tglob (r',l') when r = r' ->
         unify_iter ((List.combine l l') @ cs')
     | Tdummy _, Tdummy _ | Tunknown, Tunknown | Taxiom, Taxiom -> unify_iter cs'
     | Tvar i, Tvar j | Tvar i, Tvar' j | Tvar' i, Tvar j | Tvar' i, Tvar' j -> 
         if i=j then unify_iter cs' 
         else assert false
     | t, u -> assert false
  in unify_iter [(t1, t2)]

let rec type_of_ref r = function
  | [] -> assert false
  | (Sval (r', ty)) :: tl when eq_gr r r'-> ty
  | _ :: tl -> type_of_ref r tl

let rec mind_of_cons mi i = function
  | [] -> assert false
  | (Sind (mi', mind)) :: _ when eq_mind mi mi' -> mind
  | _ :: tl -> mind_of_cons mi i tl

let type_of_cons mi i j targs ev = 
  List.map (type_subst_list targs) (mind_of_cons mi i ev).ind_packets.(i).ip_types.(j-1)

let rec infer_ml_iter c mlt = function
  | MLrel n -> 
     let (_,ty) = List.nth c (n-1) in
     let mty = new_meta_list (type_maxvar ty) in
     let tyr = type_subst_list mty ty in
     let s' = unify tyr mlt in
     let tvars = List.map (subst_mlt s') mty in
     (s', MLrel' (n, tvars))
  | MLapp (a, bs) -> 
     let tybs = new_meta_list (List.length bs) in
     let tya = type_recomp (tybs, mlt) in
     let (sa, a') = infer_ml_iter c tya a in
     let (sb, bs') = infer_ml_list c (List.map2 (fun t -> fun u -> (t, subst_mlt sa u)) bs tybs) in
     let s = sa @ (List.flatten sb) in
     (s, MLapp' (a', bs'))
  | MLlam (x, a) -> 
     let tx = new_meta() in let ta = new_meta() in
     let s = unify mlt (Tarr (tx,ta)) in
     let tx' = subst_mlt s tx in
     let ta' = subst_mlt s ta in
     let (sa, a') = infer_ml_iter (add_var (x,tx') c) ta' a in
     (s @ sa, MLlam' (x, subst_mlt sa tx', a'))
  | MLletin (x, a, b) ->
     let ta = new_meta() in
     let (sa, a') = infer_ml_iter c ta a in
     let ta' = generalization (subst_mlt sa ta) in
     let i = List.length (free_type_vars ta') in
     let (sb, b') = infer_ml_iter (add_var (x,ta') c) (subst_mlt sa mlt) b in
     (sa @ sb, MLletin' (x, (i,ta'), a', b'))
  | MLglob r ->
     let ty = type_of_ref r !refenv in
     let mty = new_meta_list (type_maxvar ty) in
     let tyr = type_subst_list mty ty in
     let s' = unify tyr mlt in
     let tvars = List.map (subst_mlt s') mty in
     (s', MLglob' (r, tvars))
  | MLcons (ty, (ConstructRef ((mi, i), j) as cr), bs) -> 
     let mind = mind_of_cons mi i !refenv in
     let targs = new_meta_list (mind.ind_nparams) in
     let cargs_ty = type_of_cons mi i j targs !refenv in
     let (sb, bs') = infer_ml_list c (List.combine bs cargs_ty) in
     (List.flatten sb, MLcons' (ty, cr, bs'))
  | MLcons _ -> assert false
  | MLtuple _ -> assert false
  | MLcase (_, a, bs) -> 
     let ta = new_meta() in
     let (sa, a') = infer_ml_iter c ta a in
     let ta' = subst_mlt sa ta in
     (match ta' with
     | Tglob (_, targs) ->
         let (sb, bs') = infer_ml_branch ta' c mlt targs (Array.to_list bs) in
         let s = sa @ sb in
         (s, MLcase' (subst_mlt s ta, a', bs'))
     | _ -> assert false)
  | MLcase _ -> assert false
  | MLfix (i, ids, defas) -> 
     let idl = Array.to_list ids in
     let defs = Array.to_list defas in
     let l = List.length defs in
     let tys = new_meta_list l in
     let tmp_tys = List.map (fun ty -> type_recomp (tys,ty)) tys in
     let mids = List.rev (List.map (fun i -> Id i) idl) in
     let defs' = List.map (named_lams mids) defs in
     let (ss, _) = infer_ml_list c (List.combine defs' tmp_tys) in
     let tys' = List.map2 (fun si -> fun tyi -> generalization (subst_mlt si tyi)) ss tys in
     let c' = List.rev_append (List.map2 (fun id -> fun tyi -> (Id id, tyi)) idl tys') c in
     let (ss', defs'') = infer_ml_list c' (List.combine defs tys') in
     let ss'' = List.flatten ss' in
     let si = unify (subst_mlt ss'' (List.nth tys' i)) mlt in
     (ss'' @ si, MLfix' (i, Array.of_list (List.combine idl tys'), Array.of_list defs''))
  | MLexn st -> ([], MLexn' st)
  | MLdummy -> ([], MLdummy')
  | MLaxiom -> ([], MLaxiom')
  | MLmagic a -> 
     let (sa, a') = infer_ml_iter c (new_meta()) a in
     (sa, MLmagic' (a', mlt))

and infer_ml_list c mlet = 
  let rec infer_ml_list_iter ss ret = function
  | [] -> (List.rev ss, List.rev ret)
  | (a, ty) :: tl -> 
     (let (sa, a') = infer_ml_iter c ty a in
      infer_ml_list_iter (sa :: ss) (a' :: ret) tl)
  in infer_ml_list_iter [] [] mlet

and infer_ml_branch ty c tb targs bs =
  let rec infer_ml_branch_iter s ret = function
  | [] -> (s, Array.of_list (List.rev ret))
  | (ids, p, b) :: bs' ->
      let c' = match p with
               | Prel 1 -> ((List.hd ids), ty) :: c
               | Pusual (ConstructRef ((mi, i), j)) ->
                   List.rev_append (List.map2 (fun id -> fun tyi -> (id, tyi)) ids (type_of_cons mi i j targs !refenv)) c
               | Pwild -> c
               | _ -> assert false in
      let (sb, b') = infer_ml_iter c' (subst_mlt s tb) b in
      infer_ml_branch_iter (s @ sb) ((ids, p, b') :: ret) bs'
  in infer_ml_branch_iter [] [] bs

let infer_ml mlt mle = 
  let (s, mle') = infer_ml_iter [] (var2var' mlt) mle in
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

let prarray_with_sep pp f xs = prlist_with_sep pp f (Array.to_list xs)
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
        let fl' = List.combine ids' tys in
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
  str "def " ++ pr_id id ++ str " = " ++ pp_expr false 0 tvs env def

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
    ++ str " = " ++ pp_expr false (n+1) tvs' env def

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

