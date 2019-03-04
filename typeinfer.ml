module S = Source
open Source0

(*---------------------------------------------------------------------------
 * Définition of types and modules
 *)

type supra_typ = typ

let tfloat = TyConstant TyFloat


let rec re_trad_type = function
  | TyConstant TyFloat -> S.TyConstant S.TyFloat
  | TyArrow (t1, t2) -> S.TyArrow (re_trad_type t1, re_trad_type t2)
  | TyPair (t1, t2) -> S.TyPair (re_trad_type t1, re_trad_type t2)
  | TyVar {def = Some y} -> re_trad_type y
  | TyVar {def = None} -> assert false

let rec has_var = function
  | TyConstant TyFloat -> false
  | TyPair (t1, t2)
  | TyArrow (t1, t2) ->
    (has_var t1) || (has_var t2)
  | TyVar _ -> true

let rec str_of_typ typ = 
  let rec print_arrow = function
    | TyArrow (t1, t2) ->
      Printf.sprintf "%s -> %s" (print_pair t1) (print_arrow t2)
    | x -> print_pair x
  and print_atom = function
    | TyConstant TyFloat -> "float"
    | TyVar v -> Printf.sprintf "'a%d" v.id
    | x -> Printf.sprintf "(%s)" (print_arrow x)
  and print_pair = function
    | TyPair (t1, t2) ->
      Printf.sprintf "%s, %s" (print_pair t1) (print_atom t2)
    | x -> print_atom x
  in 
  print_arrow typ


module V = struct
  type t = tvar
  let compare (v1: t) (v2: t) =
    Pervasives.compare v1.id v2.id
  let equal (v1: t) (v2: t) = 
    v1.id = v2.id
  let create = 
    let cont = ref 0 in
    fun () -> 
      let _ = incr cont in
      {id = !cont; def = None}
end

(*---------------------------------------------------------------------------
 * Normalisation and unification
 *)

let rec head = function
  | TyVar {def = Some y} -> head y
  | x -> x

let rec canon = function 
  | TyConstant _ -> tfloat
	| TyArrow (x,y) -> TyArrow (canon x, canon y)
	| TyPair (x,y) -> TyPair (canon x, canon y)
  | TyVar {def = Some y} -> canon y
	| TyVar t -> TyVar t

let type_error pos msg = 
  Typechecker.type_error pos msg

  (** [occur v t] returns true iff [v] is a type occuring in [t] *) 
let rec occur (v: V.t) t = match (head t) with
	| TyConstant _ -> false
	| TyArrow (x,y) -> (occur v x) || (occur v y)
	| TyPair (x,y) -> (occur v x) || (occur v y)
	| TyVar {id = i} -> i = v.id

let rec unify x y loc = 
  match (head x), (head y) with
  | TyConstant _ , TyConstant _  -> ()
	| TyPair(x1,x2), TyPair(y1,y2)
	| TyArrow(x1,x2), TyArrow(y1, y2) ->
	  unify x1 y1 loc; 
    unify x2 y2 loc
  | TyVar v1, TyVar v2 when V.equal v1 v2 ->
    let _ = Printf.printf "Cas toto\n"  in
    ()      
	| TyVar v , t -> 
	  if occur v t then 
      let msg = Printf.sprintf "Unification error : %s is a subtype of %s"
        (str_of_typ x) (str_of_typ y)
      in
      type_error loc msg
		else 
      let _ = assert (v.def = None) in
      v.def <- Some t
	| y1 , TyVar v -> unify y x loc
	| _, _ -> 
      let msg = Printf.sprintf 
        "Unification error : types %s and %s are incompatible"
        (str_of_typ x) (str_of_typ y)
      in
      type_error loc msg




(*---------------------------------------------------------------------------
 * Environment functions
 *)

(* Quelques modules bien utiles *)
module VSet = Set.Make(V)
module VMap = Map.Make(V)
module SMap = Map.Make(String)

let rec fvars x = 
  match (head x) with
	| TyConstant _ -> VSet.empty
	| TyPair(x1,x2) | TyArrow(x1,x2) -> 
	  VSet.union (fvars x1) (fvars x2)
	| TyVar v -> VSet.singleton v

type schema = 
  { vars : VSet.t;  (** The set universally quantified variables *)
    typ : supra_typ}(** The typ of the scheme *)

type env = 
  { bindings : schema SMap.t; 
    fvars : VSet.t }

  (** the empty environment *)
let empty = 
  { bindings = SMap.empty; 
    fvars = VSet.empty }

  (** [add ident typ env] add the binding [ident] := [typ] in the map.
   It does not add generiticity in [typ] *)
let add ident typ env =
  let var_typ = fvars typ in
  let fvars = VSet.union env.fvars var_typ in
  let sch = {vars = VSet.empty; typ = typ} in
  let bindings = SMap.add ident sch env.bindings in
    { bindings = bindings; fvars = fvars }

  (** [add ident typ env] add the binding [ident] := [typ] in the map.
   It adds generiticity in [typ] *)
let add_gen ident typ env = 
  let var_typ = fvars typ in
  (* On ne rajoute que les variables qui ne sont pas libres dans l'envirronment
   * ! *)
  let sch = {vars = VSet.diff var_typ env.fvars; typ = typ} in
  let bindings = SMap.add ident sch env.bindings in
    { bindings = bindings; fvars = env.fvars }


let find ident env = 
  let sch = SMap.find ident env.bindings in
  let sub_env = 
    VSet.fold 
      (fun var map -> VMap.add var (TyVar (V.create ())) map)
      sch.vars
      VMap.empty
  in
  let rec replace t = match (head t) with
  | TyConstant _ -> 
    tfloat
  | TyArrow (t1, t2) -> 
    TyArrow (replace t1, replace t2)
  | TyPair (t1, t2) -> 
    TyPair (replace t1, replace t2)
  | TyVar v when VMap.mem v sub_env ->
    VMap.find v sub_env
  | (TyVar _) as typ -> 
    typ 
  in
    replace sch.typ


(*------------------------------------------------------------------------
 * Algorithme W
 *)

let rec alg_w env term =
  let pos = Position.position term in
  match Position.value term with
  | Var (Id ident) ->
    let typ = find ident env in
      typ, term
  | Literal _ -> 
    tfloat, term
  | Primitive f ->
  begin
    match f with
    | Sin | Cos | Exp | Inv | Neg ->
      TyArrow (tfloat, tfloat), term
    | Mul | Add ->
      TyArrow (tfloat, TyArrow (tfloat, tfloat)), term
  end
  | App (e1, e2) ->
    let t1, e1 = alg_w env e1 in
    let t2, e2 = alg_w env e2 in
    let alpha = TyVar ( V.create ()) in
    let t2' = TyArrow (t2, alpha) in
    let _ = unify t1 t2' pos in
    let final_typ = head alpha in
    let term = Position.with_pos pos (App (e1, e2)) in
      final_typ, term
  | Lam ((Id ident, typ) , e) -> 
    let typ_x = match typ with
      | Some typ -> typ
      | None -> TyVar (V.create ()) 
    in
    let new_env = add ident typ_x env in
    let t_res, e = alg_w new_env e in
    let final_typ = TyArrow (typ_x, t_res) in
    let term = Position.with_pos pos (Lam ((Id ident, Some typ_x), e)) in
      final_typ, term
  | Pair (e1, e2) ->
    let t1, e1 = alg_w env e1 in
    let t2, e2 = alg_w env e2 in
    let final_typ = TyPair (t1, t2) in
    let term = Position.with_pos pos (Pair (e1, e2)) in
      final_typ, term
  | Fst e ->
    let alpha = TyVar (V.create ()) in
    let beta = TyVar (V.create ()) in
    let t = TyPair (alpha, beta) in
    let typ, e = alg_w env e in
    let _ = unify t typ pos in
    let final_typ = head alpha in
    let term = Position.with_pos pos (Fst e) in
      final_typ, term
  | Snd e ->
    let alpha = TyVar (V.create ()) in
    let beta = TyVar (V.create ()) in
    let t = TyPair (alpha, beta) in
    let typ, e = alg_w env e in
    let _ = unify t typ pos in
    let final_typ = head beta in
    let term = Position.with_pos pos (Snd e) in
      final_typ, term

let wrapper env ( bind , term ) = 
  let (Id ident, typ0) = Position.value bind in
  let _ = Printf.printf "Typing %s\n" ident in
  let typ, term' = 
      try 
      alg_w env term 
      with Stack_overflow -> print_string ident; assert false
  in
  let _ = match typ0 with
          | None -> ()
          | Some typ0 -> unify typ0 typ (Position.position bind)
  in
  let typ = canon typ in
  let _ = Printf.printf "\t%s: %s\n" ident (str_of_typ typ) in
  let env =  add ident typ env in
    env, term'




let rec final_trad_term term = 
  let pos = Position.position term in
  match Position.value term with
  | Var (Id ident) ->
    let e = S.Var (S.Id ident) in
      Position.with_pos pos e 
  | Literal (Float x) ->
    let e = S.Literal (S.Float x) in
      Position.with_pos pos e 
  | Primitive f ->
    let f = match f with
      | Cos -> S.Cos
      | Sin -> S.Sin
      | Exp -> S.Exp
      | Neg -> S.Neg
      | Inv -> S.Inv
      | Mul -> S.Mul
      | Add -> S.Add
    in
    let e = S.Primitive f in
      Position.with_pos pos e 
  | App (e1, e2) ->
    let e1 = final_trad_term e1 in
    let e2 = final_trad_term e2 in
    let e = S.App (e1, e2) in
      Position.with_pos pos e 
  | Lam ((Id ident, typ), e1) ->
    let typ = match typ with
      | None -> assert false
      | Some typ -> re_trad_type typ 
    in
    let _ = Printf.printf "\t%s: %s\n" ident (Typechecker.string_of_type typ) in
    let e1 = final_trad_term e1 in
    let e = S.Lam ((S.Id ident, typ), e1) in
      Position.with_pos pos e 
  | Pair (e1, e2) -> 
    let e1 = final_trad_term e1 in
    let e2 = final_trad_term e2 in
    let e = S.Pair (e1, e2) in
      Position.with_pos pos e 
  | Fst e1 ->
    let e1 = final_trad_term e1 in
    let e = S.Fst e1 in
      Position.with_pos pos e 
  | Snd e1 ->
    let e1 = final_trad_term e1 in
    let e = S.Snd e1 in
      Position.with_pos pos e 


let recompute_fvar vars = 
  VSet.fold 
    (fun v s -> VSet.union (fvars (TyVar v)) s) 
    vars 
    VSet.empty
      

let rec final_trad = function
  | [] -> []
  | f::q ->
    let bind, term = f in
    let S.Id ident, typ = Position.value bind in
    let _ = Printf.printf "Translating %s\n" ident in
    let typ = re_trad_type typ in
    let _ = Printf.printf "\t%s: %s\n" ident (Typechecker.string_of_type typ) in
    let bind = Position.with_pos (Position.position bind) (S.Id ident, typ) in
    let term = final_trad_term term in
      (bind, term)::(final_trad q)



let rec over_wrap env acc = function
  | [] -> 
    let fvars = recompute_fvar env.fvars in
    let _ = if fvars <> VSet.empty then
      let msg = Printf.sprintf 
        "Type inference error. Cannot infer type for variables %s"
        (VSet.fold 
          (fun v acc -> Printf.sprintf "%s %s," acc (str_of_typ (TyVar v)))
          fvars 
          ""
       )
     in
     type_error Position.dummy msg 
   in
   final_trad acc
  | f::q ->
    let Id ident = fst @@ Position.value @@ fst f in
    let new_env, term' = wrapper env f in
    let {typ = typ} = SMap.find ident new_env.bindings in
    let bind = Position.with_pos 
      (Position.position @@ fst @@ f) 
      (S.Id ident, typ) 
    in
    let acc = acc@[bind, term'] in
    over_wrap new_env acc q

let infer_type (prog: program_with_locations) : S.program_with_locations = 
    over_wrap empty  [] prog
