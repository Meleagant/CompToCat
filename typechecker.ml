open PPrint
open Source

module SMap = Map.Make(String)
type env = 
    { id_env: typ SMap.t;
      ty_env: typ SMap.t }

(** [type_error pos msg] reports a type error and exits. *)
let type_error pos msg =
  Printf.eprintf "%s:\n%s\n"
    (Position.string_of_pos pos)
    msg;
  exit 1

(** [string_of_type ty] returns a human readable representation of a type. *)
let string_of_type t =
  let rec ty = function
    | TyConstant TyFloat ->
       string "float"
    | TyArrow (input, output) ->
       group (mayparen_ty_under_arrow_lhs input) ^^ break 1
       ^^ string "->"
       ^^ break 1 ^^ (group (ty output))
    | TyPair (lhs, rhs) ->
       group (mayparen_ty_under_pair_lhs lhs) ^^ break 1
       ^^ string "* " ^^ group (mayparen_ty_under_pair_rhs rhs)
    and mayparen_ty_under_arrow_lhs = function
      | (TyArrow _) as t ->
         PPrintCombinators.parens (ty t)
      | t ->
         ty t
    and mayparen_ty_under_pair_lhs = function
      | (TyArrow _) as t ->
         PPrintCombinators.parens (ty t)
      | t ->
         ty t
    and mayparen_ty_under_pair_rhs = function
      | (TyArrow _ | TyPair _) as t ->
         PPrintCombinators.parens (ty t)
      | t ->
         ty t
  in
  let b = Buffer.create 13 in
  PPrintEngine.ToBuffer.pretty 0.8 80 b (group (ty t));
  Buffer.contents b

(** [check_program source] returns [source] if it is well-typed or
   reports an error if it is not. *)
let check_program (source : program_with_locations) : program_with_locations =
  let empty_env () = 
      { id_env = SMap.empty ; ty_env = SMap.empty } in 
  (*
  let init_env (source: program_with_locations) : env = 
    List.fold_left 
    (fun env (binding_loc, _) ->
        let Id ident, typ = Position.value binding_loc in
        let _ = if SMap.mem ident env.id_env then assert false  in
        let id_env = SMap.add ident typ env.id_env in
        {env with id_env = id_env})
    (empty_env ())
    source in
*)  
(* The main function *)
  let rec type_term (term: term' Position.located ) env : typ = 
  match Position.value term with
  | Var (Id ident) -> 
    let _ = if not (SMap.mem ident env.id_env) then
      let pos = Position.position term in
      let msg = Printf.sprintf 
        "The identifiant %s is not in the current environment\n" ident in
        type_error pos msg
    in SMap.find ident env.id_env
  | App (t1, t2) ->
  begin
    let typ1 = type_term t1 env 
    and typ2 = type_term t2 env 
    in
    match typ1 with
    | TyArrow (typ1_left, typ1_right) when typ1_left = typ2 ->
       typ1_right 
    | _ ->
    let pos = Position.position term in
    let msg = Printf.sprintf 
      "An argument of type %s is applied to an expression of type %s"
      (string_of_type typ1) (string_of_type typ2) in
    type_error pos msg
  end
  | Lam ((Id ident, typ), t) ->
    let id_env = SMap.add ident typ env.id_env in
    let new_env = {env with id_env = id_env } in
    let typ_ret = type_term t new_env in
    TyArrow (typ, typ_ret)
  | Pair (t1, t2) ->
    let typ1 = type_term t1 env 
    and typ2 = type_term t2 env 
    in TyPair (typ1, typ2)
  | Fst t ->
  begin
    match type_term t env with
    | TyPair (typ, _) -> typ
    | typ -> 
      let pos = Position.position term in
      let msg = Printf.sprintf 
      "An argument of type %s is applied to the function Fst"
        (string_of_type typ) in
      type_error pos msg
  end
  | Snd t ->
  begin
    match type_term t env with
    | TyPair (_, typ) -> typ
    | typ -> 
      let pos = Position.position term in
      let msg = Printf.sprintf 
      "An argument of type %s is applied to the function Snd"
        (string_of_type typ) in
      type_error pos msg
  end
  | Literal _ -> TyConstant TyFloat
  | Primitive prim ->
    let tyFloat = TyConstant TyFloat in
    match prim with
    | Sin | Cos | Inv | Neg | Exp ->
    TyArrow (tyFloat, tyFloat)
    | Add | Mul ->
    TyArrow (tyFloat, TyArrow (tyFloat, tyFloat))
  in
  let _ = List.fold_left
    (fun env (bind_loc, term) ->
      let (Id id, typ) = Position.value bind_loc  in
      let typ' = type_term term env in
      let _ = if typ' <> typ then 
        let pos = Position.position bind_loc in
        let msg = Printf.sprintf 
          "The identifiant %s is declared to have type %s but has type %s"
          id (string_of_type typ) (string_of_type typ') in
        type_error pos msg
      in
      let env_id = SMap.add id typ env.id_env in
      {env with id_env = env_id})
    (empty_env ()) 
    source 
    |> ignore in
  source

(** [eta_expanse source] makes sure that only functions are defined at
    toplevel and turns them into eta-long forms if needed. *)
let eta_expanse (source: program_with_locations) :  program_with_locations =
  let eta_expanse def = 
    let bind_loc, term = def in
    let (Id id, typ) = Position.value bind_loc in
    match typ with
    | TyArrow _ ->
    begin
      match Position.value term with
      | Lam _ -> def
      | _ -> Printf.printf "Caca\n"; assert false
    end
    | _ -> Printf.printf "Caca\n"; assert false
  in List.map eta_expanse source

let program : program_with_locations -> program_with_locations = fun source ->
  let xsource = check_program source in
  let xsource = eta_expanse xsource in
  if !Options.typecheck_only then exit 0;
  eta_expanse xsource
