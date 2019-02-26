open Source
open Target
open Typechecker

module SMap = Map.Make(String)

let rec ok_of_typ = function
  | TyConstant TyFloat -> OkFloat
  | TyArrow (t1, t2) ->
     OkArrow (ok_of_typ t1, ok_of_typ t2)
  | TyPair (t1, t2) ->
     OkPair (ok_of_typ t1, ok_of_typ t2)





type direction = | Left | Right 
type path = direction list
type local_env = (path SMap.t)*typ
type glob_env = (Target.t * ok) SMap.t

let print_env env = 
    let print_direct = function
        | Left -> "Left"
        | Right -> "Right" in
    let rec print_path = function
        | [] -> ""
        | t::q -> Printf.sprintf "%s,%s" (print_direct t) (print_path q) in
    SMap.iter 
      (fun id path -> Printf.printf "%s -> %s\n" id (print_path path))
      env

let add_env (map, typ) ident new_typ = 
    let _ = if SMap.is_empty map then assert false in
    let map = SMap.map (fun l -> Left::l) map in
    let map = SMap.add ident [Right] map in
    let typ = TyPair (typ, new_typ) in
    map,typ

let extract_var (map, typ) ident = 
  let path = SMap.find ident map in
  let rec follow_path typ = function
    | [] -> (* empty should never be used shortcut for identity *)
      let ok = ok_of_typ typ in
      Identity ok, ok
    | [dir] ->
    begin
      let t_left, t_right = 
        match typ with
        | TyPair (t1, t2) -> (t1,t2)
        | _ -> assert false
      in
      let ok_left = ok_of_typ t_left
      and ok_right = ok_of_typ t_right in
      match dir with
      | Left -> Exl (ok_left, ok_right), ok_left
      | Right-> Exr (ok_left, ok_right), ok_right
    end
    | Left::path' ->
      let t_left, t_right = 
        match typ with
        | TyPair (t1, t2) -> (t1,t2)
        | _ -> assert false
      in
      let ok_left = ok_of_typ t_left
      and ok_right = ok_of_typ t_right in
      let code, ok_res = follow_path t_left path' in
      let exl = Exl (ok_left, ok_right) in
      let comp = Compose ((ok_of_typ typ), ok_left, ok_res) in
      App (App (comp, code), exl), ok_res
   | _ -> assert false
   in
   follow_path typ path 


(* Type of a path               
 *           *
 *          / \
 *         /   \
 *        *    []
 *       / \
 *      /   \
 *     *    []
 *    / \
 *   /   \
 *  []   []
 *)



let rec compile local_env glob_env = function
  | Lam ((Id ident, typ), term) ->
     let env = add_env local_env ident typ in
     let code, ok_res = compile env glob_env term in
     let oka = ok_of_typ @@ snd @@ local_env in
     let okb = ok_of_typ typ in
     let curry = Curry (oka, okb, ok_res) in
     App (curry, code), OkArrow ((ok_of_typ typ), ok_res) 
  | Var (Id ident) -> extract_var local_env ident
  | App (u, v) ->
     let code_u, ok_u = compile local_env glob_env u in
     let ok_f = match ok_u with
      | 
     let code_v, ok_v = compile local_env glob_env v in
     let ok_a = ok_of_typ (snd local_env) in
     let fork = Fork (ok_a, ok_u, ok_v) in
    assert false
  | Pair _ 
  | Fst _ 
  | Snd _ -> 
    Printf.printf "Pas encore fait !\n"; 
    assert false
  | Literal litt -> Literal litt, OkFloat 
  | Primitive f0 -> 
  begin
    match f0 with 
    | Sin | Cos | Exp | Inv ->
      let ok_res = OkArrow (OkFloat, OkFloat) in
      Primitive f0, ok_res
    | Add | Mul | Neg ->
      let ok_res = OkArrow (OkFloat, OkArrow (OkFloat, OkFloat)) in
      Primitive f0, ok_res
  end

let compile_init glob_env (((Id ident, typ), term) : binding*term) =
  let new_env, term = 
    match term with
    | Lam ((Id ident, typ), term) ->
      let map = SMap.singleton ident [] in
      (map, typ), term
    | _ -> assert false
  in
  let code, ok = compile new_env glob_env term in 
  SMap.add ident (code, ok) glob_env




(** [source_to_categories translates a [source] in a [target] language
    made of categorical combinators. *)
let source_to_categories : Source.program -> Target.program = fun source ->
    let global_env = List.fold_left compile_init SMap.empty source in
    List.map 
      (fun ((Id ident, typ), _) -> 
          (Id ident, typ), SMap.find ident global_env |> fst)
      source
