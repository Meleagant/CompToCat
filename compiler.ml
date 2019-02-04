open Source
open Target
open Typechecker

let rec ok_of_typ = function
  | TyConstant TyFloat -> OkFloat
  | TyArrow (t1, t2) ->
     OkArrow (ok_of_typ t1, ok_of_typ t2)
  | TyPair (t1, t2) ->
     OkPair (ok_of_typ t1, ok_of_typ t2)


let rec compile = function
  | Lam ((Id ident, typ), Var (Id ident')) when ident = ident' ->  
    Identity (ok_of_typ typ)
  | Lam ((Id ident, typ), App (u, v)) -> assert false
  | Lam _
  | Var _ | App _ | Pair _ | Fst _ | Snd _ | Literal _ | Primitive _ -> 
    assert false

(** [source_to_categories translates a [source] in a [target] language
    made of categorical combinators. *)
let source_to_categories : Source.program -> Target.program = fun source ->
   failwith "Student! This is your job!"
