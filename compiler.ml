open Source
open Target
open Typechecker

module SMap = Map.Make(String)

  (* [rec_of_typ typ] returns a [ok] witness corresponding to to [typ] *) 
let rec ok_of_typ = function
  | TyConstant TyFloat -> OkFloat
  | TyArrow (t1, t2) ->
     OkArrow (ok_of_typ t1, ok_of_typ t2)
  | TyPair (t1, t2) ->
     OkPair (ok_of_typ t1, ok_of_typ t2)

(* {1 How to handle the local envornment } *)

(* Dans son papier C. Elliott propose le schéma de compilation suivant pour les
 * fonctions à plusieurs variables : 
     { fun x -> fun y -> U } => { curry (fun (x, y) -> U) }
 * Le problème est que le langage Source ne permet pas de binding de paires.
 * Pour paller ce problème, je mets les variables locales dans un environment
 * local [local_env].
 * Le but de cet environement est de pouvoir compiler facilement des termes 
 * [Var ident]. Pour cela il faut facilement être capable de trouver la liste de
 * séquences de [fst], [snd], [id] correspondant à la variable.
 * Pour cette raison, la valeur liée à la clef de la variable est un [path] qui
 * décrit cette séquence : 
     * - Si la variable est seulle dans l'environement, on l'obtient par [id] et
     * la séquence associée est la liste vide
     * - Si on doit rajouter une nouvelle variable on lui donne un chemin
     * quicorrespond à [snd] et on rajoute aux séquences des autres variables
     * déjà présentes un chemin vers la droite. *)
(* Il faut aussi remarquer que l'environement a une forme de peigne : au plus
 * une occurence de [Right] peut être dans une séquence et ce forcément à la fin
 * *)

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



(** Le type d'un élément d'un séquence *)
type direction = 
    | Left    (** correspond à fst *)
    | Right   (** correspond à snd *)

type path = direction list

type local_env = (path SMap.t)*typ
  (** dans un environement local, on stocke : 
      * une `map` :: string -> path
      * le type de l'environement actuel *)

type glob_env = (Target.t * term Source.t) SMap.t

  (** [print_env env] print [env] in the standard output *)
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

  (** [add_env env ident typ] add a variable [ident) of type [typ] in [env] *)
let add_env (map, typ) ident new_typ = 
    let _ = if SMap.is_empty map then assert false in
    let map = SMap.map (fun l -> Left::l) map in
    let map = SMap.add ident [Right] map in
    let typ = TyPair (typ, new_typ) in
    map,typ

  (** [extract_var env ident] compile the call to the variable [ident] in the
   local environmenti [env] *)
let extract_var (map, typ) ident = 
  let path = SMap.find ident map in
  let rec follow_path typ = function
    | [] -> (* empty : shortcut for identity *)
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




(* ------------------------------------------------
 * Core Function
 * ------------------------------------------------
 *)
  (** [compile local_env glob_env term] returns the compiled term in the target
   langage and a [ok] witness corrzesponding to the result of the term *)
let rec compile local_env glob_env : term Source.t -> Target.t *  Target.ok = function
  (* 
   * Lambda 
   *)
  | Lam ((Id ident, typ), term) ->
    let env = add_env local_env ident typ in
    let code, ok_res = compile env glob_env term in
    let oka = ok_of_typ @@ snd @@ local_env in
    let okb = ok_of_typ typ in
    let curry = Curry (oka, okb, ok_res) in
    App (curry, code), OkArrow ((ok_of_typ typ), ok_res) 
  (*
   * Var (1st case: local variable)
   *)
  | Var (Id ident) when SMap.mem ident (fst local_env) -> 
    extract_var local_env ident
  (*
   * Var (2nd: global variable)
   *)
  | Var (Id ident) when SMap.mem ident glob_env ->
    let src = SMap.find ident glob_env |> snd  in
      compile local_env glob_env src
  (*
   * Var This case should never occurs
   *)
  | Var (Id ident) ->
    assert false
  (*
   * Compiling a primitive with both arguments
   *)
  | App (App (Primitive f0, u), v) ->
  begin
    let code_u, ok_u = compile local_env glob_env u in
    let code_v, ok_v = compile local_env glob_env v in
    let _ = assert (ok_u = OkFloat && ok_v = OkFloat) in
    match f0 with
    | Sin | Cos | Exp | Inv | Neg -> 
      assert false
    | Add | Mul -> 
      let ok_a = ok_of_typ @@ snd @@ local_env in
      let fork = Fork (ok_a, ok_u, ok_v) in
      let compose = Compose (ok_a, OkPair (ok_u, ok_v), OkFloat) in
      App (
          App (compose, Primitive f0),
          App (
              App (fork, code_u),
              code_v
              )
      ), OkFloat
  end
  (*
   * Compiling a primitive with only one argument
   *)
  | App (Primitive f0, v) ->
  begin
    let code_v, ok_v = compile local_env glob_env v in
    let _ = assert (ok_v = OkFloat) in
    match f0 with
      | Sin | Cos | Exp | Inv | Neg -> 
        let ok_a = ok_of_typ (snd local_env) in
        let compose = Compose (ok_a, OkFloat, OkFloat) in
        App (
            App (compose, Primitive f0), 
            code_v
            ), OkFloat
      | Add | Mul -> 
        let ok_a = ok_of_typ (snd local_env) in
        let compose = Compose (ok_a, OkFloat, OkArrow (OkFloat, OkFloat)) in
        let curry = Curry (OkFloat, OkFloat, OkFloat) in
        App (
            App (
                compose,
                App (curry, Primitive f0)),
            code_v), OkArrow (OkFloat, OkFloat)
  end
  (*
   * Compiling an application : general case
   *)
  | App (u, v) ->
    let code_u, ok_u = compile local_env glob_env u in
    let code_v, ok_v = compile local_env glob_env v in
    let ok_res = match ok_u with
      | OkArrow (ok_a, ok_b) when ok_a = ok_v -> ok_b
      | _ -> assert false
    in
    let ok_a = ok_of_typ (snd local_env) in
    let fork = Fork (ok_a, ok_u, ok_v) in
    let apply = Apply (ok_v, ok_res) in
    let compose = Compose (ok_a, (OkPair (ok_u, ok_v)), ok_res) in
      App (
        App (compose, apply),
        App (
          App (fork, code_u),
          code_v
        )
      ), ok_res
  (*
   * Pair
   *)
  | Pair (u, v) ->
    let code_u, ok_u = compile local_env glob_env u in
    let code_v, ok_v = compile local_env glob_env v in
    let ok_a = ok_of_typ (snd local_env) in
    let fork = Fork (ok_a, ok_u, ok_v) in
    App (
        App (fork, code_u),
        code_v), OkPair (ok_u, ok_v)
  (*
   * Fst
   *)
  | Fst u ->
    let code_u, ok_u = compile local_env glob_env u in
    let ok_a, ok_b = match ok_u with
      | OkPair (ok_a, ok_b) -> ok_a, ok_b
      | _ -> assert false
    in
    let exl = Exl (ok_a, ok_b) in
    let ok_0 = ok_of_typ (snd local_env) in
    let compose = Compose (ok_0, ok_u, ok_a) in
    App (
        App (compose, exl),
        code_u), ok_a
  (*
   * Snd
   *)
  | Snd u -> 
    let code_u, ok_u = compile local_env glob_env u in
    let ok_a, ok_b = match ok_u with
      | OkPair (ok_a, ok_b) -> ok_a, ok_b
      | _ -> assert false
    in
    let exr = Exr (ok_a, ok_b) in
    let ok_0 = ok_of_typ (snd local_env) in
    let compose = Compose (ok_0, ok_u, ok_b) in
    App (
        App (compose, exr),
        code_u), ok_b
  (*
   * Litteral
   *)
  | Literal litt -> 
    let ok_a = ok_of_typ (snd local_env) in
    let it = It ok_a in
    let compose = Compose (ok_a, OkUnit, OkFloat) in
    let unitarrow = UnitArrow OkFloat in
      App (
          App (
              compose, 
              App (unitarrow, Literal litt)),
          it), OkFloat
  (* Because of the preious cases and the eta expansion: 
      * should never occurs
   *)
  | Primitive f0 -> assert false

  (** [compile_init glob_env (binding, term)] init the compilation by creating
   an environment with the firt bind variable *)
let compile_init glob_env (((Id ident, typ), term0) : binding*term) =
  let new_env, term = 
    match term0 with
    | Lam ((Id ident, typ), term) ->
      let map = SMap.singleton ident [] in
      (map, typ), term
    | _ -> assert false
  in
  let code, ok = compile new_env glob_env term in 
  SMap.add ident (code, term0) glob_env




(** [source_to_categories translates a [source] in a [target] language
    made of categorical combinators. *)
let source_to_categories : Source.program -> Target.program = fun source ->
    let global_env = List.fold_left compile_init SMap.empty source in
    List.map 
      (fun ((Id ident, typ), _) -> 
          (Id ident, typ), SMap.find ident global_env |> fst)
      source
