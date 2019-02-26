open Target

let rec size = function
    | App (u,v) -> (size u) + (size v)
    | _ -> 1

let rec simplify = function
  | App (App (Compose _, Identity _), u)
  | App (App (Compose _, u), Identity _) -> u, true
  | App (
        App (Compose (ok0, OkPair (OkArrow (okd, okb),_), _ ), Apply _),
        App (App (
                  Fork _, 
                  App (Curry _, h)), 
             g)) ->
    let id = Identity ok0 in
    let fork = Fork (ok0, ok0, okd) in
    let compose = Compose (ok0, OkPair (ok0, okd), okb) in
    App (
        App (compose, h),
        App (App (fork, id), g)
        ), true

  | App (u, v) -> 
    let simp_u, modify_u = simplify u in
    let simp_v, modify_v = simplify v in
    App (simp_u, simp_v), modify_u || modify_v

  | x -> x, false

let rec simplify_iter prog = 
    let prog, modify = simplify prog in
    if modify then
        simplify_iter prog
    else 
        prog

let simplify_wrap prog = 
    let _ = Printf.printf "Avant simplify: %d\n" (size prog) in
    let prog = simplify_iter prog in
    let _ = Printf.printf "Après simplify: %d\n" (size prog) in
      prog


(** [rewrite defs] applies category laws to remove [apply] and [curry]
    from the compiled programs. *)
let rewrite : Target.program -> Target.program = fun defs ->
  if !Options.simplify then
      List.map (fun (bind, prog) -> bind, simplify_wrap prog) defs
  else
    defs
