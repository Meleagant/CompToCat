open Target

let rec size = function
    | App (u,v) -> (size u) + (size v)
    | _ -> 1


  (** [simplify term] returns a [term'] which is equivalent to the argument
   * [term] but may be simplified.and a boolean equals to true if term as be
   * simplified. *)
  (* La première stratégie testée consistait à traduire le term en une liste de
   * sous-termes pour aplatir l'arbre avec les composition.
   * Mais comme le code produit par le compilier contient déjà un grand nombre
   * de simplification, les seuls cas de simplification nécessaires peuvent être
   * traités de manière gloutonne avec le pattern-matching qui suit *)
let rec simplify = function
  (* simplification de 
   * (apply o ( curry h /\ g )) => (h o (id /\ g)) 
   *)
  | App (
        App (Compose (ok0, OkPair (OkArrow (okd, okb),_), _ ), Apply _),
        App (App (
                  Fork _, 
                  App (Curry _, h)), 
             g)) ->
    let id = Identity ok0 in
    let _ = if !Options.print_simplification then
      Printf.printf "On simplifie un [apply ∘ (curry h Δ g)] -> [h ∘ (id Δ g)]\n" 
    in
    let fork = Fork (ok0, ok0, okd) in
    let compose = Compose (ok0, OkPair (ok0, okd), okb) in
    App (
        App (compose, h),
        App (App (fork, id), g)
        ), true

  (* simplification des identités à gauche & à droite *)
  | App (App (Compose _, Identity _), u)
  | App (App (Compose _, u), Identity _) -> 
    let _ = if !Options.print_simplification then
      Printf.printf "On simplifie un [id ∘ f] -> [f]\n" 
    in
      u, true
  (* cas récursifs *)
  | App (u, v) -> 
    let simp_u, modify_u = simplify u in
    let simp_v, modify_v = simplify v in
    App (simp_u, simp_v), modify_u || modify_v
  (* Cas de base *)
  | x -> x, false

  (** [simplify_iter prog] calls [simplify] as long as it simplifies [prog] *)
let rec simplify_iter prog = 
    let prog, modify = simplify prog in
    if modify then
        simplify_iter prog
    else 
        prog

  (** [simplify_wrap] is a small wrapper for [simplify_*]. It also prints the
   * size of the term before and after simplification *)
let simplify_wrap prog = 
    let _ = if !Options.print_simplification then
      Printf.printf "Avant simplify: %d\n" (size prog) in
    let prog = simplify_iter prog in
    let _ = if !Options.print_simplification then
      Printf.printf "Après simplify: %d\n" (size prog) 
    in
      prog


(** [rewrite defs] applies category laws to remove [apply] and [curry]
    from the compiled programs. *)
let rewrite : Target.program -> Target.program = fun defs ->
  if !Options.simplify then
      List.map (fun (bind, prog) -> bind, simplify_wrap prog) defs
  else
    defs
