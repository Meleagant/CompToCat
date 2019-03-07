(** We need to evaluate [error] defined in [tiny_mlp.j]... *)
module Eval = Tiny_mlp.Make (Category.FloatLambdaCat)
(** ... and we also need the derivative of [error]. *)
module Diff = Tiny_mlp.Make (DiffCat)
open DiffCat

(** We study a very small MLP with two inputs, one output
    and no hidden layer. *)
type net = float * float

let make_net wxu wyu = (wxu, wyu)

let update_net (wxu, wyu) dwxu dwyu = make_net (wxu +. dwxu) (wyu +. dwyu)

(** A training set is a list of couples made of inputs and expected outputs. *)
type training_set = ((float * float) * float) list

(** A trained net must minimize the error function defined in tiny_mlp.j. *)
let acceptable_error = 0.01

let epsilon = DiffCat.epsilon

(* Si vous voulez voir l'erreur décroitre, ajoutez simplement --print-error
 * dans la commande qui lance ce fichier *)
let print_error = Array.mem "--print-error" Sys.argv

let eval_net net training_set =
  List.map 
    (fun (input, expectation) ->
      Eval.error ((input, net), expectation)
    ) 
    training_set
  |> List.fold_left max min_float

let grad (x, y) (wx, wy) result = 
    let dx = ((0., 0.), (epsilon, 0.)), 0. in
    let dy = ((0., 0.), (0., epsilon)), 0. in
    let arg = ((x, y), (wx, wy)), result in
    let err_x = epsilon_dapply Diff.error arg dx in
    let err_y = epsilon_dapply Diff.error arg dy in
    err_x, err_y

  (** [gard_set net training_set] returns the average gradient computed for
   all elements in the [training_set] by the [net]. *)
let grad_set net training_set = 
    List.fold_left
    (fun (err_x, err_y) ((x, y), result) -> 
        let err_x0, err_y0 = grad (x, y) net result in
        err_x +. err_x0, err_y +. err_y0)
    (0., 0.)
    training_set
    |>
    (fun (err_x, err_y) -> 
        let l = float_of_int @@ List.length @@ training_set in
        err_x /. l, err_y /. l
    )

(** [train training_set] returns a neural network trained for the
    [training_set]. *)
let train : training_set -> net = fun training_set ->
  let net = ref (1., 1.) in
  let _ = 
    while eval_net !net training_set >= acceptable_error do
      let _ = if print_error then
        Printf.printf "Error : %f\n" (eval_net !net training_set) in
      let grad_x, grad_y = grad_set !net training_set in
        net := (fst !net -. grad_x, snd !net -. grad_y)
    done
  in
    !net

let test =
  let training_set = [ (0., 1.), 0.; (1., 0.), 1. ] in
  let trained_net = train training_set in
  let _ = Printf.printf "Final error : %f\n" (eval_net trained_net training_set)
  in
  let _ = Printf.printf "Trained Net: wx = %f\n             wy = %f\n"
    (fst trained_net) (snd trained_net)  
  in
  assert (eval_net trained_net training_set < acceptable_error)
