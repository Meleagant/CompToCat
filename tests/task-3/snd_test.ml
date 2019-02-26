include Snd.Make (Category.FloatLambdaCat)

let tests =
  assert (sndf (0., 1.) = 1.)
