include Fst.Make (Category.FloatLambdaCat)

let tests =
  assert (fstf (0., 1.) = 0.)
