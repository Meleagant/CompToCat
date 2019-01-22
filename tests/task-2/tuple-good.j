let (f : float -> float * float * float) =
    fun (x : float) ->
    (x, x, x)
(* This exampleshows that : x, x, x = (x, x), x.
	i.e. the tuple is left-associativ	*)
let (f2 : float * float * float -> float ) =
	fun (x: float * float * float ) -> fst (fst  x)

let (f3 : float * float * float -> float ) =
	fun (x: float * float * float ) -> snd x

let (try_fst_order_functions : float -> float) = 
	fun (x: float) ->
	(* We can also define first-order functions *)
	(fun (x: float) -> sin x) x
