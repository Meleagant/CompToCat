let (cos_sin : float -> float* float) = fun (x : float) -> (sin x , cos x )
let (bidule : float -> float) = fun (x: float) -> snd (cos_sin x)  
