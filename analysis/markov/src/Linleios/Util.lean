
/--
The error function.
-/
partial def erf (x : Float) : Float :=
  if x < 0
    then - erf (- x)
    else
      let p := 0.3275911
      let a₁ := 0.254829592
      let a₂ := -0.284496736
      let a₃ := 1.421413741
      let a₄ := -1.453152027
      let a₅ := 1.061405429
      let t := 1 / (1 + p * x)
      1 - (a₁ * t + a₂ * t^2 + a₃ * t^3 + a₄ * t^4 + a₅ * t^5) * Float.exp (- x^2)

/--
The CDF for a normal distribution.
-/
def cdfGaussian (x μ σ : Float) : Float :=
  (1 + erf ((x - μ) / σ / Float.sqrt 2)) / 2

/--
A bisection search.
-/
def bisectionSearch (f : Float → Float) (low high : Float) (ε : Float) (maxIter : Nat) : Float :=
  match maxIter with
  | 0 => (low + high) / 2
  | maxIter' + 1 =>
    let mid := (low + high) / 2
    let fmid := f mid
    if high - low < ε || Float.abs fmid < ε then
      mid
    else if f low * fmid < 0 then
      bisectionSearch f low mid ε maxIter'
    else
      bisectionSearch f mid high ε maxIter'
termination_by maxIter
