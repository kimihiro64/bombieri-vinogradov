import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions

/-!
# Perron step weights at natural ratios

This module computes the three cases of the scalar Perron step weight at
`x / n` and transfers them to the twisted Dirichlet coefficient.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- A positive natural index below `x` receives Perron weight one. -/
theorem perronStepWeight_natRatio_eq_one_of_lt
    {x n : Nat} (hn : 0 < n) (hnx : n < x) :
    perronStepWeight ((x : Real) / (n : Real)) = 1 := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hnxReal : (n : Real) < (x : Real) := by exact_mod_cast hnx
  have hRatio : 1 < (x : Real) / (n : Real) := by
    rw [one_lt_div hnReal]
    exact hnxReal
  simp [perronStepWeight, not_lt_of_ge hRatio.le, ne_of_gt hRatio]

/-- The endpoint ratio receives Perron's half weight. -/
theorem perronStepWeight_natRatio_eq_half
    {x : Nat} (hx : 0 < x) :
    perronStepWeight ((x : Real) / (x : Real)) = 1 / 2 := by
  have hxNe : Ne (x : Real) 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  simp [hxNe, perronStepWeight]

/-- A positive natural index above `x` receives Perron weight zero. -/
theorem perronStepWeight_natRatio_eq_zero_of_lt
    {x n : Nat} (hn : 0 < n) (hxn : x < n) :
    perronStepWeight ((x : Real) / (n : Real)) = 0 := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hxnReal : (x : Real) < (n : Real) := by exact_mod_cast hxn
  have hRatio : (x : Real) / (n : Real) < 1 := by
    rw [div_lt_one hnReal]
    exact hxnReal
  simp [perronStepWeight, hRatio]

/-- Below the endpoint, the scalar step term is the full coefficient. -/
theorem scalarPerronStepTerm_eq_coeff_of_lt
    {N x n : Nat} (chi : DirichletCharacter Complex N)
    (hn : 0 < n) (hnx : n < x) :
    scalarPerronStepTerm chi x n = twistedMangoldtSequence chi n := by
  simp [scalarPerronStepTerm, Nat.ne_of_gt hn,
    perronStepWeight_natRatio_eq_one_of_lt hn hnx]

/-- At the endpoint, the scalar step term is half the coefficient. -/
theorem scalarPerronStepTerm_eq_half
    {N x : Nat} (chi : DirichletCharacter Complex N) (hx : 0 < x) :
    scalarPerronStepTerm chi x x =
      (1 / 2 : Complex) * twistedMangoldtSequence chi x := by
  rw [scalarPerronStepTerm, if_neg (Nat.ne_of_gt hx),
    perronStepWeight_natRatio_eq_half hx]
  simpa using mul_comm (twistedMangoldtSequence chi x) (1 / 2 : Complex)

/-- Above the endpoint, the scalar step term vanishes. -/
theorem scalarPerronStepTerm_eq_zero_of_lt
    {N x n : Nat} (chi : DirichletCharacter Complex N)
    (hn : 0 < n) (hxn : x < n) :
    scalarPerronStepTerm chi x n = 0 := by
  simp [scalarPerronStepTerm, Nat.ne_of_gt hn,
    perronStepWeight_natRatio_eq_zero_of_lt hn hxn]

end BombieriVinogradov.SiegelWalfisz
