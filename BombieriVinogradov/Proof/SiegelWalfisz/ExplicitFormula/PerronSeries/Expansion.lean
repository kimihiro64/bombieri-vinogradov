import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Definitions

/-!
# Twisted von Mangoldt expansion of the explicit-formula integrand

This module rewrites the negative logarithmic derivative using Mathlib's
twisted von Mangoldt L-series theorem and distributes the fixed Perron factor
through its convergent series.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- On the half-plane of absolute convergence, the negative logarithmic
derivative is the twisted von Mangoldt L-series. -/
theorem neg_logDeriv_LFunction_eq_LSeries
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : 1 < s.re) :
    -logDeriv chi.LFunction s = LSeries (twistedMangoldtSequence chi) s := by
  have hSeries := DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs
  rw [logDeriv_apply,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
    DirichletCharacter.LFunction_eq_LSeries chi hs]
  have hSequence : twistedMangoldtSequence chi =
      (fun n : Nat => chi n) *
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    funext n
    rfl
  rw [hSequence, <- neg_div]
  exact hSeries.symm

/-- The explicit-formula integrand is the termwise Perron expansion of the
twisted von Mangoldt L-series. -/
theorem explicitFormulaIntegrand_eq_tsum
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (s : Complex) (hs : 1 < s.re) :
    explicitFormulaIntegrand chi x s =
      tsum (fun n : Nat => explicitFormulaDirichletTerm chi x n s) := by
  rw [explicitFormulaIntegrand]
  rw [show logDeriv chi.LFunction s * (-((x : Complex) ^ s / s)) =
      (-logDeriv chi.LFunction s) * ((x : Complex) ^ s / s) by ring]
  rw [neg_logDeriv_LFunction_eq_LSeries chi hs]
  rw [LSeries]
  simp only [explicitFormulaDirichletTerm]
  rw [<- tsum_mul_right]

end BombieriVinogradov.SiegelWalfisz
