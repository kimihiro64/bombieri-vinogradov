import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Interchange

/-!
# Normalized vertical-integral interchange

This module lifts the interval-integral interchange through the fixed Perron
normalization and rewrites the pointwise series as the explicit-formula
integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The normalized vertical integral of the explicit-formula integrand is the
sum of the normalized vertical integrals of its Dirichlet terms. -/
theorem explicitFormulaVerticalIntegral_eq_tsum_VIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) :
    explicitFormulaVerticalIntegral chi x c T =
      tsum (fun n : Nat =>
        VIntegral' (explicitFormulaDirichletTerm chi x n) c (-T) T) := by
  have hFunctions : (fun t : Real =>
      explicitFormulaIntegrand chi x (c + t * Complex.I)) =
      fun t : Real => tsum (fun n : Nat =>
        perronSeriesFunction chi x n c t) := by
    funext t
    apply explicitFormulaIntegrand_eq_tsum
    simpa using hc
  have hInterchange := tsum_intervalIntegral_perronSeriesFunction
    (T := T) chi hx hc
  simp only [explicitFormulaVerticalIntegral, VIntegral', VIntegral]
  rw [hFunctions]
  rw [<- hInterchange]
  rw [<- tsum_const_smul'' Complex.I]
  rw [<- tsum_const_smul'' (1 / (2 * Real.pi * Complex.I))]
  rfl

end BombieriVinogradov.SiegelWalfisz
