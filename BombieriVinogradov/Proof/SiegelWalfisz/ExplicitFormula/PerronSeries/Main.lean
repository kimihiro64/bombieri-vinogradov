import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.TermIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.VerticalIntegralInterchange

/-!
# Perron-series representation of the explicit-formula integral

This module assembles the independent term-integral and series-interchange
branches into the finite-height Dirichlet-series representation.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The finite normalized explicit-formula integral is the convergent series
of twisted von Mangoldt coefficients times scalar truncated Perron kernels. -/
theorem explicitFormulaVerticalIntegral_eq_tsum_scalarPerronSeriesTerm
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) :
    explicitFormulaVerticalIntegral chi x c T =
      tsum (scalarPerronSeriesTerm chi x c T) := by
  calc
    explicitFormulaVerticalIntegral chi x c T =
        tsum (fun n : Nat =>
          VIntegral' (explicitFormulaDirichletTerm chi x n) c (-T) T) :=
      explicitFormulaVerticalIntegral_eq_tsum_VIntegral chi hx hc
    _ = tsum (scalarPerronSeriesTerm chi x c T) := by
      apply tsum_congr
      intro n
      exact VIntegral_explicitFormulaDirichletTerm_eq_scalarPerronSeriesTerm
        chi x n c T

end BombieriVinogradov.SiegelWalfisz
