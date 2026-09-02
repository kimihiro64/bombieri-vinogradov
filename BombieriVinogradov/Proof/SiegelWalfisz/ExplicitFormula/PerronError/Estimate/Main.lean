import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Scale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.SourceBound

/-!
# Perron error estimate

This module transfers the source-scale estimate to the finite explicit-formula
vertical integral for every Dirichlet character.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The finite explicit-formula integral differs from the half-weighted
character Chebyshev sum by the published Perron-error scale, uniformly in the
character and modulus. -/
theorem exists_norm_explicitFormulaVerticalIntegral_sub_halfSum_le_scale :
    Exists fun C : Real => And (0 < C) (forall N : Nat, forall [NeZero N],
      forall chi : DirichletCharacter Complex N, forall x : Nat, 2 < x ->
      forall c T : Real, 1 < c -> c < 2 -> 0 < T ->
        norm (explicitFormulaVerticalIntegral chi x c T -
          characterChebyshevHalfSum x chi) <=
          C * (((x : Real) ^ c / (T * (c - 1))) +
            ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T))) := by
  have hExist := exists_tsum_sourcePerronErrorMajorantTerm_le_scale
  let C : Real := hExist.choose
  have hSpec := hExist.choose_spec
  refine Exists.intro C (And.intro hSpec.1 ?_)
  intro N hNe chi x hx c T hc1 hc2 hT
  exact (norm_explicitFormulaVerticalIntegral_sub_halfSum_le_source chi
    (lt_trans zero_lt_two hx) hc1 hT).trans
      (hSpec.2 x hx c T hc1 hc2 hT)

end BombieriVinogradov.SiegelWalfisz
