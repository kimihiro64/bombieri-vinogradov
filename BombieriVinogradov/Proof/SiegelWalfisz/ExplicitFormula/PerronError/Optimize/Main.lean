import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Main
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Scale

/-!
# Optimized Perron approximation

This module proves the character version of Strombergsson Corollary 14.3 for
natural `x`, using the already established full source-scale estimate.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- One absolute constant controls the optimized finite Perron integral error,
uniformly in the character and modulus. -/
theorem exists_norm_explicitFormulaVerticalIntegral_sub_halfSum_le_optimized :
    Exists fun C : Real => And (0 < C) (forall N : Nat, forall [NeZero N],
      forall chi : DirichletCharacter Complex N, forall x : Nat, 2 < x ->
      forall T : Real, 0 < T ->
        norm (explicitFormulaVerticalIntegral chi x (optimizedPerronLine x) T -
          characterChebyshevHalfSum x chi) <=
          C * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T)) := by
  have hExist := exists_norm_explicitFormulaVerticalIntegral_sub_halfSum_le_scale
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 0 < C0 := hSpec.1
  refine Exists.intro (4 * C0) (And.intro (by positivity) ?_)
  intro N hNe chi x hx T hT
  have hLineLower := optimizedPerronLine_gt_one hx
  have hLineUpper : optimizedPerronLine x <= 3 :=
    (optimizedPerronLine_le_two hx).trans (by norm_num)
  have hGeneral := hSpec.2 N chi x hx (optimizedPerronLine x) T
    hLineLower hLineUpper hT
  have hScale := optimizedPerronScale_le hx hT
  calc
    norm (explicitFormulaVerticalIntegral chi x (optimizedPerronLine x) T -
        characterChebyshevHalfSum x chi) <=
      C0 * (((x : Real) ^ optimizedPerronLine x /
          (T * (optimizedPerronLine x - 1))) +
        ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T)) := hGeneral
    _ <= C0 *
        (4 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T)) :=
      mul_le_mul_of_nonneg_left hScale hC0.le
    _ = (4 * C0) *
        ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by ring

end BombieriVinogradov.SiegelWalfisz
