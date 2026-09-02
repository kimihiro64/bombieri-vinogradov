import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.OptimizedCenteringScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.UnitVerticalIntegralBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.VerticalIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Main
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Centered optimized Perron approximation

This module combines the ordinary optimized Perron error with the unit-point
centering correction.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- One absolute constant controls the centered optimized vertical integral by
the published Perron scale plus the logarithmic centering cost. -/
theorem exists_norm_centeredVerticalIntegral_sub_halfSum_le_optimized :
    Exists fun C : Real => And (0 < C)
      (forall N : Nat, forall [NeZero N],
        forall chi : DirichletCharacter Complex N, forall x : Nat,
          2 < x -> forall T : Real, 0 < T ->
            norm (centeredExplicitFormulaVerticalIntegral chi x
              (optimizedPerronLine x) T -
                characterChebyshevHalfSum x chi) <=
              C * (((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) +
                Real.log (x : Real))) := by
  have hMainExist :=
    exists_norm_explicitFormulaVerticalIntegral_sub_halfSum_le_optimized
  have hUnitExist := exists_norm_explicitFormulaVerticalIntegral_one_le_div
  let C0 : Real := hMainExist.choose
  let C1 : Real := hUnitExist.choose
  have hMainSpec := hMainExist.choose_spec
  have hUnitSpec := hUnitExist.choose_spec
  refine Exists.intro (C0 + C1) (And.intro (by linarith) ?_)
  intro N hNe chi x hx T hT
  let A : Real := (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T
  let L : Real := Real.log (x : Real)
  have hA : 0 <= A := by
    unfold A
    positivity
  have hL : 0 <= L := by
    unfold L
    exact le_trans zero_le_one (one_le_log_natCast hx)
  have hMain :
      norm (explicitFormulaVerticalIntegral chi x
        (optimizedPerronLine x) T - characterChebyshevHalfSum x chi) <=
        C0 * A := by
    exact hMainSpec.2 N chi x hx T hT
  have hLineLower := optimizedPerronLine_gt_one hx
  have hLineUpper : optimizedPerronLine x <= 3 :=
    (optimizedPerronLine_le_two hx).trans (by norm_num)
  have hUnit :=
    hUnitSpec.2 N chi (optimizedPerronLine x) T
      hLineLower hLineUpper hT
  have hUnitLog :
      norm (explicitFormulaVerticalIntegral chi 1
        (optimizedPerronLine x) T) <= C1 * L := by
    calc
      norm (explicitFormulaVerticalIntegral chi 1
          (optimizedPerronLine x) T) <=
        C1 / (optimizedPerronLine x - 1) := hUnit
      _ = C1 * (1 / (optimizedPerronLine x - 1)) := by ring
      _ = C1 * L := by
        rw [one_div_optimizedPerronLine_sub_one hx]
  have hTriangle :
      norm (centeredExplicitFormulaVerticalIntegral chi x
        (optimizedPerronLine x) T - characterChebyshevHalfSum x chi) <=
        norm (explicitFormulaVerticalIntegral chi x
          (optimizedPerronLine x) T - characterChebyshevHalfSum x chi) +
        norm (explicitFormulaVerticalIntegral chi 1
          (optimizedPerronLine x) T) := by
    unfold centeredExplicitFormulaVerticalIntegral
    calc
      norm ((explicitFormulaVerticalIntegral chi x
          (optimizedPerronLine x) T -
            explicitFormulaVerticalIntegral chi 1
              (optimizedPerronLine x) T) -
          characterChebyshevHalfSum x chi) =
        norm ((explicitFormulaVerticalIntegral chi x
            (optimizedPerronLine x) T -
              characterChebyshevHalfSum x chi) -
            explicitFormulaVerticalIntegral chi 1
              (optimizedPerronLine x) T) := by
          congr 1
          ring
      _ <=
        norm (explicitFormulaVerticalIntegral chi x
          (optimizedPerronLine x) T - characterChebyshevHalfSum x chi) +
        norm (explicitFormulaVerticalIntegral chi 1
          (optimizedPerronLine x) T) := norm_sub_le _ _
  calc
    norm (centeredExplicitFormulaVerticalIntegral chi x
        (optimizedPerronLine x) T - characterChebyshevHalfSum x chi) <=
      norm (explicitFormulaVerticalIntegral chi x
        (optimizedPerronLine x) T - characterChebyshevHalfSum x chi) +
      norm (explicitFormulaVerticalIntegral chi 1
        (optimizedPerronLine x) T) := hTriangle
    _ <= C0 * A + C1 * L := add_le_add hMain hUnitLog
    _ <= (C0 + C1) * A + (C0 + C1) * L := by
      apply add_le_add
      exact mul_le_mul_of_nonneg_right (by linarith [hUnitSpec.1]) hA
      exact mul_le_mul_of_nonneg_right (by linarith [hMainSpec.1]) hL
    _ = (C0 + C1) * (A + L) := by ring

end BombieriVinogradov.SiegelWalfisz
