import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.FactsFromBounds
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.Main
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.NonquadraticRealZeroExclusion
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A uniform zero-free constant for the explicit formula

The existing zero-free region and nonquadratic real-zero exclusion supply
one smaller positive constant with all retained and exceptional-zero facts.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_explicitFormulaZeroFreeData :
    exists c : Real, And (0 < c)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        3 <= N -> Ne chi 1 -> ExplicitFormulaZeroFreeData c chi) := by
  choose C hC hRegion using dirichletZeroFreeRegion
  choose R hR hNonquadratic using exists_nonquadratic_realZero_exclusion
  let c : Real := min C (min R (Real.log 3 / 4))
  have hLogCutoffPos : 0 < Real.log (3 : Real) / 4 :=
    div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min hC (lt_min hR hLogCutoffPos)
  have hcC : c <= C := by
    dsimp [c]
    exact min_le_left _ _
  have hcR : c <= R := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcLog : c <= Real.log 3 / 4 := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine Exists.intro c (And.intro hcPos ?_)
  intro N inst chi hN hchi
  have hSource := hRegion chi hchi
  have hLogNNonneg : 0 <= Real.log N := Real.log_natCast_nonneg N
  exact {
    regularGap := by
      intro s hs hzero hRegular
      have hHeightNonneg : 0 <= Real.log (abs s.im + 2) := by
        apply Real.log_nonneg
        linarith [abs_nonneg s.im]
      have hDenominatorNonneg :
          0 <= Real.log N + Real.log (abs s.im + 2) := by linarith
      have hScale := div_le_div_of_nonneg_right hcC hDenominatorNonneg
      exact hScale.trans (hSource.1 s hs hzero hRegular)
    realUnique := by
      intro s t hs ht hsZero htZero hsReal htReal hsGap htGap
      have hScale : c / Real.log N <= C / Real.log N :=
        div_le_div_of_nonneg_right hcC hLogNNonneg
      exact hSource.2.1 s t hs ht hsZero htZero hsReal htReal
        (hsGap.trans hScale) (htGap.trans hScale)
    exceptional := by
      intro beta hExceptional
      exact exceptionalZeroFacts_of_zeroFreeBounds hN hcC hcR hcLog
        hSource.2.2 (hNonquadratic chi hchi) hExceptional
  }

end BombieriVinogradov.SiegelWalfisz
