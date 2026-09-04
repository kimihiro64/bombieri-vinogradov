import BombieriVinogradov.Assembly.SiegelWalfisz.CharacterEstimate.PrimitiveZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.SelectedZeroSumScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Positivity

/-!
# Uniform retained-zero decay at the square-root-log height

The reciprocal bound chooses its constant before all character data.
The selected contour height and logarithmic absorption preserve that order.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_truncatedCriticalZeroSum_selectedHeight_le_exp
    {c a : Real} (hc : 0 < c) (ha : 0 < a) (hRate : 2 * a <= c / 4) :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
          ExplicitFormulaZeroFreeData c chi ->
          forall (e : Option Complex), IsExceptionalZeroChoice c chi e ->
            forall {x : Nat}, 3 <= x ->
              (N : Real) <= Real.exp (Real.sqrt (Real.log x)) ->
                norm (truncatedCriticalZeroSum chi x
                  (Real.exp (Real.sqrt (Real.log x))) e) <=
                  K * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x))))) := by
  choose K0 hK0Pos hK0 using exists_norm_truncatedCriticalZeroSum_le_exp_gap_mul_log_sq hc
  refine Exists.intro (32 * K0 / a ^ 2) (And.intro (by positivity) ?_)
  intro N inst hN chi hchi hPrimitive hData e hChoice x hx hModulus
  have hxOne : 1 <= x := by omega
  have hHeight : 0 < Real.exp (Real.sqrt (Real.log x)) := Real.exp_pos _
  have hRaw := hK0 hN hchi hPrimitive hData e hChoice hxOne hHeight
  exact hRaw.trans (selectedZeroSumScale_le_exp hK0Pos.le hc ha hRate hN hx hModulus)

end BombieriVinogradov.SiegelWalfisz
