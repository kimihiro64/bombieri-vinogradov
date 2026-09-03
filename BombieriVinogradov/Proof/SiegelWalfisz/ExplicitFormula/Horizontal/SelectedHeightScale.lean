import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightScale
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Scale facts for a selected horizontal height

This module packages the logarithmic and absolute-value comparisons shared
by the positive and negative horizontal contour estimates.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem selectedHeight_scale_data
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {T Tprime : Real} (hT : 2 <= T)
    (hLower : T <= Tprime) (hUpper : Tprime <= T + 1) :
    And (1 <= zeroHeightLogScale N T)
      (And (2 <= abs Tprime)
        (Real.log N + Real.log (abs Tprime + 2) <=
          zeroHeightLogScale N T)) := by
  have hNOneNat : 1 < N :=
    lt_of_lt_of_le (by norm_num) hN
  have hNOneRealRaw : ((1 : Nat) : Real) < (N : Real) :=
    (Nat.cast_lt).2 hNOneNat
  have hNOneReal : (1 : Real) < (N : Real) := by
    simpa using hNOneRealRaw
  have hLogNPos : 0 < Real.log N :=
    Real.log_pos hNOneReal
  have hTArgOne : (1 : Real) < T + 3 := by
    linarith
  have hLogTPos : 0 < Real.log (T + 3) :=
    Real.log_pos hTArgOne
  have hScaleOne : 1 <= zeroHeightLogScale N T := by
    dsimp [zeroHeightLogScale]
    linarith
  have hTprimeNonneg : 0 <= Tprime := by
    linarith
  have hAbsTprime : abs Tprime = Tprime :=
    abs_of_nonneg hTprimeNonneg
  have hAbsTprimeLower : 2 <= abs Tprime := by
    rw [hAbsTprime]
    exact hT.trans hLower
  have hCurrentArgPos : 0 < abs Tprime + 2 := by
    linarith [abs_nonneg Tprime]
  have hCurrentArgLe : abs Tprime + 2 <= T + 3 := by
    rw [hAbsTprime]
    linarith
  have hCurrentLogLe :
      Real.log (abs Tprime + 2) <= Real.log (T + 3) :=
    Real.log_le_log hCurrentArgPos hCurrentArgLe
  refine And.intro hScaleOne (And.intro hAbsTprimeLower ?_)
  dsimp [zeroHeightLogScale]
  linarith

end BombieriVinogradov.SiegelWalfisz
