import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Geometry of a selected exceptional zero

A uniform constant bounded by log(3)/4 puts each exceptional zero strictly
to the right of three quarters, separating it from its reflection.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem isExceptionalZero_three_quarters_lt_re_and_ne_reflection
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hN : 3 <= N) {c : Real} (hc : c <= Real.log 3 / 4)
    {beta : Complex} (hExceptional : IsExceptionalZero c chi beta) :
    And ((3 / 4 : Real) < beta.re) (Ne beta (1 - beta)) := by
  have hNReal : (3 : Real) <= (N : Real) := (Nat.cast_le).2 hN
  have hLogThreePos : 0 < Real.log (3 : Real) :=
    Real.log_pos (by norm_num)
  have hLogNLower : Real.log (3 : Real) <= Real.log N :=
    Real.log_le_log (by norm_num) hNReal
  have hLogNPos : 0 < Real.log N := hLogThreePos.trans_le hLogNLower
  have hLogNNe : Ne (Real.log N) 0 := ne_of_gt hLogNPos
  have hcScaled : c <= (1 / 4 : Real) * Real.log N := by linarith
  have hFraction : c / Real.log N <= (1 / 4 : Real) := by
    calc
      c / Real.log N <= ((1 / 4 : Real) * Real.log N) / Real.log N :=
        div_le_div_of_nonneg_right hcScaled hLogNPos.le
      _ = (1 / 4 : Real) := by field_simp
  have hLower : (3 / 4 : Real) < beta.re := by
    linarith [hExceptional.2.2.2.2]
  have hDistinct : Ne beta (1 - beta) := by
    intro hEqual
    have hRe := congrArg Complex.re hEqual
    simp only [Complex.sub_re, Complex.one_re] at hRe
    linarith
  exact And.intro hLower hDistinct

end BombieriVinogradov.SiegelWalfisz
