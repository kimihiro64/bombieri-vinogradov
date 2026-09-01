import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanAssembly
import Mathlib.Tactic

/-!
# Quantitative maximal bounds for the assembled Vaughan mean

This module lifts the first Type I estimates to the common endpoint maximum
before aggregating all four source contributions.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

theorem maximalVaughanS1Norm_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (v X : Nat) :
    maximalVaughanS1Norm v X q chi <=
      (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((X + 1 : Nat) : Real)) := by
  unfold maximalVaughanS1Norm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  rw [vaughanS1_eq_typeIOneCharacterSum]
  apply (norm_typeIOneCharacterSum_le hq hchi v Y).trans
  have hlog : Real.log ((Y + 1 : Nat) : Real) <=
      Real.log ((X + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.add_le_add_right hYX 1
  have hlogq : 0 <= Real.log (2 * (q : Real)) := by
    apply Real.log_nonneg
    have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
    linarith
  gcongr

theorem maximalVaughanS1Norm_trivial (v X q : Nat)
    (chi : DirichletCharacter Complex q) :
    maximalVaughanS1Norm v X q chi <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 := by
  unfold maximalVaughanS1Norm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  rw [vaughanS1_eq_typeIOneCharacterSum]
  apply (norm_typeIOneCharacterSum_trivial v Y q chi).trans
  have hlog : Real.log ((Y + 1 : Nat) : Real) <=
      Real.log ((X + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.add_le_add_right hYX 1
  have hlogY := Real.log_natCast_nonneg (Y + 1)
  have hlogX := Real.log_natCast_nonneg (X + 1)
  gcongr

end BombieriVinogradov.VaughanMeanValue
