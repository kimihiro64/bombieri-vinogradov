import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ComplexZeroGapBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveCompletedZeroIndex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Complex-character zero gap at an arbitrary level

This module completes the primitive-to-imprimitive transfer in
Strombergsson's complex-character zero-free argument.  It preserves the zero
and its height exactly, then weakens the conductor logarithm to the ambient
level logarithm only in the final comparison.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_imprimitive_complexZero_gap :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        chi ≠ 1 -> chi ^ 2 ≠ 1 ->
          forall {s : Complex}, 0 < s.re -> chi.LFunction s = 0 ->
            c / (Real.log N + Real.log (|s.im| + 2)) ≤ 1 - s.re := by
  obtain ⟨c, hcPos, hPrimitiveGap⟩ := exists_primitive_complexZero_gap
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN chi hchi hchiSquare s hs hzero
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hPrimitiveNe :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      chi hchi
  have hPrimitiveSquare :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_ne_one_of_pow_ne_one
      chi hchiSquare
  obtain ⟨p, hp⟩ :=
    exists_primitive_completedZeroIndex_of_LFunction_eq_zero
      chi hchi hs hzero
  have hGap := hPrimitiveGap hPrimitiveNe
    chi.primitiveCharacter_isPrimitive hPrimitiveSquare p
  rw [hp] at hGap
  have hConductorLower :=
    BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hchi
  have hConductorLevel :=
    BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogConductorLower : Real.log 3 ≤ Real.log chi.conductor :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hConductorLower)
  have hHeightNonneg : 0 ≤ Real.log (|s.im| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg s.im]
  have hPrimitiveDenominatorPos :
      0 < Real.log chi.conductor + Real.log (|s.im| + 2) := by
    linarith
  have hLogConductorLevel : Real.log chi.conductor ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast NeZero.pos chi.conductor)
      (by exact_mod_cast hConductorLevel)
  have hDenominatorLe :
      Real.log chi.conductor + Real.log (|s.im| + 2) ≤
        Real.log N + Real.log (|s.im| + 2) :=
    add_le_add hLogConductorLevel le_rfl
  have hRatio :
      c / (Real.log N + Real.log (|s.im| + 2)) ≤
        c / (Real.log chi.conductor + Real.log (|s.im| + 2)) :=
    div_le_div_of_nonneg_left hcPos.le hPrimitiveDenominatorPos hDenominatorLe
  exact hRatio.trans hGap

end BombieriVinogradov.SiegelWalfisz
