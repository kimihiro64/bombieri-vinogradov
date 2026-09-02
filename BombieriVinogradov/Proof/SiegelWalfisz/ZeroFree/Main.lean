import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ImprimitiveComplexZeroGapBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ImprimitiveQuadraticExceptionalRegion
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.NonquadraticRealZeroExclusion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Effective Dirichlet zero-free region

This module combines the nonquadratic and quadratic branches under one
absolute constant. Nonquadratic zeros and nonreal quadratic zeros satisfy the
standard reciprocal-logarithmic gap. Any real zero in the smaller exceptional
region is unique and simple.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem dirichletZeroFreeRegion :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        chi ≠ 1 ->
          (forall s : Complex, 0 < s.re -> chi.LFunction s = 0 ->
            (chi ^ 2 ≠ 1 ∨ s.im ≠ 0) ->
              c / (Real.log N + Real.log (|s.im| + 2)) ≤ 1 - s.re) ∧
          (forall s t : Complex,
            0 < s.re -> 0 < t.re ->
            chi.LFunction s = 0 -> chi.LFunction t = 0 ->
            s.im = 0 -> t.im = 0 ->
            1 - s.re ≤ c / Real.log N ->
            1 - t.re ≤ c / Real.log N -> s = t) ∧
          (forall s : Complex, 0 < s.re -> chi.LFunction s = 0 ->
            s.im = 0 -> 1 - s.re ≤ c / Real.log N ->
              analyticOrderNatAt chi.LFunction s = 1) := by
  obtain ⟨cComplex, hcComplexPos, hComplex⟩ :=
    exists_imprimitive_complexZero_gap
  obtain ⟨cQuadratic, hcQuadraticPos, hQuadratic⟩ :=
    exists_imprimitive_quadratic_LFunction_exceptionalRegion
  obtain ⟨cReal, hcRealPos, hReal⟩ :=
    exists_nonquadratic_realZero_exclusion
  let c : Real := min cComplex (min cQuadratic cReal)
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min hcComplexPos (lt_min hcQuadraticPos hcRealPos)
  have hcComplex : c ≤ cComplex := by
    dsimp [c]
    exact min_le_left _ _
  have hcQuadratic : c ≤ cQuadratic := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcReal : c ≤ cReal := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN chi hchi
  have hNLower :=
    BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one
      chi hchi
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogNPos : 0 < Real.log N := hLogThree.trans_le hLogNLower
  have hRealQuadratic : c / Real.log N ≤ cQuadratic / Real.log N :=
    (div_le_div_iff_of_pos_right hLogNPos).2 hcQuadratic
  have hRealNonquadratic : c / Real.log N ≤ cReal / Real.log N :=
    (div_le_div_iff_of_pos_right hLogNPos).2 hcReal
  apply And.intro
  · intro s hs hzero hRegular
    have hHeightNonneg : 0 ≤ Real.log (|s.im| + 2) := by
      apply Real.log_nonneg
      linarith [abs_nonneg s.im]
    have hDenominatorPos :
        0 < Real.log N + Real.log (|s.im| + 2) := by
      linarith
    by_cases hSquare : chi ^ 2 = 1
    · have hsNonreal : s.im ≠ 0 := by
        rcases hRegular with hSquareNe | hsNonreal
        · exact (hSquareNe hSquare).elim
        · exact hsNonreal
      have hGap := (hQuadratic chi hchi hSquare).1
        s hs hzero hsNonreal
      have hScale :
          c / (Real.log N + Real.log (|s.im| + 2)) ≤
            cQuadratic / (Real.log N + Real.log (|s.im| + 2)) :=
        (div_le_div_iff_of_pos_right hDenominatorPos).2 hcQuadratic
      exact hScale.trans hGap
    · have hGap := hComplex chi hchi hSquare hs hzero
      have hScale :
          c / (Real.log N + Real.log (|s.im| + 2)) ≤
            cComplex / (Real.log N + Real.log (|s.im| + 2)) :=
        (div_le_div_iff_of_pos_right hDenominatorPos).2 hcComplex
      exact hScale.trans hGap
  · apply And.intro
    · intro s t hs ht hsZero htZero hsReal htReal hsGap htGap
      by_cases hSquare : chi ^ 2 = 1
      · exact (hQuadratic chi hchi hSquare).2.1 s t hs ht
          hsZero htZero hsReal htReal
          (hsGap.trans hRealQuadratic) (htGap.trans hRealQuadratic)
      · have hStrict := hReal chi hchi hSquare hs hsZero hsReal
        have hUpper := hsGap.trans hRealNonquadratic
        exact (not_lt_of_ge hUpper hStrict).elim
    · intro s hs hzero hsReal hsGap
      by_cases hSquare : chi ^ 2 = 1
      · exact (hQuadratic chi hchi hSquare).2.2 s hs hzero hsReal
          (hsGap.trans hRealQuadratic)
      · have hStrict := hReal chi hchi hSquare hs hzero hsReal
        have hUpper := hsGap.trans hRealNonquadratic
        exact (not_lt_of_ge hUpper hStrict).elim

end BombieriVinogradov.SiegelWalfisz
