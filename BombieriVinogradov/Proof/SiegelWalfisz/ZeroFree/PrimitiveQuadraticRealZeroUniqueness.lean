import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveRealZeroPairGap

/-!
# Uniqueness of a primitive quadratic real exceptional index

Shrinking the real-pair separation constant by a factor of two shows that two
real multiplicity indices cannot both lie in the exceptional region.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_quadratic_realZero_unique :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi ->
            forall (p q : SymmetricCompletedZeroIndex chi),
              (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0 ->
              (Complex.Hadamard.divisorZeroIndex₀_val q).im = 0 ->
              1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re ≤
                c / Real.log N ->
              1 - (Complex.Hadamard.divisorZeroIndex₀_val q).re ≤
                c / Real.log N ->
                p = q := by
  obtain ⟨cPair, hPairPos, hPair⟩ := exists_primitive_realZeroPair_gap
  let c : Real := cPair / 2
  have hcPos : 0 < c := div_pos hPairPos (by norm_num)
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN hNLower chi hchi hPrimitive p q hpReal hqReal hpGap hqGap
  by_contra hpq
  have hPairGap := hPair hNLower hchi hPrimitive p q hpq hpReal hqReal
  have hRegion :
      1 - min
          (Complex.Hadamard.divisorZeroIndex₀_val p).re
          (Complex.Hadamard.divisorZeroIndex₀_val q).re ≤
        c / Real.log N := by
    by_cases hOrder :
        (Complex.Hadamard.divisorZeroIndex₀_val p).re ≤
          (Complex.Hadamard.divisorZeroIndex₀_val q).re
    · simpa [min_eq_left hOrder] using hpGap
    · have hReverse :
          (Complex.Hadamard.divisorZeroIndex₀_val q).re ≤
            (Complex.Hadamard.divisorZeroIndex₀_val p).re :=
        le_of_not_ge hOrder
      simpa [min_eq_right hReverse] using hqGap
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogNPos : 0 < Real.log N := hLogThree.trans_le hLogNLower
  have hStrict : c / Real.log N < cPair / Real.log N :=
    (div_lt_div_iff_of_pos_right hLogNPos).2 (by
      dsimp [c]
      linarith)
  linarith

end BombieriVinogradov.SiegelWalfisz
