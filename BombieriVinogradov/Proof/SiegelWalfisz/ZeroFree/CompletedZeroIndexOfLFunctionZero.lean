import BombieriVinogradov.Helpers.ComplexAnalysis.DivisorZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedOriginNonvanishing
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductFormula
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex

/-!
# Packaging an ordinary L-function zero as a completed divisor index

In the positive half-plane the gamma and normalization factors do not vanish,
so an ordinary L-function zero is a zero of the symmetric completed function
at exactly the same complex point.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_completedZeroIndex_of_LFunction_eq_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex} (hs : 0 < s.re)
    (hzero : chi.LFunction s = 0) :
    exists p : SymmetricCompletedZeroIndex chi,
      Complex.Hadamard.divisorZeroIndex₀_val p = s := by
  have hCompleted :=
    DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
      chi hs
  rw [hzero, zero_mul] at hCompleted
  have hSymmetric : symmetricCompletedLFunction chi s = 0 := by
    rw [symmetricCompletedLFunction, hCompleted, mul_zero]
  have hsNe : s ≠ 0 := by
    intro hsZero
    rw [hsZero] at hs
    norm_num at hs
  have hEntire := differentiable_symmetricCompletedLFunction hchi
  have hNonzero : exists w : Complex,
      symmetricCompletedLFunction chi w ≠ 0 :=
    Exists.intro 0
      (symmetricCompletedLFunction_zero_ne_zero hchi hPrimitive)
  exact BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
    hEntire hNonzero hsNe hSymmetric

end BombieriVinogradov.SiegelWalfisz
