import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardFactorization
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order

/-!
# Zero summability for a completed Dirichlet L-function

This module specializes finite-order Hadamard summability to the multiplicity-aware
nonzero-zero divisor of a primitive symmetric completed Dirichlet L-function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem summable_symmetricCompletedLFunction_divisorZeroIndex₀_norm_inv_sq
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀
          (symmetricCompletedLFunction chi) (Set.univ : Set Complex) =>
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : Nat)) := by
  simpa using
    (Complex.Hadamard.EntireOfOrderAtMost.summable_norm_inv_pow_divisorZeroIndex₀
      (ρ := (1 : Real))
      (symmetricCompletedLFunction_entireOfOrderAtMost_one hchi hPrimitive)
      (by norm_num)
      (Exists.intro 2 (symmetricCompletedLFunction_two_ne_zero hchi)))

end BombieriVinogradov.SiegelWalfisz
