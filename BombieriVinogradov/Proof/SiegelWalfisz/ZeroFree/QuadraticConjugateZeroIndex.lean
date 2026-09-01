import BombieriVinogradov.Helpers.ComplexAnalysis.DivisorZeroIndex
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedConjugation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedOriginNonvanishing
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroDivisorValues

/-!
# Conjugate divisor index for a primitive quadratic character

For a quadratic character the inverse character is the original character,
so complex conjugation carries every completed-function zero to another zero
of the same completed function, with multiplicity-aware index data.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_quadratic_conjugateZeroIndex
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hchiSquare : chi ^ 2 = 1) (p : SymmetricCompletedZeroIndex chi) :
    exists q : SymmetricCompletedZeroIndex chi,
      Complex.Hadamard.divisorZeroIndex₀_val q =
        (starRingEnd Complex) (Complex.Hadamard.divisorZeroIndex₀_val p) := by
  let rho := Complex.Hadamard.divisorZeroIndex₀_val p
  have hZero :=
    symmetricCompletedLFunction_divisorZeroIndex₀_apply_eq_zero
      hchi hPrimitive p
  have hInverse :=
    BombieriVinogradov.DirichletCharacter.inv_eq_self_of_sq_eq_one
      chi hchiSquare
  have hConjugate := symmetricCompletedLFunction_inv_eq_conj_conj
    hchi ((starRingEnd Complex) rho)
  rw [hInverse, Complex.conj_conj, hZero, map_zero] at hConjugate
  have hConjugateNe : (starRingEnd Complex) rho ≠ 0 := by
    intro hzero
    apply p.property
    have hback := congrArg (starRingEnd Complex) hzero
    change rho = 0
    simpa only [map_zero, Complex.conj_conj] using hback
  have hEntire := differentiable_symmetricCompletedLFunction hchi
  have hNonzero : exists w : Complex, symmetricCompletedLFunction chi w ≠ 0 :=
    Exists.intro 0
      (symmetricCompletedLFunction_zero_ne_zero hchi hPrimitive)
  exact BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
    hEntire hNonzero hConjugateNe hConjugate

end BombieriVinogradov.SiegelWalfisz
