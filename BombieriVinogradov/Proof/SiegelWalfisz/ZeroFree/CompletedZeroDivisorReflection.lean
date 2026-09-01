import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedDivisorEndpoints
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroMultiplicitySymmetry
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber

/-!
# Reflection involution on the completed-function zero divisor

This module lifts `rho` mapping to `1 - conj rho` from equality of analytic zero
orders to an equivalence of the multiplicity-aware nonzero-zero divisor indices.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_divisorMultiplicity_one_sub_conj
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (rho : Complex) :
    Int.toNat
        (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
          (Set.univ : Set Complex) (1 - (starRingEnd Complex) rho)) =
      Int.toNat
        (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
          (Set.univ : Set Complex) rho) := by
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (differentiable_symmetricCompletedLFunction hchi),
    Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (differentiable_symmetricCompletedLFunction hchi)]
  simp only [Int.toNat_natCast]
  exact analyticOrderNatAt_symmetricCompletedLFunction_one_sub_conj
    hchi hPrimitive rho

noncomputable def symmetricCompletedZeroReflection
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    SymmetricCompletedZeroIndex chi -> SymmetricCompletedZeroIndex chi :=
  fun p =>
    let rho := Complex.Hadamard.divisorZeroIndex₀_val p
    have hCount :
        Int.toNat
            (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
              (Set.univ : Set Complex) (1 - (starRingEnd Complex) rho)) =
          Int.toNat
            (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
              (Set.univ : Set Complex) rho) :=
      symmetricCompletedLFunction_divisorMultiplicity_one_sub_conj
        hchi hPrimitive rho
    have hOne : (1 : Complex) ≠ rho :=
      symmetricCompletedLFunction_one_ne_divisorZeroIndex₀_val
        hchi hPrimitive p
    have hNonzero : 1 - (starRingEnd Complex) rho ≠ 0 := by
      intro hZero
      have hReflected := congrArg (starRingEnd Complex) hZero
      have hOneEq : (1 : Complex) = rho := by
        have : (1 : Complex) - rho = 0 := by
          simpa only [map_sub, map_one, map_zero, Complex.conj_conj] using hReflected
        exact sub_eq_zero.mp this
      exact hOne hOneEq
    Subtype.mk
      (Sigma.mk (1 - (starRingEnd Complex) rho)
        (Fin.cast hCount.symm p.1.2))
      hNonzero

@[simp]
theorem symmetricCompletedZeroReflection_val
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : SymmetricCompletedZeroIndex chi) :
    Complex.Hadamard.divisorZeroIndex₀_val
        (symmetricCompletedZeroReflection hchi hPrimitive p) =
      1 - (starRingEnd Complex)
        (Complex.Hadamard.divisorZeroIndex₀_val p) := by
  rfl

theorem symmetricCompletedZeroReflection_involutive
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    Function.Involutive (symmetricCompletedZeroReflection hchi hPrimitive) := by
  intro p
  have hVal :
      Complex.Hadamard.divisorZeroIndex₀_val
          (symmetricCompletedZeroReflection hchi hPrimitive
            (symmetricCompletedZeroReflection hchi hPrimitive p)) =
        Complex.Hadamard.divisorZeroIndex₀_val p := by
    rw [symmetricCompletedZeroReflection_val,
      symmetricCompletedZeroReflection_val]
    simp only [map_sub, map_one, Complex.conj_conj]
    ring
  have hBounds := congrArg
    (fun z : Complex =>
      Int.toNat
        (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
          (Set.univ : Set Complex) z)) hVal
  apply Subtype.ext
  apply Sigma.ext hVal
  exact (Fin.heq_ext_iff hBounds).2 rfl

noncomputable def symmetricCompletedZeroReflectionEquiv
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    SymmetricCompletedZeroIndex chi ≃ SymmetricCompletedZeroIndex chi :=
  Equiv.ofBijective
    (symmetricCompletedZeroReflection hchi hPrimitive)
    (And.intro
      (symmetricCompletedZeroReflection_involutive hchi hPrimitive).injective
      (symmetricCompletedZeroReflection_involutive hchi hPrimitive).surjective)

@[simp]
theorem symmetricCompletedZeroReflectionEquiv_val
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : SymmetricCompletedZeroIndex chi) :
    Complex.Hadamard.divisorZeroIndex₀_val
        (symmetricCompletedZeroReflectionEquiv hchi hPrimitive p) =
      1 - (starRingEnd Complex)
        (Complex.Hadamard.divisorZeroIndex₀_val p) := by
  exact symmetricCompletedZeroReflection_val hchi hPrimitive p

end BombieriVinogradov.SiegelWalfisz
