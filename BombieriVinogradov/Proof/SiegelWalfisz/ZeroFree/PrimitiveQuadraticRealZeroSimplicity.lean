import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveQuadraticRealZeroUniqueness
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber

/-!
# Simplicity of a primitive quadratic real exceptional zero

Uniqueness at the multiplicity-index level forces the entire divisor fiber at
an exceptional real zero to be a singleton, hence its analytic order is one.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_quadratic_realZero_simple :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi ->
            forall p : SymmetricCompletedZeroIndex chi,
              (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0 ->
              1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re ≤
                c / Real.log N ->
                analyticOrderNatAt (symmetricCompletedLFunction chi)
                  (Complex.Hadamard.divisorZeroIndex₀_val p) = 1 := by
  obtain ⟨c, hcPos, hUnique⟩ :=
    exists_primitive_quadratic_realZero_unique
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN hNLower chi hchi hPrimitive p hpReal hpGap
  let z : Complex := Complex.Hadamard.divisorZeroIndex₀_val p
  let fiber :=
    Complex.Hadamard.divisorZeroIndex₀_fiberFinset
      (f := symmetricCompletedLFunction chi) z
  have hpMem : p ∈ fiber := by
    exact (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
      (f := symmetricCompletedLFunction chi) (z₀ := z) p).2 rfl
  have hFiber : fiber = {p} := by
    ext q
    constructor
    · intro hq
      have hqVal :=
        (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
          (f := symmetricCompletedLFunction chi) (z₀ := z) q).1 hq
      have hqReal :
          (Complex.Hadamard.divisorZeroIndex₀_val q).im = 0 := by
        rw [hqVal]
        simpa [z] using hpReal
      have hqGap :
          1 - (Complex.Hadamard.divisorZeroIndex₀_val q).re ≤
            c / Real.log N := by
        rw [hqVal]
        simpa [z] using hpGap
      exact Finset.mem_singleton.mpr
        (hUnique hNLower hchi hPrimitive p q hpReal hqReal hpGap hqGap).symm
    · intro hq
      have hqp : q = p := Finset.mem_singleton.mp hq
      subst q
      exact hpMem
  have hCard :=
    Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
      (hf := differentiable_symmetricCompletedLFunction hchi)
      (z₀ := z) (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p)
  change fiber.card =
    analyticOrderNatAt (symmetricCompletedLFunction chi) z at hCard
  rw [hFiber] at hCard
  simpa [z] using hCard.symm

end BombieriVinogradov.SiegelWalfisz
