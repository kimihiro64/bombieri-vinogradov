import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroStrip
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# ASCII interface for completed zero values

This module exposes the value represented by a multiplicity-aware completed
zero index and its zero and critical-strip properties through ASCII names.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The complex point represented by a completed zero index. -/
def symmetricCompletedZeroValue
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (p : SymmetricCompletedZeroIndex chi) : Complex :=
  p.1.1

/-- Every completed zero index represents an actual zero. -/
theorem symmetricCompletedZeroValue_apply_eq_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (p : SymmetricCompletedZeroIndex chi) :
    symmetricCompletedLFunction chi (symmetricCompletedZeroValue p) = 0 := by
  have hEntire := differentiable_symmetricCompletedLFunction hchi
  by_contra hValue
  have hAnalytic : AnalyticAt Complex (symmetricCompletedLFunction chi)
      (symmetricCompletedZeroValue p) :=
    Differentiable.analyticAt hEntire _
  have hOrderZero :
      analyticOrderAt (symmetricCompletedLFunction chi)
          (symmetricCompletedZeroValue p) = 0 :=
    (hAnalytic.analyticOrderAt_eq_zero).2 hValue
  have hAnalyticOn :
      AnalyticOnNhd Complex (symmetricCompletedLFunction chi)
        (Set.univ : Set Complex) :=
    hEntire.differentiableOn.analyticOnNhd isOpen_univ
  have hMeromorphic :
      MeromorphicOn (symmetricCompletedLFunction chi) (Set.univ : Set Complex) :=
    hAnalyticOn.meromorphicOn
  have hDivisor :=
    hMeromorphic.divisor_apply (Set.mem_univ (symmetricCompletedZeroValue p))
  rw [hAnalytic.meromorphicOrderAt_eq, hOrderZero] at hDivisor
  simp at hDivisor
  have hEmpty : Fin 0 := by
    have hp := p.1.2
    change Fin (Int.toNat
      (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
        (Set.univ : Set Complex) (symmetricCompletedZeroValue p))) at hp
    rw [hDivisor] at hp
    simpa using hp
  exact Fin.elim0 hEmpty

/-- Every completed zero value lies strictly inside the critical strip. -/
theorem symmetricCompletedZeroValue_re_mem_Ioo
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : SymmetricCompletedZeroIndex chi) :
    Set.Ioo 0 1 (symmetricCompletedZeroValue p).re := by
  let rho : Complex := symmetricCompletedZeroValue p
  have hZero : symmetricCompletedLFunction chi rho = 0 :=
    symmetricCompletedZeroValue_apply_eq_zero hchi p
  have hUpper : rho.re < 1 := by
    by_contra hNot
    exact symmetricCompletedLFunction_ne_zero_of_one_le_re
      hchi (le_of_not_gt hNot) hZero
  have hLower : 0 < rho.re := by
    by_contra hNot
    have hReflectedRe : 1 <=
        (1 - (starRingEnd Complex) rho).re := by
      have hConjRe : ((starRingEnd Complex) rho).re = rho.re := by
        simp
      rw [Complex.sub_re, hConjRe]
      norm_num
      linarith
    have hReflectedZero :
        symmetricCompletedLFunction chi
            (1 - (starRingEnd Complex) rho) = 0 := by
      rw [symmetricCompletedLFunction_one_sub_conj hchi hPrimitive,
        hZero, map_zero, mul_zero]
    exact symmetricCompletedLFunction_ne_zero_of_one_le_re
      hchi hReflectedRe hReflectedZero
  exact Set.mem_Ioo.mpr (And.intro hLower hUpper)

end BombieriVinogradov.SiegelWalfisz
