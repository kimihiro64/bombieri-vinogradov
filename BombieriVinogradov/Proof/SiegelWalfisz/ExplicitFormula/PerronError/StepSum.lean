import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.StepWeight

/-!
# Perron step series

This module proves that the infinite scalar step series has finite support and
equals the half-weighted character Chebyshev sum.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

/-- The scalar Perron step sequence has finite support. -/
theorem summable_scalarPerronStepTerm
    {N x : Nat} (chi : DirichletCharacter Complex N) :
    Summable (scalarPerronStepTerm chi x) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 x)
  intro n hnMem
  by_cases hnZero : n = 0
  case pos =>
    simp [scalarPerronStepTerm, hnZero]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hOne : 1 <= n := hnPos
    have hNotLe : Not (n <= x) := by
      intro hnx
      exact hnMem (by simp [hOne, hnx])
    exact scalarPerronStepTerm_eq_zero_of_lt chi hnPos
      (Nat.lt_of_not_ge hNotLe)

/-- Summing the scalar Perron step terms gives the half-weighted character
Chebyshev sum. -/
theorem tsum_scalarPerronStepTerm_eq_characterChebyshevHalfSum
    {N x : Nat} (chi : DirichletCharacter Complex N) (hx : 0 < x) :
    tsum (scalarPerronStepTerm chi x) = characterChebyshevHalfSum x chi := by
  have hTail : forall n : Nat, Not (Membership.mem (Finset.Icc 1 x) n) ->
      scalarPerronStepTerm chi x n = 0 := by
    intro n hnMem
    by_cases hnZero : n = 0
    case pos =>
      simp [scalarPerronStepTerm, hnZero]
    case neg =>
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      have hOne : 1 <= n := hnPos
      have hNotLe : Not (n <= x) := by
        intro hnx
        exact hnMem (by simp [hOne, hnx])
      exact scalarPerronStepTerm_eq_zero_of_lt chi hnPos
        (Nat.lt_of_not_ge hNotLe)
  rw [tsum_eq_sum hTail]
  have hInterior :
      Finset.sum (Finset.Ico 1 x) (scalarPerronStepTerm chi x) =
        Finset.sum (Finset.Ico 1 x) (twistedMangoldtSequence chi) := by
    apply Finset.sum_congr rfl
    intro n hnMem
    have hnBounds := Finset.mem_Ico.mp hnMem
    exact scalarPerronStepTerm_eq_coeff_of_lt chi
      (lt_of_lt_of_le zero_lt_one hnBounds.1) hnBounds.2
  have hxMem : Membership.mem (Finset.Icc 1 x) x :=
    Finset.mem_Icc.mpr (And.intro hx (le_refl x))
  have hDecomp := Finset.sum_erase_add (Finset.Icc 1 x)
    (scalarPerronStepTerm chi x) hxMem
  rw [Finset.Icc_erase_right] at hDecomp
  rw [<- hDecomp]
  rw [scalarPerronStepTerm_eq_half chi hx]
  unfold characterChebyshevHalfSum
  rw [hInterior]

end BombieriVinogradov.SiegelWalfisz
