import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroNormInvSqSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Canonical logarithmic-derivative zero-term summability

This module derives genus-one canonical-term summability through the ASCII
completed-zero interface. Squared inverse-norm convergence forces zero norms
to grow, and the standard canonical-term identity supplies the tail bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem summable_completedZero_canonicalTerm
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {z : Complex}
    (hz : forall p : SymmetricCompletedZeroIndex chi,
      Ne z (symmetricCompletedZeroValue p)) :
    Summable (fun p : SymmetricCompletedZeroIndex chi =>
      1 / (z - symmetricCompletedZeroValue p) +
        1 / symmetricCompletedZeroValue p) := by
  let R : Real := max (norm z) 1
  have hRPos : 0 < R :=
    lt_of_lt_of_le (by norm_num) (le_max_right (norm z) 1)
  have hzNormLe : norm z <= R := le_max_left (norm z) 1
  have hInvSq := summable_completedZero_norm_inv_sq hchi hPrimitive
  let majorant : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    (2 * R) * (1 / norm (symmetricCompletedZeroValue p)) ^ 2
  have hMajorant : Summable majorant := by
    simpa [majorant] using hInvSq.mul_left (2 * R)
  refine hMajorant.of_norm_bounded_eventually ?_
  have hTwoRPos : 0 < 2 * R := by nlinarith
  have hInvTwoRPos : 0 < 1 / (2 * R) :=
    div_pos (by norm_num) hTwoRPos
  have hThresholdPos : 0 < (1 / (2 * R)) ^ 2 := by
    rw [pow_two]
    exact mul_pos hInvTwoRPos hInvTwoRPos
  have hSmall :
      Filter.Eventually
        (fun p : SymmetricCompletedZeroIndex chi =>
          (1 / norm (symmetricCompletedZeroValue p)) ^ 2 <
            (1 / (2 * R)) ^ 2)
        Filter.cofinite :=
    hInvSq.tendsto_cofinite_zero.eventually_lt_const hThresholdPos
  have hBig :
      Filter.Eventually
        (fun p : SymmetricCompletedZeroIndex chi =>
          2 * R < norm (symmetricCompletedZeroValue p))
        Filter.cofinite := by
    refine hSmall.mono ?_
    intro p hp
    let rho : Complex := symmetricCompletedZeroValue p
    have hStrip : Set.Ioo 0 1 rho.re := by
      simpa [rho] using
        symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p
    have hRhoNe : Ne rho 0 := by
      intro hRhoZero
      have hRhoRePos := hStrip.1
      rw [hRhoZero] at hRhoRePos
      norm_num at hRhoRePos
    have hRhoNormPos : 0 < norm rho := norm_pos_iff.mpr hRhoNe
    by_contra hNot
    have hNormLe : norm rho <= 2 * R := le_of_not_gt hNot
    have hInvLower : 1 / (2 * R) <= 1 / norm rho :=
      one_div_le_one_div_of_le hRhoNormPos hNormLe
    have hSquareLower :
        (1 / (2 * R)) ^ 2 <= (1 / norm rho) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self hInvTwoRPos.le hInvLower
    have hpAscii :
        (1 / norm rho) ^ 2 < (1 / (2 * R)) ^ 2 := by
      simpa [rho] using hp
    exact (not_le_of_gt hpAscii) hSquareLower
  refine hBig.mono ?_
  intro p hp
  let rho : Complex := symmetricCompletedZeroValue p
  have hStrip : Set.Ioo 0 1 rho.re := by
    simpa [rho] using
      symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p
  have hRhoNe : Ne rho 0 := by
    intro hRhoZero
    have hRhoRePos := hStrip.1
    rw [hRhoZero] at hRhoRePos
    norm_num at hRhoRePos
  have hzRho : Ne z rho := by
    simpa [rho] using hz p
  have hzSubNe : Ne (z - rho) 0 := sub_ne_zero.mpr hzRho
  have hTerm :
      1 / (z - rho) + 1 / rho = z / (rho * (z - rho)) := by
    field_simp [hRhoNe, hzSubNe]
    ring
  have hTriangle : norm rho <= norm z + norm (z - rho) := by
    have hRhoIdentity : z - (z - rho) = rho := by ring
    calc
      norm rho = norm (z - (z - rho)) :=
        congrArg norm (Eq.symm hRhoIdentity)
      _ <= norm z + norm (z - rho) := norm_sub_le z (z - rho)
  have hzSubLower : norm rho / 2 <= norm (z - rho) := by
    nlinarith
  have hRhoNormPos : 0 < norm rho := norm_pos_iff.mpr hRhoNe
  have hzSubNormPos : 0 < norm (z - rho) :=
    norm_pos_iff.mpr hzSubNe
  have hBasePos : 0 < norm rho * (norm rho / 2) :=
    mul_pos hRhoNormPos (div_pos hRhoNormPos (by norm_num))
  have hDenLower :
      norm rho * (norm rho / 2) <=
        norm rho * norm (z - rho) :=
    mul_le_mul_of_nonneg_left hzSubLower hRhoNormPos.le
  have hNorm :
      norm (1 / (z - rho) + 1 / rho) <=
        (2 * R) * (1 / norm rho) ^ 2 := by
    rw [hTerm, Complex.norm_div, Complex.norm_mul]
    calc
      norm z / (norm rho * norm (z - rho)) <=
          norm z / (norm rho * (norm rho / 2)) :=
        div_le_div_of_nonneg_left (norm_nonneg z) hBasePos hDenLower
      _ <= R / (norm rho * (norm rho / 2)) :=
        div_le_div_of_nonneg_right hzNormLe hBasePos.le
      _ = (2 * R) * (1 / norm rho) ^ 2 := by
        field_simp [hRhoNormPos.ne']
  simpa [majorant, rho] using hNorm

end BombieriVinogradov.SiegelWalfisz

