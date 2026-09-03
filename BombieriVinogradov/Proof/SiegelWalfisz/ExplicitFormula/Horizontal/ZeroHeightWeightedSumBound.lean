import BombieriVinogradov.Helpers.ComplexAnalysis.ReciprocalVerticalKernel
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeRightHalfPlaneBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.SelectableZeroLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernelSummability
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Weighted count of zeros near a height

This module proves the source quadratic vertical-weight estimate for all
multiplicity-indexed zeros of a primitive nonprincipal Dirichlet L-function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The sum of quadratic vertical-gap weights over all nontrivial zeros is
bounded by one absolute constant times the modulus-height logarithm. -/
theorem exists_tsum_zero_vertical_weight_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall T : Real,
              (tsum fun p : SymmetricCompletedZeroIndex chi =>
                1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)) <=
                C * (Real.log N + Real.log (abs T + 2))) := by
  choose A hAPos hSelectable using
    exists_primitive_selectableZero_logDeriv_bound
  let Z : Real :=
    norm (-deriv riemannZeta (((2 : Real) : Complex)) /
      riemannZeta (((2 : Real) : Complex)))
  let D : Real := Real.log 3
  let C : Real := 4 * (A + Z / D)
  have hDPos : 0 < D := by
    dsimp [D]
    exact Real.log_pos (by norm_num)
  have hZNonneg : 0 <= Z := by
    dsimp [Z]
    exact norm_nonneg _
  have hZDivNonneg : 0 <= Z / D :=
    div_nonneg hZNonneg hDPos.le
  have hCPos : 0 < C := by
    dsimp [C]
    nlinarith
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T
  let s : Complex := ((2 : Real) : Complex) +
    (T : Complex) * Complex.I
  let L : Real := Real.log N + Real.log (abs T + 2)
  have hsRe : s.re = 2 := by
    simp [s, Complex.mul_re]
  have hsIm : s.im = T := by
    simp [s, Complex.mul_im]
  have hsRight : 1 < s.re := by
    rw [hsRe]
    norm_num
  have hsUpper : s.re <= 2 := hsRe.le
  have hSelectableAt :=
    hSelectable hN hchi hPrimitive hsRight hsUpper
      (Set.univ : Set (SymmetricCompletedZeroIndex chi))
  have hSelectableFull :
      -(logDeriv chi.LFunction s).re <=
        -(tsum fun p : SymmetricCompletedZeroIndex chi =>
          (1 / (s - symmetricCompletedZeroValue p)).re) +
          A * L := by
    have hSelectableAscii :
        -(logDeriv chi.LFunction s).re <=
          -(tsum fun p :
              (Set.univ : Set (SymmetricCompletedZeroIndex chi)) =>
            (1 / (s - symmetricCompletedZeroValue p.1)).re) +
            A * L := by
      simpa [symmetricCompletedZeroValue, L, hsIm] using hSelectableAt
    have hUnivKernel :
        (tsum fun p :
            (Set.univ : Set (SymmetricCompletedZeroIndex chi)) =>
          (1 / (s - symmetricCompletedZeroValue p.1)).re) =
          tsum fun p : SymmetricCompletedZeroIndex chi =>
            (1 / (s - symmetricCompletedZeroValue p)).re := by
      simpa using
        (tsum_subtype
          (Set.univ : Set (SymmetricCompletedZeroIndex chi))
          (fun p : SymmetricCompletedZeroIndex chi =>
            (1 / (s - symmetricCompletedZeroValue p)).re))
    rw [hUnivKernel] at hSelectableAscii
    exact hSelectableAscii
  have hRight :=
    norm_neg_logDeriv_LFunction_le_zeta_re chi hsRight
  have hLogNorm : norm (logDeriv chi.LFunction s) <= Z := by
    rw [logDeriv_apply]
    rw [hsRe] at hRight
    simpa [Z] using hRight
  have hLogRe : (logDeriv chi.LFunction s).re <= Z :=
    (Complex.re_le_norm _).trans hLogNorm
  have hKernelSummable :
      Summable (fun p : SymmetricCompletedZeroIndex chi =>
        (1 / (s - symmetricCompletedZeroValue p)).re) := by
    simpa [symmetricCompletedZeroValue] using
      summable_symmetricCompletedLFunction_zeroKernel_re
        hchi hPrimitive hsRight
  have hWeightNonneg : forall p : SymmetricCompletedZeroIndex chi,
      0 <= 1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2) := by
    intro p
    exact div_nonneg (by norm_num)
      (by nlinarith [sq_nonneg (T - (symmetricCompletedZeroValue p).im)])
  have hWeightPointwise : forall p : SymmetricCompletedZeroIndex chi,
      1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2) <=
        4 * (1 / (s - symmetricCompletedZeroValue p)).re := by
    intro p
    have hStrip : Set.Ioo 0 1 (symmetricCompletedZeroValue p).re :=
      symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p
    have hKernel :=
      BombieriVinogradov.ComplexAnalysis.one_div_vertical_gap_sq_le_zeroKernel_re
        (T := T) hStrip.1 hStrip.2
    rw [show s = ((2 : Real) : Complex) +
        (T : Complex) * Complex.I by rfl]
    calc
      1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2) =
        4 * (1 / (4 *
          (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2))) := by
          field_simp
      _ <= 4 * (1 /
          (((2 : Real) : Complex) + (T : Complex) * Complex.I -
            symmetricCompletedZeroValue p)).re :=
        mul_le_mul_of_nonneg_left hKernel (by norm_num)
  have hScaledKernelSummable :
      Summable (fun p : SymmetricCompletedZeroIndex chi =>
        4 * (1 / (s - symmetricCompletedZeroValue p)).re) :=
    hKernelSummable.mul_left 4
  have hWeightSummable :
      Summable (fun p : SymmetricCompletedZeroIndex chi =>
        1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)) :=
    Summable.of_nonneg_of_le hWeightNonneg hWeightPointwise
      hScaledKernelSummable
  have hWeightLeKernel :
      (tsum fun p : SymmetricCompletedZeroIndex chi =>
        1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)) <=
        4 * (tsum fun p : SymmetricCompletedZeroIndex chi =>
          (1 / (s - symmetricCompletedZeroValue p)).re) := by
    calc
      (tsum fun p : SymmetricCompletedZeroIndex chi =>
          1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)) <=
        tsum (fun p : SymmetricCompletedZeroIndex chi =>
          4 * (1 / (s - symmetricCompletedZeroValue p)).re) :=
        hWeightSummable.tsum_le_tsum hWeightPointwise
          hScaledKernelSummable
      _ = 4 * (tsum fun p : SymmetricCompletedZeroIndex chi =>
          (1 / (s - symmetricCompletedZeroValue p)).re) :=
        hKernelSummable.tsum_mul_left 4
  have hKernelUpper :
      (tsum fun p : SymmetricCompletedZeroIndex chi =>
        (1 / (s - symmetricCompletedZeroValue p)).re) <=
        Z + A * L := by
    linarith
  have hRaw :
      (tsum fun p : SymmetricCompletedZeroIndex chi =>
        1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)) <=
        4 * (Z + A * L) :=
    hWeightLeKernel.trans
      (mul_le_mul_of_nonneg_left hKernelUpper (by norm_num))
  have hLogNLower : Real.log 3 <= Real.log N := by
    apply Real.log_le_log (by norm_num)
    exact Nat.cast_le.mpr hN
  have hLogHeightNonneg : 0 <= Real.log (abs T + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg T])
  have hDLeL : D <= L := by
    dsimp [D, L]
    linarith
  have hZAbsorb : Z <= (Z / D) * L := by
    calc
      Z = (Z / D) * D := by
        field_simp [ne_of_gt hDPos]
      _ <= (Z / D) * L :=
        mul_le_mul_of_nonneg_left hDLeL hZDivNonneg
  calc
    (tsum fun p : SymmetricCompletedZeroIndex chi =>
        1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)) <=
      4 * (Z + A * L) := hRaw
    _ <= 4 * ((Z / D) * L + A * L) := by
      nlinarith
    _ = C * (Real.log N + Real.log (abs T + 2)) := by
      dsimp [C, L]
      ring

end BombieriVinogradov.SiegelWalfisz
