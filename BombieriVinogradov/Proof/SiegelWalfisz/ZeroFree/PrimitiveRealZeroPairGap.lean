import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.RealPairOptimization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.TwoZeroLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Separation of two real primitive completed zeros

Two distinct divisor indices include the double-zero case.  This module
formalizes the real-pair argument following Strombergsson equation (410) and
bounds the smaller real part away from one.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_realZeroPair_gap :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi ->
            forall (p q : SymmetricCompletedZeroIndex chi), p ≠ q ->
              (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0 ->
              (Complex.Hadamard.divisorZeroIndex₀_val q).im = 0 ->
                c / Real.log N ≤
                  1 - min
                    (Complex.Hadamard.divisorZeroIndex₀_val p).re
                    (Complex.Hadamard.divisorZeroIndex₀_val q).re := by
  obtain ⟨K0, hK0Pos, hTwoZero⟩ := exists_twoZero_logDerivative_bound
  let K := K0 + (Real.log 3)⁻¹
  let c := (15 * K)⁻¹
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hKPos : 0 < K := add_pos hK0Pos (inv_pos.mpr hLogThree)
  have hcPos : 0 < c := inv_pos.mpr (mul_pos (by norm_num) hKPos)
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN hNLower chi hchi hPrimitive p q hpq hpReal hqReal
  let Q := K * Real.log N
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogNPos : 0 < Real.log N := hLogThree.trans_le hLogNLower
  have hQPos : 0 < Q := mul_pos hKPos hLogNPos
  have hInvLogNonneg : 0 ≤ (Real.log 3)⁻¹ := (inv_pos.mpr hLogThree).le
  have hInvLogN : 1 ≤ (Real.log 3)⁻¹ * Real.log N := by
    have hScaled := mul_le_mul_of_nonneg_left hLogNLower hInvLogNonneg
    have hCancel : (Real.log 3)⁻¹ * Real.log 3 = 1 := by field_simp
    rw [hCancel] at hScaled
    exact hScaled
  have hQOne : 1 ≤ Q := by
    have hK0LogNonneg : 0 ≤ K0 * Real.log N :=
      mul_nonneg hK0Pos.le hLogNPos.le
    dsimp [Q, K]
    nlinarith
  have hOrdered : forall (r t : SymmetricCompletedZeroIndex chi), r ≠ t ->
      (Complex.Hadamard.divisorZeroIndex₀_val r).im = 0 ->
      (Complex.Hadamard.divisorZeroIndex₀_val t).im = 0 ->
      (Complex.Hadamard.divisorZeroIndex₀_val r).re ≤
        (Complex.Hadamard.divisorZeroIndex₀_val t).re ->
      c / Real.log N ≤
        1 - (Complex.Hadamard.divisorZeroIndex₀_val r).re := by
    intro r t hrt hrReal htReal hrtRe
    have hrStrip :=
      symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
        hchi hPrimitive r
    have htStrip :=
      symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
        hchi hPrimitive t
    have hCore : forall sigma : Real, 1 < sigma -> sigma ≤ 2 ->
        2 * (sigma -
          (Complex.Hadamard.divisorZeroIndex₀_val r).re)⁻¹ ≤
          (sigma - 1)⁻¹ + Q := by
      intro sigma hsigma hsigmaUpper
      have hBound :=
        hTwoZero hNLower hchi hPrimitive r t hrt hsigma hsigmaUpper
      have hrKernel :
          (1 / ((sigma : Complex) -
            Complex.Hadamard.divisorZeroIndex₀_val r)).re =
            (sigma -
              (Complex.Hadamard.divisorZeroIndex₀_val r).re)⁻¹ := by
        simpa [one_div, hrReal] using
          zeroKernel_re_of_same_im
            (s := (sigma : Complex))
            (rho := Complex.Hadamard.divisorZeroIndex₀_val r)
            (by
              simp only [Complex.ofReal_re]
              linarith [hrStrip.2])
            (by simp [hrReal])
      have htKernel :
          (1 / ((sigma : Complex) -
            Complex.Hadamard.divisorZeroIndex₀_val t)).re =
            (sigma -
              (Complex.Hadamard.divisorZeroIndex₀_val t).re)⁻¹ := by
        simpa [one_div, htReal] using
          zeroKernel_re_of_same_im
            (s := (sigma : Complex))
            (rho := Complex.Hadamard.divisorZeroIndex₀_val t)
            (by
              simp only [Complex.ofReal_re]
              linarith [htStrip.2])
            (by simp [htReal])
      rw [hrKernel, htKernel] at hBound
      have hrDistance :
          0 < sigma - (Complex.Hadamard.divisorZeroIndex₀_val r).re := by
        linarith [hrStrip.2]
      have htDistance :
          0 < sigma - (Complex.Hadamard.divisorZeroIndex₀_val t).re := by
        linarith [htStrip.2]
      have hInvOrder :
          (sigma - (Complex.Hadamard.divisorZeroIndex₀_val r).re)⁻¹ ≤
            (sigma - (Complex.Hadamard.divisorZeroIndex₀_val t).re)⁻¹ :=
        (inv_le_inv₀ hrDistance htDistance).2 (by linarith)
      have hCoefficient : K0 * Real.log N ≤ K * Real.log N := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [K]
          exact le_add_of_nonneg_right hInvLogNonneg
        · exact hLogNPos.le
      have hBoundK :
          (sigma - (Complex.Hadamard.divisorZeroIndex₀_val r).re)⁻¹ +
            (sigma - (Complex.Hadamard.divisorZeroIndex₀_val t).re)⁻¹ ≤
          (sigma - 1)⁻¹ + Q :=
        hBound.trans (by
          simpa [Q, add_comm] using
            add_le_add_left hCoefficient (sigma - 1)⁻¹)
      nlinarith
    have hGap := realPair_core_inequality_implies_gap
      hrStrip.2 hQPos hQOne hCore
    have hIdentity : c / Real.log N = (15 * Q)⁻¹ := by
      dsimp [c, Q]
      field_simp
    rw [hIdentity]
    exact hGap
  by_cases hOrder :
      (Complex.Hadamard.divisorZeroIndex₀_val p).re ≤
        (Complex.Hadamard.divisorZeroIndex₀_val q).re
  · simpa [min_eq_left hOrder] using hOrdered p q hpq hpReal hqReal hOrder
  · have hReverse :
        (Complex.Hadamard.divisorZeroIndex₀_val q).re ≤
          (Complex.Hadamard.divisorZeroIndex₀_val p).re := le_of_not_ge hOrder
    simpa [min_eq_right hReverse] using
      hOrdered q p hpq.symm hqReal hpReal hReverse

end BombieriVinogradov.SiegelWalfisz
