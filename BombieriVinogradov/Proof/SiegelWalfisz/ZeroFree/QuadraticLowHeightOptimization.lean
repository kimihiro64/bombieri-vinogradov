import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Low-height optimization for a nonreal quadratic zero

This pure real argument formalizes the optimization following Strombergsson
equation (410).  A sufficiently low positive imaginary part forces the same
reciprocal-logarithmic horizontal gap as the source proof.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem nonreal_core_inequality_implies_lowHeight_gap
    {beta gamma Q : Real} (hbeta : beta < 1) (hgamma : 0 < gamma)
    (hQ : 0 < Q) (hQOne : 1 ≤ Q)
    (hgammaSmall : gamma < (10 * Q)⁻¹)
    (hcore : forall sigma : Real, 1 < sigma -> sigma ≤ 2 ->
      2 * (sigma - beta) /
          ((sigma - beta) ^ 2 + gamma ^ 2) ≤
        (sigma - 1)⁻¹ + Q) :
    (15 * Q)⁻¹ ≤ 1 - beta := by
  let d := 1 - beta
  let x := (5 * Q)⁻¹
  let a := x + d
  have hdPos : 0 < d := sub_pos.mpr hbeta
  have hFiveQPos : 0 < 5 * Q := mul_pos (by norm_num) hQ
  have hxPos : 0 < x := inv_pos.mpr hFiveQPos
  have hFiveLe : (5 : Real) ≤ 5 * Q := by nlinarith
  have hxLe : x ≤ (5 : Real)⁻¹ :=
    (inv_le_inv₀ hFiveQPos (by norm_num)).2 hFiveLe
  have hcoreAt := hcore (1 + x) (by linarith) (by linarith)
  have hxInv : x⁻¹ = 5 * Q := by
    dsimp [x]
    rw [inv_inv]
  have hSigmaBeta : 1 + x - beta = a := by
    dsimp [a, d]
    ring
  have hSigmaOne : 1 + x - 1 = x := by ring
  rw [hSigmaBeta, hSigmaOne, hxInv] at hcoreAt
  have hCoreNormalized :
      2 * a / (a ^ 2 + gamma ^ 2) ≤ 6 * Q := by
    linarith
  have haPos : 0 < a := by dsimp [a]; linarith
  have hGammaScale : (10 * Q)⁻¹ = x / 2 := by
    dsimp [x]
    field_simp
    ring
  have hgammaHalfX : gamma < x / 2 := by
    rw [← hGammaScale]
    exact hgammaSmall
  have hgammaHalfA : gamma < a / 2 := by
    dsimp [a]
    linarith
  have hDifferencePos : 0 < a / 2 - gamma := by linarith
  have hSumPos : 0 < a / 2 + gamma := by linarith
  have hGammaSq : gamma ^ 2 < (a / 2) ^ 2 := by
    have hProduct := mul_pos hDifferencePos hSumPos
    nlinarith
  have hDenominatorPos : 0 < a ^ 2 + gamma ^ 2 := by
    nlinarith [sq_nonneg gamma]
  have hKernelLower :
      8 / (5 * a) < 2 * a / (a ^ 2 + gamma ^ 2) := by
    apply (div_lt_div_iff₀ (mul_pos (by norm_num) haPos)
      hDenominatorPos).2
    nlinarith
  by_contra hGap
  have hdUpper : d < (15 * Q)⁻¹ := lt_of_not_ge hGap
  have hGapScale : (15 * Q)⁻¹ = x / 3 := by
    dsimp [x]
    field_simp
    ring
  rw [hGapScale] at hdUpper
  have haUpper : a < 4 * x / 3 := by
    dsimp [a]
    linarith
  have hQx : Q * x = 1 / 5 := by
    dsimp [x]
    field_simp
  have hSixLower : 6 * Q < 8 / (5 * a) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) haPos)).2
    nlinarith
  exact (not_lt_of_ge hCoreNormalized) (hSixLower.trans hKernelLower)

end BombieriVinogradov.SiegelWalfisz
