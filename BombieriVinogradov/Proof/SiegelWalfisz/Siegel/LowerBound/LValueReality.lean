import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.LFunctionBlockEquality
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Values

/-!
# Reality of quadratic L-functions near one

This module proves that a quadratic character's analytically continued
L-function is real on the real slice of the fixed Siegel analytic domain.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem real_mem_siegelAnalyticDomain {s : ℝ} (hsLower : 7 / 8 ≤ s)
    (hsUpper : s ≤ 1) : (s : ℂ) ∈ siegelAnalyticDomain := by
  rw [siegelAnalyticDomain, Metric.mem_ball, Complex.dist_eq]
  have hnonpos : s - 2 ≤ 0 := by linarith
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos hnonpos]
  norm_num at hsLower ⊢
  linarith

private theorem characterLBlock_im_eq_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    (k : ℕ) (s : ℝ) : (characterLBlock chi k s).im = 0 := by
  rw [characterLBlock, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hchiSquare j with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp

theorem quadraticLFunction_im_eq_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hs : (s : ℂ) ∈ siegelAnalyticDomain) :
    (chi.LFunction s).im = 0 := by
  have hsum : Summable (fun k : ℕ ↦ characterLBlock chi k s) := by
    apply Summable.of_norm
    exact (characterLBlockMajorant_summable N).of_nonneg_of_le
      (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs
  rw [LFunction_eq_characterLBlockSeries chi hchi hs, characterLBlockSeries,
    Complex.im_tsum hsum]
  convert tsum_zero with k
  exact characterLBlock_im_eq_zero chi hchiSquare k s

end BombieriVinogradov.SiegelWalfisz
