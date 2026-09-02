import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.RiemannXiDivisorStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernel
import Mathlib.Topology.Algebra.InfiniteSum.Module
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# Positivity of the Riemann-xi logarithmic-derivative zero sum

This module proves that each genus-one xi zero term has nonnegative real part
to the right of one, then passes that inequality through the summable
multiplicity-indexed series.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem riemannXi_logDerivTerm_re_nonneg
    {s : Complex} (hs : 1 < s.re) (p : RiemannXiDivisorZeroIndex) :
    0 ≤ (1 / (s - riemannXiDivisorZeroValue p) +
      1 / riemannXiDivisorZeroValue p).re := by
  have hStrip := riemannXiDivisorZeroValue_re_mem_Ioo p
  have hFirst :
      0 ≤ (1 / (s - riemannXiDivisorZeroValue p)).re := by
    rw [one_div]
    exact zeroKernel_re_nonneg hs hStrip.2.le
  have hSecond : 0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg hStrip.1.le
      (Complex.normSq_nonneg (riemannXiDivisorZeroValue p))
  rw [Complex.add_re]
  exact add_nonneg hFirst hSecond

theorem riemannXi_logDerivTsum_re_nonneg
    {s : Complex} (hs : 1 < s.re) :
    0 ≤ (∑' p : RiemannXiDivisorZeroIndex,
      (1 / (s - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p)).re := by
  have hAway : forall p : RiemannXiDivisorZeroIndex,
      s ≠ riemannXiDivisorZeroValue p := by
    intro p hEqual
    have hUpper := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
    rw [← hEqual] at hUpper
    linarith
  have hSummable :=
    summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hAway
  have hRealPart :
      (∑' p : RiemannXiDivisorZeroIndex,
          (1 / (s - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p)).re =
        ∑' p : RiemannXiDivisorZeroIndex,
          (1 / (s - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p).re := by
    change Complex.reCLM
        (∑' p : RiemannXiDivisorZeroIndex,
          (1 / (s - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p)) = _
    rw [Complex.reCLM.map_tsum hSummable]
    rfl
  rw [hRealPart]
  exact tsum_nonneg (riemannXi_logDerivTerm_re_nonneg hs)

end BombieriVinogradov.SiegelWalfisz
