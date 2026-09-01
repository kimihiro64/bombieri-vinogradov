import BombieriVinogradov.Helpers.DirichletCharacter.CpowEndpointDecay
import BombieriVinogradov.Helpers.DirichletCharacter.CpowMajorantIntegrable
import Mathlib.NumberTheory.AbelSummation

/-!
# Ordered character Dirichlet-series convergence

This module owns Abel convergence of the natural ordered partial sums in the
half-plane `0 < re s`. It deliberately does not assert Mathlib `Summable`,
which would be an unordered and stronger convergence claim.
-/

set_option autoImplicit false

open Filter Finset MeasureTheory Set Topology

namespace BombieriVinogradov

/-- Ordered character Dirichlet partial sums converge to their Abel integral. -/
theorem characterDirichletPartialSums_tendsto_abelIntegral {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ Icc 0 n, (k : ℂ) ^ (-s) * chi k) atTop
      (𝓝 (-∫ t in Ioi (1 : ℝ), deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, chi k)) := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  have hzero : chi 0 = 0 := chi.map_zero' hN
  have hzeroNat : (fun n : ℕ => chi n) 0 = 0 := by simpa using hzero
  simpa only [zero_sub, Complex.ofReal_natCast] using
    tendsto_sum_mul_atTop_nhds_one_sub_integral₀
      (f := fun t : ℝ => (t : ℂ) ^ (-s)) (c := fun n : ℕ => chi n) (l := 0)
      hzeroNat
      (fun _t ht => differentiableAt_ofReal_cpow_neg hs ht)
      (locallyIntegrableOn_deriv_ofReal_cpow_neg hs)
      (characterPartialSum_cpow_tendsto_zero chi hchi hs)
      (deriv_cpow_mul_characterPartialSum_isBigO chi hchi s)
      (integrableAtFilter_rpow_neg_add_one_re hs)

end BombieriVinogradov
