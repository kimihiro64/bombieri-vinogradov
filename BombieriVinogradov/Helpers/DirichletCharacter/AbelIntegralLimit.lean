import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegralNormalization
import BombieriVinogradov.Helpers.DirichletCharacter.AbelPartialSumLimit

/-!
# Character partial sums converge to the Abel integral

This module is the thin convergence consumer joining the ordered Abel limit to
the source-normalized integral.
-/

set_option autoImplicit false

open Filter Finset Topology

namespace BombieriVinogradov

/-- Natural ordered character Dirichlet partial sums converge to `characterAbelIntegral`. -/
theorem characterDirichletPartialSums_tendsto_abelIntegralValue
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ Icc 0 n, (k : ℂ) ^ (-s) * chi k) atTop
      (𝓝 (characterAbelIntegral chi s)) := by
  simpa only [neg_integral_deriv_cpow_mul_characterPartialSum_eq_abelIntegral chi hchi hs] using
    characterDirichletPartialSums_tendsto_abelIntegral chi hchi hs

end BombieriVinogradov
