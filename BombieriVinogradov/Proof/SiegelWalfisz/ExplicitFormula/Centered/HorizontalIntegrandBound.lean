import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.HorizontalKernelBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.IntegrandDifference

/-!
# Pointwise centered horizontal-integrand bound

This module combines the centered integrand identity with the elementary
horizontal kernel estimate under a supplied logarithmic-derivative bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem norm_explicitFormulaIntegrand_sub_one_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (hx : 2 < x) {s : Complex}
    (hsRe : s.re <= optimizedPerronLine x)
    (hsIm : 0 < abs s.im) {B : Real}
    (hLog : norm (logDeriv chi.LFunction s) <= B) :
    norm (explicitFormulaIntegrand chi x s -
        explicitFormulaIntegrand chi 1 s) <=
      B * (4 * (x : Real) / abs s.im) := by
  have hKernel := norm_centered_cpow_kernel_horizontal_le x hx hsRe hsIm
  have hB : 0 <= B := (norm_nonneg _).trans hLog
  rw [explicitFormulaIntegrand_sub_one_eq, norm_mul, norm_neg]
  exact mul_le_mul hLog hKernel (norm_nonneg _) hB

end BombieriVinogradov.SiegelWalfisz
