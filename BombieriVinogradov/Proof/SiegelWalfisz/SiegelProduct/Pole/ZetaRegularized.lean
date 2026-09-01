import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The regular part of the Riemann zeta function

This module exposes the Mathlib completion of `ζ(s) - (s - 1)⁻¹` as the zeta input to Siegel's proof.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem zetaRegularized_differentiable : Differentiable ℂ riemannZeta₀ :=
  differentiable_riemannZeta₀

theorem riemannZeta_eq_pole_add_regularized {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s :=
  riemannZeta_eq_inv_sub_add hs

end BombieriVinogradov.SiegelWalfisz
