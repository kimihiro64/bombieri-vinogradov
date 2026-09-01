import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaIntegralNorm
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.RealGammaGrowth

/-!
# Complex Gamma growth on a right half-plane

This module transfers the real Gamma growth estimate to complex arguments
whose real part is at least one quarter.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_Gamma_le_growth {s : ℂ} (hs : 1 / 4 ≤ s.re) :
    ‖Complex.Gamma s‖ ≤ 4 * (s.re + 1) ^ (s.re + 1) := by
  exact (norm_Gamma_le_realGamma_re (by linarith)).trans
    (realGamma_le_growth hs)

end BombieriVinogradov.SiegelWalfisz
