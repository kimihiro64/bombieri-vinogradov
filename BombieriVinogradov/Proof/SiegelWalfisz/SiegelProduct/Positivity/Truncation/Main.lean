import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Truncation.PoleGrowth
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Truncation.Tail

/-!
# Truncation package for positivity near the Siegel pole

This module packages the independent tail-decay and pole-growth consequences of the cutoff.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelTruncation_spec {A B Q delta : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 ∧
      (1 + delta) ^ siegelTruncationIndex B Q K ≤
        Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) :=
  ⟨truncationTail_lt_half hA hB hAB hQ,
    truncationPoleGrowth hB hQ hdelta0 hdelta⟩

end BombieriVinogradov.SiegelWalfisz
