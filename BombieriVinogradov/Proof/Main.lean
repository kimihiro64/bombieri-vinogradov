import BombieriVinogradov.Helpers.Arithmetic

/-!
# Main proof branch

This module demonstrates a route-specific theorem that consumes reusable inner
helpers. Substantial projects should use independent subdirectories under
`Proof/` and compose them only in an outward `Assembly/` layer.
-/

namespace BombieriVinogradov

/-- Proof-side implementation of the template wiring theorem. -/
theorem main_result_proof (n : ℕ) : n + n = 2 * n := by
  exact add_self_eq_two_mul n

end BombieriVinogradov
