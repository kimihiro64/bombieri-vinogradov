import BombieriVinogradov.Proof.Main

/-!
# Final theorem assembly

This outer layer composes completed proof branches into the results exported to
`Solution.lean`. It should contain little reusable low-level mathematics.
-/

namespace BombieriVinogradov

/-- Assembled proof of the template wiring theorem. -/
theorem assembled_main_result (n : ℕ) : n + n = 2 * n := by
  exact main_result_proof n

end BombieriVinogradov
