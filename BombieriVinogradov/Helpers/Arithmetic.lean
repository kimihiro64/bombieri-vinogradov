import BombieriVinogradov.Definitions.Basic

/-!
# Reusable arithmetic helpers

This layer contains reusable lemmas that do not depend on one headline proof
route. Shared results belong here instead of inside final theorem modules.
-/

namespace BombieriVinogradov

/-- Adding a natural number to itself equals multiplication by two. -/
theorem add_self_eq_two_mul (n : ℕ) : n + n = 2 * n := by
  exact (Nat.two_mul n).symm

end BombieriVinogradov
