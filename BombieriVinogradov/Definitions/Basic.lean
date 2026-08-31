import Mathlib.Data.Nat.Basic

/-!
# Stable definitions

This innermost layer owns mathematical definitions and imports no project proof
modules. Replace the toy definition with the project's foundational objects.
-/

namespace BombieriVinogradov

/-- The toy doubling operation used by the architecture fixture. -/
def twice (n : ℕ) : ℕ := n + n

end BombieriVinogradov
