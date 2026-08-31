import BombieriVinogradov

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

theorem BombieriVinogradov.main_result (n : ℕ) : n + n = 2 * n := by
  exact assembled_main_result n
