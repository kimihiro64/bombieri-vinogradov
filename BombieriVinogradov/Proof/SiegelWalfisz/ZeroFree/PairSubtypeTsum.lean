import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Infinite sums over a two-element subtype

This module isolates the finite-subtype bookkeeping needed when Lemma 11.3
retains exactly two multiplicity-indexed zeros.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem tsum_pair_subtype {alpha : Type} [DecidableEq alpha]
    (p q : alpha) (hpq : p ≠ q) (f : alpha → Real) :
    (∑' r : ({p, q} : Set alpha), f r.1) = f p + f q := by
  classical
  let _ : Fintype ({p, q} : Set alpha) := Set.Finite.fintype (Set.toFinite _)
  rw [tsum_fintype]
  rw [← Finset.sum_subtype ({p, q} : Finset alpha) (by intro x; simp)]
  simp [hpq]

end BombieriVinogradov.SiegelWalfisz
