import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Bounded meromorphic functions have nonnegative order

This module provides the small punctured-neighborhood boundedness lemma needed
when a meromorphic principal part has been removed.
-/

set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

/-- A meromorphic complex function that is `O(1)` on a punctured
neighborhood cannot have negative meromorphic order at the puncture. -/
theorem meromorphicOrderAt_nonneg_of_isBigO_one
    {f : Complex -> Complex} {p : Complex}
    (_hf : MeromorphicAt f p)
    (hO : f =O[nhdsWithin p (Compl.compl ({p} : Set Complex))]
      (1 : Complex -> Complex)) :
    0 <= meromorphicOrderAt f p := by
  let _ : Filter.NeBot
      (nhdsWithin p (Compl.compl ({p} : Set Complex))) :=
    NormedField.nhdsNE_neBot p
  by_contra hnonneg
  have hneg : meromorphicOrderAt f p < 0 := lt_of_not_ge hnonneg
  have hnorm :
      Filter.Tendsto (fun z : Complex => norm (f z))
        (nhdsWithin p (Compl.compl ({p} : Set Complex))) Filter.atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  exact (Filter.not_isBoundedUnder_of_tendsto_atTop hnorm)
    hO.isBoundedUnder_le

end BombieriVinogradov.ComplexAnalysis
