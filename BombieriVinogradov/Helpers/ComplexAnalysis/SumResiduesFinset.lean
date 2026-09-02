import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Residue sums over finite sets

This module converts the subtype-indexed infinite sum used by sumResiduesIn
into an ordinary Finset sum when the region is finite.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.ComplexAnalysis

/-- A residue sum over the set coercion of a finset is the corresponding
finite sum. -/
theorem sumResiduesIn_finset (f : Complex -> Complex)
    (s : Finset Complex) :
    sumResiduesIn f (s : Set Complex) =
      Finset.sum s (fun z => residue f z) := by
  classical
  unfold sumResiduesIn
  let _ : Fintype (s : Set Complex) :=
    Set.Finite.fintype (Set.toFinite _)
  rw [tsum_fintype]
  rw [<- Finset.sum_subtype s (by intro z; simp)]

end BombieriVinogradov.ComplexAnalysis
