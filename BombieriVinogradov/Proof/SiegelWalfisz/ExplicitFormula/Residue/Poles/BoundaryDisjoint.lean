import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.OriginalPoleZero
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Data.Set.Lattice
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Original integrand pole exclusion on a rectangle border

This module converts zero avoidance and pointwise L-function nonvanishing
into the disjointness hypothesis required by the contour residue theorem.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem disjoint_explicitFormulaIntegrand_poles_boundary_of_LFunction_ne_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (z w : Complex)
    (hzero : Not ((RectangleBorder z w) 0))
    (hLFunction : forall p : Complex,
      (RectangleBorder z w) p -> Ne (chi.LFunction p) 0) :
    Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt (explicitFormulaIntegrand chi x) p < 0} := by
  rw [Set.disjoint_left]
  intro p hpBorder hpPole
  have hpNe : Ne p 0 := by
    intro hpZero
    apply hzero
    change (RectangleBorder z w) p at hpBorder
    rw [hpZero] at hpBorder
    exact hpBorder
  have hLZero : chi.LFunction p = 0 :=
    LFunction_eq_zero_of_explicitFormulaIntegrand_pole
      hchi x hx hpNe hpPole
  exact (hLFunction p hpBorder) hLZero

end BombieriVinogradov.SiegelWalfisz
