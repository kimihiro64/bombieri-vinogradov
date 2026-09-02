import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedBoundaryPoles
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedFinitePoles
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedMeromorphic
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedSimpleOn
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Rectangle residue theorem for the regularized integrand

This module composes the four analytic hypotheses required by the pinned
simple-pole rectangle residue theorem.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The normalized rectangle integral of the regularized explicit-formula
integrand equals the sum of its residues in every admissible rectangle. -/
theorem rectangleIntegral'_regularizedExplicitFormulaIntegrand_eq_sumResiduesIn
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (z w : Complex)
    (hre : z.re <= w.re) (him : z.im <= w.im)
    (horiginal : Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt (explicitFormulaIntegrand chi x) p < 0})
    (hzero : Not (Membership.mem (RectangleBorder z w) 0)) :
    RectangleIntegral' (regularizedExplicitFormulaIntegrand chi x) z w =
      sumResiduesIn (regularizedExplicitFormulaIntegrand chi x)
        (Set.inter (Complex.Rectangle z w)
          {p | meromorphicOrderAt
            (regularizedExplicitFormulaIntegrand chi x) p < 0}) :=
  RectangleIntegral'_eq_sumResiduesIn hre him
    (meromorphic_regularizedExplicitFormulaIntegrand hchi x hx).meromorphicOn
    (disjoint_regularizedExplicitFormulaIntegrand_poles_boundary
      hchi x hx z w horiginal hzero)
    (finite_regularizedExplicitFormulaIntegrand_polesInRectangle
      hchi x hx z w)
    (hasSimplePolesOn_regularizedExplicitFormulaIntegrand
      hchi x hx (Complex.Rectangle z w))

end BombieriVinogradov.SiegelWalfisz
