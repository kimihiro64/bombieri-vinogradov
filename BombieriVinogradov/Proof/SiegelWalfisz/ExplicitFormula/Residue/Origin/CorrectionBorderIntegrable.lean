import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Border integrability of the origin correction

This module proves the local boundary regularity needed to add the origin
correction inside a rectangle integral.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The origin double-pole correction is integrable on any rectangle border
that avoids zero. -/
theorem rectangleBorderIntegrable_originDoublePoleCorrection
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (z w : Complex)
    (hzero : Not (Membership.mem (RectangleBorder z w) 0)) :
    RectangleBorderIntegrable (originDoublePoleCorrection chi) z w := by
  have hcont : ContinuousOn (originDoublePoleCorrection chi)
      (RectangleBorder z w) := by
    change ContinuousOn
      (fun s : Complex => (lFunctionOriginMultiplicity chi : Complex) / s ^ 2)
      (RectangleBorder z w)
    exact
      continuousOn_const.div (continuousOn_id.pow 2)
        (fun s hs => pow_ne_zero 2 (by
          intro hs0
          apply hzero
          simpa [hs0] using hs))
  exact hcont.rectangleBorder_integrable

end BombieriVinogradov.SiegelWalfisz
