import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Explicit-formula contour data

This module owns the two diagonal corners of the finite rectangle and the
normalized integral over the three boundary segments left after removing the
right vertical side.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The lower-left corner `-U - iT` of the finite contour rectangle. -/
def explicitFormulaContourLowerLeft (U T : Real) : Complex :=
  Complex.mk (-U) (-T)

/-- The upper-right corner `c + iT` of the finite contour rectangle. -/
def explicitFormulaContourUpperRight (c T : Real) : Complex :=
  Complex.mk c T

/-- The normalized integral along the bottom, left, and top sides, oriented
from `c - iT` to `-U - iT`, then to `-U + iT`, then to `c + iT`. -/
def explicitFormulaBrokenBoundaryIntegral (f : Complex -> Complex)
    (U c T : Real) : Complex :=
  HIntegral' f c (-U) (-T) +
    VIntegral' f (-U) (-T) T +
    HIntegral' f (-U) c T

end BombieriVinogradov.SiegelWalfisz
