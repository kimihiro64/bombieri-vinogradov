import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Definitions

/-!
# Scalar Perron-series terms

This module owns the scalar Perron kernel weighted by one twisted von Mangoldt
coefficient, with the zeroth Dirichlet-series term defined to be zero.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- One twisted von Mangoldt coefficient multiplied by its scalar truncated
Perron kernel. -/
def scalarPerronSeriesTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) (n : Nat) : Complex :=
  if n = 0 then 0 else
    twistedMangoldtSequence chi n *
      truncatedPerronKernel ((x : Real) / (n : Real)) c T

end BombieriVinogradov.SiegelWalfisz
