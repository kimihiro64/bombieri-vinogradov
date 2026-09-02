import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Main

/-!
# Perron error data

This module owns the scalar step term paired with a Perron-series term and the
half-weighted character Chebyshev sum occurring in the source formula.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

/-- One twisted von Mangoldt coefficient multiplied by the Perron step
weight. The zeroth Dirichlet-series term is explicitly zero. -/
def scalarPerronStepTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x n : Nat) : Complex :=
  if n = 0 then 0 else
    twistedMangoldtSequence chi n *
      (perronStepWeight ((x : Real) / (n : Real)) : Complex)

/-- The character Chebyshev sum with half weight at the natural endpoint. -/
def characterChebyshevHalfSum {N : Nat}
    (x : Nat) (chi : DirichletCharacter Complex N) : Complex :=
  (Finset.sum (Finset.Ico 1 x) (twistedMangoldtSequence chi)) +
    (1 / 2 : Complex) * twistedMangoldtSequence chi x

end BombieriVinogradov.SiegelWalfisz
