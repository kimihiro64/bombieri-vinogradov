import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Definitions
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Data for the explicit-formula Perron series

This module owns the twisted von Mangoldt sequence, its pointwise Dirichlet
term after multiplication by the Perron kernel, and the finite normalized
vertical integral of the explicit-formula integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The Dirichlet coefficients `chi(n) * Lambda(n)`. -/
def twistedMangoldtSequence {N : Nat}
    (chi : DirichletCharacter Complex N) (n : Nat) : Complex :=
  chi n * (ArithmeticFunction.vonMangoldt n : Complex)

/-- One term of the twisted von Mangoldt L-series multiplied by the Perron
factor `x ^ s / s`. -/
def explicitFormulaDirichletTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x n : Nat) (s : Complex) : Complex :=
  LSeries.term (twistedMangoldtSequence chi) s n *
    ((x : Complex) ^ s / s)

/-- The finite normalized vertical integral used before the contour shift. -/
def explicitFormulaVerticalIntegral {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) : Complex :=
  VIntegral' (explicitFormulaIntegrand chi x) c (-T) T

end BombieriVinogradov.SiegelWalfisz
