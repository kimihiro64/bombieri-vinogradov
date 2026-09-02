import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Explicit-formula integrand

This module owns only the source contour integrand `-(L'/L)(s) x^s / s`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The source integrand `-(L'/L)(s) x^s / s`. -/
def explicitFormulaIntegrand {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Nat) (s : Complex) : Complex :=
  logDeriv chi.LFunction s * (-((x : Complex) ^ s / s))

end BombieriVinogradov.SiegelWalfisz
