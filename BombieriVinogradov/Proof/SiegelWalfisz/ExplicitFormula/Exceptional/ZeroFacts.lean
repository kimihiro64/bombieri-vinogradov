import Mathlib.Analysis.Analytic.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Facts required of the selected exceptional zero

This proposition keeps quadraticity, simplicity and geometric separation
together at the interface consumed by the exceptional residue calculation.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

structure ExceptionalZeroFacts
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (beta : Complex) : Prop where
  quadratic : chi ^ 2 = 1
  simple : analyticOrderNatAt chi.LFunction beta = 1
  re_lower : (3 / 4 : Real) <= beta.re
  reflection_ne : Ne beta (1 - beta)

end BombieriVinogradov.SiegelWalfisz
