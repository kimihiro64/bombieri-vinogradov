import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.CharacterFacts
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# A uniform zero-free predicate for primitive quadratic characters

This module names the family-wide zero-free alternative used in the source
dichotomy for Siegel's lower bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- Every primitive quadratic nonprincipal character is zero-free from `s` to one. -/
def PrimitiveQuadraticZeroFreeFrom (s : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N),
    DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 -> Ne chi 1 ->
      ∀ t : ℝ, s ≤ t -> t ≤ 1 -> Ne (chi.LFunction t) 0

theorem PrimitiveQuadraticZeroFreeFrom.mono {lower s : ℝ}
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom lower) (h : lower ≤ s) :
    PrimitiveQuadraticZeroFreeFrom s := by
  intro N _ chi hprimitive hsquare hne t hst ht
  exact hzeroFree N chi hprimitive hsquare hne t (h.trans hst) ht

end BombieriVinogradov.SiegelWalfisz
