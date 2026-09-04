import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLFunctionOrder
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionOrder
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber

/-!
# Equality of primitive and ambient completed-zero multiplicities

Completion changes no analytic order in the positive half-plane, and
the finite Euler correction is nonvanishing there. Thus each positive
real-part divisor fiber has exactly the same finite multiplicity.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem completedDivisorMultiplicity_eq_primitive
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Ne chi 1) {s : Complex} (hs : 0 < s.re) :
    Int.toNat (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
      (Set.univ : Set Complex) s) =
    Int.toNat (MeromorphicOn.divisor
      (symmetricCompletedLFunction chi.primitiveCharacter)
      (Set.univ : Set Complex) s) := by
  have hPrimitiveNe : Ne chi.primitiveCharacter 1 :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      chi hchi
  have hOrder : analyticOrderNatAt (symmetricCompletedLFunction chi) s =
      analyticOrderNatAt (symmetricCompletedLFunction chi.primitiveCharacter) s :=
    (analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hchi hs).trans
      ((analyticOrderNatAt_LFunction_eq_primitive chi hchi hs).trans
        (analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction
          hPrimitiveNe hs).symm)
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    (differentiable_symmetricCompletedLFunction hchi) s,
    Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (differentiable_symmetricCompletedLFunction hPrimitiveNe) s, hOrder]

end BombieriVinogradov.SiegelWalfisz
