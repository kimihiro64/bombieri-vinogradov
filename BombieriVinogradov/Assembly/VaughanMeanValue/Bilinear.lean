import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Proof.LargeSieve.CharacterReduction
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The nonmaximal bilinear character large sieve

This module derives Vaughan's nonmaximal bilinear estimate directly from the
proved primitive-character large sieve. The proof flattens the modulus and
primitive-character sums and applies weighted Cauchy--Schwarz.
-/

set_option autoImplicit false

noncomputable section

open Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

/-- An index for a primitive character together with its modulus. -/
abbrev PrimitiveCharacterIndex :=
  Sigma fun q : Nat => DirichletCharacter Complex q

/-- All primitive characters with moduli in `1,...,Q`. -/
def primitiveCharacterIndices (Q : Nat) : Finset PrimitiveCharacterIndex :=
  (Icc 1 Q).sigma primitiveCharacters

/-- The one-dimensional character large sieve in the positive-interval
coefficient convention used by the bilinear estimates. -/
theorem positiveCharacterEnergy (M Q : Nat) (a : Nat -> Complex)
    (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, ‖positiveCharacterSum a M q chi‖ ^ 2 <=
      36 * ((M : Real) + (Q : Real) ^ 2) * positiveCoefficientMass a M := by
  simpa [positiveCharacterSum, positiveCoefficientMass] using
    (characterLargeSieveNat 0 M Q (positiveIntervalCoefficients a) hQ)

/-- Vaughan's nonmaximal bilinear character large sieve, with the explicit
constant inherited from the proved one-dimensional large sieve. -/
theorem nonmaximalBilinearLargeSieve
    (M N Q : Nat) (a b : Nat -> Complex) (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖bilinearCharacterProduct a b M N q chi‖ <=
      Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) *
          positiveCoefficientMass a M) *
        Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
          positiveCoefficientMass b N) := by
  let weight : PrimitiveCharacterIndex -> Real := fun i =>
    (i.1 : Real) / (i.1.totient : Real)
  let left : PrimitiveCharacterIndex -> Real := fun i =>
    ‖positiveCharacterSum a M i.1 i.2‖
  let right : PrimitiveCharacterIndex -> Real := fun i =>
    ‖positiveCharacterSum b N i.1 i.2‖
  let leftWeighted : PrimitiveCharacterIndex -> Real := fun i =>
    Real.sqrt (weight i) * left i
  let rightWeighted : PrimitiveCharacterIndex -> Real := fun i =>
    Real.sqrt (weight i) * right i
  have hweight (i : PrimitiveCharacterIndex) (hi : i ∈ primitiveCharacterIndices Q) :
      0 <= weight i := by
    dsimp [weight]
    positivity
  have hleftSquare :
      ∑ i ∈ primitiveCharacterIndices Q, leftWeighted i ^ 2 =
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, ‖positiveCharacterSum a M q chi‖ ^ 2 := by
    unfold primitiveCharacterIndices
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hw : 0 <= (q : Real) / (q.totient : Real) := by positivity
    dsimp [leftWeighted, weight, left]
    rw [mul_pow, Real.sq_sqrt hw]
  have hrightSquare :
      ∑ i ∈ primitiveCharacterIndices Q, rightWeighted i ^ 2 =
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, ‖positiveCharacterSum b N q chi‖ ^ 2 := by
    unfold primitiveCharacterIndices
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hw : 0 <= (q : Real) / (q.totient : Real) := by positivity
    dsimp [rightWeighted, weight, right]
    rw [mul_pow, Real.sq_sqrt hw]
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt
    (primitiveCharacterIndices Q) leftWeighted rightWeighted
  have hflatten :
      (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ‖bilinearCharacterProduct a b M N q chi‖) =
        ∑ i ∈ primitiveCharacterIndices Q, leftWeighted i * rightWeighted i := by
    unfold primitiveCharacterIndices
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hw : 0 <= (q : Real) / (q.totient : Real) := by positivity
    rw [show bilinearCharacterProduct a b M N q chi =
      positiveCharacterSum a M q chi * positiveCharacterSum b N q chi by rfl]
    rw [norm_mul]
    dsimp [leftWeighted, rightWeighted, weight, left, right]
    calc
      ((q : Real) / (q.totient : Real)) *
          (‖positiveCharacterSum a M q chi‖ *
            ‖positiveCharacterSum b N q chi‖) =
        (Real.sqrt ((q : Real) / (q.totient : Real)) *
            Real.sqrt ((q : Real) / (q.totient : Real))) *
          ‖positiveCharacterSum a M q chi‖ *
          ‖positiveCharacterSum b N q chi‖ := by
            rw [Real.mul_self_sqrt hw]
            ring
      _ = (Real.sqrt ((q : Real) / (q.totient : Real)) *
              ‖positiveCharacterSum a M q chi‖) *
            (Real.sqrt ((q : Real) / (q.totient : Real)) *
              ‖positiveCharacterSum b N q chi‖) := by ring
  rw [hflatten]
  apply hcauchy.trans
  rw [hleftSquare, hrightSquare]
  have hleftEnergy := positiveCharacterEnergy M Q a hQ
  have hrightEnergy := positiveCharacterEnergy N Q b hQ
  gcongr

end BombieriVinogradov.VaughanMeanValue
