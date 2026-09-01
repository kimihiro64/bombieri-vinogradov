import BombieriVinogradov.Definitions.CharacterSums
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Vaughan mean-value definitions

This module states Vaughan's Basic Mean Value Theorem and the maximal
bilinear large-sieve estimate used in its proof. The maximal domains are
finite: real cutoffs are represented by all natural endpoints through their
floor, including endpoint zero where the relevant sum is empty.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

/-- The primitive-character Chebyshev sum through the natural endpoint `y`. -/
def psiCharacterSum (y q : Nat) (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Icc 1 y,
    (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q)

/-- The maximum of `|psi(y; chi)|` over natural `y <= floor(x)`. -/
def maximalPsiNorm (x : Real) {q : Nat}
    (chi : DirichletCharacter Complex q) : Real :=
  (range (⌊x⌋₊ + 1)).sup' (by simp) fun y => ‖psiCharacterSum y q chi‖

/-- Vaughan's weighted primitive-character mean `T(x, Q)`. -/
def primitivePsiMean (x : Real) (Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalPsiNorm x chi

/-- The explicit growth term in the Basic Mean Value Theorem. -/
def basicMeanValueMajorant (x : Real) (Q : Nat) : Real :=
  (x + x ^ (5 / 6 : Real) * (Q : Real) +
      x ^ (1 / 2 : Real) * (Q : Real) ^ 2) *
    Real.log (x * (Q : Real)) ^ 3

/-- Vaughan's Basic Mean Value Theorem with one absolute implied constant. -/
def VaughanMeanValueStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧ ∀ (x : Real) (Q : Nat), 2 <= x -> 1 <= Q ->
      primitivePsiMean x Q <= C * basicMeanValueMajorant x Q

/-- A bilinear character sum restricted by the product cutoff `m*n <= Y`. -/
def restrictedBilinearCharacterSum (a b : Nat -> Complex)
    (M N Y q : Nat) (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
    if m * n <= Y then a m * b n * chi ((m * n : Nat) : ZMod q) else 0

/-- The maximum norm of the restricted bilinear sum over `Y <= X`. -/
def maximalBilinearNorm (a b : Nat -> Complex)
    (M N X : Nat) {q : Nat} (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖restrictedBilinearCharacterSum a b M N Y q chi‖

/-- Squared `L2` mass of a coefficient sequence on `1,...,M`. -/
def coefficientMass (a : Nat -> Complex) (M : Nat) : Real :=
  ∑ m ∈ Icc 1 M, ‖a m‖ ^ 2

/-- The maximal bilinear character large sieve (Vaughan Chapter 5, Theorem 6). -/
def MaximalBilinearLargeSieveStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧
      ∀ (X M N Q : Nat) (a b : Nat -> Complex),
        2 <= X -> 1 <= M -> 1 <= N -> 1 <= Q ->
          ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
              ∑ chi ∈ primitiveCharacters q,
                maximalBilinearNorm a b M N X chi <=
            C * Real.log ((X * M * N : Nat) : Real) *
              Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
                ((N : Real) + (Q : Real) ^ 2) *
                coefficientMass a M * coefficientMass b N)

/-- Extend coefficients on positive naturals to the integer interval used by
the proved character large sieve. -/
def positiveIntervalCoefficients (a : Nat -> Complex) (n : Int) : Complex :=
  a n.toNat

/-- Character sum over the positive interval `1,...,M`, expressed in the
integer-interval convention of the character large sieve. -/
def positiveCharacterSum (a : Nat -> Complex) (M q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  intervalCharacterSum (positiveIntervalCoefficients a) 0 M q chi

/-- Coefficient mass in the same positive integer-interval convention. -/
def positiveCoefficientMass (a : Nat -> Complex) (M : Nat) : Real :=
  ∑ n ∈ Ioc (0 : Int) (M : Int), ‖positiveIntervalCoefficients a n‖ ^ 2

/-- Unrestricted bilinear character product from Vaughan Chapter 5, Lemma 5. -/
def bilinearCharacterProduct (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  positiveCharacterSum a M q chi * positiveCharacterSum b N q chi

end BombieriVinogradov.VaughanMeanValue
