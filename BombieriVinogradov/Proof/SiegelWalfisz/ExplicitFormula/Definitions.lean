import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence

/-!
# Data for the truncated Dirichlet explicit formula

This module defines the finite character Chebyshev sum, a finite
multiplicity-aware truncation of completed zeros in the critical strip, the
exceptional-zero interface, and Strombergsson's source error scale.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

/-- The source sum `psi(x, chi)` through the natural endpoint `x`. -/
def characterChebyshevSum {N : Nat} (x : Nat)
    (chi : DirichletCharacter Complex N) : Complex :=
  BombieriVinogradov.VaughanMeanValue.psiCharacterSum x N chi

/-- Multiplicity indices of completed primitive zeros in the truncated critical strip. -/
def criticalStripZeroSet {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (T : Real) :
    Set (SymmetricCompletedZeroIndex chi) :=
  {p | 0 < (Complex.Hadamard.divisorZeroIndex₀_val p).re ∧
    (Complex.Hadamard.divisorZeroIndex₀_val p).re < 1 ∧
    |(Complex.Hadamard.divisorZeroIndex₀_val p).im| < T}

theorem criticalStripZeroSet_finite {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (T : Real) :
    (criticalStripZeroSet chi T).Finite := by
  apply (Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
    (f := symmetricCompletedLFunction chi)
    (U := (Set.univ : Set Complex)) (B := |T| + 2) (by simp)).subset
  intro p hp
  rcases hp with ⟨hpRePos, hpReLt, hpIm⟩
  have hTPos : 0 < T := (abs_nonneg _).trans_lt hpIm
  have hpReAbs : |(Complex.Hadamard.divisorZeroIndex₀_val p).re| ≤ 1 := by
    rw [abs_of_pos hpRePos]
    exact hpReLt.le
  have hpImAbs : |(Complex.Hadamard.divisorZeroIndex₀_val p).im| ≤ |T| := by
    rw [abs_of_pos hTPos]
    exact hpIm.le
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

/-- Finite multiplicity-aware truncation of completed zeros in the critical strip. -/
def criticalStripZeroTruncation {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (T : Real) :
    Finset (SymmetricCompletedZeroIndex chi) :=
  (criticalStripZeroSet_finite chi T).toFinset

@[simp] theorem mem_criticalStripZeroTruncation_iff
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {p : SymmetricCompletedZeroIndex chi} :
    p ∈ criticalStripZeroTruncation chi T ↔
      0 < (Complex.Hadamard.divisorZeroIndex₀_val p).re ∧
      (Complex.Hadamard.divisorZeroIndex₀_val p).re < 1 ∧
      |(Complex.Hadamard.divisorZeroIndex₀_val p).im| < T := by
  simp [criticalStripZeroTruncation, criticalStripZeroSet]

/-- The source exceptional-zero predicate for the chosen zero-free constant. -/
def IsExceptionalZero {N : Nat} [NeZero N]
    (c : Real) (chi : DirichletCharacter Complex N) (rho : Complex) : Prop :=
  chi.LFunction rho = 0 ∧ rho.im = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧
    1 - c / Real.log N < rho.re

/-- An optional exceptional zero faithfully records existence or nonexistence. -/
def IsExceptionalZeroChoice {N : Nat} [NeZero N]
    (c : Real) (chi : DirichletCharacter Complex N) : Option Complex -> Prop
  | none => ¬ exists rho : Complex, IsExceptionalZero c chi rho
  | some rho => IsExceptionalZero c chi rho

/-- A zero survives the primed source sum unless it is exceptional or its reflection. -/
def IsRetainedZero (exceptional : Option Complex) (rho : Complex) : Prop :=
  match exceptional with
  | none => True
  | some beta => rho ≠ beta ∧ rho ≠ 1 - beta

/-- The multiplicity-aware truncated zero sum in Strombergsson equation (502). -/
def truncatedCriticalZeroSum {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Nat) (T : Real)
    (exceptional : Option Complex) : Complex := by
  classical
  exact ∑ p ∈ (criticalStripZeroTruncation chi T).filter fun p =>
        IsRetainedZero exceptional (Complex.Hadamard.divisorZeroIndex₀_val p),
      (x : Complex) ^ (Complex.Hadamard.divisorZeroIndex₀_val p) /
        Complex.Hadamard.divisorZeroIndex₀_val p

/-- The visible exceptional contribution in Strombergsson equation (502). -/
def exceptionalZeroContribution (x : Nat) : Option Complex -> Complex
  | none => 0
  | some beta => (x : Complex) ^ beta / beta

/-- The source error scale `x/T log(qx)^2 + x^(1/4) log x`. -/
def explicitFormulaRemainderMajorant (N x : Nat) (T : Real) : Real :=
  (x : Real) / T * Real.log ((N * x : Nat) : Real) ^ 2 +
    (x : Real) ^ (1 / 4 : Real) * Real.log x

end BombieriVinogradov.SiegelWalfisz
