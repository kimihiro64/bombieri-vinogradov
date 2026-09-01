import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Vaughan-identity definitions

These definitions follow the Dirichlet-series algebra in Vaughan's Chapter 6
proof. The source slide displaying Lemma 5 has a sign error and swaps two
cutoff roles; the definitions below preserve the proof's explicit convention
`F = Lambda_{<=u}` and `G = mu_{<=v}`. The later Bombieri-Vinogradov
application takes `u = v`, so the endpoint correction does not alter that
application.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.VaughanIdentity

open ArithmeticFunction

/-- Truncate an arithmetic function to positive arguments at most `cutoff`. -/
def truncateLE {R : Type*} [Zero R] (a : ArithmeticFunction R)
    (cutoff : Nat) : ArithmeticFunction R :=
  ⟨fun n => if n <= cutoff then a n else 0, by simp⟩

@[simp]
theorem truncateLE_apply {R : Type*} [Zero R]
    (a : ArithmeticFunction R) (cutoff n : Nat) :
    truncateLE a cutoff n = if n <= cutoff then a n else 0 := rfl

/-- The von Mangoldt head `F = Lambda_{<=u}`. -/
def lambdaHead (u : Nat) : ArithmeticFunction Real :=
  truncateLE ArithmeticFunction.vonMangoldt u

/-- The real-valued Moebius head `G = mu_{<=v}`. -/
def moebiusHead (v : Nat) : ArithmeticFunction Real :=
  truncateLE (ArithmeticFunction.moebius : ArithmeticFunction Real) v

/-- First Type I kernel, corresponding to `G * log`. -/
def typeI1Kernel (v : Nat) : ArithmeticFunction Real :=
  moebiusHead v * ArithmeticFunction.log

/-- Second Type I kernel, corresponding to `F * G * zeta`. -/
def typeI2Kernel (u v : Nat) : ArithmeticFunction Real :=
  lambdaHead u * moebiusHead v * ArithmeticFunction.zeta

/-- Type II kernel formed from the complementary von Mangoldt and Moebius tails. -/
def typeIIKernel (u v : Nat) : ArithmeticFunction Real :=
  (ArithmeticFunction.log - lambdaHead u * ArithmeticFunction.zeta) *
    ((ArithmeticFunction.moebius : ArithmeticFunction Real) - moebiusHead v)

/-- Weight one real arithmetic kernel by a complex test function through `y`. -/
def weightedKernelSum (kernel : ArithmeticFunction Real)
    (y : Nat) (f : Nat -> Complex) : Complex :=
  ∑ n ∈ Icc 1 y, (kernel n : Complex) * f n

/-- The finite von Mangoldt sum on the left side of Vaughan's identity. -/
def mangoldtSum (y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum ArithmeticFunction.vonMangoldt y f

/-- The first Type I piece. Its Moebius cutoff is `v`, as required by `G`. -/
def vaughanS1 (v y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum (typeI1Kernel v) y f

/-- The second Type I piece. -/
def vaughanS2 (u v y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum (typeI2Kernel u v) y f

/-- The Type II piece, with a positive sign in the corrected identity. -/
def vaughanS3 (u v y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum (typeIIKernel u v) y f

/-- The truncated von Mangoldt remainder `F`, hence cut off at `u`. -/
def vaughanS4 (u y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum (lambdaHead u) y f

/-- Corrected source-level Vaughan identity.

The displayed source formula says `S1 - S2 - S3 + S4`, but its own proof
algebra and the test `u = v = 1`, `n = 6` require a positive `S3`. The same
proof defines `F = Lambda_{<=u}` and `G = mu_{<=v}`, which fixes the cutoff
roles used here.
-/
def VaughanIdentityStatement : Prop :=
  ∀ (u v y : Nat) (f : Nat -> Complex), 0 < u -> 0 < v -> 2 <= y ->
    mangoldtSum y f =
      vaughanS1 v y f - vaughanS2 u v y f +
        vaughanS3 u v y f + vaughanS4 u y f

end BombieriVinogradov.VaughanIdentity
