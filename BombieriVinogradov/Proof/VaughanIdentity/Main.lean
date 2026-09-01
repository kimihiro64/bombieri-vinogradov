import BombieriVinogradov.Proof.VaughanIdentity.Kernel
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The corrected finite Vaughan identity

The arithmetic-function kernel equality is applied coefficientwise to an
arbitrary complex test function. Positivity of the cutoffs and `2 <= y` are
retained from the source statement even though the algebraic equality itself
does not need them.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.VaughanIdentity

/-- Vaughan's exact finite decomposition, with the source sign and cutoff
errata corrected according to its proof algebra. -/
theorem vaughanIdentity : VaughanIdentityStatement := by
  intro u v y f hu hv hy
  unfold mangoldtSum vaughanS1 vaughanS2 vaughanS3 vaughanS4 weightedKernelSum
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hcoeff := congrArg (fun kernel : ArithmeticFunction Real => kernel n)
    (vaughanKernelIdentity u v)
  change ((ArithmeticFunction.vonMangoldt n : Real) : Complex) * f n = _
  rw [hcoeff]
  change (((typeI1Kernel v n - typeI2Kernel u v n + typeIIKernel u v n +
    lambdaHead u n : Real) : Complex) * f n) = _
  push_cast
  ring

end BombieriVinogradov.VaughanIdentity
