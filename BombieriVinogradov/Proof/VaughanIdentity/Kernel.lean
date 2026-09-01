import BombieriVinogradov.Definitions.VaughanIdentity
import Mathlib.Tactic.Ring

/-!
# Vaughan's arithmetic-function kernel identity

This module proves the corrected Dirichlet-convolution identity and expands
its Type I and Type II kernels into finite factor sums. These expansions make
the sign and cutoff roles independently auditable before analytic estimates
are added.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.VaughanIdentity

open ArithmeticFunction

/-- Vaughan's exact arithmetic-function identity with the corrected Type II sign. -/
theorem vaughanKernelIdentity (u v : Nat) :
    ArithmeticFunction.vonMangoldt =
      typeI1Kernel v - typeI2Kernel u v + typeIIKernel u v + lambdaHead u := by
  have hzetaMu :
      (ArithmeticFunction.zeta : ArithmeticFunction Real) *
          (ArithmeticFunction.moebius : ArithmeticFunction Real) = 1 :=
    ArithmeticFunction.coe_zeta_mul_coe_moebius
  calc
    ArithmeticFunction.vonMangoldt =
        ArithmeticFunction.log *
          (ArithmeticFunction.moebius : ArithmeticFunction Real) :=
      ArithmeticFunction.log_mul_moebius_eq_vonMangoldt.symm
    _ = typeI1Kernel v - typeI2Kernel u v + typeIIKernel u v + lambdaHead u := by
      calc
        ArithmeticFunction.log *
            (ArithmeticFunction.moebius : ArithmeticFunction Real) =
          typeI1Kernel v - typeI2Kernel u v + typeIIKernel u v + lambdaHead u +
            lambdaHead u *
              ((ArithmeticFunction.zeta : ArithmeticFunction Real) *
                (ArithmeticFunction.moebius : ArithmeticFunction Real) - 1) := by
            unfold typeI1Kernel typeI2Kernel typeIIKernel
            ring
        _ = _ := by rw [hzetaMu]; simp

/-- Explicit first Type I coefficient: a Moebius head convolved with logarithm. -/
theorem typeI1Kernel_apply (v n : Nat) :
    typeI1Kernel v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        (if pair.1 <= v then
          ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.1)
        else 0) * Real.log pair.2 := by
  unfold typeI1Kernel
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro pair hpair
  simp [moebiusHead, truncateLE, ArithmeticFunction.log_apply]

/-- Explicit second Type I coefficient, including the two truncated factors. -/
theorem typeI2Kernel_apply (u v n : Nat) :
    typeI2Kernel u v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        (∑ factors ∈ Nat.divisorsAntidiagonal pair.1,
          (if factors.1 <= u then ArithmeticFunction.vonMangoldt factors.1 else 0) *
            (if factors.2 <= v then
              ((ArithmeticFunction.moebius : ArithmeticFunction Real) factors.2)
            else 0)) *
          ((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2) := by
  unfold typeI2Kernel
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro pair hpair
  apply congrArg (fun value : Real =>
    value * ((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2))
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro factors hfactors
  simp [lambdaHead, moebiusHead, truncateLE]

theorem log_sub_lambdaHead_mul_zeta (u : Nat) :
    ArithmeticFunction.log - lambdaHead u * ArithmeticFunction.zeta =
      (ArithmeticFunction.vonMangoldt - lambdaHead u) * ArithmeticFunction.zeta := by
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
  ring

/-- Explicit Type II coefficient: the von Mangoldt tail is paired with the
Moebius tail, so this kernel enters the corrected identity with a plus sign. -/
theorem typeIIKernel_apply (u v n : Nat) :
    typeIIKernel u v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        (∑ factors ∈ Nat.divisorsAntidiagonal pair.1,
          (if factors.1 <= u then 0 else ArithmeticFunction.vonMangoldt factors.1) *
            ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2)) *
          (if pair.2 <= v then 0 else
            ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2)) := by
  rw [typeIIKernel, log_sub_lambdaHead_mul_zeta]
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hleft :
      ((ArithmeticFunction.vonMangoldt - lambdaHead u) *
          ArithmeticFunction.zeta) pair.1 =
        ∑ factors ∈ Nat.divisorsAntidiagonal pair.1,
          (if factors.1 <= u then 0 else ArithmeticFunction.vonMangoldt factors.1) *
            ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2) := by
    rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro factors hfactors
    have htail :
        (ArithmeticFunction.vonMangoldt - lambdaHead u) factors.1 =
          if factors.1 <= u then 0 else ArithmeticFunction.vonMangoldt factors.1 := by
      change ArithmeticFunction.vonMangoldt factors.1 -
        (if factors.1 <= u then ArithmeticFunction.vonMangoldt factors.1 else 0) = _
      by_cases hle : factors.1 <= u <;> simp [hle]
    rw [htail]
  have hright :
      ((ArithmeticFunction.moebius : ArithmeticFunction Real) - moebiusHead v) pair.2 =
        if pair.2 <= v then 0 else
          ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2) := by
    change ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2) -
      (if pair.2 <= v then
        ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2) else 0) = _
    by_cases hle : pair.2 <= v <;> simp [hle]
  rw [hleft, hright]

end BombieriVinogradov.VaughanIdentity
