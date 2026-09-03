import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Complex.Basic

/-!
# Retained-zero reflection
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem isRetainedZero_one_sub_conj
    {c : Real} {N : Nat} [NeZero N]
    {chi : DirichletCharacter Complex N}
    {exceptional : Option Complex}
    (hChoice : IsExceptionalZeroChoice c chi exceptional)
    {rho : Complex} (hRetained : IsRetainedZero exceptional rho) :
    IsRetainedZero exceptional
      (1 - (starRingEnd Complex) rho) := by
  cases exceptional
  case none =>
    trivial
  case some beta =>
    change IsExceptionalZero c chi beta at hChoice
    change And (Ne rho beta) (Ne rho (1 - beta)) at hRetained
    change And
      (Ne (1 - (starRingEnd Complex) rho) beta)
      (Ne (1 - (starRingEnd Complex) rho) (1 - beta))
    have hBetaConj : (starRingEnd Complex) beta = beta := by
      apply Complex.ext <;> simp [hChoice.2.1]
    have hBetaReflect :
        1 - (starRingEnd Complex) beta = 1 - beta := by
      rw [hBetaConj]
    have hReflectInvolutive (z : Complex) :
        1 - (starRingEnd Complex)
            (1 - (starRingEnd Complex) z) = z := by
      simp only [map_sub, map_one, Complex.conj_conj,
        sub_sub_cancel]
    have hFirst :
        Ne (1 - (starRingEnd Complex) rho) beta := by
      intro hEq
      apply hRetained.2
      calc
        rho = 1 - (starRingEnd Complex)
            (1 - (starRingEnd Complex) rho) :=
          (hReflectInvolutive rho).symm
        _ = 1 - (starRingEnd Complex) beta := by rw [hEq]
        _ = 1 - beta := hBetaReflect
    have hSecond :
        Ne (1 - (starRingEnd Complex) rho) (1 - beta) := by
      intro hEq
      apply hRetained.1
      have hReflectedEq :
          1 - (starRingEnd Complex) rho =
            1 - (starRingEnd Complex) beta :=
        hEq.trans hBetaReflect.symm
      calc
        rho = 1 - (starRingEnd Complex)
            (1 - (starRingEnd Complex) rho) :=
          (hReflectInvolutive rho).symm
        _ = 1 - (starRingEnd Complex)
            (1 - (starRingEnd Complex) beta) := by
          rw [hReflectedEq]
        _ = beta := hReflectInvolutive beta
    exact And.intro hFirst hSecond

end BombieriVinogradov.SiegelWalfisz
