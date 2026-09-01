import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegral
import BombieriVinogradov.Helpers.DirichletCharacter.PartialSumBigO
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Agreement with the character L-function

This module owns agreement between the Abel integral and Mathlib's character
L-function only on the absolute-convergence half-plane `1 < re s`.
-/

set_option autoImplicit false

namespace BombieriVinogradov

/-- On `1 < re s`, the Abel integral is the ordinary absolutely convergent L-series. -/
theorem characterAbelIntegral_eq_LFunction_of_one_lt_re {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    characterAbelIntegral chi s = ZMod.LFunction chi s := by
  rw [characterAbelIntegral, ZMod.LFunction_eq_LSeries chi hs]
  symm
  exact LSeries_eq_mul_integral (fun n : ℕ => chi n) (r := 0) (by positivity)
    (by linarith) (ZMod.LSeriesSummable_of_one_lt_re chi hs)
    (characterPartialSum_isBigO_rpow_zero chi hchi)

end BombieriVinogradov
