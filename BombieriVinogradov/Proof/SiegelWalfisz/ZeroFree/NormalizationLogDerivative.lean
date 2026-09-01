import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Logarithmic derivative of the modulus normalization

This module computes the logarithmic derivative of the `N ^ (s / 2)` factor in the
symmetric completed Dirichlet L-function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_symmetricNormalization
    {N : Nat} [NeZero N] (s : Complex) :
    logDeriv (fun z : Complex => (N : Complex) ^ (z / 2)) s =
      (Real.log N : Complex) / 2 := by
  have hN : (N : Complex) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  rw [logDeriv_apply,
    Complex.deriv_const_cpow (f := fun z : Complex => z / 2) (by fun_prop)]
  simp [hN, Complex.natCast_log]
  ring

end BombieriVinogradov.SiegelWalfisz
