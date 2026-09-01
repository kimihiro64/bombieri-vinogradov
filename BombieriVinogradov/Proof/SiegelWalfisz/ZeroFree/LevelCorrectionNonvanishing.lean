import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionFactorNonvanishing
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Nonvanishing of the finite level-correction product

This module assembles the local right-half-plane nonvanishing theorem over the
finite set of prime divisors of the ambient character level.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem levelCorrection_ne_zero_of_re_pos {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) {s : Complex} (hs : 0 < s.re) :
    levelCorrection chi s ≠ 0 := by
  rw [levelCorrection]
  exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
    levelCorrectionFactor_ne_zero_of_re_pos chi
      (Nat.prime_of_mem_primeFactors hp) hs)

end BombieriVinogradov.SiegelWalfisz
