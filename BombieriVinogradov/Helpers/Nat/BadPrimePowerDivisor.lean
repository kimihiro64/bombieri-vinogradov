import BombieriVinogradov.Helpers.Nat.BadPrimePowerCover
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.PrimeFin

/-!
# A divisor cover for noncoprime prime powers

The complete logarithmic exponent range fits inside the divisors of
the modulus raised to that same integer cutoff.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem badPrimePower_dvd_level_pow_log
    {N n x : Nat} (hN : Ne N 0) (hn : n <= x)
    (hBad : Not (Nat.Coprime n N)) (hPrimePow : IsPrimePow n) :
    Dvd.dvd n (N ^ Nat.log 2 x) := by
  have hWitness := exists_primeFactor_pow_with_log_bound hN hn hBad hPrimePow
  let p : Nat := hWitness.choose
  let k : Nat := hWitness.choose_spec.choose
  have hData := hWitness.choose_spec.choose_spec
  have hDiv : Dvd.dvd p N := (Nat.mem_primeFactors.mp hData.1).2.1
  have hExponent : k <= Nat.log 2 x := hData.2.2.1
  have hPower : n = p ^ k := hData.2.2.2
  have hPowerDiv : Dvd.dvd (p ^ k) (N ^ Nat.log 2 x) :=
    pow_dvd_pow_of_dvd_of_le hDiv hExponent
  rw [hPower]
  exact hPowerDiv

end BombieriVinogradov
