import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Defs

/-!
# Logarithmic coverage of noncoprime prime powers

Every prime power below x that meets the modulus uses one of its prime
factors and a positive exponent at most Nat.log 2 x.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem exists_primeFactor_pow_with_log_bound
    {N n x : Nat} (hN : Ne N 0) (hn : n <= x)
    (hBad : Not (Nat.Coprime n N)) (hPrimePow : IsPrimePow n) :
    exists p k : Nat, And ((N.primeFactors : Set Nat) p)
      (And (0 < k) (And (k <= Nat.log 2 x) (n = p ^ k))) := by
  have hWitness := (isPrimePow_nat_iff_bounded_log n).mp hPrimePow
  let k : Nat := hWitness.choose
  have hkBound : k <= Nat.log 2 n := hWitness.choose_spec.1
  have hkPos : 0 < k := hWitness.choose_spec.2.1
  have hPrimeWitness : exists p : Nat,
      And (p <= n) (And (n = p ^ k) (Nat.Prime p)) := hWitness.choose_spec.2.2
  let p : Nat := hPrimeWitness.choose
  have hPower : n = p ^ k := hPrimeWitness.choose_spec.2.1
  have hPrime : Nat.Prime p := hPrimeWitness.choose_spec.2.2
  have hDiv : Dvd.dvd p N := by
    by_cases h : Dvd.dvd p N
    case pos => exact h
    case neg =>
      have hCoprime : Nat.Coprime p N := hPrime.coprime_iff_not_dvd.mpr h
      have hPowerCoprime : Nat.Coprime (p ^ k) N := hCoprime.pow_left k
      have hNCoprime : Nat.Coprime n N := by
        rw [hPower]
        exact hPowerCoprime
      exact False.elim (hBad hNCoprime)
  have hpMem : (N.primeFactors : Set Nat) p :=
    Nat.mem_primeFactors.mpr (And.intro hPrime (And.intro hDiv hN))
  have hLogMono : Nat.log 2 n <= Nat.log 2 x := Nat.log_mono_right hn
  exact Exists.intro p (Exists.intro k
    (And.intro hpMem (And.intro hkPos (And.intro (hkBound.trans hLogMono) hPower))))

end BombieriVinogradov
