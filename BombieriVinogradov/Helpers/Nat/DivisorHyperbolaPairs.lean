import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Sigma.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Divisor indices as distinct positive factor pairs

The map from a modulus and its divisor to the divisor and quotient
is injective, and both factors stay inside the ambient positive interval.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem divisorSigma_pair_inj (Q : Nat) :
    Set.InjOn (fun p : Sigma (fun _ : Nat => Nat) => Prod.mk p.2 (p.1 / p.2))
      (Finset.sigma (Finset.Icc 1 Q) Nat.divisors : Set (Sigma (fun _ : Nat => Nat))) := by
  intro p hp q hq h
  have hDivisor : p.2 = q.2 := congrArg Prod.fst h
  have hQuotient : p.1 / p.2 = q.1 / q.2 := congrArg Prod.snd h
  have hpDvd := Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).2
  have hqDvd := Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hq).2
  have hLevel : p.1 = q.1 := by
    calc
      p.1 = p.2 * (p.1 / p.2) := (Nat.mul_div_cancel' hpDvd).symm
      _ = q.2 * (q.1 / q.2) := by rw [hQuotient, hDivisor]
      _ = q.1 := Nat.mul_div_cancel' hqDvd
  exact Sigma.ext hLevel (heq_of_eq hDivisor)

theorem divisorSigma_pair_mem_product {Q : Nat} (p : Sigma (fun _ : Nat => Nat))
    (hp : (Finset.sigma (Finset.Icc 1 Q) Nat.divisors :
      Set (Sigma (fun _ : Nat => Nat))) p) :
    ((Finset.Icc 1 Q).product (Finset.Icc 1 Q) : Set (Prod Nat Nat))
      (Prod.mk p.2 (p.1 / p.2)) := by
  have hData := Finset.mem_sigma.mp hp
  have hRange := Finset.mem_Icc.mp hData.1
  have hLevelPos := Nat.lt_of_lt_of_le Nat.zero_lt_one hRange.1
  have hDvd := Nat.dvd_of_mem_divisors hData.2
  have hDivisorPos := Nat.pos_of_mem_divisors hData.2
  have hDivisorLe := Nat.le_of_dvd hLevelPos hDvd
  exact Finset.mem_product.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro (Nat.succ_le_iff.mpr hDivisorPos)
      (hDivisorLe.trans hRange.2)))
    (Finset.mem_Icc.mpr (And.intro
      (Nat.succ_le_iff.mpr (Nat.div_pos hDivisorLe hDivisorPos))
      ((Nat.div_le_self p.1 p.2).trans hRange.2))))

end BombieriVinogradov
