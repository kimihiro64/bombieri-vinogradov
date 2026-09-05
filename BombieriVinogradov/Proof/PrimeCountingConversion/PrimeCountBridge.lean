import BombieriVinogradov.Proof.PrimeCountingConversion.Definitions
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Nat

/-!
# Public and finite prime-count bridges

Finite filtered prime counts are identified with the public ncard and pi
definitions at the same inclusive real endpoint.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The filtered global count is Mathlib's inclusive natural prime count. -/
theorem primeGlobalNat_eq_primeCounting (N : Nat) :
    primeGlobalNat N = N.primeCounting := by
  unfold primeGlobalNat
  calc
    ((Finset.Icc 1 N).filter Nat.Prime).card = N.primesLE.card :=
      congrArg Finset.card (Nat.primesLE_eq_filter_Icc_one N).symm
    _ = N.primeCounting := Nat.primesLE_card_eq_primeCounting N

/-- The filtered progression count is the public real-cutoff ncard. -/
theorem primeProgressionNat_eq_primeCountingZMod {x : Real} (hx : 0 <= x)
    (q : Nat) (a : ZMod q) :
    primeProgressionNat (Nat.floor x) q a = Real.primeCountingZMod x q a := by
  let S : Set Nat := {n | And n.Prime (And ((n : ZMod q) = a) ((n : Real) <= x))}
  have hSubset : S <= Set.Iic (Nat.floor x) := by
    intro n hn
    exact Nat.le_floor hn.2.2
  have hFinite : S.Finite := (Set.finite_Iic (Nat.floor x)).subset hSubset
  have hSet : {n : Nat | And n.Prime
      (And ((n : ZMod q) = a) ((n : Real) <= x))} = S := by rfl
  unfold Real.primeCountingZMod
  rw [hSet, Set.ncard_eq_toFinset_card S hFinite]
  unfold primeProgressionNat
  apply congrArg Finset.card
  ext n
  rw [hFinite.mem_toFinset]
  apply Iff.intro
  case mp =>
    intro hn
    have hData := Finset.mem_filter.mp hn
    have hRange := Finset.mem_Icc.mp hData.1
    have hnCast : (n : Real) <= (Nat.floor x : Real) := Nat.cast_le.mpr hRange.2
    exact And.intro hData.2.1
      (And.intro hData.2.2 (hnCast.trans (Nat.floor_le hx)))
  case mpr =>
    intro hn
    have hUpper : n <= Nat.floor x := Nat.le_floor hn.2.2
    exact Finset.mem_filter.mpr
      (And.intro (Finset.mem_Icc.mpr (And.intro hn.1.one_le hUpper))
        (And.intro hn.1 hn.2.1))

end BombieriVinogradov.PrimeCountingConversion
