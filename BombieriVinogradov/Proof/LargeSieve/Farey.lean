import BombieriVinogradov.Proof.LargeSieve.Additive
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic

/-!
# Reduced Farey points for the additive large sieve

This module packages the reduced fractions `a / q`, with `1 <= q <= Q` and
`a` a unit modulo `q`, and proves their circular `1 / Q^2` separation.
-/

set_option autoImplicit false

namespace BombieriVinogradov.LargeSieve

/-- The reduced rational representative of a unit modulo `q`. -/
def unitFraction {q : Nat} (a : (ZMod q)ˣ) : Rat :=
  (a.val.val : Rat) / (q : Rat)

/-- A unit representative is coprime to its modulus. -/
theorem unitFraction_coprime {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    Nat.Coprime a.val.val q := by
  rw [← ZMod.isUnit_iff_coprime]
  simpa only [ZMod.natCast_zmod_val] using a.isUnit

/-- The reduced denominator of `unitFraction a` is exactly the modulus. -/
theorem unitFraction_den {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    (unitFraction a).den = q := by
  have hqInt : (0 : Int) < q := by exact_mod_cast NeZero.pos q
  have hcInt : Nat.Coprime (a.val.val : Int).natAbs (q : Int).natAbs := by
    change Nat.Coprime a.val.val q
    exact unitFraction_coprime a
  have hden : ((unitFraction a).den : Int) = (q : Int) := by
    simpa [unitFraction] using Rat.den_div_eq_of_coprime hqInt hcInt
  exact Int.ofNat_inj.mp hden

/-- The reduced numerator of `unitFraction a` is the standard unit representative. -/
theorem unitFraction_num {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    (unitFraction a).num = (a.val.val : Int) := by
  have hqInt : (0 : Int) < q := by exact_mod_cast NeZero.pos q
  have hcInt : Nat.Coprime (a.val.val : Int).natAbs (q : Int).natAbs := by
    change Nat.Coprime a.val.val q
    exact unitFraction_coprime a
  simpa [unitFraction] using Rat.num_div_eq_of_coprime hqInt hcInt

/-- The finite dependent index of reduced fractions with denominator at most `Q`. -/
abbrev FareyIndex (Q : Nat) :=
  Sigma fun q : {q : Nat // q ∈ Finset.Icc 1 Q} => (ZMod q.1)ˣ

/-- The rational value represented by a Farey index. -/
def fareyValue {Q : Nat} (i : FareyIndex Q) : Rat :=
  unitFraction i.2

theorem fareyValue_den {Q : Nat} (i : FareyIndex Q) :
    (fareyValue i).den = i.1.1 := by
  let _ : NeZero i.1.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp i.1.2).1⟩
  exact unitFraction_den i.2

theorem fareyValue_nonneg {Q : Nat} (i : FareyIndex Q) :
    0 <= fareyValue i := by
  unfold fareyValue unitFraction
  positivity

theorem fareyValue_lt_one {Q : Nat} (i : FareyIndex Q) :
    fareyValue i < 1 := by
  let _ : NeZero i.1.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp i.1.2).1⟩
  unfold fareyValue unitFraction
  rw [div_lt_one]
  · exact_mod_cast ZMod.val_lt i.2.val
  · exact_mod_cast NeZero.pos i.1.1

/-- Reduced Farey indices have unique rational values. -/
theorem fareyValue_injective (Q : Nat) :
    Function.Injective (fareyValue (Q := Q)) := by
  intro x y hxy
  have hxpos : 0 < x.1.1 := (Finset.mem_Icc.mp x.1.2).1
  have hypos : 0 < y.1.1 := (Finset.mem_Icc.mp y.1.2).1
  let _ : NeZero x.1.1 := ⟨hxpos.ne'⟩
  let _ : NeZero y.1.1 := ⟨hypos.ne'⟩
  have hq : x.1.1 = y.1.1 := by
    calc
      x.1.1 = (fareyValue x).den := (fareyValue_den x).symm
      _ = (fareyValue y).den := congrArg Rat.den hxy
      _ = y.1.1 := fareyValue_den y
  cases x with
  | mk q a =>
      cases y with
      | mk r b =>
          simp only at hq
          have hqr : q = r := Subtype.ext hq
          subst r
          have hnum : (a.val.val : Int) = (b.val.val : Int) := by
            calc
              (a.val.val : Int) = (unitFraction a).num := (unitFraction_num a).symm
              _ = (unitFraction b).num := congrArg Rat.num hxy
              _ = (b.val.val : Int) := unitFraction_num b
          have habNat : a.val.val = b.val.val := Int.ofNat_inj.mp hnum
          have habZMod : a.val = b.val := ZMod.val_injective q.1 habNat
          have hab : a = b := Units.ext habZMod
          subst b
          rfl

/-- Distinct reduced Farey points are separated by at least `1 / Q^2` on the circle. -/
theorem fareyValue_circle_separation {Q : Nat} (hQ : 0 < Q)
    {x y : FareyIndex Q} (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= ratCircleDistance (fareyValue x) (fareyValue y) := by
  apply ratCircleSeparation hQ
  · exact fareyValue_nonneg x
  · exact fareyValue_lt_one x
  · exact fareyValue_nonneg y
  · exact fareyValue_lt_one y
  · rw [fareyValue_den]
    exact (Finset.mem_Icc.mp x.1.2).2
  · rw [fareyValue_den]
    exact (Finset.mem_Icc.mp y.1.2).2
  · intro hvalue
    exact hxy (fareyValue_injective Q hvalue)

end BombieriVinogradov.LargeSieve
