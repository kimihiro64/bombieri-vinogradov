import BombieriVinogradov.Assembly.VaughanMeanValue.AbelLog
import BombieriVinogradov.Assembly.VaughanMeanValue.Hyperbola
import BombieriVinogradov.Proof.VaughanIdentity.Kernel
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Vaughan's first Type I contribution

The first Vaughan kernel is reindexed over its two factors. Pólya-Vinogradov
and discrete partial summation control every nontrivial modulus, while a
harmonic estimate handles the level-one contribution.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

open BombieriVinogradov.VaughanIdentity

def typeIOneCharacterSum (v y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ Icc 1 y,
    if m <= v then
      (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
        chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi
    else 0

theorem vaughanS1_eq_typeIOneCharacterSum (v y q : Nat)
    (chi : DirichletCharacter Complex q) :
    vaughanS1 v y (fun n => chi (n : ZMod q)) =
      typeIOneCharacterSum v y q chi := by
  unfold vaughanS1 weightedKernelSum
  simp_rw [typeI1Kernel_apply]
  push_cast
  simp_rw [Finset.sum_mul]
  have hreindex :
      (∑ n ∈ Icc 1 y, ∑ pair ∈ Nat.divisorsAntidiagonal n,
        (((if pair.1 <= v then
            ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.1 : Real)
          else 0) : Real) : Complex) * Complex.log (pair.2 : Complex) * chi (n : ZMod q)) =
        ∑ n ∈ Icc 1 y, ∑ pair ∈ Nat.divisorsAntidiagonal n,
          (((if pair.1 <= v then
              ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.1 : Real)
            else 0) : Real) : Complex) * Complex.log (pair.2 : Complex) *
              chi ((pair.1 * pair.2 : Nat) : ZMod q) := by
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro pair hp
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
  rw [hreindex]
  have hhyper := sum_divisorsAntidiagonal_Icc_eq_hyperbola
    (fun m k =>
      ((((if m <= v then
          ((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real)
        else 0) : Real) : Complex) * Complex.log (k : Complex) *
          chi ((m * k : Nat) : ZMod q))) y
  rw [hhyper]
  unfold typeIOneCharacterSum
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmv : m <= v
  · simp only [hmv, if_true]
    unfold logWeightedCharacterPrefix
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hchiMul : chi ((m * k : Nat) : ZMod q) =
        chi (m : ZMod q) * chi (k : ZMod q) := by
      rw [Nat.cast_mul, map_mul]
    rw [hchiMul, ← Complex.natCast_log]
    ring
  · simp [hmv]

theorem norm_realMoebius_le_one (m : Nat) :
    ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex)‖ <= 1 := by
  rcases ArithmeticFunction.moebius_eq_or m with hzero | hone | hneg
  · simp [hzero]
  · simp [hone]
  · simp [hneg]

theorem norm_typeIOneCharacterSum_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (v y : Nat) :
    ‖typeIOneCharacterSum v y q chi‖ <=
      (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((y + 1 : Nat) : Real)) := by
  let C : Real :=
    4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
      Real.log ((y + 1 : Nat) : Real)
  have hlogq : 0 <= Real.log (2 * (q : Real)) := by
    apply Real.log_nonneg
    have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
    linarith
  have hlogy : 0 <= Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 <= y + 1 by omega)
  have hfront : 0 <=
      4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) := by
    positivity
  have hC : 0 <= C := by
    dsimp [C]
    exact mul_nonneg hfront hlogy
  let active : Finset Nat := (Icc 1 y).filter fun m => m <= v
  have hrewrite : typeIOneCharacterSum v y q chi =
      ∑ m ∈ active,
        (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi := by
    unfold typeIOneCharacterSum active
    rw [Finset.sum_filter]
  have hterm : ∀ m ∈ active,
      ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ <= C := by
    intro m hm
    have hprefix : ‖logWeightedCharacterPrefix (y / m) q chi‖ <= C := by
      calc
        ‖logWeightedCharacterPrefix (y / m) q chi‖ <=
            4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
              Real.log (((y / m) + 1 : Nat) : Real) :=
          norm_logWeightedCharacterPrefix_le hq hchi (y / m)
        _ <= C := by
          dsimp [C]
          have hnat : y / m + 1 <= y + 1 :=
            Nat.add_le_add_right (Nat.div_le_self y m) 1
          have hlog : Real.log (((y / m) + 1 : Nat) : Real) <=
              Real.log ((y + 1 : Nat) : Real) := by
            apply Real.log_le_log
            · positivity
            · exact_mod_cast hnat
          exact mul_le_mul_of_nonneg_left hlog hfront
    calc
      ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ =
          ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex)‖ *
            ‖chi (m : ZMod q)‖ *
              ‖logWeightedCharacterPrefix (y / m) q chi‖ := by
        rw [norm_mul, norm_mul]
      _ <= 1 * 1 * C := by
        gcongr
        · exact norm_realMoebius_le_one m
        · exact DirichletCharacter.norm_le_one chi (m : ZMod q)
      _ = C := by ring
  have hactive : active ⊆ Icc 1 v := by
    intro m hm
    simp only [active, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1.1, hm.2⟩
  have hcardNat : active.card <= v := by
    have := Finset.card_le_card hactive
    simpa using this
  have hcard : (active.card : Real) <= (v : Real) := by exact_mod_cast hcardNat
  rw [hrewrite]
  calc
    ‖∑ m ∈ active,
        (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ <=
        ∑ m ∈ active,
          ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
            chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ :=
      norm_sum_le _ _
    _ <= ∑ m ∈ active, C := by
      exact Finset.sum_le_sum hterm
    _ = (active.card : Real) * C := by simp
    _ <= (v : Real) * C := mul_le_mul_of_nonneg_right hcard hC
    _ = (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((y + 1 : Nat) : Real)) := by rfl

theorem harmonic_le_three_log_add_one (y : Nat) :
    (harmonic y : Real) <= 3 * Real.log ((y + 1 : Nat) : Real) := by
  by_cases hy : y = 0
  · simp [hy]
  have hypos : 0 < y := Nat.pos_of_ne_zero hy
  have hlogMono : Real.log (y : Real) <=
      Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · exact_mod_cast hypos
    · exact_mod_cast (show y <= y + 1 by omega)
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogTwo : Real.log 2 <= Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast (show 2 <= y + 1 by omega)
  calc
    (harmonic y : Real) <= 1 + Real.log (y : Real) :=
      harmonic_le_one_add_log y
    _ <= 3 * Real.log ((y + 1 : Nat) : Real) := by linarith

theorem norm_typeIOneCharacterSum_trivial (v y q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖typeIOneCharacterSum v y q chi‖ <=
      3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2 := by
  let active : Finset Nat := (Icc 1 y).filter fun m => m <= v
  have hrewrite : typeIOneCharacterSum v y q chi =
      ∑ m ∈ active,
        (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi := by
    unfold typeIOneCharacterSum active
    rw [Finset.sum_filter]
  have hlogy : 0 <= Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 <= y + 1 by omega)
  have hterm : ∀ m ∈ active,
      ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ <=
        (y : Real) * (m : Real)⁻¹ * Real.log ((y + 1 : Nat) : Real) := by
    intro m hm
    have hmActive := Finset.mem_filter.mp hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hmActive.1).1
    have hprefix : ‖logWeightedCharacterPrefix (y / m) q chi‖ <=
        (y : Real) * (m : Real)⁻¹ * Real.log ((y + 1 : Nat) : Real) := by
      have hfloor : ((y / m : Nat) : Real) <= (y : Real) / (m : Real) :=
        Nat.cast_div_le
      have hnat : y / m + 1 <= y + 1 :=
        Nat.add_le_add_right (Nat.div_le_self y m) 1
      have hlog : Real.log (((y / m) + 1 : Nat) : Real) <=
          Real.log ((y + 1 : Nat) : Real) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hnat
      calc
        ‖logWeightedCharacterPrefix (y / m) q chi‖ <=
            ((y / m : Nat) : Real) *
              Real.log (((y / m) + 1 : Nat) : Real) :=
          norm_logWeightedCharacterPrefix_trivial (y / m) q chi
        _ <= ((y : Real) / (m : Real)) *
              Real.log (((y / m) + 1 : Nat) : Real) :=
          mul_le_mul_of_nonneg_right hfloor (Real.log_natCast_nonneg _)
        _ <= ((y : Real) / (m : Real)) *
              Real.log ((y + 1 : Nat) : Real) := by
          exact mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = (y : Real) * (m : Real)⁻¹ *
              Real.log ((y + 1 : Nat) : Real) := by
          rw [div_eq_mul_inv]
    calc
      ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ =
          ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex)‖ *
            ‖chi (m : ZMod q)‖ *
              ‖logWeightedCharacterPrefix (y / m) q chi‖ := by
        rw [norm_mul, norm_mul]
      _ <= 1 * 1 *
          ((y : Real) * (m : Real)⁻¹ * Real.log ((y + 1 : Nat) : Real)) := by
        gcongr
        · exact norm_realMoebius_le_one m
        · exact DirichletCharacter.norm_le_one chi (m : ZMod q)
      _ = (y : Real) * (m : Real)⁻¹ *
          Real.log ((y + 1 : Nat) : Real) := by ring
  have hactive : active ⊆ Icc 1 y := by
    exact fun m hm => (Finset.mem_filter.mp hm).1
  have hharmonic :
      ∑ m ∈ Icc 1 y, (m : Real)⁻¹ = (harmonic y : Real) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hrewrite]
  calc
    ‖∑ m ∈ active,
        (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ <=
        ∑ m ∈ active,
          ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
            chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ :=
      norm_sum_le _ _
    _ <= ∑ m ∈ active,
        (y : Real) * (m : Real)⁻¹ *
          Real.log ((y + 1 : Nat) : Real) := Finset.sum_le_sum hterm
    _ <= ∑ m ∈ Icc 1 y,
        (y : Real) * (m : Real)⁻¹ *
          Real.log ((y + 1 : Nat) : Real) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hactive
      intro m hmAll hmActive
      positivity
    _ = (y : Real) * (harmonic y : Real) *
        Real.log ((y + 1 : Nat) : Real) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_mul, hharmonic]
    _ <= (y : Real) *
        (3 * Real.log ((y + 1 : Nat) : Real)) *
          Real.log ((y + 1 : Nat) : Real) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (harmonic_le_three_log_add_one y) (by positivity)) hlogy
    _ = 3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2 := by ring

theorem primitiveCharacters_card_le_totient (q : Nat) [NeZero q] :
    (primitiveCharacters q).card <= q.totient := by
  calc
    (primitiveCharacters q).card <=
        (Finset.univ : Finset (DirichletCharacter Complex q)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = q.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity Complex q

theorem weighted_primitive_typeIOne_le {q : Nat} [NeZero q]
    (hq : 1 < q) (v y : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
      (q : Real) * (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((y + 1 : Nat) : Real)) := by
  classical
  let B : Real := (v : Real) *
    (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
      Real.log ((y + 1 : Nat) : Real))
  have hB : 0 <= B := by
    dsimp [B]
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
      linarith
    have hlogy : 0 <= Real.log ((y + 1 : Nat) : Real) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 <= y + 1 by omega)
    positivity
  have hchars :
      ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
        (q.totient : Real) * B := by
    calc
      ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
          ∑ chi ∈ primitiveCharacters q, B := by
        apply Finset.sum_le_sum
        intro chi hchiMem
        have hchi : DirichletCharacter.IsPrimitive chi := by
          simpa [primitiveCharacters] using (Finset.mem_filter.mp hchiMem).2
        rw [vaughanS1_eq_typeIOneCharacterSum]
        exact norm_typeIOneCharacterSum_le hq hchi v y
      _ = ((primitiveCharacters q).card : Real) * B := by simp
      _ <= (q.totient : Real) * B := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast primitiveCharacters_card_le_totient q) hB
  have hphi : 0 < (q.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  calc
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
        ((q : Real) / (q.totient : Real)) *
          ((q.totient : Real) * B) := by
      exact mul_le_mul_of_nonneg_left hchars (by positivity)
    _ = (q : Real) * B := by field_simp
    _ = (q : Real) * (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((y + 1 : Nat) : Real)) := by
      dsimp [B]
      ring

def nontrivialTypeIOneMean (v y Q : Nat) : Real :=
  ∑ q ∈ Icc 2 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖

theorem nontrivialTypeIOneMean_le (v y Q : Nat) :
    nontrivialTypeIOneMean v y Q <=
      4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
        Real.log (2 * (Q : Real)) * Real.log ((y + 1 : Nat) : Real) := by
  let D : Real := (Q : Real) * (v : Real) *
    (4 * Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) *
      Real.log ((y + 1 : Nat) : Real))
  have hlogQ : 0 <= Real.log (2 * (Q : Real)) := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · apply Real.log_nonneg
      have : (1 : Real) <= (Q : Real) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
      linarith
  have hlogy : 0 <= Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 <= y + 1 by omega)
  have hD : 0 <= D := by
    dsimp [D]
    positivity
  have hterm : ∀ q ∈ Icc 2 Q,
      ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <= D := by
    intro q hqMem
    have hqBounds := Finset.mem_Icc.mp hqMem
    let _ : NeZero q := ⟨(Nat.zero_lt_of_lt hqBounds.1).ne'⟩
    have hbase := weighted_primitive_typeIOne_le
      (show 1 < q by omega) v y
    apply hbase.trans
    dsimp [D]
    have hqcast : (q : Real) <= (Q : Real) := by exact_mod_cast hqBounds.2
    have hsqrt : Real.sqrt (q : Real) <= Real.sqrt (Q : Real) :=
      Real.sqrt_le_sqrt hqcast
    have hlog : Real.log (2 * (q : Real)) <=
        Real.log (2 * (Q : Real)) := by
      apply Real.log_le_log
      · have : (0 : Real) < (q : Real) := by exact_mod_cast NeZero.pos q
        positivity
      · nlinarith
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have hqone : 1 <= q := by omega
      have : (1 : Real) <= (q : Real) := by exact_mod_cast hqone
      linarith
    gcongr
  unfold nontrivialTypeIOneMean
  calc
    ∑ q ∈ Icc 2 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
        ∑ q ∈ Icc 2 Q, D := by
      exact Finset.sum_le_sum hterm
    _ = ((Icc 2 Q).card : Real) * D := by simp
    _ <= (Q : Real) * D := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact_mod_cast (show (Icc 2 Q).card <= Q by simp)
    _ = 4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
        Real.log (2 * (Q : Real)) * Real.log ((y + 1 : Nat) : Real) := by
      dsimp [D]
      ring

def typeIOneMean (v y Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖

theorem levelOne_typeIOne_le (v y : Nat) :
    (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
        ∑ chi ∈ primitiveCharacters 1,
          ‖vaughanS1 v y (fun n => chi (n : ZMod 1))‖ <=
      3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2 := by
  let B : Real := 3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2
  have hB : 0 <= B := by
    dsimp [B]
    positivity
  have hsum :
      ∑ chi ∈ primitiveCharacters 1,
          ‖vaughanS1 v y (fun n => chi (n : ZMod 1))‖ <= B := by
    calc
      ∑ chi ∈ primitiveCharacters 1,
          ‖vaughanS1 v y (fun n => chi (n : ZMod 1))‖ <=
          ∑ chi ∈ primitiveCharacters 1, B := by
        apply Finset.sum_le_sum
        intro chi hchi
        rw [vaughanS1_eq_typeIOneCharacterSum]
        exact norm_typeIOneCharacterSum_trivial v y 1 chi
      _ = ((primitiveCharacters 1).card : Real) * B := by simp
      _ <= B := by
        have hcard : ((primitiveCharacters 1).card : Real) <= 1 := by
          exact_mod_cast primitiveCharacters_card_le_totient 1
        nlinarith
  norm_num
  simpa [B, Nat.cast_add, Nat.cast_one] using hsum

theorem typeIOneMean_le (v y Q : Nat) (hQ : 1 <= Q) :
    typeIOneMean v y Q <=
      3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2 +
        4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
          Real.log (2 * (Q : Real)) * Real.log ((y + 1 : Nat) : Real) := by
  have hsplit : typeIOneMean v y Q =
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1,
            ‖vaughanS1 v y (fun n => chi (n : ZMod 1))‖ +
        nontrivialTypeIOneMean v y Q := by
    unfold typeIOneMean nontrivialTypeIOneMean
    rw [← Finset.insert_Icc_succ_left_eq_Icc hQ]
    rw [Finset.sum_insert (by simp)]
    simp
  rw [hsplit]
  exact add_le_add (levelOne_typeIOne_le v y)
    (nontrivialTypeIOneMean_le v y Q)

end BombieriVinogradov.VaughanMeanValue
