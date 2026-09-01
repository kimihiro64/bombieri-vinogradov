import BombieriVinogradov.Proof.LargeSieve.CharacterReduction
import BombieriVinogradov.Proof.LargeSieve.Fejer
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Pólya-Vinogradov for primitive Dirichlet characters

The proof combines the exact composite-modulus primitive Gauss norm with the
inverse-distance bound for finite additive phase sums. Summing those distances
over reduced residues is controlled by a finite harmonic sum.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators ComplexConjugate

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

noncomputable local instance polyaVinogradovUnitFintype
    (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

def oneIntegerCoefficient (_ : Int) : Complex := 1

theorem norm_intervalAdditiveResidueSum_one_eq_phaseSum
    {q : Nat} [NeZero q] (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖ =
      ‖phaseSum N (unitFraction u : Real)‖ := by
  have hq : q ∈ Finset.Icc 1 q :=
    Finset.mem_Icc.mpr ⟨NeZero.pos q, le_rfl⟩
  rw [norm_intervalAdditiveResidueSum_eq_fareySample hq
    oneIntegerCoefficient M N u]
  simp [fareyAdditiveSample, shiftedIntervalCoefficients,
    oneIntegerCoefficient, phaseSum, fareyValue]

theorem unitValue_pos {q : Nat} [NeZero q] (hq : 1 < q) (u : (ZMod q)ˣ) :
    0 < u.val.val := by
  have hcoprime := unitFraction_coprime u
  have hne : Ne u.val.val 0 := by
    intro hzero
    have : q = 1 := by simpa [hzero] using hcoprime
    omega
  exact Nat.pos_of_ne_zero hne

theorem unitFraction_ne_zero {q : Nat} [NeZero q]
    (hq : 1 < q) (u : (ZMod q)ˣ) :
    Ne (unitFraction u : Real) 0 := by
  have hnum : Ne (unitFraction u).num 0 := by
    rw [unitFraction_num]
    exact_mod_cast (Nat.ne_of_gt (unitValue_pos hq u))
  have hrat : Ne (unitFraction u) 0 := Rat.num_ne_zero.mp hnum
  exact_mod_cast hrat

theorem norm_phaseSum_unitFraction_le (N : Nat) {q : Nat} [NeZero q]
    (hq : 1 < q) (u : (ZMod q)ˣ) :
    ‖phaseSum N (unitFraction u : Real)‖ <=
      ((q : Real) / 2) *
        (((u.val.val : Real))⁻¹ + ((q - u.val.val : Nat) : Real)⁻¹) := by
  have hqpos : 0 < (q : Real) := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have haposNat : 0 < u.val.val := unitValue_pos hq u
  have hapos : 0 < (u.val.val : Real) := by exact_mod_cast haposNat
  have haltNat : u.val.val < q := ZMod.val_lt u.val
  have haleNat : u.val.val <= q := haltNat.le
  have hbposNat : 0 < q - u.val.val := Nat.sub_pos_of_lt haltNat
  have hbpos : 0 < ((q - u.val.val : Nat) : Real) := by exact_mod_cast hbposNat
  have hfrac : (unitFraction u : Real) = (u.val.val : Real) / (q : Real) := by
    unfold unitFraction
    push_cast
    rfl
  have hfracPos : 0 < (unitFraction u : Real) := by rw [hfrac]; positivity
  have hfracLt : (unitFraction u : Real) < 1 := by
    rw [hfrac, div_lt_one hqpos]
    exact_mod_cast haltNat
  have hbase := norm_phaseSum_le_phaseDistance (N := N)
    hfracPos.ne' (by rw [abs_of_pos hfracPos]; exact hfracLt)
  apply hbase.trans
  rw [phaseDistance, abs_of_pos hfracPos]
  by_cases hside : (unitFraction u : Real) <= 1 - (unitFraction u : Real)
  · rw [min_eq_left hside, hfrac]
    have hidentity : 1 / (2 * ((u.val.val : Real) / (q : Real))) =
        ((q : Real) / 2) * (u.val.val : Real)⁻¹ := by
      field_simp [hqpos.ne', hapos.ne']
    rw [hidentity]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (inv_nonneg.mpr hbpos.le)) (by positivity)
  · rw [min_eq_right (le_of_not_ge hside), hfrac]
    have hcomplement : 1 - (u.val.val : Real) / (q : Real) =
        ((q - u.val.val : Nat) : Real) / (q : Real) := by
      rw [Nat.cast_sub haleNat]
      field_simp [hqpos.ne']
    rw [hcomplement]
    have hidentity : 1 / (2 * (((q - u.val.val : Nat) : Real) / (q : Real))) =
        ((q : Real) / 2) * ((q - u.val.val : Nat) : Real)⁻¹ := by
      field_simp [hqpos.ne', hbpos.ne']
    rw [hidentity]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (inv_nonneg.mpr hapos.le)) (by positivity)

def phaseReciprocalWeight (q a : Nat) : Real :=
  ((q : Real) / 2) * (((a : Real))⁻¹ + ((q - a : Nat) : Real)⁻¹)

def unitValues (q : Nat) : Finset Nat :=
  Finset.univ.image fun u : (ZMod q)ˣ => u.val.val

theorem unitValues_subset_Ico {q : Nat} [NeZero q] (hq : 1 < q) :
    unitValues q ⊆ Ico 1 q := by
  intro a ha
  rw [unitValues] at ha
  rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
  exact Finset.mem_Ico.mpr ⟨unitValue_pos hq u, ZMod.val_lt u.val⟩

theorem sum_unit_phaseReciprocalWeight_eq {q : Nat} [NeZero q] :
    ∑ u : (ZMod q)ˣ, phaseReciprocalWeight q u.val.val =
      ∑ a ∈ unitValues q, phaseReciprocalWeight q a := by
  rw [unitValues]
  symm
  apply Finset.sum_image
  intro u hu v hv huv
  apply Units.ext
  exact ZMod.val_injective q huv

theorem sum_phaseReciprocalWeight_Ico (q : Nat) (hq : 1 <= q) :
    ∑ a ∈ Ico 1 q, phaseReciprocalWeight q a =
      (q : Real) * (harmonic (q - 1) : Real) := by
  have hreflect :
      (∑ a ∈ Ico 1 q, ((q - a : Nat) : Real)⁻¹) =
        ∑ a ∈ Ico 1 q, (a : Real)⁻¹ := by
    simpa using
      (Finset.sum_Ico_reflect (fun a : Nat => (a : Real)⁻¹) 1
        (m := q) (n := q) (by omega))
  have hinterval : Ico 1 q = Icc 1 (q - 1) := by
    ext a
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hharmonic :
      (∑ a ∈ Ico 1 q, (a : Real)⁻¹) =
        (harmonic (q - 1) : Real) := by
    rw [hinterval, harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  unfold phaseReciprocalWeight
  rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  rw [hreflect, hharmonic]
  ring

theorem sum_unit_phaseSum_le_q_harmonic (M : Int) (N : Nat)
    {q : Nat} [NeZero q] (hq : 1 < q) :
    ∑ u : (ZMod q)ˣ,
        ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖ <=
      (q : Real) * (harmonic (q - 1) : Real) := by
  calc
    (∑ u : (ZMod q)ˣ,
        ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖) =
        ∑ u : (ZMod q)ˣ, ‖phaseSum N (unitFraction u : Real)‖ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact norm_intervalAdditiveResidueSum_one_eq_phaseSum M N u
    _ <= ∑ u : (ZMod q)ˣ, phaseReciprocalWeight q u.val.val := by
      apply Finset.sum_le_sum
      intro u hu
      exact norm_phaseSum_unitFraction_le N hq u
    _ = ∑ a ∈ unitValues q, phaseReciprocalWeight q a :=
      sum_unit_phaseReciprocalWeight_eq
    _ <= ∑ a ∈ Ico 1 q, phaseReciprocalWeight q a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (unitValues_subset_Ico hq)
      intro a haIco haUnits
      unfold phaseReciprocalWeight
      positivity
    _ = (q : Real) * (harmonic (q - 1) : Real) :=
      sum_phaseReciprocalWeight_Ico q hq.le

theorem harmonic_sub_one_le_two_log (q : Nat) (hq : 1 < q) :
    (harmonic (q - 1) : Real) <= 2 * Real.log (2 * (q : Real)) := by
  have hq1 : 1 <= q := hq.le
  have hsubposNat : 0 < q - 1 := Nat.sub_pos_of_lt hq
  have hsubpos : 0 < ((q - 1 : Nat) : Real) := by exact_mod_cast hsubposNat
  have hsuble : ((q - 1 : Nat) : Real) <= (q : Real) := by
    exact_mod_cast Nat.sub_le q 1
  have hlogSub : Real.log ((q - 1 : Nat) : Real) <= Real.log (q : Real) :=
    Real.log_le_log hsubpos hsuble
  have hlogq : 0 <= Real.log (q : Real) := Real.log_nonneg (by exact_mod_cast hq1)
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogProduct : Real.log (2 * (q : Real)) =
      Real.log 2 + Real.log (q : Real) := by
    rw [Real.log_mul (by norm_num : Ne (2 : Real) 0)]
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq))
  calc
    (harmonic (q - 1) : Real) <= 1 + Real.log ((q - 1 : Nat) : Real) :=
      harmonic_le_one_add_log (q - 1)
    _ <= 2 * Real.log (2 * (q : Real)) := by
      rw [hlogProduct]
      linarith

theorem sum_unit_phaseSum_le_log (M : Int) (N : Nat)
    {q : Nat} [NeZero q] (hq : 1 < q) :
    ∑ u : (ZMod q)ˣ,
        ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖ <=
      2 * (q : Real) * Real.log (2 * (q : Real)) := by
  calc
    _ <= (q : Real) * (harmonic (q - 1) : Real) :=
      sum_unit_phaseSum_le_q_harmonic M N hq
    _ <= (q : Real) * (2 * Real.log (2 * (q : Real))) := by
      exact mul_le_mul_of_nonneg_left (harmonic_sub_one_le_two_log q hq) (by positivity)
    _ = 2 * (q : Real) * Real.log (2 * (q : Real)) := by ring

theorem norm_unitCharacterSum_intervalOne_le_log (M : Int) (N : Nat)
    {q : Nat} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter Complex q) :
    ‖unitCharacterSum
        (intervalAdditiveResidueSum oneIntegerCoefficient M N q) chi‖ <=
      2 * (q : Real) * Real.log (2 * (q : Real)) := by
  unfold unitCharacterSum
  calc
    ‖∑ u : (ZMod q)ˣ,
        intervalAdditiveResidueSum oneIntegerCoefficient M N q u *
          chi (u : ZMod q)‖ <=
        ∑ u : (ZMod q)ˣ,
          ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u *
            chi (u : ZMod q)‖ := norm_sum_le _ _
    _ = ∑ u : (ZMod q)ˣ,
        ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [norm_mul, DirichletCharacter.unit_norm_eq_one, mul_one]
    _ <= _ := sum_unit_phaseSum_le_log M N hq

theorem polyaVinogradov {q : Nat} [NeZero q] (hq : 1 < q)
    {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (M : Int) (N : Nat) :
    ‖intervalCharacterSum oneIntegerCoefficient M N q chi‖ <=
      2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) := by
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  have hqnonneg : 0 <= (q : Real) := by positivity
  have hsqrtPos : 0 < Real.sqrt (q : Real) := Real.sqrt_pos.2 (by
    exact_mod_cast (lt_trans Nat.zero_lt_one hq))
  have hgauss : ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ = Real.sqrt (q : Real) := by
    have hsq := norm_gaussSum_stdAddChar_sq hchiInv
    nlinarith [Real.sq_sqrt hqnonneg, norm_nonneg (gaussSum chi⁻¹ ZMod.stdAddChar),
      Real.sqrt_nonneg (q : Real)]
  have hinversion := congrArg norm
    (gauss_mul_intervalCharacterSum hchi oneIntegerCoefficient M N)
  rw [norm_mul, hgauss] at hinversion
  have hunit := norm_unitCharacterSum_intervalOne_le_log M N hq chi⁻¹
  have hscaled :
      Real.sqrt (q : Real) *
          ‖intervalCharacterSum oneIntegerCoefficient M N q chi‖ <=
        Real.sqrt (q : Real) *
          (2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real))) := by
    calc
      _ = ‖unitCharacterSum
          (intervalAdditiveResidueSum oneIntegerCoefficient M N q) chi⁻¹‖ := hinversion
      _ <= 2 * (q : Real) * Real.log (2 * (q : Real)) := hunit
      _ = Real.sqrt (q : Real) *
          (2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real))) := by
        let L : Real := Real.log (2 * (q : Real))
        change 2 * (q : Real) * L =
          Real.sqrt (q : Real) * (2 * Real.sqrt (q : Real) * L)
        calc
          2 * (q : Real) * L =
              2 * (Real.sqrt (q : Real) * Real.sqrt (q : Real)) * L := by
            rw [Real.mul_self_sqrt hqnonneg]
          _ = _ := by ring
  exact (mul_le_mul_iff_of_pos_left hsqrtPos).mp hscaled

end BombieriVinogradov.VaughanMeanValue
