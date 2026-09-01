import BombieriVinogradov.Assembly.VaughanMeanValue.FourierBridge
import BombieriVinogradov.Assembly.VaughanMeanValue.Hyperbola
import BombieriVinogradov.Assembly.VaughanMeanValue.PolyaVinogradov
import BombieriVinogradov.Proof.VaughanIdentity.Kernel
import Mathlib.Tactic

/-!
# Vaughan's second Type I contribution

The truncated von-Mangoldt and Möbius factors are combined into their exact
factor coefficient, bounded by `log m`, and split at the Vaughan cutoff.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity

def typeITwoKernelCoefficient (u v m : Nat) : Real :=
  ∑ factors ∈ Nat.divisorsAntidiagonal m,
    (if factors.1 <= u then ArithmeticFunction.vonMangoldt factors.1 else 0) *
      (if factors.2 <= v then
        ((ArithmeticFunction.moebius : ArithmeticFunction Real) factors.2)
      else 0)

theorem typeI2Kernel_apply_coefficients (u v n : Nat) :
    typeI2Kernel u v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        typeITwoKernelCoefficient u v pair.1 *
          ((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2) := by
  rw [typeI2Kernel_apply]
  rfl

theorem typeITwoKernelCoefficient_abs_le_log (u v m : Nat) :
    |typeITwoKernelCoefficient u v m| <= Real.log (m : Real) := by
  calc
    |typeITwoKernelCoefficient u v m| <=
        ∑ factors ∈ Nat.divisorsAntidiagonal m,
          |(if factors.1 <= u then ArithmeticFunction.vonMangoldt factors.1 else 0) *
            (if factors.2 <= v then
              ((ArithmeticFunction.moebius : ArithmeticFunction Real) factors.2)
            else 0)| := by
      unfold typeITwoKernelCoefficient
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ factors ∈ Nat.divisorsAntidiagonal m,
          ArithmeticFunction.vonMangoldt factors.1 *
            ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2) := by
      apply Finset.sum_le_sum
      intro factors hfactors
      have hright : Ne factors.2 0 :=
        Nat.right_ne_zero_of_mem_divisorsAntidiagonal hfactors
      have hlambda : 0 <= ArithmeticFunction.vonMangoldt factors.1 :=
        ArithmeticFunction.vonMangoldt_nonneg
      by_cases hleftCutoff : factors.1 <= u
      · by_cases hrightCutoff : factors.2 <= v
        · rcases ArithmeticFunction.moebius_eq_or factors.2 with hzero | hone | hneg
          · simp [hleftCutoff, hrightCutoff, hzero,
              ArithmeticFunction.zeta_apply_ne hright,
              ArithmeticFunction.vonMangoldt_nonneg]
          · simp [hleftCutoff, hrightCutoff, hone,
              ArithmeticFunction.zeta_apply_ne hright,
              abs_of_nonneg hlambda]
          · simp [hleftCutoff, hrightCutoff, hneg,
              ArithmeticFunction.zeta_apply_ne hright,
              abs_of_nonneg hlambda]
        · simp [hleftCutoff, hrightCutoff,
            ArithmeticFunction.zeta_apply_ne hright,
            ArithmeticFunction.vonMangoldt_nonneg]
      · simp [hleftCutoff, ArithmeticFunction.zeta_apply_ne hright,
          ArithmeticFunction.vonMangoldt_nonneg]
    _ = (ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction Real)) m := by
      rw [ArithmeticFunction.mul_apply]
    _ = Real.log (m : Real) := by
      rw [ArithmeticFunction.vonMangoldt_mul_zeta]
      rfl

def typeITwoCharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ Icc 1 Y, ∑ n ∈ Icc 1 (Y / m),
    (typeITwoKernelCoefficient u v m : Complex) *
      chi ((m * n : Nat) : ZMod q)

theorem vaughanS2_eq_typeITwoCharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    vaughanS2 u v Y (fun n => chi (n : ZMod q)) =
      typeITwoCharacterSum u v Y q chi := by
  unfold vaughanS2 weightedKernelSum
  simp_rw [typeI2Kernel_apply_coefficients]
  push_cast
  simp_rw [Finset.sum_mul]
  have hreindex :
      (∑ k ∈ Icc 1 Y, ∑ pair ∈ Nat.divisorsAntidiagonal k,
        (typeITwoKernelCoefficient u v pair.1 : Complex) *
          (((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2 : Real) : Complex) *
            chi (k : ZMod q)) =
        ∑ k ∈ Icc 1 Y, ∑ pair ∈ Nat.divisorsAntidiagonal k,
          (typeITwoKernelCoefficient u v pair.1 : Complex) *
            (((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2 : Real) : Complex) *
              chi ((pair.1 * pair.2 : Nat) : ZMod q) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro pair hpair
    rw [(Nat.mem_divisorsAntidiagonal.mp hpair).1]
  rw [hreindex]
  have hhyper := sum_divisorsAntidiagonal_Icc_eq_hyperbola
    (fun m n =>
      (typeITwoKernelCoefficient u v m : Complex) *
        (((ArithmeticFunction.zeta : ArithmeticFunction Real) n : Real) : Complex) *
          chi ((m * n : Nat) : ZMod q)) Y
  rw [hhyper]
  unfold typeITwoCharacterSum
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : Ne n 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  simp [ArithmeticFunction.zeta_apply_ne hn0]

theorem intervalCharacterSum_one_eq_Icc (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    intervalCharacterSum oneIntegerCoefficient 0 L q chi =
      ∑ n ∈ Icc 1 L, chi (n : ZMod q) := by
  calc
    intervalCharacterSum oneIntegerCoefficient 0 L q chi =
        positiveCharacterSum (fun _ : Nat => (1 : Complex)) L q chi := by
      rfl
    _ = ∑ n ∈ Icc 1 L, chi (n : ZMod q) := by
      rw [positiveCharacterSum_eq_sum_nat]
      simp

theorem typeITwoInnerSum_eq_prefix (u v Y m q : Nat)
    (chi : DirichletCharacter Complex q) :
    (∑ n ∈ Icc 1 (Y / m),
      (typeITwoKernelCoefficient u v m : Complex) *
        chi ((m * n : Nat) : ZMod q)) =
      (typeITwoKernelCoefficient u v m : Complex) * chi (m : ZMod q) *
        intervalCharacterSum oneIntegerCoefficient 0 (Y / m) q chi := by
  rw [intervalCharacterSum_one_eq_Icc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.cast_mul, map_mul]
  ring

def typeITwoSmallCharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ (Icc 1 Y).filter (fun m => m <= u), ∑ n ∈ Icc 1 (Y / m),
    (typeITwoKernelCoefficient u v m : Complex) *
      chi ((m * n : Nat) : ZMod q)

def typeITwoLargeCharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ (Icc 1 Y).filter (fun m => u < m), ∑ n ∈ Icc 1 (Y / m),
    (typeITwoKernelCoefficient u v m : Complex) *
      chi ((m * n : Nat) : ZMod q)

theorem typeITwoCharacterSum_eq_small_add_large (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    typeITwoCharacterSum u v Y q chi =
      typeITwoSmallCharacterSum u v Y q chi +
        typeITwoLargeCharacterSum u v Y q chi := by
  let F : Nat -> Complex := fun m =>
    ∑ n ∈ Icc 1 (Y / m),
      (typeITwoKernelCoefficient u v m : Complex) *
        chi ((m * n : Nat) : ZMod q)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Icc 1 Y) (fun m => m <= u) F
  unfold typeITwoCharacterSum typeITwoSmallCharacterSum typeITwoLargeCharacterSum
  change (∑ m ∈ Icc 1 Y, F m) =
    (∑ m ∈ (Icc 1 Y).filter (fun m => m <= u), F m) +
      ∑ m ∈ (Icc 1 Y).filter (fun m => u < m), F m
  rw [hsplit.symm]
  simp only [not_le]

theorem norm_typeITwoSmallCharacterSum_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (u v Y : Nat) :
    ‖typeITwoSmallCharacterSum u v Y q chi‖ <=
      (u : Real) *
        (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
          Real.log (2 * (q : Real))) := by
  let active : Finset Nat := (Icc 1 Y).filter fun m => m <= u
  let C : Real :=
    2 * Real.log (u : Real) * Real.sqrt (q : Real) *
      Real.log (2 * (q : Real))
  have hlogq : 0 <= Real.log (2 * (q : Real)) := by
    apply Real.log_nonneg
    have hqone : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
    linarith
  have hterm : ∀ m ∈ active,
      ‖∑ n ∈ Icc 1 (Y / m),
        (typeITwoKernelCoefficient u v m : Complex) *
          chi ((m * n : Nat) : ZMod q)‖ <= C := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hmData.1).1
    have hupos : 0 < u := lt_of_lt_of_le hmpos hmData.2
    have hlogu : 0 <= Real.log (u : Real) :=
      Real.log_nonneg (by exact_mod_cast hupos)
    have hcoeff : ‖(typeITwoKernelCoefficient u v m : Complex)‖ <=
        Real.log (u : Real) := by
      calc
        ‖(typeITwoKernelCoefficient u v m : Complex)‖ =
            |typeITwoKernelCoefficient u v m| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        _ <= Real.log (m : Real) := typeITwoKernelCoefficient_abs_le_log u v m
        _ <= Real.log (u : Real) := by
          apply Real.log_le_log
          · exact_mod_cast hmpos
          · exact_mod_cast hmData.2
    rw [typeITwoInnerSum_eq_prefix]
    calc
      ‖(typeITwoKernelCoefficient u v m : Complex) * chi (m : ZMod q) *
          intervalCharacterSum oneIntegerCoefficient 0 (Y / m) q chi‖ =
          ‖(typeITwoKernelCoefficient u v m : Complex)‖ *
            ‖chi (m : ZMod q)‖ *
              ‖intervalCharacterSum oneIntegerCoefficient 0 (Y / m) q chi‖ := by
        rw [norm_mul, norm_mul]
      _ <= Real.log (u : Real) * 1 *
          (2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real))) := by
        gcongr
        · exact DirichletCharacter.norm_le_one chi (m : ZMod q)
        · exact polyaVinogradov hq hchi 0 (Y / m)
      _ = C := by
        dsimp [C]
        ring
  have hactive : active ⊆ Icc 1 u := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hmData.1).1, hmData.2⟩
  have hcard : ((active.card : Nat) : Real) <= (u : Real) := by
    have hcardNat : active.card <= u := by
      calc
        active.card <= (Icc 1 u).card := Finset.card_le_card hactive
        _ = u := by simp
    exact_mod_cast hcardNat
  have hC : 0 <= C := by
    by_cases hu : u = 0
    · simp [C, hu]
    · dsimp [C]
      have hlogu : 0 <= Real.log (u : Real) :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hu)
      positivity
  unfold typeITwoSmallCharacterSum
  change ‖∑ m ∈ active, ∑ n ∈ Icc 1 (Y / m),
      (typeITwoKernelCoefficient u v m : Complex) *
        chi ((m * n : Nat) : ZMod q)‖ <= _
  calc
    _ <= ∑ m ∈ active, ‖∑ n ∈ Icc 1 (Y / m),
        (typeITwoKernelCoefficient u v m : Complex) *
          chi ((m * n : Nat) : ZMod q)‖ := norm_sum_le _ _
    _ <= ∑ m ∈ active, C := Finset.sum_le_sum hterm
    _ = (active.card : Real) * C := by simp
    _ <= (u : Real) * C := mul_le_mul_of_nonneg_right hcard hC
    _ = (u : Real) *
        (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
          Real.log (2 * (q : Real))) := by
      dsimp [C]

end BombieriVinogradov.VaughanMeanValue
