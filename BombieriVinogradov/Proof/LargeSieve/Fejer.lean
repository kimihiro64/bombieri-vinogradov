import BombieriVinogradov.Proof.LargeSieve.Additive
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# The Fejer kernel for the additive large sieve

Vaughan's smooth-majorant proof replaces the sharp interval cutoff by a
triangular weight.  Its Fourier transform is a nonnegative multiple of the
squared norm of a finite geometric sum.  This module isolates that kernel and
its first quantitative estimates.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators ComplexConjugate

namespace BombieriVinogradov.LargeSieve

/-- The standard additive phase `exp(2 * pi * i * x)`. -/
def additivePhase (x : Real) : Complex :=
  circleMap 0 1 (2 * Real.pi * x)

@[simp]
theorem norm_additivePhase (x : Real) : ‖additivePhase x‖ = 1 := by
  simp [additivePhase]

@[simp]
theorem additivePhase_zero : additivePhase 0 = 1 := by
  simp [additivePhase, circleMap_zero]

theorem additivePhase_add (x y : Real) :
    additivePhase (x + y) = additivePhase x * additivePhase y := by
  simpa [additivePhase, mul_add] using
    (circleMap_zero_mul 1 1 (2 * Real.pi * x) (2 * Real.pi * y)).symm

theorem additivePhase_nat_mul (n : Nat) (x : Real) :
    additivePhase ((n : Real) * x) = additivePhase x ^ n := by
  rw [additivePhase, additivePhase, circleMap_zero, circleMap_zero]
  norm_num
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

@[simp]
theorem additivePhase_one : additivePhase 1 = 1 := by
  simp [additivePhase, circleMap_zero, Complex.exp_two_pi_mul_I]

@[simp]
theorem additivePhase_nat (n : Nat) : additivePhase (n : Real) = 1 := by
  calc
    additivePhase (n : Real) = additivePhase ((n : Real) * 1) := by simp
    _ = additivePhase 1 ^ n := additivePhase_nat_mul n 1
    _ = 1 := by simp

@[simp]
theorem conj_additivePhase (x : Real) :
    conj (additivePhase x) = additivePhase (-x) := by
  rw [additivePhase, additivePhase, conj_circleMap_zero]
  congr 2
  ring

/-- The finite geometric sum whose squared norm is the Fejer kernel. -/
def phaseSum (N : Nat) (x : Real) : Complex :=
  ∑ j ∈ range N, additivePhase ((j : Real) * x)

theorem conj_phaseSum (N : Nat) (x : Real) :
    conj (phaseSum N x) = phaseSum N (-x) := by
  simp [phaseSum, conj_additivePhase]

theorem phaseSum_one_sub (N : Nat) (x : Real) :
    phaseSum N (1 - x) = conj (phaseSum N x) := by
  rw [phaseSum, phaseSum]
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    additivePhase ((j : Real) * (1 - x)) =
        additivePhase ((j : Real) + (-((j : Real) * x))) := by
      congr 1
      ring
    _ = additivePhase (j : Real) * additivePhase (-((j : Real) * x)) :=
      additivePhase_add _ _
    _ = 1 * conj (additivePhase ((j : Real) * x)) := by
      rw [additivePhase_nat, conj_additivePhase]
    _ = conj (additivePhase ((j : Real) * x)) := one_mul _

@[simp]
theorem norm_phaseSum_neg (N : Nat) (x : Real) :
    ‖phaseSum N (-x)‖ = ‖phaseSum N x‖ := by
  rw [← conj_phaseSum]
  exact norm_conj _

@[simp]
theorem norm_phaseSum_one_sub (N : Nat) (x : Real) :
    ‖phaseSum N (1 - x)‖ = ‖phaseSum N x‖ := by
  rw [phaseSum_one_sub]
  exact norm_conj _

@[simp]
theorem norm_phaseSum_abs (N : Nat) (x : Real) :
    ‖phaseSum N |x|‖ = ‖phaseSum N x‖ := by
  by_cases hx : 0 <= x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), norm_phaseSum_neg]

/-- Distance from a representative in `(-1, 1)` to the nearest integer. -/
def phaseDistance (x : Real) : Real := min |x| (1 - |x|)

theorem phaseDistance_pos {x : Real} (hx0 : Ne x 0) (hx1 : |x| < 1) :
    0 < phaseDistance x := by
  rw [phaseDistance, lt_min_iff]
  exact And.intro (abs_pos.mpr hx0) (sub_pos.mpr hx1)

/-- Vaughan's normalized Fejer kernel, with the harmless value zero at `N = 0`. -/
def fejerKernel (N : Nat) (x : Real) : Real :=
  (2 / (N : Real)) * ‖phaseSum N x‖ ^ 2

theorem fejerKernel_nonneg (N : Nat) (x : Real) :
    0 <= fejerKernel N x := by
  unfold fejerKernel
  positivity

@[simp]
theorem fejerKernel_zero (x : Real) : fejerKernel 0 x = 0 := by
  simp [fejerKernel]

theorem norm_phaseSum_le (N : Nat) (x : Real) :
    ‖phaseSum N x‖ <= N := by
  calc
    ‖phaseSum N x‖ <= ∑ j ∈ range N, ‖additivePhase ((j : Real) * x)‖ :=
      norm_sum_le _ _
    _ = N := by simp

/-- The diagonal-size bound for the Fejer kernel. -/
theorem fejerKernel_le (N : Nat) (x : Real) :
    fejerKernel N x <= 2 * N := by
  by_cases hN : N = 0
  · simp [hN]
  have hNpos : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hsq : ‖phaseSum N x‖ ^ 2 <= (N : Real) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_phaseSum_le N x) 2
  calc
    fejerKernel N x <= (2 / (N : Real)) * (N : Real) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * N := by field_simp

/-- The phase sum is the usual finite geometric progression. -/
theorem phaseSum_eq_geom (N : Nat) (x : Real) :
    phaseSum N x = ∑ j ∈ range N, additivePhase x ^ j := by
  apply Finset.sum_congr rfl
  intro j hj
  exact additivePhase_nat_mul j x

/-- The exact finite geometric-series identity underlying the off-diagonal bound. -/
theorem phaseSum_mul_sub_one (N : Nat) (x : Real) :
    phaseSum N x * (additivePhase x - 1) = additivePhase x ^ N - 1 := by
  rw [phaseSum_eq_geom]
  exact geom_sum_mul (additivePhase x) N

/-- Jordan's inequality gives a linear lower bound for the phase denominator. -/
theorem norm_additivePhase_sub_one_lower {x : Real}
    (hx0 : 0 <= x) (hx : x <= 1 / 2) :
    4 * x <= ‖additivePhase x - 1‖ := by
  have hpix0 : 0 <= Real.pi * x := mul_nonneg Real.pi_pos.le hx0
  have hpix : |Real.pi * x| <= Real.pi / 2 := by
    rw [abs_of_nonneg hpix0]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hpix
  rw [abs_of_nonneg hpix0] at hsin
  rw [additivePhase, circleMap_zero]
  norm_num
  have harg : (2 : Complex) * Real.pi * x * I =
      I * ((2 * Real.pi * x : Real) : Complex) := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
  have hcancel : 2 / Real.pi * (Real.pi * x) = 2 * x := by
    field_simp [Real.pi_ne_zero]
  nlinarith [Real.pi_pos]

/-- Away from an integer, the phase sum has inverse-distance decay. -/
theorem norm_phaseSum_le_inv {N : Nat} {x : Real}
    (hx0 : 0 < x) (hx : x <= 1 / 2) :
    ‖phaseSum N x‖ <= 1 / (2 * x) := by
  have hden := norm_additivePhase_sub_one_lower hx0.le hx
  have hgeom := congrArg norm (phaseSum_mul_sub_one N x)
  rw [norm_mul] at hgeom
  have hright : ‖additivePhase x ^ N - 1‖ <= 2 := by
    calc
      ‖additivePhase x ^ N - 1‖ <=
          ‖additivePhase x ^ N‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_additivePhase]
  have hprod : ‖phaseSum N x‖ * ‖additivePhase x - 1‖ <= 2 := by
    rw [hgeom]
    exact hright
  have hscaled : ‖phaseSum N x‖ * (4 * x) <= 2 := by
    calc
      ‖phaseSum N x‖ * (4 * x) <=
          ‖phaseSum N x‖ * ‖additivePhase x - 1‖ :=
        mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ <= 2 := hprod
  have htwo : ‖phaseSum N x‖ * (2 * x) <= 1 := by
    nlinarith [norm_nonneg (phaseSum N x)]
  exact (le_div_iff₀ (mul_pos (by norm_num) hx0)).2 htwo

/-- The geometric sum decays with circular distance to the nearest integer. -/
theorem norm_phaseSum_le_phaseDistance {N : Nat} {x : Real}
    (hx0 : Ne x 0) (hx1 : |x| < 1) :
    ‖phaseSum N x‖ <= 1 / (2 * phaseDistance x) := by
  have habs0 : 0 < |x| := abs_pos.mpr hx0
  by_cases hhalf : |x| <= 1 / 2
  · have hmin : min |x| (1 - |x|) = |x| := min_eq_left (by linarith)
    calc
      ‖phaseSum N x‖ = ‖phaseSum N |x|‖ := (norm_phaseSum_abs N x).symm
      _ <= 1 / (2 * |x|) := norm_phaseSum_le_inv habs0 hhalf
      _ = 1 / (2 * phaseDistance x) := by rw [phaseDistance, hmin]
  · have hhalf' : 1 - |x| <= 1 / 2 := by linarith
    have hcomp0 : 0 < 1 - |x| := sub_pos.mpr hx1
    have hmin : min |x| (1 - |x|) = 1 - |x| := min_eq_right (by linarith)
    calc
      ‖phaseSum N x‖ = ‖phaseSum N |x|‖ := (norm_phaseSum_abs N x).symm
      _ = ‖phaseSum N (1 - |x|)‖ := (norm_phaseSum_one_sub N |x|).symm
      _ <= 1 / (2 * (1 - |x|)) := norm_phaseSum_le_inv hcomp0 hhalf'
      _ = 1 / (2 * phaseDistance x) := by rw [phaseDistance, hmin]

/-- The off-diagonal Fejer kernel has inverse-square circular decay. -/
theorem fejerKernel_le_inv_phaseDistance {N : Nat} (hN : 0 < N)
    {x : Real} (hx0 : Ne x 0) (hx1 : |x| < 1) :
    fejerKernel N x <= 1 / (2 * (N : Real) * phaseDistance x ^ 2) := by
  have hdist := phaseDistance_pos hx0 hx1
  have hnorm := norm_phaseSum_le_phaseDistance (N := N) hx0 hx1
  have hsq : ‖phaseSum N x‖ ^ 2 <= (1 / (2 * phaseDistance x)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  unfold fejerKernel
  calc
    2 / (N : Real) * ‖phaseSum N x‖ ^ 2 <=
        2 / (N : Real) * (1 / (2 * phaseDistance x)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / (2 * (N : Real) * phaseDistance x ^ 2) := by
      field_simp [Nat.ne_of_gt hN, ne_of_gt hdist]

theorem phaseDistance_rat_sub (x y : Rat) :
    phaseDistance ((x : Real) - (y : Real)) = ratCircleDistance x y := rfl

/-- The off-diagonal kernel estimate in the rational coordinates used by Farey points. -/
theorem fejerKernel_rat_sub_le {N : Nat} (hN : 0 < N)
    {x y : Rat} (hx0 : 0 <= x) (hx1 : x < 1)
    (hy0 : 0 <= y) (hy1 : y < 1) (hxy : Ne x y) :
    fejerKernel N ((x : Real) - (y : Real)) <=
      1 / (2 * (N : Real) * ratCircleDistance x y ^ 2) := by
  have hx0' : (0 : Real) <= x := by exact_mod_cast hx0
  have hx1' : (x : Real) < 1 := by exact_mod_cast hx1
  have hy0' : (0 : Real) <= y := by exact_mod_cast hy0
  have hy1' : (y : Real) < 1 := by exact_mod_cast hy1
  have hcast : Ne (x : Real) (y : Real) := by exact_mod_cast hxy
  have hsub : Ne ((x : Real) - (y : Real)) 0 := sub_ne_zero.mpr hcast
  have habs : |(x : Real) - (y : Real)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  simpa [phaseDistance_rat_sub] using
    fejerKernel_le_inv_phaseDistance hN hsub habs

end BombieriVinogradov.LargeSieve
