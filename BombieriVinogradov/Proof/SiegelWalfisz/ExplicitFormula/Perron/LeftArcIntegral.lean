import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.CircleValue
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.LeftArcGeometry
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RightArcIntegral

/-!
# Perron integral on the left arc

This module decomposes the full circle into the previously proved right arc
and its complementary left arc.  The Cauchy value of the full circle then
identifies the truncated Perron kernel minus its residue with the normalized
left-arc integral.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The unnormalized Perron integral along the complementary left arc. -/
def perronLeftArcIntegral (y c T : Real) : Complex :=
  intervalIntegral
    (fun theta : Real =>
      (perronLeftArc c T theta * Complex.I) *
        perronKernelIntegrand y (perronLeftArc c T theta))
    (perronRightArcAngle c T)
    (2 * Real.pi - perronRightArcAngle c T)
    MeasureTheory.volume

private lemma continuous_perron_circle_integrand
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) :
    Continuous
      (fun theta : Real =>
        (perronLeftArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronLeftArc c T theta)) := by
  have hRadius : Ne (perronRightArcRadius c T) 0 := by
    apply ne_of_gt
    dsimp [perronRightArcRadius]
    positivity
  have hEq :
      (fun theta : Real =>
        (perronLeftArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronLeftArc c T theta)) =
        fun theta : Real =>
          (perronLeftArc c T theta * Complex.I) *
            (Complex.exp
                ((Real.log y : Complex) * perronLeftArc c T theta) /
              perronLeftArc c T theta) := by
    funext theta
    rw [perronKernelIntegrand_eq_exp hy]
  rw [hEq]
  simp only [perronLeftArc]
  fun_prop (disch :=
    intro theta hzero
    have hCircleNe : Ne (circleMap 0 (perronRightArcRadius c T) theta) 0 :=
      circleMap_ne_center hRadius
    exact hCircleNe hzero)

/-- The right and left arc integrals concatenate to the full circle integral. -/
theorem perronArcIntegrals_add_eq_circleIntegral
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) :
    perronRightArcIntegral y c T + perronLeftArcIntegral y c T =
      circleIntegral (perronKernelIntegrand y) 0 (perronRightArcRadius c T) := by
  let a := perronRightArcAngle c T
  let b := 2 * Real.pi - a
  let q : Real -> Complex := fun theta =>
    (perronLeftArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronLeftArc c T theta)
  have hCont : Continuous q := by
    simpa [q] using continuous_perron_circle_integrand (T := T) hy hc
  have hPeriodic : Function.Periodic q (2 * Real.pi) := by
    intro theta
    dsimp [q, perronLeftArc]
    have hCircle := periodic_circleMap 0 (perronRightArcRadius c T) theta
    rw [hCircle]
  have hShiftBase := intervalIntegral.integral_comp_add_right
    (f := q) (a := -a) (b := 0) (2 * Real.pi)
  have hShift :
      intervalIntegral q (-a) 0 MeasureTheory.volume =
        intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
    calc
      intervalIntegral q (-a) 0 MeasureTheory.volume =
          intervalIntegral (fun theta => q (theta + 2 * Real.pi))
            (-a) 0 MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro theta _
        exact (hPeriodic theta).symm
      _ = intervalIntegral q (-a + 2 * Real.pi)
          (0 + 2 * Real.pi) MeasureTheory.volume := hShiftBase
      _ = intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
        dsimp [b]
        congr 1 <;> ring
  have hIntNegZero : IntervalIntegrable q MeasureTheory.volume (-a) 0 :=
    hCont.intervalIntegrable (-a) 0
  have hIntZeroA : IntervalIntegrable q MeasureTheory.volume 0 a :=
    hCont.intervalIntegrable 0 a
  have hIntAB : IntervalIntegrable q MeasureTheory.volume a b :=
    hCont.intervalIntegrable a b
  have hIntZeroB : IntervalIntegrable q MeasureTheory.volume 0 b :=
    hCont.intervalIntegrable 0 b
  have hIntBFull : IntervalIntegrable q MeasureTheory.volume b (2 * Real.pi) :=
    hCont.intervalIntegrable b (2 * Real.pi)
  have hRightSplit := intervalIntegral.integral_add_adjacent_intervals
    hIntNegZero hIntZeroA
  have hMiddleSplit := intervalIntegral.integral_add_adjacent_intervals
    hIntZeroA hIntAB
  have hFullSplit := intervalIntegral.integral_add_adjacent_intervals
    hIntZeroB hIntBFull
  rw [perronRightArcIntegral, perronLeftArcIntegral, circleIntegral]
  simp only [deriv_circleMap, smul_eq_mul, perronRightArc, perronLeftArc]
  change intervalIntegral q (-a) a MeasureTheory.volume +
      intervalIntegral q a b MeasureTheory.volume =
    intervalIntegral q 0 (2 * Real.pi) MeasureTheory.volume
  calc
    intervalIntegral q (-a) a MeasureTheory.volume +
        intervalIntegral q a b MeasureTheory.volume =
        (intervalIntegral q (-a) 0 MeasureTheory.volume +
          intervalIntegral q 0 a MeasureTheory.volume) +
            intervalIntegral q a b MeasureTheory.volume := by
      rw [hRightSplit]
    _ = (intervalIntegral q b (2 * Real.pi) MeasureTheory.volume +
          intervalIntegral q 0 a MeasureTheory.volume) +
            intervalIntegral q a b MeasureTheory.volume := by
      rw [hShift]
    _ = (intervalIntegral q 0 a MeasureTheory.volume +
          intervalIntegral q a b MeasureTheory.volume) +
            intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
      abel
    _ = intervalIntegral q 0 b MeasureTheory.volume +
          intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
      rw [hMiddleSplit]
    _ = intervalIntegral q 0 (2 * Real.pi) MeasureTheory.volume := hFullSplit

/-- The truncated Perron kernel minus its residue is the negative normalized
left-arc integral. -/
theorem truncatedPerronKernel_sub_one_eq_neg_leftArc
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    truncatedPerronKernel y c T - 1 =
      -(1 / (2 * Real.pi * Complex.I) : Complex) *
        perronLeftArcIntegral y c T := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hRadius : 0 < perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hRaw :
      VIntegral (perronKernelIntegrand y) c (-T) T +
          perronLeftArcIntegral y c T =
        2 * Real.pi * Complex.I := by
    calc
      VIntegral (perronKernelIntegrand y) c (-T) T +
          perronLeftArcIntegral y c T =
          perronRightArcIntegral y c T +
            perronLeftArcIntegral y c T := by
        rw [vIntegral_eq_perronRightArcIntegral hy hc hT]
      _ = circleIntegral (perronKernelIntegrand y) 0
          (perronRightArcRadius c T) :=
        perronArcIntegrals_add_eq_circleIntegral hy hc
      _ = 2 * Real.pi * Complex.I :=
        circleIntegral_perronKernelIntegrand_eq hy hRadius
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  have hNormalize : a * (2 * Real.pi * Complex.I) = 1 := by
    dsimp [a]
    field_simp [ne_of_gt Real.pi_pos, Complex.I_ne_zero]
  rw [truncatedPerronKernel, VIntegral', smul_eq_mul]
  change a * VIntegral (perronKernelIntegrand y) c (-T) T - 1 =
    -a * perronLeftArcIntegral y c T
  rw [<- hNormalize]
  linear_combination a * hRaw

end BombieriVinogradov.SiegelWalfisz
