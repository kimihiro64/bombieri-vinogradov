import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RightArcGeometry
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Perron integral on the right arc

This module uses a primitive on the convex right half-plane to identify the
Perron vertical integral with the integral along the circular arc that has the
same endpoints.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The unnormalized Perron integral along the right circular arc. -/
def perronRightArcIntegral (y c T : Real) : Complex :=
  intervalIntegral
    (fun theta : Real =>
      (perronRightArc c T theta * Complex.I) *
        perronKernelIntegrand y (perronRightArc c T theta))
    (-perronRightArcAngle c T) (perronRightArcAngle c T)
    MeasureTheory.volume

private lemma continuous_perron_vertical_derivative
    {y c : Real} (hy : 0 < y) (hc : 0 < c) :
    Continuous
      (fun t : Real =>
        Complex.I * perronKernelIntegrand y
          ((c : Complex) + (t : Complex) * Complex.I)) := by
  have hEq :
      (fun t : Real =>
        Complex.I * perronKernelIntegrand y
          ((c : Complex) + (t : Complex) * Complex.I)) =
        fun t : Real => Complex.I *
          (Complex.exp
              ((Real.log y : Complex) *
                ((c : Complex) + (t : Complex) * Complex.I)) /
            ((c : Complex) + (t : Complex) * Complex.I)) := by
    funext t
    rw [perronKernelIntegrand_eq_exp hy]
  rw [hEq]
  fun_prop (disch :=
    intro t hzero
    have hReal := congrArg Complex.re hzero
    simp at hReal
    exact hc.ne' hReal)

private lemma continuous_perron_arc_derivative
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) :
    Continuous
      (fun theta : Real =>
        (perronRightArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronRightArc c T theta)) := by
  have hRadius : Ne (perronRightArcRadius c T) 0 := by
    apply ne_of_gt
    dsimp [perronRightArcRadius]
    positivity
  have hEq :
      (fun theta : Real =>
        (perronRightArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronRightArc c T theta)) =
        fun theta : Real =>
          (perronRightArc c T theta * Complex.I) *
            (Complex.exp
                ((Real.log y : Complex) * perronRightArc c T theta) /
              perronRightArc c T theta) := by
    funext theta
    rw [perronKernelIntegrand_eq_exp hy]
  rw [hEq]
  simp only [perronRightArc]
  fun_prop (disch :=
    intro theta hzero
    have hCircleNe : Ne (circleMap 0 (perronRightArcRadius c T) theta) 0 :=
      circleMap_ne_center hRadius
    exact hCircleNe (by simpa [perronRightArc] using hzero))

/-- The vertical Perron integral equals the integral along the right arc. -/
theorem vIntegral_eq_perronRightArcIntegral
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    VIntegral (perronKernelIntegrand y) c (-T) T =
      perronRightArcIntegral y c T := by
  let S : Set Complex := {z : Complex | 0 < z.re}
  have hConvex : Convex Real S := by
    simpa [S] using convex_halfSpace_re_gt (0 : Real)
  have hOpen : IsOpen S := by
    dsimp [S]
    exact isOpen_lt continuous_const Complex.continuous_re
  choose F hF using hConvex.exists_forall_hasDerivWithinAt
    (holomorphicOn_perronKernelIntegrand hy)
  let vertical : Real -> Complex :=
    fun t => (c : Complex) + (t : Complex) * Complex.I
  have hVerticalMem (t : Real) : S (vertical t) := by
    change 0 < (vertical t).re
    simp [vertical, hc]
  have hVerticalDeriv (t : Real) :
      HasDerivAt (Function.comp F vertical)
        (Complex.I * perronKernelIntegrand y (vertical t)) t := by
    have hFAt := (hF (vertical t) (hVerticalMem t)).hasDerivAt
      (hOpen.mem_nhds (hVerticalMem t))
    have hPath : HasDerivAt vertical Complex.I t := by
      simpa [vertical] using
        (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add
          (c : Complex))
    simpa [smul_eq_mul, mul_comm] using hFAt.scomp t hPath
  have hVerticalFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -T) (b := T)
    (f := Function.comp F vertical)
    (f' := fun t : Real =>
      Complex.I * perronKernelIntegrand y (vertical t))
    (fun t _ => hVerticalDeriv t)
    (by
      simpa [vertical] using
        (continuous_perron_vertical_derivative hy hc).intervalIntegrable (-T) T)
  have hArcMem (theta : Real)
      (htheta : Set.uIcc (-perronRightArcAngle c T)
        (perronRightArcAngle c T) theta) :
      S (perronRightArc c T theta) := by
    change 0 < (perronRightArc c T theta).re
    exact hc.trans_le (perronRightArc_re_ge hc hT htheta)
  have hArcDeriv (theta : Real)
      (htheta : Set.uIcc (-perronRightArcAngle c T)
        (perronRightArcAngle c T) theta) :
      HasDerivAt (Function.comp F (perronRightArc c T))
        ((perronRightArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronRightArc c T theta)) theta := by
    have hFAt := (hF (perronRightArc c T theta) (hArcMem theta htheta)).hasDerivAt
      (hOpen.mem_nhds (hArcMem theta htheta))
    have hPath : HasDerivAt (perronRightArc c T)
        (perronRightArc c T theta * Complex.I) theta := by
      change HasDerivAt (circleMap 0 (perronRightArcRadius c T))
        (circleMap 0 (perronRightArcRadius c T) theta * Complex.I) theta
      exact hasDerivAt_circleMap 0 (perronRightArcRadius c T) theta
    simpa [smul_eq_mul] using hFAt.scomp theta hPath
  have hArcFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -perronRightArcAngle c T) (b := perronRightArcAngle c T)
    (f := Function.comp F (perronRightArc c T))
    (f' := fun theta : Real =>
      (perronRightArc c T theta * Complex.I) *
        perronKernelIntegrand y (perronRightArc c T theta))
    hArcDeriv
    (by
      exact (continuous_perron_arc_derivative (T := T) hy hc).intervalIntegrable
        (-perronRightArcAngle c T) (perronRightArcAngle c T))
  rw [VIntegral, smul_eq_mul]
  have hVerticalValue :
      Complex.I * intervalIntegral
        (fun t : Real => perronKernelIntegrand y
          ((c : Complex) + (t : Complex) * Complex.I))
        (-T) T MeasureTheory.volume =
        Function.comp F vertical T - Function.comp F vertical (-T) := by
    rw [<- intervalIntegral.integral_const_mul]
    simpa [vertical] using hVerticalFTC
  rw [hVerticalValue]
  rw [perronRightArcIntegral, hArcFTC]
  simp only [Function.comp_apply, vertical]
  rw [perronRightArc_angle hc, perronRightArc_neg_angle hc]
  have hLower :
      (c : Complex) + ((-T : Real) : Complex) * Complex.I =
        (c : Complex) - (T : Complex) * Complex.I := by
    push_cast
    ring
  rw [hLower]

end BombieriVinogradov.SiegelWalfisz
