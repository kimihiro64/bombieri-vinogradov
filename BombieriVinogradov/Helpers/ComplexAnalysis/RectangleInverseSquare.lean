import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Rectangle integrals of inverse squares

This module proves that `c / s ^ 2` has zero normalized integral around any
rectangle whose border avoids the origin. The proof uses explicit
antiderivatives on the horizontal and vertical edges.
-/

set_option autoImplicit false

noncomputable section

open scoped Interval

namespace BombieriVinogradov.ComplexAnalysis

private lemma horizontalAntiderivative_hasDerivAt
    (c : Complex) (y t : Real)
    (hne : Ne ((t : Complex) + (y : Complex) * Complex.I) 0) :
    HasDerivAt
      (fun r : Real =>
        (-c) * Inv.inv ((r : Complex) + (y : Complex) * Complex.I))
      (c / ((t : Complex) + (y : Complex) * Complex.I) ^ 2) t := by
  have hpath : HasDerivAt
      (fun r : Real => (r : Complex) + (y : Complex) * Complex.I) 1 t := by
    simpa using
      (Complex.ofRealCLM.hasDerivAt (x := t)).add_const
        ((y : Complex) * Complex.I)
  simpa [div_eq_mul_inv] using
    HasDerivAt.const_mul (-c) (hpath.inv hne)

private lemma horizontalIntegral_div_sq
    (c : Complex) (a b y : Real)
    (hne : forall t, Set.uIcc a b t ->
      Ne ((t : Complex) + (y : Complex) * Complex.I) 0) :
    HIntegral (fun s : Complex => c / s ^ 2) a b y =
      -c / ((b : Complex) + (y : Complex) * Complex.I) -
        (-c / ((a : Complex) + (y : Complex) * Complex.I)) := by
  have hpath_cont : Continuous
      (fun t : Real => (t : Complex) + (y : Complex) * Complex.I) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun t : Real => c / ((t : Complex) + (y : Complex) * Complex.I) ^ 2)
      MeasureTheory.volume a b :=
    (continuousOn_const.div (hpath_cont.continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (hne t ht))).intervalIntegrable
  unfold HIntegral
  simpa [div_eq_mul_inv] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : Real =>
        (-c) * Inv.inv ((t : Complex) + (y : Complex) * Complex.I))
      (fun t ht => horizontalAntiderivative_hasDerivAt c y t (hne t ht)) hint

private lemma verticalAntiderivative_hasDerivAt
    (c : Complex) (x t : Real)
    (hne : Ne ((x : Complex) + (t : Complex) * Complex.I) 0) :
    HasDerivAt
      (fun r : Real =>
        (Complex.I * c) *
          Inv.inv ((x : Complex) + (r : Complex) * Complex.I))
      (c / ((x : Complex) + (t : Complex) * Complex.I) ^ 2) t := by
  have hpath : HasDerivAt
      (fun r : Real => (x : Complex) + (r : Complex) * Complex.I)
      Complex.I t := by
    simpa using
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add
        (x : Complex)
  have hcoef :
      (Complex.I * c) *
          (-Complex.I / ((x : Complex) + (t : Complex) * Complex.I) ^ 2) =
        c / ((x : Complex) + (t : Complex) * Complex.I) ^ 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      Complex.I * c *
          (-Complex.I *
            Inv.inv (((x : Complex) + (t : Complex) * Complex.I) ^ 2)) =
        -(Complex.I * Complex.I) * c *
          Inv.inv (((x : Complex) + (t : Complex) * Complex.I) ^ 2) := by
            ring
      _ = c * Inv.inv (((x : Complex) + (t : Complex) * Complex.I) ^ 2) := by
        rw [Complex.I_mul_I]
        ring
  simpa using
    (HasDerivAt.const_mul (Complex.I * c) (hpath.inv hne)).congr_deriv hcoef

private lemma verticalIntegral_div_sq
    (c : Complex) (x a b : Real)
    (hne : forall t, Set.uIcc a b t ->
      Ne ((x : Complex) + (t : Complex) * Complex.I) 0) :
    VIntegral (fun s : Complex => c / s ^ 2) x a b =
      -c / ((x : Complex) + (b : Complex) * Complex.I) -
        (-c / ((x : Complex) + (a : Complex) * Complex.I)) := by
  have hpath_cont : Continuous
      (fun t : Real => (x : Complex) + (t : Complex) * Complex.I) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun t : Real => c / ((x : Complex) + (t : Complex) * Complex.I) ^ 2)
      MeasureTheory.volume a b :=
    (continuousOn_const.div (hpath_cont.continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (hne t ht))).intervalIntegrable
  have hftc :
      intervalIntegral (fun t : Real =>
        c / ((x : Complex) + (t : Complex) * Complex.I) ^ 2) a b
        MeasureTheory.volume =
        (Complex.I * c) *
            Inv.inv ((x : Complex) + (b : Complex) * Complex.I) -
          (Complex.I * c) *
            Inv.inv ((x : Complex) + (a : Complex) * Complex.I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : Real =>
        (Complex.I * c) *
          Inv.inv ((x : Complex) + (t : Complex) * Complex.I))
      (fun t ht => verticalAntiderivative_hasDerivAt c x t (hne t ht)) hint
  unfold VIntegral
  rw [hftc]
  simp only [smul_eq_mul]
  have hI : forall u : Complex,
      Complex.I * (Complex.I * u) = -u := by
    intro u
    calc
      Complex.I * (Complex.I * u) =
          (Complex.I * Complex.I) * u :=
        (mul_assoc Complex.I Complex.I u).symm
      _ = -u := by
        rw [Complex.I_mul_I]
        ring
  have hII : forall u v : Complex,
      Complex.I * (Complex.I * u * v) = -(u * v) := by
    intro u v
    calc
      Complex.I * (Complex.I * u * v) =
          Complex.I * (Complex.I * (u * v)) := by
        ring
      _ = -(u * v) := hI (u * v)
  rw [mul_sub, hII, hII]
  simp [div_eq_mul_inv]

/-- The normalized rectangle integral of `c / s ^ 2` vanishes when the
rectangle border avoids the origin. -/
theorem rectangleIntegral'_div_sq_eq_zero
    (c z w : Complex)
    (hzero : Not (Membership.mem (RectangleBorder z w) 0)) :
    RectangleIntegral' (fun s : Complex => c / s ^ 2) z w = 0 := by
  have hbottom : forall t, Set.uIcc z.re w.re t ->
      Ne ((t : Complex) + (z.im : Complex) * Complex.I) 0 := by
    intro t ht heq
    apply hzero
    simpa [heq] using mapsTo_rectangleBorder_left_im z w ht
  have htop : forall t, Set.uIcc z.re w.re t ->
      Ne ((t : Complex) + (w.im : Complex) * Complex.I) 0 := by
    intro t ht heq
    apply hzero
    simpa [heq] using mapsTo_rectangleBorder_right_im z w ht
  have hright : forall t, Set.uIcc z.im w.im t ->
      Ne ((w.re : Complex) + (t : Complex) * Complex.I) 0 := by
    intro t ht heq
    apply hzero
    simpa [heq] using mapsTo_rectangleBorder_right_re z w ht
  have hleft : forall t, Set.uIcc z.im w.im t ->
      Ne ((z.re : Complex) + (t : Complex) * Complex.I) 0 := by
    intro t ht heq
    apply hzero
    simpa [heq] using mapsTo_rectangleBorder_left_re z w ht
  rw [RectangleIntegral', RectangleIntegral,
    horizontalIntegral_div_sq c z.re w.re z.im hbottom,
    horizontalIntegral_div_sq c z.re w.re w.im htop,
    verticalIntegral_div_sq c w.re z.im w.im hright,
    verticalIntegral_div_sq c z.re z.im w.im hleft]
  simp only [smul_eq_mul]
  ring

end BombieriVinogradov.ComplexAnalysis
