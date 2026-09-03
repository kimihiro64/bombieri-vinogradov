import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.HorizontalIntegrandTermContinuity
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.HorizontalIntegrandBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Oriented centered horizontal-integral bound

This module owns the orientation-independent integration estimate shared by
the top and bottom centered boundary segments.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem norm_explicitFormulaHorizontalIntegral_sub_one_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 2 < x)
    {a b T B : Real} (hT : 0 < abs T)
    (hRe : forall u : Real, Set.uIcc a b u ->
      u <= optimizedPerronLine x)
    (hNonzero : forall u : Real, Set.uIcc a b u ->
      Ne (chi.LFunction
        ((u : Complex) + (T : Complex) * Complex.I)) 0)
    (hLog : forall u : Real, Set.uIcc a b u ->
      norm (logDeriv chi.LFunction
        ((u : Complex) + (T : Complex) * Complex.I)) <= B) :
    norm
        (HIntegral' (explicitFormulaIntegrand chi x) a b T -
          HIntegral' (explicitFormulaIntegrand chi 1) a b T) <=
      (1 / (2 * Real.pi)) *
        (B * (4 * (x : Real) / abs T) * abs (b - a)) := by
  let path : Real -> Complex := fun u =>
    (u : Complex) + (T : Complex) * Complex.I
  let centered : Real -> Complex := fun u =>
    explicitFormulaIntegrand chi x (path u) -
      explicitFormulaIntegrand chi 1 (path u)
  let majorant : Real :=
    B * (4 * (x : Real) / abs T)
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  have hTNe : Ne T 0 := abs_pos.mp hT
  have hIntX :
      IntervalIntegrable
        (fun u : Real => explicitFormulaIntegrand chi x (path u))
        MeasureTheory.volume a b := by
    simpa [path] using
      intervalIntegrable_explicitFormulaIntegrand_horizontal
        hchi x hxPos hTNe hNonzero
  have hIntOne :
      IntervalIntegrable
        (fun u : Real => explicitFormulaIntegrand chi 1 (path u))
        MeasureTheory.volume a b := by
    simpa [path] using
      intervalIntegrable_explicitFormulaIntegrand_horizontal
        hchi 1 (by norm_num) hTNe hNonzero
  have hPointwise :
      forall u : Real, Set.uIcc a b u ->
        norm (centered u) <= majorant := by
    intro u hu
    have hsRe : (path u).re <= optimizedPerronLine x := by
      simpa [path] using hRe u hu
    have hsIm : 0 < abs (path u).im := by
      simpa [path] using hT
    simpa [centered, majorant, path] using
      norm_explicitFormulaIntegrand_sub_one_le
        chi x hx hsRe hsIm (hLog u hu)
  have hIntegralNorm :
      norm (intervalIntegral centered a b MeasureTheory.volume) <=
        majorant * abs (b - a) := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    simpa [centered] using
      hPointwise u (Set.uIoc_subset_uIcc hu)
  have hIntegralIdentity :
      HIntegral' (explicitFormulaIntegrand chi x) a b T -
          HIntegral' (explicitFormulaIntegrand chi 1) a b T =
        (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          intervalIntegral centered a b MeasureTheory.volume := by
    simp only [HIntegral', HIntegral, smul_eq_mul]
    rw [intervalIntegral.integral_sub hIntX hIntOne]
    dsimp [centered, path]
    ring_nf
  have hNormFactor :
      norm (1 / (2 * (Real.pi : Complex) * Complex.I)) =
        1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  calc
    norm
        (HIntegral' (explicitFormulaIntegrand chi x) a b T -
          HIntegral' (explicitFormulaIntegrand chi 1) a b T) =
      (1 / (2 * Real.pi)) *
        norm (intervalIntegral centered a b MeasureTheory.volume) := by
      rw [hIntegralIdentity, norm_mul, hNormFactor]
    _ <= (1 / (2 * Real.pi)) *
        (majorant * abs (b - a)) :=
      mul_le_mul_of_nonneg_left hIntegralNorm (by positivity)
    _ = (1 / (2 * Real.pi)) *
        (B * (4 * (x : Real) / abs T) * abs (b - a)) := by
      rfl

end BombieriVinogradov.SiegelWalfisz
