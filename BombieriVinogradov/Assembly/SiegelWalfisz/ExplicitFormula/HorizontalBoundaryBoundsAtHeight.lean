import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.BottomBoundaryIntegralBound
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.TopBoundaryIntegralBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.HorizontalStrip
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Two-sided horizontal-boundary bounds at one height

This module turns supplied L-function data on both signed horizontal lines
into the exact top and bottom centered integral bounds.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem centeredHorizontalBoundary_bounds_of_LFunction_data
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) {x : Nat} (hx : 2 < x)
    {T B : Real} (hT : 0 < T)
    (hTop : forall {s : Complex},
      s.im = T -> -(1 : Real) / 2 <= s.re -> s.re <= 2 ->
        And (Ne (chi.LFunction s) 0)
          (norm (logDeriv chi.LFunction s) <= B))
    (hBottom : forall {s : Complex},
      s.im = -T -> -(1 : Real) / 2 <= s.re -> s.re <= 2 ->
        And (Ne (chi.LFunction s) 0)
          (norm (logDeriv chi.LFunction s) <= B)) :
    And
      (norm (centeredExplicitFormulaTopBoundaryIntegral chi x
          ((1 : Real) / 2) (optimizedPerronLine x) T) <=
        (1 / (2 * Real.pi)) *
          (B * (4 * (x : Real) / abs T) *
            abs (optimizedPerronLine x - (-(1 : Real) / 2))))
      (norm (centeredExplicitFormulaBottomBoundaryIntegral chi x
          ((1 : Real) / 2) (optimizedPerronLine x) T) <=
        (1 / (2 * Real.pi)) *
          (B * (4 * (x : Real) / abs (-T)) *
            abs ((-(1 : Real) / 2) - optimizedPerronLine x))) := by
  have hTopPoint : forall u : Real,
      Set.uIcc (-(1 : Real) / 2) (optimizedPerronLine x) u ->
        And (Ne (chi.LFunction
          ((u : Complex) + (T : Complex) * Complex.I)) 0)
          (norm (logDeriv chi.LFunction
            ((u : Complex) + (T : Complex) * Complex.I)) <= B) := by
    intro u hu
    have huBounds := mem_optimizedHorizontalStrip_bounds hx hu
    exact hTop (by simp) (by simpa using huBounds.1)
      (by simpa using huBounds.2)
  have hBottomPoint : forall u : Real,
      Set.uIcc (optimizedPerronLine x) (-(1 : Real) / 2) u ->
        And (Ne (chi.LFunction
          ((u : Complex) + ((-T : Real) : Complex) * Complex.I)) 0)
          (norm (logDeriv chi.LFunction
            ((u : Complex) + ((-T : Real) : Complex) * Complex.I)) <= B) := by
    intro u hu
    rw [Set.uIcc_comm] at hu
    have huBounds := mem_optimizedHorizontalStrip_bounds hx hu
    exact hBottom (by simp) (by simpa using huBounds.1)
      (by simpa using huBounds.2)
  have hTopBound :
      norm (centeredExplicitFormulaTopBoundaryIntegral chi x
        ((1 : Real) / 2) (optimizedPerronLine x) T) <=
          (1 / (2 * Real.pi)) *
            (B * (4 * (x : Real) / abs T) *
              abs (optimizedPerronLine x - (-(1 : Real) / 2))) :=
    norm_centeredExplicitFormulaTopBoundaryIntegral_le
      hchi x hx hT (fun u hu => (hTopPoint u hu).1)
        (fun u hu => (hTopPoint u hu).2)
  have hBottomBound :
      norm (centeredExplicitFormulaBottomBoundaryIntegral chi x
        ((1 : Real) / 2) (optimizedPerronLine x) T) <=
          (1 / (2 * Real.pi)) *
            (B * (4 * (x : Real) / abs (-T)) *
              abs ((-(1 : Real) / 2) - optimizedPerronLine x)) :=
    norm_centeredExplicitFormulaBottomBoundaryIntegral_le
      hchi x hx hT (fun u hu => (hBottomPoint u hu).1)
        (fun u hu => (hBottomPoint u hu).2)
  exact And.intro hTopBound hBottomBound

end BombieriVinogradov.SiegelWalfisz
