import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.OrientedHorizontalIntegralBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.TopBoundaryIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Centered top horizontal-boundary integral bound

This module specializes the shared oriented-horizontal estimate to the top
segment from negative one half to the optimized Perron line.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem norm_centeredExplicitFormulaTopBoundaryIntegral_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 2 < x)
    {T B : Real} (hT : 0 < T)
    (hNonzero : forall u : Real,
      Set.uIcc (-(1 : Real) / 2) (optimizedPerronLine x) u ->
        Ne (chi.LFunction
          ((u : Complex) + (T : Complex) * Complex.I)) 0)
    (hLog : forall u : Real,
      Set.uIcc (-(1 : Real) / 2) (optimizedPerronLine x) u ->
        norm (logDeriv chi.LFunction
          ((u : Complex) + (T : Complex) * Complex.I)) <= B) :
    norm (centeredExplicitFormulaTopBoundaryIntegral chi x
      ((1 : Real) / 2) (optimizedPerronLine x) T) <=
      (1 / (2 * Real.pi)) *
        (B * (4 * (x : Real) / abs T) *
          abs (optimizedPerronLine x - (-(1 : Real) / 2))) := by
  have hLineLower :
      -(1 : Real) / 2 <= optimizedPerronLine x := by
    linarith [optimizedPerronLine_gt_one hx]
  have hRe : forall u : Real,
      Set.uIcc (-(1 : Real) / 2) (optimizedPerronLine x) u ->
        u <= optimizedPerronLine x := by
    intro u hu
    have huBounds :
        Set.Icc (-(1 : Real) / 2) (optimizedPerronLine x) u := by
      simpa [Set.uIcc_of_le hLineLower] using hu
    exact huBounds.2
  have hEndpoint :
      -(1 : Real) / 2 = -((1 : Real) / 2) := by
    ring
  have hGeneric :=
    norm_explicitFormulaHorizontalIntegral_sub_one_le
      hchi x hx (abs_pos.mpr (ne_of_gt hT)) hRe hNonzero hLog
  rw [hEndpoint] at hGeneric
  rw [hEndpoint]
  simpa only [centeredExplicitFormulaTopBoundaryIntegral] using
    hGeneric

end BombieriVinogradov.SiegelWalfisz
