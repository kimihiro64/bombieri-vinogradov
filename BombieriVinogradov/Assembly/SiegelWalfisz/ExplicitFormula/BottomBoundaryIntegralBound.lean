import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.OrientedHorizontalIntegralBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.BottomBoundaryIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Centered bottom horizontal-boundary integral bound

This module specializes the shared oriented-horizontal estimate to the
bottom segment at negative height.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem norm_centeredExplicitFormulaBottomBoundaryIntegral_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 2 < x)
    {T B : Real} (hT : 0 < T)
    (hNonzero : forall u : Real,
      Set.uIcc (optimizedPerronLine x) (-(1 : Real) / 2) u ->
        Ne (chi.LFunction
          ((u : Complex) + ((-T : Real) : Complex) * Complex.I)) 0)
    (hLog : forall u : Real,
      Set.uIcc (optimizedPerronLine x) (-(1 : Real) / 2) u ->
        norm (logDeriv chi.LFunction
          ((u : Complex) + ((-T : Real) : Complex) * Complex.I)) <= B) :
    norm (centeredExplicitFormulaBottomBoundaryIntegral chi x
      ((1 : Real) / 2) (optimizedPerronLine x) T) <=
      (1 / (2 * Real.pi)) *
        (B * (4 * (x : Real) / abs (-T)) *
          abs ((-(1 : Real) / 2) - optimizedPerronLine x)) := by
  have hLineLower :
      -(1 : Real) / 2 <= optimizedPerronLine x := by
    linarith [optimizedPerronLine_gt_one hx]
  have hRe : forall u : Real,
      Set.uIcc (optimizedPerronLine x) (-(1 : Real) / 2) u ->
        u <= optimizedPerronLine x := by
    intro u hu
    rw [Set.uIcc_comm] at hu
    have huBounds :
        Set.Icc (-(1 : Real) / 2) (optimizedPerronLine x) u := by
      simpa [Set.uIcc_of_le hLineLower] using hu
    exact huBounds.2
  have hEndpoint :
      -(1 : Real) / 2 = -((1 : Real) / 2) := by
    ring
  have hGeneric :=
    norm_explicitFormulaHorizontalIntegral_sub_one_le
      hchi x hx (by simpa using abs_pos.mpr (ne_of_gt hT))
      hRe hNonzero hLog
  rw [hEndpoint] at hGeneric
  rw [hEndpoint]
  simpa only [centeredExplicitFormulaBottomBoundaryIntegral] using
    hGeneric

end BombieriVinogradov.SiegelWalfisz
