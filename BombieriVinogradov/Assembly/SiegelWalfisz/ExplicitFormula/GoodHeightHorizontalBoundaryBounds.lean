import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.BottomBoundaryIntegralBound
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.TopBoundaryIntegralBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.GoodTwoSidedHeightLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.HorizontalStrip
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Centered horizontal-boundary bounds at a common good height

This module applies the common positive-and-negative horizontal-line data to
the separately verified top and bottom centered integral estimates.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_goodHeight_centeredHorizontalBoundary_bounds :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall x : Nat, 2 < x ->
              forall T : Real, 2 <= T ->
                exists Tprime : Real, And (T <= Tprime)
                  (And (Tprime <= T + 1)
                    (And
                      (norm (centeredExplicitFormulaTopBoundaryIntegral
                          chi x ((1 : Real) / 2)
                            (optimizedPerronLine x) Tprime) <=
                        (1 / (2 * Real.pi)) *
                          ((C * (zeroHeightLogScale N T) ^ 2) *
                            (4 * (x : Real) / abs Tprime) *
                              abs (optimizedPerronLine x -
                                (-(1 : Real) / 2))))
                      (norm (centeredExplicitFormulaBottomBoundaryIntegral
                          chi x ((1 : Real) / 2)
                            (optimizedPerronLine x) Tprime) <=
                        (1 / (2 * Real.pi)) *
                          ((C * (zeroHeightLogScale N T) ^ 2) *
                            (4 * (x : Real) / abs (-Tprime)) *
                              abs ((-(1 : Real) / 2) -
                                optimizedPerronLine x)))))) := by
  choose C hCPos hGood using
    exists_goodTwoSidedHeight_logDeriv_LFunction_le_sq
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive x hx T hT
  choose Tprime hTprimeLower hTprimeUpper hTop hBottom using
    hGood hN hchi hPrimitive T hT
  have hTprimePos : 0 < Tprime := by
    linarith
  have hTopPoint : forall u : Real,
      Set.uIcc (-(1 : Real) / 2) (optimizedPerronLine x) u ->
        And (Ne (chi.LFunction
          ((u : Complex) + (Tprime : Complex) * Complex.I)) 0)
          (norm (logDeriv chi.LFunction
            ((u : Complex) + (Tprime : Complex) * Complex.I)) <=
              C * (zeroHeightLogScale N T) ^ 2) := by
    intro u hu
    have huBounds := mem_optimizedHorizontalStrip_bounds hx hu
    exact hTop (by simp) (by simpa using huBounds.1)
      (by simpa using huBounds.2)
  have hBottomPoint : forall u : Real,
      Set.uIcc (optimizedPerronLine x) (-(1 : Real) / 2) u ->
        And (Ne (chi.LFunction
          ((u : Complex) + ((-Tprime : Real) : Complex) * Complex.I)) 0)
          (norm (logDeriv chi.LFunction
            ((u : Complex) + ((-Tprime : Real) : Complex) * Complex.I)) <=
              C * (zeroHeightLogScale N T) ^ 2) := by
    intro u hu
    rw [Set.uIcc_comm] at hu
    have huBounds := mem_optimizedHorizontalStrip_bounds hx hu
    exact hBottom (by simp) (by simpa using huBounds.1)
      (by simpa using huBounds.2)
  have hTopBound :=
    norm_centeredExplicitFormulaTopBoundaryIntegral_le
      hchi x hx hTprimePos
        (fun u hu => (hTopPoint u hu).1)
        (fun u hu => (hTopPoint u hu).2)
  have hBottomBound :=
    norm_centeredExplicitFormulaBottomBoundaryIntegral_le
      hchi x hx hTprimePos
        (fun u hu => (hBottomPoint u hu).1)
        (fun u hu => (hBottomPoint u hu).2)
  exact Exists.intro Tprime
    (And.intro hTprimeLower (And.intro hTprimeUpper
      (And.intro hTopBound hBottomBound)))

end BombieriVinogradov.SiegelWalfisz
