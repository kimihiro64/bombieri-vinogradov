import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.LeftIntegrandTermContinuity
import Mathlib.Tactic.NormNum

/-!
# Continuity of the centered left-line integrand

This module derives centered continuity and finite-interval integrability from
the separately owned individual-term continuity theorem.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem continuous_centered_explicitFormulaIntegrand_left_line
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 1 <= x) :
    Continuous (fun t : Real =>
      explicitFormulaIntegrand chi x
          (((-(1 : Real) / 2 : Real) : Complex) +
            (t : Complex) * Complex.I) -
        explicitFormulaIntegrand chi 1
          (((-(1 : Real) / 2 : Real) : Complex) +
            (t : Complex) * Complex.I)) := by
  have hxPos : 0 < x := Nat.zero_lt_of_lt hx
  change Continuous
    ((fun t : Real =>
        explicitFormulaIntegrand chi x
          (((-(1 : Real) / 2 : Real) : Complex) +
            (t : Complex) * Complex.I)) -
      (fun t : Real =>
        explicitFormulaIntegrand chi 1
          (((-(1 : Real) / 2 : Real) : Complex) +
            (t : Complex) * Complex.I)))
  exact
    (continuous_explicitFormulaIntegrand_left_line
      hchi hPrimitive x hxPos).sub
    (continuous_explicitFormulaIntegrand_left_line
      hchi hPrimitive 1 (by norm_num))

theorem intervalIntegrable_centered_explicitFormulaIntegrand_left_line
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 1 <= x) (T : Real) :
    IntervalIntegrable
      (fun t : Real =>
        explicitFormulaIntegrand chi x
            (((-(1 : Real) / 2 : Real) : Complex) +
              (t : Complex) * Complex.I) -
          explicitFormulaIntegrand chi 1
            (((-(1 : Real) / 2 : Real) : Complex) +
              (t : Complex) * Complex.I))
      MeasureTheory.volume (-T) T :=
  (continuous_centered_explicitFormulaIntegrand_left_line
    hchi hPrimitive x hx).intervalIntegrable _ _

end BombieriVinogradov.SiegelWalfisz
