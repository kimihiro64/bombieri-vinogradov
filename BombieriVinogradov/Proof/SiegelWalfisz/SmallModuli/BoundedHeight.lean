import BombieriVinogradov.Helpers.DirichletCharacter.ElementaryChebyshev
import BombieriVinogradov.Helpers.RealAnalysis.PolynomialExponentialWindow
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Character Chebyshev decay on a bounded height interval

The elementary logarithmic bound controls the complementary range
without any restriction on the modulus or character.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterChebyshevSum_le_boundedHeight
    {a T : Real} (ha : 0 <= a) {N x : Nat}
    (chi : _root_.DirichletCharacter Complex N) (hx : 2 <= x)
    (hHeight : Real.sqrt (Real.log x) <= T) :
    norm (characterChebyshevSum x chi) <=
      (T ^ 2 * Real.exp (a * T)) *
        ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  have hxReal : (2 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hxOne : (1 : Real) <= (x : Real) := by linarith
  have hLog : 0 <= Real.log (x : Real) := Real.log_nonneg hxOne
  have hWindow := BombieriVinogradov.RealAnalysis.sq_le_exp_window ha
    (Real.sqrt_nonneg (Real.log x)) hHeight
  rw [Real.sq_sqrt hLog] at hWindow
  have hPsi : norm (characterChebyshevSum x chi) <= (x : Real) * Real.log x :=
    BombieriVinogradov.VaughanMeanValue.norm_psiCharacterSum_le_mul_log chi x
  calc
    norm (characterChebyshevSum x chi) <= (x : Real) * Real.log x := hPsi
    _ <= (x : Real) * ((T ^ 2 * Real.exp (a * T)) *
        Real.exp (-(a * Real.sqrt (Real.log x)))) :=
      mul_le_mul_of_nonneg_left hWindow (by positivity)
    _ = (T ^ 2 * Real.exp (a * T)) *
        ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by ring

end BombieriVinogradov.SiegelWalfisz
