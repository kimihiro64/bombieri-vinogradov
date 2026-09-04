import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.DirichletCharacter.ElementaryChebyshev
import BombieriVinogradov.Helpers.RealAnalysis.NatLogSqrtEndpoint
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogElementaryAbsorption
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith

/-!
# Character sums below the square-root endpoint

The elementary character bound and scalar logarithmic absorption give a
uniform exponential-logarithmic estimate, including endpoint zero.
-/

set_option autoImplicit false

namespace BombieriVinogradov.VaughanMeanValue

/-- Every character sum below sqrt(X) fits the common decay scale with coefficient 32. -/
theorem norm_psiCharacterSum_le_smallEndpoint {X a : Real} {N y : Nat}
    (chi : _root_.DirichletCharacter Complex N) (hX : 1 <= X)
    (hLog : 1 <= Real.log X) (ha : a <= (1 / 4 : Real))
    (hy : (y : Real) <= Real.sqrt X) :
    norm (psiCharacterSum y N chi) <=
      32 * (X * Real.exp (-(a * Real.sqrt (Real.log X)))) := by
  have hXPos : 0 < X := by linarith
  exact (norm_psiCharacterSum_le_mul_log chi y).trans
    ((RealAnalysis.nat_mul_log_le_sqrt_mul_log hX hy).trans
      (RealAnalysis.sqrt_mul_log_le_exponentialLog_scale hXPos hLog ha))

end BombieriVinogradov.VaughanMeanValue
