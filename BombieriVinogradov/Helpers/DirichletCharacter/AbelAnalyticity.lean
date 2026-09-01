import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegralDifferentiable
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analyticity of the character Abel integral

This module owns conversion from pointwise complex differentiability to
analyticity on the open positive-real-part half-plane.
-/

set_option autoImplicit false

namespace BombieriVinogradov

/-- The nonprincipal character Abel integral is analytic on `re(s)>0`. -/
theorem characterAbelIntegral_analyticOnNhd {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : chi ≠ 1) :
    AnalyticOnNhd Complex (characterAbelIntegral chi) {s : Complex | 0 < s.re} := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) ?_
  · exact (characterAbelIntegral_differentiableAt chi hchi hs).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

end BombieriVinogradov
