import BombieriVinogradov.Helpers.DirichletCharacter.PartialSumIdentity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Abel integral for a character Dirichlet series

This module owns only the source-normalized integral expression used to
continue a nonprincipal character Dirichlet series into `0 < re s`.
-/

set_option autoImplicit false

open Finset MeasureTheory Set

namespace BombieriVinogradov

/-- The source integral `s * integral A(t) t^(-s-1) dt` for character prefixes `A`. -/
noncomputable def characterAbelIntegral {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  s * ∫ t in Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : ℂ) ^ (-(s + 1))

end BombieriVinogradov
