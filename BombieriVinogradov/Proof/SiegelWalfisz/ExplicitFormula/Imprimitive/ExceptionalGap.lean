import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionEulerProduct
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith

/-!
# The gap when only the primitive character has an exceptional zero

Absence from the ambient exceptional window supplies the reciprocal bound
needed for the reflected contribution.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem primitiveExceptional_gap_of_ambient_none
    {c : Real} {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : Ne chi 1) (hNone : IsExceptionalZeroChoice c chi none)
    {beta : Complex} (hExceptional : IsExceptionalZero c chi.primitiveCharacter beta) :
    c / Real.log N <= 1 - beta.re := by
  by_cases hGap : c / Real.log N <= 1 - beta.re
  case pos => exact hGap
  case neg =>
    have hZero : chi.LFunction beta = 0 := by
      rw [LFunction_eq_primitive_mul_levelCorrection chi hchi beta,
        hExceptional.1, zero_mul]
    have hAmbient : IsExceptionalZero c chi beta :=
      And.intro hZero
        (And.intro hExceptional.2.1
          (And.intro hExceptional.2.2.1
            (And.intro hExceptional.2.2.2.1 (by linarith))))
    change Not (exists rho : Complex, IsExceptionalZero c chi rho) at hNone
    exact False.elim (hNone (Exists.intro beta hAmbient))

end BombieriVinogradov.SiegelWalfisz
