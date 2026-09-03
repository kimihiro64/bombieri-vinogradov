import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.Geometry
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith

/-!
# Exceptional-zero facts from stronger zero-free bounds

Shrinking the two existing zero-free constants preserves simplicity and
excludes nonquadratic exceptional zeros; the geometric cutoff supplies
the remaining two facts required by the centered residue estimate.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exceptionalZeroFacts_of_zeroFreeBounds
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hN : 3 <= N) {c C R : Real}
    (hcC : c <= C) (hcR : c <= R) (hcLog : c <= Real.log 3 / 4)
    (hSimple : forall s : Complex,
      0 < s.re -> chi.LFunction s = 0 ->
        s.im = 0 -> 1 - s.re <= C / Real.log N ->
          analyticOrderNatAt chi.LFunction s = 1)
    (hNonquadratic : Ne (chi ^ 2) 1 ->
      forall {s : Complex}, 0 < s.re -> chi.LFunction s = 0 ->
        s.im = 0 -> R / Real.log N < 1 - s.re)
    {beta : Complex} (hExceptional : IsExceptionalZero c chi beta) :
    ExceptionalZeroFacts chi beta := by
  have hGap : 1 - beta.re < c / Real.log N := by
    linarith [hExceptional.2.2.2.2]
  have hCompareC : c / Real.log N <= C / Real.log N :=
    div_le_div_of_nonneg_right hcC (Real.log_natCast_nonneg N)
  have hCompareR : c / Real.log N <= R / Real.log N :=
    div_le_div_of_nonneg_right hcR (Real.log_natCast_nonneg N)
  have hSimpleValue : analyticOrderNatAt chi.LFunction beta = 1 :=
    hSimple beta hExceptional.2.2.1 hExceptional.1 hExceptional.2.1
      (hGap.le.trans hCompareC)
  have hQuadratic : chi ^ 2 = 1 := Classical.byContradiction (by
    intro hNot
    have hStrict := hNonquadratic hNot (s := beta)
      hExceptional.2.2.1 hExceptional.1 hExceptional.2.1
    exact not_lt_of_ge (hGap.le.trans hCompareR) hStrict)
  have hGeometry := isExceptionalZero_three_quarters_lt_re_and_ne_reflection
    hN hcLog hExceptional
  exact {
    quadratic := hQuadratic
    simple := hSimpleValue
    re_lower := hGeometry.1.le
    reflection_ne := hGeometry.2
  }

end BombieriVinogradov.SiegelWalfisz
