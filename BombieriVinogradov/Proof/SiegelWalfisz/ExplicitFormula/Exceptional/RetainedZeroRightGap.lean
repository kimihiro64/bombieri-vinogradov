import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Retained-zero gap from one
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem retainedLFunctionZero_gap_from_one
    {c : Real} (hc : 0 < c)
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hN : 3 <= N)
    (hRegularGap : forall s : Complex,
      0 < s.re -> chi.LFunction s = 0 ->
        Or (Ne (chi ^ 2) 1) (Ne s.im 0) ->
          c / (Real.log N + Real.log (abs s.im + 2)) <=
            1 - s.re)
    (hRealUnique : forall s t : Complex,
      0 < s.re -> 0 < t.re ->
        chi.LFunction s = 0 -> chi.LFunction t = 0 ->
          s.im = 0 -> t.im = 0 ->
            1 - s.re <= c / Real.log N ->
              1 - t.re <= c / Real.log N -> s = t)
    {exceptional : Option Complex}
    (hChoice : IsExceptionalZeroChoice c chi exceptional)
    {rho : Complex} (hrhoZero : chi.LFunction rho = 0)
    (hrhoPos : 0 < rho.re) (hrhoLt : rho.re < 1)
    (hrhoRetained : IsRetainedZero exceptional rho) :
    c / (Real.log N + Real.log (abs rho.im + 2)) <=
      1 - rho.re := by
  by_cases hRegular : Or (Ne (chi ^ 2) 1) (Ne rho.im 0)
  case pos =>
    exact hRegularGap rho hrhoPos hrhoZero hRegular
  case neg =>
    have hNotRegular := not_or.mp hRegular
    have hIm : rho.im = 0 :=
      not_ne_iff.mp hNotRegular.2
    have hThreeReal : (3 : Real) <= (N : Real) :=
      (Nat.cast_le).2 hN
    have hLogThreePos : 0 < Real.log (3 : Real) :=
      Real.log_pos (by norm_num)
    have hLogNLower : Real.log (3 : Real) <= Real.log N :=
      Real.log_le_log (by norm_num) hThreeReal
    have hLogNPos : 0 < Real.log N :=
      hLogThreePos.trans_le hLogNLower
    have hGapLogN :
        c / Real.log N <= 1 - rho.re := by
      apply le_of_not_gt
      intro hTooClose
      have hExceptional : IsExceptionalZero c chi rho :=
        And.intro hrhoZero
          (And.intro hIm
            (And.intro hrhoPos
              (And.intro hrhoLt (by linarith))))
      cases exceptional
      case none =>
        change Not (Exists fun z : Complex =>
          IsExceptionalZero c chi z) at hChoice
        exact hChoice (Exists.intro rho hExceptional)
      case some beta =>
        change IsExceptionalZero c chi beta at hChoice
        change And (Ne rho beta) (Ne rho (1 - beta)) at hrhoRetained
        have hrhoGap : 1 - rho.re <= c / Real.log N :=
          hTooClose.le
        have hbetaGap : 1 - beta.re <= c / Real.log N := by
          linarith [hChoice.2.2.2.2]
        have hEq := hRealUnique rho beta
          hrhoPos hChoice.2.2.1 hrhoZero hChoice.1
          hIm hChoice.2.1 hrhoGap hbetaGap
        exact hrhoRetained.1 hEq
    have hLogHeightNonneg :
        0 <= Real.log (abs rho.im + 2) := by
      apply Real.log_nonneg
      linarith [abs_nonneg rho.im]
    have hScale :
        c / (Real.log N + Real.log (abs rho.im + 2)) <=
          c / Real.log N :=
      div_le_div_of_nonneg_left hc.le hLogNPos
        (le_add_of_nonneg_right hLogHeightNonneg)
    exact hScale.trans hGapLogN

end BombieriVinogradov.SiegelWalfisz
