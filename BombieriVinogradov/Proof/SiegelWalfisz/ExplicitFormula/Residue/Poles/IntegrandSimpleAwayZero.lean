import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.LogDerivativeSimple
import Mathlib.Analysis.Meromorphic.Order

/-!
# Simple poles of the explicit-formula integrand away from zero

This module proves only that the nonvanishing Perron kernel preserves the
at-most-simple pole bound for the logarithmic derivative away from its own
pole at zero.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Away from zero, multiplying the logarithmic derivative by the Perron
kernel does not change its meromorphic order, so the explicit-formula
integrand has at most simple poles. -/
theorem hasSimplePolesOn_explicitFormulaIntegrand_away_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (U : Set Complex)
    (hzero : Not (Membership.mem U 0)) :
    HasSimplePolesOn (explicitFormulaIntegrand chi x) U := by
  have hLog := hasSimplePolesOn_logDeriv_LFunction hchi U
  intro z hz
  have hz0 : Ne z 0 := by
    intro hzEq
    apply hzero
    rw [hzEq] at hz
    exact hz
  have hxC : Ne (x : Complex) 0 := by
    exact_mod_cast hx.ne'
  have hPowAnalytic :
      AnalyticAt Complex (fun s : Complex => (x : Complex) ^ s) z := by
    simp_rw [Complex.cpow_def_of_ne_zero hxC]
    fun_prop
  have hKernelAnalytic :
      AnalyticAt Complex (fun s : Complex => -((x : Complex) ^ s / s)) z := by
    exact (hPowAnalytic.div (by fun_prop) hz0).neg
  have hKernelNe : Ne (-((x : Complex) ^ z / z)) 0 := by
    exact neg_ne_zero.mpr
      (div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hxC)) hz0)
  have hEq :
      explicitFormulaIntegrand chi x =
        (fun s : Complex => -((x : Complex) ^ s / s)) *
          logDeriv chi.LFunction := by
    funext s
    simp only [explicitFormulaIntegrand, Pi.mul_apply]
    exact mul_comm _ _
  rw [hEq, meromorphicOrderAt_mul_of_ne_zero hKernelAnalytic hKernelNe]
  exact hLog z hz

end BombieriVinogradov.SiegelWalfisz
