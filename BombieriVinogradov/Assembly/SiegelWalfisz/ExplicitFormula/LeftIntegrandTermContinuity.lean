import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLeftLineNonvanishing
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Continuity of an explicit-formula integrand term on the left line

This module proves continuity and finite-interval integrability for one
positive-base integrand before centered subtraction.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem continuous_explicitFormulaIntegrand_left_line
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 0 < x) :
    Continuous (fun t : Real =>
      explicitFormulaIntegrand chi x
        (((-(1 : Real) / 2 : Real) : Complex) +
          (t : Complex) * Complex.I)) := by
  let path : Real -> Complex := fun t =>
    (((-(1 : Real) / 2 : Real) : Complex) +
      (t : Complex) * Complex.I)
  have hPath : Continuous path := by
    dsimp [path]
    fun_prop
  have hPathRe :
      forall t : Real, (path t).re = -(1 : Real) / 2 := by
    intro t
    dsimp [path]
    simp
  have hPathNe : forall t : Real, Ne (path t) 0 := by
    intro t ht
    have htRe := congrArg Complex.re ht
    rw [hPathRe t] at htRe
    norm_num at htRe
  have hLFunctionDifferentiable :=
    DirichletCharacter.differentiable_LFunction hchi
  have hLFunctionContinuous : Continuous chi.LFunction :=
    hLFunctionDifferentiable.continuous
  have hDerivContinuous : Continuous (deriv chi.LFunction) :=
    hLFunctionDifferentiable.contDiff.continuous_deriv (le_refl 1)
  have hLogDerivPath :
      Continuous (fun t : Real => logDeriv chi.LFunction (path t)) := by
    simp_rw [logDeriv_apply]
    exact (hDerivContinuous.comp hPath).div
      (hLFunctionContinuous.comp hPath)
      (fun t =>
        LFunction_ne_zero_of_re_eq_neg_one_half
          hchi hPrimitive (hPathRe t))
  have hxNe : Ne (x : Complex) 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hx)
  have hPowerContinuous :
      Continuous (fun s : Complex => (x : Complex) ^ s) :=
    continuous_iff_continuousAt.mpr
      (fun _ => continuousAt_const_cpow hxNe)
  change Continuous (fun t : Real =>
    logDeriv chi.LFunction (path t) *
      (-((x : Complex) ^ path t / path t)))
  exact hLogDerivPath.mul
    ((hPowerContinuous.comp hPath).div hPath hPathNe).neg

theorem intervalIntegrable_explicitFormulaIntegrand_left_line
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 0 < x) (T : Real) :
    IntervalIntegrable
      (fun t : Real =>
        explicitFormulaIntegrand chi x
          (((-(1 : Real) / 2 : Real) : Complex) +
            (t : Complex) * Complex.I))
      MeasureTheory.volume (-T) T :=
  (continuous_explicitFormulaIntegrand_left_line
    hchi hPrimitive x hx).intervalIntegrable _ _

end BombieriVinogradov.SiegelWalfisz
