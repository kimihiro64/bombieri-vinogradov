import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.FunProp

/-!
# Horizontal explicit-formula integrand continuity

This module proves continuity on a finite nonzero horizontal segment and
the resulting interval integrability for one positive-base integrand term.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem continuousOn_explicitFormulaIntegrand_horizontal
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x)
    {a b T : Real} (hT : Ne T 0)
    (hNonzero : forall u : Real, Set.uIcc a b u ->
      Ne (chi.LFunction
        ((u : Complex) + (T : Complex) * Complex.I)) 0) :
    ContinuousOn
      (fun u : Real => explicitFormulaIntegrand chi x
        ((u : Complex) + (T : Complex) * Complex.I))
      (Set.uIcc a b) := by
  let path : Real -> Complex := fun u =>
    (u : Complex) + (T : Complex) * Complex.I
  have hPath : Continuous path := by
    dsimp [path]
    fun_prop
  have hPathNe : forall u : Real, Ne (path u) 0 := by
    intro u hzero
    have hImag := congrArg Complex.im hzero
    dsimp [path] at hImag
    simp at hImag
    exact hT hImag
  have hLFunctionDifferentiable : Differentiable Complex chi.LFunction :=
    DirichletCharacter.differentiable_LFunction hchi
  have hLFunctionContinuous : Continuous chi.LFunction :=
    hLFunctionDifferentiable.continuous
  have hDerivContinuous : Continuous (deriv chi.LFunction) :=
    hLFunctionDifferentiable.contDiff.continuous_deriv (le_refl 1)
  have hxNe : Ne (x : Complex) 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hx)
  have hPowerContinuous :
      Continuous (fun s : Complex => (x : Complex) ^ s) :=
    continuous_iff_continuousAt.mpr
      (fun _ => continuousAt_const_cpow hxNe)
  intro u hu
  have hLogDerivAt :
      ContinuousAt (fun v : Real => logDeriv chi.LFunction (path v)) u := by
    simp_rw [logDeriv_apply]
    exact
      (hDerivContinuous.comp hPath).continuousAt.div
        (hLFunctionContinuous.comp hPath).continuousAt
        (by simpa [path] using hNonzero u hu)
  change ContinuousWithinAt
    (fun v : Real => logDeriv chi.LFunction (path v) *
      (-((x : Complex) ^ path v / path v)))
    (Set.uIcc a b) u
  exact
    (hLogDerivAt.mul
      ((hPowerContinuous.comp hPath).div hPath hPathNe).neg.continuousAt).continuousWithinAt

theorem intervalIntegrable_explicitFormulaIntegrand_horizontal
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x)
    {a b T : Real} (hT : Ne T 0)
    (hNonzero : forall u : Real, Set.uIcc a b u ->
      Ne (chi.LFunction
        ((u : Complex) + (T : Complex) * Complex.I)) 0) :
    IntervalIntegrable
      (fun u : Real => explicitFormulaIntegrand chi x
        ((u : Complex) + (T : Complex) * Complex.I))
      MeasureTheory.volume a b :=
  (continuousOn_explicitFormulaIntegrand_horizontal
    hchi x hx hT hNonzero).intervalIntegrable

end BombieriVinogradov.SiegelWalfisz
