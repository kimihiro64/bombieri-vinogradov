import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLeftLineNonvanishing
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Continuity of the centered left-line integrand

This module uses nonvanishing on the left line to establish continuity and
finite-interval integrability before any integral linearity is invoked.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem continuous_centered_explicitFormulaIntegrand_left_line
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 1 <= x) :
    Continuous (fun t : Real =>
      explicitFormulaIntegrand chi x
          (((-(1 : Real) / 2 : Real) : Complex) +
            (t : Complex) * Complex.I) -
        explicitFormulaIntegrand chi 1
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
  have hIntegrandContinuous :
      forall y : Nat, 0 < y ->
        Continuous (fun t : Real =>
          explicitFormulaIntegrand chi y (path t)) := by
    intro y hy
    have hyNe : Ne (y : Complex) 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hy)
    have hPowerContinuous :
        Continuous (fun s : Complex => (y : Complex) ^ s) :=
      continuous_iff_continuousAt.mpr
        (fun _ => continuousAt_const_cpow hyNe)
    dsimp [explicitFormulaIntegrand]
    exact hLogDerivPath.mul
      ((hPowerContinuous.comp hPath).div hPath hPathNe).neg
  have hxPos : 0 < x := Nat.zero_lt_of_lt hx
  change Continuous
    ((fun t : Real => explicitFormulaIntegrand chi x (path t)) -
      (fun t : Real => explicitFormulaIntegrand chi 1 (path t)))
  exact (hIntegrandContinuous x hxPos).sub
    (hIntegrandContinuous 1 (by norm_num))

theorem intervalIntegrable_centered_explicitFormulaIntegrand_left_line
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 1 <= x) (T : Real) :
    IntervalIntegrable
      (fun t : Real =>
        explicitFormulaIntegrand chi x
            (((-(1 : Real) / 2 : Real) : Complex) +
              (t : Complex) * Complex.I) -
          explicitFormulaIntegrand chi 1
            (((-(1 : Real) / 2 : Real) : Complex) +
              (t : Complex) * Complex.I))
      MeasureTheory.volume (-T) T :=
  (continuous_centered_explicitFormulaIntegrand_left_line
    hchi hPrimitive x hx).intervalIntegrable _ _

end BombieriVinogradov.SiegelWalfisz
