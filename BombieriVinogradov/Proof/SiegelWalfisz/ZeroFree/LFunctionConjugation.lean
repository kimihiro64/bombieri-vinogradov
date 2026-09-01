import BombieriVinogradov.Helpers.DirichletCharacter.ComplexConjugation
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Complex conjugation of analytically continued Dirichlet L-functions

This module proves the conjugation identity first on the absolute-convergence
half-plane and then extends it to the entire nonprincipal L-function by analytic
uniqueness.
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace BombieriVinogradov.SiegelWalfisz

theorem DirichletCharacter.LFunction_inv_eq_conj_conj
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (s : Complex) :
    chi⁻¹.LFunction s = conj (chi.LFunction (conj s)) := by
  have hInverseNe : chi⁻¹ ≠ 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  let g : Complex -> Complex := conj ∘ chi.LFunction ∘ conj
  have hDifferentiableG : Differentiable Complex g := by
    intro z
    have hAtConj : DifferentiableAt Complex chi.LFunction (conj z) :=
      (chi.differentiable_LFunction hchi).differentiableAt
    simpa [g] using hAtConj.conj_conj
  have hAnalyticInv :
      AnalyticOnNhd Complex chi⁻¹.LFunction (Set.univ : Set Complex) :=
    (chi⁻¹.differentiable_LFunction hInverseNe).differentiableOn.analyticOnNhd
      isOpen_univ
  have hAnalyticG : AnalyticOnNhd Complex g (Set.univ : Set Complex) :=
    hDifferentiableG.differentiableOn.analyticOnNhd isOpen_univ
  have hRightHalfPlane : {z : Complex | 1 < z.re} ∈ nhds (2 : Complex) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have hEventually : chi⁻¹.LFunction =ᶠ[nhds (2 : Complex)] g := by
    filter_upwards [hRightHalfPlane] with z hz
    have hzConj : 1 < (conj z).re := by simpa using hz
    change chi⁻¹.LFunction z = conj (chi.LFunction (conj z))
    rw [chi⁻¹.LFunction_eq_LSeries hz,
      chi.LFunction_eq_LSeries hzConj]
    exact (BombieriVinogradov.DirichletCharacter.conj_LSeries_conj_eq_inv_LSeries
      chi z).symm
  have hFunctions : chi⁻¹.LFunction = g :=
    AnalyticOnNhd.eq_of_eventuallyEq hAnalyticInv hAnalyticG hEventually
  simpa [g] using congrFun hFunctions s

end BombieriVinogradov.SiegelWalfisz
