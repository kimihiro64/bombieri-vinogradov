import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.KernelDifference
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.LogDerivativeRemainder
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedMeromorphic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# At most a simple pole for the regularized integrand at zero

This module proves the origin order bound after the exact double-pole
correction. It keeps the scaled local model separate from the definitions and
global meromorphicity modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The double-pole-corrected explicit-formula integrand has meromorphic order
at least minus one at zero. -/
theorem neg_one_le_meromorphicOrderAt_regularizedExplicitFormulaIntegrand_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) :
    ((-1 : Int) : WithTop Int) <=
      meromorphicOrderAt (regularizedExplicitFormulaIntegrand chi x) 0 := by
  let g : Complex -> Complex := fun s => (x : Complex) ^ s
  let r : Complex -> Complex := lFunctionOriginLogDerivativeRemainder chi
  let q : Complex -> Complex := originCpowDifferenceQuotient x
  let n : Complex := (lFunctionOriginMultiplicity chi : Complex)
  let first : Complex -> Complex := fun s => -(g s * r s)
  let second : Complex -> Complex := fun s => -(n * q s)
  let model : Complex -> Complex := first + second
  let scaled : Complex -> Complex := fun s =>
    s * regularizedExplicitFormulaIntegrand chi x s
  have hxC : Ne (x : Complex) 0 := by
    exact_mod_cast hx.ne'
  have hGAnalytic : AnalyticAt Complex g 0 := by
    dsimp [g]
    simp_rw [Complex.cpow_def_of_ne_zero hxC]
    fun_prop
  have hGNe : Ne (g 0) 0 := by
    simp [g]
  have hRemainderMero : MeromorphicAt r 0 := by
    exact meromorphicAt_lFunctionOriginLogDerivativeRemainder hchi
  have hRemainderOrder : 0 <= meromorphicOrderAt r 0 := by
    exact meromorphicOrderAt_lFunctionOriginLogDerivativeRemainder_nonneg hchi
  have hQMero : MeromorphicAt q 0 := by
    exact meromorphic_originCpowDifferenceQuotient x hx 0
  have hQOrder : 0 <= meromorphicOrderAt q 0 := by
    exact meromorphicOrderAt_originCpowDifferenceQuotient_zero_nonneg x hx
  have hFirstMero : MeromorphicAt first 0 := by
    exact (hGAnalytic.meromorphicAt.mul hRemainderMero).neg
  have hFirstOrder : 0 <= meromorphicOrderAt first 0 := by
    rw [show first = -(g * r) by rfl,
      Eq.symm (meromorphicOrderAt_neg (x := 0) (f := g * r)),
      meromorphicOrderAt_mul_of_ne_zero hGAnalytic hGNe]
    exact hRemainderOrder
  have hSecondMero : MeromorphicAt second 0 := by
    exact ((MeromorphicAt.const n 0).mul hQMero).neg
  have hSecondOrder : 0 <= meromorphicOrderAt second 0 := by
    have hConstOrder :
        0 <= meromorphicOrderAt (fun _ : Complex => n) 0 :=
      (analyticAt_const (v := n) (x := 0)).meromorphicOrderAt_nonneg
    rw [show second = -((fun _ : Complex => n) * q) by rfl,
      Eq.symm (meromorphicOrderAt_neg
        (x := 0) (f := (fun _ : Complex => n) * q)),
      meromorphicOrderAt_mul (MeromorphicAt.const n 0) hQMero]
    exact add_nonneg hConstOrder hQOrder
  have hModelOrder : 0 <= meromorphicOrderAt model 0 := by
    exact (le_min hFirstOrder hSecondOrder).trans
      (meromorphicOrderAt_add hFirstMero hSecondMero)
  have hEq : Filter.EventuallyEq
      (nhdsWithin 0 (Compl.compl ({0} : Set Complex))) scaled model := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : Ne s 0 := by
      intro hsEq
      apply hs
      simp [hsEq]
    dsimp [scaled, model, first, second, g, r, q, n,
      regularizedExplicitFormulaIntegrand, originDoublePoleCorrection,
      lFunctionOriginLogDerivativeRemainder,
      originCpowDifferenceQuotient, explicitFormulaIntegrand]
    field_simp
    ring
  have hScaledOrder : 0 <= meromorphicOrderAt scaled 0 := by
    rw [meromorphicOrderAt_congr hEq]
    exact hModelOrder
  have hRegMero :
      MeromorphicAt (regularizedExplicitFormulaIntegrand chi x) 0 :=
    meromorphic_regularizedExplicitFormulaIntegrand hchi x hx 0
  have hIdOrder :
      meromorphicOrderAt (fun s : Complex => s) 0 = 1 := by
    change meromorphicOrderAt (id : Complex -> Complex) 0 = 1
    exact meromorphicOrderAt_id
  have hOrderEq :
      meromorphicOrderAt scaled 0 =
        1 + meromorphicOrderAt
          (regularizedExplicitFormulaIntegrand chi x) 0 := by
    rw [show scaled = (fun s : Complex => s) *
      regularizedExplicitFormulaIntegrand chi x by rfl,
      meromorphicOrderAt_mul (by fun_prop) hRegMero,
      hIdOrder]
  rw [hOrderEq] at hScaledOrder
  by_cases hTop :
      meromorphicOrderAt (regularizedExplicitFormulaIntegrand chi x) 0 =
        (Top.top : WithTop Int)
  case pos =>
    rw [hTop]
    exact le_top
  case neg =>
    lift meromorphicOrderAt
      (regularizedExplicitFormulaIntegrand chi x) 0 to Int using hTop
        with orderValue hOrderValue
    have hIntScaled : (0 : Int) <= 1 + orderValue := by
      exact_mod_cast hScaledOrder
    have hIntGoal : (-1 : Int) <= orderValue := by
      omega
    exact_mod_cast hIntGoal

end BombieriVinogradov.SiegelWalfisz
