import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Integrand
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# The pole of the Perron integrand

This module isolates the simple pole of `y ^ s / s` at zero.  A divided
difference supplies an entire remainder, allowing the pinned rectangle
residue theorem to evaluate any rectangle whose interior contains zero.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The analytic remainder after subtracting the principal part `1 / s`. -/
def perronKernelRemainder (y : Real) (s : Complex) : Complex :=
  dslope (fun z : Complex =>
    Complex.exp ((Real.log y : Complex) * z)) 0 s

/-- The divided-difference remainder is complex differentiable everywhere. -/
theorem differentiableAt_perronKernelRemainder
    (y : Real) (s : Complex) :
    DifferentiableAt Complex (perronKernelRemainder y) s := by
  let h : Complex -> Complex := fun z =>
    Complex.exp ((Real.log y : Complex) * z)
  by_cases hs : s = 0
  next =>
    subst s
    have hh : AnalyticAt Complex h 0 := by
      dsimp [h]
      fun_prop
    choose p hp using hh
    exact hp.has_fpower_series_dslope_fslope.differentiableAt
  next =>
    change DifferentiableAt Complex (dslope h 0) s
    exact (differentiableAt_dslope_of_ne hs).2 (by
      dsimp [h]
      fun_prop)

/-- Away from zero, subtracting `1 / s` from the Perron integrand gives the
entire divided-difference remainder. -/
theorem perronKernelIntegrand_sub_pole_eq_remainder
    {y : Real} (hy : 0 < y) :
    Set.EqOn
      (perronKernelIntegrand y - fun s : Complex => 1 / (s - 0))
      (perronKernelRemainder y) (Set.compl ({0} : Set Complex)) := by
  intro s hs
  have hs0 : Ne s 0 := by
    intro h
    apply hs
    simp [h]
  rw [Pi.sub_apply, perronKernelIntegrand_eq_exp hy]
  rw [perronKernelRemainder, dslope_of_ne _ hs0]
  simp only [slope, sub_zero, Complex.exp_zero, mul_zero, one_div]
  simp only [vsub_eq_sub, smul_eq_mul]
  ring

/-- A positively oriented rectangle containing zero has normalized Perron
integral equal to the residue `1`. -/
theorem rectangleIntegral'_perron_eq_one
    {y : Real} (hy : 0 < y) {z w : Complex}
    (hRe : z.re <= w.re) (hIm : z.im <= w.im)
    (hZero : Membership.mem (nhds (0 : Complex)) (Complex.Rectangle z w)) :
    RectangleIntegral' (perronKernelIntegrand y) z w = 1 := by
  apply ResidueTheoremOnRectangleWithSimplePole hRe hIm hZero
    (g := perronKernelRemainder y)
  next =>
    intro s _
    exact (differentiableAt_perronKernelRemainder y s).differentiableWithinAt
  next =>
    exact (perronKernelIntegrand_sub_pole_eq_remainder hy).mono
      (Set.sdiff_subset_compl _ _)

end BombieriVinogradov.SiegelWalfisz
