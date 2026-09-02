import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Integrand
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Full-circle value of the Perron integrand

This module evaluates the Perron integrand on every positively oriented circle
centered at its pole.  It is a direct instance of the Cauchy integral formula
for the entire numerator.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The full circle integral of `y ^ s / s` is `2 * pi * i`. -/
theorem circleIntegral_perronKernelIntegrand_eq
    {y R : Real} (hy : 0 < y) (hR : 0 < R) :
    circleIntegral (perronKernelIntegrand y) 0 R =
      2 * Real.pi * Complex.I := by
  let h : Complex -> Complex := fun z =>
    Complex.exp ((Real.log y : Complex) * z)
  have hd : DifferentiableOn Complex h (Metric.closedBall 0 R) := by
    intro z _
    dsimp [h]
    fun_prop
  have hw : Metric.ball (0 : Complex) R 0 := Metric.mem_ball_self hR
  have hC := hd.circleIntegral_sub_inv_smul hw
  have hEq : perronKernelIntegrand y =
      fun z : Complex => Inv.inv (z - 0) * h z := by
    funext z
    rw [perronKernelIntegrand_eq_exp hy]
    dsimp [h]
    simp [div_eq_mul_inv, mul_comm]
  rw [hEq]
  simpa [smul_eq_mul, h] using hC

end BombieriVinogradov.SiegelWalfisz
