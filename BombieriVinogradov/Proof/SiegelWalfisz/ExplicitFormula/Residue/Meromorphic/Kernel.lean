import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Integrand
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Meromorphic explicit-formula kernel

This module proves only the global meromorphicity of the negative Perron
kernel used in the explicit-formula integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For positive natural `x`, the function `s -> -(x^s / s)` is meromorphic
on the complex plane. -/
theorem meromorphic_explicitFormulaKernel (x : Nat) (hx : 0 < x) :
    Meromorphic (fun s : Complex => -((x : Complex) ^ s / s)) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hEq :
      (fun s : Complex => -((x : Complex) ^ s / s)) =
        fun s : Complex =>
          -(Complex.exp ((Real.log (x : Real) : Complex) * s) / s) := by
    funext s
    rw [show ((x : Complex) ^ s / s) =
      perronKernelIntegrand (x : Real) s by rfl]
    rw [perronKernelIntegrand_eq_exp hxReal s]
  rw [hEq]
  have hNumDiff : Differentiable Complex
      (fun s : Complex =>
        Complex.exp ((Real.log (x : Real) : Complex) * s)) := by
    fun_prop
  have hNum : Meromorphic
      (fun s : Complex =>
        Complex.exp ((Real.log (x : Real) : Complex) * s)) := by
    intro s
    exact (hNumDiff.analyticAt s).meromorphicAt
  have hDenDiff : Differentiable Complex (fun s : Complex => s) := by
    fun_prop
  have hDen : Meromorphic (fun s : Complex => s) := by
    intro s
    exact (hDenDiff.analyticAt s).meromorphicAt
  exact (hNum.div hDen).neg

end BombieriVinogradov.SiegelWalfisz
