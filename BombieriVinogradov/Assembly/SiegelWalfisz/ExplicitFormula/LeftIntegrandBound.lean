import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.LeftKernelBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLeftLineLogDerivativeBound
import Mathlib.Tactic.Ring

/-!
# Centered explicit-formula integrand bound on the left line

This thin assembly module combines the left-line logarithmic-derivative
estimate with the independently proved centered power-kernel decay.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_centered_explicitFormulaIntegrand_left_line_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N]
        {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 1 <= x ->
              forall {s : Complex}, s.re = -(1 : Real) / 2 ->
                norm (explicitFormulaIntegrand chi x s -
                    explicitFormulaIntegrand chi 1 s) <=
                  (abs (Real.log N) +
                      C * Real.log (abs s.im + 2)) *
                    (6 / (abs s.im + 1))) := by
  choose C hCPos hLFunction using
    exists_norm_logDeriv_LFunction_left_line_le
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst chi hchi hPrimitive x hx s hsRe
  have hLFunctionAt := hLFunction hchi hPrimitive hsRe
  have hLBoundNonneg :
      0 <= abs (Real.log N) +
          C * Real.log (abs s.im + 2) :=
    (norm_nonneg (logDeriv chi.LFunction s)).trans hLFunctionAt
  have hKernel :=
    norm_centered_cpow_kernel_left_line_le x hx hsRe
  have hIdentity :
      explicitFormulaIntegrand chi x s -
          explicitFormulaIntegrand chi 1 s =
        logDeriv chi.LFunction s *
          (-(((x : Complex) ^ s - 1) / s)) := by
    simp [explicitFormulaIntegrand]
    ring
  rw [hIdentity, norm_mul, norm_neg]
  exact mul_le_mul hLFunctionAt hKernel
    (norm_nonneg _) hLBoundNonneg

end BombieriVinogradov.SiegelWalfisz
