import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Coefficient
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Coefficients
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Summability
import Mathlib.NumberTheory.LSeries.Positivity

/-!
# Positive coefficients of the Siegel Dirichlet series

This module defines the source-oriented coefficients at two and proves their positivity.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

/-- The coefficient of `(2 - s)^m` in the convergent Siegel-product Dirichlet series. -/
noncomputable def siegelSourceCoefficient {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (LSeries (siegelProductCoefficients chi psi)) 2 m

/-- The source coefficients are nonnegative for quadratic characters. -/
theorem siegelSourceCoefficient_nonneg {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) (m : ℕ) :
    0 ≤ siegelSourceCoefficient chi psi m := by
  have hsumm : LSeriesSummable (siegelProductCoefficients chi psi) (3 / 2 : ℂ) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  have habs : LSeries.abscissaOfAbsConv (siegelProductCoefficients chi psi) < (2 : ℝ) :=
    hsumm.abscissaOfAbsConv_le.trans_lt (by norm_num)
  have hderiv := LSeries.iteratedDeriv_alternating
    (siegelProductCoefficients_nonneg chi psi hchi hpsi) habs m
  have hfactorial : (0 : ℂ) ≤ m.factorial := by positivity
  simpa [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, mul_div_assoc] using
      div_nonneg hderiv hfactorial

/-- The constant source coefficient is at least the first Dirichlet term, which equals one. -/
theorem one_le_siegelSourceCoefficient_zero {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) :
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 := by
  rw [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient]
  simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [LSeries]
  have hsumm : Summable (LSeries.term (siegelProductCoefficients chi psi) 2) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  calc
    (1 : ℂ) = ∑ n ∈ {1}, LSeries.term (siegelProductCoefficients chi psi) 2 n := by
      simp [LSeries.term_def, siegelProductCoefficients_one]
    _ ≤ ∑' n, LSeries.term (siegelProductCoefficients chi psi) 2 n :=
      hsumm.sum_le_tsum {1} fun n _ =>
        LSeries.term_nonneg (siegelProductCoefficients_nonneg chi psi hchi hpsi n) 2

end BombieriVinogradov.SiegelWalfisz
