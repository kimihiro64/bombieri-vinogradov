import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CircleBound
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Coefficient

/-!
# Cauchy estimate for the regular Siegel coefficients

This module applies the normalized Cauchy inequality at radius three-halves
and owns the exact conversion to the source decay factor `(2 / 3)^m`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelRegularCoefficient_le_of_circle_bound
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {C : ℝ} {K : ℕ}
    (hcircle : ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
      ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ ≤
      C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  rw [norm_siegelRegularCoefficient]
  have hcauchy := BombieriVinogradov.ComplexAnalysis.norm_taylorCoefficient_le
    m (by norm_num : (0 : ℝ) < 3 / 2)
    (siegelProduct_sub_pole_entire χ ψ hχ hψ hmul)
    (fun z hz ↦ hcircle hz)
  calc
    ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖
        ≤ (C * ((N : ℝ) * (M : ℝ)) ^ K) / (3 / 2 : ℝ) ^ m := hcauchy
    _ = C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num

end BombieriVinogradov.SiegelWalfisz
