import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.ScalarTerm

/-!
# Integral of one Perron-series term

This module identifies the normalized vertical integral of one Dirichlet term
with the corresponding twisted coefficient times the scalar Perron kernel.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Away from the zeroth term, the Dirichlet summand factors as its coefficient
times the scalar Perron integrand at `x / n`. -/
theorem explicitFormulaDirichletTerm_eq_coeff_mul_perronKernel
    {N : Nat} (chi : DirichletCharacter Complex N) (x n : Nat)
    (s : Complex) (hn : Ne n 0) :
    explicitFormulaDirichletTerm chi x n s =
      twistedMangoldtSequence chi n *
        perronKernelIntegrand ((x : Real) / (n : Real)) s := by
  rw [explicitFormulaDirichletTerm, LSeries.term_def, if_neg hn,
    perronKernelIntegrand]
  rw [Complex.ofReal_div]
  rw [Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg x)
    (Nat.cast_nonneg n)]
  simp only [Complex.ofReal_natCast]
  ring

/-- Normalized vertical integration of one Dirichlet term produces exactly its
scalar Perron-series term. -/
theorem VIntegral_explicitFormulaDirichletTerm_eq_scalarPerronSeriesTerm
    {N : Nat} (chi : DirichletCharacter Complex N) (x n : Nat)
    (c T : Real) :
    VIntegral' (explicitFormulaDirichletTerm chi x n) c (-T) T =
      scalarPerronSeriesTerm chi x c T n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [scalarPerronSeriesTerm, explicitFormulaDirichletTerm,
      LSeries.term_def, VIntegral', VIntegral]
  case neg =>
    have hFunctions : (fun t : Real =>
        explicitFormulaDirichletTerm chi x n (c + t * Complex.I)) =
        fun t : Real => twistedMangoldtSequence chi n *
          perronKernelIntegrand ((x : Real) / (n : Real))
            (c + t * Complex.I) := by
      funext t
      exact explicitFormulaDirichletTerm_eq_coeff_mul_perronKernel chi x n
        (c + t * Complex.I) hn
    rw [scalarPerronSeriesTerm, if_neg hn]
    simp only [VIntegral', VIntegral, truncatedPerronKernel]
    rw [hFunctions, intervalIntegral.integral_const_mul]
    simp only [smul_eq_mul]
    ring

end BombieriVinogradov.SiegelWalfisz
