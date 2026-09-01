import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalLogDerivativeSeriesComparison
import PrimeNumberTheoremAnd.ZetaBounds

/-!
# Principal-character logarithmic-derivative bound

This module proves the principal-character estimate in Strombergsson equation (401),
with one absolute constant independent of the modulus and real point.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_neg_re_logDeriv_principal_le_inv_add :
    exists C : Real, 0 ≤ C ∧
      forall {N : Nat} [NeZero N] {sigma : Real},
        1 < sigma -> sigma ≤ 2 ->
          (-deriv (1 : DirichletCharacter Complex N).LFunction sigma /
            (1 : DirichletCharacter Complex N).LFunction sigma).re ≤
              (sigma - 1)⁻¹ + C := by
  obtain ⟨C, hCNonneg, hZeta⟩ := triv_bound_zeta
  refine Exists.intro C (And.intro hCNonneg ?_)
  intro N _hN sigma hsigma _hsigmaUpper
  have hRealLe :
      (-deriv (1 : DirichletCharacter Complex N).LFunction sigma /
        (1 : DirichletCharacter Complex N).LFunction sigma).re ≤
        ‖-deriv (1 : DirichletCharacter Complex N).LFunction sigma /
          (1 : DirichletCharacter Complex N).LFunction sigma‖ :=
    le_trans (le_abs_self _)
      (Complex.abs_re_le_norm
        (-deriv (1 : DirichletCharacter Complex N).LFunction sigma /
          (1 : DirichletCharacter Complex N).LFunction sigma))
  have hPrincipal := norm_neg_logDeriv_principal_le_zeta
    (N := N) hsigma
  have hZetaAtSigma :
      ‖-deriv riemannZeta sigma / riemannZeta sigma‖ ≤
        (sigma - 1)⁻¹ + C := by
    simpa using hZeta sigma 0 hsigma
  exact hRealLe.trans (hPrincipal.trans hZetaAtSigma)

end BombieriVinogradov.SiegelWalfisz
