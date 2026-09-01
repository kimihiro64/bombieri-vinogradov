import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.PositivityData

/-!
# Residue lower bound from a nonpositive product value

This module takes the contrapositive of the Siegel-product positivity lemma.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductResidue_lower_of_nonpos {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * ‖siegelProductResidue chi psi‖ := by
  apply le_of_not_gt
  intro hsmall
  have hpositive := hpair.2 chi psi hchiSquare hpsiSquare hchi hpsi hmul
    s hsLower hsUpper hsmall
  linarith

end BombieriVinogradov.SiegelWalfisz
