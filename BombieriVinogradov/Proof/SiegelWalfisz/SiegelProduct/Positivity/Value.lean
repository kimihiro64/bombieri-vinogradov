import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Pole.Main

/-!
# The meromorphic Siegel-product value

This module names the four-factor value and relates it to the regular part away from the pole.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The four-factor analytic product appearing in Siegel's argument. -/
noncomputable def siegelProductValue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  riemannZeta s * siegelLProduct chi psi s

theorem siegelProductValue_eq_regular_add_pole {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelProductValue chi psi s =
      siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1) := by
  rw [siegelPoleSubtracted_apply_of_ne chi psi hs]
  unfold siegelProductValue
  ring

end BombieriVinogradov.SiegelWalfisz
