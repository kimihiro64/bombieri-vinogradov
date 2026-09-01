import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.LSeries
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Pole.Main
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.DirichletCoefficients
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.PoleCoefficients

/-!
# Coefficient bridge for the pole-subtracted Siegel product

This module identifies each positive Dirichlet-series coefficient with its regular coefficient
plus the common pole residue.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The source coefficient is the corresponding regular coefficient plus the pole residue. -/
theorem siegelSourceCoefficient_eq_regular_add_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (m : ℕ) :
    siegelSourceCoefficient chi psi m =
      siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
  let halfPlane : Set ℂ := {s | 1 < s.re}
  have hopen : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
  have htwo : (2 : ℂ) ∈ halfPlane := by norm_num [halfPlane]
  have heq : halfPlane.EqOn (LSeries (siegelProductCoefficients chi psi))
      (fun s => siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)) := by
    intro s hs
    have hsone : s ≠ 1 := by
      intro h
      subst s
      norm_num [halfPlane] at hs
    rw [siegelProduct_LSeries_eq chi psi hs]
    change _ = siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)
    rw [siegelPoleSubtracted_apply_of_ne chi psi hsone]
    rw [siegelLProduct]
    ring
  have hderiv := heq.iteratedDeriv_of_isOpen hopen m htwo
  have hregular : ContDiffAt ℂ m (siegelPoleSubtracted chi psi) 2 :=
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul).contDiff.contDiffAt
  have hpole : ContDiffAt ℂ m
      (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 := by
    fun_prop (disch := norm_num)
  change iteratedDeriv m (LSeries (siegelProductCoefficients chi psi)) 2 =
    iteratedDeriv m
      (siegelPoleSubtracted chi psi +
        fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 at hderiv
  rw [iteratedDeriv_add hregular hpole] at hderiv
  rw [siegelSourceCoefficient, siegelRegularCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, hderiv]
  calc
    (-1 : ℂ) ^ m *
          ((iteratedDeriv m (siegelPoleSubtracted chi psi) 2 +
            iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2) /
            (m.factorial : ℂ)) =
        (-1 : ℂ) ^ m *
            (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
          (-1 : ℂ) ^ m *
            (iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 /
              (m.factorial : ℂ)) := by ring
    _ = (-1 : ℂ) ^ m *
          (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
        siegelProductResidue chi psi := by
      have hpoleCoefficient := pole_source_coefficient (siegelProductResidue chi psi) m
      rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient] at hpoleCoefficient
      rw [hpoleCoefficient]

end BombieriVinogradov.SiegelWalfisz
