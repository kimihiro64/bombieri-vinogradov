import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.CoefficientBridge
import Mathlib.Algebra.Field.GeomSum

/-!
# Finite positive part of the Siegel expansion

This module isolates the positive source partial sum and rewrites the corresponding regular sum.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

/-- The finite source expansion through `cutoff - 1`. -/
noncomputable def siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.range cutoff, siegelSourceCoefficient chi psi m * (t : ℂ) ^ m

/-- A nonempty source partial sum is at least its constant term, hence at least one. -/
theorem one_le_siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    {cutoff : ℕ} (hcutoff : 0 < cutoff) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℂ) ≤ siegelSourcePartialSum chi psi cutoff t := by
  calc
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 :=
      one_le_siegelSourceCoefficient_zero chi psi hchiSquare hpsiSquare
    _ = siegelSourceCoefficient chi psi 0 * (t : ℂ) ^ 0 := by simp
    _ ≤ ∑ m ∈ Finset.range cutoff,
        siegelSourceCoefficient chi psi m * (t : ℂ) ^ m := by
      exact Finset.single_le_sum
        (fun m _ => mul_nonneg
          (siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m)
          (pow_nonneg (by exact_mod_cast ht) m))
        (Finset.mem_range.mpr hcutoff)

/-- The regular partial sum is the positive source sum minus the residue geometric sum. -/
theorem regularPartialSum_eq_source_sub_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.range cutoff,
        siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) =
      siegelSourcePartialSum chi psi cutoff t -
        siegelProductResidue chi psi * ∑ m ∈ Finset.range cutoff, (t : ℂ) ^ m := by
  rw [siegelSourcePartialSum]
  simp_rw [siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

end BombieriVinogradov.SiegelWalfisz
