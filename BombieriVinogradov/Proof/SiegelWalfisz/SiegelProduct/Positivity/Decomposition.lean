import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Expansion
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.PartialSum
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Tail
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Value

/-!
# Exact finite-plus-tail decomposition

This module rewrites the value below one as a positive partial sum, regular tail, and pole term.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_decomposition {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    siegelProductValue chi psi (1 - delta) =
      siegelSourcePartialSum chi psi cutoff (1 + delta) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta) -
          siegelProductResidue chi psi * ((1 + delta : ℝ) : ℂ) ^ cutoff / delta := by
  let s : ℂ := (1 - delta : ℝ)
  let t : ℝ := 1 + delta
  have hs : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    linarith
  have hexpansion := hasSum_siegelRegularCoefficient chi psi hchi hpsi hmul s
  have hsplit : siegelPoleSubtracted chi psi s =
      (∑ m ∈ Finset.range cutoff, siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff t := by
    have hsum := hexpansion.summable.sum_add_tsum_nat_add cutoff
    rw [hexpansion.tsum_eq] at hsum
    have hst : (2 - s : ℂ) = t := by
      dsimp [s, t]
      push_cast
      ring
    rw [hst] at hsum
    simpa only [regularCoefficientTail, Nat.add_comm] using hsum.symm
  have hsdef : (1 : ℂ) - delta = s := by
    dsimp [s]
    push_cast
    rfl
  have htdef : 1 + delta = t := rfl
  rw [hsdef, htdef]
  rw [siegelProductValue_eq_regular_add_pole chi psi hs, hsplit]
  rw [regularPartialSum_eq_source_sub_residue chi psi hchi hpsi hmul]
  have ht : (t : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [t] at hre
    norm_num at hre
    linarith
  rw [geom_sum_eq ht]
  dsimp [s, t]
  push_cast
  field_simp
  ring

end BombieriVinogradov.SiegelWalfisz
