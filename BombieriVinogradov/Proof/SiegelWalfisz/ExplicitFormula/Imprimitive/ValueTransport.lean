import BombieriVinogradov.Helpers.ComplexAnalysis.DivisorIndexTransport
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Transporting retained zero values at equal positive-half-plane multiplicity

The value, strict strip, ordinate cutoff and optional exclusions are kept
unchanged. Only the finite divisor-index label is transported.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem mem_retainedCriticalZeroValues_of_completedMultiplicity_eq
    {N M : Nat} [NeZero N] [NeZero M]
    (chi : DirichletCharacter Complex N) (psi : DirichletCharacter Complex M)
    (hCount : forall s : Complex, 0 < s.re ->
      Int.toNat (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
        (Set.univ : Set Complex) s) =
      Int.toNat (MeromorphicOn.divisor (symmetricCompletedLFunction psi)
        (Set.univ : Set Complex) s))
    (T : Real) (exceptional : Option Complex) {rho : Complex}
    (hrho : (retainedCriticalZeroValues chi T exceptional : Set Complex) rho) :
    (retainedCriticalZeroValues psi T exceptional : Set Complex) rho := by
  classical
  have hWitness := Finset.mem_image.mp hrho
  let p : SymmetricCompletedZeroIndex chi := hWitness.choose
  have hp : (retainedCriticalZeroIndices chi T exceptional :
      Set (SymmetricCompletedZeroIndex chi)) p := hWitness.choose_spec.1
  have hpValue : symmetricCompletedZeroValue p = rho := hWitness.choose_spec.2
  have hParts := mem_retainedCriticalZeroIndices_iff.mp hp
  have hStrip := mem_criticalStripZeroTruncation_iff.mp hParts.1
  have hRe : 0 < (symmetricCompletedZeroValue p).re := hStrip.1
  have hMove :=
    BombieriVinogradov.ComplexAnalysis.exists_nonzeroDivisorIndex_of_multiplicity_eq
      (g := symmetricCompletedLFunction psi) p
      (hCount (symmetricCompletedZeroValue p) hRe)
  let q : SymmetricCompletedZeroIndex psi := hMove.choose
  have hqValue : symmetricCompletedZeroValue q = symmetricCompletedZeroValue p :=
    hMove.choose_spec
  have hqTruncated : (criticalStripZeroTruncation psi T :
      Set (SymmetricCompletedZeroIndex psi)) q := by
    apply mem_criticalStripZeroTruncation_iff.mpr
    change And (0 < (symmetricCompletedZeroValue q).re)
      (And ((symmetricCompletedZeroValue q).re < 1)
        (abs (symmetricCompletedZeroValue q).im < T))
    rw [hqValue]
    exact hStrip
  have hqKept : IsRetainedZero exceptional (symmetricCompletedZeroValue q) := by
    rw [hqValue]
    exact hParts.2
  have hqRetained : (retainedCriticalZeroIndices psi T exceptional :
      Set (SymmetricCompletedZeroIndex psi)) q :=
    mem_retainedCriticalZeroIndices_iff.mpr (And.intro hqTruncated hqKept)
  exact Finset.mem_image.mpr
    (Exists.intro q (And.intro hqRetained (hqValue.trans hpValue)))

theorem retainedCriticalZeroValues_eq_of_completedMultiplicity_eq
    {N M : Nat} [NeZero N] [NeZero M]
    (chi : DirichletCharacter Complex N) (psi : DirichletCharacter Complex M)
    (hCount : forall s : Complex, 0 < s.re ->
      Int.toNat (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
        (Set.univ : Set Complex) s) =
      Int.toNat (MeromorphicOn.divisor (symmetricCompletedLFunction psi)
        (Set.univ : Set Complex) s))
    (T : Real) (exceptional : Option Complex) :
    retainedCriticalZeroValues chi T exceptional =
      retainedCriticalZeroValues psi T exceptional := by
  classical
  apply Finset.ext
  intro rho
  exact Iff.intro
    (fun h => mem_retainedCriticalZeroValues_of_completedMultiplicity_eq
      chi psi hCount T exceptional h)
    (fun h => mem_retainedCriticalZeroValues_of_completedMultiplicity_eq
      psi chi (fun s hs => (hCount s hs).symm) T exceptional h)

end BombieriVinogradov.SiegelWalfisz
