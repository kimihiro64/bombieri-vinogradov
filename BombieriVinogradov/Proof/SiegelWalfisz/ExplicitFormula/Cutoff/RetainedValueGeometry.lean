import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Geometry of a retained zero value

The finite value image preserves the strict critical strip and the
height bound carried by each multiplicity index.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem retainedCriticalZeroValue_mem_strip
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {exceptional : Option Complex} {rho : Complex}
    (hrho : (retainedCriticalZeroValues chi T exceptional : Set Complex) rho) :
    And (0 < rho.re) (And (rho.re < 1) (abs rho.im < T)) := by
  classical
  have hWitness := Finset.mem_image.mp hrho
  let p : SymmetricCompletedZeroIndex chi := hWitness.choose
  have hp : (retainedCriticalZeroIndices chi T exceptional :
      Set (SymmetricCompletedZeroIndex chi)) p := hWitness.choose_spec.1
  have hValue : symmetricCompletedZeroValue p = rho := hWitness.choose_spec.2
  have hParts := mem_retainedCriticalZeroIndices_iff.mp hp
  have hStrip := mem_criticalStripZeroTruncation_iff.mp hParts.1
  change And (0 < (symmetricCompletedZeroValue p).re)
    (And ((symmetricCompletedZeroValue p).re < 1)
      (abs (symmetricCompletedZeroValue p).im < T)) at hStrip
  rw [hValue] at hStrip
  exact hStrip

end BombieriVinogradov.SiegelWalfisz
