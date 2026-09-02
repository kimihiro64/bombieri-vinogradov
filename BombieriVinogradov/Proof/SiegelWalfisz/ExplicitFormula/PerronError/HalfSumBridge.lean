import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions

/-!
# Half-weighted and inclusive character Chebyshev sums

This module isolates the endpoint correction between the half-weighted source
sum and the inclusive character Chebyshev sum used elsewhere in the project.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

/-- The half-weighted character Chebyshev sum is the inclusive sum minus half
of its endpoint coefficient. -/
theorem characterChebyshevHalfSum_eq_characterChebyshevSum_sub
    {N x : Nat} (chi : DirichletCharacter Complex N) (hx : 0 < x) :
    characterChebyshevHalfSum x chi =
      characterChebyshevSum x chi -
        (1 / 2 : Complex) * twistedMangoldtSequence chi x := by
  have hFull : characterChebyshevSum x chi =
      Finset.sum (Finset.Icc 1 x) (twistedMangoldtSequence chi) := by
    unfold characterChebyshevSum
    unfold BombieriVinogradov.VaughanMeanValue.psiCharacterSum
    apply Finset.sum_congr rfl
    intro n _
    unfold twistedMangoldtSequence
    ring
  have hxMem : Membership.mem (Finset.Icc 1 x) x :=
    Finset.mem_Icc.mpr (And.intro hx (le_refl x))
  have hDecomp := Finset.sum_erase_add (Finset.Icc 1 x)
    (twistedMangoldtSequence chi) hxMem
  rw [Finset.Icc_erase_right] at hDecomp
  unfold characterChebyshevHalfSum
  rw [hFull]
  rw [<- hDecomp]
  ring

end BombieriVinogradov.SiegelWalfisz
