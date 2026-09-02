import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.MajorantSummable

/-!
# Summability of the source Perron majorant

The modulus-one Dirichlet character is identically one, so the source
von Mangoldt majorant is an instance of the already summable exact majorant.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Twisting by the modulus-one character leaves the norm of each von
Mangoldt coefficient unchanged. -/
theorem norm_twistedMangoldtSequence_one_eq (n : Nat) :
    norm (twistedMangoldtSequence (1 : DirichletCharacter Complex 1) n) =
      ArithmeticFunction.vonMangoldt n := by
  unfold twistedMangoldtSequence
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hOneFunction :
      ((fun m : Nat => (1 : DirichletCharacter Complex 1) m) : Nat -> Complex) = 1 :=
    DirichletCharacter.modOne_eq_one
  have hOneValue : (1 : DirichletCharacter Complex 1) n = 1 := by
    simpa using congrFun hOneFunction n
  rw [hOneValue, norm_one, one_mul]

/-- The source von Mangoldt Perron majorant is summable for every `c > 1`. -/
theorem summable_sourcePerronErrorMajorantTerm
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (sourcePerronErrorMajorantTerm x c T) := by
  have hFunction : sourcePerronErrorMajorantTerm x c T =
      scalarPerronErrorMajorantTerm
        (1 : DirichletCharacter Complex 1) x c T := by
    funext n
    unfold sourcePerronErrorMajorantTerm
    unfold scalarPerronErrorMajorantTerm
    rw [norm_twistedMangoldtSequence_one_eq]
  rw [hFunction]
  exact summable_scalarPerronErrorMajorantTerm
    (1 : DirichletCharacter Complex 1) hx hc hT

end BombieriVinogradov.SiegelWalfisz
