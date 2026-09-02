import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.ErrorDefinitions

/-!
# Source Perron-error majorant

This module removes the character from the exact termwise majorant, leaving
the von Mangoldt-weighted series estimated in Strombergsson Lemma 13.5.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The character-free Perron error term appearing in the source estimate. -/
def sourcePerronErrorMajorantTerm (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n = 0 then 0 else
    ArithmeticFunction.vonMangoldt n *
      if (x : Real) / (n : Real) = 1 then c / (Real.pi * T)
      else ((x : Real) / (n : Real)) ^ c *
        min 1 (1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))))

end BombieriVinogradov.SiegelWalfisz
