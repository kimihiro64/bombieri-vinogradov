import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions

/-!
# Scalar Perron error data

This module owns the difference between one scalar Perron-series term and its
step term, together with the exact majorant supplied by the scalar theorem.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The error between one scalar Perron-series term and its step term. -/
def scalarPerronErrorTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) (n : Nat) : Complex :=
  scalarPerronSeriesTerm chi x c T n - scalarPerronStepTerm chi x n

/-- The exact termwise majorant obtained from the scalar truncated Perron
estimate, including its separate endpoint branch. -/
def scalarPerronErrorMajorantTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n = 0 then 0 else
    norm (twistedMangoldtSequence chi n) *
      if (x : Real) / (n : Real) = 1 then c / (Real.pi * T)
      else ((x : Real) / (n : Real)) ^ c *
        min 1 (1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))))

end BombieriVinogradov.SiegelWalfisz
