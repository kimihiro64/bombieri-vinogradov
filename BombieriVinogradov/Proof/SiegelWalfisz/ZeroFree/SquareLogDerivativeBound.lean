import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.NonprincipalLogDerivativeBound

/-!
# The logarithmic-derivative bound for a squared character

This module specializes the ambient nonprincipal estimate to the squared
character appearing in Strombergsson's trigonometric positivity argument.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_square_logDeriv_bound :
    exists A : Real, 0 < A ∧
      forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        chi ^ 2 ≠ 1 ->
          forall {s : Complex}, 1 < s.re -> s.re ≤ 2 ->
            -(logDeriv (chi ^ 2).LFunction s).re ≤
              A * (Real.log N + Real.log (|s.im| + 2)) := by
  obtain ⟨A, hAPos, hGeneral⟩ := exists_nonprincipal_logDeriv_bound
  refine Exists.intro A (And.intro hAPos ?_)
  intro N _hN chi hSquare s hsLower hsUpper
  exact hGeneral hSquare hsLower hsUpper

end BombieriVinogradov.SiegelWalfisz
