import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.SelectableZeroLogDerivativeBound

/-!
# Primitive logarithmic-derivative bound without selected zeros

This is the empty-selected-set specialization of Strombergsson Lemma 11.3.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_logDeriv_bound :
    exists A : Real, 0 < A ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {s : Complex}, 1 < s.re -> s.re ≤ 2 ->
              -(logDeriv chi.LFunction s).re ≤
                A * (Real.log N + Real.log (|s.im| + 2)) := by
  obtain ⟨A, hAPos, hSelectable⟩ :=
    exists_primitive_selectableZero_logDeriv_bound
  refine Exists.intro A (And.intro hAPos ?_)
  intro N _hN hNLower chi hchi hPrimitive s hsLower hsUpper
  have hEmpty := hSelectable hNLower hchi hPrimitive hsLower hsUpper
    (∅ : Set (SymmetricCompletedZeroIndex chi))
  simpa using hEmpty

end BombieriVinogradov.SiegelWalfisz
