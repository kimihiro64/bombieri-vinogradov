import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.MajorantSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.StepSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.TermBound

/-!
# Summability of the scalar Perron errors

This module combines the termwise error estimate, its summable majorant, and
the finite-support step series.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The norms of the scalar Perron error terms form a summable sequence. -/
theorem summable_norm_scalarPerronErrorTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (fun n : Nat => norm (scalarPerronErrorTerm chi x c T n)) := by
  apply Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_scalarPerronErrorTerm_le_majorant chi hx
      (lt_trans zero_lt_one hc) hT n)
    (summable_scalarPerronErrorMajorantTerm chi hx hc hT)

/-- The scalar Perron error terms form an absolutely convergent series. -/
theorem summable_scalarPerronErrorTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (scalarPerronErrorTerm chi x c T) :=
  summable_norm_iff.mp (summable_norm_scalarPerronErrorTerm chi hx hc hT)

/-- The scalar Perron-series terms form a summable sequence. -/
theorem summable_scalarPerronSeriesTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (scalarPerronSeriesTerm chi x c T) := by
  have hFunction : scalarPerronSeriesTerm chi x c T = fun n : Nat =>
      scalarPerronErrorTerm chi x c T n + scalarPerronStepTerm chi x n := by
    funext n
    unfold scalarPerronErrorTerm
    ring
  rw [hFunction]
  exact (summable_scalarPerronErrorTerm chi hx hc hT).add
    (summable_scalarPerronStepTerm chi)

end BombieriVinogradov.SiegelWalfisz
