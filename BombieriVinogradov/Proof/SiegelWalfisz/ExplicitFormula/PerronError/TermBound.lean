import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Main
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.ErrorDefinitions

/-!
# Termwise Perron error bound

This module transfers the scalar truncated Perron estimate to one twisted von
Mangoldt coefficient.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Each twisted Dirichlet coefficient times its scalar Perron error is bounded
by the corresponding exact source majorant. -/
theorem norm_scalarPerronErrorTerm_le_majorant
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (hT : 0 < T) (n : Nat) :
    norm (scalarPerronErrorTerm chi x c T n) <=
      scalarPerronErrorMajorantTerm chi x c T n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [scalarPerronErrorTerm, scalarPerronErrorMajorantTerm,
      scalarPerronSeriesTerm, scalarPerronStepTerm]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    have hPerron := norm_truncatedPerronKernel_sub_stepWeight_lt
      hRatioPos hc hT
    rw [scalarPerronErrorTerm, scalarPerronSeriesTerm,
      scalarPerronStepTerm, if_neg hn, if_neg hn,
      scalarPerronErrorMajorantTerm, if_neg hn]
    have hFactor :
        twistedMangoldtSequence chi n *
            truncatedPerronKernel ((x : Real) / (n : Real)) c T -
          twistedMangoldtSequence chi n *
            (perronStepWeight ((x : Real) / (n : Real)) : Complex) =
        twistedMangoldtSequence chi n *
          (truncatedPerronKernel ((x : Real) / (n : Real)) c T -
            (perronStepWeight ((x : Real) / (n : Real)) : Complex)) := by
      ring
    rw [hFactor, norm_mul]
    exact mul_le_mul_of_nonneg_left hPerron.le (norm_nonneg _)

end BombieriVinogradov.SiegelWalfisz
