import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.Main

/-!
# Exceptional-zero selection for the explicit formula

The effective zero-free region supplies one absolute constant for which an
optional exceptional zero can be chosen faithfully. Any such zero is unique
and has ordinary L-function analytic order one.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_exceptionalZeroChoice :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        chi ≠ 1 ->
          (forall rho sigma : Complex,
            IsExceptionalZero c chi rho ->
            IsExceptionalZero c chi sigma -> rho = sigma) ∧
          (forall rho : Complex, IsExceptionalZero c chi rho ->
            analyticOrderNatAt chi.LFunction rho = 1) ∧
          exists exceptional : Option Complex,
            IsExceptionalZeroChoice c chi exceptional := by
  obtain ⟨c, hcPos, hRegion⟩ := dirichletZeroFreeRegion
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN chi hchi
  have hCharacterRegion := hRegion chi hchi
  apply And.intro
  · intro rho sigma hrho hsigma
    rcases hrho with
      ⟨hrhoZero, hrhoReal, hrhoPos, _hrhoLtOne, hrhoClose⟩
    rcases hsigma with
      ⟨hsigmaZero, hsigmaReal, hsigmaPos, _hsigmaLtOne, hsigmaClose⟩
    have hrhoGap : 1 - rho.re ≤ c / Real.log N := by
      linarith
    have hsigmaGap : 1 - sigma.re ≤ c / Real.log N := by
      linarith
    exact hCharacterRegion.2.1 rho sigma hrhoPos hsigmaPos
      hrhoZero hsigmaZero hrhoReal hsigmaReal hrhoGap hsigmaGap
  · apply And.intro
    · intro rho hrho
      rcases hrho with
        ⟨hrhoZero, hrhoReal, hrhoPos, _hrhoLtOne, hrhoClose⟩
      have hrhoGap : 1 - rho.re ≤ c / Real.log N := by
        linarith
      exact hCharacterRegion.2.2 rho hrhoPos hrhoZero hrhoReal hrhoGap
    · classical
      by_cases hExists : exists rho : Complex, IsExceptionalZero c chi rho
      · exact Exists.intro (some (Classical.choose hExists))
          (Classical.choose_spec hExists)
      · exact Exists.intro none hExists

end BombieriVinogradov.SiegelWalfisz
