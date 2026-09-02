import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.CandidateValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.RegularizedPoleTruncation

/-!
# Regularized poles are residue candidates

This module classifies every nonboundary regularized contour pole into the
finite residue candidate set.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Every regularized pole in the contour is either the origin, a retained
critical zero, or a value in the exceptional reflected pair. -/
theorem mem_residueCandidateValues_of_regularized_pole
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 0 < x) (U c T : Real)
    (hU : U < 1) (hT : 0 < T) (hRe : -U <= c)
    (exceptional : Option Complex) {rho : Complex}
    (hrhoRect : Membership.mem
      (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T)) rho)
    (hrhoBorder : Not (Membership.mem
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T)) rho))
    (hpole : meromorphicOrderAt
      (regularizedExplicitFormulaIntegrand chi x) rho < 0) :
    Membership.mem
      (explicitFormulaResidueCandidateValues chi T exceptional) rho := by
  rw [mem_explicitFormulaResidueCandidateValues_iff]
  by_cases hrhoZero : rho = 0
  case pos =>
    exact Or.inl hrhoZero
  case neg =>
    by_cases hRetained : IsRetainedZero exceptional rho
    case pos =>
      apply Or.inr
      apply Or.inl
      exact mem_retainedCriticalZeroValues_of_regularized_pole
        hchi hPrimitive x hx U c T hU hT hRe exceptional hrhoZero
        hRetained hrhoRect hrhoBorder hpole
    case neg =>
      apply Or.inr
      apply Or.inr
      exact mem_exceptionalZeroValues_iff.mpr hRetained

end BombieriVinogradov.SiegelWalfisz
