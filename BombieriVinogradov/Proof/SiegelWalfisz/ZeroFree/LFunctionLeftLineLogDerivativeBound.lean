import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLeftLineLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLeftLineReflection
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionThreeHalvesLogDerivativeBound

/-!
# L-function logarithmic derivative bound on the left line

This module combines the exact functional-equation reflection identity with
the right-line L-function bound and the gamma-factor bounds on both reflected
lines.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_LFunction_left_line_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N]
        {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {s : Complex}, s.re = -(1 : Real) / 2 ->
              norm (logDeriv chi.LFunction s) <=
                abs (Real.log N) +
                  C * Real.log (abs s.im + 2)) := by
  choose CRightL hCRightLPos hRightL using
    exists_norm_logDeriv_LFunction_le_log_of_re_eq_three_halves
  choose CRightGamma hCRightGammaPos hRightGamma using
    exists_norm_logDeriv_gammaFactor_le_log
  choose CLeftGamma hCLeftGammaPos hLeftGamma using
    exists_norm_logDeriv_gammaFactor_left_line_le_log
  let C : Real := CRightL + CRightGamma + CLeftGamma
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst chi hchi hPrimitive s hsRe
  have hReflection :=
    logDeriv_LFunction_left_line_eq_reflected hchi hPrimitive hsRe
  have hRightRe : (1 - s).re = (3 : Real) / 2 := by
    rw [Complex.sub_re, hsRe]
    norm_num
  have hRightLAt := hRightL (Inv.inv chi) hRightRe
  have hRightLAtScale :
      norm (logDeriv (Inv.inv chi).LFunction (1 - s)) <=
        CRightL * Real.log (abs s.im + 2) := by
    simpa using hRightLAt
  have hRightGammaAt :=
    hRightGamma (Inv.inv chi)
      (by rw [hRightRe]; norm_num)
      (by rw [hRightRe]; norm_num)
  have hRightGammaAtScale :
      norm (logDeriv (Inv.inv chi).gammaFactor (1 - s)) <=
        CRightGamma * Real.log (abs s.im + 2) := by
    simpa using hRightGammaAt
  have hLeftGammaAt := hLeftGamma chi hsRe
  rw [hReflection]
  calc
    norm
        (-((Real.log (N : Real) : Real) : Complex) -
          logDeriv (Inv.inv chi).LFunction (1 - s) -
          logDeriv (Inv.inv chi).gammaFactor (1 - s) -
          logDeriv chi.gammaFactor s) <=
        ((norm (-((Real.log (N : Real) : Real) : Complex)) +
          norm (logDeriv (Inv.inv chi).LFunction (1 - s))) +
          norm (logDeriv (Inv.inv chi).gammaFactor (1 - s))) +
          norm (logDeriv chi.gammaFactor s) := by
      calc
        norm
            (-((Real.log (N : Real) : Real) : Complex) -
              logDeriv (Inv.inv chi).LFunction (1 - s) -
              logDeriv (Inv.inv chi).gammaFactor (1 - s) -
              logDeriv chi.gammaFactor s) <=
            norm
                (-((Real.log (N : Real) : Real) : Complex) -
                  logDeriv (Inv.inv chi).LFunction (1 - s) -
                  logDeriv (Inv.inv chi).gammaFactor (1 - s)) +
              norm (logDeriv chi.gammaFactor s) :=
          norm_sub_le _ _
        _ <=
            (norm
                (-((Real.log (N : Real) : Real) : Complex) -
                  logDeriv (Inv.inv chi).LFunction (1 - s)) +
              norm (logDeriv (Inv.inv chi).gammaFactor (1 - s))) +
              norm (logDeriv chi.gammaFactor s) :=
          add_le_add (norm_sub_le _ _) (le_refl _)
        _ <=
            ((norm (-((Real.log (N : Real) : Real) : Complex)) +
              norm (logDeriv (Inv.inv chi).LFunction (1 - s))) +
              norm (logDeriv (Inv.inv chi).gammaFactor (1 - s))) +
              norm (logDeriv chi.gammaFactor s) :=
          add_le_add
            (add_le_add (norm_sub_le _ _) (le_refl _))
            (le_refl _)
    _ <=
        ((abs (Real.log N) +
          CRightL * Real.log (abs s.im + 2)) +
          CRightGamma * Real.log (abs s.im + 2)) +
          CLeftGamma * Real.log (abs s.im + 2) := by
      apply add_le_add
      apply add_le_add
      apply add_le_add
      exact le_of_eq (by
        simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs])
      exact hRightLAtScale
      exact hRightGammaAtScale
      exact hLeftGammaAt
    _ = abs (Real.log N) + C * Real.log (abs s.im + 2) := by
      dsimp [C]
      ring

end BombieriVinogradov.SiegelWalfisz
