import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalLevelCorrectionLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.RiemannZetaLogDerivativeUpperBound
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Principal-character logarithmic derivative in the high strip

This module transfers the zeta pole estimate through the finite Euler product
for the principal character at an arbitrary ambient level.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem principal_LFunction_eq_levelCorrection_mul_riemannZeta
    {N : Nat} [NeZero N] {s : Complex} (hs : s ≠ 1) :
    (1 : DirichletCharacter Complex N).LFunction s =
      principalLevelCorrection N s * riemannZeta s := by
  have hPrincipal :=
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
      (N := N) hs
  simpa [DirichletCharacter.LFunctionTrivChar,
    principalLevelCorrection, principalLevelCorrectionFactor]
    using hPrincipal

theorem logDeriv_principal_eq_levelCorrection_add_riemannZeta
    {N : Nat} [NeZero N] {s : Complex} (hs : 1 < s.re) :
    logDeriv (1 : DirichletCharacter Complex N).LFunction s =
      logDeriv (principalLevelCorrection N) s +
        logDeriv riemannZeta s := by
  have hsNe : s ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hCorrectionNe :=
    principalLevelCorrection_ne_zero (N := N) hs.le
  have hZetaNe := riemannZeta_ne_zero_of_one_lt_re hs
  have hEventually :
      Filter.EventuallyEq (nhds s)
        (1 : DirichletCharacter Complex N).LFunction
        (fun z => principalLevelCorrection N z * riemannZeta z) := by
    filter_upwards [
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    apply principal_LFunction_eq_levelCorrection_mul_riemannZeta
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hLogCongr := (logDeriv_congr_nhds hEventually).self_of_nhds
  calc
    logDeriv (1 : DirichletCharacter Complex N).LFunction s =
        logDeriv
          (fun z => principalLevelCorrection N z * riemannZeta z) s :=
      hLogCongr
    _ = logDeriv (principalLevelCorrection N) s +
        logDeriv riemannZeta s :=
      logDeriv_mul s hCorrectionNe hZetaNe
        (differentiableAt_principalLevelCorrection s)
        (differentiableAt_riemannZeta hsNe)

theorem exists_neg_re_logDeriv_principal_le_pole_add_logs :
    exists C : Real, 0 < C ∧
      forall {N : Nat} [NeZero N] {s : Complex},
        1 < s.re -> s.re ≤ 2 ->
          -(logDeriv (1 : DirichletCharacter Complex N).LFunction s).re ≤
            (1 / (s - 1)).re + Real.log N +
              C * Real.log (|s.im| + 2) := by
  obtain ⟨C, hCPos, hZeta⟩ :=
    exists_neg_re_logDeriv_riemannZeta_le_pole_add_log
  refine Exists.intro C (And.intro hCPos ?_)
  intro N _hN s hsLower hsUpper
  have hCorrectionNorm :=
    norm_logDeriv_principalLevelCorrection_le_log
      (N := N) hsLower.le
  have hCorrectionReal :
      -(logDeriv (principalLevelCorrection N) s).re ≤ Real.log N := by
    calc
      -(logDeriv (principalLevelCorrection N) s).re ≤
          |(logDeriv (principalLevelCorrection N) s).re| :=
        neg_le_abs _
      _ ≤ ‖logDeriv (principalLevelCorrection N) s‖ :=
        Complex.abs_re_le_norm _
      _ ≤ Real.log N := hCorrectionNorm
  have hZetaRaw := hZeta hsLower hsUpper
  have hZetaLog :
      -(logDeriv riemannZeta s).re ≤
        (1 / (s - 1)).re + C * Real.log (|s.im| + 2) := by
    simpa [logDeriv_apply, neg_div] using hZetaRaw
  rw [logDeriv_principal_eq_levelCorrection_add_riemannZeta hsLower]
  simp only [Complex.add_re]
  linarith

end BombieriVinogradov.SiegelWalfisz
