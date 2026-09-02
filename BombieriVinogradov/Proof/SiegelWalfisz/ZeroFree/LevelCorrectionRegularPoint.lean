import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionEulerProduct
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimeDivisorLogSum

/-!
# Level correction at regular points

This module extends the finite Euler-correction logarithmic-derivative bound
to every character at points strictly to the right of one. In particular, it
includes the principal character, whose primitive L-function is zeta.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_eq_primitive_mul_levelCorrection_of_ne_one_point
    {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    {s : Complex} (hs : s ≠ 1) :
    chi.LFunction s =
      chi.primitiveCharacter.LFunction s * levelCorrection chi s := by
  have hChange := _root_.DirichletCharacter.LFunction_changeLevel
    chi.conductor_dvd_level chi.primitiveCharacter (s := s) (.inr hs)
  rw [chi.changeLevel_primitiveCharacter] at hChange
  simpa [levelCorrection, levelCorrectionFactor] using hChange

theorem levelCorrection_ne_zero_of_one_lt_re
    {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    {s : Complex} (hs : 1 < s.re) :
    levelCorrection chi s ≠ 0 := by
  have hsNe : s ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hChiNe := _root_.DirichletCharacter.LFunction_ne_zero_of_one_le_re
    chi (.inr hsNe) hs.le
  intro hZero
  have hProduct :=
    LFunction_eq_primitive_mul_levelCorrection_of_ne_one_point chi hsNe
  rw [hZero, mul_zero] at hProduct
  exact hChiNe hProduct

theorem logDeriv_LFunction_eq_primitive_add_levelCorrection_of_one_lt_re
    {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    {s : Complex} (hs : 1 < s.re) :
    logDeriv chi.LFunction s =
      logDeriv chi.primitiveCharacter.LFunction s +
        logDeriv (levelCorrection chi) s := by
  have hsNe : s ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hPrimitiveNe :=
    _root_.DirichletCharacter.LFunction_ne_zero_of_one_le_re
      chi.primitiveCharacter (.inr hsNe) hs.le
  have hCorrectionNe := levelCorrection_ne_zero_of_one_lt_re chi hs
  have hEventually :
      Filter.EventuallyEq (nhds s) chi.LFunction
        (fun z =>
          chi.primitiveCharacter.LFunction z * levelCorrection chi z) := by
    filter_upwards [
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    apply LFunction_eq_primitive_mul_levelCorrection_of_ne_one_point chi
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hLogCongr := (logDeriv_congr_nhds hEventually).self_of_nhds
  have hPrimitiveDiff :=
    chi.primitiveCharacter.differentiableAt_LFunction s (.inl hsNe)
  have hCorrectionDiff :
      DifferentiableAt Complex (levelCorrection chi) s := by
    change DifferentiableAt Complex
      (fun z : Complex =>
        ∏ p ∈ N.primeFactors, levelCorrectionFactor chi p z) s
    exact DifferentiableAt.fun_finsetProd (fun p hp =>
      differentiableAt_levelCorrectionFactor chi
        (Nat.prime_of_mem_primeFactors hp) s)
  calc
    logDeriv chi.LFunction s =
        logDeriv (fun z =>
          chi.primitiveCharacter.LFunction z * levelCorrection chi z) s :=
      hLogCongr
    _ = logDeriv chi.primitiveCharacter.LFunction s +
        logDeriv (levelCorrection chi) s :=
      logDeriv_mul s hPrimitiveNe hCorrectionNe
        hPrimitiveDiff hCorrectionDiff

theorem logDeriv_levelCorrection_eq_sum_of_one_le_re
    {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    {s : Complex} (hs : 1 ≤ s.re) :
    logDeriv (levelCorrection chi) s =
      ∑ p ∈ N.primeFactors,
        logDeriv (levelCorrectionFactor chi p) s := by
  have hFactor : forall p, p ∈ N.primeFactors ->
      levelCorrectionFactor chi p s ≠ 0 := by
    intro p hp
    have hNorm := one_half_le_norm_levelCorrectionFactor chi
      (Nat.prime_of_mem_primeFactors hp) hs
    exact norm_pos_iff.mp ((by norm_num : (0 : Real) < 1 / 2).trans_le hNorm)
  change logDeriv
      (fun z : Complex =>
        ∏ p ∈ N.primeFactors, levelCorrectionFactor chi p z) s = _
  exact logDeriv_prod hFactor (fun p hp =>
    differentiableAt_levelCorrectionFactor chi
      (Nat.prime_of_mem_primeFactors hp) s)

theorem norm_logDeriv_LFunction_sub_primitive_le_log_of_one_lt_re
    {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    {s : Complex} (hs : 1 < s.re) :
    ‖logDeriv chi.LFunction s -
      logDeriv chi.primitiveCharacter.LFunction s‖ ≤ Real.log N := by
  have hSplit :=
    logDeriv_LFunction_eq_primitive_add_levelCorrection_of_one_lt_re
      chi hs
  have hDifference :
      logDeriv chi.LFunction s -
          logDeriv chi.primitiveCharacter.LFunction s =
        logDeriv (levelCorrection chi) s := by
    rw [hSplit]
    abel
  rw [hDifference, logDeriv_levelCorrection_eq_sum_of_one_le_re chi hs.le]
  calc
    ‖∑ p ∈ N.primeFactors,
        logDeriv (levelCorrectionFactor chi p) s‖ ≤
        ∑ p ∈ N.primeFactors,
          ‖logDeriv (levelCorrectionFactor chi p) s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ N.primeFactors, Real.log p :=
      Finset.sum_le_sum (fun p hp =>
        norm_logDeriv_levelCorrectionFactor_le_log chi
          (Nat.prime_of_mem_primeFactors hp) hs.le)
    _ ≤ Real.log N := sum_log_primeFactors_le_log N

end BombieriVinogradov.SiegelWalfisz
