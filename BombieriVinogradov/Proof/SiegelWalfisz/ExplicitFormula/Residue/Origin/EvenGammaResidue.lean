import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Ring

/-!
# Even gamma-factor residue at the origin
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

open Filter

theorem tendsto_self_mul_gammaFactor_zero_of_even
    {N : Nat} {chi : DirichletCharacter Complex N}
    (hEven : DirichletCharacter.Even chi) :
    Filter.Tendsto (fun s : Complex => s * chi.gammaFactor s)
      (nhdsWithin 0 (Compl.compl ({0} : Set Complex))) (nhds 2) := by
  have hGamma :
      Filter.Tendsto
        (fun z : Complex => z / 2 * Complex.Gamma (z / 2))
        (nhdsWithin 0 (Compl.compl ({0} : Set Complex))) (nhds 1) := by
    refine Complex.tendsto_self_mul_Gamma_nhds_zero.comp ?_
    rw [tendsto_nhdsWithin_iff,
      (by simp : nhds (0 : Complex) = nhds (0 / 2))]
    exact And.intro
      ((tendsto_id.div_const _).mono_left nhdsWithin_le_nhds)
      (eventually_of_mem self_mem_nhdsWithin
        (fun x hx => div_ne_zero hx two_ne_zero))
  have hPower :
      Filter.Tendsto
        (fun s : Complex => 2 * (Real.pi : Complex) ^ (-s / 2))
        (nhdsWithin 0 (Compl.compl ({0} : Set Complex))) (nhds 2) := by
    rw [(by simp :
      nhds (2 : Complex) =
        nhds (2 * (Real.pi : Complex) ^ (-(0 : Complex) / 2)))]
    refine Filter.Tendsto.mono_left
      (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    exact continuousAt_const.mul
      ((continuousAt_const_cpow
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).comp (by fun_prop))
  have hProduct := hPower.mul hGamma
  have hTwo : (2 : Complex) * 1 = 2 := by ring
  rw [hTwo] at hProduct
  convert hProduct using 2 with z
  rw [DirichletCharacter.gammaFactor, if_pos hEven]
  change z * ((Real.pi : Complex) ^ (-z / 2) *
    Complex.Gamma (z / 2)) = _
  ring_nf

end BombieriVinogradov.SiegelWalfisz
