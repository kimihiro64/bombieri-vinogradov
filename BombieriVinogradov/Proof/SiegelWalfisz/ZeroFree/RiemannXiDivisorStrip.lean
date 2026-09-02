import Robin1984.NicolasLandau.XiDivisorCriticalLine

/-!
# The critical strip for Riemann xi divisor zeros

This module places every multiplicity-indexed nonzero zero of Riemann's xi
function strictly between real parts zero and one.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

open Complex

theorem riemannXiDivisorZeroValue_re_mem_Ioo
    (p : RiemannXiDivisorZeroIndex) :
    (riemannXiDivisorZeroValue p).re ∈ Set.Ioo 0 1 := by
  let rho : Complex := riemannXiDivisorZeroValue p
  have hRhoZero : rho ≠ 0 :=
    riemannXiDivisorZeroValue_ne_zero p
  have hXi : riemannXi rho = 0 :=
    riemannXiDivisorZeroValue_eq_zero p
  have hXiOne : riemannXi (1 : Complex) = 1 / 2 := by
    simpa [riemannXi_zero] using (riemannXi_one_sub (0 : Complex))
  have hRhoOne : rho ≠ 1 := by
    intro h
    rw [h, hXiOne] at hXi
    norm_num at hXi
  have hZeta : riemannZeta rho = 0 :=
    Robin1984.riemannZeta_eq_zero_of_riemannXi_eq_zero
      hRhoZero hRhoOne hXi
  have hUpper : rho.re < 1 := by
    by_contra hNot
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hNot) hZeta
  have hLower : 0 < rho.re := by
    by_contra hNot
    have hMirrorXi : riemannXi (1 - rho) = 0 := by
      rw [riemannXi_one_sub]
      exact hXi
    have hMirrorZero : 1 - rho ≠ 0 :=
      sub_ne_zero.mpr hRhoOne.symm
    have hMirrorOne : 1 - rho ≠ 1 := by
      intro h
      apply hRhoZero
      exact sub_eq_self.mp h
    have hMirrorZeta : riemannZeta (1 - rho) = 0 :=
      Robin1984.riemannZeta_eq_zero_of_riemannXi_eq_zero
        hMirrorZero hMirrorOne hMirrorXi
    have hMirrorRe : 1 ≤ (1 - rho).re := by
      change 1 ≤ 1 - rho.re
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hMirrorRe hMirrorZeta
  exact Set.mem_Ioo.mpr (And.intro hLower hUpper)

end BombieriVinogradov.SiegelWalfisz
