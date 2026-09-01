import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Logarithmic derivatives as von Mangoldt series

This module transfers Mathlib's twisted von Mangoldt identity from Dirichlet
series to the analytically continued Dirichlet L-function on `re s > 1`.
-/

set_option autoImplicit false

open ArithmeticFunction hiding log
open scoped LSeries.notation

namespace BombieriVinogradov.SiegelWalfisz

theorem neg_logDeriv_LFunction_eq_twist_vonMangoldt {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    -deriv chi.LFunction s / chi.LFunction s = L (↗chi * ↗Λ) s := by
  rw [chi.deriv_LFunction_eq_deriv_LSeries hs,
    chi.LFunction_eq_LSeries hs]
  exact (chi.LSeries_twist_vonMangoldt_eq hs).symm

end BombieriVinogradov.SiegelWalfisz
