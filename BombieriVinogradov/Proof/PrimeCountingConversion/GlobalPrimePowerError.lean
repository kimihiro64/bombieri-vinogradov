import BombieriVinogradov.Proof.PrimeCountingConversion.PrimePowerError
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Global higher-prime-power error

Mathlib's global Chebyshev estimate supplies both sign and size.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The global higher-prime-power mass has Mathlib's explicit Chebyshev bound. -/
theorem global_primePower_error_bounds {N : Nat} (hN : 1 <= N) :
    And (0 <= WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N)
      (WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N <=
        2 * Real.sqrt (N : Real) * Real.log (N : Real)) := by
  rw [psiGlobal_eq_chebyshevPsi, thetaGlobalNat_eq_chebyshevTheta]
  have hNRaw : (((1 : Nat) : Real) <= (N : Real)) := Nat.cast_le.mpr hN
  have hNReal : (1 : Real) <= (N : Real) := by simpa only [Nat.cast_one] using hNRaw
  exact And.intro (sub_nonneg.mpr (Chebyshev.theta_le_psi (N : Real)))
    (Chebyshev.psi_sub_theta_le hNReal)

end BombieriVinogradov.PrimeCountingConversion
