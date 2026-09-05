import BombieriVinogradov.Assembly.PrimeCountingConversion.Main
import BombieriVinogradov.Definitions.Statement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false

/-!
# Bombieri--Vinogradov solution boundary

The theorem type is the exact consumer-facing proposition. Its proof is
supplied by the checked prime-counting assembly.
-/

namespace BombieriVinogradov

theorem bombieriVinogradov : _root_.BombieriVinogradov := by
  exact PrimeCountingConversion.weighted_to_prime_counting

end BombieriVinogradov
