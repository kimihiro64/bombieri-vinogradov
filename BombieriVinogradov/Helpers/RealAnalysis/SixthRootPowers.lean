import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Powers of the nonnegative sixth root

The natural cube and fourth power match the square root and the
two-thirds real power, including the zero endpoint.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem sixthRoot_cube_eq_sqrt {L : Real} (hL : 0 <= L) :
    (L ^ (1 / 6 : Real)) ^ (3 : Nat) = Real.sqrt L := by
  calc
    (L ^ (1 / 6 : Real)) ^ (3 : Nat) =
        (L ^ (1 / 6 : Real)) ^ (3 : Real) := (Real.rpow_natCast _ 3).symm
    _ = L ^ ((1 / 6 : Real) * 3) := (Real.rpow_mul hL (1 / 6) 3).symm
    _ = L ^ (1 / 2 : Real) := by norm_num
    _ = Real.sqrt L := (Real.sqrt_eq_rpow L).symm

theorem sixthRoot_fourth_eq_twoThirds {L : Real} (hL : 0 <= L) :
    (L ^ (1 / 6 : Real)) ^ (4 : Nat) = L ^ (2 / 3 : Real) := by
  calc
    (L ^ (1 / 6 : Real)) ^ (4 : Nat) =
        (L ^ (1 / 6 : Real)) ^ (4 : Real) := (Real.rpow_natCast _ 4).symm
    _ = L ^ ((1 / 6 : Real) * 4) := (Real.rpow_mul hL (1 / 6) 4).symm
    _ = L ^ (2 / 3 : Real) := by norm_num

end BombieriVinogradov.RealAnalysis
