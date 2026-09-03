import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Data.Real.Basic

/-!
# A five-term norm bound with one subtraction

This generic triangle estimate keeps the uncentering residual in its exact
additive order while combining five independently supplied error bounds.
-/
set_option autoImplicit false

universe u

namespace BombieriVinogradov.ComplexAnalysis

theorem norm_add_sub_add_add_le_of_le
    {E : Type u} [SeminormedAddCommGroup E]
    {a b c d e : E} {A B C D F : Real}
    (ha : norm a <= A) (hb : norm b <= B) (hc : norm c <= C)
    (hd : norm d <= D) (he : norm e <= F) :
    norm (a + b - c + d + e) <= A + B + C + D + F := by
  have hAB : norm (a + b) <= A + B := norm_add_le_of_le ha hb
  have hABC : norm (a + b - c) <= A + B + C :=
    (norm_sub_le (a + b) c).trans (add_le_add hAB hc)
  have hABCD : norm (a + b - c + d) <= A + B + C + D :=
    norm_add_le_of_le hABC hd
  exact norm_add_le_of_le hABCD he

end BombieriVinogradov.ComplexAnalysis
