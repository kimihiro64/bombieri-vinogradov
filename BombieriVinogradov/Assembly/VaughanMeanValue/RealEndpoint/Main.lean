import BombieriVinogradov.Assembly.VaughanMeanValue.RealEndpoint.Endpoint
import BombieriVinogradov.Assembly.VaughanMeanValue.RealEndpoint.Majorant

/-!
# Vaughan's Basic Mean Value Theorem

This module only assembles the exact endpoint identity, the natural cutoff
theorem, and the real-majorant comparison into the advertised existential
statement.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem vaughanMeanValue : VaughanMeanValueStatement := by
  refine Exists.intro 200000 (And.intro (by norm_num) ?_)
  intro x Q hx hQ
  rw [primitivePsiMean_eq_vaughanMean]
  have hfloor : 2 <= Nat.floor x := Nat.le_floor hx
  have hnatural := vaughanMean_le_sourceScale_nat (Nat.floor x) Q hfloor hQ
  have hmajorant := naturalMajorant_le_basicMeanValueMajorant x Q hx hQ
  calc
    vaughanMean (Nat.floor x) Q <=
        200000 * vaughanSourceScale (Nat.floor x) Q *
          vaughanLogScale (Nat.floor x) Q ^ 3 := hnatural
    _ = 200000 * (vaughanSourceScale (Nat.floor x) Q *
          vaughanLogScale (Nat.floor x) Q ^ 3) := by ring
    _ <= 200000 * basicMeanValueMajorant x Q :=
      mul_le_mul_of_nonneg_left hmajorant (by norm_num)

end BombieriVinogradov.VaughanMeanValue
