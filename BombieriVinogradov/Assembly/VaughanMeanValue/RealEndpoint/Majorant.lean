import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff
import Mathlib.Tactic

/-!
# Floor endpoint and real majorant comparison

This outward assembly module compares the natural source and logarithmic scales at `floor x`
with the advertised real-`x` Basic Mean Value majorant. Endpoint identity and
final existential assembly are owned separately.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem naturalScale_le_realScale
    (x : Real) (Q : Nat) (hx : 2 <= x) :
    vaughanSourceScale (Nat.floor x) Q <=
      x + x ^ (5 / 6 : Real) * (Q : Real) +
        x ^ (1 / 2 : Real) * (Q : Real) ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hfloor : ((Nat.floor x : Nat) : Real) <= x := Nat.floor_le hx0
  have hfloor0 : (0 : Real) <= (Nat.floor x : Nat) := by positivity
  have hq0 : (0 : Real) <= (Q : Real) := by positivity
  have hpow := Real.rpow_le_rpow hfloor0 hfloor
    (by norm_num : (0 : Real) <= 5 / 6)
  have hmiddle := mul_le_mul_of_nonneg_right hpow hq0
  have hsqrt : Real.sqrt ((Nat.floor x : Nat) : Real) <= x ^ (1 / 2 : Real) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hfloor
  have hlast := mul_le_mul_of_nonneg_right hsqrt (sq_nonneg (Q : Real))
  dsimp [vaughanSourceScale]
  linarith

theorem naturalLogScale_le_realLog
    (x : Real) (Q : Nat) (hx : 2 <= x) (hQ : 1 <= Q) :
    vaughanLogScale (Nat.floor x) Q <= Real.log (x * (Q : Real)) := by
  have hx0 : 0 <= x := by linarith
  have hfloor : ((Nat.floor x : Nat) : Real) <= x := Nat.floor_le hx0
  have hfloorNat : 2 <= Nat.floor x := Nat.le_floor hx
  have hq0 : (0 : Real) <= (Q : Real) := by positivity
  unfold vaughanLogScale
  apply Real.log_le_log
  · have hfloorPos : (0 : Real) < (Nat.floor x : Nat) := by exact_mod_cast (show 0 < Nat.floor x by omega)
    have hqPos : (0 : Real) < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
    positivity
  · exact mul_le_mul_of_nonneg_right hfloor hq0

theorem naturalMajorant_le_basicMeanValueMajorant
    (x : Real) (Q : Nat) (hx : 2 <= x) (hQ : 1 <= Q) :
    vaughanSourceScale (Nat.floor x) Q *
        vaughanLogScale (Nat.floor x) Q ^ 3 <=
      basicMeanValueMajorant x Q := by
  have hfloorNat : 2 <= Nat.floor x := Nat.le_floor hx
  have hsource := naturalScale_le_realScale x Q hx
  have hlog := naturalLogScale_le_realLog x Q hx hQ
  have hnaturalLog0 : 0 <= vaughanLogScale (Nat.floor x) Q :=
    (by norm_num : (0 : Real) <= 1 / 2).trans
      (half_le_vaughanLogScale (Nat.floor x) Q hfloorNat hQ)
  have hrealLog0 : 0 <= Real.log (x * (Q : Real)) := hnaturalLog0.trans hlog
  have hlogPow := pow_le_pow_left₀ hnaturalLog0 hlog 3
  have hrealScale0 :
      0 <= x + x ^ (5 / 6 : Real) * (Q : Real) +
        x ^ (1 / 2 : Real) * (Q : Real) ^ 2 := by positivity
  have hproduct := mul_le_mul hsource hlogPow
    (pow_nonneg hnaturalLog0 3) hrealScale0
  simpa [basicMeanValueMajorant] using hproduct

end BombieriVinogradov.VaughanMeanValue
