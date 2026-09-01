import Mathlib.Tactic

/-!
# Logarithmic normalization for Vaughan's cutoff

Every logarithm in the four Vaughan contributions is compared with the single
scale `log (X * Q)`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

def vaughanLogScale (X Q : Nat) : Real :=
  Real.log ((X : Real) * (Q : Real))

theorem two_le_cast_product (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    (2 : Real) <= (X : Real) * (Q : Real) := by
  have hXcast : (2 : Real) <= (X : Real) := by exact_mod_cast hX
  have hQcast : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
  nlinarith [mul_le_mul hXcast hQcast (by norm_num : (0 : Real) <= 1)
    (by positivity : (0 : Real) <= (X : Real))]

theorem half_le_vaughanLogScale (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    (1 / 2 : Real) <= vaughanLogScale X Q := by
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  exact hhalfLogTwo.trans
    (Real.log_le_log (by norm_num) (two_le_cast_product X Q hX hQ))

theorem log_X_le_vaughanLogScale (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log (X : Real) <= vaughanLogScale X Q := by
  unfold vaughanLogScale
  apply Real.log_le_log
  · exact_mod_cast (show 0 < X by omega)
  · have hQcast : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
    nlinarith [mul_le_mul_of_nonneg_left hQcast (by positivity : (0 : Real) <= (X : Real))]

theorem log_twoQ_le_vaughanLogScale (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log (2 * (Q : Real)) <= vaughanLogScale X Q := by
  unfold vaughanLogScale
  apply Real.log_le_log
  · exact mul_pos (by norm_num) (by exact_mod_cast (show 0 < Q by omega))
  · have hXcast : (2 : Real) <= (X : Real) := by exact_mod_cast hX
    have hQcast : 0 <= (Q : Real) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hXcast hQcast]

theorem log_X_add_one_le_two_vaughanLogScale
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log ((X + 1 : Nat) : Real) <= 2 * vaughanLogScale X Q := by
  have hXpos : 0 < (X : Real) := by exact_mod_cast (show 0 < X by omega)
  have hXOne : ((X + 1 : Nat) : Real) <= 2 * (X : Real) := by
    push_cast
    nlinarith [show (1 : Real) <= (X : Real) by exact_mod_cast (show 1 <= X by omega)]
  have hlogTwoX : Real.log (2 * (X : Real)) <= 2 * vaughanLogScale X Q := by
    rw [Real.log_mul (by norm_num : Ne (2 : Real) 0) hXpos.ne']
    have hlogTwo : Real.log 2 <= vaughanLogScale X Q :=
      Real.log_le_log (by norm_num) (two_le_cast_product X Q hX hQ)
    have hlogX := log_X_le_vaughanLogScale X Q hX hQ
    linarith
  exact (Real.log_le_log (by positivity) hXOne).trans hlogTwoX

theorem log_u_le_vaughanLogScale
    (u X Q : Nat) (hu : 1 <= u) (huX : u <= X) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log (u : Real) <= vaughanLogScale X Q := by
  have huXcast : (u : Real) <= (X : Real) := by exact_mod_cast huX
  apply (Real.log_le_log (by exact_mod_cast (show 0 < u by omega)) huXcast).trans
  exact log_X_le_vaughanLogScale X Q hX hQ

theorem log_u_add_one_le_two_vaughanLogScale
    (u X Q : Nat) (huX : u <= X) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log ((u + 1 : Nat) : Real) <= 2 * vaughanLogScale X Q := by
  have huXcast : ((u + 1 : Nat) : Real) <= ((X + 1 : Nat) : Real) := by
    exact_mod_cast Nat.add_le_add_right huX 1
  apply (Real.log_le_log (by positivity) huXcast).trans
  exact log_X_add_one_le_two_vaughanLogScale X Q hX hQ

end BombieriVinogradov.VaughanMeanValue
