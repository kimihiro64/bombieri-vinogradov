import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.Algebra
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.Logs
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanMeanAggregate
import Mathlib.Tactic

/-!
# Analytic interface for Vaughan cutoff optimization

The symbolic four-term mean estimate is reduced to four explicit inequalities
for one natural cutoff. Algebraic absorption and logarithmic normalization stay
owned by separate inward modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

def vaughanSourceScale (X Q : Nat) : Real :=
  (X : Real) + (X : Real) ^ (5 / 6 : Real) * (Q : Real) +
    Real.sqrt (X : Real) * (Q : Real) ^ 2

theorem vaughanMean_le_of_cutoff_bounds
    (u X Q : Nat) (hu : 1 <= u) (huX : u <= X) (hX : 2 <= X) (hQ : 1 <= Q)
    (hsmall : (u : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) <=
      vaughanSourceScale X Q)
    (hinverse : (X : Real) * (Q : Real) / Real.sqrt (u : Real) <=
      vaughanSourceScale X Q)
    (hforward : (u : Real) * Real.sqrt (X : Real) * (Q : Real) <=
      vaughanSourceScale X Q)
    (hshort : (u : Real) * (Q : Real) ^ 2 <= vaughanSourceScale X Q) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  apply (vaughanMean_le_preoptimized u X Q hu hX hQ).trans
  dsimp [typeITwoSourceCore, typeIISourceCore]
  let S : Real := vaughanSourceScale X Q
  have hS : 0 <= S := by dsimp [S, vaughanSourceScale]; positivity
  have hXscale : (X : Real) <= S := by
    dsimp [S, vaughanSourceScale]
    have hmiddle : 0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
    have hlast : 0 <= Real.sqrt (X : Real) * (Q : Real) ^ 2 := by positivity
    linarith
  have hsqrtScale : Real.sqrt (X : Real) * (Q : Real) ^ 2 <= S := by
    dsimp [S, vaughanSourceScale]
    have hfirst : 0 <= (X : Real) := by positivity
    have hmiddle : 0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
    linarith
  have hsmall' : (u : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) <= S := by
    exact hsmall
  have hinverse' : (X : Real) * (Q : Real) / Real.sqrt (u : Real) <= S := by
    exact hinverse
  have hforward' : (u : Real) * Real.sqrt (X : Real) * (Q : Real) <= S := by
    exact hforward
  have hshort' : (u : Real) * (Q : Real) ^ 2 <= S := by exact hshort
  have habsorb := absorb_vaughan_terms
    (x := (X : Real))
    (a := (u : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real))
    (b := (X : Real) * (Q : Real) / Real.sqrt (u : Real))
    (c := (u : Real) * Real.sqrt (X : Real) * (Q : Real))
    (d := Real.sqrt (X : Real) * (Q : Real) ^ 2)
    (short := (u : Real) * (Q : Real) ^ 2)
    (logX := Real.log (X : Real))
    (logXOne := Real.log ((X + 1 : Nat) : Real))
    (logTwoQ := Real.log (2 * (Q : Real)))
    (logu := Real.log (u : Real))
    (loguOne := Real.log ((u + 1 : Nat) : Real))
    (L := vaughanLogScale X Q) (S := S)
    (half_le_vaughanLogScale X Q hX hQ)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (Real.log_natCast_nonneg X) (Real.log_natCast_nonneg (X + 1))
    (by apply Real.log_nonneg; nlinarith [show (1 : Real) <= (Q : Real) by exact_mod_cast hQ])
    (Real.log_natCast_nonneg u) (Real.log_natCast_nonneg (u + 1)) hS
    hXscale hsmall' hinverse' hforward' hsqrtScale hshort'
    (log_X_le_vaughanLogScale X Q hX hQ)
    (log_X_add_one_le_two_vaughanLogScale X Q hX hQ)
    (log_twoQ_le_vaughanLogScale X Q hX hQ)
    (log_u_le_vaughanLogScale u X Q hu huX hX hQ)
    (log_u_add_one_le_two_vaughanLogScale u X Q huX hX hQ)
  dsimp [S] at habsorb
  simpa only [mul_assoc, mul_comm, mul_left_comm] using habsorb

end BombieriVinogradov.VaughanMeanValue
