import PrimeNumberTheoremAnd.RectangleArgumentPrinciple

/-!
# Finite pole sets on complex rectangles

This module packages the compact-divisor argument that turns meromorphicity on
a finite rectangle into finiteness of its pole set.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.ComplexAnalysis

/-- A meromorphic function has only finitely many poles inside a finite complex
rectangle. -/
theorem finite_polesIn_rectangle (f : Complex -> Complex) (z w : Complex)
    (hMero : MeromorphicOn f (Complex.Rectangle z w)) :
    (Set.inter (Complex.Rectangle z w)
      {p | meromorphicOrderAt f p < 0}).Finite := by
  have hSupport :
      (MeromorphicOn.divisor f (Complex.Rectangle z w)).support.Finite :=
    divisor_support_rectangle_finite f z w
  refine hSupport.subset ?_
  intro p hp
  have hpRect := hp.1
  have hpPole : meromorphicOrderAt f p < 0 := by exact hp.2
  simp only [Function.mem_support, ne_eq]
  rw [MeromorphicOn.divisor_apply hMero hpRect]
  change Ne (WithTop.untopD 0 (meromorphicOrderAt f p)) 0
  intro hzero
  rcases WithTop.untopD_eq_self_iff.mp hzero with hOrder | hTop
  case inl => exact (ne_of_lt hpPole) hOrder
  case inr =>
    rw [hTop] at hpPole
    exact (not_lt_of_ge le_top) hpPole

end BombieriVinogradov.ComplexAnalysis
