import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.Main
import Mathlib.Analysis.Meromorphic.NormalForm
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Border integrability away from poles

This module proves that the original explicit-formula integrand is integrable
along any rectangle border containing no pole.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

private theorem horizontalPath_not_eventuallyConst
    (h x : Real) :
    Not (Filter.EventuallyConst
      (fun r : Real => (r : Complex) + (h : Complex) * Complex.I) (nhds x)) := by
  intro hc
  have hex := Filter.eventuallyConst_iff_exists_eventuallyEq.mp hc
  choose c hc using hex
  have hpath :
      HasDerivAt (fun r : Real => (r : Complex) + (h : Complex) * Complex.I) 1 x := by
    simpa using
      (Complex.ofRealCLM.hasDerivAt (x := x)).add_const
        ((h : Complex) * Complex.I)
  have hconst :
      HasDerivAt (fun r : Real => (r : Complex) + (h : Complex) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact one_ne_zero (hpath.unique hconst)

private theorem intervalIntegrable_of_codiscreteWithin_along_path
    {f g : Complex -> Complex} {R : Set Complex}
    (heq : Membership.mem (Filter.codiscreteWithin R)
      {s : Complex | f s = g s})
    {a b : Real} {p : Real -> Complex}
    (hpAnalytic : AnalyticOnNhd Real p (Set.uIcc a b))
    (hpNonconst :
      forall x, Membership.mem (Set.uIcc a b) x ->
        Not (Filter.EventuallyConst p (nhds x)))
    (hpMaps : Set.MapsTo p (Set.uIcc a b) R)
    (hg : IntervalIntegrable (fun x => g (p x)) MeasureTheory.volume a b) :
    IntervalIntegrable (fun x => f (p x)) MeasureTheory.volume a b := by
  apply hg.congr_ae
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  change Membership.mem (Filter.codiscreteWithin (Set.uIoc a b))
    {x : Real | g (p x) = f (p x)}
  have hpull : Membership.mem (Filter.codiscreteWithin (Set.uIoc a b))
      {x : Real | f (p x) = g (p x)} := by
    change Membership.mem (Filter.codiscreteWithin (Set.uIoc a b))
      (Set.preimage p {s : Complex | f s = g s})
    exact Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc
      (hpAnalytic.preimage_mem_codiscreteWithin hpNonconst
        (Filter.codiscreteWithin_mono
          (by
            intro s hs
            choose t ht hts using hs
            subst s
            exact hpMaps ht)
          heq))
  filter_upwards [hpull] with t ht
  exact ht.symm

/-- A meromorphic explicit-formula integrand is integrable on every rectangle
border that contains none of its poles. -/
theorem rectangleBorderIntegrable_explicitFormulaIntegrand
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (z w : Complex)
    (hpoles : Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt (explicitFormulaIntegrand chi x) p < 0}) :
    RectangleBorderIntegrable (explicitFormulaIntegrand chi x) z w := by
  let R : Set Complex := Complex.Rectangle z w
  let f : Complex -> Complex := explicitFormulaIntegrand chi x
  let fNF : Complex -> Complex := toMeromorphicNFOn f R
  have hfMeromorphic : MeromorphicOn f R := by
    simpa [f, R] using meromorphicOn_explicitFormulaIntegrand hchi x hx R
  have hfNF : MeromorphicNFOn fNF R := by
    simpa [fNF] using meromorphicNFOn_toMeromorphicNFOn f R
  have hfNFAnalytic : AnalyticOnNhd Complex fNF (RectangleBorder z w) := by
    intro p hpBorder
    have hpR : Membership.mem R p := by
      exact rectangleBorder_subset_rectangle z w hpBorder
    apply (hfNF hpR).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [show meromorphicOrderAt fNF p = meromorphicOrderAt f p by
      simpa [fNF] using meromorphicOrderAt_toMeromorphicNFOn hfMeromorphic hpR]
    apply le_of_not_gt
    intro hpPole
    exact Set.disjoint_left.mp hpoles hpBorder (by simpa [f] using hpPole)
  have hfNFIntegrable : RectangleBorderIntegrable fNF z w :=
    hfNFAnalytic.continuousOn.rectangleBorder_integrable
  have heq : Membership.mem (Filter.codiscreteWithin R)
      {s : Complex | f s = fNF s} := by
    simpa [Filter.EventuallyEq, Filter.Eventually, fNF] using
      (toMeromorphicNFOn_eqOn_codiscrete (f := f) (U := R) hfMeromorphic)
  have hBottom : IntervalIntegrable
      (fun t : Real => f ((t : Complex) + (z.im : Complex) * Complex.I))
      MeasureTheory.volume z.re w.re :=
    intervalIntegrable_of_codiscreteWithin_along_path heq
      (by
        intro t _
        exact (Complex.ofRealCLM.analyticAt t).add analyticAt_const)
      (fun t _ => horizontalPath_not_eventuallyConst z.im t)
      (by simpa [R] using mapsTo_rectangle_left_im z w)
      hfNFIntegrable.1
  have hTop : IntervalIntegrable
      (fun t : Real => f ((t : Complex) + (w.im : Complex) * Complex.I))
      MeasureTheory.volume z.re w.re :=
    intervalIntegrable_of_codiscreteWithin_along_path heq
      (by
        intro t _
        exact (Complex.ofRealCLM.analyticAt t).add analyticAt_const)
      (fun t _ => horizontalPath_not_eventuallyConst w.im t)
      (by simpa [R] using mapsTo_rectangle_right_im z w)
      hfNFIntegrable.2.1
  have hRight : IntervalIntegrable
      (fun t : Real => f ((w.re : Complex) + (t : Complex) * Complex.I))
      MeasureTheory.volume z.im w.im :=
    intervalIntegrable_of_codiscreteWithin_along_path heq
      (by
        intro t _
        exact analyticAt_const.add
          ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const))
      (fun t _ => verticalPath_not_eventuallyConst w.re t)
      (by simpa [R] using mapsTo_rectangle_right_re z w)
      hfNFIntegrable.2.2.1
  have hLeft : IntervalIntegrable
      (fun t : Real => f ((z.re : Complex) + (t : Complex) * Complex.I))
      MeasureTheory.volume z.im w.im :=
    intervalIntegrable_of_codiscreteWithin_along_path heq
      (by
        intro t _
        exact analyticAt_const.add
          ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const))
      (fun t _ => verticalPath_not_eventuallyConst z.re t)
      (by simpa [R] using mapsTo_rectangle_left_re z w)
      hfNFIntegrable.2.2.2
  exact And.intro hBottom (And.intro hTop (And.intro hRight hLeft))

end BombieriVinogradov.SiegelWalfisz
