import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.LFunction
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Finite order of a nonprincipal Dirichlet L-function

This module propagates one nonzero value across the connected complex plane to
exclude infinite meromorphic order everywhere.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- A nonprincipal Dirichlet L-function is meromorphic on the complex plane. -/
theorem meromorphic_LFunction_of_ne_one
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) : Meromorphic chi.LFunction := by
  intro s
  exact ((DirichletCharacter.differentiable_LFunction hchi).analyticAt s).meromorphicAt

/-- A nonprincipal Dirichlet L-function has finite meromorphic order at every
point of the complex plane. -/
theorem meromorphicOrderAt_LFunction_ne_top
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (s : Complex) :
    Ne (meromorphicOrderAt chi.LFunction s) (Top.top : WithTop Int) := by
  have hMero := meromorphic_LFunction_of_ne_one hchi
  apply (hMero.exists_meromorphicOrderAt_ne_top_iff_forall).mp
  refine Exists.intro (2 : Complex) ?_
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hMero 2)).mpr
  have hValue : Ne (chi.LFunction (2 : Complex)) 0 :=
    chi.LFunction_ne_zero_of_one_le_re (Or.inl hchi) (by norm_num)
  have hContinuous : ContinuousAt chi.LFunction (2 : Complex) :=
    (DirichletCharacter.differentiable_LFunction hchi).continuous.continuousAt
  exact (ContinuousAt.eventually_ne hContinuous hValue).filter_mono inf_le_left

end BombieriVinogradov.SiegelWalfisz
