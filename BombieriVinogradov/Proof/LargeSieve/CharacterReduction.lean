import BombieriVinogradov.Proof.LargeSieve.GaussSum
import BombieriVinogradov.Proof.LargeSieve.SmoothMajorant

/-!
# Reduction from primitive characters to additive Farey samples

This module proves Vaughan's primitive Dirichlet-character large sieve from
the additive large sieve. The reduction uses the composite-modulus primitive
Gauss-sum norm, character Parseval on the unit group, and an exact translation
of arbitrary integer intervals to the coefficient convention used by the
Farey additive theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators ComplexConjugate

namespace BombieriVinogradov.LargeSieve

noncomputable local instance characterReductionUnitFintype
    (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- The real additive phase at an integral multiple of a reduced fraction is
Mathlib's standard additive character on the corresponding residue. -/
theorem additivePhase_int_unitFraction {q : Nat} [NeZero q]
    (n : Int) (u : (ZMod q)ˣ) :
    additivePhase ((n : Real) * (unitFraction u : Real)) =
      ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) := by
  rw [show (n : ZMod q) * (u : ZMod q) =
    (n * u.val.val : Int) by norm_num]
  rw [ZMod.stdAddChar_coe]
  rw [additivePhase, circleMap_zero]
  unfold unitFraction
  push_cast
  field_simp [NeZero.ne q]

/-- A Dirichlet-character-weighted sum over units equals the corresponding
sum over all residues, since character values vanish on nonunits. -/
theorem sum_units_eq_sum_residues {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (f : ZMod q -> Complex) :
    ∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u =
      ∑ x : ZMod q, chi x * f x := by
  classical
  let s : Finset (ZMod q) := Finset.univ.filter IsUnit
  have hunits : (∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u) =
      ∑ x ∈ s, chi x * f x := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
      (t := s) (fun u hu => (u : ZMod q))
    · intro u hu
      simp [s, u.isUnit]
    · intro u hu v hv huv
      exact Units.ext huv
    · intro x hx
      have hxunit : IsUnit x := by simpa [s] using hx
      exact ⟨hxunit.unit, Finset.mem_univ _, hxunit.unit_spec⟩
    · intro u hu
      rfl
  rw [hunits]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hxuniv hxnot
  have hxnonunit : ¬IsUnit x := by simpa [s] using hxnot
  rw [MulChar.map_nonunit chi hxnonunit, zero_mul]

/-- The additive interval sum at one reduced residue modulo `q`. -/
def intervalAdditiveResidueSum (a : Int -> Complex) (M : Int) (N q : Nat)
    [NeZero q] (u : (ZMod q)ˣ) : Complex :=
  ∑ n ∈ Ioc M (M + (N : Int)),
    a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))

/-- Primitive Gauss-sum inversion converts one multiplicative character sum
to a character transform of additive interval samples. -/
theorem gauss_mul_intervalCharacterSum {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi)
    (a : Int -> Complex) (M : Int) (N : Nat) :
    gaussSum chi⁻¹ ZMod.stdAddChar * intervalCharacterSum a M N q chi =
      unitCharacterSum (intervalAdditiveResidueSum a M N q) chi⁻¹ := by
  classical
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  have hshift (n : Int) :
      ∑ u : (ZMod q)ˣ,
          chi⁻¹ (u : ZMod q) *
            ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) =
        chi (n : ZMod q) * gaussSum chi⁻¹ ZMod.stdAddChar := by
    calc
      _ = ∑ x : ZMod q,
          chi⁻¹ x * ZMod.stdAddChar ((n : ZMod q) * x) :=
        sum_units_eq_sum_residues chi⁻¹ _
      _ = gaussSum chi⁻¹ (ZMod.stdAddChar.mulShift (n : ZMod q)) := by
        simp only [gaussSum, AddChar.mulShift_apply]
      _ = _ := by
        simpa using
          (gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hchiInv (n : ZMod q))
  unfold intervalCharacterSum unitCharacterSum intervalAdditiveResidueSum
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    gaussSum chi⁻¹ ZMod.stdAddChar * (a n * chi (n : ZMod q)) =
        a n * (chi (n : ZMod q) * gaussSum chi⁻¹ ZMod.stdAddChar) := by ring
    _ = a n * ∑ u : (ZMod q)ˣ,
        chi⁻¹ (u : ZMod q) * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) := by
      rw [hshift n]
    _ = ∑ u : (ZMod q)ˣ,
        a n * (chi⁻¹ (u : ZMod q) *
          ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))) := by
      rw [Finset.mul_sum]
    _ = ∑ u : (ZMod q)ˣ,
        a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) *
          chi⁻¹ (u : ZMod q) := by
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Squared-norm form of primitive Gauss-sum inversion. -/
theorem q_mul_norm_intervalCharacterSum_sq {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi)
    (a : Int -> Complex) (M : Int) (N : Nat) :
    (q : Real) * ‖intervalCharacterSum a M N q chi‖ ^ 2 =
      ‖unitCharacterSum (intervalAdditiveResidueSum a M N q) chi⁻¹‖ ^ 2 := by
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  calc
    (q : Real) * ‖intervalCharacterSum a M N q chi‖ ^ 2 =
        ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ ^ 2 *
          ‖intervalCharacterSum a M N q chi‖ ^ 2 := by
      rw [norm_gaussSum_stdAddChar_sq hchiInv]
    _ = ‖gaussSum chi⁻¹ ZMod.stdAddChar * intervalCharacterSum a M N q chi‖ ^ 2 := by
      rw [norm_mul]
      ring
    _ = _ := by
      rw [gauss_mul_intervalCharacterSum hchi a M N]

/-- Inversion permutes the finite set of primitive characters. -/
theorem sum_primitive_inv (q : Nat) (f : DirichletCharacter Complex q -> Real) :
    ∑ chi ∈ primitiveCharacters q, f chi⁻¹ =
      ∑ chi ∈ primitiveCharacters q, f chi := by
  classical
  apply Finset.sum_bij (s := primitiveCharacters q) (t := primitiveCharacters q)
    (fun chi hchi => chi⁻¹)
  · intro chi hchi
    have hprimitive : DirichletCharacter.IsPrimitive chi := by
      simpa [primitiveCharacters] using hchi
    have hinv : DirichletCharacter.IsPrimitive chi⁻¹ := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
      exact hprimitive
    simpa [primitiveCharacters] using hinv
  · intro chi hchi psi hpsi heq
    simpa only [inv_inv] using congrArg Inv.inv heq
  · intro psi hpsi
    refine ⟨psi⁻¹, ?_, ?_⟩
    · have hprimitive : DirichletCharacter.IsPrimitive psi := by
        simpa [primitiveCharacters] using hpsi
      have hinv : DirichletCharacter.IsPrimitive psi⁻¹ := by
        rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
        exact hprimitive
      simpa [primitiveCharacters] using hinv
    · simp
  · intro chi hchi
    rfl

/-- At a fixed positive modulus, the source weight `q / phi(q)` cancels
exactly against the Gauss norm and character Parseval constants. -/
theorem weightedPrimitiveCharacterSum_le_additive {q : Nat} [NeZero q]
    (a : Int -> Complex) (M : Int) (N : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
      ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2 := by
  classical
  let b : (ZMod q)ˣ -> Complex := intervalAdditiveResidueSum a M N q
  let S : Real := ∑ chi ∈ primitiveCharacters q,
    ‖intervalCharacterSum a M N q chi‖ ^ 2
  let E : Real := ∑ u : (ZMod q)ˣ, ‖b u‖ ^ 2
  have hscaled : (q : Real) * S =
      ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi⁻¹‖ ^ 2 := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hprimitive : DirichletCharacter.IsPrimitive chi := by
      simpa [primitiveCharacters] using hchi
    exact q_mul_norm_intervalCharacterSum_sq hprimitive a M N
  have hinv :
      (∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi⁻¹‖ ^ 2) =
        ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi‖ ^ 2 := by
    exact sum_primitive_inv q (fun chi => ‖unitCharacterSum b chi‖ ^ 2)
  have hparseval :
      ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi‖ ^ 2 <=
        (q.totient : Real) * E := by
    simpa [E] using primitiveCharacterParseval_le b
  have hcore : (q : Real) * S <= (q.totient : Real) * E := by
    rw [hscaled, hinv]
    exact hparseval
  have hphi : 0 < (q.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  change ((q : Real) / (q.totient : Real)) * S <= E
  calc
    ((q : Real) / (q.totient : Real)) * S =
        ((q : Real) * S) / (q.totient : Real) := by ring
    _ <= ((q.totient : Real) * E) / (q.totient : Real) := by
      exact (div_le_div_iff_of_pos_right hphi).2 hcore
    _ = E := by field_simp

/-- Reindex an integer interval of length `N` by `range N`. -/
theorem sum_int_Ioc_eq_sum_range {R : Type*} [AddCommMonoid R]
    (f : Int -> R) (M : Int) (N : Nat) :
    ∑ n ∈ Ioc M (M + (N : Int)), f n =
      ∑ k ∈ range N, f (M + (k : Int) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hle : M <= M + (N : Int) := by omega
      rw [Nat.cast_succ]
      rw [← add_assoc]
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hle]
      rw [Finset.sum_insert]
      · rw [Finset.sum_range_succ, ih]
        simp [add_comm, add_assoc]
      · simp

/-- Coefficients on `M < n <= M + N`, shifted to indices `0 <= k < N`. -/
def shiftedIntervalCoefficients (a : Int -> Complex) (M : Int) (k : Nat) : Complex :=
  a (M + (k : Int) + 1)

/-- Translation of an additive interval sum produces only a unit-norm common
phase, followed by the Farey sample of the shifted coefficients. -/
theorem intervalAdditiveResidueSum_eq_phase_mul_fareySample
    {Q q : Nat} [NeZero q] (hq : q ∈ Icc 1 Q)
    (a : Int -> Complex) (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    intervalAdditiveResidueSum a M N q u =
      additivePhase (((M + 1 : Int) : Real) * (unitFraction u : Real)) *
        fareyAdditiveSample (shiftedIntervalCoefficients a M) N ⟨⟨q, hq⟩, u⟩ := by
  rw [intervalAdditiveResidueSum, sum_int_Ioc_eq_sum_range]
  unfold fareyAdditiveSample shiftedIntervalCoefficients fareyValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← additivePhase_int_unitFraction (M + (k : Int) + 1) u]
  rw [show (((M + (k : Int) + 1 : Int) : Real) * (unitFraction u : Real)) =
      (((M + 1 : Int) : Real) * (unitFraction u : Real)) +
        ((k : Real) * (unitFraction u : Real)) by
    push_cast
    ring]
  rw [additivePhase_add]
  ring

/-- Norm form of interval translation, ready for the additive large sieve. -/
theorem norm_intervalAdditiveResidueSum_eq_fareySample
    {Q q : Nat} [NeZero q] (hq : q ∈ Icc 1 Q)
    (a : Int -> Complex) (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    ‖intervalAdditiveResidueSum a M N q u‖ =
      ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N ⟨⟨q, hq⟩, u⟩‖ := by
  rw [intervalAdditiveResidueSum_eq_phase_mul_fareySample hq a M N u]
  rw [norm_mul, norm_additivePhase, one_mul]

/-- Expand a sum over the explicit dependent Farey index into moduli and
units. -/
theorem sum_fareyIndices_eq_sum_attach {Q : Nat} (f : FareyIndex Q -> Real) :
    ∑ i ∈ fareyIndices Q, f i =
      ∑ q ∈ (Icc 1 Q).attach, ∑ u : (ZMod q.1)ˣ, f ⟨q, u⟩ := by
  unfold fareyIndices
  rw [Finset.sum_sigma]

/-- Total additive energy at one modulus, defined as zero at the unused
modulus `q = 0`. -/
def modulusAdditiveEnergy (a : Int -> Complex) (M : Int) (N q : Nat) : Real :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2

theorem modulusAdditiveEnergy_eq {q : Nat} [NeZero q]
    (a : Int -> Complex) (M : Int) (N : Nat) :
    modulusAdditiveEnergy a M N q =
      ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2 := by
  simp [modulusAdditiveEnergy, NeZero.ne q]

/-- The sum of fixed-modulus additive energies is exactly the Farey energy of
the shifted coefficient sequence. -/
theorem sum_modulusAdditiveEnergy_eq_fareySamples
    (Q : Nat) (a : Int -> Complex) (M : Int) (N : Nat) :
    ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q =
      ∑ i ∈ fareyIndices Q,
        ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N i‖ ^ 2 := by
  rw [sum_fareyIndices_eq_sum_attach]
  rw [← Finset.sum_attach (Icc 1 Q) (modulusAdditiveEnergy a M N)]
  apply Finset.sum_congr rfl
  intro q hqattach
  let _ : NeZero q.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp q.2).1⟩
  rw [modulusAdditiveEnergy_eq]
  apply Finset.sum_congr rfl
  intro u hu
  rw [norm_intervalAdditiveResidueSum_eq_fareySample q.2 a M N u]

/-- The primitive Dirichlet-character large sieve with explicit constant
`36`, including arbitrary integer interval origin. -/
theorem characterLargeSieveNat (M : Int) (N Q : Nat) (a : Int -> Complex)
    (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
      36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2 := by
  by_cases hNzero : N = 0
  · subst N
    simp [intervalCharacterSum]
  have hN : 0 < N := Nat.pos_of_ne_zero hNzero
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQ
  have hfixed :
      (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ‖intervalCharacterSum a M N q chi‖ ^ 2) <=
        ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := by
    apply Finset.sum_le_sum
    intro q hq
    let _ : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    rw [modulusAdditiveEnergy_eq]
    exact weightedPrimitiveCharacterSum_le_additive a M N
  calc
    _ <= ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := hfixed
    _ = ∑ i ∈ fareyIndices Q,
        ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N i‖ ^ 2 :=
      sum_modulusAdditiveEnergy_eq_fareySamples Q a M N
    _ <= 36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ k ∈ range N, ‖shiftedIntervalCoefficients a M k‖ ^ 2 :=
      additiveLargeSieve hQpos hN (shiftedIntervalCoefficients a M)
    _ = 36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2 := by
      rw [sum_int_Ioc_eq_sum_range (fun n => ‖a n‖ ^ 2) M N]
      rfl

/-- Vaughan's source-faithful character large-sieve statement. -/
theorem characterLargeSieve : CharacterLargeSieveStatement := by
  refine ⟨36, by norm_num, ?_⟩
  intro M N Q a hQ
  exact characterLargeSieveNat M N Q a hQ

end BombieriVinogradov.LargeSieve
