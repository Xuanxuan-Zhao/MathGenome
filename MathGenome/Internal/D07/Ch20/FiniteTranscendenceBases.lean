import MathGenome.Internal.Specs.D07.Ch20.FiniteTranscendenceBases
import MathGenome.Internal.D07.Ch20.FiniteTranscendenceBasesTranscendenceBasisExtraction
import MathGenome.Internal.D07.Ch15.GenericUnsolvabilityAlgebraicExchange
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

/-!
Finite transcendence bases and their degree, paper.tex:6119–6145.
Extraction supplies finite degree above a selected independent subtuple.
Algebraicity over the field adjoin is equivalent to algebraicity over the
subalgebra adjoin, so such tuples are transcendence bases in Mathlib's sense.
Their cardinalities identify the canonical degree. Finite extensions compose
finite field generation, and contribute zero to the tower formula for degree.
-/

universe u v w

namespace D07.Ch20.FiniteTranscendenceBases

open Specs.D07.Ch20.FiniteTranscendenceBases

/-- Algebraicity over the generated FIELD gives maximal independence. -/
theorem independent_tuple_is_basis
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    {ι : Type*} {a : ι → L} (ha : AlgebraicIndependent K a)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range a)) L) :
    IsTranscendenceBasis K a := by
  exact ha.isTranscendenceBasis_iff_isAlgebraic.mpr
    (IntermediateField.isAlgebraic_adjoin_iff_top.mp halg)

/-- The finite basis length equals the canonical cardinal-valued degree. -/
theorem independent_tuple_length : IndependentTupleLength.{u, v} := by
  intro K L _ _ _ r a ha halg
  have hb := independent_tuple_is_basis K L ha halg
  have h : Algebra.trdeg K L = (r : Cardinal.{v}) := by
    simpa using hb.lift_cardinalMk_eq_trdeg.symm
  exact ⟨h, by simp [h]⟩

/-- Extract from finite FIELD generators, including an empty generating list. -/
theorem finite_basis_exists : FiniteBasisExists.{u, v} := by
  classical
  intro K L _ _ _ hfg
  let := hfg
  obtain ⟨s, hs⟩ := IntermediateField.fg_top K L
  let e : Fin s.card ≃ s := s.equivFin.symm
  let b : Fin s.card → L := fun i => (e i : L)
  have hrange : Set.range b = (s : Set L) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp [b]⟩
  obtain ⟨r, j, hb, halg, hfin⟩ :=
    FiniteTranscendenceBasesTranscendenceBasisExtraction.transcendence_basis_extraction
      K L s.card b (by rw [hrange]; exact hs)
  exact ⟨r, (fun i => b (j i)), hb.1, halg, hfin,
    (independent_tuple_length K L r _ hb.1 halg).1⟩

/-- Exchange bounds applied in both directions give uniqueness. -/
theorem basis_length_unique : BasisLengthUnique.{u, v} := by
  intro K L _ _ _ r s a b ha hfa hb hfb
  let := hfa
  let := hfb
  exact Nat.le_antisymm
    (D07.Ch15.GenericUnsolvabilityAlgebraicExchange.independent_cardinality_bound
      K L s r b a (inferInstance) ha)
    (D07.Ch15.GenericUnsolvabilityAlgebraicExchange.independent_cardinality_bound
      K L r s a b (inferInstance) hb)

/-- Finite algebraic extensions contribute zero to the transcendence tower law. -/
theorem finite_extension_invariance : FiniteExtensionInvariance.{u, v, w} := by
  intro K L E _ _ _ _ _ _ _ hfg hfin
  let := hfg
  let := hfin
  have hgen : Algebra.EssFiniteType K E := Algebra.EssFiniteType.comp K L E
  have hdeg : Cardinal.lift.{w} (Algebra.trdeg K L) =
      Cardinal.lift.{v} (Algebra.trdeg K E) := by
    simpa only [trdeg_eq_zero (R := L) (A := E), Cardinal.lift_zero, add_zero] using
      (lift_trdeg_add_eq K L E)
  refine ⟨hgen, hdeg, ?_⟩
  simpa using (congrArg Cardinal.toNat hdeg).symm

/-- The canonical rational function field has one independent variable per index. -/
theorem rational_function_field_degree : RationalFunctionFieldDegree.{u} := by
  intro K _ r
  let A := MvPolynomial (Fin r) K
  let F := FractionRing A
  let : Algebra.EssFiniteType A F :=
    Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  have hfg : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K A F
  let : Algebra.IsAlgebraic A F :=
    IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have hb : IsTranscendenceBasis K
      (algebraMap A F ∘ MvPolynomial.X (σ := Fin r) (R := K)) :=
    (IsTranscendenceBasis.mvPolynomial (Fin r) K).algebraMap_comp
  have h : Algebra.trdeg K F = (r : Cardinal.{u}) := by
    simpa using hb.lift_cardinalMk_eq_trdeg.symm
  exact ⟨hfg, h, by simpa only [Cardinal.toNat_natCast] using congrArg Cardinal.toNat h⟩

/-- Evaluation identifies any independently generated field with that fraction field. -/
theorem rational_adjoin_degree : RationalAdjoinDegree.{u, v} := by
  intro K L _ _ _ r a ha
  have hfg : Algebra.EssFiniteType K (IntermediateField.adjoin K (Set.range a)) :=
    inferInstance
  have hdeg := ha.aevalEquivField.lift_trdeg_eq
  have hrat := (rational_function_field_degree K r).2.1
  have h : Algebra.trdeg K (IntermediateField.adjoin K (Set.range a)) =
      (r : Cardinal.{v}) := by
    rw [hrat] at hdeg
    simpa using hdeg.symm
  exact ⟨hfg, h, by simpa only [Cardinal.toNat_natCast] using congrArg Cardinal.toNat h⟩

/-- Each nonzero polynomial equation supplies algebraicity, hence finite degree
for the finite collection of roots. Apply finite-extension invariance to it. -/
theorem adjoining_roots_preserves_degree : AdjoiningRootsPreservesDegree.{u, v, w} := by
  intro K L E _ _ _ _ _ _ _ m b p hfg hp hroot
  have hb : ∀ i, IsAlgebraic L (b i) := fun i => ⟨p i, hp i, hroot i⟩
  have hfin : Module.Finite L (IntermediateField.adjoin L (Set.range b)) := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro x ⟨i, rfl⟩
    exact (hb i).isIntegral
  let := hfin
  have h := finite_extension_invariance K L (IntermediateField.adjoin L (Set.range b)) hfg hfin
  exact ⟨hfin, inferInstance, h⟩

end D07.Ch20.FiniteTranscendenceBases
