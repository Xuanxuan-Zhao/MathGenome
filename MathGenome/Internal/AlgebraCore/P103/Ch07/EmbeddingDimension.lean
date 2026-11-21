import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.EmbeddingDimension
import MathGenome.Internal.AlgebraCore.P103.Ch06.KrullHeight
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Spectrum.Prime.LTSeries

namespace P103.Ch07.EmbeddingDimension

universe u v
open IsLocalRing Module
open P103.Specs.Ch07.EmbeddingDimension
open P103.Specs.Ch06.DimensionConventions

noncomputable def embeddingDimension : EmbeddingDimensionType.{u} := embeddingDimensionValue
noncomputable def regularLocal : RegularLocalType.{u} := regularLocalValue

theorem finite_dimension : finite_dimensionType.{u} := by
  intro R _ _ _
  exact ⟨inferInstance, (Module.finrank_eq_rank _ _).symm⟩

theorem generators_iff_ideal_span : generators_iff_ideal_spanType.{u,v} := by
  intro R _ _ ι x
  unfold GeneratesMaximalIdeal
  rw [← (Submodule.map_injective_of_injective (Submodule.injective_subtype _)).eq_iff,
    Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  rfl

theorem span_iff : span_iffType.{u,v} := by
  intro R _ _ _ ι x
  rw [show Set.range (fun i => (maximalIdeal R).toCotangent (x i)) =
    (maximalIdeal R).toCotangent '' Set.range x from Set.range_comp _ _]
  exact CotangentSpace.span_image_eq_top_iff

theorem basis_lifts : basis_liftsType.{u,v} := by
  intro R _ _ _ ι b x hx
  apply (span_iff R ι x).mp
  simpa only [hx] using b.span_eq

theorem generator_lower_bound : generator_lower_boundType.{u,v} := by
  intro R _ _ _ ι _ x hx
  exact finrank_le_of_span_eq_top ((span_iff R ι x).mpr hx)

theorem least_generator_count : least_generator_countType.{u} := by
  intro R _ _ _
  let b := Module.finBasis (ResidueField R) (CotangentSpace R)
  choose x hx using fun i => (maximalIdeal R).toCotangent_surjective (b i)
  refine ⟨⟨x, basis_lifts R _ b x hx⟩, ?_⟩
  rintro n ⟨y, hy⟩
  simpa using generator_lower_bound R (Fin n) y hy

theorem minimum_generators_basis : minimum_generators_basisType.{u,v} := by
  intro R _ _ _ ι _ x hx hcard
  let b := basisOfTopLeSpanOfCardEqFinrank
    (fun i => (maximalIdeal R).toCotangent (x i))
    ((span_iff R ι x).mpr hx).ge hcard
  exact ⟨b, fun i => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i⟩

theorem minimal_generators_basis : minimal_generators_basisType.{u,v} := by
  intro R _ _ _ ι x hx
  let q := (maximalIdeal R).toCotangent
  have hs := (span_iff R ι x).mpr hx.1
  have hli : LinearIndependent (ResidueField R) (q ∘ x) := by
    rw [linearIndependent_iff_notMem_span]
    intro i hi
    have hsp : Submodule.span (ResidueField R) ((q ∘ x) '' (Set.univ \ {i})) = ⊤ := by
      apply top_unique
      rw [← hs]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      by_cases hji : j = i
      · subst j
        exact hi
      · exact Submodule.subset_span ⟨j, by simp [hji], rfl⟩
    have hsp' : Submodule.span R (x '' (Set.univ \ {i})) = ⊤ := by
      apply CotangentSpace.span_image_eq_top_iff.mp
      simpa only [Set.image_comp] using hsp
    exact hx.2 i hsp'
  exact ⟨Basis.mk hli hs.ge, fun i => congrFun (Basis.coe_mk _ _) i⟩

theorem dimension_le_embeddingDimension : dimension_le_embeddingDimensionType.{u} := by
  intro R _ _ _
  obtain ⟨x, hx⟩ := (least_generator_count R).1
  have hspan := (generators_iff_ideal_span R _ x).mp hx
  have hmin : maximalIdeal R ∈ (maximalIdeal R).minimalPrimes :=
    ⟨⟨inferInstance, le_rfl⟩, fun _ hp _ => hp.2⟩
  have hb := P103.Ch06.KrullHeight.height_bound R (embeddingDimensionValue R)
    (fun i => (x i : R)) (maximalIdeal R) hspan.symm
    (maximalIdeal.isMaximal R).ne_top (closedPoint R) hmin
  change (maximalIdeal R).height ≤ (embeddingDimensionValue R : ℕ∞) at hb
  change ringKrullDim R ≤ _
  rw [← maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.mpr hb

theorem dimension_bound : dimension_boundType.{u} := by
  intro R _ _ _ d hd
  have hb := dimension_le_embeddingDimension R
  rw [hd] at hb
  exact_mod_cast hb

theorem regular_iff : regular_iffType.{u} := by
  intro R _ _ _ d hd
  unfold regularLocalValue
  rw [hd]
  exact_mod_cast (Iff.rfl : embeddingDimensionValue R = d ↔ embeddingDimensionValue R = d)

theorem regular_dimension_zero : regular_dimension_zeroType.{u} := by
  intro R _ _ _ hreg hd
  have he := (regular_iff R 0 hd).mp hreg
  have hf : IsField R := finrank_cotangentSpace_eq_zero_iff.mp he
  exact ⟨isField_iff_maximalIdeal_eq.mp hf, hf⟩

end P103.Ch07.EmbeddingDimension
