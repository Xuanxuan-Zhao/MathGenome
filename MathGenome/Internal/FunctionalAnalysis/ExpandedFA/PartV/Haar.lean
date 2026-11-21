import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Haar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.HaarAveraging
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Group.Integral

/-! The measure is obtained by positive Riesz–Markov from the proved averaging
mean. Uniqueness uses continuous compact-product interchange. Its library proof
establishes product measurability of the particular continuous compactly supported
function, without identifying the two sigma algebras on the product. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal CompactlySupported
universe u v
namespace ExpandedFA.PartV.Haar
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentation

/-- Compact support gives product strong measurability even when the product
Borel sigma algebra is larger than the product of the factor Borel algebras. -/
theorem compact_product_interchange : Spec.CompactProductInterchange.{u,v} := by
  intro X Y _ _ _ _ _ _ _ _ _ _ μ ν _ _ f
  exact integral_integral_swap_of_hasCompactSupport (f := fun x y => f (x,y)) f.continuous
    (HasCompactSupport.of_compactSpace _)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

private def compactTest (f : C(G, ℝ)) : C_c(G, ℝ) :=
  ⟨f, HasCompactSupport.of_compactSpace _⟩

private def testInclusion : C_c(G, ℝ) →ₗ[ℝ] C(G, ℝ) where
  toFun f := f.toContinuousMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Group G] [IsTopologicalGroup G] [T2Space G] in
private lemma continuous_integrable (μ : Measure G) [IsFiniteMeasure μ]
    (f : C(G, ℝ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Equality of continuous tests determines a regular Borel measure. -/
lemma measure_ext_continuous {μ ν : Measure G} [μ.Regular] [ν.Regular]
    (h : ∀ f : C(G, ℝ), (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f => h f.toContinuousMap

private lemma map_eq_of_mean (μ : Measure G) [μ.Regular] [IsFiniteMeasure μ]
    (M : C(G, ℝ) →L[ℝ] ℝ) (hrep : ∀ f : C(G, ℝ), M f = ∫ x, f x ∂μ)
    (e : G ≃ₜ G) (hinv : ∀ f : C(G, ℝ), M (f.comp ⟨e, e.continuous⟩) = M f) :
    μ.map e = μ := by
  let : (μ.map e).Regular := Measure.Regular.map e
  apply measure_ext_continuous
  intro f
  rw [integral_map e.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact (hrep (f.comp ⟨e, e.continuous⟩)).symm.trans ((hinv f).trans (hrep f))

theorem representation_of_mean : Spec.RepresentationOfMean.{u} := by
  intro G _ _ _ _ _ _ _ M hM
  let I : C_c(G, ℝ) →ₗ[ℝ] ℝ := M.toLinearMap.comp testInclusion
  have hpos : ∀ f : C_c(G, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ I f := by
    intro f hf
    obtain ⟨r, hr, heq⟩ := hM.2.1 f.toContinuousMap
      (fun x => ⟨f x, hf x, rfl⟩)
    change 0 ≤ M f.toContinuousMap
    rw [heq]
    exact hr
  obtain ⟨μ, ⟨hμ, hrep⟩, _⟩ := positive_radon_representation G I hpos
  let : μ.Regular := (positiveRadon_iff_regular μ).mp hμ
  have hr (f : C(G, ℝ)) : M f = ∫ x, f x ∂μ := (hrep (compactTest f)).2
  have hmass : μ univ = 1 := by
    apply (ENNReal.toReal_eq_one_iff _).mp
    have h := (hM.1 (1 : ℝ)).symm.trans (hr (ContinuousMap.const G 1))
    simpa [Measure.real] using h.symm
  let : IsProbabilityMeasure μ := ⟨hmass⟩
  have hl : IsMulLeftInvariant μ := ⟨fun s =>
    map_eq_of_mean μ M hr (Homeomorph.mulLeft s) (hM.2.2.1 .left s)⟩
  have hright : IsMulRightInvariant μ := ⟨fun s =>
    map_eq_of_mean μ M hr (Homeomorph.mulRight s) (hM.2.2.1 .right s)⟩
  exact ⟨μ, ⟨hμ, hmass, hl⟩, hright, fun f => ⟨continuous_integrable μ f, hr f⟩⟩

/-- Continuous compact-product interchange proves equality of a left-invariant
probability and a right-invariant probability. No joint measurability of the
group multiplication map into G is needed. -/
lemma eq_of_left_right (ν μ : Measure G) [ν.Regular] [μ.Regular]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    [IsMulLeftInvariant ν] [IsMulRightInvariant μ] : ν = μ := by
  apply measure_ext_continuous
  intro f
  calc
    (∫ x, f x ∂ν) = ∫ y, ∫ x, f (y * x) ∂ν ∂μ := by
      simp_rw [integral_mul_left_eq_self]
      simp
    _ = ∫ x, ∫ y, f (y * x) ∂μ ∂ν :=
      compact_product_interchange G G μ ν
        ⟨fun p => f (p.1 * p.2), f.continuous.comp (continuous_fst.mul continuous_snd)⟩
    _ = ∫ y, f y ∂μ := by
      simp_rw [integral_mul_right_eq_self]
      simp

/-- A representing probability exists by applying Riesz–Markov to the proved
averaging mean. -/
lemma exists_representing_haar :
    ∃ μ : Measure G, IsNormalizedLeftHaar μ ∧ IsMulRightInvariant μ := by
  obtain ⟨M, hM⟩ := HaarAveraging.exists_averaging_mean G ℝ
  obtain ⟨μ, hμ, hr, _⟩ := representation_of_mean G M hM
  exact ⟨μ, hμ, hr⟩

theorem normalized_haar : Spec.NormalizedHaar.{u} := by
  intro G _ _ _ _ _ _ _
  obtain ⟨μ, hμ, hr⟩ := exists_representing_haar (G := G)
  have : μ.Regular := (positiveRadon_iff_regular μ).mp hμ.1
  have : IsProbabilityMeasure μ := ⟨hμ.2.1⟩
  have : IsMulRightInvariant μ := hr
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  have : ν.Regular := (positiveRadon_iff_regular ν).mp hν.1
  have : IsProbabilityMeasure ν := ⟨hν.2.1⟩
  have : IsMulLeftInvariant ν := hν.2.2
  exact eq_of_left_right ν μ

omit [CompactSpace G] [T2Space G] in
/-- Inversion exchanges left and right invariance using only measurable
one-variable translations and inversion, without joint measurability of multiplication. -/
lemma inv_left_invariant (μ : Measure G) [IsMulRightInvariant μ] :
    IsMulLeftInvariant μ.inv := by
  constructor
  intro g
  conv_rhs => rw [← map_mul_right_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_const_mul g) measurable_inv,
    map_map measurable_inv (measurable_mul_const g⁻¹), Function.comp_def,
    mul_inv_rev, inv_inv]

theorem additional_invariances : Spec.AdditionalInvariances.{u} := by
  intro G _ _ _ _ _ _ _ μ hμ
  obtain ⟨m, hm, hmright⟩ := exists_representing_haar (G := G)
  have : μ.Regular := (positiveRadon_iff_regular μ).mp hμ.1
  have : IsProbabilityMeasure μ := ⟨hμ.2.1⟩
  have : IsMulLeftInvariant μ := hμ.2.2
  have : m.Regular := (positiveRadon_iff_regular m).mp hm.1
  have : IsProbabilityMeasure m := ⟨hm.2.1⟩
  have : IsMulRightInvariant m := hmright
  have heq : μ = m := eq_of_left_right μ m
  have : IsMulRightInvariant μ := heq ▸ hmright
  have : IsMulLeftInvariant μ.inv := inv_left_invariant μ
  have hinvmass : μ.inv univ = 1 := by simp
  have : IsProbabilityMeasure μ.inv := ⟨hinvmass⟩
  have hinv : IsInvInvariant μ := ⟨eq_of_left_right μ.inv μ⟩
  have : IsOpenPosMeasure μ :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact univ isCompact_univ (by simp)
  exact ⟨inferInstance, hinv, fun U hU hne => hU.measure_pos μ hne⟩

end ExpandedFA.PartV.Haar

/- Mathlib proof attribution
Adapted portion near line 125:
The proof of left invariance after inversion, adapted to separate
measurability of translations.

Upstream: Mathlib/MeasureTheory/Group/Measure.lean (around line 385)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
