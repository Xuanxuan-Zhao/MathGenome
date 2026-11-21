import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.SubmanifoldRestrictions
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryImmersion

namespace SmoothManifolds.SubmanifoldRestrictions
open ModelData AtlasData MapData FiniteRegularityData MapClassData Set Filter
open scoped Topology ContDiff
universe u v w

/-- Straighten an ambient extension of the immersion, then project to its
source coordinates. No ambient half-space preservation is required. -/
theorem immersion_coordinate_recovery {k n : ℕ} {c b : ModelKind}
    {P : Type w} {N : Type v} [TopologicalSpace P] [TopologicalSpace N]
    (R : SmoothManifold k c P) (T : SmoothManifold n b N) (i : P → N)
    (hi : IsSmoothMap R T i) (himm : IsImmersion R T i) (p : P)
    (e : ModelChart k c P) (d : ModelChart n b N)
    (he : e ∈ R.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ e.source) (hip : i p ∈ d.source) :
    LocalCoordinateExtension (⊤ : ℕ∞) (fun y => (d (i y)).val)
      (fun y => (e y).val) p := by
  obtain ⟨U, hU, hepU, g, hg, heq⟩ := (hi p).2 e he d hd hp hip
  have hdg := ((hg.contDiffAt (hU.mem_nhds hepU)).differentiableAt
    (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hderiv : chartDerivative e d i p = fderiv ℝ g (e p).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p hp _ ⟨g, hdg, heq⟩
  have hi1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ i (by simp) hi
  have hgi : Function.Injective (fderiv ℝ g (e p).val) := by
    rw [← hderiv]
    exact ((MapClasses.chart_invariants R T i hi1 p e d he hd hp hip).2.1).mp (himm p)
  obtain ⟨_, h, hhs, _, O, hO, hepO, hform⟩ :=
    BoundaryImmersion.euclidean_immersion (⊤ : ℕ∞) (by simp) g U hU hg
      (e p).val hepU _ hdg hgi
  have hdp : (d (i p)).val ∈ h.source := by
    rw [← heq.eq_of_nhds]
    exact (hform _ hepO).1
  refine ⟨h.source, h.open_source, hdp, (fun z => (h z).1),
    contDiff_fst.comp_contDiffOn hhs, ?_⟩
  have hecont : ContinuousAt (fun y => (e y).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  filter_upwards [heq, hecont.preimage_mem_nhds (hO.mem_nhds hepO)] with y hy hyO
  rw [← hy, (hform _ hyO).2]

/-- A continuous lift through any smooth immersion is smooth. -/
theorem lift_through_immersion :
    Specs.SmoothManifolds.Ch03.SubmanifoldRestrictions.lift_through_immersionType.{u,v,w} := by
  intro m n k a b c M N P _ _ _ S T R i f hi himm hf hif
  intro x
  refine ⟨hf.continuousAt, ?_⟩
  intro e he j hj hx hfx
  obtain ⟨d, hd, hifx⟩ := T.smoothStructure.property.1.1 (i (f x))
  have hrec := immersion_coordinate_recovery R T i hi himm (f x) j d hj hd hfx hifx
  have hpull := LocalCoordinateExtension.precomp hrec hf.continuousAt rfl
  exact LocalCoordinateExtension.comp hpull ((hif x).2 e he d hd hx hifx)

/-- Domain restriction is composition with the smooth inclusion. -/
theorem restrict_source :
    Specs.SmoothManifolds.Ch03.SubmanifoldRestrictions.restrict_sourceType.{u,v} := by
  intro m n k a b c M N _ _ S T s t R f hi _ hf
  letI : TopologicalSpace s := t
  exact manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1
    Subtype.val f hi hf

/-- Codomain restriction uses continuity for the immersed topology. -/
theorem restrict_target :
    Specs.SmoothManifolds.Ch03.SubmanifoldRestrictions.restrict_targetType.{u,v} := by
  intro m n k a b c M N _ _ S T s t R f himage hi himm hf hcont
  letI : TopologicalSpace s := t
  exact lift_through_immersion S T R Subtype.val (fun x => ⟨f x, himage x⟩)
    hi himm hcont hf

/-- The homeomorphism onto the image supplies the required continuity. -/
theorem restrict_embedded_target :
    Specs.SmoothManifolds.Ch03.SubmanifoldRestrictions.restrict_embedded_targetType.{u,v} := by
  intro m n k a b c M N _ _ S T s t R f himage hemb hf
  letI : TopologicalSpace s := t
  obtain ⟨hi, _, himm, h, hh⟩ := hemb
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  let g : M → Set.range (Subtype.val : s → N) := fun x =>
    ⟨f x, ⟨⟨f x, himage x⟩, rfl⟩⟩
  have hgc : Continuous g := hfc.subtype_mk _
  have hcomp : h.symm ∘ g = (fun x => (⟨f x, himage x⟩ : s)) := by
    funext x
    apply h.injective
    change h (h.symm (g x)) = h ⟨f x, himage x⟩
    rw [h.apply_symm_apply]
    apply Subtype.ext
    change (g x).val = (h ⟨f x, himage x⟩).val
    exact (hh ⟨f x, himage x⟩).symm
  have hcont : Continuous (fun x => (⟨f x, himage x⟩ : s)) :=
    hcomp ▸ h.symm.continuous.comp hgc
  exact restrict_target S T s t R f himage hi himm hf hcont

end SmoothManifolds.SubmanifoldRestrictions
