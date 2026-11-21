import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.ProjectivePlaneTopology
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology
open scoped Topology
namespace D12Complex.ProjectivePlaneTopology

theorem projection_quotient : Specs.D12Complex.Ch22.ProjectivePlaneTopology.projection_quotient_type :=
  isQuotientMap_quotient_mk'

@[simp] theorem coordinateRatio_projection (i j : Fin 3) (v : HomogeneousVector) :
    coordinateRatio i j (projection v) = v.val j / v.val i := rfl

private def scale (t : ℂˣ) : HomogeneousVector ≃ₜ HomogeneousVector :=
  (Homeomorph.smul t : (Fin 3 → ℂ) ≃ₜ (Fin 3 → ℂ)).subtype (by
    intro v
    exact (smul_ne_zero_iff_ne t).symm)

theorem projection_open : Specs.D12Complex.Ch22.ProjectivePlaneTopology.projection_open_type := by
  intro U hU
  apply projection_quotient.isOpen_preimage.mp
  have he : projection ⁻¹' (projection '' U) = ⋃ t : ℂˣ, scale t '' U := by
    ext v
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨w, hw, he⟩
      obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ w.property v.property).mp he
      refine ⟨t⁻¹, w, hw, ?_⟩
      apply Subtype.ext
      change t⁻¹ • w.val = v.val
      rw [← ht, inv_smul_smul]
    · rintro ⟨t, w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      refine ⟨t⁻¹, ?_⟩
      change t⁻¹ • (t • w.val) = w.val
      exact inv_smul_smul t w.val
  rw [he]
  exact isOpen_iUnion fun t => (scale t).isOpenMap _ hU

private theorem projection_openQuotient : IsOpenQuotientMap projection :=
  .of_isOpenMap_isQuotientMap projection_open projection_quotient

/-- Proportionality is exactly the vanishing of all two by two minors. -/
theorem projection_eq_iff_minors (v w : HomogeneousVector) :
    projection v = projection w ↔ ∀ i j, v.val i * w.val j = v.val j * w.val i := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ v.property w.property).mp h
    intro i j
    rw [← ht]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, w.val i ≠ 0 := by
      by_contra! hh
      exact w.property (funext hh)
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ v.property w.property).mpr
    refine ⟨v.val i / w.val i, ?_⟩
    ext j
    change v.val i / w.val i * w.val j = v.val j
    exact (div_mul_eq_mul_div _ _ _).trans ((div_eq_iff hi).mpr (h i j))

/-- Closedness of proportionality and openness of the quotient imply Hausdorffness. -/
theorem projective_hausdorff : Specs.D12Complex.Ch22.ProjectivePlaneTopology.projective_hausdorff_type := by
  apply (t2Space_iff_of_isOpenQuotientMap projection_openQuotient).mpr
  have he : {q : HomogeneousVector × HomogeneousVector | projection q.1 = projection q.2} =
      ⋂ i : Fin 3, ⋂ j : Fin 3, {q | q.1.val i * q.2.val j = q.1.val j * q.2.val i} := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter, projection_eq_iff_minors]
  rw [he]
  have hc (i : Fin 3) : Continuous (fun v : HomogeneousVector => v.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq ((hc i).comp continuous_fst |>.mul ((hc j).comp continuous_snd))
      ((hc j).comp continuous_fst |>.mul ((hc i).comp continuous_snd))

instance : T2Space ComplexProjectivePlane := projective_hausdorff

@[simp] theorem projection_mem_patch_iff (i : Fin 3) (v : HomogeneousVector) :
    projection v ∈ coordinatePatch i ↔ v.val i ≠ 0 := by
  constructor
  · rintro ⟨w, he, hw⟩
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ w.property v.property).mp he
    intro hv
    apply hw
    have := congrFun ht i
    simpa [hv] using this.symm
  · intro h
    exact ⟨v, rfl, h⟩

theorem coordinatePatch_isOpen (i : Fin 3) : IsOpen (coordinatePatch i) := by
  apply projection_quotient.isOpen_preimage.mp
  have he : projection ⁻¹' coordinatePatch i = {v : HomogeneousVector | v.val i ≠ 0} := by
    ext v
    exact projection_mem_patch_iff i v
  rw [he]
  exact isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const

@[simp] theorem affineCoordinate_param (i : Fin 3) (z : Fin 2 → ℂ) :
    affineCoordinate i (affineParam i z) = z := by
  ext j
  simp [affineCoordinate, affineParam]

@[simp] theorem affineParam_mem_patch (i : Fin 3) (z : Fin 2 → ℂ) :
    affineParam i z ∈ coordinatePatch i := by
  simp [affineParam]

theorem affineParam_coordinate (i : Fin 3) {p : ComplexProjectivePlane}
    (hp : p ∈ coordinatePatch i) : affineParam i (affineCoordinate i p) = p := by
  induction p using Projectivization.ind with | h v hv =>
  have hi : v i ≠ 0 := (projection_mem_patch_iff i ⟨v, hv⟩).mp hp
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(v i)⁻¹, ?_⟩
  ext j
  induction j using Fin.succAboveCases i with
  | x => simp [hi]
  | p j => simp [affineCoordinate, coordinateRatio,
      div_eq_mul_inv, mul_comm]

theorem coordinatePatch_cover (p : ComplexProjectivePlane) : ∃ i, p ∈ coordinatePatch i := by
  induction p using Projectivization.ind with | h v hv =>
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  exact ⟨i, (projection_mem_patch_iff i ⟨v, hv⟩).mpr hi⟩

theorem continuous_affineParam (i : Fin 3) : Continuous (affineParam i) := by
  apply projection_quotient.continuous.comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  induction j using Fin.succAboveCases i with
  | x => simpa using (continuous_const : Continuous (fun _ : Fin 2 → ℂ => (1 : ℂ)))
  | p j => simpa using (continuous_apply j : Continuous (fun z : Fin 2 → ℂ => z j))

theorem continuousOn_affineCoordinate (i : Fin 3) :
    ContinuousOn (affineCoordinate i) (coordinatePatch i) := by
  apply (projection_quotient.continuousOn_isOpen_iff (coordinatePatch_isOpen i)).mpr
  apply continuousOn_pi.mpr
  intro j
  change ContinuousOn (fun v : HomogeneousVector => v.val (i.succAbove j) / v.val i)
    (projection ⁻¹' coordinatePatch i)
  have hc (k : Fin 3) : Continuous (fun v : HomogeneousVector => v.val k) :=
    (continuous_apply k).comp continuous_subtype_val
  apply ContinuousOn.div (hc (i.succAbove j)).continuousOn (hc i).continuousOn
  intro v hv
  exact (projection_mem_patch_iff i v).mp hv

/-- All three affine charts are homeomorphisms with the specified ratio maps. -/
def affineChart (i : Fin 3) : OpenPartialHomeomorph ComplexProjectivePlane (Fin 2 → ℂ) where
  toFun := affineCoordinate i
  invFun := affineParam i
  source := coordinatePatch i
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun z _ => affineParam_mem_patch i z
  left_inv' := fun _ hp => affineParam_coordinate i hp
  right_inv' := fun z _ => affineCoordinate_param i z
  open_source := coordinatePatch_isOpen i
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_affineCoordinate i
  continuousOn_invFun := (continuous_affineParam i).continuousOn

theorem affine_charts : Specs.D12Complex.Ch22.ProjectivePlaneTopology.affine_charts_type :=
  ⟨affineChart, (fun _ => rfl), (fun _ => rfl), (fun _ _ => rfl),
    (fun _ _ => rfl), coordinatePatch_cover⟩

theorem projective_secondCountable :
    Specs.D12Complex.Ch22.ProjectivePlaneTopology.projective_secondCountable_type := by
  let U : Fin 3 → Set ComplexProjectivePlane := coordinatePatch
  let : ∀ i, SecondCountableTopology (U i) := fun i =>
    (affineChart i).secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U) coordinatePatch_isOpen
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  exact coordinatePatch_cover p

instance : SecondCountableTopology ComplexProjectivePlane := projective_secondCountable

/-- Unit-norm representatives form a compact set and surject onto the quotient. -/
theorem projective_compact : Specs.D12Complex.Ch22.ProjectivePlaneTopology.projective_compact_type := by
  let S := {v : Fin 3 → ℂ // ‖v‖ = 1}
  have hS : IsCompact {v : Fin 3 → ℂ | ‖v‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using
      (isCompact_sphere (0 : Fin 3 → ℂ) 1)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let f : S → HomogeneousVector := fun v => ⟨v.val, by
    intro h
    have := v.property
    simp [h] at this⟩
  have hc : Continuous (projection ∘ f) :=
    projection_quotient.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hs : Function.Surjective (projection ∘ f) := by
    intro p
    induction p using Projectivization.ind with | h v hv =>
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hw : ‖(↑‖v‖ : ℂ)⁻¹ • v‖ = 1 := by
      simp [norm_smul, hn]
    refine ⟨⟨(↑‖v‖ : ℂ)⁻¹ • v, hw⟩, ?_⟩
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨(↑‖v‖ : ℂ)⁻¹, rfl⟩
  exact hs.compactSpace hc

instance : CompactSpace ComplexProjectivePlane := projective_compact

theorem projective_plane_topology :
    Specs.D12Complex.Ch22.ProjectivePlaneTopology.projective_plane_topology_type :=
  ⟨projection_quotient, projective_compact, projective_hausdorff,
    projective_secondCountable, affine_charts⟩

end D12Complex.ProjectivePlaneTopology

namespace D12Complex.ProjectivePlaneTopology.Definitions
abbrev HomogeneousVector : Specs.D12Complex.Ch22.ProjectivePlaneTopology.HomogeneousVector_type :=
  D12Complex.ProjectivePlaneTopology.HomogeneousVector
abbrev ComplexProjectivePlane : Specs.D12Complex.Ch22.ProjectivePlaneTopology.ComplexProjectivePlane_type :=
  D12Complex.ProjectivePlaneTopology.ComplexProjectivePlane
abbrev projection : Specs.D12Complex.Ch22.ProjectivePlaneTopology.projection_type :=
  D12Complex.ProjectivePlaneTopology.projection
abbrev coordinatePatch : Specs.D12Complex.Ch22.ProjectivePlaneTopology.coordinatePatch_type :=
  D12Complex.ProjectivePlaneTopology.coordinatePatch
abbrev coordinateRatio : Specs.D12Complex.Ch22.ProjectivePlaneTopology.coordinateRatio_type :=
  D12Complex.ProjectivePlaneTopology.coordinateRatio
abbrev affineCoordinate : Specs.D12Complex.Ch22.ProjectivePlaneTopology.affineCoordinate_type :=
  D12Complex.ProjectivePlaneTopology.affineCoordinate
abbrev affineParam : Specs.D12Complex.Ch22.ProjectivePlaneTopology.affineParam_type :=
  D12Complex.ProjectivePlaneTopology.affineParam
end D12Complex.ProjectivePlaneTopology.Definitions
