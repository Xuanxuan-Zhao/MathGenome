import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionFoundation
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Foundation for paper.tex 4762–4809: canonical geometric data, elementary
region topology, noncuspidal direction algebra, and a constructed collar push.
Surface, collar existence and separation are separate geometric obligations. -/
noncomputable section
open Set Topology

namespace P202.PlanarRegionTopology
open P202Specs.PlanarRegionTopology

theorem compactificationSphere : Expected.compactificationSphere :=
  ⟨onePointEquivSphereOfFinrankEq (by simp [Plane])⟩

theorem parameterCircleSphere : Expected.parameterCircleSphere := by
  let e : Circle ≃ₜ Metric.sphere (0 : Plane) 1 :=
    Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype (fun z => by
      change z ∈ Metric.sphere (0 : ℂ) 1 ↔
        Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere (0 : Plane) 1
      simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map])
  exact ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans e⟩

theorem jordanCurve_embedding (c : RegularJordanCurve) :
    Topology.IsEmbedding c.parametrization := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact (c.parametrization.continuous.isClosedEmbedding c.injective).isEmbedding

theorem compact_trace (c : RegularJordanCurve) : IsCompact c.trace := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact isCompact_range c.parametrization.continuous

theorem trace_nonempty (c : RegularJordanCurve) : c.trace.Nonempty :=
  ⟨c.parametrization 0, 0, rfl⟩

theorem boundary_nonempty (R : PlanarRegion) : R.boundary.Nonempty := by
  let i : Fin R.boundaryCount := ⟨0, R.boundaryCount_pos⟩
  obtain ⟨p, hp⟩ := trace_nonempty (R.curve i)
  refine ⟨p, ?_⟩
  change p ∈ frontier R.domain
  rw [R.boundary_eq]
  exact mem_iUnion.mpr ⟨i, hp⟩

/-- Local outside points prevent a frontier point from entering the
interior of the closure. This works without any smoothness assumption. -/
theorem interior_closure_eq_of_oneSided {U : Set Plane} (hU : IsOpen U)
    (hside : LocallyOneSided U) : interior (closure U) = U := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxu
    have hxf : x ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨interior_subset hx, hxu⟩
    obtain ⟨N, _, _, hNO, _, hout⟩ :=
      hside x hxf (interior (closure U)) isOpen_interior hx
    obtain ⟨y, hyN, hyout⟩ := hout.nonempty
    exact hyout (interior_subset (hNO hyN))
  · exact hU.subset_interior_iff.mpr subset_closure

theorem basicProperties : Expected.basicProperties := by
  intro R
  have hi : interior R.carrier = R.domain :=
    interior_closure_eq_of_oneSided R.open_domain R.one_sided
  refine ⟨R.compact_closure, R.connected_domain.closure, hi, ?_⟩
  change frontier (closure R.domain) = frontier R.domain
  change interior (closure R.domain) = R.domain at hi
  rw [frontier, closure_closure, hi, R.open_domain.frontier_eq]

/-- The sum of nonopposite unit directions has strictly positive scalar
product with both. This is independent of the sign of a corner's turn. -/
theorem unit_direction_sum_positive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : u ≠ -v) :
    0 < inner ℝ (u + v) u ∧ 0 < inner ℝ (u + v) v := by
  have hne : u + v ≠ 0 := by
    intro hz
    apply h
    exact eq_neg_of_add_eq_zero_left hz
  have hp := (real_inner_self_pos (x := u + v)).mpr hne
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have huv := real_inner_comm u v
  simp only [inner_add_left, inner_add_right] at hp ⊢
  constructor <;> nlinarith

theorem cornerTransverse : Expected.cornerTransverse := by
  intro u v hu hv h
  exact unit_direction_sum_positive hu hv h

/-- The preceding strict inequalities apply to the actual one-sided
derivatives in the regular-corner hypothesis. -/
theorem normalized_direction_sum_positive {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : NormedSpace.normalize u ≠ -NormedSpace.normalize v) :
    0 < inner ℝ (NormedSpace.normalize u + NormedSpace.normalize v)
      (NormedSpace.normalize u) ∧
    0 < inner ℝ (NormedSpace.normalize u + NormedSpace.normalize v)
      (NormedSpace.normalize v) :=
  unit_direction_sum_positive (NormedSpace.norm_normalize hu)
    (NormedSpace.norm_normalize hv) h

@[simp] theorem quarterTurn_inner (u v : Plane) :
    inner ℝ (quarterTurn u) (quarterTurn v) = inner ℝ u v := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two, add_comm]

/-- A common strict normal direction for both one-sided directed tangents.
This is the linear-algebra part of the corner graph construction. -/
theorem common_normal_direction {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : NormedSpace.normalize u ≠ -NormedSpace.normalize v) :
    ∃ w : Plane, 0 < inner ℝ w (quarterTurn u) ∧ 0 < inner ℝ w (quarterTurn v) := by
  obtain ⟨hleft, hright⟩ := normalized_direction_sum_positive hu hv h
  refine ⟨quarterTurn (NormedSpace.normalize u + NormedSpace.normalize v), ?_, ?_⟩
  · rw [quarterTurn_inner]
    have hp : 0 < inner ℝ (NormedSpace.normalize u + NormedSpace.normalize v)
        (‖u‖ • NormedSpace.normalize u) := by
      rw [inner_smul_right]
      exact mul_pos (norm_pos_iff.mpr hu) hleft
    simpa only [NormedSpace.norm_smul_normalize] using hp
  · rw [quarterTurn_inner]
    have hp : 0 < inner ℝ (NormedSpace.normalize u + NormedSpace.normalize v)
        (‖v‖ • NormedSpace.normalize v) := by
      rw [inner_smul_right]
      exact mul_pos (norm_pos_iff.mpr hv) hright
    simpa only [NormedSpace.norm_smul_normalize] using hp

/-- A push constructed from a collar supplies both homotopies for the
specific interior inclusion. No deformation retract of the closed region
onto its open interior is asserted. -/
theorem inwardPushEquivalence : Expected.inwardPushEquivalence := by
  intro K ⟨P⟩
  let r : C(K, interior K) :=
    ⟨fun x => ⟨(P.map (1, x)).val, P.at_one x⟩, by fun_prop⟩
  let F : (ContinuousMap.id K).Homotopy ((interiorInclusion K).comp r) :=
    { toContinuousMap := P.map
      map_zero_left := P.at_zero
      map_one_left := fun _ => rfl }
  let G : (ContinuousMap.id (interior K)).Homotopy (r.comp (interiorInclusion K)) :=
    { toFun := fun z =>
        ⟨(P.map (z.1, interiorInclusion K z.2)).val,
          P.interior_stays z.1 _ z.2.property⟩
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro x
        apply Subtype.ext
        change (P.map (0, interiorInclusion K x)).val = x.val
        exact congrArg (fun z : K => z.val) (P.at_zero (interiorInclusion K x))
      map_one_left := fun _ => rfl }
  exact ⟨⟨interiorInclusion K, r, ⟨G.symm⟩, ⟨F.symm⟩⟩, rfl⟩

/-- A collar coordinate push, fixed at the collar's inner end. -/
def pushedParameter (t s : unitInterval) : unitInterval :=
  ⟨max ((t : ℝ) / 2) (s : ℝ),
    le_trans s.property.1 (le_max_right _ _),
    max_le (by have := t.property.2; linarith) s.property.2⟩

theorem continuous_pushedParameter :
    Continuous (fun z : unitInterval × unitInterval => pushedParameter z.1 z.2) := by
  unfold pushedParameter
  fun_prop

@[simp] theorem pushedParameter_zero (s : unitInterval) : pushedParameter 0 s = s := by
  apply Subtype.ext
  simp [pushedParameter, max_eq_right s.property.1]

@[simp] theorem pushedParameter_one (t : unitInterval) : pushedParameter t 1 = 1 := by
  apply Subtype.ext
  change max ((t : ℝ) / 2) (1 : ℝ) = 1
  exact max_eq_right (by have := t.property.2; linarith)

namespace CollarConstruction

variable {K B : Set Plane} (C : BoundaryCollar K B)

def lowerImage : Set K := C.map '' {z : B × unitInterval | (z.2 : ℝ) < 1}

def push (z : unitInterval × K) : K := by
  classical
  exact if h : z.2 ∈ range C.map then
    let a := C.embedding.toHomeomorph.symm ⟨z.2, h⟩
    C.map (a.1, pushedParameter z.1 a.2)
  else z.2

theorem push_on_image (t : unitInterval) (a : B × unitInterval) :
    (push C) (t, C.map a) = C.map (a.1, pushedParameter t a.2) := by
  simp only [push, dite_eq_left (mem_range_self a),
    Topology.IsEmbedding.toHomeomorph_symm_apply]

theorem push_eq_self_of_not_lower (t : unitInterval) {x : K}
    (hx : x ∉ (lowerImage C)) : (push C) (t, x) = x := by
  classical
  by_cases h : x ∈ range C.map
  · obtain ⟨a, rfl⟩ := h
    have hs : a.2 = 1 := by
      apply Subtype.ext
      apply le_antisymm a.2.property.2
      apply not_lt.mp
      intro hlt
      exact hx ⟨a, hlt, rfl⟩
    rw [(push_on_image C), hs, pushedParameter_one]
    rw [← hs]
  · simp [push, h]

theorem continuous_push (hB : IsCompact B) : Continuous (push C) := by
  classical
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  have hclosed : IsClosed (range C.map) := (isCompact_range C.map.continuous).isClosed
  let S : Set (unitInterval × K) := Prod.snd ⁻¹' range C.map
  let T : Set (unitInterval × K) := Prod.snd ⁻¹' (lowerImage C)ᶜ
  have hS : IsClosed S := hclosed.preimage continuous_snd
  have hT : IsClosed T := C.open_lower_image.isClosed_compl.preimage continuous_snd
  have hcS : ContinuousOn (push C) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let a : S → B × unitInterval := fun z =>
      C.embedding.toHomeomorph.symm ⟨z.val.2, z.property⟩
    have ha : Continuous a := by unfold a; fun_prop
    have hc : Continuous (fun z : S =>
        C.map ((a z).1, pushedParameter z.val.1 (a z).2)) :=
      C.map.continuous.comp ((continuous_fst.comp ha).prodMk
        (continuous_pushedParameter.comp
          ((continuous_fst.comp continuous_subtype_val).prodMk
            (continuous_snd.comp ha))))
    convert hc using 1
    funext z
    have hz : z.val.2 ∈ range C.map := z.property
    simp only [Set.domRestrict_apply, push]
    rw [dite_eq_left hz]
  have hcT : ContinuousOn (push C) T := by
    apply continuous_snd.continuousOn.congr
    intro z hz
    exact (push_eq_self_of_not_lower C) z.1 hz
  have hcover : S ∪ T = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z.2 ∈ (lowerImage C)
    · obtain ⟨a, _, ha⟩ := hz
      exact Or.inl ⟨a, ha⟩
    · exact Or.inr hz
  exact continuousOn_univ.mp (hcover ▸ hcS.union_of_isClosed hcT hS hT)

theorem push_zero (x : K) : (push C) (0, x) = x := by
  classical
  by_cases hx : x ∈ range C.map
  · obtain ⟨a, rfl⟩ := hx
    simp [(push_on_image C)]
  · simp [push, hx]

theorem interior_of_not_image (hK : IsClosed K) (hBK : B = frontier K)
    {x : K} (hx : x ∉ range C.map) : x.val ∈ interior K := by
  by_contra hi
  have hb : x.val ∈ B := by
    rw [hBK, hK.frontier_eq]
    exact ⟨x.property, hi⟩
  apply hx
  exact ⟨(⟨x.val, hb⟩, 0), Subtype.ext (C.at_zero _)⟩

theorem push_one_interior (hK : IsClosed K) (hBK : B = frontier K) (x : K) :
    ((push C) (1, x)).val ∈ interior K := by
  classical
  by_cases hx : x ∈ range C.map
  · obtain ⟨a, rfl⟩ := hx
    rw [(push_on_image C)]
    apply C.positive_interior
    change 0 < max ((1 : ℝ) / 2) (a.2 : ℝ)
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · rw [show (push C) (1, x) = x by simp [push, hx]]
    exact (interior_of_not_image C) hK hBK hx

theorem push_interior_stays (_hK : IsClosed K) (hBK : B = frontier K)
    (t : unitInterval) (x : K) (hxint : x.val ∈ interior K) :
    ((push C) (t, x)).val ∈ interior K := by
  classical
  by_cases hx : x ∈ range C.map
  · obtain ⟨a, rfl⟩ := hx
    rw [(push_on_image C)]
    apply C.positive_interior
    have hs : 0 < (a.2 : ℝ) := by
      by_contra hn
      have heq : a.2 = 0 := Subtype.ext (le_antisymm (not_lt.mp hn) a.2.property.1)
      have hb : a.1.val ∈ frontier K := hBK ▸ a.1.property
      have hnot : a.1.val ∉ interior K := hb.2
      apply hnot
      have heq' : C.map a = C.map (a.1, 0) := congrArg C.map (Prod.ext rfl heq)
      simpa only [heq', C.at_zero] using hxint
    exact lt_of_lt_of_le hs (le_max_right _ _)
  · simpa only [push, dite_eq_right hx] using hxint

/-- Construction of the two-sided homotopy information from a compact
boundary collar, using closed-set pasting at parameter one. -/
def inwardPush (hK : IsClosed K) (hB : IsCompact B) (hBK : B = frontier K) :
    InwardPush K where
  map := ⟨(push C), (continuous_push C) hB⟩
  at_zero := (push_zero C)
  at_one := (push_one_interior C) hK hBK
  interior_stays := (push_interior_stays C) hK hBK

end CollarConstruction

theorem collaredInteriorEquivalence : Expected.collaredInteriorEquivalence := by
  intro K B hK hB hBK ⟨C⟩
  exact inwardPushEquivalence K ⟨CollarConstruction.inwardPush C hK hB hBK⟩

theorem compact_boundary (R : PlanarRegion) : IsCompact R.boundary :=
  R.compact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure

theorem regionInteriorEquivalenceOfCollar (R : PlanarRegion)
    (h : Nonempty (BoundaryCollar R.carrier R.boundary)) :
    InteriorInclusionEquivalence R.carrier := by
  have hb := (basicProperties R).2.2.2
  exact collaredInteriorEquivalence R.carrier R.boundary isClosed_closure
    (compact_boundary R) hb.symm h

/-- A constructed push, with continuity and interior invariance. -/
theorem collarInwardPush : Expected.collarInwardPush := by
  intro K B hK hB hBK ⟨C⟩
  exact ⟨CollarConstruction.inwardPush C hK hB hBK⟩

theorem commonNormalDirection : Expected.commonNormalDirection := by
  intro u v hu hv h
  exact common_normal_direction hu hv h

/-- Specialization of the strict-normal algebra to the actual curve data. -/
theorem regularJoinNormal : Expected.regularJoinNormal := by
  intro c t
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hnon⟩ := c.regular_joins t
  obtain ⟨w, hwl, hwr⟩ := common_normal_direction hnl hnr hnon
  exact ⟨δ, l, r, w, hδ, hl, hr, hel, her, hnl, hnr, hwl, hwr⟩

end P202.PlanarRegionTopology
