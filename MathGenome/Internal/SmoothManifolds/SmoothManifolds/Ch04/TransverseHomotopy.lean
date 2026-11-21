import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.TransverseHomotopy
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.FunProp

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.ParametricTransversality
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.TransversePreimage
set_option autoImplicit false

namespace SmoothManifolds.TransverseHomotopy
open ModelData AtlasData MapData BoundaryData MapClassData ProductData
  BoundaryRegularLevelData TransversePreimageData ParametricTransversalityData
  TransverseHomotopyData TangentData DifferentialData Set Filter
open scoped Topology ContDiff
universe u

@[simp] theorem intervalLeftChart_val (t : unitInterval) :
    (intervalLeftChart t).val = fun _ => t.val := rfl

@[simp] theorem intervalRightChart_val (t : unitInterval) :
    (intervalRightChart t).val = fun _ => 1 - t.val := rfl

@[simp] theorem intervalLeftChart_source :
    intervalLeftChart.source = {t | t.val < 1} := rfl

@[simp] theorem intervalRightChart_source :
    intervalRightChart.source = {t | 0 < t.val} := by
  ext t
  simp only [intervalRightChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, mem_inter_iff, mem_univ,
    true_and, mem_preimage, intervalLeftChart_source, mem_ofPred_eq]
  change 1 - t.val < 1 ↔ 0 < t.val
  constructor <;> intro h <;> linarith

/-- The two affine coordinates cover the closed interval and have smooth
transitions in the local ambient-extension sense, including at the endpoints. -/
theorem intervalAtlas_isContDiffAtlas :
    IsContDiffAtlas (⊤ : ℕ∞) intervalAtlas := by
  constructor
  · intro t
    by_cases ht : t.val < 1
    · exact ⟨intervalLeftChart, by simp [intervalAtlas], ht⟩
    · refine ⟨intervalRightChart, by simp [intervalAtlas], ?_⟩
      rw [intervalRightChart_source]
      change 0 < t.val
      linarith
  · have hlr : ∀ t, ChartContDiffAt (⊤ : ℕ∞) intervalLeftChart
        intervalRightChart id t := by
      intro t
      exact ⟨univ, isOpen_univ, mem_univ _, fun x => 1 - x,
        (contDiff_const.sub contDiff_id).contDiffOn, Eventually.of_forall fun _ => rfl⟩
    have hrl : ∀ t, ChartContDiffAt (⊤ : ℕ∞) intervalRightChart
        intervalLeftChart id t := by
      intro t
      refine ⟨univ, isOpen_univ, mem_univ _, fun x => 1 - x,
        (contDiff_const.sub contDiff_id).contDiffOn, Eventually.of_forall ?_⟩
      intro q
      ext i
      change 1 - (1 - q.val) = q.val
      ring
    intro c hc d hd
    have hc' : c = intervalLeftChart ∨ c = intervalRightChart := by
      simpa only [intervalAtlas, mem_insert_iff, mem_singleton_iff] using hc
    have hd' : d = intervalLeftChart ∨ d = intervalRightChart := by
      simpa only [intervalAtlas, mem_insert_iff, mem_singleton_iff] using hd
    rcases hc' with rfl | rfl <;> rcases hd' with rfl | rfl
    · apply contDiffCompatible_of_germs <;> intro p _ _
      all_goals exact LocalCoordinateExtension.self _ _ _
    · exact contDiffCompatible_of_germs (fun p _ _ => hlr p) (fun p _ _ => hrl p)
    · exact contDiffCompatible_of_germs (fun p _ _ => hrl p) (fun p _ _ => hlr p)
    · apply contDiffCompatible_of_germs <;> intro p _ _
      all_goals exact LocalCoordinateExtension.self _ _ _

/-- An actual standard interval structure, constructed without a certificate
assumption. This discharges the interval choice in the independent target. -/
noncomputable def intervalManifold : SmoothManifold 1 .halfSpace unitInterval where
  topologicalManifold := ⟨inferInstance, inferInstance, intervalAtlas,
    intervalAtlas_isContDiffAtlas.1⟩
  smoothStructure := ⟨_, maximalExtension_isMaximal intervalAtlas_isContDiffAtlas⟩

theorem intervalManifold_standard :
    intervalManifold.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas := rfl

theorem intervalLeftChart_mem (I : SmoothManifold 1 .halfSpace unitInterval)
    (hI : I.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas) :
    intervalLeftChart ∈ I.smoothStructure.val := by
  rw [hI]
  exact subset_maximalExtension intervalAtlas_isContDiffAtlas (by simp [intervalAtlas])

theorem intervalRightChart_mem (I : SmoothManifold 1 .halfSpace unitInterval)
    (hI : I.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas) :
    intervalRightChart ∈ I.smoothStructure.val := by
  rw [hI]
  exact subset_maximalExtension intervalAtlas_isContDiffAtlas (by simp [intervalAtlas])

theorem intervalAtlas_subset (I : SmoothManifold 1 .halfSpace unitInterval)
    (hI : I.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas) :
    intervalAtlas ⊆ I.smoothStructure.val := by
  rw [hI]
  exact subset_maximalExtension intervalAtlas_isContDiffAtlas

@[simp] theorem endpointWeight_zero : endpointWeight 0 = 0 := by simp [endpointWeight]
@[simp] theorem endpointWeight_one : endpointWeight 1 = 0 := by simp [endpointWeight]

@[simp] theorem endpointWeight_reflection (t : ℝ) :
    endpointWeight (1 - t) = endpointWeight t := by unfold endpointWeight; ring

theorem endpointWeight_contDiff : ContDiff ℝ (⊤ : ℕ∞) endpointWeight := by
  unfold endpointWeight
  fun_prop

theorem endpointWeight_pos {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    0 < endpointWeight t := mul_pos ht (sub_pos.mpr ht')

theorem endpointWeight_nonneg (t : unitInterval) : 0 ≤ endpointWeight t.val :=
  mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)

/-- A uniform quantitative bound, independent of any compactness of M. -/
theorem endpointWeight_le_quarter (t : unitInterval) : endpointWeight t.val ≤ 1 / 4 := by
  dsimp [endpointWeight]
  nlinarith [sq_nonneg (t.val - 1 / 2)]

@[simp] theorem perturbation_zero {n : ℕ} {M : Type u}
    (H : unitInterval × M → ULift.{u} (Euclidean n)) (a : Euclidean n) (p : M) :
    perturbation H a (0, p) = H (0, p) := by
  apply ULift.down_injective
  simp [perturbation]

@[simp] theorem perturbation_one {n : ℕ} {M : Type u}
    (H : unitInterval × M → ULift.{u} (Euclidean n)) (a : Euclidean n) (p : M) :
    perturbation H a (1, p) = H (1, p) := by
  apply ULift.down_injective
  simp [perturbation]

/-- The perturbation is continuous on the entire closed cylinder. -/
theorem perturbation_continuous {n : ℕ} {M : Type u} [TopologicalSpace M]
    (H : unitInterval × M → ULift.{u} (Euclidean n)) (hH : Continuous H)
    (a : Euclidean n) : Continuous (perturbation H a) := by
  have ht : Continuous (fun z : unitInterval × M => endpointWeight z.1.val) := by
    unfold endpointWeight
    fun_prop
  exact (Homeomorph.ulift.symm.continuous.comp
    ((Homeomorph.ulift.continuous.comp hH).add (ht.smul continuous_const)))

/-- The Euclidean size of the change is globally at most a quarter of ‖a‖. -/
theorem perturbation_dist_le {n : ℕ} {M : Type u}
    (H : unitInterval × M → ULift.{u} (Euclidean n)) (a : Euclidean n)
    (z : unitInterval × M) :
    ‖(perturbation H a z).down - (H z).down‖ ≤ ‖a‖ / 4 := by
  simp only [perturbation, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (endpointWeight_nonneg z.1)]
  calc
    endpointWeight z.1.val * ‖a‖ ≤ (1 / 4 : ℝ) * ‖a‖ :=
      mul_le_mul_of_nonneg_right (endpointWeight_le_quarter z.1) (norm_nonneg _)
    _ = ‖a‖ / 4 := by ring

/-- For a positive-dimensional half-space, its face is its linear part. -/
theorem halfSpace_face_iff_neg_mem {d : ℕ} (hd : 0 < d) (x : Euclidean d)
    (hx : x ∈ modelSet d .halfSpace) :
    x ∈ modelFace d .halfSpace ↔ -x ∈ modelSet d .halfSpace := by
  cases d with
  | zero => omega
  | succ d =>
    change 0 ≤ x (Fin.last d) at hx
    change x (Fin.last d) = 0 ↔ 0 ≤ -x (Fin.last d)
    constructor <;> intro h <;> linarith

/-- Every permitted linear product coordinate identification preserves the
face; the result does not depend on a chosen coordinate permutation. -/
theorem product_face_iff {m : ℕ}
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
    (x : ModelSpace 1 .halfSpace) (y : ModelSpace m .euclidean) :
    C.linearEquiv (x.val, y.val) ∈ modelFace (1 + m) .halfSpace ↔
      x.val ∈ modelFace 1 .halfSpace := by
  rw [halfSpace_face_iff_neg_mem (by omega) _ ((C.mem_model _).mpr
    ⟨x.property, y.property⟩), halfSpace_face_iff_neg_mem (by decide) _ x.property]
  rw [← map_neg, C.mem_model]
  change (-x.val ∈ modelSet 1 .halfSpace ∧ -y.val ∈ modelSet m .euclidean) ↔ _
  simp only [ModelData.modelSet, mem_univ, and_true]

theorem cylinder_productChart_mem {m : ℕ} {M : Type u} [TopologicalSpace M]
    (E : SmoothManifold m .euclidean M)
    (I : SmoothManifold 1 .halfSpace unitInterval)
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C I.smoothStructure.val E.smoothStructure.val))
    {c : ModelChart 1 .halfSpace unitInterval} (hc : c ∈ I.smoothStructure.val)
    {d : ModelChart m .euclidean M} (hd : d ∈ E.smoothStructure.val) :
    productChart C c d ∈ Q.smoothStructure.val := by
  rw [hQ]
  exact subset_maximalExtension (productAtlas_isContDiffAtlas C _ _ _
    I.smoothStructure.property.1 E.smoothStructure.property.1) ⟨c, hc, d, hd, rfl⟩

/-- An ambient polynomial realizing the endpoint weight in both interval
charts: t(1-t) is invariant under the right-end coordinate t ↦ 1-t. -/
def weightExtension {m : ℕ}
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
    (x : Euclidean (1 + m)) : ℝ := endpointWeight ((C.linearEquiv.symm x).1 0)

theorem weightExtension_contDiff {m : ℕ}
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace) :
    ContDiff ℝ (⊤ : ℕ∞) (weightExtension C) := by
  apply endpointWeight_contDiff.comp
  fun_prop

theorem weightExtension_productChart {m : ℕ} {M : Type u} [TopologicalSpace M]
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
    {c : ModelChart 1 .halfSpace unitInterval} (hc : c ∈ intervalAtlas)
    (d : ModelChart m .euclidean M) (z : unitInterval × M) :
    weightExtension C ((productChart C c d) z).val = endpointWeight z.1.val := by
  simp only [weightExtension, productChart_val, C.linearEquiv.symm_apply_apply]
  have hc' : c = intervalLeftChart ∨ c = intervalRightChart := by
    simpa only [intervalAtlas, mem_insert_iff, mem_singleton_iff] using hc
  rcases hc' with rfl | rfl
  · rfl
  · exact endpointWeight_reflection _

/-- Smoothness of each prescribed perturbation follows from an explicit ambient
extension in a product chart; in particular it holds at both endpoints. -/
theorem perturbation_smooth {m n : ℕ} {M : Type u} [TopologicalSpace M]
    (E : SmoothManifold m .euclidean M)
    (I : SmoothManifold 1 .halfSpace unitInterval)
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (hI : I.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas)
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C I.smoothStructure.val E.smoothStructure.val))
    (hT : liftedEuclideanChart n ∈ T.smoothStructure.val)
    (H : unitInterval × M → ULift.{u} (Euclidean n)) (hH : IsSmoothMap Q T H)
    (a : Euclidean n) : IsSmoothMap Q T (perturbation H a) := by
  intro z
  obtain ⟨c, hc, hcz⟩ := intervalAtlas_isContDiffAtlas.1 z.1
  obtain ⟨d, hd, hdz⟩ := E.smoothStructure.property.1.1 z.2
  have hcd := cylinder_productChart_mem E I C Q hQ (intervalAtlas_subset I hI hc) hd
  have hz : z ∈ (productChart C c d).source := by
    rw [productChart_source]; exact ⟨hcz, hdz⟩
  have hsrc : ∀ y : ULift.{u} (Euclidean n), y ∈ (liftedEuclideanChart n).source :=
    fun _ => mem_univ _
  obtain ⟨U, hU, hzU, G, hG, heG⟩ :=
    (hH z).2 _ hcd _ hT hz (hsrc _)
  apply (manifoldContDiffAt_iff_oneChart _ _ _ Q.smoothStructure.property.1
    T.smoothStructure.property.1 _ z).mpr
  refine ⟨(perturbation_continuous H
    (continuous_iff_continuousAt.mpr fun x => (hH x).1) a).continuousAt,
    _, hcd, _, hT, hz, hsrc _, U, hU, hzU,
    fun x => G x + weightExtension C x • a,
    hG.add ((weightExtension_contDiff C).contDiffOn.smul contDiffOn_const), ?_⟩
  filter_upwards [heG] with y hy
  change G ((productChart C c d) y).val +
      weightExtension C ((productChart C c d) y).val • a =
    (H y).down + endpointWeight y.1.val • a
  change G ((productChart C c d) y).val = (H y).down at hy
  rw [hy, weightExtension_productChart C hc d y]

/-- The intrinsic boundary of the standard cylinder is exactly its two ends.
Only the boundaryless Euclidean representation of M is used. -/
theorem cylinder_boundary {m : ℕ} {M : Type u} [TopologicalSpace M]
    (E : SmoothManifold m .euclidean M)
    (I : SmoothManifold 1 .halfSpace unitInterval)
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (hI : I.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas)
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C I.smoothStructure.val E.smoothStructure.val)) :
    intrinsicBoundary Q = ({0, 1} : Set unitInterval) ×ˢ (univ : Set M) := by
  ext z
  obtain ⟨d, hd, hdz⟩ := E.smoothStructure.property.1.1 z.2
  have hz0 : z.1 = 0 ↔ z.1.val = 0 := Subtype.ext_iff
  have hz1 : z.1 = 1 ↔ z.1.val = 1 := Subtype.ext_iff
  by_cases ht : z.1.val < 1
  · rw [intrinsicBoundary_iff_chart Q (productChart C intervalLeftChart d)
      (cylinder_productChart_mem E I C Q hQ (intervalLeftChart_mem I hI) hd)
      z (by rw [productChart_source]; exact ⟨ht, hdz⟩), productChart_val,
      product_face_iff]
    change z.1.val = 0 ↔ _
    simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_univ, and_true, hz0, hz1]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · linarith
  · have ht' : 0 < z.1.val := by linarith
    have hr : z.1 ∈ intervalRightChart.source := by
      rw [intervalRightChart_source]; exact ht'
    rw [intrinsicBoundary_iff_chart Q (productChart C intervalRightChart d)
      (cylinder_productChart_mem E I C Q hQ (intervalRightChart_mem I hI) hd)
      z (by rw [productChart_source]; exact ⟨hr, hdz⟩), productChart_val,
      product_face_iff]
    change 1 - z.1.val = 0 ↔ _
    simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_univ, and_true, hz0, hz1]
    constructor
    · intro h; right; linarith
    · rintro (h | h) <;> linarith

/-- The natural boundary structure required by the conditional upstream
interface exists on every cylinder, including an empty cylinder. -/
theorem cylinder_natural_boundary_exists {m : ℕ} {M : Type u} [TopologicalSpace M]
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M)) :
    ∃ B : SmoothManifold ((1 + m) - 1) .euclidean (intrinsicBoundary Q),
      IsNaturalBoundaryStructure Q B := by
  generalize hd : 1 + m = d at Q ⊢
  cases d with
  | zero => omega
  | succ d =>
    obtain ⟨B, hB, hface⟩ := exists_boundary_smoothManifold Q
    exact ⟨B, hB, hface⟩

/-- All structural choices in the independent target are available for every
boundaryless M. Thus none of its atlas or boundary premises restricts the
geometric scope of the original homotopy example. -/
theorem cylinder_structures_exist {m : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m b M) (hS : intrinsicBoundary S = ∅) :
    ∃ (E : SmoothManifold m .euclidean M)
      (I : SmoothManifold 1 .halfSpace unitInterval)
      (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
      (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
      (B : SmoothManifold ((1 + m) - 1) .euclidean (intrinsicBoundary Q)),
      IsSmoothMap S E id ∧ IsSmoothMap E S id ∧
      I.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas ∧
      Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (productAtlas C I.smoothStructure.val E.smoothStructure.val) ∧
      IsNaturalBoundaryStructure Q B := by
  obtain ⟨E, hSE, hES⟩ := exists_boundaryless_euclidean_smoothManifold S hS
  obtain ⟨C, _⟩ := exists_leftHalfSpace_productCoordinates 0 m
  obtain ⟨Q, _, hQ⟩ := exists_product_smoothManifold intervalManifold E C
  obtain ⟨B, hB⟩ := cylinder_natural_boundary_exists Q
  exact ⟨E, intervalManifold, C, Q, B, hSE, hES, rfl, hQ, hB⟩

/-- Set-theoretic identification of the endpoint fibers uses equality of maps,
not merely a homotopy of their restrictions. -/
theorem perturbation_boundary_fibers {m n : ℕ} {M : Type u} [TopologicalSpace M]
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (hQ : intrinsicBoundary Q = ({0, 1} : Set unitInterval) ×ˢ (univ : Set M))
    (H : unitInterval × M → ULift.{u} (Euclidean n))
    (s : Set (ULift.{u} (Euclidean n))) (a : Euclidean n) :
    perturbation H a ⁻¹' s ∩ intrinsicBoundary Q = endpointFibers H s := by
  ext ⟨t, p⟩
  rw [hQ]
  simp only [endpointFibers, mem_inter_iff, mem_preimage, mem_prod, mem_insert_iff,
    mem_singleton_iff, mem_univ, and_true, mem_union, mem_ofPred_eq]
  constructor
  · rintro ⟨h, rfl | rfl⟩
    · exact Or.inl ⟨rfl, by simpa using h⟩
    · exact Or.inr ⟨rfl, by simpa using h⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨by simpa using h, Or.inl rfl⟩
    · exact ⟨by simpa using h, Or.inr rfl⟩

/-- A map into the natural boundary is smooth whenever its ambient inclusion
is smooth. The coordinate extension is obtained by dropping the normal entry. -/
theorem boundary_lift_smooth {d l : ℕ} {b c : ModelKind} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold d b X)
    (B : SmoothManifold (d - 1) .euclidean (intrinsicBoundary S))
    (U : SmoothManifold l c Y) (hB : IsNaturalBoundaryStructure S B)
    (g : Y → X) (hg : IsSmoothMap U S g)
    (hb : ∀ y, g y ∈ intrinsicBoundary S) :
    IsSmoothMap U B (fun y => ⟨g y, hb y⟩) := by
  intro y
  cases d with
  | zero => exact ((Set.ext_iff.mp (intrinsicBoundary_zero S) (g y)).mp (hb y)).elim
  | succ d =>
    obtain ⟨e, he, hey⟩ := U.smoothStructure.property.1.1 y
    obtain ⟨a, ha, hay⟩ := S.smoothStructure.property.1.1 (g y)
    obtain ⟨f, hf, hface⟩ := hB.2 a ha ⟨⟨⟨g y, hb y⟩, hay⟩⟩
    have hfy : (⟨g y, hb y⟩ : intrinsicBoundary S) ∈ f.source := by
      rw [hface.1]; exact hay
    obtain ⟨V, hV, hyV, G, hG, heG⟩ := (hg y).2 e he a ha hey hay
    apply (manifoldContDiffAt_iff_oneChart _ _ _ U.smoothStructure.property.1
      B.smoothStructure.property.1 _ y).mpr
    refine ⟨((continuous_iff_continuousAt.mpr fun x => (hg x).1).subtype_mk hb).continuousAt,
      e, he, f, hf, hey, hfy,
      V, hV, hyV, fun z i => G z i.castSucc, contDiffOn_pi.mpr
        (fun i => (contDiffOn_pi.mp hG) i.castSucc), ?_⟩
    filter_upwards [heG, (hg y).1.preimage_mem_nhds (a.open_source.mem_nhds hay)] with z hz hza
    ext i
    change G (e z).val i.castSucc = (f ⟨g z, hb z⟩).val i
    rw [hz]
    exact (hface.2.2 ⟨g z, hb z⟩ (by rw [hface.1]; exact hza) i).symm

/-- Transversality can be checked on a smooth map into the source: the
derivative of a composition has image contained in the outer derivative. -/
theorem transverseAt_of_precomp {d l n k : ℕ} {b c e r : ModelKind}
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (U : SmoothManifold d b X) (V : SmoothManifold l c Y)
    (T : SmoothManifold n e Z) {s : Set Z} (R : SmoothManifold k r s)
    (f : X → Z) (g : Y → X) (hf : IsSmoothMap U T f) (hg : IsSmoothMap V U g)
    (y : Y) (hy : f (g y) ∈ s)
    (h : IsTransverseAt V T R (f ∘ g) y hy) : IsTransverseAt U T R f (g y) hy := by
  intro L I hL hI
  obtain ⟨J, hJ, _⟩ := differential_exists V U g hg y
  have hcomp := h (L.comp J) I (differential_comp V U T g f hg hf y J L hJ hL) hI
  have hrange : LinearMap.range (L.comp J) ≤ LinearMap.range L := by
    rintro _ ⟨v, rfl⟩
    exact ⟨J v, rfl⟩
  exact top_le_iff.mp (hcomp ▸ sup_le_sup_right hrange (LinearMap.range I))

/-- Constants are smooth in the shared local extension calculus. -/
theorem constant_smooth {d l : ℕ} {b c : ModelKind} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : SmoothManifold d b X) (V : SmoothManifold l c Y) (y : Y) :
    IsSmoothMap U V (fun _ => y) := by
  intro x
  refine ⟨continuousAt_const, ?_⟩
  intro e _ f _ _ _
  exact ⟨univ, isOpen_univ, mem_univ _, fun _ => (f y).val,
    contDiffOn_const, Eventually.of_forall fun _ => rfl⟩

/-- The coordinate lift of an ordinary smooth Euclidean function is smooth
between any structures containing the standard global coordinate charts. -/
theorem lifted_euclidean_smooth {n l : ℕ}
    (A : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (T : SmoothManifold l .euclidean (ULift.{u} (Euclidean l)))
    (hA : liftedEuclideanChart n ∈ A.smoothStructure.val)
    (hT : liftedEuclideanChart l ∈ T.smoothStructure.val)
    (f : Euclidean n → Euclidean l) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsSmoothMap A T (fun x => ULift.up (f x.down)) := by
  intro x
  apply (manifoldContDiffAt_iff_oneChart _ _ _ A.smoothStructure.property.1
    T.smoothStructure.property.1 _ x).mpr
  exact ⟨(Homeomorph.ulift.symm.continuous.comp
    (hf.continuous.comp Homeomorph.ulift.continuous)).continuousAt,
    _, hA, _, hT, mem_univ _, mem_univ _, univ, isOpen_univ, mem_univ _,
    f, hf.contDiffOn, Eventually.of_forall fun _ => rfl⟩

/-- A nonzero parameter coefficient gives an actual affine diffeomorphism.
This is the parameter-derivative argument without a choice of tangent basis. -/
noncomputable def affineParameterDiffeomorph {n : ℕ}
    (A T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (hA : liftedEuclideanChart n ∈ A.smoothStructure.val)
    (hT : liftedEuclideanChart n ∈ T.smoothStructure.val)
    (b : Euclidean n) (c : ℝ) (hc : c ≠ 0) :
    Diffeomorph A.smoothStructure.val T.smoothStructure.val where
  toEquiv := {
    toFun x := ULift.up (b + c • x.down)
    invFun y := ULift.up (c⁻¹ • (y.down - b))
    left_inv x := by
      apply ULift.down_injective
      simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
    right_inv y := by
      apply ULift.down_injective
      simp only [smul_smul, mul_inv_cancel₀ hc, one_smul]
      abel }
  contDiff_toFun := lifted_euclidean_smooth A T hA hT (fun x => b + c • x) (by fun_prop)
  contDiff_invFun := lifted_euclidean_smooth T A hT hA (fun y => c⁻¹ • (y - b)) (by fun_prop)

theorem affineParameter_transverse {n k : ℕ} {b : ModelKind}
    (A T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (hA : liftedEuclideanChart n ∈ A.smoothStructure.val)
    (hT : liftedEuclideanChart n ∈ T.smoothStructure.val)
    {s : Set (ULift.{u} (Euclidean n))} (R : SmoothManifold k b s)
    (v : Euclidean n) (c : ℝ) (hc : c ≠ 0) :
    IsTransverse A T R (fun x => ULift.up (v + c • x.down)) := by
  let D := affineParameterDiffeomorph A T hA hT v c hc
  change IsTransverse A T R D.toEquiv
  intro x hx L I hL _
  obtain ⟨J, hJ⟩ := differential_diffeomorph A T D x
  obtain ⟨L', _, huniq⟩ := differential_exists A T D.toEquiv D.contDiff_toFun x
  have hLJ : L = J.toLinearMap := (huniq L hL).trans (huniq J.toLinearMap hJ).symm
  rw [hLJ, LinearMap.range_eq_top.mpr J.surjective, top_sup_eq]

/-- The constant-time slices of the cylinder are smooth even at its ends. -/
theorem cylinder_slice_smooth {m : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M]
    (S : SmoothManifold m b M) (E : SmoothManifold m .euclidean M)
    (I : SmoothManifold 1 .halfSpace unitInterval)
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (hSE : IsSmoothMap S E id)
    (hI : I.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas)
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C I.smoothStructure.val E.smoothStructure.val))
    (t : unitInterval) : IsSmoothMap S Q (fun p => (t, p)) := by
  intro p
  obtain ⟨e, he, hep⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨c, hc, hct⟩ := intervalAtlas_isContDiffAtlas.1 t
  obtain ⟨d, hd, hdp⟩ := E.smoothStructure.property.1.1 p
  obtain ⟨V, hV, hpV, G, hG, heG⟩ := (hSE p).2 e he d hd hep hdp
  apply (manifoldContDiffAt_iff_oneChart _ _ _ S.smoothStructure.property.1
    Q.smoothStructure.property.1 _ p).mpr
  refine ⟨(continuous_const.prodMk continuous_id).continuousAt,
    e, he, _, cylinder_productChart_mem E I C Q hQ (intervalAtlas_subset I hI hc) hd,
    hep, ?_, V, hV, hpV, fun x => C.linearEquiv ((c t).val, G x),
    C.linearEquiv.contDiff.contDiffOn.comp (contDiffOn_const.prodMk hG)
      (mapsTo_univ _ _), ?_⟩
  · rw [productChart_source]; exact ⟨hct, hdp⟩
  · filter_upwards [heG] with y hy
    simp only [productChart_val, id_eq] at hy ⊢
    rw [hy]

/-- The whole finite-dimensional family is smooth, with a polynomial ambient
extension in each product chart. -/
theorem perturbation_family_smooth {m n : ℕ} {M : Type u} [TopologicalSpace M]
    (E : SmoothManifold m .euclidean M)
    (I : SmoothManifold 1 .halfSpace unitInterval)
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (A T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (D : ProductCoordinates n .euclidean (1 + m) .halfSpace .halfSpace)
    (FQ : SmoothManifold (n + (1 + m)) .halfSpace
      (ULift.{u} (Euclidean n) × (unitInterval × M)))
    (hI : I.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas)
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C I.smoothStructure.val E.smoothStructure.val))
    (hA : liftedEuclideanChart n ∈ A.smoothStructure.val)
    (hT : liftedEuclideanChart n ∈ T.smoothStructure.val)
    (hFQ : FQ.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas D A.smoothStructure.val Q.smoothStructure.val))
    (H : unitInterval × M → ULift.{u} (Euclidean n)) (hH : IsSmoothMap Q T H) :
    IsSmoothMap FQ T (fun z => perturbation H z.1.down z.2) := by
  intro z
  obtain ⟨c, hc, hct⟩ := intervalAtlas_isContDiffAtlas.1 z.2.1
  obtain ⟨d, hd, hdp⟩ := E.smoothStructure.property.1.1 z.2.2
  have hcd := cylinder_productChart_mem E I C Q hQ (intervalAtlas_subset I hI hc) hd
  have hz : z.2 ∈ (productChart C c d).source := by
    rw [productChart_source]; exact ⟨hct, hdp⟩
  have heF : productChart D (liftedEuclideanChart n) (productChart C c d) ∈
      FQ.smoothStructure.val := by
    rw [hFQ]
    exact subset_maximalExtension (productAtlas_isContDiffAtlas D _ _ _
      A.smoothStructure.property.1 Q.smoothStructure.property.1)
      ⟨_, hA, _, hcd, rfl⟩
  obtain ⟨V, hV, hzV, G, hG, heG⟩ := (hH z.2).2 _ hcd _ hT hz (mem_univ _)
  have hcont : Continuous (fun w : ULift.{u} (Euclidean n) × (unitInterval × M) =>
      perturbation H w.1.down w.2) := by
    unfold perturbation endpointWeight
    have hHcont := continuous_iff_continuousAt.mpr fun x => (hH x).1
    fun_prop
  apply (manifoldContDiffAt_iff_oneChart _ _ _ FQ.smoothStructure.property.1
    T.smoothStructure.property.1 _ z).mpr
  refine ⟨hcont.continuousAt, _, heF, _, hT, ?_, mem_univ _,
    (fun x => (D.linearEquiv.symm x).2) ⁻¹' V,
    hV.preimage (continuous_snd.comp D.linearEquiv.symm.continuous), ?_,
    fun x => G (D.linearEquiv.symm x).2 +
      weightExtension C (D.linearEquiv.symm x).2 • (D.linearEquiv.symm x).1, ?_, ?_⟩
  · rw [productChart_source]; exact ⟨mem_univ _, hz⟩
  · simpa only [mem_preimage, productChart_val, D.linearEquiv.symm_apply_apply] using hzV
  · apply (hG.comp D.linearEquiv.symm.contDiff.snd.contDiffOn (fun _ h => h)).add
    exact (((weightExtension_contDiff C).comp D.linearEquiv.symm.contDiff.snd).smul
      D.linearEquiv.symm.contDiff.fst).contDiffOn
  · have heG' := heG.comp_tendsto (continuous_snd.continuousAt :
        ContinuousAt Prod.snd z)
    filter_upwards [heG'] with y hy
    simp only [productChart_val, D.linearEquiv.symm_apply_apply]
    change G ((productChart C c d) y.2).val +
      weightExtension C ((productChart C c d) y.2).val • y.1.down =
      (H y.2).down + endpointWeight y.2.1.val • y.1.down
    change G ((productChart C c d) y.2).val = (H y.2).down at hy
    rw [hy, weightExtension_productChart C hc d y.2]

/-- The family is transverse on the full cylinder: in its interior the
parameter slice is an affine diffeomorphism; at an end the original transverse
endpoint map factors through the family. -/
theorem perturbation_family_transverse {m n k : ℕ} {b c : ModelKind}
    {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m b M)
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (A T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (s : Set (ULift.{u} (Euclidean n))) (R : SmoothManifold k c s)
    (D : ProductCoordinates n .euclidean (1 + m) .halfSpace .halfSpace)
    (FQ : SmoothManifold (n + (1 + m)) .halfSpace
      (ULift.{u} (Euclidean n) × (unitInterval × M)))
    (hA : liftedEuclideanChart n ∈ A.smoothStructure.val)
    (hT : liftedEuclideanChart n ∈ T.smoothStructure.val)
    (hFQ : FQ.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas D A.smoothStructure.val Q.smoothStructure.val))
    (H : unitInterval × M → ULift.{u} (Euclidean n))
    (hF : IsSmoothMap FQ T (fun z => perturbation H z.1.down z.2))
    (hslice : ∀ t, IsSmoothMap S Q (fun p => (t, p)))
    (h0 : IsTransverse S T R (fun p => H (0, p)))
    (h1 : IsTransverse S T R (fun p => H (1, p))) :
    IsTransverse FQ T R (fun z => perturbation H z.1.down z.2) := by
  rintro ⟨a, t, p⟩ hp
  by_cases ht0 : t = 0
  · subst t
    let g : M → ULift.{u} (Euclidean n) × (unitInterval × M) := fun x => (a, (0, x))
    have hg : IsSmoothMap S FQ g :=
      (differential_pair A Q S D FQ hFQ (fun _ => a) (fun x => (0, x))
        (constant_smooth S A a) (hslice 0)).1
    apply transverseAt_of_precomp FQ S T R _ g hF hg p hp
    have heq : (fun z => perturbation H z.1.down z.2) ∘ g = (fun x => H (0, x)) := by
      funext x; exact perturbation_zero H a.down x
    have ht : IsTransverse S T R ((fun z => perturbation H z.1.down z.2) ∘ g) :=
      heq.symm ▸ h0
    exact ht p hp
  by_cases ht1 : t = 1
  · subst t
    let g : M → ULift.{u} (Euclidean n) × (unitInterval × M) := fun x => (a, (1, x))
    have hg : IsSmoothMap S FQ g :=
      (differential_pair A Q S D FQ hFQ (fun _ => a) (fun x => (1, x))
        (constant_smooth S A a) (hslice 1)).1
    apply transverseAt_of_precomp FQ S T R _ g hF hg p hp
    have heq : (fun z => perturbation H z.1.down z.2) ∘ g = (fun x => H (1, x)) := by
      funext x; exact perturbation_one H a.down x
    have ht : IsTransverse S T R ((fun z => perturbation H z.1.down z.2) ∘ g) :=
      heq.symm ▸ h1
    exact ht p hp
  · have ht0' : t.val ≠ 0 := fun h => ht0 (Subtype.ext h)
    have ht1' : t.val ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hc : endpointWeight t.val ≠ 0 := ne_of_gt
      (endpointWeight_pos (by have := t.property.1; exact lt_of_le_of_ne this ht0'.symm)
        (by have := t.property.2; exact lt_of_le_of_ne this ht1'))
    let g : ULift.{u} (Euclidean n) → ULift.{u} (Euclidean n) × (unitInterval × M) :=
      fun x => (x, (t, p))
    have hg : IsSmoothMap A FQ g :=
      (differential_pair A Q A D FQ hFQ id (fun _ => (t, p))
        (manifoldContDiff_id _ _ A.smoothStructure.property.1)
        (constant_smooth A Q (t, p))).1
    apply transverseAt_of_precomp FQ A T R _ g hF hg a hp
    exact affineParameter_transverse A T hA hT R (H (t, p)).down
      (endpointWeight t.val) hc a hp

/-- Boundary transversality uses the tangent spaces of the natural boundary,
through smooth lifts of the endpoint slices. -/
theorem perturbation_family_boundary_transverse {m n k : ℕ} {b c : ModelKind}
    {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m b M)
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (B : SmoothManifold ((1 + m) - 1) .euclidean (intrinsicBoundary Q))
    (A T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (s : Set (ULift.{u} (Euclidean n))) (R : SmoothManifold k c s)
    (D : ProductCoordinates n .euclidean (1 + m) .halfSpace .halfSpace)
    (FQ : SmoothManifold (n + (1 + m)) .halfSpace
      (ULift.{u} (Euclidean n) × (unitInterval × M)))
    (DB : ProductCoordinates n .euclidean ((1 + m) - 1) .euclidean .euclidean)
    (FB : SmoothManifold (n + ((1 + m) - 1)) .euclidean
      (ULift.{u} (Euclidean n) × intrinsicBoundary Q))
    (hFQ : FQ.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas D A.smoothStructure.val Q.smoothStructure.val))
    (hFB : FB.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas DB A.smoothStructure.val B.smoothStructure.val))
    (hB : IsNaturalBoundaryStructure Q B)
    (hb : intrinsicBoundary Q = ({0, 1} : Set unitInterval) ×ˢ (univ : Set M))
    (H : unitInterval × M → ULift.{u} (Euclidean n))
    (hF : IsSmoothMap FQ T (fun z => perturbation H z.1.down z.2))
    (hslice : ∀ t, IsSmoothMap S Q (fun p => (t, p)))
    (h0 : IsTransverse S T R (fun p => H (0, p)))
    (h1 : IsTransverse S T R (fun p => H (1, p))) :
    IsTransverse FB T R (fun z => perturbation H z.1.down z.2.val) := by
  have hproj := differential_product A B DB FB hFB
  have hsecond : IsSmoothMap FB Q (fun z => z.2.val) :=
    manifoldContDiff_comp _ _ _ _ B.smoothStructure.property.1.1 _ _ hproj.2.1 hB.1
  have hj : IsSmoothMap FB FQ (fun z => (z.1, z.2.val)) :=
    (differential_pair A Q FB D FQ hFQ Prod.fst (fun z => z.2.val)
      hproj.1 hsecond).1
  have hFboundary : IsSmoothMap FB T (fun z => perturbation H z.1.down z.2.val) :=
    manifoldContDiff_comp _ _ _ _ FQ.smoothStructure.property.1.1 _ _ hj hF
  have hend0 (p : M) : (0, p) ∈ intrinsicBoundary Q := by
    rw [hb]; exact ⟨by simp, mem_univ _⟩
  have hend1 (p : M) : (1, p) ∈ intrinsicBoundary Q := by
    rw [hb]; exact ⟨by simp, mem_univ _⟩
  have hs0 : IsSmoothMap S B (fun p => ⟨(0, p), hend0 p⟩) :=
    boundary_lift_smooth Q B S hB _ (hslice 0) hend0
  have hs1 : IsSmoothMap S B (fun p => ⟨(1, p), hend1 p⟩) :=
    boundary_lift_smooth Q B S hB _ (hslice 1) hend1
  rintro ⟨a, ⟨⟨t, p⟩, hp⟩⟩ hmem
  have ht : t = 0 ∨ t = 1 := by
    rw [hb] at hp
    simpa only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_univ, and_true] using hp
  rcases ht with rfl | rfl
  · let g : M → ULift.{u} (Euclidean n) × intrinsicBoundary Q :=
      fun x => (a, ⟨(0, x), hend0 x⟩)
    have hg : IsSmoothMap S FB g :=
      (differential_pair A B S DB FB hFB (fun _ => a) _ (constant_smooth S A a) hs0).1
    apply transverseAt_of_precomp FB S T R _ g hFboundary hg p hmem
    have heq : (fun z => perturbation H z.1.down z.2.val) ∘ g = (fun x => H (0, x)) := by
      funext x; exact perturbation_zero H a.down x
    have ht : IsTransverse S T R ((fun z => perturbation H z.1.down z.2.val) ∘ g) :=
      heq.symm ▸ h0
    exact ht p hmem
  · let g : M → ULift.{u} (Euclidean n) × intrinsicBoundary Q :=
      fun x => (a, ⟨(1, x), hend1 x⟩)
    have hg : IsSmoothMap S FB g :=
      (differential_pair A B S DB FB hFB (fun _ => a) _ (constant_smooth S A a) hs1).1
    apply transverseAt_of_precomp FB S T R _ g hFboundary hg p hmem
    have heq : (fun z => perturbation H z.1.down z.2.val) ∘ g = (fun x => H (1, x)) := by
      funext x; exact perturbation_one H a.down x
    have ht : IsTransverse S T R ((fun z => perturbation H z.1.down z.2.val) ∘ g) :=
      heq.symm ▸ h1
    exact ht p hmem

/-- Chart-null sets in standard parameter space cannot fill any ball, also
when n=0 (where volume is counting measure on the one-point space). -/
theorem exists_small_parameter_outside_null {n : ℕ}
    (A : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (hA : liftedEuclideanChart n ∈ A.smoothStructure.val)
    (bad : Set (ULift.{u} (Euclidean n))) (hbad : SardData.IsNull A bad)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Euclidean n, ‖a‖ < ε ∧ ULift.up.{u} a ∉ bad := by
  by_contra h
  have hall : ∀ a : Euclidean n, ‖a‖ < ε → ULift.up.{u} a ∈ bad := by
    simpa only [not_exists, not_and, not_not] using h
  have hnull := hbad (liftedEuclideanChart n) hA
  have hsub : Metric.ball (0 : Euclidean n) ε ⊆
      (fun y => ((liftedEuclideanChart n) y).val) ''
        (bad ∩ (liftedEuclideanChart n).source) := by
    intro a ha
    refine ⟨ULift.up.{u} a, ⟨hall a ?_, mem_univ _⟩, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right] using ha
  have hzero := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub
  rw [hnull] at hzero
  exact (ne_of_gt (Metric.measure_ball_pos MeasureTheory.volume (0 : Euclidean n) hε))
    (le_antisymm hzero bot_le)

/-- All inverse-image assertions follow from the exact frozen premises once
a smooth transverse perturbation has been obtained. -/
theorem preimage_conclusion_of_transverse
    (_hparam : Specs.SmoothManifolds.Ch04.ParametricTransversality.parametric_transversalityType.{u})
    (_htranslation : Specs.SmoothManifolds.Ch04.ParametricTransversality.translation_perturbationType.{u})
    (hdimension : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_dimensionType.{u})
    (hstructure : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_structureType.{u})
    (htangent : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_tangentType.{u})
    {m n k : ℕ} {c : ModelKind} {M : Type u} [TopologicalSpace M]
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (B : SmoothManifold ((1 + m) - 1) .euclidean (intrinsicBoundary Q))
    (T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (s : Set (ULift.{u} (Euclidean n))) (R : SmoothManifold k c s)
    (H : unitInterval × M → ULift.{u} (Euclidean n)) (a : Euclidean n)
    (hb : intrinsicBoundary Q = ({0, 1} : Set unitInterval) ×ˢ (univ : Set M))
    (hB : IsNaturalBoundaryStructure Q B) (hR : intrinsicBoundary R = ∅)
    (hRT : IsSmoothEmbedding R T Subtype.val)
    (hK : IsSmoothMap Q T (perturbation H a))
    (htrans : IsTransverse Q T R (perturbation H a))
    (htransB : IsTransverse B T R (fun p => perturbation H a p.val)) :
    PreimageConclusion Q T R H a := by
  have hT : intrinsicBoundary T = ∅ := intrinsicBoundary_euclidean T
  obtain ⟨hbound, hempty, hboundarybound⟩ :=
    hdimension Q T s R (perturbation H a) B hT hR hRT hK hB htrans htransB
  obtain ⟨P, hPQ, hPb, hPd⟩ :=
    hstructure Q T s R (perturbation H a) B hT hR hRT hK hB htrans htransB
  refine ⟨hbound, hempty, ?_, P, hPQ, ?_, hPd, ?_⟩
  · intro h
    simpa only [Nat.add_sub_cancel_left] using (hboundarybound h).2
  · ext p
    rw [hPb]
    change p.val ∈ intrinsicBoundary Q ↔ p.val ∈ endpointFibers H s
    rw [← perturbation_boundary_fibers Q hb H s a]
    exact ⟨fun hp => ⟨p.property, hp⟩, fun hp => hp.2⟩
  · exact htangent Q T s R (perturbation H a) hT hR hRT hK htrans P hPQ

/-- Conditional draft of the complete source example. The five frozen
upstream propositions are explicit parameters in their prescribed order.
No declaration of the closed original target is made here. -/
theorem transverse_homotopy_conditional
    (hparam : Specs.SmoothManifolds.Ch04.ParametricTransversality.parametric_transversalityType.{u})
    (htranslation : Specs.SmoothManifolds.Ch04.ParametricTransversality.translation_perturbationType.{u})
    (hdimension : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_dimensionType.{u})
    (hstructure : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_structureType.{u})
    (htangent : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_tangentType.{u}) :
    Specs.SmoothManifolds.Ch04.TransverseHomotopy.transverse_homotopyType.{u} := by
  intro m n k b c M _ S E I C Q B T s R H _hS hSE _hES hI hQ hB hT hR hRT hH h0 h1 ε hε
  obtain ⟨D0, _⟩ := exists_rightHalfSpace_productCoordinates n m
  let D : ProductCoordinates n .euclidean (1 + m) .halfSpace .halfSpace := by
    simpa only [Nat.add_comm 1 m] using D0
  obtain ⟨FQ, _, hFQ⟩ := exists_product_smoothManifold T Q D
  obtain ⟨DB⟩ := exists_euclidean_productCoordinates n ((1 + m) - 1)
  obtain ⟨FB, _, hFB⟩ := exists_product_smoothManifold T B DB
  have hF := perturbation_family_smooth E I C Q T T D FQ hI hQ hT hT hFQ H hH
  have hslice := cylinder_slice_smooth S E I C Q hSE hI hQ
  have hfull := perturbation_family_transverse S Q T T s R D FQ hT hT hFQ H hF hslice h0 h1
  have hb := cylinder_boundary E I C Q hI hQ
  have hboundary := perturbation_family_boundary_transverse S Q B T T s R D FQ DB FB
    hFQ hFB hB hb H hF hslice h0 h1
  have hid : IsSmoothMap T T id := manifoldContDiff_id _ _ T.smoothStructure.property.1
  obtain ⟨bad, hbad, _, hgood⟩ := hparam T T Q T s R B D FQ DB FB
    (fun z => perturbation H z.1.down z.2)
    (intrinsicBoundary_euclidean T) hid hid hB hFQ hFB
    (intrinsicBoundary_euclidean T) hR hRT hF hfull hboundary
  obtain ⟨a, ha, habad⟩ := exists_small_parameter_outside_null T hT bad hbad ε hε
  have hgooda := hgood (ULift.up.{u} a) habad
  change IsTransverse Q T R (perturbation H a) ∧
    IsTransverse B T R (fun p => perturbation H a p.val) at hgooda
  have hKa := perturbation_smooth E I C Q T hI hQ hT H hH a
  exact ⟨a, ha, hKa, hgooda.1, hgooda.2, perturbation_zero H a, perturbation_one H a,
    preimage_conclusion_of_transverse hparam htranslation hdimension hstructure htangent
      Q B T s R H a hb hB hR hRT hKa hgooda.1 hgooda.2⟩

end SmoothManifolds.TransverseHomotopy

universe v8_closure_2c07313491f04bd7_u0
theorem _root_.«SmoothManifolds».«TransverseHomotopy».«transverse_homotopy» : _root_.«Specs».«SmoothManifolds».«Ch04».«TransverseHomotopy».«transverse_homotopyType».{v8_closure_2c07313491f04bd7_u0} :=
  @_root_.«SmoothManifolds».«TransverseHomotopy».«transverse_homotopy_conditional».{v8_closure_2c07313491f04bd7_u0} (@_root_.«SmoothManifolds».«ParametricTransversality».«parametric_transversality».{v8_closure_2c07313491f04bd7_u0}) (@_root_.«SmoothManifolds».«ParametricTransversality».«translation_perturbation».{v8_closure_2c07313491f04bd7_u0}) (@_root_.«SmoothManifolds».«TransversePreimage».«transverse_preimage_dimension».{v8_closure_2c07313491f04bd7_u0}) (@_root_.«SmoothManifolds».«TransversePreimage».«transverse_preimage_structure».{v8_closure_2c07313491f04bd7_u0}) (@_root_.«SmoothManifolds».«TransversePreimage».«transverse_preimage_tangent».{v8_closure_2c07313491f04bd7_u0})
