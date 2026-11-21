import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzGeometry
import MathGenome.Internal.FourierSobolev.P102.U4.GraphArea
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal Manifold ContDiff

namespace P102.Sobolev.Geometry
open P102.U4 P102.U4.GraphPieces

/-- The source bounded Lipschitz open-set predicate, on Euclidean (m+1)-space. -/
def lipschitzOpen {m : ℕ} (Ω : Set (Ambient m)) : Prop := IsLipschitzOpen Ω

/-- A Lipschitz domain is additionally connected. -/
def lipschitzDomain {m : ℕ} (Ω : Set (Ambient m)) : Prop := IsLipschitzDomain Ω

@[simp] theorem unshear_shear {m : ℕ} (γ : Space m → ℝ) (z : Ambient m) :
    unshear γ (shear γ z) = z := by
  apply (WithLp.equiv 2 (Space m × ℝ)).injective
  simpa [unshear, shear, add_comm] using Prod.eta z.ofLp

@[simp] theorem shear_unshear {m : ℕ} (γ : Space m → ℝ) (z : Ambient m) :
    shear γ (unshear γ z) = z := by
  apply (WithLp.equiv 2 (Space m × ℝ)).injective
  simpa [unshear, shear, add_comm] using Prod.eta z.ofLp

theorem shear_inverse : Expected.ShearInverse :=
  fun _ γ => ⟨unshear_shear γ, shear_unshear γ⟩

def shearEquiv {m : ℕ} (γ : Space m → ℝ) : Ambient m ≃ Ambient m where
  toFun := shear γ
  invFun := unshear γ
  left_inv := unshear_shear γ
  right_inv := shear_unshear γ

theorem horizontal_lipschitz (m : ℕ) :
    LipschitzWith 1 (fun z : Ambient m => z.ofLp.1) := by
  simpa only [Function.comp_def, one_mul] using LipschitzWith.prod_fst.comp (WithLp.prod_lipschitzWith_ofLp 2 (Space m) ℝ)

theorem vertical_lipschitz (m : ℕ) :
    LipschitzWith 1 (fun z : Ambient m => z.ofLp.2) := by
  simpa only [Function.comp_def, one_mul] using LipschitzWith.prod_snd.comp (WithLp.prod_lipschitzWith_ofLp 2 (Space m) ℝ)

theorem shear_lipschitzOn {m : ℕ} {B : Set (Space m)} {γ : Space m → ℝ}
    {L : ℝ≥0} (hL : LipschitzOnWith L γ B) :
    LipschitzOnWith (shearConstant L) (shear γ) (strip B) := by
  have hfst := (horizontal_lipschitz m).lipschitzOnWith (s := strip B)
  have hsnd := (vertical_lipschitz m).lipschitzOnWith (s := strip B)
  have hγ : LipschitzOnWith L (fun z : Ambient m => γ z.ofLp.1) (strip B) := by
    simpa only [Function.comp_def, mul_one] using hL.comp hfst (fun _ hx => hx)
  have hadd : LipschitzOnWith (L + 1)
      (fun z : Ambient m => γ z.ofLp.1 + z.ofLp.2) (strip B) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      _ ≤ dist (γ x.ofLp.1) (γ y.ofLp.1) + dist x.ofLp.2 y.ofLp.2 :=
        dist_add_add_le _ _ _ _
      _ ≤ (L : ℝ) * dist x y + (1 : ℝ) * dist x y :=
        add_le_add (hγ.dist_le_mul x hx y hy) (hsnd.dist_le_mul x hx y hy)
      _ = _ := by simp [add_mul]
  exact (WithLp.prod_lipschitzWith_toLp 2 (Space m) ℝ).comp_lipschitzOnWith
    (hfst.prodMk hadd)

theorem unshear_eq_shear_neg {m : ℕ} (γ : Space m → ℝ) :
    unshear γ = shear (fun x => -γ x) := by
  funext z
  simp [unshear, shear, sub_eq_add_neg, add_comm]

theorem unshear_lipschitzOn {m : ℕ} {B : Set (Space m)} {γ : Space m → ℝ}
    {L : ℝ≥0} (hL : LipschitzOnWith L γ B) :
    LipschitzOnWith (shearConstant L) (unshear γ) (strip B) := by
  rw [unshear_eq_shear_neg]
  apply shear_lipschitzOn
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa only [dist_neg_neg] using hL.dist_le_mul x hx y hy

theorem shear_lipschitz : Expected.ShearLipschitz :=
  fun _ _ _ _ hL => ⟨shear_lipschitzOn hL, unshear_lipschitzOn hL⟩

def shearHomeomorph {m : ℕ} (γ : Space m → ℝ) (hγ : Continuous γ) :
    Ambient m ≃ₜ Ambient m where
  toEquiv := shearEquiv γ
  continuous_toFun := by
    change Continuous (shear γ)
    unfold shear
    exact (WithLp.homeomorphProd 2 (Space m) ℝ).symm.continuous.comp
      ((WithLp.homeomorphProd 2 (Space m) ℝ).continuous.fst.prodMk
        ((hγ.comp (WithLp.homeomorphProd 2 (Space m) ℝ).continuous.fst).add
          (WithLp.homeomorphProd 2 (Space m) ℝ).continuous.snd))
  continuous_invFun := by
    change Continuous (unshear γ)
    unfold unshear
    exact (WithLp.homeomorphProd 2 (Space m) ℝ).symm.continuous.comp
      ((WithLp.homeomorphProd 2 (Space m) ℝ).continuous.fst.prodMk
        ((WithLp.homeomorphProd 2 (Space m) ℝ).continuous.snd.sub
          (hγ.comp (WithLp.homeomorphProd 2 (Space m) ℝ).continuous.fst)))

/-- Fubini on the vertical translations, transported through the
volume-preserving L²/product identification. -/
theorem shear_measurePreserving {m : ℕ} (γ : Space m → ℝ) (hγ : Measurable γ) :
    MeasurePreserving (shear γ) volume volume := by
  have hprod : MeasurePreserving
      (fun z : Space m × ℝ => (z.1, γ z.1 + z.2)) volume volume := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    apply (MeasurePreserving.id (volume : Measure (Space m))).skew_product (g := fun x t => γ x + t)
    · exact (hγ.comp measurable_fst).add measurable_snd
    · exact Filter.Eventually.of_forall fun x => (measurePreserving_add_left volume (γ x)).map_eq
  exact (WithLp.volume_preserving_toLp (Space m) ℝ).comp
    (hprod.comp (WithLp.volume_preserving_ofLp (Space m) ℝ))

theorem shear_volume_global {m : ℕ} (γ : Space m → ℝ) (hγ : Continuous γ)
    (S : Set (Ambient m)) : volume (shear γ '' S) = volume S := by
  have hmp := shear_measurePreserving γ hγ.measurable
  have h := hmp.measure_preimage_emb (shearHomeomorph γ hγ).measurableEmbedding (shear γ '' S)
  simpa only [Set.preimage_image_eq _ (show Function.Injective (shear γ) from (shearEquiv γ).injective)] using h.symm

theorem shear_volume : Expected.ShearVolume := by
  intro m B γ L hL S hSB
  obtain ⟨g, hg, heq⟩ := hL.extend_real
  have heqS : EqOn (shear γ) (shear g) S := by
    intro z hz
    simp only [shear, heq (hSB hz)]
  have heqU : EqOn (unshear γ) (unshear g) S := by
    intro z hz
    simp only [unshear, heq (hSB hz)]
  constructor
  · rw [Set.EqOn.image_eq heqS]
    exact shear_volume_global g hg.continuous S
  · rw [Set.EqOn.image_eq heqU, unshear_eq_shear_neg]
    exact shear_volume_global (fun x => -g x) hg.continuous.neg S

theorem graph_geometry : Expected.GraphGeometry := by
  intro m B γ L hL
  refine ⟨P102.U4.GraphArea.graph_lipschitzOn hL, ?_, ?_⟩
  · intro x _ y _
    simpa only [graph, WithLp.ofLp_toLp, NNReal.coe_one, one_mul] using
      (horizontal_lipschitz m).dist_le_mul (graph γ x) (graph γ y)
  · intro S hSB
    constructor
    · have h := normalized_lipschitz_image_le
        ((horizontal_lipschitz m).lipschitzOnWith (s := graph γ '' S)) m
      have hp : (fun z : Ambient m => z.ofLp.1) '' (graph γ '' S) = S := by
        simp only [← image_comp, graph, WithLp.ofLp_toLp, Function.comp_def, image_id']
      simpa only [hp, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
        ENNReal.coe_one, one_pow, one_mul] using h
    · simpa only [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, graphConstant] using
        normalized_lipschitz_image_le ((P102.U4.GraphArea.graph_lipschitzOn hL).mono hSB) m

theorem graph_geometry_in_frame : Expected.GraphGeometryInFrame := by
  intro m B γ L hL e
  obtain ⟨hgraph, hdist, harea⟩ := graph_geometry m B γ L hL
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using e.isometry.lipschitzWith.comp_lipschitzOnWith hgraph
  · intro x hx y hy
    simpa only [e.isometry.dist_eq] using hdist x hx y hy
  · intro S hSB
    rw [Set.image_comp, e.isometry.euclideanHausdorffMeasure_image]
    exact harea S hSB

theorem shear_lower_dist {m : ℕ} {B : Set (Space m)} {γ : Space m → ℝ}
    {L : ℝ≥0} (hL : LipschitzOnWith L γ B) {x y : Ambient m}
    (hx : x ∈ strip B) (hy : y ∈ strip B) :
    dist x y ≤ shearConstant L * dist (shear γ x) (shear γ y) := by
  have hx' : shear γ x ∈ strip B := hx
  have hy' : shear γ y ∈ strip B := hy
  simpa only [unshear_shear] using
    (unshear_lipschitzOn hL).dist_le_mul (shear γ x) hx' (shear γ y) hy'

theorem counting_boundary : Expected.CountingBoundary := normalized_zero_eq_count

theorem empty_open : Expected.EmptyOpen := by
  intro m
  refine ⟨isOpen_empty, Bornology.isBounded_empty, ?_⟩
  simp

/-- Extension of the graph function changes neither the original local chart
nor any of its smaller symmetric cylinders. -/
theorem chartImage_eq_of_eqOn {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    {γ δ : Space m → ℝ} {c : Space m} {r a : ℝ}
    (h : EqOn γ δ (ball c r)) : chartImage e γ c r a = chartImage e δ c r a := by
  unfold chartImage
  congr 1
  apply Set.EqOn.image_eq
  intro z hz
  simp only [shear, h hz.1]

theorem cylinder_open {m : ℕ} (c : Space m) (r a : ℝ) : IsOpen (cylinder c r a) :=
  (isOpen_ball.preimage (horizontal_lipschitz m).continuous).inter
    (isOpen_Ioo.preimage (vertical_lipschitz m).continuous)

theorem chartImage_open {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    {γ : Space m → ℝ} {c : Space m} {r a : ℝ} {L : ℝ≥0}
    (hL : LipschitzOnWith L γ (ball c r)) : IsOpen (chartImage e γ c r a) := by
  obtain ⟨g, hg, heq⟩ := hL.extend_real
  rw [chartImage_eq_of_eqOn e heq]
  exact e.toHomeomorph.isOpenMap _ ((shearHomeomorph g hg.continuous).isOpenMap _
    (cylinder_open c r a))

theorem shear_lipschitzWith {m : ℕ} {γ : Space m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L γ) : LipschitzWith (shearConstant L) (shear γ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (shear_lipschitzOn (hL.lipschitzOnWith (s := univ))).dist_le_mul x
    (mem_univ _) y (mem_univ _)

theorem cylinder_bounded {m : ℕ} (c : Space m) (r a : ℝ) :
    Bornology.IsBounded (cylinder c r a) := by
  have h : cylinder c r a = WithLp.toLp 2 '' (ball c r ×ˢ Ioo (-a) a) := by
    ext z
    constructor
    · intro hz
      exact ⟨z.ofLp, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  rw [h]
  exact (WithLp.prod_lipschitzWith_toLp 2 (Space m) ℝ).isBounded_image
    (isBounded_ball.prod (isBounded_Ioo (-a) a))

theorem chartImage_bounded {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    {γ : Space m → ℝ} {c : Space m} {r a : ℝ} {L : ℝ≥0}
    (hL : LipschitzOnWith L γ (ball c r)) :
    Bornology.IsBounded (chartImage e γ c r a) := by
  obtain ⟨g, hg, heq⟩ := hL.extend_real
  rw [chartImage_eq_of_eqOn e heq]
  exact e.isometry.lipschitzWith.isBounded_image
    ((shear_lipschitzWith hg).isBounded_image (cylinder_bounded c r a))

theorem chart_center_mem {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (γ : Space m → ℝ) (c : Space m) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    e (graph γ c) ∈ chartImage e γ c r a := by
  refine ⟨graph γ c, ?_, rfl⟩
  refine ⟨WithLp.toLp 2 (c, (0 : ℝ)), ⟨mem_ball_self hr, ?_⟩, ?_⟩
  · exact ⟨neg_neg_of_pos ha, ha⟩
  · simp only [shear, add_zero, graph]

/-- A finite cover by half-sized, hence strictly smaller, symmetric boundary
cylinders. This is just compactness of the frontier, with no connectedness assumption. -/
theorem finite_boundary_cover {m : ℕ} {Ω : Set (Ambient m)} (hΩ : IsLipschitzOpen Ω) :
    ∃ (n : ℕ) (C : Fin n → BoundaryChart Ω),
      frontier Ω ⊆ ⋃ i, chartImage (C i).frame (C i).graphFunction (C i).center
        ((C i).radius / 2) ((C i).height / 2) := by
  classical
  let J := {p : Ambient m // p ∈ frontier Ω}
  choose C hC using fun p : J => hΩ.2.2 p p.property
  let U (p : J) := chartImage (C p).frame (C p).graphFunction (C p).center
    ((C p).radius / 2) ((C p).height / 2)
  have hU (p : J) : IsOpen (U p) := chartImage_open (C p).frame
    ((C p).graph_lipschitz.mono (ball_subset_ball (by linarith [(C p).radius_pos])))
  have hcov : frontier Ω ⊆ ⋃ p, U p := by
    intro p hp
    refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    have hCp := hC ⟨p, hp⟩
    change _ = p at hCp
    have hmem := chart_center_mem (C ⟨p, hp⟩).frame (C ⟨p, hp⟩).graphFunction
      (C ⟨p, hp⟩).center (half_pos (C ⟨p, hp⟩).radius_pos)
      (half_pos (C ⟨p, hp⟩).height_pos)
    simpa only [hCp] using hmem
  have hcompact : IsCompact (frontier Ω) :=
    hΩ.2.1.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover U hU hcov
  let e := t.equivFin.symm
  refine ⟨t.card, fun i => C (e i), ?_⟩
  intro p hp
  obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp (ht hp)
  refine mem_iUnion.mpr ⟨e.symm ⟨j, hj⟩, ?_⟩
  simpa only [Equiv.apply_symm_apply] using hpj

theorem smaller_chart_compact : Expected.SmallerChartCompact := by
  intro m Ω C r a _hr hr _ha ha
  have hL := C.graph_lipschitz.mono (ball_subset_ball hr.le)
  refine ⟨(chartImage_bounded C.frame hL).isCompact_closure, ?_⟩
  obtain ⟨g, hg, heq⟩ := C.graph_lipschitz.extend_real
  rw [chartImage_eq_of_eqOn C.frame (heq.mono (ball_subset_ball hr.le)),
    chartImage_eq_of_eqOn C.frame heq]
  have hcl : IsClosed {z : Ambient m | z.ofLp.1 ∈ closedBall C.center r ∧
      z.ofLp.2 ∈ Icc (-a) a} :=
    (isClosed_closedBall.preimage (horizontal_lipschitz m).continuous).inter
      (isClosed_Icc.preimage (vertical_lipschitz m).continuous)
  have hc : closure (cylinder C.center r a) ⊆ cylinder C.center C.radius C.height := by
    have hsub : closure (cylinder C.center r a) ⊆
        {z : Ambient m | z.ofLp.1 ∈ closedBall C.center r ∧ z.ofLp.2 ∈ Icc (-a) a} :=
      closure_minimal (fun _ hz => ⟨ball_subset_closedBall hz.1, Ioo_subset_Icc_self hz.2⟩) hcl
    intro z hz
    have hz' := hsub hz
    exact ⟨closedBall_subset_ball hr hz'.1, by constructor <;> linarith [hz'.2.1, hz'.2.2]⟩
  change closure (C.frame.toHomeomorph '' (shearHomeomorph g hg.continuous ''
    cylinder C.center r a)) ⊆ C.frame.toHomeomorph ''
      (shearHomeomorph g hg.continuous '' cylinder C.center C.radius C.height)
  rw [← C.frame.toHomeomorph.image_closure, ← (shearHomeomorph g hg.continuous).image_closure]
  exact image_mono (image_mono hc)

theorem chartImage_mono {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (γ : Space m → ℝ) (c : Space m) {r R a A : ℝ} (hr : r ≤ R) (ha : a ≤ A) :
    chartImage e γ c r a ⊆ chartImage e γ c R A := by
  apply image_mono
  apply image_mono
  intro z hz
  exact ⟨ball_subset_ball hr hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩

/-- The compact boundary in dimension one consists of finitely many isolated
endpoints. The graph in any individual chart has just one base point. -/
theorem finite_frontier_oneDim {Ω : Set (Ambient 0)} (hΩ : IsLipschitzOpen Ω) :
    (frontier Ω).Finite := by
  obtain ⟨n, C, hcov⟩ := finite_boundary_cover hΩ
  apply (Set.finite_range (fun i => (C i).frame (graph (C i).graphFunction (C i).center))).subset
  intro p hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hp)
  have houter := chartImage_mono (C i).frame (C i).graphFunction (C i).center
    (le_of_lt (half_lt_self (C i).radius_pos)) (le_of_lt (half_lt_self (C i).height_pos)) hi
  have hgraph : p ∈ (C i).frame '' (graph (C i).graphFunction '' ball (C i).center (C i).radius) := by
    rw [← (C i).boundary]
    exact ⟨hp, houter⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := hgraph
  have hx0 : x = (C i).center := Subsingleton.elim _ _
  rw [hx0] at he
  exact ⟨i, he⟩

/-- The explicit dimension-one coordinate bridge preserves Euclidean length. -/
def verticalLine : Ambient 0 ≃ₗᵢ[ℝ] ℝ where
  toFun := fun z => z.ofLp.2
  invFun := fun t => WithLp.toLp 2 (0, t)
  left_inv := by
    intro z
    apply (WithLp.equiv 2 (Space 0 × ℝ)).injective
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  norm_map' := by
    intro z
    have hz : WithLp.fst z = 0 := Subsingleton.elim _ _
    simp [WithLp.prod_norm_eq_of_L2, hz, Real.sqrt_sq_eq_abs]

/-- Smooth compactly supported localization of a finite bounded open covering.
The partition is one on an open neighborhood of K, not merely on K itself. -/
theorem finite_smooth_partition {m k : ℕ} {K : Set (Ambient m)} (hK : IsCompact K)
    (U : Fin k → Set (Ambient m)) (hU : ∀ i, IsOpen (U i))
    (hUb : ∀ i, Bornology.IsBounded (U i)) (hcov : K ⊆ ⋃ i, U i) :
    ∃ (V : Set (Ambient m)) (χ : Fin k → Ambient m → ℝ),
      IsOpen V ∧ K ⊆ V ∧
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧ ∀ x, 0 ≤ χ i x) ∧
      (∀ x ∈ V, ∑ i, χ i x = 1) ∧ ∀ i, tsupport (χ i) ⊆ U i := by
  classical
  obtain ⟨V, hVo, hKV, hVU⟩ := hK.exists_isOpen_closure_subset
    ((isOpen_iUnion hU).mem_nhdsSet.mpr hcov)
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, Ambient m)) isClosed_closure U hU hVU
  refine ⟨V, fun i => f i, hVo, hKV, ?_, ?_, hf⟩
  · intro i
    refine ⟨(f i).contMDiff.contDiff, ?_, f.nonneg i⟩
    exact isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _, (hUb i).subset (hf i)⟩
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using f.sum_eq_one (subset_closure hx)

theorem finite_localization : Expected.FiniteLocalization := by
  intro m Ω hΩ
  obtain ⟨n, C, hC⟩ := finite_boundary_cover hΩ
  let U : Fin (n + 1) → Set (Ambient m) := Fin.cases Ω fun i =>
    chartImage (C i).frame (C i).graphFunction (C i).center
      ((C i).radius / 2) ((C i).height / 2)
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    refine Fin.cases hΩ.1 (fun j => ?_) i
    exact chartImage_open (C j).frame ((C j).graph_lipschitz.mono
      (ball_subset_ball (by linarith [(C j).radius_pos])))
  have hUb : ∀ i, Bornology.IsBounded (U i) := by
    intro i
    refine Fin.cases hΩ.2.1 (fun j => ?_) i
    exact chartImage_bounded (C j).frame ((C j).graph_lipschitz.mono
      (ball_subset_ball (by linarith [(C j).radius_pos])))
  have hcover : closure Ω ⊆ ⋃ i, U i := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · exact mem_iUnion.mpr ⟨0, hxΩ⟩
    · have hxf : x ∈ frontier Ω := by
        rw [hΩ.1.frontier_eq]
        exact ⟨hx, hxΩ⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hC hxf)
      exact mem_iUnion.mpr ⟨i.succ, hi⟩
  obtain ⟨V, χ, hVo, hΩV, hχ, hsum, hsupp⟩ := finite_smooth_partition
    hΩ.2.1.isCompact_closure U hU hUb hcover
  refine ⟨n, C, (fun i => (C i).radius / 2), (fun i => (C i).height / 2), ?_, hC,
    V, χ, hVo, hΩV, hχ, hsum, hsupp 0, ?_, fun i => hsupp i.succ⟩
  · intro i
    exact ⟨half_pos (C i).radius_pos, half_lt_self (C i).radius_pos,
      half_pos (C i).height_pos, half_lt_self (C i).height_pos⟩
  · obtain ⟨ε, hε, hεΩ⟩ := (hχ 0).2.1.exists_cthickening_subset_open hΩ.1 (hsupp 0)
    refine ⟨ε, hε, ?_⟩
    intro x hx y hy
    by_contra! hdist
    have hyΩ : y ∈ Ω := hεΩ (mem_cthickening_of_dist_le y x ε _ hx
      (by simpa only [dist_comm] using hdist.le))
    exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hΩ.1)) hy hyΩ

theorem real_affine_isometry_classification (e : ℝ ≃ᵃⁱ[ℝ] ℝ) :
    (∀ x, e x = e 0 + x) ∨ (∀ x, e x = e 0 - x) := by
  have hnorm : |e.linearIsometryEquiv 1| = 1 := by
    simpa only [Real.norm_eq_abs, abs_one] using e.linearIsometryEquiv.norm_map (1 : ℝ)
  have hmul (x : ℝ) : e.linearIsometryEquiv x = x * e.linearIsometryEquiv 1 := by
    simpa only [smul_eq_mul, mul_one] using e.linearIsometryEquiv.map_smul x (1 : ℝ)
  have hadd (x : ℝ) : e x = e.linearIsometryEquiv x + e 0 := by
    simpa only [vadd_eq_add, add_zero] using e.map_vadd (0 : ℝ) x
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hnorm with hp | hn
  · left
    intro x
    rw [hadd, hmul, hp, mul_one, add_comm]
  · right
    intro x
    rw [hadd, hmul, hn]
    ring

theorem real_isometry_intervals (e : ℝ ≃ᵃⁱ[ℝ] ℝ) (g a : ℝ) :
    e '' Ioo (g - a) (g + a) = Ioo (e g - a) (e g + a) ∧
      (e '' Ioo g (g + a) = Ioo (e g) (e g + a) ∨
       e '' Ioo g (g + a) = Ioo (e g - a) (e g)) := by
  rcases real_affine_isometry_classification e with h | h
  · constructor
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [mem_Ioo] at hx ⊢
        rw [h x, h g]
        constructor <;> linarith [hx.1, hx.2]
      · intro hy
        refine ⟨y - e 0, ?_, ?_⟩
        · simp only [mem_Ioo] at hy ⊢
          rw [h g] at hy
          constructor <;> linarith [hy.1, hy.2]
        · rw [h]
          ring
    · left
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [mem_Ioo] at hx ⊢
        rw [h x, h g]
        constructor <;> linarith [hx.1, hx.2]
      · intro hy
        refine ⟨y - e 0, ?_, ?_⟩
        · simp only [mem_Ioo] at hy ⊢
          rw [h g] at hy
          constructor <;> linarith [hy.1, hy.2]
        · rw [h]
          ring
  · constructor
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [mem_Ioo] at hx ⊢
        rw [h x, h g]
        constructor <;> linarith [hx.1, hx.2]
      · intro hy
        refine ⟨e 0 - y, ?_, ?_⟩
        · simp only [mem_Ioo] at hy ⊢
          rw [h g] at hy
          constructor <;> linarith [hy.1, hy.2]
        · rw [h]
          ring
    · right
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [mem_Ioo] at hx ⊢
        rw [h x, h g]
        constructor <;> linarith [hx.1, hx.2]
      · intro hy
        refine ⟨e 0 - y, ?_, ?_⟩
        · simp only [mem_Ioo] at hy ⊢
          rw [h g] at hy
          constructor <;> linarith [hy.1, hy.2]
        · rw [h]
          ring

def realFrame (e : Ambient 0 ≃ᵃⁱ[ℝ] Ambient 0) : ℝ ≃ᵃⁱ[ℝ] ℝ :=
  (verticalLine.symm.toAffineIsometryEquiv.trans e).trans verticalLine.toAffineIsometryEquiv

@[simp] theorem verticalLine_symm_apply (t : ℝ) :
    verticalLine.symm t = WithLp.toLp 2 (0, t) := rfl

@[simp] theorem verticalLine_graph (γ : Space 0 → ℝ) (c : Space 0) :
    verticalLine (graph γ c) = γ c := rfl

theorem shear_cylinder_oneDim (γ : Space 0 → ℝ) (c : Space 0) {r : ℝ}
    (hr : 0 < r) (a : ℝ) :
    shear γ '' cylinder c r a = verticalLine.symm '' Ioo (γ c - a) (γ c + a) := by
  ext z
  constructor
  · rintro ⟨w, ⟨hw, ht⟩, rfl⟩
    have hc : w.ofLp.1 = c := Subsingleton.elim _ _
    refine ⟨γ c + w.ofLp.2, ?_, ?_⟩
    · change -a < w.ofLp.2 ∧ w.ofLp.2 < a at ht
      constructor <;> linarith
    · simp only [verticalLine_symm_apply, shear, hc]
      congr 2
      exact Subsingleton.elim _ _
  · rintro ⟨t, ht, rfl⟩
    refine ⟨WithLp.toLp 2 (c, t - γ c), ?_, ?_⟩
    · refine ⟨mem_ball_self hr, ?_⟩
      change -a < t - γ c ∧ t - γ c < a
      constructor <;> linarith [ht.1, ht.2]
    · simp [shear]
      exact Subsingleton.elim _ _

theorem shear_upperCylinder_oneDim (γ : Space 0 → ℝ) (c : Space 0) {r : ℝ}
    (hr : 0 < r) (a : ℝ) :
    shear γ '' upperCylinder c r a = verticalLine.symm '' Ioo (γ c) (γ c + a) := by
  ext z
  constructor
  · rintro ⟨w, ⟨hw, ht⟩, rfl⟩
    have hc : w.ofLp.1 = c := Subsingleton.elim _ _
    refine ⟨γ c + w.ofLp.2, ?_, ?_⟩
    · change 0 < w.ofLp.2 ∧ w.ofLp.2 < a at ht
      constructor <;> linarith
    · simp only [verticalLine_symm_apply, shear, hc]
      congr 2
      exact Subsingleton.elim _ _
  · rintro ⟨t, ht, rfl⟩
    refine ⟨WithLp.toLp 2 (c, t - γ c), ?_, ?_⟩
    · refine ⟨mem_ball_self hr, ?_⟩
      change 0 < t - γ c ∧ t - γ c < a
      constructor <;> linarith [ht.1, ht.2]
    · simp [shear]
      exact Subsingleton.elim _ _

theorem chartImage_verticalLine {Ω : Set (Ambient 0)} (C : BoundaryChart Ω) :
    verticalLine '' chartImage C.frame C.graphFunction C.center C.radius C.height =
      realFrame C.frame '' Ioo (C.graphFunction C.center - C.height)
        (C.graphFunction C.center + C.height) := by
  rw [chartImage, shear_cylinder_oneDim _ _ C.radius_pos]
  simp only [← image_comp]
  rfl

theorem upperChart_verticalLine {Ω : Set (Ambient 0)} (C : BoundaryChart Ω) :
    verticalLine '' (C.frame '' (shear C.graphFunction ''
      upperCylinder C.center C.radius C.height)) =
      realFrame C.frame '' Ioo (C.graphFunction C.center)
        (C.graphFunction C.center + C.height) := by
  rw [shear_upperCylinder_oneDim _ _ C.radius_pos]
  simp only [← image_comp]
  rfl

@[simp] theorem realFrame_graph {Ω : Set (Ambient 0)} (C : BoundaryChart Ω) :
    realFrame C.frame (C.graphFunction C.center) =
      verticalLine (C.frame (graph C.graphFunction C.center)) := by
  change verticalLine (C.frame (WithLp.toLp 2 (0, C.graphFunction C.center))) = _
  have hc : (0 : Space 0) = C.center := Subsingleton.elim _ _
  simp only [graph, hc]

theorem oneDim_real_local {Ω : Set (Ambient 0)} (hΩ : IsLipschitzOpen Ω) :
    ∀ p ∈ frontier (verticalLine '' Ω), ∃ ε : ℝ, 0 < ε ∧
      ((verticalLine '' Ω) ∩ Ioo (p - ε) (p + ε) = Ioo p (p + ε) ∨
       (verticalLine '' Ω) ∩ Ioo (p - ε) (p + ε) = Ioo (p - ε) p) := by
  intro p hp
  change p ∈ frontier (verticalLine.toHomeomorph '' Ω) at hp
  rw [← verticalLine.toHomeomorph.image_frontier] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨C, hC⟩ := hΩ.2.2 q hq
  obtain ⟨hfull, hupper⟩ := real_isometry_intervals (realFrame C.frame)
    (C.graphFunction C.center) C.height
  rw [realFrame_graph, hC] at hfull hupper
  have hside := congrArg (fun S => verticalLine '' S) C.side
  rw [image_inter verticalLine.injective, chartImage_verticalLine,
    upperChart_verticalLine, hfull] at hside
  refine ⟨C.height, C.height_pos, ?_⟩
  rcases hupper with h | h
  · exact Or.inl (hside.trans h)
  · exact Or.inr (hside.trans h)

theorem oneDim_coordinate_transfer {Ω : Set (Ambient 0)} {n : ℕ} {a b : Fin n → ℝ}
    (hO : verticalLine '' Ω = ⋃ i, Ioo (a i) (b i))
    (hF : frontier (verticalLine '' Ω) = ⋃ i, {a i, b i}) :
    Ω = ⋃ i, {z | z.ofLp.2 ∈ Ioo (a i) (b i)} ∧
      frontier Ω = ⋃ i, {WithLp.toLp 2 (0, a i), WithLp.toLp 2 (0, b i)} := by
  constructor
  · ext z
    have hz : z ∈ Ω ↔ verticalLine z ∈ verticalLine '' Ω :=
      (verticalLine.injective.mem_set_image).symm
    rw [hz, hO]
    simp only [mem_iUnion, mem_ofPred_eq]
    rfl
  · change frontier (verticalLine.toHomeomorph '' Ω) = _ at hF
    rw [← verticalLine.toHomeomorph.image_frontier] at hF
    change verticalLine '' frontier Ω = _ at hF
    apply (Set.image_injective.mpr verticalLine.injective)
    rw [hF, image_iUnion]
    congr 1
    funext i
    simp only [image_insert_eq, image_singleton]
    rfl

namespace RealDecomposition

lemma open_connected_eq_Ioo {C : Set ℝ} (hCo : IsOpen C) (hCc : IsConnected C)
    (hCb : Bornology.IsBounded C) : C = Ioo (sInf C) (sSup C) := by
  have hlo := hCb.bddBelow
  have hhi := hCb.bddAbove
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a,b,hxab,habC⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hCo.mem_nhds hx)
    obtain ⟨y,hay,hyx⟩ := exists_between hxab.1
    obtain ⟨z,hxz,hzb⟩ := exists_between hxab.2
    exact ⟨(csInf_le hlo (habC ⟨hay,hyx.trans hxab.2⟩)).trans_lt hyx,
      hxz.trans_le (le_csSup hhi (habC ⟨hxab.1.trans hxz,hzb⟩))⟩
  · exact hCc.Ioo_csInf_csSup_subset hlo hhi

lemma exists_interval_component {O : Set ℝ} (hO : IsOpen O)
    (hb : Bornology.IsBounded O) {x : ℝ} (hx : x ∈ O) :
    ∃ a b : ℝ, a < x ∧ x < b ∧ a ∈ frontier O ∧ b ∈ frontier O ∧ Ioo a b ⊆ O := by
  let C := connectedComponentIn O x
  have hsub : C ⊆ O := connectedComponentIn_subset O x
  have hxo : x ∈ C := mem_connectedComponentIn hx
  have hCo : IsOpen C := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨u,v,hyuv,huvO⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hO.mem_nhds (hsub hy))
    have hsmall : Ioo u v ⊆ C := by
      have hsmall' := isPreconnected_Ioo.subset_connectedComponentIn hyuv huvO
      rwa [← connectedComponentIn_eq hy] at hsmall'
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hyuv) hsmall
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx
  have hCb := hb.subset hsub
  have hC : C = Ioo (sInf C) (sSup C) := open_connected_eq_Ioo hCo hCc hCb
  have hxi := hC ▸ hxo
  refine ⟨sInf C, sSup C, hxi.1, hxi.2, ?_, ?_, hC ▸ hsub⟩
  · have ha : sInf C ∈ closure C := csInf_mem_closure hCc.nonempty hCb.bddBelow
    have haO : sInf C ∉ O := by
      intro h
      have haC : sInf C ∈ C := by
        have hu : IsPreconnected (insert (sInf C) C) :=
          hCc.isPreconnected.subset_closure (subset_insert _ _) (insert_subset_iff.mpr ⟨ha, subset_closure⟩)
        exact hu.subset_connectedComponentIn (by simp [hxo]) (by simpa using (insert_subset_iff.mpr ⟨h,hsub⟩)) (by simp)
      have : sInf C < sInf C := ((congrArg (fun S : Set ℝ => sInf C ∈ S) hC).mp haC).1
      exact this.false
    rw [hO.frontier_eq]
    exact ⟨closure_mono hsub ha,haO⟩
  · have hb' : sSup C ∈ closure C := csSup_mem_closure hCc.nonempty hCb.bddAbove
    have hbO : sSup C ∉ O := by
      intro h
      have hbC : sSup C ∈ C := by
        have hu : IsPreconnected (insert (sSup C) C) :=
          hCc.isPreconnected.subset_closure (subset_insert _ _) (insert_subset_iff.mpr ⟨hb', subset_closure⟩)
        exact hu.subset_connectedComponentIn (by simp [hxo]) (by simpa using (insert_subset_iff.mpr ⟨h,hsub⟩)) (by simp)
      have : sSup C < sSup C := ((congrArg (fun S : Set ℝ => sSup C ∈ S) hC).mp hbC).2
      exact this.false
    rw [hO.frontier_eq]
    exact ⟨closure_mono hsub hb',hbO⟩

end RealDecomposition

namespace RealDecomposition

lemma interval_eq_of_overlap {O : Set ℝ} (hO : IsOpen O) {a b c d x : ℝ}
    (ha : a ∈ frontier O) (hb : b ∈ frontier O)
    (hc : c ∈ frontier O) (hd : d ∈ frontier O)
    (h1 : Ioo a b ⊆ O) (h2 : Ioo c d ⊆ O)
    (hx1 : x ∈ Ioo a b) (hx2 : x ∈ Ioo c d) : a = c ∧ b = d := by
  have hout : ∀ y ∈ frontier O, y ∉ O := by
    intro y hy
    exact (hO.frontier_eq ▸ hy).2
  constructor
  · rcases lt_trichotomy a c with h | h | h
    · exact False.elim (hout c hc (h1 ⟨h,hx2.1.trans hx1.2⟩))
    · exact h
    · exact False.elim (hout a ha (h2 ⟨h,hx1.1.trans hx2.2⟩))
  · rcases lt_trichotomy b d with h | h | h
    · exact False.elim (hout b hb (h2 ⟨hx2.1.trans hx1.2,h⟩))
    · exact h
    · exact False.elim (hout d hd (h1 ⟨hx1.1.trans hx2.2,h⟩))

lemma interval_endpoints_ne {O : Set ℝ}
    (hloc : ∀ p ∈ frontier O, ∃ ε : ℝ, 0 < ε ∧
      (O ∩ Ioo (p-ε) (p+ε) = Ioo p (p+ε) ∨
       O ∩ Ioo (p-ε) (p+ε) = Ioo (p-ε) p))
    {a b c : ℝ} (hab : a < b) (hbc : b < c) (hb : b ∈ frontier O)
    (h1 : Ioo a b ⊆ O) (h2 : Ioo b c ⊆ O) : False := by
  obtain ⟨ε,hε,hlocal⟩ := hloc b hb
  rcases hlocal with hr | hl
  · have hm : max a (b-ε) < b := max_lt hab (sub_lt_self _ hε)
    obtain ⟨y,hy,hyb⟩ := exists_between hm
    have hyO : y ∈ O ∩ Ioo (b-ε) (b+ε) :=
      ⟨h1 ⟨(le_max_left _ _).trans_lt hy,hyb⟩,
       (le_max_right _ _).trans_lt hy,hyb.trans (lt_add_of_pos_right _ hε)⟩
    have : b < y := (hr ▸ hyO).1
    exact (this.trans hyb).false
  · have hm : b < min c (b+ε) := lt_min hbc (lt_add_of_pos_right _ hε)
    obtain ⟨y,hby,hy⟩ := exists_between hm
    have hyO : y ∈ O ∩ Ioo (b-ε) (b+ε) :=
      ⟨h2 ⟨hby,hy.trans_le (min_le_left _ _)⟩,
       (sub_lt_self _ hε).trans hby,hy.trans_le (min_le_right _ _)⟩
    have : y < b := (hl ▸ hyO).2
    exact (hby.trans this).false

lemma finite_interval_decomposition {O : Set ℝ} (hO : IsOpen O)
    (hb : Bornology.IsBounded O) (hf : (frontier O).Finite)
    (hloc : ∀ p ∈ frontier O, ∃ ε : ℝ, 0 < ε ∧
      (O ∩ Ioo (p-ε) (p+ε) = Ioo p (p+ε) ∨
       O ∩ Ioo (p-ε) (p+ε) = Ioo (p-ε) p)) :
    ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i < b i) ∧ Function.Injective (Sum.elim a b) ∧
      Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
      O = ⋃ i, Ioo (a i) (b i) ∧ frontier O = ⋃ i, {a i,b i} := by
  classical
  let Jset : Set (ℝ × ℝ) := {p | p.1 ∈ frontier O ∧ p.2 ∈ frontier O ∧
    p.1 < p.2 ∧ Ioo p.1 p.2 ⊆ O}
  have hJfin : Jset.Finite := (hf.prod hf).subset (fun _ hp => ⟨hp.1,hp.2.1⟩)
  let J := Jset
  let : Fintype J := hJfin.fintype
  let n := Fintype.card J
  let e : Fin n ≃ J := (Fintype.equivFin J).symm
  let a : Fin n → ℝ := fun i => (e i).val.1
  let b : Fin n → ℝ := fun i => (e i).val.2
  have ha (i : Fin n) : a i ∈ frontier O := (e i).property.1
  have hb' (i : Fin n) : b i ∈ frontier O := (e i).property.2.1
  have hab (i : Fin n) : a i < b i := (e i).property.2.2.1
  have hsub (i : Fin n) : Ioo (a i) (b i) ⊆ O := (e i).property.2.2.2
  have heq (i j : Fin n) {x : ℝ} (hxi : x ∈ Ioo (a i) (b i))
      (hxj : x ∈ Ioo (a j) (b j)) : i = j := by
    obtain ⟨h1,h2⟩ := interval_eq_of_overlap hO (ha i) (hb' i) (ha j) (hb' j)
      (hsub i) (hsub j) hxi hxj
    apply e.injective
    exact Subtype.ext (Prod.ext h1 h2)
  have hleft : Function.Injective a := by
    intro i j hij
    have hmin : a i < min (b i) (b j) := lt_min (hab i) (by rw [hij]; exact hab j)
    obtain ⟨x,hx1,hx2⟩ := exists_between hmin
    exact heq i j ⟨hx1,hx2.trans_le (min_le_left _ _)⟩
      ⟨by simpa [← hij] using hx1,hx2.trans_le (min_le_right _ _)⟩
  have hright : Function.Injective b := by
    intro i j hij
    have hmax : max (a i) (a j) < b i := max_lt (hab i) (by rw [hij]; exact hab j)
    obtain ⟨x,hx1,hx2⟩ := exists_between hmax
    exact heq i j ⟨(le_max_left _ _).trans_lt hx1,hx2⟩
      ⟨(le_max_right _ _).trans_lt hx1,by simpa [← hij] using hx2⟩
  have hcross (i j : Fin n) : a i ≠ b j := by
    intro h
    exact interval_endpoints_ne hloc (hab j) (by rw [← h]; exact hab i) (hb' j)
      (hsub j) (by simpa only [h] using hsub i)
  have hcover : O = ⋃ i, Ioo (a i) (b i) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨u,v,hux,hxv,hu,hv,huv⟩ := exists_interval_component hO hb hx
      let j : J := ⟨(u,v),hu,hv,hux.trans hxv,huv⟩
      refine mem_iUnion.mpr ⟨e.symm j, ?_⟩
      simpa only [a,b,e.apply_symm_apply] using (show x ∈ Ioo u v from ⟨hux,hxv⟩)
    · exact iUnion_subset hsub
  refine ⟨n,a,b,hab,?_,?_,hcover,?_⟩
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hleft hij)
      | inr j => exact False.elim (hcross i j hij)
    | inr i =>
      cases j with
      | inl j => exact False.elim (hcross j i hij.symm)
      | inr j => exact congrArg Sum.inr (hright hij)
  · intro i j hij
    exact Set.disjoint_left.mpr (fun x hxi hxj => hij (heq i j hxi hxj))
  · apply Set.Subset.antisymm
    · rw [hcover]
      apply (show frontier (⋃ i, Ioo (a i) (b i)) ⊆ ⋃ i, frontier (Ioo (a i) (b i)) by
        simpa using (Set.finite_univ.frontier_biUnion_subset (fun i => Ioo (a i) (b i)))).trans
      apply iUnion_mono
      intro i
      rw [frontier_Ioo (hab i)]
    · apply iUnion_subset
      intro i x hx
      simp only [mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha i
      · exact hb' i

end RealDecomposition

theorem one_dimension_forward {Ω : Set (Ambient 0)} (hΩ : IsLipschitzOpen Ω) :
    ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i < b i) ∧ Function.Injective (Sum.elim a b) ∧
      Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
      Ω = ⋃ i, {z | z.ofLp.2 ∈ Ioo (a i) (b i)} ∧
      frontier Ω = ⋃ i, {WithLp.toLp 2 (0, a i), WithLp.toLp 2 (0, b i)} := by
  have ho : IsOpen (verticalLine '' Ω) := verticalLine.toHomeomorph.isOpenMap Ω hΩ.1
  have hb : Bornology.IsBounded (verticalLine '' Ω) :=
    verticalLine.isometry.lipschitzWith.isBounded_image hΩ.2.1
  have hf : (frontier (verticalLine '' Ω)).Finite := by
    have h := (finite_frontier_oneDim hΩ).image verticalLine
    change (verticalLine.toHomeomorph '' frontier Ω).Finite at h
    rw [verticalLine.toHomeomorph.image_frontier] at h
    exact h
  obtain ⟨n, a, b, hab, hinj, hdis, hO, hF⟩ :=
    RealDecomposition.finite_interval_decomposition ho hb hf (oneDim_real_local hΩ)
  obtain ⟨hΩeq, hfront⟩ := oneDim_coordinate_transfer hO hF
  exact ⟨n, a, b, hab, hinj, hdis, hΩeq, hfront⟩

theorem interval_union_open (n : ℕ) (a b : Fin n → ℝ) :
    IsOpen (⋃ i : Fin n, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}) := by
  apply isOpen_iUnion
  intro i
  exact isOpen_Ioo.preimage verticalLine.continuous

theorem interval_union_bounded (n : ℕ) (a b : Fin n → ℝ) :
    Bornology.IsBounded (⋃ i : Fin n, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}) := by
  apply Bornology.isBounded_iUnion.mpr
  intro i
  exact verticalLine.isometry.antilipschitzWith.isBounded_preimage
    (isBounded_Ioo (a i) (b i))

namespace RealDecomposition

lemma finite_interval_union_frontier {n : ℕ} (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i)
    (hdisj : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) :
    frontier (⋃ i, Ioo (a i) (b i)) = ⋃ i, {a i,b i} := by
  classical
  let O := ⋃ i, Ioo (a i) (b i)
  have hO : IsOpen O := isOpen_iUnion (fun _ => isOpen_Ioo)
  have haout (i : Fin n) : a i ∉ O := by
    intro hi
    obtain ⟨j,hj⟩ := mem_iUnion.mp hi
    by_cases hij : i = j
    · subst j
      exact (lt_irrefl _ hj.1)
    · have hm : a i < min (b i) (b j) := lt_min (hab i) hj.2
      obtain ⟨x,hx1,hx2⟩ := exists_between hm
      exact Set.disjoint_left.mp (hdisj hij)
        ⟨hx1,hx2.trans_le (min_le_left _ _)⟩
        ⟨hj.1.trans hx1,hx2.trans_le (min_le_right _ _)⟩
  have hbout (i : Fin n) : b i ∉ O := by
    intro hi
    obtain ⟨j,hj⟩ := mem_iUnion.mp hi
    by_cases hij : i = j
    · subst j
      exact (lt_irrefl _ hj.2)
    · have hm : max (a i) (a j) < b i := max_lt (hab i) hj.1
      obtain ⟨x,hx1,hx2⟩ := exists_between hm
      exact Set.disjoint_left.mp (hdisj hij)
        ⟨(le_max_left _ _).trans_lt hx1,hx2⟩
        ⟨(le_max_right _ _).trans_lt hx1,hx2.trans hj.2⟩
  apply Set.Subset.antisymm
  · apply (show frontier (⋃ i, Ioo (a i) (b i)) ⊆ ⋃ i, frontier (Ioo (a i) (b i)) by
      simpa using (Set.finite_univ.frontier_biUnion_subset (fun i => Ioo (a i) (b i)))).trans
    apply iUnion_mono
    intro i
    rw [frontier_Ioo (hab i)]
  · intro p hp
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    have hsub : Ioo (a i) (b i) ⊆ O := subset_iUnion (fun i => Ioo (a i) (b i)) i
    rw [hO.frontier_eq]
    simp only [mem_insert_iff,mem_singleton_iff] at hi
    rcases hi with rfl | rfl
    · refine ⟨closure_mono hsub ?_,haout i⟩
      rw [closure_Ioo (hab i).ne]
      exact ⟨le_rfl,(hab i).le⟩
    · refine ⟨closure_mono hsub ?_,hbout i⟩
      rw [closure_Ioo (hab i).ne]
      exact ⟨(hab i).le,le_rfl⟩

end RealDecomposition

private theorem shear_zero_1d (z : Ambient 0) : shear (fun _ => (0 : ℝ)) z = z := by
  apply (WithLp.equiv 2 (Space 0 × ℝ)).injective
  simpa [shear] using Prod.eta z.ofLp

private theorem cylinder_zero_1d (h : ℝ) :
    cylinder (0 : Space 0) 1 h = {z | z.ofLp.2 ∈ Ioo (-h) h} := by
  ext z
  have hz : WithLp.fst z = (0 : Space 0) := Subsingleton.elim _ _
  simp [cylinder, hz]

private theorem upperCylinder_zero_1d (h : ℝ) :
    upperCylinder (0 : Space 0) 1 h = {z | z.ofLp.2 ∈ Ioo 0 h} := by
  ext z
  have hz : WithLp.fst z = (0 : Space 0) := Subsingleton.elim _ _
  simp [upperCylinder, hz]

private theorem graph_zero_1d :
    graph (fun _ : Space 0 => (0 : ℝ)) '' ball (0 : Space 0) 1 = {0} := by
  ext z
  simp only [mem_image, mem_ball, mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : x = (0 : Space 0) := Subsingleton.elim _ _
    simp [graph, hx0]
  · intro hz
    subst z
    refine ⟨0, by simp, ?_⟩
    simp [graph]

private theorem mem_frame_image (e : Ambient 0 ≃ᵃⁱ[ℝ] Ambient 0)
    (S : Set (Ambient 0)) (z : Ambient 0) : z ∈ e '' S ↔ e.symm z ∈ S := by
  exact Set.mem_image_equiv

private def boundaryChartOfLocalSide {Ω : Set (Ambient 0)}
    (e : Ambient 0 ≃ᵃⁱ[ℝ] Ambient 0) (h : ℝ) (hh : 0 < h)
    (hside : ∀ z, (e.symm z).ofLp.2 ∈ Ioo (-h) h →
      (z ∈ Ω ↔ 0 < (e.symm z).ofLp.2))
    (hbd : ∀ z, (e.symm z).ofLp.2 ∈ Ioo (-h) h →
      (z ∈ frontier Ω ↔ (e.symm z).ofLp.2 = 0)) : BoundaryChart Ω where
  frame := e
  center := 0
  radius := 1
  height := h
  radius_pos := zero_lt_one
  height_pos := hh
  graphFunction := fun _ => 0
  constant := 0
  graph_lipschitz := (LipschitzWith.const 0).lipschitzOnWith
  side := by
    simp only [chartImage, shear_zero_1d, image_id', cylinder_zero_1d,
      upperCylinder_zero_1d]
    ext z
    simp only [mem_inter_iff, mem_frame_image, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨hz, hzh⟩
      exact ⟨(hside z hzh).mp hz, hzh.2⟩
    · intro hz
      have hz' : -h < (e.symm z).ofLp.2 ∧ (e.symm z).ofLp.2 < h := by
        constructor <;> linarith [hz.1, hz.2]
      exact ⟨(hside z hz').mpr hz.1, hz'⟩
  boundary := by
    simp only [chartImage, shear_zero_1d, image_id', cylinder_zero_1d, graph_zero_1d]
    ext z
    simp only [mem_inter_iff, mem_frame_image, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzh⟩
      have hzero := (hbd z hzh).mp hz
      apply (WithLp.equiv 2 (Space 0 × ℝ)).injective
      exact Prod.ext (Subsingleton.elim _ _) hzero
    · intro hz
      have hzh : (e.symm z).ofLp.2 ∈ Ioo (-h) h := by simp [hz, hh]
      exact ⟨(hbd z hzh).mpr (by simp [hz]), hzh⟩

private theorem separated_intervals {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (i j : Fin n) (hij : i ≠ j) : b j < a i ∨ b i < a j := by
  have h := Ioo_disjoint_Ioo.mp (hdis hij)
  have hle : b j ≤ a i ∨ b i ≤ a j := by
    rcases min_le_iff.mp h with h | h
    · rcases le_max_iff.mp h with h | h
      · exact False.elim ((not_le_of_gt (hab i)) h)
      · exact Or.inr h
    · rcases le_max_iff.mp h with h | h
      · exact Or.inl h
      · exact False.elim ((not_le_of_gt (hab j)) h)
  rcases hle with h | h
  · left
    refine lt_of_le_of_ne h ?_
    intro he
    have hs : (Sum.inr j : Fin n ⊕ Fin n) = Sum.inl i := hinj he
    cases hs
  · right
    refine lt_of_le_of_ne h ?_
    intro he
    have hs : (Sum.inr i : Fin n ⊕ Fin n) = Sum.inl j := hinj he
    cases hs

private theorem isolate_interval_endpoint {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (i : Fin n) (p : ℝ) (hp : p = a i ∨ p = b i) :
    ∃ h : ℝ, 0 < h ∧ h < b i - a i ∧
      ∀ t : ℝ, dist t p < h → ∀ j, t ∈ Icc (a j) (b j) → j = i := by
  let K : Set ℝ := ⋃ j : Fin n, if j = i then ∅ else Icc (a j) (b j)
  have hK : IsClosed K := isClosed_iUnion_of_finite fun j => by
    split_ifs
    · exact isClosed_empty
    · exact isClosed_Icc
  have hpK : p ∉ K := by
    simp only [K, mem_iUnion]
    rintro ⟨j, hj⟩
    by_cases hji : j = i
    · simp [hji] at hj
    · have hs := separated_intervals hab hinj hdis i j (Ne.symm hji)
      simp only [ite_eq_right hji, mem_Icc] at hj
      rcases hp with rfl | rfl <;> rcases hs with hs | hs <;> linarith [hab i]
  obtain ⟨ε, hε, hpε⟩ := Metric.isOpen_iff.mp hK.isOpen_compl p hpK
  refine ⟨min ε ((b i - a i) / 2), lt_min hε (by linarith [hab i]), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith [hab i])
  · intro t ht j hj
    by_contra hji
    have htK := hpε (show t ∈ ball p ε from lt_of_lt_of_le ht (min_le_left _ _))
    apply htK
    exact mem_iUnion.mpr ⟨j, by simp only [ite_eq_right hji]; exact hj⟩

private def translateFrame (p : ℝ) : Ambient 0 ≃ᵃⁱ[ℝ] Ambient 0 :=
  AffineIsometryEquiv.constVAdd ℝ (Ambient 0) (verticalLine.symm p)

private theorem translateFrame_symm_coord (p : ℝ) (z : Ambient 0) :
    ((translateFrame p).symm z).ofLp.2 = z.ofLp.2 - p := by
  change (-verticalLine.symm p + z).ofLp.2 = _
  change -p + z.ofLp.2 = _
  ring

private theorem translateFrame_zero (p : ℝ) : translateFrame p 0 = verticalLine.symm p := by
  change verticalLine.symm p + 0 = _
  exact add_zero _

private def reverseFrame (p : ℝ) : Ambient 0 ≃ᵃⁱ[ℝ] Ambient 0 :=
  (LinearIsometryEquiv.neg ℝ).toAffineIsometryEquiv.trans (translateFrame p)

private theorem reverseFrame_symm_coord (p : ℝ) (z : Ambient 0) :
    ((reverseFrame p).symm z).ofLp.2 = p - z.ofLp.2 := by
  change (-((translateFrame p).symm z)).ofLp.2 = _
  change -(((translateFrame p).symm z).ofLp.2) = _
  rw [translateFrame_symm_coord]
  ring

private theorem reverseFrame_zero (p : ℝ) : reverseFrame p 0 = verticalLine.symm p := by
  change translateFrame p (-0) = _
  simp only [neg_zero, translateFrame_zero]

private theorem eq_line_iff (z : Ambient 0) (t : ℝ) :
    z = WithLp.toLp 2 ((0 : Space 0), t) ↔ z.ofLp.2 = t := by
  constructor
  · rintro rfl
    rfl
  · intro hz
    apply (WithLp.equiv 2 (Space 0 × ℝ)).injective
    exact Prod.ext (Subsingleton.elim _ _) hz

private theorem chart_of_isolated_interval {n : ℕ} (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i)
    (hfront : frontier (⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}) =
      ⋃ i, {WithLp.toLp 2 ((0 : Space 0), a i), WithLp.toLp 2 ((0 : Space 0), b i)})
    (i : Fin n) (p h : ℝ) (hh : 0 < h)
    (e : Ambient 0 ≃ᵃⁱ[ℝ] Ambient 0)
    (he0 : e 0 = WithLp.toLp 2 ((0 : Space 0), p))
    (hiso : ∀ t : ℝ, dist t p < h → ∀ j, t ∈ Icc (a j) (b j) → j = i)
    (hdist : ∀ z : Ambient 0, (e.symm z).ofLp.2 ∈ Ioo (-h) h → dist z.ofLp.2 p < h)
    (hside : ∀ z : Ambient 0, (e.symm z).ofLp.2 ∈ Ioo (-h) h →
      (z.ofLp.2 ∈ Ioo (a i) (b i) ↔ 0 < (e.symm z).ofLp.2))
    (hbd : ∀ z : Ambient 0, (e.symm z).ofLp.2 ∈ Ioo (-h) h →
      (z.ofLp.2 = a i ∨ z.ofLp.2 = b i ↔ (e.symm z).ofLp.2 = 0)) :
    ∃ C : BoundaryChart (⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}),
      C.frame (graph C.graphFunction C.center) = WithLp.toLp 2 ((0 : Space 0), p) := by
  have hs : ∀ z : Ambient 0, (e.symm z).ofLp.2 ∈ Ioo (-h) h →
      (z ∈ ⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)} ↔
        0 < (e.symm z).ofLp.2) := by
    intro z hz
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj⟩
      have hji := hiso z.ofLp.2 (hdist z hz) j ⟨hj.1.le, hj.2.le⟩
      subst j
      exact (hside z hz).mp hj
    · intro ht
      exact ⟨i, (hside z hz).mpr ht⟩
  have hb : ∀ z : Ambient 0, (e.symm z).ofLp.2 ∈ Ioo (-h) h →
      (z ∈ frontier (⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}) ↔
        (e.symm z).ofLp.2 = 0) := by
    intro z hz
    rw [hfront]
    simp only [mem_iUnion, mem_insert_iff, mem_singleton_iff, eq_line_iff]
    constructor
    · rintro ⟨j, hj⟩
      have hjcc : z.ofLp.2 ∈ Icc (a j) (b j) := by
        rcases hj with hj | hj
        · rw [hj]
          exact ⟨le_rfl, (hab j).le⟩
        · rw [hj]
          exact ⟨(hab j).le, le_rfl⟩
      have hji := hiso z.ofLp.2 (hdist z hz) j hjcc
      subst j
      exact (hbd z hz).mp hj
    · intro ht
      exact ⟨i, (hbd z hz).mpr ht⟩
  refine ⟨boundaryChartOfLocalSide e h hh hs hb, ?_⟩
  change e (graph (fun _ : Space 0 => (0 : ℝ)) 0) = _
  have hg : graph (fun _ : Space 0 => (0 : ℝ)) 0 = (0 : Ambient 0) := by
    apply (WithLp.equiv 2 (Space 0 × ℝ)).injective
    rfl
  rw [hg]
  exact he0

theorem interval_union_boundary_charts {n : ℕ} (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hfront : frontier (⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}) =
      ⋃ i, {WithLp.toLp 2 ((0 : Space 0), a i), WithLp.toLp 2 ((0 : Space 0), b i)}) :
    ∀ p ∈ frontier (⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}),
      ∃ C : BoundaryChart (⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}),
        C.frame (graph C.graphFunction C.center) = p := by
  intro p hp
  rw [hfront] at hp
  obtain ⟨i, hp⟩ := mem_iUnion.mp hp
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · obtain ⟨h, hh, hwidth, hiso⟩ :=
      isolate_interval_endpoint hab hinj hdis i (a i) (Or.inl rfl)
    apply chart_of_isolated_interval a b hab hfront i (a i) h hh
      (translateFrame (a i)) (translateFrame_zero (a i)) hiso
    · intro z hz
      rw [translateFrame_symm_coord] at hz
      simpa only [Real.dist_eq, abs_lt, mem_Ioo] using hz
    · intro z hz
      rw [translateFrame_symm_coord] at hz ⊢
      simp only [mem_Ioo] at hz ⊢
      constructor
      · intro hz'
        linarith [hz'.1]
      · intro hz'
        constructor <;> linarith [hz.1, hz.2]
    · intro z hz
      rw [translateFrame_symm_coord] at hz ⊢
      constructor
      · intro hz'
        rcases hz' with hz' | hz' <;> linarith [hz.1, hz.2]
      · intro hz'
        left
        linarith
  · obtain ⟨h, hh, hwidth, hiso⟩ :=
      isolate_interval_endpoint hab hinj hdis i (b i) (Or.inr rfl)
    apply chart_of_isolated_interval a b hab hfront i (b i) h hh
      (reverseFrame (b i)) (reverseFrame_zero (b i)) hiso
    · intro z hz
      rw [reverseFrame_symm_coord] at hz
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hz.1, hz.2]
    · intro z hz
      rw [reverseFrame_symm_coord] at hz ⊢
      simp only [mem_Ioo] at hz ⊢
      constructor
      · intro hz'
        linarith [hz'.2]
      · intro hz'
        constructor <;> linarith [hz.1, hz.2]
    · intro z hz
      rw [reverseFrame_symm_coord] at hz ⊢
      constructor
      · intro hz'
        rcases hz' with hz' | hz' <;> linarith [hz.1, hz.2]
      · intro hz'
        right
        linarith

/-- Distinct component intervals give exactly their endpoints as the boundary. -/
theorem interval_union_frontier {n : ℕ} (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) :
    frontier (⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}) =
      ⋃ i, {WithLp.toLp 2 (0, a i), WithLp.toLp 2 (0, b i)} := by
  have himage : verticalLine '' (⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}) =
      ⋃ i, Ioo (a i) (b i) := by
    rw [image_iUnion]
    congr 1
    funext i
    exact verticalLine.surjective.image_preimage _
  apply (oneDim_coordinate_transfer himage ?_).2
  rw [himage]
  exact RealDecomposition.finite_interval_union_frontier a b hab hdis

/-- The interval description alone suffices for the original local graph condition. -/
theorem interval_union_lipschitz {n : ℕ} (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) :
    IsLipschitzOpen (⋃ i, {z : Ambient 0 | z.ofLp.2 ∈ Ioo (a i) (b i)}) :=
  ⟨interval_union_open n a b, interval_union_bounded n a b,
    interval_union_boundary_charts a b hab hinj hdis (interval_union_frontier a b hab hdis)⟩

theorem one_dimension : Expected.OneDimension := by
  intro Ω
  constructor
  · exact one_dimension_forward
  · rintro ⟨n, a, b, hab, hinj, hdis, hΩ, _hfront⟩
    subst Ω
    exact interval_union_lipschitz a b hab hinj hdis

end P102.Sobolev.Geometry
