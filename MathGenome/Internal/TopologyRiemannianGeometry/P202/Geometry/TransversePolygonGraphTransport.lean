import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.TransversePolygonGraphTransport
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionCornerCollar
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Transport of the actual bounded-left Jordan domain through a transverse
affine collar graph. The fibre slide is constructed below and extended by the
identity; no isotopy or area sign is an input. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace P202.TransversePolygonGraphTransport
open P202Specs.PlanarRegionTopology (Plane ParameterCircle RegularJordanCurve realLift quarterTurn)
open P202.PlanarRegionTopology

/-- A short ray into an open set determines every ray in the same local
open half-space when the frontier is locally contained in its bounding plane. -/
lemma short_ray_into_of_local_frontier {U : Set Plane} (hU : IsOpen U)
    (p w v : Plane) (L : Plane →L[ℝ] ℝ)
    (hw : 0 < L w) (hv : 0 < L v)
    (hflat : ∃ R : ℝ, 0 < R ∧ ∀ x ∈ Metric.ball p R,
      x ∈ frontier U → L x = L p)
    (hinto : ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε → p + r • w ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε → p + r • v ∈ U := by
  obtain ⟨R, hR, hflat⟩ := hflat
  let C : Set Plane := Metric.ball p R ∩ {x | L p < L x}
  have hconv : Convex ℝ C := (convex_ball p R).inter
    (convex_halfSpace_gt L.toLinearMap.isLinear (L p))
  have havoid : Disjoint C (frontier U) := by
    apply disjoint_left.mpr
    intro x hx hxf
    exact (ne_of_gt hx.2) (hflat x hx.1 hxf)
  have hball (d : Plane) : ∀ᶠ r : ℝ in 𝓝 0, p + r • d ∈ Metric.ball p R := by
    have hc : Continuous (fun r : ℝ => p + r • d) := by fun_prop
    have hp : p + (0 : ℝ) • d ∈ Metric.ball p R := by simpa using hR
    exact hc.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp)
  obtain ⟨η, hη, hηw⟩ := Metric.eventually_nhds_iff.mp (hball w)
  obtain ⟨ε, hε, hεw⟩ := hinto
  let r := min ε η / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r < ε := by dsimp [r]; have := min_le_left ε η; linarith
  have hrη : r < η := by dsimp [r]; have := min_le_right ε η; linarith
  have hmem : p + r • w ∈ C := by
    refine ⟨hηw (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hrη), ?_⟩
    change L p < L (p + r • w)
    rw [map_add, map_smul, smul_eq_mul]
    exact lt_add_of_pos_right _ (mul_pos hr hw)
  have hCU : C ⊆ U := by
    apply hconv.isPreconnected.subset_of_closure_inter_subset hU
      ⟨_, hmem, hεw r hr hre⟩
    intro x hx
    by_contra hxU
    apply disjoint_left.mp havoid hx.2
    rw [hU.frontier_eq]
    exact ⟨hx.1, hxU⟩
  obtain ⟨δ, hδ, hδv⟩ := Metric.eventually_nhds_iff.mp (hball v)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ
  apply hCU
  refine ⟨hδv (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hs] using hsδ), ?_⟩
  change L p < L (p + s • v)
  rw [map_add, map_smul, smul_eq_mul]
  exact lt_add_of_pos_right _ (mul_pos hs hv)

lemma polygon_frontier_locally_in_edgeLine {n : ℕ} (p : Polygon Plane n)
    (o : Orientation ℝ Plane (Fin 2)) (hp : P202Specs.PolygonTurning.IsSimple p)
    {U : Set Plane} (hfr : frontier U = p.boundary ℝ)
    (i : Fin n) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ Metric.ball (p.edgePath ℝ i t) R,
      x ∈ frontier U →
      inner ℝ (o.rightAngleRotation (P202Specs.PolygonTurning.edgeVector p i)) x =
        inner ℝ (o.rightAngleRotation (P202Specs.PolygonTurning.edgeVector p i))
          (p.edgePath ℝ i t) := by
  classical
  let F : Set Plane := ⋃ j : {j : Fin n // j ≠ i}, p.edgeSet ℝ j.val
  have hF : IsClosed F := by
    apply isClosed_iUnion_of_finite
    intro j
    rw [Polygon.edgeSet_eq_image_edgePath]
    exact (isCompact_Icc.image (by
      simp only [Polygon.edgePath]
      fun_prop)).isClosed
  have hx : p.edgePath ℝ i t ∉ F := by
    intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hp.2.2.2 i j.val (Ne.symm j.property))
      (lineMap_mem_openSegment ℝ (p i) (p (finRotate n i)) ht) hj
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hF.isOpen_compl.mem_nhds hx)
  refine ⟨R, hR, ?_⟩
  intro x hxball hxfr
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hfr ▸ hxfr)
  have hji : j = i := by
    by_contra hji
    exact hball hxball (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  subst j
  rw [Polygon.edgeSet_eq_image_edgePath] at hj
  obtain ⟨s, hs, rfl⟩ := hj
  have hn : inner ℝ (o.rightAngleRotation (P202Specs.PolygonTurning.edgeVector p i))
      (P202Specs.PolygonTurning.edgeVector p i) = 0 := o.inner_rightAngleRotation_self _
  simp only [Polygon.edgePath, AffineMap.lineMap_apply_module']
  change inner ℝ _ (s • P202Specs.PolygonTurning.edgeVector p i + p i) =
    inner ℝ _ (t • P202Specs.PolygonTurning.edgeVector p i + p i)
  simp only [inner_add_right, real_inner_smul_right, hn, mul_zero, zero_add]

lemma polygonLeft_of_transverse_ray {n : ℕ} (p : Polygon Plane n)
    (o : Orientation ℝ Plane (Fin 2)) (hp : P202Specs.PolygonTurning.IsSimple p)
    {U : Set Plane} (hU : IsOpen U) (hfr : frontier U = p.boundary ℝ)
    (hrays : ∀ (i : Fin n) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 →
      ∃ w : Plane, 0 < inner ℝ w (o.rightAngleRotation
          (P202Specs.PolygonTurning.edgeVector p i)) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
          p.edgePath ℝ i t + r • w ∈ U) :
    P202Specs.PolygonTurning.HasBoundedSideOnLeft o p U := by
  intro i t ht
  obtain ⟨w, hw, hray⟩ := hrays i t ht
  let v := o.rightAngleRotation (P202Specs.PolygonTurning.edgeVector p i)
  have he : P202Specs.PolygonTurning.edgeVector p i ≠ 0 :=
    sub_ne_zero.mpr (hp.2.2.1 i).symm
  have hv : v ≠ 0 := by
    intro hz
    apply he
    apply o.rightAngleRotation.injective
    simpa only [map_zero] using hz
  apply short_ray_into_of_local_frontier hU (p.edgePath ℝ i t) w v (innerSL ℝ v)
  · change 0 < inner ℝ v w
    exact (real_inner_comm w v) ▸ hw
  · exact real_inner_self_pos.mpr hv
  · exact polygon_frontier_locally_in_edgeLine p o hp hfr i t ht
  · exact hray


/-- A compactly supported tent profile on a real collar fibre. -/
def tent (b r : ℝ) : ℝ := max 0 (b - |r|)

lemma tent_zero {b : ℝ} (hb : 0 < b) : tent b 0 = b := by
  simp [tent, hb.le]

lemma tent_eq_zero {b r : ℝ} (hr : b ≤ |r|) : tent b r = 0 := by
  simp [tent, max_eq_left (sub_nonpos.mpr hr)]

lemma tent_lipschitz (b x y : ℝ) : |tent b x - tent b y| ≤ |x - y| := by
  have h := abs_max_sub_max_le_max (0 : ℝ) (b - |x|) 0 (b - |y|)
  have he : b - |x| - (b - |y|) = -(|x| - |y|) := by ring
  simp only [sub_self, abs_zero, he, abs_neg] at h
  rw [max_eq_right (abs_nonneg (|x| - |y|))] at h
  exact h.trans (abs_abs_sub_abs_le_abs_sub x y)

/-- The fibre slide sends zero to f, with support in [-b,b]. -/
def fiberSlide (b f r : ℝ) : ℝ := r + (f / b) * tent b r

lemma fiberSlide_zero {b : ℝ} (hb : 0 < b) (f : ℝ) : fiberSlide b f 0 = f := by
  simp [fiberSlide, tent_zero hb, hb.ne']

lemma fiberSlide_fixed {b f r : ℝ} (hr : b ≤ |r|) : fiberSlide b f r = r := by
  simp [fiberSlide, tent_eq_zero hr]

lemma fiberSlide_continuous (b : ℝ) :
    Continuous (fun z : ℝ × ℝ => fiberSlide b z.1 z.2) := by
  unfold fiberSlide tent
  fun_prop

lemma fiberSlide_strictMono {b f : ℝ} (hb : 0 < b) (hf : |f| < b) :
    StrictMono (fiberSlide b f) := by
  have hc : |f / b| < 1 := by rw [abs_div, abs_of_pos hb]; exact (div_lt_one hb).mpr hf
  intro x y hxy
  have hd : |tent b x - tent b y| ≤ y - x := by
    simpa only [abs_of_neg (sub_neg.mpr hxy), neg_sub] using tent_lipschitz b x y
  have hm : |(f / b) * (tent b x - tent b y)| < y - x := by
    rw [abs_mul]
    calc
      |f / b| * |tent b x - tent b y| ≤ |f / b| * (y - x) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ < 1 * (y - x) := mul_lt_mul_of_pos_right hc (sub_pos.mpr hxy)
      _ = y - x := one_mul _
  have hm' := (abs_lt.mp hm).2
  dsimp [fiberSlide]
  nlinarith


/-- A fibrewise increasing, compactly supported slide in a circle collar
extends to a genuine homeomorphism of the plane. No differentiability of the
height function or inverse collar is required. -/
theorem extend_fiber_slide {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane)
    (hs : e.source = univ ×ˢ Ioo (-a) a)
    (T : C(ParameterCircle × ℝ, ℝ))
    (hmono : ∀ q, StrictMono (fun r : ℝ => T (q, r)))
    (hfix : ∀ q r, b ≤ |r| → T (q, r) = r) :
    ∃ H : Plane ≃ₜ Plane, ∀ (q : ParameterCircle) (r : ℝ), r ∈ Ioo (-a) a →
      H (e (q, r)) = e (q, T (q, r)) := by
  classical
  have ha : 0 < a := hb.trans hba
  have hm (q : ParameterCircle) : MapsTo (fun r : ℝ => T (q, r)) (Ioo (-a) a) (Ioo (-a) a) := by
    have hn := hfix q (-a) (by simpa [abs_of_pos ha] using hba.le)
    have hp := hfix q a (by simpa [abs_of_pos ha] using hba.le)
    intro r hr
    exact ⟨hn ▸ hmono q hr.1, hp ▸ hmono q hr.2⟩
  have hsurj (q : ParameterCircle) : SurjOn (fun r : ℝ => T (q, r))
      (Ioo (-a) a) (Ioo (-a) a) := by
    have hc : Continuous (fun r : ℝ => T (q, r)) := T.continuous.comp (continuous_const.prodMk continuous_id)
    have heq := hc.image_Ioo_of_strictMono (hmono q) (a := -a) (b := a)
    rw [hfix q (-a) (by simpa [abs_of_pos ha] using hba.le),
      hfix q a (by simpa [abs_of_pos ha] using hba.le)] at heq
    exact fun _ hy => heq.symm ▸ hy
  let F : ParameterCircle × ℝ → ParameterCircle × ℝ := fun z => (z.1, T z)
  have hF : Continuous F := continuous_fst.prodMk T.continuous
  have hFS : MapsTo F e.source e.source := by
    intro z hz
    rw [hs] at hz ⊢
    exact ⟨mem_univ _, hm z.1 hz.2⟩
  have hFinj : InjOn F e.source := by
    rintro ⟨q, r⟩ hx ⟨q', r'⟩ hy hxy
    change (q, T (q, r)) = (q', T (q', r')) at hxy
    have hq : q = q' := (Prod.mk.inj hxy).1
    subst q'
    exact Prod.ext rfl ((hmono q).injective (Prod.mk.inj hxy).2)
  let H : Plane → Plane := fun x => if x ∈ e.target then e (F (e.symm x)) else x
  have hH (z : ParameterCircle × ℝ) (hz : z ∈ e.source) : H (e z) = e (F z) := by
    simp only [H, if_pos (e.map_source hz), e.left_inv hz]
  have hHT : MapsTo H e.target e.target := by
    intro x hx
    simp only [H, if_pos hx]
    exact e.map_source (hFS (e.map_target hx))
  let K : Set Plane := e '' (univ ×ˢ Icc (-b) b)
  have hKS : univ ×ˢ Icc (-b) b ⊆ e.source := by
    intro z hz
    rw [hs]
    exact ⟨mem_univ _, (neg_lt_neg hba).trans_le hz.2.1, hz.2.2.trans_lt hba⟩
  have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (e.continuousOn.mono hKS)
  let O : Set Plane := e '' (univ ×ˢ Ioo (-b) b)
  have hOS : univ ×ˢ Ioo (-b) b ⊆ e.source :=
    (prod_mono_right Ioo_subset_Icc_self).trans hKS
  have hO : IsOpen O := e.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) hOS
  have hOK : O ⊆ K := image_mono (prod_mono_right Ioo_subset_Icc_self)
  have hfixed (x : Plane) (hx : x ∉ O) : H x = x := by
    by_cases hxt : x ∈ e.target
    · have hz : e.symm x ∈ e.source := e.map_target hxt
      have hr : b ≤ |(e.symm x).2| := by
        by_contra hn
        have hi := abs_lt.mp (lt_of_not_ge hn)
        exact hx ⟨e.symm x, ⟨mem_univ _, hi⟩, e.right_inv hxt⟩
      simp only [H, if_pos hxt, F, hfix _ _ hr, Prod.eta, e.right_inv hxt]
    · exact if_neg hxt
  have hHcont : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ e.target
    · have hc : ContinuousAt (fun y => e (F (e.symm y))) x :=
        (e.continuousAt (hFS (e.map_target hx))).comp (f := fun y : Plane => F (e.symm y))
          (hF.continuousAt.comp (f := fun y : Plane => e.symm y) (e.symm.continuousAt hx))
      apply hc.congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hx] with y hy
      exact if_pos hy
    · have hxK : x ∉ K := by
        rintro ⟨z, hz, rfl⟩
        exact hx (e.map_source (hKS hz))
      apply continuousAt_id.congr_of_eventuallyEq
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hfixed y (fun h => hy (hOK h))
  have hHinj : Function.Injective H := by
    intro x y hxy
    by_cases hx : x ∈ e.target <;> by_cases hy : y ∈ e.target
    · have hz := e.injOn (hFS (e.map_target hx)) (hFS (e.map_target hy)) (by
        simpa only [H, if_pos hx, if_pos hy] using hxy)
      have hzi := hFinj (e.map_target hx) (e.map_target hy) hz
      simpa only [e.right_inv hx, e.right_inv hy] using congrArg e hzi
    · have hyy : H y = y := if_neg hy
      exact False.elim (hy (hyy ▸ hxy ▸ hHT hx))
    · have hxx : H x = x := if_neg hx
      exact False.elim (hx (hxx ▸ hxy.symm ▸ hHT hy))
    · simpa only [H, if_neg hx, if_neg hy] using hxy
  have hHsurj : Function.Surjective H := by
    intro y
    by_cases hy : y ∈ e.target
    · have hz := e.map_target hy
      rw [hs] at hz
      obtain ⟨r, hr, hTr⟩ := hsurj (e.symm y).1 hz.2
      have hrs : ((e.symm y).1, r) ∈ e.source := by rw [hs]; exact ⟨mem_univ _, hr⟩
      refine ⟨e ((e.symm y).1, r), ?_⟩
      rw [hH _ hrs]
      simpa only [F, hTr, Prod.eta] using e.right_inv hy
    · exact ⟨y, if_neg hy⟩
  have hHclosed : IsClosedMap H := by
    intro A hA
    have heq : H '' A = H '' (A ∩ K) ∪ (A ∩ Oᶜ) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_cases hxK : x ∈ K
        · exact Or.inl ⟨x, ⟨hx, hxK⟩, rfl⟩
        · right
          rw [hfixed x (fun h => hxK (hOK h))]
          exact ⟨hx, fun h => hxK (hOK h)⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨hyA, hyO⟩)
        · exact ⟨x, hx.1, rfl⟩
        · exact ⟨y, hyA, hfixed y hyO⟩
    rw [heq]
    exact ((hK.inter_left hA).image hHcont).isClosed.union (hA.inter hO.isClosed_compl)
  let HH : Plane ≃ₜ Plane := (Equiv.ofBijective H ⟨hHinj, hHsurj⟩).toHomeomorphOfContinuousClosed
    hHcont hHclosed
  refine ⟨HH, ?_⟩
  intro q r hr
  exact hH (q, r) (by rw [hs]; exact ⟨mem_univ _, hr⟩)


lemma oriented_normal_covector_positive
    (o : Orientation ℝ Plane (Fin 2)) (D : Plane →L[ℝ] ℝ) (v W : Plane)
    (htrans : 0 < inner ℝ W (o.rightAngleRotation v)) (htan : D v = 0) (hW : D W = 1) :
    0 < D (o.rightAngleRotation v) := by
  have hv : v ≠ 0 := by intro h; simp [h] at htrans
  let B := o.basisRightAngleRotation v hv
  have hdec : W = B.repr W 0 • v + B.repr W 1 • o.rightAngleRotation v := by
    simpa only [B, Fin.sum_univ_two, Orientation.coe_basisRightAngleRotation,
      Matrix.cons_val_zero, Matrix.cons_val_one] using (B.sum_repr W).symm
  have horth : inner ℝ v (o.rightAngleRotation v) = 0 := by
    rw [real_inner_comm]; exact o.inner_rightAngleRotation_self v
  have hnorm : inner ℝ (o.rightAngleRotation v) (o.rightAngleRotation v) = inner ℝ v v :=
    o.inner_comp_rightAngleRotation v v
  have hpos : 0 < B.repr W 1 := by
    rw [hdec, inner_add_left, real_inner_smul_left, real_inner_smul_left, horth, hnorm,
      mul_zero, zero_add] at htrans
    exact (mul_pos_iff_of_pos_right (real_inner_self_pos.mpr hv)).mp htrans
  have he := congrArg D hdec
  simp only [map_add, map_smul, htan, smul_eq_mul, mul_zero, zero_add, hW] at he
  exact (mul_pos_iff_of_pos_left hpos).mp (by linarith [he])

lemma oriented_transversality_standard_nonzero
    (o : Orientation ℝ Plane (Fin 2)) (v W : Plane)
    (htrans : 0 < inner ℝ W (o.rightAngleRotation v)) :
    inner ℝ W (quarterTurn v) ≠ 0 := by
  have hv : v ≠ 0 := by intro h; simp [h] at htrans
  have hdec : inner ℝ W (quarterTurn v) • quarterTurn v + inner ℝ W v • v =
      inner ℝ v v • W := by
    ext i
    fin_cases i <;>
      simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two, EuclideanSpace.real_norm_sq_eq] <;> ring
  intro hz
  have he := congrArg (fun x : Plane => inner ℝ x (o.rightAngleRotation v)) hdec
  have ho : inner ℝ v (o.rightAngleRotation v) = 0 := by
    rw [real_inner_comm]; exact o.inner_rightAngleRotation_self v
  simp only [hz, zero_smul, zero_add, real_inner_smul_left, ho, mul_zero] at he
  have hh := mul_pos (real_inner_self_pos.mpr hv) htrans
  linarith
theorem oriented_affine_bicollar_normal_rays (c : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2))
    (W : C(ParameterCircle, Plane)) (t a : ℝ) (ha : 0 < a)
    (hc : ContDiffAt ℝ ∞ (realLift c.parametrization) t)
    (hW : ContDiffAt ℝ ∞ (realLift W) t)
    (htrans : 0 < inner ℝ (realLift W t)
      (o.rightAngleRotation (deriv (realLift c.parametrization) t))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      realLift c.parametrization t +
        r • o.rightAngleRotation (deriv (realLift c.parametrization) t) ∈
        (fun z : ParameterCircle × ℝ => c.parametrization z.1 + z.2 • W z.1) ''
          (univ ×ˢ Ioo 0 a) ∧
      realLift c.parametrization t -
        r • o.rightAngleRotation (deriv (realLift c.parametrization) t) ∈
        (fun z : ParameterCircle × ℝ => c.parametrization z.1 + z.2 • W z.1) ''
          (univ ×ˢ Ioo (-a) 0) := by
  obtain ⟨e, he, heq, hesmooth, heder⟩ := smooth_linear_collar_local_inverse hc hW (oriented_transversality_standard_nonzero o _ _ htrans)
  let p := realLift c.parametrization t
  let L := planeColumnEquiv (deriv (realLift c.parametrization) t) (realLift W t) (oriented_transversality_standard_nonzero o _ _ htrans)
  let F : Plane → ℝ := fun x => (e.symm x).2
  have hline : e (t, (0 : ℝ)) = p := by simp [heq, p]
  have hsymm : e.symm p = (t, (0 : ℝ)) := by
    rw [← hline]
    exact e.left_inv he
  have hpt : p ∈ e.target := hline ▸ e.map_source he
  have hzero : F p = 0 := by simp only [F, hsymm]
  have hDF : HasFDerivAt F
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (L.symm : Plane →L[ℝ] (ℝ × ℝ))) p := by
    exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp p heder
  have hLv : L ((1 : ℝ), 0) = deriv (realLift c.parametrization) t := by
    change planeColumnMap _ _ ((1 : ℝ), 0) = _
    simp
  have hLW : L ((0 : ℝ), 1) = realLift W t := by
    change planeColumnMap _ _ ((0 : ℝ), 1) = _
    simp
  have htan : fderiv ℝ F p (deriv (realLift c.parametrization) t) = 0 := by
    rw [hDF.fderiv, ContinuousLinearMap.comp_apply, ← hLv]
    change (L.symm (L ((1 : ℝ), 0))).2 = 0
    rw [L.symm_apply_apply]
  have hunit : fderiv ℝ F p (realLift W t) = 1 := by
    rw [hDF.fderiv, ContinuousLinearMap.comp_apply, ← hLW]
    change (L.symm (L ((0 : ℝ), 1))).2 = 1
    rw [L.symm_apply_apply]
  have hinterval : F ⁻¹' Ioo (-a) a ∈ 𝓝 p :=
    hDF.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds
      ⟨by rw [hzero]; linarith, by rwa [hzero]⟩)
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_target.mem_nhds hpt) hinterval)
  apply normal_rays_in_local_sides F p _ hO hpO hDF.differentiableAt hzero
    (oriented_normal_covector_positive o _ _ _ htrans htan hunit)
  · intro x hx hsign
    refine ⟨(((e.symm x).1 : ParameterCircle), F x),
      ⟨mem_univ _, hsign, (hOsub hx).2.2⟩, ?_⟩
    simpa only [heq, F, realLift] using e.right_inv (hOsub hx).1
  · intro x hx hsign
    refine ⟨(((e.symm x).1 : ParameterCircle), F x),
      ⟨mem_univ _, (hOsub hx).2.1, hsign⟩, ?_⟩
    simpa only [heq, F, realLift] using e.right_inv (hOsub hx).1


/-- The affine collar's positive half belongs to the originally prescribed
bounded-left side. The conclusion includes fibres based at joins. -/
theorem positive_collar_subset (c : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2)) (U : Set Plane)
    (hU : P202Specs.PlaneTurning.IsBoundedSide c U)
    (hleft : P202Specs.PlaneTurning.HasBoundedSideOnLeft c o U)
    (W : C(ParameterCircle, Plane)) {a : ℝ} (ha : 0 < a)
    (e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane)
    (hs : e.source = univ ×ˢ Ioo (-a) a)
    (he : ∀ q r, e (q, r) = c.parametrization q + r • W q)
    (hW : ∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
      ContDiffAt ℝ ∞ (realLift W) t ∧
        0 < inner ℝ (W (t : ParameterCircle))
          (o.rightAngleRotation (deriv (realLift c.parametrization) t))) :
    e '' (univ ×ˢ Ioo 0 a) ⊆ U := by
  have hzero (q : ParameterCircle) : e (q, 0) = c.parametrization q := by simp [he]
  have hzs (q : ParameterCircle) : (q, (0 : ℝ)) ∈ e.source := by
    rw [hs]; exact ⟨mem_univ _, by linarith, ha⟩
  have hPS : univ ×ˢ Ioo 0 a ⊆ e.source := by
    intro z hz
    rw [hs]
    exact ⟨mem_univ _, (neg_lt_zero.mpr ha).trans hz.2.1, hz.2.2⟩
  have hconn : IsPreconnected (e '' (univ ×ˢ Ioo 0 a)) :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image e (e.continuousOn.mono hPS)
  have havoid : Disjoint (e '' (univ ×ˢ Ioo 0 a)) (frontier U) := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    rw [hU.2.2.2] at hx
    obtain ⟨q, hq⟩ := hx
    have heq : e z = e (q, 0) := by rw [hzero]; exact hq.symm
    have hz0 : z.2 = 0 := congrArg Prod.snd (e.injOn (hPS hz) (hzs q) heq)
    exact hz.2.1.ne' hz0
  rcases connected_frontier_dichotomy hU.1 hconn havoid with hpos | hneg
  · exact hpos
  · obtain ⟨t, ht, htn⟩ := exists_nonjoin_in_Ioo c (show (0 : ℝ) < 1 by norm_num)
    obtain ⟨ε, hε, hnormal⟩ := hleft t htn
    obtain ⟨η, hη, hcollar⟩ := oriented_affine_bicollar_normal_rays c o W t a ha
      (c.smooth_off_joins t htn) (hW t htn).1 (hW t htn).2
    let r := min ε η / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrε : r < ε := by dsimp [r]; have := min_le_left ε η; linarith
    have hrη : r < η := by dsimp [r]; have := min_le_right ε η; linarith
    have hp := (hcollar r hr hrη).1
    have hp' : realLift c.parametrization t +
        r • o.rightAngleRotation (deriv (realLift c.parametrization) t) ∈
        e '' (univ ×ˢ Ioo 0 a) := by
      convert hp using 1
      congr 1
      funext z
      exact he z.1 z.2
    exact False.elim (hneg hp' (subset_closure (hnormal r hr hrε)))

/-- The complete bounded-side transport theorem, with the original geometric
predicates and every edge-interior transverse test. -/
theorem transport : P202Specs.TransversePolygonGraphTransport.Expected.transport := by
  intro c o U hU hleft W a ha e hs he hW n p hp f hf hgraph htrans
  let b := a / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b < a := by dsimp [b]; linarith
  have hfb (q : ParameterCircle) : |f q| < b := by
    have := hf q
    dsimp [b]
    linarith
  let T : C(ParameterCircle × ℝ, ℝ) :=
    ⟨fun z => fiberSlide b (f z.1) z.2,
      (fiberSlide_continuous b).comp ((f.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have hmono (q : ParameterCircle) : StrictMono (fun r : ℝ => T (q, r)) :=
    fiberSlide_strictMono hb (hfb q)
  have hfix (q : ParameterCircle) (r : ℝ) (hr : b ≤ |r|) : T (q, r) = r :=
    fiberSlide_fixed hr
  have hTzero (q : ParameterCircle) : T (q, 0) = f q := fiberSlide_zero hb _
  obtain ⟨H, hH⟩ := extend_fiber_slide hb hba e hs T hmono hfix
  have hzero (q : ParameterCircle) : e (q, 0) = c.parametrization q := by simp [he]
  have hHzero (q : ParameterCircle) : H (c.parametrization q) = e (q, f q) := by
    rw [← hzero q, hH q 0 ⟨by linarith, ha⟩, hTzero]
  have hboundary : H '' c.trace = p.boundary ℝ := by
    rw [hgraph]
    ext z
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, (hHzero q).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨c.parametrization q, mem_range_self _, hHzero q⟩
  let UQ : Set Plane := H '' U
  have hUQ : P202Specs.PolygonTurning.IsBoundedSide p UQ := by
    refine ⟨H.isOpenMap U hU.1, hU.2.1.image H H.continuous.continuousOn, ?_, ?_⟩
    · exact ((hU.2.2.1.isCompact_closure.image H.continuous).isBounded).subset
        (image_mono subset_closure)
    · change frontier (H '' U) = p.boundary ℝ
      rw [← H.image_frontier, hU.2.2.2, hboundary]
  have hpositive := positive_collar_subset c o U hU hleft W ha e hs he hW
  refine ⟨UQ, hUQ, ?_⟩
  apply polygonLeft_of_transverse_ray p o hp hUQ.1 hUQ.2.2.2
  intro i t ht
  let z := p.edgePath ℝ i t
  have hzbd : z ∈ p.boundary ℝ := mem_iUnion.mpr
    ⟨i, ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩⟩
  obtain ⟨q, hq⟩ := hgraph ▸ hzbd
  change e (q, f q) = z at hq
  have hqsource : (q, f q) ∈ e.source := by
    rw [hs]
    have hfq := abs_lt.mp (hf q)
    exact ⟨mem_univ _, by linarith [hfq.1], by linarith [hfq.2]⟩
  have hqinv : e.symm z = (q, f q) := by rw [← hq]; exact e.left_inv hqsource
  refine ⟨W q, ?_, b - f q, ?_, ?_⟩
  · have hh : 0 < inner ℝ (W ((e.symm z).1))
        (o.rightAngleRotation (P202Specs.PolygonTurning.edgeVector p i)) := htrans i t ht
    simpa only [hqinv] using hh
  · have := (abs_lt.mp (hfb q)).2
    linarith
  · intro r hr hrr
    have hy : f q + r ∈ Ioo (f q) b := ⟨by linarith, by linarith⟩
    have hTc : Continuous (fun s : ℝ => T (q, s)) :=
      T.continuous.comp (continuous_const.prodMk continuous_id)
    have hTb : T (q, b) = b := hfix q b (by rw [abs_of_pos hb])
    have himg := hTc.image_Ioo_of_strictMono (hmono q) (a := (0 : ℝ)) (b := b)
    rw [hTzero, hTb] at himg
    obtain ⟨s, hspos, hTs⟩ := himg.symm ▸ hy
    have hsa : s ∈ Ioo (-a) a := ⟨by linarith [hspos.1], hspos.2.trans hba⟩
    have hxU : e (q, s) ∈ U := hpositive ⟨(q, s), ⟨mem_univ _, hspos.1, hsa.2⟩, rfl⟩
    refine ⟨e (q, s), hxU, ?_⟩
    change T (q, s) = f q + r at hTs
    rw [hH q s hsa, hTs]
    change e (q, f q + r) = z + r • W q
    rw [← hq, he, he, add_smul]
    abel

end P202.TransversePolygonGraphTransport
