import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RegionalLocalOneSidedness
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ArrangementGraphGeometry
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse

/-! Actual regional coordinate domains and full-plane local one-sidedness.
The proof transfers exact original-atlas sign chambers through ambient chart
transition germs. The exterior neighborhoods are subsets of the full plane,
including the part outside the half-space model at original boundary points.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.FiniteRegularityData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BoundaryData
open P202Specs.PlanarRegionTopology
open P202Specs.SurfaceRegionConstruction
universe u

namespace P202.SurfaceRegionConstruction
namespace PlaneSectors

def positiveOrthant (A : Set (Fin 2)) : Set Plane := {x | ∀ i ∈ A, 0 < x i}
def closedOrthant (A : Set (Fin 2)) : Set Plane := {x | ∀ i ∈ A, 0 ≤ x i}

lemma closed_closedOrthant (A : Set (Fin 2)) : IsClosed (closedOrthant A) := by
  have hc (i : Fin 2) : Continuous (fun x : Plane => x i) := by fun_prop
  have h : IsClosed (⋂ i ∈ A, {x : Plane | 0 ≤ x i}) :=
    isClosed_biInter fun i hi => isClosed_le continuous_const (hc i)
  simpa only [closedOrthant, Set.ofPred_forall] using h

lemma closure_positiveOrthant (A : Set (Fin 2)) : closure (positiveOrthant A) = closedOrthant A := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun x hx i hi => (hx i hi).le) (closed_closedOrthant A)
  · intro p hp
    let v : Plane := !₂[1, 1]
    have hv (i : Fin 2) : v i = 1 := by fin_cases i <;> rfl
    let F : ℝ → Plane := fun t => p + t • v
    have hF : Continuous F := by fun_prop
    have hz : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact (show (0 : ℝ) ≤ 0 from le_rfl)
    have hsub : F '' Ioi 0 ⊆ positiveOrthant A := by
      rintro x ⟨t, ht, rfl⟩ i hi
      change 0 < p i + t * v i
      rw [hv, mul_one]
      exact add_pos_of_nonneg_of_pos (hp i hi) ht
    have hcl := closure_mono hsub (mem_closure_image hF.continuousAt hz)
    simpa [F] using hcl

lemma convex_positiveOrthant (A : Set (Fin 2)) : Convex ℝ (positiveOrthant A) := by
  intro x hx y hy a b ha hb hab i hi
  change 0 < a * x i + b * y i
  rcases lt_or_eq_of_le ha with hapos | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos (hx i hi))
      (mul_nonneg hb (hy i hi).le)
  · have hb1 : b = 1 := by simpa using hab
    simpa only [zero_mul, zero_add, hb1, one_mul] using hy i hi

lemma open_positiveOrthant (A : Set (Fin 2)) : IsOpen (positiveOrthant A) := by
  classical
  have h : IsOpen (⋂ i ∈ A, {x : Plane | 0 < x i}) :=
    (Set.toFinite A).isOpen_biInter fun i hi => isOpen_lt continuous_const (by fun_prop)
  simpa only [positiveOrthant, Set.ofPred_forall] using h


/-- Every coordinate open orthant, including a single open half-plane and a
quadrant, is locally one-sided in the full ambient plane. The outside of a
quadrant is connected through points negative in both active coordinates. -/
theorem locallyOneSided_positiveOrthant (A : Set (Fin 2)) :
    LocallyOneSided (positiveOrthant A) := by
  classical
  intro p hp O hO hpO
  have hpcl : p ∈ closedOrthant A := by
    rw [← closure_positiveOrthant]
    exact hp.1
  have hpnot : p ∉ positiveOrthant A := by
    simpa only [(open_positiveOrthant A).interior_eq] using hp.2
  obtain ⟨i₀, hi₀, hpi₀⟩ : ∃ i ∈ A, p i = 0 := by
    simp only [positiveOrthant, mem_ofPred_eq, not_forall, not_lt] at hpnot
    obtain ⟨i, hi, hpi⟩ := hpnot
    exact ⟨i, hi, le_antisymm hpi (hpcl i hi)⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hpO)
  let B : Set (Fin 2) := {i | i ∈ A ∧ 0 < p i}
  let N : Set Plane := Metric.ball p r ∩ positiveOrthant B
  have hN : IsOpen N := Metric.isOpen_ball.inter (open_positiveOrthant B)
  have hpN : p ∈ N := ⟨Metric.mem_ball_self hr, fun i hi => hi.2⟩
  have hNconv : Convex ℝ N := (convex_ball p r).inter (convex_positiveOrthant B)
  have hin : IsConnected (N ∩ positiveOrthant A) := by
    apply (hNconv.inter (convex_positiveOrthant A)).isConnected
    obtain ⟨x, hxN, hxU⟩ := mem_closure_iff_nhds.mp hp.1 N (hN.mem_nhds hpN)
    exact ⟨x, hxN, hxU⟩
  let v : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i => if p i = 0 then -1 else 0)
  let F : ℝ → Plane := fun t => p + t • v
  have hF : Continuous F := by fun_prop
  have hFzero : F 0 = p := by simp [F]
  have hFN : F ⁻¹' N ∈ 𝓝 (0 : ℝ) := by
    apply hF.continuousAt.preimage_mem_nhds
    rw [hFzero]
    exact hN.mem_nhds hpN
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.mp hFN
  let t : ℝ := δ / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htδ : t < δ := by dsimp [t]; linarith
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htδ
  let q : Plane := F t
  have hqN : q ∈ N := hδN htball
  have hqneg : ∀ i : Fin 2, p i = 0 → q i < 0 := by
    intro i hpi
    change p i + t * (if p i = 0 then -1 else 0) < 0
    simp only [hpi, ↓reduceIte, mul_neg, mul_one, zero_add]
    exact neg_neg_of_pos ht
  have hqout : q ∈ N \ closedOrthant A := by
    refine ⟨hqN, ?_⟩
    intro hq
    exact (not_le_of_gt (hqneg i₀ hpi₀)) (hq i₀ hi₀)
  have hstar : StarConvex ℝ q (N \ closedOrthant A) := by
    intro x hx a b ha hb hab
    refine ⟨hNconv hqN hx.1 ha hb hab, ?_⟩
    obtain ⟨i, hi, hxi⟩ : ∃ i ∈ A, x i < 0 := by
      simpa only [closedOrthant, mem_ofPred_eq, not_forall, not_le, exists_prop] using hx.2
    have hpi : p i = 0 := by
      by_contra hne
      have hpp : 0 < p i := lt_of_le_of_ne (hpcl i hi) (Ne.symm hne)
      have hxp : 0 < x i := hx.1.2 i ⟨hi, hpp⟩
      exact (not_lt_of_gt hxp) hxi
    have hqi : q i < 0 := hqneg i hpi
    have hsum : (a • q + b • x) i < 0 := by
      change a * q i + b * x i < 0
      rcases lt_or_eq_of_le ha with hapos | rfl
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hapos hqi)
          (mul_nonpos_of_nonneg_of_nonpos hb hxi.le)
      · have hb1 : b = 1 := by simpa using hab
        simpa only [zero_mul, zero_add, hb1, one_mul] using hxi
    intro hz
    exact (not_le_of_gt hsum) (hz i hi)
  refine ⟨N, hN, hpN, inter_subset_left.trans hball, hin, ?_⟩
  rw [closure_positiveOrthant]
  exact (hstar.isPathConnected hqout).isConnected


/-- Local one-sidedness is preserved by an ambient homeomorphism. -/
theorem locallyOneSided_preimage (e : Plane ≃ₜ Plane) (U : Set Plane)
    (hU : LocallyOneSided U) : LocallyOneSided (e ⁻¹' U) := by
  intro p hp O hO hpO
  have hep : e p ∈ frontier U := by
    change p ∈ e ⁻¹' frontier U
    rw [e.preimage_frontier]
    exact hp
  obtain ⟨N, hN, hepN, hNO, hin, hout⟩ := hU (e p) hep
    (e '' O) (e.isOpenMap _ hO) (mem_image_of_mem e hpO)
  refine ⟨e ⁻¹' N, hN.preimage e.continuous, hepN, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hye⟩ := hNO hx
    exact e.injective hye ▸ hy
  · have hconn := hin.preimage_of_isOpenMap e.injective e.isOpenMap
      (by simp : N ∩ U ⊆ range e)
    simpa only [preimage_inter] using hconn
  · have hconn := hout.preimage_of_isOpenMap e.injective e.isOpenMap
      (by simp : N \ closure U ⊆ range e)
    simpa only [preimage_sdiff, e.preimage_closure] using hconn

/-- Independent coordinate reflections realize every sign chamber by an
ambient plane homeomorphism. -/
def flipCoordinates (s : Fin 2 → Bool) (x : Plane) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if s i then x i else -x i)

lemma flipCoordinates_involutive (s : Fin 2 → Bool) :
    Function.Involutive (flipCoordinates s) := by
  intro x
  ext i
  change (if s i then (if s i then x i else -x i)
    else -(if s i then x i else -x i)) = x i
  cases s i <;> simp

lemma continuous_flipCoordinates (s : Fin 2 → Bool) : Continuous (flipCoordinates s) := by
  have h (i : Fin 2) : Continuous (fun x : Plane => if s i then x i else -x i) := by
    cases s i <;> dsimp <;> fun_prop
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (continuous_pi h)

def signHomeomorph (s : Fin 2 → Bool) : Plane ≃ₜ Plane where
  toFun := flipCoordinates s
  invFun := flipCoordinates s
  left_inv := flipCoordinates_involutive s
  right_inv := flipCoordinates_involutive s
  continuous_toFun := continuous_flipCoordinates s
  continuous_invFun := continuous_flipCoordinates s

lemma signedOrthant_eq_preimage (A : Set (Fin 2)) (s : Fin 2 → Bool) :
    signedOrthant A s = signHomeomorph s ⁻¹' positiveOrthant A := by
  ext x
  change (∀ i ∈ A, if s i then 0 < x i else x i < 0) ↔
    ∀ i ∈ A, 0 < (if s i then x i else -x i)
  apply forall₂_congr
  intro i hi
  cases s i <;> simp

theorem locallyOneSided_signedOrthant (A : Set (Fin 2)) (s : Fin 2 → Bool) :
    LocallyOneSided (signedOrthant A s) := by
  rw [signedOrthant_eq_preimage]
  exact locallyOneSided_preimage _ _ (locallyOneSided_positiveOrthant A)


end PlaneSectors
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction

/-- Actual smooth transitions between original charts extend, even at a face,
to a genuine local homeomorphism of the full Euclidean ambient spaces. -/
theorem ambient_chart_transition {n : ℕ} {kind : SmoothManifolds.ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold n kind M)
    (c d : ModelChart n kind M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hpc : p ∈ c.source) (hpd : p ∈ d.source) :
    ∃ j : OpenPartialHomeomorph (Euclidean n) (Euclidean n),
      (c p).val ∈ j.source ∧
      (∀ᶠ x in 𝓝 p, j (c x).val = (d x).val) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target := by
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 c hc d hd) hpc hpd
  have hFd := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  have hderiv : chartDerivative c d id p = fderiv ℝ F (c p).val :=
    SmoothManifolds.FiniteRegularity.coordinateDerivative_eq c _ p hpc _ ⟨F, hFd, heF⟩
  have hchain := SmoothManifolds.FiniteRegularity.derivative_cocycle (⊤ : ℕ∞) (by simp)
    S.smoothStructure.val S.smoothStructure.property.1 c d c hc hd hc p hpc hpd hpc
  rw [SmoothManifolds.FiniteRegularity.chartDerivative_id c p hpc] at hchain
  have hinj : Function.Injective (fderiv ℝ F (c p).val) := by
    rw [← hderiv]
    intro v w hvw
    have h := congrArg (chartDerivative d c id p) hvw
    change ((chartDerivative d c id p).comp (chartDerivative c d id p)) v =
      ((chartDerivative d c id p).comp (chartDerivative c d id p)) w at h
    rwa [← hchain] at h
  have hbij : Function.Bijective (fderiv ℝ F (c p).val) :=
    ⟨hinj, (fderiv ℝ F (c p).val).toLinearMap.injective_iff_surjective.mp hinj⟩
  obtain ⟨j, hpj, hj, hjs⟩ := SmoothManifolds.InteriorInverse.euclidean_inverse
    (⊤ : ℕ∞) (by simp) F U hU hF (c p).val hpU _ hFd hbij
  exact ⟨j, hpj, by simpa only [hj, Filter.EventuallyEq, id_eq] using heF, hjs⟩

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.PlaneSectors

/-- A genuine ambient partial homeomorphism transports local closures. -/
lemma closure_mem_iff_of_partialHomeomorph (e : OpenPartialHomeomorph Plane Plane)
    (U W : Set Plane) (hmem : ∀ x ∈ e.source, x ∈ U ↔ e x ∈ W)
    {p : Plane} (hp : p ∈ e.source) :
    p ∈ closure U ↔ e p ∈ closure W := by
  constructor
  · intro hpU
    have hlocal : p ∈ closure (U ∩ e.source) := by
      rw [inter_comm]
      exact e.open_source.inter_closure ⟨hp, hpU⟩
    apply closure_mono (s := e '' (U ∩ e.source)) _
      (mem_closure_image (e.continuousAt hp) hlocal)
    rintro y ⟨x, ⟨hxU, hxs⟩, rfl⟩
    exact (hmem x hxs).mp hxU
  · intro hpW
    have hlocal : e p ∈ closure (W ∩ e.target) := by
      rw [inter_comm]
      exact e.open_target.inter_closure ⟨e.map_source hp, hpW⟩
    have himage := mem_closure_image (e.symm.continuousAt (e.map_source hp)) hlocal
    rw [e.left_inv hp] at himage
    apply closure_mono (s := e.symm '' (W ∩ e.target)) _ himage
    rintro x ⟨y, ⟨hyW, hyt⟩, rfl⟩
    apply (hmem (e.symm y) (e.map_target hyt)).mpr
    rwa [e.right_inv hyt]

/-- Full-plane one-sidedness is invariant under a genuine ambient local
homeomorphism. All agreement hypotheses concern actual open subsets. -/
theorem oneSided_at_of_partialHomeomorph (e : OpenPartialHomeomorph Plane Plane)
    (U W : Set Plane) (hU : IsOpen U) (hW : IsOpen W)
    (hmem : ∀ x ∈ e.source, x ∈ U ↔ e x ∈ W) (hside : LocallyOneSided W)
    {p : Plane} (hps : p ∈ e.source) (hp : p ∈ frontier U)
    (O : Set Plane) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ O ∧
      IsConnected (N ∩ U) ∧ IsConnected (N \ closure U) := by
  have hep : e p ∈ frontier W := by
    refine ⟨(closure_mem_iff_of_partialHomeomorph e U W hmem hps).mp hp.1, ?_⟩
    rw [hW.interior_eq]
    intro hepW
    exact hp.2 (by rw [hU.interior_eq]; exact (hmem p hps).mpr hepW)
  have hopen : IsOpen (e '' (O ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hO.inter e.open_source) inter_subset_right
  obtain ⟨N, hN, hepN, hNO, hin, hout⟩ := hside (e p) hep
    (e '' (O ∩ e.source)) hopen (mem_image_of_mem e ⟨hpO, hps⟩)
  have hNt : N ⊆ e.target := by
    intro y hy
    obtain ⟨x, ⟨_, hxs⟩, hxy⟩ := hNO hy
    exact hxy ▸ e.map_source hxs
  let V := e.source ∩ e ⁻¹' N
  have hV : IsOpen V := e.isOpen_inter_preimage hN
  have hVO : V ⊆ O := by
    rintro x ⟨hxs, hxN⟩
    obtain ⟨y, ⟨hyO, hys⟩, hyx⟩ := hNO hxN
    have hxy : y = x := by
      have hh := congrArg e.symm hyx
      rwa [e.left_inv hys, e.left_inv hxs] at hh
    exact hxy ▸ hyO
  have hinside : V ∩ U = e.symm '' (N ∩ W) := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨hxs, hxN⟩, hxU⟩
      exact ⟨e x, ⟨hxN, (hmem x hxs).mp hxU⟩, e.left_inv hxs⟩
    · rintro x ⟨y, ⟨hyN, hyW⟩, rfl⟩
      have hys : e.symm y ∈ e.source := e.map_target (hNt hyN)
      refine ⟨⟨hys, ?_⟩, (hmem _ hys).mpr ?_⟩
      · change e (e.symm y) ∈ N
        rwa [e.right_inv (hNt hyN)]
      · rwa [e.right_inv (hNt hyN)]
  have houtside : V \ closure U = e.symm '' (N \ closure W) := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨hxs, hxN⟩, hxU⟩
      refine ⟨e x, ⟨hxN, ?_⟩, e.left_inv hxs⟩
      exact fun hc => hxU ((closure_mem_iff_of_partialHomeomorph e U W hmem hxs).mpr hc)
    · rintro x ⟨y, ⟨hyN, hyW⟩, rfl⟩
      have hys : e.symm y ∈ e.source := e.map_target (hNt hyN)
      refine ⟨⟨hys, ?_⟩, ?_⟩
      · change e (e.symm y) ∈ N
        rwa [e.right_inv (hNt hyN)]
      · intro hc
        have hh := (closure_mem_iff_of_partialHomeomorph e U W hmem hys).mp hc
        rw [e.right_inv (hNt hyN)] at hh
        exact hyW hh
  refine ⟨V, hV, ⟨hps, hepN⟩, hVO, ?_, ?_⟩
  · rw [hinside]
    exact hin.image e.symm (e.symm.continuousOn.mono (inter_subset_left.trans hNt))
  · rw [houtside]
    exact hout.image e.symm (e.symm.continuousOn.mono (sdiff_subset.trans hNt))


/-- The version for an actual coordinate domain locally equal to the image of
a model chamber under an ambient partial homeomorphism. Restricting the inverse
to `V` avoids any assertion at the artificial boundary of the chart target. -/
theorem oneSided_at_of_local_image (e : OpenPartialHomeomorph Plane Plane)
    (W U V : Set Plane) (hW : IsOpen W) (hU : IsOpen U) (hV : IsOpen V)
    (heq : U ∩ V = (e '' (W ∩ e.source)) ∩ V) (hside : LocallyOneSided W)
    {p : Plane} (hpt : p ∈ e.target) (hpV : p ∈ V) (hp : p ∈ frontier U)
    (O : Set Plane) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ O ∧
      IsConnected (N ∩ U) ∧ IsConnected (N \ closure U) := by
  let d := e.symm.restrOpen V hV
  have hpds : p ∈ d.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hpt, hpV⟩
  have hmem : ∀ x ∈ d.source, x ∈ U ↔ d x ∈ W := by
    intro x hx
    have hxTV : x ∈ e.target ∩ V := by
      simpa only [d, OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.symm_source] using hx
    have heqx := Set.ext_iff.mp heq x
    have hux : x ∈ U ↔ x ∈ e '' (W ∩ e.source) := by
      simpa only [mem_inter_iff, and_iff_left hxTV.2] using heqx
    change x ∈ U ↔ e.symm x ∈ W
    rw [hux]
    constructor
    · rintro ⟨y, ⟨hyW, hys⟩, hyx⟩
      have hxy : e.symm x = y := by rw [← hyx, e.left_inv hys]
      rwa [hxy]
    · intro hxW
      exact ⟨e.symm x, ⟨hxW, e.map_target hxTV.1⟩, e.right_inv hxTV.1⟩
  exact oneSided_at_of_partialHomeomorph d U W hU hW hmem hside hpds hp O hO hpO


end P202.SurfaceRegionConstruction.PlaneSectors

namespace P202.SurfaceRegionConstruction

/-- Open subsets of an actual model chart have ambient-plane open coordinate
representatives; the equality is tested only on actual chart points. -/
theorem exists_ambient_open_coordinates
    {X : Type*} [TopologicalSpace X] {kind : ModelKind}
    (e : ModelChart 2 kind X) (U : Set X) (hU : IsOpen U) (hUs : U ⊆ e.source) :
    ∃ W : Set Plane, IsOpen W ∧
      ∀ x ∈ e.source, coordinates e x ∈ W ↔ x ∈ U := by
  have heU : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU hUs
  obtain ⟨V,hV,hVeq⟩ := isOpen_induced_iff.mp heU
  refine ⟨toPlane.symm ⁻¹' V,hV.preimage toPlane.symm.continuous,?_⟩
  intro x hxs
  change toPlane.symm (coordinates e x) ∈ V ↔ x ∈ U
  rw [show toPlane.symm (coordinates e x) = (e x).val from toPlane.symm_apply_apply _]
  change e x ∈ Subtype.val ⁻¹' V ↔ x ∈ U
  rw [hVeq]
  constructor
  · rintro ⟨y,hyU,hyx⟩
    exact e.injOn (hUs hyU) hxs hyx ▸ hyU
  · intro hxU
    exact mem_image_of_mem e hxU

/-- A full-plane chamber image in one actual chart transfers to the coordinate
domain in a second chart under an ambient transition germ. Complete equality
with the chamber ensures no points outside the original model are introduced
at the seam. -/
theorem local_image_of_chart_germ
    {X : Type*} [TopologicalSpace X] {kind : ModelKind}
    (c d : ModelChart 2 kind X) (C : Set X) (Q : Set Plane)
    (hCd : C ⊆ d.source) {p : X} (hpc : p ∈ c.source) (hpd : p ∈ d.source)
    (r : ℝ) (hr : 0 < r)
    (hchamber : coordinates c '' (C ∩ c.source) = Q ∩ Metric.ball (coordinates c p) r)
    (j : OpenPartialHomeomorph Plane Plane) (hpj : coordinates c p ∈ j.source)
    (hagree : ∀ᶠ x in 𝓝 p, j (coordinates c x) = coordinates d x) :
    ∃ (k : OpenPartialHomeomorph Plane Plane) (V : Set Plane),
      IsOpen V ∧ coordinates d p ∈ V ∧ coordinates d p ∈ k.target ∧
      (coordinates d '' C) ∩ V = (k '' (Q ∩ k.source)) ∩ V := by
  obtain ⟨U,hUsub,hUopen,hpU⟩ := mem_nhds_iff.mp hagree
  let U₁ := U ∩ c.source ∩ d.source
  have hU₁ : IsOpen U₁ := (hUopen.inter c.open_source).inter d.open_source
  have hpU₁ : p ∈ U₁ := ⟨⟨hpU,hpc⟩,hpd⟩
  obtain ⟨W,hW,hWmem⟩ := exists_ambient_open_coordinates c U₁ hU₁
    (fun x hx => hx.1.2)
  let k := j.restrOpen (W ∩ Metric.ball (coordinates c p) r) (hW.inter Metric.isOpen_ball)
  have hks : k.source = j.source ∩ (W ∩ Metric.ball (coordinates c p) r) :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hpk : coordinates c p ∈ k.source := by
    rw [hks]
    refine ⟨hpj,(hWmem p hpc).mpr hpU₁,?_⟩
    simpa only [Metric.mem_ball,dist_self] using hr
  have hkp : k (coordinates c p) = coordinates d p := Filter.EventuallyEq.eq_of_nhds hagree
  have hksub : k '' (Q ∩ k.source) ⊆ coordinates d '' C := by
    rintro z ⟨y,⟨hyQ,hys⟩,rfl⟩
    have hys' := (Set.ext_iff.mp hks y).mp hys
    have hyimage : y ∈ coordinates c '' (C ∩ c.source) := by
      rw [hchamber]
      exact ⟨hyQ,hys'.2.2⟩
    obtain ⟨x,⟨hxC,hxc⟩,hxy⟩ := hyimage
    have hxU₁ : x ∈ U₁ := (hWmem x hxc).mp (hxy ▸ hys'.2.1)
    refine ⟨x,hxC,?_⟩
    change coordinates d x = j y
    rw [← hxy]
    exact (hUsub hxU₁.1.1).symm
  let U₂ := U₁ ∩ (c.source ∩ coordinates c ⁻¹' k.source)
  have hU₂ : IsOpen U₂ := hU₁.inter (c.isOpen_inter_preimage
    (k.open_source.preimage (toPlane.continuous.comp continuous_subtype_val)))
  have hpU₂ : p ∈ U₂ := ⟨hpU₁,hpc,hpk⟩
  obtain ⟨V,hV,hVmem⟩ := exists_ambient_open_coordinates d U₂ hU₂
    (fun x hx => hx.1.2)
  refine ⟨k,V,hV,(hVmem p hpd).mpr hpU₂,?_,?_⟩
  · rw [← hkp]
    exact k.map_source hpk
  · apply Set.Subset.antisymm
    · rintro z ⟨⟨x,hxC,hxz⟩,hzV⟩
      have hxd : x ∈ d.source := hCd hxC
      have hxU₂ : x ∈ U₂ := (hVmem x hxd).mp (hxz ▸ hzV)
      have hximage : coordinates c x ∈ Q ∩ Metric.ball (coordinates c p) r := by
        rw [← hchamber]
        exact mem_image_of_mem _ ⟨hxC,hxU₂.2.1⟩
      refine ⟨⟨coordinates c x,⟨hximage.1,hxU₂.2.2⟩,?_⟩,hzV⟩
      change j (coordinates c x) = z
      exact (hUsub hxU₂.1.1.1).trans hxz
    · rintro z ⟨hzimage,hzV⟩
      exact ⟨hksub hzimage,hzV⟩

end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction

/-- The local full-plane chamber image transfers between any two actual
charts in the original maximal atlas, including at original boundary points. -/
theorem local_image_of_actual_charts
    {X : Type*} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X)
    (c d : ModelChart 2 kind X) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (C : Set X) (Q : Set Plane)
    (hCd : C ⊆ d.source) {p : X} (hpc : p ∈ c.source) (hpd : p ∈ d.source)
    (r : ℝ) (hr : 0 < r)
    (hchamber : coordinates c '' (C ∩ c.source) = Q ∩ Metric.ball (coordinates c p) r) :
    ∃ (k : OpenPartialHomeomorph Plane Plane) (V : Set Plane),
      IsOpen V ∧ coordinates d p ∈ V ∧ coordinates d p ∈ k.target ∧
      (coordinates d '' C) ∩ V = (k '' (Q ∩ k.source)) ∩ V := by
  obtain ⟨j,hpj,hagree,_⟩ := ambient_chart_transition S c d hc hd p hpc hpd
  let jP := (toPlane.symm.toHomeomorph.transOpenPartialHomeomorph j).transHomeomorph
    toPlane.toHomeomorph
  have hpjP : coordinates c p ∈ jP.source := by
    change toPlane.symm (coordinates c p) ∈ j.source
    simpa only [coordinates,toPlane.symm_apply_apply] using hpj
  have hagreeP : ∀ᶠ x in 𝓝 p, jP (coordinates c x) = coordinates d x := by
    filter_upwards [hagree] with x hx
    change toPlane (j (toPlane.symm (coordinates c x))) = toPlane (d x).val
    rw [show toPlane.symm (coordinates c x) = (c x).val from toPlane.symm_apply_apply _]
    exact congrArg toPlane hx
  exact local_image_of_chart_germ c d C Q hCd hpc hpd r hr hchamber jP hpjP hagreeP

theorem oneSided_at_of_original_chamber
    {X : Type*} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X)
    (c d : ModelChart 2 kind X) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (C : Set X) (Q : Set Plane)
    (hCd : C ⊆ d.source) {p : X} (hpc : p ∈ c.source) (hpd : p ∈ d.source)
    (r : ℝ) (hr : 0 < r)
    (hchamber : coordinates c '' (C ∩ c.source) = Q ∩ Metric.ball (coordinates c p) r)
    (hQ : IsOpen Q) (hside : P202Specs.PlanarRegionTopology.LocallyOneSided Q)
    (hDomain : IsOpen (coordinates d '' C))
    (hpfront : coordinates d p ∈ frontier (coordinates d '' C))
    (O : Set Plane) (hO : IsOpen O) (hpO : coordinates d p ∈ O) :
    ∃ N : Set Plane, IsOpen N ∧ coordinates d p ∈ N ∧ N ⊆ O ∧
      IsConnected (N ∩ (coordinates d '' C)) ∧
      IsConnected (N \ closure (coordinates d '' C)) := by
  obtain ⟨k,V,hV,hpV,hpt,heq⟩ := local_image_of_actual_charts S c d hc hd C Q hCd hpc hpd r hr hchamber
  exact PlaneSectors.oneSided_at_of_local_image k Q (coordinates d '' C) V
    hQ hDomain hV heq hside hpt hpV hpfront O hO hpO

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction
open P202Specs.PlanarRegionTopology

namespace PlaneSectors

theorem locallyOneSided_translated_signedOrthant (A : Set (Fin 2))
    (s : Fin 2 → Bool) (b : Plane) :
    LocallyOneSided {z : Plane | z-b ∈ signedOrthant A s} := by
  exact locallyOneSided_preimage (Homeomorph.subRight b) (signedOrthant A s)
    (locallyOneSided_signedOrthant A s)

end PlaneSectors

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.PlaneSectors

theorem open_translated_signedOrthant (J : Set (Fin 2)) (τ : Fin 2 → Bool) (b : Plane) :
    IsOpen {z : Plane | z-b ∈ signedOrthant J τ} := by
  have horth : IsOpen (signedOrthant J τ) := by
    rw [signedOrthant_eq_preimage]
    exact (open_positiveOrthant J).preimage (signHomeomorph τ).continuous
  exact horth.preimage (continuous_id.sub continuous_const)

end P202.SurfaceRegionConstruction.PlaneSectors

namespace P202.SurfaceRegionConstruction
open Arrangement

/-- Every actual original complementary component is locally one-sided in
the full ambient plane of any original smooth chart containing its closure.
Seam points are included by the complete signed-orthant coordinate equality. -/
theorem arrangement_component_locallyOneSided
    {X : Type u} [TopologicalSpace X] {kind : ModelKind} [CompactSpace X]
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (a : ConnectedComponents ((P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      arrangementCarrier T)ᶜ : Set X))
    (d : ModelChart 2 kind X) (hd : d ∈ S.smoothStructure.val)
    (hclosure : closure (componentSet
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)ᶜ a) ⊆
        d.source) :
    P202Specs.PlanarRegionTopology.LocallyOneSided
      (coordinates d '' componentSet
        (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)ᶜ a) := by
  let := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  let G := f ⁻¹' arrangementCarrier T
  let C := componentSet Gᶜ a
  have hG : IsClosed G := (Arrangement.isClosed_carrier T).preimage
    (D.copy_closedEmbedding s).continuous
  have hC : IsOpen C := Components.isOpen Gᶜ hG.isOpen_compl a
  have hcompact : IsCompact (closure C) := isClosed_closure.isCompact
  have hmiss : Disjoint C (intrinsicBoundary S) := Set.disjoint_left.mpr (by
    intro x hx hxb
    exact Components.subset Gᶜ a hx
      (intrinsicBoundary_subset_restricted_arrangement S D s hB T hxb))
  have hDomain : IsOpen (coordinates d '' C) :=
    isOpen_coordinate_image_away_boundary S d hd hC (subset_closure.trans hclosure) hmiss
  have hfront : frontier (coordinates d '' C) = coordinates d '' frontier C :=
    frontier_coordinate_image_away_boundary S d hd hC hcompact hclosure hmiss
  intro z hz O hO hzO
  obtain ⟨p,hpfront,hpz⟩ := (Set.ext_iff.mp hfront z).mp hz
  have hpc : p ∈ closure C := frontier_subset_closure hpfront
  have hpd : p ∈ d.source := hclosure hpc
  obtain ⟨F⟩ := T.normal_forms (f p) univ isOpen_univ (mem_univ _)
  obtain ⟨c,J,τ,hc,hcs,hpcsource,hball,hchamber,hmodel⟩ :=
    normal_copy_incident_chamber S D s hB T F a hpc
  have hpfront' : coordinates d p ∈ frontier (coordinates d '' C) := hpz ▸ hz
  have hpO : coordinates d p ∈ O := hpz ▸ hzO
  have hout := oneSided_at_of_original_chamber S c d hc hd C
    {w | w-coordinates c p ∈ PlaneSectors.signedOrthant J τ}
    (subset_closure.trans hclosure) hpcsource hpd F.radius F.radius_pos hchamber
    (PlaneSectors.open_translated_signedOrthant J τ (coordinates c p))
    (PlaneSectors.locallyOneSided_translated_signedOrthant J τ (coordinates c p))
    hDomain hpfront' O hO hpO
  simpa only [hpz] using hout

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction

/-- Coordinate-domain properties and full-plane one-sidedness of every actual
graph complementary component, in any containing original smooth chart. -/
theorem regionalLocalOneSidedness : Expected.regionalLocalOneSidedness.{u} := by
  intro kind M _ _ S D s A B hB T H a e he hsource
  let C := componentSet H.graph.carrierᶜ a
  have hC : IsOpen C := H.open_components a
  have hconn : IsConnected C := H.connected_components a
  have hcpt : IsCompact (closure C) := H.compact_closures a
  have hmiss : Disjoint C (intrinsicBoundary S) :=
    Set.disjoint_left.mpr (fun x hx hxb =>
      Components.subset H.graph.carrierᶜ a hx (H.contains_boundary hxb))
  have hopen : IsOpen (coordinates e '' C) :=
    isOpen_coordinate_image_away_boundary S e he hC (subset_closure.trans hsource) hmiss
  have hcoordconn : IsConnected (coordinates e '' C) :=
    hconn.image _ ((continuousOn_coordinates e).mono (subset_closure.trans hsource))
  have hcl : closure (coordinates e '' C) = coordinates e '' closure C :=
    closure_coordinate_image e hcpt hsource
  have hfront : frontier (coordinates e '' C) = coordinates e '' frontier C :=
    frontier_coordinate_image_away_boundary S e he hC hcpt hsource hmiss
  refine ⟨hcoordconn.nonempty, hopen, hcoordconn, ?_, hcl, hfront, ?_, ?_⟩
  · rw [hcl]
    exact hcpt.image_of_continuousOn ((continuousOn_coordinates e).mono hsource)
  · rw [hfront]
    exact (H.nonempty_frontiers a).image _
  · have hside := arrangement_component_locallyOneSided S D s hB T
    rw [← H.carrier_eq] at hside
    exact hside a e he hsource

end P202.SurfaceRegionConstruction
