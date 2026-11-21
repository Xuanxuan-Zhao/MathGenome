import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RegionalBoundaryCycles
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ArrangementGraphGeometry
import Mathlib.Topology.Subpath
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Regional boundary-cycle construction for paper.tex 5061–5074.
Whole-edge saturation and the actual occupied sign chamber give finite regional
boundary graphs with exactly two endpoint incidences at every vertex. Their
simple disjoint cyclic traversals are realized by the original regular edges,
including all closing germs, in every original chart containing the region.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BoundaryData
open P202Specs.PlanarRegionTopology
open P202Specs.SurfaceRegionConstruction
universe u v

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {X : Type u} [TopologicalSpace X]

/-- Closing a genuine interval parametrization by identifying its endpoints. -/
def closeInterval (c : C(unitInterval, X)) (h : c 0 = c 1) : C(ParameterCircle, X) :=
  ⟨AddCircle.liftIco 1 0 (IccExtend zero_le_one c),
    AddCircle.liftIco_zero_continuous
      (by simpa using h) c.continuous.Icc_extend'.continuousOn⟩

theorem closeInterval_apply (c : C(unitInterval, X)) (h : c 0 = c 1)
    (t : unitInterval) : closeInterval c h (t : ℝ) = c t := by
  by_cases ht : (t : ℝ) < 1
  · exact (AddCircle.liftIco_zero_coe_apply ⟨t.property.1, ht⟩).trans (IccExtend_of_mem _ _ t.property)
  · have ht' : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
    subst t
    change AddCircle.liftIco 1 0 (IccExtend zero_le_one c) (↑(1 : ℝ)) = _
    simpa only [AddCircle.coe_period, ← AddCircle.coe_zero, zero_add,
      AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 1)] using (IccExtend_of_mem zero_le_one c (by norm_num : (0 : ℝ) ∈ Icc 0 1)).trans h

theorem closeInterval_range (c : C(unitInterval, X)) (h : c 0 = c 1) :
    range (closeInterval c h) = range c := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    let t := AddCircle.equivIco (1 : ℝ) 0 z
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := by simpa using t.property.2.le
    refine ⟨⟨t, ht0, ht1⟩, ?_⟩
    have hz : ((t : ℝ) : ParameterCircle) = z := AddCircle.coe_equivIco
    rw [← hz]
    exact (closeInterval_apply c h ⟨t, ht0, ht1⟩).symm
  · rintro ⟨t, rfl⟩
    exact ⟨(t : ℝ), closeInterval_apply c h t⟩

theorem closeInterval_injective (c : C(unitInterval, X)) (h : c 0 = c 1)
    (hinj : Set.InjOn c {t | (t : ℝ) < 1}) :
    Function.Injective (closeInterval c h) := by
  intro z w hzw
  let t := AddCircle.equivIco (1 : ℝ) 0 z
  let q := AddCircle.equivIco (1 : ℝ) 0 w
  have ht : ((t : ℝ) : ParameterCircle) = z := AddCircle.coe_equivIco
  have hq : ((q : ℝ) : ParameterCircle) = w := AddCircle.coe_equivIco
  have heq : c ⟨t, t.property.1, by simpa using t.property.2.le⟩ =
      c ⟨q, q.property.1, by simpa using q.property.2.le⟩ := by
    calc
      _ = closeInterval c h (t : ℝ) := (closeInterval_apply c h ⟨t, t.property.1, by simpa using t.property.2.le⟩).symm
      _ = closeInterval c h (q : ℝ) := by rwa [ht, hq]
      _ = _ := closeInterval_apply c h ⟨q, q.property.1, by simpa using q.property.2.le⟩
  have hreal : (t : ℝ) = q := congrArg (fun r : unitInterval => (r : ℝ))
    (hinj (by change (t : ℝ) < 1; simpa using t.property.2)
      (by change (q : ℝ) < 1; simpa using q.property.2) heq)
  exact ht.symm.trans ((congrArg (fun r : ℝ => (r : ParameterCircle)) hreal).trans hq)

/-- The local analytic predicate on a real interval before closing its ends. -/
def RegularJoinAt (f : ℝ → Plane) (t : ℝ) : Prop :=
  ∃ (δ : ℝ) (l r : ℝ → Plane), 0 < δ ∧
    ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)) ∧
    ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)) ∧
    EqOn l f (Icc (t - δ) t) ∧ EqOn r f (Icc t (t + δ)) ∧
    deriv l t ≠ 0 ∧ deriv r t ≠ 0 ∧
    NormedSpace.normalize (deriv l t) ≠ -NormedSpace.normalize (deriv r t)

theorem RegularJoinAt.congr {f g : ℝ → Plane} {t : ℝ}
    (h : RegularJoinAt f t) (heq : f =ᶠ[𝓝 t] g) : RegularJoinAt g t := by
  obtain ⟨δ,l,r,hδ,hl,hr,hel,her,hnl,hnr,hn⟩ := h
  obtain ⟨ε,hε,hnear⟩ := Metric.eventually_nhds_iff.mp heq
  let η := min δ (ε / 2)
  have hη : 0 < η := lt_min hδ (by linarith)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηε : η < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have heq' : ∀ x ∈ Icc (t - η) (t + η), f x = g x := by
    intro x hx
    apply hnear
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  refine ⟨η,l,r,hη,hl.mono ?_,hr.mono ?_,?_,?_,hnl,hnr,hn⟩
  · intro x hx; constructor <;> linarith [hx.1,hx.2]
  · intro x hx; constructor <;> linarith [hx.1,hx.2]
  · intro x hx
    exact (hel (by constructor <;> linarith [hx.1,hx.2])).trans
      (heq' x ⟨hx.1,by linarith [hx.2]⟩)
  · intro x hx
    exact (her (by constructor <;> linarith [hx.1,hx.2])).trans
      (heq' x ⟨by linarith [hx.1],hx.2⟩)

theorem RegularJoinAt.translate {f : ℝ → Plane} {s t a : ℝ}
    (h : RegularJoinAt f s) (ha : t + a = s) :
    RegularJoinAt (fun x => f (x + a)) t := by
  obtain ⟨δ,l,r,hδ,hl,hr,hel,her,hnl,hnr,hn⟩ := h
  have hmap : MapsTo (fun x : ℝ => x + a) (Ioo (t - δ) (t + δ))
      (Ioo (s - δ) (s + δ)) := by
    intro x hx; constructor <;> linarith [hx.1,hx.2]
  have hderiv (F : ℝ → Plane) : deriv (fun x => F (x + a)) t = deriv F s := by
    rw [deriv_comp_add_const,ha]
  refine ⟨δ,(fun x => l (x+a)),(fun x => r (x+a)),hδ,
    hl.comp (by fun_prop) hmap,hr.comp (by fun_prop) hmap,?_,?_,?_,?_,?_⟩
  · intro x hx; apply hel; constructor <;> linarith [hx.1,hx.2]
  · intro x hx; apply her; constructor <;> linarith [hx.1,hx.2]
  · simpa only [hderiv] using hnl
  · simpa only [hderiv] using hnr
  · simpa only [hderiv] using hn

theorem closeInterval_realLift_eq (c : C(unitInterval, Plane)) (h : c 0 = c 1)
    {x s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (heq : (s : ParameterCircle) = x) :
    realLift (closeInterval c h) x = IccExtend zero_le_one c s := by
  rw [realLift, ← heq]
  exact (closeInterval_apply c h ⟨s, hs⟩).trans (IccExtend_of_mem _ _ hs).symm

theorem closeInterval_eventuallyEq (c : C(unitInterval, Plane)) (h : c 0 = c 1)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (heq : (s : ParameterCircle) = t) :
    realLift (closeInterval c h) =ᶠ[𝓝 t]
      (fun x => IccExtend zero_le_one c (x + (s - t))) := by
  have ht : t + (s - t) ∈ Ioo (0 : ℝ) 1 := by simpa using hs
  have hnear := (show Continuous (fun x : ℝ => x + (s-t)) by fun_prop).continuousAt.preimage_mem_nhds
    (isOpen_Ioo.mem_nhds ht)
  filter_upwards [hnear] with x hx
  apply closeInterval_realLift_eq c h ⟨hx.1.le,hx.2.le⟩
  rw [AddCircle.coe_add,AddCircle.coe_sub,heq]
  abel

/-- Terminal and initial one-sided smooth extensions have compatible directed
unit tangents when the two endpoints are identified. -/
def RegularClosingGerms (f : ℝ → Plane) : Prop :=
  ∃ (δ : ℝ) (l r : ℝ → Plane), 0 < δ ∧
    ContDiffOn ℝ ∞ l (Ioo (1 - δ) (1 + δ)) ∧
    ContDiffOn ℝ ∞ r (Ioo (-δ) δ) ∧
    EqOn l f (Icc (1 - δ) 1) ∧ EqOn r f (Icc 0 δ) ∧
    deriv l 1 ≠ 0 ∧ deriv r 0 ≠ 0 ∧
    NormedSpace.normalize (deriv l 1) ≠ -NormedSpace.normalize (deriv r 0)

theorem closeInterval_regular_at_zero (c : C(unitInterval, Plane)) (h : c 0 = c 1)
    (hg : RegularClosingGerms (IccExtend zero_le_one c)) :
    RegularJoinAt (realLift (closeInterval c h)) 0 := by
  obtain ⟨δ,l,r,hδ,hl,hr,hel,her,hnl,hnr,hn⟩ := hg
  let η : ℝ := min δ (1/2)
  have hη : 0 < η := lt_min hδ (by norm_num)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηone : η ≤ 1/2 := min_le_right _ _
  have hl' : ContDiffOn ℝ ∞ (fun x => l (x+1)) (Ioo (-η) η) := by
    apply hl.comp (by fun_prop)
    intro x hx; constructor <;> linarith [hx.1,hx.2]
  have hr' : ContDiffOn ℝ ∞ r (Ioo (-η) η) := by
    apply hr.mono
    intro x hx; constructor <;> linarith [hx.1,hx.2]
  refine ⟨η,(fun x => l (x+1)),r,hη,?_,?_,?_,?_,?_,hnr,?_⟩
  · simpa using hl'
  · simpa using hr'
  · intro x hx
    have hleft : x + 1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hx.1,hx.2]
    exact (hel (by constructor <;> linarith [hx.1,hx.2])).trans
      (closeInterval_realLift_eq c h hleft (by
        rw [AddCircle.coe_add,AddCircle.coe_period,add_zero])).symm
  · intro x hx
    have hright : x ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hx.1,hx.2]
    exact (her ⟨hx.1,by linarith [hx.2]⟩).trans
      (closeInterval_realLift_eq c h hright rfl).symm
  · simpa only [deriv_comp_add_const,zero_add] using hnl
  · simpa only [deriv_comp_add_const,zero_add] using hn

theorem closeInterval_regular_at_integer (c : C(unitInterval, Plane)) (h : c 0 = c 1)
    (hg : RegularClosingGerms (IccExtend zero_le_one c)) (t : ℝ)
    (ht : (t : ParameterCircle) = 0) :
    RegularJoinAt (realLift (closeInterval c h)) t := by
  have h0 := closeInterval_regular_at_zero c h hg
  apply (h0.translate (t := t) (a := -t) (by ring)).congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [realLift,AddCircle.coe_add,AddCircle.coe_neg,ht,neg_zero,add_zero]

/-- A closed interval with finitely many regular noncuspidal interior joins
and a regular noncuspidal closing join determines a genuine shared Jordan
curve over R/Z. This transports *all* real parameters, including the seam.
It does not assume any Jordan parametrization or boundary-curve conclusion. -/
def regularJordanCurveOfInterval (c : C(unitInterval, Plane)) (h : c 0 = c 1)
    (hinj : Set.InjOn c {t | (t : ℝ) < 1}) (J : Finset ℝ)
    (hsm : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ J →
      ContDiffAt ℝ ∞ (IccExtend zero_le_one c) s)
    (hjoin : ∀ s ∈ Ioo (0 : ℝ) 1, RegularJoinAt (IccExtend zero_le_one c) s)
    (hclosing : RegularClosingGerms (IccExtend zero_le_one c)) : RegularJordanCurve where
  parametrization := closeInterval c h
  injective := closeInterval_injective c h hinj
  joins := insert 0 (J.image (fun s : ℝ => (s : ParameterCircle)))
  smooth_off_joins := by
    intro t ht
    let s := AddCircle.equivIco (1 : ℝ) 0 (t : ParameterCircle)
    have hs0 : 0 ≤ (s : ℝ) := s.property.1
    have hs1 : (s : ℝ) < 1 := by simpa using s.property.2
    have hscoe : ((s : ℝ) : ParameterCircle) = t := AddCircle.coe_equivIco
    have hspos : 0 < (s : ℝ) := by
      by_contra hn
      have hs : (s : ℝ) = 0 := le_antisymm (le_of_not_gt hn) hs0
      have ht0 : (t : ParameterCircle) = 0 := by rw [← hscoe,hs,AddCircle.coe_zero]
      exact ht (by simp [ht0])
    have hsJ : (s : ℝ) ∉ J := by
      intro hs
      apply ht
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨s,hs,hscoe⟩
    have hsm' : ContDiffAt ℝ ∞ (fun x => IccExtend zero_le_one c (x + ((s : ℝ)-t))) t := by
      have hh : ContDiffAt ℝ ∞ (IccExtend zero_le_one c) (t + ((s : ℝ)-t)) := by
        convert hsm s ⟨hspos,hs1⟩ hsJ using 1; ring
      exact ContDiffAt.comp (g := IccExtend zero_le_one c)
        (f := fun x : ℝ => x + ((s : ℝ)-t)) t hh (by fun_prop)
    exact hsm'.congr_of_eventuallyEq (closeInterval_eventuallyEq c h ⟨hspos,hs1⟩ hscoe)
  regular_joins := by
    intro t
    change RegularJoinAt (realLift (closeInterval c h)) t
    let s := AddCircle.equivIco (1 : ℝ) 0 (t : ParameterCircle)
    have hs0 : 0 ≤ (s : ℝ) := s.property.1
    have hs1 : (s : ℝ) < 1 := by simpa using s.property.2
    have hscoe : ((s : ℝ) : ParameterCircle) = t := AddCircle.coe_equivIco
    by_cases hs : (s : ℝ) = 0
    · apply closeInterval_regular_at_integer c h hclosing t
      rw [← hscoe,hs,AddCircle.coe_zero]
    · have hspos : 0 < (s : ℝ) := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hh := (hjoin s ⟨hspos,hs1⟩).translate
        (t := t) (a := (s : ℝ)-t) (by ring)
      exact hh.congr (closeInterval_eventuallyEq c h ⟨hspos,hs1⟩ hscoe).symm

theorem regularJordanCurveOfInterval_trace (c : C(unitInterval, Plane)) (h : c 0 = c 1)
    (hinj : Set.InjOn c {t | (t : ℝ) < 1}) (J : Finset ℝ) (hsm hjoin hclosing) :
    (regularJordanCurveOfInterval c h hinj J hsm hjoin hclosing).trace = range c :=
  closeInterval_range c h

theorem normalize_ne_neg_self {u : Plane} (hu : u ≠ 0) :
    NormedSpace.normalize u ≠ -NormedSpace.normalize u := by
  intro heq
  have hz : (2 : ℝ) • NormedSpace.normalize u = 0 := by
    rw [two_smul]
    nth_rw 2 [heq]
    exact add_neg_cancel _
  have hz' : NormedSpace.normalize u = 0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  exact hu ((NormedSpace.normalize_eq_zero_iff u).mp hz')

/-- Independent crossing tangents remain noncuspidal in either directed
orientation. Positive changes of edge speed do not affect the assertion. -/
theorem normalize_ne_neg_of_independent {u v : Plane}
    (hlin : LinearIndependent ℝ ![u,v]) :
    NormedSpace.normalize u ≠ -NormedSpace.normalize v := by
  have hu : u ≠ 0 := hlin.ne_zero 0
  intro heq
  apply (LinearIndependent.pair_iff' hu).mp hlin (-‖v‖ / ‖u‖)
  calc
    (-‖v‖ / ‖u‖) • u = -(‖v‖ • NormedSpace.normalize u) := by
      simp [NormedSpace.normalize,div_eq_mul_inv,smul_smul]
    _ = ‖v‖ • NormedSpace.normalize v := by rw [heq,smul_neg,neg_neg]
    _ = v := NormedSpace.norm_smul_normalize v

/-- A smooth regular segment contributes no corner to a concatenation. -/
theorem RegularJoinAt.of_contDiffOn {f : ℝ → Plane} {a t b : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo a b)) (ht : t ∈ Ioo a b)
    (hderiv : deriv f t ≠ 0) : RegularJoinAt f t := by
  let δ := min (t-a) (b-t) / 2
  have hδ : 0 < δ := div_pos (lt_min (by linarith [ht.1]) (by linarith [ht.2])) (by norm_num)
  have hδa : δ < t-a := by
    have := min_le_left (t-a) (b-t)
    dsimp [δ]
    linarith [ht.1]
  have hδb : δ < b-t := by
    have := min_le_right (t-a) (b-t)
    dsimp [δ]
    linarith [ht.2]
  have hsub : Ioo (t-δ) (t+δ) ⊆ Ioo a b := by
    intro x hx; constructor <;> linarith [hx.1,hx.2]
  exact ⟨δ,f,f,hδ,hf.mono hsub,hf.mono hsub,fun _ _ => rfl,fun _ _ => rfl,
    hderiv,hderiv,normalize_ne_neg_self hderiv⟩

/-- Special case for an untouched smooth closed curve cut at one point. -/
def regularJordanCurveOfSmoothInterval (c : C(unitInterval, Plane)) (h : c 0 = c 1)
    (hinj : Set.InjOn c {t | (t : ℝ) < 1})
    (hsm : ContDiffOn ℝ ∞ (IccExtend zero_le_one c) (Ioo (0 : ℝ) 1))
    (hreg : ∀ t ∈ Ioo (0 : ℝ) 1, deriv (IccExtend zero_le_one c) t ≠ 0)
    (hclosing : RegularClosingGerms (IccExtend zero_le_one c)) : RegularJordanCurve :=
  regularJordanCurveOfInterval c h hinj ∅
    (fun _t ht _ => hsm.contDiffAt (isOpen_Ioo.mem_nhds ht))
    (fun t ht => RegularJoinAt.of_contDiffOn hsm ht (hreg t ht)) hclosing

/-- Open-interval simplicity plus avoidance of the starting point is exactly
what the endpoint-identification map needs for injectivity. -/
theorem injOn_halfOpen_of_open_injective (c : C(unitInterval, X))
    (hinj : Set.InjOn c {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1})
    (havoid : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → c t ≠ c 0) :
    Set.InjOn c {t | (t : ℝ) < 1} := by
  intro t ht q hq heq
  by_cases ht0 : t = 0
  · subst t
    by_contra hq0
    have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (by
      intro hh; exact hq0 (Subtype.ext hh))
    exact havoid q hqpos hq heq.symm
  · by_cases hq0 : q = 0
    · subst q
      have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
        intro hh; exact ht0 (Subtype.ext hh.symm))
      exact False.elim (havoid t htpos ht heq)
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
        intro hh; exact ht0 (Subtype.ext hh.symm))
      have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (by
        intro hh; exact hq0 (Subtype.ext hh.symm))
      exact hinj ⟨htpos,ht⟩ ⟨hqpos,hq⟩ heq

/-- A self-loop of the actual finite embedded graph has a genuine injective
circle parametrization whose image is exactly that edge, including its vertex.
No graph-degree or regional-cycle assertion is assumed here. -/
theorem embeddedGraph_loop_circle {kind : SmoothManifolds.ModelKind}
    {S : SmoothManifolds.AtlasData.SmoothManifold 2 kind X}
    (G : P202Specs.SurfaceRegionConstruction.EmbeddedGraph S) (i : Fin G.edgeCount)
    (hi : G.initial i = G.terminal i) :
    ∃ c : C(ParameterCircle, X), Function.Injective c ∧ range c = range (G.edge i) := by
  have hclose : G.edge i 0 = G.edge i 1 := by rw [G.at_zero,G.at_one,hi]
  have havoid : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      G.edge i t ≠ G.edge i 0 := by
    intro t ht ht' heq
    apply G.avoids_vertices i t ht ht'
    exact ⟨G.initial i, (G.at_zero i).symm.trans heq.symm⟩
  have hinj := injOn_halfOpen_of_open_injective (G.edge i) (G.open_injective i) havoid
  exact ⟨closeInterval (G.edge i) hclose, closeInterval_injective _ _ hinj,
    closeInterval_range _ _⟩

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {V : Type u} {E : Type v}

/-- Endpoint darts count a loop twice, as required by degree two. -/
def endpoint (initial terminal : E → V) (d : E × Bool) : V :=
  if d.2 then terminal d.1 else initial d.1

def incidences (initial terminal : E → V) (p : V) : Set (E × Bool) :=
  {d | endpoint initial terminal d = p}

/-- Replace every edge by three pieces. The two artificial vertices keep
self-loops and multiple original edges distinct in a genuine simple graph. -/
def doubleSubdivision (initial terminal : E → V) : SimpleGraph (V ⊕ (E × Bool)) where
  Adj
    | Sum.inl _, Sum.inl _ => False
    | Sum.inl p, Sum.inr d => endpoint initial terminal d = p
    | Sum.inr d, Sum.inl p => endpoint initial terminal d = p
    | Sum.inr d, Sum.inr e => d.1 = e.1 ∧ d.2 ≠ e.2
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by
    intro x
    cases x
    · exact id
    · exact fun h => h.2 rfl⟩

theorem doubleSubdivision_neighbors_original (initial terminal : E → V) (p : V) :
    (doubleSubdivision initial terminal).neighborSet (Sum.inl p) =
      Sum.inr '' incidences initial terminal p := by
  ext x
  cases x with
  | inl q => simp [SimpleGraph.mem_neighborSet,doubleSubdivision]
  | inr d => simp [SimpleGraph.mem_neighborSet,doubleSubdivision,incidences]

theorem doubleSubdivision_neighbors_artificial (initial terminal : E → V) (d : E × Bool) :
    (doubleSubdivision initial terminal).neighborSet (Sum.inr d) =
      {Sum.inl (endpoint initial terminal d), Sum.inr (d.1, !d.2)} := by
  rcases d with ⟨e,b⟩
  cases b <;> ext x <;> cases x with
  | inl p =>
      change endpoint initial terminal _ = p ↔ _
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sum.inl.injEq,Sum.inl_ne_inr,or_false]
      exact eq_comm
  | inr d =>
      rcases d with ⟨f,c⟩
      cases c <;> simp only [SimpleGraph.mem_neighborSet,doubleSubdivision,
        Set.mem_insert_iff,Set.mem_singleton_iff,Sum.inr_ne_inl,false_or,
        Sum.inr.injEq,Prod.mk.injEq,Bool.false_eq_true,Bool.true_eq_false,
        Bool.not_true,Bool.not_false,
        and_true,and_false]
      all_goals simp only [ne_eq,eq_self,not_true_eq_false,
        Bool.false_eq_true,not_false_eq_true,and_false,and_true,eq_comm]

/-- The degree-two multigraph condition is converted to the exact Mathlib
simple-graph cycle condition, including original loops and multiple edges. -/
theorem doubleSubdivision_isCycles [Finite E] (initial terminal : E → V)
    (hdegree : ∀ p, (incidences initial terminal p).Nonempty →
      (incidences initial terminal p).ncard = 2) :
    (doubleSubdivision initial terminal).IsCycles := by
  intro x hx
  cases x with
  | inl p =>
    rw [doubleSubdivision_neighbors_original] at hx ⊢
    rw [Set.ncard_image_of_injective _ Sum.inr_injective]
    exact hdegree p (Set.image_nonempty.mp hx)
  | inr d =>
    rw [doubleSubdivision_neighbors_artificial]
    exact Set.ncard_pair (Sum.inl_ne_inr)

theorem doubleSubdivision_component_cycle [Finite V] [Finite E]
    (initial terminal : E → V)
    (hdegree : ∀ p, (incidences initial terminal p).Nonempty →
      (incidences initial terminal p).ncard = 2)
    {c : (doubleSubdivision initial terminal).ConnectedComponent}
    {x : V ⊕ (E × Bool)} (hx : x ∈ c.supp)
    (hn : ((doubleSubdivision initial terminal).neighborSet x).Nonempty) :
    ∃ p : (doubleSubdivision initial terminal).Walk x x,
      p.IsCycle ∧ p.toSubgraph.verts = c.supp :=
  (doubleSubdivision_isCycles initial terminal hdegree).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hx hn

/-- A component carrying edges, excluding irrelevant isolated vertices. -/
def NonisolatedComponent {W : Type*} (G : SimpleGraph W) :=
  {c : G.ConnectedComponent // ∃ x ∈ c.supp, (G.neighborSet x).Nonempty}

/-- A genuine simple finite closed walk containing exactly its whole component. -/
structure ComponentCycle {W : Type*} (G : SimpleGraph W) (c : G.ConnectedComponent) where
  base : W
  walk : G.Walk base base
  simple : walk.IsCycle
  vertices : walk.toSubgraph.verts = c.supp

noncomputable def componentCycle {W : Type*} [Finite W] {G : SimpleGraph W}
    (h : G.IsCycles) (c : NonisolatedComponent G) : ComponentCycle G c.val := by
  classical
  apply Classical.choice
  obtain ⟨x,hx,hn⟩ := c.property
  obtain ⟨p,hp,hverts⟩ := h.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hx hn
  exact ⟨⟨x,p,hp,hverts⟩⟩

theorem componentCycle_adj {W : Type*} [Finite W] {G : SimpleGraph W}
    (h : G.IsCycles) (c : NonisolatedComponent G) (x y : W) :
    (componentCycle h c).walk.toSubgraph.Adj x y ↔ G.Adj x y ∧ x ∈ c.val.supp := by
  classical
  let : Fintype W := Fintype.ofFinite W
  let p := componentCycle h c
  constructor
  · intro hxy
    refine ⟨hxy.adj_sub,?_⟩
    rw [← p.vertices]
    exact p.walk.toSubgraph.edge_vert hxy
  · rintro ⟨hxy,hx⟩
    have hv : x ∈ p.walk.toSubgraph.verts := by rwa [p.vertices]
    exact (p.simple.adj_toSubgraph_iff_of_isCycles h hv y).mpr hxy

theorem componentCycle_pairwise_disjoint {W : Type*} [Finite W] {G : SimpleGraph W}
    (h : G.IsCycles) : Pairwise (fun c d : NonisolatedComponent G =>
      Disjoint (componentCycle h c).walk.toSubgraph.verts
        (componentCycle h d).walk.toSubgraph.verts) := by
  intro c d hcd
  rw [(componentCycle h c).vertices,(componentCycle h d).vertices]
  exact G.pairwise_disjoint_supp_connectedComponent (by
    intro heq; exact hcd (Subtype.ext heq))

/-- Every edge belongs to exactly one of the selected simple component cycles. -/
theorem componentCycle_edge_partition {W : Type*} [Finite W] {G : SimpleGraph W}
    (h : G.IsCycles) {x y : W} (hxy : G.Adj x y) :
    ∃! c : NonisolatedComponent G,
      (componentCycle h c).walk.toSubgraph.Adj x y := by
  let c : NonisolatedComponent G := ⟨G.connectedComponentMk x,
    x,SimpleGraph.ConnectedComponent.connectedComponentMk_mem,⟨y,hxy⟩⟩
  refine ⟨c,?_,?_⟩
  · exact (componentCycle_adj h c x y).mpr
      ⟨hxy,SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  · intro d hd
    apply Subtype.ext
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
      (componentCycle_adj h d x y |>.mp hd).2
      (show x ∈ c.val.supp from SimpleGraph.ConnectedComponent.connectedComponentMk_mem)

/-- Every original edge occurs in exactly one genuine simple cycle after the
necessary two subdivisions. No original simple-cycle conclusion is assumed. -/
theorem doubleSubdivision_original_edge_partition [Finite V] [Finite E]
    (initial terminal : E → V)
    (hdegree : ∀ p, (incidences initial terminal p).Nonempty →
      (incidences initial terminal p).ncard = 2) (e : E) :
    ∃! c : NonisolatedComponent (doubleSubdivision initial terminal),
      (componentCycle (doubleSubdivision_isCycles initial terminal hdegree) c).walk.toSubgraph.Adj (Sum.inr (e,false)) (Sum.inr (e,true)) := by
  apply componentCycle_edge_partition
  exact ⟨rfl,Bool.false_ne_true⟩

theorem finite_nonisolatedComponents {W : Type*} [Finite W] (G : SimpleGraph W) :
    Finite (NonisolatedComponent G) := by
  unfold NonisolatedComponent
  infer_instance

/-- An ordered finite simple cyclic vertex chain, in exactly the indexing
format needed by Path.concat. Vertices before the repeated endpoint are
injective, and each consecutive pair is an actual graph edge. -/
structure SimpleCyclicChain {W : Type*} (G : SimpleGraph W) where
  length : ℕ
  length_pos : 0 < length
  length_ge_three : 3 ≤ length
  vertex : Fin (length+1) → W
  closed : vertex 0 = vertex (Fin.last length)
  injective : Function.Injective (fun i : Fin length => vertex i.castSucc)
  adjacent : ∀ i : Fin length, G.Adj (vertex i.castSucc) (vertex i.succ)

def ComponentCycle.chain {W : Type*} {G : SimpleGraph W} {c : G.ConnectedComponent}
    (p : ComponentCycle G c) : SimpleCyclicChain G where
  length := p.walk.length
  length_pos := lt_of_lt_of_le (by norm_num : 0 < 3) p.simple.three_le_length
  length_ge_three := p.simple.three_le_length
  vertex := fun i => p.walk.getVert i.val
  closed := by simp
  injective := by
    intro i j hij
    apply Fin.ext
    exact p.simple.getVert_injOn' (by change i.val ≤ p.walk.length - 1; omega)
      (by change j.val ≤ p.walk.length - 1; omega) hij
  adjacent := fun i => p.walk.adj_getVert_succ i.isLt

theorem ComponentCycle.chain_vertices {W : Type*} {G : SimpleGraph W}
    {c : G.ConnectedComponent} (p : ComponentCycle G c) :
    range (fun i : Fin p.chain.length => p.chain.vertex i.castSucc) = c.supp := by
  rw [← p.vertices]
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact p.walk.mem_verts_toSubgraph.mpr (p.walk.getVert_mem_support i.val)
  · intro hx
    obtain ⟨n,hn,hle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (p.walk.mem_verts_toSubgraph.mp hx)
    by_cases hlt : n < p.walk.length
    · exact ⟨⟨n,hlt⟩,hn⟩
    · have heq : n = p.walk.length := Nat.le_antisymm hle (le_of_not_gt hlt)
      have hbase : p.base = x := by simpa only [heq,SimpleGraph.Walk.getVert_length] using hn
      exact ⟨⟨0,p.chain.length_pos⟩, by simpa [ComponentCycle.chain] using hbase⟩

theorem doubleSubdivision_cycle_contains_three_pieces [Finite V] [Finite E]
    (initial terminal : E → V)
    (hdegree : ∀ p, (incidences initial terminal p).Nonempty →
      (incidences initial terminal p).ncard = 2)
    (c : NonisolatedComponent (doubleSubdivision initial terminal)) (e : E) :
    let p := componentCycle (doubleSubdivision_isCycles initial terminal hdegree) c
    p.walk.toSubgraph.Adj (Sum.inr (e,false)) (Sum.inr (e,true)) ↔
      p.walk.toSubgraph.Adj (Sum.inl (initial e)) (Sum.inr (e,false)) ∧
      p.walk.toSubgraph.Adj (Sum.inr (e,false)) (Sum.inr (e,true)) ∧
      p.walk.toSubgraph.Adj (Sum.inr (e,true)) (Sum.inl (terminal e)) := by
  dsimp only
  let h := doubleSubdivision_isCycles initial terminal hdegree
  have hleft : (doubleSubdivision initial terminal).Adj
      (Sum.inl (initial e)) (Sum.inr (e,false)) := rfl
  have hmiddle : (doubleSubdivision initial terminal).Adj
      (Sum.inr (e,false)) (Sum.inr (e,true)) := ⟨rfl,Bool.false_ne_true⟩
  have hright : (doubleSubdivision initial terminal).Adj
      (Sum.inr (e,true)) (Sum.inl (terminal e)) := rfl
  constructor
  · intro hmid
    have hx := (componentCycle_adj h c _ _).mp hmid |>.2
    refine ⟨(componentCycle_adj h c _ _).mpr ⟨hleft,?_⟩,hmid,?_⟩
    · exact c.val.mem_supp_of_adj_mem_supp hx hleft.symm
    · apply (componentCycle_adj h c _ _).mpr
      exact ⟨hright,c.val.mem_supp_of_adj_mem_supp hx hmiddle⟩
  · exact fun hh => hh.2.1

/-- Nonempty original regional edge sets yield a nonempty finite collection
of the selected genuine simple closed chains. -/
theorem doubleSubdivision_nonempty_cycles [Nonempty E]
    (initial terminal : E → V) :
    Nonempty (NonisolatedComponent (doubleSubdivision initial terminal)) := by
  obtain ⟨e⟩ := ‹Nonempty E›
  refine ⟨⟨(doubleSubdivision initial terminal).connectedComponentMk (Sum.inr (e,false)),
    Sum.inr (e,false),SimpleGraph.ConnectedComponent.connectedComponentMk_mem,?_⟩⟩
  exact ⟨Sum.inr (e,true),rfl,Bool.false_ne_true⟩

def subdivisionParameter (b : Bool) : unitInterval :=
  if b then ⟨2/3,by norm_num,by norm_num⟩ else ⟨1/3,by norm_num,by norm_num⟩

theorem subdivisionParameter_pos (b : Bool) : 0 < (subdivisionParameter b : ℝ) := by
  cases b <;> norm_num [subdivisionParameter]

theorem subdivisionParameter_lt_one (b : Bool) : (subdivisionParameter b : ℝ) < 1 := by
  cases b <;> norm_num [subdivisionParameter]

theorem subdivisionParameter_injective : Function.Injective subdivisionParameter := by
  intro b c h
  cases b <;> cases c <;> try rfl
  all_goals
    have hh := congrArg (fun t : unitInterval => (t : ℝ)) h
    norm_num [subdivisionParameter] at hh

section Embedded
open P202Specs.SurfaceRegionConstruction
open SmoothManifolds.AtlasData
variable {M : Type*} [TopologicalSpace M] {kind : SmoothManifolds.ModelKind}
variable {S : SmoothManifold 2 kind M}

def subdivisionVertex (G : EmbeddedGraph S) :
    Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool) → M
  | Sum.inl v => G.vertex v
  | Sum.inr d => G.edge d.1 (subdivisionParameter d.2)

theorem subdivisionVertex_injective (G : EmbeddedGraph S) :
    Function.Injective (subdivisionVertex G) := by
  intro x y hxy
  cases x with
  | inl v =>
    cases y with
    | inl w => exact congrArg Sum.inl (G.vertex_injective hxy)
    | inr d =>
      exact False.elim ((G.avoids_vertices d.1 (subdivisionParameter d.2)
        (subdivisionParameter_pos _) (subdivisionParameter_lt_one _)) ⟨v,hxy⟩)
  | inr d =>
    cases y with
    | inl v =>
      exact False.elim ((G.avoids_vertices d.1 (subdivisionParameter d.2)
        (subdivisionParameter_pos _) (subdivisionParameter_lt_one _)) ⟨v,hxy.symm⟩)
    | inr e =>
      rcases d with ⟨d,b⟩
      rcases e with ⟨e,c⟩
      by_cases hde : d = e
      · subst e
        have hp := G.open_injective d
          ⟨subdivisionParameter_pos b,subdivisionParameter_lt_one b⟩
          ⟨subdivisionParameter_pos c,subdivisionParameter_lt_one c⟩ hxy
        have hbc := subdivisionParameter_injective hp
        subst c
        rfl
      · exact False.elim (Set.disjoint_left.mp (G.disjoint_open_edges hde)
          ⟨subdivisionParameter b,⟨subdivisionParameter_pos b,subdivisionParameter_lt_one b⟩,rfl⟩
          ⟨subdivisionParameter c,⟨subdivisionParameter_pos c,subdivisionParameter_lt_one c⟩,hxy.symm⟩)

def edgePath (G : EmbeddedGraph S) (e : Fin G.edgeCount) :
    Path (G.vertex (G.initial e)) (G.vertex (G.terminal e)) where
  toContinuousMap := G.edge e
  source' := G.at_zero e
  target' := G.at_one e

/-- Each adjacency of the subdivided combinatorial graph is realized by the
appropriate genuine subpath of an original embedded edge, in either direction. -/
def subdivisionPath (G : EmbeddedGraph S)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y) :
    Path (subdivisionVertex G x) (subdivisionVertex G y) := by
  cases x with
  | inl v =>
    cases y with
    | inl w => exact False.elim h
    | inr d =>
      rcases d with ⟨e,b⟩
      cases b
      · exact ((edgePath G e).subpath 0 (subdivisionParameter false)).cast
          (by simpa [subdivisionVertex,endpoint] using congrArg G.vertex (Eq.symm h))
          rfl
      · exact ((edgePath G e).subpath 1 (subdivisionParameter true)).cast
          (by simpa [subdivisionVertex,endpoint] using congrArg G.vertex (Eq.symm h))
          rfl
  | inr d =>
    cases y with
    | inl v =>
      rcases d with ⟨e,b⟩
      cases b
      · exact ((edgePath G e).subpath (subdivisionParameter false) 0).cast rfl
          (by simpa [subdivisionVertex,endpoint] using congrArg G.vertex (Eq.symm h))
      · exact ((edgePath G e).subpath (subdivisionParameter true) 1).cast rfl
          (by simpa [subdivisionVertex,endpoint] using congrArg G.vertex (Eq.symm h))
    | inr e =>
      rcases d with ⟨d,b⟩
      rcases e with ⟨e,c⟩
      have hde : d = e := h.1
      subst e
      exact (edgePath G d).subpath (subdivisionParameter b) (subdivisionParameter c)

end Embedded
section NonemptyConcatenation
variable {X : Type*} [TopologicalSpace X]

/-- A finite concatenation starting with the first actual edge. Mathlib's
Path.concat starts with a constant Path.refl and is unsuitable for injective
regular parametrizations because it leaves a constant initial time interval. -/
def concatenateNonempty : (n : ℕ) → 0 < n →
    (p : Fin (n+1) → X) → ((i : Fin n) → Path (p i.castSucc) (p i.succ)) →
      Path (p 0) (p (Fin.last n))
  | 0,hn,_,_ => False.elim (Nat.not_lt_zero _ hn)
  | 1,_,p,F => (F 0).cast rfl rfl
  | n+2,_,p,F =>
      (concatenateNonempty (n+1) (by omega) (p ∘ Fin.castSucc)
        (fun i => F i.castSucc)).trans (F (Fin.last (n+1)))

theorem concatenateNonempty_range (n : ℕ) (hn : 0 < n) (p : Fin (n+1) → X)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ)) :
    range (concatenateNonempty n hn p F) = ⋃ i, range (F i) := by
  match n with
  | 0 => exact False.elim (Nat.not_lt_zero _ hn)
  | 1 =>
    simp only [concatenateNonempty,Path.cast_coe]
    ext x
    constructor
    · intro hx; exact mem_iUnion.mpr ⟨0,hx⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      exact hi
  | n+2 =>
    rw [concatenateNonempty]
    erw [Path.trans_range]
    rw [concatenateNonempty_range]
    ext x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.castSucc,hi⟩
      · exact mem_iUnion.mpr ⟨Fin.last (n+1),hx⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      refine Fin.lastCases (fun hlast => Or.inr hlast)
        (fun j hj => Or.inl (mem_iUnion.mpr ⟨j,hj⟩)) i hi
termination_by n

end NonemptyConcatenation

section RealizedChain
open P202Specs.SurfaceRegionConstruction
open SmoothManifolds.AtlasData
variable {M : Type*} [TopologicalSpace M] {kind : SmoothManifolds.ModelKind}
variable {S : SmoothManifold 2 kind M}

def realizedCyclePath (G : EmbeddedGraph S)
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal)) :
    Path (subdivisionVertex G (c.vertex 0))
      (subdivisionVertex G (c.vertex (Fin.last c.length))) :=
  concatenateNonempty c.length c.length_pos (subdivisionVertex G ∘ c.vertex)
    (fun i => subdivisionPath G (c.adjacent i))

theorem realizedCyclePath_closed (G : EmbeddedGraph S)
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal)) :
    realizedCyclePath G c 0 = realizedCyclePath G c 1 := by
  rw [Path.source,Path.target,c.closed]

theorem realizedCyclePath_range (G : EmbeddedGraph S)
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal)) :
    range (realizedCyclePath G c) = ⋃ i, range (subdivisionPath G (c.adjacent i)) :=
  concatenateNonempty_range _ _ _ _

theorem realizedCycle_vertices_injective (G : EmbeddedGraph S)
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal)) :
    Function.Injective (fun i : Fin c.length => subdivisionVertex G (c.vertex i.castSucc)) :=
  (subdivisionVertex_injective G).comp c.injective

end RealizedChain
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
section HalfOpenConcatenation
variable {X : Type*} [TopologicalSpace X] {x y z : X}

/-- The terminal endpoint is omitted, so adjacent oriented pieces do not
duplicate their common vertex. This also handles the closing vertex. -/
def halfOpenRange {a b : X} (p : Path a b) : Set X :=
  p '' {t : unitInterval | (t : ℝ) < 1}

/-- At the joining parameter use the initial point of the second path. -/
theorem trans_apply_lt (p : Path x y) (q : Path y z) (t : unitInterval) :
    (p.trans q) t =
      if h : (t : ℝ) < 1 / 2 then
        p ⟨2 * t, by constructor <;> linarith [t.property.1]⟩
      else q ⟨2 * t - 1, by constructor <;> linarith [t.property.2]⟩ := by
  rw [Path.trans_apply]
  split_ifs with hle hlt hlt
  · rfl
  · have ht : (t : ℝ) = 1 / 2 := le_antisymm hle (le_of_not_gt hlt)
    have hp : (⟨2 * (t : ℝ), by constructor <;> linarith [t.property.1]⟩ :
        unitInterval) = 1 := Subtype.ext (by dsimp; linarith)
    have hq : (⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.2]⟩ :
        unitInterval) = 0 := Subtype.ext (by dsimp; linarith)
    rw [hp, hq, Path.target, Path.source]
  · exact False.elim (hle hlt.le)
  · rfl

theorem halfOpenRange_trans (p : Path x y) (q : Path y z) :
    halfOpenRange (p.trans q) = halfOpenRange p ∪ halfOpenRange q := by
  ext a
  constructor
  · rintro ⟨t, ht, rfl⟩
    change (t : ℝ) < 1 at ht
    rw [trans_apply_lt]
    split_ifs with h
    · exact Or.inl ⟨_, by dsimp; linarith, rfl⟩
    · exact Or.inr ⟨_, by dsimp; linarith, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · change (t : ℝ) < 1 at ht
      refine ⟨⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1]⟩,
        by dsimp; linarith, ?_⟩
      rw [trans_apply_lt, dite_eq_left (by dsimp; linarith)]
      congr 1
      apply Subtype.ext
      dsimp
      ring
    · change (t : ℝ) < 1 at ht
      refine ⟨⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.property.1]⟩,
        by dsimp; linarith, ?_⟩
      rw [trans_apply_lt, dite_eq_right (by dsimp; linarith [t.property.1])]
      congr 1
      apply Subtype.ext
      dsimp
      ring

/-- Half-open simple pieces with disjoint half-open images concatenate to a
half-open simple path. The common endpoint is counted only by the second piece. -/
theorem trans_halfOpen_injective (p : Path x y) (q : Path y z)
    (hp : InjOn p {t : unitInterval | (t : ℝ) < 1})
    (hq : InjOn q {t : unitInterval | (t : ℝ) < 1})
    (hdis : Disjoint (halfOpenRange p) (halfOpenRange q)) :
    InjOn (p.trans q) {t : unitInterval | (t : ℝ) < 1} := by
  intro t ht s hs heq
  change (t : ℝ) < 1 at ht
  change (s : ℝ) < 1 at hs
  rw [trans_apply_lt, trans_apply_lt] at heq
  split_ifs at heq with htleft hsleft hsleft
  · have h := hp (by dsimp; linarith) (by dsimp; linarith) heq
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    dsimp at hv
    linarith
  · exact False.elim (Set.disjoint_left.mp hdis
      ⟨_, by dsimp; linarith, rfl⟩ ⟨_, by dsimp; linarith, heq.symm⟩)
  · exact False.elim (Set.disjoint_left.mp hdis
      ⟨_, by dsimp; linarith, heq.symm⟩ ⟨_, by dsimp; linarith, rfl⟩)
  · have h := hq (by dsimp; linarith) (by dsimp; linarith) heq
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    dsimp at hv
    linarith

theorem concatenateNonempty_halfOpenRange (n : ℕ) (hn : 0 < n)
    (p : Fin (n+1) → X) (F : (i : Fin n) → Path (p i.castSucc) (p i.succ)) :
    halfOpenRange (concatenateNonempty n hn p F) = ⋃ i, halfOpenRange (F i) := by
  match n with
  | 0 => exact False.elim (Nat.not_lt_zero _ hn)
  | 1 =>
    simp only [concatenateNonempty]
    ext x
    constructor
    · intro hx; exact mem_iUnion.mpr ⟨0, hx⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      exact hi
  | n+2 =>
    rw [concatenateNonempty]
    erw [halfOpenRange_trans]
    erw [concatenateNonempty_halfOpenRange]
    ext x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.castSucc, hi⟩
      · exact mem_iUnion.mpr ⟨Fin.last (n+1), hx⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact Fin.lastCases (fun hlast => Or.inr hlast)
        (fun j hj => Or.inl (mem_iUnion.mpr ⟨j, hj⟩)) i hi
termination_by n

theorem concatenateNonempty_halfOpen_injective (n : ℕ) (hn : 0 < n)
    (p : Fin (n+1) → X) (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hinj : ∀ i, InjOn (F i) {t : unitInterval | (t : ℝ) < 1})
    (hdis : Pairwise (fun i j => Disjoint (halfOpenRange (F i)) (halfOpenRange (F j)))) :
    InjOn (concatenateNonempty n hn p F) {t : unitInterval | (t : ℝ) < 1} := by
  match n with
  | 0 => exact False.elim (Nat.not_lt_zero _ hn)
  | 1 => exact hinj 0
  | n+2 =>
    rw [concatenateNonempty]
    apply trans_halfOpen_injective
    · apply concatenateNonempty_halfOpen_injective
      · exact fun i => hinj i.castSucc
      · intro i j hij
        exact hdis (by intro heq; exact hij (Fin.castSucc_injective _ heq))
    · exact hinj _
    · rw [concatenateNonempty_halfOpenRange, Set.disjoint_iUnion_left]
      intro i
      exact hdis (Fin.castSucc_ne_last i)
termination_by n

end HalfOpenConcatenation
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
section EmbeddedSubpaths
variable {M : Type*} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

theorem edge_halfOpen_injective (G : EmbeddedGraph S) (e : Fin G.edgeCount) :
    InjOn (G.edge e) {t : unitInterval | (t : ℝ) < 1} := by
  apply injOn_halfOpen_of_open_injective _ (G.open_injective e)
  intro t ht ht' heq
  exact G.avoids_vertices e t ht ht' ⟨G.initial e, (G.at_zero e).symm.trans heq.symm⟩

theorem edge_positive_injective (G : EmbeddedGraph S) (e : Fin G.edgeCount) :
    InjOn (G.edge e) {t : unitInterval | 0 < (t : ℝ)} := by
  intro t ht s hs heq
  change 0 < (t : ℝ) at ht
  change 0 < (s : ℝ) at hs
  by_cases ht1 : t = 1
  · subst t
    by_cases hs1 : s = 1
    · exact hs1.symm
    · have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2
        (fun h => hs1 (Subtype.ext h))
      exact False.elim (G.avoids_vertices e s hs hslt
        ⟨G.terminal e, (G.at_one e).symm.trans heq⟩)
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
      (fun h => ht1 (Subtype.ext h))
    by_cases hs1 : s = 1
    · subst s
      exact False.elim (G.avoids_vertices e t ht htlt
        ⟨G.terminal e, (G.at_one e).symm.trans heq.symm⟩)
    · have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2
        (fun h => hs1 (Subtype.ext h))
      exact G.open_injective e ⟨ht, htlt⟩ ⟨hs, hslt⟩ heq

theorem convexComb_injective {a b : unitInterval} (hab : a ≠ b) :
    Function.Injective (Set.Icc.convexComb a b) := by
  intro t s heq
  have hval := congrArg Subtype.val heq
  simp only [Set.Icc.coe_convexComb] at hval
  have hprod : ((b : ℝ) - a) * ((t : ℝ) - s) = 0 := by nlinarith only [hval]
  have hba : (b : ℝ) - a ≠ 0 := sub_ne_zero.mpr
    (fun h => hab (Subtype.ext h.symm))
  exact Subtype.ext (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hba))

theorem edge_subpath_injective_of_lt_one (G : EmbeddedGraph S) (e : Fin G.edgeCount)
    {a b : unitInterval} (ha : (a : ℝ) < 1) (hb : (b : ℝ) < 1) (hab : a ≠ b) :
    Function.Injective ((edgePath G e).subpath a b) := by
  intro t s heq
  apply convexComb_injective hab
  apply edge_halfOpen_injective G e
  · change (Set.Icc.convexComb a b t : ℝ) < 1
    simp only [Set.Icc.coe_convexComb]
    exact (convex_Iio (𝕜 := ℝ) (1 : ℝ)) ha hb (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  · change (Set.Icc.convexComb a b s : ℝ) < 1
    simp only [Set.Icc.coe_convexComb]
    exact (convex_Iio (𝕜 := ℝ) (1 : ℝ)) ha hb (sub_nonneg.mpr s.property.2) s.property.1 (by ring)
  · exact heq

theorem edge_subpath_injective_of_pos (G : EmbeddedGraph S) (e : Fin G.edgeCount)
    {a b : unitInterval} (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) (hab : a ≠ b) :
    Function.Injective ((edgePath G e).subpath a b) := by
  intro t s heq
  apply convexComb_injective hab
  apply edge_positive_injective G e
  · change 0 < (Set.Icc.convexComb a b t : ℝ)
    simp only [Set.Icc.coe_convexComb]
    exact (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) ha hb (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  · change 0 < (Set.Icc.convexComb a b s : ℝ)
    simp only [Set.Icc.coe_convexComb]
    exact (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) ha hb (sub_nonneg.mpr s.property.2) s.property.1 (by ring)
  · exact heq

/-- Every individual geometric subdivision piece is a genuine arc, including
the pieces incident to an original loop vertex. -/
theorem subdivisionPath_injective (G : EmbeddedGraph S)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y) :
    Function.Injective (subdivisionPath G h) := by
  cases x with
  | inl v =>
    cases y with
    | inl w => exact False.elim h
    | inr d =>
      rcases d with ⟨e,b⟩
      cases b
      · change Function.Injective ((edgePath G e).subpath 0 (subdivisionParameter false))
        exact edge_subpath_injective_of_lt_one G e (by norm_num)
          (subdivisionParameter_lt_one _) (by
            intro heq
            have := congrArg Subtype.val heq
            norm_num [subdivisionParameter] at this)
      · change Function.Injective ((edgePath G e).subpath 1 (subdivisionParameter true))
        exact edge_subpath_injective_of_pos G e (by norm_num)
          (subdivisionParameter_pos _) (by
            intro heq
            have := congrArg Subtype.val heq
            norm_num [subdivisionParameter] at this)
  | inr d =>
    cases y with
    | inl v =>
      rcases d with ⟨e,b⟩
      cases b
      · change Function.Injective ((edgePath G e).subpath (subdivisionParameter false) 0)
        exact edge_subpath_injective_of_lt_one G e (subdivisionParameter_lt_one _)
          (by norm_num) (by
            intro heq
            have := congrArg Subtype.val heq
            norm_num [subdivisionParameter] at this)
      · change Function.Injective ((edgePath G e).subpath (subdivisionParameter true) 1)
        exact edge_subpath_injective_of_pos G e (subdivisionParameter_pos _)
          (by norm_num) (by
            intro heq
            have := congrArg Subtype.val heq
            norm_num [subdivisionParameter] at this)
    | inr e =>
      rcases d with ⟨d,b⟩
      rcases e with ⟨e,c⟩
      have hde : d = e := h.1
      subst e
      change Function.Injective ((edgePath G d).subpath
        (subdivisionParameter b) (subdivisionParameter c))
      exact edge_subpath_injective_of_lt_one G d (subdivisionParameter_lt_one _)
        (subdivisionParameter_lt_one _)
        (fun heq => h.2 (subdivisionParameter_injective heq))

end EmbeddedSubpaths
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
section FrontierPropagation
variable {X : Type*} [TopologicalSpace X]

/-- The actual interval map on the connected open real parameter interval. -/
def openParameterMap (c : C(unitInterval, X)) : C(Ioo (0 : ℝ) 1, X) :=
  ⟨fun t => c ⟨t.val, t.property.1.le, t.property.2.le⟩,
    c.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

/-- Connectedness propagates a closed-set incidence along an entire edge,
including both endpoints, once local incidence is open on the open edge.
The remaining geometric saturation step is precisely that local openness. -/
theorem whole_edge_of_open_incidence (c : C(unitInterval, X))
    {F : Set X} (hF : IsClosed F)
    (hlocal : IsOpen (openParameterMap c ⁻¹' F))
    (hmeet : (openParameterMap c ⁻¹' F).Nonempty) : range c ⊆ F := by
  let : PreconnectedSpace (Ioo (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hclosed : IsClosed (openParameterMap c ⁻¹' F) :=
    hF.preimage (openParameterMap c).continuous
  have hfull := (show IsClopen (openParameterMap c ⁻¹' F) from
    ⟨hclosed, hlocal⟩).eq_univ hmeet
  have hsub : Ioo (0 : ℝ) 1 ⊆ IccExtend zero_le_one c ⁻¹' F := by
    intro t ht
    have hm : (⟨t, ht⟩ : Ioo (0 : ℝ) 1) ∈ openParameterMap c ⁻¹' F := by
      rw [hfull]
      exact mem_univ _
    change c ⟨t, ht.1.le, ht.2.le⟩ ∈ F at hm
    simpa only [mem_preimage, IccExtend_of_mem zero_le_one c ⟨ht.1.le, ht.2.le⟩] using hm
  have hc := closure_minimal hsub (hF.preimage c.continuous.Icc_extend')
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hc
  rintro x ⟨t, rfl⟩
  have hm := hc t.property
  simpa only [mem_preimage, IccExtend_of_mem zero_le_one c t.property] using hm

theorem whole_edge_or_no_open_incidence (c : C(unitInterval, X))
    {F : Set X} (hF : IsClosed F)
    (hlocal : IsOpen (openParameterMap c ⁻¹' F)) :
    range c ⊆ F ∨ Disjoint (range (openParameterMap c)) F := by
  by_cases hm : (openParameterMap c ⁻¹' F).Nonempty
  · exact Or.inl (whole_edge_of_open_incidence c hF hlocal hm)
  · right
    apply Set.disjoint_left.mpr
    rintro x ⟨t, rfl⟩ ht
    exact hm ⟨t, ht⟩

end FrontierPropagation
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M} {D : P202Specs.SmoothSurfaceDouble.SmoothDouble S}
variable {s : Bool}
variable {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
variable {B : CompactSmoothSeam D.manifold}
variable {T : TransverseDiskArrangement D.manifold
  (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B}

/-- The full-plane coordinate frontier is the whole actual component frontier,
including its seam points, for any permitted original chart. -/
theorem graphGeometry_component_coordinates (H : ArrangementGraphGeometryData S D s T)
    (a : ConnectedComponents (H.graph.carrierᶜ : Set M))
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hsource : closure (componentSet H.graph.carrierᶜ a) ⊆ e.source) :
    let C := componentSet H.graph.carrierᶜ a
    IsOpen (coordinates e '' C) ∧ IsConnected (coordinates e '' C) ∧
      IsCompact (closure (coordinates e '' C)) ∧
      closure (coordinates e '' C) = coordinates e '' closure C ∧
      frontier (coordinates e '' C) = coordinates e '' frontier C ∧
      (frontier (coordinates e '' C)).Nonempty := by
  let C := componentSet H.graph.carrierᶜ a
  have hmiss : Disjoint C (intrinsicBoundary S) := Set.disjoint_left.mpr (by
    intro x hx hxb
    exact Components.subset H.graph.carrierᶜ a hx (H.contains_boundary hxb))
  have hcl := closure_coordinate_image e (H.compact_closures a) hsource
  have hfront := frontier_coordinate_image_away_boundary S e he
    (H.open_components a) (H.compact_closures a) hsource hmiss
  refine ⟨isOpen_coordinate_image_away_boundary S e he (H.open_components a)
    (subset_closure.trans hsource) hmiss,
    (H.connected_components a).image _
      ((continuousOn_coordinates e).mono (subset_closure.trans hsource)),
    ?_, hcl, hfront, ?_⟩
  · rw [hcl]
    exact (H.compact_closures a).image_of_continuousOn
      ((continuousOn_coordinates e).mono hsource)
  · rw [hfront]
    exact (H.nonempty_frontiers a).image _

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.BoundaryCycles
namespace SimpleCyclicChain
variable {W : Type*} {G : SimpleGraph W} (c : SimpleCyclicChain G)

def next (i : Fin c.length) : Fin c.length :=
  if h : i.val + 1 < c.length then ⟨i.val + 1, h⟩ else ⟨0, c.length_pos⟩

theorem vertex_succ (i : Fin c.length) :
    c.vertex i.succ = c.vertex (c.next i).castSucc := by
  by_cases hi : i.val + 1 < c.length
  · simp only [next, dite_eq_left hi]
    rfl
  · have hilast : i.succ = Fin.last c.length := Fin.ext (by dsimp; omega)
    rw [hilast, ← c.closed]
    simp only [next, dite_eq_right hi]
    rfl

theorem next_ne_self (i : Fin c.length) : c.next i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [next] at hv
  split_ifs at hv <;> simp only at hv <;>
    have := c.length_ge_three <;> omega

/-- A genuine simple cycle cannot traverse an edge and then the same edge
in reverse elsewhere. The lower bound of three is essential here. -/
theorem not_reverse (i j : Fin c.length) :
    ¬ (c.vertex i.castSucc = c.vertex j.succ ∧
      c.vertex i.succ = c.vertex j.castSucc) := by
  rintro ⟨hij, hji⟩
  rw [c.vertex_succ] at hij hji
  have h1 := congrArg Fin.val (c.injective hij)
  have h2 := congrArg Fin.val (c.injective hji)
  dsimp [next] at h1 h2
  split_ifs at h1 <;> split_ifs at h2 <;>
    simp only at h1 h2 <;> have := c.length_ge_three <;> omega

theorem directed_edge_injective {i j : Fin c.length}
    (h : c.vertex i.castSucc = c.vertex j.castSucc) : i = j := c.injective h

end SimpleCyclicChain
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
section SubdivisionIntersections
variable {M : Type*} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- The three geometric pieces of an original edge have distinct artificial
endpoints, even when the original edge is a loop. -/
def pieceInitial (G : EmbeddedGraph S) (e : Fin G.edgeCount) :
    Fin 3 → Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)
  | 0 => Sum.inl (G.initial e)
  | 1 => Sum.inr (e, false)
  | 2 => Sum.inr (e, true)

def pieceTerminal (G : EmbeddedGraph S) (e : Fin G.edgeCount) :
    Fin 3 → Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)
  | 0 => Sum.inr (e, false)
  | 1 => Sum.inr (e, true)
  | 2 => Sum.inl (G.terminal e)

def pieceInterior (k : Fin 3) (s : ℝ) : Prop :=
  (k.val : ℝ) / 3 < s ∧ s < ((k.val : ℝ) + 1) / 3

theorem pieceInterior_bounds {k : Fin 3} {s : ℝ} (h : pieceInterior k s) :
    0 < s ∧ s < 1 := by
  fin_cases k <;> norm_num [pieceInterior] at h <;> constructor <;> linarith

theorem pieceInterior_unique {k l : Fin 3} {s : ℝ}
    (hk : pieceInterior k s) (hl : pieceInterior l s) : k = l := by
  fin_cases k <;> fin_cases l <;> norm_num [pieceInterior] at hk hl ⊢ <;> linarith

/-- Interior points of an oriented subdivision arc have original-edge
parameter strictly inside precisely one of the three pieces. -/
theorem subdivisionPath_interior_location (G : EmbeddedGraph S)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y)
    (t : unitInterval) (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1) :
    ∃ (e : Fin G.edgeCount) (k : Fin 3) (s : unitInterval),
      pieceInterior k s ∧ G.edge e s = subdivisionPath G h t ∧
      ((x = pieceInitial G e k ∧ y = pieceTerminal G e k) ∨
       (x = pieceTerminal G e k ∧ y = pieceInitial G e k)) := by
  cases x with
  | inl v =>
    cases y with
    | inl w => exact False.elim h
    | inr d =>
      rcases d with ⟨e,b⟩
      cases b
      · change G.initial e = v at h
        subst v
        refine ⟨e, 0, Set.Icc.convexComb 0 (subdivisionParameter false) t, ?_, rfl,
          Or.inl ⟨rfl, rfl⟩⟩
        norm_num only [pieceInterior, Set.Icc.coe_convexComb, subdivisionParameter, Bool.false_eq_true, ite_false, ite_true, Set.Icc.coe_zero, Set.Icc.coe_one, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero, zero_div, zero_add, mul_one]
        constructor <;> linarith [ht.1, ht.2]
      · change G.terminal e = v at h
        subst v
        refine ⟨e, 2, Set.Icc.convexComb 1 (subdivisionParameter true) t, ?_, rfl,
          Or.inr ⟨rfl, rfl⟩⟩
        norm_num only [pieceInterior, Set.Icc.coe_convexComb, subdivisionParameter, Bool.false_eq_true, ite_false, ite_true, Set.Icc.coe_zero, Set.Icc.coe_one, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero, zero_div, zero_add, mul_one]
        constructor <;> linarith [ht.1, ht.2]
  | inr d =>
    cases y with
    | inl v =>
      rcases d with ⟨e,b⟩
      cases b
      · change G.initial e = v at h
        subst v
        refine ⟨e, 0, Set.Icc.convexComb (subdivisionParameter false) 0 t, ?_, rfl,
          Or.inr ⟨rfl, rfl⟩⟩
        norm_num only [pieceInterior, Set.Icc.coe_convexComb, subdivisionParameter, Bool.false_eq_true, ite_false, ite_true, Set.Icc.coe_zero, Set.Icc.coe_one, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero, zero_div, zero_add, mul_one]
        constructor <;> linarith [ht.1, ht.2]
      · change G.terminal e = v at h
        subst v
        refine ⟨e, 2, Set.Icc.convexComb (subdivisionParameter true) 1 t, ?_, rfl,
          Or.inl ⟨rfl, rfl⟩⟩
        norm_num only [pieceInterior, Set.Icc.coe_convexComb, subdivisionParameter, Bool.false_eq_true, ite_false, ite_true, Set.Icc.coe_zero, Set.Icc.coe_one, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero, zero_div, zero_add, mul_one]
        constructor <;> linarith [ht.1, ht.2]
    | inr f =>
      rcases d with ⟨e,b⟩
      rcases f with ⟨f,c⟩
      have hef : e = f := h.1
      subst f
      have hbc : b ≠ c := h.2
      cases b <;> cases c
      · exact False.elim (hbc rfl)
      · refine ⟨e, 1, Set.Icc.convexComb (subdivisionParameter false)
          (subdivisionParameter true) t, ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
        norm_num only [pieceInterior, Set.Icc.coe_convexComb, subdivisionParameter, Bool.false_eq_true, ite_false, ite_true, Set.Icc.coe_zero, Set.Icc.coe_one, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero, zero_div, zero_add, mul_one]
        constructor <;> linarith [ht.1, ht.2]
      · refine ⟨e, 1, Set.Icc.convexComb (subdivisionParameter true)
          (subdivisionParameter false) t, ?_, rfl, Or.inr ⟨rfl, rfl⟩⟩
        norm_num only [pieceInterior, Set.Icc.coe_convexComb, subdivisionParameter, Bool.false_eq_true, ite_false, ite_true, Set.Icc.coe_zero, Set.Icc.coe_one, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero, zero_div, zero_add, mul_one]
        constructor <;> linarith [ht.1, ht.2]
      · exact False.elim (hbc rfl)

/-- Equality between interior points of original edges determines both the
original edge and its open parameter. Loops only identify endpoints. -/
theorem open_edge_image_eq (G : EmbeddedGraph S) {e f : Fin G.edgeCount}
    {s t : unitInterval} (hs : 0 < (s : ℝ) ∧ (s : ℝ) < 1)
    (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1) (heq : G.edge e s = G.edge f t) :
    e = f ∧ s = t := by
  have hef : e = f := by
    by_contra hne
    exact Set.disjoint_left.mp (G.disjoint_open_edges hne)
      ⟨s, hs, rfl⟩ ⟨t, ht, heq.symm⟩
  subst f
  exact ⟨rfl, G.open_injective e hs ht heq⟩

/-- Distinct subdivision edges meet in their interiors only if they are the
same unoriented edge. This uses the actual embedded interval maps. -/
theorem subdivisionPath_interior_intersection (G : EmbeddedGraph S)
    {x y z w : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y)
    (h' : (doubleSubdivision G.initial G.terminal).Adj z w)
    {t q : unitInterval} (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1)
    (hq : 0 < (q : ℝ) ∧ (q : ℝ) < 1)
    (heq : subdivisionPath G h t = subdivisionPath G h' q) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  obtain ⟨e,k,s,hks,hes,hxy⟩ := subdivisionPath_interior_location G h t ht
  obtain ⟨f,l,r,hlr,hfr,hzw⟩ := subdivisionPath_interior_location G h' q hq
  obtain ⟨hef,hsr⟩ := open_edge_image_eq G (pieceInterior_bounds hks)
    (pieceInterior_bounds hlr) (hes.trans (heq.trans hfr.symm))
  subst f
  subst r
  have hkl := pieceInterior_unique hks hlr
  subst l
  rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hzw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

end SubdivisionIntersections
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
section SubdivisionSimplicity
variable {M : Type*} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- No subdivision vertex lies in the interior of any subdivision arc. -/
theorem subdivisionPath_avoids_vertices (G : EmbeddedGraph S)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y)
    (t : unitInterval) (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1) :
    subdivisionPath G h t ∉ range (subdivisionVertex G) := by
  obtain ⟨e,k,s,hks,hes,_⟩ := subdivisionPath_interior_location G h t ht
  rintro ⟨v,hv⟩
  cases v with
  | inl v =>
    exact G.avoids_vertices e s (pieceInterior_bounds hks).1
      (pieceInterior_bounds hks).2 ⟨v, hv.trans hes.symm⟩
  | inr d =>
    rcases d with ⟨f,b⟩
    obtain ⟨hef,hsb⟩ := open_edge_image_eq G (pieceInterior_bounds hks)
      ⟨subdivisionParameter_pos b,subdivisionParameter_lt_one b⟩
      (hes.trans hv.symm)
    rw [hsb] at hks
    fin_cases k <;> cases b <;> norm_num [pieceInterior,subdivisionParameter] at hks

/-- The half-open arc ranges of a genuine simple cyclic chain are disjoint.
A reversed repeat is excluded using the chain's length of at least three. -/
theorem realizedCyclePath_piece_disjoint (G : EmbeddedGraph S)
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal)) :
    Pairwise (fun i j => Disjoint
      (halfOpenRange (subdivisionPath G (c.adjacent i)))
      (halfOpenRange (subdivisionPath G (c.adjacent j)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨t,ht,htz⟩ ⟨q,hq,hqz⟩
  have heq : subdivisionPath G (c.adjacent i) t =
      subdivisionPath G (c.adjacent j) q := htz.trans hqz.symm
  by_cases ht0 : t = 0
  · subst t
    by_cases hq0 : q = 0
    · subst q
      have hv : subdivisionVertex G (c.vertex i.castSucc) =
          subdivisionVertex G (c.vertex j.castSucc) := by simpa using heq
      exact hij (c.injective (subdivisionVertex_injective G hv))
    · have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1
        (fun he => hq0 (Subtype.ext he.symm))
      exact subdivisionPath_avoids_vertices G (c.adjacent j) q ⟨hqpos,hq⟩
        ⟨c.vertex i.castSucc, by simpa using heq⟩
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (fun he => ht0 (Subtype.ext he.symm))
    by_cases hq0 : q = 0
    · subst q
      exact subdivisionPath_avoids_vertices G (c.adjacent i) t ⟨htpos,ht⟩
        ⟨c.vertex j.castSucc, by simpa using heq.symm⟩
    · have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1
        (fun he => hq0 (Subtype.ext he.symm))
      rcases subdivisionPath_interior_intersection G (c.adjacent i) (c.adjacent j)
        ⟨htpos,ht⟩ ⟨hqpos,hq⟩ heq with hdir | hrev
      · exact hij (c.injective hdir.1)
      · exact c.not_reverse i j hrev

/-- The actual finite concatenation is injective before the repeated closing
endpoint. Neither a topological circle nor a boundary certificate is assumed. -/
theorem realizedCyclePath_halfOpen_injective (G : EmbeddedGraph S)
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal)) :
    InjOn (realizedCyclePath G c) {t : unitInterval | (t : ℝ) < 1} := by
  apply concatenateNonempty_halfOpen_injective
  · exact fun i => (subdivisionPath_injective G (c.adjacent i)).injOn
  · exact realizedCyclePath_piece_disjoint G c

/-- Every actual simple cyclic subdivision chain has an injective circle
parametrization with exactly the union of its actual subdivision-arc traces.
The additional smooth joining obligations are kept separate. -/
theorem realizedCycle_circle (G : EmbeddedGraph S)
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal)) :
    ∃ f : C(ParameterCircle, M), Function.Injective f ∧
      range f = ⋃ i, range (subdivisionPath G (c.adjacent i)) := by
  exact ⟨closeInterval (realizedCyclePath G c).toContinuousMap
      (realizedCyclePath_closed G c),
    closeInterval_injective _ _ (realizedCyclePath_halfOpen_injective G c),
    (closeInterval_range _ _).trans (realizedCyclePath_range G c)⟩

end SubdivisionSimplicity
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
section DisjointRealizations
variable {M : Type*} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- A point of a subdivision arc is an endpoint or an interior point. -/
theorem subdivisionPath_range_cases (G : EmbeddedGraph S)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y) {z : M}
    (hz : z ∈ range (subdivisionPath G h)) :
    (∃ v ∈ ({x,y} : Set _), subdivisionVertex G v = z) ∨
      ∃ t : unitInterval, (0 < (t : ℝ) ∧ (t : ℝ) < 1) ∧ subdivisionPath G h t = z := by
  obtain ⟨t,rfl⟩ := hz
  by_cases ht0 : t = 0
  · subst t
    exact Or.inl ⟨x,by simp,by simp⟩
  · by_cases ht1 : t = 1
    · subst t
      exact Or.inl ⟨y,by simp,by simp⟩
    · exact Or.inr ⟨t,⟨lt_of_le_of_ne t.property.1
        (fun he => ht0 (Subtype.ext he.symm)),
        lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))⟩,rfl⟩

/-- Subdivision arcs with disjoint endpoint sets have disjoint full traces. -/
theorem subdivisionPath_disjoint_of_vertices (G : EmbeddedGraph S)
    {x y z w : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y)
    (h' : (doubleSubdivision G.initial G.terminal).Adj z w)
    (hv : Disjoint ({x,y} : Set _) {z,w}) :
    Disjoint (range (subdivisionPath G h)) (range (subdivisionPath G h')) := by
  apply Set.disjoint_left.mpr
  intro p hp hp'
  rcases subdivisionPath_range_cases G h hp with ⟨v,hvxy,hvp⟩ | ⟨t,ht,htp⟩
  · rcases subdivisionPath_range_cases G h' hp' with ⟨v',hvzw,hv'p⟩ | ⟨q,hq,hqp⟩
    · have heq := subdivisionVertex_injective G (hvp.trans hv'p.symm)
      exact Set.disjoint_left.mp hv hvxy (heq.symm ▸ hvzw)
    · exact subdivisionPath_avoids_vertices G h' q hq ⟨v,hvp.trans hqp.symm⟩
  · rcases subdivisionPath_range_cases G h' hp' with ⟨v',hvzw,hv'p⟩ | ⟨q,hq,hqp⟩
    · exact subdivisionPath_avoids_vertices G h t ht ⟨v',hv'p.trans htp.symm⟩
    · rcases subdivisionPath_interior_intersection G h h' ht hq
        (htp.trans hqp.symm) with heq | heq
      · exact Set.disjoint_left.mp hv (show x ∈ ({x,y} : Set _) from by simp) (by simp [heq.1])
      · exact Set.disjoint_left.mp hv (show x ∈ ({x,y} : Set _) from by simp) (by simp [heq.1])

/-- Vertex-disjoint simple subdivision cycles have disjoint actual traces,
including their original vertices and closing points. -/
theorem realizedCyclePath_disjoint (G : EmbeddedGraph S)
    (c d : SimpleCyclicChain (doubleSubdivision G.initial G.terminal))
    (hv : Disjoint (range (fun i : Fin c.length => c.vertex i.castSucc))
      (range (fun j : Fin d.length => d.vertex j.castSucc))) :
    Disjoint (range (realizedCyclePath G c)) (range (realizedCyclePath G d)) := by
  rw [realizedCyclePath_range,realizedCyclePath_range,Set.disjoint_iUnion_left]
  intro i
  rw [Set.disjoint_iUnion_right]
  intro j
  apply subdivisionPath_disjoint_of_vertices G (c.adjacent i) (d.adjacent j)
  apply Disjoint.mono _ _ hv
  · intro v hv
    simp only [mem_insert_iff,mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨i,rfl⟩
    · exact ⟨c.next i,(c.vertex_succ i).symm⟩
  · intro v hv
    simp only [mem_insert_iff,mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨j,rfl⟩
    · exact ⟨d.next j,(d.vertex_succ j).symm⟩

/-- In the degree-two case the selected distinct component cycles have
pairwise disjoint geometric traces, without any boundary-curve premise. -/
theorem componentCycle_realizations_disjoint (G : EmbeddedGraph S)
    (hdegree : ∀ p, (incidences G.initial G.terminal p).Nonempty →
      (incidences G.initial G.terminal p).ncard = 2) :
    let h := doubleSubdivision_isCycles G.initial G.terminal hdegree
    Pairwise (fun c d : NonisolatedComponent (doubleSubdivision G.initial G.terminal) =>
      Disjoint (range (realizedCyclePath G (componentCycle h c).chain))
        (range (realizedCyclePath G (componentCycle h d).chain))) := by
  dsimp only
  intro c d hcd
  apply realizedCyclePath_disjoint
  rw [ComponentCycle.chain_vertices,ComponentCycle.chain_vertices]
  exact (doubleSubdivision G.initial G.terminal).pairwise_disjoint_supp_connectedComponent
    (fun heq => hcd (Subtype.ext heq))

/-- A chart containing a realized cycle transports it to a genuine injective
circle in the ambient coordinate plane, with the exact coordinate trace. -/
theorem realizedCycle_circle_in_chart (G : EmbeddedGraph S)
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal))
    (e : ModelChart 2 kind M)
    (hs : range (realizedCyclePath G c) ⊆ e.source) :
    ∃ f : C(ParameterCircle, Plane), Function.Injective f ∧
      range f = coordinates e '' range (realizedCyclePath G c) := by
  let p := closeInterval (realizedCyclePath G c).toContinuousMap
    (realizedCyclePath_closed G c)
  have hp : range p = range (realizedCyclePath G c) := closeInterval_range _ _
  let f : C(ParameterCircle, Plane) := ⟨coordinates e ∘ p,
    (continuousOn_coordinates e).comp_continuous p.continuous
      (fun t => hs (hp ▸ mem_range_self t))⟩
  refine ⟨f,?_,?_⟩
  · intro t q heq
    apply closeInterval_injective _ _ (realizedCyclePath_halfOpen_injective G c)
    exact coordinates_injOn e (hs (hp ▸ mem_range_self t))
      (hs (hp ▸ mem_range_self q)) heq
  · change range (coordinates e ∘ p) = _
    rw [Set.range_comp,hp]

end DisjointRealizations
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
section CycleCoverage
variable {M : Type*} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- Reversal changes only the orientation of a geometric subdivision arc. -/
theorem subdivisionPath_reverse (G : EmbeddedGraph S)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y) :
    (subdivisionPath G h.symm).toContinuousMap = (subdivisionPath G h).symm.toContinuousMap := by
  cases x with
  | inl v =>
    cases y with
    | inl w => exact False.elim h
    | inr d =>
      rcases d with ⟨e,b⟩
      cases b <;> ext t <;>
        change (edgePath G e).subpath _ _ t = ((edgePath G e).subpath _ _).symm t <;>
        rw [Path.symm_subpath]
  | inr d =>
    cases y with
    | inl v =>
      rcases d with ⟨e,b⟩
      cases b <;> ext t <;>
        change (edgePath G e).subpath _ _ t = ((edgePath G e).subpath _ _).symm t <;>
        rw [Path.symm_subpath]
    | inr f =>
      rcases d with ⟨e,b⟩
      rcases f with ⟨f,c⟩
      have hef : e = f := h.1
      subst f
      ext t
      change (edgePath G e).subpath _ _ t = ((edgePath G e).subpath _ _).symm t
      rw [Path.symm_subpath]

theorem subdivisionPath_reverse_range (G : EmbeddedGraph S)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y) :
    range (subdivisionPath G h.symm) = range (subdivisionPath G h) := by
  change range (subdivisionPath G h.symm).toContinuousMap = _
  rw [subdivisionPath_reverse]
  exact Path.symm_range _

/-- The ordered chain traverses every edge of the underlying component cycle
in one of its two orientations. -/
theorem ComponentCycle.chain_edge {W : Type*} {G : SimpleGraph W}
    {a : G.ConnectedComponent} (p : ComponentCycle G a) {x y : W}
    (h : p.walk.toSubgraph.Adj x y) :
    ∃ i : Fin p.chain.length,
      (p.chain.vertex i.castSucc = x ∧ p.chain.vertex i.succ = y) ∨
      (p.chain.vertex i.castSucc = y ∧ p.chain.vertex i.succ = x) := by
  obtain ⟨i,hi,hil⟩ := p.walk.toSubgraph_adj_iff.mp h
  refine ⟨⟨i,hil⟩,?_⟩
  simpa only [ComponentCycle.chain,Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,
    Prod.swap_prod_mk, Fin.val_castSucc, Fin.val_mk, Fin.val_succ] using hi

/-- A selected component cycle contains the complete trace of each of its
subdivision edges, in either traversal direction. -/
theorem subdivisionPath_subset_componentCycle (G : EmbeddedGraph S)
    {a : (doubleSubdivision G.initial G.terminal).ConnectedComponent}
    (p : ComponentCycle (doubleSubdivision G.initial G.terminal) a)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : p.walk.toSubgraph.Adj x y) :
    range (subdivisionPath G h.adj_sub) ⊆ range (realizedCyclePath G p.chain) := by
  obtain ⟨i,hi⟩ := p.chain_edge h
  rw [realizedCyclePath_range]
  rcases hi with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · have heq : range (subdivisionPath G h.adj_sub) =
        range (subdivisionPath G (p.chain.adjacent i)) := by
      subst x
      subst y
      rfl
    rw [heq]
    intro z hz
    exact mem_iUnion.mpr ⟨i,hz⟩
  · have heq : range (subdivisionPath G h.adj_sub) =
        range (subdivisionPath G (p.chain.adjacent i).symm) := by
      subst x
      subst y
      rfl
    rw [heq,subdivisionPath_reverse_range G (p.chain.adjacent i)]
    intro z hz
    exact mem_iUnion.mpr ⟨i,hz⟩

/-- The three closed subdivision pieces cover the entire original edge,
including both endpoints and artificial marks. -/
theorem three_subdivision_pieces_cover (G : EmbeddedGraph S) (e : Fin G.edgeCount) :
    range (G.edge e) =
      range (subdivisionPath G (x := Sum.inl (G.initial e))
        (y := Sum.inr (e,false)) rfl) ∪
      range (subdivisionPath G (x := Sum.inr (e,false))
        (y := Sum.inr (e,true)) ⟨rfl,Bool.false_ne_true⟩) ∪
      range (subdivisionPath G (x := Sum.inr (e,true))
        (y := Sum.inl (G.terminal e)) rfl) := by
  change range (edgePath G e) =
    range ((edgePath G e).subpath 0 (subdivisionParameter false)) ∪
    range ((edgePath G e).subpath (subdivisionParameter false) (subdivisionParameter true)) ∪
    range ((edgePath G e).subpath (subdivisionParameter true) 1)
  rw [Path.range_subpath_of_le _ _ _ (by norm_num [subdivisionParameter]),
    Path.range_subpath_of_le _ _ _ (by norm_num [subdivisionParameter]),
    Path.range_subpath_of_le _ _ _ (by change (2/3 : ℝ) ≤ 1; norm_num),
    ← Set.image_union,← Set.image_union]
  have hintervals : Icc (0 : unitInterval) (subdivisionParameter false) ∪
      Icc (subdivisionParameter false) (subdivisionParameter true) ∪
      Icc (subdivisionParameter true) (1 : unitInterval) = univ := by
    ext t
    simp only [mem_union,mem_Icc,mem_univ,iff_true]
    by_cases ht : t ≤ subdivisionParameter false
    · exact Or.inl (Or.inl ⟨t.property.1,ht⟩)
    · by_cases ht' : t ≤ subdivisionParameter true
      · exact Or.inl (Or.inr ⟨(le_of_not_ge ht),ht'⟩)
      · exact Or.inr ⟨(le_of_not_ge ht'),t.property.2⟩
  rw [hintervals,Set.image_univ]

end CycleCoverage
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
section TopologicalCycleFamily
variable {M : Type*} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- Every subdivision path stays on its original graph edge. -/
theorem subdivisionPath_range_subset_edges (G : EmbeddedGraph S)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y) :
    range (subdivisionPath G h) ⊆ ⋃ e, range (G.edge e) := by
  cases x with
  | inl v =>
    cases y with
    | inl w => exact False.elim h
    | inr d =>
      rcases d with ⟨e,b⟩
      cases b <;> rintro z ⟨t,rfl⟩ <;>
        exact mem_iUnion.mpr ⟨e,⟨_,rfl⟩⟩
  | inr d =>
    cases y with
    | inl v =>
      rcases d with ⟨e,b⟩
      cases b <;> rintro z ⟨t,rfl⟩ <;>
        exact mem_iUnion.mpr ⟨e,⟨_,rfl⟩⟩
    | inr f =>
      rcases d with ⟨e,b⟩
      rcases f with ⟨f,c⟩
      have hef : e = f := h.1
      subst f
      rintro z ⟨t,rfl⟩
      exact mem_iUnion.mpr ⟨e,⟨_,rfl⟩⟩

/-- The selected geometric cycles cover exactly all original graph edges.
Isolated original vertices are intentionally absent from this equality. -/
theorem componentCycle_realizations_cover_edges (G : EmbeddedGraph S)
    (hdegree : ∀ p, (incidences G.initial G.terminal p).Nonempty →
      (incidences G.initial G.terminal p).ncard = 2) :
    let h := doubleSubdivision_isCycles G.initial G.terminal hdegree
    (⋃ c : NonisolatedComponent (doubleSubdivision G.initial G.terminal),
      range (realizedCyclePath G (componentCycle h c).chain)) = ⋃ e, range (G.edge e) := by
  dsimp only
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨c,hc⟩ := mem_iUnion.mp hz
    rw [realizedCyclePath_range] at hc
    obtain ⟨i,hi⟩ := mem_iUnion.mp hc
    exact subdivisionPath_range_subset_edges G _ hi
  · intro z hz
    obtain ⟨e,he⟩ := mem_iUnion.mp hz
    obtain ⟨c,hc,_⟩ := doubleSubdivision_original_edge_partition
      G.initial G.terminal hdegree e
    obtain ⟨hleft,hmiddle,hright⟩ :=
      (doubleSubdivision_cycle_contains_three_pieces G.initial G.terminal hdegree c e).mp hc
    apply mem_iUnion.mpr
    refine ⟨c,?_⟩
    rw [three_subdivision_pieces_cover G e] at he
    rcases he with (he | he) | he
    · exact subdivisionPath_subset_componentCycle G _ hleft he
    · exact subdivisionPath_subset_componentCycle G _ hmiddle he
    · exact subdivisionPath_subset_componentCycle G _ hright he

/-- A nonempty degree-two finite embedded multigraph, with loops counted by
two endpoint incidences, is realized by a positive finite family of disjoint
injectively parametrized circles exhausting all its edge traces. This is the
topological part of the regional boundary construction; degree two still has
to be derived for the actual regional subgraph, and smooth germs added. -/
theorem finite_topological_cycle_family (G : EmbeddedGraph S) (hne : 0 < G.edgeCount)
    (hdegree : ∀ p, (incidences G.initial G.terminal p).Nonempty →
      (incidences G.initial G.terminal p).ncard = 2) :
    ∃ (n : ℕ) (f : Fin n → C(ParameterCircle, M)), 1 ≤ n ∧
      (∀ i, Function.Injective (f i)) ∧
      Pairwise (fun i j => Disjoint (range (f i)) (range (f j))) ∧
      (⋃ i, range (f i)) = ⋃ e, range (G.edge e) := by
  classical
  let H := doubleSubdivision G.initial G.terminal
  let C := NonisolatedComponent H
  let : Finite C := finite_nonisolatedComponents H
  let : Fintype C := Fintype.ofFinite C
  let : Nonempty (Fin G.edgeCount) := ⟨⟨0,hne⟩⟩
  let : Nonempty C := doubleSubdivision_nonempty_cycles G.initial G.terminal
  let h := doubleSubdivision_isCycles G.initial G.terminal hdegree
  let enum : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  let f : C → C(ParameterCircle, M) := fun c =>
    closeInterval (realizedCyclePath G (componentCycle h c).chain).toContinuousMap
      (realizedCyclePath_closed G (componentCycle h c).chain)
  have hf (c : C) : range (f c) = range (realizedCyclePath G (componentCycle h c).chain) :=
    closeInterval_range _ _
  refine ⟨Fintype.card C,f ∘ enum,Fintype.card_pos,?_,?_,?_⟩
  · intro i
    exact closeInterval_injective _
      (realizedCyclePath_closed G (componentCycle h (enum i)).chain)
      (realizedCyclePath_halfOpen_injective G (componentCycle h (enum i)).chain)
  · intro i j hij
    change Disjoint (range (f (enum i))) (range (f (enum j)))
    rw [hf,hf]
    exact componentCycle_realizations_disjoint G hdegree
      (fun heq => hij (enum.injective heq))
  · change (⋃ i, range (f (enum i))) = _
    rw [enum.surjective.iUnion_comp (fun c => range (f c))]
    simp_rw [hf]
    exact componentCycle_realizations_cover_edges G hdegree

end TopologicalCycleFamily
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles

/-- Positive affine changes of speed preserve regular noncuspidal joins.
This supplies the speed changes in a finite path concatenation. -/
theorem RegularJoinAt.affine {f : ℝ → Plane} {s t a b : ℝ}
    (h : RegularJoinAt f s) (hb : 0 < b) (hst : b*t+a = s) :
    RegularJoinAt (fun x => f (b*x+a)) t := by
  obtain ⟨δ,l,r,hδ,hl,hr,hel,her,hnl,hnr,hn⟩ := h
  let η := δ / b
  have hη : 0 < η := div_pos hδ hb
  have hbη : b * η = δ := mul_div_cancel₀ δ hb.ne'
  have hmap : MapsTo (fun x : ℝ => b*x+a) (Ioo (t-η) (t+η))
      (Ioo (s-δ) (s+δ)) := by
    intro x hx
    constructor <;> nlinarith [mul_lt_mul_of_pos_left hx.1 hb,
      mul_lt_mul_of_pos_left hx.2 hb]
  have hd (F : ℝ → Plane) :
      deriv (fun x => F (b*x+a)) t = b • deriv F s := by
    calc
      _ = b • deriv (fun y => F (y+a)) (b*t) := deriv_comp_mul_left b _ t
      _ = _ := by rw [deriv_comp_add_const,hst]
  refine ⟨η,(fun x => l (b*x+a)),(fun x => r (b*x+a)),hη,
    hl.comp (by fun_prop) hmap,hr.comp (by fun_prop) hmap,?_,?_,?_,?_,?_⟩
  · intro x hx
    apply hel
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 hb.le,
      mul_le_mul_of_nonneg_left hx.2 hb.le]
  · intro x hx
    apply her
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 hb.le,
      mul_le_mul_of_nonneg_left hx.2 hb.le]
  · rw [hd]
    exact smul_ne_zero hb.ne' hnl
  · rw [hd]
    exact smul_ne_zero hb.ne' hnr
  · simpa only [hd,NormedSpace.normalize_smul_of_pos hb] using hn

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
section OpenEdgeNeighborhood
variable {M : Type*} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- Finite graph geometry isolates every open edge from all other edges and
vertices by an actual ambient open neighborhood. Both ends of a loop are
excluded. This is a local input for deriving regional frontier saturation. -/
theorem open_edge_neighborhood (G : EmbeddedGraph S) (i : Fin G.edgeCount)
    (t : unitInterval) (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1) :
    ∃ O : Set M, IsOpen O ∧ G.edge i t ∈ O ∧
      O ∩ G.carrier = O ∩ range (openParameterMap (G.edge i)) := by
  let := S.topologicalManifold.hausdorff
  let K : Set M := range G.vertex ∪
    ⋃ j : {j : Fin G.edgeCount // j ≠ i}, range (G.edge j.val)
  have hK : IsClosed K :=
    ((Set.finite_range G.vertex).isCompact.union
      (isCompact_iUnion (fun j : {j : Fin G.edgeCount // j ≠ i} =>
        isCompact_range (G.edge j.val).continuous))).isClosed
  have hparam {j : Fin G.edgeCount} {q : unitInterval}
      (hq : G.edge j q ∉ range G.vertex) : 0 < (q : ℝ) ∧ (q : ℝ) < 1 := by
    have hq' : q ∈ G.edge j ⁻¹' (range G.vertex)ᶜ := hq
    rwa [EmbeddedGraph.edge_preimage_compl_vertices G j] at hq'
  have hp : G.edge i t ∉ K := by
    rintro (hp | hp)
    · exact G.avoids_vertices i t ht.1 ht.2 hp
    · obtain ⟨j,q,hq⟩ := mem_iUnion.mp hp
      have hqv : G.edge j.val q ∉ range G.vertex := by
        rw [hq]
        exact G.avoids_vertices i t ht.1 ht.2
      exact Set.disjoint_left.mp (G.disjoint_open_edges j.property.symm)
        ⟨t,ht,rfl⟩ ⟨q,hparam hqv,hq⟩
  refine ⟨Kᶜ,hK.isOpen_compl,hp,?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hx,hxg⟩
    have hxv : x ∉ range G.vertex := fun hv => hx (Or.inl hv)
    rcases hxg with hxg | hxg
    · exact False.elim (hxv hxg)
    · obtain ⟨j,q,hq⟩ := mem_iUnion.mp hxg
      have hji : j = i := by
        by_contra hne
        exact hx (Or.inr (mem_iUnion.mpr ⟨⟨j,hne⟩,q,hq⟩))
      subst j
      have hqv : G.edge i q ∉ range G.vertex := by rwa [hq]
      refine ⟨hx,⟨⟨q,hparam hqv⟩,?_⟩⟩
      exact hq
  · rintro x ⟨hx,q,rfl⟩
    exact ⟨hx,Or.inr (mem_iUnion.mpr ⟨i,⟨⟨q,q.property.1.le,q.property.2.le⟩,rfl⟩⟩)⟩

end OpenEdgeNeighborhood
end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction
section ActualOpenEdge
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M} {D : P202Specs.SmoothSurfaceDouble.SmoothDouble S}
variable {s : Bool}
variable {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
variable {B : CompactSmoothSeam D.manifold}
variable {T : TransverseDiskArrangement D.manifold
  (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B}

/-- Near an actual open graph edge point the entire restricted arrangement
is precisely one actual source circle or seam. This follows from finite
embedded-graph geometry and provenance, without a regional saturation input. -/
theorem graphGeometry_open_edge_curve_neighborhood
    (H : ArrangementGraphGeometryData S D s T) (i : Fin H.graph.edgeCount)
    (t : unitInterval) (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1) :
    ∃ (k : Option (Fin T.count)) (O : Set M), IsOpen O ∧ H.graph.edge i t ∈ O ∧
      O ∩ H.graph.carrier = O ∩
        (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
          arrangementCurve B.carrier T.disk T.radius k) := by
  obtain ⟨O,hO,hp,hgraph⟩ := BoundaryCycles.open_edge_neighborhood H.graph i t ht
  obtain ⟨k,hk⟩ := H.edge_curve i
  refine ⟨k,O,hO,hp,Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    have hx' := hgraph ▸ hx
    obtain ⟨q,hq⟩ := hx'.2
    refine ⟨hx.1,?_⟩
    rw [← hq]
    exact hk ⟨q,q.property.1.le,q.property.2.le⟩
  · rintro x ⟨hx,hk⟩
    refine ⟨hx,?_⟩
    rw [H.carrier_eq]
    change P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s x ∈ arrangementCarrier T
    rw [Arrangement.carrier_eq_iUnion T]
    exact mem_iUnion.mpr ⟨k,hk⟩

end ActualOpenEdge
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction
variable {kind : ModelKind} {M : Type*} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M}

/-- Regularity in one atlas chart implies regularity in every atlas chart.
The inverse transition detects nonzero velocity, including for a manifold
modeled on a half-space. -/
theorem regular_coordinate_change (c : C(unitInterval, M)) (t : ℝ)
    (d e : ModelChart 2 kind M) (hd : d ∈ S.smoothStructure.val)
    (he : e ∈ S.smoothStructure.val)
    (htd : IccExtend zero_le_one c t ∈ d.source)
    (hte : IccExtend zero_le_one c t ∈ e.source)
    (hsm : ContDiffAt ℝ ∞ (fun r => coordinates d (IccExtend zero_le_one c r)) t)
    (hn : deriv (fun r => coordinates d (IccExtend zero_le_one c r)) t ≠ 0) :
    ContDiffAt ℝ ∞ (fun r => coordinates e (IccExtend zero_le_one c r)) t ∧
      deriv (fun r => coordinates e (IccExtend zero_le_one c r)) t ≠ 0 := by
  let f : ℝ → M := IccExtend zero_le_one c
  have hf : Continuous f := c.continuous.Icc_extend'
  obtain ⟨U,hU,hpU,K,hK,hKrep⟩ := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 d hd e he) htd hte
  obtain ⟨V,hV,hpV,L,hL,hLrep⟩ := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d hd) hte htd
  let Kp : Plane → Plane := fun z => toPlane (K (toPlane.symm z))
  let Lp : Plane → Plane := fun z => toPlane (L (toPlane.symm z))
  have hKp : ContDiffAt ℝ ∞ Kp (coordinates d (f t)) := by
    have hk : ContDiffAt ℝ ∞ K (toPlane.symm (coordinates d (f t))) := by
      simpa only [coordinates,toPlane.symm_apply_apply] using hK.contDiffAt (hU.mem_nhds hpU)
    exact toPlane.contDiff.contDiffAt.comp _
      (hk.comp _ toPlane.symm.contDiff.contDiffAt)
  have hLp : ContDiffAt ℝ ∞ Lp (coordinates e (f t)) := by
    have hl : ContDiffAt ℝ ∞ L (toPlane.symm (coordinates e (f t))) := by
      simpa only [coordinates,toPlane.symm_apply_apply] using hL.contDiffAt (hV.mem_nhds hpV)
    exact toPlane.contDiff.contDiffAt.comp _
      (hl.comp _ toPlane.symm.contDiff.contDiffAt)
  have hforward : (fun r => Kp (coordinates d (f r))) =ᶠ[𝓝 t]
      (fun r => coordinates e (f r)) := by
    filter_upwards [hKrep.comp_tendsto hf.continuousAt] with r hr
    simpa only [Kp,coordinates,toPlane.symm_apply_apply,id_eq,Function.comp_def] using congrArg toPlane hr
  have hbackward : (fun r => Lp (coordinates e (f r))) =ᶠ[𝓝 t]
      (fun r => coordinates d (f r)) := by
    filter_upwards [hLrep.comp_tendsto hf.continuousAt] with r hr
    simpa only [Lp,coordinates,toPlane.symm_apply_apply,id_eq,Function.comp_def] using congrArg toPlane hr
  have hcomp : ContDiffAt ℝ ∞ (fun r => Kp (coordinates d (f r))) t :=
    ContDiffAt.comp (g := Kp) (f := fun r => coordinates d (f r)) t hKp hsm
  have hnew : ContDiffAt ℝ ∞ (fun r => coordinates e (f r)) t :=
    hcomp.congr_of_eventuallyEq hforward.symm
  refine ⟨hnew,?_⟩
  intro hzero
  apply hn
  have hderiv := (hLp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (hnew.differentiableAt (by simp)).hasDerivAt
  calc
    deriv (fun r => coordinates d (IccExtend zero_le_one c r)) t =
        deriv (fun r => Lp (coordinates e (f r))) t := hbackward.deriv_eq.symm
    _ = (fderiv ℝ Lp (coordinates e (f t)))
        (deriv (fun r => coordinates e (f r)) t) := hderiv.deriv
    _ = 0 := by rw [hzero,map_zero]

/-- Every open-edge point is smooth and regular in any original chart. -/
theorem RegularOpenEdge.in_chart {c : C(unitInterval, M)}
    (hc : RegularOpenEdge S c) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hte : c ⟨t,ht.1.le,ht.2.le⟩ ∈ e.source) :
    ContDiffAt ℝ ∞ (fun r => coordinates e (IccExtend zero_le_one c r)) t ∧
      deriv (fun r => coordinates e (IccExtend zero_le_one c r)) t ≠ 0 := by
  obtain ⟨d,hd,htd,hsm,hn⟩ := hc t ht
  apply regular_coordinate_change c t d e hd he _ _ hsm hn
  · simpa only [IccExtend_of_mem zero_le_one c ⟨ht.1.le,ht.2.le⟩] using htd
  · simpa only [IccExtend_of_mem zero_le_one c ⟨ht.1.le,ht.2.le⟩] using hte

/-- Open-edge regularity and the two endpoint extension conditions together
supply regular coordinate germs at every parameter in every original chart. -/
theorem regularCoordinateGerms_of_regular_edges {c : C(unitInterval, M)}
    (hopen : RegularOpenEdge S c) (hends : RegularEdgeEndpoints S c) :
    RegularCoordinateGerms S c := by
  intro t e he hte
  by_cases h0 : t = 0
  · exact hends t (Or.inl h0) e he hte
  by_cases h1 : t = 1
  · exact hends t (Or.inr h1) e he hte
  have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
    intro hh; exact h0 (Subtype.ext hh.symm))
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
    intro hh; exact h1 (Subtype.ext hh))
  let f : ℝ → M := IccExtend zero_le_one c
  let U : Set ℝ := Ioo (0 : ℝ) 1 ∩ f ⁻¹' e.source
  have hU : IsOpen U := isOpen_Ioo.inter (e.open_source.preimage c.continuous.Icc_extend')
  have htU : (t : ℝ) ∈ U := by
    refine ⟨⟨ht0,ht1⟩,?_⟩
    simpa only [f,mem_preimage,IccExtend_of_mem zero_le_one c t.property] using hte
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds htU)
  have hsm : ContDiffOn ℝ ∞ (fun r => coordinates e (f r)) U := by
    apply hU.contDiffOn_iff.mpr
    intro r hr
    apply (RegularOpenEdge.in_chart hopen r hr.1 e he _).1
    simpa only [f,mem_preimage,IccExtend_of_mem zero_le_one c ⟨hr.1.1.le,hr.1.2.le⟩]
      using hr.2
  refine ⟨δ,(fun r => coordinates e (f r)),hδ,hsm.mono ?_,?_,?_⟩
  · intro r hr
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [hr.1,hr.2]
  · exact (RegularOpenEdge.in_chart hopen t ⟨ht0,ht1⟩ e he hte).2
  · intro q hq
    have hqU := hball (show (q : ℝ) ∈ Metric.ball (t : ℝ) δ by
      simpa only [Metric.mem_ball,Real.dist_eq] using hq)
    simpa only [f,mem_preimage,IccExtend_of_mem zero_le_one c q.property]
      using And.intro hqU.2 (rfl : coordinates e (f q) = coordinates e (f q))

/-- The actual graph output has genuine regular coordinate germs in every
original chart at all parameters, including artificial subdivision points. -/
theorem graphGeometry_regularCoordinateGerms
    {D : P202Specs.SmoothSurfaceDouble.SmoothDouble S} {s : Bool}
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    {T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B}
    (H : ArrangementGraphGeometryData S D s T) (i : Fin H.graph.edgeCount) :
    RegularCoordinateGerms S (H.graph.edge i) :=
  regularCoordinateGerms_of_regular_edges (H.graph.regular i) (H.endpoint_germs i)

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {x y z : Plane}

theorem RegularJoinAt.path_trans_left (p : Path x y) (q : Path y z) {t : ℝ}
    (ht : t < 1/2) (h : RegularJoinAt p.extend (2*t)) :
    RegularJoinAt (p.trans q).extend t := by
  apply (h.affine (by norm_num : (0 : ℝ) < 2) (by ring : 2*t+0=2*t)).congr
  have hnear : ∀ᶠ s : ℝ in 𝓝 t, s < 1/2 :=
    isOpen_Iio.mem_nhds ht
  filter_upwards [hnear] with s hs
  simpa only [add_zero] using (Path.extend_trans_of_le_half p q hs.le).symm

theorem RegularJoinAt.path_trans_right (p : Path x y) (q : Path y z) {t : ℝ}
    (ht : 1/2 < t) (h : RegularJoinAt q.extend (2*t-1)) :
    RegularJoinAt (p.trans q).extend t := by
  apply (h.affine (by norm_num : (0 : ℝ) < 2) (by ring : 2*t+(-1)=2*t-1)).congr
  have hnear : ∀ᶠ s : ℝ in 𝓝 t, 1/2 < s :=
    isOpen_Ioi.mem_nhds ht
  filter_upwards [hnear] with s hs
  simpa only [sub_eq_add_neg] using (Path.extend_trans_of_half_le p q hs.le).symm


/-- The terminal germ of the first piece and initial germ of the second piece
are regular and have nonopposite directed unit tangents. -/
def RegularEndpointJoin (f g : ℝ → Plane) : Prop :=
  ∃ (δ : ℝ) (l r : ℝ → Plane), 0 < δ ∧
    ContDiffOn ℝ ∞ l (Ioo (1 - δ) (1 + δ)) ∧
    ContDiffOn ℝ ∞ r (Ioo (-δ) δ) ∧
    EqOn l f (Icc (1 - δ) 1) ∧ EqOn r g (Icc 0 δ) ∧
    deriv l 1 ≠ 0 ∧ deriv r 0 ≠ 0 ∧
    NormedSpace.normalize (deriv l 1) ≠ -NormedSpace.normalize (deriv r 0)

theorem regularEndpointJoin_self_iff (f : ℝ → Plane) :
    RegularEndpointJoin f f ↔ RegularClosingGerms f := Iff.rfl

/-- The joining parameter of two paths inherits exactly the two directed
endpoint germs, with a positive factor of two in their velocities. -/
theorem RegularEndpointJoin.path_trans (p : Path x y) (q : Path y z)
    (h : RegularEndpointJoin p.extend q.extend) :
    RegularJoinAt (p.trans q).extend (1/2) := by
  obtain ⟨δ,l,r,hδ,hl,hr,hel,her,hnl,hnr,hn⟩ := h
  let η : ℝ := δ/2
  have hη : 0 < η := half_pos hδ
  have hderiv_l : deriv (fun s => l (2*s)) (1/2) = (2:ℝ) • deriv l 1 := by
    rw [deriv_comp_mul_left]
    norm_num
  have hderiv_r : deriv (fun s => r (2*s-1)) (1/2) = (2:ℝ) • deriv r 0 := by
    calc
      _ = (2:ℝ) • deriv (fun s => r (s + (-1))) (2*(1/2)) :=
        deriv_comp_mul_left 2 _ (1/2)
      _ = _ := by rw [deriv_comp_add_const]; norm_num
  refine ⟨η,(fun s => l (2*s)),(fun s => r (2*s-1)),hη,?_,?_,?_,?_,?_,?_,?_⟩
  · apply hl.comp (by fun_prop)
    intro s hs
    dsimp [η] at hs
    constructor <;> linarith [hs.1,hs.2]
  · apply hr.comp (by fun_prop)
    intro s hs
    dsimp [η] at hs
    constructor <;> linarith [hs.1,hs.2]
  · intro s hs
    apply (hel ?_).trans
    · exact (Path.extend_trans_of_le_half p q hs.2).symm
    · dsimp [η] at hs
      constructor <;> linarith [hs.1,hs.2]
  · intro s hs
    apply (her ?_).trans
    · exact (Path.extend_trans_of_half_le p q hs.1).symm
    · dsimp [η] at hs
      constructor <;> linarith [hs.1,hs.2]
  · rw [hderiv_l]
    exact smul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hnl
  · rw [hderiv_r]
    exact smul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hnr
  · simpa only [hderiv_l,hderiv_r,
      NormedSpace.normalize_smul_of_pos (by norm_num : (0:ℝ)<2)] using hn

/-- Interior regularity survives concatenation when its actual adjoining
endpoint germs are compatible. -/
theorem regularJoinAt_path_trans (p : Path x y) (q : Path y z)
    (hp : ∀ t ∈ Ioo (0:ℝ) 1, RegularJoinAt p.extend t)
    (hq : ∀ t ∈ Ioo (0:ℝ) 1, RegularJoinAt q.extend t)
    (hjoin : RegularEndpointJoin p.extend q.extend) :
    ∀ t ∈ Ioo (0:ℝ) 1, RegularJoinAt (p.trans q).extend t := by
  intro t ht
  rcases lt_trichotomy t (1/2) with hleft | rfl | hright
  · apply RegularJoinAt.path_trans_left p q hleft
    apply hp
    constructor <;> linarith [ht.1,ht.2]
  · exact hjoin.path_trans p q
  · apply RegularJoinAt.path_trans_right p q hright
    apply hq
    constructor <;> linarith [ht.1,ht.2]


/-- Smoothness away from the new midpoint is inherited under the actual
positive affine reparameterizations used by Path.trans. -/
theorem contDiffAt_path_trans_left (p : Path x y) (q : Path y z) {t : ℝ}
    (ht : t < 1/2) (h : ContDiffAt ℝ ∞ p.extend (2*t)) :
    ContDiffAt ℝ ∞ (p.trans q).extend t := by
  have hc : ContDiffAt ℝ ∞ (fun s : ℝ => p.extend (2*s)) t :=
    h.comp t (by fun_prop)
  apply hc.congr_of_eventuallyEq
  have hnear : ∀ᶠ s : ℝ in 𝓝 t, s < 1/2 := isOpen_Iio.mem_nhds ht
  filter_upwards [hnear] with s hs
  exact Path.extend_trans_of_le_half p q hs.le

theorem contDiffAt_path_trans_right (p : Path x y) (q : Path y z) {t : ℝ}
    (ht : 1/2 < t) (h : ContDiffAt ℝ ∞ q.extend (2*t-1)) :
    ContDiffAt ℝ ∞ (p.trans q).extend t := by
  have hc : ContDiffAt ℝ ∞ (fun s : ℝ => q.extend (2*s-1)) t :=
    h.comp t (by fun_prop)
  apply hc.congr_of_eventuallyEq
  have hnear : ∀ᶠ s : ℝ in 𝓝 t, 1/2 < s := isOpen_Ioi.mem_nhds ht
  filter_upwards [hnear] with s hs
  exact Path.extend_trans_of_half_le p q hs.le

/-- Joining two finite piecewise smooth paths introduces just one additional
join and affinely moves the old finite join sets. -/
theorem contDiffAt_path_trans_off_joins (p : Path x y) (q : Path y z)
    (J K : Finset ℝ)
    (hp : ∀ t ∈ Ioo (0:ℝ) 1, t ∉ J → ContDiffAt ℝ ∞ p.extend t)
    (hq : ∀ t ∈ Ioo (0:ℝ) 1, t ∉ K → ContDiffAt ℝ ∞ q.extend t) :
    ∀ t ∈ Ioo (0:ℝ) 1,
      t ∉ insert (1/2) (J.image (fun s => s/2) ∪ K.image (fun s => (s+1)/2)) →
      ContDiffAt ℝ ∞ (p.trans q).extend t := by
  classical
  intro t ht hnot
  have hneq : t ≠ 1/2 := by
    intro heq
    exact hnot (heq ▸ Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne hneq with hleft | hright
  · apply contDiffAt_path_trans_left p q hleft
    apply hp
    · constructor <;> linarith [ht.1,ht.2]
    · intro hmem
      apply hnot
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨2*t,hmem,by ring⟩
  · apply contDiffAt_path_trans_right p q hright
    apply hq
    · constructor <;> linarith [ht.1,ht.2]
    · intro hmem
      apply hnot
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨2*t-1,hmem,by ring⟩


variable {w a b : Plane}

/-- The terminal germ of a concatenation comes from its last piece. -/
theorem RegularEndpointJoin.path_trans_terminal
    (p : Path x y) (q : Path y z) (r : Path a b)
    (h : RegularEndpointJoin q.extend r.extend) :
    RegularEndpointJoin (p.trans q).extend r.extend := by
  obtain ⟨δ,l,g,hδ,hl,hg,hel,heg,hnl,hng,hn⟩ := h
  let η : ℝ := min (δ/2) (1/4)
  have hη : 0 < η := lt_min (half_pos hδ) (by norm_num)
  have hηδ : η ≤ δ/2 := min_le_left _ _
  have hηquarter : η ≤ 1/4 := min_le_right _ _
  have hderiv : deriv (fun s => l (2*s-1)) 1 = (2:ℝ) • deriv l 1 := by
    calc
      _ = (2:ℝ) • deriv (fun s => l (s + (-1))) (2*1) :=
        deriv_comp_mul_left 2 _ 1
      _ = _ := by rw [deriv_comp_add_const]; norm_num
  refine ⟨η,(fun s => l (2*s-1)),g,hη,?_,?_,?_,?_,?_,hng,?_⟩
  · apply hl.comp (by fun_prop)
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  · apply hg.mono
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  · intro s hs
    apply (hel ?_).trans
    · exact (Path.extend_trans_of_half_le p q (by linarith [hs.1])).symm
    · constructor <;> linarith [hs.1,hs.2]
  · intro s hs
    apply heg
    constructor <;> linarith [hs.1,hs.2]
  · rw [hderiv]
    exact smul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hnl
  · simpa only [hderiv,
      NormedSpace.normalize_smul_of_pos (by norm_num : (0:ℝ)<2)] using hn

/-- The initial germ of a concatenation comes from its first piece. -/
theorem RegularEndpointJoin.path_trans_initial
    (p : Path a b) (q : Path x y) (r : Path y z)
    (h : RegularEndpointJoin p.extend q.extend) :
    RegularEndpointJoin p.extend (q.trans r).extend := by
  obtain ⟨δ,l,g,hδ,hl,hg,hel,heg,hnl,hng,hn⟩ := h
  let η : ℝ := min (δ/2) (1/4)
  have hη : 0 < η := lt_min (half_pos hδ) (by norm_num)
  have hηδ : η ≤ δ/2 := min_le_left _ _
  have hηquarter : η ≤ 1/4 := min_le_right _ _
  have hderiv : deriv (fun s => g (2*s)) 0 = (2:ℝ) • deriv g 0 := by
    rw [deriv_comp_mul_left]
    norm_num
  refine ⟨η,l,(fun s => g (2*s)),hη,?_,?_,?_,?_,hnl,?_,?_⟩
  · apply hl.mono
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  · apply hg.comp (by fun_prop)
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  · intro s hs
    apply hel
    constructor <;> linarith [hs.1,hs.2]
  · intro s hs
    apply (heg ?_).trans
    · exact (Path.extend_trans_of_le_half q r (by linarith [hs.2])).symm
    · constructor <;> linarith [hs.1,hs.2]
  · rw [hderiv]
    exact smul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hng
  · simpa only [hderiv,
      NormedSpace.normalize_smul_of_pos (by norm_num : (0:ℝ)<2)] using hn

/-- The closing join of a two-piece closed traversal depends on the last
piece's terminal germ and the first piece's initial germ. -/
theorem regularClosingGerms_path_trans (p : Path x y) (q : Path y x)
    (h : RegularEndpointJoin q.extend p.extend) :
    RegularClosingGerms (p.trans q).extend := by
  exact (h.path_trans_terminal p q p).path_trans_initial (p.trans q) p q


/-- The finite concatenation retains its last piece's terminal germ. -/
theorem RegularEndpointJoin.concatenateNonempty_terminal
    (n : ℕ) (p : Fin (n+2) → Plane)
    (F : (i : Fin (n+1)) → Path (p i.castSucc) (p i.succ))
    (q : Path a b)
    (h : RegularEndpointJoin (F (Fin.last n)).extend q.extend) :
    RegularEndpointJoin
      (concatenateNonempty (n+1) (by omega) p F).extend q.extend := by
  cases n with
  | zero =>
    change RegularEndpointJoin (F 0).extend q.extend at h
    simpa only [concatenateNonempty, Path.cast_coe, Path.extend] using h
  | succ n =>
    rw [concatenateNonempty]
    exact h.path_trans_terminal _ _ q

/-- The finite concatenation retains its first piece's initial germ. -/
theorem RegularEndpointJoin.concatenateNonempty_initial
    (n : ℕ) (p : Fin (n+2) → Plane)
    (F : (i : Fin (n+1)) → Path (p i.castSucc) (p i.succ))
    (q : Path a b)
    (h : RegularEndpointJoin q.extend (F 0).extend) :
    RegularEndpointJoin q.extend
      (concatenateNonempty (n+1) (by omega) p F).extend := by
  induction n with
  | zero => simpa only [concatenateNonempty, Path.cast_coe, Path.extend, Fin.last_zero] using h
  | succ n ih =>
    rw [concatenateNonempty]
    exact (ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) h).path_trans_initial _ _ _

/-- A finite traversal of regular pieces has regular interior joins exactly
when each consecutive pair has compatible directed endpoint germs. -/
theorem regularJoinAt_concatenateNonempty (n : ℕ) (p : Fin (n+2) → Plane)
    (F : (i : Fin (n+1)) → Path (p i.castSucc) (p i.succ))
    (hF : ∀ i t, t ∈ Ioo (0:ℝ) 1 → RegularJoinAt (F i).extend t)
    (hjoin : ∀ i : Fin n,
      RegularEndpointJoin (F i.castSucc).extend (F i.succ).extend) :
    ∀ t ∈ Ioo (0:ℝ) 1,
      RegularJoinAt (concatenateNonempty (n+1) (by omega) p F).extend t := by
  induction n with
  | zero =>
    simpa only [concatenateNonempty, Path.cast_coe, Path.extend, Fin.last_zero] using hF 0
  | succ n ih =>
    rw [concatenateNonempty]
    apply regularJoinAt_path_trans
    · apply ih (p ∘ Fin.castSucc) (fun i => F i.castSucc)
      · exact fun i t ht => hF i.castSucc t ht
      · intro i
        simpa only [Fin.castSucc_succ] using hjoin i.castSucc
    · exact hF (Fin.last (n+1))
    · apply RegularEndpointJoin.concatenateNonempty_terminal
      exact hjoin (Fin.last n)


/-- Finitely many smoothness exceptions remain finite under the actual
nonempty concatenation. The recursively introduced midpoint is retained. -/
theorem contDiffAt_concatenateNonempty_off_finite_joins
    (n : ℕ) (p : Fin (n+2) → Plane)
    (F : (i : Fin (n+1)) → Path (p i.castSucc) (p i.succ))
    (hF : ∀ i, ∃ J : Finset ℝ, ∀ t ∈ Ioo (0:ℝ) 1,
      t ∉ J → ContDiffAt ℝ ∞ (F i).extend t) :
    ∃ J : Finset ℝ, ∀ t ∈ Ioo (0:ℝ) 1, t ∉ J →
      ContDiffAt ℝ ∞ (concatenateNonempty (n+1) (by omega) p F).extend t := by
  induction n with
  | zero =>
    simpa only [concatenateNonempty, Path.cast_coe, Path.extend] using hF 0
  | succ n ih =>
    obtain ⟨J,hJ⟩ := ih (p ∘ Fin.castSucc) (fun i => F i.castSucc)
      (fun i => hF i.castSucc)
    obtain ⟨K,hK⟩ := hF (Fin.last (n+1))
    refine ⟨insert (1/2) (J.image (fun s => s/2) ∪ K.image (fun s => (s+1)/2)),?_⟩
    rw [concatenateNonempty]
    exact contDiffAt_path_trans_off_joins _ _ J K hJ hK

/-- The closing germ of a finite traversal is determined by its final and
initial pieces; their positive speed changes preserve noncuspidality. -/
theorem regularClosingGerms_concatenateNonempty
    (n : ℕ) (p : Fin (n+2) → Plane)
    (F : (i : Fin (n+1)) → Path (p i.castSucc) (p i.succ))
    (h : RegularEndpointJoin (F (Fin.last n)).extend (F 0).extend) :
    RegularClosingGerms (concatenateNonempty (n+1) (by omega) p F).extend := by
  exact (h.concatenateNonempty_terminal n p F (F 0)).concatenateNonempty_initial
    n p F _


/-- A genuinely closed finite concatenation of simple regular pieces with
compatible consecutive and closing germs defines the shared regular Jordan
curve, with its exact realized trace. -/
theorem regularJordanCurveOfNonemptyConcatenation
    (n : ℕ) (p : Fin (n+2) → Plane)
    (F : (i : Fin (n+1)) → Path (p i.castSucc) (p i.succ))
    (hclosed : p 0 = p (Fin.last (n+1)))
    (hinj : InjOn (concatenateNonempty (n+1) (by omega) p F)
      {t : unitInterval | (t:ℝ)<1})
    (hsm : ∀ i, ∃ J : Finset ℝ, ∀ t ∈ Ioo (0:ℝ) 1,
      t ∉ J → ContDiffAt ℝ ∞ (F i).extend t)
    (hreg : ∀ i t, t ∈ Ioo (0:ℝ) 1 → RegularJoinAt (F i).extend t)
    (hjoin : ∀ i : Fin n,
      RegularEndpointJoin (F i.castSucc).extend (F i.succ).extend)
    (hclosing : RegularEndpointJoin (F (Fin.last n)).extend (F 0).extend) :
    ∃ c : RegularJordanCurve,
      c.trace = ⋃ i, range (F i) := by
  let q := concatenateNonempty (n+1) (by omega) p F
  have hqclosed : q 0 = q 1 :=
    q.source.trans (hclosed.trans q.target.symm)
  obtain ⟨J,hJ⟩ := contDiffAt_concatenateNonempty_off_finite_joins n p F hsm
  let c : RegularJordanCurve := regularJordanCurveOfInterval q.toContinuousMap
    hqclosed hinj J hJ (regularJoinAt_concatenateNonempty n p F hreg hjoin)
    (regularClosingGerms_concatenateNonempty n p F hclosing)
  refine ⟨c,?_⟩
  exact (regularJordanCurveOfInterval_trace _ _ _ _ _ _ _).trans
    (concatenateNonempty_range _ _ _ _)

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction
namespace NormalSectors

theorem mem_closure_chamber_of_weak_signs (J : Set (Fin 2)) (r : ℝ)
    (σ : Fin 2 → Bool) {z : Plane} (hz : z ∈ Metric.ball 0 r)
    (hweak : ∀ a ∈ J, if σ a then 0 ≤ z a else z a ≤ 0)
    (hne : (chamber J r σ).Nonempty) : z ∈ closure (chamber J r σ) := by
  obtain ⟨x,hx⟩ := hne
  apply closure_mono (show openSegment ℝ z x ⊆ chamber J r σ from ?_)
    (segment_subset_closure_openSegment (left_mem_segment ℝ z x))
  rintro y ⟨a,b,ha,hb,hab,rfl⟩
  refine ⟨(convex_ball (0 : Plane) r) hz hx.1 ha.le hb.le hab, mem_iInter₂.mpr ?_⟩
  intro i hi
  have hs := mem_iInter₂.mp hx.2 i hi
  have hw := hweak i hi
  change (if σ i then 0 < (a • z + b • x) i else (a • z + b • x) i < 0)
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  cases hσ : σ i <;> simp only [hσ, Bool.false_eq_true, ↓reduceIte] at hs hw ⊢
  · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le hw)
      (mul_neg_of_pos_of_neg hb hs)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le hw) (mul_pos hb hs)
end NormalSectors
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {W : SmoothManifold 2 .euclidean Y} {K : Set Y}
variable {A : Set (ModelChart 2 .euclidean Y)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)
variable {p : Y} {O : Set Y}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)

theorem normalInverse_mem_closure_image_chamber
    (f : X → Y) (C : Set X) (hC : C ⊆ f ⁻¹' normalNeighborhood T F)
    (σ : Fin 2 → Bool)
    (himage : (fun x => coordinates F.chart (f x)) '' C =
      NormalSectors.chamber (activeAxes T F) F.radius σ)
    {z : Plane} (hz : z ∈ Metric.ball 0 F.radius)
    (hweak : ∀ a ∈ activeAxes T F, if σ a then 0 ≤ z a else z a ≤ 0)
    (hne : C.Nonempty) : normalInverse T F z ∈ closure (f '' C) := by
  have hball : NormalSectors.chamber (activeAxes T F) F.radius σ ⊆
      Metric.ball 0 F.radius := inter_subset_left
  have hzc : z ∈ closure (NormalSectors.chamber (activeAxes T F) F.radius σ) :=
    NormalSectors.mem_closure_chamber_of_weak_signs _ _ _ hz hweak
      (himage ▸ hne.image _)
  apply ((normalInverse_continuous T F z hz).mono hball).mem_closure hzc
  rintro w hw
  rw [← himage] at hw
  obtain ⟨x,hx,rfl⟩ := hw
  refine ⟨x,hx,?_⟩
  symm
  change F.chart.symm (euclideanModelPlane.symm (euclideanModelPlane (F.chart (f x)))) = f x
  rw [Homeomorph.symm_apply_apply,F.chart.left_inv (hC hx).1]
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
namespace NormalSectors
 theorem axis_boundary_witness (J : Set (Fin 2)) (r : ℝ) (σ : Fin 2 → Bool)
    {a b : Fin 2} (hab : a ≠ b) (ha : a ∈ J)
    {x : Plane} (hx : x ∈ chamber J r σ) :
    ∃ z : Plane, z ∈ Metric.ball 0 r ∧ z b = 0 ∧ z a ≠ 0 ∧
      ∀ j ∈ J, if σ j then 0 ≤ z j else z j ≤ 0 := by
  let z : Plane := x a • axisTangent b
  have hza : z a = x a := by
    simp [z,axisTangent,toPlane,hab]
  have hzb : z b = 0 := by simp [z,axisTangent,toPlane]
  have hxn : x a ≠ 0 := by
    have h := mem_iInter₂.mp hx.2 a ha
    cases hσ : σ a <;> simp only [hσ,Bool.false_eq_true,↓reduceIte] at h
    · exact ne_of_lt h
    · exact (ne_of_gt h)
  refine ⟨z,?_,hzb,hza ▸ hxn,?_⟩
  · rw [Metric.mem_ball,dist_zero_right]
    calc
      ‖z‖ = ‖x a‖ := by simp [z,norm_smul,AxisRays.tangent_norm]
      _ ≤ ‖x‖ := PiLp.norm_apply_le x a
      _ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hx.1
  · intro j hj
    have h := mem_iInter₂.mp hx.2 j hj
    have hja : j = a ∨ j = b := by fin_cases a <;> fin_cases b <;> fin_cases j <;> simp_all
    rcases hja with hja | hjb
    · rw [hja] at h ⊢
      rw [hza]
      cases hσ : σ a <;> simp only [hσ,Bool.false_eq_true,↓reduceIte] at h ⊢ <;> exact h.le
    · rw [hjb,hzb]
      cases σ b <;> simp
end NormalSectors
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {W : SmoothManifold 2 .euclidean Y} {K : Set Y}
variable {A : Set (ModelChart 2 .euclidean Y)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)
variable {p : Y} {O : Set Y}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)

theorem activeAxes_singleton_of_copy_graph_on_curve
    (f : X → Y) (hf : IsClosedEmbedding f)
    (C : Set X) (hC : C ⊆ f ⁻¹' normalNeighborhood T F) (hne : C.Nonempty)
    (σ : Fin 2 → Bool)
    (himage : (fun x => coordinates F.chart (f x)) '' C =
      NormalSectors.chamber (activeAxes T F) F.radius σ)
    (k : Option (Fin T.count)) (a : Fin 2) (hka : F.axis k = some a)
    (hsingle : ∀ x, f x ∈ normalNeighborhood T F →
      f x ∈ arrangementCarrier T → f x ∈ arrangementCurve B.carrier T.disk T.radius k) :
    activeAxes T F = {a} := by
  apply Set.Subset.antisymm
  · intro b hb
    by_contra hab
    have hab' : a ≠ b := fun h => hab (mem_singleton_iff.mpr h.symm)
    obtain ⟨x,hx⟩ := himage ▸ hne.image (fun x => coordinates F.chart (f x))
    obtain ⟨z,hz,hzb,hza,hweak⟩ := NormalSectors.axis_boundary_witness
      (activeAxes T F) F.radius σ hab' ⟨k,hka⟩ hx
    have hzcl := normalInverse_mem_closure_image_chamber T F f C hC σ himage hz hweak hne
    have hzc : normalInverse T F z ∈ range f :=
      (hf.isClosed_range.closure_subset_iff.mpr (image_subset_range f C)) hzcl
    obtain ⟨q,hq⟩ := hzc
    have hqN : f q ∈ normalNeighborhood T F := by
      rw [hq]
      exact ⟨F.chart.map_target (normalInverse_target T F hz),
        by simpa only [mem_preimage,normalInverse_coordinates T F hz] using hz⟩
    have hqG : f q ∈ arrangementCarrier T := by
      apply (carrier_iff_axis T F hqN).mpr
      exact ⟨b,hb,by rw [hq,normalInverse_coordinates T F hz]; exact hzb⟩
    have hqk := (F.curve_eq k (f q) hqN.1 hqN.2).mp (hsingle q hqN hqG)
    obtain ⟨c,hc,hzc⟩ := hqk
    have hca : c = a := Option.some.inj (hc.symm.trans hka)
    subst c
    rw [hq,normalInverse_coordinates T F hz] at hzc
    exact hza hzc
  · rintro b rfl
    exact ⟨k,hka⟩
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {W : SmoothManifold 2 .euclidean Y} {K : Set Y}
variable {A : Set (ModelChart 2 .euclidean Y)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)
variable {p : Y} {O : Set Y}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)

theorem closure_incidence_on_single_axis
    (f : X → Y) (hf : IsEmbedding f)
    (C : Set X) (hC : C ⊆ f ⁻¹' normalNeighborhood T F) (hne : C.Nonempty)
    (σ : Fin 2 → Bool)
    (himage : (fun x => coordinates F.chart (f x)) '' C =
      NormalSectors.chamber (activeAxes T F) F.radius σ)
    (a : Fin 2) (haxes : activeAxes T F = {a})
    {q : X} (hqN : f q ∈ normalNeighborhood T F)
    (hqG : f q ∈ arrangementCarrier T) : q ∈ closure C := by
  have hqa : coordinates F.chart (f q) a = 0 := by
    obtain ⟨b,hb,hbzero⟩ := (carrier_iff_axis T F hqN).mp hqG
    have hba : b = a := by simpa only [haxes,mem_singleton_iff] using hb
    exact hba ▸ hbzero
  have hzcl := normalInverse_mem_closure_image_chamber T F f C hC σ himage hqN.2
    (by intro b hb; have hba : b = a := by simpa only [haxes,mem_singleton_iff] using hb
        rw [hba,hqa]; cases σ a <;> simp) hne
  have hinv : normalInverse T F (coordinates F.chart (f q)) = f q := by
    change F.chart.symm (euclideanModelPlane.symm (euclideanModelPlane (F.chart (f q)))) = f q
    rw [Homeomorph.symm_apply_apply,F.chart.left_inv hqN.1]
  rw [hinv] at hzcl
  rw [hf.closure_eq_preimage_closure_image]
  exact hzcl
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement
variable {kind : ModelKind} {X : Type u} [TopologicalSpace X]
variable (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
variable (s : Bool)
variable {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
variable {B : CompactSmoothSeam D.manifold}
variable (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
variable (T : TransverseDiskArrangement D.manifold
  (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)

include hB
theorem restricted_arrangement_closure_local_on_curve
    (G : Set X)
    (hG : G = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)
    (c : ConnectedComponents (Gᶜ : Set X)) {p : X}
    (hpc : p ∈ closure (componentSet Gᶜ c)) (hpG : p ∈ G)
    (k : Option (Fin T.count)) (O : Set X) (hO : IsOpen O) (hpO : p ∈ O)
    (hsingle : ∀ x ∈ O, x ∈ G →
      P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s x ∈
        arrangementCurve B.carrier T.disk T.radius k) :
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ N ⊆ O ∧
      N ∩ G ⊆ closure (componentSet Gᶜ c) := by
  subst G
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  have hf : IsClosedEmbedding f := D.copy_closedEmbedding s
  obtain ⟨V,hV,hVO⟩ := hf.isEmbedding.isInducing.isOpen_iff.mp hO
  have hpV : f p ∈ V := by change p ∈ f ⁻¹' V; rwa [hVO]
  obtain ⟨F⟩ := T.normal_forms (f p) V hV hpV
  let N := f ⁻¹' normalNeighborhood T F
  have hN : IsOpen N := (isOpen_normalNeighborhood T F).preimage hf.continuous
  have hpN : p ∈ N := mem_normalNeighborhood T F
  have hNO : N ⊆ O := by
    intro x hx
    rw [← hVO]
    exact F.neighborhood_subset hx
  obtain ⟨a,ha⟩ := (normal_copy_sector_occupancy S D s hB T F).1 c hpc
  have hlocal : N \ f ⁻¹' arrangementCarrier T = f ⁻¹'
      (normalNeighborhood T F \ arrangementCarrier T) := rfl
  obtain ⟨σ,hσ⟩ := normal_copy_component_coordinates S D s hB T F a
  let C := componentSet (N \ f ⁻¹' arrangementCarrier T) a
  have hC : C ⊆ f ⁻¹' normalNeighborhood T F :=
    fun x hx => (Components.subset _ a hx).1
  have hne : C.Nonempty := Components.nonempty _ a
  have hka_ne : F.axis k ≠ none :=
    (F.active_iff k).mpr (hsingle p hpO hpG)
  obtain ⟨b,hkb⟩ := Option.ne_none_iff_exists'.mp hka_ne
  have hsingle' : ∀ x, f x ∈ normalNeighborhood T F →
      f x ∈ arrangementCarrier T →
      f x ∈ arrangementCurve B.carrier T.disk T.radius k := by
    intro x hx hg
    exact hsingle x (hNO hx) hg
  have haxes := activeAxes_singleton_of_copy_graph_on_curve T F f hf C hC hne σ hσ k b hkb hsingle'
  refine ⟨N,hN,hpN,hNO,?_⟩
  intro q hq
  have hqcl := closure_incidence_on_single_axis T F f hf.isEmbedding C hC hne σ hσ b haxes hq.1 hq.2
  apply closure_mono inter_subset_left
  rw [ha]
  exact hqcl
end P202.SurfaceRegionConstruction
/-
Research note: the chamber closure argument uses segment_subset_closure_openSegment.
Public technical reference fetched and read at research/saturation-convex-docs.txt:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Topology.html
The search research/saturation-search.json yielded only unrelated scholarly metadata;
no paper proof was used. All theorem proofs above compiled against accepted imports.
-/

namespace P202.SurfaceRegionConstruction
open BoundaryCycles
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M} {D : P202Specs.SmoothSurfaceDouble.SmoothDouble S}
variable {s : Bool}
variable {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
variable {B : CompactSmoothSeam D.manifold}
variable {T : TransverseDiskArrangement D.manifold
  (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B}

theorem graphGeometry_open_frontier_incidence
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (H : ArrangementGraphGeometryData S D s T)
    (a : ConnectedComponents (H.graph.carrierᶜ : Set M))
    (i : Fin H.graph.edgeCount) :
    IsOpen (openParameterMap (H.graph.edge i) ⁻¹'
      frontier (componentSet H.graph.carrierᶜ a)) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  let q : unitInterval := ⟨t,t.property.1.le,t.property.2.le⟩
  have hqt : 0 < (q : ℝ) ∧ (q : ℝ) < 1 := t.property
  obtain ⟨k,O,hO,hpO,hgraph⟩ := graphGeometry_open_edge_curve_neighborhood H i q hqt
  have hpf : H.graph.edge i q ∈ frontier (componentSet H.graph.carrierᶜ a) := ht
  obtain ⟨N,hN,hpN,hNO,hNG⟩ := restricted_arrangement_closure_local_on_curve S D s hB T
    H.graph.carrier H.carrier_eq a (frontier_subset_closure hpf)
    ((H.frontiers_on_graph a ▸ hpf).2) k O hO hpO (by
      intro x hx hg
      exact (hgraph ▸ (show x ∈ O ∩ H.graph.carrier from ⟨hx,hg⟩)).2)
  have hpre : IsOpen (openParameterMap (H.graph.edge i) ⁻¹' N) :=
    hN.preimage (openParameterMap (H.graph.edge i)).continuous
  apply Filter.mem_of_superset (hpre.mem_nhds hpN)
  intro r hr
  rw [H.frontiers_on_graph]
  refine ⟨hNG ⟨hr,?_⟩,?_⟩
  all_goals exact Or.inr (mem_iUnion.mpr ⟨i,⟨⟨r,r.property.1.le,r.property.2.le⟩,rfl⟩⟩)

theorem graphGeometry_whole_edge_of_frontier_incidence
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (H : ArrangementGraphGeometryData S D s T)
    (a : ConnectedComponents (H.graph.carrierᶜ : Set M))
    (i : Fin H.graph.edgeCount)
    (hmeet : (openParameterMap (H.graph.edge i) ⁻¹'
      frontier (componentSet H.graph.carrierᶜ a)).Nonempty) :
    range (H.graph.edge i) ⊆ frontier (componentSet H.graph.carrierᶜ a) := by
  exact whole_edge_of_open_incidence (H.graph.edge i) isClosed_frontier
    (graphGeometry_open_frontier_incidence hB H a i) hmeet
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {M : Type u} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- Only the two actual interval endpoints can map to a graph vertex.
The alternatives remain separate for a self-loop. -/
theorem edge_eq_vertex_iff (G : EmbeddedGraph S) (i : Fin G.edgeCount)
    (q : unitInterval) (v : Fin G.vertexCount) :
    G.edge i q = G.vertex v ↔
      (q = 0 ∧ G.initial i = v) ∨ (q = 1 ∧ G.terminal i = v) := by
  constructor
  · intro h
    by_cases hq : q = 0
    · left
      refine ⟨hq, G.vertex_injective ?_⟩
      simpa only [hq, G.at_zero] using h
    by_cases hq' : q = 1
    · right
      refine ⟨hq', G.vertex_injective ?_⟩
      simpa only [hq', G.at_one] using h
    have hq0 : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (by
      intro heq
      apply hq
      exact Subtype.ext heq.symm)
    have hq1 : (q : ℝ) < 1 := lt_of_le_of_ne q.property.2 (by
      intro heq
      apply hq'
      exact Subtype.ext heq)
    exact False.elim (G.avoids_vertices i q hq0 hq1 ⟨v,h.symm⟩)
  · rintro (⟨rfl,hv⟩ | ⟨rfl,hv⟩)
    · rw [G.at_zero,hv]
    · rw [G.at_one,hv]

/-- Near an original vertex the finite graph consists precisely of its
incident initial and terminal tails. This keeps the two incidences of a
loop distinct, and excludes spurious nonincident edge pieces. -/
theorem vertex_tail_neighborhood (G : EmbeddedGraph S) (v : Fin G.vertexCount)
    (δ : ℝ) (hδ : 0 < δ) (_hδ' : δ < 1) :
    ∃ O : Set M, IsOpen O ∧ G.vertex v ∈ O ∧
      ∀ x ∈ O, x ∈ G.carrier ↔ x = G.vertex v ∨
        ∃ (i : Fin G.edgeCount) (q : unitInterval), G.edge i q = x ∧
          ((G.initial i = v ∧ (q : ℝ) < δ) ∨
           (G.terminal i = v ∧ 1-δ < (q : ℝ))) := by
  let := S.topologicalManifold.hausdorff
  let K : Fin G.edgeCount → Set unitInterval := fun i =>
    {q | (G.initial i = v → δ ≤ (q : ℝ)) ∧
      (G.terminal i = v → (q : ℝ) ≤ 1-δ)}
  have hK (i : Fin G.edgeCount) : IsClosed (K i) := by
    dsimp [K]
    by_cases hi : G.initial i = v <;> by_cases ht : G.terminal i = v <;>
      simp only [hi,ht,forall_true_left,forall_false,Set.ofPred_true,
        true_and,and_true]
    · exact (isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)
    · exact isClosed_le continuous_const continuous_subtype_val
    · exact isClosed_le continuous_subtype_val continuous_const
    · exact isClosed_univ
  let A : Set M := (G.vertex '' ({v}ᶜ : Set (Fin G.vertexCount))) ∪
    ⋃ i, G.edge i '' K i
  have hA : IsClosed A := by
    apply IsCompact.isClosed
    refine (Set.toFinite _).isCompact.union ?_
    exact isCompact_iUnion (fun i => (hK i).isCompact.image (G.edge i).continuous)
  have hvA : G.vertex v ∉ A := by
    rintro (⟨w,hw,hwv⟩ | hi)
    · exact hw (G.vertex_injective hwv)
    · obtain ⟨i,q,hq,hqv⟩ := mem_iUnion.mp hi
      rcases (edge_eq_vertex_iff G i q v).mp hqv with ⟨hq0,hi⟩ | ⟨hq1,ht⟩
      · have := hq.1 hi
        simp only [hq0,Set.Icc.coe_zero] at this
        linarith
      · have := hq.2 ht
        simp only [hq1,Set.Icc.coe_one] at this
        linarith
  refine ⟨Aᶜ,hA.isOpen_compl,hvA,?_⟩
  intro x hx
  constructor
  · rintro (⟨w,rfl⟩ | hi)
    · left
      by_contra hw
      exact hx (Or.inl ⟨w,(by intro hwv; exact hw (congrArg G.vertex hwv)),rfl⟩)
    · obtain ⟨i,q,hq⟩ := mem_iUnion.mp hi
      right
      refine ⟨i,q,hq,?_⟩
      have hnK : q ∉ K i := fun h => hx (Or.inr (mem_iUnion.mpr ⟨i,q,h,hq⟩))
      by_cases hi : G.initial i = v ∧ (q : ℝ) < δ
      · exact Or.inl hi
      · right
        have hfirst : G.initial i = v → δ ≤ (q : ℝ) := by
          intro h
          exact le_of_not_gt (fun hlt => hi ⟨h,hlt⟩)
        have hsecond : ¬ (G.terminal i = v → (q : ℝ) ≤ 1-δ) := by
          intro h
          exact hnK ⟨hfirst,h⟩
        by_cases ht : G.terminal i = v
        · exact ⟨ht,lt_of_not_ge (fun hle => hsecond (fun _ => hle))⟩
        · exact False.elim (hsecond (fun h => False.elim (ht h)))
  · rintro (rfl | ⟨i,q,rfl,_⟩)
    · exact Or.inl ⟨v,rfl⟩
    · exact Or.inr (mem_iUnion.mpr ⟨i,q,rfl⟩)

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology

/-- A continuous nonzero arc lying in finitely many unit rays cannot change
its ray. This applies to each sufficiently short actual endpoint tail. -/
theorem fixed_ray_on_interval {n : ℕ} (direction : Fin n → Plane)
    (hunit : ∀ i, ‖direction i‖ = 1) (δ : ℝ) (hδ : 0 < δ)
    (f : ℝ → Plane) (hf : ContinuousOn f (Ioo 0 δ))
    (hne : ∀ t ∈ Ioo 0 δ, f t ≠ 0)
    (hray : ∀ t ∈ Ioo 0 δ, ∃ (i : Fin n) (r : ℝ), 0 < r ∧ f t = r • direction i) :
    ∃ i, ∀ t ∈ Ioo 0 δ, f t = ‖f t‖ • direction i := by
  let g : ℝ → Plane := fun t => NormedSpace.normalize (f t)
  have hg : ContinuousOn g (Ioo 0 δ) :=
    (hf.norm.inv₀ (fun t ht => norm_ne_zero_iff.mpr (hne t ht))).smul hf
  have hmaps : MapsTo g (Ioo 0 δ) (range direction) := by
    intro t ht
    obtain ⟨i,r,hr,hri⟩ := hray t ht
    refine ⟨i,?_⟩
    dsimp [g]
    rw [hri,NormedSpace.normalize_smul_of_pos hr,
      NormedSpace.normalize_eq_self_of_norm_eq_one (hunit i)]
  have hmid : δ/2 ∈ Ioo (0 : ℝ) δ := by constructor <;> linarith
  obtain ⟨i,hi⟩ := hmaps hmid
  refine ⟨i,?_⟩
  intro t ht
  have heq := isPreconnected_Ioo.constant_of_mapsTo
    (Set.finite_range direction).isDiscrete hg hmaps ht hmid
  change NormedSpace.normalize (f t) = NormedSpace.normalize (f (δ/2)) at heq
  change direction i = NormedSpace.normalize (f (δ/2)) at hi
  rw [← hi] at heq
  rw [← heq]
  exact (NormedSpace.norm_smul_normalize (f t)).symm

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology Filter

/-- A nonzero right-endpoint derivative points out along the same unit ray
as the short outgoing arc, with strictly positive speed. -/
theorem derivative_points_along_ray (F : ℝ → Plane) (v d : Plane)
    (hF : HasDerivAt F v 0) (hv : v ≠ 0) (hd : ‖d‖ = 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hne : ∀ t ∈ Ioo 0 δ, F t - F 0 ≠ 0)
    (hray : ∀ t ∈ Ioo 0 δ, F t - F 0 = ‖F t - F 0‖ • d) :
    ∃ r : ℝ, 0 < r ∧ v = r • d := by
  have hcont : ContinuousAt (fun w : Plane => NormedSpace.normalize w) v :=
    (continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hv)).smul continuousAt_id
  have hlim := hcont.tendsto.comp hF.tendsto_slope_zero_right
  have hevent : (fun t : ℝ =>
      NormedSpace.normalize (t⁻¹ • (F (0+t) - F 0))) =ᶠ[𝓝[>] 0]
      (fun _ => d) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with t ht htδ
    have htpos : 0 < t := ht
    simp only [zero_add]
    rw [hray t ⟨htpos,htδ⟩,NormedSpace.normalize_smul_of_pos (inv_pos.mpr htpos)]
    rw [NormedSpace.normalize_smul_of_pos (norm_pos_iff.mpr (hne t ⟨htpos,htδ⟩)),
      NormedSpace.normalize_eq_self_of_norm_eq_one hd]
  have heq : NormedSpace.normalize v = d :=
    tendsto_nhds_unique hlim ((tendsto_congr' hevent).mpr tendsto_const_nhds)
  refine ⟨‖v‖,norm_pos_iff.mpr hv,?_⟩
  rw [← heq]
  exact (NormedSpace.norm_smul_normalize v).symm

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology

/-- Every sufficiently short positive point on a ray occurs along a
continuous arc starting at its center. This is the interval-value step used
for injectivity of the endpoint-incidence to ray correspondence. -/
theorem ray_segment_in_arc (f : ℝ → Plane) (d : Plane) (δ : ℝ)
    (hδ : 0 < δ) (hf : ContinuousOn f (Icc 0 δ)) (hf0 : f 0 = 0)
    (hne : f (δ/2) ≠ 0)
    (hray : ∀ t ∈ Ioo 0 δ, f t = ‖f t‖ • d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r, 0 < r → r < ε →
      ∃ t ∈ Ioo 0 δ, f t = r • d := by
  refine ⟨‖f (δ/2)‖,norm_pos_iff.mpr hne,?_⟩
  intro r hr hrε
  have hδhalf : 0 ≤ δ/2 := by linarith
  have hsmall : Icc (0 : ℝ) (δ/2) ⊆ Icc 0 δ := by
    intro t ht
    exact ⟨ht.1,le_trans ht.2 (by linarith)⟩
  have hrange : r ∈ Icc ‖f 0‖ ‖f (δ/2)‖ := by
    rw [hf0,norm_zero]
    exact ⟨hr.le,hrε.le⟩
  obtain ⟨t,ht,heq⟩ := intermediate_value_Icc hδhalf (hf.norm.mono hsmall) hrange
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro ht0
    have : r = 0 := by simpa only [← ht0,hf0,norm_zero] using heq.symm
    exact hr.ne' this)
  have htδ : t < δ := lt_of_le_of_lt ht.2 (by linarith)
  refine ⟨t,⟨htpos,htδ⟩,?_⟩
  change ‖f t‖ = r at heq
  rw [hray t ⟨htpos,htδ⟩,heq]

/-- Two outgoing arcs on the same ray meet away from their center.
Disjoint open graph edges, or the two disjoint tails of one loop, therefore
cannot determine the same ray. -/
theorem same_ray_arcs_intersect (f g : ℝ → Plane) (d : Plane) (δ : ℝ)
    (hδ : 0 < δ) (hf : ContinuousOn f (Icc 0 δ)) (hg : ContinuousOn g (Icc 0 δ))
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hfn : f (δ/2) ≠ 0) (hgn : g (δ/2) ≠ 0)
    (hfr : ∀ t ∈ Ioo 0 δ, f t = ‖f t‖ • d)
    (hgr : ∀ t ∈ Ioo 0 δ, g t = ‖g t‖ • d) :
    ∃ s ∈ Ioo 0 δ, ∃ t ∈ Ioo 0 δ, f s = g t := by
  obtain ⟨ε,hε,he⟩ := ray_segment_in_arc f d δ hδ hf hf0 hfn hfr
  obtain ⟨η,hη,hh⟩ := ray_segment_in_arc g d δ hδ hg hg0 hgn hgr
  let r := min ε η / 2
  have hr : 0 < r := div_pos (lt_min hε hη) (by norm_num)
  have hrε : r < ε := by dsimp [r]; have := min_le_left ε η; linarith
  have hrη : r < η := by dsimp [r]; have := min_le_right ε η; linarith
  obtain ⟨s,hs,hse⟩ := he r hr hrε
  obtain ⟨t,ht,hte⟩ := hh r hr hrη
  exact ⟨s,hs,t,ht,hse.trans hte.symm⟩

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology

/-- Traversing toward one distinct star ray and away along another cannot
form a cusp. Positive speed changes leave the normalized directions intact. -/
theorem distinct_rays_noncuspidal {n : ℕ} (direction : Fin n → Plane)
    (hinj : Function.Injective direction) (hunit : ∀ i, ‖direction i‖ = 1)
    {i j : Fin n} (hij : i ≠ j) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    NormedSpace.normalize (-(a • direction i)) +
      NormedSpace.normalize (b • direction j) ≠ 0 := by
  rw [NormedSpace.normalize_neg,NormedSpace.normalize_smul_of_pos ha,
    NormedSpace.normalize_smul_of_pos hb,
    NormedSpace.normalize_eq_self_of_norm_eq_one (hunit i),
    NormedSpace.normalize_eq_self_of_norm_eq_one (hunit j)]
  intro h
  apply hij
  apply hinj
  have : direction j = direction i := by
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg,add_comm] using h)
  exact this.symm

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction
variable {kind : ModelKind} {M : Type*} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M}

/-- Cutting and possibly reversing an edge preserves its genuine regular
coordinate extensions at both new ends and all interior points. -/
theorem RegularCoordinateGerms.subpath {a b : M} {p : Path a b}
    (hp : RegularCoordinateGerms S p.toContinuousMap) (s t : unitInterval)
    (hst : s ≠ t) : RegularCoordinateGerms S (p.subpath s t).toContinuousMap := by
  intro q e he hqe
  let u : unitInterval := Set.Icc.convexComb s t q
  let β : ℝ := (t : ℝ) - s
  have hβ : β ≠ 0 := sub_ne_zero.mpr (fun h => hst (Subtype.ext h.symm))
  have hβabs : 0 < |β| := abs_pos.mpr hβ
  have hu : β * (q : ℝ) + s = (u : ℝ) := by
    simp only [u,Set.Icc.coe_convexComb,β]
    ring
  obtain ⟨δ,F,hδ,hF,hFn,hFeq⟩ := hp u e he hqe
  let η : ℝ := δ / (2 * |β|)
  have hη : 0 < η := div_pos hδ (mul_pos (by norm_num) hβabs)
  have hβη : |β| * η < δ := by
    have heq : |β| * η = δ / 2 := by dsimp [η]; field_simp
    rw [heq]
    linarith
  have hnear (r : ℝ) (hr : |r - (q : ℝ)| < η) :
      |β * r + s - (u : ℝ)| < δ := by
    calc
      |β * r + s - (u : ℝ)| = |β * (r - (q : ℝ))| := by congr 1; rw [← hu]; ring
      _ = |β| * |r - (q : ℝ)| := abs_mul _ _
      _ < |β| * η := mul_lt_mul_of_pos_left hr hβabs
      _ < δ := hβη
  have hmap : MapsTo (fun r : ℝ => β*r+s)
      (Ioo ((q : ℝ)-η) ((q : ℝ)+η)) (Ioo ((u : ℝ)-δ) ((u : ℝ)+δ)) := by
    intro r hr
    have hh := hnear r (abs_lt.mpr (by constructor <;> linarith [hr.1,hr.2]))
    have hh' := abs_lt.mp hh
    constructor <;> linarith [hh'.1,hh'.2]
  refine ⟨η,(fun r => F (β*r+s)),hη,hF.comp (by fun_prop) hmap,?_,?_⟩
  · have hd : deriv (fun r => F (β*r+s)) (q : ℝ) = β • deriv F (u : ℝ) := by
      calc
        _ = β • deriv (fun y => F (y+s)) (β*(q : ℝ)) := deriv_comp_mul_left β _ _
        _ = _ := by rw [deriv_comp_add_const,hu]
    rw [hd]
    exact smul_ne_zero hβ hFn
  · intro r hr
    have hv : β * (r : ℝ) + s = (Set.Icc.convexComb s t r : ℝ) := by
      simp only [Set.Icc.coe_convexComb,β]; ring
    have hclose : |(Set.Icc.convexComb s t r : ℝ) - (u : ℝ)| < δ := by
      rw [← hv]
      exact hnear r hr
    have hh := hFeq (Set.Icc.convexComb s t r) hclose
    refine ⟨hh.1,?_⟩
    change F (β * (r : ℝ) + s) = coordinates e (p (Set.Icc.convexComb s t r))
    rw [hv]
    exact hh.2

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {kind : ModelKind} {M : Type*} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M}

/-- Every oriented subdivision piece retains regular coordinate germs in
all original charts, including all new and old endpoints. -/
theorem subdivisionPath_regularCoordinateGerms (G : EmbeddedGraph S)
    (hG : ∀ i, RegularCoordinateGerms S (G.edge i))
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y) :
    RegularCoordinateGerms S (subdivisionPath G h).toContinuousMap := by
  cases x with
  | inl v =>
    cases y with
    | inl w => exact False.elim h
    | inr d =>
      rcases d with ⟨e,b⟩
      cases b
      · change RegularCoordinateGerms S
          ((edgePath G e).subpath 0 (subdivisionParameter false)).toContinuousMap
        exact (hG e).subpath 0 (subdivisionParameter false) (by
          intro heq; have := congrArg Subtype.val heq
          norm_num [subdivisionParameter] at this)
      · change RegularCoordinateGerms S
          ((edgePath G e).subpath 1 (subdivisionParameter true)).toContinuousMap
        exact (hG e).subpath 1 (subdivisionParameter true) (by
          intro heq; have := congrArg Subtype.val heq
          norm_num [subdivisionParameter] at this)
  | inr d =>
    cases y with
    | inl v =>
      rcases d with ⟨e,b⟩
      cases b
      · change RegularCoordinateGerms S
          ((edgePath G e).subpath (subdivisionParameter false) 0).toContinuousMap
        exact (hG e).subpath (subdivisionParameter false) 0 (by
          intro heq; have := congrArg Subtype.val heq
          norm_num [subdivisionParameter] at this)
      · change RegularCoordinateGerms S
          ((edgePath G e).subpath (subdivisionParameter true) 1).toContinuousMap
        exact (hG e).subpath (subdivisionParameter true) 1 (by
          intro heq; have := congrArg Subtype.val heq
          norm_num [subdivisionParameter] at this)
    | inr e =>
      rcases d with ⟨d,b⟩
      rcases e with ⟨e,c⟩
      have hde : d = e := h.1
      subst e
      change RegularCoordinateGerms S ((edgePath G d).subpath
        (subdivisionParameter b) (subdivisionParameter c)).toContinuousMap
      exact (hG d).subpath _ _
        (fun heq => h.2 (subdivisionParameter_injective heq))

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {kind : ModelKind} {M : Type*} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M} {a b : M}

/-- Coordinates of an actual path contained in the chart source. -/
def coordinatePath (p : Path a b) (e : ModelChart 2 kind M)
    (hsource : range p ⊆ e.source) : Path (coordinates e a) (coordinates e b) where
  toFun := coordinates e ∘ p
  continuous_toFun := (continuousOn_coordinates e).comp_continuous p.continuous
    (fun t => hsource ⟨t,rfl⟩)
  source' := by simp only [Function.comp_apply,Path.source]
  target' := by simp only [Function.comp_apply,Path.target]

theorem coordinatePath_extend (p : Path a b) (e : ModelChart 2 kind M)
    (hsource : range p ⊆ e.source) :
    (coordinatePath p e hsource).extend = fun r => coordinates e (p.extend r) := by
  funext r
  rfl

/-- The interior of every actual coordinate piece is smooth and regular;
only its two endpoint joins need separate compatibility arguments. -/
theorem coordinatePath_interior_regular (p : Path a b) (e : ModelChart 2 kind M)
    (hsource : range p ⊆ e.source) (he : e ∈ S.smoothStructure.val)
    (hp : RegularCoordinateGerms S p.toContinuousMap) :
    ContDiffOn ℝ ∞ (coordinatePath p e hsource).extend (Ioo (0 : ℝ) 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, deriv (coordinatePath p e hsource).extend t ≠ 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, RegularJoinAt (coordinatePath p e hsource).extend t) := by
  have hsm : ContDiffOn ℝ ∞ (coordinatePath p e hsource).extend (Ioo (0 : ℝ) 1) := by
    apply isOpen_Ioo.contDiffOn_iff.mpr
    intro t ht
    rw [coordinatePath_extend]
    exact (P202.SurfaceRegionConstruction.RegularOpenEdge.in_chart hp.regular.1 t ht e he
      (hsource ⟨⟨t,ht.1.le,ht.2.le⟩,rfl⟩)).1
  have hreg (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      deriv (coordinatePath p e hsource).extend t ≠ 0 := by
    rw [coordinatePath_extend]
    exact (P202.SurfaceRegionConstruction.RegularOpenEdge.in_chart hp.regular.1 t ht e he
      (hsource ⟨⟨t,ht.1.le,ht.2.le⟩,rfl⟩)).2
  exact ⟨hsm,hreg,fun t ht => RegularJoinAt.of_contDiffOn hsm ht (hreg t ht)⟩

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.NormalSectors
 theorem exists_nonzero_weak_axis_point (J : Set (Fin 2)) (r : ℝ)
    (σ : Fin 2 → Bool) (hr : 0 < r) (hne : (chamber J r σ).Nonempty)
    (b : Fin 2) (hb : b ∈ J) :
    ∃ z : Plane, z ∈ Metric.ball 0 r ∧ z ≠ 0 ∧ z b = 0 ∧
      ∀ j ∈ J, if σ j then 0 ≤ z j else z j ≤ 0 := by
  classical
  have hrev : b.rev ≠ b := by fin_cases b <;> decide
  by_cases ha : b.rev ∈ J
  · obtain ⟨x,hx⟩ := hne
    obtain ⟨z,hz,hzb,hza,hw⟩ := axis_boundary_witness J r σ hrev ha hx
    exact ⟨z,hz,(fun h => hza (by rw [h]; rfl)),hzb,hw⟩
  · let z : Plane := (r/2) • axisTangent b
    have hz : ‖z‖ = r/2 := by
      simp only [z,norm_smul,AxisRays.tangent_norm,mul_one,Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    have hzb : z b = 0 := by simp [z,axisTangent,toPlane]
    refine ⟨z,?_,?_,hzb,?_⟩
    · rw [Metric.mem_ball,dist_zero_right,hz]
      linarith
    · intro h
      have := hz
      rw [h,norm_zero] at this
      linarith
    · intro j hj
      have hjb : j = b := by
        fin_cases j <;> fin_cases b <;> simp_all [Fin.rev]
      rw [hjb,hzb]
      cases σ b <;> simp
end P202.SurfaceRegionConstruction.NormalSectors
namespace P202.SurfaceRegionConstruction
open Arrangement
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {W : SmoothManifold 2 .euclidean Y} {K : Set Y}
variable {A : Set (ModelChart 2 .euclidean Y)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)
variable {p : Y} {O : Set Y}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)

theorem infinite_local_chamber_graph_closure
    (f : X → Y) (hf : IsClosedEmbedding f)
    (C : Set X) (hC : C ⊆ f ⁻¹' normalNeighborhood T F) (hne : C.Nonempty)
    (σ : Fin 2 → Bool)
    (himage : (fun x => coordinates F.chart (f x)) '' C =
      NormalSectors.chamber (activeAxes T F) F.radius σ)
    (b : Fin 2) (hb : b ∈ activeAxes T F) :
    (closure C ∩ f ⁻¹' arrangementCarrier T ∩ f ⁻¹' normalNeighborhood T F).Infinite := by
  obtain ⟨z,hz,hz0,hzb,hweak⟩ := NormalSectors.exists_nonzero_weak_axis_point
    (activeAxes T F) F.radius σ F.radius_pos (himage ▸ hne.image _) b hb
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hmaps : MapsTo (fun t : ℝ => t • z) (Ioo 0 1)
      ((fun x => coordinates F.chart (f x)) ''
        (closure C ∩ f ⁻¹' arrangementCarrier T ∩ f ⁻¹' normalNeighborhood T F)) := by
    intro t ht
    have htz : t • z ∈ Metric.ball 0 F.radius := by
      rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
      have hzr : ‖z‖ < F.radius := by simpa only [Metric.mem_ball,dist_zero_right] using hz
      nlinarith [mul_lt_mul_of_pos_right ht.2 hznorm]
    have htweak : ∀ a ∈ activeAxes T F, if σ a then 0 ≤ (t • z) a else (t • z) a ≤ 0 := by
      intro a ha
      have hs := hweak a ha
      simp only [PiLp.smul_apply,smul_eq_mul]
      cases hσ : σ a <;> simp only [hσ,Bool.false_eq_true,↓reduceIte] at hs ⊢
      · exact mul_nonpos_of_nonneg_of_nonpos ht.1.le hs
      · exact mul_nonneg ht.1.le hs
    have hzcl := normalInverse_mem_closure_image_chamber T F f C hC σ himage htz htweak hne
    have hcopy : normalInverse T F (t • z) ∈ range f :=
      (hf.isClosed_range.closure_subset_iff.mpr (image_subset_range f C)) hzcl
    obtain ⟨q,hq⟩ := hcopy
    have hqN : f q ∈ normalNeighborhood T F := by
      rw [hq]
      exact ⟨F.chart.map_target (normalInverse_target T F htz),
        by simpa only [mem_preimage,normalInverse_coordinates T F htz] using htz⟩
    have hqC : q ∈ closure C := by
      rw [hf.isEmbedding.closure_eq_preimage_closure_image]
      change f q ∈ closure (f '' C)
      rwa [hq]
    have hqG : f q ∈ arrangementCarrier T := by
      apply (carrier_iff_axis T F hqN).mpr
      refine ⟨b,hb,?_⟩
      rw [hq,normalInverse_coordinates T F htz]
      simp [hzb]
    exact ⟨q,⟨⟨hqC,hqG⟩,hqN⟩,by change coordinates F.chart (f q) = t • z; rw [hq,normalInverse_coordinates T F htz]⟩
  intro hfin
  have hinf : ((fun t : ℝ => t • z) '' Ioo (0 : ℝ) 1).Infinite :=
    (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).image
      (smul_left_injective ℝ hz0).injOn
  exact hinf ((hfin.image (fun x => coordinates F.chart (f x))).subset (image_subset_iff.mpr hmaps))
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement
variable {kind : ModelKind} {X : Type u} [TopologicalSpace X]
variable (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
variable (s : Bool)
variable {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
variable {B : CompactSmoothSeam D.manifold}
variable (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
variable (T : TransverseDiskArrangement D.manifold
  (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
include hB

theorem restricted_arrangement_infinite_local_closure_graph
    (G : Set X)
    (hG : G = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)
    (c : ConnectedComponents (Gᶜ : Set X)) {p : X}
    (hpc : p ∈ closure (componentSet Gᶜ c)) (hpG : p ∈ G)
    (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    (closure (componentSet Gᶜ c) ∩ G ∩ O).Infinite := by
  subst G
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  have hf : IsClosedEmbedding f := D.copy_closedEmbedding s
  obtain ⟨V,hV,hVO⟩ := hf.isEmbedding.isInducing.isOpen_iff.mp hO
  have hpV : f p ∈ V := by change p ∈ f ⁻¹' V; rwa [hVO]
  obtain ⟨F⟩ := T.normal_forms (f p) V hV hpV
  let N := f ⁻¹' normalNeighborhood T F
  have hNO : N ⊆ O := by
    intro x hx
    rw [← hVO]
    exact F.neighborhood_subset hx
  obtain ⟨a,ha⟩ := (normal_copy_sector_occupancy S D s hB T F).1 c hpc
  obtain ⟨σ,hσ⟩ := normal_copy_component_coordinates S D s hB T F a
  let C := componentSet (N \ f ⁻¹' arrangementCarrier T) a
  have hC : C ⊆ f ⁻¹' normalNeighborhood T F :=
    fun x hx => (Components.subset _ a hx).1
  have hne : C.Nonempty := Components.nonempty _ a
  obtain ⟨b,hb,_⟩ := (carrier_iff_axis T F (mem_normalNeighborhood T F)).mp hpG
  have hinf := infinite_local_chamber_graph_closure T F f hf C hC hne σ hσ b hb
  apply hinf.mono
  intro q hq
  refine ⟨⟨?_,hq.1.2⟩,hNO hq.2⟩
  apply closure_mono (show C ⊆ componentSet (f ⁻¹' arrangementCarrier T)ᶜ c from ?_) hq.1.1
  intro x hx
  exact (show x ∈ componentSet (f ⁻¹' arrangementCarrier T)ᶜ c ∩ N by rw [ha]; exact hx).1
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {kind : ModelKind} {X : Type*} [TopologicalSpace X]
variable {S : SmoothManifold 2 kind X}

theorem eq_union_whole_edges_of_infinite_local_incidence
    (G : EmbeddedGraph S) (F : Set X) (hF : F ⊆ G.carrier)
    (hlocal : ∀ p ∈ F, ∀ O : Set X, IsOpen O → p ∈ O → (F ∩ O).Infinite)
    (hsat : ∀ (i : Fin G.edgeCount) (t : unitInterval),
      0 < (t : ℝ) → (t : ℝ) < 1 → G.edge i t ∈ F → range (G.edge i) ⊆ F) :
    F = ⋃ i : {i : Fin G.edgeCount // range (G.edge i) ⊆ F}, range (G.edge i.val) := by
  let := S.topologicalManifold.hausdorff
  let U := ⋃ i : {i : Fin G.edgeCount // range (G.edge i) ⊆ F}, range (G.edge i.val)
  have hU : IsClosed U :=
    (isCompact_iUnion (fun i : {i : Fin G.edgeCount // range (G.edge i) ⊆ F} =>
      isCompact_range (G.edge i.val).continuous)).isClosed
  apply Set.Subset.antisymm
  · intro p hp
    by_contra hpU
    obtain ⟨q,hq,hqv⟩ := (hlocal p hp Uᶜ hU.isOpen_compl hpU).exists_notMem_finite
      (Set.finite_range G.vertex)
    rcases hF hq.1 with hv | he
    · exact hqv hv
    obtain ⟨i,t,ht⟩ := mem_iUnion.mp he
    have ht0 : 0 < (t : ℝ) := by
      by_contra hn
      have htz : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
      subst t
      exact hqv ⟨G.initial i,(G.at_zero i).symm.trans ht⟩
    have ht1 : (t : ℝ) < 1 := by
      by_contra hn
      have hto : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt hn))
      subst t
      exact hqv ⟨G.terminal i,(G.at_one i).symm.trans ht⟩
    have hi : range (G.edge i) ⊆ F := hsat i t ht0 ht1 (ht ▸ hq.1)
    exact hq.2 (mem_iUnion.mpr ⟨⟨i,hi⟩,t,ht⟩)
  · rintro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact i.property hi
end P202.SurfaceRegionConstruction.BoundaryCycles
namespace P202.SurfaceRegionConstruction
open BoundaryCycles
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M} {D : P202Specs.SmoothSurfaceDouble.SmoothDouble S}
variable {s : Bool}
variable {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
variable {B : CompactSmoothSeam D.manifold}
variable {T : TransverseDiskArrangement D.manifold
  (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B}

theorem graphGeometry_infinite_local_frontier
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (H : ArrangementGraphGeometryData S D s T)
    (a : ConnectedComponents (H.graph.carrierᶜ : Set M))
    {p : M} (hp : p ∈ frontier (componentSet H.graph.carrierᶜ a))
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    (frontier (componentSet H.graph.carrierᶜ a) ∩ O).Infinite := by
  rw [H.frontiers_on_graph a] at hp ⊢
  exact restricted_arrangement_infinite_local_closure_graph S D s hB T H.graph.carrier
    H.carrier_eq a hp.1 hp.2 O hO hpO

theorem graphGeometry_frontier_eq_whole_edges
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (H : ArrangementGraphGeometryData S D s T)
    (a : ConnectedComponents (H.graph.carrierᶜ : Set M)) :
    frontier (componentSet H.graph.carrierᶜ a) =
      ⋃ i : {i : Fin H.graph.edgeCount //
          range (H.graph.edge i) ⊆ frontier (componentSet H.graph.carrierᶜ a)},
        range (H.graph.edge i.val) := by
  apply eq_union_whole_edges_of_infinite_local_incidence H.graph _
    (by rw [H.frontiers_on_graph]; exact inter_subset_right)
    (fun p hp O hO hpO => graphGeometry_infinite_local_frontier hB H a hp O hO hpO)
  intro i t ht0 ht1 ht
  apply graphGeometry_whole_edge_of_frontier_incidence hB H a i
  refine ⟨⟨t,ht0,ht1⟩,?_⟩
  exact ht
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction
open BoundaryCycles
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M} {D : P202Specs.SmoothSurfaceDouble.SmoothDouble S}
variable {s : Bool}
variable {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
variable {B : CompactSmoothSeam D.manifold}
variable {T : TransverseDiskArrangement D.manifold
  (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B}

theorem graphGeometry_regional_embeddedGraph
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (H : ArrangementGraphGeometryData S D s T)
    (a : ConnectedComponents (H.graph.carrierᶜ : Set M)) :
    ∃ K : EmbeddedGraph S,
      range K.vertex = range H.graph.vertex ∩ frontier (componentSet H.graph.carrierᶜ a) ∧
      K.carrier = frontier (componentSet H.graph.carrierᶜ a) ∧
      (∀ i, ∃ j, range (H.graph.edge j) ⊆ frontier (componentSet H.graph.carrierᶜ a) ∧
        K.edge i = H.graph.edge j) ∧
      (∀ j, range (H.graph.edge j) ⊆ frontier (componentSet H.graph.carrierᶜ a) →
        ∃ i, K.edge i = H.graph.edge j) ∧
      (∀ i, RegularEdgeEndpoints S (K.edge i)) ∧
      (∀ i, ∃ k : Option (Fin T.count), ∀ t : unitInterval,
        P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s (K.edge i t) ∈
          arrangementCurve B.carrier T.disk T.radius k) ∧
      1 ≤ K.edgeCount ∧
      (∀ v : Fin K.vertexCount, (incidences K.initial K.terminal v).Nonempty) := by
  let F := frontier (componentSet H.graph.carrierᶜ a)
  have hF : F ⊆ H.graph.carrier := by
    dsimp [F]
    rw [H.frontiers_on_graph]
    exact inter_subset_right
  have hselect : ∀ i, ((H.graph.edge i '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) ∩ F).Nonempty →
      range (H.graph.edge i) ⊆ F := by
    intro i hi
    obtain ⟨x,⟨t,ht,hx⟩,hxF⟩ := hi
    apply graphGeometry_whole_edge_of_frontier_incidence hB H a i
    refine ⟨⟨t,ht⟩,?_⟩
    change H.graph.edge i t ∈ F
    rwa [hx]
  obtain ⟨K,hvertices,hcarrier,hforward,hreverse⟩ := embeddedGraph_restrict S H.graph F hselect
  have hcarrier' : K.carrier = F := hcarrier.trans (inter_eq_self_of_subset_right hF)
  have hcover : F = ⋃ i : Fin K.edgeCount, range (K.edge i) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : x ∈ ⋃ i : {i : Fin H.graph.edgeCount // range (H.graph.edge i) ⊆ F},
          range (H.graph.edge i.val) := by
        rw [← graphGeometry_frontier_eq_whole_edges hB H a]
        exact hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx'
      obtain ⟨j,hj⟩ := hreverse i.val i.property
      exact mem_iUnion.mpr ⟨j,hj.symm ▸ hi⟩
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      rw [← hcarrier']
      exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)
  refine ⟨K,hvertices,hcarrier',hforward,hreverse,?_,?_,?_,?_⟩
  · intro i
    obtain ⟨j,_,hj⟩ := hforward i
    rw [hj]
    exact H.endpoint_germs j
  · intro i
    obtain ⟨j,_,hj⟩ := hforward i
    rw [hj]
    exact H.edge_curve j
  · obtain ⟨x,hx⟩ := H.nonempty_frontiers a
    have hx' : x ∈ ⋃ i : Fin K.edgeCount, range (K.edge i) := hcover ▸ hx
    obtain ⟨i,_⟩ := mem_iUnion.mp hx'
    exact Nat.succ_le_iff.mpr (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  · intro v
    have hvF : K.vertex v ∈ F := by
      rw [← hcarrier']
      exact Or.inl (mem_range_self v)
    obtain ⟨i,t,ht⟩ := mem_iUnion.mp (hcover ▸ hvF)
    by_cases ht0 : t = 0
    · subst t
      refine ⟨(i,false),?_⟩
      change K.initial i = v
      exact K.vertex_injective ((K.at_zero i).symm.trans ht)
    by_cases ht1 : t = 1
    · subst t
      refine ⟨(i,true),?_⟩
      change K.terminal i = v
      exact K.vertex_injective ((K.at_one i).symm.trans ht)
    have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (fun h => ht0 (Subtype.ext h.symm))
    have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
      (fun h => ht1 (Subtype.ext h))
    exact False.elim (K.avoids_vertices i t htpos htlt ⟨v,ht.symm⟩)
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.BoundaryCycles

theorem normalize_ne_neg_of_injective_linearMap
    (L : Plane →ₗ[ℝ] Plane) (hL : Function.Injective L)
    {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : NormedSpace.normalize u ≠ -NormedSpace.normalize v) :
    NormedSpace.normalize (L u) ≠ -NormedSpace.normalize (L v) := by
  have hLu : L u ≠ 0 := by
    intro hh
    exact hu (hL (hh.trans (map_zero L).symm))
  have hLv : L v ≠ 0 := by
    intro hh
    exact hv (hL (hh.trans (map_zero L).symm))
  intro heq
  have hray : SameRay ℝ (L u) (L (-v)) := by
    apply (sameRay_iff_inv_norm_smul_eq_of_ne hLu (by simpa using hLv)).mpr
    change NormedSpace.normalize (L u) = NormedSpace.normalize (L (-v))
    simpa only [map_neg, NormedSpace.normalize_neg] using heq
  have hsource : SameRay ℝ u (-v) := hL.sameRay_map_iff.mp hray
  have hnorm := (sameRay_iff_inv_norm_smul_eq_of_ne hu (neg_ne_zero.mpr hv)).mp hsource
  apply h
  change NormedSpace.normalize u = NormedSpace.normalize (-v) at hnorm
  simpa only [NormedSpace.normalize_neg] using hnorm


/-- A linear map detects that two directed vectors are not opposite whenever
both mapped vectors are nonzero. This formulation transports noncuspidality
using the reverse chart derivative, without assuming ambient invertibility
of an arbitrary smooth extension of a boundary chart change. -/
theorem normalize_ne_neg_of_linear_images
    (L : Plane →ₗ[ℝ] Plane) {u v : Plane}
    (hu : L u ≠ 0) (hv : L v ≠ 0)
    (h : NormedSpace.normalize (L u) ≠ -NormedSpace.normalize (L v)) :
    NormedSpace.normalize u ≠ -NormedSpace.normalize v := by
  have hu0 : u ≠ 0 := fun hh => hu (hh ▸ map_zero L)
  have hv0 : v ≠ 0 := fun hh => hv (hh ▸ map_zero L)
  intro heq
  have hray : SameRay ℝ u (-v) := by
    apply (sameRay_iff_inv_norm_smul_eq_of_ne hu0 (neg_ne_zero.mpr hv0)).mpr
    change NormedSpace.normalize u = NormedSpace.normalize (-v)
    simpa only [NormedSpace.normalize_neg] using heq
  have hmapped : SameRay ℝ (L u) (L (-v)) := hray.map L
  have hnorm := (sameRay_iff_inv_norm_smul_eq_of_ne hu
    (by simpa only [map_neg] using neg_ne_zero.mpr hv)).mp hmapped
  apply h
  change NormedSpace.normalize (L u) = NormedSpace.normalize (L (-v)) at hnorm
  simpa only [map_neg,NormedSpace.normalize_neg] using hnorm


/-- Two smooth ambient germs agreeing on a left half-neighborhood have the
same derivative, including at the endpoint. -/
theorem deriv_eq_of_eventuallyEq_left {f g : ℝ → Plane} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t)
    (heq : f =ᶠ[𝓝[≤] t] g) : deriv f t = deriv g t := by
  have hfg := hf.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    heq.symm (show t ∈ Iic t from mem_Iic.mpr le_rfl)
  exact (hfg.derivWithin (uniqueDiffWithinAt_Iic t)).symm.trans
    (hg.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic t))

/-- The corresponding right-sided uniqueness fact for initial endpoint
extensions. -/
theorem deriv_eq_of_eventuallyEq_right {f g : ℝ → Plane} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t)
    (heq : f =ᶠ[𝓝[≥] t] g) : deriv f t = deriv g t := by
  have hfg := hf.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    heq.symm (show t ∈ Ici t from mem_Ici.mpr le_rfl)
  exact (hfg.derivWithin (uniqueDiffWithinAt_Ici t)).symm.trans
    (hg.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici t))


variable {kind : ModelKind} {M : Type*} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M}

/-- Directed endpoint compatibility proved in one original smooth chart holds
in every original smooth chart. The derivative of the reverse transition
compares both one-sided germs at their common endpoint. -/
theorem regularEndpointJoin_change_chart
    (c d : C(unitInterval, M)) (hcommon : c 1 = d 0)
    (g e : ModelChart 2 kind M) (hg : g ∈ S.smoothStructure.val)
    (he : e ∈ S.smoothStructure.val) (hcg : c 1 ∈ g.source) (hce : c 1 ∈ e.source)
    (hc : RegularEdgeEndpoints S c) (hd : RegularEdgeEndpoints S d)
    (hjoin : RegularEndpointJoin
      (fun t => coordinates g (IccExtend zero_le_one c t))
      (fun t => coordinates g (IccExtend zero_le_one d t))) :
    RegularEndpointJoin
      (fun t => coordinates e (IccExtend zero_le_one c t))
      (fun t => coordinates e (IccExtend zero_le_one d t)) := by
  obtain ⟨δ,l,r,hδ,hl,hr,hel,her,hnl,hnr,hn⟩ := hjoin
  obtain ⟨ε,F,hε,hF,hFn,hFrep⟩ := hc 1 (Or.inr rfl) e he hce
  have hde : d 0 ∈ e.source := hcommon ▸ hce
  obtain ⟨ζ,G,hζ,hG,hGn,hGrep⟩ := hd 0 (Or.inl rfl) e he hde
  have hF1 : F 1 = coordinates e (c 1) := (hFrep 1 (by simpa using hε)).2
  have hG0 : G 0 = coordinates e (c 1) := by
    exact (hGrep 0 (by simpa using hζ)).2.trans (congrArg (coordinates e) hcommon.symm)
  have hFdiff : DifferentiableAt ℝ F 1 :=
    (hF.contDiffAt (isOpen_Ioo.mem_nhds (by
      simp only [Set.Icc.coe_one]; constructor <;> linarith))).differentiableAt (by simp)
  have hGdiff : DifferentiableAt ℝ G 0 :=
    (hG.contDiffAt (isOpen_Ioo.mem_nhds (by
      simp only [Set.Icc.coe_zero]; constructor <;> linarith))).differentiableAt (by simp)
  have hldiff : DifferentiableAt ℝ l 1 :=
    (hl.contDiffAt (isOpen_Ioo.mem_nhds (by constructor <;> linarith))).differentiableAt (by simp)
  have hrdiff : DifferentiableAt ℝ r 0 :=
    (hr.contDiffAt (isOpen_Ioo.mem_nhds (by constructor <;> linarith))).differentiableAt (by simp)
  obtain ⟨U,hU,hpU,K,hK,hKrep⟩ := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he g hg) hce hcg
  let Kp : Plane → Plane := fun z => toPlane (K (toPlane.symm z))
  have hKp : ContDiffAt ℝ ∞ Kp (coordinates e (c 1)) := by
    have hk : ContDiffAt ℝ ∞ K (toPlane.symm (coordinates e (c 1))) := by
      simpa only [coordinates,toPlane.symm_apply_apply] using hK.contDiffAt (hU.mem_nhds hpU)
    exact toPlane.contDiff.contDiffAt.comp _
      (hk.comp _ toPlane.symm.contDiff.contDiffAt)
  have hKpF : ContDiffAt ℝ ∞ Kp (F 1) := by rwa [hF1]
  have hKpG : ContDiffAt ℝ ∞ Kp (G 0) := by rwa [hG0]
  have hKFdiff : DifferentiableAt ℝ (fun t => Kp (F t)) 1 :=
    (hKpF.differentiableAt (by simp)).comp 1 hFdiff
  have hKGdiff : DifferentiableAt ℝ (fun t => Kp (G t)) 0 :=
    (hKpG.differentiableAt (by simp)).comp 0 hGdiff
  have htransc : ∀ᶠ t : ℝ in 𝓝 (1:ℝ),
      Kp (coordinates e (IccExtend zero_le_one c t)) =
      coordinates g (IccExtend zero_le_one c t) := by
    have hct : Filter.Tendsto (IccExtend zero_le_one c) (𝓝 (1:ℝ)) (𝓝 (c 1)) := by
      have hcc : IccExtend zero_le_one c (1:ℝ) = c 1 := by
        rw [IccExtend_of_mem zero_le_one c (by norm_num : (1:ℝ) ∈ Icc 0 1)]
        congr 1
      simpa only [hcc] using
        (show ContinuousAt (IccExtend zero_le_one c) (1:ℝ) from c.continuous.Icc_extend'.continuousAt).tendsto
    filter_upwards [hKrep.comp_tendsto hct] with t ht
    simpa only [Kp,coordinates,toPlane.symm_apply_apply,id_eq,Function.comp_def]
      using congrArg toPlane ht
  have htransd : ∀ᶠ t : ℝ in 𝓝 (0:ℝ),
      Kp (coordinates e (IccExtend zero_le_one d t)) =
      coordinates g (IccExtend zero_le_one d t) := by
    have hdt : Filter.Tendsto (IccExtend zero_le_one d) (𝓝 (0:ℝ)) (𝓝 (c 1)) := by
      rw [hcommon]
      have hdd : IccExtend zero_le_one d (0:ℝ) = d 0 := by
        rw [IccExtend_of_mem zero_le_one d (by norm_num : (0:ℝ) ∈ Icc 0 1)]
        congr 1
      simpa only [hdd] using
        (show ContinuousAt (IccExtend zero_le_one d) (0:ℝ) from d.continuous.Icc_extend'.continuousAt).tendsto
    filter_upwards [hKrep.comp_tendsto hdt] with t ht
    simpa only [Kp,coordinates,toPlane.symm_apply_apply,id_eq,Function.comp_def]
      using congrArg toPlane ht
  have hleft : l =ᶠ[𝓝[≤] (1:ℝ)] (fun t => Kp (F t)) := by
    have hnearc : ∀ᶠ t : ℝ in 𝓝 (1:ℝ), 1-ε < t ∧ 1-δ < t ∧ 0 < t := by
      filter_upwards [Ioi_mem_nhds (by linarith : 1-ε < (1:ℝ)),
        Ioi_mem_nhds (by linarith : 1-δ < (1:ℝ)),
        Ioi_mem_nhds (by norm_num : (0:ℝ)<1)] with t htε htδ ht0
      exact ⟨htε,htδ,ht0⟩
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnearc,
      nhdsWithin_le_nhds htransc] with t ht htnear httrans
    have ht_le : t ≤ 1 := mem_Iic.mp ht
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨htnear.2.2.le,ht_le⟩
    have hFt : F t = coordinates e (IccExtend zero_le_one c t) := by
      rw [IccExtend_of_mem zero_le_one c htI]
      exact (hFrep ⟨t,htI⟩ (by
        change |t-1| < ε
        rw [abs_of_nonpos (by linarith [ht_le] : t-1≤0)]
        linarith [htnear.1])).2
    exact (hel ⟨htnear.2.1.le,ht⟩).trans (httrans.symm.trans (congrArg Kp hFt.symm))
  have hright : r =ᶠ[𝓝[≥] (0:ℝ)] (fun t => Kp (G t)) := by
    have hneard : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), t < ζ ∧ t < δ ∧ t < 1 := by
      filter_upwards [Iio_mem_nhds hζ,Iio_mem_nhds hδ,
        Iio_mem_nhds (by norm_num : (0:ℝ)<1)] with t htζ htδ ht1
      exact ⟨htζ,htδ,ht1⟩
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hneard,
      nhdsWithin_le_nhds htransd] with t ht htnear httrans
    have ht_ge : 0 ≤ t := mem_Ici.mp ht
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht_ge,htnear.2.2.le⟩
    have hGt : G t = coordinates e (IccExtend zero_le_one d t) := by
      rw [IccExtend_of_mem zero_le_one d htI]
      exact (hGrep ⟨t,htI⟩ (by
        simp only [Set.Icc.coe_zero,sub_zero]
        rw [abs_of_nonneg ht_ge]
        exact htnear.1)).2
    exact (her ⟨ht,htnear.2.1.le⟩).trans (httrans.symm.trans (congrArg Kp hGt.symm))
  let L : Plane →L[ℝ] Plane := fderiv ℝ Kp (coordinates e (c 1))
  have hDl : deriv l 1 = L (deriv F 1) := by
    rw [deriv_eq_of_eventuallyEq_left hldiff hKFdiff hleft]
    have hc := (hKpF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 1 hFdiff.hasDerivAt
    simpa only [L,hF1,Function.comp_def] using hc.deriv
  have hDr : deriv r 0 = L (deriv G 0) := by
    rw [deriv_eq_of_eventuallyEq_right hrdiff hKGdiff hright]
    have hc := (hKpG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hGdiff.hasDerivAt
    simpa only [L,hG0,Function.comp_def] using hc.deriv
  have hnoncusp : NormedSpace.normalize (deriv F 1) ≠ -NormedSpace.normalize (deriv G 0) := by
    apply normalize_ne_neg_of_linear_images L.toLinearMap
    · change L (deriv F 1) ≠ 0
      rw [← hDl]; exact hnl
    · change L (deriv G 0) ≠ 0
      rw [← hDr]; exact hnr
    · change NormedSpace.normalize (L (deriv F 1)) ≠ -NormedSpace.normalize (L (deriv G 0))
      rw [← hDl,← hDr]; exact hn
  let η : ℝ := min (min ε ζ / 2) (1/2)
  have hη : 0 < η := lt_min (half_pos (lt_min hε hζ)) (by norm_num)
  have hηε : η < ε := by
    have := min_le_left (min ε ζ / 2) (1/2:ℝ)
    have := min_le_left ε ζ
    dsimp [η] at *
    linarith
  have hηζ : η < ζ := by
    have := min_le_left (min ε ζ / 2) (1/2:ℝ)
    have := min_le_right ε ζ
    dsimp [η] at *
    linarith
  have hηhalf : η ≤ 1/2 := min_le_right _ _
  refine ⟨η,F,G,hη,?_,?_,?_,?_,hFn,hGn,hnoncusp⟩
  · apply hF.mono
    intro t ht
    simp only [Set.Icc.coe_one]
    constructor <;> linarith [ht.1,ht.2]
  · apply hG.mono
    intro t ht
    simp only [Set.Icc.coe_zero,zero_sub,zero_add]
    constructor <;> linarith [ht.1,ht.2]
  · intro t ht
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht.1],ht.2⟩
    change F t = coordinates e (IccExtend zero_le_one c t)
    rw [IccExtend_of_mem zero_le_one c htI]
    exact (hFrep ⟨t,htI⟩ (by
      change |t-1| < ε
      rw [abs_of_nonpos (by linarith [ht.2] : t-1≤0)]
      linarith [ht.1])).2
  · intro t ht
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
    change G t = coordinates e (IccExtend zero_le_one d t)
    rw [IccExtend_of_mem zero_le_one d htI]
    exact (hGrep ⟨t,htI⟩ (by
      simp only [Set.Icc.coe_zero,sub_zero]
      rw [abs_of_nonneg ht.1]
      linarith [ht.2])).2

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology
variable {M : Type u} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}

/-- Actual graph-star geometry supplies the fixed-ray description of every
continuous punctured arc in the graph. No ray assignment is assumed. -/
theorem fixed_ray_of_graphStar_arc (g : GraphStar G p) (c : ℝ → M)
    (δ : ℝ) (hδ : 0 < δ) (hc : ContinuousOn c (Icc 0 δ))
    (hmem : ∀ t ∈ Icc 0 δ, c t ∈ g.neighborhood)
    (hne : ∀ t ∈ Ioo 0 δ, c t ≠ p)
    (hgraph : ∀ t ∈ Ioo 0 δ, c t ∈ G.carrier) :
    ∃ i : Fin g.rayCount, ∀ t ∈ Ioo 0 δ,
      coordinates g.chart (c t) - coordinates g.chart p =
        ‖coordinates g.chart (c t) - coordinates g.chart p‖ • g.direction i := by
  let f : ℝ → Plane := fun t => coordinates g.chart (c t)-coordinates g.chart p
  have hcont : ContinuousOn f (Ioo 0 δ) := by
    apply ContinuousOn.sub _ continuousOn_const
    exact ((continuousOn_coordinates g.chart).comp hc
      (fun t ht => (hmem t ht).1)).mono Ioo_subset_Icc_self
  have hnonzero : ∀ t ∈ Ioo 0 δ, f t ≠ 0 := by
    intro t ht heq
    apply hne t ht
    exact coordinates_injOn g.chart (hmem t ⟨ht.1.le,ht.2.le⟩).1
      g.mem_source (sub_eq_zero.mp heq)
  have hrays : ∀ t ∈ Ioo 0 δ,
      ∃ (i : Fin g.rayCount) (r : ℝ), 0 < r ∧ f t = r • g.direction i := by
    intro t ht
    have hm := hmem t ⟨ht.1.le,ht.2.le⟩
    obtain hp | ⟨i,r,hr,_,heq⟩ := (g.graph_eq (c t) hm.1 hm.2).mp (hgraph t ht)
    · exact False.elim (hne t ht hp)
    · refine ⟨i,r,hr,?_⟩
      dsimp [f]
      rw [heq,add_sub_cancel_left]
  exact fixed_ray_on_interval g.direction g.direction_unit δ hδ f hcont hnonzero hrays

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology
variable {M : Type u} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- The outgoing real extension of either endpoint of an actual graph edge.
Terminal tails use the parameter 1-t and initial tails the parameter t. -/
def outgoingEdge (G : EmbeddedGraph S) (i : Fin G.edgeCount) (b : Bool) : ℝ → M :=
  fun t => IccExtend zero_le_one (G.edge i) (if b then 1-t else t)

theorem outgoingEdge_continuous (G : EmbeddedGraph S) (i : Fin G.edgeCount) (b : Bool) :
    Continuous (outgoingEdge G i b) := by
  cases b
  · exact (G.edge i).continuous.Icc_extend'
  · exact (G.edge i).continuous.Icc_extend'.comp (continuous_const.sub continuous_id)

theorem outgoingEdge_zero (G : EmbeddedGraph S) (i : Fin G.edgeCount) (b : Bool) :
    outgoingEdge G i b 0 = G.vertex (if b then G.terminal i else G.initial i) := by
  cases b
  · simpa only [outgoingEdge,Bool.false_eq_true,ite_false] using
      (IccExtend_of_mem zero_le_one (G.edge i) (by norm_num : (0 : ℝ) ∈ Icc 0 1)).trans (G.at_zero i)
  · simpa only [outgoingEdge,ite_true,sub_zero] using
      (IccExtend_of_mem zero_le_one (G.edge i) (by norm_num : (1 : ℝ) ∈ Icc 0 1)).trans (G.at_one i)

theorem outgoingEdge_parameter_bounds (b : Bool) {t : ℝ} (ht : t ∈ Ioo 0 (1/2 : ℝ)) :
    0 < (if b then 1-t else t) ∧ (if b then 1-t else t) < 1 := by
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    constructor <;> linarith [ht.1,ht.2]

theorem outgoingEdge_avoids_vertices (G : EmbeddedGraph S) (i : Fin G.edgeCount) (b : Bool)
    {t : ℝ} (ht : t ∈ Ioo 0 (1/2 : ℝ)) : outgoingEdge G i b t ∉ range G.vertex := by
  have hb := outgoingEdge_parameter_bounds b ht
  dsimp [outgoingEdge]
  rw [IccExtend_of_mem zero_le_one (G.edge i) ⟨hb.1.le,hb.2.le⟩]
  exact G.avoids_vertices i _ hb.1 hb.2

theorem outgoingEdge_mem_carrier (G : EmbeddedGraph S) (i : Fin G.edgeCount) (b : Bool)
    (t : ℝ) : outgoingEdge G i b t ∈ G.carrier := by
  exact Or.inr (mem_iUnion.mpr ⟨i,⟨_,rfl⟩⟩)

/-- Distinct endpoint incidences have disjoint sufficiently short outgoing
tails. This includes the two incidences of the same loop. -/
theorem outgoingEdge_intersection (G : EmbeddedGraph S)
    {i j : Fin G.edgeCount} {b c : Bool} {s t : ℝ}
    (hs : s ∈ Ioo 0 (1/2 : ℝ)) (ht : t ∈ Ioo 0 (1/2 : ℝ))
    (heq : outgoingEdge G i b s = outgoingEdge G j c t) : i = j ∧ b = c ∧ s = t := by
  have hbs := outgoingEdge_parameter_bounds b hs
  have hct := outgoingEdge_parameter_bounds c ht
  let qs : unitInterval := ⟨(if b then 1-s else s),hbs.1.le,hbs.2.le⟩
  let qt : unitInterval := ⟨(if c then 1-t else t),hct.1.le,hct.2.le⟩
  have hsimp : G.edge i qs = G.edge j qt := by
    change IccExtend zero_le_one (G.edge i) (qs : ℝ) =
      IccExtend zero_le_one (G.edge j) (qt : ℝ) at heq
    simpa only [IccExtend_of_mem zero_le_one (G.edge i) qs.property,
      IccExtend_of_mem zero_le_one (G.edge j) qt.property] using heq
  have hij : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (G.disjoint_open_edges hn) ⟨qs,hbs,rfl⟩ ⟨qt,hct,hsimp.symm⟩
  subst j
  have hparam := congrArg (fun q : unitInterval => (q : ℝ))
    (G.open_injective i hbs hct hsimp)
  change (if b then 1-s else s) = (if c then 1-t else t) at hparam
  have hbc : b = c := by
    cases b <;> cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hparam ⊢ <;>
      linarith [hs.2,ht.2]
  refine ⟨rfl,hbc,?_⟩
  subst c
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hparam
  · exact hparam
  · linarith

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology
variable {M : Type u} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- Every actual endpoint incidence selects a unique star ray after shrinking
the outgoing interval. The selected interval omits the opposite tail of a
loop and lies in the actual star neighborhood. -/
theorem outgoingEdge_fixed_ray (G : EmbeddedGraph S) (i : Fin G.edgeCount) (b : Bool)
    (g : GraphStar G (G.vertex (if b then G.terminal i else G.initial i))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      (∀ t ∈ Icc 0 δ, outgoingEdge G i b t ∈ g.neighborhood) ∧
      ∃ k : Fin g.rayCount, ∀ t ∈ Ioo 0 δ,
        coordinates g.chart (outgoingEdge G i b t) -
            coordinates g.chart (G.vertex (if b then G.terminal i else G.initial i)) =
          ‖coordinates g.chart (outgoingEdge G i b t) -
            coordinates g.chart (G.vertex (if b then G.terminal i else G.initial i))‖ •
              g.direction k := by
  have hc := outgoingEdge_continuous G i b
  have hneigh : outgoingEdge G i b ⁻¹' g.neighborhood ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by
      rw [outgoingEdge_zero]
      exact (P202.SurfaceRegionConstruction.GraphStar.isOpen_neighborhood g).mem_nhds
        (P202.SurfaceRegionConstruction.GraphStar.mem_neighborhood g))
  obtain ⟨ε,hε,hεball⟩ := Metric.mem_nhds_iff.mp hneigh
  let δ := min ε (1/2 : ℝ) / 2
  have hδ : 0 < δ := div_pos (lt_min hε (by norm_num)) (by norm_num)
  have hδε : δ < ε := by dsimp [δ]; have := min_le_left ε (1/2 : ℝ); linarith
  have hδhalf : δ < (1/2 : ℝ) := by
    dsimp [δ]
    have := min_le_right ε (1/2 : ℝ)
    linarith
  have hmem : ∀ t ∈ Icc 0 δ, outgoingEdge G i b t ∈ g.neighborhood := by
    intro t ht
    apply hεball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 hδε
  refine ⟨δ,hδ,hδhalf,hmem,?_⟩
  apply fixed_ray_of_graphStar_arc g (outgoingEdge G i b) δ hδ hc.continuousOn hmem
  · intro t ht heq
    exact outgoingEdge_avoids_vertices G i b ⟨ht.1,lt_trans ht.2 hδhalf⟩
      ⟨_,heq.symm⟩
  · intro t _
    exact outgoingEdge_mem_carrier G i b t

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology
variable {M : Type u} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- Endpoint incidences assigned the same star ray are equal. All arc and
nonintersection inputs here are the actual outgoing graph-edge tails. -/
theorem outgoingEdge_ray_injective (G : EmbeddedGraph S) {p : M} (g : GraphStar G p)
    {i j : Fin G.edgeCount} {b c : Bool} (hi : outgoingEdge G i b 0 = p)
    (hj : outgoingEdge G j c 0 = p) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1/2)
    (hmi : ∀ t ∈ Icc 0 δ, outgoingEdge G i b t ∈ g.neighborhood)
    (hmj : ∀ t ∈ Icc 0 δ, outgoingEdge G j c t ∈ g.neighborhood)
    (k : Fin g.rayCount)
    (hri : ∀ t ∈ Ioo 0 δ,
      coordinates g.chart (outgoingEdge G i b t) - coordinates g.chart p =
        ‖coordinates g.chart (outgoingEdge G i b t) - coordinates g.chart p‖ • g.direction k)
    (hrj : ∀ t ∈ Ioo 0 δ,
      coordinates g.chart (outgoingEdge G j c t) - coordinates g.chart p =
        ‖coordinates g.chart (outgoingEdge G j c t) - coordinates g.chart p‖ • g.direction k) :
    i = j ∧ b = c := by
  let f : ℝ → Plane := fun t => coordinates g.chart (outgoingEdge G i b t) - coordinates g.chart p
  let h : ℝ → Plane := fun t => coordinates g.chart (outgoingEdge G j c t) - coordinates g.chart p
  have hfi : ContinuousOn f (Icc 0 δ) :=
    ((continuousOn_coordinates g.chart).comp (outgoingEdge_continuous G i b).continuousOn
      (fun t ht => (hmi t ht).1)).sub continuousOn_const
  have hfj : ContinuousOn h (Icc 0 δ) :=
    ((continuousOn_coordinates g.chart).comp (outgoingEdge_continuous G j c).continuousOn
      (fun t ht => (hmj t ht).1)).sub continuousOn_const
  have hf0 : f 0 = 0 := by dsimp [f]; rw [hi,sub_self]
  have hh0 : h 0 = 0 := by dsimp [h]; rw [hj,sub_self]
  have hmid : δ/2 ∈ Ioo (0 : ℝ) δ := by constructor <;> linarith
  have hfmid : f (δ/2) ≠ 0 := by
    intro heq
    have heqp := coordinates_injOn g.chart (hmi (δ/2) ⟨hmid.1.le,hmid.2.le⟩).1
      g.mem_source (sub_eq_zero.mp heq)
    apply outgoingEdge_avoids_vertices G i b ⟨hmid.1,lt_trans hmid.2 hδhalf⟩
    refine ⟨(if b then G.terminal i else G.initial i),?_⟩
    exact (outgoingEdge_zero G i b).symm.trans (hi.trans heqp.symm)
  have hhmid : h (δ/2) ≠ 0 := by
    intro heq
    have heqp := coordinates_injOn g.chart (hmj (δ/2) ⟨hmid.1.le,hmid.2.le⟩).1
      g.mem_source (sub_eq_zero.mp heq)
    apply outgoingEdge_avoids_vertices G j c ⟨hmid.1,lt_trans hmid.2 hδhalf⟩
    refine ⟨(if c then G.terminal j else G.initial j),?_⟩
    exact (outgoingEdge_zero G j c).symm.trans (hj.trans heqp.symm)
  obtain ⟨s,hs,t,ht,hst⟩ := same_ray_arcs_intersect f h (g.direction k) δ hδ
    hfi hfj hf0 hh0 hfmid hhmid hri hrj
  have hpst := coordinates_injOn g.chart (hmi s ⟨hs.1.le,hs.2.le⟩).1
    (hmj t ⟨ht.1.le,ht.2.le⟩).1 (sub_left_inj.mp hst)
  have h := outgoingEdge_intersection G ⟨hs.1,lt_trans hs.2 hδhalf⟩
    ⟨ht.1,lt_trans ht.2 hδhalf⟩ hpst
  exact ⟨h.1,h.2.1⟩

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology
variable {M : Type u} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}

/-- Every actual star ray meets every neighborhood of its center. The model
and target clauses in GraphStar ensure this also at a surface boundary. -/
theorem graphStar_ray_meets_open (g : GraphStar G p) (k : Fin g.rayCount)
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ x ∈ O, x ∈ g.neighborhood ∧ x ≠ p ∧
      ∃ r : ℝ, 0 < r ∧ r < g.radius ∧
        coordinates g.chart x = coordinates g.chart p + r • g.direction k := by
  let r : unitInterval → ℝ := fun t => (t : ℝ)*g.radius/2
  have hrnonneg (t : unitInterval) : 0 ≤ r t := by
    dsimp [r]
    exact div_nonneg (mul_nonneg t.property.1 g.radius_pos.le) (by norm_num)
  have hrlt (t : unitInterval) : r t < g.radius := by
    dsimp [r]
    nlinarith [t.property.2,g.radius_pos]
  have hmodel (t : unitInterval) :
      toPlane.symm (coordinates g.chart p + r t • g.direction k) ∈ modelSet 2 kind := by
    by_cases ht : (t : ℝ) = 0
    · simpa only [r,ht,zero_mul,zero_div,zero_smul,add_zero,coordinates,
        toPlane.symm_apply_apply] using (g.chart p).property
    · apply g.rays_in_model k (r t) _ (hrlt t)
      dsimp [r]
      exact div_pos (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) g.radius_pos) (by norm_num)
  let z : unitInterval → ModelSpace 2 kind := fun t =>
    ⟨toPlane.symm (coordinates g.chart p + r t • g.direction k),hmodel t⟩
  have hz : Continuous z := by
    apply Continuous.subtype_mk
    apply toPlane.symm.continuous.comp
    exact continuous_const.add (((continuous_subtype_val.mul_const g.radius).div_const 2).smul continuous_const)
  have hztarget (t : unitInterval) : z t ∈ g.chart.target := by
    apply g.ball_in_target
    change ‖coordinates g.chart p + r t • g.direction k - coordinates g.chart p‖ < g.radius
    rw [add_sub_cancel_left,norm_smul,g.direction_unit,Real.norm_eq_abs,abs_of_nonneg (hrnonneg t),mul_one]
    exact hrlt t
  let c : C(unitInterval,M) := ⟨fun t => g.chart.symm (z t),
    g.chart.continuousOn_symm.comp_continuous hz hztarget⟩
  have hz0 : z 0 = g.chart p := by
    apply Subtype.ext
    simp only [z,r,Set.Icc.coe_zero,zero_mul,zero_div,zero_smul,add_zero,coordinates,toPlane.symm_apply_apply]
  have hc0 : c 0 = p := by
    change g.chart.symm (z 0) = p
    rw [hz0,g.chart.left_inv g.mem_source]
  have hcO : IsOpen (c ⁻¹' O) := hO.preimage c.continuous
  obtain ⟨ε,hε,hεball⟩ := Metric.isOpen_iff.mp hcO 0 (by simpa only [mem_preimage,hc0] using hpO)
  let a : ℝ := min ε 1 / 2
  have ha0 : 0 < a := div_pos (lt_min hε (by norm_num)) (by norm_num)
  have ha1 : a ≤ 1 := by dsimp [a]; have := min_le_right ε 1; linarith
  have haε : a < ε := by dsimp [a]; have := min_le_left ε 1; linarith
  let t : unitInterval := ⟨a,ha0.le,ha1⟩
  have htO : c t ∈ O := by
    apply hεball
    change |a-0| < ε
    rwa [sub_zero,abs_of_pos ha0]
  have hsource : c t ∈ g.chart.source := g.chart.map_target (hztarget t)
  have hcoord : coordinates g.chart (c t) = coordinates g.chart p + r t • g.direction k := by
    change toPlane (g.chart (g.chart.symm (z t))).val = _
    rw [g.chart.right_inv (hztarget t)]
    exact toPlane.apply_symm_apply _
  have hrpos : 0 < r t := div_pos (mul_pos ha0 g.radius_pos) (by norm_num)
  refine ⟨c t,htO,⟨hsource,?_⟩,?_,r t,hrpos,hrlt t,hcoord⟩
  · rw [mem_preimage,hcoord,Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
      g.direction_unit,Real.norm_eq_abs,abs_of_pos hrpos,mul_one]
    exact hrlt t
  · intro heq
    rw [heq] at hcoord
    have hn := congrArg norm (add_left_cancel (hcoord.symm.trans (add_zero (coordinates g.chart p)).symm))
    rw [norm_smul,g.direction_unit,Real.norm_eq_abs,abs_of_pos hrpos,mul_one,norm_zero] at hn
    exact hrpos.ne' hn

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
open P202Specs.PlanarRegionTopology
variable {M : Type u} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

structure EndpointRayData (G : EmbeddedGraph S) (v : Fin G.vertexCount)
    (g : GraphStar G (G.vertex v)) (d : Fin G.edgeCount × Bool) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_half : radius < 1/2
  mem : ∀ t ∈ Icc 0 radius, outgoingEdge G d.1 d.2 t ∈ g.neighborhood
  ray : Fin g.rayCount
  formula : ∀ t ∈ Ioo 0 radius,
    coordinates g.chart (outgoingEdge G d.1 d.2 t)-coordinates g.chart (G.vertex v) =
      ‖coordinates g.chart (outgoingEdge G d.1 d.2 t)-coordinates g.chart (G.vertex v)‖ • g.direction ray

theorem endpointRayData_exists (G : EmbeddedGraph S) (v : Fin G.vertexCount)
    (g : GraphStar G (G.vertex v)) (d : Fin G.edgeCount × Bool)
    (hd : (if d.2 then G.terminal d.1 else G.initial d.1) = v) :
    Nonempty (EndpointRayData G v g d) := by
  rcases d with ⟨i,b⟩
  dsimp at hd
  subst v
  obtain ⟨δ,hδ,hhalf,hmem,k,hk⟩ := outgoingEdge_fixed_ray G i b g
  exact ⟨⟨δ,hδ,hhalf,hmem,k,hk⟩⟩

/-- Exact graph valence equals the number of geometric rays in an actual
star, with the two endpoint incidences of a loop counted separately. -/
theorem graphStar_incidence_ncard (G : EmbeddedGraph S) (v : Fin G.vertexCount)
    (g : GraphStar G (G.vertex v)) :
    {d : Fin G.edgeCount × Bool | (if d.2 then G.terminal d.1 else G.initial d.1) = v}.ncard =
      g.rayCount := by
  classical
  let I := {d : Fin G.edgeCount × Bool // (if d.2 then G.terminal d.1 else G.initial d.1) = v}
  letI : Fintype I := Fintype.ofFinite I
  let a : (d : I) → EndpointRayData G v g d.val :=
    fun d => Classical.choice (endpointRayData_exists G v g d.val d.property)
  let f : I → Fin g.rayCount := fun d => (a d).ray
  have hzero (d : I) : outgoingEdge G d.val.1 d.val.2 0 = G.vertex v := by
    rw [outgoingEdge_zero,d.property]
  have hinj : Function.Injective f := by
    intro d e hde
    let δ := min (a d).radius (a e).radius / 2
    have hδ : 0 < δ := div_pos (lt_min (a d).radius_pos (a e).radius_pos) (by norm_num)
    have hδd : δ < (a d).radius := by
      dsimp [δ]; have := min_le_left (a d).radius (a e).radius; linarith [(a d).radius_pos]
    have hδe : δ < (a e).radius := by
      dsimp [δ]; have := min_le_right (a d).radius (a e).radius; linarith [(a e).radius_pos]
    have hhalf : δ < (1/2 : ℝ) := lt_trans hδd (a d).radius_half
    have hmemd : ∀ t ∈ Icc 0 δ, outgoingEdge G d.val.1 d.val.2 t ∈ g.neighborhood :=
      fun t ht => (a d).mem t ⟨ht.1,le_trans ht.2 hδd.le⟩
    have hmeme : ∀ t ∈ Icc 0 δ, outgoingEdge G e.val.1 e.val.2 t ∈ g.neighborhood :=
      fun t ht => (a e).mem t ⟨ht.1,le_trans ht.2 hδe.le⟩
    have hrayd := fun t (ht : t ∈ Ioo 0 δ) => (a d).formula t ⟨ht.1,lt_trans ht.2 hδd⟩
    have hraye := fun t (ht : t ∈ Ioo 0 δ) => (a e).formula t ⟨ht.1,lt_trans ht.2 hδe⟩
    change (a d).ray = (a e).ray at hde
    rw [← hde] at hraye
    have heq := outgoingEdge_ray_injective G g (hzero d) (hzero e) δ hδ hhalf
      hmemd hmeme (a d).ray hrayd hraye
    exact Subtype.ext (Prod.ext heq.1 heq.2)
  let radii : Option I → ℝ := fun d => match d with | none => 1/2 | some d => (a d).radius
  have hpos (d : Option I) : 0 < radii d := by
    cases d with
    | none => norm_num [radii]
    | some d => exact (a d).radius_pos
  let ε := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Option I)).Nonempty) radii
  have hε : 0 < ε := (Finset.lt_inf'_iff _).mpr (fun d _ => hpos d)
  have hεhalf : ε ≤ (1/2 : ℝ) := Finset.inf'_le _ (Finset.mem_univ none)
  have hεd (d : I) : ε ≤ (a d).radius := Finset.inf'_le _ (Finset.mem_univ (some d))
  obtain ⟨O,hO,hvO,hOgraph⟩ := vertex_tail_neighborhood G v ε hε (by linarith)
  have hsurj : Function.Surjective f := by
    intro k
    obtain ⟨x,hxO,hxneigh,hxne,r,hr,hrr,hxcoord⟩ := graphStar_ray_meets_open g k O hO hvO
    have hxgraph : x ∈ G.carrier := (g.graph_eq x hxneigh.1 hxneigh.2).mpr
      (Or.inr ⟨k,r,hr,hrr,hxcoord⟩)
    rcases (hOgraph x hxO).mp hxgraph with hx | ⟨i,q,hqx,hi | hi⟩
    · exact False.elim (hxne hx)
    · let d : I := ⟨(i,false),hi.1⟩
      have hqpos : 0 < (q : ℝ) := by
        apply lt_of_le_of_ne q.property.1
        intro hq0
        have hqzero : q = 0 := Subtype.ext hq0.symm
        apply hxne
        rw [← hqx,hqzero,G.at_zero,hi.1]
      have hqt : (q : ℝ) ∈ Ioo 0 (a d).radius := ⟨hqpos,lt_of_lt_of_le hi.2 (hεd d)⟩
      have hxout : outgoingEdge G i false q = x := by
        simpa only [outgoingEdge,Bool.false_eq_true,ite_false,
          IccExtend_of_mem zero_le_one (G.edge i) q.property] using hqx
      have hf := (a d).formula q hqt
      rw [hxout,hxcoord,add_sub_cancel_left,norm_smul,g.direction_unit,
        Real.norm_eq_abs,abs_of_pos hr,mul_one] at hf
      refine ⟨d,?_⟩
      apply g.direction_injective
      exact (smul_right_injective _ hr.ne' hf).symm
    · let d : I := ⟨(i,true),hi.1⟩
      have hqone : (q : ℝ) < 1 := by
        apply lt_of_le_of_ne q.property.2
        intro hq1
        have hqeq : q = 1 := Subtype.ext hq1
        apply hxne
        rw [← hqx,hqeq,G.at_one,hi.1]
      have hqt : (1-(q : ℝ)) ∈ Ioo 0 (a d).radius := by
        constructor
        · linarith
        · have := hεd d; linarith [hi.2]
      have hxout : outgoingEdge G i true (1-(q : ℝ)) = x := by
        dsimp [outgoingEdge]
        rw [sub_sub_cancel,IccExtend_of_mem zero_le_one (G.edge i) q.property]
        exact hqx
      have hf := (a d).formula (1-(q : ℝ)) hqt
      rw [hxout,hxcoord,add_sub_cancel_left,norm_smul,g.direction_unit,
        Real.norm_eq_abs,abs_of_pos hr,mul_one] at hf
      refine ⟨d,?_⟩
      apply g.direction_injective
      exact (smul_right_injective _ hr.ne' hf).symm
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)).trans (Nat.card_fin g.rayCount)

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction

theorem chamber_boundary_ray_card (J : Set (Fin 2)) (σ : Fin 2 → Bool)
    (hJ : J.Nonempty) :
    Nat.card {q : Fin 2 × Bool // q.1 ∈ J ∧
      ∀ a ∈ J, if σ a then 0 ≤ AxisRays.direction q a else AxisRays.direction q a ≤ 0} = 2 := by
  classical
  let : Fintype {q : Fin 2 × Bool // q.1 ∈ J ∧
      ∀ a ∈ J, if σ a then 0 ≤ AxisRays.direction q a else AxisRays.direction q a ≤ 0} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have hforms : J = {0} ∨ J = {1} ∨ J = univ := by
    by_cases h0 : (0 : Fin 2) ∈ J
    · by_cases h1 : (1 : Fin 2) ∈ J
      · right; right; ext a; fin_cases a <;> simp_all
      · left; ext a; fin_cases a <;> simp_all
    · right; left
      have h1 : (1 : Fin 2) ∈ J := by
        obtain ⟨a,ha⟩ := hJ
        fin_cases a
        · exact False.elim (h0 ha)
        · exact ha
      ext a; fin_cases a <;> simp_all
  have huni : (Finset.univ : Finset (Fin 2 × Bool)) =
      {(0,false),(0,true),(1,false),(1,true)} := by decide
  rcases hforms with rfl | rfl | rfl <;>
    cases hσ0 : σ 0 <;> cases hσ1 : σ 1 <;>
    norm_num [Fintype.card_subtype,huni,Finset.filter_insert,Finset.filter_singleton,
      AxisRays.direction,axisTangent,toPlane,Fin.forall_fin_two,hσ0,hσ1]

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction

theorem mem_closure_iff_coordinates_mem_closure_local
    {kind : ModelKind} {X : Type*} [TopologicalSpace X]
    (e : ModelChart 2 kind X) (C : Set X) {x : X} (hx : x ∈ e.source) :
    x ∈ closure C ↔ coordinates e x ∈ closure (coordinates e '' (C ∩ e.source)) := by
  let m : ModelSpace 2 kind → Plane := fun z => toPlane z.val
  have hm : IsEmbedding m := toPlane.toHomeomorph.isEmbedding.comp IsEmbedding.subtypeVal
  constructor
  · intro hxC
    have hxlocal : x ∈ closure (C ∩ e.source) := e.open_source.closure_inter ⟨hxC,hx⟩
    exact ((continuousOn_coordinates e x hx).mono inter_subset_right).mem_closure_image hxlocal
  · intro hxcoords
    have himage : coordinates e '' (C ∩ e.source) = m '' (e '' (C ∩ e.source)) := by
      change (fun x => m (e x)) '' (C ∩ e.source) = _
      exact (image_image _ _ _).symm
    rw [himage] at hxcoords
    have hxmodel : e x ∈ closure (e '' (C ∩ e.source)) := by
      rw [hm.closure_eq_preimage_closure_image]
      exact hxcoords
    have hecont : ContinuousAt e.symm (e x) := e.symm.continuousOn.continuousAt
      (e.open_target.mem_nhds (e.map_source hx))
    have hxback := hecont.continuousWithinAt.mem_closure_image hxmodel
    rw [e.left_inv hx] at hxback
    apply closure_mono (show e.symm '' (e '' (C ∩ e.source)) ⊆ C from ?_) hxback
    rintro y ⟨z,⟨w,hw,rfl⟩,rfl⟩
    simpa only [e.left_inv hw.2] using hw.1
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction.NormalSectors
 theorem mem_closure_chamber_iff_weak_signs (J : Set (Fin 2)) (r : ℝ)
    (σ : Fin 2 → Bool) {z : Plane} (hz : z ∈ Metric.ball 0 r)
    (hne : (chamber J r σ).Nonempty) :
    z ∈ closure (chamber J r σ) ↔ ∀ a ∈ J, if σ a then 0 ≤ z a else z a ≤ 0 := by
  have hclosed : IsClosed {z : Plane | ∀ a ∈ J, if σ a then 0 ≤ z a else z a ≤ 0} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro ha
    cases σ a
    · exact isClosed_le (by fun_prop) continuous_const
    · exact isClosed_le continuous_const (by fun_prop)
  constructor
  · apply closure_minimal _ hclosed
    intro x hx a ha
    have hs := mem_iInter₂.mp hx.2 a ha
    cases hσ : σ a <;> simp only [hσ,Bool.false_eq_true,↓reduceIte] at hs ⊢ <;> exact hs.le
  · intro hweak
    exact mem_closure_chamber_of_weak_signs J r σ hz hweak hne

 theorem mem_closure_translated_chamber_iff_weak_signs
    (J : Set (Fin 2)) (r : ℝ) (σ : Fin 2 → Bool) (c : Plane)
    {z : Plane} (hz : z ∈ Metric.ball c r)
    (hne : ({w : Plane | w-c ∈ PlaneSectors.signedOrthant J σ} ∩ Metric.ball c r).Nonempty) :
    z ∈ closure ({w : Plane | w-c ∈ PlaneSectors.signedOrthant J σ} ∩ Metric.ball c r) ↔
      ∀ a ∈ J, if σ a then 0 ≤ (z-c) a else (z-c) a ≤ 0 := by
  have heq : {w : Plane | w-c ∈ PlaneSectors.signedOrthant J σ} ∩ Metric.ball c r =
      (Homeomorph.subRight c) ⁻¹' chamber J r σ := by
    ext w
    simp only [mem_inter_iff,mem_setOf_eq,mem_preimage,chamber,PlaneSectors.signedOrthant,
      Homeomorph.subRight_apply,mem_iInter,Metric.mem_ball,dist_eq_norm,sub_zero]
    exact and_comm
  have hne' : (chamber J r σ).Nonempty := by
    obtain ⟨w,hw⟩ := hne
    exact ⟨w-c,by rwa [heq] at hw⟩
  rw [heq,← (Homeomorph.subRight c).preimage_closure]
  exact mem_closure_chamber_iff_weak_signs J r σ
    (by simpa only [Homeomorph.subRight_apply,Metric.mem_ball,dist_eq_norm,sub_zero] using hz) hne'
end P202.SurfaceRegionConstruction.NormalSectors
namespace P202.SurfaceRegionConstruction

theorem local_coordinate_chamber_membership
    {kind : ModelKind} {X : Type*} [TopologicalSpace X]
    (e : ModelChart 2 kind X) (C : Set X) (p : X) (J : Set (Fin 2))
    (σ : Fin 2 → Bool) (r : ℝ)
    (himage : coordinates e '' (C ∩ e.source) =
      {z | z-coordinates e p ∈ PlaneSectors.signedOrthant J σ} ∩ Metric.ball (coordinates e p) r)
    {x : X} (hx : x ∈ e.source) (hxball : coordinates e x ∈ Metric.ball (coordinates e p) r) :
    x ∈ C ↔ coordinates e x-coordinates e p ∈ PlaneSectors.signedOrthant J σ := by
  constructor
  · intro hxC
    have hxim : coordinates e x ∈ coordinates e '' (C ∩ e.source) := ⟨x,⟨hxC,hx⟩,rfl⟩
    exact (himage ▸ hxim).1
  · intro hxsign
    have hxim : coordinates e x ∈ coordinates e '' (C ∩ e.source) := by
      rw [himage]
      exact ⟨hxsign,hxball⟩
    obtain ⟨y,hy,hxy⟩ := hxim
    exact ((coordinates_injOn e hy.2 hx hxy) ▸ hy.1)

theorem local_coordinate_chamber_closure
    {kind : ModelKind} {X : Type*} [TopologicalSpace X]
    (e : ModelChart 2 kind X) (C : Set X) (p : X) (J : Set (Fin 2))
    (σ : Fin 2 → Bool) (r : ℝ)
    (himage : coordinates e '' (C ∩ e.source) =
      {z | z-coordinates e p ∈ PlaneSectors.signedOrthant J σ} ∩ Metric.ball (coordinates e p) r)
    (hne : (C ∩ e.source).Nonempty)
    {x : X} (hx : x ∈ e.source) (hxball : coordinates e x ∈ Metric.ball (coordinates e p) r) :
    x ∈ closure C ↔ ∀ a ∈ J,
      if σ a then 0 ≤ (coordinates e x-coordinates e p) a else
        (coordinates e x-coordinates e p) a ≤ 0 := by
  rw [mem_closure_iff_coordinates_mem_closure_local e C hx,himage]
  exact NormalSectors.mem_closure_translated_chamber_iff_weak_signs J r σ _ hxball
    (himage ▸ hne.image _)

theorem local_coordinate_chamber_frontier
    {kind : ModelKind} {X : Type*} [TopologicalSpace X]
    (e : ModelChart 2 kind X) (C : Set X) (hC : IsOpen C) (p : X)
    (J : Set (Fin 2)) (σ : Fin 2 → Bool) (r : ℝ)
    (himage : coordinates e '' (C ∩ e.source) =
      {z | z-coordinates e p ∈ PlaneSectors.signedOrthant J σ} ∩ Metric.ball (coordinates e p) r)
    (hne : (C ∩ e.source).Nonempty)
    {x : X} (hx : x ∈ e.source) (hxball : coordinates e x ∈ Metric.ball (coordinates e p) r) :
    x ∈ frontier C ↔
      (∀ a ∈ J, if σ a then 0 ≤ (coordinates e x-coordinates e p) a else
        (coordinates e x-coordinates e p) a ≤ 0) ∧
      ∃ a ∈ J, (coordinates e x-coordinates e p) a = 0 := by
  classical
  rw [frontier,hC.interior_eq,mem_diff,local_coordinate_chamber_closure e C p J σ r himage hne hx hxball,
    local_coordinate_chamber_membership e C p J σ r himage hx hxball]
  constructor
  · rintro ⟨hw,hs⟩
    refine ⟨hw,?_⟩
    simp only [PlaneSectors.signedOrthant,mem_ofPred_eq] at hs
    push_neg at hs
    obtain ⟨a,ha,hs⟩ := hs
    refine ⟨a,ha,?_⟩
    have haweak := hw a ha
    cases hσ : σ a <;> simp only [hσ,Bool.false_eq_true,↓reduceIte] at hs haweak
    · exact le_antisymm haweak (le_of_not_gt hs)
    · exact le_antisymm (le_of_not_gt hs) haweak
  · rintro ⟨hw,a,ha,hzero⟩
    refine ⟨hw,?_⟩
    intro hs
    have hast := hs a ha
    rw [hzero] at hast
    cases σ a <;> simpa using hast
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction

theorem closure_coordinate_image_subset_model
    {kind : ModelKind} {X : Type*} [TopologicalSpace X]
    (e : ModelChart 2 kind X) (C : Set X) :
    closure (coordinates e '' C) ⊆ {z : Plane | toPlane.symm z ∈ modelSet 2 kind} := by
  apply closure_minimal
  · rintro z ⟨x,hx,rfl⟩
    change toPlane.symm (coordinates e x) ∈ modelSet 2 kind
    simpa only [coordinates,toPlane.symm_apply_apply] using (e x).property
  · exact (SmoothManifolds.isClosed_modelSet 2 kind).preimage toPlane.symm.continuous

theorem local_coordinate_chamber_ray_in_model
    {kind : ModelKind} {X : Type*} [TopologicalSpace X]
    (e : ModelChart 2 kind X) (C : Set X) (p : X)
    (J : Set (Fin 2)) (σ : Fin 2 → Bool) (r : ℝ)
    (himage : coordinates e '' (C ∩ e.source) =
      {z | z-coordinates e p ∈ PlaneSectors.signedOrthant J σ} ∩ Metric.ball (coordinates e p) r)
    (hne : (C ∩ e.source).Nonempty)
    (q : Fin 2 × Bool)
    (hweak : ∀ a ∈ J, if σ a then 0 ≤ AxisRays.direction q a else AxisRays.direction q a ≤ 0)
    (t : ℝ) (ht : 0 < t) (htr : t < r) :
    toPlane.symm (coordinates e p + t • AxisRays.direction q) ∈ modelSet 2 kind := by
  apply closure_coordinate_image_subset_model e (C ∩ e.source)
  rw [himage]
  apply (NormalSectors.mem_closure_translated_chamber_iff_weak_signs J r σ _ ?_
    (himage ▸ hne.image _)).mpr
  · intro a ha
    have hs := hweak a ha
    simp only [add_sub_cancel_left,PiLp.smul_apply,smul_eq_mul]
    cases hσ : σ a <;> simp only [hσ,Bool.false_eq_true,↓reduceIte] at hs ⊢
    · exact mul_nonpos_of_nonneg_of_nonpos ht.le hs
    · exact mul_nonneg ht.le hs
  · rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,AxisRays.direction_norm,
      mul_one,Real.norm_eq_abs,abs_of_pos ht]
    exact htr
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement
variable {kind : ModelKind} {X : Type u} [TopologicalSpace X]
variable (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
variable (s : Bool)
variable {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
variable {B : CompactSmoothSeam D.manifold}
variable (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
variable (T : TransverseDiskArrangement D.manifold
  (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
include hB

theorem restricted_arrangement_frontier_local_chamber
    (G : Set X)
    (hG : G = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)
    (c : ConnectedComponents (Gᶜ : Set X))
    (hc : IsOpen (componentSet Gᶜ c)) {p : X}
    (hpc : p ∈ frontier (componentSet Gᶜ c))
    (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ (e : ModelChart 2 kind X) (J : Set (Fin 2)) (σ : Fin 2 → Bool) (r : ℝ),
      e ∈ S.smoothStructure.val ∧ p ∈ e.source ∧ e.source ⊆ O ∧ 0 < r ∧
      (∀ z : ModelSpace 2 kind,
        toPlane z.val ∈ Metric.ball (coordinates e p) r → z ∈ e.target) ∧
      J.Nonempty ∧
      (∀ x ∈ e.source, coordinates e x ∈ Metric.ball (coordinates e p) r →
        (x ∈ frontier (componentSet Gᶜ c) ↔
          (∀ a ∈ J, if σ a then 0 ≤ (coordinates e x-coordinates e p) a else
            (coordinates e x-coordinates e p) a ≤ 0) ∧
          ∃ a ∈ J, (coordinates e x-coordinates e p) a = 0)) ∧
      (∀ q : Fin 2 × Bool,
        (∀ a ∈ J, if σ a then 0 ≤ AxisRays.direction q a else AxisRays.direction q a ≤ 0) →
        ∀ t : ℝ, 0 < t → t < r →
          toPlane.symm (coordinates e p+t • AxisRays.direction q) ∈ modelSet 2 kind) := by
  subst G
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  have hf : IsClosedEmbedding f := D.copy_closedEmbedding s
  obtain ⟨V,hV,hVO⟩ := hf.isEmbedding.isInducing.isOpen_iff.mp hO
  have hpV : f p ∈ V := by change p ∈ f ⁻¹' V; rwa [hVO]
  obtain ⟨F⟩ := T.normal_forms (f p) V hV hpV
  obtain ⟨e,J,σ,he,hes,hep,heball,himage,_⟩ :=
    normal_copy_incident_chamber S D s hB T F c (frontier_subset_closure hpc)
  have heO : e.source ⊆ O := by
    rw [hes,← hVO]
    exact preimage_mono F.neighborhood_subset
  have hne : (componentSet (f ⁻¹' arrangementCarrier T)ᶜ c ∩ e.source).Nonempty := by
    obtain ⟨x,hxs,hx⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hpc) e.source
      (e.open_source.mem_nhds hep)
    exact ⟨x,hx,hxs⟩
  have hfront := fun (x : X) (hx : x ∈ e.source)
      (hxball : coordinates e x ∈ Metric.ball (coordinates e p) F.radius) =>
    local_coordinate_chamber_frontier e (componentSet (f ⁻¹' arrangementCarrier T)ᶜ c)
      hc p J σ F.radius himage hne hx hxball
  have hJ : J.Nonempty := by
    obtain ⟨_,a,ha,_⟩ := (hfront p hep (Metric.mem_ball_self F.radius_pos)).mp hpc
    exact ⟨a,ha⟩
  refine ⟨e,J,σ,F.radius,he,hep,heO,F.radius_pos,heball,hJ,hfront,?_⟩
  intro q hweak t ht htr
  exact local_coordinate_chamber_ray_in_model e
    (componentSet (f ⁻¹' arrangementCarrier T)ᶜ c) p J σ F.radius himage hne q hweak t ht htr
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {kind : ModelKind} {M : Type*} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
/-- Two simple regular graph arcs that meet only at their common end have a
regular noncuspidal directed join. The finite straight rays in an actual
smooth graph star determine their endpoint derivatives. -/
theorem regularEndpointJoin_of_disjoint_graph_arcs
    (c d : C(unitInterval, M)) (hcommon : c 1 = d 0)
    (hci : Function.Injective c) (hdi : Function.Injective d)
    (hdis : Disjoint (c '' {t : unitInterval | 0 < (t:ℝ) ∧ (t:ℝ)<1})
      (d '' {t : unitInterval | 0 < (t:ℝ) ∧ (t:ℝ)<1}))
    (hcG : range c ⊆ G.carrier) (hdG : range d ⊆ G.carrier)
    (g : GraphStar G (c 1))
    (hc : RegularEdgeEndpoints S c) (hd : RegularEdgeEndpoints S d) :
    RegularEndpointJoin
      (fun t => coordinates g.chart (IccExtend zero_le_one c t))
      (fun t => coordinates g.chart (IccExtend zero_le_one d t)) := by
  obtain ⟨ε,l,hε,hl,hnl,hlrep⟩ := hc 1 (Or.inr rfl) g.chart g.chart_mem g.mem_source
  have hds : d 0 ∈ g.chart.source := hcommon ▸ g.mem_source
  obtain ⟨ζ,r,hζ,hr,hnr,hrrep⟩ := hd 0 (Or.inl rfl) g.chart g.chart_mem hds
  have hl1 : l 1 = coordinates g.chart (c 1) := (hlrep 1 (by simpa using hε)).2
  have hr0 : r 0 = coordinates g.chart (c 1) :=
    (hrrep 0 (by simpa using hζ)).2.trans (congrArg (coordinates g.chart) hcommon.symm)
  let co : ℝ → M := fun t => IccExtend zero_le_one c (1-t)
  let dout : ℝ → M := IccExtend zero_le_one d
  have hco : Continuous co := c.continuous.Icc_extend'.comp (continuous_const.sub continuous_id)
  have hdo : Continuous dout := d.continuous.Icc_extend'
  have hco0 : co 0 = c 1 := by
    dsimp [co]
    rw [sub_zero,IccExtend_of_mem zero_le_one c (by norm_num : (1:ℝ) ∈ Icc 0 1)]
    congr 1
  have hdo0 : dout 0 = c 1 := by
    dsimp [dout]
    rw [IccExtend_of_mem zero_le_one d (by norm_num : (0:ℝ) ∈ Icc 0 1)]
    exact hcommon.symm
  have hnear : co ⁻¹' g.neighborhood ∩ dout ⁻¹' g.neighborhood ∈ 𝓝 (0:ℝ) := by
    apply Filter.inter_mem
    · apply hco.continuousAt.preimage_mem_nhds
      rw [hco0]
      exact (P202.SurfaceRegionConstruction.GraphStar.isOpen_neighborhood g).mem_nhds
        (P202.SurfaceRegionConstruction.GraphStar.mem_neighborhood g)
    · apply hdo.continuousAt.preimage_mem_nhds
      rw [hdo0]
      exact (P202.SurfaceRegionConstruction.GraphStar.isOpen_neighborhood g).mem_nhds
        (P202.SurfaceRegionConstruction.GraphStar.mem_neighborhood g)
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := min (min η ε) (min ζ (1/2)) / 2
  have hδ : 0 < δ := half_pos (lt_min (lt_min hη hε) (lt_min hζ (by norm_num)))
  have hδη : δ < η := by
    have ha := min_le_left (min η ε) (min ζ (1/2:ℝ))
    have hb := min_le_left η ε
    dsimp [δ]
    linarith
  have hδε : δ < ε := by
    have ha := min_le_left (min η ε) (min ζ (1/2:ℝ))
    have hb := min_le_right η ε
    dsimp [δ]
    linarith
  have hδζ : δ < ζ := by
    have ha := min_le_right (min η ε) (min ζ (1/2:ℝ))
    have hb := min_le_left ζ (1/2:ℝ)
    dsimp [δ]
    linarith
  have hδhalf : δ < 1/2 := by
    have ha := min_le_right (min η ε) (min ζ (1/2:ℝ))
    have hb := min_le_right ζ (1/2:ℝ)
    dsimp [δ]
    linarith
  have hmem : ∀ t ∈ Icc 0 δ, co t ∈ g.neighborhood ∧ dout t ∈ g.neighborhood := by
    intro t ht
    apply hηball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 hδη
  have hcoparam (t : ℝ) (ht : t ∈ Ioo 0 δ) : 1-t ∈ Ioo (0:ℝ) 1 := by
    constructor <;> linarith [ht.1,ht.2]
  have hdoparam (t : ℝ) (ht : t ∈ Ioo 0 δ) : t ∈ Ioo (0:ℝ) 1 :=
    ⟨ht.1,lt_trans ht.2 (by linarith)⟩
  have hcone : ∀ t ∈ Ioo 0 δ, co t ≠ c 1 := by
    intro t ht heq
    have htI := hcoparam t ht
    have hp : c ⟨1-t,htI.1.le,htI.2.le⟩ = c 1 := by
      simpa only [co,IccExtend_of_mem zero_le_one c ⟨htI.1.le,htI.2.le⟩] using heq
    have hh := congrArg (fun q : unitInterval => (q:ℝ)) (hci hp)
    simp only [Set.Icc.coe_one] at hh
    linarith [ht.1]
  have hdone : ∀ t ∈ Ioo 0 δ, dout t ≠ c 1 := by
    intro t ht heq
    have htI := hdoparam t ht
    have hp : d ⟨t,htI.1.le,htI.2.le⟩ = d 0 := by
      simpa only [dout,IccExtend_of_mem zero_le_one d ⟨htI.1.le,htI.2.le⟩,hcommon] using heq
    have hh := congrArg (fun q : unitInterval => (q:ℝ)) (hdi hp)
    simp only [Set.Icc.coe_zero] at hh
    linarith [ht.1]
  obtain ⟨i,hi⟩ := fixed_ray_of_graphStar_arc g co δ hδ hco.continuousOn
    (fun t ht => (hmem t ht).1) hcone
    (fun t ht => hcG ⟨_,rfl⟩)
  obtain ⟨j,hj⟩ := fixed_ray_of_graphStar_arc g dout δ hδ hdo.continuousOn
    (fun t ht => (hmem t ht).2) hdone
    (fun t ht => hdG ⟨_,rfl⟩)
  let f : ℝ → Plane := fun t => coordinates g.chart (co t)-coordinates g.chart (c 1)
  let h : ℝ → Plane := fun t => coordinates g.chart (dout t)-coordinates g.chart (c 1)
  have hfcont : ContinuousOn f (Icc 0 δ) :=
    ((continuousOn_coordinates g.chart).comp hco.continuousOn
      (fun t ht => (hmem t ht).1.1)).sub continuousOn_const
  have hhcont : ContinuousOn h (Icc 0 δ) :=
    ((continuousOn_coordinates g.chart).comp hdo.continuousOn
      (fun t ht => (hmem t ht).2.1)).sub continuousOn_const
  have hf0 : f 0 = 0 := by simp only [f,hco0,sub_self]
  have hh0 : h 0 = 0 := by simp only [h,hdo0,sub_self]
  have hfne : ∀ t ∈ Ioo 0 δ, f t ≠ 0 := by
    intro t ht heq
    apply hcone t ht
    exact coordinates_injOn g.chart (hmem t ⟨ht.1.le,ht.2.le⟩).1.1 g.mem_source
      (sub_eq_zero.mp heq)
  have hhne : ∀ t ∈ Ioo 0 δ, h t ≠ 0 := by
    intro t ht heq
    apply hdone t ht
    exact coordinates_injOn g.chart (hmem t ⟨ht.1.le,ht.2.le⟩).2.1 g.mem_source
      (sub_eq_zero.mp heq)
  have hij : i ≠ j := by
    intro heq
    subst j
    obtain ⟨s,hs,t,ht,hst⟩ := same_ray_arcs_intersect f h (g.direction i) δ hδ
      hfcont hhcont hf0 hh0
      (hfne (δ/2) (by constructor <;> linarith))
      (hhne (δ/2) (by constructor <;> linarith)) hi hj
    have hcoord : coordinates g.chart (co s) = coordinates g.chart (dout t) :=
      sub_left_inj.mp hst
    have hsame : co s = dout t := coordinates_injOn g.chart
      (hmem s ⟨hs.1.le,hs.2.le⟩).1.1 (hmem t ⟨ht.1.le,ht.2.le⟩).2.1 hcoord
    have hsI := hcoparam s hs
    have htI := hdoparam t ht
    have hcval : c ⟨1-s,hsI.1.le,hsI.2.le⟩ = co s :=
      (IccExtend_of_mem zero_le_one c ⟨hsI.1.le,hsI.2.le⟩).symm
    have hdval : d ⟨t,htI.1.le,htI.2.le⟩ = dout t :=
      (IccExtend_of_mem zero_le_one d ⟨htI.1.le,htI.2.le⟩).symm
    exact Set.disjoint_left.mp hdis ⟨_,hsI,hcval⟩ ⟨_,htI,hdval.trans hsame.symm⟩
  have hltail : ∀ t ∈ Ioo 0 δ, l (1-t)-l 1 = f t := by
    intro t ht
    have htI := hcoparam t ht
    have hlt : l (1-t) = coordinates g.chart (co t) := by
      dsimp [co]
      rw [IccExtend_of_mem zero_le_one c ⟨htI.1.le,htI.2.le⟩]
      exact (hlrep ⟨1-t,htI.1.le,htI.2.le⟩ (by
        simp only [Set.Icc.coe_one]
        rw [show 1-t-1 = -t by ring,abs_neg,abs_of_pos ht.1]
        exact lt_trans ht.2 hδε)).2
    dsimp [f]
    rw [hlt,hl1]
  have hrtail : ∀ t ∈ Ioo 0 δ, r t-r 0 = h t := by
    intro t ht
    have htI := hdoparam t ht
    have hrt : r t = coordinates g.chart (dout t) := by
      dsimp [dout]
      rw [IccExtend_of_mem zero_le_one d ⟨htI.1.le,htI.2.le⟩]
      exact (hrrep ⟨t,htI.1.le,htI.2.le⟩ (by
        simp only [Set.Icc.coe_zero,sub_zero]
        rw [abs_of_pos ht.1]
        exact lt_trans ht.2 hδζ)).2
    dsimp [h]
    rw [hrt,hr0]
  have hldiff : DifferentiableAt ℝ l 1 :=
    (hl.contDiffAt (isOpen_Ioo.mem_nhds (by
      simp only [Set.Icc.coe_one]; constructor <;> linarith))).differentiableAt (by simp)
  have hrdiff : DifferentiableAt ℝ r 0 :=
    (hr.contDiffAt (isOpen_Ioo.mem_nhds (by
      simp only [Set.Icc.coe_zero]; constructor <;> linarith))).differentiableAt (by simp)
  have hlder : HasDerivAt (fun t => l (1-t)) (-deriv l 1) 0 := by
    have hlu : HasDerivAt l (deriv l 1) (1-id (0:ℝ)) := by simpa using hldiff.hasDerivAt
    simpa only [id_eq,sub_zero,neg_smul,one_smul,Function.comp_def] using
      (hlu.scomp 0 ((hasDerivAt_id (0:ℝ)).const_sub 1))
  obtain ⟨a,ha,hav⟩ := derivative_points_along_ray (fun t => l (1-t)) (-deriv l 1)
    (g.direction i) hlder (neg_ne_zero.mpr hnl) (g.direction_unit i) δ hδ
    (fun t ht => by simpa only [sub_zero,hltail t ht] using hfne t ht)
    (fun t ht => by simpa only [sub_zero,hltail t ht] using hi t ht)
  obtain ⟨b,hb,hbv⟩ := derivative_points_along_ray r (deriv r 0)
    (g.direction j) hrdiff.hasDerivAt hnr (g.direction_unit j) δ hδ
    (fun t ht => by simpa only [hrtail t ht] using hhne t ht)
    (fun t ht => by simpa only [hrtail t ht] using hj t ht)
  have hnoncusp : NormedSpace.normalize (deriv l 1) ≠ -NormedSpace.normalize (deriv r 0) := by
    intro heq
    have hu : NormedSpace.normalize (-(a • g.direction i)) +
        NormedSpace.normalize (b • g.direction j) = 0 := by
      rw [← hav,neg_neg,← hbv,heq,neg_add_cancel]
    exact distinct_rays_noncuspidal g.direction g.direction_injective g.direction_unit hij ha hb hu
  refine ⟨δ,l,r,hδ,hl.mono ?_,hr.mono ?_,?_,?_,hnl,hnr,hnoncusp⟩
  · intro t ht; simp only [Set.Icc.coe_one]; constructor <;> linarith [ht.1,ht.2]
  · intro t ht; simp only [Set.Icc.coe_zero,zero_sub,zero_add]; constructor <;> linarith [ht.1,ht.2]
  · intro t ht
    change l t = coordinates g.chart (IccExtend zero_le_one c t)
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht.1],ht.2⟩
    rw [IccExtend_of_mem zero_le_one c htI]
    exact (hlrep ⟨t,htI⟩ (by
      simp only [Set.Icc.coe_one]
      rw [abs_of_nonpos (by linarith [ht.2] : t-1≤0)]
      linarith [ht.1])).2
  · intro t ht
    change r t = coordinates g.chart (IccExtend zero_le_one d t)
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
    rw [IccExtend_of_mem zero_le_one d htI]
    exact (hrrep ⟨t,htI⟩ (by
      simp only [Set.Icc.coe_zero,sub_zero]
      rw [abs_of_nonneg ht.1]
      linarith [ht.2])).2


/-- The actual graph-arc join is regular in every permitted original smooth
chart containing its common endpoint. -/
theorem regularEndpointJoin_of_disjoint_graph_arcs_in_chart
    (c d : C(unitInterval, M)) (hcommon : c 1 = d 0)
    (hci : Function.Injective c) (hdi : Function.Injective d)
    (hdis : Disjoint (c '' {t : unitInterval | 0 < (t:ℝ) ∧ (t:ℝ)<1})
      (d '' {t : unitInterval | 0 < (t:ℝ) ∧ (t:ℝ)<1}))
    (hcG : range c ⊆ G.carrier) (hdG : range d ⊆ G.carrier)
    (g : GraphStar G (c 1))
    (hc : RegularEdgeEndpoints S c) (hd : RegularEdgeEndpoints S d)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val) (hce : c 1 ∈ e.source) :
    RegularEndpointJoin
      (fun t => coordinates e (IccExtend zero_le_one c t))
      (fun t => coordinates e (IccExtend zero_le_one d t)) := by
  exact regularEndpointJoin_change_chart c d hcommon g.chart e g.chart_mem he
    g.mem_source hce hc hd
    (regularEndpointJoin_of_disjoint_graph_arcs c d hcommon hci hdi hdis hcG hdG g hc hd)

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles

/-- The weak signed boundary of a nonempty coordinate orthant has exactly
those axis rays satisfying its weak signs. The ray count remains explicit. -/
theorem graphStar_of_signed_boundary {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    {S : SmoothManifold 2 kind X} (G : EmbeddedGraph S) (p : X)
    (e : ModelChart 2 kind X) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (r : ℝ) (hr : 0 < r)
    (hball : ∀ z : ModelSpace 2 kind,
      toPlane z.val ∈ Metric.ball (coordinates e p) r → z ∈ e.target)
    (J : Set (Fin 2)) (hJ : J.Nonempty) (σ : Fin 2 → Bool)
    (hadmit : ∀ q : Fin 2 × Bool, q.1 ∈ J →
      (∀ a ∈ J, if σ a then 0 ≤ AxisRays.direction q a else AxisRays.direction q a ≤ 0) →
      ∀ t : ℝ, 0 < t → t < r →
        toPlane.symm (coordinates e p+t • AxisRays.direction q) ∈ modelSet 2 kind)
    (hgraph : ∀ x ∈ e.source, coordinates e x ∈ Metric.ball (coordinates e p) r →
      (x ∈ G.carrier ↔
        (∀ a ∈ J, if σ a then 0 ≤ (coordinates e x-coordinates e p) a
          else (coordinates e x-coordinates e p) a ≤ 0) ∧
        ∃ a ∈ J, (coordinates e x-coordinates e p) a = 0)) :
    ∃ g : GraphStar G p, g.chart = e ∧ g.radius = r ∧
      g.rayCount = Nat.card {q : Fin 2 × Bool // q.1 ∈ J ∧
        ∀ a ∈ J, if σ a then 0 ≤ AxisRays.direction q a else AxisRays.direction q a ≤ 0} := by
  classical
  let I := {q : Fin 2 × Bool // q.1 ∈ J ∧
    ∀ a ∈ J, if σ a then 0 ≤ AxisRays.direction q a else AxisRays.direction q a ≤ 0}
  let E : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let dir : Fin (Fintype.card I) → Plane := fun i => AxisRays.direction (E i).val
  refine ⟨{
    chart := e
    chart_mem := he
    mem_source := hp
    radius := r
    radius_pos := hr
    ball_in_target := hball
    rayCount := Fintype.card I
    direction := dir
    direction_injective := ?_
    direction_unit := fun _ => AxisRays.direction_norm _
    rays_in_model := ?_
    graph_eq := ?_ },rfl,rfl,(by change Fintype.card I = Nat.card I; exact (Nat.card_eq_fintype_card).symm)⟩
  · intro i j hij
    apply E.injective
    apply Subtype.ext
    exact AxisRays.direction_injective hij
  · intro i t ht htr
    exact hadmit (E i).val (E i).property.1 (E i).property.2 t ht htr
  · intro x hx hxr
    rw [hgraph x hx hxr]
    constructor
    · rintro ⟨hweak,a,ha,hzero⟩
      by_cases hxp : x = p
      · exact Or.inl hxp
      have hne : coordinates e x-coordinates e p ≠ 0 := by
        intro hz
        exact hxp (coordinates_injOn e hx hp (sub_eq_zero.mp hz))
      obtain ⟨q,hqa,t,ht,htnorm,hzt⟩ := AxisRays.decompose hne a hzero
      have htr : t < r := by
        rw [htnorm]
        simpa only [Metric.mem_ball,dist_eq_norm] using hxr
      have hqweak : ∀ b ∈ J, if σ b then 0 ≤ AxisRays.direction q b else AxisRays.direction q b ≤ 0 := by
        intro b hb
        have hwb := hweak b hb
        rw [hzt,PiLp.smul_apply,smul_eq_mul] at hwb
        split_ifs at hwb ⊢
        · exact nonneg_of_mul_nonneg_right hwb ht
        · exact nonpos_of_mul_nonpos_right hwb ht
      let qi : I := ⟨q,hqa ▸ ha,hqweak⟩
      refine Or.inr ⟨E.symm qi,t,ht,htr,?_⟩
      change coordinates e x = coordinates e p+t • AxisRays.direction (E (E.symm qi)).val
      rw [E.apply_symm_apply,← hzt]
      abel
    · rintro (rfl | ⟨i,t,ht,htr,hxi⟩)
      · refine ⟨?_,?_⟩
        · intro a ha
          simp only [sub_self,PiLp.zero_apply]
          split_ifs <;> exact le_rfl
        · obtain ⟨a,ha⟩ := hJ
          exact ⟨a,ha,by simp only [sub_self,PiLp.zero_apply]⟩
      · rw [hxi,add_sub_cancel_left]
        refine ⟨?_,(E i).val.1,(E i).property.1,?_⟩
        · intro a ha
          have hwa := (E i).property.2 a ha
          change (if σ a then 0 ≤ t * AxisRays.direction (E i).val a
            else t * AxisRays.direction (E i).val a ≤ 0)
          split_ifs at hwa ⊢
          · exact mul_nonneg ht.le hwa
          · exact mul_nonpos_of_nonneg_of_nonpos ht.le hwa
        · change (t • AxisRays.direction (E i).val) (E i).val.1 = 0
          have hdir : AxisRays.direction (E i).val (E i).val.1 = 0 := by
            rcases (E i).val with ⟨a,b⟩
            fin_cases a <;> cases b <;>
              norm_num [AxisRays.direction,axisTangent,toPlane]
          rw [PiLp.smul_apply,hdir,smul_zero]

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction
open BoundaryCycles
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M} {D : P202Specs.SmoothSurfaceDouble.SmoothDouble S}
variable {s : Bool}
variable {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
variable {B : CompactSmoothSeam D.manifold}
variable {T : TransverseDiskArrangement D.manifold
  (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B}

theorem graphGeometry_regional_two_ray_stars
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (H : ArrangementGraphGeometryData S D s T)
    (a : ConnectedComponents (H.graph.carrierᶜ : Set M))
    (K : EmbeddedGraph S) (hK : K.carrier = frontier (componentSet H.graph.carrierᶜ a))
    (p : M) (hp : p ∈ K.carrier) (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ g : GraphStar K p, g.neighborhood ⊆ O ∧ g.rayCount = 2 := by
  obtain ⟨e,J,σ,r,he,hep,heO,hr,hball,hJ,hformula,hadmit⟩ :=
    restricted_arrangement_frontier_local_chamber S D s hB T H.graph.carrier H.carrier_eq
      a (H.open_components a) (hK ▸ hp) O hO hpO
  obtain ⟨g,hchart,hrad,hcount⟩ := graphStar_of_signed_boundary K p e he hep r hr hball J hJ σ
    (fun q _ hweak => hadmit q hweak) (by
      intro x hx hxball
      rw [hK]
      exact hformula x hx hxball)
  refine ⟨g,?_,hcount.trans (chamber_boundary_ray_card J σ hJ)⟩
  intro x hx
  apply heO
  have hxsource : x ∈ g.chart.source := hx.1
  simpa only [hchart] using hxsource

theorem graphGeometry_regional_degree_two
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (H : ArrangementGraphGeometryData S D s T)
    (a : ConnectedComponents (H.graph.carrierᶜ : Set M))
    (K : EmbeddedGraph S) (hK : K.carrier = frontier (componentSet H.graph.carrierᶜ a))
    (v : Fin K.vertexCount) :
    (incidences K.initial K.terminal v).ncard = 2 := by
  obtain ⟨g,_,hcount⟩ := graphGeometry_regional_two_ray_stars hB H a K hK (K.vertex v)
    (Or.inl (mem_range_self v)) univ isOpen_univ (mem_univ _)
  exact (graphStar_incidence_ncard K v g).trans hcount
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {M : Type*} [TopologicalSpace M] {kind : ModelKind}
variable {S : SmoothManifold 2 kind M}

/-- When every original vertex is incident to an edge, the full graph
carrier is exactly the union of its compact edge traces. -/
theorem carrier_eq_edges_of_nonisolated (G : EmbeddedGraph S)
    (hnon : ∀ v, (incidences G.initial G.terminal v).Nonempty) :
    G.carrier = ⋃ i, range (G.edge i) := by
  apply union_eq_right.mpr
  rintro x ⟨v,rfl⟩
  obtain ⟨⟨i,b⟩,hi⟩ := hnon v
  apply mem_iUnion.mpr
  refine ⟨i,?_⟩
  cases b
  · change G.initial i = v at hi
    exact ⟨0,(G.at_zero i).trans (congrArg G.vertex hi)⟩
  · change G.terminal i = v at hi
    exact ⟨1,(G.at_one i).trans (congrArg G.vertex hi)⟩

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M}

/-- Every join of consecutive subdivision pieces of a simple cyclic chain,
including the closing join, has genuine regular noncuspidal coordinate germs. -/
theorem subdivisionCycle_regularEndpointJoin (G : EmbeddedGraph S)
    (hends : ∀ i, RegularEdgeEndpoints S (G.edge i))
    (hstars : ∀ p ∈ G.carrier, Nonempty (GraphStar G p))
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal))
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hsource : G.carrier ⊆ e.source) (i : Fin c.length) :
    RegularEndpointJoin
      (fun t => coordinates e ((subdivisionPath G (c.adjacent i)).extend t))
      (fun t => coordinates e ((subdivisionPath G (c.adjacent (c.next i))).extend t)) := by
  let p := subdivisionPath G (c.adjacent i)
  let q := subdivisionPath G (c.adjacent (c.next i))
  have hcommon : p 1 = q 0 := by
    simpa only [p,q,Path.target,Path.source] using congrArg (subdivisionVertex G) (c.vertex_succ i)
  have hpG : range p ⊆ G.carrier := fun x hx =>
    Or.inr (subdivisionPath_range_subset_edges G (c.adjacent i) hx)
  have hqG : range q ⊆ G.carrier := fun x hx =>
    Or.inr (subdivisionPath_range_subset_edges G (c.adjacent (c.next i)) hx)
  have hdis : Disjoint (p '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1})
      (q '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) := by
    apply (realizedCyclePath_piece_disjoint G c (c.next_ne_self i).symm).mono
    · rintro x ⟨t,ht,rfl⟩
      exact ⟨t,ht.2,rfl⟩
    · rintro x ⟨t,ht,rfl⟩
      exact ⟨t,ht.2,rfl⟩
  have hreg (j : Fin G.edgeCount) : RegularCoordinateGerms S (G.edge j) :=
    regularCoordinateGerms_of_regular_edges (G.regular j) (hends j)
  have hpends : RegularEdgeEndpoints S p.toContinuousMap :=
    (subdivisionPath_regularCoordinateGerms G hreg (c.adjacent i)).regular.2
  have hqends : RegularEdgeEndpoints S q.toContinuousMap :=
    (subdivisionPath_regularCoordinateGerms G hreg (c.adjacent (c.next i))).regular.2
  obtain ⟨g⟩ := hstars (p 1) (hpG ⟨1,rfl⟩)
  exact regularEndpointJoin_of_disjoint_graph_arcs_in_chart p.toContinuousMap q.toContinuousMap
    hcommon (subdivisionPath_injective G (c.adjacent i))
    (subdivisionPath_injective G (c.adjacent (c.next i))) hdis hpG hqG g hpends hqends e he
    (hsource (hpG ⟨1,rfl⟩))

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction
open BoundaryCycles

theorem regionalBoundaryCycles_of_realization
    (hrealization : ∀ {kind : ModelKind} {X : Type u} [TopologicalSpace X]
      {S : SmoothManifold 2 kind X} (G : EmbeddedGraph S),
      0 < G.edgeCount → (∀ i, RegularEdgeEndpoints S (G.edge i)) →
      (∀ v, (incidences G.initial G.terminal v).Nonempty →
        (incidences G.initial G.terminal v).ncard = 2) →
      (∀ p ∈ G.carrier, Nonempty (GraphStar G p)) →
      ∀ e : ModelChart 2 kind X, e ∈ S.smoothStructure.val → G.carrier ⊆ e.source →
      ∃ (n : ℕ) (curve : Fin n → RegularJordanCurve), 1 ≤ n ∧
        Pairwise (fun i j => Disjoint (curve i).trace (curve j).trace) ∧
        (⋃ i, (curve i).trace) = coordinates e '' (⋃ j, range (G.edge j))) :
    Expected.regionalBoundaryCycles.{u} := by
  intro kind M _ _ S D s A _hA _hsubordinate B hB T H a e he hsource
  obtain ⟨K,_hvertices,hK,_hforward,_hreverse,hends,_hcurves,hpos,hnon⟩ :=
    graphGeometry_regional_embeddedGraph hB H a
  have hstars : ∀ p ∈ K.carrier, Nonempty (GraphStar K p) := by
    intro p hp
    obtain ⟨g,_,_⟩ := graphGeometry_regional_two_ray_stars hB H a K hK p hp
      univ isOpen_univ (mem_univ _)
    exact ⟨g⟩
  have hKsource : K.carrier ⊆ e.source := by
    rw [hK]
    exact frontier_subset_closure.trans hsource
  obtain ⟨n,curve,hn,hdisjoint,hcover⟩ := hrealization K (by omega) hends
    (fun v _ => graphGeometry_regional_degree_two hB H a K hK v) hstars e he hKsource
  obtain ⟨_,_,_,_,hfront,_⟩ := graphGeometry_component_coordinates H a e he hsource
  refine ⟨⟨n,hn,curve,hdisjoint,?_⟩⟩
  calc
    frontier (coordinates e '' componentSet H.graph.carrierᶜ a) =
        coordinates e '' frontier (componentSet H.graph.carrierᶜ a) := hfront
    _ = coordinates e '' K.carrier := by rw [hK]
    _ = coordinates e '' (⋃ j, range (K.edge j)) := by
      rw [carrier_eq_edges_of_nonisolated K hnon]
    _ = ⋃ i, (curve i).trace := hcover.symm

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.BoundaryCycles
variable {kind : ModelKind} {M : Type*} [TopologicalSpace M]
variable {S : SmoothManifold 2 kind M}

/-- Every subdivision piece stays in the actual ambient graph carrier. -/
theorem subdivisionPath_range_subset_carrier (G : EmbeddedGraph S)
    {x y : Fin G.vertexCount ⊕ (Fin G.edgeCount × Bool)}
    (h : (doubleSubdivision G.initial G.terminal).Adj x y) :
    range (subdivisionPath G h) ⊆ G.carrier := by
  intro z hz
  exact Or.inr (subdivisionPath_range_subset_edges G h hz)

/-- The actual coordinate path associated with one cyclic subdivision piece. -/
def coordinateSubdivisionPath (G : EmbeddedGraph S)
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal))
    (e : ModelChart 2 kind M) (hsource : G.carrier ⊆ e.source) (i : Fin c.length) :
    Path (coordinates e (subdivisionVertex G (c.vertex i.castSucc)))
      (coordinates e (subdivisionVertex G (c.vertex i.succ))) :=
  coordinatePath (subdivisionPath G (c.adjacent i)) e
    ((subdivisionPath_range_subset_carrier G _).trans hsource)

/-- The generic regular Jordan assembly also applies to arbitrary positive
numbers of pieces, with successor and final indices expressed by values. -/
theorem regularJordanCurveOfPositiveConcatenation
    (n : ℕ) (hn : 0 < n) (p : Fin (n+1) → Plane)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hclosed : p 0 = p (Fin.last n))
    (hinj : InjOn (concatenateNonempty n hn p F) {t : unitInterval | (t:ℝ)<1})
    (hsm : ∀ i, ∃ J : Finset ℝ, ∀ t ∈ Ioo (0:ℝ) 1,
      t ∉ J → ContDiffAt ℝ ∞ (F i).extend t)
    (hreg : ∀ i t, t ∈ Ioo (0:ℝ) 1 → RegularJoinAt (F i).extend t)
    (hjoin : ∀ i j : Fin n, i.val+1=j.val →
      RegularEndpointJoin (F i).extend (F j).extend)
    (hclosing : ∀ i : Fin n, i.val+1=n →
      RegularEndpointJoin (F i).extend (F ⟨0,hn⟩).extend) :
    ∃ c : RegularJordanCurve, c.trace = ⋃ i, range (F i) := by
  cases n with
  | zero => omega
  | succ n =>
    apply regularJordanCurveOfNonemptyConcatenation n p F hclosed hinj hsm hreg
    · exact fun i => hjoin i.castSucc i.succ rfl
    · exact hclosing (Fin.last n) rfl

/-- Actual regular coordinate pieces with their established cyclic endpoint
joins define a regular Jordan curve with the exact coordinate trace. -/
theorem regularCycle_in_chart_of_endpoint_joins (G : EmbeddedGraph S)
    (hends : ∀ i, RegularEdgeEndpoints S (G.edge i))
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal))
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hsource : G.carrier ⊆ e.source)
    (hjoinNext : ∀ i : Fin c.length,
      RegularEndpointJoin (coordinateSubdivisionPath G c e hsource i).extend
        (coordinateSubdivisionPath G c e hsource (c.next i)).extend) :
    ∃ f : RegularJordanCurve, f.trace = coordinates e '' range (realizedCyclePath G c) := by
  let p : Fin (c.length+1) → Plane := coordinates e ∘ subdivisionVertex G ∘ c.vertex
  let F := coordinateSubdivisionPath G c e hsource
  have hFreg (i : Fin c.length) := coordinatePath_interior_regular
    (subdivisionPath G (c.adjacent i)) e
    ((subdivisionPath_range_subset_carrier G _).trans hsource) he
    (subdivisionPath_regularCoordinateGerms G
      (fun j => P202.SurfaceRegionConstruction.regularCoordinateGerms_of_regular_edges
        (G.regular j) (hends j)) (c.adjacent i))
  have hinjF (i : Fin c.length) : Function.Injective (F i) := by
    intro t u htu
    apply subdivisionPath_injective G (c.adjacent i)
    exact coordinates_injOn e
      (hsource (subdivisionPath_range_subset_carrier G _ ⟨t,rfl⟩))
      (hsource (subdivisionPath_range_subset_carrier G _ ⟨u,rfl⟩)) htu
  have hdisF : Pairwise (fun i j => Disjoint (halfOpenRange (F i)) (halfOpenRange (F j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨t,ht,htz⟩ ⟨u,hu,huz⟩
    have htu : subdivisionPath G (c.adjacent i) t = subdivisionPath G (c.adjacent j) u :=
      coordinates_injOn e
        (hsource (subdivisionPath_range_subset_carrier G _ ⟨t,rfl⟩))
        (hsource (subdivisionPath_range_subset_carrier G _ ⟨u,rfl⟩)) (htz.trans huz.symm)
    exact Set.disjoint_left.mp (realizedCyclePath_piece_disjoint G c hij)
      ⟨t,ht,rfl⟩ ⟨u,hu,htu.symm⟩
  have hclosed : p 0 = p (Fin.last c.length) := by
    exact congrArg (coordinates e ∘ subdivisionVertex G) c.closed
  obtain ⟨f,hf⟩ := regularJordanCurveOfPositiveConcatenation c.length c.length_pos p F hclosed
    (concatenateNonempty_halfOpen_injective _ _ _ _ (fun i => (hinjF i).injOn) hdisF)
    (fun i => ⟨∅,fun t ht _ => (hFreg i).1.contDiffAt (isOpen_Ioo.mem_nhds ht)⟩)
    (fun i t ht => (hFreg i).2.2 t ht) (by
      intro i j hij
      have hnext : c.next i = j := by
        simp only [SimpleCyclicChain.next,dite_eq_left (by omega : i.val+1<c.length)]
        exact Fin.ext hij
      exact (congrArg (fun k => RegularEndpointJoin (F i).extend (F k).extend) hnext).mp
        (hjoinNext i)) (by
      intro i hilast
      have hnext : c.next i = ⟨0,c.length_pos⟩ := by
        simp only [SimpleCyclicChain.next,dite_eq_right (by omega : ¬i.val+1<c.length)]
      exact (congrArg (fun k => RegularEndpointJoin (F i).extend (F k).extend) hnext).mp
        (hjoinNext i))
  refine ⟨f,hf.trans ?_⟩
  rw [realizedCyclePath_range,Set.image_iUnion]
  apply iUnion_congr
  intro i
  change range (coordinatePath _ e _) = _
  exact Set.range_comp (coordinates e) (subdivisionPath G (c.adjacent i))

/-- The geometric cycle has a genuine regular Jordan parametrization in any
original chart containing the entire graph. -/
theorem regularCycle_in_chart (G : EmbeddedGraph S)
    (hends : ∀ i, RegularEdgeEndpoints S (G.edge i))
    (hstars : ∀ p ∈ G.carrier, Nonempty (GraphStar G p))
    (c : SimpleCyclicChain (doubleSubdivision G.initial G.terminal))
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hsource : G.carrier ⊆ e.source) :
    ∃ f : RegularJordanCurve, f.trace = coordinates e '' range (realizedCyclePath G c) := by
  apply regularCycle_in_chart_of_endpoint_joins G hends c e he hsource
  intro i
  simpa only [coordinateSubdivisionPath,coordinatePath_extend] using
    subdivisionCycle_regularEndpointJoin G hends hstars c e he hsource i

/-- The finite nonempty degree-two embedded graph is an actual finite disjoint
family of shared regular Jordan curves in every permitted coordinate chart. -/
theorem finite_regular_cycle_family (G : EmbeddedGraph S) (hne : 0 < G.edgeCount)
    (hends : ∀ i, RegularEdgeEndpoints S (G.edge i))
    (hdegree : ∀ p, (incidences G.initial G.terminal p).Nonempty →
      (incidences G.initial G.terminal p).ncard = 2)
    (hstars : ∀ p ∈ G.carrier, Nonempty (GraphStar G p))
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hsource : G.carrier ⊆ e.source) :
    ∃ (n : ℕ) (f : Fin n → RegularJordanCurve), 1 ≤ n ∧
      Pairwise (fun i j => Disjoint (f i).trace (f j).trace) ∧
      (⋃ i, (f i).trace) = coordinates e '' (⋃ j, range (G.edge j)) := by
  classical
  let H := doubleSubdivision G.initial G.terminal
  let C := NonisolatedComponent H
  let : Finite C := finite_nonisolatedComponents H
  let : Fintype C := Fintype.ofFinite C
  let : Nonempty (Fin G.edgeCount) := ⟨⟨0,hne⟩⟩
  let : Nonempty C := doubleSubdivision_nonempty_cycles G.initial G.terminal
  let h := doubleSubdivision_isCycles G.initial G.terminal hdegree
  let enum : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  have hfexist (c : C) : ∃ f : RegularJordanCurve,
      f.trace = coordinates e '' range (realizedCyclePath G (componentCycle h c).chain) :=
    regularCycle_in_chart G hends hstars (componentCycle h c).chain e he hsource
  choose f hf using hfexist
  have hrange (c : C) : range (realizedCyclePath G (componentCycle h c).chain) ⊆ G.carrier := by
    rw [realizedCyclePath_range]
    exact iUnion_subset (fun i => subdivisionPath_range_subset_carrier G _)
  refine ⟨Fintype.card C,f ∘ enum,Fintype.card_pos,?_,?_⟩
  · intro i j hij
    change Disjoint (f (enum i)).trace (f (enum j)).trace
    rw [hf,hf]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy : x = y := coordinates_injOn e (hsource (hrange _ hx))
      (hsource (hrange _ hy)) (hxz.trans hyz.symm)
    exact Set.disjoint_left.mp
      (componentCycle_realizations_disjoint G hdegree
        (fun heq => hij (enum.injective heq))) hx (hxy ▸ hy)
  · change (⋃ i, (f (enum i)).trace) = _
    rw [enum.surjective.iUnion_comp (fun c => (f c).trace)]
    simp_rw [hf]
    rw [← Set.image_iUnion,componentCycle_realizations_cover_edges G hdegree]

end P202.SurfaceRegionConstruction.BoundaryCycles

namespace P202.SurfaceRegionConstruction

/-- The actual complementary component in every containing original chart
has a positive finite disjoint regular Jordan boundary, including seam points. -/
theorem regionalBoundaryCycles : Expected.regionalBoundaryCycles.{u} := by
  apply regionalBoundaryCycles_of_realization
  intro kind X _ S G hne hends hdegree hstars e he hsource
  exact BoundaryCycles.finite_regular_cycle_family G hne hends hdegree hstars e he hsource

end P202.SurfaceRegionConstruction
