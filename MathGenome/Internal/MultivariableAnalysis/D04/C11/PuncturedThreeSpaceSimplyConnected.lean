import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.PuncturedThreeSpaceSimplyConnected
import MathGenome.Internal.MultivariableAnalysis.D04.C11.SimplyConnectedOneFormPotential
import MathGenome.Internal.MultivariableAnalysis.D04.C15.RadialFluxObstruction
import Mathlib.Topology.Subpath
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
open Set
open scoped unitInterval
namespace D04.PuncturedThree
open D04
open Specs.D04.C11.PuncturedThreeSpaceSimplyConnected
open Specs.D04.C15.RadialFluxObstruction.Model

theorem punctured_open : punctured_openType := RadialFluxObstruction.puncturedSpace_open

theorem punctured_pathConnected : punctured_pathConnectedType := by
  have h : IsPathConnected puncturedSpace :=
    isPathConnected_compl_singleton_of_one_lt_rank (by
      rw [← Module.finrank_eq_rank]; norm_num [E]) 0
  exact fun a b => h.joinedIn a a.property b b.property |>.joined_subtype

theorem punctured_connected : punctured_connectedType := by
  exact (isConnected_compl_singleton_of_one_lt_rank (by
    rw [← Module.finrank_eq_rank]; norm_num [E]) (0 : E 3)).isPreconnected


/-- Affine interpolation, with the homotopy parameter first. -/
def blend (s : I) (x y : E 3) : E 3 := (1 - (s : ℝ)) • x + (s : ℝ) • y

@[simp] lemma blend_zero (x y : E 3) : blend 0 x y = x := by simp [blend]
@[simp] lemma blend_one (x y : E 3) : blend 1 x y = y := by simp [blend]
@[simp] lemma blend_self (s : I) (x : E 3) : blend s x x = x := by
  simp [blend, ← add_smul]

lemma blend_mem {V : Set (E 3)} (hV : Convex ℝ V) {x y : E 3}
    (hx : x ∈ V) (hy : y ∈ V) (s : I) : blend s x y ∈ V :=
  hV hx hy (sub_nonneg.mpr s.property.2) s.property.1 (sub_add_cancel _ _)

/-- A chord in the punctured domain, supplied with its genuine avoidance proof. -/
def chord (x y : puncturedSpace)
    (h : ∀ s : I, blend s x y ≠ 0) : Path x y where
  toFun s := ⟨blend s x y, h s⟩
  continuous_toFun := by unfold blend; fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

/-- Straight homotopies of arbitrary continuous maps into the punctured space. -/
def straightHomotopy (f g : C(I, puncturedSpace))
    (h : ∀ s t : I, blend s (f t) (g t) ≠ 0) : f.Homotopy g where
  toFun st := ⟨blend st.1 (f st.2) (g st.2), h _ _⟩
  continuous_toFun := by unfold blend; fun_prop
  map_zero_left t := by apply Subtype.ext; simp
  map_one_left t := by apply Subtype.ext; simp

lemma chord_homotopic {x y : puncturedSpace} (γ : Path x y)
    (V : Set (E 3)) (hV : Convex ℝ V) (hVU : V ⊆ puncturedSpace)
    (hγ : ∀ t, (γ t : E 3) ∈ V)
    (hchord : ∀ s : I, blend s x y ≠ 0) :
    γ.Homotopic (chord x y hchord) := by
  have hx : (x : E 3) ∈ V := by simpa using hγ 0
  have hy : (y : E 3) ∈ V := by simpa using hγ 1
  refine ⟨{ straightHomotopy γ.toContinuousMap (chord x y hchord).toContinuousMap
    (fun s t => hVU (blend_mem hV (hγ t) (blend_mem hV hx hy t) s)) with
      prop' := ?_ }⟩
  intro s t ht
  rcases ht with rfl | rfl <;> apply Subtype.ext <;>
    simp [straightHomotopy, chord]

/-- A finite concatenation preserves any predicate true on all its pieces. -/
lemma concat_property {X : Type*} [TopologicalSpace X] (Q : X → Prop)
    {N : ℕ} (v : Fin (N+1) → X)
    (e : (i : Fin N) → Path (v i.castSucc) (v i.succ))
    (h0 : Q (v 0)) (he : ∀ i t, Q (e i t)) :
    ∀ t, Q (Path.concat v e t) := by
  induction N with
  | zero => simpa using fun _ : I => h0
  | succ N ih =>
    rw [Path.concat_succ]
    intro t
    rcases (Path.trans_range (Path.concat (v ∘ Fin.castSucc) (fun i => e i.castSucc))
      (e (Fin.last N))).subset ⟨t, rfl⟩ with h | h
    · obtain ⟨s, hs⟩ := h
      exact hs ▸ ih _ _ h0 (fun i => he i.castSucc) s
    · obtain ⟨s, hs⟩ := h
      exact hs ▸ he _ _

/-- The span of two vectors is a proper subspace of three-space. -/
lemma span_pair_ne_top (x y : E 3) : Submodule.span ℝ ({x,y} : Set (E 3)) ≠ ⊤ := by
  apply ne_of_lt
  apply span_lt_top_of_ncard_lt_finrank (Set.toFinite _)
  have h : ({x,y} : Set (E 3)).ncard ≤ 2 := by simpa using (Set.ncard_insert_le x ({y} : Set (E 3)))
  have hd : Module.finrank ℝ (E 3) = 3 := by simp [E]
  omega

/-- If a point is outside a linear subspace, a chord from a nonzero point
of that subspace to the point cannot pass through zero. -/
lemma blend_ne_zero_of_not_mem (S : Submodule ℝ (E 3)) {p x : E 3}
    (hp : p ∉ S) (hx : x ∈ S) (hx0 : x ≠ 0) (s : I) : blend s x p ≠ 0 := by
  intro hz
  by_cases hs : (s : ℝ) = 0
  · have : s = 0 := Subtype.ext hs
    exact hx0 (by simpa [this] using hz)
  · have hsm : (s : ℝ) • p ∈ S := by
      have hh : (s : ℝ) • p = -((1 - (s : ℝ)) • x) :=
        eq_neg_of_add_eq_zero_right hz
      rw [hh]
      exact S.neg_mem (S.smul_mem _ hx)
    exact hp ((S.smul_mem_iff hs).mp hsm)

lemma ball_avoids_zero (x : puncturedSpace) :
    Metric.ball (x : E 3) ‖(x : E 3)‖ ⊆ puncturedSpace := by
  intro y hy hz
  subst y
  simp [Metric.mem_ball, dist_eq_norm] at hy

/-- Every continuous loop is freely nullhomotopic. The finite subdivision
is chosen from a cover by convex balls in the punctured domain; no
piecewise differentiability of the loop is assumed. -/
theorem punctured_free_contractions : punctured_free_contractionsType := by
  classical
  intro a γ
  let c (x : puncturedSpace) : Set I :=
    {t | (γ t : E 3) ∈ Metric.ball (x : E 3) ‖(x : E 3)‖}
  have hc (x : puncturedSpace) : IsOpen (c x) :=
    Metric.isOpen_ball.preimage (continuous_subtype_val.comp γ.continuous)
  have hcover : univ ⊆ ⋃ x, c x := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t, by
      change dist (γ t : E 3) (γ t) < ‖(γ t : E 3)‖
      simpa using norm_pos_iff.mpr (γ t).property⟩
  obtain ⟨r, hr0, hrmono, ⟨N, hrN⟩, hcell⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc hcover
  have hrLast : r N = 1 := hrN N le_rfl
  choose center hcenter using hcell
  have hsub (k : ℕ) (s : I) :
      (γ.subpath (r k) (r (k+1)) s : E 3) ∈
        Metric.ball (center k : E 3) ‖(center k : E 3)‖ := by
    have hm : γ.subpath (r k) (r (k+1)) s ∈
        Set.range (γ.subpath (r k) (r (k+1))) := ⟨s, rfl⟩
    rw [Path.range_subpath_of_le _ _ _ (hrmono (Nat.le_succ k))] at hm
    obtain ⟨u, hu, he⟩ := hm
    exact he ▸ hcenter k hu
  have hchord (k : ℕ) (s : I) :
      blend s (γ (r k)) (γ (r (k+1))) ≠ 0 := by
    have hleft := hsub k 0
    have hright := hsub k 1
    simp only [Path.source, Path.target] at hleft hright
    exact ball_avoids_zero (center k)
      (blend_mem (convex_ball _ _) hleft hright s)
  let v (i : Fin (N+1)) : puncturedSpace := γ (r i)
  let e (i : Fin N) : Path (v i.castSucc) (v i.succ) :=
    chord _ _ (hchord i)
  have hedge (i : Fin N) :
      (γ.subpath (r i.castSucc) (r i.succ)).Homotopic (e i) :=
    chord_homotopic _ _ (convex_ball _ _) (ball_avoids_zero (center i))
      (hsub i) (hchord i)
  let q := Path.concat v e
  have K : (γ.subpath (r 0) (r N)).Homotopic q :=
    (Path.Homotopic.concat_subpath γ (fun i : Fin (N+1) => r i)).symm.trans
      (Path.Homotopic.concat_hcomp v _ e hedge)
  have ha : a = v 0 := by simp [v, hr0]
  have hb : a = v (Fin.last N) := by simp [v, hrLast]
  let qloop : Path a a := q.cast ha hb
  have hγ : (γ.subpath (r 0) (r N)).cast ha hb = γ := by
    apply Path.ext
    funext t
    change γ (Icc.convexComb (r 0) (r N) t) = γ t
    rw [hr0, hrLast]
    congr 1
    apply Subtype.ext
    simp
  have Kloop : γ.Homotopic qloop :=
    ⟨(K.some.pathCast ha hb).cast hγ rfl⟩
  -- Every chord lies in the span of its two endpoints, of dimension at most two.
  let S (i : Fin (N+1)) : Submodule ℝ (E 3) :=
    Submodule.span ℝ ({(γ (r i) : E 3), (γ (r (i+1)) : E 3)} : Set (E 3))
  obtain ⟨p, hp⟩ := Submodule.exists_forall_notMem_of_forall_ne_top S
    (fun i => span_pair_ne_top _ _)
  have hp0 : p ≠ 0 := by
    intro hz
    exact hp 0 (hz ▸ (S 0).zero_mem)
  let b : puncturedSpace := ⟨p, hp0⟩
  have hq : ∀ t, ∃ i, (q t : E 3) ∈ S i := by
    apply concat_property (fun x : puncturedSpace => ∃ i, (x : E 3) ∈ S i) v e
    · exact ⟨0, Submodule.subset_span (by simp [v])⟩
    · intro i t
      refine ⟨i.castSucc, ?_⟩
      exact (S i.castSucc).add_mem
        ((S i.castSucc).smul_mem _ (Submodule.subset_span (by simp [v])))
        ((S i.castSucc).smul_mem _ (Submodule.subset_span (by simp [v])))
  have havoid (s t : I) : blend s (qloop t) b ≠ 0 := by
    obtain ⟨i, hi⟩ := hq t
    exact blend_ne_zero_of_not_mem (S i) (hp i) hi (qloop t).property s
  let H := straightHomotopy qloop.toContinuousMap (ContinuousMap.const I b) havoid
  have hH : ∀ s : I, H (s,0) = H (s,1) := by
    intro s
    apply Subtype.ext
    change blend s (qloop 0) b = blend s (qloop 1) b
    rw [qloop.source, qloop.target]
  let L := Kloop.some.toHomotopy.trans H
  refine ⟨b, L, ?_⟩
  intro s
  simp only [L, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (Kloop.some.source _).trans (Kloop.some.target _).symm
  · exact hH _

/-- The loop definition used by the one-form theorem agrees with based contraction. -/
theorem punctured_contraction_conventions : punctured_contraction_conventionsType :=
  D04.C11.free_iff_based puncturedSpace

theorem punctured_simplyConnected : punctured_simplyConnectedType :=
  punctured_contraction_conventions.mpr
    ⟨punctured_pathConnected, punctured_free_contractions⟩

theorem punctured_oneform_potential : punctured_oneform_potentialType := by
  intro F hF hsym
  exact D04.C11.simply_connected_potential puncturedSpace F punctured_open
    punctured_connected punctured_free_contractions hF hsym

/-- On this simply connected domain the specified smooth radial two-form
is closed, yet has no global primitive even of class C¹. -/
theorem radial_counterexample : radial_counterexampleType := by
  refine ⟨punctured_open, punctured_connected, punctured_simplyConnected, ?_,
    RadialFluxObstruction.radialForm_closed, RadialFluxObstruction.no_C1_primitive⟩
  exact ⟨RadialFluxObstruction.radialForm_smooth.1,
    fun idx => RadialFluxObstruction.radialForm_smooth.2 idx 1⟩

end D04.PuncturedThree
