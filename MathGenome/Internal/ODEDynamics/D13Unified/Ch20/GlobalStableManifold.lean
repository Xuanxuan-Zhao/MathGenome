import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.GlobalStableManifold
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.StableManifold
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.CountableImmersedAtlas
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.StableStageCompatibility
import Mathlib.Topology.Homeomorph.TransferInstance

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped ContDiff

namespace D13Unified.Ch20.GlobalStableManifold
open D13Unified.Ch06.StateDerivative
open Specs.D13Unified.Ch11.Flow Specs.D13Unified.Ch20.StableGraphs
open Specs.D13Unified.Ch20.PerronFixedPoints Specs.D13Unified.Ch20.PerronRegularity
open Specs.D13Unified.Ch20.HyperbolicSplitting
open D13Unified.Ch07
universe u v
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Translate convergence along a forward-complete original orbit. -/
lemma stableSet_forward (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    (p : E) {x : E} (hx : x ∈ stableSet F p) {s : ℝ} (hs : 0 ≤ s) :
    flow F s x ∈ stableSet F p := by
  have hdom := hx.2.1 s hs
  have hη := (Ch11.Flow.reverse_flow F hF hdom).1.1
  have htrans := Ch11.Flow.flow_translation F hF x hx.1 s hdom.2
  refine ⟨hη, ?_, ?_⟩
  · intro t ht
    exact ⟨hη, htrans.1.symm ▸ (hx.2.1 (t+s) (add_nonneg ht hs)).2⟩
  · have hh := hx.2.2.comp (tendsto_atTop_add_const_right atTop s tendsto_id)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (htrans.2 t (hx.2.1 (t+s) (add_nonneg ht hs)).2).symm

/-- Retrace a finite, actually existing segment before a stable forward orbit. -/
lemma stableSet_backward (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    (p : E) {y : E} (hy : y ∈ stableSet F p) {s : ℝ} (_hs : 0 ≤ s)
    (hback : (-s,y) ∈ flowDomain F) : flow F (-s) y ∈ stableSet F p := by
  let x := flow F (-s) y
  have hx0 := Ch11.Flow.reverse_flow F hF hback
  have htrans := Ch11.Flow.flow_translation F hF y hy.1 (-s) hback.2
  have hzero := (Ch11.Flow.flow_zero F hF y hy.1).1.2
  have htimes (t : ℝ) (ht : 0 ≤ t) : t + -s ∈ (flowInterval F y).carrier := by
    by_cases hts : t ≤ s
    · exact (flowInterval F y).ordConnected.out hback.2 hzero
        ⟨by linarith, by linarith⟩
    · exact (hy.2.1 (t + -s) (by linarith)).2
  refine ⟨hx0.1.1, ?_, ?_⟩
  · intro t ht
    exact ⟨hx0.1.1, htrans.1.symm ▸ htimes t ht⟩
  · have hh := hy.2.2.comp (tendsto_atTop_add_const_right atTop (-s) tendsto_id)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (htrans.2 t (htimes t ht)).symm

/-- Integer stages cover precisely the original global stable set once
forward invariance and eventual entry of the local portion have been proved. -/
lemma stableSet_eq_stages (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (p : E)
    {S T : Submodule ℝ E} (h : S → T) (V : Set S)
    (hstable : ∀ ξ ∈ V, graphPoint p h ξ ∈ stableSet F p)
    (hcapture : CapturesStableSet F p h V) :
    stableSet F p = ⋃ m : ℕ, backwardStage F p h V m := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨m, ξ, hξ, heq⟩ := hcapture x hx
    apply mem_iUnion.mpr
    refine ⟨m, ξ, ⟨hξ, ?_⟩, ?_⟩
    · change (-(m : ℝ), graphPoint p h ξ) ∈ flowDomain F
      rw [heq]
      exact (Ch11.Flow.reverse_flow F hF (hx.2.1 m (Nat.cast_nonneg _))).1
    · change flow F (-(m : ℝ)) (graphPoint p h ξ) = x
      rw [heq]
      exact (Ch11.Flow.reverse_flow F hF (hx.2.1 m (Nat.cast_nonneg _))).2
  · rintro x hx
    obtain ⟨m, ξ, hξ, rfl⟩ := mem_iUnion.mp hx
    exact stableSet_backward F hF p (hstable ξ hξ.1) (Nat.cast_nonneg _) hξ.2

/-- The stages are nested using only the actual existence intervals. -/
lemma stages_monotone (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (p : E)
    {S T : Submodule ℝ E} (h : S → T) (V : Set S)
    (hstable : ∀ ξ ∈ V, graphPoint p h ξ ∈ stableSet F p)
    (hinv : ∀ ξ ∈ V, ∀ t : ℝ, 0 ≤ t →
      flow F t (graphPoint p h ξ) ∈ graphPoint p h '' V) :
    Monotone (backwardStage F p h V) := by
  intro m n hmn x hx
  obtain ⟨ξ, hξ, rfl⟩ := hx
  let y := graphPoint p h ξ
  let τ : ℝ := (n : ℝ) - (m : ℝ)
  have hτ : 0 ≤ τ := sub_nonneg.mpr (by exact_mod_cast hmn)
  have hy := hstable ξ hξ.1
  have hdom := hy.2.1 τ hτ
  obtain ⟨η, hη, heq⟩ := hinv ξ hξ.1 τ hτ
  have htrans := Ch11.Flow.flow_translation F hF y hy.1 τ hdom.2
  have heqtime : -(n : ℝ) + τ = -(m : ℝ) := by dsimp [τ]; ring
  have htm : -(n : ℝ) + τ ∈ (flowInterval F y).carrier := by
    rw [heqtime]
    exact hξ.2.2
  have hnew : (-(n : ℝ), graphPoint p h η) ∈ flowDomain F := by
    rw [heq]
    refine ⟨(stableSet_forward F hF p hy hτ).1, ?_⟩
    rw [htrans.1]
    exact htm
  refine ⟨η, ⟨hη, hnew⟩, ?_⟩
  change flow F (-(n : ℝ)) (graphPoint p h η) = flow F (-(m : ℝ)) y
  rw [heq, htrans.2 _ htm, heqtime]

lemma stageDomain_open (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (p : E)
    {S T : Submodule ℝ E} {h : S → T} {V : Set S}
    (hg : Continuous (graphMap h)) (hV : IsOpen V) (m : ℕ) :
    IsOpen (stageDomain F p h V m) :=
  hV.inter ((Ch11.Flow.isOpen_timeDomain F hF _).preimage (continuous_const.add hg))

lemma stageMap_injOn (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (p : E)
    {S T : Submodule ℝ E} {h : S → T} {V : Set S}
    (hg : Function.Injective (graphMap h)) (m : ℕ) :
    InjOn (stageMap F p h m) (stageDomain F p h V m) := by
  intro ξ hξ η hη heq
  apply hg
  apply add_left_cancel (a := p)
  have hh := congrArg (flow F (m : ℝ)) heq
  change flow F (m : ℝ) (flow F (-(m : ℝ)) (graphPoint p h ξ)) =
    flow F (m : ℝ) (flow F (-(m : ℝ)) (graphPoint p h η)) at hh
  have hξr := (Ch11.Flow.reverse_flow F hF hξ.2).2
  have hηr := (Ch11.Flow.reverse_flow F hF hη.2).2
  simp only [neg_neg] at hξr hηr
  exact hξr.symm.trans (hh.trans hηr)

/-- The norm of the entire Perron trajectory supplies an invariant open
parameter portion. All survival assertions concern the original field. -/
lemma weighted_local_portion
    {n : Type u} [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain) (p : E)
    (K α β δ : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hβ : 0 < β) (hβα : β < α) (hδ : 0 ≤ δ)
    (r : E → E) (hr : r 0 = 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x-y‖)
    (φ : ℝ → E → E) (hφ : CompleteFlow (fun x => matrixOperatorEquiv b A x + r x) φ)
    (h : stableParameters b A → unstableParameters b A) (k : ℕ∞)
    (hgeom : GraphGeometry k (stableParameters b A) (unstableParameters b A) h)
    (W : stableParameters b A → WeightedPath β E) (hWc : Continuous W)
    (hW : SolutionFamily b A r K α β δ W)
    (hgraph : ∀ ξ, (W ξ).atReal 0 = graphMap h ξ)
    (ρ η : ℝ) (hρ : 0 < ρ) (hη : 0 < η) (hηρ : η ≤ ρ)
    (hloc : ∀ x, ‖x‖ < ρ → p + x ∈ F.domain ∧
      matrixOperatorEquiv b A x + r x = F.eval (p+x)) :
    LocalPortion k F p (stableParameters b A) (unstableParameters b A) h
      {ξ | ‖W ξ‖ < η} ρ := by
  have hW0 := StableGraphs.solutionFamily_zero hW
  let P := StableGraphs.stableParameterProjection b A hA
  have hflow (ξ : stableParameters b A) (t : ℝ) (ht : 0 ≤ t) :
      φ t (graphMap h ξ) = (W ξ).atReal t := by
    rw [← hgraph ξ]
    exact StableGraphs.flow_eq_solutionFamily b A r δ hδ hlip φ hφ K α β W hW ξ t ht
  have hbound (ξ : stableParameters b A) (t : ℝ) (ht : 0 ≤ t) :
      ‖φ t (graphMap h ξ)‖ ≤ Real.exp (-β*t) * ‖W ξ‖ := by
    rw [hflow ξ t ht, WeightedPath.atReal_nonneg _ ht]
    exact WeightedPath.eval_norm_le _ _
  have hexp (t : ℝ) (ht : 0 ≤ t) : Real.exp (-β*t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht)
  have hsurvive (ξ : stableParameters b A) (hξ : ‖W ξ‖ < η)
      (t : ℝ) (ht : 0 ≤ t) : ‖φ t (graphMap h ξ)‖ < ρ := by
    calc
      ‖φ t (graphMap h ξ)‖ ≤ Real.exp (-β*t)*‖W ξ‖ := hbound ξ t ht
      _ ≤ ‖W ξ‖ := mul_le_of_le_one_left (norm_nonneg _) (hexp t ht)
      _ < η := hξ
      _ ≤ ρ := hηρ
  have hmatch (ξ : stableParameters b A) (hξ : ‖W ξ‖ < η)
      (t : ℝ) (ht : 0 ≤ t) :
      (t,graphPoint p h ξ) ∈ flowDomain F ∧
      flow F t (graphPoint p h ξ) = p + φ t (graphMap h ξ) := by
    apply StableManifold.flow_matches_on_segment F hF p _ r ρ hloc φ hφ
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact hsurvive ξ hξ s hs.1
  refine ⟨hgeom, hρ, isOpen_lt hWc.norm continuous_const, ?_, ?_, ?_, ?_⟩
  · simpa only [mem_ofPred_eq, hW0, norm_zero] using hη
  · intro ξ hξ
    have hh := hsurvive ξ hξ 0 le_rfl
    rw [hφ.2.1] at hh
    exact ⟨(hloc _ hh).1, by simpa only [graphPoint, add_sub_cancel_left] using hh⟩
  · intro ξ hξ
    refine ⟨(hmatch ξ hξ 0 le_rfl).1.1, fun t ht => (hmatch ξ hξ t ht).1, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hβ)).mul_const ‖W ξ‖
    simp only [zero_mul] at he
    apply squeeze_zero' (Eventually.of_forall (fun t => dist_nonneg)) _ he
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [dist_eq_norm, (hmatch ξ hξ t ht).2, add_sub_cancel_left]
    simpa only [Function.comp_apply, id_eq, neg_mul] using hbound ξ t ht
  · intro ξ hξ t ht
    let ζ := P ((W ξ).atReal t)
    have hshift : StableGraphs.weightedShift (W ξ) t ht = W ζ :=
      StableGraphs.solutionFamily_shift b A hA K α β δ hK hα hd hβ hβα hδ
        r hr hlip W hW ξ t ht
    have hζ : ‖W ζ‖ < η := by
      rw [← hshift]
      exact ((StableGraphs.weightedShift_norm_le _ t ht).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hexp t ht))).trans_lt hξ
    refine ⟨ζ, hζ, ?_⟩
    have hh := congrArg (fun w : WeightedPath β E => w.atReal 0) hshift
    rw [StableGraphs.weightedShift_atReal _ ht le_rfl, zero_add, hgraph] at hh
    rw [(hmatch ξ hξ t ht).2, hflow ξ t ht]
    exact congrArg (fun z => p + z) hh.symm

/-- Convergence supplies a late confined half-line; local characterization
then puts its initial point on the graph, and continuity in the weighted
norm makes this point lie in the chosen open portion. -/
lemma capture_weighted_portion
    {n : Type u} [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain) (p : E)
    (h : stableParameters b A → unstableParameters b A)
    (β : ℝ) (W : stableParameters b A → WeightedPath β E)
    (hWc : Continuous W) (hW0 : W 0 = 0)
    (ρ η : ℝ) (hρ : 0 < ρ) (hη : 0 < η)
    (hchar : ∀ x : ℝ → E, ContinuousOn x (Ici 0) →
      (∀ t, 0 ≤ t → HasDerivWithinAt x (F.eval (x t)) (Ici 0) t) →
      (∀ t, 0 ≤ t → ‖x t-p‖ < ρ) → x 0-p ∈ range (graphMap h)) :
    CapturesStableSet F p h {ξ | ‖W ξ‖ < η} := by
  let P := StableGraphs.stableParameterProjection b A hA
  have hPgraph (ξ : stableParameters b A) : P (graphMap h ξ) = ξ := by
    simp only [P, graphMap, map_add, StableGraphs.stableParameterProjection_left,
      StableGraphs.stableParameterProjection_unstable, add_zero]
  intro x hx
  have hevent1 : ∀ᶠ t : ℝ in atTop, ‖flow F t x-p‖ < ρ := by
    have hn := (hx.2.2.sub_const p).norm
    simp only [sub_self, norm_zero] at hn
    exact hn.eventually_lt_const hρ
  have hevent2 : ∀ᶠ t : ℝ in atTop, ‖W (P (flow F t x-p))‖ < η := by
    have hsub := hx.2.2.sub_const p
    simp only [sub_self] at hsub
    have hn := ((hWc.comp P.continuous).tendsto 0).comp hsub
    simp only [Function.comp_apply, map_zero, hW0] at hn
    have hn' := hn.norm
    simp only [norm_zero] at hn'
    exact hn'.eventually_lt_const hη
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hevent1.and hevent2)
  obtain ⟨m, hm⟩ := exists_nat_ge T₀
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  let y := flow F (m : ℝ) x
  have hy := stableSet_forward F hF p hx hm0
  have hsol := flow_ivp F hF hy.1
  have hhalf : Ici (0 : ℝ) ⊆ (flowInterval F y).carrier := fun t ht => (hy.2.1 t ht).2
  have htrans := Ch11.Flow.flow_translation F hF x hx.1 (m : ℝ) (hx.2.1 m hm0).2
  have hgraph : y-p ∈ range (graphMap h) := by
    have hh := hchar (fun t => flow F t y)
      (hsol.1.1.continuousOn.mono hhalf)
      (fun t ht => (hsol.1.2.2 t (hhalf ht)).hasDerivWithinAt)
      (by
        intro t ht
        rw [htrans.2 t (hx.2.1 (t+m) (by positivity)).2]
        exact (hT₀ (t+m) (by linarith)).1)
    simpa only [y, (Ch11.Flow.flow_zero F hF y hy.1).2] using hh
  obtain ⟨ξ, hξ⟩ := hgraph
  have hparam : P (y-p) = ξ := by rw [← hξ, hPgraph]
  refine ⟨m, ξ, ?_, ?_⟩
  · change ‖W ξ‖ < η
    rw [← hparam]
    exact (hT₀ m hm).2
  · change p + graphMap h ξ = y
    rw [hξ]
    exact add_sub_cancel _ _

/-- Construction from exactly the original hyperbolic-equilibrium hypotheses.
The local portion uses the whole weighted trajectory norm, rather than a
parameter ball whose image need not be forward invariant. -/
theorem stable_portion_within
    {n : Type u} [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ E) (F : AutonomousODE E) (p : E)
    (A : Matrix n n ℝ) (k : ℕ∞)
    (hp : p ∈ F.domain) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k F.eval F.domain)
    (hfp : F.eval p = 0) (hdf : HasFDerivAt F.eval (matrixOperatorEquiv b A) p)
    (hA : hyperbolicValue A) (R : ℝ) (hR : 0 < R) :
    ∃ (h : stableParameters b A → unstableParameters b A)
      (V : Set (stableParameters b A)) (ρ : ℝ),
      ρ ≤ R ∧ LocalPortion k F p (stableParameters b A) (unstableParameters b A) h V ρ ∧
      CapturesStableSet F p h V := by
  obtain ⟨K, α, hK, hα, hd⟩ := D13Unified.Ch20.exponential_dichotomy b A hA
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let β : ℝ := α/2
  let δ : ℝ := α/(16*K)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβα : β < α := by dsimp [β]; linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hrate : contractionRate K α β δ = 1/6 := by
    dsimp [contractionRate, β, δ]
    field_simp
    ring
  have hq : contractionRate K α β δ < 1 := by rw [hrate]; norm_num
  have hq0 : 2*K*δ/α < 1 := by
    have heq : 2*K*δ/α = 1/8 := by dsimp [δ]; field_simp; ring
    rw [heq]
    norm_num
  obtain ⟨r, φ, hrc, hrs, hr0, hdr0, hlip, ⟨U, hU, hU0, hUF, hlocU⟩, hj, hφ⟩ :=
    StableGraphs.centered_cutoff b F.domain F.eval p A k F.isOpen_domain hp hk hf hfp hdf δ hδ
  obtain ⟨h, W, hgeom, hWc, hW, hgraph, hbound⟩ :=
    StableGraphs.stable_graph_geometry_exists b A hA K α β δ hK hα hd hβ hβα hδ.le
      hq r k hr0 hdr0 hlip hk hrc hj
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.mp hU 0 hU0
  let ρ := min r₀ R
  have hρ : 0 < ρ := lt_min hr₀ hR
  have hρU : Metric.ball (0 : E) ρ ⊆ U :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hr₀U
  have hloc (x : E) (hx : ‖x‖ < ρ) :
      p+x ∈ F.domain ∧ matrixOperatorEquiv b A x + r x = F.eval (p+x) := by
    have hxU : x ∈ U := hρU (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
    exact ⟨hUF x hxU, hlocU x hxU⟩
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hf.of_le (by exact_mod_cast hk)
  have hflowbound : ∀ ξ t, 0 ≤ t → ‖φ t (graphMap h ξ)‖ ≤
      (K / (1-contractionRate K α β δ))*‖(ξ : E)‖*Real.exp (-β*t) := by
    intro ξ t ht
    rw [← hgraph ξ, StableGraphs.flow_eq_solutionFamily b A r δ hδ.le hlip φ hφ
      K α β W hW ξ t ht]
    exact hbound ξ t ht
  have hchar (x : ℝ → E) (hc : ContinuousOn x (Ici 0))
      (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (F.eval (x t)) (Ici 0) t)
      (hb : ∀ t, 0 ≤ t → ‖x t-p‖ < ρ) : x 0-p ∈ range (graphMap h) := by
    apply StableManifold.bounded_trajectory_on_graph b A hA K α δ hK hα hd hδ.le hq0
      r hlip φ hφ h (K/(1-contractionRate K α β δ)) β
      (by positivity) hβ.le hflowbound (fun t => x t-p) (hc.sub continuousOn_const)
    · intro t ht
      have hh := (hx t ht).sub_const p
      rw [show F.eval (x t) = matrixOperatorEquiv b A (x t-p) + r (x t-p) by
        simpa only [add_sub_cancel] using (hloc (x t-p) (hb t ht)).2.symm] at hh
      exact hh
    · exact ⟨ρ, fun t ht => (hb t ht).le⟩
  let V : Set (stableParameters b A) := {ξ | ‖W ξ‖ < ρ/2}
  refine ⟨h, V, ρ, min_le_right _ _, ?_, ?_⟩
  · exact weighted_local_portion b A hA F hF1 p K α β δ hK hα hd hβ hβα hδ.le
      r hr0 hlip φ hφ h k hgeom W hWc.continuous hW hgraph ρ (ρ/2)
      hρ (by positivity) (by linarith) hloc
  · exact capture_weighted_portion b A hA F hF1 p h β W hWc.continuous
      (StableGraphs.solutionFamily_zero hW) ρ (ρ/2) hρ (by positivity) hchar

theorem stable_portion :
    Specs.D13Unified.Ch20.GlobalStableManifold.stablePortionExpected.{u,v} := by
  intro n _ _ E _ _ _ b F p A k hp hk hf hfp hdf hA
  obtain ⟨h, V, ρ, _, hlocal, hcapture⟩ :=
    stable_portion_within b F p A k hp hk hf hfp hdf hA 1 zero_lt_one
  exact ⟨h, V, ρ, hlocal, hcapture⟩

/-- Finite-order flow regularity also yields the stated smooth case. -/
lemma timeMap_contDiffOn (k : ℕ∞) (hk : 1 ≤ k) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ k F.eval F.domain) (t : ℝ) :
    ContDiffOn ℝ k (flow F t) (timeDomainValue F t) := by
  apply contDiffOn_iff_forall_nat_le.mpr
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    exact (Ch11.Flow.contDiffOn_timeMap 1 (by omega) F
      (hF.of_le (by exact_mod_cast hk)) t).of_le (by simp)
  · exact Ch11.Flow.contDiffOn_timeMap j (Nat.one_le_iff_ne_zero.mpr hj0) F
      (hF.of_le (by exact_mod_cast hj)) t

lemma stageMap_contDiffOn (k : ℕ∞) (hk : 1 ≤ k) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ k F.eval F.domain) (p : E)
    {S T : Submodule ℝ E} {h : S → T} {V : Set S}
    (hg : ContDiff ℝ k (graphMap h)) (m : ℕ) :
    ContDiffOn ℝ k (stageMap F p h m) (stageDomain F p h V m) :=
  (timeMap_contDiffOn k hk F hF _).comp
    (contDiff_const.add hg).contDiffOn (fun _ hx => hx.2)

/-- Differentiating the reverse time identity shows that a stage retains
all stable directions. No global backward completeness is required. -/
lemma stageMap_injective_differential (k : ℕ∞) (hk : 1 ≤ k) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ k F.eval F.domain) (p : E)
    {S T : Submodule ℝ E} {h : S → T} {V : Set S}
    (hg : ContDiff ℝ k (graphMap h)) (hV : IsOpen V)
    (hginj : ∀ ξ, Function.Injective (fderiv ℝ (graphMap h) ξ))
    (m : ℕ) {ξ : S} (hξ : ξ ∈ stageDomain F p h V m) :
    Function.Injective (fderiv ℝ (stageMap F p h m) ξ) := by
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hG1 : ContDiff ℝ 1 (graphMap h) := hg.of_le (by exact_mod_cast hk)
  have ho := stageDomain_open F hF1 p hg.continuous hV m
  have hstage := stageMap_contDiffOn k hk F hF p hg m (V := V)
  have hds := ((hstage.of_le (by exact_mod_cast hk)).differentiableOn_one.differentiableAt
    (ho.mem_nhds hξ)).hasFDerivAt
  have hrev := Ch11.Flow.reverse_flow F hF1 hξ.2
  have hmem : stageMap F p h m ξ ∈ timeDomainValue F (m : ℝ) := by
    simpa only [stageMap, neg_neg] using hrev.1
  have hback := ((Ch11.Flow.contDiffOn_timeMap 1 (by omega) F hF1 (m : ℝ)).differentiableOn_one.differentiableAt
    ((Ch11.Flow.isOpen_timeDomain F hF1 _).mem_nhds hmem)).hasFDerivAt
  have hcomp := hback.comp ξ hds
  have hparam := (hG1.differentiable (by norm_num) ξ).hasFDerivAt
  have hsame : HasFDerivAt (fun ζ => flow F (m : ℝ) (stageMap F p h m ζ))
      (fderiv ℝ (graphMap h) ξ) ξ := by
    apply (hparam.const_add p).congr_of_eventuallyEq
    filter_upwards [ho.mem_nhds hξ] with ζ hζ
    simpa only [stageMap, graphPoint, neg_neg] using (Ch11.Flow.reverse_flow F hF1 hζ.2).2
  have hid := hcomp.unique hsame
  intro v w hvw
  apply hginj ξ
  have hh := congrArg (fun L : S →L[ℝ] E => L v) hid
  have hh' := congrArg (fun L : S →L[ℝ] E => L w) hid
  rw [← hh, ← hh']
  change (fderiv ℝ (flow F (m : ℝ)) (stageMap F p h m ξ))
      ((fderiv ℝ (stageMap F p h m) ξ) v) =
    (fderiv ℝ (flow F (m : ℝ)) (stageMap F p h m ξ))
      ((fderiv ℝ (stageMap F p h m) ξ) w)
  rw [hvw]

/-- The exact global stable set is a nested union of injectively immersed
open parameter stages, built from the original field's actual time maps. -/
theorem global_stages :
    Specs.D13Unified.Ch20.GlobalStableManifold.globalStagesExpected.{u,v} := by
  intro n _ _ E _ _ _ b F p A k hp hk hf hfp hdf hA
  obtain ⟨h, V, ρ, hlocal, hcapture⟩ := stable_portion b F p A k hp hk hf hfp hdf hA
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hf.of_le (by exact_mod_cast hk)
  have hg := hlocal.1.2.2.2.1
  have hV := hlocal.2.2.1
  have hstable := hlocal.2.2.2.2.2.1
  have hinv := hlocal.2.2.2.2.2.2
  refine ⟨h, V, ρ, hlocal, hcapture,
    stableSet_eq_stages F hF1 p h V hstable hcapture,
    stages_monotone F hF1 p h V hstable hinv, ?_⟩
  intro m
  exact ⟨stageDomain_open F hF1 p hg.continuous hV m,
    stageMap_contDiffOn k hk F hf p hg m,
    stageMap_injOn F hF1 p hlocal.1.2.2.2.2.1.injective m,
    fun ξ hξ => stageMap_injective_differential k hk F hf p hg hV
      hlocal.1.2.2.2.2.2.1 m hξ⟩

/-- The original graph and its spectral coordinate projection meet every
hypothesis of the partial-flow stage compatibility theorem. -/
lemma localPortion_stageHypotheses
    {n : Type u} [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (k : ℕ∞) (hk : 1 ≤ k) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ k F.eval F.domain) (p : E)
    {h : stableParameters b A → unstableParameters b A}
    {V : Set (stableParameters b A)} {ρ : ℝ}
    (H : LocalPortion k F p (stableParameters b A) (unstableParameters b A) h V ρ) :
    StableStageCompatibility.Hypotheses F k (graphPoint p h)
      (fun x => StableGraphs.stableParameterProjection b A hA (x-p)) V := by
  let P := StableGraphs.stableParameterProjection b A hA
  have hg := H.1.2.2.2.1
  refine {
    one_le := hk
    field_regular := hF
    graph_regular := contDiff_const.add hg
    projection_regular := P.contDiff.comp (contDiff_id.sub contDiff_const)
    left_inverse := ?_
    graph_differential := ?_
    open_portion := H.2.2.1
    admissible := fun ξ hξ => (H.2.2.2.2.1 ξ hξ).1
    forward_exists := fun ξ hξ t ht => (H.2.2.2.2.2.1 ξ hξ).2.1 t ht
    forward_invariant := H.2.2.2.2.2.2 }
  · intro ξ
    simp only [graphPoint, add_sub_cancel_left, graphMap, map_add,
      StableGraphs.stableParameterProjection_left,
      StableGraphs.stableParameterProjection_unstable, add_zero]
  · intro ξ
    have hd := ((hg.of_le (by exact_mod_cast hk)).differentiable_one ξ).hasFDerivAt
    change Function.Injective (fderiv ℝ (fun ξ => p + graphMap h ξ) ξ)
    rw [(hd.const_add p).fderiv]
    exact H.1.2.2.2.2.2.1 ξ

/-- Glue the actual stages and transport the resulting atlas, preserving
ambient point values, to the original stable-set subtype. -/
lemma stableAtlas_of_stages
    (F : AutonomousODE E) (p : E) (k : ℕ∞)
    {S T : Submodule ℝ E} {h : S → T} {V : Set S}
    (D : CountableImmersedAtlas.Data S E k)
    (hU : D.U = StableStageCompatibility.stageDomain F (graphPoint p h) V)
    (hf : D.f = StableStageCompatibility.stageMap F (graphPoint p h))
    (hset : stableSet F p = ⋃ m : ℕ, backwardStage F p h V m) :
    Nonempty (StableAtlas k F p h V) := by
  classical
  change D.U = stageDomain F p h V at hU
  change D.f = stageMap F p h at hf
  obtain ⟨a⟩ := CountableImmersedAtlas.gluing S E k D
  have hs : stableSet F p = {x : E | ∃ m ξ, ξ ∈ D.U m ∧ D.f m ξ = x} := by
    rw [hset]
    ext x
    simp only [mem_iUnion, backwardStage, mem_image, mem_ofPred_eq, hU, hf]
  let e : stableSet F p ≃ CountableImmersedAtlas.Point D := Set.equivOfEq hs
  let : TopologicalSpace (CountableImmersedAtlas.Point D) := a.topology
  let : TopologicalSpace (stableSet F p) := e.topologicalSpace
  let eH : stableSet F p ≃ₜ CountableImmersedAtlas.Point D := e.homeomorph
  have heval (x : stableSet F p) : (e x).val = x.val := rfl
  have heval' (x : CountableImmersedAtlas.Point D) : (e.symm x).val = x.val := rfl
  let c : ℕ → OpenPartialHomeomorph (stableSet F p) S :=
    fun m => eH.toOpenPartialHomeomorph.trans (a.chart m)
  have hcsource (m : ℕ) : (c m).source = {x : stableSet F p | (x : E) ∈ backwardStage F p h V m} := by
    ext x
    simp only [c, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      mem_inter_iff, mem_univ, true_and, mem_preimage, a.source_eq]
    change (e x).val ∈ D.f m '' D.U m ↔ x.val ∈ backwardStage F p h V m
    rw [heval, hf, hU]
    rfl
  have hctarget (m : ℕ) : (c m).target = stageDomain F p h V m := by
    simp only [c, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
      preimage_univ, inter_univ, a.target_eq, hU]
  have hccover : ⋃ m, (c m).source = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨m, hm⟩ := mem_iUnion.mp (a.cover.symm ▸ mem_univ (e x))
    refine mem_iUnion.mpr ⟨m, ?_⟩
    change x ∈ univ ∧ eH x ∈ (a.chart m).source
    exact ⟨mem_univ _, hm⟩
  have hctrans (m n : ℕ) :
      ContDiffOn ℝ k ((c m).symm.trans (c n)) ((c m).symm.trans (c n)).source := by
    simpa only [c, ← Homeomorph.transOpenPartialHomeomorph_eq_trans,
      Homeomorph.transOpenPartialHomeomorph_symm_trans] using a.transitions m n
  let cs : ChartedSpace S (stableSet F p) := {
    atlas := range c
    chartAt := fun x => c (Classical.choose (mem_iUnion.mp (hccover.symm ▸ mem_univ x)))
    mem_chart_source := fun x => Classical.choose_spec (mem_iUnion.mp (hccover.symm ▸ mem_univ x))
    chart_mem_atlas := fun _ => mem_range_self _ }
  have hm : @IsManifold ℝ _ S _ _ S _ (modelWithCornersSelf ℝ S)
      (k : ℕ∞ω) (stableSet F p) _ cs := by
    let := cs
    apply isManifold_of_contDiffOn (modelWithCornersSelf ℝ S) (k : ℕ∞ω) (stableSet F p)
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    simpa using hctrans m n
  refine ⟨{
    topology := e.topologicalSpace
    hausdorff := ?_
    secondCountable := ?_
    chart := c
    source_eq := hcsource
    target_eq := hctarget
    cover := hccover
    inverse_eq := ?_
    transitions := hctrans
    parametrization := ?_
    injective_differential := ?_
    inclusion_continuous := ?_
    inclusion_injective := Subtype.val_injective
    inclusion_regular := ?_
    inclusion_differential := ?_
    chartedSpace := cs
    atlas_eq := rfl
    manifold := hm
    dimension := fun _ => rfl }⟩
  · let := a.hausdorff
    exact eH.isEmbedding.t2Space
  · let := a.second_countable
    exact eH.isInducing.secondCountableTopology
  · intro m ξ hξ
    have hξ' : ξ ∈ D.U m := by simpa only [hctarget, hU] using hξ
    change (e.symm ((a.chart m).symm ξ)).val = stageMap F p h m ξ
    rw [heval']
    simpa only [hf] using a.inverse_eq m ξ hξ'
  · intro m
    simpa only [hf, hU] using D.regular m
  · intro m ξ hξ
    simpa only [hf] using D.differential m ξ (hU.symm ▸ hξ)
  · exact a.inclusion_continuous.comp eH.continuous
  · intro m
    have he : (fun ξ => ((c m).symm ξ : E)) = (fun ξ => ((a.chart m).symm ξ).val) := by
      funext ξ
      exact heval' _
    rw [he, hctarget, ← hU]
    exact a.inclusion_regular m
  · intro m ξ hξ
    have he : (fun η => ((c m).symm η : E)) = (fun η => ((a.chart m).symm η).val) := by
      funext η
      exact heval' _
    rw [he]
    exact a.inclusion_differential m ξ (by simpa only [hctarget, ← hU] using hξ)

/-- The global stable set carries the countable compatible Cᵏ immersed
manifold atlas on the actual original-flow backward-existence domains. -/
theorem global_stable_manifold :
    Specs.D13Unified.Ch20.GlobalStableManifold.globalStableManifoldExpected.{u,v} := by
  intro n _ _ E _ _ _ b F p A k hp hk hf hfp hdf hA
  obtain ⟨h, V, ρ, H, hcapture, hset, hmono, _⟩ :=
    global_stages b F p A k hp hk hf hfp hdf hA
  have HH := localPortion_stageHypotheses b A hA k hk F hf p H
  obtain ⟨D, hU, hmaps⟩ := StableStageCompatibility.atlas_package
    (stableParameters b A) E F k (graphPoint p h)
      (fun x => StableGraphs.stableParameterProjection b A hA (x-p)) V HH
      ⟨0, H.2.2.2.1⟩
  exact ⟨h, V, ρ, H, hcapture, hset, hmono, stableAtlas_of_stages F p k D hU hmaps hset⟩

end D13Unified.Ch20.GlobalStableManifold
