import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FspaceOpenMapping
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.TvsMetrization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Baire
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Pointwise

open Set Filter
open scoped Topology Pointwise

namespace ExpandedFA.P1.FspaceOpenMapping

section ImageClosure
variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
    [NormedAddCommGroup F] [Module 𝕜 F] [ContinuousSMul 𝕜 F] [BaireSpace F]

/-- Baire's theorem and scalar absorption give interior to the closure of
an image of any zero neighborhood. The group norms need not be homogeneous. -/
theorem image_closure_interior (T : E →ₗ[𝕜] F) (hT : Function.Surjective T)
    (W : Set E) (hW : W ∈ 𝓝 (0 : E)) :
    (interior (closure (T '' W))).Nonempty := by
  let c : ℕ → 𝕜 := fun n => (n : 𝕜) + 1
  have hc : ∀ n, c n ≠ 0 := by
    intro n
    dsimp [c]
    exact_mod_cast (Nat.succ_ne_zero n)
  have hcover : (⋃ n : ℕ, closure (T '' (c n • W))) = univ := by
    apply eq_univ_iff_forall.mpr
    intro y
    obtain ⟨x, rfl⟩ := hT y
    obtain ⟨r, hr⟩ := absorbs_iff_norm.mp ((absorbent_nhds_zero (𝕜 := 𝕜) hW) x)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    have hx : x ∈ c n • W := hr (c n) (by
      dsimp [c]
      rw [← Nat.cast_add_one, RCLike.norm_natCast]
      exact hn.le.trans (by simp)) (mem_singleton x)
    exact mem_iUnion.mpr ⟨n, subset_closure (mem_image_of_mem T hx)⟩
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed
    (fun n : ℕ => isClosed_closure (s := T '' (c n • W))) hcover
  have him : T '' (c n • W) = c n • (T '' W) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨T x, mem_image_of_mem T hx, (T.map_smul _ _).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨c n • x, ⟨x, hx, rfl⟩, T.map_smul _ _⟩
  rw [him, closure_smul₀' (hc n), interior_smul₀ (hc n)] at hn
  exact smul_set_nonempty.mp hn

/-- The difference of two points of the image closure lies in the closure
of the difference image. This turns nonempty interior into a zero neighborhood. -/
theorem closure_image_mem_nhds (T : E →ₗ[𝕜] F) (hT : Function.Surjective T)
    (U : Set E) (hU : U ∈ 𝓝 (0 : E)) : closure (T '' U) ∈ 𝓝 (0 : F) := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  let W := Metric.ball (0 : E) (r / 2)
  obtain ⟨a, ha⟩ := image_closure_interior T hT W (Metric.ball_mem_nhds _ (half_pos hr))
  have hV : (fun b : F => b - a) '' interior (closure (T '' W)) ∈ 𝓝 (0 : F) := by
    simpa using (isOpenMap_sub_right a).image_mem_nhds (isOpen_interior.mem_nhds ha)
  apply mem_of_superset hV
  rintro _ ⟨b, hb, rfl⟩
  apply map_mem_closure₂ continuous_sub (interior_subset hb) (interior_subset ha)
  rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
  refine ⟨x - z, hrU ?_, T.map_sub x z⟩
  simp only [W, Metric.mem_ball, dist_zero_right] at hx hz ⊢
  exact (norm_sub_le x z).trans_lt (by linarith)

end ImageClosure

section SuccessiveCorrections
variable {E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F]

/-- Successive small corrections remove image closures, using only additive
group norms. In particular their balls need not be convex or scale like norms. -/
theorem image_mem_nhds_of_closure (T : E →+ F) (hcont : Continuous T)
    (hclosure : ∀ r : ℝ, 0 < r → closure (T '' Metric.ball (0 : E) r) ∈ 𝓝 (0 : F))
    (U : Set E) (hU : U ∈ 𝓝 (0 : E)) : T '' U ∈ 𝓝 (0 : F) := by
  classical
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  let ε : ℕ → ℝ := fun n => (r / 4) * (1 / 2 : ℝ) ^ n
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hδ : ∀ n : ℕ, ∃ d > 0,
      Metric.ball (0 : F) d ⊆ closure (T '' Metric.ball (0 : E) (ε n)) :=
    fun n => Metric.mem_nhds_iff.mp (hclosure (ε n) (hε n))
  choose δ hδpos hδsub using hδ
  let V : ℕ → Set F := fun n => Metric.ball 0 (min (δ n) ((1 / 2 : ℝ) ^ n))
  have hVpos : ∀ n, 0 < min (δ n) ((1 / 2 : ℝ) ^ n) :=
    fun n => lt_min (hδpos n) (by positivity)
  have hVsub : ∀ n, V n ⊆ closure (T '' Metric.ball (0 : E) (ε n)) := by
    intro n y hy
    exact hδsub n ((Metric.ball_subset_ball (min_le_left _ _)) hy)
  apply mem_of_superset (Metric.ball_mem_nhds (0 : F) (hVpos 0))
  intro y hy
  have hstep : ∀ (n : ℕ) (p : E), y - T p ∈ V n →
      ∃ q : E, y - T q ∈ V (n + 1) ∧ dist p q ≤ ε n := by
    intro n p hp
    obtain ⟨_, ⟨z, hz, rfl⟩, hdist⟩ :=
      Metric.mem_closure_iff.mp (hVsub n hp) _ (hVpos (n + 1))
    refine ⟨p + z, ?_, ?_⟩
    · change dist (y - T (p + z)) 0 < _
      simpa only [T.map_add, dist_eq_norm, sub_zero, sub_sub] using hdist
    · have hz' : ‖z‖ < ε n := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      simpa only [dist_eq_norm, sub_add_cancel_left, norm_neg] using hz'.le
  let next : (n : ℕ) → {p : E // y - T p ∈ V n} → {p : E // y - T p ∈ V (n + 1)} :=
    fun n p => ⟨(hstep n p.1 p.2).choose, (hstep n p.1 p.2).choose_spec.1⟩
  let p : (n : ℕ) → {x : E // y - T x ∈ V n} :=
    fun n => Nat.rec ⟨0, by simpa only [map_zero, sub_zero] using hy⟩ next n
  have hp0 : (p 0).1 = 0 := rfl
  have hdist : ∀ n, dist (p n).1 (p (n + 1)).1 ≤ (r / 4) * (1 / 2 : ℝ) ^ n := by
    intro n
    exact (hstep n (p n).1 (p n).2).choose_spec.2
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 2) (r / 4) (by norm_num) hdist)
  have hxU : x ∈ U := by
    apply hrU
    have hb := dist_le_of_le_geometric_of_tendsto₀ (1 / 2) (r / 4) (by norm_num : (1 / 2 : ℝ) < 1) hdist hx
    rw [hp0, dist_comm] at hb
    change dist x 0 < r
    have : (r / 4) / (1 - (1 / 2 : ℝ)) = r / 2 := by ring
    rw [this] at hb
    exact hb.trans_lt (half_lt_self hr)
  have hres : Tendsto (fun n => y - T (p n).1) atTop (𝓝 (0 : F)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num) :
        Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0))
    simpa only [dist_zero_right] using ((show dist (y - T (p n).1) 0 < min (δ n) ((1 / 2 : ℝ) ^ n) from
      (p n).2).le.trans (min_le_right _ _))
  have heq : y - T x = 0 := tendsto_nhds_unique
    (tendsto_const_nhds.sub (hcont.tendsto x |>.comp hx)) hres
  exact ⟨x, hxU, (sub_eq_zero.mp heq).symm⟩

end SuccessiveCorrections

/-- An invariant metric is a norm on the additive group only. No scalar
homogeneity, and hence no local convexity, is introduced by this construction. -/
private abbrev groupNormOfInvariantMetric {E : Type*} [AddCommGroup E] [MetricSpace E]
    (hd : ∀ x y z : E, dist (x + z) (y + z) = dist x y) : NormedAddCommGroup E :=
  { ‹AddCommGroup E›, ‹MetricSpace E› with
    norm := fun x => dist x 0
    dist_eq := fun x y => by
      change dist x y = dist (-x + y) 0
      calc
        dist x y = dist (x + -x) (y + -x) := (hd x y (-x)).symm
        _ = dist (-x + y) 0 := by simp only [add_neg_cancel, add_comm y, dist_comm] }

/-- The open mapping theorem without any local convexity assumption. -/
theorem open_mapping : FspaceOpenMappingSpec.OpenMapping := by
  intro 𝕜 E F _ _ _ tE _ _ tF hE hF T hcont hsurj
  obtain ⟨haddE, hsmulE, hmetE, hcompleteE⟩ := hE
  obtain ⟨haddF, hsmulF, hmetF, hcompleteF⟩ := hF
  let := haddE
  let := haddF
  let := hsmulE
  let := hsmulF
  let := hmetE
  let := hmetF
  obtain ⟨mE, hmE, hdE, _⟩ := tvs_exists_balanced_invariant_metric 𝕜 E
    ⟨haddE, hsmulE⟩ inferInstance
  obtain ⟨mF, hmF, hdF, _⟩ := tvs_exists_balanced_invariant_metric 𝕜 F
    ⟨haddF, hsmulF⟩ inferInstance
  let : MetricSpace E := mE.replaceTopology hmE.symm
  let : MetricSpace F := mF.replaceTopology hmF.symm
  let : NormedAddCommGroup E := groupNormOfInvariantMetric hdE
  let : NormedAddCommGroup F := groupNormOfInvariantMetric hdF
  have : CompleteSpace E := by
    change @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) at hcompleteE
    rwa [IsUniformAddGroup.rightUniformSpace_eq] at hcompleteE
  have : CompleteSpace F := by
    change @CompleteSpace F (IsTopologicalAddGroup.rightUniformSpace F) at hcompleteF
    rwa [IsUniformAddGroup.rightUniformSpace_eq] at hcompleteF
  have : BaireSpace F := C07Baire.baireSpace_of_completeMetric F
  apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
  rw [Filter.le_map_iff]
  intro U hU
  exact image_mem_nhds_of_closure T.toAddMonoidHom hcont
    (fun r hr => closure_image_mem_nhds T hsurj _ (Metric.ball_mem_nhds 0 hr)) U hU

end ExpandedFA.P1.FspaceOpenMapping
