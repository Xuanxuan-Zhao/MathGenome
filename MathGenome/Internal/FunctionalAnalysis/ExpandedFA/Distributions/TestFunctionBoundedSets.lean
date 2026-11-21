import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.TestFunctionLFTopology
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.TestFunctionBoundedSets
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

open Set TopologicalSpace Filter
open scoped Topology Distributions BoundedContinuousFunction NNReal

namespace ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- All iterated derivatives, as continuous linear maps on the LF space. -/
noncomputable def testDerivativeCLM (k : ℕ) :
    Tests 𝕜 Ω →L[𝕜] (Domain d →ᵇ ((Domain d) [×k]→L[ℝ] 𝕜)) := by
  letI : SeminormedAddCommGroup ((Domain d) [×k]→L[ℝ] 𝕜) := inferInstance
  exact TestFunction.limitCLM 𝕜
    (fun φ : Tests 𝕜 Ω =>
      ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k
        (ContDiffMapSupportedIn.of_support_subset (K := ⟨tsupport φ, φ.hasCompactSupport⟩)
          φ.contDiff subset_closure))
    (fun _ _ => ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k)
    (fun _ _ φ => by
      ext x
      simp only [ContDiffMapSupportedIn.structureMapCLM_top_apply]
      rfl)

@[simp] theorem testDerivativeCLM_apply (k : ℕ) (φ : Tests 𝕜 Ω) (x : Domain d) :
    testDerivativeCLM (𝕜 := 𝕜) k φ x = iteratedFDeriv ℝ k φ x := by
  change ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k
    (ContDiffMapSupportedIn.of_support_subset (K := ⟨tsupport φ, φ.hasCompactSupport⟩)
      φ.contDiff subset_closure) x = _
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  rfl

theorem step_embedding (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω) :
    Topology.IsEmbedding (TestFunction.ofSupportedIn (F := 𝕜) (n := ⊤) hK) := by
  let g := ContinuousLinearMap.pi (fun k => testDerivativeCLM (𝕜 := 𝕜) (Ω := Ω) k)
  apply Topology.IsEmbedding.of_comp (TestFunction.continuous_ofSupportedIn hK) g.continuous
  convert (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
    (𝕜 := 𝕜) (E := Domain d) (F := 𝕜) (n := ⊤) (K := K)).isEmbedding using 1
  funext φ k
  ext x
  simp [g]

theorem step_metrizable (K : Compacts (Domain d)) : MetrizableSpace (Step 𝕜 K) := by
  let : ∀ k : ℕ, MetricSpace ((Domain d) [×k]→L[ℝ] 𝕜) := fun _ => inferInstance
  exact (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
    (𝕜 := 𝕜) (E := Domain d) (F := 𝕜) (n := ⊤) (K := K)).isEmbedding.metrizableSpace

theorem step_topology :
    Specs.ExpandedFA.Distributions.TestFunctionBoundedSets.stepTopologyType := by
  intro 𝕜 _ d Ω K hK
  exact ⟨step_embedding K hK, step_seminorm_topology 𝕜 d K, step_metrizable K⟩

/-- A continuous seminorm is bounded on any von Neumann bounded set. -/
theorem bounded_seminorm_image {B : Set (Tests 𝕜 Ω)}
    (hB : Bornology.IsVonNBounded ℝ B) (p : Seminorm ℝ (Tests 𝕜 Ω))
    (hp : Continuous p) : BddAbove (p '' B) := by
  obtain ⟨e⟩ := exists_exhaustion d Ω
  exact (generating_seminorms 𝕜 d Ω e).isVonNBounded_iff_seminorm_bddAbove.mp hB
    ⟨p, fun j => hp.comp (TestFunction.continuous_ofSupportedIn (e.inside j))⟩

/-- Weighted point evaluation is a continuous real seminorm, including for
complex-valued test functions. -/
noncomputable def weightedEvaluation (x : Domain d) (c : ℝ≥0) :
    Seminorm ℝ (Tests 𝕜 Ω) :=
  c • (normSeminorm ℝ 𝕜).comp
    ((BoundedContinuousFunction.evalCLM ℝ x).comp
      (TestFunction.toBoundedContinuousFunctionCLM ℝ)).toLinearMap

@[simp] theorem weightedEvaluation_apply (x : Domain d) (c : ℝ≥0) (φ : Tests 𝕜 Ω) :
    weightedEvaluation x c φ = (c : ℝ) * ‖φ x‖ := rfl

theorem weightedEvaluation_continuous (x : Domain d) (c : ℝ≥0) :
    Continuous (weightedEvaluation (𝕜 := 𝕜) (Ω := Ω) x c) :=
  continuous_const.mul ((continuous_eval_const x).norm)

/-- Pointwise eventual vanishing gives a pointwise finite supremum of seminorms. -/
theorem seminorms_bddAbove_of_eventually_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : ℕ → Seminorm ℝ V) (h : ∀ v, ∃ N, ∀ i, N ≤ i → p i v = 0) :
    BddAbove (range p) := by
  classical
  apply Seminorm.bddAbove_range_iff.mpr
  intro v
  obtain ⟨N, hN⟩ := h v
  refine ⟨∑ i ∈ Finset.range N, p i v, forall_mem_range.mpr fun i => ?_⟩
  by_cases hi : i < N
  · exact Finset.single_le_sum (fun j _ => apply_nonneg (p j) v) (Finset.mem_range.mpr hi)
  · rw [hN i (Nat.le_of_not_gt hi)]
    exact Finset.sum_nonneg fun _ _ => apply_nonneg _ _

theorem escaping_evaluations_bddAbove (e : Exhaustion Ω) (x : ℕ → Domain d)
    (hx : ∀ i, x i ∉ e.compact i) (c : ℕ → ℝ≥0) :
    BddAbove (range fun i => weightedEvaluation (𝕜 := 𝕜) (Ω := Ω) (x i) (c i)) := by
  have hm : Monotone (fun i => (e.compact i : Set (Domain d))) :=
    monotone_nat_of_le_succ fun i => (e.nested i).trans interior_subset
  apply seminorms_bddAbove_of_eventually_zero
  intro φ
  obtain ⟨N, ψ, rfl⟩ := union_steps 𝕜 d Ω e φ
  refine ⟨N, fun i hi => ?_⟩
  have hxi : x i ∉ e.compact N := fun h => hx i (hm hi h)
  change (c i : ℝ) * ‖ψ (x i)‖ = 0
  rw [ψ.zero_on_compl hxi, Pi.zero_apply, norm_zero, mul_zero]

/-- Evaluations at points escaping the exhaustion have a continuous weighted
supremum, with arbitrary nonnegative weights. -/
theorem escaping_evaluations_continuous (e : Exhaustion Ω) (x : ℕ → Domain d)
    (hx : ∀ i, x i ∉ e.compact i) (c : ℕ → ℝ≥0) :
    Continuous ((⨆ i, weightedEvaluation (𝕜 := 𝕜) (Ω := Ω) (x i) (c i)) :
      Seminorm ℝ (Tests 𝕜 Ω)) := by
  classical
  let p := fun i => weightedEvaluation (𝕜 := 𝕜) (Ω := Ω) (x i) (c i)
  have hm : Monotone (fun i => (e.compact i : Set (Domain d))) :=
    monotone_nat_of_le_succ fun i => (e.nested i).trans interior_subset
  have hz : ∀ N (φ : Step 𝕜 (e.compact N)) i, N ≤ i →
      p i (TestFunction.ofSupportedIn (e.inside N) φ) = 0 := by
    intro N φ i hi
    have hxi : x i ∉ e.compact N := fun h => hx i (hm hi h)
    change (c i : ℝ) * ‖φ (x i)‖ = 0
    rw [φ.zero_on_compl hxi, Pi.zero_apply, norm_zero, mul_zero]
  have hb : BddAbove (range p) := escaping_evaluations_bddAbove e x hx c
  apply (seminorm_criterion 𝕜 d Ω e _).mpr
  intro N
  let f := TestFunction.ofSupportedInCLM ℝ (e.inside N) (F := 𝕜) (n := ⊤)
  change Continuous (((⨆ i, p i).comp f.toLinearMap) : Step 𝕜 (e.compact N) → ℝ)
  apply Seminorm.continuous_of_le
    (q := (Finset.range N).sup fun i => (p i).comp f.toLinearMap)
    (Seminorm.continuous_finsetSup fun i _ =>
      (weightedEvaluation_continuous (x i) (c i)).comp f.continuous)
  intro φ
  change (⨆ i, p i) (f φ) ≤ _
  rw [Seminorm.iSup_apply hb]
  apply ciSup_le
  intro i
  by_cases hi : i < N
  · exact (Finset.le_sup (f := fun i => (p i).comp f.toLinearMap)
      (Finset.mem_range.mpr hi)) φ
  · change p i (TestFunction.ofSupportedIn (e.inside N) φ) ≤ _
    rw [hz N φ i (Nat.le_of_not_gt hi)]
    exact apply_nonneg _ _

/-- A bounded family cannot have supports escaping all compact exhaustion steps. -/
theorem bounded_common_support (e : Exhaustion Ω) {B : Set (Tests 𝕜 Ω)}
    (hB : Bornology.IsVonNBounded ℝ B) :
    ∃ N, ∀ φ ∈ B, tsupport φ ⊆ e.compact N := by
  classical
  by_contra h
  have hchoose : ∀ N, ∃ φ ∈ B, ∃ x, x ∉ e.compact N ∧ φ x ≠ 0 := by
    intro N
    have hN : ¬ ∀ φ ∈ B, tsupport φ ⊆ e.compact N := fun hN => h ⟨N, hN⟩
    push Not at hN
    obtain ⟨φ, hφ, hnot⟩ := hN
    have hs : ¬ Function.support φ ⊆ (e.compact N : Set (Domain d)) := by
      intro hs
      exact hnot (closure_minimal hs (e.compact N).isCompact.isClosed)
    obtain ⟨x, hx, hxN⟩ := Set.not_subset.mp hs
    exact ⟨φ, hφ, x, hxN, hx⟩
  choose φ hφ x hx hxφ using hchoose
  let c : ℕ → ℝ≥0 := fun i =>
    ⟨((i : ℝ) + 1) / ‖φ i (x i)‖, div_nonneg (by positivity) (norm_nonneg _)⟩
  let p : Seminorm ℝ (Tests 𝕜 Ω) := ⨆ i, weightedEvaluation (x i) (c i)
  have hp : Continuous p := escaping_evaluations_continuous e x hx c
  obtain ⟨C, hC⟩ := bounded_seminorm_image hB p hp
  obtain ⟨i, hi⟩ := exists_nat_gt C
  have hw : (i : ℝ) + 1 ≤ p (φ i) := by
    have hle : weightedEvaluation (x i) (c i) ≤ p :=
      le_ciSup (f := fun j => weightedEvaluation (𝕜 := 𝕜) (Ω := Ω) (x j) (c j))
        (escaping_evaluations_bddAbove (𝕜 := 𝕜) e x hx c) i
    have hle' := hle (φ i)
    change (c i : ℝ) * ‖φ i (x i)‖ ≤ p (φ i) at hle'
    change ((i : ℝ) + 1) / ‖φ i (x i)‖ * ‖φ i (x i)‖ ≤ p (φ i) at hle'
    rwa [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hxφ i))] at hle'
  have : (i : ℝ) < C :=
    (lt_add_one (i : ℝ)).trans_le (hw.trans (hC (mem_image_of_mem p (hφ i))))
  exact (hi.trans this).false

/-- The embedding reflects boundedness; here this is recorded as bounds on
the precise partial-derivative seminorms used in the manuscript. -/
theorem bounded_step_seminorms (K : Compacts (Domain d))
    (hK : (K : Set (Domain d)) ⊆ Ω) {B : Set (Tests 𝕜 Ω)}
    (hB : Bornology.IsVonNBounded ℝ B) (m : ℕ) :
    BddAbove (stepSeminorm 𝕜 K m '' (TestFunction.ofSupportedIn hK ⁻¹' B)) := by
  let f := TestFunction.ofSupportedInCLM ℝ hK (F := 𝕜) (n := ⊤)
  let p := (stepSeminorm 𝕜 K m).restrictScalars ℝ
  have hp : Continuous p := (step_seminorm_topology 𝕜 d K).continuous_seminorm m
  obtain ⟨q, hq, hpq⟩ := Seminorm.exists_le_comp_of_isInducing hp
    (f := f.toLinearMap) (step_embedding (𝕜 := 𝕜) K hK).isInducing
  obtain ⟨C, hC⟩ := bounded_seminorm_image hB q hq
  refine ⟨C, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  exact (hpq φ).trans (hC (mem_image_of_mem q hφ))

theorem bounded_criterion :
    Specs.ExpandedFA.Distributions.TestFunctionBoundedSets.boundedCriterionType := by
  intro 𝕜 _ d Ω B
  constructor
  · intro hB
    have hB : Bornology.IsVonNBounded ℝ B := hB.restrict_scalars ℝ
    obtain ⟨e⟩ := exists_exhaustion d Ω
    obtain ⟨N, hN⟩ := bounded_common_support e hB
    refine ⟨e.compact N, e.inside N, TestFunction.ofSupportedIn (e.inside N) ⁻¹' B, ?_,
      bounded_step_seminorms _ _ hB⟩
    apply Subset.antisymm
    · intro φ hφ
      let ψ : Step 𝕜 (e.compact N) :=
        ContDiffMapSupportedIn.of_support_subset φ.contDiff (subset_closure.trans (hN φ hφ))
      exact ⟨ψ, hφ, rfl⟩
    · exact image_preimage_subset _ _
  · rintro ⟨K, hK, S, rfl, hS⟩
    have hS' : Bornology.IsVonNBounded 𝕜 S :=
      (step_seminorm_topology 𝕜 d K).isVonNBounded_iff_seminorm_bddAbove.mpr hS
    exact hS'.image (TestFunction.ofSupportedInCLM 𝕜 hK)

/-- On a compact step, seminorm convergence is exactly uniform convergence
of every coordinate partial derivative. -/
theorem step_tendsto_iff_uniform_partials (K : Compacts (Domain d)) (v : ℕ → Step 𝕜 K) :
    Tendsto v atTop (𝓝 0) ↔
      ∀ k (a : Fin k → Fin d) (ε : ℝ), 0 < ε →
        ∀ᶠ n in atTop, ∀ x ∈ (K : Set (Domain d)),
          ‖iteratedFDeriv ℝ k (v n) x (fun j => coordinateVector (a j))‖ < ε := by
  classical
  constructor
  · intro hv k a ε hε
    have hp : Tendsto (fun n => stepSeminorm 𝕜 K k (v n)) atTop (𝓝 0) := by
      simpa only [map_zero, Function.comp_def] using
        ((step_seminorm_topology 𝕜 d K).continuous_seminorm k).continuousAt.tendsto.comp hv
    filter_upwards [hp.eventually_lt_const hε] with n hn x _
    exact ((step_seminorm_formula 𝕜 d K k (v n) _ (apply_nonneg _ _)).mp le_rfl
      k le_rfl a x).trans_lt hn
  · intro hv
    apply ((step_seminorm_topology 𝕜 d K).tendsto_nhds v 0).mpr
    intro m ε hε
    have he : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (m + 1),
        ∀ a : Fin k → Fin d, ∀ x ∈ (K : Set (Domain d)),
          ‖iteratedFDeriv ℝ k (v n) x (fun j => coordinateVector (a j))‖ < ε / 2 :=
      (Finset.range (m + 1)).eventually_all.mpr fun k _ =>
        Filter.eventually_all.mpr fun a => hv k a (ε / 2) (half_pos hε)
    filter_upwards [he] with n hn
    rw [sub_zero]
    apply lt_of_le_of_lt _ (half_lt_self hε)
    apply (step_seminorm_formula 𝕜 d K m (v n) (ε / 2) (half_pos hε).le).mpr
    intro k hk a x
    by_cases hx : x ∈ K
    · exact (hn k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) a x hx).le
    · rw [(v n).iteratedFDeriv_zero_on_compl hx]
      simpa using (half_pos hε).le

theorem sequence_criterion :
    Specs.ExpandedFA.Distributions.TestFunctionBoundedSets.sequenceCriterionType := by
  intro 𝕜 _ d Ω u
  constructor
  · intro hu
    obtain ⟨e⟩ := exists_exhaustion d Ω
    obtain ⟨N, hN⟩ := bounded_common_support e (hu.isVonNBounded_range ℝ)
    have hs : ∀ n, tsupport (u n) ⊆ e.compact N := fun n => hN _ (mem_range_self n)
    let v : ℕ → Step 𝕜 (e.compact N) := fun n =>
      ContDiffMapSupportedIn.of_support_subset (u n).contDiff (subset_closure.trans (hs n))
    have hv : Tendsto v atTop (𝓝 0) := by
      apply (step_embedding (𝕜 := 𝕜) (e.compact N) (e.inside N)).isInducing.tendsto_nhds_iff.mpr
      exact hu
    exact ⟨e.compact N, e.inside N, hs, (step_tendsto_iff_uniform_partials _ v).mp hv⟩
  · rintro ⟨K, hK, hs, hder⟩
    let v : ℕ → Step 𝕜 K := fun n =>
      ContDiffMapSupportedIn.of_support_subset (u n).contDiff (subset_closure.trans (hs n))
    have hv : Tendsto v atTop (𝓝 0) := (step_tendsto_iff_uniform_partials K v).mpr hder
    exact (TestFunction.continuous_ofSupportedIn hK).continuousAt.tendsto.comp hv

/-- The image of the full derivative map is closed: uniform limits of all
derivatives form a compatible Taylor series, and retain the prescribed support. -/
theorem step_derivative_range_closed (K : Compacts (Domain d)) :
    IsClosed (range (ContinuousLinearMap.pi
      (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤) :
        Step 𝕜 K →L[𝕜] ∀ k, Domain d →ᵇ ((Domain d) [×k]→L[ℝ] 𝕜))) := by
  classical
  let : ∀ k : ℕ, SeminormedAddCommGroup ((Domain d) [×k]→L[ℝ] 𝕜) := fun _ => inferInstance
  let : ∀ k : ℕ, MetricSpace ((Domain d) [×k]→L[ℝ] 𝕜) := fun _ => inferInstance
  let J := (ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤) :
    Step 𝕜 K →L[𝕜] ∀ k, Domain d →ᵇ ((Domain d) [×k]→L[ℝ] 𝕜))
  change IsClosed (range J)
  apply IsSeqClosed.isClosed
  intro u g hu hug
  choose v hv using hu
  have hconv : Tendsto (fun n => J (v n)) atTop (𝓝 g) := by
    simpa only [hv] using hug
  have hlim : ∀ k, TendstoUniformly (fun n => iteratedFDeriv ℝ k (v n)) (g k) atTop := by
    intro k
    have hk := (tendsto_pi_nhds.mp hconv) k
    have hk' := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hk
    simpa only [J, ContinuousLinearMap.pi_apply,
      ContDiffMapSupportedIn.structureMapCLM_top_apply] using hk'
  let f : Domain d → 𝕜 := fun x => (g 0 x).curry0
  let p : Domain d → FormalMultilinearSeries ℝ (Domain d) 𝕜 := fun x k => g k x
  have hjet : HasFTaylorSeriesUpTo (⊤ : ℕ∞) f p := by
    refine ⟨fun _ => rfl, ?_, fun m _ => (g m).continuous⟩
    intro m _ x
    have hd : ∀ n x, HasFDerivAt (iteratedFDeriv ℝ m (v n))
        ((iteratedFDeriv ℝ (m + 1) (v n) x).curryLeft) x := by
      intro n x
      have h := ((v n).contDiff.differentiable_iteratedFDeriv
        (m := m) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))).differentiableAt (x := x)
      convert h.hasFDerivAt using 1
      exact (congrFun (fderiv_iteratedFDeriv (𝕜 := ℝ) (f := (v n : Domain d → 𝕜))) x).symm
    have hc := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (m + 1) => Domain d) 𝕜).isometry.uniformContinuous.comp_tendstoUniformly
        (hlim (m + 1))
    exact hasFDerivAt_of_tendstoUniformly hc hd (fun y => (hlim m).tendsto_at y) x
  have hfK : EqOn f 0 (K : Set (Domain d))ᶜ := by
    intro x hx
    have ht : Tendsto (fun n => v n x) atTop (𝓝 (f x)) := by
      have ht := (continuousMultilinearCurryFin0 ℝ (Domain d) 𝕜).continuous.continuousAt.tendsto.comp
        ((hlim 0).tendsto_at x)
      simpa only [Function.comp_def, continuousMultilinearCurryFin0_apply,
        iteratedFDeriv_zero_apply, f, ContinuousMultilinearMap.curry0] using ht
    have hz : (fun n => v n x) = fun _ => (0 : 𝕜) := funext fun n => (v n).zero_on_compl hx
    rw [hz] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  let φ : Step 𝕜 K := ⟨f, hjet.contDiff, hfK⟩
  refine ⟨φ, ?_⟩
  funext k
  apply BoundedContinuousFunction.ext
  intro x
  change ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k φ x = g k x
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact (hjet.eq_iteratedFDeriv (by simp) x).symm

theorem step_complete :
    Specs.ExpandedFA.Distributions.TestFunctionBoundedSets.stepCompleteType := by
  intro 𝕜 _ d K
  let : ∀ k : ℕ, SeminormedAddCommGroup ((Domain d) [×k]→L[ℝ] 𝕜) := fun _ => inferInstance
  exact (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
    (𝕜 := 𝕜) (E := Domain d) (F := 𝕜) (n := ⊤) (K := K)).isUniformInducing.completeSpace
      (step_derivative_range_closed K).isComplete

end ExpandedFA.Distributions
