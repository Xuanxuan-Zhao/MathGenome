import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionLimits
import Mathlib.Analysis.LocallyConvex.Barrelled

open Set TopologicalSpace Filter
open scoped Topology Distributions ContDiff NNReal BoundedContinuousFunction Uniformity

namespace ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- Finite-dimensional multilinear estimates identify the local smooth topology
with the usual coordinate-partial topology, including dimension zero. -/
theorem smooth_convergence_iff_coordinates :
    Specs.ExpandedFA.Distributions.DistributionLimits.smoothConvergenceMeaningType := by
  intro 𝕜 _ d Ω a b
  classical
  constructor
  · intro ha K hK k c ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (ha K hK k) ε hε] with j hj x hx
    calc
      _ = ‖(iteratedFDeriv ℝ k (a j).val x - iteratedFDeriv ℝ k b.val x)
          (fun i => coordinateVector (c i))‖ := rfl
      _ ≤ ‖iteratedFDeriv ℝ k (a j).val x - iteratedFDeriv ℝ k b.val x‖ *
          ∏ i, ‖coordinateVector (c i)‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ k (a j).val x - iteratedFDeriv ℝ k b.val x‖ := by
        simp [coordinateVector, Pi.norm_single]
      _ < ε := by simpa only [dist_eq_norm, norm_sub_rev] using hj x hx
  · intro ha K hK k
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    let D : ℝ := (d : ℝ) ^ k
    have hD : 0 ≤ D := by positivity
    let δ : ℝ := ε / (D + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have he : ∀ᶠ j in atTop, ∀ c : Fin k → Fin d, ∀ x ∈ (K : Set (Domain d)),
        ‖iteratedFDeriv ℝ k (a j).val x (fun i => coordinateVector (c i)) -
          iteratedFDeriv ℝ k b.val x (fun i => coordinateVector (c i))‖ < δ :=
      Filter.eventually_all.mpr fun c => ha K hK k c δ hδ
    filter_upwards [he] with j hj x hx
    rw [dist_eq_norm]
    calc
      _ ≤ D * δ := norm_multilinear_le_coordinate_bound _ δ hδ.le
        (fun c => by simpa only [sub_apply, norm_sub_rev]
          using (hj c x hx).le)
      _ < (D + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one D) hδ
      _ = ε := by rw [mul_comm]; exact div_mul_cancel₀ ε (by positivity)

/-- Banach–Steinhaus on the complete metrizable compact step, followed by
finite-seminorm domination, gives a uniform order bound. -/
theorem uniform_compact_order :
    Specs.ExpandedFA.Distributions.DistributionLimits.uniformOrderType := by
  intro 𝕜 _ d Ω u hu K hK
  let : MetrizableSpace (Step 𝕜 K) := step_metrizable K
  let : CompleteSpace (Step 𝕜 K) := step_complete 𝕜 d K
  let : (𝓤 (Step 𝕜 K)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let A : ℕ → Step 𝕜 K →L[𝕜] 𝕜 :=
    fun j => (u j).comp (TestFunction.ofSupportedInCLM 𝕜 hK)
  let p : ℕ → Seminorm 𝕜 (Step 𝕜 K) :=
    fun j => (normSeminorm 𝕜 𝕜).comp (A j).toLinearMap
  have hp : BddAbove (range p) := Seminorm.bddAbove_range_iff.mpr fun φ => hu _
  have hc : Continuous ((⨆ j, p j) : Seminorm 𝕜 (Step 𝕜 K)) := by
    rw [Seminorm.coe_iSup_eq hp]
    exact Seminorm.continuous_iSup p (fun j => (A j).continuous.norm) hp
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous (step_seminorm_topology 𝕜 d K) _ hc
  have hs : s.sup (stepSeminorm 𝕜 K) ≤ stepSeminorm 𝕜 K (s.sup id) := by
    apply Finset.sup_le
    intro m hm
    exact stepSeminorm_monotone K (Finset.le_sup (f := id) hm)
  refine ⟨C, C.coe_nonneg, s.sup id, fun j φ => ?_⟩
  have hj : p j ≤ ⨆ i, p i := le_ciSup (f := p) hp j
  exact (hj φ).trans ((hC φ).trans
    (mul_le_mul_of_nonneg_left (hs φ) C.coe_nonneg))

/-- Passing the uniform order bound to the scalar limit establishes LF continuity. -/
theorem pointwise_limit :
    Specs.ExpandedFA.Distributions.DistributionLimits.pointwiseLimitType := by
  intro 𝕜 _ d Ω u f hf
  let L : Tests 𝕜 Ω →ₗ[𝕜] 𝕜 := linearMapOfTendsto _ _ (tendsto_pi_nhds.mpr hf)
  have hu : ∀ φ : Tests 𝕜 Ω, BddAbove (range fun j => ‖u j φ‖) :=
    fun φ => (hf φ).norm.bddAbove_range
  have hcont : Continuous L := (finite_order_criterion 𝕜 d Ω L).mpr (by
    intro K hK
    obtain ⟨C, hC, m, hm⟩ := uniform_compact_order 𝕜 d Ω u hu K hK
    refine ⟨C, hC, m, fun φ => ?_⟩
    exact le_of_tendsto (hf _).norm (Eventually.of_forall fun j => hm j φ))
  exact ⟨⟨L, hcont⟩, fun _ => rfl⟩

/-- Multiplication keeps the original compact support. -/
noncomputable def coefficientMulStep (K : Compacts (Domain d))
    (hK : (K : Set (Domain d)) ⊆ Ω) (a : SmoothCoefficient 𝕜 Ω) (φ : Step 𝕜 K) :
    Step 𝕜 K :=
  ⟨fun x => a.val x * φ x,
    smooth_mul_test a (TestFunction.ofSupportedIn hK φ),
    fun x hx => by simp [φ.zero_on_compl hx]⟩

/-- A local smooth coefficient difference, without imposing conditions off Ω. -/
def coefficientSub (a b : SmoothCoefficient 𝕜 Ω) : SmoothCoefficient 𝕜 Ω :=
  ⟨a.val - b.val, a.property.sub b.property⟩

/-- The ordinary finite Leibniz estimate applies to locally smooth coefficients
at every point of Ω. Derivatives within the open set are ordinary derivatives. -/
theorem coefficient_mul_derivative_bound (a : SmoothCoefficient 𝕜 Ω)
    (φ : Tests 𝕜 Ω) (k : ℕ) {x : Domain d} (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ k (fun y => a.val y * φ y) x‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i a.val x‖ * ‖iteratedFDeriv ℝ (k - i) φ x‖ := by
  have h := norm_iteratedFDerivWithin_mul_le a.property φ.contDiff.contDiffOn
    Ω.isOpen.uniqueDiffOn hx (n := k) (by simp : (k : ℕ∞ω) ≤ ∞)
  simpa only [iteratedFDerivWithin_of_isOpen _ Ω.isOpen hx] using h

/-- C∞ local convergence of coefficients sends every fixed test to a convergent
sequence on its original compact step. -/
theorem coefficient_mul_step_tendsto (a : ℕ → SmoothCoefficient 𝕜 Ω)
    (b : SmoothCoefficient 𝕜 Ω) (ha : SmoothLocallyConverges a b)
    (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω) (φ : Step 𝕜 K) :
    Tendsto (fun j => coefficientMulStep K hK (coefficientSub (a j) b) φ)
      atTop (𝓝 0) := by
  classical
  apply (step_tendsto_iff_uniform_partials K _).mpr
  intro k c ε hε
  let D : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
    ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K (k - i) φ
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (apply_nonneg _ _)
  let δ : ℝ := ε / (D + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he (i : ℕ) : ∀ᶠ j in atTop, ∀ x ∈ (K : Set (Domain d)),
      ‖iteratedFDeriv ℝ i (coefficientSub (a j) b).val x‖ < δ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (ha K hK i) δ hδ] with j hj x hx
    change ‖iteratedFDeriv ℝ i ((a j).val - b.val) x‖ < δ
    rw [iteratedFDeriv_sub_apply
      (((a j).property x (hK hx)).contDiffAt (Ω.isOpen.mem_nhds (hK hx)) |>.of_le (by simp))
      ((b.property x (hK hx)).contDiffAt (Ω.isOpen.mem_nhds (hK hx)) |>.of_le (by simp))]
    simpa only [dist_eq_norm, norm_sub_rev] using hj x hx
  have he' := (Finset.range (k + 1)).eventually_all.mpr fun i _ => he i
  filter_upwards [he'] with j hj x hx
  let ψ := coefficientMulStep K hK (coefficientSub (a j) b) φ
  have hbound : ‖iteratedFDeriv ℝ k ψ x‖ ≤ δ * D := by
    apply (coefficient_mul_derivative_bound (coefficientSub (a j) b)
      (TestFunction.ofSupportedIn hK φ) k (hK hx)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * δ *
          ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K (k - i) φ := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hj i hi x hx).le (by positivity)
        · exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜
        · exact norm_nonneg _
        · positivity
      _ = δ * D := by simp only [D, Finset.mul_sum]; congr 1; ext i; ring
  have hlt : δ * D < ε := by
    calc
      δ * D < δ * (D + 1) := mul_lt_mul_of_pos_left (lt_add_one D) hδ
      _ = ε := div_mul_cancel₀ ε (by positivity)
  calc
    ‖iteratedFDeriv ℝ k ψ x (fun j => coordinateVector (c j))‖
      ≤ ‖iteratedFDeriv ℝ k ψ x‖ * ∏ j, ‖coordinateVector (c j)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ k ψ x‖ := by simp [coordinateVector, Pi.norm_single]
    _ < ε := hbound.trans_lt hlt

/-- A pointwise bounded sequence can be tested on a null sequence in a single
compact step. The order bound used here is derived, not assumed. -/
theorem tendsto_apply_compact_null (u : ℕ → ScalarDistribution 𝕜 Ω)
    (hu : ∀ φ : Tests 𝕜 Ω, BddAbove (range fun j => ‖u j φ‖))
    (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω)
    (ψ : ℕ → Step 𝕜 K) (hψ : Tendsto ψ atTop (𝓝 0)) :
    Tendsto (fun j => u j (TestFunction.ofSupportedIn hK (ψ j))) atTop (𝓝 0) := by
  obtain ⟨C, _, m, hm⟩ := uniform_compact_order 𝕜 d Ω u hu K hK
  have hp : Tendsto (fun j => stepSeminorm 𝕜 K m (ψ j)) atTop (𝓝 0) := by
    simpa only [map_zero, Function.comp_def] using
      ((step_seminorm_topology 𝕜 d K).continuous_seminorm m).continuousAt.tendsto.comp hψ
  apply squeeze_zero_norm (fun j => hm j (ψ j))
  simpa only [mul_zero] using hp.const_mul C

/-- The actual products constructed upstream converge weakly when both the
coefficients and the distributions vary. -/
theorem multiplyDistribution_tendsto (u : ℕ → ScalarDistribution 𝕜 Ω)
    (v : ScalarDistribution 𝕜 Ω) (a : ℕ → SmoothCoefficient 𝕜 Ω)
    (b : SmoothCoefficient 𝕜 Ω) (hu : DistributionConverges u v)
    (ha : SmoothLocallyConverges a b) :
    DistributionConverges (fun j => multiplyDistribution (a j) (u j))
      (multiplyDistribution b v) := by
  intro φ
  let K : Compacts (Domain d) := ⟨tsupport φ, φ.hasCompactSupport⟩
  have hK : (K : Set (Domain d)) ⊆ Ω := φ.tsupport_subset
  let φK : Step 𝕜 K := ContDiffMapSupportedIn.of_support_subset φ.contDiff subset_closure
  let ψ : ℕ → Step 𝕜 K := fun j => coefficientMulStep K hK (coefficientSub (a j) b) φK
  have hψ : Tendsto ψ atTop (𝓝 0) := coefficient_mul_step_tendsto a b ha K hK φK
  have hz := tendsto_apply_compact_null u (fun φ => (hu φ).norm.bddAbove_range) K hK ψ hψ
  have heq (j : ℕ) :
      multiplyDistribution (a j) (u j) φ =
        u j (TestFunction.ofSupportedIn hK (ψ j)) + u j (multiplyTestCLM b φ) := by
    change u j (multiplyTestCLM (a j) φ) = _
    rw [← map_add]
    congr 1
    ext x
    change (a j).val x * φ x = ((a j).val x - b.val x) * φ x + b.val x * φ x
    ring
  have ht := hz.add (hu (multiplyTestCLM b φ))
  simpa only [← heq, zero_add, multiplyDistribution_apply] using ht

/-- The source statement, with witnesses for the products and their precise
scalar-linear pairings. -/
theorem multiplication_limit :
    Specs.ExpandedFA.Distributions.DistributionLimits.multiplicationLimitType := by
  intro 𝕜 _ d Ω u v a b hu ha
  exact ⟨fun j => multiplyDistribution (a j) (u j), multiplyDistribution b v,
    fun j φ => ⟨multiplyTestCLM (a j) φ, fun _ => rfl, rfl⟩,
    fun φ => ⟨multiplyTestCLM b φ, fun _ => rfl, rfl⟩,
    multiplyDistribution_tendsto u v a b hu ha⟩

end ExpandedFA.Distributions
