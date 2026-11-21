import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.StableDualSchemes
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Stable dual-consistent schemes, paper.tex:16515–16570.

Stability yields weak L² subsequences in an arbitrary complex Hilbert space and
an essential bound for every weak limit. Discrete summation by parts, exact
cellwise integration of the test derivative, and compact graph-domain consistency
give the full adjoint weak identity for every graph-continuous C¹ test.
The independent Specs retain both the subsequence and all-limit conclusions.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace ExpandedFA.Semigroups
open StableDualSchemesSpec

/-- Weak subsequence extraction in an arbitrary complex Hilbert space. Only the
closed span of the sequence is made separable. -/
theorem bounded_hilbert_subsequence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (a : ℕ → E) (B : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ B) :
    ∃ (φ : ℕ → ℕ) (z : E), StrictMono φ ∧
      ∀ f : E →L[ℂ] ℂ, Tendsto (fun n => f (a (φ n))) atTop (𝓝 (f z)) := by
  let M := (Submodule.span ℂ (Set.range a)).topologicalClosure
  have hc : IsClosed (M : Set E) := Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace M := hc.isComplete.completeSpace_coe
  have hs : TopologicalSpace.IsSeparable (M : Set E) :=
    ((Set.countable_range a).isSeparable.span (R := ℂ)).closure
  letI : TopologicalSpace.SeparableSpace M := hs.separableSpace
  let b : ℕ → M := fun n => ⟨a n, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self n))⟩
  let c : ℕ → WeakDual ℂ M := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ M (b n))
  have hb : ∀ n, c n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : M →L[ℂ] ℂ) B := by
    intro n
    change dist (InnerProductSpace.toDual ℂ M (b n)) 0 ≤ B
    rw [dist_zero_right, LinearIsometryEquiv.norm_map]
    exact ha n
  obtain ⟨ξ, _, φ, hφ, hconv⟩ :=
    (WeakDual.isSeqCompact_closedBall (𝕜 := ℂ) (E := M) 0 B) hb
  let z : M := (InnerProductSpace.toDual ℂ M).symm ξ.toStrongDual
  refine ⟨φ, z, hφ, ?_⟩
  intro f
  let g : M →L[ℂ] ℂ := f.comp M.subtypeL
  let y : M := (InnerProductSpace.toDual ℂ M).symm g
  have ht := ((WeakDual.eval_continuous (𝕜 := ℂ) y).tendsto ξ).comp hconv
  change Tendsto (fun n => inner ℂ (b (φ n)) y) atTop (𝓝 (ξ y)) at ht
  have hz : ξ y = inner ℂ z y := (InnerProductSpace.toDual_symm_apply).symm
  rw [hz] at ht
  have ht' := (Complex.continuous_conj.tendsto _).comp ht
  have hval (v : M) : inner ℂ y v = f (v : E) :=
    InnerProductSpace.toDual_symm_apply
  simpa only [Function.comp_def, inner_conj_symm, hval] using ht'

/-- Each raw orbit is strongly measurable, even in a nonseparable Hilbert space. -/
theorem step_stronglyMeasurable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) (h : ℝ) :
    StronglyMeasurable (step C x h) := by
  exact (StronglyMeasurable.of_discrete (f := fun n : ℕ => (C h ^ n) x)).comp_measurable
    (Nat.measurable_floor.comp (measurable_id.div_const h))

/-- The stability bound controls the value at every time in the finite interval. -/
theorem step_norm_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) {T h B : ℝ} (hh : 0 < h)
    (hB : ∀ n : ℕ, (n : ℝ) * h ≤ T → ‖C h ^ n‖ ≤ B)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : ‖step C x h t‖ ≤ B * ‖x‖ := by
  have hn : (⌊t / h⌋₊ : ℝ) * h ≤ T :=
    (mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg ht.1 hh.le)) hh.le).trans
      (by simpa only [div_mul_cancel₀ _ hh.ne'] using ht.2)
  exact ((C h ^ ⌊t / h⌋₊).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hB _ hn) (norm_nonneg x))

/-- Raw step functions have finite range on every bounded time interval. -/
theorem step_memLp : StepMembershipExpected := by
  intro H _ _ _ C x T h hh
  have hm := step_stronglyMeasurable C x h
  let N := ⌊max T 0 / h⌋₊
  let B := ∑ n ∈ Finset.range (N + 1), ‖(C h ^ n) x‖
  apply MemLp.of_bound hm.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hn : ⌊t / h⌋₊ ≤ N := Nat.floor_mono
    (div_le_div_of_nonneg_right (ht.2.le.trans (le_max_left T 0)) hh.le)
  change ‖(C h ^ ⌊t / h⌋₊) x‖ ≤ B
  exact Finset.single_le_sum (fun n _ => norm_nonneg ((C h ^ n) x))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

theorem stepL2_ae {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) (T : ℝ) {h : ℝ} (hh : 0 < h) :
    stepL2 C x T h =ᵐ[timeMeasure T] step C x h := by
  rw [stepL2, dite_eq_left (step_memLp C x T h hh)]
  exact MemLp.coeFn_toLp _

theorem stable_eventual_pointwise_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (hC : Stable C) (x : H) {T : ℝ} (hT : 0 ≤ T)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ᵐ t ∂timeMeasure T, ‖stepL2 C x T (h n) t‖ ≤ B := by
  obtain ⟨B, hB, hpow⟩ := hC (T + 1) (add_pos_of_nonneg_of_pos hT zero_lt_one)
  have hl : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hh⟩
  refine ⟨B * ‖x‖, mul_nonneg hB (norm_nonneg _), ?_⟩
  filter_upwards [hl.eventually hpow] with n hn
  filter_upwards [stepL2_ae C x T (hh n), ae_restrict_mem measurableSet_Ioo] with t ht htT
  rw [ht]
  exact step_norm_le C x (hh n)
    (fun k hk => hn k (hk.trans (le_add_of_nonneg_right zero_le_one)))
    ⟨htT.1.le, htT.2.le⟩

/-- Compactness uses only stability; closedness and consistency enter later. -/
theorem stable_weak_subsequence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (hC : Stable C) (x : H) {T : ℝ} (hT : 0 ≤ T)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (u : TimeL2 H T), StrictMono φ ∧
      WeaklyConverges (fun n => stepL2 C x T (h (φ n))) u := by
  obtain ⟨B, hB, hbound⟩ := stable_eventual_pointwise_bound C hC x hT h hh hlim
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  obtain ⟨φ, u, hφ, hu⟩ := bounded_hilbert_subsequence
    (fun n => stepL2 C x T (h (N + n)))
    (measureUnivNNReal (timeMeasure T) ^ (2 : ℝ≥0∞).toReal⁻¹ * B)
    (fun n => Lp.norm_le_of_ae_bound hB (hN _ (Nat.le_add_right N n)))
  exact ⟨fun n => N + φ n, u, hφ.const_add N, hu⟩

theorem stable_dual_subsequence : SubsequenceExpected := by
  intro H _ _ _ G C _hclosed _hdense _hadjdense hstable _hconsistent x T hT h hh hlim
  exact stable_weak_subsequence C hstable x hT h hh hlim

/-- A uniform a.e. bound is preserved by weak convergence in L². This uses
closed convexity, not pointwise convergence of the weakly convergent sequence. -/
theorem ae_norm_bound_of_weak_tendsto {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (μ : Measure α)
    (a : ℕ → Lp E 2 μ) (u : Lp E 2 μ) (B : ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ᵐ t ∂μ, ‖a n t‖ ≤ B)
    (hweak : ∀ f : Lp E 2 μ →L[ℂ] ℂ,
      Tendsto (fun n => f (a n)) atTop (𝓝 (f u))) :
    ∀ᵐ t ∂μ, ‖u t‖ ≤ B := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let S : Set (Lp E 2 μ) := {v | ∀ᵐ t ∂μ, ‖v t‖ ≤ B}
  have hconvex : Convex ℝ S := by
    intro v hv w hw a b ha hb hab
    filter_upwards [hv, hw, Lp.coeFn_add (a • v) (b • w),
      Lp.coeFn_smul a v, Lp.coeFn_smul b w] with t ht hwt hadd hav hbw
    simp only [hadd, Pi.add_apply, hav, hbw, Pi.smul_apply]
    calc
      ‖a • v t + b • w t‖ ≤ ‖a • v t‖ + ‖b • w t‖ := norm_add_le _ _
      _ = a * ‖v t‖ + b * ‖w t‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * B + b * B := add_le_add
        (mul_le_mul_of_nonneg_left ht ha) (mul_le_mul_of_nonneg_left hwt hb)
      _ = B := by rw [← add_mul, hab, one_mul]
  have hclosed : IsClosed S := by
    apply isSeqClosed_iff_isClosed.mp
    intro v z hv hz
    obtain ⟨φ, _, ht⟩ := (tendstoInMeasure_of_tendsto_Lp hz).exists_seq_tendsto_ae
    have hv' : ∀ᵐ t ∂μ, ∀ n : ℕ, ‖v (φ n) t‖ ≤ B :=
      ae_all_iff.mpr (fun n => hv (φ n))
    filter_upwards [ht, hv'] with t ht hvt
    exact le_of_tendsto ht.norm (Eventually.of_forall hvt)
  have hwclosed : IsClosed (toWeakSpace ℂ (Lp E 2 μ) '' S) := by
    have heq := hconvex.toWeakSpace_closure ℂ
    rw [hclosed.closure_eq] at heq
    rw [heq]
    exact isClosed_closure
  have hwt : Tendsto (fun n => toWeakSpace ℂ (Lp E 2 μ) (a n)) atTop
      (𝓝 (toWeakSpace ℂ (Lp E 2 μ) u)) := by
    apply (WeakBilin.tendsto_iff_forall_eval_tendsto _
      (separatingDual_iff_injective.mp inferInstance)).mpr
    exact hweak
  obtain ⟨z, hz, hzu⟩ := hwclosed.mem_of_tendsto hwt
    (hbound.mono fun n hn => ⟨a n, hn, rfl⟩)
  exact (toWeakSpace ℂ (Lp E 2 μ)).injective hzu ▸ hz

theorem stable_weak_limit_memLp_top {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (hC : Stable C) (x : H) {T : ℝ} (hT : 0 ≤ T)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0))
    (u : TimeL2 H T) (hu : WeaklyConverges (fun n => stepL2 C x T (h n)) u) :
    MemLp (fun t => u t) ∞ (timeMeasure T) := by
  obtain ⟨B, _, hbound⟩ := stable_eventual_pointwise_bound C hC x hT h hh hlim
  exact memLp_top_of_bound (Lp.aestronglyMeasurable u) B
    (ae_norm_bound_of_weak_tendsto _ _ _ B hbound hu)

theorem stable_dual_limit_bound : LimitBoundExpected := by
  intro H _ _ _ G C _hclosed _hdense _hadjdense hstable _hconsistent x T hT h hh hlim u hu
  exact stable_weak_limit_memLp_top C hstable x hT h hh hlim u hu

/-- Exact discrete Green identity, with the manuscript's conjugate-linear
first inner product and with the test evaluated at the right cell endpoint. -/
theorem discrete_summation_by_parts {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) {h : ℝ} (hh : 0 < h)
    (w : ℕ → H) (N : ℕ) :
    (h : ℂ) * ∑ n ∈ Finset.range N,
      inner ℂ ((discreteGenerator C h).adjoint (w (n + 1))) ((C h ^ n) x) =
      inner ℂ (w N) ((C h ^ N) x) - inner ℂ (w 0) x -
        ∑ n ∈ Finset.range N,
          inner ℂ (w (n + 1) - w n) ((C h ^ n) x) := by
  have hinc (n : ℕ) :
      (h : ℂ) * inner ℂ ((discreteGenerator C h).adjoint (w (n + 1)))
          ((C h ^ n) x) =
        inner ℂ (w (n + 1)) ((C h ^ (n + 1)) x) -
          inner ℂ (w (n + 1)) ((C h ^ n) x) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [← inner_smul_right]
    have hreal : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
    simp only [discreteGenerator, smul_apply, smul_smul,
      mul_inv_cancel₀ hreal, one_smul, sub_apply,
      ContinuousLinearMap.id_apply, inner_sub_right]
    congr 2
    rw [pow_succ']
    rfl
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, hinc N, Finset.sum_range_succ]
    rw [inner_sub_left]
    abel

/-- Strong convergence of operators on a Banach space is uniform on every
compact subset, with no separability hypothesis. -/
theorem strong_tendsto_uniformlyOn_compact {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : ℕ → E →L[ℂ] F) (L : E →L[ℂ] F)
    (hA : ∀ y, Tendsto (fun n => A n y) atTop (𝓝 (L y)))
    {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n y => A n y) L atTop K := by
  obtain ⟨B, hB⟩ := banach_steinhaus (g := A) (fun y => by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (hA y))
    exact ⟨R, fun n => hR _ (Set.mem_range_self n)⟩)
  let b : NNReal := ⟨max B 0, le_max_right _ _⟩
  have hLip : ∀ n, LipschitzWith b (fun y : K => A n y) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro y z
    change dist (A n (y : E)) (A n (z : E)) ≤ (b : ℝ) * dist (y : E) (z : E)
    rw [dist_eq_norm, dist_eq_norm, ← (A n).map_sub]
    exact ((A n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((hB n).trans (le_max_left B 0)) (norm_nonneg _))
  have hEq := (LipschitzWith.uniformEquicontinuous
    (fun n (y : K) => A n y) b hLip).equicontinuous
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have ht := (hEq.tendsto_uniformFun_iff_pi atTop (fun y : K => L y)).mpr
    (tendsto_pi_nhds.mpr fun y => hA y)
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp ht)

/-- The graph-norm domain maps continuously to the graph in the ordinary
product norm. The latter is a closed Banach subspace when the operator is closed. -/
def graphDomainToGraph {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : Unbounded.Operator ℂ H H) :
    Unbounded.GraphDomain A →L[ℂ] A.graph :=
  let f : Unbounded.GraphDomain A →ₗ[ℂ] A.graph :=
    { toFun := fun y => ⟨((Unbounded.GraphDomain.toDomain A y : H),
        A (Unbounded.GraphDomain.toDomain A y)),
        A.mem_graph_iff.mpr ⟨Unbounded.GraphDomain.toDomain A y, rfl, rfl⟩⟩
      map_add' := fun y z => by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact A.map_add _ _
      map_smul' := fun c y => by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact A.map_smul _ _ }
  f.mkContinuous 1 (fun y => by
    change max ‖(Unbounded.GraphDomain.toDomain A y : H)‖
      ‖A (Unbounded.GraphDomain.toDomain A y)‖ ≤ 1 * ‖y‖
    rw [one_mul, Unbounded.GraphDomain.norm_eq]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _)))

/-- Pointwise dual consistency gives uniform consistency on compact sets in
the actual graph norm. Completeness is taken on the closed graph itself. -/
theorem dual_consistency_uniform_on_compact {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : Unbounded.Operator ℂ H H) (hG : Dense (G.domain : Set H))
    (C : ℝ → H →L[ℂ] H) (hC : DualConsistent G C)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0))
    {K : Set (Unbounded.GraphDomain (Unbounded.HilbertAdjointSpec.adjointValue G))}
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n y => (discreteGenerator C (h n)).adjoint
        (Unbounded.GraphDomain.toDomain _ y : H))
      (fun y => Unbounded.HilbertAdjointSpec.adjointValue G
        (Unbounded.GraphDomain.toDomain _ y)) atTop K := by
  let A := Unbounded.HilbertAdjointSpec.adjointValue G
  have hclosed : _root_.IsClosed (A.graph : Set (H × H)) :=
    Unbounded.hilbertAdjoint_isClosed G hG
  letI : CompleteSpace A.graph := hclosed.isComplete.completeSpace_coe
  let p : A.graph →L[ℂ] H :=
    (ContinuousLinearMap.fst ℂ H H).comp A.graph.subtypeL
  let q : A.graph →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H).comp A.graph.subtypeL
  let F : ℕ → A.graph →L[ℂ] H := fun n => (discreteGenerator C (h n)).adjoint.comp p
  have hl : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hh⟩
  have hF : ∀ y, Tendsto (fun n => F n y) atTop (𝓝 (q y)) := by
    intro y
    obtain ⟨z, hz, hAz⟩ := A.mem_graph_iff.mp y.2
    change Tendsto (fun n => (discreteGenerator C (h n)).adjoint y.1.1) atTop (𝓝 y.1.2)
    rw [← hz, ← hAz]
    exact (hC z).comp hl
  have hu := strong_tendsto_uniformlyOn_compact F q hF
    (hK.image (graphDomainToGraph A).continuous)
  exact (hu.comp (graphDomainToGraph A)).mono (Set.subset_preimage_image _ _)

theorem continuousOn_interval_memLp {E : Type*} [NormedAddCommGroup E]
    {v : ℝ → E} {T : ℝ} (hv : ContinuousOn v (Set.Icc 0 T)) :
    MemLp v 2 (timeMeasure T) := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp
    (isCompact_Icc.image_of_continuousOn hv).isBounded
  apply MemLp.of_bound
    (hv.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_Ioo
      Set.Ioo_subset_Icc_self) B
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hB _ ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩

/-- The integral pairing with a fixed L² test is a bounded linear functional. -/
theorem weak_integral_pairing_tendsto {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (μ : Measure α) (a : ℕ → Lp E 2 μ) (u : Lp E 2 μ)
    (hweak : ∀ f : Lp E 2 μ →L[ℂ] ℂ,
      Tendsto (fun n => f (a n)) atTop (𝓝 (f u)))
    {v : α → E} (hv : MemLp v 2 μ) :
    Tendsto (fun n => ∫ t, inner ℂ (v t) (a n t) ∂μ) atTop
      (𝓝 (∫ t, inner ℂ (v t) (u t) ∂μ)) := by
  have heq (z : Lp E 2 μ) :
      inner ℂ (hv.toLp v) z = ∫ t, inner ℂ (v t) (z t) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with t ht
    rw [ht]
  have ht := hweak (innerSL ℂ (hv.toLp v))
  change Tendsto (fun n => inner ℂ (hv.toLp v) (a n)) atTop
    (𝓝 (inner ℂ (hv.toLp v) u)) at ht
  simpa only [heq] using ht

/-- On the interior of a grid cell the floor is exactly its grid index. -/
theorem step_eq_on_cell {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) {h : ℝ} (hh : 0 < h) (n : ℕ)
    {t : ℝ} (ht : t ∈ Set.Ioo ((n : ℝ) * h) ((n + 1 : ℕ) * h)) :
    step C x h t = (C h ^ n) x := by
  have hfloor : ⌊t / h⌋₊ = n := by
    apply (Nat.floor_eq_iff (div_nonneg
      ((mul_nonneg (Nat.cast_nonneg n) hh.le).trans ht.1.le) hh.le)).mpr
    constructor
    · exact (le_div_iff₀ hh).mpr ht.1.le
    · simpa only [Nat.cast_add, Nat.cast_one] using (div_lt_iff₀ hh).mpr ht.2
  simp only [step, hfloor]

/-- Cellwise integration of the C¹ test derivative is exact. This avoids
introducing a separate finite-difference approximation to w'. -/
theorem integral_test_derivative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {w w' : ℝ → H} {T a b : ℝ} (hw : ContinuousOn w (Set.Icc 0 T))
    (hw' : ContinuousOn w' (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt w (w' t) (Set.Icc 0 T) t)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (y : H) :
    (∫ t in a..b, inner ℂ (w' t) y) = inner ℂ (w b - w a) y := by
  have hsub : Set.Icc a b ⊆ Set.Icc 0 T :=
    fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hcont : ContinuousOn (fun t => inner ℂ (w t) y) (Set.Icc a b) :=
    (hw.mono hsub).inner continuousOn_const
  have hint : IntervalIntegrable (fun t => inner ℂ (w' t) y) volume a b :=
    ((hw'.mono hsub).inner continuousOn_const).intervalIntegrable_of_Icc hab
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun t => inner ℂ (w t) y) (inner ℂ (w' t) y) t := by
    intro t ht
    have hwderiv := (hd t (hsub ⟨ht.1.le, ht.2.le⟩)).hasDerivAt
      (Icc_mem_nhds (ha.trans_lt ht.1) (ht.2.trans_le hb))
    simpa only [inner_zero_right, zero_add] using
      hwderiv.inner ℂ (hasDerivAt_const t y)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint,
    inner_sub_left]

/-- The two raw L² representatives have an integrable inner product. -/
theorem integrable_inner_of_memLp_two {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure α}
    {f g : α → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => inner ℂ (f t) (g t)) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t ht hgt
  rw [ht, hgt]

/-- The derivative part of the discrete weak identity is an exact integral,
including the final partial cell; its boundary contribution cancels w(Nh). -/
theorem discrete_test_integral_identity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) {h T : ℝ} (hh : 0 < h) (hT : 0 ≤ T)
    {w w' : ℝ → H} (hw : ContinuousOn w (Set.Icc 0 T))
    (hw' : ContinuousOn w' (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt w (w' t) (Set.Icc 0 T) t)
    (hend : w T = 0) :
    (∫ t in 0..T, inner ℂ (w' t) (step C x h t)) + inner ℂ (w 0) x +
      (h : ℂ) * ∑ n ∈ Finset.range ⌊T / h⌋₊,
        inner ℂ ((discreteGenerator C h).adjoint (w ((n + 1 : ℕ) * h)))
          ((C h ^ n) x) = 0 := by
  let N := ⌊T / h⌋₊
  have hNh : (N : ℝ) * h ≤ T :=
    (mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hT hh.le)) hh.le).trans_eq
      (div_mul_cancel₀ T hh.ne')
  have hTnext : T < (N + 1 : ℕ) * h := by
    have ht := Nat.lt_floor_add_one (T / h)
    exact (div_lt_iff₀ hh).mp (by simpa only [Nat.cast_add, Nat.cast_one] using ht)
  have h0Nh : 0 ≤ (N : ℝ) * h := mul_nonneg (Nat.cast_nonneg N) hh.le
  have hint : IntervalIntegrable (fun t => inner ℂ (w' t) (step C x h t)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr
      (integrable_inner_of_memLp_two (continuousOn_interval_memLp hw')
        (step_memLp C x T h hh))
  have hcell (n : ℕ) (hn : n < N) :
      (∫ t in (n : ℝ) * h..(n + 1 : ℕ) * h, inner ℂ (w' t) (step C x h t)) =
        inner ℂ (w ((n + 1 : ℕ) * h) - w ((n : ℝ) * h)) ((C h ^ n) x) := by
    have hle : (n : ℝ) * h ≤ (n + 1 : ℕ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hh.le
    have hnT : (n + 1 : ℕ) * h ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hn) hh.le).trans hNh
    rw [intervalIntegral.integral_congr_Ioo_of_le hle
      (g := fun t => inner ℂ (w' t) ((C h ^ n) x))
      (fun t ht => by rw [step_eq_on_cell C x hh n ht])]
    exact integral_test_derivative hw hw' hd
      (mul_nonneg (Nat.cast_nonneg n) hh.le) hle hnT _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ) * h) (n := N) (fun n hn => hint.mono_set (by
      have hnle : (n + 1 : ℕ) * h ≤ T :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hn) hh.le).trans hNh
      have hle : (n : ℝ) * h ≤ (n + 1 : ℕ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hh.le
      rw [Set.uIcc_of_le hT, Set.uIcc_of_le hle]
      exact Set.Icc_subset_Icc (mul_nonneg (Nat.cast_nonneg n) hh.le) hnle))
  simp only [Nat.cast_zero, zero_mul] at hsum
  have hsum' :
      (∫ t in 0..(N : ℝ) * h, inner ℂ (w' t) (step C x h t)) =
        ∑ n ∈ Finset.range N,
          inner ℂ (w ((n + 1 : ℕ) * h) - w ((n : ℝ) * h)) ((C h ^ n) x) := by
    rw [← hsum]
    exact Finset.sum_congr rfl (fun n hn => hcell n (Finset.mem_range.mp hn))
  have htail :
      (∫ t in (N : ℝ) * h..T, inner ℂ (w' t) (step C x h t)) =
        -inner ℂ (w ((N : ℝ) * h)) ((C h ^ N) x) := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hNh
      (g := fun t => inner ℂ (w' t) ((C h ^ N) x)) (fun t ht => by
        rw [step_eq_on_cell C x hh N ⟨ht.1, ht.2.trans hTnext⟩])]
    rw [integral_test_derivative hw hw' hd h0Nh hNh le_rfl _, hend,
      zero_sub, inner_neg_left]
  have hint1 : IntervalIntegrable (fun t => inner ℂ (w' t) (step C x h t))
      volume 0 ((N : ℝ) * h) := hint.mono_set (by
    rw [Set.uIcc_of_le hT, Set.uIcc_of_le h0Nh]
    exact Set.Icc_subset_Icc le_rfl hNh)
  have hint2 : IntervalIntegrable (fun t => inner ℂ (w' t) (step C x h t))
      volume ((N : ℝ) * h) T := hint.mono_set (by
    rw [Set.uIcc_of_le hT, Set.uIcc_of_le hNh]
    exact Set.Icc_subset_Icc h0Nh le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  rw [← hsplit, hsum', htail]
  have hparts := discrete_summation_by_parts C x hh (fun n => w ((n : ℝ) * h)) N
  simp only [Nat.cast_zero, zero_mul] at hparts
  rw [hparts]
  abel

/-- Quantitative comparison of a grid pairing with its time integral. The
uncovered final cell has length less than h. -/
theorem grid_pairing_error_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) {h T B Q ε : ℝ}
    (hh : 0 < h) (hT : 0 ≤ T) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (horbit : ∀ n : ℕ, (n : ℝ) * h ≤ T → ‖(C h ^ n) x‖ ≤ B)
    {v : ℝ → H} (hv : ContinuousOn v (Set.Icc 0 T))
    (hvB : ∀ t ∈ Set.Icc 0 T, ‖v t‖ ≤ Q) (z : ℕ → H)
    (hclose : ∀ n < ⌊T / h⌋₊, ∀ t ∈ Set.Icc ((n : ℝ) * h) ((n + 1 : ℕ) * h),
      ‖v t - z n‖ ≤ ε) :
    ‖(∫ t in 0..T, inner ℂ (v t) (step C x h t)) -
      (h : ℂ) * ∑ n ∈ Finset.range ⌊T / h⌋₊, inner ℂ (z n) ((C h ^ n) x)‖ ≤
      ε * B * T + Q * B * h := by
  let N := ⌊T / h⌋₊
  have hNh : (N : ℝ) * h ≤ T :=
    (mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hT hh.le)) hh.le).trans_eq
      (div_mul_cancel₀ T hh.ne')
  have hTnext : T < (N + 1 : ℕ) * h := by
    apply (div_lt_iff₀ hh).mp
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (T / h)
  have h0Nh : 0 ≤ (N : ℝ) * h := mul_nonneg (Nat.cast_nonneg N) hh.le
  have hint : IntervalIntegrable (fun t => inner ℂ (v t) (step C x h t)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr
      (integrable_inner_of_memLp_two (continuousOn_interval_memLp hv) (step_memLp C x T h hh))
  let I : ℕ → ℂ := fun n => ∫ t in (n : ℝ) * h..(n + 1 : ℕ) * h,
    inner ℂ (v t) (step C x h t)
  have hcell (n : ℕ) (hn : n < N) :
      ‖I n - (h : ℂ) * inner ℂ (z n) ((C h ^ n) x)‖ ≤ ε * B * h := by
    have hle : (n : ℝ) * h ≤ (n + 1 : ℕ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hh.le
    have hnT : (n + 1 : ℕ) * h ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hn) hh.le).trans hNh
    have hn0 : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh.le
    have hcont : ContinuousOn (fun t => inner ℂ (v t) ((C h ^ n) x))
        (Set.Icc ((n : ℝ) * h) ((n + 1 : ℕ) * h)) :=
      (hv.mono (Set.Icc_subset_Icc hn0 hnT)).inner
      (continuousOn_const (c := (C h ^ n) x))
    have hconst : (∫ t in (n : ℝ) * h..(n + 1 : ℕ) * h,
        inner ℂ (z n) ((C h ^ n) x)) = (h : ℂ) * inner ℂ (z n) ((C h ^ n) x) := by
      rw [intervalIntegral.integral_const]
      have hlen : (n + 1 : ℕ) * h - (n : ℝ) * h = h := by
        push_cast
        ring
      rw [hlen]
      rfl
    change ‖(∫ t in (n : ℝ) * h..(n + 1 : ℕ) * h,
      inner ℂ (v t) (step C x h t)) - _‖ ≤ _
    rw [intervalIntegral.integral_congr_Ioo_of_le hle
      (g := fun t => inner ℂ (v t) ((C h ^ n) x))
      (fun t ht => by rw [step_eq_on_cell C x hh n ht]), ← hconst,
      ← intervalIntegral.integral_sub (hcont.intervalIntegrable_of_Icc hle)
        (intervalIntegrable_const (c := inner ℂ (z n) ((C h ^ n) x)))]
    simp_rw [← inner_sub_left]
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (n : ℝ) * h) (b := (n + 1 : ℕ) * h)
      (f := fun t => inner ℂ (v t - z n) ((C h ^ n) x)) (C := ε * B) (fun t ht => by
        rw [Set.uIoc_of_le hle] at ht
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (hclose n hn t ⟨ht.1.le, ht.2⟩)
            (horbit n (hle.trans hnT)) (norm_nonneg _) hε))
    have hlen : (n + 1 : ℕ) * h - (n : ℝ) * h = h := by push_cast; ring
    simpa only [hlen, abs_of_pos hh] using he
  have htail : ‖∫ t in (N : ℝ) * h..T, inner ℂ (v t) (step C x h t)‖ ≤ Q * B * h := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hNh
      (g := fun t => inner ℂ (v t) ((C h ^ N) x)) (fun t ht => by
        rw [step_eq_on_cell C x hh N ⟨ht.1, ht.2.trans hTnext⟩])]
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (N : ℝ) * h) (b := T)
      (f := fun t => inner ℂ (v t) ((C h ^ N) x)) (C := Q * B) (fun t ht => by
        rw [Set.uIoc_of_le hNh] at ht
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (hvB t ⟨h0Nh.trans ht.1.le, ht.2⟩) (horbit N hNh)
            (norm_nonneg _) hQ))
    rw [abs_of_nonneg (sub_nonneg.mpr hNh)] at he
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hQ hB)
    have : T < (N : ℝ) * h + h := by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hTnext
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using this.le)
  have hint1 : IntervalIntegrable (fun t => inner ℂ (v t) (step C x h t))
      volume 0 ((N : ℝ) * h) := hint.mono_set (by
    rw [Set.uIcc_of_le hT, Set.uIcc_of_le h0Nh]
    exact Set.Icc_subset_Icc le_rfl hNh)
  have hint2 : IntervalIntegrable (fun t => inner ℂ (v t) (step C x h t))
      volume ((N : ℝ) * h) T := hint.mono_set (by
    rw [Set.uIcc_of_le hT, Set.uIcc_of_le hNh]
    exact Set.Icc_subset_Icc h0Nh le_rfl)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ) * h) (n := N) (fun n hn => hint.mono_set (by
      have hnT : (n + 1 : ℕ) * h ≤ T :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hn) hh.le).trans hNh
      have hle : (n : ℝ) * h ≤ (n + 1 : ℕ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hh.le
      rw [Set.uIcc_of_le hT, Set.uIcc_of_le hle]
      exact Set.Icc_subset_Icc (mul_nonneg (Nat.cast_nonneg n) hh.le) hnT))
  change ∑ n ∈ Finset.range N, I n = _ at hsum
  simp only [Nat.cast_zero, zero_mul] at hsum
  have heq : (∫ t in 0..T, inner ℂ (v t) (step C x h t)) -
      (h : ℂ) * ∑ n ∈ Finset.range N, inner ℂ (z n) ((C h ^ n) x) =
      (∑ n ∈ Finset.range N, (I n - (h : ℂ) * inner ℂ (z n) ((C h ^ n) x))) +
        ∫ t in (N : ℝ) * h..T, inner ℂ (v t) (step C x h t) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
      ← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    abel
  rw [heq]
  calc
    _ ≤ ‖∑ n ∈ Finset.range N, (I n - (h : ℂ) * inner ℂ (z n) ((C h ^ n) x))‖ +
        ‖∫ t in (N : ℝ) * h..T, inner ℂ (v t) (step C x h t)‖ := norm_add_le _ _
    _ ≤ (∑ n ∈ Finset.range N, ε * B * h) + Q * B * h := by
      exact add_le_add ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun n hn => hcell n (Finset.mem_range.mp hn))) htail
    _ ≤ ε * B * T + Q * B * h := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      apply add_le_add _ le_rfl
      calc
        (N : ℝ) * (ε * B * h) = ε * B * ((N : ℝ) * h) := by ring
        _ ≤ ε * B * T := mul_le_mul_of_nonneg_left hNh (mul_nonneg hε hB)

/-- Uniformly consistent samples give the correct integral pairing, even
though the bounded orbit also varies with the step size. -/
theorem grid_pairing_error_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) {T B : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0))
    (horbit : ∀ᶠ n in atTop, ∀ k : ℕ, (k : ℝ) * h n ≤ T → ‖(C (h n) ^ k) x‖ ≤ B)
    {v : ℝ → H} (hv : ContinuousOn v (Set.Icc 0 T))
    (q : ℕ → ℝ → H) (hq : TendstoUniformlyOn q v atTop (Set.Icc 0 T)) :
    Tendsto (fun n => (∫ t in 0..T, inner ℂ (v t) (step C x (h n) t)) -
      (h n : ℂ) * ∑ k ∈ Finset.range ⌊T / h n⌋₊,
        inner ℂ (q n ((k + 1 : ℕ) * h n)) ((C (h n) ^ k) x)) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
    (isCompact_Icc.image_of_continuousOn hv).isBounded
  let Q := max R 0
  have hQ : 0 ≤ Q := le_max_right R 0
  have hvQ : ∀ t ∈ Set.Icc 0 T, ‖v t‖ ≤ Q :=
    fun t ht => (hR _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (B * T + Q * B + 1)
  have hden : 0 < B * T + Q * B + 1 := by
    nlinarith [mul_nonneg hB hT, mul_nonneg hQ hB]
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hv) (η / 2) (half_pos hη)
  have hqη := Metric.tendstoUniformlyOn_iff.mp hq (η / 2) (half_pos hη)
  have hhδ := (tendsto_order.mp hlim).2 δ hδ
  have hhη := (tendsto_order.mp hlim).2 η hη
  filter_upwards [horbit, hqη, hhδ, hhη] with n hn hqn hnδ hnη
  rw [dist_zero_right]
  have hclose : ∀ k < ⌊T / h n⌋₊,
      ∀ t ∈ Set.Icc ((k : ℝ) * h n) ((k + 1 : ℕ) * h n),
        ‖v t - q n ((k + 1 : ℕ) * h n)‖ ≤ η := by
    intro k hk t ht
    have hNh : (⌊T / h n⌋₊ : ℝ) * h n ≤ T :=
      (mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hT (hh n).le)) (hh n).le).trans_eq
        (div_mul_cancel₀ T (hh n).ne')
    have hsT : (k + 1 : ℕ) * h n ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hk) (hh n).le).trans hNh
    have hk0 : 0 ≤ (k : ℝ) * h n := mul_nonneg (Nat.cast_nonneg k) (hh n).le
    have hs0 : 0 ≤ (k + 1 : ℕ) * h n := mul_nonneg (Nat.cast_nonneg _) (hh n).le
    have hd : dist t ((k + 1 : ℕ) * h n) < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
      have hlen : (k + 1 : ℕ) * h n = (k : ℝ) * h n + h n := by push_cast; ring
      rw [hlen] at *
      linarith [ht.1]
    have h1 := hmod t ⟨hk0.trans ht.1, ht.2.trans hsT⟩
      ((k + 1 : ℕ) * h n) ⟨hs0, hsT⟩ hd
    have h2 := hqn ((k + 1 : ℕ) * h n) ⟨hs0, hsT⟩
    rw [← dist_eq_norm]
    exact (dist_triangle _ (v ((k + 1 : ℕ) * h n)) _).trans
      (by linarith)
  have he := grid_pairing_error_bound C x (hh n) hT hB hQ hη.le hn hv hvQ
    (fun k => q n ((k + 1 : ℕ) * h n)) hclose
  apply he.trans_lt
  have heq : η * (B * T + Q * B + 1) = ε := div_mul_cancel₀ ε hden.ne'
  nlinarith [mul_nonneg hQ hB, mul_le_mul_of_nonneg_left hnη.le (mul_nonneg hQ hB)]

theorem time_integral_eq_interval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} (hT : 0 ≤ T) (f : ℝ → E) :
    (∫ t, f t ∂timeMeasure T) = ∫ t in 0..T, f t := by
  rw [intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo]

theorem stepL2_pairing_eq_interval {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h)
    (v : ℝ → H) :
    (∫ t, inner ℂ (v t) (stepL2 C x T h t) ∂timeMeasure T) =
      ∫ t in 0..T, inner ℂ (v t) (step C x h t) := by
  rw [← time_integral_eq_interval hT]
  apply integral_congr_ae
  filter_upwards [stepL2_ae C x T hh] with t ht
  rw [ht]

/-- Every weak L² limit satisfies the full adjoint test identity, with the
source's graph-continuous C¹ test class and no uniqueness assumption. -/
theorem stable_dual_weak_solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : Unbounded.Operator ℂ H H) (hG : Dense (G.domain : Set H))
    (C : ℝ → H →L[ℂ] H) (hstable : Stable C) (hcons : DualConsistent G C)
    (x : H) {T : ℝ} (hT : 0 ≤ T)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0))
    (u : TimeL2 H T) (hu : WeaklyConverges (fun n => stepL2 C x T (h n)) u) :
    WeakSolution G x T u := by
  intro w w' htest
  obtain ⟨hw, hw', hd, hend⟩ := htest
  let A := Unbounded.HilbertAdjointSpec.adjointValue G
  let wH : ℝ → H := fun t => (Unbounded.GraphDomain.toDomain A (w t) : H)
  let v : ℝ → H := fun t => A (Unbounded.GraphDomain.toDomain A (w t))
  let q : ℕ → ℝ → H := fun n t => (discreteGenerator C (h n)).adjoint (wH t)
  have hwH : ContinuousOn wH (Set.Icc 0 T) :=
    (((ContinuousLinearMap.fst ℂ H H).comp A.graph.subtypeL).comp
      (graphDomainToGraph A)).continuous.comp_continuousOn hw
  have hv : ContinuousOn v (Set.Icc 0 T) :=
    (((ContinuousLinearMap.snd ℂ H H).comp A.graph.subtypeL).comp
      (graphDomainToGraph A)).continuous.comp_continuousOn hw
  have hqu : TendstoUniformlyOn q v atTop (Set.Icc 0 T) :=
    ((dual_consistency_uniform_on_compact G hG C hcons h hh hlim
      (isCompact_Icc.image_of_continuousOn hw)).comp w).mono (Set.subset_preimage_image _ _)
  obtain ⟨R, hR, hpow⟩ := hstable (T + 1) (add_pos_of_nonneg_of_pos hT zero_lt_one)
  let B := R * ‖x‖
  have hB : 0 ≤ B := mul_nonneg hR (norm_nonneg _)
  have hl : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hh⟩
  have horbit : ∀ᶠ n in atTop, ∀ k : ℕ, (k : ℝ) * h n ≤ T →
      ‖(C (h n) ^ k) x‖ ≤ B := by
    filter_upwards [hl.eventually hpow] with n hn k hk
    exact ((C (h n) ^ k).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right
        (hn k (hk.trans (le_add_of_nonneg_right zero_le_one))) (norm_nonneg x))
  have herr := grid_pairing_error_tendsto C x hT hB h hh hlim horbit hv q hqu
  have hfixed (f : ℝ → H) (hf : ContinuousOn f (Set.Icc 0 T)) :
      Tendsto (fun n => ∫ t in 0..T, inner ℂ (f t) (step C x (h n) t)) atTop
        (𝓝 (∫ t, inner ℂ (f t) (u t) ∂timeMeasure T)) := by
    have ht := weak_integral_pairing_tendsto (timeMeasure T)
      (fun n => stepL2 C x T (h n)) u hu (continuousOn_interval_memLp hf)
    exact ht.congr' (Eventually.of_forall fun n =>
      stepL2_pairing_eq_interval C x hT (hh n) f)
  have hlimit := ((hfixed w' hw').add (hfixed v hv)).add_const (inner ℂ (wH 0) x)
  have heq (n : ℕ) :
      (∫ t in 0..T, inner ℂ (w' t) (step C x (h n) t)) +
        (∫ t in 0..T, inner ℂ (v t) (step C x (h n) t)) + inner ℂ (wH 0) x =
      (∫ t in 0..T, inner ℂ (v t) (step C x (h n) t)) -
        (h n : ℂ) * ∑ k ∈ Finset.range ⌊T / h n⌋₊,
          inner ℂ (q n ((k + 1 : ℕ) * h n)) ((C (h n) ^ k) x) := by
    have hi := discrete_test_integral_identity C x (hh n) hT hwH hw' hd hend
    dsimp only [q]
    linear_combination hi
  have hzero := herr.congr' (Eventually.of_forall fun n => (heq n).symm)
  have hresult := tendsto_nhds_unique hlimit hzero
  change (∫ t, inner ℂ (w' t) (u t) + inner ℂ (v t) (u t) ∂timeMeasure T) +
    inner ℂ (wH 0) x = 0
  rw [integral_add
    (integrable_inner_of_memLp_two (continuousOn_interval_memLp hw') (Lp.memLp u))
    (integrable_inner_of_memLp_two (continuousOn_interval_memLp hv) (Lp.memLp u))]
  exact hresult

theorem stable_dual_limit : LimitExpected := by
  intro H _ _ _ G C _hclosed hdense _hadjdense hstable hcons x T hT h hh hlim u hu
  exact ⟨stable_weak_limit_memLp_top C hstable x hT h hh hlim u hu,
    stable_dual_weak_solution G hdense C hstable hcons x hT h hh hlim u hu⟩

end ExpandedFA.Semigroups
