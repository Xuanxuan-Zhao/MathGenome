import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.PositiveIntegralCompletion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.Topology.MetricSpace.Isometry

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
universe u
namespace ExpandedFA.Supplements.PositiveIntegralCompletion
open PositiveIntegralCompletionSpec

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

lemma norm_continuousToL1 (f : C(K, ℝ)) :
    ‖continuousToL1 μ f‖ = ∫ x, |f x| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f] with x hx
  rw [hx, Real.norm_eq_abs]

lemma quotientMap_surjective : Function.Surjective (quotientMap μ) := by
  rintro ⟨g, f, rfl⟩
  exact ⟨f, rfl⟩

lemma embed_denseRange : DenseRange (embed μ) := by
  have hs : Function.Surjective (quotientMap μ) := quotientMap_surjective μ
  exact UniformSpace.Completion.denseRange_coe.comp hs.denseRange
    (UniformSpace.Completion.continuous_coe _)

/-- The quotient uses precisely the manuscript's integral seminorm. -/
theorem quotient_identification : QuotientIdentification.{u} := by
  intro K _ _ _ _ _ μ _ ℓ hℓ
  have hn (f : C(K, ℝ)) : ‖quotientMap μ f‖ = ℓ |f| := by
    rw [hℓ.2.2 |f|]
    exact norm_continuousToL1 μ f
  refine ⟨?_, hn, quotientMap_surjective μ⟩
  intro f g
  rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, hn]

/-- First isomorphism theorem with the exact source null space and norm. -/
theorem null_quotient_bridge : NullQuotientBridge.{u} := by
  intro K _ _ _ _ _ μ _ ℓ hℓ
  let N := LinearMap.ker (continuousToL1 μ).toLinearMap
  have hn := (quotient_identification K μ ℓ hℓ).2.1
  have hN (f : C(K, ℝ)) : f ∈ N ↔ ℓ |f| = 0 := by
    change continuousToL1 μ f = 0 ↔ _
    rw [← norm_eq_zero]
    exact congrArg (fun r : ℝ => r = 0) (hn f) |>.to_iff
  have he (f : C(K, ℝ)) :
      algebraicQuotientEquiv μ (N.mkQ f) = quotientMap μ f := by
    apply Subtype.ext
    exact (continuousToL1 μ).toLinearMap.quotKerEquivRange_apply_mk f
  exact ⟨N, hN, algebraicQuotientEquiv μ, he, fun f => by rw [he, hn]⟩

/-- The canonical quotient embedding into L¹. -/
def quotientToL1 : IntegralQuotient μ →ₗᵢ[ℝ] Lp ℝ 1 μ :=
  (continuousToL1 μ).range.subtypeₗᵢ

lemma quotientToL1_denseRange [T2Space K] [μ.WeaklyRegular] : DenseRange (quotientToL1 μ) := by
  apply (ContinuousMap.toLp_denseRange ℝ μ ℝ (by simp : (1 : ℝ≥0∞) ≠ ∞)).mono
  rintro _ ⟨f, rfl⟩
  exact ⟨quotientMap μ f, rfl⟩

/-- The extension is isometric because its dense restriction is isometric. -/
def completionMap : IntegralCompletion μ →ₗᵢ[ℝ] Lp ℝ 1 μ where
  toLinearMap := (quotientToL1 μ).toContinuousLinearMap.fromCompletion.toLinearMap
  norm_map' z := by
    have hi := (quotientToL1 μ).isometry.completion_extension
    exact hi.norm_map_of_map_zero
      ((quotientToL1 μ).toContinuousLinearMap.fromCompletion.map_zero) z

@[simp] lemma completionMap_embed (f : C(K, ℝ)) :
    completionMap μ (embed μ f) = continuousToL1 μ f := by
  exact (quotientToL1 μ).toContinuousLinearMap.fromCompletion_apply_coe (quotientMap μ f)

lemma completionMap_surjective [T2Space K] [μ.WeaklyRegular] : Function.Surjective (completionMap μ) := by
  have hd : DenseRange (completionMap μ) := by
    apply (quotientToL1_denseRange μ).mono
    rintro _ ⟨f, rfl⟩
    exact ⟨(f : IntegralCompletion μ),
      (quotientToL1 μ).toContinuousLinearMap.fromCompletion_apply_coe f⟩
  have hc : IsClosed (Set.range (completionMap μ)) :=
    (completionMap μ).isometry.isClosedEmbedding.isClosed_range
  intro y
  have hy := hd y
  rw [hc.closure_eq] at hy
  exact hy

/-- The unique canonical comparison preserves the real linear structure. -/
theorem completion_identification : CompletionIdentification.{u} := by
  intro K _ _ _ _ _ μ _ hμ
  have : μ.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ
  let e : IntegralCompletion μ ≃ₗᵢ[ℝ] Lp ℝ 1 μ := {
    toLinearEquiv := LinearEquiv.ofBijective (completionMap μ).toLinearMap
      ⟨fun a b h => (completionMap μ).isometry.injective h, completionMap_surjective μ⟩
    norm_map' := (completionMap μ).norm_map }
  refine ⟨e, completionMap_embed μ, ?_⟩
  intro e' he'
  apply LinearIsometryEquiv.ext
  exact congrFun ((embed_denseRange μ).equalizer e'.continuous e.continuous
    (funext fun f => (he' f).trans (completionMap_embed μ f).symm))

/-- Integration is continuous and restricts to the original algebraic functional. -/
theorem integration_extension : IntegrationExtension.{u} := by
  intro K _ _ _ _ _ μ _ ℓ hℓ e he
  let I : IntegralCompletion μ →L[ℝ] ℝ := L1.integralCLM.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  have hI (z : IntegralCompletion μ) : I z = ∫ x, e z x ∂μ := by
    change L1.integralCLM (e z) = _
    rw [← L1.integral_eq, L1.integral_eq_integral]
  have hIf (f : C(K, ℝ)) : I (embed μ f) = ℓ f := by
    rw [hI, he, hℓ.2.2 f]
    exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f)
  refine ⟨I, ⟨hIf, hI⟩, ?_⟩
  intro J hJ
  apply ContinuousLinearMap.ext
  exact congrFun ((embed_denseRange μ).equalizer J.continuous I.continuous
    (funext fun f => (hJ.1 f).trans (hIf f).symm))

/-- Finiteness permits an arbitrary Lipschitz scalar function, without q(0)=0. -/
lemma lipschitz_memL1 {q : ℝ → ℝ} {c : ℝ≥0} (hq : LipschitzWith c q)
    (f : Lp ℝ 1 μ) : Integrable (fun x => q (f x)) μ := by
  have hq' : LipschitzWith c (fun t => q t - q 0) := by
    simpa using hq.sub (LipschitzWith.const (q 0) : LipschitzWith 0 (fun _ : ℝ => q 0))
  have hi := memLp_one_iff_integrable.mp (hq'.comp_memLp (sub_self _) (Lp.memLp f))
  convert hi.add (integrable_const (q 0) : Integrable (fun _ : K => q 0) μ) using 1
  ext x
  exact (sub_add_cancel (q (f x)) (q 0)).symm

/-- The actual a.e. pointwise Lipschitz functional calculus on L¹. -/
def scalarL1 {q : ℝ → ℝ} {c : ℝ≥0} (hq : LipschitzWith c q)
    (f : Lp ℝ 1 μ) : Lp ℝ 1 μ :=
  (lipschitz_memL1 μ hq f).toL1 (fun x => q (f x))

lemma scalarL1_ae {q : ℝ → ℝ} {c : ℝ≥0} (hq : LipschitzWith c q)
    (f : Lp ℝ 1 μ) : scalarL1 μ hq f =ᵐ[μ] fun x => q (f x) :=
  (lipschitz_memL1 μ hq f).coeFn_toL1

lemma scalarL1_lipschitz {q : ℝ → ℝ} {c : ℝ≥0} (hq : LipschitzWith c q) :
    LipschitzWith c (scalarL1 μ hq) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [dist_eq_norm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarL1_ae μ hq f, scalarL1_ae μ hq g,
    Lp.coeFn_sub (scalarL1 μ hq f) (scalarL1 μ hq g), Lp.coeFn_sub f g]
    with x hf hg hsub hfg
  simpa only [hsub, hfg, Pi.sub_apply, hf, hg] using hq.norm_sub_le (f x) (g x)

lemma scalarL1_continuousToL1 {q : ℝ → ℝ} {c : ℝ≥0} (hq : LipschitzWith c q)
    (f : C(K, ℝ)) :
    scalarL1 μ hq (continuousToL1 μ f) =
      continuousToL1 μ ((⟨q, hq.continuous⟩ : C(ℝ, ℝ)).comp f) := by
  apply Lp.ext
  filter_upwards [scalarL1_ae μ hq (continuousToL1 μ f),
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f,
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ ((⟨q, hq.continuous⟩ : C(ℝ, ℝ)).comp f)] with x hx hf hg
  simpa only [hx, hf, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using hg.symm

/-- Uniqueness of every continuous scalar operation from its action on C(K). -/
lemma calculus_unique {q : ℝ → ℝ} (hq : Continuous q)
    {T S : IntegralCompletion μ → IntegralCompletion μ}
    (hT : ExtendsCalculus μ q T) (hS : ExtendsCalculus μ q S) : T = S :=
  (embed_denseRange μ).equalizer hT.1 hS.1
    (funext fun f => (hT.2 f hq).trans (hS.2 f hq).symm)

/-- The scalar calculus is the unique continuous extension, with the original
Lipschitz constant preserved, and has precisely its pointwise meaning. -/
theorem lipschitz_calculus : LipschitzCalculus.{u} := by
  intro K _ _ _ _ _ μ _ e he q c hq
  let T : IntegralCompletion μ → IntegralCompletion μ :=
    e.symm ∘ scalarL1 μ hq ∘ e
  have hTlip : LipschitzWith c T := by
    simpa only [one_mul, mul_one] using
      e.symm.isometry.lipschitzWith.comp ((scalarL1_lipschitz μ hq).comp e.isometry.lipschitzWith)
  have hText : ExtendsCalculus μ q T := by
    refine ⟨hTlip.continuous, ?_⟩
    intro f hqc
    apply e.injective
    simp only [T, Function.comp_apply, e.apply_symm_apply, he]
    exact scalarL1_continuousToL1 μ hq f
  refine ⟨T, ⟨hText, hTlip, ?_⟩, ?_⟩
  · intro z
    simpa only [T, Function.comp_apply, e.apply_symm_apply] using scalarL1_ae μ hq (e z)
  · intro S hS
    exact calculus_unique μ hq.continuous hS.1 hText

/-- The intrinsic closed positive cone is precisely the a.e. positive cone. -/
theorem order_identification : OrderIdentification.{u} := by
  intro K _ _ _ _ _ μ _ e he
  have hforward : ∀ z, z ∈ positiveCone μ → 0 ≤ e z := by
    intro z hz
    apply closure_minimal (s := {z | ∃ f : C(K, ℝ), (∀ x, 0 ≤ f x) ∧ embed μ f = z})
      (t := {z | 0 ≤ e z}) ?_ (isClosed_le continuous_const e.continuous) hz
    rintro _ ⟨f, hf, rfl⟩
    change 0 ≤ e (embed μ f)
    rw [he, ← Lp.coeFn_nonneg]
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f] with x hx
    exact hx ▸ hf x
  have hpos : LipschitzWith 1 (fun t : ℝ => max t 0) := lipschitzWith_posPart
  obtain ⟨P, hP, _⟩ := lipschitz_calculus K μ e he (fun t => max t 0) 1 hpos
  have hPcone : ∀ z, P z ∈ positiveCone μ := by
    apply isClosed_property (embed_denseRange μ)
      (isClosed_closure.preimage hP.1.1)
    intro f
    rw [hP.1.2 f hpos.continuous]
    apply subset_closure
    refine ⟨(⟨fun t : ℝ => max t 0, hpos.continuous⟩ : C(ℝ, ℝ)).comp f, ?_, rfl⟩
    exact fun x => le_max_right _ _
  have hcone : ∀ z, z ∈ positiveCone μ ↔ ∀ᵐ x ∂μ, 0 ≤ e z x := by
    intro z
    constructor
    · exact fun hz => (Lp.coeFn_nonneg _).mpr (hforward z hz)
    · intro hz
      have hPz : P z = z := by
        apply e.injective
        apply Lp.ext
        filter_upwards [hP.2.2 z, hz] with x hx hxpos
        exact hx.trans (max_eq_left hxpos)
      simpa only [hPz] using hPcone z
  refine ⟨hcone, ?_⟩
  intro z w
  rw [completionLE, hcone]
  constructor <;> intro h
  · filter_upwards [h, Lp.coeFn_sub (e w) (e z)] with x hx hsub
    rw [e.map_sub w z, hsub, Pi.sub_apply] at hx
    exact sub_nonneg.mp hx
  · filter_upwards [h, Lp.coeFn_sub (e w) (e z)] with x hx hsub
    rw [e.map_sub w z, hsub, Pi.sub_apply]
    exact sub_nonneg.mpr hx

/-- Absolute value as a distinguished instance of scalar functional calculus. -/
theorem absolute_value : AbsoluteValue.{u} := by
  intro K _ _ _ _ _ μ _ e he
  have habs : LipschitzWith 1 (fun t : ℝ => |t|) := by
    convert (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)) using 1
  obtain ⟨A, hA, _⟩ := lipschitz_calculus K μ e he (fun t => |t|) 1 habs
  refine ⟨A, ⟨hA.1, hA.2.1, ?_⟩, ?_⟩
  · intro z
    exact Lp.ext ((hA.2.2 z).trans (Lp.coeFn_abs (e z)).symm)
  · intro B hB
    exact calculus_unique μ habs.continuous hB.1 hA.1

/-- Distances of comparable L¹ functions equal differences of their integrals. -/
lemma norm_sub_of_le {X : Type u} [MeasurableSpace X] (ν : Measure X)
    (f g : Lp ℝ 1 ν) (hfg : f ≤ g) :
    ‖g - f‖ = (∫ x, g x ∂ν) - ∫ x, f x ∂ν := by
  rw [L1.norm_eq_integral_norm, ← integral_sub (L1.integrable_coeFn g) (L1.integrable_coeFn f)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub g f, (Lp.coeFn_le f g).mpr hfg] with x hx hle
  rw [hx, Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)]

/-- Bounded increasing integral sequences are Cauchy in L¹. Completeness and
an a.e. convergent subsequence identify the limit with the pointwise supremum. -/
theorem monotone_convergence : MonotoneConvergence.{u} := by
  intro K _ μ f hf hbdd
  have hmono : Monotone f := monotone_nat_of_le_succ hf
  let a : ℕ → ℝ := fun n => ∫ x, f n x ∂μ
  have ha : Monotone a := by
    intro m n hmn
    exact integral_mono_ae (L1.integrable_coeFn _) (L1.integrable_coeFn _)
      ((Lp.coeFn_le _ _).mpr (hmono hmn))
  have hdist : ∀ n m, dist (f n) (f m) = dist (a n) (a m) := by
    suffices H : ∀ n m, n ≤ m → dist (f n) (f m) = dist (a n) (a m) by
      intro n m
      rcases le_total n m with h | h
      · exact H n m h
      · rw [dist_comm (f n), H m n h, dist_comm]
    intro n m hnm
    rw [dist_comm, dist_eq_norm, norm_sub_of_le μ _ _ (hmono hnm),
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (ha hnm))]
    exact (neg_sub (a n) (a m)).symm
  have hca : CauchySeq a := (tendsto_atTop_ciSup ha hbdd).cauchySeq
  have hcf : CauchySeq f := by
    rw [Metric.cauchySeq_iff] at hca ⊢
    simpa only [hdist] using hca
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcf
  obtain ⟨φ, hφ, hφg⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  have haemono : ∀ᵐ x ∂μ, Monotone (fun n => f n x) := by
    have hsucc : ∀ᵐ x ∂μ, ∀ n, f n x ≤ f (n + 1) x :=
      ae_all_iff.mpr (fun n => (Lp.coeFn_le _ _).mpr (hf n))
    exact hsucc.mono fun x hx => monotone_nat_of_le_succ hx
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    filter_upwards [haemono, hφg] with x hx hlim
    exact (tendsto_iff_tendsto_subseq_of_monotone hx hφ.tendsto_atTop).mpr hlim
  refine ⟨g, ?_, hpoint, hg, ?_⟩
  · filter_upwards [haemono, hpoint] with x hx ht
    exact isLUB_of_tendsto_atTop hx ht
  · have ht := (tendsto_iff_dist_tendsto_zero.mp hg)
    simpa only [dist_eq_norm, norm_sub_rev] using ht

/-- Transport of the L¹ theorem back to the original metric completion. -/
theorem completion_monotone_convergence : CompletionMonotoneConvergence.{u} := by
  intro K _ _ _ _ _ μ _ e he f hf hbdd
  have horder := (order_identification K μ e he).2
  have hmono (n : ℕ) : e (f n) ≤ e (f (n + 1)) :=
    (Lp.coeFn_le _ _).mp ((horder _ _).mp (hf n))
  obtain ⟨g, hsup, hpoint, hlim, hnorm⟩ := monotone_convergence K μ (fun n => e (f n)) hmono hbdd
  refine ⟨e.symm g, ?_, ?_, ?_, ?_⟩
  · simpa only [e.apply_symm_apply] using hsup
  · simpa only [e.apply_symm_apply] using hpoint
  · simpa only [Function.comp_def, e.symm_apply_apply] using e.symm.continuous.continuousAt.tendsto.comp hlim
  · have hn : ∀ n, ‖e.symm g - f n‖ = ‖g - e (f n)‖ := by
      intro n
      rw [← e.norm_map, e.map_sub, e.apply_symm_apply]
    simpa only [hn] using hnorm

/-- The complete integral-space corollary. -/
theorem integral_completion : IntegralCompletionTheorem.{u} :=
  ⟨quotient_identification, null_quotient_bridge, completion_identification,
    integration_extension, order_identification, lipschitz_calculus,
    absolute_value, monotone_convergence, completion_monotone_convergence⟩

end ExpandedFA.Supplements.PositiveIntegralCompletion
