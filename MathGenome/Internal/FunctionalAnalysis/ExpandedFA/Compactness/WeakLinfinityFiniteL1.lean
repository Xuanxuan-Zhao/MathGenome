import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.WeakLinfinityFiniteL1
import Mathlib.Analysis.RCLike.Extend
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.LinearAlgebra.Countable
import Mathlib.Topology.Instances.RealVectorSpace

/-!
Weakly null sequences in L∞ are locally null in L¹. We use a separable-span
argument: simultaneously enforce all representative identities and essential
norm estimates on the countable rational span, extend its bounded point
evaluations to its real closure, and use Hahn–Banach. This proves almost
everywhere convergence. Uniform boundedness and dominated convergence on the
finite-measure restriction give the conclusion. Neither a C*-algebra structure
on L∞ nor a global finite-measure or separability hypothesis is needed.
-/

noncomputable section
namespace ExpandedFA.Compactness.WeakLinfinityFiniteL1
open MeasureTheory Filter Set
open scoped ENNReal Topology
universe u v

local instance rationalNormedSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℚ E := NormedSpace.restrictScalars ℚ ℝ E

/-- Weak nullity over either scalar field implies weak nullity for the
underlying real space. -/
theorem weakNull_real {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    {g : ℕ → E}
    (h : ∀ φ : E →L[𝕜] 𝕜, Tendsto (fun n => φ (g n)) atTop (𝓝 0))
    (φ : E →L[ℝ] ℝ) : Tendsto (fun n => φ (g n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, StrongDual.re_extendRCLike_apply, RCLike.zero_re] using
    (RCLike.continuous_re.tendsto (0 : 𝕜)).comp (h (StrongDual.extendRCLike φ))

/-- The closure of a rational subspace of a real normed space is a real
subspace. This allows extension of bounded rational-linear evaluations. -/
def realClosure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℚ E) : Submodule ℝ E where
  carrier := closure (V : Set E)
  zero_mem' := subset_closure V.zero_mem
  add_mem' := V.topologicalClosure.add_mem
  smul_mem' := by
    intro c x hx
    have hclosed : IsClosed {r : ℝ | r • x ∈ closure (V : Set E)} :=
      isClosed_closure.preimage (continuous_id.smul continuous_const)
    have hrat : ∀ q : ℚ, (q : ℝ) ∈ {r : ℝ | r • x ∈ closure (V : Set E)} := by
      intro q
      change (q : ℝ) • x ∈ V.topologicalClosure
      rw [Rat.cast_smul_eq_qsmul]
      exact V.topologicalClosure.smul_mem q hx
    exact Rat.isDenseEmbedding_coe_real.dense.induction_on c hclosed hrat

/-- Extend a continuous rational-linear map to the real closure of its domain. -/
def extendReal {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (V : Submodule ℚ E) (f : V →L[ℚ] F) : realClosure V →L[ℝ] F := by
  let e : V →L[ℚ] realClosure V :=
    { toLinearMap := V.inclusion (show V ≤ (realClosure V).restrictScalars ℚ from subset_closure)
      cont := continuous_subtype_val.subtype_mk _ }
  let f' := f.extend e
  exact f'.toLinearMap.toAddMonoidHom.toRealLinearMap f'.continuous

theorem extendReal_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (V : Submodule ℚ E) (f : V →L[ℚ] F) (v : V) :
    extendReal V f ⟨v, subset_closure v.property⟩ = f v := by
  let e : V →L[ℚ] realClosure V :=
    { toLinearMap := V.inclusion (show V ≤ (realClosure V).restrictScalars ℚ from subset_closure)
      cont := continuous_subtype_val.subtype_mk _ }
  have hd : DenseRange e := by
    change DenseRange (Set.inclusion (show (V : Set E) ⊆ closure (V : Set E) from subset_closure))
    exact (denseRange_inclusion_iff subset_closure).2 subset_rfl
  exact f.extend_eq hd (isUniformEmbedding_subtype_val.of_comp_iff.mp
    (show IsUniformEmbedding (Subtype.val ∘ e) from
      isUniformEmbedding_subtype_val)).isUniformInducing v

/-- The canonical representatives of L∞ obey the essential norm bound. -/
theorem ae_norm_le {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] (f : Lp F ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  simpa [Lp.norm_def, lpNorm] using ae_le_lpNorm_exponent_top (Lp.memLp f)

/-- A countable rational subspace admits, almost everywhere, continuous
real-linear point evaluations on its real closure. -/
theorem ae_exists_evaluation {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (V : Submodule ℚ (Lp F ∞ μ)) [Countable V] :
    ∀ᵐ x ∂μ, ∃ e : realClosure V →L[ℝ] F,
      ∀ v : V, e ⟨v, subset_closure v.property⟩ = (v : Lp F ∞ μ) x := by
  have hadd : ∀ᵐ x ∂μ, ∀ v w : V,
      ((v + w : V) : Lp F ∞ μ) x = (v : Lp F ∞ μ) x + (w : Lp F ∞ μ) x := by
    exact ae_all_iff.mpr fun v => ae_all_iff.mpr fun w => Lp.coeFn_add _ _
  have hsmul : ∀ᵐ x ∂μ, ∀ (q : ℚ) (v : V),
      ((q • v : V) : Lp F ∞ μ) x = q • (v : Lp F ∞ μ) x := by
    exact ae_all_iff.mpr fun q => ae_all_iff.mpr fun v => Lp.coeFn_smul _ _
  have hnorm : ∀ᵐ x ∂μ, ∀ v : V, ‖(v : Lp F ∞ μ) x‖ ≤ ‖v‖ := by
    exact ae_all_iff.mpr fun v => ae_norm_le v.val
  filter_upwards [hadd, hsmul, hnorm] with x ha hs hn
  let ev : V →ₗ[ℚ] F :=
    { toFun := fun v => (v : Lp F ∞ μ) x
      map_add' := ha
      map_smul' := hs }
  let evC : V →L[ℚ] F := ev.mkContinuous 1 (by
    intro v
    simpa only [one_mul, ev, LinearMap.coe_mk, AddHom.coe_mk] using hn v)
  exact ⟨extendReal V evC, fun v => extendReal_apply V evC v⟩

/-- Convergence of real and imaginary parts suffices over `RCLike`. -/
theorem tendsto_of_re_im {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜}
    (hr : Tendsto (fun n => RCLike.re (f n)) atTop (𝓝 0))
    (hi : Tendsto (fun n => RCLike.im (f n)) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hr' := ((RCLike.continuous_ofReal (K := 𝕜)).tendsto (0 : ℝ)).comp hr
  have hi' := ((RCLike.continuous_ofReal (K := 𝕜)).tendsto (0 : ℝ)).comp hi
  simpa only [Function.comp_def, RCLike.ofReal_zero, zero_mul, add_zero,
    RCLike.re_add_im] using hr'.add (hi'.mul_const (RCLike.I : 𝕜))

/-- Weakly null L∞ sequences converge almost everywhere, for arbitrary measures.
Only the rational span of this particular sequence is countable. -/
theorem ae_tendsto_zero {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → Lp 𝕜 ∞ μ}
    (h : ∀ φ : Lp 𝕜 ∞ μ →L[𝕜] 𝕜, Tendsto (fun n => φ (g n)) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 0) := by
  let V : Submodule ℚ (Lp 𝕜 ∞ μ) := Submodule.span ℚ (Set.range g)
  let W := realClosure V
  let gW : ℕ → W := fun n => ⟨g n, subset_closure (Submodule.subset_span ⟨n, rfl⟩)⟩
  have hw (φ : W →L[ℝ] ℝ) : Tendsto (fun n => φ (gW n)) atTop (𝓝 0) := by
    obtain ⟨φ', hφ', _⟩ := exists_extension_norm_eq W φ
    have ht := weakNull_real h φ'
    change Tendsto (fun n => φ' (gW n : Lp 𝕜 ∞ μ)) atTop (𝓝 0) at ht
    simpa only [hφ'] using ht
  filter_upwards [ae_exists_evaluation V] with x hx
  obtain ⟨ev, hev⟩ := hx
  have he (n : ℕ) : ev (gW n) = g n x :=
    hev ⟨g n, Submodule.subset_span ⟨n, rfl⟩⟩
  apply tendsto_of_re_im
  · simpa only [ContinuousLinearMap.comp_apply, he, RCLike.reCLM_apply] using
      hw (RCLike.reCLM.comp ev)
  · simpa only [ContinuousLinearMap.comp_apply, he, RCLike.imCLM_apply] using
      hw (RCLike.imCLM.comp ev)

/-- Uniform boundedness applied to evaluations on the complete dual space. -/
theorem weakNull_norm_bounded {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : ℕ → E}
    (h : ∀ φ : E →L[𝕜] 𝕜, Tendsto (fun n => φ (g n)) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ n, ‖g n‖ ≤ C := by
  have hp (φ : E →L[𝕜] 𝕜) : ∃ C : ℝ, ∀ n,
      ‖NormedSpace.inclusionInDoubleDual 𝕜 E (g n) φ‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (h φ))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hp
  refine ⟨C, fun n => ?_⟩
  have hn : ‖NormedSpace.inclusionInDoubleDual 𝕜 E (g n)‖ = ‖g n‖ :=
    (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (g n)
  exact hn ▸ hC n

/-- The manuscript's local L¹ conclusion, including arbitrary measures and
both scalar fields. The same proof covers a trivial measure algebra. -/
theorem weakLinfinity_finiteL1 :
    ∀ (𝕜 : Type v) [RCLike 𝕜] (α : Type u) [MeasurableSpace α]
      (μ : Measure α) (g : ℕ → Lp 𝕜 ∞ μ),
      (∀ φ : Lp 𝕜 ∞ μ →L[𝕜] 𝕜, Tendsto (fun n => φ (g n)) atTop (𝓝 0)) →
      ∀ A : Set α, MeasurableSet A → μ A < ∞ →
        Tendsto (fun n => ∫ x in A, ‖g n x‖ ∂μ) atTop (𝓝 0) := by
  intro 𝕜 _ α _ μ g hg A _ hA
  have : IsFiniteMeasure (μ.restrict A) := ⟨by simpa using hA⟩
  obtain ⟨C, hC⟩ := weakNull_norm_bounded hg
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => ‖g n x‖) (μ.restrict A) :=
    (Lp.aestronglyMeasurable (g n)).norm.restrict
  have hbound (n : ℕ) : ∀ᵐ x ∂μ.restrict A, ‖‖g n x‖‖ ≤ C := by
    filter_upwards [ae_restrict_of_ae (ae_norm_le (g n))] with x hx
    exact (norm_norm _).le.trans (hx.trans (hC n))
  have hlim : ∀ᵐ x ∂μ.restrict A, Tendsto (fun n => ‖g n x‖) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae (ae_tendsto_zero hg)] with x hx
    exact tendsto_norm_zero.comp hx
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (μ := μ.restrict A) (f := fun _ => (0 : ℝ)) (fun _ => C)
    hmeas (integrable_const C) hbound hlim

/-- Real weak nullity is transported by the actual pointwise inclusion into
complex L∞. Testing real and imaginary parts of a complex functional suffices. -/
theorem realToComplex_weakNull : Spec.RealToComplexWeakNull.{u} := by
  intro α _ μ g hg φ
  let T := Complex.ofRealCLM.compLpL ∞ μ
  let φr := Complex.reCLM.comp ((φ.restrictScalars ℝ).comp T)
  let φi := Complex.imCLM.comp ((φ.restrictScalars ℝ).comp T)
  exact tendsto_of_re_im (hg φr) (hg φi)

end ExpandedFA.Compactness.WeakLinfinityFiniteL1
