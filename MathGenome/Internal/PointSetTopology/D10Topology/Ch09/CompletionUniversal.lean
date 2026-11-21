import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.CompletionUniversal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricCompletion
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The universal property of the specified metric completion, including
continuous uniqueness, the unchanged real Lipschitz constant, and comparison
of arbitrary completions. The reciprocal counterexample uses the usual metric.
-/

open Set Filter
open scoped Topology
universe u v w

namespace D10Topology.Ch09

/-- Dense image and a Hausdorff target give uniqueness without uniform continuity. -/
theorem completion_extension_unique :
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y)
    (f : X → Y) (g h : MetricCompletion d → Y),
    @Continuous _ _ (metricTopology (completionMetric d).toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) g →
    @Continuous _ _ (metricTopology (completionMetric d).toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) h →
    g ∘ completionEmbedding d = f → h ∘ completionEmbedding d = f → g = h := by
  intro X Y d e f g h hg hh hgf hhf
  let := d
  let := e
  let := completionMetric d
  change Continuous g at hg
  change Continuous h at hh
  exact (completion_dense d).equalizer hg hh (hgf.trans hhf.symm)

theorem completion_extension :
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y) (f : X → Y),
    SequentiallyComplete e.toPseudoMetricSpace →
    UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace f →
    ∃! g : MetricCompletion d → Y,
      UniformlyContinuous (completionMetric d).toPseudoMetricSpace e.toPseudoMetricSpace g ∧
      g ∘ completionEmbedding d = f := by
  intro X Y d e f hc hf
  let := d
  let := e
  let := (sequentiallyComplete_iff_mathlib e.toPseudoMetricSpace).mp hc
  let := completionMetric d
  have hf' : UniformContinuous f := (uniformlyContinuous_iff_mathlib _ _ _).mp hf
  refine ⟨UniformSpace.Completion.extension f, ⟨?_, ?_⟩, ?_⟩
  · exact (uniformlyContinuous_iff_mathlib _ _ _).mpr
      UniformSpace.Completion.uniformContinuous_extension
  · funext x
    exact UniformSpace.Completion.extension_coe hf' x
  · intro g hg
    exact completion_extension_unique d e f g _
      ((uniformlyContinuous_iff_mathlib _ _ _).mp hg.1).continuous
      UniformSpace.Completion.continuous_extension hg.2
      (funext (UniformSpace.Completion.extension_coe hf'))

/-- The inequality is closed on the product of the completions. This proof
also handles negative real L without replacing L by a nonnegative bound. -/
theorem completion_lipschitz :
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y)
    (L : ℝ) (f : X → Y) (g : MetricCompletion d → Y),
    Lipschitz d.toPseudoMetricSpace e.toPseudoMetricSpace L f →
    @Continuous _ _ (metricTopology (completionMetric d).toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) g →
    g ∘ completionEmbedding d = f →
    Lipschitz (completionMetric d).toPseudoMetricSpace e.toPseudoMetricSpace L g := by
  intro X Y d e L f g hf hg hgf
  let := d
  let := e
  let := completionMetric d
  change Continuous g at hg
  change ∀ q r, dist (g q) (g r) ≤ L * dist q r
  intro q r
  refine UniformSpace.Completion.induction_on₂ q r
    (isClosed_le ((hg.comp continuous_fst).dist (hg.comp continuous_snd))
      (continuous_const.mul (continuous_fst.dist continuous_snd))) ?_
  intro x y
  change dist (g (completionEmbedding d x)) (g (completionEmbedding d y)) ≤
    L * dist (completionEmbedding d x) (completionEmbedding d y)
  have hx : g (completionEmbedding d x) = f x := congrFun hgf x
  have hy : g (completionEmbedding d y) = f y := congrFun hgf y
  have hd : dist (completionEmbedding d x) (completionEmbedding d y) = dist x y :=
    completion_isometry d x y
  rw [hx, hy, hd]
  exact hf x y

theorem completions_unique :
  ∀ {X : Type u} {Z : Type v} {W : Type w}
    (d : MetricSpace X) (e : MetricSpace Z) (k : MetricSpace W)
    (i : X → Z) (j : X → W),
    SequentiallyComplete e.toPseudoMetricSpace → SequentiallyComplete k.toPseudoMetricSpace →
    Isometry d.toPseudoMetricSpace e.toPseudoMetricSpace i →
    Isometry d.toPseudoMetricSpace k.toPseudoMetricSpace j →
    @DenseRange Z (metricTopology e.toPseudoMetricSpace) X i →
    @DenseRange W (metricTopology k.toPseudoMetricSpace) X j →
    ∃! T : Z → W, IsometricIsomorphism e k T ∧ T ∘ i = j := by
  intro X Z W d e k i j he hk hi hj hdi hdj
  let := d
  let := e
  let := k
  let := (sequentiallyComplete_iff_mathlib _).mp he
  let := (sequentiallyComplete_iff_mathlib _).mp hk
  have hi' : _root_.Isometry i := (isometry_iff_mathlib _ _ _).mp hi
  have hj' : _root_.Isometry j := (isometry_iff_mathlib _ _ _).mp hj
  let A : AbstractCompletion X :=
    { space := Z, coe := i, uniformStruct := e.toUniformSpace,
      complete := inferInstance, separation := inferInstance,
      isUniformInducing := hi'.isUniformInducing, dense := hdi }
  let B : AbstractCompletion X :=
    { space := W, coe := j, uniformStruct := k.toUniformSpace,
      complete := inferInstance, separation := inferInstance,
      isUniformInducing := hj'.isUniformInducing, dense := hdj }
  let T : Z ≃ᵤ W := A.compareEquiv B
  have hTj : (T : Z → W) ∘ i = j := funext (A.compare_coe B)
  have hTi : _root_.Isometry (T : Z → W) := by
    apply _root_.Isometry.of_dist_eq
    intro z z'
    refine (hdi.prodMap hdi).induction_on (p := fun zz : Z × Z =>
      dist (T zz.1) (T zz.2) = dist zz.1 zz.2) (z, z')
      (isClosed_eq ((T.continuous.comp continuous_fst).dist
        (T.continuous.comp continuous_snd)) (continuous_fst.dist continuous_snd)) ?_
    intro p
    change dist (T (i p.1)) (T (i p.2)) = dist (i p.1) (i p.2)
    have hx : T (i p.1) = j p.1 := congrFun hTj p.1
    have hy : T (i p.2) = j p.2 := congrFun hTj p.2
    rw [hx, hy, hj'.dist_eq, hi'.dist_eq]
  refine ⟨T, ⟨⟨(isometry_iff_mathlib _ _ _).mpr hTi, T.surjective⟩, hTj⟩, ?_⟩
  intro S hS
  exact hdi.equalizer ((isometry_iff_mathlib _ _ _).mp hS.1.1).continuous
    T.continuous (hS.2.trans hTj.symm)

/-- The source map uses the ordinary subspace topology and real reciprocal. -/
theorem reciprocal_continuous :
  Continuous (fun x : Ioo (0 : ℝ) 1 => (x.val)⁻¹) := by
  exact continuous_subtype_val.inv₀ (fun x => ne_of_gt x.property.1)

/-- A Cauchy sequence approaches the missing endpoint, whereas its reciprocal
escapes every finite real bound. Continuity of any extension is impossible. -/
theorem reciprocal_no_extension :
  let d : MetricSpace (Ioo (0 : ℝ) 1) := inferInstance
  ¬ ∃ g : MetricCompletion d → ℝ,
    @Continuous _ _ (metricTopology (completionMetric d).toPseudoMetricSpace)
      (inferInstance : TopologicalSpace ℝ) g ∧
    g ∘ completionEmbedding d = (fun x => (x.val)⁻¹) := by
  dsimp only
  let d : MetricSpace (Ioo (0 : ℝ) 1) := inferInstance
  let s : ℕ → Ioo (0 : ℝ) 1 := fun n =>
    ⟨((n : ℝ) + 2)⁻¹, by
      constructor
      · positivity
      · apply (inv_lt_one₀ (by positivity)).mpr
        have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith⟩
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hs : Tendsto (fun n => (s n).val) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  have hc : CauchySeq s :=
    Metric.cauchySeq_iff.mpr ((Metric.cauchySeq_iff (u := fun n => (s n).val)).mp hs.cauchySeq)
  have hj : UniformContinuous (completionEmbedding d) :=
    UniformSpace.Completion.uniformContinuous_coe _
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete (hj.comp_cauchySeq hc)
  rintro ⟨g, hg, hgf⟩
  change Continuous g at hg
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop (𝓝 (g q)) := by
    have hh := hg.continuousAt.tendsto.comp hq
    convert hh using 1
    funext n
    have hx := congrFun hgf (s n)
    change g (completionEmbedding d (s n)) = ((s n).val)⁻¹ at hx
    simpa only [Function.comp_apply, s, inv_inv] using hx.symm
  exact not_tendsto_nhds_of_tendsto_atTop ht (g q) hlim

end D10Topology.Ch09
