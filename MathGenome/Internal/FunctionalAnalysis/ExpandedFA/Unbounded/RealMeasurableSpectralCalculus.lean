import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealMeasurableSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RealDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ENNReal
namespace ExpandedFA.Unbounded.RealMeasurableSpectralCalculus
open ExpandedFA.SpectralMeasure
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {E : RealProjectionValuedMeasure S H}

private theorem boundedFunction_ext {a b : RealBoundedFunction S}
    (h : ∀ s, a s = b s) : a = b := by
  cases a
  cases b
  congr
  exact funext h

/-- The norm-limit operator; its domain is part of its value. -/
def measurableIntegral (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) : Operator ℝ H H := measurableIntegralValue C f hf

theorem truncations_converge (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : (measurableIntegral C f hf).domain) :
    Tendsto (fun n => truncatedOperator C f hf n x) atTop
      (𝓝 (measurableIntegral C f hf x)) := tendsto_nhds_limUnder x.property

/-- Bounded dominated convergence in the strong topology. The only measure
used is the finite vector measure of the particular vector x. -/
theorem bounded_integrals_tendsto_zero (C : RealBoundedRealization E)
    (g : ℕ → RealBoundedFunction S) (K : ℝ) (_hK : 0 ≤ K)
    (hbound : ∀ n s, |g n s| ≤ K)
    (hlim : ∀ s, Tendsto (fun n => g n s) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => C.integral (g n) x) atTop (𝓝 0) := by
  let := C.scalar_finite x
  have hi : Tendsto (fun n => ∫ s, |g n s| ^ 2 ∂(C.scalar x)) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence (μ := C.scalar x)
      (F := fun n s => |g n s| ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => K ^ 2)
      (fun n => ((continuous_abs.measurable.comp (g n).measurable).pow_const 2).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbound n s) 2)
      (Eventually.of_forall fun s => by simpa only [abs_zero, zero_pow (by decide : 2 ≠ 0)] using (hlim s).abs.pow 2)
  have hn : Tendsto (fun n => ‖C.integral (g n) x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [C.norm_square] using hi
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hn
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

/-- Spectral cutoffs exhaust H even for an unbounded symbol and nonseparable H. -/
theorem cutoff_tendsto (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : H) :
    Tendsto (fun n => E (truncationSet f n) x) atTop (𝓝 x) := by
  let g : ℕ → RealBoundedFunction S := fun n =>
    .add (.indicator (truncationSet f n) (measurableSet_truncationSet hf n))
      (.const (-1))
  have hg : ∀ n s, |g n s| ≤ 1 := by
    intro n s
    by_cases hs : s ∈ truncationSet f n <;>
      simp [g, RealBoundedFunction.add, RealBoundedFunction.indicator,
        RealBoundedFunction.const, hs]
  have hl : ∀ s, Tendsto (fun n => g n s) atTop (𝓝 0) := by
    intro s
    obtain ⟨N, hN⟩ := exists_nat_gt |f s|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hs : s ∈ truncationSet f n :=
      hN.le.trans (by exact_mod_cast hn)
    simp [g, RealBoundedFunction.add, RealBoundedFunction.indicator,
      RealBoundedFunction.const, hs]
  have h := bounded_integrals_tendsto_zero C g 1 zero_le_one hg hl x
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  simpa only [g, C.integral_add, C.integral_indicator, C.integral_const,
    add_apply, smul_apply, one_apply_eq_self,
    neg_one_smul, ← sub_eq_add_neg, sub_apply] using h

/-- A bounded symbol is eventually unchanged by the canonical truncations. -/
theorem bounded_truncations_eventually (g : RealBoundedFunction S) :
    ∀ᶠ n in atTop, truncation g g.measurable n = g := by
  obtain ⟨K, _, hg⟩ := g.bounded
  obtain ⟨N, hN⟩ := exists_nat_gt K
  filter_upwards [eventually_ge_atTop N] with n hn
  apply boundedFunction_ext
  intro s
  have hs : s ∈ truncationSet g n :=
    (hg s).trans (hN.le.trans (by exact_mod_cast hn))
  exact indicator_of_mem hs _

/-- Bounded symbols retain the actual bounded integral on all vectors. -/
theorem bounded_agreement (C : RealBoundedRealization E) (g : RealBoundedFunction S) :
    measurableIntegral C g g.measurable = (C.integral g).toLinearMap.toPMap ⊤ := by
  have ht (x : H) : Tendsto (fun n => truncatedOperator C g g.measurable n x)
      atTop (𝓝 (C.integral g x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [bounded_truncations_eventually g] with n hn
    simp only [truncatedOperator, hn]
  apply LinearPMap.ext
  · apply top_unique
    intro x _
    exact ⟨C.integral g x, ht x⟩
  · intro x hx hy
    exact tendsto_nhds_unique (truncations_converge C g g.measurable ⟨x, hx⟩) (ht x)


/-- A larger cutoff leaves a smaller truncated symbol unchanged. -/
theorem truncated_mul_cutoff (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) {n m : ℕ} (hnm : n ≤ m) :
    truncatedOperator C f hf n * E (truncationSet f m) = truncatedOperator C f hf n := by
  rw [truncatedOperator, ← C.integral_indicator _ (measurableSet_truncationSet hf m),
    ← C.integral_mul]
  congr 1
  apply boundedFunction_ext
  intro s
  by_cases hn : s ∈ truncationSet f n
  · have hm : s ∈ truncationSet f m := (show |f s| ≤ (n : ℝ) from hn).trans (by exact_mod_cast hnm)
    simp [RealBoundedFunction.mul, RealBoundedFunction.indicator, truncation, hn, hm]
  · simp [RealBoundedFunction.mul, truncation, hn]

/-- Cutting a larger truncated operator on the left gives the smaller one. -/
theorem cutoff_mul_truncated (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) {n m : ℕ} (hnm : n ≤ m) :
    E (truncationSet f n) * truncatedOperator C f hf m = truncatedOperator C f hf n := by
  rw [truncatedOperator, ← C.integral_indicator _ (measurableSet_truncationSet hf n),
    ← C.integral_mul]
  congr 1
  apply boundedFunction_ext
  intro s
  by_cases hn : s ∈ truncationSet f n
  · have hm : s ∈ truncationSet f m := (show |f s| ≤ (n : ℝ) from hn).trans (by exact_mod_cast hnm)
    simp [RealBoundedFunction.mul, RealBoundedFunction.indicator, truncation, hn, hm]
  · simp [RealBoundedFunction.mul, RealBoundedFunction.indicator, truncation, hn]

theorem truncated_mul_cutoff_of_ge (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) {n m : ℕ} (hnm : n ≤ m) :
    truncatedOperator C f hf m * E (truncationSet f n) = truncatedOperator C f hf n := by
  rw [← C.integral_indicator _ (measurableSet_truncationSet hf n),
    truncatedOperator, ← C.integral_mul]
  have h := cutoff_mul_truncated C f hf hnm
  rw [← C.integral_indicator _ (measurableSet_truncationSet hf n),
    truncatedOperator, ← C.integral_mul] at h
  rw [← h]
  congr 1
  apply boundedFunction_ext
  intro s
  exact mul_comm _ _

/-- Every cutoff range lies in the convergence domain. -/
theorem cutoff_mem_domain (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (n : ℕ) (x : H) :
    E (truncationSet f n) x ∈ (measurableIntegral C f hf).domain := by
  refine ⟨truncatedOperator C f hf n x, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [eventually_ge_atTop n] with m hm
  exact congrArg (fun T : H →L[ℝ] H => T x) (truncated_mul_cutoff_of_ge C f hf hm).symm

theorem integral_cutoff (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (n : ℕ) (x : H) :
    measurableIntegral C f hf ⟨E (truncationSet f n) x, cutoff_mem_domain C f hf n x⟩ =
      truncatedOperator C f hf n x := by
  apply tendsto_nhds_unique (truncations_converge C f hf _)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact congrArg (fun T : H →L[ℝ] H => T x) (truncated_mul_cutoff_of_ge C f hf hm).symm

theorem densely_defined (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) : Dense ((measurableIntegral C f hf).domain : Set H) := by
  intro x
  exact mem_closure_of_tendsto (cutoff_tendsto C f hf x)
    (Eventually.of_forall fun n => cutoff_mem_domain C f hf n x)

/-- The finite-cutoff equations characterize the full graph. -/
theorem cutoff_output (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : (measurableIntegral C f hf).domain) (n : ℕ) :
    E (truncationSet f n) (measurableIntegral C f hf x) = truncatedOperator C f hf n x := by
  apply tendsto_nhds_unique
    (((E (truncationSet f n)).continuous.tendsto _).comp (truncations_converge C f hf x))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact congrArg (fun T : H →L[ℝ] H => T (x : H)) (cutoff_mul_truncated C f hf hm).symm

theorem graph_iff_cutoffs (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x y : H) :
    (x, y) ∈ (measurableIntegral C f hf).graph ↔
      ∀ n, truncatedOperator C f hf n x = E (truncationSet f n) y := by
  constructor
  · intro hz n
    obtain ⟨z, hz, hzy⟩ := (measurableIntegral C f hf).mem_graph_iff.mp hz
    change (z : H) = x at hz
    change measurableIntegral C f hf z = y at hzy
    rw [← hz, ← hzy]
    exact (cutoff_output C f hf z n).symm
  · intro h
    have ht : Tendsto (fun n => truncatedOperator C f hf n x) atTop (𝓝 y) := by
      simpa only [h] using cutoff_tendsto C f hf y
    have hx : x ∈ (measurableIntegral C f hf).domain := ⟨y, ht⟩
    exact (measurableIntegral C f hf).mem_graph_iff.mpr
      ⟨⟨x, hx⟩, rfl, tendsto_nhds_unique (truncations_converge C f hf ⟨x, hx⟩) ht⟩

/-- Closedness follows from bounded equations for every spectral cutoff. -/
theorem isClosed (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) : (measurableIntegral C f hf).IsClosed := by
  have heq : ((measurableIntegral C f hf).graph : Set (H × H)) =
      ⋂ n, {p | truncatedOperator C f hf n p.1 = E (truncationSet f n) p.2} := by
    ext p
    exact (graph_iff_cutoffs C f hf p.1 p.2).trans (by simp)
  change _root_.IsClosed ((measurableIntegral C f hf).graph : Set (H × H))
  rw [heq]
  exact isClosed_iInter fun n => isClosed_eq
    ((truncatedOperator C f hf n).continuous.comp continuous_fst)
    ((E (truncationSet f n)).continuous.comp continuous_snd)


theorem truncated_inner (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (n : ℕ) (x y : H) :
    ⟪truncatedOperator C f hf n x, y⟫_ℝ = ⟪x, truncatedOperator C f hf n y⟫_ℝ := by
  have h := C.integral_star (truncation f hf n)
  rw [ContinuousLinearMap.star_eq_adjoint] at h
  change ⟪C.integral (truncation f hf n) x, y⟫_ℝ = _
  calc
    _ = ⟪x, ContinuousLinearMap.adjoint (C.integral (truncation f hf n)) y⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_right _ x y).symm
    _ = _ := by rw [h]; rfl

theorem symmetric (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x y : (measurableIntegral C f hf).domain) :
    ⟪measurableIntegral C f hf x, (y : H)⟫_ℝ =
      ⟪(x : H), measurableIntegral C f hf y⟫_ℝ := by
  have hx := (truncations_converge C f hf x).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := (y : H)))
  have hy := (tendsto_const_nhds (x := (x : H))).inner (𝕜 := ℝ)
    (truncations_converge C f hf y)
  apply tendsto_nhds_unique hx
  exact hy.congr' (Eventually.of_forall fun n => (truncated_inner C f hf n x y).symm)

/-- Equality includes both domains. In particular it is stronger than symmetry. -/
theorem self_adjoint (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) : hilbertAdjoint (measurableIntegral C f hf) =
      measurableIntegral C f hf := by
  let A := measurableIntegral C f hf
  have hd : DenselyDefined A := densely_defined C f hf
  have hgraph (y : (hilbertAdjoint A).domain) :
      ((y : H), hilbertAdjoint A y) ∈ A.graph := by
    apply (graph_iff_cutoffs C f hf _ _).mpr
    intro n
    apply ext_inner_left ℝ
    intro v
    have h := hilbertAdjoint_inner A hd y
      ⟨E (truncationSet f n) v, cutoff_mem_domain C f hf n v⟩
    change ⟪measurableIntegral C f hf _, (y : H)⟫_ℝ = _ at h
    rw [integral_cutoff, truncated_inner, E.selfAdjoint _
      (measurableSet_truncationSet hf n)] at h
    exact h
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, _⟩ := A.mem_graph_iff.mp (hgraph ⟨y, hy⟩)
      change (z : H) = y at hz
      simpa only [hz] using z.property
    · intro y x hyx
      obtain ⟨z, hz, hzy⟩ := A.mem_graph_iff.mp (hgraph y)
      have hzx : z = x := Subtype.ext (hz.trans hyx)
      exact (hzx ▸ hzy).symm
  · refine ⟨?_, ?_⟩
    · intro y hy
      exact (mem_hilbertAdjoint_domain_iff A hd y).mpr
        ⟨A ⟨y, hy⟩, fun x => symmetric C f hf x ⟨y, hy⟩⟩
    · intro y x hyx
      symm
      apply hilbertAdjoint_apply_eq A hd x (A y)
      intro v
      rw [← hyx]
      exact symmetric C f hf v y

/-- Normality is equality of partial products, so their domains agree as well. -/
theorem normal (C : RealBoundedRealization E) (f : S → ℝ) (hf : Measurable f) :
    product (hilbertAdjoint (measurableIntegral C f hf)) (measurableIntegral C f hf) =
      product (measurableIntegral C f hf) (hilbertAdjoint (measurableIntegral C f hf)) := by
  rw [self_adjoint C f hf]


theorem truncation_eventually_at (f : S → ℝ) (hf : Measurable f) (s : S) :
    ∀ᶠ n in atTop, truncation f hf n s = f s := by
  obtain ⟨N, hN⟩ := exists_nat_gt |f s|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hs : s ∈ truncationSet f n := hN.le.trans (by exact_mod_cast hn)
  exact indicator_of_mem hs _

theorem integrable_bounded_square (C : RealBoundedRealization E)
    (g : RealBoundedFunction S) (x : H) : Integrable (fun s => |g s| ^ 2) (C.scalar x) := by
  let := C.scalar_finite x
  obtain ⟨K, _, hg⟩ := g.bounded
  apply Integrable.of_bound ((continuous_abs.measurable.comp g.measurable).pow_const 2).aestronglyMeasurable (K ^ 2)
  exact Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hg s) 2

theorem truncated_norm_square (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (n : ℕ) (x : H) :
    ENNReal.ofReal (‖truncatedOperator C f hf n x‖ ^ 2) =
      ∫⁻ s, ENNReal.ofReal (|truncation f hf n s| ^ 2) ∂(C.scalar x) := by
  rw [truncatedOperator, C.norm_square]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_bounded_square C _ x)
    (Eventually.of_forall fun _ => sq_nonneg _)

theorem truncated_moment_tendsto (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : H) :
    Tendsto (fun n => ENNReal.ofReal (‖truncatedOperator C f hf n x‖ ^ 2)) atTop
      (𝓝 (squareMoment C f x)) := by
  simp_rw [truncated_norm_square]
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact (ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp (truncation f hf n).measurable).pow_const 2)).aemeasurable
  · apply Eventually.of_forall
    intro s n m hnm
    apply ENNReal.ofReal_le_ofReal
    by_cases hn : s ∈ truncationSet f n
    · have hm : s ∈ truncationSet f m :=
        (show |f s| ≤ (n : ℝ) from hn).trans (by exact_mod_cast hnm)
      simp [truncation, hn, hm]
    · simp only [truncation, indicator_of_notMem hn, abs_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
  · apply Eventually.of_forall
    intro s
    exact tendsto_const_nhds.congr' ((truncation_eventually_at f hf s).mono fun n hn => by dsimp only; rw [hn])

/-- The extended identity cannot conceal a divergent integral behind a
real-valued totalized integral. -/
theorem norm_square_extended (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : (measurableIntegral C f hf).domain) :
    squareMoment C f x = ENNReal.ofReal (‖measurableIntegral C f hf x‖ ^ 2) := by
  exact tendsto_nhds_unique (truncated_moment_tendsto C f hf x)
    ((ENNReal.continuous_ofReal.tendsto _).comp ((truncations_converge C f hf x).norm.pow 2))

theorem truncated_norm_sub_sq (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) {n m : ℕ} (hnm : n ≤ m) (x : H) :
    ‖truncatedOperator C f hf m x - truncatedOperator C f hf n x‖ ^ 2 =
      ‖truncatedOperator C f hf m x‖ ^ 2 - ‖truncatedOperator C f hf n x‖ ^ 2 := by
  have hp (k : ℕ) (hk : n ≤ k) :
      E (truncationSet f n) (truncatedOperator C f hf k x) = truncatedOperator C f hf n x :=
    congrArg (fun T : H →L[ℝ] H => T x) (cutoff_mul_truncated C f hf hk)
  have hi : ⟪truncatedOperator C f hf m x, truncatedOperator C f hf n x⟫_ℝ =
      ‖truncatedOperator C f hf n x‖ ^ 2 := by
    calc
      _ = ⟪truncatedOperator C f hf m x,
          E (truncationSet f n) (truncatedOperator C f hf n x)⟫_ℝ := by rw [hp n le_rfl]
      _ = ⟪E (truncationSet f n) (truncatedOperator C f hf m x),
          truncatedOperator C f hf n x⟫_ℝ :=
        (E.selfAdjoint _ (measurableSet_truncationSet hf n) _ _).symm
      _ = _ := by rw [hp m hnm, real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, hi]
  ring

/-- Finite square moment forces norm convergence of the bounded truncations. -/
theorem mem_domain_of_squareMoment_lt_top (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : H) (hx : squareMoment C f x < ∞) :
    x ∈ (measurableIntegral C f hf).domain := by
  have ht : Tendsto (fun n => ‖truncatedOperator C f hf n x‖ ^ 2) atTop
      (𝓝 (squareMoment C f x).toReal) := by
    have h := (ENNReal.tendsto_toReal (ne_of_lt hx)).comp (truncated_moment_tendsto C f hf x)
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using h
  have hc := ht.cauchySeq
  have hC : CauchySeq (fun n => truncatedOperator C f hf n x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmn := hN m hm n hn
    rw [Real.dist_eq] at hmn
    rcases le_total n m with hle | hle
    · have he := truncated_norm_sub_sq C f hf hle x
      have hle' := le_abs_self (‖truncatedOperator C f hf m x‖ ^ 2 -
        ‖truncatedOperator C f hf n x‖ ^ 2)
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (truncatedOperator C f hf m x - truncatedOperator C f hf n x)]
    · have he := truncated_norm_sub_sq C f hf hle x
      have hle' := neg_le_abs (‖truncatedOperator C f hf m x‖ ^ 2 -
        ‖truncatedOperator C f hf n x‖ ^ 2)
      rw [dist_eq_norm, norm_sub_rev]
      nlinarith [norm_nonneg (truncatedOperator C f hf n x - truncatedOperator C f hf m x)]
  exact cauchySeq_tendsto_of_complete hC

theorem maximal_domain (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : H) :
    x ∈ (measurableIntegral C f hf).domain ↔ squareMoment C f x < ∞ := by
  constructor
  · intro hx
    rw [norm_square_extended C f hf ⟨x, hx⟩]
    exact ENNReal.ofReal_lt_top
  · exact mem_domain_of_squareMoment_lt_top C f hf x


/-- Weighting a coefficient measure is the actual coefficient of the bounded
integral. This identity anchors the variation measure used below. -/
theorem bounded_coefficient_withDensity (C : RealBoundedRealization E)
    (g : RealBoundedFunction S) (x y : H) :
    C.coefficient x (C.integral g y) =
      (C.coefficient x y).withDensity g (ContinuousLinearMap.lsmul ℝ ℝ) := by
  ext B hB
  rw [C.coefficient_apply _ _ _ hB,
    VectorMeasure.withDensity_apply (C.coefficient_integrable g x y)]
  calc
    _ = ⟪x, C.integral (.mul (.indicator B hB) g) y⟫_ℝ := by
      rw [C.integral_mul, C.integral_indicator]; rfl
    _ = (C.coefficient x y).integral
        ((RealBoundedFunction.mul (.indicator B hB) g) : S → ℝ)
        (ContinuousLinearMap.lsmul ℝ ℝ) := C.coefficient_integral _ _ _
    _ = _ := by
      rw [← VectorMeasure.integral_indicator hB]
      congr 1
      funext s
      by_cases hs : s ∈ B <;>
        simp [RealBoundedFunction.mul, RealBoundedFunction.indicator, hs]

/-- The total variation identity gives a weighted L¹ bound without a common
scalar control measure or a sigma-finiteness assumption. -/
theorem bounded_lintegral_norm_le (C : RealBoundedRealization E)
    (g : RealBoundedFunction S) (x y : H) :
    (∫⁻ s, ENNReal.ofReal |g s| ∂(C.coefficient x y).variation) ≤
      ENNReal.ofReal (‖x‖ * ‖C.integral g y‖) := by
  have h := C.variation_bound x (C.integral g y)
  rw [bounded_coefficient_withDensity,
    VectorMeasure.variation_withDensity (C.coefficient_integrable g x y)
      (by intro a b; simp),
    VectorMeasure.variation_transpose_lsmul,
    MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  simpa only [Real.enorm_eq_ofReal_abs] using h

/-- Integrability against genuine coefficient variation on the maximal domain. -/
theorem coefficient_integrable (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : H) (y : (measurableIntegral C f hf).domain) :
    Integrable f (C.coefficient x y).variation := by
  have hm : Tendsto (fun n => ∫⁻ s, ENNReal.ofReal |truncation f hf n s|
      ∂(C.coefficient x y).variation) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal |f s| ∂(C.coefficient x y).variation)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp (truncation f hf n).measurable)).aemeasurable
    · apply Eventually.of_forall
      intro s n m hnm
      apply ENNReal.ofReal_le_ofReal
      by_cases hn : s ∈ truncationSet f n
      · have hm : s ∈ truncationSet f m :=
          (show |f s| ≤ (n : ℝ) from hn).trans (by exact_mod_cast hnm)
        simp [truncation, hn, hm]
      · simp only [truncation, indicator_of_notMem hn, abs_zero]
        exact abs_nonneg _
    · apply Eventually.of_forall
      intro s
      exact tendsto_const_nhds.congr'
        ((truncation_eventually_at f hf s).mono fun n hn => by dsimp only; rw [hn])
  have hb := le_of_tendsto_of_tendsto hm
    ((ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_const_nhds.mul (truncations_converge C f hf y).norm))
    (Eventually.of_forall fun n => bounded_lintegral_norm_le C (truncation f hf n) x y)
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  exact hb.trans_lt ENNReal.ofReal_lt_top

theorem coefficient_integral (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : H) (y : (measurableIntegral C f hf).domain) :
    ⟪x, measurableIntegral C f hf y⟫_ℝ =
      (C.coefficient x y).integral f (ContinuousLinearMap.lsmul ℝ ℝ) := by
  have h := VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := C.coefficient x y) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (f := f) (fun s => |f s|)
    (fun n => (truncation f hf n).measurable.aestronglyMeasurable)
    (coefficient_integrable C f hf x y).norm
    (fun n => Eventually.of_forall fun s => by
      by_cases hs : s ∈ truncationSet f n
      · simp [truncation, hs, Real.norm_eq_abs]
      · simp [truncation, hs, abs_nonneg])
    (Eventually.of_forall fun s => tendsto_const_nhds.congr' ((truncation_eventually_at f hf s).mono fun n hn => hn.symm))
  have hl := (tendsto_const_nhds (x := x)).inner (𝕜 := ℝ) (truncations_converge C f hf y)
  apply tendsto_nhds_unique hl
  simpa only [truncatedOperator, C.coefficient_integral] using h


theorem square_integrable (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : (measurableIntegral C f hf).domain) :
    Integrable (fun s => |f s| ^ 2) (C.scalar x) := by
  refine ⟨((continuous_abs.measurable.comp hf).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [Real.norm_eq_abs, abs_sq, squareMoment] using
    (maximal_domain C f hf x).mp x.property

theorem norm_square (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (x : (measurableIntegral C f hf).domain) :
    ‖measurableIntegral C f hf x‖ ^ 2 = ∫ s, |f s| ^ 2 ∂(C.scalar x) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
    (square_integrable C f hf x).aestronglyMeasurable]
  change _ = (squareMoment C f x).toReal
  rw [norm_square_extended, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem square_integrability_submodule (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) : ∃ D : Submodule ℝ H,
      (D : Set H) = {x | squareMoment C f x < ∞} := by
  refine ⟨(measurableIntegral C f hf).domain, ?_⟩
  ext x
  exact maximal_domain C f hf x

/-- The complete maximal real measurable calculus for every given bounded
realization, with no unbounded certificate among the hypotheses. -/
theorem calculus_for_every_realization : Spec.EveryRealization.{u, v} := by
  intro S H _ _ _ _ E C
  refine ⟨?_, fun g => bounded_agreement C g⟩
  intro f hf
  refine ⟨maximal_domain C f hf, ?_, square_integrability_submodule C f hf,
    truncations_converge C f hf, densely_defined C f hf, isClosed C f hf,
    self_adjoint C f hf, normal C f hf, ?_, ?_, ?_⟩
  · intro x
    exact (maximal_domain C f hf x).symm
  · exact congrArg LinearPMap.domain (normal C f hf)
  · intro x
    exact ⟨norm_square_extended C f hf x, square_integrable C f hf x, norm_square C f hf x⟩
  · intro x y
    exact ⟨coefficient_integrable C f hf x y, coefficient_integral C f hf x y⟩

/-- Existence for each given PVM follows from the bounded construction, followed
by the above universally quantified maximal extension theorem. -/
theorem calculus_exists : Spec.RealizationExists.{u, v} := by
  intro S H _ _ _ _ E
  exact ⟨E.boundedRealization, calculus_for_every_realization S H E E.boundedRealization⟩

end ExpandedFA.Unbounded.RealMeasurableSpectralCalculus
