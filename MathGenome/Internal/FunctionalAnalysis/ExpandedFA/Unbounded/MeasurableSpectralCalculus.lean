import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.MeasurableSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint

noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace ExpandedFA.Unbounded.MeasurableSpectralCalculus
universe u v

section Limits
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem limitOperator_tendsto (T : ℕ → H →L[ℂ] H) (x : (limitOperator T).domain) :
    Tendsto (fun n => T n x) atTop (nhds (limitOperator T x)) :=
  tendsto_nhds_limUnder x.2

theorem mem_limitOperator_graph_iff (T : ℕ → H →L[ℂ] H) (x y : H) :
    (x, y) ∈ (limitOperator T).graph ↔ Tendsto (fun n => T n x) atTop (nhds y) := by
  constructor
  · intro h
    obtain ⟨z, hx, hy⟩ := (limitOperator T).mem_graph_iff.mp h
    dsimp only at hx hy
    subst x y
    exact limitOperator_tendsto T z
  · intro h
    exact (limitOperator T).mem_graph_iff.mpr ⟨⟨x, ⟨y, h⟩⟩, rfl, h.limUnder_eq⟩

/-- Compatible bounded localizations characterize the limit graph. No
uniform bound on T, completeness, density or integrability is presumed. -/
theorem mem_limitOperator_graph_iff_localized (P T : ℕ → H →L[ℂ] H)
    (hP : ∀ y, Tendsto (fun n => P n y) atTop (nhds y))
    (hcompat : ∀ n, ∀ᶠ m in atTop, P n * T m = T n) (x y : H) :
    (x, y) ∈ (limitOperator T).graph ↔ ∀ n, T n x = P n y := by
  rw [mem_limitOperator_graph_iff]
  constructor
  · intro h n
    have hp := ((P n).continuous.tendsto y).comp h
    have heq : (fun m => P n (T m x)) =ᶠ[atTop] (fun _ => T n x) := by
      filter_upwards [hcompat n] with m hm
      exact congrArg (fun A : H →L[ℂ] H => A x) hm
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' heq.symm) hp
  · intro h
    simpa only [h] using hP y

/-- Closedness reduces to continuous equalities on every bounded piece. -/
theorem limitOperator_isClosed_of_localized (P T : ℕ → H →L[ℂ] H)
    (hP : ∀ y, Tendsto (fun n => P n y) atTop (nhds y))
    (hcompat : ∀ n, ∀ᶠ m in atTop, P n * T m = T n) :
    (limitOperator T).IsClosed := by
  have hgraph : ((limitOperator T).graph : Set (H × H)) =
      ⋂ n, {z | T n z.1 = P n z.2} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_limitOperator_graph_iff_localized P T hP hcompat z.1 z.2
  change _root_.IsClosed ((limitOperator T).graph : Set (H × H))
  rw [hgraph]
  exact isClosed_iInter (fun n =>
    isClosed_eq ((T n).continuous.comp continuous_fst) ((P n).continuous.comp continuous_snd))

theorem tendsto_apply_projection (P T : ℕ → H →L[ℂ] H)
    (hright : ∀ n, ∀ᶠ m in atTop, T m * P n = T n) (n : ℕ) (x : H) :
    Tendsto (fun m => T m (P n x)) atTop (nhds (T n x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hright n] with m hm
  exact (congrArg (fun A : H →L[ℂ] H => A x) hm).symm

theorem projection_mem_limitOperator_domain (P T : ℕ → H →L[ℂ] H)
    (hright : ∀ n, ∀ᶠ m in atTop, T m * P n = T n) (n : ℕ) (x : H) :
    P n x ∈ (limitOperator T).domain :=
  ⟨T n x, tendsto_apply_projection P T hright n x⟩

theorem limitOperator_apply_projection (P T : ℕ → H →L[ℂ] H)
    (hright : ∀ n, ∀ᶠ m in atTop, T m * P n = T n) (n : ℕ) (x : H) :
    limitOperator T ⟨P n x, projection_mem_limitOperator_domain P T hright n x⟩ = T n x :=
  (tendsto_apply_projection P T hright n x).limUnder_eq

theorem limitOperator_dense_of_localized (P T : ℕ → H →L[ℂ] H)
    (hP : ∀ y, Tendsto (fun n => P n y) atTop (nhds y))
    (hright : ∀ n, ∀ᶠ m in atTop, T m * P n = T n) :
    Dense ((limitOperator T).domain : Set H) := by
  intro x
  exact mem_closure_of_tendsto (hP x)
    (Eventually.of_forall (fun n => projection_mem_limitOperator_domain P T hright n x))

theorem mem_product_graph_iff (A B : Operator ℂ H H) (x z : H) :
    (x, z) ∈ (OperatorDomainsSpec.productValue A B).graph ↔
      ∃ y, (x, y) ∈ B.graph ∧ (y, z) ∈ A.graph := by
  have hgraph (A : Operator ℂ H H) (x y : H) :
      (x, y) ∈ A.graph ↔ ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = y := by
    constructor
    · intro h
      obtain ⟨u, hx, hy⟩ := A.mem_graph_iff.mp h
      dsimp only at hx hy
      subst x
      exact ⟨u.2, hy⟩
    · rintro ⟨hx, hy⟩
      exact A.mem_graph_iff.mpr ⟨⟨x, hx⟩, rfl, hy⟩
  rw [hgraph]
  constructor
  · rintro ⟨hx, hz⟩
    obtain ⟨hxB, hxA⟩ := hx
    refine ⟨B ⟨x, hxB⟩,
      (hgraph B _ _).mpr ⟨hxB, rfl⟩,
      (hgraph A _ _).mpr ⟨hxA, ?_⟩⟩
    exact hz
  · rintro ⟨y, hB, hA⟩
    obtain ⟨hxB, rfl⟩ := (hgraph B _ _).mp hB
    obtain ⟨hxA, hz⟩ := (hgraph A _ _).mp hA
    exact ⟨⟨hxB, hxA⟩, hz⟩

/-- Cross identities of bounded cutoffs pass to the products on their actual
domains. The domain assumption is explicit; no maximal-product rule is used. -/
theorem limitOperator_product_le_swap (T V : ℕ → H →L[ℂ] H)
    (hdom : (limitOperator T).domain ≤ (limitOperator V).domain)
    (hcross : ∀ n m, T n * V m = V n * T m) :
    OperatorDomainsSpec.productValue (limitOperator V) (limitOperator T) ≤
      OperatorDomainsSpec.productValue (limitOperator T) (limitOperator V) := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨x, z⟩ h
  obtain ⟨y, hxy, hyz⟩ := (mem_product_graph_iff _ _ x z).mp h
  have hx : x ∈ (limitOperator T).domain :=
    ((ExpandedFA.Unbounded.mem_graph_iff _ _).mp hxy).choose
  let v : H := limitOperator V ⟨x, hdom hx⟩
  have hv := limitOperator_tendsto V ⟨x, hdom hx⟩
  have ht := (mem_limitOperator_graph_iff T x y).mp hxy
  have heq : ∀ n, T n v = V n y := by
    intro n
    have h₁ := ((T n).continuous.tendsto v).comp hv
    have h₂ := ((V n).continuous.tendsto y).comp ht
    change Tendsto (fun m => T n (V m x)) atTop (nhds (T n v)) at h₁
    have hpoint : (fun m => T n (V m x)) = (fun m => V n (T m x)) := by
      funext m
      exact congrArg (fun A : H →L[ℂ] H => A x) (hcross n m)
    rw [hpoint] at h₁
    exact tendsto_nhds_unique h₁ h₂
  apply (mem_product_graph_iff _ _ x z).mpr
  refine ⟨v, (mem_limitOperator_graph_iff V x v).mpr hv, ?_⟩
  apply (mem_limitOperator_graph_iff T v z).mpr
  simpa only [heq] using (mem_limitOperator_graph_iff V y z).mp hyz

theorem limitOperator_products_swap (T V : ℕ → H →L[ℂ] H)
    (hdom : (limitOperator T).domain = (limitOperator V).domain)
    (hcross : ∀ n m, T n * V m = V n * T m) :
    OperatorDomainsSpec.productValue (limitOperator V) (limitOperator T) =
      OperatorDomainsSpec.productValue (limitOperator T) (limitOperator V) := by
  apply le_antisymm
  · exact limitOperator_product_le_swap T V (le_of_eq hdom) hcross
  · exact limitOperator_product_le_swap V T (le_of_eq hdom.symm)
      (fun n m => (hcross n m).symm)

end Limits

section Adjoint
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem limitOperator_domain_eq_of_dist_eq (T V : ℕ → H →L[ℂ] H)
    (hdist : ∀ x m n, dist (T m x) (T n x) = dist (V m x) (V n x)) :
    (limitOperator T).domain = (limitOperator V).domain := by
  ext x
  change (∃ y, Tendsto (fun n => T n x) atTop (nhds y)) ↔
    ∃ y, Tendsto (fun n => V n x) atTop (nhds y)
  have hc : CauchySeq (fun n => T n x) ↔ CauchySeq (fun n => V n x) := by
    simp only [Metric.cauchySeq_iff, hdist]
  constructor
  · rintro ⟨y, hy⟩
    exact cauchySeq_tendsto_of_complete (hc.mp hy.cauchySeq)
  · rintro ⟨y, hy⟩
    exact cauchySeq_tendsto_of_complete (hc.mpr hy.cauchySeq)

/-- The adjoint follows from testing on the bounded projected vectors. This
proves both inclusions of the adjoint graph, including the full adjoint domain. -/
theorem limitOperator_adjoint_of_localized (P T : ℕ → H →L[ℂ] H)
    (hP : ∀ y, Tendsto (fun n => P n y) atTop (nhds y))
    (hself : ∀ n, IsSelfAdjoint (P n))
    (hright : ∀ n, ∀ᶠ m in atTop, T m * P n = T n) :
    (limitOperator T).adjoint = limitOperator (fun n => star (T n)) := by
  have hd : DenselyDefined (limitOperator T) :=
    limitOperator_dense_of_localized P T hP hright
  apply LinearPMap.eq_of_eq_graph
  ext ⟨y, z⟩
  change (y, z) ∈ (hilbertAdjoint (limitOperator T)).graph ↔ _
  rw [mem_hilbertAdjoint_graph_iff _ hd, mem_limitOperator_graph_iff]
  constructor
  · intro h
    have heq : ∀ n, star (T n) y = P n z := by
      intro n
      apply ext_inner_left ℂ
      intro x
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      calc
        inner ℂ (T n x) y = inner ℂ
            (limitOperator T ⟨P n x, projection_mem_limitOperator_domain P T hright n x⟩) y := by
          rw [limitOperator_apply_projection P T hright]
        _ = inner ℂ (P n x) z := h _
        _ = inner ℂ x (P n z) := by
          rw [← (hself n).adjoint_eq, ContinuousLinearMap.adjoint_inner_right]
          rw [(hself n).adjoint_eq]
    simpa only [heq] using hP z
  · intro h x
    have hleft := (limitOperator_tendsto T x).inner (𝕜 := ℂ)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (nhds y))
    have hright' := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (x : H))
      atTop (nhds (x : H))).inner (𝕜 := ℂ) h
    have heq : (fun n => inner ℂ (x : H) (star (T n) y)) =
        (fun n => inner ℂ (T n x) y) := by
      funext n
      exact (T n).adjoint_inner_right _ _
    rw [heq] at hright'
    exact tendsto_nhds_unique hleft hright'

end Adjoint

section Spectral
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded realization really exists under the original PVM axioms. -/
theorem exists_boundedRealization (E : SpectralMeasure.ProjectionValuedMeasure S H) :
    Nonempty (BoundedRealization E) := by
  exact ⟨{
    measure := E.diagonalMeasure
    integral := E.spectralIntegral
    finite := E.diagonalMeasure_finite
    measure_apply := E.diagonalMeasure_apply
    simple := E.spectralIntegral_simple
    uniform_limit := E.spectralIntegral_tendsto
    one := E.spectralIntegral_one
    add := E.spectralIntegral_add
    smul := E.spectralIntegral_smul
    mul := E.spectralIntegral_mul
    map_star := E.spectralIntegral_star
    bound := fun f C hf hC hb => E.spectralIntegral_norm_le f hf C hC hb
    norm_sq := E.spectralIntegral_norm_sq_integral }⟩

theorem measurable_truncation {f : S → ℂ} (hf : Measurable f) (n : ℕ) :
    Measurable (truncation f n) :=
  hf.indicator (measurableSet_le hf.norm measurable_const)

omit [MeasurableSpace S] in
theorem norm_truncation_le (f : S → ℂ) (n : ℕ) (s : S) :
    ‖truncation f n s‖ ≤ (n : ℝ) := by
  classical
  by_cases hs : ‖f s‖ ≤ (n : ℝ)
  · simp [truncation, hs]
  · simp [truncation, hs]

theorem boundedMeasurable_truncation {f : S → ℂ} (hf : Measurable f) (n : ℕ) :
    SpectralMeasure.Spec.IsBoundedMeasurable (truncation f n) :=
  ⟨measurable_truncation hf n, ⟨n, norm_truncation_le f n⟩⟩

omit [MeasurableSpace S] in
theorem truncation_eventually_eq (f : S → ℂ) (s : S) :
    ∀ᶠ n : ℕ in atTop, truncation f n s = f s := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f s‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : s ∈ {s | ‖f s‖ ≤ (n : ℝ)} := hN.trans hNn
  exact Set.indicator_of_mem hs f

theorem truncation_tendsto (f : S → ℂ) (s : S) :
    Tendsto (fun n => truncation f n s) atTop (nhds (f s)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [truncation_eventually_eq f s] with n hn using hn.symm

omit [MeasurableSpace S] in
theorem truncation_star (f : S → ℂ) (n : ℕ) :
    truncation (star f) n = star (truncation f n) := by
  classical
  funext s
  by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [truncation, hs]

omit [MeasurableSpace S] in
theorem truncation_norm_sq_mono (f : S → ℂ) (s : S) :
    Monotone (fun n => ‖truncation f n s‖ ^ 2) := by
  classical
  intro n m hnm
  by_cases hn : ‖f s‖ ≤ (n : ℝ)
  · have hm : ‖f s‖ ≤ (m : ℝ) := hn.trans (by exact_mod_cast hnm)
    simp [truncation, hn, hm]
  · by_cases hm : ‖f s‖ ≤ (m : ℝ) <;> simp [truncation, hn, hm]

theorem boundedMeasurable_cutoffIndicator {f : S → ℂ} (hf : Measurable f) (n : ℕ) :
    SpectralMeasure.Spec.IsBoundedMeasurable (cutoffIndicator f n) := by
  refine ⟨measurable_const.indicator (measurableSet_le hf.norm measurable_const), 1, ?_⟩
  intro s
  classical
  by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [cutoffIndicator, hs]

omit [MeasurableSpace S] in
theorem truncation_mul_cutoffIndicator (f : S → ℂ) {m n : ℕ} (hnm : n ≤ m) :
    truncation f m * cutoffIndicator f n = truncation f n := by
  classical
  funext s
  have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  by_cases hn : ‖f s‖ ≤ (n : ℝ)
  · have hm := hn.trans hnm'
    simp [truncation, cutoffIndicator, hn, hm]
  · simp [truncation, cutoffIndicator, hn]

namespace BoundedRealization
variable {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)

theorem sub (f g : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    C.integral (f - g) = C.integral f - C.integral g := by
  have hng : SpectralMeasure.Spec.IsBoundedMeasurable (-g) := by
    simpa using hg.smul (-1)
  have hn : C.integral (-g) = -C.integral g := by
    simpa using C.smul (-1) g hg
  simpa only [sub_eq_add_neg, hn] using C.add f (-g) hf hng

theorem norm_star_apply (f : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (x : H) :
    ‖star (C.integral f) x‖ = ‖C.integral f x‖ := by
  have h := C.norm_sq (star f) hf.star x
  rw [C.map_star f hf] at h
  simp only [Pi.star_apply, norm_star] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h.trans (C.norm_sq f hf x).symm)

theorem integrable_norm_sq (f : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (x : H) :
    Integrable (fun s => ‖f s‖ ^ 2) (C.measure x) := by
  haveI := C.finite x
  obtain ⟨M, hM, hb⟩ := hf.nonneg_bound
  refine ⟨(hf.1.norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := M ^ 2) (Eventually.of_forall (fun s => ?_))⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f s‖)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb s) 2

theorem lintegral_norm_sq (f : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (x : H) :
    (∫⁻ s, ENNReal.ofReal (‖f s‖ ^ 2) ∂C.measure x) =
      ENNReal.ofReal (‖C.integral f x‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (C.integrable_norm_sq f hf x)
    (Eventually.of_forall (fun s => sq_nonneg ‖f s‖)), ← C.norm_sq f hf x]

theorem cutoff_selfAdjoint {f : S → ℂ} (hf : Measurable f) (n : ℕ) :
    IsSelfAdjoint (C.integral (cutoffIndicator f n)) := by
  change star (C.integral (cutoffIndicator f n)) = _
  rw [← C.map_star _ (boundedMeasurable_cutoffIndicator hf n)]
  congr 1
  classical
  funext s
  by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [cutoffIndicator, hs]

theorem cutoff_right {f : S → ℂ} (hf : Measurable f) (n : ℕ) :
    ∀ᶠ m in atTop, C.integral (truncation f m) * C.integral (cutoffIndicator f n) =
      C.integral (truncation f n) := by
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← C.mul _ _ (boundedMeasurable_truncation hf m) (boundedMeasurable_cutoffIndicator hf n),
    truncation_mul_cutoffIndicator f hm]

theorem cutoff_left {f : S → ℂ} (hf : Measurable f) (n : ℕ) :
    ∀ᶠ m in atTop, C.integral (cutoffIndicator f n) * C.integral (truncation f m) =
      C.integral (truncation f n) := by
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← C.mul _ _ (boundedMeasurable_cutoffIndicator hf n) (boundedMeasurable_truncation hf m),
    mul_comm, truncation_mul_cutoffIndicator f hm]

theorem truncation_dist_star {f : S → ℂ} (hf : Measurable f) (x : H) (m n : ℕ) :
    dist (C.integral (truncation f m) x) (C.integral (truncation f n) x) =
      dist (star (C.integral (truncation f m)) x) (star (C.integral (truncation f n)) x) := by
  have hm := boundedMeasurable_truncation hf m
  have hn := boundedMeasurable_truncation hf n
  have hdiff : SpectralMeasure.Spec.IsBoundedMeasurable (truncation f m - truncation f n) := by
    simpa only [sub_eq_add_neg] using hm.add (by simpa using hn.smul (-1))
  have h := C.norm_star_apply _ hdiff x
  rw [C.sub _ _ hm hn, star_sub] at h
  simpa only [dist_eq_norm, sub_apply] using h.symm

theorem truncation_cross {f : S → ℂ} (hf : Measurable f) (m n : ℕ) :
    C.integral (truncation f m) * star (C.integral (truncation f n)) =
      star (C.integral (truncation f m)) * C.integral (truncation f n) := by
  have hm := boundedMeasurable_truncation hf m
  have hn := boundedMeasurable_truncation hf n
  rw [← C.map_star _ hm, ← C.map_star _ hn, ← C.mul _ _ hm hn.star, ← C.mul _ _ hm.star hn]
  congr 1
  classical
  funext s
  by_cases hm : ‖f s‖ ≤ (m : ℝ) <;>
    by_cases hn : ‖f s‖ ≤ (n : ℝ) <;> simp [truncation, hm, hn, mul_comm]

theorem cutoff_tendsto {f : S → ℂ} (hf : Measurable f) (x : H) :
    Tendsto (fun n => C.integral (cutoffIndicator f n) x) atTop (nhds x) := by
  let q : ℕ → S → ℂ := fun n => cutoffIndicator f n - (fun _ => 1)
  have hq : ∀ n, SpectralMeasure.Spec.IsBoundedMeasurable (q n) := by
    intro n
    refine ⟨(boundedMeasurable_cutoffIndicator hf n).1.sub measurable_const, 1, ?_⟩
    intro s
    classical
    by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [q, cutoffIndicator, hs]
  have hq0 : ∀ s, Tendsto (fun n => q n s) atTop (nhds 0) := by
    intro s
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_ge ‖f s‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hs : ‖f s‖ ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
    simp [q, cutoffIndicator, hs]
  haveI := C.finite x
  have hInt : Tendsto (fun n => ∫ s, ‖q n s‖ ^ 2 ∂C.measure x) atTop (nhds 0) := by
    have ht : Tendsto (fun n => ∫ s, ‖q n s‖ ^ 2 ∂C.measure x) atTop
        (nhds (∫ _, (0 : ℝ) ∂C.measure x)) := by
      apply tendsto_integral_filter_of_norm_le_const
      · exact Eventually.of_forall (fun n =>
          ((hq n).1.norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
      · refine ⟨1, Eventually.of_forall (fun n => Eventually.of_forall (fun s => ?_))⟩
        have hb : ‖q n s‖ ≤ 1 := by
          classical
          by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [q, cutoffIndicator, hs]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖q n s‖)]
        simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2
      · exact Eventually.of_forall (fun s => by simpa using (hq0 s).norm.pow 2)
    simpa only [integral_zero] using ht
  have hnorm : Tendsto (fun n => ‖C.integral (q n) x‖) atTop (nhds 0) := by
    have hn : Tendsto (fun n => ‖C.integral (q n) x‖ ^ 2) atTop (nhds 0) := by
      simpa only [C.norm_sq _ (hq _) x] using hInt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn.sqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hnorm using 1
  funext n
  have hone : SpectralMeasure.Spec.IsBoundedMeasurable (fun _ : S => (1 : ℂ)) :=
    ⟨measurable_const, 1, fun _ => by simp⟩
  rw [show q n = cutoffIndicator f n - (fun _ => 1) from rfl,
    C.sub _ _ (boundedMeasurable_cutoffIndicator hf n) hone, C.one]
  rfl

end BoundedRealization

theorem squareIntegrable_of_mem_domain {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) {f : S → ℂ} (hf : Measurable f)
    (x : (measurableIntegral C f).domain) : SquareIntegrable C f x := by
  have hMCT : Tendsto
      (fun n => ∫⁻ s, ENNReal.ofReal (‖truncation f n s‖ ^ 2) ∂C.measure x)
      atTop (nhds (∫⁻ s, ENNReal.ofReal (‖f s‖ ^ 2) ∂C.measure x)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · exact fun n => (ENNReal.measurable_ofReal.comp
        ((measurable_truncation hf n).norm.pow_const 2)).aemeasurable
    · exact Eventually.of_forall (fun s n m hnm =>
        ENNReal.ofReal_le_ofReal (truncation_norm_sq_mono f s hnm))
    · exact Eventually.of_forall (fun s =>
        (ENNReal.continuous_ofReal.tendsto _).comp ((truncation_tendsto f s).norm.pow 2))
  have hnorm := (ENNReal.continuous_ofReal.tendsto _).comp
    ((limitOperator_tendsto (fun n => C.integral (truncation f n)) x).norm.pow 2)
  simp only [C.lintegral_norm_sq _ (boundedMeasurable_truncation hf _) x] at hMCT
  have heq := tendsto_nhds_unique hMCT hnorm
  change (∫⁻ s, ENNReal.ofReal (‖f s‖ ^ 2) ∂C.measure x) < ⊤
  rw [heq]
  exact ENNReal.ofReal_lt_top

theorem mem_domain_of_squareIntegrable {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) {f : S → ℂ} (hf : Measurable f) (x : H)
    (hx : SquareIntegrable C f x) : x ∈ (measurableIntegral C f).domain := by
  have hi : Integrable (fun s => ‖f s‖ ^ 2) (C.measure x) :=
    ⟨(hf.norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall (fun s => sq_nonneg ‖f s‖))).mpr hx⟩
  let R : ℕ → S → ℝ := fun n s => ‖f s - truncation f n s‖ ^ 2
  have hRmeas (n : ℕ) : AEStronglyMeasurable (R n) (C.measure x) :=
    ((hf.sub (measurable_truncation hf n)).norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable
  have hRbound (n : ℕ) (s : S) : ‖R n s‖ ≤ ‖f s‖ ^ 2 := by
    classical
    by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [R, truncation, hs]
  have hRint (n : ℕ) : Integrable (R n) (C.measure x) :=
    hi.mono' (hRmeas n) (Eventually.of_forall (hRbound n))
  have hRlim : Tendsto (fun n => ∫ s, R n s ∂C.measure x) atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun s => ‖f s‖ ^ 2)
      hRmeas hi (fun n => Eventually.of_forall (hRbound n))
      (Eventually.of_forall (fun s => by
        have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => f s) atTop (nhds (f s))).sub
          (truncation_tendsto f s)
        simpa [R] using ht.norm.pow 2))
    simpa only [integral_zero] using h
  have hdist (m n : ℕ) :
      dist (C.integral (truncation f m) x) (C.integral (truncation f n) x) ^ 2 ≤
        (∫ s, R m s ∂C.measure x) + ∫ s, R n s ∂C.measure x := by
    have hm := boundedMeasurable_truncation hf m
    have hn := boundedMeasurable_truncation hf n
    have hdiff : SpectralMeasure.Spec.IsBoundedMeasurable
        (truncation f m - truncation f n) := by
      simpa only [sub_eq_add_neg] using hm.add (by simpa using hn.smul (-1))
    calc
      _ = ‖C.integral (truncation f m - truncation f n) x‖ ^ 2 := by
        rw [C.sub _ _ hm hn, dist_eq_norm]
        rfl
      _ = ∫ s, ‖truncation f m s - truncation f n s‖ ^ 2 ∂C.measure x := C.norm_sq _ hdiff x
      _ ≤ ∫ s, R m s + R n s ∂C.measure x := by
        apply integral_mono (C.integrable_norm_sq _ hdiff x) ((hRint m).add (hRint n))
        intro s
        classical
        by_cases hm : ‖f s‖ ≤ (m : ℝ) <;>
          by_cases hn : ‖f s‖ ≤ (n : ℝ) <;> simp [R, truncation, hm, hn]
      _ = _ := integral_add (hRint m) (hRint n)
  change ∃ y, Tendsto (fun n => C.integral (truncation f n) x) atTop (nhds y)
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hsmall := hRlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 / 2 by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, fun m hm n hn => ?_⟩
  have hm' := hN m hm
  have hn' := hN n hn
  have hb := hdist m n
  have hnonneg : 0 ≤ dist (C.integral (truncation f m) x) (C.integral (truncation f n) x) :=
    dist_nonneg
  nlinarith

theorem measurableIntegral_domain {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) {f : S → ℂ} (hf : Measurable f) (x : H) :
    x ∈ (measurableIntegral C f).domain ↔ SquareIntegrable C f x := by
  constructor
  · intro hx
    exact squareIntegrable_of_mem_domain C hf ⟨x, hx⟩
  · exact mem_domain_of_squareIntegrable C hf x

theorem measurableIntegral_dense {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) {f : S → ℂ} (hf : Measurable f) :
    Dense ((measurableIntegral C f).domain : Set H) :=
  limitOperator_dense_of_localized _ _ (C.cutoff_tendsto hf) (C.cutoff_right hf)

theorem measurableIntegral_isClosed {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) {f : S → ℂ} (hf : Measurable f) :
    (measurableIntegral C f).IsClosed :=
  limitOperator_isClosed_of_localized _ _ (C.cutoff_tendsto hf) (C.cutoff_left hf)

theorem measurableIntegral_adjoint {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) {f : S → ℂ} (hf : Measurable f) :
    (measurableIntegral C f).adjoint = measurableIntegral C (star f) := by
  have h := limitOperator_adjoint_of_localized _ _ (C.cutoff_tendsto hf)
    (C.cutoff_selfAdjoint hf) (C.cutoff_right hf)
  have heq : (fun n => star (C.integral (truncation f n))) =
      (fun n => C.integral (truncation (star f) n)) := by
    funext n
    rw [truncation_star, C.map_star _ (boundedMeasurable_truncation hf n)]
  exact h.trans (congrArg limitOperator heq)

theorem measurableIntegral_normal {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) {f : S → ℂ} (hf : Measurable f) :
    OperatorDomainsSpec.productValue (measurableIntegral C f).adjoint (measurableIntegral C f) =
      OperatorDomainsSpec.productValue (measurableIntegral C f) (measurableIntegral C f).adjoint := by
  have ha := limitOperator_adjoint_of_localized _ _ (C.cutoff_tendsto hf)
    (C.cutoff_selfAdjoint hf) (C.cutoff_right hf)
  change OperatorDomainsSpec.productValue (limitOperator _).adjoint (limitOperator _) =
    OperatorDomainsSpec.productValue (limitOperator _) (limitOperator _).adjoint
  rw [ha]
  exact limitOperator_products_swap _ _
    (limitOperator_domain_eq_of_dist_eq _ _ (C.truncation_dist_star hf)) (C.truncation_cross hf)

theorem measurableIntegral_selfAdjoint {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) {f : S → ℂ} (hf : Measurable f) (hreal : ∀ s, (f s).im = 0) :
    (measurableIntegral C f).adjoint = measurableIntegral C f := by
  rw [measurableIntegral_adjoint C hf]
  congr 1
  funext s
  apply Complex.ext <;> simp [hreal s]

theorem measurableIntegral_tendsto {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) (f : S → ℂ) (x : (measurableIntegral C f).domain) :
    Tendsto (fun n => C.integral (truncation f n) x) atTop
      (nhds (measurableIntegral C f x)) :=
  limitOperator_tendsto _ x

end Spectral

/-- The unbounded integral, carrying its exact domain. The bounded realization
is merely an explicit choice of the already proved bounded calculus; its
existence for every PVM is part of the unconditional theorem below. -/
def measurableSpectralIntegral : Spec.MeasurableIntegralType.{u, v} :=
  Spec.MeasurableIntegralValue

theorem measurable_spectral_calculus : Spec.MeasurableCalculusInterface.{u, v} := by
  intro S H _ _ _ _ E C f hf
  exact ⟨measurableIntegral_domain C hf, measurableIntegral_dense C hf,
    measurableIntegral_isClosed C hf, measurableIntegral_adjoint C hf,
    measurableIntegral_normal C hf, measurableIntegral_selfAdjoint C hf,
    measurableIntegral_tendsto C f⟩

/-- No unbounded certificate is assumed: a PVM alone supplies the bounded
realization and all the conclusions for its unbounded measurable calculus. -/
theorem exists_measurable_spectral_calculus : Spec.MeasurableCalculusExistsInterface.{u, v} := by
  intro S H _ _ _ _ E
  obtain ⟨C⟩ := exists_boundedRealization E
  exact ⟨C, measurable_spectral_calculus C⟩

end ExpandedFA.Unbounded.MeasurableSpectralCalculus
