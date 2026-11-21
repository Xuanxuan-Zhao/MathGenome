import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.Mercer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.MercerExpansion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.ContinuousTraceDiagonal

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace ComplexConjugate Topology
universe u
namespace ExpandedFA.IntegralOperators.Mercer

/-- The positive clause, with the complete absolute uniform spectral expansion. -/
theorem mercer : Spec.PositiveMercer.{u} := MercerExpansion.mercer

/-- No symmetry or positivity is required in the general complex clause. -/
theorem complex_diagonal_trace : Spec.ComplexDiagonalTrace.{u} :=
  ContinuousTraceDiagonal.fullSupport_diagonalTrace

section RealTransfer
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]

/-- Scalar extension of functions only; no trace-class assertion about a
complexified operator is needed. -/
def ofRealL2 : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

lemma ofRealL2_ae (f : Lp ℝ 2 μ) :
    (ofRealL2 μ f : Q → ℂ) =ᵐ[μ] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

lemma ofRealL2_inner (f g : Lp ℝ 2 μ) :
    ⟪ofRealL2 μ f, ofRealL2 μ g⟫_ℂ = (⟪f,g⟫_ℝ : ℂ) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, (inner ℝ (f x) (g x) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ofRealL2_ae μ f, ofRealL2_ae μ g] with x hx hy
      simp [hx, hy, RCLike.inner_apply]
    _ = _ := integral_complex_ofReal

lemma ofRealL2_norm (f : Lp ℝ 2 μ) : ‖ofRealL2 μ f‖ = ‖f‖ := by
  have h : ∀ᵐ x ∂μ, ‖ofRealL2 μ f x‖ = ‖f x‖ := by
    filter_upwards [ofRealL2_ae μ f] with x hx
    simp [hx]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.ge))

lemma ofRealL2_continuous (f : C(Q, ℝ)) :
    ofRealL2 μ (ContinuousMap.toLp 2 μ ℝ f) =
      ContinuousMap.toLp 2 μ ℂ ⟨fun x => (f x : ℂ), by fun_prop⟩ := by
  apply Lp.ext
  filter_upwards [ofRealL2_ae μ (ContinuousMap.toLp 2 μ ℝ f),
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) μ f,
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ
      (⟨fun x => (f x : ℂ), by fun_prop⟩ : C(Q, ℂ))] with x hx hy hz
  simp only [hx, hy, hz, ContinuousMap.coe_mk]

lemma ofRealL2_indicator (s : Set Q) (hs : MeasurableSet s) (c : ℝ) :
    ofRealL2 μ (indicatorConstLp 2 hs (measure_ne_top μ s) c) =
      indicatorConstLp 2 hs (measure_ne_top μ s) (c : ℂ) := by
  apply Lp.ext
  filter_upwards [ofRealL2_ae μ (indicatorConstLp 2 hs (measure_ne_top μ s) c),
    @indicatorConstLp_coeFn Q ℝ _ 2 μ _ s hs (measure_ne_top μ s) c,
    @indicatorConstLp_coeFn Q ℂ _ 2 μ _ s hs (measure_ne_top μ s) (c : ℂ)] with x hx hy hz
  rw [hx, hy, hz]
  by_cases h : x ∈ s <;> simp [h]

/-- Real normalized cell vectors map to the already constructed complex ones. -/
def realCell (s : Set Q) (hs : MeasurableSet s) : Lp ℝ 2 μ :=
  indicatorConstLp 2 hs (measure_ne_top μ s) (Real.sqrt (μ.real s))⁻¹

lemma ofRealL2_cell (s : Set Q) (hs : MeasurableSet s) :
    ofRealL2 μ (realCell μ s hs) = ContinuousTraceDiagonal.cellVector μ s hs :=
  ofRealL2_indicator μ s hs _

lemma realCell_orthonormal {ι : Type*} (C : ι → Set Q)
    (hm : ∀ i, MeasurableSet (C i)) (hp : ∀ i, μ (C i) ≠ 0)
    (hd : Pairwise (fun i j => Disjoint (C i) (C j))) :
    Orthonormal ℝ (fun i => realCell μ (C i) (hm i)) := by
  classical
  have hc := ContinuousTraceDiagonal.cellVectors_orthonormal μ C hm hp hd
  rw [orthonormal_iff_ite] at hc ⊢
  intro i j
  have h := hc i j
  rw [← ofRealL2_cell, ← ofRealL2_cell, ofRealL2_inner] at h
  by_cases hij : i = j
  · simpa only [if_pos hij, Complex.ofReal_re, Complex.one_re] using congrArg Complex.re h
  · simpa only [if_neg hij, Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re h

lemma ofRealL2_projection {ι : Type*} [Fintype ι] (b : ι → Lp ℝ 2 μ)
    (f : Lp ℝ 2 μ) :
    ofRealL2 μ (ContinuousTraceDiagonal.cellProjection (𝕜 := ℝ) b f) =
      ContinuousTraceDiagonal.cellProjection (𝕜 := ℂ) (fun i => ofRealL2 μ (b i))
        (ofRealL2 μ f) := by
  simp only [ContinuousTraceDiagonal.cellProjection_apply, map_sum, map_smul,
    ofRealL2_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

/-- Finite averaging projections converge on real continuous functions, by
scalar extension and the isometry of real L² inside complex L². -/
lemma real_projection_converges
    (N : ℕ → ℕ) (C : ∀ n, Fin (N n) → Set Q)
    (hm : ∀ n i, MeasurableSet (C n i)) (hp : ∀ n i, μ (C n i) ≠ 0)
    (hd : ∀ n, Pairwise (fun i j => Disjoint (C n i) (C n j)))
    (hc : ∀ n, ∀ᵐ x ∂μ, ∃ i, x ∈ C n i)
    (hmesh : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i x, x ∈ C n i →
      ∀ y ∈ C n i, dist x y < ε) (f : C(Q, ℝ)) :
    Tendsto (fun n => ContinuousTraceDiagonal.cellProjection (𝕜 := ℝ)
      (fun i => realCell μ (C n i) (hm n i)) (ContinuousMap.toLp 2 μ ℝ f))
      atTop (𝓝 (ContinuousMap.toLp 2 μ ℝ f)) := by
  have h := ContinuousTraceDiagonal.cellProjection_tendsto_continuous μ N C hm hp hd hc hmesh
    (⟨fun x => (f x : ℂ), by fun_prop⟩ : C(Q, ℂ))
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn
  simpa only [dist_eq_norm, ← ofRealL2_continuous, ← ofRealL2_cell,
    ← ofRealL2_projection, ← map_sub, ofRealL2_norm] using hn

/-- Scalar extension intertwines the actual kernel operators. This uses the
representative formula and commutation of integration with the scalar embedding. -/
lemma ofRealL2_kernel (k : C(Q × Q, ℝ)) (f : Lp ℝ 2 μ) :
    ofRealL2 μ (MercerExpansion.Spec.operator μ k f) =
      MercerExpansion.Spec.operator μ
        (⟨fun p => (k p : ℂ), by fun_prop⟩ : C(Q × Q, ℂ)) (ofRealL2 μ f) := by
  rw [← MercerExpansion.continuousImage_toLp, ofRealL2_continuous,
    ← MercerExpansion.continuousImage_toLp]
  congr 1
  ext x
  simp only [ContinuousMap.coe_mk, MercerExpansion.continuousImage_apply]
  calc
    _ = ∫ y, ((k (x,y) * f y : ℝ) : ℂ) ∂μ := integral_complex_ofReal.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ofRealL2_ae μ f] with y hy
      simp [hy]

end RealTransfer

/-- The general diagonal trace identity over the real field. -/
theorem real_diagonal_trace : Spec.RealDiagonalTrace.{u} := by
  intro Q _ _ _ _ μ _ _ k hK
  obtain ⟨N, C, hm, hd, hp, hc, hmesh⟩ :=
    ContinuousTraceDiagonal.exists_finite_positive_partition_sequence μ
  let b : (n : ℕ) → Fin (N n) → Lp ℝ 2 μ := fun n i => realCell μ (C n i) (hm n i)
  let P : ℕ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    fun n => ContinuousTraceDiagonal.cellProjection (𝕜 := ℝ) (b n)
  have hb (n) : Orthonormal ℝ (b n) := realCell_orthonormal μ (C n) (hm n) (hp n) (hd n)
  have hbound (n) : ‖P n‖ ≤ 1 := ContinuousTraceDiagonal.cellProjection_norm_le (b n) (hb n)
  have hstrong : ∀ f, Tendsto (fun n => P n f) atTop (𝓝 f) :=
    ContinuousTraceDiagonal.strong_tendsto_of_dense_range (ContinuousMap.toLp 2 μ ℝ)
      (ContinuousMap.toLp_denseRange ℝ μ ℝ (by norm_num)) P hbound
      (real_projection_converges μ N C hm hp hd hc
        (ContinuousTraceDiagonal.eventually_cell_mesh C hmesh))
  have ht := ContinuousTraceDiagonal.trace_tendsto_comp_of_strong
    (MercerExpansion.Spec.operator μ k) hK P 1 hbound hstrong
  have heq (n) : TraceIdeals.TraceClassDefinitions.Spec.TraceValue
      ((P n).comp (MercerExpansion.Spec.operator μ k)) =
      ∑ i, ⟪b n i, MercerExpansion.Spec.operator μ k (b n i)⟫_ℝ :=
    ContinuousTraceDiagonal.trace_finite_projection (b n) (hb n) _
  simp_rw [heq] at ht
  let kc : C(Q × Q, ℂ) := ⟨fun p => (k p : ℂ), by fun_prop⟩
  have hi := ContinuousTraceDiagonal.kernel_cell_sum_tendsto μ C hm hd hp hc hmesh kc
    (MercerExpansion.Spec.operator μ kc)
    (ContinuousTraceDiagonal.continuousKernelOperator_ae μ kc)
  have hcoeff (n) (i : Fin (N n)) :
      ⟪ContinuousTraceDiagonal.cellVector μ (C n i) (hm n i),
        MercerExpansion.Spec.operator μ kc (ContinuousTraceDiagonal.cellVector μ (C n i) (hm n i))⟫_ℂ =
        (⟪b n i, MercerExpansion.Spec.operator μ k (b n i)⟫_ℝ : ℂ) := by
    rw [← ofRealL2_cell, ← ofRealL2_kernel μ k, ofRealL2_inner]
  simp_rw [hcoeff] at hi
  have hire := Complex.continuous_re.tendsto _ |>.comp hi
  simp only [Function.comp_def, Complex.re_sum, Complex.ofReal_re, kc, ContinuousMap.coe_mk,
    integral_complex_ofReal] at hire
  exact tendsto_nhds_unique ht hire

end ExpandedFA.IntegralOperators.Mercer
