import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.MercerExpansion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtKernels
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceBasisCyclicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.CompactNormalClassification
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! The positive Mercer theorem for continuous Hermitian kernels on compact
metric spaces with finite full-support measures, over either scalar field.
Operator positivity gives finite-matrix positivity by shrinking-ball averages.
Parseval in the reproducing kernel Hilbert space supplies the diagonal identity;
Dini and the canonical spectral trace then give all the stated conclusions.
Empty spaces, zero operators, and finite or empty spectral families are included. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace ComplexConjugate Topology
universe u
namespace ExpandedFA.IntegralOperators.MercerExpansion

section ContinuousLift
variable {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
  [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
  (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜))

/-- The continuous section y ↦ k(·,y), with values in C(Q). -/
def kernelSection : C(Q, C(Q, 𝕜)) :=
  (k.comp ⟨Prod.swap, continuous_swap⟩).curry

lemma section_integrable (f : Q → 𝕜) (hf : MemLp f 2 μ) :
    Integrable (fun y => f y • kernelSection k y) μ := by
  exact (hf.integrable (by norm_num)).smul_bdd ‖kernelSection k‖
    (kernelSection k).continuous.aestronglyMeasurable_of_compactSpace
    (Eventually.of_forall (kernelSection k).norm_coe_le_norm)

/-- Integration takes place in the Banach space C(Q). -/
def continuousImage (f : Lp 𝕜 2 μ) : C(Q, 𝕜) :=
  ∫ y, f y • kernelSection k y ∂μ

lemma continuousImage_apply (f : Lp 𝕜 2 μ) (x : Q) :
    continuousImage μ k f x = ∫ y, k (x,y) * f y ∂μ := by
  rw [continuousImage, ContinuousMap.integral_apply (section_integrable μ k f (Lp.memLp f))]
  simp [kernelSection, mul_comm]

lemma continuousImage_congr (f : Lp 𝕜 2 μ) (g : Q → 𝕜)
    (hfg : (f : Q → 𝕜) =ᵐ[μ] g) (x : Q) :
    continuousImage μ k f x = ∫ y, k (x,y) * g y ∂μ := by
  rw [continuousImage_apply]
  exact integral_congr_ae (hfg.mono fun y hy => by dsimp only; rw [hy])

/-- Comparison with the canonical a.e. kernel operator, for every L² input. -/
lemma continuousImage_toLp (f : Lp 𝕜 2 μ) :
    ContinuousMap.toLp 2 μ 𝕜 (continuousImage μ k f) = Spec.operator μ k f := by
  apply Lp.ext
  have hk : MemLp (fun z => k z) 2 (μ.prod μ) := k.memLp (p := 2) (μ.prod μ) 𝕜
  have hkLp : hk.toLp (fun z => k z) = Spec.kernelLp μ k := by
    apply Lp.ext
    exact hk.coeFn_toLp.trans (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (μ.prod μ) k).symm
  have hrep := ExpandedFA.PartV.L2Kernel.kernel_representative_formula μ μ
    (fun z => k z) (fun x => f x) hk (Lp.memLp f)
  rw [hkLp, Lp.toLp_coeFn] at hrep
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) μ (continuousImage μ k f), hrep] with x hx hKx
  exact hx.trans ((continuousImage_apply μ k f x).trans hKx.symm)

/-- An eigenvector with nonzero eigenvalue has a continuous representative.
The eigen-equation holds everywhere for this representative, even without
full support, since it is constructed by integration. -/
theorem continuous_eigenfunctions : Spec.ContinuousEigenfunctions.{u} := by
  intro Q 𝕜 _ _ _ _ _ μ _ k f a ha hfa
  let e : C(Q, 𝕜) := a⁻¹ • continuousImage μ k f
  have he : ContinuousMap.toLp 2 μ 𝕜 e = f := by
    dsimp only [e]
    rw [map_smul, continuousImage_toLp, hfa, smul_smul, inv_mul_cancel₀ ha, one_smul]
  refine ⟨e, he, fun x => ?_⟩
  have hae : (f : Q → 𝕜) =ᵐ[μ] e :=
    he ▸ ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) μ e
  rw [← continuousImage_congr μ k f e hae x]
  change continuousImage μ k f x = a * (a⁻¹ * continuousImage μ k f x)
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- Full support makes the continuous representative unique. -/
lemma continuous_eigenfunction_unique [μ.IsOpenPosMeasure]
    (f : Lp 𝕜 2 μ) (e g : C(Q, 𝕜))
    (he : ContinuousMap.toLp 2 μ 𝕜 e = f)
    (hg : ContinuousMap.toLp 2 μ 𝕜 g = f) : e = g :=
  ContinuousMap.toLp_injective μ (he.trans hg.symm)

/-- Positivity is used only on the actual eigenvector. -/
theorem positive_eigenvalues : Spec.PositiveEigenvalues.{u} := by
  intro Q 𝕜 _ _ _ _ _ μ _ k hk f a hf ha he
  have h := hk f
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  have hnonneg : 0 ≤ a * ‖f‖ ^ 2 := by
    simpa only [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re] using h
  have hsq : 0 < ‖f‖ ^ 2 := pow_pos (norm_pos_iff.mpr hf) 2
  exact lt_of_le_of_ne ((mul_nonneg_iff_of_pos_right hsq).mp hnonneg) (Ne.symm ha)

/-- The continuous kernel is determined even on the diagonal by its L² map.
This is where full support, including on the product space, is essential. -/
theorem continuous_kernel_faithfulness : Spec.ContinuousKernelFaithfulness.{u} := by
  intro Q 𝕜 _ _ _ _ _ μ _ _ k l hkl
  apply ContinuousMap.toLp_injective (𝕜 := 𝕜) (p := 2) (μ.prod μ)
  exact ExpandedFA.TraceIdeals.HilbertSchmidtKernels.kernel_injective μ μ hkl

lemma hermitian_kernelLp (hk : Spec.Hermitian k) :
    ExpandedFA.PartV.L2KernelCompactSpec.Hermitian μ (Spec.kernelLp μ k) := by
  have hrep := ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (μ.prod μ) k
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae_eq_comp hrep
  filter_upwards [hrep, hswap] with p hp hps
  change Spec.kernelLp μ k p = conj (Spec.kernelLp μ k p.swap)
  rw [hp, show Spec.kernelLp μ k p.swap = k p.swap from hps]
  exact hk p.1 p.2

lemma compact_selfAdjoint (hk : Spec.Hermitian k) :
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (Spec.operator μ k).toLinearMap ∧ IsSelfAdjoint (Spec.operator μ k) := by
  obtain ⟨hc, hs⟩ := ExpandedFA.PartV.L2KernelCompact.hermitian_kernel_compact_selfadjoint
    μ (Spec.kernelLp μ k) (hermitian_kernelLp μ k hk)
  exact ⟨hc, hs⟩

/-- Transfer the complete nonzero L² spectral family to continuous functions.
Only the accepted compact self-adjoint expansion is used; no Mercer
pointwise or diagonal assertion is used here. -/
theorem continuous_spectral_data : Spec.ContinuousSpectralData.{u} := by
  intro Q 𝕜 _ _ _ _ _ μ _ k hk hpos
  obtain ⟨hc, hs⟩ := compact_selfAdjoint μ k hk
  obtain ⟨ι, hi, e, a, hon, heig, htotal, hcompl, hexp, hfin, haway⟩ :=
    ExpandedFA.CompactSpectral.CompactNormalClassification.selfAdjoint_expansion
      𝕜 (Lp 𝕜 2 μ) (Spec.operator μ k) hs hc
  have hrep (i : ι) : ∃ g : C(Q, 𝕜), ContinuousMap.toLp 2 μ 𝕜 g = e i := by
    have ha : (a i : 𝕜) ≠ 0 := by exact_mod_cast (heig i).1
    obtain ⟨g, hg, _⟩ := continuous_eigenfunctions μ k (e i) (a i : 𝕜) ha (heig i).2
    exact ⟨g, hg⟩
  choose g hg using hrep
  refine ⟨{
    Index := ι
    countable := hi
    eigenvalue := a
    eigenfunction := g
    positive := ?_
    orthonormal := ?_
    eigen_equation := ?_
    vector_expansion := ?_
  }⟩
  · intro i
    exact positive_eigenvalues μ k hpos (e i) (a i) (hon.ne_zero i) (heig i).1 (heig i).2
  · simpa only [hg] using hon
  · intro i
    simpa only [hg] using (heig i).2
  · intro f
    simpa only [hg] using (hexp f).2

end ContinuousLift

/-- Dini applied to the directed set of finite subsets, followed by the
arithmetic-geometric mean estimate on each off-diagonal term. -/
theorem diagonal_uniform_tails : Spec.DiagonalUniformTails.{u} := by
  classical
  intro Q 𝕜 _ _ _ ι a e d ha hd
  let F : Finset ι → Q → ℝ := fun s x => ∑ i ∈ s, a i * ‖e i x‖ ^ 2
  have hnonneg (i : ι) (x : Q) : 0 ≤ a i * ‖e i x‖ ^ 2 :=
    mul_nonneg (ha i) (sq_nonneg _)
  have hmono : Monotone F := by
    intro s t hst x
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => hnonneg i x)
  have hu : TendstoUniformly F d atTop :=
    Monotone.tendstoUniformly_of_forall_tendsto
      (fun s => by dsimp [F]; fun_prop) hmono d.continuous (fun x => hd x)
  refine ⟨hu, fun ε hε => ?_⟩
  obtain ⟨s, hs⟩ := ((Metric.tendstoUniformly_iff.mp hu) ε hε).exists
  have htail (t : Finset ι) (hts : Disjoint t s) (x : Q) :
      (∑ i ∈ t, a i * ‖e i x‖ ^ 2) < ε := by
    have hbound := (hd x).summable.sum_le_tsum (s ∪ t) (fun i _ => hnonneg i x)
    rw [(hd x).tsum_eq, Finset.sum_union hts.symm] at hbound
    have herr := hs x
    have herr' : d x - F s x < ε := by
      exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq] using herr)
    dsimp only [F] at herr'
    linarith
  refine ⟨s, fun t hts x y => ?_⟩
  have hterm (i : ι) : ‖(a i : 𝕜) * e i x * conj (e i y)‖ ≤
      (a i * ‖e i x‖ ^ 2 + a i * ‖e i y‖ ^ 2) / 2 := by
    simp only [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (ha i), RCLike.norm_conj]
    nlinarith [mul_nonneg (ha i) (sq_nonneg (‖e i x‖ - ‖e i y‖))]
  calc
    _ ≤ ∑ i ∈ t, (a i * ‖e i x‖ ^ 2 + a i * ‖e i y‖ ^ 2) / 2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((∑ i ∈ t, a i * ‖e i x‖ ^ 2) + ∑ i ∈ t, a i * ‖e i y‖ ^ 2) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ < ε := by linarith [htail t hts x, htail t hts y]

/-- Uniform absolute Cauchy tails imply convergence in the two Banach spaces
of continuous functions. -/
theorem uniform_series_of_diagonal : Spec.UniformSeriesOfDiagonal.{u} := by
  classical
  intro Q 𝕜 _ _ _ ι a e d ha hd
  obtain ⟨_, htail⟩ := diagonal_uniform_tails ι a e d ha hd
  constructor
  · apply summable_iff_vanishing_norm.mpr
    intro ε hε
    obtain ⟨s, hs⟩ := htail (ε / 2) (half_pos hε)
    refine ⟨s, fun t hts => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro p
    simp only [ContinuousMap.sum_apply, Spec.kernelTerm, ContinuousMap.coe_mk]
    exact (norm_sum_le _ _).trans (hs t hts p.1 p.2).le
  · apply summable_iff_vanishing_norm.mpr
    intro ε hε
    obtain ⟨s, hs⟩ := htail (ε / 2) (half_pos hε)
    refine ⟨s, fun t hts => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro p
    simp only [ContinuousMap.sum_apply, Spec.absoluteKernelTerm, Spec.kernelTerm,
      ContinuousMap.coe_mk, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    exact (hs t hts p.1 p.2).le

/-- The summable spectral family is a nuclear expansion, so the already
established finite-family bound gives trace class and its nuclear trace
formula computes the same canonical trace. -/
theorem trace_of_summable_spectral_data : Spec.TraceOfSummableSpectralData.{u} := by
  intro Q 𝕜 _ _ _ _ _ μ _ k D hsum
  let v : D.Index → Lp 𝕜 2 μ := fun j => ContinuousMap.toLp 2 μ 𝕜 (D.eigenfunction j)
  have hv : ∀ j, ‖v j‖ = 1 := D.orthonormal.norm_eq_one
  have hnonneg : ∀ j, 0 ≤ D.eigenvalue j := fun j => (D.positive j).le
  constructor
  · apply (TraceIdeals.TraceNormIdeal.traceClass_of_finite_family_bound (Spec.operator μ k)
      (ExpandedFA.PartV.L2KernelCompact.kernel_compact μ μ (Spec.kernelLp μ k))
      (∑' j, D.eigenvalue j) ?_).1
    intro n a b ha hb
    exact TraceIdeals.TraceNormIdeal.finite_family_bound_of_expansion
      (Spec.operator μ k) D.eigenvalue v v hnonneg hsum hv hv D.vector_expansion a b ha hb
  · have htr := TraceIdeals.TraceBasisCyclicity.trace_of_expansion (Spec.operator μ k)
      D.eigenvalue v v hnonneg hsum 1
      (fun j => by rw [hv j]; norm_num) D.vector_expansion
    change TraceIdeals.TraceClassDefinitions.Spec.TraceValue (Spec.operator μ k) = _ at htr
    rw [htr, RCLike.ofReal_tsum]
    apply tsum_congr
    intro j
    dsimp only [v]
    rw [inner_self_eq_norm_sq_to_K, D.orthonormal.norm_eq_one j]
    simp

section DiagonalIntegral
variable {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
  [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
  (μ : Measure Q) [IsFiniteMeasure μ]

lemma integral_norm_sq (e : C(Q, 𝕜)) :
    (∫ x, ‖e x‖ ^ 2 ∂μ) = ‖ContinuousMap.toLp 2 μ 𝕜 e‖ ^ 2 := by
  have he := e.memLp (p := 2) μ 𝕜
  have hLp : he.toLp e = ContinuousMap.toLp 2 μ 𝕜 e :=
    Lp.ext (he.coeFn_toLp.trans (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) μ e).symm)
  simpa only [hLp] using ExpandedFA.PartV.L2Kernel.integral_sq_norm e he

/-- The integral as a continuous linear functional on C(Q,ℝ). -/
def integralFunctional : C(Q, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (α := Q) (E := ℝ) (μ := μ)).comp (ContinuousMap.toLp 1 μ ℝ)

lemma integralFunctional_apply (f : C(Q, ℝ)) :
    integralFunctional μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f)

/-- Monotone diagonal partial sums converge in C(Q), so their integrals
converge without needing an assumed integrable majorant for the series. -/
theorem eigenvalue_sum_of_diagonal : Spec.EigenvalueSumOfDiagonal.{u} := by
  intro Q 𝕜 _ _ _ _ _ μ _ k D hdiag
  let F : D.Index → C(Q, ℝ) := fun j =>
    ⟨fun x => D.eigenvalue j * ‖D.eigenfunction j x‖ ^ 2, by fun_prop⟩
  let d : C(Q, ℝ) := ⟨fun x => RCLike.re (k (x,x)), by fun_prop⟩
  have hmono : Monotone (fun s : Finset D.Index => ∑ j ∈ s, F j) := by
    intro s t hst x
    change (ContinuousMap.evalCLM ℝ x) (∑ j ∈ s, F j) ≤
      (ContinuousMap.evalCLM ℝ x) (∑ j ∈ t, F j)
    simp only [map_sum, ContinuousMap.evalCLM_apply]
    exact Finset.sum_le_sum_of_subset_of_nonneg hst
      (fun j _ _ => mul_nonneg (D.positive j).le (sq_nonneg _))
  have hs : HasSum F d :=
    ContinuousMap.tendsto_of_monotone_of_pointwise hmono
      (fun x => by simpa only [HasSum, SummationFilter.unconditional, ContinuousMap.sum_apply, F, d, ContinuousMap.coe_mk] using hdiag x)
  have hInt (j : D.Index) : integralFunctional μ (F j) = D.eigenvalue j := by
    rw [integralFunctional_apply]
    change (∫ x, D.eigenvalue j * ‖D.eigenfunction j x‖ ^ 2 ∂μ) = _
    rw [integral_const_mul, integral_norm_sq, D.orthonormal.norm_eq_one j]
    simp
  have h := (integralFunctional μ).hasSum hs
  simpa only [hInt, integralFunctional_apply, d, ContinuousMap.coe_mk] using h

end DiagonalIntegral
section KernelSeries
variable {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
  [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
  (μ : Measure Q) [IsFiniteMeasure μ]

lemma continuous_inner_formula (e : C(Q, 𝕜)) (f : Lp 𝕜 2 μ) :
    ⟪ContinuousMap.toLp 2 μ 𝕜 e, f⟫_𝕜 = ∫ y, conj (e y) * f y ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) μ e] with y hy
  rw [hy, RCLike.inner_apply']

lemma kernelTerm_operator (a : ℝ) (e : C(Q, 𝕜)) (f : Lp 𝕜 2 μ) :
    Spec.operator μ (Spec.kernelTerm a e) f =
      ((a : 𝕜) * ⟪ContinuousMap.toLp 2 μ 𝕜 e, f⟫_𝕜) • ContinuousMap.toLp 2 μ 𝕜 e := by
  rw [← continuousImage_toLp]
  have hImage : continuousImage μ (Spec.kernelTerm a e) f =
      ((a : 𝕜) * ⟪ContinuousMap.toLp 2 μ 𝕜 e, f⟫_𝕜) • e := by
    ext x
    rw [continuousImage_apply, continuous_inner_formula]
    simp only [Spec.kernelTerm, ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_const_mul]
    ring
  rw [hImage, map_smul]

/-- Bundling the already proved linear kernel assignment allows uniform
kernel sums to be compared with spectral sums on the actual L² quotient. -/
def continuousKernelAssignment : C(Q × Q, 𝕜) →L[𝕜] (Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) :=
  (ExpandedFA.PartV.L2KernelCompact.kernelAssignment μ μ).comp
    (ContinuousMap.toLp 2 (μ.prod μ) 𝕜)

lemma kernel_series_eq [μ.IsOpenPosMeasure] (k : C(Q × Q, 𝕜)) (D : Spec.SpectralData μ k)
    (hseries : Summable (fun j => Spec.kernelTerm (D.eigenvalue j) (D.eigenfunction j))) :
    (∑' j, Spec.kernelTerm (D.eigenvalue j) (D.eigenfunction j)) = k := by
  apply continuous_kernel_faithfulness μ
  apply ContinuousLinearMap.ext
  intro f
  have hs := (continuousKernelAssignment μ).hasSum hseries.hasSum
  have hf := (ContinuousLinearMap.apply 𝕜 (Lp 𝕜 2 μ) f).hasSum hs
  change HasSum (fun j => Spec.operator μ (Spec.kernelTerm (D.eigenvalue j) (D.eigenfunction j)) f)
    (Spec.operator μ (∑' j, Spec.kernelTerm (D.eigenvalue j) (D.eigenfunction j)) f) at hf
  simp only [kernelTerm_operator] at hf
  exact hf.unique (D.vector_expansion f)

end KernelSeries

/-- Convergence in C on a compact space is uniform convergence, for the
finite-subset partial sums used by HasSum. -/
lemma hasSum_uniform {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {G : Type*} [NormedAddCommGroup G] {ι : Type*}
    {F : ι → C(X, G)} {g : C(X, G)} (h : HasSum F g) :
    TendstoUniformly (fun s : Finset ι => fun x => ∑ i ∈ s, F i x) g atTop := by
  have ht : Tendsto (fun s : Finset ι => ∑ i ∈ s, F i) atTop (𝓝 g) := h
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht)
    Set.univ isCompact_univ
  simpa only [ContinuousMap.sum_apply, tendstoUniformlyOn_univ] using hu

/-- Conditional final assembly. The diagonal HasSum premise remains to be
established by positive-kernel localization and the feature-space Parseval proof. -/
theorem mercer_of_diagonal : Spec.MercerOfDiagonal.{u} := by
  intro Q 𝕜 _ _ _ _ _ μ _ _ k hk D hdiag
  let d : C(Q, ℝ) := ⟨fun x => RCLike.re (k (x,x)), by fun_prop⟩
  obtain ⟨hseries, habs⟩ := uniform_series_of_diagonal D.Index D.eigenvalue D.eigenfunction d
    (fun j => (D.positive j).le) hdiag
  have hsumk : HasSum (fun j => Spec.kernelTerm (D.eigenvalue j) (D.eigenfunction j)) k := by
    have h := hseries.hasSum
    rw [kernel_series_eq μ k D hseries] at h
    exact h
  have heval (x y : Q) := (ContinuousMap.evalCLM 𝕜 (x,y)).hasSum hsumk
  have hevalabs (p : Q × Q) := (ContinuousMap.evalCLM ℝ p).hasSum habs.hasSum
  have huniform := hasSum_uniform hsumk
  have hauniform := hasSum_uniform habs.hasSum
  have hsumvalue (p : Q × Q) :
      (∑' j, Spec.absoluteKernelTerm (D.eigenvalue j) (D.eigenfunction j)) p =
        ∑' j, ‖(D.eigenvalue j : 𝕜) * D.eigenfunction j p.1 * conj (D.eigenfunction j p.2)‖ :=
    (hevalabs p).tsum_eq.symm
  have hExp : Nonempty (Spec.Expansion μ k) := by
    refine ⟨{ toSpectralData := D, pointwise := ?_, absolute := ?_, uniform := ?_, absolute_uniform := ?_ }⟩
    · exact heval
    · intro x y
      exact (hevalabs (x,y)).summable
    · exact huniform
    · rw [show (⇑(∑' j, Spec.absoluteKernelTerm (D.eigenvalue j) (D.eigenfunction j))) =
          (fun p => ∑' j, ‖(D.eigenvalue j : 𝕜) * D.eigenfunction j p.1 *
            conj (D.eigenfunction j p.2)‖) from funext hsumvalue] at hauniform
      exact hauniform
  have hsum := eigenvalue_sum_of_diagonal μ k D hdiag
  obtain ⟨hclass, htrace⟩ := trace_of_summable_spectral_data μ k D hsum.summable
  refine ⟨hExp, hclass, ?_⟩
  rw [htrace, hsum.tsum_eq, ← integral_ofReal]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => (RCLike.conj_eq_iff_re.mp (hk x x).symm)

/-- Full support makes a zero L² kernel operator the zero continuous kernel.
The empty spectral family then proves all Mercer conclusions directly. -/
theorem zero_operator_case : Spec.ZeroOperatorCase.{u} := by
  intro Q 𝕜 _ _ _ _ _ μ _ _ k hK
  have hzero : Spec.operator (𝕜 := 𝕜) μ 0 = 0 := (continuousKernelAssignment μ).map_zero
  have hkzero : k = 0 := continuous_kernel_faithfulness μ (hK.trans hzero.symm)
  subst k
  let D : Spec.SpectralData (𝕜 := 𝕜) μ 0 := {
    Index := PEmpty
    countable := inferInstance
    eigenvalue := PEmpty.elim
    eigenfunction := PEmpty.elim
    positive := fun j => PEmpty.elim j
    orthonormal := by constructor <;> intro j <;> exact PEmpty.elim j
    eigen_equation := fun j => PEmpty.elim j
    vector_expansion := fun f => by rw [hzero]; exact hasSum_empty
  }
  apply mercer_of_diagonal μ 0 (fun x y => by simp) D
  intro x
  simpa only [ContinuousMap.zero_apply, RCLike.zero_re] using
    (hasSum_empty : HasSum (fun j => D.eigenvalue j * ‖D.eigenfunction j x‖ ^ 2) 0)

section Feature
variable {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
  [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
  (μ : Measure Q) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  (k : C(Q × Q, 𝕜)) (D : Spec.SpectralData μ k)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (J : H →L[𝕜] C(Q, 𝕜))
variable (I : H →L[𝕜] Lp 𝕜 2 μ)
  (hI : ∀ h, ContinuousMap.toLp 2 μ 𝕜 (J h) = I h)

include hI in
lemma diagonal_of_feature_factorization
    (hinj : Function.Injective I) (hfac : I.comp I.adjoint = Spec.operator μ k)
    (φ : Q → H) (hφ : ∀ x h, ⟪φ x, h⟫_𝕜 = J h x)
    (hdiag : ∀ x, ‖φ x‖ ^ 2 = RCLike.re (k (x,x))) :
    ∀ x, HasSum (fun j => D.eigenvalue j * ‖D.eigenfunction j x‖ ^ 2)
      (RCLike.re (k (x,x))) := by
  classical
  let e : D.Index → Lp 𝕜 2 μ := fun j => ContinuousMap.toLp 2 μ 𝕜 (D.eigenfunction j)
  let r : D.Index → ℝ := fun j => Real.sqrt (D.eigenvalue j)
  have hr (j) : 0 < r j := Real.sqrt_pos.2 (D.positive j)
  have hrsq (j) : r j * r j = D.eigenvalue j := Real.mul_self_sqrt (D.positive j).le
  let w : D.Index → H := fun j => ((r j : 𝕜)⁻¹) • I.adjoint (e j)
  have hfac' (f : Lp 𝕜 2 μ) : I (I.adjoint f) = Spec.operator μ k f :=
    DFunLike.congr_fun hfac f
  have hw (j) : I (w j) = (r j : 𝕜) • e j := by
    dsimp only [w]
    rw [map_smul, hfac', D.eigen_equation, smul_smul]
    congr 1
    have hr0 : (r j : 𝕜) ≠ 0 := by exact_mod_cast (hr j).ne'
    apply (mul_left_cancel₀ hr0)
    rw [← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
    exact_mod_cast (hrsq j).symm
  have hinner (i j) : ⟪w i, w j⟫_𝕜 =
      ((r i : 𝕜)⁻¹ * (r j : 𝕜)) * ⟪e i, e j⟫_𝕜 := by
    dsimp only [w]
    rw [inner_smul_left, map_inv₀, RCLike.conj_ofReal, ContinuousLinearMap.adjoint_inner_left]
    change (r i : 𝕜)⁻¹ * ⟪e i, I (w j)⟫_𝕜 = _
    rw [hw, inner_smul_right, mul_assoc]
  have hon : Orthonormal 𝕜 w := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner, (orthonormal_iff_ite.mp D.orthonormal)]
    split_ifs with hij
    · subst j
      rw [inv_mul_cancel₀ (by exact_mod_cast (hr i).ne'), mul_one]
    · rw [mul_zero]
  have htotal : (Submodule.span 𝕜 (Set.range w))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro h hh
    have hwe (j) : ⟪w j, h⟫_𝕜 = 0 :=
      ((Submodule.span 𝕜 (Set.range w)).mem_orthogonal h |>.mp hh) _ (Submodule.subset_span (Set.mem_range_self j))
    have heI (j) : ⟪e j, I h⟫_𝕜 = 0 := by
      have hh' := hwe j
      dsimp only [w] at hh'
      rw [inner_smul_left, map_inv₀, RCLike.conj_ofReal,
        ContinuousLinearMap.adjoint_inner_left] at hh'
      exact (mul_eq_zero.mp hh').resolve_left (inv_ne_zero (by exact_mod_cast (hr j).ne'))
    have hKI : Spec.operator μ k (I h) = 0 := by
      have hsum := D.vector_expansion (I h)
      simp only [show ∀ j, ⟪ContinuousMap.toLp 2 μ 𝕜 (D.eigenfunction j), I h⟫_𝕜 = 0 from heI,
        mul_zero, zero_smul] at hsum
      exact hsum.unique (hasSum_zero : HasSum (fun _ : D.Index => (0 : Lp 𝕜 2 μ)) 0)
    have hSI : I.adjoint (I h) = 0 := by
      apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
      rw [ContinuousLinearMap.adjoint_inner_left, hfac', hKI, inner_zero_right]
    have hI : I h = 0 := by
      apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
      rw [← ContinuousLinearMap.adjoint_inner_right, hSI, inner_zero_right]
    simpa only [Submodule.mem_bot] using hinj (hI.trans (map_zero I).symm)
  let b : HilbertBasis D.Index 𝕜 H := HilbertBasis.mkOfOrthogonalEqBot hon htotal
  have hb (j) : b j = w j := congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hon htotal) j
  have hJw (j) : J (w j) = (r j : 𝕜) • D.eigenfunction j := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := 𝕜) μ
    rw [hI]
    exact (hw j).trans (map_smul (ContinuousMap.toLp 2 μ 𝕜) (r j : 𝕜) (D.eigenfunction j)).symm
  intro x
  have hs := (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).hasSum (b.hasSum_inner_mul_inner (φ x) (φ x))
  simp only [RCLike.reCLM_apply] at hs
  have hterm (j) : RCLike.re (⟪φ x, b j⟫_𝕜 * ⟪b j, φ x⟫_𝕜) =
      D.eigenvalue j * ‖D.eigenfunction j x‖ ^ 2 := by
    rw [hb, ← inner_conj_symm (w j) (φ x), hφ, hJw]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re, norm_mul, RCLike.norm_ofReal,
      abs_of_pos (hr j), mul_pow]
    congr 1
    simpa only [sq] using hrsq j
  simpa only [hterm, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re, hdiag] using hs
end Feature

section KernelHilbert
variable {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
  [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]

def scalarKernel (k : C(Q × Q, 𝕜)) : Matrix Q Q (𝕜 →L[𝕜] 𝕜) :=
  fun x y => k (x,y) • ContinuousLinearMap.id 𝕜 𝕜

lemma scalarKernel_posSemidef (k : C(Q × Q, 𝕜))
    (hk : Spec.Hermitian k) (hpos : Spec.KernelPositiveSemidefinite k) :
    (scalarKernel k).PosSemidef := by
  change ∀ x y, k (x,y) = conj (k (y,x)) at hk
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  constructor
  · apply Matrix.IsHermitian.ext
    intro x y
    simp only [scalarKernel, ContinuousLinearMap.star_eq_adjoint,
      map_smulₛₗ, ContinuousLinearMap.adjoint_id]
    rw [← hk x y]
  · intro c
    simpa only [scalarKernel, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, RCLike.inner_apply', map_mul, ← hk,
      mul_assoc, mul_comm, mul_left_comm] using hpos c

variable (k : C(Q × Q, 𝕜)) [Fact (scalarKernel k).PosSemidef]

abbrev KernelHilbert := RKHS.OfKernel (scalarKernel k)

lemma kernelHilbert_continuous : Continuous
    (fun p : Q × Q => RKHS.kernel (KernelHilbert k) p.1 p.2) := by
  simp only [RKHS.OfKernel.kernel_ofKernel, scalarKernel]
  fun_prop

/-- Elements of the kernel Hilbert space as continuous functions. -/
def kernelHilbertToContinuous : KernelHilbert k →L[𝕜] C(Q, 𝕜) :=
  let ev : C(Q, KernelHilbert k →L[𝕜] 𝕜) :=
    ⟨RKHS.eval (KernelHilbert k),
      (RKHS.continuous_kernel_iff_continuous_eval (KernelHilbert k)).mp
        (kernelHilbert_continuous k)⟩
  LinearMap.mkContinuous {
    toFun := fun h => ⟨h, RKHS.continuous_of_continuous_kernel (kernelHilbert_continuous k) h⟩
    map_add' := fun h g => by ext x; exact congrFun (RKHS.coe_add h g) x
    map_smul' := fun a h => by ext x; exact congrFun (RKHS.coe_smul h a) x
  } ‖ev‖ (fun h => by
    change ‖(⟨h, RKHS.continuous_of_continuous_kernel (kernelHilbert_continuous k) h⟩ : C(Q, 𝕜))‖ ≤ ‖ev‖ * ‖h‖
    apply (ContinuousMap.norm_le (⟨h, RKHS.continuous_of_continuous_kernel (kernelHilbert_continuous k) h⟩ : C(Q, 𝕜))
      (mul_nonneg (norm_nonneg ev) (norm_nonneg h))).mpr
    intro x
    change ‖RKHS.eval (KernelHilbert k) x h‖ ≤ ‖ev‖ * ‖h‖
    exact ((RKHS.eval (KernelHilbert k) x).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (ev.norm_coe_le_norm x) (norm_nonneg h)))

@[simp] lemma kernelHilbertToContinuous_apply (h : KernelHilbert k) (x : Q) :
    kernelHilbertToContinuous k h x = h x := rfl

lemma kernelHilbertToContinuous_injective : Function.Injective (kernelHilbertToContinuous k) := by
  intro h g hh
  apply RKHS.ext
  intro x
  exact congrArg (fun f : C(Q, 𝕜) => f x) hh

variable (μ : Measure Q) [IsFiniteMeasure μ]

def kernelHilbertInclusion : KernelHilbert k →L[𝕜] Lp 𝕜 2 μ :=
  (ContinuousMap.toLp 2 μ 𝕜).comp (kernelHilbertToContinuous k)

lemma kernelHilbertInclusion_injective [μ.IsOpenPosMeasure] :
    Function.Injective (kernelHilbertInclusion k μ) :=
  (ContinuousMap.toLp_injective (p := 2) (𝕜 := 𝕜) μ).comp
    (kernelHilbertToContinuous_injective k)

lemma kernelHilbert_adjoint_image (hk : Spec.Hermitian k) (f : Lp 𝕜 2 μ) :
    kernelHilbertToContinuous k ((kernelHilbertInclusion k μ).adjoint f) =
      continuousImage μ k f := by
  ext x
  rw [kernelHilbertToContinuous_apply]
  have heval : ⟪RKHS.kerFun (KernelHilbert k) x (1 : 𝕜),
      (kernelHilbertInclusion k μ).adjoint f⟫_𝕜 =
      ((kernelHilbertInclusion k μ).adjoint f) x := by simp
  rw [← heval]
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪ContinuousMap.toLp 2 μ 𝕜
    (kernelHilbertToContinuous k (RKHS.kerFun (KernelHilbert k) x 1)), f⟫_𝕜 = _
  rw [continuous_inner_formula, continuousImage_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [kernelHilbertToContinuous_apply, RKHS.kerFun_apply,
      RKHS.OfKernel.kernel_ofKernel, scalarKernel, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
    rw [← hk x y]

lemma kernelHilbert_factorization (hk : Spec.Hermitian k) :
    (kernelHilbertInclusion k μ).comp (kernelHilbertInclusion k μ).adjoint = Spec.operator μ k := by
  apply ContinuousLinearMap.ext
  intro f
  change ContinuousMap.toLp 2 μ 𝕜
    (kernelHilbertToContinuous k ((kernelHilbertInclusion k μ).adjoint f)) = _
  rw [kernelHilbert_adjoint_image k μ hk, continuousImage_toLp]

lemma kernelHilbert_diagonal (x : Q) :
    ‖RKHS.kerFun (KernelHilbert k) x (1 : 𝕜)‖ ^ 2 = RCLike.re (k (x,x)) := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), RKHS.kerFun_inner]
  simp [RKHS.kerFun_apply, scalarKernel, RCLike.inner_apply']

end KernelHilbert

theorem diagonal_of_positive_kernel : Spec.DiagonalOfPositiveKernel := by
  intro Q 𝕜 _ _ _ _ _ μ _ _ k hk hpos D
  letI : Fact (scalarKernel k).PosSemidef := ⟨scalarKernel_posSemidef k hk hpos⟩
  apply diagonal_of_feature_factorization μ k D (kernelHilbertToContinuous k)
    (kernelHilbertInclusion k μ) (fun _ => rfl)
    (kernelHilbertInclusion_injective k μ) (kernelHilbert_factorization k μ hk)
    (fun x => RKHS.kerFun (KernelHilbert k) x (1 : 𝕜))
  · intro x h
    simp
  · exact kernelHilbert_diagonal k

/- Localization transfers operator positivity to the finite kernel matrices. -/
section Localization
variable {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
  [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]

/-- Averaging over a positive finite-measure set preserves a uniform error bound. -/
lemma normalized_setIntegral_error (μ : Measure Q) [IsFiniteMeasure μ]
    (f : C(Q, 𝕜)) {s : Set Q} (hs0 : μ s ≠ 0) (c : 𝕜) {ε : ℝ}
    (hε : ∀ y ∈ s, ‖f y - c‖ ≤ ε) :
    ‖(μ.real s)⁻¹ • (∫ y in s, f y ∂μ) - c‖ ≤ ε := by
  have hm : 0 < μ.real s := ENNReal.toReal_pos hs0 (measure_ne_top μ s)
  have hi : IntegrableOn (fun y => f y) s μ :=
    ((f.memLp (p := 1) μ 𝕜).integrable le_rfl).integrableOn
  have heq : (μ.real s)⁻¹ • (∫ y in s, f y ∂μ) - c =
      (μ.real s)⁻¹ • (∫ y in s, f y - c ∂μ) := by
    rw [integral_sub hi (integrable_const c), integral_const]
    simp [smul_sub, smul_smul, hm.ne']
  rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hm.le)]
  calc
    (μ.real s)⁻¹ * ‖∫ y in s, f y - c ∂μ‖ ≤
        (μ.real s)⁻¹ * (ε * μ.real s) :=
      mul_le_mul_of_nonneg_left
        (norm_setIntegral_le_of_norm_le_const (measure_lt_top μ s) hε)
        (inv_nonneg.mpr hm.le)
    _ = ε := by field_simp

/-- Full support makes shrinking-ball averages converge to every continuous value. -/
lemma normalized_ball_integral_tendsto (μ : Measure Q) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (f : C(Q, 𝕜)) (x : Q) :
    Tendsto (fun r : ℝ => (μ.real (Metric.ball x r))⁻¹ •
      (∫ y in Metric.ball x r, f y ∂μ)) (𝓝[>] 0) (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt (ε / 2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono inf_le_left] with r hr hrd
  have hb0 : μ (Metric.ball x r) ≠ 0 := (Metric.measure_ball_pos μ x hr).ne'
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (normalized_setIntegral_error μ f hb0 (f x) ?_) (half_lt_self hε)
  intro y hy
  simpa only [dist_eq_norm] using (hδf (lt_trans (Metric.mem_ball.mp hy) hrd)).le

/-- Product balls give the corresponding convergence of the double kernel averages. -/
lemma normalized_kernel_integral_tendsto (μ : Measure Q) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (k : C(Q × Q, 𝕜)) (x y : Q) :
    Tendsto (fun r : ℝ => (μ.real (Metric.ball x r))⁻¹ •
      ((μ.real (Metric.ball y r))⁻¹ •
        (∫ u in Metric.ball x r, ∫ v in Metric.ball y r, k (u,v) ∂μ ∂μ)))
      (𝓝[>] 0) (𝓝 (k (x,y))) := by
  have H := normalized_ball_integral_tendsto (μ.prod μ) k (x,y)
  convert H using 1
  funext r
  have hF : (∫ z in Metric.ball (x,y) r, k z ∂μ.prod μ) =
      ∫ u in Metric.ball x r, ∫ v in Metric.ball y r, k (u,v) ∂μ ∂μ := by
    rw [← ball_prod_same, ← Measure.prod_restrict]
    exact integral_prod k ((k.memLp (p := 1) _ 𝕜).integrable le_rfl)
  rw [hF, ← ball_prod_same, measureReal_prod_prod, mul_inv, mul_smul]


variable (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜))

/-- The L² function of integral one supported on a ball of positive radius. -/
def normalizedIndicator (x : Q) (r : ℝ) : Lp 𝕜 2 μ :=
  ((μ.real (Metric.ball x r))⁻¹ : 𝕜) •
    indicatorConstLp (s := Metric.ball x r) 2 Metric.isOpen_ball.measurableSet (measure_ne_top μ _) (1 : 𝕜)

lemma indicator_operator (s t : Set Q) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ⟪indicatorConstLp 2 hs (measure_ne_top μ s) (1 : 𝕜),
      Spec.operator μ k (indicatorConstLp 2 ht (measure_ne_top μ t) 1)⟫_𝕜 =
      ∫ x in s, ∫ y in t, k (x,y) ∂μ ∂μ := by
  rw [L2.inner_indicatorConstLp_one, ← continuousImage_toLp]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) μ
    (continuousImage μ k (indicatorConstLp 2 ht (measure_ne_top μ t) 1)))] with x hx
  rw [hx, continuousImage_apply]
  rw [← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ) (s := t) (hs := ht)
    (hμs := measure_ne_top μ t) (c := (1 : 𝕜))] with y hy
  rw [hy]
  by_cases hy' : y ∈ t <;> simp [hy']

lemma normalizedIndicator_operator (x y : Q) (r : ℝ) :
    ⟪normalizedIndicator (𝕜 := 𝕜) μ x r,
      Spec.operator μ k (normalizedIndicator (𝕜 := 𝕜) μ y r)⟫_𝕜 =
      (μ.real (Metric.ball x r))⁻¹ • (μ.real (Metric.ball y r))⁻¹ •
        (∫ a in Metric.ball x r, ∫ b in Metric.ball y r, k (a,b) ∂μ ∂μ) := by
  simp only [normalizedIndicator, map_smul, inner_smul_left, inner_smul_right,
    map_inv₀, RCLike.conj_ofReal, indicator_operator]
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv]
  ring


/-- Finite linear combinations pass quadratic positivity through the Gram limits. -/
lemma kernel_positive_of_gram_limit
    (hpos : Spec.Positive μ k) (v : Q → ℝ → Lp 𝕜 2 μ)
    (hv : ∀ x y, Tendsto
      (fun r => ⟪v x r, Spec.operator μ k (v y r)⟫_𝕜)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (k (x,y)))) :
    Spec.KernelPositiveSemidefinite k := by
  classical
  intro c
  let F : ℝ → 𝕜 := fun r => c.sum fun x a =>
    c.sum fun y b => conj a * ⟪v x r, Spec.operator μ k (v y r)⟫_𝕜 * b
  have hF : Tendsto F (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (c.sum fun x a => c.sum fun y b => conj a * k (x,y) * b)) := by
    apply tendsto_finsetSum c.support
    intro x hx
    apply tendsto_finsetSum c.support
    intro y hy
    exact (tendsto_const_nhds.mul (hv x y)).mul tendsto_const_nhds
  have hnonneg (r : ℝ) : 0 ≤ RCLike.re (F r) := by
    have heq : F r = ⟪c.sum (fun x a => a • v x r),
        Spec.operator μ k (c.sum fun x a => a • v x r)⟫_𝕜 := by
      simp only [F, Finsupp.sum, map_sum, map_smul, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    rw [heq]
    exact hpos _
  exact ge_of_tendsto' (RCLike.continuous_re.tendsto _ |>.comp hF) hnonneg


lemma kernel_positive_of_operator [μ.IsOpenPosMeasure] (hpos : Spec.Positive μ k) :
    Spec.KernelPositiveSemidefinite k := by
  apply kernel_positive_of_gram_limit μ k hpos (normalizedIndicator μ)
  intro x y
  simpa only [normalizedIndicator_operator] using normalized_kernel_integral_tendsto μ k x y

end Localization

/-- Mercer expansion with absolute uniform convergence and the canonical trace identity. -/
theorem mercer : Spec.Mercer.{u} := by
  intro Q 𝕜 _ _ _ _ _ μ _ _ k hk hpos
  obtain ⟨D⟩ := continuous_spectral_data μ k hk hpos
  exact mercer_of_diagonal μ k hk D
    (diagonal_of_positive_kernel μ k hk (kernel_positive_of_operator μ k hpos) D)

end ExpandedFA.IntegralOperators.MercerExpansion
