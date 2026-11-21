import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2KernelCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2Kernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompactIdeal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Tactic.Ring

/-! Product L² density, finite-rank approximation, and the Hilbert adjoint.
The density proof uses uniqueness of vector measures on finite rectangles,
then a sigma-finite exhaustion. No countable-generation assumption is used. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure MeasurableSpace Set Filter RCLike
open scoped ENNReal InnerProductSpace ComplexConjugate Topology
universe u v
namespace ExpandedFA.PartV.L2KernelCompact

open L2Kernel (kernelOperator)
variable {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [RCLike 𝕜] {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

lemma kernelOperator_coe (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)) (u : Lp 𝕜 2 ν) :
    (kernelOperator μ ν k u : X → 𝕜) =ᵐ[μ] fun x => ∫ y, k (x,y) * u y ∂ν := by
  change (L2KernelSpec.OperatorValue μ ν k u : X → 𝕜) =ᵐ[μ] _
  rw [L2Kernel.canonical_eq_integralOperator]
  exact L2Kernel.integralOperator_ae k u

/-- Vanishing of rectangle integrals determines a locally integrable L² function. -/
theorem eq_zero_of_rectangle_integrals (f : Lp 𝕜 2 (μ.prod ν))
    (hf : ∀ (B : Set X) (C : Set Y), MeasurableSet B → MeasurableSet C →
      μ B ≠ ∞ → ν C ≠ ∞ → ∫ z in B ×ˢ C, f z ∂(μ.prod ν) = 0) : f = 0 := by
  have hblock (B : Set X) (C : Set Y) (hB : MeasurableSet B) (hC : MeasurableSet C)
      (hμB : μ B ≠ ∞) (hνC : ν C ≠ ∞) :
      f =ᵐ[(μ.prod ν).restrict (B ×ˢ C)] 0 := by
    have hfin : (μ.prod ν) (B ×ˢ C) ≠ ∞ := by
      rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμB hνC
    have hi : Integrable f ((μ.prod ν).restrict (B ×ˢ C)) :=
      integrableOn_Lp_of_measure_ne_top f (by norm_num) hfin
    have hv : ((μ.prod ν).restrict (B ×ˢ C)).withDensityᵥ f = 0 := by
      refine VectorMeasure.ext_of_generateFrom _ ?_ generateFrom_prod.symm
        isPiSystem_prod ?_
      · rintro _ ⟨S, hS, T, hT, rfl⟩
        rw [withDensityᵥ_apply hi (hS.prod hT), Measure.restrict_restrict (hS.prod hT)]
        rw [prod_inter_prod]
        exact hf (S ∩ B) (T ∩ C) (hS.inter hB) (hT.inter hC)
          (measure_ne_top_of_subset inter_subset_right hμB)
          (measure_ne_top_of_subset inter_subset_right hνC)
      · rw [withDensityᵥ_apply hi MeasurableSet.univ, Measure.restrict_univ]
        exact hf B C hB hC hμB hνC
    exact hi.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
      (by simpa only [withDensityᵥ_zero] using hv)
  have hz : ∀ᵐ z ∂(μ.prod ν), f z = 0 := by
    have hn (n : ℕ) : ∀ᵐ z ∂(μ.prod ν),
        z ∈ spanningSets μ n ×ˢ spanningSets ν n → f z = 0 := by
      exact (ae_restrict_iff' ((measurableSet_spanningSets μ n).prod
        (measurableSet_spanningSets ν n))).mp
        (hblock _ _ (measurableSet_spanningSets μ n) (measurableSet_spanningSets ν n)
          (measure_spanningSets_lt_top μ n).ne (measure_spanningSets_lt_top ν n).ne)
    filter_upwards [ae_all_iff.mpr hn] with z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp (show z.1 ∈ ⋃ n, spanningSets μ n by simp)
    obtain ⟨m, hm⟩ := mem_iUnion.mp (show z.2 ∈ ⋃ m, spanningSets ν m by simp)
    exact hz (max n m) ⟨(monotone_spanningSets μ (le_max_left n m)) hn,
      (monotone_spanningSets ν (le_max_right n m)) hm⟩
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero 𝕜 2 (μ.prod ν)] with z hz hzero
  exact hz.trans hzero.symm

/-- Density of the algebraic span follows by showing its orthogonal complement is zero. -/
theorem tensor_density : L2KernelCompactSpec.TensorDensity.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  change f = 0
  apply eq_zero_of_rectangle_integrals f
  intro B C hB hC hμB hνC
  have hfin : (μ.prod ν) (B ×ˢ C) ≠ ∞ := by
    rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμB hνC
  rw [← L2.inner_indicatorConstLp_one (𝕜 := 𝕜) (hB.prod hC) hfin]
  apply Submodule.inner_right_of_mem_orthogonal (K := Submodule.span 𝕜
    (L2KernelCompactSpec.rectangles 𝕜 μ ν)) _ hf
  apply Submodule.subset_span
  exact ⟨B, C, hB, hC, hμB, hνC, rfl⟩


variable (μ ν)

theorem kernelOperator_add (k h : Lp 𝕜 2 (μ.prod ν)) :
    kernelOperator μ ν (k + h) = kernelOperator μ ν k + kernelOperator μ ν h := by
  ext1 f
  apply Lp.ext
  filter_upwards [kernelOperator_coe μ ν (k+h) f, kernelOperator_coe μ ν k f,
    kernelOperator_coe μ ν h f, Lp.coeFn_add (kernelOperator μ ν k f) (kernelOperator μ ν h f),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add k h), L2Kernel.kernel_sections μ ν k (Lp.memLp k),
    L2Kernel.kernel_sections μ ν h (Lp.memLp h)] with x hsum hk hh hadd hkh hks hhs
  change kernelOperator μ ν (k+h) f x = (kernelOperator μ ν k f + kernelOperator μ ν h f) x
  rw [hsum, hadd, Pi.add_apply, hk, hh]
  calc
    _ = ∫ y, k (x,y) * f y + h (x,y) * f y ∂ν := by
      apply integral_congr_ae
      filter_upwards [hkh] with y hy
      rw [hy, Pi.add_apply, add_mul]
    _ = _ := integral_add (hks.integrable_mul (Lp.memLp f))
      (hhs.integrable_mul (Lp.memLp f))

theorem kernelOperator_smul (c : 𝕜) (k : Lp 𝕜 2 (μ.prod ν)) :
    kernelOperator μ ν (c • k) = c • kernelOperator μ ν k := by
  ext1 f
  apply Lp.ext
  filter_upwards [kernelOperator_coe μ ν (c • k) f, kernelOperator_coe μ ν k f,
    Lp.coeFn_smul c (kernelOperator μ ν k f),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c k)] with x hck hk hc hcks
  change kernelOperator μ ν (c • k) f x = (c • kernelOperator μ ν k f) x
  rw [hck, hc, Pi.smul_apply, hk]
  calc
    _ = ∫ y, c • (k (x,y) * f y) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hcks] with y hy
      rw [hy, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
    _ = _ := integral_smul c _

/-- A bundled form of kernel linearity, with no change to the selected operator. -/
def kernelAssignment : Lp 𝕜 2 (μ.prod ν) →L[𝕜] (Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ) :=
  LinearMap.mkContinuous
    { toFun := kernelOperator μ ν
      map_add' := kernelOperator_add μ ν
      map_smul' := kernelOperator_smul μ ν }
    1 (fun k => by
      change ‖kernelOperator μ ν k‖ ≤ 1 * ‖k‖
      simpa only [one_mul, L2Kernel.kernelOperator] using L2Kernel.kernel_norm_bound μ ν k)

/-- The actual rank-one formula for a rectangle kernel. -/
theorem kernelOperator_rectangle (B : Set X) (C : Set Y) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hμB : μ B ≠ ∞) (hνC : ν C ≠ ∞) (f : Lp 𝕜 2 ν) :
    kernelOperator μ ν (indicatorConstLp 2 (hB.prod hC)
      (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμB hνC) (1 : 𝕜)) f =
    (∫ y in C, f y ∂ν) • indicatorConstLp 2 hB hμB (1 : 𝕜) := by
  have hprod : (μ.prod ν) (B ×ˢ C) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hμB hνC
  have hrect : (indicatorConstLp 2 (hB.prod hC) hprod (1 : 𝕜) : X × Y → 𝕜) =ᵐ[μ.prod ν]
      (B ×ˢ C).indicator (fun _ => (1 : 𝕜)) := indicatorConstLp_coeFn
  apply Lp.ext
  filter_upwards [kernelOperator_coe μ ν _ f,
    Measure.ae_ae_of_ae_prod hrect,
    Lp.coeFn_smul (∫ y in C, f y ∂ν) (indicatorConstLp 2 hB hμB (1 : 𝕜)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hB) (hμs := hμB) (c := (1 : 𝕜))]
    with x hx hrect hsmul hbind
  rw [hx, hsmul, Pi.smul_apply, hbind]
  calc
    _ = ∫ y, (B ×ˢ C).indicator (fun _ => (1 : 𝕜)) (x,y) * f y ∂ν := by
      apply integral_congr_ae
      filter_upwards [hrect] with y hy
      rw [hy]
    _ = _ := by
      by_cases hxB : x ∈ B
      · rw [Set.indicator_of_mem hxB, smul_eq_mul, mul_one]
        calc
          _ = ∫ y, C.indicator (fun y => f y) y ∂ν := by
            apply integral_congr_ae
            apply Eventually.of_forall
            intro y
            change (B ×ˢ C).indicator (fun _ => (1 : 𝕜)) (x,y) * f y =
              C.indicator (fun y => f y) y
            by_cases hy : y ∈ C
            · rw [Set.indicator_of_mem (show (x,y) ∈ B ×ˢ C from ⟨hxB, hy⟩), Set.indicator_of_mem hy, one_mul]
            · rw [Set.indicator_of_notMem (show (x,y) ∉ B ×ˢ C from fun h => hy h.2),
                Set.indicator_of_notMem hy, zero_mul]
          _ = _ := integral_indicator hC
      · rw [Set.indicator_of_notMem hxB, smul_zero]
        calc
          _ = ∫ _y : Y, (0 : 𝕜) ∂ν := by
            apply integral_congr_ae
            apply Eventually.of_forall
            intro y
            change (B ×ˢ C).indicator (fun _ => (1 : 𝕜)) (x,y) * f y = 0
            rw [Set.indicator_of_notMem (show (x,y) ∉ B ×ˢ C from fun h => hxB h.1),
              zero_mul]
          _ = 0 := integral_zero _ _

/-- Finite rank holds on the whole algebraic span, including the empty sum. -/
theorem l2_kernel_rectangle_finite_rank : ∀ (k : Lp 𝕜 2 (μ.prod ν)),
    k ∈ Submodule.span 𝕜 (L2KernelCompactSpec.rectangles 𝕜 μ ν) →
    FiniteDimensional 𝕜 (LinearMap.range (kernelOperator μ ν k).toLinearMap) := by
  intro k hk
  let A := kernelAssignment (𝕜 := 𝕜) μ ν
  change FiniteDimensional 𝕜 (LinearMap.range (A k).toLinearMap)
  induction hk using Submodule.span_induction with
  | mem k hk =>
    rcases hk with ⟨B, C, hB, hC, hμB, hνC, rfl⟩
    apply Submodule.finiteDimensional_of_le (S₂ := 𝕜 ∙ indicatorConstLp 2 hB hμB (1 : 𝕜))
    rintro _ ⟨f, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨∫ y in C, f y ∂ν,
      (kernelOperator_rectangle μ ν B C hB hC hμB hνC f).symm⟩
  | zero =>
    rw [map_zero, ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]
    infer_instance
  | add a b ha hb hfa hfb =>
    let := hfa
    let := hfb
    rw [map_add, ContinuousLinearMap.toLinearMap_add]
    exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le _ _)
  | smul c a ha hfa =>
    let := hfa
    rw [map_smul, ContinuousLinearMap.toLinearMap_smul]
    exact Submodule.finiteDimensional_of_le (LinearMap.range_smul_le_range _ _)

/-- The accepted rectangle density produces simultaneous kernel/operator
approximations, using continuity of the contractive linear assignment. -/
theorem l2_kernel_operator_approximation : L2KernelCompactSpec.OperatorApproximation.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k
  obtain ⟨kn, hkn, hlim⟩ := mem_closure_iff_seq_limit.mp (tensor_density μ ν k)
  exact ⟨kn, hkn, fun n => l2_kernel_rectangle_finite_rank μ ν (kn n) (hkn n),
    hlim, (kernelAssignment μ ν).continuous.continuousAt.tendsto.comp hlim⟩


/-- Bounded finite rank maps are compact in their original target. -/
lemma finite_rank_compact {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F)
    (hT : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)) :
    ExpandedFA.Compactness.IsCompactLinearMap T.toLinearMap := by
  let := hT
  let : LocallyCompactSpace (LinearMap.range T.toLinearMap) :=
    .of_finiteDimensional_of_complete 𝕜 _
  have h : IsCompactOperator T.rangeRestrict :=
    isCompactOperator_of_locallyCompactSpace_dom T.rangeRestrict
  exact (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr
    (h.continuous_comp continuous_subtype_val)

theorem kernel_compact : L2KernelCompactSpec.Compact.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k
  obtain ⟨kn, _, hfin, _, hlim⟩ := l2_kernel_operator_approximation μ ν k
  exact ExpandedFA.Compactness.compact_of_operatorNorm_tendsto
    (fun n => kernelOperator μ ν (kn n)) (kernelOperator μ ν k)
    (fun n => finite_rank_compact _ (hfin n))
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim)

theorem dagger_coe (k : Lp 𝕜 2 (μ.prod ν)) :
    (L2KernelCompactSpec.dagger μ ν k : Y × X → 𝕜) =ᵐ[ν.prod μ]
      (fun p => conj (k p.swap)) := by
  have hs := (measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_star k)
  exact (Lp.coeFn_compMeasurePreserving (star k) measurePreserving_swap).trans hs

theorem dagger_norm (k : Lp 𝕜 2 (μ.prod ν)) :
    ‖L2KernelCompactSpec.dagger μ ν k‖ = ‖k‖ := by
  change ‖Lp.compMeasurePreserving Prod.swap measurePreserving_swap (star k)‖ = ‖k‖
  rw [Lp.norm_compMeasurePreserving]
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star k), eLpNorm_star]

/-- The tensor product of two L² representatives is L² on the product, with
factorized norm. This uses integrability of the squared norms, not finite mass. -/
theorem memLp_tensor (v : Lp 𝕜 2 μ) (u : Lp 𝕜 2 ν) :
    ∃ ht : MemLp (fun p : X × Y => conj (v p.1) * u p.2) 2 (μ.prod ν),
      ‖ht.toLp _‖ = ‖v‖ * ‖u‖ := by
  have hm := (Lp.aestronglyMeasurable v).comp_fst.star.mul (Lp.aestronglyMeasurable u).comp_snd
  have hv : Integrable (fun x => ‖v x‖ ^ 2) μ ∧
      (∫ x, ‖v x‖ ^ 2 ∂μ) = ‖v‖ ^ 2 :=
    ⟨(memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v),
      by simpa only [Lp.toLp_coeFn] using L2Kernel.integral_sq_norm v (Lp.memLp v)⟩
  have hu : Integrable (fun y => ‖u y‖ ^ 2) ν ∧
      (∫ y, ‖u y‖ ^ 2 ∂ν) = ‖u‖ ^ 2 :=
    ⟨(memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u),
      by simpa only [Lp.toLp_coeFn] using L2Kernel.integral_sq_norm u (Lp.memLp u)⟩
  have he (p : X × Y) : ‖conj (v p.1) * u p.2‖ ^ 2 =
      ‖v p.1‖ ^ 2 * ‖u p.2‖ ^ 2 := by rw [norm_mul, norm_conj, mul_pow]
  have ht : MemLp (fun p : X × Y => conj (v p.1) * u p.2) 2 (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hm).mpr (by
      change Integrable (fun p : X × Y => ‖conj (v p.1) * u p.2‖ ^ 2) (μ.prod ν)
      simp_rw [he]
      exact hv.1.mul_prod hu.1)
  refine ⟨ht, ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [← L2Kernel.integral_sq_norm _ ht]
  simp_rw [he]
  rw [integral_prod_mul (fun x => ‖v x‖ ^ 2) (fun y => ‖u y‖ ^ 2),
    hv.2, hu.2, mul_pow]

/-- Product-space Cauchy–Schwarz bounds the integral of the absolute value. -/
theorem integral_norm_mul_bound {Z : Type*} [MeasurableSpace Z]
    {ρ : Measure Z} {f g : Z → 𝕜} (hf : MemLp f 2 ρ) (hg : MemLp g 2 ρ) :
    Integrable (fun z => f z * g z) ρ ∧
    (∫ z, ‖f z * g z‖ ∂ρ) ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  refine ⟨hf.integrable_mul hg, ?_⟩
  have hb := (by
    rw [← ExpandedFA.FunctionSpaces.lp_pairing_on_representatives ρ 2 2
      (fun z => ‖f z‖) (fun z => ‖g z‖) hf.norm hg.norm]
    exact ExpandedFA.FunctionSpaces.lp_pairing_apply_bound ρ 2 2
      (hg.norm.toLp _) (hf.norm.toLp _) :
      ‖∫ z, ‖f z‖ * ‖g z‖ ∂ρ‖ ≤ ‖hg.norm.toLp _‖ * ‖hf.norm.toLp _‖)
  rw [Real.norm_of_nonneg (integral_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    at hb
  rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm _ hf.aestronglyMeasurable,
    eLpNorm_norm _ hg.aestronglyMeasurable, ← Lp.norm_toLp, ← Lp.norm_toLp] at hb
  simpa only [norm_mul, mul_comm] using hb

theorem l2_kernel_triple_bound : L2KernelCompactSpec.TripleBound.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k v u
  obtain ⟨ht, hnorm⟩ := memLp_tensor μ ν v u
  have hb := integral_norm_mul_bound (Lp.memLp k) ht
  have he : (fun p : X × Y => k p * (conj (v p.1) * u p.2)) =
      (fun p : X × Y => conj (v p.1) * k p * u p.2) := by
    funext p
    ring
  rw [he, Lp.toLp_coeFn, hnorm, ← mul_assoc] at hb
  refine ⟨hb.1, ?_⟩
  have hei : (∫ p : X × Y, ‖conj (v p.1) * k p * u p.2‖ ∂μ.prod ν) =
      ∫ p : X × Y, ‖k p * (conj (v p.1) * u p.2)‖ ∂μ.prod ν := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => congrArg norm (congrFun he p).symm)
  rw [hei]
  exact hb.2

/-- The swapped kernel integral on the original representative. -/
theorem dagger_apply_coe (k : Lp 𝕜 2 (μ.prod ν)) (v : Lp 𝕜 2 μ) :
    (kernelOperator ν μ (L2KernelCompactSpec.dagger μ ν k) v : Y → 𝕜) =ᵐ[ν]
      (fun y => ∫ x, conj (k (x,y)) * v x ∂μ) := by
  exact (kernelOperator_coe ν μ (L2KernelCompactSpec.dagger μ ν k) v).trans
    (L2Kernel.kernel_representative_independence ν μ _ _ _ _
      (dagger_coe μ ν k) (EventuallyEq.rfl))

theorem dagger_integrable (k : Lp 𝕜 2 (μ.prod ν)) (v : Lp 𝕜 2 μ) :
    ∀ᵐ y ∂ν, Integrable (fun x => conj (k (x,y)) * v x) μ := by
  have hd := (Lp.memLp k).star.comp_measurePreserving
    (measurePreserving_swap (μ := ν) (ν := μ))
  filter_upwards [L2Kernel.kernel_sections ν μ _ hd] with y hy
  exact hy.integrable_mul (Lp.memLp v)

/-- The globally integrable product justifies the interchange in the
conjugate-first pairing, for arbitrary sigma-finite measures. -/
theorem l2Kernel_adjoint_pairing (k : Lp 𝕜 2 (μ.prod ν))
    (v : Lp 𝕜 2 μ) (u : Lp 𝕜 2 ν) :
    ⟪v, kernelOperator μ ν k u⟫_𝕜 =
      ⟪kernelOperator ν μ (L2KernelCompactSpec.dagger μ ν k) v, u⟫_𝕜 := by
  have hl : ⟪v, kernelOperator μ ν k u⟫_𝕜 =
      ∫ x, ∫ y, conj (v x) * k (x,y) * u y ∂ν ∂μ := by
    simp only [L2.inner_def, RCLike.inner_apply']
    apply integral_congr_ae
    filter_upwards [kernelOperator_coe μ ν k u] with x hx
    rw [hx]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have hr : ⟪kernelOperator ν μ (L2KernelCompactSpec.dagger μ ν k) v, u⟫_𝕜 =
      ∫ y, ∫ x, conj (v x) * k (x,y) * u y ∂μ ∂ν := by
    simp only [L2.inner_def, RCLike.inner_apply']
    apply integral_congr_ae
    filter_upwards [dagger_apply_coe μ ν k v] with y hy
    rw [hy, ← integral_conj, ← integral_mul_const]
    congr 1
    funext x
    simp only [map_mul, conj_conj]
    ring
  rw [hl, hr]
  exact integral_integral_swap (l2_kernel_triple_bound μ ν k v u).1

theorem kernelOperator_adjoint (k : Lp 𝕜 2 (μ.prod ν)) :
    ContinuousLinearMap.adjoint (kernelOperator μ ν k) =
      kernelOperator ν μ (L2KernelCompactSpec.dagger μ ν k) := by
  ext1 v
  apply ext_inner_right 𝕜
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact l2Kernel_adjoint_pairing μ ν k v u

theorem l2_kernel_adjoint_correct : L2KernelCompactSpec.AdjointFormula.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k
  refine ⟨kernelOperator_adjoint μ ν k, ?_⟩
  intro v
  refine ⟨dagger_integrable μ ν k v, ?_⟩
  change (ContinuousLinearMap.adjoint (kernelOperator μ ν k) v : Y → 𝕜) =ᵐ[ν] _
  rw [kernelOperator_adjoint]
  exact dagger_apply_coe μ ν k v


theorem hermitian_kernel_compact_selfadjoint :
    L2KernelCompactSpec.HermitianCompactSelfAdjoint.{u} := by
  intro X 𝕜 _ _ μ _ k hk
  refine ⟨kernel_compact μ μ k, ?_⟩
  change ContinuousLinearMap.adjoint (kernelOperator μ μ k) = kernelOperator μ μ k
  rw [kernelOperator_adjoint]
  have hd : L2KernelCompactSpec.dagger μ μ k = k :=
    Lp.ext ((dagger_coe μ μ k).trans hk.symm)
  rw [hd]


/-- The quantitative continuity used to pass from L² to operator norm. -/
theorem kernelOperator_sub_bound (k h : Lp 𝕜 2 (μ.prod ν)) :
    ‖kernelOperator μ ν k - kernelOperator μ ν h‖ ≤ ‖k - h‖ := by
  change ‖kernelAssignment μ ν k - kernelAssignment μ ν h‖ ≤ _
  rw [← map_sub]
  exact L2Kernel.kernel_norm_bound μ ν (k - h)

/-- The constant-kernel formula on a finite measure space. -/
theorem kernelOperator_const {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (c : ℂ) (f : Lp ℂ 2 μ) :
    kernelOperator μ μ (Lp.const 2 (μ.prod μ) c) f =
      (c * ∫ y, f y ∂μ) • Lp.const 2 μ (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [kernelOperator_coe μ μ (Lp.const 2 (μ.prod μ) c) f,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_const (p := 2) (μ := μ.prod μ) c),
    Lp.coeFn_smul (c * ∫ y, f y ∂μ) (Lp.const 2 μ (1 : ℂ)),
    Lp.coeFn_const (p := 2) (μ := μ) (1 : ℂ)] with x hx hc hs h1
  rw [hx, hs, Pi.smul_apply, h1, Function.const_apply, smul_eq_mul, mul_one]
  calc
    _ = ∫ y, c * f y ∂μ := integral_congr_ae (hc.mono fun y hy => by rw [hy]; rfl)
    _ = _ := integral_const_mul c _


/-- Constant i is symmetric but gives a nonzero skew-adjoint operator. -/
theorem symmetric_kernel_counterexample : L2KernelCompactSpec.SymmetryCounterexample.{u} := by
  intro X _ μ _
  let k := Lp.const 2 (μ.prod μ) Complex.I
  let T := kernelOperator μ μ k
  let e := Lp.const 2 μ (1 : ℂ)
  have hk : (k : X × X → ℂ) =ᵐ[μ.prod μ] (fun _ => Complex.I) := Lp.coeFn_const 2 (μ.prod μ) Complex.I
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae_eq_comp hk
  have hsym : L2KernelCompactSpec.Symmetric μ k := by
    filter_upwards [hk, hswap] with p hp hps
    exact hp.trans hps.symm
  have hdagger : L2KernelCompactSpec.dagger μ μ k = -k := by
    apply Lp.ext
    filter_upwards [dagger_coe μ μ k, hswap, Lp.coeFn_neg k, hk]
      with p hp hps hn hpk
    change k p.swap = Complex.I at hps
    rw [hp, hps, hn, Pi.neg_apply, hpk]
    exact Complex.conj_I
  have hadjoint : ContinuousLinearMap.adjoint T = -T := by
    change ContinuousLinearMap.adjoint (kernelOperator μ μ k) = -kernelOperator μ μ k
    rw [kernelOperator_adjoint, hdagger]
    exact map_neg (kernelAssignment μ μ) k
  have hformula (f : Lp ℂ 2 μ) : T f = (Complex.I * ∫ y, f y ∂μ) • e :=
    kernelOperator_const μ Complex.I f
  have heint : (∫ y, e y ∂μ) = 1 := by
    rw [integral_congr_ae (Lp.coeFn_const (p := 2) (μ := μ) (1 : ℂ))]
    simp
  have he : e ≠ 0 := by
    intro h
    have hz : (∫ y, e y ∂μ) = 0 := by
      rw [h]
      simpa using integral_congr_ae (Lp.coeFn_zero ℂ 2 μ)
    exact one_ne_zero (heint.symm.trans hz)
  have hTe : T e = Complex.I • e := by rw [hformula, heint, mul_one]
  refine ⟨k, hsym, ?_⟩
  intro h
  have hh : -T = T := hadjoint.symm.trans h
  have hh' : (-Complex.I) • e = Complex.I • e := by
    simpa [hTe] using congrArg (fun S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => S e) hh
  have hi : -Complex.I = Complex.I := smul_left_injective ℂ he hh'
  have him := congrArg Complex.im hi
  norm_num at him

end ExpandedFA.PartV.L2KernelCompact
