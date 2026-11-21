import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.EulerAndTrotterProducts
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.ChernoffProductFormula
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.HilleYosida

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace ExpandedFA.Semigroups.EulerAndTrotterProducts
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
open EulerTrotterSpec

omit [CompleteSpace X] in
/-- The domain of a closable operator is a graph core for its closure,
in the shared graph-closure convention. -/
theorem domain_core_closure (A : Unbounded.Operator 𝕜 X X) (hA : A.IsClosable) :
    Unbounded.OperatorDomainsSpec.coreValue A.closure A.domain := by
  refine ⟨A.le_closure.1, ?_⟩
  have he : A.closure.domRestrict A.domain = A := by
    apply LinearPMap.eq_of_le_of_domain_eq
    · refine ⟨by simp, ?_⟩
      intro x y hxy
      calc
        _ = A.closure ⟨x, x.2.2⟩ := LinearPMap.domRestrict_apply rfl
        _ = A y := (A.le_closure.2 hxy.symm).symm
    · exact inf_eq_left.mpr A.le_closure.1
  rw [he, hA.graph_closure_eq_closure_graph,
    hA.closure_isClosed.submodule_topologicalClosure_eq]

/-- Differentiate the product on the exact intersection domain. -/
theorem product_consistency (TA TB : C0Semigroup 𝕜 X)
    (x : (C0SemigroupSpec.generatorValue TA + C0SemigroupSpec.generatorValue TB).domain) :
    Tendsto (fun h : ℝ => (algebraMap ℝ 𝕜 h)⁻¹ •
      ((TA.operators h.toNNReal * TB.operators h.toNNReal) (x : X) - (x : X)))
      (𝓝[>] 0) (𝓝 ((C0SemigroupSpec.generatorValue TA +
        C0SemigroupSpec.generatorValue TB) x)) := by
  let xA : (C0SemigroupSpec.generatorValue TA).domain := ⟨x, x.2.1⟩
  let xB : (C0SemigroupSpec.generatorValue TB).domain := ⟨x, x.2.2⟩
  have hA := generator_has_limit TA xA
  have hB := generator_has_limit TB xB
  have ht : Tendsto (fun h : ℝ => h.toNNReal) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_real_toNNReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hp := GeneratorDeterminesSemigroup.tendsto_apply TA ht hB
  have hh := hp.add hA
  simp only [TA.zero_apply] at hh
  convert hh using 1
  · funext h
    simp only [C0SemigroupSpec.differenceQuotientValue,
      smul_apply, sub_apply,
      ContinuousLinearMap.id_apply, mul_apply_eq_comp, map_smul, map_sub, smul_sub]
    abel
  · congr 1
    exact add_comm _ _

/-- Trotter's contraction product formula for a sum whose closure generates
contractions. The closure is not assumed to exist without closability. -/
theorem trotter_formula : TrotterFormula (𝕜 := 𝕜) (X := X) := by
  intro TA TB TC hA hB hC hclos hgen
  let S := C0SemigroupSpec.generatorValue TA + C0SemigroupSpec.generatorValue TB
  have hcore : Unbounded.OperatorDomainsSpec.coreValue
      (C0SemigroupSpec.generatorValue TC) S.domain := by
    rw [← hgen]
    exact domain_core_closure S hclos
  have hF (h : ℝ≥0) : ‖TA.operators h * TB.operators h‖ ≤ 1 := by
    calc
      _ ≤ ‖TA.operators h‖ * ‖TB.operators h‖ := norm_mul_le _ _
      _ ≤ 1 := by nlinarith [norm_nonneg (TA.operators h),
        norm_nonneg (TB.operators h), hA h, hB h]
  apply ChernoffProductFormula.chernoff_product_formula TC
    (fun h => TA.operators h * TB.operators h) S.domain hC hF
    (by rw [TA.at_zero, TB.at_zero]; exact one_mul _) hcore
  intro x
  have he : S x = C0SemigroupSpec.generatorValue TC ⟨x, hcore.1 x.2⟩ := by
    have hs : S ≤ C0SemigroupSpec.generatorValue TC := by
      rw [← hgen]
      exact S.le_closure
    exact hs.2 rfl
  rw [← he]
  exact product_consistency TA TB x

/-- The contraction bound supplies every positive resolvent estimate. -/
theorem contraction_resolvent_estimates (T : C0Semigroup 𝕜 X)
    (hT : ∀ t, ‖T.operators t‖ ≤ 1) :
    YosidaConstructionSpec.ResolventEstimates (C0SemigroupSpec.generatorValue T) 1 := by
  have hb : C0SemigroupSpec.exponentialBoundValue T 1 0 :=
    ⟨le_rfl, by simpa only [zero_mul, Real.exp_zero, mul_one] using hT⟩
  have he := HilleYosida.necessary T 1 0 hb
  exact ⟨he.1, by simpa only [sub_zero, YosidaConstructionSpec.positiveResolvent] using he.2⟩

omit [CompleteSpace X] in
/-- Positive Euler steps are scaled resolvents. -/
theorem implicitStep_eq_scaled (A : Unbounded.Operator 𝕜 X X)
    {h : ℝ≥0} (hh : 0 < h) :
    implicitStep A h = YosidaConstructionSpec.scaledResolvent A (h : ℝ)⁻¹ := by
  simp only [implicitStep, ne_of_gt hh, ↓reduceIte,
    YosidaConstructionSpec.scaledResolvent, YosidaConstructionSpec.positiveResolvent]

/-- The Euler steps are contractions, including on the zero space and at h=0. -/
theorem implicitStep_contraction (T : C0Semigroup 𝕜 X)
    (hT : ∀ t, ‖T.operators t‖ ≤ 1) (h : ℝ≥0) :
    ‖implicitStep (C0SemigroupSpec.generatorValue T) h‖ ≤ 1 := by
  by_cases hh : h = 0
  · simp only [implicitStep, hh, ↓reduceIte]
    exact ContinuousLinearMap.norm_id_le
  · have hp : 0 < h := lt_of_le_of_ne (show (0 : ℝ≥0) ≤ h from zero_le) (Ne.symm hh)
    rw [implicitStep_eq_scaled _ hp]
    exact YosidaConstruction.norm_scaledResolvent_le
      (contraction_resolvent_estimates T hT) (inv_pos.mpr hp)

/-- Strong approximation by the Euler resolvents at every ambient vector. -/
theorem implicitStep_tendsto (T : C0Semigroup 𝕜 X)
    (hT : ∀ t, ‖T.operators t‖ ≤ 1) (x : X) :
    Tendsto (fun h : ℝ => implicitStep (C0SemigroupSpec.generatorValue T) h.toNNReal x)
      (𝓝[>] 0) (𝓝 x) := by
  have hl := (YosidaConstruction.scaledResolvent_tendsto
    (SemigroupGrowthAndGenerator.generator_dense T)
    (contraction_resolvent_estimates T hT) x).comp tendsto_inv_nhdsGT_zero
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [implicitStep_eq_scaled _ (Real.toNNReal_pos.mpr hh),
    Real.coe_toNNReal _ hh.le]
  rfl

/-- On D(A), the Euler difference quotient is F(h)Ax. -/
theorem implicitStep_quotient (T : C0Semigroup 𝕜 X)
    (hT : ∀ t, ‖T.operators t‖ ≤ 1) {h : ℝ} (hh : 0 < h)
    (x : (C0SemigroupSpec.generatorValue T).domain) :
    (algebraMap ℝ 𝕜 h)⁻¹ •
      (implicitStep (C0SemigroupSpec.generatorValue T) h.toNNReal (x : X) - (x : X)) =
      implicitStep (C0SemigroupSpec.generatorValue T) h.toNNReal
        (C0SemigroupSpec.generatorValue T x) := by
  have he := YosidaConstruction.scaledResolvent_sub (C0SemigroupSpec.generatorValue T)
    h⁻¹ ((contraction_resolvent_estimates T hT).1 _ (inv_pos.mpr hh)) x
  rw [implicitStep_eq_scaled _ (Real.toNNReal_pos.mpr hh), Real.coe_toNNReal _ hh.le]
  rw [he]
  simp only [YosidaConstructionSpec.scaledResolvent, smul_apply, map_inv₀]

/-- The scaled resolvent really inverts I-hA on the exact generator domain. -/
theorem implicit_euler_inverse : EulerInverse (𝕜 := 𝕜) (X := X) := by
  intro T hT h hh
  let A := C0SemigroupSpec.generatorValue T
  let c : 𝕜 := algebraMap ℝ 𝕜 (h : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact (map_ne_zero (algebraMap ℝ 𝕜)).mpr (ne_of_gt (show 0 < (h : ℝ) from hh))
  have hex := (contraction_resolvent_estimates T hT).1 (h : ℝ)⁻¹
    (inv_pos.mpr (show 0 < (h : ℝ) from hh))
  let R : Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 (h : ℝ)⁻¹) := hex.some
  have he : implicitStep A h = c⁻¹ • R.inverse := by
    rw [implicitStep_eq_scaled A hh]
    simp only [YosidaConstructionSpec.scaledResolvent,
      YosidaConstruction.positiveResolvent_eq A _ hex, map_inv₀]
    rfl
  have hmem (y : X) : implicitStep A h y ∈ A.domain := by
    rw [he, smul_apply]
    exact A.domain.smul_mem c⁻¹ (R.mem_domain y)
  refine ⟨hmem, ?_, ?_⟩
  · intro y hy
    let z : A.domain := ⟨R.inverse y, R.mem_domain y⟩
    have hz : (⟨implicitStep A h y, hy⟩ : A.domain) = c⁻¹ • z := by
      apply Subtype.ext
      exact congrArg (fun L : X →L[𝕜] X => L y) he
    change implicitStep A h y - c • A ⟨implicitStep A h y, hy⟩ = y
    rw [hz, A.map_smul]
    calc
      _ = c⁻¹ • R.inverse y - c • (c⁻¹ • A z) := by rw [he, smul_apply]
      _ = y := by
        rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        simpa only [map_inv₀] using R.right_inverse y
  · intro x
    change implicitStep A h ((x : X) - c • A x) = x
    rw [he, smul_apply, ← R.inverse.map_smul]
    have hid : c⁻¹ • ((x : X) - c • A x) = c⁻¹ • (x : X) - A x := by
      rw [smul_sub, inv_smul_smul₀ hc]
    rw [hid]
    simpa only [map_inv₀] using R.left_inverse x

/-- Implicit Euler is a Chernoff family on the full generator domain. -/
theorem implicit_euler_formula : EulerFormula (𝕜 := 𝕜) (X := X) := by
  intro T hT
  let A := C0SemigroupSpec.generatorValue T
  have hcore : Unbounded.OperatorDomainsSpec.coreValue A A.domain := by
    refine ⟨le_rfl, ?_⟩
    have he : A.domRestrict A.domain = A :=
      LinearPMap.eq_of_le_of_domain_eq LinearPMap.domRestrict_le (inf_idem _)
    rw [he]
  apply ChernoffProductFormula.chernoff_product_formula T (implicitStep A) A.domain
    hT (implicitStep_contraction T hT) (by simp [implicitStep]) hcore
  intro x
  apply (implicitStep_tendsto T hT (A x)).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (implicitStep_quotient T hT hh x).symm

end ExpandedFA.Semigroups.EulerAndTrotterProducts
