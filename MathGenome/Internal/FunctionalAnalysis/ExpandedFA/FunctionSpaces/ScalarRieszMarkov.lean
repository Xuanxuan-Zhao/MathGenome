import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

noncomputable section

namespace ExpandedFA.FunctionSpaces.ScalarRieszMarkov

open Set MeasureTheory Filter
open scoped ENNReal CompactlySupported ZeroAtInfty Topology
open ScalarRieszMarkovSpec
open PositiveRadonRepresentationSpec

universe u

theorem compact_identification : CompactIdentification.{u} := by
  intro X _ _ 𝕜 _
  let e : C(X, 𝕜) ≃ₗᵢ[𝕜] C₀(X, 𝕜) :=
    { toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
      map_add' := fun _ _ => by ext x; rfl
      map_smul' := fun _ _ => by ext x; rfl
      norm_map' := fun f => by
        apply le_antisymm
        · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
          exact f.norm_coe_le_norm
        · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
          intro x
          exact (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f).toBCF.norm_coe_le_norm x }
  exact ⟨e, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The canonical pointwise inclusion, kept linear for restriction of functionals. -/
def compactlySupportedInclusion (X : Type u) [TopologicalSpace X]
    (𝕜 : Type*) [RCLike 𝕜] : C_c(X, 𝕜) →ₗ[𝕜] C₀(X, 𝕜) where
  toFun f := (f : C₀(X, 𝕜))
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

@[simp] theorem compactlySupportedInclusion_apply {X : Type u} [TopologicalSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (f : C_c(X, 𝕜)) (x : X) :
    compactlySupportedInclusion X 𝕜 f x = f x := rfl

/-- Compact cutoffs approximate every function vanishing at infinity uniformly.
The proof does not require a countable compact exhaustion of the space. -/
theorem compactlySupportedInclusion_denseRange (X : Type u) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (𝕜 : Type*) [RCLike 𝕜] :
    DenseRange (compactlySupportedInclusion X 𝕜) := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨K, hK, hsmall⟩ := mem_cocompact.mp
    (Metric.tendsto_nhds.mp (zero_at_infty f) (ε / 2) (by positivity))
  obtain ⟨χ, hχK, hχcomp, _, hχ⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let g : C_c(X, 𝕜) :=
    ⟨⟨fun x => χ x • f x, χ.continuous.smul f.continuous⟩, (show HasCompactSupport χ from hχcomp).smul_right⟩
  refine ⟨g, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ ε / 2)).mpr
  intro x
  change ‖f x - χ x • f x‖ ≤ ε / 2
  by_cases hx : x ∈ K
  · simp only [hχK hx, Pi.one_apply, one_smul, sub_self, norm_zero]
    positivity
  · have hfx : ‖f x‖ < ε / 2 := by simpa using hsmall hx
    calc
      ‖f x - χ x • f x‖ = ‖(1 - χ x) • f x‖ := by simp [sub_smul]
      _ = (1 - χ x) * ‖f x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hχ x).2)]
      _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (by linarith [(hχ x).1]) (norm_nonneg _)
      _ ≤ ε / 2 := by simpa using hfx.le

/-- Integration as a bounded functional on the actual native C₀ functions. -/
def positiveMeasureFunctional {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    C₀(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (f.toBCF.integrable μ) (g.toBCF.integrable μ)
      map_smul' := fun c f => integral_smul c f }
    (μ.real univ) (fun f => f.toBCF.norm_integral_le_mul_norm μ)

@[simp] theorem positiveMeasureFunctional_apply {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : C₀(X, ℝ)) : positiveMeasureFunctional μ f = ∫ x, f x ∂μ := rfl

/-- A positive Radon representative of a bounded C₀ functional has finite
mass bounded by its norm. Compact cutoffs suffice even without σ-compactness. -/
theorem mass_le_norm_of_compactlySupported_representation {X : Type u}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (L : C₀(X, ℝ) →L[ℝ] ℝ) (μ : Measure X) (hμ : PositiveRadon μ)
    (hrep : ∀ f : C_c(X, ℝ), Integrable f μ ∧
      L (compactlySupportedInclusion X ℝ f) = ∫ x, f x ∂μ) :
    μ univ ≤ ENNReal.ofReal ‖L‖ := by
  have : μ.Regular := (PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ
  rw [hμ.2.2 univ isOpen_univ]
  refine iSup_le fun K => iSup_le fun _ => iSup_le fun hK => ?_
  obtain ⟨χ, hχK, hχcomp, _, hχ⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let f : C_c(X, ℝ) := ⟨χ, hχcomp⟩
  have hfnorm : ‖compactlySupportedInclusion X ℝ f‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
    intro x
    change |χ x| ≤ 1
    exact abs_le.mpr ⟨by linarith [(hχ x).1], (hχ x).2⟩
  apply (ENNReal.le_ofReal_iff_toReal_le hK.measure_lt_top.ne (norm_nonneg L)).mpr
  calc
    μ.real K = ∫ x, K.indicator (1 : X → ℝ) x ∂μ := (integral_indicator_one hK.measurableSet).symm
    _ ≤ ∫ x, f x ∂μ := by
      refine integral_mono ?_ (hrep f).1 ?_
      · exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
      · intro x
        change K.indicator (1 : X → ℝ) x ≤ χ x
        by_cases hx : x ∈ K
        · simp [hx, hχK hx]
        · simpa [hx] using (hχ x).1
    _ = L (compactlySupportedInclusion X ℝ f) := (hrep f).2.symm
    _ ≤ ‖L (compactlySupportedInclusion X ℝ f)‖ := le_abs_self _
    _ ≤ ‖L‖ * ‖compactlySupportedInclusion X ℝ f‖ := L.le_opNorm _
    _ ≤ ‖L‖ := by nlinarith [norm_nonneg L]

/-- The positive bounded C₀ theorem, with uniqueness, integrability and exact
norm equal to mass on every locally compact Hausdorff space. -/
theorem positive_representation : ScalarRieszMarkovSpec.PositiveRepresentation.{u} := by
  intro X _ _ _ _ _ L hL
  let I : C_c(X, ℝ) →ₗ[ℝ] ℝ := L.toLinearMap.comp (compactlySupportedInclusion X ℝ)
  obtain ⟨μ, ⟨hμ, hrep⟩, huniq⟩ :=
    PositiveRadonRepresentation.positive_radon_representation X I
      (fun f hf => hL _ hf)
  have hbound : μ univ ≤ ENNReal.ofReal ‖L‖ :=
    mass_le_norm_of_compactlySupported_representation L μ hμ hrep
  have hfinite : μ univ < ∞ := hbound.trans_lt ENNReal.ofReal_lt_top
  have : IsFiniteMeasure μ := ⟨hfinite⟩
  have heq : (L : C₀(X, ℝ) → ℝ) = positiveMeasureFunctional μ := by
    apply (compactlySupportedInclusion_denseRange X ℝ).equalizer L.continuous
      (positiveMeasureFunctional μ).continuous
    exact funext fun f => (hrep f).2
  have hall (f : C₀(X, ℝ)) : Integrable f μ ∧ L f = ∫ x, f x ∂μ :=
    ⟨f.toBCF.integrable μ, congrFun heq f⟩
  refine ⟨μ, hμ, hfinite, hall, le_antisymm ?_ ?_, ?_⟩
  · apply L.opNorm_le_bound ENNReal.toReal_nonneg
    intro f
    rw [(hall f).2]
    exact f.toBCF.norm_integral_le_mul_norm μ
  · exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg L) hbound
  · intro ν hν _ hνrep
    apply huniq ν
    exact ⟨hν, fun f => hνrep (compactlySupportedInclusion X ℝ f)⟩

/-- The variation inequality, with constant exactly one and multiplication
as the scalar pairing. This is the upper half of the scalar norm equality. -/
theorem scalarIntegral_bound {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {𝕜 : Type*} [RCLike 𝕜]
    (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] (f : C₀(X, 𝕜)) :
    Integrable f ν.variation ∧ ‖scalarIntegral ν f‖ ≤ ν.variation.real univ * ‖f‖ := by
  refine ⟨f.toBCF.integrable ν.variation, ?_⟩
  calc
    ‖scalarIntegral ν f‖ ≤ ‖f‖ * ‖ContinuousLinearMap.mul ℝ 𝕜‖ * ν.variation.real univ :=
      VectorMeasure.norm_integral_le_of_norm_le_const
        (Eventually.of_forall fun x => f.toBCF.norm_coe_le_norm x)
    _ ≤ ‖f‖ * 1 * ν.variation.real univ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ 𝕜
    _ = ν.variation.real univ * ‖f‖ := by ring

/-- Scalar linearity of multiplication integration, including complex scalars.
Mathlib's vector-integral `integral_smul` is real-only, so use the more
general extension theorem with its scalar-commutation hypothesis verified. -/
theorem scalarIntegral_smul {X : Type u} [MeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (ν : VectorMeasure X 𝕜) (c : 𝕜) (f : X → 𝕜) :
    scalarIntegral ν (c • f) = c • scalarIntegral ν f := by
  unfold scalarIntegral VectorMeasure.integral
  apply setToFun_smul
  intro a s x
  change (a * x) * ν s = a * (x * ν s)
  exact mul_assoc _ _ _

/-- The multiplication integral gives a bounded scalar-linear functional.
Only finiteness of the genuine total variation is needed here. -/
def scalarMeasureFunctional {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {𝕜 : Type*} [RCLike 𝕜]
    (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] : C₀(X, 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => scalarIntegral ν f
      map_add' := fun f g => VectorMeasure.integral_fun_add
        (scalarIntegral_bound ν f).1 (scalarIntegral_bound ν g).1
      map_smul' := fun c f => scalarIntegral_smul ν c f }
    (ν.variation.real univ) (fun f => (scalarIntegral_bound ν f).2)

@[simp] theorem scalarMeasureFunctional_apply {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {𝕜 : Type*} [RCLike 𝕜]
    (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] (f : C₀(X, 𝕜)) :
    scalarMeasureFunctional ν f = scalarIntegral ν f := rfl

theorem scalarMeasureFunctional_norm_le {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {𝕜 : Type*} [RCLike 𝕜]
    (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] :
    ‖scalarMeasureFunctional ν‖ ≤ ν.variation.real univ :=
  (scalarMeasureFunctional ν).opNorm_le_bound ENNReal.toReal_nonneg
    (fun f => (scalarIntegral_bound ν f).2)

/-- No exception or chosen point is needed when the underlying space is empty. -/
theorem empty_representation : EmptyRepresentation.{u} := by
  intro X _ _ _ _ 𝕜 _ L
  have hL : L = 0 := by
    ext f
    have hf : f = 0 := by ext x; exact isEmptyElim x
    simp [hf]
  have hν (ν : VectorMeasure X 𝕜) : ν = 0 := by
    ext s hs
    have hs0 : s = ∅ := Set.eq_empty_of_isEmpty s
    simp [hs0]
  have hradon : PositiveRadon (0 : Measure X) := by
    apply (PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
    infer_instance
  refine ⟨0, ⟨by simp, by simpa using hradon⟩, ?_, ?_, fun ν _ _ => hν ν⟩
  · intro f
    constructor
    · simp
    · simp [hL, scalarIntegral]
  · rw [hL]
    simpa only [VectorMeasure.variation_zero, measureReal_zero_apply] using
      (ContinuousLinearMap.opNorm_zero (𝕜 := 𝕜) (E := C₀(X, 𝕜)) (F := 𝕜))

/-- Postcomposition by a bounded real-linear scalar map preserves vanishing
at infinity, and is bounded in the supremum norm. -/
def postcompose {X : Type u} [TopologicalSpace X]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) :
    C₀(X, E) →L[ℝ] C₀(X, F) :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        { toFun := fun x => T (f x)
          continuous_toFun := T.continuous.comp f.continuous
          zero_at_infty' := by
            simpa only [map_zero, Function.comp_def] using
              (T.continuous.tendsto 0).comp (zero_at_infty f) }
      map_add' := fun f g => by ext x; exact T.map_add _ _
      map_smul' := fun c f => by ext x; exact T.map_smul c _ }
    ‖T‖ (fun f => by
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg T) (norm_nonneg f))).mpr
      intro x
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (f.toBCF.norm_coe_le_norm x) (norm_nonneg T)))

@[simp] theorem postcompose_apply {X : Type u} [TopologicalSpace X]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F)
    (f : C₀(X, E)) (x : X) : postcompose T f x = T (f x) := rfl

theorem postcompose_norm_le {X : Type u} [TopologicalSpace X]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) (f : C₀(X, E)) :
    ‖postcompose T f‖ ≤ ‖T‖ * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg T) (norm_nonneg f))).mpr
  intro x
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (f.toBCF.norm_coe_le_norm x) (norm_nonneg T))

/-- Pointwise positive part, as an actual continuous function vanishing at infinity. -/
def positivePart {X : Type u} [TopologicalSpace X] (f : C₀(X, ℝ)) : C₀(X, ℝ) where
  toFun x := max (f x) 0
  continuous_toFun := f.continuous.max continuous_const
  zero_at_infty' := by
    simpa only [max_self] using (zero_at_infty f).max
      (tendsto_const_nhds (x := (0 : ℝ)) (f := cocompact X))

@[simp] theorem positivePart_apply {X : Type u} [TopologicalSpace X]
    (f : C₀(X, ℝ)) (x : X) : positivePart f x = max (f x) 0 := rfl

/-- Positive complex functionals have positive finite Radon representatives,
with the same exact mass normalization as in the real case. -/
theorem complex_positive_representation : ComplexPositiveRepresentation.{u} := by
  intro X _ _ _ _ _ L hL
  let J : C₀(X, ℝ) →L[ℝ] C₀(X, ℂ) := postcompose Complex.ofRealCLM
  let A : C₀(X, ℝ) →L[ℝ] ℝ :=
    Complex.reCLM.comp ((L.restrictScalars ℝ).comp J)
  have hA (f : C₀(X, ℝ)) (hf : ∀ x, 0 ≤ f x) : 0 ≤ A f :=
    (hL (J f) (fun x => ⟨by simp [J], by simpa [J] using hf x⟩)).2
  obtain ⟨μ, hμ, hfinite, hrep, hnorm, huniq⟩ := positive_representation X A hA
  have : IsFiniteMeasure μ := ⟨hfinite⟩
  have hreal (f : C₀(X, ℝ)) : L (J f) = (A f : ℂ) := by
    have him (g : C₀(X, ℝ)) (hg : ∀ x, 0 ≤ g x) : (L (J g)).im = 0 :=
      (hL (J g) (fun x => ⟨by simp [J], by simpa [J] using hg x⟩)).1
    have hsplit : f = positivePart f - positivePart (-f) := by
      ext x
      simp only [ZeroAtInftyContinuousMap.sub_apply, positivePart_apply,
        ZeroAtInftyContinuousMap.neg_apply]
      by_cases hx : 0 ≤ f x
      · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    have hIm : (L (J f)).im = 0 := by
      rw [hsplit, map_sub, map_sub, Complex.sub_im,
        him _ (fun x => le_max_right _ _), him _ (fun x => le_max_right _ _)]
      simp
    apply Complex.ext
    · rfl
    · simpa using hIm
  have hall (f : C₀(X, ℂ)) : Integrable f μ ∧ L f = ∫ x, f x ∂μ := by
    let r := postcompose Complex.reCLM f
    let i := postcompose Complex.imCLM f
    have hsplit : f = J r + Complex.I • J i := by
      ext x
      change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
      exact (Complex.re_add_im (f x)).symm.trans (by ring)
    refine ⟨f.toBCF.integrable μ, ?_⟩
    calc
      L f = ((A r : ℂ) + Complex.I * (A i : ℂ)) := by
        rw [hsplit, map_add, map_smul, hreal, hreal, smul_eq_mul]
      _ = ∫ x, f x ∂μ := by
        rw [(hrep r).2, (hrep i).2]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
          exact integral_re (f.toBCF.integrable μ)
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, mul_zero, zero_add, one_mul]
          exact integral_im (f.toBCF.integrable μ)
  refine ⟨μ, hμ, hfinite, hall, le_antisymm ?_ ?_, ?_⟩
  · apply L.opNorm_le_bound ENNReal.toReal_nonneg
    intro f
    rw [(hall f).2]
    exact f.toBCF.norm_integral_le_mul_norm μ
  · rw [← hnorm]
    apply A.opNorm_le_bound (norm_nonneg L)
    intro f
    calc
      ‖A f‖ ≤ ‖L (J f)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖L‖ * ‖J f‖ := L.le_opNorm _
      _ ≤ ‖L‖ * ‖f‖ := by
        gcongr
        simpa [J] using postcompose_norm_le Complex.ofRealCLM f
  · intro η hη hηfinite hηrep
    have : IsFiniteMeasure η := ⟨hηfinite⟩
    apply huniq η hη hηfinite
    intro f
    refine ⟨f.toBCF.integrable η, ?_⟩
    have heq := congrArg Complex.re (hηrep (J f)).2
    change (L (J f)).re = (∫ x, (f x : ℂ) ∂η).re at heq
    rw [integral_complex_ofReal] at heq
    exact heq

theorem positivePart_norm_le {X : Type u} [TopologicalSpace X] (f : C₀(X, ℝ)) :
    ‖positivePart f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  change |max (f x) 0| ≤ ‖f‖
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans (f.toBCF.norm_coe_le_norm x)) (norm_nonneg f)

theorem positivePart_sub_neg {X : Type u} [TopologicalSpace X] (f : C₀(X, ℝ)) :
    positivePart f - positivePart (-f) = f := by
  ext x
  change max (f x) 0 - max (-f x) 0 = f x
  by_cases hx : 0 ≤ f x
  · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring

theorem positivePart_smul {X : Type u} [TopologicalSpace X] (c : ℝ) (hc : 0 ≤ c)
    (f : C₀(X, ℝ)) : positivePart (c • f) = c • positivePart f := by
  ext x
  change max (c * f x) 0 = c * max (f x) 0
  rw [mul_max_of_nonneg _ _ hc, mul_zero]

theorem positivePart_add_norm_le {X : Type u} [TopologicalSpace X]
    (f g : C₀(X, ℝ)) : ‖positivePart (f + g)‖ ≤ ‖positivePart f‖ + ‖positivePart g‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ ‖positivePart f‖ + ‖positivePart g‖)).mpr
  intro x
  change |max (f x + g x) 0| ≤ ‖positivePart f‖ + ‖positivePart g‖
  rw [abs_of_nonneg (le_max_right _ _)]
  have hf : f x ≤ ‖positivePart f‖ :=
    (le_max_left _ _).trans ((le_abs_self _).trans ((positivePart f).toBCF.norm_coe_le_norm x))
  have hg : g x ≤ ‖positivePart g‖ :=
    (le_max_left _ _).trans ((le_abs_self _).trans ((positivePart g).toBCF.norm_coe_le_norm x))
  exact max_le (add_le_add hf hg) (by positivity)

/-- A bounded real functional is a difference of two bounded positive
functionals. Hahn–Banach is applied to the anti-diagonal in the product,
dominated by the sum of the two positive-part norms. -/
theorem exists_positive_decomposition {X : Type u} [TopologicalSpace X]
    (L : C₀(X, ℝ) →L[ℝ] ℝ) :
    ∃ P Q : C₀(X, ℝ) →L[ℝ] ℝ,
      (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ P f) ∧
      (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ Q f) ∧ L = P - Q := by
  let E := C₀(X, ℝ)
  let S : Submodule ℝ (E × E) := LinearMap.ker ((LinearMap.id : E →ₗ[ℝ] E).coprod LinearMap.id)
  let l : S →ₗ[ℝ] ℝ := L.toLinearMap.comp ((LinearMap.fst ℝ E E).comp S.subtype)
  let N : E × E → ℝ := fun v => ‖L‖ * (‖positivePart v.1‖ + ‖positivePart v.2‖)
  have hhom (c : ℝ) (hc : 0 < c) (v : E × E) : N (c • v) = c * N v := by
    change ‖L‖ * (‖positivePart (c • v.1)‖ + ‖positivePart (c • v.2)‖) = _
    rw [positivePart_smul c hc.le, positivePart_smul c hc.le, norm_smul, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc]
    dsimp [N]
    ring
  have hadd (v w : E × E) : N (v + w) ≤ N v + N w := by
    change ‖L‖ * (‖positivePart (v.1 + w.1)‖ + ‖positivePart (v.2 + w.2)‖) ≤ _
    calc
      _ ≤ ‖L‖ * ((‖positivePart v.1‖ + ‖positivePart w.1‖) +
          (‖positivePart v.2‖ + ‖positivePart w.2‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add (positivePart_add_norm_le _ _)
          (positivePart_add_norm_le _ _)) (norm_nonneg L)
      _ = _ := by dsimp [N]; ring
  have hl (v : S) : l v ≤ N v := by
    have hv : v.val.2 = -v.val.1 := by
      have := v.property
      change v.val.1 + v.val.2 = 0 at this
      exact eq_neg_of_add_eq_zero_right this
    change L v.val.1 ≤ ‖L‖ * (‖positivePart v.val.1‖ + ‖positivePart v.val.2‖)
    calc
      _ ≤ ‖L v.val.1‖ := le_abs_self _
      _ ≤ ‖L‖ * ‖v.val.1‖ := L.le_opNorm _
      _ ≤ _ := by
        gcongr
        rw [hv]
        calc
          ‖v.val.1‖ = ‖positivePart v.val.1 - positivePart (-v.val.1)‖ :=
            congrArg norm (positivePart_sub_neg v.val.1).symm
          _ ≤ _ := norm_sub_le _ _
  obtain ⟨F, hFext, hFbound⟩ := exists_extension_of_le_sublinear ⟨S, l⟩ N hhom hadd hl
  have hb (f : E) : ‖F (f, 0)‖ ≤ ‖L‖ * ‖f‖ ∧ ‖F (0, f)‖ ≤ ‖L‖ * ‖f‖ := by
    have h (v : E × E) : F v ≤ N v := hFbound v
    have hp0 : positivePart (0 : E) = 0 := by ext x; simp [positivePart]
    constructor
    · rw [Real.norm_eq_abs, abs_le]
      have h1 := h (f, 0)
      have h2 := h (-f, 0)
      have hn : F (-f, 0) = -F (f, 0) := by simpa using F.map_neg (f, 0)
      dsimp [N] at h1 h2
      rw [hp0, norm_zero, add_zero] at h1 h2
      have h3 := mul_le_mul_of_nonneg_left (positivePart_norm_le f) (norm_nonneg L)
      have h4 := mul_le_mul_of_nonneg_left (positivePart_norm_le (-f)) (norm_nonneg L)
      rw [norm_neg] at h4
      constructor <;> linarith
    · rw [Real.norm_eq_abs, abs_le]
      have h1 := h (0, f)
      have h2 := h (0, -f)
      have hn : F (0, -f) = -F (0, f) := by simpa using F.map_neg (0, f)
      dsimp [N] at h1 h2
      rw [hp0, norm_zero, zero_add] at h1 h2
      have h3 := mul_le_mul_of_nonneg_left (positivePart_norm_le f) (norm_nonneg L)
      have h4 := mul_le_mul_of_nonneg_left (positivePart_norm_le (-f)) (norm_nonneg L)
      rw [norm_neg] at h4
      constructor <;> linarith
  let P := (F.comp (LinearMap.inl ℝ E E)).mkContinuous ‖L‖
    (fun f => by simpa only [LinearMap.comp_apply, LinearMap.inl_apply] using (hb f).1)
  let Q := (F.comp (LinearMap.inr ℝ E E)).mkContinuous ‖L‖
    (fun f => by simpa only [LinearMap.comp_apply, LinearMap.inr_apply] using (hb f).2)
  have hpos (f : E) (hf : ∀ x, 0 ≤ f x) : positivePart (-f) = 0 := by
    ext x
    change max (-f x) 0 = 0
    exact max_eq_right (neg_nonpos.mpr (hf x))
  have hp0 : positivePart (0 : E) = 0 := by ext x; simp [positivePart]
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · intro f hf
    have h := hFbound (-f, 0)
    have hn : F (-f, 0) = -P f := by
      change F (-f, 0) = -((F.comp (LinearMap.inl ℝ E E)).mkContinuous ‖L‖ _) f
      simp only [LinearMap.mkContinuous_apply, LinearMap.comp_apply, LinearMap.inl_apply]
      simpa using F.map_neg (f, 0)
    dsimp [N] at h
    rw [hpos f hf, hp0, norm_zero, zero_add, mul_zero, hn] at h
    linarith
  · intro f hf
    have h := hFbound (0, -f)
    have hn : F (0, -f) = -Q f := by
      change F (0, -f) = -((F.comp (LinearMap.inr ℝ E E)).mkContinuous ‖L‖ _) f
      simp only [LinearMap.mkContinuous_apply, LinearMap.comp_apply, LinearMap.inr_apply]
      simpa using F.map_neg (0, f)
    dsimp [N] at h
    rw [hpos f hf, hp0, norm_zero, zero_add, mul_zero, hn] at h
    linarith
  · ext f
    let v : S := ⟨(f, -f), by change f + -f = 0; simp⟩
    have hext : F (f, -f) = L f := hFext v
    have hsplit : F (f, -f) = P f - Q f := by
      dsimp only [P, Q]
      simp only [LinearMap.mkContinuous_apply, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.inr_apply]
      simpa using F.map_sub (f, 0) (0, f)
    exact hext.symm.trans hsplit

/-- Small compact complements characterize finite regularity on a Hausdorff
Borel space. This form is convenient for transferring regularity by domination. -/
theorem regular_of_small_compact_complements {X : Type u} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (ρ : Measure X) [IsFiniteMeasure ρ]
    (h : ∀ A, MeasurableSet A → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ K, K ⊆ A ∧ IsCompact K ∧ ρ (A \ K) < ε) : ρ.Regular := by
  have : ρ.InnerRegular := by
    constructor
    intro A hA r hr
    obtain ⟨K, hKA, hK, hsmall⟩ := h A hA (ρ A - r) (ne_of_gt (tsub_pos_iff_lt.mpr hr))
    refine ⟨K, hKA, hK, ?_⟩
    by_contra hn
    have hkr : ρ K ≤ r := le_of_not_gt hn
    have heq : ρ (A \ K) + ρ K = ρ A := by
      simpa only [inter_eq_right.mpr hKA] using measure_sdiff_add_inter (μ := ρ) A hK.measurableSet
    have hh : ρ A < ρ A := calc
      ρ A = ρ (A \ K) + ρ K := heq.symm
      _ < (ρ A - r) + ρ K := ENNReal.add_lt_add_right (measure_ne_top ρ K) hsmall
      _ ≤ (ρ A - r) + r := add_le_add_right hkr _
      _ = ρ A := tsub_add_cancel_of_le hr.le
    exact (lt_irrefl _ hh)
  infer_instance

/-- Finite regular measures are closed under domination, without countability
assumptions on the underlying space. -/
theorem regular_of_le {X : Type u} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {ρ μ : Measure X}
    [IsFiniteMeasure μ] [μ.Regular] (h : ρ ≤ μ) : ρ.Regular := by
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ h
  apply regular_of_small_compact_complements
  intro A hA ε hε
  obtain ⟨K, hKA, hK, hsmall⟩ := hA.exists_isCompact_sdiff_lt (measure_ne_top μ A) hε
  exact ⟨K, hKA, hK, (h _).trans_lt hsmall⟩

/-- Finite sums preserve Radon regularity even on non-σ-compact spaces. -/
theorem regular_add {X : Type u} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ η : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure η] [μ.Regular] [η.Regular] : (μ + η).Regular := by
  apply regular_of_small_compact_complements
  intro A hA ε hε
  obtain ⟨K, hKA, hK, hsmallK⟩ :=
    hA.exists_isCompact_sdiff_lt (measure_ne_top μ A) (ENNReal.half_pos hε).ne'
  obtain ⟨H, hHA, hH, hsmallH⟩ :=
    hA.exists_isCompact_sdiff_lt (measure_ne_top η A) (ENNReal.half_pos hε).ne'
  refine ⟨K ∪ H, union_subset hKA hHA, hK.union hH, ?_⟩
  calc
    (μ + η) (A \ (K ∪ H)) = μ (A \ (K ∪ H)) + η (A \ (K ∪ H)) := Measure.add_apply _ _ _
    _ ≤ μ (A \ K) + η (A \ H) := add_le_add
      (measure_mono (sdiff_subset_sdiff_right subset_union_left))
      (measure_mono (sdiff_subset_sdiff_right subset_union_right))
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hsmallK hsmallH
    _ = ε := ENNReal.add_halves ε

@[simp] theorem scalarIntegral_toSignedMeasure {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) :
    scalarIntegral μ.toSignedMeasure f = ∫ x, f x ∂μ := by
  have hpair : ContinuousLinearMap.mul ℝ ℝ = (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext
    rfl
  simp [scalarIntegral, hpair, VectorMeasure.integral_toSignedMeasure]

/-- Signed existence follows from a genuine difference of finite positive
Radon measures. No norm or uniqueness hypothesis is imposed on the witness. -/
theorem real_representation_exists {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (L : C₀(X, ℝ) →L[ℝ] ℝ) :
    ∃ ν : VectorMeasure X ℝ, FiniteScalarRadon ν ∧
      ∀ f : C₀(X, ℝ), Integrable f ν.variation ∧ L f = scalarIntegral ν f := by
  obtain ⟨P, Q, hP, hQ, hL⟩ := exists_positive_decomposition L
  obtain ⟨μ, hμ, hμfinite, hμrep, _⟩ := positive_representation X P hP
  obtain ⟨η, hη, hηfinite, hηrep, _⟩ := positive_representation X Q hQ
  have : IsFiniteMeasure μ := ⟨hμfinite⟩
  have : IsFiniteMeasure η := ⟨hηfinite⟩
  have : μ.Regular := (PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ
  have : η.Regular := (PositiveRadonRepresentation.positiveRadon_iff_regular η).mp hη
  let ν := μ.toSignedMeasure - η.toSignedMeasure
  have hbound : ν.variation ≤ μ + η := by
    simpa only [Measure.variation_toSignedMeasure] using
      (VectorMeasure.variation_sub_le (μ := μ.toSignedMeasure) (ν := η.toSignedMeasure))
  have : IsFiniteMeasure ν.variation := isFiniteMeasure_of_le (μ + η) hbound
  have : (μ + η).Regular := regular_add μ η
  have hνreg : ν.variation.Regular := regular_of_le hbound
  refine ⟨ν, ⟨measure_lt_top _ _,
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr hνreg⟩, ?_⟩
  intro f
  refine ⟨f.toBCF.integrable ν.variation, ?_⟩
  have hμint : μ.toSignedMeasure.Integrable (f : X → ℝ) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using (hμrep f).1
  have hηint : η.toSignedMeasure.Integrable (f : X → ℝ) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using (hηrep f).1
  calc
    L f = P f - Q f := by rw [hL]; rfl
    _ = (∫ x, f x ∂μ) - ∫ x, f x ∂η := by rw [(hμrep f).2, (hηrep f).2]
    _ = scalarIntegral ν f := by
      change _ = (μ.toSignedMeasure - η.toSignedMeasure).integral f (ContinuousLinearMap.mul ℝ ℝ)
      rw [VectorMeasure.integral_sub_vectorMeasure hμint hηint]
      rw [← scalarIntegral, ← scalarIntegral, scalarIntegral_toSignedMeasure,
        scalarIntegral_toSignedMeasure]

/-- Compact cutoffs approximate Borel indicators in L¹ on any LCH space.
This proof uses only separation of a compact set from a closed set. -/
theorem exists_compactlySupported_indicator_approx {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] {𝕜 : Type*} [RCLike 𝕜]
    {s : Set X} (hs : MeasurableSet s) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(X, 𝕜), (∀ x, ‖g x‖ ≤ 1) ∧
      (∫ x, ‖s.indicator (fun _ => (1 : 𝕜)) x - g x‖ ∂μ) ≤ ε := by
  have hδ : ENNReal.ofReal (ε / 2) ≠ 0 := by positivity
  obtain ⟨K, hKs, hK, hsmallK⟩ := hs.exists_isCompact_sdiff_lt (measure_ne_top μ s) hδ
  obtain ⟨U, hKU, hU, _, hsmallU⟩ :=
    hK.measurableSet.exists_isOpen_sdiff_lt (measure_ne_top μ K) hδ
  obtain ⟨χ, hχK, hχcomp, hχU, hχ⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  let g : C_c(X, 𝕜) := ⟨⟨fun x => (χ x : 𝕜), by fun_prop⟩,
    (show HasCompactSupport χ from hχcomp).comp_left (by simp)⟩
  have hgnorm (x : X) : ‖g x‖ ≤ 1 := by
    change ‖(χ x : 𝕜)‖ ≤ 1
    rw [RCLike.norm_ofReal, abs_of_nonneg (hχ x).1]
    exact (hχ x).2
  refine ⟨g, hgnorm, ?_⟩
  have hpoint (x : X) : ‖s.indicator (fun _ => (1 : 𝕜)) x - g x‖ ≤
      (s \ K).indicator (fun _ => (1 : ℝ)) x +
      (U \ K).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hxK : x ∈ K
    · have hxs := hKs hxK
      simp [hxs, hxK, g, hχK hxK]
    · by_cases hxs : x ∈ s
      · have hnorm : ‖(1 : 𝕜) - (χ x : 𝕜)‖ ≤ 1 := by
          rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal,
            abs_of_nonneg (sub_nonneg.mpr (hχ x).2)]
          linarith [(hχ x).1]
        have hn : 0 ≤ (U \ K).indicator (fun _ => (1 : ℝ)) x :=
          indicator_nonneg (fun _ _ => zero_le_one) x
        simpa only [indicator_of_mem hxs, indicator_of_mem (show x ∈ s \ K from ⟨hxs, hxK⟩), show g x = (χ x : 𝕜) from rfl] using
          hnorm.trans (le_add_of_nonneg_right hn)
      · by_cases hxU : x ∈ U
        · simpa [hxs, hxK, hxU] using hgnorm x
        · have hχ0 : χ x = 0 := by
            apply image_eq_zero_of_notMem_tsupport
            exact fun hx => hxU (hχU hx)
          simp [hxs, hxK, hxU, g, hχ0]
  have hKint : Integrable ((s \ K).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (hs.diff hK.measurableSet)
  have hUint : Integrable ((U \ K).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (hU.measurableSet.diff hK.measurableSet)
  calc
    _ ≤ ∫ x, ((s \ K).indicator (fun _ => (1 : ℝ)) x +
        (U \ K).indicator (fun _ => (1 : ℝ)) x) ∂μ := by
      apply integral_mono (by
        exact (((integrable_const (1 : 𝕜)).indicator hs).sub g.integrable).norm)
        (hKint.add hUint) hpoint
    _ = μ.real (s \ K) + μ.real (U \ K) := by
      rw [integral_add hKint hUint]
      change (∫ x, (s \ K).indicator (1 : X → ℝ) x ∂μ) +
        (∫ x, (U \ K).indicator (1 : X → ℝ) x ∂μ) = _
      rw [integral_indicator_one (hs.diff hK.measurableSet),
        integral_indicator_one (hU.measurableSet.diff hK.measurableSet)]
    _ ≤ ε / 2 + ε / 2 := add_le_add
      (ENNReal.toReal_le_of_le_ofReal (by positivity) hsmallK.le)
      (ENNReal.toReal_le_of_le_ofReal (by positivity) hsmallU.le)
    _ = ε := by ring

theorem scalarIntegral_l1_bound {X : Type u} [MeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (ν : VectorMeasure X 𝕜) (f : X → 𝕜) :
    ‖scalarIntegral ν f‖ ≤ ∫ x, ‖f x‖ ∂ν.variation := by
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℝ 𝕜‖ * ∫ x, ‖f x‖ ∂ν.variation :=
      VectorMeasure.norm_integral_le_integral_norm
    _ ≤ 1 * ∫ x, ‖f x‖ ∂ν.variation :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ 𝕜)
        (integral_nonneg (fun x => norm_nonneg _))
    _ = _ := one_mul _

/-- Continuous tests determine finite scalar Radon measures on arbitrary LCH spaces. -/
theorem scalarIntegral_injective {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (ν η : VectorMeasure X 𝕜)
    (hν : FiniteScalarRadon ν) (hη : FiniteScalarRadon η)
    (heq : ∀ f : C₀(X, 𝕜), scalarIntegral ν f = scalarIntegral η f) : ν = η := by
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : IsFiniteMeasure η.variation := ⟨hη.1⟩
  have : ν.variation.Regular :=
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  have : η.variation.Regular :=
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hη.2
  let μ := ν.variation + η.variation
  have : μ.Regular := regular_add _ _
  ext s hs
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨g, _, hg⟩ := exists_compactlySupported_indicator_approx μ hs (half_pos hε) (𝕜 := 𝕜)
  let φ : X → 𝕜 := s.indicator (fun _ => 1)
  have hμint : Integrable (fun x => ‖φ x - g x‖) μ :=
    (((integrable_const (1 : 𝕜)).indicator hs).sub g.integrable).norm
  have hnear (ξ : VectorMeasure X 𝕜) [IsFiniteMeasure ξ.variation]
      (hξ : ξ.variation ≤ μ) : ‖ξ s - scalarIntegral ξ g‖ ≤ ε / 2 := by
    have hφint : Integrable φ ξ.variation := (integrable_const (1 : 𝕜)).indicator hs
    have hgint : Integrable (g : X → 𝕜) ξ.variation :=
      ((g : C₀(X, 𝕜)).toBCF.integrable ξ.variation)
    have hi : scalarIntegral ξ φ = ξ s := by
      simp only [scalarIntegral, φ, VectorMeasure.integral_indicator_const _ hs,
        ContinuousLinearMap.mul_apply', one_mul]
    calc
      _ = ‖scalarIntegral ξ (φ - g)‖ := by
        have hsub : scalarIntegral ξ (φ - g) = scalarIntegral ξ φ - scalarIntegral ξ g :=
          VectorMeasure.integral_fun_sub hφint hgint
        rw [hsub, hi]
      _ ≤ ∫ x, ‖φ x - g x‖ ∂ξ.variation := scalarIntegral_l1_bound ξ _
      _ ≤ ∫ x, ‖φ x - g x‖ ∂μ := integral_mono_measure hξ
        (Eventually.of_forall (fun x => norm_nonneg _)) hμint
      _ ≤ ε / 2 := hg
  have hn := hnear ν (Measure.le_add_right le_rfl)
  have hη' := hnear η (Measure.le_add_left le_rfl)
  have hgeq : scalarIntegral ν g = scalarIntegral η g := heq (g : C₀(X, 𝕜))
  calc
    dist (ν s) (η s) = ‖ν s - η s‖ := dist_eq_norm _ _
    _ ≤ ‖ν s - scalarIntegral ν g‖ + ‖scalarIntegral ν g - η s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖ν s - scalarIntegral ν g‖ + ‖η s - scalarIntegral η g‖ := by rw [hgeq, norm_sub_rev (scalarIntegral η g) (η s)]
    _ ≤ ε / 2 + ε / 2 := add_le_add hn hη'
    _ = ε := by ring

def radialClip {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) : 𝕜 := (max 1 ‖z‖)⁻¹ • z

@[simp] theorem radialClip_zero {𝕜 : Type*} [RCLike 𝕜] : radialClip (0 : 𝕜) = 0 := by
  simp [radialClip]

theorem continuous_radialClip {𝕜 : Type*} [RCLike 𝕜] : Continuous (radialClip : 𝕜 → 𝕜) := by
  unfold radialClip
  exact ((continuous_const.max continuous_norm).inv₀ (fun z => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))).smul continuous_id

theorem norm_radialClip_le_one {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) : ‖radialClip z‖ ≤ 1 := by
  rw [radialClip, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (le_trans zero_le_one (le_max_left _ _))]
  exact (inv_mul_le_one₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr (le_max_right _ _)

theorem norm_radialClip_sub_self_le {𝕜 : Type*} [RCLike 𝕜] (z w : 𝕜) (hw : ‖w‖ ≤ 1) :
    ‖radialClip z - z‖ ≤ ‖z - w‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · simp [radialClip, max_eq_left hz]
  · have hz' : 1 < ‖z‖ := lt_of_not_ge hz
    have hz0 : 0 < ‖z‖ := zero_lt_one.trans hz'
    have hi : ‖z‖⁻¹ ≤ 1 := (inv_le_one₀ hz0).mpr hz'.le
    calc
      ‖radialClip z - z‖ = ‖(‖z‖⁻¹ - 1) • z‖ := by
        rw [radialClip, max_eq_right hz'.le, sub_smul, one_smul]
      _ = (1 - ‖z‖⁻¹) * ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hi), neg_sub]
      _ = ‖z‖ - 1 := by rw [sub_mul, one_mul, inv_mul_cancel₀ hz0.ne']
      _ ≤ ‖z‖ - ‖w‖ := sub_le_sub_left hw _
      _ ≤ ‖z-w‖ := norm_sub_norm_le _ _

theorem norm_radialClip_sub_le {𝕜 : Type*} [RCLike 𝕜] (z w : 𝕜) (hw : ‖w‖ ≤ 1) :
    ‖radialClip z - w‖ ≤ 2 * ‖z - w‖ := by
  calc
    ‖radialClip z - w‖ ≤ ‖radialClip z - z‖ + ‖z-w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖z-w‖ + ‖z-w‖ := add_le_add (norm_radialClip_sub_self_le z w hw) le_rfl
    _ = _ := (two_mul _).symm

def clipCompactlySupported {X : Type u} [TopologicalSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (f : C_c(X, 𝕜)) : C_c(X, 𝕜) where
  toFun x := radialClip (f x)
  continuous_toFun := continuous_radialClip.comp f.continuous
  hasCompactSupport' := HasCompactSupport.comp_left f.hasCompactSupport' (g := (radialClip : 𝕜 → 𝕜)) radialClip_zero

def normingPhase {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) : 𝕜 := star z / (‖z‖ : 𝕜)

theorem norm_normingPhase_le_one {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    ‖normingPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [normingPhase, hz]
  · simp [normingPhase, norm_ne_zero_iff.mpr hz]

theorem normingPhase_mul {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    normingPhase z * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [normingPhase, hz]
  · have hn : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    rw [normingPhase, div_mul_eq_mul_div]
    change (starRingEnd 𝕜) z * z / (‖z‖ : 𝕜) = _
    rw [RCLike.conj_mul, pow_two, mul_div_cancel_right₀ _ hn]

theorem norm_partition_phase_le_one {X : Type u} [MeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (ν : VectorMeasure X 𝕜)
    (P : Finset (Set X)) (hP : (P : Set (Set X)).PairwiseDisjoint id) (x : X) :
    ‖∑ p ∈ P, p.indicator (fun _ => normingPhase (ν p)) x‖ ≤ 1 := by
  classical
  by_cases hx : ∃ p ∈ P, x ∈ p
  · obtain ⟨p, hp, hxp⟩ := hx
    have hsum : (∑ q ∈ P, q.indicator (fun _ => normingPhase (ν q)) x) = normingPhase (ν p) := by
      rw [Finset.sum_eq_single p]
      · simp [hxp]
      · intro q hq hqp
        have hxq : x ∉ q := by
          intro hxq
          exact Set.disjoint_left.mp (hP hp hq (Ne.symm hqp)) hxp hxq
        simp [hxq]
      · exact fun h => (h hp).elim
    rw [hsum]
    exact norm_normingPhase_le_one _
  · have hzero : (∑ q ∈ P, q.indicator (fun _ => normingPhase (ν q)) x) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact indicator_of_notMem (fun hxq => hx ⟨q, hq, hxq⟩) _
    rw [hzero, norm_zero]
    exact zero_le_one

theorem scalarIntegral_partition_phase {X : Type u} [MeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation]
    (P : Finset (Set X)) (hP : ∀ p ∈ P, MeasurableSet p) :
    scalarIntegral ν (fun x => ∑ p ∈ P, p.indicator (fun _ => normingPhase (ν p)) x) =
      ((∑ p ∈ P, ‖ν p‖ : ℝ) : 𝕜) := by
  unfold scalarIntegral
  rw [VectorMeasure.integral_finsetSum P (fun p hp => (integrable_const _).indicator (hP p hp))]
  rw [RCLike.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [VectorMeasure.integral_indicator_const _ (hP p hp)]
  exact normingPhase_mul _


theorem exists_compactlySupported_constant_indicator_approx
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] [μ.Regular] {𝕜 : Type*} [RCLike 𝕜]
    (happrox : ∀ (s : Set X), MeasurableSet s → ∀ ε : ℝ, 0 < ε →
      ∃ g : C_c(X,𝕜), (∫ x, ‖s.indicator (fun _ => (1:𝕜)) x - g x‖ ∂μ) ≤ ε)
    {s : Set X} (hs : MeasurableSet s) (c : 𝕜) (hc : ‖c‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(X,𝕜), (∫ x, ‖s.indicator (fun _ => c) x - g x‖ ∂μ) ≤ ε := by
  obtain ⟨g, hg⟩ := happrox s hs ε hε
  refine ⟨c • g, ?_⟩
  have heq (x : X) : s.indicator (fun _ => c) x - (c • g) x =
      c * (s.indicator (fun _ => (1:𝕜)) x - g x) := by
    by_cases hx : x ∈ s <;> simp [hx, mul_sub]
  calc
    (∫ x, ‖s.indicator (fun _ => c) x - (c • g) x‖ ∂μ) =
        ‖c‖ * (∫ x, ‖s.indicator (fun _ => (1:𝕜)) x - g x‖ ∂μ) := by
      simp only [heq, norm_mul]
      exact integral_const_mul _ _
    _ ≤ (∫ x, ‖s.indicator (fun _ => (1:𝕜)) x - g x‖ ∂μ) :=
      mul_le_of_le_one_left (integral_nonneg fun x => norm_nonneg _) hc
    _ ≤ ε := hg

theorem exists_compactlySupported_finset_indicator_approx
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] [μ.Regular] {𝕜 : Type*} [RCLike 𝕜]
    (happrox : ∀ (s : Set X), MeasurableSet s → ∀ ε : ℝ, 0 < ε →
      ∃ g : C_c(X,𝕜), (∫ x, ‖s.indicator (fun _ => (1:𝕜)) x - g x‖ ∂μ) ≤ ε)
    (P : Finset (Set X)) (c : Set X → 𝕜)
    (hP : ∀ p ∈ P, MeasurableSet p) (hc : ∀ p ∈ P, ‖c p‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(X,𝕜), (∫ x, ‖(∑ p ∈ P, p.indicator (fun _ => c p) x) - g x‖ ∂μ) ≤ ε := by
  classical
  induction P using Finset.induction_on generalizing ε with
  | empty => exact ⟨0, by simpa using hε.le⟩
  | @insert p P hp ih =>
    have hpmeas := hP p (Finset.mem_insert_self p P)
    obtain ⟨f, hf⟩ := exists_compactlySupported_constant_indicator_approx μ happrox hpmeas
      (c p) (hc p (Finset.mem_insert_self p P)) (half_pos hε)
    obtain ⟨g, hg⟩ := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
      (fun q hq => hc q (Finset.mem_insert_of_mem hq)) (half_pos hε)
    refine ⟨f+g, ?_⟩
    have hfp : Integrable (fun x => p.indicator (fun _ => c p) x - f x) μ :=
      ((integrable_const _).indicator hpmeas).sub f.integrable
    have hgP : Integrable (fun x => (∑ q ∈ P, q.indicator (fun _ => c q) x) - g x) μ :=
      (integrable_finsetSum P (fun q hq => (integrable_const _).indicator
        (hP q (Finset.mem_insert_of_mem hq)))).sub g.integrable
    calc
      (∫ x, ‖(∑ q ∈ insert p P, q.indicator (fun _ => c q) x) - (f+g) x‖ ∂μ) ≤
          ∫ x, ‖p.indicator (fun _ => c p) x - f x‖ +
            ‖(∑ q ∈ P, q.indicator (fun _ => c q) x) - g x‖ ∂μ := by
        apply integral_mono
          ((integrable_finsetSum (insert p P) (fun q hq => (integrable_const (c q)).indicator (hP q hq))).sub (f+g).integrable).norm
          (hfp.norm.add hgP.norm)
        intro x
        change ‖(∑ q ∈ insert p P, q.indicator (fun _ => c q) x) - (f x + g x)‖ ≤ _
        rw [Finset.sum_insert hp]
        change ‖p.indicator (fun _ => c p) x + (∑ q ∈ P, q.indicator (fun _ => c q) x) -
          (f x + g x)‖ ≤ _
        have hh := norm_add_le (p.indicator (fun _ => c p) x - f x)
          ((∑ q ∈ P, q.indicator (fun _ => c q) x) - g x)
        convert hh using 1; congr 1; abel
      _ = (∫ x, ‖p.indicator (fun _ => c p) x - f x‖ ∂μ) +
          ∫ x, ‖(∑ q ∈ P, q.indicator (fun _ => c q) x) - g x‖ ∂μ :=
        integral_add hfp.norm hgP.norm
      _ ≤ ε/2 + ε/2 := add_le_add hf hg
      _ = ε := add_halves ε


theorem partition_sum_le_scalarMeasureFunctional_norm
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {𝕜 : Type*} [RCLike 𝕜]
    (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] [ν.variation.Regular]
    (P : Finset (Set X)) (hPdisj : (P : Set (Set X)).PairwiseDisjoint id)
    (hP : ∀ p ∈ P, MeasurableSet p) :
    (∑ p ∈ P, ‖ν p‖ : ℝ) ≤ ‖scalarMeasureFunctional ν‖ := by
  classical
  let φ : X → 𝕜 := fun x => ∑ p ∈ P, p.indicator (fun _ => normingPhase (ν p)) x
  have hφ : Integrable φ ν.variation :=
    integrable_finsetSum P (fun p hp => (integrable_const _).indicator (hP p hp))
  have hφbound (x : X) : ‖φ x‖ ≤ 1 := norm_partition_phase_le_one ν P hPdisj x
  apply le_of_forall_pos_le_add
  intro ε hε
  have happrox : ∀ (s : Set X), MeasurableSet s → ∀ δ : ℝ, 0 < δ →
      ∃ g : C_c(X,𝕜), (∫ x, ‖s.indicator (fun _ => (1:𝕜)) x - g x‖ ∂ν.variation) ≤ δ := by
    intro s hs δ hδ
    obtain ⟨g, _, hg⟩ := exists_compactlySupported_indicator_approx ν.variation hs hδ (𝕜 := 𝕜)
    exact ⟨g, hg⟩
  obtain ⟨f, hf⟩ := exists_compactlySupported_finset_indicator_approx ν.variation happrox P
    (fun p => normingPhase (ν p)) hP (fun p _ => norm_normingPhase_le_one _) (half_pos hε)
  let g := clipCompactlySupported f
  have hgint : Integrable (g : X → 𝕜) ν.variation := g.integrable
  have hg0norm : ‖(g : C₀(X,𝕜))‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
    intro x
    exact norm_radialClip_le_one _
  have hclose : (∫ x, ‖φ x - g x‖ ∂ν.variation) ≤ ε := by
    calc
      (∫ x, ‖φ x - g x‖ ∂ν.variation) ≤ ∫ x, 2 * ‖φ x - f x‖ ∂ν.variation := by
        apply integral_mono (hφ.sub hgint).norm (((hφ.sub f.integrable).norm).const_mul 2)
        intro x
        change ‖φ x - radialClip (f x)‖ ≤ 2 * ‖φ x - f x‖
        rw [norm_sub_rev (φ x) (radialClip (f x)), norm_sub_rev (φ x) (f x)]
        exact norm_radialClip_sub_le _ _ (hφbound x)
      _ = 2 * ∫ x, ‖φ x - f x‖ ∂ν.variation := integral_const_mul _ _
      _ ≤ 2 * (ε/2) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = ε := by ring
  have hd : ‖scalarIntegral ν φ - scalarIntegral ν (g : X → 𝕜)‖ ≤ ε := by
    have hsub : scalarIntegral ν φ - scalarIntegral ν (g : X → 𝕜) =
        scalarIntegral ν (fun x => φ x - g x) :=
      (VectorMeasure.integral_fun_sub hφ hgint).symm
    rw [hsub]
    exact (scalarIntegral_l1_bound ν _).trans hclose
  have heq : ‖scalarIntegral ν φ‖ = (∑ p ∈ P, ‖ν p‖ : ℝ) := by
    rw [scalarIntegral_partition_phase ν P hP]
    simp only [RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun p _ => norm_nonneg _)]
  have hn := norm_sub_norm_le (scalarIntegral ν φ) (scalarIntegral ν (g : X → 𝕜))
  calc
    (∑ p ∈ P, ‖ν p‖ : ℝ) ≤ ‖scalarIntegral ν (g : X → 𝕜)‖ + ε := by rw [← heq]; linarith
    _ ≤ ‖scalarMeasureFunctional ν‖ * ‖(g : C₀(X,𝕜))‖ + ε := by
      exact add_le_add ((scalarMeasureFunctional ν).le_opNorm (g : C₀(X,𝕜))) le_rfl
    _ ≤ ‖scalarMeasureFunctional ν‖ + ε := by
      exact add_le_add (mul_le_of_le_one_right (norm_nonneg (scalarMeasureFunctional ν)) hg0norm) le_rfl


theorem scalarMeasureFunctional_norm_eq {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (ν : VectorMeasure X 𝕜)
    [IsFiniteMeasure ν.variation] [ν.variation.Regular] :
    ‖scalarMeasureFunctional ν‖ = ν.variation.real univ := by
  apply le_antisymm (scalarMeasureFunctional_norm_le ν)
  by_contra hn
  have hlt : ‖scalarMeasureFunctional ν‖ < ν.variation.real univ := lt_of_not_ge hn
  have hlt' : ENNReal.ofReal ‖scalarMeasureFunctional ν‖ < ν.variation univ :=
    (ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg (scalarMeasureFunctional ν))
      (measure_ne_top ν.variation univ)).mpr hlt
  obtain ⟨P, _, hPdisj, hPmeas, hPsum⟩ :=
    ν.exists_lt_sum_of_lt_variation MeasurableSet.univ hlt'
  have hsumfinite : (∑ p ∈ P, ‖ν p‖ₑ) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr fun _ _ => enorm_lt_top).ne
  have hsumlt := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hsumfinite).mpr hPsum
  rw [ENNReal.toReal_ofReal (norm_nonneg (scalarMeasureFunctional ν)), ENNReal.toReal_sum (fun _ _ => enorm_ne_top)] at hsumlt
  simp only [toReal_enorm] at hsumlt
  exact (not_lt_of_ge (partition_sum_le_scalarMeasureFunctional_norm ν P hPdisj hPmeas)) hsumlt


/-- Full real Riesz--Markov representation, with exact norm and uniqueness
among all finite signed Radon measures. -/
theorem real_representation : RealRepresentation.{u} := by
  intro X _ _ _ _ _ L
  obtain ⟨ν, hν, hrep⟩ := real_representation_exists L
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : ν.variation.Regular :=
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  have hL : L = scalarMeasureFunctional ν := by
    ext f
    exact (hrep f).2
  refine ⟨ν, hν, hrep, ?_, ?_⟩
  · rw [hL, scalarMeasureFunctional_norm_eq]
  · intro η hη hηrep
    apply scalarIntegral_injective η ν hη hν
    intro f
    exact (hηrep f).2.symm.trans (hrep f).2

/-- Continuous real-linear maps commute with the finite-measure extension. -/
theorem setToFun_postcompose {Y E F G : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {μ : Measure Y} {T : Set Y → E →L[ℝ] F} {U : Set Y → E →L[ℝ] G}
    {C D : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hU : DominatedFinMeasAdditive μ U D) (A : F →L[ℝ] G)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → U s = A.comp (T s))
    (f : Y → E) : setToFun μ U hU f = A (setToFun μ T hT f) := by
  by_cases hf : Integrable f μ
  · apply hf.induction (P := fun f => setToFun μ U hU f = A (setToFun μ T hT f))
    · intro c s hs hμs
      rw [setToFun_indicator_const hU hs hμs.ne, setToFun_indicator_const hT hs hμs.ne,
        h s hs hμs]
      rfl
    · intro f g _ hf hg hfeq hgeq
      rw [setToFun_add hU hf hg, setToFun_add hT hf hg, A.map_add, hfeq, hgeq]
    · exact isClosed_eq (continuous_setToFun hU) (A.continuous.comp (continuous_setToFun hT))
    · intro f g hfg hf heq
      rw [← setToFun_congr_ae hU hfg, ← setToFun_congr_ae hT hfg]
      exact heq
  · rw [setToFun_undef hU hf, setToFun_undef hT hf, map_zero]

/-- The extension respects bounded linear change of its integrand. -/
theorem setToFun_precompose {Y E F G : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {μ : Measure Y} {T : Set Y → F →L[ℝ] G} {U : Set Y → E →L[ℝ] G}
    {C D : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hU : DominatedFinMeasAdditive μ U D) (A : E →L[ℝ] F)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → U s = (T s).comp A)
    (f : Y → E) (hf : Integrable f μ) :
    setToFun μ U hU f = setToFun μ T hT (fun x => A (f x)) := by
  apply hf.induction (P := fun f => setToFun μ U hU f = setToFun μ T hT (fun x => A (f x)))
  · intro c s hs hμs
    have heq : (fun x => A (s.indicator (fun _ => c) x)) = s.indicator (fun _ => A c) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [heq, setToFun_indicator_const hU hs hμs.ne,
      setToFun_indicator_const hT hs hμs.ne, h s hs hμs]
    rfl
  · intro f g _ hf hg hfeq hgeq
    have heq : (fun x => A ((f + g) x)) = (fun x => A (f x)) + (fun x => A (g x)) := by
      ext x
      exact A.map_add _ _
    rw [heq, setToFun_add hU hf hg, setToFun_add hT (A.integrable_comp hf) (A.integrable_comp hg), hfeq, hgeq]
  · have heq : (fun f : Y →₁[μ] E => setToFun μ T hT (fun x => A (f x))) =
        fun f : Y →₁[μ] E => setToFun μ T hT (A.compLp f) := by
      ext f
      exact setToFun_congr_ae hT (A.coeFn_compLp' f).symm
    change IsClosed {f : Y →₁[μ] E | setToFun μ U hU f =
      (fun f : Y →₁[μ] E => setToFun μ T hT (fun x => A (f x))) f}
    rw [heq]
    exact isClosed_eq (continuous_setToFun hU)
      ((continuous_setToFun hT).comp (A.compLpL 1 μ).continuous)
  · intro f g hfg hf heq
    exact (setToFun_congr_ae hU hfg).symm.trans
      (heq.trans (setToFun_congr_ae hT (hfg.fun_comp A)))


lemma variation_mapRange_ofReal {X : Type*} [MeasurableSpace X]
    (α : VectorMeasure X ℝ) :
    (VectorMeasure.mapRangeL Complex.ofRealCLM α).variation = α.variation := by
  have hnorm (s : Set X) :
      ‖(VectorMeasure.mapRangeL Complex.ofRealCLM α) s‖ₑ = ‖α s‖ₑ := by
    change ‖(α s : ℂ)‖ₑ = ‖α s‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  apply le_antisymm
  · apply VectorMeasure.variation_le_of_forall_enorm_le
    intro s hs
    rw [hnorm]
    exact VectorMeasure.enorm_measure_le_variation _ _
  · apply VectorMeasure.variation_le_of_forall_enorm_le
    intro s hs
    rw [← hnorm]
    exact VectorMeasure.enorm_measure_le_variation _ _

lemma scalarIntegral_mapRange_ofReal {X : Type*} [MeasurableSpace X]
    (α : VectorMeasure X ℝ) (f : X → ℂ) :
    scalarIntegral (VectorMeasure.mapRangeL Complex.ofRealCLM α) f =
      α.integral f (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
  simp only [scalarIntegral, VectorMeasure.integral,
    variation_mapRange_ofReal]
  apply setToFun_congr_left'
  intro s hs hsf
  ext z
  change z * (α s : ℂ) = (α s) • z
  simp only [Complex.real_smul, mul_comm]

lemma scalarIntegral_I_smul {X : Type*} [MeasurableSpace X]
    (ν : VectorMeasure X ℂ) (f : X → ℂ) :
    scalarIntegral (Complex.I • ν) f = Complex.I * scalarIntegral ν f := by
  have hv : (Complex.I • ν).variation = ν.variation := by
    rw [VectorMeasure.variation_smul, Complex.nnnorm_I, one_smul]
  simp only [scalarIntegral, VectorMeasure.integral, hv]
  apply setToFun_postcompose _ _ ((ContinuousLinearMap.mul ℝ ℂ) Complex.I)
  intro s hs hsf
  ext z
  change z * (Complex.I * ν s) = Complex.I * (z * ν s)
  ring


lemma signedIntegral_ofReal {X : Type*} [MeasurableSpace X]
    (α : VectorMeasure X ℝ) (f : X → ℝ) (hf : Integrable f α.variation) :
    α.integral (fun x => (f x : ℂ)) (ContinuousLinearMap.lsmul ℝ ℝ).flip =
      ((scalarIntegral α f : ℝ) : ℂ) := by
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight Complex.ofRealCLM
  calc
    _ = α.integral f B := by
      symm
      apply setToFun_precompose
        (dominatedFinMeasAdditive_cbmApplyMeasure α
          (ContinuousLinearMap.lsmul ℝ ℝ).flip)
        (dominatedFinMeasAdditive_cbmApplyMeasure α B) Complex.ofRealCLM _ f hf
      intro s hs hsf
      apply ContinuousLinearMap.ext
      intro r
      change r • (α s : ℂ) = (α s) • (r : ℂ)
      simp only [Complex.real_smul, ← Complex.ofReal_mul, mul_comm]
    _ = ((scalarIntegral α f : ℝ) : ℂ) := by
      apply setToFun_postcompose
        (dominatedFinMeasAdditive_cbmApplyMeasure α (ContinuousLinearMap.mul ℝ ℝ))
        (dominatedFinMeasAdditive_cbmApplyMeasure α B) Complex.ofRealCLM
      intro s hs hsf
      apply ContinuousLinearMap.ext
      intro r
      change r • (α s : ℂ) = ((r * α s : ℝ) : ℂ)
      simp only [Complex.real_smul, Complex.ofReal_mul]


/-- The complex scalar existence theorem, constructed from the real theorem. -/
theorem complex_representation_exists {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (L : C₀(X, ℂ) →L[ℂ] ℂ) :
    ∃ ν : VectorMeasure X ℂ, FiniteScalarRadon ν ∧
      ∀ f : C₀(X, ℂ), Integrable f ν.variation ∧ L f = scalarIntegral ν f := by
  let J : C₀(X, ℝ) →L[ℝ] C₀(X, ℂ) := postcompose Complex.ofRealCLM
  let A : C₀(X, ℝ) →L[ℝ] ℝ := Complex.reCLM.comp ((L.restrictScalars ℝ).comp J)
  let B : C₀(X, ℝ) →L[ℝ] ℝ := Complex.imCLM.comp ((L.restrictScalars ℝ).comp J)
  obtain ⟨α, hα, hαrep⟩ := real_representation_exists A
  obtain ⟨β, hβ, hβrep⟩ := real_representation_exists B
  have : IsFiniteMeasure α.variation := ⟨hα.1⟩
  have : IsFiniteMeasure β.variation := ⟨hβ.1⟩
  have : α.variation.Regular := (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hα.2
  have : β.variation.Regular := (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hβ.2
  let a : VectorMeasure X ℂ := VectorMeasure.mapRangeL Complex.ofRealCLM α
  let b : VectorMeasure X ℂ := VectorMeasure.mapRangeL Complex.ofRealCLM β
  let ν : VectorMeasure X ℂ := a + Complex.I • b
  have hva : a.variation = α.variation := variation_mapRange_ofReal α
  have hvb : b.variation = β.variation := variation_mapRange_ofReal β
  have hvIb : (Complex.I • b).variation = β.variation := by
    rw [VectorMeasure.variation_smul, Complex.nnnorm_I, one_smul, hvb]
  have : IsFiniteMeasure a.variation := by rw [hva]; infer_instance
  have : IsFiniteMeasure (Complex.I • b).variation := by rw [hvIb]; infer_instance
  have hbound : ν.variation ≤ α.variation + β.variation := by
    simpa only [ν, hva, hvIb] using
      (VectorMeasure.variation_add_le (μ := a) (ν := Complex.I • b))
  have : IsFiniteMeasure ν.variation := isFiniteMeasure_of_le (α.variation + β.variation) hbound
  have : (α.variation + β.variation).Regular := regular_add _ _
  have hreg : ν.variation.Regular := regular_of_le hbound
  let F : C₀(X, ℂ) →L[ℂ] ℂ := scalarMeasureFunctional ν
  have hFJ (f : C₀(X, ℝ)) : F (J f) = L (J f) := by
    change scalarIntegral ν (J f) = L (J f)
    calc
      scalarIntegral ν (J f) = scalarIntegral a (J f) + scalarIntegral (Complex.I • b) (J f) :=
        VectorMeasure.integral_add_vectorMeasure ((J f).toBCF.integrable a.variation)
          ((J f).toBCF.integrable (Complex.I • b).variation)
      _ = ((scalarIntegral α f : ℝ) : ℂ) + Complex.I * ((scalarIntegral β f : ℝ) : ℂ) := by
        rw [scalarIntegral_I_smul, scalarIntegral_mapRange_ofReal,
          scalarIntegral_mapRange_ofReal]
        change α.integral (fun x => (f x : ℂ)) (ContinuousLinearMap.lsmul ℝ ℝ).flip +
          Complex.I * β.integral (fun x => (f x : ℂ)) (ContinuousLinearMap.lsmul ℝ ℝ).flip = _
        rw [signedIntegral_ofReal α _ (hαrep f).1, signedIntegral_ofReal β _ (hβrep f).1]
      _ = (A f : ℂ) + Complex.I * (B f : ℂ) := by rw [← (hαrep f).2, ← (hβrep f).2]
      _ = L (J f) := by
        change ((L (J f)).re : ℂ) + Complex.I * ((L (J f)).im : ℂ) = _
        convert Complex.re_add_im (L (J f)) using 1; ring
  refine ⟨ν, ⟨measure_lt_top _ _,
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr hreg⟩, ?_⟩
  intro f
  refine ⟨f.toBCF.integrable ν.variation, ?_⟩
  let r := postcompose Complex.reCLM f
  let i := postcompose Complex.imCLM f
  have hsplit : f = J r + Complex.I • J i := by
    ext x
    change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
    exact (Complex.re_add_im (f x)).symm.trans (by ring)
  change L f = F f
  rw [hsplit, map_add, map_add, map_smul, map_smul, hFJ, hFJ]


/-- Full complex Riesz--Markov representation, with multiplication pairing,
exact norm and uniqueness among all finite complex Radon measures. -/
theorem complex_representation : ComplexRepresentation.{u} := by
  intro X _ _ _ _ _ L
  obtain ⟨ν, hν, hrep⟩ := complex_representation_exists L
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : ν.variation.Regular :=
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  have hL : L = scalarMeasureFunctional ν := by
    ext f
    exact (hrep f).2
  refine ⟨ν, hν, hrep, ?_, ?_⟩
  · rw [hL, scalarMeasureFunctional_norm_eq]
  · intro η hη hηrep
    apply scalarIntegral_injective η ν hη hν
    intro f
    exact (hηrep f).2.symm.trans (hrep f).2

end ExpandedFA.FunctionSpaces.ScalarRieszMarkov
