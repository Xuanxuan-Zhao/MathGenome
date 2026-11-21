import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.GrothendieckLp
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.GrothendieckBound
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.StdBasis

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate InnerProductSpace
universe u
namespace ExpandedFA.PartIV.GrothendieckLp

lemma toL2_injective {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (E : Submodule 𝕜 (Lp 𝕜 p μ))
    (h₂ : ∀ f : E, MemLp (f : Lp 𝕜 p μ) 2 μ) :
    Function.Injective (toL2 μ p E h₂) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Lp 𝕜 2 μ => z.val) h

private lemma coe_sum_smul {X 𝕜 ι : Type*} [MeasurableSpace X] [RCLike 𝕜]
    {μ : Measure X} [Fintype ι] (v : ι → Lp 𝕜 2 μ) (a : ι → 𝕜) :
    ⇑(∑ i, a i • v i) =ᵐ[μ] fun x => ∑ i, a i * v i x := by
  classical
  exact (Lp.coeFn_fun_finsetSum _ _).trans
    ((eventuallyEq_sum fun i _ => Lp.coeFn_smul (a i) (v i)).mono
      fun x hx => by simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx)

/-- Countability is used only for a dense set of coefficients. The finite sums
on both sides are continuous in all coefficients, so the common null set works
for every coefficient vector. -/
private lemma ae_all_sum_bound {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    {μ : Measure X} (W : Submodule 𝕜 (Lp 𝕜 2 μ)) (A : ℝ)
    (hW : ∀ f : W, MemLp (f : Lp 𝕜 2 μ) ∞ μ ∧
      (eLpNorm (f : Lp 𝕜 2 μ) ∞ μ).toReal ≤ A * ‖f‖)
    {n : ℕ} (v : Fin n → W) :
    ∀ᵐ x ∂μ, ∀ a : Fin n → 𝕜,
      ‖∑ i, a i * (v i : Lp 𝕜 2 μ) x‖ ≤ A * ‖∑ i, a i • v i‖ := by
  classical
  have ha (a : Fin n → 𝕜) : ∀ᵐ x ∂μ,
      ‖∑ i, a i * (v i : Lp 𝕜 2 μ) x‖ ≤ A * ‖∑ i, a i • v i‖ := by
    let f : W := ∑ i, a i • v i
    have hb := ae_le_lpNorm_exponent_top (hW f).1
    have he := coe_sum_smul (fun i => (v i : Lp 𝕜 2 μ)) a
    filter_upwards [hb, he] with x hx he
    have hf : (f : Lp 𝕜 2 μ) = ∑ i, a i • (v i : Lp 𝕜 2 μ) := by simp [f]
    have hb : lpNorm (f : Lp 𝕜 2 μ) ∞ μ ≤ A * ‖f‖ := by
      simpa only [toReal_eLpNorm] using (hW f).2
    rw [hf, he] at hx
    rw [hf] at hb
    exact hx.trans hb
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (Fin n → 𝕜)
  have hs : ∀ᵐ x ∂μ, ∀ a ∈ s,
      ‖∑ i, a i * (v i : Lp 𝕜 2 μ) x‖ ≤ A * ‖∑ i, a i • v i‖ :=
    (ae_ball_iff hsc).mpr fun a _ => ha a
  filter_upwards [hs] with x hx
  have hc : IsClosed {a : Fin n → 𝕜 |
      ‖∑ i, a i * (v i : Lp 𝕜 2 μ) x‖ ≤ A * ‖∑ i, a i • v i‖} := by
    apply isClosed_le <;> fun_prop
  have hi := hc.closure_subset_iff.mpr hx
  intro a
  exact hi (hsd a)

private lemma norm_sum_sq {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [Fintype ι] (v : ι → H) (hv : Orthonormal 𝕜 v)
    (a : ι → 𝕜) : ‖∑ i, a i • v i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  classical
  rw [@norm_sq_eq_re_inner 𝕜]
  simp only [hv.inner_sum a a Finset.univ, map_sum]
  simp only [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The diagonal of the reproducing kernel of a finite orthonormal family
is bounded by the square of the inclusion constant. -/
private lemma ae_sum_norm_sq_le {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    {μ : Measure X} (W : Submodule 𝕜 (Lp 𝕜 2 μ)) (A : ℝ) (hA : 0 ≤ A)
    (hW : ∀ f : W, MemLp (f : Lp 𝕜 2 μ) ∞ μ ∧
      (eLpNorm (f : Lp 𝕜 2 μ) ∞ μ).toReal ≤ A * ‖f‖)
    {n : ℕ} (v : Fin n → W) (hv : Orthonormal 𝕜 v) :
    ∀ᵐ x ∂μ, ∑ i, ‖(v i : Lp 𝕜 2 μ) x‖ ^ 2 ≤ A ^ 2 := by
  classical
  filter_upwards [ae_all_sum_bound W A hW v] with x hx
  let a : Fin n → 𝕜 := fun i => conj ((v i : Lp 𝕜 2 μ) x)
  let t : ℝ := ‖∑ i, a i • v i‖
  have ht : 0 ≤ t := norm_nonneg _
  have he : t ^ 2 = ∑ i, ‖(v i : Lp 𝕜 2 μ) x‖ ^ 2 := by
    rw [norm_sum_sq v hv a]
    simp only [a, RCLike.norm_conj]
  have hs : ∑ i, a i * (v i : Lp 𝕜 2 μ) x =
      RCLike.ofReal (∑ i, ‖(v i : Lp 𝕜 2 μ) x‖ ^ 2) := by
    simp only [a, RCLike.conj_mul, map_sum, map_pow]
  have hb := hx a
  rw [hs, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _), ← he] at hb
  have htle : t ≤ A := by nlinarith
  rw [← he]
  nlinarith

private lemma integral_norm_sq {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    {μ : Measure X} (f : Lp 𝕜 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner 𝕜, L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Integrating the diagonal gives n ≤ A² μ(X), including μ = 0. -/
theorem orthonormal_family_bound : Spec.OrthonormalFamilyBound.{u} := by
  intro X _ 𝕜 _ μ _ W A hA hW n v hv
  have hi (i : Fin n) : Integrable (fun x => ‖(v i : Lp 𝕜 2 μ) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (v i).val)).mp
      (Lp.memLp (v i).val)
  have hdiag := ae_sum_norm_sq_le W A hA hW v hv
  have hle := integral_mono_ae (integrable_finsetSum _ (fun i _ => hi i))
    (integrable_const (A ^ 2)) hdiag
  have hnorm (i : Fin n) : ‖(v i : Lp 𝕜 2 μ)‖ = 1 := hv.1 i
  simpa only [integral_finsetSum _ (fun i _ => hi i), integral_norm_sq, hnorm,
    one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, integral_const, smul_eq_mul, mul_comm] using hle

/-- Uniformly bounded dimensions of finitely generated subspaces bound the
algebraic rank, so no separability of the original L² space is required. -/
theorem finite_dimensional_of_L2_bound : Spec.FiniteDimensionOfL2Bound.{u} := by
  classical
  intro X _ 𝕜 _ μ _ W A hA hW
  apply Module.rank_lt_aleph0_iff.mp
  apply lt_of_le_of_lt (rank_le (n := ⌈A ^ 2 * μ.real Set.univ⌉₊) ?_)
    (by simp)
  intro s hs
  let U : Submodule 𝕜 W := Submodule.span 𝕜 (s : Set W)
  letI : FiniteDimensional 𝕜 U := FiniteDimensional.span_of_finite 𝕜 s.finite_toSet
  let b := stdOrthonormalBasis 𝕜 U
  have hb := orthonormal_family_bound X 𝕜 μ W A hA hW
    (Module.finrank 𝕜 U) (fun i => (b i : W))
    (b.orthonormal.comp_linearIsometry U.subtypeₗᵢ)
  have hd : Module.finrank 𝕜 U = s.card :=
    finrank_span_finset_eq_card hs
  rw [hd] at hb
  exact_mod_cast hb.trans (Nat.le_ceil _)

/-- Transport the uniform estimate to the image in L². The representatives
at exponents p and 2 are the same because the underlying AEEqFun is unchanged. -/
lemma toL2_range_bound {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (E : Submodule 𝕜 (Lp 𝕜 p μ))
    (h₂ : ∀ f : E, MemLp (f : Lp 𝕜 p μ) 2 μ)
    (hInf : ∀ f : E, MemLp (f : Lp 𝕜 p μ) ∞ μ) (A : ℝ)
    (hbound : ∀ f : E, (eLpNorm (f : Lp 𝕜 p μ) ∞ μ).toReal ≤
      A * (eLpNorm (f : Lp 𝕜 p μ) 2 μ).toReal) :
    ∀ g : (toL2 μ p E h₂).range,
      MemLp (g : Lp 𝕜 2 μ) ∞ μ ∧
      (eLpNorm (g : Lp 𝕜 2 μ) ∞ μ).toReal ≤ A * ‖g‖ := by
  intro g
  obtain ⟨f, hf⟩ := g.property
  have he : (toL2 μ p E h₂ f : X → 𝕜) =ᵐ[μ] (f : Lp 𝕜 p μ) :=
    Filter.EventuallyEq.rfl
  have hmem : MemLp (toL2 μ p E h₂ f : X → 𝕜) ∞ μ := (hInf f).ae_eq he.symm
  have hb : (eLpNorm (toL2 μ p E h₂ f : X → 𝕜) ∞ μ).toReal ≤
      A * ‖toL2 μ p E h₂ f‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae he, eLpNorm_congr_ae he]
    exact hbound f
  refine ⟨hf ▸ hmem, ?_⟩
  change (eLpNorm (g : Lp 𝕜 2 μ) ∞ μ).toReal ≤ A * ‖(g : Lp 𝕜 2 μ)‖
  rw [← hf]
  exact hb

/-- Apply the upstream closed-graph estimate, then change exponent without
changing the underlying a.e. classes. -/
theorem finite_dimensional : Spec.FiniteDimension.{u} := by
  intro X _ 𝕜 _ μ _ p hp hpt
  letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp μ
  intro E hE hInf
  obtain ⟨C, A, hC, hA, hCp, h₂A⟩ :=
    GrothendieckBound.norm_bounds X 𝕜 μ p hp hpt E hE hInf
  let h₂ : ∀ f : E, MemLp (f : Lp 𝕜 p μ) 2 μ := fun f => (h₂A f).1
  let T := toL2 μ p E h₂
  have hW := toL2_range_bound μ p E h₂ hInf A (fun f => (h₂A f).2)
  letI := finite_dimensional_of_L2_bound X 𝕜 μ T.range A hA.le hW
  exact FiniteDimensional.of_injective T.rangeRestrict
    ((LinearMap.injective_rangeRestrict_iff T).mpr (toL2_injective μ p E h₂))

/-- The numerical conclusion for every L²-orthonormal family in the original
closed subspace E. -/
theorem quantitative_conclusion : Spec.QuantitativeConclusion.{u} := by
  intro X _ 𝕜 _ μ _ p hp hpt
  letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp μ
  intro E hE hInf
  obtain ⟨C, A, hC, hA, hCp, h₂A⟩ :=
    GrothendieckBound.norm_bounds X 𝕜 μ p hp hpt E hE hInf
  let h₂ : ∀ f : E, MemLp (f : Lp 𝕜 p μ) 2 μ := fun f => (h₂A f).1
  let T := toL2 μ p E h₂
  have hW := toL2_range_bound μ p E h₂ hInf A (fun f => (h₂A f).2)
  refine ⟨A, hA, h₂, (fun f => (h₂A f).2), ?_⟩
  intro n v hv
  have hv' : Orthonormal 𝕜 (fun i => T.rangeRestrict (v i)) := hv
  exact orthonormal_family_bound X 𝕜 μ T.range A hA.le hW n
    (fun i => T.rangeRestrict (v i)) hv'

lemma coe_polynomialToLp (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (q : Polynomial 𝕜) :
    ⇑(polynomialToLp 𝕜 p q) =ᵐ[intervalMeasure] (polynomialFunction 𝕜 q) :=
  AEEqFun.coeFn_mk _ _

lemma polynomialToLp_injective (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) :
    Function.Injective (polynomialToLp 𝕜 p) := by
  intro q r h
  have he : (polynomialFunction 𝕜 q : ℝ → 𝕜) =ᵐ[intervalMeasure]
      polynomialFunction 𝕜 r := by
    exact (coe_polynomialToLp 𝕜 p q).symm.trans
      (h ▸ coe_polynomialToLp 𝕜 p r)
  have ho := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Icc_self he)
    isOpen_Ioo (polynomialFunction 𝕜 q).continuous.continuousOn
    (polynomialFunction 𝕜 r).continuous.continuousOn
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).image
    (RCLike.ofReal_injective (K := 𝕜)).injOn).mono
  rintro z ⟨x, hx, rfl⟩
  simpa only [polynomialFunction, Polynomial.aeval_continuousMap_apply,
    ContinuousMap.coe_mk, Set.mem_ofPred_eq] using ho hx

/-- Polynomial restrictions have infinite algebraic dimension, but each is
bounded on the interval. Closedness would contradict the theorem just proved. -/
theorem polynomial_counterexample : Spec.PolynomialCounterexample := by
  intro 𝕜 _ p hp hpt
  letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp intervalMeasure
  let E := (polynomialToLp 𝕜 p).range
  have hInf (f : E) : MemLp (f : Lp 𝕜 p intervalMeasure) ∞ intervalMeasure := by
    obtain ⟨q, hq⟩ := f.property
    have hm := (polynomial_memLp 𝕜 ∞ q).ae_eq (coe_polynomialToLp 𝕜 p q).symm
    rwa [hq] at hm
  have hdim : ¬ FiniteDimensional 𝕜 E := by
    intro h
    letI := h
    letI := FiniteDimensional.of_injective (polynomialToLp 𝕜 p).rangeRestrict
      ((LinearMap.injective_rangeRestrict_iff _).mpr (polynomialToLp_injective 𝕜 p))
    have hc := (Polynomial.basisMonomials 𝕜).linearIndependent.lt_aleph0_of_finiteDimensional
    simp at hc
  exact ⟨hInf, hdim, fun hE => hdim (finite_dimensional ℝ 𝕜 intervalMeasure p hp hpt E hE hInf)⟩

/-- On counting measure, evaluation of the chosen representative is exactly
linear, because the only null set is empty. -/
def countCoeLinear (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) :
    Lp 𝕜 p (Measure.count : Measure ℕ) →ₗ[𝕜] (ℕ → 𝕜) where
  toFun f := f
  map_add' f g := funext (Measure.ae_count_iff.mp (Lp.coeFn_add f g))
  map_smul' c f := funext (Measure.ae_count_iff.mp (Lp.coeFn_smul c f))

/-- The sequence realization is identified by its p-th power series, not just
by the name of the counting-measure Lp type. -/
theorem sequence_identification : Spec.SequenceIdentification := by
  intro 𝕜 _ p hp hpt a
  have hm : AEStronglyMeasurable a (Measure.count : Measure ℕ) :=
    AEStronglyMeasurable.of_discrete
  refine ⟨?_, ?_, ?_⟩
  · rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp.ne' hpt.ne hm,
      lintegral_count]
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp.ne' hpt.ne hm, lintegral_count]
  · intro ha
    have he : ⇑(ha.toLp a) = a := funext (Measure.ae_count_iff.mp ha.coeFn_toLp)
    refine ⟨ha.toLp a, he, ?_⟩
    intro g hg
    apply Lp.ext
    exact ae_of_all _ (fun n => by rw [hg, he])

lemma countLp_infinite_dimensional (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) :
    ¬ FiniteDimensional 𝕜 (Lp 𝕜 p (Measure.count : Measure ℕ)) := by
  classical
  let v : ℕ → Lp 𝕜 p (Measure.count : Measure ℕ) := fun n =>
    indicatorConstLp p (measurableSet_singleton n) (by simp) 1
  have he : (countCoeLinear 𝕜 p) ∘ v = fun n => Pi.single n (1 : 𝕜) := by
    funext n x
    have hx := Measure.ae_count_iff.mp
      (indicatorConstLp_coeFn (p := p) (μ := (Measure.count : Measure ℕ))
        (hs := measurableSet_singleton n) (hμs := by simp) (c := (1 : 𝕜))) x
    change v n x = _
    simpa only [Set.indicator_singleton, Pi.single_apply] using hx
  have hv : LinearIndependent 𝕜 v := by
    apply LinearIndependent.of_comp (countCoeLinear 𝕜 p)
    rw [he]
    exact Pi.linearIndependent_single_one ℕ 𝕜
  intro h
  letI := h
  have hc := hv.lt_aleph0_of_finiteDimensional
  simp at hc

lemma countLp_memLp_infinity (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (hp : p ≠ 0)
    (f : Lp 𝕜 p (Measure.count : Measure ℕ)) :
    MemLp f ∞ (Measure.count : Measure ℕ) := by
  apply memLp_top_of_bound (Lp.aestronglyMeasurable f)
    (eLpNorm f p (Measure.count : Measure ℕ)).toReal
  apply ae_of_all
  intro n
  simpa only [toReal_enorm] using
    ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (enorm_le_eLpNorm_count f n hp)

lemma sequenceToIntervals_eLpNorm (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞)
    (f : Lp 𝕜 p (Measure.count : Measure ℕ)) :
    eLpNorm (sequenceToIntervals 𝕜 p f) p stripMeasure =
      eLpNorm f p (Measure.count : Measure ℕ) := by
  have he : ⇑(sequenceToIntervals 𝕜 p f) =ᵐ[stripMeasure] f ∘ Prod.fst :=
    Lp.coeFn_compMeasurePreserving f measurePreserving_fst
  rw [eLpNorm_congr_ae he]
  exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) measurePreserving_fst

lemma sequenceToIntervals_isometry (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (hp : 0 < p) :
    letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp (Measure.count : Measure ℕ)
    letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp stripMeasure
    Isometry (sequenceToIntervals 𝕜 p) := by
  letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp (Measure.count : Measure ℕ)
  letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp stripMeasure
  apply AddMonoidHomClass.isometry_of_norm (sequenceToIntervals 𝕜 p)
  intro f
  change (GrothendieckBound.lpMass p stripMeasure (sequenceToIntervals 𝕜 p f)).toReal =
    (GrothendieckBound.lpMass p (Measure.count : Measure ℕ) f).toReal
  simp only [GrothendieckBound.lpMass, sequenceToIntervals_eLpNorm]

/-- The range is closed because ℓp is complete in the positive-exponent metric
and its realization on the disjoint intervals is isometric in that metric. -/
theorem infinite_measure_counterexample : Spec.InfiniteMeasureCounterexample := by
  intro 𝕜 _ p hp hpt
  letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp stripMeasure
  letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp (Measure.count : Measure ℕ)
  letI := GrothendieckBound.positiveLp_complete ℕ 𝕜 (Measure.count : Measure ℕ) p hp
  let T := sequenceToIntervals 𝕜 p
  let E := T.range
  have hT : Isometry T := sequenceToIntervals_isometry 𝕜 p hp
  have hE : IsClosed (E : Set (Lp 𝕜 p stripMeasure)) := hT.isClosedEmbedding.isClosed_range
  have hInf (f : E) : MemLp (f : Lp 𝕜 p stripMeasure) ∞ stripMeasure := by
    obtain ⟨g, hg⟩ := f.property
    have hm := (countLp_memLp_infinity 𝕜 p hp.ne' g).comp_measurePreserving
      (measurePreserving_fst (μ := (Measure.count : Measure ℕ)) (ν := intervalMeasure))
    have he := Lp.coeFn_compMeasurePreserving g
      (measurePreserving_fst (μ := (Measure.count : Measure ℕ)) (ν := intervalMeasure))
    have hmem := hm.ae_eq he.symm
    change MemLp (T g : ℕ × ℝ → 𝕜) ∞ stripMeasure at hmem
    rwa [hg] at hmem
  have hdim : ¬ FiniteDimensional 𝕜 E := by
    intro h
    letI := h
    have hd := FiniteDimensional.of_injective T.rangeRestrict
      ((LinearMap.injective_rangeRestrict_iff T).mpr hT.injective)
    exact countLp_infinite_dimensional 𝕜 p hd
  refine ⟨?_, ?_, ?_, ?_, sequenceToIntervals_eLpNorm 𝕜 p,
    hT.injective, hE, hInf, hdim⟩
  · change (Measure.count.prod intervalMeasure) Set.univ = ∞
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    simp
  · intro n
    simp [stripMeasure, unitBlock, Measure.prod_prod, intervalMeasure, Real.volume_Icc]
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hx hy
    simp only [unitBlock, Set.mem_prod, Set.mem_singleton_iff] at hx hy
    exact hnm (hx.1.symm.trans hy.1)
  · intro g
    exact Lp.coeFn_compMeasurePreserving g measurePreserving_fst

end ExpandedFA.PartIV.GrothendieckLp
