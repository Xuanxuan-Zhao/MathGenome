import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.EllipticParametrix
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.FourierHilbertScale
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.TemperedExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HilbertScaleLocalOperations
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Set
open scoped SchwartzMap ContDiff FourierTransform ComplexConjugate Topology Manifold

namespace ExpandedFA.Sobolev.Elliptic
open ExpandedFA.Fourier ExpandedFA.Distributions

lemma wordPartial_complex {d : ℕ} (w : List (Fin d)) (T : Tempered ℂ d) :
    wordPartial w T = LocalOperations.wordDerivative w T := by
  induction w generalizing T with
  | nil => rfl
  | cons i w ih => exact ih _

lemma wordPartial_real {d : ℕ} (w : List (Fin d)) (T : Tempered ℝ d) :
    wordPartial w T = LocalOperations.realWordDerivative w T := by
  induction w generalizing T with
  | nil => rfl
  | cons i w ih => exact ih _

lemma fourierSymbol_hasTemperateGrowth {d : ℕ} (c : Coefficients ℂ d) :
    (fourierSymbol c).HasTemperateGrowth := by
  unfold fourierSymbol
  apply Function.HasTemperateGrowth.sum
  intro α hα
  exact (Function.HasTemperateGrowth.const (c α)).mul
    (FourierScale.derivativeSymbol_hasTemperateGrowth α)

/-- This uses the proved coordinate-derivative bridge, so the symbol is attached
to the actual negative-transpose differential operator. -/
theorem fourier_operator :
    Specs.ExpandedFA.Sobolev.EllipticParametrix.fourierOperatorType := by
  intro d c T
  have hg (α : Fin d → ℕ) :
      (fun ξ : Euclidean d => c α * FourierScale.derivativeSymbol α ξ).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (c α)).mul
      (FourierScale.derivativeSymbol_hasTemperateGrowth α)
  rw [show fourierSymbol c = fun ξ =>
    ∑ α ∈ c.support, c α * FourierScale.derivativeSymbol α ξ from rfl,
    TemperedDistribution.smulLeftCLM_sum (fun α _ => hg α)]
  ext φ
  simp only [temperedFourier, applyOperator, ContinuousLinearMap.comp_apply,
    sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro α hα
  change (c α • temperedFourier (wordPartial (multiIndexWord α) T)) φ = _
  have hw (w : List (Fin d)) (U : Tempered ℂ d) :
      wordPartial w U = FourierScale.temperedWordDerivative w U := by
    induction w generalizing U with
    | nil => rfl
    | cons i w ih => exact ih _
  rw [hw, FourierScale.fourier_temperedMultiIndexDerivative]
  have h := congrArg
    (fun A : TemperedDistribution (Euclidean d) ℂ →L[ℂ]
      TemperedDistribution (Euclidean d) ℂ => A (temperedFourier T))
    (TemperedDistribution.smulLeftCLM_smul
      (FourierScale.derivativeSymbol_hasTemperateGrowth α) (c α))
  exact congrArg (fun S : Tempered ℂ d => S φ) h.symm

lemma regularSchwartz_complex {d : ℕ} (f : Schwartz ℂ d) :
    regularSchwartz f = schwartzRegularDistribution f := rfl

@[simp] lemma regularSchwartz_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f φ : Schwartz 𝕜 d) : regularSchwartz f φ = ∫ x, f x * φ x := rfl

@[simp] lemma regularSchwartz_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    regularSchwartz (0 : Schwartz 𝕜 d) = 0 := by
  ext φ
  simp

lemma smoothOn_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {T : Tempered 𝕜 d} {U : Set (Euclidean d)} (h : SmoothOn T U) (a : 𝕜) :
    SmoothOn (a • T) U := by
  obtain ⟨f, hf, hpair⟩ := h
  refine ⟨fun x => a * f x, contDiffOn_const.mul hf, ?_⟩
  intro φ hφ hU
  obtain ⟨hi, he⟩ := hpair φ hφ hU
  refine ⟨?_, ?_⟩
  · simpa only [mul_assoc] using hi.const_mul a
  · simp only [smul_apply, smul_eq_mul, he, mul_assoc,
      integral_const_mul]

lemma smoothOn_delta_punctured {𝕜 : Type} [RCLike 𝕜] (d : ℕ) :
    SmoothOn (Examples.delta 𝕜 d) ({0}ᶜ : Set (Euclidean d)) := by
  refine ⟨0, contDiffOn_const, ?_⟩
  intro φ hφ hU
  have h0 : (0 : Euclidean d) ∉ tsupport φ := by
    intro h
    exact hU h (by simp)
  have hφ0 := image_eq_zero_of_notMem_tsupport h0
  simp [Examples.delta, hφ0]

lemma dsupport_smul_subset {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : 𝕜) (T : Tempered 𝕜 d) :
    Distribution.dsupport (fun φ : Schwartz 𝕜 d => (a • T) φ) ⊆
      Distribution.dsupport (fun φ : Schwartz 𝕜 d => T φ) := by
  apply Distribution.dsupport_subset_dsupport
  intro U hU hT φ hφ
  simp [hT φ hφ]

lemma dsupport_delta_subset {𝕜 : Type} [RCLike 𝕜] (d : ℕ) :
    Distribution.dsupport (fun φ : Schwartz 𝕜 d => Examples.delta 𝕜 d φ) ⊆ {0} := by
  intro x hx
  apply (Distribution.mem_dsupport_iff x).mp hx {0} ?_ isClosed_singleton
  intro φ hφ
  have h0 : (0 : Euclidean d) ∉ tsupport φ := by
    intro h
    exact hφ h (by simp)
  change φ 0 = 0
  exact image_eq_zero_of_notMem_tsupport h0

lemma applyOperator_single_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : 𝕜) (T : Tempered 𝕜 d) :
    applyOperator (Finsupp.single (0 : Fin d → ℕ) a) T = a • T := by
  classical
  by_cases ha : a = 0
  · subst a
    ext φ
    simp [applyOperator]
  · have hz : multiIndexWord (0 : Fin d → ℕ) = [] := by
      simp only [multiIndexWord, Pi.zero_apply, List.replicate_zero]
      apply List.flatMap_eq_nil_iff.mpr
      intro i hi
      rfl
    simp only [applyOperator, Finsupp.support_single _ ha, Finset.sum_singleton,
      Finsupp.single_eq_same, hz, wordPartial]

lemma degree_eq_zero_iff {d : ℕ} (α : Fin d → ℕ) : degree α = 0 ↔ α = 0 := by
  simp only [degree, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp [funext_iff]

lemma hasOrder_zero_iff {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (c : Coefficients 𝕜 d) :
    HasOrder c 0 ↔ ∃ a : 𝕜, a ≠ 0 ∧ c = Finsupp.single (0 : Fin d → ℕ) a := by
  classical
  constructor
  · intro ⟨hb, α, hα, hdeg⟩
    have hα0 : α = 0 := (degree_eq_zero_iff α).mp hdeg
    subst α
    refine ⟨c 0, Finsupp.mem_support_iff.mp hα, ?_⟩
    ext β
    by_cases hβ : β = 0
    · subst β
      simp
    · have hn : β ∉ c.support := by
        intro hm
        exact hβ ((degree_eq_zero_iff β).mp (Nat.eq_zero_of_le_zero (hb β hm)))
      simp [hβ, Finsupp.notMem_support_iff.mp hn]
  · rintro ⟨a, ha, rfl⟩
    simp [HasOrder, Finsupp.support_single _ ha, degree]

/-- The complete order-zero case, over either field and in every dimension.
Both the global Schwartz remainder and the localized smooth remainder are zero. -/
theorem order_zero_parametrix {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (hc : HasOrder c 0) :
    ∃ (Q : Tempered 𝕜 d) (r : Schwartz 𝕜 d),
      Distribution.dsupport (fun φ : Schwartz 𝕜 d => Q φ) ⊆ {0} ∧
      SmoothOn Q ({0}ᶜ : Set (Euclidean d)) ∧
      applyOperator c Q = Examples.delta 𝕜 d + regularSchwartz r := by
  obtain ⟨a, ha, rfl⟩ := (hasOrder_zero_iff c).mp hc
  refine ⟨a⁻¹ • Examples.delta 𝕜 d, 0,
    (dsupport_smul_subset _ _).trans (dsupport_delta_subset d),
    smoothOn_smul (smoothOn_delta_punctured d) a⁻¹, ?_⟩
  rw [applyOperator_single_zero, smul_smul, mul_inv_cancel₀ ha, one_smul,
    regularSchwartz_zero, add_zero]

/-- Exact order prevents a vacuous positive-order ellipticity hypothesis in
Euclidean dimension zero. -/
lemma order_dimension_zero {𝕜 : Type} [RCLike 𝕜]
    (c : Coefficients 𝕜 0) (m : ℕ) (hc : HasOrder c m) : m = 0 := by
  obtain ⟨_, α, _, hα⟩ := hc
  simpa [degree] using hα.symm

/-- Boundary cases satisfy both conclusions, with support in every prescribed
positive ball. This includes the entire zero-dimensional problem. -/
theorem boundary_parametrix {𝕜 : Type} [RCLike 𝕜] {d m : ℕ}
    (c : Coefficients 𝕜 d) (hc : HasOrder c m) (h : d = 0 ∨ m = 0) :
    ∃ (Q : Tempered 𝕜 d) (r : Schwartz 𝕜 d),
      (∀ R : ℝ, 0 < R →
        Distribution.dsupport (fun φ : Schwartz 𝕜 d => Q φ) ⊆ Metric.ball 0 R) ∧
      SmoothOn Q ({0}ᶜ : Set (Euclidean d)) ∧
      applyOperator c Q = Examples.delta 𝕜 d + regularSchwartz r := by
  have hm : m = 0 := by
    rcases h with hd | hm
    · subst d
      exact order_dimension_zero c m hc
    · exact hm
  subst m
  obtain ⟨Q, r, hs, hQ, he⟩ := order_zero_parametrix c hc
  refine ⟨Q, r, ?_, hQ, he⟩
  intro R hR x hx
  have hx0 : x = 0 := hs hx
  simpa only [hx0, Metric.mem_ball, dist_self] using hR

/-- Inverse Fourier transform of a regular symbol, using the ordinary volume
functional. Temperate growth is needed for its subsequent product identities,
not assumed as part of ellipticity. -/
def inverseSymbol {d : ℕ} (q : Euclidean d → ℂ) : Tempered ℂ d :=
  𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ q (Examples.oneDistribution ℂ d))

lemma fourier_inverseSymbol {d : ℕ} (q : Euclidean d → ℂ) :
    temperedFourier (inverseSymbol q) =
      TemperedDistribution.smulLeftCLM ℂ q (Examples.oneDistribution ℂ d) := by
  change (𝓕 (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ q
    (Examples.oneDistribution ℂ d)) : TemperedDistribution (Euclidean d) ℂ) :
      TemperedDistribution (Euclidean d) ℂ) = _
  exact FourierTransform.fourier_fourierInv_eq _

lemma multiply_oneDistribution {d : ℕ} (χ : Schwartz ℂ d) :
    TemperedDistribution.smulLeftCLM ℂ χ (Examples.oneDistribution ℂ d) =
      regularSchwartz χ := by
  ext φ
  change (∫ x, (SchwartzMap.smulLeftCLM ℂ (fun x => χ x) φ) x) = ∫ x, χ x * φ x
  simp only [SchwartzMap.smulLeftCLM_apply χ.hasTemperateGrowth, smul_eq_mul]

lemma regularSchwartz_neg {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (χ : Schwartz 𝕜 d) :
    regularSchwartz (-χ) = -regularSchwartz χ := by
  ext φ
  simp [integral_neg]

/-- The full distributional equation follows from the reciprocal-symbol
identity. The remaining analytic obligations are constructing q from principal
ellipticity and proving that inverseSymbol q is smooth off zero. -/
theorem inverse_symbol_equation {d : ℕ} (c : Coefficients ℂ d)
    (q : Euclidean d → ℂ) (hq : q.HasTemperateGrowth) (χ : Schwartz ℂ d)
    (hpq : ∀ ξ, fourierSymbol c ξ * q ξ = 1 - χ ξ) :
    applyOperator c (inverseSymbol q) =
      Examples.delta ℂ d + regularSchwartz (-(𝓕⁻ χ) : Schwartz ℂ d) := by
  have hqP : q * fourierSymbol c = fun ξ => 1 - χ ξ := by
    funext ξ
    simpa only [Pi.mul_apply, mul_comm] using hpq ξ
  have hmul : TemperedDistribution.smulLeftCLM ℂ (fourierSymbol c)
      (TemperedDistribution.smulLeftCLM ℂ q (Examples.oneDistribution ℂ d)) =
      Examples.oneDistribution ℂ d - regularSchwartz χ := by
    rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hq
      (fourierSymbol_hasTemperateGrowth c), hqP]
    have hs := congrArg
      (fun A : TemperedDistribution (Euclidean d) ℂ →L[ℂ]
        TemperedDistribution (Euclidean d) ℂ => A (Examples.oneDistribution ℂ d))
      (TemperedDistribution.smulLeftCLM_sub
        (Function.HasTemperateGrowth.const (E := Euclidean d) (1 : ℂ)) χ.hasTemperateGrowth)
    calc
      _ = TemperedDistribution.smulLeftCLM ℂ (fun _ : Euclidean d => 1)
          (Examples.oneDistribution ℂ d) -
          TemperedDistribution.smulLeftCLM ℂ χ (Examples.oneDistribution ℂ d) := hs
      _ = _ := by
        rw [TemperedDistribution.smulLeftCLM_const, one_smul, multiply_oneDistribution]
  obtain ⟨e, he, _⟩ := Inversion.tempered_automorphism d
  apply e.injective
  rw [he, he, fourier_operator d c (inverseSymbol q), fourier_inverseSymbol, hmul]
  have hsum (U V : Tempered ℂ d) :
      temperedFourier (U + V) = temperedFourier U + temperedFourier V := by
    ext φ
    rfl
  rw [hsum]
  rw [(Examples.basic_fourier d).2]
  simp only [regularSchwartz_complex]
  rw [Inversion.fourier_regular_distribution d (-(𝓕⁻ χ) : Schwartz ℂ d)]
  have hχ : schwartzFourier (-(𝓕⁻ χ) : Schwartz ℂ d) = -χ := by
    rw [map_neg]
    change -(𝓕 (𝓕⁻ χ) : Schwartz ℂ d) = -χ
    rw [FourierTransform.fourier_fourierInv_eq]
  rw [hχ]
  change Examples.oneDistribution ℂ d - regularSchwartz χ =
    Examples.oneDistribution ℂ d + regularSchwartz (-χ)
  rw [regularSchwartz_neg, sub_eq_add_neg]

/-- Explicitly quantified interface for the proved boundary cases. -/
theorem boundary_cases :
    Specs.ExpandedFA.Sobolev.EllipticParametrix.boundaryParametrixType := by
  intro 𝕜 _ d m c hc h
  exact boundary_parametrix c hc h

/-- Explicitly quantified interface for the Fourier assembly calculation. -/
theorem reciprocal_equation :
    Specs.ExpandedFA.Sobolev.EllipticParametrix.inverseSymbolEquationType := by
  intro d c q hq χ hpq
  exact inverse_symbol_equation c q hq χ hpq

/-- The ordinary coordinate monomial, without Fourier normalization factors. -/
def coordinateMonomial {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (α : Fin d → ℕ) (ξ : Euclidean d) : 𝕜 := ∏ i, (ξ i : 𝕜) ^ α i

lemma coordinateMonomial_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (α : Fin d → ℕ) (t : ℝ) (ξ : Euclidean d) :
    coordinateMonomial (𝕜 := 𝕜) α (t • ξ) =
      (t : 𝕜) ^ degree α * coordinateMonomial α ξ := by
  simp only [coordinateMonomial, PiLp.smul_apply, smul_eq_mul, map_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, degree]

lemma norm_coordinateMonomial_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (α : Fin d → ℕ) (ξ : Euclidean d) :
    ‖coordinateMonomial (𝕜 := 𝕜) α ξ‖ ≤ ‖ξ‖ ^ degree α := by
  simp only [coordinateMonomial, norm_prod, norm_pow, RCLike.norm_ofReal, degree,
    ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
  intro i hi
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le ξ i) _

lemma continuous_principalSymbol {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (m : ℕ) : Continuous (principalSymbol c m) := by
  unfold principalSymbol
  fun_prop

lemma principalSymbol_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (m : ℕ) (t : ℝ) (ξ : Euclidean d) :
    principalSymbol c m (t • ξ) = (t : 𝕜) ^ m * principalSymbol c m ξ := by
  classical
  change (∑ α ∈ c.support.filter (fun α => degree α = m),
    c α * coordinateMonomial α (t • ξ)) =
      (t : 𝕜) ^ m * (∑ α ∈ c.support.filter (fun α => degree α = m),
        c α * coordinateMonomial α ξ)
  simp only [coordinateMonomial_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [(Finset.mem_filter.mp hα).2]
  ring

/-- Compactness of the unit sphere upgrades pointwise principal ellipticity
into the homogeneous lower bound. This also handles an empty unit sphere. -/
lemma principalSymbol_lower_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (m : ℕ)
    (hc : ∀ ξ : Euclidean d, ξ ≠ 0 → principalSymbol c m ξ ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ ξ : Euclidean d, ξ ≠ 0 →
      a * ‖ξ‖ ^ m ≤ ‖principalSymbol c m ξ‖ := by
  obtain ⟨a, ha, hbound⟩ := (isCompact_sphere (0 : Euclidean d) 1).exists_forall_le'
    (continuous_principalSymbol c m).norm.continuousOn (a := 0) (by
      intro ξ hξ
      exact norm_pos_iff.mpr (hc ξ (by
        intro hz
        simp [hz] at hξ)))
  refine ⟨a, ha, ?_⟩
  intro ξ hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let u : Euclidean d := ‖ξ‖⁻¹ • ξ
  have hu : u ∈ Metric.sphere (0 : Euclidean d) 1 := by
    simp [u, norm_smul, inv_mul_cancel₀ hn.ne']
  have hx : ξ = ‖ξ‖ • u := by
    simp [u, smul_smul, mul_inv_cancel₀ hn.ne']
  calc
    a * ‖ξ‖ ^ m ≤ ‖principalSymbol c m u‖ * ‖ξ‖ ^ m :=
      mul_le_mul_of_nonneg_right (hbound u hu) (by positivity)
    _ = ‖principalSymbol c m ξ‖ := by
      conv_rhs => rw [hx, principalSymbol_smul]
      rw [norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_nonneg hn.le]
      ring

/-- The polynomial before inserting the Fourier normalization factors. -/
def polynomialSymbol {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (ξ : Euclidean d) : 𝕜 :=
  ∑ α ∈ c.support, c α * coordinateMonomial α ξ

lemma polynomialSymbol_sub_principal {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (m : ℕ) (ξ : Euclidean d) :
    polynomialSymbol c ξ - principalSymbol c m ξ =
      ∑ α ∈ c.support.filter (fun α => degree α ≠ m), c α * coordinateMonomial α ξ := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not c.support (fun α => degree α = m)
    (fun α => c α * coordinateMonomial α ξ)
  change (∑ α ∈ c.support, c α * coordinateMonomial α ξ) -
    (∑ α ∈ c.support.filter (fun α => degree α = m), c α * coordinateMonomial α ξ) = _
  rw [← h]
  abel

lemma polynomialSymbol_remainder_bound {𝕜 : Type} [RCLike 𝕜] {d m : ℕ}
    (c : Coefficients 𝕜 d) (hc : HasOrder c m) (ξ : Euclidean d) (hξ : 1 ≤ ‖ξ‖) :
    ‖polynomialSymbol c ξ - principalSymbol c m ξ‖ ≤
      (∑ α ∈ c.support, ‖c α‖) * ‖ξ‖ ^ (m - 1) := by
  classical
  rw [polynomialSymbol_sub_principal]
  calc
    _ ≤ ∑ α ∈ c.support.filter (fun α => degree α ≠ m),
        ‖c α * coordinateMonomial α ξ‖ := norm_sum_le _ _
    _ ≤ ∑ α ∈ c.support.filter (fun α => degree α ≠ m), ‖c α‖ * ‖ξ‖ ^ (m - 1) := by
      apply Finset.sum_le_sum
      intro α hα
      obtain ⟨hs, hd⟩ := Finset.mem_filter.mp hα
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_coordinateMonomial_le α ξ).trans
        (pow_le_pow_right₀ hξ (by have := hc.1 α hs; omega))
    _ ≤ ∑ α ∈ c.support, ‖c α‖ * ‖ξ‖ ^ (m - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro α hα hnot
      positivity
    _ = _ := by rw [Finset.sum_mul]

/-- The finite lower-order terms can be absorbed at sufficiently large
frequency. The constants are obtained from the actual principal symbol. -/
theorem polynomialSymbol_elliptic_lower_bound {𝕜 : Type} [RCLike 𝕜] {d m : ℕ}
    (c : Coefficients 𝕜 d) (hc : IsElliptic c m) (hm : 0 < m) :
    ∃ a R : ℝ, 0 < a ∧ 1 ≤ R ∧ ∀ ξ : Euclidean d, R ≤ ‖ξ‖ →
      a * ‖ξ‖ ^ m ≤ ‖polynomialSymbol c ξ‖ := by
  obtain ⟨a, ha, hprincipal⟩ := principalSymbol_lower_bound c m hc.2
  let B : ℝ := ∑ α ∈ c.support, ‖c α‖
  refine ⟨a / 2, max 1 (2 * B / a), by positivity, le_max_left _ _, ?_⟩
  intro ξ hξ
  have hξ1 : 1 ≤ ‖ξ‖ := (le_max_left _ _).trans hξ
  have hξ0 : 0 < ‖ξ‖ := lt_of_lt_of_le zero_lt_one hξ1
  have hB : 2 * B ≤ a * ‖ξ‖ := by
    have h := (le_max_right 1 (2 * B / a)).trans hξ
    exact (div_le_iff₀ ha).mp h |>.trans_eq (mul_comm _ _)
  have hpow : ‖ξ‖ ^ m = ‖ξ‖ * ‖ξ‖ ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    ring
  have hmain := hprincipal ξ (norm_ne_zero_iff.mp hξ0.ne')
  have hrest := polynomialSymbol_remainder_bound c hc.1 ξ hξ1
  have htri : ‖principalSymbol c m ξ‖ ≤
      ‖polynomialSymbol c ξ‖ + ‖polynomialSymbol c ξ - principalSymbol c m ξ‖ :=
    norm_le_insert _ _
  have habsorb : B * ‖ξ‖ ^ (m - 1) ≤ (a / 2) * ‖ξ‖ ^ m := by
    rw [hpow]
    nlinarith [mul_le_mul_of_nonneg_right hB (pow_nonneg (norm_nonneg ξ) (m - 1))]
  change _ ≤ B * ‖ξ‖ ^ (m - 1) at hrest
  nlinarith

/-- Absorb a common factor per derivative into the finite coefficients. -/
def twistCoefficients {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (z : 𝕜) : Coefficients 𝕜 d :=
  Finsupp.onFinset c.support (fun α => c α * z ^ degree α) (by
    intro α hα
    exact Finsupp.mem_support_iff.mpr (fun h => hα (by simp [h])))

@[simp] lemma twistCoefficients_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (z : 𝕜) (α : Fin d → ℕ) :
    twistCoefficients c z α = c α * z ^ degree α := rfl

lemma twistCoefficients_support {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (z : 𝕜) (hz : z ≠ 0) :
    (twistCoefficients c z).support = c.support := by
  classical
  ext α
  simp [Finsupp.mem_support_iff, hz]

lemma principalSymbol_twist {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (m : ℕ) (z : 𝕜) (hz : z ≠ 0) (ξ : Euclidean d) :
    principalSymbol (twistCoefficients c z) m ξ = z ^ m * principalSymbol c m ξ := by
  classical
  simp only [principalSymbol, twistCoefficients_support c z hz,
    twistCoefficients_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [(Finset.mem_filter.mp hα).2]
  ring

lemma isElliptic_twist {𝕜 : Type} [RCLike 𝕜] {d m : ℕ}
    (c : Coefficients 𝕜 d) (hc : IsElliptic c m) (z : 𝕜) (hz : z ≠ 0) :
    IsElliptic (twistCoefficients c z) m := by
  refine ⟨?_, ?_⟩
  · simpa only [HasOrder, twistCoefficients_support c z hz] using hc.1
  · intro ξ hξ
    rw [principalSymbol_twist c m z hz]
    exact mul_ne_zero (pow_ne_zero _ hz) (hc.2 ξ hξ)

lemma polynomialSymbol_twist {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (z : 𝕜) (hz : z ≠ 0) (ξ : Euclidean d) :
    polynomialSymbol (twistCoefficients c z) ξ =
      ∑ α ∈ c.support, c α * ∏ i, (z * (ξ i : 𝕜)) ^ α i := by
  classical
  simp only [polynomialSymbol, twistCoefficients_support c z hz,
    twistCoefficients_apply, coordinateMonomial, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, degree]
  apply Finset.sum_congr rfl
  intro α hα
  ring

lemma fourierSymbol_eq_polynomialSymbol {d : ℕ} (c : Coefficients ℂ d) :
    fourierSymbol c = polynomialSymbol (twistCoefficients c (2 * Real.pi * Complex.I)) := by
  funext ξ
  symm
  exact polynomialSymbol_twist c _ (by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) ξ

/-- Principal-symbol ellipticity supplies the large-frequency bound for the
actual Fourier symbol of the differential operator; no such bound is assumed. -/
theorem fourierSymbol_elliptic_lower_bound {d m : ℕ}
    (c : Coefficients ℂ d) (hc : IsElliptic c m) :
    ∃ a R : ℝ, 0 < a ∧ 1 ≤ R ∧ ∀ ξ : Euclidean d, R ≤ ‖ξ‖ →
      a * ‖ξ‖ ^ m ≤ ‖fourierSymbol c ξ‖ := by
  by_cases hm : m = 0
  · subst m
    obtain ⟨a, ha, rfl⟩ := (hasOrder_zero_iff c).mp hc.1
    refine ⟨‖a‖, 1, norm_pos_iff.mpr ha, le_rfl, ?_⟩
    intro ξ hξ
    classical
    simp [fourierSymbol, Finsupp.support_single _ ha]
  · rw [fourierSymbol_eq_polynomialSymbol]
    exact polynomialSymbol_elliptic_lower_bound _
      (isElliptic_twist c hc _ (by
        exact mul_ne_zero
          (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero)) (Nat.pos_of_ne_zero hm)

lemma fourierSymbol_nonzero_at_infinity {d m : ℕ}
    (c : Coefficients ℂ d) (hc : IsElliptic c m) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ ξ : Euclidean d, R ≤ ‖ξ‖ → fourierSymbol c ξ ≠ 0 := by
  obtain ⟨a, R, ha, hR, hbound⟩ := fourierSymbol_elliptic_lower_bound c hc
  refine ⟨R, hR, ?_⟩
  intro ξ hξ
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos ha (pow_pos (lt_of_lt_of_le zero_lt_one (hR.trans hξ)) _))
    (hbound ξ hξ)

/-- A uniformly positive real temperate function has a temperate reciprocal.
The constants may depend on the derivative order, as required by the native
notion of temperate growth. -/
lemma hasTemperateGrowth_inv_of_lower_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : f.HasTemperateGrowth) {δ : ℝ} (hδ : 0 < δ) (h : ∀ x, δ ≤ f x) :
    (fun x => (f x)⁻¹).HasTemperateGrowth := by
  let t : Set ℝ := Ioi (δ / 2)
  have ht : range f ⊆ t := by
    rintro _ ⟨x, rfl⟩
    exact lt_of_lt_of_le (half_lt_self hδ) (h x)
  have hu : UniqueDiffOn ℝ t := isOpen_Ioi.uniqueDiffOn
  have hd : ContDiffOn ℝ ∞ (fun x : ℝ => x ^ (-1 : ℝ)) t :=
    contDiffOn_fun_id.rpow_const_of_ne (by
      intro x hx
      have : 0 < x := lt_trans (half_pos hδ) hx
      exact this.ne')
  have hg : (fun x => (f x) ^ (-1 : ℝ)).HasTemperateGrowth := by
    apply hf.comp' ht hu hd
    intro N
    let b : ℕ → ℝ := fun n =>
      ‖Polynomial.eval (-1 : ℝ) (descPochhammer ℝ n)‖ * (δ / 2) ^ (-1 - (n : ℝ))
    refine ⟨0, ∑ n ∈ Finset.range (N + 1), b n, by
      apply Finset.sum_nonneg
      intro n hn
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (half_pos hδ).le _), ?_⟩
    intro n hn x hx
    have hx0 : 0 < x := lt_trans (half_pos hδ) hx
    have hdiff : ContDiffAt ℝ n (fun x : ℝ => x ^ (-1 : ℝ)) x :=
      Real.contDiffAt_rpow_const (Or.inl hx0.ne')
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_eq_iteratedDeriv hu hdiff hx,
      iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, norm_mul]
    have hterm : ‖Polynomial.eval (-1 : ℝ) (descPochhammer ℝ n)‖ *
        ‖x ^ (-1 - (n : ℝ))‖ ≤ b n := by
      dsimp only [b]
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact Real.rpow_le_rpow_of_nonpos (half_pos hδ) hx.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    simpa only [pow_zero, mul_one] using hterm.trans
      (Finset.single_le_sum (s := Finset.range (N + 1)) (f := b) (fun i hi =>
        mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (half_pos hδ).le _))
        (Finset.mem_range.mpr (by omega)))
  simpa only [Real.rpow_neg_one] using hg

/-- A genuine smooth temperate reciprocal modulo a compact smooth error,
constructed from ellipticity rather than taken as an additional hypothesis.
This assertion alone makes no off-origin regularity claim about its kernel. -/
theorem exists_reciprocal_symbol {d m : ℕ} (c : Coefficients ℂ d)
    (hc : IsElliptic c m) :
    ∃ (q : Euclidean d → ℂ) (χ : Schwartz ℂ d),
      q.HasTemperateGrowth ∧ HasCompactSupport χ ∧
      ∀ ξ, fourierSymbol c ξ * q ξ = 1 - χ ξ := by
  obtain ⟨a, R, ha, hR, hbound⟩ := fourierSymbol_elliptic_lower_bound c hc
  let b : ContDiffBump (0 : Euclidean d) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := lt_of_lt_of_le zero_lt_one hR
      rIn_lt_rOut := by linarith }
  let p := fourierSymbol c
  let h : Euclidean d → ℝ := fun ξ => Complex.normSq (p ξ) + b ξ
  have hp : p.HasTemperateGrowth := fourierSymbol_hasTemperateGrowth c
  have hb : Function.HasTemperateGrowth (fun ξ => b ξ) :=
    b.hasCompactSupport.hasTemperateGrowth b.contDiff
  have hh : h.HasTemperateGrowth := by
    have hnorm : (fun ξ => Complex.normSq (p ξ)).HasTemperateGrowth := by
      simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
        ((Function.hasTemperateGrowth_norm_sq ℂ).comp hp)
    exact hnorm.add hb
  have hδ : 0 < min 1 (a ^ 2) := lt_min zero_lt_one (sq_pos_of_pos ha)
  have hlower : ∀ ξ, min 1 (a ^ 2) ≤ h ξ := by
    intro ξ
    by_cases hξ : ‖ξ‖ ≤ R
    · have hb1 : b ξ = 1 := b.one_of_mem_closedBall (by simpa [b] using hξ)
      exact (min_le_left _ _).trans (by
        dsimp only [h]
        rw [hb1]
        exact le_add_of_nonneg_left (Complex.normSq_nonneg _))
    · have hRξ : R ≤ ‖ξ‖ := le_of_lt (lt_of_not_ge hξ)
      have hpbound : a ≤ ‖p ξ‖ := by
        calc
          a ≤ a * ‖ξ‖ ^ m := le_mul_of_one_le_right ha.le
            (one_le_pow₀ (hR.trans hRξ))
          _ ≤ _ := hbound ξ hRξ
      exact (min_le_right _ _).trans (by
        dsimp only [h]
        rw [Complex.normSq_eq_norm_sq]
        exact (pow_le_pow_left₀ ha.le hpbound 2).trans (le_add_of_nonneg_right b.nonneg))
  have hinv : (fun ξ => (h ξ)⁻¹).HasTemperateGrowth :=
    hasTemperateGrowth_inv_of_lower_bound hh hδ hlower
  let q : Euclidean d → ℂ := fun ξ => conj (p ξ) * ((h ξ)⁻¹ : ℝ)
  have hq : q.HasTemperateGrowth :=
    (Complex.conjCLE.hasTemperateGrowth.comp hp).mul
      (Complex.hasTemperateGrowth_ofReal.comp hinv)
  let χf : Euclidean d → ℂ := fun ξ => ((b ξ * (h ξ)⁻¹ : ℝ) : ℂ)
  have hχ : HasCompactSupport χf :=
    (b.hasCompactSupport.mul_right (f' := fun ξ => (h ξ)⁻¹)).comp_left
      (show (Complex.ofReal 0) = 0 by simp)
  have hχsmooth : ContDiff ℝ ∞ χf :=
    (Complex.hasTemperateGrowth_ofReal.comp (hb.mul hinv)).1
  let χ : Schwartz ℂ d := hχ.toSchwartzMap hχsmooth
  refine ⟨q, χ, hq, hχ, ?_⟩
  intro ξ
  have hh0 : h ξ ≠ 0 := ne_of_gt (hδ.trans_le (hlower ξ))
  have heq : Complex.normSq (p ξ) * (h ξ)⁻¹ = 1 - b ξ * (h ξ)⁻¹ := by
    have hinv_cancel : h ξ * (h ξ)⁻¹ = 1 := mul_inv_cancel₀ hh0
    dsimp only [h] at hinv_cancel ⊢
    nlinarith [hinv_cancel]
  change p ξ * (conj (p ξ) * (((h ξ)⁻¹ : ℝ) : ℂ)) = 1 - χf ξ
  rw [← mul_assoc, Complex.mul_conj]
  simpa only [χf, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul] using
    congrArg Complex.ofReal heq

/-- The global tempered equation with Schwartz remainder is already available.
The full global theorem additionally requires smoothness on the punctured space. -/
theorem exists_tempered_parametrix_equation {d m : ℕ} (c : Coefficients ℂ d)
    (hc : IsElliptic c m) :
    ∃ (Q : Tempered ℂ d) (r : Schwartz ℂ d),
      applyOperator c Q = Examples.delta ℂ d + regularSchwartz r := by
  obtain ⟨q, χ, hq, _, heq⟩ := exists_reciprocal_symbol c hc
  exact ⟨inverseSymbol q, -(𝓕⁻ χ), inverse_symbol_equation c q hq χ heq⟩


lemma reciprocalSymbol_eq_inv_outside {d : ℕ} (p q : Euclidean d → ℂ)
    (χ : Schwartz ℂ d) (hχ : HasCompactSupport χ)
    (heq : ∀ ξ, p ξ * q ξ = 1 - χ ξ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ ξ : Euclidean d, R ≤ ‖ξ‖ → q ξ = (p ξ)⁻¹ := by
  obtain ⟨B, hB⟩ := hχ.isCompact.isBounded.subset_closedBall (0 : Euclidean d)
  refine ⟨max 1 (B + 1), le_max_left _ _, ?_⟩
  intro ξ hξ
  have hχzero : χ ξ = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hnorm : ‖ξ‖ ≤ B := by simpa only [Metric.mem_closedBall, dist_zero_right] using hB h
    have hBR : B + 1 ≤ ‖ξ‖ := (le_max_right _ _).trans hξ
    linarith
  apply eq_inv_of_mul_eq_one_right
  simpa only [hχzero, sub_zero] using heq ξ

lemma reciprocalSymbol_weighted_bound {d m : ℕ} (p q : Euclidean d → ℂ)
    (hq : Continuous q) {a R : ℝ} (ha : 0 < a) (hR : 1 ≤ R)
    (hp : ∀ ξ : Euclidean d, R ≤ ‖ξ‖ → a * ‖ξ‖ ^ m ≤ ‖p ξ‖)
    (hqi : ∀ ξ : Euclidean d, R ≤ ‖ξ‖ → q ξ = (p ξ)⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Euclidean d, (1 + ‖ξ‖) ^ m * ‖q ξ‖ ≤ C := by
  have hcont : Continuous (fun ξ : Euclidean d => (1 + ‖ξ‖) ^ m * ‖q ξ‖) := by fun_prop
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Euclidean d) R).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max (max B 0) ((2 : ℝ) ^ m / a), le_trans (le_max_right B 0) (le_max_left _ _), ?_⟩
  intro ξ
  by_cases hξ : ‖ξ‖ ≤ R
  · exact (le_abs_self _).trans ((hB ξ (by simpa using hξ)).trans
      ((le_max_left B 0).trans (le_max_left _ _)))
  · have hRξ : R ≤ ‖ξ‖ := (lt_of_not_ge hξ).le
    have hn1 : 1 ≤ ‖ξ‖ := hR.trans hRξ
    have hn : 0 < ‖ξ‖ := lt_of_lt_of_le zero_lt_one hn1
    have hap : 0 < a * ‖ξ‖ ^ m := mul_pos ha (pow_pos hn _)
    have hp0 : p ξ ≠ 0 := norm_pos_iff.mp (hap.trans_le (hp ξ hRξ))
    have hqnorm : ‖q ξ‖ ≤ (a * ‖ξ‖ ^ m)⁻¹ := by
      rw [hqi ξ hRξ, norm_inv]
      exact inv_anti₀ hap (hp ξ hRξ)
    have hpow : (1 + ‖ξ‖) ^ m ≤ 2 ^ m * ‖ξ‖ ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hbound : (1 + ‖ξ‖) ^ m * ‖q ξ‖ ≤ (2 : ℝ) ^ m / a := by
      calc
        _ ≤ (2 ^ m * ‖ξ‖ ^ m) * (a * ‖ξ‖ ^ m)⁻¹ :=
          mul_le_mul hpow hqnorm (norm_nonneg _) (by positivity)
        _ = _ := by field_simp
    exact hbound.trans (le_max_right _ _)

lemma reciprocalSymbol_bessel_weighted_bound {d m : ℕ} (q : Euclidean d → ℂ)
    {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ ξ : Euclidean d, (1 + ‖ξ‖) ^ m * ‖q ξ‖ ≤ C) :
    ∀ ξ : Euclidean d,
      ‖FourierScale.complexWeight (m : ℝ) ξ * q ξ‖ ≤
        (1 + 2 * Real.pi) ^ m * C := by
  intro ξ
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hn : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hfreq : FourierScale.frequencyWeight ξ ≤
      ((1 + 2 * Real.pi) * (1 + ‖ξ‖)) ^ 2 := by
    unfold FourierScale.frequencyWeight
    nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖), mul_nonneg hπ hn]
  have hweight : FourierScale.weight (m : ℝ) ξ ≤
      (1 + 2 * Real.pi) ^ m * (1 + ‖ξ‖) ^ m := by
    apply (sq_le_sq₀ (FourierScale.weight_pos _ _).le (by positivity)).mp
    rw [FourierScale.weight_sq, Real.rpow_natCast, ← mul_pow, ← pow_mul, mul_comm m 2, pow_mul]
    exact pow_le_pow_left₀ (FourierScale.frequencyWeight_pos ξ).le hfreq m
  rw [norm_mul]
  change ‖(FourierScale.weight (m : ℝ) ξ : ℂ)‖ * ‖q ξ‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (FourierScale.weight_pos _ _)]
  calc
    _ ≤ ((1 + 2 * Real.pi) ^ m * (1 + ‖ξ‖) ^ m) * ‖q ξ‖ :=
      mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ m * ((1 + ‖ξ‖) ^ m * ‖q ξ‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb ξ) (by positivity)

theorem exists_reciprocal_symbol_decay {d m : ℕ} (c : Coefficients ℂ d)
    (hc : IsElliptic c m) :
    ∃ (q : Euclidean d → ℂ) (χ : Schwartz ℂ d) (C R : ℝ),
      q.HasTemperateGrowth ∧ HasCompactSupport χ ∧ 0 ≤ C ∧ 1 ≤ R ∧
      (∀ ξ, fourierSymbol c ξ * q ξ = 1 - χ ξ) ∧
      (∀ ξ : Euclidean d, R ≤ ‖ξ‖ → q ξ = (fourierSymbol c ξ)⁻¹) ∧
      (∀ ξ : Euclidean d, (1 + ‖ξ‖) ^ m * ‖q ξ‖ ≤ C) ∧
      (∀ ξ : Euclidean d,
        ‖FourierScale.complexWeight (m : ℝ) ξ * q ξ‖ ≤
          (1 + 2 * Real.pi) ^ m * C) := by
  obtain ⟨q, χ, hq, hχ, heq⟩ := exists_reciprocal_symbol c hc
  obtain ⟨a, R, ha, hR, hp⟩ := fourierSymbol_elliptic_lower_bound c hc
  obtain ⟨S, hS, hi⟩ := reciprocalSymbol_eq_inv_outside (fourierSymbol c) q χ hχ heq
  have hp' : ∀ ξ : Euclidean d, max R S ≤ ‖ξ‖ →
      a * ‖ξ‖ ^ m ≤ ‖fourierSymbol c ξ‖ := by
    intro ξ hξ
    exact hp ξ ((le_max_left _ _).trans hξ)
  have hi' : ∀ ξ : Euclidean d, max R S ≤ ‖ξ‖ →
      q ξ = (fourierSymbol c ξ)⁻¹ := by
    intro ξ hξ
    exact hi ξ ((le_max_right _ _).trans hξ)
  obtain ⟨C, hC, hb⟩ := reciprocalSymbol_weighted_bound (fourierSymbol c) q
    hq.1.continuous ha (hR.trans (le_max_left _ _)) hp' hi'
  exact ⟨q, χ, C, max R S, hq, hχ, hC, hR.trans (le_max_left _ _), heq, hi', hb,
    reciprocalSymbol_bessel_weighted_bound q hC hb⟩


def cutoffProduct {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (χ : Schwartz 𝕜 d) (T : Tempered 𝕜 d) : Tempered 𝕜 d :=
  T.comp (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) χ)

@[simp] lemma cutoffProduct_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (χ φ : Schwartz 𝕜 d) (T : Tempered 𝕜 d) :
    cutoffProduct χ T φ = T (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) χ φ) := rfl

lemma cutoffProduct_dsupport_subset {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (χ : Schwartz 𝕜 d) (T : Tempered 𝕜 d) :
    Distribution.dsupport (fun φ : Schwartz 𝕜 d => cutoffProduct χ T φ) ⊆ tsupport χ := by
  intro x hx
  apply (Distribution.mem_dsupport_iff x).mp hx (tsupport χ) ?_ isClosed_closure
  intro φ hφ
  have hz : SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) χ φ = 0 := by
    ext y
    by_cases hy : y ∈ tsupport χ
    · have hyφ : y ∉ tsupport φ := by
        intro hm
        exact hφ hm hy
      simp [image_eq_zero_of_notMem_tsupport hyφ]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  simp [hz]

lemma smoothOn_cutoffProduct {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {T : Tempered 𝕜 d} {U : Set (Euclidean d)}
    (hT : SmoothOn T U) (χ : Schwartz 𝕜 d) :
    SmoothOn (cutoffProduct χ T) U := by
  obtain ⟨f, hf, hpair⟩ := hT
  refine ⟨fun x => χ x * f x, χ.smooth'.contDiffOn.mul hf, ?_⟩
  intro φ hφ hU
  let ψ := SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) χ φ
  have hψ : HasCompactSupport ψ := by
    exact hφ.of_isClosed_subset isClosed_closure tsupport_mul_subset_right
  have hψU : tsupport ψ ⊆ U := tsupport_mul_subset_right.trans hU
  obtain ⟨hi, he⟩ := hpair ψ hψ hψU
  have hh : (fun x => f x * ψ x) = fun x => (χ x * f x) * φ x := by
    funext x
    simp [ψ, mul_assoc, mul_left_comm]
  rw [hh] at hi he
  exact ⟨hi, he⟩

lemma exists_schwartz_cutoff {𝕜 : Type} [RCLike 𝕜] (d : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ χ : Schwartz 𝕜 d, HasCompactSupport χ ∧ tsupport χ ⊆ Metric.ball 0 R ∧
      ∀ᶠ x in nhds (0 : Euclidean d), χ x = 1 := by
  let f : ContDiffBump (0 : Euclidean d) :=
    { rIn := R / 4
      rOut := R / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hfc := f.hasCompactSupport
  let χ : Schwartz 𝕜 d := (hfc.comp_left (by simp : (RCLike.ofReal : ℝ → 𝕜) 0 = 0)).toSchwartzMap
      ((RCLike.ofRealCLM (K := 𝕜)).contDiff.comp f.contDiff)
  refine ⟨χ, ?_, ?_, ?_⟩
  · exact hfc.comp_left (by simp)
  · apply (tsupport_comp_subset (by simp : (RCLike.ofReal : ℝ → 𝕜) 0 = 0) f).trans
    rw [f.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [f]; linarith)
  · filter_upwards [f.eventuallyEq_one] with x hx
    change (f x : 𝕜) = 1
    simp [hx]


lemma cutoffProduct_regular_of_tsupport_subset {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {T : Tempered 𝕜 d} {U : Set (Euclidean d)} (hU : IsOpen U)
    (hT : SmoothOn T U) (a : Schwartz 𝕜 d) (hac : HasCompactSupport a)
    (haU : tsupport a ⊆ U) :
    ∃ g : Schwartz 𝕜 d, cutoffProduct a T = regularSchwartz g := by
  obtain ⟨f, hf, hp⟩ := hT
  have hgf : ContDiff ℝ ∞ (fun x => a x * f x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport a
    · exact a.smooth'.contDiffAt.mul ((hf x (haU hx)).contDiffAt (hU.mem_nhds (haU hx)))
    · apply (contDiffAt_const (c := (0 : 𝕜))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  have hgc : HasCompactSupport (fun x => a x * f x) :=
    hac.of_isClosed_subset isClosed_closure tsupport_mul_subset_left
  refine ⟨hgc.toSchwartzMap hgf, ?_⟩
  ext φ
  let ψ := SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) a φ
  obtain ⟨hi, he⟩ := hp ψ
    (hac.of_isClosed_subset isClosed_closure tsupport_mul_subset_left)
    (tsupport_mul_subset_left.trans haU)
  change T ψ = ∫ x, (a x * f x) * φ x
  rw [he]
  congr 1
  funext x
  simp [ψ, mul_assoc, mul_left_comm]

lemma regularSchwartz_partial {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Schwartz 𝕜 d) (i : Fin d) :
    wordPartial [i] (regularSchwartz a) =
      regularSchwartz (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) a) := by
  ext φ
  change -(∫ x, a x * (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) φ) x) =
    ∫ x, (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) a) x * φ x
  have h := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) a φ (basisVector i)
  exact (congrArg Neg.neg h).trans (neg_neg _)

lemma cutoffProduct_partial {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Schwartz 𝕜 d) (T : Tempered 𝕜 d) (i : Fin d) :
    wordPartial [i] (cutoffProduct a T) =
      cutoffProduct a (wordPartial [i] T) +
      cutoffProduct (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) a) T := by
  ext φ
  let D := LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i)
  have hprod : D (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) a φ) =
      SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) (D a) φ +
      SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) a (D φ) := by
    ext x
    change fderiv ℝ (fun y => a y * φ y) x (basisVector i) = _
    change fderiv ℝ ((a : Euclidean d → 𝕜) * (φ : Euclidean d → 𝕜)) x (basisVector i) = _
    rw [fderiv_mul a.differentiableAt φ.differentiableAt]
    simp [D, SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm]
    ring
  change -T (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) a (D φ)) =
    -T (D (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) a φ)) +
    T (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) (D a) φ)
  rw [hprod, map_add]
  abel


lemma regularSchwartz_add {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f g : Schwartz 𝕜 d) :
    regularSchwartz (f + g) = regularSchwartz f + regularSchwartz g := by
  ext φ
  simp [regularSchwartz, map_add]

lemma regularSchwartz_sub {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f g : Schwartz 𝕜 d) :
    regularSchwartz (f - g) = regularSchwartz f - regularSchwartz g := by
  ext φ
  simp [regularSchwartz, map_sub]

lemma wordPartial_append {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (w v : List (Fin d)) (T : Tempered 𝕜 d) :
    wordPartial (w ++ v) T = wordPartial v (wordPartial w T) := by
  induction w generalizing T with
  | nil => rfl
  | cons i w ih => exact ih _

lemma localized_wordPartial_regular {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {T : Tempered 𝕜 d} {U : Set (Euclidean d)} (hU : IsOpen U)
    (hT : SmoothOn T U) (w : List (Fin d))
    (a : Schwartz 𝕜 d) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) :
    ∃ g : Schwartz 𝕜 d, cutoffProduct a (wordPartial w T) = regularSchwartz g := by
  induction w using List.reverseRecOn generalizing a with
  | nil => exact cutoffProduct_regular_of_tsupport_subset hU hT a hac haU
  | @append_singleton w i ih =>
    let D := LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i)
    have hs : tsupport (D a) ⊆ tsupport a := tsupport_fderiv_apply_subset ℝ (basisVector i)
    obtain ⟨g, hg⟩ := ih a hac haU
    obtain ⟨g', hg'⟩ := ih (D a) (hac.of_isClosed_subset isClosed_closure hs) (hs.trans haU)
    refine ⟨D g - g', ?_⟩
    rw [wordPartial_append, regularSchwartz_sub, ← regularSchwartz_partial, ← hg, ← hg']
    exact (eq_sub_iff_add_eq.mpr (cutoffProduct_partial a (wordPartial w T) i).symm)


lemma wordPartial_singleton_add {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) (S T : Tempered 𝕜 d) :
    wordPartial [i] (S + T) = wordPartial [i] S + wordPartial [i] T := by
  ext φ
  simp [wordPartial]
  abel

lemma cutoffProduct_partial_tsupport {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Schwartz 𝕜 d) (ha : ∀ᶠ x in nhds (0 : Euclidean d), a x = 1)
    (i : Fin d) :
    tsupport (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) a) ⊆
      ({0}ᶜ : Set (Euclidean d)) := by
  have he : (a : Euclidean d → 𝕜) =ᶠ[nhds 0] (fun _ => (1 : 𝕜)) := ha
  have hz : (fun x => (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) a) x)
      =ᶠ[nhds 0] (0 : Euclidean d → 𝕜) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with x hx
    change fderiv ℝ a x (basisVector i) = 0
    rw [hx]
    simp
  have h0 := notMem_tsupport_iff_eventuallyEq.mpr hz
  intro x hx hxx
  simp only [mem_singleton_iff] at hxx
  subst x
  exact h0 hx

lemma cutoffProduct_wordPartial_error {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {T : Tempered 𝕜 d} (hT : SmoothOn T ({0}ᶜ : Set (Euclidean d)))
    (a : Schwartz 𝕜 d) (hac : HasCompactSupport a)
    (ha : ∀ᶠ x in nhds (0 : Euclidean d), a x = 1) (w : List (Fin d)) :
    ∃ g : Schwartz 𝕜 d,
      wordPartial w (cutoffProduct a T) = cutoffProduct a (wordPartial w T) +
        regularSchwartz g := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨0, ?_⟩
    have hz : regularSchwartz (0 : Schwartz 𝕜 d) = 0 := by
      ext φ
      simp [regularSchwartz]
    simp [wordPartial, hz]
  | @append_singleton w i ih =>
    let D := LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i)
    have hs : tsupport (D a) ⊆ tsupport a := tsupport_fderiv_apply_subset ℝ (basisVector i)
    obtain ⟨g, hg⟩ := ih
    obtain ⟨g', hg'⟩ := localized_wordPartial_regular isClosed_singleton.isOpen_compl hT w
      (D a) (hac.of_isClosed_subset isClosed_closure hs)
      (cutoffProduct_partial_tsupport a ha i)
    refine ⟨g' + D g, ?_⟩
    dsimp only [D] at hg' ⊢
    simp only [wordPartial_append, hg, wordPartial_singleton_add,
      cutoffProduct_partial, hg', regularSchwartz_partial, regularSchwartz_add]
    abel


lemma regularSchwartz_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (b : 𝕜) (f : Schwartz 𝕜 d) :
    regularSchwartz (b • f) = b • regularSchwartz f := by
  ext φ
  simp [regularSchwartz]

lemma regularSchwartz_sum {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {ι : Type*}
    (s : Finset ι) (g : ι → Schwartz 𝕜 d) :
    regularSchwartz (∑ j ∈ s, g j) = ∑ j ∈ s, regularSchwartz (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, regularSchwartz_add, ih]

lemma cutoffProduct_add {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Schwartz 𝕜 d) (S T : Tempered 𝕜 d) :
    cutoffProduct a (S + T) = cutoffProduct a S + cutoffProduct a T := by
  ext φ
  rfl

lemma cutoffProduct_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Schwartz 𝕜 d) (b : 𝕜) (T : Tempered 𝕜 d) :
    cutoffProduct a (b • T) = b • cutoffProduct a T := by
  ext φ
  rfl

lemma cutoffProduct_sum {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {ι : Type*}
    (a : Schwartz 𝕜 d) (s : Finset ι) (g : ι → Tempered 𝕜 d) :
    cutoffProduct a (∑ j ∈ s, g j) = ∑ j ∈ s, cutoffProduct a (g j) := by
  ext φ
  simp [cutoffProduct]

lemma cutoffProduct_operator_error {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {T : Tempered 𝕜 d} (hT : SmoothOn T ({0}ᶜ : Set (Euclidean d)))
    (a : Schwartz 𝕜 d) (hac : HasCompactSupport a)
    (ha : ∀ᶠ x in nhds (0 : Euclidean d), a x = 1) (c : Coefficients 𝕜 d) :
    ∃ g : Schwartz 𝕜 d,
      applyOperator c (cutoffProduct a T) = cutoffProduct a (applyOperator c T) +
        regularSchwartz g := by
  classical
  choose g hg using fun α : Fin d → ℕ =>
    cutoffProduct_wordPartial_error hT a hac ha (multiIndexWord α)
  refine ⟨∑ α ∈ c.support, c α • g α, ?_⟩
  simp only [applyOperator, cutoffProduct_sum, regularSchwartz_sum,
    cutoffProduct_smul, regularSchwartz_smul]
  simp_rw [hg, smul_add]
  rw [Finset.sum_add_distrib]

lemma cutoffProduct_delta {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Schwartz 𝕜 d) (ha : a 0 = 1) :
    cutoffProduct a (Examples.delta 𝕜 d) = Examples.delta 𝕜 d := by
  ext φ
  simp [cutoffProduct, Examples.delta, ha]

lemma cutoffProduct_regularSchwartz {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a r : Schwartz 𝕜 d) :
    cutoffProduct a (regularSchwartz r) =
      regularSchwartz (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) a r) := by
  ext φ
  change (∫ x, r x * (a x * φ x)) = ∫ x, (a x * r x) * φ x
  congr 1
  funext x
  ring

/-- A global tempered parametrix can be localized inside every positive ball,
with a Schwartz remainder, using only its off-zero smoothness. -/
theorem compact_parametrix_of_global {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) {Q : Tempered 𝕜 d} {r : Schwartz 𝕜 d}
    (hQ : SmoothOn Q ({0}ᶜ : Set (Euclidean d)))
    (he : applyOperator c Q = Examples.delta 𝕜 d + regularSchwartz r)
    (R : ℝ) (hR : 0 < R) :
    ∃ (Qc : Tempered 𝕜 d) (rc : Schwartz 𝕜 d),
      Distribution.dsupport (fun φ : Schwartz 𝕜 d => Qc φ) ⊆ Metric.ball 0 R ∧
      SmoothOn Qc ({0}ᶜ : Set (Euclidean d)) ∧
      applyOperator c Qc = Examples.delta 𝕜 d + regularSchwartz rc := by
  obtain ⟨a, hac, haR, ha⟩ := exists_schwartz_cutoff (𝕜 := 𝕜) d R hR
  obtain ⟨g, hg⟩ := cutoffProduct_operator_error hQ a hac ha c
  refine ⟨cutoffProduct a Q,
    SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) a r + g,
    (cutoffProduct_dsupport_subset a Q).trans haR, smoothOn_cutoffProduct hQ a, ?_⟩
  rw [hg, he, cutoffProduct_add, cutoffProduct_delta a ha.self_of_nhds,
    cutoffProduct_regularSchwartz, regularSchwartz_add]
  exact add_assoc _ _ _



section ScalarDescent
variable {𝕜 : Type} [RCLike 𝕜]
lemma toComplex_mul (a b : 𝕜) :
    RCLike.map 𝕜 ℂ (a * b) = RCLike.map 𝕜 ℂ a * RCLike.map 𝕜 ℂ b := by
  apply Complex.ext <;> simp [RCLike.map_apply, RCLike.mul_re, RCLike.mul_im,
    RCLike.I_to_complex]
lemma fromComplex_toComplex_mul (a : 𝕜) (z : ℂ) :
    RCLike.map ℂ 𝕜 (RCLike.map 𝕜 ℂ a * z) = a * RCLike.map ℂ 𝕜 z := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · simp only [RCLike.map_apply, h, mul_zero, add_zero, RCLike.im_eq_zero h]
    have hae : (RCLike.re a : 𝕜) = a := by simpa [h] using (RCLike.re_add_im a)
    simp [hae]
  · have ha : (RCLike.complexRingEquiv h) a = RCLike.map 𝕜 ℂ a := rfl
    have hz : (RCLike.complexRingEquiv h).symm z = RCLike.map ℂ 𝕜 z := rfl
    change (RCLike.complexRingEquiv h).symm ((RCLike.complexRingEquiv h) a * z) =
      a * (RCLike.complexRingEquiv h).symm z
    rw [map_mul, RingEquiv.symm_apply_apply]


def toComplexRingHom (𝕜 : Type) [RCLike 𝕜] : 𝕜 →+* ℂ where
  toFun := RCLike.map 𝕜 ℂ
  map_zero' := by simp
  map_one' := by simp [RCLike.map_apply]
  map_add' := map_add _
  map_mul' := toComplex_mul

lemma toComplexRingHom_injective : Function.Injective (toComplexRingHom 𝕜) := by
  apply (toComplexRingHom 𝕜).injective

@[simp] lemma toComplexRingHom_ofReal (a : ℝ) :
    toComplexRingHom 𝕜 (a : 𝕜) = (a : ℂ) := by simp [toComplexRingHom, RCLike.map_apply]

def scalarComplexCoefficients {d : ℕ} (c : Coefficients 𝕜 d) : Coefficients ℂ d :=
  c.mapRange (toComplexRingHom 𝕜) (map_zero _)

@[simp] lemma scalarComplexCoefficients_apply {d : ℕ} (c : Coefficients 𝕜 d)
    (α : Fin d → ℕ) : scalarComplexCoefficients c α = toComplexRingHom 𝕜 (c α) := rfl

@[simp] lemma scalarComplexCoefficients_support {d : ℕ} (c : Coefficients 𝕜 d) :
    (scalarComplexCoefficients c).support = c.support :=
  Finsupp.support_mapRange_of_injective (map_zero _) c toComplexRingHom_injective

lemma principalSymbol_scalarComplexCoefficients {d : ℕ} (c : Coefficients 𝕜 d)
    (m : ℕ) (ξ : Euclidean d) :
    principalSymbol (scalarComplexCoefficients c) m ξ = toComplexRingHom 𝕜 (principalSymbol c m ξ) := by
  classical
  simp [principalSymbol, map_sum, map_mul, map_prod, map_pow]

lemma isElliptic_scalarComplexCoefficients {d m : ℕ} (c : Coefficients 𝕜 d)
    (hc : IsElliptic c m) : IsElliptic (scalarComplexCoefficients c) m := by
  refine ⟨?_, ?_⟩
  · simpa only [HasOrder, scalarComplexCoefficients_support] using hc.1
  · intro ξ hξ
    rw [principalSymbol_scalarComplexCoefficients]
    exact (map_ne_zero_iff _ toComplexRingHom_injective).mpr (hc.2 ξ hξ)

def toComplexSchwartz {d : ℕ} : Schwartz 𝕜 d →L[ℝ] Schwartz ℂ d :=
  SchwartzMap.postcompCLM (RCLike.map 𝕜 ℂ)

def fromComplexSchwartz {d : ℕ} : Schwartz ℂ d →L[ℝ] Schwartz 𝕜 d :=
  SchwartzMap.postcompCLM (RCLike.map ℂ 𝕜)

lemma toComplexSchwartz_smul {d : ℕ} (a : 𝕜) (φ : Schwartz 𝕜 d) :
    toComplexSchwartz (a • φ) = toComplexRingHom 𝕜 a • toComplexSchwartz φ := by
  ext x
  exact toComplex_mul a (φ x)

def descendTempered {d : ℕ} (T : Tempered ℂ d) : Tempered 𝕜 d where
  toFun φ := RCLike.map ℂ 𝕜 (T (toComplexSchwartz φ))
  map_add' φ ψ := by simp [map_add]
  map_smul' a φ := by
    rw [toComplexSchwartz_smul, map_smul]
    exact fromComplex_toComplex_mul a (T (toComplexSchwartz φ))
  cont := (RCLike.map ℂ 𝕜).continuous.comp
    (T.continuous.comp toComplexSchwartz.continuous)

lemma toComplexSchwartz_lineDeriv {d : ℕ} (i : Fin d) (φ : Schwartz 𝕜 d) :
    toComplexSchwartz (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) φ) =
      LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) (toComplexSchwartz φ) := by
  ext x
  change RCLike.map 𝕜 ℂ (fderiv ℝ φ x (basisVector i)) =
    fderiv ℝ ((RCLike.map 𝕜 ℂ) ∘ φ) x (basisVector i)
  rw [((RCLike.map 𝕜 ℂ).hasFDerivAt.comp x φ.differentiableAt.hasFDerivAt).fderiv]
  rfl

lemma descendTempered_wordPartial {d : ℕ} (w : List (Fin d)) (T : Tempered ℂ d) :
    descendTempered (𝕜 := 𝕜) (wordPartial w T) = wordPartial w (descendTempered T) := by
  induction w generalizing T with
  | nil => rfl
  | cons i w ih =>
    rw [wordPartial, wordPartial, ih]
    congr 1
    ext φ
    change RCLike.map ℂ 𝕜 (-(T (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)
      (toComplexSchwartz φ)))) =
      -RCLike.map ℂ 𝕜 (T (toComplexSchwartz
        (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) φ)))
    rw [toComplexSchwartz_lineDeriv, map_neg]

lemma descendTempered_applyOperator {d : ℕ} (c : Coefficients 𝕜 d)
    (T : Tempered ℂ d) :
    descendTempered (applyOperator (scalarComplexCoefficients c) T) =
      applyOperator c (descendTempered T) := by
  classical
  ext φ
  change RCLike.map ℂ 𝕜 ((applyOperator (scalarComplexCoefficients c) T) (toComplexSchwartz φ)) = _
  simp only [applyOperator, sum_apply, smul_apply, smul_eq_mul,
    scalarComplexCoefficients_support, map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have h := congrArg (fun S : Tempered 𝕜 d => S φ)
    (descendTempered_wordPartial (𝕜 := 𝕜) (multiIndexWord α) T)
  change RCLike.map ℂ 𝕜 (wordPartial (multiIndexWord α) T (toComplexSchwartz φ)) = _ at h
  rw [scalarComplexCoefficients_apply]
  exact (fromComplex_toComplex_mul (c α) _).trans (congrArg (fun z => c α * z) h)

lemma descendTempered_regularSchwartz {d : ℕ} (r : Schwartz ℂ d) :
    descendTempered (regularSchwartz r) = regularSchwartz (fromComplexSchwartz (𝕜 := 𝕜) r) := by
  ext φ
  have hi : Integrable (fun x => r x * toComplexSchwartz φ x) := by
    exact (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) r (toComplexSchwartz φ)).integrable
      (μ := (volume : Measure (Euclidean d)))
  change RCLike.map ℂ 𝕜 (∫ x, r x * toComplexSchwartz φ x) =
    ∫ x, fromComplexSchwartz r x * φ x
  rw [← (RCLike.map ℂ 𝕜).integral_comp_comm hi]
  congr 1
  funext x
  change RCLike.map ℂ 𝕜 (r x * RCLike.map 𝕜 ℂ (φ x)) = _
  rw [mul_comm, fromComplex_toComplex_mul, mul_comm]
  rfl

lemma descendTempered_delta {d : ℕ} :
    descendTempered (Examples.delta ℂ d) = Examples.delta 𝕜 d := by
  ext φ
  change RCLike.map ℂ 𝕜 (RCLike.map 𝕜 ℂ (φ 0)) = φ 0
  simp [RCLike.map_apply]

lemma smoothOn_descendTempered {d : ℕ} {T : Tempered ℂ d}
    {U : Set (Euclidean d)} (hT : SmoothOn T U) : SmoothOn (descendTempered (𝕜 := 𝕜) T) U := by
  obtain ⟨f, hf, hpair⟩ := hT
  refine ⟨(RCLike.map ℂ 𝕜) ∘ f, (RCLike.map ℂ 𝕜).contDiff.comp_contDiffOn hf, ?_⟩
  intro φ hφ hU
  have hs : tsupport (toComplexSchwartz φ) ⊆ tsupport φ :=
    tsupport_comp_subset (g := RCLike.map 𝕜 ℂ) (map_zero _) φ
  obtain ⟨hi, he⟩ := hpair (toComplexSchwartz φ)
    (hφ.of_isClosed_subset isClosed_closure hs) (hs.trans hU)
  have heq : (fun x => RCLike.map ℂ 𝕜 (f x * toComplexSchwartz φ x)) =
      fun x => RCLike.map ℂ 𝕜 (f x) * φ x := by
    funext x
    change RCLike.map ℂ 𝕜 (f x * RCLike.map 𝕜 ℂ (φ x)) = _
    rw [mul_comm, fromComplex_toComplex_mul, mul_comm]
  refine ⟨?_, ?_⟩
  · exact ((RCLike.map ℂ 𝕜).integrable_comp hi).congr (Filter.Eventually.of_forall (fun x => congrFun heq x))
  · change RCLike.map ℂ 𝕜 (T (toComplexSchwartz φ)) = _
    rw [he, ← (RCLike.map ℂ 𝕜).integral_comp_comm hi, heq]
    rfl

lemma dsupport_descendTempered_subset {d : ℕ} (T : Tempered ℂ d) :
    Distribution.dsupport (fun φ : Schwartz 𝕜 d => descendTempered T φ) ⊆
      Distribution.dsupport (fun φ : Schwartz ℂ d => T φ) := by
  intro x hx
  by_contra hn
  obtain ⟨U, hTU, hU, hxU⟩ := (Distribution.notMem_dsupport_iff x).mp hn
  apply (Distribution.mem_dsupport_iff_not_isVanishingOn x).mp hx U hxU hU
  intro φ hφ
  have hs : tsupport (toComplexSchwartz φ) ⊆ tsupport φ :=
    tsupport_comp_subset (g := RCLike.map 𝕜 ℂ) (map_zero _) φ
  change RCLike.map ℂ 𝕜 (T (toComplexSchwartz φ)) = 0
  have hz : T (toComplexSchwartz φ) = 0 := hTU _ (hs.trans hφ)
  rw [hz, map_zero]

lemma parametrix_equation_descend {d : ℕ} (c : Coefficients 𝕜 d)
    (Q : Tempered ℂ d) (r : Schwartz ℂ d)
    (heq : applyOperator (scalarComplexCoefficients c) Q = Examples.delta ℂ d + regularSchwartz r) :
    applyOperator c (descendTempered Q) = Examples.delta 𝕜 d + regularSchwartz (fromComplexSchwartz r) := by
  rw [← descendTempered_applyOperator, heq]
  have hadd (S T : Tempered ℂ d) :
      descendTempered (𝕜 := 𝕜) (S + T) = descendTempered S + descendTempered T := by
    ext φ
    change (RCLike.map ℂ 𝕜) (S (toComplexSchwartz φ) + T (toComplexSchwartz φ)) = _
    exact map_add _ _ _
  rw [hadd, descendTempered_delta, descendTempered_regularSchwartz]

theorem exists_scalar_tempered_parametrix_equation {d m : ℕ} (c : Coefficients 𝕜 d)
    (hc : IsElliptic c m) :
    ∃ (Q : Tempered 𝕜 d) (r : Schwartz 𝕜 d),
      applyOperator c Q = Examples.delta 𝕜 d + regularSchwartz r := by
  obtain ⟨Q, r, h⟩ := exists_tempered_parametrix_equation (scalarComplexCoefficients c)
    (isElliptic_scalarComplexCoefficients c hc)
  exact ⟨descendTempered Q, fromComplexSchwartz r, parametrix_equation_descend c Q r h⟩


end ScalarDescent

lemma continuousOn_eq_of_test_pairing {d : ℕ} {U : Set (Euclidean d)}
    (hU : IsOpen U) {f g : Euclidean d → ℂ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (h : ∀ φ : Schwartz ℂ d, HasCompactSupport φ → tsupport φ ⊆ U →
      Integrable (fun x => f x * φ x) ∧ Integrable (fun x => g x * φ x) ∧
      (∫ x, f x * φ x) = ∫ x, g x * φ x) : EqOn f g U := by
  have hae : ∀ᵐ x ∂(volume : Measure (Euclidean d)), x ∈ U → (f - g) x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.locallyIntegrableOn hU.measurableSet).sub (hg.locallyIntegrableOn hU.measurableSet))
    intro a ha hac hau
    let φ : Schwartz ℂ d := (hac.comp_left (show (Complex.ofReal 0) = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp ha)
    have hφc : HasCompactSupport φ := hac.comp_left (show (Complex.ofReal 0) = 0 by simp)
    have hφu : tsupport φ ⊆ U :=
      (tsupport_comp_subset (f := a) (g := Complex.ofReal) (by simp)).trans hau
    obtain ⟨hfi, hgi, heq⟩ := h φ hφc hφu
    have hid : (fun x => a x • (f - g) x) =
        (fun x => f x * φ x - g x * φ x) := by
      funext x
      change (a x : ℂ) * (f x - g x) = f x * (a x : ℂ) - g x * (a x : ℂ)
      ring
    rw [hid, integral_sub hfi hgi, heq, sub_self]
  have hfg : f =ᵐ[volume.restrict U] g := by
    apply (ae_restrict_iff' hU.measurableSet).mpr
    filter_upwards [hae] with x hx hxU
    exact sub_eq_zero.mp (hx hxU)
  exact Measure.eqOn_open_of_ae_eq hfg hU hf hg

lemma smoothOn_of_finite_representatives {d : ℕ} {T : Tempered ℂ d}
    {U : Set (Euclidean d)} (hU : IsOpen U)
    (h : ∀ k : ℕ, ∃ f : Euclidean d → ℂ, ContDiffOn ℝ k f U ∧
      ∀ φ : Schwartz ℂ d, HasCompactSupport φ → tsupport φ ⊆ U →
        Integrable (fun x => f x * φ x) ∧ T φ = ∫ x, f x * φ x) :
    SmoothOn T U := by
  obtain ⟨f, hf, hpair⟩ := h 0
  refine ⟨f, contDiffOn_infty.mpr ?_, hpair⟩
  intro k
  obtain ⟨g, hg, hgpair⟩ := h k
  have heq : EqOn f g U := continuousOn_eq_of_test_pairing hU hf.continuousOn hg.continuousOn
    (by
      intro φ hφ hφU
      obtain ⟨hfi, hfe⟩ := hpair φ hφ hφU
      obtain ⟨hgi, hge⟩ := hgpair φ hφ hφU
      exact ⟨hfi, hgi, hfe.symm.trans hge⟩)
  exact hg.congr heq

lemma divide_compact_test {d : ℕ} (φ : Schwartz ℂ d)
    (hφ : HasCompactSupport φ) {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ ∞ a) (ha0 : ∀ x ∈ tsupport φ, a x ≠ 0) :
    ∃ ψ : Schwartz ℂ d, HasCompactSupport ψ ∧ tsupport ψ ⊆ tsupport φ ∧
      (∀ x, ψ x = φ x / a x) ∧ (∀ x, a x * ψ x = φ x) := by
  let q : Euclidean d → ℂ := fun x => φ x / a x
  have hqc : HasCompactSupport q := by
    change HasCompactSupport ((φ : Euclidean d → ℂ) * a⁻¹)
    exact hφ.mul_right
  have hqs : ContDiff ℝ ∞ q := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · simpa only [q, div_eq_mul_inv] using!
        (φ.contDiffAt (⊤ : ℕ∞)).mul (ha.contDiffAt.inv (ha0 x hx))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [q, hy, Pi.zero_apply, zero_div]
  refine ⟨hqc.toSchwartzMap hqs, hqc, ?_, fun x => rfl, ?_⟩
  · change tsupport q ⊆ tsupport φ
    simpa [q, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using
      (tsupport_mul_subset_left (f := (φ : Euclidean d → ℂ)) (g := a⁻¹))
  · intro x
    change a x * (φ x / a x) = φ x
    by_cases hx : x ∈ tsupport φ
    · exact mul_div_cancel₀ _ (ha0 x hx)
    · simp [image_eq_zero_of_notMem_tsupport hx]

lemma finiteRepresentative_of_weightedHs {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) {T : Tempered ℂ d}
    {U : Set (Euclidean d)} {a : Euclidean d → ℂ}
    (ha : a.HasTemperateGrowth) (ha0 : ∀ x ∈ U, a x ≠ 0)
    (u : FourierScale.Hs d s)
    (heq : TemperedDistribution.smulLeftCLM ℂ a T = FourierScale.realization u) :
    ∃ f : Euclidean d → ℂ, ContDiffOn ℝ k f U ∧
      ∀ φ : Schwartz ℂ d, HasCompactSupport φ → tsupport φ ⊆ U →
        Integrable (fun x => f x * φ x) ∧ T φ = ∫ x, f x * φ x := by
  obtain ⟨C, hC, h⟩ := LocalOperations.embedding d k s hs
  obtain ⟨g, hg, hgpair, hgbound⟩ := h u
  let f : Euclidean d → ℂ := fun x => g x / a x
  have hf : ContDiffOn ℝ k f U := by
    simpa only [f, div_eq_mul_inv] using!
      hg.contDiffOn.mul ((ha.1.of_le (by simp)).contDiffOn.inv ha0)
  refine ⟨f, hf, ?_⟩
  intro φ hφ hφU
  obtain ⟨ψ, hψ, hψsub, hψval, hψcancel⟩ :=
    divide_compact_test φ hφ ha.1 (fun x hx => ha0 x (hφU hx))
  have htest : SchwartzMap.smulLeftCLM ℂ a ψ = φ := by
    ext x
    simpa only [SchwartzMap.smulLeftCLM_apply_apply ha, smul_eq_mul] using hψcancel x
  have hid : (fun x => ψ x * g x) = (fun x => f x * φ x) := by
    funext x
    rw [hψval]
    dsimp only [f]
    ring
  obtain ⟨hgi, hge⟩ := hgpair ψ
  refine ⟨hid ▸ hgi, ?_⟩
  calc
    T φ = (TemperedDistribution.smulLeftCLM ℂ a T) ψ := by
      change T φ = T (SchwartzMap.smulLeftCLM ℂ a ψ)
      rw [htest]
    _ = FourierScale.realization u ψ := congrArg (fun S : Tempered ℂ d => S ψ) heq
    _ = ∫ x, ψ x * g x := hge
    _ = ∫ x, f x * φ x := by rw [hid]

/-- Multiplying by a coefficient that has no zeros on U can reveal arbitrary
Sobolev regularity without requiring a single coefficient to work at all orders. -/
lemma smoothOn_of_weightedHs {d : ℕ} {T : Tempered ℂ d}
    {U : Set (Euclidean d)} (hU : IsOpen U)
    (h : ∀ k : ℕ, ∃ (s : ℝ) (a : Euclidean d → ℂ) (u : FourierScale.Hs d s),
      (k : ℝ) + (d : ℝ) / 2 < s ∧ a.HasTemperateGrowth ∧
      (∀ x ∈ U, a x ≠ 0) ∧
      TemperedDistribution.smulLeftCLM ℂ a T = FourierScale.realization u) :
    SmoothOn T U := by
  apply smoothOn_of_finite_representatives hU
  intro k
  obtain ⟨s, a, u, hs, ha, ha0, heq⟩ := h k
  exact finiteRepresentative_of_weightedHs hs ha ha0 u heq

lemma smoothOn_punctured_of_radial_MemHs {d : ℕ} {T : Tempered ℂ d}
    (h : ∀ k : ℕ, ∃ (N : ℕ) (s : ℝ),
      (k : ℝ) + (d : ℝ) / 2 < s ∧
      FourierScale.MemHs s (TemperedDistribution.smulLeftCLM ℂ
        (fun x : Euclidean d => (((‖x‖ ^ 2) ^ N : ℝ) : ℂ)) T)) :
    SmoothOn T ({0}ᶜ : Set (Euclidean d)) := by
  apply smoothOn_of_weightedHs isClosed_singleton.isOpen_compl
  intro k
  obtain ⟨N, s, hs, hmem⟩ := h k
  obtain ⟨u, hu⟩ := (FourierScale.realization_image d s _).mpr hmem
  refine ⟨s, (fun x : Euclidean d => (((‖x‖ ^ 2) ^ N : ℝ) : ℂ)), u, hs, ?_, ?_, hu.symm⟩
  · exact Complex.hasTemperateGrowth_ofReal.comp
      ((Function.hasTemperateGrowth_norm_sq (H := Euclidean d)).pow N)
  · intro x hx
    have hx0 : x ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hx0)))


section FourierGain
open FourierScale
lemma hasFourierDensity_fourierMultiplier {d : ℕ} {T : Tempered ℂ d}
    {f : Euclidean d → ℂ} (hf : HasFourierDensity T f)
    (q : Euclidean d → ℂ) (hq : q.HasTemperateGrowth) :
    HasFourierDensity (TemperedDistribution.fourierMultiplierCLM ℂ q T)
      (fun ξ => q ξ * f ξ) := by
  refine ⟨hf.1.continuous_mul hq.1.continuous, ?_⟩
  intro φ
  let ψ : Schwartz ℂ d := SchwartzMap.smulLeftCLM ℂ q φ
  have heq : (fun ξ => ψ ξ * f ξ) = (fun ξ => φ ξ * (q ξ * f ξ)) := by
    funext ξ
    simp only [ψ, SchwartzMap.smulLeftCLM_apply_apply hq, smul_eq_mul]
    ring
  refine ⟨by rw [← heq]; exact (hf.2 ψ).1, ?_⟩
  change (𝓕 (TemperedDistribution.fourierMultiplierCLM ℂ q (T : TemperedDistribution (Euclidean d) ℂ)) :
    TemperedDistribution (Euclidean d) ℂ) φ = _
  rw [TemperedDistribution.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    TemperedDistribution.smulLeftCLM_apply_apply]
  change temperedFourier T ψ = _
  rw [(hf.2 ψ).2, heq]

lemma memHs_fourierMultiplier_gain {d : ℕ} {s t : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) (q : Euclidean d → ℂ) (hq : q.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ ξ : Euclidean d, ‖complexWeight t ξ * q ξ‖ ≤ C) :
    MemHs (s + t) (TemperedDistribution.fourierMultiplierCLM ℂ q T) := by
  obtain ⟨f, hf, hmem⟩ := hT
  refine ⟨fun ξ => q ξ * f ξ, hasFourierDensity_fourierMultiplier hf q hq, ?_⟩
  have heq : (fun ξ => complexWeight (s + t) ξ * (q ξ * f ξ)) =
      (fun ξ => (complexWeight t ξ * q ξ) * (complexWeight s ξ * f ξ)) := by
    funext ξ
    rw [complexWeight_add]
    simp only [Pi.mul_apply]
    ring
  rw [heq]
  refine hmem.of_le_mul ?_ (c := C) ?_
  · exact (((complexWeight_hasTemperateGrowth t).mul hq).1.continuous.aestronglyMeasurable).mul
      hmem.aestronglyMeasurable
  · filter_upwards [] with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)


end FourierGain

lemma fderiv_reciprocalSymbol_outside {d : ℕ} (p q : Euclidean d → ℂ)
    {R : ℝ} (hi : ∀ ξ : Euclidean d, R ≤ ‖ξ‖ → q ξ = (p ξ)⁻¹)
    {ξ : Euclidean d} (hξ : R < ‖ξ‖) (hp : DifferentiableAt ℝ p ξ) (hp0 : p ξ ≠ 0) :
    fderiv ℝ q ξ =
      (-ContinuousLinearMap.mulLeftRight ℝ ℂ (p ξ)⁻¹ (p ξ)⁻¹).comp (fderiv ℝ p ξ) := by
  have hU : {y : Euclidean d | R < ‖y‖} ∈ 𝓝 ξ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hξ
  have he : q =ᶠ[𝓝 ξ] (fun y => (p y)⁻¹) := by
    filter_upwards [hU] with y hy
    exact hi y hy.le
  rw [he.fderiv_eq]
  exact ((hasFDerivAt_inv' (𝕜 := ℝ) hp0).comp ξ hp.hasFDerivAt).fderiv

lemma norm_fderiv_reciprocalSymbol_outside {d : ℕ} (p q : Euclidean d → ℂ)
    {R : ℝ} (hi : ∀ ξ : Euclidean d, R ≤ ‖ξ‖ → q ξ = (p ξ)⁻¹)
    {ξ : Euclidean d} (hξ : R < ‖ξ‖) (hp : DifferentiableAt ℝ p ξ) (hp0 : p ξ ≠ 0) :
    ‖fderiv ℝ q ξ‖ ≤ ‖p ξ‖⁻¹ ^ 2 * ‖fderiv ℝ p ξ‖ := by
  rw [fderiv_reciprocalSymbol_outside p q hi hξ hp hp0]
  calc
    _ ≤ ‖-ContinuousLinearMap.mulLeftRight ℝ ℂ (p ξ)⁻¹ (p ξ)⁻¹‖ *
        ‖fderiv ℝ p ξ‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖(p ξ)⁻¹‖ * ‖(p ξ)⁻¹‖) * ‖fderiv ℝ p ξ‖ := by
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ ℂ _ _) (norm_nonneg _)
    _ = _ := by rw [norm_inv]; ring



lemma temperedPartial_smul {d : ℕ} (i : Fin d) (z : ℂ) (T : Tempered ℂ d) :
    temperedPartial i (z • T) = z • temperedPartial i T := by
  ext φ
  simp [temperedPartial, ContinuousLinearMap.comp_apply]

lemma smulLeft_coordinatePow_succ {d : ℕ} (i : Fin d) (n : ℕ) (T : Tempered ℂ d) :
    TemperedDistribution.smulLeftCLM ℂ (fun x : Euclidean d => (x i : ℂ) ^ (n + 1)) T =
      temperedCoordinateMultiply i
        (TemperedDistribution.smulLeftCLM ℂ (fun x : Euclidean d => (x i : ℂ) ^ n) T) := by
  ext φ
  change T (SchwartzMap.smulLeftCLM ℂ (fun x : Euclidean d => (x i : ℂ) ^ (n + 1)) φ) =
    T (SchwartzMap.smulLeftCLM ℂ (fun x : Euclidean d => (x i : ℂ) ^ n)
      (coordinateMultiply i φ))
  congr 1
  ext x
  have hpn : (fun x : Euclidean d => (x i : ℂ) ^ n).HasTemperateGrowth :=
    (coordinate_growth (𝕜 := ℂ) i).pow n
  have hps : (fun x : Euclidean d => (x i : ℂ) ^ (n + 1)).HasTemperateGrowth :=
    (coordinate_growth (𝕜 := ℂ) i).pow (n + 1)
  rw [SchwartzMap.smulLeftCLM_apply_apply hps, SchwartzMap.smulLeftCLM_apply_apply hpn]
  have hpi : (fun x : Euclidean d => (x i : ℂ)).HasTemperateGrowth :=
    coordinate_growth (𝕜 := ℂ) i
  rw [coordinateMultiply, SchwartzMap.smulLeftCLM_apply_apply hpi]
  simp only [smul_eq_mul, pow_succ, mul_assoc]

lemma fourier_coordinatePow {d : ℕ} (i : Fin d) (n : ℕ) (T : Tempered ℂ d) :
    temperedFourier
      (TemperedDistribution.smulLeftCLM ℂ (fun x : Euclidean d => (x i : ℂ) ^ n) T) =
      (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ n •
        ((temperedPartial i)^[n] (temperedFourier T)) := by
  induction n with
  | zero =>
    simp only [pow_zero, Function.iterate_zero, id_eq, one_smul]
    have h := TemperedDistribution.smulLeftCLM_const (F := ℂ) 1
      (show TemperedDistribution (Euclidean d) ℂ from T)
    rw [h, one_smul]
  | succ n ih =>
    rw [smulLeft_coordinatePow_succ, fourier_coordinate, ih, temperedPartial_smul]
    rw [smul_smul, pow_succ', Function.iterate_succ_apply']

lemma coordinatePow_memHs_of_derivative_density {d : ℕ} (i : Fin d)
    (n : ℕ) (s : ℝ) (T : Tempered ℂ d) (f : Euclidean d → ℂ)
    (hfl : LocallyIntegrable f volume)
    (hf : ∀ φ : Schwartz ℂ d, Integrable (fun x => φ x * f x) ∧
      ((temperedPartial i)^[n] (temperedFourier T)) φ = ∫ x, φ x * f x)
    (hLp : MemLp (fun x => FourierScale.complexWeight s x * f x) 2 volume) :
    FourierScale.MemHs s (TemperedDistribution.smulLeftCLM ℂ
      (fun x : Euclidean d => (x i : ℂ) ^ n) T) := by
  let z : ℂ := (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ n
  refine ⟨fun x => z * f x, ⟨?_, ?_⟩, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using! hfl.smul z
  · intro φ
    obtain ⟨hfi, hfe⟩ := hf φ
    have hid : (fun x => z * (φ x * f x)) = (fun x => φ x * (z * f x)) := by
      funext x
      ring
    refine ⟨hid ▸ hfi.const_mul z, ?_⟩
    calc
      _ = z * (((temperedPartial i)^[n] (temperedFourier T)) φ) := by
        have he := congrArg (fun S : Tempered ℂ d => S φ) (fourier_coordinatePow i n T)
        exact he
      _ = z * (∫ x, φ x * f x) := by rw [hfe]
      _ = ∫ x, z * (φ x * f x) := (integral_const_mul _ _).symm
      _ = ∫ x, φ x * (z * f x) := by rw [hid]
  · have hid : (fun x => z * (FourierScale.complexWeight s x * f x)) =
        (fun x => FourierScale.complexWeight s x * (z * f x)) := by
      funext x
      ring
    exact hid ▸ hLp.const_mul z

lemma memHs_sum {d : ℕ} {ι : Type*} (r : Finset ι) (s : ℝ)
    (F : ι → Tempered ℂ d) (hF : ∀ i ∈ r, FourierScale.MemHs s (F i)) :
    FourierScale.MemHs s (∑ i ∈ r, F i) := by
  classical
  have hF' : ∀ i : r, ∃ u : FourierScale.Hs d s, FourierScale.realization u = F i := by
    intro i
    exact (FourierScale.realization_image d s (F i)).mpr (hF i i.property)
  choose u hu using hF'
  apply (FourierScale.realization_image d s _).mp
  refine ⟨∑ i : r, u i, ?_⟩
  have hsum := map_sum (LocalOperations.realizationCLM d s) (fun i : r => u i) Finset.univ
  change FourierScale.realization (∑ i : r, u i) = ∑ i : r, FourierScale.realization (u i) at hsum
  rw [hsum]
  simp only [hu]
  exact Finset.sum_attach r F

lemma even_coordinate_sum_ne_zero {d : ℕ} (N : ℕ) (x : Euclidean d) (hx : x ≠ 0) :
    (∑ i : Fin d, (x i : ℂ) ^ (2 * N)) ≠ 0 := by
  have hex : ∃ i : Fin d, x i ≠ 0 := by
    by_contra! h
    apply hx
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hnonneg : ∀ j : Fin d, 0 ≤ (x j) ^ (2 * N) := by
    intro j
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hpos : 0 < (x i) ^ (2 * N) := by
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hi) _
  have hsumpos : 0 < ∑ j : Fin d, (x j) ^ (2 * N) :=
    Finset.sum_pos' (fun j _ => hnonneg j) ⟨i, Finset.mem_univ i, hpos⟩
  intro hsumzero
  have hsumzero' : (∑ j : Fin d, (x j) ^ (2 * N)) = 0 := by exact_mod_cast hsumzero
  exact hsumpos.ne' hsumzero'

lemma coordinateSum_memHs {d : ℕ} (N : ℕ) (s : ℝ) (T : Tempered ℂ d)
    (h : ∀ i : Fin d, FourierScale.MemHs s (TemperedDistribution.smulLeftCLM ℂ
      (fun x : Euclidean d => (x i : ℂ) ^ (2 * N)) T)) :
    FourierScale.MemHs s (TemperedDistribution.smulLeftCLM ℂ
      (fun x : Euclidean d => ∑ i : Fin d, (x i : ℂ) ^ (2 * N)) T) := by
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      (fun x : Euclidean d => (x i : ℂ) ^ (2 * N)).HasTemperateGrowth := by
    intro i hi
    exact (coordinate_growth (𝕜 := ℂ) i).pow (2 * N)
  have hm := congrArg
    (fun A : TemperedDistribution (Euclidean d) ℂ →L[ℂ]
      TemperedDistribution (Euclidean d) ℂ => A T)
    (TemperedDistribution.smulLeftCLM_sum (F := ℂ) hg)
  have heq : TemperedDistribution.smulLeftCLM ℂ
      (fun x : Euclidean d => ∑ i : Fin d, (x i : ℂ) ^ (2 * N)) T =
      ∑ i : Fin d, TemperedDistribution.smulLeftCLM ℂ
        (fun x : Euclidean d => (x i : ℂ) ^ (2 * N)) T := by
    simpa only [sum_apply] using! hm
  rw [heq]
  exact memHs_sum Finset.univ s _ (fun i _ => h i)

lemma smoothOn_punctured_of_coordinate_derivative_densities {d : ℕ} (T : Tempered ℂ d)
    (h : ∀ k : ℕ, ∃ (N : ℕ) (s : ℝ) (f : Fin d → Euclidean d → ℂ),
      (k : ℝ) + (d : ℝ) / 2 < s ∧
      ∀ i : Fin d, LocallyIntegrable (f i) volume ∧
        (∀ φ : Schwartz ℂ d, Integrable (fun x => φ x * f i x) ∧
          ((temperedPartial i)^[2 * N] (temperedFourier T)) φ = ∫ x, φ x * f i x) ∧
        MemLp (fun x => FourierScale.complexWeight s x * f i x) 2 volume) :
    SmoothOn T ({0}ᶜ : Set (Euclidean d)) := by
  apply smoothOn_of_weightedHs isClosed_singleton.isOpen_compl
  intro k
  obtain ⟨N, s, f, hs, hf⟩ := h k
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      (fun x : Euclidean d => (x i : ℂ) ^ (2 * N)).HasTemperateGrowth := by
    intro i hi
    exact (coordinate_growth (𝕜 := ℂ) i).pow (2 * N)
  have hmem : FourierScale.MemHs s (TemperedDistribution.smulLeftCLM ℂ
      (fun x : Euclidean d => ∑ i : Fin d, (x i : ℂ) ^ (2 * N)) T) := by
    apply coordinateSum_memHs N s T
    intro i
    exact coordinatePow_memHs_of_derivative_density i (2 * N) s T (f i)
      (hf i).1 (hf i).2.1 (hf i).2.2
  obtain ⟨u, hu⟩ := (FourierScale.realization_image d s _).mpr hmem
  refine ⟨s, (fun x : Euclidean d => ∑ i : Fin d, (x i : ℂ) ^ (2 * N)),
    u, hs, ?_, ?_, hu.symm⟩
  · exact Function.HasTemperateGrowth.sum hg
  · intro x hx
    exact even_coordinate_sum_ne_zero N x
      (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx)


section BaseSobolev
open FourierScale
lemma hasFourierDensity_inverseSymbol {d : ℕ} (q : Euclidean d → ℂ)
    (hq : q.HasTemperateGrowth) : HasFourierDensity (inverseSymbol q) q := by
  refine ⟨hq.1.continuous.locallyIntegrable, ?_⟩
  intro φ
  have hi : Integrable (fun ξ => φ ξ * q ξ) := by
    have h := (SchwartzMap.smulLeftCLM ℂ q φ).integrable
      (μ := (volume : Measure (Euclidean d)))
    simpa only [SchwartzMap.smulLeftCLM_apply hq, smul_eq_mul, mul_comm] using h
  refine ⟨hi, ?_⟩
  rw [fourier_inverseSymbol]
  change (∫ ξ, (SchwartzMap.smulLeftCLM ℂ q φ) ξ) = ∫ ξ, φ ξ * q ξ
  congr 1
  funext ξ
  simp only [SchwartzMap.smulLeftCLM_apply_apply hq, smul_eq_mul, mul_comm]

lemma inverseSymbol_memHs_negative {d : ℕ} (q : Euclidean d → ℂ)
    (hq : q.HasTemperateGrowth) :
    ∃ N : ℕ, MemHs (-(N : ℝ)) (inverseSymbol q) := by
  obtain ⟨M, C, hb⟩ := hq.2 0
  have hb' : ∀ ξ, ‖q ξ‖ ≤ max C 0 * (1 + ‖ξ‖) ^ M := by
    intro ξ
    have h := hb ξ
    simp only [norm_iteratedFDeriv_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨N, hN⟩ := LocalOperations.polynomial_density_memLp q hq.1.continuous M (max C 0)
    (le_max_right _ _) hb'
  exact ⟨N, q, hasFourierDensity_inverseSymbol q hq, hN⟩

end BaseSobolev

/-- Scalar descent preserves the entire global conclusion, including the
actual punctured smooth representatives and bilinear test pairings. -/
theorem global_parametrix_of_complex
    (h : ∀ (d m : ℕ) (c : Coefficients ℂ d), IsElliptic c m →
      ∃ (Q : Tempered ℂ d) (r : Schwartz ℂ d),
        SmoothOn Q ({0}ᶜ : Set (Euclidean d)) ∧
        applyOperator c Q = Examples.delta ℂ d + regularSchwartz r) :
    Specs.ExpandedFA.Sobolev.EllipticParametrix.globalParametrixType := by
  intro 𝕜 _ d m c hc
  obtain ⟨Q, r, hQ, he⟩ := h d m (scalarComplexCoefficients c)
    (isElliptic_scalarComplexCoefficients c hc)
  exact ⟨descendTempered Q, fromComplexSchwartz r,
    smoothOn_descendTempered hQ, parametrix_equation_descend c Q r he⟩


lemma reciprocal_multiplier_left_inverse {d : ℕ} (c : Coefficients ℂ d)
    (q : Euclidean d → ℂ) (hq : q.HasTemperateGrowth) (χ : Schwartz ℂ d)
    (hpq : ∀ ξ, fourierSymbol c ξ * q ξ = 1 - χ ξ) (T : Tempered ℂ d) :
    TemperedDistribution.fourierMultiplierCLM ℂ q (applyOperator c T) =
      @Sub.sub (Tempered ℂ d) inferInstance T (TemperedDistribution.fourierMultiplierCLM ℂ χ T) := by
  obtain ⟨e, he, _⟩ := Inversion.tempered_automorphism d
  apply e.injective
  rw [he, he]
  have hm (q : Euclidean d → ℂ) (S : Tempered ℂ d) :
      temperedFourier (TemperedDistribution.fourierMultiplierCLM ℂ q S) =
      TemperedDistribution.smulLeftCLM ℂ q (temperedFourier S) := by
    let SN : TemperedDistribution (Euclidean d) ℂ := S
    change 𝓕 (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ q (𝓕 SN)) : TemperedDistribution (Euclidean d) ℂ) = _
    exact FourierTransform.fourier_fourierInv_eq _
  rw [hm, fourier_operator]
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (fourierSymbol_hasTemperateGrowth c) hq]
  have hpq' : fourierSymbol c * q = fun ξ => 1 - χ ξ := by
    funext ξ
    exact hpq ξ
  rw [hpq']
  have hs := congrArg
    (fun A : TemperedDistribution (Euclidean d) ℂ →L[ℂ]
      TemperedDistribution (Euclidean d) ℂ => A (temperedFourier T))
    (TemperedDistribution.smulLeftCLM_sub
      (Function.HasTemperateGrowth.const (E := Euclidean d) (1 : ℂ)) χ.hasTemperateGrowth)
  change TemperedDistribution.smulLeftCLM ℂ ((fun _ : Euclidean d => (1 : ℂ)) - (χ : Euclidean d → ℂ)) (temperedFourier T) = _
  rw [hs]
  simp only [sub_apply]
  rw [TemperedDistribution.smulLeftCLM_const, one_smul]
  have hmχ := hm χ T
  ext φ
  have hx := congrArg (fun S : TemperedDistribution (Euclidean d) ℂ => S φ) hmχ
  change temperedFourier T φ - _ = temperedFourier T φ - _
  exact congrArg (fun z => temperedFourier T φ - z) hx.symm



section SobolevCalculus
open FourierScale
lemma memHs_mono {d : ℕ} {s t : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) (hts : t ≤ s) : MemHs t T := by
  have hb : ∀ ξ : Euclidean d, ‖complexWeight (t - s) ξ * (1 : ℂ)‖ ≤ 1 := by
    intro ξ
    rw [mul_one, show t - s = -(s - t) by ring]
    exact complexWeight_neg_norm_le_one (sub_nonneg.mpr hts) ξ
  have h := memHs_fourierMultiplier_gain hT (fun _ => 1)
    (Function.HasTemperateGrowth.const 1) hb
  simpa only [show s + (t - s) = t by ring,
    TemperedDistribution.fourierMultiplierCLM_const, one_smul,
    ContinuousLinearMap.id_apply] using h

lemma memHs_multiDerivative {d : ℕ} {s : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) (α : Fin d → ℕ) :
    MemHs (s - (∑ i, α i : ℕ)) (LocalOperations.multiDerivative α T) := by
  obtain ⟨u, hu⟩ := (realization_image d s T).mpr hT
  apply (realization_image d _ _).mp
  refine ⟨LocalOperations.derivativeMap s α u, ?_⟩
  rw [LocalOperations.derivativeMap_realization, hu]

lemma memHs_smulLeftSchwartz {d : ℕ} {s : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) (a : Schwartz ℂ d) :
    MemHs s (TemperedDistribution.smulLeftCLM ℂ a T) := by
  obtain ⟨u, hu⟩ := (realization_image d s T).mpr hT
  apply (realization_image d s _).mp
  refine ⟨LocalOperations.multiplicationMap s a u, ?_⟩
  rw [LocalOperations.multiplicationMap_realization, hu]

lemma memHs_smulLeft_compactSmooth {d : ℕ} {s : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) (a : Euclidean d → ℂ) (ha : ContDiff ℝ ∞ a)
    (hcompact : HasCompactSupport a) :
    MemHs s (TemperedDistribution.smulLeftCLM ℂ a T) := by
  exact memHs_smulLeftSchwartz hT (hcompact.toSchwartzMap ha)

lemma memHs_schwartzFourierMultiplier {d : ℕ} {s t : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) (χ : Schwartz ℂ d) :
    MemHs t (TemperedDistribution.fourierMultiplierCLM ℂ χ T) := by
  let ψ : Schwartz ℂ d := SchwartzMap.smulLeftCLM ℂ (complexWeight (t - s)) χ
  have hb : ∀ ξ : Euclidean d, ‖complexWeight (t - s) ξ * χ ξ‖ ≤
      SchwartzMap.seminorm ℂ 0 0 ψ := by
    intro ξ
    simpa only [ψ, SchwartzMap.smulLeftCLM_apply_apply
      (complexWeight_hasTemperateGrowth _), smul_eq_mul] using
      SchwartzMap.norm_le_seminorm ℂ ψ ξ
  have h := memHs_fourierMultiplier_gain hT χ χ.hasTemperateGrowth hb
  simpa only [show s + (t - s) = t by ring] using h

lemma memHs_temperedPartial {d : ℕ} {s : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) (i : Fin d) : MemHs (s - 1) (temperedPartial i T) := by
  let g : Euclidean d → ℂ := fun ξ => (2 * Real.pi * Complex.I) * (ξ i : ℂ)
  have hg : g.HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul (coordinate_growth (𝕜 := ℂ) i)
  have hb : ∀ ξ : Euclidean d, ‖complexWeight (-1) ξ * g ξ‖ ≤ 1 := by
    intro ξ
    have hsq : ‖g ξ‖ ^ 2 ≤ weight 1 ξ ^ 2 := by
      rw [weight_sq, Real.rpow_one]
      exact coordinate_symbol_norm_sq ξ i
    have hn : ‖g ξ‖ ≤ weight 1 ξ :=
      (sq_le_sq₀ (norm_nonneg _) (weight_pos _ _).le).mp hsq
    rw [norm_mul, complexWeight, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (weight_pos _ _)]
    calc
      _ ≤ weight (-1) ξ * weight 1 ξ := mul_le_mul_of_nonneg_left hn (weight_pos _ _).le
      _ = 1 := by simpa only [neg_neg] using weight_neg_mul 1 ξ
  have he : TemperedDistribution.fourierMultiplierCLM ℂ g T = temperedPartial i T := by
    apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution (Euclidean d) ℂ)).injective
    change (𝓕 (TemperedDistribution.fourierMultiplierCLM ℂ g
      (T : TemperedDistribution (Euclidean d) ℂ)) : TemperedDistribution (Euclidean d) ℂ) =
        temperedFourier (temperedPartial i T)
    rw [TemperedDistribution.fourierMultiplierCLM_apply,
      FourierTransform.fourier_fourierInv_eq, fourier_temperedPartial_symbol]
    rfl
  have h := memHs_fourierMultiplier_gain hT g hg hb
  simpa only [he, sub_eq_add_neg] using h

lemma memHs_wordPartial {d : ℕ} {s : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) (w : List (Fin d)) :
    MemHs (s - (w.length : ℝ)) (wordPartial w T) := by
  induction w generalizing s T with
  | nil => simpa only [List.length_nil, Nat.cast_zero, sub_zero, wordPartial] using hT
  | cons i w ih =>
    have h := ih (memHs_temperedPartial hT i)
    change MemHs ((s - 1) - (w.length : ℝ)) (wordPartial (i :: w) T) at h
    convert h using 1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

lemma memHs_zero {d : ℕ} (s : ℝ) : MemHs s (0 : Tempered ℂ d) := by
  apply (realization_image d s _).mp
  refine ⟨0, ?_⟩
  change (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))
    (Lp.toTemperedDistribution (0 : L2 d))) : TemperedDistribution (Euclidean d) ℂ) = 0
  have hLp : Lp.toTemperedDistribution (0 : L2 d) = 0 :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).map_zero
  rw [hLp, map_zero, FourierTransform.fourierInv_zero]

lemma memHs_add {d : ℕ} {s : ℝ} {T U : Tempered ℂ d}
    (hT : MemHs s T) (hU : MemHs s U) : MemHs s (T + U) := by
  obtain ⟨u, hu⟩ := (realization_image d s T).mpr hT
  obtain ⟨v, hv⟩ := (realization_image d s U).mpr hU
  apply (realization_image d s _).mp
  refine ⟨u + v, ?_⟩
  rw [(realization_linear d s).1, hu, hv]

lemma memHs_smul {d : ℕ} {s : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) (a : ℂ) : MemHs s (a • T) := by
  obtain ⟨u, hu⟩ := (realization_image d s T).mpr hT
  apply (realization_image d s _).mp
  refine ⟨a • u, ?_⟩
  rw [(realization_linear d s).2, hu]

lemma memHs_neg {d : ℕ} {s : ℝ} {T : Tempered ℂ d}
    (hT : MemHs s T) : MemHs s (-T) := by
  have he : (-1 : ℂ) • T = -T := by
    ext φ
    change (-1 : ℂ) * T φ = -(T φ)
    ring
  rw [← he]
  exact memHs_smul hT (-1)

lemma memHs_sub {d : ℕ} {s : ℝ} {T U : Tempered ℂ d}
    (hT : MemHs s T) (hU : MemHs s U) : MemHs s (T - U) := by
  simpa only [sub_eq_add_neg] using memHs_add hT (memHs_neg hU)

lemma memHs_regularSchwartz {d : ℕ} (s : ℝ) (f : Schwartz ℂ d) :
    MemHs s (regularSchwartz f) := by
  exact (realization_image d s _).mp (schwartz_inclusion d s f)


end SobolevCalculus

/-- The reciprocal symbol gains the full elliptic order; the low-frequency
Schwartz error is smoothing at every order. -/
lemma memHs_elliptic_gain {d m : ℕ} (c : Coefficients ℂ d) (hc : IsElliptic c m)
    {s t : ℝ} {T : Tempered ℂ d} (hT : FourierScale.MemHs s T)
    (hL : FourierScale.MemHs t (applyOperator c T)) :
    FourierScale.MemHs (t + (m : ℝ)) T := by
  obtain ⟨q, χ, C, R, hq, hχ, hC, hR, hpq, hi, hb, hweight⟩ :=
    exists_reciprocal_symbol_decay c hc
  let A : Tempered ℂ d := TemperedDistribution.fourierMultiplierCLM ℂ q (applyOperator c T)
  let B : Tempered ℂ d := TemperedDistribution.fourierMultiplierCLM ℂ χ T
  have hA : FourierScale.MemHs (t + (m : ℝ)) A :=
    memHs_fourierMultiplier_gain hL q hq hweight
  have hB : FourierScale.MemHs (t + (m : ℝ)) B :=
    memHs_schwartzFourierMultiplier hT χ
  have heq : A = T - B := reciprocal_multiplier_left_inverse c q hq χ hpq T
  have heq' : A + B = T := by rw [heq]; exact sub_add_cancel _ _
  exact heq' ▸ memHs_add hA hB


section
open FourierScale
def LocallyMemHs {d : ℕ} (s : ℝ) (U : Set (Euclidean d)) (T : Tempered ℂ d) : Prop :=
  ∀ a : Schwartz ℂ d, HasCompactSupport a → tsupport a ⊆ U → MemHs s (cutoffProduct a T)

lemma cutoffProduct_eq_smulLeft {d : ℕ} (a : Schwartz ℂ d) (T : Tempered ℂ d) :
    cutoffProduct a T = TemperedDistribution.smulLeftCLM ℂ a T := by
  ext φ
  change T (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) a φ) =
    T (SchwartzMap.smulLeftCLM ℂ (a : Euclidean d → ℂ) φ)
  congr 1
  ext x
  simp [SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth]

lemma locallyMemHs_of_memHs {d : ℕ} {s : ℝ} {U : Set (Euclidean d)}
    {T : Tempered ℂ d} (hT : MemHs s T) : LocallyMemHs s U T := by
  intro a hac haU
  rw [cutoffProduct_eq_smulLeft]
  exact memHs_smulLeftSchwartz hT a

lemma wordPartial_singleton_sub {d : ℕ} (i : Fin d) (S T : Tempered ℂ d) :
    wordPartial [i] (S - T) = wordPartial [i] S - wordPartial [i] T := by
  ext φ
  simp [wordPartial]
  abel

/-- The exact word commutator, before any regularity is imposed. -/
def wordCommutator {d : ℕ} (a : Schwartz ℂ d) (w : List (Fin d)) (T : Tempered ℂ d) :
    Tempered ℂ d := wordPartial w (cutoffProduct a T) - cutoffProduct a (wordPartial w T)

lemma wordCommutator_append_singleton {d : ℕ} (a : Schwartz ℂ d)
    (w : List (Fin d)) (i : Fin d) (T : Tempered ℂ d) :
    wordCommutator a (w ++ [i]) T = wordPartial [i] (wordCommutator a w T) +
      cutoffProduct (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) a)
        (wordPartial w T) := by
  unfold wordCommutator
  rw [wordPartial_append, wordPartial_append, wordPartial_singleton_sub, cutoffProduct_partial]
  abel


lemma locallyMemHs_partial {d : ℕ} {s : ℝ} {U : Set (Euclidean d)}
    {T : Tempered ℂ d} (hT : LocallyMemHs s U T) (i : Fin d) :
    LocallyMemHs (s - 1) U (wordPartial [i] T) := by
  intro a hac haU
  let D := LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)
  have hs : tsupport (D a) ⊆ tsupport a := tsupport_fderiv_apply_subset ℝ (basisVector i)
  have he : cutoffProduct a (wordPartial [i] T) = wordPartial [i] (cutoffProduct a T) -
      cutoffProduct (D a) T :=
    eq_sub_iff_add_eq.mpr (cutoffProduct_partial a T i).symm
  rw [he]
  refine memHs_sub ?_ ?_
  · exact memHs_temperedPartial (hT a hac haU) i
  · exact memHs_mono
      (hT (D a) (hac.of_isClosed_subset isClosed_closure hs) (hs.trans haU)) (by linarith)

lemma locallyMemHs_wordPartial {d : ℕ} {s : ℝ} {U : Set (Euclidean d)}
    {T : Tempered ℂ d} (hT : LocallyMemHs s U T) (w : List (Fin d)) :
    LocallyMemHs (s - (w.length : ℝ)) U (wordPartial w T) := by
  induction w using List.reverseRecOn with
  | nil => simpa [wordPartial] using hT
  | @append_singleton w i ih =>
    have h := locallyMemHs_partial ih i
    simpa only [wordPartial_append, List.length_append, List.length_singleton,
      Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using h

lemma wordCommutator_memHs {d : ℕ} {s : ℝ} {U : Set (Euclidean d)}
    {T : Tempered ℂ d} (hT : LocallyMemHs s U T)
    (a : Schwartz ℂ d) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U)
    (w : List (Fin d)) : MemHs (s - (w.length : ℝ) + 1) (wordCommutator a w T) := by
  induction w using List.reverseRecOn with
  | nil => simpa [wordCommutator, wordPartial] using (memHs_zero (d := d) (s + 1))
  | @append_singleton w i ih =>
    rw [wordCommutator_append_singleton]
    let D := LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)
    have hs : tsupport (D a) ⊆ tsupport a := tsupport_fderiv_apply_subset ℝ (basisVector i)
    have h₁ : MemHs (s - (w.length : ℝ)) (wordPartial [i] (wordCommutator a w T)) := by
      have h := memHs_temperedPartial ih i
      rw [show (s - (w.length : ℝ) + 1) - 1 = s - (w.length : ℝ) by ring] at h
      exact h
    have h₂ : MemHs (s - (w.length : ℝ)) (cutoffProduct (D a) (wordPartial w T)) :=
      locallyMemHs_wordPartial hT w (D a)
        (hac.of_isClosed_subset isClosed_closure hs) (hs.trans haU)
    convert memHs_add h₁ h₂ using 1
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    ring


def operatorCommutator {d : ℕ} (c : Coefficients ℂ d) (a : Schwartz ℂ d)
    (T : Tempered ℂ d) : Tempered ℂ d :=
  applyOperator c (cutoffProduct a T) - cutoffProduct a (applyOperator c T)

lemma operatorCommutator_eq_sum {d : ℕ} (c : Coefficients ℂ d) (a : Schwartz ℂ d)
    (T : Tempered ℂ d) : operatorCommutator c a T =
      ∑ α ∈ c.support, c α • wordCommutator a (multiIndexWord α) T := by
  simp only [operatorCommutator, applyOperator, cutoffProduct_sum, cutoffProduct_smul,
    wordCommutator, smul_sub, Finset.sum_sub_distrib]

lemma operatorCommutator_memHs {d m : ℕ} {s : ℝ} {U : Set (Euclidean d)}
    {T : Tempered ℂ d} (c : Coefficients ℂ d) (hc : HasOrder c m)
    (hT : LocallyMemHs s U T) (a : Schwartz ℂ d)
    (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) :
    MemHs (s - (m : ℝ) + 1) (operatorCommutator c a T) := by
  rw [operatorCommutator_eq_sum]
  apply memHs_sum
  intro α hα
  apply memHs_smul
  apply memHs_mono (wordCommutator_memHs hT a hac haU (multiIndexWord α))
  have hd := hc.1 α hα
  have hl : ((multiIndexWord α).length : ℝ) ≤ (m : ℝ) := by
    rw [multiIndexWord_length]
    exact_mod_cast hd
  linarith

lemma cutoffProduct_delta_zero {d : ℕ} (a : Schwartz ℂ d)
    (ha : tsupport a ⊆ ({0}ᶜ : Set (Euclidean d))) :
    cutoffProduct a (Examples.delta ℂ d) = 0 := by
  have h0 : (0 : Euclidean d) ∉ tsupport a := by
    intro h
    exact ha h (by simp)
  ext φ
  simp [cutoffProduct, Examples.delta, image_eq_zero_of_notMem_tsupport h0]

lemma locallyMemHs_cutoff_operator {d m : ℕ} {s : ℝ} {Q : Tempered ℂ d}
    (c : Coefficients ℂ d) (hc : HasOrder c m) (r : Schwartz ℂ d)
    (he : applyOperator c Q = Examples.delta ℂ d + regularSchwartz r)
    (hQ : LocallyMemHs s ({0}ᶜ : Set (Euclidean d)) Q)
    (a : Schwartz ℂ d) (hac : HasCompactSupport a)
    (ha : tsupport a ⊆ ({0}ᶜ : Set (Euclidean d))) :
    MemHs (s - (m : ℝ) + 1) (applyOperator c (cutoffProduct a Q)) := by
  have hE := operatorCommutator_memHs c hc hQ a hac ha
  have hrewrite : applyOperator c (cutoffProduct a Q) =
      cutoffProduct a (applyOperator c Q) + operatorCommutator c a Q := by
    unfold operatorCommutator
    abel
  rw [hrewrite, he, cutoffProduct_add, cutoffProduct_delta_zero a ha, zero_add,
    cutoffProduct_regularSchwartz]
  exact memHs_add (memHs_regularSchwartz _ _) hE


lemma locallyMemHs_elliptic_step {d m : ℕ} {s : ℝ} {Q : Tempered ℂ d}
    (c : Coefficients ℂ d) (hc : IsElliptic c m) (r : Schwartz ℂ d)
    (he : applyOperator c Q = Examples.delta ℂ d + regularSchwartz r)
    (hQ : LocallyMemHs s ({0}ᶜ : Set (Euclidean d)) Q) :
    LocallyMemHs (s + 1) ({0}ᶜ : Set (Euclidean d)) Q := by
  intro a hac ha
  have hS := hQ a hac ha
  have hL := locallyMemHs_cutoff_operator c hc.1 r he hQ a hac ha
  have h := memHs_elliptic_gain c hc hS hL
  convert h using 1
  ring

lemma locallyMemHs_elliptic_iterate {d m : ℕ} {s : ℝ} {Q : Tempered ℂ d}
    (c : Coefficients ℂ d) (hc : IsElliptic c m) (r : Schwartz ℂ d)
    (he : applyOperator c Q = Examples.delta ℂ d + regularSchwartz r)
    (hQ : LocallyMemHs s ({0}ᶜ : Set (Euclidean d)) Q) (n : ℕ) :
    LocallyMemHs (s + (n : ℝ)) ({0}ᶜ : Set (Euclidean d)) Q := by
  induction n with
  | zero => simpa using hQ
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      locallyMemHs_elliptic_step c hc r he ih

theorem locallyMemHs_all_of_parametrix_equation {d m : ℕ} {s : ℝ} {Q : Tempered ℂ d}
    (c : Coefficients ℂ d) (hc : IsElliptic c m) (r : Schwartz ℂ d)
    (he : applyOperator c Q = Examples.delta ℂ d + regularSchwartz r)
    (hQ : MemHs s Q) (t : ℝ) :
    LocallyMemHs t ({0}ᶜ : Set (Euclidean d)) Q := by
  obtain ⟨n, hn⟩ := exists_nat_ge (t - s)
  intro a hac ha
  exact memHs_mono
    (locallyMemHs_elliptic_iterate c hc r he (locallyMemHs_of_memHs hQ) n a hac ha)
    (by linarith)


end

section
lemma smoothOn_mono {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {T : Tempered 𝕜 d}
    {U V : Set (Euclidean d)} (hT : SmoothOn T U) (hVU : V ⊆ U) : SmoothOn T V := by
  obtain ⟨f, hf, hp⟩ := hT
  exact ⟨f, hf.mono hVU, fun φ hφ hφV => hp φ hφ (hφV.trans hVU)⟩
lemma smoothOn_of_cutoff_eq_one {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {T : Tempered 𝕜 d} (a : Schwartz 𝕜 d) {U : Set (Euclidean d)}
    (ha : ∀ x ∈ U, a x = 1) (hT : SmoothOn (cutoffProduct a T) U) : SmoothOn T U := by
  obtain ⟨f, hf, hp⟩ := hT
  refine ⟨f, hf, ?_⟩
  intro φ hφ hφU
  obtain ⟨hi, he⟩ := hp φ hφ hφU
  have hprod : SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) a φ = φ := by
    ext x
    by_cases hx : x ∈ tsupport φ
    · simp [ha x (hφU hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  refine ⟨hi, ?_⟩
  change T (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) a φ) = _ at he
  rwa [hprod] at he
lemma smoothOn_of_arbitrary_MemHs {d : ℕ} {T : Tempered ℂ d}
    (hT : ∀ k : ℕ, ∃ s : ℝ, (k : ℝ) + (d : ℝ) / 2 < s ∧ FourierScale.MemHs s T) :
    SmoothOn T Set.univ := by
  apply smoothOn_of_finite_representatives isOpen_univ
  intro k
  obtain ⟨s, hs, hmem⟩ := hT k
  obtain ⟨u, hu⟩ := (FourierScale.realization_image d s T).mpr hmem
  obtain ⟨C, hC, h⟩ := LocalOperations.embedding d k s hs
  obtain ⟨f, hf, hp, hb⟩ := h u
  refine ⟨f, hf.contDiffOn, ?_⟩
  intro φ hφ hφU
  obtain ⟨hi, he⟩ := hp φ
  rw [hu] at he
  simpa only [mul_comm] using And.intro hi he

end


lemma exists_schwartz_cutoff_one_nhds {d : ℕ} {K U : Set (Euclidean d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (a : Schwartz ℂ d) (V : Set (Euclidean d)),
      HasCompactSupport a ∧ tsupport a ⊆ U ∧
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ ∀ x ∈ V, a x = 1 := by
  obtain ⟨C, hC, hKC, hCU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hone, hzero, hfrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, Euclidean d))
      (n := (⊤ : ℕ∞)) hK.isClosed hKC
  have hf : ContDiff ℝ ∞ (f : Euclidean d → ℝ) := by
    simpa only [contMDiff_iff_contDiff] using f.contMDiff
  let ac : Euclidean d → ℂ := fun x => (f x : ℂ)
  have hats : tsupport ac ⊆ C := by
    apply closure_minimal _ hC.isClosed
    intro x hx
    by_contra hxC
    exact hx (by simp [ac, hzero x hxC])
  have hac : HasCompactSupport ac :=
    hC.of_isClosed_subset (isClosed_tsupport ac) hats
  have hacsmooth : ContDiff ℝ ∞ ac := Complex.ofRealCLM.contDiff.comp hf
  let a : Schwartz ℂ d := hac.toSchwartzMap hacsmooth
  obtain ⟨V, hV, hKV, hVone⟩ := eventually_nhdsSet_iff_exists.mp hone
  refine ⟨a, V ∩ U, hac, hats.trans hCU, hV.inter hU, ?_, inter_subset_right, ?_⟩
  · intro x hx
    exact ⟨hKV hx, hKU hx⟩
  · intro x hx
    change (f x : ℂ) = 1
    rw [hVone x hx.1]
    rfl


lemma smoothOn_of_compact_cover {d : ℕ} {ι : Type*} {T : Tempered ℂ d}
    {U : Set (Euclidean d)} (hU : IsOpen U) (V : ι → Set (Euclidean d))
    (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (hcover : ∀ K : Set (Euclidean d), IsCompact K → K ⊆ U → ∃ i, K ⊆ V i)
    (h : ∀ i, SmoothOn T (V i)) : SmoothOn T U := by
  classical
  choose g hg hp using h
  have hcompat : ∀ i j, EqOn (g i) (g j) (V i ∩ V j) := by
    intro i j
    apply continuousOn_eq_of_test_pairing ((hV i).inter (hV j))
      ((hg i).continuousOn.mono inter_subset_left) ((hg j).continuousOn.mono inter_subset_right)
    intro φ hφ hφV
    obtain ⟨hii, hie⟩ := hp i φ hφ (hφV.trans inter_subset_left)
    obtain ⟨hji, hje⟩ := hp j φ hφ (hφV.trans inter_subset_right)
    exact ⟨hii, hji, hie.symm.trans hje⟩
  have hex : ∀ x : U, ∃ i, (x : Euclidean d) ∈ V i := by
    intro x
    obtain ⟨i, hi⟩ := hcover {x.val} isCompact_singleton
      (singleton_subset_iff.mpr x.property)
    exact ⟨i, hi (mem_singleton _)⟩
  choose j hj using hex
  let f : Euclidean d → ℂ := fun x => if hx : x ∈ U then g (j ⟨x, hx⟩) x else 0
  have hfgi : ∀ i, EqOn f (g i) (V i) := by
    intro i x hx
    have hxU : x ∈ U := hVU i hx
    dsimp only [f]
    rw [dite_eq_left hxU]
    exact hcompat (j ⟨x, hxU⟩) i ⟨hj ⟨x, hxU⟩, hx⟩
  refine ⟨f, ?_, ?_⟩
  · apply hU.contDiffOn_iff.mpr
    intro x hx
    let i := j ⟨x, hx⟩
    have hxi : x ∈ V i := hj ⟨x, hx⟩
    apply ((hg i).contDiffAt ((hV i).mem_nhds hxi)).congr_of_eventuallyEq
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨V i, (hV i).mem_nhds hxi, hfgi i⟩
  · intro φ hφ hφU
    obtain ⟨i, hi⟩ := hcover (tsupport φ) hφ hφU
    obtain ⟨hii, hie⟩ := hp i φ hφ hi
    have hid : (fun x => f x * φ x) = (fun x => g i x * φ x) := by
      funext x
      by_cases hx : x ∈ tsupport φ
      · rw [hfgi i (hi hx)]
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    exact ⟨hid.symm ▸ hii, hie.trans (congrArg (fun F : Euclidean d → ℂ => ∫ x, F x) hid).symm⟩

lemma smoothOn_of_compact_local_smoothOn {d : ℕ} {T : Tempered ℂ d}
    {U : Set (Euclidean d)} (hU : IsOpen U)
    (h : ∀ K : Set (Euclidean d), IsCompact K → K ⊆ U →
      ∃ V : Set (Euclidean d), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ SmoothOn T V) :
    SmoothOn T U := by
  let ι := {V : Set (Euclidean d) // IsOpen V ∧ V ⊆ U ∧ SmoothOn T V}
  apply smoothOn_of_compact_cover hU (fun i : ι => i.val)
    (fun i => i.property.1) (fun i => i.property.2.1) ?_ (fun i => i.property.2.2)
  intro K hK hKU
  obtain ⟨V, hVo, hKV, hVU, hTV⟩ := h K hK hKU
  exact ⟨⟨V, hVo, hVU, hTV⟩, hKV⟩

lemma smoothOn_of_all_locallyMemHs {d : ℕ} {T : Tempered ℂ d}
    {U : Set (Euclidean d)} (hU : IsOpen U)
    (hT : ∀ s : ℝ, LocallyMemHs s U T) : SmoothOn T U := by
  apply smoothOn_of_compact_local_smoothOn hU
  intro K hK hKU
  obtain ⟨a, V, hac, haU, hV, hKV, hVU, haV⟩ :=
    exists_schwartz_cutoff_one_nhds hK hU hKU
  have hglobal : SmoothOn (cutoffProduct a T) Set.univ := by
    apply smoothOn_of_arbitrary_MemHs
    intro k
    let s : ℝ := (k : ℝ) + (d : ℝ) / 2 + 1
    exact ⟨s, by dsimp [s]; linarith, hT s a hac haU⟩
  refine ⟨V, hV, hKV, hVU, ?_⟩
  exact smoothOn_of_cutoff_eq_one a haV (smoothOn_mono hglobal (Set.subset_univ V))


/-- The global parametrix for the original constant-coefficient operator.
Its off-origin smoothness follows by local Sobolev bootstrap. -/
theorem global_parametrix :
    Specs.ExpandedFA.Sobolev.EllipticParametrix.globalParametrixType := by
  apply global_parametrix_of_complex
  intro d m c hc
  obtain ⟨q, χ, hq, hχ, hpq⟩ := exists_reciprocal_symbol c hc
  let Q : Tempered ℂ d := inverseSymbol q
  let r : Schwartz ℂ d := -(𝓕⁻ χ)
  have he : applyOperator c Q = Examples.delta ℂ d + regularSchwartz r :=
    inverse_symbol_equation c q hq χ hpq
  obtain ⟨N, hN⟩ := inverseSymbol_memHs_negative q hq
  refine ⟨Q, r, ?_, he⟩
  apply smoothOn_of_all_locallyMemHs isClosed_singleton.isOpen_compl
  intro t
  exact locallyMemHs_all_of_parametrix_equation c hc r he hN t

/-- Localization preserves the original operator and places the native
support inside every prescribed positive open ball. -/
theorem compact_parametrix :
    Specs.ExpandedFA.Sobolev.EllipticParametrix.compactParametrixType := by
  intro 𝕜 _ d m c hc R hR
  obtain ⟨Q, r, hQ, he⟩ := global_parametrix 𝕜 d m c hc
  exact compact_parametrix_of_global c hQ he R hR

end ExpandedFA.Sobolev.Elliptic
