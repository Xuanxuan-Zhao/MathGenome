import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HomogeneousFourier
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.SpecificCodomains.Pi

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Constructions

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform NNReal Topology ContDiff

noncomputable section
namespace ExpandedFA.PartIV.HomogeneousFourier
open ExpandedFA.Fourier

@[simp] theorem scaleEquiv_apply {d : ℕ} (a : ℝ) (ha : a ≠ 0) (x : Euclidean d) :
    scaleEquiv a ha x = a • x := rfl

@[simp] theorem schwartzScale_apply {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (φ : Schwartz ℂ d) (x : Euclidean d) :
    schwartzScale a ha φ x = φ (a • x) := rfl

@[simp] theorem testScale_apply {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (φ : CompactTests d) (x : Euclidean d) : testScale a ha φ x = φ (a • x) := rfl

@[simp] theorem testToSchwartz_apply {d : ℕ} (φ : CompactTests d) (x : Euclidean d) :
    testToSchwartz φ x = φ x := rfl

@[simp] theorem testToSchwartz_scale {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (φ : CompactTests d) :
    testToSchwartz (testScale a ha φ) = schwartzScale a ha (testToSchwartz φ) := by
  ext x
  rfl

lemma degreeFactor_add (a : ℝ) (z w : ℂ) :
    degreeFactor a (z + w) = degreeFactor a z * degreeFactor a w := by
  simp only [degreeFactor, mul_add, Complex.exp_add]

lemma degreeFactor_neg (a : ℝ) (z : ℂ) :
    degreeFactor a (-z) = (degreeFactor a z)⁻¹ := by
  simp only [degreeFactor, mul_neg, Complex.exp_neg]

lemma degreeFactor_inv (a : ℝ) (z : ℂ) :
    degreeFactor a⁻¹ z = (degreeFactor a z)⁻¹ := by
  simp [degreeFactor, Real.log_inv, Complex.exp_neg]

lemma degreeFactor_nat (a : ℝ) (ha : 0 < a) (n : ℕ) :
    degreeFactor a n = (a : ℂ) ^ n := by
  unfold degreeFactor
  rw [mul_comm, Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log ha]

lemma degreeFactor_fourier (d : ℕ) (a : ℝ) (ha : 0 < a) (z : ℂ) :
    degreeFactor a (-(d : ℂ) - z) =
      ((a : ℂ) ^ d)⁻¹ * degreeFactor a⁻¹ z := by
  rw [sub_eq_add_neg, degreeFactor_add, degreeFactor_neg, degreeFactor_nat a ha,
    degreeFactor_neg, degreeFactor_inv]

theorem schwartz_scaling :
    Specs.ExpandedFA.PartIV.HomogeneousFourier.schwartzScalingType := by
  intro d a ha φ
  ext ξ
  simp only [smul_apply, schwartzScale_apply]
  rw [schwartz_integral, schwartz_integral]
  unfold integralFourier
  let g : Euclidean d → ℂ := fun y =>
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (inner ℝ y (a⁻¹ • ξ) : ℝ)) * φ y
  have hc : ∀ x : Euclidean d,
      g (a • x) = Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (inner ℝ x ξ : ℝ)) * schwartzScale a ha.ne' φ x := by
    intro x
    dsimp [g]
    rw [real_inner_smul_left, real_inner_smul_right]
    simp [mul_assoc, ha.ne']
  simp_rw [← hc]
  have h := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Euclidean d)) g a (hR := ha.le)
  simpa only [Euclidean, finrank_euclideanSpace_fin, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, smul_eq_mul] using h

theorem fourier_degree :
    Specs.ExpandedFA.PartIV.HomogeneousFourier.fourierDegreeType := by
  intro d z u hu a ha φ
  change ((a : ℂ) ^ d)⁻¹ *
    u (schwartzFourier (schwartzScale a⁻¹ (inv_ne_zero ha.ne') φ)) =
      degreeFactor a (-(d : ℂ) - z) * u (schwartzFourier φ)
  rw [schwartz_scaling d a⁻¹ (inv_pos.mpr ha) φ]
  simp only [map_smul, smul_eq_mul]
  rw [hu a⁻¹ (inv_pos.mpr ha) (schwartzFourier φ), degreeFactor_fourier d a ha z]
  exact (mul_assoc _ _ _).symm

/-- An extension with the Schwartz dilation law restricts to exactly the original
compact-test dilation law. -/
theorem homogeneous_of_extension {d : ℕ} {z : ℂ} {u : Distribution d}
    {v : Tempered ℂ d} (hv : Extends v u) (h : IsTemperedHomogeneous v z) :
    IsHomogeneous u z := by
  intro a ha φ
  rw [← hv, ← hv, testToSchwartz_scale]
  exact h a ha (testToSchwartz φ)

/-- Smoothness concerns precisely the restriction to compact tests. -/
theorem smoothAwayZero_extension {d : ℕ} {u : Distribution d} {v : Tempered ℂ d}
    (hv : Extends v u) : SmoothAwayZero u ↔ TemperedSmoothAwayZero v := by
  have h : (fun φ : CompactTests d => v (testToSchwartz φ)) = u := funext hv
  simp only [TemperedSmoothAwayZero, h]

/-- Reflection transposed on the same complex-linear Schwartz dual. -/
def temperedReflect {d : ℕ} (v : Tempered ℂ d) : Tempered ℂ d :=
  v.comp (schwartzScale (-1) (by norm_num))

lemma tempered_fourier_square {d : ℕ} (v : Tempered ℂ d) :
    temperedFourier (temperedFourier v) = temperedReflect v := by
  ext φ
  change v (schwartzFourier (schwartzFourier φ)) =
    v (schwartzScale (-1) (by norm_num) φ)
  congr 1
  ext x
  simpa using Inversion.fourier_square d φ x

lemma smoothAwayZero_test_reflect {d : ℕ} {u : CompactTests d → ℂ}
    (h : SmoothAwayZero u) :
    SmoothAwayZero (fun φ => u (testScale (-1) (by norm_num) φ)) := by
  obtain ⟨k, hk, hku⟩ := h
  refine ⟨fun x => k (-x), hk.comp contDiffOn_id.neg ?_, ?_⟩
  · intro x hx
    simpa using hx
  · intro φ hφ
    have hψ : tsupport (testScale (-1) (by norm_num) φ) ⊆
        ({0}ᶜ : Set (Euclidean d)) := by
      intro x hx
      have hx' : -x ∈ tsupport φ := by
        have ht := tsupport_comp_subset_preimage (φ : Euclidean d → ℂ)
          (continuous_id.neg : Continuous (fun x : Euclidean d => -x))
        apply ht
        change x ∈ tsupport (fun y => φ ((-1 : ℝ) • y)) at hx
        simpa only [neg_smul, one_smul, Function.comp_def, Pi.neg_apply, id_eq] using hx
      have := hφ hx'
      simpa using this
    change u (testScale (-1) (by norm_num) φ) = _
    rw [hku _ hψ]
    simp only [testScale_apply, neg_smul, one_smul]
    have hi := integral_neg_eq_self (fun x : Euclidean d => k (-x) * φ x)
      (volume : Measure (Euclidean d))
    simpa only [neg_neg] using hi

lemma tempered_smooth_reflect {d : ℕ} {v : Tempered ℂ d}
    (h : TemperedSmoothAwayZero v) : TemperedSmoothAwayZero (temperedReflect v) := by
  have h' := smoothAwayZero_test_reflect h
  have he : (fun φ : CompactTests d => v (testToSchwartz
      (testScale (-1) (by norm_num) φ))) =
      (fun φ => temperedReflect v (testToSchwartz φ)) := by
    funext φ
    rw [testToSchwartz_scale]
    rfl
  simpa only [TemperedSmoothAwayZero, he] using h'

lemma tempered_reflect_reflect {d : ℕ} (v : Tempered ℂ d) :
    temperedReflect (temperedReflect v) = v := by
  ext φ
  change v (schwartzScale (-1) (by norm_num)
    (schwartzScale (-1) (by norm_num) φ)) = v φ
  congr 1
  ext x
  simp only [schwartzScale_apply, neg_smul, one_smul, neg_neg]

lemma tempered_smooth_reflect_iff {d : ℕ} (v : Tempered ℂ d) :
    TemperedSmoothAwayZero (temperedReflect v) ↔ TemperedSmoothAwayZero v := by
  constructor
  · intro h
    simpa only [tempered_reflect_reflect] using tempered_smooth_reflect h
  · exact tempered_smooth_reflect

/-- Inversion reduces the smoothness equivalence to its forward implication. -/
theorem smooth_away_zero_iff_of_forward
    (hforward : Specs.ExpandedFA.PartIV.HomogeneousFourier.smoothAwayZeroForwardType) :
    Specs.ExpandedFA.PartIV.HomogeneousFourier.smoothAwayZeroType := by
  intro d z v hv
  constructor
  · exact hforward d z v hv
  · intro h
    have h' := hforward d (-(d : ℂ) - z) (temperedFourier v)
      (fourier_degree d z v hv) h
    rw [tempered_fourier_square] at h'
    exact (tempered_smooth_reflect_iff v).mp h'

/-- The logical assembly uses only the genuine extension theorem and analytic
forward smoothness theorem, together with the proved scaling and inversion. -/
theorem homogeneous_fourier_of_extension_and_smoothness
    (hextension : Specs.ExpandedFA.PartIV.HomogeneousFourier.temperedExtensionType)
    (hsmooth : Specs.ExpandedFA.PartIV.HomogeneousFourier.smoothAwayZeroForwardType) :
    Specs.ExpandedFA.PartIV.HomogeneousFourier.homogeneousFourierType := by
  intro d z u hu
  obtain ⟨v, hvu, hv⟩ := hextension d z u hu
  refine ⟨v, hvu, hv, fourier_degree d z v hv, ?_⟩
  exact (smoothAwayZero_extension hvu).trans
    (smooth_away_zero_iff_of_forward hsmooth d z v hv)

/-- The compact-test inclusion is complex-linear and injective. -/
def testToSchwartzLM {d : ℕ} : CompactTests d →ₗ[ℂ] Schwartz ℂ d where
  toFun := testToSchwartz
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

lemma testToSchwartz_injective {d : ℕ} :
    Function.Injective (testToSchwartz (d := d)) := by
  intro φ ψ h
  ext x
  exact congrArg (fun f : Schwartz ℂ d => f x) h

/-- Fixed-support smooth tests continuously include into Schwartz space. -/
def supportedToSchwartzCLM {d : ℕ} (K : TopologicalSpace.Compacts (Euclidean d)) :
    ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K →L[ℂ] Schwartz ℂ d := by
  let T : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K →ₗ[ℂ] Schwartz ℂ d :=
    { toFun φ := φ.hasCompactSupport.toSchwartzMap (φ.contDiff.of_le (by simp))
      map_add' _ _ := by ext; rfl
      map_smul' _ _ := by ext; rfl }
  refine ⟨T, ?_⟩
  apply (schwartz_withSeminorms ℂ (Euclidean d) ℂ).continuous_of_continuous_comp T
  rintro ⟨k, n⟩
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.exists_norm_le
  let C : ℝ≥0 := ⟨max R 0, le_max_right _ _⟩
  let q := C ^ k • ContDiffMapSupportedIn.seminorm ℂ (Euclidean d) ℂ ⊤ K n
  have hq : Continuous q := by
    exact continuous_const.smul
      ((ContDiffMapSupportedIn.withSeminorms ℂ (Euclidean d) ℂ ⊤ K).continuous_seminorm n)
  apply Seminorm.continuous_of_le hq
  intro φ
  apply SchwartzMap.seminorm_le_bound ℂ k n (T φ) (apply_nonneg q φ)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n φ x‖ ≤ q φ
  by_cases hx : x ∈ (K : Set (Euclidean d))
  · change _ ≤ (C : ℝ)^k * ContDiffMapSupportedIn.seminorm ℂ (Euclidean d) ℂ ⊤ K n φ
    exact mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) ((hR x hx).trans (le_max_left R 0)) k)
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ)
      (norm_nonneg _) (by positivity)
  · simp only [φ.iteratedFDeriv_zero_on_compl hx, Pi.zero_apply, norm_zero, mul_zero]
    exact apply_nonneg q φ

/-- The actual LF compact-test inclusion, with its continuity established on
every fixed-support space. -/
def testToSchwartzCLM {d : ℕ} : CompactTests d →L[ℂ] Schwartz ℂ d :=
  TestFunction.limitCLM ℂ testToSchwartz (fun K _ => supportedToSchwartzCLM K)
    (fun _ _ _ => by ext; rfl)

@[simp] lemma testToSchwartzCLM_apply {d : ℕ} (φ : CompactTests d) :
    testToSchwartzCLM φ = testToSchwartz φ := rfl

/-- Restriction along the actual continuous compact-test inclusion. -/
def restrictTempered {d : ℕ} (v : Tempered ℂ d) : Distribution d :=
  v.comp testToSchwartzCLM

@[simp] lemma restrictTempered_apply {d : ℕ} (v : Tempered ℂ d) (φ : CompactTests d) :
    restrictTempered v φ = v (testToSchwartz φ) := rfl

lemma restrictTempered_homogeneous {d : ℕ} {z : ℂ} {v : Tempered ℂ d}
    (hv : IsTemperedHomogeneous v z) : IsHomogeneous (restrictTempered v) z := by
  intro a ha φ
  simpa only [restrictTempered_apply, testToSchwartz_scale] using hv a ha (testToSchwartz φ)


/-- The ordinary L1 Fourier integral satisfies the scalar-linear transpose pairing. -/
theorem integralFourier_pairing {d : ℕ} {f g : Euclidean d → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, integralFourier f ξ * g ξ) = ∫ x, f x * integralFourier g x := by
  simp_rw [integralFourier_eq_native]
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ (Euclidean d))
    Real.continuous_fourierChar continuous_inner hf hg

/-- An integrable regular tempered distribution has the usual Fourier kernel
on every compact test. The representative premise is on all Schwartz tests. -/
theorem temperedFourier_pairing_of_integrable {d : ℕ} {v : Tempered ℂ d}
    {f : Euclidean d → ℂ} (hf : Integrable f)
    (hfv : ∀ ψ : Schwartz ℂ d, v ψ = ∫ x, f x * ψ x) (φ : CompactTests d) :
    temperedFourier v (testToSchwartz φ) = ∫ ξ, integralFourier f ξ * φ ξ := by
  change v (schwartzFourier (testToSchwartz φ)) = _
  rw [hfv]
  simp_rw [schwartz_integral d (testToSchwartz φ)]
  exact (integralFourier_pairing hf (testToSchwartz φ).integrable).symm

/-- Fourier smoothness with exactly the norm-moment hypotheses of Mathlib. -/
theorem contDiff_integralFourier {d : ℕ} {f : Euclidean d → ℂ} {N : ℕ∞}
    (hf : ∀ n : ℕ, n ≤ N → Integrable (fun x => ‖x‖ ^ n * ‖f x‖)) :
    ContDiff ℝ N (integralFourier f) := by
  have h : integralFourier f = 𝓕 f := funext (integralFourier_eq_native f)
  rw [h]
  exact Real.contDiff_fourier hf


/-- A continuous Schwartz seminorm bound suffices to extend a distribution.
This uses complex Hahn--Banach on the actual image of the compact tests. -/
theorem exists_tempered_extension_of_bound {d : ℕ} (u : Distribution d)
    (p : Seminorm ℂ (Schwartz ℂ d)) (hp : Continuous p)
    (hbound : ∀ φ : CompactTests d, ‖u φ‖ ≤ p (testToSchwartz φ)) :
    ∃ v : Tempered ℂ d, Extends v u ∧ ∀ φ, ‖v φ‖ ≤ p φ := by
  let := (schwartz_withSeminorms ℂ (Euclidean d) ℂ).toPolynormableSpace
  let e := LinearEquiv.ofInjective (testToSchwartzLM (d := d)) testToSchwartz_injective
  let f := u.toLinearMap.comp e.symm.toLinearMap
  have hf : ∀ x : (testToSchwartzLM (d := d)).range, ‖f x‖ ≤ p x := by
    intro x
    convert hbound (e.symm x) using 1
    exact congrArg (fun y : (testToSchwartzLM (d := d)).range => p y) (e.apply_symm_apply x).symm
  obtain ⟨v, hv, hnorm⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm _ f hp hf
  refine ⟨v, ?_, hnorm⟩
  intro φ
  have h := hv (e φ)
  change v (testToSchwartz φ) = f (e φ) at h
  simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, ContinuousLinearMap.coe_coe] using h

/-- Native finite-order bound on a fixed compact set in the same Euclidean model
as the Fourier transform; no coordinate-model identification is assumed. -/
theorem distribution_fixed_compact_bound {d : ℕ} (u : Distribution d)
    (K : TopologicalSpace.Compacts (Euclidean d)) :
    ∃ (s : Finset ℕ) (C : ℝ≥0), C ≠ 0 ∧
      ∀ φ : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K,
        ‖u (TestFunction.ofSupportedIn (Set.subset_univ _) φ)‖ ≤
          C * s.sup (ContDiffMapSupportedIn.seminorm ℂ (Euclidean d) ℂ ⊤ K) φ := by
  let T := u.comp (TestFunction.ofSupportedInCLM ℂ (Set.subset_univ (K : Set (Euclidean d))))
  exact Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℂ (Euclidean d) ℂ ⊤ K)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) T.continuous.norm

/-- A Schwartz operator whose range has a common compact support also takes
values continuously in the native fixed-support test space. -/
def schwartzToSupportedCLM {d : ℕ} (K : TopologicalSpace.Compacts (Euclidean d))
    (A : Schwartz ℂ d →L[ℂ] Schwartz ℂ d)
    (hA : ∀ φ, tsupport (A φ) ⊆ (K : Set (Euclidean d))) :
    Schwartz ℂ d →L[ℂ] ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K := by
  let T : Schwartz ℂ d →ₗ[ℂ] ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K :=
    { toFun φ := ContDiffMapSupportedIn.of_support_subset
        ((A φ).smooth ⊤) (Set.Subset.trans subset_closure (hA φ))
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  refine ⟨T, ?_⟩
  apply (ContDiffMapSupportedIn.withSeminorms ℂ (Euclidean d) ℂ ⊤ K).continuous_of_continuous_comp T
  intro n
  have hq : Continuous ((SchwartzMap.seminorm ℂ 0 n).comp A.toLinearMap) :=
    ((schwartz_withSeminorms ℂ (Euclidean d) ℂ).continuous_seminorm (0, n)).comp A.continuous
  apply Seminorm.continuous_of_le hq
  intro φ
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg _ _) n (T φ)).2
  intro x _
  exact (A φ).norm_iteratedFDeriv_le_seminorm ℂ n x

/-- Multiplication by one fixed compact smooth cutoff sends Schwartz tests
continuously into the LF test space. -/
def cutoffToTestsCLM {d : ℕ} (χ : CompactTests d) :
    Schwartz ℂ d →L[ℂ] CompactTests d :=
  let K : TopologicalSpace.Compacts (Euclidean d) := ⟨tsupport χ, χ.hasCompactSupport⟩
  let A := SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ)
  (TestFunction.ofSupportedInCLM ℂ (Set.subset_univ (K : Set (Euclidean d)))).comp
    (schwartzToSupportedCLM K A (fun φ =>
      (SchwartzMap.tsupport_smulLeftCLM_subset _ φ).trans Set.inter_subset_right))

@[simp] lemma cutoffToTestsCLM_apply {d : ℕ} (χ : CompactTests d)
    (φ : Schwartz ℂ d) (x : Euclidean d) : cutoffToTestsCLM χ φ x = χ x * φ x := by
  have hχ : (χ : Euclidean d → ℂ).HasTemperateGrowth :=
    (testToSchwartz χ).hasTemperateGrowth
  convert (SchwartzMap.smulLeftCLM_apply_apply hχ φ x) using 1
  with_unfolding_all rfl

/-- The compactly localized part of any LF distribution is tempered. -/
def localizedTempered {d : ℕ} (u : Distribution d) (χ : CompactTests d) : Tempered ℂ d :=
  u.comp (cutoffToTestsCLM χ)

@[simp] theorem localizedTempered_apply {d : ℕ} (u : Distribution d) (χ : CompactTests d)
    (φ : Schwartz ℂ d) : localizedTempered u χ φ = u (cutoffToTestsCLM χ φ) := rfl


lemma cutoff_derivative_bound {d : ℕ} (χ : Schwartz ℂ d) (hχ : χ 0 = 1)
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha₁ : a ≤ 1) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y => χ (a • y) - 1) x‖ ≤
      a * (SchwartzMap.seminorm ℂ 0 1 χ + SchwartzMap.seminorm ℂ 0 n χ) * (1 + ‖x‖) := by
  by_cases hn : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero]
    have hLip : LipschitzWith ⟨SchwartzMap.seminorm ℂ 0 1 χ, apply_nonneg _ _⟩ χ := by
      apply lipschitzWith_of_nnnorm_fderiv_le ((χ.smooth 1).differentiable (by norm_num))
      intro y
      change ‖fderiv ℝ χ y‖ ≤ _
      rw [← norm_iteratedFDeriv_one]
      exact χ.norm_iteratedFDeriv_le_seminorm ℂ 1 y
    have h := hLip.norm_sub_le (a • x) 0
    rw [hχ, sub_zero, norm_smul, Real.norm_of_nonneg ha] at h
    calc
      _ ≤ SchwartzMap.seminorm ℂ 0 1 χ * (a * ‖x‖) := h
      _ ≤ a * (SchwartzMap.seminorm ℂ 0 1 χ + SchwartzMap.seminorm ℂ 0 0 χ) * (1 + ‖x‖) := by
        calc
          _ = a * SchwartzMap.seminorm ℂ 0 1 χ * ‖x‖ := by ring
          _ ≤ _ := by gcongr <;> linarith [apply_nonneg (SchwartzMap.seminorm ℂ 0 0) χ, apply_nonneg (SchwartzMap.seminorm ℂ 0 1) χ, norm_nonneg x]
  · have hs : ContDiff ℝ n (fun y : Euclidean d => χ (a • y)) :=
      (χ.smooth n).comp (by fun_prop)
    change ‖iteratedFDeriv ℝ n ((fun y => χ (a • y)) - (fun _ => (1 : ℂ))) x‖ ≤ _
    rw [iteratedFDeriv_sub hs contDiff_const, Pi.sub_apply,
      iteratedFDeriv_const_of_ne hn, Pi.zero_apply, sub_zero,
      iteratedFDeriv_comp_const_smul a (χ.smooth n)]
    simp only [norm_smul, Real.norm_of_nonneg (pow_nonneg ha n)]
    have hpow : a ^ n ≤ a := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha ha₁) ha).trans_eq (one_mul a)
    calc
      _ ≤ a * SchwartzMap.seminorm ℂ 0 n χ :=
        mul_le_mul hpow (χ.norm_iteratedFDeriv_le_seminorm ℂ n _) (norm_nonneg _) ha
      _ ≤ a * (SchwartzMap.seminorm ℂ 0 1 χ + SchwartzMap.seminorm ℂ 0 n χ) * (1 + ‖x‖) := by
        calc
          _ = a * SchwartzMap.seminorm ℂ 0 n χ * 1 := by ring
          _ ≤ _ := by gcongr <;> linarith [apply_nonneg (SchwartzMap.seminorm ℂ 0 0) χ, apply_nonneg (SchwartzMap.seminorm ℂ 0 1) χ, norm_nonneg x]

/-- A bound with one extra weight controls the linear growth of the cutoff error. -/
lemma weighted_derivative_one_add_bound {d : ℕ} (φ : Schwartz ℂ d) (k i : ℕ)
    (x : Euclidean d) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ i φ x‖ * (1 + ‖x‖) ≤
      SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ (k + 1) i φ := by
  calc
    _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ i φ x‖ +
      ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ i φ x‖ := by rw [pow_succ]; ring
    _ ≤ _ := add_le_add (φ.le_seminorm ℂ k i x) (φ.le_seminorm ℂ (k+1) i x)

/-- The cutoff approximation error has a bound linear in its scale. -/
lemma cutoff_seminorm_bound {d : ℕ} (χ : CompactTests d) (hχ : χ 0 = 1)
    (φ : Schwartz ℂ d) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      SchwartzMap.seminorm ℂ k n
        (testToSchwartz (cutoffToTestsCLM (testScale a ha.ne' χ) φ) - φ) ≤ a * C := by
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℂ 0 1 (testToSchwartz χ) +
      SchwartzMap.seminorm ℂ 0 (n-i) (testToSchwartz χ)) *
    (SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ (k+1) i φ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun a ha ha₁ => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg ha.le hC)
  intro x
  have heq : (⇑(testToSchwartz (cutoffToTestsCLM (testScale a ha.ne' χ) φ) - φ) :
      Euclidean d → ℂ) = fun y => φ y * (χ (a • y) - 1) := by
    ext y
    simp only [sub_apply, testToSchwartz_apply, cutoffToTestsCLM_apply, testScale_apply]
    ring
  rw [heq]
  have hs : ContDiff ℝ ∞ (fun y : Euclidean d => χ (a • y) - 1) :=
    (χ.contDiff.of_le (by simp)).comp (by fun_prop) |>.sub contDiff_const
  calc
    _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i φ x‖ *
        ‖iteratedFDeriv ℝ (n-i) (fun y => χ (a • y) - 1) x‖ := by
      gcongr
      exact norm_iteratedFDeriv_mul_le (φ.smooth ⊤) hs x (mod_cast le_top)
    _ ≤ a * C := by
      rw [Finset.mul_sum]
      dsimp [C]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      let D := SchwartzMap.seminorm ℂ 0 1 (testToSchwartz χ) +
        SchwartzMap.seminorm ℂ 0 (n-i) (testToSchwartz χ)
      have hD : 0 ≤ D := by dsimp [D]; positivity
      calc
        _ ≤ ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ x‖ *
            (a * D * (1 + ‖x‖))) := by
          gcongr
          exact cutoff_derivative_bound (testToSchwartz χ) hχ (n-i) a ha.le ha₁ x
        _ = a * (n.choose i : ℝ) * D *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ i φ x‖ * (1 + ‖x‖)) := by ring
        _ ≤ a * (n.choose i : ℝ) * D *
            (SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ (k+1) i φ) := by
          gcongr
          exact weighted_derivative_one_add_bound φ k i x
        _ = _ := by ring

/-- Scaled compact cutoffs approximate every Schwartz test in its actual topology. -/
theorem cutoff_approximation {d : ℕ} (χ : CompactTests d) (hχ : χ 0 = 1)
    (φ : Schwartz ℂ d) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (hε₁ : ∀ j, ε j ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => testToSchwartz
      (cutoffToTestsCLM (testScale (ε j) (hε j).ne' χ) φ)) atTop (𝓝 φ) := by
  rw [(schwartz_withSeminorms ℂ (Euclidean d) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ δ hδ
  obtain ⟨C, hC, hbound⟩ := cutoff_seminorm_bound χ hχ φ k n
  have hlim : Tendsto (fun j => ε j * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using hεlim.mul_const C
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with j hj
  exact (hbound (ε j) (hε j) (hε₁ j)).trans_lt hj

set_option maxHeartbeats 800000 in
lemma exists_test_one_at_zero (d : ℕ) : ∃ χ : CompactTests d, χ 0 = 1 := by
  obtain ⟨f, _, hf, hs, _, hf0⟩ := exists_contDiff_tsupport_subset
    (E := Euclidean d) (n := ⊤) (x := 0) (s := Set.univ) (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : Euclidean d))
  refine ⟨{ toFun := fun x => (f x : ℂ)
            contDiff' := Complex.ofRealCLM.contDiff.comp hs
            hasCompactSupport' := by
              simpa only [Function.comp_def] using hf.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
            tsupport_subset' := Set.subset_univ _ }, ?_⟩
  change (f 0 : ℂ) = 1
  simp [hf0]

/-- Compact smooth tests are dense in the same Schwartz space used by the
accepted Fourier convention. This is density in every Schwartz seminorm. -/
theorem denseRange_testToSchwartz (d : ℕ) :
    DenseRange (testToSchwartz (d := d)) := by
  obtain ⟨χ, hχ⟩ := exists_test_one_at_zero d
  intro φ
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε : ∀ j, 0 < ε j := by intro j; dsimp [ε]; positivity
  have hε₁ : ∀ j, ε j ≤ 1 := by
    intro j
    dsimp [ε]
    apply (div_le_one (by positivity)).2
    linarith [Nat.cast_nonneg (α := ℝ) j]
  apply mem_closure_of_tendsto
    (cutoff_approximation χ hχ φ ε hε hε₁ tendsto_one_div_add_atTop_nhds_zero_nat)
  exact Eventually.of_forall (fun j => ⟨_, rfl⟩)

/-- Tempered extensions are unique, because they agree on the dense compact tests. -/
theorem tempered_extension_unique {d : ℕ} {u : Distribution d} {v w : Tempered ℂ d}
    (hv : Extends v u) (hw : Extends w u) : v = w := by
  apply DFunLike.ext'
  apply (denseRange_testToSchwartz d).equalizer v.continuous w.continuous
  funext φ
  exact (hv φ).trans (hw φ).symm

/-- Any continuous extension inherits the dilation law, by compact-test density. -/
theorem temperedHomogeneous_of_extension {d : ℕ} {z : ℂ} {u : Distribution d}
    {v : Tempered ℂ d} (hu : IsHomogeneous u z) (hv : Extends v u) :
    IsTemperedHomogeneous v z := by
  intro a ha
  have heq := (denseRange_testToSchwartz d).equalizer
    (g := fun φ : Schwartz ℂ d => ((a : ℂ) ^ d)⁻¹ *
      v (schwartzScale a⁻¹ (inv_ne_zero ha.ne') φ))
    (h := fun φ : Schwartz ℂ d => degreeFactor a z * v φ)
    (continuous_const.mul (v.continuous.comp (schwartzScale a⁻¹ (inv_ne_zero ha.ne')).continuous))
    (continuous_const.mul v.continuous) ?_
  · exact congrFun heq
  · funext φ
    simp only [Function.comp_apply, ← testToSchwartz_scale]
    rw [hv _, hv _]
    exact hu a ha φ

/-- Only the global Schwartz seminorm estimate remains in the extension problem. -/
theorem tempered_extension_of_bound {d : ℕ} {z : ℂ} (u : Distribution d)
    (hu : IsHomogeneous u z) (p : Seminorm ℂ (Schwartz ℂ d)) (hp : Continuous p)
    (hbound : ∀ φ : CompactTests d, ‖u φ‖ ≤ p (testToSchwartz φ)) :
    ∃ v : Tempered ℂ d, Extends v u ∧ IsTemperedHomogeneous v z := by
  obtain ⟨v, hv, _⟩ := exists_tempered_extension_of_bound u p hp hbound
  exact ⟨v, hv, temperedHomogeneous_of_extension hu hv⟩


set_option maxHeartbeats 800000 in
/-- Continuous integral representatives on an open set are unique pointwise. -/
theorem continuous_representative_unique {d : ℕ} {U : Set (Euclidean d)}
    (hU : IsOpen U) {k l : Euclidean d → ℂ}
    (hk : ContinuousOn k U) (hl : ContinuousOn l U)
    (hpair : ∀ φ : CompactTests d, tsupport φ ⊆ U →
      (∫ x, k x * φ x) = ∫ x, l x * φ x) : Set.EqOn k l U := by
  have hkint : LocallyIntegrableOn k U volume := hk.locallyIntegrableOn hU.measurableSet
  have hlint : LocallyIntegrableOn l U volume := hl.locallyIntegrableOn hU.measurableSet
  have hae : ∀ᵐ x ∂(volume : Measure (Euclidean d)), x ∈ U → (k - l) x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hkint.sub hlint)
    intro g hg hgc hgs
    let φ : CompactTests d :=
      { toFun := fun x => (g x : ℂ)
        contDiff' := Complex.ofRealCLM.contDiff.comp (hg.of_le (by simp))
        hasCompactSupport' := hgc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
        tsupport_subset' := Set.subset_univ _ }
    let ψ : TestFunction ⟨U, hU⟩ ℝ ⊤ :=
      ⟨g, hg.of_le (by simp), hgc, hgs⟩
    have hφ : tsupport φ ⊆ U := by
      apply Set.Subset.trans (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) (by simp) g) hgs
    have he := hpair φ hφ
    have hki := ψ.integrable_smul hkint
    have hli := ψ.integrable_smul hlint
    change Integrable (fun x => g x • k x) _ at hki
    change Integrable (fun x => g x • l x) _ at hli
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hki hli]
    apply sub_eq_zero.mpr
    change (∫ x, k x * (g x : ℂ)) = ∫ x, l x * (g x : ℂ) at he
    simpa only [Complex.real_smul, mul_comm] using he
  have haeeq : k =ᵐ[volume.restrict U] l := by
    change ∀ᵐ x ∂volume.restrict U, k x = l x
    apply (ae_restrict_iff' hU.measurableSet).2
    filter_upwards [hae] with x hx hxu
    exact sub_eq_zero.mp (hx hxu)
  exact Measure.eqOn_open_of_ae_eq haeeq hU hk hl

lemma testScale_tsupport_subset {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (φ : CompactTests d) :
    tsupport (testScale a ha φ) ⊆ (fun x : Euclidean d => a • x) ⁻¹' tsupport φ := by
  exact tsupport_comp_subset_preimage (φ : Euclidean d → ℂ)
    (continuous_id.const_smul a)

lemma testScale_tsupport_away_zero {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (φ : CompactTests d) (hφ : tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d))) :
    tsupport (testScale a ha φ) ⊆ ({0}ᶜ : Set (Euclidean d)) := by
  intro x hx
  have hax := hφ (testScale_tsupport_subset a ha φ hx)
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_zero, ha, false_or] using hax

lemma integral_dilate_pairing {d : ℕ} (a : ℝ) (ha : 0 < a)
    (k : Euclidean d → ℂ) (φ : CompactTests d) :
    (∫ x, k (a • x) * φ x) = ((a : ℂ) ^ d)⁻¹ *
      ∫ x, k x * testScale a⁻¹ (inv_ne_zero ha.ne') φ x := by
  let g : Euclidean d → ℂ := fun y => k y * φ (a⁻¹ • y)
  have hg : ∀ x, g (a • x) = k (a • x) * φ x := by
    intro x
    simp [g, smul_smul, ha.ne']
  simp_rw [← hg]
  have h := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Euclidean d)) g a (hR := ha.le)
  simpa only [Euclidean, finrank_euclideanSpace_fin, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, smul_eq_mul, g, testScale_apply] using h

/-- Homogeneity of a distribution forces the ordinary homogeneity of its
continuous representative on the punctured space. -/
theorem representative_homogeneous {d : ℕ} {z : ℂ} {u : Distribution d}
    (hu : IsHomogeneous u z) {k : Euclidean d → ℂ}
    (hk : ContinuousOn k ({0}ᶜ : Set (Euclidean d)))
    (hku : ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      u φ = ∫ x, k x * φ x) :
    ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      k (a • x) = degreeFactor a z * k x := by
  intro a ha
  have hmap : Set.MapsTo (fun x : Euclidean d => a • x) {0}ᶜ {0}ᶜ := by
    intro x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_zero, ha.ne', false_or] using hx
  have heq := continuous_representative_unique
    (d := d) (U := ({0}ᶜ : Set (Euclidean d)))
    (k := fun x => k (a • x)) (l := fun x => degreeFactor a z * k x)
    isClosed_singleton.isOpen_compl
    (hk.comp (continuous_id.const_smul a).continuousOn hmap)
    (continuousOn_const.mul hk) ?_
  · intro x hx
    exact heq (by simpa using hx)
  · intro φ hφ
    rw [integral_dilate_pairing a ha k φ]
    have h := hu a ha φ
    rw [hku _ (testScale_tsupport_away_zero a⁻¹ (inv_ne_zero ha.ne') φ hφ),
      hku _ hφ] at h
    convert h using 1
    rw [← integral_const_mul]
    congr 1
    ext x
    ring


/-- Pointwise homogeneity for the actual punctured representative of a tempered distribution. -/
theorem tempered_representative_homogeneous {d : ℕ} {z : ℂ} {v : Tempered ℂ d}
    (hv : IsTemperedHomogeneous v z) {k : Euclidean d → ℂ}
    (hk : ContinuousOn k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz φ) = ∫ x, k x * φ x) :
    ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      k (a • x) = degreeFactor a z * k x := by
  intro a ha
  have hmap : Set.MapsTo (fun x : Euclidean d => a • x) {0}ᶜ {0}ᶜ := by
    intro x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_zero, ha.ne', false_or] using hx
  have heq := continuous_representative_unique
    (d := d) (U := ({0}ᶜ : Set (Euclidean d)))
    (k := fun x => k (a • x)) (l := fun x => degreeFactor a z * k x)
    isClosed_singleton.isOpen_compl
    (hk.comp (continuous_id.const_smul a).continuousOn hmap)
    (continuousOn_const.mul hk) ?_
  · intro x hx
    exact heq (by simpa using hx)
  · intro φ hφ
    rw [integral_dilate_pairing a ha k φ]
    have h := hv a ha (testToSchwartz φ)
    rw [← testToSchwartz_scale,
      hkv _ (testScale_tsupport_away_zero a⁻¹ (inv_ne_zero ha.ne') φ hφ),
      hkv _ hφ] at h
    convert h using 1
    rw [← integral_const_mul]
    congr 1
    ext x
    ring


def originCutoff (d : ℕ) : CompactTests d :=
  let b : ContDiffBump (0 : Euclidean d) :=
    { rIn := 2, rOut := 4, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  { toFun := fun x => (b x : ℂ)
    contDiff' := Complex.ofRealCLM.contDiff.comp b.contDiff
    hasCompactSupport' := b.hasCompactSupport.comp_left
      (g := fun t : ℝ => (t : ℂ)) (by simp)
    tsupport_subset' := Set.subset_univ _ }

lemma originCutoff_one {d : ℕ} (x : Euclidean d) (hx : ‖x‖ ≤ 2) :
    originCutoff d x = 1 := by
  let b : ContDiffBump (0 : Euclidean d) :=
    { rIn := 2
      rOut := 4
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  change (b x : ℂ) = 1
  have h : b x = 1 := b.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  rw [h]
  norm_num

lemma originCutoff_eventually_one (d : ℕ) :
    ∀ᶠ x in 𝓝 (0 : Euclidean d), originCutoff d x = 1 := by
  filter_upwards [Metric.ball_mem_nhds (0 : Euclidean d) (by norm_num : (0 : ℝ) < 2)] with x hx
  exact originCutoff_one x (by
    have h : ‖x‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact h.le)

def annularCutoff (d : ℕ) : CompactTests d :=
  testScale (1/2) (by norm_num) (originCutoff d) - originCutoff d

@[simp] lemma annularCutoff_apply {d : ℕ} (x : Euclidean d) :
    annularCutoff d x = originCutoff d ((1/2 : ℝ) • x) - originCutoff d x := rfl

lemma annularCutoff_vanishes {d : ℕ} (x : Euclidean d) (hx : ‖x‖ ≤ 2) :
    annularCutoff d x = 0 := by
  rw [annularCutoff_apply, originCutoff_one x hx, originCutoff_one]
  · exact sub_self _
  · rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
    linarith [norm_nonneg x]

lemma annularCutoff_support {d : ℕ} :
    tsupport (annularCutoff d) ⊆ {x : Euclidean d | 1 ≤ ‖x‖} := by
  apply closure_minimal
  · intro x hx
    by_contra h
    have hx' : ‖x‖ ≤ 2 := by simp only [Set.mem_ofPred_eq, not_le] at h; linarith
    exact hx (annularCutoff_vanishes x hx')
  · exact isClosed_le continuous_const continuous_norm


lemma dyadic_cutoff_telescope (d n : ℕ) (x : Euclidean d) :
    originCutoff d x + ∑ j ∈ Finset.range n,
      annularCutoff d (((2 : ℝ)⁻¹ ^ j) • x) =
        originCutoff d (((2 : ℝ)⁻¹ ^ n) • x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, annularCutoff_apply]
    have h : (1/2 : ℝ) • (((2 : ℝ)⁻¹ ^ n) • x) = ((2 : ℝ)⁻¹ ^ (n+1)) • x := by
      rw [smul_smul, pow_succ]
      congr 1
      norm_num
      ring
    rw [h]
    ring

lemma dyadic_cutoff_pairing_telescope {d : ℕ} (v : Tempered ℂ d)
    (ψ : Schwartz ℂ d) (n : ℕ) :
    v (testToSchwartz
      (cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ n) (by positivity) (originCutoff d)) ψ)) =
    v (testToSchwartz (cutoffToTestsCLM (originCutoff d) ψ)) +
      ∑ j ∈ Finset.range n, v (testToSchwartz
        (cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ j) (by positivity) (annularCutoff d)) ψ)) := by
  have he : testToSchwartz
      (cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ n) (by positivity) (originCutoff d)) ψ) =
      testToSchwartz (cutoffToTestsCLM (originCutoff d) ψ) +
      ∑ j ∈ Finset.range n, testToSchwartz
        (cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ j) (by positivity) (annularCutoff d)) ψ) := by
    ext x
    simp only [testToSchwartz_apply, cutoffToTestsCLM_apply, testScale_apply, add_apply, sum_apply]
    rw [← Finset.sum_mul, ← add_mul, dyadic_cutoff_telescope]
  rw [he, map_add, map_sum]

/-- Finite dyadic annular pairings converge to the actual exterior part of any
tempered distribution, by convergence in the full Schwartz topology. -/
theorem tendsto_dyadic_exterior_pairing {d : ℕ} (v : Tempered ℂ d) (ψ : Schwartz ℂ d) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, v (testToSchwartz
      (cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ j) (by positivity) (annularCutoff d)) ψ)))
      atTop (𝓝 (v ψ - v (testToSchwartz (cutoffToTestsCLM (originCutoff d) ψ)))) := by
  have hχ : originCutoff d (0 : Euclidean d) = 1 := originCutoff_one _ (by simp)
  have hpos : ∀ j : ℕ, 0 < (2 : ℝ)⁻¹ ^ j := fun _ => by positivity
  have hone : ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ 1 := fun j =>
    pow_le_one₀ (by norm_num) (by norm_num)
  have hlim := cutoff_approximation (originCutoff d) hχ ψ
    (fun j => (2 : ℝ)⁻¹ ^ j) hpos hone
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hv := (v.continuous.tendsto ψ).comp hlim
  have ht := hv.sub_const (v (testToSchwartz (cutoffToTestsCLM (originCutoff d) ψ)))
  convert ht using 1
  ext n
  simp only [Function.comp_apply]
  rw [dyadic_cutoff_pairing_telescope]
  ring


/-- Each compact test has a sufficiently large dyadic cutoff equal to one on
its support; there is no bound on the required scale uniform in the test. -/
lemma exists_dyadic_cutoff_eq_one {d : ℕ} (φ : CompactTests d) :
    ∃ n : ℕ, ∀ x ∈ tsupport φ,
      originCutoff d (((2 : ℝ)⁻¹ ^ n) • x) = 1 := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isBounded.exists_norm_le
  have hlim : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n) * R) atTop (𝓝 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_const R using 1
    simp
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2))).exists
  refine ⟨n, fun x hx => originCutoff_one _ ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) n)]
  exact (mul_le_mul_of_nonneg_left (hR x hx) (by positivity)).trans hn.le

lemma testToSchwartz_cutoff_telescope {d : ℕ} (φ : CompactTests d) (n : ℕ) :
    cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ n) (by positivity) (originCutoff d))
      (testToSchwartz φ) =
    cutoffToTestsCLM (originCutoff d) (testToSchwartz φ) +
      ∑ j ∈ Finset.range n,
        cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ j) (by positivity) (annularCutoff d))
          (testToSchwartz φ) := by
  ext x
  simp only [cutoffToTestsCLM_apply, testScale_apply, testToSchwartz_apply,
    sum_apply, add_apply]
  rw [← Finset.sum_mul, ← add_mul, dyadic_cutoff_telescope]

lemma compact_test_dyadic_partition {d : ℕ} (φ : CompactTests d) :
    ∃ n : ℕ, φ = cutoffToTestsCLM (originCutoff d) (testToSchwartz φ) +
      ∑ j ∈ Finset.range n,
        cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ j) (by positivity) (annularCutoff d))
          (testToSchwartz φ) := by
  obtain ⟨n, hn⟩ := exists_dyadic_cutoff_eq_one φ
  refine ⟨n, ?_⟩
  rw [← testToSchwartz_cutoff_telescope]
  ext x
  simp only [cutoffToTestsCLM_apply, testScale_apply, testToSchwartz_apply]
  by_cases hx : φ x = 0
  · simp only [hx, mul_zero]
  · rw [hn x (subset_closure hx), one_mul]


lemma scaled_derivative_decay {d : ℕ} (φ : Schwartz ℂ d) (N i : ℕ)
    (R : ℝ) (hR : 0 ≤ R) (x : Euclidean d) (hx : 1 ≤ ‖x‖) :
    R ^ N * ‖iteratedFDeriv ℝ i φ (R • x)‖ ≤ SchwartzMap.seminorm ℂ N i φ := by
  calc
    _ ≤ ‖R • x‖ ^ N * ‖iteratedFDeriv ℝ i φ (R • x)‖ := by
      gcongr
      rw [norm_smul, Real.norm_of_nonneg hR]
      nlinarith
    _ ≤ _ := φ.le_seminorm ℂ N i (R • x)

lemma annular_cutoff_derivative_bound {d : ℕ} (η : CompactTests d)
    (φ : Schwartz ℂ d) (N n m : ℕ) (hnm : n ≤ m)
    (R : ℝ) (hR : 1 ≤ R) (x : Euclidean d) (hx : 1 ≤ ‖x‖) :
    R ^ N * ‖iteratedFDeriv ℝ n (fun y => η y * φ (R • y)) x‖ ≤
      R ^ m * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        SchwartzMap.seminorm ℂ 0 (n-i) (testToSchwartz η) *
        SchwartzMap.seminorm ℂ N i φ := by
  have hR0 : 0 ≤ R := (zero_le_one.trans hR)
  have hs : ContDiff ℝ ∞ (fun y : Euclidean d => φ (R • y)) :=
    (φ.smooth ⊤).comp (by fun_prop)
  calc
    _ ≤ R ^ N * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y => φ (R • y)) x‖ *
        ‖iteratedFDeriv ℝ (n-i) η x‖ := by
      have heq : (fun y : Euclidean d => η y * φ (R • y)) =
          (fun y => φ (R • y) * η y) := by ext y; exact mul_comm _ _
      rw [heq]
      gcongr
      exact norm_iteratedFDeriv_mul_le hs (η.contDiff.of_le (by simp)) x (mod_cast le_top)
    _ ≤ _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by simpa only [Finset.mem_range_succ_iff] using hi
      rw [iteratedFDeriv_comp_const_smul R (φ.smooth i), norm_smul,
        Real.norm_of_nonneg (pow_nonneg hR0 i)]
      calc
        _ = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ (n-i) η x‖ *
          R ^ i * (R ^ N * ‖iteratedFDeriv ℝ i φ (R • x)‖) := by ring
        _ ≤ (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 (n-i) (testToSchwartz η) *
          R ^ m * SchwartzMap.seminorm ℂ N i φ := by
          gcongr
          · exact (testToSchwartz η).norm_iteratedFDeriv_le_seminorm ℂ (n-i) x
          · exact hin.trans hnm
          · exact scaled_derivative_decay φ N i R hR0 x hx
        _ = _ := by ring

/-- Cutoff-localized rescalings have a uniform rapid-decay bound on one fixed
annulus, even when the original distribution has no smooth representative. -/
lemma distribution_annular_bound {d : ℕ} (u : Distribution d) (η : CompactTests d)
    (hη : ∀ x ∈ tsupport η, 1 ≤ ‖x‖) :
    ∃ m : ℕ, ∀ N : ℕ, ∃ p : Seminorm ℂ (Schwartz ℂ d), Continuous p ∧
      ∀ (R : ℝ) (hR : 1 ≤ R) (φ : Schwartz ℂ d),
        ‖u (cutoffToTestsCLM η (schwartzScale R (by linarith) φ))‖ ≤
          (R ^ m / R ^ N) * p φ := by
  let K : TopologicalSpace.Compacts (Euclidean d) := ⟨tsupport η, η.hasCompactSupport⟩
  obtain ⟨s, C, _, hbound⟩ := distribution_fixed_compact_bound u K
  refine ⟨s.sup id, fun N => ?_⟩
  let q : ℕ → Seminorm ℂ (Schwartz ℂ d) := fun n =>
    ∑ i ∈ Finset.range (n+1),
      (show NNReal from ⟨(n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 (n-i) (testToSchwartz η),
        by positivity⟩) • (SchwartzMap.seminorm ℂ N i : Seminorm ℂ (Schwartz ℂ d))
  let p : Seminorm ℂ (Schwartz ℂ d) := C • ∑ n ∈ s, q n
  have hq : ∀ n, Continuous (q n) := by
    intro n
    change Continuous (fun φ => q n φ)
    simp only [q, sum_apply]
    change Continuous (fun φ => ∑ i ∈ Finset.range (n+1),
      ((n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 (n-i) (testToSchwartz η)) *
        SchwartzMap.seminorm ℂ N i φ)
    apply continuous_finsetSum
    intro i hi
    exact continuous_const.mul
      ((schwartz_withSeminorms ℂ (Euclidean d) ℂ).continuous_seminorm (N, i))
  refine ⟨p, ?_, fun R hR φ => ?_⟩
  · change Continuous (fun φ => p φ)
    simp only [p, sum_apply, smul_apply, NNReal.smul_def, smul_eq_mul]
    change Continuous (fun φ => (C : ℝ) * ∑ n ∈ s, q n φ)
    exact continuous_const.mul (continuous_finsetSum _ (fun n hn => hq n))
  · have hsR : ContDiff ℝ ∞ (fun y : Euclidean d => φ (R • y)) :=
      (φ.smooth ⊤).comp (by fun_prop)
    let ψ : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K :=
      ContDiffMapSupportedIn.of_support_subset
        (η.contDiff.mul hsR)
        (by
          intro x hx
          apply subset_closure
          exact (mul_ne_zero_iff.mp hx).1)
    have hψ : TestFunction.ofSupportedIn (Set.subset_univ _) ψ =
        cutoffToTestsCLM η (schwartzScale R (by linarith) φ) := by
      ext x
      simp only [cutoffToTestsCLM_apply, schwartzScale_apply]
      rfl
    rw [← hψ]
    have hR0 : 0 ≤ R := zero_le_one.trans hR
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    have hratio : 0 ≤ R ^ s.sup id / R ^ N := by positivity
    calc
      _ ≤ C * s.sup (ContDiffMapSupportedIn.seminorm ℂ (Euclidean d) ℂ ⊤ K) ψ := hbound ψ
      _ ≤ C * ((R ^ s.sup id / R ^ N) * ∑ n ∈ s, q n φ) := by
        gcongr
        apply Seminorm.finset_sup_apply_le (mul_nonneg hratio (by positivity))
        intro n hn
        have hns : n ≤ s.sup id := Finset.le_sup (f := id) hn
        apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ
          (mul_nonneg hratio (by positivity)) n ψ).2
        intro x hx
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (pow_pos hRpos N)).2
        have hd := annular_cutoff_derivative_bound η φ N n (s.sup id) hns R hR x (hη x hx)
        have hqn : q n φ ≤ ∑ n ∈ s, q n φ :=
          Finset.single_le_sum (fun i hi => apply_nonneg (q i) φ) hn
        have hqeval : q n φ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            SchwartzMap.seminorm ℂ 0 (n-i) (testToSchwartz η) *
            SchwartzMap.seminorm ℂ N i φ := by
          dsimp [q]
          rw [sum_apply]
          rfl
        have hd' : ‖iteratedFDeriv ℝ n ψ x‖ * R ^ N ≤ R ^ s.sup id * q n φ := by
          change ‖iteratedFDeriv ℝ n (fun y => η y * φ (R • y)) x‖ * R ^ N ≤ _
          rw [hqeval, mul_comm _ (R ^ N)]
          exact hd
        calc
          _ ≤ R ^ s.sup id * q n φ := hd'
          _ ≤ R ^ s.sup id * ∑ n ∈ s, q n φ := mul_le_mul_of_nonneg_left hqn (pow_nonneg hR0 _)
      _ = (R ^ s.sup id / R ^ N) * p φ := by simp [p, sum_apply, NNReal.smul_def, smul_eq_mul, mul_left_comm]

lemma degreeFactor_pow (a : ℝ) (j : ℕ) (z : ℂ) :
    degreeFactor (a ^ j) z = degreeFactor a z ^ j := by
  unfold degreeFactor
  rw [Real.log_pow]
  have he : (((j : ℝ) * Real.log a : ℝ) : ℂ) * z = (j : ℂ) * ((Real.log a : ℂ) * z) := by
    push_cast
    ring
  rw [he, Complex.exp_nat_mul]

lemma homogeneous_testScale_inverse {d : ℕ} {z : ℂ} (u : Distribution d)
    (hu : IsHomogeneous u z) (a : ℝ) (ha : 0 < a) (φ : CompactTests d) :
    u (testScale a⁻¹ (inv_ne_zero ha.ne') φ) =
      (a : ℂ) ^ d * degreeFactor a z * u φ := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  calc
    _ = (a : ℂ)^d * (((a : ℂ)^d)⁻¹ * u (testScale a⁻¹ (inv_ne_zero ha.ne') φ)) := by
      simp [haC]
    _ = _ := by rw [hu a ha φ]; ring

lemma homogeneous_dyadic_norm {d : ℕ} {z : ℂ} (u : Distribution d)
    (hu : IsHomogeneous u z) (j : ℕ) (φ : CompactTests d) :
    ‖u (testScale ((2 : ℝ)⁻¹ ^ j) (pow_ne_zero j (by norm_num)) φ)‖ =
      ‖(2 : ℂ) ^ d * degreeFactor 2 z‖ ^ j * ‖u φ‖ := by
  have he : (2 : ℝ)⁻¹ ^ j = (2 ^ j)⁻¹ := inv_pow (2 : ℝ) j
  rw [show testScale ((2 : ℝ)⁻¹ ^ j) (pow_ne_zero j (by norm_num)) φ =
      testScale ((2 : ℝ)^j)⁻¹ (inv_ne_zero (pow_ne_zero j (by norm_num))) φ by
    congr 1]
  rw [homogeneous_testScale_inverse u hu (2^j) (pow_pos (by norm_num) _) φ,
    degreeFactor_pow]
  simp only [Complex.ofReal_pow]
  rw [← pow_mul, Nat.mul_comm j d, pow_mul, ← mul_pow, norm_mul, norm_pow]
  norm_num

lemma dyadic_annular_scale {d : ℕ} (η : CompactTests d)
    (φ : Schwartz ℂ d) (j : ℕ) :
    cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ j) (pow_ne_zero j (by norm_num)) η) φ =
      testScale ((2 : ℝ)⁻¹ ^ j) (pow_ne_zero j (by norm_num))
        (cutoffToTestsCLM η (schwartzScale (2^j) (pow_ne_zero j (by norm_num)) φ)) := by
  ext x
  simp only [cutoffToTestsCLM_apply, testScale_apply, schwartzScale_apply, smul_smul]
  simp

lemma geometric_dyadic_bound (B : ℝ) (hB : 0 ≤ B) (m : ℕ) :
    ∃ N : ℕ, ∀ j : ℕ, B ^ j * ((2 ^ j : ℝ)^m / (2 ^ j : ℝ)^N) ≤ (1/2 : ℝ)^j := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B (show (1 : ℝ) < 2 by norm_num)
  refine ⟨m+k+1, fun j => ?_⟩
  have hbase : B * (2 : ℝ)^m / 2^(m+k+1) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).2
    rw [pow_add, pow_add]
    nlinarith [mul_le_mul_of_nonneg_right hk.le (show 0 ≤ (2 : ℝ)^m by positivity)]
  have he (r : ℕ) : (2 ^ j : ℝ) ^ r = (2 ^ r : ℝ) ^ j := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  calc
    _ = (B * (2 : ℝ)^m / 2^(m+k+1))^j := by
      rw [div_pow, mul_pow, he m, he (m+k+1)]
      ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase j

lemma annular_schwartz_derivative_bound {d : ℕ} (η : CompactTests d)
    (hη : ∀ x ∈ tsupport η, 1 ≤ ‖x‖)
    (φ : Schwartz ℂ d) (N n : ℕ) (R : ℝ) (hR : 1 ≤ R) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y => η y * φ (R • y)) x‖ ≤
      (R ^ n / R ^ N) * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        SchwartzMap.seminorm ℂ 0 (n-i) (testToSchwartz η) *
        SchwartzMap.seminorm ℂ N i φ := by
  by_cases hx : x ∈ tsupport η
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hR) N)).2
    rw [mul_comm _ (R^N)]
    exact annular_cutoff_derivative_bound η φ N n n le_rfl R hR x (hη x hx)
  · have hz : iteratedFDeriv ℝ n (fun y => η y * φ (R • y)) x = 0 := by
      by_contra h
      exact hx (tsupport_mul_subset_left (support_iteratedFDeriv_subset n h))
    rw [hz, norm_zero]
    positivity

set_option maxHeartbeats 800000 in
lemma contDiff_dyadic_cutoff_series {d : ℕ} (η : CompactTests d)
    (hη : ∀ x ∈ tsupport η, 1 ≤ ‖x‖) (c : ℂ) (φ : Schwartz ℂ d) :
    ContDiff ℝ ∞ (fun x => ∑' j : ℕ, c^j • (η x * φ ((2^j : ℝ) • x))) := by
  have hbound : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ (j : ℕ) (x : Euclidean d),
      ‖iteratedFDeriv ℝ n (fun y => c^j • (η y * φ ((2^j : ℝ) • y))) x‖ ≤ (1/2 : ℝ)^j * D := by
    intro n
    obtain ⟨N, hN⟩ := geometric_dyadic_bound ‖c‖ (norm_nonneg _) n
    let D := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
      SchwartzMap.seminorm ℂ 0 (n-i) (testToSchwartz η) * SchwartzMap.seminorm ℂ N i φ
    have hD : 0 ≤ D := by dsimp [D]; positivity
    refine ⟨D, hD, fun j x => ?_⟩
    have hs : ContDiff ℝ ∞ (fun y : Euclidean d => η y * φ ((2^j : ℝ) • y)) :=
      η.contDiff.mul ((φ.smooth ⊤).comp (by fun_prop))
    change ‖iteratedFDeriv ℝ n (c^j • (fun y : Euclidean d => η y * φ ((2^j : ℝ) • y))) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (hs.contDiffAt.of_le (by simp)), norm_smul, norm_pow]
    calc
      _ ≤ ‖c‖^j * (((2^j : ℝ)^n / (2^j : ℝ)^N) * D) :=
        mul_le_mul_of_nonneg_left
          (annular_schwartz_derivative_bound η hη φ N n (2^j) (one_le_pow₀ (by norm_num)) x)
          (pow_nonneg (norm_nonneg _) _)
      _ = (‖c‖^j * ((2^j : ℝ)^n / (2^j : ℝ)^N)) * D := by ring
      _ ≤ (1/2 : ℝ)^j * D := mul_le_mul_of_nonneg_right (hN j) hD
  choose D hD hbound using hbound
  apply contDiff_tsum (N := ⊤)
  · intro j
    exact (η.contDiff.mul ((φ.smooth ⊤).comp (by fun_prop))).const_smul (c^j)
  · intro n hn
    exact summable_geometric_two.mul_right (D n)
  · intro n j x hn
    exact hbound n j x

set_option maxHeartbeats 800000 in
lemma exists_annular_cutoff_one {d : ℕ} (x : Euclidean d) (hx : 2 ≤ ‖x‖) :
    ∃ η : CompactTests d, (∀ y ∈ tsupport η, 1 ≤ ‖y‖) ∧
      (η : Euclidean d → ℂ) =ᶠ[𝓝 x] (fun _ => 1) := by
  let b : ContDiffBump x := ⟨1/2, 1, by norm_num, by norm_num⟩
  let η : CompactTests d :=
    { toFun y := (b y : ℂ)
      contDiff' := Complex.ofRealCLM.contDiff.comp b.contDiff
      hasCompactSupport' := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
      tsupport_subset' := Set.subset_univ _ }
  refine ⟨η, ?_, ?_⟩
  · intro y hy
    have hyb : y ∈ tsupport b := (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) (by simp) b) hy
    rw [b.tsupport_eq] at hyb
    have hxy : ‖x - y‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, b] using hyb
    have hnorm : ‖x‖ ≤ ‖x-y‖ + ‖y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x-y) y
    linarith
  · filter_upwards [b.eventuallyEq_one] with y hy
    change (b y : ℂ) = 1
    simp [hy]

lemma contDiffAt_dyadic_schwartz_series_of_norm {d : ℕ} (c : ℂ)
    (φ : Schwartz ℂ d) (x : Euclidean d) (hx : 2 ≤ ‖x‖) :
    ContDiffAt ℝ ∞ (fun y => ∑' j : ℕ, c^j • φ ((2^j : ℝ) • y)) x := by
  obtain ⟨η, hη, hηx⟩ := exists_annular_cutoff_one x hx
  apply (contDiff_dyadic_cutoff_series η hη c φ).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hηx] with y hy
  apply tsum_congr
  intro j
  rw [hy, one_mul]

set_option maxHeartbeats 800000 in
lemma contDiffOn_dyadic_schwartz_series {d : ℕ} (c : ℂ) (φ : Schwartz ℂ d) :
    ContDiffOn ℝ ∞ (fun x => ∑' j : ℕ, c^j • φ ((2^j : ℝ) • x)) ({0}ᶜ : Set (Euclidean d)) := by
  rw [isClosed_singleton.isOpen_compl.contDiffOn_iff]
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  let r : ℝ := ‖x‖ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let ψ := schwartzScale r hr.ne' φ
  have hxnorm : 2 ≤ ‖r⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    dsimp [r]
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    field_simp
    nlinarith
  have h := contDiffAt_dyadic_schwartz_series_of_norm c ψ (r⁻¹ • x) hxnorm
  have hcomp := h.comp x (show ContDiffAt ℝ ∞ (fun y : Euclidean d => r⁻¹ • y) x by fun_prop)
  convert hcomp using 1
  ext y
  apply tsum_congr
  intro j
  simp only [ψ, schwartzScale_apply, smul_smul]
  congr 2
  field_simp

lemma dyadic_schwartz_norm_bound {d : ℕ} (c : ℂ) (φ : Schwartz ℂ d)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (x : Euclidean d), r ≤ ‖x‖ →
      ‖c^j • φ ((2^j : ℝ) • x)‖ ≤ (1/2 : ℝ)^j * C := by
  obtain ⟨N, hN⟩ := geometric_dyadic_bound ‖c‖ (norm_nonneg _) 0
  let Q := SchwartzMap.seminorm ℂ N 0 φ
  let C := Q / r^N
  have hC : 0 ≤ C := by dsimp [C, Q]; positivity
  refine ⟨C, hC, fun j x hx => ?_⟩
  have hR : 0 < (2^j : ℝ) := pow_pos (by norm_num) _
  have hdec : ‖φ ((2^j : ℝ) • x)‖ ≤ (1 / (2^j : ℝ)^N) * C := by
    have he : (1 / (2^j : ℝ)^N) * C = Q / ((2^j : ℝ)^N * r^N) := by
      dsimp [C]
      ring
    rw [he]
    apply (le_div_iff₀ (mul_pos (pow_pos hR N) (pow_pos hr N))).2
    calc
      _ = ((2^j : ℝ) * r)^N * ‖φ ((2^j : ℝ) • x)‖ := by rw [mul_pow]; ring
      _ ≤ ‖(2^j : ℝ) • x‖^N * ‖φ ((2^j : ℝ) • x)‖ := by
        gcongr
        rw [norm_smul, Real.norm_of_nonneg hR.le]
        exact mul_le_mul_of_nonneg_left hx hR.le
      _ ≤ Q := φ.norm_pow_mul_le_seminorm ℂ N _
  rw [norm_smul, norm_pow]
  calc
    _ ≤ ‖c‖^j * ((1 / (2^j : ℝ)^N) * C) :=
      mul_le_mul_of_nonneg_left hdec (pow_nonneg (norm_nonneg _) _)
    _ = (‖c‖^j * (1 / (2^j : ℝ)^N)) * C := by ring
    _ ≤ (1/2 : ℝ)^j * C :=
      mul_le_mul_of_nonneg_right (by simpa only [pow_zero] using hN j) hC

lemma summable_dyadic_schwartz_series {d : ℕ} (c : ℂ) (φ : Schwartz ℂ d)
    (x : Euclidean d) (hx : x ≠ 0) :
    Summable (fun j : ℕ => c^j • φ ((2^j : ℝ) • x)) := by
  obtain ⟨C, hC, hbound⟩ := dyadic_schwartz_norm_bound c φ ‖x‖ (norm_pos_iff.mpr hx)
  exact Summable.of_norm_bounded (summable_geometric_two.mul_right C) (fun j => hbound j x le_rfl)

lemma compact_test_support_norm_gap {d : ℕ} (ψ : CompactTests d)
    (hψ : tsupport ψ ⊆ ({0}ᶜ : Set (Euclidean d))) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ tsupport ψ, r ≤ ‖x‖ := by
  have hz : (0 : Euclidean d) ∈ (tsupport ψ)ᶜ := by
    intro h
    exact hψ h (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (isClosed_closure.isOpen_compl.mem_nhds hz)
  refine ⟨r, hr, fun x hx => le_of_not_gt (fun h => ?_)⟩
  exact hball (by simpa [Metric.mem_ball] using h) hx

set_option maxHeartbeats 800000 in
lemma hasSum_integral_dyadic_schwartz_series {d : ℕ} (c : ℂ) (φ : Schwartz ℂ d)
    (ψ : CompactTests d) (hψ : tsupport ψ ⊆ ({0}ᶜ : Set (Euclidean d))) :
    HasSum (fun j : ℕ => ∫ x, (c^j • φ ((2^j : ℝ) • x)) * ψ x)
      (∫ x, (∑' j : ℕ, c^j • φ ((2^j : ℝ) • x)) * ψ x) := by
  obtain ⟨r, hr, hrx⟩ := compact_test_support_norm_gap ψ hψ
  obtain ⟨C, hC, hbound⟩ := dyadic_schwartz_norm_bound c φ r hr
  let F : ℕ → Euclidean d → ℂ := fun j x => (c^j • φ ((2^j : ℝ) • x)) * ψ x
  have hint : ∀ j, Integrable (F j) := by
    intro j
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [F]
      fun_prop
    · exact ψ.hasCompactSupport.mul_left
  have hψint : Integrable (fun x : Euclidean d => ‖ψ x‖) := (testToSchwartz ψ).integrable.norm
  have hdom (j : ℕ) (x : Euclidean d) : ‖F j x‖ ≤ (1/2 : ℝ)^j * C * ‖ψ x‖ := by
    dsimp [F]
    rw [norm_mul]
    by_cases hz : ψ x = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right (hbound j x (hrx x (subset_closure hz))) (norm_nonneg _)
  have hIntegralBound (j : ℕ) :
      ∫ x, ‖F j x‖ ≤ (1/2 : ℝ)^j * (C * ∫ x, ‖ψ x‖) := by
    calc
      _ ≤ ∫ x : Euclidean d, (1/2 : ℝ)^j * C * ‖ψ x‖ :=
        integral_mono (hint j).norm (hψint.const_mul _) (hdom j)
      _ = _ := by rw [integral_const_mul]; ring
  have hsum : Summable (fun j : ℕ => ∫ x, ‖F j x‖) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (fun x => norm_nonneg _))
      hIntegralBound (summable_geometric_two.mul_right (C * ∫ x, ‖ψ x‖))
  have he := hasSum_integral_of_summable_integral_norm hint hsum
  simpa only [F, tsum_mul_right] using he
lemma integral_dyadic_schwartz_series {d : ℕ} (c : ℂ) (φ : Schwartz ℂ d)
    (ψ : CompactTests d) (hψ : tsupport ψ ⊆ ({0}ᶜ : Set (Euclidean d))) :
    (∑' j : ℕ, ∫ x, (c^j • φ ((2^j : ℝ) • x)) * ψ x) =
      ∫ x, (∑' j : ℕ, c^j • φ ((2^j : ℝ) • x)) * ψ x :=
  (hasSum_integral_dyadic_schwartz_series c φ ψ hψ).tsum_eq

lemma annularCutoff_support_away_zero (d : ℕ) :
    tsupport (annularCutoff d) ⊆ ({0}ᶜ : Set (Euclidean d)) := by
  intro x hx
  have hn : 1 ≤ ‖x‖ := annularCutoff_support hx
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  simpa using hx0

lemma contDiff_annularKernel {d : ℕ} (k : Euclidean d → ℂ)
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d))) :
    ContDiff ℝ ∞ (fun x => annularCutoff d x * k x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have h0 : (0 : Euclidean d) ∉ tsupport (annularCutoff d) := by
      intro h
      exact annularCutoff_support_away_zero d h (by simp)
    have hz : (annularCutoff d : Euclidean d → ℂ) =ᶠ[𝓝 0] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp h0
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [hy, zero_mul, Pi.zero_apply]
  · exact ((annularCutoff d).contDiff.of_le (by simp)).contDiffAt.mul
      (hk.contDiffAt (isOpen_compl_singleton.mem_nhds hx))

def annularKernel {d : ℕ} (k : Euclidean d → ℂ)
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d))) : Schwartz ℂ d :=
  ((annularCutoff d).hasCompactSupport.mul_right (f' := k)).toSchwartzMap
    (contDiff_annularKernel k hk)

@[simp] lemma annularKernel_apply {d : ℕ} (k : Euclidean d → ℂ)
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d))) (x : Euclidean d) :
    annularKernel k hk x = annularCutoff d x * k x := rfl

lemma annularKernel_dilate {d : ℕ} {z : ℂ} (k : Euclidean d → ℂ)
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hhom : ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      k (a • x) = degreeFactor a z * k x) (R : ℝ) (hR : 0 < R) (x : Euclidean d) :
    k x * testScale R⁻¹ (inv_ne_zero hR.ne') (annularCutoff d) x =
      (degreeFactor R z • schwartzScale R⁻¹ (inv_ne_zero hR.ne') (annularKernel k hk)) x := by
  by_cases hx : x = 0
  · subst x
    simp only [testScale_apply, smul_zero, smul_apply, schwartzScale_apply, annularKernel_apply]
    have hη : annularCutoff d 0 = 0 := annularCutoff_vanishes 0 (by simp)
    simp [hη]
  · have hy : R⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hR.ne') hx
    have h := hhom R hR (R⁻¹ • x) hy
    simp only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at h
    simp only [testScale_apply, smul_apply, schwartzScale_apply, annularKernel_apply, smul_eq_mul]
    rw [h]
    ring

lemma annular_schwartz_pairing {d : ℕ} {z : ℂ} {v : Tempered ℂ d}
    (hv : IsTemperedHomogeneous v z) {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ τ : CompactTests d, tsupport τ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz τ) = ∫ x, k x * τ x)
    (R : ℝ) (hR : 0 < R) (ψ : Schwartz ℂ d) :
    v (testToSchwartz (cutoffToTestsCLM (testScale R⁻¹ (inv_ne_zero hR.ne') (annularCutoff d)) ψ)) =
      ∫ x, (degreeFactor R z • schwartzScale R⁻¹ (inv_ne_zero hR.ne') (annularKernel k hk)) x * ψ x := by
  have hτ : tsupport (cutoffToTestsCLM (testScale R⁻¹ (inv_ne_zero hR.ne') (annularCutoff d)) ψ) ⊆
      ({0}ᶜ : Set (Euclidean d)) := by
    have heval : (cutoffToTestsCLM (testScale R⁻¹ (inv_ne_zero hR.ne') (annularCutoff d)) ψ : Euclidean d → ℂ) =
        (fun x => testScale R⁻¹ (inv_ne_zero hR.ne') (annularCutoff d) x * ψ x) := by
      funext x
      exact cutoffToTestsCLM_apply _ _ _
    rw [heval]
    exact tsupport_mul_subset_left.trans
      (testScale_tsupport_away_zero R⁻¹ (inv_ne_zero hR.ne') (annularCutoff d)
        (annularCutoff_support_away_zero d))
  rw [hkv _ hτ]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [cutoffToTestsCLM_apply, ← mul_assoc,
      annularKernel_dilate k hk (tempered_representative_homogeneous hv hk.continuousOn hkv) R hR x])

lemma fourier_annularKernel_dilate {d : ℕ} (z : ℂ) (g : Schwartz ℂ d) (j : ℕ) :
    schwartzFourier (degreeFactor ((2 : ℝ)^j) z •
      schwartzScale ((2 : ℝ)^j)⁻¹ (inv_ne_zero (pow_ne_zero j (by norm_num))) g) =
      ((2 : ℂ)^d * degreeFactor 2 z)^j •
        schwartzScale ((2 : ℝ)^j) (pow_ne_zero j (by norm_num)) (schwartzFourier g) := by
  rw [map_smul, schwartz_scaling d ((2 : ℝ)^j)⁻¹ (inv_pos.mpr (pow_pos (by norm_num) j)) g]
  simp only [Complex.ofReal_inv, inv_pow, inv_inv, degreeFactor_pow, smul_smul, Complex.ofReal_pow]
  have he : degreeFactor 2 z ^ j * (((2 : ℝ) : ℂ)^j)^d =
      ((2 : ℂ)^d * degreeFactor 2 z)^j := by
    norm_num only [Complex.ofReal_ofNat]
    rw [← pow_mul, Nat.mul_comm j d, pow_mul, mul_pow]
    ring
  rw [he]

lemma annular_fourier_pairing {d : ℕ} {z : ℂ} {v : Tempered ℂ d}
    (hv : IsTemperedHomogeneous v z) {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ τ : CompactTests d, tsupport τ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz τ) = ∫ x, k x * τ x) (j : ℕ) (τ : CompactTests d) :
    v (testToSchwartz (cutoffToTestsCLM
      (testScale ((2 : ℝ)⁻¹ ^ j) (pow_ne_zero j (by norm_num)) (annularCutoff d))
      (schwartzFourier (testToSchwartz τ)))) =
      ∫ ξ, (((2 : ℂ)^d * degreeFactor 2 z)^j •
        schwartzFourier (annularKernel k hk) ((2^j : ℝ) • ξ)) * τ ξ := by
  have he : (2 : ℝ)⁻¹ ^ j = (2 ^ j)⁻¹ := inv_pow 2 j
  have hτ := annular_schwartz_pairing hv hk hkv (2^j) (pow_pos (by norm_num) j)
    (schwartzFourier (testToSchwartz τ))
  have hscale : testScale ((2 : ℝ)⁻¹ ^ j) (pow_ne_zero j (by norm_num)) (annularCutoff d) =
      testScale ((2 : ℝ)^j)⁻¹ (inv_ne_zero (pow_ne_zero j (by norm_num))) (annularCutoff d) := by
    ext x
    simp only [testScale_apply, he]
  rw [hscale, hτ]
  have hp := SchwartzMap.integral_fourier_mul_eq
    (degreeFactor ((2 : ℝ)^j) z •
      schwartzScale ((2 : ℝ)^j)⁻¹ (inv_ne_zero (pow_ne_zero j (by norm_num))) (annularKernel k hk))
    (testToSchwartz τ)
  change (∫ ξ, schwartzFourier _ ξ * τ ξ) =
    (∫ x, (degreeFactor ((2 : ℝ)^j) z •
      schwartzScale ((2 : ℝ)^j)⁻¹ (inv_ne_zero (pow_ne_zero j (by norm_num))) (annularKernel k hk)) x *
      schwartzFourier (testToSchwartz τ) x) at hp
  rw [← hp, fourier_annularKernel_dilate]
  rfl

set_option maxHeartbeats 800000 in
lemma exists_smooth_fourier_exterior {d : ℕ} {z : ℂ} {v : Tempered ℂ d}
    (hv : IsTemperedHomogeneous v z) {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ τ : CompactTests d, tsupport τ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz τ) = ∫ x, k x * τ x) :
    ∃ g : Euclidean d → ℂ, ContDiffOn ℝ ∞ g ({0}ᶜ : Set (Euclidean d)) ∧
      ∀ τ : CompactTests d, tsupport τ ⊆ ({0}ᶜ : Set (Euclidean d)) →
        v (schwartzFourier (testToSchwartz τ)) -
          v (testToSchwartz (cutoffToTestsCLM (originCutoff d) (schwartzFourier (testToSchwartz τ)))) =
            ∫ ξ, g ξ * τ ξ := by
  let c : ℂ := (2 : ℂ)^d * degreeFactor 2 z
  let f := schwartzFourier (annularKernel k hk)
  refine ⟨fun ξ => ∑' j : ℕ, c^j • f ((2^j : ℝ) • ξ),
    contDiffOn_dyadic_schwartz_series c f, fun τ hτ => ?_⟩
  have hsum := hasSum_integral_dyadic_schwartz_series c f τ hτ
  have hlim := tendsto_dyadic_exterior_pairing v (schwartzFourier (testToSchwartz τ))
  have hlim' : Tendsto (fun n => ∑ j ∈ Finset.range n,
      ∫ ξ, (c^j • f ((2^j : ℝ) • ξ)) * τ ξ) atTop
      (𝓝 (v (schwartzFourier (testToSchwartz τ)) -
        v (testToSchwartz (cutoffToTestsCLM (originCutoff d) (schwartzFourier (testToSchwartz τ)))))) := by
    convert hlim using 1
    funext n
    apply Finset.sum_congr rfl
    intro j hj
    exact (annular_fourier_pairing hv hk hkv j τ).symm
  exact tendsto_nhds_unique hlim' hsum.tendsto_sum_nat

set_option maxHeartbeats 800000 in
/-- Homogeneity and the fixed-annulus finite-order bound give a uniform
continuous Schwartz seminorm bound on every compactly supported test. -/
lemma homogeneous_schwartz_bound {d : ℕ} {z : ℂ} (u : Distribution d)
    (hu : IsHomogeneous u z) :
    ∃ p : Seminorm ℂ (Schwartz ℂ d), Continuous p ∧
      ∀ φ : CompactTests d, ‖u φ‖ ≤ p (testToSchwartz φ) := by
  obtain ⟨m, hm⟩ := distribution_annular_bound u (annularCutoff d)
    (fun x hx => annularCutoff_support (d := d) hx)
  let B : ℝ := ‖(2 : ℂ) ^ d * degreeFactor 2 z‖
  obtain ⟨N, hN⟩ := geometric_dyadic_bound B (norm_nonneg _) m
  obtain ⟨p, hp, hbound⟩ := hm N
  let v₀ := localizedTempered u (originCutoff d)
  let p₀ : Seminorm ℂ (Schwartz ℂ d) := (normSeminorm ℂ ℂ).comp v₀.toLinearMap
  have hp₀ : Continuous p₀ := v₀.continuous.norm
  have hterm (φ : Schwartz ℂ d) (j : ℕ) :
      ‖u (cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ j) (by positivity) (annularCutoff d)) φ)‖ ≤
        (1/2 : ℝ)^j * p φ := by
    rw [dyadic_annular_scale, homogeneous_dyadic_norm u hu]
    calc
      _ ≤ B ^ j * (((2 ^ j : ℝ)^m / (2 ^ j : ℝ)^N) * p φ) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
        exact hbound (2^j) (one_le_pow₀ (by norm_num)) φ
      _ = (B^j * ((2 ^ j : ℝ)^m / (2 ^ j : ℝ)^N)) * p φ := by ring
      _ ≤ (1/2 : ℝ)^j * p φ := mul_le_mul_of_nonneg_right (hN j) (apply_nonneg _ _)
  refine ⟨p₀ + (2 : NNReal) • p, ?_, fun φ => ?_⟩
  · change Continuous (fun φ => p₀ φ + (2 : NNReal) • p φ)
    exact hp₀.add (continuous_const.smul hp)
  · obtain ⟨n, hn⟩ := compact_test_dyadic_partition φ
    calc
      ‖u φ‖ = ‖u (cutoffToTestsCLM (originCutoff d) (testToSchwartz φ)) +
          ∑ j ∈ Finset.range n,
            u (cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ j) (by positivity) (annularCutoff d))
              (testToSchwartz φ))‖ := by
        conv_lhs => rw [hn]
        rw [map_add, map_sum]
      _ ≤ ‖u (cutoffToTestsCLM (originCutoff d) (testToSchwartz φ))‖ +
          ∑ j ∈ Finset.range n,
            ‖u (cutoffToTestsCLM (testScale ((2 : ℝ)⁻¹ ^ j) (by positivity) (annularCutoff d))
              (testToSchwartz φ))‖ := by
        exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ p₀ (testToSchwartz φ) + ∑ j ∈ Finset.range n, (1/2 : ℝ)^j * p (testToSchwartz φ) := by
        exact add_le_add le_rfl (Finset.sum_le_sum (fun j hj => hterm (testToSchwartz φ) j))
      _ = p₀ (testToSchwartz φ) + (∑ j ∈ Finset.range n, (1/2 : ℝ)^j) * p (testToSchwartz φ) := by
        rw [Finset.sum_mul]
      _ ≤ p₀ (testToSchwartz φ) + 2 * p (testToSchwartz φ) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (sum_geometric_two_le n) (apply_nonneg p _))
      _ = (p₀ + (2 : NNReal) • p) (testToSchwartz φ) := by
        simp [NNReal.smul_def]

/-- Extension and homogeneity follow from the dyadic estimate, using complex
Hahn--Banach and the proved density of compact tests in Schwartz space. -/
theorem tempered_extension :
    Specs.ExpandedFA.PartIV.HomogeneousFourier.temperedExtensionType := by
  intro d z u hu
  obtain ⟨p, hp, hbound⟩ := homogeneous_schwartz_bound u hu
  exact tempered_extension_of_bound u hu p hp hbound

open scoped BoundedContinuousFunction

/-- A normed finite product of bounded continuous derivative fields. -/
abbrev CompactJetSpace (d : ℕ) (s : Finset ℕ) :=
  ∀ i : (↑(insert 0 s) : Set ℕ), Euclidean d →ᵇ (Euclidean d [×(i : ℕ)]→L[ℝ] ℂ)

def compactJetMap {d : ℕ} (K : TopologicalSpace.Compacts (Euclidean d)) (s : Finset ℕ) :
    ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K →ₗ[ℂ] CompactJetSpace d s :=
  LinearMap.pi (fun i => (ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ (i : ℕ)).toLinearMap)

lemma compactJetMap_injective {d : ℕ} (K : TopologicalSpace.Compacts (Euclidean d)) (s : Finset ℕ) :
    Function.Injective (compactJetMap K s) := by
  intro φ ψ h
  apply ContDiffMapSupportedIn.structureMapCLM_zero_injective ℂ
  exact congrFun h ⟨0, by simp⟩

lemma compactJetMap_seminorm_le {d : ℕ} (K : TopologicalSpace.Compacts (Euclidean d)) (s : Finset ℕ)
    (φ : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K) :
    s.sup (ContDiffMapSupportedIn.seminorm ℂ (Euclidean d) ℂ ⊤ K) φ ≤
      ‖compactJetMap K s φ‖ := by
  rw [Seminorm.finset_sup_apply]
  change (s.sup (fun i => (⟨ContDiffMapSupportedIn.seminorm ℂ (Euclidean d) ℂ ⊤ K i φ, by positivity⟩ : ℝ≥0)) : ℝ≥0) ≤ ‖compactJetMap K s φ‖₊
  apply Finset.sup_le
  intro i hi
  change ‖ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ i φ‖₊ ≤ _
  exact_mod_cast norm_le_pi_norm (compactJetMap K s φ) ⟨i, by simp [hi]⟩

/-- A distribution restricted to one compact set factors through finitely many
actual derivative fields and a continuous functional on their normed product. -/
lemma compactJet_factorization {d : ℕ} (u : Distribution d)
    (K : TopologicalSpace.Compacts (Euclidean d)) :
    ∃ (s : Finset ℕ) (L : CompactJetSpace d s →L[ℂ] ℂ),
      ∀ φ : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K,
        u (TestFunction.ofSupportedIn (Set.subset_univ _) φ) = L (compactJetMap K s φ) := by
  obtain ⟨s, C, _, hbound⟩ := distribution_fixed_compact_bound u K
  let e := LinearEquiv.ofInjective (compactJetMap K s) (compactJetMap_injective K s)
  let T := u.comp (TestFunction.ofSupportedInCLM ℂ (Set.subset_univ (K : Set (Euclidean d))))
  let f := T.toLinearMap.comp e.symm.toLinearMap
  let p : Seminorm ℂ (CompactJetSpace d s) := (C : ℝ≥0) • normSeminorm ℂ (CompactJetSpace d s)
  have hp : Continuous p := by
    change Continuous (fun x : CompactJetSpace d s => (C : ℝ) * ‖x‖)
    exact continuous_const.mul continuous_norm
  have hf : ∀ x : (compactJetMap K s).range, ‖f x‖ ≤ p x := by
    intro x
    change ‖u (TestFunction.ofSupportedIn (Set.subset_univ _) (e.symm x))‖ ≤ C * ‖(x : CompactJetSpace d s)‖
    calc
      _ ≤ C * s.sup (ContDiffMapSupportedIn.seminorm ℂ (Euclidean d) ℂ ⊤ K) (e.symm x) := hbound _
      _ ≤ C * ‖compactJetMap K s (e.symm x)‖ := by gcongr; exact compactJetMap_seminorm_le K s _
      _ = _ := by
        congr 2
        exact congrArg Subtype.val (e.apply_symm_apply x)
  obtain ⟨L, hL, _⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm _ f hp hf
  refine ⟨s, L, fun φ => ?_⟩
  have h := hL (e φ)
  change L (compactJetMap K s φ) = f (e φ) at h
  have h' : T φ = L (compactJetMap K s φ) := by
    simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply,
      ContinuousLinearMap.coe_coe] using h.symm
  exact h'



@[simp] lemma norm_degreeFactor (a : ℝ) (ha : 0 < a) (z : ℂ) :
    ‖degreeFactor a z‖ = a ^ z.re := by
  simp [degreeFactor, Complex.norm_exp, Complex.mul_re, Real.rpow_def_of_pos ha]

/-- A radial scaling law for norms turns a bound on the compact unit sphere
into a uniform power bound on the punctured space, including dimension zero. -/
theorem norm_bound_of_radial_homogeneity {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {r : ℝ} {f : Euclidean d → F}
    (hf : ContinuousOn f ({0}ᶜ : Set (Euclidean d)))
    (hhom : ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      ‖f (a • x)‖ = a ^ r * ‖f x‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d, x ≠ 0 →
      ‖f x‖ ≤ C * ‖x‖ ^ r := by
  have hs : Metric.sphere (0 : Euclidean d) 1 ⊆ ({0}ᶜ : Set (Euclidean d)) := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using norm_ne_zero_iff.mp (by linarith : ‖x‖ ≠ 0)
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Euclidean d) 1).exists_bound_of_continuousOn
    (hf.mono hs)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : Euclidean d := ‖x‖⁻¹ • x
  have hynorm : ‖y‖ = 1 := by
    simp only [y, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      inv_mul_cancel₀ hr.ne']
  have hy : y ≠ 0 := norm_ne_zero_iff.mp (by rw [hynorm]; exact one_ne_zero)
  have hyS : y ∈ Metric.sphere (0 : Euclidean d) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hynorm
  have hxy : ‖x‖ • y = x := by simp [y, smul_smul, hr.ne']
  calc
    ‖f x‖ = ‖x‖ ^ r * ‖f y‖ := by rw [← hhom ‖x‖ hr y hy, hxy]
    _ ≤ ‖x‖ ^ r * max C 0 := by
      gcongr
      exact (hC y hyS).trans (le_max_left _ _)
    _ = max C 0 * ‖x‖ ^ r := mul_comm _ _

/-- A continuous homogeneous kernel has a uniform radial power bound. -/
theorem homogeneous_kernel_norm_bound {d : ℕ} {z : ℂ} {k : Euclidean d → ℂ}
    (hk : ContinuousOn k ({0}ᶜ : Set (Euclidean d)))
    (hhom : ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      k (a • x) = degreeFactor a z * k x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d, x ≠ 0 →
      ‖k x‖ ≤ C * ‖x‖ ^ z.re := by
  apply norm_bound_of_radial_homogeneity hk
  intro a ha x hx
  rw [hhom a ha x hx, norm_mul, norm_degreeFactor a ha z]

/-- Invertible scalar pullback scales every derivative slot; this identity is
local and does not demand regularity at the origin. -/
lemma iteratedFDeriv_comp_scale {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (k : Euclidean d → ℂ) (n : ℕ) (x : Euclidean d) :
    iteratedFDeriv ℝ n (fun y => k (a • y)) x =
      a ^ n • iteratedFDeriv ℝ n k (a • x) := by
  let e := scaleEquiv (d := d) a ha
  have h := e.iteratedFDerivWithin_comp_right k
    (s := Set.univ) uniqueDiffOn_univ (x := x) (Set.mem_univ _) n
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
  change iteratedFDeriv ℝ n (fun y => k (a • y)) x = _ at h
  rw [h]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, smul_apply]
  change (iteratedFDeriv ℝ n k (a • x)) (fun j => a • v j) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp


/-- Differentiating the homogeneity identity on the punctured space scales each
of the derivative slots. -/
lemma iteratedFDeriv_homogeneous_identity {d : ℕ} {z : ℂ} {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hhom : ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      k (a • x) = degreeFactor a z * k x)
    (n : ℕ) (a : ℝ) (ha : 0 < a) (x : Euclidean d) (hx : x ≠ 0) :
    a ^ n • iteratedFDeriv ℝ n k (a • x) =
      degreeFactor a z • iteratedFDeriv ℝ n k x := by
  have he : (fun y => k (a • y)) =ᶠ[𝓝 x] (fun y => degreeFactor a z • k y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact hhom a ha y hy
  have hD := (he.iteratedFDeriv ℝ n).self_of_nhds
  rw [iteratedFDeriv_comp_scale a ha.ne',
    iteratedFDeriv_const_smul_apply'] at hD
  · exact hD
  · exact (hk.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).of_le (by simp)

lemma norm_iteratedFDeriv_homogeneous {d : ℕ} {z : ℂ} {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hhom : ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      k (a • x) = degreeFactor a z * k x)
    (n : ℕ) (a : ℝ) (ha : 0 < a) (x : Euclidean d) (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ n k (a • x)‖ =
      a ^ (z.re - (n : ℝ)) * ‖iteratedFDeriv ℝ n k x‖ := by
  have h := congrArg norm (iteratedFDeriv_homogeneous_identity hk hhom n a ha x hx)
  simp only [norm_smul, Real.norm_of_nonneg (pow_nonneg ha.le n),
    norm_degreeFactor a ha z] at h
  rw [Real.rpow_sub_natCast ha.ne']
  apply mul_left_cancel₀ (pow_ne_zero n ha.ne')
  calc
    a ^ n * ‖iteratedFDeriv ℝ n k (a • x)‖ = a ^ z.re * ‖iteratedFDeriv ℝ n k x‖ := h
    _ = a ^ n * (a ^ z.re / a ^ n * ‖iteratedFDeriv ℝ n k x‖) := by
      field_simp


/-- Every derivative of a smooth homogeneous kernel has the expected radial
power bound, without any assumption about its value or regularity at zero. -/
theorem homogeneous_kernel_derivative_norm_bound {d : ℕ} {z : ℂ}
    {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hhom : ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      k (a • x) = degreeFactor a z * k x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d, x ≠ 0 →
      ‖iteratedFDeriv ℝ n k x‖ ≤ C * ‖x‖ ^ (z.re - (n : ℝ)) := by
  have hDc : ContinuousOn (iteratedFDeriv ℝ n k) ({0}ᶜ : Set (Euclidean d)) := by
    intro x hx
    have hx0 : x ≠ 0 := hx
    exact (((hk.contDiffAt (isOpen_compl_singleton.mem_nhds hx0)).iteratedFDeriv_right
      (m := 0) (by simp)).continuousAt).continuousWithinAt
  exact norm_bound_of_radial_homogeneity hDc (norm_iteratedFDeriv_homogeneous hk hhom n)


/-- Parameter differentiation for a fixed-support test family reduces to
ordinary smoothness of all its bounded continuous derivative fields. -/
lemma distribution_pairing_contDiff {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] (u : Distribution d)
    (K : TopologicalSpace.Compacts (Euclidean d))
    (F : H → ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K)
    (hF : ∀ n : ℕ, ContDiff ℝ ∞ (fun ξ =>
      ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ n (F ξ))) :
    ContDiff ℝ ∞ (fun ξ => u (TestFunction.ofSupportedIn (Set.subset_univ _) (F ξ))) := by
  obtain ⟨s, L, hL⟩ := compactJet_factorization u K
  have hJ : ContDiff ℝ ∞ (fun ξ => compactJetMap K s (F ξ)) :=
    contDiff_pi.2 (fun i => hF i)
  have h := (L.restrictScalars ℝ).contDiff.comp hJ
  convert h using 1
  ext ξ
  exact hL (F ξ)


/-- The representative supplied by the forward theorem has radial power bounds
for every derivative. This uses its actual distributional homogeneity. -/
theorem tempered_representative_derivative_norm_bound {d : ℕ} {z : ℂ}
    {v : Tempered ℂ d} (hv : IsTemperedHomogeneous v z)
    {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz φ) = ∫ x, k x * φ x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d, x ≠ 0 →
      ‖iteratedFDeriv ℝ n k x‖ ≤ C * ‖x‖ ^ (z.re - (n : ℝ)) := by
  exact homogeneous_kernel_derivative_norm_bound hk
    (tempered_representative_homogeneous hv hk.continuousOn hkv) n

/-- Outside the cutoff support, the exterior kernel agrees locally with the
original kernel, so their ordinary derivatives agree there. -/
lemma iteratedFDeriv_exteriorKernel {d : ℕ} (χ : CompactTests d)
    (k : Euclidean d → ℂ) (n : ℕ) (x : Euclidean d)
    (hx : x ∉ tsupport χ) :
    iteratedFDeriv ℝ n (fun y => (1 - χ y) * k y) x =
      iteratedFDeriv ℝ n k x := by
  have he : (fun y => (1 - χ y) * k y) =ᶠ[𝓝 x] k := by
    rw [notMem_tsupport_iff_eventuallyEq] at hx
    filter_upwards [hx] with y hy
    simp only [hy, sub_zero, one_mul, Pi.zero_apply]
  exact (he.iteratedFDeriv ℝ n).self_of_nhds

/-- Every derivative of the actual smooth exterior kernel has the homogeneous
radial bound off a fixed compact set. -/
theorem exteriorKernel_derivative_norm_bound {d : ℕ} {z : ℂ}
    {v : Tempered ℂ d} (hv : IsTemperedHomogeneous v z)
    {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz φ) = ∫ x, k x * φ x)
    (χ : CompactTests d) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d, x ≠ 0 → x ∉ tsupport χ →
      ‖iteratedFDeriv ℝ n (fun y => (1 - χ y) * k y) x‖ ≤
        C * ‖x‖ ^ (z.re - (n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := tempered_representative_derivative_norm_bound hv hk hkv n
  refine ⟨C, hC, fun x hx hχ => ?_⟩
  rw [iteratedFDeriv_exteriorKernel χ k n x hχ]
  exact hbound x hx


open LineDeriv

/-- The phase with a bounded position field, as a bounded continuous function. -/
def boundedPhaseCLM {d : ℕ} (q : Euclidean d →ᵇ Euclidean d) (c : ℂ) :
    Euclidean d →L[ℝ] (Euclidean d →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun ξ := BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x => c * (inner ℝ (q x) ξ : ℝ))
        (by fun_prop) (‖c‖ * ‖q‖ * ‖ξ‖) (fun x => by
          simp only [norm_mul, Complex.norm_real]
          exact mul_le_mul_of_nonneg_left
            ((norm_inner_le_norm (q x) ξ).trans
              (mul_le_mul_of_nonneg_right (q.norm_coe_le_norm x) (norm_nonneg ξ)))
            (norm_nonneg c) |>.trans_eq (by ring))
      map_add' ξ η := by ext x; simp [inner_add_right, mul_add]
      map_smul' a ξ := by ext x; simp [inner_smul_right, mul_comm, mul_left_comm] }
    (‖c‖ * ‖q‖) (fun ξ =>
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) (fun x => by
        simp only [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left
          ((norm_inner_le_norm (q x) ξ).trans
            (mul_le_mul_of_nonneg_right (q.norm_coe_le_norm x) (norm_nonneg ξ)))
          (norm_nonneg c) |>.trans_eq (by ring)))

@[simp] lemma boundedPhaseCLM_apply {d : ℕ} (q : Euclidean d →ᵇ Euclidean d)
    (c : ℂ) (ξ x : Euclidean d) : boundedPhaseCLM q c ξ x = c * (inner ℝ (q x) ξ : ℝ) := rfl

def boundedExponentialFamily {d : ℕ} (q : Euclidean d →ᵇ Euclidean d) (c : ℂ)
    (ξ : Euclidean d) : Euclidean d →ᵇ ℂ := NormedSpace.exp (boundedPhaseCLM q c ξ)

lemma boundedExponentialFamily_contDiff {d : ℕ} (q : Euclidean d →ᵇ Euclidean d)
    (c : ℂ) : ContDiff ℝ ∞ (boundedExponentialFamily q c) := by
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : (Euclidean d →ᵇ ℂ) → (Euclidean d →ᵇ ℂ)) :=
    (show AnalyticOnNhd ℝ NormedSpace.exp Set.univ from
      fun x _ => NormedSpace.exp_analytic x).contDiff
  exact hexp.comp (boundedPhaseCLM q c).contDiff

@[simp] lemma boundedExponentialFamily_apply {d : ℕ} (q : Euclidean d →ᵇ Euclidean d)
    (c : ℂ) (ξ x : Euclidean d) :
    boundedExponentialFamily q c ξ x = Complex.exp (c * (inner ℝ (q x) ξ : ℝ)) := by
  let ev : (Euclidean d →ᵇ ℂ) →+* ℂ :=
    { toFun := fun f => f x
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.map_exp ev (BoundedContinuousFunction.evalCLM ℂ x).continuous
    (boundedPhaseCLM q c ξ)



/-- A bounded continuous position field agrees with the identity wherever the
compact scalar cutoff equals one. -/
def cutoffPosition {d : ℕ} (ψ : CompactTests d) : Euclidean d →ᵇ Euclidean d := by
  let q : Euclidean d → Euclidean d := fun x => (ψ x).re • x
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hc : HasCompactSupport q :=
    (ψ.hasCompactSupport.comp_left (g := Complex.re) (by simp)).smul_right
  exact ⟨⟨q, hq⟩, Metric.isBounded_range_iff.1 (hc.isCompact_range hq).isBounded⟩

@[simp] lemma cutoffPosition_apply {d : ℕ} (ψ : CompactTests d) (x : Euclidean d) :
    cutoffPosition ψ x = (ψ x).re • x := rfl

lemma exists_boundedPosition_on_tsupport {d : ℕ} (χ : CompactTests d) :
    ∃ q : Euclidean d →ᵇ Euclidean d, ∀ x ∈ tsupport χ, q x = x := by
  obtain ⟨n, hn⟩ := exists_dyadic_cutoff_eq_one χ
  let ψ := testScale ((2 : ℝ)⁻¹ ^ n) (by positivity) (originCutoff d)
  refine ⟨cutoffPosition ψ, fun x hx => ?_⟩
  change (originCutoff d (((2 : ℝ)⁻¹ ^ n) • x)).re • x = x
  rw [hn x hx]
  simp

/-- The zeroth derivative field of the actual compact oscillatory family is
smooth as a bounded-continuous-function-valued map. -/
lemma cutoff_exponential_bcf_contDiff {d : ℕ} (χ : CompactTests d) (c : ℂ) :
    ∃ F : Euclidean d → (Euclidean d →ᵇ ℂ),
      ContDiff ℝ ∞ F ∧ ∀ ξ x, F ξ x = χ x * Complex.exp (c * (inner ℝ x ξ : ℝ)) := by
  obtain ⟨q, hq⟩ := exists_boundedPosition_on_tsupport χ
  let χb : Euclidean d →ᵇ ℂ := ⟨⟨χ, χ.contDiff.continuous⟩,
    Metric.isBounded_range_iff.1 (χ.hasCompactSupport.isCompact_range χ.contDiff.continuous).isBounded⟩
  refine ⟨fun ξ => χb * boundedExponentialFamily q c ξ,
    contDiff_const.mul (boundedExponentialFamily_contDiff q c), fun ξ x => ?_⟩
  change χ x * boundedExponentialFamily q c ξ x = _
  rw [boundedExponentialFamily_apply]
  by_cases hx : x ∈ tsupport χ
  · rw [hq x hx]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]



def oscillatoryTest {d : ℕ} (χ : CompactTests d) (c : ℂ) (ξ : Euclidean d) :
    CompactTests d where
  toFun x := χ x * Complex.exp (c * (inner ℝ x ξ : ℝ))
  contDiff' := χ.contDiff.mul (Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const))))
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := Set.subset_univ _

@[simp] lemma oscillatoryTest_apply {d : ℕ} (χ : CompactTests d) (c : ℂ)
    (ξ x : Euclidean d) : oscillatoryTest χ c ξ x =
    χ x * Complex.exp (c * (inner ℝ x ξ : ℝ)) := rfl

lemma schwartz_lineDeriv_oscillatoryTest {d : ℕ} (χ : CompactTests d) (c : ℂ)
    (ξ : Euclidean d) (i : Fin d) :
    lineDerivOp (basisVector i) (testToSchwartz (oscillatoryTest χ c ξ)) =
      testToSchwartz (oscillatoryTest (TestFunction.lineDerivCLM ℂ (basisVector i) χ) c ξ) +
      (c * (ξ i : ℂ)) • testToSchwartz (oscillatoryTest χ c ξ) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp only [testToSchwartz_apply, oscillatoryTest_apply, add_apply, smul_apply, smul_eq_mul]
  have hχ := (χ.contDiff.differentiable (by simp)).differentiableAt (x := x)
  have hp := ((Complex.ofRealCLM.hasFDerivAt).comp x
    ((hasFDerivAt_id x).inner ℝ (hasFDerivAt_const ξ x))).const_mul c
  have he := hp.cexp
  have hh := congrArg (fun f : Euclidean d →L[ℝ] ℂ => f (basisVector i))
    (hχ.hasFDerivAt.mul he).fderiv
  change (fderiv ℝ (⇑χ * fun y => Complex.exp (c * (inner ℝ y ξ : ℝ)))) x (basisVector i) = _
  dsimp only [Function.comp_def, id_eq, Complex.ofRealCLM_apply] at hh
  rw [hh]
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp), hχ.lineDeriv_eq_fderiv]
  simp only [add_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_apply,
    ContinuousLinearMap.id_apply, zero_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, inner_zero_right, zero_add,
    ]
  have hid : inner ℝ (basisVector i) ξ = ξ i := by
    exact (real_inner_comm ξ (basisVector i)).trans (inner_basisVector ξ i)
  rw [hid]
  simp only [smul_eq_mul]
  ring



lemma oscillatory_word_bcf_contDiff {d : ℕ} (χ : CompactTests d) (c : ℂ)
    (n : ℕ) (b : Fin n → Fin d) :
    ContDiff ℝ ∞ (fun ξ => (iteratedLineDerivOp (fun j => basisVector (b j))
      (testToSchwartz (oscillatoryTest χ c ξ))).toBoundedContinuousFunction) := by
  induction n generalizing χ with
  | zero =>
    obtain ⟨F, hF, hFx⟩ := cutoff_exponential_bcf_contDiff χ c
    convert hF using 1
    funext ξ
    ext x
    exact (hFx ξ x).symm
  | succ n ih =>
    let χ' : CompactTests d := TestFunction.lineDerivCLM ℂ (basisVector (b (Fin.last n))) χ
    have h₁ := ih χ' (Fin.init b)
    have h₂ := ih χ (Fin.init b)
    have hs : ContDiff ℝ ∞ (fun ξ : Euclidean d => c * (ξ (b (Fin.last n)) : ℂ)) :=
      contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (EuclideanSpace.proj (𝕜 := ℝ) (b (Fin.last n))).contDiff)
    convert h₁.add (hs.smul h₂) using 1
    funext ξ
    ext x
    simp only [BoundedContinuousFunction.add_apply, SchwartzMap.toBoundedContinuousFunction_apply,
      iteratedLineDerivOp_succ_right]
    rw [schwartz_lineDeriv_oscillatoryTest, iteratedLineDerivOp_add,
      iteratedLineDerivOp_smul]
    rfl



def coordinateTensor {d n : ℕ} (b : Fin n → Fin d) : Euclidean d [×n]→L[ℝ] ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℂ).compContinuousLinearMap
    (fun j => Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (b j)))

@[simp] lemma coordinateTensor_apply {d n : ℕ} (b : Fin n → Fin d)
    (v : Fin n → Euclidean d) : coordinateTensor b v = ∏ j, ((v j (b j) : ℝ) : ℂ) := rfl

lemma multilinear_coordinate_expansion {d n : ℕ} (A : Euclidean d [×n]→L[ℝ] ℂ) :
    A = ∑ b : Fin n → Fin d, (A (fun j => basisVector (b j))) • coordinateTensor b := by
  ext v
  simp only [sum_apply, smul_apply,
    coordinateTensor_apply, smul_eq_mul]
  calc
    A v = A (fun j => ∑ i, v j i • basisVector i) := by simp only [basis_expansion]
    _ = ∑ b : Fin n → Fin d, A (fun j => v j (b j) • basisVector (b j)) := A.toMultilinearMap.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [A.map_smul_univ]
      simp only [Complex.real_smul, Complex.ofReal_prod]
      ring

def bcfTensorCLM {d n : ℕ} (b : Fin n → Fin d) :
    (Euclidean d →ᵇ ℂ) →L[ℂ] (Euclidean d →ᵇ (Euclidean d [×n]→L[ℝ] ℂ)) :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (coordinateTensor b)).compLeftContinuousBounded _

def oscillatoryCompact {d : ℕ} (χ : CompactTests d) : TopologicalSpace.Compacts (Euclidean d) :=
  ⟨tsupport χ, χ.hasCompactSupport⟩

def oscillatorySupported {d : ℕ} (χ : CompactTests d) (c : ℂ) (ξ : Euclidean d) :
    ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ (oscillatoryCompact χ) :=
  ContDiffMapSupportedIn.of_support_subset (oscillatoryTest χ c ξ).contDiff
    ((Function.support_mul_subset_left _ _).trans subset_closure)

@[simp] lemma oscillatorySupported_apply {d : ℕ} (χ : CompactTests d) (c : ℂ)
    (ξ x : Euclidean d) : oscillatorySupported χ c ξ x =
    χ x * Complex.exp (c * (inner ℝ x ξ : ℝ)) := rfl



abbrev CoordinateJetSpace (d : ℕ) (s : Finset ℕ) :=
  ∀ i : (↑(insert 0 s) : Set ℕ), (Fin (i : ℕ) → Fin d) → Euclidean d →ᵇ ℂ

def reconstructCompactJets {d : ℕ} (s : Finset ℕ) :
    CoordinateJetSpace d s →L[ℂ] CompactJetSpace d s :=
  ContinuousLinearMap.pi (fun i => ∑ b : Fin (i : ℕ) → Fin d,
    (bcfTensorCLM b).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (i : ℕ) → Fin d => Euclidean d →ᵇ ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun i : (↑(insert 0 s) : Set ℕ) => (Fin (i : ℕ) → Fin d) → Euclidean d →ᵇ ℂ) i)))

lemma compact_oscillatory_pairing_contDiff {d : ℕ} (u : Distribution d)
    (χ : CompactTests d) (c : ℂ) :
    ContDiff ℝ ∞ (fun ξ => u (oscillatoryTest χ c ξ)) := by
  obtain ⟨s, L, hL⟩ := compactJet_factorization u (oscillatoryCompact χ)
  let F : Euclidean d → CoordinateJetSpace d s := fun ξ i b =>
    (iteratedLineDerivOp (fun j => basisVector (b j))
      (testToSchwartz (oscillatoryTest χ c ξ))).toBoundedContinuousFunction
  have hF : ContDiff ℝ ∞ F :=
    contDiff_pi.2 (fun i => contDiff_pi.2 (fun b => oscillatory_word_bcf_contDiff χ c i b))
  let G : CoordinateJetSpace d s →L[ℝ] ℂ := (L.comp (reconstructCompactJets s)).restrictScalars ℝ
  have h := G.contDiff.comp hF
  convert h using 1
  funext ξ
  change u (TestFunction.ofSupportedIn (Set.subset_univ _) (oscillatorySupported χ c ξ)) =
    L (reconstructCompactJets s (F ξ))
  rw [hL (oscillatorySupported χ c ξ)]
  apply congrArg L
  funext i
  apply BoundedContinuousFunction.ext
  intro x
  change (ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ (i : ℕ)
    (oscillatorySupported χ c ξ)) x = _
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  simp only [reconstructCompactJets, ContinuousLinearMap.pi_apply, sum_apply]
  change iteratedFDeriv ℝ (i : ℕ) (oscillatorySupported χ c ξ) x =
    (BoundedContinuousFunction.evalCLM ℝ (β := Euclidean d [×(i : ℕ)]→L[ℝ] ℂ) x) _
  rw [map_sum]
  change iteratedFDeriv ℝ (i : ℕ) (oscillatorySupported χ c ξ) x =
    ∑ b : Fin (i : ℕ) → Fin d, _
  rw [multilinear_coordinate_expansion (iteratedFDeriv ℝ (i : ℕ) (oscillatorySupported χ c ξ) x)]
  apply Finset.sum_congr rfl
  intro b _
  change _ = (iteratedLineDerivOp (fun j => basisVector (b j))
    (testToSchwartz (oscillatoryTest χ c ξ))) x • coordinateTensor b
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  rfl



def coordinateJetMap {d : ℕ} (K : TopologicalSpace.Compacts (Euclidean d)) (s : Finset ℕ) :
    ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K →ₗ[ℂ] CoordinateJetSpace d s :=
  LinearMap.pi (fun _i => LinearMap.pi (fun b =>
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Euclidean d) ℂ).toLinearMap.comp
      ((iteratedLineDerivOpCLM ℂ (Schwartz ℂ d) (fun j => basisVector (b j))).toLinearMap.comp
        (testToSchwartzLM.comp (TestFunction.ofSupportedInCLM ℂ (Set.subset_univ (K : Set (Euclidean d)))).toLinearMap))))

@[simp] lemma coordinateJetMap_apply {d : ℕ} (K : TopologicalSpace.Compacts (Euclidean d)) (s : Finset ℕ)
    (φ : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K) (i : (↑(insert 0 s) : Set ℕ))
    (b : Fin (i : ℕ) → Fin d) :
    coordinateJetMap K s φ i b = (iteratedLineDerivOp (fun j => basisVector (b j))
      (testToSchwartz (TestFunction.ofSupportedIn (Set.subset_univ _) φ))).toBoundedContinuousFunction := rfl

lemma reconstruct_coordinateJetMap {d : ℕ} (K : TopologicalSpace.Compacts (Euclidean d))
    (s : Finset ℕ) (φ : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K) :
    reconstructCompactJets s (coordinateJetMap K s φ) = compactJetMap K s φ := by
  funext i
  apply BoundedContinuousFunction.ext
  intro x
  change _ = (ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ (i : ℕ) φ) x
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  symm
  simp only [reconstructCompactJets, ContinuousLinearMap.pi_apply, sum_apply]
  change iteratedFDeriv ℝ (i : ℕ) φ x =
    (BoundedContinuousFunction.evalCLM ℝ (β := Euclidean d [×(i : ℕ)]→L[ℝ] ℂ) x) _
  rw [map_sum]
  rw [multilinear_coordinate_expansion (iteratedFDeriv ℝ (i : ℕ) φ x)]
  apply Finset.sum_congr rfl
  intro b _
  change _ = (iteratedLineDerivOp (fun j => basisVector (b j))
    (testToSchwartz (TestFunction.ofSupportedIn (Set.subset_univ _) φ))) x • coordinateTensor b
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  rfl

lemma coordinateJet_factorization {d : ℕ} (u : Distribution d)
    (K : TopologicalSpace.Compacts (Euclidean d)) :
    ∃ (s : Finset ℕ) (L : CoordinateJetSpace d s →L[ℂ] ℂ),
      ∀ φ : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K,
        u (TestFunction.ofSupportedIn (Set.subset_univ _) φ) = L (coordinateJetMap K s φ) := by
  obtain ⟨s, L, hL⟩ := compactJet_factorization u K
  refine ⟨s, L.comp (reconstructCompactJets s), fun φ => ?_⟩
  rw [ContinuousLinearMap.comp_apply, reconstruct_coordinateJetMap]
  exact hL φ


/-- The compact test obtained by removing a compact cutoff. -/
def exteriorTest {d : ℕ} (χ φ : CompactTests d) : CompactTests d :=
  φ - cutoffToTestsCLM χ (testToSchwartz φ)

@[simp] lemma exteriorTest_apply {d : ℕ} (χ φ : CompactTests d) (x : Euclidean d) :
    exteriorTest χ φ x = (1 - χ x) * φ x := by
  simp only [exteriorTest, sub_apply, cutoffToTestsCLM_apply, testToSchwartz_apply]
  ring

lemma testToSchwartz_exteriorTest {d : ℕ} (χ φ : CompactTests d) :
    testToSchwartz (exteriorTest χ φ) =
      testToSchwartz φ - SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ)
        (testToSchwartz φ) := by
  have hg : (χ : Euclidean d → ℂ).HasTemperateGrowth :=
    (testToSchwartz χ).hasTemperateGrowth
  ext x
  rw [testToSchwartz_apply, exteriorTest_apply, sub_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg]
  simp only [testToSchwartz_apply, smul_eq_mul]
  ring

lemma exteriorTest_support {d : ℕ} (χ φ : CompactTests d)
    (hχ : ∀ᶠ x in 𝓝 (0 : Euclidean d), χ x = 1) :
    tsupport (exteriorTest χ φ) ⊆ ({0}ᶜ : Set (Euclidean d)) := by
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hx0
  subst x
  have hz : (0 : Euclidean d) ∉ tsupport (exteriorTest χ φ) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hχ] with y hy
    simp only [exteriorTest_apply, hy, sub_self, zero_mul, Pi.zero_apply]
  exact hz hx

lemma contDiff_exteriorKernel {d : ℕ} (χ : CompactTests d) (k : Euclidean d → ℂ)
    (hχ : ∀ᶠ x in 𝓝 (0 : Euclidean d), χ x = 1)
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d))) :
    ContDiff ℝ ∞ (fun x => (1 - χ x) * k x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hχ] with y hy
    simp only [hy, sub_self, zero_mul]
  · have hkn : ContDiffAt ℝ ∞ k x :=
      hk.contDiffAt (isOpen_compl_singleton.mem_nhds hx)
    exact (contDiffAt_const.sub (χ.contDiff.of_le (by simp)).contDiffAt).mul hkn

/-- Removing a cutoff equal to one near zero turns a smooth punctured-space
representative into a globally smooth representative, on every compact test. -/
theorem exterior_regular_representation {d : ℕ} (v : Tempered ℂ d)
    (χ : CompactTests d) (hχ : ∀ᶠ x in 𝓝 (0 : Euclidean d), χ x = 1)
    {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz φ) = ∫ x, k x * φ x) :
    ContDiff ℝ ∞ (fun x => (1 - χ x) * k x) ∧
      ∀ φ : CompactTests d,
        (v - v.comp (SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ)))
          (testToSchwartz φ) = ∫ x, ((1 - χ x) * k x) * φ x := by
  refine ⟨contDiff_exteriorKernel χ k hχ hk, ?_⟩
  intro φ
  have h := hkv (exteriorTest χ φ) (exteriorTest_support χ φ hχ)
  rw [testToSchwartz_exteriorTest, map_sub] at h
  change v (testToSchwartz φ) -
    v (SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ) (testToSchwartz φ)) = _
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [exteriorTest_apply]
  ring

/-- The compact part annihilates tests whose support misses its cutoff. -/
lemma cutoff_tempered_vanishes_of_disjoint {d : ℕ} (v : Tempered ℂ d)
    (χ φ : CompactTests d) (h : Disjoint (tsupport χ) (tsupport φ)) :
    (v.comp (SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ)))
      (testToSchwartz φ) = 0 := by
  have hg : (χ : Euclidean d → ℂ).HasTemperateGrowth :=
    (testToSchwartz χ).hasTemperateGrowth
  have hz : SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ)
      (testToSchwartz φ) = 0 := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    simp only [testToSchwartz_apply, smul_eq_mul, zero_apply]
    by_cases hc : χ x = 0
    · simp only [hc, zero_mul]
    · have hx : x ∈ tsupport χ := subset_closure hc
      have hp : φ x = 0 := by
        by_contra hp
        exact Set.disjoint_left.mp h hx (subset_closure hp)
      simp only [hp, mul_zero]
  change v (SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ)
    (testToSchwartz φ)) = 0
  rw [hz, map_zero]

/-- A smooth punctured representative gives the exterior part a globally smooth
kernel, vanishing in a neighborhood of zero. No homogeneity is needed here. -/
theorem exists_smooth_exterior_representative {d : ℕ} (v : Tempered ℂ d)
    (χ : CompactTests d) (hχ : ∀ᶠ x in 𝓝 (0 : Euclidean d), χ x = 1)
    (hv : TemperedSmoothAwayZero v) :
    ∃ g : Euclidean d → ℂ, ContDiff ℝ ∞ g ∧
      (g =ᶠ[𝓝 0] 0) ∧
      ∀ φ : CompactTests d,
        (v - v.comp (SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ)))
          (testToSchwartz φ) = ∫ x, g x * φ x := by
  obtain ⟨k, hk, hkv⟩ := hv
  have he := exterior_regular_representation v χ hχ hk hkv
  refine ⟨fun x => (1 - χ x) * k x, he.1, ?_, he.2⟩
  filter_upwards [hχ] with x hx
  simp only [hx, sub_self, zero_mul, Pi.zero_apply]


/-- The punctured zero-dimensional space is empty, so its smoothness condition
holds for every tempered distribution. -/
theorem temperedSmoothAwayZero_zero_dim (v : Tempered ℂ 0) :
    TemperedSmoothAwayZero v := by
  refine ⟨fun _ => 0, contDiffOn_const, ?_⟩
  intro φ hφ
  have hz : φ = 0 := by
    ext x
    have hx : x = 0 := Subsingleton.elim x 0
    by_contra hn
    have ht : x ∈ tsupport φ := subset_closure hn
    exact hφ ht hx
  have hzS : testToSchwartz (0 : CompactTests 0) = 0 := by ext x; rfl
  simp only [hz, hzS, map_zero, zero_mul, integral_zero]

/-- In dimension zero, compact localization at a cutoff equal to one at the only
point extends every distribution to Schwartz space. -/
theorem exists_tempered_extension_zero_dim (u : Distribution 0) :
    ∃ v : Tempered ℂ 0, Extends v u := by
  obtain ⟨χ, hχ⟩ := exists_test_one_at_zero 0
  refine ⟨localizedTempered u χ, ?_⟩
  intro φ
  change u (cutoffToTestsCLM χ (testToSchwartz φ)) = u φ
  congr 1
  ext x
  rw [cutoffToTestsCLM_apply, testToSchwartz_apply]
  have hx : x = 0 := Subsingleton.elim x 0
  rw [hx, hχ, one_mul]

/-- The full extension conclusion for the zero-dimensional source case. -/
theorem tempered_extension_zero_dim (z : ℂ) (u : Distribution 0)
    (hu : IsHomogeneous u z) :
    ∃ v : Tempered ℂ 0, Extends v u ∧ IsTemperedHomogeneous v z := by
  obtain ⟨v, hv⟩ := exists_tempered_extension_zero_dim u
  exact ⟨v, hv, temperedHomogeneous_of_extension hu hv⟩

/-- The zero-dimensional forward implication has no analytic obstruction. -/
theorem fourier_smooth_forward_zero_dim (z : ℂ) (v : Tempered ℂ 0)
    (_hv : IsTemperedHomogeneous v z) (_hs : TemperedSmoothAwayZero v) :
    TemperedSmoothAwayZero (temperedFourier v) :=
  temperedSmoothAwayZero_zero_dim _


/-- The complete source assertion in its zero-dimensional case. -/
theorem homogeneous_fourier_zero_dim (z : ℂ) (u : Distribution 0)
    (hu : IsHomogeneous u z) :
    ∃ v : Tempered ℂ 0, Extends v u ∧ IsTemperedHomogeneous v z ∧
      IsTemperedHomogeneous (temperedFourier v) (-(0 : ℂ) - z) ∧
      (SmoothAwayZero u ↔ TemperedSmoothAwayZero (temperedFourier v)) := by
  obtain ⟨v, hvu, hv⟩ := tempered_extension_zero_dim z u hu
  refine ⟨v, hvu, hv, ?_, ?_⟩
  · simpa only [Nat.cast_zero] using fourier_degree 0 z v hv
  · exact iff_of_true ((smoothAwayZero_extension hvu).mpr
      (temperedSmoothAwayZero_zero_dim v))
      (temperedSmoothAwayZero_zero_dim (temperedFourier v))


/-- Smoothness and power bounds for all derivatives outside one compact set
imply temperate growth. Each exponent may be real and may depend on the order. -/
lemma hasTemperateGrowth_of_derivative_tail_bound {d : ℕ}
    {g : Euclidean d → ℂ} (hg : ContDiff ℝ ∞ g)
    (K : Set (Euclidean d)) (hK : IsCompact K)
    (hbound : ∀ n : ℕ, ∃ (C : ℝ) (r : ℝ), 0 ≤ C ∧
      ∀ x, x ∉ K → ‖iteratedFDeriv ℝ n g x‖ ≤ C * ‖x‖ ^ r) :
    g.HasTemperateGrowth := by
  refine ⟨hg, ?_⟩
  intro n
  let K' : Set (Euclidean d) := K ∪ Metric.closedBall 0 1
  have hK' : IsCompact K' := hK.union (isCompact_closedBall 0 1)
  obtain ⟨A, hA⟩ := hK'.exists_bound_of_continuousOn
    ((hg.continuous_iteratedFDeriv (by simp)).continuousOn :
      ContinuousOn (iteratedFDeriv ℝ n g) K')
  obtain ⟨C, r, hC, hCr⟩ := hbound n
  obtain ⟨m, hm⟩ := exists_nat_ge r
  let B : ℝ := max (max A C) 0
  have hB : 0 ≤ B := le_max_right _ _
  have hAB : A ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hCB : C ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨m, B, fun x => ?_⟩
  by_cases hxK : x ∈ K'
  · calc
      ‖iteratedFDeriv ℝ n g x‖ ≤ A := hA x hxK
      _ ≤ B := hAB
      _ ≤ B * (1 + ‖x‖) ^ m := by
        exact le_mul_of_one_le_right hB (one_le_pow₀ (by linarith [norm_nonneg x]))
  · have hx : x ∉ K := fun hx => hxK (Or.inl hx)
    have hn : 1 < ‖x‖ := by
      have hxball : x ∉ Metric.closedBall (0 : Euclidean d) 1 := fun hx => hxK (Or.inr hx)
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxball
    calc
      ‖iteratedFDeriv ℝ n g x‖ ≤ C * ‖x‖ ^ r := hCr x hx
      _ ≤ B * (1 + ‖x‖) ^ m := by
        apply mul_le_mul hCB ?_ (Real.rpow_nonneg (norm_nonneg _) _) hB
        calc
          ‖x‖ ^ r ≤ ‖x‖ ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hn.le hm
          _ = ‖x‖ ^ m := Real.rpow_natCast _ _
          _ ≤ (1 + ‖x‖) ^ m := by gcongr; linarith


/-- A smooth homogeneous representative cut off near the origin has temperate
growth, including every derivative. -/
theorem exteriorKernel_hasTemperateGrowth {d : ℕ} {z : ℂ}
    {v : Tempered ℂ d} (hv : IsTemperedHomogeneous v z)
    {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz φ) = ∫ x, k x * φ x)
    (χ : CompactTests d) (hχ : ∀ᶠ x in 𝓝 (0 : Euclidean d), χ x = 1) :
    (fun x => (1 - χ x) * k x).HasTemperateGrowth := by
  apply hasTemperateGrowth_of_derivative_tail_bound
    (contDiff_exteriorKernel χ k hχ hk) (tsupport χ ∪ {0})
    (χ.hasCompactSupport.union isCompact_singleton)
  intro n
  obtain ⟨C, hC, hbound⟩ := exteriorKernel_derivative_norm_bound hv hk hkv χ n
  refine ⟨C, z.re - (n : ℝ), hC, fun x hx => ?_⟩
  exact hbound x (fun hx0 => hx (Or.inr hx0)) (fun hχx => hx (Or.inl hχx))

/-- Integration against a temperate-growth kernel is a continuous functional on
the actual Schwartz space used in the Fourier interface. -/
def regularTemperedOfGrowth {d : ℕ} (g : Euclidean d → ℂ)
    (_hg : g.HasTemperateGrowth) : Tempered ℂ d :=
  (SchwartzMap.integralCLM ℂ (volume : Measure (Euclidean d))).comp
    (SchwartzMap.smulLeftCLM ℂ g)

@[simp] lemma regularTemperedOfGrowth_apply {d : ℕ} (g : Euclidean d → ℂ)
    (hg : g.HasTemperateGrowth) (φ : Schwartz ℂ d) :
    regularTemperedOfGrowth g hg φ = ∫ x, g x * φ x := by
  change (∫ x, (SchwartzMap.smulLeftCLM ℂ g φ) x) = _
  apply integral_congr_ae
  filter_upwards [] with x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  rfl

/-- The exact compact-test exterior representation extends to equality of the
continuous Schwartz duals by density. -/
theorem exterior_eq_regularTemperedOfGrowth {d : ℕ} {z : ℂ}
    {v : Tempered ℂ d} (hv : IsTemperedHomogeneous v z)
    {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz φ) = ∫ x, k x * φ x)
    (χ : CompactTests d) (hχ : ∀ᶠ x in 𝓝 (0 : Euclidean d), χ x = 1) :
    v - v.comp (SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ)) =
      regularTemperedOfGrowth (fun x => (1 - χ x) * k x)
        (exteriorKernel_hasTemperateGrowth hv hk hkv χ hχ) := by
  apply DFunLike.ext'
  apply (denseRange_testToSchwartz d).equalizer
    (v - v.comp (SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ))).continuous
    (regularTemperedOfGrowth _ (exteriorKernel_hasTemperateGrowth hv hk hkv χ hχ)).continuous
  funext φ
  simp only [Function.comp_apply, regularTemperedOfGrowth_apply, testToSchwartz_apply]
  exact (exterior_regular_representation v χ hχ hk hkv).2 φ

/-- The exterior decomposition is an integral identity on every Schwartz test. -/
theorem exterior_schwartz_pairing {d : ℕ} {z : ℂ}
    {v : Tempered ℂ d} (hv : IsTemperedHomogeneous v z)
    {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz φ) = ∫ x, k x * φ x)
    (χ : CompactTests d) (hχ : ∀ᶠ x in 𝓝 (0 : Euclidean d), χ x = 1)
    (φ : Schwartz ℂ d) :
    v φ - v (SchwartzMap.smulLeftCLM ℂ (χ : Euclidean d → ℂ) φ) =
      ∫ x, ((1 - χ x) * k x) * φ x := by
  have h := congrArg (fun w : Tempered ℂ d => w φ)
    (exterior_eq_regularTemperedOfGrowth hv hk hkv χ hχ)
  simpa only [sub_apply, ContinuousLinearMap.comp_apply,
    regularTemperedOfGrowth_apply] using h



lemma norm_rpow_le_one_add_norm_rpow {t r : ℝ} (ht : 1 ≤ t) (hr : r ≤ 0) :
    t ^ r ≤ (2 : ℝ) ^ (-r) * (1 + t) ^ r := by
  have hp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  calc
    t ^ r = (2 : ℝ) ^ (-r) * (2 * t) ^ r := by
      rw [Real.mul_rpow (by norm_num) hp.le, ← mul_assoc,
        ← Real.rpow_add (by norm_num)]
      simp only [neg_add_cancel, Real.rpow_zero, one_mul]
    _ ≤ (2 : ℝ) ^ (-r) * (1 + t) ^ r := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (x := 1 + t) (y := 2 * t)
          (by linarith) (by linarith) hr) (Real.rpow_nonneg (by norm_num) _)

/-- A continuous function whose tail is dominated by a radial power strictly
below minus the dimension is integrable. The compact interior needs no bound
from the homogeneous kernel. -/
theorem integrable_of_norm_rpow_tail_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {f : Euclidean d → F} (hf : Continuous f)
    (K : Set (Euclidean d)) (hK : IsCompact K) (C r : ℝ) (hC : 0 ≤ C)
    (hr : r < -(d : ℝ))
    (hbound : ∀ x, x ∉ K → ‖f x‖ ≤ C * ‖x‖ ^ r) : Integrable f := by
  let K' : Set (Euclidean d) := K ∪ Metric.closedBall 0 1
  have hK' : IsCompact K' := hK.union (isCompact_closedBall 0 1)
  have hinside : IntegrableOn f K' := hf.continuousOn.integrableOn_compact hK'
  have hJ : Integrable (fun x : Euclidean d => (1 + ‖x‖) ^ r) := by
    have hdim : (Module.finrank ℝ (Euclidean d) : ℝ) < -r := by
      simp only [Euclidean, finrank_euclideanSpace_fin]
      linarith
    simpa only [neg_neg] using
      (integrable_one_add_norm (E := Euclidean d) (μ := volume) hdim)
  have hr0 : r ≤ 0 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have houtside : IntegrableOn f K'ᶜ := by
    apply ((hJ.const_mul (C * (2 : ℝ) ^ (-r))).integrableOn).mono'
      hf.aestronglyMeasurable.restrict
    filter_upwards [self_mem_ae_restrict hK'.measurableSet.compl] with x hx
    have hxK : x ∉ K := fun hxK => hx (Or.inl hxK)
    have ht : 1 < ‖x‖ := by
      have hxball : x ∉ Metric.closedBall (0 : Euclidean d) 1 := fun hxball => hx (Or.inr hxball)
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxball
    calc
      ‖f x‖ ≤ C * ‖x‖ ^ r := hbound x hxK
      _ ≤ C * ((2 : ℝ) ^ (-r) * (1 + ‖x‖) ^ r) :=
        mul_le_mul_of_nonneg_left (norm_rpow_le_one_add_norm_rpow ht.le hr0) hC
      _ = (C * (2 : ℝ) ^ (-r)) * (1 + ‖x‖) ^ r := (mul_assoc _ _ _).symm
  simpa only [Set.union_compl_self, integrableOn_univ] using hinside.union houtside


/-- Polynomially weighted derivatives of the smooth exterior kernel are
integrable once the total tail degree is strictly below minus the dimension. -/
theorem exteriorKernel_integrable_derivative_moment {d : ℕ} {z : ℂ}
    {v : Tempered ℂ d} (hv : IsTemperedHomogeneous v z)
    {k : Euclidean d → ℂ}
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)))
    (hkv : ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      v (testToSchwartz φ) = ∫ x, k x * φ x)
    (χ : CompactTests d) (hχ : ∀ᶠ x in 𝓝 (0 : Euclidean d), χ x = 1)
    (m n : ℕ) (hdecay : z.re + (m : ℝ) - (n : ℝ) < -(d : ℝ)) :
    Integrable (fun x => ‖x‖ ^ m *
      ‖iteratedFDeriv ℝ n (fun y => (1 - χ y) * k y) x‖) := by
  have hg := contDiff_exteriorKernel χ k hχ hk
  have hD := hg.continuous_iteratedFDeriv (m := n) (by simp)
  obtain ⟨C, hC, hbound⟩ := exteriorKernel_derivative_norm_bound hv hk hkv χ n
  apply integrable_of_norm_rpow_tail_bound
    ((continuous_norm.pow m).mul hD.norm) (tsupport χ ∪ {0})
    (χ.hasCompactSupport.union isCompact_singleton) C
    (z.re + (m : ℝ) - (n : ℝ)) hC hdecay
  intro x hx
  have hx0 : x ≠ 0 := fun hx0 => hx (Or.inr hx0)
  have hχx : x ∉ tsupport χ := fun hχx => hx (Or.inl hχx)
  have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
  calc
    ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (fun y => (1 - χ y) * k y) x‖ ≤
        ‖x‖ ^ m * (C * ‖x‖ ^ (z.re - (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbound x hx0 hχx) (pow_nonneg (norm_nonneg _) _)
    _ = C * (‖x‖ ^ m * ‖x‖ ^ (z.re - (n : ℝ))) := by ring
    _ = C * ‖x‖ ^ (z.re + (m : ℝ) - (n : ℝ)) := by
      rw [← Real.rpow_natCast ‖x‖ m, ← Real.rpow_add ht]
      congr 2
      ring



open LineDeriv

abbrev OscillatoryWordField {d n : ℕ} (χ : CompactTests d) (c : ℂ)
    (b : Fin n → Fin d) (ξ : Euclidean d) : Euclidean d →ᵇ ℂ :=
  (iteratedLineDerivOp (fun j => basisVector (b j))
    (testToSchwartz (oscillatoryTest χ c ξ))).toBoundedContinuousFunction

lemma oscillatory_word_field_succ {d n : ℕ} (χ : CompactTests d) (c : ℂ)
    (b : Fin (n + 1) → Fin d) (ξ : Euclidean d) :
    OscillatoryWordField χ c b ξ =
      OscillatoryWordField (TestFunction.lineDerivCLM ℂ (basisVector (b (Fin.last n))) χ)
        c (Fin.init b) ξ +
      (c * (ξ (b (Fin.last n)) : ℂ)) • OscillatoryWordField χ c (Fin.init b) ξ := by
  ext x
  simp only [OscillatoryWordField, SchwartzMap.toBoundedContinuousFunction_apply,
    iteratedLineDerivOp_succ_right, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply]
  rw [schwartz_lineDeriv_oscillatoryTest, iteratedLineDerivOp_add,
    iteratedLineDerivOp_smul]
  rfl


lemma oscillatory_word_field_integrable {d : ℕ} (χ : CompactTests d) (c : ℂ)
    (hc : c.re = 0) (n : ℕ) (b : Fin n → Fin d) (φ : Schwartz ℂ d) :
    Integrable (fun ξ => φ ξ • OscillatoryWordField χ c b ξ) := by
  induction n generalizing χ φ with
  | zero =>
    have hnorm : ∀ ξ, ‖OscillatoryWordField χ c b ξ‖ ≤
        SchwartzMap.seminorm ℂ 0 0 (testToSchwartz χ) := by
      intro ξ
      apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).2
      intro x
      simp only [OscillatoryWordField, iteratedLineDerivOp_fin_zero,
        SchwartzMap.toBoundedContinuousFunction_apply, testToSchwartz_apply,
        oscillatoryTest_apply, norm_mul, Complex.norm_exp, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hc, zero_mul,
        Real.exp_zero, mul_one]
      exact (testToSchwartz χ).norm_le_seminorm ℂ x
    have hcont : Continuous (fun ξ => φ ξ • OscillatoryWordField χ c b ξ) :=
      φ.continuous.smul (oscillatory_word_bcf_contDiff χ c 0 b).continuous
    apply (φ.integrable.norm.mul_const
      (SchwartzMap.seminorm ℂ 0 0 (testToSchwartz χ))).mono' hcont.aestronglyMeasurable
    filter_upwards [] with ξ
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hnorm ξ) (norm_nonneg _)
  | succ n ih =>
    let i : Fin d := b (Fin.last n)
    let χ' : CompactTests d := TestFunction.lineDerivCLM ℂ (basisVector i) χ
    have h₁ := ih χ' (Fin.init b) φ
    have h₂ := ih χ (Fin.init b) (coordinateMultiply i φ)
    convert h₁.add (h₂.smul c) using 1
    funext ξ
    rw [oscillatory_word_field_succ, smul_add]
    congr 1
    change φ ξ • ((c * (ξ i : ℂ)) • OscillatoryWordField χ c (Fin.init b) ξ) =
      c • (((coordinateMultiply i φ) ξ) • OscillatoryWordField χ c (Fin.init b) ξ)
    have hval : (coordinateMultiply i φ) ξ = (ξ i : ℂ) * φ ξ :=
      SchwartzMap.smulLeftCLM_apply_apply (coordinate_growth (𝕜 := ℂ) i) φ ξ
    rw [hval]
    simp only [smul_smul]
    congr 1
    ring


abbrev localizedFourierSchwartz {d : ℕ} (χ : CompactTests d) (φ : Schwartz ℂ d) :
    Schwartz ℂ d := testToSchwartz (cutoffToTestsCLM χ (schwartzFourier φ))

lemma schwartz_lineDeriv_localizedFourier {d : ℕ} (χ : CompactTests d)
    (φ : Schwartz ℂ d) (i : Fin d) :
    lineDerivOp (basisVector i) (localizedFourierSchwartz χ φ) =
      localizedFourierSchwartz (TestFunction.lineDerivCLM ℂ (basisVector i) χ) φ +
      (-(2 * (Real.pi : ℂ) * Complex.I)) •
        localizedFourierSchwartz χ (coordinateMultiply i φ) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp only [localizedFourierSchwartz, testToSchwartz_apply, cutoffToTestsCLM_apply,
    add_apply, smul_apply, smul_eq_mul]
  have hχ := (χ.contDiff.differentiable (by simp)).differentiableAt (x := x)
  have hF := (schwartzFourier φ).differentiableAt (x := x)
  have hh := congrArg (fun f : Euclidean d →L[ℝ] ℂ => f (basisVector i))
    (hχ.hasFDerivAt.mul hF.hasFDerivAt).fderiv
  have heq : (⇑(testToSchwartz (cutoffToTestsCLM χ (schwartzFourier φ))) : Euclidean d → ℂ) =
      ⇑χ * ⇑(schwartzFourier φ) := by
    ext y
    simp only [testToSchwartz_apply, cutoffToTestsCLM_apply, Pi.mul_apply]
  rw [heq]
  rw [hh]
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp), hχ.lineDeriv_eq_fderiv]
  have hFd := congrArg (fun f : Schwartz ℂ d => f x) (schwartz_partial_fourier i φ)
  simp only [lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] at hFd
  simp only [smul_apply, smul_eq_mul] at hFd
  simp only [add_apply, smul_apply]
  rw [hFd]
  simp only [smul_eq_mul]
  ring


lemma oscillatory_word_field_integral {d : ℕ} (χ : CompactTests d)
    (n : ℕ) (b : Fin n → Fin d) (φ : Schwartz ℂ d) :
    (∫ ξ, φ ξ • OscillatoryWordField χ (-(2 * (Real.pi : ℂ) * Complex.I)) b ξ) =
      (iteratedLineDerivOp (fun j => basisVector (b j))
        (localizedFourierSchwartz χ φ)).toBoundedContinuousFunction := by
  let c : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)
  have hc : c.re = 0 := by simp [c]
  change (∫ ξ, φ ξ • OscillatoryWordField χ c b ξ) = _
  induction n generalizing χ φ with
  | zero =>
    ext x
    have heval := (BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm
      (oscillatory_word_field_integrable χ c hc 0 b φ)
    calc
      (∫ ξ, φ ξ • OscillatoryWordField χ c b ξ) x =
          ∫ ξ, φ ξ * (χ x * Complex.exp (c * (inner ℝ x ξ : ℝ))) := by
        simpa only [BoundedContinuousFunction.evalCLM_apply, map_smul,
          OscillatoryWordField, iteratedLineDerivOp_fin_zero,
          BoundedContinuousFunction.smul_apply, SchwartzMap.toBoundedContinuousFunction_apply,
          testToSchwartz_apply, oscillatoryTest_apply, smul_eq_mul] using heval.symm
      _ = χ x * (schwartzFourier φ) x := by
        rw [schwartz_integral, integralFourier, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with ξ
        have hexp : c * (inner ℝ x ξ : ℝ) =
            -2 * (Real.pi : ℂ) * Complex.I * (inner ℝ ξ x : ℝ) := by
          rw [real_inner_comm ξ x]
          dsimp [c]
          ring
        rw [hexp]
        ring
      _ = _ := by
        simp only [iteratedLineDerivOp_fin_zero, SchwartzMap.toBoundedContinuousFunction_apply,
          localizedFourierSchwartz, testToSchwartz_apply, cutoffToTestsCLM_apply]
  | succ n ih =>
    let i : Fin d := b (Fin.last n)
    let χ' : CompactTests d := TestFunction.lineDerivCLM ℂ (basisVector i) χ
    have h₁ := oscillatory_word_field_integrable χ' c hc n (Fin.init b) φ
    have h₂ := oscillatory_word_field_integrable χ c hc n (Fin.init b) (coordinateMultiply i φ)
    have heq : (fun ξ => φ ξ • OscillatoryWordField χ c b ξ) =
        (fun ξ => φ ξ • OscillatoryWordField χ' c (Fin.init b) ξ +
          c • (((coordinateMultiply i φ) ξ) • OscillatoryWordField χ c (Fin.init b) ξ)) := by
      funext ξ
      rw [oscillatory_word_field_succ, smul_add]
      congr 1
      have hval : (coordinateMultiply i φ) ξ = (ξ i : ℂ) * φ ξ :=
        SchwartzMap.smulLeftCLM_apply_apply (coordinate_growth (𝕜 := ℂ) i) φ ξ
      rw [hval]
      simp only [smul_smul]
      congr 1
      ring
    have h₂' : Integrable (fun ξ =>
        c • (((coordinateMultiply i φ) ξ) • OscillatoryWordField χ c (Fin.init b) ξ)) := by
      convert h₂.smul c using 1
    rw [heq, integral_add h₁ h₂', integral_smul]
    rw [ih χ' (Fin.init b) φ, ih χ (Fin.init b) (coordinateMultiply i φ)]
    ext x
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
      SchwartzMap.toBoundedContinuousFunction_apply, iteratedLineDerivOp_succ_right]
    rw [schwartz_lineDeriv_localizedFourier, iteratedLineDerivOp_add,
      iteratedLineDerivOp_smul]
    rfl



lemma distribution_pairing_integral_of_coordinate_jets {d : ℕ} (u : Distribution d)
    (K : TopologicalSpace.Compacts (Euclidean d))
    (F : Euclidean d → ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K)
    (w : Euclidean d → ℂ) (ψ : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K)
    (hF : ∀ s : Finset ℕ, Integrable (fun ξ => w ξ • coordinateJetMap K s (F ξ)))
    (hI : ∀ s : Finset ℕ, (∫ ξ, w ξ • coordinateJetMap K s (F ξ)) =
      coordinateJetMap K s ψ) :
    u (TestFunction.ofSupportedIn (Set.subset_univ _) ψ) =
      ∫ ξ, w ξ * u (TestFunction.ofSupportedIn (Set.subset_univ _) (F ξ)) := by
  obtain ⟨s, L, hL⟩ := compactJet_factorization u K
  let G : CoordinateJetSpace d s →L[ℂ] ℂ := L.comp (reconstructCompactJets s)
  have hG (φ : ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K) :
      G (coordinateJetMap K s φ) = u (TestFunction.ofSupportedIn (Set.subset_univ _) φ) := by
    change L (reconstructCompactJets s (coordinateJetMap K s φ)) = _
    rw [reconstruct_coordinateJetMap]
    exact (hL φ).symm
  rw [← hG ψ, ← hI s, ← G.integral_comp_comm (hF s)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [map_smul, smul_eq_mul, hG]


def cutoffSupported {d : ℕ} (χ : CompactTests d) (φ : Schwartz ℂ d) :
    ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ (oscillatoryCompact χ) :=
  ContDiffMapSupportedIn.of_support_subset (χ.contDiff.mul (φ.smooth ⊤))
    ((Function.support_mul_subset_left _ _).trans subset_closure)

lemma compact_fourier_pairing {d : ℕ} (u : Distribution d) (χ : CompactTests d)
    (φ : Schwartz ℂ d) :
    u (cutoffToTestsCLM χ (schwartzFourier φ)) =
      ∫ ξ, u (oscillatoryTest χ (-(2 * (Real.pi : ℂ) * Complex.I)) ξ) * φ ξ := by
  let K := oscillatoryCompact χ
  let c : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)
  let F := oscillatorySupported χ c
  let ψ := cutoffSupported χ (schwartzFourier φ)
  have hψ : TestFunction.ofSupportedIn (Set.subset_univ _) ψ =
      cutoffToTestsCLM χ (schwartzFourier φ) := by
    ext x
    exact (cutoffToTestsCLM_apply χ (schwartzFourier φ) x).symm
  have hword (s : Finset ℕ) (i : (↑(insert 0 s) : Set ℕ)) (b : Fin (i : ℕ) → Fin d) :
      Integrable (fun ξ => (φ ξ • coordinateJetMap K s (F ξ)) i b) := by
    change Integrable (fun ξ => φ ξ • OscillatoryWordField χ c b ξ)
    exact oscillatory_word_field_integrable χ c (by simp [c]) i b φ
  have hinner (s : Finset ℕ) (i : (↑(insert 0 s) : Set ℕ)) :
      Integrable (fun ξ => (φ ξ • coordinateJetMap K s (F ξ)) i) :=
    integrable_pi_iff.mpr (hword s i)
  have hF (s : Finset ℕ) : Integrable (fun ξ => φ ξ • coordinateJetMap K s (F ξ)) :=
    integrable_pi_iff.mpr (hinner s)
  have hI (s : Finset ℕ) : (∫ ξ, φ ξ • coordinateJetMap K s (F ξ)) = coordinateJetMap K s ψ := by
    funext i
    rw [eval_integral (hinner s)]
    funext b
    rw [eval_integral (hword s i)]
    simp only [Pi.smul_apply, coordinateJetMap_apply]
    rw [hψ]
    change (∫ ξ, φ ξ • OscillatoryWordField χ (-(2 * (Real.pi : ℂ) * Complex.I)) b ξ) =
      (iteratedLineDerivOp (fun j => basisVector (b j))
        (localizedFourierSchwartz χ φ)).toBoundedContinuousFunction
    exact oscillatory_word_field_integral χ i b φ
  have h := distribution_pairing_integral_of_coordinate_jets u K F φ ψ hF hI
  rw [hψ] at h
  change u (cutoffToTestsCLM χ (schwartzFourier φ)) =
    ∫ ξ, φ ξ * u (oscillatoryTest χ c ξ) at h
  simpa only [c, mul_comm] using h


lemma integrable_mul_compact_test {d : ℕ} {U : Set (Euclidean d)} (hU : IsOpen U)
    {g : Euclidean d → ℂ} (hg : ContinuousOn g U) (τ : CompactTests d)
    (hτ : tsupport τ ⊆ U) : Integrable (fun x => g x * τ x) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hg.mul τ.contDiff.continuous.continuousOn).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_right.trans hτ)
  · exact τ.hasCompactSupport.mul_left

/-- Homogeneity controls the exterior dyadic tail; the compact part has a smooth
Fourier kernel by finite-order factorization through actual coordinate jets. -/
theorem fourier_smooth_forward :
    Specs.ExpandedFA.PartIV.HomogeneousFourier.smoothAwayZeroForwardType := by
  intro d z v hv hs
  obtain ⟨k, hk, hkv⟩ := hs
  obtain ⟨g, hg, hgv⟩ := exists_smooth_fourier_exterior hv hk hkv
  let k₀ : Euclidean d → ℂ := fun ξ => restrictTempered v
    (oscillatoryTest (originCutoff d) (-(2 * (Real.pi : ℂ) * Complex.I)) ξ)
  have hk₀ : ContDiff ℝ ∞ k₀ :=
    compact_oscillatory_pairing_contDiff (restrictTempered v) (originCutoff d) _
  refine ⟨fun ξ => k₀ ξ + g ξ, hk₀.contDiffOn.add hg, fun τ hτ => ?_⟩
  have hc := compact_fourier_pairing (restrictTempered v) (originCutoff d) (testToSchwartz τ)
  change v (testToSchwartz (cutoffToTestsCLM (originCutoff d)
    (schwartzFourier (testToSchwartz τ)))) = ∫ ξ, k₀ ξ * τ ξ at hc
  have he := hgv τ hτ
  have hi₀ := integrable_mul_compact_test isOpen_compl_singleton hk₀.continuous.continuousOn τ hτ
  have hi := integrable_mul_compact_test isOpen_compl_singleton hg.continuousOn τ hτ
  change v (schwartzFourier (testToSchwartz τ)) = _
  simp_rw [add_mul]
  rw [integral_add hi₀ hi]
  rw [← hc, ← he]
  ring


theorem smooth_away_zero_iff :
    Specs.ExpandedFA.PartIV.HomogeneousFourier.smoothAwayZeroType :=
  smooth_away_zero_iff_of_forward fourier_smooth_forward

theorem homogeneous_fourier :
    Specs.ExpandedFA.PartIV.HomogeneousFourier.homogeneousFourierType :=
  homogeneous_fourier_of_extension_and_smoothness tempered_extension fourier_smooth_forward

end ExpandedFA.PartIV.HomogeneousFourier
