import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.MarkovKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Schauder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ContinuousKernel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Positive unital operators on C(K), with no assumed boundedness.

For existence, normalized positive functionals form a closed compact convex
subset of the product of the intervals [-norm f, norm f]. The transpose is
continuous in this product topology. Schauder gives a fixed functional and
the positive Riesz theorem gives its regular Borel probability measure.

For a strictly positive kernel, subtract its constant epsilon part. The
remaining nonnegative kernel has row mass 1-epsilon, which contracts real
oscillation even when epsilon=1. Invariant integrals and this estimate yield
uniform convergence and uniqueness. Complex positivity supplies a compatible
real restriction; the final theorem treats both components explicitly. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology CompactlySupported
universe u
namespace ExpandedFA.PartV.MarkovKernel
open Spec

section RealOrder
variable {K : Type u} [TopologicalSpace K]
  (P : C(K, ℝ) →ₗ[ℝ] C(K, ℝ)) (hP : RealMarkov P)

include hP

lemma map_const (a : ℝ) : P (ContinuousMap.const K a) = ContinuousMap.const K a := by
  have h : ContinuousMap.const K a = a • (1 : C(K, ℝ)) := by ext x; simp
  rw [h, map_smul, hP.2]

lemma map_mono {f g : C(K, ℝ)} (h : ∀ x, f x ≤ g x) : ∀ x, P f x ≤ P g x := by
  have hp := hP.1 (g - f) (fun x => sub_nonneg.mpr (h x))
  simpa only [map_sub, ContinuousMap.sub_apply, sub_nonneg] using hp

lemma map_bounds (f : C(K, ℝ)) (a b : ℝ) (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) :
    ∀ x, a ≤ P f x ∧ P f x ≤ b := by
  have h₁ := map_mono P hP (f := ContinuousMap.const K a) ha
  have h₂ := map_mono P hP (g := ContinuousMap.const K b) hb
  rw [map_const P hP] at h₁ h₂
  exact fun x => ⟨h₁ x, h₂ x⟩

variable [CompactSpace K]
lemma map_norm_le (f : C(K, ℝ)) : ‖P f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  have h := map_bounds P hP f (-‖f‖) ‖f‖
    (fun y => (abs_le.mp (f.norm_coe_le_norm y)).1)
    (fun y => (abs_le.mp (f.norm_coe_le_norm y)).2) x
  exact abs_le.mpr h

end RealOrder

section Means
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

/-- Positive normalized functionals, in the topology of pointwise convergence.
The bound is proved for evaluations and preserved by the transpose. -/
def means : Set (C(K, ℝ) → ℝ) := {L |
  (∀ f, |L f| ≤ ‖f‖) ∧
  (∀ f g, L (f + g) = L f + L g) ∧
  (∀ (a : ℝ) f, L (a • f) = a * L f) ∧
  L 1 = 1 ∧ (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ L f)}

lemma means_nonempty : (means (K := K)).Nonempty := by
  let x : K := Classical.arbitrary K
  exact ⟨fun f => f x, (fun f => f.norm_coe_le_norm x),
    (fun _ _ => rfl), (fun _ _ => rfl), rfl, (fun f hf => hf x)⟩

lemma means_closed : IsClosed (means (K := K)) := by
  unfold means
  simp only [ofPred_and, ofPred_forall]
  apply IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
  · exact isClosed_iInter fun f => isClosed_le ((continuous_apply f).abs) continuous_const
  · exact isClosed_iInter fun f => isClosed_iInter fun g =>
      isClosed_eq (continuous_apply (f + g)) ((continuous_apply f).add (continuous_apply g))
  · exact isClosed_iInter fun a => isClosed_iInter fun f =>
      isClosed_eq (continuous_apply (a • f)) (continuous_const.mul (continuous_apply f))
  · exact isClosed_eq (continuous_apply 1) continuous_const
  · exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_apply f)

lemma means_compact : IsCompact (means (K := K)) := by
  have hb : IsCompact {L : C(K, ℝ) → ℝ | ∀ f, L f ∈ Icc (-‖f‖) ‖f‖} :=
    isCompact_pi_infinite (fun f => isCompact_Icc)
  exact hb.of_isClosed_subset means_closed (fun L hL f => abs_le.mp (hL.1 f))

lemma means_convex : Convex ℝ (means (K := K)) := by
  intro L hL M hM a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    change |a * L f + b * M f| ≤ ‖f‖
    calc
      _ ≤ |a * L f| + |b * M f| := abs_add_le _ _
      _ = a * |L f| + b * |M f| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * ‖f‖ + b * ‖f‖ := add_le_add (mul_le_mul_of_nonneg_left (hL.1 f) ha)
        (mul_le_mul_of_nonneg_left (hM.1 f) hb)
      _ = ‖f‖ := by rw [← add_mul, hab, one_mul]
  · intro f g
    change a * L (f + g) + b * M (f + g) = _
    simp only [hL.2.1, hM.2.1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro c f
    change a * L (c • f) + b * M (c • f) = _
    simp only [hL.2.2.1, hM.2.2.1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change a * L 1 + b * M 1 = 1
    simpa [hL.2.2.2.1, hM.2.2.2.1] using hab
  · intro f hf
    exact add_nonneg (mul_nonneg ha (hL.2.2.2.2 f hf))
      (mul_nonneg hb (hM.2.2.2.2 f hf))

lemma exists_invariant_mean (P : C(K, ℝ) →ₗ[ℝ] C(K, ℝ)) (hP : RealMarkov P) :
    ∃ L ∈ means (K := K), ∀ f, L (P f) = L f := by
  let T : means (K := K) → means (K := K) := fun L =>
    ⟨fun f => L.val (P f),
      (fun f => (L.property.1 (P f)).trans (map_norm_le P hP f)),
      (fun f g => by dsimp only; rw [map_add, L.property.2.1]),
      (fun a f => by dsimp only; rw [map_smul, L.property.2.2.1]),
      (by dsimp only; rw [hP.2, L.property.2.2.2.1]),
      (fun f hf => L.property.2.2.2.2 (P f) (hP.1 f hf))⟩
  have hT : Continuous T := by
    apply Continuous.subtype_mk
    exact continuous_pi fun f => (continuous_apply (P f)).comp continuous_subtype_val
  have hLCS : ExpandedFA.P1.LCS ℝ (C(K, ℝ) → ℝ) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨L, hL⟩ := ExpandedFA.P1.Schauder.schauder_tychonoff ℝ (C(K, ℝ) → ℝ)
    hLCS means means_nonempty means_compact means_convex T hT
  exact ⟨L.val, L.property, fun f => congrFun (congrArg Subtype.val hL) f⟩

end Means

section RealExistence
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K]

lemma measure_of_mean (L : C(K, ℝ) → ℝ) (hL : L ∈ means (K := K)) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ f : C(K, ℝ), L f = ∫ x, f x ∂μ := by
  let I : C_c(K, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => L f.toContinuousMap
      map_add' := fun f g => hL.2.1 _ _
      map_smul' := fun a f => hL.2.2.1 _ _ }
  obtain ⟨μ, ⟨hμ, hrep⟩, _⟩ :=
    ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positive_radon_representation K I
      (fun f hf => hL.2.2.2.2 _ hf)
  have hr : μ.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ
  haveI : μ.Regular := hr
  haveI : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  have hall (f : C(K, ℝ)) : L f = ∫ x, f x ∂μ := by
    exact (hrep (CompactlySupportedContinuousMap.continuousMapEquiv f)).2
  have hm : μ.real univ = 1 := by
    simpa [hL.2.2.2.1] using (hall 1).symm
  have hp : IsProbabilityMeasure μ := isProbabilityMeasure_iff_real.mpr hm
  exact ⟨μ, hp, hr, hall⟩

end RealExistence

theorem real_invariant_probability : Spec.RealExistence.{u} := by
  intro K _ _ _ _ _ _ P hP
  obtain ⟨L, hL, hfix⟩ := exists_invariant_mean P hP
  obtain ⟨μ, hp, hr, hrep⟩ := measure_of_mean L hL
  exact ⟨μ, hp, hr, fun f => (hrep (P f)).symm.trans ((hfix f).trans (hrep f))⟩

section Oscillation
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

lemma oscillation_eq_sub (f : C(K, ℝ)) :
    oscillation f = sSup (range f) - sInf (range f) :=
  Real.diam_eq (isCompact_range f.continuous).isBounded

lemma value_bounds (f : C(K, ℝ)) (x : K) :
    sInf (range f) ≤ f x ∧ f x ≤ sSup (range f) :=
  ⟨csInf_le (isCompact_range f.continuous).bddBelow (mem_range_self x),
    le_csSup (isCompact_range f.continuous).bddAbove (mem_range_self x)⟩

lemma oscillation_nonneg (f : C(K, ℝ)) : 0 ≤ oscillation f := Metric.diam_nonneg

variable [MeasurableSpace K] [BorelSpace K]
lemma continuous_integrable (μ : Measure K) [IsFiniteMeasure μ] {𝕜 : Type*} [RCLike 𝕜]
    (f : C(K, 𝕜)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma deviation_le_oscillation (μ : Measure K) [IsProbabilityMeasure μ] (f : C(K, ℝ)) :
    ‖f - ContinuousMap.const K (∫ x, f x ∂μ)‖ ≤ oscillation f := by
  apply (ContinuousMap.norm_le _ (oscillation_nonneg f)).mpr
  intro x
  change ‖f x - ∫ y, f y ∂μ‖ ≤ oscillation f
  have heq : f x - ∫ y, f y ∂μ = ∫ y, f x - f y ∂μ := by
    rw [integral_sub (integrable_const _) (continuous_integrable μ f)]
    simp
  rw [heq]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun y => f x - f y) (C := oscillation f)
    (Eventually.of_forall fun y => Metric.dist_le_diam_of_mem
      (isCompact_range f.continuous).isBounded (mem_range_self x) (mem_range_self y))
  simpa using h

end Oscillation

section StrictKernel
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K]
  (P : C(K, ℝ) →ₗ[ℝ] C(K, ℝ)) (hP : RealMarkov P)
  (ν : Measure K) [IsProbabilityMeasure ν] (k : C(K × K, ℝ)) (ε : ℝ)
  (hε : 0 < ε) (hk : ∀ x y, ε ≤ k (x, y))
  (hkernel : ∀ f x, P f x = ∫ y, k (x, y) * f y ∂ν)
include hP hε hk hkernel

lemma kernel_row_integral (x : K) : ∫ y, k (x, y) ∂ν = 1 := by
  have h := hkernel 1 x
  rw [hP.2] at h
  simpa using h.symm

lemma minorization_le_one : ε ≤ 1 := by
  let x : K := Classical.arbitrary K
  have hi := ContinuousKernel.kernel_integrable_section ν k 1 x
  have h := integral_mono (integrable_const ε)
    (by simpa using hi) (fun y => hk x y)
  simpa [kernel_row_integral P hP ν k ε hε hk hkernel x] using h

/-- Subtracting the constant kernel leaves a nonnegative kernel whose row
mass is 1-epsilon. There is no division by 1-epsilon in this estimate. -/
lemma residual_bounds (f : C(K, ℝ)) (x : K) :
    (1 - ε) * sInf (range f) ≤ P f x - ε * ∫ y, f y ∂ν ∧
    P f x - ε * ∫ y, f y ∂ν ≤ (1 - ε) * sSup (range f) := by
  let r : C(K × K, ℝ) := k - ContinuousMap.const (K × K) ε
  have hi (g : C(K, ℝ)) : Integrable (fun y => (k (x, y) - ε) * g y) ν :=
    ContinuousKernel.kernel_integrable_section ν r g x
  have hir : Integrable (fun y => k (x, y) - ε) ν := by simpa using hi 1
  have hmass : ∫ y, k (x, y) - ε ∂ν = 1 - ε := by
    rw [integral_sub (by simpa using ContinuousKernel.kernel_integrable_section ν k 1 x)
      (integrable_const ε), kernel_row_integral P hP ν k ε hε hk hkernel]
    simp
  have heq : P f x - ε * ∫ y, f y ∂ν = ∫ y, (k (x, y) - ε) * f y ∂ν := by
    simp_rw [sub_mul]
    rw [integral_sub (ContinuousKernel.kernel_integrable_section ν k f x)
      ((continuous_integrable ν f).const_mul ε), integral_const_mul, hkernel]
  rw [heq]
  constructor
  · calc
      (1 - ε) * sInf (range f) = ∫ y, (k (x, y) - ε) * sInf (range f) ∂ν := by
        rw [integral_mul_const, hmass]
      _ ≤ _ := integral_mono (hir.mul_const _) (hi f) (fun y =>
        mul_le_mul_of_nonneg_left (value_bounds f y).1 (sub_nonneg.mpr (hk x y)))
  · calc
      _ ≤ ∫ y, (k (x, y) - ε) * sSup (range f) ∂ν :=
        integral_mono (hi f) (hir.mul_const _) (fun y =>
          mul_le_mul_of_nonneg_left (value_bounds f y).2 (sub_nonneg.mpr (hk x y)))
      _ = (1 - ε) * sSup (range f) := by rw [integral_mul_const, hmass]

lemma oscillation_contract (f : C(K, ℝ)) :
    oscillation (P f) ≤ (1 - ε) * oscillation f := by
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg (sub_nonneg.mpr (minorization_le_one P hP ν k ε hε hk hkernel))
      (oscillation_nonneg f))
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [Real.dist_eq, abs_le, oscillation_eq_sub]
  have hx := residual_bounds P hP ν k ε hε hk hkernel f x
  have hy := residual_bounds P hP ν k ε hε hk hkernel f y
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

lemma oscillation_iterate (f : C(K, ℝ)) (n : ℕ) :
    oscillation ((P : C(K, ℝ) → C(K, ℝ))^[n] f) ≤ (1 - ε)^n * oscillation f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    exact (oscillation_contract P hP ν k ε hε hk hkernel _).trans (by
      nlinarith [mul_le_mul_of_nonneg_left ih
        (sub_nonneg.mpr (minorization_le_one P hP ν k ε hε hk hkernel))])

end StrictKernel

section InvariantEstimates
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K]
  (P : C(K, ℝ) →ₗ[ℝ] C(K, ℝ))

lemma invariant_iterate_integral (μ : Measure K) (hμ : RealInvariant P μ)
    (f : C(K, ℝ)) (n : ℕ) :
    ∫ x, ((P : C(K, ℝ) → C(K, ℝ))^[n] f) x ∂μ = ∫ x, f x ∂μ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hμ.2.2, ih]

lemma iterate_error (μ : Measure K) (hμ : RealInvariant P μ)
    (ε : ℝ) (hosc : ∀ (f : C(K, ℝ)) (n : ℕ),
      oscillation ((P : C(K, ℝ) → C(K, ℝ))^[n] f) ≤ (1 - ε)^n * oscillation f)
    (f : C(K, ℝ)) (n : ℕ) :
    ‖(P : C(K, ℝ) → C(K, ℝ))^[n] f - ContinuousMap.const K (∫ x, f x ∂μ)‖ ≤
      (1 - ε)^n * oscillation f := by
  haveI := hμ.1
  have h := deviation_le_oscillation μ ((P : C(K, ℝ) → C(K, ℝ))^[n] f)
  rw [invariant_iterate_integral P μ hμ f n] at h
  exact h.trans (hosc f n)

/-- A supremum norm bound with a geometric factor gives uniform convergence. -/
lemma geometric_convergence {𝕜 : Type*} [RCLike 𝕜] (g : ℕ → C(K, 𝕜))
    (c : C(K, 𝕜)) (r C : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (h : ∀ n, ‖g n - c‖ ≤ r^n * C) : Tendsto g atTop (𝓝 c) := by
  have hz : Tendsto (fun n => g n - c) atTop (𝓝 0) :=
    squeeze_zero_norm h (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).mul_const C)
  have hh := hz.add_const c
  simpa using hh

lemma unique_invariant_of_oscillation (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hosc : ∀ (f : C(K, ℝ)) (n : ℕ),
      oscillation ((P : C(K, ℝ) → C(K, ℝ))^[n] f) ≤ (1 - ε)^n * oscillation f)
    (μ η : Measure K) (hμ : RealInvariant P μ) (hη : RealInvariant P η) : η = μ := by
  haveI := hμ.1
  haveI := hη.1
  haveI := hμ.2.1
  haveI := hη.2.1
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hlim (ρ : Measure K) (hρ : RealInvariant P ρ) :=
    geometric_convergence ((P : C(K, ℝ) → C(K, ℝ))^[·] f.toContinuousMap)
      (ContinuousMap.const K (∫ x, f x ∂ρ)) (1 - ε) (oscillation f.toContinuousMap)
      (sub_nonneg.mpr hε₁) (by linarith)
      (iterate_error P ρ hρ ε hosc f.toContinuousMap)
  have heq := tendsto_nhds_unique (hlim η hη) (hlim μ hμ)
  exact congrArg (fun g : C(K, ℝ) => g (Classical.arbitrary K)) heq

end InvariantEstimates

theorem real_strict_kernel : Spec.RealStrictKernel.{u} := by
  intro K _ _ _ _ _ _ P hP ν _ k ε hε hk hkernel
  obtain ⟨μ, hμ⟩ := real_invariant_probability K P hP
  have hε₁ := minorization_le_one P hP ν k ε hε hk hkernel
  have hosc := oscillation_iterate P hP ν k ε hε hk hkernel
  have herr := iterate_error P μ hμ ε hosc
  refine ⟨μ, hμ, ?_, hε₁, hosc, herr, ?_, ?_⟩
  · exact fun η hη => unique_invariant_of_oscillation P ε hε hε₁ hosc μ η hμ hη
  · intro f
    exact geometric_convergence _ _ (1 - ε) (oscillation f)
      (sub_nonneg.mpr hε₁) (by linarith) (herr f)
  · intro heq f
    have h := herr f 1
    simp only [heq, sub_self, zero_pow (by decide : 1 ≠ 0), zero_mul,
      Function.iterate_one] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

section ComplexComponents
variable {K : Type u} [TopologicalSpace K]

/-- Pointwise real inclusion and components, with the original topology. -/
def complexLift (f : C(K, ℝ)) : C(K, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
def realPart (f : C(K, ℂ)) : C(K, ℝ) :=
  ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
def imagPart (f : C(K, ℂ)) : C(K, ℝ) :=
  ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩

@[simp] lemma complexLift_apply (f : C(K, ℝ)) (x : K) : complexLift f x = (f x : ℂ) := rfl
@[simp] lemma realPart_apply (f : C(K, ℂ)) (x : K) : realPart f x = (f x).re := rfl
@[simp] lemma imagPart_apply (f : C(K, ℂ)) (x : K) : imagPart f x = (f x).im := rfl
@[simp] lemma complexLift_add (f g : C(K, ℝ)) : complexLift (f + g) = complexLift f + complexLift g := by
  ext x <;> simp
@[simp] lemma complexLift_smul (a : ℝ) (f : C(K, ℝ)) :
    complexLift (a • f) = (a : ℂ) • complexLift f := by ext x <;> simp
@[simp] lemma complexLift_one : complexLift (1 : C(K, ℝ)) = 1 := by ext x <;> simp

lemma component_decomposition (f : C(K, ℂ)) :
    f = complexLift (realPart f) + Complex.I • complexLift (imagPart f) := by
  ext x
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- Restriction to the real part is initially just a real-linear map. Its
compatibility with P follows below from positivity, rather than an assumption. -/
def realRestriction (P : C(K, ℂ) →ₗ[ℂ] C(K, ℂ)) : C(K, ℝ) →ₗ[ℝ] C(K, ℝ) where
  toFun f := realPart (P (complexLift f))
  map_add' f g := by ext x; simp [map_add]
  map_smul' a f := by ext x; simp [map_smul, Complex.mul_re]

variable (P : C(K, ℂ) →ₗ[ℂ] C(K, ℂ)) (hP : ComplexMarkov P)
include hP

lemma complex_map_const (a : ℂ) : P (ContinuousMap.const K a) = ContinuousMap.const K a := by
  have h : ContinuousMap.const K a = a • (1 : C(K, ℂ)) := by ext x; simp
  rw [h, map_smul, hP.2]

lemma realRestriction_markov : RealMarkov (realRestriction P) := by
  constructor
  · intro f hf x
    exact (hP.1 (complexLift f) (fun y => by simpa using hf y) x).2
  · ext x
    simp [realRestriction, hP.2]

variable [CompactSpace K]
lemma map_real_im_zero (f : C(K, ℝ)) (x : K) : (P (complexLift f) x).im = 0 := by
  let c : C(K, ℂ) := ContinuousMap.const K (‖f‖ : ℂ)
  have hc : P c = c := complex_map_const P hP _
  have hpos : ∀ y, ((complexLift f + c) y).im = 0 ∧ 0 ≤ ((complexLift f + c) y).re := by
    intro y
    have h := (abs_le.mp (f.norm_coe_le_norm y)).1
    dsimp [c]
    simp only [ContinuousMap.add_apply, complexLift_apply, ContinuousMap.const_apply,
      Complex.add_im, Complex.ofReal_im, add_zero, Complex.add_re, Complex.ofReal_re]
    exact ⟨trivial, by linarith⟩
  have h := (hP.1 (complexLift f + c) hpos x).1
  rw [map_add, hc] at h
  simpa [c] using h

lemma lift_realRestriction (f : C(K, ℝ)) :
    complexLift (realRestriction P f) = P (complexLift f) := by
  ext x
  apply Complex.ext
  · rfl
  · simpa using (map_real_im_zero P hP f x).symm

lemma map_component_decomposition (f : C(K, ℂ)) :
    P f = complexLift (realRestriction P (realPart f)) +
      Complex.I • complexLift (realRestriction P (imagPart f)) := by
  rw [lift_realRestriction P hP, lift_realRestriction P hP, ← map_smul, ← map_add,
    ← component_decomposition]

lemma map_realPart (f : C(K, ℂ)) : realPart (P f) = realRestriction P (realPart f) := by
  rw [map_component_decomposition P hP]
  ext x
  simp [Complex.mul_re]

lemma map_imagPart (f : C(K, ℂ)) : imagPart (P f) = realRestriction P (imagPart f) := by
  rw [map_component_decomposition P hP]
  ext x
  simp [Complex.mul_im]

lemma iterate_realPart (f : C(K, ℂ)) (n : ℕ) :
    realPart ((P : C(K, ℂ) → C(K, ℂ))^[n] f) =
      (realRestriction P : C(K, ℝ) → C(K, ℝ))^[n] (realPart f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', map_realPart P hP, ih,
      Function.iterate_succ_apply']

lemma iterate_imagPart (f : C(K, ℂ)) (n : ℕ) :
    imagPart ((P : C(K, ℂ) → C(K, ℂ))^[n] f) =
      (realRestriction P : C(K, ℝ) → C(K, ℝ))^[n] (imagPart f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', map_imagPart P hP, ih,
      Function.iterate_succ_apply']

variable [T2Space K] [Nonempty K] [MeasurableSpace K] [BorelSpace K]

lemma invariant_real_to_complex (μ : Measure K) (hμ : RealInvariant (realRestriction P) μ) :
    ComplexInvariant P μ := by
  haveI := hμ.1
  refine ⟨hμ.1, hμ.2.1, ?_⟩
  intro f
  apply Complex.ext
  · have h := hμ.2.2 (realPart f)
    rw [← map_realPart P hP] at h
    change (∫ x, RCLike.re (P f x) ∂μ) = ∫ x, RCLike.re (f x) ∂μ at h
    rw [integral_re (continuous_integrable μ (P f)), integral_re (continuous_integrable μ f)] at h
    exact h
  · have h := hμ.2.2 (imagPart f)
    rw [← map_imagPart P hP] at h
    change (∫ x, RCLike.im (P f x) ∂μ) = ∫ x, RCLike.im (f x) ∂μ at h
    rw [integral_im (continuous_integrable μ (P f)), integral_im (continuous_integrable μ f)] at h
    exact h

lemma invariant_complex_to_real (μ : Measure K) (hμ : ComplexInvariant P μ) :
    RealInvariant (realRestriction P) μ := by
  haveI := hμ.1
  refine ⟨hμ.1, hμ.2.1, ?_⟩
  intro f
  have h := congrArg Complex.re (hμ.2.2 (complexLift f))
  rw [← lift_realRestriction P hP f] at h
  simpa only [complexLift_apply, integral_complex_ofReal, Complex.ofReal_re] using h

end ComplexComponents

theorem complex_invariant_probability : Spec.ComplexExistence.{u} := by
  intro K _ _ _ _ _ _ P hP
  obtain ⟨μ, hμ⟩ := real_invariant_probability K (realRestriction P) (realRestriction_markov P hP)
  exact ⟨μ, invariant_real_to_complex P hP μ hμ⟩

section ComplexKernel
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K]

lemma norm_le_components (f : C(K, ℂ)) : ‖f‖ ≤ ‖realPart f‖ + ‖imagPart f‖ := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  exact (Complex.norm_le_abs_re_add_abs_im (f x)).trans
    (add_le_add ((realPart f).norm_coe_le_norm x) ((imagPart f).norm_coe_le_norm x))

lemma realPart_sub_integral_const (μ : Measure K) [IsFiniteMeasure μ]
    (g f : C(K, ℂ)) :
    realPart (g - ContinuousMap.const K (∫ x, f x ∂μ)) =
      realPart g - ContinuousMap.const K (∫ x, realPart f x ∂μ) := by
  have h := integral_re (continuous_integrable μ f)
  change (∫ y, (f y).re ∂μ) = (∫ y, f y ∂μ).re at h
  ext x
  change (g x).re - (∫ y, f y ∂μ).re = (g x).re - ∫ y, (f y).re ∂μ
  rw [← h]

lemma imagPart_sub_integral_const (μ : Measure K) [IsFiniteMeasure μ]
    (g f : C(K, ℂ)) :
    imagPart (g - ContinuousMap.const K (∫ x, f x ∂μ)) =
      imagPart g - ContinuousMap.const K (∫ x, imagPart f x ∂μ) := by
  have h := integral_im (continuous_integrable μ f)
  change (∫ y, (f y).im ∂μ) = (∫ y, f y ∂μ).im at h
  ext x
  change (g x).im - (∫ y, f y ∂μ).im = (g x).im - ∫ y, (f y).im ∂μ
  rw [← h]

lemma realRestriction_kernel_formula (P : C(K, ℂ) →ₗ[ℂ] C(K, ℂ))
    (ν : Measure K) [IsProbabilityMeasure ν] (k : C(K × K, ℝ))
    (hkernel : ∀ f x, P f x = ∫ y, (k (x, y) : ℂ) * f y ∂ν)
    (f : C(K, ℝ)) (x : K) :
    realRestriction P f x = ∫ y, k (x, y) * f y ∂ν := by
  change (P (complexLift f) x).re = _
  rw [hkernel]
  have hi := ContinuousKernel.kernel_integrable_section ν (complexLift k) (complexLift f) x
  have h := integral_re hi
  change (∫ y, ((k (x, y) : ℂ) * (f y : ℂ)).re ∂ν) =
    (∫ y, (k (x, y) : ℂ) * (f y : ℂ) ∂ν).re at h
  simpa only [complexLift_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using h.symm

lemma complex_iterate_error (P : C(K, ℂ) →ₗ[ℂ] C(K, ℂ)) (hP : ComplexMarkov P)
    (μ : Measure K) [IsProbabilityMeasure μ] (ε : ℝ)
    (herr : ∀ (f : C(K, ℝ)) (n : ℕ),
      ‖(realRestriction P : C(K, ℝ) → C(K, ℝ))^[n] f -
        ContinuousMap.const K (∫ x, f x ∂μ)‖ ≤ (1 - ε)^n * oscillation f)
    (f : C(K, ℂ)) (n : ℕ) :
    ‖(P : C(K, ℂ) → C(K, ℂ))^[n] f - ContinuousMap.const K (∫ x, f x ∂μ)‖ ≤
      (1 - ε)^n * (oscillation (realPart f) + oscillation (imagPart f)) := by
  calc
    _ ≤ ‖realPart ((P : C(K, ℂ) → C(K, ℂ))^[n] f -
          ContinuousMap.const K (∫ x, f x ∂μ))‖ +
        ‖imagPart ((P : C(K, ℂ) → C(K, ℂ))^[n] f -
          ContinuousMap.const K (∫ x, f x ∂μ))‖ := norm_le_components _
    _ = ‖(realRestriction P : C(K, ℝ) → C(K, ℝ))^[n] (realPart f) -
          ContinuousMap.const K (∫ x, realPart f x ∂μ)‖ +
        ‖(realRestriction P : C(K, ℝ) → C(K, ℝ))^[n] (imagPart f) -
          ContinuousMap.const K (∫ x, imagPart f x ∂μ)‖ := by
      rw [realPart_sub_integral_const, imagPart_sub_integral_const,
        iterate_realPart P hP, iterate_imagPart P hP]
    _ ≤ (1 - ε)^n * oscillation (realPart f) +
        (1 - ε)^n * oscillation (imagPart f) := add_le_add (herr _ n) (herr _ n)
    _ = _ := by ring

end ComplexKernel

theorem complex_strict_kernel : Spec.ComplexStrictKernel.{u} := by
  intro K _ _ _ _ _ _ P hP ν _ k ε hε hk hkernel
  obtain ⟨μ, hμ, huniq, hε₁, hosc, herr, _, _⟩ :=
    real_strict_kernel K (realRestriction P) (realRestriction_markov P hP) ν k ε hε hk
      (realRestriction_kernel_formula P ν k hkernel)
  haveI := hμ.1
  have herror := complex_iterate_error P hP μ ε herr
  refine ⟨μ, invariant_real_to_complex P hP μ hμ, ?_, hε₁, ?_, herror, ?_, ?_⟩
  · exact fun η hη => huniq η (invariant_complex_to_real P hP η hη)
  · intro f n
    change oscillation (realPart ((P : C(K, ℂ) → C(K, ℂ))^[n] f)) ≤ _ ∧
      oscillation (imagPart ((P : C(K, ℂ) → C(K, ℂ))^[n] f)) ≤ _
    rw [iterate_realPart P hP, iterate_imagPart P hP]
    exact ⟨hosc _ n, hosc _ n⟩
  · intro f
    exact geometric_convergence _ _ (1 - ε)
      (oscillation (realPart f) + oscillation (imagPart f))
      (sub_nonneg.mpr hε₁) (by linarith) (herror f)
  · intro heq f
    have h := herror f 1
    simp only [heq, sub_self, zero_pow (by decide : 1 ≠ 0), zero_mul,
      Function.iterate_one] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

end ExpandedFA.PartV.MarkovKernel
