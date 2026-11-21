import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinExtreme
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinEven
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace ExpandedFA.PartIV.KreinExtreme
open KreinSolutions.Specs

lemma continuous_C (μ : ℝ) : Continuous (CValue μ) := by
  unfold CValue
  split_ifs <;> fun_prop

theorem spectral_injectivity : Spec.SpectralInjectivity := by
  intro μ ξ h
  have hd := congrArg (fun f : ℝ → ℝ => deriv (deriv f) 0) h
  have hv (r : ℝ) : deriv (deriv (CValue r)) 0 = r := by
    simpa only [(KreinSolutions.initialData r).1, mul_one] using
      (KreinSolutions.secondDerivatives r 0).1.deriv
  simpa only [hv] using hd

lemma kernel_combination (p q : ℝ → ℝ) (a b s t : ℝ) :
    KernelPlusValue (a • p + b • q) s t =
      a * KernelPlusValue p s t + b * KernelPlusValue q s t := by
  simp only [KernelPlusValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma positive_combination {p q : ℝ → ℝ}
    (hp : PositiveDefiniteValue (KernelPlusValue p))
    (hq : PositiveDefiniteValue (KernelPlusValue q))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    PositiveDefiniteValue (KernelPlusValue (a • p + b • q)) := by
  constructor
  · intro s t
    rw [kernel_combination, kernel_combination, hp.1 s t, hq.1 s t]
  · intro n x c
    have he : (∑ i, ∑ j, c i * c j * KernelPlusValue (a • p + b • q) (x i) (x j)) =
        a * (∑ i, ∑ j, c i * c j * KernelPlusValue p (x i) (x j)) +
        b * (∑ i, ∑ j, c i * c j * KernelPlusValue q (x i) (x j)) := by
      simp only [kernel_combination, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact add_nonneg (mul_nonneg ha (hp.2 n x c)) (mul_nonneg hb (hq.2 n x c))

theorem normalized_convex : Spec.NormalizedConvex := by
  intro p hp q hq a b ha hb hab
  have hpc := hp.1
  have hqc := hq.1
  have hpe := hp.2.1
  have hqe := hq.2.1
  refine ⟨(hpc.const_smul a).add (hqc.const_smul b), ?_, ?_, ?_⟩
  · intro s
    simp only [Pi.add_apply, Pi.smul_apply, hpe s, hqe s]
  · apply KreinEven.test_positive_of_kernel ((hpc.const_smul a).add (hqc.const_smul b))
      (fun s => by simp only [Pi.add_apply, Pi.smul_apply, hpe s, hqe s])
    exact positive_combination (KreinEven.kernel_positive_of_test hpc hpe hp.2.2.1)
      (KreinEven.kernel_positive_of_test hqc hqe hq.2.2.1) ha hb
  · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp.2.2.2, hq.2.2.2,
      mul_one] using hab

/-- The two-point quadratic form at s and zero, with arbitrary second coefficient. -/
lemma normalized_quadratic {p : ℝ → ℝ} (hp : p ∈ Spec.normalized) (s c : ℝ) :
    0 ≤ KernelPlusValue p s s - 2 * c * p s + c ^ 2 := by
  have h := (KreinEven.kernel_positive_of_test hp.1 hp.2.1 hp.2.2.1).2
    2 ![s, 0] ![1, -c]
  have h0s : KernelPlusValue p 0 s = p s := by
    simp [KernelPlusValue, hp.2.1 s]
  have hs0 : KernelPlusValue p s 0 = p s := by simp [KernelPlusValue]
  have h00 : KernelPlusValue p 0 0 = 1 := by simp [KernelPlusValue, hp.2.2.2]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    hs0, h0s, h00] at h
  nlinarith [h]

lemma C_normalized (μ : ℝ) : CValue μ ∈ Spec.normalized := by
  have hc := continuous_C μ
  have he := (KreinSolutions.parity μ).1
  refine ⟨hc, he, KreinEven.test_positive_of_kernel hc he ?_,
    (KreinSolutions.initialData μ).1⟩
  constructor
  · intro s t
    simp only [KernelPlusValue, KreinSolutions.additionSum μ]
    ring
  · intro n x a
    have heq : (∑ i, ∑ j, a i * a j * KernelPlusValue (CValue μ) (x i) (x j)) =
        (∑ i, a i * CValue μ (x i)) ^ 2 := by
      simp only [KernelPlusValue, KreinSolutions.additionSum μ, pow_two,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    exact sq_nonneg _

theorem scalar_extremality : Spec.ScalarExtremality := by
  intro μ
  refine ⟨C_normalized μ, ?_⟩
  intro p hp q hq hseg
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  funext s
  let c := CValue μ s
  have hsum : a * p s + b * q s = c := congrFun he s
  have hdiag : a * KernelPlusValue p s s + b * KernelPlusValue q s s = c ^ 2 := by
    rw [← kernel_combination, he, KernelPlusValue, KreinSolutions.additionSum]
    dsimp [c]
    ring
  have hP := normalized_quadratic hp s c
  have hQ := normalized_quadratic hq s c
  have hz : a * (KernelPlusValue p s s - 2 * c * p s + c ^ 2) +
      b * (KernelPlusValue q s s - 2 * c * q s + c ^ 2) = 0 := by
    calc
      _ = (a * KernelPlusValue p s s + b * KernelPlusValue q s s) -
          2 * c * (a * p s + b * q s) + (a + b) * c ^ 2 := by ring
      _ = 0 := by rw [hdiag, hsum, hab]; ring
  have hzP : KernelPlusValue p s s - 2 * c * p s + c ^ 2 = 0 := by
    nlinarith [mul_nonneg hb.le hQ]
  have hmin := normalized_quadratic hp s (p s)
  nlinarith [sq_nonneg (p s - c)]

/-- Finite measures integrating every scalar solution automatically have all
positive-half-line cosh moments, including after restriction or normalization. -/
lemma represents_integral {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hi : ∀ s : ℝ, Integrable (fun ξ => CValue ξ s) ν) :
    KreinEven.Spec.Represents (fun s => ∫ ξ, CValue ξ s ∂ν) ν := by
  refine ⟨inferInstance, ?_, fun s => ⟨hi s, rfl⟩,
    fun R _ => KreinEven.positive_moment_of_integrable (hi R)⟩
  simp [CValue]

/-- Compact domination gives continuity even for an unbounded represented function. -/
lemma represented_continuous {p : ℝ → ℝ} {ν : Measure ℝ}
    (h : KreinEven.Spec.Represents p ν) : Continuous p := by
  have heq : p = fun s => ∫ ξ, CValue ξ s ∂ν := funext fun s => (h.2.2.1 s).2
  rw [heq]
  apply continuous_iff_continuousAt.mpr
  intro s₀
  obtain ⟨g, hg, hbound⟩ := KreinEven.compact_domination p ν h (|s₀| + 1)
    (by positivity)
  apply continuousAt_of_dominated
    (Eventually.of_forall fun s => (h.2.2.1 s).1.aestronglyMeasurable) ?_ hg
    (Eventually.of_forall fun ξ => (continuous_C ξ).continuousAt)
  filter_upwards [(continuous_abs.tendsto s₀).eventually
    (gt_mem_nhds (lt_add_one |s₀|))] with s hs
  exact Eventually.of_forall fun ξ => by
    simpa only [Real.norm_eq_abs] using hbound ξ s hs.le

/-- A nonzero restriction, renormalized to mass one, stays in the original class. -/
lemma average_normalized {p : ℝ → ℝ} {ν : Measure ℝ}
    (h : KreinEven.Spec.Represents p ν) {A : Set ℝ} (hA : ν A ≠ 0) :
    (fun s => ⨍ ξ in A, CValue ξ s ∂ν) ∈ Spec.normalized := by
  let : IsFiniteMeasure ν := h.1
  let : NeZero (ν.restrict A) := ⟨fun hz => hA (Measure.restrict_eq_zero.mp hz)⟩
  let ρ : Measure ℝ := ((ν.restrict A) univ)⁻¹ • ν.restrict A
  have hi (s : ℝ) : Integrable (fun ξ => CValue ξ s) ρ :=
    (h.2.2.1 s).1.integrableOn.to_average
  have hr := represents_integral hi
  have hc : Continuous (fun s => ⨍ ξ in A, CValue ξ s ∂ν) := represented_continuous hr
  have he : Function.Even (fun s => ⨍ ξ in A, CValue ξ s ∂ν) := by
    intro s
    exact congrArg (average (ν.restrict A))
      (funext fun ξ => (KreinSolutions.parity ξ).1 s)
  refine ⟨hc, he, KreinEven.test_positive_of_kernel hc he
    (KreinEven.representation_positive_kernel hr), ?_⟩
  simp only [show (fun ξ : ℝ => CValue ξ 0) = fun _ => 1 from
    funext fun ξ => (KreinSolutions.initialData ξ).1]
  exact setAverage_const hA (measure_ne_top ν A) 1

/-- Extremality forces every scalar spectral coordinate to be almost surely constant.
This holds for any representing probability; its uniqueness is never asserted. -/
lemma extreme_ae_coordinate {p : ℝ → ℝ}
    (hp : p ∈ Spec.normalized.extremePoints ℝ) {ν : Measure ℝ}
    (h : KreinEven.Spec.Represents p ν) (s : ℝ) :
    ∀ᵐ ξ ∂ν, CValue ξ s = p s := by
  let : IsFiniteMeasure ν := h.1
  let : IsProbabilityMeasure ν := isProbabilityMeasure_iff_real.mpr
    (h.2.1.trans hp.1.2.2.2)
  have hi := (h.2.2.1 s).1
  rcases ae_eq_const_or_exists_average_ne_compl hi with he | ⟨A, hA, h₀, h₁, hne⟩
  · filter_upwards [he] with ξ hξ
    exact hξ.trans (by simpa only [Function.const_apply, average_eq_integral] using (h.2.2.1 s).2.symm)
  · let q : ℝ → ℝ := fun t => ⨍ ξ in A, CValue ξ t ∂ν
    let r : ℝ → ℝ := fun t => ⨍ ξ in Aᶜ, CValue ξ t ∂ν
    have hq : q ∈ Spec.normalized := average_normalized h h₀
    have hr : r ∈ Spec.normalized := average_normalized h h₁
    have hseg : p ∈ openSegment ℝ q r := by
      refine ⟨ν.real A, ν.real Aᶜ, ENNReal.toReal_pos h₀ (measure_ne_top _ _),
        ENNReal.toReal_pos h₁ (measure_ne_top _ _), probReal_add_probReal_compl hA, ?_⟩
      funext t
      change ν.real A • (⨍ ξ in A, CValue ξ t ∂ν) +
        ν.real Aᶜ • (⨍ ξ in Aᶜ, CValue ξ t ∂ν) = p t
      rw [measure_smul_setAverage _ (measure_ne_top _ _),
        measure_smul_setAverage _ (measure_ne_top _ _),
        integral_add_compl hA (h.2.2.1 t).1]
      exact (h.2.2.1 t).2.symm
    obtain ⟨heq, her⟩ := (mem_extremePoints.mp hp).2 q hq r hr hseg
    exact False.elim (hne ((congrFun heq s).trans (congrFun her s).symm))

theorem exhaustion : Spec.Exhaustion := by
  intro p hp
  obtain ⟨ν, hν⟩ := (KreinEven.representation p hp.1.1 hp.1.2.1).mp hp.1.2.2.1
  let : IsFiniteMeasure ν := hν.1
  let : IsProbabilityMeasure ν := isProbabilityMeasure_iff_real.mpr
    (hν.2.1.trans hp.1.2.2.2)
  have hseq : ∀ᵐ ξ ∂ν, ∀ n : ℕ,
      CValue ξ (TopologicalSpace.denseSeq ℝ n) = p (TopologicalSpace.denseSeq ℝ n) :=
    ae_all_iff.mpr fun n => extreme_ae_coordinate hp hν _
  obtain ⟨ξ, hξ⟩ := hseq.exists
  refine ⟨ξ, ?_⟩
  exact ((TopologicalSpace.denseRange_denseSeq ℝ).equalizer (continuous_C ξ) hp.1.1
    (funext hξ)).symm

theorem classification : Spec.Classification := by
  intro p
  constructor
  · intro hp
    obtain ⟨μ, rfl⟩ := exhaustion p hp
    by_cases hn : μ < 0
    · left
      exact ⟨Real.sqrt (-μ), Real.sqrt_nonneg _, by funext s; simp [CValue, hn]⟩
    · by_cases hz : μ = 0
      · left
        exact ⟨0, le_rfl, by funext s; simp [CValue, hz]⟩
      · right
        exact ⟨Real.sqrt μ, Real.sqrt_pos.mpr (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)),
          by funext s; simp [CValue, hn, hz]⟩
  · rintro (⟨a, _, rfl⟩ | ⟨b, _, rfl⟩)
    · convert scalar_extremality (-(a ^ 2)) using 1
      exact (funext fun s => KreinEven.C_neg_square a s).symm
    · convert scalar_extremality (b ^ 2) using 1
      exact (funext fun s => KreinEven.C_square b s).symm

end ExpandedFA.PartIV.KreinExtreme
