import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.DunfordPettisL1
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.DunfordPettisContinuousFunctions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.WeakLinfinityFiniteL1
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.WeakL1UniformIntegrability
import Mathlib.MeasureTheory.Function.Egorov

noncomputable section
namespace ExpandedFA.Compactness.DunfordPettisL1
open MeasureTheory Filter Set
open scoped ENNReal Topology
open FunctionSpaces FunctionSpaces.WeakL1UniformIntegrabilitySpec
universe u w

/-- Uniform absolute continuity and finite-measure tail control turn bounded
almost-everywhere null multipliers into null diagonal integrals. Egorov is
applied only on a finite-measure set, so the ambient measure can be infinite. -/
theorem diagonal_integral_tendsto_zero {α : Type u} {𝕜 : Type}
    [MeasurableSpace α] [RCLike 𝕜] (μ : Measure α)
    (f : ℕ → Lp 𝕜 1 μ) (g : ℕ → Lp 𝕜 ∞ μ)
    (hc : Controls μ (fun n => (f n : α → 𝕜)))
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 0))
    (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hg : ∀ n, ∀ᵐ x ∂μ, ‖g n x‖ ≤ C)
    (hf : ∀ n, (∫ x, ‖f n x‖ ∂μ) ≤ M) :
    Tendsto (fun n => ∫ x, f n x * g n x ∂μ) atTop (𝓝 0) := by
  have hfi (n : ℕ) : Integrable (f n : α → 𝕜) μ :=
    memLp_one_iff_integrable.mp (Lp.memLp (f n))
  have hp (n : ℕ) : Integrable (fun x => f n x * g n x) μ :=
    (lp_pairing_integral μ 1 ∞ (g n) (f n)).1
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let a := ε / (3 * (C + 1))
  let b := ε / (3 * (M + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨A, hA, hμA, htail⟩ := hc.2 a ha
  obtain ⟨δ, hδ, hsmall⟩ := hc.1 a ha
  obtain ⟨B, hBA, hB, hμB, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto
    (fun n => Lp.stronglyMeasurable (g n)) stronglyMeasurable_const hA hμA.ne
    (hpoint.mono fun _ hx _ => hx)
    (ENNReal.ofReal_pos.mpr (half_pos hδ))
  have hμB' : μ B < ENNReal.ofReal δ :=
    hμB.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hunif b hb)
  refine ⟨N, fun n hn => ?_⟩
  let F : α → ℝ := fun x => ‖f n x‖
  have hi : Integrable F μ := (hfi n).norm
  have hiA : Integrable (Aᶜ.indicator F) μ := hi.indicator hA.compl
  have hiB : Integrable (B.indicator F) μ := hi.indicator hB
  have hmajor : ∀ᵐ x ∂μ, ‖f n x * g n x‖ ≤
      C * (Aᶜ.indicator F x + B.indicator F x) + b * F x := by
    filter_upwards [hg n] with x hx
    rw [norm_mul]
    have hFx : 0 ≤ F x := norm_nonneg _
    by_cases hxA : x ∈ A
    · by_cases hxB : x ∈ B
      · rw [indicator_of_notMem (show x ∉ Aᶜ from not_not.mpr hxA),
          indicator_of_mem hxB, zero_add]
        exact (mul_le_mul_of_nonneg_left hx hFx).trans (by dsimp [F]; nlinarith)
      · have hgood := (hN n hn x ⟨hxA, hxB⟩).le
        simp only [dist_zero_left] at hgood
        rw [indicator_of_notMem (show x ∉ Aᶜ from not_not.mpr hxA),
          indicator_of_notMem hxB, add_zero, mul_zero, zero_add]
        exact (mul_le_mul_of_nonneg_left hgood hFx).trans_eq (mul_comm _ _)
    · have hxB : x ∉ B := fun h => hxA (hBA h)
      rw [indicator_of_mem (show x ∈ Aᶜ from hxA), indicator_of_notMem hxB, add_zero]
      exact (mul_le_mul_of_nonneg_left hx hFx).trans (by dsimp [F]; nlinarith)
  have hint : (∫ x, ‖f n x * g n x‖ ∂μ) ≤
      C * ((∫ x in Aᶜ, F x ∂μ) + ∫ x in B, F x ∂μ) + b * ∫ x, F x ∂μ := by
    calc
      _ ≤ ∫ x, C * (Aᶜ.indicator F x + B.indicator F x) + b * F x ∂μ :=
        integral_mono_ae (hp n).norm (((hiA.add hiB).const_mul C).add (hi.const_mul b)) hmajor
      _ = (∫ x, C * (Aᶜ.indicator F x + B.indicator F x) ∂μ) +
          ∫ x, b * F x ∂μ := integral_add ((hiA.add hiB).const_mul C) (hi.const_mul b)
      _ = _ := by
        rw [integral_const_mul, integral_const_mul]
        congr 1
        congr 1
        exact (integral_add hiA hiB).trans (by
          rw [integral_indicator hA.compl, integral_indicator hB])
  have hCa : C * a < ε / 3 := by
    have he : (C + 1) * a = ε / 3 := by dsimp [a]; field_simp
    nlinarith
  have hMb : b * M < ε / 3 := by
    have he : b * (M + 1) = ε / 3 := by dsimp [b]; field_simp
    nlinarith
  rw [dist_zero_right]
  apply (norm_integral_le_integral_norm _).trans hint |>.trans_lt
  have ht := htail n
  have hs := hsmall B hB hμB' n
  have hm := hf n
  dsimp only [F] at *
  have hle := add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add ht.le hs.le) hC)
    (mul_le_mul_of_nonneg_left hm hb.le)
  nlinarith


/-- On a sigma-finite measure the bilinear integral map is an actual
linear isometric equivalence with the full dual. Its inverse transports
weak nullity of functionals to weak nullity in L∞. -/
def densityEquiv {α : Type u} {𝕜 : Type} [MeasurableSpace α] [RCLike 𝕜]
    (μ : Measure α) [SigmaFinite μ] :
    Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] (Lp 𝕜 1 μ →L[𝕜] 𝕜) :=
  { LinearEquiv.ofBijective (lpIntegralPairing μ 1 ∞).toLinearMap
      (lp_pairing_sigmaFinite_isometric_bijective μ 1 ∞ (by simp)).2 with
    norm_map' := fun g => lp_pairing_exact_norm μ 1 ∞ (by simp)
      (Or.inl inferInstance) g }

/-- The diagonal weak-null test on sigma-finite spaces. Both controls from
the gliding-hump theorem are used, including the finite-measure tail. -/
theorem sigmaFinite_weakNull_testing {α : Type u} {𝕜 : Type}
    [MeasurableSpace α] [RCLike 𝕜] (μ : Measure α) [SigmaFinite μ] :
    DunfordPettisCriterion.WeakNullTestingProperty 𝕜 (Lp 𝕜 1 μ) := by
  intro f L hf hL
  let e := densityEquiv (𝕜 := 𝕜) μ
  let D := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let g : ℕ → Lp 𝕜 ∞ μ := fun n => D (L n)
  have hg : ∀ φ : Lp 𝕜 ∞ μ →L[𝕜] 𝕜,
      Tendsto (fun n => φ (g n)) atTop (𝓝 0) :=
    fun φ => hL (φ.comp D)
  obtain ⟨C, hC⟩ := WeakLinfinityFiniteL1.weakNull_norm_bounded hg
  obtain ⟨M, hM⟩ := WeakLinfinityFiniteL1.weakNull_norm_bounded hf
  have hcontrols := weak_l1_null_controls μ f (by
    intro φ
    simpa only [map_zero] using hf φ)
  have hdiag := diagonal_integral_tendsto_zero μ f g hcontrols
    (WeakLinfinityFiniteL1.ae_tendsto_zero hg) C M
    ((norm_nonneg (g 0)).trans (hC 0)) ((norm_nonneg (f 0)).trans (hM 0))
    (fun n => (WeakLinfinityFiniteL1.ae_norm_le (g n)).mono fun x hx => hx.trans (hC n))
    (fun n => (L1.norm_eq_integral_norm (f n)).symm ▸ hM n)
  have hrep (n : ℕ) : L n (f n) = ∫ x, f n x * g n x ∂μ := by
    have he : lpIntegralPairing μ 1 ∞ (g n) = L n := e.apply_symm_apply (L n)
    rw [← he]
    exact (lp_pairing_integral μ 1 ∞ (g n) (f n)).2
  simpa only [← hrep] using hdiag

open D11.Ch20.LpDualSigmafiniteLocal

/-- A countable family of ordinary L¹ classes has a common measurable
sigma-finite support. Restriction followed by extension fixes each class. -/
theorem common_sigmaFinite_support {α : Type u} {𝕜 : Type}
    [MeasurableSpace α] [RCLike 𝕜] (μ : Measure α) (f : ℕ → Lp 𝕜 1 μ) :
    ∃ S : Set α, ∃ hS : MeasurableSet S, SigmaFinite (μ.restrict S) ∧
      ∀ n, extendLp μ 1 S hS (restrictLp μ 1 S (f n)) = f n := by
  let E : ℕ → Set α := fun n => Function.support (f n : α → 𝕜)
  have hE (n : ℕ) : MeasurableSet (E n) ∧ SigmaFinite (μ.restrict (E n)) :=
    D11.Ch20.FunctionalVisibleSigmafiniteSupport.lp_support μ 1 (by simp) (f n)
  let S := ⋃ n, E n
  have hS : MeasurableSet S := MeasurableSet.iUnion (fun n => (hE n).1)
  refine ⟨S, hS, D11.Ch20.FunctionalVisibleSigmafiniteSupport.sigmaFinite_iUnion
    μ E (fun n => (hE n).1) (fun n => (hE n).2), fun n => ?_⟩
  exact D11.Ch20.FunctionalVisibleSigmafiniteSupport.cutoff_eq_of_support_subset
    μ 1 S hS (f n) (subset_iUnion E n)

/-- No endpoint dual representation is claimed for the original arbitrary
measure. Only the restrictions of the dual sequence to a common sigma-finite
support are represented. Both sequences remain weakly null under these
bounded linear maps. -/
theorem l1_weakNull_testing {α : Type u} {𝕜 : Type}
    [MeasurableSpace α] [RCLike 𝕜] (μ : Measure α) :
    DunfordPettisCriterion.WeakNullTestingProperty 𝕜 (Lp 𝕜 1 μ) := by
  intro f L hf hL
  obtain ⟨S, hS, hσ, hfix⟩ := common_sigmaFinite_support μ f
  letI : SigmaFinite (μ.restrict S) := hσ
  let R := restrictLp (𝕜 := 𝕜) μ 1 S
  let E := extendLp (𝕜 := 𝕜) μ 1 S hS
  let T : (Lp 𝕜 1 μ →L[𝕜] 𝕜) →L[𝕜] (Lp 𝕜 1 (μ.restrict S) →L[𝕜] 𝕜) :=
    ContinuousLinearMap.compL 𝕜 _ _ _ |>.flip E
  have ht := sigmaFinite_weakNull_testing (μ.restrict S)
    (fun n => R (f n)) (fun n => T (L n))
    (fun φ => hf (φ.comp R)) (fun ξ => hL (ξ.comp T))
  have heq (n : ℕ) : T (L n) (R (f n)) = L n (f n) := by
    change L n (E (R (f n))) = L n (f n)
    rw [hfix n]
  simpa only [heq] using ht

/-- Full Dunford--Pettis property, over either scalar field and on every
positive measure space. The target Banach space has arbitrary universe. -/
theorem l1_theorem (𝕜 : Type) [RCLike 𝕜] : Spec.L1Theorem.{u,w} 𝕜 := by
  intro α _ μ
  have ht := l1_weakNull_testing (𝕜 := 𝕜) μ
  exact ⟨ht, fun Y _ _ _ T hT =>
    DunfordPettisCriterion.testing_implies_operator_property 𝕜 (Lp 𝕜 1 μ) Y ht T hT⟩

theorem real_classical_examples : Spec.RealClassicalExamples.{u,w} :=
  ⟨DunfordPettisContinuousFunctions.real_theorem, l1_theorem ℝ⟩

theorem complex_classical_examples : Spec.ComplexClassicalExamples.{u,w} :=
  ⟨DunfordPettisContinuousFunctions.complex_theorem, l1_theorem ℂ⟩

end ExpandedFA.Compactness.DunfordPettisL1
