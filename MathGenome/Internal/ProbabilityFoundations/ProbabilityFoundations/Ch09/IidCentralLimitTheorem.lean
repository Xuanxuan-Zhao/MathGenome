import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.IidCentralLimitTheorem
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.GaussianProjectionCriterion
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.CramerWold
import Mathlib.Probability.CentralLimitTheorem

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped RealInnerProductSpace

namespace ProbabilityFoundations.Ch09

open Ch07

/-- The scalar CLT with its actual variance, including zero variance. -/
theorem scalar_iid_clt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X P)
    (hd : ∀ k, IdentDistrib (X k) (X 0) P P)
    (h₂ : Integrable (fun ω => (X 0 ω) ^ 2) P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - ∫ ω, X 0 ω ∂P))
      atTop id (fun _ => P) (gaussianReal 0 (Var[X 0; P]).toNNReal) := by
  have hm : MemLp (X 0) 2 P :=
    (memLp_two_iff_integrable_sq (hX 0).aestronglyMeasurable).mpr h₂
  convert tendstoInDistribution_inv_sqrt_mul_sum_sub HasLaw.id hm hi hd using 1
  ext n ω
  simp [Finset.sum_sub_distrib]

/-- Zero variance gives a single full-measure event for every term and sum. -/
theorem zero_variance_centered_sums {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hd : ∀ k, IdentDistrib (X k) (X 0) P P)
    (h₂ : Integrable (fun ω => (X 0 ω) ^ 2) P) (hv : Var[X 0; P] = 0) :
    ∀ᵐ ω ∂P,
      (∀ k, X k ω - ∫ ω, X 0 ω ∂P = 0) ∧
      (∀ n, ∑ k ∈ Finset.range n, (X k ω - ∫ ω, X 0 ω ∂P) = 0) ∧
      (∀ (n : ℕ), (Real.sqrt n)⁻¹ *
        ∑ k ∈ Finset.range n, (X k ω - ∫ ω, X 0 ω ∂P) = 0) := by
  have hm : MemLp (X 0) 2 P :=
    (memLp_two_iff_integrable_sq (hX 0).aestronglyMeasurable).mpr h₂
  have ha : ∀ᵐ ω ∂P, ∀ k, X k ω = ∫ ω, X 0 ω ∂P := by
    apply ae_all_iff.mpr
    intro k
    have hk := ae_eq_integral_of_variance_eq_zero ((hd k).memLp_iff.mpr hm)
      ((hd k).variance_eq.trans hv)
    simpa only [(hd k).integral_eq] using hk
  filter_upwards [ha] with ω hω
  simp [hω]

/-- A finite-moment projection has variance given by the covariance quadratic form. -/
theorem variance_projection {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d)
    (hX : Measurable X) (h₂ : MemLp X 2 P) (t : Euclidean d) :
    Var[fun ω => inner ℝ t (X ω); P] =
      t ⬝ᵥ vectorCovariance P X *ᵥ t := by
  have hm : MemLp id 2 (P.map X) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).mpr h₂
  rw [← covarianceBilin_eq_vectorCovariance P X h₂, covarianceBilin_self hm]
  exact (variance_map (by fun_prop) hX.aemeasurable).symm

/-- The full finite-dimensional CLT, with no invertibility assumption. -/
theorem iid_vector_clt {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → Euclidean d)
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X P)
    (hd : ∀ k, IdentDistrib (X k) (X 0) P P)
    (h₂ : Integrable (fun ω => ‖X 0 ω‖ ^ 2) P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ •
        ∑ k ∈ Finset.range n, (X k ω - vectorMean P (X 0)))
      atTop id (fun _ => P) (gaussianLaw 0 (vectorCovariance P (X 0))) := by
  have hm : MemLp (X 0) 2 P :=
    (memLp_two_iff_integrable_sq_norm (hX 0).aestronglyMeasurable).mpr h₂
  have hS := vectorCovariance_posSemidef P (X 0) hm
  let S (n : ℕ) (ω : Ω) := (Real.sqrt n)⁻¹ •
    ∑ k ∈ Finset.range n, (X k ω - vectorMean P (X 0))
  have hSm (n : ℕ) : Measurable (S n) := by
    exact (Finset.measurable_sum _ (fun k _ => (hX k).sub measurable_const)).const_smul
      ((Real.sqrt n)⁻¹ : ℝ)
  let μs : ℕ → ProbabilityMeasure (Euclidean d) := fun n =>
    Ch06.probabilityLaw P (S n) (hSm n)
  let μ : ProbabilityMeasure (Euclidean d) :=
    ⟨gaussianLaw 0 (vectorCovariance P (X 0)), inferInstance⟩
  have hconv : Ch06.WeaklyConverges atTop μs μ := by
    apply (weaklyConverges_iff_linear_projections μs μ).mpr
    intro t
    let Y (k : ℕ) (ω : Ω) := inner ℝ t (X k ω)
    have hYi : iIndepFun Y P := hi.comp (fun _ x => inner ℝ t x) (by fun_prop)
    have hYd (k : ℕ) : IdentDistrib (Y k) (Y 0) P P :=
      (hd k).comp (by fun_prop : Measurable (fun x : Euclidean d => inner ℝ t x))
    have hY₂ : MemLp (Y 0) 2 P := (innerSL ℝ t).comp_memLp' hm
    have hmean : (∫ ω, Y 0 ω ∂P) = inner ℝ t (vectorMean P (X 0)) :=
      integral_inner (hm.integrable (by simp)) t
    have hvar : Var[Y 0; P] = t ⬝ᵥ vectorCovariance P (X 0) *ᵥ t :=
      variance_projection P (X 0) (hX 0) hm t
    have hLaw : HasLaw (fun x : Euclidean d => inner ℝ t x)
        (gaussianReal 0 (Var[Y 0; P]).toNNReal)
        (gaussianLaw 0 (vectorCovariance P (X 0))) := by
      refine ⟨by fun_prop, ?_⟩
      simpa only [inner_zero_right, hvar] using
        gaussianLaw_map_projection 0 (vectorCovariance P (X 0)) hS t
    have ht := tendstoInDistribution_inv_sqrt_mul_sum_sub hLaw hY₂ hYi hYd
    have heq (n : ℕ) :
        (fun x => inner ℝ t x) ∘ S n =
          fun ω => (Real.sqrt n)⁻¹ *
            (∑ k ∈ Finset.range n, Y k ω - n * ∫ ω, Y 0 ω ∂P) := by
      ext ω
      simp [S, Y, hmean, inner_smul_right, inner_sum, inner_sub_right,
        Finset.sum_sub_distrib, ← Nat.cast_smul_eq_nsmul ℝ]
    have hmap (n : ℕ) :
        ((μs n).map (fun x => inner ℝ t x) : Measure ℝ) =
          P.map (fun ω => (Real.sqrt n)⁻¹ *
            (∑ k ∈ Finset.range n, Y k ω - n * ∫ ω, Y 0 ω ∂P)) := by
      simp only [ProbabilityMeasure.toMeasure_map, μs, Ch06.probabilityLaw_toMeasure]
      rw [Measure.map_map (by fun_prop) (hSm n), heq n]
    have hfun : (fun n => (μs n).map (fun x => inner ℝ t x)) =
        (fun (n : ℕ) => (⟨P.map (fun ω => (Real.sqrt n)⁻¹ *
          (∑ k ∈ Finset.range n, Y k ω - n * ∫ ω, Y 0 ω ∂P)),
          inferInstance⟩ : ProbabilityMeasure ℝ)) := by
      funext n
      exact Subtype.ext (hmap n)
    unfold Ch06.WeaklyConverges
    rw [hfun]
    exact ht.tendsto
  refine ⟨fun n => (hSm n).aemeasurable, aemeasurable_id, ?_⟩
  simpa only [Ch06.WeaklyConverges, μs, μ, Ch06.probabilityLaw, Ch01.law, S,
    Measure.map_id] using hconv

end ProbabilityFoundations.Ch09
