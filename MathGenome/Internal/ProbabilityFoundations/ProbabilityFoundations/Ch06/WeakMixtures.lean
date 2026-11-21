import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.VaryingMapping
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelComposition
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakMixtures

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ProbabilityFoundations.Ch06

universe u v
noncomputable section

/-- The probability law obtained by mixing a Markov kernel with a probability law. -/
def mixedLaw {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : ProbabilityMeasure S) (K : Kernel S T) [IsMarkovKernel K] : ProbabilityMeasure T :=
  ⟨K ∘ₘ (μ : Measure S), inferInstance⟩

/-- The composition integral formula for a bounded continuous test of a mixture. -/
lemma mixedLaw_integral {S : Type u} {T : Type v}
    [MeasurableSpace S] [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (μ : ProbabilityMeasure S) (K : Kernel S T) [IsMarkovKernel K] (f : T →ᵇ ℝ) :
    (∫ y, f y ∂(mixedLaw μ K : Measure T)) = ∫ x, ∫ y, f y ∂K x ∂(μ : Measure S) := by
  exact (Ch04.kernelComposition_integral (Kernel.const Unit (μ : Measure S)) K () f
    (f.integrable (mixedLaw μ K : Measure T))).2

/-- A bounded continuous real function agreeing with the identity on a fixed interval. -/
private lemma exists_bounded_identity (M : ℝ) (hM : 0 ≤ M) :
    ∃ f : ℝ →ᵇ ℝ, ∀ t : ℝ, ‖t‖ ≤ M → f t = t := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun t => max (-M) (min M t), by fun_prop⟩ (2 * M) (by
      intro x y
      have hxlo := le_max_left (-M) (min M x)
      have hylo := le_max_left (-M) (min M y)
      have hxhi : max (-M) (min M x) ≤ M := max_le (by linarith) (min_le_left _ _)
      have hyhi : max (-M) (min M y) ≤ M := max_le (by linarith) (min_le_left _ _)
      change |max (-M) (min M x) - max (-M) (min M y)| ≤ 2 * M
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
  refine ⟨f, fun t ht => ?_⟩
  change max (-M) (min M t) = t
  have ht' := abs_le.mp ht
  rw [min_eq_right ht'.2, max_eq_right ht'.1]

/-- Mixtures converge under the varying sequential weak-continuity hypothesis. -/
theorem weak_mixtures {S : Type u} {T : Type v}
    [MetricSpace S] [MetricSpace T]
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace T] [BorelSpace T]
    (ηs : ℕ → ProbabilityMeasure S) (η : ProbabilityMeasure S)
    (Ks : ℕ → Kernel S T) (K : Kernel S T)
    [∀ n, IsMarkovKernel (Ks n)] [IsMarkovKernel K]
    (hη : WeaklyConverges atTop ηs η)
    (C : Set S) (hC : MeasurableSet C) (hηC : (η : Measure S) C = 1)
    (hseq : ∀ x ∈ C, ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 x) →
      WeaklyConverges atTop
        (fun n => (⟨Ks n (xs n), inferInstance⟩ : ProbabilityMeasure T))
        (⟨K x, inferInstance⟩ : ProbabilityMeasure T)) :
    WeaklyConverges atTop (fun n => mixedLaw (ηs n) (Ks n)) (mixedLaw η K) := by
  apply (weaklyConverges_iff_integrals _ _ _).mpr
  intro f
  let gs : ℕ → S → ℝ := fun n x => ∫ y, f y ∂Ks n x
  let g : S → ℝ := fun x => ∫ y, f y ∂K x
  have hgs (n : ℕ) : Measurable (gs n) :=
    Ch04.kernelComposition_integral_measurable (Ks n) f f.continuous.measurable
  have hg : Measurable g :=
    Ch04.kernelComposition_integral_measurable K f f.continuous.measurable
  have hmap : WeaklyConverges atTop (fun n => (ηs n).map (gs n)) (η.map g) := by
    apply varying_mapping ηs η gs g hgs hg hη C hC hηC
    intro x hx xs hxs
    exact (weaklyConverges_iff_integrals atTop
      (fun n => (⟨Ks n (xs n), inferInstance⟩ : ProbabilityMeasure T))
      (⟨K x, inferInstance⟩ : ProbabilityMeasure T)).mp (hseq x hx xs hxs) f
  have hbound (L : Kernel S T) [IsMarkovKernel L] (x : S) :
      ‖∫ y, f y ∂L x‖ ≤ ‖f‖ := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := L x) (Eventually.of_forall f.norm_coe_le_norm)
  obtain ⟨q, hq⟩ := exists_bounded_identity ‖f‖ (norm_nonneg f)
  have heq (μ : ProbabilityMeasure S) (L : Kernel S T) [IsMarkovKernel L]
      (j : S → ℝ) (hj : Measurable j) (he : ∀ x, j x = ∫ y, f y ∂L x) :
      (∫ t, q t ∂(μ.map j : Measure ℝ)) = ∫ x, ∫ y, f y ∂L x ∂(μ : Measure S) := by
    rw [ProbabilityMeasure.toMeasure_map μ]
    rw [integral_map hj.aemeasurable q.continuous.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change q (j x) = ∫ y, f y ∂L x
      rw [he x]
      exact hq _ (hbound L x)
  have htest := (weaklyConverges_iff_integrals _ _ _).mp hmap q
  simp_rw [heq _ _ _ (hgs _) (fun _ => rfl), heq _ _ _ hg (fun _ => rfl)] at htest
  simpa only [mixedLaw_integral] using htest

end
end ProbabilityFoundations.Ch06
