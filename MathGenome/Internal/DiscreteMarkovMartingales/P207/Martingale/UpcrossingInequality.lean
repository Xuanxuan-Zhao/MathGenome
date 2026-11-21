import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.GreedyUpcrossings
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UpcrossingInequality
import Mathlib.Probability.Martingale.OptionalStopping

open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

universe u
namespace P207

variable {Ω : Type u} [m : MeasurableSpace Ω]

theorem greedyUpcrossings_measurable (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX : Adapted ℱ X) (a b : ℝ) (hab : a < b) (n : ℕ) :
    Measurable[ℱ n] (fun ω => greedyUpcrossings (fun k => X k ω) a b n) := by
  classical
  have heq : (fun ω => greedyUpcrossings (fun k => X k ω) a b n) =
      fun ω => ∑ i ∈ Finset.Ico 1 (n + 1 + 1),
        {j | upperCrossingTime a b X (n + 1) j ω < n + 1}.indicator 1 i := by
    funext ω
    rw [greedyUpcrossings_eq_process_upcrossingsBefore]
    exact upcrossingsBefore_eq_sum hab
  rw [heq]
  refine Finset.measurable_fun_sum _ fun i _ => Measurable.indicator measurable_const ?_
  change MeasurableSet[ℱ n] {ω | upperCrossingTime a b X (n + 1) i ω < n + 1}
  have ht := hX.stronglyAdapted.isStoppingTime_upperCrossingTime
    (a := a) (b := b) (N := n + 1) (n := i) n
  simpa only [ENat.some_eq_natCast, Nat.cast_le, Nat.lt_succ_iff] using ht

theorem greedyUpcrossings_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (hX : Adapted ℱ X)
    (a b : ℝ) (hab : a < b) (n : ℕ) :
    Integrable (fun ω => (greedyUpcrossings (fun k => X k ω) a b n : ℝ)) μ := by
  have heq : (fun ω => (greedyUpcrossings (fun k => X k ω) a b n : ℝ)) =
      fun ω => (upcrossingsBefore a b X (n + 1) ω : ℝ) := by
    funext ω
    rw [greedyUpcrossings_eq_process_upcrossingsBefore]
  rw [heq]
  exact hX.stronglyAdapted.integrable_upcrossingsBefore (μ := μ) (N := n + 1) hab

/-- Retain the initial-value term from the complementary strategy estimate.
Unlike the library's final-positive-part estimate, this does not discard it. -/
private theorem upcrossingsBefore_sharp (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m) (f : ℕ → Ω → ℝ) (hf : Submartingale f ℱ μ)
    (a b : ℝ) (N : ℕ) (hfN : ∀ ω, a ≤ f N ω) (hab : a < b) :
    (b - a) * (∫ ω, (upcrossingsBefore a b f N ω : ℝ) ∂μ) ≤
      (∫ ω, f N ω ∂μ) - (∫ ω, f 0 ω ∂μ) := by
  calc
    _ ≤ μ[∑ k ∈ Finset.range N,
        upcrossingStrat a b f N k * (f (k + 1) - f k)] := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg ?_ ((hf.sum_upcrossingStrat_mul a b N).integrable N) ?_
      · exact Filter.Eventually.of_forall fun ω =>
          mul_nonneg (sub_nonneg.mpr hab.le) (Nat.cast_nonneg _)
      · filter_upwards with ω
        simpa using mul_upcrossingsBefore_le (hfN ω) hab
    _ ≤ (∫ ω, f N ω ∂μ) - (∫ ω, f 0 ω ∂μ) :=
      hf.sum_mul_upcrossingStrat_le

/-- Stop at `n` before using the strict cutoff `n + 1`: its extra gain is zero. -/
theorem upcrossing_inequality (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (hX : IsSubmartingale X ℱ μ)
    (a b : ℝ) (hab : a < b) (n : ℕ) :
    (b - a) * (∫ ω, (greedyUpcrossings (fun k => X k ω) a b n : ℝ) ∂μ) ≤
      (∫ ω, (X n ω - a)⁺ ∂μ) - (∫ ω, (X 0 ω - a)⁺ ∂μ) ∧
    (∫ ω, (X n ω - a)⁺ ∂μ) - (∫ ω, (X 0 ω - a)⁺ ∂μ) ≤
      (∫ ω, (X n ω - a)⁺ ∂μ) + (∫ ω, (X 0 ω - a)⁻ ∂μ) := by
  have hlib := (submartingale_iff_library μ ℱ X).mp hX
  let Y : ℕ → Ω → ℝ := fun k ω => (X k ω - a)⁺
  have hY : Submartingale Y ℱ μ :=
    (hlib.sub_martingale (martingale_const ℱ μ a)).pos
  let Z := stoppedProcess Y (fun _ : Ω => (n : WithTop ℕ))
  have hZ : Submartingale Z ℱ μ := hY.stoppedProcess (isStoppingTime_const ℱ n)
  have hle (k : ℕ) (hk : k ≤ n) (ω : Ω) : Z k ω = Y k ω := by
    exact stoppedProcess_eq_of_le (WithTop.coe_le_coe.mpr hk)
  have hN (ω : Ω) : Z (n + 1) ω = Y n ω := by
    change stoppedProcess Y (fun _ : Ω => (n : WithTop ℕ)) (n + 1) ω = Y n ω
    exact stoppedProcess_eq_of_ge (u := Y) (τ := fun _ : Ω => (n : WithTop ℕ))
      (i := n + 1) (WithTop.coe_le_coe.mpr n.le_succ)
  have hc (ω : Ω) : upcrossingsBefore 0 (b - a) Z (n + 1) ω =
      greedyUpcrossings (fun k => X k ω) a b n := by
    rw [← greedyUpcrossings_eq_process_upcrossingsBefore]
    rw [greedyUpcrossings_locality (fun k => Z k ω) (fun k => Y k ω)
      0 (b - a) n (sub_pos.mpr hab) (fun k hk => hle k hk ω)]
    rw [greedyUpcrossings_eq_process_upcrossingsBefore,
      upcrossingsBefore_pos_eq hab, greedyUpcrossings_eq_process_upcrossingsBefore]
  have hs := upcrossingsBefore_sharp μ ℱ Z hZ 0 (b - a) (n + 1)
    (fun ω => by rw [hN]; exact posPart_nonneg _) (sub_pos.mpr hab)
  have h0 (ω : Ω) : Z 0 ω = (X 0 ω - a)⁺ := hle 0 (Nat.zero_le n) ω
  simp only [sub_zero, hc, hN, h0] at hs
  refine ⟨hs, ?_⟩
  have hp : 0 ≤ ∫ ω, (X 0 ω - a)⁺ ∂μ := integral_nonneg fun _ => posPart_nonneg _
  have hm : 0 ≤ ∫ ω, (X 0 ω - a)⁻ ∂μ := integral_nonneg fun _ => negPart_nonneg _
  linarith

theorem upcrossing_inequality_weaker (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (hX : IsSubmartingale X ℱ μ)
    (a b : ℝ) (hab : a < b) (n : ℕ) :
    (b - a) * (∫ ω, (greedyUpcrossings (fun k => X k ω) a b n : ℝ) ∂μ) ≤
      (∫ ω, (X n ω - a)⁺ ∂μ) + (∫ ω, (X 0 ω - a)⁻ ∂μ) := by
  have h := upcrossing_inequality μ ℱ X hX a b hab n
  exact h.1.trans h.2

end P207
