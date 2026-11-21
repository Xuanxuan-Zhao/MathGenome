import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureBoundsContinuity

/-!
# Elementary bounds and continuity for an arbitrary positive measure

This proves paper.tex:225–256 using the canonical measure from the upstream
source/native correspondence. All conclusions concern the original measurable
domain. In particular no global finite-measure instance is used to prove
continuity from above: its one finite term is passed explicitly.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology

universe u

namespace D11.Ch01.MeasureBoundsContinuity

theorem monotonicity {α : Type u} [MeasurableSpace α] (μ : Measure α)
    (A B : Set α) (_hA : MeasurableSet A) (_hB : MeasurableSet B) (hAB : A ⊆ B) :
    μ A ≤ μ B :=
  measure_mono hAB

theorem difference {α : Type u} [MeasurableSpace α] (μ : Measure α)
    (A B : Set α) (hA : MeasurableSet A) (_hB : MeasurableSet B)
    (hAB : A ⊆ B) (hfin : μ A < ∞) : μ (B \ A) = μ B - μ A :=
  measure_sdiff hAB hA.nullMeasurableSet hfin.ne

theorem countable_subadditivity {α : Type u} [MeasurableSpace α] (μ : Measure α)
    (E : ℕ → Set α) (_hE : ∀ n, MeasurableSet (E n)) :
    μ (⋃ n, E n) ≤ ∑' n, μ (E n) :=
  measure_iUnion_le E

theorem continuity_from_below {α : Type u} [MeasurableSpace α] (μ : Measure α)
    (E : ℕ → Set α) (s : Set α) (_hE : ∀ n, MeasurableSet (E n))
    (hmono : Monotone E) (hlim : (⋃ n, E n) = s) :
    Monotone (fun n => μ (E n)) ∧
    (⨆ n, μ (E n)) = μ s ∧
    Tendsto (fun n => μ (E n)) atTop (𝓝 (μ s)) := by
  subst s
  exact ⟨fun _ _ hij => measure_mono (hmono hij),
    hmono.measure_iUnion.symm, tendsto_measure_iUnion_atTop hmono⟩

theorem continuity_from_above {α : Type u} [MeasurableSpace α] (μ : Measure α)
    (E : ℕ → Set α) (s : Set α) (hE : ∀ n, MeasurableSet (E n))
    (hanti : Antitone E) (hlim : (⋂ n, E n) = s) (hfin : ∃ N, μ (E N) < ∞) :
    Antitone (fun n => μ (E n)) ∧
    (⨅ n, μ (E n)) = μ s ∧
    Tendsto (fun n => μ (E n)) atTop (𝓝 (μ s)) := by
  subst s
  have hfinite : ∃ N, μ (E N) ≠ ∞ := hfin.imp fun _ h => h.ne
  have hmeas : ∀ n, NullMeasurableSet (E n) μ := fun n => (hE n).nullMeasurableSet
  exact ⟨fun _ _ hij => measure_mono (hanti hij),
    (hanti.measure_iInter hmeas hfinite).symm,
    tendsto_measure_iInter_atTop hmeas hanti hfinite⟩

end D11.Ch01.MeasureBoundsContinuity
