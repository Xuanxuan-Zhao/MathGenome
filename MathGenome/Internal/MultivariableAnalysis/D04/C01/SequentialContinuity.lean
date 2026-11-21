import MathGenome.Internal.MultivariableAnalysis.D04.C01.CoordinateEstimates
import MathGenome.Internal.MultivariableAnalysis.D04.C01.TopologicalTests
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.SequentialContinuity

/-! Sequential and coordinate criteria on the specified relative domain.
The auxiliary metric-target criterion uses the sequence characterization of
closure of the bad-value set; this gives the converse without assuming that
the limit point belongs to the domain. -/

open Set Filter Topology
namespace D04

private theorem punctured_criterion {n : ℕ} {Y : Type*} [PseudoMetricSpace Y]
    (A : Set (E n)) (f : A → Y) (a : E n) (b : Y) :
    (∀ ε > 0, ∃ δ > 0, ∀ x : A,
      0 < ‖(x : E n) - a‖ → ‖(x : E n) - a‖ < δ → dist (f x) b < ε) ↔
    ∀ s : ℕ → A, (∀ k, (s k : E n) ≠ a) →
      Tendsto (fun k => (s k : E n)) atTop (𝓝 a) →
      Tendsto (fun k => f (s k)) atTop (𝓝 b) := by
  constructor
  · intro h s hs ht
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    filter_upwards [Metric.tendsto_nhds.mp ht δ hδ] with k hk
    exact hd (s k) (norm_pos_iff.mpr (sub_ne_zero.mpr (hs k)))
      (by simpa only [dist_eq_norm] using hk)
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨ε, hε, he⟩ := hn
    let B : Set (E n) := {x | ∃ hx : x ∈ A,
      x ≠ a ∧ ε ≤ dist (f ⟨x, hx⟩) b}
    have hc : a ∈ Closure B := by
      intro r hr
      obtain ⟨x, hxpos, hxr, hbad⟩ := he r hr
      refine ⟨x, ?_, hxr⟩
      exact ⟨x.property, sub_ne_zero.mp (norm_pos_iff.mp hxpos), hbad⟩
    obtain ⟨s, hs, ht⟩ := (mem_closure_iff_sequence B a).mp hc
    let u : ℕ → A := fun k => ⟨s k, (hs k).choose⟩
    have hu : ∀ k, (u k : E n) ≠ a := fun k => (hs k).choose_spec.1
    have hlim := h u hu ht
    obtain ⟨k, hk⟩ := (Metric.tendsto_nhds.mp hlim ε hε).exists
    exact (not_lt_of_ge (hs k).choose_spec.2) hk

theorem relativeLimit_iff_sequence {n m : ℕ} (A : Set (E n)) (f : A → E m)
    (a : E n) (b : E m) (ha : AccumulationPoint A a) :
    RelativeLimit A f a b ↔
      ∀ s : ℕ → A, (∀ k, (s k : E n) ≠ a) →
        Tendsto (fun k => (s k : E n)) atTop (𝓝 a) →
        Tendsto (fun k => f (s k)) atTop (𝓝 b) := by
  simpa only [RelativeLimit, ha, true_and, dist_eq_norm] using
    punctured_criterion A f a b

theorem relativeContinuousAt_iff_sequence {n m : ℕ} (A : Set (E n))
    (f : A → E m) (a : A) :
    RelativeContinuousAt A f a ↔
      ∀ s : ℕ → A, Tendsto (fun k => (s k : E n)) atTop (𝓝 (a : E n)) →
        Tendsto (fun k => f (s k)) atTop (𝓝 (f a)) := by
  rw [relativeContinuousAt_iff]
  change Tendsto f (𝓝 a) (𝓝 (f a)) ↔ _
  rw [tendsto_nhds_iff_seq_tendsto]
  simp only [tendsto_subtype_rng, Function.comp_def]

theorem relativeLimit_unique {n m : ℕ} (A : Set (E n)) (f : A → E m)
    (a : E n) (b c : E m) (ha : AccumulationPoint A a)
    (hb : RelativeLimit A f a b) (hc : RelativeLimit A f a c) : b = c := by
  obtain ⟨s, hs, ht⟩ := (accumulationPoint_iff_sequence A a).mp ha
  let u : ℕ → A := fun k => ⟨s k, (hs k).1⟩
  have hu : ∀ k, (u k : E n) ≠ a := fun k => (hs k).2
  exact tendsto_nhds_unique
    ((relativeLimit_iff_sequence A f a b ha).mp hb u hu ht)
    ((relativeLimit_iff_sequence A f a c ha).mp hc u hu ht)

theorem relativeLimit_iff_coordinates {n m : ℕ} (A : Set (E n)) (f : A → E m)
    (a : E n) (b : E m) (ha : AccumulationPoint A a) :
    RelativeLimit A f a b ↔
      ∀ i : Fin m, ∀ ε > 0, ∃ δ > 0, ∀ x : A,
        0 < ‖(x : E n) - a‖ → ‖(x : E n) - a‖ < δ → |f x i - b i| < ε := by
  rw [relativeLimit_iff_sequence A f a b ha]
  simp_rw [← Real.dist_eq, punctured_criterion]
  constructor
  · intro h i s hs ht
    exact (tendsto_iff_coordinate_tendsto (fun k => f (s k)) b).mp (h s hs ht) i
  · intro h s hs ht
    exact (tendsto_iff_coordinate_tendsto (fun k => f (s k)) b).mpr
      (fun i => h i s hs ht)

theorem relativeContinuousAt_iff_coordinates {n m : ℕ} (A : Set (E n))
    (f : A → E m) (a : A) :
    RelativeContinuousAt A f a ↔
      ∀ i : Fin m, ∀ ε > 0, ∃ δ > 0, ∀ x : A,
        ‖(x : E n) - (a : E n)‖ < δ → |f x i - f a i| < ε := by
  have hscalar (i : Fin m) :
      (∀ ε > 0, ∃ δ > 0, ∀ x : A,
        ‖(x : E n) - (a : E n)‖ < δ → |f x i - f a i| < ε) ↔
      ContinuousAt (fun x => f x i) a := by
    rw [Metric.continuousAt_iff]
    simp only [Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs]
  simp_rw [hscalar]
  rw [relativeContinuousAt_iff]
  constructor
  · intro h i
    exact (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).continuousAt.comp h
  · intro h
    have hc : ContinuousAt (fun x => fun i : Fin m => f x i) a :=
      continuousAt_pi.mpr h
    exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).continuousAt.comp hc

end D04
