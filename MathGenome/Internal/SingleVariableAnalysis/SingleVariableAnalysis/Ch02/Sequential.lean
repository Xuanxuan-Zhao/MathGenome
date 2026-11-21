import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OneSided
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Archimedean
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Sequential

/-!
# The sequential criterion

K03.02.sequential. Failure of an epsilon condition supplies a bad point in
every radius 1/(n+1), or beyond every threshold n+1. Countable choice produces
a test sequence, and the upstream Archimedean estimates prove that it has the
required input limit. The chosen points remain a fixed positive distance from
the claimed output limit. Sided criteria restrict the finite metric result to
the intersection of E with the chosen open half-line.
-/
namespace SingleVariableAnalysis

open scoped Topology
universe u v

/-- The metric form includes all four real/complex input-output combinations. -/
theorem relativePuncturedLimit_sequential_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) (L : Y) (_ha : DomainAccumulation E a) :
    RelativePuncturedLimit f E a L ↔
      ∀ x : ℕ → X, (∀ n, x n ∈ E ∧ x n ≠ a) →
        Filter.Tendsto x Filter.atTop (𝓝 a) →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L) := by
  classical
  constructor
  · intro h x hx hxa
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hxa δ hδ
    exact ⟨N, fun n hn => hb (x n) (hx n).1 (dist_pos.mpr (hx n).2) (hN n hn)⟩
  · intro h
    by_contra hfail
    change ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, 0 < dist x a → dist x a < δ → dist (f x) L < ε) at hfail
    push Not at hfail
    obtain ⟨ε, hε, hb⟩ := hfail
    have bad (n : ℕ) : ∃ x ∈ E, 0 < dist x a ∧
        dist x a < 1 / ((n : ℝ) + 1) ∧ ε ≤ dist (f x) L :=
      hb (1 / ((n : ℝ) + 1)) (by positivity)
    choose x hx hpos hdist hbad using bad
    have hxa : Filter.Tendsto x Filter.atTop (𝓝 a) := by
      apply Metric.tendsto_atTop.mpr
      intro δ hδ
      obtain ⟨N, _, hN⟩ := reciprocal_tail δ hδ
      refine ⟨N, fun n hn => (hdist n).trans ?_⟩
      have hr := hN (n + 1) (hn.trans (Nat.le_succ n))
      simpa only [Nat.cast_add, Nat.cast_one, abs_of_pos (by positivity :
        0 < 1 / ((n : ℝ) + 1))] using hr
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (h x (fun n => ⟨hx n, dist_pos.mp (hpos n)⟩) hxa) ε hε
    exact (not_lt_of_ge (hbad N)) (hN N le_rfl)

theorem rightRelativeLimit_sequential_iff
    {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y)
    (ha : RightAccumulation E a) :
    RightRelativeLimit f E a L ↔
      ∀ x : ℕ → ℝ, (∀ n, x n ∈ E ∧ a < x n) →
        RealSequenceConverges x a →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L) := by
  rw [rightRelativeLimit_relative_iff, and_iff_right ha,
    relativePuncturedLimit_sequential_iff f (E ∩ Set.Ioi a) a L
      ((rightAccumulation_domain_iff E a).mp ha)]
  constructor
  · intro h x hx hxa
    exact h x (fun n => ⟨hx n, ne_of_gt (hx n).2⟩)
      ((realSequenceConverges_iff x a).mp hxa)
  · intro h x hx hxa
    exact h x (fun n => (hx n).1) ((realSequenceConverges_iff x a).mpr hxa)

theorem leftRelativeLimit_sequential_iff
    {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y)
    (ha : LeftAccumulation E a) :
    LeftRelativeLimit f E a L ↔
      ∀ x : ℕ → ℝ, (∀ n, x n ∈ E ∧ x n < a) →
        RealSequenceConverges x a →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L) := by
  rw [leftRelativeLimit_relative_iff, and_iff_right ha,
    relativePuncturedLimit_sequential_iff f (E ∩ Set.Iio a) a L
      ((leftAccumulation_domain_iff E a).mp ha)]
  constructor
  · intro h x hx hxa
    exact h x (fun n => ⟨hx n, ne_of_lt (hx n).2⟩)
      ((realSequenceConverges_iff x a).mp hxa)
  · intro h x hx hxa
    exact h x (fun n => (hx n).1) ((realSequenceConverges_iff x a).mpr hxa)

theorem limitAtPosInfinity_sequential_iff
    {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (L : Y)
    (hE : DomainUnboundedAbove E) :
    LimitAtPosInfinity f E L ↔
      ∀ x : ℕ → ℝ, (∀ n, x n ∈ E) → DivergesToPosInfinity x →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L) := by
  classical
  rw [limitAtPosInfinity_iff, and_iff_right hE]
  constructor
  · intro h x hx hxi
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨A, _, hb⟩ := h ε hε
    obtain ⟨N, hN⟩ := hxi A
    exact ⟨N, fun n hn => hb (x n) (hx n) (hN n hn)⟩
  · intro h
    by_contra hfail
    push Not at hfail
    obtain ⟨ε, hε, hb⟩ := hfail
    have bad (n : ℕ) : ∃ x ∈ E, (n : ℝ) + 1 < x ∧ ε ≤ dist (f x) L :=
      hb ((n : ℝ) + 1) (by positivity)
    choose x hx hlarge hbad using bad
    have hxi : DivergesToPosInfinity x := by
      intro B
      obtain ⟨N, _, hN⟩ := archimedean_bound B
      refine ⟨N, fun n hn => ?_⟩
      have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      exact hN.trans (lt_of_le_of_lt hcast (by linarith [hlarge n]))
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h x hx hxi) ε hε
    exact (not_lt_of_ge (hbad N)) (hN N le_rfl)

theorem limitAtNegInfinity_sequential_iff
    {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (L : Y)
    (hE : DomainUnboundedBelow E) :
    LimitAtNegInfinity f E L ↔
      ∀ x : ℕ → ℝ, (∀ n, x n ∈ E) → DivergesToNegInfinity x →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L) := by
  classical
  rw [limitAtNegInfinity_iff, and_iff_right hE]
  constructor
  · intro h x hx hxi
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨A, _, hb⟩ := h ε hε
    obtain ⟨N, hN⟩ := hxi (-A)
    exact ⟨N, fun n hn => hb (x n) (hx n) (hN n hn)⟩
  · intro h
    by_contra hfail
    push Not at hfail
    obtain ⟨ε, hε, hb⟩ := hfail
    have bad (n : ℕ) : ∃ x ∈ E, x < -((n : ℝ) + 1) ∧ ε ≤ dist (f x) L :=
      hb ((n : ℝ) + 1) (by positivity)
    choose x hx hsmall hbad using bad
    have hxi : DivergesToNegInfinity x := by
      intro B
      obtain ⟨N, _, hN⟩ := archimedean_bound (-B)
      refine ⟨N, fun n hn => ?_⟩
      have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith [hsmall n]
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h x hx hxi) ε hε
    exact (not_lt_of_ge (hbad N)) (hN N le_rfl)

theorem real_real_sequential_iff
    (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ) (L : ℝ) (ha : DomainAccumulation E a) :
    RelativePuncturedLimit f E a L ↔
      ∀ x : ℕ → ℝ, (∀ n, x n ∈ E ∧ x n ≠ a) →
        RealSequenceConverges x a → RealSequenceConverges (fun n => f (x n)) L := by
  simp only [realSequenceConverges_iff, realSequenceConverges_iff]
  exact relativePuncturedLimit_sequential_iff f E a L ha

theorem real_complex_sequential_iff
    (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ) (L : ℂ) (ha : DomainAccumulation E a) :
    RelativePuncturedLimit f E a L ↔
      ∀ x : ℕ → ℝ, (∀ n, x n ∈ E ∧ x n ≠ a) →
        RealSequenceConverges x a → ComplexSequenceConverges (fun n => f (x n)) L := by
  simp only [realSequenceConverges_iff, complexSequenceConverges_iff]
  exact relativePuncturedLimit_sequential_iff f E a L ha

theorem complex_real_sequential_iff
    (f : ℂ → ℝ) (E : Set ℂ) (a : ℂ) (L : ℝ) (ha : DomainAccumulation E a) :
    RelativePuncturedLimit f E a L ↔
      ∀ x : ℕ → ℂ, (∀ n, x n ∈ E ∧ x n ≠ a) →
        ComplexSequenceConverges x a → RealSequenceConverges (fun n => f (x n)) L := by
  simp only [complexSequenceConverges_iff, realSequenceConverges_iff]
  exact relativePuncturedLimit_sequential_iff f E a L ha

theorem complex_complex_sequential_iff
    (f : ℂ → ℂ) (E : Set ℂ) (a : ℂ) (L : ℂ) (ha : DomainAccumulation E a) :
    RelativePuncturedLimit f E a L ↔
      ∀ x : ℕ → ℂ, (∀ n, x n ∈ E ∧ x n ≠ a) →
        ComplexSequenceConverges x a → ComplexSequenceConverges (fun n => f (x n)) L := by
  simp only [complexSequenceConverges_iff, complexSequenceConverges_iff]
  exact relativePuncturedLimit_sequential_iff f E a L ha

end SingleVariableAnalysis
