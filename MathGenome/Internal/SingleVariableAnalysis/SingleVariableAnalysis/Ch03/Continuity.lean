import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Sequential
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity

/-!
# Relative continuity

K03.03.continuity (paper.tex:489–506). We use the canonical induced topology
and metric on each domain subtype. The unpunctured epsilon condition includes
x = a. The sequential proof chooses bad points in radii 1/(n+1) if continuity
fails; it requires neither avoidance of a nor accumulation of the domain.
-/
namespace SingleVariableAnalysis

open scoped Topology
universe u v

def RelativeContinuousAt {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ E, dist x a < δ → dist (f x) (f a) < ε

def RelativeContinuous {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) : Prop :=
  ∀ a ∈ E, RelativeContinuousAt f E a

theorem relativeContinuousAt_within_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) :
    RelativeContinuousAt f E a ↔ ContinuousWithinAt f E a := by
  simp only [RelativeContinuousAt, Metric.continuousWithinAt_iff]

theorem relativeContinuousAt_subtype_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E) :
    RelativeContinuousAt f E a ↔ ContinuousAt (fun x : E => f x) a := by
  rw [relativeContinuousAt_within_iff]
  exact continuousWithinAt_iff_continuousAt_domRestrict f a.property

theorem relativeContinuous_subtype_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) :
    RelativeContinuous f E ↔ Continuous (fun x : E => f x) := by
  rw [continuous_iff_continuousAt]
  exact ⟨fun h a => (relativeContinuousAt_subtype_iff f E a).mp (h a a.property),
    fun h a ha => (relativeContinuousAt_subtype_iff f E ⟨a, ha⟩).mpr (h ⟨a, ha⟩)⟩

/-- Removing the test at a does not affect continuity, since its error is zero. -/
theorem relativeContinuousAt_punctured_iff_of_mem
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E) :
    RelativeContinuousAt f E a ↔ RelativePuncturedLimit f E a (f a) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx _ hd => hb x hx hd⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    refine ⟨δ, hδ, fun x hx hd => ?_⟩
    by_cases hxa : x = (a : X)
    · simpa only [hxa, dist_self] using hε
    · exact hb x hx (dist_pos.mpr hxa) hd

theorem relativeContinuousAt_punctured_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E) (_ha : DomainAccumulation E a) :
    RelativeContinuousAt f E a ↔ RelativePuncturedLimit f E a (f a) :=
  relativeContinuousAt_punctured_iff_of_mem f E a

theorem relativeContinuousAt_of_isolated
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E) (ha : ¬ DomainAccumulation E a) :
    RelativeContinuousAt f E a :=
  (relativeContinuousAt_punctured_iff_of_mem f E a).mpr
    (relativePuncturedLimit_of_not_accumulation f E a (f a) ha)

theorem relativeContinuousAt_of_isolating_ball
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E)
    (ha : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ E, dist x a < r → x = a) :
    RelativeContinuousAt f E a := by
  obtain ⟨r, hr, hb⟩ := ha
  intro ε hε
  exact ⟨r, hr, fun x hx hd => by simpa only [hb x hx hd, dist_self] using hε⟩

theorem relativeContinuousAt_sequential_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E) :
    RelativeContinuousAt f E a ↔
      ∀ x : ℕ → X, (∀ n, x n ∈ E) →
        Filter.Tendsto x Filter.atTop (𝓝 (a : X)) →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f a)) := by
  classical
  constructor
  · intro h x hx hxa
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hxa δ hδ
    exact ⟨N, fun n hn => hb (x n) (hx n) (hN n hn)⟩
  · intro h
    by_contra hfail
    change ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, dist x a < δ → dist (f x) (f a) < ε) at hfail
    push Not at hfail
    obtain ⟨ε, hε, hb⟩ := hfail
    have bad (n : ℕ) : ∃ x ∈ E, dist x a < 1 / ((n : ℝ) + 1) ∧
        ε ≤ dist (f x) (f a) := hb _ (by positivity)
    choose x hx hdist hbad using bad
    have hxa : Filter.Tendsto x Filter.atTop (𝓝 (a : X)) := by
      apply Metric.tendsto_atTop.mpr
      intro δ hδ
      obtain ⟨N, _, hN⟩ := reciprocal_tail δ hδ
      refine ⟨N, fun n hn => (hdist n).trans ?_⟩
      have hr := hN (n + 1) (hn.trans (Nat.le_succ n))
      simpa only [Nat.cast_add, Nat.cast_one, abs_of_pos (by positivity :
        0 < 1 / ((n : ℝ) + 1))] using hr
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h x hx hxa) ε hε
    exact (not_lt_of_ge (hbad N)) (hN N le_rfl)

theorem continuousAt_sequential_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (a : X) : ContinuousAt f a ↔
      ∀ x : ℕ → X, Filter.Tendsto x Filter.atTop (𝓝 a) →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f a)) := by
  have h := relativeContinuousAt_sequential_iff f Set.univ ⟨a, Set.mem_univ a⟩
  simpa only [relativeContinuousAt_within_iff, continuousWithinAt_univ,
    Set.mem_univ, implies_true, true_implies] using h

theorem real_relativeContinuousAt_iff
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E) :
    RelativeContinuousAt f E a ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, dist x a < δ → |f x - f a| < ε := by
  simp only [RelativeContinuousAt, Real.dist_eq]

theorem complex_relativeContinuousAt_iff
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E) :
    RelativeContinuousAt f E a ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, dist x a < δ → ‖f x - f a‖ < ε := by
  simp only [RelativeContinuousAt, dist_eq_norm]

theorem real_relativeContinuousAt_sequential_iff
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E) :
    RelativeContinuousAt f E a ↔
      ∀ x : ℕ → X, (∀ n, x n ∈ E) →
        Filter.Tendsto x Filter.atTop (𝓝 (a : X)) →
        RealSequenceConverges (fun n => f (x n)) (f a) := by
  simp only [realSequenceConverges_iff]
  exact relativeContinuousAt_sequential_iff f E a

theorem complex_relativeContinuousAt_sequential_iff
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E) :
    RelativeContinuousAt f E a ↔
      ∀ x : ℕ → X, (∀ n, x n ∈ E) →
        Filter.Tendsto x Filter.atTop (𝓝 (a : X)) →
        ComplexSequenceConverges (fun n => f (x n)) (f a) := by
  simp only [complexSequenceConverges_iff]
  exact relativeContinuousAt_sequential_iff f E a

theorem relativeOpen_iff {X : Type u} [MetricSpace X] (E : Set X) (U : Set E) :
    IsOpen U ↔ ∃ V : Set X, IsOpen V ∧ (Subtype.val ⁻¹' V : Set E) = U :=
  isOpen_induced_iff

theorem relativeClosed_iff {X : Type u} [MetricSpace X] (E : Set X) (F : Set E) :
    IsClosed F ↔ ∃ G : Set X, IsClosed G ∧ (Subtype.val ⁻¹' G : Set E) = F :=
  isClosed_induced_iff

theorem compact_relativeCover_iff {X : Type u} [MetricSpace X] (E : Set X) :
    IsCompact E ↔ ∀ {ι : Type u} (U : ι → Set E),
      (∀ i, IsOpen (U i)) → (Set.univ ⊆ ⋃ i, U i) →
        ∃ t : Finset ι, Set.univ ⊆ ⋃ i ∈ t, U i := by
  rw [isCompact_iff_isCompact_univ, isCompact_iff_finite_subcover]

end SingleVariableAnalysis
