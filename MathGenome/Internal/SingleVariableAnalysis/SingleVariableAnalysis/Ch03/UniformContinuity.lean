import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Archimedean
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.UniformContinuity

/-!
# Uniform continuity and its sequential obstruction

K03.03.uniform_continuity, paper.tex:585–591. The epsilon–delta condition is
stated on an arbitrary metric subset, including the empty set. The failure
proof uses countable choice to select bad pairs at radii 1/(n+1), then the
upstream Archimedean reciprocal bound to prove their distances tend to zero.
Its converse applies one uniform radius to a sufficiently late pair.
-/
namespace SingleVariableAnalysis

open scoped Topology
universe u v

def RelativeUniformContinuous
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → dist (f x) (f y) < ε

theorem relativeUniformContinuous_on_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) :
    RelativeUniformContinuous f E ↔ UniformContinuousOn f E := by
  exact Metric.uniformContinuousOn_iff.symm

theorem relativeUniformContinuous_subtype_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) :
    RelativeUniformContinuous f E ↔ UniformContinuous (fun x : E => f x) := by
  rw [relativeUniformContinuous_on_iff]
  exact uniformContinuousOn_iff_restrict

theorem relativeUniformContinuous_implies_continuous
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (h : RelativeUniformContinuous f E) :
    RelativeContinuous f E := by
  intro a ha ε hε
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  exact ⟨δ, hδ, fun x hx hd => hb x hx a ha hd⟩

theorem relativeUniformContinuous_failure_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) :
    ¬ RelativeUniformContinuous f E ↔
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ x y : ℕ → X,
        (∀ n, x n ∈ E) ∧ (∀ n, y n ∈ E) ∧
        Filter.Tendsto (fun n => dist (x n) (y n)) Filter.atTop (𝓝 (0 : ℝ)) ∧
        ∀ n, ε₀ ≤ dist (f (x n)) (f (y n)) := by
  classical
  constructor
  · intro hfail
    change ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → dist (f x) (f y) < ε) at hfail
    push Not at hfail
    obtain ⟨ε₀, hε₀, hb⟩ := hfail
    have bad (n : ℕ) : ∃ x ∈ E, ∃ y ∈ E,
        dist x y < 1 / ((n : ℝ) + 1) ∧ ε₀ ≤ dist (f x) (f y) :=
      hb _ (by positivity)
    choose x hx y hy hdist hbad using bad
    refine ⟨ε₀, hε₀, x, y, hx, hy, ?_, hbad⟩
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, _, hN⟩ := reciprocal_tail ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hr := hN (n + 1) (hn.trans (Nat.le_succ n))
    have hrec : 1 / ((n : ℝ) + 1) < ε := by
      simpa only [Nat.cast_add, Nat.cast_one, abs_of_pos (by positivity :
        0 < 1 / ((n : ℝ) + 1))] using hr
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using
      (hdist n).trans hrec
  · rintro ⟨ε₀, hε₀, x, y, hx, hy, hdist, hbad⟩ h
    obtain ⟨δ, hδ, hb⟩ := h ε₀ hε₀
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdist δ hδ
    have hd : dist (x N) (y N) < δ := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hN N le_rfl
    exact (not_lt_of_ge (hbad N)) (hb (x N) (hx N) (y N) (hy N) hd)

theorem real_relativeUniformContinuous_iff
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) :
    RelativeUniformContinuous f E ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → |f x - f y| < ε := by
  simp only [RelativeUniformContinuous, Real.dist_eq]

theorem complex_relativeUniformContinuous_iff
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) :
    RelativeUniformContinuous f E ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → ‖f x - f y‖ < ε := by
  simp only [RelativeUniformContinuous, dist_eq_norm]

theorem real_relativeUniformContinuous_failure_iff
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) :
    ¬ RelativeUniformContinuous f E ↔
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ x y : ℕ → X,
        (∀ n, x n ∈ E) ∧ (∀ n, y n ∈ E) ∧
        Filter.Tendsto (fun n => dist (x n) (y n)) Filter.atTop (𝓝 (0 : ℝ)) ∧
        ∀ n, ε₀ ≤ |f (x n) - f (y n)| := by
  simpa only [Real.dist_eq] using relativeUniformContinuous_failure_iff f E

theorem complex_relativeUniformContinuous_failure_iff
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) :
    ¬ RelativeUniformContinuous f E ↔
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ x y : ℕ → X,
        (∀ n, x n ∈ E) ∧ (∀ n, y n ∈ E) ∧
        Filter.Tendsto (fun n => dist (x n) (y n)) Filter.atTop (𝓝 (0 : ℝ)) ∧
        ∀ n, ε₀ ≤ ‖f (x n) - f (y n)‖ := by
  simpa only [dist_eq_norm] using relativeUniformContinuous_failure_iff f E

end SingleVariableAnalysis
