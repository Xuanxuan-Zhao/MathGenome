import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakMetrics

/-!
# The Prokhorov and bounded Lipschitz expressions

Definitions in paper.tex, §6.9, lines 2034–2050. The distances are defined by
exactly the real infimum and supremum in the source, on canonical Borel
probability laws on an arbitrary metric space. The elementary bounds below
ensure that these extrema are over nonempty sets with the required bounds.
Metric axioms and comparison with weak convergence are separate obligations.
-/

open MeasureTheory

namespace ProbabilityFoundations.Ch06

universe u
noncomputable section

/-- Open enlargement `A^a`; the existential also enforces `∅^a = ∅`.
For nonpositive radii the enlargement is empty. -/
def enlargement {S : Type u} [MetricSpace S] (a : ℝ) (A : Set S) : Set S :=
  {x | ∃ y ∈ A, dist x y < a}

/-- A positive radius satisfying both Borel-set inequalities in the source. -/
def ProkhorovAdmissible {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) (a : ℝ) : Prop :=
  0 < a ∧ ∀ A : Set S, MeasurableSet A →
    (μ : Measure S).real A ≤ (ν : Measure S).real (enlargement a A) + a ∧
    (ν : Measure S).real A ≤ (μ : Measure S).real (enlargement a A) + a

/-- The source's positive-radius, real-valued Prokhorov infimum. -/
def prokhorovDist {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) : ℝ :=
  sInf {a : ℝ | ProkhorovAdmissible μ ν a}

/-- Both the pointwise absolute bound and the Lipschitz constant are at most one. -/
def IsBoundedLipschitzTest {S : Type u} [MetricSpace S] (f : S → ℝ) : Prop :=
  (∀ x, |f x| ≤ 1) ∧ LipschitzWith 1 f

/-- The supremum uses all real functions with the two separate unit bounds. -/
def boundedLipschitzDist {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) : ℝ :=
  sSup {r : ℝ | ∃ f : S → ℝ, IsBoundedLipschitzTest f ∧
    r = |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)|}

@[simp] theorem enlargement_empty {S : Type u} [MetricSpace S] (a : ℝ) :
    enlargement a (∅ : Set S) = ∅ := by
  ext x
  simp [enlargement]

/-- This identifies the empty-safe definition with Mathlib's open thickening. -/
theorem enlargement_eq_thickening {S : Type u} [MetricSpace S] (a : ℝ) (A : Set S) :
    enlargement a A = Metric.thickening a A := by
  ext x
  exact Metric.mem_thickening_iff.symm

/-- On a nonempty set it is exactly the strict distance-to-set inequality. -/
theorem mem_enlargement_iff_infDist_lt {S : Type u} [MetricSpace S]
    (A : Set S) (hA : A.Nonempty) (a : ℝ) (x : S) :
    x ∈ enlargement a A ↔ Metric.infDist x A < a := by
  rw [enlargement_eq_thickening]
  exact Metric.mem_thickening_iff_infDist_lt hA

theorem enlargement_isOpen {S : Type u} [MetricSpace S] (a : ℝ) (A : Set S) :
    IsOpen (enlargement a A) := by
  rw [enlargement_eq_thickening]
  exact Metric.isOpen_thickening

/-- The `LipschitzWith` constraint is precisely the source's unit Lipschitz bound. -/
theorem isBoundedLipschitzTest_iff {S : Type u} [MetricSpace S] (f : S → ℝ) :
    IsBoundedLipschitzTest f ↔
      (∀ x, |f x| ≤ 1) ∧ ∀ x y, |f x - f y| ≤ dist x y := by
  simp [IsBoundedLipschitzTest, lipschitzWith_iff_dist_le_mul, Real.dist_eq]

/-- The defining tests are measurable and integrable, even without separability. -/
theorem boundedLipschitzTest_integrable {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (f : S → ℝ)
    (hf : IsBoundedLipschitzTest f) (μ : ProbabilityMeasure S) :
    Integrable f (μ : Measure S) := by
  exact Integrable.of_bound hf.2.continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hf.1 x)

/-- The radius set is nonempty, since radius one is always admissible. -/
theorem prokhorovAdmissible_one {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) :
    ProkhorovAdmissible μ ν 1 := by
  refine ⟨zero_lt_one, fun A _ => ⟨?_, ?_⟩⟩
  · exact measureReal_le_one.trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  · exact measureReal_le_one.trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)

theorem prokhorovRadii_bddBelow {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) :
    BddBelow {a : ℝ | ProkhorovAdmissible μ ν a} :=
  ⟨0, fun _ ha => ha.1.le⟩

theorem prokhorovDist_le_of_admissible {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) (a : ℝ)
    (ha : ProkhorovAdmissible μ ν a) : prokhorovDist μ ν ≤ a :=
  csInf_le (prokhorovRadii_bddBelow μ ν) ha

theorem prokhorovDist_bounds {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) :
    0 ≤ prokhorovDist μ ν ∧ prokhorovDist μ ν ≤ 1 := by
  refine ⟨le_csInf ⟨1, prokhorovAdmissible_one μ ν⟩ (fun _ ha => ha.1.le), ?_⟩
  exact prokhorovDist_le_of_admissible μ ν 1 (prokhorovAdmissible_one μ ν)

private theorem test_integral_abs_le_one {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (f : S → ℝ)
    (hf : IsBoundedLipschitzTest f) (μ : ProbabilityMeasure S) :
    |∫ x, f x ∂(μ : Measure S)| ≤ 1 := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (μ : Measure S)) (f := f) (C := 1)
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hf.1 x))

private theorem test_integral_sub_abs_le_two {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) (f : S → ℝ)
    (hf : IsBoundedLipschitzTest f) :
    |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)| ≤ 2 := by
  calc
    _ ≤ |∫ x, f x ∂(μ : Measure S)| + |∫ x, f x ∂(ν : Measure S)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (test_integral_abs_le_one f hf μ)
      (test_integral_abs_le_one f hf ν)
    _ = 2 := by norm_num

/-- The zero function provides an element of the supremum's indexing set. -/
theorem boundedLipschitzValues_nonempty {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) :
    Set.Nonempty {r : ℝ | ∃ f : S → ℝ, IsBoundedLipschitzTest f ∧
      r = |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)|} := by
  refine ⟨0, (fun _ => 0), ⟨?_, ?_⟩, ?_⟩
  · simp
  · exact LipschitzWith.const' (α := S) (0 : ℝ)
  · simp

theorem boundedLipschitzValues_bddAbove {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) :
    BddAbove {r : ℝ | ∃ f : S → ℝ, IsBoundedLipschitzTest f ∧
      r = |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)|} := by
  refine ⟨2, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact test_integral_sub_abs_le_two μ ν f hf

theorem test_integral_le_boundedLipschitzDist {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) (f : S → ℝ)
    (hf : IsBoundedLipschitzTest f) :
    |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)| ≤
      boundedLipschitzDist μ ν :=
  le_csSup (boundedLipschitzValues_bddAbove μ ν) ⟨f, hf, rfl⟩

theorem boundedLipschitzDist_bounds {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) :
    0 ≤ boundedLipschitzDist μ ν ∧ boundedLipschitzDist μ ν ≤ 2 := by
  constructor
  · obtain ⟨_, f, hf, _⟩ := boundedLipschitzValues_nonempty μ ν
    exact (abs_nonneg _).trans (test_integral_le_boundedLipschitzDist μ ν f hf)
  · exact csSup_le (boundedLipschitzValues_nonempty μ ν)
      (fun r ⟨f, hf, hr⟩ => hr ▸ test_integral_sub_abs_le_two μ ν f hf)

end
end ProbabilityFoundations.Ch06
