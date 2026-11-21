import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.MeasurableMapTests
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
Independent interface for paper.tex:5751–5763. The ambient measurable space is
never completed or enlarged. The auxiliary measure is used only for its null
ideal, whose exact local-null interpretation is a separate required theorem.
`RCLike` permits both real and complex scalars with their Borel structures.
-/

open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
universe u v

namespace D11.Ch20.LocalNullVariant

/-- Local nullity only asserts a property of measurable sets. -/
def LocallyNull {X : Type u} [MeasurableSpace X] (μ : Measure X) (N : Set X) : Prop :=
  MeasurableSet N ∧ ∀ E : Set X, MeasurableSet E → μ E < ∞ → μ (N ∩ E) = 0

/-- All tests, including the empty set, are retained. -/
def FiniteMeasurable {X : Type u} [MeasurableSpace X] (μ : Measure X) :=
  {E : Set X // MeasurableSet E ∧ μ E < ∞}

/-- An auxiliary measure on the very same sigma-algebra. Its numerical values
are irrelevant; its measurable null sets will be proved to be the local ideal. -/
def TestingMeasure {X : Type u} [MeasurableSpace X] (μ : Measure X) : Measure X :=
  Measure.sum (fun E : FiniteMeasurable μ => μ.restrict E.val)

/-- Pointwise bounded, genuinely measurable scalar functions, as a submodule. -/
def boundedMeasurableSubmodule (X : Type u) [MeasurableSpace X]
    (𝕜 : Type v) [RCLike 𝕜] : Submodule 𝕜 (X → 𝕜) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C}
  zero_mem' := ⟨measurable_const, 0, le_rfl, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, C, hC, hfC⟩ ⟨hg, D, hD, hgD⟩
    refine ⟨hf.add hg, C + D, add_nonneg hC hD, fun x => ?_⟩
    exact (norm_add_le (f x) (g x)).trans (add_le_add (hfC x) (hgD x))
  smul_mem' := by
    rintro c f ⟨hf, C, hC, hfC⟩
    refine ⟨hf.const_smul c, ‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun x => ?_⟩
    simpa only [Pi.smul_apply, norm_smul] using
      mul_le_mul_of_nonneg_left (hfC x) (norm_nonneg c)

abbrev BoundedMeasurable (X : Type u) [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜] : Type (max u v) :=
  boundedMeasurableSubmodule X 𝕜

/-- This is a model of the local quotient; the required surjection and its
exact equality criterion below certify its interpretation. -/
abbrev LocalLInfinity {X : Type u} [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (μ : Measure X) : Type (max u v) := Lp 𝕜 ∞ (TestingMeasure μ)

theorem boundedMemLp {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
    (μ : Measure X) (f : BoundedMeasurable X 𝕜) : MemLp f.val ∞ (TestingMeasure μ) := by
  obtain ⟨C, _, hC⟩ := f.property.2
  exact memLp_top_of_bound f.property.1.aestronglyMeasurable C (Eventually.of_forall hC)

/-- The quotient projection from bounded measurable functions. -/
def ClassOf {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
    (μ : Measure X) (f : BoundedMeasurable X 𝕜) : LocalLInfinity 𝕜 μ :=
  (boundedMemLp μ f).toLp f.val

/-- The literal real infimum in the manuscript. The admissible set is nonempty
for each bounded representative, including when the space or measure is zero. -/
def LocalNorm {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
    (μ : Measure X) (f : BoundedMeasurable X 𝕜) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ LocallyNull μ {x | C < ‖f.val x‖}}

end D11.Ch20.LocalNullVariant

namespace Specs.D11.Ch20.LocalNullVariant
open _root_.D11.Ch20.LocalNullVariant

def locallyNull_type := ∀ {X : Type u} [MeasurableSpace X], Measure X → Set X → Prop
def locallyNull_value : locallyNull_type := LocallyNull
def localLInfinity_type := ∀ {X : Type u} [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜],
   Measure X → Type (max u v)
def localLInfinity_value : localLInfinity_type := fun 𝕜 _ μ => LocalLInfinity 𝕜 μ
def classOf_type := ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
   (μ : Measure X), BoundedMeasurable X 𝕜 → LocalLInfinity 𝕜 μ
def classOf_value : classOf_type := ClassOf
def localNorm_type := ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
   (μ : Measure X), BoundedMeasurable X 𝕜 → ℝ
def localNorm_value : localNorm_type := LocalNorm

def locallyNull_empty : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X), LocallyNull μ ∅
def locallyNull_subset : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (N A : Set X),
     LocallyNull μ N → MeasurableSet A → A ⊆ N → LocallyNull μ A
def locallyNull_iUnion : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (N : ℕ → Set X),
     (∀ n, LocallyNull μ (N n)) → LocallyNull μ (⋃ n, N n)
def testingMeasure_null_iff : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (N : Set X),
     MeasurableSet N → (TestingMeasure μ N = 0 ↔ LocallyNull μ N)
def classOf_eq_iff : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (f g : BoundedMeasurable X 𝕜),
     ClassOf μ f = ClassOf μ g ↔ LocallyNull μ {x | f.val x ≠ g.val x}
def classOf_add : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (f g : BoundedMeasurable X 𝕜),
     ClassOf μ (f + g) = ClassOf μ f + ClassOf μ g
def classOf_smul : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (c : 𝕜) (f : BoundedMeasurable X 𝕜),
     ClassOf μ (c • f) = c • ClassOf μ f
def bounded_representative : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (q : LocalLInfinity 𝕜 μ),
     ∃ f : BoundedMeasurable X 𝕜, ClassOf μ f = q ∧ ∀ x, ‖f.val x‖ ≤ ‖q‖
def norm_formula : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (f : BoundedMeasurable X 𝕜), ‖ClassOf μ f‖ = LocalNorm μ f
def norm_well_defined : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (f g : BoundedMeasurable X 𝕜),
     LocallyNull μ {x | f.val x ≠ g.val x} → LocalNorm μ f = LocalNorm μ g
def norm_nonneg : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (q : LocalLInfinity 𝕜 μ), 0 ≤ ‖q‖
def norm_triangle : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (q r : LocalLInfinity 𝕜 μ), ‖q + r‖ ≤ ‖q‖ + ‖r‖
def norm_homogeneous : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (c : 𝕜) (q : LocalLInfinity 𝕜 μ), ‖c • q‖ = ‖c‖ * ‖q‖
def norm_definite : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (q : LocalLInfinity 𝕜 μ), ‖q‖ = 0 ↔ q = 0
def localEssentiallyBounded_representative : Prop :=
   ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
     (μ : Measure X) (g : X → 𝕜), Measurable g →
     (∃ C : ℝ, 0 ≤ C ∧ LocallyNull μ {x | C < ‖g x‖}) →
     ∃ f : BoundedMeasurable X 𝕜, LocallyNull μ {x | f.val x ≠ g x}

/-- The warning in the definition is substantive: the measurable null ideals
can differ even on a single point. -/
def localNull_can_be_nonnull : Prop :=
  ∃ (m : MeasurableSpace Unit) (μ : @Measure Unit m) (N : Set Unit),
    @LocallyNull Unit m μ N ∧ μ N ≠ 0

end Specs.D11.Ch20.LocalNullVariant
