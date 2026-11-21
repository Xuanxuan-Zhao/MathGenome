import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Independent statements for paper.tex:5410–5417. All measures have exactly the
Borel domain. Errors are extended nonnegative reals; in particular every positive
real error is admitted. Uniform tightness uses a single compact set for the whole
family. No countability or nonempty-space hypothesis is added to the Radon result.
-/
namespace Specs.D11.Ch18.FiniteRadonTightness

open Set MeasureTheory
open scoped ENNReal
universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

def compactTight_type :=
  ∀ {X : Type u} [TopologicalSpace X], @Measure X (borel X) → Prop

def compactTight_value : compactTight_type.{u} := fun μ =>
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K, IsCompact K ∧ μ (univ \ K) < ε

def uniformlyCompactTight_type :=
  ∀ {X : Type u} [TopologicalSpace X], Set (@Measure X (borel X)) → Prop

def uniformlyCompactTight_value : uniformlyCompactTight_type.{u} := fun P =>
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K, IsCompact K ∧ ∀ μ ∈ P, μ (univ \ K) < ε

def naturalDirac_type := ℕ → @Measure ℝ (borel ℝ)

noncomputable def naturalDirac_value : naturalDirac_type :=
  fun n => Measure.dirac (n : ℝ)

def naturalDiracFamily_type := Set (@Measure ℝ (borel ℝ))

def naturalDiracFamily_value : Set (@Measure ℝ (borel ℝ)) := Set.range naturalDirac_value

def finite_radon_compactTight : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)),
    RadonPredicates.isRadonValue μ → μ univ < ∞ → compactTight_value μ

def naturalDirac_probability_radon_tight : Prop :=
  ∀ n : ℕ, IsProbabilityMeasure (naturalDirac_value n) ∧
    RadonPredicates.isRadonValue (naturalDirac_value n) ∧
    compactTight_value (naturalDirac_value n)

/-- Every compact set misses the entire mass of at least one member. -/
def naturalDirac_escapes_compact : Prop :=
  ∀ K : Set ℝ, IsCompact K → ∃ n : ℕ, naturalDirac_value n (univ \ K) = 1

/-- The same family fails the shared compact bound at every positive error < 1. -/
def naturalDirac_not_uniform_at_error : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ε < 1 →
    ¬ ∃ K : Set ℝ, IsCompact K ∧
      ∀ μ ∈ naturalDiracFamily_value, μ (univ \ K) < ε

def naturalDirac_not_uniformlyCompactTight : Prop :=
  ¬ uniformlyCompactTight_value naturalDiracFamily_value

end Specs.D11.Ch18.FiniteRadonTightness
