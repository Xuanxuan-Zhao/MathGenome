import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Independent statements for paper.tex:5795–5800.  `Point` is the type synonym
`ℝ`, used to keep its countable-or-cocountable sigma-algebra distinct from the
Borel sigma-algebra on the scalar field. Its coordinate identification with
the real line is the identity. Counting measure is formed on exactly this
sigma-algebra. Native `Lp` denotes the ordinary measurable a.e. quotient,
identified with the source quotient by the accepted QuotientConstruction goal.
-/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace Specs.D11.Ch20.EndpointSurjectivityFailure

def Point := ℝ

@[instance_reducible]
def countableCocountable (X : Type*) : MeasurableSpace X where
  MeasurableSet' s := s.Countable ∨ sᶜ.Countable
  measurableSet_empty := Or.inl countable_empty
  measurableSet_compl := by
    intro s hs
    simpa only [compl_compl] using hs.symm
  measurableSet_iUnion := by
    intro s hs
    by_cases h : ∀ n, (s n).Countable
    · exact Or.inl (countable_iUnion h)
    · simp only [not_forall] at h
      obtain ⟨n, hn⟩ := h
      exact Or.inr (((hs n).resolve_left hn).mono
        (compl_subset_compl.mpr (subset_iUnion s n)))

instance pointMeasurableSpace : MeasurableSpace Point := countableCocountable Point

def μ : Measure Point := Measure.count

def positive : Set Point := {x | (0 : ℝ) < x}

def measurable_sets : Prop := ∀ s : Set Point,
  MeasurableSet s ↔ s.Countable ∨ sᶜ.Countable

def restricted_counting : Prop :=
  (∀ (s : Set Point) (hs : s.Finite), μ s = (hs.toFinset.card : ℝ≥0∞)) ∧
  (∀ (s : Set Point), s.Infinite → μ s = ∞)

def only_empty_null : Prop := ∀ s : Set Point, μ s = 0 ↔ s = ∅

/-- The source's supremum definition of semifiniteness, on the original domain. -/
def semifinite : Prop := ∀ E : Set Point, MeasurableSet E →
  μ E = ⨆ (A : Set Point) (_ : MeasurableSet A) (_ : A ⊆ E) (_ : μ A < ∞), μ A

def not_sigmaFinite : Prop := ¬ SigmaFinite μ

def positive_nonmeasurable : Prop := ¬ MeasurableSet positive

def integrable_series : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (f : Point → 𝕜), Integrable f μ →
    (Function.support f).Countable ∧ Summable (fun x => ‖f x‖) ∧
    (∫ x, f x ∂μ) = ∑' x, f x

/-- The displayed series defines a bounded scalar-linear functional, including
its absolute convergence and its norm estimate. It has no representing density
in ordinary measurable L-infinity. The product in the integral is bilinear,
with no conjugation, and the representation includes absolute integrability. -/
def endpoint_surjectivity_failure : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    ∃ ℓ : Lp 𝕜 1 μ →L[𝕜] 𝕜,
      (∀ f : Lp 𝕜 1 μ, ℓ f = ∑' x : positive, f x) ∧
      (∀ f : Lp 𝕜 1 μ, Summable (fun x : positive => ‖f x‖)) ∧
      (∀ f : Lp 𝕜 1 μ, ‖ℓ f‖ ≤ ‖f‖) ∧
      ¬ ∃ g : Point → 𝕜, Measurable g ∧ MemLp g ∞ μ ∧
        ∀ f : Lp 𝕜 1 μ, Integrable (fun x => f x * g x) μ ∧
          ℓ f = ∫ x, f x * g x ∂μ

end Specs.D11.Ch20.EndpointSurjectivityFailure
