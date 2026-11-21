import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.CoordinateDependency
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.SymmetricLocalLemma

open MeasureTheory
open scoped BigOperators Classical

namespace P205.Probability.PropertyB

/-- The two colors each have weight one half. -/
noncomputable def fairBit : FiniteModel Bool where
  weight _ := 1 / 2
  weight_nonneg _ := by norm_num
  weight_sum := by norm_num

/-- Independent fair colors at all vertices. -/
noncomputable def coloringModel (V : Type*) [Fintype V] : FiniteModel (V → Bool) :=
  FiniteModel.pi (fun _ : V => fairBit)

/-- All vertices of an edge have the specified color. -/
def colorPattern {V : Type*} (F : Finset V) (b : Bool) : Set (V → Bool) :=
  {c | ∀ v ∈ F, c v = b}

/-- The bad event for an edge is that it is monochromatic. -/
def monochromatic {V : Type*} (F : Finset V) : Set (V → Bool) :=
  colorPattern F false ∪ colorPattern F true

/-- A coloring witnesses Property B when each edge contains both colors. -/
def Bichromatic {V : Type*} (H : Finset (Finset V)) (c : V → Bool) : Prop :=
  ∀ F ∈ H, (∃ v ∈ F, c v = false) ∧ (∃ v ∈ F, c v = true)

end P205.Probability.PropertyB

namespace Specs.P205.Probability.PropertyB

open _root_.P205.Probability
open _root_.P205.Probability.PropertyB

/-- The exact monochromatic-edge probability, with a signed exponent. -/
def monochromaticProbability : Prop :=
  ∀ {V : Type*} [Fintype V] (F : Finset V), F.Nonempty →
    (coloringModel V).eventMass (monochromatic F) = (2 : ℝ) ^ (1 - (F.card : ℤ))

/-- The canonical overlap graph is a dependency graph for the bad events;
its independence condition uses the full generated sigma-algebra. -/
def monochromaticDependency : Prop :=
  ∀ {V : Type*} [Fintype V] (H : Finset (Finset V)),
    letI : MeasurableSpace Bool := ⊤
    @IsDependencyGraphValue H _ (V → Bool) _ (coloringModel V).measure
      (inferInstanceAs (IsProbabilityMeasure (coloringModel V).pmf.toMeasure))
      (fun F : H => monochromatic F.val)
      (CoordinateDependency.overlapGraph (fun F : H => (F.val : Set V)))

/-- Theorem 6.4 (p205:W30). Edges are a finite family of finite vertex sets.
The degree counts distinct other edges with nonempty intersection. Empty edge
families and k=1 are retained, and subtraction in the exponent is in ℤ. -/
def propertyB : Prop :=
  ∀ {V : Type*} [Fintype V] (H : Finset (Finset V)) (k d : ℕ),
    1 ≤ k →
    (∀ F ∈ H, k ≤ F.card) →
    (∀ F ∈ H, (H.filter (fun G => G ≠ F ∧ (F ∩ G).Nonempty)).card ≤ d) →
    Real.exp 1 * (2 : ℝ) ^ (1 - (k : ℤ)) * ((d : ℝ) + 1) ≤ 1 →
    ∃ c : V → Bool, Bichromatic H c

end Specs.P205.Probability.PropertyB
