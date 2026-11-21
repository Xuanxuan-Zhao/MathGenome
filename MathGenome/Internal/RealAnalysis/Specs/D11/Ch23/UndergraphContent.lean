import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.ElementaryMonotoneProperties
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.SetSemiring

/-! Independent specifications for paper.tex:6223–6235. The canonical intervals
are actual subsets of X × ℝ. Section length uses one-dimensional Lebesgue
measure; on every interval it is the finite real function g - min f g.
No measurable structure on X, unit, or whole-space covering is required. -/

noncomputable section
universe u
open Set MeasureTheory Function
open scoped ENNReal BigOperators

namespace D11.Ch23.Specs

def Undergraph {X : Type u} (f g : X → ℝ) : Set (X × ℝ) :=
  {p | f p.1 ≤ p.2 ∧ p.2 < g p.1}

def UndergraphFamily {X : Type u} (V : Submodule ℝ (X → ℝ)) : Set (Set (X × ℝ)) :=
  {s | ∃ f g : V, Undergraph (f : X → ℝ) (g : X → ℝ) = s}

/-- This is also defined off the semiring; only its values on intervals are used. -/
def UndergraphLength {X : Type u} (s : Set (X × ℝ)) : X → ℝ :=
  fun x => (volume ((fun t : ℝ => (x, t)) ⁻¹' s)).toReal

/-- Evaluate L when section length belongs to V, with a zero fallback.
On the semiring lattice closure guarantees the first branch is used. -/
def UndergraphContent {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) (s : Set (X × ℝ)) : ℝ≥0∞ := by
  classical
  exact if h : UndergraphLength s ∈ V then ENNReal.ofReal (L ⟨UndergraphLength s, h⟩) else 0

def UndergraphType := ∀ {X : Type u}, (X → ℝ) → (X → ℝ) → Set (X × ℝ)
def UndergraphFamilyType := ∀ {X : Type u}, Submodule ℝ (X → ℝ) → Set (Set (X × ℝ))
def UndergraphLengthType := ∀ {X : Type u}, Set (X × ℝ) → X → ℝ
def UndergraphContentType := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
  (V →ₗ[ℝ] ℝ) → Set (X × ℝ) → ℝ≥0∞

def UndergraphNormalize : Prop := ∀ {X : Type u} (f g : X → ℝ),
  Undergraph (fun x => min (f x) (g x)) g = Undergraph f g

def UndergraphLengthFormula : Prop := ∀ {X : Type u} (f g : X → ℝ),
  UndergraphLength (Undergraph f g) = fun x => g x - min (f x) (g x)

def UndergraphLengthMem : Prop := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
  IsVectorLattice V → ∀ s ∈ UndergraphFamily V, UndergraphLength s ∈ V

def UndergraphSemiring : Prop := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
  IsVectorLattice V → IsSetSemiring (UndergraphFamily V)

def UndergraphRepresentationIndependent : Prop :=
  ∀ {X : Type u} (f g f' g' : X → ℝ), Undergraph f g = Undergraph f' g' →
    (fun x => g x - min (f x) (g x)) = (fun x => g' x - min (f' x) (g' x))

def UndergraphContentOfLe : Prop := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ))
  (L : V →ₗ[ℝ] ℝ) (f g : V), (∀ x, (f : X → ℝ) x ≤ (g : X → ℝ) x) →
  UndergraphContent V L (Undergraph (f : X → ℝ) (g : X → ℝ)) = ENNReal.ofReal (L (g - f))

def UndergraphContentEmpty : Prop := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ))
  (L : V →ₗ[ℝ] ℝ), UndergraphContent V L ∅ = 0

def UndergraphContentFinite : Prop := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ))
  (L : V →ₗ[ℝ] ℝ) (s : Set (X × ℝ)), UndergraphContent V L s < ⊤

/-- Positivity is asserted for the underlying real L value, before ofReal. -/
def UndergraphIntegralLengthNonneg : Prop := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ))
  (L : V →ₗ[ℝ] ℝ), IsElementaryIntegral V L →
  ∀ (s : Set (X × ℝ)) (h : UndergraphLength s ∈ V), 0 ≤ L ⟨UndergraphLength s, h⟩

def UndergraphContentCountable : Prop := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
  IsVectorLattice V → ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L →
  ∀ (s : Set (X × ℝ)) (a : ℕ → Set (X × ℝ)), s ∈ UndergraphFamily V →
  (∀ n, a n ∈ UndergraphFamily V) → Pairwise (Disjoint on a) →
  (⋃ n, a n) = s → UndergraphContent V L s = ∑' n, UndergraphContent V L (a n)

def UndergraphContentCover : Prop := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
  IsVectorLattice V → ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L →
  ∀ (s : Set (X × ℝ)) (a : ℕ → Set (X × ℝ)), s ∈ UndergraphFamily V →
  (∀ n, a n ∈ UndergraphFamily V) → s ⊆ ⋃ n, a n →
  UndergraphContent V L s ≤ ∑' n, UndergraphContent V L (a n)

/-- Finite additivity, including an empty family and an empty domain. -/
def UndergraphContentFiniteAdditive : Prop :=
  ∀ {X : Type u} {ι : Type u} [Fintype ι] (V : Submodule ℝ (X → ℝ)),
  IsVectorLattice V → ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L →
  ∀ (s : Set (X × ℝ)) (a : ι → Set (X × ℝ)), s ∈ UndergraphFamily V →
  (∀ i, a i ∈ UndergraphFamily V) → Pairwise (Disjoint on a) →
  (⋃ i, a i) = s → UndergraphContent V L s = ∑ i, UndergraphContent V L (a i)

end D11.Ch23.Specs
