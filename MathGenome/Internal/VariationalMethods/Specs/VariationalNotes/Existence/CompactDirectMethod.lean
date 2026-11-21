import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Independent statements for paper.tex §v03-02, the coercivity definition and
Theorem `thm:direct-method`, parts 1–2 (lines 1399–1433).
The codomain `WithTop ℝ` excludes minus infinity. Properness and lower
semicontinuity are required only on the indicated set, using its subspace
topology and the previously specified extended-function conventions.
-/
noncomputable section
open Set
universe u
namespace VariationalNotes.Existence.Specs

def ProperOnType : Type (u + 1) := ∀ {X : Type u}, (X → WithTop ℝ) → Set X → Prop
def ProperOn {X : Type u} (J : X → WithTop ℝ) (C : Set X) : Prop :=
  ConvexAnalysis.Specs.Proper (fun x : C => J x)

def IsLowerSemicontinuousOnType : Type (u + 1) :=
  ∀ {X : Type u} [TopologicalSpace X], (X → WithTop ℝ) → Set X → Prop
def IsLowerSemicontinuousOn {X : Type u} [TopologicalSpace X]
    (J : X → WithTop ℝ) (C : Set X) : Prop :=
  ConvexAnalysis.Specs.IsLowerSemicontinuous (fun x : C => J x)

def CoerciveOnType : Type (u + 1) :=
  ∀ {X : Type u} [NormedAddCommGroup X], (X → WithTop ℝ) → Set X → Prop
/-- Every real sublevel in `C` is bounded in the ambient normed space. -/
def CoerciveOn {X : Type u} [NormedAddCommGroup X]
    (J : X → WithTop ℝ) (C : Set X) : Prop :=
  ∀ a : ℝ, Bornology.IsBounded {x ∈ C | J x ≤ (a : WithTop ℝ)}

def AttainsFiniteMinimumType : Type (u + 1) :=
  ∀ {X : Type u}, (X → WithTop ℝ) → Set X → Prop
/-- A feasible point of real value equal to the greatest lower bound of all
feasible values. This states attainment and finiteness of the infimum. -/
def AttainsFiniteMinimum {X : Type u} (J : X → WithTop ℝ) (C : Set X) : Prop :=
  ∃ x ∈ C, ∃ m : ℝ, J x = (m : WithTop ℝ) ∧ IsGLB (J '' C) (m : WithTop ℝ)

def compact_direct_method : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (J : X → WithTop ℝ) (C : Set X),
    ProperOn J C → IsCompact C → IsLowerSemicontinuousOn J C →
      AttainsFiniteMinimum J C

/-- The only semicontinuity and compactness assumptions are on the one
sublevel at a finite feasible comparison point. -/
def compact_sublevel_direct_method : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (J : X → WithTop ℝ) (C : Set X)
    (x₀ : X), x₀ ∈ C → J x₀ < ⊤ →
    IsCompact {x ∈ C | J x ≤ J x₀} →
    IsLowerSemicontinuousOn J {x ∈ C | J x ≤ J x₀} →
      AttainsFiniteMinimum J C

def finiteDimensional_direct_method : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (J : X → WithTop ℝ) (C : Set X),
    ProperOn J C → IsClosed C → IsLowerSemicontinuousOn J C → CoerciveOn J C →
      AttainsFiniteMinimum J C

end VariationalNotes.Existence.Specs
