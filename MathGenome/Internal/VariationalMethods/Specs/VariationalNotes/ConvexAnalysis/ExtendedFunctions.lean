import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Semicontinuity.Basic

/-!
Independent statements for paper.tex §v02-01, Definition and Proposition
`prop:epigraph-criteria` (lines 783–824). Values are `WithTop ℝ`, so minus
infinity is excluded by the type. Epigraph heights and sublevel parameters
are real. No separation or vector topology hypothesis is needed below.
-/
noncomputable section
open Set
universe u v
namespace VariationalNotes.ConvexAnalysis.Specs

def ProperType : Type (u+1) := ∀ {X : Type u}, (X → WithTop ℝ) → Prop
def Proper {X : Type u} (f : X → WithTop ℝ) : Prop := ∃ x, f x < ⊤

def effectiveDomainType : Type (u+1) := ∀ {X : Type u}, (X → WithTop ℝ) → Set X
def effectiveDomain {X : Type u} (f : X → WithTop ℝ) : Set X := {x | f x < ⊤}

def epigraphType : Type (u+1) := ∀ {X : Type u}, (X → WithTop ℝ) → Set (X × ℝ)
def epigraph {X : Type u} (f : X → WithTop ℝ) : Set (X × ℝ) :=
  {p | f p.1 ≤ (p.2 : WithTop ℝ)}

def sublevelType : Type (u+1) := ∀ {X : Type u}, (X → WithTop ℝ) → ℝ → Set X
def sublevel {X : Type u} (f : X → WithTop ℝ) (a : ℝ) : Set X :=
  {x | f x ≤ (a : WithTop ℝ)}

def IsConvexType : Type (u+1) :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X], (X → WithTop ℝ) → Prop
def IsConvex {X : Type u} [AddCommGroup X] [Module ℝ X] (f : X → WithTop ℝ) : Prop :=
  Convex ℝ (epigraph f)

def IsLowerSemicontinuousType : Type (u+1) :=
  ∀ {X : Type u} [TopologicalSpace X], (X → WithTop ℝ) → Prop
def IsLowerSemicontinuous {X : Type u} [TopologicalSpace X] (f : X → WithTop ℝ) : Prop :=
  ∀ a : ℝ, IsOpen {x | (a : WithTop ℝ) < f x}

/-- Native multiplication gives the convention `0 * (+∞) = 0`.
Only nonnegative weights occur in the convex inequalities. -/
def weightedValueType := ℝ → WithTop ℝ → WithTop ℝ
def weightedValue (a : ℝ) (r : WithTop ℝ) : WithTop ℝ := (a : WithTop ℝ) * r

def toERealType := WithTop ℝ → EReal
def toEReal (r : WithTop ℝ) : EReal := (r : WithBot (WithTop ℝ))

def proper_iff_exists_real : Prop := ∀ {X : Type u} (f : X → WithTop ℝ),
  Proper f ↔ ∃ x, ∃ r : ℝ, f x = (r : WithTop ℝ)

def mem_domain_iff : Prop := ∀ {X : Type u} (f : X → WithTop ℝ) (x : X),
  x ∈ effectiveDomain f ↔ ∃ r : ℝ, f x = r

def convex_iff_twoPoint : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] (f : X → WithTop ℝ),
  IsConvex f ↔ ∀ (x y : X) (r s : ℝ), f x = r → f y = s →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ ((a * r + b * s : ℝ) : WithTop ℝ)

def finite_jensen : Prop :=
  ∀ {X : Type u} {ι : Type v} [AddCommGroup X] [Module ℝ X]
  (f : X → WithTop ℝ), IsConvex f → ∀ (I : Finset ι) (w : ι → ℝ)
  (p : ι → X) (r : ι → ℝ), (∀ i ∈ I, 0 ≤ w i) → (∑ i ∈ I, w i) = 1 →
  (∀ i ∈ I, f (p i) ≤ (r i : WithTop ℝ)) →
  f (∑ i ∈ I, w i • p i) ≤ ((∑ i ∈ I, w i * r i : ℝ) : WithTop ℝ)

def jensen : Prop :=
  ∀ {X : Type u} {ι : Type v} [AddCommGroup X] [Module ℝ X]
  (f : X → WithTop ℝ), IsConvex f → ∀ (I : Finset ι) (w : ι → ℝ)
  (p : ι → X), (∀ i ∈ I, 0 ≤ w i) → (∑ i ∈ I, w i) = 1 →
  f (∑ i ∈ I, w i • p i) ≤ ∑ i ∈ I, weightedValue (w i) (f (p i))

def weight_conventions : Prop :=
  (∀ r : WithTop ℝ, weightedValue 0 r = 0) ∧
  (∀ a : ℝ, 0 < a → weightedValue a ⊤ = ⊤) ∧
  (∀ a r : ℝ, weightedValue a (r : WithTop ℝ) = ((a*r : ℝ) : WithTop ℝ))

def lowerSemicontinuous_iff_native : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (f : X → WithTop ℝ),
  IsLowerSemicontinuous f ↔ LowerSemicontinuous f

def lowerSemicontinuous_iff_closed_sublevels : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (f : X → WithTop ℝ),
  IsLowerSemicontinuous f ↔ ∀ a : ℝ, IsClosed (sublevel f a)

def lowerSemicontinuous_iff_closed_epigraph : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (f : X → WithTop ℝ),
  IsLowerSemicontinuous f ↔ IsClosed (epigraph f)

/-- This specifies the full value and order convention bridge to native `EReal`.
The image is exactly the extended real numbers other than minus infinity. -/
def toEReal_conventions : Prop :=
  (∀ r : ℝ, toEReal (r : WithTop ℝ) = (r : EReal)) ∧
  toEReal ⊤ = ⊤ ∧
  (∀ r : WithTop ℝ, toEReal r ≠ ⊥) ∧
  (∀ v : EReal, v ≠ ⊥ ↔ ∃ r : WithTop ℝ, toEReal r = v) ∧
  (∀ r s : WithTop ℝ, toEReal r ≤ toEReal s ↔ r ≤ s)

/-- Addition and nonnegative weighting agree with native `EReal` arithmetic.
No compatibility with negative multiples of infinity is asserted. -/
def toEReal_add : Prop := ∀ r s : WithTop ℝ,
  toEReal (r + s) = toEReal r + toEReal s

def toEReal_weightedValue : Prop := ∀ (a : ℝ) (r : WithTop ℝ), 0 ≤ a →
  toEReal (weightedValue a r) = (a : EReal) * toEReal r

end VariationalNotes.ConvexAnalysis.Specs
