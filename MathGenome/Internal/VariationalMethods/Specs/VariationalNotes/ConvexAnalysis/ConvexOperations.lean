import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
Independent obligations for paper.tex, Proposition `prop:convex-operations`,
lines 826–871, with the global convention at lines 71–80.

The original functions take values in real numbers with positive infinity.
`IsLUB` and `IsGLB` specify actual pointwise bounds, avoiding a conditional
infimum's arbitrary default when the range is unbounded below. In particular,
a WithTop-valued inf-projection exists only when the extended infimum is never
minus infinity. Properness additionally requires a finite value somewhere.
No properness of the resulting sum, supremum or pullback is asserted.
-/
noncomputable section
open Set
universe u v w
namespace VariationalNotes.ConvexAnalysis.Specs.Operations

def perspective {X : Type u} [AddCommGroup X] [Module ℝ X]
    (f : X → WithTop ℝ) (p : X × ℝ) : WithTop ℝ :=
  if 0 < p.2 then weightedValue p.2 (f (p.2⁻¹ • p.1)) else ⊤

def perspectiveType : Type (u+1) :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X],
    (X → WithTop ℝ) → (X × ℝ) → WithTop ℝ

def indicator {X : Type u} (C : Set X) (x : X) : WithTop ℝ := by
  classical
  exact if x ∈ C then 0 else ⊤
def indicatorType : Type (u+1) := ∀ {X : Type u}, Set X → X → WithTop ℝ

def IsInfProjection {X : Type u} {Y : Type v}
    (F : X × Y → WithTop ℝ) (v : X → WithTop ℝ) : Prop :=
  ∀ x, IsGLB (range fun y => F (x,y)) (v x)
def IsInfProjectionType : Type (max (u+1) (v+1)) :=
  ∀ {X : Type u} {Y : Type v}, (X × Y → WithTop ℝ) → (X → WithTop ℝ) → Prop

def hyperbolaSet : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1⁻¹ ≤ p.2}
def hyperbolaSetType := Set (ℝ × ℝ)

def convex_positive_sum : Prop :=
  ∀ {X : Type u} {ι : Type v} [AddCommGroup X] [Module ℝ X]
    (I : Finset ι) (w : ι → ℝ) (f : ι → X → WithTop ℝ),
    (∀ i ∈ I, 0 < w i) → (∀ i ∈ I, IsConvex (f i)) →
    IsConvex (fun x => ∑ i ∈ I, weightedValue (w i) (f i x))

def convex_supremum : Prop :=
  ∀ {X : Type u} {ι : Type v} [AddCommGroup X] [Module ℝ X]
    (f : ι → X → WithTop ℝ) (g : X → WithTop ℝ),
    (∀ i, IsConvex (f i)) → (∀ x, IsLUB (range fun i => f i x) (g x)) →
    IsConvex g

/-- The epigraph formulation also covers the empty supremum, whose value is
minus infinity in `EReal`. The theorem above and `supremum_iff_ereal` give the
original WithTop-valued convexity whenever the supremum has no such value. -/
def convex_ereal_supremum : Prop :=
  ∀ {X : Type u} {ι : Type v} [AddCommGroup X] [Module ℝ X]
    (f : ι → X → WithTop ℝ), (∀ i, IsConvex (f i)) →
    Convex ℝ {p : X × ℝ | (⨆ i, toEReal (f i p.1)) ≤ (p.2 : EReal)}

def convex_affine_pullback : Prop :=
  ∀ {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (f : Y → WithTop ℝ) (A : X →ᵃ[ℝ] Y),
    IsConvex f → IsConvex (f ∘ A)

def convex_perspective : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] (f : X → WithTop ℝ),
    IsConvex f → IsConvex (perspective f)

def convex_infProjection : Prop :=
  ∀ {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (F : X × Y → WithTop ℝ) (v : X → WithTop ℝ),
    IsConvex F → IsInfProjection F v → Proper v → IsConvex v

/-- This bridge makes precise that the order-theoretic projection is the
actual extended-real infimum, including the exclusion of minus infinity. -/
def infProjection_iff_ereal : Prop :=
  ∀ {X : Type u} {Y : Type v} (F : X × Y → WithTop ℝ) (v : X → WithTop ℝ),
    IsInfProjection F v ↔ ∀ x, toEReal (v x) = ⨅ y, toEReal (F (x,y))

/-- Every WithTop-valued pointwise supremum is covered; an empty family has
no supremum in this codomain (its extended-real supremum is minus infinity). -/
def supremum_iff_ereal : Prop :=
  ∀ {X : Type u} {ι : Type v} (f : ι → X → WithTop ℝ) (g : X → WithTop ℝ),
    (∀ x, IsLUB (range fun i => f i x) (g x)) ↔
      ∀ x, toEReal (g x) = ⨆ i, toEReal (f i x)

def lsc_positive_sum : Prop :=
  ∀ {X : Type u} {ι : Type v} [TopologicalSpace X]
    (I : Finset ι) (w : ι → ℝ) (f : ι → X → WithTop ℝ),
    (∀ i ∈ I, 0 < w i) → (∀ i ∈ I, IsLowerSemicontinuous (f i)) →
    IsLowerSemicontinuous (fun x => ∑ i ∈ I, weightedValue (w i) (f i x))

def lsc_supremum : Prop :=
  ∀ {X : Type u} {ι : Type v} [TopologicalSpace X]
    (f : ι → X → WithTop ℝ) (g : X → WithTop ℝ),
    (∀ i, IsLowerSemicontinuous (f i)) →
    (∀ x, IsLUB (range fun i => f i x) (g x)) → IsLowerSemicontinuous g

/-- The strict upper-level formulation for arbitrary, including empty, suprema. -/
def lsc_ereal_supremum : Prop :=
  ∀ {X : Type u} {ι : Type v} [TopologicalSpace X]
    (f : ι → X → WithTop ℝ), (∀ i, IsLowerSemicontinuous (f i)) →
    ∀ a : ℝ, IsOpen {x | (a : EReal) < ⨆ i, toEReal (f i x)}

def lsc_continuous_affine_pullback : Prop :=
  ∀ {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (f : Y → WithTop ℝ) (A : X →ᵃ[ℝ] Y), Continuous A →
    IsLowerSemicontinuous f → IsLowerSemicontinuous (f ∘ A)

def perspective_zero_counterexample : Prop :=
  let f : ℝ → WithTop ℝ := fun _ => 0
  Proper f ∧ IsConvex f ∧ IsLowerSemicontinuous f ∧
    (∀ x t : ℝ, perspective f (x,t) = if 0 < t then 0 else ⊤) ∧
    IsConvex (perspective f) ∧ ¬ IsLowerSemicontinuous (perspective f) ∧
    ∀ x : ℝ, ¬ LowerSemicontinuousAt (perspective f) (x,0)

def infProjection_counterexample : Prop :=
  let F := indicator hyperbolaSet
  let v := indicator (Ioi (0 : ℝ))
  IsClosed hyperbolaSet ∧ Convex ℝ hyperbolaSet ∧ Proper F ∧
    IsConvex F ∧ IsLowerSemicontinuous F ∧ IsInfProjection F v ∧
    Proper v ∧ IsConvex v ∧ ¬ IsLowerSemicontinuous v ∧
    ¬ LowerSemicontinuousAt v 0

end VariationalNotes.ConvexAnalysis.Specs.Operations
