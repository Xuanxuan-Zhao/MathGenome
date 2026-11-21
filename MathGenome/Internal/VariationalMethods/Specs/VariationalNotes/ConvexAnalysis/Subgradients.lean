import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.FenchelMoreau
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolarsBipolar

/-! Independent specification of paper.tex §v02-06, Definition and
Theorem `thm:fenchel-equality` (1062–1103). Finite values are exhibited by
real witnesses, so subdifferentials at infinite values are empty by definition.
The dual subdifferential uses evaluation by X, not the whole continuous bidual.
-/
noncomputable section
open Set
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

def subdifferential {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (x : X) : Set (X →L[ℝ] ℝ) :=
  {y | ∃ r : ℝ, f x = (r : WithTop ℝ) ∧
    ∀ z : X, ((r + y (z - x) : ℝ) : WithTop ℝ) ≤ f z}

def subdifferentialType : Type (u+1) :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X],
    (X → WithTop ℝ) → X → Set (X →L[ℝ] ℝ)

def pairingSubdifferential {X : Type u} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] (g : (X →L[ℝ] ℝ) → EReal) (y : X →L[ℝ] ℝ) : Set X :=
  {x | ∃ s : ℝ, g y = (s : EReal) ∧
    ∀ v : X →L[ℝ] ℝ, ((s + (v - y) x : ℝ) : EReal) ≤ g v}

def pairingSubdifferentialType : Type (u+1) :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X],
    ((X →L[ℝ] ℝ) → EReal) → (X →L[ℝ] ℝ) → Set X

def subdifferential_eq_empty_of_top : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (x : X), f x = ⊤ → subdifferential f x = ∅

def pairingSubdifferential_eq_empty_of_infinite : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (g : (X →L[ℝ] ℝ) → EReal) (y : X →L[ℝ] ℝ),
    (g y = ⊤ ∨ g y = ⊥) → pairingSubdifferential g y = ∅

def minimizes_iff_zero_mem_subdifferential : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ), Proper f → IsConvex f →
    ∀ x ∈ effectiveDomain f,
      (∀ z, f x ≤ f z) ↔ (0 : X →L[ℝ] ℝ) ∈ subdifferential f x

def subdifferential_indicator : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (C : Set X), C.Nonempty → Convex ℝ C → ∀ x ∈ C,
    subdifferential (indicator C) x = VariationalNotes.ConvexGeometry.Specs.normalCone C x

/-- No regularity of f is needed for the first Fenchel equality characterization.
Membership of x in the effective domain already implies properness. -/
def subgradient_iff_fenchel_equality : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (x : X), x ∈ effectiveDomain f →
    ∀ y : X →L[ℝ] ℝ, y ∈ subdifferential f x ↔
      toEReal (f x) + conjugate f y = (y x : EReal)

def subgradient_iff_pairing_subgradient : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
    [LocallyConvexSpace ℝ X]
    (f : X → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ x ∈ effectiveDomain f, ∀ y : X →L[ℝ] ℝ,
      y ∈ subdifferential f x ↔ x ∈ pairingSubdifferential (conjugate f) y

end VariationalNotes.ConvexAnalysis.Specs
