import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
Independent specification for paper.tex §2.4 (definition and basic assertions
of Proposition `prop:conjugate-basic`) and the biconjugate definition in §2.5.
The preface's dual is the continuous real dual. `EReal` allows the empty
supremum and the minus-infinite terms in the biconjugate; properness excludes
minus infinity for the conjugate. Convexity uses finite-height epigraphs,
exactly as in §2.1. No convexity or lower semicontinuity is imposed on `f`.
The stronger statements below need only a real topological vector space,
and hence apply in particular to every real Hausdorff locally convex space.
-/
noncomputable section
open Set
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

/-- The supremum is restricted to finite values. On this domain `untopD`
is the unique real value of `f`, so its default is irrelevant. -/
def conjugate {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (y : X →L[ℝ] ℝ) : EReal :=
  ⨆ x ∈ effectiveDomain f, ((y x - (f x).untopD 0 : ℝ) : EReal)

def conjugateType : Type (u+1) :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X],
    (X → WithTop ℝ) → (X →L[ℝ] ℝ) → EReal

def indicator {X : Type u} (C : Set X) (x : X) : WithTop ℝ :=
  by classical exact if x ∈ C then 0 else ⊤

def indicatorType : Type (u+1) := ∀ {X : Type u}, Set X → X → WithTop ℝ

/-- Evaluation is by the original primal space, not the whole bidual. -/
def biconjugate {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (x : X) : EReal :=
  ⨆ y : X →L[ℝ] ℝ, (y x : EReal) - conjugate f y

def biconjugateType : Type (u+1) :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X],
    (X → WithTop ℝ) → X → EReal

def indicator_values : Prop := ∀ {X : Type u} (C : Set X),
  (∀ x ∈ C, indicator C x = 0) ∧ (∀ x ∉ C, indicator C x = ⊤) ∧
  (Proper (indicator C) ↔ C.Nonempty)

def conjugate_finite_lower_bound : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (x : X) (r : ℝ), f x = (r : WithTop ℝ) →
    ∀ y : X →L[ℝ] ℝ, ((y x - r : ℝ) : EReal) ≤ conjugate f y

def conjugate_ne_bot : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ), Proper f → ∀ y : X →L[ℝ] ℝ, conjugate f y ≠ ⊥

/-- Equivalent unrestricted supremum, with infinite primal values contributing
minus infinity. This also certifies compatibility with the shared embedding. -/
def conjugate_eq_iSup_sub : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (y : X →L[ℝ] ℝ),
    conjugate f y = ⨆ x : X, (y x : EReal) - toEReal (f x)

def conjugate_convex : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ),
    Convex ℝ {p : (X →L[ℝ] ℝ) × ℝ | conjugate f p.1 ≤ (p.2 : EReal)}

/-- The domain topology here is exactly σ(X′,X), via native `WeakDual`. -/
def conjugate_weakStar_lowerSemicontinuous : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ),
    LowerSemicontinuous (fun y : WeakDual ℝ X => conjugate f y)

def fenchel_young : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ), Proper f → ∀ (x : X) (y : X →L[ℝ] ℝ),
    (y x : EReal) ≤ toEReal (f x) + conjugate f y

def conjugate_term_conventions : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (x : X) (y : X →L[ℝ] ℝ),
    (∀ r : ℝ, f x = (r : WithTop ℝ) →
      (y x : EReal) - toEReal (f x) = ((y x - r : ℝ) : EReal)) ∧
    (f x = ⊤ → (y x : EReal) - toEReal (f x) = ⊥) ∧
    (conjugate f y = ⊤ → (y x : EReal) - conjugate f y = ⊥)

end VariationalNotes.ConvexAnalysis.Specs
