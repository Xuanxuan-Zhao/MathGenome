import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RecessionSets
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Data.EReal.Inv

/-! Independent statements for paper.tex, Proposition `prop:rec-function`
and its unbounded-sublevel consequence (§v01-06, lines 540–573).
The function values exclude minus infinity; infima and quotients use `EReal`.
The analytic conclusions are stated in the stronger general topological setting;
finite dimension is needed only for the unboundedness criterion. -/
noncomputable section
open Set
universe u
namespace VariationalNotes.ConvexGeometry.Specs

def recessionFunction {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (d : E) : EReal :=
  sInf ((fun r : ℝ => (r : EReal)) ''
    {r : ℝ | (d, r) ∈ recession (ConvexAnalysis.Specs.epigraph f)})

def recessionFunctionType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], (E → WithTop ℝ) → E → EReal

def rayQuotient {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (x d : E) (t : ℝ) : EReal :=
  (ConvexAnalysis.Specs.toEReal (f (x + t • d)) -
    ConvexAnalysis.Specs.toEReal (f x)) / (t : EReal)

def rayQuotientType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E],
    (E → WithTop ℝ) → E → E → ℝ → EReal

def recessionFunction_eq_sup : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E],
  ∀ (f : E → WithTop ℝ), ConvexAnalysis.Specs.Proper f →
    ConvexAnalysis.Specs.IsConvex f → ConvexAnalysis.Specs.IsLowerSemicontinuous f →
    ∀ x : E, f x < ⊤ → ∀ d : E,
      recessionFunction f d = ⨆ (t : ℝ) (_ : 0 < t), rayQuotient f x d t

def raySupremum_independent : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E],
  ∀ (f : E → WithTop ℝ), ConvexAnalysis.Specs.Proper f →
    ConvexAnalysis.Specs.IsConvex f → ConvexAnalysis.Specs.IsLowerSemicontinuous f →
    ∀ x y : E, f x < ⊤ → f y < ⊤ → ∀ d : E,
      (⨆ (t : ℝ) (_ : 0 < t), rayQuotient f x d t) =
        ⨆ (t : ℝ) (_ : 0 < t), rayQuotient f y d t

def recessionFunction_ne_bot : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E],
  ∀ (f : E → WithTop ℝ), ConvexAnalysis.Specs.Proper f →
    ConvexAnalysis.Specs.IsConvex f → ConvexAnalysis.Specs.IsLowerSemicontinuous f →
    ∀ d : E, recessionFunction f d ≠ ⊥

def recession_sublevel : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E],
  ∀ (f : E → WithTop ℝ), ConvexAnalysis.Specs.Proper f →
    ConvexAnalysis.Specs.IsConvex f → ConvexAnalysis.Specs.IsLowerSemicontinuous f →
    ∀ a : ℝ, (ConvexAnalysis.Specs.sublevel f a).Nonempty →
      recession (ConvexAnalysis.Specs.sublevel f a) = {d | recessionFunction f d ≤ 0}

def rayQuotient_monotone : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (f : E → WithTop ℝ),
    ConvexAnalysis.Specs.IsConvex f → ∀ x : E, f x < ⊤ → ∀ d : E,
      MonotoneOn (rayQuotient f x d) (Ioi 0)

def recessionFunction_empty_fiber : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (f : E → WithTop ℝ) (d : E),
    (¬ ∃ r : ℝ, (d,r) ∈ recession (ConvexAnalysis.Specs.epigraph f)) →
      recessionFunction f d = ⊤

def unbounded_sublevel_iff : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → WithTop ℝ), ConvexAnalysis.Specs.Proper f →
    ConvexAnalysis.Specs.IsConvex f → ConvexAnalysis.Specs.IsLowerSemicontinuous f →
    ∀ a : ℝ, (ConvexAnalysis.Specs.sublevel f a).Nonempty →
      (¬ Bornology.IsVonNBounded ℝ (ConvexAnalysis.Specs.sublevel f a) ↔
        ∃ d : E, d ≠ 0 ∧ recessionFunction f d ≤ 0)

end VariationalNotes.ConvexGeometry.Specs
