import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Conjugates
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolarsBipolar
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Independent statements of the set and norm examples in paper.tex,
Proposition `prop:conjugate-basic` (§2.4, lines 958–960).
Support functions use the canonical §1.5 definition. Conjugating support
functions pairs the continuous dual with the original space by evaluation;
there is no replacement of the original space by its bidual.
-/
noncomputable section
open Set
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

def conjugate_indicator : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (C : Set X), C.Nonempty → ∀ y : X →L[ℝ] ℝ,
    conjugate (indicator C) y = ConvexGeometry.Specs.supportFunction C y

def conjugate_supportFunction : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
    [LocallyConvexSpace ℝ X] (C : Set X),
    C.Nonempty → IsClosed C → Convex ℝ C → ∀ x : X,
    (⨆ y : X →L[ℝ] ℝ, (y x : EReal) - ConvexGeometry.Specs.supportFunction C y) =
      toEReal (indicator C x)

def conjugate_norm : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (y : X →L[ℝ] ℝ),
    conjugate (fun x : X => (‖x‖ : WithTop ℝ)) y =
      toEReal (indicator {z : X →L[ℝ] ℝ | ‖z‖ ≤ 1} y)

end VariationalNotes.ConvexAnalysis.Specs
