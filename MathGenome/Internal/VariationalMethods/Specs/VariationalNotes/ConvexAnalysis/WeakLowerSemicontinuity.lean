import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
The first two assertions of paper.tex, Theorem `thm:convex-weak-closed`
(§v02-03). `WeakSpace ℝ X` carries σ(X,X′), where X′ consists of the
continuous linear functionals for the original norm topology on X.
The canonical linear equivalence transports sets and functions without
changing their points or values. Lower semicontinuity is asserted for
the full weak topology using open strict real superlevels.
No completeness, reflexivity, or properness assumption is imposed.
-/
noncomputable section
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

/-- Every norm-closed convex set is closed in the weak topology. -/
def normClosed_convex_isWeaklyClosed : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X), IsClosed C → Convex ℝ C →
    IsClosed ((toWeakSpace ℝ X) '' C)

/-- A norm-lower-semicontinuous convex extended-real function is weakly
lower semicontinuous, with no restriction to convergent sequences. -/
def convex_normLowerSemicontinuous_isWeaklyLowerSemicontinuous : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → WithTop ℝ), IsConvex f → IsLowerSemicontinuous f →
    IsLowerSemicontinuous
      (fun x : WeakSpace ℝ X => f ((toWeakSpace ℝ X).symm x))

end VariationalNotes.ConvexAnalysis.Specs
