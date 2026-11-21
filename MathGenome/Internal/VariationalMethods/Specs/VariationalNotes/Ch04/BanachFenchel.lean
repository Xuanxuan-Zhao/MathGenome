import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Conjugates
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.WithTop

/-! The continuity qualification theorem, paper.tex §v04-03,
`thm:banach-fenchel`. Continuity is at a finite value in the ambient norm
topology, with the order topology on `WithTop ℝ`. The adjoint applied to `y`
is the continuous functional `y.comp A`. No primal minimizer or lower
semicontinuity assumption occurs. -/
noncomputable section
universe u v
namespace VariationalNotes.Ch04.Specs
open VariationalNotes.ConvexAnalysis.Specs

def banach_fenchel : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (f : X → WithTop ℝ) (g : Y → WithTop ℝ),
    Proper f → IsConvex f → Proper g → IsConvex g →
    (∃ x₀ : X, x₀ ∈ effectiveDomain f ∧
      A x₀ ∈ effectiveDomain g ∧ ContinuousAt g (A x₀)) →
    ∀ p : ℝ, (⨅ x : X, toEReal (f x + g (A x))) = (p : EReal) →
      (∃ y : Y →L[ℝ] ℝ,
        -conjugate f (-(y.comp A)) - conjugate g y = (p : EReal) ∧
        ∀ z : Y →L[ℝ] ℝ,
          -conjugate f (-(z.comp A)) - conjugate g z ≤ (p : EReal)) ∧
      (⨆ y : Y →L[ℝ] ℝ,
        -conjugate f (-(y.comp A)) - conjugate g y) = (p : EReal)

end VariationalNotes.Ch04.Specs
