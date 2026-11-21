import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Independent statements for paper.tex §v03-04, Theorem 3.6 and Corollary 3.7.
The infimum and subtraction are taken in `EReal` after the canonical inclusion
of `WithTop ℝ`. A derivative of an extended-valued function at a finite point
is expressed by a real-valued representative agreeing on a neighborhood. -/
noncomputable section
open Filter
open scoped Topology
universe u
namespace VariationalNotes.Existence.Specs
open VariationalNotes.ConvexAnalysis.Specs

def ekeland : Prop :=
  ∀ {M : Type u} [MetricSpace M] [CompleteSpace M] (f : M → WithTop ℝ),
    Proper f → IsLowerSemicontinuous f →
    (∃ b : ℝ, ∀ x, (b : WithTop ℝ) ≤ f x) →
    ∀ (ε lam : ℝ), 0 < ε → 0 < lam → ∀ x₀ : M,
    toEReal (f x₀) ≤ (⨅ x, toEReal (f x)) + (ε : EReal) →
    ∃ xstar : M, f xstar ≤ f x₀ ∧ dist x₀ xstar ≤ lam ∧
      ∀ y : M, y ≠ xstar →
        toEReal (f xstar) - ((ε / lam * dist y xstar : ℝ) : EReal) < toEReal (f y)

/-- This conclusion applies to every point satisfying the theorem's variational
inequality, hence in particular to its produced point. No global smoothness is
assumed. -/
def approximate_stationarity : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (f : X → WithTop ℝ) (ε lam : ℝ), 0 < ε → 0 < lam →
    ∀ xstar : X,
    (∀ y : X, y ≠ xstar →
      toEReal (f xstar) - ((ε / lam * dist y xstar : ℝ) : EReal) < toEReal (f y)) →
    ∀ (g : X → ℝ) (A : X →L[ℝ] ℝ),
      (∀ᶠ y in 𝓝 xstar, f y = (g y : WithTop ℝ)) →
      HasFDerivAt g A xstar → ‖A‖ ≤ ε / lam

end VariationalNotes.Existence.Specs
