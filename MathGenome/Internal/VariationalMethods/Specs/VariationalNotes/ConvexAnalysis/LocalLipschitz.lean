import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Independent statements of `paper.tex`, Theorem `thm:convex-local-lipschitz`
(lines 877–907). Values in `WithTop ℝ` exclude minus infinity. On the
neighborhoods in these statements all values are finite, so `untopD 0`
is the unique real-valued representative, and its default is irrelevant.
The second statement uses neighborhoods and the induced metric in the affine
hull of the effective domain, including when that hull is a singleton.
-/
noncomputable section
open Set Topology
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

def localLipschitz_of_boundedAbove : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → WithTop ℝ), Proper f → IsConvex f → ∀ a : E,
    (∃ M : ℝ, ∀ᶠ x in 𝓝 a, f x ≤ (M : WithTop ℝ)) →
    ∃ U : Set E, U ∈ 𝓝 a ∧ ∃ K : NNReal,
      (∀ x ∈ U, f x < ⊤) ∧
      LipschitzOnWith K (fun x => (f x).untopD 0) U

def localLipschitz_relativeInterior : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → WithTop ℝ), Proper f → IsConvex f →
    ∀ a : E, a ∈ ConvexGeometry.Specs.relativeInterior (effectiveDomain f) →
    ∃ aA : affineSpan ℝ (effectiveDomain f), (aA : E) = a ∧
      ∃ U : Set (affineSpan ℝ (effectiveDomain f)), U ∈ 𝓝 aA ∧ ∃ K : NNReal,
        (∀ x ∈ U, f (x : E) < ⊤) ∧
        LipschitzOnWith K (fun x : affineSpan ℝ (effectiveDomain f) =>
          (f (x : E)).untopD 0) U

end VariationalNotes.ConvexAnalysis.Specs
