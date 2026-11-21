import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.ContinuousProcessLaw
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.Tightness
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Independent statements of `thm:p06-path-weak`, paper.tex 2308–2340.
The canonical compact-open metric on these compact-domain continuous maps is
exactly the uniform metric. The state space has the Euclidean norm, including
the one-point case d = 0. No path law with the limiting marginals is assumed. -/

open MeasureTheory Filter Topology Set

namespace ProbabilityFoundations.Ch06.PathWeakSpec

noncomputable section

abbrev Path (T : ℝ) (d : ℕ) := C(Ch05.Time T, EuclideanSpace ℝ (Fin d))

/-- Evaluation at a finite set of the chosen dense times. -/
def finiteEval {T : ℝ} {d : ℕ} {D : Set (Ch05.Time T)} (I : Finset D)
    (f : Path T d) : I → EuclideanSpace ℝ (Fin d) := fun i => f i.1.1

/-- The limiting marginal laws may be specified independently. Tightness must
produce a path law realizing all of them, convergence of the whole sequence,
and uniqueness among all path laws realizing the marginals. -/
def existenceType : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (d : ℕ) (D : Set (Ch05.Time T)),
    D.Countable → Dense D → ∀ (μ : ℕ → ProbabilityMeasure (Path T d)),
    _root_.Specs.ProbabilityFoundations.Ch06.Tightness.uniformlyTightValue (range μ) →
    ∀ (ν : (I : Finset D) → ProbabilityMeasure (I → EuclideanSpace ℝ (Fin d))),
    (∀ I, Tendsto (fun n => (μ n).map (finiteEval I)) atTop (𝓝 (ν I))) →
    ∃ η : ProbabilityMeasure (Path T d),
      (∀ I, η.map (finiteEval I) = ν I) ∧
      Tendsto μ atTop (𝓝 η) ∧
      ∀ ρ : ProbabilityMeasure (Path T d),
        (∀ I, ρ.map (finiteEval I) = ν I) → ρ = η

/-- The criterion for a specified limit law, with the same countable dense
set used for all finite-dimensional marginals. -/
def convergenceIffType : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (d : ℕ) (D : Set (Ch05.Time T)),
    D.Countable → Dense D →
    ∀ (μ : ℕ → ProbabilityMeasure (Path T d)) (η : ProbabilityMeasure (Path T d)),
    Tendsto μ atTop (𝓝 η) ↔
      _root_.Specs.ProbabilityFoundations.Ch06.Tightness.uniformlyTightValue (range μ) ∧
      ∀ I : Finset D,
        Tendsto (fun n => (μ n).map (finiteEval I)) atTop (𝓝 (η.map (finiteEval I)))

end
end ProbabilityFoundations.Ch06.PathWeakSpec
