import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework

/-!
Independent statements of Cramér–Wold, paper.tex:2591–2602.
All spaces have their canonical Borel sigma algebras. Real linear projections
are x ↦ ⟪t,x⟫, for every t, including zero. Dimension zero is also included.
Weak convergence uses the shared topology of bounded continuous real tests.
-/

open MeasureTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch07.CramerWold

open _root_.ProbabilityFoundations.Ch07

/-- All one-dimensional linear image laws determine a Borel probability law. -/
def measureEquality : Prop :=
  ∀ {d : ℕ} (μ ν : Measure (Euclidean d)),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    (∀ t : Euclidean d,
      Measure.map (fun x => inner ℝ t x) μ =
        Measure.map (fun x => inner ℝ t x) ν) →
    μ = ν

/-- Weak convergence to the stipulated law is equivalent to weak convergence
of every real linear image to the corresponding image of that law. -/
def weakConvergence : Prop :=
  ∀ {d : ℕ} (μs : ℕ → ProbabilityMeasure (Euclidean d))
    (μ : ProbabilityMeasure (Euclidean d)),
    Specs.ProbabilityFoundations.Ch06.WeakFramework.weaklyConvergesValue atTop μs μ ↔
      ∀ t : Euclidean d,
        Specs.ProbabilityFoundations.Ch06.WeakFramework.weaklyConvergesValue atTop
          (fun n => (μs n).map (fun x => inner ℝ t x))
          (μ.map (fun x => inner ℝ t x))

end Specs.ProbabilityFoundations.Ch07.CramerWold
