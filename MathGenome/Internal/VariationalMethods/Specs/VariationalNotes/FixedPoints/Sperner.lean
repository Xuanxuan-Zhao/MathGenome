import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.SimplexGeometry
import Mathlib.Algebra.Ring.Parity

/-! Statements for paper.tex, Lemma `lem:sperner-parity` (4596–4624).
The dimensions range over all natural numbers, including zero. The labeling
hypothesis is exactly positivity of the coordinate indexed by the label. -/
namespace Specs.VariationalNotes.FixedPoints.Sperner

open Specs.VariationalNotes.FixedPoints.SimplexGeometry

/-- The number of fully labeled top-dimensional cells is odd. -/
def sperner_odd : Prop :=
  ∀ {d : ℕ} (T : Triangulation d) (ℓ : VertexLabeling T),
    SpernerLabeling T ℓ → Odd (fullyLabeledCells T ℓ).card

/-- In particular, there is a top-dimensional cell carrying every label. -/
def sperner_exists : Prop :=
  ∀ {d : ℕ} (T : Triangulation d) (ℓ : VertexLabeling T),
    SpernerLabeling T ℓ → ∃ s ∈ topCells T, FullyLabeled T ℓ s

end Specs.VariationalNotes.FixedPoints.Sperner
