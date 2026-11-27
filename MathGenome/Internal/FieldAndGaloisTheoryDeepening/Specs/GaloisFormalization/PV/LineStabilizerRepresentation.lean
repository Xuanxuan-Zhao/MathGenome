import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.MatrixGroupCoordinates
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace GaloisFormalization.PV.LineStabilizerRepresentation.Specs

open MatrixGroupCoordinates.Specs
open scoped MatrixGroupCoordinates.Specs

universe u

/-- Every Zariski-closed subgroup of an algebraic matrix group over the
constant field is the stabilizer of a line in a finite-dimensional regular
representation. The line is specified by a nonzero generating vector. -/
def ExistsLineStabilizerRepresentation : Prop :=
  ∀ {C : Type u} [Field C] [IsAlgClosed C] [CharZero C] {n : ℕ}
    (G : Subgroup (GL (Fin n) C)), IsAlgebraicSubgroup G →
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
      ∃ (m : ℕ) (ρ : G →* GL (Fin m) C) (w : Fin m → C),
        IsRegularRepresentation ρ ∧ w ≠ 0 ∧
        ∀ g : G, (Submodule.span C {w}).map (Matrix.toLin' (ρ g).val) =
          Submodule.span C {w} ↔ g ∈ H

end GaloisFormalization.PV.LineStabilizerRepresentation.Specs
