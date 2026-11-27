import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.LineStabilizerRepresentation

namespace GaloisFormalization.PV.ClosedSubgroupRepresentations.Specs

open MatrixGroupCoordinates.Specs
open scoped MatrixGroupCoordinates.Specs

universe u

/-- A closed subgroup is the stabilizer of a line in a finite-dimensional regular
representation. The shared statement specifies the line by a nonzero vector. -/
abbrev ExistsLineStabilizerRepresentation : Prop :=
  LineStabilizerRepresentation.Specs.ExistsLineStabilizerRepresentation.{u}

/-- A closed normal subgroup of an algebraic matrix group is the kernel of a
finite-dimensional regular representation over the constant field. -/
def ExistsKernelRepresentation : Prop :=
  ∀ {C : Type u} [Field C] [IsAlgClosed C] [CharZero C] {n : ℕ}
    (G : Subgroup (GL (Fin n) C)), IsAlgebraicSubgroup G →
    ∀ (H : Subgroup G), IsClosed (H : Set G) → H.Normal →
      ∃ (m : ℕ) (ρ : G →* GL (Fin m) C), IsRegularRepresentation ρ ∧ ρ.ker = H

end GaloisFormalization.PV.ClosedSubgroupRepresentations.Specs
