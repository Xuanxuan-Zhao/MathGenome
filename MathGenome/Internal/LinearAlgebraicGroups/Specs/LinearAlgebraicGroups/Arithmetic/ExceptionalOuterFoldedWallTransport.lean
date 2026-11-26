import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedWeyl

noncomputable section

set_option autoImplicit false

namespace LinearAlgebraicGroups.Specs.ExceptionalOuterFoldedWallTransport

open ExceptionalFoldedWeyl

/-- Every projected root is obtained from a projected simple root by a word
in the four simple orbit reflections. -/
def FoldedRootOrbit : Prop :=
  ∀ β ∈ foldedRoots, ∃ (word : List (Fin 4)) (i : Fin 4),
    let w := (word.map orbitReflection).prod
    w ∈ diagramCentralizingWeyl ∧ β = w (foldedSimple i)

/-- The action transports the coroot, reflection, and integral wall equation
in the same Cartan coordinates. -/
def FoldedWallEquivariance : Prop :=
  ∀ w ∈ diagramCentralizingWeyl, ∀ β x : E6Space,
    w (foldedCoroot β) = foldedCoroot (w β) ∧
    w (reflection β x) = reflection (w β) (w x) ∧
    (OnWall (w β) (w x) ↔ OnWall β x)

/-- The Weyl inverse still commutes with the diagram. The two actions restrict
to mutually inverse maps on the fixed space and the projected lattice. -/
def WeylInverseActions : Prop :=
  ∀ w ∈ diagramCentralizingWeyl, ∃ v ∈ diagramCentralizingWeyl,
    w * v = 1 ∧ v * w = 1 ∧
    Set.MapsTo w foldedSpace foldedSpace ∧ Set.MapsTo v foldedSpace foldedSpace ∧
    Set.MapsTo w projectedLattice projectedLattice ∧
    Set.MapsTo v projectedLattice projectedLattice

/-- The intersection of a folded root line with the projected lattice
consists of the integral multiples of that root. -/
def FoldedRootPrimitivity : Prop :=
  ∀ β ∈ foldedRoots, ∀ t : ℝ,
    t • β ∈ projectedLattice ↔ ∃ m : ℤ, t = (m : ℝ)

/-- Reflection fixes a class modulo the projected lattice precisely when
the class is on the corresponding integral wall. -/
def ReflectionShiftCriterion : Prop :=
  ∀ β ∈ foldedRoots, ∀ x : E6Space,
    reflection β x - x ∈ projectedLattice ↔ OnWall β x

end LinearAlgebraicGroups.Specs.ExceptionalOuterFoldedWallTransport
