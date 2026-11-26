import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Separable

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup)

/-- A subtorus splits as a finite power of the multiplicative group over a
separable field extension. -/
def IsTorusSubgroup {k : Type u} [Field k] {G : GroupScheme k} (S : ClosedSubgroup G) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Algebra.IsSeparable k K) (r : ℕ),
    Nonempty ((groupBaseChange k K).obj S.group ≅
      (Specs.StandardGroups.multiplicativePowerGroup K (ULift.{u} (Fin r))).val)

end LinearAlgebraicGroups.CocharacterDynamics

namespace LinearAlgebraicGroups.Specs.CocharacterDynamics

open LinearAlgebraicGroups.CocharacterDynamics

/-- The scheme centralizer of a subtorus in a smooth connected affine
algebraic group represents centralization on all families and is smooth and
geometrically connected. -/
def ConnectedTorusCentralizer : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    [ConnectedSpace G.val.X.left] (S : ClosedSubgroup G.val), IsTorusSubgroup S →
    ∃ C : ClosedSubgroup G.val,
      RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g) ∧
      Smooth C.group.X.hom ∧ GeometricallyConnected C.group.X.hom

end LinearAlgebraicGroups.Specs.CocharacterDynamics
