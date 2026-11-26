import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.ExactOperations
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.GeometricRadicals

open SchemeDerivedGroup (IsSubgroupOf IsSolvable)
open Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup IsUnipotent)

noncomputable section

variable {k : Type u} [Field k]

/-- The identity closed subgroup of an affine algebraic group. -/
def identitySubgroup (G : AffineAlgebraicGroup k) : ClosedSubgroup G.val := by
  let e : Grp.trivial (SchemeOver k) ⟶ G.val := default
  let eLeft : Spec (CommRingCat.of k) ⟶ G.val.X.left := e.hom.hom.left
  have h : eLeft ≫ G.val.X.hom = 𝟙 (Spec (CommRingCat.of k)) := e.hom.hom.w
  exact ⟨_, e, isClosedImmersion_of_comp_eq_id G.val.X.hom eLeft h⟩

def IsSmoothConnectedNormal {G : AffineAlgebraicGroup k} (N : ClosedSubgroup G.val) : Prop :=
  Smooth N.group.X.hom ∧ ConnectedSpace N.group.X.left ∧ IsNormalSubgroup N.inclusion

/-- The largest smooth connected normal subgroup satisfying the displayed group property. -/
def IsRadical (G : AffineAlgebraicGroup k) (P : AffineAlgebraicGroup k → Prop)
    (N : ClosedSubgroup G.val) : Prop :=
  IsSmoothConnectedNormal N ∧ P (closedSubgroupAlgebraicGroup N) ∧
    ∀ H : ClosedSubgroup G.val, IsSmoothConnectedNormal H →
      P (closedSubgroupAlgebraicGroup H) → IsSubgroupOf H N

def IsUnipotentRadical (G : AffineAlgebraicGroup k) : ClosedSubgroup G.val → Prop :=
  IsRadical G IsUnipotent

def IsSolvableRadical (G : AffineAlgebraicGroup k) : ClosedSubgroup G.val → Prop :=
  IsRadical G (fun H ↦ IsSolvable H.val)

abbrev GeometricGroup (G : AffineAlgebraicGroup k) : AffineAlgebraicGroup (AlgebraicClosure k) :=
  baseChangedAlgebraicGroup (AlgebraicClosure k) G

/-- A choice of the geometrically largest smooth connected normal unipotent subgroup. -/
def geometricUnipotentRadical (G : AffineAlgebraicGroup k) :
    ClosedSubgroup (GeometricGroup G).val :=
  letI : Nonempty (ClosedSubgroup (GeometricGroup G).val) := ⟨identitySubgroup _⟩
  Classical.epsilon (IsUnipotentRadical (GeometricGroup G))

/-- A choice of the geometrically largest smooth connected normal solvable subgroup. -/
def geometricSolvableRadical (G : AffineAlgebraicGroup k) :
    ClosedSubgroup (GeometricGroup G).val :=
  letI : Nonempty (ClosedSubgroup (GeometricGroup G).val) := ⟨identitySubgroup _⟩
  Classical.epsilon (IsSolvableRadical (GeometricGroup G))

/-- For a closed subgroup, triviality is an isomorphism with the trivial group scheme. -/
def IsTrivialSubgroup {G : GroupScheme k} (N : ClosedSubgroup G) : Prop :=
  Nonempty (N.group ≅ Grp.trivial (SchemeOver k))

def IsReductive (G : AffineAlgebraicGroup k) : Prop :=
  Smooth G.val.X.hom ∧ GeometricallyConnected G.val.X.hom ∧
    IsTrivialSubgroup (geometricUnipotentRadical G)

def IsSemisimple (G : AffineAlgebraicGroup k) : Prop :=
  Smooth G.val.X.hom ∧ GeometricallyConnected G.val.X.hom ∧
    IsTrivialSubgroup (geometricSolvableRadical G)

/-- A split torus is isomorphic over its ground field to a finite power of Gₘ. -/
def IsSplitTorus (T : GroupScheme k) : Prop :=
  ∃ r : ℕ, Nonempty (T ≅ (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val)

/-- A torus is a split torus after separable algebraic field extension. -/
def IsTorus (T : GroupScheme k) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra.IsSeparable k E),
    IsSplitTorus ((groupBaseChange k E).obj T)

/-- A maximal torus is maximal for inclusion among the closed tori in the given group. -/
def IsMaximalTorus {G : GroupScheme k} (T : ClosedSubgroup G) : Prop :=
  IsTorus T.group ∧ ∀ S : ClosedSubgroup G, IsTorus S.group →
    IsSubgroupOf T S → IsSubgroupOf S T

/-- The given closed subgroup after field extension. The last argument witnesses
the closed-immersion property of the base-changed inclusion. -/
def baseChangedSubgroup (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (T : ClosedSubgroup G)
    (h : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left) :
    ClosedSubgroup ((groupBaseChange k K).obj G) :=
  ⟨_, (groupBaseChange k K).map T.inclusion, h⟩

def IsSplitReductive (G : AffineAlgebraicGroup k) : Prop :=
  IsReductive G ∧ ∃ T : ClosedSubgroup G.val, IsSplitTorus T.group ∧
    ∃ h : IsClosedImmersion
      ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
      IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)

abbrev GroupPredicateType := ∀ {k : Type u} [Field k], AffineAlgebraicGroup k → Prop
abbrev TorusPredicateType := ∀ {k : Type u} [Field k], GroupScheme k → Prop
abbrev MaximalTorusPredicateType := ∀ {k : Type u} [Field k] {G : GroupScheme k},
  ClosedSubgroup G → Prop
abbrev RadicalPredicateType := ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
  ClosedSubgroup G.val → Prop
abbrev GeometricRadicalType := ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
  ClosedSubgroup (GeometricGroup G).val

def TorusCoordinateComparison : Prop :=
  ∀ {k : Type u} [Field k] (A : HopfAlgebraCategory k),
    IsTorus (specGroup A) ↔ CharacterDescent.IsTorus A

def UnipotentRadicalExists : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    ∃ N : ClosedSubgroup G.val, IsUnipotentRadical G N

def SolvableRadicalExists : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    ∃ N : ClosedSubgroup G.val, IsSolvableRadical G N

def RadicalUnique : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : AffineAlgebraicGroup k → Prop)
    {H N : ClosedSubgroup G.val}, IsRadical G P H → IsRadical G P N →
      ∃! e : H.group ≅ N.group, e.hom ≫ N.inclusion = H.inclusion

def GeometricUnipotentRadicalLargest : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsUnipotentRadical (GeometricGroup G) (geometricUnipotentRadical G)

def GeometricSolvableRadicalLargest : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsSolvableRadical (GeometricGroup G) (geometricSolvableRadical G)

end
end LinearAlgebraicGroups.Specs.GeometricRadicals
