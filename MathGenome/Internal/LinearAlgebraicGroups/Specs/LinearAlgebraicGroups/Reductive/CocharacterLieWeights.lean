import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

open AlgebraicGeometry CategoryTheory
open scoped Matrix

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup Lie IdentityLieStructure)
open Specs.AdjointRepresentation (GroupPoints RelativeTangent TangentCoordinates)
open Specs.CharacterDescent (Cocharacter)

noncomputable section

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- A basis of adjoint character vectors, with the action formula on the
identity tangent over every commutative test algebra. -/
structure AdjointWeightBasis (cochar : Cocharacter G) (s : IdentityLieStructure G) where
  dimension : ℕ
  basis : letI := s.lieRing; letI := s.lieAlgebra
    Module.Basis (ULift.{u} (Fin dimension)) k (Lie k G)
  coordinates : letI := s.lieRing; letI := s.lieAlgebra
    TangentCoordinates G (ULift.{u} (Fin dimension)) basis
  weight : ULift.{u} (Fin dimension) → ℤ
  diagonal : letI := s.lieRing; letI := s.lieAlgebra
    ∀ (R : TestAlgebra k) (t : Rˣ) (v : ULift.{u} (Fin dimension) → R),
    (coordinates.equiv R (fun j ↦ (↑(t ^ weight j) : R) * v j)).toMul.val =
      Specs.AdjointRepresentation.conjugate (cocharacterPoint cochar R t) (coordinates.equiv R v)

/-- The image of the differential of a closed subgroup inclusion at the identity. -/
def lieImage (S : ClosedSubgroup G) : Set (Lie k G) :=
  Set.range (mapPointKernel S.inclusion)

/-- The image of the relative identity tangent of a closed subgroup inclusion. -/
def relativeLieImage (S : ClosedSubgroup G) (R : TestAlgebra k) :
    Set (RelativeTangent G R) :=
  { p | ∃ q : RelativeTangent S.group R,
    ((groupPointsFunctor k).map S.inclusion).app (CommAlgCat.of k (DualNumber R))
      q.toMul.val = p.toMul.val }

end

end LinearAlgebraicGroups.CocharacterDynamics

namespace LinearAlgebraicGroups.Specs.CocharacterDynamics

open LinearAlgebraicGroups.CocharacterDynamics
open AdjointRepresentation (RelativeTangent)
open CharacterDescent (Cocharacter)

def ExistsAdjointWeightBasis : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (cochar : Cocharacter G.val) (s : IdentityLieStructure G.val),
    Nonempty (AdjointWeightBasis cochar s)

/-- The signed weight conditions identify the inclusion images over every test algebra. -/
def RelativeLieWeights : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (cochar : Cocharacter G.val) (D : LimitDecomposition cochar)
    (s : IdentityLieStructure G.val) (W : AdjointWeightBasis cochar s),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (R : TestAlgebra k) (v : ULift.{u} (Fin W.dimension) → R),
      (W.coordinates.equiv R v ∈ relativeLieImage D.parabolic R ↔
        ∀ j, W.weight j < 0 → v j = 0) ∧
      (W.coordinates.equiv R v ∈ relativeLieImage D.contracting R ↔
        ∀ j, W.weight j ≤ 0 → v j = 0) ∧
      (W.coordinates.equiv R v ∈ relativeLieImage D.centralizer R ↔
        ∀ j, W.weight j ≠ 0 → v j = 0)

/-- With the same basis, the opposite contracting subgroup gives the strictly
negative part of the relative tangent. -/
def RelativeOppositeContractingWeights : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (cochar : Cocharacter G.val) (D : LimitDecomposition (oppositeCocharacter cochar))
    (s : IdentityLieStructure G.val) (W : AdjointWeightBasis cochar s),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (R : TestAlgebra k) (v : ULift.{u} (Fin W.dimension) → R),
      W.coordinates.equiv R v ∈ relativeLieImage D.contracting R ↔
        ∀ j, 0 ≤ W.weight j → v j = 0

/-- The three Lie algebras viewed inside the canonical identity Lie algebra of G. -/
def LieWeights : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (cochar : Cocharacter G.val) (D : LimitDecomposition cochar) (s : IdentityLieStructure G.val),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ W : AdjointWeightBasis cochar s,
      lieImage D.parabolic =
        {v | ∀ j, W.weight j < 0 → W.basis.equivFun v j = 0} ∧
      lieImage D.contracting =
        {v | ∀ j, W.weight j ≤ 0 → W.basis.equivFun v j = 0} ∧
      lieImage D.centralizer =
        {v | ∀ j, W.weight j ≠ 0 → W.basis.equivFun v j = 0}

end LinearAlgebraicGroups.Specs.CocharacterDynamics
