import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLieWeights
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open LinearAlgebraicGroups.Specs (GroupScheme Lie)

/-- Identity tangent directions fixed by scheme-theoretic conjugation. -/
def invariantLie {k : Type u} [Field k] {G H : GroupScheme k} (i : H ⟶ G) :
    Set (Lie k G) :=
  {v | IsFixedBy ((i.hom.hom ▷ G.X) ≫ GrpObj.conj G.X) v.toMul.val}

end LinearAlgebraicGroups.CocharacterDynamics

namespace LinearAlgebraicGroups.Specs.CocharacterDynamics

open LinearAlgebraicGroups.CocharacterDynamics
open CharacterDescent (Cocharacter)
open DiagonalizableGroups (IntegerCharacters)

def SmoothCocharacterCentralizer : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    (cochar : Cocharacter G.val) (C : ClosedSubgroup G.val),
    RepresentsSubgroup C (fun _ g ↦ Centralizes cochar g) → Smooth C.group.X.hom

def CentralizerLieInvariants : Prop :=
  ∀ {k : Type u} [Field k] {G H : GroupScheme k} (i : H ⟶ G) (C : ClosedSubgroup G),
    RepresentsSubgroup C (fun _ g ↦ Centralizes i g) →
    lieImage C = invariantLie i

def TorusCentralizer : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    [ConnectedSpace G.val.X.left] (S : ClosedSubgroup G.val), IsTorusSubgroup S →
    ∃ C : ClosedSubgroup G.val,
      RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g) ∧
      Smooth C.group.X.hom ∧ GeometricallyConnected C.group.X.hom ∧
      lieImage C = invariantLie S.inclusion

/-- The signed adjoint weight description for one choice of representing subgroups. -/
def HasLieWeights {k : Type u} [Field k] {G : GroupScheme k}
    {cochar : Cocharacter G} (D : LimitDecomposition cochar) (s : IdentityLieStructure G) : Prop :=
  letI := s.lieRing
  letI := s.lieAlgebra
  ∃ W : AdjointWeightBasis cochar s,
    lieImage D.parabolic =
      {v | ∀ j, W.weight j < 0 → W.basis.equivFun v j = 0} ∧
    lieImage D.contracting =
      {v | ∀ j, W.weight j ≤ 0 → W.basis.equivFun v j = 0} ∧
    lieImage D.centralizer =
      {v | ∀ j, W.weight j ≠ 0 → W.basis.equivFun v j = 0}

/-- The cocharacter limit subgroups and their geometry for a smooth connected group. -/
def Dynamics : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    [ConnectedSpace G.val.X.left] (cochar : Cocharacter G.val),
    ∃ (D : LimitDecomposition cochar) (Dneg : LimitDecomposition (oppositeCocharacter cochar)),
      Smooth D.parabolic.group.X.hom ∧ Smooth D.contracting.group.X.hom ∧
      Smooth D.centralizer.group.X.hom ∧
      GeometricallyConnected D.parabolic.group.X.hom ∧
      GeometricallyConnected D.contracting.group.X.hom ∧
      GeometricallyConnected D.centralizer.group.X.hom ∧
      GeometricallyConnected Dneg.contracting.group.X.hom ∧
      Unipotent.IsUnipotent
        (affineAlgebraicSubgroup D.contracting G.property.1 G.property.2.1 G.property.2.2) ∧
      Nonempty (IdentityLieStructure G.val) ∧
      (∀ s : IdentityLieStructure G.val, HasLieWeights D s) ∧
      IsOpenImmersion (bigCellMap D Dneg).left ∧
      GeometricallyConnected
        (Dneg.contracting.group.X ⊗ (D.centralizer.group.X ⊗ D.contracting.group.X)).hom ∧
      ∃ (I : AffineAlgebraicGroup k) (p : Cocharacter I.val) (i : I.val ⟶ G.val),
        IsImageFactorization cochar p i ∧ IsCanonicalImage cochar p i ∧
        RepresentsSubgroup D.centralizer (fun _ g ↦ Centralizes i g)

end LinearAlgebraicGroups.Specs.CocharacterDynamics
