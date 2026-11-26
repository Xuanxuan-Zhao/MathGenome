import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RationalCocharacter

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.Relative.MaximalSplitTori

open BorelProper (IsParabolic)
open CharacterDescent (Cocharacter)
open GeometricBorelConjugacy (ConjugatesSubgroups subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open RankOneFlag (SameSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open StandardParabolicLevi (IsContractingRadical)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)

variable {k : Type u} [Field k]

/-- Minimality is among parabolics defined over the ground field. -/
def IsMinimalParabolic (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val) : Prop :=
  IsParabolic G P ∧
    ∀ Q : ClosedSubgroup G.val, IsParabolic G Q → IsSubgroupOf Q P → IsSubgroupOf P Q

/-- Maximality is among split tori in the indicated ambient group over the ground field. -/
def IsMaximalSplitTorus {G : GroupScheme k} (S : ClosedSubgroup G) : Prop :=
  IsSplitTorus S.group ∧
    ∀ T : ClosedSubgroup G, IsSplitTorus T.group → IsSubgroupOf S T → IsSubgroupOf T S

def MinimalParabolicsConjugate : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P Q : ClosedSubgroup G.val),
    IsMinimalParabolic G P → IsMinimalParabolic G Q →
    ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, ConjugatesSubgroups g P Q

def SplitTorusConjugateIntoMinimalParabolic : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P S : ClosedSubgroup G.val),
    IsMinimalParabolic G P → IsSplitTorus S.group →
    ∃ (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) (T : ClosedSubgroup P.group),
      ConjugatesSubgroups g S (subgroupOfSubgroup P T)

def MaximalSplitToriConjugate : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S T : ClosedSubgroup G.val, IsMaximalSplitTorus S → IsMaximalSplitTorus T →
      ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, ConjugatesSubgroups g S T

def MaximalSplitToriConjugateByRadical : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsMinimalParabolic G P →
    ∀ (U : ClosedSubgroup P.group), IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U →
    ∀ S T : ClosedSubgroup P.group, IsMaximalSplitTorus S → IsMaximalSplitTorus T →
      ∃ a : 𝟙_ (SchemeOver k) ⟶ U.group.X,
        ConjugatesSubgroups (a ≫ U.inclusion.hom.hom) S T

/-- The cocharacter of the specified split torus gives the Levi decomposition
of the minimal parabolic, with Levi the scheme centralizer of that torus. -/
def MinimalParabolicLevi : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsMinimalParabolic G P →
    ∀ S : ClosedSubgroup P.group, IsMaximalSplitTorus S →
      ∃ (c : Cocharacter S.group)
        (D : LimitDecomposition (c ≫ (subgroupOfSubgroup P S).inclusion)),
        SameSubgroup P D.parabolic ∧ IsContractingRadical D ∧
        IsReductive (closedSubgroupAlgebraicGroup D.centralizer) ∧
        IsSubgroupOf (subgroupOfSubgroup P S) D.centralizer ∧
        RepresentsSubgroup D.centralizer
          (fun _ g ↦ Centralizes (subgroupOfSubgroup P S).inclusion g)

end LinearAlgebraicGroups.Specs.Relative.MaximalSplitTori
