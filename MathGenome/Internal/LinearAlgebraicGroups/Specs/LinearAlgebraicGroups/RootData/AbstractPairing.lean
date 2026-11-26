import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.RootSystem.Reduced

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.AbstractPairing

open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots pairing)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (Centralizer FlagIdentification IsGeometricallyMaximal IsRankOneBorelPair)
open RootGroups (AdditiveLine CorootReflection HasScalarAction IsRootSubgroup
  ProjectiveAction TransvectionParametrization)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The index of the root datum is the set of nontrivial adjoint weights. -/
abbrev Root (T : ClosedSubgroup G.val) := ↥(absoluteRoots T)

/-- This cocharacter comes from the rank-one word in the matched transvection
coordinates of the marked flag. -/
def IsAttachedCoroot (T : ClosedSubgroup G.val) (α : Root T) (c : Cocharacter T.group) : Prop :=
  ∃ (C : Centralizer T α.val) (cochar : Cocharacter T.group),
    IsReductive (Unipotent.closedSubgroupAlgebraicGroup C.subgroup) ∧
    0 < pairing T.group α.val cochar ∧
    ∃ (D : LimitDecomposition (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))
      (E : LimitDecomposition (oppositeCocharacter (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))),
      IsRankOneBorelPair C cochar D E ∧
      ∃ (Q : QuotientEmbedding.Presentation D.parabolic)
        (F : FlagIdentification C.torus D.parabolic E.parabolic E.contracting Q)
        (P : ProjectiveAction F.action (η[C.subgroup.group.X] ≫ Q.projection)
          (F.normalizerPoint ≫ Q.projection))
        (A : AdditiveLine k)
        (p : TransvectionParametrization P A D.contracting ⟨0⟩ ⟨1⟩ (by decide))
        (n : TransvectionParametrization P A E.contracting ⟨1⟩ ⟨0⟩ (by decide)),
        IsRootSubgroup T (subgroupOfSubgroup C.subgroup D.contracting) α.val ∧
        IsRootSubgroup T (subgroupOfSubgroup C.subgroup E.contracting) α.val⁻¹ ∧
        let xpos := p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion
        let xneg := n.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion
        HasScalarAction T α.val xpos ∧ HasScalarAction T α.val⁻¹ xneg ∧
          ∃ r : CorootReflection T α.val xpos xneg, r.coroot = c

/-- The rational normalizer acts through its scheme conjugation of the torus.
The left actions are inverse pullback on characters and pushforward on
cocharacters. Mathlib records the coweight component contravariantly. -/
def NormalizerAction (T : ClosedSubgroup G.val) [IsCommMonObj T.group.X]
    (P : RootDatum (Root T) (Additive (Character T.group)) (Additive (Cocharacter T.group))) :
    Prop :=
  ∃ N : ClosedSubgroup G.val,
    RepresentsSubgroup N (fun _ n ↦ Normalizes T.inclusion n) ∧
    ∃ act : (𝟙_ (SchemeOver k) ⟶ N.group.X) →* P.Aut,
      ∀ n, ∃ e : T.group ≅ T.group,
        let g := toUnit T.group.X ≫ n ≫ N.inclusion.hom.hom
        (e.hom ≫ T.inclusion).hom.hom = g * T.inclusion.hom.hom * g⁻¹ ∧
        (∀ χ : Character T.group,
          (act n).weightEquiv (Additive.ofMul χ) = Additive.ofMul (e.inv ≫ χ)) ∧
        (∀ cochar : Cocharacter T.group,
          (act n).coweightEquiv.symm (Additive.ofMul cochar) = Additive.ofMul (cochar ≫ e.hom))

/-- The reduced integral root datum on the actual two lattices of the torus,
with the normalizer action and the rank-one attachment of its coroots. -/
structure Datum (T : ClosedSubgroup G.val) [IsCommMonObj T.group.X] where
  finiteRoots : Finite (Root T)
  freeCharacters : Module.Free ℤ (Additive (Character T.group))
  finiteCharacters : Module.Finite ℤ (Additive (Character T.group))
  freeCocharacters : Module.Free ℤ (Additive (Cocharacter T.group))
  finiteCocharacters : Module.Finite ℤ (Additive (Cocharacter T.group))
  rootDatum : RootDatum (Root T) (Additive (Character T.group)) (Additive (Cocharacter T.group))
  root_eq : ∀ α, rootDatum.root α = Additive.ofMul α.val
  pairing_eq : ∀ (χ : Character T.group) (cochar : Cocharacter T.group),
    rootDatum.toLinearMap (Additive.ofMul χ) (Additive.ofMul cochar) = pairing T.group χ cochar
  attached : ∀ α, IsAttachedCoroot T α (Additive.toMul (rootDatum.coroot α))
  reduced : rootDatum.IsReduced
  reducedCoroots : rootDatum.flip.IsReduced
  opposite : ∀ α β, rootDatum.root β = -rootDatum.root α ↔
    rootDatum.coroot β = -rootDatum.coroot α
  normalizerAction : NormalizerAction T rootDatum

/-- Every split connected reductive pair has its finite reduced integral
root datum. This includes the empty root set of a torus. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∃ h : IsCommMonObj T.group.X, letI := h; Nonempty (Datum T)

end

end LinearAlgebraicGroups.Specs.AbstractPairing
