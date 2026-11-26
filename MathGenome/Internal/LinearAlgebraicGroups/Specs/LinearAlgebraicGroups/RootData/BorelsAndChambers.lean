import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterDynamics
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.Basic.Real.Basic

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.BorelsAndChambers

open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots adjointWeightVectors pairing)
open GeometricBorelConjugacy (ConjugatesSubgroups IsBorel IsKBorel)
open GeometricRadicals (GeometricGroup IsReductive IsSplitTorus IsUnipotentRadical
  baseChangedSubgroup)
open RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open RootGroups (IsRootSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition lieImage)

noncomputable section

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- Regularity is measured on the actual absolute roots of the torus. -/
def IsRegular (T : ClosedSubgroup G) (cochar : Cocharacter T.group) : Prop :=
  ∀ α : ↥(absoluteRoots T), pairing T.group α.val cochar ≠ 0

/-- The roots which pair strictly positively with the displayed cocharacter. -/
def positiveRoots (T : ClosedSubgroup G) (cochar : Cocharacter T.group) : Set ↥(absoluteRoots T) :=
  {α | 0 < pairing T.group α.val cochar}

/-- The roots whose ambient tangent weight space lies in the subgroup's Lie algebra. -/
def subgroupRoots (T B : ClosedSubgroup G) : Set ↥(absoluteRoots T) :=
  {α | adjointWeightVectors T α.val ⊆ lieImage B}

/-- A positive system is the set of signs determined by a real linear functional
on the character lattice that vanishes on no root. -/
def IsPositiveSystem (T : ClosedSubgroup G) (S : Set ↥(absoluteRoots T)) : Prop :=
  ∃ f : Additive (Character T.group) →ₗ[ℤ] ℝ,
    (∀ α : ↥(absoluteRoots T), f (Additive.ofMul α.val) ≠ 0) ∧
      S = {α | 0 < f (Additive.ofMul α.val)}

/-- The contracting group as a closed subgroup of the parabolic, via the
kernel morphism of its limit map. -/
def contractingSubgroup {cochar : Cocharacter G} (D : LimitDecomposition cochar) :
    ClosedSubgroup D.parabolic.group := by
  letI := D.parabolic.isClosedImmersion
  haveI : IsClosedImmersion
      (D.contractingToParabolic.hom.hom.left ≫ D.parabolic.inclusion.hom.hom.left) := by
    change IsClosedImmersion (D.contractingToParabolic ≫ D.parabolic.inclusion).hom.hom.left
    rw [D.contracting_in_G]
    exact D.contracting.isClosedImmersion
  exact ⟨D.contracting.group, D.contractingToParabolic,
    IsClosedImmersion.of_comp_isClosedImmersion _ D.parabolic.inclusion.hom.hom.left⟩

/-- Every chamber of the real root hyperplane arrangement has a representative
in the cocharacter lattice of the split torus. -/
def PositiveSystemsFromCocharacters : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ S : Set ↥(absoluteRoots T),
      IsPositiveSystem T S ↔
        ∃ cochar : Cocharacter T.group, IsRegular T cochar ∧ positiveRoots T cochar = S

/-- The regular limit parabolic is a Borel through T. Its limit section is T
and its split kernel is the unipotent radical, also over the algebraic closure.
The semidirect product uses the actual multiplication in `LimitDecomposition`. -/
def RegularCocharacterBorel : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ cochar : Cocharacter T.group, IsRegular T cochar →
    ∀ D : LimitDecomposition (cochar ≫ T.inclusion),
      SameSubgroup D.centralizer T ∧
      IsKBorel D.parabolic ∧ IsSubgroupOf T D.parabolic ∧
      subgroupRoots T D.parabolic = positiveRoots T cochar ∧
      let B := closedSubgroupAlgebraicGroup D.parabolic
      let U := contractingSubgroup D
      IsUnipotentRadical B U ∧
        ∃ hU : IsClosedImmersion
            ((groupBaseChange k (AlgebraicClosure k)).map U.inclusion).hom.hom.left,
          IsUnipotentRadical (GeometricGroup B) (baseChangedSubgroup (AlgebraicClosure k) U hU)

/-- Each k-Borel through T is a regular limit parabolic. Taking the roots of
its Lie algebra gives the bijection with positive systems, with uniqueness as
closed subgroups of G. -/
def BorelsThroughT : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      (∀ B : ClosedSubgroup G.val, IsKBorel B → IsSubgroupOf T B →
        ∃ (cochar : Cocharacter T.group) (D : LimitDecomposition (cochar ≫ T.inclusion)),
          IsRegular T cochar ∧ SameSubgroup B D.parabolic ∧
            subgroupRoots T B = positiveRoots T cochar) ∧
      ∀ S : Set ↥(absoluteRoots T),
        IsPositiveSystem T S ↔
          ∃ B : ClosedSubgroup G.val,
            IsKBorel B ∧ IsSubgroupOf T B ∧ subgroupRoots T B = S ∧
            ∀ B' : ClosedSubgroup G.val, IsKBorel B' → IsSubgroupOf T B' →
              subgroupRoots T B' = S → SameSubgroup B B'

/-- Geometric conjugacy through T can be realized by a Weyl representative.
The left action on the chamber is pullback by inverse torus conjugation. -/
def GeometricBorelChamberConjugacy : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ B₁ B₂ : ClosedSubgroup G.val, IsBorel B₁ → IsBorel B₂ →
      IsSubgroupOf T B₁ → IsSubgroupOf T B₂ →
      ∃ (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (c : T.group ≅ T.group),
        Normalizes T.inclusion n ∧ ConjugatesSubgroups n B₁ B₂ ∧
        (let t : T.group.X ⟶ G.val.X := toUnit T.group.X ≫ n
         (c.hom ≫ T.inclusion).hom.hom = t * T.inclusion.hom.hom * t⁻¹) ∧
        (fun α : ↥(absoluteRoots T) ↦ c.inv ≫ α.val) '' subgroupRoots T B₁ =
          Subtype.val '' subgroupRoots T B₂

/-- For each absolute root the Lie weight line belongs to the Lie algebra of a
geometric Borel through T exactly when the Borel contains its root subgroup. -/
def GeometricBorelRootSubgroups : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ B : ClosedSubgroup G.val, IsBorel B → IsSubgroupOf T B →
    ∀ (α : ↥(absoluteRoots T)) (U : ClosedSubgroup G.val),
      IsRootSubgroup T U α.val → (α ∈ subgroupRoots T B ↔ IsSubgroupOf U B)

end

end LinearAlgebraicGroups.Specs.BorelsAndChambers
