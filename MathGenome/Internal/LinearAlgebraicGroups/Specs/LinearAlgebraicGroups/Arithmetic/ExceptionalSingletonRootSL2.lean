import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.NumberTheory.LocalField.Basic

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalSingletonRootSL2

open AbstractPairing (Root)
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open GeneralLinearStructure (SpecialMatrixPoints)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open GeometricRadicals (IsMaximalTorus IsSemisimple)
open Pinning (AttachedDatum SplitBorelPair)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open RootGroups (IsRootSubgroup Proportional)
open SchemeDerivedGroup (IsSubgroupOf)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (Index closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)

noncomputable section

variable {F : Type u} [Field F]

local notation "Fsep" => SeparableClosure F
private abbrev Gm (K : Type u) [Field K] := specGroup (groupAlgebra K IntegerCharacters)

/-- The rational torus inclusion and its identification with the torus of the
marked split pair over the separable closure. -/
structure MarkedTori (G : AffineAlgebraicGroup F) where
  S : ClosedSubgroup G.val
  maximalSplit : IsMaximalSplitTorus S
  T : ClosedSubgroup G.val
  maximalTorus : IsMaximalTorus T
  intoTorus : S.group ⟶ T.group
  intoTorus_eq : intoTorus ≫ T.inclusion = S.inclusion
  P : SplitBorelPair Fsep
  datum : AttachedDatum P
  ambient : P.G.val ≅ (groupBaseChange F Fsep).obj G.val
  torus : (groupBaseChange F Fsep).obj T.group ≅ P.T.group
  torus_eq : torus.hom ≫ P.T.inclusion ≫ ambient.hom =
    (groupBaseChange F Fsep).map T.inclusion

variable {G : AffineAlgebraicGroup F}

abbrev MarkedTori.splitInAbsolute (A : MarkedTori G) :
    (groupBaseChange F Fsep).obj A.S.group ⟶ A.P.T.group :=
  (groupBaseChange F Fsep).map A.intoTorus ≫ A.torus.hom

abbrev MarkedTori.restrict (A : MarkedTori G) (χ : Character A.P.T.group) :
    Character ((groupBaseChange F Fsep).obj A.S.group) :=
  A.splitInAbsolute ≫ χ

/-- The only absolute roots restricting to the given nonzero rational line
are the indicated root and its opposite. -/
def HasSingletonRootLine (A : MarkedTori G) (α : Root A.P.T) : Prop :=
  A.restrict α.val ≠ 1 ∧
    ∀ β : Root A.P.T, A.restrict β.val ≠ 1 →
      Proportional (A.restrict α.val) (A.restrict β.val) →
        β.val = α.val ∨ β.val = α.val⁻¹

/-- A closed split SL₂ in the original group. Its two elementary unipotent
subgroups are the descents of the marked absolute root groups. -/
structure SplitRootSL2 (A : MarkedTori G) (α : Root A.P.T) where
  subgroup : ClosedSubgroup G.val
  matrix : SpecialMatrixPoints (closedSubgroupAlgebraicGroup subgroup) 2
  positive : ClosedSubgroup subgroup.group
  negative : ClosedSubgroup subgroup.group
  positive_eq : ∀ (R : TestAlgebra F) (g : GroupPoints subgroup.group R),
    g ∈ SubgroupSections positive ((testSpec F).obj (op R)) ↔
      let m := (matrix.hom.app R g).val
      m (⟨0⟩ : Index.{u} 2) ⟨0⟩ = 1 ∧ m ⟨1⟩ ⟨1⟩ = 1 ∧ m ⟨1⟩ ⟨0⟩ = 0
  negative_eq : ∀ (R : TestAlgebra F) (g : GroupPoints subgroup.group R),
    g ∈ SubgroupSections negative ((testSpec F).obj (op R)) ↔
      let m := (matrix.hom.app R g).val
      m (⟨0⟩ : Index.{u} 2) ⟨0⟩ = 1 ∧ m ⟨1⟩ ⟨1⟩ = 1 ∧ m ⟨0⟩ ⟨1⟩ = 0
  generated : ∀ H : ClosedSubgroup G.val,
    IsSubgroupOf (subgroupOfSubgroup subgroup positive) H →
    IsSubgroupOf (subgroupOfSubgroup subgroup negative) H →
      IsSubgroupOf subgroup H
  positiveAbsolute : ClosedSubgroup A.P.G.val
  negativeAbsolute : ClosedSubgroup A.P.G.val
  positiveIso : (groupBaseChange F Fsep).obj positive.group ≅ positiveAbsolute.group
  negativeIso : (groupBaseChange F Fsep).obj negative.group ≅ negativeAbsolute.group
  positiveInclusion : positiveIso.hom ≫ positiveAbsolute.inclusion ≫ A.ambient.hom =
    (groupBaseChange F Fsep).map (positive.inclusion ≫ subgroup.inclusion)
  negativeInclusion : negativeIso.hom ≫ negativeAbsolute.inclusion ≫ A.ambient.hom =
    (groupBaseChange F Fsep).map (negative.inclusion ≫ subgroup.inclusion)
  positiveRoot : IsRootSubgroup A.P.T positiveAbsolute α.val
  negativeRoot : IsRootSubgroup A.P.T negativeAbsolute α.val⁻¹
  diagonal : Cocharacter subgroup.group
  diagonal_eq : ∀ (R : TestAlgebra F) (t : Rˣ),
    (matrix.hom.app R (cocharacterPoint diagonal R t)).val =
      Matrix.diagonal (fun i : Index.{u} 2 => if i.down = 0 then (t : R) else (t⁻¹ : Rˣ))
  coroot : Cocharacter A.S.group
  diagonalInAmbient : diagonal ≫ subgroup.inclusion = coroot ≫ A.S.inclusion
  multiplicative : Gm Fsep ≅ (groupBaseChange F Fsep).obj (Gm F)
  multiplicative_eq : ∀ (R : TestAlgebra Fsep) (t : Rˣ),
    baseChangePoint F Fsep (Gm F).X R (unitPoint R t ≫ multiplicative.hom.hom.hom) =
      unitPoint ((restrictTestAlgebra F Fsep).obj R) t
  coroot_eq : multiplicative.hom ≫ (groupBaseChange F Fsep).map coroot ≫ A.splitInAbsolute =
    Additive.toMul (A.datum.toBased.datum.coroot α)
  coroot_primitive : ∃ χ : Character A.P.T.group,
    pairing A.P.T.group χ (Additive.toMul (A.datum.toBased.datum.coroot α)) = 1

/-- Extend the specified rational point and view it in the marked absolute group. -/
abbrev MarkedTori.absolutePoint (A : MarkedTori G) (w : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
    𝟙_ (SchemeOver Fsep) ⟶ A.P.G.val.X :=
  scalarExtendedRationalPoint Fsep w ≫ A.ambient.inv.hom.hom

/-- The anti-diagonal in the descended SL₂ acts on the two marked tori by
scheme conjugation. On the absolute lattices it acts by the attached reflection. -/
structure RationalReflection {A : MarkedTori G} {α : Root A.P.T}
    (H : SplitRootSL2 A α) where
  representative : 𝟙_ (SchemeOver F) ⟶ H.subgroup.group.X
  representative_eq :
    (H.matrix.hom.app (CommAlgCat.of F F)
      (toUnit _ ≫ representative)).val =
      fun i j : Index.{u} 2 =>
        if i.down = j.down then 0 else if i.down = 0 then 1 else -1
  splitConjugation : A.S.group ≅ A.S.group
  splitConjugates :
    let w := toUnit A.S.group.X ≫ representative ≫ H.subgroup.inclusion.hom.hom
    (splitConjugation.hom ≫ A.S.inclusion).hom.hom = w * A.S.inclusion.hom.hom * w⁻¹
  absoluteConjugation : A.P.T.group ≅ A.P.T.group
  absoluteConjugates :
    let w := toUnit A.P.T.group.X ≫ A.absolutePoint (representative ≫ H.subgroup.inclusion.hom.hom)
    (absoluteConjugation.hom ≫ A.P.T.inclusion).hom.hom = w * A.P.T.inclusion.hom.hom * w⁻¹
  characterReflection : ∀ χ : Character A.P.T.group,
    Additive.ofMul (absoluteConjugation.inv ≫ χ) =
      A.datum.toBased.datum.reflection α (Additive.ofMul χ)
  cocharacterReflection : ∀ c : Cocharacter A.P.T.group,
    Additive.ofMul (c ≫ absoluteConjugation.hom) =
      A.datum.toBased.datum.coreflection α (Additive.ofMul c)

/-- A singleton absolute root line over a nonzero relative line gives a
closed split SL₂ and a rational representative of its marked reflection. -/
def SingletonRootSL2 : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsSemisimple G → GeometricallySimplyConnected G →
      ∀ (A : MarkedTori G) (α : Root A.P.T), HasSingletonRootLine A α →
        ∃ H : SplitRootSL2 A α, Nonempty (RationalReflection H)

end

end LinearAlgebraicGroups.Specs.ExceptionalSingletonRootSL2
