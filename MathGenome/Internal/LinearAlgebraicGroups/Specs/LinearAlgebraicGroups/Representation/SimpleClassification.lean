import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.InducedNonvanishing
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.BaseChange
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

open CategoryTheory AlgebraicGeometry WithConv Coalgebra
open scoped CategoryTheory.MonObj TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.Specs.SimpleClassification

open FlagLineBundle
open CharacterDescent (Character Cocharacter)
open GeometricRadicals (IsUnipotentRadical IsSemisimple IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open RootWeightAction (Representation IsPrimitive fixedSpace weightSpace act extendVector)
open PrimitiveLine (IsSimple IsEquivariant)
open InducedNonvanishing (Dominant)
open InducedSocle (IsSimpleSubmodule)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.RationalRepresentations
  (evaluate tensorCoordinate scalarExtension IsScalarExtension)
open AbstractPairing (Datum)
open SimplyConnectedLattice (corootLatticeOf GeometricallySimplyConnected)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- A highest weight of a simple module is the weight of a primitive vector
for the positive Borel. -/
def HasHighestWeight {I : Type u} [Fintype I] [DecidableEq I]
    (P : OppositeBorelPair G) (U : ClosedSubgroup P.positive.group)
    (ρ : Representation G.val I) (χ : Character P.torus.group) : Prop :=
  ∃ v, IsPrimitive ρ P.torus P.positive U χ v

/-- The matrix action of a coaction on a vector space expressed in a basis. -/
def Realizes {V I : Type u} [AddCommGroup V] [Module k V] [Fintype I] [DecidableEq I]
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (b : Module.Basis I k V) (δ : RightComodule k A V) (ρ : Representation G.val I) : Prop :=
  ∀ (R : TestAlgebra k) (g : A →ₐ[k] R) (v : I → k) (i : I),
    act ρ R ((testSpec k).map (CommAlgCat.ofHom g).op ≫ e.hom.hom.hom)
      (extendVector R v) i = tensorCoordinate b i (evaluate A δ g (b.equivFun.symm v))

/-- A basis presentation of (L(χ)) as the simple socle of the left
translation action on the regular functions with opposite Borel covariance. -/
structure SocleModel (P : OppositeBorelPair G) (U : ClosedSubgroup P.positive.group)
    (χ : Character P.torus.group) where
  projection : BorelProjection P
  A : HopfAlgebraCategory k
  D : HopfAlgebraCategory k
  groupIso : specGroup A ≅ G.val
  borelIso : specGroup D ≅ P.negative.group
  restriction : A ⟶ D
  character : DiagonalizableGroups.groupAlgebra k
    DiagonalizableGroups.IntegerCharacters ⟶ D
  coordinate : GroupLike k D
  restriction_spec :
    specGroupMap restriction ≫ groupIso.hom = borelIso.hom ≫ P.negative.inclusion
  character_spec :
    specGroupMap character = borelIso.hom ≫ projection.projection ≫ χ
  coordinate_spec : (coordinate : D) = characterCoordinate character
  inducedCoaction : RightComodule k A (covariantFunctions restriction coordinate)
  leftTranslation :
    ((covariantFunctions restriction coordinate).subtype.rTensor A).comp
      inducedCoaction.coaction =
        (leftRegularCoaction A).comp (covariantFunctions restriction coordinate).subtype
  I : Type u
  [finiteI : Fintype I]
  [decI : DecidableEq I]
  inducedBasis : Module.Basis I k (covariantFunctions restriction coordinate)
  inducedAction : Representation G.val I
  inducedAction_spec : Realizes groupIso inducedBasis inducedCoaction inducedAction
  socle : Submodule k (I → k)
  socle_simple : IsSimpleSubmodule inducedAction socle
  socle_unique : ∀ M : Submodule k (I → k), IsSimpleSubmodule inducedAction M → M = socle
  highestVector : socle
  highest_primitive :
    IsPrimitive inducedAction P.torus P.positive U χ (highestVector : I → k)
  inducedFixedLine :
    fixedSpace inducedAction (U.inclusion ≫ P.positive.inclusion) =
      Submodule.span k {(highestVector : I → k)}
  socleCoaction : RightComodule k A socle
  socleCoaction_spec :
    let i := inducedBasis.equivFun.symm.toLinearMap.comp socle.subtype
    (i.rTensor A).comp socleCoaction.coaction = inducedCoaction.coaction.comp i
  J : Type u
  [finiteJ : Fintype J]
  [decJ : DecidableEq J]
  socleBasis : Module.Basis J k socle
  socleAction : Representation G.val J
  socleAction_spec : Realizes groupIso socleBasis socleCoaction socleAction
  simple : IsSimple socleAction
  highestLine :
    weightSpace socleAction P.torus χ = Submodule.span k {socleBasis.equivFun highestVector}
  primitive :
    IsPrimitive socleAction P.torus P.positive U χ (socleBasis.equivFun highestVector)

attribute [instance] SocleModel.finiteI SocleModel.decI SocleModel.finiteJ SocleModel.decJ

/-- Every simple module has one dominant highest weight. Each dominant weight
is realized by the simple socle of the induced module, which accounts for
all simple modules with that weight up to equivariant isomorphism. -/
def Classification : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G)
    (U : ClosedSubgroup P.positive.group),
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    (∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I), IsSimple ρ →
      ∃! χ : Character P.torus.group, Dominant P χ ∧ HasHighestWeight P U ρ χ) ∧
    (∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I), IsSimple ρ →
      ∀ χ, HasHighestWeight P U ρ χ → Dominant P χ) ∧
    ∀ χ, Dominant P χ →
      ∃ S : SocleModel P U χ,
        ∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I), IsSimple ρ →
          (Nonempty {f : (I → k) ≃ₗ[k] (S.J → k) //
             IsEquivariant ρ S.socleAction f.toLinearMap} ↔ HasHighestWeight P U ρ χ)

/-- Every equivariant endomorphism of a simple representation is a unique
scalar. This applies in particular to each (L(χ)). -/
def ScalarEndomorphisms : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
    (G : AffineAlgebraicGroup k) (_P : OppositeBorelPair G)
    (ρ : Representation G.val I), IsSimple ρ →
    ∀ f : (I → k) →ₗ[k] (I → k), IsEquivariant ρ ρ f →
      ∃! a : k, f = a • LinearMap.id

/-- Absolute simplicity with its highest weight. The two linear equations
are the coactions restricted along the base changes of (U 	o G) and
(T 	o G). The factor (1 otimes c) is the extended character of (T). -/
def AbsoluteSimplicity : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G)
    (U : ClosedSubgroup P.positive.group),
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∀ (χ : Character P.torus.group) (S : SocleModel P U χ),
      ∃ (C E : HopfAlgebraCategory k) (eU : specGroup C ≅ U.group)
        (eT : specGroup E ≅ P.torus.group) (qU : S.A ⟶ C) (qT : S.A ⟶ E)
        (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ E),
        specGroupMap qU ≫ S.groupIso.hom = eU.hom ≫ U.inclusion ≫ P.positive.inclusion ∧
        specGroupMap qT ≫ S.groupIso.hom = eT.hom ≫ P.torus.inclusion ∧
        specGroupMap φ = eT.hom ≫ χ ∧
        ∀ (K : Type u) [Field K] [Algebra k K],
          ∃ δ : RightComodule K (scalarExtension S.A K) (K ⊗[k] S.socle),
            IsScalarExtension S.A S.socleCoaction δ ∧
            (⊤ : Submodule K (K ⊗[k] S.socle)) ≠ ⊥ ∧
            (∀ M : Submodule K (K ⊗[k] S.socle), δ.IsSubcomodule M → M = ⊥ ∨ M = ⊤) ∧
            ((1 : K) ⊗ₜ[k] S.highestVector) ≠ 0 ∧
            (let restrict := fun {B : HopfAlgebraCategory k} (q : S.A ⟶ B) =>
                ((extendedHopfMap K q).hom.toAlgHom.toLinearMap.lTensor (K ⊗[k] S.socle)).comp
                  δ.coaction
             let v := (1 : K) ⊗ₜ[k] S.highestVector
             {x | restrict qU x = x ⊗ₜ[K] (1 : scalarExtension C K)} = (Submodule.span K {v} : Set _) ∧
             {x | restrict qT x = x ⊗ₜ[K] ((1 : K) ⊗ₜ[k] characterCoordinate φ)} =
               (Submodule.span K {v} : Set _))

/-- The full integral weight lattice for a semisimple root datum is the dual
of the coroot lattice. The actual characters map to it by the root datum
pairing. -/
def weightLatticeMap {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) : Additive (Character T.group) →ₗ[ℤ] Module.Dual ℤ (corootLatticeOf D) :=
  (corootLatticeOf D).subtype.dualMap.comp D.rootDatum.toLinearMap

def SimplyConnectedWeightLattice : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsSemisimple G →
    ∀ (T : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∀ [IsCommMonObj T.group.X] (D : Datum T),
        Function.Injective (weightLatticeMap D) ∧
          (Function.Surjective (weightLatticeMap D) ↔ GeometricallySimplyConnected G)

end LinearAlgebraicGroups.Specs.SimpleClassification
