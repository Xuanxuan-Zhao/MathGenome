import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagLineBundle
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FiniteDistributions
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.KrullDimension.Polynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.FlagRelativeFrobeniusAtlas

noncomputable section

variable {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p]

/-- Frobenius on the base scheme. -/
def baseFrobenius : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (iterateFrobenius k p r))

variable [IsAlgClosed k]

/-- Model for base change by Frobenius over a perfect field. The first
projection is the identity of the underlying scheme. -/
def twist : SchemeOver k ⥤ SchemeOver k :=
  Over.map (Spec.map (CommRingCat.ofHom (iterateFrobeniusEquiv k p r).symm.toRingHom))

def TwistType := ∀ {k : Type u} [Field k] (p : ℕ) (_r : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k], SchemeOver k ⥤ SchemeOver k

def TwistValue : TwistType.{u} := @twist

/-- The displayed model is the scalar base change with its specified
projections. -/
def TwistIsBaseChange : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (X : SchemeOver k),
    IsPullback (𝟙 X.left) ((twist p r).obj X).hom X.hom (baseFrobenius p r)

/-- A relative Frobenius component in the displayed twist model has the
identity underlying point map and takes the prescribed powers on sections. -/
def IsRelativeFrobenius (X : SchemeOver k) (F : X ⟶ (twist p r).obj X) : Prop :=
  (∀ x : X.left, F.left x = x) ∧
  ∀ (U : X.left.Opens), (h : U ≤ F.left ⁻¹ᵁ U) →
    ∀ s : Γ(X.left, U), F.left.appLE U U h s = s ^ (p ^ r)

/-- Naturality in all schemes over the field, including the projection
of the flag quotient, the group multiplication and its action. -/
def RelativeFrobeniusNaturality : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k],
    ∃ F : 𝟭 (SchemeOver k) ⟶ twist p r,
      ∀ X, IsRelativeFrobenius p r X (F.app X)

instance twistEquivalence : (twist (k := k) p r).IsEquivalence := by
  let e := Scheme.Spec.mapIso (iterateFrobeniusEquiv k p r).symm.toCommRingCatIso.op
  let : IsIso (Spec.map (CommRingCat.ofHom (iterateFrobeniusEquiv k p r).symm.toRingHom)) :=
    e.isIso_hom
  unfold twist
  infer_instance

/-- Pullback of group objects along the scalar Frobenius. -/
instance twistMonoidal : (twist (k := k) p r).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

abbrev twistGroup : GroupScheme k ⥤ GroupScheme k := (twist p r).mapGrp

def RelativeGroupNaturality : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k],
    ∃ F : 𝟭 (GroupScheme k) ⟶ twistGroup p r,
      ∀ G, IsRelativeFrobenius p r G.X (F.app G).hom.hom

/-- The projection from a scalar extension of an affine group. -/
def affineScalarProjection (K : Type u) [Field K] [Algebra k K] (A : HopfAlgebraCategory k) :
    (specGroup (extendedHopf K A)).X.left ⟶ (specGroup A).X.left :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom)

/-- The projection from the affine Frobenius twist to the original spectrum. -/
def affineTwistProjection (A : HopfAlgebraCategory k) :
    (specGroup (LinearAlgebraicGroups.FiniteDistributions.twistCoordinates k p r A)).X.left ⟶
      (specGroup A).X.left :=
  letI := (iterateFrobenius k p r).toAlgebra
  affineScalarProjection k A

/-- The group morphism agrees with the Hopf-algebra construction on the
actual base change of the group. -/
def AffineFrobeniusComparison : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (A : HopfAlgebraCategory k),
    ∃ (F : specGroup A ⟶ (twistGroup p r).obj (specGroup A))
      (e : specGroup (LinearAlgebraicGroups.FiniteDistributions.twistCoordinates k p r A) ≅
        (twistGroup p r).obj (specGroup A))
      (f : LinearAlgebraicGroups.FiniteDistributions.twistCoordinates k p r A ⟶ A),
      IsRelativeFrobenius p r (specGroup A).X F.hom.hom ∧
      e.hom.hom.hom.left = affineTwistProjection p r A ∧
      LinearAlgebraicGroups.FiniteDistributions.FrobeniusFormula k p r A f ∧
      specGroupMap f ≫ e.hom = F

/-- The structure map to the spectrum of the prime field. -/
def primeFieldMap : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (ULift.{u} (ZMod p))) :=
  Spec.map (CommRingCat.ofHom ((ZMod.castHom (dvd_refl p) k).comp ULift.ringEquiv.toRingHom))

/-- Any model over the prime field is unchanged by twisting its scalar extension.
The naturality includes morphisms in a marked flag presentation. -/
def PrimeFieldModels : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k],
    Nonempty (Over.pullback (primeFieldMap (k := k) p) ⋙ twist p r ≅
      Over.pullback (primeFieldMap (k := k) p))

def TwistPreservesSplitTorus : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (T : GroupScheme k), GeometricRadicals.IsSplitTorus T →
      GeometricRadicals.IsSplitTorus ((twistGroup p r).obj T)

/-- The inclusion from the Hopf quotient for the kernel maps to the identity
under the geometric Frobenius. This applies even to nonreduced test schemes. -/
def HopfKernelActsTrivially : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (A : HopfAlgebraCategory k)
    (f : LinearAlgebraicGroups.FiniteDistributions.twistCoordinates k p r A ⟶ A)
    [_h : (kernelIdeal f).IsHopfIdeal k]
    (e : specGroup (LinearAlgebraicGroups.FiniteDistributions.twistCoordinates k p r A) ≅
      (twistGroup p r).obj (specGroup A))
    (F : specGroup A ⟶ (twistGroup p r).obj (specGroup A)),
      specGroupMap f ≫ e.hom = F →
      (specGroupMap (hopfQuotientMap A (kernelIdeal f)) ≫ F).hom.hom = 1

open DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open LinearAlgebraicGroups.FiniteDistributions (twistCoordinates FrobeniusFormula)

/-- Character transport keeps the exponent in the split multiplicative group.
The coefficient calculation is stated for the character on the Borel, so it
also applies directly to the functions defining the associated line. -/
def TwistedCharacters : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k],
    ∃ e : (twistGroup p r).obj (specGroup (groupAlgebra k IntegerCharacters)) ≅
          specGroup (groupAlgebra k IntegerCharacters),
      (∀ (H : GroupScheme k) (χ : CharacterDescent.Character H)
        (F : H ⟶ (twistGroup p r).obj H),
        IsRelativeFrobenius p r H.X F.hom.hom →
        F ≫ ((twistGroup p r).map χ ≫ e.hom) = χ ^ (p ^ r)) ∧
      ∀ (D : HopfAlgebraCategory k) (χ : groupAlgebra k IntegerCharacters ⟶ D),
        ∃ (d : specGroup (twistCoordinates k p r D) ≅ (twistGroup p r).obj (specGroup D))
          (χ' : groupAlgebra k IntegerCharacters ⟶ twistCoordinates k p r D),
          d.hom.hom.hom.left = affineTwistProjection p r D ∧
          specGroupMap χ' = d.hom ≫ (twistGroup p r).map (specGroupMap χ) ≫ e.hom ∧
          χ'.hom (MonoidAlgebra.of k _ integerGenerator) =
            RelativeFrobenius.scalarTensor (iterateFrobenius k p r) D 1
              (χ.hom (MonoidAlgebra.of k _ integerGenerator)) ∧
          ∀ (f : twistCoordinates k p r D ⟶ D), FrobeniusFormula k p r D f →
            f.hom (χ'.hom (MonoidAlgebra.of k _ integerGenerator)) =
              (χ.hom (MonoidAlgebra.of k _ integerGenerator)) ^ (p ^ r)

section Flag

open FlagLineBundle (OppositeBorelPair BorelProjection)
open QuotientEmbedding (Presentation)
open AbstractPairing (Root)
open BorelsAndChambers (subgroupRoots)
open OrderedRootProducts (RootSubgroupFamily Enumerates rootProduct product)

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative)

/-- The marked subgroup in the Frobenius twist is its scalar base change. -/
def twistSubgroup {M : GroupScheme k} (H : ClosedSubgroup M) :
    ClosedSubgroup ((twistGroup p r).obj M) :=
  ⟨(twistGroup p r).obj H.group, (twistGroup p r).map H.inclusion, H.isClosedImmersion⟩

/-- The affine algebraic group in the scalar twist, with the twisted structure map. -/
def twistAffineGroup (G : AffineAlgebraicGroup k) : AffineAlgebraicGroup k := by
  let t := Spec.map (CommRingCat.ofHom (iterateFrobeniusEquiv k p r).symm.toRingHom)
  letI : IsIso t :=
    (Scheme.Spec.mapIso (iterateFrobeniusEquiv k p r).symm.toCommRingCatIso.op).isIso_hom
  refine ⟨(twistGroup p r).obj G.val, G.property.1, ?_, ?_⟩
  · let := G.property.2.1
    exact inferInstanceAs (LocallyOfFiniteType (G.val.X.hom ≫ t))
  · let := G.property.2.2
    exact inferInstanceAs (QuasiCompact (G.val.X.hom ≫ t))

open GeometricRadicals (IsReductive IsSplitTorus)
open GeometricBorelConjugacy (IsKBorel)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open CharacterDescent (Character)

/-- The properties of the three specified subgroup inclusions after scalar
transport. Their maps are the actual twisted inclusions. -/
structure TwistedPairProperties (P : OppositeBorelPair G) : Prop where
  reductive : IsReductive (twistAffineGroup p r G)
  split : IsSplitTorus (twistSubgroup p r P.torus).group
  maximal : IsGeometricallyMaximal (twistSubgroup p r P.torus)
  positiveBorel : IsKBorel (twistSubgroup p r P.positive)
  negativeBorel : IsKBorel (twistSubgroup p r P.negative)
  inPositive : IsSubgroupOf (twistSubgroup p r P.torus) (twistSubgroup p r P.positive)
  inNegative : IsSubgroupOf (twistSubgroup p r P.torus) (twistSubgroup p r P.negative)
  opposite : OpenCell.AreOpposite (twistSubgroup p r P.torus)
    (twistSubgroup p r P.positive) (twistSubgroup p r P.negative)

/-- The split marking on the twisted group, using the transported subgroups. -/
def TwistedPairProperties.pair (h : TwistedPairProperties p r P) :
    OppositeBorelPair (twistAffineGroup p r G) where
  torus := twistSubgroup p r P.torus
  positive := twistSubgroup p r P.positive
  negative := twistSubgroup p r P.negative
  reductive := h.reductive
  split := h.split
  maximal := h.maximal
  positiveBorel := h.positiveBorel
  negativeBorel := h.negativeBorel
  inPositive := h.inPositive
  inNegative := h.inNegative
  opposite := h.opposite

/-- The actual relative Frobenius target as a marked split flag, with the
quotient comparison and the maps needed for pullback of associated lines. -/
structure MarkedFlagTwist (Q : Presentation P.negative) (b : BorelProjection P) where
  properties : TwistedPairProperties p r P
  borel : BorelProjection (properties.pair p r)
  inclusion_eq : borel.inclusion = (twistGroup p r).map b.inclusion
  projection_eq : borel.projection = (twistGroup p r).map b.projection
  radical_eq : borel.radical = twistSubgroup p r b.radical
  quotient : Presentation (properties.pair p r).negative
  comparison : quotient.scheme ≅ (twist p r).obj Q.scheme
  quotient_eq : quotient.projection ≫ comparison.hom = (twist p r).map Q.projection
  groupFrobenius : G.val ⟶ (twistGroup p r).obj G.val
  borelFrobenius : P.negative.group ⟶ (properties.pair p r).negative.group
  torusFrobenius : P.torus.group ⟶ (properties.pair p r).torus.group
  flagFrobenius : Q.scheme ⟶ quotient.scheme
  group_formula : IsRelativeFrobenius p r G.val.X groupFrobenius.hom.hom
  borel_formula : IsRelativeFrobenius p r P.negative.group.X borelFrobenius.hom.hom
  torus_formula : IsRelativeFrobenius p r P.torus.group.X torusFrobenius.hom.hom
  flag_formula : IsRelativeFrobenius p r Q.scheme (flagFrobenius ≫ comparison.hom)
  inclusion_square : P.negative.inclusion ≫ groupFrobenius =
    borelFrobenius ≫ (properties.pair p r).negative.inclusion
  torus_inclusion_square : b.inclusion ≫ borelFrobenius = torusFrobenius ≫ borel.inclusion
  projection_square : b.projection ≫ torusFrobenius = borelFrobenius ≫ borel.projection
  quotient_square : Q.projection ≫ flagFrobenius = groupFrobenius.hom.hom ≫ quotient.projection
  multiplicativeComparison :
    (twistGroup p r).obj (specGroup (groupAlgebra k IntegerCharacters)) ≅
      specGroup (groupAlgebra k IntegerCharacters)
  multiplicativeCoordinate :
    let A := groupAlgebra k IntegerCharacters
    ∃ a : A →+* A,
      multiplicativeComparison.inv.hom.hom.left = Spec.map (CommRingCat.ofHom a) ∧
      a (MonoidAlgebra.of k _ integerGenerator) = MonoidAlgebra.of k _ integerGenerator
  characters : Character P.torus.group ≃ Character (properties.pair p r).torus.group
  characters_eq : ∀ χ, characters χ = (twistGroup p r).map χ ≫ multiplicativeComparison.hom
  roots : Root P.torus ≃ Root (properties.pair p r).torus
  root_character : ∀ α, (roots α).val = characters α.val
  positive_roots : ∀ α, roots α ∈ subgroupRoots (properties.pair p r).torus
    (properties.pair p r).positive ↔ α ∈ subgroupRoots P.torus P.positive
  negative_roots : ∀ α, roots α ∈ subgroupRoots (properties.pair p r).torus
    (properties.pair p r).negative ↔ α ∈ subgroupRoots P.torus P.negative
  character_pullback : ∀ χ, borelFrobenius ≫ (borel.projection ≫ characters χ) =
    (b.projection ≫ χ) ^ (p ^ r)

def HasMarkedFlagTwist : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (b : BorelProjection P), Nonempty (MarkedFlagTwist p r Q b)

/-- The base-changed projection presents the right quotient by the twisted Borel. -/
def TwistedFlagQuotient : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative),
      let H := twistSubgroup p r P.negative
      let q := (twist p r).map Q.projection
      IsPullback prod.fst (HomogeneousQuotient.rightMultiplication H) q q ∧
      ∃ e : rightQuotientSheaf H ≅ schemeFppfSheaf ((twist p r).obj Q.scheme),
        rightQuotientProjection H ≫ e.hom = (fppfOver k).uliftYoneda.map q

/-- The twisted flag is represented by a right quotient with the transported
split torus and the transported projection of the Borel onto it. -/
def TwistedFlagPresentation : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative),
      let H := twistSubgroup p r P.negative
      let T := twistSubgroup p r P.torus
      ∃ (Q' : Presentation H) (e : Q'.scheme ≅ (twist p r).obj Q.scheme),
        Q'.projection ≫ e.hom = (twist p r).map Q.projection ∧
        GeometricRadicals.IsSplitTorus T.group ∧
        ∀ b : BorelProjection P,
          (twistGroup p r).map b.inclusion ≫ H.inclusion = T.inclusion ∧
          (twistGroup p r).map b.inclusion ≫ (twistGroup p r).map b.projection = 𝟙 T.group

/-- Both the quotient map and the action commute with relative Frobenius.
The kernel acts by the identity on the entire target functor of points. -/
def TwistedFlagActions : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∃ (f : G.val ⟶ (twistGroup p r).obj G.val)
      (F : Q.scheme ⟶ (twist p r).obj Q.scheme)
      (a' : ModObj ((twistGroup p r).obj G.val).X ((twist p r).obj Q.scheme)),
      IsRelativeFrobenius p r G.val.X f.hom.hom ∧ IsRelativeFrobenius p r Q.scheme F ∧
      a'.smul = Functor.LaxMonoidal.μ (twist p r) G.val.X Q.scheme ≫ (twist p r).map a.smul ∧
      μ[((twistGroup p r).obj G.val).X] ≫ (twist p r).map Q.projection =
        (𝟙 _ ⊗ₘ (twist p r).map Q.projection) ≫ a'.smul ∧
      Q.projection ≫ F = f.hom.hom ≫ (twist p r).map Q.projection ∧
      a.smul ≫ F = (f.hom.hom ⊗ₘ F) ≫ a'.smul ∧
      (∀ N : ClosedSubgroup G.val, IsSchemeKernel f N →
        let Y := (twist p r).obj Q.scheme
        lift (fst N.group.X Y ≫ N.inclusion.hom.hom ≫ f.hom.hom) (snd N.group.X Y) ≫ a'.smul =
          snd N.group.X Y) ∧
      ∀ (S : SchemeOver k) (x : S ⟶ G.val.X) (y : S ⟶ (twist p r).obj Q.scheme),
        x ≫ f.hom.hom = 1 → lift (x ≫ f.hom.hom) y ≫ a'.smul = y

/-- Affine space with the coordinates indexed by the chosen root order. -/
abbrev affineChart (k : Type u) [Field k] (n : ℕ) : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (MvPolynomial (Fin n) k)))

/-- Multiplication of the ordered positive root groups gives a common
system of coordinates for all left translates of the open cell. -/
structure RootCellCoordinates where
  roots : RootSubgroupFamily P.torus
  order : List (Root P.torus)
  enumerates : Enumerates order (subgroupRoots P.torus P.positive)
  coordinates : affineChart k order.length ≅ product (fun α => (roots α).val.group.X) order

variable (C : RootCellCoordinates (P := P))

/-- A translated open-cell map lifted to the group. -/
def translatedLift (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    affineChart k C.order.length ⟶ G.val.X :=
  (toUnit _ ≫ g) * (C.coordinates.hom ≫ rootProduct C.roots C.order)

/-- The common coordinates on the translated cells of the right quotient. -/
def translatedChart (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    affineChart k C.order.length ⟶ Q.scheme :=
  translatedLift C g ≫ Q.projection

def HasCellCover : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative), ∃ C : RootCellCoordinates (P := P),
      (∀ g, IsOpenImmersion (translatedChart Q C g).left) ∧
      (∀ y : Q.scheme.left, ∃ g, y ∈ Set.range (translatedChart Q C g).left) ∧
      C.order.length = (subgroupRoots P.torus P.positive).ncard ∧
      topologicalKrullDim Q.scheme.left = C.order.length

/-- The coordinate-power homomorphism of affine-space coordinate rings. -/
def powerMap (q n : ℕ) : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k :=
  MvPolynomial.expand q

abbrev powerMorphism (q n : ℕ) : affineChart k n ⟶ affineChart k n :=
  (testSpec k).map (CommAlgCat.ofHom (powerMap q n)).op

def PowerMapFormula : Prop :=
  ∀ {k : Type u} [Field k] (q n : ℕ),
    (∀ c : k, powerMap q n (MvPolynomial.C c) = MvPolynomial.C c) ∧
    ∀ i : Fin n, powerMap q n (MvPolynomial.X i : MvPolynomial (Fin n) k) =
      MvPolynomial.X i ^ q

/-- The germ of a polynomial on the affine chart. -/
def chartGerm {n : ℕ} (x : (affineChart k n).left) :
    CommRingCat.of (MvPolynomial (Fin n) k) ⟶ (affineChart k n).left.presheaf.stalk x :=
  (Scheme.ΓSpecIso _).inv ≫ (affineChart k n).left.presheaf.germ ⊤ x (by simp)

/-- The same coordinate formula on the local rings of the affine charts. -/
def PowerMapStalkFormula : Prop :=
  ∀ {k : Type u} [Field k] (q n : ℕ) (x : (affineChart k n).left),
    let f := (powerMorphism (k := k) q n).left
    (∀ c : k, f.stalkMap x (chartGerm (f x) (MvPolynomial.C c)) =
      chartGerm x (MvPolynomial.C c)) ∧
    ∀ i : Fin n, f.stalkMap x (chartGerm (f x) (MvPolynomial.X i)) =
      (chartGerm x (MvPolynomial.X i)) ^ q

def HasFrobeniusCellCover : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative),
    1 ≤ r →
    ∃ (F : Q.scheme ⟶ (twist p r).obj Q.scheme) (C : RootCellCoordinates (P := P))
      (e : affineChart k C.order.length ≅ (twist p r).obj (affineChart k C.order.length)),
      IsRelativeFrobenius p r Q.scheme F ∧
      C.order.length = (subgroupRoots P.torus P.positive).ncard ∧
      topologicalKrullDim Q.scheme.left = C.order.length ∧
      (∀ g, IsOpenImmersion (translatedChart Q C g).left ∧
        IsOpenImmersion (e.hom ≫ (twist p r).map (translatedChart Q C g)).left ∧
        (e.hom ≫ (twist p r).map (translatedLift C g)) ≫ (twist p r).map Q.projection =
          e.hom ≫ (twist p r).map (translatedChart Q C g) ∧
        IsPullback (powerMorphism (p ^ r) C.order.length).left (translatedChart Q C g).left
          (e.hom ≫ (twist p r).map (translatedChart Q C g)).left F.left) ∧
      ∀ y : ((twist p r).obj Q.scheme).left,
        ∃ g, y ∈ Set.range (e.hom ≫ (twist p r).map (translatedChart Q C g)).left

/-- A geometric target point has a unique lift over its algebraically closed field. -/
def UniqueGeometricFiberPoint : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (X : SchemeOver k) (F : X ⟶ (twist p r).obj X),
    IsRelativeFrobenius p r X F →
    ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
      (y : Points ((twist p r).obj X) (CommAlgCat.of k K)),
      ∃! x : Points X (CommAlgCat.of k K), x ≫ F = y

/-- A closed point of the target has exactly one rational source point above it. -/
def UniqueClosedFiberPoint : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (F : Q.scheme ⟶ (twist p r).obj Q.scheme),
    IsRelativeFrobenius p r Q.scheme F →
    ∀ y : closedPoints ((twist p r).obj Q.scheme).left,
      ∃! x : 𝟙_ (SchemeOver k) ⟶ Q.scheme,
        F.left (x.left (IsLocalRing.closedPoint k)) = y.val

end Flag
end

end LinearAlgebraicGroups.Specs.FlagRelativeFrobeniusAtlas
