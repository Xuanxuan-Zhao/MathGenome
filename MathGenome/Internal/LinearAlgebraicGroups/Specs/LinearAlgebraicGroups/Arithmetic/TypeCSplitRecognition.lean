import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatum
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.TypeCSplitRecognition

open Pinning (BasedRootDatum BasedIso AttachedDatum SplitBorelPair PinnedGroup PinnedIso)
open SymplecticDatumTorusAndBorel (RootLabel rootVector simpleLabel HyperbolicIndex)
open SymplecticDatum (corootVector)
open SymplecticMatrixStructure (symplecticPoints PointGroup)
open AutomorphismSequence (relativePoints)
open RelativeFormComparison (fieldTest transportedAut IsInduced)
open RootGroups (AdditiveLine)
open GeometricRadicals (IsSemisimple GeometricGroup)
open SimplyConnectedLattice (GeometricallySimplyConnected)

noncomputable section

/-- Coordinates of the simply connected based datum of type C of rank `n + 1`.
Both lattices are the full integral lattices, and the same bijection labels
each root and its coroot. These conditions make sense independently of groups. -/
structure TypeCCoordinates (n : ℕ) (D : BasedRootDatum.{u}) where
  characters : D.X ≃ₗ[ℤ] (Fin (n + 1) → ℤ)
  cocharacters : D.Y ≃ₗ[ℤ] (Fin (n + 1) → ℤ)
  roots : RootLabel (n + 1) ≃ D.I
  pairing : ∀ x y, D.datum.toLinearMap x y =
    ∑ i, characters x i * cocharacters y i
  root : ∀ a, characters (D.datum.root (roots a)) = rootVector a
  coroot : ∀ a, cocharacters (D.datum.coroot (roots a)) = corootVector a
  simple : ∀ a, roots a ∈ D.base.support ↔ ∃ i, a = simpleLabel i

/-- A split presentation of the type C datum over an extension field. -/
def HasAbsoluteTypeC {k S : Type u} [Field k] [Field S] [Algebra k S]
    (n : ℕ) (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (P : SplitBorelPair S) (D : AttachedDatum P),
    Nonempty (TypeCCoordinates n D.toBased) ∧
      Nonempty ((groupBaseChange k S).obj G.val ≅ P.G.val)

/-- Absolute simply connected type C, measured on the actual geometric group.
The full lattices specify the simply connected form. -/
def HasGeometricTypeC {k : Type u} [Field k]
    (n : ℕ) (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (P : SplitBorelPair (AlgebraicClosure k)) (D : AttachedDatum P),
    P.G = GeometricGroup G ∧ Nonempty (TypeCCoordinates n D.toBased)

/-- The Cartan matrix of type C of rank `n + 1`, with coroots indexing the
rows and the long simple root at the last vertex. Rank one has the entry 2. -/
def cartanEntry (n : ℕ) (i j : Fin (n + 1)) : ℤ :=
  if j = i then 2 else
    if j.val + 1 = i.val ∨ i.val + 1 = j.val then
      (if j.val = n then -2 else -1)
    else 0

/-- The type of the actual absolute simple roots, expressed by their
Cartan entries. -/
def HasGeometricCartanTypeC {k : Type u} [Field k]
    (n : ℕ) (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (P : SplitBorelPair (AlgebraicClosure k)) (D : AttachedDatum P),
    P.G = GeometricGroup G ∧
    ∃ s : Fin (n + 1) ≃ ↥D.toBased.base.support, ∀ i j,
      D.toBased.datum.pairing (s j).val (s i).val = cartanEntry n i j

/-- Simple connectedness and the absolute Cartan type give the full
geometric character and cocharacter coordinates. -/
def GeometricTypeCFromCartan : Prop :=
  ∀ {k : Type u} [Field k] (n : ℕ) (G : AffineAlgebraicGroup k),
    IsSemisimple G → GeometricallySimplyConnected G →
    HasGeometricCartanTypeC n G → HasGeometricTypeC n G

/-- A reductive group admits a split Borel pair over a separable closure. -/
def SeparableBorelPair : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k), GeometricRadicals.IsReductive G →
    ∃ P : SplitBorelPair S, P.G = Unipotent.baseChangedAlgebraicGroup S G

/-- Applicability of the separable splitting construction to the geometric datum. -/
def GeometricApplicability : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (n : ℕ) (G : AffineAlgebraicGroup k), HasGeometricTypeC n G →
    HasAbsoluteTypeC (S := S) n G

def BasedRigidity : Prop :=
  ∀ (n : ℕ) (D : BasedRootDatum.{u}), TypeCCoordinates n D → ∀ d : Aut D, d = 1

/-- The split comparison is a pinned lift of the prescribed identification
on the full character and cocharacter lattices and all root labels. -/
def PinnedRecognition : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (n : ℕ) (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair)
    (x : TypeCCoordinates n D.toBased) (y : TypeCCoordinates n E.toBased),
    ∃ (e : BasedIso D.toBased E.toBased) (f : PinnedIso P Q),
      (∀ χ, e.val.weightEquiv χ = y.characters.symm (x.characters χ)) ∧
      (∀ y₀, e.val.coweightEquiv y₀ = x.cocharacters.symm (y.cocharacters y₀)) ∧
      (∀ a, e.val.indexEquiv (x.roots a) = y.roots a) ∧
      (∀ χ : CharacterDescent.Character P.pair.T.group,
        e.val.weightEquiv (Additive.ofMul χ) =
          Additive.ofMul (Pinning.transportCharacter f.torus χ)) ∧
      ∀ y₀ : CharacterDescent.Cocharacter Q.pair.T.group,
        e.val.coweightEquiv (Additive.ofMul y₀) = Additive.ofMul (y₀ ≫ f.torus.inv)

def FiniteSplitRecognition : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (n : ℕ) (G H : AffineAlgebraicGroup k)
    (_c : (groupPointsFunctor k).obj H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))),
    HasAbsoluteTypeC (S := S) n G →
    ∃ L : FiniteGaloisIntermediateField k S,
      Nonempty ((groupBaseChange k L).obj H.val ≅ (groupBaseChange k L).obj G.val)

open LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle pointAction)
open SymplecticDatum (MatrixAlgebra adjoint conjugateMatrix)
open SymplecticDatumAdjointDescent (GroupPoints ScalarCentre)
open SymplecticMatrixStructure (mapSymplecticPoint)
open SchemeDerivedGroup (RepresentsQuotient)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A test algebra over the splitting field as an object of the big slice. -/
abbrev sliceTest (R : TestAlgebra K) : Over (fieldTest k K) :=
  Over.mk ((testSpec k).map
    (CommAlgCat.ofHom ({ toRingHom := algebraMap K R, commutes' := fun _ => rfl } :
      K →ₐ[k] (restrictTestAlgebra k K).obj R)).op)

/-- The adjoint cocycle comes from the chosen split comparison itself. Its
matrix action and its effect on symplectic points are recorded over every
test algebra of the splitting field. -/
structure MatrixTwisting (n : ℕ) (G H : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1)))
    (f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val) where
  comparison : relativePoints H.val (fieldTest k K) ≅ relativePoints G.val (fieldTest k K)
  induced : IsInduced k K f comparison
  centre : ClosedSubgroup H.val
  isCentre : CentralTorus.IsSchemeCentre centre
  scalar : ScalarCentre c centre
  quotient : AffineAlgebraicGroup k
  projection : H.val ⟶ quotient.val
  kernel : IsSchemeKernel projection centre
  represents : RepresentsQuotient centre projection
  cocycle : @Cocycle (Gal(K/k)) (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points
    k K quotient.val.X) _ (krullTopology k K) _ ⊥ (pointAction k K quotient.val.X)
  action : ∀ R : TestAlgebra k, GroupPoints quotient.val R →*
    (MatrixAlgebra (HyperbolicIndex.{u} (n + 1)) R ≃ₐ[R]
      MatrixAlgebra (HyperbolicIndex.{u} (n + 1)) R)
  preservesAdjoint : ∀ (R : TestAlgebra k) (a : GroupPoints quotient.val R) X,
    action R a (adjoint X) = adjoint (action R a X)
  naturality : ∀ (R S : TestAlgebra k) (b : R ⟶ S) (a : GroupPoints quotient.val R) X,
    (action R a X).map b.hom = action S (((groupPointsFunctor k).obj quotient.val).map b a)
      (X.map b.hom)
  onLift : ∀ (R : TestAlgebra k) (g : GroupPoints H.val R) X,
    action R (((groupPointsFunctor k).map projection).app R g) X =
      conjugateMatrix (c.hom.app R g) X
  onTestAlgebra : ∀ (σ : Gal(K/k)) (R : TestAlgebra K)
    (g : GroupPoints H.val ((restrictTestAlgebra k K).obj R)),
    let R₀ := (restrictTestAlgebra k K).obj R
    let a : GroupPoints quotient.val R₀ := (sliceTest (k := k) R).hom ≫ cocycle σ
    let h := ((transportedAut k K comparison σ).asIso.hom.app
      (op (sliceTest (k := k) R))).hom g
    (show PointGroup (HyperbolicIndex.{u} (n + 1)) R₀ from c.hom.app R₀ h).val =
      action R₀ a (show PointGroup (HyperbolicIndex.{u} (n + 1)) R₀ from c.hom.app R₀ g).val

/-- The inner cocycle is attached to any specified finite Galois trivialization. -/
def TwistingForTrivialization : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (n : ℕ) (G H : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1)))
    (f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val),
    Nonempty (MatrixTwisting n G H c f)

/-- The comparison and inner cocycle at one finite Galois splitting level,
using the represented matrix group and the fppf quotient by its scalar μ₂. -/
def FiniteMatrixRecognition {k S : Type u} [Field k] [Field S] [Algebra k S]
    (n : ℕ) (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (H : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1)))
    (L : FiniteGaloisIntermediateField k S)
    (f : (groupBaseChange k L).obj H.val ≅ (groupBaseChange k L).obj G.val),
    Nonempty (MatrixTwisting n G H c f)

def Statement : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (n : ℕ) (G : AffineAlgebraicGroup k), HasGeometricTypeC n G →
    FiniteMatrixRecognition (S := S) n G

def StatementFromCartan : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (n : ℕ) (G : AffineAlgebraicGroup k), IsSemisimple G →
    GeometricallySimplyConnected G → HasGeometricCartanTypeC n G →
    FiniteMatrixRecognition (S := S) n G

end

end LinearAlgebraicGroups.Specs.TypeCSplitRecognition
