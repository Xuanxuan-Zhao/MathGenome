import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.PeirceFrames
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitApproximation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.OrthogonalDoubling
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeFormComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm

namespace LinearAlgebraicGroups.Specs.OctonionForms

open _root_.LinearAlgebraicGroups.Composition Composition.Specification Composition.PeirceSpecification
open Arithmetic.LocalDivisionAlgebras
open RM03.CSA

universe u v w

/-- The reduced norm on a quaternion division algebra over a
nonarchimedean local field maps units onto units. -/
def LocalQuaternionNormSurjective : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : IsCentralSimple F B), degree F B = 2 →
    ∀ c : F, c ≠ 0 → ∃ x : Bˣ, reducedNorm hB (x : B) = c

/-- The reduced norm of a split quaternion algebra is surjective on units. -/
def SplitQuaternionNormSurjective : Prop :=
  ∀ {F : Type u} [Field F] {B : Type v} [Ring B] [Algebra F B]
    (hB : IsCentralSimple F B), degree F B = 2 →
    Nonempty (B ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) →
    ∀ c : F, c ≠ 0 → ∃ x : Bˣ, reducedNorm hB (x : B) = c

/-- An octonion algebra with its regular composition norm over an
algebraically closed field has a norm-preserving Zorn presentation. -/
def AlgebraicallyClosedSplit : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {C : Type v} [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C]
    {n : QuadraticForm k C}, OctonionNormConditions n → Nonempty (ZornIsomorphism n)

/-- The octonion algebra at a complex place is split. -/
def ComplexSplit : Prop :=
  ∀ {C : Type v} [NonAssocRing C] [Module ℂ C]
    [IsScalarTower ℂ C C] [SMulCommClass ℂ C C] {n : QuadraticForm ℂ C},
    OctonionNormConditions n → Nonempty (ZornIsomorphism n)

/-- Over the real field, the regular octonion norm is either split or positive definite. -/
def RealSplitOrPositive : Prop :=
  ∀ {C : Type v} [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C]
    [SMulCommClass ℝ C C] {n : QuadraticForm ℝ C},
    OctonionNormConditions n →
      Nonempty (ZornIsomorphism n) ∨ ∀ x : C, x ≠ 0 → 0 < n x

/-- Every octonion algebra over a nonarchimedean local field is split,
including in residue and field characteristic two. -/
def NonarchimedeanSplit : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {C : Type v} [NonAssocRing C] [Module F C]
    [IsScalarTower F C C] [SMulCommClass F C C]
    {n : QuadraticForm F C}, OctonionNormConditions n → Nonempty (ZornIsomorphism n)

/-- The Euclidean structure of a positive definite real composition norm. -/
@[instance_reducible] noncomputable def realNormCore {C : Type v} [AddCommGroup C] [Module ℝ C]
    (n : QuadraticForm ℝ C) (hp : ∀ x : C, x ≠ 0 → 0 < n x) :
    InnerProductSpace.Core ℝ C where
  inner x y := n.associated x y
  conj_inner_symm x y := by simpa using (QuadraticMap.associated_isSymm ℝ n y x)
  re_inner_nonneg x := by
    change 0 ≤ n.associated x x
    rw [show n.associated x x = n x from QuadraticMap.associated_eq_self_apply ℝ n x]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (hp x hx).le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x h := by
    change n.associated x x = 0 at h
    rw [show n.associated x x = n x from QuadraticMap.associated_eq_self_apply ℝ n x] at h
    by_contra hx
    exact (hp x hx).ne' h

/-- The matrix columns of the real linear automorphisms preserving the octonion
product and unit. The topology on the columns is the Euclidean topology. -/
def realAutomorphismColumns {C : Type v} [NonAssocRing C] [Module ℝ C]
    (b : Module.Basis (Fin 8) ℝ C) : Set (Fin 8 → C) :=
  {a | ∃ f : C ≃ₗ[ℝ] C,
    (∀ i, f (b i) = a i) ∧ f 1 = 1 ∧
    ∀ x y, f (x * y) = f x * f y}

/-- Compactness for the real points of the positive definite octonion
automorphism group, in the topology of its faithful matrix representation. -/
def RealCompact : Prop :=
  ∀ {C : Type v} [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C]
    [SMulCommClass ℝ C C] {n : QuadraticForm ℝ C},
    OctonionNormConditions n →
    ∀ (hp : ∀ x : C, x ≠ 0 → 0 < n x) (b : Module.Basis (Fin 8) ℝ C),
      letI := (realNormCore n hp).toNormedAddCommGroup
      IsCompact (realAutomorphismColumns b)

/-- Connectedness in the same real topology. -/
def RealConnected : Prop :=
  ∀ {C : Type v} [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C]
    [SMulCommClass ℝ C C] {n : QuadraticForm ℝ C},
    OctonionNormConditions n →
    ∀ (hp : ∀ x : C, x ≠ 0 → 0 < n x) (b : Module.Basis (Fin 8) ℝ C),
      letI := (realNormCore n hp).toNormedAddCommGroup
      IsConnected (realAutomorphismColumns b)

/-- The finite completions of either kind of global field split every octonion. -/
def FiniteCompletionSplit : Prop :=
  ∀ {k : Type u} [Field k] (D : Arithmetic.GlobalFieldData.{u,w} k) (v₀ : D.FinitePlace)
    {C : Type v} [NonAssocRing C] [Module (D.FiniteCompletion v₀) C]
    [IsScalarTower (D.FiniteCompletion v₀) C C] [SMulCommClass (D.FiniteCompletion v₀) C C]
    {n : QuadraticForm (D.FiniteCompletion v₀) C},
    OctonionNormConditions n → Nonempty (ZornIsomorphism n)

section Groups

open AlgebraicGeometry CategoryTheory
open Composition.OctonionAutomorphismSpecification
open Composition.ZornSpecification (norm)
open CharacterDescent (Cocharacter)
open GeometricRadicals (GeometricGroup IsReductive IsSemisimple IsSplitReductive)
open Pinning (AttachedDatum BasedRootDatum SplitBorelPair)
open AdjointRepresentation (GroupPoints)
open RelativeRank (relativeRank)
open Arithmetic.AdelicGroups
open IntegralModels (MatrixRealization)
open Unipotent (baseChangedAlgebraicGroup)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open scoped TensorProduct

/-- The type `G₂` Cartan matrix with rows indexed by coroots and the short root first. -/
def g2CartanMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -3; -1, 2]

/-- The Cartan matrix of the actual simple roots and attached coroots has type `G₂`. -/
def HasG2Cartan (D : BasedRootDatum.{u}) : Prop :=
  ∃ e : Fin 2 ≃ D.base.support,
    ∀ i j, D.datum.pairing (e j).val (e i).val = g2CartanMatrix i j

/-- Absolute type `G₂` for a semisimple group, read from a Borel pair of its
geometric group. -/
def IsAbsoluteG2 {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  IsSemisimple G ∧ ∃ P : SplitBorelPair (AlgebraicClosure k),
    P.G = GeometricGroup G ∧ ∃ D : AttachedDatum P, HasG2Cartan D.toBased

/-- A form of the split type-`G₂` scheme, using the split Zorn octonion model
and an isomorphism over the separable closure. -/
def IsG2Form {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  ∃ A : AutomorphismGroup k (Zorn k),
    Nonempty ((groupBaseChange k (SeparableClosure k)).obj G.val ≅
      (groupBaseChange k (SeparableClosure k)).obj A.group)

/-- Every semisimple group of absolute type `G₂` is isomorphic to the split
octonion automorphism group after separable scalar extension. -/
def AbsoluteG2IsForm : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsAbsoluteG2 G → IsG2Form G

/-- A rational nontrivial split cocharacter, evaluated on algebra-valued
points so that finite ground fields are included. -/
def HasNontrivialSplitCocharacter {k : Type u} [Field k] (G : GroupScheme k) : Prop :=
  ∃ c : Cocharacter G,
    ∃ (S : CommAlgCat.{u} k) (t : GroupPoints _ S),
      ((groupPointsFunctor k).map c).app S t ≠ 1

/-- Every form of the split octonion automorphism scheme is represented
by the automorphisms of an octonion algebra with its descended norm. -/
def G2OctonionDescentOfForm : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsG2Form G →
    ∃ (C : Type u) (_ringC : NonAssocRing C) (_moduleC : Module k C)
      (_towerC : IsScalarTower k C C) (_commC : SMulCommClass k C C)
      (n : QuadraticForm k C),
      OctonionNormConditions n ∧ ∃ A : AutomorphismGroup k C, Nonempty (G.val ≅ A.group)

/-- A semisimple group of absolute type `G₂` is the automorphism scheme of
an octonion algebra with its descended regular norm. -/
def G2OctonionDescent : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsAbsoluteG2 G →
    ∃ (C : Type u) (_ringC : NonAssocRing C) (_moduleC : Module k C)
      (_towerC : IsScalarTower k C C) (_commC : SMulCommClass k C C)
      (n : QuadraticForm k C),
      OctonionNormConditions n ∧ ∃ A : AutomorphismGroup k C, Nonempty (G.val ≅ A.group)

/-- The group scheme of type `G₂` splits at every finite place of a global field. -/
def FiniteCompletionG2Split : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsAbsoluteG2 G →
    ∀ (D : Arithmetic.GlobalFieldData.{u,w} k) (p : D.FinitePlace),
      letI : Algebra k (D.FiniteCompletion p) := (D.embedding (.inl p)).toAlgebra
      IsSplitReductive (baseChangedAlgebraicGroup (D.FiniteCompletion p) G)

/-- The group scheme of type `G₂` splits at every complex place of a number field. -/
def ComplexCompletionG2Split : Prop :=
  ∀ {k : Type u} [Field k] [NumberField k] (G : AffineAlgebraicGroup k), IsAbsoluteG2 G →
    ∀ (p : NumberField.InfinitePlace k), p.IsComplex →
      IsSplitReductive (baseChangedAlgebraicGroup p.Completion G)

/-- Over the real field a group of type `G₂` is split or has a positive definite
octonion model whose real points are compact and connected in matrix coordinates. -/
def RealG2SplitOrCompactConnected : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ), IsAbsoluteG2 G →
    IsSplitReductive G ∨
      ∃ (C : Type) (_ringC : NonAssocRing C) (_moduleC : Module ℝ C)
        (_towerC : IsScalarTower ℝ C C) (_commC : SMulCommClass ℝ C C)
        (n : QuadraticForm ℝ C) (_hn : OctonionNormConditions n)
        (hp : ∀ x : C, x ≠ 0 → 0 < n x),
        (∃ A : AutomorphismGroup ℝ C, Nonempty (G.val ≅ A.group)) ∧
          ∀ b : Module.Basis (Fin 8) ℝ C,
            letI := (realNormCore n hp).toNormedAddCommGroup
            IsCompact (realAutomorphismColumns b) ∧ IsConnected (realAutomorphismColumns b)

/-- The nontrivial weight argument on the rational representation of the
split one-dimensional torus. Norm preservation is tested at its universal point. -/
def NontrivialNormCoactionSplit : Prop :=
  ∀ {k : Type u} [Field k] {C : Type u} [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {n : QuadraticForm k C}
    (hn : OctonionNormConditions n),
    let A := groupAlgebra k IntegerCharacters
    letI := hn.projective
    ∀ ρ : RightComodule k A C,
      ρ.coaction ≠ LinearAlgebraicGroups.RationalRepresentations.trivialLinearMap A →
      (∀ x : C, normBaseChange A n ((TensorProduct.comm k C A) (ρ.coaction x)) =
        algebraMap k A (n x)) →
      Nonempty (ZornIsomorphism n)

/-- A nontrivial split cocharacter acts on the octonions with a nonzero
weight, so the norm is isotropic and the algebra has a Zorn presentation. -/
def OctonionSplitOfCocharacter : Prop :=
  ∀ {k C : Type u} [Field k] [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {n : QuadraticForm k C},
    OctonionNormConditions n → ∀ A : AutomorphismGroup k C,
      HasNontrivialSplitCocharacter A.group → Nonempty (ZornIsomorphism n)

/-- An isotropic form of type `G₂` splits over its ground field. -/
def IsotropicG2Split : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsAbsoluteG2 G → 0 < relativeRank G → IsSplitReductive G

/-- Strong approximation outside every finite nonempty set of places
for globally isotropic forms of the split group of type `G₂`. -/
def IsotropicG2StrongApproximation : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsAbsoluteG2 G →
    0 < relativeRank G →
    ∀ (D : Arithmetic.GlobalFieldData.{u,w} k) (i : MatrixRealization G) (S : Finset D.Place),
      S.Nonempty → StrongApproximation D i S

end Groups

section Descent

open AlgebraicGeometry CategoryTheory
open AutomorphismSequence (relativePoints RelativeAut innerAut)
open RelativeFormComparison (fieldTest transportedAut)
open Composition.OctonionAutomorphismSpecification
open GeometricRadicals (IsReductive IsSemisimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open scoped TensorProduct

/-- The split octonion automorphism group has the adjoint root datum of type G₂
and is geometrically simply connected. -/
def SplitOctonionGroupStructure : Prop :=
  ∀ {k : Type u} [Field k] {C : Type v} [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {n : QuadraticForm k C},
    OctonionNormConditions n → Nonempty (ZornIsomorphism n) →
    ∀ A : AutomorphismGroup k C,
      let G : AffineAlgebraicGroup k :=
        ⟨A.group, A.groupAffine, A.groupFiniteType, A.groupQuasiCompact⟩
      IsAdjointG2 G ∧ GeometricallySimplyConnected G

/-- A separable form admits a finite Galois trivialization with a unique
conjugating point for each Galois displacement. -/
def FiniteG2InnerTrivialization : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsG2Form G →
    ∃ (A : AutomorphismGroup k (Zorn k)) (K : Type u) (_ : Field K)
      (_ : Algebra k K) (_ : FiniteDimensional k K) (_ : IsGalois k K)
      (i : relativePoints A.group (fieldTest k K) ≅ relativePoints G.val (fieldTest k K)),
        ∀ σ : Gal(K/k), ∃! g : fieldTest k K ⟶ A.group.X,
          innerAut g = transportedAut k K i σ

/-- Effective descent of an octonion algebra with a semilinear action preserving
its unit and multiplication and carrying the norm by the Galois action. -/
def FiniteOctonionScalarDescent : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] {V : Type w} [NonAssocRing V]
    [Module K V] [Module k V] [IsScalarTower k K V]
    [IsScalarTower K V V] [SMulCommClass K V V] [IsScalarTower k V V] [SMulCommClass k V V]
    {n : QuadraticForm K V}, OctonionNormConditions n →
    ∀ ρ : SemilinearAction k K V,
    (∀ σ, ρ.act σ 1 = 1) →
    (∀ σ x y, ρ.act σ (x * y) = ρ.act σ x * ρ.act σ y) →
    (∀ σ x, n (ρ.act σ x) = σ (n x)) →
      ∃ (D : UnitalSubalgebra k V) (q : QuadraticForm k D) (hq : OctonionNormConditions q),
        D.toSubmodule = ρ.fixed ∧
          letI := hq.projective
          ∃ e : (K ⊗[k] D) ≃ₗ[K] V,
            (∀ s x, e (s ⊗ₜ[k] x) = s • (x : V)) ∧ e 1 = 1 ∧
            (∀ x y, e (x * y) = e x * e y) ∧
            ∀ x, n (e x) = normBaseChange K q x

end Descent

end LinearAlgebraicGroups.Specs.OctonionForms
