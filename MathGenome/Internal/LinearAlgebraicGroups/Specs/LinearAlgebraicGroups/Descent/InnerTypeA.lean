import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.MatrixAlgebraForms
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.NormOneGroup

open AlgebraicGeometry CategoryTheory
open scoped MatrixGroups TensorProduct

universe u w

namespace LinearAlgebraicGroups.Descent.InnerTypeA.Specification

noncomputable section

open _root_.Specs.RM03.CSA (isCentralSimple degree genericReducedNorm reducedNorm)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open _root_.RM03.Brauer.ProjectiveClassification (Cocycle IsTransport Implements)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)
open LinearAlgebraicGroups.Specs.StandardGroups
open Matrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {A : Type u} [Ring A] [Algebra k A]
variable {ι : Type u} [Fintype ι]

/-- The determinant-one equation in the coordinates of the chosen basis. -/
def normOneIdeal (hA : isCentralSimple k A) (b : Module.Basis ι k A) :
    Ideal (MvPolynomial ι k) :=
  Ideal.span {genericReducedNorm hA b - 1}

abbrev NormOneCoordinates (hA : isCentralSimple k A) (b : Module.Basis ι k A) :=
  MvPolynomial ι k ⧸ normOneIdeal hA b

/-- The coordinates on the open subspace of invertible elements. -/
abbrev UnitCoordinates (hA : isCentralSimple k A) (b : Module.Basis ι k A) :=
  Localization.Away (genericReducedNorm hA b)

/-- The polynomial norm commutes with scalar extension, becomes determinant in
a splitting and is multiplicative over arbitrary commutative test algebras. -/
def ReducedNormComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : Type u} [Ring A] [Algebra k A] {ι : Type u} [Fintype ι]
    (hA : isCentralSimple k A) (b : Module.Basis ι k A)
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K),
    (∀ hK : isCentralSimple K (K ⊗[k] A),
      genericReducedNorm hK (b.baseChange K) =
        MvPolynomial.map (algebraMap k K) (genericReducedNorm hA b)) ∧
    MvPolynomial.map (algebraMap k K) (genericReducedNorm hA b) =
        (_root_.Specs.RM03.CSA.genericMatrix fun i => s (1 ⊗ₜ[k] b i)).det ∧
    (∀ x y : A, reducedNorm hA (x * y) = reducedNorm hA x * reducedNorm hA y) ∧
    (∀ a : A, normAt hA b ((1 : k) ⊗ₜ[k] a) = reducedNorm hA a) ∧
    (∀ (R : TestAlgebra k) (x y : R ⊗[k] A), normAt hA b (1 : R ⊗[k] A) = 1 ∧
      normAt hA b (x * y) = normAt hA b x * normAt hA b y) ∧
    (∀ (R S : TestAlgebra k) (f : R ⟶ S) (x : R ⊗[k] A),
      normAt hA b (Algebra.TensorProduct.map f.hom (.id k A) x : S ⊗[k] A) =
        f.hom (normAt hA b x))

/-- Scheme coordinates on the norm-one group, with their actual evaluation at
a point and with multiplication computed in the scalar extension of the algebra. -/
def NormOneModel (hA : isCentralSimple k A) (b : Module.Basis ι k A) : Prop :=
  ∃ H : HopfOperations k (NormOneCoordinates hA b),
    letI := H.hopf
    ∃ F : TestAlgebra k ⥤ GrpCat.{u},
      ∃ point : ∀ R : TestAlgebra k, F.obj R ≃ {x : R ⊗[k] A // normAt hA b x = 1},
        (∀ R, (point R 1).1 = 1) ∧
        (∀ R (x y : F.obj R), (point R (x * y)).1 = (point R x).1 * (point R y).1) ∧
        (∀ {R S : TestAlgebra k} (f : R ⟶ S) (x : F.obj R),
          (point S (F.map f x)).1 = Algebra.TensorProduct.map f.hom (.id k A) (point R x).1) ∧
        Represents (NormOneCoordinates hA b) F (fun R f x =>
          ∀ i, (b.baseChange R).repr (point R x).1 i =
            f (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X i)))

def NormOneRepresentability : Prop :=
  ∀ {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
    {ι : Type u} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A),
    NormOneModel hA b

/-- Natural points of the invertible locus, with evaluations in the original
algebra coordinates. -/
def UnitGroupModel (hA : isCentralSimple k A) (b : Module.Basis ι k A) : Prop :=
  ∃ H : HopfOperations k (UnitCoordinates hA b),
    letI := H.hopf
    ∃ F : TestAlgebra k ⥤ GrpCat.{u},
      ∃ point : ∀ R : TestAlgebra k, F.obj R ≃* (R ⊗[k] A)ˣ,
        (∀ {R S : TestAlgebra k} (f : R ⟶ S) (x : F.obj R),
          point S (F.map f x) =
            Units.map (Algebra.TensorProduct.map f.hom (.id k A)).toMonoidHom (point R x)) ∧
        Represents (UnitCoordinates hA b) F (fun R f x =>
          ∀ i, (b.baseChange R).repr (point R x).val i =
            f (algebraMap (MvPolynomial ι k) (UnitCoordinates hA b) (MvPolynomial.X i)))

def UnitGroupRepresentability : Prop :=
  ∀ {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
    {ι : Type u} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A),
    UnitGroupModel hA b

/-- The adjoint group represents the fppf quotient of the units by the central
scalar torus, with the scalar embedding specified on every test algebra. -/
def ProjectiveModel : Prop :=
  ∀ {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
    {ι : Type u} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A),
    ∃ (J : HopfOperations k (UnitCoordinates hA b)) (H : HopfOperations k (LaurentPolynomial k)),
      let U := @spectrum k _ (UnitCoordinates hA b) _ J.hopf inferInstance
      let M := @spectrum k _ (LaurentPolynomial k) _ H.hopf inferInstance
      ∃ (F : TestAlgebra k ⥤ GrpCat.{u})
        (point : ∀ R : TestAlgebra k, F.obj R ≃* (R ⊗[k] A)ˣ)
        (e : (groupPointsFunctor k).obj U.val ≅ F)
        (m : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
        (i : M.val ⟶ U.val) (hi : IsClosedImmersion i.hom.hom.left),
        (∀ {R S : TestAlgebra k} (a : R ⟶ S) (x : F.obj R),
          point S (F.map a x) =
            Units.map (Algebra.TensorProduct.map a.hom (.id k A)).toMonoidHom (point R x)) ∧
        (∀ (R : TestAlgebra k) (f : UnitCoordinates hA b →ₐ[k] R)
          (p : Points U.val.X R), p.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
          ∀ j, (b.baseChange R).repr (point R (e.hom.app R p)).val j =
            f (algebraMap (MvPolynomial ι k) (UnitCoordinates hA b) (MvPolynomial.X j))) ∧
        (∀ (R : TestAlgebra k) (a : Points M.val.X R),
          point R (e.hom.app R (a ≫ i.hom.hom)) =
            Units.map (algebraMap R (R ⊗[k] A)).toMonoidHom (m.hom.app R a)) ∧
        Specs.IsNormalSubgroup i ∧
        let B : Specs.ClosedSubgroup U.val := ⟨M.val, i, hi⟩
        ∃ (Q : Specs.AffineAlgebraicGroup k) (q : U.val ⟶ Q.val),
          Specs.IsSchemeKernel q B ∧
          ∃ eq : Specs.rightQuotientSheaf B ≅ Specs.schemeFppfSheaf Q.val.X,
            Specs.rightQuotientProjection B ≫ eq.hom =
              (Specs.fppfOver k).uliftYoneda.map q.hom.hom

/-- A matrix comparison intertwines every semilinear change of test algebra
with entrywise change followed by conjugation by the specified cocycle. -/
def IsCocycleComparison {n : ℕ}
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (d : ∀ R : TestAlgebra K,
      (restrictTestAlgebraObj k K R ⊗[k] A) ≃ₐ[R] Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ [FiniteDimensional k K] [IsGalois k K]
    (ρ : AlgebraAction k K (Matrix (Fin n) (Fin n) K)) (c : Cocycle k K n),
    IsTransport ρ s → Implements ρ c →
    ∀ {R S : TestAlgebra K} (σ : Gal(K/k)) (G : GL (Fin n) K),
      ProjGenLinGroup.mk G = c.val σ →
      ∀ (f : restrictTestAlgebraObj k K R ⟶ restrictTestAlgebraObj k K S),
        (∀ a : K, f.hom (algebraMap K R a) = algebraMap K S (σ a)) →
        ∀ x : restrictTestAlgebraObj k K R ⊗[k] A,
          d S (Algebra.TensorProduct.map f.hom (.id k A) x) =
            ((G : Matrix (Fin n) (Fin n) K).map (algebraMap K S)) *
              (d R x).map f.hom *
            ((↑G⁻¹ : Matrix (Fin n) (Fin n) K).map (algebraMap K S))

def CocycleOnTestAlgebras : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ}
    {A : Type u} [Ring A] [Algebra k A]
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (d : ∀ R : TestAlgebra K,
      (restrictTestAlgebraObj k K R ⊗[k] A) ≃ₐ[R] Matrix (Fin n) (Fin n) R),
    (∀ (R : TestAlgebra K) (r : R) (a : A),
      d R (r ⊗ₜ[k] a) = r • (s (1 ⊗ₜ[k] a)).map (algebraMap K R)) →
    IsCocycleComparison s d

/-- The norm-one scheme, after base change to any splitting field, identifies
with the split special linear group through the given matrix coordinates. -/
def SpecialLinearSplitting : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : Type u} [Ring A] [Algebra k A] {ι : Type u} [Fintype ι]
    (hA : isCentralSimple k A) (b : Module.Basis ι k A)
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K),
    let I := ULift.{u} (Fin (degree k A))
    ∃ (H : HopfOperations k (NormOneCoordinates hA b))
      (J : HopfOperations K (SLCoordinates K I)),
      let G := @spectrum k _ (NormOneCoordinates hA b) _ H.hopf inferInstance
      let L := @spectrum K _ (SLCoordinates K I) _ J.hopf inferInstance
      ∃ (F : TestAlgebra k ⥤ GrpCat.{u})
        (point : ∀ R : TestAlgebra k, F.obj R ≃ {x : R ⊗[k] A // normAt hA b x = 1})
        (e : (groupPointsFunctor k).obj G.val ≅ F)
        (z : (groupPointsFunctor K).obj L.val ≅ specialLinearPoints K I)
        (j : (groupBaseChange k K).obj G.val ≅ L.val)
        (d : ∀ R : TestAlgebra K,
          (restrictTestAlgebraObj k K R ⊗[k] A) ≃ₐ[R]
            Matrix (Fin (degree k A)) (Fin (degree k A)) R),
        (∀ (R : TestAlgebra K) (r : R) (a : A),
          d R (r ⊗ₜ[k] a) = r • (s (1 ⊗ₜ[k] a)).map (algebraMap K R)) ∧
        IsCocycleComparison s d ∧
        (∀ {R S : TestAlgebra k} (f : R ⟶ S) (x : F.obj R),
          (point S (F.map f x)).1 =
            Algebra.TensorProduct.map f.hom (.id k A) (point R x).1) ∧
        (∀ (R : TestAlgebra k) (f : NormOneCoordinates hA b →ₐ[k] R)
          (p : Points G.val.X R), p.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
          ∀ i, (b.baseChange R).repr (point R (e.hom.app R p)).1 i =
            f (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X i))) ∧
        ∀ (R : TestAlgebra K) (p : Points ((groupBaseChange k K).obj G.val).X R) (i j₀ : I),
          (show Matrix.SpecialLinearGroup I R from z.hom.app R (p ≫ j.hom.hom.hom)).val i j₀ =
            d R (point (restrictTestAlgebraObj k K R)
              (e.hom.app _ (baseChangePoint k K G.val.X R p))).1 i.down j₀.down

/-- The section of the projective quotient defined by an invertible matrix. -/
def projectiveMatrixPoint {n : ℕ} (P : MatrixAlgebraForms.ProjectivePresentation k n)
    (R : TestAlgebra k) (g : GL (Fin n) R) : Points P.projectiveGroup.val.X R :=
  P.linearPoints.inv.app R (MatrixAlgebraForms.liftMatrix g) ≫ P.projection.hom.hom

abbrev restrictedGroupPoints (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : Specs.GroupScheme k) : TestAlgebra K ⥤ GrpCat.{u} :=
  restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj G

open scoped CategoryTheory.MonObj in
/-- The comparison intertwines coefficient change on the descended group
with coefficient change followed by the projective conjugation on the split
group. The equation applies to all test-algebra sections of the quotient. -/
def IsProjectiveCocycleComparison {n : ℕ}
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (Q : Specs.GroupScheme k) (P : MatrixAlgebraForms.ProjectivePresentation k n)
    (e : restrictedGroupPoints k K Q ≅ restrictedGroupPoints k K P.projectiveGroup.val) : Prop :=
  ∀ [FiniteDimensional k K] [IsGalois k K]
    (ρ : AlgebraAction k K (Matrix (Fin n) (Fin n) K)) (c : Cocycle k K n),
    IsTransport ρ s → Implements ρ c →
    ∀ {R S : TestAlgebra K} (σ : Gal(K/k)) (G : GL (Fin n) K),
      ProjGenLinGroup.mk G = c.val σ →
      ∀ (f : restrictTestAlgebraObj k K R ⟶ restrictTestAlgebraObj k K S),
        (∀ a : K, f.hom (algebraMap K R a) = algebraMap K S (σ a)) →
        ∀ p : Points Q.X (restrictTestAlgebraObj k K R),
          let g := projectiveMatrixPoint P (restrictTestAlgebraObj k K S)
            (Units.map (algebraMap K S).mapMatrix.toMonoidHom G)
          e.hom.app S (mapPoints f p) = g * mapPoints f (e.hom.app R p) * g⁻¹

/-- At a splitting the projective quotient is the scalar extension of the
split projective linear group. Its comparison is induced by the splitting on
units, and it transports the Galois datum via the given projective cocycle. -/
def ProjectiveSplitting : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : Type u} [Ring A] [Algebra k A] {ι : Type u} [Fintype ι]
    (hA : isCentralSimple k A) (b : Module.Basis ι k A)
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K),
    let n := degree k A
    ∃ (J : HopfOperations k (UnitCoordinates hA b))
      (H : Specs.GroupScheme k),
      let U := @spectrum k _ (UnitCoordinates hA b) _ J.hopf inferInstance
      ∃ (F : TestAlgebra k ⥤ GrpCat.{u})
        (point : ∀ R : TestAlgebra k, F.obj R ≃* (R ⊗[k] A)ˣ)
        (e : (groupPointsFunctor k).obj U.val ≅ F)
        (m : (groupPointsFunctor k).obj H ≅ multiplicativePoints k)
        (i : H ⟶ U.val) (hi : IsClosedImmersion i.hom.hom.left)
        (Q : Specs.AffineAlgebraicGroup k) (q : U.val ⟶ Q.val)
        (P : MatrixAlgebraForms.ProjectivePresentation k n)
        (j : (groupBaseChange k K).obj Q.val ≅ (groupBaseChange k K).obj P.projectiveGroup.val)
        (z : restrictedGroupPoints k K Q.val ≅ restrictedGroupPoints k K P.projectiveGroup.val)
        (d : ∀ R : TestAlgebra K, (restrictTestAlgebraObj k K R ⊗[k] A) ≃ₐ[R]
          Matrix (Fin n) (Fin n) R),
        (∀ {R S : TestAlgebra k} (f : R ⟶ S) (x : F.obj R),
          point S (F.map f x) =
            Units.map (Algebra.TensorProduct.map f.hom (.id k A)).toMonoidHom (point R x)) ∧
        (∀ (R : TestAlgebra k) (f : UnitCoordinates hA b →ₐ[k] R)
          (p : Points U.val.X R), p.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
          ∀ i, (b.baseChange R).repr (point R (e.hom.app R p)).val i =
            f (algebraMap (MvPolynomial ι k) (UnitCoordinates hA b) (MvPolynomial.X i))) ∧
        (∀ (R : TestAlgebra k) (p : Points H.X R),
          point R (e.hom.app R (p ≫ i.hom.hom)) =
            Units.map (algebraMap R (R ⊗[k] A)).toMonoidHom (m.hom.app R p)) ∧
        (let B : Specs.ClosedSubgroup U.val := ⟨H, i, hi⟩
         Specs.IsSchemeKernel q B ∧ ∃ eq : Specs.rightQuotientSheaf B ≅ Specs.schemeFppfSheaf Q.val.X,
           Specs.rightQuotientProjection B ≫ eq.hom =
             (Specs.fppfOver k).uliftYoneda.map q.hom.hom) ∧
        (∀ (R : TestAlgebra K) (r : R) (a : A),
          d R (r ⊗ₜ[k] a) = r • (s (1 ⊗ₜ[k] a)).map (algebraMap K R)) ∧
        (∀ (R : TestAlgebra K) (p : Points ((groupBaseChange k K).obj Q.val).X R),
          z.hom.app R (baseChangePoint k K Q.val.X R p) =
            baseChangePoint k K P.projectiveGroup.val.X R (p ≫ j.hom.hom.hom)) ∧
        (∀ (R : TestAlgebra K) (p : Points U.val.X (restrictTestAlgebraObj k K R)),
          z.hom.app R (p ≫ q.hom.hom) =
            projectiveMatrixPoint P (restrictTestAlgebraObj k K R)
              (Units.map (d R).toMonoidHom (point _ (e.hom.app _ p)))) ∧
        (∀ [FiniteDimensional k K] [IsGalois k K], MatrixAlgebraForms.Classifies.{u,u} (K := K) P) ∧
        IsProjectiveCocycleComparison s Q.val P z

/-- The pointed classification used by the group twists is the one via the
transport of the splitting and the effective descent of the matrix algebra. -/
abbrev InnerClassification : Prop := MatrixAlgebraForms.Classification.{u,w}

/-- The opposite algebra has the transposed splitting. Its transported cocycle
is obtained by inverse-transposing projective matrix lifts. The two cocycles
represent the same inner data precisely when the algebras are isomorphic. -/
def OppositeTwisting : Prop :=
  ∀ {k K A : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Ring A] [Algebra k A] {n : ℕ} (_hA : isCentralSimple k A)
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (ρ : AlgebraAction k K (Matrix (Fin n) (Fin n) K)) (c : Cocycle k K n),
    IsTransport ρ s → Implements ρ c →
    ∃ t : (K ⊗[k] Aᵐᵒᵖ) ≃ₐ[K] Matrix (Fin n) (Fin n) K,
      (∀ (r : K) (a : A), t (r ⊗ₜ[k] MulOpposite.op a) = (s (r ⊗ₜ[k] a)).transpose) ∧
      ∃ (τ : AlgebraAction k K (Matrix (Fin n) (Fin n) K)) (d : Cocycle k K n),
        IsTransport τ t ∧ Implements τ d ∧
        (∀ (σ : Gal(K/k)) (G : GL (Fin n) K), ProjGenLinGroup.mk G = c.val σ →
          ∃ H : GL (Fin n) K, H.val = (↑G⁻¹ : Matrix (Fin n) (Fin n) K).transpose ∧
            ProjGenLinGroup.mk H = d.val σ) ∧
        ((Quot.mk _ c : _root_.RM03.Brauer.ProjectiveClassification.H1 k K n) = Quot.mk _ d ↔
          Nonempty (A ≃ₐ[k] Aᵐᵒᵖ))

/-- The norm-one group schemes are identified by inversion into the opposite
algebra on every test algebra. -/
def InversionIsomorphism {κ : Type u} [Fintype κ]
    (hA : isCentralSimple k A) (b : Module.Basis ι k A) (c : Module.Basis κ k Aᵐᵒᵖ) : Prop :=
  ∃ hO : isCentralSimple k Aᵐᵒᵖ,
  ∃ (H : HopfOperations k (NormOneCoordinates hA b))
    (J : HopfOperations k (NormOneCoordinates hO c)),
    let G := @spectrum k _ (NormOneCoordinates hA b) _ H.hopf inferInstance
    let L := @spectrum k _ (NormOneCoordinates hO c) _ J.hopf inferInstance
    ∃ j : G.val ≅ L.val,
      ∀ (R : TestAlgebra k)
        (f : NormOneCoordinates hA b →ₐ[k] R) (g : NormOneCoordinates hO c →ₐ[k] R)
        (p : Points G.val.X R),
        p.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
        (p ≫ j.hom.hom.hom).left = Spec.map (CommRingCat.ofHom g.toRingHom) →
        let x := (b.baseChange R).equivFun.symm
          (fun i => f (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X i)))
        let y := (c.baseChange R).equivFun.symm
          (fun i => g (Ideal.Quotient.mk (normOneIdeal hO c) (MvPolynomial.X i)))
        ∃ u : (R ⊗[k] A)ˣ, u.val = x ∧
          y = TensorProduct.map (LinearMap.id : R →ₗ[k] R)
            (MulOpposite.opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ).toLinearMap (↑u⁻¹ : R ⊗[k] A)

/-- Inversion into the opposite algebra identifies the two norm-one groups. -/
def OppositeNormOne : Prop :=
  ∀ {k A ι κ : Type u} [Field k] [Ring A] [Algebra k A] [Fintype ι] [Fintype κ]
    (hA : isCentralSimple k A) (b : Module.Basis ι k A) (c : Module.Basis κ k Aᵐᵒᵖ),
    InversionIsomorphism hA b c

/-- There are degree-three algebras with distinct inner twisting data whose
norm-one groups are isomorphic by inversion into the opposite algebra. -/
def InnerDataCanBeLost : Prop :=
  ∃ (k K A : Type) (_ : Field k) (_ : Field K) (_ : Algebra k K)
    (_ : FiniteDimensional k K) (_ : IsGalois k K) (_ : Ring A) (_ : Algebra k A)
    (hA : isCentralSimple k A),
    degree k A = 3 ∧
    Nonempty ((K ⊗[k] A) ≃ₐ[K] Matrix (Fin 3) (Fin 3) K) ∧
    ¬ Nonempty (A ≃ₐ[k] Aᵐᵒᵖ) ∧
    ∃ (ι κ : Type) (_ : Fintype ι) (_ : Fintype κ)
      (b : Module.Basis ι k A) (c : Module.Basis κ k Aᵐᵒᵖ), InversionIsomorphism hA b c

/-- Transpose-inverse is a natural automorphism of the split special linear
group and, in degree at least three, is not induced by projective conjugation. -/
def TransposeInverseOuter : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 3 ≤ n →
    let I := ULift.{u} (Fin n)
    ∃ e : specialLinearPoints k I ≅ specialLinearPoints k I,
      (∀ (R : TestAlgebra k) (x : Matrix.SpecialLinearGroup I R),
        (show Matrix.SpecialLinearGroup I R from e.hom.app R x).val =
          ((x⁻¹ : Matrix.SpecialLinearGroup I R) : Matrix I I R).transpose) ∧
      ∀ (K : Type u) [Field K] [Algebra k K], ∀ g : GL I K, ∃ x : Matrix.SpecialLinearGroup I K,
        (show Matrix.SpecialLinearGroup I K from e.hom.app (CommAlgCat.of k K) x).val ≠
          (g : Matrix I I K) * (x : Matrix I I K) * (↑g⁻¹ : Matrix I I K)

end

end LinearAlgebraicGroups.Descent.InnerTypeA.Specification
