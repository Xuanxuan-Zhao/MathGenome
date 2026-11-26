import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatum
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.MatrixAlgebraForms

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.SymplecticDatumAdjointDescent (MatrixAlgebra adjoint ScalarCentre conjugateMatrix)
open Specs.SymplecticMatrixStructure (Indices PointGroup symplecticPoints mapSymplecticPoint)
open RM03.Brauer.ProjectiveClassification (Mat)
open RM03.Brauer.SemilinearDescent (AlgebraAction)

noncomputable section

abbrev PointsOf {k : Type u} [Field k] (G : GroupScheme k) := (groupPointsFunctor k).obj G

/-- The quotient by the scalar scheme centre, with its two conjugation actions. -/
structure AdjointPresentation (k I : Type u) [Field k] [Fintype I] [DecidableEq I] where
  splitGroup : AffineAlgebraicGroup k
  splitPoints : PointsOf splitGroup.val ≅ symplecticPoints k I
  centre : ClosedSubgroup splitGroup.val
  centre_spec : CentralTorus.IsSchemeCentre centre
  centre_scalar : ScalarCentre splitPoints centre
  quotient : AffineAlgebraicGroup k
  projection : splitGroup.val ⟶ quotient.val
  kernel : IsSchemeKernel projection centre
  represents : SchemeDerivedGroup.RepresentsQuotient centre projection
  localLift : ∀ (R : TestAlgebra k) (a : (PointsOf quotient.val).obj R),
    ∃ (S : TestAlgebra k) (f : R ⟶ S) (g : (PointsOf splitGroup.val).obj S),
      f.hom.toRingHom.FaithfullyFlat ∧ f.hom.toRingHom.FinitePresentation ∧
      ((groupPointsFunctor k).map projection).app S g = (PointsOf quotient.val).map f a
  onAlgebra : ∀ R : TestAlgebra k, (PointsOf quotient.val).obj R →*
    (MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R)
  onGroup : ∀ R : TestAlgebra k, (PointsOf quotient.val).obj R →* MulAut (PointGroup I R)
  preservesAdjoint : ∀ (R : TestAlgebra k) (a : (PointsOf quotient.val).obj R) X,
    onAlgebra R a (adjoint X) = adjoint (onAlgebra R a X)
  algebraNatural : ∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : (PointsOf quotient.val).obj R) X,
    (onAlgebra R a X).map f.hom = onAlgebra S ((PointsOf quotient.val).map f a) (X.map f.hom)
  onLift : ∀ (R : TestAlgebra k) (g : (PointsOf splitGroup.val).obj R) X,
    onAlgebra R (((groupPointsFunctor k).map projection).app R g) X =
      conjugateMatrix (splitPoints.hom.app R g) X
  groupMatrix : ∀ (R : TestAlgebra k) (a : (PointsOf quotient.val).obj R) (g : PointGroup I R),
    (onGroup R a g).val = onAlgebra R a g.val

def QuotientPresentation : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [Nonempty I]
    (G : AffineAlgebraicGroup k) (c : PointsOf G.val ≅ symplecticPoints k I),
    ∃ P : AdjointPresentation k I, ∃ e : P.splitGroup = G, e ▸ P.splitPoints = c

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]

abbrev Coefficients (P : AdjointPresentation k I) := (PointsOf P.quotient.val).obj (CommAlgCat.of k K)

abbrev Cocycle (P : AdjointPresentation k I) :=
  Descent.MatrixAlgebraForms.GaloisCocycle
    (Descent.NonabelianCohomology.pointAction k K P.quotient.val.X)

abbrev overBase (k K : Type u) [Field k] [Field K] [Algebra k K]
    (S : TestAlgebra K) := (restrictTestAlgebra k K).obj S

abbrev coefficientHom (S : TestAlgebra K) :
    CommAlgCat.of k K ⟶ overBase k K S :=
  ConcreteCategory.ofHom (C := CommAlgCat k) ({ toRingHom := algebraMap K S, commutes' := fun _ => rfl } :
    K →ₐ[k] overBase k K S)

/-- The transported automorphism cocycle is the inner action. The equation uses
semilinear maps on test algebras, so it specifies the automorphism on all points
over the splitting field. -/
structure SplitComparison (P : AdjointPresentation k I) (G : AffineAlgebraicGroup k)
    (a : Cocycle (K := K) P) where
  iso : restrictTestAlgebra k K ⋙ PointsOf G.val ≅
    restrictTestAlgebra k K ⋙ symplecticPoints k I
  inner : ∀ (g : Gal(K/k)) (S T : TestAlgebra K) (f : overBase k K S ⟶ overBase k K T)
    (_h : ∀ b : K, f.hom (algebraMap K S b) = algebraMap K T (g b))
    (x : (PointsOf G.val).obj (overBase k K S)),
    iso.hom.app T ((PointsOf G.val).map f x) =
      P.onGroup (overBase k K T)
        ((PointsOf P.quotient.val).map
          (coefficientHom T) (a g))
        (mapSymplecticPoint f.hom.toRingHom (iso.hom.app S x))

/-- A linear involution of the first kind on an algebra. -/
structure Involution (k A : Type u) [CommRing k] [Ring A] [Algebra k A] where
  toLinearMap : A →ₗ[k] A
  map_one : toLinearMap 1 = 1
  map_mul : ∀ x y, toLinearMap (x * y) = toLinearMap y * toLinearMap x
  involutive : Function.Involutive toLinearMap

namespace Involution

variable {B A : Type u} [CommRing B] [Ring A] [Algebra B A] (σ : Involution B A)

theorem fixesScalar (r : B) : σ.toLinearMap (algebraMap B A r) = algebraMap B A r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, σ.map_one]


/-- The scalar extension acts trivially on the test-algebra factor. -/
def baseChange (R : Type u) [CommRing R] [Algebra B R] :
    Involution R (R ⊗[B] A) where
  toLinearMap := σ.toLinearMap.baseChange R
  map_one := by
    rw [Algebra.TensorProduct.one_def, LinearMap.baseChange_tmul, σ.map_one]
  map_mul := by
    intro x y
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [add_mul, mul_add, map_add, hx, hz]
    | tmul r a =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [mul_add, add_mul, map_add, hy, hz]
      | tmul s b =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
          σ.map_mul, mul_comm r s]
  involutive x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a => simp only [LinearMap.baseChange_tmul, σ.involutive a]

@[simp] theorem baseChange_tmul (R : Type u) [CommRing R] [Algebra B R] (r : R) (a : A) :
    (σ.baseChange R).toLinearMap (r ⊗ₜ[B] a) = r ⊗ₜ[B] σ.toLinearMap a := rfl

/-- The isometries are units satisfying the defining involution equation. -/
def isometries : Subgroup Aˣ where
  carrier := {g | σ.toLinearMap (g : A) * (g : A) = 1}
  one_mem' := by change σ.toLinearMap 1 * 1 = 1; rw [σ.map_one, one_mul]
  mul_mem' := by
    intro x y hx hy
    change σ.toLinearMap (↑x * ↑y) * (↑x * ↑y) = 1
    change σ.toLinearMap (x : A) * (x : A) = 1 at hx
    change σ.toLinearMap (y : A) * (y : A) = 1 at hy
    rw [σ.map_mul, mul_assoc (σ.toLinearMap ↑y), ← mul_assoc (σ.toLinearMap ↑x), hx, one_mul]
    exact hy
  inv_mem' := by
    intro x hx
    change σ.toLinearMap (x : A) * (x : A) = 1 at hx
    have h : σ.toLinearMap (x : A) = (↑x⁻¹ : A) :=
      (Units.mul_left_inj x).mp (hx.trans x.inv_val.symm)
    change σ.toLinearMap (↑x⁻¹ : A) * (↑x⁻¹ : A) = 1
    rw [← h, σ.involutive x, h]
    exact x.val_inv

theorem mem_isometries (x : Aˣ) :
    x ∈ σ.isometries ↔ σ.toLinearMap (x : A) * (x : A) = 1 := Iff.rfl

variable {D C : Type u} [CommRing D] [Ring C] [Algebra D C]

/-- A ring map commuting with the involutions maps the isometry groups. -/
def mapIsometries (τ : Involution D C) (f : A →+* C)
    (hf : ∀ x, f (σ.toLinearMap x) = τ.toLinearMap (f x)) :
    σ.isometries →* τ.isometries :=
  ((Units.map f.toMonoidHom).comp σ.isometries.subtype) |>.codRestrict τ.isometries (fun x => by
    change τ.toLinearMap (f (x.val : A)) * f (x.val : A) = 1
    rw [← hf, ← _root_.map_mul, (σ.mem_isometries x.val).mp x.property, _root_.map_one])


end Involution

/-- Change of test algebra on the tensor product used to evaluate the isometry
group. -/
abbrev tensorMap {A : Type u} [Ring A] [Algebra k A] {R S : TestAlgebra k}
    (f : R ⟶ S) : (R ⊗[k] A) →ₐ[k] (S ⊗[k] A) :=
  Algebra.TensorProduct.map f.hom (AlgHom.id k A)

theorem tensorMap_involution {A : Type u} [Ring A] [Algebra k A] (σ : Involution k A)
    {R S : TestAlgebra k} (f : R ⟶ S) (x : R ⊗[k] A) :
    tensorMap f ((σ.baseChange R).toLinearMap x) =
      (σ.baseChange S).toLinearMap (tensorMap f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The unitary group functor, defined on every commutative test algebra. -/
def isometryPoints {A : Type u} [Ring A] [Algebra k A] (σ : Involution k A) :
    TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (σ.baseChange R).isometries
  map f := GrpCat.ofHom ((σ.baseChange _).mapIsometries (σ.baseChange _)
    (tensorMap f).toRingHom (tensorMap_involution σ f))
  map_id R := by
    apply GrpCat.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    change tensorMap (𝟙 R) (g.val : R ⊗[k] A) = _
    rw [show tensorMap (A := A) (𝟙 R) = AlgHom.id k _ from Algebra.TensorProduct.map_id]
    rfl
  map_comp f g := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Units.ext
    change tensorMap (f ≫ g) (x.val : _ ⊗[k] A) = tensorMap g (tensorMap f _)
    rw [show tensorMap (A := A) (f ≫ g) = (tensorMap g).comp (tensorMap f) by
      rw [← Algebra.TensorProduct.map_comp]
      rfl]
    rfl

/-- Relabel the hyperbolic matrix indices by a standard finite type. -/
abbrev relabel (I : Type u) [Fintype I] [DecidableEq I] (R : Type u) [CommRing R] :
    MatrixAlgebra I R ≃ₐ[R] Mat R (2 * Fintype.card I) :=
  Matrix.reindexAlgEquiv R R
    ((Fintype.equivFin (Indices I)).trans
      (finCongr (by simp [Indices, two_mul])))

structure FixedAlgebra (P : AdjointPresentation k I) (a : Cocycle (K := K) P) where
  action : AlgebraAction k K (Mat K (2 * Fintype.card I))
  twist : ∀ (g : Gal(K/k)) (X : MatrixAlgebra I K),
    action.act g (relabel I K X) =
      relabel I K (P.onAlgebra (CommAlgCat.of k K) (a g) (X.map g))
  centralSimple : _root_.Specs.RM03.CSA.isCentralSimple k action.fixedSubalgebra
  degree : _root_.Specs.RM03.CSA.degree k action.fixedSubalgebra = 2 * Fintype.card I
  involution : Involution k (action.fixedSubalgebra : Type u)
  involutionFormula : ∀ x : action.fixedSubalgebra,
    (relabel I K).symm (involution.toLinearMap x).val =
      adjoint ((relabel I K).symm x.val)
  split : (K ⊗[k] (action.fixedSubalgebra : Type u)) ≃ₐ[K] MatrixAlgebra I K
  splitPure : ∀ (r : K) (x : action.fixedSubalgebra),
    split (r ⊗ₜ[k] x) = r • (relabel I K).symm x.val
  splitInvolution : ∀ x,
    split ((involution.baseChange K).toLinearMap x) = adjoint (split x)

def AlgebraDescent : Prop :=
  ∀ (k K I : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype I] [DecidableEq I] [Nonempty I] (P : AdjointPresentation k I) (a : Cocycle (K := K) P),
    Nonempty (FixedAlgebra P a)

/-- The group comparison and its specified scalar-extension identification. -/
structure Model (P : AdjointPresentation k I) (G : AffineAlgebraicGroup k)
    (a : Cocycle (K := K) P) (c : SplitComparison P G a) where
  fixed : FixedAlgebra P a
  comparison : PointsOf G.val ≅ isometryPoints fixed.involution
  splitting : ∀ S : TestAlgebra K,
    (overBase k K S ⊗[k] (fixed.action.fixedSubalgebra : Type u)) ≃ₐ[S] MatrixAlgebra I S
  splittingPure : ∀ (S : TestAlgebra K) (r : S) (x : fixed.action.fixedSubalgebra),
    splitting S (r ⊗ₜ[k] x) = r • ((relabel I K).symm x.val).map (algebraMap K S)
  splittingInvolution : ∀ (S : TestAlgebra K) x,
    splitting S ((fixed.involution.baseChange (overBase k K S)).toLinearMap x) =
      adjoint (splitting S x)
  splittingEquivariant : ∀ (g : Gal(K/k)) (S T : TestAlgebra K)
    (f : overBase k K S ⟶ overBase k K T),
    (∀ b : K, f.hom (algebraMap K S b) = algebraMap K T (g b)) →
    ∀ x, splitting T (tensorMap f x) =
      P.onAlgebra (overBase k K T)
        ((PointsOf P.quotient.val).map (coefficientHom T) (a g))
        ((splitting S x).map f.hom)
  comparisonSplit : ∀ (S : TestAlgebra K) (g : (PointsOf G.val).obj (overBase k K S)),
    splitting S
      (((comparison.hom.app (overBase k K S) g).val :
        (overBase k K S ⊗[k] (fixed.action.fixedSubalgebra : Type u))ˣ) :
          overBase k K S ⊗[k] (fixed.action.fixedSubalgebra : Type u)) =
      (show PointGroup I S from c.iso.hom.app S g).val

def DescentStatement : Prop :=
  ∀ (k K I : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype I] [DecidableEq I] [Nonempty I] (P : AdjointPresentation k I)
    (G : AffineAlgebraicGroup k) (a : Cocycle (K := K) P) (c : SplitComparison P G a),
    Nonempty (Model P G a c)


end

end LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
