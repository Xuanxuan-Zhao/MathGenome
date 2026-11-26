import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedNorm
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors

open LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open _root_.Specs.RM03.CSA (degree isCentralSimple isCentralDivision reducedNorm)
open scoped Matrix TensorProduct BigOperators

universe u v

abbrev Mat (r : ℕ) (D : Type*) := Matrix (Fin r) (Fin r) D

abbrev adj {K E A : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] (s : SecondKind K E A) (x : A) : A :=
  (s.adjoint x).unop

section Model

variable {K E A D : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ}

/-- Coefficient conjugation and transposition on the division matrix algebra. -/
def dagger (σ : SecondKind K E D) (X : Mat r D) : Mat r D :=
  X.transpose.map (adj σ)

/-- The adjoint of the given algebra involution in a right division-module basis. -/
def HermitianMatrix (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (H : (Mat r D)ˣ) : Prop :=
  σ.conjugation = s.conjugation ∧ dagger σ H.val = H.val ∧
    ∀ a, e (adj s a) = (H⁻¹ : (Mat r D)ˣ).val * dagger σ (e a) * H.val

/-- The form on column vectors, with right scalars on the second argument. -/
def form (σ : SecondKind K E D) (H : Mat r D) (x y : Fin r → D) : D :=
  (fun i => adj σ (x i)) ⬝ᵥ (H *ᵥ y)

def rightMul (x : Fin r → D) (d : D) : Fin r → D := fun i => x i * d

/-- The first slot is conjugate right-linear by symmetry and the second-slot laws. -/
def IsHermitianForm (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D) : Prop :=
  (∀ x y z, h x (y + z) = h x y + h x z) ∧
  (∀ x y d, h x (rightMul y d) = h x y * d) ∧
  (∀ x y, adj σ (h x y) = h y x) ∧
  (∀ y, (∀ x, h x y = 0) → y = 0) ∧
  ∀ a x y, h (e a *ᵥ x) y = h x (e (adj s a) *ᵥ y)

end Model

/-- A division factor with the given conjugation and an invertible Hermitian Gram matrix. -/
def HermitianPresentation : Prop :=
  ∀ {K E A : Type u} [Field K] [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    Module.finrank K E = 2 → ∀ (_ : isCentralSimple E A) (s : SecondKind K E A),
    ∃ (r : ℕ) (D : Type u) (_ : DivisionRing D) (_ : Algebra E D),
      letI : Algebra K D := Algebra.compHom D (algebraMap K E)
      letI : IsScalarTower K E D := IsScalarTower.of_algebraMap_eq fun _ => rfl
      isCentralDivision E D ∧ 0 < r ∧
      ∃ (e : A ≃ₐ[E] Mat r D) (σ : SecondKind K E D) (H : (Mat r D)ˣ),
        HermitianMatrix s e σ H ∧ IsHermitianForm s e σ (form σ H.val)

section ColumnAction

variable {E A D : Type u} [Field E]
  [Ring A] [Algebra E A] [Ring D] [Algebra E D] {r : ℕ}

open Matrix in
/-- The action by left matrix multiplication on the right division module. -/
def columnAction (e : A ≃ₐ[E] Mat r D) : A →ₐ[E] Module.End E (Fin r → D) where
  toFun a := mulVecBilin E E (e a)
  map_one' := LinearMap.ext fun x => by simp [mulVecBilin]
  map_zero' := LinearMap.ext fun x => by simp [mulVecBilin]
  map_mul' a b := LinearMap.ext fun x => by simp [mulVecBilin, mulVec_mulVec]
  map_add' a b := LinearMap.ext fun x => by simp [mulVecBilin, add_mulVec]
  commutes' c := LinearMap.ext fun x => by
    change (e (algebraMap E A c)) *ᵥ x = c • x
    rw [e.commutes, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec]


end ColumnAction

def DeterminantComparison : Prop :=
  ∀ {E A D : Type u} [Field E] [Ring A] [Algebra E A]
    [DivisionRing D] [Algebra E D] {r : ℕ},
    ∀ (hA : isCentralSimple E A) (_ : isCentralDivision E D)
      (e : A ≃ₐ[E] Mat r D) (a : A),
      LinearMap.det (columnAction e a) = reducedNorm hA a ^ degree E D

section Tensors

variable {K E A D : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ}

/-- Right multiplication, the full Hermitian pairing and the centre-valued
top exterior form, expressed on the ground-field space. -/
def PreservesTensors {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    (b : Module.Basis J K D) (v : Module.Basis I E (Fin r → D))
    (h : (Fin r → D) → (Fin r → D) → D) (g : (Fin r → D) ≃ₗ[K] (Fin r → D)) : Prop :=
  (∀ j x, g (rightMul x (b j)) = rightMul (g x) (b j)) ∧
  (∀ x y, h (g x) (g y) = h x y) ∧
  ∀ x : I → (Fin r → D), v.det (g ∘ x) = v.det x

def TensorStabilizer : Prop :=
  ∀ (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D),
    IsHermitianForm s e σ h →
    ∀ {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
      (b : Module.Basis J K D) (v : Module.Basis I E (Fin r → D))
      (g : (Fin r → D) ≃ₗ[K] (Fin r → D)),
      PreservesTensors b v h g ↔
        ∃ a : Aˣ, (∀ x, g x = columnAction e a.val x) ∧
          adj s a.val * a.val = 1 ∧ LinearMap.det (columnAction e a.val) = 1

def GroundFieldBilinearity : Prop :=
  ∀ (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D),
    IsHermitianForm s e σ h →
    ∃ B : (Fin r → D) →ₗ[K] (Fin r → D) →ₗ[K] D, ∀ x y, B x y = h x y

end Tensors

section Polynomials

variable {K V W I J : Type u} [CommRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype I]

open MvPolynomial in
/-- The coordinates of the diagonal of a bilinear map in the given bases. -/
noncomputable def diagonalPolynomial (b : Module.Basis I K V) (c : Module.Basis J K W)
    (h : V →ₗ[K] V →ₗ[K] W) (j : J) : MvPolynomial I K :=
  ∑ a, ∑ d, C (c.repr (h (b a) (b d)) j) * X a * X d

def DiagonalCoordinates : Prop :=
  ∀ (b : Module.Basis I K V) (c : Module.Basis J K W) (h : V →ₗ[K] V →ₗ[K] W),
    (∀ j, (diagonalPolynomial b c h j).IsHomogeneous 2) ∧
    (∀ x j, MvPolynomial.eval (fun i => b.repr x i) (diagonalPolynomial b c h j) =
      c.repr (h x x) j) ∧
    (∀ g : V ≃ₗ[K] V, (∀ x y, h (g x) (g y) = h x y) →
      ∀ x j, MvPolynomial.eval (fun i => b.repr (g x) i) (diagonalPolynomial b c h j) =
        MvPolynomial.eval (fun i => b.repr x i) (diagonalPolynomial b c h j)) ∧
    ((∀ x, x ≠ 0 → h x x ≠ 0) → ∀ x, x ≠ 0 →
      ∃ j, MvPolynomial.eval (fun i => b.repr x i) (diagonalPolynomial b c h j) ≠ 0)

end Polynomials

section Application

variable {K E A D : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ}

def HyperbolicPartner : Prop :=
  ∀ (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D),
    IsHermitianForm s e σ h →
    ∀ x, x ≠ 0 → h x x = 0 → ∃ y, h x y = 1 ∧ h y x = 1 ∧ h y y = 0

/-- The hyperbolic lines produce two mutually adjoint orthogonal idempotents
interchanged by conjugation in the original algebra. -/
def HyperbolicIdempotents : Prop :=
  ∀ (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D),
    IsHermitianForm s e σ h →
    ∀ x, x ≠ 0 → h x x = 0 →
      ∃ (p q : A) (w : Aˣ), p ≠ 0 ∧ p * p = p ∧ q * q = q ∧
        p * q = 0 ∧ q * p = 0 ∧ adj s p = q ∧ w.val * p * w.inv = q

/-- A primitive projector with its full corner and the induced involution.
The image is the right line generated by x. -/
def IsSelfAdjointDivisionCorner (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (x : Fin r → D) (p : A) (i : D →ₗ[E] A) (τ : SecondKind K E D) : Prop :=
  x ≠ 0 ∧ p * p = p ∧ adj s p = p ∧
  Set.range (columnAction e p) = Set.range (rightMul x) ∧
  i 1 = p ∧ Function.Injective i ∧ (∀ d c, i (d * c) = i d * i c) ∧
  (∀ a, p * a * p = a ↔ a ∈ Set.range i) ∧
  τ.conjugation = s.conjugation ∧ (∀ d, adj s (i d) = i (adj τ d))

def SelfAdjointCorner : Prop :=
  ∀ (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D),
    IsHermitianForm s e σ h → σ.conjugation = s.conjugation → 0 < r →
    ∃ (x : Fin r → D) (p : A) (i : D →ₗ[E] A) (τ : SecondKind K E D),
      IsSelfAdjointDivisionCorner s e x p i τ


def TensorStabilizerNorm : Prop :=
  ∀ (hA : isCentralSimple E A) (_ : isCentralDivision E D)
    (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D),
    IsHermitianForm s e σ h →
    ∀ {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
      (b : Module.Basis J K D) (v : Module.Basis I E (Fin r → D))
      (g : (Fin r → D) ≃ₗ[K] (Fin r → D)),
      PreservesTensors b v h g →
        ∃ a : Aˣ, (∀ x, g x = columnAction e a.val x) ∧
          adj s a.val * a.val = 1 ∧ reducedNorm hA a.val ^ degree E D = 1

def GroundFieldDeterminantOne : Prop :=
  ∀ (hA : isCentralSimple E A) (_ : isCentralDivision E D)
    (e : A ≃ₐ[E] Mat r D) (a : A),
    reducedNorm hA a = 1 → LinearMap.det ((columnAction e a).restrictScalars K) = 1

end Application

section Coefficients

variable {K E A D R : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [Ring D] [Algebra E D] [Algebra K D] [IsScalarTower K E D]
  [CommRing R] [Algebra K R] {r : ℕ}

/-- The column action with scalars restricted to the ground field. -/
def groundColumnAction (e : A ≃ₐ[E] Mat r D) : A →ₐ[K] Module.End K (Fin r → D) :=
  AlgHom.ofLinearMap ((LinearMap.restrictScalarsₗ (R := K) (S := E) (M := Fin r → D) (N := Fin r → D) (R₁ := K)).comp
    (((columnAction e).toLinearMap).restrictScalars K))
    (by change (columnAction e 1).restrictScalars K = 1
        rw [map_one]
        rfl)
    (fun a b => by
      change (columnAction e (a * b)).restrictScalars K =
        (columnAction e a).restrictScalars K * (columnAction e b).restrictScalars K
      rw [map_mul]
      rfl)

/-- The action on the actual scalar extension of the original column space. -/
def extendedColumnAction (e : A ≃ₐ[E] Mat r D) :
    (R ⊗[K] A) →ₐ[R] Module.End R (R ⊗[K] (Fin r → D)) :=
  Algebra.TensorProduct.lift (R := K) (S := R) (Algebra.ofId R _)
    ((Module.End.baseChangeHom K R _).comp (groundColumnAction e))
    (fun a _ => Algebra.commutes a _)

/-- Compatibility of the action with each place of either kind of global field. -/
def CompletionColumnAction : Prop :=
  ∀ (k : LinearAlgebraicGroups.Arithmetic.GlobalFieldData.{u,v} K) (w : k.Place)
    (e : A ≃ₐ[E] Mat r D),
    letI : Algebra K (k.Completion w) := (k.embedding w).toAlgebra
    ∀ (c b : k.Completion w) (a : A) (x : Fin r → D),
      extendedColumnAction e (c ⊗ₜ[K] a) (b ⊗ₜ[K] x) =
        (c * b) ⊗ₜ[K] (columnAction e a x)

end Coefficients

section SplitTorus

open LinearAlgebraicGroups.UnitaryNormEquations (IsSpecialUnitary)

variable {K E A : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]

/-- Extend a ground-field linear functional to the test algebra. -/
def coefficientAt {R : Type u} [CommRing R] [Algebra K R] (l : A →ₗ[K] K) :
    (R ⊗[K] A) →ₗ[K] R :=
  (TensorProduct.rid K R).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l

/-- An embedding of the split one-dimensional torus into the special unitary
functor. The image is cut out by the displayed equations in every test algebra.
The two parameters are recovered by linear functions of the algebra coordinates. -/
def HasSplitUnitaryTorus {I : Type u} [Fintype I]
    (hA : isCentralSimple E A) (b : Module.Basis I E A) (s : SecondKind K E A) : Prop :=
  ∃ T : ∀ (R : Type u) [CommRing R] [Algebra K R], Rˣ →* (R ⊗[K] A)ˣ,
    (∀ (R : Type u) [CommRing R] [Algebra K R], Function.Injective (T R)) ∧
    (∀ (R : Type u) [CommRing R] [Algebra K R] (t : Rˣ), IsSpecialUnitary hA b s (T R t)) ∧
    (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
      (f : R →ₐ[K] S) (t : Rˣ),
      T S (Units.map f.toMonoidHom t) =
        Units.map (Algebra.TensorProduct.map f (.id K A)).toMonoidHom (T R t)) ∧
    ∃ (p q : A) (l m : A →ₗ[K] K),
      (∀ (R : Type u) [CommRing R] [Algebra K R] (t : Rˣ),
        coefficientAt l (T R t).val = t.val ∧ coefficientAt m (T R t).val = t.inv) ∧
      ∀ (R : Type u) [CommRing R] [Algebra K R] (x : (R ⊗[K] A)ˣ),
        let a := coefficientAt l x.val
        let b := coefficientAt m x.val
        (∃ t : Rˣ, T R t = x) ↔
          a * b = 1 ∧ x.val = a ⊗ₜ[K] p + b ⊗ₜ[K] q + (1 : R) ⊗ₜ[K] (1 - p - q)

def SplitUnitaryTorusOfIdempotents : Prop :=
  ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A) (b : Module.Basis I E A)
    (s : SecondKind K E A) (p q : A) (w : Aˣ),
    p ≠ 0 → p * p = p → q * q = q → p * q = 0 → q * p = 0 →
    adj s p = q → w.val * p * w.inv = q → HasSplitUnitaryTorus hA b s

def HermitianAnisotropy {D : Type u} [DivisionRing D]
    [Algebra K D] [Algebra E D] [IsScalarTower K E D] {r : ℕ} : Prop :=
  ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A) (b : Module.Basis I E A)
    (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D),
    IsHermitianForm s e σ h → ¬ HasSplitUnitaryTorus hA b s →
    ∀ x, x ≠ 0 → h x x ≠ 0

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.OuterTypeAModels (RepresentsUnitary)

/-- A closed embedding of the rank-one split torus into the original group. -/
def HasClosedSplitTorus (G : AffineAlgebraicGroup K) : Prop :=
  ∃ f : (LinearAlgebraicGroups.Specs.StandardGroups.multiplicativePowerGroup K
      (ULift.{u} (Fin 1))).val ⟶ G.val,
    IsClosedImmersion f.hom.hom.left

def SplitTorusInUnitaryModel : Prop :=
  ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A) (b : Module.Basis I E A)
    (s : SecondKind K E A) (G : AffineAlgebraicGroup K),
    RepresentsUnitary hA b s G → HasSplitUnitaryTorus hA b s → HasClosedSplitTorus G

def SchemeHermitianAnisotropy {D : Type u} [DivisionRing D]
    [Algebra K D] [Algebra E D] [IsScalarTower K E D] {r : ℕ} : Prop :=
  ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A) (b : Module.Basis I E A)
    (s : SecondKind K E A) (G : AffineAlgebraicGroup K),
    RepresentsUnitary hA b s G → ¬ HasClosedSplitTorus G →
    ∀ (e : A ≃ₐ[E] Mat r D) (σ : SecondKind K E D)
      (h : (Fin r → D) → (Fin r → D) → D),
      IsHermitianForm s e σ h → ∀ x, x ≠ 0 → h x x ≠ 0

/-- The division involution in the anisotropic Hermitian presentation is the
one induced by the original adjoint on the exhibited primitive corner. -/
def AnisotropicHermitianModel : Prop :=
  ∀ [Algebra.IsSeparable K E],
    Module.finrank K E = 2 →
    ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A) (_ : 3 ≤ degree E A)
    (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K),
    RepresentsUnitary hA b s G → ¬ HasClosedSplitTorus G →
    ∃ (r : ℕ) (D : Type u) (_ : DivisionRing D) (_ : Algebra E D),
      letI : Algebra K D := Algebra.compHom D (algebraMap K E)
      letI : IsScalarTower K E D := IsScalarTower.of_algebraMap_eq fun _ => rfl
      isCentralDivision E D ∧ 0 < r ∧ 0 < degree E D ∧ degree E A = r * degree E D ∧
      ∃ (e : A ≃ₐ[E] Mat r D) (x : Fin r → D) (p : A) (i : D →ₗ[E] A)
        (τ : SecondKind K E D) (H : (Mat r D)ˣ),
        IsSelfAdjointDivisionCorner s e x p i τ ∧ HermitianMatrix s e τ H ∧
        IsHermitianForm s e τ (form τ H.val) ∧
        ∃ B : (Fin r → D) →ₗ[K] (Fin r → D) →ₗ[K] D,
          (∀ x y, B x y = form τ H.val x y) ∧ ∀ x, x ≠ 0 → B x x ≠ 0

end SplitTorus

section ExtendedForm

variable {K R V W : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Bilinear scalar extension, so that both input vectors and the value
are extended by the same coefficient algebra. -/
def extendForm (h : V →ₗ[K] V →ₗ[K] W) :
    (R ⊗[K] V) →ₗ[R] (R ⊗[K] V) →ₗ[R] (R ⊗[K] W) :=
  (TensorProduct.AlgebraTensorModule.lift
    ({ toFun := fun r => r • LinearMap.baseChangeHom K R V W
       map_add' := fun _ _ => add_smul _ _ _
       map_smul' := fun a r => mul_smul a r _ } :
      R →ₗ[R] (V →ₗ[K] W) →ₗ[K] ((R ⊗[K] V) →ₗ[R] (R ⊗[K] W)))).comp (h.baseChange R)

end ExtendedForm

section LocalInvariance

open LinearAlgebraicGroups.UnitaryNormEquations (IsSpecialUnitary)

variable {K E A D : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ}

/-- At each completion, the original special unitary point acts in the
base-changed basis, preserves the extended form and preserves each of its
quadratic diagonal coordinates with the canonical coefficient embedding. -/
def CompletionInvariance : Prop :=
  ∀ (k : LinearAlgebraicGroups.Arithmetic.GlobalFieldData.{u,v} K) (w : k.Place)
    {L I J : Type u} [Fintype L] [Fintype I]
    (hA : isCentralSimple E A) (b : Module.Basis L E A) (s : SecondKind K E A)
    (e : A ≃ₐ[E] Mat r D) (σ : SecondKind K E D)
    (B : (Fin r → D) →ₗ[K] (Fin r → D) →ₗ[K] D),
    IsHermitianForm s e σ (fun x y => B x y) →
    ∀ (v : Module.Basis I K (Fin r → D)) (c : Module.Basis J K D),
    let R := k.Completion w
    letI : Algebra K R := (k.embedding w).toAlgebra
    ∀ g : (R ⊗[K] A)ˣ, IsSpecialUnitary hA b s g →
    let f := extendedColumnAction e g.val
    (∀ x y, extendForm B (f x) (f y) = extendForm B x y) ∧
    ∀ x j, (diagonalPolynomial v c B j).eval₂ (k.embedding w)
        (fun i => (v.baseChange R).repr (f x) i) =
      (diagonalPolynomial v c B j).eval₂ (k.embedding w)
        (fun i => (v.baseChange R).repr x i)

end LocalInvariance

section ExtendedDeterminant

open LinearAlgebraicGroups.UnitaryNormEquations (IsSpecialUnitary)

variable {K E A D : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ}

/-- At every place the special unitary action is determinant one in the
ground-field representation, including at places with split centre. -/
def CompletionDeterminantOne : Prop :=
  ∀ (k : LinearAlgebraicGroups.Arithmetic.GlobalFieldData.{u,v} K) (w : k.Place)
    {I : Type u} [Fintype I] (hA : isCentralSimple E A) (_ : isCentralDivision E D)
    (b : Module.Basis I E A) (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D),
    let R := k.Completion w
    letI : Algebra K R := (k.embedding w).toAlgebra
    ∀ g : (R ⊗[K] A)ˣ, IsSpecialUnitary hA b s g →
      LinearMap.det (extendedColumnAction e g.val) = 1

end ExtendedDeterminant

section CompletionTensors

open LinearAlgebraicGroups.UnitaryNormEquations (Centre IsSpecialUnitary associateCentre unitaryNorm)

variable {K E A D R : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D]
  [CommRing R] [Algebra K R] {r : ℕ}

/-- Right multiplication by a fixed division-algebra element on the column space. -/
def rightMultiplication (d : D) : Module.End K (Fin r → D) where
  toFun x := rightMul x d
  map_add' x y := funext fun i => add_mul (x i) (y i) d
  map_smul' c x := funext fun i => smul_mul_assoc c (x i) d

/-- The extended action commutes with the scalar extensions of the right multiplication tensors. -/
def CompletionRightMultiplication : Prop :=
  ∀ (k : LinearAlgebraicGroups.Arithmetic.GlobalFieldData.{u,v} K) (w : k.Place)
    (e : A ≃ₐ[E] Mat r D),
    let R := k.Completion w
    letI : Algebra K R := (k.embedding w).toAlgebra
    ∀ (a : R ⊗[K] A) (d : D),
      Commute (extendedColumnAction e a) ((rightMultiplication (K := K) (r := r) d).baseChange R)

local instance (priority := 2000) : Algebra E (Centre K E R) :=
  Algebra.TensorProduct.rightAlgebra

/-- Reassociate the scalar extension of a vector space over the centre. -/
def associateColumn :
    R ⊗[K] (Fin r → D) ≃ₗ[R] Centre K E R ⊗[E] (Fin r → D) :=
  let V := Fin r → D
  let p : R ⊗[K] V ≃ₗ[K] Centre K E R ⊗[E] V :=
    (TensorProduct.comm K R V).trans
      (((TensorProduct.AlgebraTensorModule.cancelBaseChange K E E V R).symm.trans
        ((TensorProduct.congr (LinearEquiv.refl E V)
          (Algebra.TensorProduct.commRight K E R).toLinearEquiv).trans
          (TensorProduct.comm E V (Centre K E R)))).restrictScalars K)
  have hp (b : R) (x : V) : p (b ⊗ₜ[K] x) = (b ⊗ₜ[K] (1 : E)) ⊗ₜ[E] x := rfl
  { p.toAddEquiv with
    map_smul' := fun b y => by
      change p (b • y) = b • p y
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => rw [smul_add, map_add, hy, hz, map_add, smul_add]
      | tmul c x =>
        change p ((b * c) ⊗ₜ[K] x) = b • p (c ⊗ₜ[K] x)
        rw [hp, hp]
        rfl }

/-- The coefficient extension of the centre-valued volume. -/
noncomputable def extendedVolume {I : Type u} [Fintype I] [DecidableEq I]
    (v : Module.Basis I E (Fin r → D)) (x : I → (R ⊗[K] (Fin r → D))) : Centre K E R :=
  (v.baseChange (Centre K E R)).det (associateColumn ∘ x)

/-- At each completion the special unitary action preserves the extended centre-valued volume. -/
def CompletionVolumeInvariance : Prop :=
  ∀ (k : LinearAlgebraicGroups.Arithmetic.GlobalFieldData.{u,v} K) (w : k.Place)
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq J]
    (hA : isCentralSimple E A) (_ : isCentralDivision E D)
    (b : Module.Basis I E A) (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (v : Module.Basis J E (Fin r → D)),
    let R := k.Completion w
    letI : Algebra K R := (k.embedding w).toAlgebra
    ∀ (g : (R ⊗[K] A)ˣ), IsSpecialUnitary hA b s g →
      ∀ x, extendedVolume v (extendedColumnAction e g.val ∘ x) = extendedVolume v x

end CompletionTensors

/- Closed propositions for checking the polymorphic declarations against these Specs. -/

def TensorStabilizerSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    TensorStabilizer (K := K) (E := E) (A := A) (D := D) (r := r)

def GroundFieldBilinearitySpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    GroundFieldBilinearity (K := K) (E := E) (A := A) (D := D) (r := r)

def DiagonalCoordinatesSpec : Prop :=
  ∀ {K V W I J : Type u} [CommRing K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I],
    DiagonalCoordinates (K := K) (V := V) (W := W) (I := I) (J := J)

def TensorStabilizerNormSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    TensorStabilizerNorm (K := K) (E := E) (A := A) (D := D) (r := r)

def GroundFieldDeterminantOneSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    GroundFieldDeterminantOne (K := K) (E := E) (A := A) (D := D) (r := r)

def HyperbolicPartnerSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    HyperbolicPartner (K := K) (E := E) (A := A) (D := D) (r := r)

def HyperbolicIdempotentsSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    HyperbolicIdempotents (K := K) (E := E) (A := A) (D := D) (r := r)

def SelfAdjointCornerSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    SelfAdjointCorner (K := K) (E := E) (A := A) (D := D) (r := r)

def CompletionColumnActionSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [Ring D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    CompletionColumnAction.{u,v} (K := K) (E := E) (A := A) (D := D) (r := r)

def SplitUnitaryTorusOfIdempotentsSpec : Prop :=
  ∀ {K E A : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    SplitUnitaryTorusOfIdempotents (K := K) (E := E) (A := A)

def HermitianAnisotropySpec : Prop :=
  ∀ {K E A : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    {D : Type u} [DivisionRing D] [Algebra K D] [Algebra E D] [IsScalarTower K E D] {r : ℕ},
    HermitianAnisotropy (K := K) (E := E) (A := A) (D := D) (r := r)

def SplitTorusInUnitaryModelSpec : Prop :=
  ∀ {K E A : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    SplitTorusInUnitaryModel (K := K) (E := E) (A := A)

def SchemeHermitianAnisotropySpec : Prop :=
  ∀ {K E A : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    {D : Type u} [DivisionRing D] [Algebra K D] [Algebra E D] [IsScalarTower K E D] {r : ℕ},
    SchemeHermitianAnisotropy (K := K) (E := E) (A := A) (D := D) (r := r)

def AnisotropicHermitianModelSpec : Prop :=
  ∀ {K E A : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    AnisotropicHermitianModel (K := K) (E := E) (A := A)

def CompletionInvarianceSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    CompletionInvariance.{u,v} (K := K) (E := E) (A := A) (D := D) (r := r)

def CompletionDeterminantOneSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    CompletionDeterminantOne.{u,v} (K := K) (E := E) (A := A) (D := D) (r := r)

def CompletionVolumeInvarianceSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    CompletionVolumeInvariance.{u,v} (K := K) (E := E) (A := A) (D := D) (r := r)

def CompletionRightMultiplicationSpec : Prop :=
  ∀ {K E A D : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ},
    CompletionRightMultiplication.{u,v} (K := K) (E := E) (A := A) (D := D) (r := r)

end LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors
