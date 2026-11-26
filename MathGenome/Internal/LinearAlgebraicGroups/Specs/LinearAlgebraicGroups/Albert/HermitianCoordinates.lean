import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.Adjoints
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! Weighted Hermitian matrices and their scalar and octonion coordinates. -/

namespace LinearAlgebraicGroups.Albert.HermitianSpecification

open Composition.Specification
open Composition.AdjointSpecification (conjugate)
open scoped TensorProduct Matrix

set_option linter.checkUnivs false

universe u v w

abbrev Mat (A : Type v) := Matrix (Fin 3) (Fin 3) A
abbrev Coordinates (R : Type u) (A : Type v) := (Fin 3 → R) × (Fin 3 → A)

def cyclicNext (i : Fin 3) : Fin 3 := i + 1
def cyclicPrev (i : Fin 3) : Fin 3 := i + 2

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]

/-- The matrix unit \(E_{ii}\). -/
def diagonalIdempotent (i : Fin 3) : Mat A := Matrix.single i i 1

def diagonalIdempotentType :=
  ∀ {A : Type v} [NonAssocRing A], Fin 3 → Mat A

/-- The two entries for the block with cyclic indices \(i,j,\ell\). -/
def block (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (i : Fin 3) (c : A) : Mat A :=
  Matrix.single (cyclicNext i) (cyclicPrev i) ((γ (cyclicPrev i) : R) • c) +
    Matrix.single (cyclicPrev i) (cyclicNext i) ((γ (cyclicNext i) : R) • conjugate n c)

def blockType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → Fin 3 → A → Mat A

/-- The entrywise coefficient of \(\Gamma x\Gamma^{-1}\). -/
def weight (γ : Fin 3 → Rˣ) (i j : Fin 3) : R := (γ i * (γ j)⁻¹ : Rˣ)

/-- The source equation, entry by entry, together with the scalar diagonal. -/
def hermitian (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) : Submodule R (Mat A) where
  carrier := {x | (∀ i j, conjugate n (x j i) = weight γ i j • x i j) ∧
    ∀ i, ∃ r : R, r • (1 : A) = x i i}
  zero_mem' := by
    exact ⟨fun _ _ => by simp, fun _ => ⟨0, zero_smul _ _⟩⟩
  add_mem' := by
    rintro x y ⟨hx, dx⟩ ⟨hy, dy⟩
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · change conjugate n (x j i + y j i) = weight γ i j • (x i j + y i j)
      rw [map_add, hx, hy, smul_add]
    · obtain ⟨a, ha⟩ := dx i
      obtain ⟨b, hb⟩ := dy i
      exact ⟨a + b, by simp only [add_smul, ha, hb, Matrix.add_apply]⟩
  smul_mem' := by
    rintro r x ⟨hx, dx⟩
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · change conjugate n (r • x j i) = weight γ i j • (r • x i j)
      rw [map_smul, hx, smul_comm]
    · obtain ⟨a, ha⟩ := dx i
      exact ⟨r * a, by rw [mul_smul, ha]; rfl⟩

def hermitianType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → Submodule R (Mat A)

/-- The displayed matrix in NA13-C04.01, with indices shifted to Fin 3. -/
def assemble (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (p : Coordinates R A) : Mat A :=
  !![p.1 0 • (1 : A), (γ 1 : R) • p.2 2, (γ 2 : R) • conjugate n (p.2 1);
     (γ 0 : R) • conjugate n (p.2 2), p.1 1 • (1 : A), (γ 2 : R) • p.2 0;
     (γ 0 : R) • p.2 1, (γ 1 : R) • conjugate n (p.2 0), p.1 2 • (1 : A)]

def assembleType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → Coordinates R A → Mat A

def matrixDescription : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (x : Mat A),
    x ∈ hermitian n γ ↔
      (x.map (conjugate n))ᵀ =
        (Matrix.diagonal fun i => (γ i : R) • (1 : A)) * x *
          (Matrix.diagonal fun i => (((γ i)⁻¹ : Rˣ) : R) • (1 : A)) ∧
      ∀ i, ∃ r : R, r • (1 : A) = x i i

def diagonalIdempotentMem : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} [IsScalarTower R A A] [SMulCommClass R A A], OctonionNormConditions n →
    ∀ (γ : Fin 3 → Rˣ) i, diagonalIdempotent (A := A) i ∈ hermitian n γ

def diagonalIdempotentLaw : Prop :=
  ∀ {A : Type v} [NonAssocRing A] (i : Fin 3), diagonalIdempotent (A := A) i * diagonalIdempotent i = diagonalIdempotent i

def blockMem : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} [IsScalarTower R A A] [SMulCommClass R A A], OctonionNormConditions n →
    ∀ (γ : Fin 3 → Rˣ) i c, block n γ i c ∈ hermitian n γ

def coordinatesSum : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (p : Coordinates R A),
    assemble n γ p = ∑ i, (p.1 i • diagonalIdempotent i + block n γ i (p.2 i))

def coordinatesDecomposition : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} [IsScalarTower R A A] [SMulCommClass R A A], OctonionNormConditions n → ∀ γ : Fin 3 → Rˣ,
    ∃ e : Coordinates R A ≃ₗ[R] hermitian n γ,
      ∀ p, (e p : Mat A) = assemble n γ p

def ringRank : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} [IsScalarTower R A A] [SMulCommClass R A A], OctonionNormConditions n → ∀ γ : Fin 3 → Rˣ,
    Module.Finite R (hermitian n γ) ∧ Module.Projective R (hermitian n γ) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (hermitian n γ) p = 27

def fieldDimension : Prop :=
  ∀ {A : Type v} [NonAssocRing A] {k : Type u} [Field k] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] {n : QuadraticForm k A}, OctonionNormConditions n → ∀ γ : Fin 3 → kˣ,
    Module.finrank k (hermitian n γ) = 27

def jordanClosure : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} [IsScalarTower R A A] [SMulCommClass R A A], OctonionNormConditions n →
    ∀ (γ : Fin 3 → Rˣ) (two : Rˣ), (two : R) = 2 →
      ∀ x y : hermitian n γ,
        (((two⁻¹ : Rˣ) : R) • ((x : Mat A) * (y : Mat A) + (y : Mat A) * (x : Mat A)))
          ∈ hermitian n γ

section BaseChange

variable (S : Type w) [CommRing S] [Algebra R S]

/-- Tensoring each entry of a matrix. -/
noncomputable def matrixBaseChange : S ⊗[R] Mat A ≃ₗ[S] Mat (S ⊗[R] A) :=
  TensorProduct.piRight R S S (fun _ : Fin 3 => Fin 3 → A) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => TensorProduct.piRight R S S (fun _ : Fin 3 => A))

def matrixBaseChangeType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (S : Type w) [CommRing S] [Algebra R S], S ⊗[R] Mat A ≃ₗ[S] Mat (S ⊗[R] A)

/-- Tensoring the scalar and octonion coordinates separately. -/
noncomputable def coordinatesBaseChange :
    S ⊗[R] Coordinates R A ≃ₗ[S] Coordinates S (S ⊗[R] A) :=
  TensorProduct.prodRight R S S (Fin 3 → R) (Fin 3 → A) ≪≫ₗ
    (TensorProduct.piScalarRight R S S (Fin 3)).prodCongr
      (TensorProduct.piRight R S S (fun _ : Fin 3 => A))

def coordinatesBaseChangeType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (S : Type w) [CommRing S] [Algebra R S],
    S ⊗[R] Coordinates R A ≃ₗ[S] Coordinates S (S ⊗[R] A)

abbrev baseChangedWeights (γ : Fin 3 → Rˣ) : Fin 3 → Sˣ :=
  fun i => Units.map (algebraMap R S) (γ i)

end BaseChange

/-- Both the matrix inclusion and the coordinate equivalence commute with scalar extension. -/
def hermitianBaseChange : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (S : Type w) [CommRing S] [Algebra R S] [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (h : OctonionNormConditions n) (γ : Fin 3 → Rˣ),
    letI := h.projective
    let M := hermitian n γ
    let M' := hermitian (normBaseChange S n) (baseChangedWeights S γ)
    ∃ (e : S ⊗[R] M ≃ₗ[S] M')
      (f : Coordinates R A ≃ₗ[R] M) (g : Coordinates S (S ⊗[R] A) ≃ₗ[S] M'),
      (∀ p, (f p : Mat A) = assemble n γ p) ∧
      (∀ p, (g p : Mat (S ⊗[R] A)) = assemble (normBaseChange S n) (baseChangedWeights S γ) p) ∧
      (∀ z, (e z : Mat (S ⊗[R] A)) = matrixBaseChange S (M.subtype.baseChange S z)) ∧
      (f.baseChange R S _ _).trans e = (coordinatesBaseChange S).trans g


end LinearAlgebraicGroups.Albert.HermitianSpecification
