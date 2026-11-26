import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

open CategoryTheory
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.OuterTypeALocalModels

open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras (conjugateTranspose)
open LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open LinearAlgebraicGroups.Specs.OuterTypeAModels
open LinearAlgebraicGroups.Specs.GeneralLinearStructure (SpecialMatrixPoints)
open LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open LinearAlgebraicGroups.Specs.Unipotent (baseChangedAlgebraicGroup)
open _root_.Specs.RM03.CSA (isCentralSimple degree)

section Hermitian

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

/-- The extension of quadratic conjugation to a test algebra. -/
def conjugationAt (σ : E ≃ₐ[F] E) (R : TestAlgebra F) :
    R ⊗[F] E →ₐ[R] R ⊗[F] E :=
  Algebra.TensorProduct.map (.id R R) σ.toAlgHom

/-- The special unitary matrix equation over a test algebra. -/
def PreservesHermitianMatrix (σ : E ≃ₐ[F] E) {n : ℕ}
    (H : Mat E n) (R : TestAlgebra F)
    (g : Matrix.SpecialLinearGroup (Fin n) (R ⊗[F] E)) : Prop :=
  let H' := H.map (Algebra.TensorProduct.includeRight (R := F) (A := R))
  (g.val.map (conjugationAt σ R)).transpose * H' * g.val = H'

/-- The multiplication and coefficient maps are those of the special unitary
matrix functor on all commutative test algebras. -/
def RepresentsHermitian {n : ℕ} (σ : E ≃ₐ[F] E) (H : Mat E n)
    (G : AffineAlgebraicGroup F) : Prop :=
  ∃ e : ∀ R : TestAlgebra F, GroupPoints G.val R ≃
      {g : Matrix.SpecialLinearGroup (Fin n) (R ⊗[F] E) // PreservesHermitianMatrix σ H R g},
    (∀ R x y, (e R (x * y)).val = (e R x).val * (e R y).val) ∧
    ∀ {R S : TestAlgebra F} (f : R ⟶ S) x,
      (e S (mapPoints f x)).val = Matrix.SpecialLinearGroup.map
        (Algebra.TensorProduct.map f.hom (.id F E)).toRingHom (e R x).val

end Hermitian

section Local

open Algebra.TensorProduct (includeRight)

variable {K E F A : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]

/-- The field centre is the scalar extension of the global centre, and its
conjugation extends that of the original unitary algebra. The size of the
Hermitian matrix is the degree of the original algebra. -/
def NonsplitModel (star : SecondKind K E A) (G : AffineAlgebraicGroup K) : Prop :=
  ∃ (Q : Type u) (_ : Field Q) (_ : Algebra F Q) (_ : Algebra.IsSeparable F Q)
    (c : (F ⊗[K] E) ≃ₐ[F] Q),
    Module.finrank F Q = 2 ∧
    ∃ (σ : Q ≃ₐ[F] Q) (H : (Mat Q (degree E A))ˣ),
      σ ≠ 1 ∧
      (∀ a : E, σ (c (includeRight a)) = c (includeRight (star.conjugation a))) ∧
      conjugateTranspose σ H.val = H.val ∧
      (letI : Algebra E Q := (c.toRingHom.comp
        (includeRight (R := K) (A := F) (B := E)).toRingHom).toAlgebra
       ∃ e : (Q ⊗[E] A) ≃ₐ[Q] Mat Q (degree E A),
         ∀ a : A, e (1 ⊗ₜ[E] (star.adjoint a).unop) =
           (↑H⁻¹ : Mat Q (degree E A)) * conjugateTranspose σ (e (1 ⊗ₜ[E] a)) * H.val) ∧
      RepresentsHermitian σ H.val (baseChangedAlgebraicGroup F G) ∧
      (((∃ c : Cocharacter G.val, IsNoncentral c) ∨
          (∃ c : Cocharacter (baseChangedAlgebraicGroup F G).val, IsNoncentral c)) →
        ∃ x : Fin (degree E A) → Q, x ≠ 0 ∧ dotProduct (σ ∘ x) (H.val.mulVec x) = 0)

/-- The two projections of the split centre are the chosen embedding and its
conjugate. The group is the norm-one group of the corresponding factor. -/
def SplitModel (star : SecondKind K E A) (_hA : isCentralSimple E A)
    {ι : Type u} [Fintype ι] (b : Module.Basis ι E A) (G : AffineAlgebraicGroup K) : Prop :=
  ∃ j : E →ₐ[K] F,
    letI : Algebra E F := j.toRingHom.toAlgebra
    let c := Algebra.TensorProduct.lift (AlgHom.id F F) j (fun _ _ => Commute.all _ _)
    Function.Bijective (c.prod (c.comp (Algebra.TensorProduct.map (.id F F)
      star.conjugation.toAlgHom))) ∧
    ∃ hF : isCentralSimple F (F ⊗[E] A),
      degree F (F ⊗[E] A) = degree E A ∧
      RepresentsNormOne hF (b.baseChange F) (baseChangedAlgebraicGroup F G)

/-- Scalar extension of the given global unitary algebra at every completion,
with the two alternatives for its quadratic centre. -/
def UnitaryLocalModels : Prop :=
  ∀ {K E A : Type u} [Field K] [Field E] [Algebra K E]
    [Algebra.IsQuadraticExtension K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    (hA : isCentralSimple E A) {ι : Type u} [Fintype ι] (b : Module.Basis ι E A)
    (star : SecondKind K E A) (G : AffineAlgebraicGroup K),
    RepresentsUnitary hA b star G →
    ∀ (D : GlobalFieldData.{u,v} K) (w : D.Place),
      NonsplitModel (F := D.Completion w) star G ∨ SplitModel (F := D.Completion w) star hA b G

end Local

/-- The models come from the even subgroup of the character of the specified
finite Galois matrix trivialization, with the original odd action as adjoint. -/
def LocalModelsForTrivialization : Prop :=
  ∀ {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {n : ℕ}, 3 ≤ n →
    ∀ {S G : AffineAlgebraicGroup K} (s : SpecialMatrixPoints S n)
      (i : (groupBaseChange K L).obj S.val ≅ (groupBaseChange K L).obj G.val)
      (χ : DiagramCharacter K L) (g : Gal(L/K) → GL (Unipotent.Index.{u} n) L),
      HasMatrixTransport s i χ g → Function.Surjective χ →
      ∃ (g' : Gal(L/K) → GL (Unipotent.Index.{u} n) L)
        (β : ∀ τ : Gal(L/K), MatrixLift n τ (χ τ)),
        HasMatrixTransport s i χ g' ∧
        (∀ τ x, (β τ).toAddEquiv x =
          (g' τ).val.submatrix ULift.up ULift.up *
            (if χ τ = 1 then x.map τ else (x.map τ).transpose) *
            (g' τ)⁻¹.val.submatrix ULift.up ULift.up) ∧
        let E := DiagramField χ
        Module.finrank K E = 2 ∧ Algebra.IsSeparable K E ∧
        ∃ ρ : RM03.Brauer.SemilinearDescent.AlgebraAction E L (Mat L n),
          (∀ (τ : χ.ker) x, ρ.act (IntermediateField.subgroupEquivAlgEquiv χ.ker τ) x =
            (β τ.val).toAddEquiv x) ∧
          let A := ρ.fixedSubalgebra
          ∃ hA : isCentralSimple E A, degree E A = n ∧
            ∃ star : SecondKind K E A,
              (∀ (τ : Gal(L/K)) (_ : χ τ ≠ 1) (x : A),
                ((star.adjoint x).unop : Mat L n) = (β τ).toAddEquiv x.val) ∧
              (∀ (τ : Gal(L/K)) (_ : χ τ ≠ 1) (a : E), (star.conjugation a : L) = τ (a : L)) ∧
              ∃ (ι : Type u) (_ : Fintype ι) (b : Module.Basis ι E A),
                RepresentsUnitary hA b star G ∧
                ∀ (D : GlobalFieldData.{u,v} K) (w : D.Place),
                  NonsplitModel (F := D.Completion w) star G ∨
                    SplitModel (F := D.Completion w) star hA b G

end LinearAlgebraicGroups.Specs.Arithmetic.OuterTypeALocalModels
