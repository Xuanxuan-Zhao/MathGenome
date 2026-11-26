import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.QuadraticOperators
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.ZornModel
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.Idempotents

/-! Untwisted Hermitian models over the scalar, split quadratic, split quaternion,
and Zorn algebras. The scalar norm is defined over every commutative ring. -/

namespace LinearAlgebraicGroups.Albert.LowerRankSpecification

open _root_.LinearAlgebraicGroups.Composition
open Composition.AdjointSpecification (conjugate trace)
open HermitianSpecification CubicSpecification QuadraticOperatorSpecification
open scoped Matrix TensorProduct

universe u v

abbrev SplitQuaternion (R : Type u) := Matrix (Fin 2) (Fin 2) R

abbrev untwisted (R : Type u) [CommRing R] : Fin 3 → Rˣ := fun _ => 1

def pairNorm (R : Type u) [CommRing R] : QuadraticForm R (R × R) :=
  QuadraticMap.linMulLin (LinearMap.fst R R R) (LinearMap.snd R R R)

abbrev scalarNorm := Composition.Specification.scalarNorm
abbrev quaternionNorm := ZornSpecification.matrixDetNorm
abbrev zornNorm := ZornSpecification.norm

section Embeddings

variable (R : Type u) [CommRing R]

def scalarEmbedding : R →ₗ[R] Zorn R :=
  (Zorn.coordinates R).symm.toLinearMap.comp
    (LinearMap.id.prod ((0 : R →ₗ[R] Fin 3 → R).prod
      ((0 : R →ₗ[R] Fin 3 → R).prod LinearMap.id)))

def pairEmbedding : (R × R) →ₗ[R] Zorn R :=
  (Zorn.coordinates R).symm.toLinearMap.comp
    ((LinearMap.fst R R R).prod ((0 : (R × R) →ₗ[R] Fin 3 → R).prod
      ((0 : (R × R) →ₗ[R] Fin 3 → R).prod (LinearMap.snd R R R))))

def quaternionEmbedding : SplitQuaternion R →ₗ[R] Zorn R :=
  let e := Matrix.entryLinearMap R R
  let axis := LinearMap.single R (fun _ : Fin 3 => R) 0
  (Zorn.coordinates R).symm.toLinearMap.comp
    ((e 0 0).prod ((axis.comp (e 0 1)).prod ((axis.comp (e 1 0)).prod (e 1 1))))

def scalarProjection : Zorn R →ₗ[R] R :=
  (LinearMap.fst R _ _).comp (Zorn.coordinates R).toLinearMap

def pairProjection : Zorn R →ₗ[R] R × R :=
  { toFun := fun x => ((Zorn.coordinates R x).1, (Zorn.coordinates R x).2.2.2)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def quaternionProjection : Zorn R →ₗ[R] SplitQuaternion R :=
  { toFun := fun x =>
      let (a, u, v, b) := Zorn.coordinates R x
      !![a, u 0; v 0, b]
    map_add' := by
      intro x y
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    map_smul' := by
      intro r x
      ext i j
      fin_cases i <;> fin_cases j <;> rfl }

end Embeddings

section Formulas

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]

/-- Keep the scalar diagonal and apply the same linear map in each off-diagonal block. -/
def mapBlocks {D : Type*} [AddCommGroup D] [Module R D] (e : C →ₗ[R] D) :
    Coordinates R C →ₗ[R] Coordinates R D :=
  (LinearMap.fst R _ _).prod
    (LinearMap.pi fun i => e.comp ((LinearMap.proj i).comp (LinearMap.snd R _ _)))

/-- A split linear inclusion preserving the norm and the unital multiplication. -/
def embeddingLaws (n : QuadraticForm R C) (e : C →ₗ[R] Zorn R) (p : Zorn R →ₗ[R] C) : Prop :=
  p.comp e = LinearMap.id ∧ e 1 = 1 ∧ (∀ x y, e (x * y) = e x * e y) ∧
    (∀ x, zornNorm R (e x) = n x) ∧ (∀ x, e (conjugate n x) = conjugate (zornNorm R) (e x))

def scalarMatrix (x : Coordinates R R) : Mat R :=
  !![x.1 0, x.2 2, x.2 1; x.2 2, x.1 1, x.2 0; x.2 1, x.2 0, x.1 2]

def scalarAdjoint (x : Coordinates R R) : Coordinates R R :=
  (fun i => x.1 (cyclicNext i) * x.1 (cyclicPrev i) - x.2 i ^ 2,
   fun i => x.2 (cyclicNext i) * x.2 (cyclicPrev i) - x.1 i * x.2 i)

end Formulas

def embeddingsType : Prop :=
  ∀ (R : Type u) [CommRing R],
    embeddingLaws (scalarNorm R) (scalarEmbedding R) (scalarProjection R) ∧
    embeddingLaws (pairNorm R) (pairEmbedding R) (pairProjection R) ∧
    embeddingLaws (quaternionNorm R) (quaternionEmbedding R) (quaternionProjection R)

def compositionFormulasType : Prop :=
  ∀ (R : Type u) [CommRing R],
    (∀ a : R, scalarNorm R a = a ^ 2 ∧ conjugate (scalarNorm R) a = a) ∧
    (∀ a b : R, pairNorm R (a, b) = a * b ∧ conjugate (pairNorm R) (a, b) = (b, a)) ∧
    (∀ x : SplitQuaternion R, quaternionNorm R x = x.det ∧
      conjugate (quaternionNorm R) x = x.adjugate)

def scalarAdjointType : Prop :=
  ∀ (R : Type u) [CommRing R] (x : Coordinates R R),
    cubicAdjoint (scalarNorm R) (untwisted R) x = scalarAdjoint x

def scalarTraceType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ((scalarNorm R).polarBilin.IsPerfPair ↔ IsUnit (2 : R)) ∧
    ((tracePairing (scalarNorm R) (untwisted R)).IsPerfPair ↔ IsUnit (2 : R)) ∧
    ((2 : R) = 0 → ∀ (c : Fin 3 → R) (y : Coordinates R R),
      tracePairing (scalarNorm R) (untwisted R) (0, c) y = 0) ∧
    ((2 : R) = 0 → Nontrivial R →
      ¬(tracePairing (scalarNorm R) (untwisted R)).Nondegenerate)

def scalarSandwichType : Prop :=
  ∀ (R : Type u) [CommRing R] (x y : Coordinates R R),
    scalarMatrix (applyOperator (scalarNorm R) (untwisted R) x y) =
      scalarMatrix x * scalarMatrix y * scalarMatrix x

def scalarMatrixType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ e : Coordinates R R ≃ₗ[R] hermitian (scalarNorm R) (untwisted R),
      (∀ x, (e x : Mat R) = scalarMatrix x) ∧
      (∀ X : Mat R, X ∈ hermitian (scalarNorm R) (untwisted R) ↔ X.IsSymm)

section Agreement

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
variable (n : QuadraticForm R C)

/-- The common untwisted formulas transported by a map of composition inputs. -/
def formulaAgreement {D : Type*} [NonAssocRing D] [Module R D]
    (m : QuadraticForm R D) (e : C →ₗ[R] D) : Prop :=
  let w := untwisted R
  mapBlocks e cubicUnit = cubicUnit ∧
  (∀ x, cubicNorm m w (mapBlocks e x) = cubicNorm n w x) ∧
  (∀ x, cubicAdjoint m w (mapBlocks e x) = mapBlocks e (cubicAdjoint n w x)) ∧
  (∀ x y, tracePairing m w (mapBlocks e x) (mapBlocks e y) = tracePairing n w x y) ∧
  (∀ x y, applyOperator m w (mapBlocks e x) (mapBlocks e y) =
    mapBlocks e (applyOperator n w x y)) ∧
  (∀ x, assemble m w (mapBlocks e x) = (assemble n w x).map e)

/-- The unital quadratic Jordan law is the restriction of the Zorn law, with the
same cubic formula on scalar extensions of the coordinates. -/
def restrictedModel [IsScalarTower R C C] [SMulCommClass R C C] [Module.Projective R C]
    (e : C →ₗ[R] Zorn R) : Prop :=
  ∃ J : Specs.LinearAlgebraicGroups.Albert.QuadraticJordan R (Coordinates R C),
    J.unit = cubicUnit ∧
    (∀ x y, J.groundOp x y = applyOperator n (untwisted R) x y) ∧
    (∀ (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] Coordinates R C),
      coordinatesBaseChange S (J.op S x y) =
        applyOperator (Composition.Specification.normBaseChange S n) (untwisted S)
          (coordinatesBaseChange S x) (coordinatesBaseChange S y)) ∧
    formulaAgreement n (zornNorm R) e ∧
    (∀ (S : Type u) [CommRing S] [Algebra R S],
      formulaAgreement (Composition.Specification.normBaseChange S n)
        (zornNorm S) ((ZornSpecification.baseChange R S).toLinearMap.comp (e.baseChange S)))

end Agreement

def restrictedModelsType : Prop :=
  ∀ (R : Type u) [CommRing R],
    restrictedModel (scalarNorm R) (scalarEmbedding R) ∧
    restrictedModel (pairNorm R) (pairEmbedding R) ∧
    restrictedModel (quaternionNorm R) (quaternionEmbedding R) ∧
    restrictedModel (zornNorm R) (LinearMap.id : Zorn R →ₗ[R] Zorn R)

def matrixModel {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
    (n : QuadraticForm R C) (r : ℕ) : Prop :=
  ∃ f : Coordinates R C ≃ₗ[R] hermitian n (untwisted R),
    (∀ x, (f x : Mat C) = assemble n (untwisted R) x) ∧
    Module.Finite R (hermitian n (untwisted R)) ∧
    Module.Free R (hermitian n (untwisted R)) ∧
    ∀ p : PrimeSpectrum R, Module.rankAtStalk (hermitian n (untwisted R)) p = r

def matrixModelsType : Prop :=
  ∀ (R : Type u) [CommRing R],
    matrixModel (scalarNorm R) 6 ∧ matrixModel (pairNorm R) 9 ∧
    matrixModel (quaternionNorm R) 15 ∧ matrixModel (zornNorm R) 27


/-- Comparison with the standard model over the new base ring. The block map
is also used to compare the cubic and matrix operations. -/
def nativeBaseChange {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {C : Type u} {D : Type v} [NonAssocRing C] [Module R C] [Module.Projective R C]
    [IsScalarTower R C C] [SMulCommClass R C C] [NonAssocRing D] [Module S D]
    (n : QuadraticForm R C) (m : QuadraticForm S D)
    (e : C →ₗ[R] Zorn R) (f : D →ₗ[S] Zorn S) : Prop :=
  ∃ b : (S ⊗[R] C) ≃ₗ[S] D,
    (∀ z, f (b z) = ZornSpecification.baseChange R S (e.baseChange S z)) ∧
    formulaAgreement (Composition.Specification.normBaseChange S n) m b.toLinearMap

def nativeBaseChangesType : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S],
    nativeBaseChange (scalarNorm R) (scalarNorm S) (scalarEmbedding R) (scalarEmbedding S) ∧
    nativeBaseChange (pairNorm R) (pairNorm S) (pairEmbedding R) (pairEmbedding S) ∧
    nativeBaseChange (quaternionNorm R) (quaternionNorm S)
      (quaternionEmbedding R) (quaternionEmbedding S) ∧
    nativeBaseChange (zornNorm R) (zornNorm S) LinearMap.id LinearMap.id


section Components

variable {I : Type u} (B : I → Type u) [∀ i, CommRing (B i)]
variable (C : I → Type u) [∀ i, NonAssocRing (C i)] [∀ i, Module (B i) (C i)]

/-- Each factor is a module over the product ring via its coordinate projection. -/
abbrev componentModule (i : I) : Module (∀ i, B i) (C i) :=
  Module.compHom (C i) (Pi.evalRingHom B i)

/-- Project the scalar and off-diagonal coordinates onto a specified factor. -/
def componentCoordinates (x : Coordinates (∀ i, B i) (∀ i, C i)) (i : I) :
    Coordinates (B i) (C i) := (fun j => x.1 j i, fun j => x.2 j i)

/-- The composition inputs may vary independently among the split types on the factors. -/
def componentModels [∀ i, IsScalarTower (B i) (C i) (C i)]
    [∀ i, SMulCommClass (B i) (C i) (C i)] (n : ∀ i, QuadraticForm (B i) (C i)) : Prop :=
  letI (i : I) := componentModule B C i
  letI : IsScalarTower (∀ i, B i) (∀ i, C i) (∀ i, C i) :=
    ⟨fun r x y => funext fun i => smul_mul_assoc (r i) (x i) (y i)⟩
  letI : SMulCommClass (∀ i, B i) (∀ i, C i) (∀ i, C i) :=
    ⟨fun r x y => funext fun i => smul_comm (r i) (x i) (y i)⟩
  Function.Bijective (componentCoordinates B C) ∧
  ∃ (N : QuadraticForm (∀ i, B i) (∀ i, C i))
    (hP : Module.Projective (∀ i, B i) (∀ i, C i)),
    letI := hP
    ∃ J : Specs.LinearAlgebraicGroups.Albert.QuadraticJordan (∀ i, B i)
        (Coordinates (∀ i, B i) (∀ i, C i)),
      J.unit = cubicUnit ∧
      (∀ x i, N x i = n i (x i)) ∧
      (∀ x y, J.groundOp x y = applyOperator N (untwisted _) x y) ∧
      (∀ (S : Type u) [CommRing S] [Algebra (∀ i, B i) S]
        (x y : S ⊗[∀ i, B i] Coordinates (∀ i, B i) (∀ i, C i)),
        coordinatesBaseChange S (J.op S x y) =
          applyOperator (Composition.Specification.normBaseChange S N) (untwisted S)
            (coordinatesBaseChange S x) (coordinatesBaseChange S y)) ∧
      (∀ i x,
        cubicNorm N (untwisted _) x i =
          cubicNorm (n i) (untwisted _) (componentCoordinates B C x i)) ∧
      (∀ i x,
        componentCoordinates B C (cubicAdjoint N (untwisted _) x) i =
          cubicAdjoint (n i) (untwisted _) (componentCoordinates B C x i)) ∧
      (∀ i x y,
        tracePairing N (untwisted _) x y i =
          tracePairing (n i) (untwisted _) (componentCoordinates B C x i)
            (componentCoordinates B C y i)) ∧
      (∀ i x y,
        componentCoordinates B C (J.groundOp x y) i =
          applyOperator (n i) (untwisted _) (componentCoordinates B C x i)
            (componentCoordinates B C y i))

end Components

def componentModelsType : Prop :=
  ∀ (I : Type u) [Fintype I] (B C : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, NonAssocRing (C i)] [∀ i, Module (B i) (C i)]
    [∀ i, IsScalarTower (B i) (C i) (C i)] [∀ i, SMulCommClass (B i) (C i) (C i)]
    (n : ∀ i, QuadraticForm (B i) (C i))
    (e : ∀ i, C i →ₗ[B i] Zorn (B i)) (p : ∀ i, Zorn (B i) →ₗ[B i] C i),
    (∀ i, embeddingLaws (n i) (e i) (p i)) → componentModels B C n

def idempotentDecompositionType : Prop :=
  ∀ (R I : Type u) [CommRing R] [Fintype I] (a : I → R), CompleteOrthogonalIdempotents a →
    ∃ f : R ≃+* ∀ i, R ⧸ Ideal.span {1 - a i},
      ∀ x i, f x i = Ideal.Quotient.mk (Ideal.span {1 - a i}) x

/-- When two is a unit, polarizing the quadratic law gives the symmetrized
matrix product in the same Hermitian coordinates. -/
def matrixProduct {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
    (n : QuadraticForm R C) : Prop :=
  ∀ (J : Specs.LinearAlgebraicGroups.Albert.QuadraticJordan R (Coordinates R C)),
    J.unit = cubicUnit →
    (∀ x y, J.groundOp x y = applyOperator n (untwisted R) x y) →
    ∀ (d : Rˣ), (d : R) = 2 → ∀ x y,
      assemble n (untwisted R) (J.groundProduct d x y) =
        (↑d⁻¹ : R) • (assemble n (untwisted R) x * assemble n (untwisted R) y +
          assemble n (untwisted R) y * assemble n (untwisted R) x)

def matrixProductsType : Prop :=
  ∀ (R : Type u) [CommRing R],
    matrixProduct (scalarNorm R) ∧ matrixProduct (pairNorm R) ∧
    matrixProduct (quaternionNorm R) ∧ matrixProduct (zornNorm R)

def regularTraceType : Prop :=
  ∀ (R : Type u) [CommRing R],
    (pairNorm R).polarBilin.IsPerfPair ∧ (quaternionNorm R).polarBilin.IsPerfPair ∧
    (tracePairing (pairNorm R) (untwisted R)).IsPerfPair ∧
    (tracePairing (quaternionNorm R) (untwisted R)).IsPerfPair ∧
    (tracePairing (zornNorm R) (untwisted R)).IsPerfPair

end LinearAlgebraicGroups.Albert.LowerRankSpecification
