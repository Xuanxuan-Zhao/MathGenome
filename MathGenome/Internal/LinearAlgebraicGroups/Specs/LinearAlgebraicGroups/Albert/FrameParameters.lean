import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.QuadraticOperators

/-! The diagonal frame, its multiplication, and changes of Hermitian parameters. -/

namespace LinearAlgebraicGroups.Albert.FrameSpecification

open HermitianSpecification CubicSpecification QuadraticOperatorSpecification
open Composition.Specification (OctonionNormConditions normBaseChange)
open scoped BigOperators TensorProduct

universe u v w

set_option linter.checkUnivs false

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]

def frameAxis (i : Fin 3) : Coordinates R A :=
  diagonalCoordinates (Pi.single i 1)

def frameAxisType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A], Fin 3 → Coordinates R A

def frameType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (n : QuadraticForm R A) (γ : Fin 3 → Rˣ),
    (∑ i, frameAxis (R := R) (A := A) i) = cubicUnit ∧
    (∀ i, assemble n γ (frameAxis i) = diagonalIdempotent i) ∧
    (∀ i (y : Coordinates R A), applyOperator n γ (frameAxis i) y = y.1 i • frameAxis i) ∧
    (∀ i (y : Coordinates R A),
      triple n γ (frameAxis (cyclicNext i)) y (frameAxis (cyclicPrev i)) =
        singleBlockCoordinates i (y.2 i)) ∧
    (∀ i m, applyOperator n γ (frameAxis i) (frameAxis m) =
      if i = m then frameAxis i else 0) ∧
    (∀ i, applyOperator n γ (frameAxis i) cubicUnit = frameAxis i) ∧
    (∀ y : Coordinates R A, (∑ i, (applyOperator n γ (frameAxis i) y +
      triple n γ (frameAxis (cyclicNext i)) y (frameAxis (cyclicPrev i)))) = y)

/-- The linear product is half of the quadratic polarization at the unit. -/
def frameProduct (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (d : Rˣ)
    (x y : Coordinates R A) : Coordinates R A :=
  (↑d⁻¹ : R) • triple n γ x cubicUnit y

def frameProductType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → Rˣ → Coordinates R A → Coordinates R A → Coordinates R A

def productsType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    OctonionNormConditions n → ∀ (γ : Fin 3 → Rˣ) (d : Rˣ), (d : R) = 2 →
    let p := frameProduct n γ d
    let e := frameAxis (R := R) (A := A)
    let b := singleBlockCoordinates (R := R) (A := A)
    let h : R := ↑d⁻¹
    (∀ i m, p (e i) (e m) = if i = m then e i else 0) ∧
    (∀ i a, p (e i) (b i a) = 0) ∧
    (∀ i a, p (e (cyclicNext i)) (b i a) = h • b i a) ∧
    (∀ i a, p (e (cyclicPrev i)) (b i a) = h • b i a) ∧
    (∀ i a c, p (b i a) (b i c) =
      (h * blockWeight γ i * n.polarBilin a c) • (e (cyclicNext i) + e (cyclicPrev i))) ∧
    (∀ i a c, p (b i a) (b (cyclicNext i) c) =
      h • b (cyclicPrev i) ((γ (cyclicPrev i) : R) • Composition.AdjointSpecification.conjugate n (a * c))) ∧
    (∀ x y, assemble n γ (p x y) =
      h • (assemble n γ x * assemble n γ y + assemble n γ y * assemble n γ x))

def baseChangeType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A}
    (h : OctonionNormConditions n) (γ : Fin 3 → Rˣ)
    (B : Type w) [CommRing B] [Algebra R B],
    letI := h.projective
    let q := normBaseChange B n
    let δ := baseChangedWeights B γ
    let f := coordinatesBaseChange (A := A) B
    (∀ i, extendCoordinates B (frameAxis (R := R) (A := A) i) = frameAxis i) ∧
    (∀ i (a : A), extendCoordinates B (singleBlockCoordinates (R := R) i a) =
      singleBlockCoordinates i ((1 : B) ⊗ₜ[R] a)) ∧
    (∀ i (z : B ⊗[R] Coordinates R A),
      let p := ((LinearMap.proj i : (Fin 3 → R) →ₗ[R] R).comp
        (LinearMap.fst R (Fin 3 → R) (Fin 3 → A))).smulRight (frameAxis (R := R) (A := A) i)
      f (p.baseChange B z) = applyOperator q δ (frameAxis i) (f z)) ∧
    (∀ i (z : B ⊗[R] Coordinates R A),
      let p := LinearMap.prod
        (0 : Coordinates R A →ₗ[R] (Fin 3 → R))
        ((LinearMap.single R (fun _ : Fin 3 => A) i).comp
          ((LinearMap.proj i).comp (LinearMap.snd R (Fin 3 → R) (Fin 3 → A))))
      f (p.baseChange B z) = triple q δ (frameAxis (cyclicNext i)) (f z) (frameAxis (cyclicPrev i)))

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The condition for a unital quadratic Jordan isomorphism in Hermitian coordinates.
The two laws are transported by the canonical tensor-coordinate identifications. -/
def IsParameterIso (n : QuadraticForm R A) (h : OctonionNormConditions n)
    (γ γ' : Fin 3 → Rˣ) (F : Coordinates R A ≃ₗ[R] Coordinates R A) : Prop :=
  F cubicUnit = cubicUnit ∧
    ∀ (B : Type u) [CommRing B] [Algebra R B],
      letI := h.projective
      let q := normBaseChange B n
      let e := coordinatesBaseChange (A := A) B
      let G := fun x => e (F.toLinearMap.baseChange B (e.symm x))
      ∀ x y, G (applyOperator q (baseChangedWeights B γ) x y) =
        applyOperator q (baseChangedWeights B γ') (G x) (G y)

def commonScalingType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (h : OctonionNormConditions n) (γ : Fin 3 → Rˣ) (a : Rˣ),
    let γ' := fun i => a * γ i
    ∃ F : Coordinates R A ≃ₗ[R] Coordinates R A,
      IsParameterIso n h γ γ' F ∧ ∀ x, assemble n γ' (F x) = assemble n γ x

def squareScalingType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (h : OctonionNormConditions n)
    (γ s : Fin 3 → Rˣ),
    let γ' := fun i => s i ^ 2 * γ i
    ∃ F : Coordinates R A ≃ₗ[R] Coordinates R A,
      IsParameterIso n h γ γ' F ∧ ∀ x i j,
        assemble n γ' (F x) i j = (↑((s i)⁻¹ * s j) : R) • assemble n γ x i j

def permutationType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (h : OctonionNormConditions n)
    (γ : Fin 3 → Rˣ) (σ : Equiv.Perm (Fin 3)),
    ∃ F : Coordinates R A ≃ₗ[R] Coordinates R A,
      IsParameterIso n h γ (γ ∘ σ) F ∧ ∀ x i j,
        assemble n (γ ∘ σ) (F x) i j = assemble n γ x (σ i) (σ j)

def normalizationType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (h : OctonionNormConditions n) (γ : Fin 3 → Rˣ),
    ∃ (γ' : Fin 3 → Rˣ) (F : Coordinates R A ≃ₗ[R] Coordinates R A),
      weightProduct γ' = 1 ∧ IsParameterIso n h γ γ' F

/-- The map (X\mapsto\Gamma X) to the isotope of the untwisted model.
The target unit is the inverse of (u=\Gamma^{-1}), and its law is
(U^{(u)}_x(y)=U_x(U_u(y))). -/
def isotopeType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (h : OctonionNormConditions n) (γ : Fin 3 → Rˣ),
    let ones : Fin 3 → Rˣ := fun _ => 1
    let u : Coordinates R A := diagonalCoordinates (fun i => ↑(γ i)⁻¹)
    let v : Coordinates R A := diagonalCoordinates (fun i => ↑(γ i))
    ∃ F : Coordinates R A ≃ₗ[R] Coordinates R A,
      (∀ x i j, assemble n ones (F x) i j = (γ i : R) • assemble n γ x i j) ∧
      F cubicUnit = v ∧
      applyOperator n ones u v = u ∧
      (∀ y, applyOperator n ones u (applyOperator n ones v y) = y ∧
        applyOperator n ones v (applyOperator n ones u y) = y) ∧
      (∀ (B : Type u) [CommRing B] [Algebra R B],
        letI := h.projective
        let q := normBaseChange B n
        let e := coordinatesBaseChange (A := A) B
        let G := fun x => e (F.toLinearMap.baseChange B (e.symm x))
        ∀ x y, G (applyOperator q (baseChangedWeights B γ) x y) =
          applyOperator q (fun _ => 1) (G x)
            (applyOperator q (fun _ => 1) (extendCoordinates B u) (G y)))


/-- The frame members are trace-one idempotents with zero adjoint. The
complementary projector fixes the two opposite diagonal axes and their block. -/
def frameComplementsType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (n : QuadraticForm R A) (γ : Fin 3 → Rˣ),
    let e := frameAxis (R := R) (A := A)
    ∀ i, linearTrace n γ (e i) = 1 ∧ cubicAdjoint n γ (e i) = 0 ∧
      (∀ m, i ≠ m → triple n γ (e i) cubicUnit (e m) = 0) ∧
      ∀ y : Coordinates R A, applyOperator n γ (cubicUnit - e i) y =
        y.1 (cyclicNext i) • e (cyclicNext i) + y.1 (cyclicPrev i) • e (cyclicPrev i) +
          singleBlockCoordinates i (y.2 i)

/-- For the untwisted algebra, the operator of (u=\Gamma^{-1}) is the
diagonal sandwich. Polarizing the isotope law at its unit gives the sum of
the two mixed sandwiches, whose half is the isotope product when (2) is a unit. -/
def isotopeSandwichType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A}, OctonionNormConditions n → ∀ (γ : Fin 3 → Rˣ),
    let ones : Fin 3 → Rˣ := fun _ => 1
    let u : Coordinates R A := diagonalCoordinates (fun i => ↑(γ i)⁻¹)
    let M := assemble n ones
    let D := M u
    (∀ y, M (applyOperator n ones u y) = (D * M y) * D) ∧
      (∀ x z, M (triple n ones x u z) = (M x * D) * M z + (M z * D) * M x)

end LinearAlgebraicGroups.Albert.FrameSpecification
