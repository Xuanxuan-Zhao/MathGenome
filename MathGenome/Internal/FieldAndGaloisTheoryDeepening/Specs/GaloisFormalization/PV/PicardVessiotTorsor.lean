import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTensor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.MatrixGroupCoordinates
import Mathlib.RingTheory.TensorProduct.Maps

/-! The matrix realization and the actions in Theorem 2.2. -/
namespace GaloisFormalization.PV.Specs

open scoped Matrix TensorProduct MatrixGroupCoordinates.Specs
open Matrix (GeneralLinearGroup)
open Algebra.TensorProduct (lift)

universe u v

noncomputable section

section Definitions

variable {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
  [Algebra K R] {n : ℕ}

/-- Base-algebra automorphisms commuting with the specified operator, with
multiplication given by composition. -/
def operatorAutomorphisms (K : Type u) [Field K] {R : Type v} [CommRing R]
    [Algebra K R] (E : operator kind R) : Subgroup (R ≃ₐ[K] R) where
  carrier := {τ | commutes E E τ}
  one_mem' := fun _ => rfl
  mul_mem' {τ υ} hτ hυ := by
    intro x
    change τ (υ (apply E x)) = apply E (τ (υ x))
    rw [hυ x, hτ (υ x)]
  inv_mem' {τ} hτ := by
    intro x
    change τ.symm (apply E x) = apply E (τ.symm x)
    apply τ.injective
    rw [AlgEquiv.apply_symm_apply, hτ, AlgEquiv.apply_symm_apply]

variable (δ : operatorField kind K) (E : operator kind R) (Y : GL (Fin n) R)

local notation "C" => constantSubfield δ

/-- The inclusion of base constants into the extension. -/
private abbrev constantsIn : C →+* R :=
  (algebraMap K R).comp (constantSubfield δ).subtype

private theorem fixesConstantMatrices (τ : R ≃ₐ[K] R) (g : GL (Fin n) C) :
    GeneralLinearGroup.map τ.toRingHom (GeneralLinearGroup.map (constantsIn δ) g) =
      GeneralLinearGroup.map (constantsIn δ) g := by
  have h : τ.toRingHom.comp (constantsIn δ (R := R)) = constantsIn δ := by
    ext c
    exact τ.commutes (c : K)
  rw [← GeneralLinearGroup.map_comp_apply, ← GeneralLinearGroup.map_comp, h]

private theorem map_mul_automorphisms (τ υ : R ≃ₐ[K] R) (W : GL (Fin n) R) :
    GeneralLinearGroup.map (τ * υ).toRingHom W =
      GeneralLinearGroup.map τ.toRingHom (GeneralLinearGroup.map υ.toRingHom W) := by
  rfl

/-- The actual matrices of operator automorphisms in the chosen fundamental matrix. -/
def matrixGaloisGroup : Subgroup (GL (Fin n) C) where
  carrier := {g | ∃ τ : operatorAutomorphisms K E,
    GeneralLinearGroup.map τ.val.toRingHom Y =
      Y * GeneralLinearGroup.map (constantsIn δ) g}
  one_mem' := by
    refine ⟨1, ?_⟩
    change GeneralLinearGroup.map (RingHom.id R) Y =
      Y * GeneralLinearGroup.map (constantsIn δ) 1
    simp
  mul_mem' := by
    rintro g h ⟨τ, hτ⟩ ⟨υ, hυ⟩
    refine ⟨τ * υ, ?_⟩
    change GeneralLinearGroup.map (τ.val * υ.val).toRingHom Y =
      Y * GeneralLinearGroup.map (constantsIn δ) (g * h)
    rw [map_mul_automorphisms, hυ, map_mul, hτ, fixesConstantMatrices, map_mul, mul_assoc]
  inv_mem' := by
    rintro g ⟨τ, hτ⟩
    refine ⟨τ⁻¹, ?_⟩
    have h := congrArg (GeneralLinearGroup.map τ.val.symm.toRingHom) hτ
    change GeneralLinearGroup.map (τ.val.symm * τ.val).toRingHom Y =
      GeneralLinearGroup.map τ.val.symm.toRingHom
        (Y * GeneralLinearGroup.map (constantsIn δ) g) at h
    rw [← AlgEquiv.aut_inv, inv_mul_cancel] at h
    change Y = _ at h
    rw [map_mul, fixesConstantMatrices] at h
    change GeneralLinearGroup.map τ.val.symm.toRingHom Y =
      Y * GeneralLinearGroup.map (constantsIn δ) g⁻¹
    rw [map_inv]
    exact (eq_mul_inv_iff_mul_eq).2 h.symm

/-- The action on the ring, specified by the automorphism whose right multiplier is g. -/
def matrixAutomorphism (g : matrixGaloisGroup δ E Y) : operatorAutomorphisms K E :=
  Classical.choose g.property

/-- The action on the total ring, obtained by extension to the actual localization. -/
def matrixFractionAutomorphism (g : matrixGaloisGroup δ E Y) :
    totalQuotientRing R ≃+* totalQuotientRing R :=
  fractionRingEquiv (matrixAutomorphism δ E Y g).val.toRingEquiv

/-- The relations of the tensor ratio, in the common coordinate polynomial ring. -/
def tensorRatioRelations : Ideal (MatrixGroupCoordinates.Specs.CoordinatePolynomial C n) :=
  letI : Algebra C R := Algebra.compHom R (constantSubfield δ).subtype
  RingHom.ker (MatrixGroupCoordinates.Specs.evalAt (tensorRatio K Y))

end Definitions

section Types

set_option linter.checkUnivs false

def operatorAutomorphismsType :=
  {kind : OperatorKind} → (K : Type u) → [Field K] →
    {R : Type v} → [CommRing R] → [Algebra K R] →
    operator kind R → Subgroup (R ≃ₐ[K] R)

def matrixGaloisGroupType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] →
    {R : Type v} → [CommRing R] → [Algebra K R] → {n : ℕ} →
    (δ : operatorField kind K) → operator kind R → GL (Fin n) R →
    Subgroup (GL (Fin n) (constantSubfield δ))

def matrixAutomorphismType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] →
    {R : Type v} → [CommRing R] → [Algebra K R] → {n : ℕ} →
    (δ : operatorField kind K) → (E : operator kind R) → (Y : GL (Fin n) R) →
    matrixGaloisGroup δ E Y → operatorAutomorphisms K E

def matrixFractionAutomorphismType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] →
    {R : Type v} → [CommRing R] → [Algebra K R] → {n : ℕ} →
    (δ : operatorField kind K) → (E : operator kind R) → (Y : GL (Fin n) R) →
    matrixGaloisGroup δ E Y → (totalQuotientRing R ≃+* totalQuotientRing R)

def tensorRatioRelationsType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] →
    {R : Type v} → [CommRing R] → [Algebra K R] → {n : ℕ} →
    (δ : operatorField kind K) → GL (Fin n) R →
    Ideal (MatrixGroupCoordinates.Specs.CoordinatePolynomial (constantSubfield δ) n)

end Types

section Theorems

open MatrixGroupCoordinates.Specs (CoordinateRing coordinateMap evalAt IsAlgebraicSubgroup
  vanishingIdeal zeroLocus)

/-- The chosen automorphisms are unique and give the action of the matrix group on the ring. -/
def galoisRingAction : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotRing δ A E → isFundamental A E Y →
    let G := matrixGaloisGroup δ E Y
    ∃ e : G ≃* operatorAutomorphisms K E,
      (∀ g, e g = matrixAutomorphism δ E Y g) ∧
      ∀ g τ, e g = τ ↔ GeneralLinearGroup.map τ.val.toRingHom Y =
        Y * GeneralLinearGroup.map (constantsIn δ) g.val

/-- Evaluation sends the entries of the tensor ratio to the matrix of an
automorphism. Its inverse restricts the map sending a ⊗ b to a * τ b to D. -/
def galoisEvaluation : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotRing δ A E → isFundamental A E Y →
    let C := constantSubfield δ
    let D := picardVessiotCoordinateAlgebra δ Y
    let G := matrixGaloisGroup δ E Y
    ∃ B : GL (Fin n) D, GeneralLinearGroup.map D.val.toRingHom B = tensorRatio K Y ∧
      ∃ e : (D →ₐ[C] C) ≃ G,
        (∀ f, (e f).val = GeneralLinearGroup.map f.toRingHom B) ∧
        ∀ (g : G) (d : D), constantsIn δ (e.symm g d) =
          lift (AlgHom.id K R) (matrixAutomorphism δ E Y g).val.toAlgHom
            (fun _ _ => Commute.all _ _) (d : R ⊗[K] R)

/-- The matrix subgroup is the zero locus of the relations of the tensor
ratio, and the algebra identification respects the polynomial coordinates. -/
def galoisCoordinateAlgebra : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotRing δ A E → isFundamental A E Y →
    let C := constantSubfield δ
    let D := picardVessiotCoordinateAlgebra δ Y
    let G := matrixGaloisGroup δ E Y
    (G : Set (GL (Fin n) C)) = zeroLocus (tensorRatioRelations δ Y) ∧
    IsAlgebraicSubgroup G ∧
    tensorRatioRelations δ Y = vanishingIdeal (G : Set (GL (Fin n) C)) ∧
    ∃ e : D ≃ₐ[C] CoordinateRing (G : Set (GL (Fin n) C)),
      letI : Algebra C R := Algebra.compHom R (constantSubfield δ).subtype
      ∀ p, ↑(e.symm (coordinateMap (G : Set (GL (Fin n) C)) p)) =
        evalAt (C := C) (tensorRatio K Y) p

/-- Extension and restriction identify the same matrix group with the
operator automorphism group of the total ring of fractions. -/
def galoisTotalRingAction : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (Y : GL (Fin n) R) (F : operator kind (totalQuotientRing R)),
    isBaseField δ → isPicardVessiotRing δ A E → isFundamental A E Y → isAlgebra E F →
    let G := matrixGaloisGroup δ E Y
    let Q := totalQuotientRing R
    letI : Algebra K Q := Algebra.compHom Q (algebraMap K R)
    ∃ e : G ≃* operatorAutomorphisms K F,
      (∀ g, (e g).val.toRingEquiv = matrixFractionAutomorphism δ E Y g) ∧
      ∀ g τ, e g = τ ↔ ∀ r : R, τ.val (algebraMap R Q r) =
        algebraMap R Q ((matrixAutomorphism δ E Y g).val r)

/-- For any second fundamental matrix the same automorphisms in the two
realizations correspond by the indicated inner conjugation. -/
def galoisChangeFundamentalMatrix : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (Y Y' : GL (Fin n) R),
    isBaseField δ → isPicardVessiotRing δ A E → isFundamental A E Y →
    isFundamental A E Y' →
    let C := constantSubfield δ
    let G := matrixGaloisGroup δ E Y
    (∃ b : GL (Fin n) C, Y' = Y * GeneralLinearGroup.map (constantsIn δ) b) ∧
    ∀ b : GL (Fin n) C, Y' = Y * GeneralLinearGroup.map (constantsIn δ) b →
      (∀ g : GL (Fin n) C, b⁻¹ * g * b ∈ matrixGaloisGroup δ E Y' ↔ g ∈ G) ∧
      ∀ (g : G) (hg : b⁻¹ * g.val * b ∈ matrixGaloisGroup δ E Y'),
        matrixAutomorphism δ E Y' ⟨b⁻¹ * g.val * b, hg⟩ = matrixAutomorphism δ E Y g

end Theorems

end

end GaloisFormalization.PV.Specs
