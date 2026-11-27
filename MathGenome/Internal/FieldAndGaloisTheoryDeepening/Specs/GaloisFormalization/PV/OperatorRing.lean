import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Basic

namespace GaloisFormalization.PV

/-- The two kinds of operators in Picard–Vessiot theory. -/
inductive OperatorKind
  | differential
  | difference

end GaloisFormalization.PV

/-! Independent definitions of the operator-ring interface in Definition 1.1. -/
namespace GaloisFormalization.PV.Specs

universe u v w

-- The universes of the quantified types occur separately in the specification values.
set_option linter.checkUnivs false

def operatorType :=
  (kind : OperatorKind) → (R : Type u) → [CommRing R] → Type u

def operator : operatorType.{u} := fun kind R _ =>
  match kind with
  | .differential => Derivation ℤ R R
  | .difference => R ≃+* R

def operatorFieldType :=
  (kind : OperatorKind) → (K : Type u) → [Field K] → Type u

def operatorField : operatorFieldType.{u} :=
  fun kind K _ => operator kind K

def differentialType :=
  {R : Type u} → [CommRing R] → Derivation ℤ R R → operator .differential R

def differential : differentialType.{u} := fun d => d

def differenceType :=
  {R : Type u} → [CommRing R] → (R ≃+* R) → operator .difference R

def difference : differenceType.{u} := fun σ => σ

def toDerivationType :=
  {R : Type u} → [CommRing R] → operator .differential R → Derivation ℤ R R

def toDerivation : toDerivationType.{u} := fun D => D

def toRingEquivType :=
  {R : Type u} → [CommRing R] → operator .difference R → (R ≃+* R)

def toRingEquiv : toRingEquivType.{u} := fun D => D

def applyType :=
  {kind : OperatorKind} → {R : Type u} → [CommRing R] → operator kind R → R → R

def apply : applyType.{u} := fun {kind R} _ D x =>
  match kind, D with
  | .differential, d => (show Derivation ℤ R R from d) x
  | .difference, σ => (show R ≃+* R from σ) x

def trivialType :=
  (kind : OperatorKind) → (R : Type u) → [CommRing R] → operator kind R

def trivial : trivialType.{u} := fun kind R _ =>
  match kind with
  | .differential => (0 : Derivation ℤ R R)
  | .difference => RingEquiv.refl R

def commutesType :=
  {kind : OperatorKind} → {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    operator kind R → operator kind S → (R → S) → Prop

def commutes : commutesType.{u, v} := fun D E f =>
  ∀ x, f (apply D x) = apply E (f x)

def ringHomType :=
  {kind : OperatorKind} → {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    operator kind R → operator kind S → Type (max u v)

def ringHom : ringHomType.{u, v} :=
  fun {_kind R S} _ _ D E => { f : R →+* S // commutes D E f }

def ringEquivType :=
  {kind : OperatorKind} → {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    operator kind R → operator kind S → Type (max u v)

def ringEquiv : ringEquivType.{u, v} :=
  fun {_kind R S} _ _ D E => { f : R ≃+* S // commutes D E f }

def algHomType :=
  {kind : OperatorKind} → {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    (A : Type w) → [CommRing A] → [Algebra A R] → [Algebra A S] →
    operator kind R → operator kind S → Type (max u v)

def algHom : algHomType.{u, v, w} :=
  fun {_kind R S} _ _ A _ _ _ D E => { f : R →ₐ[A] S // commutes D E f }

def algEquivType :=
  {kind : OperatorKind} → {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    (A : Type w) → [CommRing A] → [Algebra A R] → [Algebra A S] →
    operator kind R → operator kind S → Type (max u v)

def algEquiv : algEquivType.{u, v, w} :=
  fun {_kind R S} _ _ A _ _ _ D E => { f : R ≃ₐ[A] S // commutes D E f }

def isAlgebraType :=
  {kind : OperatorKind} → {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    operator kind R → operator kind S → [Algebra R S] → Prop

def isAlgebra : isAlgebraType.{u, v} := fun {_kind R S} _ _ D E _ =>
  commutes D E (algebraMap R S)

def isExtensionType :=
  {kind : OperatorKind} → {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    operator kind R → operator kind S → [Algebra R S] → Prop

def isExtension : isExtensionType.{u, v} := fun {_kind R S} _ _ D E _ =>
  commutes D E (algebraMap R S) ∧ Function.Injective (algebraMap R S)

def isStableType :=
  {kind : OperatorKind} → {R : Type u} → [CommRing R] → operator kind R → Set R → Prop

def isStable : isStableType.{u} := fun {kind R} _ D U =>
  match kind, D with
  | .differential, d => ∀ ⦃x⦄, x ∈ U → (show Derivation ℤ R R from d) x ∈ U
  | .difference, σ =>
    let σ : R ≃+* R := σ
    (∀ ⦃x⦄, x ∈ U → σ x ∈ U) ∧ (∀ ⦃x⦄, x ∈ U → σ.symm x ∈ U)

def subringType :=
  {kind : OperatorKind} → {R : Type u} → [CommRing R] → operator kind R → Type u

def subring : subringType.{u} :=
  fun {_kind R} _ D => { U : Subring R // isStable D (U : Set R) }

def subalgebraType :=
  {kind : OperatorKind} → {R : Type u} → [CommRing R] →
    (A : Type v) → [CommRing A] → [Algebra A R] → operator kind R → Type u

def subalgebra : subalgebraType.{u, v} := fun {_kind R} _ A _ _ D =>
  { U : Subalgebra A R // isStable D (U : Set R) }

def idealType :=
  {kind : OperatorKind} → {R : Type u} → [CommRing R] → operator kind R → Type u

def ideal : idealType.{u} :=
  fun {_kind R} _ D => { I : Ideal R // isStable D (I : Set R) }

def isSimpleType :=
  {kind : OperatorKind} → {R : Type u} → [CommRing R] → operator kind R → Prop

def isSimple : isSimpleType.{u} := fun {_kind R} _ D =>
  Nontrivial R ∧ ∀ I : Ideal R, isStable D (I : Set R) → I = ⊥ ∨ I = ⊤

def isConstantType :=
  {kind : OperatorKind} → {R : Type u} → [CommRing R] → operator kind R → R → Prop

def isConstant : isConstantType.{u} := fun {kind _R} _ D x =>
  match kind with
  | .differential => apply D x = 0
  | .difference => apply D x = x

def constantSubringType :=
  {kind : OperatorKind} → {R : Type u} → [CommRing R] → operator kind R → Subring R

def constantSubring : constantSubringType.{u} := fun {kind R} _ D =>
  match kind, D with
  | .differential, D =>
    let d : Derivation ℤ R R := D
    { carrier := {x | d x = 0}
      zero_mem' := d.map_zero
      one_mem' := d.map_one_eq_zero
      add_mem' := fun {a b} ha hb => by
        change d (a + b) = 0
        simp only [d.map_add, show d a = 0 from ha, show d b = 0 from hb, add_zero]
      mul_mem' := fun {a b} ha hb => by
        change d (a * b) = 0
        simp only [d.leibniz, show d a = 0 from ha, show d b = 0 from hb, smul_zero, add_zero]
      neg_mem' := fun {a} ha => by
        change d (-a) = 0
        simp only [d.map_neg, show d a = 0 from ha, neg_zero] }
  | .difference, D =>
    (show R ≃+* R from D).toRingHom.eqLocus (RingHom.id R)

def memConstantSubring :=
  ∀ {kind : OperatorKind} {R : Type u} [CommRing R] (D : operator kind R) (x : R),
    x ∈ constantSubring D ↔ isConstant D x

private theorem constantSubring_mem : memConstantSubring.{u} := by
  intro kind
  cases kind <;> intros <;> rfl

def constantSubringEmbeddingType :=
  {kind : OperatorKind} → {R : Type u} → [CommRing R] → (D : operator kind R) →
    ringHom (trivial kind (constantSubring D)) D

def constantSubringEmbedding : constantSubringEmbeddingType.{u} :=
  fun {kind R} _ D => ⟨(constantSubring D).subtype, by
    intro x
    have hx := (constantSubring_mem D (x : R)).mp x.property
    cases kind <;> exact hx.symm⟩

def constantSubringEmbeddingInjective :=
  ∀ {kind : OperatorKind} {R : Type u} [CommRing R] (D : operator kind R),
    Function.Injective (constantSubringEmbedding D).val

def mapConstantsType :=
  {kind : OperatorKind} → {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    {D : operator kind R} → {E : operator kind S} → ringHom D E →
    ((constantSubring D : Type u) →+* (constantSubring E : Type v))

def mapConstants : mapConstantsType.{u, v} := fun {kind R S} _ _ {D E} f =>
  (f.val.comp (constantSubring D).subtype).codRestrict (constantSubring E) fun x => by
    apply (constantSubring_mem E _).mpr
    have hx := (constantSubring_mem D (x : R)).mp x.property
    have h := f.property (x : R)
    cases kind with
    | differential =>
      change apply D x.val = 0 at hx
      change apply E (f.val x.val) = 0
      rw [← h, hx, f.val.map_zero]
    | difference =>
      change apply D x.val = x.val at hx
      change apply E (f.val x.val) = f.val x.val
      rw [← h, hx]

def constantSubfieldType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → operatorField kind K → Subfield K

def constantSubfield : constantSubfieldType.{u} := fun {kind K} _ D =>
  { toSubring := constantSubring D
    inv_mem' := by
      intro x hx
      cases kind with
      | differential =>
        let d : Derivation ℤ K K := D
        change d x = 0 at hx
        change d x⁻¹ = 0
        rw [d.leibniz_inv, hx, smul_zero]
      | difference =>
        let σ : K ≃+* K := D
        change σ x = x at hx
        change σ x⁻¹ = x⁻¹
        rw [map_inv₀, hx] }

def memConstantSubfield :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] (D : operatorField kind K) (x : K),
    x ∈ constantSubfield D ↔ isConstant D x

def constantSubfieldEmbeddingType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → (D : operatorField kind K) →
    ringHom (trivial kind (constantSubfield D)) D

def constantSubfieldEmbedding : constantSubfieldEmbeddingType.{u} :=
  fun {kind K} _ D => ⟨(constantSubfield D).subtype, by
    intro x
    have hx := (constantSubring_mem D (x : K)).mp x.property
    cases kind <;> exact hx.symm⟩

def constantSubfieldEmbeddingInjective :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] (D : operatorField kind K),
    Function.Injective (constantSubfieldEmbedding D).val

def isBaseFieldType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → operatorField kind K → Prop

def isBaseField : isBaseFieldType.{u} := fun {_kind K} _ D =>
  CharZero K ∧ IsAlgClosed (constantSubfield D)

end GaloisFormalization.PV.Specs
