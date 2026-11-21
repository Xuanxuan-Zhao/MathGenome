import MathGenome.Internal.Specs.D07.Ch16.StructureExistence
import MathGenome.Internal.Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants
import MathGenome.Internal.Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment

/-! Uniqueness for arbitrary decompositions, with all unit cyclic factors
excluded in the invariant-factor form. Finite products model finite direct
sums; the implementation also supplies the direct-sum versions. -/
universe u v
namespace Specs.D07.Ch16.StructureUniqueness

open Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment (Cyclic)

/-- The pair records the prime up to associates and its positive exponent,
including repetitions. No choice of prime representatives is imposed. -/
noncomputable def elementaryData {R : Type u} [CommRing R]
    {t : ℕ} (q : Fin t → R) (e : Fin t → ℕ) : Multiset (Associates R × ℕ) :=
  Finset.univ.val.map (fun i => (Associates.mk (q i), e i))

def FreeRankUniqueness : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (r s r' s' : ℕ) (d : Fin s → R) (d' : Fin s' → R),
    (∀ i, d i ≠ 0) → (∀ i, d' i ≠ 0) →
    (M ≃ₗ[R] ((Fin r → R) × (∀ i, Cyclic R (d i)))) →
    (M ≃ₗ[R] ((Fin r' → R) × (∀ i, Cyclic R (d' i)))) → r = r'

def PrimaryUniqueness : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r t r' t' : ℕ) (q : Fin t → R) (e : Fin t → ℕ)
    (q' : Fin t' → R) (e' : Fin t' → ℕ),
    (∀ i, Prime (q i) ∧ 0 < e i) → (∀ i, Prime (q' i) ∧ 0 < e' i) →
    (M ≃ₗ[R] ((Fin r → R) × (∀ i, Cyclic R (q i ^ e i)))) →
    (M ≃ₗ[R] ((Fin r' → R) × (∀ i, Cyclic R (q' i ^ e' i)))) →
    r = r' ∧ t = t' ∧ elementaryData q e = elementaryData q' e'

def InvariantFactorUniqueness : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r s r' s' : ℕ) (d : Fin s → R) (d' : Fin s' → R),
    (∀ i, d i ≠ 0 ∧ ¬ IsUnit (d i)) → (∀ i, d' i ≠ 0 ∧ ¬ IsUnit (d' i)) →
    (∀ i j, i ≤ j → d i ∣ d j) → (∀ i j, i ≤ j → d' i ∣ d' j) →
    (M ≃ₗ[R] ((Fin r → R) × (∀ i, Cyclic R (d i)))) →
    (M ≃ₗ[R] ((Fin r' → R) × (∀ i, Cyclic R (d' i)))) →
    r = r' ∧ ∃ h : s = s', ∀ i, Associated (d i) (d' (Fin.cast h i))

/-- The source's direct-sum primary form, including equality of the multiset
of actual prime powers modulo associates, as well as prime/exponent data. -/
def DirectSumPrimaryUniqueness : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r t r' t' : ℕ) (q : Fin t → R) (e : Fin t → ℕ)
    (q' : Fin t' → R) (e' : Fin t' → ℕ),
    (∀ i, Prime (q i) ∧ 0 < e i) → (∀ i, Prime (q' i) ∧ 0 < e' i) →
    (M ≃ₗ[R] ((Fin r → R) × DirectSum (Fin t) (fun i => Cyclic R (q i ^ e i)))) →
    (M ≃ₗ[R] ((Fin r' → R) × DirectSum (Fin t') (fun i => Cyclic R (q' i ^ e' i)))) →
    r = r' ∧ t = t' ∧ elementaryData q e = elementaryData q' e' ∧
      Finset.univ.val.map (fun i => Associates.mk (q i ^ e i)) =
        Finset.univ.val.map (fun i => Associates.mk (q' i ^ e' i))

def DirectSumInvariantFactorUniqueness : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r s r' s' : ℕ) (d : Fin s → R) (d' : Fin s' → R),
    (∀ i, d i ≠ 0 ∧ ¬ IsUnit (d i)) → (∀ i, d' i ≠ 0 ∧ ¬ IsUnit (d' i)) →
    (∀ i j, i ≤ j → d i ∣ d j) → (∀ i j, i ≤ j → d' i ∣ d' j) →
    (M ≃ₗ[R] ((Fin r → R) × DirectSum (Fin s) (fun i => Cyclic R (d i)))) →
    (M ≃ₗ[R] ((Fin r' → R) × DirectSum (Fin s') (fun i => Cyclic R (d' i)))) →
    r = r' ∧ ∃ h : s = s', ∀ i, Associated (d i) (d' (Fin.cast h i))

/-- Preserve the intrinsic residue-field filtration, and the canonical
sorting, left-zero-padding, and CRT reconstruction interfaces. -/
def IntrinsicFiltration : Prop :=
  StructureUniquenessPrimaryFiltrationInvariants.LayerDimension.{u,v} ∧
  StructureUniquenessPrimaryFiltrationInvariants.ExponentMultiplicity.{u,v}

def CanonicalAlignment : Prop :=
  StructureUniquenessInvariantFactorAlignment.ExponentAlignment.{u} ∧
  StructureUniquenessInvariantFactorAlignment.ColumnProperties.{u} ∧
  StructureUniquenessInvariantFactorAlignment.Reconstruction.{u} ∧
  StructureUniquenessInvariantFactorAlignment.ChainUniqueness.{u} ∧
  StructureUniquenessInvariantFactorAlignment.EmptyCase.{u}

end Specs.D07.Ch16.StructureUniqueness
