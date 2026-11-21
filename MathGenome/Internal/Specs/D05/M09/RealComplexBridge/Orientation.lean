import MathGenome.Internal.Specs.D05.M09.RealComplexBridge.Realification
import MathGenome.Internal.Specs.D05.M05.Orientation
import MathGenome.Internal.Specs.D05.Foundations.PermutationSign

/-! The ordered-basis quotient from M05 is used, including its single class
in dimension zero. All index maps below act on positions, never on vectors.
Grouped positions are j, n+j; interleaved positions are 2j, 2j+1.
The alternating-map identity records the sign for volume generators without
choosing a realization of the determinant line. -/
noncomputable section
open scoped BigOperators
namespace Specs.D05.M09.RealComplexBridge.Orientation

/-- Product order: the real block followed by the imaginary block. -/
def groupedIndex (n : ℕ) : (Fin 2 × Fin n) ≃ Fin (n+n) :=
  finProdFinEquiv.trans (finCongr (two_mul n))

/-- Product order after exchanging factors: each vector followed by i times it. -/
def interleavedIndex (n : ℕ) : (Fin 2 × Fin n) ≃ Fin (n+n) :=
  ((Equiv.prodComm _ _).trans finProdFinEquiv).trans (finCongr (mul_two n))

def groupingPermutation (n : ℕ) : Equiv.Perm (Fin (n+n)) :=
  (groupedIndex n).symm.trans (interleavedIndex n)

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def groupedBasis (b : Module.Basis (Fin n) ℂ V) : Module.Basis (Fin (n+n)) ℝ V :=
  (Complex.basisOneI.smulTower b).reindex (groupedIndex n)

def interleavedBasis (b : Module.Basis (Fin n) ℂ V) : Module.Basis (Fin (n+n)) ℝ V :=
  (groupedBasis b).reindex (groupingPermutation n)

def complexOrientation (b : Module.Basis (Fin n) ℂ V) :
    Specs.D05.M05.Orientation.classes_value V (n+n) :=
  Specs.D05.M05.Orientation.classOf_value (interleavedBasis b)

def greubOrientation (b : Module.Basis (Fin n) ℂ V) :
    Specs.D05.M05.Orientation.classes_value V (n+n) :=
  Specs.D05.M05.Orientation.classOf_value (groupedBasis b)

-- Definition bindings: exact types and values.
def groupingPermutation_type := (n : ℕ) → Equiv.Perm (Fin (n+n))
def groupingPermutation_value : groupingPermutation_type := groupingPermutation

def groupedBasis_type := {V : Type*} → [AddCommGroup V] → [Module ℂ V] → {n : ℕ} →
  Module.Basis (Fin n) ℂ V → Module.Basis (Fin (n+n)) ℝ V
def groupedBasis_value : groupedBasis_type := @groupedBasis

def interleavedBasis_type := groupedBasis_type
def interleavedBasis_value : interleavedBasis_type := @interleavedBasis

def complexOrientation_type := {V : Type*} → [AddCommGroup V] → [Module ℂ V] → {n : ℕ} →
  Module.Basis (Fin n) ℂ V → Specs.D05.M05.Orientation.classes_value V (n+n)
def complexOrientation_value : complexOrientation_type := @complexOrientation

/-- A preferred class depending only on the space. Its presentation through
`Module.finBasis` is proved equal to the class from every complex basis of
that dimension. -/
def canonicalOrientation (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] :
    Specs.D05.M05.Orientation.classes_value V
      (Module.finrank ℂ V + Module.finrank ℂ V) :=
  complexOrientation (Module.finBasis ℂ V)

def canonicalOrientation_type := (V : Type*) → [AddCommGroup V] → [Module ℂ V] →
  [FiniteDimensional ℂ V] → Specs.D05.M05.Orientation.classes_value V
    (Module.finrank ℂ V + Module.finrank ℂ V)
def canonicalOrientation_value : canonicalOrientation_type := canonicalOrientation

def canonical_orientation_basis : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V),
    canonicalOrientation V = complexOrientation b

def greubOrientation_type := complexOrientation_type
def greubOrientation_value : greubOrientation_type := @greubOrientation

/-- Explicit vector order, with zero-based indices. -/
def basis_vectors : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (j : Fin n),
    groupedBasis b (Fin.castAdd n j) = b j ∧
    groupedBasis b (Fin.natAdd n j) = Complex.I • b j ∧
    interleavedBasis b (interleavedIndex n (0,j)) = b j ∧
    interleavedBasis b (interleavedIndex n (1,j)) = Complex.I • b j

/-- These are the actual numbered positions 2j and 2j+1. -/
def index_positions : Prop := ∀ n (j : Fin n),
  (interleavedIndex n (0,j)).val = 2*j.val ∧
  (interleavedIndex n (1,j)).val = 2*j.val+1 ∧
  groupingPermutation n (Fin.castAdd n j) = interleavedIndex n (0,j) ∧
  groupingPermutation n (Fin.natAdd n j) = interleavedIndex n (1,j)

/-- Both ordered real conversion determinants equal |det_C P|², where P
has the new complex basis as columns in the old basis. -/
def transition_determinants : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℂ V),
    _root_.D05.M05.determinant (Specs.D05.M04.ChangeBasis.changeMatrix_value
      (groupedBasis b) (groupedBasis c)) = ‖b.det c‖^2 ∧
    _root_.D05.M05.determinant (Specs.D05.M04.ChangeBasis.changeMatrix_value
      (interleavedBasis b) (interleavedBasis c)) = ‖b.det c‖^2

def transition_positive : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℂ V),
    Specs.D05.M05.Orientation.sameOrientation_value (interleavedBasis b) (interleavedBasis c) ∧
    Specs.D05.M05.Orientation.sameOrientation_value (groupedBasis b) (groupedBasis c)

def basis_independence : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℂ V),
    complexOrientation b = complexOrientation c ∧ greubOrientation b = greubOrientation c

/-- Simultaneous permutation of coordinate rows and columns preserves the
conversion determinant (the permutation matrix acts by conjugation). -/
def reindex_transition : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}
    (b c : Module.Basis (Fin m) ℝ V) (σ : Equiv.Perm (Fin m)),
    _root_.D05.M05.determinant (Specs.D05.M04.ChangeBasis.changeMatrix_value
      (b.reindex σ) (c.reindex σ)) =
    _root_.D05.M05.determinant (Specs.D05.M04.ChangeBasis.changeMatrix_value b c)

/-- S has columns e_{σ⁻¹(j)}. It is the same permutation matrix
for every real basis, so every transition is conjugated by this fixed S. -/
def reindex_conjugation : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}
    (b c : Module.Basis (Fin m) ℝ V) (σ : Equiv.Perm (Fin m)),
    let S := (1 : Matrix (Fin m) (Fin m) ℝ).submatrix id σ.symm
    S * S.transpose = 1 ∧ S.transpose * S = 1 ∧
    Specs.D05.M04.ChangeBasis.changeMatrix_value (b.reindex σ) (c.reindex σ) =
      S.transpose * Specs.D05.M04.ChangeBasis.changeMatrix_value b c * S

/-- The operator identities retain exactly the same values when interleaved
coordinates replace grouped coordinates; no nonsingularity is assumed. -/
def interleaved_invariants : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (T : V →ₗ[ℂ] V),
    letI := Module.Finite.of_basis b
    (LinearMap.toMatrix (interleavedBasis b) (interleavedBasis b)
      (T.restrictScalars ℝ)).det = ‖LinearMap.det T‖^2 ∧
    (LinearMap.toMatrix (interleavedBasis b) (interleavedBasis b)
      (T.restrictScalars ℝ)).charpoly.map (algebraMap ℝ ℂ) =
        T.charpoly * T.charpoly.map (starRingEnd ℂ)

def grouping_inversions : Prop := ∀ n,
  _root_.D05.Foundations.inversionCount (groupingPermutation n) = n*(n-1)/2

def grouping_sign : Prop := ∀ n,
  _root_.D05.Foundations.permutationSign (groupingPermutation n) = (-1 : ℤ)^(n*(n-1)/2)

/-- This sign relates the two volume generators; it is not in general +1. -/
def volume_sign : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (f : V [⋀^Fin (n+n)]→ₗ[ℝ] M),
    f (interleavedBasis b) = (-1 : ℝ)^(n*(n-1)/2) • f (groupedBasis b)

def convention_determinant : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V),
    _root_.D05.M05.determinant (Specs.D05.M04.ChangeBasis.changeMatrix_value
      (groupedBasis b) (interleavedBasis b)) = (-1 : ℝ)^(n*(n-1)/2)

def conventions_agree_iff : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V),
    complexOrientation b = greubOrientation b ↔ Even (n*(n-1)/2)

def zero_orientation : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (b : Module.Basis (Fin 0) ℂ V),
    complexOrientation b = greubOrientation b ∧
    ∀ o : Specs.D05.M05.Orientation.classes_value V 0, o = complexOrientation b

end Specs.D05.M09.RealComplexBridge.Orientation
