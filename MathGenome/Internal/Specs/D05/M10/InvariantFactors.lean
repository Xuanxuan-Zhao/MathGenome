import MathGenome.Internal.Specs.D05.M10.Rational
import MathGenome.Internal.Specs.D05.M10.InvariantFactors.CompanionPresentation
import Mathlib.Data.List.OfFn

/-! K05.10.invariant_factors, paper.tex:1519–1527. The canonical list is
computed from determinantal divisors, not postulated as a decomposition
certificate. RationalFactors describes actual companion matrices in an actual
basis. All fields and zero dimensions are retained. -/
noncomputable section
open Polynomial Matrix
open scoped BigOperators
namespace Specs.D05.M10.InvariantFactors
open D05.M10.Smith D05.M10.InvariantFactorComputation
open CompanionPresentation (BlockIndex companionBlocks)

/-- Ordered nonunit Smith entries computed from consecutive minor gcds. -/
def matrixFactors {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : List K[X] := by
  classical
  exact (List.ofFn (fun i : Fin n =>
    minorGcd A.charmatrix (i.val+1) / minorGcd A.charmatrix i.val)).filter
      (fun p => decide (¬ IsUnit p))

/-- A coordinate definition whose basis independence is a theorem below. -/
def factors {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) : List K[X] :=
  matrixFactors (LinearMap.toMatrix (Module.finBasis K V) (Module.finBasis K V) T)

/-- A rational representation over the original field, with the prescribed
ascending divisibility order and nonconstant monic entries. -/
def RationalFactors {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {r : ℕ} (d : Fin r → K[X]) : Prop :=
  (∀ i, (d i).Monic) ∧ (∀ i, 0 < (d i).natDegree) ∧
    (∀ i j, i ≤ j → d i ∣ d j) ∧
    ∃ b : Module.Basis (BlockIndex d) K V,
      LinearMap.toMatrix b b T = companionBlocks d

/-- Literal invertible constant matrix conjugacy, with column coordinates. -/
def Similar {K : Type*} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ P : (Matrix (Fin n) (Fin n) K)ˣ, (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * A * (P : Matrix (Fin n) (Fin n) K) = B

def similarity_minors : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K),
    Similar A B → ∀ k, minorIdeal A.charmatrix k = minorIdeal B.charmatrix k ∧
      minorGcd A.charmatrix k = minorGcd B.charmatrix k

def basis_independence : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (T : Module.End K V), matrixFactors (LinearMap.toMatrix b b T) = factors T

def rational_identification : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (d : Fin r → K[X]),
    RationalFactors T d → factors T = List.ofFn d

def rational_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r s : ℕ}
    (d : Fin r → K[X]) (e : Fin s → K[X]),
    RationalFactors T d → RationalFactors T e → List.ofFn d = List.ofFn e

def module_identification : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (d : Fin r → K[X]),
    (∀ i, (d i).Monic) → (∀ i, 0 < (d i).natDegree) →
    (∀ i j, i ≤ j → d i ∣ d j) →
    Nonempty (Module.AEval' T ≃ₗ[K[X]] (∀ i, Rational.Residue (d i))) →
      factors T = List.ofFn d

def exists_invariant_factors : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    ∃ (r : ℕ) (d : Fin r → K[X]), RationalFactors T d ∧ factors T = List.ofFn d

def charpoly_product : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (d : Fin r → K[X]),
    RationalFactors T d → T.charpoly = ∏ i, d i

def minpoly_largest : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (d : Fin (r+1) → K[X]),
    RationalFactors T d → minpoly K T = d (Fin.last r)

/-- Positive dimension forces a nonempty list, so the preceding largest-entry
formula applies to every nonzero finite-dimensional space. -/
def nonempty_factors : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (d : Fin r → K[X]),
    RationalFactors T d → (r = 0 ↔ Module.finrank K V = 0)

def zero_case : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V), Module.finrank K V = 0 →
      factors T = [] ∧ T.charpoly = 1 ∧ minpoly K T = 1

def similarity_iff : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K),
    Similar A B ↔ matrixFactors A = matrixFactors B

end Specs.D05.M10.InvariantFactors
