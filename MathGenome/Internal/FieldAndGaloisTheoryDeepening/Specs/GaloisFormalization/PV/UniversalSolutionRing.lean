import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.LinearSystem
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic

/-! Independent specifications for the universal matrix construction in Theorem 1.7. -/

namespace GaloisFormalization.PV.Specs.UniversalSolutionRing

open scoped Matrix

universe u

abbrev polynomialRingType := (K : Type u) → [Field K] → (n : ℕ) → Type u

abbrev polynomialRing (K : Type u) [Field K] (n : ℕ) : Type u :=
  MvPolynomial (Fin n × Fin n) K

abbrev indeterminateMatrixType :=
  (K : Type u) → [Field K] → (n : ℕ) → Matrix (Fin n) (Fin n) (polynomialRing K n)

/-- The square matrix of distinct polynomial variables. -/
noncomputable def indeterminateMatrix (K : Type u) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (polynomialRing K n) :=
  fun i j => MvPolynomial.X (i, j)

abbrev ringType := (K : Type u) → [Field K] → (n : ℕ) → Type u

/-- The polynomial ring with the determinant of the generic matrix inverted. -/
abbrev ring (K : Type u) [Field K] (n : ℕ) : Type u :=
  Localization.Away (indeterminateMatrix K n).det

abbrev genericMatrixType :=
  (K : Type u) → [Field K] → (n : ℕ) → Matrix.GeneralLinearGroup (Fin n) (ring K n)

/-- The generic matrix as a matrix unit over the localization. -/
noncomputable def genericMatrix (K : Type u) [Field K] (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) (ring K n) :=
  Matrix.GeneralLinearGroup.mk''
    ((indeterminateMatrix K n).map (algebraMap (polynomialRing K n) (ring K n))) (by
      change IsUnit (Matrix.det
        ((algebraMap (polynomialRing K n) (ring K n)).mapMatrix (indeterminateMatrix K n)))
      rw [← RingHom.map_det]
      exact IsLocalization.Away.algebraMap_isUnit (S := ring K n) (indeterminateMatrix K n).det)

/-- Both derivations, with their actions on coefficients, variables and the localization map. -/
def differentialOperator :=
  ∀ {K : Type u} [Field K] {n : ℕ}
    (d : Derivation ℤ K K) (A : Matrix (Fin n) (Fin n) K),
    ∃ dP : Derivation ℤ (polynomialRing K n) (polynomialRing K n),
    ∃ dU : Derivation ℤ (ring K n) (ring K n),
      (∀ a : K, dP (MvPolynomial.C a) = MvPolynomial.C (d a)) ∧
      (indeterminateMatrix K n).map dP =
        A.map MvPolynomial.C * indeterminateMatrix K n ∧
      (∀ p : polynomialRing K n, dU (algebraMap (polynomialRing K n) (ring K n) p) =
        algebraMap (polynomialRing K n) (ring K n) (dP p))

/-- The forward and inverse substitutions on the polynomial ring and their extension to the
localization. The determinant formula ensures that the forward substitution inverts the
necessary element in the target. -/
def differenceOperator :=
  ∀ {K : Type u} [Field K] {n : ℕ} (σ : K ≃+* K)
    (A : Matrix.GeneralLinearGroup (Fin n) K),
    ∃ σP : polynomialRing K n ≃+* polynomialRing K n,
    ∃ σU : ring K n ≃+* ring K n,
      (∀ a : K, σP (MvPolynomial.C a) = MvPolynomial.C (σ a)) ∧
      (∀ a : K, σP.symm (MvPolynomial.C a) = MvPolynomial.C (σ.symm a)) ∧
      (indeterminateMatrix K n).map σP =
        A.val.map MvPolynomial.C * indeterminateMatrix K n ∧
      (indeterminateMatrix K n).map σP.symm =
        (A⁻¹).val.map (fun a => MvPolynomial.C (σ.symm a)) * indeterminateMatrix K n ∧
      σP (indeterminateMatrix K n).det =
        MvPolynomial.C A.val.det * (indeterminateMatrix K n).det ∧
      (∀ p : polynomialRing K n, σU (algebraMap (polynomialRing K n) (ring K n) p) =
        algebraMap (polynomialRing K n) (ring K n) (σP p)) ∧
      (∀ p : polynomialRing K n, σU.symm (algebraMap (polynomialRing K n) (ring K n) p) =
        algebraMap (polynomialRing K n) (ring K n) (σP.symm p))

/-- The localization is a compatible extension of the base field in which the generic
matrix is fundamental for the given system. -/
def existsOperator :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
    (D : operator kind K) (A : linearSystem kind K n),
    ∃ E : operator kind (ring K n), isExtension D E ∧ isFundamental A E (genericMatrix K n)

/-- The entries and inverse determinant of the generic matrix generate the localization. -/
def generatedByEntries :=
  ∀ (K : Type u) [Field K] (n : ℕ),
    Algebra.adjoin K
      (Set.range (fun p : Fin n × Fin n => (genericMatrix K n).val p.1 p.2) ∪
        {determinantInverse (genericMatrix K n)}) = ⊤

def nontrivial :=
  ∀ (K : Type u) [Field K] (n : ℕ), Nontrivial (ring K n)

def finiteType :=
  ∀ (K : Type u) [Field K] (n : ℕ), Algebra.FiniteType K (ring K n)

def isNoetherian :=
  ∀ (K : Type u) [Field K] (n : ℕ), IsNoetherianRing (ring K n)

end GaloisFormalization.PV.Specs.UniversalSolutionRing
