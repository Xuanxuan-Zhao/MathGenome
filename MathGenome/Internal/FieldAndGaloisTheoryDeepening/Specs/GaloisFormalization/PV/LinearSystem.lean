import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorRing
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Independent specifications for the linear systems in Lemma 1.2. -/
namespace GaloisFormalization.PV.Specs

open scoped Matrix

universe u v

-- The specification values quantify over separate base and solution ring universes.
set_option linter.checkUnivs false

def linearSystemType :=
  (kind : OperatorKind) → (K : Type u) → [Field K] → (n : ℕ) → Type u

def linearSystem : linearSystemType.{u} := fun kind K _ n =>
  match kind with
  | .differential => Matrix (Fin n) (Fin n) K
  | .difference => Matrix.GeneralLinearGroup (Fin n) K

def differentialSystemType :=
  {K : Type u} → [Field K] → {n : ℕ} →
    Matrix (Fin n) (Fin n) K → linearSystem .differential K n

def differentialSystem : differentialSystemType.{u} := fun A => A

def differenceSystemType :=
  {K : Type u} → [Field K] → {n : ℕ} →
    Matrix.GeneralLinearGroup (Fin n) K → linearSystem .difference K n

def differenceSystem : differenceSystemType.{u} := fun A => A

def coefficientMatrixType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → {n : ℕ} →
    linearSystem kind K n → Matrix (Fin n) (Fin n) K

def coefficientMatrix : coefficientMatrixType.{u} := fun {kind K} _ {n} A =>
  match kind, A with
  | .differential, M => M
  | .difference, M => (show Matrix.GeneralLinearGroup (Fin n) K from M).val

def mapCoefficientsType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → {n : ℕ} →
    linearSystem kind K n → (S : Type v) → [CommRing S] → [Algebra K S] →
    Matrix (Fin n) (Fin n) S

def mapCoefficients : mapCoefficientsType.{u, v} := fun {_kind K} _ {_n} A S _ _ =>
  (coefficientMatrix A).map (algebraMap K S)

section Solutions

variable {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
variable {S : Type v} [CommRing S] [Algebra K S]

def isSolutionType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → {n : ℕ} →
    {S : Type v} → [CommRing S] → [Algebra K S] →
    linearSystem kind K n → operator kind S → (Fin n → S) → Prop

def isSolution (A : linearSystem kind K n) (E : operator kind S) (x : Fin n → S) : Prop :=
  (fun i => apply E (x i)) = mapCoefficients A S *ᵥ x

def isFundamentalType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → {n : ℕ} →
    {S : Type v} → [CommRing S] → [Algebra K S] →
    linearSystem kind K n → operator kind S → Matrix.GeneralLinearGroup (Fin n) S → Prop

def isFundamental (A : linearSystem kind K n) (E : operator kind S)
    (Y : Matrix.GeneralLinearGroup (Fin n) S) : Prop :=
  Y.val.map (apply E) = mapCoefficients A S * Y.val

def solutionType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → {n : ℕ} →
    {S : Type v} → [CommRing S] → [Algebra K S] →
    linearSystem kind K n → operator kind S → Type v

def solution (A : linearSystem kind K n) (E : operator kind S) : Type v :=
  {x // isSolution A E x}

def fundamentalMatrixType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → {n : ℕ} →
    {S : Type v} → [CommRing S] → [Algebra K S] →
    linearSystem kind K n → operator kind S → Type v

def fundamentalMatrix (A : linearSystem kind K n) (E : operator kind S) : Type v :=
  {Y // isFundamental A E Y}

end Solutions

def determinantInverseType :=
  {n : ℕ} → {S : Type v} → [CommRing S] → Matrix.GeneralLinearGroup (Fin n) S → S

def determinantInverse : determinantInverseType.{v} := fun Y =>
  ((Matrix.GeneralLinearGroup.det Y)⁻¹ : _ˣ).val

end GaloisFormalization.PV.Specs
