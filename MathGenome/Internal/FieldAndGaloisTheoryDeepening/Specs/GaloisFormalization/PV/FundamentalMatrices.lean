import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.LinearSystem

namespace GaloisFormalization.PV.Specs

open scoped Matrix BigOperators
open Function

universe u v

section Fundamental

def fundamentalColumnEquivalence : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
    {S : Type v} [CommRing S] [Algebra K S], ∀ (D : operatorField kind K) (_ : isBaseField D) (E : operator kind S),
    isExtension D E → ∀ (A : linearSystem kind K n)
      (Y : Matrix.GeneralLinearGroup (Fin n) S), isFundamental A E Y →
      ∃ e : (Fin n → constantSubring E) ≃ solution A E,
        (∀ c, (e c).val = Y.val *ᵥ (fun i => (c i : S))) ∧
        (∀ x i, (e.symm x i : S) = ((Y⁻¹).val *ᵥ x.val) i)

def fundamentalRightMultiplier : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
    {S : Type v} [CommRing S] [Algebra K S], ∀ (D : operatorField kind K) (_ : isBaseField D) (E : operator kind S),
    isExtension D E → ∀ (A : linearSystem kind K n)
      (Y Z : Matrix.GeneralLinearGroup (Fin n) S), isFundamental A E Y →
      isFundamental A E Z →
      ∃! B : Matrix.GeneralLinearGroup (Fin n) (constantSubring E),
        Z = Y * Matrix.GeneralLinearGroup.map (constantSubring E).subtype B

def orderZeroFundamental : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S],
    ∀ (A : linearSystem kind K 0) (E : operator kind S),
    isFundamental A E 1 ∧ ∀ Y : Matrix.GeneralLinearGroup (Fin 0) S, Y = 1

end Fundamental

section Scalar

def companionMatrixType :=
  {K : Type u} → [CommRing K] → {n : ℕ} →
    (Fin (n + 1) → K) → Matrix (Fin (n + 1)) (Fin (n + 1)) K

def companionMatrix : companionMatrixType.{u} :=
  fun {_} _ {_} a => Matrix.of (Fin.lastCases (fun j => -a j)
    (fun i j => if i.succ = j then 1 else 0))

def scalarColumnType :=
  {kind : OperatorKind} → {S : Type v} → [CommRing S] → {n : ℕ} →
    operator kind S → S → Fin n → S

def scalarColumn : scalarColumnType.{v} :=
  fun {_ _} _ {_} E x i => (apply E)^[i.val] x

set_option linter.checkUnivs false in
def isScalarSolutionType :=
  {kind : OperatorKind} → {K : Type u} → [Field K] → {n : ℕ} →
    {S : Type v} → [CommRing S] → [Algebra K S] →
    (Fin n → K) → operator kind S → S → Prop

def isScalarSolution : isScalarSolutionType.{u, v} :=
  fun {_ K} _ {n S} _ _ a E x =>
    (apply E)^[n] x + ∑ i : Fin n, algebraMap K S (a i) * (apply E)^[i.val] x = 0

def differentialCompanionType :=
  {K : Type u} → [Field K] → {n : ℕ} → (Fin (n + 1) → K) →
    linearSystem .differential K (n + 1)

def differentialCompanion : differentialCompanionType.{u} :=
  fun {_} _ {_} a => differentialSystem (companionMatrix a)

def companionDeterminant : Prop :=
  ∀ {K : Type u} [CommRing K] {n : ℕ} (a : Fin (n + 1) → K),
    (companionMatrix a).det = (-1 : K) ^ (n + 1) * a 0

def differenceCompanionExists : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (a : Fin (n + 1) → K),
    (∃ A : linearSystem .difference K (n + 1), coefficientMatrix A = companionMatrix a) ↔
      a 0 ≠ 0

def companionColumnEquivalence : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
    {S : Type v} [CommRing S] [Algebra K S], ∀ (D : operatorField kind K) (_ : isBaseField D) (E : operator kind S),
    isExtension D E → ∀ (a : Fin (n + 1) → K) (A : linearSystem kind K (n + 1)),
      coefficientMatrix A = companionMatrix a →
      ∃ e : {x // isScalarSolution a E x} ≃ solution A E,
        (∀ x, (e x).val = scalarColumn E x.val) ∧
        (∀ w, (e.symm w).val = w.val 0)

def orderZeroScalarSolutions : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S],
    ∀ (E : operator kind S) (a : Fin 0 → K) (x : S),
    isScalarSolution a E x ↔ x = 0

def orderZeroColumnEquivalence : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S],
    ∀ (E : operator kind S) (a : Fin 0 → K) (A : linearSystem kind K 0),
    ∃ e : {x // isScalarSolution a E x} ≃ solution A E,
      (∀ x, (e x).val = scalarColumn E x.val) ∧ (∀ w, (e.symm w).val = 0)

end Scalar
end GaloisFormalization.PV.Specs
