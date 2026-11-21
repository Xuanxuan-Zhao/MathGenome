import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.JacobianPresentation
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Logic.Equiv.Fintype

/-! SM-03 (paper.tex:987–996). Finite presentations retain their specified
variables and relations. Rows are variables and columns are relations; a minor
selects distinct rows and every relation column. Rings may be zero. -/
namespace Specs.AdvCommAlg.Smooth

universe u v
noncomputable section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

def selectedMinor {n c : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin c))
    (a : Fin c ↪ Fin n) : Matrix (Fin c) (Fin c) B :=
  (Differentials.presentationJacobian P).submatrix a id

def presentationStandardSmooth {n c : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin c)) : Prop :=
  ∃ a : Fin c ↪ Fin n, IsUnit (selectedMinor P a).det

/-- Use the canonical library predicate, with its finite-minor characterization
specified below. -/
def standardSmoothType := ∀ (A : Type u) (B : Type v),
  [CommRing A] → [CommRing B] → [Algebra A B] → Prop

def standardSmoothValue : standardSmoothType.{u,v} :=
  fun A B _ _ _ => Algebra.IsStandardSmooth A B

def selectedMinorType := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ},
  Algebra.Presentation A B (Fin n) (Fin c) →
    (Fin c ↪ Fin n) → Matrix (Fin c) (Fin c) B

def selectedMinorValue : selectedMinorType.{u,v} := @selectedMinor

def presentationStandardSmoothType := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ},
  Algebra.Presentation A B (Fin n) (Fin c) → Prop

def presentationStandardSmoothValue : presentationStandardSmoothType.{u,v} :=
  @presentationStandardSmooth

def minorEntries : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin c)) (a : Fin c ↪ Fin n) (i j : Fin c),
  selectedMinor P a i j = MvPolynomial.aeval P.val
    (MvPolynomial.pderiv (a i) (P.relation j))

def minorJacobian : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ}
  (P : Algebra.PreSubmersivePresentation A B (Fin n) (Fin c)),
  P.jacobian = (selectedMinor P.toPresentation ⟨P.map, P.map_inj⟩).det

/-- Identification preserves the given presentation, not merely the algebra. -/
def submersiveIff : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin c)),
  presentationStandardSmooth P ↔
    ∃ Q : Algebra.SubmersivePresentation A B (Fin n) (Fin c), Q.toPresentation = P

def presentationBounds : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin c)),
  presentationStandardSmooth P → c ≤ n

def standardSmoothIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  standardSmoothValue A B ↔ ∃ (n c : ℕ)
    (P : Algebra.Presentation A B (Fin n) (Fin c)), presentationStandardSmooth P

def emptyMinor : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin 0)) (a : Fin 0 ↪ Fin n),
  (selectedMinor P a).det = 1

def emptyPresentation : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin 0)), presentationStandardSmooth P

/-- Reindex variables and relations together with the row selection. The two
square indices are reindexed by the same relation permutation. -/
def minorReindex : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin c)) (a : Fin c ↪ Fin n)
  (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin c)),
  selectedMinor (P.reindex e f) (f.toEmbedding.trans (a.trans e.symm.toEmbedding)) =
    (selectedMinor P a).submatrix f f

def minorDetReindex : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin c)) (a : Fin c ↪ Fin n)
  (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin c)),
  (selectedMinor (P.reindex e f)
    (f.toEmbedding.trans (a.trans e.symm.toEmbedding))).det = (selectedMinor P a).det

/-- A variable permutation moves the selected rows to the initial c variables,
while preserving the order of the relations and the entire selected matrix. -/
def orderedRows : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin c)) (a : Fin c ↪ Fin n),
  ∃ (h : c ≤ n) (e : Equiv.Perm (Fin n)),
    (∀ j : Fin c, e (Fin.castLE h j) = a j) ∧
    selectedMinor (P.reindex e (Equiv.refl _)) ⟨Fin.castLE h, Fin.castLE_injective h⟩ =
      selectedMinor P a

def orderedPresentation : Prop := ∀ {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B] {n c : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin c)),
  presentationStandardSmooth P ↔ ∃ (h : c ≤ n) (e : Equiv.Perm (Fin n)),
    IsUnit (selectedMinor (P.reindex e (Equiv.refl _))
      ⟨Fin.castLE h, Fin.castLE_injective h⟩).det

end
end Specs.AdvCommAlg.Smooth
