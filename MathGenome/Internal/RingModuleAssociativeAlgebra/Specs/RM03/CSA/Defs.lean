import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.RingTheory.TensorProduct.Maps

/-! Specifications for RM03-C04.01. -/

-- Expected types quantify over independent field and carrier universes.
set_option linter.checkUnivs false

namespace Specs.RM03.CSA

open scoped TensorProduct

universe u v w

def IsCentralSimpleType :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A], Prop

def isCentralSimple (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] : Prop :=
  IsSimpleRing A ∧ Algebra.IsCentral k A ∧ FiniteDimensional k A

def IsCentralDivisionType :=
  ∀ (k : Type u) [Field k] (D : Type v) [DivisionRing D] [Algebra k D], Prop

def isCentralDivision (k : Type u) [Field k] (D : Type v) [DivisionRing D] [Algebra k D] :
    Prop :=
  Algebra.IsCentral k D ∧ FiniteDimensional k D

def IsSplitType :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A], Prop

def isSplit (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] : Prop :=
  ∃ n : ℕ, 0 < n ∧ Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) k)

def BaseChangeType :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A], Type (max w v)

/-- The extension field acts through the left tensor factor. -/
abbrev baseChange (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A] : Type (max w v) :=
  L ⊗[k] A

def SplitsType :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A], Prop

def splits (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A] : Prop :=
  isSplit L (baseChange k L A)

def AlgebraMapBaseChange : Prop :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A] (l : L),
    algebraMap L (baseChange k L A) l = l ⊗ₜ[k] (1 : A)

def BaseChangeEquivTensorType :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A],
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := A) (B := L)
    baseChange k L A ≃ₐ[L] A ⊗[k] L

def baseChangeEquivTensor (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A] :
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := A) (B := L)
    baseChange k L A ≃ₐ[L] A ⊗[k] L :=
  Algebra.TensorProduct.commRight k L A

def IsCentralSimpleIff : Prop :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A],
    isCentralSimple k A ↔
      Nontrivial A ∧
      (∀ I : TwoSidedIdeal A, I = ⊥ ∨ I = ⊤) ∧
      FiniteDimensional k A ∧
      (Subalgebra.center k A : Set A) = Set.range (algebraMap k A)

def IsCentralDivisionIff : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [DivisionRing D] [Algebra k D],
    isCentralDivision k D ↔
      FiniteDimensional k D ∧ (Subalgebra.center k D : Set D) = Set.range (algebraMap k D)

def IsCentralSimpleOfIsCentralDivision : Prop :=
  ∀ (k : Type u) [Field k] (D : Type v) [DivisionRing D] [Algebra k D],
    isCentralDivision k D → isCentralSimple k D

def ToCSAType :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A → _root_.CSA.{u, v} k

def toCSA {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    (h : isCentralSimple k A) : _root_.CSA.{u, v} k where
  toAlgCat := AlgCat.of k A
  isSimple := h.1
  isCentral := h.2.1
  fin_dim := h.2.2

def IsCentralSimpleIffExistsCSA : Prop :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A],
    isCentralSimple k A ↔ ∃ B : _root_.CSA.{u, v} k, B.toAlgCat = AlgCat.of k A

end Specs.RM03.CSA
