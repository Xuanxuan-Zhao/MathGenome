import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs
import Mathlib.RingTheory.SimpleRing.Basic

/-! Central simple and central division algebras and their splitting fields. -/

namespace RM03.CSA

open scoped TensorProduct

universe u v w

/-- A finite-dimensional simple algebra whose center is the image of the scalar field. -/
def IsCentralSimple (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] : Prop :=
  IsSimpleRing A ∧ Algebra.IsCentral k A ∧ FiniteDimensional k A

/-- A finite-dimensional division algebra whose center is the image of the scalar field. -/
def IsCentralDivision (k : Type u) [Field k] (D : Type v) [DivisionRing D] [Algebra k D] :
    Prop :=
  Algebra.IsCentral k D ∧ FiniteDimensional k D

/-- An algebra is split if it is isomorphic over the base field to a positive-size matrix algebra. -/
def IsSplit (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] : Prop :=
  ∃ n : ℕ, 0 < n ∧ Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) k)

/-- Scalar extension, with the extension field in the left tensor factor. -/
abbrev BaseChange (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A] : Type (max w v) :=
  L ⊗[k] A

/-- A field extension splits the algebra when its scalar extension is split. -/
def Splits (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A] : Prop :=
  IsSplit L (BaseChange k L A)

theorem algebraMap_baseChange (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A] (l : L) :
    algebraMap L (BaseChange k L A) l = l ⊗ₜ[k] (1 : A) :=
  rfl

/-- The tensor flip identifies scalar extension with the paper's tensor order. -/
def baseChangeEquivTensor (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A] :
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := A) (B := L)
    BaseChange k L A ≃ₐ[L] A ⊗[k] L :=
  Algebra.TensorProduct.commRight k L A

private theorem isCentral_iff_center_eq_range
    (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] :
    Algebra.IsCentral k A ↔ (Subalgebra.center k A : Set A) = Set.range (algebraMap k A) := by
  rw [← Algebra.coe_bot]
  constructor
  · intro h
    exact congrArg (fun S : Subalgebra k A => (S : Set A)) (eq_bot_iff.mpr h.out)
  · intro h
    exact ⟨fun x hx => show x ∈ ((⊥ : Subalgebra k A) : Set A) from h ▸ hx⟩

theorem isCentralSimple_iff (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] :
    IsCentralSimple k A ↔
      Nontrivial A ∧
      (∀ I : TwoSidedIdeal A, I = ⊥ ∨ I = ⊤) ∧
      FiniteDimensional k A ∧
      (Subalgebra.center k A : Set A) = Set.range (algebraMap k A) := by
  constructor
  · rintro ⟨hs, hc, hf⟩
    exact ⟨@IsSimpleRing.instNontrivial A _ hs, hs.simple.eq_bot_or_eq_top, hf,
      (isCentral_iff_center_eq_range k A).mp hc⟩
  · rintro ⟨hn, hi, hf, hc⟩
    exact ⟨@IsSimpleRing.of_eq_bot_or_eq_top A _ hn hi,
      (isCentral_iff_center_eq_range k A).mpr hc, hf⟩

theorem isCentralDivision_iff (k : Type u) [Field k] (D : Type v) [DivisionRing D] [Algebra k D] :
    IsCentralDivision k D ↔
      FiniteDimensional k D ∧ (Subalgebra.center k D : Set D) = Set.range (algebraMap k D) := by
  unfold IsCentralDivision
  rw [isCentral_iff_center_eq_range, and_comm]

theorem isCentralSimple_of_isCentralDivision
    (k : Type u) [Field k] (D : Type v) [DivisionRing D] [Algebra k D]
    (h : IsCentralDivision k D) : IsCentralSimple k D :=
  ⟨inferInstance, h.1, h.2⟩

/-- Bundle the given algebra and its central simplicity properties as Mathlib's `CSA`. -/
def toCSA {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    (h : IsCentralSimple k A) : _root_.CSA.{u, v} k where
  toAlgCat := AlgCat.of k A
  isSimple := h.1
  isCentral := h.2.1
  fin_dim := h.2.2

theorem isCentralSimple_iff_exists_csa
    (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] :
    IsCentralSimple k A ↔ ∃ B : _root_.CSA.{u, v} k, B.toAlgCat = AlgCat.of k A := by
  constructor
  · intro h
    exact ⟨toCSA h, rfl⟩
  · rintro ⟨B, hB⟩
    let P (C : AlgCat.{v} k) : Prop := IsCentralSimple k C
    have h : P B.toAlgCat := ⟨B.isSimple, B.isCentral, B.fin_dim⟩
    exact show P (AlgCat.of k A) from hB ▸ h

end RM03.CSA
