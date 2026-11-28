import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaQuotients
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.SetTheory.Cardinal.Finite

/-! The simple baby Verma modules for the normalized nonzero nilpotent character. -/

namespace Specs.LieNotes.SuperRestricted.BabyVermaNilpotent

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction

universe u w

/-- The canonical map from the prime-field labels to the scalar field. -/
def primeFieldEmbedding (k : Type u) [Field k] (p : ℕ) [CharP k p] : ZMod p →+* k :=
  ZMod.castHom (dvd_refl p) k

/-- The highest-weight involution for the nilpotent character. -/
def labelInvolution {p : ℕ} (m : ZMod p) : ZMod p :=
  -m - 2

@[simp] theorem labelInvolution_apply_apply {p : ℕ} (m : ZMod p) :
    labelInvolution (labelInvolution m) = m := by
  unfold labelInvolution
  rw [neg_sub, sub_neg_eq_add, add_comm (2 : ZMod p), add_sub_cancel_right]

/-- The orbits of the highest-weight involution. -/
def labelSetoid (p : ℕ) : Setoid (ZMod p) where
  r m n := n = m ∨ n = labelInvolution m
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro m n h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, labelInvolution_apply_apply])
    trans := by
      intro m n r hmn hnr
      rcases hmn with rfl | hmn
      · exact hnr
      rcases hnr with rfl | hnr
      · exact Or.inr hmn
      · exact Or.inl (by rw [hnr, hmn, labelInvolution_apply_apply]) }

/-- All induced modules at the normalized nilpotent character are simple of dimension
`p`. They exhaust the simples, and their labels classify them up to the involution. -/
def babyVermaNilpotentType : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] (hp : 2 < p),
    letI : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
    ∀ (P : restrictedPowerValue k p (Model k)), MatrixPower P →
    ∀ (χ : Model k →ₗ[k] k), χ (E k) = 0 → χ (H k) = 0 → χ (F k) = 1 →
      ∃ (Q : restrictedPowerValue k p (Borel k))
        (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ),
        InheritedPower P Q ∧ CanonicalInclusion P Q χ j ∧ Function.Injective j ∧
        ∃ θ : ZMod p → (BorelAlgebra Q χ →ₐ[k] k),
          (∀ m, LineCharacter Q χ (primeFieldEmbedding k p m) (θ m) ∧
            BasisAndActions j (θ m) (primeFieldEmbedding k p m) ∧
            IsSimpleModule (Ambient P χ) (BabyVerma j (θ m)) ∧
            Module.finrank k (BabyVerma j (θ m)) = p) ∧
          (∀ m (weight : k),
            (∃ v : BabyVerma j (θ m), v ≠ 0 ∧
              generator P χ (E k) • v = 0 ∧ generator P χ (H k) • v = weight • v) ↔
            weight = primeFieldEmbedding k p m ∨
              weight = primeFieldEmbedding k p (labelInvolution m)) ∧
          (∀ m n, Nonempty (BabyVerma j (θ m) ≃ₗ[Ambient P χ] BabyVerma j (θ n)) ↔
            (labelSetoid p).r m n) ∧
          (∀ (V : Type w) [AddCommGroup V] [Module (Ambient P χ) V]
            [IsSimpleModule (Ambient P χ) V],
            ∃ m, Nonempty (BabyVerma j (θ m) ≃ₗ[Ambient P χ] V)) ∧
          (∀ m : ZMod p, labelInvolution m = m ↔ m = -1) ∧
          Nat.card (Quotient (labelSetoid p)) = (p + 1) / 2

end Specs.LieNotes.SuperRestricted.BabyVermaNilpotent
