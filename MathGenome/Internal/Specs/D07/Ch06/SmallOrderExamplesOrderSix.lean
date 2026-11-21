import MathGenome.Internal.Specs.D07.Ch01.Presentations
import MathGenome.Internal.Specs.D07.Ch04.SemidirectRecognition

/-! The order-six part of paper.tex:1078–1084. The presented group is the
normal-closure quotient, with precisely the three displayed relations. -/
namespace Specs.D07.Ch06.SmallOrderExamplesOrderSix
universe u
open Specs.D07.Ch04.SemidirectRecognition

abbrev C6 := Multiplicative (ZMod 6)
abbrev S3 := Equiv.Perm (Fin 3)
def relators : Set (FreeGroup Bool) :=
  {FreeGroup.of false ^ 3, FreeGroup.of true ^ 2,
    FreeGroup.of true * FreeGroup.of false * FreeGroup.of true * FreeGroup.of false}
abbrev P := Specs.D07.Ch01.Presentations.presentationValue Bool relators
def a : P := Specs.D07.Ch01.Presentations.generatorValue Bool relators false
def b : P := Specs.D07.Ch01.Presentations.generatorValue Bool relators true

def Classification : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Nat.card G = 6 →
    Nonempty (G ≃* C6) ∨ Nonempty (G ≃* S3)

def Models : Prop :=
  Nat.card C6 = 6 ∧ Nat.card S3 = 6 ∧ ¬ Nonempty (C6 ≃* S3)

def PresentationIdentification : Prop :=
  a ^ 3 = 1 ∧ b ^ 2 = 1 ∧ b * a * b = a⁻¹ ∧
  (∀ x : P, ∃ (i : Fin 3) (j : Fin 2), x = a ^ i.val * b ^ j.val) ∧
  Nat.card P = 6 ∧
  ∃ e : P ≃* S3, e a = threeCycle ∧ e b = transposition

/-- Actual semidirect action, equivalence and generator values. -/
def PresentationSemidirect : Prop :=
  ∃ φ : C2 →* MulAut C3,
    (∀ n : C3, φ (Multiplicative.ofAdd 1) n = n⁻¹) ∧
    φ (Multiplicative.ofAdd 1) ≠ 1 ∧
    ∃ e : P ≃* _root_.SemidirectProduct C3 C2 φ,
      e a = _root_.SemidirectProduct.inl (Multiplicative.ofAdd 1) ∧
      e b = _root_.SemidirectProduct.inr (Multiplicative.ofAdd 1)

/-- Normal cyclic three-factor and complementary cyclic two-factor, including
recognition and the pointwise conjugation action, for every group of order six. -/
def Splitting : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Nat.card G = 6 →
    ∃ (x y : G), orderOf x = 3 ∧ orderOf y = 2 ∧
      (Subgroup.zpowers x).Normal ∧
      (Subgroup.zpowers x).IsComplement' (Subgroup.zpowers y) ∧
      ∃ φ : Subgroup.zpowers y →* MulAut (Subgroup.zpowers x),
        (∀ (h : Subgroup.zpowers y) (n : Subgroup.zpowers x),
          (φ h n : G) = (h : G) * n * (h : G)⁻¹) ∧
        ∃ e : _root_.SemidirectProduct (Subgroup.zpowers x) (Subgroup.zpowers y) φ ≃* G,
          ∀ z, e z = (z.left : G) * (z.right : G)

/-- The nonabelian case has the source's presentation, with its generators
identified, and the same nontrivial inversion semidirect product. -/
def NonabelianCorrespondence : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Nat.card G = 6 →
    (∃ x y : G, x * y ≠ y * x) →
    ∃ (x y : G), orderOf x = 3 ∧ orderOf y = 2 ∧ y * x * y = x⁻¹ ∧
      (∃ e : P ≃* G, e a = x ∧ e b = y) ∧
      ∃ φ : C2 →* MulAut C3,
        (∀ n : C3, φ (Multiplicative.ofAdd 1) n = n⁻¹) ∧
        φ (Multiplicative.ofAdd 1) ≠ 1 ∧
        ∃ e : _root_.SemidirectProduct C3 C2 φ ≃* G,
          e (_root_.SemidirectProduct.inl (Multiplicative.ofAdd 1)) = x ∧
          e (_root_.SemidirectProduct.inr (Multiplicative.ofAdd 1)) = y
end Specs.D07.Ch06.SmallOrderExamplesOrderSix
