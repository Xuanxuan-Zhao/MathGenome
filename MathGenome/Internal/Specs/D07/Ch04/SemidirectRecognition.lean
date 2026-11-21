import MathGenome.Internal.Specs.D07.Ch04.SemidirectProduct
import MathGenome.Internal.Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
import Mathlib.Data.Fintype.Perm

/-! Independent obligations for paper.tex:802–814. All internal products use
left conjugation and the map `(n,h) ↦ nh`. The finite examples use actual
permutations and the quaternion model identified with the source matrices
upstream. No recognition theorem, complement, or splitting is assumed. -/
namespace Specs.D07.Ch04.SemidirectRecognition

open scoped Pointwise
open Specs.D07.Ch01
universe u

/-- Recognition, including construction and the value of the action. -/
def Recognition : Prop :=
  ∀ (G : Type u) [Group G] (N H : Subgroup G) [N.Normal],
    N ⊓ H = ⊥ → (N : Set G) * (H : Set G) = Set.univ →
    ∃ φ : H →* MulAut N,
      (∀ (h : H) (n : N), (φ h n : G) = (h : G) * n * (h : G)⁻¹) ∧
      ∃ e : _root_.SemidirectProduct N H φ ≃* G,
        ∀ x, e x = (x.left : G) * (x.right : G)

abbrev Q8 := QuaternionGroup 2
def qi : Q8 := .a 1
def minusOne : Q8 := .a 2
def quaternionN : Subgroup Q8 := Subgroup.zpowers qi

/-- The source's order, index, normality, square and involution computations. -/
def QuaternionFacts : Prop :=
  Nat.card Q8 = 8 ∧ Nat.card quaternionN = 4 ∧ quaternionN.index = 2 ∧
  quaternionN.Normal ∧
  (∀ q : Q8, q ≠ 1 → q ≠ minusOne → q ^ 2 = minusOne) ∧
  (∀ q : Q8, (q ≠ 1 ∧ q ^ 2 = 1) ↔ q = minusOne) ∧
  minusOne ∈ quaternionN

def QuaternionComplementOrder : Prop :=
  ∀ H : Subgroup Q8, quaternionN.IsComplement' H → Nat.card H = 2

def QuaternionNoComplement : Prop :=
  ¬ ∃ H : Subgroup Q8, quaternionN.IsComplement' H

/-- Normality is explicit before the quotient homomorphism is formed. -/
def QuaternionNonsplit : Prop :=
  ∀ hN : quaternionN.Normal, letI := hN
    Nat.card (Q8 ⧸ quaternionN) = 2 ∧
    ¬ ∃ s : Q8 ⧸ quaternionN →* Q8,
      (QuotientGroup.mk' quaternionN).comp s = MonoidHom.id _

/-- Tie the obstruction to the exact matrix model in the original source,
with the displayed generator I, rather than an unrelated group of order 8. -/
def QuaternionMatrixObstruction : Prop :=
  ∃ M : Subgroup DihedralQuaternionModelsQuaternionMatrices.MatrixGroup,
    (∀ g : DihedralQuaternionModelsQuaternionMatrices.MatrixGroup,
      g ∈ M ↔ (g : DihedralQuaternionModelsQuaternionMatrices.Mat) ∈
        DihedralQuaternionModelsQuaternionMatrices.eightMatrices) ∧
    ∃ e : Q8 ≃* M,
      (∀ q : Q8, (((e q : M) :
        DihedralQuaternionModelsQuaternionMatrices.MatrixGroup) :
        DihedralQuaternionModelsQuaternionMatrices.Mat) =
          DihedralQuaternionModelsQuaternionMatrices.modelMatrix q) ∧
      (Subgroup.zpowers (e qi)).index = 2 ∧
      (Subgroup.zpowers (e qi)).Normal ∧
      ¬ ∃ H : Subgroup M, (Subgroup.zpowers (e qi)).IsComplement' H

abbrev S3 := Equiv.Perm (Fin 3)
def threeCycle : S3 := Equiv.swap 0 1 * Equiv.swap 1 2
def transposition : S3 := Equiv.swap 0 1
def s3N : Subgroup S3 := Subgroup.zpowers threeCycle
def s3H : Subgroup S3 := Subgroup.zpowers transposition

/-- The concrete subgroups used for the split example satisfy recognition,
and their conjugation is inversion, with noncommuting generators. -/
def SymmetricSubgroups : Prop :=
  orderOf threeCycle = 3 ∧ orderOf transposition = 2 ∧
  s3N.Normal ∧ s3N ⊓ s3H = ⊥ ∧
  (s3N : Set S3) * (s3H : Set S3) = Set.univ ∧
  (∀ n : s3N, transposition * (n : S3) * transposition⁻¹ = ((n : S3)⁻¹)) ∧
  threeCycle * transposition ≠ transposition * threeCycle

abbrev C3 := Multiplicative (ZMod 3)
abbrev C2 := Multiplicative (ZMod 2)

/-- S₃ is C₃ ⋊ C₂ with the nonidentity element acting by inversion.
The generator values identify the cyclic factors with the source subgroups. -/
def SymmetricSplit : Prop :=
  ∃ φ : C2 →* MulAut C3,
    (∀ n : C3, φ (Multiplicative.ofAdd 1) n = n⁻¹) ∧
    φ (Multiplicative.ofAdd 1) ≠ 1 ∧
    ∃ e : _root_.SemidirectProduct C3 C2 φ ≃* S3,
      e (_root_.SemidirectProduct.inl (Multiplicative.ofAdd 1)) = threeCycle ∧
      e (_root_.SemidirectProduct.inr (Multiplicative.ofAdd 1)) = transposition

/-- The untwisted direct product would give the wrong group. -/
def SymmetricNotDirect : Prop := ¬ Nonempty (S3 ≃* C3 × C2)

end Specs.D07.Ch04.SemidirectRecognition
