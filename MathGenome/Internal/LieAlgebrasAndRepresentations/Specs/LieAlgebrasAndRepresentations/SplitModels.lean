import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ChevalleyBasis
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreSimplicity
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.TraceForm
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The split model in LA-J02, notes/005, lines 4583–4586 and 4599–4616. -/

noncomputable section

open Module
open scoped TensorProduct

namespace LieAlgebrasAndRepresentations.SplitModels

/-- Integrality of every structure constant in the given complex basis. -/
def IntegralBasis {I L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (b : Basis I ℂ L) : Prop :=
  ∀ i j k, ∃ z : ℤ, b.repr ⁅b i, b j⁆ k = (z : ℂ)

/-- The integer span inside the complex Lie algebra, with the inherited bracket. -/
def integerLattice {I L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (b : Basis I ℂ L)
    (closed : ∀ x ∈ Submodule.span ℤ (Set.range b),
      ∀ y ∈ Submodule.span ℤ (Set.range b), ⁅x, y⁆ ∈ Submodule.span ℤ (Set.range b)) :
    LieSubalgebra ℤ L where
  toSubmodule := Submodule.span ℤ (Set.range b)
  lie_mem' hx hy := closed _ hx _ hy

/-- Ordinary joint eigenspaces of the indicated Cartan generators. -/
def jointSpace {K ι L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (h : ι → L) (χ : ι → K) : Submodule K L where
  carrier := { x | ∀ i, ⁅h i, x⁆ = χ i • x }
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; rw [lie_add, hx i, hy i, smul_add]
  smul_mem' := by
    intro a x hx i
    rw [lie_smul, hx i, smul_smul, smul_smul, mul_comm a]

/-- The integer Killing matrix in the indicated lattice basis. -/
def integralKillingMatrix {I M : Type*} [LieRing M] [Fintype I]
    (b : Basis I ℤ M) : Matrix I I ℤ :=
  fun i j => _root_.killingForm ℤ M (b i) (b j)

/-- The root coordinates on the chosen simple coroots, over the integer lattice. -/
def RootCoordinates {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : Set E} (s : Basis ι ℝ E) (a : R → ι → ℤ) : Prop :=
  ∀ α i, (a α i : ℝ) = rootCartan α.val (s i)

/-- The split Cartan and a complete account of all its ordinary weights. -/
def SplitRootSpaces {K ι κ L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (b : Basis (ι ⊕ κ) K L) (a : κ → ι → K) : Prop :=
  ∃ H : LieSubalgebra K L,
    H.toSubmodule = Submodule.span K (Set.range fun i => b (.inl i)) ∧
    IsLieAbelian H ∧ H.IsCartanSubalgebra ∧
    (∀ i j, ⁅b (.inl i), b (.inl j)⁆ = 0) ∧
    (∀ i α, ⁅b (.inl i), b (.inr α)⁆ = a α i • b (.inr α)) ∧
    Function.Injective a ∧ (∀ α, a α ≠ 0) ∧
    jointSpace (fun i => b (.inl i)) 0 = H.toSubmodule ∧
    (∀ α, jointSpace (fun i => b (.inl i)) (a α) =
      Submodule.span K {b (.inr α)}) ∧
    ∀ χ, χ ≠ 0 → (jointSpace (fun i => b (.inl i)) χ ≠ ⊥ ↔ χ ∈ Set.range a)

end LieAlgebrasAndRepresentations.SplitModels

namespace Specs.LieAlgebrasAndRepresentations.SplitModels

open _root_.LieAlgebrasAndRepresentations
open _root_.LieAlgebrasAndRepresentations.SplitModels
open RootDecomposition RootForm

universe u v w

def latticeClosedType : Prop :=
  ∀ {I : Type u} {L : Type v} [LieRing L] [LieAlgebra ℂ L]
    (b : Basis I ℂ L), IntegralBasis b →
      ∀ x ∈ Submodule.span ℤ (Set.range b),
        ∀ y ∈ Submodule.span ℤ (Set.range b), ⁅x, y⁆ ∈ Submodule.span ℤ (Set.range b)

/-- The lattice, its actual complexification and Killing determinant, and the
same determinant and semisimplicity after base change to any char-zero field. -/
def scalarExtensionType : Prop := by
  classical
  exact ∀ {I : Type u} {L : Type v} [Fintype I] [LieRing L] [LieAlgebra ℂ L]
    [Module.Finite ℂ L] (b : Basis I ℂ L),
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ closed,
    let Z := integerLattice b closed
    ∃ (bZ : Basis I ℤ Z) (e : (ℂ ⊗[ℤ] Z) ≃ₗ⁅ℂ⁆ L),
      (∀ i, (bZ i : L) = b i) ∧
      (∀ z : Z, e (1 ⊗ₜ[ℤ] z) = (z : L)) ∧
      (integralKillingMatrix bZ).det ≠ 0 ∧
      ∀ (K : Type w) [Field K] [CharZero K],
        let bK := bZ.baseChange K
        (∀ i j, _root_.killingForm K (K ⊗[ℤ] Z) (bK i) (bK j) =
          (integralKillingMatrix bZ i j : K)) ∧
        (Matrix.of (fun i j => _root_.killingForm K (K ⊗[ℤ] Z) (bK i) (bK j))).det =
          ((integralKillingMatrix bZ).det : K) ∧
        LieAlgebra.radical K (K ⊗[ℤ] Z) = ⊥

def diagonalSplitType : Prop :=
  ∀ {K : Type w} {ι κ : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
    (b : Basis (ι ⊕ κ) K L) (a : κ → ι → K),
    Function.Injective a → (∀ α, a α ≠ 0) →
    (∀ i j, ⁅b (.inl i), b (.inl j)⁆ = 0) →
    (∀ i α, ⁅b (.inl i), b (.inr α)⁆ = a α i • b (.inr α)) →
    SplitRootSpaces b a

/-- The prescribed Euclidean root system is realized by the base-changed
Chevalley lattice. The root labels reindex the root vectors of the same
Chevalley basis that generates the lattice. The labeled coroots are the
opposite-pair brackets, and the labels preserve all Cartan pairings. -/
def splitModelType : Prop := by
  classical
  exact ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : Set E) (hR : IsRootSystem R),
    letI := hR.finite.fintype
    ∃ (z : E) (ι : Type u) (fi : Fintype ι) (s : Basis ι ℝ E)
      (hs : ∀ i, s i ∈ R)
      (A : Matrix ι ι ℤ),
      letI := fi
      letI := Classical.decEq ι
      letI := Classical.decEq (ι ⊕ R)
      let L := Serre.Algebra A
      ∃ finite : Module.Finite ℂ L,
      letI := finite
      ∃ (H : LieSubalgebra ℂ L)
      (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)
      (rootEmbedding : E →ₗ[ℝ] Module.Dual ℂ H)
      (simpleLabel : ι ≃ SerreRelations.simple H φ)
      (rootLabel : R ≃ rootSet_value H)
      (b : Basis (ι ⊕ R) ℂ L)
      (negRoot : ∀ α : rootSet_value H, -α.val ∈ rootSet_value H)
      (N : ∀ α β : rootSet_value H, α.val + β.val ∈ rootSet_value H → ℤ)
      (σ : L ≃ₗ⁅ℂ⁆ L)
      (a : R → ι → ℤ) (p : R → R → ℤ)
      (closed : ∀ x ∈ Submodule.span ℤ (Set.range b),
        ∀ y ∈ Submodule.span ℤ (Set.range b), ⁅x, y⁆ ∈ Submodule.span ℤ (Set.range b)),
      let Z := integerLattice b closed
      let x (α : rootSet_value H) := b (.inr (rootLabel.symm α))
      let oppRoot (α : rootSet_value H) : rootSet_value H := ⟨-α.val, negRoot α⟩
      let opp (α : R) : R := ⟨-α.val, by
        have h := hR.reflection_mem α.val α.property α.val α.property
        have hn := hR.nonzero α.val α.property
        have he : rootReflection α.val α.val = -α.val := by
          have hne : inner ℝ α.val α.val ≠ 0 := by simpa using hn
          rw [rootReflection, mul_div_cancel_right₀ _ hne, two_smul]
          abel
        rwa [he] at h⟩
      RootRegular R z ∧ IsSimpleBasis R z s ∧
      (∀ i j, (A i j : ℝ) = cartanMatrix s i j) ∧
      SolvableRadical.IsSemisimple_value ℂ L ∧ MaximalTori.IsMaximalToral_value H ∧
      (∀ μ ∈ rootSet_value H, φ μ ≠ 0) ∧
      Function.Injective rootEmbedding ∧
      (∀ α : R, (rootLabel α).val = rootEmbedding α.val) ∧
      (∀ i, (rootLabel ⟨s i, hs i⟩).val = (simpleLabel i).val) ∧
      (∀ i, b (.inl i) = (coroot_value H (simpleLabel i).val : L)) ∧
      (∀ α, b (.inr α) ∈ rootSpace_value H (rootLabel α).val) ∧
      (∀ α, ⁅b (.inr α), b (.inr (opp α))⁆ = (coroot_value H (rootLabel α).val : L)) ∧
      (∀ α, rootLabel (opp α) = oppRoot (rootLabel α)) ∧
      Function.Involutive σ ∧ (∀ h : H, σ (h : L) = -(h : L)) ∧
      (∀ α, σ (x α) = -x (oppRoot α)) ∧
      (∀ α β (h : α.val + β.val ∈ rootSet_value H),
        ⁅x α, x β⁆ = (N α β h : ℂ) • x ⟨α.val + β.val, h⟩ ∧
        N (oppRoot α) (oppRoot β) (by
          simpa only [oppRoot, neg_add] using negRoot ⟨_, h⟩) = -N α β h ∧
        ∃ p q : ℕ,
          ChevalleyBasis.IsString H α.val β.val p q ∧
          (N α β h = (p : ℤ) + 1 ∨ N α β h = -((p : ℤ) + 1))) ∧
      (∀ α β, α.val + β.val ≠ 0 → α.val + β.val ∉ rootSet_value H → ⁅x α, x β⁆ = 0) ∧
      IntegralBasis b ∧ RootCoordinates s a ∧
      (∀ α β, (p α β : ℝ) = rootCartan β.val α.val) ∧
      ∃ (bZ : Basis (ι ⊕ R) ℤ Z) (e : (ℂ ⊗[ℤ] Z) ≃ₗ⁅ℂ⁆ L),
        (∀ i, (bZ i : L) = b i) ∧
        (∀ x : Z, e (1 ⊗ₜ[ℤ] x) = (x : L)) ∧
        (integralKillingMatrix bZ).det ≠ 0 ∧
        ∀ (K : Type w) [Field K] [CharZero K],
          let bK := bZ.baseChange K
          Module.Finite K (K ⊗[ℤ] Z) ∧
          (IsEmpty R → Subsingleton (K ⊗[ℤ] Z)) ∧
          LieAlgebra.radical K (K ⊗[ℤ] Z) = ⊥ ∧
          (Matrix.of (fun i j => _root_.killingForm K (K ⊗[ℤ] Z) (bK i) (bK j))).det =
            ((integralKillingMatrix bZ).det : K) ∧
          SplitRootSpaces bK (fun α i => (a α i : K)) ∧
          (∀ α, ⁅bK (.inr α), bK (.inr (opp α))⁆ ∈
            Submodule.span K (Set.range fun i => bK (.inl i))) ∧
          ∀ α β, ⁅⁅bK (.inr α), bK (.inr (opp α))⁆, bK (.inr β)⁆ =
            (p α β : K) • bK (.inr β)

end Specs.LieAlgebrasAndRepresentations.SplitModels
