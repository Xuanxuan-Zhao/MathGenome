import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreRelations

/-! LA-F05, notes/005, lines 2765–2849. The Cartan subalgebra is maximal
toral and the roots, simple roots, and Killing coroots are the shared objects.
The regular real functional specifies the positive system. -/

universe u

namespace Specs.LieAlgebrasAndRepresentations.ChevalleyBasis

open RootDecomposition RootForm SerreRelations

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

abbrev Root (H : LieSubalgebra ℂ L) := rootSet_value H

/-- The integer interval of roots containing `β` in the direction `α`. -/
def IsString (H : LieSubalgebra ℂ L) (α β : Module.Dual ℂ H) (p q : ℕ) : Prop :=
  ∀ k : ℤ, β + k • α ∈ rootSet_value H ↔ -(p : ℤ) ≤ k ∧ k ≤ (q : ℤ)

def chevalley_basis_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ), (∀ α ∈ rootSet_value H, φ α ≠ 0) →
    ∃ (negRoot : ∀ α : Root H, -(α : Module.Dual ℂ H) ∈ rootSet_value H)
      (x : Root H → L)
      (N : ∀ α β : Root H, α.val + β.val ∈ rootSet_value H → ℤ)
      (σ : L ≃ₗ⁅ℂ⁆ L)
      (b : Module.Basis (simple H φ ⊕ Root H) ℂ L),
      let opp := fun α : Root H => (⟨-α.val, negRoot α⟩ : Root H)
      (∀ α, x α ∈ rootSpace_value H α.val ∧ x α ≠ 0) ∧
      (∀ α, ⁅x α, x (opp α)⁆ = (coroot_value H α.val : L)) ∧
      Function.Involutive σ ∧ (∀ h : H, σ (h : L) = -(h : L)) ∧
      (∀ α, σ (x α) = -x (opp α)) ∧
      (∀ α β (h : α.val + β.val ∈ rootSet_value H),
        ⁅x α, x β⁆ = (N α β h : ℂ) • x ⟨α.val + β.val, h⟩ ∧
        N (opp α) (opp β) (by simpa only [opp, neg_add] using negRoot ⟨_, h⟩) = -N α β h ∧
        ∃ p q : ℕ, IsString H α.val β.val p q ∧
          (N α β h = (p : ℤ) + 1 ∨ N α β h = -((p : ℤ) + 1))) ∧
      (∀ α β, α.val + β.val ≠ 0 → α.val + β.val ∉ rootSet_value H → ⁅x α, x β⁆ = 0) ∧
      (∀ i, b (.inl i) = (coroot_value H i.val : L)) ∧
      (∀ α, b (.inr α) = x α) ∧
      (∀ i j k, ∃ z : ℤ, b.repr ⁅b i, b j⁆ k = (z : ℂ)) ∧
      (∀ c : Root H → ℂ,
        (∀ α, ⁅c α • x α, c (opp α) • x (opp α)⁆ = (coroot_value H α.val : L)) ↔
          ∀ α, c α * c (opp α) = 1) ∧
      (∀ (c : Root H → ℂ), (∀ α, c α * c (opp α) = 1) →
        ∀ α β (h : α.val + β.val ∈ rootSet_value H),
          ⁅c α • x α, c β • x β⁆ =
            (c α * c β / c ⟨α.val + β.val, h⟩ * (N α β h : ℂ)) •
              (c ⟨α.val + β.val, h⟩ • x ⟨α.val + β.val, h⟩))

end Specs.LieAlgebrasAndRepresentations.ChevalleyBasis
