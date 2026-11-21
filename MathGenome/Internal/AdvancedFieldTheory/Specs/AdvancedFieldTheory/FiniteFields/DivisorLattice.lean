import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.RootFields

/-!
Independent specification of FT-E02, Proposition E02 in
notes/003/advanced-field-theory.tex, lines 1081–1107.
The infimum is intersection and the supremum is the compositum of the
literal intermediate subfields of the chosen algebraic closure.
-/

universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]

/-- The literal inclusion for a divisibility of indices. This definition works
also at index zero; the lattice statements below concern positive indices. -/
def rootFieldInclusion {m n : ℕ} (h : m ∣ n) :
    rootField k Ω m →ₐ[k] rootField k Ω n :=
  IntermediateField.inclusion (by
    obtain ⟨r, rfl⟩ := h
    intro x hx
    change ((FiniteField.frobeniusAlgHom k Ω) ^ m) x = x at hx
    change ((FiniteField.frobeniusAlgHom k Ω) ^ (m * r)) x = x
    rw [pow_mul]
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ, AlgHom.mul_apply, hx, ih])

set_option linter.checkUnivs false in
def finiteRootFieldInclusion_type :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    {m n : ℕ}, m ∣ n → (rootField k Ω m →ₐ[k] rootField k Ω n)

def finiteRootFieldInclusion_value : finiteRootFieldInclusion_type := rootFieldInclusion

def finiteRootField_le_iff_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (m n : ℕ), 0 < m → 0 < n →
      (rootField k Ω m ≤ rootField k Ω n ↔ m ∣ n)

def finiteRootField_inf_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (m n : ℕ), 0 < m → 0 < n →
      rootField k Ω m ⊓ rootField k Ω n = rootField k Ω (Nat.gcd m n)

def finiteRootField_sup_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (m n : ℕ), 0 < m → 0 < n →
      rootField k Ω m ⊔ rootField k Ω n = rootField k Ω (Nat.lcm m n)

def finiteRootFieldInclusion_coe_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    {m n : ℕ} (h : m ∣ n) (x : rootField k Ω m),
      ((rootFieldInclusion k Ω h x : rootField k Ω n) : Ω) = (x : Ω)

def finiteRootFieldInclusion_injective_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    {m n : ℕ} (h : m ∣ n), Function.Injective (rootFieldInclusion k Ω h)

def finiteRootFieldInclusion_refl_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    (n : ℕ), rootFieldInclusion k Ω (dvd_refl n) = AlgHom.id k (rootField k Ω n)

def finiteRootFieldInclusion_comp_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    {l m n : ℕ} (hlm : l ∣ m) (hmn : m ∣ n),
    (rootFieldInclusion k Ω hmn).comp (rootFieldInclusion k Ω hlm) =
      rootFieldInclusion k Ω (dvd_trans hlm hmn)

end Specs.AdvancedFieldTheory
