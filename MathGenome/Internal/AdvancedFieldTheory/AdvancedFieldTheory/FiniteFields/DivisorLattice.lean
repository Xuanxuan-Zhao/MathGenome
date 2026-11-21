import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.DivisorLattice
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.RootFields

/-!
# The divisor lattice of finite root subfields (FT-E02)

All fields and embeddings lie in the same specified ambient algebraic closure.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]

/-- Inclusion of the actual root subfields of the ambient field. -/
abbrev finiteRootFieldInclusion {m n : ℕ} (h : m ∣ n) :
    finiteRootField k Ω m →ₐ[k] finiteRootField k Ω n :=
  Specs.AdvancedFieldTheory.rootFieldInclusion k Ω h

@[simp] theorem finiteRootFieldInclusion_coe {m n : ℕ} (h : m ∣ n)
    (x : finiteRootField k Ω m) :
    ((finiteRootFieldInclusion k Ω h x : finiteRootField k Ω n) : Ω) = (x : Ω) := rfl

theorem finiteRootFieldInclusion_injective {m n : ℕ} (h : m ∣ n) :
    Function.Injective (finiteRootFieldInclusion k Ω h) :=
  (finiteRootFieldInclusion k Ω h).injective

@[simp] theorem finiteRootFieldInclusion_refl (n : ℕ) :
    finiteRootFieldInclusion k Ω (dvd_refl n) = AlgHom.id k (finiteRootField k Ω n) := by
  ext x
  rfl

@[simp] theorem finiteRootFieldInclusion_comp {l m n : ℕ} (hlm : l ∣ m) (hmn : m ∣ n) :
    (finiteRootFieldInclusion k Ω hmn).comp (finiteRootFieldInclusion k Ω hlm) =
      finiteRootFieldInclusion k Ω (dvd_trans hlm hmn) := by
  ext x
  rfl

/-- Divisibility fixes each element under the longer Frobenius iterate. -/
theorem finiteRootField_le_of_dvd {m n : ℕ} (h : m ∣ n) :
    finiteRootField k Ω m ≤ finiteRootField k Ω n := by
  intro x hx
  exact (finiteRootFieldInclusion k Ω h ⟨x, hx⟩).property

variable [IsAlgClosure k Ω]

/-- The converse uses the degree tower for literal intermediate fields. -/
theorem finiteRootField_le_iff (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    finiteRootField k Ω m ≤ finiteRootField k Ω n ↔ m ∣ n := by
  constructor
  · intro h
    have hd := IntermediateField.finrank_dvd_of_le_right h
    rwa [finiteRootField_finrank k Ω m hm, finiteRootField_finrank k Ω n hn] at hd
  · exact finiteRootField_le_of_dvd k Ω

/-- Intersecting the two literal root fields gives the gcd layer. -/
theorem finiteRootField_inf (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    finiteRootField k Ω m ⊓ finiteRootField k Ω n =
      finiteRootField k Ω (Nat.gcd m n) := by
  let I := finiteRootField k Ω m ⊓ finiteRootField k Ω n
  let := (finiteRootField_finite_galois k Ω m hm).1
  let : FiniteDimensional k I := FiniteDimensional.of_injective
    (IntermediateField.inclusion (show I ≤ finiteRootField k Ω m from inf_le_left)).toLinearMap
    (IntermediateField.inclusion_injective
      (show I ≤ finiteRootField k Ω m from inf_le_left))
  have hg : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm
  have hle : finiteRootField k Ω (Nat.gcd m n) ≤ I :=
    le_inf (finiteRootField_le_of_dvd k Ω (Nat.gcd_dvd_left m n))
      (finiteRootField_le_of_dvd k Ω (Nat.gcd_dvd_right m n))
  have hd : Module.finrank k I ∣ Nat.gcd m n := by
    apply Nat.dvd_gcd
    · have h := IntermediateField.finrank_dvd_of_le_right
        (show I ≤ finiteRootField k Ω m from inf_le_left)
      rwa [finiteRootField_finrank k Ω m hm] at h
    · have h := IntermediateField.finrank_dvd_of_le_right
        (show I ≤ finiteRootField k Ω n from inf_le_right)
      rwa [finiteRootField_finrank k Ω n hn] at h
  symm
  apply IntermediateField.eq_of_le_of_finrank_le hle
  rw [finiteRootField_finrank k Ω (Nat.gcd m n) hg]
  exact Nat.le_of_dvd hg hd

/-- The supremum in the intermediate-field lattice is the compositum in Ω. -/
theorem finiteRootField_sup (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    finiteRootField k Ω m ⊔ finiteRootField k Ω n =
      finiteRootField k Ω (Nat.lcm m n) := by
  let J := finiteRootField k Ω m ⊔ finiteRootField k Ω n
  have hl : 0 < Nat.lcm m n := Nat.lcm_pos hm hn
  have hle : J ≤ finiteRootField k Ω (Nat.lcm m n) :=
    sup_le (finiteRootField_le_of_dvd k Ω (Nat.dvd_lcm_left m n))
      (finiteRootField_le_of_dvd k Ω (Nat.dvd_lcm_right m n))
  let := (finiteRootField_finite_galois k Ω (Nat.lcm m n) hl).1
  let : FiniteDimensional k J := FiniteDimensional.of_injective
    (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)
  have hd : Nat.lcm m n ∣ Module.finrank k J := by
    apply Nat.lcm_dvd
    · have h := IntermediateField.finrank_dvd_of_le_right
        (show finiteRootField k Ω m ≤ J from le_sup_left)
      rwa [finiteRootField_finrank k Ω m hm] at h
    · have h := IntermediateField.finrank_dvd_of_le_right
        (show finiteRootField k Ω n ≤ J from le_sup_right)
      rwa [finiteRootField_finrank k Ω n hn] at h
  apply IntermediateField.eq_of_le_of_finrank_le hle
  rw [finiteRootField_finrank k Ω (Nat.lcm m n) hl]
  exact Nat.le_of_dvd Module.finrank_pos hd

end AdvancedFieldTheory
