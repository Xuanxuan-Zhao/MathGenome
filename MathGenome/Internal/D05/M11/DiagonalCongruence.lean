import MathGenome.Internal.Specs.D05.M11.DiagonalCongruence
import MathGenome.Internal.D05.M11.Radicals

/-! Orthogonal diagonalization and its radical directions (K05.11.diagonal_congruence). -/
namespace D05.M11.DiagonalCongruence

open Module
open scoped BigOperators

/-- Pairing against a basis vector extracts its diagonal-weighted coordinate. -/
theorem apply_basis_eq_coordinate {K V I : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (B : LinearMap.BilinForm K V) (b : Basis I K V)
    (hO : ∀ i j, i ≠ j → B (b i) (b j) = 0) (x : V) (i : I) :
    B x (b i) = b.repr x i * B (b i) (b i) := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  simp only [B.map_sum₂, LinearMap.map_smul₂, smul_eq_mul]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [hO j i hji, mul_zero]
  · simp

theorem mem_radical_iff_coordinates :
    Specs.D05.M11.DiagonalCongruence.mem_radical_iff_coordinates := by
  intro K V I _ _ _ _ B b hO x
  rw [Radicals.mem_leftRadical]
  constructor
  · intro hx i
    rw [← apply_basis_eq_coordinate B b hO x i]
    exact hx (b i)
  · intro hx y
    conv_lhs => rw [← b.sum_repr y]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i _
    rw [apply_basis_eq_coordinate B b hO x i, hx i, mul_zero]

theorem radical_eq_span : Specs.D05.M11.DiagonalCongruence.radical_eq_span := by
  intro K V I _ _ _ _ B b hO
  classical
  ext x
  rw [mem_radical_iff_coordinates B b hO x, b.mem_span_image]
  constructor
  · intro hx i hi
    exact (mul_eq_zero.mp (hx i)).resolve_left (Finsupp.mem_support_iff.mp hi)
  · intro hx i
    by_cases hi : b.repr x i = 0
    · rw [hi, zero_mul]
    · rw [hx (Finsupp.mem_support_iff.mpr hi), mul_zero]

theorem radical_basis : Specs.D05.M11.DiagonalCongruence.radical_basis := by
  intro K V I _ _ _ _ B b hO
  classical
  let S : Set I := {i | B (b i) (b i) = 0}
  have hli : LinearIndependent K (fun i : S => b i) :=
    b.linearIndependent.comp _ Subtype.val_injective
  have heq : Submodule.span K (Set.range (fun i : S => b i)) =
      Specs.D05.M11.Radicals.leftRadical_value B := by
    rw [radical_eq_span B b hO]
    congr 1
    exact Set.range_comp b Subtype.val |>.trans (by simp [S])
  let c := (Basis.span hli).map (LinearEquiv.ofEq _ _ heq)
  refine ⟨c, ?_⟩
  intro i
  change ((LinearEquiv.ofEq _ _ heq) (Basis.span hli i) : V) = b i
  simp

theorem orthogonal_basis_radical :
    Specs.D05.M11.DiagonalCongruence.orthogonal_basis_radical := by
  intro K V _ _ _ _ hTwo B hB
  letI : Invertible (2 : K) := invertibleOfNonzero hTwo
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hB)
  have hO : ∀ i j, i ≠ j → B (b i) (b j) = 0 :=
    LinearMap.isOrthoᵢ_def.mp hb
  exact ⟨b, hO, radical_basis B b hO⟩

end D05.M11.DiagonalCongruence
