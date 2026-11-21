import MathGenome.Internal.Specs.D07.Ch20.Hilbert90Additive
import MathGenome.Internal.D07.Ch20.TracePairing
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.Ring.GeomSum

/-! Additive Hilbert 90, including characteristic dividing the degree. -/

universe u v
namespace D07.Ch20.Hilbert90Additive
noncomputable section

open Module LinearMap

theorem fixed_generator_iff (K : Type*) (L : Type*)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L) :
    σ x = x ↔ x ∈ Set.range (algebraMap K L) := by
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).mpr
    intro τ
    obtain ⟨j, rfl⟩ := hσ τ
    exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy L σ from hx) j
  · rintro ⟨c, rfl⟩
    exact σ.commutes c

theorem additive_hilbert90 :
    Specs.D07.Ch20.Hilbert90Additive.AdditiveHilbert90.{u,v} := by
  intro K L _ _ _ _ _ σ hσ a
  let D : L →ₗ[K] L := LinearMap.id - σ.toLinearMap
  have hker : LinearMap.ker D = LinearMap.range (Algebra.linearMap K L) := by
    ext x
    change x - σ x = 0 ↔ x ∈ Set.range (algebraMap K L)
    rw [sub_eq_zero, eq_comm]
    exact fixed_generator_iff K L σ hσ x
  have hkdim : finrank K (LinearMap.ker D) = 1 := by
    rw [hker, LinearMap.finrank_range_of_inj (algebraMap K L).injective,
      Module.finrank_self]
  have hle : LinearMap.range D ≤ LinearMap.ker (Algebra.trace K L) := by
    rintro _ ⟨b, rfl⟩
    change Algebra.trace K L (b - σ b) = 0
    rw [map_sub, Algebra.trace_eq_of_algEquiv σ, sub_self]
  have htrdim : finrank K (LinearMap.range (Algebra.trace K L)) = 1 := by
    rw [LinearMap.range_eq_top.mpr (TracePairing.trace_surjective K L)]
    simp
  have heq : LinearMap.range D = LinearMap.ker (Algebra.trace K L) := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hD := D.finrank_range_add_finrank_ker
    have hT := (Algebra.trace K L).finrank_range_add_finrank_ker
    rw [hkdim] at hD
    rw [htrdim] at hT
    omega
  change a ∈ LinearMap.ker (Algebra.trace K L) ↔ _
  rw [← heq]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb.symm⟩

theorem finite_field_additive :
    Specs.D07.Ch20.Hilbert90Additive.FiniteFieldAdditive.{u,v} := by
  intro K L _ _ _ _ _ a
  let : Fintype K := Fintype.ofFinite K
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic K L
  have hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ := by
    intro τ
    obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).surjective τ
    rw [← hj]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _
  rw [additive_hilbert90 K L σ hσ]
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨-b, ?_⟩
    simp only [Nat.card_eq_fintype_card]
    change b - σ b = σ (-b) - -b
    rw [map_neg]
    simp [sub_eq_add_neg, add_comm]
  · rintro ⟨b, rfl⟩
    refine ⟨-b, ?_⟩
    simp only [Nat.card_eq_fintype_card]
    change σ b - b = -b - σ (-b)
    rw [map_neg]
    simp [sub_eq_add_neg, add_comm]

/-- The norm-one subgroup of a finite field is precisely the subgroup of
`(q-1)`st powers. Here the norm is the operator determinant, connected to
the power formula by `FiniteField.algebraMap_norm_eq_pow_sum`. -/
theorem finite_field_multiplicative :
    Specs.D07.Ch20.Hilbert90Additive.FiniteFieldMultiplicative.{u,v} := by
  intro K L _ _ _ _ _ a ha
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Fintype L := Fintype.ofFinite L
  let N : ℕ := ∑ i ∈ Finset.range (finrank K L), Nat.card K ^ i
  have hN : N ≠ 0 := (geom_sum_pos (Nat.zero_le (Nat.card K))
    (Module.finrank_pos.ne' : finrank K L ≠ 0)).ne'
  have hcard : N * (Nat.card K - 1) = Nat.card L - 1 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := L)]
    exact geom_sum_mul_of_one_le
      (by simpa only [Nat.card_eq_fintype_card] using
        (Fintype.one_lt_card (α := K)).le) _
  constructor
  · intro hn
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
    obtain ⟨j, hj⟩ : Units.mk0 a ha ∈ Submonoid.powers g :=
      mem_powers_iff_mem_zpowers.mpr (hg _)
    have haj : (g : L) ^ j = a := congrArg Units.val hj
    have hord : orderOf g = Nat.card L - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
    have hp : (g ^ (N * j) : Lˣ) = 1 := by
      apply Units.ext
      change (g : L) ^ (N * j) = 1
      rw [Nat.mul_comm N j, pow_mul, haj]
      exact (FiniteField.algebraMap_norm_eq_pow_sum K L a).symm.trans (by simp [hn])
    have hd : Nat.card K - 1 ∣ j := by
      have hd' := orderOf_dvd_of_pow_eq_one hp
      rw [hord, ← hcard] at hd'
      exact (mul_dvd_mul_iff_left hN).mp hd'
    obtain ⟨k, hk⟩ := hd
    refine ⟨g ^ k, ?_⟩
    rw [← haj, hk, Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_comm]
  · rintro ⟨c, rfl⟩
    apply (algebraMap K L).injective
    rw [map_one, FiniteField.algebraMap_norm_eq_pow_sum]
    change ((c : L) ^ (Nat.card K - 1)) ^ N = 1
    rw [← pow_mul, Nat.mul_comm _ N, hcard]
    simpa only [Nat.card_eq_fintype_card] using
      FiniteField.pow_card_sub_one_eq_one (c : L) c.ne_zero

end
end D07.Ch20.Hilbert90Additive
