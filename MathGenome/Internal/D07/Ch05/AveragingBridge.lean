import MathGenome.Internal.Specs.D07.Ch05.AveragingBridge
import MathGenome.Internal.D07.Ch01.ElementaryGroupLaws
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite averaging of a multiplicative family of linear operators

K07.05.averaging_bridge, paper.tex:930–945. Left multiplication reindexes
the finite sum. No identity-preservation hypothesis on the family is used.
All vector spaces, including the zero space and infinite-dimensional spaces,
are permitted. The canonical average and fixed subspace live in the independent
Specs module so their actual definitions are shared by every statement.
-/

namespace D07.Ch05.AveragingBridge

open Specs.D07.Ch05.AveragingBridge

universe u v w

theorem normalization_cases : NormalizationCases.{u, w} := by
  intro K _ G _
  constructor
  · intro h
    simp [averagingScalar, h]
  · intro h
    simp [averagingScalar, h]

theorem average_invariant : InvariantImage.{u, v, w} := by
  intro K E G _ _ _ _ _ ρ hmul h x
  classical
  have reindex : (∑ g : G, ρ (h * g) x) = ∑ g : G, ρ g x :=
    (D07.Ch01.ElementaryGroupLaws.left_multiplication_bijective G h).sum_comp
      (fun g => ρ g x)
  calc
    ρ h (average ρ x) = averagingScalar K G • ∑ g : G, ρ h (ρ g x) := by
      simp only [average, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    _ = averagingScalar K G • ∑ g : G, ρ (h * g) x := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      rw [hmul, LinearMap.comp_apply]
    _ = average ρ x := by
      rw [reindex]
      simp only [average, LinearMap.smul_apply, LinearMap.sum_apply]

theorem average_fixed : FixesFixedVectors.{u, v, w} := by
  intro K E G _ _ _ _ _ ρ hm x hx
  classical
  have ha := (normalization_cases K G).1 hm
  calc
    average ρ x = averagingScalar K G • ∑ _g : G, x := by
      simp only [average, LinearMap.smul_apply, LinearMap.sum_apply, hx]
    _ = averagingScalar K G • (orderScalar K G • x) := by
      rw [Finset.sum_const, Finset.card_univ, orderScalar, Nat.cast_smul_eq_nsmul]
    _ = x := by rw [ha, smul_smul, inv_mul_cancel₀ hm, one_smul]

theorem average_idempotent : IdempotentAverage.{u, v, w} := by
  intro K E G _ _ _ _ _ ρ hmul hm
  apply LinearMap.ext
  intro x
  exact average_fixed K E G ρ hm (average ρ x)
    (fun h => average_invariant K E G ρ hmul h x)

theorem range_average : RangeAverage.{u, v, w} := by
  intro K E G _ _ _ _ _ ρ hmul hm
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact fun h => average_invariant K E G ρ hmul h y
  · intro x hx
    exact ⟨x, average_fixed K E G ρ hm x hx⟩

theorem zero_order : ZeroOrder.{u, v, w} := by
  intro K E G _ _ _ _ _ ρ hm
  have ha := (normalization_cases K G).2 hm
  exact ⟨ha, by simp [average, ha]⟩

theorem trivial_representation_failure : TrivialRepresentationFailure.{u, v, w} := by
  intro K E G _ _ _ _ _ _ hm
  dsimp only
  let ρ : G → E →ₗ[K] E := fun _ => LinearMap.id
  change (∀ g h, ρ (g * h) = (ρ g).comp (ρ h)) ∧ _
  have hzero : average ρ = 0 := (zero_order K E G ρ hm).2
  have htop : fixedSubspace ρ = ⊤ := by
    apply le_antisymm le_top
    intro x _ g
    rfl
  have hnonzero : fixedSubspace ρ ≠ ⊥ := by
    rw [htop]
    exact top_ne_bot
  refine ⟨?_, htop, hnonzero, ?_, ?_⟩
  · intro g h
    exact LinearMap.id_comp LinearMap.id |>.symm
  · obtain ⟨x, hx⟩ := exists_ne (0 : E)
    refine ⟨x, hx, fun _ => rfl, ?_⟩
    change average ρ x ≠ x
    rw [hzero, LinearMap.zero_apply]
    exact hx.symm
  · rw [hzero, LinearMap.range_zero]
    exact Ne.symm hnonzero

end D07.Ch05.AveragingBridge
