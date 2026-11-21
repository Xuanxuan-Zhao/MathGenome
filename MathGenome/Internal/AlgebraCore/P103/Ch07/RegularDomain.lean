import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.RegularDomain
import MathGenome.Internal.AlgebraCore.P103.Ch07.RegularAssociatedGraded
import MathGenome.Internal.AlgebraCore.P103.Ch07.KrullIntersection
import Mathlib.Algebra.Ring.Basic

namespace P103.RegularDomain

noncomputable section
open IsLocalRing P103.Rees
open P103.Specs.Ch07.EmbeddingDimension

universe u
variable {R : Type u} [CommRing R]

/-- A separated ideal-power filtration gives a last nonzero initial class. -/
theorem exists_order (I : Ideal R) (hsep : (⨅ n : ℕ, I ^ n) = ⊥)
    (a : R) (ha : a ≠ 0) :
    ∃ n : ℕ, a ∈ I ^ n ∧ a ∉ I ^ (n + 1) := by
  classical
  have hex : ∃ n : ℕ, a ∉ I ^ n := by
    by_contra h
    have hm : a ∈ (⨅ n : ℕ, I ^ n) := by
      simp only [Submodule.mem_iInf]
      exact fun n => by simpa using not_exists.mp h n
    rw [hsep] at hm
    exact ha hm
  have hn0 : Nat.find hex ≠ 0 := by
    intro hz
    have := Nat.find_spec hex
    rw [hz] at this
    simp at this
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨n, ?_, ?_⟩
  · by_contra h
    have hh := Nat.find_min' hex h
    omega
  · simpa only [hn, Nat.succ_eq_add_one] using Nat.find_spec hex

/-- This transfer uses the actual Rees quotient classes and their multiplication. -/
theorem noZeroDivisors_of_associated [Nontrivial R] (I : Ideal R)
    (hsep : (⨅ n : ℕ, I ^ n) = ⊥) [IsDomain (AssociatedRing I)] :
    NoZeroDivisors R := by
  apply NoZeroDivisors.mk
  intro a b hab
  by_contra h
  have ha : a ≠ 0 := fun ha => h (Or.inl ha)
  have hb : b ≠ 0 := fun hb => h (Or.inr hb)
  obtain ⟨n, han, han'⟩ := exists_order I hsep a ha
  obtain ⟨m, hbm, hbm'⟩ := exists_order I hsep b hb
  have hca : ringClass I n ⟨a, han⟩ ≠ 0 :=
    fun hc => han' ((ringClass_eq_zero_iff I n _).mp hc)
  have hcb : ringClass I m ⟨b, hbm⟩ ≠ 0 :=
    fun hc => hbm' ((ringClass_eq_zero_iff I m _).mp hc)
  have hp := mul_ne_zero hca hcb
  rw [ringClass_mul] at hp
  apply hp
  apply (ringClass_eq_zero_iff I (n + m) _).mpr
  change a * b ∈ I ^ (n + m + 1)
  rw [hab]
  exact Ideal.zero_mem _

/-- A generating family of the least cardinality is minimal in the shared
(deletion) convention, as seen from its basis in the cotangent space. -/
theorem exists_minimal_generators [IsNoetherianRing R] [IsLocalRing R] :
    ∃ x : Fin (embeddingDimensionValue R) → maximalIdeal R,
      MinimalGeneratingFamily x := by
  obtain ⟨x, hx⟩ := (P103.Ch07.EmbeddingDimension.least_generator_count R).1
  obtain ⟨b, hb⟩ := P103.Ch07.EmbeddingDimension.minimum_generators_basis
    R _ x hx (Fintype.card_fin _)
  refine ⟨x, hx, fun i hi => ?_⟩
  have hs : Submodule.span (ResidueField R)
      ((maximalIdeal R).toCotangent '' (x '' (Set.univ \ {i}))) = ⊤ :=
    CotangentSpace.span_image_eq_top_iff.mpr hi
  have he : (maximalIdeal R).toCotangent '' (x '' (Set.univ \ {i})) =
      b '' (Set.univ \ {i}) := by
    rw [← Set.image_comp]
    congr 1
    funext j
    exact (hb j).symm
  rw [he] at hs
  exact b.linearIndependent.notMem_span_image (by simp : i ∉ Set.univ \ {i})
    (hs.symm ▸ Submodule.mem_top)

/-- The canonical associated graded ring is a polynomial domain, including
when the family of variables is empty. -/
theorem associated_isDomain [IsNoetherianRing R] [IsLocalRing R]
    (hreg : regularLocalValue R) : IsDomain (AssociatedRing (maximalIdeal R)) := by
  obtain ⟨x, hx⟩ := exists_minimal_generators (R := R)
  obtain ⟨_, e, _⟩ := P103.RegularAssociatedGraded.graded_isomorphism
    R _ x hreg hx
  exact e.toRingEquiv.symm.toMulEquiv.isDomain _

theorem domain : Specs.P103.RegularDomain.domainType.{u} := by
  intro R _ _ _ hreg
  let I := maximalIdeal R
  have hI : I ≤ Ring.jacobson R := by
    rw [ringJacobson_eq_maximalIdeal]
  have hsep : (⨅ n : ℕ, I ^ n) = ⊥ := by
    have hs := P103.Ch07.KrullIntersection.jacobson_vanishing R I R hI
    simpa only [show ∀ n : ℕ, I ^ n • (⊤ : Submodule R R) = I ^ n from
      fun n => by
        change I ^ n * ⊤ = I ^ n
        exact Ideal.mul_top _] using hs
  let : IsDomain (AssociatedRing I) := associated_isDomain hreg
  let : NoZeroDivisors R := noZeroDivisors_of_associated I hsep
  exact NoZeroDivisors.to_isDomain R

theorem dimension_zero : Specs.P103.RegularDomain.dimensionZeroType.{u} := by
  intro R _ _ _ hreg hd
  exact (P103.Ch07.EmbeddingDimension.regular_dimension_zero R hreg hd).2

end
end P103.RegularDomain
