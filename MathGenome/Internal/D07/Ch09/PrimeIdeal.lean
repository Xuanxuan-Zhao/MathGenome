import MathGenome.Internal.Specs.D07.Ch09.PrimeIdeal
import MathGenome.Internal.D07.Ch08.IdealProduct
import MathGenome.Internal.D07.Ch08.PrincipalDivisibility

/-! Prime ideals and their equivalent ideal-product criterion. -/

universe u

namespace D07.Ch09.PrimeIdeal

open Specs.D07.Ch09.PrimeIdeal

theorem primeCharacterization : PrimeCharacterization.{u} := by
  intro R _ P
  constructor
  · intro hP
    exact ⟨hP.ne_top, fun _ _ hab => hP.mem_or_mem hab⟩
  · rintro ⟨hproper, hmul⟩
    exact ⟨hproper, fun {a b} hab => hmul a b hab⟩

theorem principalProduct : PrincipalProduct.{u} := by
  intro R _ a b
  exact Ideal.span_singleton_mul_span_singleton a b

/-- If one ideal is not contained in a prime ideal, the elementwise prime
condition forces every member of the other ideal into it. Conversely, apply
the product criterion to the two principal ideals. -/
theorem primeProductCharacterization : PrimeProductCharacterization.{u} := by
  intro R _ P
  classical
  constructor
  · intro hP
    refine ⟨hP.ne_top, ?_⟩
    intro I J hIJ
    by_cases hIP : I ≤ P
    · exact Or.inl hIP
    · right
      intro b hb
      by_contra hbP
      apply hIP
      intro a ha
      exact (hP.mem_or_mem (hIJ (Ideal.mul_mem_mul ha hb))).resolve_right hbP
  · rintro ⟨hproper, hmul⟩
    apply (primeCharacterization R P).mpr
    refine ⟨hproper, ?_⟩
    intro a b hab
    have hprincipal : Ideal.span {a} * Ideal.span {b} ≤ P := by
      rw [principalProduct R a b]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hab)
    rcases hmul (Ideal.span {a}) (Ideal.span {b}) hprincipal with ha | hb
    · exact Or.inl (ha (Ideal.mem_span_singleton_self a))
    · exact Or.inr (hb (Ideal.mem_span_singleton_self b))

end D07.Ch09.PrimeIdeal
