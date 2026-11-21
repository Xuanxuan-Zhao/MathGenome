import MathGenome.Internal.Specs.D07.Ch18.FiniteNilpotent
import MathGenome.Internal.D07.Ch18.FiniteNilpotentNormalSylowMultiplication
import MathGenome.Internal.D07.Ch18.NormalizerCondition
import MathGenome.Internal.D07.Ch18.SylowNormalizer
import MathGenome.Internal.D07.Ch18.PgroupNilpotent
import MathGenome.Internal.D07.Ch18.NilpotenceClosure
import Mathlib.Tactic.TFAE

/-!
The four finite nilpotence conditions, paper.tex:5103–5136.

The normalizer condition forces each Sylow normalizer to be the whole group,
because that normalizer is self-normalizing. Normal Sylows give the actual
chosen-family multiplication isomorphism by the upstream construction.
Conversely each Sylow factor has prime-power order, hence is nilpotent;
the finite product is nilpotent, as is its isomorphic image G.
-/

namespace D07.Ch18.FiniteNilpotent

open Specs.D07.Ch18.FiniteNilpotent
open Specs.D07.Ch18.FiniteNilpotentNormalSylowMultiplication

universe u

theorem normalizer_implies_normal_sylow (G : Type u) [Group G] [Finite G]
    (h : normalizerConditionValue G) : AllSylowNormal G := by
  intro p hp P
  apply Subgroup.normalizer_eq_top_iff.mp
  by_contra hn
  have hlt := h (Subgroup.normalizer (P : Set G)) (lt_top_iff_ne_top.mpr hn)
  rw [SylowNormalizer.normalizer_normalizer G p hp P] at hlt
  exact lt_irrefl _ hlt

theorem normal_sylow_implies_multiplication (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G) (h : AllSylowNormal G) :
    sylowMultiplicationValue G P :=
  FiniteNilpotentNormalSylowMultiplication.multiplication_isomorphism G P h

theorem multiplication_implies_nilpotent (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G)
    (h : sylowMultiplicationValue G P) : Group.IsNilpotent G := by
  obtain ⟨e, _⟩ := h
  have hP : ∀ p : PrimeDivisors G, Group.IsNilpotent (P p) := by
    intro p
    have hp : p.val.Prime := Nat.prime_of_mem_primeFactors p.property
    let : Fact p.val.Prime := ⟨hp⟩
    exact PgroupNilpotent.prime_power_nilpotent (P p) p.val
      ((Nat.card G).factorization p.val) hp (P p).card_eq_multiplicity
  have hprod := NilpotenceClosure.finite_product_nilpotent
    (PrimeDivisors G) (fun p => P p) hP
  let := hprod
  exact Group.nilpotent_of_mulEquiv e

theorem chosen_family_equivalences (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G) :
    List.TFAE [Group.IsNilpotent G, normalizerConditionValue G,
      AllSylowNormal G, sylowMultiplicationValue G P] := by
  tfae_have 1 → 2 := fun h => NormalizerCondition.normalizer_condition G h
  tfae_have 2 → 3 := normalizer_implies_normal_sylow G
  tfae_have 3 → 4 := normal_sylow_implies_multiplication G P
  tfae_have 4 → 1 := multiplication_implies_nilpotent G P
  tfae_finish

theorem equivalent_conditions (G : Type u) [Group G] [Finite G] :
    List.TFAE [Group.IsNilpotent G, normalizerConditionValue G,
      AllSylowNormal G,
      ∃ P : ∀ p : PrimeDivisors G, Sylow p.val G, sylowMultiplicationValue G P] := by
  tfae_have 1 → 2 := fun h => NormalizerCondition.normalizer_condition G h
  tfae_have 2 → 3 := normalizer_implies_normal_sylow G
  tfae_have 3 → 4 := by
    intro h
    classical
    let P : ∀ p : PrimeDivisors G, Sylow p.val G := fun _ => Classical.arbitrary _
    exact ⟨P, normal_sylow_implies_multiplication G P h⟩
  tfae_have 4 → 1 := by
    rintro ⟨P, h⟩
    exact multiplication_implies_nilpotent G P h
  tfae_finish

theorem trivial_case (G : Type u) [Group G] [Finite G] [Subsingleton G] :
    Group.IsNilpotent G ∧ normalizerConditionValue G ∧ AllSylowNormal G ∧
      IsEmpty (PrimeDivisors G) ∧
      ∀ P : ∀ p : PrimeDivisors G, Sylow p.val G, sylowMultiplicationValue G P := by
  have hnil : Group.IsNilpotent G := inferInstance
  have hnorm : normalizerConditionValue G := NormalizerCondition.normalizer_condition G hnil
  have hsyl := normalizer_implies_normal_sylow G hnorm
  exact ⟨hnil, hnorm, hsyl,
    (FiniteNilpotentNormalSylowMultiplication.empty_product G).1,
    fun P => normal_sylow_implies_multiplication G P hsyl⟩

end D07.Ch18.FiniteNilpotent
