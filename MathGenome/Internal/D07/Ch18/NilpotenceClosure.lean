import MathGenome.Internal.Specs.D07.Ch18.NilpotenceClosure
import MathGenome.Internal.D07.Ch18.NilpotenceCriteria

/-!
Subgroups, homomorphic images and finite products, paper.tex:5031–5054.

The bound proofs use lower central series termination, including at class zero.
For subgroups, map the subgroup's intrinsic lower series into the ambient group;
for surjections, use the exact image of each lower term. Finite products have
coordinatewise lower terms. Minimal termination lengths therefore give precisely
the maximum, with the empty product treated by subsingletonness.
-/

namespace D07.Ch18.NilpotenceClosure

open Specs.D07.Ch18.CentralSeries
open Specs.D07.Ch18.NilpotenceCriteria
open D07.Ch18.NilpotenceCriteria

universe u v

/-- The source γ_(n+1), expressed in the library's zero-based indexing. -/
theorem lower_value_indexing (G : Type u) [Group G] (n : ℕ) :
    lowerValue G (n + 1) = (⊤ : Subgroup G).lowerCentralSeries n :=
  CentralSeries.lower_indexing G n

theorem subgroup_classAtMost (G : Type u) [Group G] (H : Subgroup G) (c : ℕ)
    (hc : classAtMostValue G c) : classAtMostValue H c := by
  apply (classAtMost_iff_lower H c).mpr
  have hG := (classAtMost_iff_lower G c).mp hc
  rw [lower_value_indexing] at hG ⊢
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_bot, Subgroup.top_subtype_lowerCentralSeries]
  exact eq_bot_iff.mpr ((Subgroup.lowerCentralSeries_mono c le_top).trans hG.le)

theorem surjective_classAtMost (G : Type u) (Q : Type v) [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (c : ℕ)
    (hc : classAtMostValue G c) : classAtMostValue Q c := by
  apply (classAtMost_iff_lower Q c).mpr
  have hG := (classAtMost_iff_lower G c).mp hc
  rw [lower_value_indexing] at hG ⊢
  have hmap := Subgroup.map_lowerCentralSeries (⊤ : Subgroup G) f c
  rw [Subgroup.map_top_of_surjective f hf, hG, Subgroup.map_bot] at hmap
  exact hmap.symm

theorem range_classAtMost (G : Type u) (Q : Type v) [Group G] [Group Q]
    (f : G →* Q) (c : ℕ) (hc : classAtMostValue G c) :
    classAtMostValue f.range c :=
  surjective_classAtMost G f.range f.rangeRestrict f.rangeRestrict_surjective c hc

theorem prod_classAtMost_iff (A : Type u) (B : Type v) [Group A] [Group B] (c : ℕ) :
    classAtMostValue (A × B) c ↔ classAtMostValue A c ∧ classAtMostValue B c := by
  simp only [classAtMost_iff_lower, lower_value_indexing,
    Subgroup.top_lowerCentralSeries_prod, Subgroup.prod_eq_bot_iff]

theorem prod_hasClass (A : Type u) (B : Type v) [Group A] [Group B] (a b : ℕ)
    (ha : hasClassValue A a) (hb : hasClassValue B b) :
    hasClassValue (A × B) (max a b) := by
  obtain ⟨hA, hca⟩ := (hasClass_iff_libraryClass A a).mp ha
  obtain ⟨hB, hcb⟩ := (hasClass_iff_libraryClass B b).mp hb
  let := hA
  let := hB
  apply (hasClass_iff_libraryClass (A × B) (max a b)).mpr
  exact ⟨inferInstance, by rw [Group.nilpotencyClass_prod, hca, hcb]⟩

theorem finite_product_classAtMost_iff (I : Type u) (G : I → Type v)
    [∀ i, Group (G i)] [Finite I] (c : ℕ) :
    classAtMostValue (∀ i, G i) c ↔ ∀ i, classAtMostValue (G i) c := by
  simp only [classAtMost_iff_lower, lower_value_indexing,
    Subgroup.top_lowerCentralSeries_pi_of_finite, Subgroup.pi_eq_bot_iff]

theorem finite_product_nilpotent (I : Type u) (G : I → Type v)
    [∀ i, Group (G i)] [Finite I] (hG : ∀ i, Group.IsNilpotent (G i)) :
    Group.IsNilpotent (∀ i, G i) := by
  let := hG
  exact Group.isNilpotent_pi

theorem finite_product_hasClass (I : Type u) (G : I → Type v)
    [∀ i, Group (G i)] [Fintype I] (c : I → ℕ)
    (hc : ∀ i, hasClassValue (G i) (c i)) :
    hasClassValue (∀ i, G i) (Finset.univ.sup c) := by
  have hG : ∀ i, Group.IsNilpotent (G i) :=
    fun i => ((hasClass_iff_libraryClass (G i) (c i)).mp (hc i)).1
  let := hG
  apply (hasClass_iff_libraryClass (∀ i, G i) (Finset.univ.sup c)).mpr
  refine ⟨finite_product_nilpotent I G hG, ?_⟩
  rw [Group.nilpotencyClass_pi]
  congr 1
  funext i
  exact ((hasClass_iff_libraryClass (G i) (c i)).mp (hc i)).2

theorem empty_product_hasClass_zero (I : Type u) (G : I → Type v)
    [∀ i, Group (G i)] [IsEmpty I] : hasClassValue (∀ i, G i) 0 := by
  apply (class_zero_iff_subsingleton (∀ i, G i)).mpr
  infer_instance

end D07.Ch18.NilpotenceClosure
