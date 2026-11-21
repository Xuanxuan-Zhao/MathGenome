import MathGenome.Internal.D07.Ch05.ConjugacyCounting
import MathGenome.Internal.Specs.D07.Ch05.ClassEquation
import Mathlib.GroupTheory.ClassEquation

/-!
The class equation (`K07.05.class_equation`, paper.tex:899–909).
The cardinality identity is the finite partition by conjugacy classes,
with singleton classes identified with central elements. Substitution of
the accepted conjugacy-counting formula gives the centralizer indices.
-/

namespace D07.Ch05.ClassEquation

universe u

/-- The library's nontrivial-class predicate is exactly source noncentrality. -/
theorem noncentral_class_criterion (G : Type u) [Group G] (x : G) :
    ConjClasses.mk x ∈ ConjClasses.noncenter G ↔ x ∉ Subgroup.center G := by
  classical
  apply not_iff_not.mp
  simp only [not_not]
  constructor
  · intro hx
    have hs : (ConjClasses.mk x).carrier.Subsingleton := Set.not_nontrivial_iff.mp hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply mul_inv_eq_iff_eq_mul.mp
    apply hs _ ConjClasses.mem_carrier_mk
    exact isConj_iff.mpr ⟨g, rfl⟩
  · intro hx
    exact (ConjClasses.mk_bijOn G).mapsTo hx

/-- Sum the actual cardinalities of the noncentral classes, without representatives. -/
theorem class_equation_cardinalities (G : Type u) [Group G] [Finite G] :
    let := Fintype.ofFinite ↥(ConjClasses.noncenter G)
    Nat.card G = Nat.card (Subgroup.center G) +
      ∑ c : ↥(ConjClasses.noncenter G), Nat.card ↥c.val.carrier := by
  classical
  let := Fintype.ofFinite ↥(ConjClasses.noncenter G)
  have h := (Group.nat_card_center_add_sum_card_noncenter_eq_card G).symm
  rwa [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype] at h

/-- For every choice of representatives, replace each class size by its centralizer index. -/
theorem class_equation_indices (G : Type u) [Group G] [Finite G]
    (x : ↥(ConjClasses.noncenter G) → G)
    (hx : ∀ c, x c ∈ c.val.carrier) :
    let := Fintype.ofFinite ↥(ConjClasses.noncenter G)
    Nat.card G = Nat.card (Subgroup.center G) +
      ∑ c : ↥(ConjClasses.noncenter G), (Subgroup.centralizer {x c}).index := by
  classical
  let := Fintype.ofFinite ↥(ConjClasses.noncenter G)
  rw [class_equation_cardinalities G]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  have hc := ConjClasses.mem_carrier_iff_mk_eq.mp (hx c)
  rw [← hc]
  exact ConjugacyCounting.conjugacy_class_card_eq_index G (x c)

/-- A representative set can be chosen arbitrarily, provided each class occurs once. -/
theorem class_equation_representative_set (G : Type u) [Group G] [Finite G]
    (R : Finset G)
    (hR : Set.BijOn ConjClasses.mk (R : Set G) (ConjClasses.noncenter G)) :
    Nat.card G = Nat.card (Subgroup.center G) +
      ∑ x ∈ R, (Subgroup.centralizer {x}).index := by
  classical
  let := Fintype.ofFinite ↥(ConjClasses.noncenter G)
  let e : ↥(R : Set G) ≃ ↥(ConjClasses.noncenter G) := hR.equiv _
  rw [class_equation_cardinalities G]
  congr 1
  calc
    ∑ c : ↥(ConjClasses.noncenter G), Nat.card ↥c.val.carrier =
        ∑ x : ↥(R : Set G), Nat.card ↥(ConjClasses.mk (x : G)).carrier :=
      (Equiv.sum_comp e (fun c => Nat.card ↥c.val.carrier)).symm
    _ = ∑ x : ↥(R : Set G), (Subgroup.centralizer {(x : G)}).index := by
      apply Finset.sum_congr rfl
      intro x _
      exact ConjugacyCounting.conjugacy_class_card_eq_index G (x : G)
    _ = ∑ x ∈ R, (Subgroup.centralizer {x}).index := by
      simpa using (Finset.sum_set_coe (R : Set G)
        (f := fun x : G => (Subgroup.centralizer {x}).index))

end D07.Ch05.ClassEquation
