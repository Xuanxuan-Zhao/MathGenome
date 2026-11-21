import MathGenome.Internal.Specs.D07.Ch01.DihedralQuaternionModels
import MathGenome.Internal.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
import MathGenome.Internal.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices

/-!
The two concrete nonabelian families of `paper.tex:363–375`.
The source's `D_{2n}` has `2n` elements and is represented by
`DihedralGroup n`, via its proved action on the entire Euclidean plane.
-/

noncomputable section
namespace D07.Ch01.DihedralQuaternionModels

open Specs.D07.Ch01.DihedralQuaternionModels
open Specs.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries

/-- Unique source normal forms imply that the two specified elements
generate the entire group, so the forms also apply to every signed word. -/
lemma generated_by_normal_forms {G : Type*} [Group G] (n : ℕ) (r s : G)
    (h : ∀ f : G, ∃! p : Fin n × Bool,
      f = if p.2 then r ^ p.1.val * s else r ^ p.1.val) :
    Subgroup.closure ({r, s} : Set G) = ⊤ := by
  apply (Subgroup.eq_top_iff' _).2
  intro f
  obtain ⟨p, hp, _⟩ := h f
  have hr : r ∈ Subgroup.closure ({r, s} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hs : s ∈ Subgroup.closure ({r, s} : Set G) :=
    Subgroup.subset_closure (by simp)
  rw [hp]
  split
  · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hr _) hs
  · exact Subgroup.pow_mem _ hr _

/-- The specified generators fail to commute for every polygon in scope,
including the triangle; the excluded small parameters are exactly 1 and 2. -/
lemma dihedral_generators_do_not_commute (n : ℕ) (hn : 3 ≤ n) :
    (DihedralGroup.r 1 : DihedralGroup n) * .sr 0 ≠ .sr 0 * .r 1 := by
  intro h
  have hneg : (-1 : ZMod n) = 1 := by simpa using h
  rcases ZMod.neg_one_eq_one_iff.mp hneg with h1 | h2 <;> omega

theorem dihedral_models : DihedralModels := by
  intro n c a hn ha
  obtain ⟨hfinite, hcard⟩ :=
    DihedralQuaternionModelsPolygonSymmetries.geometric_order n (vertices n c a) hn
      ⟨c, a, ha, rfl⟩
  obtain ⟨e, hr, hs, hrn, hs2, hsrs, hforms⟩ :=
    DihedralQuaternionModelsPolygonSymmetries.full_geometric_model n c a hn ha
  refine ⟨hfinite, hcard, e, hr, hs, hrn, hs2, hsrs, ?_, hforms, ?_, ?_⟩
  · have h : (e (.sr 0) * e (.r 1)) * e (.sr 0) =
        ((e (.r 1))⁻¹ * e (.sr 0)) * e (.sr 0) := by
      calc
        _ = (e (.r 1))⁻¹ := hsrs
        _ = _ := by rw [mul_assoc, ← pow_two, hs2, mul_one]
    exact mul_right_cancel h
  · exact generated_by_normal_forms n _ _ hforms
  · intro h
    apply dihedral_generators_do_not_commute n hn
    apply e.injective
    simpa only [map_mul] using h

theorem quaternion_models : QuaternionModels :=
  ⟨DihedralQuaternionModelsQuaternionMatrices.matrix_identities,
    DihedralQuaternionModelsQuaternionMatrices.eight_distinct,
    DihedralQuaternionModelsQuaternionMatrices.matrix_closure,
    DihedralQuaternionModelsQuaternionMatrices.quaternion_matrix_model⟩

theorem dihedral_quaternion_models : ConcreteNonabelianFamilies :=
  ⟨dihedral_models, DihedralQuaternionModelsPolygonSymmetries.geometric_order,
    quaternion_models⟩

end D07.Ch01.DihedralQuaternionModels
