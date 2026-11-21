import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ElementaryTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ClosureCalculus

/-! The elementary topologies of paper.tex, d10:01:examples.
Canonical definitions are shared with the independent Spec. Topologies on the
same underlying type are explicit, so usual and lower-limit real topologies
are never conflated through a global instance. -/
open Set
open scoped Topology
universe u

namespace D10Topology.Ch01

abbrev realIntervalBasis : Set (Set ℝ) :=
  Specs.D10Topology.Ch01.ElementaryTopologies.realIntervalBasis
abbrev lowerLimitBasis : Set (Set ℝ) :=
  Specs.D10Topology.Ch01.ElementaryTopologies.lowerLimitBasis
@[instance_reducible] def lowerLimitTopology : TopologicalSpace ℝ :=
  Specs.D10Topology.Ch01.ElementaryTopologies.lowerLimitTopology
@[instance_reducible] def cofiniteTopology (X : Type u) : TopologicalSpace X :=
  Specs.D10Topology.Ch01.ElementaryTopologies.cofiniteTopology X
@[instance_reducible] def cocountableTopology (X : Type u) : TopologicalSpace X :=
  Specs.D10Topology.Ch01.ElementaryTopologies.cocountableTopology X

theorem usual_intervals_basis : BasisFor inferInstance realIntervalBasis := by
  apply (basis_iff_mathlib _ _).mpr
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨a, b, _, rfl⟩
    exact isOpen_Ioo
  · intro x U hxU hU
    obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hxU)
    exact ⟨Ioo a b, ⟨a, b, hab.1.trans hab.2, rfl⟩, hab, hsub⟩

theorem lowerLimit_basis_criterion : BasisCriterion lowerLimitBasis := by
  constructor
  · apply eq_univ_of_forall
    intro x
    exact mem_sUnion.mpr ⟨Ico x (x + 1), ⟨x, x + 1, lt_add_one x, rfl⟩,
      le_refl x, lt_add_one x⟩
  · rintro U ⟨a, b, hab, rfl⟩ V ⟨c, d, hcd, rfl⟩ x ⟨hxU, hxV⟩
    refine ⟨Ico x (min b d), ⟨x, min b d, lt_min hxU.2 hxV.2, rfl⟩,
      ⟨le_refl x, lt_min hxU.2 hxV.2⟩, ?_⟩
    intro y hy
    exact ⟨⟨hxU.1.trans hy.1, (lt_min_iff.mp hy.2).1⟩,
      ⟨hxV.1.trans hy.1, (lt_min_iff.mp hy.2).2⟩⟩

theorem lowerLimit_basis : BasisFor lowerLimitTopology lowerLimitBasis :=
  basis_generated _ lowerLimit_basis_criterion

theorem lowerLimit_opens (U : Set ℝ) :
    IsOpen[lowerLimitTopology] U ↔ ∃ A : Set (Set ℝ), A ⊆ lowerLimitBasis ∧ U = ⋃₀ A :=
  basis_open_iff_union _ _ lowerLimit_basis U

theorem lowerLimit_witness :
    IsOpen[lowerLimitTopology] (Ico (0 : ℝ) 1) ∧ ¬ IsOpen (Ico (0 : ℝ) 1) := by
  constructor
  · exact lowerLimit_basis.1 _ ⟨0, 1, zero_lt_one, rfl⟩
  · intro h
    obtain ⟨a, b, hab, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (h.mem_nhds (show (0 : ℝ) ∈ Ico 0 1 from
        ⟨le_refl 0, zero_lt_one⟩))
    obtain ⟨z, haz, hz0⟩ := exists_between hab.1
    exact (not_le_of_gt hz0) (hsub ⟨haz, hz0.trans hab.2⟩).1

theorem lowerLimit_strictly_finer :
    openSets (inferInstance : TopologicalSpace ℝ) ⊂ openSets lowerLimitTopology := by
  have hle : openSets (inferInstance : TopologicalSpace ℝ) ⊆ openSets lowerLimitTopology := by
    apply (basis_comparison _ _ _ _ usual_intervals_basis lowerLimit_basis).mpr
    rintro U ⟨a, b, hab, rfl⟩ x hx
    exact ⟨Ico x b, ⟨x, b, hx.2, rfl⟩, ⟨le_refl x, hx.2⟩,
      fun y hy => ⟨hx.1.trans_le hy.1, hy.2⟩⟩
  exact ⟨hle, fun h => lowerLimit_witness.2 (h lowerLimit_witness.1)⟩

theorem cofinite_opens (X : Type u) (U : Set X) :
    IsOpen[cofiniteTopology X] U ↔ U = ∅ ∨ Uᶜ.Finite := by
  change (U.Nonempty → Uᶜ.Finite) ↔ _
  simp only [nonempty_iff_ne_empty, or_iff_not_imp_left]

theorem cocountable_opens (X : Type u) (U : Set X) :
    IsOpen[cocountableTopology X] U ↔ U = ∅ ∨ Uᶜ.Countable := by
  change (U.Nonempty → Uᶜ.Countable) ↔ _
  simp only [nonempty_iff_ne_empty, or_iff_not_imp_left]

theorem cofinite_topology_axioms (X : Type u) :
    OpenFamilyAxioms {U : Set X | U = ∅ ∨ Uᶜ.Finite} := by
  have heq : {U : Set X | U = ∅ ∨ Uᶜ.Finite} = openSets (cofiniteTopology X) := by
    ext U
    exact (cofinite_opens X U).symm
  rw [heq]
  exact open_axioms _

theorem cocountable_topology_axioms (X : Type u) :
    OpenFamilyAxioms {U : Set X | U = ∅ ∨ Uᶜ.Countable} := by
  have heq : {U : Set X | U = ∅ ∨ Uᶜ.Countable} = openSets (cocountableTopology X) := by
    ext U
    exact (cocountable_opens X U).symm
  rw [heq]
  exact open_axioms _

theorem cofinite_closed (X : Type u) (F : Set X) :
    IsClosed[cofiniteTopology X] F ↔ F.Finite ∨ F = univ := by
  rw [← @isOpen_compl_iff X F (cofiniteTopology X), cofinite_opens]
  simp only [compl_compl, compl_empty_iff, or_comm]

theorem cofinite_infinite_dense (X : Type u) (A : Set X) (hA : A.Infinite) :
    @Dense X (cofiniteTopology X) A := by
  letI := cofiniteTopology X
  apply dense_iff_closure_eq.mpr
  rcases (cofinite_closed X (closure A)).mp isClosed_closure with h | h
  · exact (hA (h.subset subset_closure)).elim
  · exact h

theorem cocountable_closed (X : Type u) (F : Set X) :
    IsClosed[cocountableTopology X] F ↔ F.Countable ∨ F = univ := by
  rw [← @isOpen_compl_iff X F (cocountableTopology X), cocountable_opens]
  simp only [compl_compl, compl_empty_iff, or_comm]

theorem cocountable_countable_closed (X : Type u) (A : Set X) (hA : A.Countable) :
    IsClosed[cocountableTopology X] A :=
  (cocountable_closed X A).mpr (Or.inl hA)

theorem cocountable_uncountable_dense (X : Type u) (A : Set X) (hA : ¬ A.Countable) :
    @Dense X (cocountableTopology X) A := by
  letI := cocountableTopology X
  apply dense_iff_closure_eq.mpr
  rcases (cocountable_closed X (closure A)).mp isClosed_closure with h | h
  · exact (hA (h.mono subset_closure)).elim
  · exact h

end D10Topology.Ch01
