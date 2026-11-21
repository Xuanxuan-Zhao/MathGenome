import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.SorgenfreyLine
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ElementaryTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.ShrinkingHierarchy
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.MetrizableCountability
import Mathlib.Analysis.Real.Cardinality

/-! Basic properties of the actual lower-limit topology on ℝ.
The proofs use the chapter 1 basis, without changing the underlying real type.
Non-second-countability follows by assigning distinct basis members to distinct
left endpoints. Nonmetrizability then uses separability and metric countability.
-/
open Set Filter TopologicalSpace
open scoped Topology

namespace D10Topology.Ch08

section LowerLimit
local instance : TopologicalSpace ℝ := Ch01.lowerLimitTopology

/-- The accepted chapter 1 basis, in Mathlib's neighborhood-basis interface. -/
lemma lowerLimit_topologicalBasis : IsTopologicalBasis Ch01.lowerLimitBasis :=
  (Ch01.basis_iff_mathlib _ _).mp Ch01.lowerLimit_basis

lemma lowerLimit_isOpen_Ico (a b : ℝ) (hab : a < b) : IsOpen (Ico a b) :=
  Ch01.lowerLimit_basis.1 _ ⟨a, b, hab, rfl⟩

/-- An interval beginning at the point can be used in every neighborhood. -/
lemma lowerLimit_nhds_basis (x : ℝ) : (𝓝 x).HasBasis (x < ·) (Ico x ·) := by
  constructor
  intro N
  constructor
  · intro hN
    obtain ⟨U, ⟨a, b, _, rfl⟩, hx, hUN⟩ := lowerLimit_topologicalBasis.mem_nhds_iff.mp hN
    exact ⟨b, hx.2, (Ico_subset_Ico_left hx.1).trans hUN⟩
  · rintro ⟨b, hxb, hbN⟩
    exact mem_of_superset ((lowerLimit_isOpen_Ico x b hxb).mem_nhds ⟨le_rfl, hxb⟩) hbN

lemma lowerLimit_isOpen_iff (U : Set ℝ) :
    IsOpen U ↔ ∀ x ∈ U, ∃ b > x, Ico x b ⊆ U := by
  simp only [isOpen_iff_mem_nhds, (lowerLimit_nhds_basis _).mem_iff]

theorem sorgenfrey_basic_clopen (a b : ℝ) (hab : a < b) : IsClopen (Ico a b) := by
  refine ⟨?_, lowerLimit_isOpen_Ico a b hab⟩
  apply isOpen_compl_iff.mp
  apply (lowerLimit_isOpen_iff _).mpr
  intro x hx
  by_cases hxa : x < a
  · refine ⟨a, hxa, ?_⟩
    intro y hy h
    exact (not_lt_of_ge h.1) hy.2
  · have hbx : b ≤ x := le_of_not_gt (fun hxb => hx ⟨le_of_not_gt hxa, hxb⟩)
    refine ⟨x + 1, lt_add_one x, ?_⟩
    intro y hy h
    exact (not_lt_of_ge (hbx.trans hy.1)) h.2

theorem sorgenfrey_t3 : Ch07.T3 ℝ := by
  constructor
  · apply RegularSpace.of_hasBasis lowerLimit_nhds_basis
    intro a b hab
    exact (sorgenfrey_basic_clopen a b hab).isClosed
  · apply t1Space_iff_exists_open.mpr
    intro x y hxy
    rcases lt_or_gt_of_ne hxy with h | h
    · refine ⟨Ico x y, lowerLimit_isOpen_Ico x y h, ⟨le_rfl, h⟩, ?_⟩
      simp
    · refine ⟨Ico x (x + 1), lowerLimit_isOpen_Ico x (x + 1) (lt_add_one x),
        ⟨le_rfl, lt_add_one x⟩, ?_⟩
      exact fun hy => (not_le_of_gt h) hy.1

theorem sorgenfrey_reciprocal_localBase (x : ℝ) :
    Ch01.LocalBase Ch01.lowerLimitTopology x
      (range (fun n : ℕ => Ico x (x + 1 / (n + 1 : ℝ)))) := by
  constructor
  · rintro V ⟨n, rfl⟩
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    exact ⟨_, lowerLimit_isOpen_Ico _ _ (lt_add_of_pos_right _ hpos),
      ⟨le_rfl, lt_add_of_pos_right _ hpos⟩, subset_rfl⟩
  · intro N hN
    obtain ⟨b, hxb, hbN⟩ := (lowerLimit_nhds_basis x).mem_iff.mp
      ((Ch01.neighborhood_iff_mem_nhds _ _ _).mp hN)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hxb)
    refine ⟨_, mem_range_self n, ?_⟩
    apply Subset.trans _ hbN
    apply Ico_subset_Ico_right
    linarith

theorem sorgenfrey_firstCountable : FirstCountable Ch01.lowerLimitTopology := by
  intro x
  exact ⟨_, countable_range _, sorgenfrey_reciprocal_localBase x⟩

theorem sorgenfrey_rationals_dense : Dense (range ((↑) : ℚ → ℝ)) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨b, hxb, hsub⟩ := (lowerLimit_isOpen_iff U).mp hU x hx
  obtain ⟨q, hxq, hqb⟩ := exists_rat_btwn hxb
  exact ⟨q, hsub ⟨hxq.le, hqb⟩, mem_range_self q⟩

theorem sorgenfrey_separable : SeparableSpace ℝ :=
  ⟨⟨_, countable_range _, sorgenfrey_rationals_dense⟩⟩

theorem sorgenfrey_not_secondCountable : ¬ SecondCountableTopology ℝ := by
  classical
  intro h
  let := h
  obtain ⟨B, hBc, _, hB⟩ := exists_countable_basis ℝ
  have hex : ∀ x : ℝ, ∃ U ∈ B, x ∈ U ∧ U ⊆ Ico x (x + 1) := by
    intro x
    exact hB.exists_subset_of_mem_open ⟨le_rfl, lt_add_one x⟩
      (lowerLimit_isOpen_Ico _ _ (lt_add_one x))
  choose U hUB hxU hsub using hex
  have hinj : Function.Injective U := by
    intro x y heq
    apply le_antisymm
    · exact (hsub x (heq ▸ hxU y)).1
    · exact (hsub y (heq ▸ hxU x)).1
  have hc : (univ : Set ℝ).Countable :=
    countable_of_injective_of_countable_image hinj.injOn
      (hBc.mono (by rintro _ ⟨x, _, rfl⟩; exact hUB x))
  exact (not_countable_univ : ¬ (univ : Set ℝ).Countable) hc

theorem sorgenfrey_not_metrizable : ¬ Ch09.Metrizable Ch01.lowerLimitTopology := by
  intro hm
  exact sorgenfrey_not_secondCountable
    ((metrizable_secondCountable_iff_separable hm).mpr sorgenfrey_separable)

end LowerLimit
end D10Topology.Ch08
