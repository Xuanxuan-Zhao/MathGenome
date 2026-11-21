import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.SorgenfreyLindelof
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.SorgenfreyLine
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.RegularLindelofNormal

/-! Lindelöfness of the lower-limit real line, paper.tex d10:08:sorgenfrey-line.
The auxiliary argument takes place in the usual real topology: the interiors
of a cover by [x,b x) have a countable subfamily with the same union. Outside
that union the corresponding nonempty open intervals are pairwise disjoint,
so there are only countably many remaining left endpoints.
-/
open Set TopologicalSpace
universe v

namespace D10Topology.Ch08

/-- Any choice of a right endpoint beyond each real point gives a countable
cover by the associated half-open intervals. Here ℝ has its usual topology. -/
lemma countable_halfOpen_refinement (b : ℝ → ℝ) (hb : ∀ x, x < b x) :
    ∃ C : Set ℝ, C.Countable ∧ (⋃ x ∈ C, Ico x (b x)) = univ := by
  classical
  let O := ⋃ x, Ioo x (b x)
  have hdisj : Oᶜ.PairwiseDisjoint (fun x => Ioo x (b x)) := by
    intro x hx y hy hxy
    apply disjoint_left.mpr
    intro z hzx hzy
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · have hby : b x ≤ y := le_of_not_gt (fun h =>
        hy (mem_iUnion.mpr ⟨x, hlt, h⟩))
      exact (not_lt_of_ge (hzx.2.le.trans hby)) hzy.1
    · have hbx : b y ≤ x := le_of_not_gt (fun h =>
        hx (mem_iUnion.mpr ⟨y, hlt, h⟩))
      exact (not_lt_of_ge (hzy.2.le.trans hbx)) hzx.1
  have hE : Oᶜ.Countable := hdisj.countable_of_Ioo (fun x _ => hb x)
  obtain ⟨C, hC, hcov⟩ := isOpen_iUnion_countable (fun x => Ioo x (b x))
    (fun _ => isOpen_Ioo)
  refine ⟨C ∪ Oᶜ, hC.union hE, eq_univ_of_forall (fun x => ?_)⟩
  by_cases hx : x ∈ O
  · have hx' : x ∈ ⋃ y ∈ C, Ioo y (b y) := hcov.symm ▸ hx
    obtain ⟨y, hyC, hxy⟩ := mem_iUnion₂.mp hx'
    exact mem_iUnion₂.mpr ⟨y, Or.inl hyC, hxy.1.le, hxy.2⟩
  · exact mem_iUnion₂.mpr ⟨x, Or.inr hx, le_rfl, hb x⟩

section LowerLimit
local instance : TopologicalSpace ℝ := Ch01.lowerLimitTopology

/-- The countable-subcover assertion for an arbitrary indexed open cover. -/
theorem sorgenfrey_countable_subcover {ι : Type v} (U : ι → Set ℝ)
    (ho : ∀ i, IsOpen (U i)) (hc : (⋃ i, U i) = univ) :
    ∃ J : Set ι, J.Countable ∧ (⋃ i ∈ J, U i) = univ := by
  classical
  have hcover : ∀ x : ℝ, ∃ i, x ∈ U i := by
    intro x
    exact mem_iUnion.mp (hc.symm ▸ mem_univ x)
  choose i hi using hcover
  have href : ∀ x : ℝ, ∃ b > x, Ico x b ⊆ U (i x) :=
    fun x => (lowerLimit_isOpen_iff _).mp (ho (i x)) x (hi x)
  choose b hb hsub using href
  obtain ⟨C, hC, hcov⟩ := countable_halfOpen_refinement b hb
  refine ⟨i '' C, hC.image i, eq_univ_of_forall (fun x => ?_)⟩
  obtain ⟨y, hyC, hxy⟩ := mem_iUnion₂.mp (hcov.symm ▸ mem_univ x)
  exact mem_iUnion₂.mpr ⟨i y, mem_image_of_mem i hyC, hsub y hxy⟩

theorem sorgenfrey_lindelof : Lindelof Ch01.lowerLimitTopology := by
  apply lindelof_iff_countable_subcover.mpr
  exact fun U ho hc => sorgenfrey_countable_subcover U ho hc

theorem sorgenfrey_normal : Ch07.Normal ℝ :=
  regular_lindelof_normal sorgenfrey_t3.1 sorgenfrey_lindelof

theorem sorgenfrey_t4 : Ch07.T4 ℝ :=
  ⟨sorgenfrey_normal, sorgenfrey_t3.2⟩

end LowerLimit
end D10Topology.Ch08
