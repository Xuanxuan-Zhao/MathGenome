import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.KTopology
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set TopologicalSpace
open scoped Topology
namespace D10Topology.Ch18.KTopology

abbrev K := Specs.D10Topology.Ch18.KTopology.K
abbrev basis := Specs.D10Topology.Ch18.KTopology.basis
abbrev topology := Specs.D10Topology.Ch18.KTopology.topology
abbrev rationalBasis := Specs.D10Topology.Ch18.KTopology.rationalBasis

theorem mem_K (x : ℝ) : x ∈ K ↔ ∃ n : ℕ, 1 ≤ n ∧ x = 1 / (n : ℝ) := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n+1, by omega, by push_cast; rfl⟩
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ⟨m, by push_cast; rfl⟩

private theorem basis_ordinary (a b : ℝ) (h : a < b) : Ioo a b ∈ basis :=
  ⟨a, b, h, Or.inl rfl⟩
private theorem basis_deleted (a b : ℝ) (h : a < b) : Ioo a b \ K ∈ basis :=
  ⟨a, b, h, Or.inr rfl⟩

/-- At a point in a basis member, its underlying ordinary interval is available. -/
theorem basis_interval {U : Set ℝ} (hU : U ∈ basis) {x : ℝ} (hx : x ∈ U) :
    ∃ a b : ℝ, x ∈ Ioo a b ∧
      ((Ioo a b ⊆ U) ∨ (x ∉ K ∧ Ioo a b \ K ⊆ U)) := by
  obtain ⟨a,b,_, rfl | rfl⟩ := hU
  · exact ⟨a,b,hx,Or.inl Subset.rfl⟩
  · exact ⟨a,b,hx.1,Or.inr ⟨hx.2,Subset.rfl⟩⟩

theorem basis_criterion : Ch01.BasisCriterion basis := by
  constructor
  · apply sUnion_eq_univ_iff.mpr
    intro x
    exact ⟨Ioo (x-1) (x+1), basis_ordinary _ _ (by linarith), by constructor <;> linarith⟩
  · intro U hU V hV x hx
    obtain ⟨a,b,hx1,h1⟩ := basis_interval hU hx.1
    obtain ⟨c,d,hx2,h2⟩ := basis_interval hV hx.2
    have hab : max a c < min b d := by
      exact (max_lt hx1.1 hx2.1).trans (lt_min hx1.2 hx2.2)
    have hmem : x ∈ Ioo (max a c) (min b d) :=
      ⟨max_lt hx1.1 hx2.1, lt_min hx1.2 hx2.2⟩
    have hsub : Ioo (max a c) (min b d) ⊆ Ioo a b ∩ Ioo c d := by
      intro y hy
      exact ⟨⟨(le_max_left _ _).trans_lt hy.1, hy.2.trans_le (min_le_left _ _)⟩,
        ⟨(le_max_right _ _).trans_lt hy.1, hy.2.trans_le (min_le_right _ _)⟩⟩
    rcases h1 with h1 | ⟨hk,h1⟩ <;> rcases h2 with h2 | ⟨hk',h2⟩
    · exact ⟨_, basis_ordinary _ _ hab, hmem, fun y hy => ⟨h1 (hsub hy).1, h2 (hsub hy).2⟩⟩
    · exact ⟨_, basis_deleted _ _ hab, ⟨hmem,hk'⟩,
        fun y hy => ⟨h1 (hsub hy.1).1, h2 ⟨(hsub hy.1).2,hy.2⟩⟩⟩
    · exact ⟨_, basis_deleted _ _ hab, ⟨hmem,hk⟩,
        fun y hy => ⟨h1 ⟨(hsub hy.1).1,hy.2⟩, h2 (hsub hy.1).2⟩⟩
    · exact ⟨_, basis_deleted _ _ hab, ⟨hmem,hk⟩,
        fun y hy => ⟨h1 ⟨(hsub hy.1).1,hy.2⟩, h2 ⟨(hsub hy.1).2,hy.2⟩⟩⟩

theorem basis_for : Ch01.BasisFor topology basis := Ch01.basis_generated _ basis_criterion
private theorem basis_mathlib : IsTopologicalBasis (t := topology) basis :=
  (Ch01.basis_iff_mathlib _ _).mp basis_for

theorem finer_than_usual : topology ≤ (inferInstance : TopologicalSpace ℝ) := by
  intro U hU
  have href : ∀ x ∈ U, ∃ a b : ℝ, x ∈ Ioo a b ∧ Ioo a b ⊆ U := by
    intro x hx
    exact mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
  let : TopologicalSpace ℝ := topology
  apply basis_mathlib.isOpen_iff.mpr
  intro x hx
  obtain ⟨a,b,hxab,hsub⟩ := href x hx
  exact ⟨_, basis_ordinary a b (hxab.1.trans hxab.2), hxab, hsub⟩

theorem hausdorff : @T2Space ℝ topology := t2Space_antitone finer_than_usual inferInstance

theorem rational_basis : Ch01.BasisFor topology rationalBasis := by
  let : TopologicalSpace ℝ := topology
  apply (Ch01.basis_iff_mathlib _ _).mpr
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨a,b,hab,h⟩
    apply basis_mathlib.isOpen
    exact ⟨a,b,by exact_mod_cast hab,h⟩
  · intro x U hx hU
    obtain ⟨V,hV,hxV,hVU⟩ := basis_mathlib.isOpen_iff.mp hU x hx
    obtain ⟨a,b,hxab,hV'⟩ := basis_interval hV hxV
    obtain ⟨p,hap,hpx⟩ := exists_rat_btwn hxab.1
    obtain ⟨q,hxq,hqb⟩ := exists_rat_btwn hxab.2
    have hpq : p < q := by exact_mod_cast hpx.trans hxq
    have hsub : Ioo (p : ℝ) q ⊆ Ioo a b := fun _ h => ⟨hap.trans h.1,h.2.trans hqb⟩
    rcases hV' with hV' | ⟨hk,hV'⟩
    · exact ⟨_,⟨p,q,hpq,Or.inl rfl⟩,⟨hpx,hxq⟩,hsub.trans (hV'.trans hVU)⟩
    · exact ⟨_,⟨p,q,hpq,Or.inr rfl⟩,⟨⟨hpx,hxq⟩,hk⟩,
        (sdiff_subset_sdiff_left hsub).trans (hV'.trans hVU)⟩

theorem rational_basis_countable : rationalBasis.Countable := by
  have h : rationalBasis ⊆
      range (fun p : ℚ × ℚ => Ioo (p.1 : ℝ) p.2) ∪
      range (fun p : ℚ × ℚ => Ioo (p.1 : ℝ) p.2 \ K) := by
    rintro U ⟨a,b,_,rfl | rfl⟩
    · exact Or.inl ⟨(a,b),rfl⟩
    · exact Or.inr ⟨(a,b),rfl⟩
  exact ((countable_range _).union (countable_range _)).mono h

theorem second_countable : @SecondCountableTopology ℝ topology := by
  let : TopologicalSpace ℝ := topology
  exact ((Ch01.basis_iff_mathlib _ _).mp rational_basis).secondCountableTopology rational_basis_countable

theorem K_closed : IsClosed[topology] K := by
  let : TopologicalSpace ℝ := topology
  apply isOpen_compl_iff.mp
  apply basis_mathlib.isOpen_iff.mpr
  intro x hx
  refine ⟨_,basis_deleted (x-1) (x+1) (by linarith),?_,sdiff_subset_compl _ _⟩
  exact ⟨⟨by linarith,by linarith⟩,hx⟩

theorem zero_not_mem_K : (0 : ℝ) ∉ K := by
  rintro ⟨n,hn⟩
  have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- An irrational point cannot be one of the reciprocal positive integers. -/
theorem irrational_not_mem_K {x : ℝ} (hx : Irrational x) : x ∉ K := by
  rintro ⟨n,rfl⟩
  exact hx ⟨1 / ((n : ℚ) + 1), by push_cast; rfl⟩

/-- Every neighborhood of zero contains a deleted ordinary interval about zero. -/
theorem zero_neighborhood_interval (U : Set ℝ) (hU : U ∈ @nhds ℝ topology 0) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ Ioo a b \ K ⊆ U := by
  let : TopologicalSpace ℝ := topology
  obtain ⟨V,hV,h0V,hVU⟩ := basis_mathlib.mem_nhds_iff.mp hU
  obtain ⟨a,b,h0ab,hab⟩ := basis_interval hV h0V
  refine ⟨a,b,h0ab.1,h0ab.2,?_⟩
  rcases hab with hab | ⟨_,hab⟩
  · exact sdiff_subset.trans (hab.trans hVU)
  · exact hab.trans hVU

/-- A neighborhood of a point of K contains an ordinary interval about that point. -/
theorem K_neighborhood_interval {x : ℝ} (hx : x ∈ K) (U : Set ℝ)
    (hU : U ∈ @nhds ℝ topology x) :
    ∃ a b : ℝ, x ∈ Ioo a b ∧ Ioo a b ⊆ U := by
  let : TopologicalSpace ℝ := topology
  obtain ⟨V,hV,hxV,hVU⟩ := basis_mathlib.mem_nhds_iff.mp hU
  obtain ⟨a,b,hxab,hab⟩ := basis_interval hV hxV
  rcases hab with hab | ⟨hk,_⟩
  · exact ⟨a,b,hxab,hab.trans hVU⟩
  · exact False.elim (hk hx)

theorem neighborhood_closure_meets_K (U : Set ℝ) (hU : U ∈ @nhds ℝ topology 0) :
    ((@closure ℝ topology U) ∩ K).Nonempty := by
  let : TopologicalSpace ℝ := topology
  obtain ⟨a,b,ha,hb,hab⟩ := zero_neighborhood_interval U hU
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hb
  let k : ℝ := 1 / ((n : ℝ) + 1)
  have hk : k ∈ K := ⟨n,rfl⟩
  have hkpos : 0 < k := by dsimp [k]; positivity
  have hka : a < k := ha.trans hkpos
  refine ⟨k,?_,hk⟩
  apply mem_closure_iff.mpr
  intro W hW hkW
  obtain ⟨c,d,hkcd,hcd⟩ := K_neighborhood_interval hk W (hW.mem_nhds hkW)
  have hlt : max a c < min b d :=
    (max_lt hka hkcd.1).trans (lt_min hn hkcd.2)
  obtain ⟨z,hz,hzlo,hzhi⟩ := exists_irrational_btwn hlt
  refine ⟨z,hcd ⟨(le_max_right _ _).trans_lt hzlo,hzhi.trans_le (min_le_right _ _)⟩,?_⟩
  exact hab ⟨⟨(le_max_left _ _).trans_lt hzlo,hzhi.trans_le (min_le_left _ _)⟩,
    irrational_not_mem_K hz⟩

theorem not_regular : ¬ @RegularSpace ℝ topology := by
  let : TopologicalSpace ℝ := topology
  intro h
  let : RegularSpace ℝ := h
  have h0 : Kᶜ ∈ @nhds ℝ topology 0 := K_closed.isOpen_compl.mem_nhds zero_not_mem_K
  obtain ⟨U,hU,hclosed,hUK⟩ := exists_mem_nhds_isClosed_subset h0
  obtain ⟨x,hx,hxK⟩ := neighborhood_closure_meets_K U hU
  rw [hclosed.closure_eq] at hx
  exact hUK hx hxK

theorem not_metrizable : ¬ @MetrizableSpace ℝ topology := by
  let : TopologicalSpace ℝ := topology
  intro h
  let : MetrizableSpace ℝ := h
  exact not_regular inferInstance

end D10Topology.Ch18.KTopology
