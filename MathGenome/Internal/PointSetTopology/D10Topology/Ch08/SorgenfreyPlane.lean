import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.SorgenfreyPlane
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.SorgenfreyLindelof
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountableProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityPermanence
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.JonesCounting

open Set TopologicalSpace
open scoped Topology Cardinal

namespace D10Topology.Ch08

@[instance_reducible] def sorgenfreyPlaneTopology : TopologicalSpace (ℝ × ℝ) :=
  Specs.D10Topology.Ch08.SorgenfreyPlane.topology
abbrev sorgenfreyAntiDiagonal : Set (ℝ × ℝ) :=
  Specs.D10Topology.Ch08.SorgenfreyPlane.antiDiagonal
abbrev sorgenfreyRationalPlane : Set (ℝ × ℝ) :=
  Specs.D10Topology.Ch08.SorgenfreyPlane.rationalPlane

section Plane
local instance : TopologicalSpace ℝ := Ch01.lowerLimitTopology
local instance : TopologicalSpace (ℝ × ℝ) := sorgenfreyPlaneTopology

theorem sorgenfreyAntiDiagonal_eq_range :
    sorgenfreyAntiDiagonal = range (fun t : ℝ => (t, -t)) := by
  ext p
  constructor
  · intro hp
    refine ⟨p.1, ?_⟩
    have h : p.1 + p.2 = 0 := hp
    apply Prod.ext
    · rfl
    · dsimp
      linarith
  · rintro ⟨t, rfl⟩
    exact add_neg_cancel t

theorem sorgenfreyPlane_rationals_countable : sorgenfreyRationalPlane.Countable :=
  (countable_range ((↑) : ℚ → ℝ)).prod (countable_range ((↑) : ℚ → ℝ))

theorem sorgenfreyPlane_rationals_dense : Dense sorgenfreyRationalPlane :=
  sorgenfrey_rationals_dense.prod sorgenfrey_rationals_dense

theorem sorgenfreyPlane_separable : SeparableSpace (ℝ × ℝ) :=
  ⟨⟨_, sorgenfreyPlane_rationals_countable, sorgenfreyPlane_rationals_dense⟩⟩

theorem sorgenfreyPlane_firstCountable : FirstCountable sorgenfreyPlaneTopology := by
  let : FirstCountableTopology ℝ := firstCountable_iff_mathlib.mp sorgenfrey_firstCountable
  exact firstCountable_iff_mathlib.mpr inferInstance

theorem sorgenfreyPlane_t3 : Ch07.T3 (ℝ × ℝ) := by
  let : RegularSpace ℝ := sorgenfrey_t3.1
  let : T1Space ℝ := sorgenfrey_t3.2
  exact ⟨inferInstance, inferInstance⟩

/-- Basic rectangles are open in precisely the specified product topology. -/
lemma sorgenfreyPlane_isOpen_rectangle (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    IsOpen (Ico a b ×ˢ Ico c d) :=
  (lowerLimit_isOpen_Ico a b hab).prod (lowerLimit_isOpen_Ico c d hcd)

/-- Off the anti-diagonal, a small rightward rectangle keeps the sum's sign. -/
theorem sorgenfreyAntiDiagonal_closed : IsClosed sorgenfreyAntiDiagonal := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hp' : p.1 + p.2 ≠ 0 := hp
  rcases lt_or_gt_of_ne hp' with hneg | hpos
  · let ε := -(p.1 + p.2) / 2
    have he : 0 < ε := by dsimp [ε]; linarith
    apply Filter.mem_of_superset
      ((sorgenfreyPlane_isOpen_rectangle p.1 (p.1 + ε) p.2 (p.2 + ε)
        (by linarith) (by linarith)).mem_nhds
          (show p ∈ Ico p.1 (p.1 + ε) ×ˢ Ico p.2 (p.2 + ε) from
            ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩))
    intro q hq hE
    have hq' : q.1 + q.2 = 0 := hE
    have h1 := hq.1.2
    have h2 := hq.2.2
    dsimp [ε] at h1 h2
    linarith
  · apply Filter.mem_of_superset
      ((sorgenfreyPlane_isOpen_rectangle p.1 (p.1 + 1) p.2 (p.2 + 1)
        (lt_add_one _) (lt_add_one _)).mem_nhds
          (show p ∈ Ico p.1 (p.1 + 1) ×ˢ Ico p.2 (p.2 + 1) from
            ⟨⟨le_rfl, lt_add_one _⟩, ⟨le_rfl, lt_add_one _⟩⟩))
    intro q hq hE
    have hq' : q.1 + q.2 = 0 := hE
    have h1 := hq.1.1
    have h2 := hq.2.1
    linarith

/-- At a point of E, a rightward rectangle isolates that point in E. -/
theorem sorgenfreyAntiDiagonal_discrete : DiscreteTopology sorgenfreyAntiDiagonal := by
  apply discreteTopology_subtype_iff'.mpr
  intro p hp
  refine ⟨Ico p.1 (p.1 + 1) ×ˢ Ico p.2 (p.2 + 1),
    sorgenfreyPlane_isOpen_rectangle _ _ _ _ (lt_add_one _) (lt_add_one _), ?_⟩
  ext q
  constructor
  · rintro ⟨hq, hE⟩
    have hp' : p.1 + p.2 = 0 := hp
    have hq' : q.1 + q.2 = 0 := hE
    have h1 := hq.1.1
    have h2 := hq.2.1
    apply mem_singleton_iff.mpr
    apply Prod.ext <;> linarith
  · intro hq
    obtain rfl := mem_singleton_iff.mp hq
    exact ⟨⟨⟨le_rfl, lt_add_one _⟩, ⟨le_rfl, lt_add_one _⟩⟩, hp⟩

/-- A bijection of underlying sets; the real domain here has no topology claim. -/
def sorgenfreyAntiDiagonalEquiv : ℝ ≃ sorgenfreyAntiDiagonal where
  toFun t := ⟨(t, -t), add_neg_cancel t⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    have hp : p.1.1 + p.1.2 = 0 := p.2
    apply Prod.ext
    · rfl
    · dsimp
      linarith

theorem sorgenfreyAntiDiagonal_cardinality :
    Cardinal.mk sorgenfreyAntiDiagonal = (2 : Cardinal) ^ ℵ₀ := by
  rw [← Cardinal.mk_congr sorgenfreyAntiDiagonalEquiv, Cardinal.mk_real,
    Cardinal.two_power_aleph0]

lemma sorgenfreyAntiDiagonal_uncountable : ¬ Countable sorgenfreyAntiDiagonal := by
  intro hc
  have h := Cardinal.mk_le_aleph0_iff.mpr hc
  rw [sorgenfreyAntiDiagonal_cardinality, Cardinal.two_power_aleph0] at h
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) h

theorem sorgenfreyAntiDiagonal_not_separable : ¬ SeparableSpace sorgenfreyAntiDiagonal := by
  let := sorgenfreyAntiDiagonal_discrete
  intro h
  exact sorgenfreyAntiDiagonal_uncountable (separableSpace_iff_countable.mp h)

theorem sorgenfreyAntiDiagonal_not_lindelof : ¬ LindelofSpace sorgenfreyAntiDiagonal := by
  let := sorgenfreyAntiDiagonal_discrete
  intro h
  let := h
  exact sorgenfreyAntiDiagonal_uncountable countable_of_Lindelof_of_discrete

theorem sorgenfreyPlane_not_lindelof : ¬ LindelofSpace (ℝ × ℝ) := by
  intro h
  exact sorgenfreyAntiDiagonal_not_lindelof
    (lindelof_closed_subspace h _ sorgenfreyAntiDiagonal_closed)

theorem sorgenfreyPlane_not_normal : ¬ Ch07.Normal (ℝ × ℝ) := by
  let := sorgenfreyAntiDiagonal_discrete
  apply jones_counting sorgenfreyRationalPlane sorgenfreyAntiDiagonal
    sorgenfreyPlane_rationals_dense sorgenfreyAntiDiagonal_closed
  rw [sorgenfreyAntiDiagonal_cardinality]
  exact Cardinal.power_le_power_left two_ne_zero
    (Cardinal.le_aleph0_iff_set_countable.mpr sorgenfreyPlane_rationals_countable)

theorem sorgenfreyPlane_closed_subspace_counterexample :
    SeparableSpace (ℝ × ℝ) ∧ IsClosed sorgenfreyAntiDiagonal ∧
      ¬ SeparableSpace sorgenfreyAntiDiagonal :=
  ⟨sorgenfreyPlane_separable, sorgenfreyAntiDiagonal_closed,
    sorgenfreyAntiDiagonal_not_separable⟩

theorem sorgenfreyPlane_product_counterexample :
    (Lindelof Ch01.lowerLimitTopology ∧ Ch07.Normal ℝ) ∧
      ¬ LindelofSpace (ℝ × ℝ) ∧ ¬ Ch07.Normal (ℝ × ℝ) :=
  ⟨⟨sorgenfrey_lindelof, sorgenfrey_normal⟩,
    sorgenfreyPlane_not_lindelof, sorgenfreyPlane_not_normal⟩

end Plane
end D10Topology.Ch08
