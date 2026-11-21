import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.MetricSigmaRefinement
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.LocallyFiniteConventions
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Linarith

/-!
The well-ordered-cover construction of paper.tex, d10:15:metric-sigma.
At scale r, use the points whose r-ball lies in U i and which belong to no
earlier cover member. Balls of radius r/3 about these points give the layer.
Different members have distance greater than r/3, so a ball of radius r/6
meets at most one indexed member.
-/

open Set Metric
open scoped Topology
universe u v

namespace D10Topology.Ch15

theorem metric_sigma_refinement {X : Type u} {I : Type v} [MetricSpace X]
    (U : I → Set X) (ho : ∀ i, IsOpen (U i)) (hU : (⋃ i, U i) = univ) :
    ∃ V : ℕ × I → Set X,
      (∀ j, IsOpen (V j)) ∧ CoverRefinement U V ∧
        SigmaLocallyDiscrete V ∧ ∀ j, V j ⊆ U j.2 := by
  classical
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n =>
    div_pos zero_lt_one (Nat.cast_add_one_pos n)
  let F : ℕ → I → Set X := fun n i =>
    {x | ball x (r n) ⊆ U i ∧ ∀ j, WellOrderingRel j i → x ∉ U j}
  let V : ℕ × I → Set X := fun j =>
    ⋃ x ∈ F j.1 j.2, ball x (r j.1 / 3)
  have hopen : ∀ j, IsOpen (V j) := fun j =>
    isOpen_iUnion fun x => isOpen_iUnion fun _ => isOpen_ball
  have hsub : ∀ j, V j ⊆ U j.2 := by
    intro ⟨n, i⟩ p hp
    obtain ⟨x, hx, hp⟩ := mem_iUnion₂.mp hp
    apply hx.1
    exact ball_subset_ball (show r n / 3 ≤ r n by linarith [hr n]) hp
  have hcover : (⋃ j, V j) = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨i, hxi, hmin⟩ := (IsWellOrder.wf (r := @WellOrderingRel I)).has_min
      {i | x ∈ U i} (iUnion_eq_univ_iff.mp hU x)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (ho i) x hxi
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hxF : x ∈ F n i := by
      refine ⟨(ball_subset_ball hn.le).trans hball, ?_⟩
      intro j hji hxj
      exact hmin j hxj hji
    refine ⟨(n, i), mem_iUnion₂.mpr ⟨x, hxF, ?_⟩⟩
    exact mem_ball_self (by linarith [hr n])
  have hsep : ∀ n i j, i ≠ j → ∀ p ∈ V (n, i), ∀ q ∈ V (n, j),
      r n / 3 < dist p q := by
    intro n i j hij p hp q hq
    obtain ⟨x, hx, hp⟩ := mem_iUnion₂.mp hp
    obtain ⟨y, hy, hq⟩ := mem_iUnion₂.mp hq
    have hxy : r n ≤ dist x y := by
      rcases trichotomous_of (@WellOrderingRel I) i j with h | h | h
      · have hn : ¬ dist y x < r n := fun hdist => hy.2 i h (hx.1 hdist)
        simpa only [dist_comm] using le_of_not_gt hn
      · exact (hij h).elim
      · exact le_of_not_gt (fun hdist => hx.2 j h (hy.1 hdist))
    have ht := dist_triangle x p y
    have ht' := dist_triangle p q y
    rw [dist_comm x p] at ht
    change dist p x < r n / 3 at hp
    change dist q y < r n / 3 at hq
    linarith
  have hdisc : ∀ n, LocallyDiscrete (fun i => V (n, i)) := by
    intro n z
    refine ⟨ball z (r n / 6), ball_mem_nhds z (by linarith [hr n]), ?_⟩
    intro i hi j hj
    by_contra hij
    obtain ⟨p, hp, hpz⟩ := hi
    obtain ⟨q, hq, hqz⟩ := hj
    have hs := hsep n i j hij p hp q hq
    have ht := dist_triangle p z q
    rw [dist_comm z q] at ht
    change dist p z < r n / 6 at hpz
    change dist q z < r n / 6 at hqz
    linarith
  refine ⟨V, hopen, ⟨hcover, fun j => ⟨j.2, hsub j⟩⟩, ?_, hsub⟩
  apply (sigmaLocallyDiscrete_iff_layers V).mpr
  refine ⟨Prod.fst, fun n => ?_⟩
  let e : {j : ℕ × I // j.1 = n} → I := fun j => j.val.2
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · exact a.property.trans b.property.symm
    · exact hab
  have hd := LocallyDiscrete.comp_injective (hdisc n) he
  change LocallyDiscrete (fun j : {j : ℕ × I // j.1 = n} => V (n, e j)) at hd
  have hEq : (fun j : {j : ℕ × I // j.1 = n} => V (n, e j)) =
      (fun j => V j.val) := by
    funext j
    exact congrArg V (Prod.ext j.property.symm rfl)
  rw [hEq] at hd
  exact hd

end D10Topology.Ch15
