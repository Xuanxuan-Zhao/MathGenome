import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.DyadicChains
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Uniformity NNReal SetRel
universe u

namespace D10Topology.Ch12

/-- A fast decreasing reflexive symmetric relation sequence admits the exact
quantitative chain pseudometric. No topology is required for this step. -/
theorem pseudometric_of_dyadic_relations {X : Type u} (V : ℕ → Set (X × X))
    (hrefl : ∀ n x, (x, x) ∈ V n)
    (hsym : ∀ n, SetRel.IsSymm (V n))
    (hcube : ∀ n, V (n + 1) ○ (V (n + 1) ○ V (n + 1)) ⊆ V n) :
    ∃ I : PseudoMetricSpace X,
      (∀ x y, @dist X I.toDist x y ≤ 1) ∧
      ∀ n, V n ⊆ {q | @dist X I.toDist q.1 q.2 ≤ (1 / 2 : ℝ) ^ n} ∧
        {q | @dist X I.toDist q.1 q.2 < (1 / 2 : ℝ) ^ (n + 1)} ⊆ V n := by
  classical
  have hstep (n : ℕ) : V (n + 1) ⊆ V n := by
    rintro ⟨x, y⟩ hxy
    exact hcube n ⟨x, hrefl _ x, x, hrefl _ x, hxy⟩
  have hanti : Antitone V := antitone_nat_of_succ_le hstep
  let (n : ℕ) : SetRel.IsSymm (V n) := hsym n
  let d : X → X → ℝ≥0 := fun x y =>
    if h : ∃ n, (x, y) ∉ V n then (1 / 2) ^ Nat.find h else 0
  have hdself (x : X) : d x x = 0 := by
    simp [d, hrefl]
  have hdsymm (x y : X) : d x y = d y x := by
    simp only [d, SetRel.comm (V _)]
  have hr : (1 / 2 : ℝ≥0) ∈ Ioo (0 : ℝ≥0) 1 :=
    ⟨half_pos one_pos, NNReal.half_lt_self one_ne_zero⟩
  have hle_d : ∀ {x y : X} {n : ℕ},
      (1 / 2) ^ n ≤ d x y ↔ (x, y) ∉ V n := by
    intro x y n
    dsimp only [d]
    split_ifs with h
    · rw [(pow_right_strictAnti₀ hr.1 hr.2).le_iff_ge, Nat.find_le_iff]
      exact ⟨fun ⟨m, hmn, hm⟩ hn => hm (hanti hmn hn), fun h => ⟨n, le_rfl, h⟩⟩
    · push Not at h
      simp only [h, not_true, (pow_pos hr.1 _).not_ge]
  let I := PseudoMetricSpace.ofPreNNDist d hdself hdsymm
  have hdist_le : ∀ x y, @dist X I.toDist x y ≤ d x y :=
    PseudoMetricSpace.dist_ofPreNNDist_le _ _ _
  have hd_le : ∀ x y, ↑(d x y) ≤ 2 * @dist X I.toDist x y := by
    refine PseudoMetricSpace.le_two_mul_dist_ofPreNNDist _ _ _ fun a b c e => ?_
    by_cases H : ∃ n, (a, e) ∉ V n
    · refine (dite_eq_left H).trans_le ?_
      rw [← div_le_iff₀' zero_lt_two, ← mul_one_div (_ ^ _), ← pow_succ]
      simp only [le_max_iff, hle_d, ← not_and_or]
      rintro ⟨hab, hbc, hce⟩
      exact Nat.find_spec H (hcube _ ⟨b, hab, c, hbc, hce⟩)
    · exact (dite_eq_right H).trans_le zero_le
  refine ⟨I, ?_, ?_⟩
  · intro x y
    refine (hdist_le x y).trans ?_
    change (d x y : ℝ) ≤ 1
    have : d x y ≤ 1 := by
      dsimp only [d]
      split_ifs
      · exact pow_le_one₀ zero_le hr.2.le
      · exact zero_le
    exact_mod_cast this
  · intro n
    constructor
    · rintro ⟨x, y⟩ hxy
      refine (hdist_le x y).trans ?_
      have hdlt : d x y < (1 / 2) ^ n := by
        exact lt_of_not_ge (fun h => hle_d.mp h hxy)
      exact_mod_cast hdlt.le
    · rintro ⟨x, y⟩ hp
      by_contra hn
      have hlower : (1 / 2 : ℝ) ^ n ≤ (d x y : ℝ) := by
        exact_mod_cast (hle_d.mpr hn)
      have htwo := hd_le x y
      have heq : (1 / 2 : ℝ) ^ (n + 1) * 2 = (1 / 2 : ℝ) ^ n := by
        rw [pow_succ]
        ring
      change @dist X I.toDist x y < _ at hp
      linarith

/-- The full dyadic chain lemma, with uniform continuity in the original
product uniformity. -/
theorem dyadic_chains : Specs.D10Topology.Ch12.DyadicChains.dyadic_chains := by
  intro X uX V hzero hVpos hsympos hpower
  have hV (n : ℕ) : V n ∈ 𝓤 X := by
    cases n with
    | zero => rw [hzero]; exact univ_mem
    | succ n => exact hVpos n
  have hsym (n : ℕ) :
      Specs.D10Topology.Ch12.UniformConventions.relationInverse (V n) = V n := by
    cases n with
    | zero => simp [hzero, Specs.D10Topology.Ch12.UniformConventions.relationInverse]
    | succ n => exact hsympos n
  have hrefl (n : ℕ) (x : X) : (x, x) ∈ V n := refl_mem_uniformity (hV n)
  have hs (n : ℕ) : SetRel.IsSymm (V n) := by
    constructor
    intro x y hxy
    have : (x, y) ∈ Specs.D10Topology.Ch12.UniformConventions.relationInverse (V n) := by
      rw [hsym n]
      exact hxy
    exact this
  have hc (n : ℕ) : V (n + 1) ○ (V (n + 1) ○ V (n + 1)) ⊆ V n := by
    rintro ⟨a, e⟩ ⟨b, hab, c, hbc, hce⟩
    apply hpower n
    exact ⟨c, ⟨b, ⟨a, rfl, hab⟩, hbc⟩, hce⟩
  obtain ⟨I, hbound, hinc⟩ := pseudometric_of_dyadic_relations V hrefl hs hc
  let p : X → X → ℝ := @dist X I.toDist
  refine ⟨p, ?_, hbound, hinc, ?_⟩
  · let _ := I
    exact ⟨fun _ _ => dist_nonneg, dist_self, dist_comm, dist_triangle⟩
  · have hdiff (a b : X × X) :
        dist (p a.1 a.2) (p b.1 b.2) ≤ p a.1 b.1 + p a.2 b.2 := by
      let _ := I
      exact dist_dist_dist_le _ _ _ _
    apply ((𝓤 (X × X)).basis_sets.uniformContinuous_iff Metric.uniformity_basis_dist).mpr
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (show (1 / 2 : ℝ) < 1 by norm_num)
    let W : Set ((X × X) × (X × X)) :=
      {q | (q.1.1, q.2.1) ∈ V n} ∩ {q | (q.1.2, q.2.2) ∈ V n}
    have hW : W ∈ 𝓤 (X × X) :=
      inter_mem (uniformContinuous_fst (hV n)) (uniformContinuous_snd (hV n))
    refine ⟨W, hW, ?_⟩
    intro a b hab
    have h1 := (hinc n).1 hab.1
    have h2 := (hinc n).1 hab.2
    change @dist X I.toDist a.1 b.1 ≤ _ at h1
    change @dist X I.toDist a.2 b.2 ≤ _ at h2
    apply (hdiff a b).trans_lt
    dsimp only [p]
    linarith

end D10Topology.Ch12

/- Mathlib proof attribution
Adapted portion near line 14:
The Nat.find dyadic distance and the estimates constructing its pseudometric,
adapted to the given relation sequence.

Upstream: Mathlib/Topology/Metrizable/Uniformity.lean (around line 200)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
