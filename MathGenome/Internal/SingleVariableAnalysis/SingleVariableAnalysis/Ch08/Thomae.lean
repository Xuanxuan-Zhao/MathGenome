import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Thomae
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Criterion
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Dirichlet
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Thomae's function on the closed unit interval (paper.tex:2261–2282).
The proof uses finite low-denominator sets. A point touches at most two closed
partition cells, so their total length is at most twice the mesh. This gives
small upper sums directly, while irrational zeros force all lower sums to zero.
No discontinuity-set integrability criterion or measure integral is used. -/

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators Topology Classical
namespace ThomaeSpec
export Specs.SingleVariableAnalysis.Ch08.Thomae (thomaeValue lowDenominatorsValue)
end ThomaeSpec
noncomputable abbrev thomae := ThomaeSpec.thomaeValue
abbrev thomaeLowDenominators := ThomaeSpec.lowDenominatorsValue

theorem thomae_rational_value : Specs.SingleVariableAnalysis.Ch08.Thomae.rationalValue := by
  intro q hq
  have h : ∃ r : ℚ, (r : ℝ) = (q : ℝ) := ⟨q, rfl⟩
  have heq : Classical.choose h = q := Rat.cast_injective (Classical.choose_spec h)
  simp only [ThomaeSpec.thomaeValue, hq, ite_eq_left, dite_eq_left h, heq]

theorem thomae_irrational_value : Specs.SingleVariableAnalysis.Ch08.Thomae.irrationalValue := by
  intro x hx
  have hn : ¬ ∃ q : ℚ, (q : ℝ) = x := hx
  simp [ThomaeSpec.thomaeValue, hn]

theorem thomae_range (x : ℝ) : 0 ≤ thomae x ∧ thomae x ≤ 1 := by
  classical
  unfold thomae ThomaeSpec.thomaeValue
  split_ifs with hx h
  · have hd : (1 : ℝ) ≤ (Classical.choose h).den := by
      exact_mod_cast (Classical.choose h).den_pos
    exact ⟨by positivity, (div_le_one (by positivity)).mpr hd⟩
  all_goals norm_num

theorem thomae_bounded : Specs.SingleVariableAnalysis.Ch08.Thomae.bounded := by
  exact ⟨⟨0, by rintro _ ⟨x, _, rfl⟩; exact (thomae_range x).1⟩,
    ⟨1, by rintro _ ⟨x, _, rfl⟩; exact (thomae_range x).2⟩⟩

theorem thomae_finite_low_denominators :
    Specs.SingleVariableAnalysis.Ch08.Thomae.finiteLowDenominators := by
  intro N
  let A : Set (ℤ × ℕ) := Set.Icc (0 : ℤ) N ×ˢ Set.Icc (0 : ℕ) N
  have hA : A.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  apply (hA.image (fun p : ℤ × ℕ => (p.1 : ℝ) / (p.2 : ℝ))).subset
  rintro x ⟨q, rfl, hx, hN⟩
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hn0 : (0 : ℝ) ≤ q.num := by
    rw [← (eq_div_iff hd.ne').mp (Rat.cast_def q)]
    exact mul_nonneg hx.1 hd.le
  have hn1 : (q.num : ℝ) ≤ (q.den : ℝ) := (div_le_one hd).mp (by
    simpa only [Rat.cast_def] using hx.2)
  refine ⟨(q.num, q.den), ⟨⟨?_, ?_⟩, ⟨Nat.zero_le _, hN⟩⟩, ?_⟩
  · exact_mod_cast hn0
  · have : (q.num : ℝ) ≤ (N : ℝ) := hn1.trans (by exact_mod_cast hN)
    exact_mod_cast this
  · exact (Rat.cast_def q).symm

theorem thomae_outside_low_denominators :
    Specs.SingleVariableAnalysis.Ch08.Thomae.outsideLowDenominators := by
  intro N hN x hx hn
  refine ⟨(thomae_range x).1, ?_⟩
  by_cases h : ∃ q : ℚ, (q : ℝ) = x
  · obtain ⟨q, rfl⟩ := h
    rw [thomae_rational_value q hx]
    have hd : N < q.den := Nat.lt_of_not_ge (fun hle => hn ⟨q, rfl, hx, hle⟩)
    exact one_div_le_one_div_of_le (by exact_mod_cast hN) (by exact_mod_cast hd.le)
  · have hirr : Irrational x := h
    rw [thomae_irrational_value x hirr]
    positivity

theorem thomae_continuous_irrational :
    Specs.SingleVariableAnalysis.Ch08.Thomae.continuousIrrational := by
  intro x hx hirr
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨N, hN, hsmall⟩ := reciprocal_tail ε hε
  have hxnot : x ∉ thomaeLowDenominators N := by
    rintro ⟨q, hq, _, _⟩
    exact hirr ⟨q, hq⟩
  have hnhds : (thomaeLowDenominators N)ᶜ ∈ 𝓝 x :=
    (thomae_finite_low_denominators N).isClosed.isOpen_compl.mem_nhds hxnot
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ, ?_⟩
  intro y hy hdist
  have hout := thomae_outside_low_denominators N hN y hy (hball hdist)
  rw [thomae_irrational_value x hirr, Real.dist_eq, sub_zero, abs_of_nonneg hout.1]
  have hsmallN := hsmall N le_rfl
  rw [abs_of_pos (one_div_pos.mpr (Nat.cast_pos.mpr hN))] at hsmallN
  exact hout.2.trans_lt hsmallN

theorem thomae_discontinuous_rational :
    Specs.SingleVariableAnalysis.Ch08.Thomae.discontinuousRational := by
  intro q hq hc
  have hp : (0 : ℝ) < 1 / (q.den : ℝ) := by positivity
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousWithinAt_iff.mp hc _ (half_pos hp)
  obtain ⟨a, b, ha, hab, hb, hnear⟩ := interval_inside_unit_neighborhood hq hδ
  obtain ⟨r, hirr, har, hrb⟩ := dirichlet_irrational_density a b hab
  have hrc := hcδ ⟨ha.trans har.le, hrb.le.trans hb⟩ (hnear r ⟨har, hrb⟩)
  rw [thomae_irrational_value r hirr, thomae_rational_value q hq] at hrc
  norm_num [Real.dist_eq, abs_of_pos hp] at hrc
  simp only [one_div] at hp
  linarith

/-- In a strict partition a point lies in at most two closed cells. -/
theorem touching_cells_card_le_two {a b : ℝ} (P : Partition a b) (x : ℝ) :
    (Finset.univ.filter (fun i : Fin P.n => x ∈ cell P i)).card ≤ 2 := by
  classical
  let s := Finset.univ.filter (fun i : Fin P.n => x ∈ cell P i)
  have hcard : s.card ≤ (Finset.univ : Finset Bool).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin P.n => decide (P.point i.castSucc < x))
      (fun _ _ => Finset.mem_univ _)
    intro i hi j hj heq
    have hi' : x ∈ cell P i := (Finset.mem_filter.mp hi).2
    have hj' : x ∈ cell P j := (Finset.mem_filter.mp hj).2
    by_cases hil : P.point i.castSucc < x
    · have hjl : P.point j.castSucc < x := by
        by_contra hn
        simp [hil, hn] at heq
      apply le_antisymm
      · apply le_of_not_gt
        intro hji
        have hp := P.strictMono.monotone
          (show j.succ ≤ i.castSucc from Nat.succ_le_of_lt hji)
        exact (not_lt_of_ge (hj'.2.trans hp)) hil
      · apply le_of_not_gt
        intro hij
        have hp := P.strictMono.monotone
          (show i.succ ≤ j.castSucc from Nat.succ_le_of_lt hij)
        exact (not_lt_of_ge (hi'.2.trans hp)) hjl
    · have hjl : ¬ P.point j.castSucc < x := by
        intro hjl
        simp [hil, hjl] at heq
      apply Fin.castSucc_injective
      apply P.strictMono.injective
      exact (le_antisymm hi'.1 (le_of_not_gt hil)).trans
        (le_antisymm hj'.1 (le_of_not_gt hjl)).symm
  simpa only [Finset.card_univ, Fintype.card_bool] using hcard

/-- Total length of all cells meeting one fixed point. -/
theorem touching_cells_length_le {a b : ℝ} (P : Partition a b) (x : ℝ) :
    (∑ i : Fin P.n, if x ∈ cell P i then cellLength P i else 0) ≤ 2 * mesh P := by
  classical
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin P.n => x ∈ cell P i), mesh P :=
      Finset.sum_le_sum (fun i _ => cellLength_le_mesh P i)
    _ = ((Finset.univ.filter (fun i : Fin P.n => x ∈ cell P i)).card : ℝ) * mesh P := by
      simp
    _ ≤ 2 * mesh P := mul_le_mul_of_nonneg_right
      (by exact_mod_cast touching_cells_card_le_two P x) (mesh_nonneg P)

/-- A finite exceptional set can only affect a small total cell length. -/
theorem upperSum_le_finite_exceptions (f : ℝ → ℝ) (hf : BoundedOnInterval f 0 1)
    (s : Finset ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ 1)
    (hsmall : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ∉ s → f x ≤ c)
    (P : Partition 0 1) :
    upperSum f P hf ≤ c + (s.card : ℝ) * (2 * mesh P) := by
  classical
  have hcoeff (i : Fin P.n) : cellSupremum f P hf i ≤
      c + ∑ r ∈ s, if r ∈ cell P i then (1 : ℝ) else 0 := by
    apply csSup_le ((cell_nonempty P i).image f)
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxs : x ∈ s
    · have hsum : 1 ≤ ∑ r ∈ s, if r ∈ cell P i then (1 : ℝ) else 0 := by
        calc
          1 = (if x ∈ cell P i then (1 : ℝ) else 0) := by simp [hx]
          _ ≤ ∑ r ∈ s, if r ∈ cell P i then (1 : ℝ) else 0 :=
            Finset.single_le_sum (f := fun r => if r ∈ cell P i then (1 : ℝ) else 0)
              (fun r _ => by positivity) hxs
      exact (hf1 x (cell_subset_interval P i hx)).trans (by linarith)
    · exact (hsmall x (cell_subset_interval P i hx) hxs).trans
        (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => by positivity)))
  calc
    upperSum f P hf ≤ ∑ i : Fin P.n,
        (c + ∑ r ∈ s, if r ∈ cell P i then (1 : ℝ) else 0) * cellLength P i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hcoeff i) (cell_positive P i).le)
    _ = c * (∑ i : Fin P.n, cellLength P i) +
        ∑ r ∈ s, ∑ i : Fin P.n, if r ∈ cell P i then cellLength P i else 0 := by
      simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
    _ ≤ c * (∑ i : Fin P.n, cellLength P i) + ∑ _r ∈ s, 2 * mesh P :=
      add_le_add le_rfl (Finset.sum_le_sum (fun r _ => touching_cells_length_le P r))
    _ = c + (s.card : ℝ) * (2 * mesh P) := by
      have hlen : (∑ i : Fin P.n, cellLength P i) = 1 := by
        change (∑ i : Fin P.n, (P.point i.succ - P.point i.castSucc)) = 1
        rw [sum_cell_differences, P.last, P.first, sub_zero]
      rw [hlen, mul_one]
      simp

/-- Density of the irrational zeros forces every lower sum to vanish. -/
theorem thomae_lower_sums_zero : Specs.SingleVariableAnalysis.Ch08.Thomae.lowerSumsZero := by
  intro P hf
  have hzero (i : Fin P.n) : cellInfimum thomae P hf i = 0 := by
    obtain ⟨r, hr, hleft, hright⟩ := dirichlet_irrational_density
      (P.point i.castSucc) (P.point i.succ) (P.strictMono (Fin.castSucc_lt_succ (i := i)))
    apply le_antisymm
    · exact (cellInfimum_le thomae P hf i ⟨hleft.le, hright.le⟩).trans_eq
        (thomae_irrational_value r hr)
    · apply le_csInf ((cell_nonempty P i).image thomae)
      rintro _ ⟨x, _, rfl⟩
      exact (thomae_range x).1
  change (∑ i : Fin P.n, cellInfimum thomae P hf i * cellLength P i) = 0
  simp only [hzero, zero_mul, Finset.sum_const_zero]

/-- Choose a fine partition after fixing the finite low-denominator set. -/
theorem thomae_small_upper_sums : Specs.SingleVariableAnalysis.Ch08.Thomae.smallUpperSums := by
  classical
  intro hf ε hε
  obtain ⟨N, hN, hrecip⟩ := reciprocal_tail (ε / 2) (half_pos hε)
  let s := (thomae_finite_low_denominators N).toFinset
  have hs (x : ℝ) : x ∈ s ↔ x ∈ thomaeLowDenominators N := Set.Finite.mem_toFinset _
  let δ := ε / (4 * ((s.card : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨P, _hmesh, hP⟩ := arbitrarily_fine (by norm_num : (0 : ℝ) < 1) δ hδ
  refine ⟨P, ?_⟩
  have hupper := upperSum_le_finite_exceptions thomae hf s (1 / (N : ℝ))
    (by positivity) (fun x _ => (thomae_range x).2)
    (fun x hx hxs => (thomae_outside_low_denominators N hN x hx
      (fun h => hxs ((hs x).mpr h))).2) P
  have hsmall : 1 / (N : ℝ) < ε / 2 := by
    have ht := hrecip N le_rfl
    rwa [abs_of_pos (one_div_pos.mpr (Nat.cast_pos.mpr hN))] at ht
  have hprod : (s.card : ℝ) * (2 * mesh P) < ε / 2 := by
    have hden : (0 : ℝ) < 4 * ((s.card : ℝ) + 1) := by positivity
    have hmul : mesh P * (4 * ((s.card : ℝ) + 1)) < ε :=
      (lt_div_iff₀ hden).mp hP
    have hm := mesh_nonneg P
    nlinarith
  linarith

theorem thomae_integrable : Specs.SingleVariableAnalysis.Ch08.Thomae.integrable := by
  apply (darboux_criterion thomae (by norm_num : (0 : ℝ) < 1) thomae_bounded).mpr
  intro ε hε
  obtain ⟨P, hP⟩ := thomae_small_upper_sums thomae_bounded ε hε
  refine ⟨P, ?_⟩
  have hzero : lowerSum thomae P thomae_bounded = 0 := thomae_lower_sums_zero P thomae_bounded
  change upperSum thomae P thomae_bounded - lowerSum thomae P thomae_bounded < ε
  rw [hzero, sub_zero]
  exact hP

theorem thomae_integral_zero : Specs.SingleVariableAnalysis.Ch08.Thomae.integralZero := by
  intro h
  have hlower : Set.range (fun P : Partition 0 1 => lowerSum thomae P thomae_bounded) = {0} := by
    ext z
    constructor
    · rintro ⟨P, rfl⟩
      exact thomae_lower_sums_zero P thomae_bounded
    · intro hz
      obtain ⟨P⟩ := partition_exists (by norm_num : (0 : ℝ) ≤ 1)
      exact ⟨P, (thomae_lower_sums_zero P thomae_bounded).trans
        (Set.mem_singleton_iff.mp hz).symm⟩
  have hv := (realIntegral_common_value thomae h (by norm_num) thomae_bounded).1
  change realIntegral thomae h = lowerIntegral thomae _ thomae_bounded at hv
  apply hv.trans
  change sSup _ = 0
  rw [hlower, csSup_singleton]


end SingleVariableAnalysis.Riemann
