import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.IntegralTest
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Monotone
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Nonnegative

namespace SingleVariableAnalysis.Riemann.Improper
open scoped BigOperators Topology
open Filter

/-- Bounds at the endpoints give the boundedness needed by the proper
monotone integrability theorem; no continuity is required. -/
theorem decreasing_local_integrable (f : ℝ → ℝ) (hm : AntitoneOn f (Set.Ici 1))
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : RealIntegrable f a b := by
  have hb : BoundedOnInterval f a b := by
    constructor
    · refine ⟨f b, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hm (ha.trans hx.1) (ha.trans hab) hx.2
    · refine ⟨f a, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hm ha (ha.trans hx.1) hx.1
  exact real_monotone_integrable f hab hb
    (Or.inr fun _ hx _ hy hxy => hm (ha.trans hx.1) (ha.trans hy.1) hxy)

theorem integral_test_local_integrability :
    Specs.SingleVariableAnalysis.Ch10.IntegralTest.localIntegrability := by
  intro f _ hm a b ha hab
  exact decreasing_local_integrable f hm ha hab

/-- The integral on a unit interval is between its endpoint values. -/
theorem decreasing_unit_bounds (f : ℝ → ℝ) (hm : AntitoneOn f (Set.Ici 1))
    {a : ℝ} (ha : 1 ≤ a) (hi : RealIntegrable f a (a+1)) :
    f (a+1) ≤ realIntegral f hi ∧ realIntegral f hi ≤ f a := by
  constructor
  · obtain ⟨P⟩ := partition_exists hi.ordered
    apply le_trans _ (realIntegral_bounds f hi P).1
    have hl (i : Fin P.n) : f (a+1) ≤ cellInfimum f P hi.bounded i := by
      apply (cell_bounds f P hi.bounded i).1.2
      rintro _ ⟨x, hx, rfl⟩
      have hx' := cell_subset_interval P i hx
      exact hm (ha.trans hx'.1) (show 1 ≤ a + 1 by linarith) hx'.2
    calc
      f (a+1) = ∑ i : Fin P.n, f (a+1) * cellLength P i := by
        rw [← Finset.mul_sum, sum_cellLength]; ring
      _ ≤ lowerSum f P hi.bounded := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hl i) (cell_positive P i).le
  · simpa using realIntegral_le_mul_bound hi (fun x hx => hm ha (ha.trans hx.1) hx.1)

/-- Proper integral up to the m-th integer cut, including the zero-length cut. -/
noncomputable def decreasingCut (f : ℝ → ℝ) (hm : AntitoneOn f (Set.Ici 1))
    (a : ℝ) (ha : 1 ≤ a) (m : ℕ) : ℝ :=
  realIntegral f (decreasing_local_integrable f hm ha (le_add_of_nonneg_right (Nat.cast_nonneg m) : a ≤ a + (m : ℝ)))

/-- Summing the two rectangle bounds on consecutive unit intervals. -/
theorem decreasing_cut_bounds (f : ℝ → ℝ) (hm : AntitoneOn f (Set.Ici 1))
    (a : ℝ) (ha : 1 ≤ a) (m : ℕ) :
    (∑ n ∈ Finset.range m, f (a + (n : ℝ) + 1)) ≤ decreasingCut f hm a ha m ∧
      decreasingCut f hm a ha m ≤ ∑ n ∈ Finset.range m, f (a + (n : ℝ)) := by
  induction m with
  | zero => simp [decreasingCut, realIntegral_degenerate]
  | succ m ih =>
    have ham : 1 ≤ a + (m : ℝ) := ha.trans (le_add_of_nonneg_right (Nat.cast_nonneg m))
    let hi := decreasing_local_integrable f hm ham (by linarith : a + (m : ℝ) ≤ a + (m : ℝ) + 1)
    have hu := decreasing_unit_bounds f hm ham hi
    have he : decreasingCut f hm a ha (m+1) =
        decreasingCut f hm a ha m + realIntegral f hi := by
      unfold decreasingCut
      have hcast : a + ((m+1 : ℕ) : ℝ) = a + (m : ℝ) + 1 := by push_cast; ring
      generalize_proofs hbig hsmall
      have hsplit := (real_split f (le_add_of_nonneg_right (Nat.cast_nonneg m) : a ≤ a + (m : ℝ))
        (by push_cast; linarith : a + (m : ℝ) ≤ a + ((m+1 : ℕ) : ℝ)) (RealIntegrable.bounded hbig)).2
      simpa only [hcast] using hsplit hbig hsmall (hcast.symm ▸ hi)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, he]
    exact ⟨add_le_add ih.1 hu.1, add_le_add ih.2 hu.2⟩

/-- Every tail has the regular proper truncations required at infinity. -/
theorem decreasing_right_regular (f : ℝ → ℝ) (hm : AntitoneOn f (Set.Ici 1))
    {a : ℝ} (ha : 1 ≤ a) : RightRegular .real f a ⊤ := by
  refine ⟨WithTop.coe_lt_top a, fun t => ?_⟩
  exact decreasing_local_integrable f hm ha t.property.1.le

/-- Convergence equivalence at any real starting point at least one. -/
theorem decreasing_series_integral_iff (f : ℝ → ℝ)
    (hn : ∀ x, 1 ≤ x → 0 ≤ f x) (hm : AntitoneOn f (Set.Ici 1))
    (a : ℝ) (ha : 1 ≤ a) :
    RealSeriesConverges (fun n => f (a + (n : ℝ))) ↔ RightConverges .real f a ⊤ := by
  let hreg := decreasing_right_regular f hm ha
  have hpos (x : ℝ) (hx : a ≤ x) (_ : (x : WithTop ℝ) < ⊤) : 0 ≤ f x := hn x (ha.trans hx)
  have hseq (n : ℕ) : 0 ≤ f (a + (n : ℝ)) := hn _ (show 1 ≤ a + _ from ha.trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  refine (nonnegative_series_converges_iff _ hseq).trans (Iff.trans ?_
    (right_nonnegative_converges_iff_bounded f a ⊤ hreg hpos).symm)
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨t, rfl⟩
    obtain ⟨m, hm'⟩ := exists_nat_gt (t.val - a)
    let v : RightIndex a ⊤ := ⟨a + ((m+1 : ℕ) : ℝ), by push_cast; linarith,
      WithTop.coe_lt_top _⟩
    have ht : t.val ≤ v.val := by dsimp [v]; push_cast; linarith
    have hmono := right_nonnegative_monotone f a ⊤ hreg hpos t v ht
    have hb := (decreasing_cut_bounds f hm a ha (m+1)).2
    change (show ℝ from RightTruncation .real f a ⊤ hreg t) ≤ C
    exact hmono.trans (hb.trans (hC (Set.mem_range_self m)))
  · rintro ⟨C, hC⟩
    refine ⟨f a + C, ?_⟩
    rintro _ ⟨m, rfl⟩
    let v : RightIndex a ⊤ := ⟨a + ((m+1 : ℕ) : ℝ), by push_cast; linarith,
      WithTop.coe_lt_top _⟩
    have hv : decreasingCut f hm a ha (m+1) ≤ C := hC (Set.mem_range_self v)
    have hb := (decreasing_cut_bounds f hm a ha (m+1)).1
    have hsum : realPartialSum (fun n => f (a + (n : ℝ))) m ≤
        f a + ∑ n ∈ Finset.range (m+1), f (a + (n : ℝ) + 1) := by
      change (∑ n ∈ Finset.range (m+1), f (a + (n : ℝ))) ≤ _
      rw [Finset.sum_range_succ' (fun n => f (a + (n : ℝ))) m,
        Finset.sum_range_succ (fun n => f (a + (n : ℝ) + 1)) m]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, add_assoc]
      linarith [hn (a + ((m : ℝ) + 1)) (by linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m])]
    exact hsum.trans (by linarith)

/-- Integral cuts tend to the same finite improper value. -/
theorem decreasing_cut_limit (f : ℝ → ℝ) (hm : AntitoneOn f (Set.Ici 1))
    (a : ℝ) (ha : 1 ≤ a) (L : ℝ) (hL : RightHasIntegral .real f a ⊤ L) :
    Tendsto (fun m => decreasingCut f hm a ha (m+1)) atTop (𝓝 L) := by
  apply (realSequenceConverges_iff _ _).mp
  intro ε hε
  obtain ⟨hreg, hlim⟩ := hL
  obtain ⟨r, hr⟩ := hlim ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (r.val - a)
  refine ⟨M, fun m hm' => ?_⟩
  let t : RightIndex a ⊤ := ⟨a + ((m+1 : ℕ) : ℝ), by push_cast; linarith,
    WithTop.coe_lt_top _⟩
  have hrt : r.val < t.val := by
    have hMm : (M : ℝ) ≤ m := Nat.cast_le.mpr hm'
    dsimp [t]; push_cast; linarith
  have he := hr t hrt
  change dist (decreasingCut f hm a ha (m+1)) L < ε at he
  simpa only [Real.dist_eq] using he

/-- The source integral test, with ordinary sums starting at n=1. -/
theorem integral_test : Specs.SingleVariableAnalysis.Ch10.IntegralTest.integralTest := by
  intro f hn hm
  change RealSeriesConverges (fun n => f ((n : ℝ) + 1)) ↔ RightConverges .real f 1 ⊤
  simpa only [add_comm (1 : ℝ)] using decreasing_series_integral_iff f hn hm 1 le_rfl

/-- All shifted nonnegative series converge when the original one does. -/
theorem decreasing_series_tail_converges (f : ℝ → ℝ)
    (hn : ∀ x, 1 ≤ x → 0 ≤ f x) (hm : AntitoneOn f (Set.Ici 1))
    (hs : RealSeriesConverges (fun n => f ((n : ℝ) + 1)))
    (a : ℝ) (ha : 1 ≤ a) : RealSeriesConverges (fun n => f (a + (n : ℝ))) := by
  have hp (n : ℕ) : 0 ≤ f (a + (n : ℝ)) :=
    hn _ (ha.trans (le_add_of_nonneg_right (Nat.cast_nonneg n)))
  have hp1 (n : ℕ) : 0 ≤ f ((n : ℝ) + 1) :=
    hn _ (le_add_of_nonneg_left (Nat.cast_nonneg n))
  apply (nonnegative_series_converges_iff (fun n => f (a + (n : ℝ))) hp).mpr
  obtain ⟨C, hC⟩ := (nonnegative_series_converges_iff _ hp1).mp hs
  refine ⟨C, ?_⟩
  rintro _ ⟨m, rfl⟩
  apply le_trans _ (hC (Set.mem_range_self m))
  apply Finset.sum_le_sum
  intro n _
  exact hm (show 1 ≤ (n : ℝ) + 1 from le_add_of_nonneg_left (Nat.cast_nonneg n))
    (show 1 ≤ a + (n : ℝ) from ha.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))) (by linarith)

/-- Both source remainder bounds, with existence of each ordinary tail sum
and each improper tail integral included in the conclusion. -/
theorem integral_test_remainder_bounds :
    Specs.SingleVariableAnalysis.Ch10.IntegralTest.remainderBounds := by
  intro f hn hm hs N hN
  have ha : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hsN := decreasing_series_tail_converges f hn hm hs (N : ℝ) ha
  have hsN1 := decreasing_series_tail_converges f hn hm hs ((N : ℝ) + 1) ha1
  obtain ⟨R, hR⟩ := hsN1
  have hI := (decreasing_series_integral_iff f hn hm (N : ℝ) ha).mp hsN
  have hI1 := (decreasing_series_integral_iff f hn hm ((N : ℝ) + 1) ha1).mp ⟨R, hR⟩
  refine ⟨R, hR, hI, hI1, ?_, ?_⟩
  · apply le_of_tendsto_of_tendsto' (decreasing_cut_limit f hm _ ha1 _
      (right_integral_hasValue .real f _ ⊤ hI1)) ((realSequenceConverges_iff _ _).mp hR)
    intro m
    exact (decreasing_cut_bounds f hm ((N : ℝ) + 1) ha1 (m+1)).2
  · apply le_of_tendsto_of_tendsto' ((realSequenceConverges_iff _ _).mp hR)
      (decreasing_cut_limit f hm _ ha _ (right_integral_hasValue .real f _ ⊤ hI))
    intro m
    have hb := (decreasing_cut_bounds f hm (N : ℝ) ha (m+1)).1
    convert hb using 1; congr 1
    funext n
    congr 1
    ring

end SingleVariableAnalysis.Riemann.Improper

