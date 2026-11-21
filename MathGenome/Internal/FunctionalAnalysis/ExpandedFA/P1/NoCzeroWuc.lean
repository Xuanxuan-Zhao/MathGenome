import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.NoCzeroWuc
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BasicSelection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15UnconditionalCriteria

open Filter Topology
open scoped BigOperators ENNReal
noncomputable section
universe u v
namespace ExpandedFA.P1.NoCzeroWuc
open Spec C01SequenceSpaces ExpandedFA.FunctionSpaces.SequenceDuals
open EquivalentBases.Spec

variable {𝕜 : Type u} [RCLike 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Banach–Steinhaus on the complete dual bounds all finite multipliers. -/
theorem wuc_finite_multiplier_bound {x : ℕ → E}
    (hx : WeaklyUnconditionallyCauchy (𝕜 := 𝕜) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℕ) (a : ℕ → 𝕜),
      (∀ n ∈ s, ‖a n‖ ≤ 1) → ‖∑ n ∈ s, a n • x n‖ ≤ C := by
  classical
  let I := {p : Finset ℕ × (ℕ → 𝕜) // ∀ n ∈ p.1, ‖p.2 n‖ ≤ 1}
  obtain ⟨C, hC, hb⟩ := C12BoundedSequences.norm_bound_of_scalar_bounds 𝕜 E I
    (fun p => ∑ n ∈ p.val.1, p.val.2 n • x n) (by
      intro f
      refine ⟨∑' n, ‖f (x n)‖, fun p => ?_⟩
      simp only [map_sum, map_smul]
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum fun n hn => ?_).trans
        ((hx f).sum_le_tsum _ (fun n _ => norm_nonneg _))
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) (p.property n hn))
  exact ⟨C, hC, fun s a ha => hb ⟨(s, a), ha⟩⟩

theorem c0_coordinate_norm (n : ℕ) : ‖c0Coordinate 𝕜 n‖ = 1 := by
  change ‖lp.single (E := fun _ : ℕ => 𝕜) ∞ n (1 : 𝕜)‖ = 1
  simp

/-- The canonical coordinate series in c₀ is scalarwise absolutely summable. -/
theorem c0_coordinate_wuc :
    WeaklyUnconditionallyCauchy (𝕜 := 𝕜) (c0Coordinate 𝕜) := by
  intro f
  exact summable_of_sum_le (fun n => norm_nonneg (f (c0Coordinate 𝕜 n)))
    (c0_dual_finite_coefficient_bound f)

/-- Transport of the classical c₀ counterexample into any isomorphic subspace. -/
theorem containsC0_counterexample (h : ContainsC0 𝕜 E) :
    ∃ x : ℕ → E, WeaklyUnconditionallyCauchy (𝕜 := 𝕜) x ∧
      ¬C15Unconditional.Spec.UnconditionallyConvergentValue x := by
  obtain ⟨S, ⟨U⟩⟩ := h
  let T : SequenceC0 𝕜 →L[𝕜] E := S.subtypeL.comp U.toContinuousLinearMap
  refine ⟨fun n => T (c0Coordinate 𝕜 n), ?_, ?_⟩
  · intro f
    exact c0_coordinate_wuc (f.comp T)
  · intro hu
    have hn : Tendsto (fun n => T (c0Coordinate 𝕜 n)) atTop (𝓝 0) :=
      ((C15Unconditional.unconditionallyConvergent_iff_summable _).mp hu).tendsto_atTop_zero
    have hbound (n : ℕ) :
        1 ≤ ‖U.symm.toContinuousLinearMap‖ * ‖T (c0Coordinate 𝕜 n)‖ := by
      change 1 ≤ ‖U.symm.toContinuousLinearMap‖ * ‖U (c0Coordinate 𝕜 n)‖
      have hb := U.symm.toContinuousLinearMap.le_opNorm (U (c0Coordinate 𝕜 n))
      simpa only [ContinuousLinearEquiv.coe_coe, U.symm_apply_apply,
        c0_coordinate_norm] using hb
    have hz := hn.norm.const_mul ‖U.symm.toContinuousLinearMap‖
    have hf : (1 : ℝ) ≤ 0 := by
      simpa using ge_of_tendsto hz (Eventually.of_forall hbound)
    norm_num at hf

/-- Uniform limits of scalar null sequences are null sequences. -/
theorem c0_isClosed : IsClosed (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜)) := by
  apply IsSeqClosed.isClosed
  intro z y hz hy
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hy (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hz k) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  calc
    ‖y n‖ ≤ ‖y n - z k n‖ + ‖z k n‖ := by simpa only [sub_add_cancel] using norm_add_le (y n - z k n) (z k n)
    _ ≤ ‖y - z k‖ + ‖z k n‖ := by
      gcongr
      exact lp.norm_apply_le_norm (by simp) (y - z k) n
    _ < ε := by
      have h₁ : ‖y - z k‖ < ε / 2 := by
        simpa only [dist_eq_norm, norm_sub_rev] using hk k le_rfl
      have h₂ : ‖z k n‖ < ε / 2 := by simpa using hN n hn
      linarith

instance c0_completeSpace : CompleteSpace (SequenceC0 𝕜) := c0_isClosed.completeSpace_coe

theorem c0_linearCombination_apply (a : ℕ →₀ 𝕜) (n : ℕ) :
    (Finsupp.linearCombination 𝕜 (c0Coordinate 𝕜) a).val n = a n := by
  classical
  change (∑ i ∈ a.support, a i • c0Coordinate 𝕜 i : SequenceC0 𝕜).val n = a n
  simp only [Submodule.coe_sum, Submodule.coe_smul, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    c0Coordinate_apply, mul_ite, mul_one, mul_zero]
  simp_rw [eq_comm (a := n)]
  by_cases hn : n ∈ a.support <;> simp_all


/-- The coordinate vectors span a norm-dense subspace of the actual c₀. -/
theorem c0_closedSpan : closedSpan (𝕜 := 𝕜) (c0Coordinate 𝕜) = ⊤ := by
  apply top_unique
  intro x _
  apply (Submodule.isClosed_topologicalClosure
    (Submodule.span 𝕜 (Set.range (c0Coordinate 𝕜)))).mem_of_tendsto
      (c0_truncation_convergence 𝕜 x)
  apply Eventually.of_forall
  intro N
  apply Submodule.sum_mem
  intro n hn
  exact Submodule.smul_mem _ _ (spanVector (𝕜 := 𝕜) (c0Coordinate 𝕜) n).property

/-- Scalar absolute summability is preserved under disjoint finite blocking. -/
theorem wuc_disjoint_blocks {x : ℕ → E}
    (hx : WeaklyUnconditionallyCauchy (𝕜 := 𝕜) x) (F : ℕ → Finset ℕ)
    (hF : Pairwise (fun m n => Disjoint (F m) (F n))) :
    WeaklyUnconditionallyCauchy (𝕜 := 𝕜) (fun k => ∑ n ∈ F k, x n) := by
  classical
  intro f
  apply summable_of_sum_le (fun k => norm_nonneg _) (c := ∑' n, ‖f (x n)‖)
  intro s
  calc
    ∑ k ∈ s, ‖f (∑ n ∈ F k, x n)‖ ≤ ∑ k ∈ s, ∑ n ∈ F k, ‖f (x n)‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [map_sum]
      exact norm_sum_le _ _
    _ = ∑ n ∈ s.biUnion F, ‖f (x n)‖ := by
      symm
      exact Finset.sum_biUnion (fun m hm n hn hmn => hF hmn)
    _ ≤ ∑' n, ‖f (x n)‖ := (hx f).sum_le_tsum _ (fun n _ => norm_nonneg _)

/-- The unconditional Cauchy criterion produces disjoint nonvanishing blocks.
Successiveness is unnecessary: disjointness suffices for scalar summability. -/
theorem exists_nonvanishing_blocks [CompleteSpace E] {x : ℕ → E}
    (hx : ¬C15Unconditional.Spec.UnconditionallyConvergentValue x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F : ℕ → Finset ℕ,
      Pairwise (fun m n => Disjoint (F m) (F n)) ∧
      ∀ k, ε ≤ ‖∑ n ∈ F k, x n‖ := by
  classical
  have hns : ¬Summable x := fun hs => hx
    ((C15Unconditional.unconditionallyConvergent_iff_summable x).mpr hs)
  rw [summable_iff_vanishing_norm] at hns
  push Not at hns
  obtain ⟨ε, hε, hbad⟩ := hns
  have hstep (t : Set (Finset ℕ)) (ht : t.Finite) :
      ∃ F : Finset ℕ, ε ≤ ‖∑ n ∈ F, x n‖ ∧ ∀ G ∈ t, Disjoint F G := by
    obtain ⟨F, hF, hn⟩ := hbad (ht.toFinset.biUnion id)
    refine ⟨F, hn, fun G hG => hF.mono_right ?_⟩
    exact Finset.subset_biUnion_of_mem id (ht.mem_toFinset.mpr hG)
  obtain ⟨F, hF⟩ := Set.seq_of_forall_finite_exists hstep
  refine ⟨ε, hε, F, ?_, fun k => (hF k).1⟩
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact ((hF n).2 (F m) ⟨m, h, rfl⟩).symm
  · exact (hF m).2 (F n) ⟨n, h, rfl⟩

/-- Weak nullity uses the topology generated by the original scalar-linear dual. -/
theorem wuc_weakly_null {x : ℕ → E}
    (hx : WeaklyUnconditionallyCauchy (𝕜 := 𝕜) x) :
    Tendsto x atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) 0) := by
  rw [dualPairTopology_evaluation 𝕜 E, nhds_iInf]
  apply tendsto_iInf.mpr
  intro f
  rw [nhds_induced, tendsto_comap_iff]
  simpa only [Function.comp_def, map_zero] using
    (tendsto_zero_iff_norm_tendsto_zero.mpr (hx f).tendsto_atTop_zero)

/-- A common multiplier bound scales by the supremum norm of the coefficients. -/
theorem finite_multiplier_bound_scaled (y : ℕ → E) {C : ℝ}
    (hC : ∀ (s : Finset ℕ) (a : ℕ → 𝕜),
      (∀ n ∈ s, ‖a n‖ ≤ 1) → ‖∑ n ∈ s, a n • y n‖ ≤ C)
    (a : ℕ →₀ 𝕜) :
    ‖Finsupp.linearCombination 𝕜 y a‖ ≤
      C * ‖Finsupp.linearCombination 𝕜 (c0Coordinate 𝕜) a‖ := by
  classical
  let z := Finsupp.linearCombination 𝕜 (c0Coordinate 𝕜) a
  have ha (n : ℕ) : ‖a n‖ ≤ ‖z‖ := by
    change ‖a n‖ ≤ ‖z.val‖
    rw [← c0_linearCombination_apply a n]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero z.val n
  by_cases hz : ‖z‖ = 0
  · have ha0 : a = 0 := by
      ext n
      exact norm_eq_zero.mp (le_antisymm (by simpa only [hz] using ha n) (norm_nonneg _))
    simp [ha0]
  · have hzp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hzk : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast hz
    let b : ℕ → 𝕜 := fun n => (‖z‖ : 𝕜)⁻¹ * a n
    have hb (n : ℕ) : ‖b n‖ ≤ 1 := by
      simp only [b, norm_mul, norm_inv, RCLike.norm_coe_norm]
      exact (inv_mul_le_iff₀ hzp).mpr (by simpa using ha n)
    have hbound := hC a.support b (fun n _ => hb n)
    have heq : (‖z‖ : 𝕜) • (∑ n ∈ a.support, b n • y n) =
        Finsupp.linearCombination 𝕜 y a := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum,
        smul_smul, b, ← mul_assoc, mul_inv_cancel₀ hzk, one_mul]
    rw [← heq, norm_smul, RCLike.norm_coe_norm]
    exact (mul_le_mul_of_nonneg_left hbound (norm_nonneg z)).trans_eq (mul_comm _ _)

/-- A seminormalized basic w.u.C. sequence has closed span isomorphic to c₀. -/
theorem basic_wuc_containsC0 [CompleteSpace E] {y : ℕ → E}
    (hy : IsBasicSequence (𝕜 := 𝕜) y)
    (hw : WeaklyUnconditionallyCauchy (𝕜 := 𝕜) y)
    {ε : ℝ} (hε : 0 < ε) (hlo : ∀ n, ε ≤ ‖y n‖) : ContainsC0 𝕜 E := by
  classical
  obtain ⟨T, H, _, _⟩ := C15PartialSums.raw_partial_sum_bounds hy
  obtain ⟨hK, f, hf, hfnorm⟩ := EquivalentBases.extended_coordinates hy T H.agrees
  let D : ℝ := 2 * C15PartialSums.Spec.basisConstant T / ε + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hfD (n : ℕ) : ‖f n‖ ≤ D := by
    apply (hfnorm n).trans
    have hh := div_le_div_of_nonneg_left (by positivity :
      0 ≤ 2 * C15PartialSums.Spec.basisConstant T) hε (hlo n)
    dsimp [D]
    linarith
  obtain ⟨C, hC, hb⟩ := wuc_finite_multiplier_bound hw
  have hfinite : FiniteSumBounds (𝕜 := 𝕜) (c0Coordinate 𝕜) y := by
    refine ⟨D⁻¹, max C D⁻¹, inv_pos.mpr hD, le_max_right _ _, fun a => ⟨?_, ?_⟩⟩
    · apply (inv_mul_le_iff₀ hD).mpr
      change ‖(Finsupp.linearCombination 𝕜 (c0Coordinate 𝕜) a).val‖ ≤ _
      apply lp.norm_le_of_forall_le (mul_nonneg hD.le (norm_nonneg _))
      intro n
      rw [c0_linearCombination_apply]
      have heq : f n (Finsupp.linearCombination 𝕜 y a) = a n := by
        simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
          hf, Pi.single_apply, smul_eq_mul, mul_ite, eq_comm]
      rw [← heq]
      exact ((f n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hfD n) (norm_nonneg _))
    · exact (finite_multiplier_bound_scaled y hb a).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨U, _⟩ := (EquivalentBases.equivalentFamilies_iff (c0Coordinate 𝕜) y).mpr hfinite
  let V : closedSpan (𝕜 := 𝕜) (c0Coordinate 𝕜) ≃L[𝕜] SequenceC0 𝕜 :=
    (ContinuousLinearEquiv.ofEq _ _ (c0_closedSpan (𝕜 := 𝕜))).trans
      (Submodule.topContEquiv (R := 𝕜) (M := SequenceC0 𝕜))
  exact ⟨closedSpan (𝕜 := 𝕜) y, ⟨V.symm.trans U⟩⟩

/-- Nonconvergent w.u.C. series force an isomorphic c₀ subspace. -/
theorem wuc_not_unconditional_containsC0 [CompleteSpace E] {x : ℕ → E}
    (hx : WeaklyUnconditionallyCauchy (𝕜 := 𝕜) x)
    (hn : ¬C15Unconditional.Spec.UnconditionallyConvergentValue x) : ContainsC0 𝕜 E := by
  obtain ⟨ε, hε, F, hF, hlo⟩ := exists_nonvanishing_blocks hn
  let z : ℕ → E := fun k => ∑ n ∈ F k, x n
  have hw : WeaklyUnconditionallyCauchy (𝕜 := 𝕜) z := wuc_disjoint_blocks hx F hF
  have hnz : ¬Tendsto z atTop (𝓝 0) := by
    intro hz
    have hh : ε ≤ 0 := by simpa using ge_of_tendsto hz.norm (Eventually.of_forall hlo)
    exact (not_le_of_gt hε) hh
  obtain ⟨φ, hφ, hb⟩ := BasicSelection.weakly_null_basic_subsequence z
    (wuc_weakly_null hw) hnz
  exact basic_wuc_containsC0 hb
    (fun f => (hw f).comp_injective hφ.injective) hε (fun n => hlo (φ n))

theorem noC0_iff_wuc_unconditional : Spec.NoC0IffWucUnconditional := by
  intro 𝕜 E _ _ _ _
  constructor
  · intro h x hx
    by_contra hn
    exact h (wuc_not_unconditional_containsC0 hx hn)
  · intro h hc
    obtain ⟨x, hw, hn⟩ := containsC0_counterexample hc
    exact hn (h x hw)

end ExpandedFA.P1.NoCzeroWuc
