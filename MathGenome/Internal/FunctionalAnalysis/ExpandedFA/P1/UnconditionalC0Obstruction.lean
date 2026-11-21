import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UnconditionalC0Obstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DualBases
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15SubsetProjections
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EquivalentBases
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Filter Topology
open scoped BigOperators ENNReal ComplexConjugate
noncomputable section
universe u v
namespace ExpandedFA.P1.UnconditionalC0Obstruction
open C01SequenceSpaces C15SubsetProjections.Spec
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

local instance : NormedAddCommGroup (SequenceC0 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (SequenceC0 𝕜) := inferInstance

@[simp] theorem c0Unit_apply (n i : ℕ) :
    (c0Unit 𝕜 n).val i = if i = n then 1 else 0 := by
  simp [c0Unit, lp.single_apply, Pi.single_apply, eq_comm]

@[simp] theorem norm_c0Unit (n : ℕ) : ‖c0Unit 𝕜 n‖ = 1 := by
  change ‖lp.single (E := fun _ : ℕ => 𝕜) ∞ n (1 : 𝕜)‖ = 1
  simp [lp.norm_single]

/-- Unit vectors with scalar coefficients of modulus at most one have every
finite synthesis in the closed unit ball of the actual c₀ space. -/
theorem norm_sum_c0Unit_le_one (s : Finset ℕ) (a : ℕ → 𝕜)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) :
    ‖∑ i ∈ s, a i • c0Unit 𝕜 i‖ ≤ 1 := by
  classical
  change ‖(∑ i ∈ s, a i • c0Unit 𝕜 i : SequenceC0 𝕜).val‖ ≤ 1
  apply lp.norm_le_of_forall_le zero_le_one
  intro j
  have he : (∑ i ∈ s, a i • c0Unit 𝕜 i : SequenceC0 𝕜).val j =
      if j ∈ s then a j else 0 := by
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul_of_tower, c0Unit, ← lp.single_smul, smul_eq_mul,
      mul_one, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]
  rw [he]
  split_ifs with hj
  · exact ha j hj
  · simp

/-- The phase chosen here works over both ℝ and ℂ, including zero values. -/
private theorem phase_mul (z : 𝕜) :
    (starRingEnd 𝕜 z / (‖z‖ : 𝕜)) * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [div_mul_eq_mul_div, RCLike.conj_mul]
    have hn : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    simp [pow_two, hn]

private theorem norm_phase_le_one (z : 𝕜) :
    ‖starRingEnd 𝕜 z / (‖z‖ : 𝕜)‖ ≤ 1 := by
  rw [norm_div, RCLike.norm_conj, RCLike.norm_of_nonneg (norm_nonneg z)]
  exact div_le_one_of_le₀ le_rfl (norm_nonneg z)

/-- A direct scalar dual estimate: no identification of c₀' with ℓ¹ is assumed. -/
theorem summable_c0Unit_values (f : SequenceC0 𝕜 →L[𝕜] 𝕜) :
    Summable (fun n => ‖f (c0Unit 𝕜 n)‖) := by
  classical
  apply summable_of_sum_le (fun _ => norm_nonneg _) (c := ‖f‖)
  intro s
  let a : ℕ → 𝕜 := fun n => starRingEnd 𝕜 (f (c0Unit 𝕜 n)) / (‖f (c0Unit 𝕜 n)‖ : 𝕜)
  have he : f (∑ i ∈ s, a i • c0Unit 𝕜 i) =
      ((∑ i ∈ s, ‖f (c0Unit 𝕜 i)‖ : ℝ) : 𝕜) := by
    change f.toLinearMap (∑ i ∈ s, a i • c0Unit 𝕜 i) = _
    simp only [map_sum, map_smul, smul_eq_mul, a, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (starRingEnd 𝕜 (f (c0Unit 𝕜 i)) / (‖f (c0Unit 𝕜 i)‖ : 𝕜)) *
      f (c0Unit 𝕜 i) = (‖f (c0Unit 𝕜 i)‖ : 𝕜)
    exact phase_mul _
  have hnorm := f.le_opNorm (∑ i ∈ s, a i • c0Unit 𝕜 i)
  rw [he, RCLike.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at hnorm
  exact hnorm.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (norm_sum_c0Unit_le_one s a (fun i _ => norm_phase_le_one _)) (norm_nonneg f))

/-- The canonical unit sequence of c₀ is weakly null over either scalar field. -/
theorem c0Unit_weakly_null (f : SequenceC0 𝕜 →L[𝕜] 𝕜) :
    Tendsto (fun n => f (c0Unit 𝕜 n)) atTop (𝓝 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (summable_c0Unit_values f).tendsto_atTop_zero


/-- Coordinatewise weak nullity makes each fixed initial projection tend to zero. -/
theorem initial_projections_tendsto_zero (b : SchauderBasis 𝕜 E) (x : ℕ → E)
    (hx : ∀ i, Tendsto (fun n => b.coord i (x n)) atTop (𝓝 0)) (N : ℕ) :
    Tendsto (fun n => b.proj N (x n)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range N)
    (fun i _ => (hx i).smul_const (b i))
  simpa only [SchauderBasis.proj_apply, zero_smul, Finset.sum_const_zero] using h

/-- The gliding-hump construction uses only vanishing coordinates, so it also
applies before an embedded c₀ sequence has been shown basic. -/
theorem coordinate_null_block_approximation (b : SchauderBasis 𝕜 E) (x : ℕ → E)
    (hx : ∀ i, Tendsto (fun n => b.coord i (x n)) atTop (𝓝 0))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) :
    ∃ σ p : ℕ → ℕ, StrictMono σ ∧ StrictMono p ∧ p 0 = 0 ∧
      ∀ k, ‖x (σ k) - ∑ i ∈ Finset.Ico (p k) (p (k + 1)),
        b.coord i (x (σ k)) • b i‖ < ε k := by
  classical
  have hstep (k m p : ℕ) : ∃ t : ℕ × ℕ, m < t.1 ∧ p < t.2 ∧
      ‖x t.1 - ∑ i ∈ Finset.Ico p t.2, b.coord i (x t.1) • b i‖ < ε k := by
    have he : 0 < ε k / 2 := half_pos (hε k)
    have hsmall : ∀ᶠ n in atTop, ‖b.proj p (x n)‖ < ε k / 2 :=
      (initial_projections_tendsto_zero b x hx p).norm.eventually
        (gt_mem_nhds (by simpa only [norm_zero] using he))
    obtain ⟨n, hn, hnorm⟩ := ((eventually_gt_atTop m).and hsmall).exists
    have htail : ∀ᶠ q in atTop, ‖b.proj q (x n) - x n‖ < ε k / 2 :=
      ((b.tendsto_proj (x n)).sub_const (x n)).norm.eventually
        (gt_mem_nhds (by simpa only [sub_self, norm_zero] using he))
    obtain ⟨q, hq, hnormq⟩ := ((eventually_gt_atTop p).and htail).exists
    refine ⟨(n, q), hn, hq, ?_⟩
    rw [Finset.sum_Ico_eq_sub _ hq.le]
    simp only [← SchauderBasis.proj_apply]
    have hid : x n - (b.proj q (x n) - b.proj p (x n)) =
        (x n - b.proj q (x n)) + b.proj p (x n) := by abel
    rw [hid]
    have ht : ‖x n - b.proj q (x n)‖ < ε k / 2 := by
      simpa only [sub_self, norm_sub_rev] using hnormq
    have hp : ‖b.proj p (x n)‖ < ε k / 2 := by simpa only [norm_zero] using hnorm
    exact (norm_add_le _ _).trans_lt (by linarith)
  choose step hstep₁ hstep₂ hstep₃ using hstep
  let z : ℕ → ℕ × ℕ := fun k => Nat.rec (0, 0) (fun j t => step j t.1 t.2) k
  have hz (k) : z (k + 1) = step k (z k).1 (z k).2 := rfl
  let σ : ℕ → ℕ := fun k => (z (k + 1)).1
  let p : ℕ → ℕ := fun k => (z k).2
  refine ⟨σ, p, strictMono_nat_of_lt_succ (fun k => ?_),
    strictMono_nat_of_lt_succ (fun k => ?_), rfl, fun k => ?_⟩
  · change (z (k + 1)).1 < (z (k + 1 + 1)).1
    rw [hz (k + 1)]
    exact hstep₁ _ _ _
  · change (z k).2 < (z (k + 1)).2
    rw [hz]
    exact hstep₂ _ _ _
  · change ‖x (z (k + 1)).1 - ∑ i ∈ Finset.Ico (z k).2 (z (k + 1)).2,
        b.coord i (x (z (k + 1)).1) • b i‖ < ε k
    rw [hz]
    exact hstep₃ _ _ _

/-- In particular an actual c₀ unit sequence in the ambient Banach space
admits the source's successive-block approximations, for arbitrarily small
summable error budgets as well as general positive budgets. -/
theorem c0_block_approximation : Spec.C0BlockApproximation := by
  intro 𝕜 E _ _ _ b T ε hε
  exact coordinate_null_block_approximation b (fun n => T (c0Unit 𝕜 n))
    (fun i => c0Unit_weakly_null ((b.coord i).comp T)) ε hε


@[simp] theorem coord_initial_projection (b : SchauderBasis 𝕜 E) (N i : ℕ) (x : E) :
    b.coord i (b.proj N x) = if i < N then b.coord i x else 0 := by
  classical
  simp [SchauderBasis.proj_apply, map_sum, map_smul, b.ortho, Pi.single_apply]

/-- Bounded completeness applies to compatible completed blocks, even though
ambient partial sums can cut a block in its interior. -/
theorem boundedlyComplete_compatible_converges [CompleteSpace E]
    (b : SchauderBasis 𝕜 E)
    (hb : DualBasisBasicity.Spec.IsBoundedlyComplete (𝕜 := 𝕜) b.basis)
    (p : ℕ → ℕ) (hp : StrictMono p) (v : ℕ → E)
    (hv : BddAbove (Set.range fun N => ‖v N‖))
    (hcompat : ∀ n m, n ≤ m → b.proj (p n) (v m) = v n) :
    ∃ x : E, Tendsto v atTop (𝓝 x) := by
  have hcoord (n m i : ℕ) (hnm : n ≤ m) (hi : i < p n) :
      b.coord i (v m) = b.coord i (v n) := by
    have h := congrArg (b.coord i) (hcompat n m hnm)
    simpa only [coord_initial_projection, ite_eq_left hi] using h
  let a : ℕ → 𝕜 := fun i => b.coord i (v (i + 1))
  have ha (n i : ℕ) (hi : i < p n) : a i = b.coord i (v n) := by
    have hi' : i < p (i + 1) := lt_of_lt_of_le (Nat.lt_succ_self i) (hp.id_le _)
    exact (hcoord (i + 1) (max (i + 1) n) i (le_max_left _ _) hi').symm.trans
      (hcoord n (max (i + 1) n) i (le_max_right _ _) hi)
  have hsum (N) : C15Basis.Spec.orderedPartialSum b.basis a N = b.proj N (v N) := by
    simp only [C15Basis.Spec.orderedPartialSum, SchauderBasis.proj_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ha N i (lt_of_lt_of_le (Finset.mem_range.mp hi) (hp.id_le N))]
  obtain ⟨K, hK⟩ := b.exists_norm_proj_le
  have hK0 : 0 ≤ K := by simpa using hK 0
  obtain ⟨B, hB⟩ := hv
  have hbound : BddAbove (Set.range fun N => ‖C15Basis.Spec.orderedPartialSum b.basis a N‖) := by
    refine ⟨K * B, ?_⟩
    rintro _ ⟨N, rfl⟩
    change ‖C15Basis.Spec.orderedPartialSum b.basis a N‖ ≤ K * B
    rw [hsum]
    exact ((b.proj N).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hK N) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hB (Set.mem_range_self N)) hK0))
  obtain ⟨x, hx⟩ := hb a hbound
  have hax (i) : b.coord i x = a i := by
    have ht := ((b.coord i).continuous.tendsto x).comp hx
    have hc : Tendsto (fun N => b.coord i (C15Basis.Spec.orderedPartialSum b.basis a N))
        atTop (𝓝 (a i)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop i] with N hN
      simp [C15Basis.Spec.orderedPartialSum, map_sum, map_smul, b.ortho,
        Pi.single_apply, hN]
    exact tendsto_nhds_unique ht hc
  have heq (N) : b.proj (p N) x = v N := by
    rw [← hcompat N N le_rfl]
    simp only [SchauderBasis.proj_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hax, ha N i (Finset.mem_range.mp hi)]
  refine ⟨x, ?_⟩
  simpa only [Function.comp_def, heq] using (b.tendsto_proj x).comp hp.tendsto_atTop

/-- A finite basis, including the empty one, cannot contain an isomorphic c₀. -/
theorem finite_basis_no_c0 {d : ℕ} (b : UnconditionalSchauderBasis (Fin d) 𝕜 E) :
    ¬ Spec.ContainsC0 𝕜 E := by
  rintro ⟨S, _, ⟨U⟩⟩
  let T : SequenceC0 𝕜 →L[𝕜] E := S.subtypeL.comp U.toContinuousLinearMap
  have hexp (x : E) : (∑ i, b.coord i x • b i) = x :=
    (hasSum_fintype _).unique (b.expansion x)
  have ht : Tendsto (fun n => T (c0Unit 𝕜 n)) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.univ : Finset (Fin d))
      (fun i _ => (c0Unit_weakly_null ((b.coord i).comp T)).smul_const (b i))
    simpa only [ContinuousLinearMap.comp_apply, hexp, zero_smul, Finset.sum_const_zero] using hh
  have hn (n) : (1 : ℝ) ≤ ‖U.symm.toContinuousLinearMap‖ * ‖T (c0Unit 𝕜 n)‖ := by
    change 1 ≤ ‖U.symm.toContinuousLinearMap‖ * ‖U (c0Unit 𝕜 n)‖
    have h := U.symm.toContinuousLinearMap.le_opNorm (U (c0Unit 𝕜 n))
    simpa only [ContinuousLinearEquiv.coe_coe, U.symm_apply_apply, norm_c0Unit] using h
  have hlim : Tendsto (fun n => ‖U.symm.toContinuousLinearMap‖ * ‖T (c0Unit 𝕜 n)‖)
      atTop (𝓝 0) := by simpa using ht.norm.const_mul ‖U.symm.toContinuousLinearMap‖
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hn)
  norm_num at hbad

theorem finite_boundedCompleteness_criterion : Spec.FiniteBoundedCompletenessCriterion := by
  intro 𝕜 E _ _ _ _ d e he
  obtain ⟨b, hb, _, _⟩ := C15CoordinateContinuity.finite_native_basis he
  have hn : ¬ Spec.ContainsC0 𝕜 E := finite_basis_no_c0 b
  have hc : DualBases.Spec.finiteBoundedlyComplete (𝕜 := 𝕜) e :=
    DualBases.finite_boundedly_complete e
  exact ⟨fun _ => hn, fun _ => hc⟩


/-- Finite sums along any subsequence of the c₀ unit vectors remain bounded. -/
theorem norm_sum_c0Unit_subsequence_le_one (σ : ℕ → ℕ) (hσ : Function.Injective σ)
    (s : Finset ℕ) : ‖∑ i ∈ s, c0Unit 𝕜 (σ i)‖ ≤ 1 := by
  classical
  have hh := norm_sum_c0Unit_le_one (𝕜 := 𝕜) (s.image σ) (fun _ => 1)
    (by intros; simp)
  simpa only [one_smul, Finset.sum_image hσ.injOn] using hh

set_option maxHeartbeats 800000 in
/-- Every boundedly complete Schauder basis excludes c₀, without an additional
unconditionality hypothesis. The coefficients cut inside blocks are controlled
by `boundedlyComplete_compatible_converges`. -/
theorem boundedlyComplete_no_c0 [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (hb : DualBasisBasicity.Spec.IsBoundedlyComplete (𝕜 := 𝕜) b.basis) :
    ¬ Spec.ContainsC0 𝕜 E := by
  classical
  rintro ⟨S, _, ⟨U⟩⟩
  let T : SequenceC0 𝕜 →L[𝕜] E := S.subtypeL.comp U.toContinuousLinearMap
  let ε : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have hε : HasSum ε 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) using 1
    norm_num [ε]
  obtain ⟨σ, p, hσ, hp, _, herr⟩ := c0_block_approximation b T ε
    (fun k => by dsimp [ε]; positivity)
  let x : ℕ → E := fun k => T (c0Unit 𝕜 (σ k))
  let u : ℕ → E := fun k => b.proj (p (k + 1)) (x k) - b.proj (p k) (x k)
  have huerr (k) : ‖u k - x k‖ ≤ ε k := by
    have h := herr k
    rw [Finset.sum_Ico_eq_sub _ (hp.monotone (Nat.le_succ k))] at h
    simpa only [← SchauderBasis.proj_apply, norm_sub_rev] using h.le
  have he : Tendsto (fun k => u k - x k) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) huerr hε.summable.tendsto_atTop_zero
  let v : ℕ → E := fun N => ∑ k ∈ Finset.range N, u k
  have hvbound : BddAbove (Set.range fun N => ‖v N‖) := by
    refine ⟨‖T‖ + 2, ?_⟩
    rintro _ ⟨N, rfl⟩
    have hxbound : ‖∑ k ∈ Finset.range N, x k‖ ≤ ‖T‖ := by
      have ht := T.le_opNorm (∑ k ∈ Finset.range N, c0Unit 𝕜 (σ k))
      have hsum : T (∑ k ∈ Finset.range N, c0Unit 𝕜 (σ k)) =
          ∑ k ∈ Finset.range N, x k := by
        change T.toLinearMap (∑ k ∈ Finset.range N, c0Unit 𝕜 (σ k)) = _
        simp only [map_sum]; rfl
      rw [hsum] at ht
      exact ht.trans (by
        simpa using mul_le_mul_of_nonneg_left
          (norm_sum_c0Unit_subsequence_le_one (𝕜 := 𝕜) σ hσ.injective _) (norm_nonneg T))
    have hebound : ‖∑ k ∈ Finset.range N, (u k - x k)‖ ≤ 2 := by
      calc
        _ ≤ ∑ k ∈ Finset.range N, ‖u k - x k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range N, ε k := Finset.sum_le_sum (fun k _ => huerr k)
        _ ≤ ∑' k, ε k := hε.summable.sum_le_tsum _ (fun k _ => by dsimp [ε]; positivity)
        _ = 2 := hε.tsum_eq
    have hvsum : v N = (∑ k ∈ Finset.range N, (u k - x k)) +
        ∑ k ∈ Finset.range N, x k := by simp [v, Finset.sum_sub_distrib]
    change ‖v N‖ ≤ ‖T‖ + 2
    rw [hvsum]
    exact (norm_add_le _ _).trans (by linarith)
  have hproj (N k) : b.proj (p N) (u k) = if k < N then u k else 0 := by
    dsimp only [u]
    rw [map_sub, SchauderBasis.proj_comp, SchauderBasis.proj_comp]
    split_ifs with hk
    · rw [min_eq_right (hp.monotone (Nat.succ_le_of_lt hk)),
        min_eq_right (hp.monotone hk.le)]
    · rw [min_eq_left (hp.monotone (Nat.le_of_not_gt hk)),
        min_eq_left (hp.monotone ((Nat.le_of_not_gt hk).trans (Nat.le_succ _))), sub_self]
  have hcompat (n m : ℕ) (hnm : n ≤ m) : b.proj (p n) (v m) = v n := by
    dsimp only [v]
    rw [map_sum]
    calc
      _ = ∑ k ∈ Finset.range n, b.proj (p n) (u k) := by
        symm
        apply Finset.sum_subset (Finset.range_mono hnm)
        intro k hkm hkn
        rw [hproj, ite_eq_right (by simpa only [Finset.mem_range] using hkn)]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hproj, ite_eq_left (Finset.mem_range.mp hk)]
  obtain ⟨z, hz⟩ := boundedlyComplete_compatible_converges b hb p hp v hvbound hcompat
  have huv (N) : u N = v (N + 1) - v N := by simp [v, Finset.sum_range_succ]
  have hu : Tendsto u atTop (𝓝 0) := by
    have hh := (hz.comp (tendsto_add_atTop_nat 1)).sub hz
    simpa only [sub_self, Function.comp_def, ← huv] using hh
  have hx : Tendsto x atTop (𝓝 0) := by
    have hh := hu.sub he
    simpa only [sub_self, sub_sub_cancel] using hh
  have hn (k) : (1 : ℝ) ≤ ‖U.symm.toContinuousLinearMap‖ * ‖x k‖ := by
    change 1 ≤ ‖U.symm.toContinuousLinearMap‖ * ‖U (c0Unit 𝕜 (σ k))‖
    have h := U.symm.toContinuousLinearMap.le_opNorm (U (c0Unit 𝕜 (σ k)))
    simpa only [ContinuousLinearEquiv.coe_coe, U.symm_apply_apply, norm_c0Unit] using h
  have hlim : Tendsto (fun k => ‖U.symm.toContinuousLinearMap‖ * ‖x k‖) atTop (𝓝 0) := by
    simpa using hx.norm.const_mul ‖U.symm.toContinuousLinearMap‖
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hn)
  norm_num at hbad


/-- Failure of bounded completeness provides successive coefficient blocks,
uniformly separated from zero, from one bounded sequence of initial sums. -/
theorem failure_boundedCompleteness_blocks [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (hbad : ¬ DualBasisBasicity.Spec.IsBoundedlyComplete (𝕜 := 𝕜) b.basis) :
    ∃ (a : ℕ → 𝕜) (δ : ℝ) (p : ℕ → ℕ), 0 < δ ∧ StrictMono p ∧ p 0 = 0 ∧
      BddAbove (Set.range fun N => ‖C15Basis.Spec.orderedPartialSum b.basis a N‖) ∧
      ∀ k, δ ≤ ‖∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i • b i‖ := by
  classical
  simp only [DualBasisBasicity.Spec.IsBoundedlyComplete] at hbad
  push Not at hbad
  obtain ⟨a, hbound, hnoconv⟩ := hbad
  let s : ℕ → E := C15Basis.Spec.orderedPartialSum b.basis a
  have hnc : ¬ CauchySeq s := by
    intro hc
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
    exact hnoconv x hx
  rw [Metric.cauchySeq_iff'] at hnc
  push Not at hnc
  obtain ⟨δ, hδ, hδbad⟩ := hnc
  have hex (n : ℕ) : ∃ m, n < m ∧ δ ≤ ‖s m - s n‖ := by
    obtain ⟨m, hm, hd⟩ := hδbad n
    have hne : m ≠ n := by
      intro h
      subst m
      simp only [dist_self] at hd
      linarith
    exact ⟨m, lt_of_le_of_ne hm (Ne.symm hne), by simpa only [dist_eq_norm] using hd⟩
  choose next hnext hnorm using hex
  let p : ℕ → ℕ := fun k => Nat.rec 0 (fun _ n => next n) k
  have hp (k) : p (k + 1) = next (p k) := rfl
  refine ⟨a, δ, p, hδ, strictMono_nat_of_lt_succ (fun k => ?_), rfl, hbound, fun k => ?_⟩
  · rw [hp]
    exact hnext _
  · rw [Finset.sum_Ico_eq_sub _ (hnext (p k)).le]
    change δ ≤ ‖s (p (k + 1)) - s (p k)‖
    rw [hp]
    exact hnorm _


/-- A point with coefficients in [0,1] is a convex combination of subset sums.
The translated form makes the elementary induction independent of ordering. -/
theorem norm_affine_sum_le_of_subset_bounds [NormedSpace ℝ E]
    (s : Finset ℕ) (v : ℕ → E) (a : ℕ → ℝ) (z : E) (B : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1)
    (hB : ∀ t ⊆ s, ‖z + ∑ i ∈ t, v i‖ ≤ B) :
    ‖z + ∑ i ∈ s, a i • v i‖ ≤ B := by
  classical
  induction s using Finset.induction_on generalizing z with
  | empty => simpa using hB ∅ (by simp)
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self i s)
    have has : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have h₀ : ‖z + ∑ j ∈ s, a j • v j‖ ≤ B :=
      ih z has (fun t ht => hB t (ht.trans (Finset.subset_insert i s)))
    have h₁ : ‖(z + v i) + ∑ j ∈ s, a j • v j‖ ≤ B := by
      apply ih (z + v i) has
      intro t ht
      have hit : i ∉ t := fun h => hi (ht h)
      simpa only [Finset.sum_insert hit, add_assoc] using
        hB (insert i t) (Finset.insert_subset_insert i ht)
    rw [Finset.sum_insert hi]
    have heq : z + (a i • v i + ∑ j ∈ s, a j • v j) =
        a i • ((z + v i) + ∑ j ∈ s, a j • v j) +
        (1 - a i) • (z + ∑ j ∈ s, a j • v j) := by
      simp only [sub_smul, one_smul, smul_add]
      abel
    rw [heq]
    calc
      _ ≤ ‖a i • ((z + v i) + ∑ j ∈ s, a j • v j)‖ +
          ‖(1 - a i) • (z + ∑ j ∈ s, a j • v j)‖ := norm_add_le _ _
      _ = a i * ‖(z + v i) + ∑ j ∈ s, a j • v j‖ +
          (1 - a i) * ‖z + ∑ j ∈ s, a j • v j‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hai.1, abs_of_nonneg (sub_nonneg.mpr hai.2)]
      _ ≤ a i * B + (1 - a i) * B := add_le_add
        (mul_le_mul_of_nonneg_left h₁ hai.1)
        (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hai.2))
      _ = B := by ring

/-- Signed real multipliers cost at most two times the bound on subset sums. -/
theorem norm_real_sum_le_of_subset_bounds [NormedSpace ℝ E]
    (s : Finset ℕ) (v : ℕ → E) (a : ℕ → ℝ) (B : ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1)
    (hB : ∀ t ⊆ s, ‖∑ i ∈ t, v i‖ ≤ B) :
    ‖∑ i ∈ s, a i • v i‖ ≤ 2 * B := by
  classical
  let apos : ℕ → ℝ := fun i => max (a i) 0
  let aneg : ℕ → ℝ := fun i => max (-a i) 0
  have hpos : ∀ i ∈ s, 0 ≤ apos i ∧ apos i ≤ 1 := by
    intro i hi
    exact ⟨le_max_right _ _, max_le (le_trans (le_abs_self _) (ha i hi)) zero_le_one⟩
  have hneg : ∀ i ∈ s, 0 ≤ aneg i ∧ aneg i ≤ 1 := by
    intro i hi
    exact ⟨le_max_right _ _, max_le (le_trans (neg_le_abs _) (ha i hi)) zero_le_one⟩
  have hp := norm_affine_sum_le_of_subset_bounds s v apos 0 B hpos
    (by simpa only [zero_add] using hB)
  have hn := norm_affine_sum_le_of_subset_bounds s v aneg 0 B hneg
    (by simpa only [zero_add] using hB)
  simp only [zero_add] at hp hn
  have heq : (∑ i ∈ s, a i • v i) =
      (∑ i ∈ s, apos i • v i) - ∑ i ∈ s, aneg i • v i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_smul]
    congr 1
    dsimp only [apos, aneg]
    rcases le_total 0 (a i) with hi | hi
    · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), sub_zero]
    · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), zero_sub, neg_neg]
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)

/-- A uniform bound on all subset sums controls every real or complex unit
multiplier, with one harmless common constant for both scalar fields. -/
theorem norm_sum_le_of_subset_bounds
    (s : Finset ℕ) (v : ℕ → E) (a : ℕ → 𝕜) (B : ℝ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1)
    (hB : ∀ t ⊆ s, ‖∑ i ∈ t, v i‖ ≤ B) :
    ‖∑ i ∈ s, a i • v i‖ ≤ 4 * B := by
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  have hB0 : 0 ≤ B := by simpa using hB ∅ (by simp)
  have hr := norm_real_sum_le_of_subset_bounds s v (fun i => RCLike.re (a i)) B
    (fun i hi => (RCLike.abs_re_le_norm _).trans (ha i hi)) hB
  have hi := norm_real_sum_le_of_subset_bounds s v (fun i => RCLike.im (a i)) B
    (fun i hi => (RCLike.abs_im_le_norm _).trans (ha i hi)) hB
  have heq : (∑ i ∈ s, a i • v i) =
      (∑ i ∈ s, RCLike.re (a i) • v i) +
        (RCLike.I : 𝕜) • ∑ i ∈ s, RCLike.im (a i) • v i := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜),
      smul_smul, ← add_smul, mul_comm, RCLike.re_add_im]
  rw [heq]
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by rw [RCLike.norm_I]; split_ifs <;> norm_num
  calc
    _ ≤ ‖∑ i ∈ s, RCLike.re (a i) • v i‖ +
        ‖(RCLike.I : 𝕜) • ∑ i ∈ s, RCLike.im (a i) • v i‖ := norm_add_le _ _
    _ ≤ 2 * B + 2 * B := add_le_add hr (by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right hI (norm_nonneg _)).trans (by simpa using hi))
    _ = 4 * B := by ring


/-- Uniform limits of null sequences are null, for the upstream supremum norm. -/
theorem sequenceC0_isClosed : IsClosed (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change Tendsto (fun i => x i) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy (ε / 2) (half_pos hε)
  refine ⟨N, fun i hi => ?_⟩
  have happ := lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) i
  have hdiff : ‖x i - y i‖ < ε / 2 := by
    exact happ.trans_lt (by simpa only [dist_eq_norm] using hxy)
  have htail : ‖y i‖ < ε / 2 := by simpa only [dist_zero_right] using hN i hi
  rw [dist_zero_right]
  have hid : x i = (x i - y i) + y i := by abel
  calc
    ‖x i‖ = ‖(x i - y i) + y i‖ := congrArg norm hid
    _ ≤ ‖x i - y i‖ + ‖y i‖ := norm_add_le _ _
    _ < ε := by linarith

instance sequenceC0_complete : CompleteSpace (SequenceC0 𝕜) :=
  sequenceC0_isClosed.completeSpace_coe

@[simp] theorem c0_synthesis_apply (c : ℕ →₀ 𝕜) (i : ℕ) :
    (Finsupp.linearCombination 𝕜 (c0Unit 𝕜) c).val i = c i := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul_of_tower, c0Unit, ← lp.single_smul, smul_eq_mul,
    mul_one, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]
  split_ifs with hi
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hi).symm

theorem c0_coefficient_le_norm_synthesis (c : ℕ →₀ 𝕜) (i : ℕ) :
    ‖c i‖ ≤ ‖Finsupp.linearCombination 𝕜 (c0Unit 𝕜) c‖ := by
  change ‖c i‖ ≤ ‖(Finsupp.linearCombination 𝕜 (c0Unit 𝕜) c).val‖
  simpa only [c0_synthesis_apply] using lp.norm_apply_le_norm ENNReal.top_ne_zero
    (Finsupp.linearCombination 𝕜 (c0Unit 𝕜) c).val i

theorem c0_closedSpan_top : EquivalentBases.Spec.closedSpan (𝕜 := 𝕜) (c0Unit 𝕜) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  have hc : IsClosed (EquivalentBases.Spec.closedSpan (𝕜 := 𝕜) (c0Unit 𝕜) :
      Set (SequenceC0 𝕜)) := Submodule.isClosed_topologicalClosure
        (Submodule.span 𝕜 (Set.range (c0Unit 𝕜)))
  apply hc.mem_of_tendsto (C15SubsetProjections.canonical_c0_unconditional_expansion 𝕜 x)
  apply Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self i)))

/-- A bounded scalar coefficient series has bounded arbitrary finite subsums
whenever the ambient coordinate projections are uniformly bounded. -/
theorem coefficient_subset_bound (b : SchauderBasis 𝕜 E)
    (K B : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ F : Finset ℕ, ‖GeneralSchauderBasis.proj b F‖ ≤ K)
    (a : ℕ → 𝕜)
    (hB : ∀ N, ‖C15Basis.Spec.orderedPartialSum b.basis a N‖ ≤ B) (F : Finset ℕ) :
    ‖∑ i ∈ F, a i • b i‖ ≤ K * B := by
  classical
  let M := F.sup id + 1
  have hM (i) (hi : i ∈ F) : i < M :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have hcoord (i N) : b.coord i (C15Basis.Spec.orderedPartialSum b.basis a N) =
      if i < N then a i else 0 := by
    simp [C15Basis.Spec.orderedPartialSum, map_sum, map_smul, b.ortho, Pi.single_apply]
  have heq : GeneralSchauderBasis.proj b F (C15Basis.Spec.orderedPartialSum b.basis a M) =
      ∑ i ∈ F, a i • b i := by
    simp only [GeneralSchauderBasis.proj_apply, hcoord]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left (hM i hi)]
  rw [← heq]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_right (hK F) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hB M) hK0))

/-- Disjoint successive blocks inherit the bound on all finite subsums. -/
theorem coefficient_block_subset_bound (b : SchauderBasis 𝕜 E)
    (K B : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ F : Finset ℕ, ‖GeneralSchauderBasis.proj b F‖ ≤ K)
    (a : ℕ → 𝕜) (hB : ∀ N, ‖C15Basis.Spec.orderedPartialSum b.basis a N‖ ≤ B)
    (p : ℕ → ℕ) (hp : StrictMono p) (t : Finset ℕ) :
    ‖∑ k ∈ t, ∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i • b i‖ ≤ K * B := by
  classical
  have hd : Set.PairwiseDisjoint (↑t) (fun k => Finset.Ico (p k) (p (k + 1))) := by
    intro k hk l hl hkl
    apply Finset.disjoint_left.mpr
    intro i hki hli
    rcases Finset.mem_Ico.mp hki with ⟨hk₁, hk₂⟩
    rcases Finset.mem_Ico.mp hli with ⟨hl₁, hl₂⟩
    rcases lt_or_gt_of_ne hkl with h | h
    · have hh : p (k + 1) ≤ p l := hp.monotone (by omega)
      omega
    · have hh : p (l + 1) ≤ p k := hp.monotone (by omega)
      omega
  have hh := coefficient_subset_bound b K B hK0 hK a hB
    (t.biUnion (fun k => Finset.Ico (p k) (p (k + 1))))
  rwa [Finset.sum_biUnion hd] at hh

/-- Each initial ambient projection either retains a whole earlier block or
annihilates a later block at the chosen endpoints. -/
theorem initial_projection_coefficient_block (b : SchauderBasis 𝕜 E)
    (a : ℕ → 𝕜) (p : ℕ → ℕ) (hp : StrictMono p) (N k : ℕ) :
    b.proj (p N) (∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i • b i) =
      if k < N then ∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i • b i else 0 := by
  classical
  simp only [map_sum, map_smul, SchauderBasis.proj_apply_basis_mem]
  split_ifs with hk
  · apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left ((Finset.mem_Ico.mp hi).2.trans_le (hp.monotone (Nat.succ_le_of_lt hk)))]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [ite_eq_right (not_lt.mpr ((hp.monotone (Nat.le_of_not_gt hk)).trans (Finset.mem_Ico.mp hi).1)),
      smul_zero]


set_option maxHeartbeats 1200000 in
/-- The upper and lower c₀ estimates for the successive blocks produced by
failure of bounded completeness. The lower bound uses actual ambient projections. -/
theorem coefficient_blocks_c0_bounds (b : SchauderBasis 𝕜 E)
    (K B δ : ℝ) (hK1 : 1 ≤ K) (hδ : 0 < δ)
    (hK : ∀ F : Finset ℕ, ‖GeneralSchauderBasis.proj b F‖ ≤ K)
    (a : ℕ → 𝕜) (hB : ∀ N, ‖C15Basis.Spec.orderedPartialSum b.basis a N‖ ≤ B)
    (p : ℕ → ℕ) (hp : StrictMono p)
    (hblock : ∀ k, δ ≤ ‖∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i • b i‖) :
    EquivalentBases.Spec.FiniteSumBounds (𝕜 := 𝕜) (c0Unit 𝕜)
      (fun k => ∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i • b i) := by
  classical
  let u : ℕ → E := fun k => ∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i • b i
  let L : ℝ := 2 * K / δ
  have hK0 : 0 ≤ K := by linarith
  have hL : 0 < L := by dsimp [L]; positivity
  have hsub (s : Finset ℕ) : ‖∑ k ∈ s, u k‖ ≤ K * B :=
    coefficient_block_subset_bound b K B hK0 hK a hB p hp s
  have hproj (N k) : b.proj (p N) (u k) = if k < N then u k else 0 :=
    initial_projection_coefficient_block b a p hp N k
  refine ⟨L⁻¹, max L⁻¹ (4 * (K * B)), inv_pos.mpr hL, le_max_left _ _, fun c => ?_⟩
  let y : E := Finsupp.linearCombination 𝕜 u c
  let z : SequenceC0 𝕜 := Finsupp.linearCombination 𝕜 (c0Unit 𝕜) c
  have hcoord (l : ℕ) : b.proj (p (l + 1)) y - b.proj (p l) y = c l • u l := by
    dsimp only [y, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
    have heq : ∀ k ∈ c.support,
        b.proj (p (l + 1)) (c k • u k) - b.proj (p l) (c k • u k) =
          if k = l then c k • u k else 0 := by
      intro k _
      simp only [map_smul, hproj]
      by_cases hk : k < l
      · have hk' : k < l + 1 := by omega
        simp [hk, hk', ne_of_lt hk]
      · by_cases hkl : k = l
        · subst k; simp
        · have hk' : ¬ k < l + 1 := by omega
          simp [hk, hk', hkl]
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_ite_eq']
    by_cases hl : l ∈ c.support
    · simp [hl]
    · simp [hl, Finsupp.notMem_support_iff.mp hl]
  have hc (l : ℕ) : ‖c l‖ ≤ L * ‖y‖ := by
    have hh : ‖c l‖ * δ ≤ (2 * K) * ‖y‖ := by
      calc
        ‖c l‖ * δ ≤ ‖c l‖ * ‖u l‖ := mul_le_mul_of_nonneg_left (hblock l) (norm_nonneg _)
        _ = ‖c l • u l‖ := (norm_smul _ _).symm
        _ = ‖b.proj (p (l + 1)) y - b.proj (p l) y‖ := congrArg norm (hcoord l).symm
        _ ≤ ‖b.proj (p (l + 1)) y‖ + ‖b.proj (p l) y‖ := norm_sub_le _ _
        _ ≤ K * ‖y‖ + K * ‖y‖ := add_le_add
          (((b.proj _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
            (hK (Finset.range _)) (norm_nonneg _)))
          (((b.proj _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
            (hK (Finset.range _)) (norm_nonneg _)))
        _ = (2 * K) * ‖y‖ := by ring
    dsimp only [L]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hδ).mpr hh
  have hz : ‖z‖ ≤ L * ‖y‖ := by
    change ‖z.val‖ ≤ L * ‖y‖
    apply lp.norm_le_of_forall_le (mul_nonneg hL.le (norm_nonneg _))
    intro l
    simpa only [z, c0_synthesis_apply] using hc l
  have hlower : L⁻¹ * ‖z‖ ≤ ‖y‖ := (inv_mul_le_iff₀ hL).mpr hz
  refine ⟨hlower, ?_⟩
  have hupp : ‖y‖ ≤ (4 * (K * B)) * ‖z‖ := by
    by_cases hz0 : ‖z‖ = 0
    · have hc0 : c = 0 := by
        ext l
        apply norm_eq_zero.mp
        exact le_antisymm (by simpa only [← hz0] using c0_coefficient_le_norm_synthesis c l)
          (norm_nonneg _)
      simp [y, z, hc0]
    · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
      have hcast : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast hz0
      have hn := norm_sum_le_of_subset_bounds c.support u (fun k => c k / (‖z‖ : 𝕜)) (K * B)
        (fun k _ => by
          rw [norm_div, RCLike.norm_of_nonneg (norm_nonneg _)]
          exact (div_le_one hzpos).mpr (c0_coefficient_le_norm_synthesis c k))
        (fun t _ => hsub t)
      have hy : y = (‖z‖ : 𝕜) • ∑ k ∈ c.support, (c k / (‖z‖ : 𝕜)) • u k := by
        simp only [y, Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_div_cancel₀ _ hcast]
      rw [hy, norm_smul, RCLike.norm_of_nonneg (norm_nonneg _)]
      nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg z)]
  exact hupp.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

set_option maxHeartbeats 1200000 in
/-- The finite inequalities extend to an isomorphism onto the closed block span. -/
theorem containsC0_of_coefficient_blocks [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (K B δ : ℝ) (hK1 : 1 ≤ K) (hδ : 0 < δ)
    (hK : ∀ F : Finset ℕ, ‖GeneralSchauderBasis.proj b F‖ ≤ K)
    (a : ℕ → 𝕜) (hB : ∀ N, ‖C15Basis.Spec.orderedPartialSum b.basis a N‖ ≤ B)
    (p : ℕ → ℕ) (hp : StrictMono p)
    (hblock : ∀ k, δ ≤ ‖∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i • b i‖) :
    Spec.ContainsC0 𝕜 E := by
  let u : ℕ → E := fun k => ∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i • b i
  have hbound := coefficient_blocks_c0_bounds b K B δ hK1 hδ hK a hB p hp hblock
  obtain ⟨U, _⟩ := (EquivalentBases.equivalentFamilies_iff (c0Unit 𝕜) u).mpr hbound
  let V : SequenceC0 𝕜 ≃L[𝕜] EquivalentBases.Spec.closedSpan (𝕜 := 𝕜) (c0Unit 𝕜) :=
    Submodule.topContEquiv.symm.trans
      (ContinuousLinearEquiv.ofEq _ _ c0_closedSpan_top).symm
  exact ⟨EquivalentBases.Spec.closedSpan u, Submodule.isClosed_topologicalClosure _, ⟨V.trans U⟩⟩


/-- Uniform finite-coordinate bounds turn the nonconvergent bounded coefficient
series into an actual closed c₀ subspace. -/
theorem containsC0_of_not_boundedlyComplete [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (hproj : ∃ K : ℝ, ∀ F : Finset ℕ, ‖GeneralSchauderBasis.proj b F‖ ≤ K)
    (hbad : ¬ DualBasisBasicity.Spec.IsBoundedlyComplete (𝕜 := 𝕜) b.basis) :
    Spec.ContainsC0 𝕜 E := by
  obtain ⟨a, δ, p, hδ, hp, _, ⟨B, hB⟩, hblock⟩ := failure_boundedCompleteness_blocks b hbad
  obtain ⟨K, hK⟩ := hproj
  exact containsC0_of_coefficient_blocks b (max 1 K) B δ (le_max_left _ _) hδ
    (fun F => (hK F).trans (le_max_right _ _)) a (fun N => hB (Set.mem_range_self N)) p hp hblock

/-- The manuscript criterion with its original unconditional raw-basis input.
Coordinate continuity and all finite-coordinate bounds are obtained from the
accepted upstream theorems, rather than included as additional hypotheses. -/
theorem boundedCompleteness_criterion : Spec.BoundedCompletenessCriterion := by
  intro 𝕜 E _ _ _ _ e hu
  have hraw := (C15SubsetProjections.rawBasis_iff_uniqueOrderedExpansions e).mpr hu.1
  obtain ⟨b, hb, hc, _⟩ := C15CoordinateContinuity.raw_native_basis hraw
  constructor
  · intro hbc
    exact boundedlyComplete_no_c0 b (by simpa only [hb] using hbc)
  · intro hn
    by_contra hbc
    have hbc' : ¬ DualBasisBasicity.Spec.IsBoundedlyComplete (𝕜 := 𝕜) b.basis := by
      simpa only [hb] using hbc
    let bu : UnconditionalSchauderBasis ℕ 𝕜 E :=
      { basis := b.basis
        coord := b.coord
        ortho := b.ortho
        expansion := by
          intro x
          have hx := (C15Unconditional.isUnconditionalSchauderBasis_iff 𝕜 E e).mp hu |>.2
            x (C15Basis.Spec.rawCoordinates hraw x)
            ((C01Banach.hasSequentialSum_iff E _ x).mpr (C15Basis.rawCoordinates_tendsto hraw x))
          simpa only [hb, hc] using
            (C15Unconditional.hasUnconditionalSum_iff_hasSum _ _).mp hx }
    obtain ⟨K, hK⟩ := bu.exists_norm_proj_le
    have hK' : ∀ F : Finset ℕ, ‖GeneralSchauderBasis.proj b F‖ ≤ K := hK
    exact hn (containsC0_of_not_boundedlyComplete b ⟨K, hK'⟩ hbc')

end ExpandedFA.P1.UnconditionalC0Obstruction
