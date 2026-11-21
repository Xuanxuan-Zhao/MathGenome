import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceShrinking
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceBanachBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DualBasisBasicity
import Mathlib.Algebra.Order.Chebyshev
import Batteries.Tactic.OpenPrivate

noncomputable section
open Filter
open scoped BigOperators Topology
namespace ExpandedFA.P1.JamesShrinking
open private cyclicEnergy_le_norm_sq from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceBanachBasis

/-- Two point evaluations of a disjoint family involve at most two summands. -/
theorem disjoint_edge_square {ι : Type*} [Fintype ι] (a : ι → ℕ → ℝ)
    (hd : ∀ i j, i ≠ j → ∀ k, a i k = 0 ∨ a j k = 0) (x y : ℕ) :
    ((∑ i, a i x) - ∑ i, a i y)^2 ≤ 2 * ∑ i, (a i x - a i y)^2 := by
  classical
  let s := Finset.univ.filter (fun i => a i x - a i y ≠ 0)
  have hcard (z : ℕ) : (Finset.univ.filter (fun i => a i z ≠ 0)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact (hd i j hij z).elim (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hs : s.card ≤ 2 := by
    have hsub : s ⊆ (Finset.univ.filter (fun i => a i x ≠ 0)) ∪
        (Finset.univ.filter (fun i => a i y ≠ 0)) := by
      intro i hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra h
      push Not at h
      exact (Finset.mem_filter.mp hi).2 (by simp [h.1, h.2])
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (by have := hcard x; have := hcard y; omega))
  have he : (∑ i ∈ s, (a i x - a i y)) = ∑ i, (a i x - a i y) := by
    exact Finset.sum_filter_ne_zero _
  have he2 : (∑ i ∈ s, (a i x - a i y)^2) = ∑ i, (a i x - a i y)^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : a i x - a i y = 0 := by simpa [s] using hi
    simp [hz]
  have hh := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => a i x - a i y)
  rw [he, he2, Finset.sum_sub_distrib] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (by positivity))

/-- The edge estimate includes the cyclic closing edge. -/
theorem disjoint_cyclicEnergy {ι : Type*} [Fintype ι] (a : ι → ℕ → ℝ)
    (hd : ∀ i j, i ≠ j → ∀ k, a i k = 0 ∨ a j k = 0)
    (k : ℕ) (p : Fin (k + 2) → ℕ) :
    James.cyclicEnergy (fun z => ∑ i, a i z) k p ≤
      2 * ∑ i, James.cyclicEnergy (a i) k p := by
  have he := Finset.sum_le_sum (s := Finset.univ) fun j (_ : j ∈ (Finset.univ : Finset (Fin (k+1)))) =>
    disjoint_edge_square a hd (p j.castSucc) (p j.succ)
  have hc := disjoint_edge_square a hd (p (Fin.last (k+1))) (p 0)
  unfold James.cyclicEnergy
  calc
    _ ≤ (∑ j : Fin (k+1), 2 * ∑ i, (a i (p j.castSucc) - a i (p j.succ))^2) +
        2 * ∑ i, (a i (p (Fin.last (k+1))) - a i (p 0))^2 := add_le_add he hc
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm, ← mul_add, ← Finset.sum_add_distrib]

section Model

lemma model_val_sum (m : JamesBanachBasisSpec.BanachBasisModel) :
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  ∀ {ι : Type*} (s : Finset ι) (u : ι → JamesBanachBasisSpec.Sequence),
    (∑ i ∈ s, u i).val = fun k => ∑ i ∈ s, (u i).val k := by
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  intro ι s u
  classical
  induction s using Finset.induction_on with
  | empty => simpa using m.zero_eq
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, m.add_eq, ih]

lemma model_energy_bound (m : JamesBanachBasisSpec.BanachBasisModel) :
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  ∀ (a : JamesBanachBasisSpec.Sequence) (k : ℕ)
    (p : Fin (k+2) → ℕ) (hp : StrictMono p),
    James.cyclicEnergy a.val k p ≤ 2 * ‖a‖^2 := by
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  intro a k p hp
  rw [m.norm_eq]
  exact cyclicEnergy_le_norm_sq a k p hp

/-- Uniform upper ℓ² bound for disjoint supports in the actual norm. -/
theorem model_disjoint_bound (m : JamesBanachBasisSpec.BanachBasisModel) :
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  ∀ {ι : Type*} [Fintype ι] (u : ι → JamesBanachBasisSpec.Sequence)
    (hd : ∀ i j, i ≠ j → ∀ k, (u i).val k = 0 ∨ (u j).val k = 0),
    ‖∑ i, u i‖ ^ 2 ≤ 2 * ∑ i, ‖u i‖ ^ 2 := by
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  intro ι _ u hd
  classical
  let C := 2 * ∑ i, ‖u i‖^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hn : ‖∑ i, u i‖ ≤ Real.sqrt C := by
    rw [m.norm_eq]
    apply James.norm_le_of_variation_le _ (Real.sqrt_nonneg _)
    intro k p hp
    have he := (disjoint_cyclicEnergy (fun i => (u i).val) hd k p).trans
      (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => model_energy_bound m (u i) k p hp) (by norm_num : (0:ℝ) ≤ 2))
    have hv : James.cyclicEnergy (∑ i, u i).val k p ≤ 2 * C := by
      rw [model_val_sum m]
      simpa [C, Finset.mul_sum, mul_assoc] using he
    rw [James.variation, James.probe_norm, one_div_mul_eq_div]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))).mpr
    have hs : Real.sqrt (James.cyclicEnergy (∑ i, u i).val k p) ≤ Real.sqrt (2*C) :=
      Real.sqrt_le_sqrt hv
    simpa [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_comm] using hs
  have hh := mul_self_le_mul_self (norm_nonneg _) hn
  nlinarith [Real.sq_sqrt hC]

/-- Every functional is uniformly small on sufficiently late finitely
supported unit vectors. Otherwise disjoint unit vectors have linear functional
values of order n, contradicting the upper square estimate of order n. -/
theorem finite_tail_small (m : JamesBanachBasisSpec.BanachBasisModel) :
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  ∀ (f : JamesBanachBasisSpec.Sequence →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0 < ε),
    ∃ N : ℕ, ∀ (M : ℕ) (x : JamesBanachBasisSpec.Sequence),
      (∀ k, k < N ∨ M ≤ k → x.val k = 0) → ‖x‖ ≤ 1 → |f x| ≤ ε := by
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  intro f ε hε
  classical
  by_contra h
  push Not at h
  have hbad : ∀ N : ℕ, ∃ (M : ℕ) (x : JamesBanachBasisSpec.Sequence),
      N < M ∧ (∀ k, k < N ∨ M ≤ k → x.val k = 0) ∧ ‖x‖ ≤ 1 ∧ ε < f x := by
    intro N
    obtain ⟨M, x, hx, hn, hf⟩ := h N
    let y := if 0 ≤ f x then x else -x
    refine ⟨max M (N+1), y, by omega, ?_, ?_, ?_⟩
    · intro k hk
      have hz := hx k (hk.elim Or.inl (fun hh => Or.inr (le_trans (le_max_left _ _) hh)))
      dsimp [y]
      split_ifs <;> simp [m.neg_eq, hz]
    · dsimp [y]; split_ifs <;> simpa using hn
    · dsimp [y]; split_ifs with hf0
      · simpa [abs_of_nonneg hf0] using hf
      · simpa [map_neg, abs_of_neg (lt_of_not_ge hf0)] using hf
  choose M u hM hs hu hf using hbad
  let c : ℕ → ℕ := fun n => Nat.rec 0 (fun _ N => M N) n
  have hc (i : ℕ) : c (i+1) = M (c i) := rfl
  have hmono : StrictMono c := strictMono_nat_of_lt_succ fun i => by rw [hc]; exact hM _
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖f‖^2 / ε^2)
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hnε : 2 * ‖f‖^2 < (n:ℝ) * ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hn
  let v : Fin n → JamesBanachBasisSpec.Sequence := fun i => u (c i)
  have hd : ∀ i j, i ≠ j → ∀ k, (v i).val k = 0 ∨ (v j).val k = 0 := by
    intro i j hij k
    wlog hh : i < j generalizing i j
    · exact (this j i (Ne.symm hij) (lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hij))).symm
    by_cases hk : k < M (c i)
    · right
      apply hs
      left
      have hi : c (i.val+1) ≤ c j.val := hmono.monotone (by exact hh)
      rw [hc] at hi
      exact hk.trans_le hi
    · left
      exact hs _ k (Or.inr (le_of_not_gt hk))
  have hb := model_disjoint_bound m v hd
  have hunit : (∑ i : Fin n, ‖v i‖^2) ≤ n := by
    calc
      _ ≤ ∑ i : Fin n, (1:ℝ) := Finset.sum_le_sum fun i _ => by
        dsimp [v]; nlinarith [hu (c i), norm_nonneg (u (c i))]
      _ = _ := by simp
  have hlow : (n:ℝ) * ε ≤ f (∑ i, v i) := by
    rw [map_sum]
    calc
      _ = ∑ _i : Fin n, ε := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => le_of_lt (hf (c i))
  have hop := f.le_opNorm (∑ i, v i)
  rw [Real.norm_eq_abs] at hop
  have hlow' := mul_self_le_mul_self (by positivity : 0 ≤ (n:ℝ)*ε)
    (hlow.trans ((le_abs_self _).trans hop))
  have hup := mul_le_mul_of_nonneg_left (hb.trans (by linarith : 2 * ∑ i, ‖v i‖^2 ≤ 2*(n:ℝ)))
    (sq_nonneg ‖f‖)
  have hh := mul_lt_mul_of_pos_left hnε hn0
  nlinarith

/-- Native projections have the actual truncated coordinates. -/
lemma projection_val (m : JamesBanachBasisSpec.BanachBasisModel) :
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  ∀ (b : SchauderBasis ℝ JamesBanachBasisSpec.Sequence)
    (hb : ∀ i x, b.coord i x = x.val i) (N : ℕ)
    (x : JamesBanachBasisSpec.Sequence) (i : ℕ),
    (b.proj N x).val i = if i < N then x.val i else 0 := by
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  intro b hb N x i
  have hh := congrArg (fun g : JamesBanachBasisSpec.Sequence →L[ℝ] ℝ => g x)
    (DualBasisBasicity.coord_projection b N i)
  by_cases hi : i < N
  · rw [if_pos hi] at hh ⊢
    change b.coord i (b.proj N x) = b.coord i x at hh
    simpa only [hb] using hh
  · rw [if_neg hi] at hh ⊢
    change b.coord i (b.proj N x) = 0 at hh
    simpa only [hb] using hh

/-- The uniform finite-tail estimate extends by basis convergence and yields
operator-norm convergence of the dual projections. -/
theorem shrinking_of_coordinates (m : JamesBanachBasisSpec.BanachBasisModel) :
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  ∀ (b : SchauderBasis ℝ JamesBanachBasisSpec.Sequence)
    (he : b.basis = m.e) (hb : ∀ i x, b.coord i x = x.val i),
    DualBasisBasicity.Spec.IsShrinking b := by
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.toBanachModel.toNormedModel.scalars
  intro b he hb
  have hcontract (N : ℕ) (x : JamesBanachBasisSpec.Sequence) : ‖b.proj N x‖ ≤ ‖x‖ := by
    have hh := m.monotone N x
    simpa only [SchauderBasis.proj_apply, he, hb, C15Basis.Spec.orderedPartialSum] using hh
  intro f
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := finite_tail_small m f (ε/4) (by positivity)
  refine ⟨N, fun K hK => ?_⟩
  have hnorm : ‖f - f.comp (b.proj K)‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    let y := (1/2:ℝ) • (x - b.proj K x)
    have hy : ‖y‖ ≤ 1 := by
      calc
        ‖y‖ = (1/2:ℝ) * ‖x - b.proj K x‖ := by simp [y, norm_smul]
        _ ≤ (1/2:ℝ) * (‖x‖ + ‖b.proj K x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
        _ ≤ 1 := by linarith [hcontract K x]
    have hyzero (i : ℕ) (hi : i < N) : y.val i = 0 := by
      have hix : i < K := hi.trans_le hK
      have hcoord : b.coord i (b.proj K x) = b.coord i x := by
        rw [hb, hb, projection_val m b hb K x i, if_pos hix]
      have hh : b.coord i y = 0 := by
        simp only [y, map_smul, map_sub, hcoord, sub_self, smul_zero]
      rwa [hb] at hh
    have hfinite (M : ℕ) : |f (b.proj M y)| ≤ ε/4 := by
      apply hN M (b.proj M y) _ ((hcontract M y).trans hy)
      intro i hi
      rw [projection_val m b hb]
      rcases hi with hi | hi
      · simp [hyzero i hi]
      · simp [Nat.not_lt.mpr hi]
    have hlimit : |f y| ≤ ε/4 := by
      apply le_of_tendsto ((f.continuous.tendsto y).comp (b.tendsto_proj y)).abs
      exact Eventually.of_forall hfinite
    have heq : f y = (1/2:ℝ) * (f - f.comp (b.proj K)) x := by
      simp [y, map_smul, map_sub]
    rw [heq, abs_mul] at hlimit
    change |(f - f.comp (b.proj K)) x| ≤ ε/2
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 1/2)] at hlimit
    linarith
  simpa only [Real.dist_eq, sub_zero, norm_norm, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
    using lt_of_le_of_lt hnorm (by linarith : ε/2 < ε)

end Model

theorem disjoint_block_estimate : JamesShrinkingSpec.DisjointBlockEstimate := by
  intro m n u hd
  exact model_disjoint_bound m u hd

/-- The coordinate basis of the cyclic James space is shrinking. -/
theorem shrinking : JamesShrinkingSpec.ShrinkingConclusion := by
  refine ⟨James.banach_basis, ?_⟩
  intro m
  letI := m.toBanachModel.toNormedModel.group
  letI := m.toBanachModel.toNormedModel.scalars
  letI : CompleteSpace JamesBanachBasisSpec.Sequence := m.complete
  obtain ⟨b, he, hc, _⟩ := C15CoordinateContinuity.raw_native_basis m.schauder
  have hb (i : ℕ) (x : JamesBanachBasisSpec.Sequence) : b.coord i x = x.val i := by
    rw [hc, m.coordinates]
  exact ⟨b, he, hb, shrinking_of_coordinates m b he hb⟩

end ExpandedFA.P1.JamesShrinking
