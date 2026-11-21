import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.PerturbationZeros
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.Rouche
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Zero counts under uniform holomorphic perturbations and coefficient
perturbations, paper.tex:2295–2300. The proofs retain the original cycle,
the weak holomorphy predicate, and ordinary analytic/algebraic multiplicities.
-/
noncomputable section
open Set Polynomial
open scoped BigOperators

namespace D12Complex.PerturbationZeros

/-- The strict supremum/minimum estimate preserves finite weighted zero counts. -/
theorem cycle_sup_min :
    Specs.D12Complex.Ch09.PerturbationZeros.cycle_sup_min_type := by
  intro Ω Γ f g hf hg htrace hindex hbound
  apply Rouche.cycle Ω Γ f g hf hg htrace hindex
  intro z hz
  have hcompact : IsCompact Γ.trace := PiecewiseC1Length.chain_trace_compact Γ.chain
  have hfc : ContinuousOn f Γ.trace := fun a ha =>
    (hf.2 a (htrace ha)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g Γ.trace := fun a ha =>
    (hg.2 a (htrace ha)).continuousAt.continuousWithinAt
  have habove : BddAbove ((fun w => ‖g w - f w‖) '' Γ.trace) :=
    (hcompact.image_of_continuousOn (hgc.sub hfc).norm).bddAbove
  have hbelow : BddBelow ((fun w => ‖f w‖) '' Γ.trace) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact norm_nonneg _
  exact (le_csSup habove ⟨z, hz, rfl⟩).trans_lt
    (hbound.trans_le (csInf_le hbelow ⟨z, hz, rfl⟩))

/-- A zero-free compact trace has a positive uniform tolerance. -/
theorem cycle_uniform :
    Specs.D12Complex.Ch09.PerturbationZeros.cycle_uniform_type := by
  intro Ω Γ f hf htrace hindex hzero
  have hcompact : IsCompact Γ.trace := PiecewiseC1Length.chain_trace_compact Γ.chain
  have hfc : ContinuousOn f Γ.trace := fun a ha =>
    (hf.2 a (htrace ha)).continuousAt.continuousWithinAt
  obtain ⟨ε, hε, hmin⟩ := hcompact.exists_forall_le' hfc.norm
    (fun z hz => norm_pos_iff.mpr (hzero z hz))
  refine ⟨ε, hε, fun g hg hsmall => ?_⟩
  exact Rouche.cycle Ω Γ f g hf hg htrace hindex
    (fun z hz => (hsmall z hz).trans_le (hmin z hz))

lemma isolating_disk_of_boundary_error
    (Ω : Set ℂ) (c : ℂ) (r : ℝ) (f g : ℂ → ℂ) (m : ℕ)
    (hr : 0 < r) (hf : HolomorphicOn Ω f) (hg : HolomorphicOn Ω g)
    (hclosed : Metric.closedBall c r ⊆ Ω)
    (hm : LocalZeroFactorization.HasFiniteOrder f c m) (hzero : f c = 0)
    (hisol : ∀ z ∈ Metric.closedBall c r, f z = 0 → z = c)
    (herror : ∀ z ∈ Metric.sphere c r, ‖g z - f z‖ < ‖f z‖) :
    (∀ a ∈ Metric.ball c r,
      LocalZeroFactorization.HasFiniteOrder g a (analyticOrderNatAt g a)) ∧
    (∀ z ∈ Metric.sphere c r, g z ≠ 0) ∧
    ∃ t : Finset ℂ,
      (∀ a, a ∈ t ↔ a ∈ Metric.ball c r ∧ g a = 0) ∧
      (∑ a ∈ t, analyticOrderNatAt g a) = m := by
  classical
  obtain ⟨horders, s, t, hs, ht, heq⟩ := Rouche.circle Ω c r f g hr hf hg hclosed herror
  have hsingle : s = {c} := by
    ext a
    rw [hs, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hfa⟩
      exact hisol a (Metric.ball_subset_closedBall ha) hfa
    · rintro rfl
      exact ⟨Metric.mem_ball_self hr, hzero⟩
  have hnat : analyticOrderNatAt f c = m :=
    Rouche.finiteOrder_natOrder ⟨Ω, hclosed (Metric.mem_closedBall_self hr.le), hf⟩ hm
  refine ⟨fun a ha => (horders a ha).2, ?_, t, ht, ?_⟩
  · intro z hz hgz
    have he := herror z hz
    simp [hgz] at he
  · simpa [hsingle, hnat] using heq.symm

lemma isolating_disk
    (Ω : Set ℂ) (c : ℂ) (r : ℝ) (f : ℂ → ℂ) (m : ℕ)
    (hr : 0 < r) (hf : HolomorphicOn Ω f)
    (hclosed : Metric.closedBall c r ⊆ Ω)
    (hm : LocalZeroFactorization.HasFiniteOrder f c m) (hzero : f c = 0)
    (hisol : ∀ z ∈ Metric.closedBall c r, f z = 0 → z = c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (U : Set ℂ) (g : ℂ → ℂ),
      HolomorphicOn U g → Metric.closedBall c r ⊆ U →
      (∀ z ∈ Metric.sphere c r, ‖g z - f z‖ < ε) →
      (∀ a ∈ Metric.ball c r,
        LocalZeroFactorization.HasFiniteOrder g a (analyticOrderNatAt g a)) ∧
      (∀ z ∈ Metric.sphere c r, g z ≠ 0) ∧
      ∃ t : Finset ℂ,
        (∀ a, a ∈ t ↔ a ∈ Metric.ball c r ∧ g a = 0) ∧
        (∑ a ∈ t, analyticOrderNatAt g a) = m := by
  have hcontf : ContinuousOn f (Metric.sphere c r) :=
    fun z hz => (hf.2 z (hclosed (Metric.sphere_subset_closedBall hz))).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun z => ‖f z‖) (Metric.sphere c r) := hcontf.norm
  have hpos : ∀ z ∈ Metric.sphere c r, (0 : ℝ) < ‖f z‖ := by
    intro z hz
    apply norm_pos_iff.mpr
    intro hzeroz
    have hzc := hisol z (Metric.sphere_subset_closedBall hz) hzeroz
    subst z
    have hzr : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hz
    exact (ne_of_gt hr) hzr.symm
  obtain ⟨ε, hε, hbound⟩ := (isCompact_sphere c r).exists_forall_le' hcont hpos
  refine ⟨ε, hε, ?_⟩
  intro U g hg hU herror
  have hf' : HolomorphicOn (Ω ∩ U) f :=
    ⟨hf.1.inter hg.1, fun z hz => hf.2 z hz.1⟩
  have hg' : HolomorphicOn (Ω ∩ U) g :=
    ⟨hf.1.inter hg.1, fun z hz => hg.2 z hz.2⟩
  exact isolating_disk_of_boundary_error (Ω ∩ U) c r f g m hr hf' hg'
    (fun z hz => ⟨hclosed hz, hU hz⟩) hm hzero hisol
    (fun z hz => (herror z hz).trans_le (hbound z hz))

theorem exists_coeff_uniform_bound
    (P : ℂ[X]) (N : ℕ) (hPN : P.natDegree ≤ N)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ > 0, ∀ Q : ℂ[X], Q.natDegree ≤ N →
      (∀ j ≤ N, ‖Q.coeff j - P.coeff j‖ < δ) →
      ∀ z : ℂ, ‖z‖ ≤ R → ‖Q.eval z - P.eval z‖ < ε := by
  let S : ℝ := ∑ j ∈ Finset.range (N + 1), R ^ j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j hj => pow_nonneg hR j
  let δ := ε / (S + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro Q hQN hcoeff z hz
  have heval : Q.eval z - P.eval z =
      ∑ j ∈ Finset.range (N + 1), (Q.coeff j - P.coeff j) * z ^ j := by
    rw [Polynomial.eval_eq_sum_range' (show Q.natDegree < N + 1 by omega),
      Polynomial.eval_eq_sum_range' (show P.natDegree < N + 1 by omega),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hbound : ‖Q.eval z - P.eval z‖ ≤ δ * S := by
    rw [heval]
    calc
      ‖∑ j ∈ Finset.range (N + 1), (Q.coeff j - P.coeff j) * z ^ j‖ ≤
          ∑ j ∈ Finset.range (N + 1), ‖(Q.coeff j - P.coeff j) * z ^ j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (N + 1), δ * R ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_pow]
        apply mul_le_mul
        · exact (hcoeff j (by simpa using Finset.mem_range.mp hj)).le
        · exact pow_le_pow_left₀ (norm_nonneg z) hz j
        · exact pow_nonneg (norm_nonneg z) j
        · exact hδ.le
      _ = δ * S := by simp [S, Finset.mul_sum]
  have hmul : δ * (S + 1) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ ε (by positivity)
  exact hbound.trans_lt (by nlinarith)


theorem exists_coeff_uniform_bound_on_bounded
    (P : ℂ[X]) (N : ℕ) (hPN : P.natDegree ≤ N)
    (K : Set ℂ) (hK : Bornology.IsBounded K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ Q : ℂ[X], Q.natDegree ≤ N →
      (∀ j ≤ N, ‖Q.coeff j - P.coeff j‖ < δ) →
      ∀ z ∈ K, ‖Q.eval z - P.eval z‖ < ε := by
  obtain ⟨R, hR, hKR⟩ := hK.exists_pos_norm_le
  obtain ⟨δ, hδ, hδprop⟩ := exists_coeff_uniform_bound P N hPN R ε hR.le hε
  exact ⟨δ, hδ, fun Q hQ hcoeff z hz => hδprop Q hQ hcoeff z (hKR z hz)⟩


theorem polynomial_analyticOrderAt_eq_rootMultiplicity
    (P : ℂ[X]) (hP : P ≠ 0) (a : ℂ) :
    analyticOrderAt (fun z => P.eval z) a = (P.rootMultiplicity a : ℕ∞) := by
  have hPa : AnalyticAt ℂ (fun z => P.eval z) a :=
    (AnalyticOnNhd.eval_polynomial P) a (Set.mem_univ a)
  apply hPa.analyticOrderAt_eq_natCast.mpr
  let q := P /ₘ (X - C a) ^ P.rootMultiplicity a
  refine ⟨fun z => q.eval z,
    (AnalyticOnNhd.eval_polynomial q) a (Set.mem_univ a),
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hP, ?_⟩
  apply Filter.Eventually.of_forall
  intro z
  have h := congrArg (fun Q : ℂ[X] => Q.eval z)
    (P.pow_mul_divByMonic_rootMultiplicity_eq a)
  simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul] using h.symm

theorem polynomial_analyticOrderNatAt_eq_rootMultiplicity
    (P : ℂ[X]) (a : ℂ) :
    analyticOrderNatAt (fun z => P.eval z) a = P.rootMultiplicity a := by
  by_cases hP : P = 0
  · subst P
    simp only [eval_zero, rootMultiplicity_zero, analyticOrderNatAt]
    change (analyticOrderAt (0 : ℂ → ℂ) a).toNat = 0
    simp
  · simp [analyticOrderNatAt, polynomial_analyticOrderAt_eq_rootMultiplicity P hP a]


theorem polynomial_finiteOrder
    (P : ℂ[X]) (hP : P ≠ 0) (a : ℂ) :
    D12Complex.LocalZeroFactorization.HasFiniteOrder (fun z => P.eval z) a
      (P.rootMultiplicity a) := by
  apply (D12Complex.LocalZeroFactorization.order_eq_nat_iff _ _
    ((D12Complex.LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mpr
      ((AnalyticOnNhd.eval_polynomial P) a (Set.mem_univ a))) _).mp
  exact polynomial_analyticOrderAt_eq_rootMultiplicity P hP a



/-- Polynomial and analytic multiplicities in the form used by the perturbation
statements. This local division argument needs no global root theorem. -/
theorem polynomial_multiplicity :
    Specs.D12Complex.Ch09.PerturbationZeros.polynomial_multiplicity_type := by
  intro P hP a
  exact ⟨polynomial_finiteOrder P hP a,
    polynomial_analyticOrderNatAt_eq_rootMultiplicity P a⟩

/-- One coefficient tolerance controls every chosen isolating boundary. -/
theorem polynomial_disks :
    Specs.D12Complex.Ch09.PerturbationZeros.polynomial_disks_type := by
  classical
  intro P N k c r hP hPN hr hroot hisol
  let K : Set ℂ := ⋃ i : Fin k, Metric.sphere (c i) (r i)
  have hK : IsCompact K := isCompact_iUnion fun i => isCompact_sphere (c i) (r i)
  have hnonzero : ∀ z ∈ K, P.eval z ≠ 0 := by
    intro z hz hzero
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    have hzc := hisol i z (Metric.sphere_subset_closedBall hi) hzero
    subst z
    have he : (0 : ℝ) = r i := by simpa [Metric.mem_sphere] using hi
    exact (hr i).ne' he.symm
  have hcont : ContinuousOn (fun z => P.eval z) K :=
    (Polynomial.continuous P).continuousOn
  obtain ⟨ε, hε, hmin⟩ := hK.exists_forall_le' hcont.norm
    (fun z hz => norm_pos_iff.mpr (hnonzero z hz))
  obtain ⟨δ, hδ, hbound⟩ :=
    exists_coeff_uniform_bound_on_bounded P N hPN K hK.isBounded ε hε
  refine ⟨δ, hδ, ?_⟩
  intro Q hQN hcoeff i
  have hhol (A : Polynomial ℂ) : HolomorphicOn Set.univ (fun z => A.eval z) :=
    ⟨isOpen_univ, fun z _ => A.differentiableAt⟩
  have herr : ∀ z ∈ Metric.sphere (c i) (r i), ‖Q.eval z - P.eval z‖ < ‖P.eval z‖ := by
    intro z hz
    have hzK : z ∈ K := Set.mem_iUnion.mpr ⟨i, hz⟩
    exact (hbound Q hQN hcoeff z hzK).trans_le (hmin z hzK)
  obtain ⟨_, hboundary, t, ht, hsum⟩ := isolating_disk_of_boundary_error Set.univ
    (c i) (r i) (fun z => P.eval z) (fun z => Q.eval z)
    (P.rootMultiplicity (c i)) (hr i) (hhol P) (hhol Q) (subset_univ _)
    (polynomial_finiteOrder P hP (c i)) (hroot i) (hisol i) herr
  refine ⟨hboundary, t, ht, ?_⟩
  simpa only [polynomial_analyticOrderNatAt_eq_rootMultiplicity] using hsum

/-- In a disk about a simple root the count one gives one simple root. -/
theorem simple_polynomial_disks :
    Specs.D12Complex.Ch09.PerturbationZeros.simple_polynomial_disks_type := by
  classical
  intro P N k c r hP hPN hr hroot hsimple hisol
  obtain ⟨δ, hδ, hprop⟩ := polynomial_disks P N k c r hP hPN hr hroot hisol
  refine ⟨δ, hδ, ?_⟩
  intro Q hQN hcoeff i
  obtain ⟨_, t, ht, hsum⟩ := hprop Q hQN hcoeff i
  rw [hsimple i] at hsum
  have hQ : Q ≠ 0 := by
    intro hzero
    subst Q
    simp at hsum
  have htpos : ∀ a ∈ t, 1 ≤ Q.rootMultiplicity a := by
    intro a ha
    exact (Polynomial.rootMultiplicity_pos hQ).mpr ((ht a).mp ha).2
  have hcardle : t.card ≤ 1 := by
    calc
      t.card = ∑ a ∈ t, 1 := by simp
      _ ≤ ∑ a ∈ t, Q.rootMultiplicity a := Finset.sum_le_sum htpos
      _ = 1 := hsum
  have htnonempty : t.Nonempty := by
    by_contra hempty
    have hte : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp [hte] at hsum
  have hcard : t.card = 1 := by
    have hcardpos := Finset.card_pos.mpr htnonempty
    omega
  obtain ⟨a, hta⟩ := Finset.card_eq_one.mp hcard
  have ha : a ∈ t := by simp [hta]
  have ham : Q.rootMultiplicity a = 1 := by simpa [hta] using hsum
  refine ⟨a, ((ht a).mp ha).1, ((ht a).mp ha).2, ham, ?_⟩
  intro b hb hbzero
  have hbt : b ∈ t := (ht b).mpr ⟨hb, hbzero⟩
  simpa [hta] using hbt

end D12Complex.PerturbationZeros
