import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularSurgeryPartition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularCornerRounding
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.FiniteCircularArcs
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularAngularCuts
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularRetainedDisplay
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Sort
import Lean.Elab.Tactic.Omega
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
open Set Metric MeasureTheory
open scoped Topology ContDiff NNReal Interval

noncomputable section
namespace D12Complex.CircularSurgeryPartition

open CircularCornerRounding

/-- A closed removal preserves the actual set and frontier on its open
complement. This is also the local side equality needed on retained arcs. -/
lemma closed_removal_local_equality {U K : Set ℂ} (hK : IsClosed K) {z : ℂ}
    (hz : z ∉ K) :
    ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧
      U ∩ W = (U \ K) ∩ W ∧
      frontier U ∩ W = frontier (U \ K) ∩ W := by
  refine ⟨Kᶜ, hK.isOpen_compl, hz, ?_, ?_⟩
  · ext w
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  · have h := frontier_inter_open_inter (s := U) hK.isOpen_compl
    change frontier (U \ K) ∩ Kᶜ = frontier U ∩ Kᶜ at h
    exact h.symm

/-- Actual literal surgery and its uniform charts. This component does not
claim a finite subdivision of the supplied parameter intervals. -/
theorem literal_surgery_uniform :
    Specs.D12Complex.Ch14.CircularSurgeryPartition.literal_surgery_uniform_type := by
  intro U J hgeom
  obtain ⟨θ, e, R, L, hR, hL, hθ, hside, hc, hp, hdisj, hLip⟩ :=
    exists_uniform_corner_charts hgeom
  refine ⟨θ, e, R, L, ⟨hR, hL, hθ, hside, hc, hp, hdisj, hLip⟩, ?_⟩
  intro ε hε hεR
  have htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target := by
    intro p hpJ
    exact (sectorTip_subset_closedBall hε).trans
      ((closedBall_subset_closedBall hεR.le).trans (hLip p hpJ).1)
  obtain ⟨hK, hV, hdef, hclass, hparam⟩ :=
    finite_chart_surgery hgeom e θ hε hθ hside hc hp hdisj htip
  exact ⟨hK, hV, hdef, hclass, hparam,
    fun _ hz => closed_removal_local_equality hK.isClosed hz,
    chart_surgery_isImage e θ ε hside hdisj htip⟩

lemma speed_continuousOn {g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : ContDiff ℝ 1 γ)
    (hg : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 g (γ t)) :
    ContinuousOn (fun t => ‖deriv (g ∘ γ) t‖) (Icc a b) := by
  intro t ht
  have hc : ContDiffAt ℝ 1 (g ∘ γ) t := (hg t ht).comp t hγ.contDiffAt
  have hcont := (hc.continuousAt_fderiv (by norm_num)).norm
  simpa only [norm_deriv_eq_norm_fderiv] using hcont.continuousWithinAt

lemma norm_deriv_comp_le {g : ℂ → ℂ} {γ : ℝ → ℂ} {R t K : ℝ} {L : ℝ≥0}
    (hg : DifferentiableAt ℝ g (γ t)) (hγ : DifferentiableAt ℝ γ t)
    (hLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hR : ‖γ t‖ < R) (hK : ‖deriv γ t‖ ≤ K) :
    ‖deriv (g ∘ γ) t‖ ≤ (L : ℝ) * K := by
  have hball : closedBall (0 : ℂ) R ∈ 𝓝 (γ t) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds (by simpa using hR)) ball_subset_closedBall
  rw [(hg.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt).deriv]
  calc
    ‖(fderiv ℝ g (γ t)) (deriv γ t)‖ ≤
        ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (L : ℝ) * K := mul_le_mul (norm_fderiv_le_of_lipschitzOn ℝ hball hLip)
        hK (norm_nonneg _) L.coe_nonneg

lemma integrated_speed_comp_le {g : ℂ → ℂ} {γ : ℝ → ℂ} {a b R K : ℝ}
    {L : ℝ≥0} (hab : a ≤ b) (hγ : ContDiff ℝ 1 γ)
    (hg : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 g (γ t))
    (hLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hR : ∀ t ∈ Icc a b, ‖γ t‖ < R)
    (hK : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ K) :
    IntervalIntegrable (fun t => ‖deriv (g ∘ γ) t‖) volume a b ∧
    (∫ t in a..b, ‖deriv (g ∘ γ) t‖) ≤ (b - a) * (L : ℝ) * K := by
  have hi : IntervalIntegrable (fun t => ‖deriv (g ∘ γ) t‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using speed_continuousOn hγ hg
  refine ⟨hi, ?_⟩
  have hbound : ∀ t ∈ Icc a b, ‖deriv (g ∘ γ) t‖ ≤ (L : ℝ) * K := by
    intro t ht
    exact norm_deriv_comp_le ((hg t ht).differentiableAt (by norm_num))
      (hγ.differentiable (by norm_num) t) hLip (hR t ht) (hK t ht)
  have hmono := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := (L : ℝ) * K)) hbound
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_assoc] using hmono

open D12Complex.CircularCornerRounding
lemma chart_rounding_length_le {g : ℂ → ℂ} {W : Set ℂ} {L : ℝ≥0} {R ε θ : ℝ}
    (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (hball : closedBall (0 : ℂ) R ⊆ W)
    (hLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hε : 0 < ε) (hεR : ε < R) (hθ : 0 < θ) :
    IntervalIntegrable (fun t => ‖deriv (g ∘ roundingArc ε θ) t‖) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ‖deriv (g ∘ roundingArc ε θ) t‖) ≤
      (L : ℝ) * (Real.pi / 2 + 6 * θ) * ε := by
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖roundingArc ε θ t‖ ≤ ε := by
    intro t ht
    rw [norm_roundingArc hε.le ht]
    exact mul_le_of_le_one_right hε.le (radialProfile_bounds ht).2
  have hgc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 g (roundingArc ε θ t) := by
    intro t ht
    apply hg.contDiffAt (hW.mem_nhds _)
    exact hball (by simpa using (hnorm t ht).trans hεR.le)
  have hi := integrated_speed_comp_le (g := g) (γ := roundingArc ε θ)
    (R := R) (L := L) (by norm_num : (0 : ℝ) ≤ 1)
    ((contDiff_roundingArc ε θ).of_le (by simp)) hgc hLip
    (fun t ht => (hnorm t ht).trans_lt hεR)
    (fun t ht => norm_deriv_roundingArc_le hε hθ ht)
  constructor
  · exact hi.1
  · simpa only [sub_zero, one_mul, mul_assoc] using hi.2

/-- Integrated actual speed of the inverse-chart rounding curve. -/
theorem pullback_roundingArc_length :
    Specs.D12Complex.Ch14.CircularSurgeryPartition.pullback_roundingArc_length_type := by
  intro g R L hg hLip ε θ hε hεR hθ
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖roundingArc ε θ t‖ < R := by
    intro t ht
    rw [norm_roundingArc hε.le ht]
    exact (mul_le_of_le_one_right hε.le (radialProfile_bounds ht).2).trans_lt hεR
  have hgc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 g (roundingArc ε θ t) := by
    intro t ht
    exact hg.contDiffAt (isOpen_ball.mem_nhds (by simpa using hnorm t ht))
  have hi := integrated_speed_comp_le (g := g) (γ := roundingArc ε θ)
    (R := R) (L := L) (by norm_num : (0 : ℝ) ≤ 1)
    ((contDiff_roundingArc ε θ).of_le (by simp)) hgc hLip hnorm
    (fun t ht => norm_deriv_roundingArc_le hε hθ ht)
  exact ⟨hi.1, by simpa only [sub_zero, one_mul, mul_assoc, Function.comp_def] using! hi.2⟩

/-- The same estimate for the literal normalized short ray, including every
unit-bounded direction. -/
theorem pullback_shortRay_length :
    Specs.D12Complex.Ch14.CircularSurgeryPartition.pullback_shortRay_length_type := by
  intro g R L hg hLip ε ξ hε hεR hξ
  let γ : ℝ → ℂ := fun t => (ε * t) • ξ
  have hγ : ContDiff ℝ 1 γ := (contDiff_const.mul contDiff_id).smul contDiff_const
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ < R := by
    intro t ht
    have hεt : 0 ≤ ε * t := mul_nonneg hε.le ht.1
    calc
      ‖γ t‖ = (ε * t) * ‖ξ‖ := by
        change ‖(ε * t) • ξ‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hεt]
      _ ≤ ε * t := mul_le_of_le_one_right hεt hξ
      _ ≤ ε := mul_le_of_le_one_right hε.le ht.2
      _ < R := hεR
  have hgc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 g (γ t) := by
    intro t ht
    exact hg.contDiffAt (isOpen_ball.mem_nhds (by simpa using hnorm t ht))
  have hd : ∀ t : ℝ, HasDerivAt γ (ε • ξ) t := by
    intro t
    simpa only [γ, mul_one, id_eq] using! ((hasDerivAt_id t).const_mul ε).smul_const ξ
  have hK : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ ≤ ε := by
    intro t _
    rw [(hd t).deriv, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact mul_le_of_le_one_right hε.le hξ
  have hi := integrated_speed_comp_le (g := g) (γ := γ) (R := R) (L := L)
    (by norm_num : (0 : ℝ) ≤ 1) hγ hgc hLip hnorm hK
  exact ⟨hi.1, by simpa only [sub_zero, one_mul, Function.comp_def, γ] using! hi.2⟩

lemma contDiff_ray (θ : ℝ) :
    ContDiff ℝ 1 (fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  exact (Complex.ofRealCLM.contDiff : ContDiff ℝ 1 ((↑) : ℝ → ℂ)).mul contDiff_const

lemma hasDerivAt_ray (θ r : ℝ) :
    HasDerivAt (fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I)) r := by
  simpa using (hasDerivAt_id r).ofReal_comp.mul_const
    (Complex.exp ((θ : ℂ) * Complex.I))

lemma chart_shortRay_length_le {g : ℂ → ℂ} {W : Set ℂ} {L : ℝ≥0} {R ε θ : ℝ}
    (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (hball : closedBall (0 : ℂ) R ⊆ W)
    (hLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hε : 0 ≤ ε) (hεR : ε < R) :
    IntervalIntegrable
      (fun r => ‖deriv (g ∘ fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) r‖)
      volume 0 ε ∧
    (∫ r in (0 : ℝ)..ε,
      ‖deriv (g ∘ fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) r‖) ≤
      (L : ℝ) * ε := by
  let γ : ℝ → ℂ := fun r => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hnorm : ∀ r ∈ Icc (0 : ℝ) ε, ‖γ r‖ = r := by
    intro r hr
    simp only [γ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg hr.1]
  have hgc : ∀ r ∈ Icc (0 : ℝ) ε, ContDiffAt ℝ 1 g (γ r) := by
    intro r hr
    apply hg.contDiffAt (hW.mem_nhds _)
    exact hball (by simpa [hnorm r hr] using hr.2.trans hεR.le)
  have hi := integrated_speed_comp_le (g := g) (γ := γ) (R := R) (L := L)
    hε (contDiff_ray θ) hgc hLip
    (fun r hr => by rw [hnorm r hr]; exact hr.2.trans_lt hεR) (K := 1)
    (fun r hr => by
      rw [(hasDerivAt_ray θ r).deriv]
      exact (Complex.norm_exp_ofReal_mul_I θ).le)
  constructor
  · exact hi.1
  · simpa [γ, mul_comm] using hi.2


lemma chart_normalized_shortRay_length_le {g : ℂ → ℂ} {W : Set ℂ}
    {L : ℝ≥0} {R ε θ : ℝ}
    (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (hball : closedBall (0 : ℂ) R ⊆ W)
    (hLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hε : 0 ≤ ε) (hεR : ε < R) :
    IntervalIntegrable
      (fun t => ‖deriv (g ∘ fun t : ℝ => ((ε * t : ℝ) : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I)) t‖) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1,
      ‖deriv (g ∘ fun t : ℝ => ((ε * t : ℝ) : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I)) t‖) ≤ (L : ℝ) * ε := by
  let γ : ℝ → ℂ := fun t => ((ε * t : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hγ : ContDiff ℝ 1 γ :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ ε := by
    intro t ht
    change ‖((ε * t : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ ε
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg (mul_nonneg hε ht.1)]
    exact mul_le_of_le_one_right hε ht.2
  have hgc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 g (γ t) := by
    intro t ht
    apply hg.contDiffAt (hW.mem_nhds _)
    exact hball (by simpa using (hnorm t ht).trans hεR.le)
  have hderiv : ∀ t : ℝ, HasDerivAt γ
      ((ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) t := by
    intro t
    simpa [γ] using ((hasDerivAt_id t).const_mul ε).ofReal_comp.mul_const
      (Complex.exp ((θ : ℂ) * Complex.I))
  have hi := integrated_speed_comp_le (g := g) (γ := γ) (R := R) (L := L)
    (by norm_num : (0 : ℝ) ≤ 1) hγ hgc hLip
    (fun t ht => (hnorm t ht).trans_lt hεR) (K := ε)
    (fun t _ => by
      rw [(hderiv t).deriv]
      simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hε])
  constructor
  · exact hi.1
  · simpa only [sub_zero, one_mul] using hi.2


/-- Finitely many physical marked points have only finitely many parameters on a
closed interval when the open part is injectively parametrized. The two ends
may coincide, as they do for a complete circle. -/
lemma finite_marked_parameters {β : Type*} {γ : ℝ → β} {a b : ℝ}
    (hγ : InjOn γ (Ioo a b)) (F : Set β) (hF : F.Finite) :
    (Icc a b ∩ γ ⁻¹' F).Finite := by
  have hmid : (Ioo a b ∩ γ ⁻¹' F).Finite :=
    hF.of_injOn (f := γ) (fun _ hx => hx.2) (hγ.mono inter_subset_left)
  apply (hmid.union (finite_singleton a |>.union (finite_singleton b))).subset
  intro t ht
  by_cases hta : t = a
  · exact Or.inr (Or.inl hta)
  by_cases htb : t = b
  · exact Or.inr (Or.inr htb)
  exact Or.inl ⟨⟨lt_of_le_of_ne ht.1.1 (Ne.symm hta),
    lt_of_le_of_ne ht.1.2 htb⟩, ht.2⟩

/-- In particular every physical fiber is finite, even at a repeated
full-circle endpoint. -/
lemma finite_parameter_fiber {β : Type*} {γ : ℝ → β} {a b : ℝ}
    (hγ : InjOn γ (Ioo a b)) (z : β) :
    (Icc a b ∩ γ ⁻¹' {z}).Finite :=
  finite_marked_parameters hγ {z} (finite_singleton z)

/-- A strict finite node array that cuts at every marked physical point.
All open consecutive intervals therefore avoid all marks. No continuity of the
curve is needed for this purely finite combinatorial construction. -/
lemma exists_finite_marked_nodes {β : Type*} {γ : ℝ → β} {a b : ℝ}
    (hab : a < b) (hγ : InjOn γ (Ioo a b)) (F : Set β) (hF : F.Finite) :
    ∃ (k : ℕ) (node : Fin (k + 1) → ℝ),
      StrictMono node ∧ node 0 = a ∧ node (Fin.last k) = b ∧
      (∀ t ∈ Icc a b, γ t ∈ F → t ∈ Set.range node) ∧
      ∀ (j : Fin k) (t : ℝ),
        t ∈ Ioo (node j.castSucc) (node j.succ) → γ t ∉ F := by
  classical
  let S : Set ℝ := insert a (insert b (Icc a b ∩ γ ⁻¹' F))
  have hS : S.Finite := ((finite_marked_parameters hγ F hF).insert b).insert a
  let s : Finset ℝ := hS.toFinset
  have hs (t : ℝ) : t ∈ s ↔ t ∈ S := Set.Finite.mem_toFinset hS
  have ha : a ∈ s := (hs a).mpr (by exact Or.inl rfl)
  have hb : b ∈ s := (hs b).mpr (by exact Or.inr (Or.inl rfl))
  have hbound : ∀ t ∈ s, a ≤ t ∧ t ≤ b := by
    intro t ht
    rcases (hs t).mp ht with rfl | rfl | ht
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
    · exact ht.1
  have hcard : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard)
  let node : Fin (k + 1) → ℝ := s.orderEmbOfFin hk
  have hnode : StrictMono node := (s.orderEmbOfFin hk).strictMono
  have hmem (j : Fin (k + 1)) : node j ∈ s := s.orderEmbOfFin_mem hk j
  have hsurj (t : ℝ) (ht : t ∈ s) : t ∈ Set.range node := by
    rw [show Set.range node = (s : Set ℝ) from s.range_orderEmbOfFin hk]
    exact ht
  have hfirst : node 0 = a := by
    obtain ⟨j, hj⟩ := hsurj a ha
    apply le_antisymm
    · rw [← hj]
      exact hnode.monotone (Fin.zero_le j)
    · exact (hbound _ (hmem 0)).1
  have hlast : node (Fin.last k) = b := by
    obtain ⟨j, hj⟩ := hsurj b hb
    apply le_antisymm
    · exact (hbound _ (hmem _)).2
    · rw [← hj]
      exact hnode.monotone (Fin.le_last j)
  refine ⟨k, node, hnode, hfirst, hlast, ?_, ?_⟩
  · intro t ht hFt
    exact hsurj t ((hs t).mpr (Or.inr (Or.inr ⟨ht, hFt⟩)))
  · intro j t ht hFt
    have hta : a < t := lt_of_le_of_lt (hbound _ (hmem j.castSucc)).1 ht.1
    have htb : t < b := lt_of_lt_of_le ht.2 (hbound _ (hmem j.succ)).2
    obtain ⟨l, hl⟩ := hsurj t ((hs t).mpr (Or.inr (Or.inr ⟨⟨hta.le, htb.le⟩, hFt⟩)))
    have hleft : j.castSucc < l := hnode.lt_iff_lt.mp (hl ▸ ht.1)
    have hright : l < j.succ := hnode.lt_iff_lt.mp (hl ▸ ht.2)
    have hleft' : (j : ℕ) < (l : ℕ) := hleft
    have hright' : (l : ℕ) < (j : ℕ) + 1 := hright
    omega


open CircularExhaustion CircularCornerRounding

/-- Restrict actual uniform charts to exclude finitely many supplied endpoints
other than their center. The inverse Lipschitz constant is unchanged; only the
common positive coordinate radius is shrunk. -/
theorem uniformCharts_restrict_away_finite
    {U : Set ℂ} {J : Finset ℂ} {θ : ℂ → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {R : ℝ} {L : ℝ≥0}
    (h : UniformCharts U J θ e R L) (F : Finset ℂ) :
    ∃ (E : ℂ → OpenPartialHomeomorph ℂ ℂ) (r : ℝ),
      UniformCharts U J θ E r L ∧ r ≤ R ∧
      (∀ p : ℂ, (E p : ℂ → ℂ) = e p ∧ ((E p).symm : ℂ → ℂ) = (e p).symm) ∧
      (∀ p ∈ J, (E p).source ⊆ (e p).source ∧
        ∀ q ∈ F, q ≠ p → q ∉ (E p).source) := by
  classical
  obtain ⟨hR, hL, hθ, hside, hc, hp, hdisj, hLip⟩ := h
  let A : ℂ → Set ℂ := fun p => (↑(F.erase p) : Set ℂ)ᶜ
  have hA : ∀ p : ℂ, IsOpen (A p) := fun p =>
    (F.erase p).finite_toSet.isClosed.isOpen_compl
  let E : ℂ → OpenPartialHomeomorph ℂ ℂ := fun p => (e p).restrOpen (A p) (hA p)
  have hpE : ∀ p ∈ J, p ∈ (E p).source ∧ E p p = 0 := by
    intro p hpJ
    refine ⟨⟨(hp p hpJ).1, ?_⟩, (hp p hpJ).2⟩
    simp only [A, mem_compl_iff, Finset.mem_coe, Finset.mem_erase, ne_eq,
      not_true_eq_false, false_and, not_false_eq_true]
  have hradius : ∀ p : ℂ, ∃ s : ℝ, 0 < s ∧
      (p ∈ J → closedBall (0 : ℂ) s ⊆ (E p).target) := by
    intro p
    by_cases hpJ : p ∈ J
    · have hz : (0 : ℂ) ∈ (E p).target := by
        rw [← (hpE p hpJ).2]
        exact (E p).map_source (hpE p hpJ).1
      obtain ⟨s, hs, hsT⟩ := Metric.mem_nhds_iff.mp ((E p).open_target.mem_nhds hz)
      exact ⟨s / 2, by positivity, fun _ =>
        (closedBall_subset_ball (by linarith : s / 2 < s)).trans hsT⟩
    · exact ⟨1, by norm_num, fun hp => (hpJ hp).elim⟩
  choose rp hrp htarget using hradius
  obtain ⟨r₀, hr₀, hr₀p⟩ := finite_positive_lower_bound J rp (fun p _ => hrp p)
  let r : ℝ := min R r₀
  have hr : 0 < r := lt_min hR hr₀
  have hrR : r ≤ R := min_le_left _ _
  have hrp' : ∀ p ∈ J, r ≤ rp p := fun p hpJ =>
    (min_le_right R r₀).trans (hr₀p p hpJ)
  have htarget' : ∀ p ∈ J, closedBall (0 : ℂ) r ⊆ (E p).target := by
    intro p hpJ
    exact (closedBall_subset_closedBall (hrp' p hpJ)).trans (htarget p hpJ)
  refine ⟨E, r, ?_, hrR, ?_, ?_⟩
  · refine ⟨hr, hL, hθ, ?_, ?_, hpE, ?_, ?_⟩
    · intro p hpJ z hz
      exact hside p hpJ hz.1
    · intro p hpJ
      exact ⟨(hc p hpJ).1.mono inter_subset_left,
        (hc p hpJ).2.mono inter_subset_left⟩
    · intro p hpJ q hqJ hpq
      exact (hdisj p hpJ q hqJ hpq).mono inter_subset_left inter_subset_left
    · intro p hpJ
      exact ⟨htarget' p hpJ,
        (hLip p hpJ).2.mono (closedBall_subset_closedBall hrR)⟩
  · intro p
    exact ⟨rfl, rfl⟩
  · intro p hpJ
    refine ⟨inter_subset_left, ?_⟩
    intro q hqF hqp hqE
    exact hqE.2 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hqp, hqF⟩))


open CircularCornerRounding

lemma inverse_chart_curve_deriv_ne_zero (e : OpenPartialHomeomorph ℂ ℂ)
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    {γ : ℝ → ℂ} {t : ℝ} (hγ : DifferentiableAt ℝ γ t)
    (ht : γ t ∈ e.target) (hreg : deriv γ t ≠ 0) :
    deriv (fun s => e.symm (γ s)) t ≠ 0 := by
  have hed := (he.contDiffAt (e.open_source.mem_nhds (e.map_target ht))).differentiableAt
    (by norm_num)
  have heid := (hei.contDiffAt (e.open_target.mem_nhds ht)).differentiableAt (by norm_num)
  have hδ := heid.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
  have hcomp := hed.hasFDerivAt.comp_hasDerivAt t hδ
  have heq : γ =ᶠ[𝓝 t] e ∘ e.symm ∘ γ := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds ht)] with s hs
    exact (e.right_inv hs).symm
  have hid : fderiv ℝ e (e.symm (γ t)) (fderiv ℝ e.symm (γ t) (deriv γ t)) =
      deriv γ t := by
    exact (hcomp.congr_of_eventuallyEq heq).deriv.symm
  intro hz
  have hz' : fderiv ℝ e.symm (γ t) (deriv γ t) = 0 := by
    simpa only [Function.comp_def] using hδ.deriv.symm.trans hz
  apply hreg
  rw [← hid, hz', map_zero]

lemma inserted_curve_regular_neighborhood {U : Set ℂ} {J : Finset ℂ}
    {θ : ℂ → ℝ} {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {R ε : ℝ} {L : ℝ≥0}
    (hc : UniformCharts U J θ e R L) (hε : 0 < ε) (hεR : ε < R)
    {p : ℂ} (hp : p ∈ J) :
    ∃ T : Set ℝ, IsOpen T ∧ Icc (0 : ℝ) 1 ⊆ T ∧
      ContDiffOn ℝ 1 (fun t => (e p).symm (roundingArc ε (θ p) t)) T ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t ≠ 0) ∧
      InjOn (fun t => (e p).symm (roundingArc ε (θ p) t)) (Icc (0 : ℝ) 1) := by
  obtain ⟨hR, hL, hθ, hside, hdiff, horig, hdisj, hball⟩ := hc
  have htarget : ∀ t ∈ Icc (0 : ℝ) 1, roundingArc ε (θ p) t ∈ (e p).target := by
    intro t ht
    apply (hball p hp).1
    rw [mem_closedBall, dist_zero_right, norm_roundingArc hε.le ht]
    exact (mul_le_of_le_one_right hε.le (radialProfile_bounds ht).2).trans hεR.le
  let T : Set ℝ := roundingArc ε (θ p) ⁻¹' (e p).target
  refine ⟨T, (e p).open_target.preimage (contDiff_roundingArc ε (θ p)).continuous,
    htarget, ?_, ?_, ?_⟩
  · exact (hdiff p hp).2.comp ((contDiff_roundingArc ε (θ p)).of_le (by simp)).contDiffOn (fun _ ht => ht)
  · intro t ht
    exact inverse_chart_curve_deriv_ne_zero (e p) (hdiff p hp).1 (hdiff p hp).2
      ((hasDerivAt_roundingArc ε (θ p) t).differentiableAt) (htarget t ht)
      (roundingArc_regular hε (hθ p hp).1 ht)
  · intro s hs t ht heq
    apply roundingArc_injOn hε (hθ p hp).1 (hθ p hp).2 hs ht
    exact (e p).symm.injOn (htarget s hs) (htarget t ht) heq

open CircularCornerRounding

lemma inserted_curves_total_speed {U : Set ℂ} {J : Finset ℂ}
    {θ : ℂ → ℝ} {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {R : ℝ} {L : ℝ≥0}
    (hc : UniformCharts U J θ e R L) :
    let C := (L : ℝ) * (∑ p ∈ J, (Real.pi / 2 + 6 * θ p)) + 1
    0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < R →
      (∀ p ∈ J, IntervalIntegrable
        (fun t => ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖)
        volume 0 1) ∧
      (∑ p ∈ J, ∫ t in (0 : ℝ)..1,
        ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖) ≤ C * ε := by
  obtain ⟨hR, hL, hθ, hside, hdiff, horig, hdisj, hball⟩ := hc
  have hsum : 0 ≤ ∑ p ∈ J, (Real.pi / 2 + 6 * θ p) := by
    apply Finset.sum_nonneg
    intro p hp
    have hpθ := (hθ p hp).1
    positivity
  refine ⟨by positivity, ?_⟩
  intro ε hε hεR
  have hpart : ∀ p ∈ J,
      IntervalIntegrable
        (fun t => ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖)
        volume 0 1 ∧
      (∫ t in (0 : ℝ)..1,
        ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖) ≤
          (L : ℝ) * (Real.pi / 2 + 6 * θ p) * ε := by
    intro p hp
    exact chart_rounding_length_le (e p).open_target (hdiff p hp).2
      (hball p hp).1 (hball p hp).2 hε hεR (hθ p hp).1
  refine ⟨fun p hp => (hpart p hp).1, ?_⟩
  calc
    (∑ p ∈ J, ∫ t in (0 : ℝ)..1,
        ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖)
        ≤ ∑ p ∈ J, (L : ℝ) * (Real.pi / 2 + 6 * θ p) * ε :=
      Finset.sum_le_sum (fun p hp => (hpart p hp).2)
    _ = ((L : ℝ) * ∑ p ∈ J, (Real.pi / 2 + 6 * θ p)) * ε := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ((L : ℝ) * (∑ p ∈ J, (Real.pi / 2 + 6 * θ p)) + 1) * ε :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) hε.le

open CircularExhaustion CircularCornerRounding Complex


open CircularExhaustion CircularCornerRounding Complex

lemma bottom_mem_frontier_sector {θ r : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : 0 ≤ r) :
    (r : ℂ) ∈ frontier (sector θ) := by
  have hpos : Ioi (0 : ℝ) ⊆ (fun s : ℝ => (s : ℂ)) ⁻¹' frontier (sector θ) := by
    intro s hs
    refine ⟨closure_mono sdiff_subset (bottomTail_mem_frontier_roundedSector hs hθ hθ' le_rfl).1, ?_⟩
    intro hi
    have hm : (s : ℂ) ∈ sector θ := by simpa only [(isOpen_sector θ).interior_eq] using hi
    have hn := (polar_mem_sector_iff hs ⟨le_rfl, hθ.le⟩ hθ').mp
      (show (s : ℂ) * exp ((0 : ℂ) * I) ∈ sector θ by simpa using hm)
    exact (lt_irrefl (0 : ℝ)) hn.1
  have hc := closure_minimal hpos (isClosed_frontier.preimage Complex.continuous_ofReal)
  rw [closure_Ioi] at hc
  exact hc hr

lemma top_mem_frontier_sector {θ r : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : 0 ≤ r) :
    (r : ℂ) * exp ((θ : ℂ) * I) ∈ frontier (sector θ) := by
  have hpos : Ioi (0 : ℝ) ⊆ (fun s : ℝ => (s : ℂ) * exp ((θ : ℂ) * I)) ⁻¹'
      frontier (sector θ) := by
    intro s hs
    refine ⟨closure_mono sdiff_subset (topTail_mem_frontier_roundedSector hs hθ hθ' le_rfl).1, ?_⟩
    intro hi
    have hm : (s : ℂ) * exp ((θ : ℂ) * I) ∈ sector θ := by
      simpa only [(isOpen_sector θ).interior_eq] using hi
    have hn := (polar_mem_sector_iff hs ⟨hθ.le, le_rfl⟩ hθ').mp hm
    exact (lt_irrefl θ) hn.2
  have hc := closure_minimal hpos (isClosed_frontier.preimage
    (Complex.continuous_ofReal.mul_const (exp ((θ : ℂ) * I))))
  rw [closure_Ioi] at hc
  exact hc hr

lemma frontier_sector_inter_tip_eq_shortRays {ε θ : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    frontier (sector θ) ∩ sectorTip ε θ = shortRays ε θ := by
  apply Subset.antisymm (frontier_sector_inter_tip_subset_shortRays hε hθ)
  intro z hz
  rcases hz with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · refine ⟨bottom_mem_frontier_sector hθ hθ' hr.1, ?_⟩
    have hm := (polar_mem_sectorTip_iff hε hθ hθ' hr.1 (by simp : (0 : ℝ) ∈ Icc 0 1)).mpr
      (show r ≤ ε * radialProfile 0 by simpa [radialProfile] using hr.2)
    norm_num [smoothStep] at hm
    exact hm
  · refine ⟨top_mem_frontier_sector hθ hθ' hr.1, ?_⟩
    have hm := (polar_mem_sectorTip_iff hε hθ hθ' hr.1 (by simp : (1 : ℝ) ∈ Icc 0 1)).mpr
      (show r ≤ ε * radialProfile 1 by simpa [radialProfile] using hr.2)
    norm_num [smoothStep] at hm
    exact hm

lemma bottom_mem_frontier_roundedSector_iff {ε θ r : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) (hr : 0 ≤ r) :
    (r : ℂ) ∈ frontier (roundedSector ε θ) ↔ ε ≤ r := by
  refine ⟨?_, bottomTail_mem_frontier_roundedSector hε hθ hθ'⟩
  intro hz
  by_cases hr0 : r = 0
  · subst r
    exact False.elim (zero_not_mem_closure_roundedSector hε hθ (by simpa using hz.1))
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  obtain ⟨s, t, ht, hst, he⟩ := mem_closure_roundedSector_polar hε hθ hθ' hz.1
  have hsp : 0 < s := (mul_pos hε (radialProfile_pos ht)).trans_le hst
  have ha := angle_eq_of_polar_eq hrp hsp ⟨le_rfl, hθ.le⟩
    ⟨mul_nonneg hθ.le (smoothStep_mem_Icc ht).1,
      by nlinarith [(smoothStep_mem_Icc ht).2]⟩ hθ'
    (show (r : ℂ) * exp ((0 : ℂ) * I) =
      (s : ℂ) * exp ((θ * smoothStep t : ℝ) * I) by simpa using he)
  have hstep : smoothStep t = 0 := by nlinarith
  have ht0 : t = 0 := smoothStep_strictMonoOn.injOn ht (by simp) (by simpa using hstep)
  have hsr : s = r := by
    subst t
    simpa [smoothStep] using congrArg Complex.re he.symm
  simpa [ht0, hsr, radialProfile] using hst

lemma top_mem_frontier_roundedSector_iff {ε θ r : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) (hr : 0 ≤ r) :
    (r : ℂ) * exp ((θ : ℂ) * I) ∈ frontier (roundedSector ε θ) ↔ ε ≤ r := by
  refine ⟨?_, topTail_mem_frontier_roundedSector hε hθ hθ'⟩
  intro hz
  by_cases hr0 : r = 0
  · subst r
    exact False.elim (zero_not_mem_closure_roundedSector hε hθ (by simpa using hz.1))
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  obtain ⟨s, t, ht, hst, he⟩ := mem_closure_roundedSector_polar hε hθ hθ' hz.1
  have hsp : 0 < s := (mul_pos hε (radialProfile_pos ht)).trans_le hst
  have ha := angle_eq_of_polar_eq hrp hsp ⟨hθ.le, le_rfl⟩
    ⟨mul_nonneg hθ.le (smoothStep_mem_Icc ht).1,
      by nlinarith [(smoothStep_mem_Icc ht).2]⟩ hθ' he
  have hstep : smoothStep t = 1 := by nlinarith
  have ht1 : t = 1 := smoothStep_strictMonoOn.injOn ht (by simp) (by simpa using hstep)
  have hsr : s = r := by
    have hn := congrArg norm he
    rw [norm_polar hr, norm_polar hsp.le] at hn
    exact hn.symm
  simpa [ht1, hsr, radialProfile] using hst

lemma removed_sector_frontier_eq_open_shortRays {ε θ : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    frontier (sector θ) \ frontier (roundedSector ε θ) =
      (fun r : ℝ => (r : ℂ)) '' Ico 0 ε ∪
      (fun r : ℝ => (r : ℂ) * exp ((θ : ℂ) * I)) '' Ico 0 ε := by
  ext z
  constructor
  · intro hz
    rcases removed_sector_frontier_subset_shortRays hε hθ hz with
      ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · exact Or.inl ⟨r, ⟨hr.1, lt_of_not_ge (fun h => hz.2
        ((bottom_mem_frontier_roundedSector_iff hε hθ hθ' hr.1).mpr h))⟩, rfl⟩
    · exact Or.inr ⟨r, ⟨hr.1, lt_of_not_ge (fun h => hz.2
        ((top_mem_frontier_roundedSector_iff hε hθ hθ' hr.1).mpr h))⟩, rfl⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨bottom_mem_frontier_sector hθ hθ' hr.1, fun hz =>
        (not_le_of_gt hr.2) ((bottom_mem_frontier_roundedSector_iff hε hθ hθ' hr.1).mp hz)⟩
    · exact ⟨top_mem_frontier_sector hθ hθ' hr.1, fun hz =>
        (not_le_of_gt hr.2) ((top_mem_frontier_roundedSector_iff hε hθ hθ' hr.1).mp hz)⟩



open CircularExhaustion CircularCornerRounding Complex

/-- Exact original-frontier removal for the literal finite disjoint chart
surgery. Every removed original point lies on one literal inverse-chart ray
with radial parameter in [0,ε), and conversely. -/
lemma chart_surgery_removed_frontier_eq {U : Set ℂ} {J : Finset ℂ}
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hθ : ∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi)
    (hside : ∀ p ∈ J, (e p).IsImage U (sector (θ p)))
    (hdisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source)
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target) :
    let V := U \ ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
    frontier U \ frontier V = ⋃ p ∈ J, (e p).symm ''
      ((fun r : ℝ => (r : ℂ)) '' Ico 0 ε ∪
        (fun r : ℝ => (r : ℂ) * exp ((θ p : ℂ) * I)) '' Ico 0 ε) := by
  let K := ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
  have hK : IsClosed K := (J.isCompact_biUnion fun p hp =>
    (isCompact_sectorTip ε (θ p)).image_of_continuousOn
      ((e p).symm.continuousOn.mono (htip p hp))).isClosed
  have hlocal := chart_surgery_isImage e θ ε hside hdisj htip
  apply Subset.antisymm
  · intro z hz
    have hzK : z ∈ K := (closed_removal_locality (U := U) hK).2.1 hz
    obtain ⟨p, hpJ, w, hw, he⟩ := mem_iUnion₂.mp hzK
    have hzs : z ∈ (e p).source := he ▸ (e p).map_target (htip p hpJ hw)
    have hold : e p z ∈ frontier (sector (θ p)) :=
      ((hside p hpJ).frontier hzs).mpr hz.1
    have hnew : e p z ∉ frontier (roundedSector ε (θ p)) :=
      fun h => hz.2 (((hlocal p hpJ).frontier hzs).mp h)
    have hshort := (Set.ext_iff.mp
      (removed_sector_frontier_eq_open_shortRays hε (hθ p hpJ).1 (hθ p hpJ).2) (e p z)).mp
      ⟨hold, hnew⟩
    exact mem_iUnion₂.mpr ⟨p, hpJ, e p z, hshort, (e p).left_inv hzs⟩
  · intro z hz
    obtain ⟨p, hpJ, w, hw, rfl⟩ := mem_iUnion₂.mp hz
    have hremoved : w ∈ frontier (sector (θ p)) \ frontier (roundedSector ε (θ p)) :=
      (Set.ext_iff.mp
        (removed_sector_frontier_eq_open_shortRays hε (hθ p hpJ).1 (hθ p hpJ).2) w).mpr hw
    have hwshort : w ∈ shortRays ε (θ p) := by
      rcases hw with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · exact Or.inl ⟨r, ⟨hr.1, hr.2.le⟩, rfl⟩
      · exact Or.inr ⟨r, ⟨hr.1, hr.2.le⟩, rfl⟩
    have hwtip : w ∈ sectorTip ε (θ p) :=
      ((Set.ext_iff.mp
        (frontier_sector_inter_tip_eq_shortRays hε (hθ p hpJ).1 (hθ p hpJ).2) w).mpr hwshort).2
    have hwt : w ∈ (e p).target := htip p hpJ hwtip
    have hzs : (e p).symm w ∈ (e p).source := (e p).map_target hwt
    have her : e p ((e p).symm w) = w := (e p).right_inv hwt
    refine ⟨((hside p hpJ).frontier hzs).mp (by simpa only [her] using hremoved.1), ?_⟩
    intro hznew
    apply hremoved.2
    have hh := ((hlocal p hpJ).frontier hzs).mpr hznew
    simpa only [her] using hh



open CircularExhaustion CircularCornerRounding

/-- An embedded regular model frontier pulls back to regular local extensions
of any displayed curve that agrees with its literal parameter on the closed
interval. The local extension is the actual inverse-chart/model composition. -/
theorem local_regular_extensions_of_model
    {V S : Set ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    (hside : e.IsImage V S)
    (he : ContDiffOn ℝ 1 e e.source)
    (hei : ContDiffOn ℝ 1 e.symm e.target)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfemb : Topology.IsEmbedding f)
    (hfregular : ∀ t : ℝ, deriv f t ≠ 0)
    (hfront : frontier S = Set.range f)
    {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : ∀ t ∈ Icc a b, γ t = e.symm (f t))
    (htarget : ∀ t ∈ Icc a b, f t ∈ e.target) :
    HasLocalRegularExtensions V γ a b := by
  intro t ht
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (hf.continuous.continuousAt (e.open_target.mem_nhds (htarget t ht)))
  let I : Set ℝ := Ioo (t - δ) (t + δ)
  have hI : IsOpen I := isOpen_Ioo
  have htI : t ∈ I := by constructor <;> linarith
  have hmap : ∀ s ∈ I, f s ∈ e.target := by
    intro s hs
    apply hδsub
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨N, hN, hpre⟩ := hfemb.isInducing.isOpen_iff.mp hI
  let W : Set ℂ := e.symm '' (N ∩ e.target)
  let η : ℝ → ℂ := e.symm ∘ f
  have hW : IsOpen W := e.symm.isOpen_image_of_subset_source
    (hN.inter e.open_target) inter_subset_right
  have hηsource : ∀ s ∈ I, η s ∈ e.source := fun s hs => e.map_target (hmap s hs)
  have hηinverse : ∀ s ∈ I, e (η s) = f s := fun s hs => e.right_inv (hmap s hs)
  have hηsmooth : ContDiffOn ℝ 1 η I := hei.comp hf.contDiffOn hmap
  have hηregular : ∀ s ∈ I, deriv η s ≠ 0 := by
    intro s hs hzero
    have hηd := (hηsmooth.contDiffAt (hI.mem_nhds hs)).differentiableAt (by norm_num)
    have hed := (he.contDiffAt (e.open_source.mem_nhds (hηsource s hs))).differentiableAt (by norm_num)
    have hd := hed.hasFDerivAt.comp_hasDerivAt s hηd.hasDerivAt
    have heq : f =ᶠ[𝓝 s] (e ∘ η) :=
      Filter.mem_of_superset (hI.mem_nhds hs) (fun u hu => (hηinverse u hu).symm)
    have hfd := hd.congr_of_eventuallyEq heq
    have hderiv := hfd.unique ((hf.differentiable (by norm_num) s).hasDerivAt)
    rw [hzero, map_zero] at hderiv
    exact hfregular s hderiv.symm
  have hηemb : Topology.IsEmbedding (fun s : I => η s) := by
    have hfI : Topology.IsEmbedding (fun s : I => f s) :=
      hfemb.comp Topology.IsEmbedding.subtypeVal
    have hfT : Topology.IsEmbedding (fun s : I => (⟨f s, hmap s s.2⟩ : e.target)) :=
      hfI.codRestrict e.target (fun s => hmap s s.2)
    exact e.symm.isEmbedding_restrict.comp hfT
  refine ⟨δ, W, η, hδ, hW, ?_, hηsmooth, hηregular, ?_, hηemb, ?_⟩
  · rw [hγ t ht]
    refine ⟨f t, ⟨?_, htarget t ht⟩, rfl⟩
    change t ∈ f ⁻¹' N
    rw [hpre]
    exact htI
  · intro s hs
    exact (hγ s hs.2).symm
  · ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨(hside.frontier (hηsource s hs)).mp ?_, ?_⟩
      · rw [hηinverse s hs, hfront]
        exact ⟨s, rfl⟩
      · refine ⟨f s, ⟨?_, hmap s hs⟩, rfl⟩
        change s ∈ f ⁻¹' N
        rw [hpre]
        exact hs
    · rintro ⟨hzf, y, ⟨hyN, hyT⟩, rfl⟩
      have hyf : y ∈ frontier S := by
        have hh := (hside.frontier (e.map_target hyT)).mpr hzf
        simpa only [e.right_inv hyT] using hh
      rw [hfront] at hyf
      obtain ⟨s, rfl⟩ := hyf
      refine ⟨s, ?_, rfl⟩
      change s ∈ I
      rw [← hpre]
      exact hyN

/-- The literal pulled-back rounding arc has C1 regular extensions through
both endpoints, furnished by the actual joinedRounding curve. -/
theorem pullback_roundingArc_hasLocalRegularExtensions
    {V : Set ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    (hside : e.IsImage V (roundedSector ε θ))
    (he : ContDiffOn ℝ 1 e e.source)
    (hei : ContDiffOn ℝ 1 e.symm e.target)
    (htarget : ∀ t ∈ Icc (0 : ℝ) 1, roundingArc ε θ t ∈ e.target) :
    HasLocalRegularExtensions V (fun t => e.symm (roundingArc ε θ t)) 0 1 := by
  apply local_regular_extensions_of_model e hside he hei
    (contDiff_joinedRounding ε θ) (isClosedEmbedding_joinedRounding hε hθ hθ').isEmbedding
    (joinedRounding_regular hε hθ) (frontier_roundedSector_eq_range hε hθ hθ')
  · intro t ht
    congr 1
    simp only [joinedRounding]
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst t
      simp [bottomRay, roundingArc_endpoints]
    · simp only [Set.piecewise, mem_Iic, not_le.mpr h, ite_false, ht.2, ite_true]
  · intro t ht
    have heq : joinedRounding ε θ t = roundingArc ε θ t := by
      simp only [joinedRounding]
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst t
        simp [bottomRay, roundingArc_endpoints]
      · simp only [Set.piecewise, mem_Iic, not_le.mpr h, ite_false, ht.2, ite_true]
    rw [heq]
    exact htarget t ht


/-- Each literal inserted curve for the finite surgery has its required local
regular extensions, including both new joins. -/
theorem surgery_inserted_hasLocalRegularExtensions
    {U : Set ℂ} {J : Finset ℂ} {θ : ℂ → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {R : ℝ} {L : ℝ≥0}
    (h : UniformCharts U J θ e R L) {ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ∀ p ∈ J, HasLocalRegularExtensions (surgeryDomain U J e θ ε)
      (fun t => (e p).symm (roundingArc ε (θ p) t)) 0 1 := by
  obtain ⟨_, _, hθ, hside, hc, _, hdisj, hLip⟩ := h
  have htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target := by
    intro p hp
    exact (sectorTip_subset_closedBall hε).trans
      ((closedBall_subset_closedBall hεR.le).trans (hLip p hp).1)
  have hmodel := chart_surgery_isImage e θ ε hside hdisj htip
  intro p hp
  apply pullback_roundingArc_hasLocalRegularExtensions (e p) hε
    (hθ p hp).1 (hθ p hp).2 (hmodel p hp) (hc p hp).1 (hc p hp).2
  intro t ht
  apply htip p hp
  exact roundingArc_image_subset_sectorTip ε (θ p) ⟨t, ht, rfl⟩




lemma speed_integrable_of_contDiffOn_open {η : ℝ → ℂ} {lo hi : ℝ} {S : Set ℝ}
    (hlohi : lo ≤ hi) (hS : IsOpen S) (hη : ContDiffOn ℝ 1 η S)
    (hIS : Icc lo hi ⊆ S) :
    IntervalIntegrable (fun s => ‖deriv η s‖) volume lo hi := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hlohi]
  intro s hs
  have hc := (hη.contDiffAt (hS.mem_nhds (hIS hs))).continuousAt_fderiv (by norm_num)
  simpa only [norm_deriv_eq_norm_fderiv] using hc.norm.continuousWithinAt

lemma deriv_congr_comp_on_interior {γ η : ℝ → ℂ} {φ : ℝ → ℝ} {a b t : ℝ}
    (hγ : EqOn γ (η ∘ φ) (Icc a b)) (ht : t ∈ Ioo a b)
    (hη : DifferentiableAt ℝ η (φ t)) (hφ : DifferentiableAt ℝ φ t) :
    deriv γ t = deriv φ t • deriv η (φ t) := by
  have heq : γ =ᶠ[𝓝 t] (η ∘ φ) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact hγ hs
  exact heq.deriv_eq.trans (deriv.scomp t hη hφ)

lemma unsigned_speed_substitution {γ η : ℝ → ℂ} {φ : ℝ → ℝ}
    {a b lo hi : ℝ} {T S : Set ℝ} (hab : a ≤ b) (hlohi : lo ≤ hi)
    (hT : IsOpen T) (hφ : ContDiffOn ℝ 1 φ T) (hIT : Icc a b ⊆ T)
    (hS : IsOpen S) (hη : ContDiffOn ℝ 1 η S) (hIS : Icc lo hi ⊆ S)
    (hm : (MonotoneOn φ (Icc a b) ∧ φ a = lo ∧ φ b = hi) ∨
      (AntitoneOn φ (Icc a b) ∧ φ a = hi ∧ φ b = lo))
    (hγ : EqOn γ (η ∘ φ) (Icc a b)) :
    IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b ∧
      (∫ t in a..b, ‖deriv γ t‖) = ∫ s in lo..hi, ‖deriv η s‖ := by
  have hcont : ContinuousOn φ [[a, b]] := by
    simpa only [uIcc_of_le hab] using hφ.continuousOn.mono hIT
  have hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt φ (deriv φ t) t := by
    intro t ht
    have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
    exact ((hφ.contDiffAt (hT.mem_nhds (hIT (Ioo_subset_Icc_self ht')))).differentiableAt
      (by norm_num)).hasDerivAt
  have hspeed := speed_integrable_of_contDiffOn_open hlohi hS hη hIS
  rcases hm with ⟨hmono, hfirst, hlast⟩ | ⟨hanti, hfirst, hlast⟩
  · have hmaps : MapsTo φ (Icc a b) (Icc lo hi) := by
      intro t ht
      exact ⟨hfirst ▸ hmono (left_mem_Icc.mpr hab) ht ht.1,
        hlast ▸ hmono ht (right_mem_Icc.mpr hab) ht.2⟩
    have hn : ∀ t ∈ Ioo (min a b) (max a b), 0 ≤ deriv φ t := by
      intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)]
      exact hmono.derivWithin_nonneg
    have hweight : IntervalIntegrable
        (fun t => deriv φ t • ((fun s => ‖deriv η s‖) ∘ φ) t) volume a b := by
      apply (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg hcont hd hn).2
      simpa only [hfirst, hlast] using hspeed
    have heq : EqOn (fun t => deriv φ t • ((fun s => ‖deriv η s‖) ∘ φ) t)
        (fun t => ‖deriv γ t‖) (Ioo a b) := by
      intro t ht
      have ht' : t ∈ Ioo (min a b) (max a b) := by
        simpa only [min_eq_left hab, max_eq_right hab] using ht
      dsimp only
      rw [deriv_congr_comp_on_interior hγ ht
        ((hη.contDiffAt (hS.mem_nhds (hIS (hmaps (Ioo_subset_Icc_self ht))))).differentiableAt
          (by norm_num)) ((hd t ht').differentiableAt)]
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hn t ht'),
        Function.comp_apply, smul_eq_mul]
    refine ⟨hweight.congr_uIoo (by simpa only [uIoo_of_le hab] using heq), ?_⟩
    calc
      (∫ t in a..b, ‖deriv γ t‖) =
          ∫ t in a..b, deriv φ t • ((fun s => ‖deriv η s‖) ∘ φ) t :=
        (intervalIntegral.integral_congr_Ioo_of_le hab heq).symm
      _ = _ := by
        simpa only [hfirst, hlast] using
          (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
            (g := fun s => ‖deriv η s‖) hcont hd hn)
  · have hmaps : MapsTo φ (Icc a b) (Icc lo hi) := by
      intro t ht
      exact ⟨hlast ▸ hanti ht (right_mem_Icc.mpr hab) ht.2,
        hfirst ▸ hanti (left_mem_Icc.mpr hab) ht ht.1⟩
    have hn : ∀ t ∈ Ioo (min a b) (max a b), deriv φ t ≤ 0 := by
      intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)]
      exact hanti.derivWithin_nonpos
    have hweight : IntervalIntegrable
        (fun t => deriv φ t • ((fun s => ‖deriv η s‖) ∘ φ) t) volume a b := by
      apply (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonpos hcont hd hn).2
      simpa only [hfirst, hlast] using hspeed.symm
    have heq : EqOn (fun t => -(deriv φ t • ((fun s => ‖deriv η s‖) ∘ φ) t))
        (fun t => ‖deriv γ t‖) (Ioo a b) := by
      intro t ht
      have ht' : t ∈ Ioo (min a b) (max a b) := by
        simpa only [min_eq_left hab, max_eq_right hab] using ht
      dsimp only
      rw [deriv_congr_comp_on_interior hγ ht
        ((hη.contDiffAt (hS.mem_nhds (hIS (hmaps (Ioo_subset_Icc_self ht))))).differentiableAt
          (by norm_num)) ((hd t ht').differentiableAt)]
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonpos (hn t ht'),
        Function.comp_apply, smul_eq_mul, neg_mul]
    refine ⟨hweight.neg.congr_uIoo (by
      intro t ht
      exact heq (by simpa only [uIoo_of_le hab] using ht)), ?_⟩
    calc
      (∫ t in a..b, ‖deriv γ t‖) =
          ∫ t in a..b, -(deriv φ t • ((fun s => ‖deriv η s‖) ∘ φ) t) :=
        (intervalIntegral.integral_congr_Ioo_of_le hab heq).symm
      _ = -(∫ t in a..b, deriv φ t • ((fun s => ‖deriv η s‖) ∘ φ) t) :=
        intervalIntegral.integral_neg
      _ = -(∫ s in hi..lo, ‖deriv η s‖) := by
        congr 1
        simpa only [hfirst, hlast] using
          (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
            (g := fun s => ‖deriv η s‖) hcont hd hn)
      _ = _ := (intervalIntegral.integral_symm hi lo).symm


lemma unsigned_speed_ray_substitution {γ : ℝ → ℂ} {g : ℂ → ℂ} {φ : ℝ → ℝ}
    {a b lo hi ε R : ℝ} {ξ : ℂ} {T : Set ℝ}
    (hab : a ≤ b) (hlohi : lo ≤ hi) (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hε : 0 < ε) (hεR : ε < R) (hξ : ‖ξ‖ ≤ 1)
    (hg : ContDiffOn ℝ 1 g (ball (0 : ℂ) R))
    (hT : IsOpen T) (hφ : ContDiffOn ℝ 1 φ T) (hIT : Icc a b ⊆ T)
    (hm : (MonotoneOn φ (Icc a b) ∧ φ a = lo ∧ φ b = hi) ∨
      (AntitoneOn φ (Icc a b) ∧ φ a = hi ∧ φ b = lo))
    (hγ : ∀ t ∈ Icc a b, γ t = g ((ε * φ t) • ξ)) :
    IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b ∧
      (∫ t in a..b, ‖deriv γ t‖) =
        ∫ s in lo..hi, ‖deriv (fun s : ℝ => g ((ε * s) • ξ)) s‖ := by
  let μ : ℝ → ℂ := fun s => (ε * s) • ξ
  let S : Set ℝ := μ ⁻¹' ball (0 : ℂ) R
  have hμ : ContDiff ℝ 1 μ := by
    have hscale : ContDiff ℝ 1 (fun s : ℝ => ε * s) := contDiff_const.mul contDiff_id
    exact hscale.smul contDiff_const
  have hS : IsOpen S := isOpen_ball.preimage hμ.continuous
  have hη : ContDiffOn ℝ 1 (g ∘ μ) S :=
    hg.comp hμ.contDiffOn (fun _ hs => hs)
  have hIS : Icc lo hi ⊆ S := by
    intro s hs
    have hs0 : 0 ≤ s := hlo.trans hs.1
    have hs1 : s ≤ 1 := hs.2.trans hhi
    have hnorm : ‖μ s‖ ≤ ε := by
      calc
        ‖μ s‖ = (ε * s) * ‖ξ‖ := by
          simp only [μ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε.le hs0)]
        _ ≤ ε * s := mul_le_of_le_one_right (mul_nonneg hε.le hs0) hξ
        _ ≤ ε := mul_le_of_le_one_right hε.le hs1
    simpa only [S, mem_preimage, mem_ball, dist_zero_right] using hnorm.trans_lt hεR
  exact unsigned_speed_substitution hab hlohi hT hφ hIT hS hη hIS hm hγ

lemma deleted_curve_length_le {γ : ℝ → ℂ} {g : ℂ → ℂ} {φ : ℝ → ℝ}
    {a b lo hi ε R : ℝ} {ξ : ℂ} {L : NNReal} {T : Set ℝ}
    (hab : a ≤ b) (hlohi : lo ≤ hi) (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hε : 0 < ε) (hεR : ε < R) (hξ : ‖ξ‖ ≤ 1)
    (hg : ContDiffOn ℝ 1 g (ball (0 : ℂ) R))
    (hLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hT : IsOpen T) (hφ : ContDiffOn ℝ 1 φ T) (hIT : Icc a b ⊆ T)
    (hm : (MonotoneOn φ (Icc a b) ∧ φ a = lo ∧ φ b = hi) ∨
      (AntitoneOn φ (Icc a b) ∧ φ a = hi ∧ φ b = lo))
    (hγ : ∀ t ∈ Icc a b, γ t = g ((ε * φ t) • ξ)) :
    IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b ∧
      (∫ t in a..b, ‖deriv γ t‖) ≤ (L : ℝ) * ε * (hi - lo) := by
  have hsubst := unsigned_speed_ray_substitution hab hlohi hlo hhi hε hεR hξ hg hT hφ hIT hm hγ
  let μ : ℝ → ℂ := fun s => (ε * s) • ξ
  have hμ : ContDiff ℝ 1 μ := by
    have hscale : ContDiff ℝ 1 (fun s : ℝ => ε * s) := contDiff_const.mul contDiff_id
    exact hscale.smul contDiff_const
  have hnorm : ∀ s ∈ Icc lo hi, ‖μ s‖ < R := by
    intro s hs
    have hs0 : 0 ≤ s := hlo.trans hs.1
    have hs1 : s ≤ 1 := hs.2.trans hhi
    apply lt_of_le_of_lt _ hεR
    calc
      ‖μ s‖ = (ε * s) * ‖ξ‖ := by
        simp only [μ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε.le hs0)]
      _ ≤ ε * s := mul_le_of_le_one_right (mul_nonneg hε.le hs0) hξ
      _ ≤ ε := mul_le_of_le_one_right hε.le hs1
  have hspeed : ∀ s ∈ Icc lo hi, ‖deriv (g ∘ μ) s‖ ≤ (L : ℝ) * ε := by
    intro s hs
    have hgs := (hg.contDiffAt (isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_zero_right] using hnorm s hs))).differentiableAt (by norm_num)
    have hμderiv : HasDerivAt μ (ε • ξ) s := by
      simpa only [μ, mul_one, id_eq] using ((hasDerivAt_id s).const_mul ε).smul_const ξ
    rw [(hgs.hasFDerivAt.comp_hasDerivAt s hμderiv).deriv]
    have hLipBound : ‖fderiv ℝ g (μ s)‖ ≤ (L : ℝ) :=
      norm_fderiv_le_of_lipschitzOn ℝ
        (Filter.mem_of_superset (isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_zero_right] using hnorm s hs)) ball_subset_closedBall) hLip
    have hvel : ‖ε • ξ‖ ≤ ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      exact mul_le_of_le_one_right hε.le hξ
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul hLipBound hvel (norm_nonneg _) L.coe_nonneg)
  have hmodelInt : IntervalIntegrable (fun s => ‖deriv (g ∘ μ) s‖) volume lo hi := by
    let S : Set ℝ := μ ⁻¹' ball (0 : ℂ) R
    apply speed_integrable_of_contDiffOn_open hlohi (isOpen_ball.preimage hμ.continuous)
      (hg.comp hμ.contDiffOn (fun _ hs => hs))
    intro s hs
    simpa only [mem_preimage, mem_ball, dist_zero_right] using hnorm s hs
  refine ⟨hsubst.1, ?_⟩
  rw [hsubst.2]
  have hbnd := intervalIntegral.integral_mono_on hlohi hmodelInt
    (intervalIntegrable_const (c := (L : ℝ) * ε)) hspeed
  simpa only [μ, Function.comp_def, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hbnd




lemma finite_disjoint_interval_lengths_le {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ)
    (hlo : ∀ i ∈ s, 0 ≤ lo i) (horder : ∀ i ∈ s, lo i ≤ hi i)
    (hhi : ∀ i ∈ s, hi i ≤ 1)
    (hdisj : Set.PairwiseDisjoint (↑s) (fun i => Ioo (lo i) (hi i))) :
    (∑ i ∈ s, (hi i - lo i)) ≤ 1 := by
  have hsub : (⋃ i ∈ s, Ioo (lo i) (hi i)) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    exact ⟨(hlo i hi).trans_lt hx.1, hx.2.trans_le (hhi i hi)⟩
  calc
    (∑ i ∈ s, (hi i - lo i)) =
        ∑ i ∈ s, volume.real (Ioo (lo i) (hi i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Real.volume_real_Ioo_of_le (horder i hi)).symm
    _ = volume.real (⋃ i ∈ s, Ioo (lo i) (hi i)) :=
      (measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_Ioo)
        (fun _ _ => by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).symm
    _ ≤ volume.real (Ioo (0 : ℝ) 1) := measureReal_mono hsub
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    _ = 1 := by simp

lemma circle_speed_integral (c : ℂ) {r a b : ℝ} (hr : 0 < r) :
    (∫ t in a..b, ‖deriv (CircularExhaustion.arcParam c r) t‖) = r * (b - a) := by
  have hnorm : ∀ t : ℝ, ‖deriv (CircularExhaustion.arcParam c r) t‖ = r := by
    intro t
    change ‖deriv (circleMap c r) t‖ = r
    rw [(FiniteCircularArcs.circle_hasDerivAt c r t).deriv]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one, abs_of_pos hr]
  simp_rw [hnorm]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_comm]


namespace CutConversion

abbrev subdivision {a b : ℝ} (P : CircularAngularCuts.Subdivision a b) :
    AngularSubdivision a b where
  count := P.k
  node := P.node
  strict := P.strict
  first := P.first
  last := P.last
  keep := P.retained

abbrev change {U : Set ℂ} {J : Finset ℂ} {c : CircularAngularCuts.UniformCharts U J}
    {ε : ℝ} {z : ℂ} {r a b : ℝ} (d : CircularAngularCuts.RayChange c ε z r a b) :
    DeletedRayChange J c.chart c.angle ε z r a b where
  join := d.corner
  join_mem := d.corner_mem
  upper := d.upper
  lo := d.lo
  hi := d.hi
  lo_nonneg := d.lo_nonneg
  lo_lt_hi := d.lo_lt_hi
  hi_le_one := d.hi_le_one
  φ := d.scalar
  T := d.neighborhood
  open_T := d.open_neighborhood
  interval_subset := d.contains_interval
  smooth := d.smooth
  regular := fun t ht => d.regular t (d.contains_interval ht)
  monotone := d.monotonicity
  image := d.image_interval
  curve_eq := d.curve_eq

variable {U : Set ℂ} {J : Finset ℂ} {c : CircularAngularCuts.UniformCharts U J}
  {n : ℕ} {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ} {ε Cdel : ℝ}

abbrev subdivisions (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel) :=
  fun i => subdivision (h.cuts i)

abbrev changes (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel)
    (d : DeletedIndex (subdivisions h)) :
    DeletedRayChange J c.chart c.angle ε (center d.1) (radius d.1)
      ((subdivisions h d.1).node d.2.1.castSucc) ((subdivisions h d.1).node d.2.1.succ) :=
  change (h.deleted d.1 d.2.1 d.2.2)

lemma radial_cover (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel)
    (p : ℂ) (hp : p ∈ J) (upper : Bool) :
    (⋃ d : DeletedIndex (subdivisions h),
      ⋃ (_ : (changes h d).join = p), ⋃ (_ : (changes h d).upper = upper),
        Icc (changes h d).lo (changes h d).hi) = Icc (0 : ℝ) 1 := by
  ext s
  simp only [mem_iUnion]
  constructor
  · rintro ⟨d, _, _, hs⟩
    exact ⟨le_trans (changes h d).lo_nonneg hs.1, le_trans hs.2 (changes h d).hi_le_one⟩
  · intro hs
    obtain ⟨i, j, hj, hcorner, hupper, hs⟩ := h.radial_cover p hp upper s hs
    exact ⟨⟨i, ⟨j, hj⟩⟩, hcorner, hupper, hs⟩

lemma deletedIndex_ne_pair (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel)
    (d f : DeletedIndex (subdivisions h)) (hdf : d ≠ f) :
    (d.1, d.2.1.val) ≠ (f.1, f.2.1.val) := by
  intro heq
  apply hdf
  cases d with
  | mk i d =>
    cases f with
    | mk i' f =>
      obtain hii : i = i' := congrArg Prod.fst heq
      subst i'
      congr 1
      apply Subtype.ext
      apply Fin.ext
      exact congrArg Prod.snd heq

lemma radial_disjoint (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel)
    (d f : DeletedIndex (subdivisions h)) (hdf : d ≠ f)
    (hjoin : (changes h d).join = (changes h f).join)
    (hupper : (changes h d).upper = (changes h f).upper) :
    Disjoint (Ioo (changes h d).lo (changes h d).hi)
      (Ioo (changes h f).lo (changes h f).hi) :=
  h.radial_disjoint d.1 d.2.1 d.2.2 f.1 f.2.1 f.2.2
    (deletedIndex_ne_pair h d f hdf) hjoin hupper

lemma deleted_length (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel) :
    (∑ i, ∑ j : Fin (subdivisions h i).count, if (subdivisions h i).keep j then 0 else
      radius i * ((subdivisions h i).node j.succ - (subdivisions h i).node j.castSucc)) ≤
      Cdel * ε := h.deleted_length

end CutConversion

namespace DisplayConversion

abbrev circleData {U : Set ℂ} {n : ℕ} {center : Fin n → ℂ}
    {radius start stop sign : Fin n → ℝ}
    (hb : CircularBoundary U n center radius start stop sign) :
    CircularRetainedDisplay.CircleData U where
  n := n
  center := center
  radius := radius
  start := start
  stop := stop
  sign := sign
  bounds := hb.1
  signs := hb.2.1
  cover := hb.2.2.1
  injective := hb.2.2.2.2.1
  disjoint := hb.2.2.2.1
  side := hb.2.2.2.2.2

abbrev charts {U : Set ℂ} {J : Finset ℂ} (c : CircularAngularCuts.UniformCharts U J) :
    CircularRetainedDisplay.Charts U J where
  e := c.chart
  angle := c.angle
  radius := c.R
  lip := c.L
  radius_pos := c.radius_pos
  lip_pos := c.lipschitz_pos
  angles := c.angle_bounds
  side := c.side
  smooth := c.smooth
  normalized := c.normalized
  disjoint := c.disjoint
  target_ball := fun p hp => (c.target_bound p hp).1
  inverse_bound := fun p hp => (c.target_bound p hp).2

variable {U : Set ℂ} {J : Finset ℂ} {c : CircularAngularCuts.UniformCharts U J}
  {n : ℕ} {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ} {ε Cdel : ℝ}

abbrev cutData (hb : CircularBoundary U n center radius start stop sign)
    (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel) :
    CircularRetainedDisplay.CutData (circleData hb)
      (CircularRetainedDisplay.surgeryDomain (charts c) ε) where
  count := fun i => (h.cuts i).k
  node := fun i => (h.cuts i).node
  strict := fun i => (h.cuts i).strict
  first := fun i => (h.cuts i).first
  last := fun i => (h.cuts i).last
  retained := fun i => (h.cuts i).retained
  retained_frontier := h.retained_closed
  retained_cover := by
    ext z
    simp only [mem_iUnion, exists_prop]
    exact h.retained_cover z
  classification := h.open_classification
  unchanged_side := by
    intro i j hj t ht
    obtain ⟨W, hW, htW, heq, hside⟩ := h.retained_side i j hj t ht
    refine ⟨W, hW, htW, heq, ?_⟩
    intro z hzW
    have hzuv : z ∈ U ↔ z ∈ CircularAngularCuts.surgeryDomain c ε := by
      have hz := Set.ext_iff.mp heq z
      simpa only [mem_inter_iff, hzW, and_true] using hz
    exact hzuv.trans (hside z hzW)

abbrev retainedEquiv (hb : CircularBoundary U n center radius start stop sign)
    (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel) :
    CircularRetainedDisplay.RetainedIndex (cutData hb h) ≃
      RetainedIndex (CutConversion.subdivisions h) where
  toFun := fun q => ⟨q.val.1, ⟨q.val.2, q.property⟩⟩
  invFun := fun q => ⟨⟨q.1, q.2.1⟩, q.2.2⟩
  left_inv := fun q => by cases q; rfl
  right_inv := fun q => by cases q; rfl

abbrev displayIndex (hb : CircularBoundary U n center radius start stop sign)
    (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel)
    (D : CircularRetainedDisplay.RawDisplay (circleData hb) (charts c) ε (cutData hb h)) :
    Fin D.count ≃ RetainedIndex (CutConversion.subdivisions h) ⊕ {p : ℂ // p ∈ J} :=
  D.index.trans (Equiv.sumCongr (retainedEquiv hb h) (Equiv.refl _))

lemma retained_curve (hb : CircularBoundary U n center radius start stop sign)
    (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel)
    (D : CircularRetainedDisplay.RawDisplay (circleData hb) (charts c) ε (cutData hb h))
    (q : Fin D.count) (d : RetainedIndex (CutConversion.subdivisions h))
    (he : displayIndex hb h D q = Sum.inl d) :
    D.curve q = arcParam (center d.1) (radius d.1) ∧
    D.left q = (CutConversion.subdivisions h d.1).node d.2.1.castSucc ∧
    D.right q = (CutConversion.subdivisions h d.1).node d.2.1.succ := by
  have he' : D.index q = Sum.inl ⟨⟨d.1, d.2.1⟩, d.2.2⟩ := by
    apply (Equiv.sumCongr (retainedEquiv hb h) (Equiv.refl {p : ℂ // p ∈ J})).injective
    exact he
  refine ⟨?_, ?_, ?_⟩
  · rw [D.literal q, he']
  · rw [D.left_eq q, he']
  · rw [D.right_eq q, he']

lemma inserted_curve (hb : CircularBoundary U n center radius start stop sign)
    (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel)
    (D : CircularRetainedDisplay.RawDisplay (circleData hb) (charts c) ε (cutData hb h))
    (q : Fin D.count) (p : {p : ℂ // p ∈ J})
    (he : displayIndex hb h D q = Sum.inr p) :
    D.curve q = (fun t => (c.chart p).symm (roundingArc ε (c.angle p) t)) ∧
    D.left q = 0 ∧ D.right q = 1 := by
  have he' : D.index q = Sum.inr p := by
    apply (Equiv.sumCongr (retainedEquiv hb h) (Equiv.refl {p : ℂ // p ∈ J})).injective
    exact he
  refine ⟨?_, ?_, ?_⟩
  · rw [D.literal q, he']; rfl
  · rw [D.left_eq q, he']
  · rw [D.right_eq q, he']

/-- Assemble the complete parent partition from geometric angular cuts and
an independently proved raw retained/inserted display. -/
noncomputable def partitionAtOfCuts (hgeom : RoundingGeometry U J)
    (hb : CircularBoundary U n center radius start stop sign)
    (h : CircularAngularCuts.CutsAt c n center radius start stop sign ε Cdel)
    (hε : 0 < ε) (hεR : ε < c.R) {C : ℝ} (hC : Cdel ≤ C)
    (hspeed : ∀ p ∈ J, IntervalIntegrable
      (fun t => ‖deriv (fun s => (c.chart p).symm (roundingArc ε (c.angle p) s)) t‖)
      volume 0 1)
    (hadded : (∑ p ∈ J, ∫ t in (0 : ℝ)..1,
      ‖deriv (fun s => (c.chart p).symm (roundingArc ε (c.angle p) s)) t‖) ≤ C * ε) :
    SurgeryPartitionAt U J n center radius start stop sign c.chart c.angle C ε := by
  let D := (CircularRetainedDisplay.circular_retained_display U J hgeom
    (circleData hb) (charts c) ε hε hεR (cutData hb h)).some
  exact {
    subdivision := CutConversion.subdivisions h
    change := CutConversion.changes h
    radial_cover := CutConversion.radial_cover h
    radial_disjoint := CutConversion.radial_disjoint h
    retained_closed := h.retained_closed
    classify_interior := h.open_classification
    retained_side := fun i j t hj ht => h.retained_side i j hj t ht
    deleted_length := (CutConversion.deleted_length h).trans (mul_le_mul_of_nonneg_right hC hε.le)
    m := D.count
    index := displayIndex hb h D
    γ := D.curve
    a := D.left
    b := D.right
    retained_curve := retained_curve hb h D
    inserted_curve := inserted_curve hb h D
    ordered := D.positive
    regular_neighborhood := D.regular
    frontier_eq := D.cover
    injective_open := D.injective
    disjoint_open := D.disjoint
    extensions := D.extensions
    speed_integrable := hspeed
    added_length := hadded }

end DisplayConversion

/-- The chosen angular-cut charts satisfy the original uniform geometric
interface, with exactly the same global map and inverse functions. -/
lemma uniformCharts_of_angularCharts {U : Set ℂ} {J : Finset ℂ}
    (c : CircularAngularCuts.UniformCharts U J) :
    UniformCharts U J c.angle c.chart c.R c.L :=
  ⟨c.radius_pos, c.lipschitz_pos, c.angle_bounds, c.side, c.smooth,
    c.normalized, c.disjoint, c.target_bound⟩

/-- Literal finite chart surgery with subdivisions of the supplied original
circle arrays, regular closed endpoint extensions, and uniform actual speed
bounds for both the removed and inserted parameter pieces. -/
theorem circular_surgery_partition :
    Specs.D12Complex.Ch14.CircularSurgeryPartition.circular_surgery_partition_type := by
  intro U J hgeom n center radius start stop sign hb
  obtain ⟨c, ε₀, Cdel, hε₀, hε₀R, hCdel, _havoid, hcuts⟩ :=
    CircularAngularCuts.circular_angular_cuts U J hgeom n center radius start stop sign hb
  have hc := uniformCharts_of_angularCharts c
  let Cadd : ℝ := (c.L : ℝ) * (∑ p ∈ J, (Real.pi / 2 + 6 * c.angle p)) + 1
  obtain ⟨hCadd, hadded⟩ := inserted_curves_total_speed hc
  let C : ℝ := Cdel + Cadd
  refine ⟨c.angle, c.chart, c.R, c.L, C, ε₀, hc,
    add_pos hCdel hCadd, hε₀, hε₀R, ?_⟩
  intro ε hε hεsmall
  have hεR : ε < c.R := hεsmall.trans_le hε₀R
  obtain ⟨cuts⟩ := hcuts ε hε hεsmall
  obtain ⟨hV, hdef, hclass, _hparam⟩ :=
    CircularAngularCuts.literal_surgery_regular U J hgeom c ε hε hεR
  obtain ⟨hInt, hLen⟩ := hadded ε hε hεR
  refine ⟨hV, hdef, hclass, ?_⟩
  have hCdel' : Cdel ≤ C := le_add_of_nonneg_right hCadd.le
  have hCadd' : Cadd ≤ C := le_add_of_nonneg_left hCdel.le
  have hLen' : (∑ p ∈ J, ∫ t in (0 : ℝ)..1,
      ‖deriv (fun s => (c.chart p).symm (roundingArc ε (c.angle p) s)) t‖) ≤ C * ε :=
    hLen.trans (mul_le_mul_of_nonneg_right hCadd' hε.le)
  exact ⟨DisplayConversion.partitionAtOfCuts hgeom hb cuts hε hεR hCdel' hInt hLen'⟩

end D12Complex.CircularSurgeryPartition
