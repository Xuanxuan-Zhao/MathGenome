import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.MeanValueStrongPrinciple
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarmonicFoundation
import Mathlib.Analysis.Complex.Harmonic.MeanValue

noncomputable section
open Set Metric Complex
open scoped Topology

namespace D12Complex.MeanValueStrongPrinciple

/-- Candidate-owned export of the shared predicate, with the same definition. -/
abbrev LocalCircleMeanProperty :
    Specs.D12Complex.Ch13.MeanValueStrongPrinciple.LocalCircleMeanProperty_type :=
  _root_.D12Complex.LocalCircleMeanProperty

lemma circle_average_eq {U : Set ℂ} {u : ℂ → ℝ} (hu : HarmonicOn U u)
    {a : ℂ} {R : ℝ} (hR : 0 ≤ R) (hsub : closedBall a R ⊆ U) :
    Real.circleAverage u a R = u a := by
  apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
  rw [abs_of_nonneg hR]
  exact ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U u hu.1).mp hu).mono hsub

theorem circle_mean_value :
    Specs.D12Complex.Ch13.MeanValueStrongPrinciple.circle_mean_value_type := by
  intro U u hu a R hR hsub
  exact (circle_average_eq hu hR.le hsub).symm

theorem harmonic_local_circle_mean :
    Specs.D12Complex.Ch13.MeanValueStrongPrinciple.harmonic_local_circle_mean_type := by
  intro U u hu a ha
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hu.1 a ha
  refine ⟨ρ / 2, half_pos hρ, ?_, fun r hr hrρ => ?_⟩
  · exact (closedBall_subset_ball (by linarith)).trans hsub
  · exact circle_average_eq hu hr.le ((closedBall_subset_ball (by linarith)).trans hsub)

/-- Equality in the circle average upper bound forces equality everywhere on
that circle. Continuity rules out a strict deficit even at an endpoint of
the angular parameter interval. -/
lemma eq_on_circle_of_average_eq {u : ℂ → ℝ} {a : ℂ} {r M : ℝ}
    (hr : 0 ≤ r) (hc : ContinuousOn u (sphere a r))
    (hle : ∀ z ∈ sphere a r, u z ≤ M)
    (heq : Real.circleAverage u a r = M) :
    ∀ z ∈ sphere a r, u z = M := by
  have hmap (t : ℝ) : circleMap a r t ∈ sphere a r := circleMap_mem_sphere a hr t
  have hcont : ContinuousOn (fun t => u (circleMap a r t)) (Icc 0 (2 * Real.pi)) :=
    hc.comp (continuous_circleMap a r).continuousOn (fun t _ => hmap t)
  intro z hz
  apply le_antisymm (hle z hz)
  by_contra hn
  have hlt : u z < M := lt_of_not_ge hn
  have hz' : z ∈ circleMap a r '' Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc, abs_of_nonneg hr]
    exact hz
  obtain ⟨t, ht, rfl⟩ := hz'
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    Real.two_pi_pos hcont continuousOn_const
    (fun t _ => hle _ (hmap t)) ⟨t, ⟨ht.1.le, ht.2⟩, hlt⟩
  have := mul_lt_mul_of_pos_left hi (inv_pos.mpr Real.two_pi_pos)
  change (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..2 * Real.pi, u (circleMap a r t)) < _ at this
  change (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..2 * Real.pi, u (circleMap a r t)) = M at heq
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
  rw [← mul_assoc, inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul, heq] at this
  exact lt_irrefl M this

/-- The set of maximizers contains a disk about each of its points. -/
lemma maximum_locally_constant {U : Set ℂ} {u : ℂ → ℝ}
    (hc : ContinuousOn u U) (hm : LocalCircleMeanProperty U u)
    {a : ℂ} (ha : a ∈ U) (hmax : ∀ z ∈ U, u z ≤ u a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball a ρ ⊆ U ∧ ∀ z ∈ ball a ρ, u z = u a := by
  obtain ⟨ρ, hρ, hsub, hmean⟩ := hm a ha
  refine ⟨ρ, hρ, ball_subset_closedBall.trans hsub, fun z hz => ?_⟩
  by_cases he : z = a
  · simp [he]
  have hd : 0 < dist z a := dist_pos.mpr he
  have hs : sphere a (dist z a) ⊆ U :=
    (sphere_subset_closedBall.trans (closedBall_subset_closedBall (mem_ball.mp hz).le)).trans hsub
  exact eq_on_circle_of_average_eq hd.le (hc.mono hs)
    (fun w hw => hmax w (hs hw)) (hmean _ hd (mem_ball.mp hz)) z (by simp [dist_eq_norm])

theorem continuous_mean_maximum :
    Specs.D12Complex.Ch13.MeanValueStrongPrinciple.continuous_mean_maximum_type := by
  intro U u hU hc hm a ha hmax
  let V : Set ℂ := U ∩ {z | u z = u a}
  let W : Set ℂ := U ∩ {z | u z ≠ u a}
  have hVo : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨ρ, hρ, hsub, heq⟩ := maximum_locally_constant hc hm hz.1
      (fun w hw => (hmax w hw).trans_eq hz.2.symm)
    apply Filter.mem_of_superset (ball_mem_nhds z hρ)
    intro w hw
    exact ⟨hsub hw, (heq w hw).trans hz.2⟩
  have hWo : IsOpen W := hc.isOpen_inter_preimage hU.2.1 isOpen_ne
  have hVW : Disjoint V W := disjoint_left.mpr (fun _ hv hw => hw.2 hv.2)
  have hcover : U ⊆ V ∪ W := by
    intro z hz
    rcases eq_or_ne (u z) (u a) with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  have hsub := hU.2.2.subset_left_of_subset_union hVo hWo hVW hcover
    (show (U ∩ V).Nonempty from ⟨a, ha, ha, rfl⟩)
  exact fun z hz => (hsub hz).2

theorem continuous_mean_minimum :
    Specs.D12Complex.Ch13.MeanValueStrongPrinciple.continuous_mean_minimum_type := by
  intro U u hU hc hm a ha hmin
  have hmneg : LocalCircleMeanProperty U (fun z => -u z) := by
    intro z hz
    obtain ⟨ρ, hρ, hsub, hmean⟩ := hm z hz
    refine ⟨ρ, hρ, hsub, fun r hr hrρ => ?_⟩
    simpa [Real.circleAverage] using congrArg Neg.neg (hmean r hr hrρ)
  have heq := continuous_mean_maximum U (fun z => -u z) hU hc.neg hmneg a ha
    (fun z hz => neg_le_neg (hmin z hz))
  intro z hz
  exact neg_injective (heq z hz)

theorem harmonic_maximum :
    Specs.D12Complex.Ch13.MeanValueStrongPrinciple.harmonic_maximum_type := by
  intro U u hU hu
  exact continuous_mean_maximum U u hU hu.2.1.continuousOn (harmonic_local_circle_mean U u hu)

theorem harmonic_minimum :
    Specs.D12Complex.Ch13.MeanValueStrongPrinciple.harmonic_minimum_type := by
  intro U u hU hu
  exact continuous_mean_minimum U u hU hu.2.1.continuousOn (harmonic_local_circle_mean U u hu)

end D12Complex.MeanValueStrongPrinciple
