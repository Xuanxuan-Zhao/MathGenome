import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.SubharmonicDefinition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.DiskDirichlet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.MeanValueStrongPrinciple
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric Complex InnerProductSpace
open scoped Topology

namespace D12Complex.SubharmonicDefinition

/- Candidate-owned exports of the canonical definitions used by downstream Specs. -/
abbrev diskPoissonExtension := _root_.D12Complex.diskPoissonExtension
abbrev SubharmonicOn := _root_.D12Complex.SubharmonicOn
abbrev CircleSubmeanOn := _root_.D12Complex.CircleSubmeanOn
abbrev HarmonicComparisonOn := _root_.D12Complex.HarmonicComparisonOn
abbrev SuperharmonicOn := _root_.D12Complex.SuperharmonicOn

theorem diskPoissonExtension_solution :
    Specs.D12Complex.Ch14.SubharmonicDefinition.diskPoissonExtension_solution_type := by
  intro a R φ hR hφ
  let ψ : ℂ → ℝ := fun w => φ (a + w)
  have hψ : ContinuousOn ψ (sphere (0 : ℂ) R) := by
    apply hφ.comp (continuous_const.add continuous_id).continuousOn
    intro w hw
    simpa [dist_eq_norm] using hw
  have hP := DiskDirichlet.closedPoissonIntegral_solution R ψ hR hψ
  let P := DiskDirichlet.closedPoissonIntegral R ψ
  change ContinuousOn P (closedBall (0 : ℂ) R) ∧
    HarmonicOn (ball 0 R) P ∧ EqOn P ψ (sphere 0 R) ∧ _ at hP
  have hmap : MapsTo (fun z : ℂ => z - a) (closedBall a R) (closedBall 0 R) := by
    intro z hz
    simpa [dist_eq_norm] using hz
  refine ⟨hP.1.comp (continuous_id.sub continuous_const).continuousOn hmap, ?_, ?_⟩
  · exact HarmonicFoundation.harmonicOn_comp_holomorphic (ball 0 R) (ball a R)
      P (fun z => z - a) hP.2.1
      ⟨isOpen_ball, fun z _ => differentiableAt_id.sub_const a⟩
      (fun z hz => by simpa [dist_eq_norm] using hz)
  · intro z hz
    have he := hP.2.2.1 (show z - a ∈ sphere (0 : ℂ) R by
      simpa [dist_eq_norm] using hz)
    change DiskDirichlet.closedPoissonIntegral R ψ (z - a) = φ z
    simpa [ψ] using he

theorem diskPoissonExtension_center :
    Specs.D12Complex.Ch14.SubharmonicDefinition.diskPoissonExtension_center_type := by
  intro a R φ hR hφ
  obtain ⟨hc, hh, he⟩ := diskPoissonExtension_solution a R φ hR hφ
  have hn := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp hh
  have hm : Real.circleAverage (diskPoissonExtension a R φ) a R =
      diskPoissonExtension a R φ a :=
    (HarmonicContOnCl.mk_ball (by simpa [abs_of_pos hR] using hn)
      (by simpa [abs_of_pos hR] using hc)).circleAverage_eq
  calc
    diskPoissonExtension a R φ a = Real.circleAverage (diskPoissonExtension a R φ) a R := hm.symm
    _ = Real.circleAverage φ a R := Real.circleAverage_congr_sphere (by
      simpa [abs_of_pos hR] using he)

/-- At a maximum, the submean inequality is an equality on each small
circle. Continuity then forces the whole circle to have the maximum value. -/
lemma submean_maximum_locally_constant {U : Set ℂ} {u : ℂ → ℝ}
    (hU : IsOpen U) (hc : ContinuousOn u U)
    (hm : ∀ (b : ℂ) (r : ℝ), 0 < r → closedBall b r ⊆ U →
      u b ≤ Real.circleAverage u b r)
    {a : ℂ} (ha : a ∈ U) (hmax : ∀ z ∈ U, u z ≤ u a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball a ρ ⊆ U ∧ ∀ z ∈ ball a ρ, u z = u a := by
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hU a ha
  refine ⟨ρ, hρ, hsub, fun z hz => ?_⟩
  by_cases he : z = a
  · simp [he]
  have hd : 0 < dist z a := dist_pos.mpr he
  have hs : closedBall a (dist z a) ⊆ U :=
    (closedBall_subset_ball (mem_ball.mp hz)).trans hsub
  have hsc := sphere_subset_closedBall.trans hs
  have hu := (hc.mono hsc).circleIntegrable hd.le
  have hupper : Real.circleAverage u a (dist z a) ≤ u a :=
    Real.circleAverage_mono_on_of_le_circle hu (by
      simpa [abs_of_pos hd] using (fun w hw => hmax w (hsc hw)))
  exact MeanValueStrongPrinciple.eq_on_circle_of_average_eq hd.le (hc.mono hsc)
    (fun w hw => hmax w (hsc hw)) (le_antisymm hupper (hm a _ hd hs)) z (by simp [dist_eq_norm])

/-- A continuous submean function on a closed disk is bounded above by
its boundary bound. The positive maximum set would be compact and open
in the entire plane, which is impossible. -/
lemma submean_closedDisk_maximum {a : ℂ} {R M : ℝ} {u : ℂ → ℝ}
    (hc : ContinuousOn u (closedBall a R))
    (hm : ∀ (b : ℂ) (r : ℝ), 0 < r → closedBall b r ⊆ ball a R →
      u b ≤ Real.circleAverage u b r)
    (hb : ∀ z ∈ sphere a R, u z ≤ M) :
    ∀ z ∈ closedBall a R, u z ≤ M := by
  intro z hz
  by_contra hn
  have hMz : M < u z := lt_of_not_ge hn
  obtain ⟨b, hbC, hmax⟩ := (isCompact_closedBall a R).exists_isMaxOn ⟨z, hz⟩ hc
  have hMb : M < u b := hMz.trans_le (hmax hz)
  let K : Set ℂ := closedBall a R ∩ u ⁻¹' {u b}
  have hKc : IsCompact K :=
    (isCompact_closedBall a R).of_isClosed_subset
      (hc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton)
      inter_subset_left
  have hKi : K ⊆ ball a R := by
    intro w hw
    have heq : u w = u b := hw.2
    have hwi : dist w a < R := by
      by_contra hni
      have hws : w ∈ sphere a R := le_antisymm hw.1 (le_of_not_gt hni)
      have := hb w hws
      linarith
    exact hwi
  have hKo : IsOpen K := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    have heq : u w = u b := hw.2
    obtain ⟨ρ, hρ, hsub, he⟩ := submean_maximum_locally_constant isOpen_ball
      (hc.mono ball_subset_closedBall) hm (hKi hw)
      (fun v hv => (hmax (ball_subset_closedBall hv)).trans_eq heq.symm)
    apply Filter.mem_of_superset (ball_mem_nhds w hρ)
    intro v hv
    exact ⟨ball_subset_closedBall (hsub hv), (he v hv).trans heq⟩
  have heq : K = univ := (show IsClopen K from ⟨hKc.isClosed, hKo⟩).eq_univ
    ⟨b, hbC, rfl⟩
  exact NormedSpace.unbounded_univ ℝ ℂ (heq ▸ hKc.isBounded)

/-- Subtracting the harmonic test function reduces comparison to the
closed-disk submean maximum argument. -/
lemma circleSubmeanOn_harmonicComparisonOn {U : Set ℂ} {u : ℂ → ℝ}
    (hu : CircleSubmeanOn U u) : HarmonicComparisonOn U u := by
  refine ⟨hu.1, hu.2.1, ?_⟩
  intro a R _hR hsub h hc hh hb z hz
  have huc : ContinuousOn u (closedBall a R) := hu.2.1.mono hsub
  have hm : ∀ (b : ℂ) (r : ℝ), 0 < r → closedBall b r ⊆ ball a R →
      (u b - h b) ≤ Real.circleAverage (fun w => u w - h w) b r := by
    intro b r hr hbr
    have hs : sphere b r ⊆ closedBall a R :=
      (sphere_subset_closedBall.trans hbr).trans ball_subset_closedBall
    have hui := (huc.mono hs).circleIntegrable hr.le
    have hhi := (hc.mono hs).circleIntegrable hr.le
    rw [Real.circleAverage_fun_sub hui hhi,
      MeanValueStrongPrinciple.circle_average_eq hh hr.le hbr]
    exact sub_le_sub_right (hu.2.2 b r hr
      (hbr.trans (ball_subset_closedBall.trans hsub))) (h b)
  have hv := submean_closedDisk_maximum (huc.sub hc) hm
    (M := 0) (fun w hw => sub_nonpos.mpr (hb w hw)) z hz
  exact sub_nonpos.mp hv

lemma harmonicComparisonOn_subharmonicOn {U : Set ℂ} {u : ℂ → ℝ}
    (hu : HarmonicComparisonOn U u) : SubharmonicOn U u := by
  refine ⟨hu.1, hu.2.1, ?_⟩
  intro a R hR hsub
  obtain ⟨hc, hh, hb⟩ := diskPoissonExtension_solution a R u hR
    (hu.2.1.mono (sphere_subset_closedBall.trans hsub))
  exact hu.2.2 a R hR hsub (diskPoissonExtension a R u) hc hh
    (fun ζ hζ => (hb hζ).ge)

lemma subharmonicOn_circleSubmeanOn {U : Set ℂ} {u : ℂ → ℝ}
    (hu : SubharmonicOn U u) : CircleSubmeanOn U u := by
  refine ⟨hu.1, hu.2.1, ?_⟩
  intro a R hR hsub
  rw [← diskPoissonExtension_center a R u hR
    (hu.2.1.mono (sphere_subset_closedBall.trans hsub))]
  exact hu.2.2 a R hR hsub a (mem_closedBall_self hR.le)

theorem subharmonicOn_iff_circleSubmeanOn :
    Specs.D12Complex.Ch14.SubharmonicDefinition.subharmonicOn_iff_circleSubmeanOn_type := by
  intro U u
  exact ⟨subharmonicOn_circleSubmeanOn,
    fun hu => harmonicComparisonOn_subharmonicOn (circleSubmeanOn_harmonicComparisonOn hu)⟩

theorem subharmonicOn_iff_harmonicComparisonOn :
    Specs.D12Complex.Ch14.SubharmonicDefinition.subharmonicOn_iff_harmonicComparisonOn_type := by
  intro U u
  exact ⟨fun hu => circleSubmeanOn_harmonicComparisonOn (subharmonicOn_circleSubmeanOn hu),
    harmonicComparisonOn_subharmonicOn⟩

end D12Complex.SubharmonicDefinition
