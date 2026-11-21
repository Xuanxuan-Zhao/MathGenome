import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.LegendreLatticeShifts
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.ZetaSigmaQuasiperiods
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.EllipticResidueSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Legendre's relation is obtained from the residue theorem on a translated
fundamental cell with no lattice point on its frontier. Its unique interior
lattice point has residue one. Pairing the four oriented sides gives
`eta₁ * ω₂ - eta₂ * ω₁`. Integer iteration supplies both shift identities;
Legendre's relation converts the mixed exponential into `(-1)^(m*n)`.
The sigma identities hold even at its zeros, without division by sigma. -/

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.Ch22.LegendreLatticeShifts
open ZetaSigmaConvergence (lattice zeta sigma)
open ZetaSigmaQuasiperiods (eta)
open D12Complex.EllipticResidueSum
open D12Complex.WeakGoursat

/-- Iteration of an additive increment, with negative shifts included. -/
lemma additive_integer_shift {f : ℂ → ℂ} {ω η : ℂ} {S : AddSubgroup ℂ}
    (hω : ω ∈ S) (hf : ∀ z ∉ S, f (z + ω) = f z + η) (m : ℤ) :
    ∀ z ∉ S, f (z + (m : ℂ) * ω) = f z + (m : ℂ) * η := by
  have step (k : ℤ) (hk : ∀ z ∉ S, f (z + (k : ℂ) * ω) = f z + (k : ℂ) * η) :
      ∀ z ∉ S, f (z + ((k + 1 : ℤ) : ℂ) * ω) = f z + ((k + 1 : ℤ) : ℂ) * η := by
    intro z hz
    have hz' : z + (k : ℂ) * ω ∉ S := by
      intro h
      exact hz (by simpa using sub_mem h (S.zsmul_mem hω k))
    rw [Int.cast_add, Int.cast_one, add_mul, one_mul, ← add_assoc, hf _ hz', hk z hz]
    ring
  have back (k : ℤ) (hk : ∀ z ∉ S, f (z + (k : ℂ) * ω) = f z + (k : ℂ) * η) :
      ∀ z ∉ S, f (z + ((k - 1 : ℤ) : ℂ) * ω) = f z + ((k - 1 : ℤ) : ℂ) * η := by
    intro z hz
    have hz' : z - ω ∉ S := by
      intro h
      exact hz (by simpa using add_mem h hω)
    have h := hk (z - ω) hz'
    have hg := hf (z - ω) hz'
    rw [sub_add_cancel] at hg
    have he : z + ((k - 1 : ℤ) : ℂ) * ω = z - ω + (k : ℂ) * ω := by push_cast; ring
    rw [he, h]
    push_cast
    linear_combination -hg
  exact Int.induction_on m (by simp) (fun k => step k) (fun k => back (-k))

theorem zeta_lattice_shift :
    Specs.D12Complex.Ch22.LegendreLatticeShifts.zeta_lattice_shift_type := by
  intro ω₁ ω₂ h₁ h₂ m n a
  have hω₁ : ω₁ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hω₂ : ω₂ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hshift₁ := additive_integer_shift (S := (lattice ω₁ ω₂).toAddSubgroup) hω₁
    (ZetaSigmaQuasiperiods.zeta_shift_off_lattice h₁ h₂ hω₁
      (ZetaSigmaQuasiperiods.generator_properties h₁ h₂ (by simp : ω₁ ∈ ({ω₁, ω₂} : Set ℂ))).2) m
  have hshift₂ := additive_integer_shift (S := (lattice ω₁ ω₂).toAddSubgroup) hω₂
    (ZetaSigmaQuasiperiods.zeta_shift_off_lattice h₁ h₂ hω₂
      (ZetaSigmaQuasiperiods.generator_properties h₁ h₂ (by simp : ω₂ ∈ ({ω₁, ω₂} : Set ℂ))).2) n
  filter_upwards [ZetaSigmaConvergence.off_lattice_eventually h₁ h₂ a] with z hz
  have hz' : z + (m : ℂ) * ω₁ ∉ lattice ω₁ ω₂ := by
    intro h
    exact hz (by simpa using sub_mem h ((lattice ω₁ ω₂).smul_mem m hω₁))
  change zeta ω₁ ω₂ (z + ((m : ℂ) * ω₁ + (n : ℂ) * ω₂)) = _
  rw [← add_assoc, hshift₂ _ hz', hshift₁ _ hz]
  ring

/-- Translation of a segment integral for a function with a constant increment. -/
lemma segment_increment_integral (f : ℂ → ℂ) (a b τ η : ℂ)
    (hc : ContinuousOn f (segmentPath a b).trace)
    (hd : ContinuousOn f (segmentPath (a + τ) (b + τ)).trace)
    (hf : ∀ z ∈ (segmentPath a b).trace, f (z + τ) = f z + η) :
    (segmentPath (a + τ) (b + τ)).integral f =
      (segmentPath a b).integral f + η * (b - a) := by
  rw [segment_integral_formula _ _ _ hd, segment_integral_formula _ _ _ hc]
  have hcont : ContinuousOn (fun t : ℝ => f (a + t • (b - a)) * (b - a)) (Icc 0 1) := by
    apply ContinuousOn.mul_const
    exact hc.comp (by fun_prop) (fun t ht => ⟨t, ht, rfl⟩)
  calc
    _ = ∫ t in (0 : ℝ)..1, (f (a + t • (b - a)) * (b - a) + η * (b - a)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [show b + τ - (a + τ) = b - a by abel,
        show a + τ + t • (b - a) = (a + t • (b - a)) + τ by abel,
        hf (a + t • (b - a)) ⟨t, (by change t ∈ Icc (0 : ℝ) 1; simpa using ht), rfl⟩]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        ((show ContinuousOn _ (uIcc (0 : ℝ) 1) by simpa using hcont).intervalIntegrable) intervalIntegrable_const]
      simp

lemma zeta_residue_one {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {a : ℂ} (ha : a ∈ lattice ω₁ ω₂) : Residue.residue (zeta ω₁ ω₂) a = 1 := by
  obtain ⟨g, hg, heq⟩ := ZetaSigmaConvergence.zeta_principal_part ω₁ ω₂ h₁ h₂ a ha
  let G : ℂ → ℂ := fun z => 1 + (z - a) * g z
  have hG : AnalyticAt ℂ G a := analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hg)
  obtain ⟨r, hr, hGr⟩ := hG.exists_ball_analyticOnNhd
  have hgerm : zeta ω₁ ω₂ =ᶠ[𝓝[≠] a] (fun z => (z - a)⁻¹ • G z) := by
    filter_upwards [heq, self_mem_nhdsWithin] with z hz hza
    change zeta ω₁ ω₂ z = 1 / (z - a) + g z at hz
    rw [hz]
    have hn : z - a ≠ 0 := sub_ne_zero.mpr hza
    dsimp [G]
    simp only [one_div]
    field_simp
  obtain ⟨s, hs, hfs⟩ := Metric.mem_nhdsWithin_iff.mp hgerm
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral (zeta ω₁ ω₂) a ρ = 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hr),
      nhdsWithin_le_nhds (Iio_mem_nhds hs)] with ρ hρ hρr hρs
    have hc : circleIntegral (zeta ω₁ ω₂) a ρ =
        circleIntegral (fun z => (z - a)⁻¹ • G z) a ρ := by
      apply circleIntegral.integral_congr hρ.le
      intro z hz
      apply hfs
      refine ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hz).trans_lt hρs), ?_⟩
      simp only [mem_compl_iff, mem_singleton_iff]
      intro he
      subst z
      have := Metric.mem_sphere.mp hz
      simp only [dist_self] at this
      exact hρ.ne' this.symm
    rw [hc]
    have h := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      countable_empty (Metric.mem_ball_self hρ)
      ((hGr.mono (Metric.closedBall_subset_ball hρr)).continuousOn)
      (fun z hz => (hGr z (Metric.ball_subset_ball hρr.le hz.1)).differentiableAt)
    simpa [G, smul_eq_mul] using h
  exact Tendsto.limUnder_eq (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))

open private periodBasis periodBasis_zero periodBasis_one from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.LatticeGeometry

/-- Continuous boundary values on all four sides of a pole-free cell. -/
lemma zeta_boundary_continuity {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (a : ℂ) (havoid : Disjoint
      (frontier (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂))
      (lattice ω₁ ω₂ : Set ℂ)) :
    ContinuousOn (zeta ω₁ ω₂) (segmentPath a (a + ω₁)).trace ∧
    ContinuousOn (zeta ω₁ ω₂) (segmentPath (a + ω₁) (a + ω₁ + ω₂)).trace ∧
    ContinuousOn (zeta ω₁ ω₂) (segmentPath (a + ω₁ + ω₂) (a + ω₂)).trace ∧
    ContinuousOn (zeta ω₁ ω₂) (segmentPath (a + ω₂) a).trace := by
  let b := periodBasis h₁ h₂
  have hb₀ : b 0 = ω₁ := periodBasis_zero h₁ h₂
  have hb₁ : b 1 = ω₂ := periodBasis_one h₁ h₂
  have hc (r s : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
      (he : r = 0 ∨ r = 1 ∨ s = 0 ∨ s = 1) :
      ContinuousAt (zeta ω₁ ω₂) (a + r • ω₁ + s • ω₂) := by
    have hf := parallelogram_boundary_point b a r s hr hs he
    rw [hb₀, hb₁] at hf
    exact ((ZetaSigmaConvergence.zeta_holomorphic ω₁ ω₂ h₁ h₂).2 _
      (fun h => Set.disjoint_left.mp havoid hf h)).continuousAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro z ⟨t, ht, rfl⟩
    apply ContinuousAt.continuousWithinAt
    simpa [segmentPath, PiecewiseC1Path.path] using hc t 0 ht (by simp) (by simp)
  · rintro z ⟨t, ht, rfl⟩
    apply ContinuousAt.continuousWithinAt
    simpa [segmentPath, PiecewiseC1Path.path] using hc 1 t (by simp) ht (by simp)
  · rintro z ⟨t, ht, rfl⟩
    change t ∈ Icc (0 : ℝ) 1 at ht
    apply ContinuousAt.continuousWithinAt
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    convert hc (1 - t) 1 ht' (by simp) (by simp) using 1
    simp only [segmentPath, PiecewiseC1Path.path,
      sub_smul, one_smul, smul_sub, smul_add]
    abel
  · rintro z ⟨t, ht, rfl⟩
    change t ∈ Icc (0 : ℝ) 1 at ht
    apply ContinuousAt.continuousWithinAt
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    convert hc 0 (1 - t) (by simp) ht' (by simp) using 1
    simp only [segmentPath, PiecewiseC1Path.path,
      sub_smul, one_smul, zero_smul, add_zero, smul_sub, smul_add]
    abel

lemma zeta_boundary_integral {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (a : ℂ) (havoid : Disjoint
      (frontier (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂))
      (lattice ω₁ ω₂ : Set ℂ)) :
    parallelogramBoundaryIntegral a ω₁ ω₂ (zeta ω₁ ω₂) =
      eta ω₁ ω₂ ω₁ * ω₂ - eta ω₁ ω₂ ω₂ * ω₁ := by
  obtain ⟨hb, hr, ht, hl⟩ := zeta_boundary_continuity h₁ h₂ a havoid
  have hleft : ContinuousOn (zeta ω₁ ω₂) (segmentPath a (a + ω₂)).trace := by
    rwa [segment_trace_reverse] at hl
  have htop : ContinuousOn (zeta ω₁ ω₂) (segmentPath (a + ω₂) (a + ω₁ + ω₂)).trace := by
    rwa [segment_trace_reverse] at ht
  have hω₁ : ω₁ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hω₂ : ω₂ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hoff {z : ℂ} (hz : z ∈ (segmentPath a (a + ω₁)).trace ∨
      z ∈ (segmentPath a (a + ω₂)).trace) : z ∉ lattice ω₁ ω₂ := by
    let b := periodBasis h₁ h₂
    have hb₀ : b 0 = ω₁ := periodBasis_zero h₁ h₂
    have hb₁ : b 1 = ω₂ := periodBasis_one h₁ h₂
    apply fun h => Set.disjoint_left.mp havoid ?_ h
    rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · have h := parallelogram_boundary_point b a t 0 ht (by simp) (by simp)
      simpa [hb₀, hb₁, segmentPath, PiecewiseC1Path.path] using h
    · have h := parallelogram_boundary_point b a 0 t (by simp) ht (by simp)
      simpa [hb₀, hb₁, segmentPath, PiecewiseC1Path.path] using h
  have hR := segment_increment_integral (zeta ω₁ ω₂) a (a + ω₂) ω₁ (eta ω₁ ω₂ ω₁)
    hleft (by simpa [add_assoc, add_comm, add_left_comm] using hr)
    (fun z hz => ZetaSigmaQuasiperiods.zeta_shift_off_lattice h₁ h₂ hω₁
      (ZetaSigmaQuasiperiods.generator_properties h₁ h₂ (by simp : ω₁ ∈ ({ω₁, ω₂} : Set ℂ))).2
      z (hoff (Or.inr hz)))
  have hT := segment_increment_integral (zeta ω₁ ω₂) a (a + ω₁) ω₂ (eta ω₁ ω₂ ω₂)
    hb htop (fun z hz => ZetaSigmaQuasiperiods.zeta_shift_off_lattice h₁ h₂ hω₂
      (ZetaSigmaQuasiperiods.generator_properties h₁ h₂ (by simp : ω₂ ∈ ({ω₁, ω₂} : Set ℂ))).2
      z (hoff (Or.inl hz)))
  have htoprev := segment_reverse_integral (a + ω₂) (a + ω₁ + ω₂) (zeta ω₁ ω₂) htop
  have hleftrev := segment_reverse_integral a (a + ω₂) (zeta ω₁ ω₂) hleft
  have heq : a + ω₂ + ω₁ = a + ω₁ + ω₂ := by abel
  rw [heq] at hR
  unfold parallelogramBoundaryIntegral
  rw [htoprev, hleftrev, hR, hT]
  ring

/-- The oriented boundary encloses exactly one lattice point of residue one. -/
theorem legendre_relation :
    Specs.D12Complex.Ch22.LegendreLatticeShifts.legendre_relation_type := by
  classical
  intro ω₁ ω₂ h₁ h₂
  let b := periodBasis h₁ h₂
  have hb₀ : b 0 = ω₁ := periodBasis_zero h₁ h₂
  have hb₁ : b 1 = ω₂ := periodBasis_one h₁ h₂
  let L := WeierstrassSeries.periodPair h₁ h₂
  have hclosed : IsClosed (lattice ω₁ ω₂ : Set ℂ) := L.isClosed_lattice
  let : DiscreteTopology (lattice ω₁ ω₂) := D12Complex.Ch22.LatticeGeometry.discrete ω₁ ω₂ h₁ h₂
  have hdisc : IsDiscrete (lattice ω₁ ω₂ : Set ℂ) := isDiscrete_iff_discreteTopology.mpr inferInstance
  have hcount : (lattice ω₁ ω₂ : Set ℂ).Countable := hclosed.isLindelof.countable_of_isDiscrete hdisc
  obtain ⟨a, havoid⟩ := exists_avoiding_cell b (lattice ω₁ ω₂ : Set ℂ) hcount
  rw [hb₀, hb₁] at havoid
  let P := Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂
  have hreps := representatives_in_avoiding_cell h₁ h₂ (lattice ω₁ ω₂ : Set ℂ) a
    (fun z l hl => ⟨fun h => by simpa using sub_mem h hl, fun hz => add_mem hz hl⟩) havoid
  obtain ⟨w, hw, huniq⟩ := hreps 0 (zero_mem _)
  have hwL : w ∈ lattice ω₁ ω₂ := by
    have h := (D12Complex.TorusSurface.projection_eq_iff w 0).mp hw.2
    simpa using h
  have hI (z : ℂ) (hz : z ∈ lattice ω₁ ω₂) : z ∈ interior P ↔ z = w := by
    refine ⟨fun hzi => huniq z ⟨hzi, ?_⟩, fun he => he.symm ▸ hw.1⟩
    exact (D12Complex.TorusSurface.projection_eq_iff z 0).mpr (by simpa using hz)
  obtain ⟨Γ, htrace, hInt, _⟩ := parallelogram_cycle_on_frontier h₁ h₂ a
  have havoid' : Disjoint Γ.trace (lattice ω₁ ω₂ : Set ℂ) := havoid.mono_left htrace
  have hindex (z : ℂ) (hz : z ∈ lattice ω₁ ω₂) : Γ.index z = if z = w then 1 else 0 := by
    have hztr : z ∉ Γ.trace := fun h => Set.disjoint_left.mp havoid' h hz
    rw [Γ.index_eq_integral z hztr, hInt _ (Γ.chain.reciprocal_continuousOn_trace z hztr)]
    by_cases he : z = w
    · rw [ite_eq_left he, parallelogram_reciprocal_integral_of_mem_interior h₁ h₂ a z ((hI z hz).mpr he)]
      exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
    · have hn : z ∉ P := by
        intro hp
        have hnI : z ∉ interior P := fun hi => he ((hI z hz).mp hi)
        exact Set.disjoint_left.mp havoid ((mem_frontier_iff_notMem_interior hp).mpr hnI) hz
      rw [ite_eq_right he, parallelogram_reciprocal_integral_of_notMem hn, mul_zero]
  have hhol : HolomorphicOn (univ \ (lattice ω₁ ω₂ : Set ℂ)) (zeta ω₁ ω₂) := by
    rw [← compl_eq_univ_sdiff]
    exact ZetaSigmaConvergence.zeta_holomorphic ω₁ ω₂ h₁ h₂
  obtain ⟨s, hs, hint⟩ := ResidueCycle.residue_theorem univ (lattice ω₁ ω₂ : Set ℂ)
    (zeta ω₁ ω₂) Γ isOpen_univ (subset_univ _) (hclosed.preimage continuous_subtype_val) hdisc
    hhol (subset_univ _) havoid' (by simp)
  have hs' : s = {w} := by
    ext z
    rw [hs, Finset.mem_singleton]
    by_cases hz : z ∈ lattice ω₁ ω₂
    · rw [hindex z hz]
      simp [hz]
    · have hn : z ≠ w := fun he => hz (he.symm ▸ hwL)
      simp [hz, hn]
  have hc : ContinuousOn (zeta ω₁ ω₂) Γ.trace := by
    intro z hz
    exact ((ZetaSigmaConvergence.zeta_holomorphic ω₁ ω₂ h₁ h₂).2 z
      (fun h => Set.disjoint_left.mp havoid' hz h)).continuousAt.continuousWithinAt
  rw [hs'] at hint
  simp only [Finset.sum_singleton, hindex w hwL, ite_true,
    zeta_residue_one h₁ h₂ hwL, mul_one] at hint
  rw [hInt _ hc, zeta_boundary_integral h₁ h₂ a havoid] at hint
  simpa only [ite_true, mul_one] using hint

/-- The multiplier for repeated translation in one direction. -/
private def shiftFactor (ω η : ℂ) (k : ℤ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * Complex.exp ((k : ℂ) * η * (z + (k : ℂ) * ω / 2))

private lemma shiftFactor_succ (ω η z : ℂ) (k : ℤ) :
    shiftFactor ω η (k + 1) z =
      -Complex.exp (η * (z + (k : ℂ) * ω + ω / 2)) * shiftFactor ω η k z := by
  unfold shiftFactor
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
  push_cast
  rw [show ((k : ℂ) + 1) * η * (z + ((k : ℂ) + 1) * ω / 2) =
    η * (z + (k : ℂ) * ω + ω / 2) + (k : ℂ) * η * (z + (k : ℂ) * ω / 2) by ring,
    Complex.exp_add]
  ring

lemma multiplicative_integer_shift {f : ℂ → ℂ} {ω η : ℂ}
    (hf : ∀ z, f (z + ω) = -Complex.exp (η * (z + ω / 2)) * f z) (m : ℤ) :
    ∀ z, f (z + (m : ℂ) * ω) =
      (-1 : ℂ) ^ m * Complex.exp ((m : ℂ) * η * (z + (m : ℂ) * ω / 2)) * f z := by
  change ∀ z, f (z + (m : ℂ) * ω) = shiftFactor ω η m z * f z
  have step (k : ℤ) (hk : ∀ z, f (z + (k : ℂ) * ω) = shiftFactor ω η k z * f z) :
      ∀ z, f (z + ((k + 1 : ℤ) : ℂ) * ω) = shiftFactor ω η (k + 1) z * f z := by
    intro z
    rw [Int.cast_add, Int.cast_one, add_mul, one_mul, ← add_assoc, hf, hk,
      shiftFactor_succ]
    ring
  have back (k : ℤ) (hk : ∀ z, f (z + (k : ℂ) * ω) = shiftFactor ω η k z * f z) :
      ∀ z, f (z + ((k - 1 : ℤ) : ℂ) * ω) = shiftFactor ω η (k - 1) z * f z := by
    intro z
    apply mul_left_cancel₀ (neg_ne_zero.mpr (Complex.exp_ne_zero
      (η * (z + ((k - 1 : ℤ) : ℂ) * ω + ω / 2))))
    rw [← hf, show z + ((k - 1 : ℤ) : ℂ) * ω + ω = z + (k : ℂ) * ω by push_cast; ring,
      hk, ← mul_assoc, ← shiftFactor_succ, sub_add_cancel]
  exact Int.induction_on m (by simp [shiftFactor]) (fun k => step k) (fun k => back (-k))

lemma sigma_shift_of_legendre {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im)
    (hL : eta ω₁ ω₂ ω₁ * ω₂ - eta ω₁ ω₂ ω₂ * ω₁ = 2 * Real.pi * Complex.I)
    (m n : ℤ) (z : ℂ) :
    sigma ω₁ ω₂ (z + ((m : ℂ) * ω₁ + (n : ℂ) * ω₂)) =
      (-1 : ℂ) ^ (m + n + m * n) *
        Complex.exp (((m : ℂ) * eta ω₁ ω₂ ω₁ + (n : ℂ) * eta ω₁ ω₂ ω₂) *
          (z + ((m : ℂ) * ω₁ + (n : ℂ) * ω₂) / 2)) * sigma ω₁ ω₂ z := by
  have hs₁ := multiplicative_integer_shift (f := sigma ω₁ ω₂) (η := eta ω₁ ω₂ ω₁)
    (ZetaSigmaQuasiperiods.sigma_quasiperiod ω₁ ω₂ h₁ h₂ ω₁ (by simp)) m z
  have hs₂ := multiplicative_integer_shift (f := sigma ω₁ ω₂) (η := eta ω₁ ω₂ ω₂)
    (ZetaSigmaQuasiperiods.sigma_quasiperiod ω₁ ω₂ h₁ h₂ ω₂ (by simp)) n
    (z + (m : ℂ) * ω₁)
  rw [← add_assoc, hs₂, hs₁]
  let E := ((m : ℂ) * eta ω₁ ω₂ ω₁ + (n : ℂ) * eta ω₁ ω₂ ω₂) *
    (z + ((m : ℂ) * ω₁ + (n : ℂ) * ω₂) / 2)
  have hexp : (n : ℂ) * eta ω₁ ω₂ ω₂ * (z + (m : ℂ) * ω₁ + (n : ℂ) * ω₂ / 2) +
      (m : ℂ) * eta ω₁ ω₂ ω₁ * (z + (m : ℂ) * ω₁ / 2) =
      E + ((m * n : ℤ) : ℂ) * (-(Real.pi * Complex.I)) := by
    dsimp [E]
    push_cast
    linear_combination -((m : ℂ) * (n : ℂ) / 2) * hL
  have he : Complex.exp (((m * n : ℤ) : ℂ) * (-(Real.pi * Complex.I))) = (-1 : ℂ) ^ (m * n) := by
    rw [Complex.exp_int_mul, Complex.exp_neg_pi_mul_I]
  calc
    _ = (-1 : ℂ) ^ n * (-1 : ℂ) ^ m *
        Complex.exp ((n : ℂ) * eta ω₁ ω₂ ω₂ * (z + (m : ℂ) * ω₁ + (n : ℂ) * ω₂ / 2) +
          (m : ℂ) * eta ω₁ ω₂ ω₁ * (z + (m : ℂ) * ω₁ / 2)) * sigma ω₁ ω₂ z := by
      rw [Complex.exp_add]; ring
    _ = _ := by
      rw [hexp, Complex.exp_add, he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      dsimp [E]
      ring

theorem sigma_lattice_shift :
    Specs.D12Complex.Ch22.LegendreLatticeShifts.sigma_lattice_shift_type := by
  intro ω₁ ω₂ h₁ h₂ m n z
  exact sigma_shift_of_legendre h₁ h₂ (legendre_relation ω₁ ω₂ h₁ h₂) m n z

end D12Complex.Ch22.LegendreLatticeShifts
