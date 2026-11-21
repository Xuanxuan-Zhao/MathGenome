import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfReturnExpansion
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

noncomputable section
namespace D13Unified.Ch16.HopfPeriodicOrbitBridge

open Complex Filter Set
open scoped NNReal
open Specs.D13Unified.Ch16.CubicHomologicalElimination
open Specs.D13Unified.Ch16.CubicNormalForm
open Specs.D13Unified.Ch16.HopfReturnExpansion
open Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge

/-- A monotone map has no nontrivial finite cycle lying wholly in its local
monotonicity domain. No invariant interval or global monotonicity is used. -/
theorem noHigherCycles {f : ℝ → ℝ} {S : Set ℝ} (hf : MonotoneOn f S)
    {r : ℝ} {n : ℕ} (hn : 0 < n)
    (hstay : ∀ j ≤ n, f^[j] r ∈ S) (hcycle : f^[n] r = r) : f r = r := by
  have h0 : r ∈ S := by simpa using hstay 0 (Nat.zero_le _)
  rcases lt_trichotomy r (f r) with hlt | heq | hgt
  · have hsteps : ∀ j, j < n → f^[j] r ≤ f^[j + 1] r := by
      intro j
      induction j with
      | zero => intro _; simpa using hlt.le
      | succ j ih =>
        intro hj
        have hprev := ih (by omega)
        simpa only [Function.iterate_succ_apply'] using
          hf (hstay j (by omega)) (hstay (j + 1) (by omega)) hprev
    have hbound : ∀ j, j ≤ n → 0 < j → f r ≤ f^[j] r := by
      intro j
      induction j with
      | zero => intro _ hj; omega
      | succ j ih =>
        intro hj _
        by_cases hz : j = 0
        · subst j; simp
        · exact (ih (by omega) (by omega)).trans (hsteps j (by omega))
    have hh := hbound n le_rfl hn
    rw [hcycle] at hh
    exact (not_le_of_gt hlt hh).elim
  · exact heq.symm
  · have hsteps : ∀ j, j < n → f^[j + 1] r ≤ f^[j] r := by
      intro j
      induction j with
      | zero => intro _; simpa using hgt.le
      | succ j ih =>
        intro hj
        have hprev := ih (by omega)
        simpa only [Function.iterate_succ_apply'] using
          hf (hstay (j + 1) (by omega)) (hstay j (by omega)) hprev
    have hbound : ∀ j, j ≤ n → 0 < j → f^[j] r ≤ f r := by
      intro j
      induction j with
      | zero => intro _ hj; omega
      | succ j ih =>
        intro hj _
        by_cases hz : j = 0
        · subst j; simp
        · exact (hsteps j (by omega)).trans (ih (by omega) (by omega))
    have hh := hbound n le_rfl hn
    rw [hcycle] at hh
    exact (not_le_of_gt hgt hh).elim

/-- Package the actual upstream result, without adding a periodic-orbit premise. -/
theorem sourceReturnData (F : ℝ × ℂ → ℂ) (ω : ℝ) (h : SourceHypotheses F ω) :
    ∃ ε ρ δ C : ℝ, ∃ P Q : ℝ × ℝ → ℝ, ReturnData F ω ε ρ δ C P Q := by
  obtain ⟨_, ε, hε, ρ, hρ, δ, hδ, C, hC, P, Q, hrest⟩ :=
    HopfReturnExpansion.returnExpansion F ω h.1 h.2.1 h.2.2.1 h.2.2.2
  exact ⟨ε, ρ, δ, C, P, Q, hε, hρ, hδ, hC, hrest⟩

lemma returnBox_isOpen (δ ε : ℝ) : IsOpen (returnBox δ ε) :=
  (isOpen_lt (continuous_fst.abs) continuous_const).inter
    (isOpen_lt (continuous_snd.abs) continuous_const)

/-- A C² scalar map with positive radial derivative at the origin is strictly
increasing on a smaller fixed rectangle. -/
theorem localStrictMono {P : ℝ × ℝ → ℝ} {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hP : ContDiffOn ℝ 2 P (returnBox δ ε))
    (hd : HasDerivAt (fun r => P (r, 0)) 1 0) :
    ∃ d > 0, ∃ η > 0, d ≤ δ ∧ η ≤ ε ∧
      ∀ μ : ℝ, |μ| < η → StrictMonoOn (fun r => P (r, μ)) (Ioo 0 d) := by
  have hzero : (0, 0) ∈ returnBox δ ε := by simpa [returnBox] using And.intro hδ hε
  have hP0 : ContDiffAt ℝ 2 P (0, 0) :=
    hP.contDiffAt ((returnBox_isOpen δ ε).mem_nhds hzero)
  have hD : ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ P q (1, 0)) (0, 0) :=
    (hP0.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have hD0 : fderiv ℝ P (0, 0) (1, 0) = 1 := by
    have hc := hP0.differentiableAt (by norm_num)
    have ht := hc.hasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, 0)) (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
    exact ht.unique hd
  have hev : ∀ᶠ q : ℝ × ℝ in nhds (0, 0), 0 < fderiv ℝ P q (1, 0) :=
    hD.eventually (lt_mem_nhds (by change 0 < fderiv ℝ P (0, 0) (1, 0); rw [hD0]; norm_num))
  obtain ⟨b, hb, hbd⟩ := Metric.eventually_nhds_iff.mp hev
  let d := min δ (b / 2)
  let η := min ε (b / 2)
  have hdpos : 0 < d := lt_min hδ (by positivity)
  have hηpos : 0 < η := lt_min hε (by positivity)
  refine ⟨d, hdpos, η, hηpos, min_le_left _ _, min_le_left _ _, ?_⟩
  intro μ hμ
  have hslice : ContDiffOn ℝ 2 (fun r => P (r, μ)) (Ioo 0 d) := by
    apply hP.comp (contDiffOn_id.prodMk contDiffOn_const)
    intro r hr
    exact ⟨by change |r| < δ; rw [abs_of_pos hr.1]; exact hr.2.trans_le (min_le_left _ _),
      hμ.trans_le (min_le_left _ _)⟩
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 d) hslice.continuousOn
  intro r hr
  have hrr : r ∈ Ioo 0 d := interior_subset hr
  have hq : (r, μ) ∈ returnBox δ ε :=
    ⟨by rw [abs_of_pos hrr.1]; exact hrr.2.trans_le (min_le_left _ _),
      hμ.trans_le (min_le_left _ _)⟩
  have hPr := hP.contDiffAt ((returnBox_isOpen δ ε).mem_nhds hq)
  have hder := (hPr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r μ))
  have hval : deriv (fun r => P (r, μ)) r = fderiv ℝ P (r, μ) (1, 0) := by
    simpa only [Function.comp_def, id_eq] using hder.deriv
  rw [hval]
  apply hbd
  rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs,
    Real.norm_eq_abs, max_lt_iff]
  constructor
  · rw [abs_of_pos hrr.1]
    exact (hrr.2.trans_le (min_le_right _ _)).trans (by linarith)
  · exact (hμ.trans_le (min_le_right _ _)).trans (by linarith)

/-- Differentiating P=r(1+Q) at zero uses the genuine Q value supplied upstream. -/
theorem return_radial_derivative (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (hF : SourceHypotheses F ω)
    (h : ReturnData F ω ε ρ δ C P Q) :
    HasDerivAt (fun r => P (r, 0)) 1 0 := by
  rcases h with ⟨hε, _, hδ, _, _, _, _, hQ, _, hzero, hfac, _⟩
  have hq0 : (0, 0) ∈ returnBox δ ε := by simpa [returnBox] using And.intro hδ hε
  have hreg := hQ.contDiffAt ((returnBox_isOpen δ ε).mem_nhds hq0)
  have hqder := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    (f := fun r : ℝ => (r, 0)) (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
  have ha : spectralReal F 0 = 0 :=
    (CubicNormalForm.normalForm F ω hF.1 hF.2.1 hF.2.2.1 hF.2.2.2).1
  have hQ0 : Q (0, 0) = 0 := by
    rw [(hzero 0 (by simpa using hε)).2]
    simp [linearReturnFactor, angularLinear, ha]
  have hd := (hasDerivAt_id (0 : ℝ)).mul (hqder.const_add 1)
  have hde : HasDerivAt (fun r => r * (1 + Q (r, 0))) 1 0 := by
    convert! hd using 1 <;> simp [hQ0]
  apply hde.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with r hr
  exact (hfac (r, 0) ⟨abs_lt.mpr hr, by simpa using hε⟩).1

/-- Actual-map monotonicity and exclusion of every finite higher cycle. -/
theorem localMonotonicity : LocalMonotonicity := by
  intro F ω hF ε ρ δ C P Q h
  obtain ⟨d, hd, η, hη, hdδ, hηε, hmono⟩ :=
    localStrictMono h.2.2.1 h.1 h.2.2.2.2.2.2.1
      (return_radial_derivative F ω ε ρ δ C P Q hF h)
  refine ⟨d, hd, η, hη, hdδ, hηε, ?_⟩
  intro μ hμ
  exact ⟨hmono μ hμ, fun r n hn hs hc => noHigherCycles (hmono μ hμ).monotoneOn hn hs hc⟩

/-- Time translation preserves the complete autonomous equation and the period. -/
theorem periodicSolution_shift {V : ℂ → ℂ} {z : ℝ → ℂ} {T : ℝ}
    (hz : IsPeriodicSolution V z T) (a : ℝ) :
    IsPeriodicSolution V (fun t => z (t + a)) T := by
  refine ⟨hz.1, ?_, ?_, ?_⟩
  · intro t
    simpa only [add_assoc, add_comm T a] using hz.2.1 (t + a)
  · intro t
    convert! (hz.2.2.1 (t + a)).scomp t ((hasDerivAt_id t).add_const a) using 1 <;> simp
  · obtain ⟨s, t, hst⟩ := hz.2.2.2
    exact ⟨s - a, t - a, by simpa using hst⟩

/-- ODE uniqueness identifies orbit traces, regardless of phase or repeated
periods. This also applies to nonperiodic complete trajectories. -/
theorem periodicOrbit_eq_of_common_point {V : ℂ → ℂ} {S Γ Λ : Set ℂ}
    {K : ℝ≥0} (hV : LipschitzOnWith K V S)
    (hΓ : IsPeriodicOrbit V Γ) (hΛ : IsPeriodicOrbit V Λ)
    (hΓS : Γ ⊆ S) (hΛS : Λ ⊆ S) {p : ℂ} (hpΓ : p ∈ Γ) (hpΛ : p ∈ Λ) : Γ = Λ := by
  obtain ⟨z, T, hz, rfl⟩ := hΓ
  obtain ⟨w, U, hw, rfl⟩ := hΛ
  obtain ⟨a, ha⟩ := hpΓ
  obtain ⟨b, hb⟩ := hpΛ
  have hza := periodicSolution_shift hz a
  have hwb := periodicSolution_shift hw b
  have heq : (fun t => z (t + a)) = (fun t => w (t + b)) :=
    ODE_solution_unique_univ (v := fun _ => V) (s := fun _ => S) (t₀ := 0)
      (fun _ => hV)
      (fun t => ⟨hza.2.2.1 t, hΓS (mem_range_self _)⟩)
      (fun t => ⟨hwb.2.2.1 t, hΛS (mem_range_self _)⟩)
      (by simpa using ha.trans hb.symm)
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t - a + b, ?_⟩
    simpa using (congrFun heq (t - a)).symm
  · rintro ⟨t, rfl⟩
    refine ⟨t - b + a, ?_⟩
    simpa using congrFun heq (t - b)

/-- A nonconstant complete trajectory cannot meet a locally unique equilibrium. -/
theorem periodicSolution_ne_equilibrium {V : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hV : LipschitzOnWith K V S) {p : ℂ} (hp : p ∈ S) (hpV : V p = 0)
    {z : ℝ → ℂ} {T : ℝ} (hz : IsPeriodicSolution V z T)
    (hzS : range z ⊆ S) : ∀ t, z t ≠ p := by
  intro t ht
  have heq : z = fun _ => p :=
    ODE_solution_unique_univ (v := fun _ => V) (s := fun _ => S) (t₀ := t)
      (fun _ => hV) (fun t => ⟨hz.2.2.1 t, hzS (mem_range_self _)⟩)
      (fun t => ⟨by simpa [hpV] using hasDerivAt_const t p, hp⟩) ht
  obtain ⟨s, u, hsu⟩ := hz.2.2.2
  exact hsu (by rw [heq])

/-- The actual chart sends complete confined normal solutions to complete
solutions of the original family; injectivity preserves nonconstancy. -/
theorem coordinateTransport (F : ℝ × ℂ → ℂ) {ε ρ μ : ℝ}
    (hcoord : CoordinateValidity F ε ρ) (hμ : |μ| < ε)
    {z : ℝ → ℂ} {T : ℝ}
    (hz : IsPeriodicSolution (fun w => transformedField F (μ, w)) z T)
    (hstay : ∀ t, ‖z t‖ < ρ) :
    IsPeriodicSolution (fun x => F (μ, x)) (fun t => coordinate F μ (z t)) T := by
  obtain ⟨e, he, hsrc, _, hreg⟩ := hcoord
  have hmem : ∀ t, (μ, z t) ∈ stateParameterBox ε ρ := fun t => ⟨hμ, hstay t⟩
  have heq : ∀ x, e x = familyCoordinate F x := fun x => congrFun he x
  refine ⟨hz.1, ?_, ?_, ?_⟩
  · intro t
    exact congrArg (coordinate F μ) (hz.2.1 t)
  · intro t
    have hec := (hreg (μ, z t) (hmem t)).1
    have hc : ContDiffAt ℝ 2 (coordinate F μ) (z t) := by
      have hh := (contDiffAt_snd.comp (μ, z t) hec).comp (z t)
        (contDiffAt_const.prodMk contDiffAt_id)
      simpa only [he, familyCoordinate, Function.comp_def] using hh
    have hd := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hz.2.2.1 t)
    rwa [(hreg (μ, z t) (hmem t)).2.2.2] at hd
  · obtain ⟨s, t, hst⟩ := hz.2.2.2
    refine ⟨s, t, ?_⟩
    intro hc
    apply hst
    have hh : e (μ, z s) = e (μ, z t) := by
      rw [heq, heq]
      exact Prod.ext rfl hc
    exact congrArg Prod.snd (e.injOn (hsrc (hmem s)) (hsrc (hmem t)) hh)

/-- Normal-form estimates give a fixed ball on which every parameter slice is
Lipschitz and has its equilibrium at zero. The Lipschitz constant may depend
on the parameter; the confinement ball and parameter interval do not. -/
theorem sourceLocalLipschitz (F : ℝ × ℂ → ℂ) (ω : ℝ) (hF : SourceHypotheses F ω) :
    ∃ ε > 0, ∃ σ > 0, ∀ μ : ℝ, |μ| < ε →
      transformedField F (μ, 0) = 0 ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (fun w => transformedField F (μ, w))
        (Metric.closedBall 0 σ) := by
  obtain ⟨_, _, ε, hε, ρ, hρ, C, _, _, hR, _⟩ :=
    CubicNormalForm.normalForm F ω hF.1 hF.2.1 hF.2.2.1 hF.2.2.2
  refine ⟨ε, hε, ρ / 2, by positivity, ?_⟩
  intro μ hμ
  have hreg : ContDiffOn ℝ 1 (fun w => transformedField F (μ, w))
      (Metric.closedBall 0 (ρ / 2)) := by
    intro w hw
    have hwρ : ‖w‖ < ρ := by
      have hh : ‖w‖ ≤ ρ / 2 := by simpa using hw
      linarith
    exact ((hR (μ, w) ⟨hμ, hwρ⟩).2.2.1.of_le (by norm_num)).contDiffWithinAt
  have hbound := (hR (μ, 0) ⟨hμ, by simpa using hρ⟩).2.2.2.2.2.1
  have hr0 : remainder F (μ, 0) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa using hbound
  have hzero : transformedField F (μ, 0) = 0 := by
    simpa [remainder, normalPolynomial] using hr0
  exact ⟨hzero, hreg.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : ℂ) (ρ / 2)) (isCompact_closedBall _ _)⟩

/-- These orbit assertions follow from the original C⁵ family, with no
assumed section point and no assumed periodic-orbit correspondence. -/
theorem localOrbitUniqueness : LocalOrbitUniqueness := by
  intro F ω hF
  obtain ⟨ε, hε, σ, hσ, hdata⟩ := sourceLocalLipschitz F ω hF
  refine ⟨ε, hε, σ, hσ, ?_⟩
  intro μ hμ
  obtain ⟨hzero, K, hK⟩ := hdata μ hμ
  constructor
  · intro Γ hΓ hΓball hp
    obtain ⟨z, T, hz, rfl⟩ := hΓ
    obtain ⟨t, ht⟩ := hp
    exact periodicSolution_ne_equilibrium hK (Metric.mem_closedBall_self hσ.le) hzero hz
      (hΓball.trans Metric.ball_subset_closedBall) t ht
  · intro Γ Λ hΓ hΛ hΓball hΛball hinter
    obtain ⟨p, hpΓ, hpΛ⟩ := hinter
    exact periodicOrbit_eq_of_common_point hK hΓ hΛ
      (hΓball.trans Metric.ball_subset_closedBall)
      (hΛball.trans Metric.ball_subset_closedBall) hpΓ hpΛ

/-- Repeat a closed physical solution segment. Matching endpoint field values
give the derivative at every join; no global completeness assumption is used. -/
theorem periodicExtension {V : ℂ → ℂ} {z : ℝ → ℂ} {T : ℝ}
    (hT : 0 < T) (hend : z T = z 0)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (V (z t)) (Icc 0 T) t) :
    ∃ w : ℝ → ℂ, Function.Periodic w T ∧ EqOn w z (Icc 0 T) ∧
      (∀ t : ℝ, HasDerivAt w (V (w t)) t) ∧ range w ⊆ z '' Icc 0 T := by
  let w : ℝ → ℂ := fun t => z (toIcoMod hT 0 t)
  have hwper : Function.Periodic w T := (toIcoMod_periodic hT 0).comp z
  have heq : ∀ t ∈ Ico 0 T, w t = z t := by
    intro t ht
    dsimp [w]
    rw [(toIcoMod_eq_self hT).mpr (by simpa using ht)]
  have hw0 : w 0 = z 0 := heq 0 ⟨le_rfl, hT⟩
  have heqcc : EqOn w z (Icc 0 T) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htT | rfl
    · exact heq t ⟨ht.1, htT⟩
    · have hh : w t = w 0 := by simpa using hwper 0
      exact hh.trans (hw0.trans hend.symm)
  have hright : HasDerivWithinAt w (V (z 0)) (Ici 0) 0 := by
    have hd : HasDerivWithinAt z (V (z 0)) (Ici 0) 0 :=
      (hz 0 ⟨le_rfl, hT.le⟩).congr_set (by
        filter_upwards [gt_mem_nhds hT] with t ht
        simp only [mem_Icc, mem_Ici]
        exact propext (and_iff_left ht.le))
    apply hd.congr_of_eventuallyEq _ hw0
    filter_upwards [eventually_mem_nhdsWithin, (gt_mem_nhds hT).filter_mono nhdsWithin_le_nhds]
      with t ht htT
    exact heq t ⟨ht, htT⟩
  have hleft : HasDerivWithinAt w (V (z 0)) (Iic 0) 0 := by
    have hd : HasDerivWithinAt (fun t => z (t + T)) (V (z 0)) (Icc (-T) 0) 0 := by
      have hh := (hz T ⟨hT.le, le_rfl⟩).scomp_of_eq (0 : ℝ)
        (((hasDerivAt_id (0 : ℝ)).add_const T).hasDerivWithinAt (s := Icc (-T) 0))
        (by intro t ht; change 0 ≤ t + T ∧ t + T ≤ T; constructor <;> linarith [ht.1, ht.2]) (by simp)
      convert! hh using 1 <;> simp [hend]
    have hd' : HasDerivWithinAt (fun t => z (t + T)) (V (z 0)) (Iic 0) 0 :=
      hd.congr_set (by
        filter_upwards [lt_mem_nhds (neg_lt_zero.mpr hT)] with t ht
        simp only [mem_Icc, mem_Iic]
        exact propext (and_iff_right ht.le))
    apply hd'.congr_of_eventuallyEq _ (by simpa [hend] using hw0)
    filter_upwards [eventually_mem_nhdsWithin,
      (lt_mem_nhds (neg_lt_zero.mpr hT)).filter_mono nhdsWithin_le_nhds] with t ht htT
    rcases lt_or_eq_of_le (show t ≤ 0 from ht) with ht0 | rfl
    · have hh : t + T ∈ Ico 0 T := ⟨by linarith, by linarith⟩
      have hr := toIcoMod_add_right hT 0 t
      have hv := (toIcoMod_eq_self hT).mpr (show t + T ∈ Ico 0 (0 + T) by simpa using hh)
      dsimp [w]
      rw [← hr, hv]
    · simpa [hend] using hw0
  have hd0 : HasDerivAt w (V (w 0)) 0 := by
    rw [hw0]
    have hh := hright.union hleft
    rw [Ici_union_Iic] at hh
    exact hh.hasDerivAt (by simp)
  have hbase : ∀ u ∈ Ico 0 T, HasDerivAt w (V (w u)) u := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with rfl | hu0
    · exact hd0
    have hd := (hz u ⟨hu.1, hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu0 hu.2)
    rw [heq u hu]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hu0 hu.2] with t ht
    exact heq t ⟨ht.1.le, ht.2⟩
  refine ⟨w, hwper, heqcc, ?_, ?_⟩
  · intro t
    let u := toIcoMod hT 0 t
    let k := toIcoDiv hT 0 t
    have hu : u ∈ Ico 0 T := by simpa [u] using toIcoMod_mem_Ico hT 0 t
    have htu : t - (k : ℝ) * T = u := by
      dsimp [u, k]
      linarith [toIcoMod_add_toIcoDiv_mul hT 0 t]
    have hwu : w u = w t := by
      rw [← htu]
      exact hwper.sub_int_mul_eq k
    have hh := (hbase u hu).scomp_of_eq t
      ((hasDerivAt_id t).sub_const ((k : ℝ) * T)) htu.symm
    have hh' : HasDerivAt (fun x => w (x - (k : ℝ) * T)) (V (w t)) t := by
      convert! hh using 1 <;> simp [hwu]
    apply hh'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun x => (hwper.sub_int_mul_eq k).symm)
  · rintro x ⟨t, rfl⟩
    refine ⟨toIcoMod hT 0 t, ?_, rfl⟩
    exact Ico_subset_Icc_self (by simpa using toIcoMod_mem_Ico hT 0 t)

/-- A fixed full turn gives an actual complete periodic ODE solution. -/
theorem fixedTurnPeriodic : FixedTurnPeriodic := by
  intro F ω μ r ρ hr hturn
  obtain ⟨u, clock, z, _, _, _, hT, _, _, _, hz0, hzT, hphysical, hfirst⟩ := hturn
  let T := clock turnAngle
  obtain ⟨w, hwper, heq, hwder, hwimage⟩ :=
    periodicExtension (V := fun w => transformedField F (μ, w)) hT (hzT.trans hz0.symm) (fun t ht => (hphysical t ht).2)
  have hw0 : w 0 = (r : ℂ) := (heq ⟨le_rfl, hT.le⟩).trans hz0
  have hhalf : T / 2 ∈ Ioo 0 T := ⟨by dsimp [T]; linarith, by dsimp [T]; linarith⟩
  have hnc : w 0 ≠ w (T / 2) := by
    intro hconst
    apply hfirst (T / 2) hhalf
    have hh : z (T / 2) = (r : ℂ) :=
      (heq (Ioo_subset_Icc_self hhalf)).symm.trans (hconst.symm.trans hw0)
    rw [hh]
    exact ⟨by simp, by simpa using hr⟩
  have hwsol : IsPeriodicSolution (fun w => transformedField F (μ, w)) w T :=
    ⟨hT, hwper, hwder, 0, T / 2, hnc⟩
  refine ⟨range w, ⟨w, T, hwsol, rfl⟩, ⟨0, hw0⟩, ?_⟩
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hwimage hx
  simpa using (hphysical t ht).1

/-- A finite physical itinerary and local monotonicity force a first-return
fixed point. This lemma does not assume that the physical period is one turn. -/
theorem itinerary_fixed {F : ℝ × ℂ → ℂ} {ω μ d ρ η : ℝ}
    {P : ℝ × ℝ → ℝ} {Γ : Set ℂ} (hmono : NoHigherReturnCycles P d η)
    (hμ : |μ| < η) (hit : PeriodicItinerary F ω μ P d ρ Γ) :
    ∃ r : ℝ, 0 < r ∧ r < d ∧ (r : ℂ) ∈ Γ ∧ P (r, μ) = r := by
  obtain ⟨z, T, n, times, radii, angle, _, htrace, hn, _, _, _, _, _, _, _, hnodes,
    hclosed, hsteps⟩ := hit
  have hiter : ∀ j ≤ n, (fun s => P (s, μ))^[j] (radii 0) = radii j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact (hsteps j (by omega)).1.symm
  have hstay : ∀ j ≤ n, (fun s => P (s, μ))^[j] (radii 0) ∈ Ioo 0 d := by
    intro j hj
    rw [hiter j hj]
    exact ⟨(hnodes j hj).1, (hnodes j hj).2.1⟩
  have hfixed : P (radii 0, μ) = radii 0 :=
    (hmono μ hμ).2 (radii 0) n hn hstay ((hiter n le_rfl).trans hclosed)
  refine ⟨radii 0, (hnodes 0 (Nat.zero_le _)).1,
    (hnodes 0 (Nat.zero_le _)).2.1, ?_, hfixed⟩
  rw [← htrace, ← (hnodes 0 (Nat.zero_le _)).2.2.1]
  exact mem_range_self _

lemma coordinate_zero (F : ℝ × ℂ → ℂ) (μ : ℝ) : coordinate F μ 0 = 0 := by
  simp [coordinate, Quadratic.eval, Cubic.eval]

/-- A single original open neighborhood has inverse images in a prescribed
normal ball for every sufficiently small parameter. This is a local chart
statement, with the actual inverse rather than a global invertibility premise. -/
theorem uniformInverseNeighborhood (F : ℝ × ℂ → ℂ) {ε ρ σ : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ) (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hcoord : CoordinateValidity F ε ρ) :
    ∃ η > 0, ∃ U : Set ℂ, η ≤ ε ∧ IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∃ e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ),
        (e : ℝ × ℂ → ℝ × ℂ) = familyCoordinate F ∧
        stateParameterBox η σ ⊆ e.source ∧
        ∀ μ x, |μ| < η → x ∈ U →
          (μ, x) ∈ e.target ∧ (e.symm (μ, x)).1 = μ ∧ ‖(e.symm (μ, x)).2‖ < σ := by
  obtain ⟨e, he, hsrc, hparam, hreg⟩ := hcoord
  have h0 : (0, 0) ∈ stateParameterBox ε ρ := by
    simpa [stateParameterBox] using And.intro hε hρ
  have he0 : e (0, 0) = (0, 0) := by
    rw [he]
    simp [familyCoordinate, coordinate_zero]
  have hi0 : e.symm (0, 0) = (0, 0) :=
    (congrArg e.symm he0.symm).trans (e.left_inv (hsrc h0))
  have ht0 : (0, 0) ∈ e.target := he0 ▸ e.map_source (hsrc h0)
  have hc : ContinuousAt e.symm (0, 0) := by
    rw [← he0]
    exact (hreg (0, 0) h0).2.1.continuousAt
  have hsmall : ∀ᶠ y : ℝ × ℂ in nhds (0, 0), ‖(e.symm y).2‖ < σ :=
    hc.snd.norm.eventually (gt_mem_nhds (by simpa [hi0] using hσ))
  obtain ⟨b, hb, hball⟩ := Metric.eventually_nhds_iff.mp
    ((show ∀ᶠ y : ℝ × ℂ in nhds (0, 0), y ∈ e.target from
      e.open_target.mem_nhds ht0).and hsmall)
  let η := min ε (b / 2)
  refine ⟨η, lt_min hε (by positivity), Metric.ball 0 (b / 2), min_le_left _ _,
    Metric.isOpen_ball, Metric.mem_ball_self (by positivity), e, he, ?_, ?_⟩
  · intro x hx
    exact hsrc ⟨hx.1.trans_le (min_le_left _ _), hx.2.trans_le hσρ⟩
  · intro μ x hμ hx
    have hdist : dist (μ, x) (0, 0) < b := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
      constructor
      · exact (hμ.trans_le (min_le_right _ _)).trans (by linarith)
      · have hx' : ‖x‖ < b / 2 := by simpa using hx
        linarith
    obtain ⟨htarget, hnorm⟩ := hball hdist
    exact ⟨htarget, hparam _ htarget, hnorm⟩

/-- Inverse coordinate transport on an actual chart. Invertibility of the
spatial derivative proves the lifted equation; it is not an assumed certificate. -/
theorem inverseCoordinateTransport (F : ℝ × ℂ → ℂ) {ε ρ μ : ℝ}
    (e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ))
    (he : (e : ℝ × ℂ → ℝ × ℂ) = familyCoordinate F)
    (hparam : ∀ y ∈ e.target, (e.symm y).1 = y.1)
    (hreg : ∀ x ∈ stateParameterBox ε ρ,
      ContDiffAt ℝ 2 (e : ℝ × ℂ → ℝ × ℂ) x ∧
      ContDiffAt ℝ 2 e.symm (e x) ∧
      (fderiv ℝ (coordinate F x.1) x.2).IsInvertible ∧
      fderiv ℝ (coordinate F x.1) x.2 (transformedField F x) =
        F (x.1, coordinate F x.1 x.2))
    (hμ : |μ| < ε) {z : ℝ → ℂ} {T : ℝ}
    (hz : IsPeriodicSolution (fun x => F (μ, x)) z T)
    (htarget : ∀ t, (μ, z t) ∈ e.target)
    (hstay : ∀ t, ‖(e.symm (μ, z t)).2‖ < ρ) :
    IsPeriodicSolution (fun w => transformedField F (μ, w))
      (fun t => (e.symm (μ, z t)).2) T ∧
    (∀ t, coordinate F μ (e.symm (μ, z t)).2 = z t) ∧
    range z = coordinate F μ '' range (fun t => (e.symm (μ, z t)).2) := by
  let w : ℝ → ℂ := fun t => (e.symm (μ, z t)).2
  have hi : ∀ t, e.symm (μ, z t) = (μ, w t) := by
    intro t
    exact Prod.ext (hparam _ (htarget t)) rfl
  have hei : ∀ t, e (μ, w t) = (μ, z t) := by
    intro t
    rw [← hi t]
    exact e.right_inv (htarget t)
  have hfw : ∀ t, coordinate F μ (w t) = z t := by
    intro t
    have hh := congrArg Prod.snd (hei t)
    simpa only [he, familyCoordinate] using hh
  have hmem : ∀ t, (μ, w t) ∈ stateParameterBox ε ρ := fun t => ⟨hμ, hstay t⟩
  have hwder : ∀ t, HasDerivAt w (transformedField F (μ, w t)) t := by
    intro t
    have hr := hreg (μ, w t) (hmem t)
    have hec : ContDiffAt ℝ 2 e.symm (μ, z t) := by
      rw [← hei t]
      exact hr.2.1
    have hzpair : DifferentiableAt ℝ (fun s => (μ, z s)) t :=
      (differentiableAt_const μ).prodMk (hz.2.2.1 t).differentiableAt
    have hwd : DifferentiableAt ℝ w t :=
      ((hec.differentiableAt (by norm_num)).comp t hzpair).snd
    have hc : ContDiffAt ℝ 2 (coordinate F μ) (w t) := by
      have hh := (contDiffAt_snd.comp (μ, w t) hr.1).comp (w t)
        (contDiffAt_const.prodMk contDiffAt_id)
      simpa only [he, familyCoordinate, Function.comp_def] using hh
    have hdc := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hwd.hasDerivAt
    have heq : (fun s => coordinate F μ (w s)) = z := funext hfw
    change HasDerivAt (fun s => coordinate F μ (w s))
      (fderiv ℝ (coordinate F μ) (w t) (deriv w t)) t at hdc
    rw [heq] at hdc
    have hde : deriv w t = transformedField F (μ, w t) := by
      apply hr.2.2.1.bijective.1
      rw [hdc.unique (hz.2.2.1 t), hr.2.2.2, hfw]
    rw [← hde]
    exact hwd.hasDerivAt
  refine ⟨⟨hz.1, ?_, hwder, ?_⟩, hfw, ?_⟩
  · intro t
    change (e.symm (μ, z (t + T))).2 = (e.symm (μ, z t)).2
    rw [hz.2.1 t]
  · obtain ⟨s, t, hst⟩ := hz.2.2.2
    refine ⟨s, t, ?_⟩
    intro hh
    apply hst
    rw [← hfw s, ← hfw t]
    exact congrArg (coordinate F μ) hh
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨w t, mem_range_self t, hfw t⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (hfw t).symm⟩

/-- A continuous nonvanishing physical trajectory admits a continuous logarithm
on all real time. This is a covering lift, not the discontinuous principal arg. -/
theorem continuousLogLift {z : ℝ → ℂ} (hz : Continuous z) (hnz : ∀ t, z t ≠ 0)
    (L₀ : ℂ) (hL₀ : Complex.exp L₀ = z 0) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L 0 = L₀ ∧ ∀ t, Complex.exp (L t) = z t := by
  obtain ⟨L, ⟨hzero, hlift⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
      (⟨z, hz⟩ : C(ℝ, ℂ)) hL₀ (by intro t; simpa using hnz t)
  exact ⟨L, L.continuous, hzero, fun t => congrFun hlift t⟩

/-- Differentiating a continuous logarithm lift is justified through the
invertible real derivative of exp, even though physical time is real. -/
theorem logLift_hasDerivAt {z L : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hL : ContinuousAt L t) (hlift : ∀ s, Complex.exp (L s) = z s)
    (hz : HasDerivAt z v t) : HasDerivAt L (v / z t) t := by
  have hexp := (Complex.hasDerivAt_exp (L t)).hasFDerivAt.restrictScalars ℝ
  let A : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ (Complex.exp (L t))⁻¹
  have hinv : Function.LeftInverse A
      ((ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp (L t))).restrictScalars ℝ) := by
    intro x
    change (Complex.exp (L t))⁻¹ * (x * Complex.exp (L t)) = x
    field_simp
  have hh := HasFDerivAt.of_comp_of_leftInverse hL hexp hz.hasFDerivAt
    (f'symm := A) (Filter.Eventually.of_forall hlift) hinv
  convert! hh.hasDerivAt using 1
  simp [A, hlift t, div_eq_mul_inv, mul_comm]

/-- A closed trajectory has integral winding in a continuous logarithm lift. -/
theorem logLift_winding {z L : ℝ → ℂ} {T : ℝ}
    (hperiod : z T = z 0) (hlift : ∀ t, Complex.exp (L t) = z t) :
    ∃ n : ℤ, (L T).im - (L 0).im = turnAngle * n := by
  have he : Complex.exp (L T) = Complex.exp (L 0) := by rw [hlift, hlift, hperiod]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  refine ⟨n, ?_⟩
  have hi := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im] at hi
  norm_num [Complex.mul_re, Complex.mul_im] at hi
  dsimp [turnAngle]
  linarith

lemma exp_polar (w : ℂ) : Complex.exp w = polarPoint ‖Complex.exp w‖ w.im := by
  rw [polarPoint, direction, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  exact (Complex.re_add_im w).symm

/-- The physical logarithmic angular derivative equals the angular velocity
of the canonical field, at every nonzero polar point. -/
lemma logAngularVelocity (F : ℝ × ℂ → ℂ) (μ r θ : ℝ) (hr : 0 < r) :
    (transformedField F (μ, polarPoint r θ) / polarPoint r θ).im =
      angularVelocity F θ r μ := by
  have hrot := HopfReturnExpansion.polarVelocityIdentity F μ r θ hr.ne'
  have hAD := HopfReturnExpansion.direction_conj_mul θ
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hD : direction θ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hAD
    exact zero_ne_one hAD
  have hV : transformedField F (μ, polarPoint r θ) =
      direction θ * ((radialVelocity F θ r μ : ℂ) + I * (r * angularVelocity F θ r μ)) := by
    calc
      _ = direction θ * ((starRingEnd ℂ) (direction θ) * transformedField F (μ, polarPoint r θ)) := by
        rw [← mul_assoc, mul_comm (direction θ) ((starRingEnd ℂ) (direction θ)), hAD, one_mul]
      _ = _ := congrArg (fun v : ℂ => direction θ * v) hrot
  have hquot : transformedField F (μ, polarPoint r θ) / polarPoint r θ =
      (radialVelocity F θ r μ : ℂ) / (r : ℂ) + I * (angularVelocity F θ r μ : ℂ) := by
    rw [hV, polarPoint]
    push_cast
    field_simp [hrC, hD]
    <;> ring
  rw [hquot]
  simp [Complex.div_im]

/-- A logarithm lift of a genuine physical trajectory differentiates to the
actual angular equation. No principal-argument branch cut is crossed. -/
theorem logLift_angle_derivative (F : ℝ × ℂ → ℂ) {μ : ℝ} {z L : ℝ → ℂ}
    (hL : Continuous L) (hlift : ∀ t, Complex.exp (L t) = z t)
    (hz : ∀ t, HasDerivAt z (transformedField F (μ, z t)) t) :
    ∀ t, HasDerivAt (fun s => (L s).im)
      (angularVelocity F (L t).im ‖z t‖ μ) t := by
  intro t
  have hnz : z t ≠ 0 := by rw [← hlift t]; exact Complex.exp_ne_zero _
  have hp : z t = polarPoint ‖z t‖ (L t).im := by
    rw [← hlift t]
    exact exp_polar _
  have hd := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt t
    (logLift_hasDerivAt hL.continuousAt hlift (hz t))
  have hangle : (transformedField F (μ, z t) / z t).im =
      angularVelocity F (L t).im ‖z t‖ μ := by
    simpa only [← hp] using
      logAngularVelocity F μ ‖z t‖ (L t).im (norm_pos_iff.mpr hnz)
  simpa only [Function.comp_def, Complex.imCLM_apply, hangle] using hd

/-- Every sufficiently confined physical periodic trajectory has a strictly
increasing global phase lift and positive integral winding over its period. -/
theorem sourcePhaseLift (F : ℝ × ℂ → ℂ) (ω : ℝ) (hF : SourceHypotheses F ω) :
    ∃ ε > 0, ∃ σ > 0, ∀ μ : ℝ, |μ| < ε →
      ∀ (z : ℝ → ℂ) (T : ℝ),
        IsPeriodicSolution (fun w => transformedField F (μ, w)) z T →
        (∀ t, ‖z t‖ < σ) →
        ∃ L : ℝ → ℂ, Continuous L ∧ (∀ t, Complex.exp (L t) = z t) ∧
          StrictMono (fun t => (L t).im) ∧
          (∀ t, HasDerivAt (fun s => (L s).im)
            (angularVelocity F (L t).im ‖z t‖ μ) t) ∧
          ∃ n : ℤ, 0 < n ∧ (L T).im - (L 0).im = turnAngle * n := by
  obtain ⟨ε₁, hε₁, σ₁, hσ₁, hlocal⟩ := sourceLocalLipschitz F ω hF
  obtain ⟨ε₂, hε₂, σ₂, hσ₂, _, hangular⟩ :=
    HopfReturnExpansion.polarNeighborhood F ω hF.1 hF.2.1 hF.2.2.1 hF.2.2.2
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, min σ₁ σ₂, lt_min hσ₁ hσ₂, ?_⟩
  intro μ hμ z T hz hstay
  obtain ⟨hzero, K, hK⟩ := hlocal μ (hμ.trans_le (min_le_left _ _))
  have hnonzero : ∀ t, z t ≠ 0 := periodicSolution_ne_equilibrium hK
    (Metric.mem_closedBall_self hσ₁.le) hzero hz (by
      rintro x ⟨t, rfl⟩
      have hh := (hstay t).trans_le (min_le_left σ₁ σ₂)
      exact Metric.mem_closedBall.mpr (by simpa using hh.le))
  have hcont : Continuous z := continuous_iff_continuousAt.mpr
    (fun t => (hz.2.2.1 t).continuousAt)
  obtain ⟨L, hL, hl0, hlift⟩ := continuousLogLift hcont hnonzero
    (Complex.log (z 0)) (Complex.exp_log (hnonzero 0))
  have hder := logLift_angle_derivative F hL hlift hz.2.2.1
  have hmono : StrictMono (fun t => (L t).im) := by
    apply strictMono_of_deriv_pos
    intro t
    rw [(hder t).deriv]
    have hh := hangular μ ‖z t‖ (L t).im
      (hμ.trans_le (min_le_right _ _))
      (by simpa only [abs_norm] using (hstay t).trans_le (min_le_right σ₁ σ₂))
    linarith [hF.2.1]
  obtain ⟨n, hn⟩ := logLift_winding (by simpa using hz.2.1 0) hlift
  have hnpos : 0 < (n : ℝ) := by
    have hh := hmono hz.1
    dsimp [turnAngle] at hn
    nlinarith [Real.pi_pos]
  refine ⟨L, hL, hlift, hmono, hder, n, ?_, hn⟩
  exact_mod_cast hnpos

/-- Positive integral phase winding forces an actual positive-ray crossing. -/
theorem phaseRayCrossing {z L : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hL : Continuous L) (hlift : ∀ t, Complex.exp (L t) = z t)
    {n : ℤ} (hn : 0 < n) (hwind : (L T).im - (L 0).im = turnAngle * n) :
    ∃ t ∈ Icc 0 T, positiveRay (z t) := by
  let a := (L 0).im
  let k := Int.ceil (a / turnAngle)
  have hturn : 0 < turnAngle := Real.two_pi_pos
  have hlo : a ≤ turnAngle * (k : ℝ) := by
    have hh := Int.le_ceil (a / turnAngle)
    simpa only [k, mul_comm] using (div_le_iff₀ hturn).mp hh
  have hup : turnAngle * (k : ℝ) < a + turnAngle := by
    have hh := Int.ceil_lt_add_one (a / turnAngle)
    have ht := (mul_lt_mul_iff_of_pos_left hturn).mpr hh
    dsimp [k]
    field_simp at ht
    nlinarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbound : turnAngle * (k : ℝ) ≤ (L T).im := by
    dsimp [a] at hlo hup
    nlinarith
  have hφ : Continuous (fun t => (L t).im) := Complex.continuous_im.comp hL
  obtain ⟨t, ht, hat⟩ := intermediate_value_Icc (f := fun t => (L t).im)
    hT.le hφ.continuousOn ⟨hlo, hbound⟩
  change (L t).im = turnAngle * (k : ℝ) at hat
  have hd : direction (turnAngle * (k : ℝ)) = 1 := by
    simpa [direction, turnAngle, mul_comm] using Complex.exp_mul_I_periodic.int_mul_eq k
  have hp : z t = (‖z t‖ : ℂ) := by
    have he := exp_polar (L t)
    rw [hlift t, hat] at he
    simpa [polarPoint, hd] using he
  refine ⟨t, ht, ?_⟩
  constructor
  · rw [hp]; simp
  · rw [hp]
    simpa using norm_pos_iff.mpr (show z t ≠ 0 by rw [← hlift t]; exact Complex.exp_ne_zero _)

/-- Section intersection is derived from positive winding, without a global
section or an assumed first-return fixed point. -/
theorem containedSection : ContainedSection := by
  intro F ω hF
  obtain ⟨ε, hε, σ, hσ, hphase⟩ := sourcePhaseLift F ω hF
  refine ⟨ε, hε, σ, hσ, ?_⟩
  intro μ hμ Γ hΓ hstay
  obtain ⟨z, T, hz, rfl⟩ := hΓ
  have hb : ∀ t, ‖z t‖ < σ := by
    intro t
    simpa using hstay (mem_range_self t)
  obtain ⟨L, hL, hlift, _, _, n, hn, hwind⟩ := hphase μ hμ z T hz hb
  obtain ⟨t, ht, hcross⟩ := phaseRayCrossing hz.1 hL hlift hn hwind
  refine ⟨(z t).re, hcross.2, (Complex.re_le_norm _).trans_lt (hb t), ?_⟩
  have he : ((z t).re : ℂ) = z t := by
    apply Complex.ext
    · simp
    · simpa using hcross.1.symm
  rw [he]
  exact mem_range_self t


-- Compile-checked 2026-11-04 against current D13Unified.Ch16.HopfPeriodicOrbitBridge.
-- Paste after inverseCoordinateTransport inside the existing namespace.
-- Uses only the existing accepted imports and helper theorems.

theorem uniformCoordinateNeighborhood (F : ℝ × ℂ → ℂ) {ε ρ σ : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ) (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hcoord : CoordinateValidity F ε ρ) :
    ∃ η > 0, ∃ κ > 0, ∃ U : Set ℂ,
      η ≤ ε ∧ κ < σ ∧ IsOpen U ∧ (0 : ℂ) ∈ U ∧
      (∀ μ w, |μ| < η → ‖w‖ < κ → coordinate F μ w ∈ U) ∧
      ∃ e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ),
        (e : ℝ × ℂ → ℝ × ℂ) = familyCoordinate F ∧
        stateParameterBox η σ ⊆ e.source ∧
        (∀ μ x, |μ| < η → x ∈ U →
          (μ, x) ∈ e.target ∧ (e.symm (μ, x)).1 = μ ∧ ‖(e.symm (μ, x)).2‖ < σ) ∧
        (∀ μ : ℝ, |μ| < η →
          ∀ Γ : Set ℂ, IsPeriodicOrbit (fun x => F (μ, x)) Γ → Γ ⊆ U →
            ∃ (z : ℝ → ℂ) (T : ℝ),
              IsPeriodicSolution (fun x => F (μ, x)) z T ∧ range z = Γ ∧
              IsPeriodicSolution (fun w => transformedField F (μ, w))
                (fun t => (e.symm (μ, z t)).2) T ∧
              (∀ t : ℝ, ‖(e.symm (μ, z t)).2‖ < σ ∧
                coordinate F μ (e.symm (μ, z t)).2 = z t) ∧
              Γ = coordinate F μ '' range (fun t => (e.symm (μ, z t)).2)) := by
  obtain ⟨e, he, hsrc, hparam, hreg⟩ := hcoord
  have h0 : (0, 0) ∈ stateParameterBox ε ρ := by
    simpa [stateParameterBox] using And.intro hε hρ
  have he0 : e (0, 0) = (0, 0) := by
    rw [he]
    simp [familyCoordinate, coordinate_zero]
  have hi0 : e.symm (0, 0) = (0, 0) :=
    (congrArg e.symm he0.symm).trans (e.left_inv (hsrc h0))
  have ht0 : (0, 0) ∈ e.target := he0 ▸ e.map_source (hsrc h0)
  have hc : ContinuousAt e.symm (0, 0) := by
    rw [← he0]
    exact (hreg (0, 0) h0).2.1.continuousAt
  have hsmall : ∀ᶠ y : ℝ × ℂ in nhds (0, 0), ‖(e.symm y).2‖ < σ :=
    hc.snd.norm.eventually (gt_mem_nhds (by simpa [hi0] using hσ))
  obtain ⟨b, hb, hball⟩ := Metric.eventually_nhds_iff.mp
    ((show ∀ᶠ y : ℝ × ℂ in nhds (0, 0), y ∈ e.target from
      e.open_target.mem_nhds ht0).and hsmall)
  let U : Set ℂ := Metric.ball 0 (b / 2)
  have hU0 : (0 : ℂ) ∈ U := Metric.mem_ball_self (by positivity)
  have hcont : ContinuousAt (fun q : ℝ × ℂ => coordinate F q.1 q.2) (0, 0) := by
    simpa only [he, familyCoordinate, Function.comp_def] using
      ((hreg (0, 0) h0).1.continuousAt.snd)
  have hforward : ∀ᶠ q : ℝ × ℂ in nhds (0, 0), coordinate F q.1 q.2 ∈ U :=
    hcont.eventually ((show IsOpen U from Metric.isOpen_ball).mem_nhds
      (by change coordinate F 0 0 ∈ U; rw [coordinate_zero]; exact hU0))
  obtain ⟨a, ha, hmap⟩ := Metric.eventually_nhds_iff.mp hforward
  let η := min ε (min (b / 2) (a / 2))
  let κ := min (σ / 2) (a / 2)
  have hη : 0 < η := lt_min hε (lt_min (by positivity) (by positivity))
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hηε : η ≤ ε := min_le_left _ _
  have htarget : ∀ μ x, |μ| < η → x ∈ U →
      (μ, x) ∈ e.target ∧ (e.symm (μ, x)).1 = μ ∧ ‖(e.symm (μ, x)).2‖ < σ := by
    intro μ x hμ hx
    have hdist : dist (μ, x) (0, 0) < b := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
      constructor
      · exact (hμ.trans_le ((min_le_right _ _).trans (min_le_left _ _))).trans (by linarith)
      · have hx' : ‖x‖ < b / 2 := by simpa [U] using hx
        linarith
    obtain ⟨htarget, hnorm⟩ := hball hdist
    exact ⟨htarget, hparam _ htarget, hnorm⟩
  have hκσ : κ < σ := (min_le_left (σ / 2) (a / 2)).trans_lt (by linarith)
  refine ⟨η, hη, κ, hκ, U, hηε, hκσ,
    Metric.isOpen_ball, hU0, ?_, e, he, ?_, htarget, ?_⟩
  · intro μ w hμ hw
    apply hmap (y := (μ, w))
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
    constructor
    · exact (hμ.trans_le ((min_le_right _ _).trans (min_le_right _ _))).trans (by linarith)
    · exact (hw.trans_le (min_le_right _ _)).trans (by linarith)
  · intro x hx
    exact hsrc ⟨hx.1.trans_le hηε, hx.2.trans_le hσρ⟩
  · intro μ hμ Γ hΓ hΓU
    obtain ⟨z, T, hz, hzΓ⟩ := hΓ
    have hzU : ∀ t, z t ∈ U := fun t => hΓU (hzΓ ▸ mem_range_self t)
    have hlift := inverseCoordinateTransport F e he hparam hreg
      (hμ.trans_le hηε) hz
      (fun t => (htarget μ (z t) hμ (hzU t)).1)
      (fun t => (htarget μ (z t) hμ (hzU t)).2.2.trans_le hσρ)
    refine ⟨z, T, hz, hzΓ, hlift.1, ?_, ?_⟩
    · intro t
      exact ⟨(htarget μ (z t) hμ (hzU t)).2.2, hlift.2.1 t⟩
    · rw [← hzΓ]
      exact hlift.2.2



-- Compile-checked 2026-11-04 against current D13Unified.Ch16.HopfPeriodicOrbitBridge.
-- Paste after logLift_angle_derivative inside existing namespace.

/-- A positive-ray initial point fixes the physical phase uniquely at zero.
The winding over a possibly repeated physical period is a positive natural. -/
theorem normalizedPhaseLift (F : ℝ × ℂ → ℂ) {ω μ σ r T : ℝ}
    {K : ℝ≥0} (hω : 0 < ω) (hσ : 0 < σ)
    (hzero : transformedField F (μ, 0) = 0)
    (hV : LipschitzOnWith K (fun w => transformedField F (μ, w))
      (Metric.closedBall 0 σ))
    (hang : ∀ s θ : ℝ, |s| < σ → ω / 2 < angularVelocity F θ s μ)
    {z : ℝ → ℂ}
    (hz : IsPeriodicSolution (fun w => transformedField F (μ, w)) z T)
    (hstay : ∀ t, ‖z t‖ < σ) (hr : 0 < r) (hz0 : z 0 = (r : ℂ)) :
    ∃ (α : ℝ → ℝ) (n : ℕ), Continuous α ∧ α 0 = 0 ∧ StrictMono α ∧
      (∀ t, HasDerivAt α (angularVelocity F (α t) ‖z t‖ μ) t) ∧
      (∀ t, z t = polarPoint ‖z t‖ (α t)) ∧
      0 < n ∧ α T = turnAngle * n := by
  have hnonzero : ∀ t, z t ≠ 0 := periodicSolution_ne_equilibrium hV
    (Metric.mem_closedBall_self hσ.le) hzero hz (by
      rintro x ⟨t, rfl⟩
      exact Metric.mem_closedBall.mpr (by simpa using (hstay t).le))
  have hcont : Continuous z := continuous_iff_continuousAt.mpr
    (fun t => (hz.2.2.1 t).continuousAt)
  have hinit : Complex.exp (Real.log r : ℂ) = z 0 := by
    rw [hz0, ← Complex.ofReal_exp, Real.exp_log hr]
  obtain ⟨L, hL, hL0, hlift⟩ := continuousLogLift hcont hnonzero
    (Real.log r : ℂ) hinit
  let α : ℝ → ℝ := fun t => (L t).im
  have hα0 : α 0 = 0 := by simp [α, hL0]
  have hder : ∀ t, HasDerivAt α (angularVelocity F (α t) ‖z t‖ μ) t :=
    logLift_angle_derivative F hL hlift hz.2.2.1
  have hmono : StrictMono α := by
    apply strictMono_of_deriv_pos
    intro t
    rw [(hder t).deriv]
    have hh := hang ‖z t‖ (α t) (by simpa only [abs_norm] using hstay t)
    linarith
  have hpolar : ∀ t, z t = polarPoint ‖z t‖ (α t) := by
    intro t
    rw [← hlift t]
    exact exp_polar (L t)
  obtain ⟨n, hn⟩ := logLift_winding (by simpa using hz.2.1 0) hlift
  have hnreal : 0 < (n : ℝ) := by
    have hh := hmono hz.1
    change α T - α 0 = turnAngle * n at hn
    rw [hα0, sub_zero] at hn
    dsimp [turnAngle] at hn
    nlinarith [Real.pi_pos]
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hnreal
  have hnNat : (0 : ℕ) < n.toNat := by omega
  have hncast : ((n.toNat : ℕ) : ℝ) = n := by
    exact_mod_cast Int.toNat_of_nonneg hnpos.le
  refine ⟨α, n.toNat, Complex.continuous_im.comp hL, hα0, hmono, hder, hpolar, hnNat, ?_⟩
  change α T - α 0 = turnAngle * n at hn
  simpa only [hα0, sub_zero, hncast] using hn



/-- Finite successive crossings of prescribed equally spaced phase levels. -/
theorem finitePhaseCrossings {α : ℝ → ℝ} {T A : ℝ} {n : ℕ}
    (hT : 0 ≤ T) (hA : 0 < A) (hα : ContinuousOn α (Icc 0 T))
    (hzero : α 0 = 0) (hend : α T = A * n)
    (hmono : StrictMonoOn α (Icc 0 T)) :
    ∃ times : ℕ → ℝ,
      times 0 = 0 ∧ times n = T ∧ StrictMonoOn times (Icc 0 n) ∧
      ∀ j ≤ n, times j ∈ Icc 0 T ∧ α (times j) = A * j := by
  have hex : ∀ j : ℕ, j ≤ n → ∃ t ∈ Icc 0 T, α t = A * j := by
    intro j hj
    apply intermediate_value_Icc hT hα
    rw [hzero, hend]
    constructor
    · positivity
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hA.le
  choose t ht using hex
  let times : ℕ → ℝ := fun j => if hj : j ≤ n then t j hj else 0
  have hnodes : ∀ j ≤ n, times j ∈ Icc 0 T ∧ α (times j) = A * j := by
    intro j hj
    simpa only [times, dif_pos hj] using ht j hj
  refine ⟨times, ?_, ?_, ?_, hnodes⟩
  · apply hmono.injOn (hnodes 0 (Nat.zero_le n)).1 ⟨le_rfl, hT⟩
    simpa [hzero] using (hnodes 0 (Nat.zero_le n)).2
  · apply hmono.injOn (hnodes n le_rfl).1 ⟨hT, le_rfl⟩
    exact (hnodes n le_rfl).2.trans hend.symm
  · intro j hj k hk hjk
    by_contra h
    have hh := hmono.monotoneOn (hnodes k hk.2).1 (hnodes j hj.2).1
      (le_of_not_gt h)
    rw [(hnodes k hk.2).2, (hnodes j hj.2).2] at hh
    have hjk' : (j : ℝ) < k := by exact_mod_cast hjk
    exact (not_le_of_gt (mul_lt_mul_of_pos_left hjk' hA)) hh


/-- A compact solution through a confined complete solution inherits its
confinement. The competing compact solution need not a priori stay in the
Lipschitz ball. -/
theorem compactSolution_eq_confined {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {V : E → E} {K : ℝ≥0} {R S : ℝ}
    {z v : ℝ → E} (hS : 0 ≤ S)
    (hV : LipschitzOnWith K V (Metric.closedBall 0 R))
    (hz : ∀ t, HasDerivAt z (V (z t)) t) (hstay : ∀ t, ‖z t‖ < R)
    (hv : ∀ t ∈ Icc 0 S, HasDerivWithinAt v (V (v t)) (Icc 0 S) t)
    (hzero : v 0 = z 0) : EqOn v z (Icc 0 S) := by
  have hvc : ContinuousOn v (Icc 0 S) := fun t ht => (hv t ht).continuousWithinAt
  have hzc : Continuous z := continuous_iff_continuousAt.mpr
    (fun t => (hz t).continuousAt)
  have hv0 : ‖v 0‖ < R := by rw [hzero]; exact hstay 0
  have hcompare : ∀ a ∈ Icc 0 S,
      (∀ t ∈ Icc 0 a, ‖v t‖ ≤ R) → EqOn v z (Icc 0 a) := by
    intro a ha hav
    apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => V)
      (s := fun _ => Metric.closedBall 0 R) (K := K)
    · intro t ht
      exact hV
    · exact hvc.mono (Icc_subset_Icc_right ha.2)
    · intro t ht
      exact (hv t ⟨ht.1, ht.2.le.trans ha.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans_le ha.2⟩)
    · intro t ht
      simpa using hav t (Ico_subset_Icc_self ht)
    · exact hzc.continuousOn
    · intro t ht
      exact (hz t).hasDerivWithinAt
    · intro t ht
      simpa using (hstay t).le
    · exact hzero
  have hvstay : ∀ t ∈ Icc 0 S, ‖v t‖ < R := by
    intro t ht
    by_contra h
    let A : Set ℝ := Icc 0 S ∩ (fun u => ‖v u‖) ⁻¹' Ici R
    have hAc : IsCompact A := by
      apply isCompact_Icc.of_isClosed_subset
        (hvc.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
      exact inter_subset_left
    have hAne : A.Nonempty := ⟨t, ht, le_of_not_gt h⟩
    obtain ⟨a, ha⟩ := hAc.exists_isLeast hAne
    have haI : a ∈ Icc 0 S := ha.1.1
    have hapos : 0 < a := by
      by_contra hn
      have ha0 : a = 0 := le_antisymm (le_of_not_gt hn) haI.1
      have hnorm : R ≤ ‖v 0‖ := by simpa [ha0] using ha.1.2
      exact (not_le_of_gt hv0) hnorm
    have hnormeq : ‖v a‖ = R := by
      obtain ⟨b, hb, heq⟩ := intermediate_value_Icc hapos.le
        (hvc.norm.mono (Icc_subset_Icc_right haI.2))
        (show R ∈ Icc ‖v 0‖ ‖v a‖ from ⟨hv0.le, ha.1.2⟩)
      have hab : a ≤ b := ha.2 ⟨⟨hb.1, hb.2.trans haI.2⟩, heq.ge⟩
      have hba : b = a := le_antisymm hb.2 hab
      simpa [hba] using heq
    have hav : ∀ b ∈ Icc 0 a, ‖v b‖ ≤ R := by
      intro b hb
      rcases eq_or_lt_of_le hb.2 with hba | hba
      · simpa [hba, hnormeq]
      · apply le_of_lt
        by_contra hn
        have hab : a ≤ b := ha.2 ⟨⟨hb.1, hb.2.trans haI.2⟩, le_of_not_gt hn⟩
        exact (not_le_of_gt hba) hab
    have heq := hcompare a haI hav ⟨hapos.le, le_rfl⟩
    have hlt : ‖v a‖ < R := by rw [heq]; exact hstay a
    exact (ne_of_lt hlt) hnormeq
  exact hcompare S ⟨hS, le_rfl⟩ (fun t ht => (hvstay t ht).le)


/-- Two trajectories that agree until the earlier of their first returns to a
section have the same return time and agree on their entire return segments. -/
theorem firstReturnSegments_eq {α : Type*} {S : Set α} {z w : ℝ → α} {T U : ℝ}
    (hT : 0 < T) (hU : 0 < U)
    (heq : EqOn z w (Icc 0 (min T U)))
    (hzT : z T ∈ S) (hwU : w U ∈ S)
    (hzfirst : ∀ t ∈ Ioo 0 T, z t ∉ S)
    (hwfirst : ∀ t ∈ Ioo 0 U, w t ∉ S) :
    T = U ∧ EqOn z w (Icc 0 T) := by
  have hTU : T = U := by
    rcases lt_trichotomy T U with hlt | hequal | hgt
    · have hh := heq ⟨hT.le, le_min le_rfl hlt.le⟩
      exact (hwfirst T ⟨hT, hlt⟩ (hh ▸ hzT)).elim
    · exact hequal
    · have hh := heq ⟨hU.le, le_min hgt.le le_rfl⟩
      exact (hzfirst U ⟨hU, hgt⟩ (hh.symm ▸ hwU)).elim
  refine ⟨hTU, ?_⟩
  simpa only [hTU, min_self] using heq

/-- Physical first turns agree as soon as ODE uniqueness identifies their
overlap. The comparison itself requires no global flow or ambient confinement
for either segment. -/
theorem firstAngularSegments_eq {z w : ℝ → ℂ} {T U : ℝ}
    (hT : 0 < T) (hU : 0 < U)
    (heq : EqOn z w (Icc 0 (min T U)))
    (hzT : positiveRay (z T)) (hwU : positiveRay (w U))
    (hzfirst : ∀ t ∈ Ioo 0 T, ¬ positiveRay (z t))
    (hwfirst : ∀ t ∈ Ioo 0 U, ¬ positiveRay (w t)) :
    T = U ∧ EqOn z w (Icc 0 T) :=
  firstReturnSegments_eq (S := {v | positiveRay v}) hT hU heq hzT hwU hzfirst hwfirst



/-- A uniform angular amplitude bound transfers to every physical time through
surjectivity of the actual clock. -/
theorem boundedTurnOfCurve (F : ℝ × ℂ → ℂ) (ω ε ρ μ r κ : ℝ)
    (u : ℝ → ℝ) (hrec : Specs.D13Unified.Ch16.HopfPolarReduction.ReconstructionOnChart F ε ρ)
    (hpos : ∀ θ s ν, |s| < ρ → |ν| < ε → ω / 2 < angularVelocity F θ s ν)
    (hμ : |μ| < ε) (hr : 0 < r) (hu0 : u 0 = r)
    (hu : ContinuousOn u (Icc 0 turnAngle))
    (hud : ∀ θ ∈ Icc 0 turnAngle,
      HasDerivWithinAt u (angularField F θ (u θ) μ) (Icc 0 turnAngle) θ)
    (hur : ∀ θ ∈ Icc 0 turnAngle, 0 < u θ ∧ u θ < ρ ∧ u θ < κ) :
    FullAngularTurn F ω μ r (u turnAngle) κ := by
  obtain ⟨T, hT, z, hc0, hcT, hcc, hcm, hcb, hcd, hzc, hzd,
    hzclock, hz0, hzT, hfirst⟩ := hrec μ r u hμ hr hu0 hu hud
      (fun θ hθ => ⟨(hur θ hθ).1, (hur θ hθ).2.1⟩)
  let clock := Specs.D13Unified.Ch16.HopfPolarReduction.physicalClock F μ u
  change clock turnAngle = T at hcT
  subst T
  refine ⟨u, clock, z, hu0, rfl, hc0, hT, hcm, hcb, ?_, hz0, hzT, ?_, ?_⟩
  · intro θ hθ
    exact ⟨(hur θ hθ).1, (hur θ hθ).2.2,
      hpos θ (u θ) μ (by rw [abs_of_pos (hur θ hθ).1]; exact (hur θ hθ).2.1) hμ,
      hud θ hθ, hcd θ hθ, hzclock θ hθ⟩
  · intro t ht
    obtain ⟨θ, hθ, heq⟩ := hcb.surjOn ht
    refine ⟨?_, (hzd t ht).1⟩
    rw [← heq, hzclock θ hθ, HopfReturnExpansion.polarPoint_norm,
      abs_of_pos (hur θ hθ).1]
    exact (hur θ hθ).2.2
  · intro t ht
    obtain ⟨θ, hθ, heq⟩ := hcb.surjOn ⟨ht.1.le, ht.2.le⟩
    have hθ0 : 0 < θ := by
      by_contra hn
      have hz : θ = 0 := le_antisymm (le_of_not_gt hn) hθ.1
      have hz' : t = 0 := by simpa only [hz, hc0] using heq.symm
      exact ht.1.ne' hz'
    have hθT : θ < turnAngle := by
      by_contra hn
      have hz : θ = turnAngle := le_antisymm hθ.2 (le_of_not_gt hn)
      have hz' : clock turnAngle = t := by simpa only [hz] using heq
      exact ht.2.ne hz'.symm
    rw [← heq, hzclock θ hθ]
    exact HopfReturnExpansion.polarPoint_not_positiveRay (u θ) θ (hur θ hθ).1 ⟨hθ0, hθT⟩

/-- For any prescribed normal radius there are uniformly smaller initial
radii whose genuine complete turn stays below that radius. -/
theorem sourceSmallTurns (F : ℝ × ℂ → ℂ) (ω : ℝ) (hF : SourceHypotheses F ω)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ η > 0, ∃ τ > 0, ∀ μ r : ℝ, |μ| < η → 0 < r → r < τ →
      ∃ p : ℝ, FullAngularTurn F ω μ r p κ := by
  obtain ⟨ε, hε, ρ, hρ, C, hC, G, hp, hrec⟩ :=
    HopfPolarReduction.polarReduction F ω hF.1 hF.2.1 hF.2.2.1 hF.2.2.2
  let d := HopfReturnExpansion.scalarData F ε ρ C G
  have hd : _root_.D13Unified.Ch16.HopfAngularScalarEstimates.Hypotheses d := HopfReturnExpansion.scalarHypotheses F ω ε ρ C G hε hρ hC hp
  obtain ⟨δ, η, L, a, b, hδ, hδρ, hη, hηε, hL, ha, hb, hLδ, hdom,
    hY, hsol, hzero, hQ, hfactor⟩ := HopfAngularScalarEstimates.normalizedEvolution d hd
  let τ := min δ (κ / (2 * L))
  have hτ : 0 < τ := lt_min hδ (by positivity)
  refine ⟨η, hη, τ, hτ, ?_⟩
  intro μ r hμ hr hrt
  have hrδ : r < δ := hrt.trans_le (min_le_left _ _)
  have hrμ : (r,μ) ∈ _root_.D13Unified.Ch16.HopfAngularScalarEstimates.parameterBox δ η :=
    ⟨abs_lt.mp (by rwa [abs_of_pos hr]), abs_lt.mp hμ⟩
  let u := fun θ => HopfAngularScalarEstimates.radialSolution d hd θ r μ
  have hI : Icc 0 turnAngle ⊆ Ioo a b := by
    intro θ hθ
    exact ⟨ha.trans_le hθ.1, hθ.2.trans_lt hb⟩
  obtain ⟨_, hder, hu0, hbounds⟩ := hsol r μ hrμ
  have hu : ContinuousOn u (Icc 0 turnAngle) :=
    (HopfAngularScalarEstimates.radialSolution_c2_on d hd
      (fun θ hθ => hdom ⟨hI hθ,hrμ⟩)).continuousOn
  have hur : ∀ θ ∈ Icc 0 turnAngle, 0 < u θ ∧ u θ < ρ ∧ u θ < κ := by
    intro θ hθ
    have hpositive : 0 < u θ := (hbounds θ hθ).2.2 hr
    have hh : |u θ| < ρ := (hbounds θ hθ).2.1
    refine ⟨hpositive, (le_abs_self _).trans_lt hh, ?_⟩
    have hsmall : L * r < κ / 2 := by
      have hrt' : r < κ / (2 * L) := hrt.trans_le (min_le_right _ _)
      have hmul := (lt_div_iff₀ (show 0 < 2 * L by positivity)).mp hrt'
      nlinarith
    calc
      u θ ≤ |u θ| := le_abs_self _
      _ ≤ L * r := by simpa only [abs_of_pos hr] using (hbounds θ hθ).1
      _ < κ / 2 := hsmall
      _ < κ := by linarith
  have hud : ∀ θ ∈ Icc 0 turnAngle,
      HasDerivWithinAt u (angularField F θ (u θ) μ) (Icc 0 turnAngle) θ := by
    intro θ hθ
    have hh := (hder θ (hI hθ)).2.2
    have hx : (θ,u θ,μ) ∈ Specs.D13Unified.Ch16.HopfPolarReduction.polarBox ε ρ :=
      ⟨by linarith [hθ.1], by dsimp [turnAngle] at hθ ⊢; linarith [hθ.2],
        by rw [abs_of_pos (hur θ hθ).1]; exact (hur θ hθ).2.1,
        hμ.trans hηε⟩
    rw [(hp.2.2.2.2.2 _ hx).2.1]
    exact hh.hasDerivWithinAt
  exact ⟨u turnAngle, boundedTurnOfCurve F ω ε ρ μ r κ u hrec hp.2.2.2.2.1
    (hμ.trans hηε) hr hu0 hu hud hur⟩



/-- A compact solution through a confined compact reference solution inherits its
confinement. The competing compact solution need not a priori stay in the
Lipschitz ball. -/
theorem compactSegments_eq_confined {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {V : E → E} {K : ℝ≥0} {R S : ℝ}
    {z v : ℝ → E} (hS : 0 ≤ S)
    (hV : LipschitzOnWith K V (Metric.closedBall 0 R))
    (hz : ∀ t ∈ Icc 0 S, HasDerivWithinAt z (V (z t)) (Icc 0 S) t)
    (hstay : ∀ t ∈ Icc 0 S, ‖z t‖ < R)
    (hv : ∀ t ∈ Icc 0 S, HasDerivWithinAt v (V (v t)) (Icc 0 S) t)
    (hzero : v 0 = z 0) : EqOn v z (Icc 0 S) := by
  have hvc : ContinuousOn v (Icc 0 S) := fun t ht => (hv t ht).continuousWithinAt
  have hzc : ContinuousOn z (Icc 0 S) := fun t ht => (hz t ht).continuousWithinAt
  have hv0 : ‖v 0‖ < R := by rw [hzero]; exact hstay 0 ⟨le_rfl, hS⟩
  have hcompare : ∀ a ∈ Icc 0 S,
      (∀ t ∈ Icc 0 a, ‖v t‖ ≤ R) → EqOn v z (Icc 0 a) := by
    intro a ha hav
    apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => V)
      (s := fun _ => Metric.closedBall 0 R) (K := K)
    · intro t ht
      exact hV
    · exact hvc.mono (Icc_subset_Icc_right ha.2)
    · intro t ht
      exact (hv t ⟨ht.1, ht.2.le.trans ha.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans_le ha.2⟩)
    · intro t ht
      simpa using hav t (Ico_subset_Icc_self ht)
    · exact hzc.mono (Icc_subset_Icc_right ha.2)
    · intro t ht
      exact (hz t ⟨ht.1, ht.2.le.trans ha.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans_le ha.2⟩)
    · intro t ht
      simpa using (hstay t ⟨ht.1, ht.2.le.trans ha.2⟩).le
    · exact hzero
  have hvstay : ∀ t ∈ Icc 0 S, ‖v t‖ < R := by
    intro t ht
    by_contra h
    let A : Set ℝ := Icc 0 S ∩ (fun u => ‖v u‖) ⁻¹' Ici R
    have hAc : IsCompact A := by
      apply isCompact_Icc.of_isClosed_subset
        (hvc.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
      exact inter_subset_left
    have hAne : A.Nonempty := ⟨t, ht, le_of_not_gt h⟩
    obtain ⟨a, ha⟩ := hAc.exists_isLeast hAne
    have haI : a ∈ Icc 0 S := ha.1.1
    have hapos : 0 < a := by
      by_contra hn
      have ha0 : a = 0 := le_antisymm (le_of_not_gt hn) haI.1
      have hnorm : R ≤ ‖v 0‖ := by simpa [ha0] using ha.1.2
      exact (not_le_of_gt hv0) hnorm
    have hnormeq : ‖v a‖ = R := by
      obtain ⟨b, hb, heq⟩ := intermediate_value_Icc hapos.le
        (hvc.norm.mono (Icc_subset_Icc_right haI.2))
        (show R ∈ Icc ‖v 0‖ ‖v a‖ from ⟨hv0.le, ha.1.2⟩)
      have hab : a ≤ b := ha.2 ⟨⟨hb.1, hb.2.trans haI.2⟩, heq.ge⟩
      have hba : b = a := le_antisymm hb.2 hab
      simpa [hba] using heq
    have hav : ∀ b ∈ Icc 0 a, ‖v b‖ ≤ R := by
      intro b hb
      rcases eq_or_lt_of_le hb.2 with hba | hba
      · simpa [hba, hnormeq]
      · apply le_of_lt
        by_contra hn
        have hab : a ≤ b := ha.2 ⟨⟨hb.1, hb.2.trans haI.2⟩, le_of_not_gt hn⟩
        exact (not_le_of_gt hba) hab
    have heq := hcompare a haI hav ⟨hapos.le, le_rfl⟩
    have hlt : ‖v a‖ < R := by rw [heq]; exact hstay a haI
    exact (ne_of_lt hlt) hnormeq
  exact hcompare S ⟨hS, le_rfl⟩ (fun t ht => (hvstay t ht).le)


/-- A genuine turn confined to a ball of ODE uniqueness determines the endpoint
of every competing genuine turn with the same initial section point. The
competing turn has no a priori confinement premise in this smaller ball. -/
theorem fullAngularTurn_endpoint_eq_confined {F : ℝ × ℂ → ℂ} {ω μ r p q ρ₁ ρ₂ R : ℝ}
    {K : ℝ≥0}
    (hV : LipschitzOnWith K (fun w => transformedField F (μ, w)) (Metric.closedBall 0 R))
    (hρ₁ : ρ₁ ≤ R)
    (h₁ : FullAngularTurn F ω μ r p ρ₁)
    (h₂ : FullAngularTurn F ω μ r q ρ₂) : p = q := by
  obtain ⟨u, clock, z, _, huT, _, hT, _, _, hangular, hz0, hzT, hphysical, hfirst⟩ := h₁
  obtain ⟨v, clock', w, _, hvU, _, hU, _, _, hangular', hw0, hwU, hphysical', hfirst'⟩ := h₂
  let T := clock turnAngle
  let U := clock' turnAngle
  have hp : 0 < p := by
    rw [← huT]
    exact (hangular turnAngle ⟨Real.two_pi_pos.le, le_rfl⟩).1
  have hq : 0 < q := by
    rw [← hvU]
    exact (hangular' turnAngle ⟨Real.two_pi_pos.le, le_rfl⟩).1
  have hsubT : Icc 0 (min T U) ⊆ Icc 0 T := Icc_subset_Icc_right (min_le_left _ _)
  have hsubU : Icc 0 (min T U) ⊆ Icc 0 U := Icc_subset_Icc_right (min_le_right _ _)
  have heq : EqOn z w (Icc 0 (min T U)) :=
    (compactSegments_eq_confined (le_min hT.le hU.le) hV
      (fun t ht => ((hphysical t (hsubT ht)).2).mono hsubT)
      (fun t ht => (hphysical t (hsubT ht)).1.trans_le hρ₁)
      (fun t ht => ((hphysical' t (hsubU ht)).2).mono hsubU)
      (hw0.trans hz0.symm)).symm
  obtain ⟨hTU, heqfull⟩ := firstAngularSegments_eq hT hU heq
    (by rw [hzT]; exact ⟨by simp, by simpa using hp⟩)
    (by rw [hwU]; exact ⟨by simp, by simpa using hq⟩) hfirst hfirst'
  have hpq : (p : ℂ) = (q : ℂ) := by
    calc
      (p : ℂ) = z T := hzT.symm
      _ = w T := heqfull ⟨hT.le, le_rfl⟩
      _ = w U := congrArg w hTU
      _ = (q : ℂ) := hwU
  exact_mod_cast hpq


lemma direction_sub_nat_turn (θ : ℝ) (j : ℕ) :
    direction (θ - turnAngle * j) = direction θ := by
  have hj : direction (turnAngle * j) = 1 := by
    simpa [direction, turnAngle, mul_comm] using Complex.exp_mul_I_periodic.nat_mul_eq j
  change Complex.exp (((θ - turnAngle * j : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I)
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  change Complex.exp ((θ : ℂ) * I) / direction (turnAngle * j) = _
  rw [hj, div_one]

lemma polarPoint_sub_nat_turn (r θ : ℝ) (j : ℕ) :
    polarPoint r (θ - turnAngle * j) = polarPoint r θ := by
  simp only [polarPoint, direction_sub_nat_turn]

/-- A phase interval between consecutive whole turns has no earlier
positive-ray intersection. -/
theorem phaseSegment_noEarlierRay {z : ℝ → ℂ} {α : ℝ → ℝ} {T a b : ℝ} {j : ℕ}
    (hmono : StrictMonoOn α (Icc 0 T))
    (hpolar : ∀ t ∈ Icc 0 T, z t = polarPoint ‖z t‖ (α t))
    (hpos : ∀ t ∈ Icc 0 T, 0 < ‖z t‖)
    (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T)
    (haa : α a = turnAngle * j) (hba : α b = turnAngle * (j + 1)) :
    ∀ t ∈ Ioo 0 (b - a), ¬ positiveRay (z (a + t)) := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hat : a + t ∈ Icc 0 T := by constructor <;> linarith [ha.1, hb.2]
  have hlo := hmono ha hat (show a < a + t by linarith)
  have hhi := hmono hat hb (show a + t < b by linarith)
  rw [haa] at hlo
  rw [hba] at hhi
  rw [hpolar (a + t) hat, ← polarPoint_sub_nat_turn ‖z (a + t)‖ (α (a + t)) j]
  apply HopfReturnExpansion.polarPoint_not_positiveRay _ _ (hpos _ hat)
  constructor
  · linarith
  · dsimp [turnAngle] at *
    push_cast at hhi
    nlinarith

/-- Positive phase winding enumerates a genuine finite return itinerary for
any prescribed scalar first-return map supplied by full turns. -/
theorem periodicItinerary_of_phase {F : ℝ × ℂ → ℂ} {ω μ d ρ R : ℝ}
    {P : ℝ × ℝ → ℝ} {K : ℝ≥0} {z : ℝ → ℂ} {T : ℝ} {n : ℕ} {α : ℝ → ℝ}
    (hz : IsPeriodicSolution (fun w => transformedField F (μ, w)) z T)
    (hn : 0 < n) (hdR : d ≤ R)
    (hV : LipschitzOnWith K (fun w => transformedField F (μ, w)) (Metric.closedBall 0 R))
    (hstay : ∀ t, ‖z t‖ < d) (hnorm : ∀ t, 0 < ‖z t‖)
    (hα : Continuous α) (hα0 : α 0 = 0) (hαT : α T = turnAngle * n)
    (hmono : StrictMono α)
    (hpolar : ∀ t, z t = polarPoint ‖z t‖ (α t))
    (hder : ∀ t, HasDerivAt α (angularVelocity F (α t) ‖z t‖ μ) t)
    (hturn : ∀ r, 0 < r → r < d → FullAngularTurn F ω μ r (P (r, μ)) ρ) :
    PeriodicItinerary F ω μ P d ρ (range z) := by
  obtain ⟨times, ht0, htn, htm, hnodesRaw⟩ := finitePhaseCrossings (A := turnAngle)
    hz.1.le Real.two_pi_pos hα.continuousOn hα0 hαT (hmono.strictMonoOn _)
  have hnodes : ∀ j ≤ n, times j ∈ Icc 0 T ∧ α (times j) = turnAngle * j := hnodesRaw
  let radii : ℕ → ℝ := fun j => ‖z (times j)‖
  have hnodez : ∀ j ≤ n, z (times j) = (radii j : ℂ) := by
    intro j hj
    rw [hpolar, (hnodes j hj).2]
    have hd : direction (turnAngle * j) = 1 := by
      simpa [direction, turnAngle, mul_comm] using Complex.exp_mul_I_periodic.nat_mul_eq j
    simp [radii, polarPoint, hd]
  refine ⟨z, T, n, times, radii, α, hz, rfl, hn, ht0, htn, htm,
    hα0, hαT, (hmono.strictMonoOn _), ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨hnorm t, hpolar t, (hder t).hasDerivWithinAt⟩
  · intro j hj
    exact ⟨hnorm _, hstay _, hnodez j hj, (hnodes j hj).2⟩
  · dsimp [radii]
    rw [htn, ht0]
    simpa using congrArg norm (hz.2.1 0)
  · intro j hj
    have hjn : j ≤ n := hj.le
    have hj1n : j + 1 ≤ n := by omega
    have htime : times j < times (j + 1) :=
      htm ⟨Nat.zero_le _, hjn⟩ ⟨Nat.zero_le _, hj1n⟩ (by omega)
    let S := times (j + 1) - times j
    have hS : 0 < S := sub_pos.mpr htime
    let w : ℝ → ℂ := fun t => z (times j + t)
    have hwder : ∀ t, HasDerivAt w (transformedField F (μ, w t)) t := by
      intro t
      convert! (hz.2.2.1 (times j + t)).scomp t
        ((hasDerivAt_id t).const_add (times j)) using 1 <;> simp [w]
    have hw0 : w 0 = (radii j : ℂ) := by simpa [w] using hnodez j hjn
    have hwS : w S = (radii (j + 1) : ℂ) := by
      simpa [w, S] using hnodez (j + 1) hj1n
    have hwfirst : ∀ t ∈ Ioo 0 S, ¬ positiveRay (w t) :=
      phaseSegment_noEarlierRay (hmono.strictMonoOn _) (fun t _ => hpolar t)
        (fun t _ => hnorm t) (hnodes j hjn).1 (hnodes (j + 1) hj1n).1
        (hnodes j hjn).2 (by simpa only [Nat.cast_add, Nat.cast_one] using (hnodes (j + 1) hj1n).2)
    obtain ⟨u, clock, v, hu0, huA, hc0, hcpos, hcm, hcb, hangular,
      hv0, hvA, hvphysical, hvfirst⟩ := hturn (radii j) (hnorm _) (hstay _)
    have heq : EqOn v w (Icc 0 (clock turnAngle)) :=
      compactSolution_eq_confined hcpos.le hV hwder
        (fun t => (hstay _).trans_le hdR)
        (fun t ht => (hvphysical t ht).2) (hv0.trans hw0.symm)
    have hp : 0 < P (radii j, μ) := by
      rw [← huA]
      exact (hangular turnAngle ⟨Real.two_pi_pos.le, le_rfl⟩).1
    obtain ⟨hcS, heqfull⟩ := firstAngularSegments_eq hcpos hS
      (heq.mono (Icc_subset_Icc_right (min_le_left _ _)))
      (by rw [hvA]; exact ⟨by simp, by simpa using hp⟩)
      (by rw [hwS]; exact ⟨by simp, by simpa only [Complex.ofReal_re] using (show 0 < radii (j + 1) from hnorm (times (j + 1)))⟩)
      hvfirst hwfirst
    have hP : radii (j + 1) = P (radii j, μ) := by
      have hc : (radii (j + 1) : ℂ) = (P (radii j, μ) : ℂ) := by
        calc
          (radii (j + 1) : ℂ) = w S := hwS.symm
          _ = w (clock turnAngle) := congrArg w hcS.symm
          _ = v (clock turnAngle) := (heq ⟨hcpos.le, le_rfl⟩).symm
          _ = (P (radii j, μ) : ℂ) := hvA
      exact_mod_cast hc
    refine ⟨hP, ?_, u, clock, v, hu0, huA.trans hP.symm, hc0, hcS, ?_, ?_⟩
    · refine ⟨S, hS, w, ?_, ?_, hw0, hwS, hnorm _, hwfirst⟩
      · exact fun t ht => (hwder t).continuousAt.continuousWithinAt
      · exact fun t ht => (hwder t).hasDerivWithinAt
    · intro θ hθ
      exact (hangular θ hθ).2.2.2.2.2
    · intro t ht
      have ht' : t ∈ Icc 0 (clock turnAngle) := by simpa only [hcS] using ht
      exact ⟨heq ht', (hvphysical t ht').1,
        by simpa only [hcS] using (hvphysical t ht').2⟩

/-- Every sufficiently confined periodic trace yields an itinerary for the
actual return data, even when the supplied return turn initially has a larger
confinement scale. -/
theorem sourceContainedItinerary (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (hF : SourceHypotheses F ω) :
    ∃ ε₁ > 0, ∃ σ₁ > 0,
      ∀ (ε ρ δ C : ℝ) (P Q : ℝ × ℝ → ℝ), ReturnData F ω ε ρ δ C P Q →
      ∀ (μ σ : ℝ), |μ| < ε₁ → |μ| < ε → 0 < σ → σ ≤ σ₁ → σ ≤ δ →
      ∀ Γ : Set ℂ,
        IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ →
        Γ ⊆ Metric.ball 0 σ → PeriodicItinerary F ω μ P σ ρ Γ := by
  obtain ⟨εv, hεv, Rv, hRv, hv⟩ := sourceLocalLipschitz F ω hF
  obtain ⟨εa, hεa, Ra, hRa, _, hangular⟩ :=
    HopfReturnExpansion.polarNeighborhood F ω hF.1 hF.2.1 hF.2.2.1 hF.2.2.2
  obtain ⟨εs, hεs, Rs, hRs, hs⟩ := containedSection F ω hF
  let R := min Rv Ra
  have hR : 0 < R := lt_min hRv hRa
  refine ⟨min εv (min εa εs), lt_min hεv (lt_min hεa hεs),
    min R Rs, lt_min hR hRs, ?_⟩
  intro ε ρ δ C P Q hret μ σ hμ₁ hμε hσ hσσ hσδ Γ hΓ hΓσ
  have hμv : |μ| < εv := hμ₁.trans_le (min_le_left _ _)
  have hμa : |μ| < εa := (hμ₁.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hμs : |μ| < εs := (hμ₁.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hσR : σ ≤ R := hσσ.trans (min_le_left _ _)
  have hσRs : σ ≤ Rs := hσσ.trans (min_le_right _ _)
  obtain ⟨hzero, K, hV⟩ := hv μ hμv
  have hVR : LipschitzOnWith K (fun w => transformedField F (μ, w))
      (Metric.closedBall 0 R) :=
    hV.mono (Metric.closedBall_subset_closedBall (min_le_left _ _))
  have hΓRs : Γ ⊆ Metric.ball 0 Rs :=
    hΓσ.trans (Metric.ball_subset_ball hσRs)
  obtain ⟨r, hr, _, hrΓ⟩ := hs μ hμs Γ hΓ hΓRs
  obtain ⟨z, T, hz, htrace⟩ := hΓ
  obtain ⟨a, ha⟩ := (show (r : ℂ) ∈ range z by rwa [htrace])
  let w : ℝ → ℂ := fun t => z (t + a)
  have hw : IsPeriodicSolution (fun w => transformedField F (μ, w)) w T :=
    periodicSolution_shift hz a
  have hw0 : w 0 = (r : ℂ) := by simpa [w] using ha
  have hwtrace : range w = Γ := by
    rw [← htrace]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t + a, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t - a, by simp [w]⟩
  have hwstay : ∀ t, ‖w t‖ < σ := by
    intro t
    have ht : w t ∈ Γ := by rw [← hwtrace]; exact mem_range_self t
    simpa using hΓσ ht
  have hwstayR : ∀ t, ‖w t‖ < R := fun t => (hwstay t).trans_le hσR
  have hnonzero : ∀ t, w t ≠ 0 := periodicSolution_ne_equilibrium hVR
    (Metric.mem_closedBall_self hR.le) hzero hw (by
      rintro x ⟨t, rfl⟩
      exact Metric.mem_closedBall.mpr (by simpa using (hwstayR t).le))
  obtain ⟨α, n, hα, hα0, hαmono, hαder, hαpolar, hn, hαT⟩ :=
    normalizedPhaseLift F hF.2.1 hR hzero hVR
      (fun s θ hs => hangular μ s θ hμa (hs.trans_le (min_le_right _ _)))
      hw hwstayR hr hw0
  rw [← hwtrace]
  apply periodicItinerary_of_phase hw hn hσR hVR hwstay
    (fun t => norm_pos_iff.mpr (hnonzero t)) hα hα0 hαT hαmono hαpolar hαder
  intro q hq hqσ
  exact hret.2.2.2.2.2.2.2.2.2.2.2 μ q hμε hq (hqσ.trans_le hσδ)


/-- Shrinking parameters and starting radii confines every fixed-return cycle
both in a prescribed normal ball and in a prescribed original neighborhood. -/
theorem uniformFixedReturnOrbits (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (hF : SourceHypotheses F ω) (ε ρ δ C : ℝ) (P Q : ℝ × ℝ → ℝ)
    (h : ReturnData F ω ε ρ δ C P Q)
    (σ κ ηU : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (hηU : 0 < ηU)
    (U : Set ℂ) (hmap : ∀ μ w, |μ| < ηU → ‖w‖ < κ → coordinate F μ w ∈ U) :
    ∃ η > 0, ∃ τ > 0, η ≤ ε ∧ η ≤ ηU ∧ τ < σ ∧
      ∀ μ r : ℝ, |μ| < η → 0 < r → r < τ → P (r, μ) = r →
        ∃ Γ : Set ℂ, IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ ∧
          (r : ℂ) ∈ Γ ∧ Γ ⊆ Metric.ball 0 σ ∧
          IsPeriodicOrbit (fun x => F (μ, x)) (coordinate F μ '' Γ) ∧
          coordinate F μ '' Γ ⊆ U := by
  obtain ⟨εL, hεL, R, hR, hlocal⟩ := sourceLocalLipschitz F ω hF
  let β := min (min σ κ) (min R ρ)
  have hβ : 0 < β := lt_min (lt_min hσ hκ) (lt_min hR h.2.1)
  have hβσ : β ≤ σ := (min_le_left _ _).trans (min_le_left _ _)
  have hβκ : β ≤ κ := (min_le_left _ _).trans (min_le_right _ _)
  have hβR : β ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have hβρ : β ≤ ρ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨εS, hεS, τS, hτS, hsmall⟩ := sourceSmallTurns F ω hF β hβ
  let η := min (min ε ηU) (min εL εS)
  let τ := min (min δ τS) (σ / 2)
  have hη : 0 < η := lt_min (lt_min h.1 hηU) (lt_min hεL hεS)
  have hτ : 0 < τ := lt_min (lt_min h.2.2.1 hτS) (by positivity)
  have hηε : η ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hηU' : η ≤ ηU := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨η, hη, τ, hτ, hηε, hηU', (min_le_right _ _).trans_lt (by linarith), ?_⟩
  intro μ r hμ hr hrt hfixed
  obtain ⟨_, K, hV⟩ := hlocal μ
    (hμ.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨p, hp⟩ := hsmall μ r
    (hμ.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hr
    (hrt.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hturn := h.2.2.2.2.2.2.2.2.2.2.2 μ r (hμ.trans_le hηε) hr
    (hrt.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hpr : p = r := (fullAngularTurn_endpoint_eq_confined hV hβR hp hturn).trans hfixed
  rw [hpr] at hp
  obtain ⟨Γ, hΓ, hrΓ, hΓβ⟩ := fixedTurnPeriodic F ω μ r β hr hp
  have hnormal : Γ ⊆ Metric.ball 0 σ := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_ball.mp (hΓβ hx)).trans_le hβσ)
  have himage : IsPeriodicOrbit (fun x => F (μ, x)) (coordinate F μ '' Γ) := by
    obtain ⟨z, T, hz, hzΓ⟩ := hΓ
    refine ⟨fun t => coordinate F μ (z t), T,
      coordinateTransport F h.2.2.2.2.2.1 (hμ.trans_le hηε) hz (fun t => ?_), ?_⟩
    · have hh := hΓβ (hzΓ ▸ mem_range_self t)
      exact (by simpa using hh : ‖z t‖ < β).trans_le hβρ
    · rw [← hzΓ]
      exact Set.range_comp (coordinate F μ) z
  refine ⟨Γ, hΓ, hrΓ, hnormal, himage, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact hmap μ w (hμ.trans_le hηU')
    ((by simpa using hΓβ hw : ‖w‖ < β).trans_le hβκ)



/-- Restrict local monotonicity and its finite-itinerary consequence to a
smaller rectangle; no invariant interval is introduced. -/
theorem noHigherReturnCycles_mono {P : ℝ × ℝ → ℝ} {d η d' η' : ℝ}
    (h : NoHigherReturnCycles P d η) (hd : d' ≤ d) (hη : η' ≤ η) :
    NoHigherReturnCycles P d' η' := by
  intro μ hμ
  have hsub : Ioo 0 d' ⊆ Ioo 0 d := Ioo_subset_Ioo le_rfl hd
  have hm := (h μ (hμ.trans_le hη)).1.mono hsub
  exact ⟨hm, fun r n hn hs hc => noHigherCycles hm.monotoneOn hn hs hc⟩

/-- The uniform geometric bridge for the actual original family and any
return data supplied upstream. Both confinement directions retain their own
radius, and the original-state neighborhood is fixed for all parameters. -/
theorem geometricBridge : GeometricBridge := by
  intro F ω hF ε ρ δ C P Q hret d η hd hdδ hη hηε
  obtain ⟨dM, hdM, ηM, hηM, hdMδ, hηMε, hmono⟩ :=
    localMonotonicity F ω hF ε ρ δ C P Q hret
  obtain ⟨εI, hεI, σI, hσI, hitinerary⟩ := sourceContainedItinerary F ω hF
  obtain ⟨εU, hεU, σU, hσU, huni⟩ := localOrbitUniqueness F ω hF
  let b := min d (min dM (min ρ (min σI σU)))
  have hb : 0 < b := lt_min hd (lt_min hdM (lt_min hret.2.1 (lt_min hσI hσU)))
  let σ := b / 2
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσb : σ < b := by dsimp [σ]; linarith
  have hσd : σ < d := hσb.trans_le (min_le_left _ _)
  have hσdM : σ ≤ dM := hσb.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσρ : σ < ρ := hσb.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hσI : σ ≤ σI := hσb.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hσU' : σ ≤ σU := hσb.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hσδ : σ ≤ δ := hσd.le.trans hdδ
  obtain ⟨ηC, hηC, κ, hκ, U, hηCε, hκσ, hU, hU0, hmap,
    e, he, hsrc, hinv, hlift⟩ := uniformCoordinateNeighborhood F hret.1 hret.2.1 hσ hσρ.le
      hret.2.2.2.2.2.1
  obtain ⟨ηF, hηF, τ, hτ, hηFε, hηFηC, hτσ, hfixed⟩ :=
    uniformFixedReturnOrbits F ω hF ε ρ δ C P Q hret σ κ ηC hσ hκ hηC U hmap
  let ε₀ := min η (min ηM (min εI (min εU ηF)))
  have hε₀ : 0 < ε₀ := lt_min hη (lt_min hηM (lt_min hεI (lt_min hεU hηF)))
  have hε₀η : ε₀ ≤ η := min_le_left _ _
  have hε₀ηM : ε₀ ≤ ηM := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀I : ε₀ ≤ εI := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀U : ε₀ ≤ εU := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε₀F : ε₀ ≤ ηF := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hε₀C : ε₀ ≤ ηC := hε₀F.trans hηFηC
  have hε₀ε : ε₀ ≤ ε := hε₀η.trans hηε
  have hcycle : NoHigherReturnCycles P σ ε₀ :=
    noHigherReturnCycles_mono hmono hσdM hε₀ηM
  refine ⟨ε₀, hε₀, σ, hσ, τ, hτ, U, hε₀η, hσd, hσρ, hτσ, hU, hU0,
    hcycle, ?_, ?_⟩
  · refine ⟨e, he, ?_, ?_, ?_⟩
    · intro x hx
      exact hsrc ⟨hx.1.trans_le hε₀C, hx.2⟩
    · intro μ x hμ hx
      exact hinv μ x (hμ.trans_le hε₀C) hx
    · intro μ hμ
      exact hlift μ (hμ.trans_le hε₀C)
  · intro μ hμ
    refine ⟨?_, ?_, ?_⟩
    · intro Γ hΓ hΓσ
      have hit := hitinerary ε ρ δ C P Q hret μ σ (hμ.trans_le hε₀I)
        (hμ.trans_le hε₀ε) hσ hσI hσδ Γ hΓ hΓσ
      obtain ⟨r, hr, hrσ, hrΓ, hPr⟩ := itinerary_fixed hcycle hμ hit
      exact ⟨hit, r, hr, hrσ.trans hσd, hrΓ, hPr⟩
    · intro r
      exact hfixed μ r (hμ.trans_le hε₀F)
    · intro Γ Λ hΓ hΛ hΓσ hΛσ r hr hrΓ hrΛ
      exact ((huni μ (hμ.trans_le hε₀U)).2 Γ Λ hΓ hΛ
        (hΓσ.trans (Metric.ball_subset_ball hσU'))
        (hΛσ.trans (Metric.ball_subset_ball hσU')) ⟨(r : ℂ), hrΓ, hrΛ⟩)


end D13Unified.Ch16.HopfPeriodicOrbitBridge
