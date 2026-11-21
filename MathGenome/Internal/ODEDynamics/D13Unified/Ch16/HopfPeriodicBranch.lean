import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfPeriodicBranch
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfReturnExpansion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfScalarBranchAnalysis
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfPeriodicOrbitBridge
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
The independent full `PeriodicBranch` specification is assembled from the
quantitative scalar branch and the geometric first-return correspondence.
All neighborhoods are fixed before choosing the parameter or periodic orbit.
-/
noncomputable section

namespace D13Unified.Ch16.HopfPeriodicBranch

open Set Filter
open Specs.D13Unified.Ch16.HopfPeriodicBranch
open Specs.D13Unified.Ch16.CubicHomologicalElimination
open Specs.D13Unified.Ch16.CubicNormalForm
open Specs.D13Unified.Ch16.HopfReturnExpansion

/-- The local interval need only contain this finite orbit. -/
theorem noHigherCycles : NoHigherCycles := by
  intro f s hf n r hn hit hcycle
  have hr : r ∈ s := by simpa using hit 0 (Nat.zero_le n)
  rcases lt_trichotomy r (f r) with hlt | heq | hgt
  · have hi : ∀ k ≤ n, r ≤ (f^[k]) r := by
      intro k hk
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hlt.le.trans (hf hr (hit k (by omega)) (ih (by omega)))
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hstrict : r < (f^[k + 1]) r := by
      rw [Function.iterate_succ_apply']
      exact hlt.trans_le (hf hr (hit k (by omega)) (hi k (by omega)))
    exact (ne_of_lt hstrict) hcycle.symm |>.elim
  · exact heq.symm
  · have hi : ∀ k ≤ n, (f^[k]) r ≤ r := by
      intro k hk
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (hf (hit k (by omega)) hr (ih (by omega))).trans hgt.le
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hstrict : (f^[k + 1]) r < r := by
      rw [Function.iterate_succ_apply']
      exact (hf (hit k (by omega)) hr (hi k (by omega))).trans_lt hgt
    exact (ne_of_lt hstrict) hcycle |>.elim

/-- The C² local graph theorem is applied to a genuine uncurried scalar map. -/
theorem implicitGraph : ImplicitGraph := by
  intro Q hQ hzero hinv
  let ψ := hQ.implicitFunction (by norm_num) hinv
  refine ⟨ψ, hQ.contDiffAt_implicitFunction (by norm_num) hinv,
    hQ.implicitFunction_apply_self (by norm_num) hinv, ?_⟩
  filter_upwards [hQ.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv] with q hq
  simpa only [hzero, eq_comm] using hq

/-- Repackage the upstream theorem, without adding any nondegeneracy premise
to that theorem or assuming any return-map certificate. -/
theorem sourceReturnData (F : ℝ × ℂ → ℂ) (ω : ℝ) (h : SourceHypotheses F ω) :
    ∃ ε > 0, ∃ ρ > 0, ∃ δ > 0, ∃ C > 0, ∃ P Q : ℝ × ℝ → ℝ,
      ReturnData F ω ε ρ δ C P Q := by
  obtain ⟨_, ε, hε, ρ, hρ, δ, hδ, C, hC, P, Q,
    hdρ, hc, hP, hQ, hE, hz, he, ht⟩ :=
    HopfReturnExpansion.returnExpansion F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
  exact ⟨ε, hε, ρ, hρ, δ, hδ, C, hC, P, Q,
    ⟨hdρ, hc, hP, hQ, hE, hz, he, ht⟩⟩

/-- Parameter derivative of the linear return displacement at the critical
parameter. This is computed from the actual spectral functions. -/
theorem linear_displacement_derivative (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (ha0 : spectralReal F 0 = 0) (hb0 : spectralImag F 0 = ω) (hω : 0 < ω)
    (ha : DifferentiableAt ℝ (spectralReal F) 0)
    (hb : DifferentiableAt ℝ (spectralImag F) 0) :
    HasDerivAt (fun μ => linearReturnFactor F μ - 1)
      (turnAngle * deriv (spectralReal F) 0 / ω) 0 := by
  have hh := (((ha.hasDerivAt.div hb.hasDerivAt (by simpa [hb0] using hω.ne')).const_mul
    turnAngle).exp).sub_const 1
  convert hh using 1 <;> simp [linearReturnFactor, angularLinear, ha0, hb0] <;>
    field_simp [hω.ne'] <;> ring

/-- The parameter derivative of Q at (0,0) is nonzero. No parameter
regularity of a freely chosen eigenvalue label is being assumed. -/
theorem quotient_parameter_derivative (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (h : SourceHypotheses F ω) (hε : 0 < ε)
    (hd : ReturnData F ω ε ρ δ C P Q) :
    HasDerivAt (fun μ => Q (0, μ))
      (turnAngle * deriv (spectralReal F) 0 / ω) 0 := by
  obtain ⟨ha0, hb0, η, hη, _, _, _, _, _, _, hs⟩ :=
    CubicNormalForm.normalForm F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
  have hs0 := hs 0 (by simpa using hη)
  have he : (fun μ => Q (0, μ)) =ᶠ[nhds 0]
      (fun μ => linearReturnFactor F μ - 1) := by
    have hm : ∀ᶠ μ : ℝ in nhds 0, |μ| < ε := by
      change {μ : ℝ | |μ| < ε} ∈ nhds 0
      simpa [Metric.ball, Real.dist_eq] using (Metric.ball_mem_nhds (0 : ℝ) hε)
    filter_upwards [hm] with μ hμ
    exact (hd.at_zero μ hμ).2
  exact (linear_displacement_derivative F ω ha0 hb0 h.2.1
    (hs0.2.1.differentiableAt (by norm_num))
    (hs0.2.2.1.differentiableAt (by norm_num))).congr_of_eventuallyEq he

/-- The full return data give a genuine C² implicit zero graph at the origin.
The quantitative expansion and global-on-a-small-interval branch classification
remain separate obligations. -/
theorem sourceImplicitGraph (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (h : SourceHypotheses F ω) (hε : 0 < ε) (hδ : 0 < δ)
    (hd : ReturnData F ω ε ρ δ C P Q) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = 0 ∧
      (∀ᶠ q in nhds (0, 0), Q q = 0 ↔ q.2 = ψ q.1) := by
  have hopen : IsOpen (returnBox δ ε) :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  have h00 : (0,0) ∈ returnBox δ ε := by simpa [returnBox] using And.intro hδ hε
  have hQ : ContDiffAt ℝ 2 Q (0,0) :=
    hd.smooth_quotient.contDiffAt (hopen.mem_nhds h00)
  have hzero : Q (0,0) = 0 := by
    obtain ⟨ha0, _, _⟩ := CubicNormalForm.normalForm F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
    rw [(hd.at_zero 0 (by simpa using hε)).2]
    simp [linearReturnFactor, angularLinear, ha0]
  let κ := turnAngle * deriv (spectralReal F) 0 / ω
  have hκ : κ ≠ 0 := by
    dsimp [κ, turnAngle]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      h.2.2.2.2.1) h.2.1.ne'
  have hdμ := quotient_parameter_derivative F ω ε ρ δ C P Q h hε hd
  have hcomp : fderiv ℝ Q (0,0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      κ • ContinuousLinearMap.id ℝ ℝ := by
    have hc := (hQ.differentiableAt (by norm_num)).hasFDerivAt.comp 0
      (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt
    convert hc.unique hdμ.hasFDerivAt using 1 <;>
      ext x <;> simp [κ, smul_eq_mul, mul_comm]
  have hinv : (fderiv ℝ Q (0,0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hcomp]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := κ⁻¹ • ContinuousLinearMap.id ℝ ℝ) <;>
      ext x <;> simp [smul_eq_mul, hκ, mul_assoc]
  exact implicitGraph Q hQ hzero hinv

/-- Dividing the value error is justified by the factorization at nonzero
radii; at zero the upstream extension supplies the value separately. -/
theorem quotient_error_bound (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (hd : ReturnData F ω ε ρ δ C P Q)
    (r μ : ℝ) (hr : |r| < δ) (hμ : |μ| < ε) :
    |Q (r,μ) - (linearReturnFactor F μ - 1) - cubicReturnCoefficient F μ * r ^ 2|
      ≤ C * |r| ^ 3 := by
  by_cases hz : r = 0
  · simp [hz, (hd.at_zero μ hμ).2]
  have ha : 0 < |r| := abs_pos.mpr hz
  have hmul : r * (Q (r,μ) - (linearReturnFactor F μ - 1) -
      cubicReturnCoefficient F μ * r ^ 2) = returnError F P (r,μ) := by
    dsimp [returnError]
    rw [(hd.estimates (r,μ) ⟨hr,hμ⟩).1]
    ring
  have he := (hd.estimates (r,μ) ⟨hr,hμ⟩).2.1
  rw [← hmul, abs_mul] at he
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith only [he]

/-- The radial derivative of the divided displacement vanishes at the
critical point. A cubic value bound proves this without assuming it. -/
theorem quotient_radial_derivative (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hd : ReturnData F ω ε ρ δ C P Q) :
    HasDerivAt (fun r => Q (r,0)) 0 0 := by
  let K := cubicReturnCoefficient F 0
  let g := fun r : ℝ => Q (r,0) - Q (0,0) - K * r ^ 2
  have hg0 : g 0 = 0 := by simp [g]
  have hg : g =O[nhds 0] (fun r : ℝ => r ^ 3) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨C, ?_⟩
    have hm : ∀ᶠ r : ℝ in nhds 0, |r| < δ := by
      change {r : ℝ | |r| < δ} ∈ nhds 0
      simpa [Metric.ball, Real.dist_eq] using (Metric.ball_mem_nhds (0 : ℝ) hδ)
    filter_upwards [hm] with r hr
    simpa only [g, K, (hd.at_zero 0 (by simpa using hε)).2,
      Real.norm_eq_abs, abs_pow] using
      quotient_error_bound F ω ε ρ δ C P Q hd r 0 hr (by simpa using hε)
  have hlo := hg.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by decide : 1 < 3))
  have hgd : HasDerivAt g 0 0 := by
    apply HasDerivAt.of_isLittleO
    simpa only [hg0, sub_zero, smul_zero] using hlo
  have hpol : HasDerivAt (fun r : ℝ => K * r ^ 2) 0 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).pow 2).const_mul K using 1 <;> norm_num
  have hh := (hgd.add hpol).add_const (Q (0,0))
  convert hh using 1 <;> simp only [Pi.add_apply, g, zero_add] <;>
    first | rfl | (funext r; ring)

/-- A C² return map with the upstream factorization is increasing on a
smaller fixed rectangle. The finite-cycle conclusion is then an order fact. -/
theorem sourceNoHigherReturnCycles (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (h : SourceHypotheses F ω) (hε : 0 < ε) (hδ : 0 < δ)
    (hd : ReturnData F ω ε ρ δ C P Q) :
    ∃ η > 0, ∃ d > 0, η ≤ ε ∧ d ≤ δ ∧ NoHigherReturnCycles P η d := by
  have hopen : IsOpen (returnBox δ ε) :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  have h00 : (0,0) ∈ returnBox δ ε := by simpa [returnBox] using And.intro hδ hε
  have hQ : ContDiffAt ℝ 2 Q (0,0) :=
    hd.smooth_quotient.contDiffAt (hopen.mem_nhds h00)
  have hP : ContDiffAt ℝ 2 P (0,0) :=
    hd.smooth_map.contDiffAt (hopen.mem_nhds h00)
  have hzero : Q (0,0) = 0 := by
    obtain ⟨ha0, _, _⟩ := CubicNormalForm.normalForm F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
    rw [(hd.at_zero 0 (by simpa using hε)).2]
    simp [linearReturnFactor, angularLinear, ha0]
  have hfactor : P =ᶠ[nhds (0,0)] (fun q => q.1 * (1 + Q q)) := by
    filter_upwards [hopen.mem_nhds h00] with q hq
    exact (hd.estimates q hq).1
  have hD0 : HasFDerivAt P (ContinuousLinearMap.fst ℝ ℝ ℝ) (0,0) := by
    have hh := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((0,0) : ℝ × ℝ))).mul
      ((hasFDerivAt_const (1 : ℝ) (0,0)).add (hQ.differentiableAt (by norm_num)).hasFDerivAt)
    have hh' : HasFDerivAt (fun q => q.1 * (1 + Q q))
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (0,0) := by
      convert! hh using 1 <;> simp [hzero, Pi.mul_apply, Pi.add_apply]
    exact hh'.congr_of_eventuallyEq hfactor
  have hcont : ContinuousAt (fun q => fderiv ℝ P q (1,0)) (0,0) :=
    (hP.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have hpos : ∀ᶠ q in nhds (0,0), 0 < fderiv ℝ P q (1,0) :=
    hcont.eventually (lt_mem_nhds (by change 0 < fderiv ℝ P (0,0) (1,0); rw [hD0.fderiv]; norm_num))
  obtain ⟨b, hb, hball⟩ := Metric.eventually_nhds_iff.mp hpos
  let η := min ε b
  let d := min δ b
  have hη : 0 < η := lt_min hε hb
  have hdpos : 0 < d := lt_min hδ hb
  have hsubset : returnBox d η ⊆ returnBox δ ε := by
    intro q hq
    exact ⟨hq.1.trans_le (min_le_left _ _), hq.2.trans_le (min_le_left _ _)⟩
  have hpos' : ∀ q ∈ returnBox d η, 0 < fderiv ℝ P q (1,0) := by
    intro q hq
    apply hball
    simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using
      And.intro (hq.1.trans_le (min_le_right _ _)) (hq.2.trans_le (min_le_right _ _))
  have hder : ∀ μ r : ℝ, |μ| < η → |r| < d →
      HasDerivAt (fun s => P (s,μ)) (fderiv ℝ P (r,μ) (1,0)) r := by
    intro μ r hμ hr
    have hp := (hd.smooth_map.contDiffAt
      (hopen.mem_nhds (hsubset (show (r,μ) ∈ returnBox d η from ⟨hr,hμ⟩)))).differentiableAt (by norm_num)
    have hi : HasDerivAt (fun s : ℝ => (s,μ)) (1,0) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_const r μ)
    exact hp.hasFDerivAt.comp_hasDerivAt r hi
  have hmono : ∀ μ : ℝ, |μ| < η → StrictMonoOn (fun r => P (r,μ)) (Ioo 0 d) := by
    intro μ hμ
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 d)
    · intro r hr
      exact (hder μ r hμ (by rw [abs_of_pos hr.1]; exact hr.2)).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Ioo] at hr
      rw [(hder μ r hμ (by rw [abs_of_pos hr.1]; exact hr.2)).deriv]
      exact hpos' (r,μ) ⟨by rw [abs_of_pos hr.1]; exact hr.2,hμ⟩
  refine ⟨η, hη, d, hdpos, min_le_left _ _, min_le_left _ _, hmono, ?_⟩
  intro μ r n hμ hn hit hcycle
  exact noHigherCycles _ _ (hmono μ hμ).monotoneOn n r hn hit hcycle

/-- The source zero graph is tangent to the parameter-zero axis. -/
theorem sourceFlatImplicitGraph (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (h : SourceHypotheses F ω) (hε : 0 < ε) (hδ : 0 < δ)
    (hd : ReturnData F ω ε ρ δ C P Q) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = 0 ∧ deriv ψ 0 = 0 ∧
      (∀ᶠ q in nhds (0, 0), Q q = 0 ↔ q.2 = ψ q.1) := by
  obtain ⟨ψ, hψ, hψ0, hgraph⟩ := sourceImplicitGraph F ω ε ρ δ C P Q h hε hδ hd
  have hopen : IsOpen (returnBox δ ε) :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  have h00 : (0,0) ∈ returnBox δ ε := by simpa [returnBox] using And.intro hδ hε
  have hQ := (hd.smooth_quotient.contDiffAt (hopen.mem_nhds h00)).differentiableAt (by norm_num)
  let D := fderiv ℝ Q (0,0)
  let κ := turnAngle * deriv (spectralReal F) 0 / ω
  have hκ : κ ≠ 0 := by
    dsimp [κ, turnAngle]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      h.2.2.2.2.1) h.2.1.ne'
  have hDr : D (1,0) = 0 := by
    have hh := hQ.hasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r,0)) 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 (0 : ℝ)))
    exact hh.unique (quotient_radial_derivative F ω ε ρ δ C P Q hε hδ hd)
  have hDμ : D (0,1) = κ := by
    have hh := hQ.hasFDerivAt.comp_hasDerivAt (f := fun μ : ℝ => (0,μ)) 0
      ((hasDerivAt_const 0 (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))
    exact hh.unique (quotient_parameter_derivative F ω ε ρ δ C P Q h hε hd)
  have hchain : HasDerivAt (fun r => Q (r,ψ r)) (D (1,deriv ψ 0)) 0 := by
    have hh := hQ.hasFDerivAt.comp_hasDerivAt_of_eq (f := fun r => (r,ψ r)) 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hψ.differentiableAt (by norm_num)).hasDerivAt)
      (by simp [hψ0])
    exact hh
  have ht : Tendsto (fun r => (r,ψ r)) (nhds 0) (nhds (0,0)) := by
    simpa [hψ0] using (continuousAt_id.prodMk hψ.continuousAt).tendsto
  have heq : (fun r => Q (r,ψ r)) =ᶠ[nhds 0] (fun _ => 0) := by
    filter_upwards [ht.eventually hgraph] with r hr
    exact hr.mpr rfl
  have hz : D (1,deriv ψ 0) = 0 :=
    (hchain.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const 0 (0 : ℝ))
  have hv : (1,deriv ψ 0) = (1,0) + deriv ψ 0 • ((0,1) : ℝ × ℝ) := by ext <;> simp
  rw [hv, map_add, map_smul, hDr, hDμ, zero_add, smul_eq_mul] at hz
  exact ⟨ψ, hψ, hψ0, (mul_eq_zero.mp hz).resolve_right hκ, hgraph⟩



/-- Restrict the genuine return data without changing the return map or chart. -/
theorem ReturnData.restrictParameter {F : ℝ × ℂ → ℂ} {ω ε ρ δ C ε' : ℝ}
    {P Q : ℝ × ℝ → ℝ} (h : ReturnData F ω ε ρ δ C P Q) (he : ε' ≤ ε) :
    ReturnData F ω ε' ρ δ C P Q := by
  have hsub : returnBox δ ε' ⊆ returnBox δ ε := fun _ hq => ⟨hq.1, hq.2.trans_le he⟩
  exact ⟨h.radius_lt, CubicNormalForm.coordinateValidity_mono h.coordinates he le_rfl,
    h.smooth_map.mono hsub, h.smooth_quotient.mono hsub, h.smooth_error.mono hsub,
    fun μ hμ => h.at_zero μ (hμ.trans_le he), fun q hq => h.estimates q (hsub hq),
    fun μ r hμ => h.turn μ r (hμ.trans_le he)⟩

/-- Both interfaces describe the same complete physical solutions and traces. -/
theorem periodicOrbit_iff (V : ℂ → ℂ) (Γ : Set ℂ) :
    IsPeriodicOrbit V Γ ↔
      Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge.IsPeriodicOrbit V Γ := by
  constructor
  · rintro ⟨z, T, hT, hp, hd, hn, hΓ⟩
    exact ⟨z, T, ⟨hT, hp, hd, hn⟩, hΓ.symm⟩
  · rintro ⟨z, T, ⟨hT, hp, hd, hn⟩, hΓ⟩
    exact ⟨z, T, hT, hp, hd, hn, hΓ.symm⟩

/-- Translate the scalar theorem, retaining its larger zero-graph box and
allowing the existence parameter interval to be made smaller for confinement. -/
theorem branchDescription_of_scalar {F : ℝ × ℂ → ℂ} {P Q : ℝ × ℝ → ℝ}
    {d δ₀ ε₀ ε₁ ε : ℝ} {ψ : ℝ → ℝ}
    (hd : 0 < d) (hdδ : d ≤ δ₀) (hε : 0 < ε) (he : ε ≤ ε₁) (he₁ : ε₁ ≤ ε₀)
    (h : Specs.D13Unified.Ch16.HopfScalarBranchAnalysis.BranchDescription F P Q d ε₀ ε₁ ψ) :
    ∃ C > 0, BranchDescription F P Q ε₀ δ₀ ε d C ψ := by
  obtain ⟨M, hM, hest⟩ := h.1.estimates
  have hc : Specs.D13Unified.Ch16.HopfScalarBranchAnalysis.branchCoefficient F ≠ 0 := by
    have hp := h.1.slope (d / 2) ⟨by linarith, by linarith⟩
    intro hz
    simp [hz] at hp
  have hmono : StrictMonoOn ψ (Ioo 0 d) ∨ StrictAntiOn ψ (Ioo 0 d) := by
    rcases lt_or_gt_of_ne hc with hn | hp
    · right
      intro r hr s hs hrs
      have hh := h.1.monotone hr hs hrs
      nlinarith
    · left
      intro r hr s hs hrs
      exact (mul_lt_mul_iff_right₀ hp).mp (h.1.monotone hr hs hrs)
  refine ⟨M, hM, hε, he.trans he₁, hd, hdδ, hM, h.1.regular, h.1.zero,
    h.1.flat, ?_, ?_, hmono, ?_, ?_, ?_⟩
  · intro r hr
    refine ⟨h.1.parameter_bound r hr, ?_, ?_⟩
    · simpa only [Specs.D13Unified.Ch16.HopfScalarBranchAnalysis.branchCoefficient,
        neg_div, neg_mul, sub_neg_eq_add] using (hest r hr).1
    · convert (hest r hr).2 using 1 <;>
        simp only [Specs.D13Unified.Ch16.HopfScalarBranchAnalysis.branchCoefficient,
          neg_div, mul_neg, neg_mul, sub_neg_eq_add, sq_abs] <;> ring
  · intro r μ hr hrd hμ
    have hq := h.1.quotient_zeros r μ (by rwa [abs_of_pos hr]) hμ
    exact ⟨(h.1.fixed_points r μ hr hrd hμ).trans hq.symm, hq⟩
  · intro μ hμ
    constructor
    · rintro ⟨r, hr, hp⟩
      have hroot := (h.1.fixed_points r μ hr.1 hr.2 ((hμ.trans_le he).trans_le he₁)).mp hp
      apply (h.2.1 μ (hμ.trans_le he)).1.mp
      refine ⟨r, ⟨hr.1, hr.2, hp⟩, ?_⟩
      intro s hs
      have hsr := (h.1.fixed_points s μ hs.1 hs.2.1 ((hμ.trans_le he).trans_le he₁)).mp hs.2.2
      apply hmono.elim (fun hm => hm.injOn ⟨hs.1, hs.2.1⟩ hr (hsr.symm.trans hroot))
        (fun hm => hm.injOn ⟨hs.1, hs.2.1⟩ hr (hsr.symm.trans hroot))
    · intro hside
      obtain ⟨r, hr, _⟩ := (h.2.1 μ (hμ.trans_le he)).1.mpr hside
      exact ⟨r, ⟨hr.1, hr.2.1⟩, hr.2.2⟩
  · intro μ r s hμ hr hs hpr hps
    have hμ₀ := (hμ.trans_le he).trans_le he₁
    have hEq := ((h.1.fixed_points r μ hr.1 hr.2 hμ₀).mp hpr).symm.trans
      ((h.1.fixed_points s μ hs.1 hs.2 hμ₀).mp hps)
    exact hmono.elim (fun hm => hm.injOn hr hs hEq) (fun hm => hm.injOn hr hs hEq)
  · intro η hη
    obtain ⟨ζ, hζ, _, hamp⟩ := h.2.2.1 η hη
    exact ⟨ζ, hζ, fun μ r hμ hr hp =>
      hamp μ r (hμ.trans_le (min_le_right _ _)) hr.1 hr.2 hp⟩

/-- Full Hopf existence, uniqueness and amplitude theorem. Scalar roots are
first confined to the smaller geometric starting radius. Every contained
physical orbit is then classified via its actual finite return itinerary. -/
theorem periodicBranch : PeriodicBranch := by
  intro F ω h
  have hs : Specs.D13Unified.Ch16.HopfScalarBranchAnalysis.SourceHypotheses F ω :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hg : Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge.SourceHypotheses F ω :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  obtain ⟨hK, εR, hεR, ρ, hρ, δR, hδR, CR, hCR, P, Q,
    hdρ, hcoord, hP, hQ, hE, hz, hb, ht⟩ :=
    HopfReturnExpansion.returnExpansion F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
  have hret : ReturnData F ω εR ρ δR CR P Q :=
    ⟨hdρ, hcoord, hP, hQ, hE, hz, hb, ht⟩
  have hscalar : Specs.D13Unified.Ch16.HopfScalarBranchAnalysis.ReturnData F ω εR δR CR P Q :=
    ⟨hK, hP, hQ, hE, hz, hb⟩
  have hgeom : Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge.ReturnData F ω εR ρ δR CR P Q :=
    ⟨hεR, hρ, hδR, hCR, hdρ, hcoord, hP, hQ, hE, hz, hb, ht⟩
  obtain ⟨η, hη, dM, hdM, hηR, hdMR, hcycles⟩ :=
    sourceNoHigherReturnCycles F ω εR ρ δR CR P Q h hεR hδR hret
  obtain ⟨d, hd, ε₀, hε₀, ε₁, hε₁, ψ, hddM, he₀R, he₁₀, hbranch⟩ :=
    HopfScalarBranchAnalysis.scalarBranchAnalysis F ω hs εR δR CR P Q
      hεR hδR hCR hscalar dM hdM hdMR
  have hddR := hddM.trans hdMR
  obtain ⟨εG, hεG, σ, hσ, τ, hτ, U, heGη, hσd, _, hτσ, hU, hU0,
    _, hechart, hgeometry⟩ :=
    HopfPeriodicOrbitBridge.geometricBridge F ω hg εR ρ δR CR P Q hgeom
      d (min η ε₁) hd hddR (lt_min hη hε₁) ((min_le_left _ _).trans hηR)
  obtain ⟨ν, hν, hνε₁, hshrink⟩ := hbranch.2.2.2 τ hτ (hτσ.trans hσd)
  let ε := min εG ν
  have hε : 0 < ε := lt_min hεG hν
  have heG : ε ≤ εG := min_le_left _ _
  have heν : ε ≤ ν := min_le_right _ _
  have he₁ : ε ≤ ε₁ := heν.trans hνε₁
  obtain ⟨C, hC, hdesc⟩ := branchDescription_of_scalar hd hddR hε he₁ he₁₀ hbranch
  have hμG {μ : ℝ} (hμ : |μ| < ε) : |μ| < εG := hμ.trans_le heG
  have rootSmall {μ r : ℝ} (hμ : |μ| < ε) (hr : r ∈ Ioo 0 d) (hp : P (r, μ) = r) :
      r < τ := hshrink μ r (hμ.trans_le heν) hr.1 hr.2 hp
  have hbridge : OrbitFixedPointBridge F P ε d σ := by
    intro μ hμ
    have hgeo := hgeometry μ (hμG hμ)
    refine ⟨?_, ?_⟩
    · intro Γ hΓ hΓσ
      obtain ⟨_, r, hr, hrd, hrΓ, hp⟩ := hgeo.1 Γ ((periodicOrbit_iff _ _).mp hΓ) hΓσ
      exact ⟨r, ⟨hr, hrd⟩, hrΓ, hp⟩
    · intro r hr hp
      obtain ⟨Γ, hΓ, hrΓ, hΓσ, _, _⟩ := hgeo.2.1 r hr.1 (rootSmall hμ hr hp) hp
      refine ⟨Γ, ⟨(periodicOrbit_iff _ _).mpr hΓ, hrΓ, hΓσ⟩, ?_⟩
      intro Δ hΔ
      exact hgeo.2.2 Δ Γ ((periodicOrbit_iff _ _).mp hΔ.1) hΓ hΔ.2.2 hΓσ r hr.1 hΔ.2.1 hrΓ
  have hrootSide : ∀ μ, |μ| < ε →
      ((∃ r ∈ Ioo 0 d, P (r, μ) = r) ↔
        spectralReal F μ * firstLyapunovCoefficient F < 0) := hdesc.2.2.2.2.2.2.2.2.2.2.2.1
  have hrootUnique : ∀ μ r s, |μ| < ε → r ∈ Ioo 0 d → s ∈ Ioo 0 d →
      P (r, μ) = r → P (s, μ) = s → r = s := hdesc.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hclass : OrbitClassification F ε σ := by
    intro μ hμ
    refine ⟨?_, ?_⟩
    · constructor
      · rintro ⟨Γ, hΓ, hΓσ⟩
        obtain ⟨r, hr, _, hp⟩ := (hbridge μ hμ).1 Γ hΓ hΓσ
        exact (hrootSide μ hμ).mp ⟨r, hr, hp⟩
      · intro hside
        obtain ⟨r, hr, hp⟩ := (hrootSide μ hμ).mpr hside
        obtain ⟨Γ, hΓ, _⟩ := (hbridge μ hμ).2 r hr hp
        exact ⟨Γ, hΓ.1, hΓ.2.2⟩
    · intro Γ Δ hΓ hΓσ hΔ hΔσ
      obtain ⟨r, hr, hrΓ, hpr⟩ := (hbridge μ hμ).1 Γ hΓ hΓσ
      obtain ⟨s, hs, hsΔ, hps⟩ := (hbridge μ hμ).1 Δ hΔ hΔσ
      have hrs := hrootUnique μ r s hμ hr hs hpr hps
      subst s
      exact (hgeometry μ (hμG hμ)).2.2 Γ Δ ((periodicOrbit_iff _ _).mp hΓ)
        ((periodicOrbit_iff _ _).mp hΔ) hΓσ hΔσ r hr.1 hrΓ hsΔ
  have hlift : ∀ μ, |μ| < ε → ∀ Γ,
      IsPeriodicOrbit (fun z => F (μ, z)) Γ → Γ ⊆ U →
      ∃ Δ, IsPeriodicOrbit (fun z => transformedField F (μ, z)) Δ ∧
        Δ ⊆ Metric.ball 0 σ ∧ Γ = coordinate F μ '' Δ := by
    obtain ⟨e, _, _, _, helift⟩ := hechart
    intro μ hμ Γ hΓ hΓU
    obtain ⟨z, T, _, _, hsol, hbound, himage⟩ :=
      helift μ (hμG hμ) Γ ((periodicOrbit_iff _ _).mp hΓ) hΓU
    refine ⟨range (fun t => (e.symm (μ, z t)).2),
      (periodicOrbit_iff _ _).mpr ⟨_, T, hsol, rfl⟩, ?_, himage⟩
    rintro w ⟨t, rfl⟩
    simpa using (hbound t).1
  have horiginal : OriginalOrbitClassification F ε σ := by
    refine ⟨U, hU, hU0, ?_⟩
    intro μ hμ
    refine ⟨?_, ?_, hlift μ hμ⟩
    · constructor
      · rintro ⟨Γ, hΓ, hΓU⟩
        obtain ⟨Δ, hΔ, hΔσ, _⟩ := hlift μ hμ Γ hΓ hΓU
        exact (hclass μ hμ).1.mp ⟨Δ, hΔ, hΔσ⟩
      · intro hside
        obtain ⟨r, hr, hp⟩ := (hrootSide μ hμ).mpr hside
        obtain ⟨Γ, _, _, _, hΓ, hΓU⟩ :=
          (hgeometry μ (hμG hμ)).2.1 r hr.1 (rootSmall hμ hr hp) hp
        exact ⟨coordinate F μ '' Γ, (periodicOrbit_iff _ _).mpr hΓ, hΓU⟩
    · intro Γ Λ hΓ hΓU hΛ hΛU
      obtain ⟨Δ, hΔ, hΔσ, hΓΔ⟩ := hlift μ hμ Γ hΓ hΓU
      obtain ⟨Θ, hΘ, hΘσ, hΛΘ⟩ := hlift μ hμ Λ hΛ hΛU
      rw [hΓΔ, hΛΘ, (hclass μ hμ).2 Δ Θ hΔ hΔσ hΘ hΘσ]
  have hcycles' : NoHigherReturnCycles P ε d := by
    have heη : ε ≤ η := heG.trans (heGη.trans (min_le_left _ _))
    have hm : ∀ μ, |μ| < ε → StrictMonoOn (fun r => P (r, μ)) (Ioo 0 d) :=
      fun μ hμ => (hcycles.1 μ (hμ.trans_le heη)).mono (Ioo_subset_Ioo le_rfl hddM)
    exact ⟨hm, fun μ r n hμ hn hit hcycle => noHigherCycles _ _ (hm μ hμ).monotoneOn n r hn hit hcycle⟩
  exact ⟨ε₀, hε₀, ρ, hρ, δR, hδR, CR, hCR, P, Q,
    ReturnData.restrictParameter hret he₀R, ε, d, C, ψ, hdesc, hcycles', σ, hσ, hσd,
    hbridge, hclass, horiginal⟩

end D13Unified.Ch16.HopfPeriodicBranch
