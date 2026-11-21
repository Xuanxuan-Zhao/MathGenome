import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.ZetaSigmaConvergence
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.WeierstrassPeriods
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue

/-! For a lattice translation whose half is not in the lattice, the zeta
increment has derivative zero on the connected lattice complement. Oddness
at the negative half-translation identifies its constant as `2 * zeta (τ/2)`.
The same argument applied to `sigma (z+τ) / (sigma z * exp (eta* z))`
identifies its nonzero constant by oddness. The punctured germ identities
supply entire constant extensions across every apparent singularity; the
sigma formula itself holds at lattice points because both sides vanish.
No vanishing of arbitrary integration periods is used. -/

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.Ch22.ZetaSigmaQuasiperiods
open ZetaSigmaConvergence (lattice zeta sigma)
abbrev eta := Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods.eta

lemma lattice_compl_preconnected {ω₁ ω₂ : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    IsPreconnected (lattice ω₁ ω₂ : Set ℂ)ᶜ := by
  let L := WeierstrassSeries.periodPair h₁ h₂
  exact (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    (countable_of_Lindelof_of_discrete (X := L.lattice))).2

lemma add_notMem_lattice {ω₁ ω₂ τ z : ℂ} (hτ : τ ∈ lattice ω₁ ω₂)
    (hz : z ∉ lattice ω₁ ω₂) : z + τ ∉ lattice ω₁ ω₂ := by
  intro h
  exact hz (by simpa using sub_mem h hτ)

lemma generator_properties {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {ω : ℂ} (hω : ω ∈ ({ω₁, ω₂} : Set ℂ)) :
    ω ∈ lattice ω₁ ω₂ ∧ ω / 2 ∉ lattice ω₁ ω₂ := by
  let L := WeierstrassSeries.periodPair h₁ h₂
  rcases hω with h | h
  · subst ω
    exact ⟨L.ω₁_mem_lattice, L.ω₁_div_two_notMem_lattice⟩
  · have h := Set.mem_singleton_iff.mp h
    subst ω
    exact ⟨L.ω₂_mem_lattice, L.ω₂_div_two_notMem_lattice⟩

lemma zeta_shift_off_lattice {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {τ : ℂ} (hτ : τ ∈ lattice ω₁ ω₂) (hh : τ / 2 ∉ lattice ω₁ ω₂) :
    ∀ z ∉ lattice ω₁ ω₂, zeta ω₁ ω₂ (z + τ) = zeta ω₁ ω₂ z + eta ω₁ ω₂ τ := by
  let F : ℂ → ℂ := fun z => zeta ω₁ ω₂ (z + τ) - zeta ω₁ ω₂ z
  have hd (z : ℂ) (hz : z ∉ lattice ω₁ ω₂) : HasDerivAt F 0 z := by
    have ha := (ZetaSigmaConvergence.zeta_derivative ω₁ ω₂ h₁ h₂ (z + τ)
      (add_notMem_lattice hτ hz)).comp z ((hasDerivAt_id z).add_const τ)
    have hb := ZetaSigmaConvergence.zeta_derivative ω₁ ω₂ h₁ h₂ z hz
    have hp := (WeierstrassSeries.periodPair h₁ h₂).weierstrassP_add_coe z ⟨τ, hτ⟩
    change Specs.D12Complex.Ch22.ZetaSigmaConvergence.weierstrassP ω₁ ω₂ (z + τ) =
      Specs.D12Complex.Ch22.ZetaSigmaConvergence.weierstrassP ω₁ ω₂ z at hp
    convert ha.sub hb using 1
    · rfl
    · rw [hp]
      ring
  have hneg : -(τ / 2) ∉ lattice ω₁ ω₂ := fun h => hh (by simpa using neg_mem h)
  intro z hz
  have hconst := (ZetaSigmaConvergence.lattice_compl_open h₁ h₂).is_const_of_deriv_eq_zero
    (lattice_compl_preconnected h₁ h₂) (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) (x := z) (y := -(τ / 2)) hz hneg
  have he : F (-(τ / 2)) = eta ω₁ ω₂ τ := by
    have hodd : zeta ω₁ ω₂ (-(τ / 2)) = -zeta ω₁ ω₂ (τ / 2) :=
      ZetaSigmaConvergence.zeta_odd ω₁ ω₂ h₁ h₂ _
    change zeta ω₁ ω₂ (-(τ / 2) + τ) - zeta ω₁ ω₂ (-(τ / 2)) = 2 * zeta ω₁ ω₂ (τ / 2)
    rw [show -(τ / 2) + τ = τ / 2 by ring, hodd]
    ring
  have := hconst.trans he
  dsimp [F] at this
  exact (sub_eq_iff_eq_add.mp this).trans (add_comm _ _)

lemma sigma_derivative_off_lattice {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z : ℂ} (hz : z ∉ lattice ω₁ ω₂) :
    HasDerivAt (sigma ω₁ ω₂) (zeta ω₁ ω₂ z * sigma ω₁ ω₂ z) z := by
  have hd := (ZetaSigmaConvergence.sigma_entire ω₁ ω₂ h₁ h₂).2 z (mem_univ z)
  have hn := (ZetaSigmaConvergence.sigma_zero_iff ω₁ ω₂ h₁ h₂ z).not.mpr hz
  have he := (div_eq_iff hn).mp (ZetaSigmaConvergence.sigma_logDeriv ω₁ ω₂ h₁ h₂ z hz)
  exact he ▸ hd.hasDerivAt

lemma sigma_ratio_off_lattice {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {τ : ℂ} (hτ : τ ∈ lattice ω₁ ω₂) (hh : τ / 2 ∉ lattice ω₁ ω₂) :
    ∀ z ∉ lattice ω₁ ω₂,
      sigma ω₁ ω₂ (z + τ) / (sigma ω₁ ω₂ z * Complex.exp (eta ω₁ ω₂ τ * z)) =
        -Complex.exp (eta ω₁ ω₂ τ * (τ / 2)) := by
  let R : ℂ → ℂ := fun z => sigma ω₁ ω₂ (z + τ) /
    (sigma ω₁ ω₂ z * Complex.exp (eta ω₁ ω₂ τ * z))
  have hd (z : ℂ) (hz : z ∉ lattice ω₁ ω₂) : HasDerivAt R 0 z := by
    have ha := (sigma_derivative_off_lattice h₁ h₂ (add_notMem_lattice hτ hz)).comp z
      ((hasDerivAt_id z).add_const τ)
    have hb := (sigma_derivative_off_lattice h₁ h₂ hz).mul
      (((hasDerivAt_id z).const_mul (eta ω₁ ω₂ τ)).cexp)
    have hn := mul_ne_zero ((ZetaSigmaConvergence.sigma_zero_iff ω₁ ω₂ h₁ h₂ z).not.mpr hz)
      (Complex.exp_ne_zero (eta ω₁ ω₂ τ * z))
    convert ha.div hb hn using 1
    · rfl
    · simp only [Function.comp_def, Pi.mul_apply, id_eq]
      rw [zeta_shift_off_lattice h₁ h₂ hτ hh z hz]
      ring
  have hneg : -(τ / 2) ∉ lattice ω₁ ω₂ := fun h => hh (by simpa using neg_mem h)
  intro z hz
  have hconst := (ZetaSigmaConvergence.lattice_compl_open h₁ h₂).is_const_of_deriv_eq_zero
    (lattice_compl_preconnected h₁ h₂) (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) (x := z) (y := -(τ / 2)) hz hneg
  have he : R (-(τ / 2)) = -Complex.exp (eta ω₁ ω₂ τ * (τ / 2)) := by
    have hodd : sigma ω₁ ω₂ (-(τ / 2)) = -sigma ω₁ ω₂ (τ / 2) :=
      ZetaSigmaConvergence.sigma_odd ω₁ ω₂ h₁ h₂ _
    dsimp [R]
    rw [show -(τ / 2) + τ = τ / 2 by ring, hodd,
      show eta ω₁ ω₂ τ * -(τ / 2) = -(eta ω₁ ω₂ τ * (τ / 2)) by ring,
      Complex.exp_neg]
    have hn := (ZetaSigmaConvergence.sigma_zero_iff ω₁ ω₂ h₁ h₂ (τ / 2)).not.mpr hh
    field_simp [hn]
  exact hconst.trans he

theorem zeta_quasiperiod : Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods.zeta_quasiperiod_type := by
  intro ω₁ ω₂ h₁ h₂ ω hω a
  obtain ⟨hωL, hhalf⟩ := generator_properties h₁ h₂ hω
  filter_upwards [ZetaSigmaConvergence.off_lattice_eventually h₁ h₂ a] with z hz
  exact zeta_shift_off_lattice h₁ h₂ hωL hhalf z hz

theorem sigma_quasiperiod : Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods.sigma_quasiperiod_type := by
  intro ω₁ ω₂ h₁ h₂ ω hω z
  change sigma ω₁ ω₂ (z + ω) = -Complex.exp (eta ω₁ ω₂ ω * (z + ω / 2)) * sigma ω₁ ω₂ z
  obtain ⟨hωL, hhalf⟩ := generator_properties h₁ h₂ hω
  by_cases hz : z ∈ lattice ω₁ ω₂
  · have hza := add_mem hz hωL
    have ha : sigma ω₁ ω₂ z = 0 := (ZetaSigmaConvergence.sigma_zero_iff ω₁ ω₂ h₁ h₂ z).mpr hz
    have hb : sigma ω₁ ω₂ (z + ω) = 0 := (ZetaSigmaConvergence.sigma_zero_iff ω₁ ω₂ h₁ h₂ (z + ω)).mpr hza
    rw [ha, hb, mul_zero]
  · have he := sigma_ratio_off_lattice h₁ h₂ hωL hhalf z hz
    have hn := mul_ne_zero ((ZetaSigmaConvergence.sigma_zero_iff ω₁ ω₂ h₁ h₂ z).not.mpr hz)
      (Complex.exp_ne_zero (eta ω₁ ω₂ ω * z))
    have he := (div_eq_iff hn).mp he
    rw [he, mul_add, Complex.exp_add]
    ring

theorem zeta_pole_cancellation :
    Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods.zeta_pole_cancellation_type := by
  intro ω₁ ω₂ h₁ h₂ ω hω
  refine ⟨fun _ => eta ω₁ ω₂ ω, differentiable_const _, fun _ => rfl, ?_⟩
  intro a
  have he : (fun z => zeta ω₁ ω₂ (z + ω)) =ᶠ[𝓝[≠] a]
      (fun z => zeta ω₁ ω₂ z + eta ω₁ ω₂ ω) := zeta_quasiperiod ω₁ ω₂ h₁ h₂ ω hω a
  filter_upwards [he] with z hz
  change zeta ω₁ ω₂ (z + ω) - zeta ω₁ ω₂ z = eta ω₁ ω₂ ω
  rw [hz]
  ring

theorem sigma_ratio : Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods.sigma_ratio_type := by
  intro ω₁ ω₂ h₁ h₂ ω hω
  obtain ⟨hωL, hhalf⟩ := generator_properties h₁ h₂ hω
  refine ⟨-Complex.exp (eta ω₁ ω₂ ω * (ω / 2)), neg_ne_zero.mpr (Complex.exp_ne_zero _), rfl, ?_⟩
  intro a
  filter_upwards [ZetaSigmaConvergence.off_lattice_eventually h₁ h₂ a] with z hz
  exact sigma_ratio_off_lattice h₁ h₂ hωL hhalf z hz

theorem generator_quasiperiods :
    Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods.generator_quasiperiods_type := by
  intro ω₁ ω₂ h₁ h₂
  refine ⟨eta ω₁ ω₂ ω₁, eta ω₁ ω₂ ω₂, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact zeta_quasiperiod ω₁ ω₂ h₁ h₂ ω₁ (by simp)
  · exact zeta_quasiperiod ω₁ ω₂ h₁ h₂ ω₂ (by simp)
  · exact sigma_quasiperiod ω₁ ω₂ h₁ h₂ ω₁ (by simp)
  · exact sigma_quasiperiod ω₁ ω₂ h₁ h₂ ω₂ (by simp)

end D12Complex.Ch22.ZetaSigmaQuasiperiods
