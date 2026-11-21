import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.ContinuationUniqueOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.GermsContinuation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.IdentityTheorem
import Mathlib.Topology.LocallyConstant.Basic

open Set Filter
open scoped Topology
noncomputable section

/-! Candidate-owned aliases expose the canonical constructions for declaration
and value checking. The independent Spec remains usable without this module. -/
namespace D12Complex.ContinuationUniqueOperations

abbrev leftParam :
    Specs.D12Complex.Ch19.ContinuationUniqueOperations.leftParam_type :=
  ContinuationOperations.leftParam

abbrev rightParam :
    Specs.D12Complex.Ch19.ContinuationUniqueOperations.rightParam_type :=
  ContinuationOperations.rightParam

abbrev concatPath :
    Specs.D12Complex.Ch19.ContinuationUniqueOperations.concatPath_type :=
  ContinuationOperations.concatPath

abbrev concatFamily :
    Specs.D12Complex.Ch19.ContinuationUniqueOperations.concatFamily_type :=
  @ContinuationOperations.concatFamily

end D12Complex.ContinuationUniqueOperations

namespace D12Complex.ContinuationOperations

private lemma analytic_of_holomorphic {U : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn U f) : AnalyticOnNhd ℂ f U := by
  intro z hz
  exact (LocalZeroFactorization.holomorphicNear_iff_analyticAt f z).mp ⟨U, hz, hf⟩

private lemma family_heq {A : Type*} {B : A → Type*} (F : ∀ a, B a)
    {a b : A} (h : a = b) : HEq (F a) (F b) := by
  cases h
  rfl

private lemma representation_of_heq {a b : ℂ} (hab : a = b)
    {ξ : HolomorphicGerm a} {η : HolomorphicGerm b} (h : HEq ξ η)
    {U : Set ℂ} {f : ℂ → ℂ} (hf : HolomorphicOn U f)
    (hr : ∃ hb : b ∈ U, η = HolomorphicGerm.ofFunction f hf hb) :
    ∃ ha : a ∈ U, ξ = HolomorphicGerm.ofFunction f hf ha := by
  cases hab
  obtain ⟨hb, hr⟩ := hr
  exact ⟨hb, (eq_of_heq h).trans hr⟩

private lemma representatives_eventuallyEq {a b : ℂ} (hab : a = b)
    {U V : Set ℂ} {f g : ℂ → ℂ} (hf : HolomorphicOn U f)
    (hg : HolomorphicOn V g) (ha : a ∈ U) (hb : b ∈ V)
    (h : HEq (HolomorphicGerm.ofFunction f hf ha) (HolomorphicGerm.ofFunction g hg hb)) :
    f =ᶠ[𝓝 b] g := by
  cases hab
  exact Germ.coe_eq.mp (congrArg Subtype.val (eq_of_heq h))

/-- On a connected open set, equality of one germ propagates to every germ. -/
private lemma germ_eq_propagates {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hc : IsPreconnected U) (hf : HolomorphicOn U f)
    (hg : HolomorphicOn U g) {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U)
    (h : (f : Germ (𝓝 a) ℂ) = (g : Germ (𝓝 a) ℂ)) :
    (f : Germ (𝓝 b) ℂ) = (g : Germ (𝓝 b) ℂ) := by
  have heq := (analytic_of_holomorphic hf).eqOn_of_preconnected_of_eventuallyEq
    (analytic_of_holomorphic hg) hc ha (Germ.coe_eq.mp h)
  exact Germ.coe_eq.mpr (heq.eventuallyEq_of_mem (hU.mem_nhds hb))

private lemma locally_constant_agreement {γ : unitInterval → ℂ}
    {Φ Ψ : GermFamily γ} (hγ : Continuous γ)
    (hΦ : LocallyRepresented γ Φ) (hΨ : LocallyRepresented γ Ψ) :
    IsLocallyConstant (fun t => Φ t = Ψ t) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro s
  obtain ⟨U, f, hf, hfr⟩ := (locallyRepresented_iff γ Φ).mp hΦ s
  obtain ⟨V, g, hg, hgr⟩ := (locallyRepresented_iff γ Ψ).mp hΨ s
  have hsU := (hfr.self_of_nhds).choose
  have hsV := (hgr.self_of_nhds).choose
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    ((hf.1.inter hg.1).mem_nhds ⟨hsU, hsV⟩)
  let B := Metric.ball (γ s) r
  have hB : γ s ∈ B := Metric.mem_ball_self hr
  have hfB : HolomorphicOn B f := ⟨Metric.isOpen_ball, fun z hz => hf.2 z (hsub hz).1⟩
  have hgB : HolomorphicOn B g := ⟨Metric.isOpen_ball, fun z hz => hg.2 z (hsub hz).2⟩
  have hequiv (t) (ht : γ t ∈ B)
      (hft : ∃ ha : γ t ∈ U, Φ t = HolomorphicGerm.ofFunction f hf ha)
      (hgt : ∃ ha : γ t ∈ V, Ψ t = HolomorphicGerm.ofFunction g hg ha) :
      (Φ t = Ψ t) ↔ (Φ s = Ψ s) := by
    obtain ⟨_, hft⟩ := hft
    obtain ⟨_, hgt⟩ := hgt
    obtain ⟨_, hfs⟩ := hfr.self_of_nhds
    obtain ⟨_, hgs⟩ := hgr.self_of_nhds
    rw [hft, hgt, hfs, hgs]
    constructor <;> intro h <;> apply Subtype.ext
    · exact germ_eq_propagates Metric.isOpen_ball Metric.isPreconnected_ball hfB hgB ht hB
        (congrArg Subtype.val h)
    · exact germ_eq_propagates Metric.isOpen_ball Metric.isPreconnected_ball hfB hgB hB ht
        (congrArg Subtype.val h)
  filter_upwards [hfr, hgr, hγ.continuousAt (Metric.isOpen_ball.mem_nhds hB)] with t ht hg htB
  exact propext (hequiv t htB ht hg)

theorem continuation_unique :
    Specs.D12Complex.Ch19.ContinuationUniqueOperations.continuation_unique_type := by
  intro Ω γ φ Φ Ψ hΦ hΨ t
  have hc := locally_constant_agreement hΦ.2.1 hΦ.2.2.2.2 hΨ.2.2.2.2
  have heq := hc.apply_eq_of_preconnectedSpace t 0
  exact heq.mpr (hΦ.2.2.2.1.trans hΨ.2.2.2.1.symm)

/-- Any continuous parameter map pulls local representatives back. -/
lemma locallyRepresented_comp {γ : unitInterval → ℂ} {Φ : GermFamily γ}
    (hΦ : LocallyRepresented γ Φ) {ρ : unitInterval → unitInterval}
    (hρ : Continuous ρ) : LocallyRepresented (γ ∘ ρ) (fun t => Φ (ρ t)) := by
  intro s
  obtain ⟨U, f, I, ho, hs, hr⟩ := hΦ (ρ s)
  exact ⟨U, f, ρ ⁻¹' I, ho.preimage hρ, hs, hr.1, fun t ht => hr.2 (ρ t) ht⟩

theorem continuation_reverse :
    Specs.D12Complex.Ch19.ContinuationUniqueOperations.continuation_reverse_type := by
  intro Ω γ φ Φ hΦ
  exact ⟨hΦ.1, hΦ.2.1.comp unitInterval.continuous_symm,
    fun t => hΦ.2.2.1 _, rfl,
    locallyRepresented_comp hΦ.2.2.2.2 unitInterval.continuous_symm⟩

theorem continuation_reparam :
    Specs.D12Complex.Ch19.ContinuationUniqueOperations.continuation_reparam_type := by
  intro Ω γ φ Φ ρ hΦ hρ
  have hzero : ρ 0 = 0 := by
    obtain ⟨s, hs⟩ := ρ.surjective 0
    apply le_antisymm
    · simpa [hs] using hρ.monotone (show (0 : unitInterval) ≤ s from bot_le)
    · exact bot_le
  have hone : ρ 1 = 1 := by
    obtain ⟨s, hs⟩ := ρ.surjective 1
    apply le_antisymm
    · exact le_top
    · simpa [hs] using hρ.monotone (show s ≤ (1 : unitInterval) from le_top)
  refine ⟨⟨hΦ.1, hΦ.2.1.comp ρ.continuous, fun t => hΦ.2.2.1 _, rfl,
    locallyRepresented_comp hΦ.2.2.2.2 ρ.continuous⟩, hzero, hone, ?_, ?_⟩
  · exact (family_heq Φ hzero).trans (heq_of_eq hΦ.2.2.2.1)
  · exact family_heq Φ hone

private lemma continuous_leftParam : Continuous leftParam :=
  continuous_projIcc.comp (continuous_const.mul continuous_subtype_val)

private lemma continuous_rightParam : Continuous rightParam :=
  continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)

private def midpoint : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

private lemma leftParam_midpoint : leftParam midpoint = 1 := by
  apply Subtype.ext
  norm_num [leftParam, midpoint, Set.projIcc]

private lemma rightParam_midpoint : rightParam midpoint = 0 := by
  apply Subtype.ext
  norm_num [rightParam, midpoint, Set.projIcc]

private lemma continuous_concatPath {γ δ : unitInterval → ℂ}
    (hγ : Continuous γ) (hδ : Continuous δ) (h : γ 1 = δ 0) :
    Continuous (concatPath γ δ) := by
  apply Continuous.if_le (hγ.comp continuous_leftParam) (hδ.comp continuous_rightParam)
    continuous_subtype_val continuous_const
  intro t ht
  have ht' : t = midpoint := Subtype.ext ht
  subst t
  simpa only [Function.comp_apply, leftParam_midpoint, rightParam_midpoint] using h

private lemma concatFamily_heq_left {γ δ : unitInterval → ℂ}
    (Φ : GermFamily γ) (Ψ : GermFamily δ) (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) :
    HEq (concatFamily Φ Ψ t) (Φ (leftParam t)) := by
  unfold concatFamily
  simp only [dite_eq_left h]
  exact cast_heq _ _

private lemma concatFamily_heq_right {γ δ : unitInterval → ℂ}
    (Φ : GermFamily γ) (Ψ : GermFamily δ) (t : unitInterval) (h : ¬(t : ℝ) ≤ 1 / 2) :
    HEq (concatFamily Φ Ψ t) (Ψ (rightParam t)) := by
  unfold concatFamily
  simp only [dite_eq_right h]
  exact cast_heq _ _

/-- At the seam, matching quotient classes identify the two local functions
on a neighborhood. This equality itself persists as an equality of germs. -/
private lemma locallyRepresented_concat {γ δ : unitInterval → ℂ}
    {Φ : GermFamily γ} {Ψ : GermFamily δ} (hδ : Continuous δ)
    (hΦ : LocallyRepresented γ Φ) (hΨ : LocallyRepresented δ Ψ)
    (hbase : γ 1 = δ 0) (hmatch : HEq (Φ 1) (Ψ 0)) :
    LocallyRepresented (concatPath γ δ) (concatFamily Φ Ψ) := by
  apply (locallyRepresented_iff _ _).mpr
  intro t
  rcases lt_trichotomy (t : ℝ) (1 / 2) with hlt | heq | hgt
  · obtain ⟨U, f, hf, hr⟩ := (locallyRepresented_iff γ Φ).mp hΦ (leftParam t)
    refine ⟨U, f, hf, ?_⟩
    have hlt' : ∀ᶠ s : unitInterval in 𝓝 t, (s : ℝ) < 1 / 2 :=
      (isOpen_lt continuous_subtype_val continuous_const).mem_nhds hlt
    filter_upwards [continuous_leftParam.continuousAt hr, hlt'] with s hs hsl
    exact representation_of_heq (by simp only [concatPath, ite_eq_left hsl.le])
      (concatFamily_heq_left Φ Ψ s hsl.le) hf hs
  · have ht : t = midpoint := Subtype.ext heq
    subst t
    obtain ⟨U, f, hf, hr⟩ := (locallyRepresented_iff γ Φ).mp hΦ 1
    obtain ⟨V, g, hg, hs⟩ := (locallyRepresented_iff δ Ψ).mp hΨ 0
    obtain ⟨ha, hfa⟩ := hr.self_of_nhds
    obtain ⟨hb, hgb⟩ := hs.self_of_nhds
    have hfg : f =ᶠ[𝓝 (δ 0)] g := by
      have H : HEq (HolomorphicGerm.ofFunction f hf ha)
          (HolomorphicGerm.ofFunction g hg hb) :=
        (heq_of_eq hfa.symm).trans (hmatch.trans (heq_of_eq hgb))
      exact representatives_eventuallyEq hbase hf hg ha hb H
    have hfmem : ∀ᶠ z in 𝓝 (δ 0), z ∈ U := by
      rw [← hbase]
      exact hf.1.mem_nhds ha
    have hr' : ∀ᶠ s in 𝓝 midpoint,
        ∃ ha : γ (leftParam s) ∈ U,
          Φ (leftParam s) = HolomorphicGerm.ofFunction f hf ha := by
      have H : Tendsto leftParam (𝓝 midpoint) (𝓝 (leftParam midpoint)) :=
        continuous_leftParam.continuousAt
      rw [leftParam_midpoint] at H
      exact H hr
    have hs' : ∀ᶠ s in 𝓝 midpoint,
        ∃ ha : δ (rightParam s) ∈ V,
          Ψ (rightParam s) = HolomorphicGerm.ofFunction g hg ha := by
      have H : Tendsto rightParam (𝓝 midpoint) (𝓝 (rightParam midpoint)) :=
        continuous_rightParam.continuousAt
      rw [rightParam_midpoint] at H
      exact H hs
    have hδr : ContinuousAt (fun s => δ (rightParam s)) midpoint :=
      (hδ.comp continuous_rightParam).continuousAt
    change Tendsto (fun s => δ (rightParam s)) (𝓝 midpoint)
      (𝓝 (δ (rightParam midpoint))) at hδr
    rw [rightParam_midpoint] at hδr
    refine ⟨U, f, hf, ?_⟩
    filter_upwards [hr', hs', hδr hfmem, hδr hfg.eventuallyEq_nhds] with s hsf hsg hU hfgs
    have hright : ∃ ha : δ (rightParam s) ∈ U,
        Ψ (rightParam s) = HolomorphicGerm.ofFunction f hf ha := by
      obtain ⟨_, hsg⟩ := hsg
      refine ⟨hU, ?_⟩
      rw [hsg]
      apply Subtype.ext
      exact Germ.coe_eq.mpr hfgs.symm
    by_cases h : (s : ℝ) ≤ 1 / 2
    · exact representation_of_heq (by simp only [concatPath, ite_eq_left h])
        (concatFamily_heq_left Φ Ψ s h) hf hsf
    · exact representation_of_heq (by simp only [concatPath, ite_eq_right h])
        (concatFamily_heq_right Φ Ψ s h) hf hright
  · obtain ⟨U, f, hf, hr⟩ := (locallyRepresented_iff δ Ψ).mp hΨ (rightParam t)
    refine ⟨U, f, hf, ?_⟩
    have hgt' : ∀ᶠ s : unitInterval in 𝓝 t, 1 / 2 < (s : ℝ) :=
      (isOpen_lt continuous_const continuous_subtype_val).mem_nhds hgt
    filter_upwards [continuous_rightParam.continuousAt hr, hgt'] with s hs hsl
    exact representation_of_heq (by simp only [concatPath, ite_eq_right (not_le.mpr hsl)])
      (concatFamily_heq_right Φ Ψ s (not_le.mpr hsl)) hf hs

theorem continuation_concat :
    Specs.D12Complex.Ch19.ContinuationUniqueOperations.continuation_concat_type := by
  intro Ω γ δ φ ψ Φ Ψ hΦ hΨ hbase hmatch
  have hm : HEq (Φ 1) (Ψ 0) :=
    hmatch.trans (heq_of_eq hΨ.2.2.2.1.symm)
  have hzero : leftParam 0 = 0 := by
    apply Subtype.ext
    norm_num [leftParam, Set.projIcc]
  have hone : rightParam 1 = 1 := by
    apply Subtype.ext
    norm_num [rightParam, Set.projIcc]
  refine ⟨⟨hΦ.1, continuous_concatPath hΦ.2.1 hΨ.2.1 hbase, ?_, rfl,
    locallyRepresented_concat hΨ.2.1 hΦ.2.2.2.2 hΨ.2.2.2.2 hbase hm⟩, ?_, ?_⟩
  · intro t
    unfold concatPath
    split_ifs
    · exact hΦ.2.2.1 _
    · exact hΨ.2.2.1 _
  · exact (concatFamily_heq_left Φ Ψ 0 (by norm_num)).trans
      ((family_heq Φ hzero).trans (heq_of_eq hΦ.2.2.2.1))
  · exact (concatFamily_heq_right Φ Ψ 1 (by norm_num)).trans (family_heq Ψ hone)

end D12Complex.ContinuationOperations
