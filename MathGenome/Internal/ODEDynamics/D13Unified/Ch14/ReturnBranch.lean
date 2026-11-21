import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.ReturnBranch
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flow
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! Return branches on affine transverse sections, paper.tex d13:14:return-map.
We use the scalar implicit function theorem on ker ℓ × ℝ. The transverse
projection of the fixed-time derivative is invertible because that derivative
is injective and preserves the velocity. The inverse function theorem on the
section then supplies the Cᵏ local inverse on actual open neighborhoods. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch14.ReturnBranch
open Ch06.StateDerivative Ch06.C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linear projection onto the section along its transverse velocity. -/
def transverseProjection (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0) : E →L[ℝ] ℓ.ker :=
  ((ContinuousLinearMap.id ℝ E) - ℓ.smulRight ((ℓ a)⁻¹ • a)).codRestrict ℓ.ker (by
    intro x
    change ℓ (((ContinuousLinearMap.id ℝ E) - ℓ.smulRight ((ℓ a)⁻¹ • a)) x) = 0
    simp [ha])

lemma transverseProjection_apply (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0) (x : E) :
    (transverseProjection ℓ a ha x : E) = x - (ℓ x / ℓ a) • a := by
  simp [transverseProjection, smul_smul, div_eq_mul_inv]

@[simp] lemma transverseProjection_velocity (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0) :
    transverseProjection ℓ a ha a = 0 := by
  apply Subtype.ext
  simp [transverseProjection_apply, ha]

@[simp] lemma transverseProjection_section (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0)
    (v : ℓ.ker) : transverseProjection ℓ a ha (v : E) = v := by
  apply Subtype.ext
  simp [transverseProjection_apply, show ℓ (v : E) = 0 from v.property]

variable [FiniteDimensional ℝ E]

/-- Projection of an invertible map fixing the transverse direction induces
an invertible map on the section. This includes a zero-dimensional section. -/
lemma transverse_invertible (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0)
    (M : E →L[ℝ] E) (hM : Function.Injective M) (hMa : M a = a) :
    ((transverseProjection ℓ a ha).comp (M.comp ℓ.ker.subtypeL)).IsInvertible := by
  let B := (transverseProjection ℓ a ha).comp (M.comp ℓ.ker.subtypeL)
  have hinj : Function.Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro v hv
    have he : M (v : E) = (ℓ (M (v : E)) / ℓ a) • a := by
      have he := congrArg (fun w : ℓ.ker => (w : E)) hv
      simpa only [B, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        transverseProjection_apply, ZeroMemClass.coe_zero, sub_eq_zero] using he
    have hv' : (v : E) = (ℓ (M (v : E)) / ℓ a) • a := by
      apply hM
      simpa only [map_smul, hMa] using he
    have hc : ℓ (M (v : E)) / ℓ a = 0 := by
      have h := congrArg ℓ hv'
      rw [show ℓ (v : E) = 0 from v.property, map_smul, smul_eq_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_right ha
    apply Subtype.ext
    simpa [hc] using hv'
  let e : ℓ.ker ≃L[ℝ] ℓ.ker :=
    (LinearEquiv.ofBijective B.toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

/-- Shrink both sides of the inverse function theorem to prescribed open
neighborhoods while retaining Cᵏ regularity of the two actual representatives. -/
lemma local_diffeomorphism (k : ℕ) (hk : 1 ≤ k) (f : E → E) (hf : ContDiffAt ℝ k f 0)
    (hf0 : f 0 = 0) (L : E ≃L[ℝ] E) (hd : HasFDerivAt f (L : E →L[ℝ] E) 0)
    (S R : Set E) (hS : IsOpen S) (hR : IsOpen R) (h0S : 0 ∈ S) (h0R : 0 ∈ R) :
    ∃ e : OpenPartialHomeomorph E E,
      (e : E → E) = f ∧ 0 ∈ e.source ∧ e.source ⊆ S ∧ e.target ⊆ R ∧
      ContDiffOn ℝ k e e.source ∧ ContDiffOn ℝ k e.symm e.target := by
  have hn : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  let e₀ := hf.toOpenPartialHomeomorph f hd hn
  have h0 : (0 : E) ∈ e₀.source := hf.mem_toOpenPartialHomeomorph_source hd hn
  have hi : ContDiffAt ℝ k (e₀.symm : E → E) 0 := by
    have hi := hf.to_localInverse hd hn
    simpa only [ContDiffAt.localInverse, HasStrictFDerivAt.localInverse_def,
      e₀, ContDiffAt.toOpenPartialHomeomorph, hf0] using hi
  obtain ⟨A, hAn, hA⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨A', hA'A, hoA, h0A⟩ := mem_nhds_iff.mp hAn
  obtain ⟨B, hBn, hB⟩ := hi.contDiffOn le_rfl (by simp)
  obtain ⟨B', hB'B, hoB, h0B⟩ := mem_nhds_iff.mp hBn
  let e₁ := (e₀.symm.restrOpen (B' ∩ R) (hoB.inter hR)).symm
  let e := e₁.restrOpen (A' ∩ S) (hoA.inter hS)
  have he0 : e₀ 0 = 0 := hf0
  have h01 : (0 : E) ∈ e₁.source := by
    change (0 : E) ∈ e₀.source ∩ e₀ ⁻¹' (B' ∩ R)
    exact ⟨h0, by change e₀ 0 ∈ B' ∩ R; rw [he0]; exact ⟨h0B, h0R⟩⟩
  refine ⟨e, rfl, ⟨h01, h0A, h0S⟩, fun x hx => hx.2.2, ?_, ?_, ?_⟩
  · intro y hy
    exact hy.1.2.2
  · exact (hA.mono (fun x hx => hA'A hx.2.1))
  · apply hB.mono
    intro y hy
    exact hB'B hy.1.2.1



/-- The derivative of the actual flow in both time and initial state. -/
lemma flow_joint_derivative (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    {t : ℝ} {p : E} (hq : (t,p) ∈ flowDomain F) :
    HasFDerivAt (fun q : ℝ × E => flow F q.1 q.2)
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval (flow F t p))).coprod
        (fderiv ℝ (flow F t) p)) (t,p) := by
  have hreg := Ch11.Flow.flow_regularity 1 (by omega) F hF
  have h : HasFDerivAt (fun q : ℝ × E => flow F q.1 q.2)
      (fderiv ℝ (fun q : ℝ × E => flow F q.1 q.2) (t,p)) (t,p) :=
    (hreg.2.1.contDiffAt (hreg.1.mem_nhds hq)).differentiableAt_one.hasFDerivAt
  have ht := h.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t p)
  have ht' := (flow_ivp F hF hq.1).1.2.2 t hq.2
  have he₁ := ht.unique ht'.hasFDerivAt
  have he₂ := (h.comp p (hasFDerivAt_prodMk_right (𝕜 := ℝ) t p)).fderiv
  have he : (((ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval (flow F t p))).coprod
      (fderiv ℝ (flow F t) p)) = fderiv ℝ (fun q : ℝ × E => flow F q.1 q.2) (t,p) := by
    apply ContinuousLinearMap.ext
    intro q
    rw [← (fderiv ℝ (fun q : ℝ × E => flow F q.1 q.2) (t,p)).comp_inl_add_comp_inr q,
      he₁, ← he₂]
    rfl
  rw [he]
  exact h

lemma flow_state_injective (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    {t : ℝ} {p : E} (hq : (t,p) ∈ flowDomain F) :
    Function.Injective (fderiv ℝ (flow F t) p) := by
  have hr := Ch11.Flow.reverse_flow F hF hq
  have ho := Ch11.Flow.isOpen_timeDomain F hF t
  have hod := Ch11.Flow.isOpen_timeDomain F hF (-t)
  have hf := ((Ch11.Flow.contDiffOn_timeMap 1 (by omega) F hF t).contDiffAt
    (ho.mem_nhds hq)).differentiableAt_one.hasFDerivAt
  have hg := ((Ch11.Flow.contDiffOn_timeMap 1 (by omega) F hF (-t)).contDiffAt
    (hod.mem_nhds hr.1)).differentiableAt_one.hasFDerivAt
  have hd := hg.comp p hf
  have he : HasFDerivAt (fun x => flow F (-t) (flow F t x))
      (ContinuousLinearMap.id ℝ E) p := by
    apply (hasFDerivAt_id p).congr_of_eventuallyEq
    filter_upwards [ho.mem_nhds hq] with x hx
    exact (Ch11.Flow.reverse_flow F hF hx).2
  have heq := hd.unique he
  have hl : Function.LeftInverse (fderiv ℝ (flow F (-t)) (flow F t p))
      (fderiv ℝ (flow F t) p) := fun x => by
    simpa using congrArg (fun L : E →L[ℝ] E => L x) heq
  exact hl.injective


/-- Implicit return time, with uniqueness on a product neighborhood in the
actual flow domain and the full derivative along the section. -/
lemma implicit_return_time (k : ℕ) (hk : 1 ≤ k) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ k (autonomousEvalValue F) F.domain)
    {p : E} (hp : p ∈ F.domain) {T : ℝ} (hT : T ∈ (flowInterval F p).carrier)
    (hr : flow F T p = p) (ℓ : E →L[ℝ] ℝ) (ha : ℓ (F.eval p) ≠ 0) :
    ∃ τ : ℓ.ker → ℝ, τ 0 = T ∧ ContDiffAt ℝ k τ 0 ∧
      (∀ᶠ q : ℓ.ker × ℝ in 𝓝 (0,T),
        (q.2, p + (q.1 : E)) ∈ flowDomain F ∧
        (ℓ (flow F q.2 (p + (q.1 : E)) - p) = 0 ↔ q.2 = τ q.1)) ∧
      (∀ᶠ v : ℓ.ker in 𝓝 0,
        (τ v, p + (v : E)) ∈ flowDomain F ∧
          ℓ (flow F (τ v) (p + (v : E)) - p) = 0) ∧
      ∀ v : ℓ.ker, (fderiv ℝ τ 0) v =
        -ℓ ((fderiv ℝ (flow F T) p) (v : E)) / ℓ (F.eval p) := by
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hn : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  let M := fderiv ℝ (flow F T) p
  let a := F.eval p
  let H : ℓ.ker × ℝ → E := fun q => flow F q.2 (p + (q.1 : E))
  let g : ℓ.ker × ℝ → ℝ := fun q => ℓ (H q - p)
  have hbase : (T,p) ∈ flowDomain F := ⟨hp,hT⟩
  have hreg := Ch11.Flow.flow_regularity k hk F hF
  have hcdH : ContDiffAt ℝ k H (0,T) := by
    have hf : ContDiffAt ℝ k (fun q : ℝ × E => flow F q.1 q.2)
        (((0,T) : ℓ.ker × ℝ).2, p + (((0,T) : ℓ.ker × ℝ).1 : E)) := by
      simpa using hreg.2.1.contDiffAt (hreg.1.mem_nhds hbase)
    have hl : ContDiffAt ℝ k (fun q : ℓ.ker × ℝ => (q.2, p + (q.1 : E))) (0,T) :=
      contDiffAt_snd.prodMk (contDiffAt_const.add
        (ℓ.ker.subtypeL.contDiff.contDiffAt.comp (0,T) contDiffAt_fst))
    have hh := hf.comp (0,T) hl
    simpa [H, Function.comp_def] using hh
  have hcd : ContDiffAt ℝ k g (0,T) :=
    ℓ.contDiff.contDiffAt.comp (0,T) (hcdH.sub contDiffAt_const)
  let L : ℓ.ker × ℝ →L[ℝ] E :=
    (M.comp ℓ.ker.subtypeL).coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight a)
  have hdH : HasFDerivAt H L (0,T) := by
    have hf : HasFDerivAt (fun q : ℝ × E => flow F q.1 q.2)
        (((ContinuousLinearMap.id ℝ ℝ).smulRight a).coprod M)
        (((0,T) : ℓ.ker × ℝ).2, p + ((((0,T) : ℓ.ker × ℝ).1) : E)) := by
      simpa [hr,a,M] using flow_joint_derivative F hF1 hbase
    have hl := (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0,T) : ℓ.ker × ℝ))).prodMk
      ((ℓ.ker.subtypeL.hasFDerivAt.comp (0,T) hasFDerivAt_fst).const_add p)
    have hh := hf.comp (0,T) hl
    convert hh using 1
    · simp [H, Function.comp_def]
    · apply ContinuousLinearMap.ext
      intro q
      simp [L, M, a, add_comm]
  have hdg : HasFDerivAt g (ℓ.comp L) (0,T) :=
    ℓ.hasFDerivAt.comp (0,T) (hdH.sub_const p)
  have hright : (fderiv ℝ g (0,T)).comp (ContinuousLinearMap.inr ℝ ℓ.ker ℝ) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (ℓ a) := by
    rw [hdg.fderiv]
    apply ContinuousLinearMap.ext
    intro r
    simp [L]
  have hleft : (fderiv ℝ g (0,T)).comp (ContinuousLinearMap.inl ℝ ℓ.ker ℝ) =
      ℓ.comp (M.comp ℓ.ker.subtypeL) := by
    rw [hdg.fderiv]
    ext v
    simp [L]
  have hinv : ((fderiv ℝ g (0,T)).comp (ContinuousLinearMap.inr ℝ ℓ.ker ℝ)).IsInvertible := by
    rw [hright]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (ContinuousLinearMap.id ℝ ℝ).smulRight ((ℓ a)⁻¹)) <;>
      apply ContinuousLinearMap.ext <;> intro r <;> simp [a, ha]
  let τ := hcd.implicitFunction hn hinv
  have hτ0 : τ 0 = T := hcd.implicitFunction_apply_self hn hinv
  have hg0 : g (0,T) = 0 := by simp [g,H,hr]
  have hτcd : ContDiffAt ℝ k τ 0 := hcd.contDiffAt_implicitFunction hn hinv
  have hdom : ∀ᶠ q : ℓ.ker × ℝ in 𝓝 (0,T),
      (q.2, p + (q.1 : E)) ∈ flowDomain F := by
    apply (continuous_snd.prodMk (continuous_const.add
      (ℓ.ker.subtypeL.continuous.comp continuous_fst))).continuousAt.preimage_mem_nhds
    simpa [Function.comp_def] using hreg.1.mem_nhds hbase
  have huniq : ∀ᶠ q : ℓ.ker × ℝ in 𝓝 (0,T),
      g q = 0 ↔ q.2 = τ q.1 := by
    simpa only [hg0, eq_comm] using hcd.eventually_apply_eq_iff_implicitFunction hn hinv
  have hgraph : ∀ᶠ v : ℓ.ker in 𝓝 0,
      (τ v, p + (v : E)) ∈ flowDomain F ∧ g (v,τ v) = 0 := by
    have ht : Tendsto (fun v => (v,τ v)) (𝓝 (0 : ℓ.ker)) (𝓝 (0,T)) :=
      by simpa only [id_eq] using
        tendsto_id.prodMk_nhds (by simpa only [hτ0] using hτcd.continuousAt.tendsto)
    filter_upwards [ht.eventually hdom, hcd.eventually_apply_implicitFunction hn hinv]
      with v hv he
    exact ⟨hv, he.trans hg0⟩
  refine ⟨τ,hτ0,hτcd,?_,hgraph,?_⟩
  · filter_upwards [hdom,huniq] with q hq he
    exact ⟨hq,he⟩
  · intro v
    have hdτ := (hcd.hasStrictFDerivAt_implicitFunction hn hinv).hasFDerivAt
    rw [hdτ.fderiv]
    simp only [ContinuousLinearMap.comp_apply, neg_apply, hleft]
    have hi : ((fderiv ℝ g (0,T)).comp (ContinuousLinearMap.inr ℝ ℓ.ker ℝ)).inverse
        (ℓ (M (v : E))) = ℓ (M (v : E)) / ℓ a := by
      apply hinv.inverse_apply_eq.mpr
      rw [hright]
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      exact (div_mul_cancel₀ _ ha).symm
    change -(((fderiv ℝ g (0,T)).comp (ContinuousLinearMap.inr ℝ ℓ.ker ℝ)).inverse
        (ℓ (M (v : E)))) = _
    rw [hi]
    exact (neg_div _ _).symm


/-- The near-return branch and local diffeomorphism, on arbitrarily prescribed
local section pieces. The least-period case in the paper is a specialization. -/
theorem return_branch : Specs.D13Unified.Ch14.ReturnBranch.ReturnBranchExpected.{u} := by
  intro E _ _ _ k hk F hF p hp T hT hr ℓ ha S hS h0S ε hε
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hn : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  obtain ⟨τ,hτ0,hτcd,hpair,hgraph,hτd⟩ := implicit_return_time k hk F hF hp hT hr ℓ ha
  let a := F.eval p
  let M := fderiv ℝ (flow F T) p
  let Q := transverseProjection ℓ a ha
  let R : ℓ.ker → ℓ.ker := fun v => Q (flow F (τ v) (p + (v : E)) - p)
  have hR0 : R 0 = 0 := by simp [R,hτ0,hr]
  have hbase : (T,p) ∈ flowDomain F := ⟨hp,hT⟩
  have hreg := Ch11.Flow.flow_regularity k hk F hF
  have hcdψ : ContDiffAt ℝ k (fun v : ℓ.ker => flow F (τ v) (p + (v : E))) 0 := by
    have hf : ContDiffAt ℝ k (fun q : ℝ × E => flow F q.1 q.2)
        (τ 0, p + ((0 : ℓ.ker) : E)) := by
      simpa only [hτ0,ZeroMemClass.coe_zero,add_zero] using
        hreg.2.1.contDiffAt (hreg.1.mem_nhds hbase)
    exact hf.comp 0 (hτcd.prodMk (contDiffAt_const.add ℓ.ker.subtypeL.contDiff.contDiffAt))
  have hRcd : ContDiffAt ℝ k R 0 :=
    Q.contDiff.contDiffAt.comp 0 (hcdψ.sub contDiffAt_const)
  let B := Q.comp (M.comp ℓ.ker.subtypeL)
  have hRd : HasFDerivAt R B 0 := by
    have hf : HasFDerivAt (fun q : ℝ × E => flow F q.1 q.2)
        (((ContinuousLinearMap.id ℝ ℝ).smulRight a).coprod M)
        (τ 0, p + ((0 : ℓ.ker) : E)) := by
      simpa only [hτ0,ZeroMemClass.coe_zero,add_zero,hr] using flow_joint_derivative F hF1 hbase
    have hdψ := hf.comp 0 ((hτcd.differentiableAt hn).hasFDerivAt.prodMk
      (ℓ.ker.subtypeL.hasFDerivAt.const_add p))
    have hh := Q.hasFDerivAt.comp 0 (hdψ.sub_const p)
    have hh' : HasFDerivAt R
        (Q.comp ((((ContinuousLinearMap.id ℝ ℝ).smulRight a).coprod M).comp
          ((fderiv ℝ τ 0).prod ℓ.ker.subtypeL))) 0 := by
      simpa [R,Function.comp_def] using hh
    apply hh'.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp [B,Q,a,ContinuousLinearMap.coprod_apply]
  have hMa : M a = a := by
    simpa [M,a,hr,AutonomousODE.eval] using Ch11.Flow.flow_pushforward F hF1 (T,p) hbase
  obtain ⟨L,hL⟩ := transverse_invertible ℓ a ha M (flow_state_injective F hF1 hbase) hMa
  have hRd' : HasFDerivAt R (L : ℓ.ker →L[ℝ] ℓ.ker) 0 := by
    rw [hL]
    exact hRd
  rw [nhds_prod_eq] at hpair
  obtain ⟨A,hAn,J,hJn,hAJ⟩ := Filter.mem_prod_iff.mp hpair
  obtain ⟨r,hrpos,hrJ⟩ := Metric.mem_nhds_iff.mp hJn
  let δ := min (r/2) (ε/2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htimeJ : Ioo (T-δ) (T+δ) ⊆ J := by
    intro t ht
    apply hrJ
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hτtime : ∀ᶠ v : ℓ.ker in 𝓝 0, τ v ∈ Ioo (T-δ) (T+δ) := by
    apply hτcd.continuousAt.preimage_mem_nhds
    rw [hτ0]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  let D : Set ℓ.ker := {v | p + (v : E) ∈ F.domain}
  have hDo : IsOpen D := F.isOpen_domain.preimage
    (continuous_const.add ℓ.ker.subtypeL.continuous)
  have h0D : (0 : ℓ.ker) ∈ D := by simpa [D] using hp
  obtain ⟨C,hCn,hCcd⟩ := hτcd.contDiffOn le_rfl (by simp)
  have hgood : ∀ᶠ v : ℓ.ker in 𝓝 0,
      v ∈ S ∧ v ∈ D ∧ v ∈ A ∧ v ∈ C ∧ τ v ∈ Ioo (T-δ) (T+δ) ∧
        (τ v, p + (v : E)) ∈ flowDomain F ∧
        ℓ (flow F (τ v) (p + (v : E)) - p) = 0 := by
    filter_upwards [hS.mem_nhds h0S,hDo.mem_nhds h0D,hAn,hCn,hτtime,hgraph]
      with v hvS hvD hvA hvC hvt hvg
    exact ⟨hvS,hvD,hvA,hvC,hvt,hvg⟩
  obtain ⟨W,hWsub,hWo,h0W⟩ := mem_nhds_iff.mp hgood
  obtain ⟨P,hPR,h0P,hPW,hPT,hPcd,hPicd⟩ :=
    local_diffeomorphism k hk R hRcd hR0 L hRd' W (S ∩ D)
      hWo (hS.inter hDo) h0W ⟨h0S,h0D⟩
  have hP0 : P 0 = 0 := by rw [hPR]; exact hR0
  have h0Pt : (0 : ℓ.ker) ∈ P.target := hP0 ▸ P.map_source h0P
  have hgoodP (v : ℓ.ker) (hv : v ∈ P.source) := hWsub (hPW hv)
  refine ⟨δ,hδ,hδε,τ,P,h0P,h0Pt,?_,?_,?_,?_,hτ0,hP0,?_,hPcd,hPicd,?_,?_,?_,?_,hτd,?_⟩
  · exact fun v hv => (hgoodP v hv).1
  · exact fun v hv => (hPT hv).1
  · exact fun v hv => (hgoodP v hv).2.1
  · exact fun v hv => (hPT hv).2
  · exact hCcd.mono (fun v hv => (hgoodP v hv).2.2.2.1)
  · exact fun v hv => (hgoodP v hv).2.2.2.2.1
  · intro v hv t ht
    exact (hAJ (show (v,t) ∈ A ×ˢ J from ⟨(hgoodP v hv).2.2.1,htimeJ ht⟩)).1
  · intro v hv
    have hz := (hgoodP v hv).2.2.2.2.2.2
    have hvR : (R v : E) = flow F (τ v) (p + (v : E)) - p := by
      change (transverseProjection ℓ a ha (flow F (τ v) (p + (v : E)) - p) : E) = _
      rw [transverseProjection_apply,hz]
      simp
    rw [hPR,hvR]
    abel
  · intro v hv t ht
    exact (hAJ (show (v,t) ∈ A ×ˢ J from ⟨(hgoodP v hv).2.2.1,htimeJ ht⟩)).2
  · intro v
    rw [hPR,hRd.fderiv]
    exact transverseProjection_apply ℓ a ha (M (v : E))

/-- Specialize the stronger return theorem to the original nonconstant
periodic orbit with its named least positive period. -/
theorem periodic_return_branch :
    Specs.D13Unified.Ch14.ReturnBranch.PeriodicReturnBranchExpected.{u} := by
  intro E _ _ _ k hk F hF p hp T _ hc hperiod _ _
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hT : T ∈ (flowInterval F p).carrier := by rw [hc]; trivial
  have hr : flow F T p = p := by
    simpa only [zero_add] using (hperiod 0).trans (Ch11.Flow.flow_zero F hF1 p hp).2
  exact return_branch k hk F hF p hp T hT hr

end D13Unified.Ch14.ReturnBranch
