import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Flowbox
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flow
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch11.Flowbox
open Ch06.StateDerivative Ch06.C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch11.Flowbox
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A nonzero vector is the first column of a linear coordinate frame. -/
lemma exists_frame (v : E) (hv : v ≠ 0) :
    ∃ A : (ℝ × (Fin (Module.finrank ℝ E - 1) → ℝ)) ≃L[ℝ] E,
      A (1,0) = v := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℝ hv
  let B : (ℝ × LinearMap.ker l) ≃ₗ[ℝ] E :=
    { toFun := fun q => q.1 • v + q.2.val
      invFun := fun x => (l x, ⟨x - l x • v, by simp [hl]⟩)
      left_inv := by
        rintro ⟨s,z⟩
        have hz : l z.val = 0 := z.property
        simp only [map_add, map_smul, hl, smul_eq_mul, mul_one, hz, add_zero]
        congr 1
        apply Subtype.ext
        simp
      right_inv := by intro x; simp
      map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add,
        Submodule.coe_add, add_smul]; abel
      map_smul' := by intro s q; simp [smul_add, smul_smul] }
  have hd : Module.finrank ℝ (LinearMap.ker l) = Module.finrank ℝ E - 1 := by
    have h := B.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_self] at h
    omega
  let C : (Fin (Module.finrank ℝ E - 1) → ℝ) ≃ₗ[ℝ] LinearMap.ker l :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hd])
  let A := ((LinearEquiv.refl ℝ ℝ).prodCongr C).trans B
  exact ⟨A.toContinuousLinearEquiv, by simp [A, B]⟩

/-- The joint derivative of the partial flow at elapsed time zero. -/
lemma flow_derivative_zero (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain) :
    HasFDerivAt (fun q : ℝ × E => flow F q.1 q.2)
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval p)).coprod
        (ContinuousLinearMap.id ℝ E)) (0,p) := by
  have h0 := Flow.flow_zero F hF p hp
  have hd := ((autonomous_joint_c1 F hF).contDiffAt
    ((isOpen_flowDomain F hF).mem_nhds h0.1)).differentiableAt_one.hasFDerivAt
  have ht := hd.comp (0 : ℝ) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) p)
  have hx := hd.comp p (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : ℝ) p)
  have ht' : HasFDerivAt (fun t => flow F t p)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval p)) 0 := by
    convert ((flow_ivp F hF hp).1.2.2 0 h0.1.2).hasFDerivAt using 1
    ext
    simp [AutonomousODE.toODE_eval, h0.2]
  have hx' : HasFDerivAt (fun x => flow F 0 x) (ContinuousLinearMap.id ℝ E) p := by
    apply (hasFDerivAt_id p).congr_of_eventuallyEq
    filter_upwards [F.isOpen_domain.mem_nhds hp] with x hx
    exact (Flow.flow_zero F hF x hx).2
  have he : fderiv ℝ (fun q : ℝ × E => flow F q.1 q.2) (0,p) =
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval p)).coprod
        (ContinuousLinearMap.id ℝ E) := by
    have hte := ht.unique ht'
    have hxe := hx.unique hx'
    apply ContinuousLinearMap.ext
    intro q
    have ha := congrArg (fun L : ℝ →L[ℝ] E => L q.1) hte
    have hb := congrArg (fun L : E →L[ℝ] E => L q.2) hxe
    change fderiv ℝ (fun q : ℝ × E => flow F q.1 q.2) (0,p) q = _
    rw [show q = (q.1,0) + (0,q.2) by simp, map_add]
    simpa using congrArg₂ (fun a b : E => a+b) ha hb
  simpa only [he] using hd

/-- Straightening on a product neighborhood, with the actual partial-flow
law and Cᵏ regularity of both coordinate directions. -/
theorem flowbox : Specs.D13Unified.Ch11.Flowbox.FlowboxStatement.{u} := by
  intro E _ _ _ k hk F hF p hp hv
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let H := Fin (Module.finrank ℝ E - 1) → ℝ
  obtain ⟨A,hA⟩ := exists_frame (F.eval p) hv
  let J : H →L[ℝ] E := (A : (ℝ × H) →L[ℝ] E).comp (ContinuousLinearMap.inr ℝ ℝ H)
  let c : ℝ × H → ℝ × E := fun q => (q.1,p+J q.2)
  let g : ℝ × H → E := fun q => flow F q.1 (p+J q.2)
  let d : Set (ℝ × H) := c ⁻¹' flowDomain F
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hR := Flow.flow_regularity k hk F hF
  have hc : ContDiff ℝ k c :=
    contDiff_fst.prodMk (contDiff_const.add (J.contDiff.comp contDiff_snd))
  have hdo : IsOpen d := hR.1.preimage hc.continuous
  have hd0 : (0,0) ∈ d := by
    simpa [d,c] using (Flow.flow_zero F hF1 p hp).1
  have hg : ContDiffOn ℝ k g d := hR.2.1.comp hc.contDiffOn (fun _ hq => hq)
  have hg0 : g (0,0) = p := by simpa [g] using (Flow.flow_zero F hF1 p hp).2
  have hgAt : ContDiffAt ℝ k g (0,0) := hg.contDiffAt (hdo.mem_nhds hd0)
  have hcin : HasFDerivAt c
      ((ContinuousLinearMap.fst ℝ ℝ H).prod
        (J.comp (ContinuousLinearMap.snd ℝ ℝ H))) (0,0) := by
    convert (hasFDerivAt_fst (𝕜 := ℝ) (p := (0, (0 : H)))).prodMk
      ((hasFDerivAt_const p (0, (0 : H))).add
        (J.hasFDerivAt.comp ((0 : ℝ),(0 : H))
          (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0 : ℝ),(0 : H)))))) using 1 <;> simp [c]
  have hgDer : HasFDerivAt g (A : (ℝ × H) →L[ℝ] E) (0,0) := by
    have hc0 : c (0,0) = (0,p) := by simp [c]
    have hder0 := flow_derivative_zero F hF1 hp
    rw [← hc0] at hder0
    have h := hder0.comp ((0 : ℝ),(0 : H)) hcin
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      rintro ⟨s,z⟩
      change A (s,z) = s • F.eval p + A (0,z)
      rw [← hA, ← map_smul, ← map_add]
      congr 1
      simp
  have hkn : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  let e := hgAt.toOpenPartialHomeomorph g hgDer hkn
  have he0 : (0,0) ∈ e.source := hgAt.mem_toOpenPartialHomeomorph_source hgDer hkn
  have hinv : ContDiffAt ℝ k e.symm p := by
    change ContDiffAt ℝ k (hgAt.localInverse hgDer hkn) p
    simpa only [hg0] using hgAt.to_localInverse hgDer hkn
  obtain ⟨U,hUp,hU⟩ := hinv.contDiffOn le_rfl (by simp)
  have hgood : e.source ∩ d ∩ g ⁻¹' U ∈ 𝓝 (0,(0 : H)) := by
    refine inter_mem (inter_mem (e.open_source.mem_nhds he0) (hdo.mem_nhds hd0)) ?_
    apply hgAt.continuousAt.preimage_mem_nhds
    simpa only [hg0] using hUp
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hgood
  let S : Set (ℝ × H) := Ioo (-r) r ×ˢ Metric.ball (0 : H) r
  have hSo : IsOpen S := isOpen_Ioo.prod Metric.isOpen_ball
  have hS0 : (0,(0 : H)) ∈ S := by simp [S, hr]
  have hSgood : S ⊆ e.source ∩ d ∩ g ⁻¹' U := by
    apply Subset.trans _ hrs
    rw [← ball_prod_same]
    exact prod_mono (by simp [Real.ball_eq_Ioo]) Subset.rfl
  let b := e.restrOpen S hSo
  have hbsource : b.source = S := by
    change e.source ∩ S = S
    exact inter_eq_right.mpr (fun q hq => (hSgood hq).1.1)
  have hbcoe : (b : (ℝ × H) → E) = g := rfl
  have hbdom (q : ℝ × H) (hq : q ∈ b.source) : q ∈ d :=
    (hSgood (hbsource ▸ hq)).1.2
  have hbg : ContDiffOn ℝ k b b.source := hg.mono hbdom
  have hbt : b.target ⊆ F.domain := by
    intro y hy
    have hq := b.map_target hy
    have hid := b.right_inv hy
    have hd := hbdom (b.symm y) hq
    have := hR.2.2 (c (b.symm y)) hd
    change g (b.symm y) ∈ F.domain at this
    simpa only [← hbcoe, hid] using this
  have hbinv : ContDiffOn ℝ k b.symm b.target := by
    apply hU.mono
    intro y hy
    have hq := b.map_target hy
    have hu := (hSgood (hbsource ▸ hq)).2
    change g (b.symm y) ∈ U at hu
    simpa only [← hbcoe, b.right_inv hy] using hu
  refine ⟨{
    frame := A
    frame_time := hA
    ε := r
    ε_pos := hr
    transverse := Metric.ball 0 r
    transverse_open := Metric.isOpen_ball
    transverse_zero := Metric.mem_ball_self hr
    coord := b
    source_eq := hbsource
    target_domain := hbt
    origin := hg0
    target_point := ?_
    regular := hbg
    inverse_regular := hbinv
    flow_domain := hbdom
    formula := fun _ _ => rfl
    velocity := ?_
    translation := ?_ }⟩
  · rw [← hg0]
    exact b.map_source (hbsource.symm ▸ hS0)
  · intro q hq
    have hqd := hbdom q hq
    have hder := (hbg.contDiffAt (b.open_source.mem_nhds hq)).differentiableAt
      hkn
    have ht := hder.hasFDerivAt.comp q.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)
    have ht' := (flow_ivp F hF1 hqd.1).1.2.2 q.1 hqd.2
    have heq := ht.unique ht'.hasFDerivAt
    have := congrArg (fun L : ℝ →L[ℝ] E => L 1) heq
    simpa [Function.comp_def, hbcoe, g, c, AutonomousODE.toODE_eval, AutonomousODE.eval] using this
  · intro q hq t ht
    have hs := hbdom q hq
    have hst := hbdom (q.1+t,q.2) ht
    have htrans := Flow.flow_translation F hF1 (p+J q.2) hs.1 q.1 hs.2
    have hstate : g q ∈ F.domain := hR.2.2 (c q) hs
    have hsum : t+q.1 ∈ (flowInterval F (p+J q.2)).carrier := by
      simpa only [add_comm t q.1] using hst.2
    refine ⟨⟨hstate, ?_⟩, ?_⟩
    · change t ∈ (flowInterval F (flow F q.1 (p+J q.2))).carrier
      rw [htrans.1]
      exact hsum
    · change flow F t (flow F q.1 (p+J q.2)) = flow F (q.1+t) (p+J q.2)
      simpa only [add_comm t q.1] using htrans.2 t hsum

end D13Unified.Ch11.Flowbox
