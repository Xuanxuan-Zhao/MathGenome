import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.Flow
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.C1Dependence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.SolutionDiffeomorphism
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.LinearGrowth
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

noncomputable section
open Set
open scoped ContDiff NNReal
namespace P201.Hyperbolic
open P201Specs.Hyperbolic
open D13Unified
open D13Unified.Ch06.C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap

private lemma equation_eval {n : ℕ} (b : LocalField n) {t : ℝ}
    {y : P201Specs.Space n} {p : ℝ} (h : (t, y) ∈ b.domain) :
    parameterEvalValue b.equation t y p = b.velocity (t, y) := by
  simp [parameterEvalValue, LocalField.equation, h]

private lemma equation_regular {n : ℕ} (b : LocalField n) :
    ContDiffOn ℝ 1 (field b.equation) b.equation.domain := by
  have h : ContDiffOn ℝ 1 (fun q : (ℝ × P201Specs.Space n) × ℝ => b.velocity q.1)
      b.equation.domain := b.regular.comp contDiffOn_fst (fun _ h => h)
  exact h.congr (fun q hq => equation_eval b (p := q.2) hq)

/-- The canonical local solution, with maximality and the original survival
sets retained. No completion of a local field is assumed. -/
theorem localFlow : P201Specs.Hyperbolic.localFlowStatement := by
  intro n hn b
  have hF := equation_regular b
  have hL := b.equation.locallyLipschitzInState_of_contDiffOn hF
  have hj := D13Unified.Ch06.C1Dependence.joint_c1 b.equation hF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hj.1.preimage
      (continuous_fst.prodMk ((continuous_snd.prodMk continuous_const)))
  · exact hj.2.comp
      (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const))
      (fun _ h => h)
  · intro s y hsy
    have hx := ParameterODE.solutionValue_ivp b.equation hL s y 0 hsy
    exact ⟨⟨hsy, hx.2.1⟩, hx.2.2⟩
  · intro t s y ht
    have hg := (ParameterODE.solutionValue_on_domain b.equation hL t s y 0 ht).2
    have hd := D13Unified.Ch06.C1Dependence.terminal_derivative b.equation hF t s y 0 ht
    change (t, solution b.equation (t, ((s, y), 0))) ∈ b.domain at hg
    rw [equation_eval b (p := 0) hg] at hd
    exact ⟨hg, hd⟩
  · intro s y hsy I x hx hs hxy
    have hx' : IsClassicalParameterIVPOn b.equation 0 I x s y := by
      refine ⟨⟨hx.1, hx.2.1, ?_⟩, hs, hxy⟩
      intro t ht
      simpa only [equation_eval b (hx.2.1 t ht)] using hx.2.2 t ht
    obtain ⟨_, _, _, _, _, hcover, _⟩ :=
      ParameterODE.canonical_solution b.equation hL s y 0 hsy
    have hc := hcover I x ((classicalParameterIVPOn_iff b.equation 0 I x s y).mp hx')
    refine ⟨fun t ht => ⟨hsy, hc.1 ht⟩, ?_⟩
    intro t ht
    exact (ParameterODE.solutionValue_on_domain b.equation hL t s y 0
      ⟨hsy, hc.1 ht⟩).1.trans (hc.2 ht)
  · intro r s y hr t
    have hg := (ParameterODE.solutionValue_on_domain b.equation hL r s y 0 hr).2
    have hb := ParameterODE.rebase b.equation hL s y 0 hr.1 r hr.2
      (P201Specs.Hyperbolic.localFlow b r s y) rfl
    refine ⟨?_, fun ht => hb.2 t ht.2⟩
    constructor
    · intro ht
      exact ⟨hr.1, hb.1 ▸ ht.2⟩
    · intro ht
      exact ⟨hg, hb.1.symm ▸ ht.2⟩
  · intro s t
    exact D13Unified.Ch06.SolutionDiffeomorphism.solution_diffeomorphism
      1 (by omega) b.equation hF s t 0


/-- Bounded velocity on all of time-space precludes finite escape. This lemma
identifies the D13 maximal domain; it does not replace it by fiat. -/
private lemma total_domain {n : ℕ} (b : LocalField n)
    (hU : b.domain = univ) (M : ℝ≥0) (hM : ∀ q, ‖b.velocity q‖ ≤ M) :
    localFlowDomain b = univ := by
  have hF := equation_regular b
  have hL := b.equation.locallyLipschitzInState_of_contDiffOn hF
  apply eq_univ_of_forall
  intro q
  have hs : (q.2.1, q.2.2) ∈ b.domain := hU ▸ mem_univ _
  obtain ⟨hx, hsi, hξ, hmax, _, _, _⟩ :=
    ParameterODE.canonical_solution b.equation hL q.2.1 q.2.2 0 hs
  let F := atParameterValue b.equation 0
  let x : Solution F :=
    ⟨parameterMaximalIntervalValue b.equation q.2.1 q.2.2 0,
      parameterSolutionCurveValue b.equation q.2.1 q.2.2 0, hx⟩
  have hFU : F.domain = univ := by
    ext z
    change (z ∈ b.domain) ↔ z ∈ univ
    rw [hU]
  have heval (t : ℝ) (y : P201Specs.Space n) : F.eval t y = b.velocity (t, y) := by
    simp [ODE.eval, F, atParameterValue, LocalField.equation, hU]
  have hglobal := D13Unified.Ch04.LinearGrowth.global_existence F
    (ParameterODE.LocallyLipschitzInState.atParameter b.equation hL 0) hFU
    (fun B hB => ⟨M, 0, M.coe_nonneg, le_rfl, by
      intro t ht y
      simpa only [heval, zero_mul, add_zero] using hM (t, y)⟩) x hmax
  exact ⟨hs, hglobal ▸ mem_univ q.1⟩

/-- The coefficient assumptions yield the spatial Lipschitz constant also at
both endpoints of the time slab. -/
private lemma slab_lipschitz {n : ℕ} {T : ℝ} (b : SlabField n T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    LipschitzWith b.spatialBound (fun x => b.velocity (t, x)) := by
  have hc : ContDiff ℝ 1 (fun x => b.velocity (t, x)) := by
    rw [← contDiffOn_univ]
    exact b.regular.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ _ => ⟨ht, mem_univ _⟩)
  exact lipschitzWith_of_nnnorm_fderiv_le hc.differentiable_one
    (fun y => b.spatial_bound t ht y)

/-- Uniqueness on a closed slab, comparing arbitrary endpoint-aware solutions
and allowing the initial time to be either endpoint or an interior time. -/
private lemma slab_unique {n : ℕ} {T : ℝ} (b : SlabField n T)
    {s : ℝ} (hs : s ∈ Icc 0 T) {x z : ℝ → P201Specs.Space n}
    (hx : IsSlabSolution b x) (hz : IsSlabSolution b z) (he : x s = z s) :
    EqOn x z (Icc 0 T) := by
  have hright : EqOn x z (Icc s T) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun t y => b.velocity (t, y)) (s := fun _ => univ)
      (fun t ht => (slab_lipschitz b ⟨hs.1.trans ht.1, ht.2.le⟩).lipschitzOnWith)
      (hx.1.mono (Icc_subset_Icc_left hs.1))
      (fun t ht => (hx.2 t ⟨hs.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hs.1.trans ht.1, ht.2⟩))
      (fun _ _ => mem_univ _)
      (hz.1.mono (Icc_subset_Icc_left hs.1))
      (fun t ht => (hz.2 t ⟨hs.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hs.1.trans ht.1, ht.2⟩))
      (fun _ _ => mem_univ _) he
  have hleft : EqOn x z (Icc 0 s) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun t y => b.velocity (t, y)) (s := fun _ => univ)
      (fun t ht => (slab_lipschitz b ⟨ht.1.le, ht.2.trans hs.2⟩).lipschitzOnWith)
      (hx.1.mono (Icc_subset_Icc_right hs.2))
      (fun t ht => (hx.2 t ⟨ht.1.le, ht.2.trans hs.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans hs.2⟩))
      (fun _ _ => mem_univ _)
      (hz.1.mono (Icc_subset_Icc_right hs.2))
      (fun t ht => (hz.2 t ⟨ht.1.le, ht.2.trans hs.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans hs.2⟩))
      (fun _ _ => mem_univ _) he
  intro t ht
  rcases le_total t s with h | h
  · exact hleft ⟨ht.1, h⟩
  · exact hright ⟨h, ht.2⟩

/-- The source's sharp displacement bound uses only velocity values on the
original slab, irrespective of the bounds of an auxiliary extension. -/
private lemma slab_displacement {n : ℕ} {T : ℝ} (b : SlabField n T)
    {x : ℝ → P201Specs.Space n} (hx : IsSlabSolution b x)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    ‖x t - x s‖ ≤ slabVelocityNorm b * |t - s| := by
  have hb : BddAbove ((fun q : ℝ × P201Specs.Space n => ‖b.velocity q‖) ''
      (Icc 0 T ×ˢ univ)) := by
    refine ⟨b.bound, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact b.velocity_bound q.1 hq.1 q.2
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hx.2
    (fun r hr => le_csSup hb ⟨(r, x r), ⟨hr, mem_univ _⟩, rfl⟩)
    (convex_Icc 0 T) hs ht


/-- Assembly of all closed-slab flow assertions from an independently proved
C¹ extension lemma. The extension is an argument to this assembly theorem,
not an added hypothesis in the final source theorem. -/
theorem slabFlow_of_extension (hext : slabExtensionStatement) : slabFlowStatement := by
  intro n hn T hT b
  obtain ⟨v, hv, he, ⟨M, hM⟩⟩ := hext n hn T hT b
  let c : LocalField n := ⟨univ, isOpen_univ, v, hv.contDiffOn⟩
  have hc := localFlow n hn c
  have hfull : localFlowDomain c = univ := total_domain c rfl M hM
  have hdom (t s : ℝ) (y : P201Specs.Space n) : (t, s, y) ∈ localFlowDomain c :=
    hfull ▸ mem_univ _
  let X := P201Specs.Hyperbolic.localFlow c
  have hreg : ContDiff ℝ 1 (fun q : ℝ × (ℝ × P201Specs.Space n) => X q.1 q.2.1 q.2.2) := by
    have h := hc.regular
    rw [hfull] at h
    exact contDiffOn_univ.mp h
  have hinit (s : ℝ) (y : P201Specs.Space n) : X s s y = y :=
    (hc.initial s y (mem_univ _)).2
  have hsol (s : ℝ) (y : P201Specs.Space n) : IsSlabSolution b (fun t => X t s y) := by
    have htreg : ContDiff ℝ 1 (fun t => X t s y) :=
      hreg.comp (contDiff_id.prodMk (contDiff_const.prodMk contDiff_const))
    refine ⟨htreg.continuous.continuousOn, ?_⟩
    intro t ht
    have hd := (hc.equation t s y (hdom t s y)).2.hasDerivWithinAt (s := Icc 0 T)
    change HasDerivWithinAt (fun r => X r s y) (v (t, X t s y)) (Icc 0 T) t at hd
    rwa [he ⟨ht, mem_univ _⟩] at hd
  refine ⟨X, ⟨hreg.contDiffOn, fun s hs y => hinit s y,
    fun s hs y => hsol s y, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs y x hx hxy
    exact slab_unique b hs hx (hsol s y) (hxy.trans (hinit s y).symm)
  · intro t ht r hr s hs y
    exact (hc.composition r s y (hdom r s y) t).2 (hdom t s y)
  · intro t ht s hs y
    have hd := slab_displacement b (hsol s y) hs ht
    simpa only [hinit] using hd
  · intro t ht s hs
    obtain ⟨_, _, _, e, hsource, htarget, hforward, hback, hce, hci⟩ := hc.diffeomorphism s t
    have hes : e.source = univ := hsource.trans (eq_univ_of_forall (fun y => hdom t s y))
    have het : e.target = univ := htarget.trans (eq_univ_of_forall (fun y => hdom s t y))
    refine ⟨e.toHomeomorphOfSourceEqUnivTargetEqUniv hes het, hforward, hback, ?_, ?_⟩
    · change ContDiff ℝ 1 (e : P201Specs.Space n → P201Specs.Space n)
      rw [hes] at hce
      exact contDiffOn_univ.mp hce
    · change ContDiff ℝ 1 (e.symm : P201Specs.Space n → P201Specs.Space n)
      rw [het] at hci
      exact contDiffOn_univ.mp hci

/-- The degenerate slab does not require a time extension theorem. -/
private lemma slab_extension_zero {n : ℕ} (b : SlabField n 0) :
    ∃ v : ℝ × P201Specs.Space n → P201Specs.Space n,
      ContDiff ℝ 1 v ∧ EqOn v b.velocity (Icc 0 0 ×ˢ univ) ∧
      ∃ M : ℝ≥0, ∀ q, ‖v q‖ ≤ M := by
  have hs : ContDiff ℝ 1 (fun x => b.velocity (0, x)) := by
    rw [← contDiffOn_univ]
    exact b.regular.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ _ => ⟨⟨le_rfl, le_rfl⟩, mem_univ _⟩)
  refine ⟨fun q => b.velocity (0, q.2), hs.comp contDiff_snd, ?_, b.bound, ?_⟩
  · intro q hq
    have hq0 : q.1 = 0 := le_antisymm hq.1.2 hq.1.1
    change b.velocity (0, q.2) = b.velocity (q.1, q.2)
    rw [hq0]
  · intro q
    exact b.velocity_bound 0 ⟨le_rfl, le_rfl⟩ q.2

/-- A continuously varying derivative specified on a closed piece. -/
private def C1With {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (d : E → E →L[ℝ] F) (s : Set E) : Prop :=
  ContinuousOn d s ∧ ∀ x ∈ s, HasFDerivWithinAt f (d x) s x

private lemma C1With.union {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {d : E → E →L[ℝ] F} {s t : Set E}
    (hs : IsClosed s) (ht : IsClosed t) (hfs : C1With f d s) (hft : C1With f d t) :
    C1With f d (s ∪ t) := by
  refine ⟨hfs.1.union_of_isClosed hft.1 hs ht, ?_⟩
  intro x hx
  have hds : HasFDerivWithinAt f (d x) s x := by
    by_cases h : x ∈ s
    · exact hfs.2 x h
    · exact HasFDerivWithinAt.of_notMem_closure (by simpa [hs.closure_eq] using h)
  have hdt : HasFDerivWithinAt f (d x) t x := by
    by_cases h : x ∈ t
    · exact hft.2 x h
    · exact HasFDerivWithinAt.of_notMem_closure (by simpa [ht.closure_eq] using h)
  exact hds.union hdt

private lemma C1With.contDiff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {d : E → E →L[ℝ] F} (h : C1With f d univ) :
    ContDiff ℝ 1 f := by
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨d, continuousOn_univ.mp h.1, fun x => (h.2 x (mem_univ _)).hasFDerivAt (by simp)⟩

private lemma C1With.congr {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {d e : E → E →L[ℝ] F} {s : Set E}
    (h : C1With f d s) (hf : EqOn g f s) (hd : EqOn e d s) : C1With g e s := by
  refine ⟨h.1.congr hd, ?_⟩
  intro x hx
  rw [hd hx]
  exact (h.2 x hx).congr (fun y hy => hf hy) (hf hx)

private lemma C1With.of_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} (h : ContDiffOn ℝ 1 f s) (hs : UniqueDiffOn ℝ s) :
    C1With f (fderivWithin ℝ f s) s :=
  ⟨h.continuousOn_fderivWithin hs le_rfl,
    fun x hx => (h.differentiableOn one_ne_zero x hx).hasFDerivWithinAt⟩

private lemma C1With.paste {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {d e : E → E →L[ℝ] F} {s t : Set E}
    [DecidablePred (· ∈ s)]
    (hs : IsClosed s) (ht : IsClosed t) (hf : C1With f d s) (hg : C1With g e t)
    (hfg : EqOn f g (s ∩ t)) (hde : EqOn d e (s ∩ t)) :
    C1With (s.piecewise f g) (s.piecewise d e) (s ∪ t) := by
  classical
  apply C1With.union hs ht
  · exact hf.congr (fun x hx => by simp [hx]) (fun x hx => by simp [hx])
  · apply hg.congr
    · intro x hx
      by_cases h : x ∈ s
      · simp [h, hfg ⟨h, hx⟩]
      · simp [h]
    · intro x hx
      by_cases h : x ∈ s
      · simp [h, hde ⟨h, hx⟩]
      · simp [h]

private lemma C1With.comp_contDiff {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {d : F → F →L[ℝ] G} {s : Set F} {t : Set E}
    (hf : C1With f d s) {v : E → F} (hv : ContDiff ℝ 1 v) (hm : MapsTo v t s) :
    C1With (f ∘ v) (fun x => (d (v x)).comp (fderiv ℝ v x)) t := by
  refine ⟨(hf.1.comp hv.continuous.continuousOn hm).clm_comp
    (hv.continuous_fderiv one_ne_zero).continuousOn, ?_⟩
  intro x hx
  exact (hf.2 (v x) (hm hx)).comp x
    (hv.differentiable_one x).hasFDerivAt.hasFDerivWithinAt hm

private lemma C1With.sub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {d e : E → E →L[ℝ] F} {s : Set E}
    (hf : C1With f d s) (hg : C1With g e s) :
    C1With (fun x => f x - g x) (fun x => d x - e x) s :=
  ⟨hf.1.sub hg.1, fun x hx => (hf.2 x hx).sub (hg.2 x hx)⟩

private lemma C1With.smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {d : E → E →L[ℝ] F} {s : Set E}
    (hf : C1With f d s) (a : ℝ) :
    C1With (fun x => a • f x) (fun x => a • d x) s :=
  ⟨hf.1.const_smul a, fun x hx => (hf.2 x hx).const_smul a⟩

private def bendTime {E : Type*} (a k : ℝ) (q : ℝ × E) : ℝ × E :=
  (a + k * (1 - Real.exp ((q.1 - a) * k⁻¹)), q.2)

private lemma bendTime_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a k : ℝ) : ContDiff ℝ 1 (bendTime (E := E) a k) := by
  unfold bendTime
  fun_prop

private lemma bendTime_at {E : Type*} (a k : ℝ) (y : E) :
    bendTime a k (a, y) = (a, y) := by simp [bendTime]

private lemma bendTime_fderiv_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a k : ℝ) (hk : k ≠ 0) (y : E) :
    fderiv ℝ (bendTime a k) (a, y) =
      (-ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E) := by
  have hd := (((((hasFDerivAt_fst (𝕜 := ℝ) (p := (a, y))).sub_const a).mul_const
    k⁻¹).exp.const_sub 1).const_mul k).const_add a
  have hd' := hd.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := (a, y)))
  change fderiv ℝ (fun p : ℝ × E => (a + k * (1 - Real.exp ((p.1 - a) * k⁻¹)), p.2)) (a, y) = _
  simpa only [sub_self, zero_mul, Real.exp_zero, one_smul, smul_neg, smul_smul,
    one_mul, mul_inv_cancel₀ hk] using hd'.fderiv

private def reflectValue {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × E → F) (a k : ℝ) (q : ℝ × E) : F :=
  (2 : ℝ) • f (a, q.2) - f (bendTime a k q)

private def reflectDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℝ × E → (ℝ × E) →L[ℝ] F) (a k : ℝ) (q : ℝ × E) :
    (ℝ × E) →L[ℝ] F :=
  (2 : ℝ) • (d (a, q.2)).comp (fderiv ℝ (fun p : ℝ × E => (a, p.2)) q) -
    (d (bendTime a k q)).comp (fderiv ℝ (bendTime a k) q)

private lemma reflectValue_at {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × E → F) (a k : ℝ) (y : E) :
    reflectValue f a k (a, y) = f (a, y) := by
  simp [reflectValue, bendTime_at, two_smul]

private lemma reflectDeriv_at {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℝ × E → (ℝ × E) →L[ℝ] F) (a k : ℝ) (hk : k ≠ 0) (y : E) :
    reflectDeriv d a k (a, y) = d (a, y) := by
  have hp : fderiv ℝ (fun p : ℝ × E => (a, p.2)) (a, y) =
      (0 : (ℝ × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ E) :=
    ((hasFDerivAt_const a (a, y)).prodMk hasFDerivAt_snd).fderiv
  simp only [reflectDeriv, hp, bendTime_at, bendTime_fderiv_at a k hk]
  apply ContinuousLinearMap.ext
  intro v
  change (2 : ℝ) • d (a, y) (0, v.2) - d (a, y) (-v.1, v.2) = d (a, y) v
  rw [← map_smul, ← map_sub]
  congr 1
  apply Prod.ext <;> simp [two_smul]

private lemma C1With.reflect {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} {d : ℝ × E → (ℝ × E) →L[ℝ] F} {s t : Set (ℝ × E)}
    (hf : C1With f d s) (a k : ℝ)
    (hp : MapsTo (fun p : ℝ × E => (a, p.2)) t s)
    (hr : MapsTo (bendTime a k) t s) :
    C1With (reflectValue f a k) (reflectDeriv d a k) t := by
  exact ((hf.comp_contDiff (contDiff_const.prodMk contDiff_snd) hp).smul 2).sub
    (hf.comp_contDiff (bendTime_contDiff a k) hr)

private lemma bendTime_lower_maps {E : Type*} (T : ℝ) (hT : 0 < T) :
    MapsTo (bendTime (E := E) 0 T) (Iic 0 ×ˢ univ) (Icc 0 T ×ˢ univ) := by
  intro q hq
  have he : Real.exp ((q.1 - 0) * T⁻¹) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by simpa using hq.1)
      (inv_nonneg.mpr hT.le))
  have hp := Real.exp_pos ((q.1 - 0) * T⁻¹)
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> dsimp [bendTime]
  · exact add_nonneg le_rfl (mul_nonneg hT.le (sub_nonneg.mpr he))
  · nlinarith [mul_pos hT hp]

private lemma bendTime_upper_maps {E : Type*} (T : ℝ) (hT : 0 < T) :
    MapsTo (bendTime (E := E) T (-T)) (Ici T ×ˢ univ) (Icc 0 T ×ˢ univ) := by
  intro q hq
  have he : Real.exp ((q.1 - T) * (-T)⁻¹) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq.1)
      (inv_nonpos.mpr (neg_nonpos.mpr hT.le)))
  have hp := Real.exp_pos ((q.1 - T) * (-T)⁻¹)
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> dsimp [bendTime]
  · nlinarith [mul_pos hT hp]
  · nlinarith [mul_nonneg hT.le (sub_nonneg.mpr he)]

/-- Bounded intrinsic C¹ data on a positive-length time slab admit a bounded
C¹ extension. Exponential reflections sample only the original slab. -/
theorem bounded_slab_extension {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T : ℝ} (hT : 0 < T) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ univ)) (M : ℝ≥0)
    (hM : ∀ q ∈ Icc 0 T ×ˢ univ, ‖f q‖ ≤ M) :
    ∃ v : ℝ × E → F, ContDiff ℝ 1 v ∧ EqOn v f (Icc 0 T ×ˢ univ) ∧
      ∀ q, ‖v q‖ ≤ (3 : ℝ) * M := by
  classical
  let S : Set (ℝ × E) := Icc 0 T ×ˢ univ
  let A : Set (ℝ × E) := Iic 0 ×ˢ univ
  let B : Set (ℝ × E) := Ici T ×ˢ univ
  let d := fderivWithin ℝ f S
  have hS : IsClosed S := isClosed_Icc.prod isClosed_univ
  have hA : IsClosed A := isClosed_Iic.prod isClosed_univ
  have hB : IsClosed B := isClosed_Ici.prod isClosed_univ
  have hfd : C1With f d S := C1With.of_contDiffOn hf
    ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ)
  have hp0 : MapsTo (fun p : ℝ × E => (0, p.2)) A S :=
    fun _ _ => ⟨⟨le_rfl, hT.le⟩, mem_univ _⟩
  have hpT : MapsTo (fun p : ℝ × E => (T, p.2)) B S :=
    fun _ _ => ⟨⟨hT.le, le_rfl⟩, mem_univ _⟩
  have hl := hfd.reflect 0 T hp0 (bendTime_lower_maps T hT)
  have hr := hfd.reflect T (-T) hpT (bendTime_upper_maps T hT)
  have he0 : ∀ q ∈ A ∩ S, q.1 = 0 := fun q hq => le_antisymm hq.1.1 hq.2.1.1
  have hg := hl.paste hA hS hfd
    (fun q hq => by
      obtain ⟨t, y⟩ := q
      have ht := he0 (t, y) hq
      dsimp only [Prod.fst] at ht
      subst t
      exact reflectValue_at f 0 T y)
    (fun q hq => by
      obtain ⟨t, y⟩ := q
      have ht := he0 (t, y) hq
      dsimp only [Prod.fst] at ht
      subst t
      exact reflectDeriv_at d 0 T hT.ne' y)
  let g := A.piecewise (reflectValue f 0 T) f
  let dg := A.piecewise (reflectDeriv d 0 T) d
  have heT : ∀ q ∈ (A ∪ S) ∩ B, q.1 = T := by
    intro q hq
    rcases hq.1 with hqA | hqS
    · exact False.elim ((not_le_of_gt hT) (hq.2.1.trans hqA.1))
    · exact le_antisymm hqS.1.2 hq.2.1
  have hgT : EqOn g (reflectValue f T (-T)) ((A ∪ S) ∩ B) := by
    rintro ⟨t, y⟩ hq
    have ht := heT (t, y) hq
    dsimp only [Prod.fst] at ht
    subst t
    simp [g, A, not_le_of_gt hT, reflectValue_at]
  have hdgT : EqOn dg (reflectDeriv d T (-T)) ((A ∪ S) ∩ B) := by
    rintro ⟨t, y⟩ hq
    have ht := heT (t, y) hq
    dsimp only [Prod.fst] at ht
    subst t
    simp [dg, A, not_le_of_gt hT, reflectDeriv_at d T (-T) (neg_ne_zero.mpr hT.ne')]
  have hv := hg.paste (hA.union hS) hB hr hgT hdgT
  have hcover : (A ∪ S) ∪ B = univ := by
    apply eq_univ_of_forall
    intro q
    by_cases h0 : q.1 ≤ 0
    · exact Or.inl (Or.inl ⟨h0, mem_univ _⟩)
    · by_cases h1 : q.1 ≤ T
      · exact Or.inl (Or.inr ⟨⟨le_of_not_ge h0, h1⟩, mem_univ _⟩)
      · exact Or.inr ⟨le_of_not_ge h1, mem_univ _⟩
  let v := (A ∪ S).piecewise g (reflectValue f T (-T))
  refine ⟨v, ?_, ?_, ?_⟩
  · exact C1With.contDiff (hcover ▸ hv)
  · intro q hq
    have hq' : q ∈ S := hq
    simp only [v, Set.piecewise, ite_eq_left (show q ∈ A ∪ S from Or.inr hq')]
    by_cases hqA : q ∈ A
    · have h0 := he0 q ⟨hqA, hq'⟩
      obtain ⟨t, y⟩ := q
      dsimp at h0
      subst t
      simp [g, A, reflectValue_at]
    · simp [g, hqA]
  · have hreflect (a k : ℝ) (q : ℝ × E)
        (hp : (a, q.2) ∈ S) (hb : bendTime a k q ∈ S) :
        ‖reflectValue f a k q‖ ≤ (3 : ℝ) * M := by
      calc
        ‖reflectValue f a k q‖ ≤ ‖(2 : ℝ) • f (a, q.2)‖ + ‖f (bendTime a k q)‖ :=
          norm_sub_le _ _
        _ = 2 * ‖f (a, q.2)‖ + ‖f (bendTime a k q)‖ := by simp [norm_smul]
        _ ≤ 3 * M := by linarith [hM (a, q.2) hp, hM _ hb]
    intro q
    by_cases hq : q ∈ A ∪ S
    · simp only [v, Set.piecewise, ite_eq_left hq]
      by_cases hqA : q ∈ A
      · simp only [g, Set.piecewise, ite_eq_left hqA]
        exact hreflect 0 T q (hp0 hqA) (bendTime_lower_maps T hT hqA)
      · simp only [g, Set.piecewise, ite_eq_right hqA]
        have hqS := hq.resolve_left hqA
        have hh := hM q hqS
        linarith [M.coe_nonneg]
    · simp only [v, Set.piecewise, ite_eq_right hq]
      have hqB : q ∈ B := by
        have hall : q ∈ (A ∪ S) ∪ B := hcover ▸ mem_univ q
        exact hall.resolve_left hq
      exact hreflect T (-T) q (hpT hqB) (bendTime_upper_maps T hT hqB)

/-- Closed-slab coefficients have a bounded C¹ extension; both the degenerate
and positive-length slabs are covered without an extra hypothesis. -/
private theorem slab_extension : slabExtensionStatement := by
  intro n hn T hT b
  by_cases hz : T = 0
  · subst T
    exact slab_extension_zero b
  · have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hz)
    obtain ⟨v, hv, he, hbound⟩ := bounded_slab_extension hpos b.regular b.bound
      (fun q hq => b.velocity_bound q.1 hq.1 q.2)
    refine ⟨v, hv, he, 3 * b.bound, ?_⟩
    intro q
    simpa using hbound q

/-- The complete nonautonomous characteristic flow on the closed time slab,
including endpoint equations, uniqueness, and reverse-time C¹ inverses. -/
theorem slabFlow : P201Specs.Hyperbolic.slabFlowStatement :=
  slabFlow_of_extension slab_extension

end P201.Hyperbolic
