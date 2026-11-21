import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.RegularConstraints
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.DerivativeCriterion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.Peano
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalExistenceUniqueness
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace D13Unified.Ch11.RegularConstraints

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

/-- A regular level has C¹ coordinates whose derivative lifts every tangent
vector. The coordinate space is the actual kernel, which may be zero. -/
lemma regular_level_chart (Ω : Set E) (hΩ : IsOpen Ω) (h : E → H)
    (hh : ContDiffOn ℝ 1 h Ω) (c : H) (p : E) (hp : p ∈ Ω) (hcp : h p = c)
    (hrank : Function.Surjective (fderiv ℝ h p)) :
    let A := fderiv ℝ h p
    ∃ (V : Set A.ker) (ψ : A.ker → E) (P : E →L[ℝ] A.ker),
      IsOpen V ∧ (0 : A.ker) ∈ V ∧ ContDiffOn ℝ 1 ψ V ∧ ψ 0 = p ∧
      (∀ u ∈ V, ψ u ∈ Ω ∧ h (ψ u) = c) ∧
      ∀ u ∈ V, ∀ v : E, (fderiv ℝ h (ψ u)) v = 0 →
        (fderiv ℝ ψ u) (P v) = v := by
  classical
  let := FiniteDimensional.complete ℝ E
  let := FiniteDimensional.complete ℝ H
  let A := fderiv ℝ h p
  have hhp : ContDiffAt ℝ 1 h p := hh.contDiffAt (hΩ.mem_nhds hp)
  have hs : HasStrictFDerivAt h A p := hhp.hasStrictFDerivAt (by norm_num)
  have hsur : A.range = ⊤ := LinearMap.range_eq_top.mpr hrank
  let φ := hs.implicitFunctionDataOfComplemented h A hsur
    A.ker_closedComplemented_of_finiteDimensional_range
  let e := φ.toOpenPartialHomeomorph
  let ψ : A.ker → E := fun u => e.symm (c, u)
  have hright : ContDiffAt ℝ 1 φ.rightFun p := by
    change ContDiffAt ℝ 1 (fun x => (Classical.choose
      A.ker_closedComplemented_of_finiteDimensional_range) (x - p)) p
    fun_prop
  have hinv : ContDiffAt ℝ 1 (e.symm : H × A.ker → E) (c, 0) := by
    have hi := φ.contDiffAt_implicitFunction hhp hright (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have he0 : φ.prodFun φ.pt = (c, 0) := by simp [φ, hcp]
    change ContDiffAt ℝ 1 (e.symm : H × A.ker → E) (φ.prodFun φ.pt) at hi
    rw [he0] at hi
    exact hi
  have hpt : (c, (0 : A.ker)) ∈ e.target := by
    convert φ.map_pt_mem_toOpenPartialHomeomorph_target using 1
    simp [φ, hcp]
  have hψ0 : ψ 0 = p := by
    have he := e.left_inv φ.pt_mem_toOpenPartialHomeomorph_source
    convert he using 1 <;> simp [ψ, e, φ, hcp,
      ImplicitFunctionData.toOpenPartialHomeomorph_apply]
  have hd : ∀ᶠ q : H × A.ker in 𝓝 (c, 0), e.symm q ∈ Ω := by
    apply hinv.continuousAt.preimage_mem_nhds
    simpa only [show e.symm (c, 0) = p from hψ0] using hΩ.mem_nhds hp
  have htarg : ∀ᶠ q in 𝓝 (c, (0 : A.ker)), q ∈ e.target :=
    e.open_target.mem_nhds hpt
  have hall := (hinv.eventually (by norm_num)).and (htarg.and hd)
  obtain ⟨W, hW, hWo, hW0⟩ := eventually_nhds_iff.mp hall
  let V : Set A.ker := (fun u => (c, u)) ⁻¹' W
  have hVo : IsOpen V := hWo.preimage (continuous_const.prodMk continuous_id)
  have hV0 : (0 : A.ker) ∈ V := hW0
  have hψ : ∀ u ∈ V, ContDiffAt ℝ 1 ψ u := by
    intro u hu
    exact (hW (c, u) hu).1.comp u (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨V, ψ, φ.rightDeriv, hVo, hV0,
    fun u hu => (hψ u hu).contDiffWithinAt, hψ0, ?_, ?_⟩
  · intro u hu
    refine ⟨(hW (c, u) hu).2.2, ?_⟩
    have he := e.right_inv (hW (c, u) hu).2.1
    exact (congrArg Prod.fst he).trans rfl
  · intro u hu v hv
    have ht : (c, u) ∈ e.target := (hW (c, u) hu).2.1
    have hsrc : ψ u ∈ e.source := e.map_target ht
    have hdom : ψ u ∈ Ω := (hW (c, u) hu).2.2
    have hdh := (hh.contDiffAt (hΩ.mem_nhds hdom)).differentiableAt (by norm_num)
    have hde : HasFDerivAt (e : E → H × A.ker)
        ((fderiv ℝ h (ψ u)).prod φ.rightDeriv) (ψ u) := by
      change HasFDerivAt (fun x => (h x, φ.rightFun x)) _ _
      exact hdh.hasFDerivAt.prodMk
        (φ.rightDeriv.hasFDerivAt.comp (ψ u) ((hasFDerivAt_id (ψ u)).sub_const p))
    have hdi := (hW (c, u) hu).1.differentiableAt (by norm_num)
    have her : e (ψ u) = (c, u) := e.right_inv ht
    have hdi' : HasFDerivAt (e.symm : H × A.ker → E)
        (fderiv ℝ (e.symm : H × A.ker → E) (e (ψ u))) (e (ψ u)) := by
      rw [her]
      exact hdi.hasFDerivAt
    have hcomp := hdi'.comp (ψ u) hde
    have hleft : (fun x => e.symm (e x)) =ᶠ[𝓝 (ψ u)] id :=
      e.eventually_left_inverse hsrc
    have hid : (fderiv ℝ (e.symm : H × A.ker → E) (e (ψ u))).comp
        ((fderiv ℝ h (ψ u)).prod φ.rightDeriv) = ContinuousLinearMap.id ℝ E :=
      (hcomp.congr_of_eventuallyEq hleft.symm).unique (hasFDerivAt_id (ψ u))
    have hderψ : fderiv ℝ ψ u =
        (fderiv ℝ (e.symm : H × A.ker → E) (c, u)).comp
          (ContinuousLinearMap.inr ℝ H A.ker) := by
      exact (hdi.hasFDerivAt.comp u
        ((hasFDerivAt_const c u).prodMk (hasFDerivAt_id u))).fderiv
    rw [hderψ]
    change (fderiv ℝ (e.symm : H × A.ker → E) (c, u)) (0, φ.rightDeriv v) = v
    have hv' := congrArg (fun L : E →L[ℝ] E => L v) hid
    simpa [her, hv] using hv'

/-- Peano in a regular-level chart supplies a two-sided constrained solution.
No Lipschitz estimate for the induced coordinate field is used. -/
lemma constrained_local_solution (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (h : E → H)
    (hh : ContDiffOn ℝ 1 h F.domain) (c : H)
    (htan : ∀ p ∈ F.domain, h p = c → (fderiv ℝ h p) (F.eval p) = 0)
    (p : E) (hp : p ∈ F.domain) (hcp : h p = c)
    (hrank : Function.Surjective (fderiv ℝ h p)) (s : ℝ) :
    ∃ (I : OpenTimeInterval) (y : ℝ → E),
      IsClassicalAutonomousIVPOn F I y s p ∧ ∀ t ∈ I.carrier, h (y t) = c := by
  classical
  obtain ⟨V, ψ, P, hVo, hV0, hψ, hψ0, hlevel, hlift⟩ :=
    regular_level_chart F.domain F.isOpen_domain h hh c p hp hcp hrank
  let g : (fderiv ℝ h p).ker → (fderiv ℝ h p).ker := fun u => P (F.eval (ψ u))
  have hg : ContinuousOn g V := P.continuous.comp_continuousOn
    (hF.continuousOn.comp hψ.continuousOn (fun u hu => (hlevel u hu).1))
  let G : AutonomousODE (fderiv ℝ h p).ker :=
    { domain := V
      isOpen_domain := hVo
      field := fun u => g u
      continuous_field := hg.domRestrict }
  obtain ⟨a, ha, u, hu⟩ := Ch03.peano_local G.toODE s 0 hV0
  let I : OpenTimeInterval :=
    ⟨⟨Ioo (s-a) (s+a), ⟨s, sub_lt_self s ha, lt_add_of_pos_right s ha⟩,
      ordConnected_Ioo⟩, isOpen_Ioo⟩
  have hu' : IsClassicalAutonomousIVPOn G I u s 0 := hu
  have hgu : ∀ t ∈ I.carrier, G.eval (u t) = g (u t) := by
    intro t ht
    simp only [AutonomousODE.eval, Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue,
      dite_eq_left (hu'.1.2.1 t ht)]
    rfl
  refine ⟨I, fun t => ψ (u t), ⟨⟨?_, ?_, ?_⟩, hu'.2.1, ?_⟩, ?_⟩
  · exact hψ.comp hu'.1.1 (fun t ht => hu'.1.2.1 t ht)
  · intro t ht
    exact (hlevel (u t) (hu'.1.2.1 t ht)).1
  · intro t ht
    have hut := hu'.1.2.1 t ht
    have hdψ := (hψ.contDiffAt (hVo.mem_nhds hut)).differentiableAt (by norm_num)
    have hd := hdψ.hasFDerivAt.comp_hasDerivAt t (hu'.1.2.2 t ht)
    change HasDerivAt (fun r => ψ (u r)) ((fderiv ℝ ψ (u t)) (G.eval (u t))) t at hd
    rw [hgu t ht] at hd
    have heq : (fderiv ℝ ψ (u t)) (g (u t)) = F.eval (ψ (u t)) :=
      hlift (u t) hut (F.eval (ψ (u t)))
        (htan _ (hlevel (u t) hut).1 (hlevel (u t) hut).2)
    rw [heq] at hd
    exact hd
  · change ψ (u s) = p
    rw [hu'.2.2, hψ0]
  · intro t ht
    exact (hlevel (u t) (hu'.1.2.1 t ht)).2

/-- Local constrained existence and ambient uniqueness propagate the constraint
through any connected open solution interval, in either direction from s. -/
lemma constraint_on_solution (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (h : E → H)
    (hh : ContDiffOn ℝ 1 h F.domain) (c : H)
    (hrank : ∀ p ∈ F.domain, h p = c → Function.Surjective (fderiv ℝ h p))
    (htan : ∀ p ∈ F.domain, h p = c → (fderiv ℝ h p) (F.eval p) = 0)
    (I : OpenTimeInterval) (x : ℝ → E) (hx : IsClassicalAutonomousSolutionOn F I x)
    (s : ℝ) (hs : s ∈ I.carrier) (hxs : h (x s) = c) :
    ∀ t ∈ I.carrier, h (x t) = c := by
  let T : Set I.carrier := {t | h (x t) = c}
  have hc : Continuous (fun t : I.carrier => h (x t)) :=
    (hh.continuousOn.comp hx.1.continuousOn hx.2.1).domRestrict
  have hTc : IsClosed T := isClosed_eq hc continuous_const
  have hTo : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨J, y, hy, hyl⟩ := constrained_local_solution F hF h hh c htan
      (x t) (hx.2.1 t t.property) ht (hrank _ (hx.2.1 t t.property) ht) t
    have heq : EqOn x y (I.carrier ∩ J.carrier) :=
      Ch03.LocalExistenceUniqueness.overlap_uniqueness F.toODE
        (F.locallyLipschitzInState_of_contDiffOn hF) I J x y t (x t)
        ⟨hx, t.property, rfl⟩ hy
    have hnb : (Subtype.val ⁻¹' J.carrier : Set I.carrier) ∈ 𝓝 t :=
      (J.isOpen.preimage continuous_subtype_val).mem_nhds hy.2.1
    apply mem_of_superset hnb
    intro r hr
    change h (x r) = c
    rw [heq ⟨r.property, hr⟩]
    exact hyl r hr
  let : PreconnectedSpace I.carrier :=
    isPreconnected_iff_preconnectedSpace.mp I.ordConnected.isPreconnected
  have hTu : T = univ := IsClopen.eq_univ ⟨hTc, hTo⟩ ⟨⟨s, hs⟩, hxs⟩
  intro t ht
  exact (show (⟨t, ht⟩ : I.carrier) ∈ T by rw [hTu]; trivial)

/-- A regular C¹ constraint with tangency on its own level set is invariant on
its actual maximal lifespan. No global completeness or off-level tangency is
assumed. Empty level sets and zero-dimensional levels are included. -/
theorem regular_constraints :
    Specs.D13Unified.Ch11.RegularConstraints.Invariance.{u, v} := by
  intro E _ _ _ H _ _ _ F hF h hh c hrank htan
  refine ⟨fun p hp => hp.1, ?_⟩
  intro p hp t ht
  have hL := F.locallyLipschitzInState_of_contDiffOn hF
  obtain ⟨hx, hs, hinit, _⟩ := ODE.canonical_solution F.toODE hL 0 p hp.1
  have hsol : IsClassicalAutonomousSolutionOn F (Ch06.StateDerivative.flowInterval F p)
      (fun t => Ch06.StateDerivative.flow F t p) := hx
  refine ⟨hsol.2.1 t ht, ?_⟩
  apply constraint_on_solution F hF h hh c hrank htan
    (Ch06.StateDerivative.flowInterval F p) (fun t => Ch06.StateDerivative.flow F t p)
    hsol 0 hs ?_ t ht
  simpa only [show Ch06.StateDerivative.flow F 0 p = p from hinit] using hp.2

end D13Unified.Ch11.RegularConstraints
