import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.ReductionOrder
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.SimplyConnectedCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

noncomputable section
open Set MeasureTheory
namespace D13Unified.Ch09.ReductionOrder

/-- The calculation common to real and holomorphic reduction of order. -/
lemma reduction_from_primitives {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    {J : Set 𝕂} {p q y dy ddy e v : 𝕂 → 𝕂}
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy : IsSecondOrderSolutionOn J p q y dy ddy)
    (hne : ∀ t ∈ J, y t ≠ 0)
    (he : ∀ t ∈ J, HasDerivWithinAt e (-p t * e t) J t)
    (hv : ∀ t ∈ J, HasDerivWithinAt v (e t / y t ^ 2) J t) :
    ∃ dz ddz : 𝕂 → 𝕂,
      IsSecondOrderSolutionOn J p q (fun t => y t * v t) dz ddz ∧
      ∀ t ∈ J, y t * dz t - dy t * (y t * v t) = e t := by
  let g := fun t => e t / y t ^ 2
  let dz := fun t => dy t * v t + y t * g t
  let ddz := fun t => -p t * dz t - q t * (y t * v t)
  have hcE : ContinuousOn e J := fun t ht => (he t ht).continuousWithinAt
  have hcV : ContinuousOn v J := fun t ht => (hv t ht).continuousWithinAt
  have hcG : ContinuousOn g J := hcE.div (hy.1.pow 2) (fun t ht => pow_ne_zero _ (hne t ht))
  have hcZ : ContinuousOn (fun t => y t * v t) J := hy.1.mul hcV
  have hcDZ : ContinuousOn dz J := (hy.2.1.mul hcV).add (hy.1.mul hcG)
  refine ⟨dz, ddz, ⟨hcZ, hcDZ, (hp.neg.mul hcDZ).sub (hq.mul hcZ), ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    exact (hy.2.2.2.1 t ht).mul (hv t ht)
  · intro t ht
    have hg := (he t ht).div ((hy.2.2.2.1 t ht).pow 2) (pow_ne_zero _ (hne t ht))
    have hd := ((hy.2.2.2.2.1 t ht).mul (hv t ht)).add
      ((hy.2.2.2.1 t ht).mul hg)
    have hyy : ddy t = -p t * dy t - q t * y t := by
      linear_combination hy.2.2.2.2.2 t ht
    convert hd using 1
    dsimp [ddz, dz, g]
    rw [hyy]
    field_simp [hne t ht]
    ring
  · intro t ht
    dsimp [ddz]
    ring
  · intro t ht
    dsimp [dz, g]
    field_simp [hne t ht]
    ring

/-- A nonzero Wronskian at one point rules out a constant linear relation. -/
lemma independentOn_of_wronskian {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    {J : Set 𝕂} {y z : 𝕂 → 𝕂} {dy dz : 𝕂} {t : 𝕂}
    (ht : t ∈ J) (hu : UniqueDiffWithinAt 𝕂 J t)
    (hy : HasDerivWithinAt y dy J t) (hz : HasDerivWithinAt z dz J t)
    (hW : y t * dz - dy * z t ≠ 0) : IndependentOn J y z := by
  intro a b hab
  have hval := hab t ht
  have hd := (hy.const_mul a).add (hz.const_mul b)
  have hd0 : HasDerivWithinAt (fun r => a * y r + b * z r) 0 J t :=
    (hasDerivWithinAt_const t J (0 : 𝕂)).congr_of_mem hab ht
  have hder : a * dy + b * dz = 0 := (hd.derivWithin hu).symm.trans (hd0.derivWithin hu)
  have ha : a * (y t * dz - dy * z t) = 0 := by
    linear_combination dz * hval - z t * hder
  have hb : b * (y t * dz - dy * z t) = 0 := by
    linear_combination y t * hder - dy * hval
  exact ⟨(mul_eq_zero.mp ha).resolve_right hW, (mul_eq_zero.mp hb).resolve_right hW⟩

/-- The witness formulation has the expected C² regularity in Mathlib's calculus. -/
lemma IsSecondOrderSolutionOn.contDiffOn {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    {J : Set 𝕂} {p q y dy ddy : 𝕂 → 𝕂}
    (hy : IsSecondOrderSolutionOn J p q y dy ddy) (hU : UniqueDiffOn 𝕂 J) :
    ContDiffOn 𝕂 2 y J := by
  have hd : EqOn (derivWithin y J) dy J :=
    fun t ht => (hy.2.2.2.1 t ht).derivWithin (hU t ht)
  have hdd : EqOn (derivWithin dy J) ddy J :=
    fun t ht => (hy.2.2.2.2.1 t ht).derivWithin (hU t ht)
  have hdy : ContDiffOn 𝕂 1 dy J :=
    (contDiffOn_one_iff_derivWithin hU).2
      ⟨fun t ht => (hy.2.2.2.2.1 t ht).differentiableWithinAt, hy.2.2.1.congr hdd⟩
  exact (contDiffOn_succ_iff_derivWithin hU).2
    ⟨fun t ht => (hy.2.2.2.1 t ht).differentiableWithinAt, by simp, hdy.congr hd⟩

/-- Conversely a C² solution supplies the continuous derivative witnesses. -/
lemma secondOrderSolutionOn_of_contDiffOn {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    {J : Set 𝕂} {p q y : 𝕂 → 𝕂} (hU : UniqueDiffOn 𝕂 J)
    (hy : ContDiffOn 𝕂 2 y J)
    (heq : ∀ t ∈ J, derivWithin (derivWithin y J) J t +
      p t * derivWithin y J t + q t * y t = 0) :
    IsSecondOrderSolutionOn J p q y (derivWithin y J) (derivWithin (derivWithin y J) J) := by
  have hdy : ContDiffOn 𝕂 1 (derivWithin y J) J := hy.derivWithin hU (by norm_num)
  refine ⟨hy.continuousOn, hdy.continuousOn,
    hdy.continuousOn_derivWithin hU le_rfl, ?_, ?_, heq⟩
  · intro t ht
    exact (hy.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  · intro t ht
    exact (hdy.differentiableOn (by norm_num) t ht).hasDerivWithinAt

/-- On a domain with unique derivatives, the second derivative witness is canonical. -/
lemma IsSecondOrderSolutionOn.second_derivWithin {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    {J : Set 𝕂} {p q y dy ddy : 𝕂 → 𝕂}
    (hy : IsSecondOrderSolutionOn J p q y dy ddy) (hU : UniqueDiffOn 𝕂 J) :
    EqOn (derivWithin (derivWithin y J) J) ddy J := by
  intro t ht
  have hd : EqOn (derivWithin y J) dy J :=
    fun r hr => (hy.2.2.2.1 r hr).derivWithin (hU r hr)
  exact ((hy.2.2.2.2.1 t ht).congr_of_mem hd ht).derivWithin (hU t ht)

/-- Real reduction of order on the actual interval, with oriented integrals. -/
theorem real_reduction_with_derivatives :
    Specs.D13Unified.Ch09.ReductionOrder.RealReductionWithDerivatives := by
  intro I t₀ p q y dy ddy hI ht₀ hp hq hy hne
  let e := fun t => Real.exp (-(∫ r in t₀..t, p r))
  let v := fun t => ∫ s in t₀..t, e s / y s ^ 2
  have he : ∀ t ∈ I.carrier, HasDerivWithinAt e (-p t * e t) I.carrier t := by
    intro t ht
    have hd := (hasDerivWithinAt_integral_on_interval I.ordConnected hp ht₀ ht).neg.exp
    convert hd using 1
    dsimp [e]
    ring
  have hcE : ContinuousOn e I.carrier := fun t ht => (he t ht).continuousWithinAt
  have hg : ContinuousOn (fun s => e s / y s ^ 2) I.carrier :=
    hcE.div (hy.1.pow 2) (fun t ht => pow_ne_zero _ (hne t ht))
  have hv : ∀ t ∈ I.carrier, HasDerivWithinAt v (e t / y t ^ 2) I.carrier t :=
    fun t ht => hasDerivWithinAt_integral_on_interval I.ordConnected hg ht₀ ht
  obtain ⟨dz, ddz, hz, hW⟩ := reduction_from_primitives hp hq hy hne he hv
  refine ⟨dz, ddz, hz, hW, ?_⟩
  have hconv : Convex ℝ I.carrier := I.ordConnected.convex
  have hU : UniqueDiffOn ℝ I.carrier :=
    uniqueDiffOn_convex hconv (hconv.nontrivial_iff_nonempty_interior.mp hI)
  apply independentOn_of_wronskian ht₀ (hU t₀ ht₀) (hy.2.2.2.1 t₀ ht₀)
    (hz.2.2.2.1 t₀ ht₀)
  rw [hW t₀ ht₀]
  exact Real.exp_ne_zero _

/-- C² formulation with the canonical within derivatives, including endpoint derivatives. -/
theorem real_reduction : Specs.D13Unified.Ch09.ReductionOrder.RealReduction := by
  intro I t₀ p q y hI ht₀ hp hq hy heq hne
  have hconv : Convex ℝ I.carrier := I.ordConnected.convex
  have hU : UniqueDiffOn ℝ I.carrier :=
    uniqueDiffOn_convex hconv (hconv.nontrivial_iff_nonempty_interior.mp hI)
  have hsol := secondOrderSolutionOn_of_contDiffOn hU hy heq
  obtain ⟨dz, ddz, hz, hW, hind⟩ :=
    real_reduction_with_derivatives I t₀ p q y _ _ hI ht₀ hp hq hsol hne
  refine ⟨hz.contDiffOn hU, ?_, ?_, hind⟩
  · intro t ht
    rw [hz.second_derivWithin hU ht, (hz.2.2.2.1 t ht).derivWithin (hU t ht)]
    exact hz.2.2.2.2.2 t ht
  · intro t ht
    rw [(hz.2.2.2.1 t ht).derivWithin (hU t ht)]
    exact hW t ht

/-- Ordinary second derivatives and within second derivatives agree on an open set. -/
lemma second_derivWithin_of_isOpen {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    {J : Set 𝕂} (hJ : IsOpen J) (y : 𝕂 → 𝕂) {t : 𝕂} (ht : t ∈ J) :
    derivWithin (derivWithin y J) J t = deriv (deriv y) t := by
  rw [derivWithin_of_isOpen hJ ht]
  apply Filter.EventuallyEq.deriv_eq
  exact Filter.eventuallyEq_of_mem (hJ.mem_nhds ht)
    (fun r hr => derivWithin_of_isOpen hJ hr)

/-- The original classical open-interval version, without added hypotheses. -/
theorem classical_real_reduction : Specs.D13Unified.Ch09.ReductionOrder.ClassicalRealReduction := by
  intro I t₀ p q y ht₀ hp hq hy heq hne
  have hI : I.carrier.Nontrivial := by
    apply (I.ordConnected.convex.nontrivial_iff_nonempty_interior).mpr
    simpa [I.isOpen.interior_eq] using I.nonempty
  have heq' : ∀ t ∈ I.carrier,
      derivWithin (derivWithin y I.carrier) I.carrier t +
        p t * derivWithin y I.carrier t + q t * y t = 0 := by
    intro t ht
    rw [second_derivWithin_of_isOpen I.isOpen y ht, derivWithin_of_isOpen I.isOpen ht]
    exact heq t ht
  obtain ⟨hc, hd, hW, hind⟩ := real_reduction I.toTimeInterval t₀ p q y hI ht₀ hp hq hy heq' hne
  refine ⟨hc, ?_, ?_, hind⟩
  · intro t ht
    simpa only [second_derivWithin_of_isOpen I.isOpen _ ht,
      derivWithin_of_isOpen I.isOpen ht] using hd t ht
  · intro t ht
    simpa only [derivWithin_of_isOpen I.isOpen ht] using hW t ht

/-- The prior simply-connected primitive theorem with the base value normalized. -/
lemma normalized_holomorphic_primitive {D : Set ℂ} {t₀ : ℂ} {g : ℂ → ℂ}
    (hD : IsOpen D) (hSC : IsSimplyConnected D) (hg : DifferentiableOn ℂ g D) :
    ∃ P : ℂ → ℂ, P t₀ = 0 ∧ ∀ z ∈ D, HasDerivAt P (g z) z := by
  have hDom : D12Complex.IsDomain D :=
    ⟨hSC.nonempty, hD, hSC.isPathConnected.isConnected.isPreconnected⟩
  have hhol : D12Complex.HolomorphicOn D g :=
    ⟨hD, fun z hz => (hg z hz).differentiableAt (hD.mem_nhds hz)⟩
  obtain ⟨F, hF, hdF⟩ := D12Complex.SimplyConnectedCalculus.exists_primitive D g hDom hSC hhol
  refine ⟨fun z => F z - F t₀, sub_self _, ?_⟩
  intro z hz
  simpa [hdF z hz] using (hF.2 z hz).hasDerivAt.sub_const (F t₀)

/-- Holomorphic reduction of order on the original simply connected domain. -/
theorem holomorphic_reduction : Specs.D13Unified.Ch09.ReductionOrder.HolomorphicReduction := by
  intro D t₀ p q y hD hSC ht₀ hp hq hy hne heq
  obtain ⟨P, hP₀, hP⟩ := normalized_holomorphic_primitive (t₀ := t₀) hD hSC hp
  let e := fun z => Complex.exp (-P z)
  have he : ∀ z ∈ D, HasDerivAt e (-p z * e z) z := by
    intro z hz
    convert (hP z hz).neg.cexp using 1
    dsimp [e]
    ring
  have hcE : DifferentiableOn ℂ e D := fun z hz => (he z hz).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z => e z / y z ^ 2) D :=
    hcE.div (hy.pow 2) (fun z hz => pow_ne_zero _ (hne z hz))
  obtain ⟨V, hV₀, hV⟩ := normalized_holomorphic_primitive (t₀ := t₀) hD hSC hg
  have hcV : DifferentiableOn ℂ V D :=
    fun z hz => (hV z hz).differentiableAt.differentiableWithinAt
  have hy' := hy.deriv hD
  have hy'' := hy'.deriv hD
  have hsol : IsSecondOrderSolutionOn D p q y (deriv y) (deriv (deriv y)) :=
    ⟨hy.continuousOn, hy'.continuousOn, hy''.continuousOn,
      fun z hz => ((hy z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt.hasDerivWithinAt,
      fun z hz => ((hy' z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt.hasDerivWithinAt,
      heq⟩
  obtain ⟨dz, ddz, hz, hW⟩ := reduction_from_primitives hp.continuousOn hq.continuousOn
    hsol hne (fun z hz => (he z hz).hasDerivWithinAt)
    (fun z hz => (hV z hz).hasDerivWithinAt)
  have hd (z : ℂ) (hzD : z ∈ D) : deriv (fun w => y w * V w) z = dz z :=
    ((hz.2.2.2.1 z hzD).hasDerivAt (hD.mem_nhds hzD)).deriv
  have hdd (z : ℂ) (hzD : z ∈ D) : deriv (deriv (fun w => y w * V w)) z = ddz z := by
    have h := (hz.2.2.2.2.1 z hzD).hasDerivAt (hD.mem_nhds hzD)
    exact (h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hD.mem_nhds hzD)
      (fun w hw => hd w hw))).deriv
  refine ⟨P, V, hP₀, hV₀, hP, hV, hy.mul hcV, ?_, ?_, ?_⟩
  · intro z hzD
    rw [hdd z hzD, hd z hzD]
    exact hz.2.2.2.2.2 z hzD
  · intro z hzD
    rw [hd z hzD]
    exact hW z hzD
  · apply independentOn_of_wronskian ht₀ (hD.uniqueDiffOn t₀ ht₀)
      (hsol.2.2.2.1 t₀ ht₀) (hz.2.2.2.1 t₀ ht₀)
    rw [hW t₀ ht₀]
    exact Complex.exp_ne_zero _

end D13Unified.Ch09.ReductionOrder
