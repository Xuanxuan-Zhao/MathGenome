import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.ScalarLinear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory

namespace D13Unified.ScalarLinear
variable {𝕂 : Type*} [RCLike 𝕂]

lemma hasDerivWithinAt_exp_comp {J : Set ℝ} {f : ℝ → 𝕂} {v : 𝕂} {t : ℝ}
    (hf : HasDerivWithinAt f v J t) :
    HasDerivWithinAt (fun r => NormedSpace.exp (f r))
      (NormedSpace.exp (f t) * v) J t := by
  convert! (hasFDerivAt_exp (𝕂 := ℝ) (𝔸 := 𝕂)).comp_hasDerivWithinAt t hf using 1

lemma primitive_deriv (I : TimeInterval) {a : ℝ → 𝕂}
    (ha : ContinuousOn a I.carrier) {s t : ℝ} (hs : s ∈ I.carrier)
    (ht : t ∈ I.carrier) :
    HasDerivWithinAt (primitive a s) (a t) I.carrier t :=
  hasDerivWithinAt_integral_on_interval I.ordConnected ha hs ht

lemma primitive_continuous (I : TimeInterval) {a : ℝ → 𝕂}
    (ha : ContinuousOn a I.carrier) {s : ℝ} (hs : s ∈ I.carrier) :
    ContinuousOn (primitive a s) I.carrier :=
  fun _ ht => (primitive_deriv I ha hs ht).continuousWithinAt

lemma exponential_primitive_continuous (I : TimeInterval) {a : ℝ → 𝕂}
    (ha : ContinuousOn a I.carrier) {s : ℝ} (hs : s ∈ I.carrier) :
    ContinuousOn (fun t => NormedSpace.exp (primitive a s t)) I.carrier :=
  fun _ ht => (hasDerivWithinAt_exp_comp (primitive_deriv I ha hs ht)).continuousWithinAt

lemma inverse_factor_continuous (I : TimeInterval) {a : ℝ → 𝕂}
    (ha : ContinuousOn a I.carrier) {s : ℝ} (hs : s ∈ I.carrier) :
    ContinuousOn (fun t => NormedSpace.exp (-primitive a s t)) I.carrier :=
  fun _ ht => (hasDerivWithinAt_exp_comp (primitive_deriv I ha hs ht).neg).continuousWithinAt

/-- The two integrating factors are inverse, over either scalar field. -/
lemma factor_cancel (z : 𝕂) :
    NormedSpace.exp z * NormedSpace.exp (-z) = 1 := by
  rw [← NormedSpace.exp_add, add_neg_cancel, NormedSpace.exp_zero]

/-- Differentiation of the displayed formula, relative to the actual interval. -/
theorem variation_isIVP (I : TimeInterval) (a b : ℝ → 𝕂)
    (s : ℝ) (ξ : 𝕂) (ha : ContinuousOn a I.carrier)
    (hb : ContinuousOn b I.carrier) (hs : s ∈ I.carrier) :
    IsIVP I a b s ξ (variation a b s ξ) := by
  let g : ℝ → 𝕂 := fun r => NormedSpace.exp (-primitive a s r) * b r
  have hg : ContinuousOn g I.carrier := (inverse_factor_continuous I ha hs).mul hb
  have hd (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivWithinAt (variation a b s ξ)
        (a t * variation a b s ξ t + b t) I.carrier t := by
    have hA := hasDerivWithinAt_exp_comp (primitive_deriv I ha hs ht)
    have hB := (hasDerivWithinAt_integral_on_interval I.ordConnected hg hs ht).const_add ξ
    have he := hA.mul hB
    convert! he using 1
    dsimp [variation, g]
    calc
      a t * (NormedSpace.exp (primitive a s t) *
        (ξ + ∫ r in s..t, NormedSpace.exp (-primitive a s r) * b r)) + b t =
        NormedSpace.exp (primitive a s t) * a t *
          (ξ + ∫ r in s..t, NormedSpace.exp (-primitive a s r) * b r) +
          (NormedSpace.exp (primitive a s t) * NormedSpace.exp (-primitive a s t)) * b t := by
            rw [factor_cancel]; ring
      _ = _ := by ring
  refine ⟨fun t ht => (hd t ht).continuousWithinAt, hs, ?_, hd⟩
  simp [variation, primitive, NormedSpace.exp_zero]

/-- Integrating the derivative of the integrating-factor product forces the
formula, with oriented integrals in both time directions. -/
theorem eq_variation_of_isIVP (I : TimeInterval) (a b : ℝ → 𝕂)
    (s : ℝ) (ξ : 𝕂) (ha : ContinuousOn a I.carrier)
    (hb : ContinuousOn b I.carrier) {x : ℝ → 𝕂}
    (hx : IsIVP I a b s ξ x) : EqOn x (variation a b s ξ) I.carrier := by
  let m : ℝ → 𝕂 := fun r => NormedSpace.exp (-primitive a s r)
  have hm : ContinuousOn m I.carrier := inverse_factor_continuous I ha hx.2.1
  have hg : ContinuousOn (fun r => m r * b r) I.carrier := hm.mul hb
  have hd : ∀ t ∈ I.carrier,
      HasDerivWithinAt (fun r => m r * x r) (m t * b t) I.carrier t := by
    intro t ht
    have hm' := hasDerivWithinAt_exp_comp (primitive_deriv I ha hx.2.1 ht).neg
    have hp := hm'.mul (hx.2.2.2 t ht)
    convert! hp using 1
    dsimp [m]
    ring
  intro t ht
  have hi := integral_eq_sub_on_interval I.ordConnected (hm.mul hx.1) hg hd hx.2.1 ht
  have hms : m s = 1 := by simp [m, primitive, NormedSpace.exp_zero]
  have hy : m t * x t = ξ + ∫ r in s..t, m r * b r := by
    rw [hi]
    change m t * x t = ξ + (m t * x t - m s * x s)
    rw [hms, hx.2.2.1, one_mul]
    exact (add_sub_cancel ξ (m t * x t)).symm
  calc
    x t = (NormedSpace.exp (primitive a s t) * m t) * x t := by
      dsimp [m]; rw [factor_cancel, one_mul]
    _ = NormedSpace.exp (primitive a s t) * (m t * x t) := mul_assoc _ _ _
    _ = variation a b s ξ t := by rw [hy]; rfl

/-- Full variation of constants: the formula exists on all of `I`, and
exactly the curves agreeing with it on `I` solve the prescribed IVP. -/
theorem variation_of_constants :
    Specs.D13Unified.Ch02.ScalarLinear.variationOfConstantsExpected := by
  intro 𝕂 _ I a b s ξ ha hb hs
  have h0 := variation_isIVP I a b s ξ ha hb hs
  refine ⟨h0, fun x => ⟨fun hx => eq_variation_of_isIVP I a b s ξ ha hb hx, ?_⟩⟩
  intro h
  refine ⟨h0.1.congr h, hs, ?_, ?_⟩
  · rw [h hs]; exact h0.2.2.1
  · intro t ht
    have hd := (h0.2.2.2 t ht).congr_of_mem (fun r hr => h hr) ht
    simpa only [← h ht] using hd

/-- Open-interval solutions have exactly the source's C¹ regularity. -/
theorem classical_variation_of_constants :
    Specs.D13Unified.Ch02.ScalarLinear.classicalExpected := by
  intro 𝕂 _ I a b s ξ ha hb hs x
  rw [← (variation_of_constants I.toTimeInterval a b s ξ ha hb hs).2 x]
  constructor
  · rintro ⟨hc, hξ, hd⟩
    exact ⟨hc.continuousOn, hs, hξ, fun t ht => (hd t ht).hasDerivWithinAt⟩
  · intro hx
    refine ⟨?_, hx.2.2.1, fun t ht =>
      (hx.2.2.2 t ht).hasDerivAt (I.isOpen.mem_nhds ht)⟩
    rw [contDiffOn_one_iff_derivWithin I.isOpen.uniqueDiffOn]
    refine ⟨fun t ht => (hx.2.2.2 t ht).differentiableWithinAt, ?_⟩
    apply ((ha.mul hx.1).add hb).congr
    intro t ht
    exact (hx.2.2.2 t ht).derivWithin (I.isOpen.uniqueDiffOn t ht)

/-- The scalar predicate specializes the shared solution concepts without
imposing an extension hypothesis on the coefficients. -/
theorem shared_ivp_iff : Specs.D13Unified.Ch02.ScalarLinear.sharedIVPExpected := by
  intro 𝕂 _ F I a b x s ξ hg he
  constructor
  · rintro ⟨⟨hc, _, hd⟩, hs, hξ⟩
    exact ⟨hc, hs, hξ, fun t ht => he t ht ▸ hd t ht⟩
  · rintro ⟨hc, hs, hξ, hd⟩
    exact ⟨⟨hc, hg, fun t ht => (he t ht).symm ▸ hd t ht⟩, hs, hξ⟩

end D13Unified.ScalarLinear
