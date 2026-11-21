import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.PerronRegularity
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.PerronFixedPoints
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

/-! Weighted Banach-space regularity for the Lyapunov–Perron equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped ContDiff

namespace D13Unified.Ch20.PerronRegularity

section Banach
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Neumann invertibility, including the uniform inverse bound. The argument
allows the zero Banach space; it does not assume the identity has norm one. -/
theorem inverse_sub_of_norm_le (T : X →L[ℝ] X) {q : ℝ}
    (hT : ‖T‖ ≤ q) (hq : q < 1) :
    ∃ J : X ≃L[ℝ] X,
      J.toContinuousLinearMap = ContinuousLinearMap.id ℝ X - T ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ (1 - q)⁻¹ := by
  obtain ⟨U, hU⟩ := isUnit_one_sub_of_norm_lt_one (lt_of_le_of_lt hT hq)
  let J : X ≃L[ℝ] X := ContinuousLinearEquiv.ofUnit U
  have hJ : J.toContinuousLinearMap = ContinuousLinearMap.id ℝ X - T := hU
  refine ⟨J, hJ, ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_⟩
  intro y
  have hid : y = J.symm y - T (J.symm y) := by
    calc
      y = J (J.symm y) := (J.apply_symm_apply y).symm
      _ = J.symm y - T (J.symm y) := by
        change J.toContinuousLinearMap (J.symm y) = _
        rw [hJ]
        rfl
  have h := norm_add_le y (T (J.symm y))
  have heq : J.symm y = y + T (J.symm y) := (sub_eq_iff_eq_add).mp hid.symm
  have hle : ‖J.symm y‖ ≤ ‖y‖ + q * ‖J.symm y‖ := by
    calc
      ‖J.symm y‖ = ‖y + T (J.symm y)‖ := congrArg norm heq
      _ ≤ ‖y‖ + ‖T (J.symm y)‖ := h
      _ ≤ ‖y‖ + q * ‖J.symm y‖ := by
        gcongr
        exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  change ‖J.symm y‖ ≤ (1 - q)⁻¹ * ‖y‖
  rw [inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hq)]
  nlinarith

end Banach

section Parameter
variable {P X : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Parameter regularity in Banach norm for an affine fixed-point equation.
No regularity of the selected solution is assumed. Local implicit solutions
are identified using uniqueness in the entire path space. -/
theorem contDiff_fixedPoint_family {k : ℕ∞ω} (hk : k ≠ 0)
    (L : P →L[ℝ] X) (N : X → X) (hN : ContDiff ℝ k N)
    (W : P → X) (hW : ∀ x, W x = L x + N (W x))
    (huniq : ∀ x y, y = L x + N y → y = W x)
    (hinv : ∀ w, (ContinuousLinearMap.id ℝ X - fderiv ℝ N w).IsInvertible) :
    ContDiff ℝ k W := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let F : P × X → X := fun p => p.2 - N p.2 - L p.1
  have hF : ContDiff ℝ k F :=
    (contDiff_snd.sub (hN.comp contDiff_snd)).sub (L.contDiff.comp contDiff_fst)
  have hdiffN := hN.differentiable hk
  have hderiv : HasFDerivAt F
      ((ContinuousLinearMap.snd ℝ P X -
        (fderiv ℝ N (W x)).comp (ContinuousLinearMap.snd ℝ P X)) -
        L.comp (ContinuousLinearMap.fst ℝ P X)) (x, W x) :=
    (hasFDerivAt_snd.sub ((hdiffN (W x)).hasFDerivAt.comp (x, W x) hasFDerivAt_snd)).sub
      (L.hasFDerivAt.comp (x, W x) hasFDerivAt_fst)
  have hinvF : (fderiv ℝ F (x, W x) ∘L .inr ℝ P X).IsInvertible := by
    rw [hderiv.fderiv]
    convert hinv (W x) using 1
    ext y
    simp
  have hzero : F (x, W x) = 0 := by
    dsimp [F]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (hW x))
  let ψ := (hF.contDiffAt (x := (x, W x))).implicitFunction hk hinvF
  have hψ : ContDiffAt ℝ k ψ x :=
    (hF.contDiffAt (x := (x, W x))).contDiffAt_implicitFunction hk hinvF
  apply hψ.congr_of_eventuallyEq
  filter_upwards [(hF.contDiffAt (x := (x, W x))).eventually_apply_implicitFunction hk hinvF]
    with y hy
  apply (huniq y (ψ y) ?_).symm
  change ψ y - N (ψ y) - L y = F (x, W x) at hy
  rw [hzero] at hy
  have heq := sub_eq_zero.mp hy
  exact sub_eq_iff_eq_add.mp heq

end Parameter
section Taylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniform continuity of the derivative supplies a Taylor remainder radius
independent of the base point. This is the uniformity needed at infinite time. -/
theorem uniform_taylor_remainder (r : E → F) (hr : Differentiable ℝ r)
    (hu : UniformContinuous (fderiv ℝ r)) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x v : E, ‖v‖ < η →
      ‖r (x + v) - r x - fderiv ℝ r x v‖ ≤ ε * ‖v‖ := by
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨η, hη, ?_⟩
  intro x v hv
  have hb : ∀ z ∈ segment ℝ x (x + v), ‖fderiv ℝ r z - fderiv ℝ r x‖ ≤ ε := by
    intro z hz
    apply le_of_lt
    apply (show ‖fderiv ℝ r z - fderiv ℝ r x‖ < ε from ?_)
    rw [← dist_eq_norm]
    apply hmod
    rw [dist_eq_norm]
    have hdist := norm_sub_le_of_mem_segment hz
    exact hdist.trans_lt (by simpa using hv)
  simpa using (convex_segment x (x + v)).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hr z) hb (left_mem_segment ℝ x (x + v)) (right_mem_segment ℝ x (x + v))

/-- The cutoff's Lipschitz bound controls the derivative with the same
constant, which is needed for the precise contraction rate qβ. -/
theorem remainder_derivative_le (r : E → F) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) (x : E) :
    ‖fderiv ℝ r x‖ ≤ δ :=
  norm_fderiv_le_of_lip' ℝ hδ (Filter.Eventually.of_forall (fun y => hlip y x))

/-- Bridge from the specification's first iterated derivative to the usual
Fréchet derivative used by the weighted Taylor estimate. -/
theorem regularDerivatives_fderiv {k : ℕ∞} (hk : 1 ≤ k) (r : E → E)
    (hr : Specs.D13Unified.Ch20.PerronRegularity.regularDerivatives k r) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ r x‖ ≤ C) ∧
    UniformContinuous (fderiv ℝ r) := by
  obtain ⟨hb, hu⟩ := hr 1 le_rfl hk
  refine ⟨?_, ?_⟩
  · simpa using hb
  · have heq : fderiv ℝ r =
        (continuousMultilinearCurryFin1 ℝ E E) ∘ iteratedFDeriv ℝ 1 r := by
      funext x
      ext y
      simp [continuousMultilinearCurryFin1_apply]
    rw [heq]
    exact (continuousMultilinearCurryFin1 ℝ E E).isometry.uniformContinuous.comp hu

end Taylor

section WeightedEvaluation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : ℝ}

/-- Weighted coordinates determine the path from its actual half-line values. -/
theorem weightedPath_ext {w v : WeightedPath β E}
    (h : ∀ t : ℝ, 0 ≤ t → w.atReal t = v.atReal t) : w = v := by
  apply (WeightedPath.coordinates β E).injective
  apply BoundedContinuousFunction.ext
  intro t
  have hte : 0 ≤ (t : ℝ) := t.property
  have ht := h t hte
  simp only [WeightedPath.atReal, dite_eq_left hte, WeightedPath.eval] at ht
  exact smul_right_injective E (Real.exp_ne_zero _) ht

@[simp] theorem eval_add (w v : WeightedPath β E) (t : HalfLine) :
    (w + v).eval t = w.eval t + v.eval t := by
  change _ • (w.weighted t + v.weighted t) = _
  exact smul_add _ _ _

@[simp] theorem eval_smul (c : ℝ) (w : WeightedPath β E) (t : HalfLine) :
    (c • w).eval t = c • w.eval t := by
  change Real.exp (-β * (t : ℝ)) • (c • w.weighted t) =
    c • (Real.exp (-β * (t : ℝ)) • w.weighted t)
  simp only [smul_smul, mul_comm]

@[simp] theorem atReal_add (w v : WeightedPath β E) (t : ℝ) :
    (w + v).atReal t = w.atReal t + v.atReal t := by
  by_cases ht : 0 ≤ t <;> simp [WeightedPath.atReal, ht]

@[simp] theorem atReal_smul (c : ℝ) (w : WeightedPath β E) (t : ℝ) :
    (c • w).atReal t = c • w.atReal t := by
  by_cases ht : 0 ≤ t <;> simp [WeightedPath.atReal, ht]

theorem weighted_eval_norm (w : WeightedPath β E) (t : HalfLine) :
    Real.exp (β * (t : ℝ)) * ‖w.eval t‖ = ‖w.weighted t‖ := by
  simp only [WeightedPath.eval, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf
  simp

/-- The norm estimate required to take Taylor remainders uniformly in time. -/
theorem weighted_eval_le_norm (w : WeightedPath β E) (t : HalfLine) :
    Real.exp (β * (t : ℝ)) * ‖w.eval t‖ ≤ ‖w‖ := by
  rw [weighted_eval_norm]
  exact w.weighted.norm_coe_le_norm t

theorem eval_le_norm (hβ : 0 ≤ β) (w : WeightedPath β E) (t : HalfLine) :
    ‖w.eval t‖ ≤ ‖w‖ := by
  calc
    ‖w.eval t‖ ≤ Real.exp (β * (t : ℝ)) * ‖w.eval t‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg hβ t.property))
    _ ≤ ‖w‖ := weighted_eval_le_norm w t

/-- Products of any positive number of path directions retain one exponential
weight. This is the estimate used for every higher Nemytskii derivative. -/
theorem weighted_product_eval_le (hβ : 0 ≤ β) (t : HalfLine) :
    ∀ (j : ℕ) (v : Fin (j + 1) → WeightedPath β E),
      Real.exp (β * (t : ℝ)) * ∏ i, ‖(v i).eval t‖ ≤ ∏ i, ‖v i‖ := by
  intro j
  induction j with
  | zero =>
      intro v
      simpa using weighted_eval_le_norm (v 0) t
  | succ j ih =>
      intro v
      rw [Fin.prod_univ_succ (fun i : Fin (j + 1 + 1) => ‖(v i).eval t‖),
        Fin.prod_univ_succ (fun i : Fin (j + 1 + 1) => ‖v i‖)]
      calc
        _ = ‖(v 0).eval t‖ *
            (Real.exp (β * (t : ℝ)) * ∏ i : Fin (j + 1), ‖(v i.succ).eval t‖) := by ring
        _ ≤ ‖v 0‖ * ∏ i : Fin (j + 1), ‖v i.succ‖ :=
          mul_le_mul (eval_le_norm hβ (v 0) t) (ih (fun i => v i.succ))
            (by positivity) (norm_nonneg _)

/-- A bounded multilinear form evaluated on weighted path directions has
the weighted bound used by every positive-order superposition derivative. -/
theorem weighted_multilinear_eval_le (hβ : 0 ≤ β) (t : HalfLine)
    (j : ℕ) (D : ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) E)
    (v : Fin (j + 1) → WeightedPath β E) :
    Real.exp (β * (t : ℝ)) * ‖D (fun i => (v i).eval t)‖ ≤
      ‖D‖ * ∏ i, ‖v i‖ := by
  calc
    _ ≤ Real.exp (β * (t : ℝ)) * (‖D‖ * ∏ i, ‖(v i).eval t‖) :=
      mul_le_mul_of_nonneg_left (D.le_opNorm _) (Real.exp_pos _).le
    _ = ‖D‖ * (Real.exp (β * (t : ℝ)) * ∏ i, ‖(v i).eval t‖) := by ring
    _ ≤ ‖D‖ * ∏ i, ‖v i‖ :=
      mul_le_mul_of_nonneg_left (weighted_product_eval_le hβ t j v) (norm_nonneg _)

/-- The full weighted first-order remainder bound, uniform over all
nonnegative times and over the base weighted path. -/
theorem weighted_taylor_remainder (hβ : 0 ≤ β) (r : E → E)
    (hr : Differentiable ℝ r) (hu : UniformContinuous (fderiv ℝ r))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ w v : WeightedPath β E, ‖v‖ < η → ∀ t : HalfLine,
      Real.exp (β * (t : ℝ)) *
        ‖r (w.eval t + v.eval t) - r (w.eval t) - fderiv ℝ r (w.eval t) (v.eval t)‖
        ≤ ε * ‖v‖ := by
  obtain ⟨η, hη, hrem⟩ := uniform_taylor_remainder r hr hu hε
  refine ⟨η, hη, ?_⟩
  intro w v hv t
  calc
    _ ≤ Real.exp (β * (t : ℝ)) * (ε * ‖v.eval t‖) :=
      mul_le_mul_of_nonneg_left
        (hrem (w.eval t) (v.eval t) ((eval_le_norm hβ v t).trans_lt hv))
        (Real.exp_pos _).le
    _ = ε * (Real.exp (β * (t : ℝ)) * ‖v.eval t‖) := by ring
    _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_left (weighted_eval_le_norm v t) hε.le

end WeightedEvaluation

section Conditional
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.PerronFixedPoints
open Specs.D13Unified.Ch20.PerronRegularity
universe u v

/-- Every proposed positive-order pointwise derivative is an actual weighted
path, with a bound in the weighted norm, rather than only a pointwise formula. -/
theorem lift_multilinear_directions_conditional
    (_hfixed : fixedPointsExpected.{u, v})
    (_hcomplete : weightedCompleteExpected.{v})
    (hnorm : weightedNormExpected.{v})
    (hrepr : weightedRepresentationExpected.{v})
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (β : ℝ) (hβ : 0 ≤ β) (j : ℕ)
    (D : E → ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) E)
    (hD : Continuous D) (C : ℝ) (hC : 0 ≤ C) (hDb : ∀ x, ‖D x‖ ≤ C)
    (w : WeightedPath β E) (v : Fin (j + 1) → WeightedPath β E) :
    ∃ z : WeightedPath β E,
      (∀ t : HalfLine, z.eval t = D (w.eval t) (fun i => (v i).eval t)) ∧
      ‖z‖ ≤ C * ∏ i, ‖v i‖ := by
  let f : HalfLine → E := fun t => D (w.eval t) (fun i => (v i).eval t)
  have hw : Continuous w.eval := (hnorm β w).1
  have hv : ∀ i, Continuous (v i).eval := fun i => (hnorm β (v i)).1
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hb : ∀ t : HalfLine, Real.exp (β * (t : ℝ)) * ‖f t‖ ≤ C * ∏ i, ‖v i‖ := by
    intro t
    exact (weighted_multilinear_eval_le hβ t j (D (w.eval t)) v).trans
      (mul_le_mul_of_nonneg_right (hDb _) (by positivity))
  let z := WeightedPath.ofPath β f hf (C * ∏ i, ‖v i‖) hb
  refine ⟨z, ?_, ?_⟩
  · exact fun t => congrFun (hrepr β f hf _ hb) t
  · change ‖z.weighted‖ ≤ _
    apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity)
    intro t
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb t

/-- A family with all the upstream properties, selected from the first
conditional premise. This does not yet assert parameter regularity. -/
theorem exists_solutionFamily_conditional
    (hfixed : fixedPointsExpected.{u, v})
    (_hcomplete : weightedCompleteExpected.{v})
    (_hnorm : weightedNormExpected.{v})
    (_hrepr : weightedRepresentationExpected.{v}) :
    ∀ {n : Type u} [Fintype n] [DecidableEq n]
      {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A →
      ∀ K α β δ : ℝ, 1 ≤ K → 0 < α → dichotomyBounds b A K α →
        0 < β → β < α → 0 ≤ δ → contractionRate K α β δ < 1 →
        ∀ r : E → E, r 0 = 0 → (∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) →
        ∃ W : stableParameters b A → WeightedPath β E,
          SolutionFamily b A r K α β δ W := by
  classical
  intro n _ _ E _ _ _ b A hA K α β δ hK hα hd hβ hβα hδ hq r hr hlip
  have hex := fun ξ : stableParameters b A =>
    hfixed b A hA K α β δ hK hα hd hβ hβα hδ hq r hr hlip (ξ : E) ξ.property
  choose W hW using hex
  exact ⟨W, hW⟩

/-- The linear evolution into the weighted path space can be reconstructed
from the exact conditional fixed-point theorem at zero remainder. Its
linearity is proved from actual path values, and its operator norm is ≤ K. -/
theorem exists_linearEvolution_conditional
    (hfixed : fixedPointsExpected.{u, v})
    (_hcomplete : weightedCompleteExpected.{v})
    (_hnorm : weightedNormExpected.{v})
    (_hrepr : weightedRepresentationExpected.{v})
    {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (K α β : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hβ : 0 < β) (hβα : β < α) :
    ∃ L : stableParameters b A →L[ℝ] WeightedPath β E,
      ‖L‖ ≤ K ∧ ∀ ξ t, 0 ≤ t → (L ξ).atReal t = evolution b A t (ξ : E) := by
  classical
  have hex := fun ξ : stableParameters b A =>
    hfixed b A hA K α β 0 hK hα hd hβ hβα le_rfl
      (by simp [contractionRate]) (fun _ => 0) rfl
      (by intros; simp) (ξ : E) ξ.property
  choose W hW using hex
  have hval : ∀ ξ t, 0 ≤ t → (W ξ).atReal t = evolution b A t (ξ : E) := by
    intro ξ t ht
    simpa [kernel] using ((hW ξ).1 t ht).2.2
  have hbound : ∀ ξ, ‖W ξ‖ ≤ K * ‖ξ‖ := by
    intro ξ
    simpa [contractionRate] using (hW ξ).2.2.2.2
  let L₀ : stableParameters b A →ₗ[ℝ] WeightedPath β E :=
    { toFun := W
      map_add' := by
        intro ξ η
        apply weightedPath_ext
        intro t ht
        rw [atReal_add, hval _ t ht, hval _ t ht, hval _ t ht]
        simp
      map_smul' := by
        intro c ξ
        apply weightedPath_ext
        intro t ht
        rw [atReal_smul, hval _ t ht, hval _ t ht]
        simp }
  let L := L₀.mkContinuous K hbound
  exact ⟨L, L₀.mkContinuous_norm_le (le_trans zero_le_one hK) hbound, hval⟩

/-- Application of the abstract inverse estimate to the exact weighted path
space used by the frozen interface, using completeness only as a conditional
proof input. The other three premises are kept in the mandated order. -/
theorem inverse_derivative_conditional
    (_hfixed : fixedPointsExpected.{u, v})
    (hcomplete : weightedCompleteExpected.{v})
    (_hnorm : weightedNormExpected.{v})
    (_hrepr : weightedRepresentationExpected.{v})
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (β : ℝ) (N : WeightedPath β E → WeightedPath β E) {q : ℝ}
    (hq : q < 1) (hN : ∀ w, ‖fderiv ℝ N w‖ ≤ q) :
    ∀ w, ∃ J : WeightedPath β E ≃L[ℝ] WeightedPath β E,
      J.toContinuousLinearMap = ContinuousLinearMap.id ℝ _ - fderiv ℝ N w ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ (1 - q)⁻¹ := by
  let := hcomplete (E := E) β
  intro w
  exact inverse_sub_of_norm_le (fderiv ℝ N w) (hN w) hq

/-- Assembly step once the nonlinear weighted integral operator has been
constructed and its Cᵏ regularity and derivative bound have been proved.
Those analytic inputs remain explicit here: this is not the original target. -/
theorem regularity_from_operator_conditional
    (hfixed : fixedPointsExpected.{u, v})
    (hcomplete : weightedCompleteExpected.{v})
    (hnorm : weightedNormExpected.{v})
    (hrepr : weightedRepresentationExpected.{v})
    {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (K α β δ : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hβ : 0 < β) (hβα : β < α) (hδ : 0 ≤ δ) (hq : contractionRate K α β δ < 1)
    (r : E → E) (hr : r 0 = 0) (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (k : ℕ∞) (hk : 1 ≤ k)
    (N : WeightedPath β E → WeightedPath β E)
    (hNeq : NonlinearOperator b A r β N) (hNsmooth : ContDiff ℝ k N)
    (hNbound : ∀ w, ‖fderiv ℝ N w‖ ≤ contractionRate K α β δ) :
    (∀ w, ∃ J : WeightedPath β E ≃L[ℝ] WeightedPath β E,
      J.toContinuousLinearMap = ContinuousLinearMap.id ℝ _ - fderiv ℝ N w ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ (1 - contractionRate K α β δ)⁻¹) ∧
    ∃ W : stableParameters b A → WeightedPath β E,
      ContDiff ℝ k W ∧ SolutionFamily b A r K α β δ W := by
  let := hcomplete (E := E) β
  have hInv := inverse_derivative_conditional hfixed hcomplete hnorm hrepr β N hq hNbound
  refine ⟨hInv, ?_⟩
  obtain ⟨L, _, hL⟩ := exists_linearEvolution_conditional hfixed hcomplete hnorm hrepr
    b A hA K α β hK hα hd hβ hβα
  obtain ⟨W, hW⟩ := exists_solutionFamily_conditional hfixed hcomplete hnorm hrepr
    b A hA K α β δ hK hα hd hβ hβα hδ hq r hr hlip
  have hfix : ∀ ξ, W ξ = L ξ + N (W ξ) := by
    intro ξ
    apply weightedPath_ext
    intro t ht
    rw [atReal_add, hL ξ t ht, ((hNeq (W ξ) t ht).2.2)]
    have hh := ((hW ξ).1 t ht).2.2
    simpa only [sub_eq_add_neg, add_assoc] using hh
  have hunique : ∀ ξ y, y = L ξ + N y → y = W ξ := by
    intro ξ y hy
    apply (hW ξ).2.1 y
    intro t ht
    obtain ⟨hs, hu, hv⟩ := hNeq y t ht
    refine ⟨hs, hu, ?_⟩
    have hh := congrArg (fun w : WeightedPath β E => w.atReal t) hy
    rw [atReal_add, hL ξ t ht, hv] at hh
    simpa only [sub_eq_add_neg, add_assoc] using hh
  refine ⟨W, contDiff_fixedPoint_family ?_ L N hNsmooth W hfix hunique ?_, hW⟩
  · have hk0 : k ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hk)
    simpa using hk0
  · intro w
    obtain ⟨J, hJ, _⟩ := hInv w
    exact ⟨J, hJ⟩

end Conditional

section BoundedSuperposition
open scoped BoundedContinuousFunction
universe uB
variable {ι : Type*} {E F : Type uB} [TopologicalSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise application, bundled in the supremum norm. -/
def bcfApply (a : ι →ᵇ (E →L[ℝ] F)) (w : ι →ᵇ E) : ι →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => a t (w t))
    (by fun_prop) (‖a‖ * ‖w‖) (fun t =>
      ((a t).le_opNorm _).trans
        (mul_le_mul (a.norm_coe_le_norm t) (w.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg a)))

@[simp] theorem bcfApply_eval (a : ι →ᵇ (E →L[ℝ] F)) (w : ι →ᵇ E) (t : ι) :
    bcfApply a w t = a t (w t) := rfl

theorem bcfApply_norm (a : ι →ᵇ (E →L[ℝ] F)) (w : ι →ᵇ E) :
    ‖bcfApply a w‖ ≤ ‖a‖ * ‖w‖ :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr (fun t =>
    ((a t).le_opNorm _).trans
      (mul_le_mul (a.norm_coe_le_norm t) (w.norm_coe_le_norm t)
        (norm_nonneg _) (norm_nonneg a)))

def bcfApplyLinear (a : ι →ᵇ (E →L[ℝ] F)) : (ι →ᵇ E) →L[ℝ] (ι →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := bcfApply a
      map_add' := by intros; ext t; simp
      map_smul' := by intros; ext t; simp }
    ‖a‖ (bcfApply_norm a)

def bcfLift : (ι →ᵇ (E →L[ℝ] F)) →L[ℝ] ((ι →ᵇ E) →L[ℝ] (ι →ᵇ F)) :=
  LinearMap.mkContinuous
    { toFun := bcfApplyLinear
      map_add' := by intros; ext w t; simp [bcfApplyLinear]
      map_smul' := by intros; ext w t; simp [bcfApplyLinear] }
    1 (fun a => by
      simpa using ContinuousLinearMap.opNorm_le_bound (bcfApplyLinear a)
        (norm_nonneg a) (bcfApply_norm a))

/-- Composition by a globally bounded continuous map. This auxiliary
construction is used for derivatives, which are bounded by hypothesis. -/
def bcfCompose (f : E → F) (hf : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (w : ι →ᵇ E) : ι →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => f (w t))
    (hf.comp w.continuous) hb.choose (fun t => hb.choose_spec _)

@[simp] theorem bcfCompose_eval (f : E → F) (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (w : ι →ᵇ E) (t : ι) :
    bcfCompose f hf hb w t = f (w t) := rfl

/-- Uniform continuity is preserved by superposition in the supremum norm. -/
theorem bcfCompose_continuous (f : E → F) (hf : UniformContinuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Continuous (bcfCompose (ι := ι) f hf.continuous hb) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε / 2) (by positivity)
  refine ⟨η, hη, ?_⟩
  intro v hv
  apply lt_of_le_of_lt _ (half_lt_self hε)
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  simpa only [BoundedContinuousFunction.sub_apply, bcfCompose_eval, ← dist_eq_norm] using
    (hmod ((BoundedContinuousFunction.dist_coe_le_dist t).trans_lt hv)).le

/-- The Taylor remainder is uniform in every evaluation point, so this is a
Fréchet derivative in supremum norm, rather than just a pointwise derivative. -/
theorem bcfCompose_hasFDerivAt (f : E → F) (hf : Differentiable ℝ f)
    (hu : UniformContinuous (fderiv ℝ f))
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hdb : ∃ C : ℝ, ∀ x, ‖fderiv ℝ f x‖ ≤ C) (w : ι →ᵇ E) :
    HasFDerivAt (bcfCompose f hf.continuous hb)
      (bcfLift (bcfCompose (fderiv ℝ f) hu.continuous hdb w)) w := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨η, hη, hrem⟩ := uniform_taylor_remainder f hf hu hε
  filter_upwards [Metric.ball_mem_nhds (0 : ι →ᵇ E) hη] with v hv
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  change ‖f (w t + v t) - f (w t) - fderiv ℝ f (w t) (v t)‖ ≤ ε * ‖v‖
  exact (hrem (w t) (v t) ((v.norm_coe_le_norm t).trans_lt
    (by simpa [Metric.mem_ball, dist_zero_right] using hv))).trans
      (mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hε.le)

/-- Bounded uniformly continuous jets, including the zeroth jet, for the
auxiliary bounded superposition theorem. -/
def boundedUCJets (m : ℕ) (f : E → F) : Prop :=
  ∀ j : ℕ, j ≤ m → (∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C) ∧
    UniformContinuous (iteratedFDeriv ℝ j f)

theorem boundedUCJets_zero {m : ℕ} {f : E → F} (h : boundedUCJets m f) :
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧ UniformContinuous f := by
  obtain ⟨hb, hu⟩ := h 0 (Nat.zero_le _)
  refine ⟨by simpa using hb, ?_⟩
  have heq : f = (continuousMultilinearCurryFin0 ℝ E F) ∘ iteratedFDeriv ℝ 0 f := by
    funext x
    simp [iteratedFDeriv_zero_eq_comp]
  rw [heq]
  exact (continuousMultilinearCurryFin0 ℝ E F).isometry.uniformContinuous.comp hu

theorem boundedUCJets_fderiv {m : ℕ} {f : E → F} (h : boundedUCJets (m + 1) f) :
    boundedUCJets m (fderiv ℝ f) := by
  intro j hj
  obtain ⟨hb, hu⟩ := h (j + 1) (Nat.add_le_add_right hj 1)
  refine ⟨by simpa only [norm_iteratedFDeriv_fderiv] using hb, ?_⟩
  have heq : iteratedFDeriv ℝ j (fderiv ℝ f) =
      (continuousMultilinearCurryRightEquiv' ℝ j E F) ∘ iteratedFDeriv ℝ (j + 1) f := by
    funext x
    change _ = (continuousMultilinearCurryRightEquiv' ℝ j E F) (iteratedFDeriv ℝ (j + 1) f x)
    rw [iteratedFDeriv_succ_eq_comp_right]
    exact ((continuousMultilinearCurryRightEquiv' ℝ j E F).apply_symm_apply _).symm
  rw [heq]
  exact (continuousMultilinearCurryRightEquiv' ℝ j E F).isometry.uniformContinuous.comp hu

/-- Smooth bounded superposition on the full, possibly noncompact, time domain.
The induction is in the Banach norm and applies also to operator-valued jets. -/
theorem bcfCompose_contDiff (m : ℕ) (f : E → F) (hf : ContDiff ℝ m f)
    (hj : boundedUCJets m f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    ContDiff ℝ m (bcfCompose (ι := ι) f hf.continuous hb) := by
  induction m generalizing F with
  | zero =>
      exact contDiff_zero.mpr (bcfCompose_continuous f (boundedUCJets_zero hj).2 hb)
  | succ m ih =>
      have hj' := boundedUCJets_fderiv hj
      have hf' : ContDiff ℝ m (fderiv ℝ f) := hf.fderiv_right (by simp)
      obtain ⟨hdb, hdu⟩ := boundedUCJets_zero hj'
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun w => bcfLift (bcfCompose (fderiv ℝ f) hf'.continuous hdb w), ?_, ?_⟩
      · exact ContDiff.comp (g := (bcfLift (ι := ι) (E := E) (F := F)))
          (ContinuousLinearMap.contDiff _) (ih (fderiv ℝ f) hf' hj' hdb)
      · intro w
        exact bcfCompose_hasFDerivAt f (hf.differentiable (by simp)) hdu hb hdb w

end BoundedSuperposition

section WeightedSuperposition
open Specs.D13Unified.Ch20.PerronRegularity
open scoped BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : ℝ}

/-- A bounded operator field acts on weighted coordinates with no loss in norm. -/
def weightedApply (a : HalfLine →ᵇ (E →L[ℝ] E)) (w : WeightedPath β E) :
    WeightedPath β E := ⟨bcfApply a w.weighted⟩

@[simp] theorem weightedApply_eval (a : HalfLine →ᵇ (E →L[ℝ] E))
    (w : WeightedPath β E) (t : HalfLine) :
    (weightedApply a w).eval t = a t (w.eval t) := by
  change Real.exp (-β * (t : ℝ)) • a t (w.weighted t) = _
  rw [WeightedPath.eval, map_smul]

theorem weightedApply_norm (a : HalfLine →ᵇ (E →L[ℝ] E)) (w : WeightedPath β E) :
    ‖weightedApply a w‖ ≤ ‖a‖ * ‖w‖ := bcfApply_norm a w.weighted

def weightedApplyLinear (a : HalfLine →ᵇ (E →L[ℝ] E)) :
    WeightedPath β E →L[ℝ] WeightedPath β E :=
  LinearMap.mkContinuous
    { toFun := weightedApply a
      map_add' := by intros; apply WeightedPath.ext; intro t; simp
      map_smul' := by intros; apply WeightedPath.ext; intro t; simp }
    ‖a‖ (weightedApply_norm a)

def weightedLift : (HalfLine →ᵇ (E →L[ℝ] E)) →L[ℝ]
    (WeightedPath β E →L[ℝ] WeightedPath β E) :=
  LinearMap.mkContinuous
    { toFun := weightedApplyLinear
      map_add' := by intros; ext w t; simp [weightedApplyLinear]
      map_smul' := by intros; ext w t; simp [weightedApplyLinear] }
    1 (fun a => by
      simpa using ContinuousLinearMap.opNorm_le_bound (weightedApplyLinear a)
        (norm_nonneg a) (weightedApply_norm a))

@[simp] theorem weightedLift_eval (a : HalfLine →ᵇ (E →L[ℝ] E))
    (w : WeightedPath β E) (t : HalfLine) :
    ((weightedLift a) w).eval t = a t (w.eval t) := weightedApply_eval a w t

/-- Forgetting a nonnegative weight is a bounded linear map of norm at most one. -/
def unweightedPath (hβ : 0 ≤ β) : WeightedPath β E →L[ℝ] (HalfLine →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun w => BoundedContinuousFunction.ofNormedAddCommGroup w.eval
        w.eval_continuous ‖w‖ (fun t => eval_le_norm hβ w t)
      map_add' := by intros; ext t; simp
      map_smul' := by intros; ext t; simp }
    1 (fun w => by
      simpa using (BoundedContinuousFunction.norm_le (norm_nonneg w)).mpr
        (fun t => eval_le_norm hβ w t))

@[simp] theorem unweightedPath_eval (hβ : 0 ≤ β) (w : WeightedPath β E) (t : HalfLine) :
    unweightedPath hβ w t = w.eval t := rfl

/-- The positive jets of r are precisely all the jets needed for the bounded
operator-valued superposition of Dr. No boundedness of r is introduced. -/
theorem regularDerivatives_jets {k : ℕ∞} (r : E → E)
    (hj : regularDerivatives k r) {m : ℕ} (hm : ((m + 1 : ℕ) : ℕ∞) ≤ k) :
    boundedUCJets m (fderiv ℝ r) := by
  intro j hjm
  have hjm' : ((j + 1 : ℕ) : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.add_le_add_right hjm 1
  have hjk : ((j + 1 : ℕ) : ℕ∞) ≤ k := hjm'.trans hm
  obtain ⟨⟨C, _, hb⟩, hu⟩ := hj (j + 1) (by omega) hjk
  refine ⟨⟨C, by simpa only [norm_iteratedFDeriv_fderiv] using hb⟩, ?_⟩
  have heq : iteratedFDeriv ℝ j (fderiv ℝ r) =
      (continuousMultilinearCurryRightEquiv' ℝ j E E) ∘ iteratedFDeriv ℝ (j + 1) r := by
    funext x
    change _ = (continuousMultilinearCurryRightEquiv' ℝ j E E) (iteratedFDeriv ℝ (j + 1) r x)
    rw [iteratedFDeriv_succ_eq_comp_right]
    exact ((continuousMultilinearCurryRightEquiv' ℝ j E E).apply_symm_apply _).symm
  rw [heq]
  exact (continuousMultilinearCurryRightEquiv' ℝ j E E).isometry.uniformContinuous.comp hu

/-- Differentiation of superposition in the original weighted Banach norm. -/
theorem superposition_hasFDerivAt (hβ : 0 ≤ β) (r : E → E)
    (δ : ℝ) (hδ : 0 ≤ δ) (hr : r 0 = 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (hd : Differentiable ℝ r) (hu : UniformContinuous (fderiv ℝ r))
    (hb : ∃ C : ℝ, ∀ x, ‖fderiv ℝ r x‖ ≤ C) (w : WeightedPath β E) :
    HasFDerivAt (WeightedPath.superposition r δ hδ hr hlip)
      (weightedLift (bcfCompose (fderiv ℝ r) hu.continuous hb (unweightedPath hβ w))) w := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨η, hη, hrem⟩ := weighted_taylor_remainder hβ r hd hu hε
  filter_upwards [Metric.ball_mem_nhds (0 : WeightedPath β E) hη] with v hv
  apply (WeightedPath.norm_le_iff _ (by positivity)).mpr
  intro t
  simpa only [WeightedPath.eval_sub, WeightedPath.eval_add, WeightedPath.eval_superposition,
    weightedLift_eval, bcfCompose_eval, unweightedPath_eval] using
      hrem w v (by simpa [Metric.mem_ball, dist_zero_right] using hv) t

/-- All orders, including the highest continuous derivative, are controlled in
weighted norm. Finite-time smooth dependence is not used. -/
theorem superposition_contDiff (hβ : 0 ≤ β) (r : E → E)
    (δ : ℝ) (hδ : 0 ≤ δ) (hr : r 0 = 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (k : ℕ∞) (hk : 1 ≤ k) (hc : ContDiff ℝ k r) (hj : regularDerivatives k r) :
    ContDiff ℝ k (WeightedPath.superposition (β := β) r δ hδ hr hlip) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro m hm
  cases m with
  | zero =>
      apply contDiff_zero.mpr
      exact (LipschitzWith.of_dist_le_mul (K := NNReal.mk δ hδ) (fun w v => by
        simpa only [dist_eq_norm, NNReal.coe_mk] using
          WeightedPath.superposition_lipschitz r δ hδ hr hlip w v)).continuous
  | succ m =>
      have hj' := regularDerivatives_jets r hj hm
      obtain ⟨hb, hu⟩ := boundedUCJets_zero hj'
      have hcr : ContDiff ℝ (m + 1) r := hc.of_le (by exact_mod_cast hm)
      have hcd : ContDiff ℝ m (fderiv ℝ r) := hcr.fderiv_right (by simp)
      have hs := bcfCompose_contDiff (ι := HalfLine) m (fderiv ℝ r) hcd hj' hb
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun w => weightedLift (bcfCompose (fderiv ℝ r) hu.continuous hb
        (unweightedPath hβ w)), ?_, ?_⟩
      · exact (weightedLift (β := β) (E := E)).contDiff.comp
          (hs.comp (unweightedPath hβ).contDiff)
      · intro w
        exact superposition_hasFDerivAt hβ r δ hδ hr hlip
          (hcr.differentiable (by simp)) hu hb w

end WeightedSuperposition

section GreenOperator
open Specs.D13Unified.Ch20.PerronWeightedIntegrals
open PerronFixedPoints.WeightedGreen
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Linearity of the already constructed convergent half-line integrals. -/
theorem greenPath_linear_combination (L Ps Pu : E →L[ℝ] E) (K α β : ℝ)
    (hK : 1 ≤ K) (hβ : 0 < β) (hβα : β < α)
    (hs : StableDecay L Ps K α) (hu : UnstableDecay L Pu K α)
    (g h : WeightedPath β E) (c d : ℝ) :
    greenPath L Ps Pu K α β hK hβ hβα hs hu (c • g + d • h) =
      c • greenPath L Ps Pu K α β hK hβ hβα hs hu g +
        d • greenPath L Ps Pu K α β hK hβ hβα hs hu h := by
  apply WeightedPath.ext
  intro t
  rw [WeightedPath.eval_add, WeightedPath.eval_smul, WeightedPath.eval_smul,
    greenPath_eval, greenPath_eval, greenPath_eval]
  have heq : (c • g + d • h).atReal = fun s => c • g.atReal s + d • h.atReal s := by
    funext s
    rw [atReal_add, atReal_smul, atReal_smul]
  rw [heq]
  exact PerronWeightedIntegrals.integral_linearity L Ps Pu K α β hK hβ hβα hs hu
    g.atReal h.atReal ‖g‖ ‖h‖ (weightedBound β g) (weightedBound β h) c d t t.property

/-- The half-line Green operator as a bounded linear map on the actual
weighted space. Its bound is independent of the forcing. -/
def greenLinear (L Ps Pu : E →L[ℝ] E) (K α β : ℝ)
    (hK : 1 ≤ K) (hβ : 0 < β) (hβα : β < α)
    (hs : StableDecay L Ps K α) (hu : UnstableDecay L Pu K α) :
    WeightedPath β E →L[ℝ] WeightedPath β E :=
  LinearMap.mkContinuous
    { toFun := greenPath L Ps Pu K α β hK hβ hβα hs hu
      map_add' := by
        intro g h
        simpa using greenPath_linear_combination L Ps Pu K α β hK hβ hβα hs hu g h 1 1
      map_smul' := by
        intro c g
        simpa [greenPath_zero L Ps Pu K α β hK hβ hβα hs hu] using
          greenPath_linear_combination L Ps Pu K α β hK hβ hβα hs hu g 0 c 0 }
    (K * ((α - β)⁻¹ + (α + β)⁻¹)) (fun g => by
      convert greenPath_norm L Ps Pu K α β hK hβ hβα hs hu g using 1 <;> ring)

end GreenOperator

section Assembly
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.PerronFixedPoints
open Specs.D13Unified.Ch20.PerronRegularity
open _root_.D13Unified.Ch07
open MeasureTheory
universe u v

/-- Lyapunov–Perron regularity on the infinite-time weighted Banach space,
with the integral equation, ODE, stable initial projection, uniqueness and
quantitative estimate retained from the fixed-point theorem. -/
theorem perron_regularity : regularityExpected.{u, v} := by
  intro n _ _ E _ _ _ b A hA K α β δ hK hα hd hβ hβα hδ hq r k hr hlip hk hc hj
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L := matrixOperatorEquiv b A
  let Ps := projection b A true
  let Pu := projection b A false
  obtain ⟨hs, hu⟩ := PerronFixedPoints.operator_decay b A K α hd
  let R := WeightedPath.superposition (β := β) r δ hδ hr hlip
  let G := greenLinear L Ps Pu K α β hK hβ hβα hs hu
  let N : WeightedPath β E → WeightedPath β E := fun w => G (R w)
  have hNsmooth : ContDiff ℝ k N :=
    G.contDiff.comp (superposition_contDiff hβ.le r δ hδ hr hlip k hk hc hj)
  have hcoef : 0 ≤ K * ((α - β)⁻¹ + (α + β)⁻¹) := by
    have : 0 ≤ K := zero_le_one.trans hK
    have : 0 < α - β := sub_pos.mpr hβα
    have : 0 < α + β := by linarith
    positivity
  have hNlip : ∀ w v : WeightedPath β E,
      ‖N w - N v‖ ≤ contractionRate K α β δ * ‖w - v‖ := by
    intro w v
    calc
      ‖N w - N v‖ ≤ (K * ((α - β)⁻¹ + (α + β)⁻¹)) * ‖R w - R v‖ :=
        PerronFixedPoints.WeightedGreen.greenPath_lipschitz L Ps Pu K α β
          hK hβ hβα hs hu (R w) (R v)
      _ ≤ (K * ((α - β)⁻¹ + (α + β)⁻¹)) * (δ * ‖w - v‖) :=
        mul_le_mul_of_nonneg_left
          (WeightedPath.superposition_lipschitz r δ hδ hr hlip w v) hcoef
      _ = contractionRate K α β δ * ‖w - v‖ := by unfold contractionRate; ring
  have hq0 : 0 ≤ contractionRate K α β δ := by
    convert mul_nonneg hcoef hδ using 1
    unfold contractionRate
    ring
  have hNbound : ∀ w, ‖fderiv ℝ N w‖ ≤ contractionRate K α β δ :=
    remainder_derivative_le N hq0 hNlip
  have he (t : ℝ) : PerronIntegralODE.evolution L t = evolution b A t :=
    (matrixOperator_exp b A t).symm
  have hR (w : WeightedPath β E) : (R w).atReal = fun s => r (w.atReal s) := by
    funext s
    by_cases hs0 : 0 ≤ s
    · rw [WeightedPath.atReal_nonneg _ hs0, WeightedPath.atReal_nonneg _ hs0]
      exact WeightedPath.eval_superposition r δ hδ hr hlip w _
    · simp [WeightedPath.atReal, hs0, hr]
  have hkern (w : WeightedPath β E) (stable : Bool) (t : ℝ) :
      (fun s => PerronIntegralODE.evolution L (t-s)
        ((if stable then Ps else Pu) ((R w).atReal s))) = kernel b A r β w stable t := by
    funext s
    rw [he, hR]
    cases stable <;> rfl
  have hNeq : NonlinearOperator b A r β N := by
    intro w t ht
    have hfinite := PerronIntegralODE.finite_integrable L Ps (R w).atReal_continuousOn ht
    have htail := (PerronWeightedIntegrals.unstable_estimate L Pu K α β ‖R w‖
      hK hβ hβα hu (R w).atReal
      (PerronFixedPoints.WeightedGreen.weightedBound β (R w)) t ht).1
    change IntegrableOn (fun s => PerronIntegralODE.evolution L (t - s)
      (Pu ((R w).atReal s))) (Ici t) at htail
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← hkern w true t, ↓reduceIte] using hfinite
    · simpa only [← hkern w false t, Bool.false_eq_true, ↓reduceIte] using htail
    · change (PerronFixedPoints.WeightedGreen.greenPath L Ps Pu K α β
          hK hβ hβα hs hu (R w)).atReal t = _
      rw [PerronFixedPoints.WeightedGreen.greenPath_atReal]
      dsimp only [PerronIntegralODE.stableIntegral, PerronIntegralODE.unstableIntegral]
      rw [← hkern w true t, ← hkern w false t]
      rfl
      exact ht
  obtain ⟨hinv, W, hWc, hW⟩ := regularity_from_operator_conditional
    PerronFixedPoints.perron_fixed_points weighted_complete weighted_norm weighted_representation
    b A hA K α β δ hK hα hd hβ hβα hδ hq r hr hlip k hk N hNeq hNsmooth hNbound
  exact ⟨N, W, hNeq, hNsmooth, hNbound, hinv, hWc, hW⟩

end Assembly
end D13Unified.Ch20.PerronRegularity
