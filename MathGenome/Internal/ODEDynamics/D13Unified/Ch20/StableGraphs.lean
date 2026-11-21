import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.StableGraphs
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.PerronRegularity
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.Cutoff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Comp

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped ContDiff NNReal

namespace D13Unified.Ch20.StableGraphs
open D13Unified.Ch07
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.PerronFixedPoints
open Specs.D13Unified.Ch20.PerronRegularity
open Specs.D13Unified.Ch20.StableGraphs

universe u v
variable {n : Type u} [Fintype n] [DecidableEq n]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Evaluation at zero in the original, unweighted coordinates. -/
def evaluationAtZero (β : ℝ) : WeightedPath β E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun w => w.eval ⟨0, by simp [HalfLine]⟩
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    1 (fun w => by simpa using WeightedPath.eval_norm_le w ⟨0, by simp [HalfLine]⟩)

@[simp] lemma evaluationAtZero_apply (β : ℝ) (w : WeightedPath β E) :
    evaluationAtZero β w = w.atReal 0 := by
  exact (WeightedPath.atReal_nonneg w le_rfl).symm

lemma projection_mem (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (s : Bool) (x : E) :
    b.equivFun (projection b A s x) ∈ realSpectralSpace A s := by
  rw [projection, matrixOperator_action]
  have heq : (Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A s).mulVec (b.equivFun x) =
      projectionValue A s (b.equivFun x) := by
    simpa only [Specs.D13Unified.Ch20.Dichotomy.projectionMatrix,
      Matrix.toLinAlgEquiv'_apply] using
      congrArg (fun f : Module.End ℝ (n → ℝ) => f (b.equivFun x))
        (Matrix.toLinAlgEquiv'.apply_symm_apply (projectionValue A s))
  rw [heq, projection_eq A hA s]
  exact Submodule.projection_apply_mem _ _

/-- Projection to the actual stable subtype, not a new copy of that space. -/
def stableParameterProjection (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) : E →L[ℝ] stableParameters b A :=
  (projection b A true).codRestrict _ (projection_mem b A hA true)

def unstableParameterProjection (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) : E →L[ℝ] unstableParameters b A :=
  (projection b A false).codRestrict _ (projection_mem b A hA false)

@[simp] lemma stableParameterProjection_coe (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (x : E) :
    (stableParameterProjection b A hA x : E) = projection b A true x := rfl

@[simp] lemma unstableParameterProjection_coe (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (x : E) :
    (unstableParameterProjection b A hA x : E) = projection b A false x := rfl

lemma projection_sum (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (x : E) :
    projection b A true x + projection b A false x = x := by
  have h := congrArg (fun L : E →L[ℝ] E => L x)
    (PerronFixedPoints.operator_projection_laws b A hA).1
  simpa using h

lemma stableParameterProjection_left (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (ξ : stableParameters b A) :
    stableParameterProjection b A hA (ξ : E) = ξ := by
  apply Subtype.ext
  exact PerronFixedPoints.stable_projection_eq_self b A hA ξ ξ.property

lemma unstableParameterProjection_stable (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (ξ : stableParameters b A) :
    unstableParameterProjection b A hA (ξ : E) = 0 := by
  apply Subtype.ext
  change projection b A false (ξ : E) = 0
  have hs := PerronFixedPoints.stable_projection_eq_self b A hA ξ ξ.property
  have hsum := projection_sum b A hA ξ
  rw [hs] at hsum
  exact add_left_cancel (hsum.trans (add_zero (ξ : E)).symm)

/-- The exact decay constant follows from the weighted norm, including at t=0. -/
lemma trajectory_bound {b : Module.Basis n ℝ E} {A : Matrix n n ℝ}
    {r : E → E} {K α β δ : ℝ}
    {W : stableParameters b A → WeightedPath β E}
    (hW : SolutionFamily b A r K α β δ W) (ξ : stableParameters b A)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖(W ξ).atReal t‖ ≤ (K / (1 - contractionRate K α β δ)) *
      ‖(ξ : E)‖ * Real.exp (-β * t) := by
  rw [WeightedPath.atReal_nonneg _ ht]
  calc
    ‖(W ξ).eval ⟨t, ht⟩‖ ≤ Real.exp (-β * t) * ‖W ξ‖ :=
      WeightedPath.eval_norm_le _ _
    _ ≤ Real.exp (-β * t) * (K * ‖(ξ : E)‖ / (1 - contractionRate K α β δ)) :=
      mul_le_mul_of_nonneg_left (hW ξ).2.2.2.2 (Real.exp_pos _).le
    _ = _ := by ring

/-- A flat state remainder induces a flat superposition operator in weighted norm. -/
lemma superposition_hasFDerivAt_zero {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (r : E → E) (hr : r 0 = 0) (hrd : HasFDerivAt r (0 : E →L[ℝ] E) 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (k : ℕ∞) (hk : 1 ≤ k) (hc : ContDiff ℝ k r) (hj : regularDerivatives k r) :
    HasFDerivAt (WeightedPath.superposition (β := β) r δ hδ hr hlip)
      (0 : WeightedPath β E →L[ℝ] WeightedPath β E) 0 := by
  obtain ⟨⟨C, _, hC⟩, hu⟩ := PerronRegularity.regularDerivatives_fderiv hk r hj
  have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hk))
  have hd := PerronRegularity.superposition_hasFDerivAt hβ r δ hδ hr hlip
    (hc.differentiable hk0) hu ⟨C, hC⟩ (0 : WeightedPath β E)
  have hz : PerronRegularity.bcfCompose (fderiv ℝ r) hu.continuous ⟨C, hC⟩
      (PerronRegularity.unweightedPath hβ (0 : WeightedPath β E)) = 0 := by
    ext t
    simp [PerronRegularity.bcfCompose_eval, hrd.fderiv]
  rw [hz] at hd
  simpa only [map_zero] using hd

/-- The integral identity identifies any represented nonlinear Perron operator
with the bounded Green map after superposition. This proves, rather than assumes,
that its derivative vanishes at the zero path. -/
lemma nonlinearOperator_hasFDerivAt_zero
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (K α β δ : ℝ) (hK : 1 ≤ K) (hd : dichotomyBounds b A K α)
    (hβ : 0 < β) (hβα : β < α) (hδ : 0 ≤ δ)
    (r : E → E) (hr : r 0 = 0) (hrd : HasFDerivAt r (0 : E →L[ℝ] E) 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (k : ℕ∞) (hk : 1 ≤ k) (hc : ContDiff ℝ k r) (hj : regularDerivatives k r)
    (N : WeightedPath β E → WeightedPath β E) (hN : NonlinearOperator b A r β N) :
    HasFDerivAt N (0 : WeightedPath β E →L[ℝ] WeightedPath β E) 0 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨hs, hu⟩ := PerronFixedPoints.operator_decay b A K α hd
  let R := WeightedPath.superposition (β := β) r δ hδ hr hlip
  let G := PerronRegularity.greenLinear (matrixOperatorEquiv b A)
    (projection b A true) (projection b A false) K α β hK hβ hβα hs hu
  have he (t : ℝ) : PerronIntegralODE.evolution (matrixOperatorEquiv b A) t =
      evolution b A t := (matrixOperator_exp b A t).symm
  have hR (w : WeightedPath β E) : (R w).atReal = fun s => r (w.atReal s) := by
    funext s
    by_cases hs0 : 0 ≤ s
    · rw [WeightedPath.atReal_nonneg _ hs0, WeightedPath.atReal_nonneg _ hs0]
      exact WeightedPath.eval_superposition r δ hδ hr hlip w _
    · simp [WeightedPath.atReal, hs0, hr]
  have heq : N = fun w => G (R w) := by
    funext w
    apply PerronRegularity.weightedPath_ext
    intro t ht
    rw [(hN w t ht).2.2]
    change _ = (PerronFixedPoints.WeightedGreen.greenPath (matrixOperatorEquiv b A)
      (projection b A true) (projection b A false) K α β hK hβ hβα hs hu (R w)).atReal t
    rw [PerronFixedPoints.WeightedGreen.greenPath_atReal _ _ _ _ _ _ _ _ _ _ _ _ _ ht]
    simp only [PerronIntegralODE.stableIntegral, PerronIntegralODE.unstableIntegral,
      he, hR, kernel]
  rw [heq]
  simpa only [Function.comp_def, R, ContinuousLinearMap.comp_zero] using
    G.hasFDerivAt.comp 0
      (superposition_hasFDerivAt_zero hβ.le hδ r hr hrd hlip k hk hc hj)

/-- The zero parameter really gives the zero path; this uses the actual norm
estimate and does not assume an equilibrium certificate for the selected family. -/
lemma solutionFamily_zero {b : Module.Basis n ℝ E} {A : Matrix n n ℝ}
    {r : E → E} {K α β δ : ℝ} {W : stableParameters b A → WeightedPath β E}
    (hW : SolutionFamily b A r K α β δ W) : W 0 = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa using (hW 0).2.2.2.2

/-- Differentiate the affine fixed-point identity at zero in the Banach norm.
Flatness of the nonlinear operator leaves precisely the homogeneous evolution. -/
lemma solutionFamily_hasFDerivAt_zero
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (K α β δ : ℝ) (r : E → E) (k : ℕ∞) (hk : 1 ≤ k)
    (N : WeightedPath β E → WeightedPath β E) (hN : NonlinearOperator b A r β N)
    (hNd : HasFDerivAt N (0 : WeightedPath β E →L[ℝ] WeightedPath β E) 0)
    (W : stableParameters b A → WeightedPath β E) (hWc : ContDiff ℝ k W)
    (hW : SolutionFamily b A r K α β δ W)
    (L : stableParameters b A →L[ℝ] WeightedPath β E)
    (hL : ∀ ξ t, 0 ≤ t → (L ξ).atReal t = evolution b A t (ξ : E)) :
    HasFDerivAt W L 0 := by
  have hfix : W = fun ξ => L ξ + N (W ξ) := by
    funext ξ
    apply PerronRegularity.weightedPath_ext
    intro t ht
    rw [WeightedPath.atReal_add, hL ξ t ht, (hN (W ξ) t ht).2.2]
    simpa only [sub_eq_add_neg, add_assoc] using ((hW ξ).1 t ht).2.2
  have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hk))
  have hWd := (hWc.differentiable hk0 0).hasFDerivAt
  have hNd' : HasFDerivAt N (0 : WeightedPath β E →L[ℝ] WeightedPath β E) (W 0) := by
    rw [solutionFamily_zero hW]
    exact hNd
  have hh := L.hasFDerivAt.add (hNd'.comp 0 hWd)
  simp only [ContinuousLinearMap.zero_comp, add_zero] at hh
  rw [hfix]
  exact hh

lemma stableParameterProjection_unstable (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (η : unstableParameters b A) :
    stableParameterProjection b A hA (η : E) = 0 := by
  apply Subtype.ext
  change projection b A true (η : E) = 0
  apply b.equivFun.injective
  rw [projection, matrixOperator_action, map_zero]
  have heq : (Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A true).mulVec (b.equivFun η) =
      projectionValue A true (b.equivFun η) := by
    simpa only [Specs.D13Unified.Ch20.Dichotomy.projectionMatrix,
      Matrix.toLinAlgEquiv'_apply] using
      congrArg (fun f : Module.End ℝ (n → ℝ) => f (b.equivFun η))
        (Matrix.toLinAlgEquiv'.apply_symm_apply (projectionValue A true))
  rw [heq, projection_eq A hA true]
  exact Submodule.projection_apply_of_mem_right (hyperbolic_splitting A hA) η.property

/-- A complementary Cᵏ graph is a global embedded manifold, with its
subspace as model. Its stable projection is a continuous smooth left inverse,
which also proves full rank everywhere, including zero-dimensional models. -/
lemma stable_graph_geometry (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (k : ℕ∞) (hk : 1 ≤ k)
    (h : stableParameters b A → unstableParameters b A)
    (hc : ContDiff ℝ k h) (h0 : h 0 = 0)
    (hd0 : HasFDerivAt h (0 : stableParameters b A →L[ℝ] unstableParameters b A) 0) :
    GraphGeometry k (stableParameters b A) (unstableParameters b A) h := by
  let S := stableParameters b A
  let T := unstableParameters b A
  let P := stableParameterProjection b A hA
  have hg : ContDiff ℝ k (graphMap h) :=
    S.subtypeL.contDiff.add (T.subtypeL.contDiff.comp hc)
  have hinv : Function.LeftInverse P (graphMap h) := by
    intro ξ
    change P ((ξ : E) + (h ξ : E)) = ξ
    rw [map_add, stableParameterProjection_left, stableParameterProjection_unstable, add_zero]
  have hembed := hinv.isEmbedding P.continuous hg.continuous
  have hrange : Set.range (graphMap h) = {x : E | graphMap h (P x) = x} := by
    ext x
    constructor
    · rintro ⟨ξ, rfl⟩
      simp only [Set.mem_ofPred_eq, hinv ξ]
    · intro hx
      exact ⟨P x, hx⟩
  have hclosed : IsClosed (Set.range (graphMap h)) := by
    rw [hrange]
    exact isClosed_eq (hg.continuous.comp P.continuous) continuous_id
  have hfull : ∀ ξ, Function.Injective (fderiv ℝ (graphMap h) ξ) := by
    intro ξ
    have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hk))
    have hh := P.hasFDerivAt.comp ξ ((hg.differentiable hk0 ξ).hasFDerivAt)
    have hid : P ∘ graphMap h = id := funext hinv
    rw [hid] at hh
    have hcL : P.comp (fderiv ℝ (graphMap h) ξ) = ContinuousLinearMap.id ℝ S :=
      hh.unique (hasFDerivAt_id ξ)
    intro v w hvw
    have he := congrArg P hvw
    change (P.comp (fderiv ℝ (graphMap h) ξ)) v =
      (P.comp (fderiv ℝ (graphMap h) ξ)) w at he
    rw [hcL] at he
    change v = w at he
    exact he
  refine ⟨hc, h0, hd0, hg, ⟨hembed, hclosed⟩, hfull, ?_⟩
  have hh : HasFDerivAt (graphMap h) (S.subtypeL + T.subtypeL.comp 0) 0 :=
    S.subtypeL.hasFDerivAt.add (T.subtypeL.hasFDerivAt.comp 0 hd0)
  simpa only [ContinuousLinearMap.comp_zero, add_zero] using hh

/-- Evaluation and unstable projection turn the regular Perron family into
a flat Cᵏ stable graph with the original quantitative trajectory estimate. -/
theorem stable_graph_geometry_exists : stableGeometryExpected.{u, v} := by
  intro n _ _ E _ _ _ b A hA K α β δ hK hα hd hβ hβα hδ hq r k hr hrd hlip hk hc hj
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨N, W, hN, _, _, _, hWc, hW⟩ := PerronRegularity.perron_regularity
    b A hA K α β δ hK hα hd hβ hβα hδ hq r k hr hlip hk hc hj
  obtain ⟨L, _, hL⟩ := PerronRegularity.exists_linearEvolution_conditional
    PerronFixedPoints.perron_fixed_points weighted_complete weighted_norm weighted_representation
    b A hA K α β hK hα hd hβ hβα
  have hNd := nonlinearOperator_hasFDerivAt_zero b A K α β δ hK hd hβ hβα hδ
    r hr hrd hlip k hk hc hj N hN
  have hWd := solutionFamily_hasFDerivAt_zero b A K α β δ r k hk N hN hNd W hWc hW L hL
  let Q := unstableParameterProjection b A hA
  let ev : WeightedPath β E →L[ℝ] E := evaluationAtZero β
  let h : stableParameters b A → unstableParameters b A := fun ξ => Q (ev (W ξ))
  have hhc : ContDiff ℝ k h := Q.contDiff.comp (ev.contDiff.comp hWc)
  have hh0 : h 0 = 0 := by simp [h, solutionFamily_zero hW]
  have heL (ξ : stableParameters b A) : ev (L ξ) = (ξ : E) := by
    rw [show ev (L ξ) = (L ξ).atReal 0 from evaluationAtZero_apply β _, hL ξ 0 le_rfl]
    simp [evolution, Specs.D13Unified.Ch07.MatrixExponential.exponentialValue]
  have hhder : HasFDerivAt h (0 : stableParameters b A →L[ℝ] unstableParameters b A) 0 := by
    have hcl : Q.comp (ev.comp L) = 0 := by
      apply ContinuousLinearMap.ext
      intro ξ
      change Q (ev (L ξ)) = 0
      rw [heL]
      exact unstableParameterProjection_stable b A hA ξ
    have hcomp : HasFDerivAt h (Q.comp (ev.comp L)) 0 :=
      Q.hasFDerivAt.comp 0 (ev.hasFDerivAt.comp 0 hWd)
    rw [hcl] at hcomp
    exact hcomp
  have hgraph (ξ : stableParameters b A) : (W ξ).atReal 0 = graphMap h ξ := by
    have hsum := projection_sum b A hA ((W ξ).atReal 0)
    rw [(hW ξ).2.2.2.1] at hsum
    simpa only [graphMap, h, Q, ev, evaluationAtZero_apply,
      unstableParameterProjection_coe] using hsum.symm
  exact ⟨h, W, stable_graph_geometry b A hA k hk h hhc hh0 hhder,
    hWc, hW, hgraph, trajectory_bound hW⟩

/-- Shifting an exponentially decaying half-line trajectory keeps it in
exactly the same weighted space, with the sharp shift factor. -/
def weightedShift {β : ℝ} (w : WeightedPath β E) (τ : ℝ) (hτ : 0 ≤ τ) :
    WeightedPath β E :=
  WeightedPath.ofPath β (fun t : HalfLine => w.eval ⟨(t : ℝ) + τ, add_nonneg t.property hτ⟩)
    (w.eval_continuous.comp (by fun_prop))
    (Real.exp (-β * τ) * ‖w‖) (by
      intro t
      calc
        Real.exp (β * (t : ℝ)) * ‖w.eval ⟨(t : ℝ) + τ, add_nonneg t.property hτ⟩‖ ≤
            Real.exp (β * (t : ℝ)) * (Real.exp (-β * ((t : ℝ) + τ)) * ‖w‖) :=
          mul_le_mul_of_nonneg_left (WeightedPath.eval_norm_le w _) (Real.exp_pos _).le
        _ = Real.exp (-β * τ) * ‖w‖ := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring)

lemma weightedShift_atReal {β : ℝ} (w : WeightedPath β E) {τ : ℝ} (hτ : 0 ≤ τ)
    {t : ℝ} (ht : 0 ≤ t) : (weightedShift w τ hτ).atReal t = w.atReal (t + τ) := by
  rw [WeightedPath.atReal_nonneg _ ht, weightedShift, WeightedPath.eval_ofPath,
    WeightedPath.atReal_nonneg _ (add_nonneg ht hτ)]

lemma weightedShift_norm_le {β : ℝ} (w : WeightedPath β E) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖weightedShift w τ hτ‖ ≤ Real.exp (-β * τ) * ‖w‖ := by
  apply (WeightedPath.norm_le_iff _ (by positivity)).mpr
  intro t
  rw [weightedShift, WeightedPath.eval_ofPath]
  calc
    Real.exp (β * (t : ℝ)) * ‖w.eval ⟨(t : ℝ) + τ, add_nonneg t.property hτ⟩‖ ≤
        Real.exp (β * (t : ℝ)) * (Real.exp (-β * ((t : ℝ) + τ)) * ‖w‖) :=
      mul_le_mul_of_nonneg_left (WeightedPath.eval_norm_le w _) (Real.exp_pos _).le
    _ = Real.exp (-β * τ) * ‖w‖ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The complete extension flow agrees with each constructed stable trajectory
on the whole forward half-line, not just for a short existence interval. -/
lemma flow_eq_solutionFamily
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (r : E → E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (φ : ℝ → E → E) (hφ : CompleteFlow (fun x => matrixOperatorEquiv b A x + r x) φ)
    (K α β : ℝ) (W : stableParameters b A → WeightedPath β E)
    (hW : SolutionFamily b A r K α β δ W) (ξ : stableParameters b A)
    (t : ℝ) (ht : 0 ≤ t) : φ t ((W ξ).atReal 0) = (W ξ).atReal t := by
  let F : E → E := fun x => matrixOperatorEquiv b A x + r x
  let Kr : ℝ≥0 := ⟨δ, hδ⟩
  have hrl : LipschitzWith Kr r := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    convert hlip x y using 1 <;> rfl
  have hF : LipschitzWith (‖matrixOperatorEquiv b A‖₊ + Kr) F :=
    (matrixOperatorEquiv b A).lipschitzWith.add hrl
  have hφc : Continuous (fun s => φ s ((W ξ).atReal 0)) :=
    continuous_iff_continuousAt.mpr (fun s => (hφ.2.2.2 _ s).continuousAt)
  have heq := ODE_solution_unique (v := fun _ => F) (a := 0) (b := t)
    (fun _ => hF) (hφc.continuousOn)
    (fun s _ => (hφ.2.2.2 _ s).hasDerivWithinAt)
    ((W ξ).atReal_continuousOn.mono (Icc_subset_Ici_self))
    (fun s hs => ((hW ξ).2.2.1 s hs.1).mono (by
      intro u hu
      exact le_trans hs.1 hu)) (hφ.2.1 _)
  exact heq ⟨ht, le_rfl⟩

/-- A bounded forward homogeneous orbit whose stable initial projection is
zero must vanish. Only the backward decay on the unstable range is used. -/
lemma homogeneous_halfLine_zero
    (L Ps Pu : E →L[ℝ] E) (K α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hSum : Ps + Pu = 1)
    (hComm : Commute Pu L)
    (hu : Specs.D13Unified.Ch20.PerronWeightedIntegrals.UnstableDecay L Pu K α)
    (w : WeightedPath β E)
    (hw : ∀ t, 0 ≤ t → HasDerivWithinAt w.atReal (L (w.atReal t)) (Ici 0) t)
    (h0 : Ps (w.atReal 0) = 0) : w = 0 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have heq (t : ℝ) (ht : 0 ≤ t) :
      w.atReal t = PerronIntegralODE.evolution L t (w.atReal 0) := by
    have hd (s : ℝ) : HasDerivAt
        (fun u => PerronIntegralODE.evolution L u (w.atReal 0))
        (L (PerronIntegralODE.evolution L s (w.atReal 0))) s := by
      simpa only [PerronIntegralODE.evolution, mul_apply_eq_comp, map_zero, add_zero] using
        (hasDerivAt_exp_smul_const' L s).clm_apply (hasDerivAt_const s (w.atReal 0))
    have hh := ODE_solution_unique (v := fun _ => L) (a := 0) (b := t)
      (fun _ => L.lipschitzWith)
      (w.atReal_continuousOn.mono Icc_subset_Ici_self)
      (fun s hs => (hw s hs.1).mono (fun u hu => hs.1.trans hu))
      ((continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn)
      (fun s _ => (hd s).hasDerivWithinAt)
      (by simp [PerronIntegralODE.evolution])
    exact hh ⟨ht, le_rfl⟩
  have hPu : Pu (w.atReal 0) = w.atReal 0 := by
    have h := congrArg (fun P : E →L[ℝ] E => P (w.atReal 0)) hSum
    simpa only [ContinuousLinearMap.add_apply, one_apply_eq_self, h0, zero_add] using h
  have hbound (t : ℝ) (ht : 0 ≤ t) :
      ‖w.atReal 0‖ ≤ K * Real.exp (-α * t) * ‖w‖ := by
    have hback : PerronIntegralODE.evolution L (-t) (Pu (w.atReal t)) = w.atReal 0 := by
      rw [heq t ht]
      have hc := congrArg (fun P : E →L[ℝ] E => P (w.atReal 0))
        (PerronIntegralODE.commute_evolution L Pu hComm t).eq
      change Pu (PerronIntegralODE.evolution L t (w.atReal 0)) =
        PerronIntegralODE.evolution L t (Pu (w.atReal 0)) at hc
      rw [hc, hPu]
      simpa only [neg_neg] using PerronIntegralODE.evolution_cancel L (-t) (w.atReal 0)
    calc
      ‖w.atReal 0‖ = ‖(PerronIntegralODE.evolution L (-t)).comp Pu (w.atReal t)‖ := by
        rw [ContinuousLinearMap.comp_apply, hback]
      _ ≤ ‖(PerronIntegralODE.evolution L (-t)).comp Pu‖ * ‖w.atReal t‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * Real.exp (-α * t)) * ‖w‖ :=
        mul_le_mul (hu t ht)
          (by simpa only [WeightedPath.atReal_nonneg _ ht] using
            WeightedPath.eval_norm_le_norm hβ w ⟨t, ht⟩)
          (norm_nonneg _) ((norm_nonneg _).trans (hu t ht))
  have hlim : Tendsto (fun t : ℝ => K * Real.exp (-α * t) * ‖w‖) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hα)
    simpa only [Function.comp_def, id_eq, neg_mul, mul_zero, zero_mul] using
      (hh.const_mul K).mul_const ‖w‖
  have hz : w.atReal 0 = 0 := norm_eq_zero.mp <|
    le_antisymm (ge_of_tendsto hlim (eventually_atTop.2 ⟨0, hbound⟩)) (norm_nonneg _)
  apply WeightedPath.ext
  intro t
  have hh := heq t t.property
  rw [hz, map_zero, WeightedPath.atReal_nonneg _ t.property] at hh
  simpa only [WeightedPath.eval_zero] using hh

@[simp] lemma weightedPath_atReal_sub {β : ℝ} (w v : WeightedPath β E) (t : ℝ) :
    (w - v).atReal t = w.atReal t - v.atReal t := by
  unfold WeightedPath.atReal
  split_ifs <;> simp

/-- Every weighted solution of the actual ODE satisfies the convergent Perron
formula. The integral equation is derived, rather than required as input. -/
lemma perronEquation_of_ode
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (K α β δ : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hβ : 0 < β) (hβα : β < α) (hδ : 0 ≤ δ)
    (r : E → E) (hr : r 0 = 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (ξ : stableParameters b A) (w : WeightedPath β E)
    (hw : ∀ t, 0 ≤ t → HasDerivWithinAt w.atReal
      (matrixOperatorEquiv b A (w.atReal t) + r (w.atReal t)) (Ici 0) t)
    (h0 : projection b A true (w.atReal 0) = (ξ : E)) :
    PerronEquation b A r β (ξ : E) w := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L := matrixOperatorEquiv b A
  let Ps := projection b A true
  let Pu := projection b A false
  obtain ⟨hs, hu⟩ := PerronFixedPoints.operator_decay b A K α hd
  obtain ⟨hSum, hCross, hCommS, hCommU⟩ := PerronFixedPoints.operator_projection_laws b A hA
  let g := WeightedPath.superposition (β := β) r δ hδ hr hlip w
  let a := PerronFixedPoints.stableLinearPath b A hA K α β hd hβα.le ξ ξ.property
  let v := a + PerronFixedPoints.WeightedGreen.greenPath L Ps Pu K α β hK hβ hβα hs hu g
  have he (t : ℝ) : PerronIntegralODE.evolution L t = evolution b A t :=
    (matrixOperator_exp b A t).symm
  have hg : g.atReal = fun s => r (w.atReal s) := by
    funext s
    by_cases hs0 : 0 ≤ s
    · rw [WeightedPath.atReal_nonneg _ hs0, WeightedPath.atReal_nonneg _ hs0]
      exact WeightedPath.eval_superposition r δ hδ hr hlip w _
    · simp [g, WeightedPath.atReal, hs0, hr]
  have hpath (t : ℝ) (ht : 0 ≤ t) :
      v.atReal t = PerronIntegralODE.perronPath L Ps Pu g.atReal ξ t := by
    dsimp only [v]
    rw [WeightedPath.atReal_add,
      PerronFixedPoints.WeightedGreen.greenPath_atReal L Ps Pu K α β hK hβ hβα hs hu g t ht]
    rw [show a.atReal t = evolution b A t ξ by
      rw [WeightedPath.atReal_nonneg _ ht]
      dsimp only [a]
      rw [PerronFixedPoints.stableLinearPath, WeightedPath.eval_ofPath]]
    dsimp only [PerronIntegralODE.perronPath]
    rw [he]
    abel
  have ht0 := (PerronWeightedIntegrals.unstable_estimate L Pu K α β ‖g‖
    hK hβ hβα hu g.atReal (PerronFixedPoints.WeightedGreen.weightedBound β g) 0 le_rfl).1
  have htail : MeasureTheory.IntegrableOn
      (fun s => PerronIntegralODE.evolution L (-s) (Pu (g.atReal s))) (Ici 0) := by
    change MeasureTheory.IntegrableOn
      (fun s => PerronIntegralODE.evolution L (0-s) (Pu (g.atReal s))) (Ici 0) at ht0
    simpa only [zero_sub] using ht0
  have hb := PerronIntegralODE.perron_integral_ode L Ps Pu hSum hCross hCommS hCommU
    g.atReal g.atReal_continuousOn htail ξ
    (PerronFixedPoints.stable_projection_eq_self b A hA ξ ξ.property)
  have hv (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt v.atReal
      (L (v.atReal t) + r (w.atReal t)) (Ici 0) t := by
    have hh := hb.2.2.1 t ht
    rw [← hpath t ht, congrFun hg t] at hh
    exact hh.congr_of_mem (fun u hu => hpath u hu) ht
  have hz : w - v = 0 := by
    apply homogeneous_halfLine_zero L Ps Pu K α β hα hβ.le hSum hCommU hu
    · intro t ht
      have hh := (hw t ht).sub (hv t ht)
      change HasDerivWithinAt (w.atReal - v.atReal)
        ((L (w.atReal t) + r (w.atReal t)) -
          (L (v.atReal t) + r (w.atReal t))) (Ici 0) t at hh
      simp only [← map_sub, add_sub_add_right_eq_sub] at hh
      rw [← weightedPath_atReal_sub] at hh
      exact hh.congr_of_mem (fun u _ => weightedPath_atReal_sub w v u) ht
    · rw [weightedPath_atReal_sub, map_sub, h0, hpath 0 le_rfl, hb.2.2.2, sub_self]
  have hwv : w = v := sub_eq_zero.mp hz
  intro t ht
  have hi := hb.1 t ht
  have hk (s : Bool) :
      (fun u => PerronIntegralODE.evolution L (t-u)
        ((if s then Ps else Pu) (g.atReal u))) = kernel b A r β w s t := by
    funext u
    rw [he, hg]
    cases s <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [← hk true, ↓reduceIte] using hi.1
  · simpa only [← hk false, Bool.false_eq_true, ↓reduceIte] using hi.2
  · calc
      w.atReal t = v.atReal t := congrArg (fun z : WeightedPath β E => z.atReal t) hwv
      _ = _ := by
        rw [hpath t ht]
        dsimp only [PerronIntegralODE.perronPath, PerronIntegralODE.stableIntegral,
          PerronIntegralODE.unstableIntegral]
        rw [he, ← hk true, ← hk false]
        rfl

/-- Covariance of the Perron family under every nonnegative time shift,
with parameter the actual stable projection of the shifted initial state. -/
lemma solutionFamily_shift
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (K α β δ : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hβ : 0 < β) (hβα : β < α) (hδ : 0 ≤ δ)
    (r : E → E) (hr : r 0 = 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (W : stableParameters b A → WeightedPath β E) (hW : SolutionFamily b A r K α β δ W)
    (ξ : stableParameters b A) (τ : ℝ) (hτ : 0 ≤ τ) :
    weightedShift (W ξ) τ hτ = W (stableParameterProjection b A hA ((W ξ).atReal τ)) := by
  apply (hW _).2.1
  apply perronEquation_of_ode b A hA K α β δ hK hα hd hβ hβα hδ r hr hlip
  · intro t ht
    have hh := ((hW ξ).2.2.1 (t + τ) (add_nonneg ht hτ)).scomp t
      ((hasDerivWithinAt_id t (Ici 0)).add_const τ)
      (show MapsTo (fun s : ℝ => s + τ) (Ici 0) (Ici 0) from
        fun s hs => add_nonneg hs hτ)
    simp only [one_smul] at hh
    rw [← weightedShift_atReal (W ξ) hτ ht] at hh
    exact hh.congr_of_mem (fun s hs => weightedShift_atReal (W ξ) hτ hs) ht
  · rw [weightedShift_atReal (W ξ) hτ le_rfl, zero_add]
    rfl

lemma stable_graph_forward_invariant
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (K α β δ : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hβ : 0 < β) (hβα : β < α) (hδ : 0 ≤ δ)
    (r : E → E) (hr : r 0 = 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (W : stableParameters b A → WeightedPath β E) (hW : SolutionFamily b A r K α β δ W)
    (h : stableParameters b A → unstableParameters b A)
    (hgraph : ∀ ξ, (W ξ).atReal 0 = graphMap h ξ)
    (φ : ℝ → E → E) (hφ : CompleteFlow (fun x => matrixOperatorEquiv b A x + r x) φ) :
    ∀ ξ t, 0 ≤ t → φ t (graphMap h ξ) ∈ Set.range (graphMap h) := by
  intro ξ t ht
  let η := stableParameterProjection b A hA ((W ξ).atReal t)
  refine ⟨η, ?_⟩
  rw [← hgraph ξ, flow_eq_solutionFamily b A r δ hδ hlip φ hφ K α β W hW ξ t ht]
  have hh := congrArg (fun w : WeightedPath β E => w.atReal 0)
    (solutionFamily_shift b A hA K α β δ hK hα hd hβ hβα hδ r hr hlip W hW ξ t ht)
  rw [weightedShift_atReal (W ξ) ht le_rfl, zero_add, hgraph] at hh
  exact hh.symm

/-- Apply the controlled extension to the original field in coordinates
centered at its equilibrium, retaining the actual neighborhood. -/
lemma centered_cutoff
    (b : Module.Basis n ℝ E) (U : Set E) (f : E → E) (p : E)
    (A : Matrix n n ℝ) (k : ℕ∞)
    (hU : IsOpen U) (hp : p ∈ U) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f U)
    (hfp : f p = 0) (hdf : HasFDerivAt f (matrixOperatorEquiv b A) p)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (r : E → E) (φ : ℝ → E → E),
      ContDiff ℝ k r ∧ HasCompactSupport r ∧ r 0 = 0 ∧
      HasFDerivAt r (0 : E →L[ℝ] E) 0 ∧
      (∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) ∧
      (∃ V : Set E, IsOpen V ∧ (0 : E) ∈ V ∧ (∀ x ∈ V, p + x ∈ U) ∧
        ∀ x ∈ V, matrixOperatorEquiv b A x + r x = f (p + x)) ∧
      regularDerivatives k r ∧
      CompleteFlow (fun x => matrixOperatorEquiv b A x + r x) φ := by
  let U₀ : Set E := (fun x => p + x) ⁻¹' U
  let f₀ : E → E := fun x => f (p + x)
  have hU₀ : IsOpen U₀ := hU.preimage (continuous_const.add continuous_id)
  have h0 : (0 : E) ∈ U₀ := by simpa only [U₀, mem_preimage, add_zero] using hp
  have hf₀ : ContDiffOn ℝ k f₀ U₀ :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hx => hx)
  have hf₀0 : f₀ 0 = 0 := by simpa only [f₀, add_zero] using hfp
  have hdf₀ : HasFDerivAt f₀ (matrixOperatorEquiv b A) 0 := by
    have hd : HasFDerivAt (fun x : E => p + x) (ContinuousLinearMap.id ℝ E) 0 :=
      (hasFDerivAt_id (0 : E)).const_add p
    have hdf' : HasFDerivAt f (matrixOperatorEquiv b A) (p + (0 : E)) := by
      simpa only [add_zero] using hdf
    have hh := hdf'.comp (0 : E) hd
    simpa only [add_zero, ContinuousLinearMap.comp_id, f₀, Function.comp_def] using hh
  obtain ⟨r, hrc, hrs, hr0, hdr0, hlip, ⟨V, hV, hV0, hVU, heq⟩, hj, φ, hφ⟩ :=
    Cutoff.cutoff U₀ f₀ (matrixOperatorEquiv b A) k hU₀ h0 hk hf₀ hf₀0 hdf₀ δ hδ
  exact ⟨r, φ, hrc, hrs, hr0, hdr0, hlip,
    ⟨V, hV, hV0, fun x hx => hVU hx, heq⟩,
    (fun j _ hjk => hj j hjk), hφ⟩


/-- The stable graph with all dynamical conclusions for any selected complete flow. -/
lemma stable_graph_flow_exists
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (K α β δ : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hβ : 0 < β) (hβα : β < α) (hδ : 0 ≤ δ)
    (hq : contractionRate K α β δ < 1)
    (r : E → E) (k : ℕ∞) (hr : r 0 = 0)
    (hrd : HasFDerivAt r (0 : E →L[ℝ] E) 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (hk : 1 ≤ k) (hc : ContDiff ℝ k r) (hj : regularDerivatives k r)
    (φ : ℝ → E → E) (hφ : CompleteFlow (fun x => matrixOperatorEquiv b A x + r x) φ) :
    ∃ h : stableParameters b A → unstableParameters b A,
      GraphGeometry k (stableParameters b A) (unstableParameters b A) h ∧
      (∀ ξ t, 0 ≤ t → φ t (graphMap h ξ) ∈ Set.range (graphMap h)) ∧
      (∀ ξ t, 0 ≤ t → ‖φ t (graphMap h ξ)‖ ≤
        (K / (1 - contractionRate K α β δ)) * ‖(ξ : E)‖ * Real.exp (-β * t)) := by
  obtain ⟨h, W, hgeom, _, hW, hgraph, hbound⟩ := stable_graph_geometry_exists
    b A hA K α β δ hK hα hd hβ hβα hδ hq r k hr hrd hlip hk hc hj
  refine ⟨h, hgeom,
    stable_graph_forward_invariant b A hA K α β δ hK hα hd hβ hβα hδ
      r hr hlip W hW h hgraph φ hφ, ?_⟩
  intro ξ t ht
  rw [← hgraph ξ, flow_eq_solutionFamily b A r δ hδ hlip φ hφ K α β W hW ξ t ht]
  exact hbound ξ t ht


lemma complexification_neg (A : Matrix n n ℝ) :
    complexification (-A) = -complexification A := by
  simp [complexification, Matrix.map_neg]

lemma maxGenEigenspace_neg (L : Module.End ℂ (n → ℂ)) (μ : ℂ) :
    (-L).maxGenEigenspace μ = L.maxGenEigenspace (-μ) := by
  have hneg (B : Module.End ℂ (n → ℂ)) : (-1 : ℂ) • B = -B := by
    ext x i
    simp
  apply le_antisymm
  · simpa only [hneg, neg_neg, neg_one_mul] using
      Module.End.genEigenspace_le_smul (-L) μ (-1) ⊤
  · simpa only [hneg, neg_neg, neg_one_mul] using
      Module.End.genEigenspace_le_smul L (-μ) (-1) ⊤

lemma complexSpectralSpace_neg (A : Matrix n n ℝ) (s : Bool) :
    complexSpectralSpace (-A) s = complexSpectralSpace A (!s) := by
  have hle (B : Matrix n n ℝ) (q : Bool) :
      complexSpectralSpace (-B) q ≤ complexSpectralSpace B (!q) := by
    unfold complexSpectralSpace
    refine iSup_le fun μ => ?_
    rw [complexification_neg, maxGenEigenspace_neg]
    have hm : (if !q then (-μ.val).re < 0 else 0 < (-μ.val).re) := by
      cases q <;> simpa using μ.property
    exact le_iSup_of_le (f := fun ν : {ν : ℂ // if !q then ν.re < 0 else 0 < ν.re} =>
      (complexification B).maxGenEigenspace ν.val) ⟨-μ.val, hm⟩ le_rfl
  exact le_antisymm (hle A s) (by simpa only [neg_neg, Bool.not_not] using hle (-A) (!s))

lemma realSpectralSpace_neg (A : Matrix n n ℝ) (s : Bool) :
    realSpectralSpace (-A) s = realSpectralSpace A (!s) := by
  simp only [realSpectralSpace, complexSpectralSpace_neg]

lemma hyperbolic_neg (A : Matrix n n ℝ) (hA : hyperbolicValue A) : hyperbolicValue (-A) := by
  intro μ hμ
  rw [complexification_neg, Module.End.hasEigenvalue_neg_iff] at hμ
  have hh := hA (-μ) hμ
  simpa using hh

lemma projectionValue_neg (A : Matrix n n ℝ) (s : Bool) :
    projectionValue (-A) s = projectionValue A (!s) := by
  have hs : realSpectralSpace (-A) s = realSpectralSpace A (!s) := realSpectralSpace_neg A s
  have ht : realSpectralSpace (-A) (!s) = realSpectralSpace A (!(!s)) :=
    realSpectralSpace_neg A (!s)
  by_cases h : IsCompl (realSpectralSpace (-A) s) (realSpectralSpace (-A) (!s))
  · have h' : IsCompl (realSpectralSpace A (!s)) (realSpectralSpace A (!(!s))) := by
      rw [← hs, ← ht]
      exact h
    rw [projectionValue, dite_eq_left h, projectionValue, dite_eq_left h']
    congr 1
  · have h' : ¬ IsCompl (realSpectralSpace A (!s)) (realSpectralSpace A (!(!s))) := by
      rw [← hs, ← ht]
      exact h
    rw [projectionValue, dite_eq_right h, projectionValue, dite_eq_right h']

lemma projection_neg (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (s : Bool) :
    projection b (-A) s = projection b A (!s) := by
  unfold projection Specs.D13Unified.Ch20.Dichotomy.projectionMatrix
  rw [projectionValue_neg]

lemma evolution_neg (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (t : ℝ) :
    evolution b (-A) t = evolution b A (-t) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  change matrixOperatorEquiv b (matrixExp (-A) t) = matrixOperatorEquiv b (matrixExp A (-t))
  rw [matrixOperator_exp, matrixOperator_exp]
  simp only [Algebra.algebraMap_self_apply, map_neg, smul_neg, neg_smul]

lemma dichotomyBounds_neg (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (K α : ℝ) (hd : dichotomyBounds b A K α) : dichotomyBounds b (-A) K α := by
  intro t ht
  have ho := PerronFixedPoints.operator_decay b A K α hd
  have he (t : ℝ) : Specs.D13Unified.Ch20.PerronWeightedIntegrals.evolution
      (matrixOperatorEquiv b A) t = evolution b A t := (matrixOperator_exp b A t).symm
  constructor
  · change ‖matrixOperatorEquiv b
        (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue (-A) t *
          Specs.D13Unified.Ch20.Dichotomy.projectionMatrix (-A) true)‖ ≤ _
    rw [map_mul]
    change ‖evolution b (-A) t * projection b (-A) true‖ ≤ _
    rw [evolution_neg, projection_neg, Bool.not_true, ← he]
    exact ho.2 t ht
  · change ‖matrixOperatorEquiv b
        (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue (-A) (-t) *
          Specs.D13Unified.Ch20.Dichotomy.projectionMatrix (-A) false)‖ ≤ _
    rw [map_mul]
    change ‖evolution b (-A) (-t) * projection b (-A) false‖ ≤ _
    rw [evolution_neg, projection_neg, neg_neg, Bool.not_false, ← he]
    exact ho.1 t ht

lemma stableParameters_neg (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) :
    stableParameters b (-A) = unstableParameters b A := by
  simp only [stableParameters, unstableParameters, stableSpaceValue, unstableSpaceValue,
    realSpectralSpace_neg, Bool.not_true]

lemma unstableParameters_neg (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) :
    unstableParameters b (-A) = stableParameters b A := by
  simp only [stableParameters, unstableParameters, stableSpaceValue, unstableSpaceValue,
    realSpectralSpace_neg, Bool.not_false]

lemma regularDerivatives_neg {k : ℕ∞} {r : E → E} (hj : regularDerivatives k r) :
    regularDerivatives k (-r) := by
  intro j hj1 hjk
  obtain ⟨⟨C, hC, hb⟩, hu⟩ := hj j hj1 hjk
  rw [iteratedFDeriv_neg]
  refine ⟨⟨C, hC, ?_⟩, hu.neg⟩
  intro x
  simpa only [Pi.neg_apply, norm_neg] using hb x

lemma completeFlow_reverse {v : E → E} {φ : ℝ → E → E}
    (hφ : CompleteFlow v φ) : CompleteFlow (-v) (fun t x => φ (-t) x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hφ.1.comp ((continuous_neg.comp continuous_fst).prodMk continuous_snd)
  · intro x
    simpa only [neg_zero] using hφ.2.1 x
  · intro t s x
    simpa only [neg_add] using hφ.2.2.1 (-t) (-s) x
  · intro x t
    simpa only [Function.comp_def, neg_one_smul, Pi.neg_apply] using
      (hφ.2.2.2 x (-t)).scomp t (hasDerivAt_neg t)


/-- Canonical time reversal produces the unstable graph on the original
unstable spectral subspace, with the same constants and all negative times. -/
lemma unstable_graph_exists
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : hyperbolicValue A)
    (K α β δ : ℝ) (hK : 1 ≤ K) (hα : 0 < α) (hd : dichotomyBounds b A K α)
    (hβ : 0 < β) (hβα : β < α) (hδ : 0 ≤ δ)
    (hq : contractionRate K α β δ < 1)
    (r : E → E) (k : ℕ∞) (hr : r 0 = 0)
    (hrd : HasFDerivAt r (0 : E →L[ℝ] E) 0)
    (hlip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (hk : 1 ≤ k) (hc : ContDiff ℝ k r) (hcompact : HasCompactSupport r)
    (φ : ℝ → E → E) (hφ : CompleteFlow (fun x => matrixOperatorEquiv b A x + r x) φ) :
    ∃ hu : unstableParameters b A → stableParameters b A,
      GraphGeometry k (unstableParameters b A) (stableParameters b A) hu ∧
      (∀ η t, t ≤ 0 → φ t (graphMap hu η) ∈ Set.range (graphMap hu)) ∧
      (∀ η t, t ≤ 0 → ‖φ t (graphMap hu η)‖ ≤
        (K / (1 - contractionRate K α β δ)) * ‖(η : E)‖ * Real.exp (β * t)) := by
  have hj : regularDerivatives k r := by
    intro j _ hjk
    exact Cutoff.controlled_derivatives k r hc hcompact j hjk
  have hrneg : (-r) 0 = 0 := by simp only [Pi.neg_apply, hr, neg_zero]
  have hrdneg : HasFDerivAt (-r) (0 : E →L[ℝ] E) 0 := by
    simpa only [neg_zero] using hrd.neg
  have hlipneg : ∀ x y, ‖(-r) x - (-r) y‖ ≤ δ * ‖x - y‖ := by
    intro x y
    change ‖-r x - -r y‖ ≤ _
    calc
      ‖-r x - -r y‖ = ‖-(r x - r y)‖ := congrArg norm (by abel)
      _ = ‖r x - r y‖ := norm_neg _
      _ ≤ _ := hlip x y
  have hφneg : CompleteFlow (fun x => matrixOperatorEquiv b (-A) x + (-r) x)
      (fun t x => φ (-t) x) := by
    have heq : (fun x => matrixOperatorEquiv b (-A) x + (-r) x) =
        -(fun x => matrixOperatorEquiv b A x + r x) := by
      funext x
      simp only [map_neg, neg_apply, Pi.neg_apply, neg_add]
    rw [heq]
    exact completeFlow_reverse hφ
  have hrev := stable_graph_flow_exists b (-A) (hyperbolic_neg A hA)
    K α β δ hK hα (dichotomyBounds_neg b A K α hd) hβ hβα hδ hq
    (-r) k hrneg hrdneg hlipneg hk hc.neg (regularDerivatives_neg hj)
    (fun t x => φ (-t) x) hφneg
  rw [stableParameters_neg, unstableParameters_neg] at hrev
  obtain ⟨hu, hgeom, hinv, hbound⟩ := hrev
  refine ⟨hu, hgeom, ?_, ?_⟩
  · intro η t ht
    simpa only [neg_neg] using hinv η (-t) (neg_nonneg.mpr ht)
  · intro η t ht
    simpa only [neg_neg, mul_neg, neg_mul] using hbound η (-t) (neg_nonneg.mpr ht)


/-- Stable and unstable global graphs for a controlled complete extension,
with both invariance directions and the selected sharp weighted constant. -/
theorem stable_graphs_exists : stableGraphsExpected.{u, v} := by
  intro n _ _ E _ _ _ b U f p A k hU hp hk hf hfp hdf hA
    K α β δ hK hα hd hβ hβα hδ hq
  obtain ⟨r, φ, hrc, hcompact, hr0, hdr0, hlip, hlocal, hj, hφ⟩ :=
    centered_cutoff b U f p A k hU hp hk hf hfp hdf δ hδ
  obtain ⟨hs, hsg, hsinv, hsbound⟩ := stable_graph_flow_exists
    b A hA K α β δ hK hα hd hβ hβα hδ.le hq
    r k hr0 hdr0 hlip hk hrc hj φ hφ
  obtain ⟨hu, hug, huinv, hubound⟩ := unstable_graph_exists
    b A hA K α β δ hK hα hd hβ hβα hδ.le hq
    r k hr0 hdr0 hlip hk hrc hcompact φ hφ
  exact ⟨r, φ, hs, hu, hrc, hcompact, hr0, hdr0, hlip, hlocal, hφ,
    hsg, hug, hsinv, huinv, hsbound, hubound⟩

end D13Unified.Ch20.StableGraphs
