import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.PerronFixedPoints
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.HyperbolicSplitting
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.MatrixExponential
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.PerronWeightedIntegrals
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.PerronIntegralODE

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BoundedContinuousFunction

namespace D13Unified.Ch20
namespace WeightedPath
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : ℝ}

/-- Multiplication by the positive exponential is a linear isometry onto the
ordinary bounded continuous function space. -/
def weightedIsometry (β : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    WeightedPath β E ≃ₗᵢ[ℝ] (HalfLine →ᵇ E) where
  toLinearEquiv := (coordinates β E).addEquiv.linearEquiv ℝ
  norm_map' := fun _ => rfl

omit [NormedSpace ℝ E] in
@[simp] theorem norm_weighted (w : WeightedPath β E) : ‖w.weighted‖ = ‖w‖ := rfl

@[simp] theorem eval_zero (t : HalfLine) : (0 : WeightedPath β E).eval t = 0 := by
  simp [eval, coordinates, Equiv.zero_def]

@[simp] theorem eval_add (w v : WeightedPath β E) (t : HalfLine) :
    (w + v).eval t = w.eval t + v.eval t := by
  change Real.exp (-β * (t : ℝ)) • (w.weighted t + v.weighted t) = _
  exact smul_add _ _ _

@[simp] theorem eval_sub (w v : WeightedPath β E) (t : HalfLine) :
    (w - v).eval t = w.eval t - v.eval t := by
  change Real.exp (-β * (t : ℝ)) • (w.weighted t - v.weighted t) = _
  exact smul_sub _ _ _

@[simp] theorem eval_smul (a : ℝ) (w : WeightedPath β E) (t : HalfLine) :
    (a • w).eval t = a • w.eval t := by
  change Real.exp (-β * (t : ℝ)) • (a • w.weighted t) = _
  exact smul_comm _ _ _

lemma eval_continuous (w : WeightedPath β E) : Continuous w.eval := by
  unfold eval
  fun_prop

@[simp] lemma atReal_nonneg (w : WeightedPath β E) {t : ℝ} (ht : 0 ≤ t) :
    w.atReal t = w.eval ⟨t, ht⟩ := dite_eq_left ht

@[simp] lemma atReal_add (w v : WeightedPath β E) (t : ℝ) :
    (w + v).atReal t = w.atReal t + v.atReal t := by
  unfold atReal
  split_ifs <;> simp

lemma atReal_continuousOn (w : WeightedPath β E) : ContinuousOn w.atReal (Ici 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun t : HalfLine => w.atReal t)
  have heq : (fun t : HalfLine => w.atReal t) = w.eval := by
    funext t
    exact w.atReal_nonneg t.property
  rw [heq]
  exact w.eval_continuous

/-- The weight and its reciprocal cancel exactly, including at time zero. -/
lemma weight_eval (w : WeightedPath β E) (t : HalfLine) :
    Real.exp (β * (t : ℝ)) • w.eval t = w.weighted t := by
  rw [eval, smul_smul, ← Real.exp_add]
  simp

lemma weighted_norm_eval (w : WeightedPath β E) (t : HalfLine) :
    Real.exp (β * (t : ℝ)) * ‖w.eval t‖ = ‖w.weighted t‖ := by
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    congrArg norm (weight_eval w t)

/-- The exact norm required in the paper, with a nonempty half-line domain. -/
theorem norm_eq_weighted_sup (w : WeightedPath β E) :
    ‖w‖ = ⨆ t : HalfLine, Real.exp (β * (t : ℝ)) * ‖w.eval t‖ := by
  simp_rw [weighted_norm_eval]
  exact BoundedContinuousFunction.norm_eq_iSup_norm w.weighted

lemma weighted_eval_le (w : WeightedPath β E) (t : HalfLine) :
    Real.exp (β * (t : ℝ)) * ‖w.eval t‖ ≤ ‖w‖ := by
  rw [weighted_norm_eval]
  exact w.weighted.norm_coe_le_norm t

lemma eval_norm_le (w : WeightedPath β E) (t : HalfLine) :
    ‖w.eval t‖ ≤ Real.exp (-β * (t : ℝ)) * ‖w‖ := by
  rw [eval, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (w.weighted.norm_coe_le_norm t) (Real.exp_pos _).le

/-- Evaluation controls the unweighted supremum when β is nonnegative. -/
lemma eval_norm_le_norm (hβ : 0 ≤ β) (w : WeightedPath β E) (t : HalfLine) :
    ‖w.eval t‖ ≤ ‖w‖ := by
  apply (eval_norm_le w t).trans
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) t.property)

@[ext] theorem ext {w v : WeightedPath β E} (h : ∀ t, w.eval t = v.eval t) : w = v := by
  apply (coordinates β E).injective
  apply BoundedContinuousFunction.ext
  intro t
  change w.weighted t = v.weighted t
  simpa only [weight_eval] using congrArg (fun z : E => Real.exp (β * (t : ℝ)) • z) (h t)

lemma eval_ofPath (w : HalfLine → E) (hw : Continuous w) (C : ℝ)
    (hC : ∀ t : HalfLine, Real.exp (β * (t : ℝ)) * ‖w t‖ ≤ C) :
    (ofPath β w hw C hC).eval = w := by
  funext t
  change Real.exp (-β * (t : ℝ)) • (Real.exp (β * (t : ℝ)) • w t) = w t
  rw [smul_smul, ← Real.exp_add]
  simp

instance [CompleteSpace E] : CompleteSpace (WeightedPath β E) :=
  (weightedIsometry β E).toIsometryEquiv.completeSpace

/-- Weighted pointwise norm bounds characterize the path norm. -/
lemma norm_le_iff (w : WeightedPath β E) {C : ℝ} (hC : 0 ≤ C) :
    ‖w‖ ≤ C ↔ ∀ t : HalfLine, Real.exp (β * (t : ℝ)) * ‖w.eval t‖ ≤ C := by
  simp_rw [weighted_norm_eval]
  exact BoundedContinuousFunction.norm_le hC

/-- A zero-preserving globally Lipschitz remainder acts on the whole weighted
space. No differentiability or bounded-support hypothesis is needed here. -/
def superposition (r : E → E) (δ : ℝ) (hδ : 0 ≤ δ) (hr : r 0 = 0)
    (hLip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) (w : WeightedPath β E) :
    WeightedPath β E :=
  ofPath β (fun t => r (w.eval t))
    ((LipschitzWith.of_dist_le_mul (K := NNReal.mk δ hδ) (fun x y => by
      simpa only [dist_eq_norm, NNReal.coe_mk] using hLip x y)).continuous.comp
      w.eval_continuous)
    (δ * ‖w‖) (fun t => by
      have hnorm : ‖r (w.eval t)‖ ≤ δ * ‖w.eval t‖ := by
        simpa only [hr, sub_zero] using hLip (w.eval t) 0
      calc
        Real.exp (β * (t : ℝ)) * ‖r (w.eval t)‖ ≤
            Real.exp (β * (t : ℝ)) * (δ * ‖w.eval t‖) :=
          mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
        _ = δ * (Real.exp (β * (t : ℝ)) * ‖w.eval t‖) := by ring
        _ ≤ δ * ‖w‖ := mul_le_mul_of_nonneg_left (w.weighted_eval_le t) hδ)

@[simp] lemma eval_superposition (r : E → E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hr : r 0 = 0) (hLip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (w : WeightedPath β E) (t : HalfLine) :
    (superposition r δ hδ hr hLip w).eval t = r (w.eval t) := by
  unfold superposition
  rw [eval_ofPath]

lemma superposition_zero (r : E → E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hr : r 0 = 0) (hLip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) :
    superposition (β := β) r δ hδ hr hLip 0 = 0 := by
  ext t
  simp [hr]

lemma superposition_lipschitz (r : E → E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hr : r 0 = 0) (hLip : ∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖)
    (w v : WeightedPath β E) :
    ‖superposition r δ hδ hr hLip w - superposition r δ hδ hr hLip v‖ ≤
      δ * ‖w - v‖ := by
  apply (norm_le_iff _ (mul_nonneg hδ (norm_nonneg _))).mpr
  intro t
  simp only [eval_sub, eval_superposition]
  calc
    Real.exp (β * (t : ℝ)) * ‖r (w.eval t) - r (v.eval t)‖ ≤
        Real.exp (β * (t : ℝ)) * (δ * ‖w.eval t - v.eval t‖) :=
      mul_le_mul_of_nonneg_left (hLip _ _) (Real.exp_pos _).le
    _ = δ * (Real.exp (β * (t : ℝ)) * ‖(w - v).eval t‖) := by rw [eval_sub]; ring
    _ ≤ δ * ‖w - v‖ := mul_le_mul_of_nonneg_left ((w - v).weighted_eval_le t) hδ

end WeightedPath

universe u v

/-- Exact norm and continuity bridge for the encoded path space. -/
theorem weighted_norm : Specs.D13Unified.Ch20.PerronFixedPoints.weightedNormExpected.{v} := by
  intro E _ _ β w
  exact ⟨w.eval_continuous, w.norm_eq_weighted_sup⟩

/-- Every original continuous path with finite weighted norm is encoded. -/
theorem weighted_representation :
    Specs.D13Unified.Ch20.PerronFixedPoints.weightedRepresentationExpected.{v} := by
  intro E _ _ β w hw C hC
  exact WeightedPath.eval_ofPath w hw C hC

/-- Completeness follows from the explicitly constructed onto isometry. -/
theorem weighted_complete :
    Specs.D13Unified.Ch20.PerronFixedPoints.weightedCompleteExpected.{v} := by
  intro E _ _ _ β
  infer_instance

/-- The purely Banach-space part of the Perron argument: once the integral
operator has its quantitative bound, the full affine fixed-point construction
and the factor `1 / (1-q)` follow, also when q = 0. -/
lemma affine_contraction_fixed_point {X : Type*} [NormedAddCommGroup X]
    [CompleteSpace X] (a : X) (N : X → X) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hN0 : N 0 = 0)
    (hN : ∀ x y, ‖N x - N y‖ ≤ q * ‖x - y‖) :
    ∃ w : X, w = a + N w ∧ (∀ v : X, v = a + N v → v = w) ∧
      ‖w‖ ≤ ‖a‖ / (1 - q) := by
  let F : X → X := fun w => a + N w
  have hc : ContractingWith (NNReal.mk q hq) F := by
    refine ⟨hq1, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simpa only [F, dist_eq_norm, add_sub_add_left_eq_sub, NNReal.coe_mk] using hN x y
  refine ⟨hc.fixedPoint F, hc.fixedPoint_isFixedPt.symm, ?_, ?_⟩
  · intro v hv
    exact hc.fixedPoint_unique hv.symm
  · have hbound := hc.dist_le_of_fixedPoint 0 hc.fixedPoint_isFixedPt
    simpa only [F, hN0, add_zero, dist_zero_left, NNReal.coe_mk] using hbound


namespace PerronFixedPoints
open _root_.D13Unified.Ch07
open Specs.D13Unified.Ch20.PerronFixedPoints
open Specs.D13Unified.Ch20.HyperbolicSplitting
variable {n E : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Stable membership uses the actual canonical spectral projection. -/
lemma stable_projection_eq_self (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (ξ : E) (hξ : b.equivFun ξ ∈ stableSpaceValue A) :
    projection b A true ξ = ξ := by
  apply b.equivFun.injective
  rw [projection, matrixOperator_action]
  have hmatrix :
      (Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A true).mulVec (b.equivFun ξ) =
      projectionValue A true (b.equivFun ξ) := by
    simpa only [Specs.D13Unified.Ch20.Dichotomy.projectionMatrix,
      Matrix.toLinAlgEquiv'_apply] using
      congrArg (fun f : Module.End ℝ (n → ℝ) => f (b.equivFun ξ))
        (Matrix.toLinAlgEquiv'.apply_symm_apply (projectionValue A true))
  rw [hmatrix, projection_eq A hA true]
  exact Submodule.projection_apply_of_mem_left (hyperbolic_splitting A hA) hξ

lemma evolution_continuous (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) :
    Continuous (evolution b A) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have heq (t : ℝ) : evolution b A t = NormedSpace.exp (t • matrixOperatorEquiv b A) := by
    exact matrixOperator_exp b A t
  have hf : evolution b A = fun t : ℝ => NormedSpace.exp (t • matrixOperatorEquiv b A) := funext heq
  rw [hf]
  have hexp : Continuous (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    continuous_iff_continuousAt.mpr (fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt)
  exact hexp.comp (continuous_id.smul continuous_const)

/-- Uniform weighted bound for the homogeneous stable term. -/
lemma stable_linear_bound (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (K α β : ℝ) (hD : dichotomyBounds b A K α)
    (hβ : β ≤ α) (ξ : E) (hξ : b.equivFun ξ ∈ stableSpaceValue A)
    (t : HalfLine) :
    Real.exp (β * (t : ℝ)) * ‖evolution b A t ξ‖ ≤ K * ‖ξ‖ := by
  have hproj := stable_projection_eq_self b A hA ξ hξ
  have hpoint : ‖evolution b A t ξ‖ ≤ (K * Real.exp (-α * (t : ℝ))) * ‖ξ‖ := by
    calc
      ‖evolution b A t ξ‖ =
          ‖matrixOperatorEquiv b
            (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue A t *
              Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A true) ξ‖ := by
        rw [map_mul]
        change ‖evolution b A t ξ‖ = ‖evolution b A t (projection b A true ξ)‖
        rw [hproj]
      _ ≤ _ := (matrixOperator_norm_apply b _ ξ).trans
        (mul_le_mul_of_nonneg_right (hD t t.property).1 (norm_nonneg _))
  have hscalar : Real.exp (β * (t : ℝ)) * Real.exp (-α * (t : ℝ)) ≤ 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ (t : ℝ) := t.property
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ) ht]
  have hK : 0 ≤ K := by
    have hb := (hD 0 le_rfl).1
    simp only [mul_zero, Real.exp_zero, mul_one] at hb
    exact (norm_nonneg _).trans hb
  calc
    Real.exp (β * (t : ℝ)) * ‖evolution b A t ξ‖ ≤
        Real.exp (β * (t : ℝ)) * ((K * Real.exp (-α * (t : ℝ))) * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left hpoint (Real.exp_pos _).le
    _ = (K * ‖ξ‖) * (Real.exp (β * (t : ℝ)) * Real.exp (-α * (t : ℝ))) := by ring
    _ ≤ K * ‖ξ‖ := mul_le_of_le_one_right (mul_nonneg hK (norm_nonneg _)) hscalar

/-- The homogeneous stable solution as a genuine element of the weighted space. -/
def stableLinearPath (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (K α β : ℝ) (hD : dichotomyBounds b A K α)
    (hβ : β ≤ α) (ξ : E) (hξ : b.equivFun ξ ∈ stableSpaceValue A) :
    WeightedPath β E :=
  WeightedPath.ofPath β (fun t => evolution b A t ξ)
    (by exact ((evolution_continuous b A).comp continuous_subtype_val).clm_apply continuous_const)
    (K * ‖ξ‖) (stable_linear_bound b A hA K α β hD hβ ξ hξ)

lemma stableLinearPath_norm (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) (K α β : ℝ) (hK : 0 ≤ K) (hD : dichotomyBounds b A K α)
    (hβ : β ≤ α) (ξ : E) (hξ : b.equivFun ξ ∈ stableSpaceValue A) :
    ‖stableLinearPath b A hA K α β hD hβ ξ hξ‖ ≤ K * ‖ξ‖ := by
  apply (WeightedPath.norm_le_iff _ (mul_nonneg hK (norm_nonneg _))).mpr
  intro t
  unfold stableLinearPath
  rw [WeightedPath.eval_ofPath]
  exact stable_linear_bound b A hA K α β hD hβ ξ hξ t

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The given dichotomy is exactly the operator-norm decay used by the
analytic integral estimates. -/
lemma operator_decay (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (K α : ℝ) (hD : dichotomyBounds b A K α) :
    Specs.D13Unified.Ch20.PerronWeightedIntegrals.StableDecay
      (matrixOperatorEquiv b A) (projection b A true) K α ∧
    Specs.D13Unified.Ch20.PerronWeightedIntegrals.UnstableDecay
      (matrixOperatorEquiv b A) (projection b A false) K α := by
  have he (t : ℝ) :
      Specs.D13Unified.Ch20.PerronWeightedIntegrals.evolution (matrixOperatorEquiv b A) t =
        evolution b A t := (matrixOperator_exp b A t).symm
  constructor
  · intro t ht
    rw [he]
    simpa only [matrixOperatorNorm, map_mul, projection, evolution,
      ContinuousLinearMap.mul_def] using (hD t ht).1
  · intro t ht
    rw [he]
    simpa only [matrixOperatorNorm, map_mul, projection, evolution,
      ContinuousLinearMap.mul_def] using (hD t ht).2

/-- Algebraic laws of the canonical spectral projections in the given state basis. -/
lemma operator_projection_laws (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : hyperbolicValue A) :
    projection b A true + projection b A false = 1 ∧
    projection b A true * projection b A false = 0 ∧
    Commute (projection b A true) (matrixOperatorEquiv b A) ∧
    Commute (projection b A false) (matrixOperatorEquiv b A) := by
  let e := Matrix.toLinAlgEquiv' (R := ℝ) (n := n)
  let Ps := Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A true
  let Pu := Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A false
  have hps : e Ps = projectionValue A true := e.apply_symm_apply _
  have hpu : e Pu = projectionValue A false := e.apply_symm_apply _
  have hl := spectral_projection_laws A hA
  have hsum : Ps + Pu = 1 := by
    apply e.injective
    simpa only [map_add, map_one, hps, hpu] using hl.1
  have hcross : Ps * Pu = 0 := by
    apply e.injective
    simpa only [map_mul, map_zero, hps, hpu] using hl.2.2.2.2.2.2.2.1
  have hcomm (stable : Bool) :
      Commute (Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A stable) A := by
    apply e.injective
    simpa only [map_mul, e, Specs.D13Unified.Ch20.Dichotomy.projectionMatrix,
      AlgEquiv.apply_symm_apply] using (spectral_projections_commute A hA stable).1.eq
  refine ⟨?_, ?_, (hcomm true).map (matrixOperatorEquiv b),
    (hcomm false).map (matrixOperatorEquiv b)⟩
  · change matrixOperatorEquiv b Ps + matrixOperatorEquiv b Pu = 1
    rw [← map_add, hsum, map_one]
  · change matrixOperatorEquiv b Ps * matrixOperatorEquiv b Pu = 0
    rw [← map_mul, hcross, map_zero]

namespace WeightedGreen
open Specs.D13Unified.Ch20.PerronWeightedIntegrals

omit [FiniteDimensional ℝ E] in
lemma weightedBound (β : ℝ) (w : WeightedPath β E) : WeightedBound β ‖w‖ w.atReal := by
  refine ⟨w.atReal_continuousOn, norm_nonneg _, ?_⟩
  intro s hs
  rw [w.atReal_nonneg hs]
  exact w.weighted_eval_le ⟨s, hs⟩

/-- The half-line Green operator, encoded with the original weighted norm. -/
def greenPath (L Ps Pu : E →L[ℝ] E) (K α β : ℝ)
    (hK : 1 ≤ K) (hβ : 0 < β) (hβα : β < α)
    (hs : StableDecay L Ps K α) (hu : UnstableDecay L Pu K α)
    (g : WeightedPath β E) : WeightedPath β E :=
  WeightedPath.ofPath β (fun t => greenIntegral L Ps Pu g.atReal t)
    (by
      have hc := PerronWeightedIntegrals.integral_continuity L Ps Pu K α β ‖g‖
        hK hβ hβα hs hu g.atReal (weightedBound β g)
      exact (hc.1.sub hc.2).domRestrict)
    (K * ‖g‖ * ((α - β)⁻¹ + (α + β)⁻¹))
    (fun t => PerronWeightedIntegrals.green_estimate L Ps Pu K α β ‖g‖ hK hβ hβα
      hs hu g.atReal (weightedBound β g) t t.property)

lemma greenPath_eval (L Ps Pu : E →L[ℝ] E) (K α β : ℝ)
    (hK : 1 ≤ K) (hβ : 0 < β) (hβα : β < α)
    (hs : StableDecay L Ps K α) (hu : UnstableDecay L Pu K α)
    (g : WeightedPath β E) (t : HalfLine) :
    (greenPath L Ps Pu K α β hK hβ hβα hs hu g).eval t =
      greenIntegral L Ps Pu g.atReal t := by
  unfold greenPath
  rw [WeightedPath.eval_ofPath]

lemma greenPath_norm (L Ps Pu : E →L[ℝ] E) (K α β : ℝ)
    (hK : 1 ≤ K) (hβ : 0 < β) (hβα : β < α)
    (hs : StableDecay L Ps K α) (hu : UnstableDecay L Pu K α)
    (g : WeightedPath β E) :
    ‖greenPath L Ps Pu K α β hK hβ hβα hs hu g‖ ≤
      K * ‖g‖ * ((α - β)⁻¹ + (α + β)⁻¹) := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hdiff : 0 < α - β := sub_pos.mpr hβα
  have hsum : 0 < α + β := by linarith
  apply (WeightedPath.norm_le_iff _ (by positivity)).mpr
  intro t
  rw [greenPath_eval]
  exact PerronWeightedIntegrals.green_estimate L Ps Pu K α β ‖g‖ hK hβ hβα
    hs hu g.atReal (weightedBound β g) t t.property

lemma greenPath_sub (L Ps Pu : E →L[ℝ] E) (K α β : ℝ)
    (hK : 1 ≤ K) (hβ : 0 < β) (hβα : β < α)
    (hs : StableDecay L Ps K α) (hu : UnstableDecay L Pu K α)
    (g h : WeightedPath β E) :
    greenPath L Ps Pu K α β hK hβ hβα hs hu (g - h) =
      greenPath L Ps Pu K α β hK hβ hβα hs hu g -
      greenPath L Ps Pu K α β hK hβ hβα hs hu h := by
  apply WeightedPath.ext
  intro t
  rw [WeightedPath.eval_sub, greenPath_eval, greenPath_eval, greenPath_eval]
  have heq : (g - h).atReal = fun s => (1 : ℝ) • g.atReal s + (-1 : ℝ) • h.atReal s := by
    funext s
    by_cases hs : 0 ≤ s
    · rw [WeightedPath.atReal_nonneg _ hs, WeightedPath.atReal_nonneg _ hs,
        WeightedPath.atReal_nonneg _ hs, WeightedPath.eval_sub]
      simp [sub_eq_add_neg]
    · simp [WeightedPath.atReal, hs]
  rw [heq]
  simpa only [one_smul, neg_one_smul, sub_eq_add_neg] using PerronWeightedIntegrals.integral_linearity L Ps Pu K α β hK hβ hβα hs hu
    g.atReal h.atReal ‖g‖ ‖h‖ (weightedBound β g) (weightedBound β h) 1 (-1) t t.property

lemma greenPath_atReal (L Ps Pu : E →L[ℝ] E) (K α β : ℝ)
    (hK : 1 ≤ K) (hβ : 0 < β) (hβα : β < α)
    (hs : StableDecay L Ps K α) (hu : UnstableDecay L Pu K α)
    (g : WeightedPath β E) (t : ℝ) (ht : 0 ≤ t) :
    (greenPath L Ps Pu K α β hK hβ hβα hs hu g).atReal t =
      PerronIntegralODE.stableIntegral L Ps g.atReal t -
        PerronIntegralODE.unstableIntegral L Pu g.atReal t := by
  rw [WeightedPath.atReal_nonneg _ ht, greenPath_eval, greenIntegral,
    PerronWeightedIntegrals.stable_interval_eq L Ps g.atReal t ht]
  rfl

lemma greenPath_zero (L Ps Pu : E →L[ℝ] E) (K α β : ℝ)
    (hK : 1 ≤ K) (hβ : 0 < β) (hβα : β < α)
    (hs : StableDecay L Ps K α) (hu : UnstableDecay L Pu K α) :
    greenPath L Ps Pu K α β hK hβ hβα hs hu 0 = 0 := by
  apply WeightedPath.ext
  intro t
  rw [greenPath_eval, WeightedPath.eval_zero]
  simp [greenIntegral, stableIntegral, unstableIntegral,
    Specs.D13Unified.Ch20.PerronWeightedIntegrals.kernel, WeightedPath.atReal]

lemma greenPath_lipschitz (L Ps Pu : E →L[ℝ] E) (K α β : ℝ)
    (hK : 1 ≤ K) (hβ : 0 < β) (hβα : β < α)
    (hs : StableDecay L Ps K α) (hu : UnstableDecay L Pu K α)
    (g h : WeightedPath β E) :
    ‖greenPath L Ps Pu K α β hK hβ hβα hs hu g -
        greenPath L Ps Pu K α β hK hβ hβα hs hu h‖ ≤
      (K * ((α - β)⁻¹ + (α + β)⁻¹)) * ‖g - h‖ := by
  rw [← greenPath_sub]
  convert greenPath_norm L Ps Pu K α β hK hβ hβα hs hu (g - h) using 1
  ring

end WeightedGreen

/-- The original Lyapunov--Perron theorem, including uniqueness in the whole
weighted space, its differential equation and the quantitative weighted bound. -/
theorem perron_fixed_points :
    Specs.D13Unified.Ch20.PerronFixedPoints.fixedPointsExpected := by
  intro n _ _ E _ _ _ b A hA K α β δ hK hα hD hβ hβα hδ hq1 r hr hLip ξ hξ
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L := matrixOperatorEquiv b A
  let Ps := projection b A true
  let Pu := projection b A false
  obtain ⟨hs, hu⟩ := operator_decay b A K α hD
  obtain ⟨hSum, hCross, hCommS, hCommU⟩ := operator_projection_laws b A hA
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hdiff : 0 < α - β := sub_pos.mpr hβα
  have hsum : 0 < α + β := by linarith
  have hcoef : 0 ≤ K * ((α - β)⁻¹ + (α + β)⁻¹) := by positivity
  have hq0 : 0 ≤ contractionRate K α β δ := by unfold contractionRate; positivity
  let R := WeightedPath.superposition (β := β) r δ hδ hr hLip
  let G := WeightedGreen.greenPath L Ps Pu K α β hK hβ hβα hs hu
  let N := fun v : WeightedPath β E => G (R v)
  let a := stableLinearPath b A hA K α β hD hβα.le ξ hξ
  have hR0 : R 0 = 0 := WeightedPath.superposition_zero r δ hδ hr hLip
  have hN0 : N 0 = 0 := by
    dsimp only [N]
    rw [hR0]
    exact WeightedGreen.greenPath_zero L Ps Pu K α β hK hβ hβα hs hu
  have hN : ∀ w v : WeightedPath β E,
      ‖N w - N v‖ ≤ contractionRate K α β δ * ‖w - v‖ := by
    intro w v
    calc
      ‖N w - N v‖ ≤ (K * ((α - β)⁻¹ + (α + β)⁻¹)) * ‖R w - R v‖ :=
        WeightedGreen.greenPath_lipschitz L Ps Pu K α β hK hβ hβα hs hu (R w) (R v)
      _ ≤ (K * ((α - β)⁻¹ + (α + β)⁻¹)) * (δ * ‖w - v‖) :=
        mul_le_mul_of_nonneg_left
          (WeightedPath.superposition_lipschitz r δ hδ hr hLip w v) hcoef
      _ = contractionRate K α β δ * ‖w - v‖ := by unfold contractionRate; ring
  obtain ⟨w, hw, huniq, hnorm⟩ :=
    affine_contraction_fixed_point a N (contractionRate K α β δ) hq0 hq1 hN0 hN
  have he (t : ℝ) : PerronIntegralODE.evolution L t = evolution b A t :=
    (matrixOperator_exp b A t).symm
  have hR (v : WeightedPath β E) : (R v).atReal = fun s => r (v.atReal s) := by
    funext s
    by_cases hs0 : 0 ≤ s
    · rw [WeightedPath.atReal_nonneg _ hs0, WeightedPath.atReal_nonneg _ hs0]
      exact WeightedPath.eval_superposition r δ hδ hr hLip v _
    · simp [WeightedPath.atReal, hs0, hr]
  have hpath (v : WeightedPath β E) (t : ℝ) (ht : 0 ≤ t) :
      PerronIntegralODE.perronPath L Ps Pu (R v).atReal ξ t = (a + N v).atReal t := by
    rw [WeightedPath.atReal_add]
    dsimp only [a, N, G]
    rw [WeightedPath.atReal_nonneg _ ht, stableLinearPath, WeightedPath.eval_ofPath,
      WeightedGreen.greenPath_atReal L Ps Pu K α β hK hβ hβα hs hu (R v) t ht]
    dsimp only [PerronIntegralODE.perronPath]
    rw [he]
    abel
  have hk (v : WeightedPath β E) (stable : Bool) (t : ℝ) :
      (fun s => PerronIntegralODE.evolution L (t-s)
        ((if stable then Ps else Pu) ((R v).atReal s))) =
      kernel b A r β v stable t := by
    funext s
    rw [he, hR]
    cases stable <;> rfl
  have hbridge (v : WeightedPath β E) := by
    have htail := (PerronWeightedIntegrals.unstable_estimate L Pu K α β ‖R v‖
      hK hβ hβα hu (R v).atReal (WeightedGreen.weightedBound β (R v)) 0 le_rfl).1
    have htail' : IntegrableOn
        (fun s => PerronIntegralODE.evolution L (-s) (Pu ((R v).atReal s))) (Ici 0) := by
      change IntegrableOn (fun s => PerronIntegralODE.evolution L (0-s)
        (Pu ((R v).atReal s))) (Ici 0) at htail
      simpa only [zero_sub] using htail
    exact PerronIntegralODE.perron_integral_ode L Ps Pu hSum hCross hCommS hCommU
      (R v).atReal (R v).atReal_continuousOn htail' ξ
      (stable_projection_eq_self b A hA ξ hξ)
  have hformula (v : WeightedPath β E) (t : ℝ) :
      PerronIntegralODE.perronPath L Ps Pu (R v).atReal ξ t =
        evolution b A t ξ + (∫ s in (0 : ℝ)..t, kernel b A r β v true t s) -
          ∫ s in Ici t, kernel b A r β v false t s := by
    dsimp only [PerronIntegralODE.perronPath, PerronIntegralODE.stableIntegral,
      PerronIntegralODE.unstableIntegral]
    rw [he, ← hk v true t, ← hk v false t]
    rfl
  have hiff (v : WeightedPath β E) : PerronEquation b A r β ξ v ↔ v = a + N v := by
    constructor
    · intro hv
      apply WeightedPath.ext
      intro t
      have ht := t.property
      have hpoint := (hv t ht).2.2
      rw [← hformula v t, hpath v t ht] at hpoint
      simpa only [WeightedPath.atReal_nonneg _ ht] using hpoint
    · intro hv t ht
      have hi := (hbridge v).1 t ht
      refine ⟨?_, ?_, ?_⟩
      · simpa only [← hk v true t, ↓reduceIte] using hi.1
      · simpa only [← hk v false t, Bool.false_eq_true, ↓reduceIte] using hi.2
      · rw [← hformula v t, hpath v t ht, ← hv]
  have heq (t : ℝ) (ht : 0 ≤ t) :
      w.atReal t = PerronIntegralODE.perronPath L Ps Pu (R w).atReal ξ t := by
    rw [hpath w t ht, ← hw]
  refine ⟨w, (hiff w).mpr hw, fun v hv => huniq v ((hiff v).mp hv), ?_, ?_, ?_⟩
  · intro t ht
    have hd := (hbridge w).2.2.1 t ht
    rw [← heq t ht, congrFun (hR w) t] at hd
    exact hd.congr_of_mem (fun u hu0 => heq u hu0) ht
  · rw [heq 0 le_rfl]
    exact (hbridge w).2.2.2
  · exact hnorm.trans (div_le_div_of_nonneg_right
      (stableLinearPath_norm b A hA K α β hK0 hD hβα.le ξ hξ)
      (sub_pos.mpr hq1).le)

end PerronFixedPoints

end D13Unified.Ch20
