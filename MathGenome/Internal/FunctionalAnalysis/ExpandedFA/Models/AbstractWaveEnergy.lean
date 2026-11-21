import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.AbstractWaveEnergy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-! Abstract wave evolution on arbitrary real and complex Hilbert spaces.
The graph-norm energy solutions, classical equation, kernel drift and positive-gap
unitary group are proved from the domain-carrying spectral calculi. -/
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace ExpandedFA.Models.AbstractWaveEnergy
open Unbounded
universe u

section Dual
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (S : Operator 𝕜 H H)

@[simp] theorem dualInjection_apply (h : H) (w : GraphDomain S) :
    dualInjection S h w = inner 𝕜 h (position S w) := rfl

@[simp] theorem formFunctional_apply (u w : GraphDomain S) :
    formFunctional S u w = inner 𝕜 (gradient S u) (gradient S w) := rfl

theorem dualInjection_smul (a : 𝕜) (h : H) :
    dualInjection S (a • h) = star a • dualInjection S h := by
  ext w
  simp [inner_smul_left]

theorem formFunctional_smul (a : 𝕜) (u : GraphDomain S) :
    formFunctional S (a • u) = star a • formFunctional S u := by
  ext w
  simp [inner_smul_left]

/-- Explicit real-time transport to the conjugated scalar weak equation.
No identification of scalar-linear duals with antiduals is used. -/
theorem weak_derivative_conjugate {u : ℝ → GraphDomain S} {v : ℝ → H}
    (h : ∀ (w : GraphDomain S) t,
      HasDerivAt (fun s => dualInjection S (v s) w) (-formFunctional S (u t) w) t) :
    ∀ (w : GraphDomain S) t,
      HasDerivAt (fun s => inner 𝕜 (position S w) (v s))
        (-inner 𝕜 (gradient S w) (gradient S (u t))) t := by
  intro w t
  simpa only [dualInjection_apply, formFunctional_apply, star_neg,
    ← starRingEnd_apply, map_neg, inner_conj_symm] using (h w t).star

theorem weak_derivative_conjugate_iff (u : ℝ → GraphDomain S) (v : ℝ → H) :
    (∀ (w : GraphDomain S) t,
      HasDerivAt (fun s => dualInjection S (v s) w) (-formFunctional S (u t) w) t) ↔
    (∀ (w : GraphDomain S) t,
      HasDerivAt (fun s => inner 𝕜 (position S w) (v s))
        (-inner 𝕜 (gradient S w) (gradient S (u t))) t) := by
  constructor
  · exact weak_derivative_conjugate S
  · intro h w t
    simpa only [dualInjection_apply, formFunctional_apply, star_neg,
      ← starRingEnd_apply, map_neg, inner_conj_symm] using (h w t).star

variable [NormedSpace ℝ H]

/-- The position/velocity equation gives the first scalar derivative. -/
theorem IsEnergySolution.scalar_first_derivative {u : ℝ → GraphDomain S}
    {v : ℝ → H} (h : IsEnergySolution S u v) (w : GraphDomain S) (t : ℝ) :
    HasDerivAt (fun s => dualInjection S (position S (u s)) w)
      (dualInjection S (v t) w) t := by
  simpa using (h.derivative t).inner 𝕜 (hasDerivAt_const t (position S w))


/-- The velocity field is the continuous first derivative in H. -/
theorem IsEnergySolution.contDiff_position {u : ℝ → GraphDomain S}
    {v : ℝ → H} (h : IsEnergySolution S u v) :
    ContDiff ℝ 1 (fun s => position S (u s)) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (h.derivative t).differentiableAt, ?_⟩
  have hd : deriv (fun s => position S (u s)) = v := by
    funext t
    exact (h.derivative t).deriv
  rw [hd]
  exact h.continuous_velocity

/-- The weak velocity equation is the literal scalar second derivative. -/
theorem IsEnergySolution.scalar_second_derivative {u : ℝ → GraphDomain S}
    {v : ℝ → H} (h : IsEnergySolution S u v) (w : GraphDomain S) (t : ℝ) :
    HasDerivAt (deriv (fun s => dualInjection S (position S (u s)) w))
      (-formFunctional S (u t) w) t := by
  have hd : deriv (fun s => dualInjection S (position S (u s)) w) =
      fun s => dualInjection S (v s) w := by
    funext s
    exact (IsEnergySolution.scalar_first_derivative S h w s).deriv
  rw [hd]
  exact h.weak_derivative w t

end Dual

section GraphTopology
variable {𝕜 H X : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [TopologicalSpace X] (S : Operator 𝕜 H H)

/-- The graph topology is exactly joint continuity of u and Su. -/
theorem continuous_graph_iff (u : X → GraphDomain S) :
    Continuous u ↔ Continuous (fun x => position S (u x)) ∧
      Continuous (fun x => gradient S (u x)) := by
  constructor
  · intro h
    exact ⟨(position S).continuous.comp h, (gradient S).continuous.comp h⟩
  · rintro ⟨hp, hg⟩
    rw [continuous_iff_continuousAt]
    intro x
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have h₁ := ((hp.tendsto x).sub_const (position S (u x))).norm
    have h₂ := ((hg.tendsto x).sub_const (gradient S (u x))).norm
    have heq (y : X) : ‖u y - u x‖ =
        ‖position S (u y) - position S (u x)‖ +
          ‖gradient S (u y) - gradient S (u x)‖ := by
      rw [GraphDomain.norm_eq]
      change ‖position S (u y - u x)‖ + ‖gradient S (u y - u x)‖ = _
      rw [map_sub, map_sub]
    simpa only [heq, sub_self, norm_zero, zero_add] using h₁.add h₂

end GraphTopology

section GraphCompleteness
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
/-- A graph-norm domain is continuously linearly equivalent to the graph. -/
def graphCoordinates (S : Operator 𝕜 H H) : GraphDomain S ≃L[𝕜] S.graph := by
  let e : GraphDomain S ≃ₗ[𝕜] S.graph :=
    { toFun := fun x => ⟨((GraphDomain.toDomain S x : H), S (GraphDomain.toDomain S x)),
        S.mem_graph_iff.mpr ⟨GraphDomain.toDomain S x, rfl, rfl⟩⟩
      invFun := fun x => (S.mem_graph_iff.mp x.2).choose
      left_inv := by
        intro x
        apply Subtype.ext
        exact (S.mem_graph_iff.mp (S.mem_graph_iff.mpr
          ⟨GraphDomain.toDomain S x, rfl, rfl⟩)).choose_spec.1
      right_inv := by
        intro x
        apply Subtype.ext
        exact Prod.ext (S.mem_graph_iff.mp x.2).choose_spec.1
          (S.mem_graph_iff.mp x.2).choose_spec.2
      map_add' := by intros; apply Subtype.ext; exact Prod.ext rfl (S.map_add _ _)
      map_smul' := by intros; apply Subtype.ext; exact Prod.ext rfl (S.map_smul _ _) }
  apply e.toContinuousLinearEquivOfBounds 1 2
  · intro x
    change max ‖(GraphDomain.toDomain S x : H)‖ ‖S (GraphDomain.toDomain S x)‖ ≤
      1 * (‖(GraphDomain.toDomain S x : H)‖ + ‖S (GraphDomain.toDomain S x)‖)
    rw [one_mul]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  · intro x
    have h₁ := (S.mem_graph_iff.mp x.2).choose_spec.1
    have h₂ := (S.mem_graph_iff.mp x.2).choose_spec.2
    change ‖((S.mem_graph_iff.mp x.2).choose : H)‖ +
      ‖S (S.mem_graph_iff.mp x.2).choose‖ ≤ 2 * max ‖x.val.1‖ ‖x.val.2‖
    rw [h₁, h₂]
    linarith [le_max_left ‖x.val.1‖ ‖x.val.2‖, le_max_right ‖x.val.1‖ ‖x.val.2‖]

/-- Closed operators have complete sum-graph domains. -/
theorem complete_graphDomain [CompleteSpace H] (S : Operator 𝕜 H H) (hS : S.IsClosed) :
    CompleteSpace (GraphDomain S) := by
  letI : CompleteSpace S.graph := hS.completeSpace_coe
  let e := graphCoordinates S
  let u : GraphDomain S ≃ᵤ S.graph :=
    { toEquiv := e.toEquiv
      uniformContinuous_toFun := e.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := e.symm.toContinuousLinearMap.uniformContinuous }
  exact u.completeSpace_iff.mpr inferInstance


/-- A coercive domain embedding gives an equivalent pure-energy norm. -/
theorem gradient_antilipschitz (S : Operator 𝕜 H H) (K : ℝ≥0)
    (hK : ∀ x : GraphDomain S, ‖position S x‖ ≤ K * ‖gradient S x‖) :
    AntilipschitzWith (K + 1) (gradient S) := by
  apply (gradient S).antilipschitz_of_bound
  intro x
  change ‖position S x‖ + ‖gradient S x‖ ≤ ↑(K + 1) * ‖gradient S x‖
  simp only [NNReal.coe_add, NNReal.coe_one]
  nlinarith [hK x]

/-- The S-coordinate identifies its graph domain with its closed image. -/
def gradientCoordinates (S : Operator 𝕜 H H) (K : ℝ≥0)
    (hK : ∀ x : GraphDomain S, ‖position S x‖ ≤ K * ‖gradient S x‖) :
    GraphDomain S ≃L[𝕜] (gradient S).range := by
  let e := LinearEquiv.ofInjective (gradient S).toLinearMap
    (gradient_antilipschitz S K hK).injective
  apply e.toContinuousLinearEquivOfBounds 1 (K + 1)
  · intro x
    change ‖gradient S x‖ ≤ 1 * ‖x‖
    change ‖gradient S x‖ ≤ 1 * (‖position S x‖ + ‖gradient S x‖)
    simp only [one_mul]
    exact le_add_of_nonneg_left (norm_nonneg _)
  · intro y
    have h := (gradient S).bound_of_antilipschitz
      (gradient_antilipschitz S K hK) (e.symm y)
    have he : gradient S (e.symm y) = (y : H) := by
      exact LinearEquiv.ofInjective_symm_apply (gradient S).toLinearMap y
    rw [he] at h
    exact h


/-- A concrete complete Hilbert model for the coercive energy form. -/
def energyHilbertModelOfBound {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : Operator 𝕜 H H) (hS : S.IsClosed) (K : ℝ≥0)
    (hK : ∀ x : GraphDomain S, ‖position S x‖ ≤ K * ‖gradient S x‖) :
    EnergyHilbertModel S := by
  letI : CompleteSpace (GraphDomain S) := complete_graphDomain S hS
  letI : CompleteSpace (gradient S).range :=
    (gradient_antilipschitz S K hK).completeSpace_range_clm
  let e := (gradientCoordinates S K hK).prodCongr (ContinuousLinearEquiv.refl 𝕜 H)
  let p := (WithLp.prodContinuousLinearEquiv 2 𝕜 ((gradient S).range) H).symm
  exact
    { Space := WithLp 2 ((gradient S).range × H)
      coordinates := e.trans p
      inner_eq := by
        intro x y
        rfl }


section Uniqueness
variable [CompleteSpace H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

/-- A zero-data weak energy solution vanishes, by the integrated energy identity. -/
theorem energy_solution_zero (S : Operator 𝕜 H H) (hS : S.IsClosed)
    (u : ℝ → GraphDomain S) (v : ℝ → H) (huv : IsEnergySolution S u v)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0) : u = 0 ∧ v = 0 := by
  letI : NormedSpace ℝ (GraphDomain S) := NormedSpace.restrictScalars ℝ 𝕜 _
  letI : CompleteSpace (GraphDomain S) := complete_graphDomain S hS
  let U : ℝ → GraphDomain S := fun t => ∫ s in (0 : ℝ)..t, u s
  have hU (t : ℝ) : HasDerivAt U (u t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
      (huv.continuous_graph.intervalIntegrable _ _)
    · exact huv.continuous_graph.stronglyMeasurable.stronglyMeasurableAtFilter
    · exact huv.continuous_graph.continuousAt
  have hSU (t : ℝ) : HasDerivAt (fun s => gradient S (U s)) (gradient S (u t)) t := by
    exact ((gradient S).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hU t)
  have hweak (w : GraphDomain S) (t : ℝ) :
      inner 𝕜 (v t) (position S w) + inner 𝕜 (gradient S (U t)) (gradient S w) = 0 := by
    have hd (t : ℝ) :
        HasDerivAt (fun s => inner 𝕜 (v s) (position S w) +
          inner 𝕜 (gradient S (U s)) (gradient S w)) 0 t := by
      have hv := huv.weak_derivative w t
      change HasDerivAt (fun s => inner 𝕜 (v s) (position S w))
        (-inner 𝕜 (gradient S (u t)) (gradient S w)) t at hv
      convert hv.add ((hSU t).inner 𝕜 (hasDerivAt_const t (gradient S w))) using 1 <;> simp
    have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa [U, hv0] using hc
  have henergy (t : ℝ) :
      inner 𝕜 (gradient S (U t)) (gradient S (U t)) +
        inner 𝕜 (position S (u t)) (position S (u t)) = 0 := by
    have hd (t : ℝ) : HasDerivAt (fun s =>
        inner 𝕜 (gradient S (U s)) (gradient S (U s)) +
          inner 𝕜 (position S (u s)) (position S (u s))) 0 t := by
      have hw := hweak (u t) t
      have hw' := congrArg (starRingEnd 𝕜) hw
      simp only [map_add, inner_conj_symm, map_zero] at hw'
      convert ((hSU t).inner 𝕜 (hSU t)).add
        ((huv.derivative t).inner 𝕜 (huv.derivative t)) using 1
      linear_combination -hw - hw'
    have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa [U, hu0] using hc
  have hpos (t : ℝ) : position S (u t) = 0 := by
    have h := congrArg RCLike.re (henergy t)
    simp only [map_add, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow,
      map_zero] at h
    have hnonneg := sq_nonneg ‖gradient S (U t)‖
    have hnorm := norm_nonneg (position S (u t))
    exact norm_eq_zero.mp (by nlinarith)
  have hu : u = 0 := by
    funext t
    apply Subtype.ext
    exact hpos t
  refine ⟨hu, ?_⟩
  funext t
  have hd := huv.derivative t
  simp only [hu, Pi.zero_apply, map_zero] at hd
  exact hd.unique (hasDerivAt_const t (0 : H))

/-- Weak energy solutions form a vector space; subtraction preserves the equation. -/
theorem IsEnergySolution.sub {S : Operator 𝕜 H H}
    {u z : ℝ → GraphDomain S} {v w : ℝ → H}
    (huv : IsEnergySolution S u v) (hzw : IsEnergySolution S z w) :
    IsEnergySolution S (u - z) (v - w) where
  continuous_graph := huv.continuous_graph.sub hzw.continuous_graph
  continuous_velocity := huv.continuous_velocity.sub hzw.continuous_velocity
  derivative t := by
    simpa only [Pi.sub_def, map_sub] using (huv.derivative t).sub (hzw.derivative t)
  weak_derivative a t := by
    have hd := (huv.weak_derivative a t).sub (hzw.weak_derivative a t)
    simpa only [Pi.sub_def, dualInjection, formFunctional,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_sub, inner_sub_left,
      neg_sub_neg, sub_apply, neg_apply, neg_sub] using hd

/-- Uniqueness of all weak energy solutions for given original data. -/
theorem energy_solution_unique (S : Operator 𝕜 H H) (hS : S.IsClosed)
    (u z : ℝ → GraphDomain S) (v w : ℝ → H)
    (huv : IsEnergySolution S u v) (hzw : IsEnergySolution S z w)
    (hu0 : u 0 = z 0) (hv0 : v 0 = w 0) : u = z ∧ v = w := by
  have h := energy_solution_zero S hS (u - z) (v - w) (huv.sub hzw)
    (by simp [hu0]) (by simp [hv0])
  exact ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2⟩
end Uniqueness

end GraphCompleteness

section Rotation
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The spectral rotation preserves the sum of squared norms over both fields.
Only self-adjointness, commutation and A²+B²=I enter the proof. -/
theorem rotation_energy (A B : H →L[𝕜] H)
    (hA : ContinuousLinearMap.adjoint A = A)
    (hB : ContinuousLinearMap.adjoint B = B)
    (hcomm : A * B = B * A) (hsq : A * A + B * B = 1) (x y : H) :
    ‖A x + B y‖ ^ 2 + ‖-B x + A y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have hnorm (z : H) : ‖A z‖ ^ 2 + ‖B z‖ ^ 2 = ‖z‖ ^ 2 := by
    have hz : A (A z) + B (B z) = z := by
      simpa only [_root_.add_apply, mul_apply_eq_comp,
        one_apply_eq_self] using congrArg (fun T : H →L[𝕜] H => T z) hsq
    have ha : inner 𝕜 (A z) (A z) = inner 𝕜 z (A (A z)) := by
      simpa only [hA] using (A.adjoint_inner_right z (A z)).symm
    have hb : inner 𝕜 (B z) (B z) = inner 𝕜 z (B (B z)) := by
      simpa only [hB] using (B.adjoint_inner_right z (B z)).symm
    have hinner : inner 𝕜 (A z) (A z) + inner 𝕜 (B z) (B z) = inner 𝕜 z z := by
      rw [ha, hb, ← inner_add_right, hz]
    simpa only [map_add, inner_self_eq_norm_sq] using congrArg RCLike.re hinner
  have hcross : inner 𝕜 (A x) (B y) = inner 𝕜 (B x) (A y) := by
    have hc : A (B y) = B (A y) :=
      congrArg (fun T : H →L[𝕜] H => T y) hcomm
    calc
      inner 𝕜 (A x) (B y) = inner 𝕜 x (A (B y)) := by
        simpa only [hA] using (A.adjoint_inner_right x (B y)).symm
      _ = inner 𝕜 x (B (A y)) := congrArg (inner 𝕜 x) hc
      _ = inner 𝕜 (B x) (A y) := by
        simpa only [hB] using B.adjoint_inner_right x (A y)
  have hcrossRe := congrArg RCLike.re hcross
  have hxy := hnorm x
  have hyy := hnorm y
  rw [@norm_add_sq 𝕜, @norm_add_sq 𝕜, norm_neg, inner_neg_left, map_neg]
  linarith

end Rotation

section RealFormula
open RealNonnegativeSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Bounded convergence gives strong continuity for a uniformly bounded
one-parameter family of symbols. No scalar control measure is needed. -/
theorem continuous_bounded_family (C : Calculus (H := H)) (f : ℝ → ℝ≥0 → ℝ)
    (hf : ∀ t, IsBoundedMeasurable (f t))
    (hM : ∃ M : ℝ, ∀ t s, |f t s| ≤ M)
    (ht : ∀ s, Continuous (fun t => f t s)) (x : H) :
    Continuous (fun t => C.bounded (f t) x) := by
  apply continuous_iff_seqContinuous.mpr
  intro a t ha
  apply C.strong_convergence (f t) (fun n => f (a n)) (hf t) (fun n => hf (a n))
    (by obtain ⟨M, hM⟩ := hM; exact ⟨M, fun n s => hM (a n) s⟩)
    (fun _ => Filter.Eventually.of_forall (fun s => ((ht s).tendsto t).comp ha)) x

theorem continuous_cosine_apply (C : Calculus (H := H)) (x : H) :
    Continuous (fun t => cosOperator C t x) := by
  apply continuous_bounded_family C cosine boundedMeasurable_cosine
    ⟨1, fun _ _ => Real.abs_cos_le_one _⟩
  intro s
  exact Real.continuous_cos.comp (continuous_id.mul_const (root s))

theorem continuous_sine_apply (C : Calculus (H := H)) (x : H) :
    Continuous (fun t => sinOperator C t x) := by
  apply continuous_bounded_family C sine boundedMeasurable_sine
    ⟨1, fun _ _ => Real.abs_sin_le_one _⟩
  intro s
  exact Real.continuous_sin.comp (continuous_id.mul_const (root s))

/-- The sinc extension retains t at the zero spectral mode. -/
theorem continuous_quotient_apply (C : Calculus (H := H)) (x : H) :
    Continuous (fun t => quotientOperator C t x) := by
  let f : ℝ → ℝ≥0 → ℝ := fun t s => Real.sinc (t * root s)
  have hf (t : ℝ) : IsBoundedMeasurable (f t) := by
    refine ⟨?_, 1, fun _ => Real.abs_sinc_le_one _⟩
    exact (Real.continuous_sinc.comp (continuous_const.mul continuous_root)).measurable
  have hc : Continuous (fun t => C.bounded (f t) x) := by
    apply continuous_bounded_family C f hf ⟨1, fun _ _ => Real.abs_sinc_le_one _⟩
    intro s
    exact Real.continuous_sinc.comp (continuous_id.mul_const (root s))
  have heq (t : ℝ) : quotientOperator C t x = t • C.bounded (f t) x := by
    have hsym : quotientSine t = t • f t := by
      funext s
      exact quotientSine_eq_sinc t s
    change C.bounded (quotientSine t) x = _
    rw [hsym, C.bounded_smul t (f t) (hf t)]
    rfl
  apply (continuous_id.smul hc).congr
  intro t
  exact (heq t).symm

theorem real_square_root : Spec.RealSquareRoot.{u} := by
  intro H _ _ _ C
  have h := wave_laws C (C.integral coordinate) rfl
  exact ⟨⟨C.dense root continuous_root.measurable,
      C.selfAdjoint root continuous_root.measurable, h.2.2.1⟩, h.1, h.2.1⟩

theorem real_displacement_graph : Spec.RealDisplacementGraph.{u} := by
  intro H _ _ _ C u₀ v₀ t
  have hC := C.bounded_commutes root (cosine t) continuous_root.measurable
    (boundedMeasurable_cosine t) (GraphDomain.toDomain (squareRoot C) u₀)
  have hQ := (wave_laws C (C.integral coordinate) rfl).2.2.2.2.1 t v₀
  exact (squareRoot C).graph.add_mem hC hQ

theorem real_formula_energy : Spec.RealFormulaEnergy.{u} := by
  intro H _ _ _ C u₀ v₀ t
  apply rotation_energy (cosOperator C t) (sinOperator C t)
  · exact C.bounded_adjoint _ (boundedMeasurable_cosine t)
  · exact C.bounded_adjoint _ (boundedMeasurable_sine t)
  · change C.bounded (cosine t) * C.bounded (sine t) =
      C.bounded (sine t) * C.bounded (cosine t)
    rw [← C.bounded_mul _ _ (boundedMeasurable_cosine t) (boundedMeasurable_sine t),
      ← C.bounded_mul _ _ (boundedMeasurable_sine t) (boundedMeasurable_cosine t), mul_comm]
  · have hc : IsBoundedMeasurable (cosine t * cosine t) :=
      ⟨(continuous_cosine t).measurable.mul (continuous_cosine t).measurable, 1,
        fun s => by
          rw [Pi.mul_apply, abs_mul]
          exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
            (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)⟩
    have hs : IsBoundedMeasurable (sine t * sine t) :=
      ⟨(continuous_sine t).measurable.mul (continuous_sine t).measurable, 1,
        fun s => by
          rw [Pi.mul_apply, abs_mul]
          exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
            (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)⟩
    change C.bounded (cosine t) * C.bounded (cosine t) +
      C.bounded (sine t) * C.bounded (sine t) = 1
    rw [← C.bounded_mul _ _ (boundedMeasurable_cosine t) (boundedMeasurable_cosine t),
      ← C.bounded_mul _ _ (boundedMeasurable_sine t) (boundedMeasurable_sine t),
      ← C.bounded_add _ _ hc hs]
    have heq : cosine t * cosine t + sine t * sine t = fun _ => 1 := by
      funext s
      change cosine t s * cosine t s + sine t s * sine t s = 1
      nlinarith [cosine_sq_add_sine_sq t s]
    rw [heq, C.bounded_one]

theorem real_graph_continuity : Spec.RealGraphContinuity.{u} := by
  intro H _ _ _ C u₀ v₀
  let F := realFamily C
  have hg := real_displacement_graph C u₀ v₀
  choose u hu huS using fun t => (F.S.mem_graph_iff.mp (hg t))
  let z : ℝ → GraphDomain F.S := fun t => u t
  have hp (t : ℝ) : position F.S (z t) = F.displacement u₀ v₀ t := hu t
  have hs (t : ℝ) : gradient F.S (z t) =
      F.cosine t (gradient F.S u₀) + F.sine t v₀ := huS t
  constructor
  · refine ⟨z, (continuous_graph_iff F.S z).mpr ⟨?_, ?_⟩, fun t => ⟨hp t, hs t⟩⟩
    · simp only [hp]
      exact (continuous_cosine_apply C _).add (continuous_quotient_apply C _)
    · simp only [hs]
      exact (continuous_cosine_apply C _).add (continuous_sine_apply C _)
  · exact (continuous_sine_apply C _).neg.add (continuous_cosine_apply C _)

theorem real_initial_conditions : Spec.RealInitialConditions.{u} := by
  intro H _ _ _ C u₀ v₀
  have hz : C.bounded (fun _ => 0) = 0 := by
    simpa only [zero_smul, Pi.zero_def] using C.bounded_smul 0 (fun _ => 1)
      ⟨measurable_const, 1, fun _ => by simp⟩
  have hc : cosine 0 = fun _ => 1 := by funext s; simp [cosine]
  have hs : sine 0 = fun _ => 0 := by funext s; simp [sine]
  have hq : quotientSine 0 = fun _ => 0 := by
    funext s
    rw [quotientSine_eq_sinc]
    simp
  simp only [WaveFamily.displacement, WaveFamily.velocity, realFamily,
    cosOperator, sinOperator, quotientOperator, hc, hs, hq, hz, C.bounded_one,
    one_apply_eq_self, zero_apply, neg_zero, zero_add, add_zero, and_self]

end RealFormula

/-- Nonnegative spectral support rebased to [0,∞), for the arbitrary original
complex Hilbert space. This is a construction, not an input certificate. -/
theorem complex_spectral_existence : Spec.ComplexSpectralExistence.{u} := by
  intro H _ _ _ L hL
  have hc : L.IsClosed := by
    rw [← hL.2.1]
    exact LinearPMap.adjoint_isClosed hL.1
  obtain ⟨E, hE⟩ := (UnboundedNormalSpectralTheorem.selfadjoint_spectral
    H L hL.1 hc hL.2.1).1
  obtain ⟨C, hC, _⟩ :=
    RealNonnegativeSpectralCalculus.SupportWork.realResolves_nonnegative_rebase
      L E hE hL.2.2
  exact ⟨_, C, hC⟩

section RealComposition
open RealNonnegativeSpectralCalculus
theorem cosine_add_symbol (s t : ℝ) :
    cosine (s + t) = cosine s * cosine t + (-1 : ℝ) • (sine s * sine t) := by
  funext a
  simp only [cosine, sine, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, Real.cos_add]
  ring

theorem sine_add_symbol (s t : ℝ) :
    sine (s + t) = sine s * cosine t + cosine s * sine t := by
  funext a
  simp only [sine, cosine, Pi.add_apply, Pi.mul_apply, add_mul, Real.sin_add]

theorem quotientSine_add_symbol (s t : ℝ) :
    quotientSine (s + t) = cosine s * quotientSine t + quotientSine s * cosine t := by
  funext a
  by_cases ha : a = 0
  · simp [quotientSine, ha, cosine, root]
    ring
  · simp only [quotientSine, ite_eq_right ha, Pi.add_apply, Pi.mul_apply,
      cosine, add_mul, Real.sin_add]
    ring

section RealState
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem waveBoundedMeasurable_mul {f g : ℝ≥0 → ℝ}
    (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) :
    IsBoundedMeasurable (f * g) := by
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨hf.mul hg, |a| * |b|, fun x => ?_⟩
  simp only [Pi.mul_apply, abs_mul]
  exact mul_le_mul ((ha x).trans (le_abs_self a)) ((hb x).trans (le_abs_self b))
    (abs_nonneg _) (abs_nonneg _)

theorem waveBoundedMeasurable_smul (a : ℝ) {f : ℝ≥0 → ℝ}
    (hf : IsBoundedMeasurable f) : IsBoundedMeasurable (a • f) := by
  obtain ⟨hf, M, hM⟩ := hf
  refine ⟨measurable_const.mul hf, |a| * M, fun x => ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
    mul_le_mul_of_nonneg_left (hM x) (abs_nonneg a)

theorem cosOperator_add (C : Calculus (H := H)) (s t : ℝ) :
    cosOperator C (s + t) = cosOperator C s * cosOperator C t -
      sinOperator C s * sinOperator C t := by
  change C.bounded _ = _
  rw [cosine_add_symbol, C.bounded_add _ _
    (waveBoundedMeasurable_mul (boundedMeasurable_cosine s) (boundedMeasurable_cosine t))
    (waveBoundedMeasurable_smul _ (waveBoundedMeasurable_mul (boundedMeasurable_sine s)
      (boundedMeasurable_sine t))),
    C.bounded_smul _ _ (waveBoundedMeasurable_mul (boundedMeasurable_sine s)
      (boundedMeasurable_sine t)),
    C.bounded_mul _ _ (boundedMeasurable_cosine s) (boundedMeasurable_cosine t),
    C.bounded_mul _ _ (boundedMeasurable_sine s) (boundedMeasurable_sine t)]
  simp only [neg_one_smul, sub_eq_add_neg, cosOperator, sinOperator]

theorem sinOperator_add (C : Calculus (H := H)) (s t : ℝ) :
    sinOperator C (s + t) = sinOperator C s * cosOperator C t +
      cosOperator C s * sinOperator C t := by
  change C.bounded _ = _
  rw [sine_add_symbol, C.bounded_add _ _
    (waveBoundedMeasurable_mul (boundedMeasurable_sine s) (boundedMeasurable_cosine t))
    (waveBoundedMeasurable_mul (boundedMeasurable_cosine s) (boundedMeasurable_sine t)),
    C.bounded_mul _ _ (boundedMeasurable_sine s) (boundedMeasurable_cosine t),
    C.bounded_mul _ _ (boundedMeasurable_cosine s) (boundedMeasurable_sine t)]
  rfl

theorem quotientOperator_add (C : Calculus (H := H)) (s t : ℝ) :
    quotientOperator C (s + t) = cosOperator C s * quotientOperator C t +
      quotientOperator C s * cosOperator C t := by
  change C.bounded _ = _
  rw [quotientSine_add_symbol, C.bounded_add _ _
    (waveBoundedMeasurable_mul (boundedMeasurable_cosine s) (boundedMeasurable_quotientSine t))
    (waveBoundedMeasurable_mul (boundedMeasurable_quotientSine s) (boundedMeasurable_cosine t)),
    C.bounded_mul _ _ (boundedMeasurable_cosine s) (boundedMeasurable_quotientSine t),
    C.bounded_mul _ _ (boundedMeasurable_quotientSine s) (boundedMeasurable_cosine t)]
  rfl

theorem bounded_apply_comm (C : Calculus (H := H)) {f g : ℝ≥0 → ℝ}
    (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) (x : H) :
    C.bounded f (C.bounded g x) = C.bounded g (C.bounded f x) := by
  have he : C.bounded f * C.bounded g = C.bounded g * C.bounded f := by
    rw [← C.bounded_mul f g hf hg, ← C.bounded_mul g f hg hf, mul_comm]
  exact congrArg (fun T : H →L[ℝ] H => T x) he

theorem quotient_gradient (C : Calculus (H := H)) (t : ℝ)
    (u : GraphDomain (realFamily C).S) :
    quotientOperator C t (gradient (realFamily C).S u) =
      sinOperator C t (position (realFamily C).S u) := by
  have h₁ := C.bounded_commutes root (quotientSine t) continuous_root.measurable
    (boundedMeasurable_quotientSine t) (GraphDomain.toDomain (squareRoot C) u)
  have h₂ := (wave_laws C (C.integral coordinate) rfl).2.2.2.2.1 t
    (position (realFamily C).S u)
  exact (squareRoot C).mem_graph_snd_inj h₁ h₂ rfl

theorem real_state_composition_formula (C : Calculus (H := H))
    (u₀ : GraphDomain (realFamily C).S) (v₀ : H) (s t : ℝ)
    (z : GraphDomain (realFamily C).S)
    (hz : position (realFamily C).S z = (realFamily C).displacement u₀ v₀ t)
    (hSz : gradient (realFamily C).S z =
      cosOperator C t (gradient (realFamily C).S u₀) + sinOperator C t v₀) :
    (realFamily C).displacement z ((realFamily C).velocity u₀ v₀ t) s =
      (realFamily C).displacement u₀ v₀ (s + t) ∧
    (realFamily C).velocity z ((realFamily C).velocity u₀ v₀ t) s =
      (realFamily C).velocity u₀ v₀ (s + t) := by
  have hQ : quotientOperator C s (sinOperator C t (gradient (realFamily C).S u₀)) =
      sinOperator C s (sinOperator C t (position (realFamily C).S u₀)) := by
    change C.bounded (quotientSine s) (C.bounded (sine t) _) = _
    rw [bounded_apply_comm C (boundedMeasurable_quotientSine s) (boundedMeasurable_sine t)]
    change sinOperator C t (quotientOperator C s (gradient (realFamily C).S u₀)) = _
    rw [quotient_gradient]
    exact bounded_apply_comm C (boundedMeasurable_sine t) (boundedMeasurable_sine s) _
  constructor
  · change cosOperator C s (position (realFamily C).S z) +
      quotientOperator C s (-sinOperator C t (gradient (realFamily C).S u₀) +
        cosOperator C t v₀) = _
    rw [hz]
    change cosOperator C s (cosOperator C t (position (realFamily C).S u₀) +
      quotientOperator C t v₀) + quotientOperator C s
      (-sinOperator C t (gradient (realFamily C).S u₀) + cosOperator C t v₀) =
      cosOperator C (s + t) (position (realFamily C).S u₀) + quotientOperator C (s + t) v₀
    rw [cosOperator_add, quotientOperator_add]
    simp only [map_add, map_neg, _root_.sub_apply,
      _root_.add_apply, mul_apply_eq_comp, hQ]
    abel
  · change -sinOperator C s (gradient (realFamily C).S z) +
      cosOperator C s (-sinOperator C t (gradient (realFamily C).S u₀) +
        cosOperator C t v₀) =
      -sinOperator C (s + t) (gradient (realFamily C).S u₀) + cosOperator C (s + t) v₀
    rw [hSz, cosOperator_add, sinOperator_add]
    simp only [map_add, map_neg, _root_.sub_apply,
      _root_.add_apply, mul_apply_eq_comp]
    abel

end RealState
end RealComposition

section
open RealNonnegativeSpectralCalculus
section ComplexFormula
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H}

private theorem measurable_wave_complexSymbol {f : ℝ≥0 → ℝ} (hf : Measurable f) :
    Measurable (complexSymbol f) := Complex.measurable_ofReal.comp hf
private theorem boundedMeasurable_wave_complexSymbol {f : ℝ≥0 → ℝ}
    (hf : IsBoundedMeasurable f) :
    SpectralMeasure.Spec.IsBoundedMeasurable (complexSymbol f) := by
  refine ⟨measurable_wave_complexSymbol hf.1, hf.2.choose, fun s => ?_⟩
  simpa only [complexSymbol, Complex.norm_real, Real.norm_eq_abs] using hf.2.choose_spec s
private theorem wave_complexSymbol_mul (f g : ℝ≥0 → ℝ) :
    complexSymbol (f * g) = complexSymbol f * complexSymbol g := by
  ext; simp [complexSymbol]
private theorem wave_complexSymbol_star (f : ℝ≥0 → ℝ) :
    star (complexSymbol f) = complexSymbol f := by
  ext; simp [complexSymbol]

/-- Strong continuity for uniformly bounded, pointwise continuous complex symbols. -/
theorem continuous_complex_bounded_family
    (C : MeasurableSpectralCalculus.BoundedRealization E) (f : ℝ → ℝ≥0 → ℂ)
    (hf : ∀ t, SpectralMeasure.Spec.IsBoundedMeasurable (f t))
    (hM : ∃ M : ℝ, ∀ t s, ‖f t s‖ ≤ M)
    (ht : ∀ s, Continuous (fun t => f t s)) (x : H) :
    Continuous (fun t => C.integral (f t) x) := by
  apply continuous_iff_seqContinuous.mpr
  intro a t ha
  apply UnboundedNormalSpectralTheorem.SpectralRepresentation.strong_convergence C
    (f t) (fun n => f (a n)) (hf t) (fun n => hf (a n))
    (by obtain ⟨M, hM⟩ := hM; exact ⟨M, fun n s => hM (a n) s⟩)
    (fun s => ((ht s).tendsto t).comp ha) x

theorem continuous_complex_cosine_apply
    (C : MeasurableSpectralCalculus.BoundedRealization E) (x : H) :
    Continuous (fun t => (complexFamily C).cosine t x) := by
  apply continuous_complex_bounded_family C
    (fun t => complexSymbol (cosine t))
    (fun t => boundedMeasurable_wave_complexSymbol (boundedMeasurable_cosine t))
    ⟨1, fun _ _ => by simpa only [complexSymbol, Complex.norm_real, Real.norm_eq_abs, cosine]
      using Real.abs_cos_le_one _⟩
  intro s
  exact Complex.continuous_ofReal.comp
    (Real.continuous_cos.comp (continuous_id.mul_const (root s)))

theorem continuous_complex_sine_apply
    (C : MeasurableSpectralCalculus.BoundedRealization E) (x : H) :
    Continuous (fun t => (complexFamily C).sine t x) := by
  apply continuous_complex_bounded_family C
    (fun t => complexSymbol (sine t))
    (fun t => boundedMeasurable_wave_complexSymbol (boundedMeasurable_sine t))
    ⟨1, fun _ _ => by simpa only [complexSymbol, Complex.norm_real, Real.norm_eq_abs, sine]
      using Real.abs_sin_le_one _⟩
  intro s
  exact Complex.continuous_ofReal.comp
    (Real.continuous_sin.comp (continuous_id.mul_const (root s)))

theorem continuous_complex_quotient_apply
    (C : MeasurableSpectralCalculus.BoundedRealization E) (x : H) :
    Continuous (fun t => (complexFamily C).quotient t x) := by
  let f : ℝ → ℝ≥0 → ℝ := fun t s => Real.sinc (t * root s)
  have hf (t : ℝ) : IsBoundedMeasurable (f t) := by
    refine ⟨?_, 1, fun _ => Real.abs_sinc_le_one _⟩
    exact (Real.continuous_sinc.comp (continuous_const.mul continuous_root)).measurable
  have hc : Continuous (fun t => C.integral (complexSymbol (f t)) x) := by
    apply continuous_complex_bounded_family C
      (fun t => complexSymbol (f t)) (fun t => boundedMeasurable_wave_complexSymbol (hf t))
      ⟨1, fun _ _ => by simpa only [complexSymbol, Complex.norm_real, Real.norm_eq_abs]
        using Real.abs_sinc_le_one _⟩
    intro s
    exact Complex.continuous_ofReal.comp
      (Real.continuous_sinc.comp (continuous_id.mul_const (root s)))
  have heq (t : ℝ) : (complexFamily C).quotient t x =
      (t : ℂ) • C.integral (complexSymbol (f t)) x := by
    have hsym : complexSymbol (quotientSine t) = (t : ℂ) • complexSymbol (f t) := by
      funext s
      simp only [complexSymbol, Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul]
      exact congrArg Complex.ofReal (quotientSine_eq_sinc t s)
    change C.integral (complexSymbol (quotientSine t)) x = _
    rw [hsym, C.smul (t : ℂ) (complexSymbol (f t)) (boundedMeasurable_wave_complexSymbol (hf t))]
    rfl
  apply (Complex.continuous_ofReal.smul hc).congr
  intro t
  exact (heq t).symm

theorem complex_displacement_graph
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (u₀ : GraphDomain (complexFamily C).S) (v₀ : H) (t : ℝ) :
    ((complexFamily C).displacement u₀ v₀ t,
      (complexFamily C).cosine t (gradient (complexFamily C).S u₀) +
        (complexFamily C).sine t v₀) ∈ (complexFamily C).S.graph := by
  have hC := UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_commutes C
    (measurable_wave_complexSymbol continuous_root.measurable)
    (boundedMeasurable_wave_complexSymbol (boundedMeasurable_cosine t))
    (GraphDomain.toDomain (complexFamily C).S u₀)
  have hprod : complexSymbol root * complexSymbol (quotientSine t) = complexSymbol (sine t) := by
    rw [← wave_complexSymbol_mul, root_mul_quotientSine]
  have hQ := UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_product_graph C
    (measurable_wave_complexSymbol continuous_root.measurable)
    (boundedMeasurable_wave_complexSymbol (boundedMeasurable_quotientSine t))
    (hprod ▸ boundedMeasurable_wave_complexSymbol (boundedMeasurable_sine t)) v₀
  rw [hprod] at hQ
  exact (complexFamily C).S.graph.add_mem hC hQ

theorem complex_formula_energy
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (u₀ : GraphDomain (complexFamily C).S) (v₀ : H) (t : ℝ) :
    ‖(complexFamily C).cosine t (gradient (complexFamily C).S u₀) +
      (complexFamily C).sine t v₀‖ ^ 2 + ‖(complexFamily C).velocity u₀ v₀ t‖ ^ 2 =
      energy (complexFamily C).S u₀ v₀ := by
  apply rotation_energy ((complexFamily C).cosine t) ((complexFamily C).sine t)
  · change ContinuousLinearMap.adjoint (C.integral (complexSymbol (cosine t))) = _
    rw [← ContinuousLinearMap.star_eq_adjoint,
      ← C.map_star _ (boundedMeasurable_wave_complexSymbol (boundedMeasurable_cosine t)),
      wave_complexSymbol_star]
    rfl
  · change ContinuousLinearMap.adjoint (C.integral (complexSymbol (sine t))) = _
    rw [← ContinuousLinearMap.star_eq_adjoint,
      ← C.map_star _ (boundedMeasurable_wave_complexSymbol (boundedMeasurable_sine t)),
      wave_complexSymbol_star]
    rfl
  · change C.integral (complexSymbol (cosine t)) * C.integral (complexSymbol (sine t)) =
      C.integral (complexSymbol (sine t)) * C.integral (complexSymbol (cosine t))
    rw [← C.mul _ _ (boundedMeasurable_wave_complexSymbol (boundedMeasurable_cosine t))
        (boundedMeasurable_wave_complexSymbol (boundedMeasurable_sine t)),
      ← C.mul _ _ (boundedMeasurable_wave_complexSymbol (boundedMeasurable_sine t))
        (boundedMeasurable_wave_complexSymbol (boundedMeasurable_cosine t)), mul_comm]
  · let c := complexSymbol (cosine t)
    let s := complexSymbol (sine t)
    have hc : SpectralMeasure.Spec.IsBoundedMeasurable c :=
      boundedMeasurable_wave_complexSymbol (boundedMeasurable_cosine t)
    have hs : SpectralMeasure.Spec.IsBoundedMeasurable s :=
      boundedMeasurable_wave_complexSymbol (boundedMeasurable_sine t)
    change C.integral c * C.integral c + C.integral s * C.integral s = 1
    rw [← C.mul _ _ hc hc, ← C.mul _ _ hs hs, ← C.add _ _ (hc.mul hc) (hs.mul hs)]
    have heq : c * c + s * s = fun _ => 1 := by
      funext a
      change (cosine t a : ℂ) * (cosine t a : ℂ) +
        (sine t a : ℂ) * (sine t a : ℂ) = 1
      have hreal : cosine t a * cosine t a + sine t a * sine t a = 1 := by
        nlinarith [cosine_sq_add_sine_sq t a]
      exact_mod_cast hreal
    rw [heq, C.one]

theorem complex_graph_continuity
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (u₀ : GraphDomain (complexFamily C).S) (v₀ : H) :
    (∃ u : ℝ → GraphDomain (complexFamily C).S,
      Continuous u ∧ ∀ t,
        position (complexFamily C).S (u t) = (complexFamily C).displacement u₀ v₀ t ∧
        gradient (complexFamily C).S (u t) =
          (complexFamily C).cosine t (gradient (complexFamily C).S u₀) +
            (complexFamily C).sine t v₀) ∧
    Continuous ((complexFamily C).velocity u₀ v₀) := by
  let F := complexFamily C
  have hg := complex_displacement_graph C u₀ v₀
  choose u hu huS using fun t => (F.S.mem_graph_iff.mp (hg t))
  let z : ℝ → GraphDomain F.S := fun t => u t
  have hp (t : ℝ) : position F.S (z t) = F.displacement u₀ v₀ t := hu t
  have hs (t : ℝ) : gradient F.S (z t) =
      F.cosine t (gradient F.S u₀) + F.sine t v₀ := huS t
  constructor
  · refine ⟨z, (continuous_graph_iff F.S z).mpr ⟨?_, ?_⟩, fun t => ⟨hp t, hs t⟩⟩
    · simp only [hp]
      exact (continuous_complex_cosine_apply C _).add (continuous_complex_quotient_apply C _)
    · simp only [hs]
      exact (continuous_complex_cosine_apply C _).add (continuous_complex_sine_apply C _)
  · exact (continuous_complex_sine_apply C _).neg.add (continuous_complex_cosine_apply C _)

theorem complex_initial_conditions
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (u₀ : GraphDomain (complexFamily C).S) (v₀ : H) :
    (complexFamily C).displacement u₀ v₀ 0 = position (complexFamily C).S u₀ ∧
      (complexFamily C).velocity u₀ v₀ 0 = v₀ := by
  have hz : C.integral (fun _ => 0) = 0 := by
    simpa only [zero_smul, Pi.zero_def] using C.smul 0 (fun _ => 1)
      ⟨measurable_const, 1, fun _ => by simp⟩
  have hc : complexSymbol (cosine 0) = fun _ => 1 := by funext s; simp [complexSymbol, cosine]
  have hs : complexSymbol (sine 0) = fun _ => 0 := by funext s; simp [complexSymbol, sine]
  have hq : complexSymbol (quotientSine 0) = fun _ => 0 := by
    funext s
    simp [complexSymbol, quotientSine]
  simp [WaveFamily.displacement, WaveFamily.velocity, complexFamily, hc, hs, hq, C.one, hz]

/-- The complex square root squares to the coordinate integral on its exact domain. -/
theorem complex_square_root_square
    (C : MeasurableSpectralCalculus.BoundedRealization E) :
    OperatorDomainsSpec.productValue (complexFamily C).S (complexFamily C).S =
      MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate) := by
  have hroot : complexSymbol root * complexSymbol root = complexSymbol coordinate := by
    rw [← wave_complexSymbol_mul, root_mul_root]
  have hdom : (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)).domain ≤
      (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol root)).domain := by
    apply ComplexCalculus.domain_growth C
      (measurable_wave_complexSymbol continuous_root.measurable)
      (measurable_wave_complexSymbol continuous_coordinate.measurable)
    refine ⟨1, 1, zero_le_one, zero_le_one, fun s => ?_⟩
    simp only [complexSymbol, Complex.norm_real, Real.norm_eq_abs, sq_abs, root_sq]
    nlinarith [sq_nonneg (coordinate s - 1 / 2)]
  have hprod := SpectralProductAndSumDomains.product_rule C (complexSymbol root) (complexSymbol root)
    (measurable_wave_complexSymbol continuous_root.measurable)
    (measurable_wave_complexSymbol continuous_root.measurable)
  apply LinearPMap.eq_of_le_of_domain_eq
  · simpa only [complexFamily, hroot] using hprod.2
  · simpa only [complexFamily, hroot, inf_eq_right.mpr hdom] using hprod.1

/-- The complex spectral square root is densely defined, self-adjoint and nonnegative,
with the exact square and kernel of the coordinate integral. -/
theorem complex_square_root
    (C : MeasurableSpectralCalculus.BoundedRealization E) :
    IsNonnegativeSquareRoot
      (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate))
      (complexFamily C).S := by
  have hf := measurable_wave_complexSymbol continuous_root.measurable
  have hd := MeasurableSpectralCalculus.measurableIntegral_dense C hf
  have hsa := MeasurableSpectralCalculus.measurableIntegral_selfAdjoint C hf
    (fun _ => Complex.ofReal_im _)
  refine ⟨⟨hd, hsa, ?_⟩, complex_square_root_square C, ?_⟩
  · intro x
    exact PositivityWork.measurableIntegral_nonnegative C hf
      (fun _ => Complex.ofReal_im _) (fun s => Real.sqrt_nonneg _) x
  · let S := (complexFamily C).S
    have hs : S.IsFormalAdjoint S := by
      have h := LinearPMap.adjoint_isFormalAdjoint hd
      rw [hsa] at h
      exact h
    rw [← complex_square_root_square C]
    change S.ker = (OperatorDomainsSpec.productValue S S).ker
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hz⟩ := (mem_kernel_iff S x).mp hx
      have hSx : S ⟨x, hx⟩ ∈ S.domain := by rw [hz]; exact S.domain.zero_mem
      apply (mem_kernel_iff (OperatorDomainsSpec.productValue S S) x).mpr
      refine ⟨⟨hx, hSx⟩, ?_⟩
      rw [product_apply S S ⟨x, hx⟩ hSx]
      simp only [hz]
      change S (0 : S.domain) = 0
      exact S.map_zero
    · intro hx
      obtain ⟨hx, hz⟩ := (mem_kernel_iff (OperatorDomainsSpec.productValue S S) x).mp hx
      obtain ⟨hxd, hSd⟩ := (mem_product_domain_iff S S x).mp hx
      have hh := hs ⟨x, hxd⟩ ⟨S ⟨x, hxd⟩, hSd⟩
      have hSS : S ⟨S ⟨x, hxd⟩, hSd⟩ = 0 := by
        rw [← product_apply S S ⟨x, hxd⟩ hSd]
        exact hz
      rw [hSS, inner_zero_right] at hh
      exact (mem_kernel_iff S x).mpr ⟨hxd, inner_self_eq_zero.mp hh⟩
end ComplexFormula
end

section
open RealNonnegativeSpectralCalculus
lemma scalar_quotient_deriv (t : ℝ) (s : ℝ≥0) :
    HasDerivAt (fun t => quotientSine t s) (cosine t s) t := by
  by_cases hs : s = 0
  · convert (hasDerivAt_id t) using 1 <;> simp [quotientSine, hs, cosine, root] <;> rfl
  have hr : root s ≠ 0 := by
    simpa [root, Real.sqrt_eq_zero s.2] using hs
  have hd := (((hasDerivAt_id t).mul_const (root s)).sin).div_const (root s)
  simpa [quotientSine, hs, cosine, hr] using hd

lemma abs_slope_quotient_le (t r : ℝ) (s : ℝ≥0) :
    |slope (fun z => quotientSine z s) t r| ≤ 1 := by
  by_cases hr : r = t
  · simp [slope, hr]
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => quotientSine z s) (f' := fun z => cosine z s)
    (s := Set.univ) (C := 1)
    (fun z _ => (scalar_quotient_deriv z s).hasDerivWithinAt)
    (fun z _ => Real.abs_cos_le_one (z * root s)) convex_univ
    (Set.mem_univ t) (Set.mem_univ r)
  rw [slope, smul_eq_mul, abs_mul, abs_inv]
  rw [inv_mul_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hr))]
  simpa only [Real.norm_eq_abs, one_mul, mul_one, vsub_eq_sub] using hb

lemma scalar_cosine_deriv (t : ℝ) (s : ℝ≥0) :
    HasDerivAt (fun t => cosine t s) (-sine t s * root s) t := by
  simpa [cosine, sine] using (((hasDerivAt_id t).mul_const (root s)).cos)

lemma scalar_sine_deriv (t : ℝ) (s : ℝ≥0) :
    HasDerivAt (fun t => sine t s) (cosine t s * root s) t := by
  simpa [cosine, sine] using (((hasDerivAt_id t).mul_const (root s)).sin)

lemma abs_slope_cosine_le (t r : ℝ) (s : ℝ≥0) :
    |slope (fun z => cosine z s) t r| ≤ root s := by
  by_cases hr : r = t
  · simp [slope, hr, root, Real.sqrt_nonneg]
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => cosine z s) (f' := fun z => -sine z s * root s)
    (s := Set.univ) (C := root s)
    (fun z _ => (scalar_cosine_deriv z s).hasDerivWithinAt)
    (fun z _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (show 0 ≤ root s from Real.sqrt_nonneg _)]
      exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (Real.sqrt_nonneg _)).trans_eq (one_mul _))
    convex_univ (Set.mem_univ t) (Set.mem_univ r)
  rw [slope, smul_eq_mul, abs_mul, abs_inv]
  rw [inv_mul_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hr))]
  simpa only [Real.norm_eq_abs, vsub_eq_sub, mul_comm] using hb

lemma abs_slope_sine_le (t r : ℝ) (s : ℝ≥0) :
    |slope (fun z => sine z s) t r| ≤ root s := by
  by_cases hr : r = t
  · simp [slope, hr, root, Real.sqrt_nonneg]
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => sine z s) (f' := fun z => cosine z s * root s)
    (s := Set.univ) (C := root s)
    (fun z _ => (scalar_sine_deriv z s).hasDerivWithinAt)
    (fun z _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ root s from Real.sqrt_nonneg _)]
      exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (Real.sqrt_nonneg _)).trans_eq (one_mul _))
    convex_univ (Set.mem_univ t) (Set.mem_univ r)
  rw [slope, smul_eq_mul, abs_mul, abs_inv]
  rw [inv_mul_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hr))]
  simpa only [Real.norm_eq_abs, vsub_eq_sub, mul_comm] using hb

section RealDerivative
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma boundedMeasurable_sub {f g : ℝ≥0 → ℝ}
    (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) :
    IsBoundedMeasurable (f - g) := by
  rcases hf with ⟨hf, M, hM⟩
  rcases hg with ⟨hg, N, hN⟩
  exact ⟨hf.sub hg, M+N, fun s => (abs_sub _ _).trans (add_le_add (hM s) (hN s))⟩

lemma boundedMeasurable_smul (a : ℝ) {f : ℝ≥0 → ℝ}
    (hf : IsBoundedMeasurable f) : IsBoundedMeasurable (a • f) := by
  rcases hf with ⟨hf, M, hM⟩
  exact ⟨measurable_const.mul hf, |a| * M, fun s => by
    simpa [abs_mul] using mul_le_mul_of_nonneg_left (hM s) (abs_nonneg a)⟩

lemma bounded_sub (C : Calculus (H := H)) {f g : ℝ≥0 → ℝ}
    (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) :
    C.bounded (f-g) = C.bounded f - C.bounded g := by
  have he : f-g = f + (-1:ℝ) • g := by ext s; simp [sub_eq_add_neg]
  rw [he, C.bounded_add _ _ hf (boundedMeasurable_smul _ hg), C.bounded_smul _ _ hg]
  simp [sub_eq_add_neg]

lemma hasDerivAt_bounded_family (C : Calculus (H := H))
    (f : ℝ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ) (t : ℝ)
    (hf : ∀ r, IsBoundedMeasurable (f r)) (hg : IsBoundedMeasurable g)
    (hd : ∀ s, HasDerivAt (fun r => f r s) (g s) t)
    (hM : ∃ M : ℝ, ∀ r s, |slope (fun z => f z s) t r| ≤ M)
    (x : H) : HasDerivAt (fun r => C.bounded (f r) x) (C.bounded g x) t := by
  rw [hasDerivAt_iff_tendsto_slope, Filter.tendsto_iff_seq_tendsto]
  intro a ha
  let k : ℕ → ℝ≥0 → ℝ := fun n s => slope (fun r => f r s) t (a n)
  have hk (n) : IsBoundedMeasurable (k n) := by
    change IsBoundedMeasurable (((a n-t)⁻¹) • (f (a n)-f t))
    exact boundedMeasurable_smul _ (boundedMeasurable_sub (hf _) (hf _))
  have hlim := C.strong_convergence g k hg hk
    (by obtain ⟨M,hM⟩ := hM; exact ⟨M,fun n s => hM (a n) s⟩)
    (fun _ => Eventually.of_forall (fun s => (hd s).tendsto_slope.comp ha)) x
  convert hlim using 1
  funext n
  change (a n-t)⁻¹ • (C.bounded (f (a n)) x - C.bounded (f t) x) = _
  change _ = C.bounded (((a n-t)⁻¹) • (f (a n)-f t)) x
  rw [C.bounded_smul _ _ (boundedMeasurable_sub (hf _) (hf _)), bounded_sub C (hf _) (hf _)]
  rfl
lemma hasDerivAt_quotient_apply (C : Calculus (H := H)) (x : H) (t : ℝ) :
    HasDerivAt (fun r => quotientOperator C r x) (cosOperator C t x) t := by
  exact hasDerivAt_bounded_family C quotientSine (cosine t) t
    boundedMeasurable_quotientSine (boundedMeasurable_cosine t)
    (scalar_quotient_deriv t) ⟨1, abs_slope_quotient_le t⟩ x

private def rootSlope (f : ℝ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ) (t r : ℝ)
    (s : ℝ≥0) : ℝ :=
  if root s = 0 then g s else slope (fun z => f z s) t r / root s

lemma hasDerivAt_root_bounded_family (C : Calculus (H := H))
    (f : ℝ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ) (t : ℝ)
    (hf : ∀ r, IsBoundedMeasurable (f r)) (hg : IsBoundedMeasurable g)
    (hg1 : ∀ s, |g s| ≤ 1)
    (hd : ∀ s, HasDerivAt (fun r => f r s) (g s * root s) t)
    (hM : ∀ r s, |slope (fun z => f z s) t r| ≤ root s)
    (x : (squareRoot C).domain) :
    HasDerivAt (fun r => C.bounded (f r) x) (C.bounded g (squareRoot C x)) t := by
  let k := rootSlope f g t
  have hkb (r : ℝ) (s : ℝ≥0) : |k r s| ≤ 1 := by
    dsimp [k, rootSlope]
    split_ifs with hs
    · exact hg1 s
    · rw [abs_div, abs_of_nonneg (show 0 ≤ root s from Real.sqrt_nonneg _)]
      exact (div_le_one (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs))).mpr (hM r s)
  have hk (r : ℝ) : IsBoundedMeasurable (k r) := by
    refine ⟨?_, 1, hkb r⟩
    exact Measurable.ite (measurableSet_eq_fun continuous_root.measurable measurable_const)
      hg.1 ((measurable_const.mul ((hf r).1.sub (hf t).1)).div continuous_root.measurable)
  have hkr (r : ℝ) : root * k r = (r-t)⁻¹ • (f r-f t) := by
    funext s
    change root s * k r s = slope (fun z => f z s) t r
    dsimp [k, rootSlope]
    split_ifs with hs
    · rw [hs, zero_mul]
      have hh : |slope (fun z => f z s) t r| = 0 := by
        exact le_antisymm (hs ▸ hM r s) (abs_nonneg _)
      exact (abs_eq_zero.mp hh).symm
    · exact mul_div_cancel₀ _ hs
  rw [hasDerivAt_iff_tendsto_slope, Filter.tendsto_iff_seq_tendsto]
  intro a ha
  have hpoint (s : ℝ≥0) : Tendsto (fun n => k (a n) s) atTop (𝓝 (g s)) := by
    dsimp [k, rootSlope]
    split_ifs with hs
    · exact tendsto_const_nhds
    · convert ((hd s).tendsto_slope.comp ha).div_const (root s) using 1 <;> first | rfl | rw [mul_div_cancel_right₀ _ hs]
  have hlim := C.strong_convergence g (fun n => k (a n)) hg
    (fun n => hk (a n)) ⟨1, fun n s => hkb (a n) s⟩
    (fun _ => Eventually.of_forall hpoint) (squareRoot C x)
  convert hlim using 1
  funext n
  have hleft := bounded_product_graph C continuous_root.measurable (hk (a n))
    (by rw [hkr]; exact boundedMeasurable_smul _ (boundedMeasurable_sub (hf _) (hf _))) (x:H)
  have hright := C.bounded_commutes root (k (a n)) continuous_root.measurable (hk (a n)) x
  have he := (C.integral root).mem_graph_snd_inj hleft hright rfl
  rw [hkr, C.bounded_smul _ _ (boundedMeasurable_sub (hf _) (hf _)),
    bounded_sub C (hf _) (hf _)] at he
  exact he

lemma hasDerivAt_cosine_apply (C : Calculus (H := H))
    (x : (squareRoot C).domain) (t : ℝ) :
    HasDerivAt (fun r => cosOperator C r x) (-sinOperator C t (squareRoot C x)) t := by
  have hg : IsBoundedMeasurable (-sine t) := by
    simpa only [neg_one_smul] using boundedMeasurable_smul (-1) (boundedMeasurable_sine t)
  have hh := hasDerivAt_root_bounded_family C cosine (-sine t) t
    boundedMeasurable_cosine hg
    (fun s => by simpa only [Pi.neg_apply, abs_neg, sine] using Real.abs_sin_le_one (t * root s))
    (scalar_cosine_deriv t) (abs_slope_cosine_le t) x
  have he : C.bounded (-sine t) = -C.bounded (sine t) := by
    rw [show -sine t = (-1:ℝ) • sine t by ext s; simp,
      C.bounded_smul _ _ (boundedMeasurable_sine t)]
    simp
  simpa only [cosOperator, sinOperator, he, ContinuousLinearMap.neg_apply] using hh

lemma hasDerivAt_sine_apply (C : Calculus (H := H))
    (x : (squareRoot C).domain) (t : ℝ) :
    HasDerivAt (fun r => sinOperator C r x) (cosOperator C t (squareRoot C x)) t := by
  exact hasDerivAt_root_bounded_family C sine (cosine t) t
    boundedMeasurable_sine (boundedMeasurable_cosine t)
    (fun s => Real.abs_cos_le_one _) (scalar_sine_deriv t) (abs_slope_sine_le t) x

lemma hasDerivAt_real_displacement (C : Calculus (H := H))
    (u₀ : GraphDomain (realFamily C).S) (v₀ : H) (t : ℝ) :
    HasDerivAt ((realFamily C).displacement u₀ v₀)
      ((realFamily C).velocity u₀ v₀ t) t := by
  exact (hasDerivAt_cosine_apply C (GraphDomain.toDomain (squareRoot C) u₀) t).add
    (hasDerivAt_quotient_apply C v₀ t)

lemma inner_cosine_apply (C : Calculus (H := H)) (t : ℝ) (x y : H) :
    inner ℝ (cosOperator C t x) y = inner ℝ x (cosOperator C t y) := by
  have h := (cosOperator C t).adjoint_inner_right x y
  rw [show ContinuousLinearMap.adjoint (cosOperator C t) = cosOperator C t from
    C.bounded_adjoint _ (boundedMeasurable_cosine t)] at h
  exact h.symm

lemma inner_sine_apply (C : Calculus (H := H)) (t : ℝ) (x y : H) :
    inner ℝ (sinOperator C t x) y = inner ℝ x (sinOperator C t y) := by
  have h := (sinOperator C t).adjoint_inner_right x y
  rw [show ContinuousLinearMap.adjoint (sinOperator C t) = sinOperator C t from
    C.bounded_adjoint _ (boundedMeasurable_sine t)] at h
  exact h.symm

lemma hasDerivAt_real_velocity_weak (C : Calculus (H := H))
    (u₀ w : GraphDomain (realFamily C).S) (v₀ : H) (t : ℝ) :
    HasDerivAt (fun r => dualInjection (realFamily C).S ((realFamily C).velocity u₀ v₀ r) w)
      (-inner ℝ
        (cosOperator C t (gradient (realFamily C).S u₀) + sinOperator C t v₀)
        (gradient (realFamily C).S w)) t := by
  let x : (squareRoot C).domain := GraphDomain.toDomain (squareRoot C) w
  let a := gradient (realFamily C).S u₀
  have hs := (hasDerivAt_const t a).inner ℝ (hasDerivAt_sine_apply C x t)
  have hc := (hasDerivAt_const t v₀).inner ℝ (hasDerivAt_cosine_apply C x t)
  have he : (fun r => dualInjection (realFamily C).S ((realFamily C).velocity u₀ v₀ r) w) =
      (fun r => -inner ℝ a (sinOperator C r x) + inner ℝ v₀ (cosOperator C r x)) := by
    funext r
    change inner ℝ (-sinOperator C r a + cosOperator C r v₀) (x:H) = _
    rw [inner_add_left, inner_neg_left, inner_sine_apply, inner_cosine_apply]
  rw [he]
  convert hs.neg.add hc using 1
  change -(inner ℝ (cosOperator C t a + sinOperator C t v₀) (squareRoot C x)) = _
  simp only [inner_zero_left, zero_add, inner_neg_right, inner_add_left,
    inner_cosine_apply, inner_sine_apply, neg_add_rev, add_comm]


end RealDerivative
end

section
open MeasureTheory RealNonnegativeSpectralCalculus
section ComplexKernel
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H}

/-- The spectral atom at zero is the orthogonal projection onto the actual
kernel of the maximal coordinate integral. -/
theorem complex_kernel_projection
    (C : MeasurableSpectralCalculus.BoundedRealization E) :
    IsKernelProjection
      (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate))
      (E {0}) := by
  let B : Set ℝ≥0 := {0}
  have hB : MeasurableSet B := measurableSet_singleton 0
  have hf : Measurable (complexSymbol coordinate) :=
    Complex.measurable_ofReal.comp continuous_coordinate.measurable
  have hz : C.integral (fun _ => 0) = 0 := by
    simpa only [zero_smul, Pi.zero_def] using C.smul 0 (fun _ => 1)
      ⟨measurable_const, 1, fun _ => by simp⟩
  refine ⟨?_, ?_, E.inner_left B hB⟩
  · intro x
    have hzero : B.indicator (complexSymbol coordinate) = fun _ => 0 := by
      classical
      funext s
      by_cases hs : s = 0
      · subst s
        simp [B, complexSymbol, coordinate]
      · simp [B, hs]
    have h := UnboundedNormalSpectralTheorem.SpectralRepresentation.localized_graph C hf hB
      (M := 0) (by intro s hs; have hs' : s = 0 := hs; subst s; simp [complexSymbol, coordinate]) x
    rw [hzero, hz] at h
    obtain ⟨hx, hxval⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp h
    exact (mem_kernel_iff _ _).mpr ⟨hx, hxval⟩
  · intro x
    obtain ⟨hx, hLx⟩ := (mem_kernel_iff _ _).mp x.2
    have hl := MeasurableSpectralCalculus.unbounded_lintegral_norm_sq C hf ⟨(x : H), hx⟩
    rw [hLx, norm_zero, zero_pow (by decide), ENNReal.ofReal_zero] at hl
    have hae := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp (hf.norm.pow_const 2))).mp hl
    have hsupport : ∀ᵐ s ∂C.measure (x : H), s = 0 := by
      filter_upwards [hae] with s hs
      have hs' : ‖complexSymbol coordinate s‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hs
      have hn : ‖complexSymbol coordinate s‖ = 0 := by
        nlinarith [norm_nonneg (complexSymbol coordinate s)]
      have hc := norm_eq_zero.mp hn
      exact NNReal.coe_eq_zero.mp (Complex.ofReal_eq_zero.mp hc)
    have hind : SpectralMeasure.Spec.IsBoundedMeasurable (B.indicator (fun _ : ℝ≥0 => (1 : ℂ))) :=
      SpectralMeasure.BorelNormSpectrum.bounded_indicator B hB
        (SpectralMeasure.BorelNormSpectrum.bounded_const 1)
    calc
      E {0} x = C.integral (B.indicator (fun _ => 1)) x := by
        rw [UnboundedNormalSpectralTheorem.SpectralRepresentation.integral_indicator_one C B hB]
      _ = C.integral (fun _ => 1) x := by
        apply C.integral_apply_congr_ae _ _ hind
          (SpectralMeasure.BorelNormSpectrum.bounded_const 1)
        filter_upwards [hsupport] with s hs
        simp [B, hs]
      _ = (x : H) := by rw [C.one]; rfl

/-- A bounded multiplier acts on the zero spectral component by its value at zero. -/
theorem complex_zero_mode_apply
    (C : MeasurableSpectralCalculus.BoundedRealization E) (f : ℝ≥0 → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (x : H) :
    E {0} (C.integral f x) = f 0 • E {0} x := by
  let B : Set ℝ≥0 := {0}
  have hB : MeasurableSet B := measurableSet_singleton 0
  let p : ℝ≥0 → ℂ := B.indicator (fun _ => 1)
  have hp : SpectralMeasure.Spec.IsBoundedMeasurable p :=
    SpectralMeasure.BorelNormSpectrum.bounded_indicator B hB
      (SpectralMeasure.BorelNormSpectrum.bounded_const 1)
  have heq : p * f = f 0 • p := by
    classical
    funext s
    by_cases hs : s = 0
    · subst s; simp [p, B]
    · simp [p, B, hs]
  have hP : C.integral p = E {0} :=
    UnboundedNormalSpectralTheorem.SpectralRepresentation.integral_indicator_one C B hB
  rw [← hP]
  change (C.integral p * C.integral f) x = _
  rw [← C.mul _ _ hp hf, heq, C.smul _ _ hp]
  rfl

/-- Exact drift of the zero spectral modes, including nonzero kernel velocities. -/
theorem complex_kernel_drift
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (u₀ : GraphDomain (complexFamily C).S) (v₀ : H) (t : ℝ) :
    E {0} ((complexFamily C).displacement u₀ v₀ t) =
      E {0} (position (complexFamily C).S u₀) + t • E {0} v₀ := by
  have hc : SpectralMeasure.Spec.IsBoundedMeasurable (complexSymbol (cosine t)) :=
    boundedMeasurable_complexSymbol (boundedMeasurable_cosine t)
  have hq : SpectralMeasure.Spec.IsBoundedMeasurable (complexSymbol (quotientSine t)) :=
    boundedMeasurable_complexSymbol (boundedMeasurable_quotientSine t)
  change E {0} (C.integral (complexSymbol (cosine t)) (position (complexFamily C).S u₀) +
      C.integral (complexSymbol (quotientSine t)) v₀) = _
  rw [map_add, complex_zero_mode_apply C _ hc, complex_zero_mode_apply C _ hq]
  simp only [complexSymbol, cosine, root_zero, mul_zero, Real.cos_zero, Complex.ofReal_one,
    one_smul, quotientSine_zero]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

end ComplexKernel
end

section
open RealNonnegativeSpectralCalculus
open scoped ContDiff
section RealDerivative
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma real_solution_claims (C : Calculus (H := H)) : SolutionClaims (realFamily C) := by
  intro u₀ v₀
  obtain ⟨⟨u, huc, hu⟩, hvc⟩ := real_graph_continuity C u₀ v₀
  have huv : IsEnergySolution (realFamily C).S u ((realFamily C).velocity u₀ v₀) := by
    refine ⟨huc, hvc, ?_, ?_⟩
    · intro t
      convert hasDerivAt_real_displacement C u₀ v₀ t using 1
      funext r
      exact (hu r).1
    · intro w t
      change HasDerivAt _ (-inner ℝ (gradient (realFamily C).S (u t)) (gradient (realFamily C).S w)) t
      rw [(hu t).2]
      exact hasDerivAt_real_velocity_weak C u₀ w v₀ t
  have h0 : u 0 = u₀ := by
    apply Subtype.ext
    change position (realFamily C).S (u 0) = position (realFamily C).S u₀
    rw [(hu 0).1]
    exact (real_initial_conditions C u₀ v₀).1
  have hv0 := (real_initial_conditions C u₀ v₀).2
  refine ⟨u, fun t => (hu t).1, huv, h0, hv0, ?_, ?_⟩
  · intro z w hzw hz0 hw0
    exact energy_solution_unique (realFamily C).S (C.closed root continuous_root.measurable)
      z u w ((realFamily C).velocity u₀ v₀) hzw huv (hz0.trans h0.symm) (hw0.trans hv0.symm)
  · intro t
    unfold energy
    rw [(hu t).2]
    exact real_formula_energy C u₀ v₀ t

lemma real_classical_claims (C : Calculus (H := H)) :
    ClassicalClaims (C.integral coordinate) (realFamily C) := by
  intro u₀ v₀ hu₀ hv₀
  let S := squareRoot C
  let x : S.domain := GraphDomain.toDomain S u₀
  have hx : (x:H) ∈ (OperatorDomainsSpec.productValue S S).domain := by
    rw [squareRoot_square C]
    exact hu₀
  have hSx : S x ∈ S.domain := (mem_product_domain_iff S S (x:H)).mp hx |>.2
  let y : S.domain := ⟨S x, hSx⟩
  let z : S.domain := ⟨v₀, hv₀⟩
  let a : ℝ → H := fun t => cosOperator C t (S y) + sinOperator C t (S z)
  have hd (t : ℝ) : HasDerivAt ((realFamily C).velocity u₀ v₀) (-a t) t := by
    have hh := (hasDerivAt_sine_apply C y t).neg.add (hasDerivAt_cosine_apply C z t)
    change HasDerivAt (fun r => -sinOperator C r (S x) + cosOperator C r v₀)
      (-(cosOperator C t (S y) + sinOperator C t (S z))) t
    convert hh using 1 <;> simp only [Pi.add_apply, Pi.neg_apply, y, z, neg_add, S] <;> rfl
  have hc : Continuous a := (continuous_cosine_apply C _).add (continuous_sine_apply C _)
  have hvderiv : deriv ((realFamily C).velocity u₀ v₀) = -a := by
    funext t
    exact (hd t).deriv
  have hvelocity : ContDiff ℝ 1 ((realFamily C).velocity u₀ v₀) := by
    rw [contDiff_one_iff_deriv, hvderiv]
    exact ⟨fun t => (hd t).differentiableAt, hc.neg⟩
  have hudiff := hasDerivAt_real_displacement C u₀ v₀
  have hud : deriv ((realFamily C).displacement u₀ v₀) = (realFamily C).velocity u₀ v₀ := by
    funext t
    exact (hudiff t).deriv
  constructor
  · rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv, hud]
    exact ⟨fun t => (hudiff t).differentiableAt, by simp, hvelocity⟩
  · intro t
    have hu := real_displacement_graph C u₀ v₀ t
    have hSu := S.graph.add_mem
      (C.bounded_commutes root (cosine t) continuous_root.measurable (boundedMeasurable_cosine t) y)
      (C.bounded_commutes root (sine t) continuous_root.measurable (boundedMeasurable_sine t) z)
    obtain ⟨b, hb, hbS⟩ := S.mem_graph_iff.mp hu
    change (b:H) = (realFamily C).displacement u₀ v₀ t at hb
    change S b = cosOperator C t (S x) + sinOperator C t v₀ at hbS
    obtain ⟨c, hc0, hcS⟩ := S.mem_graph_iff.mp hSu
    change (c:H) = cosOperator C t (S x) + sinOperator C t v₀ at hc0
    change S c = a t at hcS
    have hSb : S b ∈ S.domain := by
      rw [hbS, ← hc0]
      exact c.property
    have hdom : (realFamily C).displacement u₀ v₀ t ∈ (C.integral coordinate).domain := by
      rw [← squareRoot_square C]
      apply (mem_product_domain_iff S S _).mpr
      rw [← hb]
      exact ⟨b.property, hSb⟩
    refine ⟨hdom, ?_⟩
    have he : C.integral coordinate ⟨(realFamily C).displacement u₀ v₀ t, hdom⟩ = a t := by
      have hgraph : ((realFamily C).displacement u₀ v₀ t, a t) ∈
          (OperatorDomainsSpec.productValue S S).graph := by
        apply (OperatorDomainsSpec.productValue S S).mem_graph_iff.mpr
        refine ⟨⟨(b:H), ⟨b.property, hSb⟩⟩, hb, ?_⟩
        rw [product_apply S S b hSb]
        have hbc : (⟨S b, hSb⟩ : S.domain) = c := by
          apply Subtype.ext
          exact hbS.trans hc0.symm
        rw [hbc]
        exact hcS
      rw [squareRoot_square C] at hgraph
      obtain ⟨d, hd0, hd1⟩ := (C.integral coordinate).mem_graph_iff.mp hgraph
      change (d:H) = (realFamily C).displacement u₀ v₀ t at hd0
      have hde : (⟨(realFamily C).displacement u₀ v₀ t, hdom⟩ : (C.integral coordinate).domain) = d :=
        Subtype.ext hd0.symm
      rw [hde]
      exact hd1
    rw [he]
    exact hd t

end RealDerivative
end

section
open MeasureTheory RealNonnegativeSpectralCalculus
section RealKernel
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem real_bounded_norm_sq (C : Calculus (H := H))
    (f : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) (x : H) :
    ‖C.bounded f x‖ ^ 2 = ∫ s, |f s| ^ 2 ∂C.measure x := by
  have hdom : x ∈ (C.integral f).domain := by
    rw [C.bounded_agrees f hf]
    exact Submodule.mem_top
  have heval : C.integral f ⟨x, hdom⟩ = C.bounded f x :=
    (LinearPMap.ext_iff.mp (C.bounded_agrees f hf)).2 (hg := Submodule.mem_top)
  rw [← heval]
  exact C.norm_sq f hf.1 ⟨x, hdom⟩

private theorem real_bounded_congr_ae (C : Calculus (H := H))
    (f g : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g)
    (x : H) (heq : f =ᵐ[C.measure x] g) : C.bounded f x = C.bounded g x := by
  have hng : IsBoundedMeasurable (-g) := by
    refine ⟨hg.1.neg, hg.2.choose, fun s => ?_⟩
    simpa only [Pi.neg_apply, abs_neg] using hg.2.choose_spec s
  have hfg : IsBoundedMeasurable (f + -g) := by
    refine ⟨hf.1.add hng.1, hf.2.choose + hng.2.choose, fun s => ?_⟩
    exact (abs_add_le _ _).trans (add_le_add (hf.2.choose_spec s) (hng.2.choose_spec s))
  have hneg : C.bounded (-g) = -C.bounded g := by
    simpa only [neg_one_smul] using C.bounded_smul (-1) g hg
  have hn : ‖C.bounded f x - C.bounded g x‖ ^ 2 = 0 := by
    rw [← sub_apply, sub_eq_add_neg, ← hneg, ← C.bounded_add _ _ hf hng,
      real_bounded_norm_sq C _ hfg x]
    calc
      _ = ∫ _, (0 : ℝ) ∂C.measure x := integral_congr_ae (by
        filter_upwards [heq] with s hs
        simp [hs])
      _ = 0 := by simp
  have hz : ‖C.bounded f x - C.bounded g x‖ = 0 := by
    nlinarith [norm_nonneg (C.bounded f x - C.bounded g x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

private theorem real_bounded_indicator_mem (B : Set ℝ≥0) (hB : MeasurableSet B) :
    IsBoundedMeasurable (B.indicator (fun _ : ℝ≥0 => (1 : ℝ))) := by
  refine ⟨measurable_const.indicator hB, 1, fun s => ?_⟩
  classical
  by_cases hs : s ∈ B <;> simp [hs]

/-- The real spectral atom at zero is exactly the projection onto the coordinate
integral's kernel. The kernel support argument uses genuine integrability. -/
theorem real_kernel_projection (C : Calculus (H := H)) :
    IsKernelProjection (C.integral coordinate) (C.E {0}) := by
  let B : Set ℝ≥0 := {0}
  have hB : MeasurableSet B := measurableSet_singleton 0
  let p : ℝ≥0 → ℝ := B.indicator (fun _ => 1)
  have hp : IsBoundedMeasurable p := real_bounded_indicator_mem B hB
  have hz : C.bounded (fun _ => 0) = 0 := by
    simpa only [zero_smul, Pi.zero_def] using C.bounded_smul 0 (fun _ => 1)
      ⟨measurable_const, 1, fun _ => by simp⟩
  have hP : C.bounded p = C.E {0} := C.bounded_indicator B hB
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hzero : coordinate * p = fun _ => 0 := by
      classical
      funext s
      by_cases hs : s = 0
      · subst s; simp [p, B, coordinate]
      · simp [p, B, hs]
    have hprod : IsBoundedMeasurable (coordinate * p) := by
      rw [hzero]
      exact ⟨measurable_const, 0, fun _ => by simp⟩
    have h := RealNonnegativeSpectralCalculus.bounded_product_graph C
      continuous_coordinate.measurable hp hprod x
    rw [hP, hzero, hz] at h
    obtain ⟨hx, hxval⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp h
    exact (mem_kernel_iff _ _).mpr ⟨hx, hxval⟩
  · intro x
    obtain ⟨hx, hLx⟩ := (mem_kernel_iff _ _).mp x.2
    have hfinite := (C.domain coordinate continuous_coordinate.measurable (x : H)).mp hx
    have hi : Integrable (fun s => |coordinate s| ^ 2) (C.measure (x : H)) := by
      refine ⟨(continuous_coordinate.measurable.norm.pow_const 2).aestronglyMeasurable, ?_⟩
      exact (hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall fun s => sq_nonneg |coordinate s|)).mpr hfinite
    have hnorm := C.norm_sq coordinate continuous_coordinate.measurable ⟨(x : H), hx⟩
    rw [hLx, norm_zero, zero_pow (by decide)] at hnorm
    have hl : (∫⁻ s, ENNReal.ofReal (|coordinate s| ^ 2) ∂C.measure (x : H)) = 0 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun s => sq_nonneg |coordinate s|), ← hnorm]
      exact ENNReal.ofReal_zero
    have hae := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp
      (continuous_coordinate.measurable.norm.pow_const 2))).mp hl
    have hsupport : ∀ᵐ s ∂C.measure (x : H), s = 0 := by
      filter_upwards [hae] with s hs
      have hs' : |coordinate s| ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hs
      apply NNReal.coe_eq_zero.mp
      change coordinate s = 0
      rw [sq_abs] at hs'
      nlinarith [sq_nonneg (coordinate s)]
    calc
      C.E {0} x = C.bounded p x := by rw [hP]
      _ = C.bounded (fun _ => 1) x := by
        apply real_bounded_congr_ae C _ _ hp ⟨measurable_const, 1, fun _ => by simp⟩
        filter_upwards [hsupport] with s hs
        simp [p, B, hs]
      _ = (x : H) := by rw [C.bounded_one]; rfl
  · exact (C.E.selfAdjoint B hB).isSymmetric

/-- A bounded real multiplier acts on the zero spectral mode by its zero value. -/
theorem real_zero_mode_apply (C : Calculus (H := H)) (f : ℝ≥0 → ℝ)
    (hf : IsBoundedMeasurable f) (x : H) :
    C.E {0} (C.bounded f x) = f 0 • C.E {0} x := by
  let B : Set ℝ≥0 := {0}
  have hB : MeasurableSet B := measurableSet_singleton 0
  let p : ℝ≥0 → ℝ := B.indicator (fun _ => 1)
  have hp : IsBoundedMeasurable p := real_bounded_indicator_mem B hB
  have heq : p * f = f 0 • p := by
    classical
    funext s
    by_cases hs : s = 0
    · subst s; simp [p, B]
    · simp [p, B, hs]
  have hP : C.bounded p = C.E {0} := C.bounded_indicator B hB
  rw [← hP]
  change (C.bounded p * C.bounded f) x = _
  rw [← C.bounded_mul _ _ hp hf, heq, C.bounded_smul _ _ hp]
  rfl

/-- The actual real spectral formula retains kernel velocities as linear drift. -/
theorem real_kernel_drift (C : Calculus (H := H))
    (u₀ : GraphDomain (realFamily C).S) (v₀ : H) (t : ℝ) :
    C.E {0} ((realFamily C).displacement u₀ v₀ t) =
      C.E {0} (position (realFamily C).S u₀) + t • C.E {0} v₀ := by
  change C.E {0} (C.bounded (cosine t) (position (realFamily C).S u₀) +
      C.bounded (quotientSine t) v₀) = _
  rw [map_add, real_zero_mode_apply C _ (boundedMeasurable_cosine t),
    real_zero_mode_apply C _ (boundedMeasurable_quotientSine t)]
  simp only [cosine, root_zero, mul_zero, Real.cos_zero, one_smul, quotientSine_zero]

end RealKernel
end

section
open RealNonnegativeSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- Bounded spectral cutoffs increasing to the identity. -/
def realSpectralCutoff (n : ℕ) : ℝ≥0 → ℝ :=
  {s | coordinate s ≤ (n : ℝ)}.indicator (fun _ => 1)

lemma boundedMeasurable_realSpectralCutoff (n : ℕ) :
    IsBoundedMeasurable (realSpectralCutoff n) := by
  have hm : MeasurableSet {s : ℝ≥0 | coordinate s ≤ (n : ℝ)} :=
    measurableSet_le continuous_coordinate.measurable measurable_const
  refine ⟨measurable_const.indicator hm, 1, ?_⟩
  intro s
  by_cases hs : coordinate s ≤ (n : ℝ) <;> simp [realSpectralCutoff, hs]

lemma boundedMeasurable_coordinate_cutoff (n : ℕ) :
    IsBoundedMeasurable (coordinate * realSpectralCutoff n) := by
  refine ⟨continuous_coordinate.measurable.mul (boundedMeasurable_realSpectralCutoff n).1,
    n, ?_⟩
  intro s
  by_cases hs : coordinate s ≤ (n : ℝ)
  · simpa [realSpectralCutoff, hs, abs_of_nonneg (show 0 ≤ coordinate s from s.2)] using hs
  · simp [realSpectralCutoff, hs]

lemma realSpectralCutoff_tendsto (s : ℝ≥0) :
    Tendsto (fun n => realSpectralCutoff n s) atTop (𝓝 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (coordinate s)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  have hs : coordinate s ≤ (m : ℝ) := hn.le.trans (by exact_mod_cast hm)
  simp [realSpectralCutoff, hs]

lemma realSpectralCutoff_strong (C : Calculus (H := H)) (x : H) :
    Tendsto (fun n => C.bounded (realSpectralCutoff n) x) atTop (𝓝 x) := by
  have h := C.strong_convergence (fun _ => 1) realSpectralCutoff
    ⟨measurable_const, 1, fun s => by norm_num⟩ boundedMeasurable_realSpectralCutoff
    ⟨1, fun n s => by
      by_cases hs : coordinate s ≤ (n : ℝ) <;> simp [realSpectralCutoff, hs]⟩
    (fun x => Filter.Eventually.of_forall realSpectralCutoff_tendsto) x
  simpa [C.bounded_one] using h

/-- The original gap inequality on D(L) extends to the full form domain. -/
theorem real_root_gap (C : Calculus (H := H)) (c : ℝ)
    (hgap : ∀ x : (C.integral coordinate).domain,
      c * ‖(x : H)‖ ^ 2 ≤ inner ℝ (x : H) (C.integral coordinate x))
    (u : GraphDomain (squareRoot C)) :
    c * ‖position (squareRoot C) u‖ ^ 2 ≤ ‖gradient (squareRoot C) u‖ ^ 2 := by
  let S := squareRoot C
  let p (n : ℕ) := C.bounded (realSpectralCutoff n)
  have hs : S.IsFormalAdjoint S := by
    have h := LinearPMap.adjoint_isFormalAdjoint (C.dense root continuous_root.measurable)
    rw [C.selfAdjoint root continuous_root.measurable] at h
    exact h
  have hbound (n : ℕ) :
      c * ‖p n (position S u)‖ ^ 2 ≤ ‖p n (gradient S u)‖ ^ 2 := by
    have hL := bounded_product_graph C continuous_coordinate.measurable
      (boundedMeasurable_realSpectralCutoff n) (boundedMeasurable_coordinate_cutoff n)
      (position S u)
    obtain ⟨x, hx, hy⟩ := (C.integral coordinate).mem_graph_iff.mp hL
    dsimp only at hx hy
    have hxL := hgap x
    have hS : (p n (position S u), p n (gradient S u)) ∈ S.graph :=
      C.bounded_commutes root (realSpectralCutoff n) continuous_root.measurable
        (boundedMeasurable_realSpectralCutoff n) (GraphDomain.toDomain S u)
    obtain ⟨y, hy₁, hy₂⟩ := S.mem_graph_iff.mp hS
    dsimp only at hy₁ hy₂
    have hprod : (p n (position S u), C.integral coordinate x) ∈
        (OperatorDomainsSpec.productValue S S).graph := by
      rw [show OperatorDomainsSpec.productValue S S = _ from squareRoot_square C]
      exact (C.integral coordinate).mem_graph_iff.mpr ⟨x, hx, rfl⟩
    obtain ⟨z, hz₁, hz₂⟩ := (OperatorDomainsSpec.productValue S S).mem_graph_iff.mp hprod
    dsimp only at hz₁ hz₂
    have hzd := z.2.choose
    have hSzd := z.2.choose_spec
    have hzz : (⟨(z : H), hzd⟩ : S.domain) = y := Subtype.ext (hz₁.trans hy₁.symm)
    have hsym := hs y ⟨S ⟨z, hzd⟩, hSzd⟩
    have he : inner ℝ (x : H) (C.integral coordinate x) = ‖p n (gradient S u)‖ ^ 2 := by
      rw [← hz₂]
      change inner ℝ (x : H) (S ⟨S ⟨z, hzd⟩, hSzd⟩) = _
      rw [hx, ← hy₁, ← hsym]
      change inner ℝ (S y) (S ⟨z, hzd⟩) = _
      rw [hzz, hy₂, real_inner_self_eq_norm_sq]
    rwa [he, hx] at hxL
  exact le_of_tendsto_of_tendsto
    ((realSpectralCutoff_strong C (position S u)).norm.pow 2 |>.const_mul c)
    ((realSpectralCutoff_strong C (gradient S u)).norm.pow 2)
    (Filter.Eventually.of_forall hbound)

/-- Quantitative norm equivalence from the original positive operator gap. -/
theorem real_root_coercivity (C : Calculus (H := H)) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ x : (C.integral coordinate).domain,
      c * ‖(x : H)‖ ^ 2 ≤ inner ℝ (x : H) (C.integral coordinate x))
    (u : GraphDomain (squareRoot C)) :
    ‖position (squareRoot C) u‖ ≤ (Real.sqrt c)⁻¹ * ‖gradient (squareRoot C) u‖ := by
  have h := real_root_gap C c hgap u
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsq := Real.sq_sqrt hc.le
  have hp := norm_nonneg (position (squareRoot C) u)
  have hg := norm_nonneg (gradient (squareRoot C) u)
  have hm : Real.sqrt c * ‖position (squareRoot C) u‖ ≤ ‖gradient (squareRoot C) u‖ := by
    nlinarith
  rw [mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ hs).mpr
  nlinarith

/-- The real spectral square root has the required energy Hilbert realization. -/
def realEnergyHilbertModel (C : Calculus (H := H)) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ x : (C.integral coordinate).domain,
      c * ‖(x : H)‖ ^ 2 ≤ inner ℝ (x : H) (C.integral coordinate x)) :
    EnergyHilbertModel (squareRoot C) :=
  energyHilbertModelOfBound (squareRoot C) (C.closed root continuous_root.measurable)
    ⟨(Real.sqrt c)⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg c)⟩
    (real_root_coercivity C c hc hgap)

end

section
open RealNonnegativeSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- The actual graph-valued wave state. -/
def realGraphState (C : Calculus (H := H)) (t : ℝ)
    (x : GraphDomain (realFamily C).S × H) : GraphDomain (realFamily C).S × H :=
  (((realFamily C).S.mem_graph_iff.mp (real_displacement_graph C x.1 x.2 t)).choose,
    (realFamily C).velocity x.1 x.2 t)

@[simp] theorem realGraphState_position (C : Calculus (H := H)) (t : ℝ)
    (x : GraphDomain (realFamily C).S × H) :
    position (realFamily C).S (realGraphState C t x).1 =
      (realFamily C).displacement x.1 x.2 t :=
  ((realFamily C).S.mem_graph_iff.mp (real_displacement_graph C x.1 x.2 t)).choose_spec.1

@[simp] theorem realGraphState_gradient (C : Calculus (H := H)) (t : ℝ)
    (x : GraphDomain (realFamily C).S × H) :
    gradient (realFamily C).S (realGraphState C t x).1 =
      cosOperator C t (gradient (realFamily C).S x.1) + sinOperator C t x.2 :=
  ((realFamily C).S.mem_graph_iff.mp (real_displacement_graph C x.1 x.2 t)).choose_spec.2

@[simp] theorem realGraphState_velocity (C : Calculus (H := H)) (t : ℝ)
    (x : GraphDomain (realFamily C).S × H) :
    (realGraphState C t x).2 = (realFamily C).velocity x.1 x.2 t := rfl

/-- Linearity retains the original graph-domain displacement coordinate. -/
def realStateLinear (C : Calculus (H := H)) (t : ℝ) :
    (GraphDomain (realFamily C).S × H) →ₗ[ℝ] (GraphDomain (realFamily C).S × H) where
  toFun := realGraphState C t
  map_add' x y := by
    apply Prod.ext
    · apply (show Function.Injective (position (realFamily C).S) from
        fun a b h => Subtype.ext h)
      simp only [map_add, realGraphState_position, Prod.fst_add, Prod.snd_add,
        WaveFamily.displacement]
      abel
    · simp only [realGraphState_velocity, Prod.snd_add, Prod.fst_add, WaveFamily.velocity,
        map_add]
      abel
  map_smul' a x := by
    apply Prod.ext
    · apply (show Function.Injective (position (realFamily C).S) from
        fun a b h => Subtype.ext h)
      simp only [RingHom.id_apply, map_smul, realGraphState_position, Prod.smul_fst, Prod.smul_snd,
        WaveFamily.displacement]
      simp only [map_smul, smul_add]
    · simp only [RingHom.id_apply, realGraphState_velocity, Prod.smul_snd, Prod.smul_fst, WaveFamily.velocity,
        map_smul, smul_add, smul_neg]

@[simp] theorem realGraphState_zero (C : Calculus (H := H))
    (x : GraphDomain (realFamily C).S × H) : realGraphState C 0 x = x := by
  apply Prod.ext
  · apply (show Function.Injective (position (realFamily C).S) from
      fun a b h => Subtype.ext h)
    rw [realGraphState_position]
    exact (real_initial_conditions C x.1 x.2).1
  · exact (real_initial_conditions C x.1 x.2).2

@[simp] theorem realGraphState_add (C : Calculus (H := H)) (s t : ℝ)
    (x : GraphDomain (realFamily C).S × H) :
    realGraphState C (s + t) x = realGraphState C s (realGraphState C t x) := by
  have h := real_state_composition_formula C x.1 x.2 s t (realGraphState C t x).1
    (realGraphState_position C t x) (realGraphState_gradient C t x)
  apply Prod.ext
  · apply (show Function.Injective (position (realFamily C).S) from
      fun a b h => Subtype.ext h)
    simp only [realGraphState_position, realGraphState_velocity]
    exact h.1.symm
  · exact h.2.symm

/-- Strong continuity in the original graph-product topology. -/
theorem realGraphState_continuous (C : Calculus (H := H))
    (x : GraphDomain (realFamily C).S × H) : Continuous (fun t => realGraphState C t x) := by
  obtain ⟨⟨u, hu, hcoords⟩, hv⟩ := real_graph_continuity C x.1 x.2
  have he (t : ℝ) : (realGraphState C t x).1 = u t := by
    apply (show Function.Injective (position (realFamily C).S) from
      fun a b h => Subtype.ext h)
    rw [realGraphState_position, (hcoords t).1]
  exact (hu.congr (fun t => (he t).symm)).prodMk hv

/-- Any exact Hilbert realization of energy carries the genuine real wave group. -/
theorem real_group_of_model (C : Calculus (H := H)) (M : EnergyHilbertModel (realFamily C).S) :
    ∃ U : ℝ → M.Space ≃ₗᵢ[ℝ] M.Space,
      (∀ x, U 0 x = x) ∧
      (∀ s t x, U (s + t) x = U s (U t x)) ∧
      (∀ x, Continuous (fun t => U t x)) ∧
      ∀ (x : GraphDomain (realFamily C).S × H) t,
        position (realFamily C).S (M.coordinates.symm (U t (M.coordinates x))).1 =
          (realFamily C).displacement x.1 x.2 t ∧
        (M.coordinates.symm (U t (M.coordinates x))).2 = (realFamily C).velocity x.1 x.2 t := by
  let A (t : ℝ) : M.Space →ₗ[ℝ] M.Space :=
    M.coordinates.toLinearMap.comp ((realStateLinear C t).comp M.coordinates.symm.toLinearMap)
  have hA (t : ℝ) (x : M.Space) : A t x =
      M.coordinates (realGraphState C t (M.coordinates.symm x)) := rfl
  have hnorm (t : ℝ) (x : M.Space) : ‖A t x‖ = ‖x‖ := by
    have henergy := real_formula_energy C (M.coordinates.symm x).1 (M.coordinates.symm x).2 t
    have he (z : GraphDomain (realFamily C).S × H) :
        ‖M.coordinates z‖ ^ 2 = energy (realFamily C).S z.1 z.2 := by
      rw [← real_inner_self_eq_norm_sq, M.inner_eq]
      simp only [energyInner, energy, real_inner_self_eq_norm_sq]
    have hsq : ‖A t x‖ ^ 2 = ‖x‖ ^ 2 := by
      calc
        ‖A t x‖ ^ 2 = energy (realFamily C).S
            (realGraphState C t (M.coordinates.symm x)).1
            (realGraphState C t (M.coordinates.symm x)).2 := by rw [hA, he]
        _ = energy (realFamily C).S (M.coordinates.symm x).1 (M.coordinates.symm x).2 := by
          change ‖gradient (realFamily C).S (realGraphState C t (M.coordinates.symm x)).1‖ ^ 2 +
            ‖(realGraphState C t (M.coordinates.symm x)).2‖ ^ 2 = _
          rw [realGraphState_gradient, realGraphState_velocity]
          exact henergy
        _ = ‖x‖ ^ 2 := by simpa only [M.coordinates.apply_symm_apply] using
          (he (M.coordinates.symm x)).symm
    nlinarith [norm_nonneg (A t x), norm_nonneg x]
  let I (t : ℝ) : M.Space →ₗᵢ[ℝ] M.Space :=
    { toLinearMap := A t
      norm_map' := hnorm t }
  have hcomp (s t : ℝ) (x : M.Space) : A (s + t) x = A s (A t x) := by
    simp only [hA, M.coordinates.symm_apply_apply, realGraphState_add]
  have hzero (x : M.Space) : A 0 x = x := by
    simp only [hA, realGraphState_zero, M.coordinates.apply_symm_apply]
  have hsurj (t : ℝ) : Function.Surjective (I t) := by
    intro x
    refine ⟨A (-t) x, ?_⟩
    change A t (A (-t) x) = x
    rw [← hcomp, add_neg_cancel, hzero]
  let U (t : ℝ) := LinearIsometryEquiv.ofSurjective (I t) (hsurj t)
  refine ⟨U, hzero, hcomp, ?_, ?_⟩
  · intro x
    change Continuous (fun t => M.coordinates (realGraphState C t (M.coordinates.symm x)))
    exact M.coordinates.continuous.comp (realGraphState_continuous C _)
  · intro x t
    have hx : M.coordinates.symm (U t (M.coordinates x)) = realGraphState C t x := by
      change M.coordinates.symm
        (M.coordinates (realGraphState C t (M.coordinates.symm (M.coordinates x)))) = _
      simp only [M.coordinates.symm_apply_apply]
    rw [hx]
    exact ⟨realGraphState_position C t x, realGraphState_velocity C t x⟩

/-- The positive-gap real wave evolution is a strongly continuous unitary group. -/
theorem real_gap_group (C : Calculus (H := H)) :
    GapGroup (C.integral coordinate) (realFamily C) := by
  intro c hc hgap
  let M := realEnergyHilbertModel C c hc hgap
  exact ⟨M, real_group_of_model C M⟩

end

section
open RealNonnegativeSpectralCalculus
section ComplexGap
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H}

/-- Bounded coordinate products of the actual complex spectral cutoffs. -/
private theorem complex_coordinate_cutoff_bounded (n : ℕ) :
    SpectralMeasure.Spec.IsBoundedMeasurable
      (complexSymbol coordinate * MeasurableSpectralCalculus.cutoffIndicator (complexSymbol coordinate) n) := by
  have hf : Measurable (complexSymbol coordinate) :=
    Complex.measurable_ofReal.comp continuous_coordinate.measurable
  refine ⟨hf.mul (MeasurableSpectralCalculus.boundedMeasurable_cutoffIndicator hf n).1, n, ?_⟩
  intro s
  classical
  by_cases hs : ‖complexSymbol coordinate s‖ ≤ (n : ℝ)
  · simpa [MeasurableSpectralCalculus.cutoffIndicator, hs] using hs
  · simp [MeasurableSpectralCalculus.cutoffIndicator, hs]

/-- The original complex gap inequality extends from D(L) to the form domain. -/
theorem complex_root_gap (C : MeasurableSpectralCalculus.BoundedRealization E) (c : ℝ)
    (hgap : ∀ x : (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)).domain,
      c * ‖(x : H)‖ ^ 2 ≤
        RCLike.re (inner ℂ (x : H)
          (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate) x)))
    (u : GraphDomain (complexFamily C).S) :
    c * ‖position (complexFamily C).S u‖ ^ 2 ≤ ‖gradient (complexFamily C).S u‖ ^ 2 := by
  let S := (complexFamily C).S
  let L := MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)
  let q (n : ℕ) := MeasurableSpectralCalculus.cutoffIndicator (complexSymbol coordinate) n
  let p (n : ℕ) := C.integral (q n)
  have hf : Measurable (complexSymbol coordinate) :=
    Complex.measurable_ofReal.comp continuous_coordinate.measurable
  have hr : Measurable (complexSymbol root) :=
    Complex.measurable_ofReal.comp continuous_root.measurable
  have hq (n : ℕ) : SpectralMeasure.Spec.IsBoundedMeasurable (q n) :=
    MeasurableSpectralCalculus.boundedMeasurable_cutoffIndicator hf n
  have hs : S.IsFormalAdjoint S := by
    have h := LinearPMap.adjoint_isFormalAdjoint (MeasurableSpectralCalculus.measurableIntegral_dense C hr)
    rw [MeasurableSpectralCalculus.measurableIntegral_selfAdjoint C hr (fun _ => Complex.ofReal_im _)] at h
    exact h
  have hbound (n : ℕ) :
      c * ‖p n (position S u)‖ ^ 2 ≤ ‖p n (gradient S u)‖ ^ 2 := by
    have hL := UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_product_graph C hf
      (hq n) (complex_coordinate_cutoff_bounded n) (position S u)
    obtain ⟨x, hx, hy⟩ := L.mem_graph_iff.mp hL
    dsimp only at hx hy
    have hxL := hgap x
    have hS : (p n (position S u), p n (gradient S u)) ∈ S.graph :=
      UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_commutes C hr (hq n)
        (GraphDomain.toDomain S u)
    obtain ⟨y, hy₁, hy₂⟩ := S.mem_graph_iff.mp hS
    dsimp only at hy₁ hy₂
    have hprod : (p n (position S u), L x) ∈
        (OperatorDomainsSpec.productValue S S).graph := by
      rw [show OperatorDomainsSpec.productValue S S = _ from complex_square_root_square C]
      exact L.mem_graph_iff.mpr ⟨x, hx, rfl⟩
    obtain ⟨z, hz₁, hz₂⟩ := (OperatorDomainsSpec.productValue S S).mem_graph_iff.mp hprod
    dsimp only at hz₁ hz₂
    have hzd := z.2.choose
    have hSzd := z.2.choose_spec
    have hzz : (⟨(z : H), hzd⟩ : S.domain) = y := Subtype.ext (hz₁.trans hy₁.symm)
    have hsym := hs y ⟨S ⟨z, hzd⟩, hSzd⟩
    have he : RCLike.re (inner ℂ (x : H) (L x)) = ‖p n (gradient S u)‖ ^ 2 := by
      rw [← hz₂]
      change RCLike.re (inner ℂ (x : H) (S ⟨S ⟨z, hzd⟩, hSzd⟩)) = _
      rw [hx, ← hy₁, ← hsym]
      change RCLike.re (inner ℂ (S y) (S ⟨z, hzd⟩)) = _
      rw [hzz, hy₂, inner_self_eq_norm_sq]
    rwa [he, hx] at hxL
  exact le_of_tendsto_of_tendsto
    ((C.cutoff_tendsto hf (position S u)).norm.pow 2 |>.const_mul c)
    ((C.cutoff_tendsto hf (gradient S u)).norm.pow 2)
    (Filter.Eventually.of_forall hbound)

/-- Quantitative coercivity on D(S) from the original complex operator gap. -/
theorem complex_root_coercivity (C : MeasurableSpectralCalculus.BoundedRealization E)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ x : (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)).domain,
      c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (inner ℂ (x : H)
        (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate) x)))
    (u : GraphDomain (complexFamily C).S) :
    ‖position (complexFamily C).S u‖ ≤ (Real.sqrt c)⁻¹ * ‖gradient (complexFamily C).S u‖ := by
  have h := complex_root_gap C c hgap u
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsq := Real.sq_sqrt hc.le
  have hp := norm_nonneg (position (complexFamily C).S u)
  have hg := norm_nonneg (gradient (complexFamily C).S u)
  have hm : Real.sqrt c * ‖position (complexFamily C).S u‖ ≤ ‖gradient (complexFamily C).S u‖ := by
    nlinarith
  rw [mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ hs).mpr
  nlinarith

/-- The complex form domain has an exact complete Hilbert energy realization. -/
def complexEnergyHilbertModel (C : MeasurableSpectralCalculus.BoundedRealization E)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ x : (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)).domain,
      c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (inner ℂ (x : H)
        (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate) x))) :
    EnergyHilbertModel (complexFamily C).S :=
  energyHilbertModelOfBound (complexFamily C).S
    (MeasurableSpectralCalculus.measurableIntegral_isClosed C
      (Complex.measurable_ofReal.comp continuous_root.measurable))
    ⟨(Real.sqrt c)⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg c)⟩
    (complex_root_coercivity C c hc hgap)

end ComplexGap
end


/-- The complete energy evolution on every real Hilbert space. -/
theorem real_abstract_wave_energy : Spec.RealTheorem.{u} := by
  intro H _ _ _ L hL
  obtain ⟨C, hC⟩ := RealNonnegativeSpectralCalculus.spectral_existence H L hL
  refine ⟨C, hC, ?_⟩
  rw [← hC]
  exact ⟨real_square_root C, real_solution_claims C, real_classical_claims C,
    ⟨C.E {0}, real_kernel_projection C, real_kernel_drift C⟩, real_gap_group C⟩

section
open RealNonnegativeSpectralCalculus
open UnboundedNormalSpectralTheorem.SpectralRepresentation
open scoped ContDiff
section ComplexDerivative
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
  {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H}

lemma complex_integral_sub (C : MeasurableSpectralCalculus.BoundedRealization E)
    {f g : ℝ≥0 → ℝ} (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) :
    C.integral (complexSymbol (f-g)) = C.integral (complexSymbol f) - C.integral (complexSymbol g) := by
  have he : complexSymbol (f-g) = complexSymbol f + (-1:ℂ) • complexSymbol g := by
    ext s
    simp [complexSymbol, sub_eq_add_neg]
  rw [he, C.add _ _ (boundedMeasurable_wave_complexSymbol hf)
    ((boundedMeasurable_wave_complexSymbol hg).smul (-1)),
    C.smul _ _ (boundedMeasurable_wave_complexSymbol hg)]
  simp [sub_eq_add_neg]

lemma complex_integral_smul_real (C : MeasurableSpectralCalculus.BoundedRealization E)
    (a : ℝ) {f : ℝ≥0 → ℝ} (hf : IsBoundedMeasurable f) (x : H) :
    C.integral (complexSymbol (a • f)) x = a • C.integral (complexSymbol f) x := by
  have he : complexSymbol (a • f) = (a:ℂ) • complexSymbol f := by
    ext s
    simp [complexSymbol]
  rw [he, C.smul _ _ (boundedMeasurable_wave_complexSymbol hf)]
  change (a:ℂ) • C.integral (complexSymbol f) x = _
  exact IsScalarTower.algebraMap_smul ℂ a _

lemma hasDerivAt_complex_bounded_family (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f : ℝ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ) (t : ℝ)
    (hf : ∀ r, IsBoundedMeasurable (f r)) (hg : IsBoundedMeasurable g)
    (hd : ∀ s, HasDerivAt (fun r => f r s) (g s) t)
    (hM : ∃ M : ℝ, ∀ r s, |slope (fun z => f z s) t r| ≤ M)
    (x : H) : HasDerivAt (fun r => C.integral (complexSymbol (f r)) x)
      (C.integral (complexSymbol g) x) t := by
  rw [hasDerivAt_iff_tendsto_slope, Filter.tendsto_iff_seq_tendsto]
  intro a ha
  let k : ℕ → ℝ≥0 → ℝ := fun n s => slope (fun r => f r s) t (a n)
  have hk (n) : IsBoundedMeasurable (k n) := by
    change IsBoundedMeasurable (((a n-t)⁻¹) • (f (a n)-f t))
    exact boundedMeasurable_smul _ (boundedMeasurable_sub (hf _) (hf _))
  have hlim := strong_convergence C (complexSymbol g) (fun n => complexSymbol (k n))
    (boundedMeasurable_wave_complexSymbol hg) (fun n => boundedMeasurable_wave_complexSymbol (hk n))
    (by
      obtain ⟨M,hM⟩ := hM
      refine ⟨M, fun n s => ?_⟩
      simpa only [complexSymbol, Complex.norm_real, Real.norm_eq_abs, k] using hM (a n) s)
    (fun s => Complex.continuous_ofReal.tendsto (g s) |>.comp ((hd s).tendsto_slope.comp ha)) x
  convert hlim using 1
  funext n
  change (a n-t)⁻¹ • (C.integral (complexSymbol (f (a n))) x -
    C.integral (complexSymbol (f t)) x) = C.integral (complexSymbol (((a n-t)⁻¹) • (f (a n)-f t))) x
  rw [complex_integral_smul_real C _ (boundedMeasurable_sub (hf _) (hf _)),
    complex_integral_sub C (hf _) (hf _)]
  rfl

lemma hasDerivAt_complex_quotient_apply (C : MeasurableSpectralCalculus.BoundedRealization E)
    (x : H) (t : ℝ) :
    HasDerivAt (fun r => (complexFamily C).quotient r x) ((complexFamily C).cosine t x) t := by
  exact hasDerivAt_complex_bounded_family C quotientSine (cosine t) t
    boundedMeasurable_quotientSine (boundedMeasurable_cosine t)
    (scalar_quotient_deriv t) ⟨1,abs_slope_quotient_le t⟩ x

lemma hasDerivAt_complex_root_bounded_family (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f : ℝ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ) (t : ℝ)
    (hf : ∀ r, IsBoundedMeasurable (f r)) (hg : IsBoundedMeasurable g)
    (hg1 : ∀ s, |g s| ≤ 1)
    (hd : ∀ s, HasDerivAt (fun r => f r s) (g s * root s) t)
    (hM : ∀ r s, |slope (fun z => f z s) t r| ≤ root s)
    (x : (complexFamily C).S.domain) :
    HasDerivAt (fun r => C.integral (complexSymbol (f r)) x)
      (C.integral (complexSymbol g) ((complexFamily C).S x)) t := by
  let k := rootSlope f g t
  have hkb (r : ℝ) (s : ℝ≥0) : |k r s| ≤ 1 := by
    dsimp [k, rootSlope]
    split_ifs with hs
    · exact hg1 s
    · rw [abs_div, abs_of_nonneg (show 0 ≤ root s from Real.sqrt_nonneg _)]
      exact (div_le_one (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs))).mpr (hM r s)
  have hk (r : ℝ) : IsBoundedMeasurable (k r) := by
    refine ⟨?_, 1, hkb r⟩
    exact Measurable.ite (measurableSet_eq_fun continuous_root.measurable measurable_const)
      hg.1 ((measurable_const.mul ((hf r).1.sub (hf t).1)).div continuous_root.measurable)
  have hkr (r : ℝ) : root * k r = (r-t)⁻¹ • (f r-f t) := by
    funext s
    change root s * k r s = slope (fun z => f z s) t r
    dsimp [k, rootSlope]
    split_ifs with hs
    · rw [hs, zero_mul]
      have hh : |slope (fun z => f z s) t r| = 0 :=
        le_antisymm (hs ▸ hM r s) (abs_nonneg _)
      exact (abs_eq_zero.mp hh).symm
    · exact mul_div_cancel₀ _ hs
  have hkrC (r : ℝ) : complexSymbol root * complexSymbol (k r) =
      complexSymbol ((r-t)⁻¹ • (f r-f t)) := by
    rw [← wave_complexSymbol_mul, hkr]
  rw [hasDerivAt_iff_tendsto_slope, Filter.tendsto_iff_seq_tendsto]
  intro a ha
  have hpoint (s : ℝ≥0) : Tendsto (fun n => k (a n) s) atTop (𝓝 (g s)) := by
    dsimp [k, rootSlope]
    split_ifs with hs
    · exact tendsto_const_nhds
    · convert ((hd s).tendsto_slope.comp ha).div_const (root s) using 1 <;>
        first | rfl | rw [mul_div_cancel_right₀ _ hs]
  have hlim := strong_convergence C (complexSymbol g) (fun n => complexSymbol (k (a n)))
    (boundedMeasurable_wave_complexSymbol hg)
    (fun n => boundedMeasurable_wave_complexSymbol (hk (a n)))
    ⟨1, fun n s => by simpa only [complexSymbol, Complex.norm_real, Real.norm_eq_abs] using hkb (a n) s⟩
    (fun s => Complex.continuous_ofReal.tendsto (g s) |>.comp (hpoint s)) ((complexFamily C).S x)
  convert hlim using 1
  funext n
  have hleft := UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_product_graph C
    (measurable_wave_complexSymbol continuous_root.measurable)
    (boundedMeasurable_wave_complexSymbol (hk (a n)))
    (by
      rw [hkrC]
      exact boundedMeasurable_wave_complexSymbol
        (boundedMeasurable_smul _ (boundedMeasurable_sub (hf _) (hf _)))) (x:H)
  have hright := UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_commutes C
    (measurable_wave_complexSymbol continuous_root.measurable)
    (boundedMeasurable_wave_complexSymbol (hk (a n))) x
  have he := (complexFamily C).S.mem_graph_snd_inj hleft hright rfl
  rw [hkrC, complex_integral_smul_real C _ (boundedMeasurable_sub (hf _) (hf _)),
    complex_integral_sub C (hf _) (hf _)] at he
  exact he

lemma hasDerivAt_complex_cosine_apply (C : MeasurableSpectralCalculus.BoundedRealization E)
    (x : (complexFamily C).S.domain) (t : ℝ) :
    HasDerivAt (fun r => (complexFamily C).cosine r x)
      (-(complexFamily C).sine t ((complexFamily C).S x)) t := by
  have hg : IsBoundedMeasurable (-sine t) := by
    simpa only [neg_one_smul] using boundedMeasurable_smul (-1) (boundedMeasurable_sine t)
  have hh := hasDerivAt_complex_root_bounded_family C cosine (-sine t) t
    boundedMeasurable_cosine hg
    (fun s => by simpa only [Pi.neg_apply, abs_neg, sine] using Real.abs_sin_le_one (t * root s))
    (scalar_cosine_deriv t) (abs_slope_cosine_le t) x
  have he : C.integral (complexSymbol (-sine t)) ((complexFamily C).S x) =
      -C.integral (complexSymbol (sine t)) ((complexFamily C).S x) := by
    simpa only [neg_one_smul] using complex_integral_smul_real C (-1)
      (boundedMeasurable_sine t) ((complexFamily C).S x)
  rw [he] at hh
  exact hh

lemma hasDerivAt_complex_sine_apply (C : MeasurableSpectralCalculus.BoundedRealization E)
    (x : (complexFamily C).S.domain) (t : ℝ) :
    HasDerivAt (fun r => (complexFamily C).sine r x)
      ((complexFamily C).cosine t ((complexFamily C).S x)) t := by
  exact hasDerivAt_complex_root_bounded_family C sine (cosine t) t
    boundedMeasurable_sine (boundedMeasurable_cosine t)
    (fun s => Real.abs_cos_le_one _) (scalar_sine_deriv t) (abs_slope_sine_le t) x

lemma hasDerivAt_complex_displacement (C : MeasurableSpectralCalculus.BoundedRealization E)
    (u₀ : GraphDomain (complexFamily C).S) (v₀ : H) (t : ℝ) :
    HasDerivAt ((complexFamily C).displacement u₀ v₀)
      ((complexFamily C).velocity u₀ v₀ t) t := by
  exact (hasDerivAt_complex_cosine_apply C (GraphDomain.toDomain (complexFamily C).S u₀) t).add
    (hasDerivAt_complex_quotient_apply C v₀ t)

lemma complex_integral_inner (C : MeasurableSpectralCalculus.BoundedRealization E)
    {f : ℝ≥0 → ℝ} (hf : IsBoundedMeasurable f) (x y : H) :
    inner ℂ (C.integral (complexSymbol f) x) y = inner ℂ x (C.integral (complexSymbol f) y) := by
  have h := (C.integral (complexSymbol f)).adjoint_inner_right x y
  have ha : ContinuousLinearMap.adjoint (C.integral (complexSymbol f)) = C.integral (complexSymbol f) := by
    rw [← ContinuousLinearMap.star_eq_adjoint,
      ← C.map_star _ (boundedMeasurable_wave_complexSymbol hf), wave_complexSymbol_star]
  rw [ha] at h
  exact h.symm

lemma inner_complex_cosine_apply (C : MeasurableSpectralCalculus.BoundedRealization E)
    (t : ℝ) (x y : H) :
    inner ℂ ((complexFamily C).cosine t x) y = inner ℂ x ((complexFamily C).cosine t y) :=
  complex_integral_inner C (boundedMeasurable_cosine t) x y

lemma inner_complex_sine_apply (C : MeasurableSpectralCalculus.BoundedRealization E)
    (t : ℝ) (x y : H) :
    inner ℂ ((complexFamily C).sine t x) y = inner ℂ x ((complexFamily C).sine t y) :=
  complex_integral_inner C (boundedMeasurable_sine t) x y

lemma hasDerivAt_complex_velocity_weak (C : MeasurableSpectralCalculus.BoundedRealization E)
    (u₀ w : GraphDomain (complexFamily C).S) (v₀ : H) (t : ℝ) :
    HasDerivAt (fun r => dualInjection (complexFamily C).S ((complexFamily C).velocity u₀ v₀ r) w)
      (-inner ℂ
        ((complexFamily C).cosine t (gradient (complexFamily C).S u₀) + (complexFamily C).sine t v₀)
        (gradient (complexFamily C).S w)) t := by
  let x := GraphDomain.toDomain (complexFamily C).S w
  let a := gradient (complexFamily C).S u₀
  have hs := (hasDerivAt_const t a).inner ℂ (hasDerivAt_complex_sine_apply C x t)
  have hc := (hasDerivAt_const t v₀).inner ℂ (hasDerivAt_complex_cosine_apply C x t)
  have he : (fun r => dualInjection (complexFamily C).S ((complexFamily C).velocity u₀ v₀ r) w) =
      (fun r => -inner ℂ a ((complexFamily C).sine r x) + inner ℂ v₀ ((complexFamily C).cosine r x)) := by
    funext r
    change inner ℂ (-(complexFamily C).sine r a + (complexFamily C).cosine r v₀) (x:H) = _
    rw [inner_add_left, inner_neg_left, inner_complex_sine_apply, inner_complex_cosine_apply]
  rw [he]
  convert hs.neg.add hc using 1
  change -(inner ℂ ((complexFamily C).cosine t a + (complexFamily C).sine t v₀) ((complexFamily C).S x)) = _
  simp only [inner_zero_left, zero_add, inner_neg_right, inner_add_left,
    inner_complex_cosine_apply, inner_complex_sine_apply, neg_add_rev, add_comm]

lemma complex_solution_claims (C : MeasurableSpectralCalculus.BoundedRealization E) :
    SolutionClaims (complexFamily C) := by
  intro u₀ v₀
  obtain ⟨⟨u,huc,hu⟩,hvc⟩ := complex_graph_continuity C u₀ v₀
  have huv : IsEnergySolution (complexFamily C).S u ((complexFamily C).velocity u₀ v₀) := by
    refine ⟨huc,hvc,?_,?_⟩
    · intro t
      convert hasDerivAt_complex_displacement C u₀ v₀ t using 1
      funext r
      exact (hu r).1
    · intro w t
      change HasDerivAt _ (-inner ℂ (gradient (complexFamily C).S (u t)) (gradient (complexFamily C).S w)) t
      rw [(hu t).2]
      exact hasDerivAt_complex_velocity_weak C u₀ w v₀ t
  have h0 : u 0 = u₀ := by
    apply Subtype.ext
    change position (complexFamily C).S (u 0) = position (complexFamily C).S u₀
    rw [(hu 0).1]
    exact (complex_initial_conditions C u₀ v₀).1
  have hv0 := (complex_initial_conditions C u₀ v₀).2
  refine ⟨u,fun t => (hu t).1,huv,h0,hv0,?_,?_⟩
  · intro z w hzw hz0 hw0
    exact energy_solution_unique (complexFamily C).S
      (MeasurableSpectralCalculus.measurableIntegral_isClosed C
        (measurable_wave_complexSymbol continuous_root.measurable))
      z u w ((complexFamily C).velocity u₀ v₀) hzw huv (hz0.trans h0.symm) (hw0.trans hv0.symm)
  · intro t
    unfold energy
    rw [(hu t).2]
    exact complex_formula_energy C u₀ v₀ t

lemma complex_classical_claims (C : MeasurableSpectralCalculus.BoundedRealization E) :
    ClassicalClaims (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)) (complexFamily C) := by
  intro u₀ v₀ hu₀ hv₀
  let S := (complexFamily C).S
  let x : S.domain := GraphDomain.toDomain S u₀
  have hx : (x:H) ∈ (OperatorDomainsSpec.productValue S S).domain := by
    rw [complex_square_root_square C]
    exact hu₀
  have hSx : S x ∈ S.domain := (mem_product_domain_iff S S (x:H)).mp hx |>.2
  let y : S.domain := ⟨S x, hSx⟩
  let z : S.domain := ⟨v₀, hv₀⟩
  let a : ℝ → H := fun t => (complexFamily C).cosine t (S y) + (complexFamily C).sine t (S z)
  have hd (t : ℝ) : HasDerivAt ((complexFamily C).velocity u₀ v₀) (-a t) t := by
    have hh := (hasDerivAt_complex_sine_apply C y t).neg.add (hasDerivAt_complex_cosine_apply C z t)
    change HasDerivAt (fun r => -(complexFamily C).sine r (S x) + (complexFamily C).cosine r v₀)
      (-((complexFamily C).cosine t (S y) + (complexFamily C).sine t (S z))) t
    convert hh using 1 <;> simp only [Pi.add_apply, Pi.neg_apply, y, z, neg_add, S] <;> rfl
  have hc : Continuous a := (continuous_complex_cosine_apply C _).add (continuous_complex_sine_apply C _)
  have hvderiv : deriv ((complexFamily C).velocity u₀ v₀) = -a := by
    funext t
    exact (hd t).deriv
  have hvelocity : ContDiff ℝ 1 ((complexFamily C).velocity u₀ v₀) := by
    rw [contDiff_one_iff_deriv, hvderiv]
    exact ⟨fun t => (hd t).differentiableAt, hc.neg⟩
  have hudiff := hasDerivAt_complex_displacement C u₀ v₀
  have hud : deriv ((complexFamily C).displacement u₀ v₀) = (complexFamily C).velocity u₀ v₀ := by
    funext t
    exact (hudiff t).deriv
  constructor
  · rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv, hud]
    exact ⟨fun t => (hudiff t).differentiableAt, by simp, hvelocity⟩
  · intro t
    have hu := complex_displacement_graph C u₀ v₀ t
    have hSu := S.graph.add_mem
      (UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_commutes C
        (measurable_wave_complexSymbol continuous_root.measurable)
        (boundedMeasurable_wave_complexSymbol (boundedMeasurable_cosine t)) y)
      (UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_commutes C
        (measurable_wave_complexSymbol continuous_root.measurable)
        (boundedMeasurable_wave_complexSymbol (boundedMeasurable_sine t)) z)
    obtain ⟨b, hb, hbS⟩ := S.mem_graph_iff.mp hu
    change (b:H) = (complexFamily C).displacement u₀ v₀ t at hb
    change S b = (complexFamily C).cosine t (S x) + (complexFamily C).sine t v₀ at hbS
    obtain ⟨c, hc0, hcS⟩ := S.mem_graph_iff.mp hSu
    change (c:H) = (complexFamily C).cosine t (S x) + (complexFamily C).sine t v₀ at hc0
    change S c = a t at hcS
    have hSb : S b ∈ S.domain := by
      rw [hbS, ← hc0]
      exact c.property
    have hdom : (complexFamily C).displacement u₀ v₀ t ∈ (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)).domain := by
      rw [← complex_square_root_square C]
      apply (mem_product_domain_iff S S _).mpr
      rw [← hb]
      exact ⟨b.property, hSb⟩
    refine ⟨hdom, ?_⟩
    have he : MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate) ⟨(complexFamily C).displacement u₀ v₀ t, hdom⟩ = a t := by
      have hgraph : ((complexFamily C).displacement u₀ v₀ t, a t) ∈
          (OperatorDomainsSpec.productValue S S).graph := by
        apply (OperatorDomainsSpec.productValue S S).mem_graph_iff.mpr
        refine ⟨⟨(b:H), ⟨b.property, hSb⟩⟩, hb, ?_⟩
        rw [product_apply S S b hSb]
        have hbc : (⟨S b, hSb⟩ : S.domain) = c := by
          apply Subtype.ext
          exact hbS.trans hc0.symm
        rw [hbc]
        exact hcS
      rw [complex_square_root_square C] at hgraph
      obtain ⟨d, hd0, hd1⟩ := (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)).mem_graph_iff.mp hgraph
      change (d:H) = (complexFamily C).displacement u₀ v₀ t at hd0
      have hde : (⟨(complexFamily C).displacement u₀ v₀ t, hdom⟩ : (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)).domain) = d :=
        Subtype.ext hd0.symm
      rw [hde]
      exact hd1
    rw [he]
    exact hd t

end ComplexDerivative
end

section
open RealNonnegativeSpectralCalculus
section ComplexState
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H}

private theorem complex_bounded_real_add (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f g : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) :
    C.integral (complexSymbol (f + g)) =
      C.integral (complexSymbol f) + C.integral (complexSymbol g) := by
  change C.integral (RealNonnegativeSpectralCalculus.complexSymbol (f + g)) = _
  rw [RealNonnegativeSpectralCalculus.complexSymbol_add]
  exact C.add _ _ (boundedMeasurable_complexSymbol hf) (boundedMeasurable_complexSymbol hg)

private theorem complex_bounded_real_smul (C : MeasurableSpectralCalculus.BoundedRealization E)
    (a : ℝ) (f : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) :
    C.integral (complexSymbol (a • f)) = (a : ℂ) • C.integral (complexSymbol f) := by
  change C.integral (RealNonnegativeSpectralCalculus.complexSymbol (a • f)) = _
  rw [RealNonnegativeSpectralCalculus.complexSymbol_smul]
  exact C.smul _ _ (boundedMeasurable_complexSymbol hf)

private theorem complex_bounded_real_mul (C : MeasurableSpectralCalculus.BoundedRealization E)
    (f g : ℝ≥0 → ℝ) (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) :
    C.integral (complexSymbol (f * g)) =
      C.integral (complexSymbol f) * C.integral (complexSymbol g) := by
  change C.integral (RealNonnegativeSpectralCalculus.complexSymbol (f * g)) = _
  rw [RealNonnegativeSpectralCalculus.complexSymbol_mul]
  exact C.mul _ _ (boundedMeasurable_complexSymbol hf) (boundedMeasurable_complexSymbol hg)

/-- Addition formula for the cosine multiplier of the actual complex PVM. -/
theorem complex_cosOperator_add (C : MeasurableSpectralCalculus.BoundedRealization E) (s t : ℝ) :
    (complexFamily C).cosine (s + t) =
      (complexFamily C).cosine s * (complexFamily C).cosine t -
        (complexFamily C).sine s * (complexFamily C).sine t := by
  change C.integral (complexSymbol (cosine (s + t))) = _
  rw [cosine_add_symbol, complex_bounded_real_add C _ _
    (waveBoundedMeasurable_mul (boundedMeasurable_cosine s) (boundedMeasurable_cosine t))
    (waveBoundedMeasurable_smul _ (waveBoundedMeasurable_mul (boundedMeasurable_sine s)
      (boundedMeasurable_sine t))),
    complex_bounded_real_smul C _ _ (waveBoundedMeasurable_mul (boundedMeasurable_sine s)
      (boundedMeasurable_sine t)),
    complex_bounded_real_mul C _ _ (boundedMeasurable_cosine s) (boundedMeasurable_cosine t),
    complex_bounded_real_mul C _ _ (boundedMeasurable_sine s) (boundedMeasurable_sine t)]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, sub_eq_add_neg]
  rfl

/-- Addition formula for the sine multiplier of the actual complex PVM. -/
theorem complex_sinOperator_add (C : MeasurableSpectralCalculus.BoundedRealization E) (s t : ℝ) :
    (complexFamily C).sine (s + t) =
      (complexFamily C).sine s * (complexFamily C).cosine t +
        (complexFamily C).cosine s * (complexFamily C).sine t := by
  change C.integral (complexSymbol (sine (s + t))) = _
  rw [sine_add_symbol, complex_bounded_real_add C _ _
    (waveBoundedMeasurable_mul (boundedMeasurable_sine s) (boundedMeasurable_cosine t))
    (waveBoundedMeasurable_mul (boundedMeasurable_cosine s) (boundedMeasurable_sine t)),
    complex_bounded_real_mul C _ _ (boundedMeasurable_sine s) (boundedMeasurable_cosine t),
    complex_bounded_real_mul C _ _ (boundedMeasurable_cosine s) (boundedMeasurable_sine t)]
  rfl

/-- Addition formula retaining the zero-mode quotient value. -/
theorem complex_quotientOperator_add (C : MeasurableSpectralCalculus.BoundedRealization E) (s t : ℝ) :
    (complexFamily C).quotient (s + t) =
      (complexFamily C).cosine s * (complexFamily C).quotient t +
        (complexFamily C).quotient s * (complexFamily C).cosine t := by
  change C.integral (complexSymbol (quotientSine (s + t))) = _
  rw [quotientSine_add_symbol, complex_bounded_real_add C _ _
    (waveBoundedMeasurable_mul (boundedMeasurable_cosine s) (boundedMeasurable_quotientSine t))
    (waveBoundedMeasurable_mul (boundedMeasurable_quotientSine s) (boundedMeasurable_cosine t)),
    complex_bounded_real_mul C _ _ (boundedMeasurable_cosine s) (boundedMeasurable_quotientSine t),
    complex_bounded_real_mul C _ _ (boundedMeasurable_quotientSine s) (boundedMeasurable_cosine t)]
  rfl

theorem complex_bounded_apply_comm (C : MeasurableSpectralCalculus.BoundedRealization E)
    {f g : ℝ≥0 → ℝ} (hf : IsBoundedMeasurable f) (hg : IsBoundedMeasurable g) (x : H) :
    C.integral (complexSymbol f) (C.integral (complexSymbol g) x) =
      C.integral (complexSymbol g) (C.integral (complexSymbol f) x) := by
  have he : C.integral (complexSymbol f) * C.integral (complexSymbol g) =
      C.integral (complexSymbol g) * C.integral (complexSymbol f) := by
    rw [← complex_bounded_real_mul C f g hf hg, ← complex_bounded_real_mul C g f hg hf, mul_comm]
  exact congrArg (fun T : H →L[ℂ] H => T x) he

theorem complex_quotient_gradient (C : MeasurableSpectralCalculus.BoundedRealization E)
    (t : ℝ) (u : GraphDomain (complexFamily C).S) :
    (complexFamily C).quotient t (gradient (complexFamily C).S u) =
      (complexFamily C).sine t (position (complexFamily C).S u) := by
  have hr : Measurable (complexSymbol root) :=
    Complex.measurable_ofReal.comp continuous_root.measurable
  have hq : SpectralMeasure.Spec.IsBoundedMeasurable (complexSymbol (quotientSine t)) :=
    boundedMeasurable_complexSymbol (boundedMeasurable_quotientSine t)
  have h₁ := UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_commutes C hr hq
    (GraphDomain.toDomain (complexFamily C).S u)
  have heq : complexSymbol root * complexSymbol (quotientSine t) = complexSymbol (sine t) := by
    change RealNonnegativeSpectralCalculus.complexSymbol root *
      RealNonnegativeSpectralCalculus.complexSymbol (quotientSine t) = _
    rw [← RealNonnegativeSpectralCalculus.complexSymbol_mul, root_mul_quotientSine]
    rfl
  have h₂ := UnboundedNormalSpectralTheorem.SpectralRepresentation.bounded_product_graph C hr hq
    (heq ▸ boundedMeasurable_complexSymbol (boundedMeasurable_sine t))
    (position (complexFamily C).S u)
  rw [heq] at h₂
  exact (complexFamily C).S.mem_graph_snd_inj h₁ h₂ rfl

/-- Exact time composition on the original complex graph-domain states. -/
theorem complex_state_composition_formula (C : MeasurableSpectralCalculus.BoundedRealization E)
    (u₀ : GraphDomain (complexFamily C).S) (v₀ : H) (s t : ℝ)
    (z : GraphDomain (complexFamily C).S)
    (hz : position (complexFamily C).S z = (complexFamily C).displacement u₀ v₀ t)
    (hSz : gradient (complexFamily C).S z =
      (complexFamily C).cosine t (gradient (complexFamily C).S u₀) +
        (complexFamily C).sine t v₀) :
    (complexFamily C).displacement z ((complexFamily C).velocity u₀ v₀ t) s =
      (complexFamily C).displacement u₀ v₀ (s + t) ∧
    (complexFamily C).velocity z ((complexFamily C).velocity u₀ v₀ t) s =
      (complexFamily C).velocity u₀ v₀ (s + t) := by
  have hQ : (complexFamily C).quotient s
      ((complexFamily C).sine t (gradient (complexFamily C).S u₀)) =
      (complexFamily C).sine s ((complexFamily C).sine t (position (complexFamily C).S u₀)) := by
    change C.integral (complexSymbol (quotientSine s)) (C.integral (complexSymbol (sine t)) _) = _
    rw [complex_bounded_apply_comm C (boundedMeasurable_quotientSine s) (boundedMeasurable_sine t)]
    change (complexFamily C).sine t ((complexFamily C).quotient s (gradient (complexFamily C).S u₀)) = _
    rw [complex_quotient_gradient]
    exact complex_bounded_apply_comm C (boundedMeasurable_sine t) (boundedMeasurable_sine s) _
  constructor
  · change (complexFamily C).cosine s (position (complexFamily C).S z) +
      (complexFamily C).quotient s (-(complexFamily C).sine t (gradient (complexFamily C).S u₀) +
        (complexFamily C).cosine t v₀) = _
    rw [hz]
    change (complexFamily C).cosine s ((complexFamily C).cosine t (position (complexFamily C).S u₀) +
      (complexFamily C).quotient t v₀) + (complexFamily C).quotient s
      (-(complexFamily C).sine t (gradient (complexFamily C).S u₀) + (complexFamily C).cosine t v₀) =
      (complexFamily C).cosine (s + t) (position (complexFamily C).S u₀) +
        (complexFamily C).quotient (s + t) v₀
    rw [complex_cosOperator_add, complex_quotientOperator_add]
    simp only [map_add, map_neg, sub_apply,
      _root_.add_apply, mul_apply_eq_comp, hQ]
    abel
  · change -(complexFamily C).sine s (gradient (complexFamily C).S z) +
      (complexFamily C).cosine s (-(complexFamily C).sine t (gradient (complexFamily C).S u₀) +
        (complexFamily C).cosine t v₀) =
      -(complexFamily C).sine (s + t) (gradient (complexFamily C).S u₀) +
        (complexFamily C).cosine (s + t) v₀
    rw [hSz, complex_cosOperator_add, complex_sinOperator_add]
    simp only [map_add, map_neg, sub_apply,
      _root_.add_apply, mul_apply_eq_comp]
    abel

end ComplexState
end

section
open RealNonnegativeSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H}
/-- The actual graph-valued wave state. -/
def complexGraphState (C : MeasurableSpectralCalculus.BoundedRealization E) (t : ℝ)
    (x : GraphDomain (complexFamily C).S × H) : GraphDomain (complexFamily C).S × H :=
  (((complexFamily C).S.mem_graph_iff.mp (complex_displacement_graph C x.1 x.2 t)).choose,
    (complexFamily C).velocity x.1 x.2 t)

@[simp] theorem complexGraphState_position (C : MeasurableSpectralCalculus.BoundedRealization E) (t : ℝ)
    (x : GraphDomain (complexFamily C).S × H) :
    position (complexFamily C).S (complexGraphState C t x).1 =
      (complexFamily C).displacement x.1 x.2 t :=
  ((complexFamily C).S.mem_graph_iff.mp (complex_displacement_graph C x.1 x.2 t)).choose_spec.1

@[simp] theorem complexGraphState_gradient (C : MeasurableSpectralCalculus.BoundedRealization E) (t : ℝ)
    (x : GraphDomain (complexFamily C).S × H) :
    gradient (complexFamily C).S (complexGraphState C t x).1 =
      (complexFamily C).cosine t (gradient (complexFamily C).S x.1) + (complexFamily C).sine t x.2 :=
  ((complexFamily C).S.mem_graph_iff.mp (complex_displacement_graph C x.1 x.2 t)).choose_spec.2

@[simp] theorem complexGraphState_velocity (C : MeasurableSpectralCalculus.BoundedRealization E) (t : ℝ)
    (x : GraphDomain (complexFamily C).S × H) :
    (complexGraphState C t x).2 = (complexFamily C).velocity x.1 x.2 t := rfl

/-- Linearity retains the original graph-domain displacement coordinate. -/
def complexStateLinear (C : MeasurableSpectralCalculus.BoundedRealization E) (t : ℝ) :
    (GraphDomain (complexFamily C).S × H) →ₗ[ℂ] (GraphDomain (complexFamily C).S × H) where
  toFun := complexGraphState C t
  map_add' x y := by
    apply Prod.ext
    · apply (show Function.Injective (position (complexFamily C).S) from
        fun a b h => Subtype.ext h)
      simp only [map_add, complexGraphState_position, Prod.fst_add, Prod.snd_add,
        WaveFamily.displacement]
      abel
    · simp only [complexGraphState_velocity, Prod.snd_add, Prod.fst_add, WaveFamily.velocity,
        map_add]
      abel
  map_smul' a x := by
    apply Prod.ext
    · apply (show Function.Injective (position (complexFamily C).S) from
        fun a b h => Subtype.ext h)
      simp only [RingHom.id_apply, map_smul, complexGraphState_position, Prod.smul_fst, Prod.smul_snd,
        WaveFamily.displacement]
      simp only [map_smul, smul_add]
    · simp only [RingHom.id_apply, complexGraphState_velocity, Prod.smul_snd, Prod.smul_fst, WaveFamily.velocity,
        map_smul, smul_add, smul_neg]

@[simp] theorem complexGraphState_zero (C : MeasurableSpectralCalculus.BoundedRealization E)
    (x : GraphDomain (complexFamily C).S × H) : complexGraphState C 0 x = x := by
  apply Prod.ext
  · apply (show Function.Injective (position (complexFamily C).S) from
      fun a b h => Subtype.ext h)
    rw [complexGraphState_position]
    exact (complex_initial_conditions C x.1 x.2).1
  · exact (complex_initial_conditions C x.1 x.2).2

@[simp] theorem complexGraphState_add (C : MeasurableSpectralCalculus.BoundedRealization E) (s t : ℝ)
    (x : GraphDomain (complexFamily C).S × H) :
    complexGraphState C (s + t) x = complexGraphState C s (complexGraphState C t x) := by
  have h := complex_state_composition_formula C x.1 x.2 s t (complexGraphState C t x).1
    (complexGraphState_position C t x) (complexGraphState_gradient C t x)
  apply Prod.ext
  · apply (show Function.Injective (position (complexFamily C).S) from
      fun a b h => Subtype.ext h)
    simp only [complexGraphState_position, complexGraphState_velocity]
    exact h.1.symm
  · exact h.2.symm

/-- Strong continuity in the original graph-product topology. -/
theorem complexGraphState_continuous (C : MeasurableSpectralCalculus.BoundedRealization E)
    (x : GraphDomain (complexFamily C).S × H) : Continuous (fun t => complexGraphState C t x) := by
  obtain ⟨⟨u, hu, hcoords⟩, hv⟩ := complex_graph_continuity C x.1 x.2
  have he (t : ℝ) : (complexGraphState C t x).1 = u t := by
    apply (show Function.Injective (position (complexFamily C).S) from
      fun a b h => Subtype.ext h)
    rw [complexGraphState_position, (hcoords t).1]
  exact (hu.congr (fun t => (he t).symm)).prodMk hv

/-- Any exact Hilbert realization of energy carries the genuine complex wave group. -/
theorem complex_group_of_model (C : MeasurableSpectralCalculus.BoundedRealization E) (M : EnergyHilbertModel (complexFamily C).S) :
    ∃ U : ℝ → M.Space ≃ₗᵢ[ℂ] M.Space,
      (∀ x, U 0 x = x) ∧
      (∀ s t x, U (s + t) x = U s (U t x)) ∧
      (∀ x, Continuous (fun t => U t x)) ∧
      ∀ (x : GraphDomain (complexFamily C).S × H) t,
        position (complexFamily C).S (M.coordinates.symm (U t (M.coordinates x))).1 =
          (complexFamily C).displacement x.1 x.2 t ∧
        (M.coordinates.symm (U t (M.coordinates x))).2 = (complexFamily C).velocity x.1 x.2 t := by
  let A (t : ℝ) : M.Space →ₗ[ℂ] M.Space :=
    M.coordinates.toLinearMap.comp ((complexStateLinear C t).comp M.coordinates.symm.toLinearMap)
  have hA (t : ℝ) (x : M.Space) : A t x =
      M.coordinates (complexGraphState C t (M.coordinates.symm x)) := rfl
  have hnorm (t : ℝ) (x : M.Space) : ‖A t x‖ = ‖x‖ := by
    have henergy := complex_formula_energy C (M.coordinates.symm x).1 (M.coordinates.symm x).2 t
    have he (z : GraphDomain (complexFamily C).S × H) :
        ‖M.coordinates z‖ ^ 2 = energy (complexFamily C).S z.1 z.2 := by
      have h := congrArg RCLike.re (M.inner_eq z z)
      simpa only [energyInner, energy, map_add, inner_self_eq_norm_sq] using h
    have hsq : ‖A t x‖ ^ 2 = ‖x‖ ^ 2 := by
      calc
        ‖A t x‖ ^ 2 = energy (complexFamily C).S
            (complexGraphState C t (M.coordinates.symm x)).1
            (complexGraphState C t (M.coordinates.symm x)).2 := by rw [hA, he]
        _ = energy (complexFamily C).S (M.coordinates.symm x).1 (M.coordinates.symm x).2 := by
          change ‖gradient (complexFamily C).S (complexGraphState C t (M.coordinates.symm x)).1‖ ^ 2 +
            ‖(complexGraphState C t (M.coordinates.symm x)).2‖ ^ 2 = _
          rw [complexGraphState_gradient, complexGraphState_velocity]
          exact henergy
        _ = ‖x‖ ^ 2 := by simpa only [M.coordinates.apply_symm_apply] using
          (he (M.coordinates.symm x)).symm
    nlinarith [norm_nonneg (A t x), norm_nonneg x]
  let I (t : ℝ) : M.Space →ₗᵢ[ℂ] M.Space :=
    { toLinearMap := A t
      norm_map' := hnorm t }
  have hcomp (s t : ℝ) (x : M.Space) : A (s + t) x = A s (A t x) := by
    simp only [hA, M.coordinates.symm_apply_apply, complexGraphState_add]
  have hzero (x : M.Space) : A 0 x = x := by
    simp only [hA, complexGraphState_zero, M.coordinates.apply_symm_apply]
  have hsurj (t : ℝ) : Function.Surjective (I t) := by
    intro x
    refine ⟨A (-t) x, ?_⟩
    change A t (A (-t) x) = x
    rw [← hcomp, add_neg_cancel, hzero]
  let U (t : ℝ) := LinearIsometryEquiv.ofSurjective (I t) (hsurj t)
  refine ⟨U, hzero, hcomp, ?_, ?_⟩
  · intro x
    change Continuous (fun t => M.coordinates (complexGraphState C t (M.coordinates.symm x)))
    exact M.coordinates.continuous.comp (complexGraphState_continuous C _)
  · intro x t
    have hx : M.coordinates.symm (U t (M.coordinates x)) = complexGraphState C t x := by
      change M.coordinates.symm
        (M.coordinates (complexGraphState C t (M.coordinates.symm (M.coordinates x)))) = _
      simp only [M.coordinates.symm_apply_apply]
    rw [hx]
    exact ⟨complexGraphState_position C t x, complexGraphState_velocity C t x⟩

/-- The positive-gap complex wave evolution is a strongly continuous unitary group. -/
theorem complex_gap_group (C : MeasurableSpectralCalculus.BoundedRealization E) :
    GapGroup (MeasurableSpectralCalculus.measurableIntegral C (complexSymbol coordinate)) (complexFamily C) := by
  intro c hc hgap
  let M := complexEnergyHilbertModel C c hc hgap
  exact ⟨M, complex_group_of_model C M⟩

end


/-- The complete energy evolution on every complex Hilbert space. -/
theorem complex_abstract_wave_energy : Spec.ComplexTheorem.{u} := by
  intro H _ _ _ L hL
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  obtain ⟨E, C, hC⟩ := complex_spectral_existence H L hL
  refine ⟨E, C, hC, ?_⟩
  rw [← hC]
  exact ⟨complex_square_root C, complex_solution_claims C, complex_classical_claims C,
    ⟨E {0}, complex_kernel_projection C, complex_kernel_drift C⟩, complex_gap_group C⟩

/-- The abstract wave theorem with both scalar fields and all energy-space clauses. -/
theorem abstract_wave_energy : Spec.FullTheorem.{u} :=
  ⟨real_abstract_wave_energy, complex_abstract_wave_energy⟩

end ExpandedFA.Models.AbstractWaveEnergy
