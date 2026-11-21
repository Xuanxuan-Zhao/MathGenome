import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.BallSchauderSolvability
import MathGenome.Internal.LinearPDE.P201.Elliptic.MaximumComparison
import MathGenome.Internal.LinearPDE.P201.Elliptic.WeightedInterpolation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import MathGenome.Internal.LinearPDE.P201.Elliptic.PoissonSchauder
import MathGenome.Internal.LinearPDE.P201.Potential.BallPoisson
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import MathGenome.Internal.FourierSobolev.P102.U4.RegularDerivatives
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Tactic.Module

import MathGenome.Internal.LinearPDE.P201.Elliptic.VariableSchauder
/-!
Conditional derivations for the ball Dirichlet problem, including every
positive dimension and continuous sphere data. The public conditional
helpers take the full frozen global, interior and local boundary Schauder
statements in that order. The original closed targets are intentionally
not declared; their owner supplies wrappers only after dependency closure.

The Laplacian start is constructed from Newton and Poisson potentials, with
the interval handled directly and higher-dimensional boundary regularity
proved through Kelvin inversion and the supplied flat-boundary theorem.
The concrete Hölder Banach spaces, uniform barriers, actual operator path,
continuity argument, smooth approximation and derivative-limit bridges
establish all three original statements under precisely those parameters.
-/
noncomputable section
open Set Metric Filter
open scoped ContDiff NNReal ENNReal Topology

namespace P201.Elliptic.BallSchauderSolvability
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201Specs.Elliptic.BallSchauderSolvability
open P201Specs.Elliptic.HolderCancellation

/-- The bounded scalar Hölder predicate implies genuine continuity on its
set, for every positive exponent, including non-open sets. -/
lemma continuousOn_of_isHolderOn {n : ℕ} {α : ℝ} (hα : 0 < α)
    {f : Space n → ℝ} {s : Set (Space n)} (hf : IsHolderOn α f s) :
    ContinuousOn f s := by
  obtain ⟨M, H, hM, hH, hb, hh⟩ := hf
  let C : ℝ≥0 := ⟨H, hH⟩
  let β : ℝ≥0 := ⟨α, hα.le⟩
  have h : HolderOnWith C β f s := by
    intro x hx y hy
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal (dist (f x) (f y)) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal (dist x y) ^ α
    rw [← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le]
    change ENNReal.ofReal (dist (f x) (f y)) ≤
      ENNReal.ofReal H * ENNReal.ofReal (dist x y ^ α)
    rw [← ENNReal.ofReal_mul hH]
    exact ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using hh x hx y hy)
  exact h.continuousOn hα

/-- Componentwise Hölder coefficients and the specified ellipticity bound
give exactly the upstream maximum principle's coefficient hypotheses. -/
lemma ellipticCoefficients_of_holder {n : ℕ} {α ell : ℝ} (hα : 0 < α)
    (hell : 0 < ell) {Ω : Domain n} {s : Set (Space n)}
    (hΩs : (Ω : Set (Space n)) ⊆ s)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c : Space n → ℝ}
    (he : UniformlyEllipticOn ell a s) (hh : CoefficientsHolderOn α a b c s) :
    EllipticCoefficients Ω a b c := by
  refine ⟨?_, ?_, (continuousOn_of_isHolderOn hα hh.2.2).mono hΩs,
    fun x hx => he.1 x (hΩs hx), ell, hell, fun x hx => he.2 x (hΩs hx)⟩
  · exact (continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      continuousOn_of_isHolderOn hα (hh.1 i j)).mono hΩs
  · have hb : ContinuousOn (fun x => WithLp.ofLp (b x)) s :=
      continuousOn_pi.mpr fun i => continuousOn_of_isHolderOn hα (hh.2.1 i)
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp_continuousOn hb).mono hΩs

/-- Comparison applies on the ball, including the one-dimensional interval,
and continuity then propagates the inequality to its closed ball. -/
lemma comparison_on_closedBall {n : ℕ} (hn : 1 ≤ n)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c u v : Space n → ℝ}
    (hcoeff : EllipticCoefficients (ballDomain z r) a b c)
    (hc : ∀ x ∈ ball z r, c x ≤ 0)
    (hu : ContDiffOn ℝ 2 u (ball z r)) (hucl : ContinuousOn u (closedBall z r))
    (hv : ContDiffOn ℝ 2 v (ball z r)) (hvcl : ContinuousOn v (closedBall z r))
    (hL : ∀ x ∈ ball z r, nondivergenceOperator a b c v x ≤
      nondivergenceOperator a b c u x)
    (hboundary : ∀ x ∈ sphere z r, u x ≤ v x) :
    ∀ x ∈ closedBall z r, u x ≤ v x := by
  have hcl : closure (ball z r) = closedBall z r := closure_ball z hr.ne'
  have hfront : frontier (ball z r) = sphere z r := frontier_ball z hr.ne'
  have hi : ∀ x ∈ ball z r, u x ≤ v x :=
    P201.Elliptic.comparison n hn (ballDomain z r) isBounded_ball
      (convex_ball z r).isPreconnected a b c u v hcoeff hc hu
      (hcl.symm ▸ hucl) hv (hcl.symm ▸ hvcl) hL (hfront.symm ▸ hboundary)
  intro x hx
  exact le_on_closure hi (hcl.symm ▸ hucl) (hcl.symm ▸ hvcl) (hcl.symm ▸ hx)

/-- Uniqueness for the exact continuous-data solution predicate. Its proof
uses only classical comparison; no a priori Schauder premise is needed. -/
lemma ball_solution_unique {n : ℕ} (hn : 1 ≤ n)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c f : Space n → ℝ}
    {g : C(sphere z r, ℝ)} {u v : Space n → ℝ}
    (hcoeff : EllipticCoefficients (ballDomain z r) a b c)
    (hc : ∀ x ∈ ball z r, c x ≤ 0)
    (hu : IsBallSolution a b c f z r g u)
    (hv : IsBallSolution a b c f z r g v) : EqOn u v (closedBall z r) := by
  have huv := comparison_on_closedBall hn hr hcoeff hc hu.1 hu.2.1 hv.1 hv.2.1
    (fun x hx => by rw [hu.2.2.1 x hx, hv.2.2.1 x hx])
    (fun x hx => by rw [hu.2.2.2 ⟨x, hx⟩, hv.2.2.2 ⟨x, hx⟩])
  have hvu := comparison_on_closedBall hn hr hcoeff hc hv.1 hv.2.1 hu.1 hu.2.1
    (fun x hx => by rw [hu.2.2.1 x hx, hv.2.2.1 x hx])
    (fun x hx => by rw [hu.2.2.2 ⟨x, hx⟩, hv.2.2.2 ⟨x, hx⟩])
  exact fun x hx => le_antisymm (huv x hx) (hvu x hx)

/-- One-sided stability for two solutions of the same equation. The maximum
principle permits any nonnegative boundary bound, even when c is nonzero. -/
lemma difference_le_on_closedBall {n : ℕ} (hn : 1 ≤ n)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c u v : Space n → ℝ}
    (hcoeff : EllipticCoefficients (ballDomain z r) a b c)
    (hc : ∀ x ∈ ball z r, c x ≤ 0)
    (hu : ContDiffOn ℝ 2 u (ball z r)) (hucl : ContinuousOn u (closedBall z r))
    (hv : ContDiffOn ℝ 2 v (ball z r)) (hvcl : ContinuousOn v (closedBall z r))
    (hL : ∀ x ∈ ball z r, nondivergenceOperator a b c u x =
      nondivergenceOperator a b c v x)
    {M : ℝ} (hM : 0 ≤ M) (hboundary : ∀ x ∈ sphere z r, u x - v x ≤ M) :
    ∀ x ∈ closedBall z r, u x - v x ≤ M := by
  have hcl : closure (ball z r) = closedBall z r := closure_ball z hr.ne'
  have hfront : frontier (ball z r) = sphere z r := frontier_ball z hr.ne'
  have hLdiff : ∀ x ∈ ball z r,
      0 ≤ nondivergenceOperator a b c (fun y => u y - v y) x := by
    intro x hx
    have hd := P201.Elliptic.nondivergenceOperator_mul_sub a b c
      (Ω := ballDomain z r) hu hv 1 hx
    simp only [one_mul] at hd
    rw [hd, hL x hx, sub_self]
  have hi := P201.Elliptic.weakMaximumBoundaryBound hn
    (Ω := ballDomain z r) isBounded_ball (convex_ball z r).isPreconnected
    hcoeff hc (hu.sub hv) (hcl.symm ▸ hucl.sub hvcl) hLdiff hM
    (hfront.symm ▸ hboundary)
  intro x hx
  exact le_on_closure hi (hcl.symm ▸ hucl.sub hvcl) continuousOn_const (hcl.symm ▸ hx)

/-- The closed-ball solution is a contraction with respect to the uniform
norm of its continuous boundary datum when the source is fixed. This gives
the uniform Cauchy estimate needed to pass from smooth to continuous data. -/
lemma ball_solution_boundary_stability {n : ℕ} (hn : 1 ≤ n)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c f : Space n → ℝ}
    {g h : C(sphere z r, ℝ)} {u v : Space n → ℝ}
    (hcoeff : EllipticCoefficients (ballDomain z r) a b c)
    (hc : ∀ x ∈ ball z r, c x ≤ 0)
    (hu : IsBallSolution a b c f z r g u)
    (hv : IsBallSolution a b c f z r h v) :
    ∀ x ∈ closedBall z r, ‖u x - v x‖ ≤ ‖g - h‖ := by
  have hb : ∀ x ∈ sphere z r, ‖u x - v x‖ ≤ ‖g - h‖ := by
    intro x hx
    rw [hu.2.2.2 ⟨x, hx⟩, hv.2.2.2 ⟨x, hx⟩]
    exact (g - h).norm_coe_le_norm ⟨x, hx⟩
  have hL : ∀ x ∈ ball z r, nondivergenceOperator a b c u x =
      nondivergenceOperator a b c v x := by
    intro x hx
    rw [hu.2.2.1 x hx, hv.2.2.1 x hx]
  have hupper := difference_le_on_closedBall hn hr hcoeff hc hu.1 hu.2.1 hv.1 hv.2.1
    hL (norm_nonneg (g - h)) (fun x hx => (le_abs_self _).trans (hb x hx))
  have hlower := difference_le_on_closedBall hn hr hcoeff hc hv.1 hv.2.1 hu.1 hu.2.1
    (fun x hx => (hL x hx).symm) (norm_nonneg (g - h)) (fun x hx => by
      have hbx := (abs_le.mp (hb x hx)).1
      linarith)
  intro x hx
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hlower x hx], hupper x hx⟩

/-- Uniqueness under exactly the Hölder/ellipticity hypotheses used by the
continuous-data existence statement, without assuming an existence theorem. -/
lemma ball_solution_unique_of_holder {n : ℕ} (hn : 1 ≤ n)
    {α : ℝ} (hα : 0 < α) {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c f : Space n → ℝ}
    (he : ∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (closedBall z r))
    (hh : CoefficientsHolderOn α a b c (closedBall z r))
    (hc : ∀ x ∈ closedBall z r, c x ≤ 0)
    {g : C(sphere z r, ℝ)} {u v : Space n → ℝ}
    (hu : IsBallSolution a b c f z r g u)
    (hv : IsBallSolution a b c f z r g v) : EqOn u v (closedBall z r) := by
  obtain ⟨ell, hell, he⟩ := he
  exact ball_solution_unique hn hr
    (ellipticCoefficients_of_holder hα hell (Ω := ballDomain z r)
      ball_subset_closedBall he hh)
    (fun x hx => hc x (ball_subset_closedBall hx)) hu hv

/-- The global Hölder solution class also has uniqueness; one-sided
regularity on the closed ball supplies both interior C² and continuity. -/
lemma lifted_ball_solution_unique {n : ℕ} (hn : 1 ≤ n)
    {α : ℝ} (hα : 0 < α) {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c f G : Space n → ℝ}
    (he : ∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (closedBall z r))
    (hh : CoefficientsHolderOn α a b c (closedBall z r))
    (hc : ∀ x ∈ closedBall z r, c x ≤ 0)
    {u v : Space n → ℝ}
    (hu : IsLiftedBallSolution α a b c f G z r u)
    (hv : IsLiftedBallSolution α a b c f G z r v) : EqOn u v (closedBall z r) := by
  obtain ⟨ell, hell, he⟩ := he
  have hcoeff := ellipticCoefficients_of_holder hα hell (Ω := ballDomain z r)
    ball_subset_closedBall he hh
  have hc' : ∀ x ∈ ball z r, c x ≤ 0 :=
    fun x hx => hc x (ball_subset_closedBall hx)
  have hu' := hu.1.1.mono (ball_subset_closedBall (x := z) (ε := r))
  have hv' := hv.1.1.mono (ball_subset_closedBall (x := z) (ε := r))
  have huv := comparison_on_closedBall hn hr hcoeff hc' hu' hu.1.1.continuousOn
    hv' hv.1.1.continuousOn
    (fun x hx => by rw [hu.2.1 x hx, hv.2.1 x hx])
    (fun x hx => by rw [hu.2.2 x hx, hv.2.2 x hx])
  have hvu := comparison_on_closedBall hn hr hcoeff hc' hv' hv.1.1.continuousOn
    hu' hu.1.1.continuousOn
    (fun x hx => by rw [hu.2.1 x hx, hv.2.1 x hx])
    (fun x hx => by rw [hu.2.2 x hx, hv.2.2 x hx])
  exact fun x hx => le_antisymm (huv x hx) (hvu x hx)

/-- A slab barrier. Its sign is chosen for the positive-principal-part
operator: the operator applied to this function is uniformly negative. -/
def exponentialBarrier {n : ℕ} (i : Fin n) (d k : ℝ) (x : Space n) : ℝ :=
  Real.exp (k * d) - Real.exp (k * x i)

lemma exponentialBarrier_contDiff {n : ℕ} (i : Fin n) (d k : ℝ) :
    ContDiff ℝ ⊤ (exponentialBarrier i d k) := by
  exact contDiff_const.sub (contDiff_const.mul (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff).exp

lemma coordinate_exponential_hasFDerivAt {n : ℕ} (i : Fin n) (k : ℝ) (x : Space n) :
    HasFDerivAt (fun y : Space n => Real.exp (k * y i))
      (Real.exp (k * x i) • (k • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i)) x := by
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.const_mul k).exp

lemma exponentialBarrier_firstPartial {n : ℕ} (i j : Fin n) (d k : ℝ) (x : Space n) :
    firstPartial (exponentialBarrier i d k) j x =
      -(Real.exp (k * x i) * k * (if i = j then 1 else 0)) := by
  change fderiv ℝ (fun y : Space n => Real.exp (k * d) - Real.exp (k * y i)) x
    (coordinate n j) = _
  rw [fderiv_const_sub, (coordinate_exponential_hasFDerivAt i k x).fderiv]
  simp [coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply,
    PiLp.single_apply, PiLp.proj_apply]

lemma exponentialBarrier_secondPartial {n : ℕ} (i j l : Fin n) (d k : ℝ) (x : Space n) :
    secondPartial (exponentialBarrier i d k) j l x =
      -(Real.exp (k * x i) * k ^ 2 *
        (if i = j then 1 else 0) * (if i = l then 1 else 0)) := by
  have he : firstPartial (exponentialBarrier i d k) l =
      fun y => -(Real.exp (k * y i) * k * (if i = l then 1 else 0)) :=
    funext (exponentialBarrier_firstPartial i l d k)
  rw [secondPartial, he, firstPartial]
  have hh := (((coordinate_exponential_hasFDerivAt i k x).mul_const k).mul_const
    (if i = l then (1 : ℝ) else 0)).neg
  change fderiv ℝ (-(fun y : Space n => Real.exp (k * y i) * k *
    (if i = l then (1 : ℝ) else 0))) x (coordinate n j) = _
  rw [hh.fderiv]
  simp only [neg_apply, smul_apply,
    smul_eq_mul, PiLp.proj_apply, coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]
  split_ifs <;> ring

lemma exponentialBarrier_operator {n : ℕ} (i : Fin n) (d k : ℝ)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ) (x : Space n) :
    nondivergenceOperator a b c (exponentialBarrier i d k) x =
      -Real.exp (k * x i) * (a x i i * k ^ 2 + b x i * k) +
        c x * exponentialBarrier i d k x := by
  simp only [nondivergenceOperator, exponentialBarrier_firstPartial,
    exponentialBarrier_secondPartial]
  simp only [mul_ite, mul_zero, mul_one, neg_ite, neg_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- Ellipticity controls each diagonal entry by testing on a unit coordinate. -/
lemma diagonal_lower_bound {n : ℕ} {ell : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {s : Set (Space n)}
    (he : UniformlyEllipticOn ell a s) {x : Space n} (hx : x ∈ s) (i : Fin n) :
    ell ≤ a x i i := by
  have h := he.2 x hx (coordinate n i)
  simpa [coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply,
    PiLp.single_apply, PiLp.norm_single, mul_ite, Finset.sum_ite_eq,
    mul_zero, mul_one] using h

/-- On a symmetric slab, the exponential barrier has a uniform operator
bound. Only a lower principal bound, one drift bound, and c ≤ 0 enter. -/
lemma exponentialBarrier_operator_le {n : ℕ} (i : Fin n)
    {d k ell B : ℝ} (hk : 0 ≤ k) {x : Space n}
    (hslab : -d ≤ x i ∧ x i ≤ d)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ)
    (ha : ell ≤ a x i i) (hb : -B ≤ b x i) (hc : c x ≤ 0)
    (hq : 0 ≤ ell * k ^ 2 - B * k) :
    nondivergenceOperator a b c (exponentialBarrier i d k) x ≤
      -((ell * k ^ 2 - B * k) * Real.exp (-k * d)) := by
  have hψ : 0 ≤ exponentialBarrier i d k x := by
    apply sub_nonneg.mpr
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hslab.2 hk)
  have hE : Real.exp (-k * d) ≤ Real.exp (k * x i) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hslab.1 hk]
  have hq' : ell * k ^ 2 - B * k ≤ a x i i * k ^ 2 + b x i * k := by
    nlinarith [mul_le_mul_of_nonneg_right ha (sq_nonneg k),
      mul_le_mul_of_nonneg_right hb hk]
  rw [exponentialBarrier_operator]
  have h1 := mul_le_mul_of_nonneg_left hq' (Real.exp_nonneg (k * x i))
  have h2 := mul_le_mul_of_nonneg_left hE hq
  have h3 := mul_nonpos_of_nonpos_of_nonneg hc hψ
  nlinarith

/-- A single smooth supersolution works for every coefficient field with
these bounds. In particular the constant is chosen before the operator. -/
lemma exists_uniform_ball_barrier {n : ℕ} (hn : 1 ≤ n)
    (z : Space n) {r : ℝ} (_hr : 0 < r) {ell B : ℝ}
    (hell : 0 < ell) (_hB : 0 ≤ B) :
    ∃ (ψ : Space n → ℝ) (δ M : ℝ),
      0 < δ ∧ 0 < M ∧ ContDiff ℝ ⊤ ψ ∧
      (∀ x ∈ closedBall z r, 0 ≤ ψ x ∧ ψ x ≤ M) ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ),
        UniformlyEllipticOn ell a (closedBall z r) →
        (∀ x ∈ closedBall z r, ∀ i : Fin n, ‖b x i‖ ≤ B) →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        ∀ x ∈ ball z r, nondivergenceOperator a b c ψ x ≤ -δ := by
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨k, hk, hq⟩ := P201.Elliptic.exists_positive_quadratic_parameter
    (A := ell) (B := B) (C := 0) hell (le_refl 0)
  simp only [sub_zero] at hq
  let d : ℝ := ‖z‖ + r
  have hslab : ∀ x ∈ closedBall z r, -d ≤ x i ∧ x i ≤ d := by
    intro x hx
    have hxnorm : ‖x‖ ≤ d := by
      calc
        ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by simpa using norm_add_le (x - z) z
        _ ≤ r + ‖z‖ := add_le_add (mem_closedBall_iff_norm.mp hx) le_rfl
        _ = d := add_comm _ _
    have hxi : ‖x i‖ ≤ d := (PiLp.norm_apply_le x i).trans hxnorm
    exact abs_le.mp (Real.norm_eq_abs _ ▸ hxi)
  refine ⟨exponentialBarrier i d k, (ell * k ^ 2 - B * k) * Real.exp (-k * d),
    Real.exp (k * d), mul_pos hq (Real.exp_pos _), Real.exp_pos _,
    exponentialBarrier_contDiff i d k, ?_, ?_⟩
  · intro x hx
    refine ⟨sub_nonneg.mpr (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hslab x hx).2 hk.le)), ?_⟩
    exact sub_le_self _ (Real.exp_nonneg _)
  · intro a b c he hb hc x hx
    have hx' := ball_subset_closedBall hx
    exact exponentialBarrier_operator_le i hk.le (hslab x hx') a b c
      (diagonal_lower_bound he hx' i) (abs_le.mp (hb x hx' i)).1 (hc x hx') hq.le

/-- Comparing with a multiple of a strict supersolution bounds a classical
solution by its boundary bound and the size of its source. -/
lemma le_boundary_add_barrier {n : ℕ} (hn : 1 ≤ n)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c u ψ : Space n → ℝ}
    (hcoeff : EllipticCoefficients (ballDomain z r) a b c)
    (hc : ∀ x ∈ ball z r, c x ≤ 0)
    (hu : ContDiffOn ℝ 2 u (ball z r)) (hucl : ContinuousOn u (closedBall z r))
    (hψ : ContDiff ℝ ⊤ ψ)
    {δ F A : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hψ0 : ∀ x ∈ closedBall z r, 0 ≤ ψ x)
    (hLψ : ∀ x ∈ ball z r, nondivergenceOperator a b c ψ x ≤ -δ)
    (hLu : ∀ x ∈ ball z r, -F ≤ nondivergenceOperator a b c u x)
    (hboundary : ∀ x ∈ sphere z r, u x ≤ A) :
    ∀ x ∈ closedBall z r, u x ≤ A + (F / δ) * ψ x := by
  have ht : 0 ≤ F / δ := div_nonneg hF hδ.le
  have hψ' : ContDiffOn ℝ 2 ψ (ball z r) := (hψ.of_le (by simp)).contDiffOn
  have hdiff : ContDiffOn ℝ 2 (fun y => u y - (F / δ) * ψ y) (ball z r) :=
    hu.sub (contDiffOn_const.mul hψ')
  have hdiffcl : ContinuousOn (fun y => u y - (F / δ) * ψ y) (closedBall z r) :=
    hucl.sub (hψ.continuous.continuousOn.const_mul (F / δ))
  have hLdiff : ∀ x ∈ ball z r,
      0 ≤ nondivergenceOperator a b c (fun y => u y - (F / δ) * ψ y) x := by
    intro x hx
    have hd := P201.Elliptic.nondivergenceOperator_mul_sub a b c
      (Ω := ballDomain z r) hψ' hu (F / δ) hx
    have hsign := mul_le_mul_of_nonneg_left (hLψ x hx) ht
    have hprod : (F / δ) * δ = F := div_mul_cancel₀ F hδ.ne'
    have he := P201.Elliptic.nondivergenceOperator_const_sub a b c
      (fun y => (F / δ) * ψ y - u y) 0 x
    simp only [mul_zero, zero_sub, neg_sub] at he
    rw [he, hd]
    nlinarith [hLu x hx]
  have hcl : closure (ball z r) = closedBall z r := closure_ball z hr.ne'
  have hfront : frontier (ball z r) = sphere z r := frontier_ball z hr.ne'
  have hi := P201.Elliptic.weakMaximumBoundaryBound hn
    (Ω := ballDomain z r) isBounded_ball (convex_ball z r).isPreconnected
    hcoeff hc hdiff (hcl.symm ▸ hdiffcl) hLdiff hA
    (hfront.symm ▸ fun x hx => (sub_le_self _
      (mul_nonneg ht (hψ0 x (sphere_subset_closedBall hx)))).trans (hboundary x hx))
  intro x hx
  have := le_on_closure hi (hcl.symm ▸ hdiffcl) continuousOn_const (hcl.symm ▸ hx)
  linarith

/-- Uniform C⁰ estimate on a ball. Neither existence nor a Schauder estimate
is assumed. The bound applies to every classical interior solution continuous
on the closed ball, in all positive dimensions. -/
lemma uniform_ball_supremum_estimate {n : ℕ} (hn : 1 ≤ n)
    (z : Space n) {r : ℝ} (hr : 0 < r) {ell B : ℝ}
    (hell : 0 < ell) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c u : Space n → ℝ),
        EllipticCoefficients (ballDomain z r) a b c →
        UniformlyEllipticOn ell a (closedBall z r) →
        (∀ x ∈ closedBall z r, ∀ i : Fin n, ‖b x i‖ ≤ B) →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        ContDiffOn ℝ 2 u (ball z r) → ContinuousOn u (closedBall z r) →
        ∀ F A : ℝ, 0 ≤ F → 0 ≤ A →
          (∀ x ∈ ball z r, ‖nondivergenceOperator a b c u x‖ ≤ F) →
          (∀ x ∈ sphere z r, ‖u x‖ ≤ A) →
          ∀ x ∈ closedBall z r, ‖u x‖ ≤ A + C * F := by
  obtain ⟨ψ, δ, M, hδ, hM, hψ, hψbound, hLψ⟩ :=
    exists_uniform_ball_barrier hn z hr hell hB
  refine ⟨M / δ, div_pos hM hδ, ?_⟩
  intro a b c u hcoeff he hb hc hu hucl F A hF hA hLu hboundary
  have hc' : ∀ x ∈ ball z r, c x ≤ 0 := fun x hx => hc x (ball_subset_closedBall hx)
  have hupp := le_boundary_add_barrier hn hr hcoeff hc' hu hucl hψ hδ hF hA
    (fun x hx => (hψbound x hx).1) (hLψ a b c he hb hc)
    (fun x hx => (abs_le.mp (hLu x hx)).1)
    (fun x hx => (le_abs_self _).trans (hboundary x hx))
  have hlo := le_boundary_add_barrier hn hr hcoeff hc' hu.neg hucl.neg hψ hδ hF hA
    (fun x hx => (hψbound x hx).1) (hLψ a b c he hb hc)
    (fun x hx => by
      have hd := P201.Elliptic.nondivergenceOperator_const_sub a b c u 0 x
      simp only [mul_zero, zero_sub] at hd
      rw [hd]
      have hh := (abs_le.mp (hLu x hx)).2
      linarith)
    (fun x hx => (neg_le_abs _).trans (hboundary x hx))
  intro x hx
  have hbound : (F / δ) * ψ x ≤ (M / δ) * F := by
    calc
      (F / δ) * ψ x ≤ (F / δ) * M :=
        mul_le_mul_of_nonneg_left (hψbound x hx).2 (div_nonneg hF hδ.le)
      _ = (M / δ) * F := by ring
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hlo x hx], by linarith [hupp x hx]⟩

private lemma nonneg_real_supremum {s : Set ℝ} (h : ∀ x ∈ s, 0 ≤ x) :
    0 ≤ sSup s := by
  by_cases hb : BddAbove s
  · rcases s.eq_empty_or_nonempty with he | he
    · simp [he]
    · obtain ⟨x, hx⟩ := he
      exact (h x hx).trans (le_csSup hb hx)
  · rw [Real.sSup_of_not_bddAbove hb]

lemma holderNormOn_nonneg {n : ℕ} (α : ℝ) (f : Space n → ℝ) (s : Set (Space n)) :
    0 ≤ holderNormOn α f s := by
  apply add_nonneg
  · exact nonneg_real_supremum (by rintro t ⟨x, hx, rfl⟩; exact norm_nonneg _)
  · exact nonneg_real_supremum (by
      rintro t ⟨x, hx, y, hy, hxy, rfl⟩
      exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _))

lemma norm_le_holderNormOn {n : ℕ} {α : ℝ} {f : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) {x : Space n} (hx : x ∈ s) :
    ‖f x‖ ≤ holderNormOn α f s := by
  obtain ⟨M, H, hM, hH, hb, hh⟩ := hf
  have hsup : ‖f x‖ ≤ sSup {t : ℝ | ∃ y ∈ s, t = ‖f y‖} :=
    le_csSup ⟨M, by rintro t ⟨y, hy, rfl⟩; exact hb y hy⟩ ⟨x, hx, rfl⟩
  have hseminorm : 0 ≤ sSup {t : ℝ | ∃ y ∈ s, ∃ z ∈ s,
      y ≠ z ∧ t = ‖f y - f z‖ / dist y z ^ α} :=
    nonneg_real_supremum (by
      rintro t ⟨y, hy, z, hz, hyz, rfl⟩
      exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _))
  exact hsup.trans (le_add_of_nonneg_right hseminorm)

/-- The canonical coefficient norm supplies the drift bound used by the
uniform barrier. Thus no additional bound is needed in the target interface. -/
lemma drift_bound_of_coefficientNorm {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c : Space n → ℝ} {s : Set (Space n)}
    (hh : CoefficientsHolderOn α a b c s) (hK : coefficientNormOn α a b c s ≤ K)
    {x : Space n} (hx : x ∈ s) (i : Fin n) : ‖b x i‖ ≤ K := by
  have hnorm := norm_le_holderNormOn (hh.2.1 i) hx
  have hsum : holderNormOn α (fun y => b y i) s ≤
      ∑ j : Fin n, holderNormOn α (fun y => b y j) s :=
    Finset.single_le_sum (fun j _ => holderNormOn_nonneg α (fun y => b y j) s)
      (Finset.mem_univ i)
  have ha : 0 ≤ ∑ j : Fin n, ∑ l : Fin n, holderNormOn α (fun y => a y j l) s :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => holderNormOn_nonneg _ _ _
  have hc := holderNormOn_nonneg α c s
  unfold coefficientNormOn at hK
  linarith

/-- The C⁰ bound uses exactly the target's coefficient regularity, ellipticity
and coefficient norm bound. Its constant precedes all coefficient fields. -/
lemma uniform_ball_supremum_estimate_of_holder {n : ℕ} (hn : 1 ≤ n)
    {α : ℝ} (hα : 0 < α) (z : Space n) {r : ℝ} (hr : 0 < r)
    {ell K : ℝ} (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c u : Space n → ℝ),
        UniformlyEllipticOn ell a (closedBall z r) →
        CoefficientsHolderOn α a b c (closedBall z r) →
        coefficientNormOn α a b c (closedBall z r) ≤ K →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        ContDiffOn ℝ 2 u (ball z r) → ContinuousOn u (closedBall z r) →
        ∀ F A : ℝ, 0 ≤ F → 0 ≤ A →
          (∀ x ∈ ball z r, ‖nondivergenceOperator a b c u x‖ ≤ F) →
          (∀ x ∈ sphere z r, ‖u x‖ ≤ A) →
          ∀ x ∈ closedBall z r, ‖u x‖ ≤ A + C * F := by
  obtain ⟨C, hC, hestimate⟩ := uniform_ball_supremum_estimate hn z hr hell hK
  refine ⟨C, hC, ?_⟩
  intro a b c u he hh hnorm hc hu hucl
  exact hestimate a b c u
    (ellipticCoefficients_of_holder hα hell (Ω := ballDomain z r)
      ball_subset_closedBall he hh) he
    (fun x hx i => drift_bound_of_coefficientNorm hh hnorm hx i) hc hu hucl

/-- Real supremum norms are nonnegative, including empty observation sets. -/
lemma supNormOn_nonneg {n : ℕ} (f : Space n → ℝ) (s : Set (Space n)) :
    0 ≤ supNormOn f s :=
  nonneg_real_supremum (by rintro t ⟨x, hx, rfl⟩; exact norm_nonneg _)

lemma norm_le_supNormOn {n : ℕ} {f : Space n → ℝ} {s : Set (Space n)}
    (hf : IsBoundedOn f s) {x : Space n} (hx : x ∈ s) : ‖f x‖ ≤ supNormOn f s := by
  obtain ⟨M, hM, hb⟩ := hf
  exact le_csSup ⟨M, by rintro t ⟨y, hy, rfl⟩; exact hb y hy⟩ ⟨x, hx, rfl⟩

/-- The norm in the independent target controls the value on the boundary
as well as in the interior; no extension outside the observation set enters. -/
lemma norm_le_c2HolderUpToNormOn {n : ℕ} {α : ℝ} {G : Space n → ℝ}
    {s : Set (Space n)} (hG : IsC2HolderUpToOn α G s)
    {x : Space n} (hx : x ∈ s) : ‖G x‖ ≤ c2HolderUpToNormOn α G s := by
  have h0 := norm_le_supNormOn hG.2.1 hx
  have h1 : 0 ≤ ∑ i : Fin n, supNormOn (firstPartialWithin G s i) s :=
    Finset.sum_nonneg fun i _ => supNormOn_nonneg _ _
  have h2 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      supNormOn (secondPartialWithin G s i j) s :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => supNormOn_nonneg _ _
  have h3 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      holderSeminormOn α (secondPartialWithin G s i j) s := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact nonneg_real_supremum (by
      rintro t ⟨y, hy, z, hz, hyz, rfl⟩
      exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _))
  simp only [c2HolderUpToNormOn, scaledWithinSolutionNorm, one_mul, one_pow,
    Real.one_rpow]
  linarith

/-- The supremum term in the conditional Schauder estimate is controlled by
the known source and lift, uniformly over the prescribed coefficient class.
This is an a priori result for any existing lifted solution. -/
lemma lifted_ball_solution_supremum_estimate {n : ℕ} (hn : 1 ≤ n)
    {α : ℝ} (hα : 0 < α) (z : Space n) {r : ℝ} (hr : 0 < r)
    {ell K : ℝ} (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c f G u : Space n → ℝ),
        UniformlyEllipticOn ell a (closedBall z r) →
        CoefficientsHolderOn α a b c (closedBall z r) →
        coefficientNormOn α a b c (closedBall z r) ≤ K →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        IsHolderOn α f (closedBall z r) →
        IsC2HolderUpToOn α G (closedBall z r) →
        IsLiftedBallSolution α a b c f G z r u →
        supNormOn u (closedBall z r) ≤
          C * (holderNormOn α f (closedBall z r) + c2HolderUpToNormOn α G (closedBall z r)) := by
  obtain ⟨C, hC, hestimate⟩ := uniform_ball_supremum_estimate_of_holder hn hα z hr hell hK
  refine ⟨max C 1, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro a b c f G u he hh hnorm hc hf hG hu
  have hF := holderNormOn_nonneg α f (closedBall z r)
  have hGnorm : 0 ≤ c2HolderUpToNormOn α G (closedBall z r) :=
    (norm_nonneg (G z)).trans (norm_le_c2HolderUpToNormOn hG (mem_closedBall_self hr.le))
  have hb := hestimate a b c u he hh hnorm hc
    (hu.1.1.mono ball_subset_closedBall) hu.1.1.continuousOn
    (holderNormOn α f (closedBall z r)) (c2HolderUpToNormOn α G (closedBall z r)) hF hGnorm
    (fun x hx => by rw [hu.2.1 x hx]; exact norm_le_holderNormOn hf (ball_subset_closedBall hx))
    (fun x hx => by rw [hu.2.2 x hx]; exact norm_le_c2HolderUpToNormOn hG (sphere_subset_closedBall hx))
  apply csSup_le
  · exact ⟨‖u z‖, z, mem_closedBall_self hr.le, rfl⟩
  · rintro t ⟨x, hx, rfl⟩
    calc
      ‖u x‖ ≤ c2HolderUpToNormOn α G (closedBall z r) + C * holderNormOn α f (closedBall z r) := hb x hx
      _ ≤ (max C 1) * c2HolderUpToNormOn α G (closedBall z r) +
          (max C 1) * holderNormOn α f (closedBall z r) :=
        add_le_add (le_mul_of_one_le_left hGnorm (le_max_right _ _))
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hF)
      _ = _ := by ring

/-- Principal coefficients on the source's path from Δ to L. -/
def pathPrincipal {n : ℕ} (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (x : Space n) (i j : Fin n) : ℝ :=
  (1 - t) * (if i = j then 1 else 0) + t * a x i j

lemma pathPrincipal_quadratic_form {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x ξ : Space n) :
    (∑ i : Fin n, ∑ j : Fin n, pathPrincipal a t x i j * ξ i * ξ j) =
      (1 - t) * ‖ξ‖ ^ 2 + t * (∑ i : Fin n, ∑ j : Fin n, a x i j * ξ i * ξ j) := by
  simp only [pathPrincipal, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  · simp only [mul_assoc, ← Finset.mul_sum]

lemma pathPrincipal_uniformlyEllipticOn {n : ℕ} {ell t : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {s : Set (Space n)}
    (he : UniformlyEllipticOn ell a s) (ht : t ∈ Icc (0 : ℝ) 1) :
    UniformlyEllipticOn (min ell 1) (pathPrincipal a t) s := by
  refine ⟨?_, ?_⟩
  · intro x hx i j
    simp only [pathPrincipal, he.1 x hx i j, eq_comm (a := i) (b := j)]
  · intro x hx ξ
    rw [pathPrincipal_quadratic_form]
    have hmin1 := mul_le_mul_of_nonneg_right (min_le_right ell 1) (sq_nonneg ‖ξ‖)
    have hminell := mul_le_mul_of_nonneg_right (min_le_left ell 1) (sq_nonneg ‖ξ‖)
    have hfirst := mul_le_mul_of_nonneg_left hmin1 (sub_nonneg.mpr ht.2)
    have hsecond := mul_le_mul_of_nonneg_left (hminell.trans (he.2 x hx ξ)) ht.1
    nlinarith

/-- The path has the same continuous coefficient hypotheses required by
comparison, with the common ellipticity lower bound min(ell,1). -/
lemma path_ellipticCoefficients {n : ℕ} {α ell t : ℝ}
    (hα : 0 < α) (hell : 0 < ell) {Ω : Domain n} {s : Set (Space n)}
    (hΩ : (Ω : Set (Space n)) ⊆ s)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c : Space n → ℝ}
    (he : UniformlyEllipticOn ell a s) (hh : CoefficientsHolderOn α a b c s)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    EllipticCoefficients Ω (pathPrincipal a t) (fun x => t • b x) (fun x => t * c x) := by
  have he' := pathPrincipal_uniformlyEllipticOn he ht
  have hcoeff := ellipticCoefficients_of_holder hα hell hΩ he hh
  refine ⟨?_, ?_, ?_, fun x hx => he'.1 x (hΩ hx), min ell 1,
    lt_min hell zero_lt_one, fun x hx => he'.2 x (hΩ hx)⟩
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact continuousOn_const.add (continuousOn_const.mul
      ((continuousOn_of_isHolderOn hα (hh.1 i j)).mono hΩ))
  · exact (continuousOn_const : ContinuousOn (fun _ : Space n => t) (Ω : Set (Space n))).smul
      hcoeff.2.1
  · exact continuousOn_const.mul hcoeff.2.2.1

/-- Repeated coordinates in the canonical multi-index are exactly the
iterated classical partials used by the nondivergence operator. -/
lemma secondPartial_diagonal_eq_multiPartial {n : ℕ} (u : Space n → ℝ)
    (i : Fin n) (x : Space n) : secondPartial u i i x = multiPartial u {i, i} x := by
  have hs : ({i, i} : MultiIndex n).sort (· ≤ ·) = [i, i] := by
    change (i ::ₘ ({i} : Multiset (Fin n))).sort (· ≤ ·) = [i, i]
    rw [Multiset.sort_cons i ({i} : Multiset (Fin n)) (· ≤ ·) (by simp),
      Multiset.sort_singleton]
  change secondPartial u i i x = P102.U4.partialWord u (({i, i} : MultiIndex n).sort (· ≤ ·)) x
  rw [hs]
  rfl

/-- The coefficient path represents the actual path (1-t)Δ+tL with the
source's shared Laplacian, rather than a separately postulated operator. -/
lemma path_operator_identity {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ) (t : ℝ) (x : Space n) :
    nondivergenceOperator (pathPrincipal a t) (fun y => t • b y) (fun y => t * c y) u x =
      (1 - t) * laplacian u x + t * nondivergenceOperator a b c u x := by
  have hprincipal : (∑ i : Fin n, ∑ j : Fin n, pathPrincipal a t x i j * secondPartial u i j x) =
      (1 - t) * laplacian u x +
        t * (∑ i : Fin n, ∑ j : Fin n, a x i j * secondPartial u i j x) := by
    simp only [pathPrincipal, add_mul, Finset.sum_add_distrib]
    congr 1
    · simp only [mul_assoc, ← Finset.mul_sum]
      congr 1
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        secondPartial_diagonal_eq_multiPartial]
    · simp only [mul_assoc, ← Finset.mul_sum]
  have hfirst : (∑ i : Fin n, (t • b x) i * firstPartial u i x) =
      t * (∑ i : Fin n, b x i * firstPartial u i x) := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  change (∑ i : Fin n, ∑ j : Fin n, pathPrincipal a t x i j * secondPartial u i j x) +
    (∑ i : Fin n, (t • b x) i * firstPartial u i x) + t * c x * u x = _
  rw [hprincipal, hfirst]
  unfold nondivergenceOperator
  ring

/-- The C⁰ estimate is uniform on the complete continuity path, before
choosing t, the coefficients, or the solution. -/
lemma uniform_path_supremum_estimate {n : ℕ} (hn : 1 ≤ n)
    {α : ℝ} (hα : 0 < α) (z : Space n) {r : ℝ} (hr : 0 < r)
    {ell K : ℝ} (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ),
        UniformlyEllipticOn ell a (closedBall z r) →
        CoefficientsHolderOn α a b c (closedBall z r) →
        coefficientNormOn α a b c (closedBall z r) ≤ K →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Space n → ℝ,
          ContDiffOn ℝ 2 u (ball z r) → ContinuousOn u (closedBall z r) →
          ∀ F A : ℝ, 0 ≤ F → 0 ≤ A →
            (∀ x ∈ ball z r,
              ‖nondivergenceOperator (pathPrincipal a t) (fun y => t • b y) (fun y => t * c y) u x‖ ≤ F) →
            (∀ x ∈ sphere z r, ‖u x‖ ≤ A) →
            ∀ x ∈ closedBall z r, ‖u x‖ ≤ A + C * F := by
  obtain ⟨C, hC, hestimate⟩ := uniform_ball_supremum_estimate hn z hr
    (lt_min hell zero_lt_one) hK
  refine ⟨C, hC, ?_⟩
  intro a b c he hh hnorm hc t ht u hu hucl
  apply hestimate (pathPrincipal a t) (fun x => t • b x) (fun x => t * c x) u
    (path_ellipticCoefficients hα hell (Ω := ballDomain z r)
      ball_subset_closedBall he hh ht) (pathPrincipal_uniformlyEllipticOn he ht)
  · intro x hx i
    have hb := drift_bound_of_coefficientNorm hh hnorm hx i
    simp only [PiLp.smul_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left hb ht.1).trans
      (mul_le_of_le_one_left hK ht.2)
  · intro x hx
    exact mul_nonpos_of_nonneg_of_nonpos ht.1 (hc x hx)
  · exact hu
  · exact hucl

/-- Quantitative perturbation of an invertible operator. The Neumann series
is applied only to an actual continuous endomorphism of a Banach space. -/
lemma invertible_of_uniformly_bounded_inverse_nearby
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : E ≃L[ℝ] F) (T : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x : E, ‖x‖ ≤ C * ‖e x‖)
    (hnear : C * ‖(e : E →L[ℝ] F) - T‖ < 1) : T.IsInvertible := by
  have hinv : ‖(e.symm : F →L[ℝ] E)‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro y
    simpa using hbound (e.symm y)
  let Q : E →L[ℝ] E := (e.symm : F →L[ℝ] E).comp ((e : E →L[ℝ] F) - T)
  have hQ : ‖Q‖ < 1 :=
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))).trans_lt hnear
  have hbij : Function.Bijective (1 - Q : E →L[ℝ] E) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp (IsUnit.one_sub_of_norm_lt_one hQ)
  have heq : (e : E →L[ℝ] F).comp (1 - Q) = T := by
    ext x
    simp [Q]
  have hT : Function.Bijective T := by
    rw [← heq]
    exact e.bijective.comp hbij
  exact ⟨ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hT.1) (LinearMap.range_eq_top.mpr hT.2),
    ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- The open-and-closed step of the continuity method. Uniform a priori
bounds keep inverse norms bounded at closure points. No surjectivity is
assumed at those points. -/
lemma continuous_family_invertible_of_uniform_bound
    {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace J] [PreconnectedSpace J]
    (T : J → E →L[ℝ] F) (hT : Continuous T) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t : J, ∀ x : E, ‖x‖ ≤ C * ‖T t x‖)
    {t₀ : J} (hstart : (T t₀).IsInvertible) :
    ∀ t : J, (T t).IsInvertible := by
  let S : Set J := {t | (T t).IsInvertible}
  have hOpen : IsOpen S := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hT
  have hClosed : IsClosed S := by
    apply isClosed_of_closure_subset
    intro t ht
    have hε : 0 < 1 / (C + 1) := one_div_pos.mpr (by linarith)
    have hnb : T ⁻¹' ball (T t) (1 / (C + 1)) ∈ nhds t :=
      hT.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε)
    obtain ⟨s, hsnear, hsinv⟩ := mem_closure_iff_nhds.mp ht _ hnb
    obtain ⟨e, he⟩ := hsinv
    have hdist : ‖(e : E →L[ℝ] F) - T t‖ < 1 / (C + 1) := by
      simpa [he, dist_eq_norm] using hsnear
    apply invertible_of_uniformly_bounded_inverse_nearby e (T t) hC
      (fun x => by
        change ‖x‖ ≤ C * ‖(e : E →L[ℝ] F) x‖
        rw [he]
        exact hbound s x)
    have hmul := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1) :
      C ≤ C + 1) (norm_nonneg ((e : E →L[ℝ] F) - T t))
    have hdist' := (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hdist
    nlinarith
  have hAll : S = univ := IsClopen.eq_univ ⟨hClosed, hOpen⟩ ⟨t₀, hstart⟩
  intro t
  change t ∈ S
  rw [hAll]
  exact mem_univ t

/-- The Banach-space continuity theorem for the exact affine path used in
the source. The domain and codomain are actual Banach spaces and the estimate
is uniform on the whole closed parameter interval. -/
lemma affine_method_of_continuity
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L₀ L₁ : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : E,
      ‖x‖ ≤ C * ‖((1 - t) • L₀ + t • L₁) x‖)
    (hstart : Function.Surjective L₀) : Function.Bijective L₁ := by
  have hbound₀ : ∀ x : E, ‖x‖ ≤ C * ‖L₀ x‖ := by
    simpa using hbound 0 (by simp)
  have hinj : Function.Injective L₀ :=
    (L₀.antilipschitz_of_bound (K := ⟨C, hC⟩) hbound₀).injective
  let e₀ := ContinuousLinearEquiv.ofBijective L₀
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hstart)
  let T : Icc (0 : ℝ) 1 → E →L[ℝ] F := fun t => (1 - (t : ℝ)) • L₀ + (t : ℝ) • L₁
  have hT : Continuous T :=
    ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  let : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  have hinit : (T ⟨0, by simp⟩).IsInvertible := by
    refine ⟨e₀, ?_⟩
    simpa [T, e₀] using ContinuousLinearEquiv.coe_ofBijective L₀
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hstart)
  obtain ⟨e₁, he₁⟩ := continuous_family_invertible_of_uniform_bound T hT hC
    (fun t => hbound t t.property) hinit ⟨1, by simp⟩
  have he₁' : (e₁ : E →L[ℝ] F) = L₁ := by simpa [T] using he₁
  rw [← he₁']
  exact e₁.bijective


lemma isHolderOn_const {n : ℕ} (α : ℝ) (k : ℝ) (s : Set (Space n)) :
    IsHolderOn α (fun _ => k) s := by
  refine ⟨‖k‖, 0, norm_nonneg _, le_rfl, ?_, ?_⟩
  · intro x hx; exact le_rfl
  · intro x hx y hy; simp

lemma isHolderOn_add {n : ℕ} {α : ℝ} {f g : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) (hg : IsHolderOn α g s) :
    IsHolderOn α (fun x => f x + g x) s := by
  obtain ⟨Mf, Hf, hMf, hHf, hbf, hhf⟩ := hf
  obtain ⟨Mg, Hg, hMg, hHg, hbg, hhg⟩ := hg
  refine ⟨Mf + Mg, Hf + Hg, add_nonneg hMf hMg, add_nonneg hHf hHg, ?_, ?_⟩
  · intro x hx
    exact (norm_add_le _ _).trans (add_le_add (hbf x hx) (hbg x hx))
  · intro x hx y hy
    calc
      ‖f x + g x - (f y + g y)‖ = ‖(f x - f y) + (g x - g y)‖ := by congr 1; ring
      _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
      _ ≤ Hf * dist x y ^ α + Hg * dist x y ^ α := add_le_add (hhf x hx y hy) (hhg x hx y hy)
      _ = (Hf + Hg) * dist x y ^ α := by ring

lemma isHolderOn_const_mul {n : ℕ} {α : ℝ} {f : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) (k : ℝ) : IsHolderOn α (fun x => k * f x) s := by
  obtain ⟨M, H, hM, hH, hb, hh⟩ := hf
  refine ⟨‖k‖ * M, ‖k‖ * H, mul_nonneg (norm_nonneg _) hM,
    mul_nonneg (norm_nonneg _) hH, ?_, ?_⟩
  · intro x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg _)
  · intro x hx y hy
    rw [← mul_sub, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hh x hx y hy) (norm_nonneg _)

lemma holderSeminormOn_nonneg {n : ℕ} (α : ℝ) (f : Space n → ℝ) (s : Set (Space n)) :
    0 ≤ holderSeminormOn α f s :=
  Real.sSup_nonneg (by
    rintro t ⟨x, hx, y, hy, hxy, rfl⟩
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _))

lemma norm_le_supNormOn_of_holder {n : ℕ} {α : ℝ} {f : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) {x : Space n} (hx : x ∈ s) :
    ‖f x‖ ≤ supNormOn f s := by
  obtain ⟨M, H, hM, hH, hb, hh⟩ := hf
  exact le_csSup ⟨M, by rintro t ⟨y, hy, rfl⟩; exact hb y hy⟩ ⟨x, hx, rfl⟩

lemma holderQuotient_le_holderSeminormOn {n : ℕ} {α : ℝ} {f : Space n → ℝ}
    {s : Set (Space n)} (hf : IsHolderOn α f s)
    {x y : Space n} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    ‖f x - f y‖ / dist x y ^ α ≤ holderSeminormOn α f s := by
  obtain ⟨M, H, hM, hH, hb, hh⟩ := hf
  have hbd : BddAbove {t : ℝ | ∃ a ∈ s, ∃ b ∈ s,
      a ≠ b ∧ t = ‖f a - f b‖ / dist a b ^ α} := by
    refine ⟨H, ?_⟩
    rintro t ⟨a, ha, b, hb, hab, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hab) _)).mpr (hh a ha b hb)
  exact le_csSup hbd ⟨x, hx, y, hy, hxy, rfl⟩

lemma holderNormOn_add_le {n : ℕ} {α : ℝ} {f g : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) (hg : IsHolderOn α g s) :
    holderNormOn α (fun x => f x + g x) s ≤ holderNormOn α f s + holderNormOn α g s := by
  have hsup : supNormOn (fun x => f x + g x) s ≤ supNormOn f s + supNormOn g s := by
    apply Real.sSup_le _ (add_nonneg (supNormOn_nonneg _ _) (supNormOn_nonneg _ _))
    rintro t ⟨x, hx, rfl⟩
    exact (norm_add_le _ _).trans (add_le_add (norm_le_supNormOn_of_holder hf hx) (norm_le_supNormOn_of_holder hg hx))
  have hsemi : holderSeminormOn α (fun x => f x + g x) s ≤
      holderSeminormOn α f s + holderSeminormOn α g s := by
    apply Real.sSup_le _ (add_nonneg (holderSeminormOn_nonneg _ _ _) (holderSeminormOn_nonneg _ _ _))
    rintro t ⟨x, hx, y, hy, hxy, rfl⟩
    calc
      ‖f x + g x - (f y + g y)‖ / dist x y ^ α =
          ‖(f x - f y) + (g x - g y)‖ / dist x y ^ α := by congr 2; ring
      _ ≤ (‖f x - f y‖ + ‖g x - g y‖) / dist x y ^ α :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (Real.rpow_nonneg dist_nonneg _)
      _ = ‖f x - f y‖ / dist x y ^ α + ‖g x - g y‖ / dist x y ^ α := add_div _ _ _
      _ ≤ holderSeminormOn α f s + holderSeminormOn α g s :=
        add_le_add (holderQuotient_le_holderSeminormOn hf hx hy hxy)
          (holderQuotient_le_holderSeminormOn hg hx hy hxy)
  change supNormOn (fun x => f x + g x) s + holderSeminormOn α (fun x => f x + g x) s ≤
    (supNormOn f s + holderSeminormOn α f s) + (supNormOn g s + holderSeminormOn α g s)
  linarith

lemma holderNormOn_const_mul_le {n : ℕ} {α : ℝ} {f : Space n → ℝ}
    {s : Set (Space n)} (hf : IsHolderOn α f s) (k : ℝ) :
    holderNormOn α (fun x => k * f x) s ≤ ‖k‖ * holderNormOn α f s := by
  have hsup : supNormOn (fun x => k * f x) s ≤ ‖k‖ * supNormOn f s := by
    apply Real.sSup_le _ (mul_nonneg (norm_nonneg _) (supNormOn_nonneg _ _))
    rintro t ⟨x, hx, rfl⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_le_supNormOn_of_holder hf hx) (norm_nonneg _)
  have hsemi : holderSeminormOn α (fun x => k * f x) s ≤
      ‖k‖ * holderSeminormOn α f s := by
    apply Real.sSup_le _ (mul_nonneg (norm_nonneg _) (holderSeminormOn_nonneg _ _ _))
    rintro t ⟨x, hx, y, hy, hxy, rfl⟩
    rw [← mul_sub, norm_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (holderQuotient_le_holderSeminormOn hf hx hy hxy) (norm_nonneg _)
  change supNormOn (fun x => k * f x) s + holderSeminormOn α (fun x => k * f x) s ≤
    ‖k‖ * (supNormOn f s + holderSeminormOn α f s)
  nlinarith

lemma holderNormOn_const_le {n : ℕ} (α : ℝ) (k : ℝ) (s : Set (Space n)) :
    holderNormOn α (fun _ => k) s ≤ ‖k‖ := by
  have hsup : supNormOn (fun _ : Space n => k) s ≤ ‖k‖ := by
    apply Real.sSup_le _ (norm_nonneg _)
    rintro t ⟨x, hx, rfl⟩
    exact le_rfl
  have hsemi : holderSeminormOn α (fun _ : Space n => k) s ≤ 0 := by
    apply Real.sSup_le _ le_rfl
    rintro t ⟨x, hx, y, hy, hxy, rfl⟩
    simp
  change supNormOn (fun _ => k) s + holderSeminormOn α (fun _ => k) s ≤ ‖k‖
  linarith


lemma holder_difference_le_holderNormOn {n : ℕ} {α : ℝ} {f : Space n → ℝ}
    {s : Set (Space n)} (hf : IsHolderOn α f s)
    {x y : Space n} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f x - f y‖ ≤ holderNormOn α f s * dist x y ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero]
    exact mul_nonneg (holderNormOn_nonneg _ _ _) (Real.rpow_nonneg dist_nonneg _)
  · have hq := holderQuotient_le_holderSeminormOn hf hx hy hxy
    have hs : holderSeminormOn α f s ≤ holderNormOn α f s := by
      change holderSeminormOn α f s ≤ supNormOn f s + holderSeminormOn α f s
      exact le_add_of_nonneg_left (supNormOn_nonneg _ _)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) _)).mp (hq.trans hs)

lemma path_coefficientsHolderOn {n : ℕ} {α : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s : Set (Space n)}
    (hh : CoefficientsHolderOn α a b c s) (t : ℝ) :
    CoefficientsHolderOn α (pathPrincipal a t) (fun x => t • b x) (fun x => t * c x) s := by
  refine ⟨?_, ?_, isHolderOn_const_mul hh.2.2 t⟩
  · intro i j
    exact isHolderOn_add (isHolderOn_const α ((1 - t) * if i = j then 1 else 0) s)
      (isHolderOn_const_mul (hh.1 i j) t)
  · intro i
    simpa only [PiLp.smul_apply, smul_eq_mul] using isHolderOn_const_mul (hh.2.1 i) t

lemma holderNormOn_const_mul_le_of_unitInterval {n : ℕ} {α t : ℝ}
    {f : Space n → ℝ} {s : Set (Space n)} (hf : IsHolderOn α f s)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    holderNormOn α (fun x => t * f x) s ≤ holderNormOn α f s := by
  calc
    _ ≤ ‖t‖ * holderNormOn α f s := holderNormOn_const_mul_le hf t
    _ ≤ holderNormOn α f s := by
      rw [Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (holderNormOn_nonneg _ _ _) ht.2

lemma path_coefficientNorm_bound {n : ℕ} {α t K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s : Set (Space n)}
    (hh : CoefficientsHolderOn α a b c s)
    (hnorm : coefficientNormOn α a b c s ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) :
    coefficientNormOn α (pathPrincipal a t) (fun x => t • b x) (fun x => t * c x) s ≤
      K + (n : ℝ) ^ 2 := by
  have ha (i j : Fin n) : holderNormOn α (fun x => pathPrincipal a t x i j) s ≤
      1 + holderNormOn α (fun x => a x i j) s := by
    have hconst : holderNormOn α (fun _ : Space n => (1 - t) * if i = j then 1 else 0) s ≤ 1 := by
      apply (holderNormOn_const_le α _ s).trans
      by_cases hij : i = j
      · simpa [hij, Real.norm_of_nonneg (sub_nonneg.mpr ht.2)] using sub_le_self 1 ht.1
      · simp [hij]
    exact (holderNormOn_add_le
      (isHolderOn_const α ((1 - t) * if i = j then 1 else 0) s)
      (isHolderOn_const_mul (hh.1 i j) t)).trans
        (add_le_add hconst (holderNormOn_const_mul_le_of_unitInterval (hh.1 i j) ht))
  have hA := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => ha i j))
  have hB := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    holderNormOn_const_mul_le_of_unitInterval (hh.2.1 i) ht)
  have hC := holderNormOn_const_mul_le_of_unitInterval hh.2.2 ht
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hA
  simp only [coefficientNormOn, PiLp.smul_apply, smul_eq_mul] at hnorm ⊢
  nlinarith


lemma isHolderOn_mul {n : ℕ} {α : ℝ} {f g : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) (hg : IsHolderOn α g s) :
    IsHolderOn α (fun x => f x * g x) s := by
  obtain ⟨Mf, Hf, hMf, hHf, hbf, hhf⟩ := hf
  obtain ⟨Mg, Hg, hMg, hHg, hbg, hhg⟩ := hg
  refine ⟨Mf * Mg, Mf * Hg + Hf * Mg, mul_nonneg hMf hMg,
    add_nonneg (mul_nonneg hMf hHg) (mul_nonneg hHf hMg), ?_, ?_⟩
  · intro x hx
    rw [norm_mul]
    exact mul_le_mul (hbf x hx) (hbg x hx) (norm_nonneg _) hMf
  · intro x hx y hy
    calc
      ‖f x * g x - f y * g y‖ = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by congr 1; ring
      _ ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
      _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul]
      _ ≤ Mf * (Hg * dist x y ^ α) + (Hf * dist x y ^ α) * Mg :=
        add_le_add (mul_le_mul (hbf x hx) (hhg x hx y hy) (norm_nonneg _) hMf)
          (mul_le_mul (hhf x hx y hy) (hbg y hy) (norm_nonneg _)
            (mul_nonneg hHf (Real.rpow_nonneg dist_nonneg _)))
      _ = (Mf * Hg + Hf * Mg) * dist x y ^ α := by ring

lemma holderNormOn_mul_le {n : ℕ} {α : ℝ} {f g : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) (hg : IsHolderOn α g s) :
    holderNormOn α (fun x => f x * g x) s ≤ holderNormOn α f s * holderNormOn α g s := by
  have hsup : supNormOn (fun x => f x * g x) s ≤ supNormOn f s * supNormOn g s := by
    apply Real.sSup_le _ (mul_nonneg (supNormOn_nonneg _ _) (supNormOn_nonneg _ _))
    rintro t ⟨x, hx, rfl⟩
    rw [norm_mul]
    exact mul_le_mul (norm_le_supNormOn_of_holder hf hx) (norm_le_supNormOn_of_holder hg hx)
      (norm_nonneg _) (supNormOn_nonneg _ _)
  have hsemi : holderSeminormOn α (fun x => f x * g x) s ≤
      supNormOn f s * holderSeminormOn α g s + holderSeminormOn α f s * supNormOn g s := by
    apply Real.sSup_le _ (add_nonneg
      (mul_nonneg (supNormOn_nonneg _ _) (holderSeminormOn_nonneg _ _ _))
      (mul_nonneg (holderSeminormOn_nonneg _ _ _) (supNormOn_nonneg _ _)))
    rintro t ⟨x, hx, y, hy, hxy, rfl⟩
    calc
      ‖f x * g x - f y * g y‖ / dist x y ^ α =
          ‖f x * (g x - g y) + (f x - f y) * g y‖ / dist x y ^ α := by congr 2; ring
      _ ≤ (‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖) / dist x y ^ α :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (Real.rpow_nonneg dist_nonneg _)
      _ = ‖f x‖ * (‖g x - g y‖ / dist x y ^ α) +
          (‖f x - f y‖ / dist x y ^ α) * ‖g y‖ := by rw [norm_mul, norm_mul]; ring
      _ ≤ supNormOn f s * holderSeminormOn α g s + holderSeminormOn α f s * supNormOn g s :=
        add_le_add
          (mul_le_mul (norm_le_supNormOn_of_holder hf hx)
            (holderQuotient_le_holderSeminormOn hg hx hy hxy)
            (div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)) (supNormOn_nonneg _ _))
          (mul_le_mul (holderQuotient_le_holderSeminormOn hf hx hy hxy)
            (norm_le_supNormOn_of_holder hg hy) (norm_nonneg _) (holderSeminormOn_nonneg _ _ _))
  change supNormOn (fun x => f x * g x) s + holderSeminormOn α (fun x => f x * g x) s ≤
    (supNormOn f s + holderSeminormOn α f s) * (supNormOn g s + holderSeminormOn α g s)
  nlinarith [mul_nonneg (holderSeminormOn_nonneg α f s) (holderSeminormOn_nonneg α g s)]


lemma exists_nonexpansive_retraction_closedBall {n : ℕ} (z : Space n) {r : ℝ} (hr : 0 ≤ r) :
    ∃ p : Space n → Space n,
      (∀ x, p x ∈ closedBall z r) ∧ (∀ x ∈ closedBall z r, p x = x) ∧
      LipschitzWith 1 p := by
  have hne : (closedBall z r).Nonempty := ⟨z, mem_closedBall_self hr⟩
  have hc : Convex ℝ (closedBall z r) := convex_closedBall z r
  have hcomplete : IsComplete (closedBall z r) := isClosed_closedBall.isComplete
  choose p hmem hmin using exists_norm_eq_iInf_of_complete_convex hne hcomplete hc
  have hinner (x : Space n) : ∀ w ∈ closedBall z r,
      inner ℝ (x - p x) (w - p x) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hc (hmem x)).mp (hmin x)
  have hLip : LipschitzWith 1 p := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    have hx := hinner x (p y) (hmem y)
    have hy := hinner y (p x) (hmem x)
    have hsum : ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by
      have heq : inner ℝ (x - y) (p x - p y) = ‖p x - p y‖ ^ 2 +
          inner ℝ (x - p x) (p x - p y) - inner ℝ (y - p y) (p x - p y) := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right]
        ring
      have hx' : inner ℝ (x - p x) (p x - p y) ≥ 0 := by
        have heq' : p x - p y = -(p y - p x) := by abel
        rw [heq', inner_neg_right]
        linarith
      rw [heq]
      linarith
    have hcs := real_inner_le_norm (x-y) (p x-p y)
    nlinarith [norm_nonneg (p x-p y), norm_nonneg (x-y)]
  refine ⟨p, hmem, ?_, hLip⟩
  intro x hx
  have hx' := hinner x x hx
  rw [real_inner_self_eq_norm_sq] at hx'
  have : ‖x-p x‖ = 0 := by nlinarith [norm_nonneg (x-p x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

lemma exists_bounded_holder_extension {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (z : Space n) {r : ℝ} (hr : 0 ≤ r) {f : Space n → ℝ}
    (hf : IsHolderOn α f (closedBall z r)) :
    ∃ F : Space n → ℝ, IsHolder α F ∧ EqOn F f (closedBall z r) := by
  obtain ⟨p, hp, heq, hLip⟩ := exists_nonexpansive_retraction_closedBall z hr
  obtain ⟨M, H, hM, hH, hb, hh⟩ := hf
  refine ⟨f ∘ p, ⟨M,H,hM,hH,fun x => hb (p x) (hp x), ?_⟩, ?_⟩
  · intro x y
    apply (hh (p x) (hp x) (p y) (hp y)).trans
    apply mul_le_mul_of_nonneg_left _ hH
    apply Real.rpow_le_rpow dist_nonneg _ hα
    simpa using hLip.dist_le_mul x y
  · intro x hx
    simp only [Function.comp_apply, heq x hx]

/-- A cutoff which is one on the original ball and vanishes beyond radius `r+1`. -/
def ballCutoff {n : ℕ} (z : Space n) (r : ℝ) (x : Space n) : ℝ :=
  min (max (r + 1 - dist x z) 0) 1

lemma ballCutoff_bounds {n : ℕ} (z : Space n) (r : ℝ) (x : Space n) :
    0 ≤ ballCutoff z r x ∧ ballCutoff z r x ≤ 1 := by
  unfold ballCutoff
  exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

lemma ballCutoff_lipschitz {n : ℕ} (z : Space n) (r : ℝ) :
    LipschitzWith 1 (ballCutoff z r) := by
  have h : LipschitzWith 1 (fun x : Space n => r+1-dist x z) := by
    simpa using ((LipschitzWith.const (r+1)).sub (LipschitzWith.dist_left z))
  exact (h.max_const 0).min_const 1

lemma ballCutoff_eq_one {n : ℕ} {z x : Space n} {r : ℝ}
    (hx : x ∈ closedBall z r) : ballCutoff z r x = 1 := by
  have hx' : dist x z ≤ r := hx
  unfold ballCutoff
  rw [min_eq_right]
  exact (by linarith : (1:ℝ) ≤ r+1-dist x z).trans (le_max_left _ _)

lemma ballCutoff_eq_zero {n : ℕ} {z x : Space n} {r : ℝ}
    (hx : x ∉ closedBall z (r+1)) : ballCutoff z r x = 0 := by
  have hx' : r+1 < dist x z := lt_of_not_ge hx
  unfold ballCutoff
  rw [max_eq_right (by linarith), min_eq_left zero_le_one]

lemma ballCutoff_hasCompactSupport {n : ℕ} (z : Space n) (r : ℝ) :
    HasCompactSupport (ballCutoff z r) := by
  exact HasCompactSupport.intro' (isCompact_closedBall z (r+1)) isClosed_closedBall
    (fun x hx => ballCutoff_eq_zero hx)

lemma ballCutoff_tsupport {n : ℕ} (z : Space n) (r : ℝ) :
    tsupport (ballCutoff z r) ⊆ closedBall z (r+1) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hnot
  exact hx (ballCutoff_eq_zero hnot)

lemma holderBounds_mul {n : ℕ} {α M H N J : ℝ} {f g : Space n → ℝ}
    (hf : HolderBounds α f M H) (hg : HolderBounds α g N J) :
    HolderBounds α (fun x => f x * g x) (M*N) (M*J+N*H) := by
  obtain ⟨hM,hH,hf,hff⟩ := hf
  obtain ⟨hN,hJ,hg,hgg⟩ := hg
  refine ⟨mul_nonneg hM hN, add_nonneg (mul_nonneg hM hJ) (mul_nonneg hN hH), ?_, ?_⟩
  · intro x
    rw [norm_mul]
    exact mul_le_mul (hf x) (hg x) (norm_nonneg _) hM
  · intro x y
    calc
      ‖f x * g x - f y * g y‖ = ‖f x * (g x-g y) + g y * (f x-f y)‖ := by congr 1; ring
      _ ≤ ‖f x‖ * ‖g x-g y‖ + ‖g y‖ * ‖f x-f y‖ :=
        (norm_add_le _ _).trans (by simp only [norm_mul]; rfl)
      _ ≤ M * (J * dist x y ^ α) + N * (H * dist x y ^ α) := by gcongr; exacts [hf x, hgg x y, hg y, hff x y]
      _ = (M*J+N*H) * dist x y ^ α := by ring

lemma ballCutoff_holderBounds {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (z : Space n) (r : ℝ) : HolderBounds α (ballCutoff z r) 1 2 := by
  have hb (x : Space n) : ‖ballCutoff z r x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_bounds z r x).1]
    exact (ballCutoff_bounds z r x).2
  refine ⟨zero_le_one, by norm_num, hb, ?_⟩
  intro x y
  by_cases hd : dist x y ≤ 1
  · calc
      ‖ballCutoff z r x - ballCutoff z r y‖ ≤ dist x y := by
        simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
          (ballCutoff_lipschitz z r).dist_le_mul x y
      _ ≤ dist x y ^ α := Real.self_le_rpow_of_le_one dist_nonneg hd hα1
      _ ≤ 2 * dist x y ^ α := by nlinarith [Real.rpow_nonneg (dist_nonneg : 0 ≤ dist x y) α]
  · calc
      ‖ballCutoff z r x - ballCutoff z r y‖ ≤ ‖ballCutoff z r x‖+‖ballCutoff z r y‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [hb x,hb y]
      _ ≤ 2 * dist x y ^ α := by
        nlinarith [Real.one_le_rpow (le_of_not_ge hd) hα]

lemma exists_compactlySupported_holder_extension {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (z : Space n) {r : ℝ} (hr : 0 ≤ r) {f : Space n → ℝ}
    (hf : IsHolderOn α f (closedBall z r)) :
    ∃ F : Space n → ℝ, HasCompactSupport F ∧ tsupport F ⊆ closedBall z (r+1) ∧
      IsHolder α F ∧ EqOn F f (closedBall z r) := by
  obtain ⟨G, ⟨M,H,hG⟩, heq⟩ := exists_bounded_holder_extension hα z hr hf
  let F := fun x => ballCutoff z r x * G x
  refine ⟨F, (ballCutoff_hasCompactSupport z r).mul_right, ?_, ?_, ?_⟩
  · exact tsupport_mul_subset_left.trans (ballCutoff_tsupport z r)
  · exact ⟨1*M,1*H+M*2, holderBounds_mul (ballCutoff_holderBounds hα hα1 z r) hG⟩
  · intro x hx
    change ballCutoff z r x * G x = f x
    rw [ballCutoff_eq_one hx, one_mul, heq hx]

/-- Quantitative form: the original supremum bound is preserved and the new
seminorm bound is at most `H + 2*M`; neither constant depends on the data. -/
lemma exists_compactlySupported_holder_extension_bounds {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (z : Space n) {r : ℝ} (hr : 0 ≤ r)
    {f : Space n → ℝ} {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hb : ∀ x ∈ closedBall z r, ‖f x‖ ≤ M)
    (hh : ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r,
      ‖f x-f y‖ ≤ H * dist x y ^ α) :
    ∃ F : Space n → ℝ, HasCompactSupport F ∧ tsupport F ⊆ closedBall z (r+1) ∧
      HolderBounds α F M (H+2*M) ∧ EqOn F f (closedBall z r) := by
  obtain ⟨p, hp, heq, hLip⟩ := exists_nonexpansive_retraction_closedBall z hr
  let G := f ∘ p
  have hG : HolderBounds α G M H := by
    refine ⟨hM,hH,fun x => hb (p x) (hp x), ?_⟩
    intro x y
    apply (hh (p x) (hp x) (p y) (hp y)).trans
    apply mul_le_mul_of_nonneg_left _ hH
    apply Real.rpow_le_rpow dist_nonneg _ hα
    simpa using hLip.dist_le_mul x y
  let F := fun x => ballCutoff z r x * G x
  refine ⟨F, (ballCutoff_hasCompactSupport z r).mul_right,
    tsupport_mul_subset_left.trans (ballCutoff_tsupport z r), ?_, ?_⟩
  · convert holderBounds_mul (ballCutoff_holderBounds hα hα1 z r) hG using 1 <;> ring
  · intro x hx
    change ballCutoff z r x * f (p x) = f x
    rw [ballCutoff_eq_one hx, one_mul, heq x hx]

/-- The maximum principle upgrades Cauchy boundary data to Cauchy solutions
in the genuine supremum norm on the compact closed ball. -/
lemma ball_solution_maps_cauchy {n : ℕ} (hn : 1 ≤ n)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c f : Space n → ℝ}
    (hcoeff : EllipticCoefficients (ballDomain z r) a b c)
    (hc : ∀ x ∈ ball z r, c x ≤ 0)
    {g : ℕ → C(sphere z r, ℝ)} (hg : CauchySeq g)
    {u : ℕ → Space n → ℝ} (hu : ∀ j, IsBallSolution a b c f z r (g j) (u j)) :
    CauchySeq (fun j => (⟨fun x : closedBall z r => u j x,
      continuousOn_iff_continuous_domRestrict.mp (hu j).2.1⟩ : C(closedBall z r, ℝ))) := by
  rw [Metric.cauchySeq_iff] at hg ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hg ε hε
  refine ⟨N, fun j hj k hk => ?_⟩
  apply lt_of_le_of_lt ?_ (hN j hj k hk)
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro x
  simp only [dist_eq_norm]
  change ‖u j x - u k x‖ ≤ ‖g j - g k‖
  exact ball_solution_boundary_stability hn hr hcoeff hc (hu j) (hu k) x x.property

/-- For any approximating sequence of actual ball solutions, convergence of
the sphere data constructs a continuous closed-ball limit with the right
trace. The quantitative maximum-principle bound survives the limit. No
interior differentiability of the limit is assumed or asserted here. -/
lemma ball_solution_uniform_limit {n : ℕ} (hn : 1 ≤ n)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c f : Space n → ℝ}
    (hcoeff : EllipticCoefficients (ballDomain z r) a b c)
    (hc : ∀ x ∈ ball z r, c x ≤ 0)
    {g : ℕ → C(sphere z r, ℝ)} {g₀ : C(sphere z r, ℝ)}
    (hg : Tendsto g atTop (𝓝 g₀))
    {u : ℕ → Space n → ℝ} (hu : ∀ j, IsBallSolution a b c f z r (g j) (u j)) :
    ∃ v : Space n → ℝ, ContinuousOn v (closedBall z r) ∧
      TendstoUniformlyOn u v atTop (closedBall z r) ∧
      (∀ ζ : sphere z r, v ζ = g₀ ζ) ∧
      ∀ j : ℕ, ∀ x ∈ closedBall z r, ‖u j x - v x‖ ≤ ‖g j - g₀‖ := by
  classical
  let U : ℕ → C(closedBall z r, ℝ) := fun j =>
    ⟨fun x => u j x, continuousOn_iff_continuous_domRestrict.mp (hu j).2.1⟩
  have hU : CauchySeq U := ball_solution_maps_cauchy hn hr hcoeff hc hg.cauchySeq hu
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hU
  let v : Space n → ℝ := fun x => if hx : x ∈ closedBall z r then V ⟨x, hx⟩ else 0
  have hv (x : closedBall z r) : v x = V x := by
    dsimp [v]
    rw [dite_eq_left x.property]
  have hconv : TendstoUniformlyOn u v atTop (closedBall z r) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    convert ContinuousMap.tendsto_iff_tendstoUniformly.mp hV using 1
    exact funext hv
  refine ⟨v, ?_, hconv, ?_, ?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    convert V.continuous using 1
    exact funext hv
  · intro ζ
    have huv := hconv.tendsto_at (sphere_subset_closedBall ζ.property)
    have hgg := (ContinuousMap.tendsto_iff_tendstoUniformly.mp hg).tendsto_at ζ
    apply tendsto_nhds_unique huv
    simpa only [(hu _).2.2.2 ζ] using hgg
  · intro j x hx
    have hux := hconv.tendsto_at hx
    have hgn : Tendsto (fun k => ‖g j - g k‖) atTop (𝓝 ‖g j - g₀‖) :=
      (tendsto_const_nhds.sub hg).norm
    have hxn : Tendsto (fun k => ‖u j x - u k x‖) atTop (𝓝 ‖u j x - v x‖) :=
      (tendsto_const_nhds.sub hux).norm
    apply le_of_tendsto_of_tendsto hxn hgn
    exact Filter.Eventually.of_forall fun k =>
      ball_solution_boundary_stability hn hr hcoeff hc (hu j) (hu k) x hx


/-- Uniform convergence of two genuine derivative fields identifies both
limiting derivatives and yields C² regularity on an open set. -/
lemma contDiffOn_two_of_uniform_derivative_limits
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {u : ℕ → E → F} {v : E → F}
    {A : E → E →L[ℝ] F} {B : E → E →L[ℝ] (E →L[ℝ] F)}
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) s)
    (h₀ : ∀ x ∈ s, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    (h₁ : TendstoUniformlyOn (fun j => fderiv ℝ (u j)) A atTop s)
    (h₂ : TendstoUniformlyOn (fun j => fderiv ℝ (fderiv ℝ (u j))) B atTop s) :
    ContDiffOn ℝ 2 v s ∧ EqOn (fderiv ℝ v) A s ∧
      EqOn (fderiv ℝ (fderiv ℝ v)) B s := by
  have hu₁ (j : ℕ) : ContDiffOn ℝ 1 (fderiv ℝ (u j)) s :=
    (hu j).fderiv_of_isOpen hs (by norm_num)
  have hA (x : E) (hx : x ∈ s) : HasFDerivAt v (A x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn hs h₁ _ h₀ hx
    intro j y hy
    exact ((hu j).contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hB (x : E) (hx : x ∈ s) : HasFDerivAt A (B x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn hs h₂ _ (fun y hy => h₁.tendsto_at hy) hx
    intro j y hy
    exact ((hu₁ j).contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hBc : ContinuousOn B s := by
    apply h₂.continuousOn
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall fun j =>
      (hu₁ j).continuousOn_fderiv_of_isOpen hs (by norm_num))
  have hAC : ContDiffOn ℝ 1 A s := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hs.uniqueDiffOn).mpr
    refine ⟨by simp, B, contDiffOn_zero.mpr hBc, fun x hx => (hB x hx).hasFDerivWithinAt⟩
  have hv : ContDiffOn ℝ 2 v s := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 1) hs.uniqueDiffOn).mpr
    exact ⟨by simp, A, hAC, fun x hx => (hA x hx).hasFDerivWithinAt⟩
  have hfirst : EqOn (fderiv ℝ v) A s := fun x hx => (hA x hx).fderiv
  refine ⟨hv, hfirst, ?_⟩
  intro x hx
  have hEq : fderiv ℝ v =ᶠ[𝓝 x] A := Filter.eventually_of_mem (hs.mem_nhds hx) (fun y hy => hfirst hy)
  exact (hEq.fderiv_eq).trans (hB x hx).fderiv

/-- Uniform bounds and all-pairs Hölder constants pass to pointwise limits. -/
lemma isHolderOn_of_pointwise_limit {n : ℕ} {α M H : ℝ} {s : Set (Space n)}
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hb : ∀ j, ∀ x ∈ s, ‖u j x‖ ≤ M)
    (hh : ∀ j, ∀ x ∈ s, ∀ y ∈ s, ‖u j x - u j y‖ ≤ H * dist x y ^ α)
    (hv : ∀ x ∈ s, Tendsto (fun j => u j x) atTop (𝓝 (v x))) :
    IsHolderOn α v s := by
  refine ⟨M, H, hM, hH, ?_, ?_⟩
  · intro x hx
    exact le_of_tendsto (hv x hx).norm (Eventually.of_forall fun j => hb j x hx)
  · intro x hx y hy
    exact le_of_tendsto ((hv x hx).sub (hv y hy)).norm
      (Eventually.of_forall fun j => hh j x hx y hy)

namespace BallGeometry
open P201Specs P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.VariableSchauder P201Specs.Elliptic.BallSchauderSolvability
open P102.U4.GraphPieces P102.Sobolev.Geometry


lemma holder_of_bounded_lipschitz {n : ℕ} {α : ℝ} {g : Space n → ℝ}
    {s : Set (Space n)} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hg : IsBoundedOn g s)
    {L : NNReal} (hL : LipschitzOnWith L g s) :
    P201Specs.Elliptic.NewtonHessian.IsHolderOn α g s := by
  rcases hg with ⟨M, hM, hbound⟩
  refine ⟨M, max (L : ℝ) (2 * M), hM,
    le_trans L.coe_nonneg (le_max_left _ _), hbound, ?_⟩
  intro x hx y hy
  by_cases hd : dist x y ≤ 1
  · calc
      ‖g x - g y‖ ≤ (L : ℝ) * dist x y := by simpa only [dist_eq_norm] using hL.dist_le_mul x hx y hy
      _ ≤ (L : ℝ) * dist x y ^ α :=
        mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one dist_nonneg hd hα1) L.coe_nonneg
      _ ≤ max (L : ℝ) (2 * M) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
  · calc
      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hbound x hx, hbound y hy]
      _ ≤ (2 * M) * dist x y ^ α :=
        le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (not_le.mp hd).le hα)
      _ ≤ max (L : ℝ) (2 * M) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)

lemma smooth_c2HolderOn_closedBall {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (Ω : Domain n) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ (3 : ℕ) u Ω) (z : Space n) (r : ℝ)
    (hsub : closedBall z r ⊆ (Ω : Set _)) :
    IsC2HolderOn α u (closedBall z r) := by
  have hs := isCompact_closedBall z r
  have bounded {f : Space n → ℝ} (hf : ContinuousOn f (closedBall z r)) :
      IsBoundedOn f (closedBall z r) := by
    obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hf
    exact ⟨max M 0, le_max_right _ _, fun x hx => (hM x hx).trans (le_max_left _ _)⟩
  refine ⟨(hu.of_le (by norm_num)).mono hsub, bounded (hu.continuousOn.mono hsub), ?_, ?_⟩
  · intro i
    have hd : ContDiffOn ℝ 1 (multiPartial u {i}) Ω :=
      P102.U4.partialWord_contDiffOn Ω hu (({i} : MultiIndex n).sort (· ≤ ·)) 1 (by simp)
    exact bounded (hd.continuousOn.mono hsub)
  · intro i j
    have hd : ContDiffOn ℝ 1 (multiPartial u {i, j}) Ω :=
      P102.U4.partialWord_contDiffOn Ω hu (({i, j} : MultiIndex n).sort (· ≤ ·)) 1 (by simp)
    obtain ⟨L, hL⟩ := (hd.mono hsub).exists_lipschitzOnWith (by norm_num) (convex_closedBall z r) hs
    exact holder_of_bounded_lipschitz hα hα1 (bounded (hd.continuousOn.mono hsub)) hL

lemma c2HolderOn_mono {n : ℕ} {α : ℝ} {u : Space n → ℝ} {s t : Set (Space n)}
    (hu : IsC2HolderOn α u t) (hsub : s ⊆ t) : IsC2HolderOn α u s := by
  rcases hu with ⟨hc,hb,h1,h2⟩
  refine ⟨hc.mono hsub, ?_, ?_, ?_⟩
  · rcases hb with ⟨M,hM,hb⟩; exact ⟨M,hM,fun x hx => hb x (hsub hx)⟩
  · intro i; rcases h1 i with ⟨M,hM,hb⟩; exact ⟨M,hM,fun x hx => hb x (hsub hx)⟩
  · intro i j
    rcases h2 i j with ⟨M,H,hM,hH,hb,hh⟩
    exact ⟨M,H,hM,hH,fun x hx => hb x (hsub hx),fun x hx y hy => hh x (hsub hx) y (hsub hy)⟩

def lowerSphereGraph {m : ℕ} (r : ℝ) (x : Space m) : ℝ :=
  -Real.sqrt (r ^ 2 - ‖x‖ ^ 2)

lemma lowerSphereGraph_smooth {m : ℕ} {r : ℝ} (hr : 0 < r) :
    ContDiffOn ℝ (3 : ℕ) (lowerSphereGraph r : Space m → ℝ) (ball 0 r) := by
  apply ContDiffOn.neg
  apply ContDiffOn.sqrt
  · exact contDiffOn_const.sub (contDiff_norm_sq ℝ : ContDiff ℝ (3 : ℕ) (fun x : Space m => ‖x‖ ^ 2)).contDiffOn
  · intro x hx
    have hx' : ‖x‖ < r := by simpa using hx
    nlinarith [norm_nonneg x]

lemma lowerSphereGraph_holder {m : ℕ} {α r : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hr : 0 < r) :
    IsC2HolderOn α (lowerSphereGraph r : Space m → ℝ) (ball 0 (r / 2)) := by
  apply c2HolderOn_mono (smooth_c2HolderOn_closedBall hα hα1
    ⟨ball 0 r, isOpen_ball⟩ (lowerSphereGraph_smooth hr) 0 (r / 2) ?_) ball_subset_closedBall
  intro x hx
  have hx' : ‖x‖ ≤ r / 2 := by simpa using hx
  have : ‖x‖ < r := by linarith
  simpa using this

lemma lowerSphereGraph_lipschitz {m : ℕ} {r : ℝ} (hr : 0 < r) :
    ∃ L, LipschitzOnWith L (lowerSphereGraph r : Space m → ℝ) (ball 0 (r / 2)) := by
  have hsub : closedBall (0 : Space m) (r / 2) ⊆ ball 0 r := by
    intro x hx
    have hx' : ‖x‖ ≤ r / 2 := by simpa using hx
    have : ‖x‖ < r := by linarith
    simpa using this
  obtain ⟨L,hL⟩ := ((lowerSphereGraph_smooth hr).mono hsub).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall 0 (r / 2)) (isCompact_closedBall 0 (r / 2))
  exact ⟨L,hL.mono ball_subset_closedBall⟩

lemma lowerSphereGraph_shear_norm {m : ℕ} (r : ℝ) (x : Space m) (t : ℝ) :
    ‖shear (lowerSphereGraph r) (WithLp.toLp 2 (x,t))‖ ^ 2 =
      ‖x‖ ^ 2 + (-Real.sqrt (r^2 - ‖x‖^2) + t) ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [shear, lowerSphereGraph, Real.norm_eq_abs, sq_abs]

lemma lowerSphereGraph_sqrt_bound {m : ℕ} {r : ℝ} (hr : 0 < r) {x : Space m}
    (hx : x ∈ ball 0 (r / 2)) :
    r / 2 < Real.sqrt (r^2 - ‖x‖^2) ∧
      Real.sqrt (r^2 - ‖x‖^2) ^ 2 = r^2 - ‖x‖^2 := by
  have hx' : ‖x‖ < r / 2 := by simpa using hx
  have ha : 0 ≤ r^2 - ‖x‖^2 := by nlinarith [norm_nonneg x]
  have hs := Real.sq_sqrt ha
  exact ⟨by nlinarith [Real.sqrt_nonneg (r^2 - ‖x‖^2), norm_nonneg x], hs⟩

lemma lowerSphereGraph_shear_mem_ball {m : ℕ} {r : ℝ} (hr : 0 < r)
    {x : Space m} (hx : x ∈ ball 0 (r / 2)) {t : ℝ}
    (ht : t ∈ Ioo (-(r / 2)) (r / 2)) :
    shear (lowerSphereGraph r) (WithLp.toLp 2 (x,t)) ∈ ball 0 r ↔ 0 < t := by
  obtain ⟨hs,heq⟩ := lowerSphereGraph_sqrt_bound hr hx
  have hn := lowerSphereGraph_shear_norm r x t
  have hnn := norm_nonneg (shear (lowerSphereGraph r) (WithLp.toLp 2 (x,t)))
  simp only [mem_ball, dist_zero_right]
  constructor
  · intro hh
    have hh2 : ‖shear (lowerSphereGraph r) (WithLp.toLp 2 (x,t))‖ ^ 2 < r^2 :=
      sq_lt_sq₀ hnn hr.le |>.mpr hh
    nlinarith [sq_nonneg t]
  · intro hh
    have hmul : t * (2 * Real.sqrt (r^2 - ‖x‖^2) - t) > 0 := by
      apply mul_pos hh
      linarith [ht.2]
    nlinarith

lemma lowerSphereGraph_shear_mem_sphere {m : ℕ} {r : ℝ} (hr : 0 < r)
    {x : Space m} (hx : x ∈ ball 0 (r / 2)) {t : ℝ}
    (ht : t ∈ Ioo (-(r / 2)) (r / 2)) :
    shear (lowerSphereGraph r) (WithLp.toLp 2 (x,t)) ∈ sphere 0 r ↔ t = 0 := by
  obtain ⟨hs,heq⟩ := lowerSphereGraph_sqrt_bound hr hx
  have hn := lowerSphereGraph_shear_norm r x t
  simp only [mem_sphere, dist_zero_right]
  constructor
  · intro hh
    have hh2 : ‖shear (lowerSphereGraph r) (WithLp.toLp 2 (x,t))‖ ^ 2 = r^2 := by rw [hh]
    have hp : 0 < 2 * Real.sqrt (r^2 - ‖x‖^2) - t := by linarith [ht.2]
    have hmul : t * (2 * Real.sqrt (r^2 - ‖x‖^2) - t) = 0 := by nlinarith
    exact (mul_eq_zero.mp hmul).resolve_right hp.ne'
  · rintro rfl
    have hnn := norm_nonneg (shear (lowerSphereGraph r) (WithLp.toLp 2 (x,(0:ℝ))))
    nlinarith


lemma lowerSphereGraph_side {m : ℕ} {r : ℝ} (hr : 0 < r) :
    ball (0 : Ambient m) r ∩
        (shear (lowerSphereGraph r) '' cylinder (0 : Space m) (r / 2) (r / 2)) =
      shear (lowerSphereGraph r) '' upperCylinder (0 : Space m) (r / 2) (r / 2) := by
  ext z
  constructor
  · rintro ⟨hz,w,hw,rfl⟩
    refine ⟨w,⟨hw.1,?_,hw.2.2⟩,rfl⟩
    exact (lowerSphereGraph_shear_mem_ball hr hw.1 hw.2).mp hz
  · rintro ⟨w,hw,rfl⟩
    have ht : w.ofLp.2 ∈ Ioo (-(r/2)) (r/2) := ⟨by linarith [hw.2.1],hw.2.2⟩
    exact ⟨(lowerSphereGraph_shear_mem_ball hr hw.1 ht).mpr hw.2.1,
      w,⟨hw.1,ht⟩,rfl⟩

lemma lowerSphereGraph_boundary {m : ℕ} {r : ℝ} (hr : 0 < r) :
    frontier (ball (0 : Ambient m) r) ∩
        (shear (lowerSphereGraph r) '' cylinder (0 : Space m) (r / 2) (r / 2)) =
      graph (lowerSphereGraph r) '' ball (0 : Space m) (r / 2) := by
  rw [frontier_ball _ hr.ne']
  ext z
  constructor
  · rintro ⟨hz,w,hw,rfl⟩
    have ht := (lowerSphereGraph_shear_mem_sphere hr hw.1 hw.2).mp hz
    refine ⟨w.ofLp.1,hw.1,?_⟩
    change WithLp.toLp 2 (w.ofLp.1, lowerSphereGraph r w.ofLp.1) =
      WithLp.toLp 2 (w.ofLp.1, lowerSphereGraph r w.ofLp.1 + w.ofLp.2)
    rw [ht,add_zero]
  · rintro ⟨x,hx,rfl⟩
    have ht : (0 : ℝ) ∈ Ioo (-(r/2)) (r/2) := ⟨by linarith, by linarith⟩
    have heq : shear (lowerSphereGraph r) (WithLp.toLp 2 (x,(0:ℝ))) =
        graph (lowerSphereGraph r) x := by simp [shear, graph]
    refine ⟨?_,WithLp.toLp 2 (x,0),⟨hx,ht⟩,heq⟩
    rw [← heq]
    exact (lowerSphereGraph_shear_mem_sphere hr hx ht).mpr rfl

lemma affineImage_ball_inter {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (r : ℝ) (s : Set (Ambient m)) :
    ball (e 0) r ∩ e '' s = e '' (ball 0 r ∩ s) := by
  ext z
  constructor
  · rintro ⟨hz,w,hw,rfl⟩
    refine ⟨w,⟨?_,hw⟩,rfl⟩
    simpa only [mem_ball,e.dist_map] using hz
  · rintro ⟨w,⟨hw,hs⟩,rfl⟩
    exact ⟨by simpa only [mem_ball,e.dist_map] using hw,w,hs,rfl⟩

lemma affineImage_sphere_inter {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (r : ℝ) (s : Set (Ambient m)) :
    sphere (e 0) r ∩ e '' s = e '' (sphere 0 r ∩ s) := by
  ext z
  constructor
  · rintro ⟨hz,w,hw,rfl⟩
    refine ⟨w,⟨?_,hw⟩,rfl⟩
    simpa only [mem_sphere,e.dist_map] using hz
  · rintro ⟨w,⟨hw,hs⟩,rfl⟩
    exact ⟨by simpa only [mem_sphere,e.dist_map] using hw,w,hs,rfl⟩

noncomputable def sphereBoundaryChart {m : ℕ} {r : ℝ} (hr : 0 < r)
    (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) : BoundaryChart (ball (e 0) r) where
  frame := e
  center := 0
  radius := r/2
  height := r/2
  radius_pos := by positivity
  height_pos := by positivity
  graphFunction := lowerSphereGraph r
  constant := (lowerSphereGraph_lipschitz hr).choose
  graph_lipschitz := (lowerSphereGraph_lipschitz hr).choose_spec
  side := by
    change ball (e 0) r ∩ e '' _ = _
    rw [affineImage_ball_inter, lowerSphereGraph_side hr]
  boundary := by
    change frontier (ball (e 0) r) ∩ e '' _ = _
    rw [frontier_ball _ hr.ne',affineImage_sphere_inter, ← frontier_ball (0 : Ambient m) hr.ne',
      lowerSphereGraph_boundary hr]


lemma lowerSphereGraph_zero {m : ℕ} {r : ℝ} (hr : 0 < r) :
    lowerSphereGraph r (0 : Space m) = -r := by
  simp [lowerSphereGraph,Real.sqrt_sq hr.le]

lemma lowerSphereGraph_pole_norm {m : ℕ} {r : ℝ} (hr : 0 < r) :
    ‖graph (lowerSphereGraph r) (0 : Space m)‖ = r := by
  have hsq : ‖graph (lowerSphereGraph r) (0 : Space m)‖ ^ 2 = r^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖(0 : Space m)‖ ^ 2 + ‖lowerSphereGraph r (0 : Space m)‖ ^ 2 = r^2
    simp [lowerSphereGraph_zero hr, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg (graph (lowerSphereGraph r) (0 : Space m))]

lemma sphere_point_frame {m : ℕ} {r : ℝ} (hr : 0 < r)
    (z p : Ambient m) (hp : p ∈ sphere z r) :
    ∃ e : Ambient m ≃ᵃⁱ[ℝ] Ambient m,
      e 0 = z ∧ e (graph (lowerSphereGraph r) (0 : Space m)) = p := by
  let q := graph (lowerSphereGraph r) (0 : Space m)
  have hq : ‖q‖ = ‖p-z‖ := by
    rw [lowerSphereGraph_pole_norm hr]
    simpa only [mem_sphere,dist_eq_norm] using hp.symm
  let R := (ℝ ∙ (q - (p-z)))ᗮ.reflection
  let e := R.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ (Ambient m) z)
  refine ⟨e,?_,?_⟩
  · simp [e]
  · have hR : R q = p-z := Submodule.reflection_sub hq
    change z + R q = p
    rw [hR]
    abel

lemma geometricOpen_ball {m : ℕ} (z : Space (m+1)) (r : ℝ) :
    (P102.Sobolev.Extension.geometricOpen (graphFrame m) (ballDomain z r) : Set (Ambient m)) =
      ball ((graphFrame m).symm z) r := by
  ext x
  change dist (graphFrame m x) z < r ↔ dist x ((graphFrame m).symm z) < r
  conv_lhs => rw [← (graphFrame m).apply_symm_apply z, (graphFrame m).dist_map]

lemma ball_hasC2HolderBoundary {m : ℕ} {α r : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (z : Space (m+1)) (hr : 0 < r) :
    HasC2HolderBoundary α (ballDomain z r) := by
  intro p hp _
  have hp' : p ∈ sphere z r := by
    simpa only [ballDomain, TopologicalSpace.Opens.coe_mk, frontier_ball z hr.ne'] using hp
  have hpA : (graphFrame m).symm p ∈ sphere ((graphFrame m).symm z) r := by
    simpa only [mem_sphere, (graphFrame m).symm.dist_map] using hp'
  obtain ⟨e,he0,hep⟩ := sphere_point_frame hr ((graphFrame m).symm z) ((graphFrame m).symm p) hpA
  have hex : ∃ C : BoundaryChart (ball (e 0) r),
      graphFrame m (C.frame (graph C.graphFunction C.center)) = p ∧
        IsC2HolderOn α C.graphFunction (ball C.center C.radius) := by
    refine ⟨sphereBoundaryChart hr e,?_,lowerSphereGraph_holder hα hα1 hr⟩
    change graphFrame m (e (graph (lowerSphereGraph r) 0)) = p
    rw [hep, (graphFrame m).apply_symm_apply]
  rw [he0] at hex
  rw [geometricOpen_ball z r]
  exact hex

end BallGeometry



lemma lifted_ball_solution_schauder_estimate
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r)
    (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ),
        UniformlyEllipticOn ell a (closedBall z r) →
        CoefficientsHolderOn α a b c (closedBall z r) →
        coefficientNormOn α a b c (closedBall z r) ≤ K →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        ∀ f G : Space n → ℝ,
          IsHolderOn α f (closedBall z r) →
          IsC2HolderUpToOn α G (closedBall z r) →
          ∀ u : Space n → ℝ, IsLiftedBallSolution α a b c f G z r u →
            c2HolderUpToNormOn α u (closedBall z r) ≤
              C * (holderNormOn α f (closedBall z r) + c2HolderUpToNormOn α G (closedBall z r)) := by
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨Cg, hCg, hglobalest⟩ := hglobal m α hα hα1 (ballDomain z r)
      isBounded_ball (BallGeometry.ball_hasC2HolderBoundary hα.le hα1.le z hr) ell K hell hK
    simp only [ballDomain, TopologicalSpace.Opens.coe_mk, closure_ball z hr.ne',
      frontier_ball z hr.ne'] at hglobalest
    obtain ⟨Cs, hCs, hsup⟩ := lifted_ball_solution_supremum_estimate hn hα z hr hell hK
    refine ⟨Cg * (Cs + 1), mul_pos hCg (by linarith), ?_⟩
    intro a b c he hh hnorm hc f G hf hG u hu
    have hg := hglobalest a b c he hh hnorm u f G hu.1 hf hG hu.2.1 hu.2.2
    have hs := hsup a b c f G u he hh hnorm hc hf hG hu
    have hm := mul_le_mul_of_nonneg_left hs hCg.le
    nlinarith


lemma uniform_path_schauder_estimate
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r)
    (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ),
        UniformlyEllipticOn ell a (closedBall z r) →
        CoefficientsHolderOn α a b c (closedBall z r) →
        coefficientNormOn α a b c (closedBall z r) ≤ K →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ f G : Space n → ℝ,
          IsHolderOn α f (closedBall z r) →
          IsC2HolderUpToOn α G (closedBall z r) →
          ∀ u : Space n → ℝ,
            IsLiftedBallSolution α (pathPrincipal a t) (fun x => t • b x) (fun x => t * c x) f G z r u →
            c2HolderUpToNormOn α u (closedBall z r) ≤
              C * (holderNormOn α f (closedBall z r) + c2HolderUpToNormOn α G (closedBall z r)) := by
  obtain ⟨C, hC, hest⟩ := lifted_ball_solution_schauder_estimate hglobal hn α hα hα1 z hr
    (min ell 1) (K + (n : ℝ)^2) (lt_min hell zero_lt_one) (add_nonneg hK (sq_nonneg _))
  refine ⟨C, hC, ?_⟩
  intro a b c he hh hnorm hc t ht f G hf hG u hu
  exact hest (pathPrincipal a t) (fun x => t • b x) (fun x => t * c x)
    (pathPrincipal_uniformlyEllipticOn he ht) (path_coefficientsHolderOn hh t)
    (path_coefficientNorm_bound hh hnorm ht)
    (fun x hx => mul_nonpos_of_nonneg_of_nonpos ht.1 (hc x hx)) f G hf hG u hu



lemma secondPartial_eq_fderiv_fderiv {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (i j : Fin n) :
    secondPartial u i j x =
      (fderiv ℝ (fderiv ℝ u) x (coordinate n i)) (coordinate n j) := by
  unfold secondPartial firstPartial
  rw [fderiv_clm_apply hu (differentiableAt_const (coordinate n j))]
  simp

lemma nondivergenceOperator_tendsto {n : ℕ} {s : Set (Space n)} (hs : IsOpen s)
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) s)
    (h₀ : ∀ x ∈ s, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {A : Space n → Space n →L[ℝ] ℝ}
    {B : Space n → Space n →L[ℝ] (Space n →L[ℝ] ℝ)}
    (h₁ : TendstoUniformlyOn (fun j => fderiv ℝ (u j)) A atTop s)
    (h₂ : TendstoUniformlyOn (fun j => fderiv ℝ (fderiv ℝ (u j))) B atTop s)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n) (c : Space n → ℝ)
    {x : Space n} (hx : x ∈ s) :
    Tendsto (fun j => nondivergenceOperator a b c (u j) x) atTop
      (𝓝 (nondivergenceOperator a b c v x)) := by
  obtain ⟨hv,hA,hB⟩ := contDiffOn_two_of_uniform_derivative_limits hs hu h₀ h₁ h₂
  have hfirst (i : Fin n) : Tendsto (fun j => firstPartial (u j) i x) atTop
      (𝓝 (firstPartial v i x)) := by
    unfold firstPartial
    rw [hA hx]
    exact ((ContinuousLinearMap.apply ℝ ℝ (coordinate n i)).continuous.tendsto _).comp
      (h₁.tendsto_at hx)
  have hsecond (i j : Fin n) : Tendsto (fun k => secondPartial (u k) i j x) atTop
      (𝓝 (secondPartial v i j x)) := by
    have hregular (k : ℕ) : DifferentiableAt ℝ (fderiv ℝ (u k)) x :=
      ((hu k).fderiv_of_isOpen hs (m := 1) (by norm_num)).contDiffAt
        (hs.mem_nhds hx) |>.differentiableAt (by norm_num)
    have hvregular : DifferentiableAt ℝ (fderiv ℝ v) x :=
      (hv.fderiv_of_isOpen hs (m := 1) (by norm_num)).contDiffAt
        (hs.mem_nhds hx) |>.differentiableAt (by norm_num)
    simp_rw [secondPartial_eq_fderiv_fderiv (hregular _) i j]
    rw [secondPartial_eq_fderiv_fderiv hvregular i j, hB hx]
    exact ((ContinuousLinearMap.apply ℝ ℝ (coordinate n j)).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) (coordinate n i)).continuous.tendsto _).comp
        (h₂.tendsto_at hx))
  unfold nondivergenceOperator
  exact ((tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (hsecond i j).const_mul (a x i j)).add
    (tendsto_finsetSum _ fun i _ => (hfirst i).const_mul (b x i))).add
      ((h₀ x hx).const_mul (c x))

/-- The limiting equation follows from convergence of actual derivatives;
it is not included among the hypotheses about the candidate limit. -/
lemma equation_of_uniform_derivative_limits {n : ℕ} {s : Set (Space n)} (hs : IsOpen s)
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) s)
    (h₀ : ∀ x ∈ s, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {A : Space n → Space n →L[ℝ] ℝ}
    {B : Space n → Space n →L[ℝ] (Space n →L[ℝ] ℝ)}
    (h₁ : TendstoUniformlyOn (fun j => fderiv ℝ (u j)) A atTop s)
    (h₂ : TendstoUniformlyOn (fun j => fderiv ℝ (fderiv ℝ (u j))) B atTop s)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n) (c f : Space n → ℝ)
    (hL : ∀ j, ∀ x ∈ s, nondivergenceOperator a b c (u j) x = f x) :
    ∀ x ∈ s, nondivergenceOperator a b c v x = f x := by
  intro x hx
  apply tendsto_nhds_unique (nondivergenceOperator_tendsto hs hu h₀ h₁ h₂ a b c hx)
  simpa only [hL _ x hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))

lemma laplacian_affine_scalar {n : ℕ} (q : Space n →L[ℝ] ℝ) (A B : ℝ) (x : Space n) :
    P201Specs.laplacian (fun y => A+B*q y) x = 0 := by
  have hd (y : Space n) : fderiv ℝ (fun y => A+B*q y) y = B • q := by
    simp only [fderiv_const_add, fderiv_const_mul q.differentiableAt, q.fderiv]
  unfold P201Specs.laplacian
  apply Finset.sum_eq_zero
  intro i _
  have hs : ({i,i} : MultiIndex n).sort (· ≤ ·) = [i,i] := by
    change (i ::ₘ ({i} : Multiset (Fin n))).sort (· ≤ ·) = [i,i]
    rw [Multiset.sort_cons i ({i} : Multiset (Fin n)) (· ≤ ·) (by simp), Multiset.sort_singleton]
  change P102.U4.partialWord (fun y => A+B*q y) (({i,i} : MultiIndex n).sort (· ≤ ·)) x = 0
  rw [hs]
  change fderiv ℝ (fun y => fderiv ℝ (fun y => A+B*q y) y (coordinate n i)) x (coordinate n i) = 0
  simp only [hd]
  simp

lemma interval_harmonic_extension (z : Space 1) {r : ℝ} (hr : 0 < r)
    (g : C(sphere z r, ℝ)) :
    ∃ h : Space 1 → ℝ, ContDiff ℝ 2 h ∧ (∀ x, P201Specs.laplacian h x = 0) ∧
      (∀ ζ : sphere z r, h ζ = g ζ) := by
  let q : Space 1 ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  have hnorm (x : Space 1) : ‖x‖ = |q x| := by
    simp [EuclideanSpace.norm_eq, q, Real.sqrt_sq_eq_abs]
  let a := q.symm (q z-r)
  let b := q.symm (q z+r)
  have ha : a ∈ sphere z r := by
    rw [mem_sphere, dist_eq_norm, hnorm, map_sub]
    simp only [a, q.apply_symm_apply, sub_sub_cancel_left, abs_neg, abs_of_pos hr]
  have hb : b ∈ sphere z r := by
    rw [mem_sphere, dist_eq_norm, hnorm, map_sub]
    simp only [b, q.apply_symm_apply, add_sub_cancel_left, abs_of_pos hr]
  let ga := g ⟨a,ha⟩
  let gb := g ⟨b,hb⟩
  let B := (gb-ga)/(2*r)
  let A := (ga+gb)/2-B*q z
  let h := fun x : Space 1 => A+B*q x
  refine ⟨h, (contDiff_const.add (contDiff_const.mul q.contDiff)),
    laplacian_affine_scalar q.toContinuousLinearMap A B, ?_⟩
  intro ζ
  have hz : |q ζ-q z| = r := by
    simpa only [mem_sphere, dist_eq_norm, hnorm, map_sub] using ζ.property
  obtain hleft | hright := (abs_eq hr.le).mp hz
  · have heq : (ζ : Space 1) = b := by
      apply q.injective
      dsimp [b]
      rw [q.apply_symm_apply]
      linarith
    have hg : g ζ = gb := by congr 1; apply Subtype.ext; exact heq
    change A+B*q ζ = g ζ
    rw [hg]
    dsimp [A,B]
    have hcoord : q ζ = q z+r := by linarith
    rw [hcoord]
    field_simp
    ring
  · have heq : (ζ : Space 1) = a := by
      apply q.injective
      dsimp [a]
      rw [q.apply_symm_apply]
      linarith
    have hg : g ζ = ga := by congr 1; apply Subtype.ext; exact heq
    change A+B*q ζ = g ζ
    rw [hg]
    dsimp [A,B]
    have hcoord : q ζ = q z-r := by linarith
    rw [hcoord]
    field_simp
    ring

lemma harmonic_ball_extension {n : ℕ} (hn : 1 ≤ n) (z : Space n) {r : ℝ}
    (hr : 0 < r) (g : C(sphere z r, ℝ)) :
    ∃ h : Space n → ℝ, ContDiffOn ℝ 2 h (ball z r) ∧
      ContinuousOn h (closedBall z r) ∧ (∀ x ∈ ball z r, P201Specs.laplacian h x = 0) ∧
      (∀ ζ : sphere z r, h ζ = g ζ) := by
  by_cases hn1 : n=1
  · subst n
    obtain ⟨h,hh,heq,hg⟩ := interval_harmonic_extension z hr g
    exact ⟨h,hh.contDiffOn,hh.continuous.continuousOn,fun x _ => heq x,hg⟩
  · have hn2 : 2 ≤ n := by omega
    have hh := P201.BallPoisson.poissonExtension_harmonic hn2 z hr g
    have ht := P201.BallPoisson.continuous_extension hn2 z r hr g
    exact ⟨P201.BallPoisson.poissonExtension z r g,hh.1,ht.1,hh.2,ht.2⟩

lemma isHolderOn_neg {n : ℕ} {α : ℝ} {f : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) : IsHolderOn α (-f) s := by
  obtain ⟨M,H,hM,hH,hb,hh⟩ := hf
  refine ⟨M,H,hM,hH,?_,?_⟩
  · intro x hx
    simpa only [Pi.neg_apply,norm_neg] using hb x hx
  · intro x hx y hy
    simpa only [Pi.neg_apply,neg_sub_neg,norm_sub_rev] using hh x hx y hy

lemma isHolderLoc_on_ball {n : ℕ} {α : ℝ} {f : Space n → ℝ}
    {z : Space n} {r : ℝ} (hf : IsHolderOn α f (closedBall z r)) :
    IsHolderLoc α f ⟨ball z r,isOpen_ball⟩ := by
  intro x hx
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
  exact ⟨ε,hε,he,P201.Elliptic.PoissonSchauder.isHolderOn_mono hf
    (he.trans ball_subset_closedBall)⟩

lemma laplacian_ball_classical_solution {n : ℕ} (hn : 1 ≤ n)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r) {f : Space n → ℝ}
    (hf : IsHolderOn α f (closedBall z r)) (g : C(sphere z r, ℝ)) :
    ∃ u : Space n → ℝ,
      ContDiffOn ℝ 2 u (ball z r) ∧ ContinuousOn u (closedBall z r) ∧
      (∀ x ∈ ball z r, P201Specs.laplacian u x = f x) ∧ (∀ ζ : sphere z r, u ζ = g ζ) ∧
      IsC2HolderLocOn α u ⟨ball z r,isOpen_ball⟩ := by
  obtain ⟨F,hc,hsupp,hF,hagree⟩ :=
    exists_compactlySupported_holder_extension hα.le hα1.le z hr.le hf
  obtain ⟨C,hC,hest⟩ := P201.Elliptic.NewtonHessian.potentialEstimate hn α hα hα1
    (∅ : Set (Space n)) Bornology.isBounded_empty z (r+1) (by linarith)
  have hw : ContDiff ℝ 2 (holderPotential F) := (hest F hc hsupp hF).1.1
  let k : C(sphere z r, ℝ) := g +
    ⟨fun ζ => holderPotential F ζ, hw.continuous.comp continuous_subtype_val⟩
  obtain ⟨h,hh,hcl,heq,htrace⟩ := harmonic_ball_extension hn z hr k
  let u := h-holderPotential F
  have hu : ContDiffOn ℝ 2 u (ball z r) := hh.sub hw.contDiffOn
  have hueq : ∀ x ∈ ball z r, P201Specs.laplacian u x = f x := by
    intro x hx
    have hhx : ContDiffAt ℝ 2 h x := (hh x hx).contDiffAt (isOpen_ball.mem_nhds hx)
    have hwx : ContDiffAt ℝ 2 (holderPotential F) x := hw.contDiffAt
    change P201Specs.laplacian (h-holderPotential F) x = f x
    rw [P201.MeanValues.laplacian_bridge (h-holderPotential F) x (hhx.sub hwx), hhx.laplacian_sub hwx,
      ← P201.MeanValues.laplacian_bridge _ _ hhx, ← P201.MeanValues.laplacian_bridge _ _ hwx]
    have hheq := heq x hx
    have hwq := P201.Elliptic.PoissonSchauder.potential_equation hn α hα hα1 F hc hF x
    have hFq := hagree (ball_subset_closedBall hx)
    linarith
  refine ⟨u,hu,hcl.sub hw.continuous.continuousOn,hueq,?_,?_⟩
  · intro ζ
    change h ζ-holderPotential F ζ = g ζ
    have htq := htrace ζ
    change h ζ = g ζ+holderPotential F ζ at htq
    linarith
  · apply P201.Elliptic.PoissonSchauder.local_regularity hn α hα hα1
      ⟨ball z r,isOpen_ball⟩ u (-f) hu
      (isHolderLoc_on_ball (isHolderOn_neg hf))
    intro x hx
    simpa only [Pi.neg_apply] using congrArg Neg.neg (hueq x hx)


namespace BallApprox
open P201Specs P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.VariableSchauder P201Specs.Elliptic.BallSchauderSolvability
open P201Specs.Elliptic.ConstantSchauder

lemma sphere_continuous_extension {n : ℕ} {z : Space n} {r : ℝ} (hr : 0 < r)
    (g : C(sphere z r,ℝ)) :
    ∃ F : Space n → ℝ, UniformContinuous F ∧ ∀ ζ : sphere z r, F ζ = g ζ := by
  obtain ⟨f,hf⟩ := g.exists_restrict_eq isClosed_sphere
  let χ : ContDiffBump z :=
    {rIn := r+1, rOut := r+2, rIn_pos := by linarith, rIn_lt_rOut := by linarith}
  refine ⟨fun x => χ x * f x,?_,?_⟩
  · exact (χ.hasCompactSupport.mul_right (f' := (f : Space n → ℝ))).uniformContinuous_of_continuous
      (χ.continuous.mul f.continuous)
  · intro ζ
    have hz : (ζ : Space n) ∈ closedBall z χ.rIn := by
      change dist (ζ : Space n) z ≤ r+1
      rw [ζ.property]
      linarith
    change χ ζ * f ζ = g ζ
    rw [χ.one_of_mem_closedBall hz,one_mul]
    exact congrArg (fun h : C(sphere z r,ℝ) => h ζ) hf

lemma sphere_smooth_approximation {n : ℕ} {z : Space n} {r ε : ℝ} (hr : 0 < r)
    (g : C(sphere z r,ℝ)) (hε : 0 < ε) :
    ∃ G : Space n → ℝ, ContDiff ℝ ∞ G ∧ ∀ ζ : sphere z r, ‖G ζ - g ζ‖ < ε := by
  obtain ⟨F,hF,hFg⟩ := sphere_continuous_extension hr g
  obtain ⟨G,hG,hGF⟩ := hF.exists_contDiff_dist_le hε
  refine ⟨G,hG,?_⟩
  intro ζ
  simpa only [hFg ζ,dist_eq_norm] using hGF ζ


lemma sphere_smooth_approximation_sequence {n : ℕ} {z : Space n} {r : ℝ} (hr : 0 < r)
    (g : C(sphere z r,ℝ)) :
    ∃ G : ℕ → C(Space n,ℝ),
      (∀ j, ContDiff ℝ ∞ (G j)) ∧
      (∀ j, ∀ ζ : sphere z r, ‖G j ζ - g ζ‖ < 1 / ((j : ℝ)+1)) ∧
      Tendsto (fun j => (G j).restrict (sphere z r)) atTop (𝓝 g) := by
  have hh (j : ℕ) : ∃ G : Space n → ℝ, ContDiff ℝ ∞ G ∧
      ∀ ζ : sphere z r, ‖G ζ-g ζ‖ < 1 / ((j : ℝ)+1) :=
    sphere_smooth_approximation hr g (by positivity)
  choose G hG hGg using hh
  let F : ℕ → C(Space n,ℝ) := fun j => ⟨G j,(hG j).continuous⟩
  refine ⟨F,hG,hGg,?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro ζ
  exact (hGg j ζ).le


lemma uniqueDiffOn_closedBall {n : ℕ} (z : Space n) {r : ℝ} (hr : 0 < r) :
    UniqueDiffOn ℝ (closedBall z r) := by
  apply uniqueDiffOn_convex (convex_closedBall z r)
  refine ⟨z,?_⟩
  rw [mem_interior_iff_mem_nhds]
  exact mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hr)) ball_subset_closedBall

lemma smooth_c2HolderUpToOn_compact_convex {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) {s : Set (Space n)}
    (hs : IsCompact s) (hconv : Convex ℝ s) (hUnique : UniqueDiffOn ℝ s) :
    IsC2HolderUpToOn α u s := by
  let D1 : Fin n → Space n → ℝ := fun i x => fderiv ℝ u x (coordinate n i)
  let D2 : Fin n → Fin n → Space n → ℝ := fun i j x => fderiv ℝ (D1 j) x (coordinate n i)
  have hD1 (i : Fin n) : ContDiff ℝ 2 (D1 i) := by
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hD2 (i j : Fin n) : ContDiff ℝ 1 (D2 i j) := by
    exact ((hD1 j).fderiv_right (by norm_num)).clm_apply contDiff_const
  have hfirst (i : Fin n) : EqOn (firstPartialWithin u s i) (D1 i) s := by
    intro x hx
    unfold firstPartialWithin
    rw [fderivWithin_eq_fderiv (hUnique x hx) (hu.differentiable (by simp) x)]
  have hsecond (i j : Fin n) : EqOn (secondPartialWithin u s i j) (D2 i j) s := by
    intro x hx
    unfold secondPartialWithin
    rw [fderivWithin_congr' (hfirst j) hx,
      fderivWithin_eq_fderiv (hUnique x hx) ((hD1 j).differentiable (by norm_num) x)]
  have bounded {f : Space n → ℝ} (hf : ContinuousOn f s) : IsBoundedOn f s := by
    obtain ⟨M,hM⟩ := hs.exists_bound_of_continuousOn hf
    exact ⟨max M 0,le_max_right _ _,fun x hx => (hM x hx).trans (le_max_left _ _)⟩
  refine ⟨hu.contDiffOn.of_le (by simp),bounded hu.continuous.continuousOn,?_,?_⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := bounded (hD1 i).continuous.continuousOn
    exact ⟨M,hM,fun x hx => by rw [hfirst i hx]; exact hb x hx⟩
  · intro i j
    obtain ⟨L,hL⟩ := (hD2 i j).contDiffOn.exists_lipschitzOnWith (by norm_num) hconv hs
    obtain ⟨M,H,hM,hH,hb,hh⟩ := BallGeometry.holder_of_bounded_lipschitz hα hα1
      (bounded (hD2 i j).continuous.continuousOn) hL
    refine ⟨M,H,hM,hH,?_,?_⟩
    · intro x hx
      rw [hsecond i j hx]
      exact hb x hx
    · intro x hx y hy
      rw [hsecond i j hx,hsecond i j hy]
      exact hh x hx y hy

lemma smooth_c2HolderUpToOn_closedBall {n : ℕ} {α r : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (z : Space n) (hr : 0 < r)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) :
    IsC2HolderUpToOn α u (closedBall z r) :=
  smooth_c2HolderUpToOn_compact_convex hα hα1 hu (isCompact_closedBall z r)
    (convex_closedBall z r) (uniqueDiffOn_closedBall z hr)


lemma partialWord_two_swap {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) (i j : Fin n) :
    P102.U4.partialWord u [i,j] = P102.U4.partialWord u [j,i] := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  simp only [P102.U4.partialWord]
  rw [fderiv_clm_apply hd (differentiableAt_const (coordinate n j)),
    fderiv_clm_apply hd (differentiableAt_const (coordinate n i))]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using
    hu.contDiffAt.isSymmSndFDerivAt (by norm_num) (coordinate n i) (coordinate n j)

lemma classical_second_eq_multiPartial {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) (i j : Fin n) :
    (fun x => fderiv ℝ (fun y => fderiv ℝ u y (coordinate n j)) x (coordinate n i)) =
      multiPartial u {i,j} := by
  change P102.U4.partialWord u [i,j] = P102.U4.partialWord u (({i,j} : MultiIndex n).sort (· ≤ ·))
  by_cases hij : i ≤ j
  · rw [Multiset.insert_eq_cons, Multiset.sort_cons i {j} (· ≤ ·) (by simpa using hij),Multiset.sort_singleton]
  · have hji : j ≤ i := (le_of_not_ge hij)
    rw [show ({i,j} : MultiIndex n) = {j,i} from Multiset.pair_comm i j,
      Multiset.insert_eq_cons, Multiset.sort_cons j {i} (· ≤ ·) (by simpa using hji),Multiset.sort_singleton]
    exact partialWord_two_swap hu i j

lemma c2HolderOn_to_upToOn {n : ℕ} {α : ℝ} {u : Space n → ℝ} {s : Set (Space n)}
    (hu : ContDiff ℝ 2 u) (hUnique : UniqueDiffOn ℝ s) (hHolder : IsC2HolderOn α u s) :
    IsC2HolderUpToOn α u s := by
  have hfirst (i : Fin n) : EqOn (firstPartialWithin u s i) (multiPartial u {i}) s := by
    intro x hx
    simp only [firstPartialWithin, P102.U4.multiPartial,
      Multiset.sort_singleton,P102.U4.partialWord]
    rw [fderivWithin_eq_fderiv (hUnique x hx) (hu.differentiable (by norm_num) x)]
  have hsecond (i j : Fin n) : EqOn (secondPartialWithin u s i j) (multiPartial u {i,j}) s := by
    intro x hx
    unfold secondPartialWithin
    rw [fderivWithin_congr' (hfirst j) hx]
    have hd : DifferentiableAt ℝ (multiPartial u {j}) x := by
      simp only [P102.U4.multiPartial,Multiset.sort_singleton,P102.U4.partialWord]
      exact (((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
        (by norm_num) x)
    rw [fderivWithin_eq_fderiv (hUnique x hx) hd]
    simpa only [P102.U4.multiPartial,Multiset.sort_singleton,P102.U4.partialWord] using
      congrFun (classical_second_eq_multiPartial hu i j) x
  rcases hHolder with ⟨hC2,hb,h1,h2⟩
  refine ⟨hC2,hb,?_,?_⟩
  · intro i
    rcases h1 i with ⟨M,hM,hb⟩
    exact ⟨M,hM,fun x hx => by rw [hfirst i hx]; exact hb x hx⟩
  · intro i j
    rcases h2 i j with ⟨M,H,hM,hH,hb,hh⟩
    refine ⟨M,H,hM,hH,?_,?_⟩
    · intro x hx; rw [hsecond i j hx]; exact hb x hx
    · intro x hx y hy; rw [hsecond i j hx,hsecond i j hy]; exact hh x hx y hy

lemma c2HolderOn_to_upToOn_closedBall {n : ℕ} {α r : ℝ} {z : Space n} (hr : 0 < r)
    {u : Space n → ℝ} (hu : ContDiff ℝ 2 u) (hHolder : IsC2HolderOn α u (closedBall z r)) :
    IsC2HolderUpToOn α u (closedBall z r) :=
  c2HolderOn_to_upToOn hu (uniqueDiffOn_closedBall z hr) hHolder


lemma sphere_smooth_lift_sequence {n : ℕ} {α r : ℝ} {z : Space n}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hr : 0 < r) (g : C(sphere z r,ℝ)) :
    ∃ G : ℕ → C(Space n,ℝ),
      (∀ j, ContDiff ℝ ∞ (G j) ∧ IsC2HolderUpToOn α (G j) (closedBall z r)) ∧
      (∀ j, ∀ ζ : sphere z r, ‖G j ζ - g ζ‖ < 1 / ((j : ℝ)+1)) ∧
      Tendsto (fun j => (G j).restrict (sphere z r)) atTop (𝓝 g) := by
  obtain ⟨G,hG,hGg,hlim⟩ := sphere_smooth_approximation_sequence hr g
  exact ⟨G,fun j => ⟨hG j,smooth_c2HolderUpToOn_closedBall hα hα1 z hr (hG j)⟩,hGg,hlim⟩

end BallApprox

lemma isHolderOn_finset_sum {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {ι : Type*} (I : Finset ι) (f : ι → Space n → ℝ)
    (hf : ∀ i ∈ I, IsHolderOn α (f i) s) :
    IsHolderOn α (fun x => ∑ i ∈ I, f i x) s := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using isHolderOn_const α 0 s
  | @insert i I hi ih =>
    simpa only [Finset.sum_insert hi] using
      isHolderOn_add (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma holderNormOn_zero {n : ℕ} (α : ℝ) (s : Set (Space n)) :
    holderNormOn α (fun _ => 0) s = 0 := by
  exact le_antisymm (by simpa using holderNormOn_const_le α 0 s) (holderNormOn_nonneg _ _ _)

lemma holderNormOn_finset_sum_le {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {ι : Type*} (I : Finset ι) (f : ι → Space n → ℝ)
    (hf : ∀ i ∈ I, IsHolderOn α (f i) s) :
    holderNormOn α (fun x => ∑ i ∈ I, f i x) s ≤ ∑ i ∈ I, holderNormOn α (f i) s := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [holderNormOn_zero]
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (holderNormOn_add_le (hf i (Finset.mem_insert_self _ _))
      (isHolderOn_finset_sum I f (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).trans
        (add_le_add le_rfl (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

lemma isHolderOn_nondivergenceOperator {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u : Space n → ℝ} (hc : CoefficientsHolderOn α a b c s)
    (hu : IsHolderOn α u s) (h1 : ∀ i, IsHolderOn α (firstPartial u i) s)
    (h2 : ∀ i j, IsHolderOn α (secondPartial u i j) s) :
    IsHolderOn α (nondivergenceOperator a b c u) s := by
  exact isHolderOn_add (isHolderOn_add
    (isHolderOn_finset_sum Finset.univ _ (fun i _ =>
      isHolderOn_finset_sum Finset.univ _ (fun j _ => isHolderOn_mul (hc.1 i j) (h2 i j))))
    (isHolderOn_finset_sum Finset.univ _ (fun i _ => isHolderOn_mul (hc.2.1 i) (h1 i))))
    (isHolderOn_mul hc.2.2 hu)

lemma holderNormOn_nondivergenceOperator_le {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u : Space n → ℝ} (hc : CoefficientsHolderOn α a b c s)
    (hu : IsHolderOn α u s) (h1 : ∀ i, IsHolderOn α (firstPartial u i) s)
    (h2 : ∀ i j, IsHolderOn α (secondPartial u i j) s) :
    holderNormOn α (nondivergenceOperator a b c u) s ≤
      (∑ i : Fin n, ∑ j : Fin n,
        holderNormOn α (fun x => a x i j) s * holderNormOn α (secondPartial u i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s * holderNormOn α (firstPartial u i) s) +
      holderNormOn α c s * holderNormOn α u s := by
  let A : Space n → ℝ := fun x => ∑ i : Fin n, ∑ j : Fin n, a x i j * secondPartial u i j x
  let B : Space n → ℝ := fun x => ∑ i : Fin n, b x i * firstPartial u i x
  let D : Space n → ℝ := fun x => c x * u x
  have hA : IsHolderOn α A s := isHolderOn_finset_sum Finset.univ _ (fun i _ =>
    isHolderOn_finset_sum Finset.univ _ (fun j _ => isHolderOn_mul (hc.1 i j) (h2 i j)))
  have hB : IsHolderOn α B s := isHolderOn_finset_sum Finset.univ _ (fun i _ =>
    isHolderOn_mul (hc.2.1 i) (h1 i))
  have hD : IsHolderOn α D s := isHolderOn_mul hc.2.2 hu
  have hAnorm : holderNormOn α A s ≤ ∑ i : Fin n, ∑ j : Fin n,
      holderNormOn α (fun x => a x i j) s * holderNormOn α (secondPartial u i j) s := by
    apply (holderNormOn_finset_sum_le Finset.univ _ (fun i _ =>
      isHolderOn_finset_sum Finset.univ _ (fun j _ => isHolderOn_mul (hc.1 i j) (h2 i j)))).trans
    apply Finset.sum_le_sum
    intro i hi
    exact (holderNormOn_finset_sum_le Finset.univ _
      (fun j _ => isHolderOn_mul (hc.1 i j) (h2 i j))).trans
        (Finset.sum_le_sum (fun j _ => holderNormOn_mul_le (hc.1 i j) (h2 i j)))
  have hBnorm : holderNormOn α B s ≤ ∑ i : Fin n,
      holderNormOn α (fun x => b x i) s * holderNormOn α (firstPartial u i) s := by
    exact (holderNormOn_finset_sum_le Finset.univ _
      (fun i _ => isHolderOn_mul (hc.2.1 i) (h1 i))).trans
        (Finset.sum_le_sum (fun i _ => holderNormOn_mul_le (hc.2.1 i) (h1 i)))
  exact ((holderNormOn_add_le (isHolderOn_add hA hB) hD).trans
    (add_le_add (holderNormOn_add_le hA hB) le_rfl)).trans
      (add_le_add (add_le_add hAnorm hBnorm) (holderNormOn_mul_le hc.2.2 hu))

lemma lower_order_holder_jets_on_closedBall {n : ℕ} {α r : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (z : Space n) (hr : 0 < r)
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u (closedBall z r)) :
    IsHolderOn α u (closedBall z r) ∧
      ∀ i, IsHolderOn α (firstPartialWithin u (closedBall z r) i) (closedBall z r) := by
  have hs : UniqueDiffOn ℝ (closedBall z r) := uniqueDiffOn_convex (convex_closedBall z r)
    ⟨z, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds z hr)⟩
  constructor
  · obtain ⟨L, hL⟩ := hu.1.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall z r) (isCompact_closedBall z r)
    exact BallGeometry.holder_of_bounded_lipschitz hα hα1 hu.2.1 hL
  · intro i
    have hdi : ContDiffOn ℝ 1 (firstPartialWithin u (closedBall z r) i) (closedBall z r) :=
      (hu.1.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
    obtain ⟨L, hL⟩ := hdi.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall z r) (isCompact_closedBall z r)
    exact BallGeometry.holder_of_bounded_lipschitz hα hα1 (hu.2.2.1 i) hL


/-- The differential expression evaluated using the genuine jets within s.
It supplies the Hölder boundary representative of the classical operator. -/
def nondivergenceWithinOperator {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c u : Space n → ℝ) (s : Set (Space n)) (x : Space n) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, a x i j * secondPartialWithin u s i j x) +
    (∑ i : Fin n, b x i * firstPartialWithin u s i x) + c x * u x

lemma firstPartialWithin_eq_of_mem_interior {n : ℕ} (u : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hx : x ∈ interior s) (i : Fin n) :
    firstPartialWithin u s i x = firstPartial u i x := by
  exact congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinate n i))
    (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx))

lemma secondPartialWithin_eq_of_mem_interior {n : ℕ} (u : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hx : x ∈ interior s) (i j : Fin n) :
    secondPartialWithin u s i j x = secondPartial u i j x := by
  have heq : firstPartialWithin u s j =ᶠ[nhds x] firstPartial u j := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact firstPartialWithin_eq_of_mem_interior u hy j
  change fderivWithin ℝ (firstPartialWithin u s j) s x (coordinate n i) =
    fderiv ℝ (firstPartial u j) x (coordinate n i)
  rw [fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx), heq.fderiv_eq]

lemma nondivergenceWithinOperator_eq_of_mem_interior {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c u : Space n → ℝ) {s : Set (Space n)} {x : Space n} (hx : x ∈ interior s) :
    nondivergenceWithinOperator a b c u s x = nondivergenceOperator a b c u x := by
  simp only [nondivergenceWithinOperator, nondivergenceOperator,
    firstPartialWithin_eq_of_mem_interior u hx, secondPartialWithin_eq_of_mem_interior u hx]

lemma nondivergenceWithinOperator_holder_on_closedBall {n : ℕ} {α r : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (z : Space n) (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hu : IsC2HolderUpToOn α u (closedBall z r)) :
    IsHolderOn α (nondivergenceWithinOperator a b c u (closedBall z r)) (closedBall z r) := by
  have hjet := lower_order_holder_jets_on_closedBall hα hα1 z hr hu
  exact isHolderOn_add (isHolderOn_add
    (isHolderOn_finset_sum Finset.univ _ (fun i _ =>
      isHolderOn_finset_sum Finset.univ _ (fun j _ => isHolderOn_mul (hc.1 i j) (hu.2.2.2 i j))))
    (isHolderOn_finset_sum Finset.univ _ (fun i _ => isHolderOn_mul (hc.2.1 i) (hjet.2 i))))
    (isHolderOn_mul hc.2.2 hjet.1)

lemma nondivergenceOperator_holder_extension_on_closedBall {n : ℕ} {α r : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (z : Space n) (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hu : IsC2HolderUpToOn α u (closedBall z r)) :
    ∃ F : Space n → ℝ, IsHolderOn α F (closedBall z r) ∧
      EqOn F (nondivergenceOperator a b c u) (ball z r) := by
  refine ⟨nondivergenceWithinOperator a b c u (closedBall z r),
    nondivergenceWithinOperator_holder_on_closedBall hα hα1 z hr hc hu, ?_⟩
  intro x hx
  exact nondivergenceWithinOperator_eq_of_mem_interior a b c u
    (mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall))


lemma exists_compactlySupported_holder_extension_norm {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (z : Space n) {r : ℝ} (hr : 0 ≤ r)
    {f : Space n → ℝ} (hf : IsHolderOn α f (closedBall z r)) :
    ∃ F : Space n → ℝ, HasCompactSupport F ∧ tsupport F ⊆ closedBall z (r+1) ∧
      IsHolder α F ∧ EqOn F f (closedBall z r) ∧
      holderNorm α F ≤ 4 * holderNormOn α f (closedBall z r) := by
  obtain ⟨hN,hb,hh⟩ := P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn hf
  obtain ⟨F,hc,hsupp,hF,heq⟩ :=
    exists_compactlySupported_holder_extension_bounds hα hα1 z hr hN hN hb hh
  refine ⟨F,hc,hsupp,⟨_,_,hF⟩,heq,?_⟩
  have hnorm := P201.Elliptic.HolderCancellation.holderNorm_le hn hF
  linarith

lemma laplacian_interval_global_solution {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r) {f : Space 1 → ℝ}
    (hf : IsHolderOn α f (closedBall z r)) (g : C(sphere z r, ℝ)) :
    ∃ u : Space 1 → ℝ, IsC2HolderLoc α u ∧
      (∀ x ∈ closedBall z r, P201Specs.laplacian u x = f x) ∧
      (∀ ζ : sphere z r, u ζ = g ζ) := by
  obtain ⟨F,hc,hsupp,hF,hagree⟩ :=
    exists_compactlySupported_holder_extension hα.le hα1.le z hr.le hf
  obtain ⟨C,hC,hest⟩ := P201.Elliptic.NewtonHessian.potentialEstimate (by omega) α hα hα1
    (∅ : Set (Space 1)) Bornology.isBounded_empty z (r+1) (by linarith)
  have hw : ContDiff ℝ 2 (holderPotential F) := (hest F hc hsupp hF).1.1
  let k : C(sphere z r, ℝ) := g +
    ⟨fun ζ => holderPotential F ζ, hw.continuous.comp continuous_subtype_val⟩
  obtain ⟨h,hh,heq,htrace⟩ := interval_harmonic_extension z hr k
  let u := h-holderPotential F
  have hu : ContDiff ℝ 2 u := hh.sub hw
  have hueq (x : Space 1) : P201Specs.laplacian u x = F x := by
    change P201Specs.laplacian (h-holderPotential F) x = F x
    rw [P201.MeanValues.laplacian_bridge (h-holderPotential F) x (hh.contDiffAt.sub hw.contDiffAt),
      hh.contDiffAt.laplacian_sub hw.contDiffAt,
      ← P201.MeanValues.laplacian_bridge _ _ hh.contDiffAt,
      ← P201.MeanValues.laplacian_bridge _ _ hw.contDiffAt]
    have hheq := heq x
    have hwq := P201.Elliptic.PoissonSchauder.potential_equation (by omega) α hα hα1 F hc hF x
    linarith
  have hjet : multiPartial u ({0,0} : MultiIndex 1) = F := by
    funext x
    simpa only [P201Specs.laplacian, Fin.sum_univ_one] using hueq x
  refine ⟨u,⟨hu,?_⟩,fun x hx => (hueq x).trans (hagree hx),?_⟩
  · intro s _ i j
    fin_cases i
    fin_cases j
    change IsHolderOn α (multiPartial u ({0,0} : MultiIndex 1)) s
    rw [hjet]
    exact P201.Elliptic.NewtonHessian.isHolderOn_of_isHolder hF s
  · intro ζ
    change h ζ-holderPotential F ζ = g ζ
    have htq := htrace ζ
    change h ζ = g ζ+holderPotential F ζ at htq
    linarith

lemma isC2HolderUpToOn_closedBall_of_isC2HolderLoc {n : ℕ} {α : ℝ}
    {u : Space n → ℝ} (hu : IsC2HolderLoc α u) (z : Space n) {r : ℝ} (hr : 0 < r) :
    P201Specs.Elliptic.ConstantSchauder.IsC2HolderUpToOn α u (closedBall z r) := by
  exact BallApprox.c2HolderOn_to_upToOn_closedBall hr hu.1
    (P201.Elliptic.PoissonSchauder.c2HolderOn_of_global hu isBounded_closedBall)

lemma laplacian_interval_solution_upTo {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r) {f : Space 1 → ℝ}
    (hf : IsHolderOn α f (closedBall z r)) (g : C(sphere z r, ℝ)) :
    ∃ u : Space 1 → ℝ,
      P201Specs.Elliptic.ConstantSchauder.IsC2HolderUpToOn α u (closedBall z r) ∧
      (∀ x ∈ closedBall z r, P201Specs.laplacian u x = f x) ∧
      (∀ ζ : sphere z r, u ζ = g ζ) := by
  obtain ⟨u,hu,heq,hg⟩ := laplacian_interval_global_solution hα hα1 z hr hf g
  exact ⟨u,isC2HolderUpToOn_closedBall_of_isC2HolderLoc hu z hr,heq,hg⟩

lemma exists_newton_potential_upTo_closedBall {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (z : Space n) {r : ℝ} (hr : 0 < r)
    {f : Space n → ℝ} (hf : IsHolderOn α f (closedBall z r)) :
    ∃ w : Space n → ℝ,
      P201Specs.Elliptic.ConstantSchauder.IsC2HolderUpToOn α w (closedBall z r) ∧
      (∀ x ∈ closedBall z r, -P201Specs.laplacian w x = f x) := by
  obtain ⟨F,hc,hsupp,hF,hagree⟩ :=
    exists_compactlySupported_holder_extension hα.le hα1.le z hr.le hf
  obtain ⟨C,hC,hest⟩ := P201.Elliptic.NewtonHessian.potentialEstimate hn α hα hα1
    (∅ : Set (Space n)) Bornology.isBounded_empty z (r+1) (by linarith)
  have hw : IsC2HolderLoc α (holderPotential F) := (hest F hc hsupp hF).1
  refine ⟨holderPotential F,isC2HolderUpToOn_closedBall_of_isC2HolderLoc hw z hr,?_⟩
  intro x hx
  exact (P201.Elliptic.PoissonSchauder.potential_equation hn α hα hα1 F hc hF x).trans (hagree hx)

lemma nondivergenceOperator_identity {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    nondivergenceOperator (fun _ i j => if i = j then 1 else 0)
      (fun _ => 0) (fun _ => 0) u x = P201Specs.laplacian u x := by
  simp only [nondivergenceOperator, PiLp.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    secondPartial_diagonal_eq_multiPartial]

lemma identity_uniformlyEllipticOn {n : ℕ} (s : Set (Space n)) :
    UniformlyEllipticOn 1 (fun _ i j => if i = j then 1 else 0) s := by
  refine ⟨fun x hx i j => by simp [eq_comm], fun x hx ξ => ?_⟩
  have h := pathPrincipal_quadratic_form (fun _ i j => (0 : ℝ)) 0 x ξ
  simpa only [pathPrincipal, sub_zero, one_mul, zero_mul, add_zero] using h.ge

/-- The continuous-data ball result is unconditional for the Laplacian,
including the interval case. The ambient representative is unique on the
closed ball among all classical interior solutions continuous there. -/
lemma laplacian_ball_continuous_solvability {n : ℕ} (hn : 1 ≤ n)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r) {f : Space n → ℝ}
    (hf : IsHolderOn α f (closedBall z r)) (g : C(sphere z r, ℝ)) :
    ∃ u : Space n → ℝ,
      IsBallSolution (fun _ i j => if i = j then 1 else 0) (fun _ => 0) (fun _ => 0) f z r g u ∧
      IsC2HolderLocOn α u (ballDomain z r) ∧
      ∀ v : Space n → ℝ,
        IsBallSolution (fun _ i j => if i = j then 1 else 0) (fun _ => 0) (fun _ => 0) f z r g v →
          EqOn v u (closedBall z r) := by
  obtain ⟨u,hu,hcl,heq,htrace,hh⟩ := laplacian_ball_classical_solution hn hα hα1 z hr hf g
  have hcoeff : CoefficientsHolderOn α
      (fun _ : Space n => fun i j => if i=j then 1 else 0) (fun _ => 0) (fun _ => 0)
      (closedBall z r) := by
    exact ⟨fun i j => isHolderOn_const α _ _, fun i => isHolderOn_const α 0 _, isHolderOn_const α 0 _⟩
  have hsol : IsBallSolution (fun _ i j => if i=j then 1 else 0) (fun _ => 0) (fun _ => 0) f z r g u :=
    ⟨hu,hcl,fun x hx => (nondivergenceOperator_identity u x).trans (heq x hx),htrace⟩
  refine ⟨u,hsol,hh,fun v hv => ?_⟩
  exact ball_solution_unique_of_holder hn hα hr
    ⟨1,zero_lt_one,identity_uniformlyEllipticOn _⟩ hcoeff (by simp) hv hsol


lemma secondPartial_eq_multiPartial_at {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin n) :
    secondPartial u i j x = multiPartial u {i,j} x := by
  have hswap : secondPartial u i j x = secondPartial u j i x := by
    have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [secondPartial_eq_fderiv_fderiv hd i j, secondPartial_eq_fderiv_fderiv hd j i]
    exact hu.isSymmSndFDerivAt (by norm_num) (coordinate n i) (coordinate n j)
  change P102.U4.partialWord u [i,j] x = P102.U4.partialWord u (({i,j} : MultiIndex n).sort (· ≤ ·)) x
  by_cases hij : i ≤ j
  · rw [Multiset.insert_eq_cons, Multiset.sort_cons i {j} (· ≤ ·) (by simpa using hij), Multiset.sort_singleton]
  · rw [show ({i,j} : MultiIndex n) = {j,i} from Multiset.pair_comm i j,
      Multiset.insert_eq_cons, Multiset.sort_cons j {i} (· ≤ ·) (by simpa using le_of_not_ge hij), Multiset.sort_singleton]
    exact hswap

/-- Canonical second multi-index derivatives converge to the corresponding
actual derivatives of the limit, when genuine derivative fields converge. -/
lemma multiPartial_pair_tendsto {n : ℕ} {s : Set (Space n)} (hs : IsOpen s)
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) s)
    (h₀ : ∀ x ∈ s, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {A : Space n → Space n →L[ℝ] ℝ}
    {B : Space n → Space n →L[ℝ] (Space n →L[ℝ] ℝ)}
    (h₁ : TendstoUniformlyOn (fun j => fderiv ℝ (u j)) A atTop s)
    (h₂ : TendstoUniformlyOn (fun j => fderiv ℝ (fderiv ℝ (u j))) B atTop s)
    {x : Space n} (hx : x ∈ s) (i j : Fin n) :
    Tendsto (fun k => multiPartial (u k) {i,j} x) atTop
      (𝓝 (multiPartial v {i,j} x)) := by
  obtain ⟨hv,hA,hB⟩ := contDiffOn_two_of_uniform_derivative_limits hs hu h₀ h₁ h₂
  have hregular (k : ℕ) : DifferentiableAt ℝ (fderiv ℝ (u k)) x :=
    ((hu k).fderiv_of_isOpen hs (m := 1) (by norm_num)).contDiffAt
      (hs.mem_nhds hx) |>.differentiableAt (by norm_num)
  have hvregular : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_of_isOpen hs (m := 1) (by norm_num)).contDiffAt
      (hs.mem_nhds hx) |>.differentiableAt (by norm_num)
  simp_rw [← secondPartial_eq_multiPartial_at ((hu _).contDiffAt (hs.mem_nhds hx)) i j,
    secondPartial_eq_fderiv_fderiv (hregular _) i j]
  rw [← secondPartial_eq_multiPartial_at (hv.contDiffAt (hs.mem_nhds hx)) i j,
    secondPartial_eq_fderiv_fderiv hvregular i j, hB hx]
  exact ((ContinuousLinearMap.apply ℝ ℝ (coordinate n j)).continuous.tendsto _).comp
    (((ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) (coordinate n i)).continuous.tendsto _).comp
      (h₂.tendsto_at hx))

/-- Hölder bounds on the actual Hessians pass to the C² limit. All pairs
in the observation set are retained, including disconnected sets. -/
lemma hessian_holder_of_uniform_derivative_limits {n : ℕ} {α M H : ℝ}
    {s t : Set (Space n)} (hs : IsOpen s) (ht : t ⊆ s)
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) s)
    (h₀ : ∀ x ∈ s, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {A : Space n → Space n →L[ℝ] ℝ}
    {B : Space n → Space n →L[ℝ] (Space n →L[ℝ] ℝ)}
    (h₁ : TendstoUniformlyOn (fun j => fderiv ℝ (u j)) A atTop s)
    (h₂ : TendstoUniformlyOn (fun j => fderiv ℝ (fderiv ℝ (u j))) B atTop s)
    (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hb : ∀ k i j, ∀ x ∈ t, ‖multiPartial (u k) {i,j} x‖ ≤ M)
    (hh : ∀ k i j, ∀ x ∈ t, ∀ y ∈ t,
      ‖multiPartial (u k) {i,j} x - multiPartial (u k) {i,j} y‖ ≤ H * dist x y ^ α) :
    ∀ i j : Fin n, IsHolderOn α (multiPartial v {i,j}) t := by
  intro i j
  exact isHolderOn_of_pointwise_limit hM hH (fun k => hb k i j) (fun k => hh k i j)
    (fun x hx => multiPartial_pair_tendsto hs hu h₀ h₁ h₂ (ht hx) i j)

lemma exists_uniform_limit_of_uniformCauchySeqOn
    {X F : Type*} [UniformSpace F] [CompleteSpace F] [Nonempty F]
    {u : ℕ → X → F} {s : Set X} (hu : UniformCauchySeqOn u atTop s) :
    ∃ v : X → F, TendstoUniformlyOn u v atTop s := by
  classical
  have hlim (x : X) : ∃ v : F, x ∈ s → Tendsto (fun j => u j x) atTop (𝓝 v) := by
    by_cases hx : x ∈ s
    · obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete (hu.cauchySeq hx)
      exact ⟨v,fun _ => hv⟩
    · exact ⟨Classical.choice inferInstance,fun h => (hx h).elim⟩
  choose v hv using hlim
  exact ⟨v,hu.tendstoUniformlyOn_of_tendsto hv⟩

/-- Completeness of the two derivative fields suffices to obtain actual C²
regularity of the pointwise limit; no differentiability of that limit is a
premise. -/
lemma contDiffOn_two_of_uniformCauchy_derivatives
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) {u : ℕ → E → F} {v : E → F}
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) s)
    (h₀ : ∀ x ∈ s, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    (h₁ : UniformCauchySeqOn (fun j => fderiv ℝ (u j)) atTop s)
    (h₂ : UniformCauchySeqOn (fun j => fderiv ℝ (fderiv ℝ (u j))) atTop s) :
    ContDiffOn ℝ 2 v s := by
  obtain ⟨A,hA⟩ := exists_uniform_limit_of_uniformCauchySeqOn h₁
  obtain ⟨B,hB⟩ := exists_uniform_limit_of_uniformCauchySeqOn h₂
  exact (contDiffOn_two_of_uniform_derivative_limits hs hu h₀ hA hB).1

lemma equation_of_uniformCauchy_derivatives {n : ℕ} {s : Set (Space n)} (hs : IsOpen s)
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) s)
    (h₀ : ∀ x ∈ s, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    (h₁ : UniformCauchySeqOn (fun j => fderiv ℝ (u j)) atTop s)
    (h₂ : UniformCauchySeqOn (fun j => fderiv ℝ (fderiv ℝ (u j))) atTop s)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n) (c f : Space n → ℝ)
    (hL : ∀ j, ∀ x ∈ s, nondivergenceOperator a b c (u j) x = f x) :
    ∀ x ∈ s, nondivergenceOperator a b c v x = f x := by
  obtain ⟨A,hA⟩ := exists_uniform_limit_of_uniformCauchySeqOn h₁
  obtain ⟨B,hB⟩ := exists_uniform_limit_of_uniformCauchySeqOn h₂
  exact equation_of_uniform_derivative_limits hs hu h₀ hA hB a b c f hL

/-- Local completeness and preservation of the Hölder Hessian bound on
open neighborhoods. This is the derivative-limit bridge used after interior
Schauder estimates have made the approximating solutions Cauchy. -/
lemma isC2HolderLocOn_of_local_uniformCauchy_derivatives
    {n : ℕ} {α : ℝ} {Ω : Domain n} {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) Ω)
    (h₀ : ∀ x ∈ Ω, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    (hlocal : ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ (Ω : Set (Space n)) ∧
      UniformCauchySeqOn (fun j => fderiv ℝ (u j)) atTop (ball x r) ∧
      UniformCauchySeqOn (fun j => fderiv ℝ (fderiv ℝ (u j))) atTop (ball x r) ∧
      ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧
        (∀ k i j, ∀ y ∈ ball x r, ‖multiPartial (u k) {i,j} y‖ ≤ M) ∧
        (∀ k i j, ∀ y ∈ ball x r, ∀ z ∈ ball x r,
          ‖multiPartial (u k) {i,j} y - multiPartial (u k) {i,j} z‖ ≤ H * dist y z ^ α)) :
    IsC2HolderLocOn α v Ω := by
  have hv : ContDiffOn ℝ 2 v Ω := by
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    obtain ⟨r,hr,hsub,hc1,hc2,hrest⟩ := hlocal x hx
    have hC2 := contDiffOn_two_of_uniformCauchy_derivatives isOpen_ball
      (fun j => (hu j).mono hsub) (fun y hy => h₀ y (hsub hy)) hc1 hc2
    exact ⟨ball x r,isOpen_ball,mem_ball_self hr,hC2.mono inter_subset_right⟩
  refine ⟨hv,?_⟩
  intro x hx
  obtain ⟨r,hr,hsub,hc1,hc2,M,H,hM,hH,hb,hh⟩ := hlocal x hx
  obtain ⟨A,hA⟩ := exists_uniform_limit_of_uniformCauchySeqOn hc1
  obtain ⟨B,hB⟩ := exists_uniform_limit_of_uniformCauchySeqOn hc2
  exact ⟨r,hr,hsub,hessian_holder_of_uniform_derivative_limits isOpen_ball Subset.rfl
    (fun j => (hu j).mono hsub) (fun y hy => h₀ y (hsub hy)) hA hB hM hH hb hh⟩

namespace BallHolderSpace
open P201Specs P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder

abbrev DistinctPairs {n : ℕ} (s : Set (Space n)) :=
  {p : s × s // p.1 ≠ p.2}

abbrev Ambient {n : ℕ} (s : Set (Space n)) :=
  C(s,ℝ) × lp (fun _ : DistinctPairs s => ℝ) ∞

def graphSubmodule {n : ℕ} (α : ℝ) (s : Set (Space n)) : Submodule ℝ (Ambient s) where
  carrier := {v | ∀ p : DistinctPairs s,
    v.2 p * dist (p.val.1 : Space n) p.val.2 ^ α = v.1 p.val.1 - v.1 p.val.2}
  zero_mem' := by intro p; simp
  add_mem' := by
    intro u v hu hv p
    change (u.2 p+v.2 p) * _ = (u.1 p.val.1+v.1 p.val.1) - (u.1 p.val.2+v.1 p.val.2)
    rw [add_mul,hu p,hv p]
    ring
  smul_mem' := by
    intro c v hv p
    change (c*v.2 p) * _ = c*v.1 p.val.1-c*v.1 p.val.2
    rw [mul_assoc,hv p]
    ring

variable {n : ℕ} {s : Set (Space n)} [CompactSpace s]

omit [CompactSpace s] in
lemma graphSubmodule_isClosed (α : ℝ) : IsClosed (graphSubmodule α s : Set (Ambient s)) := by
  change IsClosed {v : Ambient s | ∀ p : DistinctPairs s,
    v.2 p * dist (p.val.1 : Space n) p.val.2 ^ α = v.1 p.val.1 - v.1 p.val.2}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro p
  apply isClosed_eq
  · exact ((lp.evalCLM ℝ (fun _ : DistinctPairs s => ℝ) ∞ p).continuous.comp continuous_snd).mul continuous_const
  · exact ((ContinuousMap.evalCLM ℝ p.val.1).continuous.comp continuous_fst).sub
      ((ContinuousMap.evalCLM ℝ p.val.2).continuous.comp continuous_fst)

abbrev HolderSpace (α : ℝ) (s : Set (Space n)) := graphSubmodule α s

instance (α : ℝ) : CompleteSpace (HolderSpace α s) :=
  (graphSubmodule_isClosed α).completeSpace_coe


def quotient (α : ℝ) (f : Space n → ℝ) (p : DistinctPairs s) : ℝ :=
  (f p.val.1-f p.val.2) / dist (p.val.1 : Space n) p.val.2 ^ α

omit [CompactSpace s] in
lemma pair_dist_pos (p : DistinctPairs s) : 0 < dist (p.val.1 : Space n) p.val.2 := by
  apply dist_pos.mpr
  intro he
  exact p.property (Subtype.ext he)

omit [CompactSpace s] in
lemma quotient_bound {α : ℝ} {f : Space n → ℝ} {H : ℝ}
    (hh : ∀ x ∈ s, ∀ y ∈ s, ‖f x-f y‖ ≤ H * dist x y ^ α)
    (p : DistinctPairs s) : ‖quotient α f p‖ ≤ H := by
  have hd := Real.rpow_pos_of_pos (pair_dist_pos p) α
  simp only [quotient,norm_div,Real.norm_eq_abs,abs_of_pos hd]
  exact (div_le_iff₀ hd).mpr (hh _ p.val.1.property _ p.val.2.property)

noncomputable def ofHolder {α : ℝ} (hα : 0 < α) {f : Space n → ℝ}
    (hf : IsHolderOn α f s) : HolderSpace α s := by
  let F : C(s,ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp (continuousOn_of_isHolderOn hα hf)⟩
  have hq : Memℓp (quotient α f : DistinctPairs s → ℝ) ∞ := by
    obtain ⟨M,H,hM,hH,hb,hh⟩ := hf
    apply memℓp_infty
    exact ⟨H,by rintro _ ⟨p,rfl⟩; exact quotient_bound hh p⟩
  refine ⟨(F,⟨quotient α f,hq⟩),?_⟩
  intro p
  change (f p.val.1-f p.val.2) / dist (p.val.1 : Space n) p.val.2 ^ α * _ = _
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos (pair_dist_pos p) α).ne'

omit [CompactSpace s] in
@[simp] lemma ofHolder_apply {α : ℝ} (hα : 0 < α) {f : Space n → ℝ}
    (hf : IsHolderOn α f s) (x : s) : (ofHolder hα hf).val.1 x = f x := rfl

lemma holder_of_representation {α : ℝ} (v : HolderSpace α s) {f : Space n → ℝ}
    (hrep : ∀ x : s, v.val.1 x = f x) : IsHolderOn α f s := by
  refine ⟨‖v.val.1‖,‖v.val.2‖,norm_nonneg _,norm_nonneg _,?_,?_⟩
  · intro x hx
    rw [← hrep ⟨x,hx⟩]
    exact v.val.1.norm_coe_le_norm ⟨x,hx⟩
  · intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simp only [sub_self,norm_zero]
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)
    · let p : DistinctPairs s := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun he => hxy (congrArg Subtype.val he)⟩
      have hv := v.property p
      change v.val.2 p * dist x y ^ α = v.val.1 ⟨x,hx⟩ - v.val.1 ⟨y,hy⟩ at hv
      rw [hrep,hrep] at hv
      rw [← hv]
      simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)]
      exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero v.val.2 p)
        (Real.rpow_nonneg dist_nonneg _)

lemma isHolderOn_iff_represented {α : ℝ} (hα : 0 < α) {f : Space n → ℝ} :
    IsHolderOn α f s ↔ ∃ v : HolderSpace α s, ∀ x : s, v.val.1 x = f x := by
  constructor
  · intro hf
    exact ⟨ofHolder hα hf,ofHolder_apply hα hf⟩
  · rintro ⟨v,hv⟩
    exact holder_of_representation v hv

noncomputable def representative {α : ℝ} (v : HolderSpace α s) (x : Space n) : ℝ :=
  by classical exact if hx : x ∈ s then v.val.1 ⟨x,hx⟩ else 0

omit [CompactSpace s] in
@[simp] lemma representative_apply {α : ℝ} (v : HolderSpace α s) (x : s) :
    representative v x = v.val.1 x := by simp [representative,x.property]

lemma representative_isHolderOn {α : ℝ} (v : HolderSpace α s) :
    IsHolderOn α (representative v) s :=
  holder_of_representation v (fun x => (representative_apply v x).symm)


omit [CompactSpace s] in
lemma quotient_eq_snd {α : ℝ} (v : HolderSpace α s) {f : Space n → ℝ}
    (hrep : ∀ x : s, v.val.1 x = f x) (p : DistinctPairs s) :
    quotient α f p = v.val.2 p := by
  apply (div_eq_iff (Real.rpow_pos_of_pos (pair_dist_pos p) α).ne').mpr
  rw [← hrep,← hrep]
  exact (v.property p).symm

omit [CompactSpace s] in
lemma quotient_norm_eq (α : ℝ) (f : Space n → ℝ) (p : DistinctPairs s) :
    ‖quotient α f p‖ = ‖f p.val.1-f p.val.2‖ / dist (p.val.1 : Space n) p.val.2 ^ α := by
  rw [quotient,norm_div,Real.norm_of_nonneg (Real.rpow_nonneg dist_nonneg _)]

lemma fst_norm_eq_supNormOn {α : ℝ} (v : HolderSpace α s) {f : Space n → ℝ}
    (hrep : ∀ x : s, v.val.1 x = f x) : ‖v.val.1‖ = supNormOn f s := by
  have hb : BddAbove {t : ℝ | ∃ x ∈ s, t = ‖f x‖} := by
    refine ⟨‖v.val.1‖,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    rw [← hrep ⟨x,hx⟩]
    exact v.val.1.norm_coe_le_norm ⟨x,hx⟩
  have hsup : 0 ≤ supNormOn f s := Real.sSup_nonneg (by rintro _ ⟨x,hx,rfl⟩; exact norm_nonneg _)
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ hsup).mpr
    intro x
    rw [hrep x]
    exact le_csSup hb ⟨x,x.property,rfl⟩
  · apply Real.sSup_le _ (norm_nonneg _)
    rintro _ ⟨x,hx,rfl⟩
    rw [← hrep ⟨x,hx⟩]
    exact v.val.1.norm_coe_le_norm ⟨x,hx⟩

omit [CompactSpace s] in
lemma snd_norm_eq_holderSeminormOn {α : ℝ} (v : HolderSpace α s) {f : Space n → ℝ}
    (hrep : ∀ x : s, v.val.1 x = f x) : ‖v.val.2‖ = holderSeminormOn α f s := by
  have raw_bound {x y : Space n} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
      ‖f x-f y‖ / dist x y ^ α ≤ ‖v.val.2‖ := by
    let p : DistinctPairs s := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun he => hxy (congrArg Subtype.val he)⟩
    have hh : ‖f x-f y‖ / dist x y ^ α = ‖v.val.2 p‖ := by
      rw [← quotient_eq_snd v hrep p, quotient_norm_eq]
    rw [hh]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero v.val.2 p
  have hb : BddAbove {t : ℝ | ∃ x ∈ s, ∃ y ∈ s,
      x ≠ y ∧ t = ‖f x-f y‖ / dist x y ^ α} := by
    exact ⟨‖v.val.2‖,by rintro _ ⟨x,hx,y,hy,hxy,rfl⟩; exact raw_bound hx hy hxy⟩
  have hsup : 0 ≤ holderSeminormOn α f s := Real.sSup_nonneg (by
    rintro _ ⟨x,hx,y,hy,hxy,rfl⟩
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _))
  apply le_antisymm
  · apply lp.norm_le_of_forall_le hsup
    intro p
    rw [← quotient_eq_snd v hrep p, quotient_norm_eq]
    exact le_csSup hb ⟨p.val.1,p.val.1.property,p.val.2,p.val.2.property,
      dist_pos.mp (pair_dist_pos p),rfl⟩
  · apply Real.sSup_le _ (norm_nonneg _)
    rintro _ ⟨x,hx,y,hy,hxy,rfl⟩
    exact raw_bound hx hy hxy

lemma holderNormOn_eq_sum_norm {α : ℝ} (v : HolderSpace α s) {f : Space n → ℝ}
    (hrep : ∀ x : s, v.val.1 x = f x) :
    holderNormOn α f s = ‖v.val.1‖+‖v.val.2‖ := by
  rw [fst_norm_eq_supNormOn v hrep,snd_norm_eq_holderSeminormOn v hrep]
  rfl

lemma norm_le_holderNormOn {α : ℝ} (v : HolderSpace α s) {f : Space n → ℝ}
    (hrep : ∀ x : s, v.val.1 x = f x) : ‖v‖ ≤ holderNormOn α f s := by
  rw [holderNormOn_eq_sum_norm v hrep]
  change max ‖v.val.1‖ ‖v.val.2‖ ≤ _
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

lemma holderNormOn_le_two_norm {α : ℝ} (v : HolderSpace α s) {f : Space n → ℝ}
    (hrep : ∀ x : s, v.val.1 x = f x) : holderNormOn α f s ≤ 2 * ‖v‖ := by
  rw [holderNormOn_eq_sum_norm v hrep]
  have h1 := norm_fst_le v.val
  have h2 := norm_snd_le v.val
  change ‖v.val.1‖+‖v.val.2‖ ≤ 2 * ‖v.val‖
  linarith


omit [CompactSpace s] in
@[ext] lemma ext {α : ℝ} {v w : HolderSpace α s}
    (h : ∀ x : s, v.val.1 x = w.val.1 x) : v = w := by
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMap.ext h
  · apply lp.ext
    funext p
    apply mul_right_cancel₀ (Real.rpow_pos_of_pos (pair_dist_pos p) α).ne'
    rw [v.property p,w.property p,h,h]

noncomputable def valueCLM (α : ℝ) : HolderSpace α s →L[ℝ] C(s,ℝ) :=
  (ContinuousLinearMap.fst ℝ (C(s,ℝ)) (lp (fun _ : DistinctPairs s => ℝ) ∞)).comp
    (graphSubmodule α s).subtypeL

omit [CompactSpace s] in
@[simp] lemma valueCLM_apply {α : ℝ} (v : HolderSpace α s) :
    valueCLM α v = v.val.1 := rfl

omit [CompactSpace s] in
lemma valueCLM_injective (α : ℝ) : Function.Injective (valueCLM (s := s) α) := by
  intro v w h
  apply ext
  intro x
  exact congrArg (fun f : C(s,ℝ) => f x) h

omit [CompactSpace s] in
lemma representative_add {α : ℝ} (v w : HolderSpace α s) :
    representative (v+w) = representative v + representative w := by
  funext x
  classical
  by_cases hx : x ∈ s
  · simp only [Pi.add_apply,representative,dite_eq_left hx]
    rfl
  · simp [representative,hx]

omit [CompactSpace s] in
lemma representative_smul {α : ℝ} (c : ℝ) (v : HolderSpace α s) :
    representative (c • v) = c • representative v := by
  funext x
  classical
  by_cases hx : x ∈ s
  · simp only [Pi.smul_apply,representative,dite_eq_left hx]
    rfl
  · simp [representative,hx]


noncomputable def representativeLinear (α : ℝ) : HolderSpace α s →ₗ[ℝ] (Space n → ℝ) where
  toFun := representative
  map_add' := representative_add
  map_smul' := representative_smul

lemma ofHolder_representative {α : ℝ} (hα : 0 < α) (v : HolderSpace α s) :
    ofHolder hα (representative_isHolderOn v) = v := by
  apply ext
  intro x
  simp only [ofHolder_apply,representative_apply]


set_option backward.isDefEq.respectTransparency false in
lemma holderNormOn_complete {α : ℝ} (hα : 0 < α) (f : ℕ → Space n → ℝ)
    (hf : ∀ j, IsHolderOn α (f j) s)
    (hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      holderNormOn α (f j-f k) s < ε) :
    ∃ g : Space n → ℝ, IsHolderOn α g s ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, holderNormOn α (f j-g) s < ε := by
  let F : ℕ → HolderSpace α s := fun j => ofHolder hα (hf j)
  have hF : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N,hN⟩ := hCauchy ε hε
    refine ⟨N,fun j hj k hk => ?_⟩
    rw [dist_eq_norm]
    have hrep : ∀ x : s, (F j-F k).val.1 x = (f j-f k) x := by intro x; rfl
    exact (norm_le_holderNormOn (F j-F k) hrep).trans_lt (hN j hj k hk)
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hF
  refine ⟨representative v,representative_isHolderOn v,?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hv (ε/2) (half_pos hε)
  refine ⟨N,fun j hj => ?_⟩
  have hrep : ∀ x : s, (F j-v).val.1 x = (f j-representative v) x := by
    intro x
    change (ofHolder hα (hf j)).val.1 x-v.val.1 x = f j x-representative v x
    rw [ofHolder_apply,representative_apply]
  have hbound := holderNormOn_le_two_norm (F j-v) hrep
  have hsmall : ‖F j-v‖ < ε/2 := by simpa only [dist_eq_norm] using hN j hj
  linarith

end BallHolderSpace


lemma norm_clm_le_sum_coordinates {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : Space n →L[ℝ] F) :
    ‖A‖ ≤ ∑ i : Fin n, ‖A (coordinate n i)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (s := Finset.univ) fun i _ => norm_nonneg _)
  intro x
  have he : ∑ i : Fin n, x i • coordinate n i = x :=
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  calc
    ‖A x‖ = ‖A (∑ i : Fin n, x i • coordinate n i)‖ := congrArg (fun z => ‖A z‖) he.symm
    _ = ‖∑ i : Fin n, x i • A (coordinate n i)‖ := by simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin n, ‖x i • A (coordinate n i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖x‖ * ‖A (coordinate n i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = (∑ i : Fin n, ‖A (coordinate n i)‖) * ‖x‖ := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma norm_fderiv_le_sum_multiPartial {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    ‖fderiv ℝ u x‖ ≤ ∑ i : Fin n, ‖multiPartial u {i} x‖ := by
  simpa only [P102.U4.multiPartial,
    Multiset.sort_singleton, P102.U4.partialWord] using
      P201.Elliptic.PoissonSchauder.norm_linearMap_le_sum_coordinates (fderiv ℝ u x)

lemma norm_fderiv_fderiv_le_sum_secondPartial {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖secondPartial u i j x‖ := by
  apply (norm_clm_le_sum_coordinates (fderiv ℝ (fderiv ℝ u) x)).trans
  apply Finset.sum_le_sum
  intro i hi
  simpa only [secondPartial_eq_fderiv_fderiv hu] using
    P201.Elliptic.PoissonSchauder.norm_linearMap_le_sum_coordinates
      (fderiv ℝ (fderiv ℝ u) x (coordinate n i))


lemma norm_fderiv_fderiv_le_sum_multiPartial {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖multiPartial u {i,j} x‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  simpa only [secondPartial_eq_multiPartial_at hu] using
    norm_fderiv_fderiv_le_sum_secondPartial hd

lemma partialWord_neg {n : ℕ} (u : Space n → ℝ) (l : List (Fin n)) :
    P102.U4.partialWord (-u) l = -P102.U4.partialWord u l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    simp only [P102.U4.partialWord, ih, fderiv_neg, neg_apply, Pi.neg_apply]

lemma partialWord_sub_on {n N : ℕ} (Ω : Domain n) {u v : Space n → ℝ}
    (hu : ContDiffOn ℝ (N : ℕ) u Ω) (hv : ContDiffOn ℝ (N : ℕ) v Ω)
    (l : List (Fin n)) (hl : l.length ≤ N) :
    EqOn (P102.U4.partialWord (u - v) l)
      (P102.U4.partialWord u l - P102.U4.partialWord v l) Ω := by
  have h := P201.Elliptic.PoissonSchauder.partialWord_add_on Ω hu
    (show ContDiffOn ℝ (N : ℕ) (-v) Ω from hv.neg) l hl
  rw [partialWord_neg] at h
  simpa only [sub_eq_add_neg] using h

lemma c2HolderOn_sub {n : ℕ} {α : ℝ} (Ω : Domain n) {u v : Space n → ℝ}
    (hu : IsC2HolderOn α u Ω) (hv : IsC2HolderOn α v Ω) : IsC2HolderOn α (u - v) Ω := by
  have h1 (i : Fin n) : EqOn (multiPartial (u-v) {i}) (multiPartial u {i} - multiPartial v {i}) Ω :=
    partialWord_sub_on Ω hu.1 hv.1 (({i} : MultiIndex n).sort (· ≤ ·)) (by simp)
  have h2 (i j : Fin n) : EqOn (multiPartial (u-v) {i,j})
      (multiPartial u {i,j} - multiPartial v {i,j}) Ω :=
    partialWord_sub_on Ω hu.1 hv.1 (({i,j} : MultiIndex n).sort (· ≤ ·)) (by simp)
  have hb {f g : Space n → ℝ} (hf : IsBoundedOn f Ω) (hg : IsBoundedOn g Ω) :
      IsBoundedOn (f-g) Ω := by
    obtain ⟨Mf,hMf,hbf⟩ := hf
    obtain ⟨Mg,hMg,hbg⟩ := hg
    exact ⟨Mf+Mg, add_nonneg hMf hMg,
      fun x hx => (norm_sub_le _ _).trans (add_le_add (hbf x hx) (hbg x hx))⟩
  refine ⟨hu.1.sub hv.1, hb hu.2.1 hv.2.1, ?_, ?_⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := hb (hu.2.2.1 i) (hv.2.2.1 i)
    exact ⟨M,hM,fun x hx => (congrArg norm (h1 i hx)).trans_le (hb x hx)⟩
  · intro i j
    have hneg : IsHolderOn α (fun x => -multiPartial v {i,j} x) Ω := by
      simpa only [neg_one_mul] using isHolderOn_const_mul (hv.2.2.2 i j) (-1)
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr (isHolderOn_add (hu.2.2.2 i j) hneg)
    intro x hx
    simpa only [Pi.sub_apply, sub_eq_add_neg] using h2 i j hx

lemma norm_fderiv_le_c2HolderNormOn {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s : Set (Space n)} (hu : IsC2HolderOn α u s) {x : Space n} (hx : x ∈ s) :
    ‖fderiv ℝ u x‖ ≤ (n : ℝ) * c2HolderNormOn α u s := by
  apply (norm_fderiv_le_sum_multiPartial u x).trans
  calc
    (∑ i : Fin n, ‖multiPartial u {i} x‖) ≤ ∑ _i : Fin n, c2HolderNormOn α u s :=
      Finset.sum_le_sum (fun i _ => (norm_le_supNormOn (hu.2.2.1 i) hx).trans
        ((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α u s).2.1 i))
    _ = _ := by simp

lemma norm_fderiv_fderiv_le_c2HolderNormOn {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : IsOpen s) (hu : IsC2HolderOn α u s)
    {x : Space n} (hx : x ∈ s) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ (n : ℝ)^2 * c2HolderNormOn α u s := by
  apply (norm_fderiv_fderiv_le_sum_multiPartial (hu.1.contDiffAt (hs.mem_nhds hx))).trans
  calc
    (∑ i : Fin n, ∑ j : Fin n, ‖multiPartial u {i,j} x‖) ≤
        ∑ _i : Fin n, ∑ _j : Fin n, c2HolderNormOn α u s :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        (norm_le_holderNormOn (hu.2.2.2 i j) hx).trans
          ((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α u s).2.2 i j)))
    _ = _ := by simp [pow_two, mul_assoc]


lemma fderiv_fderiv_sub_of_contDiffAt {n : ℕ} {u v : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    fderiv ℝ (fderiv ℝ (u-v)) x = fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ v) x := by
  have heq : fderiv ℝ (u-v) =ᶠ[nhds x] (fun y => fderiv ℝ u y - fderiv ℝ v y) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y huy hvy
    exact fderiv_sub (huy.differentiableAt (by norm_num)) (hvy.differentiableAt (by norm_num))
  rw [heq.fderiv_eq]
  exact fderiv_fun_sub
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)

lemma uniformCauchySeqOn_fderiv_of_c2HolderNormOn_cauchy {n : ℕ} {α : ℝ}
    {s : Set (Space n)} (hs : IsOpen s) {u : ℕ → Space n → ℝ}
    (hu : ∀ j, IsC2HolderOn α (u j) s)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      c2HolderNormOn α (u p-u q) s < ε) :
    UniformCauchySeqOn (fun j x => fderiv ℝ (u j) x) atTop s := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hden : 0 < (n : ℝ) + 1 := by positivity
  obtain ⟨N,hN⟩ := hc (ε / ((n : ℝ)+1)) (div_pos hε hden)
  refine ⟨N,?_⟩
  intro p hp q hq x hx
  have hup := (hu p).1.contDiffAt (hs.mem_nhds hx)
  have huq := (hu q).1.contDiffAt (hs.mem_nhds hx)
  have hdiff : IsC2HolderOn α (u p-u q) s := c2HolderOn_sub ⟨s,hs⟩ (hu p) (hu q)
  have hnorm := norm_fderiv_le_c2HolderNormOn hdiff hx
  have hsmall := (lt_div_iff₀ hden).mp (hN p hp q hq)
  have hnonneg := P201.Elliptic.PoissonSchauder.c2HolderNormOn_nonneg α (u p-u q) s
  rw [dist_eq_norm, ← fderiv_sub (hup.differentiableAt (by norm_num)) (huq.differentiableAt (by norm_num))]
  nlinarith

lemma uniformCauchySeqOn_second_fderiv_of_c2HolderNormOn_cauchy {n : ℕ} {α : ℝ}
    {s : Set (Space n)} (hs : IsOpen s) {u : ℕ → Space n → ℝ}
    (hu : ∀ j, IsC2HolderOn α (u j) s)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      c2HolderNormOn α (u p-u q) s < ε) :
    UniformCauchySeqOn (fun j x => fderiv ℝ (fderiv ℝ (u j)) x) atTop s := by
  apply (Metric.uniformCauchySeqOn_iff (α := Space n →L[ℝ] Space n →L[ℝ] ℝ)).mpr
  intro ε hε
  have hden : 0 < (n : ℝ)^2 + 1 := by positivity
  obtain ⟨N,hN⟩ := hc (ε / ((n : ℝ)^2+1)) (div_pos hε hden)
  refine ⟨N,?_⟩
  intro p hp q hq x hx
  have hup := (hu p).1.contDiffAt (hs.mem_nhds hx)
  have huq := (hu q).1.contDiffAt (hs.mem_nhds hx)
  have hdiff : IsC2HolderOn α (u p-u q) s := c2HolderOn_sub ⟨s,hs⟩ (hu p) (hu q)
  have hnorm := norm_fderiv_fderiv_le_c2HolderNormOn hs hdiff hx
  have hsmall := (lt_div_iff₀ hden).mp (hN p hp q hq)
  have hnonneg := P201.Elliptic.PoissonSchauder.c2HolderNormOn_nonneg α (u p-u q) s
  rw [dist_eq_norm (fderiv ℝ (fderiv ℝ (u p)) x) (fderiv ℝ (fderiv ℝ (u q)) x)]
  rw [← fderiv_fderiv_sub_of_contDiffAt hup huq]
  nlinarith


lemma isC2HolderLocOn_ball_of_upTo {n : ℕ} {α : ℝ} {z : Space n} {r : ℝ}
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u (closedBall z r)) :
    IsC2HolderLocOn α u (ballDomain z r) := by
  have huC : ContDiffOn ℝ 2 u (ball z r) := hu.1.mono ball_subset_closedBall
  have hEq (i j : Fin n) : EqOn (P201Specs.multiPartial u {i,j})
      (secondPartialWithin u (closedBall z r) i j) (ball z r) := by
    intro x hx
    rw [secondPartialWithin_eq_of_mem_interior u
      (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall))]
    exact (secondPartial_eq_multiPartial_at (huC.contDiffAt (isOpen_ball.mem_nhds hx)) i j).symm
  refine ⟨huC,?_⟩
  intro x hx
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
  refine ⟨ε,hε,hsub,?_⟩
  intro i j
  apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
    (P201.Elliptic.PoissonSchauder.isHolderOn_mono (hu.2.2.2 i j) (hsub.trans ball_subset_closedBall))
  exact fun y hy => hEq i j (hsub hy)

lemma isC2HolderOn_ball_of_upTo {n : ℕ} {α : ℝ} {z : Space n} {r : ℝ}
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u (closedBall z r)) :
    IsC2HolderOn α u (ball z r) := by
  have huC : ContDiffOn ℝ 2 u (ball z r) := hu.1.mono ball_subset_closedBall
  have hfirst (i : Fin n) : EqOn (P201Specs.multiPartial u {i})
      (firstPartialWithin u (closedBall z r) i) (ball z r) := by
    intro x hx
    rw [firstPartialWithin_eq_of_mem_interior u
      (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall))]
    simp only [P201Specs.multiPartial, P102.U4.multiPartial, Multiset.sort_singleton,
      P102.U4.partialWord, firstPartial]
  have hsecond (i j : Fin n) : EqOn (P201Specs.multiPartial u {i,j})
      (secondPartialWithin u (closedBall z r) i j) (ball z r) := by
    intro x hx
    rw [secondPartialWithin_eq_of_mem_interior u
      (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall))]
    exact (secondPartial_eq_multiPartial_at (huC.contDiffAt (isOpen_ball.mem_nhds hx)) i j).symm
  refine ⟨huC,?_,?_,?_⟩
  · obtain ⟨M,hM,hb⟩ := hu.2.1
    exact ⟨M,hM,fun x hx => hb x (ball_subset_closedBall hx)⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := hu.2.2.1 i
    exact ⟨M,hM,fun x hx => by rw [hfirst i hx]; exact hb x (ball_subset_closedBall hx)⟩
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono (hu.2.2.2 i j) ball_subset_closedBall)
    exact hsecond i j

namespace BallReflection
open P201Specs
lemma laplacian_comp_linearIsometry {n : ℕ} {u : Space n → ℝ}
    (e : Space n ≃ₗᵢ[ℝ] Space n) (x : Space n)
    (hu : ContDiffAt ℝ 2 u (e x)) :
    P201Specs.laplacian (u ∘ e) x = P201Specs.laplacian u (e x) := by
  have hcomp : ContDiffAt ℝ 2 (u ∘ e) x := hu.comp x e.contDiff.contDiffAt
  rw [P201.MeanValues.laplacian_bridge _ _ hcomp, P201.MeanValues.laplacian_bridge _ _ hu]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (u ∘ e)
    (EuclideanSpace.basisFun (Fin n) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
      ((EuclideanSpace.basisFun (Fin n) ℝ).map e)]
  apply Finset.sum_congr rfl
  intro i _
  have hiter := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right u
    uniqueDiffOn_univ (x := x) (mem_univ _) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hiter
  change iteratedFDeriv ℝ 2 (u ∘ e) x =
    (iteratedFDeriv ℝ 2 u (e x)).compContinuousLinearMap (fun _ => e.toContinuousLinearMap) at hiter
  rw [hiter]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

lemma harmonic_comp_linearIsometry {n : ℕ} (Ω : Domain n) {u : Space n → ℝ}
    (hu : P201Specs.MeanValues.IsHarmonic Ω u) (e : Space n ≃ₗᵢ[ℝ] Space n) :
    P201Specs.MeanValues.IsHarmonic
      ⟨e ⁻¹' (Ω : Set (Space n)), Ω.isOpen.preimage e.continuous⟩ (u ∘ e) := by
  refine ⟨hu.1.comp e.contDiff.contDiffOn (fun _ hx => hx), ?_⟩
  intro x hx
  rw [laplacian_comp_linearIsometry e x
    ((hu.1 (e x) hx).contDiffAt (Ω.isOpen.mem_nhds hx))]
  exact hu.2 (e x) hx

lemma poissonExtension_odd {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r)
    (e : Space n ≃ₗᵢ[ℝ] Space n) (g : C(sphere (0 : Space n) r, ℝ))
    (hg : ∀ ζ : sphere (0 : Space n) r,
      g ⟨e ζ, by simpa only [mem_sphere,dist_zero_right,e.norm_map] using ζ.property⟩ = -g ζ) :
    ∀ x ∈ closedBall (0 : Space n) r,
      P201.BallPoisson.poissonExtension 0 r g (e x) =
        -P201.BallPoisson.poissonExtension 0 r g x := by
  let h := P201.BallPoisson.poissonExtension (0 : Space n) r g
  have hh := P201.BallPoisson.poissonExtension_harmonic hn 0 hr g
  have hc := (P201.BallPoisson.continuous_extension hn 0 r hr g).1
  have heball : e ⁻¹' ball (0 : Space n) r = ball 0 r := by
    ext x
    simp only [mem_preimage,mem_ball,dist_zero_right,e.norm_map]
  have hch : P201Specs.MeanValues.IsHarmonic ⟨ball 0 r,isOpen_ball⟩ (h ∘ e) := by
    have hcomp := harmonic_comp_linearIsometry ⟨ball 0 r,isOpen_ball⟩ hh e
    change P201Specs.MeanValues.IsHarmonic ⟨e ⁻¹' ball 0 r,_⟩ (h ∘ e) at hcomp
    have hdom : (⟨e ⁻¹' ball (0 : Space n) r,isOpen_ball.preimage e.continuous⟩ : Domain n) =
        ⟨ball 0 r,isOpen_ball⟩ := by
      exact TopologicalSpace.Opens.ext heball
    rw [hdom] at hcomp
    exact hcomp
  have hv : P201Specs.MeanValues.IsHarmonic ⟨ball 0 r,isOpen_ball⟩ (-(h ∘ e)) := by
    apply (P201.MeanValues.harmonic_bridge _ _).mpr
    intro x hx
    exact (((P201.MeanValues.harmonic_bridge _ _).mp hch) x hx).neg
  have hvcl : ContinuousOn (-(h ∘ e)) (closedBall 0 r) := by
    apply (hc.comp e.continuous.continuousOn ?_).neg
    intro x hx
    simpa only [mem_closedBall,dist_zero_right,e.norm_map] using hx
  have heq := P201.BallPoisson.uniqueness hn 0 r hr g (-(h ∘ e)) hv hvcl ?_
  · intro x hx
    have heqx := heq hx
    change -h (e x) = h x at heqx
    linarith
  · intro ζ
    have hs : e ζ ∈ sphere (0 : Space n) r := by
      simpa only [mem_sphere,dist_zero_right,e.norm_map] using ζ.property
    have htrace := (P201.BallPoisson.continuous_extension hn 0 r hr g).2 ⟨e ζ,hs⟩
    change -h (e ζ) = g ζ
    change h (e ζ) = g ⟨e ζ,hs⟩ at htrace
    rw [htrace,hg ζ,neg_neg]

lemma harmonic_eqOn_of_max {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hconn : IsPreconnected (Ω : Set (Space n))) (u : Space n → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic Ω u) {x : Space n} (hx : x ∈ Ω)
    (hmax : ∀ y ∈ Ω, u y ≤ u x) : EqOn u (fun _ => u x) Ω := by
  let S : Set Ω := {y | u y=u x}
  have hc : Continuous (fun y : Ω => u y) := hu.1.continuousOn.domRestrict
  have hclosed : IsClosed S := isClosed_eq hc continuous_const
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨ε,hε,_,heq⟩ := P201.BallPoisson.harmonic_constant_near_max hn Ω u hu
      y.property (fun z hz => (hmax z hz).trans_eq hy.symm)
    have hnhds : {z : Ω | (z : Space n) ∈ ball (y : Space n) ε} ∈ 𝓝 y :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε)
    apply mem_of_superset hnhds
    intro z hz
    exact (heq hz).trans hy
  haveI : PreconnectedSpace Ω := Subtype.preconnectedSpace hconn
  have hevery := IsClopen.eq_univ ⟨hclosed,hopen⟩ (show S.Nonempty from ⟨⟨x,hx⟩,rfl⟩)
  intro y hy
  have : (⟨y,hy⟩ : Ω) ∈ S := by rw [hevery]; trivial
  exact this

lemma harmonic_nonpos_of_boundary {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (hconn : IsPreconnected (Ω : Set (Space n))) {u : Space n → ℝ}
    (hu : P201Specs.MeanValues.IsHarmonic Ω u)
    (hc : ContinuousOn u (closure (Ω : Set (Space n))))
    (hboundary : ∀ x ∈ frontier (Ω : Set (Space n)), u x ≤ 0) :
    ∀ x ∈ Ω, u x ≤ 0 := by
  apply P201.Elliptic.boundaryBound_of_interior_constancy hn hb hc hboundary
  intro z hz _ hmax
  exact harmonic_eqOn_of_max hn Ω hconn u hu hz hmax

lemma harmonic_eqOn_of_boundary {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (hconn : IsPreconnected (Ω : Set (Space n))) {u v : Space n → ℝ}
    (hu : P201Specs.MeanValues.IsHarmonic Ω u) (hv : P201Specs.MeanValues.IsHarmonic Ω v)
    (huc : ContinuousOn u (closure (Ω : Set (Space n))))
    (hvc : ContinuousOn v (closure (Ω : Set (Space n))))
    (hboundary : EqOn u v (frontier (Ω : Set (Space n)))) : EqOn u v Ω := by
  have hsub : P201Specs.MeanValues.IsHarmonic Ω (u-v) := by
    apply (P201.MeanValues.harmonic_bridge _ _).mpr
    intro x hx
    exact (((P201.MeanValues.harmonic_bridge _ _).mp hu) x hx).sub
      (((P201.MeanValues.harmonic_bridge _ _).mp hv) x hx)
  have hsub' : P201Specs.MeanValues.IsHarmonic Ω (v-u) := by
    apply (P201.MeanValues.harmonic_bridge _ _).mpr
    intro x hx
    exact (((P201.MeanValues.harmonic_bridge _ _).mp hv) x hx).sub
      (((P201.MeanValues.harmonic_bridge _ _).mp hu) x hx)
  have hle := harmonic_nonpos_of_boundary hn Ω hb hconn hsub (huc.sub hvc)
    (fun x hx => by simp only [Pi.sub_apply,hboundary hx,sub_self,le_refl])
  have hge := harmonic_nonpos_of_boundary hn Ω hb hconn hsub' (hvc.sub huc)
    (fun x hx => by simp only [Pi.sub_apply,hboundary hx,sub_self,le_refl])
  intro x hx
  exact le_antisymm (sub_nonpos.mp (hle x hx)) (sub_nonpos.mp (hge x hx))

/-- Schwarz reflection across the fixed hyperplane of a linear reflection.
Only harmonicity above the plane, continuity up to it, and zero trace are assumed. -/
lemma harmonic_reflection_extension {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r)
    (e : Space n ≃ₗᵢ[ℝ] Space n) (l : Space n →L[ℝ] ℝ)
    (he : Function.Involutive e) (hl : ∀ x, l (e x) = -l x)
    (hfix : ∀ x, l x=0 → e x=x) (u : Space n → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨ball 0 r ∩ {x | 0 < l x},isOpen_ball.inter (isOpen_lt continuous_const l.continuous)⟩ u)
    (huc : ContinuousOn u (closedBall 0 r ∩ {x | 0 ≤ l x}))
    (hzero : ∀ x ∈ closedBall 0 r, l x=0 → u x=0) :
    ∃ v : Space n → ℝ,
      P201Specs.MeanValues.IsHarmonic ⟨ball 0 r,isOpen_ball⟩ v ∧
      EqOn v u (ball 0 r ∩ {x | 0 ≤ l x}) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let P : Set (Space n) := {x | 0 ≤ l x}
  let Q : Set (Space n) := {x | 0 < l x}
  let S := closedBall (0 : Space n) r ∩ P
  let Ω : Domain n := ⟨ball 0 r ∩ Q,isOpen_ball.inter (isOpen_lt continuous_const l.continuous)⟩
  have hP : IsClosed P := isClosed_le continuous_const l.continuous
  have hQ : IsOpen Q := isOpen_lt continuous_const l.continuous
  have hS : IsClosed S := isClosed_closedBall.inter hP
  have hΩS : closure (Ω : Set (Space n)) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    have hx' : x ∈ ball (0 : Space n) r ∧ 0 < l x := hx
    exact ⟨ball_subset_closedBall hx'.1,hx'.2.le⟩
  have hfrontP : ∀ x ∈ frontier P, l x=0 := by
    intro x hx
    have h := l.continuous.frontier_preimage_subset (Ici (0:ℝ)) hx
    simpa only [mem_preimage,frontier_Ici,mem_singleton_iff] using h
  have hneg : closure Pᶜ ⊆ {x | l x ≤ 0} := by
    apply closure_minimal _ (isClosed_le l.continuous continuous_const)
    intro x hx
    change ¬0 ≤ l x at hx
    exact (lt_of_not_ge hx).le
  let U := fun x : Space n => if 0 ≤ l x then u x else -u (e x)
  have hU : ContinuousOn U (closedBall 0 r) := by
    apply ContinuousOn.if ?_ ?_ ?_
    · intro x hx
      have hz := hfrontP x hx.2
      rw [hfix x hz,hzero x hx.1 hz,neg_zero]
    · exact huc.mono (by
        intro x hx
        refine ⟨hx.1,?_⟩
        have hxP : x ∈ closure P := hx.2
        rw [hP.closure_eq] at hxP
        exact hxP)
    · apply (huc.comp e.continuous.continuousOn ?_).neg
      intro x hx
      refine ⟨?_,?_⟩
      · simpa only [mem_closedBall,dist_zero_right,e.norm_map] using hx.1
      · change 0 ≤ l (e x)
        rw [hl]
        exact neg_nonneg.mpr (hneg hx.2)
  have hUodd (x : Space n) (hx : x ∈ closedBall 0 r) : U (e x) = -U x := by
    by_cases hz : l x=0
    · simp only [U,hz,neg_zero,le_refl,ite_true,hfix x hz,hzero x hx hz]
    · by_cases hp : 0 < l x
      · have hnp : ¬0 ≤ -l x := by linarith
        simp only [U,hl,hp.le,ite_true,hnp,ite_false,he x]
      · have hn' : l x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
        simp only [U,hl,hn'.not_ge,ite_false,neg_nonneg.mpr hn'.le,ite_true,neg_neg]
  let g : C(sphere (0 : Space n) r,ℝ) :=
    ⟨fun ζ => U ζ,(hU.mono sphere_subset_closedBall).domRestrict⟩
  let v := P201.BallPoisson.poissonExtension (0 : Space n) r g
  have hv := P201.BallPoisson.poissonExtension_harmonic hn 0 hr g
  have hvc := P201.BallPoisson.continuous_extension hn 0 r hr g
  have hvodd := poissonExtension_odd hn hr e g (fun ζ => hUodd ζ (sphere_subset_closedBall ζ.property))
  have hvzero (x : Space n) (hx : x ∈ closedBall 0 r) (hz : l x=0) : v x=0 := by
    have heq := hvodd x hx
    change v (e x) = -v x at heq
    rw [hfix x hz] at heq
    linarith
  have hvΩ : P201Specs.MeanValues.IsHarmonic Ω v :=
    ⟨hv.1.mono inter_subset_left,fun x hx => hv.2 x hx.1⟩
  have hconn : IsPreconnected (Ω : Set (Space n)) := by
    apply Convex.isPreconnected
    exact (convex_ball 0 r).inter ((convex_Ioi (0:ℝ)).linear_preimage l.toLinearMap)
  have hb : Bornology.IsBounded (Ω : Set (Space n)) := isBounded_ball.subset inter_subset_left
  have hboundary : EqOn v u (frontier (Ω : Set (Space n))) := by
    intro x hx
    have hxS := hΩS (frontier_subset_closure hx)
    have hfront := frontier_inter_subset (ball (0 : Space n) r) Q hx
    rcases hfront with hxball | hxQ
    · have hxs : x ∈ sphere (0 : Space n) r := by
        have h := hxball.1
        rwa [frontier_ball 0 hr.ne'] at h
      have heq := hvc.2 ⟨x,hxs⟩
      change v x = U x at heq
      exact heq.trans (ite_eq_left hxS.2)
    · have hlx : l x=0 := by
        have h := l.continuous.frontier_preimage_subset (Ioi (0:ℝ)) hxQ.2
        simpa only [mem_preimage,frontier_Ioi,mem_singleton_iff] using h
      rw [hvzero x hxS.1 hlx,hzero x hxS.1 hlx]
  have heq := harmonic_eqOn_of_boundary (by omega) Ω hb hconn hvΩ hu
    (hvc.1.mono (fun x hx => (hΩS hx).1)) (huc.mono hΩS) hboundary
  refine ⟨v,hv,?_⟩
  intro x hx
  by_cases hlx : 0 < l x
  · exact heq ⟨hx.1,hlx⟩
  · have hz : l x=0 := le_antisymm (le_of_not_gt hlx) hx.2
    rw [hvzero x (ball_subset_closedBall hx.1) hz,hzero x (ball_subset_closedBall hx.1) hz]

lemma harmonic_reflection_extension_normal {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r)
    (a : Space n) (u : Space n → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨ball 0 r ∩ {x | 0 < inner ℝ a x},
        isOpen_ball.inter (isOpen_lt continuous_const (continuous_const.inner continuous_id))⟩ u)
    (huc : ContinuousOn u (closedBall 0 r ∩ {x | 0 ≤ inner ℝ a x}))
    (hzero : ∀ x ∈ closedBall 0 r, inner ℝ a x=0 → u x=0) :
    ∃ v : Space n → ℝ,
      P201Specs.MeanValues.IsHarmonic ⟨ball 0 r,isOpen_ball⟩ v ∧
      EqOn v u (ball 0 r ∩ {x | 0 ≤ inner ℝ a x}) := by
  let e := (ℝ ∙ a)ᗮ.reflection
  let l : Space n →L[ℝ] ℝ := innerSL ℝ a
  have he : Function.Involutive e := Submodule.reflection_involutive _
  have hea : e a = -a := Submodule.reflection_orthogonalComplement_singleton_eq_neg a
  have hl (x : Space n) : l (e x) = -l x := by
    have h := e.inner_map_map a (e x)
    rw [hea,he x,inner_neg_left] at h
    exact h.symm
  have hfix (x : Space n) (hx : l x=0) : e x=x := by
    apply Submodule.reflection_mem_subspace_eq_self
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr hx
  exact harmonic_reflection_extension hn hr e l he hl hfix u hu huc hzero

lemma coordinate_inner {n : ℕ} (i : Fin n) (x : Space n) :
    inner ℝ (coordinate n i) x = x i := by
  simp [coordinate,P201Specs.coordinate,P102.U4.coordinateVector,EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left]

lemma harmonic_reflection_extension_coordinate {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r)
    (i : Fin n) (u : Space n → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨ball 0 r ∩ {x | 0 < x i},
        isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))⟩ u)
    (huc : ContinuousOn u (closedBall 0 r ∩ {x | 0 ≤ x i}))
    (hzero : ∀ x ∈ closedBall 0 r, x i=0 → u x=0) :
    ∃ v : Space n → ℝ,
      P201Specs.MeanValues.IsHarmonic ⟨ball 0 r,isOpen_ball⟩ v ∧
      EqOn v u (ball 0 r ∩ {x | 0 ≤ x i}) := by
  have h := harmonic_reflection_extension_normal hn hr (coordinate n i) u
    (by simpa only [coordinate_inner] using hu)
    (by simpa only [coordinate_inner] using huc)
    (by simpa only [coordinate_inner] using hzero)
  simpa only [coordinate_inner] using h
end BallReflection



lemma holderNormOn_le_of_bounds {n : ℕ} {α M H : ℝ} {f : Space n → ℝ} {s : Set (Space n)}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hb : ∀ x ∈ s, ‖f x‖ ≤ M)
    (hh : ∀ x ∈ s, ∀ y ∈ s, ‖f x-f y‖ ≤ H * dist x y ^ α) :
    holderNormOn α f s ≤ M+H := by
  apply add_le_add
  · exact Real.sSup_le (by rintro t ⟨x,hx,rfl⟩; exact hb x hx) hM
  · apply Real.sSup_le _ hH
    rintro t ⟨x,hx,y,hy,hxy,rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) _)).mpr (hh x hx y hy)

lemma holderNormOn_le_of_bounded_lipschitz {n : ℕ} {α M L : ℝ} {f : Space n → ℝ}
    {s : Set (Space n)} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hb : ∀ x ∈ s, ‖f x‖ ≤ M)
    (hl : ∀ x ∈ s, ∀ y ∈ s, ‖f x-f y‖ ≤ L * dist x y) :
    holderNormOn α f s ≤ 3*M+L := by
  refine (holderNormOn_le_of_bounds (H := L+2*M) hM (add_nonneg hL (by positivity)) hb ?_).trans_eq (by ring)
  · intro x hx y hy
    by_cases hd : dist x y ≤ 1
    · calc
        ‖f x-f y‖ ≤ L * dist x y := hl x hx y hy
        _ ≤ L * dist x y ^ α :=
          mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one dist_nonneg hd hα1) hL
        _ ≤ (L+2*M) * dist x y ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _)
    · calc
        ‖f x-f y‖ ≤ ‖f x‖+‖f y‖ := norm_sub_le _ _
        _ ≤ 2*M := by linarith [hb x hx, hb y hy]
        _ ≤ (2*M) * dist x y ^ α :=
          le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (not_le.mp hd).le hα)
        _ ≤ (L+2*M) * dist x y ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _)

lemma c2HolderUpToNormOn_eq_holder_sums {n : ℕ} (α : ℝ) (u : Space n → ℝ) (s : Set (Space n)) :
    c2HolderUpToNormOn α u s = supNormOn u s +
      (∑ i : Fin n, supNormOn (firstPartialWithin u s i) s) +
      ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (secondPartialWithin u s i j) s := by
  simp only [c2HolderUpToNormOn, scaledWithinSolutionNorm, one_mul, one_pow,
    Real.one_rpow, holderNormOn, supNormOn, holderSeminormOn, Finset.sum_add_distrib]
  ring

lemma c2HolderUpToNormOn_nonneg {n : ℕ} (α : ℝ) (u : Space n → ℝ) (s : Set (Space n)) :
    0 ≤ c2HolderUpToNormOn α u s := by
  rw [c2HolderUpToNormOn_eq_holder_sums]
  exact add_nonneg (add_nonneg (supNormOn_nonneg _ _) (Finset.sum_nonneg fun _ _ => supNormOn_nonneg _ _))
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => holderNormOn_nonneg _ _ _)

lemma c2HolderUpToNormOn_components {n : ℕ} (α : ℝ) (u : Space n → ℝ) (s : Set (Space n)) :
    supNormOn u s ≤ c2HolderUpToNormOn α u s ∧
      (∑ i : Fin n, supNormOn (firstPartialWithin u s i) s) ≤ c2HolderUpToNormOn α u s ∧
      (∀ i : Fin n, supNormOn (firstPartialWithin u s i) s ≤ c2HolderUpToNormOn α u s) ∧
      (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (secondPartialWithin u s i j) s) ≤
        c2HolderUpToNormOn α u s ∧
      ∀ i j : Fin n, holderNormOn α (secondPartialWithin u s i j) s ≤ c2HolderUpToNormOn α u s := by
  have h0 := supNormOn_nonneg u s
  have h1 : ∀ i : Fin n, 0 ≤ supNormOn (firstPartialWithin u s i) s := fun i => supNormOn_nonneg _ _
  have h2 : ∀ i j : Fin n, 0 ≤ holderNormOn α (secondPartialWithin u s i j) s := fun i j => holderNormOn_nonneg _ _ _
  have hS1 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => h1 i)
  have hS2 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => Finset.sum_nonneg (s := Finset.univ) (fun j _ => h2 i j))
  rw [c2HolderUpToNormOn_eq_holder_sums]
  refine ⟨by linarith, by linarith, ?_, by linarith, ?_⟩
  · intro i
    have hi := Finset.single_le_sum (fun j _ => h1 j) (Finset.mem_univ i)
    linarith
  · intro i j
    have hij := Finset.single_le_sum (fun j _ => h2 i j) (Finset.mem_univ j)
    have hi := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (s := Finset.univ) fun j _ => h2 i j) (Finset.mem_univ i)
    linarith

lemma norm_fderivWithin_le_c2HolderUpToNormOn {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s : Set (Space n)} (hu : IsC2HolderUpToOn α u s) {x : Space n} (hx : x ∈ s) :
    ‖fderivWithin ℝ u s x‖ ≤ c2HolderUpToNormOn α u s := by
  apply (norm_clm_le_sum_coordinates _).trans
  exact (Finset.sum_le_sum (fun i _ => norm_le_supNormOn (hu.2.2.1 i) hx)).trans
    (c2HolderUpToNormOn_components α u s).2.1

lemma norm_fderivWithin_firstPartial_le_c2HolderUpToNormOn {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s : Set (Space n)} (hu : IsC2HolderUpToOn α u s) {x : Space n} (hx : x ∈ s) (i : Fin n) :
    ‖fderivWithin ℝ (firstPartialWithin u s i) s x‖ ≤ c2HolderUpToNormOn α u s := by
  apply (norm_clm_le_sum_coordinates _).trans
  apply le_trans ?_ (c2HolderUpToNormOn_components α u s).2.2.2.1
  apply Finset.sum_le_sum
  intro j hj
  apply (norm_le_holderNormOn (hu.2.2.2 j i) hx).trans
  exact Finset.single_le_sum (fun k _ => holderNormOn_nonneg _ _ _) (Finset.mem_univ i)

lemma lower_order_holderNormOn_le_four_c2HolderUpToNormOn {n : ℕ} {α r : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (z : Space n) (hr : 0 < r)
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u (closedBall z r)) :
    holderNormOn α u (closedBall z r) ≤ 4*c2HolderUpToNormOn α u (closedBall z r) ∧
      ∀ i, holderNormOn α (firstPartialWithin u (closedBall z r) i) (closedBall z r) ≤
        4*c2HolderUpToNormOn α u (closedBall z r) := by
  let N := c2HolderUpToNormOn α u (closedBall z r)
  have hN : 0 ≤ N := c2HolderUpToNormOn_nonneg _ _ _
  have hs : UniqueDiffOn ℝ (closedBall z r) := uniqueDiffOn_convex (convex_closedBall z r)
    ⟨z, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds z hr)⟩
  constructor
  · have hb : ∀ x ∈ closedBall z r, ‖u x‖ ≤ N := fun x hx => norm_le_c2HolderUpToNormOn hu hx
    have hl : ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r, ‖u x-u y‖ ≤ N * dist x y := by
      intro x hx y hy
      simpa only [dist_eq_norm] using (convex_closedBall z r).norm_image_sub_le_of_norm_fderivWithin_le
        (hu.1.differentiableOn (by norm_num))
        (fun x hx => norm_fderivWithin_le_c2HolderUpToNormOn hu hx) hy hx
    exact (holderNormOn_le_of_bounded_lipschitz hα hα1 hN hN hb hl).trans_eq (by dsimp [N]; ring)
  · intro i
    have hb : ∀ x ∈ closedBall z r, ‖firstPartialWithin u (closedBall z r) i x‖ ≤ N :=
      fun x hx => (norm_le_supNormOn (hu.2.2.1 i) hx).trans
        ((c2HolderUpToNormOn_components α u (closedBall z r)).2.2.1 i)
    have hdi : ContDiffOn ℝ 1 (firstPartialWithin u (closedBall z r) i) (closedBall z r) :=
      (hu.1.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
    have hl : ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r,
        ‖firstPartialWithin u (closedBall z r) i x-firstPartialWithin u (closedBall z r) i y‖ ≤ N * dist x y := by
      intro x hx y hy
      simpa only [dist_eq_norm] using (convex_closedBall z r).norm_image_sub_le_of_norm_fderivWithin_le
        (hdi.differentiableOn (by norm_num))
        (fun x hx => norm_fderivWithin_firstPartial_le_c2HolderUpToNormOn hu hx i) hy hx
    exact (holderNormOn_le_of_bounded_lipschitz hα hα1 hN hN hb hl).trans_eq (by dsimp [N]; ring)


lemma holderNormOn_nondivergenceWithinOperator_le {n : ℕ} {α r : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (z : Space n) (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hu : IsC2HolderUpToOn α u (closedBall z r)) :
    holderNormOn α (nondivergenceWithinOperator a b c u (closedBall z r)) (closedBall z r) ≤
      4 * coefficientNormOn α a b c (closedBall z r) * c2HolderUpToNormOn α u (closedBall z r) := by
  let s := closedBall z r
  let N := c2HolderUpToNormOn α u s
  have hN : 0 ≤ N := c2HolderUpToNormOn_nonneg _ _ _
  have hjets := lower_order_holder_jets_on_closedBall hα hα1 z hr hu
  have hjnorm := lower_order_holderNormOn_le_four_c2HolderUpToNormOn hα hα1 z hr hu
  let A : Space n → ℝ := fun x => ∑ i : Fin n, ∑ j : Fin n, a x i j * secondPartialWithin u s i j x
  let B : Space n → ℝ := fun x => ∑ i : Fin n, b x i * firstPartialWithin u s i x
  let D : Space n → ℝ := fun x => c x * u x
  have hA : IsHolderOn α A s := isHolderOn_finset_sum Finset.univ _ (fun i _ =>
    isHolderOn_finset_sum Finset.univ _ (fun j _ => isHolderOn_mul (hc.1 i j) (hu.2.2.2 i j)))
  have hB : IsHolderOn α B s := isHolderOn_finset_sum Finset.univ _ (fun i _ =>
    isHolderOn_mul (hc.2.1 i) (hjets.2 i))
  have hD : IsHolderOn α D s := isHolderOn_mul hc.2.2 hjets.1
  have hAnorm : holderNormOn α A s ≤
      ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s * (4*N) := by
    apply (holderNormOn_finset_sum_le Finset.univ _ (fun i _ =>
      isHolderOn_finset_sum Finset.univ _ (fun j _ => isHolderOn_mul (hc.1 i j) (hu.2.2.2 i j)))).trans
    apply Finset.sum_le_sum
    intro i hi
    apply (holderNormOn_finset_sum_le Finset.univ _
      (fun j _ => isHolderOn_mul (hc.1 i j) (hu.2.2.2 i j))).trans
    apply Finset.sum_le_sum
    intro j hj
    apply (holderNormOn_mul_le (hc.1 i j) (hu.2.2.2 i j)).trans
    apply mul_le_mul_of_nonneg_left ?_ (holderNormOn_nonneg _ _ _)
    exact ((c2HolderUpToNormOn_components α u s).2.2.2.2 i j).trans (by change N ≤ 4*N; linarith)
  have hBnorm : holderNormOn α B s ≤
      ∑ i : Fin n, holderNormOn α (fun x => b x i) s * (4*N) := by
    apply (holderNormOn_finset_sum_le Finset.univ _
      (fun i _ => isHolderOn_mul (hc.2.1 i) (hjets.2 i))).trans
    exact Finset.sum_le_sum (fun i _ => (holderNormOn_mul_le (hc.2.1 i) (hjets.2 i)).trans
      (mul_le_mul_of_nonneg_left (hjnorm.2 i) (holderNormOn_nonneg _ _ _)))
  have hDnorm : holderNormOn α D s ≤ holderNormOn α c s * (4*N) :=
    (holderNormOn_mul_le hc.2.2 hjets.1).trans
      (mul_le_mul_of_nonneg_left hjnorm.1 (holderNormOn_nonneg _ _ _))
  calc
    holderNormOn α (nondivergenceWithinOperator a b c u s) s ≤
        holderNormOn α A s + holderNormOn α B s + holderNormOn α D s :=
      (holderNormOn_add_le (isHolderOn_add hA hB) hD).trans
        (add_le_add (holderNormOn_add_le hA hB) le_rfl)
    _ ≤ (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s * (4*N)) +
        (∑ i : Fin n, holderNormOn α (fun x => b x i) s * (4*N)) + holderNormOn α c s * (4*N) :=
      add_le_add (add_le_add hAnorm hBnorm) hDnorm
    _ = 4 * coefficientNormOn α a b c s * N := by
      simp only [coefficientNormOn, ← Finset.sum_mul]
      ring


namespace BallWithinLimit
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasFDerivWithinAt_closedBall_of_uniformLimit {z : E} {r : ℝ} (hr : 0 < r)
    {f : ℕ → E → F} {A : ℕ → E → E →L[ℝ] F}
    {g : E → F} {B : E → E →L[ℝ] F}
    (hderiv : ∀ j, ∀ x ∈ closedBall z r, HasFDerivWithinAt (f j) (A j x) (closedBall z r) x)
    (hAcont : ∀ j, ContinuousOn (A j) (closedBall z r))
    (hf : TendstoUniformlyOn f g atTop (closedBall z r))
    (hA : TendstoUniformlyOn A B atTop (closedBall z r)) :
    ∀ x ∈ closedBall z r, HasFDerivWithinAt g (B x) (closedBall z r) x := by
  have hgcont : ContinuousOn g (closedBall z r) := hf.continuousOn (Frequently.of_forall
    (fun j x hx => (hderiv j x hx).continuousWithinAt))
  have hBcont : ContinuousOn B (closedBall z r) := hA.continuousOn (Frequently.of_forall hAcont)
  have hderivOpen : ∀ x ∈ ball z r, HasFDerivAt g (B x) x := by
    intro x hx
    refine hasFDerivAt_of_tendstoUniformlyOn (f := f) (g := g) isOpen_ball (hA.mono ball_subset_closedBall) ?_ ?_ hx
    · intro j x hx
      exact (hderiv j x (ball_subset_closedBall hx)).hasFDerivAt
        (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
    · intro x hx
      exact hf.tendsto_at (ball_subset_closedBall hx)
  have hdiff : DifferentiableOn ℝ g (ball z r) :=
    fun x hx => (hderivOpen x hx).differentiableAt.differentiableWithinAt
  intro x hx
  have hext : HasFDerivWithinAt g (B x) (closure (ball z r)) x := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff (convex_ball z r) isOpen_ball
    · intro y hy
      rw [closure_ball z hr.ne'] at hy
      exact (hgcont y hy).mono ball_subset_closedBall
    · have hBlim : Tendsto B (𝓝[ball z r] x) (𝓝 (B x)) :=
        (hBcont x hx).mono ball_subset_closedBall
      apply hBlim.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hderivOpen y hy).fderiv.symm
  simpa only [closure_ball z hr.ne'] using hext


lemma uniqueDiffOn_closedBall (z : E) {r : ℝ} (hr : 0 < r) :
    UniqueDiffOn ℝ (closedBall z r) := by
  apply uniqueDiffOn_convex (convex_closedBall z r)
  refine ⟨z,?_⟩
  rw [mem_interior_iff_mem_nhds]
  exact mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hr)) ball_subset_closedBall

lemma contDiffOn_two_closedBall_of_uniformJets {z : E} {r : ℝ} (hr : 0 < r)
    {f : ℕ → E → F} {A : ℕ → E → E →L[ℝ] F}
    {B : ℕ → E → E →L[ℝ] (E →L[ℝ] F)}
    {g : E → F} {a : E → E →L[ℝ] F} {b : E → E →L[ℝ] (E →L[ℝ] F)}
    (hderiv1 : ∀ j, ∀ x ∈ closedBall z r, HasFDerivWithinAt (f j) (A j x) (closedBall z r) x)
    (hderiv2 : ∀ j, ∀ x ∈ closedBall z r, HasFDerivWithinAt (A j) (B j x) (closedBall z r) x)
    (hBcont : ∀ j, ContinuousOn (B j) (closedBall z r))
    (hf : TendstoUniformlyOn f g atTop (closedBall z r))
    (hA : TendstoUniformlyOn A a atTop (closedBall z r))
    (hB : TendstoUniformlyOn B b atTop (closedBall z r)) :
    ContDiffOn ℝ 2 g (closedBall z r) ∧
      (∀ x ∈ closedBall z r, fderivWithin ℝ g (closedBall z r) x = a x) ∧
      ∀ x ∈ closedBall z r, fderivWithin ℝ a (closedBall z r) x = b x := by
  have hAcont : ∀ j, ContinuousOn (A j) (closedBall z r) :=
    fun j x hx => (hderiv2 j x hx).continuousWithinAt
  have hderivG := hasFDerivWithinAt_closedBall_of_uniformLimit hr hderiv1 hAcont hf hA
  have hderivA := hasFDerivWithinAt_closedBall_of_uniformLimit hr hderiv2 hBcont hA hB
  have hbcont : ContinuousOn b (closedBall z r) := hB.continuousOn (Frequently.of_forall hBcont)
  have hs := uniqueDiffOn_closedBall z hr
  have haC1 : ContDiffOn ℝ 1 a (closedBall z r) := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hs).mpr
    exact ⟨by simp, b,contDiffOn_zero.mpr hbcont,hderivA⟩
  refine ⟨?_,fun x hx => (hderivG x hx).fderivWithin (hs x hx),
    fun x hx => (hderivA x hx).fderivWithin (hs x hx)⟩
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 1) hs).mpr
  exact ⟨by simp,a,haC1,hderivG⟩


lemma contDiffOn_two_closedBall_of_uniformWithinJets {z : E} {r : ℝ} (hr : 0 < r)
    {f : ℕ → E → F} {g : E → F} {a : E → E →L[ℝ] F}
    {b : E → E →L[ℝ] (E →L[ℝ] F)}
    (hC2 : ∀ j, ContDiffOn ℝ 2 (f j) (closedBall z r))
    (hf : TendstoUniformlyOn f g atTop (closedBall z r))
    (hA : TendstoUniformlyOn (fun j => fderivWithin ℝ (f j) (closedBall z r)) a atTop (closedBall z r))
    (hB : TendstoUniformlyOn
      (fun j => fderivWithin ℝ (fderivWithin ℝ (f j) (closedBall z r)) (closedBall z r))
      b atTop (closedBall z r)) :
    ContDiffOn ℝ 2 g (closedBall z r) ∧
      (∀ x ∈ closedBall z r, fderivWithin ℝ g (closedBall z r) x = a x) ∧
      ∀ x ∈ closedBall z r, fderivWithin ℝ a (closedBall z r) x = b x := by
  have hs := uniqueDiffOn_closedBall z hr
  have hC1 (j : ℕ) : ContDiffOn ℝ 1 (fderivWithin ℝ (f j) (closedBall z r)) (closedBall z r) :=
    (hC2 j).fderivWithin hs (by norm_num)
  apply contDiffOn_two_closedBall_of_uniformJets hr _ _ _ hf hA hB
  · intro j x hx
    exact ((hC2 j).differentiableOn (by norm_num) x hx).hasFDerivWithinAt
  · intro j x hx
    exact ((hC1 j).differentiableOn (by norm_num) x hx).hasFDerivWithinAt
  · intro j
    exact (hC1 j).continuousOn_fderivWithin hs (by norm_num)

end BallWithinLimit


namespace KelvinProduct
open P201Specs

lemma secondDirectional_mul {n : ℕ} {a b : Space n → ℝ} {x : Space n}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) (v : Space n) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => a z*b z) y v) x v =
      a x * fderiv ℝ (fun y => fderiv ℝ b y v) x v +
      b x * fderiv ℝ (fun y => fderiv ℝ a y v) x v +
      2 * (fderiv ℝ a x v) * (fderiv ℝ b x v) := by
  have hda := ha.differentiableAt (by norm_num)
  have hdb := hb.differentiableAt (by norm_num)
  have hdda : DifferentiableAt ℝ (fun y => fderiv ℝ a y v) x :=
    ((ha.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const v)
  have hddb : DifferentiableAt ℝ (fun y => fderiv ℝ b y v) x :=
    ((hb.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const v)
  have hfirst : (fun y => fderiv ℝ (fun z => a z*b z) y v) =ᶠ[nhds x]
      (fun y => a y * fderiv ℝ b y v + b y * fderiv ℝ a y v) := by
    filter_upwards [ha.eventually (by norm_num), hb.eventually (by norm_num)] with y hay hby
    rw [fderiv_fun_mul (hay.differentiableAt (by norm_num)) (hby.differentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hfirst.fderiv_eq]
  change fderiv ℝ ((a * fun y => fderiv ℝ b y v) + (b * fun y => fderiv ℝ a y v)) x v = _
  rw [fderiv_add (hda.mul hddb) (hdb.mul hdda), fderiv_mul hda hddb, fderiv_mul hdb hdda]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma laplacian_eq_sum_secondDirectional {n : ℕ} (a : Space n → ℝ) (x : Space n) :
    P201Specs.laplacian a x = ∑ i : Fin n,
      fderiv ℝ (fun y => fderiv ℝ a y (coordinate n i)) x (coordinate n i) := by
  change (∑ i : Fin n, multiPartial a ({i,i} : MultiIndex n) x) = _
  apply Finset.sum_congr rfl
  intro i hi
  have hsort : ({i,i} : MultiIndex n).sort (· ≤ ·) = [i,i] := by
    rw [Multiset.insert_eq_cons, Multiset.sort_cons i {i} (· ≤ ·) (by simp), Multiset.sort_singleton]
  simp only [P201Specs.multiPartial, P102.U4.multiPartial, hsort, P102.U4.partialWord]

lemma laplacian_mul {n : ℕ} {a b : Space n → ℝ} {x : Space n}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    P201Specs.laplacian (fun y => a y*b y) x =
      a x * P201Specs.laplacian b x + b x * P201Specs.laplacian a x +
      2 * ∑ i : Fin n, (fderiv ℝ a x (coordinate n i)) * (fderiv ℝ b x (coordinate n i)) := by
  simp only [laplacian_eq_sum_secondDirectional, secondDirectional_mul ha hb,
    Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]

end KelvinProduct

namespace KelvinCalculus
open P201Specs

def unitInversion {n : ℕ} : Space n → Space n := EuclideanGeometry.inversion 0 1

lemma unitInversion_apply {n : ℕ} (x : Space n) :
    unitInversion x = (‖x‖^2)⁻¹ • x := by
  simp only [unitInversion,EuclideanGeometry.inversion,dist_zero_right,
    vsub_eq_sub,sub_zero,one_div,inv_pow,vadd_eq_add,add_zero]

lemma unitInversion_fderiv_apply {n : ℕ} {x : Space n} (hx : x ≠ 0) (v : Space n) :
    fderiv ℝ unitInversion x v = (‖x‖^2)⁻¹ • v -
      (2*(‖x‖^4)⁻¹*inner ℝ x v) • x := by
  have hq := P201.BallPoisson.norm_inv_pow_hasFDerivAt (0 : Space n) x 2 hx
  simp only [sub_zero] at hq
  have hd := hq.smul (hasFDerivAt_id x)
  change HasFDerivAt (fun y : Space n => (‖y‖^2)⁻¹ • y) _ x at hd
  have heq : (fun y : Space n => (‖y‖^2)⁻¹ • y) = unitInversion := by
    funext y
    exact (unitInversion_apply y).symm
  rw [heq] at hd
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul,div_eq_mul_inv,id_eq,Nat.cast_ofNat]
  module

lemma unitInversion_secondDirectional {n : ℕ} {x : Space n} (hx : x ≠ 0) (v : Space n) :
    fderiv ℝ (fun y => fderiv ℝ unitInversion y v) x v =
      -(4*(‖x‖^4)⁻¹*inner ℝ x v) • v - (2*(‖x‖^4)⁻¹*‖v‖^2) • x +
      (8*(‖x‖^6)⁻¹*(inner ℝ x v)^2) • x := by
  have hq₂ := P201.BallPoisson.norm_inv_pow_hasFDerivAt (0 : Space n) x 2 hx
  have hq₄ := P201.BallPoisson.norm_inv_pow_hasFDerivAt (0 : Space n) x 4 hx
  simp only [sub_zero] at hq₂ hq₄
  have hp : HasFDerivAt (fun y : Space n => inner ℝ y v) (innerSL ℝ v) x := by
    convert (innerSL ℝ v).hasFDerivAt (x := x) using 1
    funext y
    exact real_inner_comm v y
  have hd := (hq₂.smul_const v).sub (((hq₄.const_mul 2).mul hp).smul (hasFDerivAt_id x))
  change HasFDerivAt (fun y => (‖y‖^2)⁻¹ • v - (2*(‖y‖^4)⁻¹*inner ℝ y v) • y) _ x at hd
  have heq : (fun y => fderiv ℝ unitInversion y v) =ᶠ[𝓝 x]
      (fun y => (‖y‖^2)⁻¹ • v - (2*(‖y‖^4)⁻¹*inner ℝ y v) • y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact unitInversion_fderiv_apply hy v
  rw [heq.fderiv_eq,hd.fderiv]
  simp only [sub_apply,add_apply,
    ContinuousLinearMap.smulRight_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.comp_apply,innerSL_apply_apply,real_inner_self_eq_norm_sq,
    real_inner_comm v x,smul_eq_mul,div_eq_mul_inv,id_eq,Nat.cast_ofNat,Pi.mul_apply]
  module

lemma normInvPow_fderiv_apply {n : ℕ} {x : Space n} (hx : x ≠ 0) (k : ℕ) (v : Space n) :
    fderiv ℝ (fun y : Space n => (‖y‖^k)⁻¹) x v =
      -(k:ℝ)*(‖x‖^(k+2))⁻¹*inner ℝ x v := by
  have hd := P201.BallPoisson.norm_inv_pow_hasFDerivAt (0 : Space n) x k hx
  simp only [sub_zero] at hd
  rw [hd.fderiv]
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,div_eq_mul_inv]

lemma normInvPow_secondDirectional {n : ℕ} {x : Space n} (hx : x ≠ 0) (k : ℕ) (v : Space n) :
    fderiv ℝ (fun y => fderiv ℝ (fun z : Space n => (‖z‖^k)⁻¹) y v) x v =
      (k:ℝ)*(k+2:ℕ)*(‖x‖^(k+4))⁻¹*(inner ℝ x v)^2 -
        (k:ℝ)*(‖x‖^(k+2))⁻¹*‖v‖^2 := by
  have hq := P201.BallPoisson.norm_inv_pow_hasFDerivAt (0 : Space n) x (k+2) hx
  simp only [sub_zero] at hq
  have hp : HasFDerivAt (fun y : Space n => inner ℝ y v) (innerSL ℝ v) x := by
    convert (innerSL ℝ v).hasFDerivAt (x := x) using 1
    funext y
    exact real_inner_comm v y
  have hd := (hq.const_mul (-(k:ℝ))).mul hp
  change HasFDerivAt (fun y : Space n => -(k:ℝ)*(‖y‖^(k+2))⁻¹*inner ℝ y v) _ x at hd
  have heq : (fun y => fderiv ℝ (fun z : Space n => (‖z‖^k)⁻¹) y v) =ᶠ[𝓝 x]
      (fun y => -(k:ℝ)*(‖y‖^(k+2))⁻¹*inner ℝ y v) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact normInvPow_fderiv_apply hy k v
  rw [heq.fderiv_eq,hd.fderiv]
  simp only [add_apply,smul_apply,innerSL_apply_apply,smul_eq_mul,real_inner_self_eq_norm_sq,
    div_eq_mul_inv,show k+2+2=k+4 by omega,Pi.mul_apply]
  rw [real_inner_comm v x]
  ring

lemma normInvPow_laplacian {n : ℕ} {x : Space n} (hx : x ≠ 0) (k : ℕ) :
    P201Specs.laplacian (fun y : Space n => (‖y‖^k)⁻¹) x =
      (k:ℝ)*((k:ℝ)+2-n)*(‖x‖^(k+2))⁻¹ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let f := fun y : Space n => (‖y‖^k)⁻¹
  have hc : ContDiffAt ℝ 2 f x :=
    ((contDiffAt_norm ℝ hx).pow k).inv (pow_ne_zero k (norm_ne_zero_iff.mpr hx))
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hiter (v : Space n) : iteratedFDeriv ℝ 2 f x ![v,v] =
      fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
    rw [iteratedFDeriv_two_apply,fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [P201.MeanValues.laplacian_bridge _ _ hc,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp_rw [hiter]
  change (∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z : Space n => (‖z‖^k)⁻¹) y (b i)) x (b i)) = _
  simp_rw [normInvPow_secondDirectional hx k]
  simp only [b.orthonormal.norm_eq_one,one_pow,mul_one,Finset.sum_sub_distrib,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hsq : (∑ i : Fin n, (inner ℝ x (b i))^2) = ‖x‖^2 := b.sum_sq_inner_left x
  rw [hsq]
  simp only [pow_add]
  field_simp [norm_ne_zero_iff.mpr hx]
  push_cast
  ring

lemma kelvin_weight_harmonic {n : ℕ} (hn : 2 ≤ n) {x : Space n} (hx : x ≠ 0) :
    P201Specs.laplacian (fun y : Space n => (‖y‖^(n-2))⁻¹) x = 0 := by
  rw [normInvPow_laplacian hx]
  have hcast : ((n-2:ℕ):ℝ)+2-n=0 := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [hcast,mul_zero,zero_mul]

lemma secondDirectional_comp {n : ℕ} {u : Space n → ℝ} {g : Space n → Space n}
    {x : Space n} (hu : ContDiffAt ℝ 2 u (g x)) (hg : ContDiffAt ℝ 2 g x) (v : Space n) :
    fderiv ℝ (fun y => fderiv ℝ (u ∘ g) y v) x v =
      fderiv ℝ (fderiv ℝ u) (g x) (fderiv ℝ g x v) (fderiv ℝ g x v) +
      fderiv ℝ u (g x) (fderiv ℝ (fun y => fderiv ℝ g y v) x v) := by
  have huD : DifferentiableAt ℝ (fderiv ℝ u) (g x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hgD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hA : DifferentiableAt ℝ (fun y => fderiv ℝ u (g y)) x :=
    huD.comp x (hg.differentiableAt (by norm_num))
  have hB : DifferentiableAt ℝ (fun y => fderiv ℝ g y v) x :=
    hgD.clm_apply (differentiableAt_const v)
  have heq : (fun y => fderiv ℝ (u ∘ g) y v) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u (g y) (fderiv ℝ g y v)) := by
    filter_upwards [(hg.continuousAt.tendsto).eventually (hu.eventually (by norm_num)),
      hg.eventually (by norm_num)] with y huy hgy
    rw [fderiv_comp y (huy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))]
    rfl
  rw [heq.fderiv_eq,fderiv_clm_apply hA hB,
    fderiv_fun_comp x huD (hg.differentiableAt (by norm_num))]
  simp only [add_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply]
  exact add_comm _ _

lemma unitInversion_second_trace {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    (∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ unitInversion y (coordinate n i)) x (coordinate n i)) =
      ((4-2*(n:ℝ))*(‖x‖^4)⁻¹) • x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  change (∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ unitInversion y (b i)) x (b i)) = _
  simp_rw [unitInversion_secondDirectional hx]
  simp only [b.orthonormal.norm_eq_one,one_pow,mul_one]
  have hs : (∑ i : Fin n, inner ℝ x (b i) • b i) = x := by
    simpa only [real_inner_comm] using b.sum_repr' x
  have hsq : (∑ i : Fin n, (inner ℝ x (b i))^2) = ‖x‖^2 := b.sum_sq_inner_left x
  have hfirst : (∑ i : Fin n, -(4*(‖x‖^4)⁻¹*inner ℝ x (b i)) • b i) =
      (-(4*(‖x‖^4)⁻¹)) • x := by
    calc
      _ = (-(4*(‖x‖^4)⁻¹)) • (∑ i : Fin n, inner ℝ x (b i) • b i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        module
      _ = _ := by rw [hs]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin]
  rw [hfirst]
  have hlast : (∑ i : Fin n, (8*(‖x‖^6)⁻¹*(inner ℝ x (b i))^2) • x) =
      (8*(‖x‖^6)⁻¹*‖x‖^2) • x := by
    rw [← Finset.sum_smul,← Finset.mul_sum,hsq]
  rw [hlast]
  have hpower : (‖x‖^6)⁻¹*‖x‖^2 = (‖x‖^4)⁻¹ := by
    field_simp [norm_ne_zero_iff.mpr hx] <;> ring
  simp only [mul_assoc, hpower]
  module

lemma laplacian_eq_hessian_trace {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) (b : OrthonormalBasis (Fin n) ℝ (Space n)) :
    P201Specs.laplacian u x = ∑ i, fderiv ℝ (fderiv ℝ u) x (b i) (b i) := by
  rw [P201.MeanValues.laplacian_bridge _ _ hu,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]

lemma unitInversion_contDiffAt {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 unitInversion x := by
  exact contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx

lemma laplacian_comp_unitInversion {n : ℕ} {u : Space n → ℝ} {x : Space n} (hx : x ≠ 0)
    (hu : ContDiffAt ℝ 2 u (unitInversion x)) :
    P201Specs.laplacian (u ∘ unitInversion) x =
      (‖x‖^4)⁻¹ * P201Specs.laplacian u (unitInversion x) +
      ((4-2*(n:ℝ))*(‖x‖^4)⁻¹) * fderiv ℝ u (unitInversion x) x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let e := (ℝ ∙ x)ᗮ.reflection
  have hI := unitInversion_contDiffAt hx
  have hcomp := hu.comp x hI
  have hDI (v : Space n) : fderiv ℝ unitInversion x v = (‖x‖^2)⁻¹ • e v := by
    have hd := EuclideanGeometry.hasFDerivAt_inversion (R := (1:ℝ)) hx
    change HasFDerivAt unitInversion _ x at hd
    rw [hd.fderiv]
    simp only [dist_zero_right,one_div,inv_pow,smul_apply,sub_zero]
    rfl
  have hiter (v : Space n) : iteratedFDeriv ℝ 2 (u ∘ unitInversion) x ![v,v] =
      fderiv ℝ (fun y => fderiv ℝ (u ∘ unitInversion) y v) x v := by
    have hd : DifferentiableAt ℝ (fderiv ℝ (u ∘ unitInversion)) x :=
      (hcomp.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [iteratedFDeriv_two_apply,fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [P201.MeanValues.laplacian_bridge _ _ hcomp,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp_rw [hiter,secondDirectional_comp hu hI]
  rw [Finset.sum_add_distrib]
  have hA : (∑ i : Fin n,
      fderiv ℝ (fderiv ℝ u) (unitInversion x) (fderiv ℝ unitInversion x (b i))
        (fderiv ℝ unitInversion x (b i))) =
        (‖x‖^4)⁻¹ * P201Specs.laplacian u (unitInversion x) := by
    rw [laplacian_eq_hessian_trace hu (b.map e),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [hDI]
    simp only [map_smul,smul_apply,smul_eq_mul,OrthonormalBasis.map_apply]
    ring
  rw [hA]
  congr 1
  have ht := unitInversion_second_trace hx
  change (∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ unitInversion y (b i)) x (b i)) = _ at ht
  rw [← map_sum,ht,map_smul,smul_eq_mul]

lemma unitInversion_fderiv_self {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    fderiv ℝ unitInversion x x = -(‖x‖^2)⁻¹ • x := by
  rw [unitInversion_fderiv_apply hx]
  have hpower : (‖x‖^4)⁻¹*‖x‖^2 = (‖x‖^2)⁻¹ := by
    field_simp [norm_ne_zero_iff.mpr hx] <;> ring
  rw [real_inner_self_eq_norm_sq,mul_assoc,hpower]
  module

lemma kelvin_gradient_cross_trace {n : ℕ} {u : Space n → ℝ} {x : Space n} (hx : x ≠ 0)
    (hu : ContDiffAt ℝ 2 u (unitInversion x)) (k : ℕ) :
    (∑ i : Fin n,
      fderiv ℝ (fun y : Space n => (‖y‖^k)⁻¹) x (coordinate n i) *
        fderiv ℝ (u ∘ unitInversion) x (coordinate n i)) =
      (k:ℝ)*(‖x‖^(k+4))⁻¹*fderiv ℝ u (unitInversion x) x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let T := (fderiv ℝ u (unitInversion x)).comp (fderiv ℝ unitInversion x)
  have hs : (∑ i : Fin n, inner ℝ x (b i) * T (b i)) = T x := by
    calc
      _ = T (∑ i : Fin n, inner ℝ x (b i) • b i) := by
        simp only [map_sum,map_smul,smul_eq_mul]
      _ = _ := by
        congr 1
        simpa only [real_inner_comm] using b.sum_repr' x
  have ht : fderiv ℝ (u ∘ unitInversion) x = T :=
    fderiv_comp x (hu.differentiableAt (by norm_num))
      ((unitInversion_contDiffAt hx).differentiableAt (by norm_num))
  change (∑ i : Fin n, fderiv ℝ (fun y : Space n => (‖y‖^k)⁻¹) x (b i) *
    fderiv ℝ (u ∘ unitInversion) x (b i)) = _
  simp_rw [normInvPow_fderiv_apply hx k,ht]
  simp only [mul_assoc,← Finset.mul_sum,hs]
  change -(k:ℝ)*((‖x‖^(k+2))⁻¹ *
    fderiv ℝ u (unitInversion x) (fderiv ℝ unitInversion x x)) = _
  rw [unitInversion_fderiv_self hx,map_smul,smul_eq_mul]
  simp only [pow_add]
  ring

def kelvinTransform {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  (‖x‖^(n-2))⁻¹ * u (unitInversion x)

lemma unitInversion_norm {n : ℕ} (x : Space n) : ‖unitInversion x‖ = ‖x‖⁻¹ := by
  have h := EuclideanGeometry.dist_inversion_center (0 : Space n) x 1
  simpa only [unitInversion,dist_zero_right,one_pow,one_div] using h

lemma unitInversion_involutive {n : ℕ} (x : Space n) : unitInversion (unitInversion x) = x :=
  EuclideanGeometry.inversion_inversion 0 one_ne_zero x

lemma kelvinTransform_involutive {n : ℕ} (u : Space n → ℝ) {x : Space n} (hx : x ≠ 0) :
    kelvinTransform (kelvinTransform u) x = u x := by
  simp only [kelvinTransform,unitInversion_involutive,unitInversion_norm,inv_pow,inv_inv]
  rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hx)),one_mul]

lemma normInvPow_contDiffAt {n : ℕ} {x : Space n} (hx : x ≠ 0) (k : ℕ) :
    ContDiffAt ℝ 2 (fun y : Space n => (‖y‖^k)⁻¹) x :=
  ((contDiffAt_norm ℝ hx).pow k).inv (pow_ne_zero k (norm_ne_zero_iff.mpr hx))

lemma kelvinTransform_contDiffAt {n : ℕ} {u : Space n → ℝ} {x : Space n} (hx : x ≠ 0)
    (hu : ContDiffAt ℝ 2 u (unitInversion x)) : ContDiffAt ℝ 2 (kelvinTransform u) x :=
  (normInvPow_contDiffAt hx (n-2)).mul (hu.comp x (unitInversion_contDiffAt hx))

/-- The full Kelvin identity for a genuinely C² function at the inverted point.
The inverse natural power equals the usual |x|^(2-n) weight for n≥2. -/
lemma laplacian_kelvinTransform {n : ℕ} (hn : 2 ≤ n) {u : Space n → ℝ}
    {x : Space n} (hx : x ≠ 0) (hu : ContDiffAt ℝ 2 u (unitInversion x)) :
    P201Specs.laplacian (kelvinTransform u) x = (‖x‖^(n+2))⁻¹ * P201Specs.laplacian u (unitInversion x) := by
  have hW := normInvPow_contDiffAt hx (n-2)
  have hcomp := hu.comp x (unitInversion_contDiffAt hx)
  change P201Specs.laplacian (fun y => (‖y‖^(n-2))⁻¹ * (u ∘ unitInversion) y) x = _
  rw [KelvinProduct.laplacian_mul hW hcomp,kelvin_weight_harmonic hn hx,
    mul_zero,add_zero,laplacian_comp_unitInversion hx hu,kelvin_gradient_cross_trace hx hu]
  have hpow : ‖x‖^(n+2) = ‖x‖^(n-2) * ‖x‖^4 := by
    rw [← pow_add]
    congr 1
    omega
  have hpow' : n-2+4=n+2 := by omega
  rw [hpow',hpow]
  rw [Nat.cast_sub hn]
  push_cast
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

lemma kelvinTransform_harmonic {n : ℕ} (hn : 2 ≤ n) (Ω V : Domain n)
    {u : Space n → ℝ} (hu : P201Specs.MeanValues.IsHarmonic Ω u)
    (hx : ∀ x ∈ V, x ≠ 0) (hmap : MapsTo unitInversion (V : Set (Space n)) (Ω : Set (Space n))) :
    P201Specs.MeanValues.IsHarmonic V (kelvinTransform u) := by
  refine ⟨?_,?_⟩
  · intro x hxV
    exact (kelvinTransform_contDiffAt (hx x hxV)
      ((hu.1 _ (hmap hxV)).contDiffAt (Ω.isOpen.mem_nhds (hmap hxV)))).contDiffWithinAt
  · intro x hxV
    rw [laplacian_kelvinTransform hn (hx x hxV)
      ((hu.1 _ (hmap hxV)).contDiffAt (Ω.isOpen.mem_nhds (hmap hxV))),hu.2 _ (hmap hxV),mul_zero]
lemma unitInversion_norm_sub_sq {n : ℕ} (a : Space n) {x : Space n} (hx : x ≠ 0) :
    ‖unitInversion x-a‖^2 * ‖x‖^2 = 1-2*inner ℝ a x+‖a‖^2*‖x‖^2 := by
  rw [norm_sub_sq_real,unitInversion_norm,unitInversion_apply]
  simp only [inner_smul_left,conj_trivial,real_inner_comm x a]
  field_simp [norm_ne_zero_iff.mpr hx] <;> ring

lemma unitInversion_mem_ball_tangent {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r)
    (ha : ‖a‖=r) {x : Space n} (hx : x ≠ 0) :
    unitInversion x ∈ ball a r ↔ (1:ℝ)/2 < inner ℝ a x := by
  have hq : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hs := unitInversion_norm_sub_sq a hx
  rw [ha] at hs
  rw [mem_ball,dist_eq_norm]
  constructor
  · intro h
    have hlt : ‖unitInversion x-a‖^2 < r^2 := by nlinarith [norm_nonneg (unitInversion x-a)]
    have hm := mul_lt_mul_of_pos_right hlt hq
    nlinarith
  · intro h
    have hlt : ‖unitInversion x-a‖^2 < r^2 := by
      nlinarith
    nlinarith [norm_nonneg (unitInversion x-a)]

lemma unitInversion_mem_closedBall_tangent {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r)
    (ha : ‖a‖=r) {x : Space n} (hx : x ≠ 0) :
    unitInversion x ∈ closedBall a r ↔ (1:ℝ)/2 ≤ inner ℝ a x := by
  have hq : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hs := unitInversion_norm_sub_sq a hx
  rw [ha] at hs
  rw [mem_closedBall,dist_eq_norm]
  constructor
  · intro h
    have hle : ‖unitInversion x-a‖^2 ≤ r^2 := by nlinarith [norm_nonneg (unitInversion x-a)]
    have hm := mul_le_mul_of_nonneg_right hle hq.le
    nlinarith
  · intro h
    have hle : ‖unitInversion x-a‖^2 ≤ r^2 := by
      nlinarith
    nlinarith [norm_nonneg (unitInversion x-a)]

lemma unitInversion_mem_sphere_tangent {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r)
    (ha : ‖a‖=r) {x : Space n} (hx : x ≠ 0) :
    unitInversion x ∈ sphere a r ↔ inner ℝ a x=(1:ℝ)/2 := by
  have hq : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hs := unitInversion_norm_sub_sq a hx
  rw [ha] at hs
  rw [mem_sphere,dist_eq_norm]
  constructor
  · intro h
    rw [h] at hs
    linarith
  · intro h
    have heq : ‖unitInversion x-a‖^2 = r^2 := by
      nlinarith
    nlinarith [norm_nonneg (unitInversion x-a)]

lemma kelvin_weight_eq_rpow {n : ℕ} (hn : 2 ≤ n) (x : Space n) :
    (‖x‖^(n-2))⁻¹ = ‖x‖ ^ (2-(n:ℝ)) := by
  calc
    _ = ‖x‖ ^ (-((n-2:ℕ):ℝ)) := by
      rw [Real.rpow_neg (norm_nonneg x),Real.rpow_natCast]
    _ = _ := by
      congr 1
      rw [Nat.cast_sub hn]
      push_cast
      ring

lemma kelvin_equation_factor_eq_rpow {n : ℕ} (x : Space n) :
    (‖x‖^(n+2))⁻¹ = ‖x‖ ^ (-(n:ℝ)-2) := by
  calc
    _ = ‖x‖ ^ (-((n+2:ℕ):ℝ)) := by
      rw [Real.rpow_neg (norm_nonneg x),Real.rpow_natCast]
    _ = _ := by push_cast; ring

lemma kelvinTransform_eq_rpow {n : ℕ} (hn : 2 ≤ n) (u : Space n → ℝ) (x : Space n) :
    kelvinTransform u x = ‖x‖ ^ (2-(n:ℝ))*u (unitInversion x) := by
  rw [kelvinTransform,kelvin_weight_eq_rpow hn]

lemma laplacian_kelvinTransform_rpow {n : ℕ} (hn : 2 ≤ n) {u : Space n → ℝ}
    {x : Space n} (hx : x ≠ 0) (hu : ContDiffAt ℝ 2 u (unitInversion x)) :
    P201Specs.laplacian (fun y => ‖y‖ ^ (2-(n:ℝ))*u (unitInversion y)) x =
      ‖x‖ ^ (-(n:ℝ)-2)*P201Specs.laplacian u (unitInversion x) := by
  have heq : (fun y => ‖y‖ ^ (2-(n:ℝ))*u (unitInversion y)) = kelvinTransform u := by
    funext y
    exact (kelvinTransform_eq_rpow hn u y).symm
  rw [heq,laplacian_kelvinTransform hn hx hu,kelvin_equation_factor_eq_rpow]

end KelvinCalculus



lemma isC2HolderUpToOn_congr {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {u v : Space n → ℝ} (hu : IsC2HolderUpToOn α u s) (hEq : EqOn v u s) :
    IsC2HolderUpToOn α v s := by
  have hfirst (i : Fin n) : EqOn (firstPartialWithin v s i) (firstPartialWithin u s i) s := by
    intro x hx
    unfold firstPartialWithin
    rw [fderivWithin_congr' hEq hx]
  have hsecond (i j : Fin n) : EqOn (secondPartialWithin v s i j) (secondPartialWithin u s i j) s := by
    intro x hx
    unfold secondPartialWithin
    rw [fderivWithin_congr' (hfirst j) hx]
  refine ⟨hu.1.congr hEq,?_,?_,?_⟩
  · obtain ⟨M,hM,hb⟩ := hu.2.1
    exact ⟨M,hM,fun x hx => by rw [hEq hx]; exact hb x hx⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := hu.2.2.1 i
    exact ⟨M,hM,fun x hx => by rw [hfirst i hx]; exact hb x hx⟩
  · intro i j
    exact P201.Elliptic.PoissonSchauder.isHolderOn_congr (hu.2.2.2 i j) (hsecond i j)

lemma isC2HolderUpToOn_of_classical_on_open {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {Ω : Domain n} {s : Set (Space n)} (hsub : s ⊆ (Ω : Set (Space n)))
    (hu : ContDiffOn ℝ 2 u Ω) (hs : UniqueDiffOn ℝ s)
    (hholder : IsC2HolderOn α u s) : IsC2HolderUpToOn α u s := by
  have hfirst (i : Fin n) : EqOn (firstPartialWithin u s i) (P201Specs.multiPartial u {i}) s := by
    intro x hx
    simp only [firstPartialWithin, P201Specs.multiPartial, P102.U4.multiPartial,
      Multiset.sort_singleton, P102.U4.partialWord]
    rw [fderivWithin_eq_fderiv (hs x hx)
      ((hu.contDiffAt (Ω.isOpen.mem_nhds (hsub hx))).differentiableAt (by norm_num))]
  have hsecond (i j : Fin n) : EqOn (secondPartialWithin u s i j) (P201Specs.multiPartial u {i,j}) s := by
    intro x hx
    have hux := hu.contDiffAt (Ω.isOpen.mem_nhds (hsub hx))
    have hd : DifferentiableAt ℝ (firstPartial u j) x :=
      ((hux.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt one_ne_zero
    unfold secondPartialWithin
    have hfirst' : EqOn (firstPartialWithin u s j) (firstPartial u j) s := by
      intro y hy
      simpa only [P201Specs.multiPartial,P102.U4.multiPartial,Multiset.sort_singleton,P102.U4.partialWord,firstPartial] using hfirst j hy
    rw [fderivWithin_congr' hfirst' hx, fderivWithin_eq_fderiv (hs x hx) hd]
    exact secondPartial_eq_multiPartial_at hux i j
  refine ⟨hholder.1,hholder.2.1,?_,?_⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := hholder.2.2.1 i
    exact ⟨M,hM,fun x hx => by rw [hfirst i hx]; exact hb x hx⟩
  · intro i j
    exact P201.Elliptic.PoissonSchauder.isHolderOn_congr (hholder.2.2.2 i j) (hsecond i j)

lemma smooth_c2HolderUpToOn_compact_convex_on_open {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {Ω : Domain n} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ (3 : ℕ) u Ω) {s : Set (Space n)}
    (hs : IsCompact s) (hconv : Convex ℝ s) (hUnique : UniqueDiffOn ℝ s)
    (hsub : s ⊆ (Ω : Set (Space n))) : IsC2HolderUpToOn α u s := by
  have bounded {f : Space n → ℝ} (hf : ContinuousOn f s) : IsBoundedOn f s := by
    obtain ⟨M,hM⟩ := hs.exists_bound_of_continuousOn hf
    exact ⟨max M 0,le_max_right _ _,fun x hx => (hM x hx).trans (le_max_left _ _)⟩
  apply isC2HolderUpToOn_of_classical_on_open hsub (hu.of_le (by norm_num)) hUnique
  refine ⟨(hu.of_le (by norm_num)).mono hsub,bounded (hu.continuousOn.mono hsub),?_,?_⟩
  · intro i
    exact bounded (((P102.U4.partialWord_contDiffOn Ω hu
      (({i} : MultiIndex n).sort (· ≤ ·)) 1 (by simp)).continuousOn).mono hsub)
  · exact P201.Elliptic.PoissonSchauder.smooth_holder_on_compact_convex hα hα1 Ω hu hs hconv hsub


namespace BallC2Complete
set_option backward.isDefEq.respectTransparency false
open P201Specs P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201.Elliptic.BallSchauderSolvability


lemma firstPartialWithin_sub {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ 1 u s) (hv : ContDiffOn ℝ 1 v s)
    (i : Fin n) : EqOn (firstPartialWithin (u-v) s i)
      (firstPartialWithin u s i-firstPartialWithin v s i) s := by
  intro x hx
  unfold firstPartialWithin
  rw [fderivWithin_sub (hs x hx) (hu.differentiableOn (by norm_num) x hx)
    (hv.differentiableOn (by norm_num) x hx)]
  rfl

lemma secondPartialWithin_sub {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ 2 u s) (hv : ContDiffOn ℝ 2 v s)
    (i j : Fin n) : EqOn (secondPartialWithin (u-v) s i j)
      (secondPartialWithin u s i j-secondPartialWithin v s i j) s := by
  intro x hx
  have hD1u : ContDiffOn ℝ 1 (firstPartialWithin u s j) s :=
    (hu.fderivWithin (m := 1) hs (by norm_num)).clm_apply contDiffOn_const
  have hD1v : ContDiffOn ℝ 1 (firstPartialWithin v s j) s :=
    (hv.fderivWithin (m := 1) hs (by norm_num)).clm_apply contDiffOn_const
  unfold secondPartialWithin
  rw [fderivWithin_congr' (firstPartialWithin_sub hs (hu.of_le (by norm_num))
      (hv.of_le (by norm_num)) j) hx,
    fderivWithin_sub (hs x hx) (hD1u.differentiableOn (by norm_num) x hx)
      (hD1v.differentiableOn (by norm_num) x hx)]
  rfl

lemma isBoundedOn_sub {n : ℕ} {s : Set (Space n)} {u v : Space n → ℝ}
    (hu : IsBoundedOn u s) (hv : IsBoundedOn v s) : IsBoundedOn (u-v) s := by
  obtain ⟨M,hM,hb⟩ := hu
  obtain ⟨N,hN,hc⟩ := hv
  exact ⟨M+N,add_nonneg hM hN,fun x hx => (norm_sub_le _ _).trans (add_le_add (hb x hx) (hc x hx))⟩

lemma isHolderOn_sub {n : ℕ} {s : Set (Space n)} {α : ℝ} {u v : Space n → ℝ}
    (hu : IsHolderOn α u s) (hv : IsHolderOn α v s) : IsHolderOn α (u-v) s := by
  change IsHolderOn α (fun x => u x-v x) s
  simpa only [neg_one_mul,sub_eq_add_neg] using
    isHolderOn_add hu (isHolderOn_const_mul hv (-1))

lemma isC2HolderUpToOn_sub {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {α : ℝ} {u v : Space n → ℝ} (hu : IsC2HolderUpToOn α u s) (hv : IsC2HolderUpToOn α v s) :
    IsC2HolderUpToOn α (u-v) s := by
  refine ⟨hu.1.sub hv.1,isBoundedOn_sub hu.2.1 hv.2.1,?_,?_⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := isBoundedOn_sub (hu.2.2.1 i) (hv.2.2.1 i)
    exact ⟨M,hM,fun x hx => by
      rw [firstPartialWithin_sub hs (hu.1.of_le (by norm_num)) (hv.1.of_le (by norm_num)) i hx]
      exact hb x hx⟩
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_sub (hu.2.2.2 i j) (hv.2.2.2 i j))
    exact secondPartialWithin_sub hs hu.1 hv.1 i j

lemma supNormOn_congr {n : ℕ} {s : Set (Space n)} {u v : Space n → ℝ} (h : EqOn u v s) :
    supNormOn u s = supNormOn v s := by
  unfold supNormOn
  congr 1
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩; exact ⟨x,hx,by rw [h hx]⟩
  · rintro ⟨x,hx,rfl⟩; exact ⟨x,hx,by rw [h hx]⟩

lemma holderNormOn_congr {n : ℕ} {s : Set (Space n)} {α : ℝ} {u v : Space n → ℝ}
    (h : EqOn u v s) : holderNormOn α u s = holderNormOn α v s := by
  have h0 := supNormOn_congr h
  change supNormOn u s+holderSeminormOn α u s = supNormOn v s+holderSeminormOn α v s
  rw [h0]
  congr 1
  unfold holderSeminormOn
  congr 1
  ext t
  constructor
  · rintro ⟨x,hx,y,hy,hxy,rfl⟩; exact ⟨x,hx,y,hy,hxy,by rw [h hx,h hy]⟩
  · rintro ⟨x,hx,y,hy,hxy,rfl⟩; exact ⟨x,hx,y,hy,hxy,by rw [h hx,h hy]⟩


lemma secondPartialWithin_eq_second_fderivWithin {n : ℕ} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u s)
    {x : Space n} (hx : x ∈ s) (i j : Fin n) :
    secondPartialWithin u s i j x =
      fderivWithin ℝ (fderivWithin ℝ u s) s x (coordinate n i) (coordinate n j) := by
  unfold secondPartialWithin firstPartialWithin
  rw [fderivWithin_clm_apply (hs x hx)
    ((hu.fderivWithin (m := 1) hs (by norm_num)).differentiableOn (by norm_num) x hx)
    (differentiableWithinAt_const (coordinate n j))]
  simp only [fderivWithin_const_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]

lemma second_fderivWithin_sub {n : ℕ} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) {u v : Space n → ℝ} (hu : ContDiffOn ℝ 2 u s) (hv : ContDiffOn ℝ 2 v s)
    {x : Space n} (hx : x ∈ s) :
    fderivWithin ℝ (fderivWithin ℝ (u-v) s) s x =
      fderivWithin ℝ (fderivWithin ℝ u s) s x-fderivWithin ℝ (fderivWithin ℝ v s) s x := by
  have heq : EqOn (fderivWithin ℝ (u-v) s) (fderivWithin ℝ u s-fderivWithin ℝ v s) s := by
    intro y hy
    exact fderivWithin_sub (hs y hy) (hu.differentiableOn (by norm_num) y hy)
      (hv.differentiableOn (by norm_num) y hy)
  rw [fderivWithin_congr' heq hx]
  exact fderivWithin_sub (hs x hx)
    ((hu.fderivWithin (m := 1) hs (by norm_num)).differentiableOn (by norm_num) x hx)
    ((hv.fderivWithin (m := 1) hs (by norm_num)).differentiableOn (by norm_num) x hx)


lemma norm_second_fderivWithin_le_c2HolderUpToNormOn {n : ℕ} {α : ℝ} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u s)
    {x : Space n} (hx : x ∈ s) :
    ‖fderivWithin ℝ (fderivWithin ℝ u s) s x‖ ≤ c2HolderUpToNormOn α u s := by
  apply (norm_clm_le_sum_coordinates _).trans
  apply le_trans ?_ (c2HolderUpToNormOn_components α u s).2.2.2.1
  apply Finset.sum_le_sum
  intro i _
  apply (norm_clm_le_sum_coordinates _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [← secondPartialWithin_eq_second_fderivWithin hs hu.1 hx i j]
  exact norm_le_holderNormOn (hu.2.2.2 i j) hx

lemma uniformCauchyWithinJets_of_c2HolderUpToNormOn_cauchy {n : ℕ} {α : ℝ} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) {u : ℕ → Space n → ℝ}
    (hu : ∀ j, IsC2HolderUpToOn α (u j) s)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      c2HolderUpToNormOn α (u j-u k) s < ε) :
    UniformCauchySeqOn (fun j => fderivWithin ℝ (u j) s) atTop s ∧
      UniformCauchySeqOn (fun j => fderivWithin ℝ (fderivWithin ℝ (u j) s) s) atTop s := by
  constructor
  · apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hc ε hε
    refine ⟨N,fun j hj k hk x hx => ?_⟩
    rw [dist_eq_norm,← fderivWithin_sub (hs x hx)
      ((hu j).1.differentiableOn (by norm_num) x hx) ((hu k).1.differentiableOn (by norm_num) x hx)]
    exact (norm_fderivWithin_le_c2HolderUpToNormOn (isC2HolderUpToOn_sub hs (hu j) (hu k)) hx).trans_lt (hN j hj k hk)
  · apply (Metric.uniformCauchySeqOn_iff (α := Space n →L[ℝ] Space n →L[ℝ] ℝ)).mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hc ε hε
    refine ⟨N,fun j hj k hk x hx => ?_⟩
    rw [dist_eq_norm (fderivWithin ℝ (fderivWithin ℝ (u j) s) s x)
      (fderivWithin ℝ (fderivWithin ℝ (u k) s) s x),← second_fderivWithin_sub hs (hu j).1 (hu k).1 hx]
    exact (norm_second_fderivWithin_le_c2HolderUpToNormOn hs (isC2HolderUpToOn_sub hs (hu j) (hu k)) hx).trans_lt (hN j hj k hk)

lemma tendstoUniformlyOn_of_holderNormOn_tendsto {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, IsHolderOn α (u j) s) (hv : IsHolderOn α v s)
    (hlim : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, holderNormOn α (u j-v) s < ε) :
    TendstoUniformlyOn u v atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := hlim ε hε
  filter_upwards [eventually_ge_atTop N] with j hj x hx
  simpa only [dist_eq_norm,norm_sub_rev,Pi.sub_apply] using
    (norm_le_holderNormOn (isHolderOn_sub (hu j) hv) hx).trans_lt (hN j hj)

lemma tendsto_zero_of_nonneg_bound {u : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j)
    (hlim : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, u j < ε) : Tendsto u atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := hlim ε hε
  exact ⟨N,fun j hj => by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (hu j)] using hN j hj⟩


lemma c2HolderUpToNormOn_complete {n : ℕ} {α r : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (z : Space n) (hr : 0 < r) (u : ℕ → Space n → ℝ)
    (hu : ∀ j, IsC2HolderUpToOn α (u j) (closedBall z r))
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      c2HolderUpToNormOn α (u j-u k) (closedBall z r) < ε) :
    ∃ g : Space n → ℝ, IsC2HolderUpToOn α g (closedBall z r) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, c2HolderUpToNormOn α (u j-g) (closedBall z r) < ε := by
  let s := closedBall z r
  have hs : UniqueDiffOn ℝ s := BallWithinLimit.uniqueDiffOn_closedBall z hr
  have hlow (j : ℕ) := lower_order_holder_jets_on_closedBall hα.le hα1 z hr (hu j)
  have hC0 : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, holderNormOn α (u j-u k) s < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hc (ε/4) (by positivity)
    refine ⟨N,fun j hj k hk => ?_⟩
    have hb := (lower_order_holderNormOn_le_four_c2HolderUpToNormOn hα.le hα1 z hr
      (isC2HolderUpToOn_sub hs (hu j) (hu k))).1
    have hsmall := hN j hj k hk
    dsimp [s] at *
    linarith
  obtain ⟨g,hg,hgconv⟩ := BallHolderSpace.holderNormOn_complete hα u (fun j => (hlow j).1) hC0
  have hC1 (i : Fin n) : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      holderNormOn α (firstPartialWithin (u j) s i-firstPartialWithin (u k) s i) s < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hc (ε/4) (by positivity)
    refine ⟨N,fun j hj k hk => ?_⟩
    rw [← holderNormOn_congr (firstPartialWithin_sub hs ((hu j).1.of_le (by norm_num))
      ((hu k).1.of_le (by norm_num)) i)]
    have hb := (lower_order_holderNormOn_le_four_c2HolderUpToNormOn hα.le hα1 z hr
      (isC2HolderUpToOn_sub hs (hu j) (hu k))).2 i
    have hsmall := hN j hj k hk
    dsimp [s] at *
    linarith
  have hFirst (i : Fin n) := BallHolderSpace.holderNormOn_complete hα
    (fun j => firstPartialWithin (u j) s i) (fun j => (hlow j).2 i) (hC1 i)
  choose v1 hv1 hv1conv using hFirst
  have hC2 (i j : Fin n) : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      holderNormOn α (secondPartialWithin (u p) s i j-secondPartialWithin (u q) s i j) s < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hc ε hε
    refine ⟨N,fun p hp q hq => ?_⟩
    rw [← holderNormOn_congr (secondPartialWithin_sub hs (hu p).1 (hu q).1 i j)]
    exact ((c2HolderUpToNormOn_components α (u p-u q) s).2.2.2.2 i j).trans_lt (hN p hp q hq)
  have hSecond (i j : Fin n) := BallHolderSpace.holderNormOn_complete hα
    (fun p => secondPartialWithin (u p) s i j) (fun p => (hu p).2.2.2 i j) (hC2 i j)
  choose v2 hv2 hv2conv using hSecond
  have hU := tendstoUniformlyOn_of_holderNormOn_tendsto (fun j => (hlow j).1) hg hgconv
  have hJets := uniformCauchyWithinJets_of_c2HolderUpToNormOn_cauchy hs hu hc
  obtain ⟨A,hA⟩ := exists_uniform_limit_of_uniformCauchySeqOn hJets.1
  obtain ⟨B,hB⟩ := exists_uniform_limit_of_uniformCauchySeqOn hJets.2
  have hG := BallWithinLimit.contDiffOn_two_closedBall_of_uniformWithinJets hr
    (fun j => (hu j).1) hU hA hB
  have hfirst (i : Fin n) : EqOn (firstPartialWithin g s i) (v1 i) s := by
    intro x hx
    have hp := (tendstoUniformlyOn_of_holderNormOn_tendsto
      (fun j => (hlow j).2 i) (hv1 i) (hv1conv i)).tendsto_at hx
    have hq : Tendsto (fun j => firstPartialWithin (u j) s i x) atTop (𝓝 (A x (coordinate n i))) :=
      ((ContinuousLinearMap.apply ℝ ℝ (coordinate n i)).continuous.tendsto (A x)).comp (hA.tendsto_at hx)
    have he := tendsto_nhds_unique hq hp
    unfold firstPartialWithin
    rw [hG.2.1 x hx,he]
  have hsecond (i j : Fin n) : EqOn (secondPartialWithin g s i j) (v2 i j) s := by
    intro x hx
    have hp := (tendstoUniformlyOn_of_holderNormOn_tendsto
      (fun p => (hu p).2.2.2 i j) (hv2 i j) (hv2conv i j)).tendsto_at hx
    have hq : Tendsto (fun p => secondPartialWithin (u p) s i j x) atTop
        (𝓝 (B x (coordinate n i) (coordinate n j))) := by
      let L : (Space n →L[ℝ] (Space n →L[ℝ] ℝ)) →L[ℝ] ℝ :=
        (ContinuousLinearMap.apply ℝ ℝ (coordinate n j)).comp
          (ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) (coordinate n i))
      have hh := (L.continuous.tendsto (B x)).comp (hB.tendsto_at hx)
      apply hh.congr'
      exact Eventually.of_forall (fun p => (secondPartialWithin_eq_second_fderivWithin hs (hu p).1 hx i j).symm)
    have he := tendsto_nhds_unique hq hp
    rw [secondPartialWithin_eq_second_fderivWithin hs hG.1 hx i j,
      fderivWithin_congr' hG.2.1 hx,hG.2.2 x hx,he]
  have hgUp : IsC2HolderUpToOn α g s := by
    refine ⟨hG.1,?_,?_,?_⟩
    · obtain ⟨M,H,hM,hH,hb,hh⟩ := hg
      exact ⟨M,hM,hb⟩
    · intro i
      obtain ⟨M,H,hM,hH,hb,hh⟩ := hv1 i
      exact ⟨M,hM,fun x hx => by rw [hfirst i hx]; exact hb x hx⟩
    · intro i j
      exact P201.Elliptic.PoissonSchauder.isHolderOn_congr (hv2 i j) (hsecond i j)
  have hpartial1 (p : ℕ) (i : Fin n) : EqOn (firstPartialWithin (u p-g) s i)
      (firstPartialWithin (u p) s i-v1 i) s := by
    intro x hx
    rw [firstPartialWithin_sub hs ((hu p).1.of_le (by norm_num)) (hgUp.1.of_le (by norm_num)) i hx]
    simp only [Pi.sub_apply,hfirst i hx]
  have hpartial2 (p : ℕ) (i j : Fin n) : EqOn (secondPartialWithin (u p-g) s i j)
      (secondPartialWithin (u p) s i j-v2 i j) s := by
    intro x hx
    rw [secondPartialWithin_sub hs (hu p).1 hgUp.1 i j hx]
    simp only [Pi.sub_apply,hsecond i j hx]
  have hbound (p : ℕ) : c2HolderUpToNormOn α (u p-g) s ≤
      holderNormOn α (u p-g) s +
        (∑ i : Fin n, holderNormOn α (firstPartialWithin (u p) s i-v1 i) s) +
        ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (secondPartialWithin (u p) s i j-v2 i j) s := by
    rw [c2HolderUpToNormOn_eq_holder_sums]
    apply add_le_add
    · apply add_le_add
      · exact le_add_of_nonneg_right (holderSeminormOn_nonneg _ _ _)
      · apply Finset.sum_le_sum
        intro i _
        rw [supNormOn_congr (hpartial1 p i)]
        exact le_add_of_nonneg_right (holderSeminormOn_nonneg _ _ _)
    · apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact le_of_eq (holderNormOn_congr (hpartial2 p i j))
  have hlim0 := tendsto_zero_of_nonneg_bound (fun p => holderNormOn_nonneg α (u p-g) s) hgconv
  have hlim1 (i : Fin n) := tendsto_zero_of_nonneg_bound
    (fun p => holderNormOn_nonneg α (firstPartialWithin (u p) s i-v1 i) s) (hv1conv i)
  have hlim2 (i j : Fin n) := tendsto_zero_of_nonneg_bound
    (fun p => holderNormOn_nonneg α (secondPartialWithin (u p) s i j-v2 i j) s) (hv2conv i j)
  have hlimSum1 := tendsto_finsetSum Finset.univ (fun i _ => hlim1 i)
  have hlimSum2 := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => hlim2 i j))
  have hlimBound : Tendsto (fun p => holderNormOn α (u p-g) s +
      (∑ i : Fin n, holderNormOn α (firstPartialWithin (u p) s i-v1 i) s) +
      ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (secondPartialWithin (u p) s i j-v2 i j) s)
      atTop (𝓝 0) := by simpa using (hlim0.add hlimSum1).add hlimSum2
  have hlim := squeeze_zero (fun p => c2HolderUpToNormOn_nonneg α (u p-g) s) hbound hlimBound
  refine ⟨g,hgUp,?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  exact ⟨N,fun p hp => by
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (c2HolderUpToNormOn_nonneg α (u p-g) s)] using hN p hp⟩

end BallC2Complete

namespace BallBanachX
set_option backward.isDefEq.respectTransparency false
open P201Specs P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201.Elliptic.BallSchauderSolvability
open BallC2Complete

variable {n : ℕ} {α : ℝ} {s : Set (Space n)} [CompactSpace s]
abbrev H (α : ℝ) (s : Set (Space n)) := BallHolderSpace.HolderSpace α s
abbrev JetAmbient (α : ℝ) (s : Set (Space n)) := H α s × (Fin n → H α s) × (Fin n → Fin n → H α s)

lemma scalar_rep_sub (v w : H α s) : BallHolderSpace.representative (v-w) =
    BallHolderSpace.representative v-BallHolderSpace.representative w :=
  (BallHolderSpace.representativeLinear α).map_sub v w

def Rep (v : JetAmbient α s) : Space n → ℝ := BallHolderSpace.representative v.1

lemma rep_sub (v w : JetAmbient α s) : Rep (v-w) = Rep v-Rep w :=
  (BallHolderSpace.representativeLinear α).map_sub v.1 w.1

lemma rep_smul (c : ℝ) (v : JetAmbient α s) : Rep (c • v) = c • Rep v :=
  (BallHolderSpace.representativeLinear α).map_smul c v.1

lemma firstPartialWithin_smul (hs : UniqueDiffOn ℝ s) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 1 u s) (c : ℝ) (i : Fin n) :
    EqOn (firstPartialWithin (c • u) s i) (c • firstPartialWithin u s i) s := by
  intro x hx
  unfold firstPartialWithin
  rw [((hu.differentiableOn (by norm_num) x hx).hasFDerivWithinAt.const_smul c).fderivWithin (hs x hx)]
  rfl

lemma secondPartialWithin_smul (hs : UniqueDiffOn ℝ s) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u s) (c : ℝ) (i j : Fin n) :
    EqOn (secondPartialWithin (c • u) s i j) (c • secondPartialWithin u s i j) s := by
  intro x hx
  have hd : ContDiffOn ℝ 1 (firstPartialWithin u s j) s :=
    (hu.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
  unfold secondPartialWithin
  rw [fderivWithin_congr' (firstPartialWithin_smul hs (hu.of_le (by norm_num)) c j) hx]
  rw [((hd.differentiableOn (by norm_num) x hx).hasFDerivWithinAt.const_smul c).fderivWithin (hs x hx)]
  rfl

def IsJet (t : Set (Space n)) (v : JetAmbient α s) : Prop :=
  ContDiffOn ℝ 2 (Rep v) s ∧
    (∀ i, EqOn (firstPartialWithin (Rep v) s i) (BallHolderSpace.representative (v.2.1 i)) s) ∧
    (∀ i j, EqOn (secondPartialWithin (Rep v) s i j) (BallHolderSpace.representative (v.2.2 i j)) s) ∧
    ∀ x ∈ t, Rep v x = 0

lemma isJet_sub (hs : UniqueDiffOn ℝ s) {t : Set (Space n)} {v w : JetAmbient α s}
    (hv : IsJet t v) (hw : IsJet t w) : IsJet t (v-w) := by
  rw [IsJet,rep_sub]
  refine ⟨hv.1.sub hw.1,?_,?_,?_⟩
  · intro i x hx
    rw [firstPartialWithin_sub hs (hv.1.of_le (by norm_num)) (hw.1.of_le (by norm_num)) i hx]
    change firstPartialWithin (Rep v) s i x-firstPartialWithin (Rep w) s i x =
      BallHolderSpace.representative (v.2.1 i-w.2.1 i) x
    rw [scalar_rep_sub]
    simp only [Pi.sub_apply,hv.2.1 i hx,hw.2.1 i hx]
  · intro i j x hx
    rw [secondPartialWithin_sub hs hv.1 hw.1 i j hx]
    change secondPartialWithin (Rep v) s i j x-secondPartialWithin (Rep w) s i j x =
      BallHolderSpace.representative (v.2.2 i j-w.2.2 i j) x
    rw [scalar_rep_sub]
    simp only [Pi.sub_apply,hv.2.2.1 i j hx,hw.2.2.1 i j hx]
  · intro x hx
    simp only [Pi.sub_apply,hv.2.2.2 x hx,hw.2.2.2 x hx,sub_self]

lemma isJet_smul (hs : UniqueDiffOn ℝ s) {t : Set (Space n)} {v : JetAmbient α s}
    (hv : IsJet t v) (c : ℝ) : IsJet t (c • v) := by
  rw [IsJet,rep_smul]
  refine ⟨hv.1.const_smul c,?_,?_,?_⟩
  · intro i x hx
    rw [firstPartialWithin_smul hs (hv.1.of_le (by norm_num)) c i hx]
    change c • firstPartialWithin (Rep v) s i x = BallHolderSpace.representative (c • v.2.1 i) x
    rw [BallHolderSpace.representative_smul]
    simp only [Pi.smul_apply,hv.2.1 i hx]
  · intro i j x hx
    rw [secondPartialWithin_smul hs hv.1 c i j hx]
    change c • secondPartialWithin (Rep v) s i j x = BallHolderSpace.representative (c • v.2.2 i j) x
    rw [BallHolderSpace.representative_smul]
    simp only [Pi.smul_apply,hv.2.2.1 i j hx]
  · intro x hx
    simp only [Pi.smul_apply,hv.2.2.2 x hx,smul_zero]

noncomputable def jetSubmodule (hs : UniqueDiffOn ℝ s) (t : Set (Space n)) : Submodule ℝ (JetAmbient α s) where
  carrier := {v | IsJet t v}
  zero_mem' := by
    have hrep : Rep (0 : JetAmbient α s) = 0 := (BallHolderSpace.representativeLinear α).map_zero
    change IsJet t (0 : JetAmbient α s)
    unfold IsJet
    rw [hrep]
    have hfirst0 (j : Fin n) : firstPartialWithin (0 : Space n → ℝ) s j = 0 := by
      funext x; simp [firstPartialWithin]
    refine ⟨contDiffOn_const,?_,?_,?_⟩
    · intro i x hx
      simp [firstPartialWithin,BallHolderSpace.representative,Rep]
    · intro i j x hx
      simp only [secondPartialWithin,hfirst0]
      simp [BallHolderSpace.representative]
    · intro x hx
      rfl
  add_mem' := by
    intro v w hv hw
    change IsJet t (v+w)
    have hh := isJet_sub hs hv (isJet_smul hs hw (-1))
    have he : (-1 : ℝ) • w = -w := neg_one_smul ℝ w
    rw [he,sub_neg_eq_add] at hh
    exact hh
  smul_mem' := by intro c v hv; exact isJet_smul hs hv c


lemma isJet_class {t : Set (Space n)} {v : JetAmbient α s} (hv : IsJet t v) :
    IsC2HolderUpToOn α (Rep v) s := by
  have hb {u : Space n → ℝ} (hh : IsHolderOn α u s) : IsBoundedOn u s := by
    obtain ⟨M,H,hM,hH,hb,hh⟩ := hh
    exact ⟨M,hM,hb⟩
  refine ⟨hv.1,hb (BallHolderSpace.representative_isHolderOn v.1),?_,?_⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := hb (BallHolderSpace.representative_isHolderOn (v.2.1 i))
    exact ⟨M,hM,fun x hx => by rw [hv.2.1 i hx]; exact hb x hx⟩
  · intro i j
    exact P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (BallHolderSpace.representative_isHolderOn (v.2.2 i j)) (hv.2.2.1 i j)

lemma supNorm_rep_le_norm (v : H α s) : supNormOn (BallHolderSpace.representative v) s ≤ ‖v‖ := by
  rw [← BallHolderSpace.fst_norm_eq_supNormOn v (fun x => (BallHolderSpace.representative_apply v x).symm)]
  exact norm_fst_le v.val

lemma holderNorm_rep_le_two_norm (v : H α s) :
    holderNormOn α (BallHolderSpace.representative v) s ≤ 2*‖v‖ :=
  BallHolderSpace.holderNormOn_le_two_norm v (fun x => (BallHolderSpace.representative_apply v x).symm)

lemma norm_le_holderNorm_rep (v : H α s) : ‖v‖ ≤ holderNormOn α (BallHolderSpace.representative v) s :=
  BallHolderSpace.norm_le_holderNormOn v (fun x => (BallHolderSpace.representative_apply v x).symm)

lemma jet_norm_bounds (v : JetAmbient α s) : ‖v.1‖ ≤ ‖v‖ ∧
    (∀ i, ‖v.2.1 i‖ ≤ ‖v‖) ∧ ∀ i j, ‖v.2.2 i j‖ ≤ ‖v‖ := by
  refine ⟨norm_fst_le v,?_,?_⟩
  · intro i
    exact (norm_le_pi_norm v.2.1 i).trans ((norm_fst_le v.2).trans (norm_snd_le v))
  · intro i j
    exact (norm_le_pi_norm (v.2.2 i) j).trans ((norm_le_pi_norm v.2.2 i).trans
      ((norm_snd_le v.2).trans (norm_snd_le v)))

lemma canonical_norm_le_jet_norm {t : Set (Space n)} {v : JetAmbient α s} (hv : IsJet t v) :
    c2HolderUpToNormOn α (Rep v) s ≤ (1+(n:ℝ)+2*(n:ℝ)^2)*‖v‖ := by
  have hn := jet_norm_bounds v
  rw [c2HolderUpToNormOn_eq_holder_sums]
  have h0 : supNormOn (Rep v) s ≤ ‖v‖ := (supNorm_rep_le_norm v.1).trans hn.1
  have h1 : (∑ i : Fin n, supNormOn (firstPartialWithin (Rep v) s i) s) ≤ (n:ℝ)*‖v‖ := by
    calc
      _ ≤ ∑ i : Fin n, ‖v‖ := Finset.sum_le_sum (fun i _ => by
        rw [supNormOn_congr (hv.2.1 i)]
        exact (supNorm_rep_le_norm (v.2.1 i)).trans (hn.2.1 i))
      _ = _ := by simp
  have h2 : (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (secondPartialWithin (Rep v) s i j) s) ≤
      2*(n:ℝ)^2*‖v‖ := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, 2*‖v‖ := Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => by
          rw [holderNormOn_congr (hv.2.2.1 i j)]
          exact (holderNorm_rep_le_two_norm (v.2.2 i j)).trans (by nlinarith [hn.2.2 i j])))
      _ = _ := by simp [pow_two]; ring
  nlinarith

lemma jet_norm_le_four_canonical_norm {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {v : JetAmbient α (closedBall z r)}
    {t : Set (Space n)} (hv : IsJet t v) :
    ‖v‖ ≤ 4*c2HolderUpToNormOn α (Rep v) (closedBall z r) := by
  let N := c2HolderUpToNormOn α (Rep v) (closedBall z r)
  have hN : 0 ≤ N := c2HolderUpToNormOn_nonneg _ _ _
  have hlow := lower_order_holderNormOn_le_four_c2HolderUpToNormOn hα hα1 z hr (isJet_class hv)
  change max ‖v.1‖ (max ‖v.2.1‖ ‖v.2.2‖) ≤ 4*N
  refine max_le ((norm_le_holderNorm_rep v.1).trans hlow.1) (max_le ?_ ?_)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    apply (norm_le_holderNorm_rep (v.2.1 i)).trans
    rw [← holderNormOn_congr (hv.2.1 i)]
    exact hlow.2 i
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    apply (norm_le_holderNorm_rep (v.2.2 i j)).trans
    rw [← holderNormOn_congr (hv.2.2.1 i j)]
    exact ((c2HolderUpToNormOn_components α (Rep v) (closedBall z r)).2.2.2.2 i j).trans (by change N ≤ 4*N; linarith)


lemma pointwise_jets_of_canonical_convergence (hs : UniqueDiffOn ℝ s)
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, IsC2HolderUpToOn α (u j) s) (hv : IsC2HolderUpToOn α v s)
    (hlim : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, c2HolderUpToNormOn α (u j-v) s < ε)
    {x : Space n} (hx : x ∈ s) :
    Tendsto (fun j => u j x) atTop (𝓝 (v x)) ∧
      (∀ i, Tendsto (fun j => firstPartialWithin (u j) s i x) atTop (𝓝 (firstPartialWithin v s i x))) ∧
      ∀ i k, Tendsto (fun j => secondPartialWithin (u j) s i k x) atTop (𝓝 (secondPartialWithin v s i k x)) := by
  have hN := tendsto_zero_of_nonneg_bound (fun j => c2HolderUpToNormOn_nonneg α (u j-v) s) hlim
  have hdiff (j : ℕ) := isC2HolderUpToOn_sub hs (hu j) hv
  refine ⟨?_,?_,?_⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => norm_le_c2HolderUpToNormOn (hdiff j) hx) hN
  · intro i
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hN
    change ‖(firstPartialWithin (u j) s i-firstPartialWithin v s i) x‖ ≤ _
    rw [← firstPartialWithin_sub hs ((hu j).1.of_le (by norm_num)) (hv.1.of_le (by norm_num)) i hx]
    exact (norm_le_supNormOn ((hdiff j).2.2.1 i) hx).trans ((c2HolderUpToNormOn_components α (u j-v) s).2.2.1 i)
  · intro i k
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hN
    change ‖(secondPartialWithin (u j) s i k-secondPartialWithin v s i k) x‖ ≤ _
    rw [← secondPartialWithin_sub hs (hu j).1 hv.1 i k hx]
    exact (norm_le_holderNormOn ((hdiff j).2.2.2 i k) hx).trans
      ((c2HolderUpToNormOn_components α (u j-v) s).2.2.2.2 i k)

lemma source_rep_tendsto {u : ℕ → H α s} {v : H α s} (hu : Tendsto u atTop (𝓝 v)) (x : s) :
    Tendsto (fun j => BallHolderSpace.representative (u j) x) atTop (𝓝 (BallHolderSpace.representative v x)) := by
  let L : H α s →L[ℝ] ℝ := (ContinuousMap.evalCLM ℝ x).comp (BallHolderSpace.valueCLM α)
  have hh := (L.continuous.tendsto v).comp hu
  change Tendsto (fun j => (u j).val.1 x) atTop (𝓝 (v.val.1 x)) at hh
  simpa only [BallHolderSpace.representative_apply] using hh

lemma jetSubmodule_closed_ball {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    IsClosed (jetSubmodule (α := α) (BallWithinLimit.uniqueDiffOn_closedBall z hr) (sphere z r) :
      Set (JetAmbient α (closedBall z r))) := by
  let s := closedBall z r
  let hs := BallWithinLimit.uniqueDiffOn_closedBall z hr
  apply IsSeqClosed.isClosed
  intro V v hV hv
  have hclass (j : ℕ) : IsC2HolderUpToOn α (Rep (V j)) s := isJet_class (hV j)
  have hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      c2HolderUpToNormOn α (Rep (V j)-Rep (V k)) s < ε := by
    intro ε hε
    let K := 1+(n:ℝ)+2*(n:ℝ)^2
    have hK : 0 < K := by dsimp [K]; positivity
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hv.cauchySeq (ε/K) (div_pos hε hK)
    refine ⟨N,fun j hj k hk => ?_⟩
    rw [← rep_sub]
    have hb := canonical_norm_le_jet_norm (isJet_sub hs (hV j) (hV k))
    have hsmall : ‖V j-V k‖ * K < ε := (lt_div_iff₀ hK).mp (by simpa only [dist_eq_norm] using hN j hj k hk)
    dsimp [K] at *
    nlinarith
  obtain ⟨u,hu,hlim⟩ := c2HolderUpToNormOn_complete hα hα1 z hr (fun j => Rep (V j)) hclass hCauchy
  have hrep : EqOn (Rep v) u s := by
    intro x hx
    have ha := source_rep_tendsto hv.fst_nhds (⟨x,hx⟩ : s)
    have hb := (pointwise_jets_of_canonical_convergence hs hclass hu hlim hx).1
    exact tendsto_nhds_unique ha hb
  have hfirstRep (i : Fin n) : EqOn (firstPartialWithin (Rep v) s i) (firstPartialWithin u s i) s := by
    intro x hx
    unfold firstPartialWithin
    rw [fderivWithin_congr' hrep hx]
  have hsecondRep (i j : Fin n) : EqOn (secondPartialWithin (Rep v) s i j) (secondPartialWithin u s i j) s := by
    intro x hx
    unfold secondPartialWithin
    rw [fderivWithin_congr' (hfirstRep j) hx]
  change IsJet (sphere z r) v
  refine ⟨hu.1.congr hrep,?_,?_,?_⟩
  · intro i x hx
    have ha := source_rep_tendsto (tendsto_pi_nhds.mp hv.snd_nhds.fst_nhds i) (⟨x,hx⟩ : s)
    have hb := (pointwise_jets_of_canonical_convergence hs hclass hu hlim hx).2.1 i
    have ha' : Tendsto (fun j => firstPartialWithin (Rep (V j)) s i x) atTop
        (𝓝 (BallHolderSpace.representative (v.2.1 i) x)) := by
      apply ha.congr'
      exact Eventually.of_forall (fun j => ((hV j).2.1 i hx).symm)
    exact (hfirstRep i hx).trans (tendsto_nhds_unique hb ha')
  · intro i k x hx
    have ha := source_rep_tendsto (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv.snd_nhds.snd_nhds i) k) (⟨x,hx⟩ : s)
    have hb := (pointwise_jets_of_canonical_convergence hs hclass hu hlim hx).2.2 i k
    have ha' : Tendsto (fun j => secondPartialWithin (Rep (V j)) s i k x) atTop
        (𝓝 (BallHolderSpace.representative (v.2.2 i k) x)) := by
      apply ha.congr'
      exact Eventually.of_forall (fun j => ((hV j).2.2.1 i k hx).symm)
    exact (hsecondRep i k hx).trans (tendsto_nhds_unique hb ha')
  · intro x hx
    have ha := source_rep_tendsto hv.fst_nhds (⟨x,sphere_subset_closedBall hx⟩ : s)
    have hb : Tendsto (fun j => Rep (V j) x) atTop (𝓝 0) := by
      have he : (fun j => Rep (V j) x) = (fun _ : ℕ => (0 : ℝ)) := funext (fun j => (hV j).2.2.2 x hx)
      rw [he]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique ha hb

abbrev BallSpace (α : ℝ) (z : Space n) (r : ℝ) (hr : 0 < r) :=
  jetSubmodule (α := α) (BallWithinLimit.uniqueDiffOn_closedBall z hr) (sphere z r)

instance ballSpace_complete {r : ℝ} (z : Space n) (hr : 0 < r)
    [hα : Fact (0 < α)] [hα1 : Fact (α ≤ 1)] : CompleteSpace (BallSpace α z r hr) :=
  (jetSubmodule_closed_ball z hr hα.out hα1.out).completeSpace_coe


lemma source_rep_ofHolder_apply (hα : 0 < α) {u : Space n → ℝ}
    (hu : IsHolderOn α u s) {x : Space n} (hx : x ∈ s) :
    BallHolderSpace.representative (BallHolderSpace.ofHolder hα hu) x = u x :=
  (BallHolderSpace.representative_apply (BallHolderSpace.ofHolder hα hu) (⟨x,hx⟩ : s)).trans
    (BallHolderSpace.ofHolder_apply hα hu (⟨x,hx⟩ : s))

noncomputable def ofFunction {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α ≤ 1) {u : Space n → ℝ}
    (hu : IsC2HolderUpToOn α u (closedBall z r))
    (hzero : ∀ x ∈ sphere z r, u x = 0) : BallSpace α z r hr := by
  let s := closedBall z r
  have hlow := lower_order_holder_jets_on_closedBall hα.le hα1 z hr hu
  let v : JetAmbient α s := (BallHolderSpace.ofHolder hα hlow.1,
    (fun i => BallHolderSpace.ofHolder hα (hlow.2 i)),
    (fun i j => BallHolderSpace.ofHolder hα (hu.2.2.2 i j)))
  have hrep : EqOn (Rep v) u s := by
    intro x hx
    change BallHolderSpace.representative (BallHolderSpace.ofHolder hα hlow.1) (⟨x,hx⟩ : s) = u (⟨x,hx⟩ : s)
    exact source_rep_ofHolder_apply hα hlow.1 hx
  have hfirst (i : Fin n) : EqOn (firstPartialWithin (Rep v) s i) (firstPartialWithin u s i) s := by
    intro x hx
    unfold firstPartialWithin
    rw [fderivWithin_congr' hrep hx]
  have hsecond (i j : Fin n) : EqOn (secondPartialWithin (Rep v) s i j) (secondPartialWithin u s i j) s := by
    intro x hx
    unfold secondPartialWithin
    rw [fderivWithin_congr' (hfirst j) hx]
  refine ⟨v,?_⟩
  change IsJet (sphere z r) v
  refine ⟨hu.1.congr hrep,?_,?_,?_⟩
  · intro i x hx
    rw [hfirst i hx]
    change firstPartialWithin u s i (⟨x,hx⟩ : s) =
      BallHolderSpace.representative (BallHolderSpace.ofHolder hα (hlow.2 i)) (⟨x,hx⟩ : s)
    exact (source_rep_ofHolder_apply hα (hlow.2 i) hx).symm
  · intro i j x hx
    rw [hsecond i j hx]
    change secondPartialWithin u s i j (⟨x,hx⟩ : s) =
      BallHolderSpace.representative (BallHolderSpace.ofHolder hα (hu.2.2.2 i j)) (⟨x,hx⟩ : s)
    exact (source_rep_ofHolder_apply hα (hu.2.2.2 i j) hx).symm
  · intro x hx
    rw [hrep (sphere_subset_closedBall hx),hzero x hx]

@[simp] lemma ofFunction_rep {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α ≤ 1) {u : Space n → ℝ}
    (hu : IsC2HolderUpToOn α u (closedBall z r))
    (hzero : ∀ x ∈ sphere z r, u x = 0) :
    EqOn (Rep (ofFunction z hr hα hα1 hu hzero).val) u (closedBall z r) := by
  intro x hx
  change BallHolderSpace.representative
    (BallHolderSpace.ofHolder hα (lower_order_holder_jets_on_closedBall hα.le hα1 z hr hu).1)
    (⟨x,hx⟩ : closedBall z r) = u (⟨x,hx⟩ : closedBall z r)
  exact source_rep_ofHolder_apply hα (lower_order_holder_jets_on_closedBall hα.le hα1 z hr hu).1 hx

lemma ballSpace_class {r : ℝ} {z : Space n} {hr : 0 < r} (v : BallSpace α z r hr) :
    IsC2HolderUpToOn α (Rep v.val) (closedBall z r) := isJet_class v.property

lemma ballSpace_zero_trace {r : ℝ} {z : Space n} {hr : 0 < r} (v : BallSpace α z r hr) :
    ∀ x ∈ sphere z r, Rep v.val x = 0 := v.property.2.2.2

end BallBanachX

namespace BallHolderSpace
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {α : ℝ} {s : Set (Space n)} [CompactSpace s]

/-- Multiplication by a fixed genuine scalar Hölder function on the source space. -/
noncomputable def multiplicationCLM (hα : 0 < α) {f : Space n → ℝ}
    (hf : IsHolderOn α f s) : HolderSpace α s →L[ℝ] HolderSpace α s :=
  LinearMap.mkContinuous
    { toFun := fun v => ofHolder hα (isHolderOn_mul hf (representative_isHolderOn v))
      map_add' := by
        intro v w
        apply ext
        intro x
        simp only [ofHolder_apply,representative_add,Pi.add_apply]
        change f x * (representative v x+representative w x) =
          f x*representative v x + f x*representative w x
        ring
      map_smul' := by
        intro c v
        apply ext
        intro x
        simp only [ofHolder_apply,representative_smul,Pi.smul_apply]
        change f x*(c*representative v x) = c*(f x*representative v x)
        ring }
    (2*holderNormOn α f s)
    (by
      intro v
      have hrep : ∀ x : s,
          (ofHolder hα (isHolderOn_mul hf (representative_isHolderOn v))).val.1 x =
            f x*representative v x := fun _ => rfl
      change ‖ofHolder hα (isHolderOn_mul hf (representative_isHolderOn v))‖ ≤ _
      apply (norm_le_holderNormOn (f := fun x => f x * representative v x) _ hrep).trans
      apply (holderNormOn_mul_le hf (representative_isHolderOn v)).trans
      have hh := holderNormOn_le_two_norm v (fun x => (representative_apply v x).symm)
      nlinarith [holderNormOn_nonneg α f s])

@[simp] lemma multiplicationCLM_apply (hα : 0 < α) {f : Space n → ℝ}
    (hf : IsHolderOn α f s) (v : HolderSpace α s) (x : s) :
    (multiplicationCLM hα hf v).val.1 x = f x * representative v x := rfl

lemma norm_multiplicationCLM_le (hα : 0 < α) {f : Space n → ℝ}
    (hf : IsHolderOn α f s) :
    ‖multiplicationCLM hα hf‖ ≤ 2*holderNormOn α f s := by
  apply LinearMap.mkContinuous_norm_le
  exact mul_nonneg (by norm_num) (holderNormOn_nonneg _ _ _)

end BallHolderSpace

namespace BallBanachX
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {α : ℝ} {s : Set (Space n)} [CompactSpace s]

noncomputable def valueProjection : JetAmbient α s →L[ℝ] H α s :=
  ContinuousLinearMap.fst ℝ _ _

noncomputable def firstProjection (i : Fin n) : JetAmbient α s →L[ℝ] H α s :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

noncomputable def secondProjection (i j : Fin n) : JetAmbient α s →L[ℝ] H α s :=
  (ContinuousLinearMap.proj j : (Fin n → H α s) →L[ℝ] H α s).comp
    ((ContinuousLinearMap.proj i : (Fin n → Fin n → H α s) →L[ℝ] (Fin n → H α s)).comp
      ((ContinuousLinearMap.snd ℝ (Fin n → H α s) (Fin n → Fin n → H α s)).comp
        (ContinuousLinearMap.snd ℝ (H α s) ((Fin n → H α s) × (Fin n → Fin n → H α s)))))

/-- The actual nondivergence expression as a bounded map on scalar jet fields. -/
noncomputable def jetOperatorCLM (hα : 0 < α)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c s) :
    JetAmbient α s →L[ℝ] H α s :=
  (∑ i : Fin n, ∑ j : Fin n,
    (BallHolderSpace.multiplicationCLM hα (hc.1 i j)).comp (secondProjection i j)) +
    (∑ i : Fin n,
      (BallHolderSpace.multiplicationCLM hα (hc.2.1 i)).comp (firstProjection i)) +
    (BallHolderSpace.multiplicationCLM hα hc.2.2).comp valueProjection

lemma jetOperatorCLM_apply (hα : 0 < α)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c s)
    (v : JetAmbient α s) (x : s) :
    (jetOperatorCLM hα hc v).val.1 x =
      (∑ i : Fin n, ∑ j : Fin n, a x i j * BallHolderSpace.representative (v.2.2 i j) x) +
      (∑ i : Fin n, b x i * BallHolderSpace.representative (v.2.1 i) x) + c x * Rep v x := by
  let L : H α s →L[ℝ] ℝ := (ContinuousMap.evalCLM ℝ x).comp (BallHolderSpace.valueCLM α)
  change L (jetOperatorCLM hα hc v) = _
  simp only [jetOperatorCLM,ContinuousLinearMap.add_apply,sum_apply,map_add,map_sum,
    ContinuousLinearMap.comp_apply]
  rfl

lemma jetOperatorCLM_eq_within (hα : 0 < α)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c s)
    {t : Set (Space n)} {v : JetAmbient α s} (hv : IsJet t v) {x : Space n} (hx : x ∈ s) :
    BallHolderSpace.representative (jetOperatorCLM hα hc v) x =
      nondivergenceWithinOperator a b c (Rep v) s x := by
  have he := jetOperatorCLM_apply hα hc v (⟨x,hx⟩ : s)
  rw [BallHolderSpace.representative_apply (jetOperatorCLM hα hc v) (⟨x,hx⟩ : s)]
  rw [he]
  simp only [nondivergenceWithinOperator,Subtype.coe_mk,
    ← hv.2.1 _ hx,← hv.2.2.1 _ _ hx]

/-- The differential operator on the actual zero-trace Banach space. -/
noncomputable def ballOperatorCLM {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 < α)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r)) :
    BallSpace α z r hr →L[ℝ] H α (closedBall z r) :=
  (jetOperatorCLM hα hc).comp (jetSubmodule
    (BallWithinLimit.uniqueDiffOn_closedBall z hr) (sphere z r)).subtypeL

lemma ballOperatorCLM_eq_within {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 < α)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (v : BallSpace α z r hr) {x : Space n} (hx : x ∈ closedBall z r) :
    BallHolderSpace.representative (ballOperatorCLM z hr hα hc v) x =
      nondivergenceWithinOperator a b c (Rep v.val) (closedBall z r) x :=
  jetOperatorCLM_eq_within hα hc v.property hx

lemma ballOperatorCLM_eq_classical {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 < α)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (v : BallSpace α z r hr) {x : Space n} (hx : x ∈ ball z r) :
    BallHolderSpace.representative (ballOperatorCLM z hr hα hc v) x =
      nondivergenceOperator a b c (Rep v.val) x := by
  rw [ballOperatorCLM_eq_within z hr hα hc v (ball_subset_closedBall hx)]
  apply nondivergenceWithinOperator_eq_of_mem_interior
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)

lemma ballOperatorCLM_norm_bound {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α ≤ 1)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (v : BallSpace α z r hr) :
    ‖ballOperatorCLM z hr hα hc v‖ ≤
      4*coefficientNormOn α a b c (closedBall z r) * (1+(n:ℝ)+2*(n:ℝ)^2) * ‖v‖ := by
  have hrep : ∀ x : closedBall z r,
      (ballOperatorCLM z hr hα hc v).val.1 x =
        nondivergenceWithinOperator a b c (Rep v.val) (closedBall z r) x := by
    intro x
    rw [← BallHolderSpace.representative_apply (ballOperatorCLM z hr hα hc v) x]
    exact ballOperatorCLM_eq_within z hr hα hc v x.property
  apply (BallHolderSpace.norm_le_holderNormOn _ hrep).trans
  apply (holderNormOn_nondivergenceWithinOperator_le hα.le hα1 z hr hc (ballSpace_class v)).trans
  have hK : 0 ≤ coefficientNormOn α a b c (closedBall z r) := by
    unfold coefficientNormOn
    exact add_nonneg (add_nonneg
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => holderNormOn_nonneg _ _ _)))
      (Finset.sum_nonneg (fun i _ => holderNormOn_nonneg _ _ _))) (holderNormOn_nonneg _ _ _)
  have hnorm := canonical_norm_le_jet_norm v.property
  change _ ≤ _*‖v.val‖
  nlinarith

end BallBanachX

lemma nondivergenceWithinOperator_path {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c u : Space n → ℝ) (s : Set (Space n)) (t : ℝ) (x : Space n) :
    nondivergenceWithinOperator (pathPrincipal a t) (fun y => t • b y) (fun y => t*c y) u s x =
      (1-t) * nondivergenceWithinOperator (fun _ => 1) (fun _ => 0) (fun _ => 0) u s x +
      t * nondivergenceWithinOperator a b c u s x := by
  simp only [nondivergenceWithinOperator, pathPrincipal, PiLp.smul_apply, smul_eq_mul,
    Matrix.one_apply, PiLp.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring

lemma identity_coefficientsHolderOn {n : ℕ} (α : ℝ) (s : Set (Space n)) :
    CoefficientsHolderOn α (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ))
      (fun _ => 0) (fun _ => 0) s := by
  refine ⟨?_, ?_, isHolderOn_const α 0 s⟩
  · intro i j
    simpa only [Matrix.one_apply] using isHolderOn_const α (if i = j then 1 else 0) s
  · intro i
    simpa only [PiLp.zero_apply] using isHolderOn_const α 0 s


lemma firstPartialWithin_zero_fun {n : ℕ} (s : Set (Space n)) (i : Fin n) :
    firstPartialWithin (fun _ => (0 : ℝ)) s i = fun _ => 0 := by
  funext x
  unfold P201Specs.Elliptic.ConstantSchauder.firstPartialWithin
  simp

lemma secondPartialWithin_zero_fun {n : ℕ} (s : Set (Space n)) (i j : Fin n) :
    secondPartialWithin (fun _ => (0 : ℝ)) s i j = fun _ => 0 := by
  funext x
  unfold P201Specs.Elliptic.ConstantSchauder.secondPartialWithin
  rw [firstPartialWithin_zero_fun]
  simp

lemma isC2HolderUpToOn_zero {n : ℕ} (α : ℝ) (s : Set (Space n)) :
    IsC2HolderUpToOn α (fun _ => 0) s := by
  refine ⟨contDiffOn_const, ⟨0,le_rfl,fun x hx => by simp⟩, ?_, ?_⟩
  · intro i
    exact ⟨0,le_rfl,fun x hx => by rw [firstPartialWithin_zero_fun]; simp⟩
  · intro i j
    rw [secondPartialWithin_zero_fun]
    exact isHolderOn_const α 0 s

lemma c2HolderUpToNormOn_zero {n : ℕ} (α : ℝ) (s : Set (Space n)) :
    c2HolderUpToNormOn α (fun _ => 0) s = 0 := by
  have hsup : supNormOn (fun _ : Space n => (0 : ℝ)) s = 0 := by
    apply le_antisymm
    · exact Real.sSup_le (by rintro t ⟨x,hx,rfl⟩; simp) le_rfl
    · exact supNormOn_nonneg _ _
  have hsemi : holderSeminormOn α (fun _ : Space n => (0 : ℝ)) s = 0 := by
    apply le_antisymm
    · apply Real.sSup_le _ le_rfl
      rintro t ⟨x,hx,y,hy,hxy,rfl⟩
      simp
    · exact holderSeminormOn_nonneg _ _ _
  simp only [c2HolderUpToNormOn_eq_holder_sums, firstPartialWithin_zero_fun,
    secondPartialWithin_zero_fun, holderNormOn_zero, hsup, Finset.sum_const_zero, add_zero]


namespace BallBanachX
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {α : ℝ}

lemma ballOperatorCLM_apply_within {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 < α)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (v : BallSpace α z r hr) (x : closedBall z r) :
    (ballOperatorCLM z hr hα hc v).val.1 x =
      nondivergenceWithinOperator a b c (Rep v.val) (closedBall z r) x := by
  rw [← BallHolderSpace.representative_apply (ballOperatorCLM z hr hα hc v) x]
  exact ballOperatorCLM_eq_within z hr hα hc v x.property

lemma ballOperatorCLM_path {r : ℝ} (z : Space n) (hr : 0 < r)
    (hα : 0 < α)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r)) (t : ℝ) :
    ballOperatorCLM z hr hα (path_coefficientsHolderOn hc t) =
      (1-t) • ballOperatorCLM z hr hα (identity_coefficientsHolderOn α (closedBall z r)) +
      t • ballOperatorCLM z hr hα hc := by
  apply ContinuousLinearMap.ext
  intro v
  apply BallHolderSpace.ext
  intro x
  change (ballOperatorCLM z hr hα (path_coefficientsHolderOn hc t) v).val.1 x =
    (1-t)*(ballOperatorCLM z hr hα (identity_coefficientsHolderOn α (closedBall z r)) v).val.1 x +
    t*(ballOperatorCLM z hr hα hc v).val.1 x
  simp only [ballOperatorCLM_apply_within]
  exact nondivergenceWithinOperator_path a b c (Rep v.val) (closedBall z r) t x

set_option maxHeartbeats 800000 in
/-- The uniform Schauder estimate in the actual Banach norms, on the actual
bounded operator path. The full global statement is an explicit premise. -/
lemma uniform_ballOperatorCLM_lower_bound
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r)
    (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ),
        UniformlyEllipticOn ell a (closedBall z r) →
        ∀ hc : CoefficientsHolderOn α a b c (closedBall z r),
        coefficientNormOn α a b c (closedBall z r) ≤ K →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : BallSpace α z r hr,
          ‖v‖ ≤ C * ‖((1-t) • ballOperatorCLM z hr hα
            (identity_coefficientsHolderOn α (closedBall z r)) +
            t • ballOperatorCLM z hr hα hc) v‖ := by
  obtain ⟨C,hC,hest⟩ := uniform_path_schauder_estimate hglobal hn α hα hα1 z hr ell K hell hK
  refine ⟨8*C,by positivity,?_⟩
  intro a b c he hc hnorm hczero t ht v
  rw [← ballOperatorCLM_path z hr hα hc t]
  let T := ballOperatorCLM z hr hα (path_coefficientsHolderOn hc t)
  let f := BallHolderSpace.representative (T v)
  have hf : IsHolderOn α f (closedBall z r) := BallHolderSpace.representative_isHolderOn (T v)
  have hu : IsLiftedBallSolution α (pathPrincipal a t) (fun x => t • b x)
      (fun x => t*c x) f 0 z r (Rep v.val) := by
    refine ⟨ballSpace_class v,?_,ballSpace_zero_trace v⟩
    intro x hx
    exact (ballOperatorCLM_eq_classical z hr hα (path_coefficientsHolderOn hc t) v hx).symm
  have hbound := hest a b c he hc hnorm hczero t ht f 0 hf (isC2HolderUpToOn_zero α _) (Rep v.val) hu
  have hzero : c2HolderUpToNormOn α (0 : Space n → ℝ) (closedBall z r) = 0 :=
    c2HolderUpToNormOn_zero α _
  rw [hzero,add_zero] at hbound
  have hv := jet_norm_le_four_canonical_norm z hr hα.le hα1.le v.property
  have hfbound := BallHolderSpace.holderNormOn_le_two_norm (T v)
    (fun x => (BallHolderSpace.representative_apply (T v) x).symm)
  change holderNormOn α f (closedBall z r) ≤ 2*‖T v‖ at hfbound
  change ‖v.val‖ ≤ 8*C*‖T v‖
  nlinarith

end BallBanachX

namespace BallOperatorBridges
open P201Specs P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201.Elliptic.BallSchauderSolvability

lemma nondivergenceWithinOperator_congr {n : ℕ} {s : Set (Space n)}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n) (c : Space n → ℝ)
    {u v : Space n → ℝ} (hEq : EqOn u v s) :
    EqOn (nondivergenceWithinOperator a b c u s) (nondivergenceWithinOperator a b c v s) s := by
  have hfirst (i : Fin n) : EqOn (firstPartialWithin u s i) (firstPartialWithin v s i) s := by
    intro x hx
    unfold firstPartialWithin
    rw [fderivWithin_congr' hEq hx]
  have hsecond (i j : Fin n) : EqOn (secondPartialWithin u s i j) (secondPartialWithin v s i j) s := by
    intro x hx
    unfold secondPartialWithin
    rw [fderivWithin_congr' (hfirst j) hx]
  intro x hx
  simp only [nondivergenceWithinOperator,hEq hx,hfirst _ hx,hsecond _ _ hx]

lemma holderSpace_eq_of_eqOn_ball {n : ℕ} {α r : ℝ} {z : Space n}
    (hα : 0 < α) (hr : 0 < r)
    {v w : BallHolderSpace.HolderSpace α (closedBall z r)}
    (hEq : EqOn (BallHolderSpace.representative v) (BallHolderSpace.representative w) (ball z r)) :
    v = w := by
  have hv : ContinuousOn (BallHolderSpace.representative v) (closedBall z r) :=
    continuousOn_of_isHolderOn hα (BallHolderSpace.representative_isHolderOn v)
  have hw : ContinuousOn (BallHolderSpace.representative w) (closedBall z r) :=
    continuousOn_of_isHolderOn hα (BallHolderSpace.representative_isHolderOn w)
  have hclosure : EqOn (BallHolderSpace.representative v) (BallHolderSpace.representative w) (closedBall z r) :=
    hEq.of_subset_closure hv hw ball_subset_closedBall (by rw [closure_ball z hr.ne'])
  apply BallHolderSpace.ext
  intro x
  exact (BallHolderSpace.representative_apply v x).symm.trans
    ((hclosure x.property).trans (BallHolderSpace.representative_apply w x))

end BallOperatorBridges

namespace BallBanachX
set_option backward.isDefEq.respectTransparency false

/-- Surjectivity of the actual interval Laplacian from the complete zero-trace
C²,α space to the actual Hölder source Banach space. -/
lemma laplacian_interval_operator_surjective {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r) :
    Function.Surjective (ballOperatorCLM z hr hα (identity_coefficientsHolderOn α (closedBall z r))) := by
  intro F
  let f := BallHolderSpace.representative F
  have hf : IsHolderOn α f (closedBall z r) := BallHolderSpace.representative_isHolderOn F
  obtain ⟨u,hu,hΔ,htrace⟩ := laplacian_interval_solution_upTo hα hα1 z hr hf 0
  have hzero : ∀ x ∈ sphere z r, u x = 0 := by
    intro x hx
    exact htrace (⟨x,hx⟩ : sphere z r)
  let v := ofFunction z hr hα hα1.le hu hzero
  refine ⟨v,?_⟩
  apply BallOperatorBridges.holderSpace_eq_of_eqOn_ball hα hr
  intro x hx
  have hxi : x ∈ interior (closedBall z r) := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  rw [ballOperatorCLM_eq_within z hr hα _ v (ball_subset_closedBall hx)]
  rw [BallOperatorBridges.nondivergenceWithinOperator_congr
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => 0) (fun _ => 0)
    (ofFunction_rep z hr hα hα1.le hu hzero) (ball_subset_closedBall hx)]
  rw [nondivergenceWithinOperator_eq_of_mem_interior _ _ _ _ hxi]
  have hid : (fun _ : Space 1 => (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
      (fun _ i j => if i = j then (1 : ℝ) else 0) := by
    funext y i j
    exact Matrix.one_apply
  rw [hid]
  exact (nondivergenceOperator_identity u x).trans (hΔ x (ball_subset_closedBall hx))

end BallBanachX

namespace BallSpaceBridges
open P201Specs P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201.Elliptic.BallSchauderSolvability BallBanachX

lemma scalar_source_ext {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {v w : BallHolderSpace.HolderSpace α s}
    (hEq : EqOn (BallHolderSpace.representative v) (BallHolderSpace.representative w) s) : v = w := by
  apply BallHolderSpace.ext
  intro x
  exact (BallHolderSpace.representative_apply v x).symm.trans
    ((hEq x.property).trans (BallHolderSpace.representative_apply w x))

lemma jetSubmodule_ext {n : ℕ} {α : ℝ} {s t : Set (Space n)} [CompactSpace s]
    {hs : UniqueDiffOn ℝ s} {v w : jetSubmodule (α := α) hs t}
    (hEq : EqOn (Rep v.val) (Rep w.val) s) : v = w := by
  have hfirst (i : Fin n) : EqOn (firstPartialWithin (Rep v.val) s i)
      (firstPartialWithin (Rep w.val) s i) s := by
    intro x hx
    unfold firstPartialWithin
    rw [fderivWithin_congr' hEq hx]
  have hsecond (i j : Fin n) : EqOn (secondPartialWithin (Rep v.val) s i j)
      (secondPartialWithin (Rep w.val) s i j) s := by
    intro x hx
    unfold secondPartialWithin
    rw [fderivWithin_congr' (hfirst j) hx]
  apply Subtype.ext
  apply Prod.ext
  · exact scalar_source_ext hEq
  · apply Prod.ext
    · funext i
      apply scalar_source_ext
      intro x hx
      exact (v.property.2.1 i hx).symm.trans ((hfirst i hx).trans (w.property.2.1 i hx))
    · funext i j
      apply scalar_source_ext
      intro x hx
      exact (v.property.2.2.1 i j hx).symm.trans ((hsecond i j hx).trans (w.property.2.2.1 i j hx))

lemma ballSpace_ext {n : ℕ} {α r : ℝ} {z : Space n} {hr : 0 < r}
    {v w : BallSpace α z r hr}
    (hEq : EqOn (Rep v.val) (Rep w.val) (closedBall z r)) : v = w :=
  jetSubmodule_ext hEq


lemma ballOperatorCLM_injective {n : ℕ} (hn : 1 ≤ n) {α r : ℝ} {z : Space n}
    (hr : 0 < r) (hα : 0 < α)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n} {c : Space n → ℝ}
    (he : ∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hnonpos : ∀ x ∈ closedBall z r, c x ≤ 0) :
    Function.Injective (ballOperatorCLM z hr hα hc) := by
  intro v w hEq
  apply ballSpace_ext
  let f := BallHolderSpace.representative (ballOperatorCLM z hr hα hc v)
  have hu : P201Specs.Elliptic.BallSchauderSolvability.IsLiftedBallSolution α a b c f (fun _ => 0) z r (Rep v.val) := by
    refine ⟨ballSpace_class v,?_,ballSpace_zero_trace v⟩
    intro x hx
    exact (ballOperatorCLM_eq_classical z hr hα hc v hx).symm
  have hw : P201Specs.Elliptic.BallSchauderSolvability.IsLiftedBallSolution α a b c f (fun _ => 0) z r (Rep w.val) := by
    refine ⟨ballSpace_class w,?_,ballSpace_zero_trace w⟩
    intro x hx
    change P201Specs.Elliptic.nondivergenceOperator a b c (Rep w.val) x =
      BallHolderSpace.representative (ballOperatorCLM z hr hα hc v) x
    rw [hEq]
    exact (ballOperatorCLM_eq_classical z hr hα hc w hx).symm
  exact lifted_ball_solution_unique hn hα hr he hc hnonpos hu hw

end BallSpaceBridges

namespace BallLiftAlgebra
set_option backward.isDefEq.respectTransparency false

lemma firstPartialWithin_add {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ 1 u s) (hv : ContDiffOn ℝ 1 v s)
    (i : Fin n) : EqOn (firstPartialWithin (u+v) s i)
      (firstPartialWithin u s i+firstPartialWithin v s i) s := by
  intro x hx
  unfold firstPartialWithin
  rw [fderivWithin_add (hs x hx) (hu.differentiableOn (by norm_num) x hx)
    (hv.differentiableOn (by norm_num) x hx)]
  rfl

lemma secondPartialWithin_add {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ 2 u s) (hv : ContDiffOn ℝ 2 v s)
    (i j : Fin n) : EqOn (secondPartialWithin (u+v) s i j)
      (secondPartialWithin u s i j+secondPartialWithin v s i j) s := by
  intro x hx
  have hD1u : ContDiffOn ℝ 1 (firstPartialWithin u s j) s :=
    (hu.fderivWithin (m := 1) hs (by norm_num)).clm_apply contDiffOn_const
  have hD1v : ContDiffOn ℝ 1 (firstPartialWithin v s j) s :=
    (hv.fderivWithin (m := 1) hs (by norm_num)).clm_apply contDiffOn_const
  unfold secondPartialWithin
  rw [fderivWithin_congr' (firstPartialWithin_add hs (hu.of_le (by norm_num))
      (hv.of_le (by norm_num)) j) hx,
    fderivWithin_add (hs x hx) (hD1u.differentiableOn (by norm_num) x hx)
      (hD1v.differentiableOn (by norm_num) x hx)]
  rfl

lemma isC2HolderUpToOn_add {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {α : ℝ} {u v : Space n → ℝ} (hu : IsC2HolderUpToOn α u s) (hv : IsC2HolderUpToOn α v s) :
    IsC2HolderUpToOn α (u+v) s := by
  have hb {f g : Space n → ℝ} (hf : IsBoundedOn f s) (hg : IsBoundedOn g s) :
      IsBoundedOn (f+g) s := by
    obtain ⟨M,hM,hf⟩ := hf
    obtain ⟨N,hN,hg⟩ := hg
    exact ⟨M+N,add_nonneg hM hN,fun x hx => (norm_add_le _ _).trans (add_le_add (hf x hx) (hg x hx))⟩
  refine ⟨hu.1.add hv.1,hb hu.2.1 hv.2.1,?_,?_⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := hb (hu.2.2.1 i) (hv.2.2.1 i)
    exact ⟨M,hM,fun x hx => by
      rw [firstPartialWithin_add hs (hu.1.of_le (by norm_num)) (hv.1.of_le (by norm_num)) i hx]
      exact hb x hx⟩
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_add (hu.2.2.2 i j) (hv.2.2.2 i j))
    exact secondPartialWithin_add hs hu.1 hv.1 i j

lemma nondivergenceWithinOperator_add {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n) (c : Space n → ℝ)
    {α : ℝ} {u v : Space n → ℝ} (hu : IsC2HolderUpToOn α u s) (hv : IsC2HolderUpToOn α v s) :
    EqOn (nondivergenceWithinOperator a b c (u+v) s)
      (nondivergenceWithinOperator a b c u s+nondivergenceWithinOperator a b c v s) s := by
  intro x hx
  have h1 (i : Fin n) := firstPartialWithin_add hs (hu.1.of_le (by norm_num)) (hv.1.of_le (by norm_num)) i hx
  have h2 (i j : Fin n) := secondPartialWithin_add hs hu.1 hv.1 i j hx
  simp only [nondivergenceWithinOperator, h1, h2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring


end BallLiftAlgebra

namespace BallBanachX
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000

/-- The concrete interval operator is bijective, using the proved Laplacian
start and the full global Schauder statement as an explicit premise. -/
lemma interval_operator_bijective
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r)
    {a : Space 1 → Matrix (Fin 1) (Fin 1) ℝ} {b : Space 1 → Space 1}
    {c : Space 1 → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0) :
    Function.Bijective (ballOperatorCLM z hr hα hc) := by
  letI : Fact (0 < α) := ⟨hα⟩
  letI : Fact (α ≤ 1) := ⟨hα1.le⟩
  let K := coefficientNormOn α a b c (closedBall z r)
  have hK : 0 ≤ K := by
    unfold K coefficientNormOn
    exact add_nonneg (add_nonneg
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => holderNormOn_nonneg _ _ _)))
      (Finset.sum_nonneg (fun i _ => holderNormOn_nonneg _ _ _))) (holderNormOn_nonneg _ _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_ballOperatorCLM_lower_bound hglobal (by omega) α hα hα1 z hr ell K hell hK
  let S := jetSubmodule (α := α) (BallWithinLimit.uniqueDiffOn_closedBall z hr) (sphere z r)
  let E := ↥S
  let F := H α (closedBall z r)
  letI eGroup : NormedAddCommGroup E := S.normedAddCommGroup
  letI eSpace : NormedSpace ℝ E := S.normedSpace
  letI eComplete : CompleteSpace E := ballSpace_complete z hr
  letI fGroup : NormedAddCommGroup F := (BallHolderSpace.graphSubmodule α (closedBall z r)).normedAddCommGroup
  letI fSpace : NormedSpace ℝ F := (BallHolderSpace.graphSubmodule α (closedBall z r)).normedSpace
  letI fComplete : CompleteSpace F := inferInstance
  let L0 : E →L[ℝ] F := ballOperatorCLM z hr hα (identity_coefficientsHolderOn α (closedBall z r))
  let L1 : E →L[ℝ] F := ballOperatorCLM z hr hα hc
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : E, ‖x‖ ≤ C*‖((1-t) • L0+t • L1) x‖ :=
    hbound a b c he hc le_rfl hczero
  have hs : Function.Surjective L0 := laplacian_interval_operator_surjective hα hα1 z hr
  exact @affine_method_of_continuity E F eGroup eSpace eComplete fGroup fSpace fComplete L0 L1 C hC.le hb hs

lemma interval_zero_trace_solvability
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r)
    {a : Space 1 → Matrix (Fin 1) (Fin 1) ℝ} {b : Space 1 → Space 1}
    {c : Space 1 → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0)
    {f : Space 1 → ℝ} (hf : IsHolderOn α f (closedBall z r)) :
    ∃ u : Space 1 → ℝ, IsLiftedBallSolution α a b c f 0 z r u ∧
      ∀ v : Space 1 → ℝ, IsLiftedBallSolution α a b c f 0 z r v →
        EqOn v u (closedBall z r) := by
  have hsurj := (interval_operator_bijective hglobal hα hα1 z hr hell he hc hczero).2
  obtain ⟨v,hv⟩ := hsurj (BallHolderSpace.ofHolder hα hf)
  have hu : IsLiftedBallSolution α a b c f 0 z r (Rep v.val) := by
    refine ⟨ballSpace_class v,?_,ballSpace_zero_trace v⟩
    intro x hx
    rw [← ballOperatorCLM_eq_classical z hr hα hc v hx,hv]
    exact source_rep_ofHolder_apply hα hf (ball_subset_closedBall hx)
  refine ⟨Rep v.val,hu,?_⟩
  intro w hw
  exact (lifted_ball_solution_unique (by omega) hα hr ⟨ell,hell,he⟩ hc hczero hu hw).symm

end BallBanachX

namespace BallInterval
set_option backward.isDefEq.respectTransparency false

lemma interval_lifted_ball_solvability
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r)
    {a : Space 1 → Matrix (Fin 1) (Fin 1) ℝ} {b : Space 1 → Space 1}
    {c : Space 1 → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0)
    {f G : Space 1 → ℝ} (hf : IsHolderOn α f (closedBall z r))
    (hG : IsC2HolderUpToOn α G (closedBall z r)) :
    ∃ u : Space 1 → ℝ, IsLiftedBallSolution α a b c f G z r u ∧
      ∀ v : Space 1 → ℝ, IsLiftedBallSolution α a b c f G z r v →
        EqOn v u (closedBall z r) := by
  let F := f - nondivergenceWithinOperator a b c G (closedBall z r)
  have hF : IsHolderOn α F (closedBall z r) := BallC2Complete.isHolderOn_sub hf
    (nondivergenceWithinOperator_holder_on_closedBall hα.le hα1.le z hr hc hG)
  obtain ⟨v,hv,hvuniq⟩ := BallBanachX.interval_zero_trace_solvability hglobal hα hα1 z hr hell he hc hczero hF
  have hu : IsLiftedBallSolution α a b c f G z r (v+G) := by
    refine ⟨BallLiftAlgebra.isC2HolderUpToOn_add (BallWithinLimit.uniqueDiffOn_closedBall z hr) hv.1 hG,?_,?_⟩
    · intro x hx
      have hxi : x ∈ interior (closedBall z r) := mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
      have hvEq : nondivergenceWithinOperator a b c v (closedBall z r) x = F x :=
        (nondivergenceWithinOperator_eq_of_mem_interior a b c v hxi).trans (hv.2.1 x hx)
      calc
        nondivergenceOperator a b c (v+G) x =
            nondivergenceWithinOperator a b c (v+G) (closedBall z r) x :=
          (nondivergenceWithinOperator_eq_of_mem_interior a b c (v+G) hxi).symm
        _ = nondivergenceWithinOperator a b c v (closedBall z r) x +
            nondivergenceWithinOperator a b c G (closedBall z r) x :=
          BallLiftAlgebra.nondivergenceWithinOperator_add (BallWithinLimit.uniqueDiffOn_closedBall z hr)
            a b c hv.1 hG (ball_subset_closedBall hx)
        _ = f x := by rw [hvEq]; change f x - _ + _ = f x; ring
    · intro x hx
      change v x+G x = G x
      rw [hv.2.2 x hx]
      simp
  refine ⟨v+G,hu,?_⟩
  intro w hw
  exact (lifted_ball_solution_unique (by omega) hα hr ⟨ell,hell,he⟩ hc hczero hu hw).symm

lemma interval_holder_solvability
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement) :
    ∀ α : ℝ, 0 < α → α < 1 →
      ∀ (z : Space 1) (r : ℝ), 0 < r →
        ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
          ∃ C : ℝ, 0 < C ∧
            ∀ (a : Space 1 → Matrix (Fin 1) (Fin 1) ℝ)
              (b : Space 1 → Space 1) (c : Space 1 → ℝ),
              UniformlyEllipticOn ell a (closedBall z r) →
              CoefficientsHolderOn α a b c (closedBall z r) →
              coefficientNormOn α a b c (closedBall z r) ≤ K →
              (∀ x ∈ closedBall z r, c x ≤ 0) →
              ∀ f G : Space 1 → ℝ,
                IsHolderOn α f (closedBall z r) →
                IsC2HolderUpToOn α G (closedBall z r) →
                ∃ u : Space 1 → ℝ,
                  IsLiftedBallSolution α a b c f G z r u ∧
                  c2HolderUpToNormOn α u (closedBall z r) ≤
                    C * (holderNormOn α f (closedBall z r) +
                      c2HolderUpToNormOn α G (closedBall z r)) ∧
                  ∀ v : Space 1 → ℝ, IsLiftedBallSolution α a b c f G z r v →
                    EqOn v u (closedBall z r) := by
  intro α hα hα1 z r hr ell K hell hK
  obtain ⟨C,hC,hest⟩ := lifted_ball_solution_schauder_estimate hglobal (by omega) α hα hα1 z hr ell K hell hK
  refine ⟨C,hC,?_⟩
  intro a b c he hc hnorm hczero f G hf hG
  obtain ⟨u,hu,huniq⟩ := interval_lifted_ball_solvability hglobal hα hα1 z hr hell he hc hczero hf hG
  exact ⟨u,hu,hest a b c he hc hnorm hczero f G hf hG u hu,huniq⟩


end BallInterval

namespace IntervalBoundaryLift
open P201Specs P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder
open P201.Elliptic.BallSchauderSolvability

lemma continuous_interval_boundary_lift (α : ℝ) (z : Space 1) {r : ℝ} (hr : 0 < r)
    (g : C(sphere z r,ℝ)) :
    ∃ G : Space 1 → ℝ, IsC2HolderUpToOn α G (closedBall z r) ∧
      ∀ ζ : sphere z r, G ζ = g ζ := by
  obtain ⟨G,hG,hLap,htrace⟩ := interval_harmonic_extension z hr g
  have hjet : multiPartial G ({0,0} : MultiIndex 1) = fun _ => 0 := by
    funext x
    simpa only [P201Specs.laplacian,Fin.sum_univ_one] using hLap x
  have hglobal : IsC2HolderLoc α G := by
    refine ⟨hG,?_⟩
    intro s hs i j
    fin_cases i
    fin_cases j
    change IsHolderOn α (multiPartial G ({0,0} : MultiIndex 1)) s
    rw [hjet]
    exact isHolderOn_const α 0 s
  exact ⟨G,isC2HolderUpToOn_closedBall_of_isC2HolderLoc hglobal z hr,htrace⟩

end IntervalBoundaryLift

namespace BallInterval
set_option backward.isDefEq.respectTransparency false

lemma interval_continuous_data_upTo
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r)
    {a : Space 1 → Matrix (Fin 1) (Fin 1) ℝ} {b : Space 1 → Space 1}
    {c : Space 1 → ℝ}
    (he : ∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0)
    {f : Space 1 → ℝ} (hf : IsHolderOn α f (closedBall z r))
    (g : C(sphere z r,ℝ)) :
    ∃ u : Space 1 → ℝ, IsBallSolution a b c f z r g u ∧
      IsC2HolderUpToOn α u (closedBall z r) ∧
      ∀ v : Space 1 → ℝ, IsBallSolution a b c f z r g v →
        EqOn v u (closedBall z r) := by
  obtain ⟨ell,hell,he'⟩ := he
  obtain ⟨G,hG,htrace⟩ := IntervalBoundaryLift.continuous_interval_boundary_lift α z hr g
  obtain ⟨u,hu,huniq⟩ := interval_lifted_ball_solvability hglobal hα hα1 z hr hell he' hc hczero hf hG
  have hsol : IsBallSolution a b c f z r g u := by
    refine ⟨hu.1.1.mono ball_subset_closedBall,hu.1.1.continuousOn,hu.2.1,?_⟩
    intro ζ
    exact (hu.2.2 ζ ζ.property).trans (htrace ζ)
  exact ⟨u,hsol,hu.1,fun v hv =>
    ball_solution_unique_of_holder (by omega) hα hr ⟨ell,hell,he'⟩ hc hczero hv hsol⟩

lemma interval_continuous_solvability
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r)
    {a : Space 1 → Matrix (Fin 1) (Fin 1) ℝ} {b : Space 1 → Space 1}
    {c : Space 1 → ℝ}
    (he : ∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0)
    {f : Space 1 → ℝ} (hf : IsHolderOn α f (closedBall z r))
    (g : C(sphere z r,ℝ)) :
    ∃ u : Space 1 → ℝ, IsBallSolution a b c f z r g u ∧
      IsC2HolderLocOn α u (ballDomain z r) ∧
      ∀ v : Space 1 → ℝ, IsBallSolution a b c f z r g v →
        EqOn v u (closedBall z r) := by
  obtain ⟨u,hu,hupTo,huniq⟩ := interval_continuous_data_upTo hglobal hα hα1 z hr he hc hczero hf g
  exact ⟨u,hu,isC2HolderLocOn_ball_of_upTo hupTo,huniq⟩

lemma interval_solution_upTo_of_continuous
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r)
    {a : Space 1 → Matrix (Fin 1) (Fin 1) ℝ} {b : Space 1 → Space 1}
    {c : Space 1 → ℝ}
    (he : ∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0)
    {f : Space 1 → ℝ} (hf : IsHolderOn α f (closedBall z r))
    {g : C(sphere z r,ℝ)} {u : Space 1 → ℝ}
    (hu : IsBallSolution a b c f z r g u) :
    IsC2HolderUpToOn α u (closedBall z r) := by
  obtain ⟨v,hv,hvp,huniq⟩ := interval_continuous_data_upTo hglobal hα hα1 z hr he hc hczero hf g
  exact isC2HolderUpToOn_congr hvp (huniq u hu)

end BallInterval

namespace UpToIntersection
open P201Specs P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder

lemma firstPartialWithin_inter_open {n : ℕ} (u : Space n → ℝ) (s : Set (Space n))
    {t : Set (Space n)} (ht : IsOpen t) {x : Space n} (hx : x ∈ t) (i : Fin n) :
    firstPartialWithin u (s ∩ t) i x = firstPartialWithin u s i x := by
  unfold firstPartialWithin
  rw [fderivWithin_inter (ht.mem_nhds hx)]

lemma secondPartialWithin_inter_open {n : ℕ} (u : Space n → ℝ) (s : Set (Space n))
    {t : Set (Space n)} (ht : IsOpen t) {x : Space n} (hx : x ∈ t) (i j : Fin n) :
    secondPartialWithin u (s ∩ t) i j x = secondPartialWithin u s i j x := by
  have hEq : firstPartialWithin u (s ∩ t) j =ᶠ[𝓝 x] firstPartialWithin u s j := by
    filter_upwards [ht.mem_nhds hx] with y hy
    exact firstPartialWithin_inter_open u s ht hy j
  unfold secondPartialWithin
  rw [hEq.fderivWithin_eq_of_nhds, fderivWithin_inter (ht.mem_nhds hx)]

lemma isC2HolderUpToOn_inter_open {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s t : Set (Space n)} (hu : IsC2HolderUpToOn α u s) (ht : IsOpen t) :
    IsC2HolderUpToOn α u (s ∩ t) := by
  refine ⟨hu.1.mono inter_subset_left,?_,?_,?_⟩
  · obtain ⟨M,hM,hb⟩ := hu.2.1
    exact ⟨M,hM,fun x hx => hb x hx.1⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := hu.2.2.1 i
    refine ⟨M,hM,fun x hx => ?_⟩
    rw [firstPartialWithin_inter_open u s ht hx.2 i]
    exact hb x hx.1
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono (hu.2.2.2 i j) inter_subset_left)
    intro x hx
    exact secondPartialWithin_inter_open u s ht hx.2 i j

end UpToIntersection

namespace BallInterval

lemma interval_boundary_regularity
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space 1) {r : ℝ} (hr : 0 < r)
    {a : Space 1 → Matrix (Fin 1) (Fin 1) ℝ} {b : Space 1 → Space 1}
    {c : Space 1 → ℝ}
    (he : ∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0)
    {f : Space 1 → ℝ} (hf : IsHolderOn α f (closedBall z r))
    {g : C(sphere z r,ℝ)} {u : Space 1 → ℝ}
    (hu : IsBallSolution a b c f z r g u) (V : Domain 1) :
    IsC2HolderUpToOn α u (closedBall z r ∩ (V : Set (Space 1))) :=
  UpToIntersection.isC2HolderUpToOn_inter_open
    (interval_solution_upTo_of_continuous hglobal hα hα1 z hr he hc hczero hf hu) V.isOpen

end BallInterval



namespace BallBanachX
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
/-- Constructive surjectivity bridge: actual zero-boundary solutions give
surjectivity in the concrete Hölder Banach spaces. -/
lemma ball_operator_surjective_of_zero_trace_solutions
    {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hsolve : ∀ f : Space n → ℝ, IsHolderOn α f (closedBall z r) →
      ∃ u : Space n → ℝ, IsLiftedBallSolution α a b c f 0 z r u) :
    Function.Surjective (ballOperatorCLM z hr hα hc) := by
  intro F
  let f := BallHolderSpace.representative F
  have hf : IsHolderOn α f (closedBall z r) := BallHolderSpace.representative_isHolderOn F
  obtain ⟨u,hu⟩ := hsolve f hf
  let v := ofFunction z hr hα hα1.le hu.1 hu.2.2
  refine ⟨v,?_⟩
  apply BallOperatorBridges.holderSpace_eq_of_eqOn_ball hα hr
  intro x hx
  have hxi : x ∈ interior (closedBall z r) := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  rw [ballOperatorCLM_eq_within z hr hα hc v (ball_subset_closedBall hx)]
  rw [BallOperatorBridges.nondivergenceWithinOperator_congr a b c
    (ofFunction_rep z hr hα hα1.le hu.1 hu.2.2) (ball_subset_closedBall hx)]
  rw [nondivergenceWithinOperator_eq_of_mem_interior a b c u hxi]
  exact hu.2.1 x hx

lemma ball_operator_bijective_of_laplacian_surjective
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r)
    (hstart : Function.Surjective (BallBanachX.ballOperatorCLM z hr hα
      (identity_coefficientsHolderOn α (closedBall z r))))
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0) :
    Function.Bijective (ballOperatorCLM z hr hα hc) := by
  letI : Fact (0 < α) := ⟨hα⟩
  letI : Fact (α ≤ 1) := ⟨hα1.le⟩
  let K := coefficientNormOn α a b c (closedBall z r)
  have hK : 0 ≤ K := by
    unfold K coefficientNormOn
    exact add_nonneg (add_nonneg
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => holderNormOn_nonneg _ _ _)))
      (Finset.sum_nonneg (fun i _ => holderNormOn_nonneg _ _ _))) (holderNormOn_nonneg _ _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_ballOperatorCLM_lower_bound hglobal hn α hα hα1 z hr ell K hell hK
  let S := jetSubmodule (α := α) (BallWithinLimit.uniqueDiffOn_closedBall z hr) (sphere z r)
  let E := ↥S
  let F := H α (closedBall z r)
  letI eGroup : NormedAddCommGroup E := S.normedAddCommGroup
  letI eSpace : NormedSpace ℝ E := S.normedSpace
  letI eComplete : CompleteSpace E := ballSpace_complete z hr
  letI fGroup : NormedAddCommGroup F := (BallHolderSpace.graphSubmodule α (closedBall z r)).normedAddCommGroup
  letI fSpace : NormedSpace ℝ F := (BallHolderSpace.graphSubmodule α (closedBall z r)).normedSpace
  letI fComplete : CompleteSpace F := inferInstance
  let L0 : E →L[ℝ] F := ballOperatorCLM z hr hα (identity_coefficientsHolderOn α (closedBall z r))
  let L1 : E →L[ℝ] F := ballOperatorCLM z hr hα hc
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : E, ‖x‖ ≤ C*‖((1-t) • L0+t • L1) x‖ :=
    hbound a b c he hc le_rfl hczero
  exact @affine_method_of_continuity E F eGroup eSpace eComplete fGroup fSpace fComplete L0 L1 C hC.le hb hstart

lemma ball_zero_trace_solvability_of_laplacian_surjective
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r)
    (hstart : Function.Surjective (BallBanachX.ballOperatorCLM z hr hα
      (identity_coefficientsHolderOn α (closedBall z r))))
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0)
    {f : Space n → ℝ} (hf : IsHolderOn α f (closedBall z r)) :
    ∃ u : Space n → ℝ, IsLiftedBallSolution α a b c f 0 z r u ∧
      ∀ v : Space n → ℝ, IsLiftedBallSolution α a b c f 0 z r v →
        EqOn v u (closedBall z r) := by
  have hsurj := (ball_operator_bijective_of_laplacian_surjective hglobal hn hα hα1 z hr hstart hell he hc hczero).2
  obtain ⟨v,hv⟩ := hsurj (BallHolderSpace.ofHolder hα hf)
  have hu : IsLiftedBallSolution α a b c f 0 z r (Rep v.val) := by
    refine ⟨ballSpace_class v,?_,ballSpace_zero_trace v⟩
    intro x hx
    rw [← ballOperatorCLM_eq_classical z hr hα hc v hx,hv]
    exact source_rep_ofHolder_apply hα hf (ball_subset_closedBall hx)
  refine ⟨Rep v.val,hu,?_⟩
  intro w hw
  exact (lifted_ball_solution_unique hn hα hr ⟨ell,hell,he⟩ hc hczero hu hw).symm

end BallBanachX

namespace BallContinuity
set_option backward.isDefEq.respectTransparency false

lemma lifted_ball_solvability_of_laplacian_surjective
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r)
    (hstart : Function.Surjective (BallBanachX.ballOperatorCLM z hr hα
      (identity_coefficientsHolderOn α (closedBall z r))))
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hczero : ∀ x ∈ closedBall z r, c x ≤ 0)
    {f G : Space n → ℝ} (hf : IsHolderOn α f (closedBall z r))
    (hG : IsC2HolderUpToOn α G (closedBall z r)) :
    ∃ u : Space n → ℝ, IsLiftedBallSolution α a b c f G z r u ∧
      ∀ v : Space n → ℝ, IsLiftedBallSolution α a b c f G z r v →
        EqOn v u (closedBall z r) := by
  let F := f - nondivergenceWithinOperator a b c G (closedBall z r)
  have hF : IsHolderOn α F (closedBall z r) := BallC2Complete.isHolderOn_sub hf
    (nondivergenceWithinOperator_holder_on_closedBall hα.le hα1.le z hr hc hG)
  obtain ⟨v,hv,hvuniq⟩ := BallBanachX.ball_zero_trace_solvability_of_laplacian_surjective hglobal hn hα hα1 z hr hstart hell he hc hczero hF
  have hu : IsLiftedBallSolution α a b c f G z r (v+G) := by
    refine ⟨BallLiftAlgebra.isC2HolderUpToOn_add (BallWithinLimit.uniqueDiffOn_closedBall z hr) hv.1 hG,?_,?_⟩
    · intro x hx
      have hxi : x ∈ interior (closedBall z r) := mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
      have hvEq : nondivergenceWithinOperator a b c v (closedBall z r) x = F x :=
        (nondivergenceWithinOperator_eq_of_mem_interior a b c v hxi).trans (hv.2.1 x hx)
      calc
        nondivergenceOperator a b c (v+G) x =
            nondivergenceWithinOperator a b c (v+G) (closedBall z r) x :=
          (nondivergenceWithinOperator_eq_of_mem_interior a b c (v+G) hxi).symm
        _ = nondivergenceWithinOperator a b c v (closedBall z r) x +
            nondivergenceWithinOperator a b c G (closedBall z r) x :=
          BallLiftAlgebra.nondivergenceWithinOperator_add (BallWithinLimit.uniqueDiffOn_closedBall z hr)
            a b c hv.1 hG (ball_subset_closedBall hx)
        _ = f x := by rw [hvEq]; change f x - _ + _ = f x; ring
    · intro x hx
      change v x+G x = G x
      rw [hv.2.2 x hx]
      simp
  refine ⟨v+G,hu,?_⟩
  intro w hw
  exact (lifted_ball_solution_unique hn hα hr ⟨ell,hell,he⟩ hc hczero hu hw).symm

lemma holder_solvability_of_laplacian_surjective
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    (hstart : ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, ∀ hα : 0 < α, α < 1 →
      ∀ (z : Space n) (r : ℝ) (hr : 0 < r),
        Function.Surjective (BallBanachX.ballOperatorCLM z hr hα
          (identity_coefficientsHolderOn α (closedBall z r)))) :
    HolderSolvabilityStatement := by
  intro n hn α hα hα1 z r hr ell K hell hK
  obtain ⟨C,hC,hest⟩ := lifted_ball_solution_schauder_estimate hglobal hn α hα hα1 z hr ell K hell hK
  refine ⟨C,hC,?_⟩
  intro a b c he hc hnorm hczero f G hf hG
  obtain ⟨u,hu,huniq⟩ := lifted_ball_solvability_of_laplacian_surjective hglobal hn hα hα1 z hr
    (hstart hn α hα hα1 z r hr) hell he hc hczero hf hG
  exact ⟨u,hu,hest a b c he hc hnorm hczero f G hf hG u hu,huniq⟩

end BallContinuity


namespace BallBanachX
set_option backward.isDefEq.respectTransparency true
/-- General-dimensional Laplacian start from actual zero-trace up-to-boundary
solutions. This statement does not assert that its explicit premise is proved. -/
lemma laplacian_operator_surjective_of_upTo_solutions
    {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r)
    (hsolve : ∀ f : Space n → ℝ, IsHolderOn α f (closedBall z r) →
      ∃ u : Space n → ℝ, IsC2HolderUpToOn α u (closedBall z r) ∧
        (∀ x ∈ ball z r, P201Specs.laplacian u x = f x) ∧
        ∀ x ∈ sphere z r, u x = 0) :
    Function.Surjective (ballOperatorCLM z hr hα
      (identity_coefficientsHolderOn α (closedBall z r))) := by
  apply ball_operator_surjective_of_zero_trace_solutions hα hα1 z hr
  intro f hf
  obtain ⟨u,hu,hΔ,hzero⟩ := hsolve f hf
  refine ⟨u,hu,?_,hzero⟩
  intro x hx
  have hid : (fun _ : Space n => (1 : Matrix (Fin n) (Fin n) ℝ)) =
      (fun _ i j => if i = j then (1 : ℝ) else 0) := by
    funext y i j
    exact Matrix.one_apply
  rw [hid]
  exact (nondivergenceOperator_identity u x).trans (hΔ x hx)

/-- The already proved classical continuous-data construction supplies every
zero-boundary Laplacian solution needed for the start. The only explicit extra
hypothesis here is its genuine up-to-boundary regularity. -/
lemma laplacian_operator_surjective_of_upTo_regularity
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r)
    (hregular : ∀ f : Space n → ℝ, IsHolderOn α f (closedBall z r) →
      ∀ u : Space n → ℝ,
        IsBallSolution (fun _ i j => if i = j then 1 else 0)
          (fun _ => 0) (fun _ => 0) f z r 0 u →
        IsC2HolderLocOn α u (ballDomain z r) →
        IsC2HolderUpToOn α u (closedBall z r)) :
    Function.Surjective (ballOperatorCLM z hr hα
      (identity_coefficientsHolderOn α (closedBall z r))) := by
  apply laplacian_operator_surjective_of_upTo_solutions hα hα1 z hr
  intro f hf
  obtain ⟨u,hu,hloc,huniq⟩ := laplacian_ball_continuous_solvability hn hα hα1 z hr hf 0
  refine ⟨u,hregular f hf u hu hloc,?_,?_⟩
  · intro x hx
    exact (nondivergenceOperator_identity u x).symm.trans (hu.2.2.1 x hx)
  · intro x hx
    exact hu.2.2.2 (⟨x,hx⟩ : sphere z r)

end BallBanachX


namespace BallContinuousLimit

lemma coefficientsHolderLoc_of_closedBall {n : ℕ} {α : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {z : Space n} {r : ℝ}
    (hc : CoefficientsHolderOn α a b c (closedBall z r)) :
    CoefficientsHolderLoc α a b c (ballDomain z r) :=
  ⟨fun i j => isHolderLoc_on_ball (hc.1 i j),
    fun i => isHolderLoc_on_ball (hc.2.1 i), isHolderLoc_on_ball hc.2.2⟩

lemma coefficientNormOn_mono {n : ℕ} {α : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s t : Set (Space n)}
    (hc : CoefficientsHolderOn α a b c t) (hst : s ⊆ t) :
    coefficientNormOn α a b c s ≤ coefficientNormOn α a b c t :=
  add_le_add (add_le_add
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      P201.Elliptic.PoissonSchauder.holderNormOn_mono (hc.1 i j) hst)
    (Finset.sum_le_sum fun i _ =>
      P201.Elliptic.PoissonSchauder.holderNormOn_mono (hc.2.1 i) hst))
    (P201.Elliptic.PoissonSchauder.holderNormOn_mono hc.2.2 hst)

lemma c2HolderLocOn_sub {n : ℕ} {α : ℝ} {Ω : Domain n}
    {u v : Space n → ℝ} (hu : IsC2HolderLocOn α u Ω)
    (hv : IsC2HolderLocOn α v Ω) : IsC2HolderLocOn α (u-v) Ω := by
  refine ⟨hu.1.sub hv.1, ?_⟩
  intro x hx
  obtain ⟨r,hr,hrs,hur⟩ := hu.2 x hx
  obtain ⟨t,ht,hts,hvt⟩ := hv.2 x hx
  have hs : ball x (min r t) ⊆ (Ω : Set (Space n)) :=
    (ball_subset_ball (min_le_left r t)).trans hrs
  refine ⟨min r t, lt_min hr ht, hs, ?_⟩
  intro i j
  have huH := P201.Elliptic.PoissonSchauder.isHolderOn_mono (hur i j)
    (ball_subset_ball (min_le_left r t))
  have hvH := P201.Elliptic.PoissonSchauder.isHolderOn_mono (hvt i j)
    (ball_subset_ball (min_le_right r t))
  apply P201.Elliptic.PoissonSchauder.isHolderOn_congr (BallC2Complete.isHolderOn_sub huH hvH)
  intro y hy
  exact partialWord_sub_on Ω hu.1 hv.1 (({i,j} : MultiIndex n).sort (· ≤ ·)) (by simp) (hs hy)

/-- Interior Schauder estimates turn uniform boundary Cauchy control into
Cauchy control of the actual interior C²,α norm. -/
lemma interior_control_of_lifted_sequence
    (hinterior : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f : Space n → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hcz : ∀ x ∈ closedBall z r, c x ≤ 0)
    {g : ℕ → C(sphere z r,ℝ)} {u : ℕ → Space n → ℝ}
    (hu : ∀ j, IsBallSolution a b c f z r (g j) (u j))
    (hureg : ∀ j, IsC2HolderLocOn α (u j) (ballDomain z r))
    (V : Domain n) (hVb : Bornology.IsBounded (V : Set (Space n)))
    (hV : closure (V : Set (Space n)) ⊆ ball z r) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℕ,
      IsC2HolderOn α (u p-u q) V ∧
      c2HolderNormOn α (u p-u q) V ≤ C * ‖g p-g q‖ := by
  let Ω := ballDomain z r
  have hcΩ : CoefficientsHolderOn α a b c Ω :=
    ⟨fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hc.1 i j) ball_subset_closedBall,
      fun i => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hc.2.1 i) ball_subset_closedBall,
      P201.Elliptic.PoissonSchauder.isHolderOn_mono hc.2.2 ball_subset_closedBall⟩
  let K := coefficientNormOn α a b c (closedBall z r)
  have hK : 0 ≤ K := by
    exact add_nonneg (add_nonneg
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => holderNormOn_nonneg _ _ _)
      (Finset.sum_nonneg fun i _ => holderNormOn_nonneg _ _ _)) (holderNormOn_nonneg _ _ _)
  obtain ⟨C,hC,hest⟩ := hinterior hn α hα hα1 Ω V Ω hVb hV le_rfl ell K hell hK
  refine ⟨C,hC,?_⟩
  intro p q
  have hb : ∀ x ∈ ball z r, ‖(u p-u q) x‖ ≤ ‖g p-g q‖ := by
    intro x hx
    exact ball_solution_boundary_stability hn hr
      (ellipticCoefficients_of_holder hα hell ball_subset_closedBall he hc)
      (fun y hy => hcz y (ball_subset_closedBall hy)) (hu p) (hu q) x (ball_subset_closedBall hx)
  have hf0 : IsHolderOn α (fun _ : Space n => (0:ℝ)) Ω := isHolderOn_const α 0 (Ω : Set (Space n))
  have hL : ∀ x ∈ Ω, nondivergenceOperator a b c (u p-u q) x = 0 := by
    intro x hx
    have hd := P201.Elliptic.nondivergenceOperator_mul_sub a b c
      (Ω := Ω) (hu p).1 (hu q).1 1 hx
    simpa only [Pi.sub_def, one_mul, (hu p).2.2.1 x hx, (hu q).2.2.1 x hx, sub_self] using hd
  obtain ⟨hclass,hbound⟩ := hest a b c
    ⟨fun x hx => he.1 x (ball_subset_closedBall hx),
      fun x hx => he.2 x (ball_subset_closedBall hx)⟩
    (coefficientsHolderLoc_of_closedBall hc) hcΩ (coefficientNormOn_mono hc ball_subset_closedBall)
    (u p-u q) (fun _ => 0) (c2HolderLocOn_sub (hureg p) (hureg q))
    (P201.Elliptic.PoissonSchauder.isHolderLoc_of_isHolderOn hf0) hL
    ⟨‖g p-g q‖,norm_nonneg _,hb⟩ hf0
  refine ⟨hclass, hbound.trans ?_⟩
  rw [holderNormOn_zero,add_zero]
  exact mul_le_mul_of_nonneg_left
    (P201.Elliptic.NewtonHessian.supNormOn_le (norm_nonneg _) hb) hC.le


/-- Uniform bounds and Cauchy convergence of sphere data control all interior
jets. The approximants are genuine locally Hölder classical solutions. -/
lemma local_interior_control
    (hinterior : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f : Space n → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hcz : ∀ x ∈ closedBall z r, c x ≤ 0)
    (hf : IsHolderOn α f (closedBall z r))
    {g : ℕ → C(sphere z r,ℝ)} (hg : CauchySeq g)
    {u : ℕ → Space n → ℝ}
    (hu : ∀ j, IsBallSolution a b c f z r (g j) (u j))
    (hureg : ∀ j, IsC2HolderLocOn α (u j) (ballDomain z r))
    {A : ℝ} (hA : 0 ≤ A) (hAb : ∀ j, ∀ x ∈ ball z r, ‖u j x‖ ≤ A)
    (V : Domain n) (hVb : Bornology.IsBounded (V : Set (Space n)))
    (hV : closure (V : Set (Space n)) ⊆ ball z r) :
    UniformCauchySeqOn (fun j => fderiv ℝ (u j)) atTop V ∧
    UniformCauchySeqOn (fun j => fderiv ℝ (fderiv ℝ (u j))) atTop V ∧
    ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧
      (∀ k i j, ∀ y ∈ V, ‖multiPartial (u k) {i,j} y‖ ≤ M) ∧
      (∀ k i j, ∀ y ∈ V, ∀ y' ∈ V,
        ‖multiPartial (u k) {i,j} y - multiPartial (u k) {i,j} y'‖ ≤ H * dist y y' ^ α) := by
  let Ω := ballDomain z r
  have hcΩ : CoefficientsHolderOn α a b c Ω :=
    ⟨fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hc.1 i j) ball_subset_closedBall,
      fun i => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hc.2.1 i) ball_subset_closedBall,
      P201.Elliptic.PoissonSchauder.isHolderOn_mono hc.2.2 ball_subset_closedBall⟩
  have heΩ : UniformlyEllipticOn ell a Ω :=
    ⟨fun x hx => he.1 x (ball_subset_closedBall hx),
      fun x hx => he.2 x (ball_subset_closedBall hx)⟩
  let K := coefficientNormOn α a b c (closedBall z r)
  have hK : 0 ≤ K := by
    exact add_nonneg (add_nonneg
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => holderNormOn_nonneg _ _ _)
      (Finset.sum_nonneg fun i _ => holderNormOn_nonneg _ _ _)) (holderNormOn_nonneg _ _ _)
  have hfΩ := P201.Elliptic.PoissonSchauder.isHolderOn_mono hf ball_subset_closedBall
  obtain ⟨C,hC,hest⟩ := hinterior hn α hα hα1 Ω V Ω hVb hV le_rfl ell K hell hK
  have hnorm (j : ℕ) : IsC2HolderOn α (u j) V ∧
      c2HolderNormOn α (u j) V ≤ C*(A+holderNormOn α f Ω) := by
    obtain ⟨hj,hbound⟩ := hest a b c heΩ (coefficientsHolderLoc_of_closedBall hc) hcΩ
      (coefficientNormOn_mono hc ball_subset_closedBall) (u j) f (hureg j)
      (P201.Elliptic.PoissonSchauder.isHolderLoc_of_isHolderOn hfΩ) (hu j).2.2.1
      ⟨A,hA,hAb j⟩ hfΩ
    have hsup : supNormOn (u j) Ω ≤ A :=
      P201.Elliptic.NewtonHessian.supNormOn_le hA (hAb j)
    exact ⟨hj,hbound.trans (mul_le_mul_of_nonneg_left (by linarith) hC.le)⟩
  obtain ⟨D,hD,hcontrol⟩ := interior_control_of_lifted_sequence hinterior hn hα hα1 hr
    hell he hc hcz hu hureg V hVb hV
  have hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      c2HolderNormOn α (u p-u q) V < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hg (ε/D) (div_pos hε hD)
    refine ⟨N,fun p hp q hq => ?_⟩
    apply (hcontrol p q).2.trans_lt
    have hd : ‖g p-g q‖ < ε/D := by simpa only [dist_eq_norm] using hN p hp q hq
    simpa only [mul_comm] using (lt_div_iff₀ hD).mp hd
  refine ⟨uniformCauchySeqOn_fderiv_of_c2HolderNormOn_cauchy V.isOpen
      (fun j => (hnorm j).1) hCauchy,
    uniformCauchySeqOn_second_fderiv_of_c2HolderNormOn_cauchy V.isOpen
      (fun j => (hnorm j).1) hCauchy, C*(A+holderNormOn α f Ω),
    C*(A+holderNormOn α f Ω), ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg hC.le (add_nonneg hA (holderNormOn_nonneg _ _ _))
  · exact mul_nonneg hC.le (add_nonneg hA (holderNormOn_nonneg _ _ _))
  · intro k i j y hy
    exact (norm_le_holderNormOn ((hnorm k).1.2.2.2 i j) hy).trans
      (((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α (u k) V).2.2 i j).trans
        (hnorm k).2)
  · intro k i j y hy y' hy'
    apply (P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm
      ((hnorm k).1.2.2.2 i j) hy hy').trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
    apply (show holderSeminormOn α (multiPartial (u k) {i,j}) V ≤
        holderNormOn α (multiPartial (u k) {i,j}) V from by
      rw [P201.Elliptic.PoissonSchauder.holderNormOn_eq]
      exact le_add_of_nonneg_left (supNormOn_nonneg _ _)).trans
    exact ((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α (u k) V).2.2 i j).trans
      (hnorm k).2


/-- The continuous limit of actual regular approximating solutions remains
an actual solution and retains local C²,α regularity. -/
lemma solution_limit_of_approximants
    (hinterior : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f : Space n → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hcz : ∀ x ∈ closedBall z r, c x ≤ 0)
    (hf : IsHolderOn α f (closedBall z r))
    {g : ℕ → C(sphere z r,ℝ)} {g₀ : C(sphere z r,ℝ)}
    (hg : Tendsto g atTop (𝓝 g₀))
    {u : ℕ → Space n → ℝ}
    (hu : ∀ j, IsBallSolution a b c f z r (g j) (u j))
    (hureg : ∀ j, IsC2HolderLocOn α (u j) (ballDomain z r)) :
    ∃ v : Space n → ℝ, IsBallSolution a b c f z r g₀ v ∧
      IsC2HolderLocOn α v (ballDomain z r) ∧
      ∀ w : Space n → ℝ, IsBallSolution a b c f z r g₀ w →
        EqOn w v (closedBall z r) := by
  have hcoeff : EllipticCoefficients (ballDomain z r) a b c :=
    ellipticCoefficients_of_holder hα hell ball_subset_closedBall he hc
  have hcz' : ∀ x ∈ ball z r, c x ≤ 0 :=
    fun x hx => hcz x (ball_subset_closedBall hx)
  obtain ⟨v,hvcont,hvlim,hvtrace,hvest⟩ :=
    ball_solution_uniform_limit hn hr hcoeff hcz' hg hu
  let U : ℕ → C(closedBall z r,ℝ) := fun j =>
    ⟨fun x => u j x, continuousOn_iff_continuous_domRestrict.mp (hu j).2.1⟩
  have hUC : CauchySeq U := ball_solution_maps_cauchy hn hr hcoeff hcz' hg.cauchySeq hu
  obtain ⟨A,hA⟩ := hUC.isBounded_range.exists_norm_le
  have hAb : ∀ j, ∀ x ∈ ball z r, ‖u j x‖ ≤ max A 0 := by
    intro j x hx
    exact ((U j).norm_coe_le_norm ⟨x,ball_subset_closedBall hx⟩).trans
      ((hA (U j) ⟨j,rfl⟩).trans (le_max_left A 0))
  have hlocal : ∀ x ∈ ball z r, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ ball z r ∧
      UniformCauchySeqOn (fun j => fderiv ℝ (u j)) atTop (ball x ρ) ∧
      UniformCauchySeqOn (fun j => fderiv ℝ (fderiv ℝ (u j))) atTop (ball x ρ) ∧
      ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧
        (∀ k i j, ∀ y ∈ ball x ρ, ‖multiPartial (u k) {i,j} y‖ ≤ M) ∧
        (∀ k i j, ∀ y ∈ ball x ρ, ∀ y' ∈ ball x ρ,
          ‖multiPartial (u k) {i,j} y - multiPartial (u k) {i,j} y'‖ ≤ H * dist y y' ^ α) := by
    intro x hx
    obtain ⟨s,hs,hsub⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
    have hρ : 0 < s/2 := half_pos hs
    have hcl : closure (ball x (s/2)) ⊆ ball z r := by
      rw [closure_ball x hρ.ne']
      intro y hy
      apply hsub
      exact (mem_closedBall.mp hy).trans_lt (by linarith)
    exact ⟨s/2,hρ,(subset_closure.trans hcl),
      local_interior_control hinterior hn hα hα1 hr hell he hc hcz hf hg.cauchySeq
        hu hureg (le_max_right A 0) hAb (ballDomain x (s/2)) isBounded_ball hcl⟩
  have hvreg : IsC2HolderLocOn α v (ballDomain z r) :=
    isC2HolderLocOn_of_local_uniformCauchy_derivatives (fun j => (hu j).1)
      (fun x hx => hvlim.tendsto_at (ball_subset_closedBall hx)) hlocal
  have hveq : ∀ x ∈ ball z r, nondivergenceOperator a b c v x = f x := by
    intro x hx
    obtain ⟨ρ,hρ,hsub,h1,h2,hrest⟩ := hlocal x hx
    exact equation_of_uniformCauchy_derivatives isOpen_ball
      (fun j => (hu j).1.mono hsub)
      (fun y hy => hvlim.tendsto_at (ball_subset_closedBall (hsub hy))) h1 h2 a b c f
      (fun j y hy => (hu j).2.2.1 y (hsub hy)) x (mem_ball_self hρ)
  have hv : IsBallSolution a b c f z r g₀ v := ⟨hvreg.1,hvcont,hveq,hvtrace⟩
  exact ⟨v,hv,hvreg,fun w hw => ball_solution_unique hn hr hcoeff hcz' hw hv⟩

/-- Once the lifted Hölder problem is solved, the full continuous-data
problem follows by smooth approximation and the interior a priori estimate.
The boundary datum is only a continuous map on the sphere. -/
lemma continuous_solvability_of_holder
    (hholder : HolderSolvabilityStatement)
    (hinterior : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement) :
    ContinuousSolvabilityStatement := by
  intro n hn α hα hα1 z r hr a b c he hc hcz f hf g
  obtain ⟨ell,hell,he⟩ := he
  let K := coefficientNormOn α a b c (closedBall z r)
  have hK : 0 ≤ K := by
    exact add_nonneg (add_nonneg
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => holderNormOn_nonneg _ _ _)
      (Finset.sum_nonneg fun i _ => holderNormOn_nonneg _ _ _)) (holderNormOn_nonneg _ _ _)
  obtain ⟨C,hC,hsolve⟩ := hholder hn α hα hα1 z r hr ell K hell hK
  obtain ⟨G,hGreg,hGbound,hGlim⟩ := BallApprox.sphere_smooth_lift_sequence hα.le hα1.le hr g
  have hsol : ∀ j : ℕ, ∃ u : Space n → ℝ,
      IsLiftedBallSolution α a b c f (G j) z r u := by
    intro j
    obtain ⟨u,hu,hestimate,hunique⟩ :=
      hsolve a b c he hc le_rfl hcz f (G j) hf (hGreg j).2
    exact ⟨u,hu⟩
  choose u hu using hsol
  have huclass : ∀ j, IsBallSolution a b c f z r ((G j).restrict (sphere z r)) (u j) := by
    intro j
    exact ⟨(hu j).1.1.mono ball_subset_closedBall, (hu j).1.1.continuousOn,
      (hu j).2.1, fun ζ => (hu j).2.2 ζ ζ.property⟩
  exact solution_limit_of_approximants hinterior hn hα hα1 hr hell he hc hcz hf hGlim
    huclass (fun j => isC2HolderLocOn_ball_of_upTo (hu j).1)

end BallContinuousLimit


namespace BallReflection
lemma laplacian_comp_add_left {n : ℕ} {u : Space n → ℝ}
    (c x : Space n) (hu : ContDiffAt ℝ 2 u (c+x)) :
    P201Specs.laplacian (fun y => u (c+y)) x = P201Specs.laplacian u (c+x) := by
  have hcomp : ContDiffAt ℝ 2 (fun y => u (c+y)) x :=
    hu.comp x (contDiffAt_const.add contDiffAt_id)
  rw [P201.MeanValues.laplacian_bridge _ _ hcomp,P201.MeanValues.laplacian_bridge _ _ hu]
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin n) ℝ), iteratedFDeriv_comp_add_left]

lemma harmonic_comp_add_left {n : ℕ} (Ω V : Domain n) {u : Space n → ℝ}
    (hu : P201Specs.MeanValues.IsHarmonic Ω u) (c : Space n)
    (hmap : MapsTo (fun y => c+y) (V : Set (Space n)) (Ω : Set (Space n))) :
    P201Specs.MeanValues.IsHarmonic V (fun y => u (c+y)) := by
  refine ⟨hu.1.comp (contDiffOn_const.add contDiffOn_id) hmap,?_⟩
  intro x hx
  rw [laplacian_comp_add_left c x
    ((hu.1 _ (hmap hx)).contDiffAt (Ω.isOpen.mem_nhds (hmap hx)))]
  exact hu.2 _ (hmap hx)

lemma harmonic_reflection_extension_affine {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r)
    (a c : Space n) (u : Space n → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨ball c r ∩ {x | 0 < inner ℝ a (x-c)},
        isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))⟩ u)
    (huc : ContinuousOn u (closedBall c r ∩ {x | 0 ≤ inner ℝ a (x-c)}))
    (hzero : ∀ x ∈ closedBall c r, inner ℝ a (x-c)=0 → u x=0) :
    ∃ v : Space n → ℝ,
      P201Specs.MeanValues.IsHarmonic ⟨ball c r,isOpen_ball⟩ v ∧
      EqOn v u (ball c r ∩ {x | 0 ≤ inner ℝ a (x-c)}) := by
  let Ω : Domain n := ⟨ball c r ∩ {x | 0 < inner ℝ a (x-c)},
    isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))⟩
  let V : Domain n := ⟨ball (0 : Space n) r ∩ {x | 0 < inner ℝ a x},
    isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))⟩
  have hmap : MapsTo (fun y => c+y) (V : Set (Space n)) (Ω : Set (Space n)) := by
    intro x hx
    refine ⟨?_,by simpa only [mem_ofPred_eq,add_sub_cancel_left] using hx.2⟩
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,dist_zero_right,sub_zero] using hx.1
  have hU := harmonic_comp_add_left Ω V hu c hmap
  obtain ⟨v,hv,heq⟩ := harmonic_reflection_extension_normal hn hr a (fun y => u (c+y)) hU
    (huc.comp (continuous_const.add continuous_id).continuousOn (by
      intro x hx
      refine ⟨?_,by simpa only [mem_ofPred_eq,add_sub_cancel_left] using hx.2⟩
      simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,dist_zero_right,sub_zero] using hx.1))
    (fun x hx hax => hzero (c+x) (by
      simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,dist_zero_right,sub_zero] using hx)
      (by simpa only [add_sub_cancel_left] using hax))
  refine ⟨fun y => v (-c+y),?_,?_⟩
  · apply harmonic_comp_add_left ⟨ball (0 : Space n) r,isOpen_ball⟩
      ⟨ball c r,isOpen_ball⟩ hv (-c)
    intro x hx
    change -c+x ∈ ball (0 : Space n) r
    change x ∈ ball c r at hx
    simpa only [mem_inter_iff,mem_ofPred_eq,mem_ball,dist_zero_right,dist_eq_norm,neg_add_eq_sub,sub_zero] using hx
  · intro x hx
    have hx' : -c+x ∈ ball (0 : Space n) r ∩ {y | 0 ≤ inner ℝ a y} := by
      simpa only [mem_inter_iff,mem_ofPred_eq,mem_ball,dist_zero_right,dist_eq_norm,neg_add_eq_sub,sub_zero] using hx
    simpa only [add_neg_cancel_left] using heq hx'
end BallReflection
namespace KelvinCalculus
lemma unitInversion_ne_zero {n : ℕ} {x : Space n} (hx : x ≠ 0) : unitInversion x ≠ 0 := by
  intro h
  have heq := unitInversion_involutive x
  rw [h,unitInversion_apply] at heq
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),inv_zero,zero_smul] at heq
  exact hx heq.symm

/-- Local spherical reflection, away from the inversion pole. Only the
interior harmonic class, continuity up to the sphere, and zero trace on the
local portion are assumed. -/
lemma harmonic_sphere_reflection_at_tangent {n : ℕ} (hn : 2 ≤ n)
    (a : Space n) {r : ℝ} (hr : 0 < r) (ha : ‖a‖ = r)
    (Ω : Domain n) (u : Space n → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨(Ω : Set (Space n)) ∩ ball a r,Ω.isOpen.inter isOpen_ball⟩ u)
    (huc : ContinuousOn u ((Ω : Set (Space n)) ∩ closedBall a r))
    (hzero : ∀ x ∈ (Ω : Set (Space n)) ∩ sphere a r, u x=0)
    {p : Space n} (hp : p ∈ (Ω : Set (Space n)) ∩ sphere a r) (hp0 : p ≠ 0) :
    ∃ (W : Domain n) (v : Space n → ℝ), p ∈ W ∧
      P201Specs.MeanValues.IsHarmonic W v ∧
      EqOn v u ((W : Set (Space n)) ∩ closedBall a r) := by
  let q := unitInversion p
  have hq0 : q ≠ 0 := unitInversion_ne_zero hp0
  have hq : inner ℝ a q = (1:ℝ)/2 :=
    (unitInversion_mem_sphere_tangent a hr ha hq0).mp (by
      simpa only [q,unitInversion_involutive] using hp.2)
  have hN : {y : Space n | y ≠ 0} ∩ unitInversion ⁻¹' (Ω : Set (Space n)) ∈ 𝓝 q := by
    apply inter_mem (eventually_ne_nhds hq0)
    apply (unitInversion_contDiffAt hq0).continuousAt.preimage_mem_nhds
    have hqp : unitInversion q = p := unitInversion_involutive p
    rw [hqp]
    exact Ω.isOpen.mem_nhds hp.1
  obtain ⟨R,hR,hRN⟩ : ∃ R : ℝ, 0<R ∧ closedBall q R ⊆
      {y : Space n | y ≠ 0} ∩ unitInversion ⁻¹' (Ω : Set (Space n)) :=
    Metric.nhds_basis_closedBall.mem_iff.mp hN
  let D : Domain n := ⟨(Ω : Set (Space n)) ∩ ball a r,Ω.isOpen.inter isOpen_ball⟩
  let H : Domain n := ⟨ball q R ∩ {x | 0 < inner ℝ a (x-q)},
    isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))⟩
  have hhalf (x : Space n) : inner ℝ a (x-q) = inner ℝ a x-(1:ℝ)/2 := by
    rw [inner_sub_right,hq]
  have hUH : P201Specs.MeanValues.IsHarmonic H (kelvinTransform u) := by
    apply kelvinTransform_harmonic hn D H hu
    · intro x hx
      exact (hRN (ball_subset_closedBall hx.1)).1
    · intro x hx
      have hnx := (hRN (ball_subset_closedBall hx.1)).1
      refine ⟨(hRN (ball_subset_closedBall hx.1)).2,?_⟩
      apply (unitInversion_mem_ball_tangent a hr ha hnx).mpr
      have hax : 0 < inner ℝ a (x-q) := hx.2
      rw [hhalf] at hax
      linarith
  have hmap : MapsTo unitInversion (closedBall q R ∩ {x | 0 ≤ inner ℝ a (x-q)})
      ((Ω : Set (Space n)) ∩ closedBall a r) := by
    intro x hx
    refine ⟨(hRN hx.1).2,?_⟩
    apply (unitInversion_mem_closedBall_tangent a hr ha (hRN hx.1).1).mpr
    have hax : 0 ≤ inner ℝ a (x-q) := hx.2
    rw [hhalf] at hax
    linarith
  have hUc : ContinuousOn (kelvinTransform u)
      (closedBall q R ∩ {x | 0 ≤ inner ℝ a (x-q)}) := by
    apply ContinuousOn.mul
    · intro x hx
      exact (normInvPow_contDiffAt (hRN hx.1).1 (n-2)).continuousAt.continuousWithinAt
    · apply huc.comp ?_ hmap
      intro x hx
      exact (unitInversion_contDiffAt (hRN hx.1).1).continuousAt.continuousWithinAt
  have hUz : ∀ x ∈ closedBall q R, inner ℝ a (x-q)=0 → kelvinTransform u x=0 := by
    intro x hx hz
    have hxS : unitInversion x ∈ sphere a r := by
      apply (unitInversion_mem_sphere_tangent a hr ha (hRN hx).1).mpr
      rw [hhalf] at hz
      linarith
    rw [kelvinTransform,hzero _ ⟨(hRN hx).2,hxS⟩,mul_zero]
  obtain ⟨v,hv,heq⟩ := BallReflection.harmonic_reflection_extension_affine hn hR a q
    (kelvinTransform u) hUH hUc hUz
  have hIcont : ContinuousOn (unitInversion (n := n)) {x : Space n | x ≠ 0} :=
    fun x hx => (unitInversion_contDiffAt hx).continuousAt.continuousWithinAt
  let W : Domain n := ⟨{x : Space n | x ≠ 0} ∩ unitInversion ⁻¹' ball q R,
    hIcont.isOpen_inter_preimage (isClosed_singleton.isOpen_compl) isOpen_ball⟩
  refine ⟨W,kelvinTransform v,?_,?_,?_⟩
  · exact ⟨hp0,by simp only [mem_preimage,mem_ball,show unitInversion p=q from rfl,dist_self]; exact hR⟩
  · apply kelvinTransform_harmonic hn ⟨ball q R,isOpen_ball⟩ W hv
    · intro x hx
      exact hx.1
    · intro x hx
      exact hx.2
  · intro x hx
    have hix : unitInversion x ∈ ball q R ∩ {y | 0 ≤ inner ℝ a (y-q)} := by
      refine ⟨hx.1.2,?_⟩
      have hax := (unitInversion_mem_closedBall_tangent a hr ha
        (unitInversion_ne_zero hx.1.1)).mp (by simpa only [unitInversion_involutive] using hx.2)
      change 0 ≤ inner ℝ a (unitInversion x-q)
      rw [hhalf]
      linarith
    change (‖x‖^(n-2))⁻¹*v (unitInversion x)=u x
    rw [heq hix]
    exact kelvinTransform_involutive u hx.1.1
end KelvinCalculus



namespace BallWithinRestriction

lemma within_jets_mono {n : ℕ} {s t : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t) (hst : s ⊆ t)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u t) :
    (∀ i, EqOn (firstPartialWithin u s i) (firstPartialWithin u t i) s) ∧
    ∀ i j, EqOn (secondPartialWithin u s i j) (secondPartialWithin u t i j) s := by
  have hfirst (i : Fin n) : EqOn (firstPartialWithin u s i) (firstPartialWithin u t i) s := by
    intro x hx
    unfold firstPartialWithin
    rw [fderivWithin_subset hst (hs x hx) ((hu.differentiableOn (by norm_num)) x (hst hx))]
  refine ⟨hfirst,?_⟩
  intro i j x hx
  unfold secondPartialWithin
  rw [fderivWithin_congr' (hfirst j) hx]
  rw [fderivWithin_subset hst (hs x hx)]
  exact (((hu.fderivWithin ht (m := 1) (by norm_num)).clm_apply contDiffOn_const).differentiableOn
    (by norm_num)) x (hst hx)

lemma isC2HolderUpToOn_mono {n : ℕ} {α : ℝ} {s t : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t) (hst : s ⊆ t)
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u t) :
    IsC2HolderUpToOn α u s := by
  have hjets := within_jets_mono hs ht hst hu.1
  refine ⟨hu.1.mono hst, P201.Elliptic.PoissonSchauder.boundedOn_mono hu.2.1 hst, ?_, ?_⟩
  · intro i
    obtain ⟨M,hM,hb⟩ := hu.2.2.1 i
    exact ⟨M,hM,fun x hx => (congrArg norm (hjets.1 i hx)).trans_le (hb x (hst hx))⟩
  · intro i j
    exact P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono (hu.2.2.2 i j) hst) (hjets.2 i j)

lemma c2HolderUpToNormOn_mono {n : ℕ} {α : ℝ} {s t : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t) (hst : s ⊆ t)
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u t) :
    c2HolderUpToNormOn α u s ≤ c2HolderUpToNormOn α u t := by
  have hjets := within_jets_mono hs ht hst hu.1
  rw [c2HolderUpToNormOn_eq_holder_sums,c2HolderUpToNormOn_eq_holder_sums]
  apply add_le_add
  · apply add_le_add
    · exact P201.Elliptic.PoissonSchauder.supNormOn_mono hu.2.1 hst
    · apply Finset.sum_le_sum
      intro i hi
      rw [BallC2Complete.supNormOn_congr (hjets.1 i)]
      exact P201.Elliptic.PoissonSchauder.supNormOn_mono (hu.2.2.1 i) hst
  · apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    rw [BallC2Complete.holderNormOn_congr (hjets.2 i j)]
    exact P201.Elliptic.PoissonSchauder.holderNormOn_mono (hu.2.2.2 i j) hst

end BallWithinRestriction


namespace HolderComposition

lemma isHolderOn_comp_lipschitz {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {f : Space n → ℝ} {φ : Space n → Space n} {s t : Set (Space n)}
    (hf : IsHolderOn α f t) (hmap : MapsTo φ s t)
    {L : NNReal} (hL : LipschitzOnWith L φ s) : IsHolderOn α (f ∘ φ) s := by
  obtain ⟨M,H,hM,hH,hb,hh⟩ := hf
  refine ⟨M,H*(L:ℝ)^α,hM,mul_nonneg hH (Real.rpow_nonneg L.coe_nonneg _),
    fun x hx => hb _ (hmap hx),?_⟩
  intro x hx y hy
  calc
    ‖f (φ x)-f (φ y)‖ ≤ H*dist (φ x) (φ y)^α := hh _ (hmap hx) _ (hmap hy)
    _ ≤ H*((L:ℝ)*dist x y)^α := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (hL.dist_le_mul x hx y hy) hα) hH
    _ = _ := by rw [Real.mul_rpow L.coe_nonneg dist_nonneg]; ring

lemma lower_order_holder_jets {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u : Space n → ℝ} {s : Set (Space n)} (hs : IsCompact s) (hconv : Convex ℝ s)
    (hdiff : UniqueDiffOn ℝ s) (hu : IsC2HolderUpToOn α u s) :
    IsHolderOn α u s ∧ ∀ i, IsHolderOn α (firstPartialWithin u s i) s := by
  constructor
  · obtain ⟨L,hL⟩ := hu.1.exists_lipschitzOnWith (by norm_num) hconv hs
    exact BallGeometry.holder_of_bounded_lipschitz hα hα1 hu.2.1 hL
  · intro i
    have hdi : ContDiffOn ℝ 1 (firstPartialWithin u s i) s :=
      (hu.1.fderivWithin hdiff (by norm_num)).clm_apply contDiffOn_const
    obtain ⟨L,hL⟩ := hdi.exists_lipschitzOnWith (by norm_num) hconv hs
    exact BallGeometry.holder_of_bounded_lipschitz hα hα1 (hu.2.2.1 i) hL

lemma lower_order_holder_jets_convex {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u : Space n → ℝ} {s : Set (Space n)} (hconv : Convex ℝ s)
    (hdiff : UniqueDiffOn ℝ s) (hu : IsC2HolderUpToOn α u s) :
    IsHolderOn α u s ∧ ∀ i, IsHolderOn α (firstPartialWithin u s i) s := by
  let N := c2HolderUpToNormOn α u s
  have hN : 0 ≤ N := c2HolderUpToNormOn_nonneg _ _ _
  have hL : LipschitzOnWith ⟨N,hN⟩ u s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change ‖u x-u y‖ ≤ N*dist x y
    simpa only [dist_eq_norm] using hconv.norm_image_sub_le_of_norm_fderivWithin_le
      (hu.1.differentiableOn (by norm_num))
      (fun x hx => norm_fderivWithin_le_c2HolderUpToNormOn hu hx) hy hx
  refine ⟨BallGeometry.holder_of_bounded_lipschitz hα hα1 hu.2.1 hL,?_⟩
  intro i
  have hdi : ContDiffOn ℝ 1 (firstPartialWithin u s i) s :=
    (hu.1.fderivWithin hdiff (by norm_num)).clm_apply contDiffOn_const
  have hLi : LipschitzOnWith ⟨N,hN⟩ (firstPartialWithin u s i) s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change ‖firstPartialWithin u s i x-firstPartialWithin u s i y‖ ≤ N*dist x y
    simpa only [dist_eq_norm] using hconv.norm_image_sub_le_of_norm_fderivWithin_le
      (hdi.differentiableOn (by norm_num))
      (fun x hx => norm_fderivWithin_firstPartial_le_c2HolderUpToNormOn hu hx i) hy hx
  exact BallGeometry.holder_of_bounded_lipschitz hα hα1 (hu.2.2.1 i) hLi

lemma clm_apply_eq_sum_coordinates {n : ℕ} (A : Space n →L[ℝ] ℝ) (v : Space n) :
    A v = ∑ i : Fin n, A (coordinate n i)*v i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma firstPartialWithin_comp {n : ℕ} {u : Space n → ℝ} {φ : Space n → Space n}
    {s t : Set (Space n)} {x : Space n} (hx : x ∈ s) (hs : UniqueDiffOn ℝ s)
    (hu : DifferentiableWithinAt ℝ u t (φ x)) (hφ : DifferentiableWithinAt ℝ φ s x)
    (hmap : MapsTo φ s t) (i : Fin n) :
    firstPartialWithin (u ∘ φ) s i x = ∑ j : Fin n,
      firstPartialWithin u t j (φ x)*firstPartialWithin (fun y => φ y j) s i x := by
  have hcoord (j : Fin n) :
      fderivWithin ℝ (fun y => φ y j) s x =
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).comp (fderivWithin ℝ φ s x) := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasFDerivWithinAt
      x hφ.hasFDerivWithinAt).fderivWithin (hs x hx)
  unfold firstPartialWithin
  rw [fderivWithin_comp x hu hφ hmap (hs x hx),ContinuousLinearMap.comp_apply,
    clm_apply_eq_sum_coordinates]
  apply Finset.sum_congr rfl
  intro j _
  rw [hcoord]
  rfl

lemma firstPartialWithin_sum {n : ℕ} {ι : Type*} (I : Finset ι)
    (f : ι → Space n → ℝ) {s : Set (Space n)} {x : Space n}
    (hs : UniqueDiffWithinAt ℝ s x)
    (hf : ∀ i ∈ I, DifferentiableWithinAt ℝ (f i) s x) (j : Fin n) :
    firstPartialWithin (fun y => ∑ i ∈ I, f i y) s j x =
      ∑ i ∈ I, firstPartialWithin (f i) s j x := by
  unfold firstPartialWithin
  rw [fderivWithin_fun_sum hs hf]
  simp only [sum_apply]

lemma firstPartialWithin_mul {n : ℕ} {u v : Space n → ℝ}
    {s : Set (Space n)} {x : Space n} (hs : UniqueDiffWithinAt ℝ s x)
    (hu : DifferentiableWithinAt ℝ u s x) (hv : DifferentiableWithinAt ℝ v s x) (i : Fin n) :
    firstPartialWithin (fun y => u y*v y) s i x =
      u x*firstPartialWithin v s i x+v x*firstPartialWithin u s i x := by
  unfold firstPartialWithin
  rw [fderivWithin_fun_mul hs hu hv]
  rfl

lemma secondPartialWithin_comp {n : ℕ} {u : Space n → ℝ} {φ : Space n → Space n}
    {s t : Set (Space n)} {x : Space n} (hx : x ∈ s)
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hu : ContDiffOn ℝ 2 u t) (hφ : ContDiffOn ℝ 2 φ s)
    (hmap : MapsTo φ s t) (i j : Fin n) :
    secondPartialWithin (u ∘ φ) s i j x = ∑ k : Fin n,
      (firstPartialWithin u t k (φ x)*secondPartialWithin (fun y => φ y k) s i j x+
        firstPartialWithin (fun y => φ y k) s j x * ∑ l : Fin n,
          secondPartialWithin u t l k (φ x)*firstPartialWithin (fun y => φ y l) s i x) := by
  have hu' (k : Fin n) : ContDiffOn ℝ 1 (firstPartialWithin u t k) t :=
    (hu.fderivWithin ht (by norm_num)).clm_apply contDiffOn_const
  have hφc (k : Fin n) : ContDiffOn ℝ 2 (fun y => φ y k) s :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k).contDiff.comp_contDiffOn hφ
  have hφ' (k : Fin n) : ContDiffOn ℝ 1 (firstPartialWithin (fun y => φ y k) s j) s :=
    ((hφc k).fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
  have hfirst : EqOn (firstPartialWithin (u ∘ φ) s j)
      (fun y => ∑ k : Fin n, firstPartialWithin u t k (φ y)*
        firstPartialWithin (fun z => φ z k) s j y) s := by
    intro y hy
    exact firstPartialWithin_comp hy hs (hu.differentiableOn (by norm_num) _ (hmap hy))
      (hφ.differentiableOn (by norm_num) y hy) hmap j
  change fderivWithin ℝ (firstPartialWithin (u ∘ φ) s j) s x (coordinate n i) = _
  rw [fderivWithin_congr' hfirst hx]
  change firstPartialWithin (fun y => ∑ k : Fin n, firstPartialWithin u t k (φ y)*
    firstPartialWithin (fun z => φ z k) s j y) s i x = _
  rw [firstPartialWithin_sum Finset.univ _ (hs x hx) (by
    intro k _
    exact (((hu' k).differentiableOn (by norm_num) _ (hmap hx)).comp x
      (hφ.differentiableOn (by norm_num) x hx) hmap).mul
        ((hφ' k).differentiableOn (by norm_num) x hx))]
  apply Finset.sum_congr rfl
  intro k _
  rw [firstPartialWithin_mul (u := fun y => firstPartialWithin u t k (φ y))
    (v := firstPartialWithin (fun y => φ y k) s j) (hs x hx)
    (((hu' k).differentiableOn (by norm_num) _ (hmap hx)).comp x
      (hφ.differentiableOn (by norm_num) x hx) hmap)
    ((hφ' k).differentiableOn (by norm_num) x hx) i]
  have he : firstPartialWithin (fun y => firstPartialWithin u t k (φ y)) s i x =
      ∑ l : Fin n, firstPartialWithin (firstPartialWithin u t k) t l (φ x)*
        firstPartialWithin (fun y => φ y l) s i x := by
    simpa only [Function.comp_def] using
      firstPartialWithin_comp (u := firstPartialWithin u t k) hx hs
        ((hu' k).differentiableOn (by norm_num) _ (hmap hx))
        (hφ.differentiableOn (by norm_num) x hx) hmap i
  rw [he]
  rfl

/-- The actual C²,α class is stable under a C²,α coordinate map between
compact convex sets. Both first and second derivatives are within derivatives,
so this applies on genuine closed boundary patches. -/
lemma c2HolderUpToOn_comp {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u : Space n → ℝ} {φ : Space n → Space n} {s t : Set (Space n)}
    (hs : IsCompact s) (hsconv : Convex ℝ s) (hsdiff : UniqueDiffOn ℝ s)
    (ht : IsCompact t) (htconv : Convex ℝ t) (htdiff : UniqueDiffOn ℝ t)
    (hu : IsC2HolderUpToOn α u t)
    (hφ : ∀ k : Fin n, IsC2HolderUpToOn α (fun y => φ y k) s)
    (hmap : MapsTo φ s t) : IsC2HolderUpToOn α (u ∘ φ) s := by
  have hφC : ContDiffOn ℝ 2 φ s := (contDiffOn_piLp 2).mpr (fun k => (hφ k).1)
  obtain ⟨L,hL⟩ := hφC.exists_lipschitzOnWith (by norm_num) hsconv hs
  have hujet := lower_order_holder_jets hα hα1 ht htconv htdiff hu
  have hφjet (k : Fin n) := lower_order_holder_jets hα hα1 hs hsconv hsdiff (hφ k)
  have hF (i : Fin n) : IsHolderOn α (firstPartialWithin (u ∘ φ) s i) s := by
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_finset_sum Finset.univ _ (fun k _ =>
        isHolderOn_mul (isHolderOn_comp_lipschitz hα (hujet.2 k) hmap hL) ((hφjet k).2 i)))
    intro x hx
    exact firstPartialWithin_comp hx hsdiff (hu.1.differentiableOn (by norm_num) _ (hmap hx))
      (hφC.differentiableOn (by norm_num) x hx) hmap i
  refine ⟨hu.1.comp hφC hmap,?_,?_,?_⟩
  · obtain ⟨M,hM,hb⟩ := hu.2.1
    exact ⟨M,hM,fun x hx => hb _ (hmap hx)⟩
  · intro i
    obtain ⟨M,H,hM,hH,hb,hh⟩ := hF i
    exact ⟨M,hM,hb⟩
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_finset_sum Finset.univ _ (fun k _ =>
        isHolderOn_add
          (isHolderOn_mul (isHolderOn_comp_lipschitz hα (hujet.2 k) hmap hL)
            ((hφ k).2.2.2 i j))
          (isHolderOn_mul ((hφjet k).2 j)
            (isHolderOn_finset_sum Finset.univ _ (fun l _ =>
              isHolderOn_mul (isHolderOn_comp_lipschitz hα (hu.2.2.2 l k) hmap hL)
                ((hφjet l).2 i))))))
    intro x hx
    exact secondPartialWithin_comp hx hsdiff htdiff hu.1 hφC hmap i j

/-- Composition on convex boundary patches; the target need not be compact. -/
lemma c2HolderUpToOn_comp_of_lipschitz {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u : Space n → ℝ} {φ : Space n → Space n} {s t : Set (Space n)}
    (hsconv : Convex ℝ s) (hsdiff : UniqueDiffOn ℝ s)
    (htconv : Convex ℝ t) (htdiff : UniqueDiffOn ℝ t)
    (hu : IsC2HolderUpToOn α u t)
    (hφ : ∀ k : Fin n, IsC2HolderUpToOn α (fun y => φ y k) s)
    (hmap : MapsTo φ s t) {L : NNReal} (hL : LipschitzOnWith L φ s) :
    IsC2HolderUpToOn α (u ∘ φ) s := by
  have hφC : ContDiffOn ℝ 2 φ s := (contDiffOn_piLp 2).mpr (fun k => (hφ k).1)
  have hujet := lower_order_holder_jets_convex hα hα1 htconv htdiff hu
  have hφjet (k : Fin n) := lower_order_holder_jets_convex hα hα1 hsconv hsdiff (hφ k)
  have hF (i : Fin n) : IsHolderOn α (firstPartialWithin (u ∘ φ) s i) s := by
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_finset_sum Finset.univ _ (fun k _ =>
        isHolderOn_mul (isHolderOn_comp_lipschitz hα (hujet.2 k) hmap hL) ((hφjet k).2 i)))
    intro x hx
    exact firstPartialWithin_comp hx hsdiff (hu.1.differentiableOn (by norm_num) _ (hmap hx))
      (hφC.differentiableOn (by norm_num) x hx) hmap i
  refine ⟨hu.1.comp hφC hmap,?_,?_,?_⟩
  · obtain ⟨M,hM,hb⟩ := hu.2.1
    exact ⟨M,hM,fun x hx => hb _ (hmap hx)⟩
  · intro i
    obtain ⟨M,H,hM,hH,hb,hh⟩ := hF i
    exact ⟨M,hM,hb⟩
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_finset_sum Finset.univ _ (fun k _ =>
        isHolderOn_add
          (isHolderOn_mul (isHolderOn_comp_lipschitz hα (hujet.2 k) hmap hL)
            ((hφ k).2.2.2 i j))
          (isHolderOn_mul ((hφjet k).2 j)
            (isHolderOn_finset_sum Finset.univ _ (fun l _ =>
              isHolderOn_mul (isHolderOn_comp_lipschitz hα (hu.2.2.2 l k) hmap hL)
                ((hφjet l).2 i))))))
    intro x hx
    exact secondPartialWithin_comp hx hsdiff htdiff hu.1 hφC hmap i j

lemma firstPartialWithin_add {n : ℕ} {u v : Space n → ℝ}
    {s : Set (Space n)} {x : Space n} (hs : UniqueDiffWithinAt ℝ s x)
    (hu : DifferentiableWithinAt ℝ u s x) (hv : DifferentiableWithinAt ℝ v s x) (i : Fin n) :
    firstPartialWithin (fun y => u y+v y) s i x =
      firstPartialWithin u s i x+firstPartialWithin v s i x := by
  unfold firstPartialWithin
  rw [fderivWithin_fun_add hs hu hv]
  rfl

lemma secondPartialWithin_mul {n : ℕ} {u v : Space n → ℝ}
    {s : Set (Space n)} {x : Space n} (hx : x ∈ s) (hs : UniqueDiffOn ℝ s)
    (hu : ContDiffOn ℝ 2 u s) (hv : ContDiffOn ℝ 2 v s) (i j : Fin n) :
    secondPartialWithin (fun y => u y*v y) s i j x =
      (u x*secondPartialWithin v s i j x+
        firstPartialWithin v s j x*firstPartialWithin u s i x)+
      (v x*secondPartialWithin u s i j x+
        firstPartialWithin u s j x*firstPartialWithin v s i x) := by
  have hu' : ContDiffOn ℝ 1 (firstPartialWithin u s j) s :=
    (hu.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
  have hv' : ContDiffOn ℝ 1 (firstPartialWithin v s j) s :=
    (hv.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
  have heq : EqOn (firstPartialWithin (fun y => u y*v y) s j)
      (fun y => u y*firstPartialWithin v s j y+v y*firstPartialWithin u s j y) s := by
    intro y hy
    exact firstPartialWithin_mul (hs y hy)
      (hu.differentiableOn (by norm_num) y hy) (hv.differentiableOn (by norm_num) y hy) j
  change fderivWithin ℝ (firstPartialWithin (fun y => u y*v y) s j) s x (coordinate n i) = _
  rw [fderivWithin_congr' heq hx]
  change firstPartialWithin (fun y => u y*firstPartialWithin v s j y+
    v y*firstPartialWithin u s j y) s i x = _
  rw [firstPartialWithin_add (u := fun y => u y*firstPartialWithin v s j y)
    (v := fun y => v y*firstPartialWithin u s j y) (hs x hx)
    ((hu.differentiableOn (by norm_num) x hx).mul (hv'.differentiableOn (by norm_num) x hx))
    ((hv.differentiableOn (by norm_num) x hx).mul (hu'.differentiableOn (by norm_num) x hx)) i,
    firstPartialWithin_mul (hs x hx) (hu.differentiableOn (by norm_num) x hx)
      (hv'.differentiableOn (by norm_num) x hx) i,
    firstPartialWithin_mul (hs x hx) (hv.differentiableOn (by norm_num) x hx)
      (hu'.differentiableOn (by norm_num) x hx) i]
  rfl

lemma c2HolderUpToOn_mul {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u v : Space n → ℝ} {s : Set (Space n)}
    (hs : IsCompact s) (hconv : Convex ℝ s) (hdiff : UniqueDiffOn ℝ s)
    (hu : IsC2HolderUpToOn α u s) (hv : IsC2HolderUpToOn α v s) :
    IsC2HolderUpToOn α (fun y => u y*v y) s := by
  have hujet := lower_order_holder_jets hα hα1 hs hconv hdiff hu
  have hvjet := lower_order_holder_jets hα hα1 hs hconv hdiff hv
  have hF (i : Fin n) : IsHolderOn α (firstPartialWithin (fun y => u y*v y) s i) s := by
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_add (isHolderOn_mul hujet.1 (hvjet.2 i))
        (isHolderOn_mul hvjet.1 (hujet.2 i)))
    intro x hx
    exact firstPartialWithin_mul (hdiff x hx) (hu.1.differentiableOn (by norm_num) x hx)
      (hv.1.differentiableOn (by norm_num) x hx) i
  refine ⟨hu.1.mul hv.1,?_,?_,?_⟩
  · obtain ⟨M,H,hM,hH,hb,hh⟩ := isHolderOn_mul hujet.1 hvjet.1
    exact ⟨M,hM,hb⟩
  · intro i
    obtain ⟨M,H,hM,hH,hb,hh⟩ := hF i
    exact ⟨M,hM,hb⟩
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_add
        (isHolderOn_add (isHolderOn_mul hujet.1 (hv.2.2.2 i j))
          (isHolderOn_mul (hvjet.2 j) (hujet.2 i)))
        (isHolderOn_add (isHolderOn_mul hvjet.1 (hu.2.2.2 i j))
          (isHolderOn_mul (hujet.2 j) (hvjet.2 i))))
    intro x hx
    exact secondPartialWithin_mul hx hdiff hu.1 hv.1 i j

lemma c2HolderUpToOn_mono {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s t : Set (Space n)} (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hu : IsC2HolderUpToOn α u t) (hsub : s ⊆ t) : IsC2HolderUpToOn α u s :=
  BallWithinRestriction.isC2HolderUpToOn_mono hs ht hsub hu

/-- Kelvin transport preserves the actual C²,α up-to-boundary class on
compact convex patches away from the pole. The map and scalar weight are
verified smooth; no regularity pullback certificate is assumed. -/
lemma kelvinTransform_c2HolderUpToOn {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u : Space n → ℝ} {s t : Set (Space n)}
    (hs : IsCompact s) (hsconv : Convex ℝ s) (hsdiff : UniqueDiffOn ℝ s)
    (ht : IsCompact t) (htconv : Convex ℝ t) (htdiff : UniqueDiffOn ℝ t)
    (hu : IsC2HolderUpToOn α u t)
    (hs0 : ∀ x ∈ s, x ≠ 0) (hmap : MapsTo KelvinCalculus.unitInversion s t) :
    IsC2HolderUpToOn α (KelvinCalculus.kelvinTransform u) s := by
  let D : Domain n := ⟨{x : Space n | x ≠ 0},isClosed_singleton.isOpen_compl⟩
  have hI : ContDiffOn ℝ (3:ℕ) (KelvinCalculus.unitInversion (n := n)) D := by
    intro x hx
    exact (contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx).contDiffWithinAt
  have hweight : ContDiffOn ℝ (3:ℕ) (fun y : Space n => (‖y‖^(n-2))⁻¹) D := by
    intro x hx
    exact (((contDiffAt_norm ℝ hx).pow (n-2)).inv
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))).contDiffWithinAt
  have hW := smooth_c2HolderUpToOn_compact_convex_on_open hα hα1 hweight hs hsconv hsdiff hs0
  have hcoords (k : Fin n) :
      IsC2HolderUpToOn α (fun y => KelvinCalculus.unitInversion y k) s := by
    apply smooth_c2HolderUpToOn_compact_convex_on_open hα hα1 (Ω := D)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k).contDiff.comp_contDiffOn hI)
      hs hsconv hsdiff hs0
  exact c2HolderUpToOn_mul hα hα1 hs hsconv hsdiff hW
    (c2HolderUpToOn_comp hα hα1 hs hsconv hsdiff ht htconv htdiff hu hcoords hmap)

/-- Kelvin transport preserves the actual C²,α up-to-boundary class on
compact convex patches away from the pole. The map and scalar weight are
verified smooth; no regularity pullback certificate is assumed. -/
lemma kelvinTransform_c2HolderUpToOn_convex_target {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u : Space n → ℝ} {s t : Set (Space n)}
    (hs : IsCompact s) (hsconv : Convex ℝ s) (hsdiff : UniqueDiffOn ℝ s)
    (htconv : Convex ℝ t) (htdiff : UniqueDiffOn ℝ t)
    (hu : IsC2HolderUpToOn α u t)
    (hs0 : ∀ x ∈ s, x ≠ 0) (hmap : MapsTo KelvinCalculus.unitInversion s t) :
    IsC2HolderUpToOn α (KelvinCalculus.kelvinTransform u) s := by
  let D : Domain n := ⟨{x : Space n | x ≠ 0},isClosed_singleton.isOpen_compl⟩
  have hI : ContDiffOn ℝ (3:ℕ) (KelvinCalculus.unitInversion (n := n)) D := by
    intro x hx
    exact (contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx).contDiffWithinAt
  have hweight : ContDiffOn ℝ (3:ℕ) (fun y : Space n => (‖y‖^(n-2))⁻¹) D := by
    intro x hx
    exact (((contDiffAt_norm ℝ hx).pow (n-2)).inv
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))).contDiffWithinAt
  have hW := smooth_c2HolderUpToOn_compact_convex_on_open hα hα1 hweight hs hsconv hsdiff hs0
  have hcoords (k : Fin n) :
      IsC2HolderUpToOn α (fun y => KelvinCalculus.unitInversion y k) s := by
    apply smooth_c2HolderUpToOn_compact_convex_on_open hα hα1 (Ω := D)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k).contDiff.comp_contDiffOn hI)
      hs hsconv hsdiff hs0
  obtain ⟨L,hL⟩ := (hI.mono hs0).exists_lipschitzOnWith (by norm_num) hsconv hs
  exact c2HolderUpToOn_mul hα hα1 hs hsconv hsdiff hW
    (c2HolderUpToOn_comp_of_lipschitz hα hα1 hsconv hsdiff htconv htdiff hu hcoords hmap hL)

end HolderComposition


namespace ConvexWithinLimit
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasFDerivWithinAt_convex_of_uniformLimit {s : Set E}
    (hconv : Convex ℝ s) (hclosed : IsClosed s) (hint : (interior s).Nonempty)
    {f : ℕ → E → F} {A : ℕ → E → E →L[ℝ] F}
    {g : E → F} {B : E → E →L[ℝ] F}
    (hderiv : ∀ j, ∀ x ∈ s, HasFDerivWithinAt (f j) (A j x) (s) x)
    (hAcont : ∀ j, ContinuousOn (A j) (s))
    (hf : TendstoUniformlyOn f g atTop (s))
    (hA : TendstoUniformlyOn A B atTop (s)) :
    ∀ x ∈ s, HasFDerivWithinAt g (B x) (s) x := by
  have hclosure : closure (interior s) = s :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hint).trans hclosed.closure_eq
  have hgcont : ContinuousOn g (s) := hf.continuousOn (Frequently.of_forall
    (fun j x hx => (hderiv j x hx).continuousWithinAt))
  have hBcont : ContinuousOn B (s) := hA.continuousOn (Frequently.of_forall hAcont)
  have hderivOpen : ∀ x ∈ interior s, HasFDerivAt g (B x) x := by
    intro x hx
    refine hasFDerivAt_of_tendstoUniformlyOn (f := f) (g := g) isOpen_interior (hA.mono interior_subset) ?_ ?_ hx
    · intro j x hx
      exact (hderiv j x (interior_subset hx)).hasFDerivAt
        (mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset)
    · intro x hx
      exact hf.tendsto_at (interior_subset hx)
  have hdiff : DifferentiableOn ℝ g (interior s) :=
    fun x hx => (hderivOpen x hx).differentiableAt.differentiableWithinAt
  intro x hx
  have hext : HasFDerivWithinAt g (B x) (closure (interior s)) x := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff (hconv.interior) isOpen_interior
    · intro y hy
      rw [hclosure] at hy
      exact (hgcont y hy).mono interior_subset
    · have hBlim : Tendsto B (𝓝[interior s] x) (𝓝 (B x)) :=
        (hBcont x hx).mono interior_subset
      apply hBlim.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hderivOpen y hy).fderiv.symm
  simpa only [hclosure] using hext

lemma contDiffOn_two_convex_of_uniformJets {s : Set E}
    (hconv : Convex ℝ s) (hclosed : IsClosed s) (hint : (interior s).Nonempty)
    {f : ℕ → E → F} {A : ℕ → E → E →L[ℝ] F}
    {B : ℕ → E → E →L[ℝ] (E →L[ℝ] F)}
    {g : E → F} {a : E → E →L[ℝ] F} {b : E → E →L[ℝ] (E →L[ℝ] F)}
    (hderiv1 : ∀ j, ∀ x ∈ s, HasFDerivWithinAt (f j) (A j x) (s) x)
    (hderiv2 : ∀ j, ∀ x ∈ s, HasFDerivWithinAt (A j) (B j x) (s) x)
    (hBcont : ∀ j, ContinuousOn (B j) (s))
    (hf : TendstoUniformlyOn f g atTop (s))
    (hA : TendstoUniformlyOn A a atTop (s))
    (hB : TendstoUniformlyOn B b atTop (s)) :
    ContDiffOn ℝ 2 g (s) ∧
      (∀ x ∈ s, fderivWithin ℝ g (s) x = a x) ∧
      ∀ x ∈ s, fderivWithin ℝ a (s) x = b x := by
  have hAcont : ∀ j, ContinuousOn (A j) (s) :=
    fun j x hx => (hderiv2 j x hx).continuousWithinAt
  have hderivG := hasFDerivWithinAt_convex_of_uniformLimit hconv hclosed hint hderiv1 hAcont hf hA
  have hderivA := hasFDerivWithinAt_convex_of_uniformLimit hconv hclosed hint hderiv2 hBcont hA hB
  have hbcont : ContinuousOn b (s) := hB.continuousOn (Frequently.of_forall hBcont)
  have hs := uniqueDiffOn_convex hconv hint
  have haC1 : ContDiffOn ℝ 1 a (s) := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hs).mpr
    exact ⟨by simp, b,contDiffOn_zero.mpr hbcont,hderivA⟩
  refine ⟨?_,fun x hx => (hderivG x hx).fderivWithin (hs x hx),
    fun x hx => (hderivA x hx).fderivWithin (hs x hx)⟩
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 1) hs).mpr
  exact ⟨by simp,a,haC1,hderivG⟩


lemma contDiffOn_two_convex_of_uniformWithinJets {s : Set E}
    (hconv : Convex ℝ s) (hclosed : IsClosed s) (hint : (interior s).Nonempty)
    {f : ℕ → E → F} {g : E → F} {a : E → E →L[ℝ] F}
    {b : E → E →L[ℝ] (E →L[ℝ] F)}
    (hC2 : ∀ j, ContDiffOn ℝ 2 (f j) (s))
    (hf : TendstoUniformlyOn f g atTop (s))
    (hA : TendstoUniformlyOn (fun j => fderivWithin ℝ (f j) (s)) a atTop (s))
    (hB : TendstoUniformlyOn
      (fun j => fderivWithin ℝ (fderivWithin ℝ (f j) (s)) (s))
      b atTop (s)) :
    ContDiffOn ℝ 2 g (s) ∧
      (∀ x ∈ s, fderivWithin ℝ g (s) x = a x) ∧
      ∀ x ∈ s, fderivWithin ℝ a (s) x = b x := by
  have hs := uniqueDiffOn_convex hconv hint
  have hC1 (j : ℕ) : ContDiffOn ℝ 1 (fderivWithin ℝ (f j) (s)) (s) :=
    (hC2 j).fderivWithin hs (by norm_num)
  apply contDiffOn_two_convex_of_uniformJets hconv hclosed hint _ _ _ hf hA hB
  · intro j x hx
    exact ((hC2 j).differentiableOn (by norm_num) x hx).hasFDerivWithinAt
  · intro j x hx
    exact ((hC1 j).differentiableOn (by norm_num) x hx).hasFDerivWithinAt
  · intro j
    exact (hC1 j).continuousOn_fderivWithin hs (by norm_num)

set_option backward.isDefEq.respectTransparency false
open BallC2Complete

lemma lower_order_holder_jets_on_convex {n : ℕ} {α : ℝ}
    {s : Set (Space n)} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hconv : Convex ℝ s) (hint : (interior s).Nonempty)
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u s) :
    IsHolderOn α u s ∧ ∀ i, IsHolderOn α (firstPartialWithin u s i) s := by
  let N := c2HolderUpToNormOn α u s
  have hN : 0 ≤ N := c2HolderUpToNormOn_nonneg _ _ _
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_convex hconv hint
  constructor
  · have hL : LipschitzOnWith (⟨N,hN⟩ : ℝ≥0) u s := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      change dist (u x) (u y) ≤ N * dist x y
      simpa only [dist_eq_norm, N] using hconv.norm_image_sub_le_of_norm_fderivWithin_le
        (hu.1.differentiableOn (by norm_num))
        (fun x hx => norm_fderivWithin_le_c2HolderUpToNormOn hu hx) hy hx
    exact BallGeometry.holder_of_bounded_lipschitz hα hα1 hu.2.1 hL
  · intro i
    have hdi : ContDiffOn ℝ 1 (firstPartialWithin u s i) s :=
      (hu.1.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
    have hL : LipschitzOnWith (⟨N,hN⟩ : ℝ≥0) (firstPartialWithin u s i) s := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      change dist (firstPartialWithin u s i x) (firstPartialWithin u s i y) ≤ N * dist x y
      simpa only [dist_eq_norm, N] using hconv.norm_image_sub_le_of_norm_fderivWithin_le
        (hdi.differentiableOn (by norm_num))
        (fun x hx => norm_fderivWithin_firstPartial_le_c2HolderUpToNormOn hu hx i) hy hx
    exact BallGeometry.holder_of_bounded_lipschitz hα hα1 (hu.2.2.1 i) hL

lemma lower_order_holderNormOn_le_four_c2HolderUpToNormOn_convex
    {n : ℕ} {α : ℝ} {s : Set (Space n)}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hconv : Convex ℝ s) (hint : (interior s).Nonempty)
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u (s)) :
    holderNormOn α u (s) ≤ 4*c2HolderUpToNormOn α u (s) ∧
      ∀ i, holderNormOn α (firstPartialWithin u (s) i) (s) ≤
        4*c2HolderUpToNormOn α u (s) := by
  let N := c2HolderUpToNormOn α u (s)
  have hN : 0 ≤ N := c2HolderUpToNormOn_nonneg _ _ _
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_convex hconv hint
  constructor
  · have hb : ∀ x ∈ s, ‖u x‖ ≤ N := fun x hx => norm_le_c2HolderUpToNormOn hu hx
    have hl : ∀ x ∈ s, ∀ y ∈ s, ‖u x-u y‖ ≤ N * dist x y := by
      intro x hx y hy
      simpa only [dist_eq_norm] using hconv.norm_image_sub_le_of_norm_fderivWithin_le
        (hu.1.differentiableOn (by norm_num))
        (fun x hx => norm_fderivWithin_le_c2HolderUpToNormOn hu hx) hy hx
    exact (holderNormOn_le_of_bounded_lipschitz hα hα1 hN hN hb hl).trans_eq (by dsimp [N]; ring)
  · intro i
    have hb : ∀ x ∈ s, ‖firstPartialWithin u (s) i x‖ ≤ N :=
      fun x hx => (norm_le_supNormOn (hu.2.2.1 i) hx).trans
        ((c2HolderUpToNormOn_components α u (s)).2.2.1 i)
    have hdi : ContDiffOn ℝ 1 (firstPartialWithin u (s) i) (s) :=
      (hu.1.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
    have hl : ∀ x ∈ s, ∀ y ∈ s,
        ‖firstPartialWithin u (s) i x-firstPartialWithin u (s) i y‖ ≤ N * dist x y := by
      intro x hx y hy
      simpa only [dist_eq_norm] using hconv.norm_image_sub_le_of_norm_fderivWithin_le
        (hdi.differentiableOn (by norm_num))
        (fun x hx => norm_fderivWithin_firstPartial_le_c2HolderUpToNormOn hu hx i) hy hx
    exact (holderNormOn_le_of_bounded_lipschitz hα hα1 hN hN hb hl).trans_eq (by dsimp [N]; ring)


lemma c2HolderUpToNormOn_complete_convex {n : ℕ} {α : ℝ} {s : Set (Space n)}
    (hα : 0 < α) (hα1 : α ≤ 1) (hconv : Convex ℝ s)
    (hcompact : IsCompact s) (hint : (interior s).Nonempty) (u : ℕ → Space n → ℝ)
    (hu : ∀ j, IsC2HolderUpToOn α (u j) (s))
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      c2HolderUpToNormOn α (u j-u k) (s) < ε) :
    ∃ g : Space n → ℝ, IsC2HolderUpToOn α g (s) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, c2HolderUpToNormOn α (u j-g) (s) < ε := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hcompact
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_convex hconv hint
  have hlow (j : ℕ) := lower_order_holder_jets_on_convex hα.le hα1 hconv hint (hu j)
  have hC0 : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, holderNormOn α (u j-u k) s < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hc (ε/4) (by positivity)
    refine ⟨N,fun j hj k hk => ?_⟩
    have hb := (lower_order_holderNormOn_le_four_c2HolderUpToNormOn_convex hα.le hα1 hconv hint
      (isC2HolderUpToOn_sub hs (hu j) (hu k))).1
    have hsmall := hN j hj k hk
    linarith
  obtain ⟨g,hg,hgconv⟩ := BallHolderSpace.holderNormOn_complete hα u (fun j => (hlow j).1) hC0
  have hC1 (i : Fin n) : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      holderNormOn α (firstPartialWithin (u j) s i-firstPartialWithin (u k) s i) s < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hc (ε/4) (by positivity)
    refine ⟨N,fun j hj k hk => ?_⟩
    rw [← holderNormOn_congr (firstPartialWithin_sub hs ((hu j).1.of_le (by norm_num))
      ((hu k).1.of_le (by norm_num)) i)]
    have hb := (lower_order_holderNormOn_le_four_c2HolderUpToNormOn_convex hα.le hα1 hconv hint
      (isC2HolderUpToOn_sub hs (hu j) (hu k))).2 i
    have hsmall := hN j hj k hk
    linarith
  have hFirst (i : Fin n) := BallHolderSpace.holderNormOn_complete hα
    (fun j => firstPartialWithin (u j) s i) (fun j => (hlow j).2 i) (hC1 i)
  choose v1 hv1 hv1conv using hFirst
  have hC2 (i j : Fin n) : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      holderNormOn α (secondPartialWithin (u p) s i j-secondPartialWithin (u q) s i j) s < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hc ε hε
    refine ⟨N,fun p hp q hq => ?_⟩
    rw [← holderNormOn_congr (secondPartialWithin_sub hs (hu p).1 (hu q).1 i j)]
    exact ((c2HolderUpToNormOn_components α (u p-u q) s).2.2.2.2 i j).trans_lt (hN p hp q hq)
  have hSecond (i j : Fin n) := BallHolderSpace.holderNormOn_complete hα
    (fun p => secondPartialWithin (u p) s i j) (fun p => (hu p).2.2.2 i j) (hC2 i j)
  choose v2 hv2 hv2conv using hSecond
  have hU := tendstoUniformlyOn_of_holderNormOn_tendsto (fun j => (hlow j).1) hg hgconv
  have hJets := uniformCauchyWithinJets_of_c2HolderUpToNormOn_cauchy hs hu hc
  obtain ⟨A,hA⟩ := exists_uniform_limit_of_uniformCauchySeqOn hJets.1
  obtain ⟨B,hB⟩ := exists_uniform_limit_of_uniformCauchySeqOn hJets.2
  have hG := contDiffOn_two_convex_of_uniformWithinJets hconv hcompact.isClosed hint
    (fun j => (hu j).1) hU hA hB
  have hfirst (i : Fin n) : EqOn (firstPartialWithin g s i) (v1 i) s := by
    intro x hx
    have hp := (tendstoUniformlyOn_of_holderNormOn_tendsto
      (fun j => (hlow j).2 i) (hv1 i) (hv1conv i)).tendsto_at hx
    have hq : Tendsto (fun j => firstPartialWithin (u j) s i x) atTop (𝓝 (A x (coordinate n i))) :=
      ((ContinuousLinearMap.apply ℝ ℝ (coordinate n i)).continuous.tendsto (A x)).comp (hA.tendsto_at hx)
    have he := tendsto_nhds_unique hq hp
    unfold firstPartialWithin
    rw [hG.2.1 x hx,he]
  have hsecond (i j : Fin n) : EqOn (secondPartialWithin g s i j) (v2 i j) s := by
    intro x hx
    have hp := (tendstoUniformlyOn_of_holderNormOn_tendsto
      (fun p => (hu p).2.2.2 i j) (hv2 i j) (hv2conv i j)).tendsto_at hx
    have hq : Tendsto (fun p => secondPartialWithin (u p) s i j x) atTop
        (𝓝 (B x (coordinate n i) (coordinate n j))) := by
      let L : (Space n →L[ℝ] (Space n →L[ℝ] ℝ)) →L[ℝ] ℝ :=
        (ContinuousLinearMap.apply ℝ ℝ (coordinate n j)).comp
          (ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) (coordinate n i))
      have hh := (L.continuous.tendsto (B x)).comp (hB.tendsto_at hx)
      apply hh.congr'
      exact Eventually.of_forall (fun p => (secondPartialWithin_eq_second_fderivWithin hs (hu p).1 hx i j).symm)
    have he := tendsto_nhds_unique hq hp
    rw [secondPartialWithin_eq_second_fderivWithin hs hG.1 hx i j,
      fderivWithin_congr' hG.2.1 hx,hG.2.2 x hx,he]
  have hgUp : IsC2HolderUpToOn α g s := by
    refine ⟨hG.1,?_,?_,?_⟩
    · obtain ⟨M,H,hM,hH,hb,hh⟩ := hg
      exact ⟨M,hM,hb⟩
    · intro i
      obtain ⟨M,H,hM,hH,hb,hh⟩ := hv1 i
      exact ⟨M,hM,fun x hx => by rw [hfirst i hx]; exact hb x hx⟩
    · intro i j
      exact P201.Elliptic.PoissonSchauder.isHolderOn_congr (hv2 i j) (hsecond i j)
  have hpartial1 (p : ℕ) (i : Fin n) : EqOn (firstPartialWithin (u p-g) s i)
      (firstPartialWithin (u p) s i-v1 i) s := by
    intro x hx
    rw [firstPartialWithin_sub hs ((hu p).1.of_le (by norm_num)) (hgUp.1.of_le (by norm_num)) i hx]
    simp only [Pi.sub_apply,hfirst i hx]
  have hpartial2 (p : ℕ) (i j : Fin n) : EqOn (secondPartialWithin (u p-g) s i j)
      (secondPartialWithin (u p) s i j-v2 i j) s := by
    intro x hx
    rw [secondPartialWithin_sub hs (hu p).1 hgUp.1 i j hx]
    simp only [Pi.sub_apply,hsecond i j hx]
  have hbound (p : ℕ) : c2HolderUpToNormOn α (u p-g) s ≤
      holderNormOn α (u p-g) s +
        (∑ i : Fin n, holderNormOn α (firstPartialWithin (u p) s i-v1 i) s) +
        ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (secondPartialWithin (u p) s i j-v2 i j) s := by
    rw [c2HolderUpToNormOn_eq_holder_sums]
    apply add_le_add
    · apply add_le_add
      · exact le_add_of_nonneg_right (holderSeminormOn_nonneg _ _ _)
      · apply Finset.sum_le_sum
        intro i _
        rw [supNormOn_congr (hpartial1 p i)]
        exact le_add_of_nonneg_right (holderSeminormOn_nonneg _ _ _)
    · apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact le_of_eq (holderNormOn_congr (hpartial2 p i j))
  have hlim0 := tendsto_zero_of_nonneg_bound (fun p => holderNormOn_nonneg α (u p-g) s) hgconv
  have hlim1 (i : Fin n) := tendsto_zero_of_nonneg_bound
    (fun p => holderNormOn_nonneg α (firstPartialWithin (u p) s i-v1 i) s) (hv1conv i)
  have hlim2 (i j : Fin n) := tendsto_zero_of_nonneg_bound
    (fun p => holderNormOn_nonneg α (secondPartialWithin (u p) s i j-v2 i j) s) (hv2conv i j)
  have hlimSum1 := tendsto_finsetSum Finset.univ (fun i _ => hlim1 i)
  have hlimSum2 := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => hlim2 i j))
  have hlimBound : Tendsto (fun p => holderNormOn α (u p-g) s +
      (∑ i : Fin n, holderNormOn α (firstPartialWithin (u p) s i-v1 i) s) +
      ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (secondPartialWithin (u p) s i j-v2 i j) s)
      atTop (𝓝 0) := by simpa using (hlim0.add hlimSum1).add hlimSum2
  have hlim := squeeze_zero (fun p => c2HolderUpToNormOn_nonneg α (u p-g) s) hbound hlimBound
  refine ⟨g,hgUp,?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  exact ⟨N,fun p hp => by
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (c2HolderUpToNormOn_nonneg α (u p-g) s)] using hN p hp⟩

/-- A prescribed pointwise limit of a C²,α-norm Cauchy sequence on a compact
convex set is genuinely C²,α up to its boundary. -/
lemma isC2HolderUpToOn_of_c2HolderUpToNormOn_cauchy_convex
    {n : ℕ} {α : ℝ} {s : Set (Space n)}
    (hα : 0 < α) (hα1 : α ≤ 1) (hconv : Convex ℝ s)
    (hcompact : IsCompact s) (hint : (interior s).Nonempty)
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, IsC2HolderUpToOn α (u j) s)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      c2HolderUpToNormOn α (u j-u k) s < ε)
    (hpoint : ∀ x ∈ s, Tendsto (fun j => u j x) atTop (𝓝 (v x))) :
    IsC2HolderUpToOn α v s := by
  obtain ⟨g,hg,hgconv⟩ := c2HolderUpToNormOn_complete_convex hα hα1 hconv hcompact hint u hu hc
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_convex hconv hint
  apply isC2HolderUpToOn_congr hg
  intro x hx
  have hglim : Tendsto (fun j => u j x) atTop (𝓝 (g x)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hgconv ε hε
    refine ⟨N,fun j hj => ?_⟩
    simpa only [dist_eq_norm,Pi.sub_apply] using
      (norm_le_c2HolderUpToNormOn (isC2HolderUpToOn_sub hs (hu j) hg) hx).trans_lt (hN j hj)
  exact tendsto_nhds_unique (hpoint x hx) hglim

lemma interior_closedBall_inter_nonempty {z y : E} {r ρ : ℝ}
    (hoverlap : (ball z r ∩ ball y ρ).Nonempty) :
    (interior (closedBall z r ∩ closedBall y ρ)).Nonempty := by
  obtain ⟨x,hx,hy⟩ := hoverlap
  exact ⟨x,by rw [interior_inter]; exact ⟨ball_subset_interior_closedBall hx,ball_subset_interior_closedBall hy⟩⟩

lemma uniqueDiffOn_closedBall_inter {z y : E} {r ρ : ℝ}
    (hoverlap : (ball z r ∩ ball y ρ).Nonempty) :
    UniqueDiffOn ℝ (closedBall z r ∩ closedBall y ρ) :=
  uniqueDiffOn_convex ((convex_closedBall z r).inter (convex_closedBall y ρ))
    (interior_closedBall_inter_nonempty hoverlap)

lemma ball_inter_nonempty_of_mem_closedBall {z y : E} {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hy : y ∈ closedBall z r) :
    (ball z r ∩ ball y ρ).Nonempty := by
  have hycl : y ∈ closure (ball z r) := by
    rw [closure_ball z hr.ne']
    exact hy
  obtain ⟨x,hx,hxy⟩ := Metric.mem_closure_iff.mp hycl ρ hρ
  exact ⟨x,hx,by simpa only [mem_ball,dist_comm] using hxy⟩

lemma c2HolderUpToNormOn_complete_closedBall_inter {n : ℕ} {α r ρ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (z y : Space n)
    (hoverlap : (ball z r ∩ ball y ρ).Nonempty) (u : ℕ → Space n → ℝ)
    (hu : ∀ j, IsC2HolderUpToOn α (u j) (closedBall z r ∩ closedBall y ρ))
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      c2HolderUpToNormOn α (u j-u k) (closedBall z r ∩ closedBall y ρ) < ε) :
    ∃ g : Space n → ℝ, IsC2HolderUpToOn α g (closedBall z r ∩ closedBall y ρ) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N,
        c2HolderUpToNormOn α (u j-g) (closedBall z r ∩ closedBall y ρ) < ε :=
  c2HolderUpToNormOn_complete_convex hα hα1
    ((convex_closedBall z r).inter (convex_closedBall y ρ))
    ((isCompact_closedBall z r).inter_right isClosed_closedBall)
    (interior_closedBall_inter_nonempty hoverlap) u hu hc

end ConvexWithinLimit



namespace BallBoundaryLimit

lemma local_upTo_of_global {n : ℕ} {α r : ℝ} {z : Space n} (hr : 0 < r)
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u (closedBall z r)) (U : Domain n) :
    IsC2HolderLocUpToOn α u (ballDomain z r) U := by
  simp only [IsC2HolderLocUpToOn, ballDomain, TopologicalSpace.Opens.coe_mk,
    closure_ball z hr.ne']
  refine ⟨hu.1.mono inter_subset_left,?_⟩
  intro x hx
  obtain ⟨ρ,hρ,hsub⟩ := Metric.isOpen_iff.mp U.isOpen x hx.2
  exact ⟨ρ,hρ,hsub,UpToIntersection.isC2HolderUpToOn_inter_open hu isOpen_ball⟩

/-- Approximants which share the same lift on an outer spherical portion
are Cauchy in the actual C²,α norm on every smaller portion. -/
lemma boundary_control_of_lifted_sequence
    (hboundary : P201Specs.Elliptic.VariableSchauder.LocalBoundaryEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f : Space n → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hcz : ∀ x ∈ closedBall z r, c x ≤ 0)
    {g : ℕ → C(sphere z r,ℝ)} {u : ℕ → Space n → ℝ}
    (hu : ∀ j, IsBallSolution a b c f z r (g j) (u j))
    (hureg : ∀ j, IsC2HolderUpToOn α (u j) (closedBall z r))
    (U V : Domain n) (hVb : Bornology.IsBounded (V : Set (Space n)))
    (hV : closure (V : Set (Space n)) ⊆ U)
    {G : Space n → ℝ}
    (htrace : ∀ j, ∀ ζ : sphere z r, (ζ : Space n) ∈ U → g j ζ = G ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℕ,
      IsC2HolderUpToOn α (u p-u q) (closedBall z r ∩ (V : Set (Space n))) ∧
      c2HolderUpToNormOn α (u p-u q) (closedBall z r ∩ (V : Set (Space n))) ≤
        C * ‖g p-g q‖ := by
  cases n with
  | zero => omega
  | succ m =>
    let T := closedBall z r ∩ (U : Set (Space (m+1)))
    have hcT : CoefficientsHolderOn α a b c T :=
      ⟨fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hc.1 i j) inter_subset_left,
        fun i => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hc.2.1 i) inter_subset_left,
        P201.Elliptic.PoissonSchauder.isHolderOn_mono hc.2.2 inter_subset_left⟩
    let K := coefficientNormOn α a b c (closedBall z r)
    have hK : 0 ≤ K := by
      exact add_nonneg (add_nonneg
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => holderNormOn_nonneg _ _ _)
        (Finset.sum_nonneg fun i _ => holderNormOn_nonneg _ _ _)) (holderNormOn_nonneg _ _ _)
    have hB : HasC2HolderBoundaryOn α (ballDomain z r) U := by
      intro p hp hpU
      exact BallGeometry.ball_hasC2HolderBoundary hα.le hα1.le z hr p hp (mem_univ p)
    obtain ⟨C,hC,hest⟩ := hboundary m α hα hα1 (ballDomain z r) U hB V hVb hV ell K hell hK
    simp only [ballDomain, TopologicalSpace.Opens.coe_mk, closure_ball z hr.ne',
      frontier_ball z hr.ne'] at hest
    refine ⟨C,hC,?_⟩
    intro p q
    have hb : ∀ x ∈ T, ‖(u p-u q) x‖ ≤ ‖g p-g q‖ := by
      intro x hx
      exact ball_solution_boundary_stability hn hr
        (ellipticCoefficients_of_holder hα hell ball_subset_closedBall he hc)
        (fun y hy => hcz y (ball_subset_closedBall hy)) (hu p) (hu q) x hx.1
    have hf0 : IsHolderOn α (fun _ : Space (m+1) => (0:ℝ)) T := isHolderOn_const α 0 T
    have hL : ∀ x ∈ ball z r ∩ (U : Set (Space (m+1))),
        nondivergenceOperator a b c (u p-u q) x = 0 := by
      intro x hx
      have hd := P201.Elliptic.nondivergenceOperator_mul_sub a b c
        (Ω := ballDomain z r) (hu p).1 (hu q).1 1 hx.1
      simpa only [Pi.sub_def,one_mul,(hu p).2.2.1 x hx.1,(hu q).2.2.1 x hx.1,sub_self] using hd
    have hzero : ∀ x ∈ sphere z r ∩ (U : Set (Space (m+1))), (u p-u q) x = 0 := by
      intro x hx
      change u p x-u q x=0
      rw [(hu p).2.2.2 ⟨x,hx.1⟩,(hu q).2.2.2 ⟨x,hx.1⟩,
        htrace p ⟨x,hx.1⟩ hx.2,htrace q ⟨x,hx.1⟩ hx.2,sub_self]
    obtain ⟨hclass,hbound⟩ := hest a b c
      ⟨fun x hx => he.1 x hx.1,fun x hx => he.2 x hx.1⟩ hcT
      (BallContinuousLimit.coefficientNormOn_mono hc inter_subset_left)
      (u p-u q) (fun _ => 0) (fun _ => 0)
      (local_upTo_of_global hr
        (BallC2Complete.isC2HolderUpToOn_sub (BallWithinLimit.uniqueDiffOn_closedBall z hr)
          (hureg p) (hureg q)) U)
      ⟨‖g p-g q‖,norm_nonneg _,hb⟩ hf0 (isC2HolderUpToOn_zero α T) hL hzero
    refine ⟨hclass,hbound.trans ?_⟩
    rw [holderNormOn_zero,c2HolderUpToNormOn_zero,add_zero,add_zero]
    exact mul_le_mul_of_nonneg_left
      (P201.Elliptic.NewtonHessian.supNormOn_le (norm_nonneg _) hb) hC.le

end BallBoundaryLimit






namespace BallLocalApprox

lemma firstPartialWithin_mul {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ 1 u s) (hv : ContDiffOn ℝ 1 v s)
    (i : Fin n) : EqOn (firstPartialWithin (u*v) s i)
      (fun x => firstPartialWithin u s i x*v x+u x*firstPartialWithin v s i x) s := by
  intro x hx
  unfold firstPartialWithin
  rw [fderivWithin_mul (hs x hx) (hu.differentiableOn (by norm_num) x hx)
    (hv.differentiableOn (by norm_num) x hx)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma secondPartialWithin_mul {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ 2 u s) (hv : ContDiffOn ℝ 2 v s)
    (i j : Fin n) : EqOn (secondPartialWithin (u*v) s i j)
      (fun x => secondPartialWithin u s i j x*v x+
        firstPartialWithin u s j x*firstPartialWithin v s i x+
        firstPartialWithin u s i x*firstPartialWithin v s j x+
        u x*secondPartialWithin v s i j x) s := by
  intro x hx
  have hu1 : ContDiffOn ℝ 1 u s := hu.of_le (by norm_num)
  have hv1 : ContDiffOn ℝ 1 v s := hv.of_le (by norm_num)
  have hdu : ContDiffOn ℝ 1 (firstPartialWithin u s j) s :=
    (hu.fderivWithin (m:=1) hs (by norm_num)).clm_apply contDiffOn_const
  have hdv : ContDiffOn ℝ 1 (firstPartialWithin v s j) s :=
    (hv.fderivWithin (m:=1) hs (by norm_num)).clm_apply contDiffOn_const
  unfold secondPartialWithin
  rw [fderivWithin_congr' (firstPartialWithin_mul hs hu1 hv1 j) hx]
  change (fderivWithin ℝ ((firstPartialWithin u s j)*v+u*(firstPartialWithin v s j)) s x) (coordinate n i)=_
  rw [fderivWithin_add (hs x hx)
      ((hdu.differentiableOn (by norm_num) x hx).mul (hv1.differentiableOn (by norm_num) x hx))
      ((hu1.differentiableOn (by norm_num) x hx).mul (hdv.differentiableOn (by norm_num) x hx)),
    fderivWithin_mul (hs x hx) (hdu.differentiableOn (by norm_num) x hx)
      (hv1.differentiableOn (by norm_num) x hx),
    fderivWithin_mul (hs x hx) (hu1.differentiableOn (by norm_num) x hx)
      (hdv.differentiableOn (by norm_num) x hx)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  simp only [firstPartialWithin]
  ring

lemma lower_jets_holder_of_upTo_convex {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (hc : Convex ℝ s)
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u s) :
    IsHolderOn α u s ∧ ∀ i, IsHolderOn α (firstPartialWithin u s i) s :=
  HolderComposition.lower_order_holder_jets_convex hα hα1 hc hs hu

lemma isC2HolderUpToOn_mul_convex {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (hc : Convex ℝ s)
    {u v : Space n → ℝ} (hu : IsC2HolderUpToOn α u s)
    (hv : IsC2HolderUpToOn α v s) : IsC2HolderUpToOn α (u*v) s := by
  obtain ⟨hu0,hu1⟩ := lower_jets_holder_of_upTo_convex hα hα1 hs hc hu
  obtain ⟨hv0,hv1⟩ := lower_jets_holder_of_upTo_convex hα hα1 hs hc hv
  have hbound {f : Space n → ℝ} (hf : IsHolderOn α f s) : IsBoundedOn f s := by
    obtain ⟨M,H,hM,hH,hb,hh⟩ := hf
    exact ⟨M,hM,hb⟩
  refine ⟨hu.1.mul hv.1,hbound (isHolderOn_mul hu0 hv0),?_,?_⟩
  · intro i
    apply hbound
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_add (isHolderOn_mul (hu1 i) hv0) (isHolderOn_mul hu0 (hv1 i)))
    exact firstPartialWithin_mul hs (hu.1.of_le (by norm_num)) (hv.1.of_le (by norm_num)) i
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (isHolderOn_add (isHolderOn_add (isHolderOn_add
        (isHolderOn_mul (hu.2.2.2 i j) hv0)
        (isHolderOn_mul (hu1 j) (hv1 i)))
        (isHolderOn_mul (hu1 i) (hv1 j)))
        (isHolderOn_mul hu0 (hv.2.2.2 i j)))
    exact secondPartialWithin_mul hs hu.1 hv.1 i j

/-- Local C²,α up to a ball boundary can be multiplied by a smooth cutoff
supported strictly in its regularity portion. No finite norm on the portion
is assumed. -/
lemma cutoff_local_lift_upTo {n : ℕ} {α r : ℝ} {z : Space n}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hr : 0 < r)
    (U : Domain n) {G χ : Space n → ℝ}
    (hG : IsC2HolderLocUpToOn α G (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r) U)
    (hχ : ContDiff ℝ ∞ χ) (hχsupport : tsupport χ ⊆ (U : Set (Space n))) :
    IsC2HolderUpToOn α (χ*G) (closedBall z r) := by
  let S : Set (Space n) := closedBall z r
  have hS : UniqueDiffOn ℝ S := BallApprox.uniqueDiffOn_closedBall z hr
  have hχclass : IsC2HolderUpToOn α χ S :=
    BallApprox.smooth_c2HolderUpToOn_closedBall hα hα1 z hr hχ
  have hGlocal : ∀ x ∈ S ∩ (U : Set (Space n)), ∃ δ : ℝ, 0 < δ ∧
      IsC2HolderUpToOn α G (S ∩ ball x δ) := by
    intro x hx
    have hx' : x ∈ closure (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r : Set (Space n)) ∩
        (U : Set (Space n)) := by
      change x ∈ closure (ball z r) ∩ (U : Set (Space n))
      rw [closure_ball z hr.ne']
      exact hx
    obtain ⟨δ,hδ,hδU,hreg⟩ := hG.2 x hx'
    refine ⟨δ,hδ,?_⟩
    change IsC2HolderUpToOn α G (closure (ball z r) ∩ ball x δ) at hreg
    rwa [closure_ball z hr.ne'] at hreg
  have hpatch : ∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧
      IsC2HolderUpToOn α (χ*G) (S ∩ ball x δ) := by
    intro x hx
    by_cases hxU : x ∈ (U : Set (Space n))
    · obtain ⟨δ,hδ,hreg⟩ := hGlocal x ⟨hx,hxU⟩
      exact ⟨δ,hδ,isC2HolderUpToOn_mul_convex hα hα1 (hS.inter isOpen_ball)
        ((convex_closedBall z r).inter (convex_ball x δ))
        (UpToIntersection.isC2HolderUpToOn_inter_open hχclass isOpen_ball) hreg⟩
    · have hxsupport : x ∉ tsupport χ := fun hs => hxU (hχsupport hs)
      obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds hxsupport)
      refine ⟨δ,hδ,isC2HolderUpToOn_congr (isC2HolderUpToOn_zero α (S ∩ ball x δ)) ?_⟩
      intro y hy
      simp only [Pi.mul_apply, image_eq_zero_of_notMem_tsupport (hδsub hy.2),zero_mul]
  have hlocal : P201Specs.Elliptic.WeightedInterpolation.IsLocC2HolderWithinOn α (χ*G) S := by
    refine ⟨?_,hpatch⟩
    intro x hx
    obtain ⟨δ,hδ,hreg⟩ := hpatch x hx
    exact (hreg.1 x ⟨hx,mem_ball_self hδ⟩).mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hδ))))
  obtain ⟨hb,hfirst,hsecond⟩ :=
    P201.Elliptic.WeightedInterpolation.local_within_jet_bounds_on_compact hα
      (isCompact_closedBall z r) Subset.rfl hlocal
  exact ⟨hlocal.1,hb,hfirst,hsecond⟩


lemma exists_smooth_cutoff_one_near_compact {n : ℕ}
    {K U : Set (Space n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : Space n → ℝ) (W : Set (Space n)),
      ContDiff ℝ ∞ χ ∧ IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      (∀ x, χ x ∈ Icc (0:ℝ) 1) ∧ tsupport χ ⊆ U ∧
      (∀ x ∈ W, χ x=1) ∧ HasCompactSupport χ := by
  obtain ⟨W,hW,hKW,hWclU,hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨O,hO,hWclO,hOclU,hOcompact⟩ :=
    exists_open_between_and_isCompact_closure hWcompact hU hWclU
  obtain ⟨χ,hχ,hχrange,hχsupport,hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n:=(⊤ : ℕ∞)) hO isClosed_closure hWclO
  have htsupport : tsupport χ=closure O := by rw [tsupport,hχsupport]
  exact ⟨χ,W,hχ,hW,hKW,(subset_closure.trans hWclU),
    (fun x => hχrange (mem_range_self x)),htsupport ▸ hOclU,
    (fun x hx => (hχone x).mp (subset_closure hx)),
    (by change IsCompact (tsupport χ); rw [htsupport]; exact hOcompact)⟩

/-- Preserve an exact lift on a patch while approximating arbitrary sphere
 data: only the part multiplied by `1-χ` is smoothed. -/
lemma sphere_lift_sequence_eqOn_of_cutoff {n : ℕ} {α r : ℝ} {z : Space n}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hr : 0 < r)
    (g : C(sphere z r,ℝ)) {χ H G : Space n → ℝ} {W : Set (Space n)}
    (hχ : ContDiff ℝ ∞ χ) (hχrange : ∀ x, χ x ∈ Icc (0:ℝ) 1)
    (hH : IsC2HolderUpToOn α H (closedBall z r))
    (hHtrace : ∀ ζ : sphere z r, H ζ = χ ζ * g ζ)
    (hWχ : ∀ x ∈ W, χ x = 1) (hWG : EqOn H G W) :
    ∃ F : ℕ → Space n → ℝ,
      (∀ j, IsC2HolderUpToOn α (F j) (closedBall z r)) ∧
      (∀ j, EqOn (F j) G W) ∧
      (∀ j, ∀ ζ : sphere z r, ‖F j ζ-g ζ‖ < 1 / ((j:ℝ)+1)) := by
  obtain ⟨A,hA,hAg,hAlim⟩ := BallApprox.sphere_smooth_lift_sequence hα hα1 hr g
  let F : ℕ → Space n → ℝ := fun j x => H x+(1-χ x)*A j x
  refine ⟨F,?_,?_,?_⟩
  · intro j
    exact BallLiftAlgebra.isC2HolderUpToOn_add (BallApprox.uniqueDiffOn_closedBall z hr)
      hH (BallApprox.smooth_c2HolderUpToOn_closedBall hα hα1 z hr
        ((contDiff_const.sub hχ).mul (hA j).1))
  · intro j x hx
    change H x+(1-χ x)*A j x=G x
    rw [hWχ x hx,sub_self,zero_mul,add_zero,hWG hx]
  · intro j ζ
    have heq : F j ζ-g ζ=(1-χ ζ)*(A j ζ-g ζ) := by
      dsimp [F]
      rw [hHtrace]
      ring
    rw [heq,norm_mul]
    have hnorm : ‖1-χ ζ‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hχrange ζ).2)]
      linarith [(hχrange ζ).1]
    exact (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_lt (by
      simpa only [one_mul] using hAg j ζ)

/-- Approximate continuous sphere data by global Hölder lifts that all agree
with a single fixed Hölder lift on an open neighborhood of a given compact
subset of the regularity portion. -/
lemma local_sphere_lift_sequence {n : ℕ} {α r : ℝ} {z : Space n}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hr : 0 < r)
    (g : C(sphere z r,ℝ)) (U : Domain n) {G : Space n → ℝ}
    (hG : IsC2HolderLocUpToOn α G (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r) U)
    (hgG : ∀ ζ : sphere z r, (ζ : Space n) ∈ (U : Set (Space n)) → g ζ=G ζ)
    {K : Set (Space n)} (hK : IsCompact K) (hKU : K ⊆ (U : Set (Space n))) :
    ∃ (W : Domain n) (H : Space n → ℝ) (F : ℕ → Space n → ℝ),
      K ⊆ (W : Set (Space n)) ∧ W ≤ U ∧
      IsC2HolderUpToOn α H (closedBall z r) ∧
      EqOn H G (W : Set (Space n)) ∧
      (∀ j, IsC2HolderUpToOn α (F j) (closedBall z r)) ∧
      (∀ j, EqOn (F j) G (W : Set (Space n))) ∧
      (∀ j, EqOn (F j) H (W : Set (Space n))) ∧
      (∀ j, ∀ ζ : sphere z r, ‖F j ζ-g ζ‖ < 1 / ((j:ℝ)+1)) := by
  obtain ⟨χ,W,hχ,hW,hKW,hWU,hχrange,hχsupport,hχone,hχcompact⟩ :=
    exists_smooth_cutoff_one_near_compact hK U.isOpen hKU
  let H : Space n → ℝ := χ*G
  have hH : IsC2HolderUpToOn α H (closedBall z r) :=
    cutoff_local_lift_upTo hα hα1 hr U hG hχ hχsupport
  have hHtrace : ∀ ζ : sphere z r, H ζ=χ ζ*g ζ := by
    intro ζ
    change χ ζ*G ζ=χ ζ*g ζ
    by_cases hχzero : χ ζ=0
    · simp only [hχzero,zero_mul]
    · rw [hgG ζ (hχsupport (subset_tsupport χ hχzero))]
  have hHG : EqOn H G W := by
    intro x hx
    change χ x*G x=G x
    rw [hχone x hx,one_mul]
  obtain ⟨F,hF,hFG,hFerror⟩ := sphere_lift_sequence_eqOn_of_cutoff
    hα hα1 hr g hχ hχrange hH hHtrace hχone hHG
  refine ⟨⟨W,hW⟩,H,F,hKW,hWU,hH,hHG,hF,hFG,?_,hFerror⟩
  intro j x hx
  exact (hFG j hx).trans (hHG hx).symm

lemma local_sphere_lift_sequence_at {n : ℕ} {α r : ℝ} {z p : Space n}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hr : 0 < r)
    (g : C(sphere z r,ℝ)) (U : Domain n) {G : Space n → ℝ}
    (hG : IsC2HolderLocUpToOn α G (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r) U)
    (hgG : ∀ ζ : sphere z r, (ζ : Space n) ∈ (U : Set (Space n)) → g ζ=G ζ)
    (hp : p ∈ (U : Set (Space n))) :
    ∃ (W : Domain n) (H : Space n → ℝ) (F : ℕ → Space n → ℝ),
      p ∈ W ∧ W ≤ U ∧
      IsC2HolderUpToOn α H (closedBall z r) ∧
      EqOn H G (W : Set (Space n)) ∧
      (∀ j, IsC2HolderUpToOn α (F j) (closedBall z r)) ∧
      (∀ j, EqOn (F j) G (W : Set (Space n))) ∧
      (∀ j, EqOn (F j) H (W : Set (Space n))) ∧
      (∀ j, ∀ ζ : sphere z r, ‖F j ζ-g ζ‖ < 1 / ((j:ℝ)+1)) := by
  obtain ⟨W,H,F,hpW,hWU,hH,hHG,hF,hFG,hFH,herr⟩ := local_sphere_lift_sequence
    hα hα1 hr g U hG hgG (K:={p}) isCompact_singleton (singleton_subset_iff.mpr hp)
  exact ⟨W,H,F,hpW (mem_singleton p),hWU,hH,hHG,hF,hFG,hFH,herr⟩

end BallLocalApprox


namespace BallBoundaryLimit

lemma boundary_limit_upTo_on_lens
    (hboundary : P201Specs.Elliptic.VariableSchauder.LocalBoundaryEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {z : Space n} {r : ℝ} (hr : 0 < r)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f : Space n → ℝ} {ell : ℝ} (hell : 0 < ell)
    (he : UniformlyEllipticOn ell a (closedBall z r))
    (hc : CoefficientsHolderOn α a b c (closedBall z r))
    (hcz : ∀ x ∈ closedBall z r, c x ≤ 0)
    {g : ℕ → C(sphere z r,ℝ)} {g₀ : C(sphere z r,ℝ)}
    (hg : Tendsto g atTop (𝓝 g₀))
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hu : ∀ j, IsBallSolution a b c f z r (g j) (u j))
    (hv : IsBallSolution a b c f z r g₀ v)
    (hureg : ∀ j, IsC2HolderUpToOn α (u j) (closedBall z r))
    (U : Domain n) {G : Space n → ℝ}
    (htrace : ∀ j, ∀ ζ : sphere z r, (ζ : Space n) ∈ U → g j ζ = G ζ)
    {p : Space n} {ρ : ℝ} (hρ : 0 < ρ) (hp : p ∈ closedBall z r)
    (houter : closedBall p (2*ρ) ⊆ (U : Set (Space n))) :
    IsC2HolderUpToOn α v (closedBall z r ∩ closedBall p ρ) := by
  let S := closedBall z r ∩ closedBall p ρ
  let T := closedBall z r ∩ ball p (2*ρ)
  have hs : UniqueDiffOn ℝ S := ConvexWithinLimit.uniqueDiffOn_closedBall_inter
    (ConvexWithinLimit.ball_inter_nonempty_of_mem_closedBall hr hρ hp)
  have ht : UniqueDiffOn ℝ T := (BallWithinLimit.uniqueDiffOn_closedBall z hr).inter isOpen_ball
  have hST : S ⊆ T := by
    intro x hx
    exact ⟨hx.1,closedBall_subset_ball (by linarith) hx.2⟩
  have hV : closure (ball p (2*ρ)) ⊆ (U : Set (Space n)) := by
    rw [closure_ball p (by positivity : (2*ρ) ≠ 0)]
    exact houter
  obtain ⟨C,hC,hcontrol⟩ := boundary_control_of_lifted_sequence hboundary hn hα hα1 hr
    hell he hc hcz hu hureg U (ballDomain p (2*ρ)) isBounded_ball hV htrace
  have hclass : ∀ j, IsC2HolderUpToOn α (u j) S := fun j =>
    BallWithinRestriction.isC2HolderUpToOn_mono hs (BallWithinLimit.uniqueDiffOn_closedBall z hr)
      inter_subset_left (hureg j)
  have hcauchy : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      c2HolderUpToNormOn α (u j-u k) S < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hg.cauchySeq (ε/C) (div_pos hε hC)
    refine ⟨N,fun j hj k hk => ?_⟩
    apply (BallWithinRestriction.c2HolderUpToNormOn_mono hs ht hST (hcontrol j k).1).trans_lt
    apply (hcontrol j k).2.trans_lt
    have hdist : ‖g j-g k‖ < ε/C := by simpa only [dist_eq_norm] using hN j hj k hk
    simpa only [mul_comm] using (lt_div_iff₀ hC).mp hdist
  apply ConvexWithinLimit.isC2HolderUpToOn_of_c2HolderUpToNormOn_cauchy_convex hα hα1.le
    ((convex_closedBall z r).inter (convex_closedBall p ρ))
    ((isCompact_closedBall z r).inter_right isClosed_closedBall)
    (ConvexWithinLimit.interior_closedBall_inter_nonempty
      (ConvexWithinLimit.ball_inter_nonempty_of_mem_closedBall hr hρ hp)) hclass hcauchy
  intro x hx
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun j => norm_nonneg _) (fun j =>
    ball_solution_boundary_stability hn hr
      (ellipticCoefficients_of_holder hα hell ball_subset_closedBall he hc)
      (fun y hy => hcz y (ball_subset_closedBall hy)) (hu j) hv x hx.1)
    ((tendsto_iff_norm_sub_tendsto_zero.mp hg))

end BallBoundaryLimit



namespace BallBoundaryLimit
/-- Package uniformly approximating ambient representatives as actual
continuous sphere maps, with convergence in their supremum norm. -/
lemma sphere_maps_of_uniform_lifts {n : ℕ} {z : Space n} {r : ℝ}
    (g : C(sphere z r,ℝ)) {F : ℕ → Space n → ℝ}
    (hF : ∀ j, ContinuousOn (F j) (closedBall z r))
    (herr : ∀ j, ∀ ζ : sphere z r, ‖F j ζ-g ζ‖ < 1/((j:ℝ)+1)) :
    ∃ g' : ℕ → C(sphere z r,ℝ),
      (∀ j ζ, g' j ζ=F j ζ) ∧ Tendsto g' atTop (𝓝 g) := by
  let g' : ℕ → C(sphere z r,ℝ) := fun j =>
    ⟨fun ζ => F j ζ,continuousOn_iff_continuous_domRestrict.mp
      ((hF j).mono sphere_subset_closedBall)⟩
  refine ⟨g',fun _ _ => rfl,?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro ζ
  exact (herr j ζ).le

/-- The local boundary conclusion for arbitrary continuous sphere data
follows from lifted solvability and the full local a priori estimate.
The local lift needs no finite norm on its entire open portion. -/
lemma local_boundary_regularity_of_holder
    (hholder : HolderSolvabilityStatement)
    (hboundary : P201Specs.Elliptic.VariableSchauder.LocalBoundaryEstimateStatement) :
    LocalBoundaryRegularityStatement := by
  intro n hn α hα hα1 z r hr a b c he hc hcz f hf g u hu hureg U G hG htrace V hVb hV
  obtain ⟨ell,hell,he⟩ := he
  let K := coefficientNormOn α a b c (closedBall z r)
  have hK : 0 ≤ K := by
    exact add_nonneg (add_nonneg
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => holderNormOn_nonneg _ _ _)
      (Finset.sum_nonneg fun i _ => holderNormOn_nonneg _ _ _)) (holderNormOn_nonneg _ _ _)
  obtain ⟨C,hC,hsolve⟩ := hholder hn α hα hα1 z r hr ell K hell hK
  let S := closedBall z r
  have hpatch : ∀ p ∈ S ∩ (U : Set (Space n)),
      ∃ ρ : ℝ, 0 < ρ ∧ ball p ρ ⊆ (U : Set (Space n)) ∧
        IsC2HolderUpToOn α u (S ∩ ball p ρ) := by
    intro p hp
    obtain ⟨W,H,F,hpW,hWU,hH,hHG,hF,hFG,hFH,herr⟩ :=
      BallLocalApprox.local_sphere_lift_sequence_at hα.le hα1.le hr g U hG htrace hp.2
    obtain ⟨g',hg'F,hg'lim⟩ := sphere_maps_of_uniform_lifts g
      (fun j => (hF j).1.continuousOn) herr
    have hsol : ∀ j : ℕ, ∃ v : Space n → ℝ, IsLiftedBallSolution α a b c f (F j) z r v := by
      intro j
      obtain ⟨v,hv,hbound,hunique⟩ := hsolve a b c he hc le_rfl hcz f (F j) hf (hF j)
      exact ⟨v,hv⟩
    choose v hv using hsol
    have hvclass : ∀ j, IsBallSolution a b c f z r (g' j) (v j) := by
      intro j
      refine ⟨(hv j).1.1.mono ball_subset_closedBall,(hv j).1.1.continuousOn,(hv j).2.1,?_⟩
      intro ζ
      rw [hg'F]
      exact (hv j).2.2 ζ ζ.property
    have hvtrace : ∀ j, ∀ ζ : sphere z r, (ζ : Space n) ∈ W → g' j ζ = G ζ := by
      intro j ζ hζ
      rw [hg'F]
      exact hFG j hζ
    obtain ⟨ε,hε,hεW⟩ : ∃ ε : ℝ, 0 < ε ∧ closedBall p ε ⊆ (W : Set (Space n)) :=
      Metric.nhds_basis_closedBall.mem_iff.mp (W.isOpen.mem_nhds hpW)
    let ρ := ε/4
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have houter : closedBall p (2*ρ) ⊆ (W : Set (Space n)) :=
      (closedBall_subset_closedBall (by dsimp [ρ]; linarith)).trans hεW
    have hballU : ball p ρ ⊆ (U : Set (Space n)) :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by dsimp [ρ]; linarith))).trans
        (hεW.trans hWU)
    have hreg : IsC2HolderUpToOn α u (S ∩ closedBall p ρ) :=
      boundary_limit_upTo_on_lens hboundary hn hα hα1 hr hell he hc hcz hg'lim
        hvclass hu (fun j => (hv j).1) W hvtrace hρ hp.1 houter
    refine ⟨ρ,hρ,hballU,?_⟩
    exact BallWithinRestriction.isC2HolderUpToOn_mono
      ((BallWithinLimit.uniqueDiffOn_closedBall z hr).inter isOpen_ball)
      (ConvexWithinLimit.uniqueDiffOn_closedBall_inter
        (ConvexWithinLimit.ball_inter_nonempty_of_mem_closedBall hr hρ hp.1))
      (fun x hx => ⟨hx.1,ball_subset_closedBall hx.2⟩) hreg
  have hlocal : P201Specs.Elliptic.WeightedInterpolation.IsLocC2HolderWithinOn α u
      (S ∩ (U : Set (Space n))) := by
    constructor
    · intro p hp
      obtain ⟨ρ,hρ,hρU,hreg⟩ := hpatch p hp
      exact (hreg.1 p ⟨hp.1,mem_ball_self hρ⟩).mono_of_mem_nhdsWithin
        (inter_mem (mem_of_superset self_mem_nhdsWithin inter_subset_left)
          (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ))))
    · intro p hp
      obtain ⟨ρ,hρ,hρU,hreg⟩ := hpatch p hp
      refine ⟨ρ,hρ,?_⟩
      have heq : (S ∩ (U : Set (Space n))) ∩ ball p ρ = S ∩ ball p ρ := by
        ext x
        constructor
        · intro hx; exact ⟨hx.1.1,hx.2⟩
        · intro hx; exact ⟨⟨hx.1,hρU hx.2⟩,hx.2⟩
      rwa [heq]
  have hres := P201.Elliptic.WeightedInterpolation.locally_within_regular_restriction
    (s := S ∩ (U : Set (Space n))) (k := S ∩ closure (V : Set (Space n)))
    (U := (V : Set (Space n))) hα.le
    ((isCompact_closedBall z r).inter_right isClosed_closure)
    (fun x (hx : x ∈ S ∩ closure (V : Set (Space n))) => ⟨hx.1,hV hx.2⟩)
    V.isOpen
    (fun x (hx : x ∈ (S ∩ (U : Set (Space n))) ∩ (V : Set (Space n))) =>
      ⟨hx.1.1,subset_closure hx.2⟩) hlocal
  have heq : (S ∩ (U : Set (Space n))) ∩ (V : Set (Space n)) = S ∩ (V : Set (Space n)) := by
    ext x
    constructor
    · intro hx; exact ⟨hx.1.1,hx.2⟩
    · intro hx; exact ⟨⟨hx.1,hV (subset_closure hx.2)⟩,hx.2⟩
  rwa [heq] at hres

end BallBoundaryLimit


open P201Specs.Elliptic.HalfSpaceLift

namespace KelvinCalculus
lemma uniqueDiffOn_closed_sphere_patch {n : ℕ} {a p : Space n} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hp : p ∈ sphere a r) :
    UniqueDiffOn ℝ (closedBall a r ∩ closedBall p ε) := by
  apply uniqueDiffOn_convex ((convex_closedBall a r).inter (convex_closedBall p ε))
  have hpcl : p ∈ closure (ball a r) := by
    rw [closure_ball a hr.ne']
    exact sphere_subset_closedBall hp
  obtain ⟨x,hxa,hxp⟩ := Metric.mem_closure_iff.mp hpcl ε hε
  have hx : x ∈ ball a r ∩ ball p ε := ⟨hxa,by simpa only [mem_ball,dist_comm] using hxp⟩
  refine ⟨x,?_⟩
  apply interior_mono (inter_subset_inter ball_subset_closedBall ball_subset_closedBall)
  exact mem_interior_iff_mem_nhds.mpr ((isOpen_ball.inter isOpen_ball).mem_nhds hx)

lemma exists_inversion_sphere_patch {n : ℕ} {a p q : Space n} {r R : ℝ}
    (hr : 0 < r) (ha : ‖a‖=r) (hp : p ∈ sphere a r) (hp0 : p ≠ 0)
    (hR : 0 < R) (hq : q=unitInversion p) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ x ∈ closedBall p ε, x ≠ 0) ∧
      MapsTo unitInversion (closedBall a r ∩ closedBall p ε)
        (ball q R ∩ {y | (1:ℝ)/2 ≤ inner ℝ a y}) := by
  have hnhds : {x : Space n | x ≠ 0} ∩ unitInversion ⁻¹' ball q R ∈ 𝓝 p := by
    apply inter_mem (eventually_ne_nhds hp0)
    apply (unitInversion_contDiffAt hp0).continuousAt.preimage_mem_nhds
    rw [hq]
    exact ball_mem_nhds _ hR
  obtain ⟨ε,hε,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhds
  refine ⟨ε,hε,fun x hx => (hsub hx).1,?_⟩
  intro x hx
  refine ⟨(hsub hx.2).2,?_⟩
  exact (unitInversion_mem_closedBall_tangent a hr ha (unitInversion_ne_zero (hsub hx.2).1)).mp
    (by simpa only [unitInversion_involutive] using hx.1)
lemma tangent_ball_poisson_boundary_regular {m : ℕ} (hm : 1 ≤ m) {α r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    (u f : Space (m+1) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball (r • coordinate (m+1) (Fin.last m)) r))
    (hc : ContinuousOn u (closedBall (r • coordinate (m+1) (Fin.last m)) r))
    (hz : ∀ x ∈ sphere (r • coordinate (m+1) (Fin.last m)) r, u x=0)
    (hf : IsHolderOn α f (closedBall (r • coordinate (m+1) (Fin.last m)) r))
    (heq : ∀ x ∈ ball (r • coordinate (m+1) (Fin.last m)) r, P201Specs.laplacian u x=f x)
    {p : Space (m+1)} (hp : p ∈ sphere (r • coordinate (m+1) (Fin.last m)) r)
    (hp0 : p ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ IsC2HolderUpToOn α u
      (closedBall (r • coordinate (m+1) (Fin.last m)) r ∩ closedBall p ε) := by
  let a : Space (m+1) := r • coordinate (m+1) (Fin.last m)
  let c : Space (m+1) := ((1:ℝ)/(2*r)) • coordinate (m+1) (Fin.last m)
  let q := unitInversion p-c
  let D : Domain (m+1) := ⟨{y | c+y ≠ 0},isClosed_singleton.isOpen_compl.preimage (continuous_const.add continuous_id)⟩
  have hn : 2 ≤ m+1 := by omega
  have ha : ‖a‖=r := by
    dsimp [a]
    rw [norm_smul]
    simp [coordinate,P201Specs.coordinate,P102.U4.coordinateVector,Real.norm_of_nonneg hr.le]
  have hcoordnorm : ‖coordinate (m+1) (Fin.last m)‖=1 := by
    simp [coordinate,P201Specs.coordinate,P102.U4.coordinateVector]
  have hcheight : height c=(1:ℝ)/(2*r) := by
    change ((1:ℝ)/(2*r))*height (coordinate (m+1) (Fin.last m)) = _
    rw [P201.Elliptic.HalfSpaceLift.height_coordinate_last,mul_one]
  have hac (y : Space (m+1)) : inner ℝ a (c+y) = (1:ℝ)/2+r*height y := by
    dsimp only [a]
    rw [inner_smul_left]
    simp only [conj_trivial]
    rw [inner_add_right,P201.Elliptic.ConstantSchauder.coordinate_height_inner,
      P201.Elliptic.ConstantSchauder.coordinate_height_inner,hcheight]
    field_simp
    <;> ring
  have hcp : c+q=unitInversion p := by dsimp [q]; abel
  have hcq0 : c+q ≠ 0 := by rw [hcp]; exact unitInversion_ne_zero hp0
  have hq : height q=0 := by
    have hs := (unitInversion_mem_sphere_tangent a hr ha (unitInversion_ne_zero hp0)).mp
      (by simpa only [unitInversion_involutive] using hp)
    rw [← hcp,hac] at hs
    nlinarith
  obtain ⟨δ,hδ,hδD⟩ : ∃ δ : ℝ, 0<δ ∧ closedBall q δ ⊆ (D : Set (Space (m+1))) :=
    Metric.nhds_basis_closedBall.mem_iff.mp (D.isOpen.mem_nhds hcq0)
  let R := δ/2
  have hR : 0<R := by dsimp [R]; positivity
  have h2R : 2*R=δ := by dsimp [R]; ring
  let S := closedBall q δ ∩ closedHalfSpace m
  let T := ball q R ∩ closedHalfSpace m
  let ψ := fun y : Space (m+1) => unitInversion (c+y)
  let v := fun y : Space (m+1) => kelvinTransform u (c+y)
  let F := fun y : Space (m+1) => (‖c+y‖^((m+1)+2))⁻¹*f (ψ y)
  have hψsmooth : ContDiffOn ℝ (3:ℕ) ψ D := by
    intro y hy
    exact (contDiffAt_const.inversion contDiffAt_const
      (contDiffAt_const.add contDiffAt_id) hy).contDiffWithinAt
  have hψmap : MapsTo ψ S (closedBall a r) := by
    intro y hy
    apply (unitInversion_mem_closedBall_tangent a hr ha (hδD hy.1)).mpr
    rw [hac]
    have hyh : 0≤height y := hy.2
    nlinarith
  have hψint : ∀ y ∈ ball q δ ∩ openHalfSpace m, ψ y ∈ ball a r := by
    intro y hy
    apply (unitInversion_mem_ball_tangent a hr ha (hδD (ball_subset_closedBall hy.1))).mpr
    rw [hac]
    have hyh : 0<height y := hy.2
    nlinarith
  have hKu (y : Space (m+1)) (hy : y ∈ ball q δ ∩ openHalfSpace m) :
      ContDiffAt ℝ 2 (kelvinTransform u) (c+y) :=
    kelvinTransform_contDiffAt (hδD (ball_subset_closedBall hy.1))
      ((hu _ (hψint y hy)).contDiffAt (isOpen_ball.mem_nhds (hψint y hy)))
  have hv : ContDiffOn ℝ 2 v (ball q δ ∩ openHalfSpace m) := by
    intro y hy
    exact ((hKu y hy).comp y (contDiffAt_const.add contDiffAt_id)).contDiffWithinAt
  have hvc : ContinuousOn v S := by
    apply ContinuousOn.mul
    · intro y hy
      exact (normInvPow_contDiffAt (hδD hy.1) ((m+1)-2)).continuousAt.comp
        (continuous_const.add continuous_id).continuousAt |>.continuousWithinAt
    · exact hc.comp ((hψsmooth.mono (fun _ hy => hδD hy.1)).continuousOn) hψmap
  have hvz : ∀ y ∈ ball q δ, height y=0 → v y=0 := by
    intro y hy hyh
    have hys : ψ y ∈ sphere a r := by
      apply (unitInversion_mem_sphere_tangent a hr ha (hδD (ball_subset_closedBall hy))).mpr
      rw [hac,hyh,mul_zero,add_zero]
    change (‖c+y‖^((m+1)-2))⁻¹*u (ψ y)=0
    rw [hz _ hys,mul_zero]
  have hScompact : IsCompact S := (isCompact_closedBall q δ).inter_right
    (P201.Elliptic.HalfSpaceLift.isClosed_closedHalfSpace m)
  obtain ⟨M,hM⟩ := hScompact.exists_bound_of_continuousOn hvc
  have hvb : IsBoundedOn v (ball q δ ∩ closedHalfSpace m) :=
    ⟨max M 0,le_max_right _ _,fun y hy =>
      (hM y ⟨ball_subset_closedBall hy.1,hy.2⟩).trans (le_max_left _ _)⟩
  obtain ⟨L,hL⟩ := (hψsmooth.mono hδD).exists_lipschitzOnWith (by norm_num)
    (convex_closedBall q δ) (isCompact_closedBall q δ)
  have hFcomp : IsHolderOn α (f ∘ ψ) S :=
    HolderComposition.isHolderOn_comp_lipschitz hα.le hf hψmap (hL.mono inter_subset_left)
  have hWsm : ContDiffOn ℝ (3:ℕ) (fun y : Space (m+1) => (‖c+y‖^((m+1)+2))⁻¹) D := by
    intro y hy
    exact ((((contDiffAt_norm ℝ hy).pow ((m+1)+2)).inv
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hy))).comp y
        (contDiffAt_const.add contDiffAt_id)).contDiffWithinAt
  have hWreg := smooth_c2HolderUpToOn_compact_convex_on_open hα.le hα1.le hWsm
    (isCompact_closedBall q δ) (convex_closedBall q δ) (BallApprox.uniqueDiffOn_closedBall q hδ) hδD
  have hWh := (HolderComposition.lower_order_holder_jets hα.le hα1.le
    (isCompact_closedBall q δ) (convex_closedBall q δ) (BallApprox.uniqueDiffOn_closedBall q hδ) hWreg).1
  have hFh : IsHolderOn α F S :=
    isHolderOn_mul (P201.Elliptic.PoissonSchauder.isHolderOn_mono hWh inter_subset_left) hFcomp
  have hveq : ∀ y ∈ ball q δ ∩ openHalfSpace m, P201Specs.laplacian v y=F y := by
    intro y hy
    rw [BallReflection.laplacian_comp_add_left c y (hKu y hy),
      laplacian_kelvinTransform hn (hδD (ball_subset_closedBall hy.1))
        ((hu _ (hψint y hy)).contDiffAt (isOpen_ball.mem_nhds (hψint y hy))),heq _ (hψint y hy)]
  obtain ⟨C,hC,hflat⟩ := P201.Elliptic.ConstantSchauder.laplacian_translated_half_ball_estimate m α hα hα1
  obtain ⟨hvreg,hvbound⟩ := hflat q hq R hR v F (by simpa only [h2R] using hv)
    (hvc.mono (by intro y hy; exact ⟨ball_subset_closedBall (by simpa only [h2R] using hy.1),hy.2⟩))
    (by simpa only [h2R] using hvz) (by simpa only [h2R] using hvb)
    (P201.Elliptic.PoissonSchauder.isHolderOn_mono hFh (by
      intro y hy; exact ⟨ball_subset_closedBall (by simpa only [h2R] using hy.1),hy.2⟩))
    (by simpa only [h2R] using hveq)
  have hTconv : Convex ℝ T := (convex_ball q R).inter
    (P201.Elliptic.HalfSpaceLift.convex_closedHalfSpace m)
  have hTdiff : UniqueDiffOn ℝ T := by
    apply uniqueDiffOn_convex hTconv
    let z := q+(R/2) • coordinate (m+1) (Fin.last m)
    have hzball : z ∈ ball q R := by
      change ‖z-q‖ < R
      dsimp [z]
      rw [add_sub_cancel_left,norm_smul]
      rw [hcoordnorm,mul_one,Real.norm_of_nonneg (by positivity : 0≤R/2)]
      linarith
    have hzh : z ∈ openHalfSpace m := by
      change 0<height z
      simp only [z,height,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      change 0<height q+R/2*height (coordinate (m+1) (Fin.last m))
      rw [hq,P201.Elliptic.HalfSpaceLift.height_coordinate_last,zero_add,mul_one]
      positivity
    refine ⟨z,interior_mono (inter_subset_inter Subset.rfl (by intro y hy; change 0≤height y; exact le_of_lt hy)) ?_⟩
    exact mem_interior_iff_mem_nhds.mpr
      ((isOpen_ball.inter (P201.Elliptic.HalfSpaceLift.isOpen_openHalfSpace m)).mem_nhds ⟨hzball,hzh⟩)
  have hφnhds : {x : Space (m+1) | x ≠ 0} ∩
      (fun x => unitInversion x-c) ⁻¹' ball q R ∈ 𝓝 p := by
    apply inter_mem (eventually_ne_nhds hp0)
    apply (((unitInversion_contDiffAt hp0).continuousAt).sub continuous_const.continuousAt).preimage_mem_nhds
    exact ball_mem_nhds _ hR
  obtain ⟨ε,hε,hεsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hφnhds
  let s := closedBall a r ∩ closedBall p ε
  have hscompact : IsCompact s := (isCompact_closedBall a r).inter_right isClosed_closedBall
  have hsconv : Convex ℝ s := (convex_closedBall a r).inter (convex_closedBall p ε)
  have hsdiff : UniqueDiffOn ℝ s := uniqueDiffOn_closed_sphere_patch hr hε hp
  let E : Domain (m+1) := ⟨{x : Space (m+1) | x ≠ 0},isClosed_singleton.isOpen_compl⟩
  have hs0 : s ⊆ (E : Set (Space (m+1))) := fun x hx => (hεsub hx.2).1
  let φ := fun x : Space (m+1) => unitInversion x-c
  have hφsm : ContDiffOn ℝ (3:ℕ) φ E := by
    intro x hx
    exact ((contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx).sub contDiffAt_const).contDiffWithinAt
  have hφcoords (k : Fin (m+1)) : IsC2HolderUpToOn α (fun x => φ x k) s := by
    exact smooth_c2HolderUpToOn_compact_convex_on_open hα.le hα1.le
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m+1) => ℝ) k).contDiff.comp_contDiffOn hφsm)
      hscompact hsconv hsdiff hs0
  have hφmap : MapsTo φ s T := by
    intro x hx
    refine ⟨(hεsub hx.2).2,?_⟩
    have hix := (unitInversion_mem_closedBall_tangent a hr ha
      (unitInversion_ne_zero (hs0 hx))).mp (by simpa only [unitInversion_involutive] using hx.1)
    have hh : inner ℝ a (c+φ x) = (1:ℝ)/2+r*height (φ x) := hac _
    have he : c+φ x=unitInversion x := by dsimp [φ]; abel
    rw [he] at hh
    change 0≤height (φ x)
    nlinarith
  obtain ⟨Lφ,hLφ⟩ := (hφsm.mono hs0).exists_lipschitzOnWith (by norm_num) hsconv hscompact
  have hvcomp : IsC2HolderUpToOn α (v ∘ φ) s :=
    HolderComposition.c2HolderUpToOn_comp_of_lipschitz hα.le hα1.le hsconv hsdiff
      hTconv hTdiff hvreg hφcoords hφmap hLφ
  have hweight : ContDiffOn ℝ (3:ℕ) (fun x : Space (m+1) => (‖x‖^((m+1)-2))⁻¹) E := by
    intro x hx
    exact (((contDiffAt_norm ℝ hx).pow ((m+1)-2)).inv
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))).contDiffWithinAt
  have hweightreg := smooth_c2HolderUpToOn_compact_convex_on_open hα.le hα1.le hweight
    hscompact hsconv hsdiff hs0
  have hreg := HolderComposition.c2HolderUpToOn_mul hα.le hα1.le hscompact hsconv hsdiff
    hweightreg hvcomp
  refine ⟨ε,hε,isC2HolderUpToOn_congr hreg ?_⟩
  intro x hx
  change u x=(‖x‖^((m+1)-2))⁻¹*kelvinTransform u (c+(unitInversion x-c))
  have hxid : c+(unitInversion x-c)=unitInversion x := by abel
  rw [hxid]
  exact (kelvinTransform_involutive u (hs0 hx)).symm

end KelvinCalculus



namespace KelvinCalculus
lemma tangent_ball_poisson_boundary_regular_all_points {m : ℕ} (hm : 1 ≤ m) {α r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    (u f : Space (m+1) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball (r • coordinate (m+1) (Fin.last m)) r))
    (hc : ContinuousOn u (closedBall (r • coordinate (m+1) (Fin.last m)) r))
    (hz : ∀ x ∈ sphere (r • coordinate (m+1) (Fin.last m)) r, u x=0)
    (hf : IsHolderOn α f (closedBall (r • coordinate (m+1) (Fin.last m)) r))
    (heq : ∀ x ∈ ball (r • coordinate (m+1) (Fin.last m)) r, P201Specs.laplacian u x=f x)
    {p : Space (m+1)} (hp : p ∈ sphere (r • coordinate (m+1) (Fin.last m)) r) :
    ∃ ε : ℝ, 0 < ε ∧ IsC2HolderUpToOn α u
      (closedBall (r • coordinate (m+1) (Fin.last m)) r ∩ closedBall p ε) := by
  by_cases hp0 : p ≠ 0
  · exact tangent_ball_poisson_boundary_regular hm hα hα1 hr u f hu hc hz hf heq hp hp0
  · have hp0' : p=0 := not_ne_iff.mp hp0
    subst p
    let a : Space (m+1) := r • coordinate (m+1) (Fin.last m)
    let F := fun x : Space (m+1) => a+a-x
    have hFdef : F=AffineIsometryEquiv.pointReflection ℝ a := by
      funext x
      rw [AffineIsometryEquiv.pointReflection_apply]
      change a+a-x=(a-x)+a
      abel
    have hFiso : Isometry F := by rw [hFdef]; exact AffineIsometryEquiv.isometry _
    have hFinv (x : Space (m+1)) : F (F x)=x := by dsimp [F]; abel
    have hFa : F a=a := by dsimp [F]; abel
    have hFdist (x : Space (m+1)) : dist (F x) a=dist x a := by
      calc
        dist (F x) a=dist (F x) (F a) := by rw [hFa]
        _=dist x a := hFiso.dist_eq _ _
    have hFball : MapsTo F (ball a r) (ball a r) := by
      intro x hx
      simpa only [mem_ball,hFdist] using hx
    have hFclosed : MapsTo F (closedBall a r) (closedBall a r) := by
      intro x hx
      simpa only [mem_closedBall,hFdist] using hx
    have hFsphere : MapsTo F (sphere a r) (sphere a r) := by
      intro x hx
      simpa only [mem_sphere,hFdist] using hx
    have hFsmooth : ContDiff ℝ ∞ F := contDiff_const.sub contDiff_id
    let q := F 0
    have ha0 : a ≠ 0 := by
      apply norm_ne_zero_iff.mp
      change ‖r • coordinate (m+1) (Fin.last m)‖ ≠ 0
      rw [norm_smul]
      simp [coordinate,P201Specs.coordinate,P102.U4.coordinateVector,hr.ne']
    have hq0 : q ≠ 0 := by
      have hqa : q=(2:ℝ) • a := by dsimp [q,F]; module
      rw [hqa]
      exact smul_ne_zero two_ne_zero ha0
    have hq : q ∈ sphere a r := hFsphere hp
    let v := u ∘ F
    let g := f ∘ F
    have hv : ContDiffOn ℝ 2 v (ball a r) := hu.comp (hFsmooth.of_le (by simp)).contDiffOn hFball
    have hvc : ContinuousOn v (closedBall a r) := hc.comp hFsmooth.continuous.continuousOn hFclosed
    have hvz : ∀ x ∈ sphere a r, v x=0 := fun x hx => hz _ (hFsphere hx)
    have hg : IsHolderOn α g (closedBall a r) :=
      HolderComposition.isHolderOn_comp_lipschitz hα.le hf hFclosed hFiso.lipschitzWith.lipschitzOnWith
    have hveq : ∀ x ∈ ball a r, P201Specs.laplacian v x=g x := by
      intro x hx
      have hh := P201.Elliptic.PoissonSchauder.laplacian_affine_on
        ⟨ball a r,isOpen_ball⟩ hu (a+a) (-1) (y := x) (by
          change a+a+(-1:ℝ) • x ∈ ball a r
          simpa only [F,neg_one_smul,← sub_eq_add_neg] using hFball hx)
      have hh' : P201Specs.laplacian v x=P201Specs.laplacian u (F x) := by
        simpa only [v,F,Function.comp_def,neg_one_smul,← sub_eq_add_neg,neg_one_sq,one_mul] using hh
      rw [hh',heq _ (hFball hx)]
      rfl
    obtain ⟨ε,hε,hvreg⟩ := tangent_ball_poisson_boundary_regular hm hα hα1 hr v g hv hvc hvz hg hveq hq hq0
    let s := closedBall a r ∩ closedBall (0 : Space (m+1)) ε
    let t := closedBall a r ∩ closedBall q ε
    have hscompact : IsCompact s := (isCompact_closedBall a r).inter_right isClosed_closedBall
    have hsconv : Convex ℝ s := (convex_closedBall a r).inter (convex_closedBall 0 ε)
    have hsdiff : UniqueDiffOn ℝ s := uniqueDiffOn_closed_sphere_patch hr hε hp
    have htcompact : IsCompact t := (isCompact_closedBall a r).inter_right isClosed_closedBall
    have htconv : Convex ℝ t := (convex_closedBall a r).inter (convex_closedBall q ε)
    have htdiff : UniqueDiffOn ℝ t := uniqueDiffOn_closed_sphere_patch hr hε hq
    have hFcoords (k : Fin (m+1)) : IsC2HolderUpToOn α (fun x => F x k) s :=
      BallApprox.smooth_c2HolderUpToOn_compact_convex hα.le hα1.le
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m+1) => ℝ) k).contDiff.comp hFsmooth)
        hscompact hsconv hsdiff
    have hFmap : MapsTo F s t := by
      intro x hx
      refine ⟨hFclosed hx.1,?_⟩
      change dist (F x) (F 0) ≤ ε
      rw [hFiso.dist_eq]
      exact hx.2
    have hreg := HolderComposition.c2HolderUpToOn_comp hα.le hα1.le hscompact hsconv hsdiff
      htcompact htconv htdiff hvreg hFcoords hFmap
    refine ⟨ε,hε,isC2HolderUpToOn_congr hreg ?_⟩
    intro x hx
    change u x=u (F (F x))
    rw [hFinv]

end KelvinCalculus


/-- Genuine local up-to-boundary regularity near each sphere point, together
with interior Hölder regularity, implies the global closed-ball class. -/
lemma closedBall_upTo_of_spherical_patches {n : ℕ} {α r : ℝ} {z : Space n}
    (hα : 0 ≤ α) (hr : 0 < r) {u : Space n → ℝ}
    (hinterior : IsC2HolderLocOn α u (ballDomain z r))
    (hboundary : ∀ p ∈ sphere z r, ∃ ε : ℝ, 0 < ε ∧
      IsC2HolderUpToOn α u (closedBall z r ∩ closedBall p ε)) :
    IsC2HolderUpToOn α u (closedBall z r) := by
  let S : Set (Space n) := closedBall z r
  have hpatch : ∀ x ∈ S, ∃ ε : ℝ, 0 < ε ∧
      IsC2HolderUpToOn α u (S ∩ ball x ε) := by
    intro x hx
    by_cases hxb : x ∈ ball z r
    · obtain ⟨δ,hδ,hδsub⟩ := Metric.isOpen_iff.mp isOpen_ball x hxb
      have hcsub : closedBall x (δ/2) ⊆ ball z r :=
        (closedBall_subset_ball (by linarith : δ/2<δ)).trans hδsub
      have hholder := P201.Elliptic.WeightedInterpolation.c2HolderOn_of_local_on_compact
        hα (ballDomain z r) (isCompact_closedBall x (δ/2)) hcsub hinterior
      have hbsub : ball x (δ/2) ⊆ ball z r := ball_subset_closedBall.trans hcsub
      have hup : IsC2HolderUpToOn α u (ball x (δ/2)) :=
        isC2HolderUpToOn_of_classical_on_open hbsub hinterior.1 isOpen_ball.uniqueDiffOn
          (P201.Elliptic.PoissonSchauder.c2HolderOn_mono hholder ball_subset_closedBall)
      refine ⟨δ/2,by positivity,?_⟩
      have heq : S ∩ ball x (δ/2)=ball x (δ/2) :=
        inter_eq_right.mpr (hbsub.trans ball_subset_closedBall)
      rwa [heq]
    · have hxSphere : x ∈ sphere z r := by
        apply mem_sphere.mpr
        exact le_antisymm (mem_closedBall.mp hx) (le_of_not_gt (fun h => hxb (mem_ball.mpr h)))
      obtain ⟨ε,hε,hreg⟩ := hboundary x hxSphere
      have hreg' := UpToIntersection.isC2HolderUpToOn_inter_open hreg (isOpen_ball (x:=x) (ε:=ε))
      have heq : (closedBall z r ∩ closedBall x ε) ∩ ball x ε=S ∩ ball x ε := by
        ext y
        constructor
        · intro hy
          exact ⟨hy.1.1,hy.2⟩
        · intro hy
          exact ⟨⟨hy.1,ball_subset_closedBall hy.2⟩,hy.2⟩
      exact ⟨ε,hε,heq ▸ hreg'⟩
  have hlocal : P201Specs.Elliptic.WeightedInterpolation.IsLocC2HolderWithinOn α u S := by
    refine ⟨?_,hpatch⟩
    intro x hx
    obtain ⟨ε,hε,hreg⟩ := hpatch x hx
    exact (hreg.1 x ⟨hx,mem_ball_self hε⟩).mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hε))))
  obtain ⟨hb,hfirst,hsecond⟩ :=
    P201.Elliptic.WeightedInterpolation.local_within_jet_bounds_on_compact hα
      (isCompact_closedBall z r) Subset.rfl hlocal
  exact ⟨hlocal.1,hb,hfirst,hsecond⟩




namespace HolderComposition
lemma c2HolderUpToOn_comp_add_left {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (c : Space n) {u : Space n → ℝ} {s t : Set (Space n)}
    (hs : IsCompact s) (hsconv : Convex ℝ s) (hsdiff : UniqueDiffOn ℝ s)
    (htconv : Convex ℝ t) (htdiff : UniqueDiffOn ℝ t)
    (hu : IsC2HolderUpToOn α u t) (hmap : MapsTo (fun x => c+x) s t) :
    IsC2HolderUpToOn α (fun x => u (c+x)) s := by
  have hcoords (k : Fin n) : IsC2HolderUpToOn α (fun x : Space n => (c+x) k) s := by
    exact smooth_c2HolderUpToOn_compact_convex_on_open hα hα1
      (Ω := ⟨univ,isOpen_univ⟩)
      (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k).contDiff.comp
        (contDiff_const.add contDiff_id)).contDiffOn)
      hs hsconv hsdiff (subset_univ s)
  exact c2HolderUpToOn_comp_of_lipschitz hα hα1 hsconv hsdiff htconv htdiff
    hu hcoords hmap (isometry_add_left c).lipschitzWith.lipschitzOnWith
end HolderComposition
namespace KelvinCalculus
lemma ball_poisson_boundary_regular {m : ℕ} (hm : 1 ≤ m) {α r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    (z : Space (m+1)) (u f : Space (m+1) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball z r)) (hc : ContinuousOn u (closedBall z r))
    (hz : ∀ x ∈ sphere z r, u x=0) (hf : IsHolderOn α f (closedBall z r))
    (heq : ∀ x ∈ ball z r, P201Specs.laplacian u x=f x)
    {p : Space (m+1)} (hp : p ∈ sphere z r) :
    ∃ ε : ℝ, 0 < ε ∧ IsC2HolderUpToOn α u
      (closedBall z r ∩ closedBall p ε) := by
  let a := r • coordinate (m+1) (Fin.last m)
  let c := z-a
  let q := p-c
  let v := fun x => u (c+x)
  let F := fun x => f (c+x)
  have hca : c+a=z := by dsimp [c]; abel
  have hcq : c+q=p := by dsimp [q]; abel
  have hdist (x : Space (m+1)) : dist (c+x) z = dist x a := by
    simpa only [hca] using dist_add_left c x a
  have hmb : MapsTo (fun x => c+x) (ball a r) (ball z r) := by
    intro x hx
    change dist (c+x) z<r
    rwa [hdist]
  have hmc : MapsTo (fun x => c+x) (closedBall a r) (closedBall z r) := by
    intro x hx
    change dist (c+x) z≤r
    rwa [hdist]
  have hms : MapsTo (fun x => c+x) (sphere a r) (sphere z r) := by
    intro x hx
    change dist (c+x) z=r
    rwa [hdist]
  have hv : ContDiffOn ℝ 2 v (ball a r) :=
    hu.comp (contDiff_const.add contDiff_id).contDiffOn hmb
  have hvc : ContinuousOn v (closedBall a r) :=
    hc.comp (continuous_const.add continuous_id).continuousOn hmc
  have hvz : ∀ x ∈ sphere a r, v x=0 := fun x hx => hz _ (hms hx)
  have hF : IsHolderOn α F (closedBall a r) :=
    HolderComposition.isHolderOn_comp_lipschitz hα.le hf hmc
      (isometry_add_left c).lipschitzWith.lipschitzOnWith
  have hveq : ∀ x ∈ ball a r, P201Specs.laplacian v x=F x := by
    intro x hx
    rw [BallReflection.laplacian_comp_add_left c x
      ((hu _ (hmb hx)).contDiffAt (isOpen_ball.mem_nhds (hmb hx)))]
    exact heq _ (hmb hx)
  have hq : q ∈ sphere a r := by
    change dist q a=r
    rw [← hdist,hcq]
    exact hp
  obtain ⟨ε,hε,hreg⟩ := tangent_ball_poisson_boundary_regular_all_points hm hα hα1 hr v F hv hvc hvz hF hveq hq
  let s := closedBall z r ∩ closedBall p ε
  let t := closedBall a r ∩ closedBall q ε
  have hs : IsCompact s := (isCompact_closedBall z r).inter_right isClosed_closedBall
  have hsconv : Convex ℝ s := (convex_closedBall z r).inter (convex_closedBall p ε)
  have hsdiff : UniqueDiffOn ℝ s := uniqueDiffOn_closed_sphere_patch hr hε hp
  have htconv : Convex ℝ t := (convex_closedBall a r).inter (convex_closedBall q ε)
  have htdiff : UniqueDiffOn ℝ t := uniqueDiffOn_closed_sphere_patch hr hε hq
  have hbackdist (x : Space (m+1)) : dist (-c+x) a=dist x z := by
    simpa only [add_neg_cancel_left] using (hdist (-c+x)).symm
  have hbackdistq (x : Space (m+1)) : dist (-c+x) q=dist x p := by
    simpa only [add_neg_cancel_left,hcq] using (dist_add_left c (-c+x) q).symm
  have hback : MapsTo (fun x => -c+x) s t := by
    intro x hx
    exact ⟨by change dist (-c+x) a≤r; rw [hbackdist]; exact hx.1,
      by change dist (-c+x) q≤ε; rw [hbackdistq]; exact hx.2⟩
  have hup := HolderComposition.c2HolderUpToOn_comp_add_left hα.le hα1.le (-c)
    hs hsconv hsdiff htconv htdiff hreg hback
  refine ⟨ε,hε,isC2HolderUpToOn_congr hup ?_⟩
  intro x hx
  change u x=u (c+(-c+x))
  rw [add_neg_cancel_left]
end KelvinCalculus

lemma laplacian_ball_zero_trace_upTo {n : ℕ} (hn : 2 ≤ n)
    {α r : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) (hr : 0 < r) (f : Space n → ℝ)
    (hf : IsHolderOn α f (closedBall z r)) (u : Space n → ℝ)
    (hu : IsBallSolution (fun _ i j => if i=j then 1 else 0)
      (fun _ => 0) (fun _ => 0) f z r 0 u)
    (hinterior : IsC2HolderLocOn α u (ballDomain z r)) :
    IsC2HolderUpToOn α u (closedBall z r) := by
  cases n with
  | zero => omega
  | succ m =>
    have hm : 1 ≤ m := by omega
    apply closedBall_upTo_of_spherical_patches hα.le hr hinterior
    intro p hp
    apply KelvinCalculus.ball_poisson_boundary_regular hm hα hα1 hr z u f hu.1 hu.2.1
      (fun x hx => hu.2.2.2 (⟨x,hx⟩ : sphere z r)) hf _ hp
    intro x hx
    exact (nondivergenceOperator_identity u x).symm.trans (hu.2.2.1 x hx)


/-- The actual zero-trace Laplacian is onto in every positive dimension.
The interval is integrated directly; higher dimensions use the constructed
classical solution and the proved Kelvin/flat-boundary upgrade. -/
lemma laplacian_ball_operator_surjective
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (z : Space n) {r : ℝ} (hr : 0 < r) :
    Function.Surjective (BallBanachX.ballOperatorCLM z hr hα
      (identity_coefficientsHolderOn α (closedBall z r))) := by
  by_cases hn1 : n=1
  · subst n
    exact BallBanachX.laplacian_interval_operator_surjective hα hα1 z hr
  · exact BallBanachX.laplacian_operator_surjective_of_upTo_regularity hn hα hα1 z hr
      (fun f hf u hu hint => laplacian_ball_zero_trace_upTo (by omega) hα hα1 z hr f hf u hu hint)

/-- Conditional derivation of the original lifted Hölder solvability
statement. The three full frozen a priori statements are explicit parameters
in the required order; no original closed target is declared here. -/
theorem holder_solvability_conditional
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    (_hinterior : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    (_hboundary : P201Specs.Elliptic.VariableSchauder.LocalBoundaryEstimateStatement) :
    HolderSolvabilityStatement := by
  apply BallContinuity.holder_solvability_of_laplacian_surjective hglobal
  intro n hn α hα hα1 z r hr
  exact laplacian_ball_operator_surjective hn hα hα1 z hr

/-- Continuous sphere data, with the original local interior regularity,
equation and closed-ball uniqueness, under the exact ordered premises. -/
theorem continuous_solvability_conditional
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    (hinterior : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    (hboundary : P201Specs.Elliptic.VariableSchauder.LocalBoundaryEstimateStatement) :
    ContinuousSolvabilityStatement :=
  BallContinuousLimit.continuous_solvability_of_holder
    (holder_solvability_conditional hglobal hinterior hboundary) hinterior

/-- The original local spherical-boundary conclusion, with only a local
lift hypothesis, under the exact ordered frozen a priori statements. -/
theorem local_boundary_regularity_conditional
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    (hinterior : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    (hboundary : P201Specs.Elliptic.VariableSchauder.LocalBoundaryEstimateStatement) :
    LocalBoundaryRegularityStatement :=
  BallBoundaryLimit.local_boundary_regularity_of_holder
    (holder_solvability_conditional hglobal hinterior hboundary) hboundary


end P201.Elliptic.BallSchauderSolvability

theorem _root_.«P201».«Elliptic».«BallSchauderSolvability».«continuous_solvability» : _root_.«P201Specs».«Elliptic».«BallSchauderSolvability».«ContinuousSolvabilityStatement» :=
  @_root_.«P201».«Elliptic».«BallSchauderSolvability».«continuous_solvability_conditional» (@_root_.«P201».«Elliptic».«VariableSchauder».«global_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«interior_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«local_boundary_estimate»)
theorem _root_.«P201».«Elliptic».«BallSchauderSolvability».«holder_solvability» : _root_.«P201Specs».«Elliptic».«BallSchauderSolvability».«HolderSolvabilityStatement» :=
  @_root_.«P201».«Elliptic».«BallSchauderSolvability».«holder_solvability_conditional» (@_root_.«P201».«Elliptic».«VariableSchauder».«global_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«interior_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«local_boundary_estimate»)
theorem _root_.«P201».«Elliptic».«BallSchauderSolvability».«local_boundary_regularity» : _root_.«P201Specs».«Elliptic».«BallSchauderSolvability».«LocalBoundaryRegularityStatement» :=
  @_root_.«P201».«Elliptic».«BallSchauderSolvability».«local_boundary_regularity_conditional» (@_root_.«P201».«Elliptic».«VariableSchauder».«global_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«interior_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«local_boundary_estimate»)
