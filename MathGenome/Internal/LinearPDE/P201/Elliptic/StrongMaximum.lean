import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.StrongMaximum
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set TopologicalSpace Metric Filter
open scoped ContDiff RealInnerProductSpace Topology
namespace P201.Elliptic
open P201Specs.Elliptic
attribute [local instance] Matrix.seminormedAddCommGroup

@[simp] theorem firstPartial_const_sub {n : ℕ} (u : P201Specs.Space n → ℝ)
    (M : ℝ) (i : Fin n) (x : P201Specs.Space n) :
    firstPartial (fun y => M - u y) i x = -firstPartial u i x := by
  simp [firstPartial, fderiv_const_sub]

@[simp] theorem secondPartial_const_sub {n : ℕ} (u : P201Specs.Space n → ℝ)
    (M : ℝ) (i j : Fin n) (x : P201Specs.Space n) :
    secondPartial (fun y => M - u y) i j x = -secondPartial u i j x := by
  have he : firstPartial (fun y => M - u y) j = fun y => -firstPartial u j y :=
    funext (firstPartial_const_sub u M j)
  simp only [secondPartial, he, firstPartial, fderiv_fun_neg,
    neg_apply]
  rfl

/-- This identity needs no global differentiability assumptions: the derivative
operations commute with subtraction of a constant even at their default values. -/
theorem nondivergenceOperator_const_sub {n : ℕ}
    (a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : P201Specs.Space n → P201Specs.Space n) (c u : P201Specs.Space n → ℝ)
    (M : ℝ) (x : P201Specs.Space n) :
    nondivergenceOperator a b c (fun y => M - u y) x =
      c x * M - nondivergenceOperator a b c u x := by
  simp only [nondivergenceOperator, secondPartial_const_sub, firstPartial_const_sub,
    mul_neg, Finset.sum_neg_distrib]
  ring

/-- First derivatives retain one degree of interior regularity. -/
theorem firstPartial_contDiffOn {n : ℕ} {Ω : P201Specs.Domain n}
    {u : P201Specs.Space n → ℝ} (hu : ContDiffOn ℝ 2 u (Ω : Set _)) (i : Fin n) :
    ContDiffOn ℝ 1 (firstPartial u i) (Ω : Set _) := by
  exact (hu.fderiv_of_isOpen Ω.isOpen (by norm_num)).clm_apply contDiffOn_const

theorem firstPartial_mul_sub {n : ℕ} {Ω : P201Specs.Domain n}
    {u v : P201Specs.Space n → ℝ} (hu : ContDiffOn ℝ 2 u (Ω : Set _))
    (hv : ContDiffOn ℝ 2 v (Ω : Set _)) (ε : ℝ) (i : Fin n)
    {x : P201Specs.Space n} (hx : x ∈ (Ω : Set _)) :
    firstPartial (fun y => ε * u y - v y) i x =
      ε * firstPartial u i x - firstPartial v i x := by
  have hu' := (hu.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
  have hv' := (hv.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
  simp [firstPartial, fderiv_fun_sub (hu'.const_mul ε) hv', fderiv_const_mul hu']

theorem secondPartial_mul_sub {n : ℕ} {Ω : P201Specs.Domain n}
    {u v : P201Specs.Space n → ℝ} (hu : ContDiffOn ℝ 2 u (Ω : Set _))
    (hv : ContDiffOn ℝ 2 v (Ω : Set _)) (ε : ℝ) (i j : Fin n)
    {x : P201Specs.Space n} (hx : x ∈ (Ω : Set _)) :
    secondPartial (fun y => ε * u y - v y) i j x =
      ε * secondPartial u i j x - secondPartial v i j x := by
  have he : firstPartial (fun y => ε * u y - v y) j =ᶠ[nhds x]
      (fun y => ε * firstPartial u j y - firstPartial v j y) := by
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact firstPartial_mul_sub hu hv ε j hy
  have hu' := ((firstPartial_contDiffOn hu j).contDiffAt
    (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
  have hv' := ((firstPartial_contDiffOn hv j).contDiffAt
    (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
  change fderiv ℝ (firstPartial (fun y => ε * u y - v y) j) x _ = _
  rw [he.fderiv_eq]
  simp only [
    fderiv_fun_sub (hu'.const_mul ε) hv', fderiv_const_mul hu',
    sub_apply, smul_apply, smul_eq_mul]
  rfl

theorem nondivergenceOperator_mul_sub {n : ℕ} {Ω : P201Specs.Domain n}
    (a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : P201Specs.Space n → P201Specs.Space n) (c : P201Specs.Space n → ℝ)
    {u v : P201Specs.Space n → ℝ} (hu : ContDiffOn ℝ 2 u (Ω : Set _))
    (hv : ContDiffOn ℝ 2 v (Ω : Set _)) (ε : ℝ)
    {x : P201Specs.Space n} (hx : x ∈ (Ω : Set _)) :
    nondivergenceOperator a b c (fun y => ε * u y - v y) x =
      ε * nondivergenceOperator a b c u x - nondivergenceOperator a b c v x := by
  simp only [nondivergenceOperator, secondPartial_mul_sub hu hv ε _ _ hx,
    firstPartial_mul_sub hu hv ε _ hx, mul_sub, Finset.sum_sub_distrib]
  simp_rw [show ∀ (p q : ℝ), p * (ε * q) = ε * (p * q) from fun p q => by ring]
  simp only [← Finset.mul_sum]
  ring


/-- The reduction w=M-u retains precisely the sign condition needed by the
source: either M≥0 and c≤0, or c=0 without a restriction on M. -/
theorem maximum_defect_supersolution {n : ℕ}
    (Ω : P201Specs.Domain n)
    (a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : P201Specs.Space n → P201Specs.Space n) (c u : P201Specs.Space n → ℝ)
    (M : ℝ)
    (hLu : ∀ x ∈ (Ω : Set _), 0 ≤ nondivergenceOperator a b c u x)
    (hM : (0 ≤ M ∧ ∀ x ∈ (Ω : Set _), c x ≤ 0) ∨
      (∀ x ∈ (Ω : Set _), c x = 0)) :
    ∀ x ∈ (Ω : Set _), nondivergenceOperator a b c (fun y => M - u y) x ≤ 0 := by
  intro x hx
  rw [nondivergenceOperator_const_sub]
  have hcM : c x * M ≤ 0 := by
    rcases hM with ⟨hM, hc⟩ | hc
    · exact mul_nonpos_of_nonpos_of_nonneg (hc x hx) hM
    · simp [hc x hx]
  linarith [hLu x hx]

/-- A continuous nonnegative function on a connected open set, with both a zero
and a positive value, has a strictly positive ball tangent to its zero set.
The entire closed ball lies in the original open set. This is purely local
metric geometry and uses no regularity of the boundary of the original set. -/
theorem exists_positive_tangent_ball {E : Type*} [MetricSpace E] [ProperSpace E]
    {Ω : Set E} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    {w : E → ℝ} (hw : ContinuousOn w Ω)
    (hnonneg : ∀ x ∈ Ω, 0 ≤ w x)
    (hzero : ∃ x ∈ Ω, w x = 0) (hpos : ∃ x ∈ Ω, 0 < w x) :
    ∃ (y z : E) (R : ℝ), 0 < R ∧ closedBall y R ⊆ Ω ∧
      z ∈ sphere y R ∧ w z = 0 ∧ ∀ x ∈ ball y R, 0 < w x := by
  let P : Set E := {x | x ∈ Ω ∧ 0 < w x}
  have hP : IsOpen P := hw.isOpen_inter_preimage hΩ isOpen_Ioi
  have hPne : (Ω ∩ P).Nonempty := by
    obtain ⟨x, hx, hwx⟩ := hpos
    exact ⟨x, hx, hx, hwx⟩
  have hp : ∃ p ∈ Ω, p ∈ closure P ∧ w p = 0 := by
    by_contra h
    have hclosed : closure P ∩ Ω ⊆ P := by
      intro x hx
      refine ⟨hx.2, ?_⟩
      have hne : w x ≠ 0 := by
        intro hx0
        exact h ⟨x, hx.2, hx.1, hx0⟩
      exact lt_of_le_of_ne (hnonneg x hx.2) (Ne.symm hne)
    have hsub : Ω ⊆ P := hconn.subset_of_closure_inter_subset hP hPne hclosed
    obtain ⟨x, hx, hx0⟩ := hzero
    have hxp := (hsub hx).2
    linarith
  obtain ⟨p, hpΩ, hpcl, hp0⟩ := hp
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp hΩ p hpΩ
  have hpclose : (ball p (δ / 4) ∩ P).Nonempty :=
    mem_closure_iff_nhds.mp hpcl _ (ball_mem_nhds p (by linarith))
  obtain ⟨y, hyp, hyΩ, hypos⟩ := hpclose
  have hyp' : dist y p < δ / 4 := mem_ball.mp hyp
  let K : Set E := closedBall p (δ / 2)
  have hKΩ : K ⊆ Ω := by
    intro x hx
    apply hδΩ
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith))
  let Z : Set E := {x | x ∈ K ∧ w x = 0}
  have hZcompact : IsCompact Z := by
    exact (isCompact_closedBall p (δ / 2)).of_isClosed_subset
      (isClosed_closedBall.isClosed_eq (hw.mono hKΩ) continuousOn_const)
      (fun _ hx => hx.1)
  have hpZ : p ∈ Z := ⟨mem_closedBall_self (by linarith), hp0⟩
  obtain ⟨z, hzZ, hzmin⟩ := hZcompact.exists_isMinOn ⟨p, hpZ⟩
    (continuous_const.dist continuous_id).continuousOn
  let R := dist y z
  have hRle : R ≤ dist y p := hzmin hpZ
  have hR : 0 < R := by
    apply dist_pos.mpr
    intro hyz
    have := hzZ.2
    rw [← hyz] at this
    linarith
  have hballK : closedBall y R ⊆ K := by
    intro x hx
    have hdist := dist_triangle x y p
    have hxy : dist x y ≤ R := mem_closedBall.mp hx
    exact mem_closedBall.mpr (by linarith)
  refine ⟨y, z, R, hR, hballK.trans hKΩ, ?_, hzZ.2, ?_⟩
  · exact mem_sphere.mpr (dist_comm z y)
  · intro x hx
    have hxK : x ∈ K := hballK (ball_subset_closedBall hx)
    have hxΩ : x ∈ Ω := hKΩ hxK
    have hx0 : w x ≠ 0 := by
      intro hx0
      have hmin : R ≤ dist y x := hzmin ⟨hxK, hx0⟩
      have hlt : dist y x < R := by simpa [dist_comm] using mem_ball.mp hx
      linarith
    exact lt_of_le_of_ne (hnonneg x hxΩ) (Ne.symm hx0)

/-- Restriction to an interior open subdomain preserves the same ellipticity
constant, without introducing bounds at its boundary. -/
theorem ellipticCoefficients_mono {n : ℕ} {Ω D : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c : P201Specs.Space n → ℝ}
    (h : EllipticCoefficients Ω a b c) (hD : (D : Set (P201Specs.Space n)) ⊆ (Ω : Set (P201Specs.Space n))) :
    EllipticCoefficients D a b c := by
  refine ⟨h.1.mono hD, h.2.1.mono hD, h.2.2.1.mono hD, ?_, ?_⟩
  · intro x hx
    exact h.2.2.2.1 x (hD hx)
  · obtain ⟨ell, hell, hbound⟩ := h.2.2.2.2
    exact ⟨ell, hell, fun x hx => hbound x (hD hx)⟩

/-- The elementary large-parameter step in the Gaussian barrier estimate. -/
theorem exists_positive_quadratic_parameter {A B C : ℝ} (hA : 0 < A) (hC : 0 ≤ C) :
    ∃ k : ℝ, 0 < k ∧ 0 < A * k ^ 2 - B * k - C := by
  obtain ⟨k, hk⟩ := exists_gt (max 1 ((B + C + 1) / A))
  have hk1 : 1 < k := (le_max_left _ _).trans_lt hk
  have hk0 : 0 < k := lt_trans zero_lt_one hk1
  have hka : B + C + 1 < k * A :=
    (div_lt_iff₀ hA).mp ((le_max_right _ _).trans_lt hk)
  have hmul := mul_pos (sub_pos.mpr hka) hk0
  have hCk := mul_nonneg hC (sub_nonneg.mpr hk1.le)
  refine ⟨k, hk0, ?_⟩
  nlinarith

/-- Interior continuity supplies exactly the bounds used by a local Gaussian
barrier; the compact set must be contained in the open domain. -/
theorem coefficients_bounded_on_compact {n : ℕ} {Ω : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c)
    {K : Set (P201Specs.Space n)} (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set _)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K,
      (∀ i j, |a x i j| ≤ C) ∧ (∀ i, |b x i| ≤ C) ∧ |c x| ≤ C := by
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hcoeff.1.mono hKΩ)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hcoeff.2.1.mono hKΩ)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hcoeff.2.2.1.mono hKΩ)
  let C := max 0 (max A (max B D))
  have hAC : A ≤ C := (le_max_left A _).trans (le_max_right 0 _)
  have hBC : B ≤ C := (le_max_left B D).trans
    ((le_max_right A _).trans (le_max_right 0 _))
  have hDC : D ≤ C := (le_max_right B D).trans
    ((le_max_right A _).trans (le_max_right 0 _))
  refine ⟨C, le_max_left 0 _, ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact (Matrix.norm_entry_le_entrywise_sup_norm (a x)).trans ((hA x hx).trans hAC)
  · intro i
    exact (PiLp.norm_apply_le (b x) i).trans ((hB x hx).trans hBC)
  · exact (hD x hx).trans hDC

/-- A comparison on the closed ball implies comparison of inward derivatives
at a contact point. The tangent-cone theorem avoids assuming an extension of
the comparison across the sphere. -/
theorem inward_derivative_ge_of_ball_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w ψ : E → ℝ} {y z : E} {R ε : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ closedBall y R)
    (hw : DifferentiableAt ℝ w z) (hψ : DifferentiableAt ℝ ψ z)
    (hcontact : w z = ε * ψ z)
    (hcomp : ∀ x ∈ closedBall y R, ε * ψ x ≤ w x) :
    ε * fderiv ℝ ψ z (y - z) ≤ fderiv ℝ w z (y - z) := by
  have hmin : IsMinOn (fun x => w x - ε * ψ x) (closedBall y R) z := by
    intro x hx
    dsimp
    rw [hcontact]
    linarith [hcomp x hx]
  have htangent : y - z ∈ posTangentConeAt (closedBall y R) z :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_closedBall y R).segment_subset hz (mem_closedBall_self hR))
  have hf := hw.hasFDerivAt.sub (hψ.hasFDerivAt.const_mul ε)
  have hnonneg := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt htangent
  change 0 ≤ fderiv ℝ w z (y - z) - ε * fderiv ℝ ψ z (y - z) at hnonneg
  linarith

/-- A positive continuous function on a compact set dominates a small multiple
of any function bounded above by one. This chooses the inner-ball comparison
constant without any quantitative positivity assumption on w. -/
theorem exists_positive_comparison_factor
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    (hKne : K.Nonempty) {w ψ : E → ℝ} (hw : ContinuousOn w K)
    (hwpos : ∀ x ∈ K, 0 < w x) (hψ : ∀ x ∈ K, ψ x ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε * ψ x ≤ w x := by
  obtain ⟨z, hz, hzmin⟩ := hK.exists_isMinOn hKne hw
  refine ⟨w z, hwpos z hz, ?_⟩
  intro x hx
  calc
    w z * ψ x ≤ w z * 1 := mul_le_mul_of_nonneg_left (hψ x hx) (hwpos z hz).le
    _ = w z := mul_one _
    _ ≤ w x := hzmin hx

/-- The Gaussian barrier with the source normalization. -/
def gaussianBarrier {n : ℕ} (y : P201Specs.Space n) (R k : ℝ) (x : P201Specs.Space n) : ℝ :=
  Real.exp (-k * ‖x-y‖^2) - Real.exp (-k * R^2)

theorem gaussianBarrier_contDiff {n : ℕ} (y : P201Specs.Space n) (R k : ℝ) :
    ContDiff ℝ ⊤ (gaussianBarrier y R k) := by
  unfold gaussianBarrier
  have hnorm : ContDiff ℝ ⊤ (fun x : P201Specs.Space n => ‖x-y‖^2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  exact (contDiff_const.mul hnorm).exp.sub contDiff_const

theorem gaussian_hasFDerivAt {n : ℕ} (y x : P201Specs.Space n) (k : ℝ) :
    HasFDerivAt (fun t => Real.exp (-k * ‖t-y‖^2))
      (Real.exp (-k * ‖x-y‖^2) • (-k • (2 • innerSL ℝ (x-y)))) x := by
  convert (((hasFDerivAt_id x).sub_const y).norm_sq.const_mul (-k)).exp using 1 <;>
    simp

theorem gaussianBarrier_fderiv {n : ℕ} (y x v : P201Specs.Space n) (R k : ℝ) :
    fderiv ℝ (gaussianBarrier y R k) x v =
      -2*k * ⟪x-y, v⟫ * Real.exp (-k * ‖x-y‖^2) := by
  change fderiv ℝ (fun t => Real.exp (-k * ‖t-y‖^2) - Real.exp (-k*R^2)) x v = _
  rw [fderiv_sub_const, (gaussian_hasFDerivAt y x k).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

theorem gaussianBarrier_firstPartial {n : ℕ} (y x : P201Specs.Space n)
    (R k : ℝ) (i : Fin n) :
    firstPartial (gaussianBarrier y R k) i x =
      -2*k * (x i-y i) * Real.exp (-k * ‖x-y‖^2) := by
  rw [firstPartial, gaussianBarrier_fderiv]
  simp only [P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.inner_basisFun_real, PiLp.sub_apply]

theorem gaussianBarrier_secondPartial {n : ℕ} (y x : P201Specs.Space n)
    (R k : ℝ) (i j : Fin n) :
    secondPartial (gaussianBarrier y R k) i j x =
      (4*k^2*(x i-y i)*(x j-y j) - 2*k*(if i=j then 1 else 0)) *
        Real.exp (-k * ‖x-y‖^2) := by
  have he : firstPartial (gaussianBarrier y R k) j =
      (fun x => -2*k * ⟪x-y, P201Specs.coordinate n j⟫ * Real.exp (-k * ‖x-y‖^2)) := by
    funext t
    rw [firstPartial, gaussianBarrier_fderiv]
  rw [secondPartial, he, firstPartial]
  have hlin := (((hasFDerivAt_id x).sub_const y).inner ℝ (hasFDerivAt_const (P201Specs.coordinate n j) x)).const_mul (-2*k)
  have hh : HasFDerivAt (fun t => -2*k * ⟪t-y, P201Specs.coordinate n j⟫ * Real.exp (-k*‖t-y‖^2)) _ x :=
    hlin.mul (gaussian_hasFDerivAt y x k)
  rw [hh.fderiv]
  simp only [smul_apply, add_apply, innerSL_apply_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply, inner_zero_right, zero_add,
    P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.inner_basisFun_real, PiLp.sub_apply, smul_eq_mul,
    id_eq]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  simp only [eq_comm (a := j) (b := i)]
  split_ifs with h
  · subst i; ring
  · ring


/-- The one-dimensional second derivative test, from the mean value theorem. -/
theorem second_derivative_nonpos_of_local_max {F G : ℝ → ℝ} {D : ℝ}
    (hmax : IsLocalMax F 0)
    (hF : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt F (G t) t)
    (hG : HasDerivAt G D 0) : D ≤ 0 := by
  by_contra hn
  have hD : 0 < D := lt_of_not_ge hn
  have hG0 : G 0 = 0 := hmax.hasDerivAt_eq_zero (hF.self_of_nhds)
  have hs := hG.tendsto_slope.eventually (eventually_gt_nhds hD)
  have hs' : ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 → 0 < slope G 0 t := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using hs
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp (hF.and (hmax.and hs'))
  have hI : Icc (0 : ℝ) (δ / 2) ⊆ ball 0 δ := by
    intro t ht
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  have hc : ContinuousOn F (Icc 0 (δ/2)) := by
    intro t ht
    exact (hbound (by simpa [mem_ball] using hI ht)).1.continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Ioo 0 (δ/2), HasDerivAt F (G t) t := by
    intro t ht
    exact (hbound (by simpa [mem_ball] using hI ⟨ht.1.le, ht.2.le⟩)).1
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope F G (by linarith : 0 < δ/2) hc hd
  have htball := hI ⟨ht.1.le, ht.2.le⟩
  have hgpos := (hbound (by simpa [mem_ball] using htball)).2.2 (ne_of_gt ht.1)
  have hgpos' : 0 < G t := by
    simpa only [slope_def_field, hG0, sub_zero, div_pos_iff_of_pos_right ht.1] using hgpos
  have hfmax : F (δ / 2) ≤ F 0 := (hbound (by simpa [mem_ball] using hI ⟨by linarith, le_rfl⟩)).2.1
  have hfquot : (F (δ / 2) - F 0) / (δ / 2 - 0) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hfmax) (by linarith)
  linarith


section MatrixFactor
open scoped MatrixOrder

theorem matrix_posSemidef_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : ∃ B : Matrix (Fin n) (Fin n) ℝ, A = B.transpose * B := by
  let B := CFC.sqrt A
  have hB := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  refine ⟨B, ?_⟩
  have he : B.transpose = B := by
    ext i j
    simpa using congrArg (fun M => M i j) hB.eq
  rw [he, ← pow_two]
  exact (CFC.sq_sqrt A hA.nonneg).symm

theorem bilinear_coordinates {n : ℕ}
    (H : P201Specs.Space n →L[ℝ] P201Specs.Space n →L[ℝ] ℝ)
    (v : P201Specs.Space n) :
    H v v = ∑ i, ∑ j, v i * v j * H (P201Specs.coordinate n i) (P201Specs.coordinate n j) := by
  have he := congrArg₂ (fun a b => H a b)
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
  rw [he]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    EuclideanSpace.basisFun_repr, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  change v j * (v i * H _ _) = _
  simp only [P201Specs.coordinate, P102.U4.coordinateVector]
  ring

theorem elliptic_contraction_nonpos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef)
    (H : P201Specs.Space n →L[ℝ] P201Specs.Space n →L[ℝ] ℝ)
    (hH : ∀ v, H v v ≤ 0) :
    (∑ i, ∑ j, A i j * H (P201Specs.coordinate n i) (P201Specs.coordinate n j)) ≤ 0 := by
  obtain ⟨B, rfl⟩ := matrix_posSemidef_factor hA
  have hH' (k : Fin n) : (∑ i, ∑ j, B k i * B k j * H (P201Specs.coordinate n i) (P201Specs.coordinate n j)) ≤ 0 := by
    simpa only [bilinear_coordinates] using hH (WithLp.toLp 2 (fun i => B k i))
  have he : (∑ i, ∑ j, (B.transpose * B) i j * H (P201Specs.coordinate n i) (P201Specs.coordinate n j)) =
      ∑ k, ∑ i, ∑ j, B k i * B k j * H (P201Specs.coordinate n i) (P201Specs.coordinate n j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [he]
  exact Finset.sum_nonpos fun k _ => hH' k


end MatrixFactor

theorem hessian_nonpos_at_local_max {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    {x : E} (hx : x ∈ Ω) (hmax : IsLocalMax u x) (v : E) :
    fderiv ℝ (fderiv ℝ u) x v v ≤ 0 := by
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hline0 : x + (0 : ℝ) • v = x := by simp
  have hlinecont : ContinuousAt (fun t : ℝ => x + t • v) 0 := (hline 0).continuousAt
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ Ω := by
    apply hlinecont.preimage_mem_nhds
    simpa using hΩ.mem_nhds hx
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_of_isOpen (m := 1) hΩ (by norm_num)).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
  apply second_derivative_nonpos_of_local_max
    (F := fun t : ℝ => u (x + t • v)) (G := fun t : ℝ => fderiv ℝ u (x+t•v) v)
  · have hm : IsLocalMax u (x + (0 : ℝ) • v) := by simpa using hmax
    simpa only [Function.comp_def] using hm.comp_continuous (g := fun t : ℝ => x+t•v) (b := 0) hlinecont
  · filter_upwards [hmem] with t ht
    exact ((hu.contDiffAt (hΩ.mem_nhds ht)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hline t)
  · have hh := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hline 0) hline0.symm
    simpa using hh.clm_apply (hasDerivAt_const 0 v)


theorem gaussianBarrier_le_one {n : ℕ} (y x : P201Specs.Space n) (R k : ℝ) (hk : 0 < k) :
    gaussianBarrier y R k x ≤ 1 := by
  have he : Real.exp (-k * ‖x-y‖^2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (sq_nonneg _))
  unfold gaussianBarrier
  linarith [Real.exp_pos (-k * R^2)]

theorem gaussianBarrier_eq_zero_of_mem_sphere {n : ℕ} (y z : P201Specs.Space n) (R k : ℝ)
    (hz : z ∈ sphere y R) : gaussianBarrier y R k z = 0 := by
  have hnorm : ‖z-y‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hz
  simp [gaussianBarrier, hnorm]

theorem gaussianBarrier_inward_derivative_pos {n : ℕ} (y z : P201Specs.Space n) (R k : ℝ)
    (hR : 0 < R) (hk : 0 < k) (hz : z ∈ sphere y R) :
    0 < fderiv ℝ (gaussianBarrier y R k) z (y-z) := by
  rw [gaussianBarrier_fderiv]
  have hnorm : ‖z-y‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hz
  rw [show y-z = -(z-y) by abel, inner_neg_right, real_inner_self_eq_norm_sq, hnorm]
  apply mul_pos
  · nlinarith [sq_pos_of_pos hR]
  · exact Real.exp_pos _

theorem nonneg_on_closedBall_of_pos_on_ball {n : ℕ} {Ω : P201Specs.Domain n} {w : P201Specs.Space n → ℝ}
    {y : P201Specs.Space n} {R : ℝ} (hR : 0 < R)
    (hball : closedBall y R ⊆ (Ω : Set _)) (hw : ContinuousOn w (Ω : Set _))
    (hpos : ∀ x ∈ ball y R, 0 < w x) : ∀ x ∈ closedBall y R, 0 ≤ w x := by
  have hwcl : ContinuousOn w (closure (ball y R)) := by
    rw [closure_ball y hR.ne']
    exact hw.mono hball
  intro x hx
  apply le_on_closure (fun x hx => (hpos x hx).le) continuousOn_const hwcl
  simpa [closure_ball y hR.ne'] using hx


theorem secondPartial_eq_hessian {n : ℕ} {Ω : P201Specs.Domain n}
    {u : P201Specs.Space n → ℝ} (hu : ContDiffOn ℝ 2 u (Ω : Set _))
    {x : P201Specs.Space n} (hx : x ∈ (Ω : Set _)) (i j : Fin n) :
    secondPartial u i j x =
      fderiv ℝ (fderiv ℝ u) x (P201Specs.coordinate n i) (P201Specs.coordinate n j) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_of_isOpen (m := 1) Ω.isOpen (by norm_num)).contDiffAt
      (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
  change fderiv ℝ (fun y => fderiv ℝ u y (P201Specs.coordinate n j)) x _ = _
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const (P201Specs.coordinate n j) x)).fderiv]
  simp

theorem ellipticCoefficients_posSemidef {n : ℕ} {Ω : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c)
    {x : P201Specs.Space n} (hx : x ∈ (Ω : Set _)) :
    (a x).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact (hcoeff.2.2.2.1 x hx i j).symm
  · intro v
    obtain ⟨ell, hell, hbound⟩ := hcoeff.2.2.2.2
    have hb := hbound x hx (WithLp.toLp 2 v)
    have hzero : 0 ≤ ell * ‖WithLp.toLp 2 v‖ ^ 2 := mul_nonneg hell.le (sq_nonneg _)
    have hv : 0 ≤ ∑ i, ∑ j, a x i j * v i * v j := hzero.trans hb
    simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum,
      mul_left_comm, mul_comm, mul_assoc] using hv

theorem nondivergenceOperator_nonpos_at_positive_local_max {n : ℕ}
    {Ω : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c u : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c)
    (hc : ∀ x ∈ (Ω : Set _), c x ≤ 0)
    (hu : ContDiffOn ℝ 2 u (Ω : Set _))
    {x : P201Specs.Space n} (hx : x ∈ (Ω : Set _))
    (hmax : IsLocalMax u x) (hpos : 0 ≤ u x) :
    nondivergenceOperator a b c u x ≤ 0 := by
  have hH := elliptic_contraction_nonpos (ellipticCoefficients_posSemidef hcoeff hx)
    (fderiv ℝ (fderiv ℝ u) x) (hessian_nonpos_at_local_max Ω.isOpen hu hx hmax)
  have hprincipal : (∑ i, ∑ j, a x i j * secondPartial u i j x) ≤ 0 := by
    simpa only [secondPartial_eq_hessian hu hx] using hH
  have hgradient : ∀ i, firstPartial u i x = 0 := by
    intro i
    simp only [firstPartial, hmax.fderiv_eq_zero, zero_apply]
  unfold nondivergenceOperator
  simp only [hgradient, mul_zero, Finset.sum_const_zero, add_zero]
  exact add_nonpos hprincipal (mul_nonpos_of_nonpos_of_nonneg (hc x hx) hpos)

/-- A strict subsolution controlled on an inner ball and the outer sphere is
nonpositive on the full closed ball. Only interior C² regularity is used. -/
theorem strictMaximum_closedBall_nonpos {n : ℕ}
    {Ω : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c f : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c)
    (hc : ∀ x ∈ (Ω : Set _), c x ≤ 0)
    (hf : ContDiffOn ℝ 2 f (Ω : Set _))
    {y : P201Specs.Space n} {R r : ℝ}
    (hball : closedBall y R ⊆ (Ω : Set _))
    (hinner : ∀ x ∈ closedBall y r, f x ≤ 0)
    (houter : ∀ x ∈ sphere y R, f x ≤ 0)
    (hLf : ∀ x ∈ ball y R, r < dist x y →
      0 < nondivergenceOperator a b c f x) :
    ∀ x ∈ closedBall y R, f x ≤ 0 := by
  intro x hx
  by_contra hn
  have hxpos : 0 < f x := lt_of_not_ge hn
  obtain ⟨z, hz, hzmax⟩ := (isCompact_closedBall y R).exists_isMaxOn
    ⟨x, hx⟩ (hf.continuousOn.mono hball)
  have hzpos : 0 < f z := hxpos.trans_le (hzmax hx)
  have hzoff : dist z y ≠ R := by
    intro hdist
    exact (houter z (mem_sphere.mpr hdist)).not_gt hzpos
  have hzlt : dist z y < R := lt_of_le_of_ne (mem_closedBall.mp hz) hzoff
  have hzball : z ∈ ball y R := mem_ball.mpr hzlt
  have hzinner : r < dist z y := by
    by_contra h
    exact (hinner z (mem_closedBall.mpr (le_of_not_gt h))).not_gt hzpos
  have hlocal : IsLocalMax f z :=
    hzmax.isLocalMax (Filter.mem_of_superset (isOpen_ball.mem_nhds hzball)
      ball_subset_closedBall)
  exact (nondivergenceOperator_nonpos_at_positive_local_max hcoeff hc hf
    (hball hz) hlocal hzpos.le).not_gt (hLf z hzball hzinner)


theorem gaussianBarrier_operator_expansion {n : ℕ}
    (a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : P201Specs.Space n → P201Specs.Space n) (c : P201Specs.Space n → ℝ)
    (y x : P201Specs.Space n) (R k : ℝ) :
    nondivergenceOperator a b c (gaussianBarrier y R k) x =
      Real.exp (-k * ‖x-y‖^2) *
        (4*k^2 * (∑ i, ∑ j, a x i j * (x i-y i) * (x j-y j)) -
          2*k * (∑ i, a x i i) - 2*k * (∑ i, b x i * (x i-y i))) +
        c x * gaussianBarrier y R k x := by
  unfold nondivergenceOperator
  simp only [gaussianBarrier_secondPartial, gaussianBarrier_firstPartial]
  congr 1
  simp only [Finset.mul_sum]
  have hfirst : (∑ i, ∑ j,
      a x i j * ((4*k^2*(x i-y i)*(x j-y j)-2*k*(if i=j then 1 else 0))*
        Real.exp (-k*‖x-y‖^2))) =
      ∑ i, ∑ j, (Real.exp (-k*‖x-y‖^2)* (4*k^2*(a x i j*(x i-y i)*(x j-y j))) -
        Real.exp (-k*‖x-y‖^2)*(2*k*(a x i j*(if i=j then 1 else 0)))) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfirst]
  simp only [Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  have hb : (∑ i, b x i * (-2*k*(x i-y i)*Real.exp (-k*‖x-y‖^2))) =
      -(∑ i, Real.exp (-k*‖x-y‖^2)*(2*k*(b x i*(x i-y i)))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hb]
  conv_rhs =>
    rw [mul_sub, mul_sub]
    simp only [Finset.mul_sum]
  ring

theorem exists_gaussianBarrier_strict {n : ℕ} {Ω : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c)
    {y : P201Specs.Space n} {R : ℝ} (hR : 0 < R)
    (hball : closedBall y R ⊆ (Ω : Set (P201Specs.Space n))) :
    ∃ k : ℝ, 0 < k ∧ ∀ x : P201Specs.Space n,
      R/2 < dist x y → dist x y < R →
        0 < nondivergenceOperator a b c (gaussianBarrier y R k) x := by
  obtain ⟨C, hC, hbound⟩ := coefficients_bounded_on_compact hcoeff
    (isCompact_closedBall y R) hball
  obtain ⟨ell, hell, hellbound⟩ := hcoeff.2.2.2.2
  have hA : 0 < 4*ell*(R/2)^2 := by positivity
  obtain ⟨k, hk, hparam⟩ := exists_positive_quadratic_parameter
    (B := 2*(n:ℝ)*C + 2*(n:ℝ)*C*R) hA hC
  refine ⟨k, hk, ?_⟩
  intro x hxinner hxouter
  have hxball : x ∈ closedBall y R := mem_closedBall.mpr hxouter.le
  have hxΩ := hball hxball
  obtain ⟨ha, hb, hc⟩ := hbound x hxball
  have hxnorm : ‖x-y‖ < R := by simpa [dist_eq_norm] using hxouter
  have hxinorm : R/2 < ‖x-y‖ := by simpa [dist_eq_norm] using hxinner
  have htrace : (∑ i, a x i i) ≤ (n:ℝ)*C := by
    calc
      (∑ i, a x i i) ≤ ∑ _i : Fin n, C := by
        apply Finset.sum_le_sum
        intro i _
        exact (le_abs_self _).trans (ha i i)
      _ = (n:ℝ)*C := by simp
  have hdrift : (∑ i, b x i * (x i-y i)) ≤ (n:ℝ)*C*R := by
    calc
      (∑ i, b x i * (x i-y i)) ≤ ∑ _i : Fin n, C*R := by
        apply Finset.sum_le_sum
        intro i _
        have hcoord : |x i-y i| ≤ R := by
          calc
            |x i-y i| = ‖(x-y) i‖ := by simp
            _ ≤ ‖x-y‖ := PiLp.norm_apply_le _ _
            _ ≤ R := hxnorm.le
        calc
          b x i * (x i-y i) ≤ |b x i * (x i-y i)| := le_abs_self _
          _ = |b x i| * |x i-y i| := abs_mul _ _
          _ ≤ C*R := mul_le_mul (hb i) hcoord (abs_nonneg _) hC
      _ = (n:ℝ)*C*R := by simp [mul_assoc]
  have hQ : ell*(R/2)^2 ≤ ∑ i, ∑ j, a x i j * (x i-y i) * (x j-y j) := by
    have hsq : (R/2)^2 ≤ ‖x-y‖^2 := by nlinarith [norm_nonneg (x-y)]
    exact (mul_le_mul_of_nonneg_left hsq hell.le).trans
      (by simpa only [PiLp.sub_apply] using hellbound x hxΩ (x-y))
  let E : ℝ := Real.exp (-k*‖x-y‖^2)
  have hE : 0 < E := Real.exp_pos _
  have hψnonneg : 0 ≤ gaussianBarrier y R k x := by
    unfold gaussianBarrier
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    have hsq : ‖x-y‖^2 ≤ R^2 := by nlinarith [norm_nonneg (x-y)]
    exact mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hk.le)
  have hψle : gaussianBarrier y R k x ≤ E := by
    dsimp [gaussianBarrier, E]
    linarith [Real.exp_pos (-k*R^2)]
  have hcψ : -C*E ≤ c x * gaussianBarrier y R k x := by
    have hcLower : -C ≤ c x := (abs_le.mp hc).1
    calc
      -C*E ≤ -C*gaussianBarrier y R k x :=
        mul_le_mul_of_nonpos_left hψle (neg_nonpos.mpr hC)
      _ ≤ c x*gaussianBarrier y R k x :=
        mul_le_mul_of_nonneg_right hcLower hψnonneg
  have hmain : 4*ell*(R/2)^2*k^2 - (2*(n:ℝ)*C+2*(n:ℝ)*C*R)*k-C ≤
      4*k^2*(∑ i, ∑ j, a x i j*(x i-y i)*(x j-y j)) -
        2*k*(∑ i, a x i i)-2*k*(∑ i, b x i*(x i-y i))-C := by
    have hq := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 4*k^2 by positivity)
    have ht := mul_le_mul_of_nonneg_left htrace (show 0 ≤ 2*k by positivity)
    have hd := mul_le_mul_of_nonneg_left hdrift (show 0 ≤ 2*k by positivity)
    nlinarith
  rw [gaussianBarrier_operator_expansion]
  change 0 < E*(4*k^2*(∑ i, ∑ j, a x i j*(x i-y i)*(x j-y j))-
      2*k*(∑ i, a x i i)-2*k*(∑ i, b x i*(x i-y i))) +
    c x*gaussianBarrier y R k x
  calc
    0 < E*(4*ell*(R/2)^2*k^2-(2*(n:ℝ)*C+2*(n:ℝ)*C*R)*k-C) := mul_pos hE hparam
    _ ≤ E*(4*k^2*(∑ i, ∑ j, a x i j*(x i-y i)*(x j-y j))-
      2*k*(∑ i, a x i i)-2*k*(∑ i, b x i*(x i-y i))-C) :=
        mul_le_mul_of_nonneg_left hmain hE.le
    _ ≤ E*(4*k^2*(∑ i, ∑ j, a x i j*(x i-y i)*(x j-y j))-
      2*k*(∑ i, a x i i)-2*k*(∑ i, b x i*(x i-y i))) +
        c x*gaussianBarrier y R k x := by nlinarith [hcψ]


/-- The local Gaussian annulus barrier gives a positive inward derivative.
The full closed ball is inside Ω, so interior continuity provides all
coefficient bounds needed by the barrier. -/
theorem tangentBall_inward_derivative_pos {n : ℕ} (_hn : 1 ≤ n)
    {Ω : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c w : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c)
    (hc : ∀ x ∈ (Ω : Set _), c x ≤ 0)
    (hw : ContDiffOn ℝ 2 w (Ω : Set _))
    (hLw : ∀ x ∈ (Ω : Set _), nondivergenceOperator a b c w x ≤ 0)
    {y z : P201Specs.Space n} {R : ℝ} (hR : 0 < R)
    (hball : closedBall y R ⊆ (Ω : Set _)) (hz : z ∈ sphere y R)
    (hwz : w z = 0) (hpos : ∀ x ∈ ball y R, 0 < w x) :
    0 < fderiv ℝ w z (y - z) := by
  obtain ⟨k, hk, hLψ⟩ := exists_gaussianBarrier_strict hcoeff hR hball
  let ψ := gaussianBarrier y R k
  have hψ : ContDiffOn ℝ 2 ψ (Ω : Set _) :=
    (gaussianBarrier_contDiff y R k).contDiffOn.of_le (by simp)
  have hinner : closedBall y (R/2) ⊆ ball y R := by
    intro x hx
    exact mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by linarith))
  have hinnerΩ : closedBall y (R/2) ⊆ (Ω : Set _) :=
    hinner.trans (ball_subset_closedBall.trans hball)
  obtain ⟨ε, hε, hεcomp⟩ := exists_positive_comparison_factor
    (ψ := ψ) (isCompact_closedBall y (R/2))
    ⟨y, mem_closedBall_self (by linarith)⟩
    (hw.continuousOn.mono hinnerΩ) (fun x hx => hpos x (hinner hx))
    (fun x _hx => gaussianBarrier_le_one y x R k hk)
  have hwclosed := nonneg_on_closedBall_of_pos_on_ball hR hball hw.continuousOn hpos
  have hf : ContDiffOn ℝ 2 (fun x => ε * ψ x - w x) (Ω : Set _) :=
    (contDiffOn_const.mul hψ).sub hw
  have hcomp : ∀ x ∈ closedBall y R, ε * ψ x ≤ w x := by
    have hcompare := strictMaximum_closedBall_nonpos hcoeff hc hf hball
      (r := R/2)
      (fun x hx => sub_nonpos.mpr (hεcomp x hx))
      (fun x hx => by
        have hψx : ψ x = 0 := gaussianBarrier_eq_zero_of_mem_sphere y x R k hx
        simp only [hψx, mul_zero, zero_sub, neg_nonpos]
        exact hwclosed x (sphere_subset_closedBall hx))
      (fun x hx hxinner => by
        rw [nondivergenceOperator_mul_sub a b c hψ hw ε (hball (ball_subset_closedBall hx))]
        have hp := mul_pos hε (hLψ x hxinner (mem_ball.mp hx))
        linarith [hLw x (hball (ball_subset_closedBall hx))])
    intro x hx
    exact sub_nonpos.mp (hcompare x hx)
  have hzclosed := sphere_subset_closedBall hz
  have hzΩ := hball hzclosed
  have hw' := (hw.contDiffAt (Ω.isOpen.mem_nhds hzΩ)).differentiableAt (by norm_num)
  have hψ' := (hψ.contDiffAt (Ω.isOpen.mem_nhds hzΩ)).differentiableAt (by norm_num)
  have hcontact : w z = ε * ψ z := by
    rw [hwz, show ψ z = 0 from gaussianBarrier_eq_zero_of_mem_sphere y z R k hz, mul_zero]
  have hderiv := inward_derivative_ge_of_ball_comparison hR.le hzclosed hw' hψ'
    hcontact hcomp
  exact (mul_pos hε (gaussianBarrier_inward_derivative_pos y z R k hR hk hz)).trans_le hderiv

/-- The strong minimum principle follows from connectedness and the local
interior-ball barrier, with no regularity assumption on the domain boundary. -/
theorem strongMinimum {n : ℕ} (hn : 1 ≤ n)
    {Ω : P201Specs.Domain n} (hconn : IsPreconnected (Ω : Set (P201Specs.Space n)))
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c w : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c)
    (hc : ∀ x ∈ (Ω : Set _), c x ≤ 0)
    (hw : ContDiffOn ℝ 2 w (Ω : Set _))
    (hLw : ∀ x ∈ (Ω : Set _), nondivergenceOperator a b c w x ≤ 0)
    (hnonneg : ∀ x ∈ (Ω : Set _), 0 ≤ w x)
    (hzero : ∃ x ∈ (Ω : Set _), w x = 0) :
    ∀ x ∈ (Ω : Set _), w x = 0 := by
  intro x hx
  by_contra hne
  have hxpos : 0 < w x := lt_of_le_of_ne (hnonneg x hx) (Ne.symm hne)
  obtain ⟨y, z, R, hR, hball, hz, hwz, hpos⟩ := exists_positive_tangent_ball
    Ω.isOpen hconn hw.continuousOn hnonneg hzero ⟨x, hx, hxpos⟩
  have hzΩ : z ∈ (Ω : Set _) := hball (sphere_subset_closedBall hz)
  have hzmin : IsLocalMin w z := by
    filter_upwards [Ω.isOpen.mem_nhds hzΩ] with t ht
    simpa [hwz] using hnonneg t ht
  have hslope := tangentBall_inward_derivative_pos hn hcoeff hc hw hLw hR hball hz hwz hpos
  rw [hzmin.fderiv_eq_zero] at hslope
  simp at hslope

/-- Strong maximum principle under the exact source hypotheses. -/
theorem strongMaximum : P201Specs.Elliptic.strongMaximumStatement := by
  intro n hn Ω _hbounded hconn a b c u hcoeff hc hu _hclosure hLu x₀ hx₀ hM hmax x hx
  have hdefect := maximum_defect_supersolution Ω a b c u (u x₀) hLu (Or.inl ⟨hM, hc⟩)
  have hzero := strongMinimum hn hconn.isPreconnected hcoeff hc
    (contDiffOn_const.sub hu) hdefect
    (fun y hy => sub_nonneg.mpr (hmax y hy)) ⟨x₀, hx₀, sub_self _⟩ x hx
  linarith

/-- The zero-order-free version retains maxima of arbitrary sign. -/
theorem strongMaximumZeroOrderFree : P201Specs.Elliptic.strongMaximumZeroOrderFreeStatement := by
  intro n hn Ω _hbounded hconn a b c u hcoeff hc hu _hclosure hLu x₀ hx₀ hmax x hx
  have hdefect := maximum_defect_supersolution Ω a b c u (u x₀) hLu (Or.inr hc)
  have hcneg : ∀ y ∈ (Ω : Set _), c y ≤ 0 := fun y hy => le_of_eq (hc y hy)
  have hzero := strongMinimum hn hconn.isPreconnected hcoeff hcneg
    (contDiffOn_const.sub hu) hdefect
    (fun y hy => sub_nonneg.mpr (hmax y hy)) ⟨x₀, hx₀, sub_self _⟩ x hx
  linarith

end P201.Elliptic
