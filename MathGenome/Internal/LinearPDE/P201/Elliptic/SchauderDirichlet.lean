import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.SchauderDirichlet
import MathGenome.Internal.LinearPDE.P201.Elliptic.MaximumComparison
import MathGenome.Internal.LinearPDE.P201.Elliptic.PoissonSchauder
import MathGenome.Internal.LinearPDE.P201.Elliptic.ChartSchauder
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt

import MathGenome.Internal.LinearPDE.P201.Elliptic.BallSchauderSolvability
import MathGenome.Internal.LinearPDE.P201.Elliptic.SchauderRegularity
import MathGenome.Internal.LinearPDE.P201.Elliptic.VariableSchauder
/-!
Conditional derivation of the final classical Schauder theorem.
All conditional target helpers retain all eight ordered premise types.
The original targets remain undefined pending real upstream dependency closure.
-/
noncomputable section
open Set Metric TopologicalSpace Filter
open scoped ContDiff NNReal ENNReal Topology InnerProductSpace
namespace P201.Elliptic.SchauderDirichlet
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201Specs.Elliptic.SchauderDirichlet

/-- Components of an open Euclidean set have no new boundary inside it. -/
theorem component_frontier_subset {n : ℕ} (Ω : Domain n) (x : Space n) :
    frontier (connectedComponentIn (Ω : Set (Space n)) x) ⊆
      frontier (Ω : Set (Space n)) := by
  let D := connectedComponentIn (Ω : Set (Space n)) x
  have hD : IsOpen D := Ω.isOpen.connectedComponentIn
  have hsub : D ⊆ (Ω : Set (Space n)) := connectedComponentIn_subset _ _
  intro p hp
  rw [frontier, hD.interior_eq] at hp
  rw [frontier, Ω.isOpen.interior_eq]
  refine ⟨closure_mono hsub hp.1, ?_⟩
  intro hpΩ
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen p hpΩ
  obtain ⟨q, hqD, hqr⟩ :=
    (closure_inter_open_nonempty_iff isOpen_ball).mp ⟨p, hp.1, mem_ball_self hr⟩
  have hxΩ : x ∈ (Ω : Set (Space n)) := connectedComponentIn_nonempty_iff.mp ⟨q, hqD⟩
  have hU : IsPreconnected (D ∪ ball p r) :=
    isPreconnected_connectedComponentIn.union q hqD hqr (convex_ball p r).isPreconnected
  have hUD : D ∪ ball p r ⊆ D :=
    hU.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hxΩ))
      (union_subset hsub hrΩ)
  exact hp.2 (hUD (Or.inr (mem_ball_self hr)))

/-- Classical comparison on any bounded open set, component by component.
The coefficient, derivative and boundary assumptions are unchanged. -/
theorem comparison_on_bounded_open {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c u v : Space n → ℝ) (hcoeff : EllipticCoefficients Ω a b c)
    (hc : ∀ x ∈ Ω, c x ≤ 0)
    (hu : ContDiffOn ℝ 2 u Ω) (huc : ContinuousOn u (closure (Ω : Set (Space n))))
    (hv : ContDiffOn ℝ 2 v Ω) (hvc : ContinuousOn v (closure (Ω : Set (Space n))))
    (hL : ∀ x ∈ Ω, nondivergenceOperator a b c v x ≤ nondivergenceOperator a b c u x)
    (hboundary : ∀ x ∈ frontier (Ω : Set (Space n)), u x ≤ v x) :
    ∀ x ∈ closure (Ω : Set (Space n)), u x ≤ v x := by
  have hle : ∀ x ∈ (Ω : Set (Space n)), u x ≤ v x := by
    intro x hx
    let D : Domain n := ⟨connectedComponentIn (Ω : Set (Space n)) x,
      Ω.isOpen.connectedComponentIn⟩
    have hsub : (D : Set (Space n)) ⊆ (Ω : Set (Space n)) := connectedComponentIn_subset _ _
    exact P201.Elliptic.comparison n hn D (hb.subset hsub)
      isPreconnected_connectedComponentIn a b c u v
      (ellipticCoefficients_mono hcoeff hsub) (fun y hy => hc y (hsub hy))
      (hu.mono hsub) (huc.mono (closure_mono hsub))
      (hv.mono hsub) (hvc.mono (closure_mono hsub)) (fun y hy => hL y (hsub hy))
      (fun y hy => hboundary y (component_frontier_subset Ω x hy))
      x (mem_connectedComponentIn hx)
  intro x hx
  exact le_on_closure hle huc hvc hx

/-- Hölder coefficients have the actual interior continuity used by comparison. -/
theorem continuousOn_of_isHolderOn {n : ℕ} {α : ℝ} (hα : 0 < α)
    {g : Space n → ℝ} {s : Set (Space n)} (hg : IsHolderOn α g s) :
    ContinuousOn g s := by
  obtain ⟨M, H, hM, hH, hb, hh⟩ := hg
  let C : ℝ≥0 := ⟨H, hH⟩
  let exponent : ℝ≥0 := ⟨α, hα.le⟩
  have hholder : HolderOnWith C exponent g s := by
    intro x hx y hy
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal (dist (g x) (g y)) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal (dist x y) ^ α
    rw [← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le]
    change ENNReal.ofReal (dist (g x) (g y)) ≤
      ENNReal.ofReal H * ENNReal.ofReal (dist x y ^ α)
    rw [← ENNReal.ofReal_mul hH]
    exact ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using hh x hx y hy)
  exact hholder.continuousOn hα

/-- Bridge from the shared Hölder and ellipticity data to classical comparison. -/
theorem ellipticCoefficients_of_holder {n : ℕ} {α ell : ℝ} (hα : 0 < α)
    (hell : 0 < ell) (Ω : Domain n)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n)))) :
    EllipticCoefficients Ω a b c := by
  have hconta : ContinuousOn a (closure (Ω : Set (Space n))) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact continuousOn_of_isHolderOn hα (hcoeff.1 i j)
  have hcontb : ContinuousOn b (closure (Ω : Set (Space n))) := by
    have hconvert : Continuous (fun v : Fin n → ℝ => WithLp.toLp 2 v) := by fun_prop
    exact hconvert.comp_continuousOn (continuousOn_pi.mpr
      (fun i => continuousOn_of_isHolderOn hα (hcoeff.2.1 i)))
  exact ⟨hconta.mono subset_closure, hcontb.mono subset_closure,
    (continuousOn_of_isHolderOn hα hcoeff.2.2).mono subset_closure,
    fun x hx => ha.1 x (subset_closure hx),
    ell, hell, fun x hx => ha.2 x (subset_closure hx)⟩

/-- Uniqueness on the closed domain without connectedness, including the empty set.
Only C² interior regularity and continuity on the closure are needed. -/
theorem classical_solution_unique {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c f G u v : Space n → ℝ) (hcoeff : EllipticCoefficients Ω a b c)
    (hc : ∀ x ∈ Ω, c x ≤ 0)
    (hu : ContDiffOn ℝ 2 u Ω) (huc : ContinuousOn u (closure (Ω : Set (Space n))))
    (hv : ContDiffOn ℝ 2 v Ω) (hvc : ContinuousOn v (closure (Ω : Set (Space n))))
    (hLu : ∀ x ∈ Ω, nondivergenceOperator a b c u x = f x)
    (hLv : ∀ x ∈ Ω, nondivergenceOperator a b c v x = f x)
    (hbu : ∀ x ∈ frontier (Ω : Set (Space n)), u x = G x)
    (hbv : ∀ x ∈ frontier (Ω : Set (Space n)), v x = G x) :
    EqOn u v (closure (Ω : Set (Space n))) := by
  have huv := comparison_on_bounded_open hn Ω hb a b c u v hcoeff hc hu huc hv hvc
    (fun x hx => by rw [hLu x hx, hLv x hx])
    (fun x hx => by rw [hbu x hx, hbv x hx])
  have hvu := comparison_on_bounded_open hn Ω hb a b c v u hcoeff hc hv hvc hu huc
    (fun x hx => by rw [hLu x hx, hLv x hx])
    (fun x hx => by rw [hbu x hx, hbv x hx])
  exact fun x hx => le_antisymm (huv x hx) (hvu x hx)

/-- The uniqueness clause of the final theorem follows from the original data. -/
theorem dirichlet_solution_unique {n : ℕ} (hn : 1 ≤ n) {α ell : ℝ}
    (hα : 0 < α) (hell : 0 < ell) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G u v : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    (hu : IsDirichletSolution α Ω a b c f G u)
    (hv : IsDirichletSolution α Ω a b c f G v) :
    EqOn u v (closure (Ω : Set (Space n))) := by
  exact classical_solution_unique hn Ω hb a b c f G u v
    (ellipticCoefficients_of_holder hα hell Ω ha hcoeff)
    (fun x hx => hc x (subset_closure hx))
    (hu.1.1.mono subset_closure) hu.1.1.continuousOn
    (hv.1.1.mono subset_closure) hv.1.1.continuousOn hu.2.1 hv.2.1 hu.2.2 hv.2.2

/-- Local equality preserves the actual iterated coordinate derivatives,
including their totalized values at points without differentiability. -/
theorem partialWord_eqOn {n : ℕ} {Ω : Domain n} {u v : Space n → ℝ}
    (heq : EqOn u v Ω) (l : List (Fin n)) :
    EqOn (P102.U4.partialWord u l) (P102.U4.partialWord v l) Ω := by
  induction l with
  | nil => exact heq
  | cons i l ih =>
    intro x hx
    have hlocal : P102.U4.partialWord u l =ᶠ[𝓝 x] P102.U4.partialWord v l := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact ih hy
    exact congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinate n i)) hlocal.fderiv_eq

/-- The classical operator depends only on the solution's germ inside Ω. -/
theorem nondivergenceOperator_eqOn {n : ℕ} {Ω : Domain n}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) {u v : Space n → ℝ} (heq : EqOn u v Ω) :
    EqOn (nondivergenceOperator a b c u) (nondivergenceOperator a b c v) Ω := by
  intro x hx
  have hfirst (i : Fin n) : firstPartial u i x = firstPartial v i x :=
    partialWord_eqOn heq [i] hx
  have hsecond (i j : Fin n) : secondPartial u i j x = secondPartial v i j x :=
    partialWord_eqOn heq [i, j] hx
  simp only [nondivergenceOperator, hfirst, hsecond, heq hx]

/-- The shared local Hölder solution class is intrinsic to its open domain. -/
theorem isC2HolderLocOn_congr {n : ℕ} {α : ℝ} {Ω : Domain n}
    {u v : Space n → ℝ} (hv : IsC2HolderLocOn α v Ω) (heq : EqOn u v Ω) :
    IsC2HolderLocOn α u Ω := by
  refine ⟨hv.1.congr (fun x hx => heq hx), ?_⟩
  intro x hx
  obtain ⟨r, hr, hB, hh⟩ := hv.2 x hx
  refine ⟨r, hr, hB, ?_⟩
  intro i j
  obtain ⟨M, H, hM, hH, hb, hholder⟩ := hh i j
  have hd : EqOn (P201Specs.multiPartial u {i, j}) (P201Specs.multiPartial v {i, j}) Ω :=
    partialWord_eqOn heq _
  refine ⟨M, H, hM, hH, ?_, ?_⟩
  · intro y hy
    rw [hd (hB hy)]
    exact hb y hy
  · intro y hy z hz
    rw [hd (hB hy), hd (hB hz)]
    exact hholder y hy z hz

/-- Perron subfunctions for the actual inhomogeneous operator. Testing against
all ordered classical ball solutions is equivalent to testing against the ball
solution with the function's own trace whenever continuous ball solvability is
available. This definition assumes no global solution. -/
def IsSubfunction {n : ℕ} (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c f G v : Space n → ℝ) : Prop :=
  ContinuousOn v (closure (Ω : Set (Space n))) ∧
    (∀ x ∈ frontier (Ω : Set (Space n)), v x ≤ G x) ∧
    ∀ (z : Space n) (r : ℝ), 0 < r → closedBall z r ⊆ (Ω : Set (Space n)) →
      ∀ w : Space n → ℝ, ContDiffOn ℝ 2 w (ball z r) →
        ContinuousOn w (closedBall z r) →
        (∀ x ∈ ball z r, nondivergenceOperator a b c w x = f x) →
        (∀ x ∈ sphere z r, v x ≤ w x) → ∀ x ∈ ball z r, v x ≤ w x

/-- The finite-maximum closure step of the inhomogeneous Perron construction. -/
theorem isSubfunction_max {n : ℕ} {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G u v : Space n → ℝ}
    (hu : IsSubfunction Ω a b c f G u) (hv : IsSubfunction Ω a b c f G v) :
    IsSubfunction Ω a b c f G (fun x => max (u x) (v x)) := by
  refine ⟨hu.1.sup hv.1, ?_, ?_⟩
  · intro x hx
    exact max_le (hu.2.1 x hx) (hv.2.1 x hx)
  · intro z r hr hB w hw hwc heq hbound x hx
    exact max_le
      (hu.2.2 z r hr hB w hw hwc heq
        (fun y hy => (le_max_left _ _).trans (hbound y hy)) x hx)
      (hv.2.2 z r hr hB w hw hwc heq
        (fun y hy => (le_max_right _ _).trans (hbound y hy)) x hx)

/-- Classical subsolutions are Perron subfunctions, including on disconnected Ω. -/
theorem isSubfunction_of_classical {n : ℕ} (hn : 1 ≤ n) {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G v : Space n → ℝ} (hcoeff : EllipticCoefficients Ω a b c)
    (hc : ∀ x ∈ Ω, c x ≤ 0) (hv : ContDiffOn ℝ 2 v Ω)
    (hvc : ContinuousOn v (closure (Ω : Set (Space n))))
    (hLv : ∀ x ∈ Ω, f x ≤ nondivergenceOperator a b c v x)
    (hbv : ∀ x ∈ frontier (Ω : Set (Space n)), v x ≤ G x) :
    IsSubfunction Ω a b c f G v := by
  refine ⟨hvc, hbv, ?_⟩
  intro z r hr hB w hw hwc heq hbound x hx
  let B : Domain n := ⟨ball z r, isOpen_ball⟩
  have hsub : (B : Set (Space n)) ⊆ (Ω : Set (Space n)) := ball_subset_closedBall.trans hB
  have hvB : ContDiffOn ℝ 2 v B := hv.mono hsub
  have hvcB : ContinuousOn v (closure (B : Set (Space n))) :=
    hvc.mono (closure_mono hsub)
  have hwcB : ContinuousOn w (closure (B : Set (Space n))) := by
    simpa only [B, Opens.coe_mk, closure_ball z hr.ne'] using hwc
  apply comparison_on_bounded_open hn B isBounded_ball a b c v w
    (ellipticCoefficients_mono hcoeff hsub) (fun y hy => hc y (hsub hy))
    hvB hvcB hw hwcB ?_ ?_ x (subset_closure hx)
  · intro y hy
    rw [heq y hy]
    exact hLv y (hsub hy)
  · intro y hy
    exact hbound y (frontier_ball_subset_sphere hy)

/-- Replace on the open ball and retain the original function everywhere else. -/
def ballReplacement {n : ℕ} (z : Space n) (r : ℝ) (w v : Space n → ℝ) :
    Space n → ℝ := by
  classical
  exact (ball z r).piecewise w v

@[simp] theorem ballReplacement_of_mem {n : ℕ} {z x : Space n} {r : ℝ}
    {w v : Space n → ℝ} (hx : x ∈ ball z r) :
    ballReplacement z r w v x = w x := by
  classical
  simp [ballReplacement, hx]

@[simp] theorem ballReplacement_of_not_mem {n : ℕ} {z x : Space n} {r : ℝ}
    {w v : Space n → ℝ} (hx : x ∉ ball z r) :
    ballReplacement z r w v x = v x := by
  classical
  simp [ballReplacement, hx]

/-- Ball replacement preserves subfunctions. The intersection comparison is
performed on a bounded open set without any boundary smoothness hypothesis. -/
theorem isSubfunction_ballReplacement {n : ℕ} (hn : 1 ≤ n) {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G v : Space n → ℝ} (hcoeff : EllipticCoefficients Ω a b c)
    (hc : ∀ x ∈ Ω, c x ≤ 0) (hv : IsSubfunction Ω a b c f G v)
    {z : Space n} {r : ℝ} (hr : 0 < r) (hB : closedBall z r ⊆ (Ω : Set (Space n)))
    {w : Space n → ℝ} (hw : ContDiffOn ℝ 2 w (ball z r))
    (hwc : ContinuousOn w (closedBall z r))
    (heq : ∀ x ∈ ball z r, nondivergenceOperator a b c w x = f x)
    (htrace : ∀ x ∈ sphere z r, w x = v x) :
    IsSubfunction Ω a b c f G (ballReplacement z r w v) ∧
      ∀ x, v x ≤ ballReplacement z r w v x := by
  classical
  have hraise : ∀ x ∈ ball z r, v x ≤ w x :=
    hv.2.2 z r hr hB w hw hwc heq (fun x hx => (htrace x hx).ge)
  have hraiseAll : ∀ x, v x ≤ ballReplacement z r w v x := by
    intro x
    by_cases hx : x ∈ ball z r
    · simpa only [ballReplacement_of_mem hx] using hraise x hx
    · simp only [ballReplacement_of_not_mem hx, le_refl]
  refine ⟨⟨?_, ?_, ?_⟩, hraiseAll⟩
  · apply ContinuousOn.piecewise
    · intro x hx
      exact htrace x (frontier_ball_subset_sphere hx.2)
    · exact hwc.mono (by
        rw [closure_ball z hr.ne']
        exact inter_subset_right)
    · exact hv.1.mono inter_subset_left
  · intro x hx
    have hxnot : x ∉ ball z r := by
      intro hxB
      have hxnot : x ∉ (Ω : Set (Space n)) := by
        have := hx.2
        simpa only [Ω.isOpen.interior_eq] using this
      exact hxnot (hB (ball_subset_closedBall hxB))
    simpa only [ballReplacement_of_not_mem hxnot] using hv.2.1 x hx
  · intro z' r' hr' hB' t ht htc hteq hbound x hx
    have hvle : ∀ y ∈ ball z' r', v y ≤ t y :=
      hv.2.2 z' r' hr' hB' t ht htc hteq
        (fun y hy => (hraiseAll y).trans (hbound y hy))
    have hvleClosed : ∀ y ∈ closedBall z' r', v y ≤ t y := by
      rw [← closure_ball z' hr'.ne']
      exact fun y hy => le_on_closure hvle
        (hv.1.mono (by
          rw [closure_ball z' hr'.ne']
          exact hB'.trans subset_closure))
        (by simpa only [closure_ball z' hr'.ne'] using htc) hy
    by_cases hxB : x ∈ ball z r
    · rw [ballReplacement_of_mem hxB]
      let D : Domain n := ⟨ball z r ∩ ball z' r', isOpen_ball.inter isOpen_ball⟩
      have hDB : (D : Set (Space n)) ⊆ ball z r := inter_subset_left
      have hDB' : (D : Set (Space n)) ⊆ ball z' r' := inter_subset_right
      have hDΩ : (D : Set (Space n)) ⊆ (Ω : Set (Space n)) :=
        hDB.trans (ball_subset_closedBall.trans hB)
      have hclB : closure (D : Set (Space n)) ⊆ closedBall z r := by
        simpa only [closure_ball z hr.ne'] using closure_mono hDB
      have hclB' : closure (D : Set (Space n)) ⊆ closedBall z' r' := by
        simpa only [closure_ball z' hr'.ne'] using closure_mono hDB'
      apply comparison_on_bounded_open hn D (isBounded_ball.subset hDB)
        a b c w t (ellipticCoefficients_mono hcoeff hDΩ)
        (fun y hy => hc y (hDΩ hy)) (hw.mono hDB) (hwc.mono hclB)
        (ht.mono hDB') (htc.mono hclB') ?_ ?_ x (subset_closure ⟨hxB, hx⟩)
      · intro y hy
        rw [heq y hy.1, hteq y hy.2]
      · intro y hy
        have hyB := hclB (frontier_subset_closure hy)
        have hyB' := hclB' (frontier_subset_closure hy)
        by_cases hyin : y ∈ ball z r
        · have hynotin : y ∉ ball z' r' := by
            intro hyin'
            have hynot : y ∉ (D : Set (Space n)) := by
              have := hy.2
              simpa only [D.isOpen.interior_eq] using this
            exact hynot ⟨hyin, hyin'⟩
          have hysphere : y ∈ sphere z' r' :=
            mem_sphere.mpr (le_antisymm (mem_closedBall.mp hyB')
              (not_lt.mp (by simpa only [mem_ball] using hynotin)))
          simpa only [ballReplacement_of_mem hyin] using hbound y hysphere
        · have hysphere : y ∈ sphere z r :=
            mem_sphere.mpr (le_antisymm (mem_closedBall.mp hyB)
              (not_lt.mp (by simpa only [mem_ball] using hyin)))
          rw [htrace y hysphere]
          exact hvleClosed y hyB'
    · simpa only [ballReplacement_of_not_mem hxB] using hvle x hx

/-- Continuous-data ball solvability supplies the raising operation with
actual locally Hölder classical solutions. This is an application of precisely
the first conditional premise, rather than an assumed replacement certificate. -/
theorem exists_subfunction_ballReplacement
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G v : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space n))))
    (hv : IsSubfunction Ω a b c f G v)
    {z : Space n} {r : ℝ} (hr : 0 < r) (hB : closedBall z r ⊆ (Ω : Set (Space n))) :
    ∃ V : Space n → ℝ, IsSubfunction Ω a b c f G V ∧ (∀ x, v x ≤ V x) ∧
      IsC2HolderLocOn α V (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r) ∧
      (∀ x ∈ ball z r, nondivergenceOperator a b c V x = f x) ∧
      ∀ x ∉ ball z r, V x = v x := by
  have hclosed : closedBall z r ⊆ closure (Ω : Set (Space n)) := hB.trans subset_closure
  have hmono {g : Space n → ℝ} (hg : IsHolderOn α g (closure (Ω : Set (Space n)))) :
      IsHolderOn α g (closedBall z r) := by
    obtain ⟨M, H, hM, hH, hb, hh⟩ := hg
    exact ⟨M, H, hM, hH, fun x hx => hb x (hclosed hx),
      fun x hx y hy => hh x (hclosed hx) y (hclosed hy)⟩
  have hvSphere : ContinuousOn v (sphere z r) :=
    hv.1.mono (sphere_subset_closedBall.trans hclosed)
  let g : C(sphere z r, ℝ) := ⟨fun x => v x, hvSphere.domRestrict⟩
  have haB : UniformlyEllipticOn ell a (closedBall z r) :=
    ⟨fun x hx => ha.1 x (hclosed hx), fun x hx => ha.2 x (hclosed hx)⟩
  have hcoeffB : CoefficientsHolderOn α a b c (closedBall z r) :=
    ⟨fun i j => hmono (hcoeff.1 i j), fun i => hmono (hcoeff.2.1 i), hmono hcoeff.2.2⟩
  obtain ⟨w, hw, hwreg, _⟩ := hcontinuous hn α hα hα1 z r hr a b c
    ⟨ell, hell, haB⟩ hcoeffB (fun x hx => hc x (hclosed hx)) f (hmono hf) g
  have hwtrace : ∀ x ∈ sphere z r, w x = v x := by
    intro x hx
    exact hw.2.2.2 ⟨x, hx⟩
  obtain ⟨hV, hraise⟩ := isSubfunction_ballReplacement hn
    (ellipticCoefficients_of_holder hα hell Ω ha hcoeff)
    (fun x hx => hc x (subset_closure hx)) hv hr hB hw.1 hw.2.1 hw.2.2.1 hwtrace
  have heq : EqOn (ballReplacement z r w v) w
      (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r) :=
    fun x hx => ballReplacement_of_mem hx
  exact ⟨ballReplacement z r w v, hV, hraise, isC2HolderLocOn_congr hwreg heq,
    fun x hx => (nondivergenceOperator_eqOn a b c heq hx).trans (hw.2.2.1 x hx),
    fun x hx => ballReplacement_of_not_mem hx⟩

/-- The one-coordinate exponential used for the uniform slab barrier. -/
def coordinateExponential {n : ℕ} (i : Fin n) (k : ℝ) (x : Space n) : ℝ :=
  Real.exp (k * x i)

theorem coordinateExponential_contDiff {n : ℕ} (i : Fin n) (k : ℝ) :
    ContDiff ℝ ⊤ (coordinateExponential i k) := by
  exact (contDiff_const.mul (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff).exp

theorem coordinateExponential_hasFDerivAt {n : ℕ} (i : Fin n) (k : ℝ) (x : Space n) :
    HasFDerivAt (coordinateExponential i k)
      (Real.exp (k * x i) • (k • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i)) x := by
  exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).hasFDerivAt).const_mul k).exp

theorem coordinateExponential_firstPartial {n : ℕ} (i j : Fin n) (k : ℝ) (x : Space n) :
    firstPartial (coordinateExponential i k) j x =
      k * (if j = i then 1 else 0) * Real.exp (k * x i) := by
  rw [firstPartial, (coordinateExponential_hasFDerivAt i k x).fderiv]
  simp only [smul_apply, smul_eq_mul]
  by_cases hij : j = i <;>
    simp [P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, PiLp.single_apply, PiLp.proj_apply, hij, eq_comm] <;> ring

theorem coordinateExponential_secondPartial {n : ℕ} (i j l : Fin n) (k : ℝ) (x : Space n) :
    secondPartial (coordinateExponential i k) j l x =
      k ^ 2 * (if j = i then 1 else 0) * (if l = i then 1 else 0) *
        Real.exp (k * x i) := by
  have hfirst : firstPartial (coordinateExponential i k) l =
      fun y => (k * (if l = i then 1 else 0)) * coordinateExponential i k y := by
    funext y
    exact coordinateExponential_firstPartial i l k y
  rw [secondPartial, hfirst, firstPartial,
    (((coordinateExponential_hasFDerivAt i k x).const_mul
      (k * (if l = i then 1 else 0))).fderiv)]
  simp only [smul_apply, smul_eq_mul]
  by_cases hij : j = i <;> by_cases hil : l = i <;>
    simp [P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, PiLp.single_apply, PiLp.proj_apply, hij, hil, eq_comm] <;> ring

/-- The positive slab barrier; R bounds the absolute coordinate on Ω̄. -/
def slabBarrier {n : ℕ} (i : Fin n) (k R : ℝ) (x : Space n) : ℝ :=
  Real.exp (k * (R + 1)) - coordinateExponential i k x

theorem slabBarrier_contDiff {n : ℕ} (i : Fin n) (k R : ℝ) :
    ContDiff ℝ ⊤ (slabBarrier i k R) :=
  contDiff_const.sub (coordinateExponential_contDiff i k)

theorem slabBarrier_operator {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) (i : Fin n) (k R : ℝ) (x : Space n) :
    nondivergenceOperator a b c (slabBarrier i k R) x =
      -Real.exp (k * x i) * (a x i i * k ^ 2 + b x i * k) +
        c x * slabBarrier i k R x := by
  unfold nondivergenceOperator slabBarrier
  simp only [firstPartial_const_sub, secondPartial_const_sub,
    coordinateExponential_firstPartial, coordinateExponential_secondPartial]
  simp only [mul_neg, Finset.sum_neg_distrib, mul_ite, ite_mul, mul_zero,
    zero_mul, mul_one, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Uniform strict barrier from a single diagonal ellipticity bound and a
single drift bound. There is no bound or strict negativity assumption on c. -/
theorem exists_uniform_slabBarrier {n : ℕ} (i : Fin n) {ell K R : ℝ}
    (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ k δ A : ℝ, 0 < k ∧ 0 < δ ∧ 0 < A ∧
      ∀ (s : Set (Space n))
        (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
        (c : Space n → ℝ),
        (∀ x ∈ s, |x i| ≤ R) →
        (∀ x ∈ s, ell ≤ a x i i) →
        (∀ x ∈ s, |b x i| ≤ K) →
        (∀ x ∈ s, c x ≤ 0) →
        (∀ x ∈ s, 0 < slabBarrier i k R x ∧ slabBarrier i k R x ≤ A) ∧
        ∀ x ∈ s, nondivergenceOperator a b c (slabBarrier i k R) x ≤ -δ := by
  let k := (K + 1) / ell
  have hk : 0 < k := div_pos (by linarith) hell
  have hkell : ell * k = K + 1 := by dsimp [k]; field_simp
  let δ := k * Real.exp (-k * R)
  let A := Real.exp (k * (R + 1))
  have hδ : 0 < δ := mul_pos hk (Real.exp_pos _)
  refine ⟨k, δ, A, hk, hδ, Real.exp_pos _, ?_⟩
  intro s a b c hcoord ha hb hc
  constructor
  · intro x hx
    have hxi : x i < R + 1 := lt_of_le_of_lt (le_abs_self _ |>.trans (hcoord x hx)) (by linarith)
    have hpos : 0 < slabBarrier i k R x :=
      sub_pos.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hxi hk))
    exact ⟨hpos, sub_le_self _ (Real.exp_pos _).le⟩
  · intro x hx
    have hxi := abs_le.mp (hcoord x hx)
    have hbxi := (abs_le.mp (hb x hx)).1
    have hmain : k ≤ a x i i * k ^ 2 + b x i * k := by
      have h1 := mul_le_mul_of_nonneg_right (ha x hx) (sq_nonneg k)
      have h2 := mul_le_mul_of_nonneg_right hbxi hk.le
      have hrel : ell * k ^ 2 = (K + 1) * k := by rw [pow_two, ← mul_assoc, hkell]
      nlinarith
    have hExp : Real.exp (-k * R) ≤ Real.exp (k * x i) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hψ : 0 ≤ slabBarrier i k R x := by
      apply sub_nonneg.mpr
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith : x i ≤ R + 1) hk.le)
    rw [slabBarrier_operator]
    have h1 := mul_le_mul_of_nonneg_left hmain (Real.exp_pos (k * x i)).le
    have h2 := mul_le_mul_of_nonneg_left hExp hk.le
    have h3 := mul_nonpos_of_nonpos_of_nonneg (hc x hx) hψ
    dsimp [δ]
    nlinarith

/-- A diagonal coefficient inherits the quadratic ellipticity lower bound. -/
theorem diagonal_lower_bound {n : ℕ} {ell : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {s : Set (Space n)}
    (ha : UniformlyEllipticOn ell a s) (i : Fin n) {x : Space n} (hx : x ∈ s) :
    ell ≤ a x i i := by
  have h := ha.2 x hx (P201Specs.coordinate n i)
  have hnorm : ‖P201Specs.coordinate n i‖ = 1 :=
    (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
  rw [hnorm, one_pow, mul_one] at h
  simpa only [P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, mul_one, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

/-- The actual coefficient norm bounds each drift coordinate, including on
sets with multiple components. Boundedness precedes every real supremum use. -/
theorem drift_bound_of_coefficientNorm {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s : Set (Space n)}
    (hcoeff : CoefficientsHolderOn α a b c s)
    (hK : coefficientNormOn α a b c s ≤ K) (i : Fin n) {x : Space n} (hx : x ∈ s) :
    |b x i| ≤ K := by
  have ha0 (j l : Fin n) : 0 ≤ holderNormOn α (fun y => a y j l) s :=
    (P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn (hcoeff.1 j l)).1
  have hb0 (j : Fin n) : 0 ≤ holderNormOn α (fun y => b y j) s :=
    (P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn (hcoeff.2.1 j)).1
  have hc0 := (P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn hcoeff.2.2).1
  have hsumA : 0 ≤ ∑ j : Fin n, ∑ l : Fin n, holderNormOn α (fun y => a y j l) s :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => ha0 j l
  have hsumB : (∑ j : Fin n, holderNormOn α (fun y => b y j) s) ≤ K := by
    dsimp [coefficientNormOn] at hK
    linarith
  have hi : holderNormOn α (fun y => b y i) s ≤
      ∑ j : Fin n, holderNormOn α (fun y => b y j) s :=
    Finset.single_le_sum (fun j _ => hb0 j) (Finset.mem_univ i)
  exact ((P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn
    (hcoeff.2.1 i)).2.1 x hx).trans (hi.trans hsumB)

/-- The within-derivative C²,α norm controls its order-zero part. -/
theorem supNormOn_le_c2HolderUpToNormOn {n : ℕ} (α : ℝ) (G : Space n → ℝ)
    (s : Set (Space n)) : supNormOn G s ≤ c2HolderUpToNormOn α G s := by
  have h1 : 0 ≤ ∑ i : Fin n, supNormOn (firstPartialWithin G s i) s :=
    Finset.sum_nonneg fun i _ => P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have h2 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, supNormOn (secondPartialWithin G s i j) s :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have h3 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      holderSeminormOn α (secondPartialWithin G s i j) s :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _
  dsimp [c2HolderUpToNormOn, scaledWithinSolutionNorm]
  simp only [one_mul, one_pow, Real.one_rpow]
  linarith

/-- A fixed bounded domain and fixed coefficient bounds admit a single strict
positive smooth barrier, chosen before the coefficient fields themselves. -/
theorem exists_uniform_domain_barrier {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hbounded : Bornology.IsBounded (Ω : Set (Space n))) {ell K : ℝ}
    (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ (ψ : Space n → ℝ) (δ A : ℝ),
      0 < δ ∧ 0 < A ∧ ContDiff ℝ ⊤ ψ ∧
      (∀ x ∈ closure (Ω : Set (Space n)), 0 < ψ x ∧ ψ x ≤ A) ∧
      ∀ (α : ℝ) (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ),
        UniformlyEllipticOn ell a (closure (Ω : Set (Space n))) →
        CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))) →
        coefficientNormOn α a b c (closure (Ω : Set (Space n))) ≤ K →
        (∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0) →
        ∀ x ∈ closure (Ω : Set (Space n)), nondivergenceOperator a b c ψ x ≤ -δ := by
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨R, hR, hRΩ⟩ := hbounded.closure.subset_closedBall_lt 0 (0 : Space n)
  have hcoord : ∀ x ∈ closure (Ω : Set (Space n)), |x i| ≤ R := by
    intro x hx
    exact (PiLp.norm_apply_le x i).trans (by simpa using mem_closedBall.mp (hRΩ hx))
  obtain ⟨k, δ, A, hk, hδ, hA, hbar⟩ := exists_uniform_slabBarrier (R := R) i hell hK
  -- Positivity depends only on the coordinate slab, not on the coefficients.
  have hψpos : ∀ x ∈ closure (Ω : Set (Space n)), 0 < slabBarrier i k R x ∧
      slabBarrier i k R x ≤ A := by
    -- Use an auxiliary diagonal matrix with entry ell; no PDE is assumed.
    let a0 : Space n → Matrix (Fin n) (Fin n) ℝ := fun _ _ _ => ell
    exact (hbar (closure (Ω : Set (Space n))) a0 (fun _ => 0) (fun _ => 0) hcoord
      (fun _ _ => le_refl ell) (fun _ _ => by simpa using hK)
      (fun _ _ => le_refl 0)).1
  refine ⟨slabBarrier i k R, δ, A, hδ, hA, slabBarrier_contDiff i k R, hψpos, ?_⟩
  intro α a b c ha hcoeff hbound hc
  exact (hbar (closure (Ω : Set (Space n))) a b c hcoord
    (fun x hx => diagonal_lower_bound ha i hx)
    (fun x hx => drift_bound_of_coefficientNorm hcoeff hbound i hx) hc).2

/-- Addition of constants changes only the zeroth-order term of L. -/
theorem nondivergenceOperator_add_const {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c u : Space n → ℝ) (M : ℝ) (x : Space n) :
    nondivergenceOperator a b c (fun y => u y + M) x =
      nondivergenceOperator a b c u x + c x * M := by
  have hfirst (i : Fin n) : firstPartial (fun y => u y + M) i = firstPartial u i := by
    funext y
    simp only [firstPartial, fderiv_add_const]
  have hsecond (i j : Fin n) :
      secondPartial (fun y => u y + M) i j x = secondPartial u i j x := by
    simp only [secondPartial, hfirst]
  simp only [nondivergenceOperator, hfirst, hsecond]
  ring

@[simp] theorem nondivergenceOperator_zero {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) (x : Space n) :
    nondivergenceOperator a b c (fun _ => 0) x = 0 := by
  have hfirst (i : Fin n) : firstPartial (fun _ : Space n => (0 : ℝ)) i = fun _ => 0 := by
    funext y
    simp [firstPartial]
  simp only [nondivergenceOperator, secondPartial, hfirst]
  simp [firstPartial]

/-- Scalar linearity on an open domain, with actual derivative hypotheses. -/
theorem nondivergenceOperator_const_mul {n : ℕ} {Ω : Domain n}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (t : ℝ) {x : Space n} (hx : x ∈ Ω) :
    nondivergenceOperator a b c (fun y => t * u y) x =
      t * nondivergenceOperator a b c u x := by
  have h := nondivergenceOperator_mul_sub a b c hu
    (contDiffOn_const : ContDiffOn ℝ 2 (fun _ : Space n => (0 : ℝ)) Ω) t hx
  simpa only [sub_zero, nondivergenceOperator_zero] using h

/-- The pointwise two-sided C⁰ bound from a genuine smooth strict barrier. -/
theorem classical_solution_barrier_bound {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c u f ψ : Space n → ℝ) (hcoeff : EllipticCoefficients Ω a b c)
    (hc : ∀ x ∈ Ω, c x ≤ 0)
    (hu : ContDiffOn ℝ 2 u Ω) (huc : ContinuousOn u (closure (Ω : Set (Space n))))
    (hLu : ∀ x ∈ Ω, nondivergenceOperator a b c u x = f x)
    {F M δ : ℝ} (hF : 0 ≤ F) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hf : ∀ x ∈ Ω, ‖f x‖ ≤ F)
    (hboundary : ∀ x ∈ frontier (Ω : Set (Space n)), ‖u x‖ ≤ M)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hψ0 : ∀ x ∈ closure (Ω : Set (Space n)), 0 ≤ ψ x)
    (hLψ : ∀ x ∈ Ω, nondivergenceOperator a b c ψ x ≤ -δ) :
    ∀ x ∈ closure (Ω : Set (Space n)), ‖u x‖ ≤ (F / δ) * ψ x + M := by
  let W : Space n → ℝ := fun x => (F / δ) * ψ x + M
  have hψ2 : ContDiffOn ℝ 2 ψ Ω := hψ.contDiffOn.of_le (by norm_num)
  have hW : ContDiffOn ℝ 2 W Ω := (contDiffOn_const.mul hψ2).add contDiffOn_const
  have hWc : ContinuousOn W (closure (Ω : Set (Space n))) :=
    (continuousOn_const.mul hψ.continuous.continuousOn).add continuousOn_const
  have hratio : 0 ≤ F / δ := div_nonneg hF hδ.le
  have hLW : ∀ x ∈ Ω, nondivergenceOperator a b c W x ≤ -F := by
    intro x hx
    dsimp [W]
    rw [nondivergenceOperator_add_const, nondivergenceOperator_const_mul a b c hψ2 _ hx]
    have h1 := mul_le_mul_of_nonneg_left (hLψ x hx) hratio
    have h2 := mul_nonpos_of_nonpos_of_nonneg (hc x hx) hM
    have hcancel : (F / δ) * (-δ) = -F := by field_simp
    linarith
  have hbound : ∀ x ∈ frontier (Ω : Set (Space n)), u x ≤ W x := by
    intro x hx
    have hxcl := frontier_subset_closure hx
    exact (le_abs_self _ |>.trans (hboundary x hx)).trans
      (le_add_of_nonneg_left (mul_nonneg hratio (hψ0 x hxcl)))
  have hupper := comparison_on_bounded_open hn Ω hb a b c u W hcoeff hc hu huc hW hWc
    (fun x hx => by
      rw [hLu x hx]
      exact (hLW x hx).trans (by have := (abs_le.mp (hf x hx)).1; linarith)) hbound
  have hnegative : ∀ x ∈ Ω, nondivergenceOperator a b c (fun y => -u y) x = -f x := by
    intro x hx
    have h := nondivergenceOperator_const_sub a b c u 0 x
    simpa only [zero_sub, mul_zero, hLu x hx] using h
  have hnbound : ∀ x ∈ frontier (Ω : Set (Space n)), -u x ≤ W x := by
    intro x hx
    have hxcl := frontier_subset_closure hx
    exact ((neg_le_abs _).trans (hboundary x hx)).trans
      (le_add_of_nonneg_left (mul_nonneg hratio (hψ0 x hxcl)))
  have hlower := comparison_on_bounded_open hn Ω hb a b c (fun y => -u y) W hcoeff hc
    hu.neg huc.neg hW hWc (fun x hx => by
      rw [hnegative x hx]
      exact (hLW x hx).trans (by have := (abs_le.mp (hf x hx)).2; linarith)) hnbound
  intro x hx
  exact abs_le.mpr ⟨by have := hlower x hx; dsimp [W] at this; linarith, hupper x hx⟩

/-- Uniform C⁰ control, with constants chosen before the coefficient fields,
source, boundary lift, and solution. No connectedness or smooth boundary is needed. -/
theorem uniform_c0_estimate {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α)
    (Ω : Domain n) (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
        (c u f G : Space n → ℝ),
        UniformlyEllipticOn ell a (closure (Ω : Set (Space n))) →
        CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))) →
        coefficientNormOn α a b c (closure (Ω : Set (Space n))) ≤ K →
        (∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0) →
        ContDiffOn ℝ 2 u Ω → ContinuousOn u (closure (Ω : Set (Space n))) →
        (∀ x ∈ Ω, nondivergenceOperator a b c u x = f x) →
        (∀ x ∈ frontier (Ω : Set (Space n)), u x = G x) →
        IsHolderOn α f (closure (Ω : Set (Space n))) →
        IsC2HolderUpToOn α G (closure (Ω : Set (Space n))) →
        supNormOn u (closure (Ω : Set (Space n))) ≤
          C * (holderNormOn α f (closure (Ω : Set (Space n))) +
            c2HolderUpToNormOn α G (closure (Ω : Set (Space n)))) := by
  obtain ⟨ψ, δ, A, hδ, hA, hψ, hψbound, hLψ⟩ :=
    exists_uniform_domain_barrier hn Ω hb hell hK
  refine ⟨A / δ + 1, by positivity, ?_⟩
  intro a b c u f G ha hcoeff hbound hc hu huc hLu htrace hf hG
  let s := closure (Ω : Set (Space n))
  let F := supNormOn f s
  let M := supNormOn G s
  have hF : 0 ≤ F := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hM : 0 ≤ M := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hfBounded : IsBoundedOn f s := by
    obtain ⟨N, H, hN, _, hb, _⟩ := hf
    exact ⟨N, hN, hb⟩
  have hpoint := classical_solution_barrier_bound hn Ω hb a b c u f ψ
    (ellipticCoefficients_of_holder hα hell Ω ha hcoeff)
    (fun x hx => hc x (subset_closure hx)) hu huc hLu hF hM hδ
    (fun x hx => P201.Elliptic.PoissonSchauder.norm_le_supNormOn hfBounded (subset_closure hx))
    (fun x hx => by rw [htrace x hx]; exact
      P201.Elliptic.PoissonSchauder.norm_le_supNormOn hG.2.1 (frontier_subset_closure hx))
    hψ (fun x hx => (hψbound x hx).1.le)
    (fun x hx => hLψ α a b c ha hcoeff hbound hc x (subset_closure hx))
  have hFnorm : F ≤ holderNormOn α f s := by
    change supNormOn f s ≤ supNormOn f s + holderSeminormOn α f s
    exact le_add_of_nonneg_right (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
  have hMnorm : M ≤ c2HolderUpToNormOn α G s := supNormOn_le_c2HolderUpToNormOn _ _ _
  have hf0 : 0 ≤ holderNormOn α f s :=
    (P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn hf).1
  have hG0 : 0 ≤ c2HolderUpToNormOn α G s := hM.trans hMnorm
  apply P201.Elliptic.NewtonHessian.supNormOn_le (mul_nonneg (by positivity) (add_nonneg hf0 hG0))
  intro x hx
  calc
    ‖u x‖ ≤ (F / δ) * ψ x + M := hpoint x hx
    _ ≤ (F / δ) * A + M := add_le_add
      (mul_le_mul_of_nonneg_left (hψbound x hx).2 (div_nonneg hF hδ.le)) (le_refl M)
    _ ≤ (A / δ) * holderNormOn α f s + c2HolderUpToNormOn α G s := by
      have hmul := mul_le_mul_of_nonneg_left hFnorm (div_nonneg hA.le hδ.le)
      have hcomm : (F / δ) * A = (A / δ) * F := by ring
      rw [hcomm]
      exact add_le_add hmul hMnorm
    _ ≤ (A / δ + 1) * (holderNormOn α f s + c2HolderUpToNormOn α G s) := by
      have := mul_nonneg (div_nonneg hA.le hδ.le) hG0
      nlinarith

/-- Combining the original global Schauder estimate with the slab-barrier
bound removes the solution's C⁰ norm for every existing lifted solution. -/
theorem global_estimate_without_c0
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasC2HolderBoundary α Ω) (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
        (b : Space (m + 1) → Space (m + 1)) (c f G u : Space (m + 1) → ℝ),
        UniformlyEllipticOn ell a (closure (Ω : Set (Space (m + 1)))) →
        CoefficientsHolderOn α a b c (closure (Ω : Set (Space (m + 1)))) →
        coefficientNormOn α a b c (closure (Ω : Set (Space (m + 1)))) ≤ K →
        (∀ x ∈ closure (Ω : Set (Space (m + 1))), c x ≤ 0) →
        IsHolderOn α f (closure (Ω : Set (Space (m + 1)))) →
        IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1)))) →
        IsDirichletSolution α Ω a b c f G u →
        c2HolderUpToNormOn α u (closure (Ω : Set (Space (m + 1)))) ≤
          C * (holderNormOn α f (closure (Ω : Set (Space (m + 1)))) +
            c2HolderUpToNormOn α G (closure (Ω : Set (Space (m + 1))))) := by
  obtain ⟨C0, hC0, hc0⟩ := uniform_c0_estimate (by omega) α hα Ω hb ell K hell hK
  obtain ⟨C1, hC1, hest⟩ := hglobal m α hα hα1 Ω hb hboundary ell K hell hK
  refine ⟨C1 * (C0 + 1), by positivity, ?_⟩
  intro a b c f G u ha hcoeff hbound hc hf hG hu
  have hsup := hc0 a b c u f G ha hcoeff hbound hc
    (hu.1.1.mono subset_closure) hu.1.1.continuousOn hu.2.1 hu.2.2 hf hG
  calc
    _ ≤ C1 * (supNormOn u (closure (Ω : Set _)) +
        holderNormOn α f (closure (Ω : Set _)) + c2HolderUpToNormOn α G (closure (Ω : Set _))) :=
      hest a b c ha hcoeff hbound u f G hu.1 hf hG hu.2.1 hu.2.2
    _ ≤ C1 * (C0 * (holderNormOn α f (closure (Ω : Set _)) +
        c2HolderUpToNormOn α G (closure (Ω : Set _))) +
        holderNormOn α f (closure (Ω : Set _)) + c2HolderUpToNormOn α G (closure (Ω : Set _))) :=
      mul_le_mul_of_nonneg_left (by linarith) hC1.le
    _ = _ := by ring

/-- A Perron subfunction lies below every ordered strict classical
supersolution. No connectedness, smooth outer boundary, or global existence
is assumed: only the continuous-data ball-solvability premise is used. -/
theorem subfunction_le_strict_supersolution
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) {Ω : Domain n}
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G v W : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space n))))
    (hv : IsSubfunction Ω a b c f G v)
    (hW : ContDiffOn ℝ 2 W Ω)
    (hWc : ContinuousOn W (closure (Ω : Set (Space n))))
    (hLW : ∀ x ∈ Ω, nondivergenceOperator a b c W x < f x)
    (hboundary : ∀ x ∈ frontier (Ω : Set (Space n)), v x ≤ W x) :
    ∀ x ∈ closure (Ω : Set (Space n)), v x ≤ W x := by
  intro x hx
  by_contra hnot
  have hxpos : 0 < v x - W x := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨z, hz, hmax⟩ := hb.isCompact_closure.exists_isMaxOn ⟨x, hx⟩ (hv.1.sub hWc)
  let M := v z - W z
  have hM : 0 < M := hxpos.trans_le (hmax hx)
  have hzΩ : z ∈ (Ω : Set (Space n)) := by
    by_contra hznot
    have hzfront : z ∈ frontier (Ω : Set (Space n)) := by
      rw [frontier, Ω.isOpen.interior_eq]
      exact ⟨hz, hznot⟩
    exact (sub_nonpos.mpr (hboundary z hzfront)).not_gt hM
  obtain ⟨r, hr, hB⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hzΩ)
  obtain ⟨V, hVsub, hraise, hV, hLV, hout⟩ := exists_subfunction_ballReplacement hcontinuous hn
    hα hα1 hell ha hcoeff hc hf hv hr hB
  let B : Domain n := ⟨ball z r, isOpen_ball⟩
  have hBΩ : (B : Set (Space n)) ⊆ (Ω : Set (Space n)) := ball_subset_closedBall.trans hB
  have hBcl : closure (B : Set (Space n)) = closedBall z r := closure_ball z hr.ne'
  have hcoeffΩ := ellipticCoefficients_of_holder hα hell Ω ha hcoeff
  have hcoeffB : EllipticCoefficients B a b c := ellipticCoefficients_mono hcoeffΩ hBΩ
  have hVcont : ContinuousOn V (closedBall z r) :=
    hVsub.1.mono (hB.trans subset_closure)
  have hcompare : ∀ y ∈ closure (B : Set (Space n)), V y ≤ W y + M := by
    apply comparison_on_bounded_open hn B isBounded_ball a b c V (fun y => W y + M)
      hcoeffB (fun y hy => hc y (subset_closure (hBΩ hy))) hV.1
      (hBcl ▸ hVcont) ((hW.mono hBΩ).add contDiffOn_const)
      ((hWc.mono (closure_mono hBΩ)).add continuousOn_const)
    · intro y hy
      rw [nondivergenceOperator_add_const, hLV y hy]
      exact (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg
        (hc y (subset_closure (hBΩ hy))) hM.le)).trans (hLW y (hBΩ hy)).le
    · intro y hy
      have hys : y ∈ sphere z r := frontier_ball_subset_sphere hy
      rw [hout y (fun hyball => (mem_ball.mp hyball).ne (mem_sphere.mp hys))]
      have hpoint := hmax (subset_closure (hB (sphere_subset_closedBall hys)))
      change v y - W y ≤ v z - W z at hpoint
      dsimp [M]
      linarith
  have hzB : z ∈ (B : Set (Space n)) := mem_ball_self hr
  have hcenter : V z - W z = M := by
    have hupper := hcompare z (subset_closure hzB)
    have hlower := hraise z
    dsimp [M] at *
    linarith
  have hlocal : IsLocalMax (fun y => V y - W y) z := by
    apply IsMaxOn.isLocalMax (s := (B : Set (Space n)))
    · intro y hy
      change V y - W y ≤ V z - W z
      rw [hcenter]
      have := hcompare y (subset_closure hy)
      linarith
    · exact B.isOpen.mem_nhds hzB
  have hnonpos := nondivergenceOperator_nonpos_at_positive_local_max hcoeffB
    (fun y hy => hc y (subset_closure (hBΩ hy)))
    (hV.1.sub (hW.mono hBΩ)) hzB hlocal (hcenter ▸ hM.le)
  have hdiff := nondivergenceOperator_mul_sub a b c hV.1 (hW.mono hBΩ) 1 hzB
  simp only [one_mul] at hdiff
  rw [hdiff, hLV z hzB] at hnonpos
  exact (sub_pos.mpr (hLW z hzΩ)).not_ge hnonpos

/-- The strict slab barrier gives a genuine subfunction and a common upper
bound for the entire Perron family. Only bounded boundary values are needed;
neither boundary smoothness nor a global solution is assumed. -/
theorem exists_perron_barriers
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell K : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hK : 0 ≤ K) {Ω : Domain n}
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hbound : coefficientNormOn α a b c (closure (Ω : Set (Space n))) ≤ K)
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space n))))
    (hG : IsBoundedOn G (frontier (Ω : Set (Space n)))) :
    ∃ (W : Space n → ℝ) (B : ℝ), 0 ≤ B ∧ ContDiff ℝ ⊤ W ∧
      (∀ x ∈ closure (Ω : Set (Space n)), 0 ≤ W x ∧ W x ≤ B) ∧
      IsSubfunction Ω a b c f G (fun x => -W x) ∧
      ∀ v : Space n → ℝ, IsSubfunction Ω a b c f G v →
        ∀ x ∈ closure (Ω : Set (Space n)), v x ≤ W x := by
  obtain ⟨ψ, δ, A, hδ, hA, hψ, hψbound, hLψ⟩ :=
    exists_uniform_domain_barrier hn Ω hb hell hK
  obtain ⟨F, H, hF, hH, hfBound, hfHolder⟩ := hf
  obtain ⟨M, hM, hGbound⟩ := hG
  let t : ℝ := (F + 1) / δ
  have ht : 0 ≤ t := div_nonneg (by linarith) hδ.le
  have htδ : t * δ = F + 1 := by dsimp [t]; field_simp
  let W : Space n → ℝ := fun x => t * ψ x + M
  have hW : ContDiff ℝ ⊤ W := (contDiff_const.mul hψ).add contDiff_const
  have hW2 : ContDiffOn ℝ 2 W Ω := hW.contDiffOn.of_le (by norm_num)
  have hψ2 : ContDiffOn ℝ 2 ψ Ω := hψ.contDiffOn.of_le (by norm_num)
  have hLW : ∀ x ∈ Ω, nondivergenceOperator a b c W x ≤ -(F + 1) := by
    intro x hx
    dsimp [W]
    rw [nondivergenceOperator_add_const, nondivergenceOperator_const_mul a b c hψ2 t hx]
    have h1 := mul_le_mul_of_nonneg_left
      (hLψ α a b c ha hcoeff hbound hc x (subset_closure hx)) ht
    have h2 := mul_nonpos_of_nonpos_of_nonneg (hc x (subset_closure hx)) hM
    nlinarith
  have hWlower : ∀ x ∈ closure (Ω : Set (Space n)), M ≤ W x := by
    intro x hx
    exact le_add_of_nonneg_left (mul_nonneg ht (hψbound x hx).1.le)
  have hWbound : ∀ x ∈ closure (Ω : Set (Space n)),
      0 ≤ W x ∧ W x ≤ t * A + M := by
    intro x hx
    refine ⟨hM.trans (hWlower x hx), ?_⟩
    simpa only [W, add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left (hψbound x hx).2 ht) M
  have hsub : IsSubfunction Ω a b c f G (fun x => -W x) := by
    apply isSubfunction_of_classical hn (ellipticCoefficients_of_holder hα hell Ω ha hcoeff)
      (fun x hx => hc x (subset_closure hx)) hW2.neg hW.continuous.continuousOn.neg
    · intro x hx
      have hneg := nondivergenceOperator_const_mul a b c hW2 (-1) hx
      simp only [neg_one_mul] at hneg
      rw [hneg]
      have := (abs_le.mp (hfBound x (subset_closure hx))).2
      have := hLW x hx
      linarith
    · intro x hx
      have := (abs_le.mp (hGbound x hx)).1
      have := hWlower x (frontier_subset_closure hx)
      linarith
  refine ⟨W, t * A + M, add_nonneg (mul_nonneg ht hA.le) hM, hW, hWbound, hsub, ?_⟩
  intro v hv
  apply subfunction_le_strict_supersolution hcontinuous hn hα hα1 hell hb ha hcoeff hc
    ⟨F, H, hF, hH, hfBound, hfHolder⟩ hv hW2 hW.continuous.continuousOn
  · intro x hx
    have := (abs_le.mp (hfBound x (subset_closure hx))).1
    have := hLW x hx
    linarith
  · intro x hx
    exact (hv.2.1 x hx).trans (((abs_le.mp (hGbound x hx)).2).trans
      (hWlower x (frontier_subset_closure hx)))

/-- The real-valued Perron envelope. Finiteness claims are made only on the
closed domain and with a proved common bound for the subfunction family. -/
def perronEnvelope {n : ℕ} (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c f G : Space n → ℝ) (x : Space n) : ℝ :=
  sSup {r : ℝ | ∃ v : Space n → ℝ, IsSubfunction Ω a b c f G v ∧ r = v x}

/-- Each subfunction is bounded by the envelope once its pointwise family is
bounded above. This lemma does not assume that the envelope solves the PDE. -/
theorem le_perronEnvelope {n : ℕ} {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G v : Space n → ℝ} {x : Space n}
    (hbounded : BddAbove {r : ℝ | ∃ w : Space n → ℝ,
      IsSubfunction Ω a b c f G w ∧ r = w x})
    (hv : IsSubfunction Ω a b c f G v) :
    v x ≤ perronEnvelope Ω a b c f G x :=
  le_csSup hbounded ⟨v, hv, rfl⟩

/-- Supremum construction and lower semicontinuity, with all finiteness
hypotheses explicit. The bounds may depend on the source and boundary data. -/
theorem perronEnvelope_bounds_and_lowerSemicontinuous {n : ℕ} {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G v₀ W : Space n → ℝ}
    (hv₀ : IsSubfunction Ω a b c f G v₀)
    (hupper : ∀ v : Space n → ℝ, IsSubfunction Ω a b c f G v →
      ∀ x ∈ closure (Ω : Set (Space n)), v x ≤ W x) :
    (∀ x ∈ closure (Ω : Set (Space n)),
      v₀ x ≤ perronEnvelope Ω a b c f G x ∧ perronEnvelope Ω a b c f G x ≤ W x) ∧
      LowerSemicontinuousOn (perronEnvelope Ω a b c f G) (closure (Ω : Set (Space n))) := by
  have hne (x : Space n) : {r : ℝ | ∃ v : Space n → ℝ,
      IsSubfunction Ω a b c f G v ∧ r = v x}.Nonempty := ⟨v₀ x, v₀, hv₀, rfl⟩
  have hbounded (x : Space n) (hx : x ∈ closure (Ω : Set (Space n))) :
      BddAbove {r : ℝ | ∃ v : Space n → ℝ, IsSubfunction Ω a b c f G v ∧ r = v x} := by
    refine ⟨W x, ?_⟩
    rintro r ⟨v, hv, rfl⟩
    exact hupper v hv x hx
  refine ⟨?_, ?_⟩
  · intro x hx
    refine ⟨le_perronEnvelope (hbounded x hx) hv₀, csSup_le (hne x) ?_⟩
    rintro r ⟨v, hv, rfl⟩
    exact hupper v hv x hx
  · intro x hx r hr
    obtain ⟨t, ⟨v, hv, rfl⟩, hrv⟩ := exists_lt_of_lt_csSup (hne x) hr
    filter_upwards [hv.1.lowerSemicontinuousOn x hx r hrv,
      self_mem_nhdsWithin] with y hy hycl
    exact hy.trans_le (le_perronEnvelope (hbounded y hycl) hv)

/-- At any point one may approximate the finite envelope from below by an
actual subfunction, without assuming existence of a global classical solution. -/
theorem exists_subfunction_gt_perronEnvelope_sub {n : ℕ} {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G : Space n → ℝ}
    (hne : ∃ v : Space n → ℝ, IsSubfunction Ω a b c f G v)
    (x : Space n) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Space n → ℝ, IsSubfunction Ω a b c f G v ∧
      perronEnvelope Ω a b c f G x - ε < v x := by
  obtain ⟨v₀, hv₀⟩ := hne
  have hnonempty : {r : ℝ | ∃ v : Space n → ℝ,
      IsSubfunction Ω a b c f G v ∧ r = v x}.Nonempty := ⟨v₀ x, v₀, hv₀, rfl⟩
  obtain ⟨t, ⟨v, hv, rfl⟩, ht⟩ := exists_lt_of_lt_csSup hnonempty
    (sub_lt_self (perronEnvelope Ω a b c f G x) hε)
  exact ⟨v, hv, ht⟩

section ExteriorGeometry

/-- A quadratic lower support estimate gives a strictly touching exterior
sphere, in any real inner product space, with no finite-dimensional hypothesis. -/
theorem distance_gt_radius_of_quadratic_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p x ν : E) (A r : ℝ) (hν : ‖ν‖ = 1)
    (hr : 0 < r) (hsmall : 2 * r * A < 1)
    (hsupport : -A * ‖x - p‖ ^ 2 ≤ ⟪x - p, ν⟫_ℝ) (hxp : x ≠ p) :
    r < dist x (p - r • ν) := by
  have hdist : dist x (p - r • ν) ^ 2 =
      ‖x - p‖ ^ 2 + 2 * r * ⟪x - p, ν⟫_ℝ + r ^ 2 := by
    rw [dist_eq_norm]
    have heq : x - (p - r • ν) = (x - p) + r • ν := by abel
    rw [heq, norm_add_sq_real, real_inner_smul_right, norm_smul, hν]
    simp only [Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hpos : 0 < ‖x - p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxp))
  have hscaled := mul_le_mul_of_nonneg_left hsupport (show 0 ≤ 2 * r by positivity)
  have hprod := mul_pos (show 0 < 1 - 2 * r * A by linarith) hpos
  have hsq : r ^ 2 < dist x (p - r • ν) ^ 2 := by nlinarith [hdist]
  nlinarith [dist_nonneg (x := x) (y := p - r • ν)]

/-- Uniform quadratic lower support on a set gives a closed exterior ball
whose only possible contact with that set is its prescribed point. -/
theorem closedBall_inter_eq_singleton_of_quadratic_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Set E) (p ν : E) (A r : ℝ) (hp : p ∈ s) (hν : ‖ν‖ = 1)
    (hr : 0 < r) (hsmall : 2 * r * A < 1)
    (hsupport : ∀ x ∈ s, -A * ‖x - p‖ ^ 2 ≤ ⟪x - p, ν⟫_ℝ) :
    Metric.closedBall (p - r • ν) r ∩ s = {p} := by
  ext x
  constructor
  · rintro ⟨hxB, hxs⟩
    by_contra hxp
    have hne : x ≠ p := by simpa using hxp
    exact (not_lt.mpr hxB) (distance_gt_radius_of_quadratic_support p x ν A r hν hr hsmall
      (hsupport x hxs) hne)
  · intro hx
    have hxp : x = p := by simpa using hx
    subst x
    refine ⟨?_, hp⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : p - (p - r • ν) = r • ν := by abel
    rw [heq, norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos hr]

/-- The same exterior sphere conclusion needs quadratic support only in a
neighborhood of the contact point. The smaller sphere misses the far part
by the triangle inequality. -/
theorem closedBall_inter_eq_singleton_of_local_quadratic_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Set E) (p ν : E) (A r ε : ℝ) (hp : p ∈ s) (hν : ‖ν‖ = 1)
    (hr : 0 < r) (hsmall : 2 * r * A < 1) (hlocal : 2 * r < ε)
    (hsupport : ∀ x ∈ s ∩ Metric.ball p ε,
      -A * ‖x - p‖ ^ 2 ≤ ⟪x - p, ν⟫_ℝ) :
    Metric.closedBall (p - r • ν) r ∩ s = {p} := by
  have hcenter : dist (p - r • ν) p = r := by
    rw [dist_eq_norm]
    have heq : (p - r • ν) - p = -(r • ν) := by abel
    rw [heq, norm_neg, norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  ext x
  constructor
  · rintro ⟨hxB, hxs⟩
    have hdist : dist x p < ε := by
      have ht := dist_triangle x (p - r • ν) p
      rw [hcenter] at ht
      have hb : dist x (p - r • ν) ≤ r := hxB
      linarith
    by_contra hxp
    have hne : x ≠ p := by simpa using hxp
    exact (not_lt.mpr hxB) (distance_gt_radius_of_quadratic_support p x ν A r hν hr hsmall
      (hsupport x ⟨hxs, hdist⟩) hne)
  · intro hx
    have hxp : x = p := by simpa using hx
    subst x
    refine ⟨?_, hp⟩
    rw [Metric.mem_closedBall, dist_comm, hcenter]


/-- A Lipschitz derivative gives the quadratic graph remainder bound needed
for the exterior-sphere construction. No sharp factor 1/2 is required. -/
theorem quadratic_remainder_of_lipschitz_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (f' : E → E →L[ℝ] F) (p x : E) (K : ℝ≥0)
    (hf : ∀ z ∈ segment ℝ p x, HasFDerivAt f (f' z) z)
    (hLip : LipschitzOnWith K f' (segment ℝ p x)) :
    ‖f x - f p - f' p (x - p)‖ ≤ K * ‖x - p‖ ^ 2 := by
  have hderiv : ∀ z ∈ segment ℝ p x,
      HasFDerivWithinAt (fun y => f y - f' p y)
        (f' z - f' p) (segment ℝ p x) z := by
    intro z hz
    exact ((hf z hz).sub (f' p).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ segment ℝ p x,
      ‖f' z - f' p‖ ≤ (K : ℝ) * ‖x - p‖ := by
    intro z hz
    exact (hLip.norm_sub_le hz (left_mem_segment ℝ p x)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have h := (convex_segment p x).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hbound (left_mem_segment ℝ p x) (right_mem_segment ℝ p x)
  simpa only [map_sub, sub_sub_sub_comm, pow_two, mul_assoc] using h

/-- Every genuinely C² graph has a quadratic Taylor bound near its center. -/
theorem exists_local_quadratic_remainder_of_contDiffAt_two
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (p : E) (hf : ContDiffAt ℝ 2 f p) :
    ∃ (K : ℝ≥0) (r : ℝ), 0 < r ∧ ∀ x ∈ Metric.ball p r,
      ‖f x - f p - fderiv ℝ f p (x - p)‖ ≤ K * ‖x - p‖ ^ 2 := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) p := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hLip⟩ := hdf.exists_lipschitzOnWith
  have hd : ∀ᶠ z in nhds p, DifferentiableAt ℝ f z :=
    (hf.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hd)
  refine ⟨K, r, hr, ?_⟩
  intro x hx
  have hseg : segment ℝ p x ⊆ Metric.ball p r :=
    (convex_ball p r).segment_subset (Metric.mem_ball_self hr) hx
  apply quadratic_remainder_of_lipschitz_derivative f (fderiv ℝ f) p x K
  · intro z hz
    exact (hball (hseg hz)).2.hasFDerivAt
  · exact hLip.mono (fun z hz => (hball (hseg hz)).1)


/-- A C² local defining function with nonzero derivative provides a globally
strict exterior tangent sphere for the entire set. -/
theorem exists_exterior_sphere_of_local_defining_function
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (s : Set E) (p : E) (F : E → ℝ) (hp : p ∈ s)
    (hF : ContDiffAt ℝ 2 F p) (hdF : fderiv ℝ F p ≠ 0)
    (hsign : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s ∩ Metric.ball p δ, F p ≤ F x) :
    ∃ (y : E) (r : ℝ), 0 < r ∧ dist p y = r ∧
      Metric.closedBall y r ∩ s = {p} := by
  obtain ⟨K, ρ, hρ, hTaylor⟩ := exists_local_quadratic_remainder_of_contDiffAt_two F p hF
  obtain ⟨δ, hδ, hsign⟩ := hsign
  let g : E := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F p)
  have hg : g ≠ 0 := by
    intro h
    apply hdF
    have hi := congrArg (InnerProductSpace.toDual ℝ E) h
    simpa [g] using hi
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  let ν : E := ‖g‖⁻¹ • g
  have hν : ‖ν‖ = 1 := by
    dsimp [ν]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hgn.le), inv_mul_cancel₀ hgn.ne']
  let A : ℝ := (K : ℝ) / ‖g‖
  have hA : 0 ≤ A := div_nonneg K.coe_nonneg hgn.le
  let ε : ℝ := min δ ρ
  have hε : 0 < ε := lt_min hδ hρ
  have hsupp : ∀ x ∈ s ∩ Metric.ball p ε,
      -A * ‖x - p‖ ^ 2 ≤ ⟪x - p, ν⟫_ℝ := by
    intro x hx
    have hxδ : x ∈ Metric.ball p δ := Metric.ball_subset_ball (min_le_left δ ρ) hx.2
    have hxρ : x ∈ Metric.ball p ρ := Metric.ball_subset_ball (min_le_right δ ρ) hx.2
    have hT := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hTaylor x hxρ)).2
    have hS := hsign x ⟨hx.1, hxδ⟩
    have hraw : -(K : ℝ) * ‖x - p‖ ^ 2 ≤ fderiv ℝ F p (x - p) := by linarith
    have hInner : ⟪x - p, ν⟫_ℝ = ‖g‖⁻¹ * fderiv ℝ F p (x - p) := by
      dsimp [ν, g]
      rw [real_inner_smul_right, real_inner_comm,
        InnerProductSpace.toDual_symm_apply]
    rw [hInner]
    have hm := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hgn.le)
    dsimp [A]
    convert hm using 1 <;> ring
  let r : ℝ := min (ε / 4) (1 / (4 * (A + 1)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrε : 2 * r < ε := by
    have := min_le_left (ε / 4) (1 / (4 * (A + 1)))
    dsimp [r] at *
    linarith
  have hrA : 2 * r * A < 1 := by
    have hrle : r ≤ 1 / (4 * (A + 1)) := min_le_right _ _
    have hden : 0 < 4 * (A + 1) := by positivity
    have hprod : r * (4 * (A + 1)) ≤ 1 := (le_div_iff₀ hden).mp hrle
    nlinarith
  refine ⟨p - r • ν, r, hr, ?_, ?_⟩
  · rw [dist_eq_norm]
    have heq : p - (p - r • ν) = r • ν := by abel
    rw [heq, norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  · exact closedBall_inter_eq_singleton_of_local_quadratic_support
      s p ν A r ε hp hν hr hrA hrε hsupp


open Set Metric
open P201Specs P201Specs.Elliptic P201Specs.Elliptic.HalfSpaceLift
open P201Specs.Elliptic.VariableSchauder
open P201.Elliptic.ChartSchauder P201.Elliptic.HalfSpaceLift
open P102.Sobolev.Geometry P102.U4.GraphPieces

/-- The actual one-sided C²,α graph-chart boundary has strict exterior
spheres at every boundary point, including dimension one. -/
theorem exists_strict_exterior_sphere_of_hasC2HolderBoundary
    {m : ℕ} {α : ℝ} {Ω : P201Specs.Domain (m + 1)}
    (hboundary : HasC2HolderBoundary α Ω)
    {p : P201Specs.Space (m + 1)}
    (hp : p ∈ frontier (Ω : Set (P201Specs.Space (m + 1)))) :
    ∃ (y : P201Specs.Space (m + 1)) (r : ℝ), 0 < r ∧ dist p y = r ∧
      closedBall y r ∩ closure (Ω : Set (P201Specs.Space (m + 1))) = {p} := by
  obtain ⟨C, hCp, hC⟩ := hboundary p hp (mem_univ p)
  change chartPoint C = p at hCp
  have hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius) := hC.1
  have hbase : ((graphFrame m).symm (0 : P201Specs.Space (m + 1)) +
      WithLp.toLp 2 (C.center, (0 : ℝ))).ofLp.1 ∈ ball C.center C.radius := by
    simpa only [map_zero, zero_add, WithLp.ofLp_toLp] using mem_ball_self C.radius_pos
  have hibase : (C.frame.symm ((graphFrame m).symm (chartPoint C))).ofLp.1 ∈
      ball C.center C.radius := by
    simp only [chartPoint, LinearIsometryEquiv.symm_apply_apply,
      AffineIsometryEquiv.symm_apply_apply, graph, WithLp.ofLp_toLp]
    exact mem_ball_self C.radius_pos
  let e := chartParametrization C
  let F : P201Specs.Space (m + 1) → ℝ := fun x => height (e.symm x)
  have he0 : e (0 : P201Specs.Space (m + 1)) = chartPoint C := chartParametrization_zero C
  have hInv : ContDiffAt ℝ 2 (e.symm : P201Specs.Space (m + 1) →
      P201Specs.Space (m + 1)) (chartPoint C) :=
    chartParametrization_symm_contDiffAt C hγ hibase
  have he : ContDiffAt ℝ 2 (e : P201Specs.Space (m + 1) →
      P201Specs.Space (m + 1)) 0 := chartParametrization_contDiffAt C hγ hbase
  have hF : ContDiffAt ℝ 2 F (chartPoint C) :=
    ((height_contDiff m).of_le (show (2 : WithTop ℕ∞) ≤ ⊤ from le_top)).contDiffAt.comp _ hInv
  have hFzero : F (chartPoint C) = 0 := by
    change height ((chartParametrization C).symm (chartPoint C)) = 0
    rw [chartParametrization_symm_center]
    rfl
  have hdF : fderiv ℝ F (chartPoint C) ≠ 0 := by
    intro hzero
    have hF' : DifferentiableAt ℝ F (e 0) := by
      rw [he0]
      exact hF.differentiableAt (by norm_num)
    have hchain := fderiv_comp (0 : P201Specs.Space (m + 1)) hF'
      (he.differentiableAt (by norm_num))
    have heq : (F ∘ e : P201Specs.Space (m + 1) → ℝ) = @height m := by
      funext x
      simp only [Function.comp_apply, F, Equiv.symm_apply_apply]
    rw [heq, he0, hzero, ContinuousLinearMap.zero_comp] at hchain
    have hderiv : fderiv ℝ (@height m) (0 : P201Specs.Space (m + 1)) =
        PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).fderiv
    rw [hderiv] at hchain
    have hval := congrArg (fun L : P201Specs.Space (m + 1) →L[ℝ] ℝ =>
      L (coordinate (m + 1) (Fin.last m))) hchain
    change height (coordinate (m + 1) (Fin.last m)) = 0 at hval
    rw [height_coordinate_last] at hval
    norm_num at hval
  obtain ⟨_, R, _, hR, _, _, hchart⟩ :=
    chart_radii C isOpen_univ (mem_univ (chartPoint C))
  have hRpos : 0 < R := lt_trans (by positivity) hR
  obtain ⟨ρ, hρ, _, hρmap⟩ := exists_physical_inner_radius C hγ hRpos zero_lt_one hchart
  have hsign : ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ closure (Ω : Set (P201Specs.Space (m + 1))) ∩ ball (chartPoint C) δ,
        F (chartPoint C) ≤ F x := by
    refine ⟨ρ, hρ, ?_⟩
    intro x hx
    rw [hFzero]
    exact (hρmap hx).2
  have hpclosure : chartPoint C ∈ closure (Ω : Set (P201Specs.Space (m + 1))) :=
    hCp.symm ▸ frontier_subset_closure hp
  obtain ⟨y, r, hr, hd, hi⟩ := exists_exterior_sphere_of_local_defining_function
    (closure (Ω : Set (P201Specs.Space (m + 1)))) (chartPoint C) F hpclosure hF hdF hsign
  exact ⟨y, r, hr, hCp ▸ hd, hCp ▸ hi⟩


/-- Numeric form of strict exterior contact, convenient for radial barriers. -/
theorem exists_exterior_sphere_distance_bounds
    {m : ℕ} {α : ℝ} {Ω : P201Specs.Domain (m + 1)}
    (hboundary : HasC2HolderBoundary α Ω)
    {p : P201Specs.Space (m + 1)}
    (hp : p ∈ frontier (Ω : Set (P201Specs.Space (m + 1)))) :
    ∃ (y : P201Specs.Space (m + 1)) (r : ℝ), 0 < r ∧ dist p y = r ∧
      ∀ x ∈ closure (Ω : Set (P201Specs.Space (m + 1))),
        r ≤ dist x y ∧ (x ≠ p → r < dist x y) := by
  obtain ⟨y, r, hr, hpdist, hi⟩ :=
    exists_strict_exterior_sphere_of_hasC2HolderBoundary hboundary hp
  refine ⟨y, r, hr, hpdist, ?_⟩
  intro x hx
  by_cases hxp : x = p
  · subst x
    exact ⟨hpdist.ge, fun h => (h rfl).elim⟩
  · have hstrict : r < dist x y := by
      by_contra hnot
      have hmem : x ∈ closedBall y r ∩ closure (Ω : Set (P201Specs.Space (m + 1))) :=
        ⟨not_lt.mp hnot, hx⟩
      rw [hi] at hmem
      exact hxp (by simpa using hmem)
    exact ⟨hstrict.le, fun _ => hstrict⟩

end ExteriorGeometry

namespace Compactness

theorem equicontinuous_of_holder_bound
    {I X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {v : I → X → Y} {α H : ℝ} (hα : 0 < α)
    (hv : ∀ k x y, ‖v k x - v k y‖ ≤ H * dist x y ^ α) :
    Equicontinuous v := by
  have hmod : Tendsto (fun t : ℝ => H * t ^ α) (𝓝 0) (𝓝 0) := by
    convert tendsto_const_nhds.mul (Real.continuousAt_rpow_const 0 α (.inr hα.le)) using 1
    simp [Real.zero_rpow hα.ne']
  exact Metric.equicontinuous_of_continuity_modulus _ hmod v
    (fun x y k => by simpa only [dist_eq_norm] using hv k x y)

theorem TendstoUniformly.subsequence
    {X Y : Type*} [UniformSpace Y] {v : ℕ → X → Y} {w : X → Y}
    (h : TendstoUniformly v w atTop) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoUniformly (fun k => v (φ k)) w atTop :=
  fun U hU => hφ.tendsto_atTop.eventually (h U hU)

/-- A sequential form of Arzelà--Ascoli for a uniformly bounded family. -/
theorem exists_uniformly_convergent_subseq
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Y] [ProperSpace Y]
    (v : ℕ → X → Y) (hv : ∀ k, Continuous (v k))
    (heq : Equicontinuous v) (y : Y) (M : ℝ)
    (hb : ∀ k x, dist (v k x) y ≤ M) :
    ∃ w : X → Y, Continuous w ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly (fun k => v (φ k)) w atTop := by
  let V : ℕ → BoundedContinuousFunction X Y := fun k =>
    BoundedContinuousFunction.mkOfCompact ⟨v k, hv k⟩
  have hV : Equicontinuous ((↑) : range V → X → Y) := by
    classical
    convert heq.comp (rangeSplitting V) using 1
    funext f x
    exact congrArg (fun g : BoundedContinuousFunction X Y => g x)
      (apply_rangeSplitting V f).symm
  have hcomp : IsCompact (closure (range V)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall y M) (isCompact_closedBall y M)
      (range V) (by
        rintro f x ⟨k, rfl⟩
        exact hb k x) hV
  obtain ⟨w, _, φ, hφ, hlim⟩ := hcomp.tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  exact ⟨w, w.continuous, φ, hφ,
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim⟩

theorem exists_uniformly_convergent_subseq_three
    {X Y₀ Y₁ Y₂ : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup Y₀] [ProperSpace Y₀]
    [NormedAddCommGroup Y₁] [ProperSpace Y₁]
    [NormedAddCommGroup Y₂] [ProperSpace Y₂]
    (v₀ : ℕ → X → Y₀) (v₁ : ℕ → X → Y₁) (v₂ : ℕ → X → Y₂)
    (hc₀ : ∀ k, Continuous (v₀ k)) (hc₁ : ∀ k, Continuous (v₁ k))
    (hc₂ : ∀ k, Continuous (v₂ k))
    (heq₀ : Equicontinuous v₀) (heq₁ : Equicontinuous v₁)
    (heq₂ : Equicontinuous v₂) (M₀ M₁ M₂ : ℝ)
    (hb₀ : ∀ k x, ‖v₀ k x‖ ≤ M₀) (hb₁ : ∀ k x, ‖v₁ k x‖ ≤ M₁)
    (hb₂ : ∀ k x, ‖v₂ k x‖ ≤ M₂) :
    ∃ w₀ w₁ w₂, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun k => v₀ (φ k)) w₀ atTop ∧
      TendstoUniformly (fun k => v₁ (φ k)) w₁ atTop ∧
      TendstoUniformly (fun k => v₂ (φ k)) w₂ atTop := by
  obtain ⟨w₀, _, φ₀, hφ₀, hlim₀⟩ := exists_uniformly_convergent_subseq
    v₀ hc₀ heq₀ 0 M₀ (by simpa only [dist_zero_right] using hb₀)
  obtain ⟨w₁, _, φ₁, hφ₁, hlim₁⟩ := exists_uniformly_convergent_subseq
    (fun k => v₁ (φ₀ k)) (fun k => hc₁ _) (heq₁.comp φ₀) 0 M₁
    (by simpa only [dist_zero_right] using fun k => hb₁ (φ₀ k))
  obtain ⟨w₂, _, φ₂, hφ₂, hlim₂⟩ := exists_uniformly_convergent_subseq
    (fun k => v₂ (φ₀ (φ₁ k))) (fun k => hc₂ _) ((heq₂.comp φ₀).comp φ₁) 0 M₂
    (by simpa only [dist_zero_right] using fun k => hb₂ (φ₀ (φ₁ k)))
  exact ⟨w₀, w₁, w₂, φ₀ ∘ φ₁ ∘ φ₂, hφ₀.comp (hφ₁.comp hφ₂),
    TendstoUniformly.subsequence (TendstoUniformly.subsequence hlim₀ hφ₁) hφ₂,
    TendstoUniformly.subsequence hlim₁ hφ₂, hlim₂⟩

/-- Uniform limits preserve one fixed Hölder constant. -/
theorem holder_bound_of_pointwise_limit
    {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {v : ℕ → X → Y} {w : X → Y} {s : Set X} {α H : ℝ}
    (hv : ∀ k x, x ∈ s → ∀ y, y ∈ s →
      ‖v k x - v k y‖ ≤ H * dist x y ^ α)
    (hw : ∀ x ∈ s, Tendsto (fun k => v k x) atTop (𝓝 (w x))) :
    ∀ x ∈ s, ∀ y ∈ s, ‖w x - w y‖ ≤ H * dist x y ^ α := by
  intro x hx y hy
  exact le_of_tendsto ((hw x hx).sub (hw y hy)).norm
    (Filter.Eventually.of_forall (fun k => hv k x hx y hy))

/-- Convergent first and second derivative fields identify a C² limit.
The derivative fields here are genuine Fréchet derivatives, with no
regularity certificate postulated for the limit function. -/
theorem contDiffOn_two_of_uniform_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u : ℕ → E → F} {u₁ : ℕ → E → E →L[ℝ] F}
    {u₂ : ℕ → E → E →L[ℝ] E →L[ℝ] F}
    {w : E → F} {w₁ : E → E →L[ℝ] F}
    {w₂ : E → E →L[ℝ] E →L[ℝ] F} {s : Set E}
    (hs : IsOpen s)
    (hu₁ : ∀ k x, x ∈ s → HasFDerivAt (u k) (u₁ k x) x)
    (hu₂ : ∀ k x, x ∈ s → HasFDerivAt (u₁ k) (u₂ k x) x)
    (hc₂ : ∀ k, ContinuousOn (u₂ k) s)
    (hlim : ∀ x ∈ s, Tendsto (fun k => u k x) atTop (𝓝 (w x)))
    (hlim₁ : TendstoUniformlyOn u₁ w₁ atTop s)
    (hlim₂ : TendstoUniformlyOn u₂ w₂ atTop s) :
    ContDiffOn ℝ 2 w s ∧
      (∀ x ∈ s, HasFDerivAt w (w₁ x) x) ∧
      ∀ x ∈ s, HasFDerivAt w₁ (w₂ x) x := by
  have hw₁ : ∀ x ∈ s, HasFDerivAt w (w₁ x) x :=
    fun x hx => hasFDerivAt_of_tendstoUniformlyOn hs hlim₁ hu₁ hlim hx
  have hw₂ : ∀ x ∈ s, HasFDerivAt w₁ (w₂ x) x :=
    fun x hx => hasFDerivAt_of_tendstoUniformlyOn hs hlim₂ hu₂
      (fun x hx => hlim₁.tendsto_at hx) hx
  have hcw₂ : ContinuousOn w₂ s := hlim₂.continuousOn (Frequently.of_forall hc₂)
  have hcw₁ : ContDiffOn ℝ 1 w₁ s := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (n := 0) hs.uniqueDiffOn).mpr
    exact ⟨by simp, w₂, by simpa using hcw₂,
      fun x hx => (hw₂ x hx).hasFDerivWithinAt⟩
  have hcw : ContDiffOn ℝ 2 w s := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (n := 1) hs.uniqueDiffOn).mpr
    exact ⟨by simp, w₁, hcw₁, fun x hx => (hw₁ x hx).hasFDerivWithinAt⟩
  exact ⟨hcw, hw₁, hw₂⟩

end Compactness

namespace PerronCompactness
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201.Elliptic.PoissonSchauder
open P201.Elliptic.ChartSchauder Compactness

def zeroExtension {X Y : Type*} [Zero Y] (s : Set X) (v : s → Y) (x : X) : Y := by
  classical
  exact if h : x ∈ s then v ⟨x, h⟩ else 0

theorem zeroExtension_apply {X Y : Type*} [Zero Y] (s : Set X) (v : s → Y)
    (x : s) : zeroExtension s v x = v x := by
  simp [zeroExtension, x.property]

theorem exists_c2_limit_on_inner_ball
    {n : ℕ} {α N r R : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hN : 0 ≤ N) (hrR : r < R) (z : Space n)
    (u : ℕ → Space n → ℝ)
    (hu : ∀ k, IsC2HolderOn α (u k) (ball z R))
    (hNorm : ∀ k, c2HolderNormOn α (u k) (ball z R) ≤ N) :
    ∃ w : Space n → ℝ, ∃ w₁ : Space n → Space n →L[ℝ] ℝ,
      ∃ w₂ : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContDiffOn ℝ 2 w (ball z r) ∧
        TendstoUniformlyOn (fun k => u (φ k)) w atTop (ball z r) ∧
        TendstoUniformlyOn (fun k => fderiv ℝ (u (φ k))) w₁ atTop (ball z r) ∧
        TendstoUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (u (φ k))))
          w₂ atTop (ball z r) ∧
        (∀ x ∈ ball z r, HasFDerivAt w (w₁ x) x) ∧
        ∀ x ∈ ball z r, HasFDerivAt w₁ (w₂ x) x := by
  let s := closedBall z r
  have hs : IsCompact s := isCompact_closedBall z r
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hsB : s ⊆ ball z R := closedBall_subset_ball hrR
  have hbB : ball z r ⊆ s := ball_subset_closedBall
  have hureg₁ (k : ℕ) : ContDiffOn ℝ 1 (fderiv ℝ (u k)) (ball z R) :=
    (hu k).1.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hureg₂ (k : ℕ) : ContinuousOn (fderiv ℝ (fderiv ℝ (u k))) (ball z R) :=
    ((hureg₁ k).fderiv_of_isOpen isOpen_ball (m := 0) (by norm_num)).continuousOn
  have hd (k : ℕ) := c2Holder_fderiv_bounds hα.le hα1.le isOpen_ball
    (convex_ball z R) (hu k)
  have hb₀ (k : ℕ) (x : s) : ‖u k x‖ ≤ N :=
    (norm_le_supNormOn (hu k).2.1 (hsB x.property)).trans
      ((c2HolderNormOn_components α (u k) (ball z R)).1.trans (hNorm k))
  have hb₁ (k : ℕ) (x : s) : ‖fderiv ℝ (u k) x‖ ≤ (n : ℝ) * N :=
    (hd k).1 x (hsB x.property) |>.trans
      (mul_le_mul_of_nonneg_left (hNorm k) (by positivity))
  have hb₂ (k : ℕ) (x : s) :
      ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ (n : ℝ)^2 * N :=
    (hd k).2.2.1 x (hsB x.property) |>.trans
      (mul_le_mul_of_nonneg_left (hNorm k) (by positivity))
  have hh₀ (k : ℕ) (x y : s) : ‖u k x - u k y‖ ≤
      ((n : ℝ) + 3) * N * dist x y ^ α := by
    have hb (a : Space n) (ha : a ∈ ball z R) : ‖u k a‖ ≤
        c2HolderNormOn α (u k) (ball z R) :=
      (norm_le_supNormOn (hu k).2.1 ha).trans
        (c2HolderNormOn_components α (u k) (ball z R)).1
    have hfirst (i : Fin n) (a : Space n) (ha : a ∈ ball z R) :
        ‖firstPartial (u k) i a‖ ≤ c2HolderNormOn α (u k) (ball z R) := by
      rw [P201.Elliptic.ConstantSchauder.firstPartial_eq_multiPartial]
      exact (norm_le_supNormOn ((hu k).2.2.1 i) ha).trans
        ((c2HolderNormOn_components α (u k) (ball z R)).2.1 i)
    obtain ⟨hh, hhh⟩ := holder_of_coordinate_gradient_on hα.le hα1.le
      (c2HolderNormOn_nonneg α (u k) (ball z R))
      (fun a ha => (((hu k).1 a ha).contDiffAt
        (isOpen_ball.mem_nhds ha)).differentiableAt (by norm_num))
      (convex_ball z R) hb hfirst
    exact ((holder_bounds_by_normOn hh).2.2 x (hsB x.property) y (hsB y.property)).trans
      (mul_le_mul_of_nonneg_right (hhh.trans
        (mul_le_mul_of_nonneg_left (hNorm k) (by positivity)))
        (Real.rpow_nonneg dist_nonneg α))
  have hh₁ (k : ℕ) (x y : s) : ‖fderiv ℝ (u k) x - fderiv ℝ (u k) y‖ ≤
      (n : ℝ) * ((n : ℝ)+3) * N * dist x y ^ α :=
    ((hd k).2.1 x (hsB x.property) y (hsB y.property)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hNorm k) (by positivity))
        (Real.rpow_nonneg dist_nonneg α))
  have hh₂ (k : ℕ) (x y : s) :
      ‖fderiv ℝ (fderiv ℝ (u k)) x - fderiv ℝ (fderiv ℝ (u k)) y‖ ≤
      (n : ℝ)^2 * N * dist x y ^ α :=
    ((hd k).2.2.2 x (hsB x.property) y (hsB y.property)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hNorm k) (by positivity))
        (Real.rpow_nonneg dist_nonneg α))
  obtain ⟨v, v₁, v₂, φ, hφ, hlim, hlim₁, hlim₂⟩ :=
    exists_uniformly_convergent_subseq_three
      (fun k (x : s) => u k x) (fun k (x : s) => fderiv ℝ (u k) x)
      (fun k (x : s) => fderiv ℝ (fderiv ℝ (u k)) x)
      (fun k => ((hu k).1.continuousOn.mono hsB).domRestrict)
      (fun k => ((hureg₁ k).continuousOn.mono hsB).domRestrict)
      (fun k => by exact ((hureg₂ k).mono hsB).domRestrict)
      (equicontinuous_of_holder_bound hα hh₀)
      (equicontinuous_of_holder_bound hα hh₁)
      (equicontinuous_of_holder_bound hα hh₂)
      N ((n : ℝ)*N) ((n : ℝ)^2*N) hb₀ hb₁ hb₂
  let w := zeroExtension s v
  let w₁ := zeroExtension s v₁
  let w₂ := zeroExtension s v₂
  have hl : TendstoUniformlyOn (fun k => u (φ k)) w atTop (ball z r) := by
    apply TendstoUniformlyOn.mono (s := s) _ hbB
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have heq : zeroExtension s v ∘ Subtype.val = v := by
      funext x
      exact zeroExtension_apply s v x
    simpa only [w, heq] using hlim
  have hl₁ : TendstoUniformlyOn (fun k => fderiv ℝ (u (φ k))) w₁ atTop (ball z r) := by
    apply TendstoUniformlyOn.mono (s := s) _ hbB
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have heq : zeroExtension s v₁ ∘ Subtype.val = v₁ := by
      funext x
      exact zeroExtension_apply s v₁ x
    simpa only [w₁, heq] using hlim₁
  have hl₂ : TendstoUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (u (φ k))))
      w₂ atTop (ball z r) := by
    apply TendstoUniformlyOn.mono (s := s) _ hbB
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have heq : zeroExtension s v₂ ∘ Subtype.val = v₂ := by
      funext x
      exact zeroExtension_apply s v₂ x
    simpa only [w₂, heq] using hlim₂
  obtain ⟨hC2, hw₁, hw₂⟩ := contDiffOn_two_of_uniform_jets isOpen_ball
    (fun k x hx => (((hu (φ k)).1 x (hsB (hbB hx))).contDiffAt
      (isOpen_ball.mem_nhds (hsB (hbB hx)))).differentiableAt (by norm_num) |>.hasFDerivAt)
    (fun k x hx => (((hureg₁ (φ k)) x (hsB (hbB hx))).contDiffAt
      (isOpen_ball.mem_nhds (hsB (hbB hx)))).differentiableAt (by norm_num) |>.hasFDerivAt)
    (fun k => (hureg₂ (φ k)).mono (ball_subset_ball hrR.le))
    (fun x hx => hl.tendsto_at hx) hl₁ hl₂
  exact ⟨w, w₁, w₂, φ, hφ, hC2, hl, hl₁, hl₂, hw₁, hw₂⟩

theorem exists_holder_solution_limit_on_inner_ball
    {n : ℕ} {α N r R : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hN : 0 ≤ N) (hrR : r < R) (z : Space n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c f : Space n → ℝ) (u : ℕ → Space n → ℝ)
    (hu : ∀ k, IsC2HolderOn α (u k) (ball z R))
    (hNorm : ∀ k, c2HolderNormOn α (u k) (ball z R) ≤ N)
    (heq : ∀ k x, x ∈ ball z R → nondivergenceOperator a b c (u k) x = f x) :
    ∃ w : Space n → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      IsC2HolderOn α w (ball z r) ∧
      (∀ x ∈ ball z r, nondivergenceOperator a b c w x = f x) ∧
      ∀ x ∈ ball z r, Tendsto (fun k => u (φ k) x) atTop (𝓝 (w x)) := by
  obtain ⟨w, w₁, w₂, φ, hφ, hC2, hlim, hlim₁, hlim₂, hw₁, hw₂⟩ :=
    exists_c2_limit_on_inner_ball hα hα1 hN hrR z u hu hNorm
  have hsub : ball z r ⊆ ball z R := ball_subset_ball hrR.le
  have hwf (x : Space n) (hx : x ∈ ball z r) : fderiv ℝ w x = w₁ x :=
    (hw₁ x hx).fderiv
  have hwff (x : Space n) (hx : x ∈ ball z r) :
      fderiv ℝ (fderiv ℝ w) x = w₂ x := by
    have hlocal : fderiv ℝ w =ᶠ[𝓝 x] w₁ :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) (fun y hy => hwf y hy)
    exact hlocal.fderiv_eq.trans (hw₂ x hx).fderiv
  have hfirst (i : Fin n) (x : Space n) (hx : x ∈ ball z r) :
      Tendsto (fun k => firstPartial (u (φ k)) i x) atTop (𝓝 (firstPartial w i x)) := by
    have h := ((ContinuousLinearMap.apply ℝ ℝ (coordinate n i)).continuous.tendsto
      (w₁ x)).comp (hlim₁.tendsto_at hx)
    change Tendsto (fun k => fderiv ℝ (u (φ k)) x (coordinate n i)) atTop
      (𝓝 (w₁ x (coordinate n i))) at h
    simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply, firstPartial, hwf x hx] using h
  have hsecond (i j : Fin n) (x : Space n) (hx : x ∈ ball z r) :
      Tendsto (fun k => secondPartial (u (φ k)) i j x) atTop
        (𝓝 (secondPartial w i j x)) := by
    have h := ((ContinuousLinearMap.apply ℝ ℝ (coordinate n j)).continuous.tendsto
      (w₂ x (coordinate n i))).comp
      (((ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) (coordinate n i)).continuous.tendsto
        (w₂ x)).comp (hlim₂.tendsto_at hx))
    have hpoint (k : ℕ) : ContDiffAt ℝ 2 (u (φ k)) x :=
      ((hu (φ k)).1 x (hsub hx)).contDiffAt (isOpen_ball.mem_nhds (hsub hx))
    have hwpoint : ContDiffAt ℝ 2 w x :=
      (hC2 x hx).contDiffAt (isOpen_ball.mem_nhds hx)
    change Tendsto (fun k => fderiv ℝ (fderiv ℝ (u (φ k))) x
      (coordinate n i) (coordinate n j)) atTop
      (𝓝 (w₂ x (coordinate n i) (coordinate n j))) at h
    simpa only [P201.Elliptic.ConstantSchauder.secondPartial_eq_bilinear
      (hpoint _), P201.Elliptic.ConstantSchauder.secondPartial_eq_bilinear hwpoint,
      hwff x hx] using h
  have hmulti₁ (i : Fin n) (x : Space n) (hx : x ∈ ball z r) :
      Tendsto (fun k => multiPartial (u (φ k)) {i} x) atTop (𝓝 (multiPartial w {i} x)) := by
    simpa only [← P201.Elliptic.ConstantSchauder.firstPartial_eq_multiPartial]
      using hfirst i x hx
  have hmulti₂ (i j : Fin n) (x : Space n) (hx : x ∈ ball z r) :
      Tendsto (fun k => multiPartial (u (φ k)) {i,j} x) atTop
        (𝓝 (multiPartial w {i,j} x)) := by
    have hpoint (k : ℕ) : ContDiffAt ℝ 2 (u (φ k)) x :=
      ((hu (φ k)).1 x (hsub hx)).contDiffAt (isOpen_ball.mem_nhds (hsub hx))
    have hwpoint : ContDiffAt ℝ 2 w x :=
      (hC2 x hx).contDiffAt (isOpen_ball.mem_nhds hx)
    simpa only [P201.Elliptic.ConstantSchauder.secondPartial_eq_multiPartial (hpoint _),
      P201.Elliptic.ConstantSchauder.secondPartial_eq_multiPartial hwpoint]
      using hsecond i j x hx
  have hb₀ (k : ℕ) (x : Space n) (hx : x ∈ ball z r) : ‖u k x‖ ≤ N :=
    (norm_le_supNormOn (hu k).2.1 (hsub hx)).trans
      ((c2HolderNormOn_components α (u k) (ball z R)).1.trans (hNorm k))
  have hb₁ (k : ℕ) (i : Fin n) (x : Space n) (hx : x ∈ ball z r) :
      ‖multiPartial (u k) {i} x‖ ≤ N :=
    (norm_le_supNormOn ((hu k).2.2.1 i) (hsub hx)).trans
      (((c2HolderNormOn_components α (u k) (ball z R)).2.1 i).trans (hNorm k))
  have hb₂ (k : ℕ) (i j : Fin n) (x : Space n) (hx : x ∈ ball z r) :
      ‖multiPartial (u k) {i,j} x‖ ≤ N :=
    ((holder_bounds_by_normOn ((hu k).2.2.2 i j)).2.1 x (hsub hx)).trans
      (((c2HolderNormOn_components α (u k) (ball z R)).2.2 i j).trans (hNorm k))
  have hh₂ (k : ℕ) (i j : Fin n) (x : Space n) (hx : x ∈ ball z r)
      (y : Space n) (hy : y ∈ ball z r) :
      ‖multiPartial (u k) {i,j} x - multiPartial (u k) {i,j} y‖ ≤ N * dist x y ^ α :=
    ((holder_bounds_by_normOn ((hu k).2.2.2 i j)).2.2 x (hsub hx) y (hsub hy)).trans
      (mul_le_mul_of_nonneg_right
        (((c2HolderNormOn_components α (u k) (ball z R)).2.2 i j).trans (hNorm k))
        (Real.rpow_nonneg dist_nonneg α))
  have hholder : IsC2HolderOn α w (ball z r) := by
    refine ⟨hC2, ⟨N, hN, ?_⟩, (fun i => ⟨N, hN, ?_⟩), ?_⟩
    · intro x hx
      exact le_of_tendsto (hlim.tendsto_at hx).norm
        (Eventually.of_forall (fun k => hb₀ (φ k) x hx))
    · intro x hx
      exact le_of_tendsto (hmulti₁ i x hx).norm
        (Eventually.of_forall (fun k => hb₁ (φ k) i x hx))
    · intro i j
      refine ⟨N, N, hN, hN, ?_, ?_⟩
      · intro x hx
        exact le_of_tendsto (hmulti₂ i j x hx).norm
          (Eventually.of_forall (fun k => hb₂ (φ k) i j x hx))
      · exact holder_bound_of_pointwise_limit
          (fun k x hx y hy => hh₂ (φ k) i j x hx y hy) (hmulti₂ i j)
  refine ⟨w, φ, hφ, hholder, ?_, fun x hx => hlim.tendsto_at hx⟩
  intro x hx
  have hL : Tendsto (fun k => nondivergenceOperator a b c (u (φ k)) x)
      atTop (𝓝 (nondivergenceOperator a b c w x)) := by
    unfold nondivergenceOperator
    exact ((tendsto_finset_sum _ (fun i _ => tendsto_finset_sum _
      (fun j _ => (hsecond i j x hx).const_mul (a x i j)))).add
      (tendsto_finset_sum _ (fun i _ => (hfirst i x hx).const_mul (b x i)))).add
      ((hlim.tendsto_at hx).const_mul (c x))
  have heq' : (fun k => nondivergenceOperator a b c (u (φ k)) x) = fun _ => f x := by
    funext k
    exact heq (φ k) x (hsub hx)
  rw [heq'] at hL
  exact tendsto_nhds_unique hL tendsto_const_nhds

end PerronCompactness

/-- Successive finite maxima, starting with the zeroth member. -/
def runningMax {X : Type*} (v : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => v 0
  | j + 1 => fun x => max (runningMax v j x) (v (j + 1) x)

theorem runningMax_monotone {X : Type*} (v : ℕ → X → ℝ) (x : X) :
    Monotone (fun j => runningMax v j x) := by
  apply monotone_nat_of_le_succ
  intro j
  exact le_max_left _ _

theorem le_runningMax {X : Type*} (v : ℕ → X → ℝ) {k j : ℕ}
    (hkj : k ≤ j) (x : X) : v k x ≤ runningMax v j x := by
  have hself : v k x ≤ runningMax v k x := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  exact hself.trans (runningMax_monotone v x hkj)

theorem isSubfunction_runningMax {n : ℕ} {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G : Space n → ℝ} {v : ℕ → Space n → ℝ}
    (hv : ∀ j, IsSubfunction Ω a b c f G (v j)) :
    ∀ j, IsSubfunction Ω a b c f G (runningMax v j) := by
  intro j
  induction j with
  | zero => exact hv 0
  | succ j ih => exact isSubfunction_max ih (hv (j + 1))

/-- The finite-maximum and ball-replacement sequence for an arbitrary list of
interior points. Its values converge to the envelope at every listed point;
density is needed only in the subsequent identification of an interior limit. -/
theorem exists_monotone_perron_ball_sequence
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G v₀ W : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space n))))
    (hv₀ : IsSubfunction Ω a b c f G v₀)
    (hupper : ∀ v : Space n → ℝ, IsSubfunction Ω a b c f G v →
      ∀ x ∈ closure (Ω : Set (Space n)), v x ≤ W x)
    {z : Space n} {r : ℝ} (hr : 0 < r) (hB : closedBall z r ⊆ (Ω : Set (Space n)))
    (d : ℕ → Space n) (hd : ∀ k, d k ∈ ball z r) :
    ∃ V : ℕ → Space n → ℝ,
      (∀ j, IsSubfunction Ω a b c f G (V j)) ∧
      (∀ j, IsC2HolderLocOn α (V j)
        (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r)) ∧
      (∀ j, ∀ x ∈ ball z r, nondivergenceOperator a b c (V j) x = f x) ∧
      (∀ x, Monotone (fun j => V j x)) ∧
      (∀ j x, v₀ x ≤ V j x) ∧
      (∀ j, ∀ x ∈ closure (Ω : Set (Space n)),
        V j x ≤ perronEnvelope Ω a b c f G x) ∧
      (∀ k, Tendsto (fun j => V j (d k)) atTop
        (𝓝 (perronEnvelope Ω a b c f G (d k)))) := by
  classical
  have happ (j k : ℕ) : ∃ v : Space n → ℝ,
      IsSubfunction Ω a b c f G v ∧
      perronEnvelope Ω a b c f G (d k) - 1 / ((j : ℝ) + 1) < v (d k) :=
    exists_subfunction_gt_perronEnvelope_sub ⟨v₀, hv₀⟩ (d k) (by positivity)
  choose v hv hvapprox using happ
  let q : ℕ → Space n → ℝ :=
    runningMax (fun j x => max (v₀ x) (runningMax (v j) j x))
  have hq : ∀ j, IsSubfunction Ω a b c f G (q j) :=
    isSubfunction_runningMax
      (fun j => isSubfunction_max hv₀ (isSubfunction_runningMax (hv j) j))
  have hqmono (x : Space n) : Monotone (fun j => q j x) :=
    runningMax_monotone _ x
  have hvq (j k : ℕ) (hkj : k ≤ j) (x : Space n) : v j k x ≤ q j x := by
    exact (le_runningMax (v j) hkj x).trans ((le_max_right _ _).trans
      (le_runningMax (fun i y => max (v₀ y) (runningMax (v i) i y))
        (k := j) (j := j) le_rfl x))
  have hv₀q (j : ℕ) (x : Space n) : v₀ x ≤ q j x :=
    (le_max_left _ _).trans
      (le_runningMax (fun i y => max (v₀ y) (runningMax (v i) i y))
        (k := j) (j := j) le_rfl x)
  have hrepl (j : ℕ) := exists_subfunction_ballReplacement hcontinuous hn hα hα1 hell
    ha hcoeff hc hf (hq j) hr hB
  choose V hVsub hVraise hVreg hVL hVout using hrepl
  have hbounded (x : Space n) (hx : x ∈ closure (Ω : Set (Space n))) :
      BddAbove {t : ℝ | ∃ v : Space n → ℝ,
        IsSubfunction Ω a b c f G v ∧ t = v x} := by
    refine ⟨W x, ?_⟩
    rintro t ⟨v, hv, rfl⟩
    exact hupper v hv x hx
  have hVU (j : ℕ) (x : Space n) (hx : x ∈ closure (Ω : Set (Space n))) :
      V j x ≤ perronEnvelope Ω a b c f G x :=
    le_perronEnvelope (hbounded x hx) (hVsub j)
  have hVmono (x : Space n) : Monotone (fun j => V j x) := by
    intro i j hij
    change V i x ≤ V j x
    by_cases hx : x ∈ ball z r
    · let B : Domain n := ⟨ball z r, isOpen_ball⟩
      have hBΩ : (B : Set (Space n)) ⊆ (Ω : Set (Space n)) :=
        ball_subset_closedBall.trans hB
      have hBcl : closure (B : Set (Space n)) = closedBall z r := closure_ball z hr.ne'
      apply comparison_on_bounded_open hn B isBounded_ball a b c (V i) (V j)
        (ellipticCoefficients_mono (ellipticCoefficients_of_holder hα hell Ω ha hcoeff) hBΩ)
        (fun y hy => hc y (subset_closure (hBΩ hy))) (hVreg i).1
        ((hVsub i).1.mono (closure_mono hBΩ)) (hVreg j).1
        ((hVsub j).1.mono (closure_mono hBΩ)) ?_ ?_ x (subset_closure hx)
      · intro y hy
        rw [hVL i y hy, hVL j y hy]
      · intro y hy
        have hys : y ∈ sphere z r := frontier_ball_subset_sphere hy
        have hynot : y ∉ ball z r :=
          fun hyball => (mem_ball.mp hyball).ne (mem_sphere.mp hys)
        rw [hVout i y hynot, hVout j y hynot]
        exact hqmono y hij
    · rw [hVout i x hx, hVout j x hx]
      exact hqmono x hij
  refine ⟨V, hVsub, hVreg, hVL, hVmono,
    fun j x => (hv₀q j x).trans (hVraise j x), hVU, ?_⟩
  intro k
  have hlower : ∀ᶠ j : ℕ in atTop,
      perronEnvelope Ω a b c f G (d k) - 1 / ((j : ℝ) + 1) ≤ V j (d k) := by
    filter_upwards [eventually_ge_atTop k] with j hkj
    exact (hvapprox j k).le.trans ((hvq j k hkj (d k)).trans (hVraise j (d k)))
  have hlim : Tendsto (fun j : ℕ =>
      perronEnvelope Ω a b c f G (d k) - 1 / ((j : ℝ) + 1)) atTop
      (𝓝 (perronEnvelope Ω a b c f G (d k))) := by
    simpa only [sub_zero] using
      tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply hlim.squeeze' tendsto_const_nhds hlower
  filter_upwards [] with j
  exact hVU j (d k) (subset_closure (hB (ball_subset_closedBall (hd k))))

/-- A lower semicontinuous envelope cannot exceed a continuous candidate
which agrees with it on a dense subset. -/
theorem eqOn_of_lowerSemicontinuousOn_of_denseRange {n : ℕ}
    {s : Set (Space n)} {U w : Space n → ℝ}
    (hU : LowerSemicontinuousOn U s) (hw : ContinuousOn w s)
    (hbelow : ∀ x ∈ s, w x ≤ U x)
    {d : ℕ → s} (hd : DenseRange d) (heq : ∀ j, U (d j) = w (d j)) :
    EqOn U w s := by
  have hlower : LowerSemicontinuous (fun x : s => U x + -w x) :=
    (lowerSemicontinuous_restrict_iff.mpr hU).add
      (continuousOn_iff_continuous_domRestrict.mp hw).neg.lowerSemicontinuous
  have hclosed : IsClosed {x : s | U x ≤ w x} := by
    simpa only [Set.preimage, Set.mem_Iic, add_neg_le_iff_le_add, zero_add] using
      hlower.isClosed_preimage 0
  have hcontains : closure (range d) ⊆ {x : s | U x ≤ w x} := by
    apply hclosed.closure_subset_iff.mpr
    rintro x ⟨j, rfl⟩
    exact (heq j).le
  intro x hx
  exact le_antisymm (hcontains (hd ⟨x, hx⟩)) (hbelow x hx)

/-- Continuity of the Perron function in the interior and its limits at
all boundary points imply continuity on the actual closed domain. -/
theorem continuousOn_closure_of_interior_of_boundary {n : ℕ} {Ω : Domain n}
    {u : Space n → ℝ} (hu : ContinuousOn u Ω)
    (hboundary : ∀ p ∈ frontier (Ω : Set (Space n)),
      ContinuousWithinAt u (closure (Ω : Set (Space n))) p) :
    ContinuousOn u (closure (Ω : Set (Space n))) := by
  intro p hp
  by_cases hpΩ : p ∈ (Ω : Set (Space n))
  · exact ((hu p hpΩ).continuousAt (Ω.isOpen.mem_nhds hpΩ)).continuousWithinAt
  · apply hboundary p
    rw [frontier, Ω.isOpen.interior_eq]
    exact ⟨hp, hpΩ⟩

/-- A pointwise subsequential limit of the Perron raising sequence equals the
finite envelope, once the sequence realizes the envelope on a dense list. -/
theorem perronEnvelope_eqOn_subsequence_limit {n : ℕ} {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G v₀ W : Space n → ℝ}
    (hv₀ : IsSubfunction Ω a b c f G v₀)
    (hupper : ∀ v : Space n → ℝ, IsSubfunction Ω a b c f G v →
      ∀ x ∈ closure (Ω : Set (Space n)), v x ≤ W x)
    {z : Space n} {r : ℝ} (hB : closedBall z r ⊆ (Ω : Set (Space n)))
    {V : ℕ → Space n → ℝ} (hV : ∀ j, IsSubfunction Ω a b c f G (V j))
    {d : ℕ → ball z r} (hd : DenseRange d)
    (happrox : ∀ k, Tendsto (fun j => V j (d k)) atTop
      (𝓝 (perronEnvelope Ω a b c f G (d k))))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {w : Space n → ℝ}
    (hw : ContinuousOn w (ball z r))
    (hlim : ∀ x ∈ ball z r, Tendsto (fun j => V (φ j) x) atTop (𝓝 (w x))) :
    EqOn (perronEnvelope Ω a b c f G) w (ball z r) := by
  have hBcl : ball z r ⊆ closure (Ω : Set (Space n)) :=
    (ball_subset_closedBall.trans hB).trans subset_closure
  have hU := (perronEnvelope_bounds_and_lowerSemicontinuous hv₀ hupper).2.mono hBcl
  have hVU (j : ℕ) (x : Space n) (hx : x ∈ ball z r) :
      V j x ≤ perronEnvelope Ω a b c f G x := by
    apply le_perronEnvelope (hv := hV j)
    refine ⟨W x, ?_⟩
    rintro t ⟨v, hv, rfl⟩
    exact hupper v hv x (hBcl hx)
  exact eqOn_of_lowerSemicontinuousOn_of_denseRange hU hw
    (fun x hx => le_of_tendsto (hlim x hx)
      (Eventually.of_forall (fun j => hVU (φ j) x hx))) hd
    (fun k => tendsto_nhds_unique ((happrox k).comp hφ.tendsto_atTop)
      (hlim (d k) (d k).property))

/-- Once compactness provides an actual locally Hölder classical ball limit,
dense-point realization identifies it with the envelope and transfers the
actual derivatives and PDE, using equality of germs on the open ball. -/
theorem perronEnvelope_ball_solution_of_subsequence_limit
    {n : ℕ} {α : ℝ} {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G v₀ W : Space n → ℝ}
    (hv₀ : IsSubfunction Ω a b c f G v₀)
    (hupper : ∀ v : Space n → ℝ, IsSubfunction Ω a b c f G v →
      ∀ x ∈ closure (Ω : Set (Space n)), v x ≤ W x)
    {z : Space n} {r : ℝ} (hB : closedBall z r ⊆ (Ω : Set (Space n)))
    {V : ℕ → Space n → ℝ} (hV : ∀ j, IsSubfunction Ω a b c f G (V j))
    {d : ℕ → ball z r} (hd : DenseRange d)
    (happrox : ∀ k, Tendsto (fun j => V j (d k)) atTop
      (𝓝 (perronEnvelope Ω a b c f G (d k))))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {w : Space n → ℝ}
    (hw : IsC2HolderLocOn α w
      (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r))
    (hLw : ∀ x ∈ ball z r, nondivergenceOperator a b c w x = f x)
    (hlim : ∀ x ∈ ball z r, Tendsto (fun j => V (φ j) x) atTop (𝓝 (w x))) :
    IsC2HolderLocOn α (perronEnvelope Ω a b c f G)
      (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r) ∧
      ∀ x ∈ ball z r,
        nondivergenceOperator a b c (perronEnvelope Ω a b c f G) x = f x := by
  have heq := perronEnvelope_eqOn_subsequence_limit hv₀ hupper hB hV hd happrox hφ
    hw.1.continuousOn hlim
  refine ⟨isC2HolderLocOn_congr hw heq, ?_⟩
  intro x hx
  exact (nondivergenceOperator_eqOn
    (Ω := P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r) a b c heq hx).trans
      (hLw x hx)

/-- Local classical Hölder ball solutions give the actual solution class on
an arbitrary open set, without any connectedness hypothesis. -/
theorem isC2HolderLocOn_of_ball_neighborhoods {n : ℕ} {α : ℝ}
    {Ω : Domain n} {u : Space n → ℝ}
    (hball : ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ (Ω : Set (Space n)) ∧
      IsC2HolderLocOn α u
        (P201Specs.Elliptic.BallSchauderSolvability.ballDomain x r)) :
    IsC2HolderLocOn α u Ω := by
  constructor
  · intro x hx
    obtain ⟨r, hr, hB, hu⟩ := hball x hx
    exact (hu.1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).contDiffWithinAt
  · intro x hx
    obtain ⟨r, hr, hB, hu⟩ := hball x hx
    obtain ⟨s, hs, hsB, hholder⟩ := hu.2 x (mem_ball_self hr)
    exact ⟨s, hs, hsB.trans hB, hholder⟩

/-- The local Perron identification on each compactly contained ball patches
into a solution on every open component at once. -/
theorem perronEnvelope_interior_solution_of_ball_solutions
    {n : ℕ} {α : ℝ} {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G : Space n → ℝ}
    (hball : ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ (Ω : Set (Space n)) ∧
      IsC2HolderLocOn α (perronEnvelope Ω a b c f G)
        (P201Specs.Elliptic.BallSchauderSolvability.ballDomain x r) ∧
      ∀ y ∈ ball x r,
        nondivergenceOperator a b c (perronEnvelope Ω a b c f G) y = f y) :
    IsC2HolderLocOn α (perronEnvelope Ω a b c f G) Ω ∧
      ∀ x ∈ Ω, nondivergenceOperator a b c (perronEnvelope Ω a b c f G) x = f x := by
  refine ⟨isC2HolderLocOn_of_ball_neighborhoods ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, hB, hu, hLu⟩ := hball x hx
    exact ⟨r, hr, hB, hu⟩
  · intro x hx
    obtain ⟨r, hr, hB, hu, hLu⟩ := hball x hx
    exact hLu x (mem_ball_self hr)

theorem exists_bounded_dense_perron_ball_sequence
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G W : Space n → ℝ} {B : ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space n))))
    (hW : ∀ x ∈ closure (Ω : Set (Space n)), 0 ≤ W x ∧ W x ≤ B)
    (hsub : IsSubfunction Ω a b c f G (fun x => -W x))
    (hupper : ∀ v : Space n → ℝ, IsSubfunction Ω a b c f G v →
      ∀ x ∈ closure (Ω : Set (Space n)), v x ≤ W x)
    {z : Space n} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hB : closedBall z R ⊆ (Ω : Set (Space n))) :
    ∃ (d : ℕ → ball z r) (V : ℕ → Space n → ℝ), DenseRange d ∧
      (∀ j, IsSubfunction Ω a b c f G (V j)) ∧
      (∀ j, IsC2HolderLocOn α (V j)
        (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z R)) ∧
      (∀ j, ∀ x ∈ ball z R, nondivergenceOperator a b c (V j) x = f x) ∧
      (∀ x, Monotone (fun j => V j x)) ∧
      (∀ j, ∀ x ∈ closure (Ω : Set (Space n)), ‖V j x‖ ≤ B) ∧
      (∀ k, Tendsto (fun j => V j (d k)) atTop
        (𝓝 (perronEnvelope Ω a b c f G (d k)))) := by
  classical
  haveI : Nonempty (ball z r) := ⟨⟨z, mem_ball_self hr⟩⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (ball z r)
  have hdR (k : ℕ) : (d k : Space n) ∈ ball z R :=
    (ball_subset_ball hrR) (d k).property
  obtain ⟨V, hVsub, hVreg, hVL, hVmono, hVlower, hVU, hVapprox⟩ :=
    exists_monotone_perron_ball_sequence hcontinuous hn hα hα1 hell ha hcoeff hc hf hsub
      hupper (hr.trans_le hrR) hB (fun k => (d k : Space n)) hdR
  refine ⟨d, V, hd, hVsub, hVreg, hVL, hVmono, ?_, hVapprox⟩
  intro j x hx
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hlower := hVlower j x
    have hWx := (hW x hx).2
    linarith
  · exact (hupper (V j) (hVsub j) x hx).trans (hW x hx).2

/-- Bounded Hölder regularity on an open set includes the shared local class. -/
theorem isC2HolderLocOn_of_isC2HolderOn {n : ℕ} {α : ℝ}
    {Ω : Domain n} {u : Space n → ℝ} (hu : IsC2HolderOn α u Ω) :
    IsC2HolderLocOn α u Ω := by
  refine ⟨hu.1, ?_⟩
  intro x hx
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  refine ⟨r, hr, hB, ?_⟩
  intro i j
  exact P201.Elliptic.PoissonSchauder.isHolderOn_mono (hu.2.2.2 i j) hB


/-- The actual conditional interior estimate gives common bounded C²,α norms
for a uniformly bounded sequence of classical solutions on a larger ball. -/
theorem perron_ball_sequence_interior_norm_bound
    (hestimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hf : IsHolderOn α f (closure (Ω : Set (Space n))))
    {z : Space n} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hB : closedBall z R ⊆ (Ω : Set (Space n)))
    {u : ℕ → Space n → ℝ}
    (hu : ∀ j, IsC2HolderLocOn α (u j)
      (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z R))
    (hLu : ∀ j, ∀ x ∈ ball z R, nondivergenceOperator a b c (u j) x = f x)
    {B : ℝ} (hBnonneg : 0 ≤ B) (hub : ∀ j, ∀ x ∈ ball z R, ‖u j x‖ ≤ B) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ j, IsC2HolderOn α (u j) (ball z r) ∧
      P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α (u j) (ball z r) ≤ N := by
  let D := P201Specs.Elliptic.BallSchauderSolvability.ballDomain z R
  let D' := P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r
  have hDcl : (D : Set (Space n)) ⊆ closure (Ω : Set (Space n)) :=
    (ball_subset_closedBall.trans hB).trans subset_closure
  have hDD : closure (D' : Set (Space n)) ⊆ (D : Set (Space n)) := by
    rw [show closure (D' : Set (Space n)) = closedBall z r from closure_ball z hr.ne']
    exact closedBall_subset_ball hrR
  have hcoeffD : CoefficientsHolderOn α a b c D :=
    ⟨fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hcoeff.1 i j) hDcl,
      fun i => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hcoeff.2.1 i) hDcl,
      P201.Elliptic.PoissonSchauder.isHolderOn_mono hcoeff.2.2 hDcl⟩
  have hcoeffLoc : CoefficientsHolderLoc α a b c D :=
    ⟨fun i j => P201.Elliptic.PoissonSchauder.isHolderLoc_of_isHolderOn (hcoeffD.1 i j),
      fun i => P201.Elliptic.PoissonSchauder.isHolderLoc_of_isHolderOn (hcoeffD.2.1 i),
      P201.Elliptic.PoissonSchauder.isHolderLoc_of_isHolderOn hcoeffD.2.2⟩
  have haD : UniformlyEllipticOn ell a D :=
    ⟨fun x hx => ha.1 x (hDcl hx), fun x hx => ha.2 x (hDcl hx)⟩
  have hfD : IsHolderOn α f D :=
    P201.Elliptic.PoissonSchauder.isHolderOn_mono hf hDcl
  let K : ℝ := max (coefficientNormOn α a b c D) 0
  obtain ⟨C, hC, hest⟩ := hestimate hn α hα hα1 D D' D isBounded_ball hDD le_rfl ell K
    hell (le_max_right _ _)
  refine ⟨max (C * (B + holderNormOn α f D)) 0, le_max_right _ _, ?_⟩
  intro j
  obtain ⟨hclass, hnorm⟩ := hest a b c haD hcoeffLoc hcoeffD (le_max_left _ _) (u j) f
    (hu j) (P201.Elliptic.PoissonSchauder.isHolderLoc_of_isHolderOn hfD) (hLu j)
    ⟨B, hBnonneg, hub j⟩ hfD
  refine ⟨hclass, hnorm.trans ?_⟩
  apply le_trans _ (le_max_left _ _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hsup : supNormOn (u j) (D : Set (Space n)) ≤ B :=
    P201.Elliptic.NewtonHessian.supNormOn_le hBnonneg (hub j)
  linarith


/-- The bounded raising sequence, the actual interior estimate, and C²
compactness identify the Perron envelope as a solution on a smaller ball. -/
theorem perronEnvelope_solution_on_inner_ball
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    (hestimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G W : Space n → ℝ} {B : ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space n))))
    (hBnonneg : 0 ≤ B)
    (hW : ∀ x ∈ closure (Ω : Set (Space n)), 0 ≤ W x ∧ W x ≤ B)
    (hsub : IsSubfunction Ω a b c f G (fun x => -W x))
    (hupper : ∀ v : Space n → ℝ, IsSubfunction Ω a b c f G v →
      ∀ x ∈ closure (Ω : Set (Space n)), v x ≤ W x)
    {z : Space n} {R : ℝ} (hR : 0 < R)
    (hB : closedBall z R ⊆ (Ω : Set (Space n))) :
    IsC2HolderLocOn α (perronEnvelope Ω a b c f G)
      (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z (R / 4)) ∧
      ∀ x ∈ ball z (R / 4),
        nondivergenceOperator a b c (perronEnvelope Ω a b c f G) x = f x := by
  have hquarter : 0 < R / 4 := by positivity
  have hhalf : 0 < R / 2 := by positivity
  have hqh : R / 4 < R / 2 := by linarith
  have hhR : R / 2 < R := by linarith
  have hqR : R / 4 ≤ R := by linarith
  obtain ⟨d, V, hd, hVsub, hVreg, hVL, hVmono, hVbound, hVapprox⟩ :=
    exists_bounded_dense_perron_ball_sequence hcontinuous hn hα hα1 hell ha hcoeff hc hf
      hW hsub hupper hquarter hqR hB
  have hVboundB (j : ℕ) (x : Space n) (hx : x ∈ ball z R) : ‖V j x‖ ≤ B :=
    hVbound j x (subset_closure (hB (ball_subset_closedBall hx)))
  obtain ⟨N, hN, hNorm⟩ := perron_ball_sequence_interior_norm_bound hestimate hn hα hα1 hell
    ha hcoeff hf hhalf hhR hB hVreg hVL hBnonneg hVboundB
  obtain ⟨w, φ, hφ, hw, hLw, hlim⟩ :=
    PerronCompactness.exists_holder_solution_limit_on_inner_ball hα hα1 hN hqh z a b c f V
      (fun j => (hNorm j).1) (fun j => (hNorm j).2)
      (fun j x hx => hVL j x (ball_subset_ball hhR.le hx))
  have hBquarter : closedBall z (R / 4) ⊆ (Ω : Set (Space n)) :=
    (closedBall_subset_closedBall hqR).trans hB
  exact perronEnvelope_ball_solution_of_subsequence_limit hsub hupper hBquarter hVsub hd
    hVapprox hφ (isC2HolderLocOn_of_isC2HolderOn hw) hLw hlim

/-- The real Perron envelope solves the equation in the interior of every
bounded open set under the original coefficient hypotheses. This conclusion
is independent of boundary charts and requires only bounded outer data. -/
theorem perronEnvelope_interior_solution
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    (hestimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell K : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hK : 0 ≤ K) {Ω : Domain n}
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f G : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hbound : coefficientNormOn α a b c (closure (Ω : Set (Space n))) ≤ K)
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space n))))
    (hG : IsBoundedOn G (frontier (Ω : Set (Space n)))) :
    IsC2HolderLocOn α (perronEnvelope Ω a b c f G) Ω ∧
      ∀ x ∈ Ω, nondivergenceOperator a b c (perronEnvelope Ω a b c f G) x = f x := by
  obtain ⟨W, B, hBnonneg, hWsmooth, hW, hsub, hupper⟩ :=
    exists_perron_barriers hcontinuous hn hα hα1 hell hK hb ha hcoeff hbound hc hf hG
  apply perronEnvelope_interior_solution_of_ball_solutions
  intro x hx
  obtain ⟨R, hR, hBR⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hx)
  obtain ⟨hu, hLu⟩ := perronEnvelope_solution_on_inner_ball hcontinuous hestimate hn hα hα1 hell
    ha hcoeff hc hf hBnonneg hW hsub hupper hR hBR
  refine ⟨R / 4, by positivity, ?_, hu, hLu⟩
  exact (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith : R / 4 ≤ R))).trans hBR

/-- A radial power written in terms of the squared distance, including
negative powers with their only pole at the specified exterior point. -/
def squaredRadialPower {n : ℕ} (y : Space n) (p : ℝ) (x : Space n) : ℝ :=
  (‖x - y‖ ^ 2) ^ p

theorem squaredRadialPower_contDiffAt {n : ℕ} (y : Space n) (p : ℝ)
    {x : Space n} (hxy : x ≠ y) : ContDiffAt ℝ ⊤ (squaredRadialPower y p) x := by
  exact ((contDiffAt_id : ContDiffAt ℝ ⊤ (fun z : Space n => z) x).sub contDiffAt_const).norm_sq ℝ |>.rpow_const_of_ne
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)))

theorem squaredRadialPower_firstPartial {n : ℕ} (y : Space n) (p : ℝ)
    {x : Space n} (hxy : x ≠ y) (i : Fin n) :
    firstPartial (squaredRadialPower y p) i x =
      2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (x i - y i) := by
  have hS := ((hasFDerivAt_id x).sub_const y).norm_sq
  have h := hS.rpow_const (p := p)
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))))
  simp only [id_eq, Pi.mul_apply, EuclideanSpace.proj, PiLp.proj_apply] at h
  have hinner : inner ℝ (x - y) (coordinate n i) = x i - y i := by
    simp [P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
  change fderiv ℝ (fun z : Space n => (‖z - y‖ ^ 2) ^ p) x (coordinate n i) = _
  rw [h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, innerSL_apply_apply, hinner]
  ring

theorem squaredRadialPower_secondPartial {n : ℕ} (y : Space n) (p : ℝ)
    {x : Space n} (hxy : x ≠ y) (i j : Fin n) :
    secondPartial (squaredRadialPower y p) i j x =
      4 * p * (p - 1) * (‖x - y‖ ^ 2) ^ (p - 2) * (x i - y i) * (x j - y j) +
      2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (if i = j then 1 else 0) := by
  classical
  have heq : firstPartial (squaredRadialPower y p) j =ᶠ[𝓝 x]
      (fun z => 2 * p * (‖z - y‖ ^ 2) ^ (p - 1) * (z j - y j)) := by
    filter_upwards [isOpen_ne.mem_nhds hxy] with z hz
    exact squaredRadialPower_firstPartial y p hz j
  have hS := ((hasFDerivAt_id x).sub_const y).norm_sq
  have hp := hS.rpow_const (p := p - 1)
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))))
  have hj := (EuclideanSpace.proj j : Space n →L[ℝ] ℝ).hasFDerivAt (x := x) |>.sub_const (y j)
  have h := (hp.const_mul (2 * p)).mul hj
  simp only [id_eq, Pi.mul_apply, EuclideanSpace.proj, PiLp.proj_apply] at h
  have hinner : inner ℝ (x - y) (coordinate n i) = x i - y i := by
    simp [P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
  have hcoord : (coordinate n i) j = if i = j then 1 else 0 := by
    simp [P201Specs.coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
  change fderiv ℝ (firstPartial (squaredRadialPower y p) j) x (coordinate n i) = _
  change HasFDerivAt (fun z : Space n => 2 * p * (‖z - y‖ ^ 2) ^ (p - 1) * (z j - y j)) _ x at h
  rw [heq.fderiv_eq, h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    innerSL_apply_apply, EuclideanSpace.proj, PiLp.proj_apply, hinner, hcoord]
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

/-- Exact radial-power operator identity, using actual coordinate derivatives. -/
theorem squaredRadialPower_operator {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) (y : Space n) (p : ℝ)
    {x : Space n} (hxy : x ≠ y) :
    nondivergenceOperator a b c (squaredRadialPower y p) x =
      4 * p * (p - 1) * (‖x - y‖ ^ 2) ^ (p - 2) *
        (∑ i : Fin n, ∑ j : Fin n, a x i j * (x i - y i) * (x j - y j)) +
      2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (∑ i : Fin n, a x i i) +
      2 * p * (‖x - y‖ ^ 2) ^ (p - 1) *
        (∑ i : Fin n, b x i * (x i - y i)) + c x * squaredRadialPower y p x := by
  classical
  unfold nondivergenceOperator
  simp_rw [squaredRadialPower_firstPartial y p hxy,
    squaredRadialPower_secondPartial y p hxy]
  have hdiag : (∑ i : Fin n, ∑ j : Fin n,
      a x i j * (2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (if i = j then 1 else 0))) =
      2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (∑ i : Fin n, a x i i) := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hprincipal : (∑ i : Fin n, ∑ j : Fin n,
      a x i j * (4 * p * (p - 1) * (‖x - y‖ ^ 2) ^ (p - 2) * (x i - y i) * (x j - y j))) =
      4 * p * (p - 1) * (‖x - y‖ ^ 2) ^ (p - 2) *
        (∑ i : Fin n, ∑ j : Fin n, a x i j * (x i - y i) * (x j - y j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdrift : (∑ i : Fin n, b x i * (2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (x i - y i))) =
      2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (∑ i : Fin n, b x i * (x i - y i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hprincipal, hdiag, hdrift]

/-- The usual exterior-sphere barrier; a negative squared-radius power
is used so the derivative formulas hold for every positive dimension. -/
def exteriorSphereBarrier {n : ℕ} (y : Space n) (R q : ℝ) (x : Space n) : ℝ :=
  (R ^ 2) ^ (-q) - squaredRadialPower y (-q) x

theorem exteriorSphereBarrier_nonneg {n : ℕ} {y x : Space n} {R q : ℝ}
    (hR : 0 < R) (hq : 0 ≤ q) (hx : R ≤ dist x y) :
    0 ≤ exteriorSphereBarrier y R q x := by
  unfold exteriorSphereBarrier squaredRadialPower
  apply sub_nonneg.mpr
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hR)
    (by rw [dist_eq_norm] at hx; nlinarith [norm_nonneg (x - y)]) (by linarith)

theorem exteriorSphereBarrier_zero {n : ℕ} {y x : Space n} {R q : ℝ}
    (hx : dist x y = R) : exteriorSphereBarrier y R q x = 0 := by
  unfold exteriorSphereBarrier squaredRadialPower
  rw [← dist_eq_norm, hx, sub_self]


/-- The radial exponent can dominate the trace and drift terms uniformly.
This estimate includes a positive strict margin and the actual zeroth order term. -/
theorem exteriorSphereBarrier_operator_le {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) {y x : Space n} {R q ell M : ℝ}
    (hR : 0 < R) (hq : 0 < q) (hell : 0 < ell)
    (hxy : R ≤ dist x y) (hM : ‖x - y‖ ^ 2 ≤ M) (hc : c x ≤ 0)
    (ha : ell * ‖x - y‖ ^ 2 ≤
      ∑ i : Fin n, ∑ j : Fin n, a x i j * (x i - y i) * (x j - y j))
    (htrace : (∑ i : Fin n, a x i i) + (∑ i : Fin n, b x i * (x i - y i)) ≤
      2 * (q + 1) * ell - 1) :
    nondivergenceOperator a b c (exteriorSphereBarrier y R q) x ≤
      -(2 * q * M ^ (-q - 1)) := by
  have hne : x ≠ y := dist_pos.mp (hR.trans_le hxy)
  let S : ℝ := ‖x - y‖ ^ 2
  let Q : ℝ := ∑ i : Fin n, ∑ j : Fin n, a x i j * (x i - y i) * (x j - y j)
  let T : ℝ := (∑ i : Fin n, a x i i) + (∑ i : Fin n, b x i * (x i - y i))
  have hS : 0 < S := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hpower : S ^ (-q - 1) = S ^ (-q - 2) * S := by
    have hh := Real.rpow_add hS (-q - 2) 1
    rw [Real.rpow_one] at hh
    convert hh using 1 <;> ring
  have heq : nondivergenceOperator a b c (exteriorSphereBarrier y R q) x =
      (2 * q * S ^ (-q - 2)) * (S * T - 2 * (q + 1) * Q) +
        c x * exteriorSphereBarrier y R q x := by
    unfold exteriorSphereBarrier
    rw [nondivergenceOperator_const_sub, squaredRadialPower_operator a b c y (-q) hne]
    change _ = (2 * q * S ^ (-q - 2)) * (S * T - 2 * (q + 1) * Q) + _
    dsimp [S, T, Q] at hpower ⊢
    rw [hpower]
    ring
  have hinner : S * T - 2 * (q + 1) * Q ≤ -S := by
    have ht := mul_le_mul_of_nonneg_left htrace hS.le
    have hqQ := mul_le_mul_of_nonneg_left ha (show 0 ≤ 2 * (q + 1) by positivity)
    change ell * S ≤ Q at ha
    change S * T ≤ _ at ht
    change 2 * (q + 1) * (ell * S) ≤ 2 * (q + 1) * Q at hqQ
    nlinarith
  have hβ := exteriorSphereBarrier_nonneg hR hq.le hxy
  have hczero := mul_nonpos_of_nonpos_of_nonneg hc hβ
  have hcoef : 0 ≤ 2 * q * S ^ (-q - 2) := by positivity
  have hp := Real.rpow_le_rpow_of_nonpos hS hM (show -q - 1 ≤ 0 by linarith)
  rw [heq]
  calc
    _ ≤ (2 * q * S ^ (-q - 2)) * (-S) := by
      have hh := mul_le_mul_of_nonneg_left hinner hcoef
      linarith
    _ = -(2 * q * S ^ (-q - 1)) := by rw [hpower]; ring
    _ ≤ -(2 * q * M ^ (-q - 1)) := by nlinarith


/-- A bounded elliptic domain lying outside a ball has a classical strict
radial barrier at every contact point. All coefficient bounds are obtained
from the original Hölder data, rather than assumed as a barrier certificate. -/
theorem exists_exteriorSphereBarrier {n : ℕ} {α ell : ℝ}
    (hα : 0 < α) (hell : 0 < ell) {Ω : Domain n}
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    {y : Space n} {R : ℝ} (hR : 0 < R)
    (hout : ∀ x ∈ closure (Ω : Set (Space n)), R ≤ dist x y) :
    ∃ (β : Space n → ℝ) (δ : ℝ), 0 < δ ∧ ContDiffOn ℝ 2 β Ω ∧
      ContinuousOn β (closure (Ω : Set (Space n))) ∧
      (∀ x ∈ closure (Ω : Set (Space n)), 0 ≤ β x) ∧
      (∀ p : Space n, dist p y = R → β p = 0) ∧
      ∀ x ∈ Ω, nondivergenceOperator a b c β x ≤ -δ := by
  let T : Space n → ℝ := fun x =>
    (∑ i : Fin n, a x i i) + ∑ i : Fin n, b x i * (x i - y i)
  have hT : ContinuousOn T (closure (Ω : Set (Space n))) := by
    apply ContinuousOn.add
    · apply continuousOn_finsetSum
      intro i _
      exact continuousOn_of_isHolderOn hα (hcoeff.1 i i)
    · apply continuousOn_finsetSum
      intro i _
      exact (continuousOn_of_isHolderOn hα (hcoeff.2.1 i)).mul
        ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).continuous.continuousOn.sub continuousOn_const)
  obtain ⟨B, hB⟩ := hb.isCompact_closure.bddAbove_image hT
  let q : ℝ := (max 0 B + 1) / ell + 1
  have hq : 0 < q := by dsimp [q]; positivity
  have hqell : (q - 1) * ell = max 0 B + 1 := by
    dsimp [q]
    field_simp
    ring
  have htrace : ∀ x ∈ closure (Ω : Set (Space n)), T x ≤ 2 * (q + 1) * ell - 1 := by
    intro x hx
    have hTx : T x ≤ B := hB (mem_image_of_mem T hx)
    have hBmax := le_max_right 0 B
    have hzero := le_max_left 0 B
    nlinarith
  obtain ⟨D, hD, hdist⟩ := hb.closure.subset_closedBall_lt 0 y
  let δ : ℝ := 2 * q * (D ^ 2) ^ (-q - 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hneq (x : Space n) (hx : x ∈ closure (Ω : Set (Space n))) : x ≠ y :=
    dist_pos.mp (hR.trans_le (hout x hx))
  have hβ : ContDiffOn ℝ 2 (exteriorSphereBarrier y R q) Ω := by
    intro x hx
    exact (contDiffAt_const.sub (squaredRadialPower_contDiffAt y (-q)
      (hneq x (subset_closure hx)))).contDiffWithinAt.of_le (by norm_num)
  have hβc : ContinuousOn (exteriorSphereBarrier y R q) (closure (Ω : Set (Space n))) := by
    intro x hx
    exact (continuousAt_const.sub (squaredRadialPower_contDiffAt y (-q)
      (hneq x hx)).continuousAt).continuousWithinAt
  refine ⟨exteriorSphereBarrier y R q, δ, hδ, hβ, hβc,
    fun x hx => exteriorSphereBarrier_nonneg hR hq.le (hout x hx),
    fun p hp => exteriorSphereBarrier_zero hp, ?_⟩
  intro x hx
  apply exteriorSphereBarrier_operator_le a b c hR hq hell (hout x (subset_closure hx))
  · have hh : dist x y ≤ D := mem_closedBall.mp (hdist (subset_closure hx))
    rw [dist_eq_norm] at hh
    nlinarith [norm_nonneg (x - y)]
  · exact hc x (subset_closure hx)
  · simpa only [WithLp.ofLp_sub, Pi.sub_apply] using ha.2 x (subset_closure hx) (x - y)
  · exact htrace x (subset_closure hx)

/-- A genuine boundary barrier bounds the zero-data Perron envelope and
proves its boundary limit. The barrier is classical only on the actual
open domain, so exterior-pole barriers are allowed. -/
theorem perronEnvelope_zero_boundary_barrier
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) {Ω : Domain n}
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c f β : Space n → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space n))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space n))))
    (hc : ∀ x ∈ closure (Ω : Set (Space n)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space n))))
    (hβ : ContDiffOn ℝ 2 β Ω)
    (hβc : ContinuousOn β (closure (Ω : Set (Space n))))
    (hβ0 : ∀ x ∈ closure (Ω : Set (Space n)), 0 ≤ β x)
    {δ : ℝ} (hδ : 0 < δ)
    (hLβ : ∀ x ∈ Ω, nondivergenceOperator a b c β x ≤ -δ) :
    ∃ t : ℝ, 0 < t ∧
      (∀ x ∈ closure (Ω : Set (Space n)),
        ‖perronEnvelope Ω a b c f (fun _ => 0) x‖ ≤ t * β x) ∧
      ∀ p ∈ closure (Ω : Set (Space n)), β p = 0 →
        perronEnvelope Ω a b c f (fun _ => 0) p = 0 ∧
        ContinuousWithinAt (perronEnvelope Ω a b c f (fun _ => 0))
          (closure (Ω : Set (Space n))) p := by
  obtain ⟨F, H, hF, hH, hfB, hfH⟩ := hf
  let t : ℝ := (F + 1) / δ
  have ht : 0 < t := div_pos (by linarith) hδ
  have htδ : t * δ = F + 1 := by dsimp [t]; field_simp
  let W : Space n → ℝ := fun x => t * β x
  have hW : ContDiffOn ℝ 2 W Ω := contDiffOn_const.mul hβ
  have hWc : ContinuousOn W (closure (Ω : Set (Space n))) :=
    continuousOn_const.mul hβc
  have hLW : ∀ x ∈ Ω, nondivergenceOperator a b c W x ≤ -(F + 1) := by
    intro x hx
    dsimp [W]
    rw [nondivergenceOperator_const_mul a b c hβ _ hx]
    have := mul_le_mul_of_nonneg_left (hLβ x hx) ht.le
    nlinarith
  have hnegative : IsSubfunction Ω a b c f (fun _ => 0) (fun x => -W x) := by
    apply isSubfunction_of_classical hn (ellipticCoefficients_of_holder hα hell Ω ha hcoeff)
      (fun x hx => hc x (subset_closure hx)) hW.neg hWc.neg
    · intro x hx
      have hneg := nondivergenceOperator_const_mul a b c hW (-1) hx
      simp only [neg_one_mul] at hneg
      rw [hneg]
      have := (abs_le.mp (hfB x (subset_closure hx))).2
      have := hLW x hx
      linarith
    · intro x hx
      exact neg_nonpos.mpr (mul_nonneg ht.le (hβ0 x (frontier_subset_closure hx)))
  have hupper : ∀ v : Space n → ℝ, IsSubfunction Ω a b c f (fun _ => 0) v →
      ∀ x ∈ closure (Ω : Set (Space n)), v x ≤ W x := by
    intro v hv
    apply subfunction_le_strict_supersolution hcontinuous hn hα hα1 hell hb ha hcoeff hc
      ⟨F, H, hF, hH, hfB, hfH⟩ hv hW hWc
    · intro x hx
      have := (abs_le.mp (hfB x (subset_closure hx))).1
      have := hLW x hx
      linarith
    · intro x hx
      exact (hv.2.1 x hx).trans (mul_nonneg ht.le (hβ0 x (frontier_subset_closure hx)))
  have hbound := (perronEnvelope_bounds_and_lowerSemicontinuous hnegative hupper).1
  have habs : ∀ x ∈ closure (Ω : Set (Space n)),
      ‖perronEnvelope Ω a b c f (fun _ => 0) x‖ ≤ t * β x := by
    intro x hx
    exact abs_le.mpr (hbound x hx)
  refine ⟨t, ht, habs, ?_⟩
  intro p hp hzero
  have hpzero : perronEnvelope Ω a b c f (fun _ => 0) p = 0 := by
    have := habs p hp
    rw [hzero, mul_zero] at this
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
  refine ⟨hpzero, ?_⟩
  change Tendsto _ (𝓝[closure (Ω : Set (Space n))] p) (𝓝 _)
  rw [hpzero]
  have hlim : Tendsto (fun x => t * β x) (𝓝[closure (Ω : Set (Space n))] p) (𝓝 0) := by
    have h := (hβc p hp).const_mul t
    change Tendsto (fun x => t * β x) (𝓝[closure (Ω : Set (Space n))] p) (𝓝 (t * β p)) at h
    simpa only [hzero, mul_zero] using h
  have hlimneg : Tendsto (fun x => -(t * β x))
      (𝓝[closure (Ω : Set (Space n))] p) (𝓝 0) := by
    simpa only [neg_zero] using hlim.neg
  exact hlimneg.squeeze' hlim
    (by filter_upwards [self_mem_nhdsWithin] with x hx; exact (hbound x hx).1)
    (by filter_upwards [self_mem_nhdsWithin] with x hx; exact (hbound x hx).2)

/-- Boundary convergence of the zero-data Perron construction follows from
the actual graph geometry and original coefficients. No regularity or
boundary values of the envelope are assumed. -/
theorem perronEnvelope_zero_boundary_values
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    {m : ℕ} {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    {Ω : Domain (m + 1)} (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasC2HolderBoundary α Ω)
    {a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {b : Space (m + 1) → Space (m + 1)} {c f : Space (m + 1) → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space (m + 1)))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space (m + 1)))))
    (hc : ∀ x ∈ closure (Ω : Set (Space (m + 1))), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space (m + 1))))) :
    ∀ p ∈ frontier (Ω : Set (Space (m + 1))),
      perronEnvelope Ω a b c f (fun _ => 0) p = 0 ∧
      ContinuousWithinAt (perronEnvelope Ω a b c f (fun _ => 0))
        (closure (Ω : Set (Space (m + 1)))) p := by
  intro p hp
  obtain ⟨y, R, hR, hpR, hout⟩ := exists_exterior_sphere_distance_bounds hboundary hp
  obtain ⟨β, δ, hδ, hβ, hβc, hβnonneg, hβzero, hLβ⟩ :=
    exists_exteriorSphereBarrier hα hell hb ha hcoeff hc hR (fun x hx => (hout x hx).1)
  obtain ⟨t, ht, hbound, hlimit⟩ := perronEnvelope_zero_boundary_barrier hcontinuous
    (by omega) hα hα1 hell hb ha hcoeff hc hf hβ hβc hβnonneg hδ hLβ
  exact hlimit p (frontier_subset_closure hp) (hβzero p hpR)

/-- Once the interior Perron limit has been identified, its zero trace and
continuity on the closure need no further analytic compactness argument. -/
theorem perronEnvelope_zero_continuousOn
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    {m : ℕ} {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    {Ω : Domain (m + 1)} (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasC2HolderBoundary α Ω)
    {a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {b : Space (m + 1) → Space (m + 1)} {c f : Space (m + 1) → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space (m + 1)))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space (m + 1)))))
    (hc : ∀ x ∈ closure (Ω : Set (Space (m + 1))), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space (m + 1)))))
    (hu : ContinuousOn (perronEnvelope Ω a b c f (fun _ => 0)) Ω) :
    ContinuousOn (perronEnvelope Ω a b c f (fun _ => 0))
      (closure (Ω : Set (Space (m + 1)))) ∧
      ∀ p ∈ frontier (Ω : Set (Space (m + 1))),
        perronEnvelope Ω a b c f (fun _ => 0) p = 0 := by
  have hvalues := perronEnvelope_zero_boundary_values hcontinuous hα hα1 hell hb
    hboundary ha hcoeff hc hf
  exact ⟨continuousOn_closure_of_interior_of_boundary hu (fun p hp => (hvalues p hp).2),
    fun p hp => (hvalues p hp).1⟩

/-- Existence and classical uniqueness for zero outer data on the original
bounded C²,α domain. Up-to-boundary derivatives are not claimed here: this
lemma isolates the completed Perron construction from that remaining step. -/
theorem zero_dirichlet_classical_solution
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    (hestimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    {m : ℕ} {α ell K : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hK : 0 ≤ K) {Ω : Domain (m + 1)}
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasC2HolderBoundary α Ω)
    {a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {b : Space (m + 1) → Space (m + 1)} {c f : Space (m + 1) → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space (m + 1)))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space (m + 1)))))
    (hbound : coefficientNormOn α a b c (closure (Ω : Set (Space (m + 1)))) ≤ K)
    (hc : ∀ x ∈ closure (Ω : Set (Space (m + 1))), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space (m + 1))))) :
    ∃ u : Space (m + 1) → ℝ,
      IsC2HolderLocOn α u Ω ∧ ContinuousOn u (closure (Ω : Set (Space (m + 1)))) ∧
      (∀ x ∈ Ω, nondivergenceOperator a b c u x = f x) ∧
      (∀ p ∈ frontier (Ω : Set (Space (m + 1))), u p = 0) ∧
      ∀ v : Space (m + 1) → ℝ, ContDiffOn ℝ 2 v Ω →
        ContinuousOn v (closure (Ω : Set (Space (m + 1)))) →
        (∀ x ∈ Ω, nondivergenceOperator a b c v x = f x) →
        (∀ p ∈ frontier (Ω : Set (Space (m + 1))), v p = 0) →
        EqOn v u (closure (Ω : Set (Space (m + 1)))) := by
  have hG : IsBoundedOn (fun _ : Space (m + 1) => (0 : ℝ))
      (frontier (Ω : Set (Space (m + 1)))) := ⟨0, le_rfl, by simp⟩
  obtain ⟨hu, hLu⟩ := perronEnvelope_interior_solution hcontinuous hestimate
    (by omega) hα hα1 hell hK hb ha hcoeff hbound hc hf hG
  obtain ⟨huc, hub⟩ := perronEnvelope_zero_continuousOn hcontinuous hα hα1 hell hb
    hboundary ha hcoeff hc hf hu.1.continuousOn
  refine ⟨perronEnvelope Ω a b c f (fun _ => 0), hu, huc, hLu, hub, ?_⟩
  intro v hv hvc hLv hvb
  exact classical_solution_unique (by omega) Ω hb a b c f (fun _ => 0) v
    (perronEnvelope Ω a b c f (fun _ => 0))
    (ellipticCoefficients_of_holder hα hell Ω ha hcoeff)
    (fun x hx => hc x (subset_closure hx)) hv hvc hu.1 huc hLv hLu hvb hub

section BoundaryRegularity

open P201Specs.Elliptic.HalfSpaceLift
open P201.Elliptic.ChartSchauder P201.Elliptic.HalfSpaceLift
open P102.Sobolev.Geometry P102.U4.GraphPieces

/-- One-sided jets on the closure of the actual C²,α open set are unique,
without any connectedness or boundedness assumption. -/
theorem uniqueDiffOn_closure_of_hasC2HolderBoundary
    {m : ℕ} {α : ℝ} {Ω : P201Specs.Domain (m + 1)}
    (hboundary : HasC2HolderBoundary α Ω) :
    UniqueDiffOn ℝ (closure (Ω : Set (P201Specs.Space (m + 1)))) := by
  intro p hp
  by_cases hpΩ : p ∈ (Ω : Set (P201Specs.Space (m + 1)))
  · exact (Ω.isOpen.uniqueDiffWithinAt hpΩ).mono subset_closure
  · have hpf : p ∈ frontier (Ω : Set (P201Specs.Space (m + 1))) := by
      rw [frontier, Ω.isOpen.interior_eq]
      exact ⟨hp, hpΩ⟩
    obtain ⟨C, hCp, hC⟩ := hboundary p hpf (mem_univ p)
    change chartPoint C = p at hCp
    apply chart_closure_uniqueDiffWithinAt C hC.1 hp
    rw [← hCp]
    exact chartPoint_mem C

/-- In dimension one the graph shear is a translation because the
horizontal space has exactly one point. -/
theorem shear_dim_zero_eq_add (γ : P201Specs.Space 0 → ℝ)
    (z : Ambient 0) :
    shear γ z = z + WithLp.toLp 2 ((0 : P201Specs.Space 0), γ 0) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · simp only [shear, WithLp.ofLp_toLp, WithLp.ofLp_add, Prod.snd_add]
    rw [show z.ofLp.1 = (0 : P201Specs.Space 0) from Subsingleton.elim _ _]
    exact add_comm _ _

/-- A one-dimensional C² graph chart is an isometry, not merely a local
nonlinear diffeomorphism. No tangent-frame assumption is used. -/
theorem chartParametrization_dim_zero_isometry
    {Ω : P201Specs.Domain 1}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame 0) Ω : Set (Ambient 0))) :
    Isometry (chartParametrization C) := by
  have hshear : Isometry (shear C.graphFunction : Ambient 0 → Ambient 0) := by
    convert isometry_add_right (WithLp.toLp 2 ((0 : P201Specs.Space 0), C.graphFunction 0)) using 1
    exact funext (shear_dim_zero_eq_add C.graphFunction)
  exact (graphFrame 0).isometry.comp (C.frame.isometry.comp
    (hshear.comp ((isometry_add_right (WithLp.toLp 2 (C.center, (0 : ℝ)))).comp
      (graphFrame 0).symm.isometry)))

/-- The Euclidean norm in the shared dimension-one coordinates. -/
theorem norm_dim_one (x : P201Specs.Space 1) : ‖x‖ = |height x| := by
  have hh : (horizontal x : P201Specs.Space 0) = 0 := Subsingleton.elim _ _
  have hs := norm_sq_horizontal_height x
  simp [hh] at hs
  nlinarith [norm_nonneg x, abs_nonneg (height x), sq_abs (height x)]

theorem dist_dim_one (x y : P201Specs.Space 1) : dist x y = |height x - height y| := by
  rw [dist_eq_norm, norm_dim_one]
  rfl

theorem mem_ball_center_dim_one {r : ℝ} {x : P201Specs.Space 1} :
    x ∈ ball (point (0 : P201Specs.Space 0) r) r ↔
      0 < height x ∧ height x < 2 * r := by
  rw [mem_ball, dist_dim_one, height_point, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem mem_closedBall_center_dim_one {r : ℝ} {x : P201Specs.Space 1} :
    x ∈ closedBall (point (0 : P201Specs.Space 0) r) r ↔
      0 ≤ height x ∧ height x ≤ 2 * r := by
  rw [mem_closedBall, dist_dim_one, height_point, abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- A one-dimensional chart contains an actual ball sharing the endpoint,
and agrees with that ball on a full neighborhood of the endpoint. -/
theorem exists_interior_ball_sharing_endpoint
    {Ω : P201Specs.Domain 1}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame 0) Ω : Set (Ambient 0)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius)) :
    ∃ (z : P201Specs.Space 1) (r : ℝ), 0 < r ∧
      ball z r ⊆ (Ω : Set (P201Specs.Space 1)) ∧
      closedBall z r ⊆ closure (Ω : Set (P201Specs.Space 1)) ∧
      chartPoint C ∈ sphere z r ∧
      closedBall z r ∩ ball (chartPoint C) r =
        closure (Ω : Set (P201Specs.Space 1)) ∩ ball (chartPoint C) r ∧
      sphere z r ∩ ball (chartPoint C) r ⊆ {chartPoint C} := by
  obtain ⟨a, ha, _, hflat, hmap⟩ := exists_flat_half_ball C hγ zero_lt_one
  let e := chartParametrization C
  have hi : Isometry e := chartParametrization_dim_zero_isometry C
  let r : ℝ := a / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let q : P201Specs.Space 1 := point (0 : P201Specs.Space 0) r
  let z : P201Specs.Space 1 := e q
  have he0 : e (0 : P201Specs.Space 1) = chartPoint C := chartParametrization_zero C
  have hmem (y : P201Specs.Space 1) :
      y ∈ closedBall z r ↔ e.symm y ∈ closedBall q r := by
    change dist y (e q) ≤ r ↔ dist (e.symm y) q ≤ r
    rw [← hi.dist_eq (e.symm y) q, Equiv.apply_symm_apply]
  have hmemopen (y : P201Specs.Space 1) :
      y ∈ ball z r ↔ e.symm y ∈ ball q r := by
    change dist y (e q) < r ↔ dist (e.symm y) q < r
    rw [← hi.dist_eq (e.symm y) q, Equiv.apply_symm_apply]
  have hnear (y : P201Specs.Space 1) (hy : y ∈ ball (chartPoint C) r) :
      e.symm y ∈ ball (0 : P201Specs.Space 1) r := by
    change dist (e.symm y) 0 < r
    rw [← hi.dist_eq (e.symm y) 0, Equiv.apply_symm_apply, he0]
    exact hy
  have hhalf (x : P201Specs.Space 1) (hx : x ∈ closedBall q r) :
      x ∈ halfBallWithFace 0 (2 * a) := by
    have hh := mem_closedBall_center_dim_one.mp hx
    refine ⟨?_, hh.1⟩
    rw [mem_ball, dist_zero_right, norm_dim_one, abs_of_nonneg hh.1]
    dsimp [r] at hh
    linarith [hh.2]
  have hclosed : closedBall z r ⊆ closure (Ω : Set (P201Specs.Space 1)) := by
    intro y hy
    have hm := (hmap (hhalf (e.symm y) ((hmem y).mp hy))).1
    change e (e.symm y) ∈ _ at hm
    simpa only [Equiv.apply_symm_apply] using hm
  have hopen : ball z r ⊆ (Ω : Set (P201Specs.Space 1)) := by
    intro y hy
    have hx := (hmemopen y).mp hy
    have hhe := hhalf (e.symm y) (ball_subset_closedBall hx)
    have hm := (chartParametrization_mem_domain_iff C (hflat hhe.1)).mpr
      (mem_ball_center_dim_one.mp hx).1
    change e (e.symm y) ∈ (Ω : Set (P201Specs.Space 1)) at hm
    simpa only [Equiv.apply_symm_apply] using hm
  have hpball : chartPoint C ∈ sphere z r := by
    change dist (chartPoint C) (e q) = r
    rw [← he0, hi.dist_eq, dist_dim_one]
    change |0 - r| = r
    rw [zero_sub, abs_neg, abs_of_pos hr]
  refine ⟨z, r, hr, hopen, hclosed, hpball, ?_, ?_⟩
  · ext y
    constructor
    · exact fun hy => ⟨hclosed hy.1, hy.2⟩
    · intro hy
      have hxy := hnear y hy.2
      have hbig : e.symm y ∈ ball (0 : P201Specs.Space 1) (2 * a) :=
        ball_subset_ball (by dsimp [r]; linarith) hxy
      have hheight : 0 ≤ height (e.symm y) := by
        apply (chartParametrization_mem_closure_iff C (hflat hbig)).mp
        change e (e.symm y) ∈ _
        simpa only [Equiv.apply_symm_apply] using hy.1
      have habs : |height (e.symm y)| < r := by
        rw [mem_ball, dist_zero_right, norm_dim_one] at hxy
        exact hxy
      have hxB : e.symm y ∈ closedBall q r := by
        apply mem_closedBall_center_dim_one.mpr
        exact ⟨hheight, le_trans ((le_abs_self _).trans habs.le) (by linarith)⟩
      exact ⟨(hmem y).mpr hxB, hy.2⟩
  · intro y hy
    have hxy := hnear y hy.2
    have habs : |height (e.symm y)| < r := by
      rw [mem_ball, dist_zero_right, norm_dim_one] at hxy
      exact hxy
    have hys : dist (e.symm y) q = r := by
      rw [← hi.dist_eq, Equiv.apply_symm_apply]
      exact hy.1
    rw [dist_dim_one, show height q = r from height_point _ _] at hys
    have hlt : height (e.symm y) - r ≤ 0 := by linarith [le_abs_self (height (e.symm y))]
    rw [abs_of_nonpos hlt] at hys
    have hzero : height (e.symm y) = 0 := by linarith
    have hxzero : e.symm y = 0 := by
      apply norm_eq_zero.mp
      rw [norm_dim_one, hzero, abs_zero]
    have hyzero := congrArg e hxzero
    rw [Equiv.apply_symm_apply, he0] at hyzero
    exact hyzero

/-- Interior C²,α regularity restricts to any smaller open domain. -/
theorem isC2HolderLocOn_restrict {n : ℕ} {α : ℝ} {u : P201Specs.Space n → ℝ}
    {D Ω : P201Specs.Domain n} (hDΩ : (D : Set (P201Specs.Space n)) ⊆ Ω)
    (hu : IsC2HolderLocOn α u Ω) : IsC2HolderLocOn α u D := by
  refine ⟨hu.1.mono hDΩ, ?_⟩
  intro x hx
  obtain ⟨r, hr, _, hH⟩ := hu.2 x (hDΩ hx)
  obtain ⟨s, hs, hB⟩ := Metric.isOpen_iff.mp D.isOpen x hx
  refine ⟨min r s, lt_min hr hs, (ball_subset_ball (min_le_right r s)).trans hB, ?_⟩
  intro i j
  exact P201.Elliptic.PoissonSchauder.isHolderOn_mono (hH i j)
    (ball_subset_ball (min_le_left r s))

/-- The positive closed ball has unique one-sided derivatives. -/
theorem uniqueDiffOn_closedBall_pos {n : ℕ} (z : P201Specs.Space n) {r : ℝ}
    (hr : 0 < r) : UniqueDiffOn ℝ (closedBall z r) := by
  apply uniqueDiffOn_convex (convex_closedBall z r)
  refine ⟨z, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (ball_mem_nhds z hr) ball_subset_closedBall

/-- Global ball regularity provides the exact locally lifted boundary class
used by the frozen continuous-data boundary premise. -/
theorem local_upToOn_ball_of_global {n : ℕ} {α : ℝ} {G : P201Specs.Space n → ℝ}
    {z : P201Specs.Space n} {r : ℝ} (hr : 0 < r)
    (hG : IsC2HolderUpToOn α G (closedBall z r)) (U : P201Specs.Domain n) :
    IsC2HolderLocUpToOn α G
      (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r) U := by
  have hcl : closure (ball z r) = closedBall z r := closure_ball z hr.ne'
  change ContDiffOn ℝ 2 G (closure (ball z r) ∩ (U : Set (P201Specs.Space n))) ∧ _
  simp only [hcl]
  refine ⟨hG.1.mono inter_subset_left, ?_⟩
  intro x hx
  obtain ⟨ρ, hρ, hBU⟩ := Metric.isOpen_iff.mp U.isOpen x hx.2
  refine ⟨ρ, hρ, hBU, ?_⟩
  change IsC2HolderUpToOn α G (closure (ball z r) ∩ ball x ρ)
  rw [hcl]
  exact c2HolderUpToOn_mono inter_subset_left
    ((uniqueDiffOn_closedBall_pos z hr).inter isOpen_ball)
    (uniqueDiffOn_closedBall_pos z hr) hG

/-- Complete one-dimensional boundary upgrade: an initially interior C²,α
solution continuous on the closure becomes C²,α near every endpoint, using
exactly the supplied continuous-ball local boundary theorem. -/
theorem local_boundary_regularity_dim_one
    (hballBoundary : P201Specs.Elliptic.BallSchauderSolvability.LocalBoundaryRegularityStatement)
    {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    {Ω : P201Specs.Domain 1}
    (hboundary : HasC2HolderBoundary α Ω)
    {a : P201Specs.Space 1 → Matrix (Fin 1) (Fin 1) ℝ}
    {b : P201Specs.Space 1 → P201Specs.Space 1} {c f G u : P201Specs.Space 1 → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (P201Specs.Space 1))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (P201Specs.Space 1))))
    (hc : ∀ x ∈ closure (Ω : Set (P201Specs.Space 1)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (P201Specs.Space 1))))
    (hG : IsC2HolderUpToOn α G (closure (Ω : Set (P201Specs.Space 1))))
    (hu : IsC2HolderLocOn α u Ω)
    (huc : ContinuousOn u (closure (Ω : Set (P201Specs.Space 1))))
    (hLu : ∀ x ∈ Ω, nondivergenceOperator a b c u x = f x)
    (hub : ∀ x ∈ frontier (Ω : Set (P201Specs.Space 1)), u x = G x)
    {p : P201Specs.Space 1} (hp : p ∈ frontier (Ω : Set (P201Specs.Space 1))) :
    ∃ ρ : ℝ, 0 < ρ ∧ IsC2HolderUpToOn α u
      (closure (Ω : Set (P201Specs.Space 1)) ∩ ball p ρ) := by
  obtain ⟨C, hCp, hC⟩ := hboundary p hp (mem_univ p)
  change chartPoint C = p at hCp
  obtain ⟨z, r, hr, hopen, hclosed, hps, heq, hsp⟩ :=
    exists_interior_ball_sharing_endpoint C hC.1
  rw [hCp] at hps heq hsp
  have hmono {v : P201Specs.Space 1 → ℝ}
      (hv : IsHolderOn α v (closure (Ω : Set (P201Specs.Space 1)))) :
      IsHolderOn α v (closedBall z r) :=
    P201.Elliptic.PoissonSchauder.isHolderOn_mono hv hclosed
  have haB : UniformlyEllipticOn ell a (closedBall z r) :=
    ⟨fun x hx => ha.1 x (hclosed hx), fun x hx => ha.2 x (hclosed hx)⟩
  have hcoeffB : CoefficientsHolderOn α a b c (closedBall z r) :=
    ⟨fun i j => hmono (hcoeff.1 i j), fun i => hmono (hcoeff.2.1 i), hmono hcoeff.2.2⟩
  have hGreg : IsC2HolderUpToOn α G (closedBall z r) :=
    c2HolderUpToOn_mono hclosed (uniqueDiffOn_closedBall_pos z hr)
      (uniqueDiffOn_closure_of_hasC2HolderBoundary hboundary) hG
  have huSphere : ContinuousOn u (sphere z r) :=
    huc.mono (sphere_subset_closedBall.trans hclosed)
  let g : C(sphere z r, ℝ) := ⟨fun x => u x, huSphere.domRestrict⟩
  have huB : P201Specs.Elliptic.BallSchauderSolvability.IsBallSolution
      a b c f z r g u :=
    ⟨hu.1.mono hopen, huc.mono hclosed, fun x hx => hLu x (hopen hx), fun _ => rfl⟩
  have hureg : IsC2HolderLocOn α u
      (P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r) :=
    isC2HolderLocOn_restrict hopen hu
  let U : P201Specs.Domain 1 := ⟨ball p r, isOpen_ball⟩
  let V : P201Specs.Domain 1 := ⟨ball p (r / 2), isOpen_ball⟩
  have hVcl : closure (V : Set (P201Specs.Space 1)) ⊆ (U : Set (P201Specs.Space 1)) :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  have htrace : ∀ ζ : sphere z r, (ζ : P201Specs.Space 1) ∈ (U : Set (P201Specs.Space 1)) →
      g ζ = G ζ := by
    intro ζ hζ
    have hζp : (ζ : P201Specs.Space 1) = p := by simpa using hsp ⟨ζ.property, hζ⟩
    change u ζ = G ζ
    rw [hζp]
    exact hub p hp
  have hreg := hballBoundary (by omega : 1 ≤ 1) α hα hα1 z r hr a b c
    ⟨ell, hell, haB⟩ hcoeffB (fun x hx => hc x (hclosed hx)) f (hmono hf)
    g u huB hureg U G (local_upToOn_ball_of_global hr hGreg U) htrace
    V isBounded_ball hVcl
  have heqsmall : closedBall z r ∩ (V : Set (P201Specs.Space 1)) =
      closure (Ω : Set (P201Specs.Space 1)) ∩ ball p (r / 2) := by
    ext x
    have hVU : (V : Set (P201Specs.Space 1)) ⊆ (U : Set (P201Specs.Space 1)) :=
      ball_subset_ball (by linarith)
    constructor
    · exact fun hx => ⟨hclosed hx.1, hx.2⟩
    · intro hx
      have hlarge : x ∈ closedBall z r ∩ ball p r := by
        rw [heq]
        exact ⟨hx.1, hVU hx.2⟩
      exact ⟨hlarge.1, hx.2⟩
  refine ⟨r / 2, by positivity, ?_⟩
  rwa [heqsmall] at hreg

/-- Local one-sided C²,α classes patch to the full class on a compact set.
The actual within jets agree on relatively open patches by locality. -/
theorem c2HolderUpToOn_of_local_on_compact
    {n : ℕ} {α : ℝ} (hα : 0 ≤ α) {u : P201Specs.Space n → ℝ}
    {s : Set (P201Specs.Space n)} (hcompact : IsCompact s)
    (hlocal : ∀ x ∈ s, ∃ r : ℝ, 0 < r ∧
      IsC2HolderUpToOn α u (s ∩ ball x r)) :
    IsC2HolderUpToOn α u s := by
  have hC : ContDiffOn ℝ 2 u s := by
    intro x hx
    obtain ⟨r, hr, hreg⟩ := hlocal x hx
    exact (contDiffWithinAt_inter (ball_mem_nhds x hr)).mp
      (hreg.1 x ⟨hx, mem_ball_self hr⟩)
  have hLoc : P201Specs.Elliptic.WeightedInterpolation.IsLocC2HolderWithinOn α u s :=
    ⟨hC, hlocal⟩
  obtain ⟨hzero, hfirst, hsecond⟩ :=
    P201.Elliptic.WeightedInterpolation.local_within_jet_bounds_on_compact
      hα hcompact (Subset.refl s) hLoc
  exact ⟨hC, hzero, hfirst, hsecond⟩

/-- Interior local C²,α regularity yields the closed-domain within class on
a small physical neighborhood of every interior point. -/
theorem local_upToOn_at_interior
    {n : ℕ} {α : ℝ} (hα : 0 ≤ α) {u : P201Specs.Space n → ℝ}
    {Ω : P201Specs.Domain n} (hu : IsC2HolderLocOn α u Ω)
    {p : P201Specs.Space n} (hp : p ∈ (Ω : Set (P201Specs.Space n))) :
    ∃ r : ℝ, 0 < r ∧ IsC2HolderUpToOn α u
      (closure (Ω : Set (P201Specs.Space n)) ∩ ball p r) := by
  obtain ⟨R, hR, hB⟩ := Metric.isOpen_iff.mp Ω.isOpen p hp
  let B : P201Specs.Domain n := ⟨ball p R, isOpen_ball⟩
  have huB : IsC2HolderLocOn α u B := isC2HolderLocOn_restrict hB hu
  have hreg : IsC2HolderUpToOn α u (ball p (R / 2)) :=
    P201.Elliptic.WeightedInterpolation.ball_regular_restriction hα huB (by linarith)
  have heq : closure (Ω : Set (P201Specs.Space n)) ∩ ball p (R / 2) = ball p (R / 2) := by
    apply inter_eq_right.mpr
    exact ((ball_subset_ball (by linarith : R / 2 ≤ R)).trans hB).trans subset_closure
  refine ⟨R / 2, by positivity, ?_⟩
  rw [heq]
  exact hreg

/-- Complete global dimension-one up-to-boundary regularity from the frozen
ball boundary premise, with the original data and boundary regularity. -/
theorem global_boundary_regularity_dim_one
    (hballBoundary : P201Specs.Elliptic.BallSchauderSolvability.LocalBoundaryRegularityStatement)
    {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    {Ω : P201Specs.Domain 1} (hb : Bornology.IsBounded (Ω : Set (P201Specs.Space 1)))
    (hboundary : HasC2HolderBoundary α Ω)
    {a : P201Specs.Space 1 → Matrix (Fin 1) (Fin 1) ℝ}
    {b : P201Specs.Space 1 → P201Specs.Space 1} {c f G u : P201Specs.Space 1 → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (P201Specs.Space 1))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (P201Specs.Space 1))))
    (hc : ∀ x ∈ closure (Ω : Set (P201Specs.Space 1)), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (P201Specs.Space 1))))
    (hG : IsC2HolderUpToOn α G (closure (Ω : Set (P201Specs.Space 1))))
    (hu : IsC2HolderLocOn α u Ω)
    (huc : ContinuousOn u (closure (Ω : Set (P201Specs.Space 1))))
    (hLu : ∀ x ∈ Ω, nondivergenceOperator a b c u x = f x)
    (hub : ∀ x ∈ frontier (Ω : Set (P201Specs.Space 1)), u x = G x) :
    IsC2HolderUpToOn α u (closure (Ω : Set (P201Specs.Space 1))) := by
  apply c2HolderUpToOn_of_local_on_compact hα.le hb.isCompact_closure
  intro p hp
  by_cases hpΩ : p ∈ (Ω : Set (P201Specs.Space 1))
  · exact local_upToOn_at_interior hα.le hu hpΩ
  · have hpf : p ∈ frontier (Ω : Set (P201Specs.Space 1)) := by
      rw [frontier, Ω.isOpen.interior_eq]
      exact ⟨hp, hpΩ⟩
    exact local_boundary_regularity_dim_one hballBoundary hα hα1 hell hboundary
      ha hcoeff hc hf hG hu huc hLu hub hpf

end BoundaryRegularity

namespace LiftBridge
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201Specs.Elliptic.SchauderDirichlet
open P201.Elliptic.ConstantSchauder P201.Elliptic.ChartSchauder
open P201.Elliptic.HalfSpaceLift
open P201.Elliptic.PoissonSchauder P201.Elliptic.WeightedInterpolation
open P102.Sobolev.Geometry P102.U4.GraphPieces

theorem closure_uniqueDiffOn_of_boundary {m : ℕ} {α : ℝ}
    {Ω : Domain (m + 1)} (hΩ : HasC2HolderBoundary α Ω) :
    UniqueDiffOn ℝ (closure (Ω : Set (Space (m + 1)))) := by
  intro x hx
  by_cases hxΩ : x ∈ (Ω : Set (Space (m + 1)))
  · exact (Ω.isOpen.uniqueDiffOn x hxΩ).mono subset_closure
  · have hxfront : x ∈ frontier (Ω : Set (Space (m + 1))) := by
      simpa only [frontier, Ω.isOpen.interior_eq, mem_diff] using And.intro hx hxΩ
    obtain ⟨C, hCx, hC⟩ := hΩ x hxfront (mem_univ x)
    have hpoint : chartPoint C = x := hCx
    exact chart_closure_uniqueDiffWithinAt C hC.1 hx
      (by rw [← hpoint]; exact chartPoint_mem C)

theorem lower_within_jets_holder_locally {m : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {Ω : Domain (m + 1)}
    (hΩ : HasC2HolderBoundary α Ω) {G : Space (m + 1) → ℝ}
    (hG : IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1))))) :
    ∀ x ∈ closure (Ω : Set (Space (m + 1))), ∃ ρ : ℝ, 0 < ρ ∧
      IsHolderOn α G (closure (Ω : Set (Space (m + 1))) ∩ ball x ρ) ∧
      ∀ i, IsHolderOn α (firstPartialWithin G (closure (Ω : Set (Space (m + 1)))) i)
        (closure (Ω : Set (Space (m + 1))) ∩ ball x ρ) := by
  let t := closure (Ω : Set (Space (m + 1)))
  have ht : UniqueDiffOn ℝ t := closure_uniqueDiffOn_of_boundary hΩ
  intro x hx
  by_cases hxΩ : x ∈ (Ω : Set (Space (m + 1)))
  · obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen x hxΩ
    let s := ball x ρ
    have hs : UniqueDiffOn ℝ s := isOpen_ball.uniqueDiffOn
    have hsT : MapsTo (id : Space (m + 1) → Space (m + 1)) s t :=
      fun y hy => subset_closure (hball hy)
    have hidL : ∀ y ∈ s, ‖fderivWithin ℝ (id : Space (m + 1) → Space (m + 1)) s y‖ ≤ (1 : ℝ) := by
      intro y hy
      rw [fderivWithin_id (hs y hy)]
      exact ContinuousLinearMap.norm_id_le
    obtain ⟨hzero, hone⟩ := lower_within_jets_pullback_holder hα hα1 (convex_ball x ρ)
      hs ht differentiableOn_id hsT (by norm_num : (0 : ℝ) ≤ 1) hidL hG
    refine ⟨ρ, hρ, ?_, ?_⟩
    · simpa only [Function.comp_id] using isHolderOn_mono hzero.1
        (inter_subset_right : t ∩ ball x ρ ⊆ s)
    · intro i
      simpa only [Function.comp_id] using isHolderOn_mono (hone i).1
        (inter_subset_right : t ∩ ball x ρ ⊆ s)
  · have hxfront : x ∈ frontier (Ω : Set (Space (m + 1))) := by
      simpa only [frontier, Ω.isOpen.interior_eq, mem_diff] using And.intro hx hxΩ
    obtain ⟨C, hCx, hC⟩ := hΩ x hxfront (mem_univ x)
    have hpoint : chartPoint C = x := hCx
    obtain ⟨ρ, R, r, hρ, hρR, _, _, hRC, hr, _, hrregion, hmap, hinv⟩ :=
      exists_chart_scales C hC.1 isOpen_univ (mem_univ (chartPoint C))
    let s := halfBallWithFace m (2 * r)
    let q := t ∩ ball (chartPoint C) ρ
    have hs : UniqueDiffOn ℝ s := uniqueDiffOn_halfBallWithFace m (2*r)
    have hsregion : s ⊆ flatChartRegion C := fun y hy => hrregion hy.1
    obtain ⟨_, hΦ, _, hΦL⟩ := chartParametrization_within_data C hC.1 hs hsregion
    have hmapT : MapsTo (chartParametrization C) s t := fun y hy => (hmap hy).1
    obtain ⟨hzero, hone⟩ := lower_within_jets_pullback_holder hα hα1
      ((convex_ball _ _).inter (convex_closedHalfSpace m)) hs ht
      (hΦ.differentiableOn (by norm_num)) hmapT (shearConstant C.constant).coe_nonneg hΦL hG
    have hqchart : q ⊆ physicalChart C := by
      intro y hy
      exact hRC ((ball_subset_ball (by linarith : ρ ≤ R)) hy.2)
    have hiLip := (chartParametrization_symm_lipschitzOn C).mono
      (fun y hy => physicalChart_inverse_base C (hqchart hy))
    have hiMap : MapsTo (chartParametrization C).symm q s := by
      intro y hy
      have h := hinv hy
      exact ⟨(ball_subset_ball (by linarith : r ≤ 2*r)) h.1, h.2⟩
    refine ⟨ρ, hρ, ?_, ?_⟩
    · have h := (holder_pullback_lipschitz hα hzero.1 hiLip hiMap).1
      have heq : EqOn G ((G ∘ chartParametrization C) ∘ (chartParametrization C).symm) q := by
        intro y hy
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
      have h' := isHolderOn_congr h heq
      simpa only [← hpoint, t, q] using h'
    · intro i
      have h := (holder_pullback_lipschitz hα (hone i).1 hiLip hiMap).1
      have heq : EqOn (firstPartialWithin G t i)
          (((firstPartialWithin G t i) ∘ chartParametrization C) ∘
            (chartParametrization C).symm) q := by
        intro y hy
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
      have h' := isHolderOn_congr h heq
      simpa only [← hpoint, t, q] using h'

theorem lower_within_jets_holder {m : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {Ω : Domain (m + 1)}
    (hbounded : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hΩ : HasC2HolderBoundary α Ω) {G : Space (m + 1) → ℝ}
    (hG : IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1))))) :
    IsHolderOn α G (closure (Ω : Set (Space (m + 1)))) ∧
      ∀ i, IsHolderOn α (firstPartialWithin G (closure (Ω : Set (Space (m + 1)))) i)
        (closure (Ω : Set (Space (m + 1)))) := by
  have hc : IsCompact (closure (Ω : Set (Space (m + 1)))) :=
    isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure
  have hl := lower_within_jets_holder_locally hα hα1 hΩ hG
  refine ⟨isHolderOn_of_local_on_compact hα hc ?_, ?_⟩
  · intro x hx
    obtain ⟨ρ, hρ, hzero, _⟩ := hl x hx
    exact ⟨ρ, hρ, hzero⟩
  · intro i
    apply isHolderOn_of_local_on_compact hα hc
    intro x hx
    obtain ⟨ρ, hρ, _, hone⟩ := hl x hx
    exact ⟨ρ, hρ, hone i⟩

/-- The subtraction source is genuinely Hölder on the full closure, using
the actual within derivatives of the original one-sided boundary lift. -/
theorem liftedWithinSource_holder_on_closure {m : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {Ω : Domain (m + 1)}
    (hbounded : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hΩ : HasC2HolderBoundary α Ω)
    {a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {b : Space (m + 1) → Space (m + 1)} {c f G : Space (m + 1) → ℝ}
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space (m + 1)))))
    (hf : IsHolderOn α f (closure (Ω : Set (Space (m + 1)))))
    (hG : IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1))))) :
    IsHolderOn α (liftedWithinSource a b c G f (closure (Ω : Set (Space (m + 1)))))
      (closure (Ω : Set (Space (m + 1)))) := by
  obtain ⟨hG₀, hG₁⟩ := lower_within_jets_holder hα hα1 hbounded hΩ hG
  obtain ⟨hF, _⟩ := liftedWithinSource_holder_bound
    (K := coefficientNormOn α a b c (closure (Ω : Set (Space (m + 1)))))
    hcoeff.1 hcoeff.2.1 hcoeff.2.2 le_rfl hf hG₀ hG₁ hG.2.2.2
  exact hF

/-- Adding back a genuine one-sided lift reverses the source subtraction
on the interior, where the within and ordinary derivatives agree. -/
theorem equation_add_lift {n : ℕ} {Ω : Domain n}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ)
    {w G f : Space n → ℝ} {s : Set (Space n)}
    (hw : ContDiffOn ℝ 2 w Ω) (hG : ContDiffOn ℝ 2 G s)
    (hΩs : (Ω : Set (Space n)) ⊆ s)
    (heq : ∀ x ∈ Ω, nondivergenceOperator a b c w x = liftedWithinSource a b c G f s x) :
    ∀ x ∈ Ω, nondivergenceOperator a b c (w + G) x = f x := by
  intro x hx
  have hlin := P201.Elliptic.nondivergenceOperator_mul_sub a b c
    (hw.add (hG.mono hΩs)) (hG.mono hΩs) 1 hx
  simp only [one_mul, Pi.add_apply, add_sub_cancel_right] at hlin
  change nondivergenceOperator a b c w x =
    nondivergenceOperator a b c (w + G) x - nondivergenceOperator a b c G x at hlin
  have hs : s ∈ 𝓝 x := Filter.mem_of_superset (Ω.isOpen.mem_nhds hx) hΩs
  have heq' := heq x hx
  rw [liftedWithinSource,
    nondivergenceWithinOperator_eq_nondivergenceOperator a b c G hs] at heq'
  linarith

/-- This is only a change of data for an already constructed zero-trace
solution. Existence is supplied separately by the Perron construction. -/
theorem add_lift_isDirichletSolution {m : ℕ} {α : ℝ} {Ω : Domain (m + 1)}
    (hΩ : HasC2HolderBoundary α Ω)
    {a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {b : Space (m + 1) → Space (m + 1)} {c f G w : Space (m + 1) → ℝ}
    (hG : IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1)))))
    (hw : IsDirichletSolution α Ω a b c
      (liftedWithinSource a b c G f (closure (Ω : Set (Space (m + 1)))))
      (fun _ => 0) w) :
    IsDirichletSolution α Ω a b c f G (w + G) := by
  refine ⟨c2HolderUpToOn_add (closure_uniqueDiffOn_of_boundary hΩ) hw.1 hG,
    equation_add_lift a b c (hw.1.1.mono subset_closure) hG.1 subset_closure hw.2.1, ?_⟩
  intro x hx
  simp only [Pi.add_apply, hw.2.2 x hx, zero_add]

/-- Conversely, subtracting the lift preserves the full one-sided class
and gives exactly zero boundary data for the genuine lifted source. -/
theorem sub_lift_isDirichletSolution {m : ℕ} {α : ℝ} {Ω : Domain (m + 1)}
    (hΩ : HasC2HolderBoundary α Ω)
    {a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {b : Space (m + 1) → Space (m + 1)} {c f G u : Space (m + 1) → ℝ}
    (hG : IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1)))))
    (hu : IsDirichletSolution α Ω a b c f G u) :
    IsDirichletSolution α Ω a b c
      (liftedWithinSource a b c G f (closure (Ω : Set (Space (m + 1)))))
      (fun _ => 0) (u - G) := by
  have hs := closure_uniqueDiffOn_of_boundary hΩ
  refine ⟨?_, equation_sub_lift a b c hu.1.1 hG.1 subset_closure hu.2.1, ?_⟩
  · simpa only [sub_eq_add_neg] using
      c2HolderUpToOn_add hs hu.1 (c2HolderUpToOn_neg hs hG)
  · intro x hx
    simp only [Pi.sub_apply, hu.2.2 x hx, sub_self]

theorem upToOn_isC2HolderLocOn {n : ℕ} {α : ℝ} {Ω : Domain n}
    {G : Space n → ℝ}
    (hG : IsC2HolderUpToOn α G (closure (Ω : Set (Space n)))) :
    IsC2HolderLocOn α G Ω := by
  refine ⟨hG.1.mono subset_closure, ?_⟩
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  refine ⟨r, hr, hball, ?_⟩
  intro i j
  apply isHolderOn_congr (isHolderOn_mono (hG.2.2.2 i j)
    (hball.trans subset_closure))
  intro y hy
  have hnhds : closure (Ω : Set (Space n)) ∈ 𝓝 y :=
    Filter.mem_of_superset (Ω.isOpen.mem_nhds (hball hy)) subset_closure
  have hpoint : ContDiffAt ℝ 2 G y :=
    (hG.1 y (subset_closure (hball hy))).contDiffAt hnhds
  exact (P201.Elliptic.ConstantSchauder.secondPartial_eq_multiPartial hpoint i j).symm.trans
    (secondPartialWithin_eq_secondPartial G hnhds i j).symm

theorem isC2HolderLocOn_add {n : ℕ} {α : ℝ} {Ω : Domain n}
    {u v : Space n → ℝ} (hu : IsC2HolderLocOn α u Ω) (hv : IsC2HolderLocOn α v Ω) :
    IsC2HolderLocOn α (u + v) Ω := by
  refine ⟨hu.1.add hv.1, ?_⟩
  intro x hx
  obtain ⟨r, hr, hrΩ, hhr⟩ := hu.2 x hx
  obtain ⟨s, hs, hsΩ, hhs⟩ := hv.2 x hx
  let t := min r s
  have ht : 0 < t := lt_min hr hs
  have htr : ball x t ⊆ ball x r := ball_subset_ball (min_le_left r s)
  have hts : ball x t ⊆ ball x s := ball_subset_ball (min_le_right r s)
  refine ⟨t, ht, htr.trans hrΩ, ?_⟩
  intro i j
  apply isHolderOn_congr (isHolderOn_add (isHolderOn_mono (hhr i j) htr)
    (isHolderOn_mono (hhs i j) hts))
  intro y hy
  exact P201.Elliptic.PoissonSchauder.partialWord_add_on Ω hu.1 hv.1
    (({i,j} : MultiIndex n).sort (· ≤ ·)) (by simp) (htr.trans hrΩ hy)

end LiftBridge

namespace LiftBridge
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201.Elliptic.ChartSchauder P201.Elliptic.SchauderDirichlet

/-- The completed zero-data Perron theorem and the genuine one-sided lift
give arbitrary original lifted boundary data in the classical solution class.
The full up-to-boundary derivative assertion is a separate later step. -/
theorem lifted_classical_dirichlet_solution
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    (hestimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    {m : ℕ} {α ell K : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hK : 0 ≤ K) {Ω : Domain (m + 1)}
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasC2HolderBoundary α Ω)
    {a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {b : Space (m + 1) → Space (m + 1)} {c f G : Space (m + 1) → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space (m + 1)))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space (m + 1)))))
    (hbound : coefficientNormOn α a b c (closure (Ω : Set (Space (m + 1)))) ≤ K)
    (hc : ∀ x ∈ closure (Ω : Set (Space (m + 1))), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space (m + 1)))))
    (hG : IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1))))) :
    ∃ u : Space (m + 1) → ℝ,
      IsC2HolderLocOn α u Ω ∧ ContinuousOn u (closure (Ω : Set (Space (m + 1)))) ∧
      (∀ x ∈ Ω, nondivergenceOperator a b c u x = f x) ∧
      (∀ p ∈ frontier (Ω : Set (Space (m + 1))), u p = G p) ∧
      ∀ v : Space (m + 1) → ℝ, ContDiffOn ℝ 2 v Ω →
        ContinuousOn v (closure (Ω : Set (Space (m + 1)))) →
        (∀ x ∈ Ω, nondivergenceOperator a b c v x = f x) →
        (∀ p ∈ frontier (Ω : Set (Space (m + 1))), v p = G p) →
        EqOn v u (closure (Ω : Set (Space (m + 1)))) := by
  let F := liftedWithinSource a b c G f (closure (Ω : Set (Space (m + 1))))
  have hF : IsHolderOn α F (closure (Ω : Set (Space (m + 1)))) :=
    liftedWithinSource_holder_on_closure hα.le hα1.le hb hboundary hcoeff hf hG
  obtain ⟨w, hw, hwc, hLw, hwb, _⟩ := zero_dirichlet_classical_solution
    hcontinuous hestimate hα hα1 hell hK hb hboundary ha hcoeff hbound hc hF
  have hureg : IsC2HolderLocOn α (w + G) Ω :=
    isC2HolderLocOn_add hw (upToOn_isC2HolderLocOn hG)
  have huc : ContinuousOn (w + G) (closure (Ω : Set (Space (m + 1)))) :=
    hwc.add hG.1.continuousOn
  have hLu : ∀ x ∈ Ω, nondivergenceOperator a b c (w + G) x = f x :=
    equation_add_lift a b c hw.1 hG.1 subset_closure hLw
  have hub : ∀ p ∈ frontier (Ω : Set (Space (m + 1))), (w + G) p = G p := by
    intro p hp
    simp only [Pi.add_apply, hwb p hp, zero_add]
  refine ⟨w + G, hureg, huc, hLu, hub, ?_⟩
  intro v hv hvc hLv hvb
  exact classical_solution_unique (by omega) Ω hb a b c f G v (w + G)
    (ellipticCoefficients_of_holder hα hell Ω ha hcoeff)
    (fun x hx => hc x (subset_closure hx)) hv hvc hureg.1 huc hLv hLu hvb hub

end LiftBridge

/-- The complete Dirichlet solvability conclusion in dimension one, including
the uniform estimate and uniqueness on the closure of a disconnected open set. -/
theorem solvability_dim_one
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    (hballBoundary : P201Specs.Elliptic.BallSchauderSolvability.LocalBoundaryRegularityStatement)
    (hestimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    (hglobal : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement) :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ Ω : Domain 1,
      Bornology.IsBounded (Ω : Set (Space 1)) → HasC2HolderBoundary α Ω →
      ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : Space 1 → Matrix (Fin 1) (Fin 1) ℝ)
            (b : Space 1 → Space 1) (c : Space 1 → ℝ),
            UniformlyEllipticOn ell a (closure (Ω : Set (Space 1))) →
            CoefficientsHolderOn α a b c (closure (Ω : Set (Space 1))) →
            coefficientNormOn α a b c (closure (Ω : Set (Space 1))) ≤ K →
            (∀ x ∈ closure (Ω : Set (Space 1)), c x ≤ 0) →
            ∀ f G : Space 1 → ℝ,
              IsHolderOn α f (closure (Ω : Set (Space 1))) →
              IsC2HolderUpToOn α G (closure (Ω : Set (Space 1))) →
              ∃ u : Space 1 → ℝ,
                IsDirichletSolution α Ω a b c f G u ∧
                c2HolderUpToNormOn α u (closure (Ω : Set (Space 1))) ≤
                  C * (holderNormOn α f (closure (Ω : Set (Space 1))) +
                    c2HolderUpToNormOn α G (closure (Ω : Set (Space 1)))) ∧
                ∀ v : Space 1 → ℝ, IsDirichletSolution α Ω a b c f G v →
                  EqOn v u (closure (Ω : Set (Space 1))) := by
  intro α hα hα1 Ω hb hboundary ell K hell hK
  obtain ⟨C, hC, hest⟩ := global_estimate_without_c0 hglobal 0 α hα hα1 Ω hb
    hboundary ell K hell hK
  refine ⟨C, hC, ?_⟩
  intro a b c ha hcoeff hbound hc f G hf hG
  obtain ⟨u, hu, huc, hLu, hub, hunique⟩ := LiftBridge.lifted_classical_dirichlet_solution
    hcontinuous hestimate hα hα1 hell hK hb hboundary ha hcoeff hbound hc hf hG
  have hreg := global_boundary_regularity_dim_one hballBoundary hα hα1 hell hb hboundary
    ha hcoeff hc hf hG hu huc hLu hub
  have hsol : IsDirichletSolution α Ω a b c f G u := ⟨hreg, hLu, hub⟩
  refine ⟨u, hsol, hest a b c f G u ha hcoeff hbound hc hf hG hsol, ?_⟩
  intro v hv
  exact hunique v (hv.1.1.mono subset_closure) hv.1.1.continuousOn hv.2.1 hv.2.2

section SphericalCoordinates

open P201.Elliptic.ChartSchauder P201.Elliptic.PoissonSchauder

open P201Specs.Elliptic.HalfSpaceLift
open P201.Elliptic.HalfSpaceLift

/-- Lower graph of the radius-R sphere centered at height R. The totalized
square root only matters outside its intended horizontal disk. -/
def lowerSphereGraph {E : Type*} [NormedAddCommGroup E] (R : ℝ) (x : E) : ℝ :=
  R - Real.sqrt (R ^ 2 - ‖x‖ ^ 2)

/-- The lower sphere graph is nonnegative everywhere for R>0. -/
theorem lowerSphereGraph_nonneg {E : Type*} [NormedAddCommGroup E]
    {R : ℝ} (hR : 0 < R) (x : E) : 0 ≤ lowerSphereGraph R x := by
  have hs : Real.sqrt (R ^ 2 - ‖x‖ ^ 2) ≤ R := by
    calc
      Real.sqrt (R ^ 2 - ‖x‖ ^ 2) ≤ Real.sqrt (R ^ 2) :=
        Real.sqrt_le_sqrt (sub_le_self _ (sq_nonneg _))
      _ = R := (Real.sqrt_sq_eq_abs R).trans (abs_of_pos hR)
  exact sub_nonneg.mpr hs

theorem lowerSphereGraph_le_radius {E : Type*} [NormedAddCommGroup E]
    (R : ℝ) (x : E) : lowerSphereGraph R x ≤ R :=
  sub_le_self _ (Real.sqrt_nonneg _)

/-- Smoothness of the sphere graph holds on its actual horizontal disk. -/
theorem lowerSphereGraph_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ < R) :
    ContDiffAt ℝ ∞ (lowerSphereGraph R : E → ℝ) x := by
  have hrad : 0 < R ^ 2 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  exact contDiffAt_const.sub
    ((contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt hrad.ne')

/-- This identity locates the graph on the true sphere. -/
theorem lowerSphereGraph_sphere_identity
    {E : Type*} [NormedAddCommGroup E]
    {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    ‖x‖ ^ 2 + (R - lowerSphereGraph R x) ^ 2 = R ^ 2 := by
  have hrad : 0 ≤ R ^ 2 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  dsimp [lowerSphereGraph]
  rw [sub_sub_cancel, Real.sq_sqrt hrad]
  ring

/-- The bump is one on the quarter-radius disk and supported in the
half-radius disk. -/
def lowerSphereBump {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : E) :=
  ⟨R / 4, R / 2, by positivity, by linarith⟩

/-- A global smooth shear profile coinciding with the sphere near its pole. -/
def lowerSphereCutoff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (hR : 0 < R) (x : E) : ℝ :=
  lowerSphereBump (E := E) R hR x * lowerSphereGraph R x

/-- The cutoff is C∞ globally, including the singular equator of the
uncut square-root expression: it vanishes on a neighborhood there. -/
theorem lowerSphereCutoff_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) : ContDiff ℝ ∞ (lowerSphereCutoff R hR : E → ℝ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : ‖x‖ < R
  · exact (lowerSphereBump (E := E) R hR).contDiffAt.mul (lowerSphereGraph_contDiffAt hR hx)
  · have hfar : R / 2 < ‖x‖ := by linarith [not_lt.mp hx]
    have hnbd : {y : E | R / 2 < ‖y‖} ∈ 𝓝 x :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hfar
    have heq : (lowerSphereCutoff R hR : E → ℝ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hnbd] with y hy
      dsimp [lowerSphereCutoff]
      rw [(lowerSphereBump (E := E) R hR).zero_of_le_dist (by
        change R / 2 ≤ dist y 0
        simpa only [dist_zero_right] using hy.le), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem lowerSphereCutoff_eq_graph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R / 4) :
    lowerSphereCutoff R hR x = lowerSphereGraph R x := by
  dsimp [lowerSphereCutoff]
  rw [(lowerSphereBump (E := E) R hR).one_of_mem_closedBall (by
    change dist x 0 ≤ R / 4
    simpa only [dist_zero_right] using hx), one_mul]

theorem lowerSphereCutoff_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {x : E} (hx : R / 2 ≤ ‖x‖) :
    lowerSphereCutoff R hR x = 0 := by
  dsimp [lowerSphereCutoff]
  rw [(lowerSphereBump (E := E) R hR).zero_of_le_dist (by
    change R / 2 ≤ dist x 0
    simpa only [dist_zero_right] using hx), zero_mul]

theorem lowerSphereCutoff_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (x : E) :
    0 ≤ lowerSphereCutoff R hR x ∧ lowerSphereCutoff R hR x ≤ lowerSphereGraph R x := by
  refine ⟨mul_nonneg (lowerSphereBump (E := E) R hR).nonneg (lowerSphereGraph_nonneg hR x), ?_⟩
  exact mul_le_of_le_one_left (lowerSphereGraph_nonneg hR x) (lowerSphereBump (E := E) R hR).le_one

/-- Complete smooth sphere-cutoff profile with exactly the requested radii.
The bounds hold globally, hence on the original sphere graph disk. -/
theorem exists_smooth_lower_sphere_cutoff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (hR : 0 < R) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧
      (∀ x, ‖x‖ ≤ R / 4 → β x = lowerSphereGraph R x) ∧
      (∀ x, R / 2 ≤ ‖x‖ → β x = 0) ∧
      ∀ x, 0 ≤ β x ∧ β x ≤ lowerSphereGraph R x := by
  exact ⟨lowerSphereCutoff R hR, lowerSphereCutoff_contDiff hR,
    fun _ hx => lowerSphereCutoff_eq_graph hR hx,
    fun _ hx => lowerSphereCutoff_eq_zero hR hx, lowerSphereCutoff_bounds hR⟩


/-- The smooth map from spherical coordinates back to flat coordinates. -/
def sphereFlattening {m : ℕ} (h : P201Specs.Space m → ℝ)
    (x : P201Specs.Space (m + 1)) : P201Specs.Space (m + 1) :=
  point (horizontal x) (height x - h (horizontal x))

/-- Its inverse moves the flat boundary to the cutoff sphere graph. -/
def sphereUnflattening {m : ℕ} (h : P201Specs.Space m → ℝ)
    (x : P201Specs.Space (m + 1)) : P201Specs.Space (m + 1) :=
  point (horizontal x) (height x + h (horizontal x))

@[simp] theorem horizontal_sphereFlattening {m : ℕ} (h : P201Specs.Space m → ℝ)
    (x : P201Specs.Space (m + 1)) : horizontal (sphereFlattening h x) = horizontal x :=
  horizontal_point _ _

@[simp] theorem height_sphereFlattening {m : ℕ} (h : P201Specs.Space m → ℝ)
    (x : P201Specs.Space (m + 1)) : height (sphereFlattening h x) = height x - h (horizontal x) :=
  height_point _ _

@[simp] theorem horizontal_sphereUnflattening {m : ℕ} (h : P201Specs.Space m → ℝ)
    (x : P201Specs.Space (m + 1)) : horizontal (sphereUnflattening h x) = horizontal x :=
  horizontal_point _ _

@[simp] theorem height_sphereUnflattening {m : ℕ} (h : P201Specs.Space m → ℝ)
    (x : P201Specs.Space (m + 1)) : height (sphereUnflattening h x) = height x + h (horizontal x) :=
  height_point _ _

@[simp] theorem sphereFlattening_sphereUnflattening {m : ℕ} (h : P201Specs.Space m → ℝ)
    (x : P201Specs.Space (m + 1)) : sphereFlattening h (sphereUnflattening h x) = x := by
  simp only [sphereFlattening, horizontal_sphereUnflattening, height_sphereUnflattening,
    add_sub_cancel_right, point_horizontal_height]

@[simp] theorem sphereUnflattening_sphereFlattening {m : ℕ} (h : P201Specs.Space m → ℝ)
    (x : P201Specs.Space (m + 1)) : sphereUnflattening h (sphereFlattening h x) = x := by
  simp only [sphereUnflattening, horizontal_sphereFlattening, height_sphereFlattening,
    sub_add_cancel, point_horizontal_height]

def sphereFlatteningEquiv {m : ℕ} (h : P201Specs.Space m → ℝ) :
    P201Specs.Space (m + 1) ≃ P201Specs.Space (m + 1) where
  toFun := sphereFlattening h
  invFun := sphereUnflattening h
  left_inv := sphereUnflattening_sphereFlattening h
  right_inv := sphereFlattening_sphereUnflattening h

/-- The sphere shear and its inverse are globally C∞ for an actual smooth
cutoff profile. -/
theorem sphereFlattening_contDiff {m : ℕ} {h : P201Specs.Space m → ℝ}
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (sphereFlattening h) := by
  exact ((point_contDiff m).of_le le_top).comp
    (((horizontal_contDiff m).of_le le_top).prodMk
      (((height_contDiff m).of_le le_top).sub
        (hh.comp ((horizontal_contDiff m).of_le le_top))))

theorem sphereUnflattening_contDiff {m : ℕ} {h : P201Specs.Space m → ℝ}
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (sphereUnflattening h) := by
  exact ((point_contDiff m).of_le le_top).comp
    (((horizontal_contDiff m).of_le le_top).prodMk
      (((height_contDiff m).of_le le_top).add
        (hh.comp ((horizontal_contDiff m).of_le le_top))))

/-- The cutoff sphere shear changes the Euclidean norm by at most R. -/
theorem sphereFlattening_norm_le {m : ℕ} {h : P201Specs.Space m → ℝ} {R : ℝ}
    (hbound : ∀ y, 0 ≤ h y ∧ h y ≤ R) (x : P201Specs.Space (m + 1)) :
    ‖sphereFlattening h x‖ ≤ ‖x‖ + R := by
  let ν := coordinate (m + 1) (Fin.last m)
  have hν : ‖ν‖ = 1 := by
    have hs := norm_sq_horizontal_height ν
    simp only [ν, height_coordinate_last, horizontal_coordinate_last, norm_zero] at hs
    nlinarith [norm_nonneg ν]
  have heq : sphereFlattening h x = x + (-h (horizontal x)) • ν := by
    simpa only [sphereFlattening, sub_eq_add_neg, point_horizontal_height, ν] using
      point_add_normal (horizontal x) (height x) (-h (horizontal x))
  rw [heq]
  calc
    ‖x + (-h (horizontal x)) • ν‖ ≤ ‖x‖ + ‖(-h (horizontal x)) • ν‖ := norm_add_le _ _
    _ = ‖x‖ + h (horizontal x) := by
      rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hbound _).1]
    _ ≤ ‖x‖ + R := add_le_add_right (hbound _).2 _

theorem sphereUnflattening_norm_le {m : ℕ} {h : P201Specs.Space m → ℝ} {R : ℝ}
    (hbound : ∀ y, 0 ≤ h y ∧ h y ≤ R) (x : P201Specs.Space (m + 1)) :
    ‖sphereUnflattening h x‖ ≤ ‖x‖ + R := by
  let ν := coordinate (m + 1) (Fin.last m)
  have hν : ‖ν‖ = 1 := by
    have hs := norm_sq_horizontal_height ν
    simp only [ν, height_coordinate_last, horizontal_coordinate_last, norm_zero] at hs
    nlinarith [norm_nonneg ν]
  have heq : sphereUnflattening h x = x + h (horizontal x) • ν := by
    simpa only [sphereUnflattening, point_horizontal_height, ν] using
      point_add_normal (horizontal x) (height x) (h (horizontal x))
  rw [heq]
  calc
    ‖x + h (horizontal x) • ν‖ ≤ ‖x‖ + ‖h (horizontal x) • ν‖ := norm_add_le _ _
    _ = ‖x‖ + h (horizontal x) := by
      rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_nonneg (hbound _).1]
    _ ≤ ‖x‖ + R := add_le_add_right (hbound _).2 _



open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.HalfSpaceLift
open P201.Elliptic.HalfSpaceLift

/-- The actual Euclidean distance in horizontal/height coordinates. -/
theorem dist_sq_point_zero_height {m : ℕ} (x : Space (m + 1)) (R : ℝ) :
    dist x (point (0 : Space m) R) ^ 2 =
      (height x - R) ^ 2 + ‖horizontal x‖ ^ 2 := by
  have hhor : horizontal (x - point (0 : Space m) R) = horizontal x := by
    change horizontalCLM m (x - point (0 : Space m) R) = horizontal x
    rw [map_sub]
    simp
  have hheight : height (x - point (0 : Space m) R) = height x - R := by
    simp [height, point]
  rw [dist_eq_norm, norm_sq_horizontal_height, hhor, hheight]

/-- Every interior point of the tangent ball lies above its lower graph. -/
theorem ball_spherical_lower_graph {m : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Space (m + 1)} (hx : x ∈ ball (point (0 : Space m) R) R) :
    ‖horizontal x‖ < R ∧ R - Real.sqrt (R ^ 2 - ‖horizontal x‖ ^ 2) < height x := by
  have hd : dist x (point (0 : Space m) R) ^ 2 < R ^ 2 :=
    (sq_lt_sq₀ dist_nonneg hR.le).mpr (mem_ball.mp hx)
  rw [dist_sq_point_zero_height] at hd
  have hrad : (height x - R) ^ 2 < R ^ 2 - ‖horizontal x‖ ^ 2 := by linarith
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg (height x - R), norm_nonneg (horizontal x)]
  · have h := Real.neg_sqrt_lt_of_sq_lt hrad
    linarith

/-- The analogous non-strict inequalities hold on the closed tangent ball. -/
theorem closedBall_spherical_lower_graph {m : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Space (m + 1)} (hx : x ∈ closedBall (point (0 : Space m) R) R) :
    ‖horizontal x‖ ≤ R ∧ R - Real.sqrt (R ^ 2 - ‖horizontal x‖ ^ 2) ≤ height x := by
  have hd : dist x (point (0 : Space m) R) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ dist_nonneg hR.le).mpr (mem_closedBall.mp hx)
  rw [dist_sq_point_zero_height] at hd
  have hrad : (height x - R) ^ 2 ≤ R ^ 2 - ‖horizontal x‖ ^ 2 := by linarith
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg (height x - R), norm_nonneg (horizontal x)]
  · have h := Real.neg_sqrt_le_of_sq_le hrad
    linarith

/-- A graph below the lower spherical cap contains the whole tangent ball. -/
theorem ball_subset_spherical_graph_domain {m : ℕ} {R : ℝ} (hR : 0 < R)
    {h : Space m → ℝ}
    (hbelow : ∀ u, ‖u‖ < R → h u ≤ R - Real.sqrt (R ^ 2 - ‖u‖ ^ 2)) :
    ball (point (0 : Space m) R) R ⊆ {x | h (horizontal x) < height x} := by
  intro x hx
  obtain ⟨hhor, hheight⟩ := ball_spherical_lower_graph hR hx
  exact (hbelow _ hhor).trans_lt hheight

/-- Non-strict containment for closed graph domains. -/
theorem closedBall_subset_spherical_closed_graph_domain {m : ℕ} {R : ℝ} (hR : 0 < R)
    {h : Space m → ℝ}
    (hbelow : ∀ u, ‖u‖ ≤ R → h u ≤ R - Real.sqrt (R ^ 2 - ‖u‖ ^ 2)) :
    closedBall (point (0 : Space m) R) R ⊆ {x | h (horizontal x) ≤ height x} := by
  intro x hx
  obtain ⟨hhor, hheight⟩ := closedBall_spherical_lower_graph hR hx
  exact (hbelow _ hhor).trans hheight

/-- Near the tangent point only the lower spherical cap is encountered. -/
theorem spherical_graph_domain_eq_ball_near_zero {m : ℕ} {R : ℝ} (hR : 0 < R)
    {h : Space m → ℝ}
    (hgraph : ∀ u, ‖u‖ ≤ R / 4 → h u = R - Real.sqrt (R ^ 2 - ‖u‖ ^ 2)) :
    {x | h (horizontal x) < height x} ∩ ball 0 (R / 8) =
      ball (point (0 : Space m) R) R ∩ ball 0 (R / 8) := by
  ext x
  constructor
  · rintro ⟨hxgraph, hxnear⟩
    refine ⟨?_, hxnear⟩
    have hxnorm : ‖x‖ < R / 8 := by simpa using mem_ball.mp hxnear
    have hhor : ‖horizontal x‖ ≤ R / 4 := by
      have := horizontal_norm_le x
      linarith
    have hheight : height x < R := by
      have ht := height_dist_le x 0
      simp [height, dist_zero_right] at ht
      change |height x| ≤ ‖x‖ at ht
      have := le_abs_self (height x)
      linarith
    rw [mem_ofPred_eq, hgraph _ hhor] at hxgraph
    have hsq : (height x - R) ^ 2 < R ^ 2 - ‖horizontal x‖ ^ 2 := by
      apply Real.sq_lt.mpr
      exact ⟨by linarith, (by linarith [Real.sqrt_nonneg (R ^ 2 - ‖horizontal x‖ ^ 2)])⟩
    apply mem_ball.mpr
    apply (sq_lt_sq₀ dist_nonneg hR.le).mp
    rw [dist_sq_point_zero_height]
    linarith
  · rintro ⟨hxball, hxnear⟩
    refine ⟨?_, hxnear⟩
    have hxnorm : ‖x‖ < R / 8 := by simpa using mem_ball.mp hxnear
    have hhor : ‖horizontal x‖ ≤ R / 4 := by
      have := horizontal_norm_le x
      linarith
    rw [mem_ofPred_eq, hgraph _ hhor]
    exact (ball_spherical_lower_graph hR hxball).2

/-- The local equality also holds for the closed graph and closed ball. -/
theorem spherical_closed_graph_domain_eq_closedBall_near_zero
    {m : ℕ} {R : ℝ} (hR : 0 < R) {h : Space m → ℝ}
    (hgraph : ∀ u, ‖u‖ ≤ R / 4 → h u = R - Real.sqrt (R ^ 2 - ‖u‖ ^ 2)) :
    {x | h (horizontal x) ≤ height x} ∩ ball 0 (R / 8) =
      closedBall (point (0 : Space m) R) R ∩ ball 0 (R / 8) := by
  ext x
  constructor
  · rintro ⟨hxgraph, hxnear⟩
    refine ⟨?_, hxnear⟩
    have hxnorm : ‖x‖ < R / 8 := by simpa using mem_ball.mp hxnear
    have hhor : ‖horizontal x‖ ≤ R / 4 := by
      have := horizontal_norm_le x
      linarith
    have hheight : height x < R := by
      have ht := height_dist_le x 0
      simp [height, dist_zero_right] at ht
      change |height x| ≤ ‖x‖ at ht
      have := le_abs_self (height x)
      linarith
    have hrad : 0 ≤ R ^ 2 - ‖horizontal x‖ ^ 2 := by
      have := norm_nonneg (horizontal x)
      nlinarith
    rw [mem_ofPred_eq, hgraph _ hhor] at hxgraph
    have hsq : (height x - R) ^ 2 ≤ R ^ 2 - ‖horizontal x‖ ^ 2 := by
      apply (Real.sq_le hrad).mpr
      exact ⟨by linarith, (by linarith [Real.sqrt_nonneg (R ^ 2 - ‖horizontal x‖ ^ 2)])⟩
    apply mem_closedBall.mpr
    apply (sq_le_sq₀ dist_nonneg hR.le).mp
    rw [dist_sq_point_zero_height]
    linarith
  · rintro ⟨hxball, hxnear⟩
    refine ⟨?_, hxnear⟩
    have hxnorm : ‖x‖ < R / 8 := by simpa using mem_ball.mp hxnear
    have hhor : ‖horizontal x‖ ≤ R / 4 := by
      have := horizontal_norm_le x
      linarith
    rw [mem_ofPred_eq, hgraph _ hhor]
    exact (closedBall_spherical_lower_graph hR hxball).2



/-- Any globally C¹ scalar function is Hölder on an arbitrary bounded
observation set for each exponent between zero and one. -/
theorem isHolderOn_of_contDiff_one_on_bounded
    {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {g : P201Specs.Space n → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set (P201Specs.Space n)} (hs : Bornology.IsBounded s) :
    IsHolderOn α g s := by
  obtain ⟨R, _, hsub⟩ := hs.subset_closedBall_lt 0 (0 : P201Specs.Space n)
  have hgB : ContDiffOn ℝ 1 g (closedBall (0 : P201Specs.Space n) R) := hg.contDiffOn
  obtain ⟨L, hL⟩ := hgB.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hb : P201Specs.Elliptic.PoissonSchauder.IsBoundedOn g
      (closedBall (0 : P201Specs.Space n) R) :=
    boundedOn_of_continuousOn_compact (isCompact_closedBall _ _) hgB.continuousOn
  exact isHolderOn_mono (isHolderOn_of_bounded_lipschitz hα hα1 hb hL) hsub

/-- The actual Jacobian and Hessian entries of a globally smooth map have
finite Hölder norms on every bounded set. -/
theorem smooth_map_holder_derivatives_on_bounded
    {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {Φ : P201Specs.Space n → P201Specs.Space n} (hΦ : ContDiff ℝ ∞ Φ)
    {s : Set (P201Specs.Space n)} (hs : Bornology.IsBounded s) :
    (∀ i k : Fin n, IsHolderOn α
      (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s) ∧
    ∀ i j k : Fin n, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
  have hdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ Φ)) := hd.fderiv_right (by simp)
  constructor
  · intro i k
    apply isHolderOn_of_contDiff_one_on_bounded hα hα1 _ hs
    have hi := hd.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : P201Specs.Space n => coordinate n i))
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k).contDiff.comp hi).of_le (by simp)
  · intro i j k
    apply isHolderOn_of_contDiff_one_on_bounded hα hα1 _ hs
    have hi := hdd.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : P201Specs.Space n => coordinate n i))
    have hij := hi.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : P201Specs.Space n => coordinate n j))
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k).contDiff.comp hij).of_le (by simp)

/-- A single positive bound controls every actual first/second scalar
coordinate derivative of a globally smooth map on a bounded set. -/
theorem smooth_map_holder_derivative_bounds_on_bounded
    {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {Φ : P201Specs.Space n → P201Specs.Space n} (hΦ : ContDiff ℝ ∞ Φ)
    {s : Set (P201Specs.Space n)} (hs : Bornology.IsBounded s) :
    ∃ D : ℝ, 0 < D ∧
      (∀ i k : Fin n, IsHolderOn α
        (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s ∧
        holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s ≤ D) ∧
      (∀ i j k : Fin n, IsHolderOn α
        (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s ∧
        holderNormOn α
          (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s ≤ D) := by
  obtain ⟨hJac, hHess⟩ := smooth_map_holder_derivatives_on_bounded hα hα1 hΦ hs
  obtain ⟨D, hD, hJN, hHN⟩ := exists_positive_holder_derivative_bound hJac hHess
  exact ⟨D, hD, fun i k => ⟨hJac i k, hJN i k⟩,
    fun i j k => ⟨hHess i j k, hHN i j k⟩⟩

/-- Smooth sphere shears have a finite Lipschitz constant on each closed
ball, chosen independently of the equation's coefficients or solution. -/
theorem smooth_map_lipschitz_on_closedBall
    {n : ℕ} {Φ : P201Specs.Space n → P201Specs.Space n}
    (hΦ : ContDiff ℝ ∞ Φ) (z : P201Specs.Space n) (r : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L Φ (closedBall z r) :=
  hΦ.contDiffOn.exists_lipschitzOnWith (by simp) (convex_closedBall z r)
    (isCompact_closedBall z r)

/-- Changing only the height changes Euclidean distance by that scalar amount. -/
theorem dist_point_same_horizontal_height {m : ℕ} (x : Space (m + 1)) (t : ℝ) :
    dist x (point (horizontal x) t) = |height x - t| := by
  have hhor : horizontal (x - point (horizontal x) t) = 0 := by
    change horizontalCLM m (x - point (horizontal x) t) = 0
    rw [map_sub]
    simp
  have hheight : height (x - point (horizontal x) t) = height x - t := by
    simp [height, point]
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
  rw [dist_eq_norm, norm_sq_horizontal_height, hhor, norm_zero, zero_pow (by norm_num),
    add_zero, hheight, sq_abs]

/-- The closed graph is the actual topological closure of the open graph
when the height profile is continuous. Vertical approximation works for m=0. -/
theorem closure_graph_domain {m : ℕ} {h : Space m → ℝ} (hh : Continuous h) :
    closure {x : Space (m + 1) | h (horizontal x) < height x} =
      {x : Space (m + 1) | h (horizontal x) ≤ height x} := by
  apply subset_antisymm
  · apply closure_minimal ?_ (isClosed_le (hh.comp (horizontal_contDiff m).continuous)
      (height_contDiff m).continuous)
    intro x hx
    change h (horizontal x) ≤ height x
    exact (show h (horizontal x) < height x from hx).le
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨point (horizontal x) (height x + ε / 2), ?_, ?_⟩
    · simp only [mem_ofPred_eq, horizontal_point, height_point]
      exact hx.trans_lt (by linarith)
    · rw [dist_point_same_horizontal_height]
      have : height x - (height x + ε / 2) = -(ε / 2) := by ring
      rw [this, abs_neg, abs_of_pos (by positivity : 0 < ε / 2)]
      linarith

/-- The real closure of the graph-domain agrees with the closed tangent ball
in a whole neighborhood of the contact point. -/
theorem closure_spherical_graph_domain_eq_closedBall_near_zero
    {m : ℕ} {R : ℝ} (hR : 0 < R) {h : Space m → ℝ} (hh : Continuous h)
    (hgraph : ∀ u, ‖u‖ ≤ R / 4 → h u = R - Real.sqrt (R ^ 2 - ‖u‖ ^ 2)) :
    closure {x | h (horizontal x) < height x} ∩ ball 0 (R / 8) =
      closedBall (point (0 : Space m) R) R ∩ ball 0 (R / 8) := by
  rw [closure_graph_domain hh]
  exact spherical_closed_graph_domain_eq_closedBall_near_zero hR hgraph


/-- The graph and the tangent sphere share an actual relatively open boundary
patch around zero, expressed as equality of their ambient frontiers there. -/
theorem frontier_spherical_graph_domain_eq_sphere_near_zero
    {m : ℕ} {R : ℝ} (hR : 0 < R) {h : Space m → ℝ} (hh : Continuous h)
    (hgraph : ∀ u, ‖u‖ ≤ R / 4 → h u = R - Real.sqrt (R ^ 2 - ‖u‖ ^ 2)) :
    frontier {x | h (horizontal x) < height x} ∩ ball 0 (R / 8) =
      sphere (point (0 : Space m) R) R ∩ ball 0 (R / 8) := by
  have hopen : IsOpen {x : Space (m + 1) | h (horizontal x) < height x} :=
    isOpen_lt (hh.comp (horizontal_contDiff m).continuous) (height_contDiff m).continuous
  rw [hopen.frontier_eq, closure_graph_domain hh]
  have hcl := spherical_closed_graph_domain_eq_closedBall_near_zero hR hgraph
  have hop := spherical_graph_domain_eq_ball_near_zero hR hgraph
  ext x
  have hclx : x ∈ {y : Space (m + 1) | h (horizontal y) ≤ height y} ∩ ball 0 (R / 8) ↔
      x ∈ closedBall (point (0 : Space m) R) R ∩ ball 0 (R / 8) := by rw [hcl]
  have hopx : x ∈ {y : Space (m + 1) | h (horizontal y) < height y} ∩ ball 0 (R / 8) ↔
      x ∈ ball (point (0 : Space m) R) R ∩ ball 0 (R / 8) := by rw [hop]
  constructor
  · rintro ⟨⟨hxclosed, hxnot⟩, hxnear⟩
    have hdle := mem_closedBall.mp (hclx.mp ⟨hxclosed, hxnear⟩).1
    have hdge : R ≤ dist x (point (0 : Space m) R) := by
      by_contra hnot
      exact hxnot (hopx.mpr ⟨mem_ball.mpr (lt_of_not_ge hnot), hxnear⟩).1
    exact ⟨mem_sphere.mpr (le_antisymm hdle hdge), hxnear⟩
  · rintro ⟨hxsphere, hxnear⟩
    refine ⟨⟨(hclx.mpr ⟨sphere_subset_closedBall hxsphere, hxnear⟩).1, ?_⟩, hxnear⟩
    intro hxopen
    have hxball := (hopx.mp ⟨hxopen, hxnear⟩).1
    exact (mem_ball.mp hxball).ne (mem_sphere.mp hxsphere)

open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.HalfSpaceLift P201Specs.Elliptic.NewtonHessian
open P201.Elliptic.HalfSpaceLift P201.Elliptic.ChartSchauder
open P102.Sobolev.Geometry P102.U4.GraphPieces

/-- The actual spherical chart: first flatten the cutoff spherical graph,
then apply the given physical boundary chart. -/
def sphericalChartEquiv {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (s : ℝ) (hs : 0 < s) : Space (m + 1) ≃ Space (m + 1) :=
  (sphereFlatteningEquiv (lowerSphereCutoff s hs : Space m → ℝ)).trans
    (chartParametrization C)

/-- The lower sphere cutoff vanishes at the tangent point. -/
theorem lowerSphereCutoff_zero {m : ℕ} {s : ℝ} (hs : 0 < s) :
    lowerSphereCutoff s hs (0 : Space m) = 0 := by
  rw [lowerSphereCutoff_eq_graph hs (by simpa using (show 0 ≤ s / 4 by positivity))]
  simp [lowerSphereGraph, Real.sqrt_sq_eq_abs, abs_of_pos hs]

@[simp] theorem sphericalChartEquiv_zero {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {s : ℝ} (hs : 0 < s) : sphericalChartEquiv C s hs 0 = chartPoint C := by
  change chartParametrization C (sphereFlattening (lowerSphereCutoff s hs) 0) = _
  have hz : sphereFlattening (lowerSphereCutoff s hs : Space m → ℝ) 0 = 0 := by
    have hh0 : horizontal (0 : Space (m + 1)) = (0 : Space m) := by ext i; rfl
    have ht0 : height (0 : Space (m + 1)) = 0 := rfl
    rw [sphereFlattening, hh0, ht0, lowerSphereCutoff_zero hs, sub_self]
    simpa only [hh0, ht0] using (point_horizontal_height (0 : Space (m + 1)))
  rw [hz, chartParametrization_zero]

/-- A closed tangent sphere of radius s fits inside the given chart scale t
when 3s<2t. The physical chart need not be tangent or linear. -/
theorem sphericalChart_flat_region
    {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hsmall : 3 * s < 2 * t)
    (hflat : ball (0 : Space (m + 1)) (2 * t) ⊆ flatChartRegion C) :
    ∀ x ∈ closedBall (point (0 : Space m) s) s,
      sphereFlattening (lowerSphereCutoff s hs : Space m → ℝ) x ∈ flatChartRegion C := by
  intro x hx
  have hcenter : ‖point (0 : Space m) s‖ = s := by
    have he := norm_sq_horizontal_height (point (0 : Space m) s)
    simp only [height_point, horizontal_point, norm_zero] at he
    nlinarith [norm_nonneg (point (0 : Space m) s)]
  have hxn : ‖x‖ ≤ 2 * s := by
    have htri := norm_add_le (x - point (0 : Space m) s) (point (0 : Space m) s)
    rw [sub_add_cancel, ← dist_eq_norm, hcenter] at htri
    have hdist : dist x (point (0 : Space m) s) ≤ s := hx
    linarith
  have hb : ∀ y : Space m, 0 ≤ lowerSphereCutoff s hs y ∧ lowerSphereCutoff s hs y ≤ s :=
    fun y => ⟨(lowerSphereCutoff_bounds hs y).1,
      (lowerSphereCutoff_bounds hs y).2.trans (lowerSphereGraph_le_radius s y)⟩
  have hfn := sphereFlattening_norm_le hb x
  apply hflat
  rw [mem_ball, dist_zero_right]
  linarith

/-- The actual chart sends the entire spherical closed ball into the domain
closure and its interior into the domain. -/
theorem sphericalChart_maps_ball_and_closure
    {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hsmall : 3 * s < 2 * t)
    (hflat : ball (0 : Space (m + 1)) (2 * t) ⊆ flatChartRegion C) :
    MapsTo (sphericalChartEquiv C s hs) (closedBall (point (0 : Space m) s) s)
      (closure (Ω : Set (Space (m + 1)))) ∧
    MapsTo (sphericalChartEquiv C s hs) (ball (point (0 : Space m) s) s)
      (Ω : Set (Space (m + 1))) := by
  let h : Space m → ℝ := lowerSphereCutoff s hs
  have hclosed := closedBall_subset_spherical_closed_graph_domain hs
    (h := h) (fun y _ => (lowerSphereCutoff_bounds hs y).2)
  have hopen := ball_subset_spherical_graph_domain hs
    (h := h) (fun y _ => (lowerSphereCutoff_bounds hs y).2)
  constructor
  · intro x hx
    have hregion := sphericalChart_flat_region C ht hs hsmall hflat x hx
    apply (chartParametrization_mem_closure_iff C hregion).mpr
    change 0 ≤ height (sphereFlattening h x)
    rw [height_sphereFlattening]
    exact sub_nonneg.mpr (hclosed hx)
  · intro x hx
    have hregion := sphericalChart_flat_region C ht hs hsmall hflat x (ball_subset_closedBall hx)
    apply (chartParametrization_mem_domain_iff C hregion).mpr
    change 0 < height (sphereFlattening h x)
    rw [height_sphereFlattening]
    exact sub_pos.mpr (hopen hx)

/-- The spherical patch is sent to the actual physical frontier. -/
theorem sphericalChart_maps_spherical_patch
    {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hsmall : 3 * s < 2 * t)
    (hflat : ball (0 : Space (m + 1)) (2 * t) ⊆ flatChartRegion C) :
    MapsTo (sphericalChartEquiv C s hs)
      (sphere (point (0 : Space m) s) s ∩ ball 0 (s / 8))
      (frontier (Ω : Set (Space (m + 1)))) := by
  let h : Space m → ℝ := lowerSphereCutoff s hs
  have hgraph : ∀ y : Space m, ‖y‖ ≤ s / 4 →
      h y = s - Real.sqrt (s ^ 2 - ‖y‖ ^ 2) :=
    fun y hy => lowerSphereCutoff_eq_graph hs hy
  have hlocal := spherical_graph_domain_eq_ball_near_zero hs hgraph
  have hclosed := closedBall_subset_spherical_closed_graph_domain hs
    (h := h) (fun y _ => (lowerSphereCutoff_bounds hs y).2)
  intro x hx
  have hheight : h (horizontal x) = height x := by
    have hle := hclosed (sphere_subset_closedBall hx.1)
    by_contra hne
    have hlt : h (horizontal x) < height x := lt_of_le_of_ne hle hne
    have hxball : x ∈ ball (point (0 : Space m) s) s ∩ ball 0 (s / 8) := by
      rw [← hlocal]
      exact ⟨hlt, hx.2⟩
    exact (ne_of_lt hxball.1) hx.1
  have hregion := sphericalChart_flat_region C ht hs hsmall hflat x (sphere_subset_closedBall hx.1)
  apply (chartParametrization_mem_frontier_iff C hregion).mpr
  change height (sphereFlattening h x) = 0
  rw [height_sphereFlattening, hheight, sub_self]

/-- The flat-coordinate inverse is exactly the smooth sphere flattening. -/
@[simp] theorem sphericalChart_original_inverse
    {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {s : ℝ} (hs : 0 < s) (x : Space (m + 1)) :
    (chartParametrization C).symm (sphericalChartEquiv C s hs x) =
      sphereFlattening (lowerSphereCutoff s hs : Space m → ℝ) x :=
  (chartParametrization C).symm_apply_apply _

/-- The physical spherical image remains inside the actual graph chart. -/
theorem sphericalChart_image_in_physicalChart
    {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hsmall : 3 * s < 2 * t)
    (hflat : ball (0 : Space (m + 1)) (2 * t) ⊆ flatChartRegion C) :
    MapsTo (sphericalChartEquiv C s hs) (closedBall (point (0 : Space m) s) s)
      (physicalChart C) := by
  intro x hx
  have hregion := sphericalChart_flat_region C ht hs hsmall hflat x hx
  change chartParametrization C (sphereFlattening (lowerSphereCutoff s hs) x) ∈ physicalChart C
  exact ⟨_, ⟨_, ⟨_, hregion, rfl⟩, rfl⟩, rfl⟩

/-- Both actual inverse and forward charts are C² at all source closed-ball
points. The physical boundary chart has only its original C² regularity. -/
theorem sphericalChart_contDiffAt_two
    {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hsmall : 3 * s < 2 * t)
    (hflat : ball (0 : Space (m + 1)) (2 * t) ⊆ flatChartRegion C) :
    ∀ x ∈ closedBall (point (0 : Space m) s) s,
      ContDiffAt ℝ 2 (sphericalChartEquiv C s hs) x ∧
      ContDiffAt ℝ 2 (sphericalChartEquiv C s hs).symm (sphericalChartEquiv C s hs x) := by
  let h : Space m → ℝ := lowerSphereCutoff s hs
  have hh : ContDiff ℝ ∞ h := lowerSphereCutoff_contDiff hs
  intro x hx
  have hregion := sphericalChart_flat_region C ht hs hsmall hflat x hx
  have hΦ : ContDiffAt ℝ 2 (chartParametrization C) (sphereFlattening h x) :=
    chartParametrization_contDiffAt C hγ hregion.1
  have hibase : (C.frame.symm ((graphFrame m).symm
      (chartParametrization C (sphereFlattening h x)))).ofLp.1 ∈
      ball C.center C.radius := by
    simpa only [chartParametrization_apply, LinearIsometryEquiv.symm_apply_apply,
      AffineIsometryEquiv.symm_apply_apply, shear, WithLp.ofLp_toLp] using hregion.1
  have hiΦ : ContDiffAt ℝ 2 (chartParametrization C).symm
      (chartParametrization C (sphereFlattening h x)) :=
    chartParametrization_symm_contDiffAt C hγ hibase
  constructor
  · change ContDiffAt ℝ 2 ((chartParametrization C) ∘ sphereFlattening h) x
    exact hΦ.comp x ((sphereFlattening_contDiff hh).of_le (by simp)).contDiffAt
  · change ContDiffAt ℝ 2
      (sphereUnflattening h ∘ (chartParametrization C).symm)
      (chartParametrization C (sphereFlattening h x))
    exact ((sphereUnflattening_contDiff hh).of_le (by simp)).contDiffAt.comp _ hiΦ

/-- The inverse spherical chart sends a full physical closure neighborhood
into the actual closed sphere ball on its shared spherical patch. -/
theorem exists_sphericalChart_physical_inner_radius
    {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {s : ℝ} (hs : 0 < s) :
    ∃ ρ : ℝ, 0 < ρ ∧ MapsTo (sphericalChartEquiv C s hs).symm
      (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) ρ)
      (closedBall (point (0 : Space m) s) s ∩ ball 0 (s / 16)) := by
  let h : Space m → ℝ := lowerSphereCutoff s hs
  let e := sphericalChartEquiv C s hs
  have hh : ContDiff ℝ ∞ h := lowerSphereCutoff_contDiff hs
  have hbase : (C.frame.symm ((graphFrame m).symm (chartPoint C))).ofLp.1 ∈
      ball C.center C.radius := by
    simp only [chartPoint, LinearIsometryEquiv.symm_apply_apply,
      AffineIsometryEquiv.symm_apply_apply, graph, WithLp.ofLp_toLp]
    exact mem_ball_self C.radius_pos
  have hiΦ : ContDiffAt ℝ 2 (chartParametrization C).symm (chartPoint C) :=
    chartParametrization_symm_contDiffAt C hγ hbase
  have hi : ContDiffAt ℝ 2 (e.symm : Space (m + 1) → Space (m + 1)) (chartPoint C) := by
    change ContDiffAt ℝ 2
      (sphereUnflattening h ∘ (chartParametrization C).symm) (chartPoint C)
    exact ((sphereUnflattening_contDiff hh).of_le (by simp)).contDiffAt.comp _ hiΦ
  have he0 : e 0 = chartPoint C := sphericalChartEquiv_zero C hs
  have hie0 : e.symm (chartPoint C) = 0 := by rw [← he0, Equiv.symm_apply_apply]
  have hnear : e.symm ⁻¹' ball (0 : Space (m + 1)) (s / 16) ∈ 𝓝 (chartPoint C) := by
    apply hi.continuousAt.preimage_mem_nhds
    rw [hie0]
    exact ball_mem_nhds 0 (by positivity)
  have hnbd : (e.symm ⁻¹' ball (0 : Space (m + 1)) (s / 16) ∩ physicalChart C) ∈
      𝓝 (chartPoint C) :=
    Filter.inter_mem hnear ((physicalChart_open C).mem_nhds (chartPoint_mem C))
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hnbd
  refine ⟨ρ, hρ, ?_⟩
  intro x hx
  have hsmall := (hsub hx.2).1
  have hphysical := (hsub hx.2).2
  have hregion := chartParametrization_symm_mem_flatChartRegion C hphysical
  have hheight : 0 ≤ height ((chartParametrization C).symm x) := by
    apply (chartParametrization_mem_closure_iff C hregion).mp
    simpa only [Equiv.apply_symm_apply] using hx.1
  have hflatInverse : sphereFlattening h (e.symm x) = (chartParametrization C).symm x := by
    have heq := sphericalChart_original_inverse C hs (e.symm x)
    change (chartParametrization C).symm (e (e.symm x)) = sphereFlattening h (e.symm x) at heq
    rw [Equiv.apply_symm_apply] at heq
    exact heq.symm
  rw [← hflatInverse, height_sphereFlattening] at hheight
  have hgraph : h (horizontal (e.symm x)) ≤ height (e.symm x) := sub_nonneg.mp hheight
  have heq := spherical_closed_graph_domain_eq_closedBall_near_zero hs
    (h := h) (fun y hy => lowerSphereCutoff_eq_graph hs hy)
  have hy8 : e.symm x ∈ ball (0 : Space (m + 1)) (s / 8) :=
    ball_subset_ball (by linarith) hsmall
  have hball : e.symm x ∈ closedBall (point (0 : Space m) s) s ∩ ball 0 (s / 8) := by
    rw [← heq]
    exact ⟨hgraph, hy8⟩
  exact ⟨hball.1, hsmall⟩


/-- Original flat chart inverse coordinates of the spherical ball are bounded
by 3s; this is independent of the chart coefficients and their derivatives. -/
theorem sphericalChart_original_inverse_norm_le
    {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {s : ℝ} (hs : 0 < s) {x : Space (m + 1)}
    (hx : x ∈ closedBall (point (0 : Space m) s) s) :
    ‖(chartParametrization C).symm (sphericalChartEquiv C s hs x)‖ ≤ 3 * s := by
  rw [sphericalChart_original_inverse]
  have hcenter : ‖point (0 : Space m) s‖ = s := by
    have he := norm_sq_horizontal_height (point (0 : Space m) s)
    simp only [height_point, horizontal_point, norm_zero] at he
    nlinarith [norm_nonneg (point (0 : Space m) s)]
  have hxn : ‖x‖ ≤ 2 * s := by
    have htri := norm_add_le (x - point (0 : Space m) s) (point (0 : Space m) s)
    rw [sub_add_cancel, ← dist_eq_norm, hcenter] at htri
    have hdist : dist x (point (0 : Space m) s) ≤ s := hx
    linarith
  have hb : ∀ y : Space m, 0 ≤ lowerSphereCutoff s hs y ∧ lowerSphereCutoff s hs y ≤ s :=
    fun y => ⟨(lowerSphereCutoff_bounds hs y).1,
      (lowerSphereCutoff_bounds hs y).2.trans (lowerSphereGraph_le_radius s y)⟩
  have hfn := sphereFlattening_norm_le hb x
  linarith

/-- All physical image points lie in the exact inverse-chart base disk
where the actual graph Jacobian and Hessian have their Hölder bounds. -/
theorem sphericalChart_image_in_inverse_base
    {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hsmall : 3 * s < 2 * t)
    (hflat : ball (0 : Space (m + 1)) (2 * t) ⊆ flatChartRegion C) :
    MapsTo (sphericalChartEquiv C s hs) (closedBall (point (0 : Space m) s) s)
      ((inverseChartBaseMap C) ⁻¹' ball C.center C.radius) := by
  intro x hx
  exact physicalChart_inverse_base C
    (sphericalChart_image_in_physicalChart C ht hs hsmall hflat hx)

end SphericalCoordinates


/-- Local coincidence of the actual closed domains transports local boundary
regularity, including its actual within derivatives, without any boundary
regularity assumption on the parts outside the observation set. -/
theorem isC2HolderLocUpToOn_of_closure_inter_eq {n : ℕ} {α : ℝ}
    {Ω B U : Domain n} {u : Space n → ℝ}
    (heq : closure (Ω : Set (Space n)) ∩ (U : Set (Space n)) =
      closure (B : Set (Space n)) ∩ (U : Set (Space n)))
    (hu : IsC2HolderLocUpToOn α u B U) : IsC2HolderLocUpToOn α u Ω U := by
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hu.1
  · intro x hx
    have hxB : x ∈ closure (B : Set (Space n)) ∩ (U : Set (Space n)) := heq ▸ hx
    obtain ⟨r, hr, hball, hholder⟩ := hu.2 x hxB
    refine ⟨r, hr, hball, ?_⟩
    have hlocaleq : closure (Ω : Set (Space n)) ∩ ball x r =
        closure (B : Set (Space n)) ∩ ball x r := by
      ext y
      constructor
      · intro hy
        have hyU : y ∈ closure (Ω : Set (Space n)) ∩ (U : Set (Space n)) :=
          ⟨hy.1, hball hy.2⟩
        rw [heq] at hyU
        exact ⟨hyU.1, hy.2⟩
      · intro hy
        have hyU : y ∈ closure (B : Set (Space n)) ∩ (U : Set (Space n)) :=
          ⟨hy.1, hball hy.2⟩
        rw [← heq] at hyU
        exact ⟨hyU.1, hy.2⟩
    rw [hlocaleq]
    exact hholder


/-- Equality on an ambient open neighborhood gives equality of the actual
closed sets on that same neighborhood. -/
theorem closure_inter_eq_of_inter_eq {n : ℕ} {s t : Set (Space n)} {U : Domain n}
    (heq : s ∩ (U : Set (Space n)) = t ∩ (U : Set (Space n))) :
    closure s ∩ (U : Set (Space n)) = closure t ∩ (U : Set (Space n)) := by
  apply subset_antisymm
  · intro x hx
    have hxlocal : x ∈ closure (s ∩ (U : Set (Space n))) := U.isOpen.closure_inter hx
    rw [heq] at hxlocal
    exact ⟨closure_mono inter_subset_left hxlocal, hx.2⟩
  · intro x hx
    have hxlocal : x ∈ closure (t ∩ (U : Set (Space n))) := U.isOpen.closure_inter hx
    rw [← heq] at hxlocal
    exact ⟨closure_mono inter_subset_left hxlocal, hx.2⟩

/-- Local equality of the domains suffices to transport the whole local
boundary regularity assertion, including its one-sided derivatives. -/
theorem isC2HolderLocUpToOn_of_inter_eq {n : ℕ} {α : ℝ}
    {Ω B U : Domain n} {u : Space n → ℝ}
    (heq : (Ω : Set (Space n)) ∩ (U : Set (Space n)) =
      (B : Set (Space n)) ∩ (U : Set (Space n)))
    (hu : IsC2HolderLocUpToOn α u B U) : IsC2HolderLocUpToOn α u Ω U :=
  isC2HolderLocUpToOn_of_closure_inter_eq (closure_inter_eq_of_inter_eq heq) hu

namespace JetComposition
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder
open P201.Elliptic.ConstantSchauder P201.Elliptic.ChartSchauder
open P201.Elliptic.PoissonSchauder

theorem firstPartial_coordinate {n : ℕ} {Φ : Space n → Space n} {x : Space n}
    (hΦ : DifferentiableAt ℝ Φ x) (i k : Fin n) :
    firstPartial (fun y => Φ y k) i x = (fderiv ℝ Φ x (coordinate n i)) k := by
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k
  have h := P.hasFDerivAt.comp x hΦ.hasFDerivAt
  change HasFDerivAt (fun y => Φ y k) (P.comp (fderiv ℝ Φ x)) x at h
  rw [firstPartial, h.fderiv]
  rfl

theorem secondPartial_coordinate {n : ℕ} {Φ : Space n → Space n} {x : Space n}
    (hΦ : ContDiffAt ℝ 2 Φ x) (i j k : Fin n) :
    secondPartial (fun y => Φ y k) i j x =
      (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k := by
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k
  have h := secondPartial_comp_nonlinear P.contDiff.contDiffAt hΦ i j
  have hdP : fderiv ℝ (P : Space n → ℝ) = fun _ => P := by
    funext y
    exact P.fderiv
  have hddP : fderiv ℝ (fderiv ℝ (P : Space n → ℝ)) (Φ x) = 0 := by
    rw [hdP]
    simp
  simp only [hddP, zero_apply, zero_add] at h
  simpa only [P, ContinuousLinearMap.fderiv, Function.comp_def, PiLp.proj_apply] using h

theorem jacobian_comp_coordinates {n : ℕ}
    {Φ Ψ : Space n → Space n} {x : Space n}
    (hΦ : ContDiffAt ℝ 2 Φ x) (hΨ : ContDiffAt ℝ 2 Ψ (Φ x)) (i k : Fin n) :
    (fderiv ℝ (Ψ ∘ Φ) x (coordinate n i)) k =
      ∑ j : Fin n, (fderiv ℝ Φ x (coordinate n i)) j *
        (fderiv ℝ Ψ (Φ x) (coordinate n j)) k := by
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k
  have hPk : ContDiffAt ℝ 2 (fun y => Ψ y k) (Φ x) :=
    P.contDiff.contDiffAt.comp (Φ x) hΨ
  have h := firstPartial_comp_nonlinear (hPk.differentiableAt (by norm_num))
    (hΦ.differentiableAt (by norm_num)) i
  rw [← firstPartial_coordinate ((hΨ.comp x hΦ).differentiableAt (by norm_num)) i k]
  simpa only [firstPartial_coordinate (hΨ.differentiableAt (by norm_num)), Function.comp_def] using h

theorem hessian_comp_coordinates {n : ℕ}
    {Φ Ψ : Space n → Space n} {x : Space n}
    (hΦ : ContDiffAt ℝ 2 Φ x) (hΨ : ContDiffAt ℝ 2 Ψ (Φ x)) (i j k : Fin n) :
    (fderiv ℝ (fderiv ℝ (Ψ ∘ Φ)) x (coordinate n i) (coordinate n j)) k =
      (∑ p : Fin n, ∑ q : Fin n,
        (fderiv ℝ Φ x (coordinate n i)) p *
        (fderiv ℝ Φ x (coordinate n j)) q *
        (fderiv ℝ (fderiv ℝ Ψ) (Φ x) (coordinate n p) (coordinate n q)) k) +
      ∑ p : Fin n, (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) p *
        (fderiv ℝ Ψ (Φ x) (coordinate n p)) k := by
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k
  have hPk : ContDiffAt ℝ 2 (fun y => Ψ y k) (Φ x) :=
    P.contDiff.contDiffAt.comp (Φ x) hΨ
  have h := secondPartial_comp_nonlinear_coordinates hPk hΦ i j
  rw [← secondPartial_coordinate (hΨ.comp x hΦ) i j k]
  simpa only [secondPartial_coordinate hΨ,
    firstPartial_coordinate (hΨ.differentiableAt (by norm_num)), Function.comp_def] using h

/-- Genuine scalar Jacobian and Hessian Hölder data compose. This applies
to a smooth spherical shear after a C²,α inverse boundary chart without
asserting that the inverse boundary chart is globally smooth. -/
theorem holder_derivatives_comp {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {Φ Ψ : Space n → Space n} {s t : Set (Space n)} {L : ℝ≥0}
    (hΦ : ∀ x ∈ s, ContDiffAt ℝ 2 Φ x)
    (hΨ : ∀ y ∈ t, ContDiffAt ℝ 2 Ψ y)
    (hLip : LipschitzOnWith L Φ s) (hmap : MapsTo Φ s t)
    (hΦJac : ∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s)
    (hΦHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s)
    (hΨJac : ∀ i k, IsHolderOn α
      (fun y => (fderiv ℝ Ψ y (coordinate n i)) k) t)
    (hΨHess : ∀ i j k, IsHolderOn α
      (fun y => (fderiv ℝ (fderiv ℝ Ψ) y (coordinate n i) (coordinate n j)) k) t) :
    (∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ (Ψ ∘ Φ) x (coordinate n i)) k) s) ∧
    (∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ (Ψ ∘ Φ)) x
        (coordinate n i) (coordinate n j)) k) s) := by
  have hJ (i k : Fin n) : IsHolderOn α
      (fun x => (fderiv ℝ Ψ (Φ x) (coordinate n i)) k) s :=
    (holder_pullback_lipschitz hα (hΨJac i k) hLip hmap).1
  have hH (i j k : Fin n) : IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ Ψ) (Φ x) (coordinate n i) (coordinate n j)) k) s :=
    (holder_pullback_lipschitz hα (hΨHess i j k) hLip hmap).1
  refine ⟨?_, ?_⟩
  · intro i k
    apply isHolderOn_congr (isHolderOn_finset_sum Finset.univ _ (fun j _ =>
      isHolderOn_mul (hΦJac i j) (hJ j k)))
    intro x hx
    exact jacobian_comp_coordinates (hΦ x hx) (hΨ _ (hmap hx)) i k
  · intro i j k
    apply isHolderOn_congr (isHolderOn_add
      (isHolderOn_finset_sum Finset.univ _ (fun p _ =>
        isHolderOn_finset_sum Finset.univ _ (fun q _ =>
          isHolderOn_mul (isHolderOn_mul (hΦJac i p) (hΦJac j q)) (hH p q k))))
      (isHolderOn_finset_sum Finset.univ _ (fun p _ =>
        isHolderOn_mul (hΦHess i j p) (hJ p k))))
    intro x hx
    exact hessian_comp_coordinates (hΦ x hx) (hΨ _ (hmap hx)) i j k

theorem exists_holder_derivative_bound_comp {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {Φ Ψ : Space n → Space n} {s t : Set (Space n)} {L : ℝ≥0}
    (hΦ : ∀ x ∈ s, ContDiffAt ℝ 2 Φ x)
    (hΨ : ∀ y ∈ t, ContDiffAt ℝ 2 Ψ y)
    (hLip : LipschitzOnWith L Φ s) (hmap : MapsTo Φ s t)
    (hΦJac : ∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s)
    (hΦHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s)
    (hΨJac : ∀ i k, IsHolderOn α
      (fun y => (fderiv ℝ Ψ y (coordinate n i)) k) t)
    (hΨHess : ∀ i j k, IsHolderOn α
      (fun y => (fderiv ℝ (fderiv ℝ Ψ) y (coordinate n i) (coordinate n j)) k) t) :
    ∃ D : ℝ, 0 < D ∧
      (∀ i k, IsHolderOn α
        (fun x => (fderiv ℝ (Ψ ∘ Φ) x (coordinate n i)) k) s ∧
        holderNormOn α (fun x => (fderiv ℝ (Ψ ∘ Φ) x (coordinate n i)) k) s ≤ D) ∧
      (∀ i j k, IsHolderOn α
        (fun x => (fderiv ℝ (fderiv ℝ (Ψ ∘ Φ)) x (coordinate n i) (coordinate n j)) k) s ∧
        holderNormOn α (fun x => (fderiv ℝ (fderiv ℝ (Ψ ∘ Φ)) x
          (coordinate n i) (coordinate n j)) k) s ≤ D) := by
  obtain ⟨hJ, hH⟩ := holder_derivatives_comp hα hΦ hΨ hLip hmap hΦJac hΦHess hΨJac hΨHess
  obtain ⟨D, hD, hJN, hHN⟩ := exists_positive_holder_derivative_bound hJ hH
  exact ⟨D, hD, fun i k => ⟨hJ i k, hJN i k⟩,
    fun i j k => ⟨hH i j k, hHN i j k⟩⟩

/-- Reverse transport of a spherical-patch solution to a physical patch.
The target must be convex to control its lower derivatives; the physical
source only needs unique one-sided derivatives. All map jets are actual
ambient jets and are identified with the genuine within jets in the proof. -/
theorem upToOn_comp_of_ambient_holder_derivatives {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {Φ : Space n → Space n} {s t : Set (Space n)} {L : ℝ≥0}
    (hc : Convex ℝ t) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hΦ : ∀ x ∈ s, ContDiffAt ℝ 2 Φ x)
    (hmap : MapsTo Φ s t) (hLip : LipschitzOnWith L Φ s)
    (hJac : ∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s)
    (hHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x
        (coordinate n i) (coordinate n j)) k) s)
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u t) :
    IsC2HolderUpToOn α (u ∘ Φ) s := by
  obtain ⟨D, hD, hJN, hHN⟩ := exists_positive_holder_derivative_bound hJac hHess
  have hambient (x : Space n) (hx : x ∈ s) := ambient_chart_within_derivatives hs hΦ hx
  have hJ (i k : Fin n) : EqOn
      (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k)
      (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s := by
    intro x hx
    exact congrArg (fun T : Space n →L[ℝ] Space n => (T (coordinate n i)) k)
      (hambient x hx).1
  have hH (i j k : Fin n) : EqOn
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
        (coordinate n i) (coordinate n j)) k)
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x
        (coordinate n i) (coordinate n j)) k) s := by
    intro x hx
    exact congrArg (fun T : Space n →L[ℝ] Space n →L[ℝ] Space n =>
      (T (coordinate n i) (coordinate n j)) k) (hambient x hx).2
  apply (c2HolderUpToOn_comp_from_convex_target hα hα1 hc hs ht
    (fun x hx => (hΦ x hx).contDiffWithinAt) hmap hLip hD.le hD.le
    (fun i k => isHolderOn_congr (hJac i k) (hJ i k))
    (fun i k => ?_) (fun i j k => isHolderOn_congr (hHess i j k) (hH i j k))
    (fun i j k => ?_) hu).1
  · rw [P201.Elliptic.ChartSchauder.holderNormOn_congr (hJ i k)]
    exact hJN i k
  · rw [P201.Elliptic.ChartSchauder.holderNormOn_congr (hH i j k)]
    exact hHN i j k

end JetComposition

namespace BoundaryTransport
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201.Elliptic.ConstantSchauder P201.Elliptic.ChartSchauder
open P201.Elliptic.PoissonSchauder

/-- The coefficient class needed by the actual ball theorem follows from
the original coefficients and actual derivative fields of the inverse map.
The containing physical observation set need not be convex or open. -/
theorem transformed_coefficients_holder_pullback
    {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (e : Space n ≃ Space n)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s t : Set (Space n)} {L : ℝ≥0}
    (hcoeff : CoefficientsHolderOn α a b c t)
    (he : LipschitzOnWith L e s) (hmap : MapsTo e s t)
    (hJac : ∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ e.symm x (coordinate n i)) k) t)
    (hHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ e.symm) x
        (coordinate n i) (coordinate n j)) k) t) :
    CoefficientsHolderOn α
      (fun y => transformedPrincipalAt a e.symm (e y))
      (fun y => WithLp.toLp 2 (transformedDriftAt a b e.symm (e y)))
      (c ∘ e) s := by
  have hP (k l : Fin n) :
      IsHolderOn α (fun x => transformedPrincipalAt a e.symm x k l) t := by
    unfold transformedPrincipalAt
    apply isHolderOn_finset_sum Finset.univ
    intro i hi
    apply isHolderOn_finset_sum Finset.univ
    intro j hj
    exact isHolderOn_mul (isHolderOn_mul (hcoeff.1 i j) (hJac i k)) (hJac j l)
  have hB (k : Fin n) :
      IsHolderOn α (fun x => transformedDriftAt a b e.symm x k) t := by
    unfold transformedDriftAt
    apply isHolderOn_add
    · apply isHolderOn_finset_sum Finset.univ
      intro i hi
      apply isHolderOn_finset_sum Finset.univ
      intro j hj
      exact isHolderOn_mul (hcoeff.1 i j) (hHess i j k)
    · apply isHolderOn_finset_sum Finset.univ
      intro i hi
      exact isHolderOn_mul (hcoeff.2.1 i) (hJac i k)
  exact ⟨fun i j => (holder_pullback_lipschitz hα (hP i j) he hmap).1,
    fun i => (holder_pullback_lipschitz hα (hB i) he hmap).1,
    (holder_pullback_lipschitz hα hcoeff.2.2 he hmap).1⟩

/-- A bounded genuine forward derivative controls the transformed lower
ellipticity bound. Both inverse identities come from the actual equivalence. -/
theorem transformed_uniformlyEllipticOn
    {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell) (hL : 0 < L)
    (e : Space n ≃ Space n)
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {s t : Set (Space n)}
    (ha : UniformlyEllipticOn ell a t) (hmap : MapsTo e s t)
    (he : ∀ y ∈ s, DifferentiableAt ℝ e y)
    (hi : ∀ y ∈ s, DifferentiableAt ℝ e.symm (e y))
    (hbound : ∀ y ∈ s, ‖fderiv ℝ e y‖ ≤ L) :
    UniformlyEllipticOn (ell / L^2)
      (fun y => transformedPrincipalAt a e.symm (e y)) s := by
  refine ⟨fun y hy => transformedPrincipalAt_symmetric a e.symm (e y) (ha.1 _ (hmap hy)), ?_⟩
  intro y hy ξ
  obtain ⟨T, hT, hTi⟩ := derivative_equiv_of_inverse e (he y hy) (hi y hy)
  apply transformedPrincipalAt_lower_bound hell hL (ha.2 _ (hmap hy)) T.symm hTi
  change ‖T.toContinuousLinearMap‖ ≤ L
  rw [← hT]
  exact hbound y hy

theorem isC2HolderUpToOn_zero {n : ℕ} (α : ℝ) (s : Set (Space n)) :
    IsC2HolderUpToOn α (fun _ => 0) s := by
  have hfirst (i : Fin n) : firstPartialWithin (fun _ : Space n => (0 : ℝ)) s i = 0 := by
    funext x
    simp [firstPartialWithin]
  have hsecond (i j : Fin n) :
      secondPartialWithin (fun _ : Space n => (0 : ℝ)) s i j = 0 := by
    funext x
    simp [secondPartialWithin, hfirst, firstPartialWithin]
  refine ⟨contDiffOn_const, ⟨0, le_rfl, by simp⟩, ?_, ?_⟩
  · intro i
    exact ⟨0, le_rfl, by simp [hfirst]⟩
  · intro i j
    exact ⟨0, 0, le_rfl, le_rfl, by simp [hsecond], by simp [hsecond]⟩

/-- The exact supplied ball boundary premise applies directly to any existing
classical solution with zero data on an open spherical patch. The actual
initially-C² regularity premise supplies its required interior Hölder class. -/
theorem classical_ball_boundary_regularity_zero
    (hlocal : P201Specs.Elliptic.SchauderRegularity.LocalRegularityStatement)
    (hboundary : P201Specs.Elliptic.BallSchauderSolvability.LocalBoundaryRegularityStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (z : Space n) (r : ℝ) (hr : 0 < r)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c f u : Space n → ℝ)
    (ha : UniformlyEllipticOn ell a (closedBall z r))
    (hcoeff : CoefficientsHolderOn α a b c (closedBall z r))
    (hc : ∀ x ∈ closedBall z r, c x ≤ 0)
    (hf : IsHolderOn α f (closedBall z r))
    (hu : ContDiffOn ℝ 2 u (ball z r)) (huc : ContinuousOn u (closedBall z r))
    (hLu : ∀ x ∈ ball z r, nondivergenceOperator a b c u x = f x)
    (U : Domain n) (htrace : ∀ x ∈ sphere z r, x ∈ (U : Set (Space n)) → u x = 0)
    (V : Domain n) (hbV : Bornology.IsBounded (V : Set (Space n)))
    (hVU : closure (V : Set (Space n)) ⊆ (U : Set (Space n))) :
    IsC2HolderUpToOn α u (closedBall z r ∩ (V : Set (Space n))) := by
  let B := P201Specs.Elliptic.BallSchauderSolvability.ballDomain z r
  have hcoeffB : CoefficientsHolderOn α a b c B :=
    ⟨fun i j => isHolderOn_mono (hcoeff.1 i j) ball_subset_closedBall,
      fun i => isHolderOn_mono (hcoeff.2.1 i) ball_subset_closedBall,
      isHolderOn_mono hcoeff.2.2 ball_subset_closedBall⟩
  have hcoeffLoc : CoefficientsHolderLoc α a b c B :=
    ⟨fun i j => isHolderLoc_of_isHolderOn (hcoeffB.1 i j),
      fun i => isHolderLoc_of_isHolderOn (hcoeffB.2.1 i),
      isHolderLoc_of_isHolderOn hcoeffB.2.2⟩
  have haLoc : P201Specs.Elliptic.SchauderRegularity.LocallyUniformlyEllipticOn a B := by
    intro x hx
    obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
    exact ⟨ρ, hρ, hρB, ell, hell,
      (fun y hy => ha.1 y (ball_subset_closedBall (hρB hy))),
      (fun y hy => ha.2 y (ball_subset_closedBall (hρB hy)))⟩
  have hureg : IsC2HolderLocOn α u B := hlocal hn α hα hα1 B a b c u f
    haLoc hcoeffLoc hu (isHolderLoc_of_isHolderOn (isHolderOn_mono hf ball_subset_closedBall)) hLu
  let g : C(sphere z r, ℝ) := ⟨fun x => u x, (huc.mono sphere_subset_closedBall).domRestrict⟩
  have hball : P201Specs.Elliptic.BallSchauderSolvability.IsBallSolution a b c f z r g u :=
    ⟨hu, huc, hLu, fun _ => rfl⟩
  have hzero : IsC2HolderLocUpToOn α (fun _ : Space n => 0) B U := by
    refine ⟨contDiffOn_const, ?_⟩
    intro x hx
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp U.isOpen x hx.2
    exact ⟨ρ, hρ, hρU, isC2HolderUpToOn_zero α _⟩
  exact hboundary hn α hα hα1 z r hr a b c ⟨ell, hell, ha⟩ hcoeff hc f hf g u hball
    hureg U (fun _ => 0) hzero (fun x hx => htrace x x.property hx) V hbV hVU

/-- A generic sphericalizing equivalence transfers an existing zero-trace
classical solution to the actual ball boundary theorem. All geometric and
inverse-jet inputs are explicit; none assert regularity of the solution. -/
theorem zero_solution_spherical_pullback_regularity
    (hlocal : P201Specs.Elliptic.SchauderRegularity.LocalRegularityStatement)
    (hboundary : P201Specs.Elliptic.BallSchauderSolvability.LocalBoundaryRegularityStatement)
    {n : ℕ} (hn : 1 ≤ n) {α ell D : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hD : 0 < D) (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c f u : Space n → ℝ) (e : Space n ≃ Space n)
    {t : Set (Space n)} (ht : t ⊆ closure (Ω : Set (Space n)))
    (z : Space n) (r : ℝ) (hr : 0 < r) {L : ℝ≥0}
    (ha : UniformlyEllipticOn ell a t) (hcoeff : CoefficientsHolderOn α a b c t)
    (hc : ∀ x ∈ t, c x ≤ 0) (hf : IsHolderOn α f t)
    (hu : ContDiffOn ℝ 2 u Ω) (huc : ContinuousOn u (closure (Ω : Set (Space n))))
    (hLu : ∀ x ∈ Ω, nondivergenceOperator a b c u x = f x)
    (hub : ∀ x ∈ frontier (Ω : Set (Space n)), u x = 0)
    (hmap : MapsTo e (closedBall z r) t) (hmapInterior : MapsTo e (ball z r) Ω)
    (he : ∀ y ∈ closedBall z r, ContDiffAt ℝ 2 e y)
    (hi : ∀ y ∈ closedBall z r, ContDiffAt ℝ 2 e.symm (e y))
    (heLip : LipschitzOnWith L e (closedBall z r))
    (heD : ∀ y ∈ closedBall z r, ‖fderiv ℝ e y‖ ≤ D)
    (hJac : ∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ e.symm x (coordinate n i)) k) t)
    (hHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ e.symm) x
        (coordinate n i) (coordinate n j)) k) t)
    (U : Domain n)
    (hshared : ∀ y ∈ sphere z r, y ∈ (U : Set (Space n)) →
      e y ∈ frontier (Ω : Set (Space n)))
    (V : Domain n) (hbV : Bornology.IsBounded (V : Set (Space n)))
    (hVU : closure (V : Set (Space n)) ⊆ (U : Set (Space n))) :
    IsC2HolderUpToOn α (u ∘ e) (closedBall z r ∩ (V : Set (Space n))) := by
  let A := fun y => transformedPrincipalAt a e.symm (e y)
  let B := fun y => (WithLp.toLp 2 (transformedDriftAt a b e.symm (e y)) : Space n)
  let C := c ∘ e
  have ha' : UniformlyEllipticOn (ell / D^2) A (closedBall z r) :=
    transformed_uniformlyEllipticOn hell.le hD e ha hmap
      (fun y hy => (he y hy).differentiableAt (by norm_num))
      (fun y hy => (hi y hy).differentiableAt (by norm_num)) heD
  have hcoeff' : CoefficientsHolderOn α A B C (closedBall z r) :=
    transformed_coefficients_holder_pullback hα.le e hcoeff heLip hmap hJac hHess
  have hf' : IsHolderOn α (f ∘ e) (closedBall z r) :=
    (holder_pullback_lipschitz hα.le hf heLip hmap).1
  have hu' : ContDiffOn ℝ 2 (u ∘ e) (ball z r) := by
    intro y hy
    exact (((hu _ (hmapInterior hy)).contDiffAt
      (Ω.isOpen.mem_nhds (hmapInterior hy))).comp y
      (he y (ball_subset_closedBall hy))).contDiffWithinAt
  have huc' : ContinuousOn (u ∘ e) (closedBall z r) :=
    huc.comp (fun y hy => (he y hy).continuousAt.continuousWithinAt)
      (fun y hy => ht (hmap hy))
  have hLu' : ∀ y ∈ ball z r, nondivergenceOperator A B C (u ∘ e) y = (f ∘ e) y := by
    intro y hy
    exact equation_pullback e a b c
      ((hu _ (hmapInterior hy)).contDiffAt (Ω.isOpen.mem_nhds (hmapInterior hy)))
      (he y (ball_subset_closedBall hy)) (hi y (ball_subset_closedBall hy))
      (hLu _ (hmapInterior hy))
  apply classical_ball_boundary_regularity_zero hlocal hboundary hn hα hα1
    (div_pos hell (sq_pos_of_pos hD)) z r hr A B C (f ∘ e) (u ∘ e)
    ha' hcoeff' (fun y hy => hc _ (hmap hy)) hf' hu' huc' hLu' U ?_ V hbV hVU
  intro y hy hyU
  exact hub _ (hshared y hy hyU)

/-- An actual spherical-patch regularity conclusion pulls back to the
physical patch. The source may be nonconvex; convexity is imposed only on
the spherical target where lower-jet control is available. -/
theorem c2HolderUpToOn_pullback_inverse {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (e : Space n ≃ Space n)
    {s S : Set (Space n)} {L : ℝ≥0}
    (hSconv : Convex ℝ S) (hs : UniqueDiffOn ℝ s) (hS : UniqueDiffOn ℝ S)
    (hi : ∀ x ∈ s, ContDiffAt ℝ 2 e.symm x)
    (hmap : MapsTo e.symm s S) (hLip : LipschitzOnWith L e.symm s)
    (hJac : ∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ e.symm x (coordinate n i)) k) s)
    (hHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ e.symm) x
        (coordinate n i) (coordinate n j)) k) s)
    {u : Space n → ℝ} (hreg : IsC2HolderUpToOn α (u ∘ e) S) :
    IsC2HolderUpToOn α u s := by
  have h := JetComposition.upToOn_comp_of_ambient_holder_derivatives hα hα1
    hSconv hs hS hi hmap hLip hJac hHess hreg
  have hid : (u ∘ e) ∘ e.symm = u := by
    funext x
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rwa [hid] at h

end BoundaryTransport


namespace SphericalAnalytic
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder P201Specs.Elliptic.VariableSchauder
open P201Specs.Elliptic.HalfSpaceLift
open P201.Elliptic.ConstantSchauder P201.Elliptic.ChartSchauder
open P201.Elliptic.PoissonSchauder P201.Elliptic.SchauderDirichlet
open P102.Sobolev.Geometry P102.U4.GraphPieces

theorem sphericalizing_map_analytic_data
    {m : ℕ} {α s : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s)
    {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : IsC2HolderOn α C.graphFunction (ball C.center C.radius)) :
    let h : Space m → ℝ := lowerSphereCutoff s hs
    let e := (sphereFlatteningEquiv h).trans (chartParametrization C)
    let z : Space (m + 1) := point 0 s
    let t := e '' closedBall z s
    t ⊆ physicalChart C →
    (∀ y ∈ closedBall z s, ‖sphereFlattening h y‖ ≤ 3*s) →
    (∀ y ∈ closedBall z s, ContDiffAt ℝ 2 e y) →
    ∃ L I : ℝ≥0, ∃ D : ℝ, 0 < D ∧
      LipschitzOnWith L e (closedBall z s) ∧
      (∀ y ∈ closedBall z s, ‖fderiv ℝ e y‖ ≤ D) ∧
      LipschitzOnWith I e.symm t ∧
      (∀ x ∈ t, ContDiffAt ℝ 2 e.symm x) ∧
      (∀ i k, IsHolderOn α
        (fun x => (fderiv ℝ e.symm x (coordinate (m+1) i)) k) t) ∧
      ∀ i j k, IsHolderOn α
        (fun x => (fderiv ℝ (fderiv ℝ e.symm) x
          (coordinate (m+1) i) (coordinate (m+1) j)) k) t := by
  dsimp only
  let h : Space m → ℝ := lowerSphereCutoff s hs
  let e := (sphereFlatteningEquiv h).trans (chartParametrization C)
  let z : Space (m+1) := point 0 s
  let t := e '' closedBall z s
  intro htchart hnorm he
  have heOn : ContDiffOn ℝ 2 e (closedBall z s) :=
    fun y hy => (he y hy).contDiffWithinAt
  obtain ⟨L, heLip⟩ := heOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hDe : ContinuousOn (fderiv ℝ e) (closedBall z s) := by
    intro y hy
    exact ((he y hy).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall z s).exists_bound_of_continuousOn hDe
  let D := max M 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ y ∈ closedBall z s, ‖fderiv ℝ e y‖ ≤ D :=
    fun y hy => (hM y hy).trans (le_max_left _ _)
  let Φ := (chartParametrization C).symm
  let Ψ := sphereUnflattening h
  let q := closedBall (0 : Space (m+1)) (3*s)
  have hinv : (e.symm : Space (m+1) → Space (m+1)) = Ψ ∘ Φ := rfl
  have hΦbase (x : Space (m+1)) (hx : x ∈ t) :
      (C.frame.symm ((graphFrame m).symm x)).ofLp.1 ∈ ball C.center C.radius :=
    physicalChart_inverse_base C (htchart hx)
  have hΦreg : ∀ x ∈ t, ContDiffAt ℝ 2 Φ x :=
    fun x hx => chartParametrization_symm_contDiffAt C hγ.1 (hΦbase x hx)
  have hΦLip : LipschitzOnWith (shearConstant C.constant) Φ t :=
    (chartParametrization_symm_lipschitzOn C).mono hΦbase
  have hΦmap : MapsTo Φ t q := by
    rintro x ⟨y, hy, rfl⟩
    have heq : Φ (e y) = sphereFlattening h y := by
      change (chartParametrization C).symm
        ((chartParametrization C) ((sphereFlatteningEquiv h) y)) = _
      exact Equiv.symm_apply_apply _ _
    rw [heq]
    exact mem_closedBall.mpr (by simpa only [dist_zero_right] using hnorm y hy)
  have hh : ContDiff ℝ ∞ h := lowerSphereCutoff_contDiff hs
  have hΨsmooth : ContDiff ℝ ∞ Ψ := sphereUnflattening_contDiff hh
  obtain ⟨I₀, hΨLip⟩ := smooth_map_lipschitz_on_closedBall hΨsmooth
    (0 : Space (m+1)) (3*s)
  have hΨreg : ∀ y ∈ q, ContDiffAt ℝ 2 Ψ y :=
    fun y hy => (hΨsmooth.of_le (by simp)).contDiffAt
  obtain ⟨hΦJ, hΦH⟩ := chartParametrization_symm_holder_derivatives hα hα1 C hγ
  have hstrip : t ⊆ (inverseChartBaseMap C) ⁻¹' ball C.center C.radius :=
    fun x hx => hΦbase x hx
  have hΦJt := fun i k => isHolderOn_mono (hΦJ i k) hstrip
  have hΦHt := fun i j k => isHolderOn_mono (hΦH i j k) hstrip
  obtain ⟨hΨJ, hΨH⟩ := smooth_map_holder_derivatives_on_bounded hα hα1 hΨsmooth
    (isBounded_closedBall (x := (0 : Space (m+1))) (r := 3*s))
  obtain ⟨hJ, hH⟩ := P201.Elliptic.SchauderDirichlet.JetComposition.holder_derivatives_comp
    hα hΦreg hΨreg hΦLip hΦmap hΦJt hΦHt hΨJ hΨH
  have hiLip : LipschitzOnWith (I₀ * shearConstant C.constant) e.symm t := by
    rw [hinv]
    exact hΨLip.comp hΦLip hΦmap
  have hiReg : ∀ x ∈ t, ContDiffAt ℝ 2 e.symm x := by
    intro x hx
    rw [hinv]
    exact (hΨreg _ (hΦmap hx)).comp x (hΦreg x hx)
  refine ⟨L, I₀ * shearConstant C.constant, D, hD, heLip, hbound, hiLip, hiReg, ?_, ?_⟩
  · rw [hinv]
    exact hJ
  · rw [hinv]
    exact hH

end SphericalAnalytic

section GlobalBoundaryRegularity

open P201.Elliptic.PoissonSchauder
open P201.Elliptic.ChartSchauder
open P201Specs.Elliptic.HalfSpaceLift P201.Elliptic.HalfSpaceLift
open P102.Sobolev.Geometry P102.U4.GraphPieces

/-- Full original up-to-boundary regularity for an existing zero-trace
classical solution, using the independently established ball boundary and
initially-C² local regularity statements. All sphericalization maps and
actual inverse derivative bounds are constructed from the original chart. -/
theorem zero_global_boundary_regularity
    (hlocal : P201Specs.Elliptic.SchauderRegularity.LocalRegularityStatement)
    (hballBoundary : P201Specs.Elliptic.BallSchauderSolvability.LocalBoundaryRegularityStatement)
    {m : ℕ} {α ell : ℝ} (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    {Ω : Domain (m + 1)} (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hboundary : HasC2HolderBoundary α Ω)
    {a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {b : Space (m + 1) → Space (m + 1)} {c f u : Space (m + 1) → ℝ}
    (ha : UniformlyEllipticOn ell a (closure (Ω : Set (Space (m + 1)))))
    (hcoeff : CoefficientsHolderOn α a b c (closure (Ω : Set (Space (m + 1)))))
    (hc : ∀ x ∈ closure (Ω : Set (Space (m + 1))), c x ≤ 0)
    (hf : IsHolderOn α f (closure (Ω : Set (Space (m + 1)))))
    (hu : IsC2HolderLocOn α u Ω)
    (huc : ContinuousOn u (closure (Ω : Set (Space (m + 1)))))
    (hLu : ∀ x ∈ Ω, nondivergenceOperator a b c u x = f x)
    (hub : ∀ x ∈ frontier (Ω : Set (Space (m + 1))), u x = 0) :
    IsC2HolderUpToOn α u (closure (Ω : Set (Space (m + 1)))) := by
  apply c2HolderUpToOn_of_local_on_compact hα.le hb.isCompact_closure
  intro p hp
  by_cases hpΩ : p ∈ (Ω : Set (Space (m + 1)))
  · exact local_upToOn_at_interior hα.le hu hpΩ
  · have hpf : p ∈ frontier (Ω : Set (Space (m + 1))) := by
      rw [frontier, Ω.isOpen.interior_eq]
      exact ⟨hp, hpΩ⟩
    obtain ⟨C, hCp, hC⟩ := hboundary p hpf (mem_univ p)
    change chartPoint C = p at hCp
    obtain ⟨_, _, t, _, _, _, _, _, ht, _, hflat, _, _⟩ :=
      exists_chart_scales C hC.1 isOpen_univ (mem_univ (chartPoint C))
    let s : ℝ := t / 4
    have hs : 0 < s := by dsimp [s]; positivity
    have hsmall : 3 * s < 2 * t := by dsimp [s]; linarith
    let h : Space m → ℝ := lowerSphereCutoff s hs
    let e := sphericalChartEquiv C s hs
    let z : Space (m + 1) := point (0 : Space m) s
    let T : Set (Space (m + 1)) := e '' closedBall z s
    have hgeo := sphericalChart_maps_ball_and_closure C ht hs hsmall hflat
    have hgeoShared := sphericalChart_maps_spherical_patch C ht hs hsmall hflat
    have hgeoReg := sphericalChart_contDiffAt_two C hC.1 ht hs hsmall hflat
    have hgeoPhysical := sphericalChart_image_in_physicalChart C ht hs hsmall hflat
    have hTclosure : T ⊆ closure (Ω : Set (Space (m + 1))) := by
      rintro x ⟨y, hy, rfl⟩
      exact hgeo.1 hy
    have hTchart : T ⊆ physicalChart C := by
      rintro x ⟨y, hy, rfl⟩
      exact hgeoPhysical hy
    have hnorm : ∀ y ∈ closedBall z s, ‖sphereFlattening h y‖ ≤ 3 * s := by
      intro y hy
      rw [← sphericalChart_original_inverse C hs]
      exact sphericalChart_original_inverse_norm_le C hs hy
    have he : ∀ y ∈ closedBall z s, ContDiffAt ℝ 2 e y :=
      fun y hy => (hgeoReg y hy).1
    have hi : ∀ y ∈ closedBall z s, ContDiffAt ℝ 2 e.symm (e y) :=
      fun y hy => (hgeoReg y hy).2
    obtain ⟨L, I, D, hD, heLip, heD, hiLip, hiReg, hJac, hHess⟩ :=
      SphericalAnalytic.sphericalizing_map_analytic_data hα.le hα1.le hs C hC
        hTchart hnorm he
    have hmap : MapsTo e (closedBall z s) T := fun y hy => ⟨y, hy, rfl⟩
    have haT : UniformlyEllipticOn ell a T :=
      ⟨fun x hx => ha.1 x (hTclosure hx), fun x hx => ha.2 x (hTclosure hx)⟩
    have hcoeffT : CoefficientsHolderOn α a b c T :=
      ⟨fun i j => isHolderOn_mono (hcoeff.1 i j) hTclosure,
        fun i => isHolderOn_mono (hcoeff.2.1 i) hTclosure,
        isHolderOn_mono hcoeff.2.2 hTclosure⟩
    let U : Domain (m + 1) := ⟨ball 0 (s / 8), isOpen_ball⟩
    let V : Domain (m + 1) := ⟨ball 0 (s / 16), isOpen_ball⟩
    have hVU : closure (V : Set (Space (m + 1))) ⊆ (U : Set (Space (m + 1))) :=
      closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
    have hshared : ∀ y ∈ sphere z s, y ∈ (U : Set (Space (m + 1))) →
        e y ∈ frontier (Ω : Set (Space (m + 1))) :=
      fun y hy hyU => hgeoShared ⟨hy, hyU⟩
    have hreg := BoundaryTransport.zero_solution_spherical_pullback_regularity
      hlocal hballBoundary (by omega : 1 ≤ m + 1) hα hα1 hell hD Ω a b c f u e
      hTclosure z s hs haT hcoeffT (fun x hx => hc x (hTclosure hx))
      (isHolderOn_mono hf hTclosure) hu.1 huc hLu hub hmap hgeo.2 he hi heLip heD
      hJac hHess U hshared V isBounded_ball hVU
    obtain ⟨ρ, hρ, hcover⟩ := exists_sphericalChart_physical_inner_radius C hC.1 hs
    let P : Set (Space (m + 1)) := closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) ρ
    let S : Set (Space (m + 1)) := closedBall z s ∩ (V : Set (Space (m + 1)))
    have hPT : P ⊆ T := by
      intro x hx
      refine ⟨e.symm x, (hcover hx).1, ?_⟩
      exact e.apply_symm_apply x
    have hPunique : UniqueDiffOn ℝ P :=
      (LiftBridge.closure_uniqueDiffOn_of_boundary hboundary).inter isOpen_ball
    have hSunique : UniqueDiffOn ℝ S :=
      (uniqueDiffOn_closedBall_pos z hs).inter V.isOpen
    have hSconv : Convex ℝ S := (convex_closedBall z s).inter (convex_ball 0 (s / 16))
    have hregP : IsC2HolderUpToOn α u P :=
      BoundaryTransport.c2HolderUpToOn_pullback_inverse hα.le hα1.le e
        hSconv hPunique hSunique (fun x hx => hiReg x (hPT hx)) hcover
        (hiLip.mono hPT) (fun i k => isHolderOn_mono (hJac i k) hPT)
        (fun i j k => isHolderOn_mono (hHess i j k) hPT) hreg
    refine ⟨ρ, hρ, ?_⟩
    rw [← hCp]
    exact hregP



end GlobalBoundaryRegularity

set_option linter.unusedVariables false in
/-- Conditional derivation of the complete original solvability statement.
Every upstream premise retains its original full quantified type. -/
theorem solvability_conditional
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    (hholder : P201Specs.Elliptic.BallSchauderSolvability.HolderSolvabilityStatement)
    (hballBoundary : P201Specs.Elliptic.BallSchauderSolvability.LocalBoundaryRegularityStatement)
    (hinterior : P201Specs.Elliptic.SchauderRegularity.InteriorEstimateStatement)
    (hlocal : P201Specs.Elliptic.SchauderRegularity.LocalRegularityStatement)
    (hglobalEstimate : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    (hinteriorEstimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    (hboundaryEstimate : P201Specs.Elliptic.VariableSchauder.LocalBoundaryEstimateStatement) :
    P201Specs.Elliptic.SchauderDirichlet.SolvabilityStatement := by
  intro m α hα hα1 Ω hb hboundary ell K hell hK
  obtain ⟨C, hC, hest⟩ := global_estimate_without_c0 hglobalEstimate m α hα hα1 Ω hb
    hboundary ell K hell hK
  refine ⟨C, hC, ?_⟩
  intro a b c ha hcoeff hbound hc f G hf hG
  let F : Space (m + 1) → ℝ := P201.Elliptic.ChartSchauder.liftedWithinSource a b c G f (closure (Ω : Set (Space (m + 1))))
  have hF : IsHolderOn α F (closure (Ω : Set (Space (m + 1)))) :=
    LiftBridge.liftedWithinSource_holder_on_closure hα.le hα1.le hb hboundary hcoeff hf hG
  obtain ⟨w, hw, hwc, hLw, hwb, _⟩ := zero_dirichlet_classical_solution
    hcontinuous hinteriorEstimate hα hα1 hell hK hb hboundary ha hcoeff hbound hc hF
  have hwFull : IsC2HolderUpToOn α w (closure (Ω : Set (Space (m + 1)))) :=
    zero_global_boundary_regularity hlocal hballBoundary hα hα1 hell hb hboundary
      ha hcoeff hc hF hw hwc hLw hwb
  have hwSol : IsDirichletSolution α Ω a b c F (fun _ => 0) w := ⟨hwFull, hLw, hwb⟩
  have huSol : IsDirichletSolution α Ω a b c f G (w + G) :=
    LiftBridge.add_lift_isDirichletSolution hboundary hG hwSol
  refine ⟨w + G, huSol, hest a b c f G (w + G) ha hcoeff hbound hc hf hG huSol, ?_⟩
  intro v hv
  exact dirichlet_solution_unique (by omega) hα hell Ω hb ha hcoeff hc hv huSol

set_option linter.unusedVariables false in
theorem local_regularity_conditional
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    (hholder : P201Specs.Elliptic.BallSchauderSolvability.HolderSolvabilityStatement)
    (hboundary : P201Specs.Elliptic.BallSchauderSolvability.LocalBoundaryRegularityStatement)
    (hinterior : P201Specs.Elliptic.SchauderRegularity.InteriorEstimateStatement)
    (hlocal : P201Specs.Elliptic.SchauderRegularity.LocalRegularityStatement)
    (hglobalEstimate : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    (hinteriorEstimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    (hboundaryEstimate : P201Specs.Elliptic.VariableSchauder.LocalBoundaryEstimateStatement) :
    P201Specs.Elliptic.SchauderDirichlet.LocalRegularityStatement :=
  hlocal

set_option linter.unusedVariables false in
theorem interior_estimate_conditional
    (hcontinuous : P201Specs.Elliptic.BallSchauderSolvability.ContinuousSolvabilityStatement)
    (hholder : P201Specs.Elliptic.BallSchauderSolvability.HolderSolvabilityStatement)
    (hboundary : P201Specs.Elliptic.BallSchauderSolvability.LocalBoundaryRegularityStatement)
    (hinterior : P201Specs.Elliptic.SchauderRegularity.InteriorEstimateStatement)
    (hlocal : P201Specs.Elliptic.SchauderRegularity.LocalRegularityStatement)
    (hglobalEstimate : P201Specs.Elliptic.VariableSchauder.GlobalEstimateStatement)
    (hinteriorEstimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement)
    (hboundaryEstimate : P201Specs.Elliptic.VariableSchauder.LocalBoundaryEstimateStatement) :
    P201Specs.Elliptic.SchauderDirichlet.InteriorEstimateStatement :=
  hinterior

end P201.Elliptic.SchauderDirichlet

theorem _root_.«P201».«Elliptic».«SchauderDirichlet».«interior_estimate» : _root_.«P201Specs».«Elliptic».«SchauderDirichlet».«InteriorEstimateStatement» :=
  @_root_.«P201».«Elliptic».«SchauderDirichlet».«interior_estimate_conditional» (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«continuous_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«holder_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«local_boundary_regularity») (@_root_.«P201».«Elliptic».«SchauderRegularity».«interior_estimate») (@_root_.«P201».«Elliptic».«SchauderRegularity».«local_regularity») (@_root_.«P201».«Elliptic».«VariableSchauder».«global_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«interior_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«local_boundary_estimate»)
theorem _root_.«P201».«Elliptic».«SchauderDirichlet».«local_regularity» : _root_.«P201Specs».«Elliptic».«SchauderDirichlet».«LocalRegularityStatement» :=
  @_root_.«P201».«Elliptic».«SchauderDirichlet».«local_regularity_conditional» (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«continuous_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«holder_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«local_boundary_regularity») (@_root_.«P201».«Elliptic».«SchauderRegularity».«interior_estimate») (@_root_.«P201».«Elliptic».«SchauderRegularity».«local_regularity») (@_root_.«P201».«Elliptic».«VariableSchauder».«global_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«interior_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«local_boundary_estimate»)
theorem _root_.«P201».«Elliptic».«SchauderDirichlet».«solvability» : _root_.«P201Specs».«Elliptic».«SchauderDirichlet».«SolvabilityStatement» :=
  @_root_.«P201».«Elliptic».«SchauderDirichlet».«solvability_conditional» (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«continuous_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«holder_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«local_boundary_regularity») (@_root_.«P201».«Elliptic».«SchauderRegularity».«interior_estimate») (@_root_.«P201».«Elliptic».«SchauderRegularity».«local_regularity») (@_root_.«P201».«Elliptic».«VariableSchauder».«global_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«interior_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«local_boundary_estimate»)
