import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.LinearizedInstability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.StateDerivative
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.CompactEscape
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.MatrixLyapunov
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

/-! A direct proof of the unstable assertion of paper.tex
d13:12:linearized-stability. Conjugation-invariant generalized spectral sums
give a real invariant splitting. Shifted Lyapunov equations then give a
quadratic cone, and a local Chetaev argument gives escape at an actual time
in the canonical maximal interval.
-/
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch12.LinearizedInstability
open Specs.D13Unified.Ch12.LinearizedInstability
open Specs.D13Unified.Ch12.StabilityDefinitions
open Specs.D13Unified.Ch01.AutonomousParameters
open D13Unified.Ch06.StateDerivative
universe u v

/-- A bounded differentiable function on the half-line cannot start positive
and have derivative at least a positive multiple of itself wherever positive.
First fence it above zero; a linear lower bound then contradicts boundedness.
-/
lemma not_bounded_of_positive_derivative
    (v d : ℝ → ℝ) (c M : ℝ) (hc : 0 < c) (hv0 : 0 < v 0)
    (hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt v (d t) t)
    (hgrow : ∀ t : ℝ, 0 ≤ t → 0 < v t → c * v t ≤ d t)
    (hbound : ∀ t : ℝ, 0 ≤ t → v t ≤ M) : False := by
  have hhalf (t : ℝ) (ht : 0 ≤ t) : v 0 / 2 ≤ v t := by
    have hf : ContinuousOn (fun s => -v s) (Icc 0 t) :=
      fun s hs => (hd s hs.1).continuousAt.neg.continuousWithinAt
    have hf' : ∀ s ∈ Ico 0 t,
        HasDerivWithinAt (fun s => -v s) (-d s) (Ici s) s :=
      fun s hs => (hd s hs.1).neg.hasDerivWithinAt
    have h := image_le_of_deriv_right_lt_deriv_boundary hf hf'
      (B := fun _ => -(v 0 / 2)) (B' := fun _ => 0)
      (by linarith) (fun _ => hasDerivAt_const _ _) (by
        intro s hs he
        have he' : v s = v 0 / 2 := by linarith
        have hp : 0 < v s := by rw [he']; linarith
        have hh := hgrow s hs.1 hp
        have := mul_pos hc hp
        linarith)
      (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
    linarith
  let a : ℝ := c * (v 0 / 2)
  have ha : 0 < a := mul_pos hc (by linarith)
  have hlinear (t : ℝ) (ht : 0 ≤ t) : v 0 + a * t ≤ v t := by
    have hf : ContinuousOn (fun s => v 0 + a * s) (Icc 0 t) := by fun_prop
    have hf' : ∀ s ∈ Ico 0 t,
        HasDerivWithinAt (fun s => v 0 + a * s) a (Ici s) s := by
      intro s _
      simpa using ((hasDerivAt_id s).const_mul a |>.const_add (v 0)).hasDerivWithinAt
    have h := image_le_of_deriv_right_le_deriv_boundary hf hf'
      (B := v) (B' := d) (by simp)
      (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hd s hs.1).hasDerivWithinAt) (by
        intro s hs
        have hh := hhalf s hs.1
        have hp : 0 < v s := by linarith
        exact (mul_le_mul_of_nonneg_left hh hc.le).trans (hgrow s hs.1 hp))
      (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
    exact h
  let t : ℝ := max 0 ((M - v 0 + 1) / a)
  have ht : 0 ≤ t := le_max_left _ _
  have hat : M - v 0 + 1 ≤ a * t := by
    have hh := le_max_right (0 : ℝ) ((M - v 0 + 1) / a)
    simpa only [t, mul_comm] using (div_le_iff₀ ha).mp hh
  have := hlinear t ht
  have := hbound t ht
  linarith

theorem escape_implies_unstable : EscapeImpliesUnstable.{u} := by
  intro E _ _ _ F hF h0 heq hescape hstable
  obtain ⟨ε, hε, hescape⟩ := hescape
  obtain ⟨δ, hδ, hstable⟩ := hstable ε hε
  obtain ⟨x, hx, hxδ, t, ht, _, hnorm⟩ := hescape δ hδ
  exact (not_lt_of_ge hnorm) ((hstable x hx hxδ).2 t ht)

theorem chetaev_unstable : ChetaevCriterion.{u} := by
  intro E _ _ _ F hF h0 heq V r c M hr hc hV hbound hgrow hpositive hstable
  obtain ⟨δ, hδ, hstable⟩ := hstable r hr
  obtain ⟨x, hx, hxδ, hxV⟩ := hpositive δ hδ
  obtain ⟨hcomplete, hsmall⟩ := hstable x hx hxδ
  have hivp := flow_ivp F hF hx
  let v : ℝ → ℝ := fun t => V (flow F t x)
  let d : ℝ → ℝ := fun t => (fderiv ℝ V (flow F t x))
    (autonomousEvalValue F (flow F t x))
  apply not_bounded_of_positive_derivative v d c M hc
  · simpa only [v, hivp.2.2] using hxV
  · intro t ht
    have htI := (hcomplete t ht).2
    have hdiff := (hV _ (hsmall t ht)).hasFDerivAt
    have htime := hivp.1.2.2 t htI
    simpa only [v, d, flow, Function.comp_def, AutonomousODE.toODE_eval,
      AutonomousODE.eval] using
      hdiff.comp_hasDerivAt t htime
  · intro t ht hp
    exact hgrow _ (hivp.1.2.1 t (hcomplete t ht).2) (hsmall t ht) hp
  · intro t ht
    exact hbound _ (hsmall t ht)

/-- A forward orbit confined in a compact subset of the original state
domain has no finite right endpoint. Uses the canonical maximal solution. -/
lemma confined_forward_complete
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {x : E} (hx : x ∈ F.domain) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ F.domain)
    (hconf : ∀ t : ℝ, 0 ≤ t → t ∈ (flowInterval F x).carrier → flow F t x ∈ K) :
    forwardCompleteValue F hF x := by
  classical
  let L := F.locallyLipschitzInState_of_contDiffOn hF
  obtain ⟨hsol, hzero, hx0, hmax, hend, hcover, huniq⟩ :=
    ODE.canonical_solution F.toODE L 0 x hx
  let bE := Specs.D13Unified.Ch04.MaximalSolutionMap.upperEndpointValue F.toODE 0 x
  have hI : (flowInterval F x).carrier = {t : ℝ |
      Specs.D13Unified.Ch04.MaximalSolutionMap.lowerEndpointValue F.toODE 0 x <
        (t : EReal) ∧ (t : EReal) < bE} := hend.2.2
  have hbtop : bE = ⊤ := by
    by_contra htop
    have hbot : bE ≠ ⊥ := by
      intro hh
      have hh' := hend.2.1
      change (0 : EReal) < bE at hh'
      rw [hh] at hh'
      exact not_lt_bot hh'
    let b := bE.toReal
    have hb : bE = (b : EReal) := (EReal.coe_toReal htop hbot).symm
    have hbpos : 0 < b := by
      have hh := hend.2.1
      change (0 : EReal) < bE at hh
      rw [hb] at hh
      exact_mod_cast hh
    obtain ⟨τ, hτ, hesc⟩ := Ch04.CompactEscape.right_escape F.toODE L 0 x hx b hb
      (Icc 0 b ×ˢ K) (isCompact_Icc.prod hK) (fun q hq => hKU hq.2)
    let t := (max 0 τ + b) / 2
    have hm : max 0 τ < b := max_lt hbpos hτ
    have ht0 : 0 ≤ t := by have := le_max_left (0 : ℝ) τ; dsimp [t]; linarith
    have htt : τ < t := by have := le_max_right (0 : ℝ) τ; dsimp [t]; linarith
    have htb : t < b := by dsimp [t]; linarith
    have htI : t ∈ (flowInterval F x).carrier := by
      rw [hI]
      refine ⟨hend.1.trans_le (by exact_mod_cast ht0), ?_⟩
      simpa only [hb, EReal.coe_lt_coe_iff] using htb
    have hv := (ODE.solutionValue_on_domain F.toODE L t 0 x ⟨hx, htI⟩).1
    apply hesc t ⟨htt, htb⟩
    refine ⟨⟨ht0, htb.le⟩, ?_⟩
    rw [hv]
    exact hconf t ht0 htI
  intro t ht
  refine ⟨hx, ?_⟩
  rw [hI]
  refine ⟨hend.1.trans_le (by exact_mod_cast ht), ?_⟩
  change (t : EReal) < bE
  simp [hbtop]

theorem unstable_iff_escape : UnstableIffEscape.{u} := by
  intro E _ _ _ F hF h0 heq
  classical
  refine ⟨?_, fun h => escape_implies_unstable F hF h0 heq h⟩
  intro hunstable
  by_contra hescape
  apply hunstable
  intro ε hε
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp F.isOpen_domain 0 h0
  let η := min ε (r / 2)
  have hη : 0 < η := lt_min hε (by linarith)
  have hn : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F.domain, ‖x‖ < δ →
      ∀ t : ℝ, 0 ≤ t → t ∈ (flowInterval F x).carrier → ‖flow F t x‖ < η := by
    by_contra hh
    apply hescape
    refine ⟨η, hη, ?_⟩
    intro δ hδ
    push Not at hh
    obtain ⟨x, hx, hxδ, t, ht, htI, hnorm⟩ := hh δ hδ
    exact ⟨x, hx, hxδ, t, ht, htI, hnorm⟩
  obtain ⟨δ, hδ, hn⟩ := hn
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxδ
  have hc : forwardCompleteValue F hF x :=
    confined_forward_complete F hF hx (Metric.closedBall 0 η)
      (isCompact_closedBall 0 η) (by
        intro y hy
        apply hrU
        have hy' : ‖y‖ ≤ η := by simpa using hy
        have hh := min_le_right ε (r / 2)
        change dist y 0 < r
        rw [dist_zero_right]
        dsimp [η] at hy'
        linarith)
      (fun t ht htI => by simpa using (hn x hx hxδ t ht htI).le)
  refine ⟨hc, ?_⟩
  intro t ht
  exact (hn x hx hxδ t ht (hc t ht).2).trans_le (min_le_left _ _)

/-- Differentiability at the equilibrium supplies a uniform small remainder
on a ball. The ambient representative is used only inside the given domain. -/
lemma local_remainder_bound
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : F.eval 0 = 0)
    {a : ℝ} (ha : 0 < a) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ‖F.eval x - (fderiv ℝ F.eval 0) x‖ ≤ a * ‖x‖ := by
  have hd : HasFDerivAt F.eval (fderiv ℝ F.eval 0) 0 :=
    (hF.differentiableOn (by norm_num)).differentiableAt
      (F.isOpen_domain.mem_nhds h0) |>.hasFDerivAt
  have hh := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd).bound ha
  simp only [zero_add, heq, sub_zero] at hh
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hh
  exact ⟨r, hr, fun x hx => hball x (by simpa using hx)⟩

/-- The small-o nonlinear remainder preserves the strict growth of a linear
quadratic cone. All constants and the neighborhood are chosen before the
arbitrarily small initial point; no invariant-manifold theorem is used. -/
theorem certificate_implies_escape : CertificateImpliesEscape.{u} := by
  intro E _ _ _ F hF h0 heq hcert
  obtain ⟨V, C, c, hC, hc, hV, hVbound, hDVbound, hgrow, hpositive⟩ := hcert
  let a : ℝ := c / (2 * C)
  have ha : 0 < a := div_pos hc (mul_pos (by norm_num) hC)
  have hac : C * a = c / 2 := by dsimp [a]; field_simp
  obtain ⟨r₁, hr₁, hrem⟩ := local_remainder_bound F hF h0 heq ha
  obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.mp F.isOpen_domain 0 h0
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hsmallU (x : E) (hx : ‖x‖ < r) : x ∈ F.domain :=
    hball (by simpa using hx.trans_le (min_le_right r₁ r₂))
  have hinst : unstableValue F hF h0 heq := by
    apply chetaev_unstable F hF h0 heq V r a (C * r ^ 2) hr ha
    · intro x _
      exact hV x
    · intro x hx
      have hn : ‖x‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg x]
      exact (le_abs_self (V x)).trans
        ((hVbound x).trans (mul_le_mul_of_nonneg_left hn hC.le))
    · intro x _ hx hp
      let A := fderiv ℝ F.eval 0
      have hb : ‖F.eval x - A x‖ ≤ a * ‖x‖ := hrem x (hx.trans_le (min_le_left _ _))
      have herr : |(fderiv ℝ V x) (F.eval x - A x)| ≤ (c / 2) * ‖x‖ ^ 2 := by
        have hh := (fderiv ℝ V x).le_opNorm (F.eval x - A x)
        rw [Real.norm_eq_abs] at hh
        calc
          _ ≤ ‖fderiv ℝ V x‖ * ‖F.eval x - A x‖ := hh
          _ ≤ (C * ‖x‖) * (a * ‖x‖) :=
            mul_le_mul (hDVbound x) hb (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))
          _ = (c / 2) * ‖x‖ ^ 2 := by rw [← hac]; ring
      have hlin := hgrow x hp
      have hid : (fderiv ℝ V x) (F.eval x - A x) =
          (fderiv ℝ V x) (F.eval x) - (fderiv ℝ V x) (A x) := map_sub _ _ _
      have hlo := neg_le_of_abs_le herr
      have hv := (le_abs_self (V x)).trans (hVbound x)
      have hav : a * V x ≤ (c / 2) * ‖x‖ ^ 2 := by
        calc
          _ ≤ a * (C * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hv ha.le
          _ = (c / 2) * ‖x‖ ^ 2 := by rw [← hac]; ring
      change a * V x ≤ (fderiv ℝ V x) (F.eval x)
      change c * ‖x‖ ^ 2 ≤ (fderiv ℝ V x) (A x) at hlin
      rw [hid] at hlo
      linarith
    · intro δ hδ
      obtain ⟨x, hx, hp⟩ := hpositive (min δ r) (lt_min hδ hr)
      exact ⟨x, hsmallU x (hx.trans_le (min_le_right _ _)),
        hx.trans_le (min_le_left _ _), hp⟩
  exact ⟨(unstable_iff_escape F hF h0 heq).mp hinst, hinst⟩

/-- The derivative of the diagonal of a continuous bilinear form. Symmetry
is not needed for this identity or the uniform quadratic bounds below. -/
lemma bilinear_diagonal_fderiv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (x y : E) :
    (fderiv ℝ (fun z => B z z) x) y = B x y + B y x := by
  exact congrArg (fun L : E →L[ℝ] ℝ => L y)
    (B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)).fderiv

/-- A single positive direction of a homogeneous quadratic form gives positive
values arbitrarily close to zero. The growth premise is still a pure linear
inequality, and will be supplied by the shifted Lyapunov equations. -/
lemma bilinear_growth_certificate
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hgrow : ∀ x, 0 < B x x → c * ‖x‖ ^ 2 ≤ B x (A x) + B (A x) x)
    (hpositive : ∃ y, 0 < B y y) : LinearGrowthCertificate A := by
  let C : ℝ := 2 * ‖B‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : ‖B‖ ≤ C := by dsimp [C]; nlinarith [norm_nonneg B]
  refine ⟨(fun x => B x x), C, c, hC, hc, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)).differentiableAt
  · intro x
    calc
      |B x x| ≤ ‖B‖ * ‖x‖ * ‖x‖ := by simpa using B.le_opNorm₂ x x
      _ ≤ C * ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  · intro x
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC.le (norm_nonneg x))
    intro y
    rw [bilinear_diagonal_fderiv]
    calc
      ‖B x y + B y x‖ ≤ ‖B x y‖ + ‖B y x‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖x‖ * ‖y‖ + ‖B‖ * ‖y‖ * ‖x‖ :=
        add_le_add (B.le_opNorm₂ x y) (B.le_opNorm₂ y x)
      _ ≤ (C * ‖x‖) * ‖y‖ := by
        dsimp [C]
        nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  · intro x hx
    rw [bilinear_diagonal_fderiv]
    exact hgrow x hx
  · intro δ hδ
    obtain ⟨y, hy⟩ := hpositive
    let r : ℝ := δ / (2 * (‖y‖ + 1))
    have hr : 0 < r := div_pos hδ (by positivity)
    have heq : r * (2 * (‖y‖ + 1)) = δ := div_mul_cancel₀ _ (by positivity)
    refine ⟨r • y, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith [norm_nonneg y]
    · simp only [map_smul, smul_apply, smul_eq_mul]
      exact mul_pos hr (mul_pos hr hy)

/-- The ordinary supremum norm of a finite real vector is bounded by its
Euclidean square sum. This includes the empty coordinate space. -/
lemma pi_norm_sq_le_dotProduct {n : Type*} [Fintype n] (x : n → ℝ) :
    ‖x‖ ^ 2 ≤ x ⬝ᵥ x := by
  classical
  have hq : 0 ≤ x ⬝ᵥ x := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  have hn : ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    simpa only [dotProduct, pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
  nlinarith [Real.sq_sqrt hq, norm_nonneg x, Real.sqrt_nonneg (x ⬝ᵥ x)]

/-- Evaluation of a shifted Lyapunov equation along the original linear
vector field, with its full square-norm term retained. -/
lemma shifted_quadratic_identity
    {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix n n ℝ) (a : ℝ) (hP : P.transpose = P)
    (heq : (A - a • 1).transpose * P + P * (A - a • 1) = -1)
    (x : n → ℝ) :
    2 * (x ⬝ᵥ P.mulVec (A.mulVec x)) =
      2 * a * (x ⬝ᵥ P.mulVec x) - x ⬝ᵥ x := by
  have h := quadratic_lyapunovOperator (A - a • 1) P hP x
  rw [heq] at h
  simp only [Matrix.neg_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, dotProduct_neg, dotProduct_sub, Matrix.mulVec_sub,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at h
  linarith

/-- A real invariant block decomposition with a gap produces the full linear
quadratic-growth certificate. The second block may have dimension zero. The
existence of this decomposition from the spectrum is a separate obligation. -/
lemma block_growth_certificate
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype k] [DecidableEq k]
    (A : E →L[ℝ] E) (T : E ≃L[ℝ] ((n → ℝ) × (k → ℝ)))
    (Au : Matrix n n ℝ) (Ac : Matrix k k ℝ) (α η : ℝ)
    (hη : 0 < η) (hgap : η < α)
    (hAu : IsHurwitz (-Au + α • 1)) (hAc : IsHurwitz (Ac - η • 1))
    (hTu : ∀ x, (T (A x)).1 = Au.mulVec (T x).1)
    (hTc : ∀ x, (T (A x)).2 = Ac.mulVec (T x).2) :
    LinearGrowthCertificate A := by
  classical
  obtain ⟨Pu, hPu, heu⟩ := (matrix_lyapunov_iff (-Au + α • 1)).mp hAu
    1 Matrix.PosDef.one
  obtain ⟨Pc, hPc, hec⟩ := (matrix_lyapunov_iff (Ac - η • 1)).mp hAc
    1 Matrix.PosDef.one
  have hPus : Pu.transpose = Pu := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hPu.isHermitian
  have hPcs : Pc.transpose = Pc := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hPc.isHermitian
  let U : E →L[ℝ] (n → ℝ) :=
    (ContinuousLinearMap.fst ℝ (n → ℝ) (k → ℝ)).comp T.toContinuousLinearMap
  let W : E →L[ℝ] (k → ℝ) :=
    (ContinuousLinearMap.snd ℝ (n → ℝ) (k → ℝ)).comp T.toContinuousLinearMap
  let Bu := (Matrix.toBilin' Pu).toContinuousBilinearMap
  let Bc := (Matrix.toBilin' Pc).toContinuousBilinearMap
  let B : E →L[ℝ] E →L[ℝ] ℝ := Bu.bilinearComp U U - Bc.bilinearComp W W
  have hB (x y : E) : B x y =
      U x ⬝ᵥ Pu.mulVec (U y) - W x ⬝ᵥ Pc.mulVec (W y) := by
    change Matrix.toBilin' Pu (U x) (U y) - Matrix.toBilin' Pc (W x) (W y) = _
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  have huA (x : E) : U (A x) = Au.mulVec (U x) := hTu x
  have hwA (x : E) : W (A x) = Ac.mulVec (W x) := hTc x
  have hdu (u : n → ℝ) : 2 * (u ⬝ᵥ Pu.mulVec (Au.mulVec u)) =
      2 * α * (u ⬝ᵥ Pu.mulVec u) + u ⬝ᵥ u := by
    have h := shifted_quadratic_identity (-Au) Pu (-α) hPus (by simpa using heu) u
    simp only [Matrix.neg_mulVec, dotProduct_neg, Matrix.mulVec_neg] at h
    linarith
  have hdc (w : k → ℝ) := shifted_quadratic_identity Ac Pc η hPcs hec w
  let K : ℝ := ‖T.symm.toContinuousLinearMap‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hnorm (x : E) : ‖x‖ ^ 2 ≤ K ^ 2 *
      (U x ⬝ᵥ U x + W x ⬝ᵥ W x) := by
    have hi : ‖x‖ ≤ K * ‖T x‖ := by
      calc
        ‖x‖ = ‖T.symm (T x)‖ := by rw [T.symm_apply_apply]
        _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T x‖ :=
          T.symm.toContinuousLinearMap.le_opNorm (T x)
        _ ≤ K * ‖T x‖ := by dsimp [K]; nlinarith [norm_nonneg (T x)]
    have hu := pi_norm_sq_le_dotProduct (U x)
    have hw := pi_norm_sq_le_dotProduct (W x)
    have hprod : ‖T x‖ ^ 2 ≤ U x ⬝ᵥ U x + W x ⬝ᵥ W x := by
      change max ‖U x‖ ‖W x‖ ^ 2 ≤ _
      rcases le_total ‖U x‖ ‖W x‖ with h | h
      · rw [max_eq_right h]
        nlinarith [sq_nonneg ‖U x‖]
      · rw [max_eq_left h]
        nlinarith [sq_nonneg ‖W x‖]
    nlinarith [mul_le_mul_of_nonneg_left hprod (sq_nonneg K),
      sq_nonneg (K * ‖T x‖ - ‖x‖), norm_nonneg x, norm_nonneg (T x)]
  apply bilinear_growth_certificate A B (1 / K ^ 2) (by positivity)
  · intro x hx
    have hu : 0 ≤ U x ⬝ᵥ Pu.mulVec (U x) := by
      simpa only [star_trivial] using hPu.posSemidef.dotProduct_mulVec_nonneg (U x)
    have hd1 := hdu (U x)
    have hd2 := hdc (W x)
    have he : B x (A x) + B (A x) x =
        2 * η * B x x + 2 * (α - η) * (U x ⬝ᵥ Pu.mulVec (U x)) +
          (U x ⬝ᵥ U x + W x ⬝ᵥ W x) := by
      simp only [hB, huA, hwA]
      rw [symmetric_dotProduct Pu hPus (Au.mulVec (U x)) (U x),
        symmetric_dotProduct Pc hPcs (Ac.mulVec (W x)) (W x)]
      linarith
    have hg : 0 ≤ 2 * (α - η) * (U x ⬝ᵥ Pu.mulVec (U x)) := by positivity
    have hp : 0 ≤ 2 * η * B x x := by positivity
    rw [he]
    have hnx := (div_le_iff₀ (sq_pos_of_pos hK)).mpr
      (show ‖x‖ ^ 2 ≤ (U x ⬝ᵥ U x + W x ⬝ᵥ W x) * K ^ 2 from
        (hnorm x).trans_eq (mul_comm _ _))
    have hnx' : (1 / K ^ 2) * ‖x‖ ^ 2 ≤ U x ⬝ᵥ U x + W x ⬝ᵥ W x := by
      simpa only [one_div, div_eq_inv_mul, mul_one] using hnx
    linarith
  · let i : n := Classical.choice inferInstance
    let u : n → ℝ := Pi.single i 1
    have hu : u ≠ 0 := by
      intro h
      have hi := congrFun h i
      simp [u] at hi
    refine ⟨T.symm (u, 0), ?_⟩
    rw [hB]
    have hU : U (T.symm (u, 0)) = u := by
      change (T (T.symm (u, 0))).1 = u
      simp
    have hW : W (T.symm (u, 0)) = 0 := by
      change (T (T.symm (u, 0))).2 = 0
      simp
    simpa only [hU, hW, Matrix.mulVec_zero, dotProduct_zero, sub_zero, star_trivial]
      using hPu.dotProduct_mulVec_pos hu

/-- Generalized eigenspaces whose eigenvalues lie in a selected set. -/
def spectralSubspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (S : Set ℂ) : Submodule ℂ V :=
  ⨆ μ ∈ S, f.maxGenEigenspace μ

lemma spectralSubspace_invariant {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (S : Set ℂ) :
    ∀ x ∈ spectralSubspace f S, f x ∈ spectralSubspace f S := by
  change spectralSubspace f S ≤ (spectralSubspace f S).comap f
  rw [← Submodule.map_le_iff_le_comap]
  simp only [spectralSubspace, Submodule.map_iSup]
  refine iSup₂_le fun μ hμ => ?_
  rintro y ⟨x, hx, rfl⟩
  exact (le_biSup f.maxGenEigenspace hμ)
    (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hx)

/-- A partition of the complex spectrum gives complementary invariant sums.
Only algebraic closedness and finite dimension are used here. -/
lemma spectralSubspace_isCompl {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (S : Set ℂ) :
    IsCompl (spectralSubspace f S) (spectralSubspace f Sᶜ) := by
  refine ⟨f.independent_maxGenEigenspace.disjoint_biSup_biSup disjoint_compl_right, ?_⟩
  rw [codisjoint_iff, ← Module.End.iSup_maxGenEigenspace_eq_top f]
  apply le_antisymm (sup_le (iSup₂_le fun _ _ => le_iSup _ _) (iSup₂_le fun _ _ => le_iSup _ _))
  apply iSup_le
  intro μ
  by_cases hμ : μ ∈ S
  · exact (le_biSup f.maxGenEigenspace hμ).trans le_sup_left
  · exact (le_biSup f.maxGenEigenspace hμ).trans le_sup_right

lemma eigenvalue_mem_of_mem_spectralSubspace
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (S : Set ℂ) {μ : ℂ} {x : V}
    (hx : f.HasEigenvector μ x) (hS : x ∈ spectralSubspace f S) : μ ∈ S := by
  by_contra hμ
  have hd := f.independent_maxGenEigenspace.disjoint_biSup hμ
  have hmax : x ∈ f.maxGenEigenspace μ := Module.End.eigenspace_le_maxGenEigenspace hx.1
  exact hx.2 ((Submodule.disjoint_def.mp hd) x hmax hS)

/-- Coordinate conjugation as a semilinear map. -/
def conjugateVector {n : Type*} : (n → ℂ) →ₛₗ[starRingEnd ℂ] (n → ℂ) where
  toFun x i := star (x i)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp [smul_eq_mul]

lemma conjugate_mem_maxGenEigenspace
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (μ : ℂ) {x : n → ℂ}
    (hx : x ∈ Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) μ) :
    conjugateVector x ∈
      Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) (star μ) := by
  let f : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' (A.map Complex.ofReal)
  have hs : Function.Semiconj (conjugateVector (n := n)) ⇑(f - μ • 1) ⇑(f - star μ • 1) := by
    intro z
    ext i
    simp [f, conjugateVector, Matrix.mulVec, dotProduct, smul_eq_mul]
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
  refine ⟨m, ?_⟩
  simp only [Module.End.pow_apply] at hm ⊢
  rw [← hs.iterate_right, hm, map_zero]

lemma conjugate_mem_spectralSubspace
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (S : Set ℂ) (hS : ∀ μ ∈ S, star μ ∈ S) {x : n → ℂ}
    (hx : x ∈ spectralSubspace (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) S) :
    conjugateVector x ∈ spectralSubspace (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) S := by
  suffices (spectralSubspace (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) S).map
      conjugateVector ≤ spectralSubspace (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) S from
    this (Submodule.mem_map_of_mem hx)
  simp only [spectralSubspace, Submodule.map_iSup]
  refine iSup₂_le fun μ hμ => ?_
  rintro y ⟨z, hz, rfl⟩
  exact (le_biSup (Module.End.maxGenEigenspace
      (Matrix.toLinAlgEquiv' (A.map Complex.ofReal))) (hS μ hμ))
    (conjugate_mem_maxGenEigenspace A μ hz)

/-- The real coordinate subspace of a complex subspace. -/
def realVector {n : Type*} : (n → ℝ) →ₗ[ℝ] (n → ℂ) where
  toFun x i := (x i : ℂ)
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp [smul_eq_mul]

def realSubspace {n : Type*} (P : Submodule ℂ (n → ℂ)) : Submodule ℝ (n → ℝ) :=
  (P.restrictScalars ℝ).comap realVector

lemma real_imag_mem_of_conjugate_invariant
    {n : Type*} (P : Submodule ℂ (n → ℂ))
    (hP : ∀ x ∈ P, conjugateVector x ∈ P) {z : n → ℂ} (hz : z ∈ P) :
    (fun i => (z i).re) ∈ realSubspace P ∧
      (fun i => (z i).im) ∈ realSubspace P := by
  have hc := hP z hz
  have hr : realVector (fun i => (z i).re) = (1 / 2 : ℂ) • (z + conjugateVector z) := by
    ext i
    apply Complex.ext <;> simp [realVector, conjugateVector, smul_eq_mul, Complex.mul_re,
      Complex.mul_im] <;> ring
  have hi : realVector (fun i => (z i).im) =
      ((-((1 / 2 : ℝ) : ℂ)) * Complex.I) • (z - conjugateVector z) := by
    ext i
    apply Complex.ext <;> simp [realVector, conjugateVector, smul_eq_mul, Complex.mul_re,
      Complex.mul_im] <;> ring
  constructor
  · change realVector _ ∈ P
    rw [hr]
    exact P.smul_mem _ (P.add_mem hz hc)
  · change realVector _ ∈ P
    rw [hi]
    exact P.smul_mem _ (P.sub_mem hz hc)

/-- Conjugation-invariant complex complementary spaces descend to real
complementary spaces. Taking real parts of a complex decomposition suffices;
there is no assumption that the second space is nonzero. -/
lemma realSubspace_isCompl
    {n : Type*} (P Q : Submodule ℂ (n → ℂ)) (hPQ : IsCompl P Q)
    (hP : ∀ x ∈ P, conjugateVector x ∈ P)
    (hQ : ∀ x ∈ Q, conjugateVector x ∈ Q) :
    IsCompl (realSubspace P) (realSubspace Q) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hy
    have he : realVector x = 0 := Submodule.disjoint_def.mp hPQ.disjoint _ hx hy
    ext i
    have hi := congrArg (fun z : n → ℂ => (z i).re) he
    simpa [realVector] using hi
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    obtain ⟨u, v, huv, _⟩ := Submodule.existsUnique_add_of_isCompl hPQ (realVector x)
    have hu := (real_imag_mem_of_conjugate_invariant P hP u.property).1
    have hv := (real_imag_mem_of_conjugate_invariant Q hQ v.property).1
    have hsum : (fun i => (u.val i).re) + (fun i => (v.val i).re) = x := by
      ext i
      have he := congrArg (fun z : n → ℂ => (z i).re) huv
      simpa [realVector] using he
    rw [← hsum]
    exact Submodule.add_mem_sup hu hv

lemma realSubspace_invariant
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (S : Set ℂ) :
    ∀ x ∈ realSubspace (spectralSubspace (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) S),
      A.mulVec x ∈ realSubspace
        (spectralSubspace (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) S) := by
  intro x hx
  change realVector (A.mulVec x) ∈
    spectralSubspace (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) S
  have he : realVector (A.mulVec x) = (A.map Complex.ofReal).mulVec (realVector x) := by
    ext i
    exact Complex.ofRealHom.map_mulVec A x i
  rw [he]
  exact spectralSubspace_invariant (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) S _ hx

/-- A complex eigenvector of a real restriction lifts to a nonzero complex
eigenvector of the original matrix inside the original complex subspace. -/
lemma lift_restriction_eigenvector
    {n j : Type*} [Fintype n] [DecidableEq n] [Fintype j] [DecidableEq j]
    (A : Matrix n n ℝ) (P : Submodule ℂ (n → ℂ))
    (hinv : ∀ x ∈ realSubspace P, A.mulVec x ∈ realSubspace P)
    (b : Module.Basis j ℝ (realSubspace P)) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (Matrix.toLinAlgEquiv'
      ((LinearMap.toMatrix b b ((Matrix.toLinAlgEquiv' A).restrict hinv)).map
        Complex.ofReal)) μ) :
    ∃ z : n → ℂ,
      Module.End.HasEigenvector (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) μ z ∧ z ∈ P := by
  let g := (Matrix.toLinAlgEquiv' A).restrict hinv
  let M := LinearMap.toMatrix b b g
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have he : (M.map Complex.ofReal).mulVec v = μ • v := hv.apply_eq_smul
  let vr : j → ℝ := fun i => (v i).re
  let vi : j → ℝ := fun i => (v i).im
  have hre : M.mulVec vr = μ.re • vr - μ.im • vi := by
    ext i
    have hi := congrArg (fun z : j → ℂ => (z i).re) he
    simpa [Matrix.mulVec, dotProduct, Complex.mul_re, vr, vi, smul_eq_mul] using hi
  have him : M.mulVec vi = μ.im • vr + μ.re • vi := by
    ext i
    have hi := congrArg (fun z : j → ℂ => (z i).im) he
    simpa [Matrix.mulVec, dotProduct, Complex.mul_im, vr, vi, smul_eq_mul, add_comm] using hi
  let u := b.equivFun.symm vr
  let w := b.equivFun.symm vi
  have hrepr (x : realSubspace P) : b.equivFun (g x) = M.mulVec (b.equivFun x) := by
    simpa only [Module.Basis.equivFun_apply] using (g.toMatrix_mulVec_repr b b x).symm
  have hu : g u = μ.re • u - μ.im • w := by
    apply b.equivFun.injective
    rw [hrepr, map_sub, map_smul, map_smul]
    simpa only [u, w, LinearEquiv.apply_symm_apply] using hre
  have hw : g w = μ.im • u + μ.re • w := by
    apply b.equivFun.injective
    rw [hrepr, map_add, map_smul, map_smul]
    simpa only [u, w, LinearEquiv.apply_symm_apply] using him
  have hu' : A.mulVec (u : n → ℝ) = μ.re • (u : n → ℝ) - μ.im • (w : n → ℝ) :=
    congrArg Subtype.val hu
  have hw' : A.mulVec (w : n → ℝ) = μ.im • (u : n → ℝ) + μ.re • (w : n → ℝ) :=
    congrArg Subtype.val hw
  let z : n → ℂ := realVector (u : n → ℝ) + Complex.I • realVector (w : n → ℝ)
  have hzP : z ∈ P := P.add_mem u.property (P.smul_mem _ w.property)
  have hz0 : z ≠ 0 := by
    intro hzero
    have hu0 : u = 0 := by
      apply Subtype.ext
      ext i
      have hi := congrArg (fun z : n → ℂ => (z i).re) hzero
      simpa [z, realVector] using hi
    have hw0 : w = 0 := by
      apply Subtype.ext
      ext i
      have hi := congrArg (fun z : n → ℂ => (z i).im) hzero
      simpa [z, realVector] using hi
    have hr0 : vr = 0 := by
      have := congrArg b.equivFun hu0
      simpa only [u, LinearEquiv.apply_symm_apply, map_zero] using this
    have hi0 : vi = 0 := by
      have := congrArg b.equivFun hw0
      simpa only [w, LinearEquiv.apply_symm_apply, map_zero] using this
    apply hv.2
    ext i
    exact Complex.ext (congrFun hr0 i) (congrFun hi0 i)
  refine ⟨z, ⟨?_, hz0⟩, hzP⟩
  rw [Module.End.mem_eigenspace_iff]
  change (A.map Complex.ofReal).mulVec z = μ • z
  ext i
  apply Complex.ext
  · have hi := congrFun hu' i
    simpa [z, realVector, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
      smul_eq_mul] using hi
  · have hi := congrFun hw' i
    simpa [z, realVector, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
      smul_eq_mul, add_comm] using hi

lemma positive_spectral_gap
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    ∃ a : ℝ, 0 < a ∧ ∀ μ : ℂ, f.HasEigenvalue μ → 0 < μ.re → 2 * a < μ.re := by
  have aux (s : Finset ℂ) :
      ∃ a : ℝ, 0 < a ∧ ∀ μ ∈ s, 0 < μ.re → 2 * a < μ.re := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert μ s hnot ih =>
      obtain ⟨a, ha, hs⟩ := ih
      by_cases hμ : 0 < μ.re
      · refine ⟨min a (μ.re / 4), lt_min ha (by positivity), ?_⟩
        intro z hz hzpos
        rcases Finset.mem_insert.mp hz with rfl | hz
        · have := min_le_right a (z.re / 4)
          linarith
        · have := hs z hz hzpos
          have := min_le_left a (μ.re / 4)
          linarith
      · refine ⟨a, ha, ?_⟩
        intro z hz hzpos
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact (hμ hzpos).elim
        · exact hs z hz hzpos
  obtain ⟨a, ha, hs⟩ := aux f.finite_hasEigenvalue.toFinset
  exact ⟨a, ha, fun μ hμ => hs μ (by simpa using hμ)⟩

lemma matrix_shift_hurwitz
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (a : ℝ)
    (hM : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLinAlgEquiv' (M.map Complex.ofReal)) μ → μ.re < a) :
    IsHurwitz (M - a • 1) := by
  intro μ hμ
  let f : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' (M.map Complex.ofReal)
  have heq : Matrix.toLinAlgEquiv' ((M - a • 1).map Complex.ofReal) =
      f - (a : ℂ) • LinearMap.id := by
    have hmap : (M - a • 1).map Complex.ofReal =
        M.map Complex.ofReal - (a : ℂ) • 1 := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> simp_all
    rw [hmap, map_sub, map_smul, map_one]
    rfl
  rw [heq] at hμ
  have h := hM (μ + a) (Module.End.hasEigenvalue_sub_iff.mp hμ)
  simp only [Complex.add_re, Complex.ofReal_re] at h
  linarith

lemma matrix_negative_shift_hurwitz
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (a : ℝ)
    (hM : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLinAlgEquiv' (M.map Complex.ofReal)) μ → a < μ.re) :
    IsHurwitz (-M + a • 1) := by
  intro μ hμ
  let f : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' (M.map Complex.ofReal)
  have heq : Matrix.toLinAlgEquiv' ((-M + a • 1).map Complex.ofReal) =
      (a : ℂ) • LinearMap.id - f := by
    have hmap : (-M + a • 1).map Complex.ofReal =
        (a : ℂ) • 1 - M.map Complex.ofReal := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> simp_all <;> ring
    rw [hmap, map_sub, map_smul, map_one]
    rfl
  rw [heq] at hμ
  have h := hM (a - μ) (Module.End.hasEigenvalue_sub'_iff.mp hμ)
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  linarith

/-- The full finite-dimensional spectral-to-quadratic bridge. The positive
and nonpositive spectral sums are descended from the complexification before
choosing real bases. No invariant-manifold theorem is used. -/
theorem positive_eigenvalue_growth_certificate
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : Type*} [Fintype n] [DecidableEq n]
    (basis : Module.Basis n ℝ E) (A : E →L[ℝ] E)
    (hpos : ∃ μ : ℂ, 0 < μ.re ∧ Module.End.HasEigenvalue
      (Matrix.toLinAlgEquiv' ((LinearMap.toMatrix basis basis A.toLinearMap).map
        Complex.ofReal)) μ) : LinearGrowthCertificate A := by
  classical
  let R := LinearMap.toMatrix basis basis A.toLinearMap
  let f : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' (R.map Complex.ofReal)
  let S : Set ℂ := {μ | 0 < μ.re}
  let P := spectralSubspace f S
  let Q := spectralSubspace f Sᶜ
  have hSc : ∀ μ ∈ S, star μ ∈ S := by
    intro μ hμ
    simpa [S] using hμ
  have hScc : ∀ μ ∈ Sᶜ, star μ ∈ Sᶜ := by
    intro μ hμ
    simpa [S] using hμ
  have hP : ∀ x ∈ P, conjugateVector x ∈ P :=
    fun _ hx => conjugate_mem_spectralSubspace R S hSc hx
  have hQ : ∀ x ∈ Q, conjugateVector x ∈ Q :=
    fun _ hx => conjugate_mem_spectralSubspace R Sᶜ hScc hx
  let U := realSubspace P
  let W := realSubspace Q
  have hUW : IsCompl U W := realSubspace_isCompl P Q (spectralSubspace_isCompl f S) hP hQ
  have hUi : ∀ x ∈ U, R.mulVec x ∈ U := realSubspace_invariant R S
  have hWi : ∀ x ∈ W, R.mulVec x ∈ W := realSubspace_invariant R Sᶜ
  have hUne : U ≠ ⊥ := by
    intro hbot
    obtain ⟨μ, hμ, hμe⟩ := hpos
    obtain ⟨z, hz⟩ := hμe.exists_hasEigenvector
    have hzP : z ∈ P := (le_biSup f.maxGenEigenspace hμ)
      (Module.End.eigenspace_le_maxGenEigenspace hz.1)
    obtain ⟨hr, hi⟩ := real_imag_mem_of_conjugate_invariant P hP hzP
    have hr0 : (fun i => (z i).re) = 0 := (Submodule.mem_bot ℝ).mp (hbot ▸ hr)
    have hi0 : (fun i => (z i).im) = 0 := (Submodule.mem_bot ℝ).mp (hbot ▸ hi)
    apply hz.2
    ext i
    exact Complex.ext (congrFun hr0 i) (congrFun hi0 i)
  letI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
  let bU := Module.finBasis ℝ U
  let bW := Module.finBasis ℝ W
  let gu := (Matrix.toLinAlgEquiv' R).restrict hUi
  let gw := (Matrix.toLinAlgEquiv' R).restrict hWi
  let Mu := LinearMap.toMatrix bU bU gu
  let Mw := LinearMap.toMatrix bW bW gw
  obtain ⟨a, ha, hgap⟩ := positive_spectral_gap f
  have hMu : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLinAlgEquiv' (Mu.map Complex.ofReal)) μ → a < μ.re := by
    intro μ hμ
    obtain ⟨z, hz, hzP⟩ := lift_restriction_eigenvector R P hUi bU μ hμ
    have hm := eigenvalue_mem_of_mem_spectralSubspace f S hz hzP
    have hh := hgap μ (Module.End.hasEigenvalue_of_hasEigenvector hz) hm
    linarith
  have hMw : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLinAlgEquiv' (Mw.map Complex.ofReal)) μ → μ.re < a / 2 := by
    intro μ hμ
    obtain ⟨z, hz, hzQ⟩ := lift_restriction_eigenvector R Q hWi bW μ hμ
    have hm := eigenvalue_mem_of_mem_spectralSubspace f Sᶜ hz hzQ
    have hh : μ.re ≤ 0 := le_of_not_gt hm
    linarith
  let e := Submodule.prodEquivOfIsCompl U W hUW
  let T : E ≃L[ℝ] ((Fin (Module.finrank ℝ U) → ℝ) × (Fin (Module.finrank ℝ W) → ℝ)) :=
    (basis.equivFun.trans (e.symm.trans (bU.equivFun.prodCongr bW.equivFun))).toContinuousLinearEquiv
  letI : Nonempty (Fin (Module.finrank ℝ U)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  have hcoord (x : E) : basis.equivFun (A x) = R.mulVec (basis.equivFun x) := by
    change (basis.repr (A.toLinearMap x) : n → ℝ) =
      (LinearMap.toMatrix basis basis A.toLinearMap).mulVec (basis.repr x)
    exact (A.toLinearMap.toMatrix_mulVec_repr basis basis x).symm
  have heA (x : n → ℝ) : e.symm (R.mulVec x) =
      (gu (e.symm x).1, gw (e.symm x).2) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change R.mulVec x = R.mulVec ((e.symm x).1 : n → ℝ) +
      R.mulVec ((e.symm x).2 : n → ℝ)
    rw [← Matrix.mulVec_add]
    congr 1
    exact (e.apply_symm_apply x).symm
  apply block_growth_certificate A T Mu Mw a (a / 2) (by positivity) (by linarith)
    (matrix_negative_shift_hurwitz Mu a hMu) (matrix_shift_hurwitz Mw (a / 2) hMw)
  · intro x
    change bU.equivFun (e.symm (basis.equivFun (A x))).1 =
      Mu.mulVec (bU.equivFun (e.symm (basis.equivFun x)).1)
    rw [hcoord, heA]
    simpa only [Module.Basis.equivFun_apply] using
      (gu.toMatrix_mulVec_repr bU bU (e.symm (basis.equivFun x)).1).symm
  · intro x
    change bW.equivFun (e.symm (basis.equivFun (A x))).2 =
      Mw.mulVec (bW.equivFun (e.symm (basis.equivFun x)).2)
    rw [hcoord, heA]
    simpa only [Module.Basis.equivFun_apply] using
      (gw.toMatrix_mulVec_repr bW bW (e.symm (basis.equivFun x)).2).symm

theorem linearized_instability : linearizedInstabilityType.{u, v} := by
  intro E _ _ _ n _ _ basis F hF h0 heq hpos
  exact certificate_implies_escape F hF h0 heq
    (positive_eigenvalue_growth_certificate basis (fderiv ℝ (autonomousEvalValue F) 0) hpos)

end D13Unified.Ch12.LinearizedInstability
