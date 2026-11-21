import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.StampacchiaSolvability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! Stampacchia solvability by a projected coercive forward step.
All norms and metric structures are the original Hilbert ones. The zero
space is treated before choosing a step involving division by the bound. -/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.StampacchiaSolvability
universe u v

/-- Coercivity bounds a forward step in the original Hilbert norm. -/
theorem norm_coercive_forward_step (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (A : H →L[𝕜] H) (M α τ : ℝ)
    (hτ : 0 ≤ τ) (hA : ‖A‖ ≤ M)
    (hc : ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, A x⟫_𝕜)
    (hq : 0 ≤ 1 - 2 * τ * α + τ ^ 2 * M ^ 2) (x : H) :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal 𝕜 H
    ‖x - τ • A x‖ ≤ Real.sqrt (1 - 2 * τ * α + τ ^ 2 * M ^ 2) * ‖x‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal 𝕜 H
  have hb : ‖A x‖ ≤ M * ‖x‖ :=
    (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hb2 : ‖A x‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg (A x), norm_nonneg x]
  have hc' : α * ‖x‖ ^ 2 ≤ ⟪x, A x⟫_ℝ := hc x
  have heq : ‖x - τ • A x‖ ^ 2 =
      ‖x‖ ^ 2 - 2 * τ * ⟪x, A x⟫_ℝ + τ ^ 2 * ‖A x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hτ]
    ring
  have hsq : ‖x - τ • A x‖ ^ 2 ≤
      (1 - 2 * τ * α + τ ^ 2 * M ^ 2) * ‖x‖ ^ 2 := by
    rw [heq]
    nlinarith [mul_nonneg hτ (sub_nonneg.mpr hc'),
      mul_nonneg (sq_nonneg τ) (sub_nonneg.mpr hb2)]
  have hsqrt := Real.sq_sqrt hq
  have hpos := mul_nonneg (Real.sqrt_nonneg (1 - 2 * τ * α + τ ^ 2 * M ^ 2))
    (norm_nonneg x)
  nlinarith [norm_nonneg (x - τ • A x)]

/-- The variational inequality is the fixed-point equation for each positive step. -/
theorem projected_variational_iff (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (A : H →L[𝕜] H)
    (hA : ∀ x y, a x y = ⟪x, A y⟫_𝕜) (f : H)
    (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconvex : Conventions.RealConvex 𝕜 H C) (τ : ℝ) (hτ : 0 < τ) (u : H) :
    letI := Conventions.realification 𝕜 H
    (u ∈ C ∧ ∀ v ∈ C, RCLike.re ⟪v - u, f⟫_𝕜 ≤ RCLike.re (a (v - u) u)) ↔
      u = Projection.convexProjection 𝕜 H C hne hclosed hconvex
        (u - τ • (A u - f)) := by
  let := Conventions.realification 𝕜 H
  have hinner (v : H) :
      RCLike.re ⟪(u - τ • (A u - f)) - u, v - u⟫_𝕜 =
        -τ * (RCLike.re (a (v - u) u) - RCLike.re ⟪v - u, f⟫_𝕜) := by
    rw [hA]
    change ⟪(u - τ • (A u - f)) - u, v - u⟫_ℝ =
      -τ * (⟪v - u, A u⟫_ℝ - ⟪v - u, f⟫_ℝ)
    rw [← inner_sub_right, sub_sub_cancel_left, inner_neg_left,
      real_inner_smul_left, real_inner_comm]
    ring
  constructor
  · rintro ⟨hu, hv⟩
    apply (Projection.eq_convexProjection_iff_variational 𝕜 H C hne hclosed hconvex
      (u - τ • (A u - f)) u).mpr
    refine ⟨hu, fun v hvC => ?_⟩
    rw [hinner]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr (hv v hvC))
  · intro hfix
    obtain ⟨hu, hv⟩ :=
      (Projection.eq_convexProjection_iff_variational 𝕜 H C hne hclosed hconvex
        (u - τ • (A u - f)) u).mp hfix
    refine ⟨hu, fun v hvC => ?_⟩
    have h := hv v hvC
    rw [hinner] at h
    nlinarith

theorem stampacchia_exists_unique : Spec.ExistenceUniqueness.{u, v} := by
  intro 𝕜 H _ _ _ _ a M α ha hc f C hne hclosed hconvex
  classical
  let := Conventions.realification 𝕜 H
  cases subsingleton_or_nontrivial H with
  | inl hzero =>
    let : Subsingleton H := hzero
    obtain ⟨u, hu⟩ := hne
    refine ⟨u, ⟨hu, ?_⟩, fun y _ => Subsingleton.elim y u⟩
    intro v _
    simp [Subsingleton.elim v u]
  | inr hnontrivial =>
    let : Nontrivial H := hnontrivial
    obtain ⟨A, hA, hnorm, _⟩ := RieszRepresentation.form_representation 𝕜 H a
    have hAnorm : ‖A‖ ≤ M := hnorm.trans_le
      ((Conventions.form_norm_least_bound 𝕜 H H a).2 ha)
    have hαM : α ≤ M := by
      obtain ⟨x, hx⟩ := exists_ne (0 : H)
      have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      have h := (hc.2 x).trans ((RCLike.re_le_norm (a x x)).trans (ha.2 x x))
      nlinarith
    have hM : 0 < M := lt_of_lt_of_le hc.1 hαM
    have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
    let τ := α / M ^ 2
    have hτ : 0 < τ := div_pos hc.1 hM2
    have hτmax : τ * M ^ 2 < 2 * α := by
      dsimp [τ]
      rw [div_mul_cancel₀ _ (ne_of_gt hM2)]
      linarith [hc.1]
    let b := 1 - 2 * τ * α + τ ^ 2 * M ^ 2
    have hb : 0 ≤ b := by
      have hs : α ^ 2 ≤ M ^ 2 := by nlinarith [hc.1]
      have h := mul_nonneg (sq_nonneg τ) (sub_nonneg.mpr hs)
      dsimp [b]
      nlinarith [sq_nonneg (1 - τ * α)]
    have hb1 : b < 1 := by
      have h := mul_pos hτ (sub_pos.mpr hτmax)
      dsimp [b]
      nlinarith
    let q : NNReal := ⟨Real.sqrt b, Real.sqrt_nonneg _⟩
    have hq1 : q < 1 := by
      change Real.sqrt b < 1
      exact (Real.sqrt_lt hb zero_le_one).mpr (by simpa using hb1)
    let S : H → H := fun x => Projection.convexProjection 𝕜 H C hne hclosed hconvex
      (x - τ • (A x - f))
    have hmaps (x : H) : S x ∈ C :=
      (Projection.convexProjection_spec 𝕜 H C hne hclosed hconvex _).1
    have hLip : LipschitzWith q S := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, dist_eq_norm]
      change ‖S x - S y‖ ≤ Real.sqrt b * ‖x - y‖
      have heq : (x - τ • (A x - f)) - (y - τ • (A y - f)) =
          (x - y) - τ • A (x - y) := by
        rw [A.map_sub]
        simp only [smul_sub]
        abel
      have h := Projection.convexProjection_nonexpansive 𝕜 H C hne hclosed hconvex
        (x - τ • (A x - f)) (y - τ • (A y - f))
      rw [heq] at h
      exact h.trans (norm_coercive_forward_step 𝕜 H A M α τ hτ.le hAnorm
        (fun x => by rw [← hA]; exact hc.2 x) hb (x - y))
    have hS : ContractingWith q S := ⟨hq1, hLip⟩
    let u := hS.fixedPoint S
    have hfix : S u = u := hS.fixedPoint_isFixedPt
    have hequiv := projected_variational_iff 𝕜 H a A hA f C hne hclosed hconvex τ hτ
    refine ⟨u, (hequiv u).mpr hfix.symm, ?_⟩
    intro y hy
    exact hS.fixedPoint_unique ((hequiv y).mp hy).symm

end ExpandedFA.Hilbert.StampacchiaSolvability
