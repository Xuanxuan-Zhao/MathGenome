import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.WeierstrassExcess
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.FirstVariation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace VariationalNotes.Classical

/-- The piecewise strong minimum restricts to the same strong minimum on C¹
jets.  The proof checks both admissibility and equality of the two actions. -/
theorem piecewiseStrongLocalMinimum_strong {I : Interval} {m : ℕ}
    (L : Lagrangian m) (xₐ xᵦ : State m) (u : C1Curve I m)
    (hu : graphAdmissible L u)
    (h : piecewiseStrongLocalMinimum L xₐ xᵦ u.state) :
    strongLocalMinimum L xₐ xᵦ u := by
  obtain ⟨hu', ε, hε, hmin⟩ := h
  refine ⟨⟨hu, hu'.2⟩, ε, hε, ?_⟩
  intro v hv hdist
  have hv' : v.state ∈ piecewiseFixedEndpointClass L xₐ xᵦ :=
    ⟨VariationSpaces.graphAdmissible_piecewise I m L v hv.1, hv.2⟩
  have hm := hmin v.state hv' hdist
  rwa [VariationSpaces.piecewiseAction_of_C1 I m L u,
    VariationSpaces.piecewiseAction_of_C1 I m L v] at hm

namespace Weierstrass

/-- An endpoint-zero tent.  For positive h and 0 < s < 1 its slopes on
[t₀,t₀+s*h] and [t₀+s*h,t₀+h] are 1 and -s/(1-s), respectively. -/
def triangularProfile (t₀ s h t : ℝ) : ℝ :=
  max 0 (min (t - t₀) ((s / (1 - s)) * (t₀ + h - t)))

theorem triangularProfile_continuous (t₀ s h : ℝ) :
    Continuous (triangularProfile t₀ s h) := by
  exact continuous_const.max
    ((continuous_id.sub continuous_const).min
      (continuous_const.mul (continuous_const.sub continuous_id)))

theorem triangularProfile_nonneg (t₀ s h t : ℝ) :
    0 ≤ triangularProfile t₀ s h t := le_max_left _ _

theorem triangularProfile_eq_zero_left (t₀ s h t : ℝ) (ht : t ≤ t₀) :
    triangularProfile t₀ s h t = 0 := by
  apply max_eq_left
  exact (min_le_left _ _).trans (sub_nonpos.mpr ht)

theorem triangularProfile_eq_zero_right (t₀ s h t : ℝ)
    (hs : 0 ≤ s) (hs' : s < 1) (ht : t₀ + h ≤ t) :
    triangularProfile t₀ s h t = 0 := by
  apply max_eq_left
  apply (min_le_right _ _).trans
  exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hs (by linarith)) (by linarith)

theorem triangularProfile_eq_rising (t₀ s h t : ℝ) (hs : s < 1)
    (ht : t₀ ≤ t) (ht' : t ≤ t₀ + s * h) :
    triangularProfile t₀ s h t = t - t₀ := by
  have hpos : 0 < 1 - s := by linarith
  have hh : t - t₀ ≤ (s / (1 - s)) * (t₀ + h - t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith
  simp only [triangularProfile, min_eq_left hh, max_eq_right (sub_nonneg.mpr ht)]

theorem triangularProfile_eq_falling (t₀ s h t : ℝ) (hs : 0 ≤ s) (hs' : s < 1)
    (ht : t₀ + s * h ≤ t) (ht' : t ≤ t₀ + h) :
    triangularProfile t₀ s h t = (s / (1 - s)) * (t₀ + h - t) := by
  have hpos : 0 < 1 - s := by linarith
  have hh : (s / (1 - s)) * (t₀ + h - t) ≤ t - t₀ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith
  have hn : 0 ≤ (s / (1 - s)) * (t₀ + h - t) :=
    mul_nonneg (div_nonneg hs hpos.le) (by linarith)
  simp only [triangularProfile, min_eq_right hh, max_eq_right hn]

theorem triangularProfile_le (t₀ s h t : ℝ) (hs : 0 ≤ s) (hs' : s < 1)
    (hh : 0 ≤ h) : triangularProfile t₀ s h t ≤ s * h := by
  apply max_le (mul_nonneg hs hh)
  by_cases ht : t ≤ t₀ + s * h
  · exact (min_le_left _ _).trans (by linarith)
  · apply (min_le_right _ _).trans
    have hratio : 0 ≤ s / (1 - s) := div_nonneg hs (by linarith)
    have hb := mul_le_mul_of_nonneg_left
      (show t₀ + h - t ≤ t₀ + h - (t₀ + s * h) by linarith) hratio
    have he : (s / (1 - s)) * (t₀ + h - (t₀ + s * h)) = s * h := by
      field_simp
      ring
    exact he ▸ hb

/-- The triangular perturbation changes only positions in the uniform norm.
It need not be small in the C¹ norm. -/
def triangularCompetitor {I : Interval} {m : ℕ} (u : C1Curve I m)
    (t₀ : I.Points) (w : State m) (s h : ℝ) : C(I.Points, State m) :=
  ⟨fun t => u.state t + triangularProfile t₀ s h t • (w - u.velocity t₀),
    u.state.continuous.add
      (((triangularProfile_continuous t₀ s h).comp continuous_subtype_val).smul
        continuous_const)⟩

theorem triangularCompetitor_left {I : Interval} {m : ℕ} (u : C1Curve I m)
    (t₀ : I.Points) (w : State m) (s h : ℝ) :
    triangularCompetitor u t₀ w s h I.left = u.state I.left := by
  change u.state I.left + triangularProfile t₀ s h I.a • (w - u.velocity t₀) = _
  rw [triangularProfile_eq_zero_left _ _ _ _ t₀.property.1, zero_smul, add_zero]

theorem triangularCompetitor_right {I : Interval} {m : ℕ} (u : C1Curve I m)
    (t₀ : I.Points) (w : State m) (s h : ℝ)
    (hs : 0 ≤ s) (hs' : s < 1) (hh : (t₀ : ℝ) + h ≤ I.b) :
    triangularCompetitor u t₀ w s h I.right = u.state I.right := by
  change u.state I.right + triangularProfile t₀ s h I.b • (w - u.velocity t₀) = _
  rw [triangularProfile_eq_zero_right _ _ _ _ hs hs' hh, zero_smul, add_zero]

theorem triangularCompetitor_eq_outside {I : Interval} {m : ℕ} (u : C1Curve I m)
    (t₀ : I.Points) (w : State m) (s h : ℝ) (t : I.Points)
    (hs : 0 ≤ s) (hs' : s < 1)
    (ht : (t : ℝ) ≤ t₀ ∨ (t₀ : ℝ) + h ≤ t) :
    triangularCompetitor u t₀ w s h t = u.state t := by
  change u.state t + triangularProfile t₀ s h t • (w - u.velocity t₀) = _
  rcases ht with ht | ht
  · rw [triangularProfile_eq_zero_left _ _ _ _ ht, zero_smul, add_zero]
  · rw [triangularProfile_eq_zero_right _ _ _ _ hs hs' ht, zero_smul, add_zero]

theorem extendState_triangularCompetitor {I : Interval} {m : ℕ} (u : C1Curve I m)
    (t₀ : I.Points) (w : State m) (s h t : ℝ) (ht : t ∈ Icc I.a I.b) :
    extendState I m (triangularCompetitor u t₀ w s h) t =
      stateField I m u t + triangularProfile t₀ s h t • (w - u.velocity t₀) := by
  simp [extendState, stateField, ht, triangularCompetitor]

/-- Transfer the smooth affine formula for the scalar profile to a whole
closed piece, retaining the one-sided derivatives at its endpoints. -/
theorem triangularCompetitor_contDiffOn_of_profile {I : Interval} {m : ℕ}
    (u : C1Curve I m) (t₀ : I.Points) (w : State m) (s h c d : ℝ)
    (hsub : Icc c d ⊆ Icc I.a I.b) (P : ℝ → ℝ)
    (hP : ContDiffOn ℝ 1 P (Icc c d))
    (heq : ∀ t ∈ Icc c d, triangularProfile t₀ s h t = P t) :
    ContDiffOn ℝ 1 (extendState I m (triangularCompetitor u t₀ w s h)) (Icc c d) := by
  apply (((VariationSpaces.c1_contDiffOn I m u).mono hsub).add
    (hP.smul_const (w - u.velocity t₀))).congr
  intro t ht
  rw [extendState_triangularCompetitor u t₀ w s h t (hsub ht), heq t ht]

theorem triangularCompetitor_hasDerivWithinAt_of_profile {I : Interval} {m : ℕ}
    (u : C1Curve I m) (t₀ : I.Points) (w : State m) (s h c d t : ℝ)
    (hsub : Icc c d ⊆ Icc I.a I.b) (ht : t ∈ Icc c d)
    (P : ℝ → ℝ) (P' : ℝ) (hP : HasDerivWithinAt P P' (Icc c d) t)
    (heq : ∀ x ∈ Icc c d, triangularProfile t₀ s h x = P x) :
    HasDerivWithinAt (extendState I m (triangularCompetitor u t₀ w s h))
      (u.velocity ⟨t, hsub ht⟩ + P' • (w - u.velocity t₀)) (Icc c d) t := by
  apply (((VariationSpaces.curve_derivative I m u ⟨t, hsub ht⟩).mono hsub).add
    (hP.smul_const (w - u.velocity t₀))).congr_of_mem _ ht
  intro x hx
  rw [extendState_triangularCompetitor u t₀ w s h x (hsub hx), heq x hx]
  rfl

private theorem consecutive_five_knots {a b c d e x y : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hx : x ∈ ({a, b, c, d, e} : Finset ℝ))
    (hy : y ∈ ({a, b, c, d, e} : Finset ℝ)) (hxy : x < y)
    (hn : ∀ z ∈ ({a, b, c, d, e} : Finset ℝ), ¬ (x < z ∧ z < y)) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = c) ∨ (x = c ∧ y = d) ∨ (x = d ∧ y = e) := by
  have hB := hn b (by simp)
  have hC := hn c (by simp)
  have hD := hn d (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    | solve | exfalso; linarith
    | solve | exfalso; apply hB; constructor <;> linarith
    | solve | exfalso; apply hC; constructor <;> linarith
    | solve | exfalso; apply hD; constructor <;> linarith

theorem triangularCompetitor_piecewiseC1 {I : Interval} {m : ℕ}
    (u : C1Curve I m) (t₀ : I.Points) (w : State m) (s h : ℝ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo I.a I.b) (hs : 0 < s) (hs' : s < 1)
    (hh : 0 < h) (hh' : (t₀ : ℝ) + h < I.b) :
    piecewiseC1 (triangularCompetitor u t₀ w s h) := by
  have hleft := ht₀.1
  have hright := ht₀.2
  have hp : (t₀ : ℝ) < t₀ + s * h := by nlinarith
  have hp' : (t₀ : ℝ) + s * h < t₀ + h := by nlinarith
  refine ⟨{I.a, (t₀ : ℝ), t₀ + s * h, t₀ + h, I.b}, by simp, by simp, ?_, ?_⟩
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> constructor <;> linarith [I.increasing]
  · intro c hc d hd hcd hn
    rcases consecutive_five_knots ht₀.1 hp hp' hh' hc hd hcd hn with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply triangularCompetitor_contDiffOn_of_profile u t₀ w s h I.a t₀
        (Icc_subset_Icc le_rfl t₀.property.2) (fun _ => 0) contDiffOn_const
      intro t ht
      exact triangularProfile_eq_zero_left _ _ _ _ ht.2
    · apply triangularCompetitor_contDiffOn_of_profile u t₀ w s h t₀ (t₀ + s * h)
        (Icc_subset_Icc t₀.property.1 (by linarith)) (fun t => t - t₀)
        ((contDiff_id.sub contDiff_const).contDiffOn)
      intro t ht
      exact triangularProfile_eq_rising _ _ _ _ hs' ht.1 ht.2
    · apply triangularCompetitor_contDiffOn_of_profile u t₀ w s h (t₀ + s * h) (t₀ + h)
        (Icc_subset_Icc (by linarith) hh'.le) (fun t => (s / (1 - s)) * (t₀ + h - t))
        ((contDiff_const.mul (contDiff_const.sub contDiff_id)).contDiffOn)
      intro t ht
      exact triangularProfile_eq_falling _ _ _ _ hs.le hs' ht.1 ht.2
    · apply triangularCompetitor_contDiffOn_of_profile u t₀ w s h (t₀ + h) I.b
        (Icc_subset_Icc (by linarith) le_rfl) (fun _ => 0) contDiffOn_const
      intro t ht
      exact triangularProfile_eq_zero_right _ _ _ _ hs.le hs' ht.1

/-- The graph on a closed piece, including its one-sided velocities, is
computed using any smooth formula for the scalar tent on that piece. -/
theorem triangularCompetitor_admissible_piece_of_profile {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (t₀ : I.Points) (w : State m)
    (s h c d : ℝ) (hcd : c < d) (hsub : Icc c d ⊆ Icc I.a I.b)
    (P : ℝ → ℝ) (P' : ℝ) (hP : ContDiffOn ℝ 1 P (Icc c d))
    (hP' : ∀ t ∈ Icc c d, HasDerivWithinAt P P' (Icc c d) t)
    (heq : ∀ t ∈ Icc c d, triangularProfile t₀ s h t = P t)
    (hgraph : ∀ t : I.Points, (t : ℝ) ∈ Icc c d →
      ((t : ℝ), triangularCompetitor u t₀ w s h t,
        u.velocity t + P' • (w - u.velocity t₀)) ∈ L.domain) :
    ContDiffOn ℝ 1 (extendState I m (triangularCompetitor u t₀ w s h)) (Icc c d) ∧
    ∀ t ∈ Icc c d, (t, extendState I m (triangularCompetitor u t₀ w s h) t,
      derivWithin (extendState I m (triangularCompetitor u t₀ w s h)) (Icc c d) t) ∈
        L.domain := by
  refine ⟨triangularCompetitor_contDiffOn_of_profile u t₀ w s h c d hsub P hP heq, ?_⟩
  intro t ht
  rw [(triangularCompetitor_hasDerivWithinAt_of_profile u t₀ w s h c d t hsub ht
    P P' (hP' t ht) heq).derivWithin (uniqueDiffOn_Icc hcd t ht)]
  simpa [extendState, hsub ht] using hgraph ⟨t, hsub ht⟩ ht

theorem triangularCompetitor_piecewiseAdmissible_of_graphs {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (t₀ : I.Points) (w : State m) (s h : ℝ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo I.a I.b) (hs : 0 < s) (hs' : s < 1)
    (hh : 0 < h) (hh' : (t₀ : ℝ) + h < I.b) (hbase : graphAdmissible L u)
    (hrise : ∀ t : I.Points, (t : ℝ) ∈ Icc (t₀ : ℝ) (t₀ + s * h) →
      ((t : ℝ), triangularCompetitor u t₀ w s h t,
        u.velocity t + (w - u.velocity t₀)) ∈ L.domain)
    (hfall : ∀ t : I.Points, (t : ℝ) ∈ Icc (t₀ + s * h) (t₀ + h) →
      ((t : ℝ), triangularCompetitor u t₀ w s h t,
        u.velocity t - (s / (1 - s)) • (w - u.velocity t₀)) ∈ L.domain) :
    piecewiseAdmissible L (triangularCompetitor u t₀ w s h) := by
  have hleft := ht₀.1
  have hright := ht₀.2
  have hp : (t₀ : ℝ) < t₀ + s * h := by nlinarith
  have hp' : (t₀ : ℝ) + s * h < t₀ + h := by nlinarith
  refine ⟨{I.a, (t₀ : ℝ), t₀ + s * h, t₀ + h, I.b}, by simp, by simp, ?_, ?_⟩
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> constructor <;> linarith [I.increasing]
  · intro c hc d hd hcd hn
    rcases consecutive_five_knots ht₀.1 hp hp' hh' hc hd hcd hn with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply triangularCompetitor_admissible_piece_of_profile L u t₀ w s h I.a t₀ hcd
        (Icc_subset_Icc le_rfl t₀.property.2) (fun _ => 0) 0 contDiffOn_const
        (fun _ _ => hasDerivWithinAt_const _ _ _) (fun t ht =>
          triangularProfile_eq_zero_left _ _ _ _ ht.2)
      intro t ht
      rw [triangularCompetitor_eq_outside u t₀ w s h t hs.le hs' (Or.inl ht.2)]
      simpa [graphPoint] using hbase t
    · apply triangularCompetitor_admissible_piece_of_profile L u t₀ w s h t₀ (t₀ + s * h) hcd
        (Icc_subset_Icc t₀.property.1 (by linarith)) (fun t => t - t₀) 1
        ((contDiff_id.sub contDiff_const).contDiffOn)
        (fun t _ => ((hasDerivAt_id t).sub_const (t₀ : ℝ)).hasDerivWithinAt)
        (fun t ht => triangularProfile_eq_rising _ _ _ _ hs' ht.1 ht.2)
      simpa using hrise
    · apply triangularCompetitor_admissible_piece_of_profile L u t₀ w s h
        (t₀ + s * h) (t₀ + h) hcd (Icc_subset_Icc (by linarith) hh'.le)
        (fun t => (s / (1 - s)) * (t₀ + h - t)) (-(s / (1 - s)))
        ((contDiff_const.mul (contDiff_const.sub contDiff_id)).contDiffOn)
        (by
          intro t ht
          simpa using
            (((hasDerivAt_id t).const_sub ((t₀ : ℝ) + h)).const_mul
              (s / (1 - s))).hasDerivWithinAt)
        (fun t ht => triangularProfile_eq_falling _ _ _ _ hs.le hs' ht.1 ht.2)
      simpa only [neg_smul, sub_eq_add_neg] using hfall
    · apply triangularCompetitor_admissible_piece_of_profile L u t₀ w s h (t₀ + h) I.b hcd
        (Icc_subset_Icc (by linarith) le_rfl) (fun _ => 0) 0 contDiffOn_const
        (fun _ _ => hasDerivWithinAt_const _ _ _) (fun t ht =>
          triangularProfile_eq_zero_right _ _ _ _ hs.le hs' ht.1)
      intro t ht
      rw [triangularCompetitor_eq_outside u t₀ w s h t hs.le hs' (Or.inr ht.1)]
      simpa [graphPoint] using hbase t

/-- A continuous graph based in an open set remains there over a shrinking
right interval.  Both interval endpoints are included. -/
theorem eventually_between_mem_of_continuousAt {E : Type*} [TopologicalSpace E]
    (F : ℝ × ℝ → E) (t₀ : ℝ) {U : Set E} (hU : IsOpen U)
    (hF : ContinuousAt F (0, t₀)) (hx : F (0, t₀) ∈ U) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc t₀ (t₀ + h), F (h, t) ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hF.eventually (hU.mem_nhds hx))
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < ε :=
    nhdsWithin_le_nhds (Iio_mem_nhds hε)
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  filter_upwards [hsmall, hpos] with h hsmall hpos
  intro t ht
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq,
    sub_zero, abs_of_pos hpos, abs_of_nonneg (sub_nonneg.mpr ht.1)]
  exact max_lt_iff.mpr ⟨hsmall, lt_of_le_of_lt (by linarith [ht.2]) hsmall⟩

theorem triangularCompetitor_norm_le {I : Interval} {m : ℕ} (u : C1Curve I m)
    (t₀ : I.Points) (w : State m) (s h : ℝ)
    (hs : 0 ≤ s) (hs' : s < 1) (hh : 0 ≤ h) :
    ‖triangularCompetitor u t₀ w s h - u.state‖ ≤ s * h * ‖w - u.velocity t₀‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg hs hh) (norm_nonneg _))).2
  intro t
  change ‖(u.state t + triangularProfile t₀ s h t • (w - u.velocity t₀)) -
    u.state t‖ ≤ _
  rw [add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (triangularProfile_nonneg _ _ _ _)]
  exact mul_le_mul_of_nonneg_right (triangularProfile_le _ _ _ _ hs hs' hh) (norm_nonneg _)

theorem triangularCompetitor_tendsto {I : Interval} {m : ℕ} (u : C1Curve I m)
    (t₀ : I.Points) (w : State m) (s : ℝ) (hs : 0 ≤ s) (hs' : s < 1) :
    Tendsto (fun h : ℝ => ‖triangularCompetitor u t₀ w s h - u.state‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (hpos.mono (fun h hh =>
      triangularCompetitor_norm_le u t₀ w s h hs hs' hh.le))
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa using ((tendsto_const_nhds (x := s)).mul hid).mul_const ‖w - u.velocity t₀‖

/-- A normalized action limit of uniformly small admissible competitors is
nonnegative at a piecewise strong local minimum. -/
theorem nonneg_of_piecewise_action_limit {I : Interval} {m : ℕ}
    (L : Lagrangian m) (xₐ xᵦ : State m) (u : C1Curve I m)
    (hmin : piecewiseStrongLocalMinimum L xₐ xᵦ u.state)
    (family : ℝ → C(I.Points, State m))
    (hadm : ∀ᶠ h in 𝓝[>] (0 : ℝ), family h ∈ piecewiseFixedEndpointClass L xₐ xᵦ)
    (hsmall : Tendsto (fun h => ‖family h - u.state‖) (𝓝[>] 0) (𝓝 0))
    {c : ℝ}
    (hlim : Tendsto
      (fun h => (piecewiseAction L (family h) - action L u) / h)
      (𝓝[>] 0) (𝓝 c)) : 0 ≤ c := by
  obtain ⟨_, ε, hε, hm⟩ := hmin
  apply ge_of_tendsto hlim
  have hn := hsmall.eventually (Iio_mem_nhds hε)
  filter_upwards [hadm, hn, self_mem_nhdsWithin] with h hh hnorm hpos
  have hineq := hm (family h) hh hnorm
  rw [VariationSpaces.piecewiseAction_of_C1 I m L u] at hineq
  exact div_nonneg (sub_nonneg.mpr hineq) hpos.le

theorem velocityInsertionRegular.regularNearGraph {I : Interval} {m : ℕ}
    {L : Lagrangian m} {u : C1Curve I m} {t₀ : I.Points} {w : State m}
    (h : velocityInsertionRegular L u t₀ w) : regularNearGraph L u 1 := by
  obtain ⟨U, hU, hdom, hdiff, hu, _⟩ := h
  exact ⟨U, hU, hu, hdom, hdiff⟩

theorem velocityInsertionRegular.graphAdmissible {I : Interval} {m : ℕ}
    {L : Lagrangian m} {u : C1Curve I m} {t₀ : I.Points} {w : State m}
    (h : velocityInsertionRegular L u t₀ w) : graphAdmissible L u := by
  obtain ⟨U, _, hdom, _, hu, _⟩ := h
  exact fun t => hdom (hu t)

theorem velocityInsertionRegular.eventual_triangular_admissibility
    {I : Interval} {m : ℕ} {L : Lagrangian m} {u : C1Curve I m}
    {t₀ : I.Points} {w xₐ xᵦ : State m}
    (hreg : velocityInsertionRegular L u t₀ w)
    (ht₀ : (t₀ : ℝ) ∈ Ioo I.a I.b)
    (hleft : u.state I.left = xₐ) (hright : u.state I.right = xᵦ) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
      triangularCompetitor u t₀ w s h ∈ piecewiseFixedEndpointClass L xₐ xᵦ := by
  have hbase := hreg.graphAdmissible
  obtain ⟨U, _, hdom, _, _, δ, hδ, hseg⟩ := hreg
  have hw : ((t₀ : ℝ), u.state t₀, w) ∈ L.domain := by
    apply hdom
    simpa using hseg t₀ (by simpa using hδ) 1 (by simp)
  have hratio : ContinuousAt (fun s : ℝ => s / (1 - s)) 0 :=
    continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hret : ContinuousAt (fun s : ℝ =>
      ((t₀ : ℝ), u.state t₀,
        u.velocity t₀ - (s / (1 - s)) • (w - u.velocity t₀))) 0 :=
    continuousAt_const.prodMk
      (continuousAt_const.prodMk
        (continuousAt_const.sub (hratio.smul continuousAt_const)))
  have hzero : ((t₀ : ℝ), u.state t₀,
      u.velocity t₀ - ((0 : ℝ) / (1 - 0)) • (w - u.velocity t₀)) ∈ L.domain := by
    simpa [graphPoint] using hbase t₀
  have hreturn := (hret.eventually (L.isOpen_domain.mem_nhds hzero)).filter_mono
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hspos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hslt : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hz : ContinuousAt (stateField I m u) (t₀ : ℝ) :=
    (stateField_continuousOn I m u).continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hv : ContinuousAt (velocityField I m u) (t₀ : ℝ) :=
    (velocityField_continuousOn I m u).continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  filter_upwards [hreturn, hspos, hslt] with s hreturn hspos hslt
  have hp : Continuous (fun x : ℝ × ℝ => triangularProfile t₀ s x.1 x.2) :=
    continuous_const.max ((continuous_snd.sub continuous_const).min
      (continuous_const.mul ((continuous_const.add continuous_fst).sub continuous_snd)))
  let F : ℝ × ℝ → ℝ × State m × State m := fun x =>
    (x.2, stateField I m u x.2 + triangularProfile t₀ s x.1 x.2 • (w - u.velocity t₀),
      velocityField I m u x.2 + (w - u.velocity t₀))
  let G : ℝ × ℝ → ℝ × State m × State m := fun x =>
    (x.2, stateField I m u x.2 + triangularProfile t₀ s x.1 x.2 • (w - u.velocity t₀),
      velocityField I m u x.2 - (s / (1 - s)) • (w - u.velocity t₀))
  have hF : ContinuousAt F (0, (t₀ : ℝ)) :=
    continuousAt_snd.prodMk
      (((hz.comp (f := fun x : ℝ × ℝ => x.2) continuousAt_snd).add (hp.continuousAt.smul continuousAt_const)).prodMk
        ((hv.comp (f := fun x : ℝ × ℝ => x.2) continuousAt_snd).add continuousAt_const))
  have hG : ContinuousAt G (0, (t₀ : ℝ)) :=
    continuousAt_snd.prodMk
      (((hz.comp (f := fun x : ℝ × ℝ => x.2) continuousAt_snd).add (hp.continuousAt.smul continuousAt_const)).prodMk
        ((hv.comp (f := fun x : ℝ × ℝ => x.2) continuousAt_snd).sub continuousAt_const))
  have hFzero : F (0, (t₀ : ℝ)) ∈ L.domain := by
    simpa [F, triangularProfile, stateField, velocityField, extendState, t₀.property.1, t₀.property.2,
      ← add_sub_assoc, add_comm] using hw
  have hGzero : G (0, (t₀ : ℝ)) ∈ L.domain := by
    have heq : G (0, (t₀ : ℝ)) = ((t₀ : ℝ), u.state t₀,
        u.velocity t₀ - (s / (1 - s)) • (w - u.velocity t₀)) := by
      simp [G, triangularProfile, stateField, velocityField, extendState,
        t₀.property.1, t₀.property.2]
    rw [heq]
    exact hreturn
  have hFnear := eventually_between_mem_of_continuousAt F t₀ L.isOpen_domain hF hFzero
  have hGnear := eventually_between_mem_of_continuousAt G t₀ L.isOpen_domain hG hGzero
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  have hbound : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < I.b - t₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr ht₀.2))
  filter_upwards [hFnear, hGnear, hpos, hbound] with h hFnear hGnear hpos hbound
  have hb : (t₀ : ℝ) + h < I.b := by linarith
  refine ⟨triangularCompetitor_piecewiseAdmissible_of_graphs L u t₀ w s h ht₀ hspos hslt
    hpos hb hbase ?_ ?_, ?_, ?_⟩
  · intro t ht
    have ht' : (t : ℝ) ∈ Icc (t₀ : ℝ) (t₀ + h) := ⟨ht.1, by nlinarith [ht.2]⟩
    simpa [F, triangularCompetitor, stateField, velocityField, extendState, t.property.1, t.property.2] using
      hFnear (t : ℝ) ht'
  · intro t ht
    have ht' : (t : ℝ) ∈ Icc (t₀ : ℝ) (t₀ + h) := ⟨by nlinarith [ht.1], ht.2⟩
    simpa [G, triangularCompetitor, stateField, velocityField, extendState, t.property.1, t.property.2] using
      hGnear (t : ℝ) ht'
  · rw [triangularCompetitor_left, hleft]
  · rw [triangularCompetitor_right u t₀ w s h hspos.le hslt hb.le, hright]

/-- The inserted velocity and all sufficiently small returning velocities
lie in the same smooth neighborhood.  In particular the returning side
does not require a global assumption on the velocity domain. -/
theorem velocityInsertionRegular.frozen_continuity {I : Interval} {m : ℕ}
    {L : Lagrangian m} {u : C1Curve I m} {t₀ : I.Points} {w : State m}
    (h : velocityInsertionRegular L u t₀ w) :
    ContinuousAt L.value (graphPoint u t₀) ∧
    ContinuousAt L.value ((t₀ : ℝ), u.state t₀, w) ∧
    ∀ᶠ s in 𝓝 (0 : ℝ), ContinuousAt L.value
      ((t₀ : ℝ), u.state t₀,
        u.velocity t₀ - (s / (1 - s)) • (w - u.velocity t₀)) := by
  obtain ⟨U, hU, _, hdiff, hu, δ, hδ, hseg⟩ := h
  have hc : ∀ x ∈ U, ContinuousAt L.value x := fun x hx =>
    hdiff.continuousOn.continuousAt (hU.mem_nhds hx)
  have hw : ((t₀ : ℝ), u.state t₀, w) ∈ U := by
    simpa using hseg t₀ (by simpa using hδ) 1 (by simp)
  refine ⟨hc _ (hu t₀), hc _ hw, ?_⟩
  have hratio : ContinuousAt (fun s : ℝ => s / (1 - s)) 0 :=
    continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hret : ContinuousAt (fun s : ℝ =>
      ((t₀ : ℝ), u.state t₀,
        u.velocity t₀ - (s / (1 - s)) • (w - u.velocity t₀))) 0 :=
    continuousAt_const.prodMk
      (continuousAt_const.prodMk
        (continuousAt_const.sub (hratio.smul continuousAt_const)))
  have hzero : ((t₀ : ℝ), u.state t₀,
      u.velocity t₀ - ((0 : ℝ) / (1 - 0)) • (w - u.velocity t₀)) ∈ U := by
    simpa [graphPoint] using hu t₀
  exact (hret.eventually (hU.mem_nhds hzero)).mono (fun _ hx => hc _ hx)

/-- A right local minimum at zero gives a nonnegative derivative.  This
version uses a punctured right neighborhood, suited to the needle length. -/
theorem nonneg_derivative_of_right_minimum {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0)
    (hm : ∀ᶠ s in 𝓝[>] (0 : ℝ), f 0 ≤ f s) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [hm, self_mem_nhdsWithin] with s hs hpos
  simpa only [zero_add, smul_eq_mul] using
    mul_nonneg (inv_nonneg.mpr hpos.le) (sub_nonneg.mpr hs)

/-- Recover the supporting hyperplane inequality from the two-slope
comparison obtained by shrinking an endpoint-zero triangular perturbation.
Only differentiability at v is used; no convexity assumption is made. -/
theorem supporting_inequality_of_two_slope_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (v w : E) (D : E →L[ℝ] ℝ)
    (hf : HasFDerivAt f D v)
    (hcomp : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      f v ≤ s * f w + (1 - s) * f (v - (s / (1 - s)) • (w - v))) :
    0 ≤ f w - f v - D (w - v) := by
  have hratio : HasDerivAt (fun s : ℝ => s / (1 - s)) 1 0 := by
    convert (hasDerivAt_id (0 : ℝ)).div
      ((hasDerivAt_id (0 : ℝ)).const_sub 1) (by norm_num) using 1 <;>
      first | rfl | norm_num
  have hpath : HasDerivAt (fun s : ℝ => v - (s / (1 - s)) • (w - v))
      (-(w - v)) 0 := by
    simpa using (hratio.smul_const (w - v)).const_sub v
  have hinner : HasDerivAt (fun s : ℝ => f (v - (s / (1 - s)) • (w - v)))
        (D (-(w - v))) 0 := by
    have hv : v - ((0 : ℝ) / (1 - 0)) • (w - v) = v := by simp
    exact (hv.symm ▸ hf).comp_hasDerivAt 0 hpath
  have hg : HasDerivAt
      (fun s : ℝ => s * f w + (1 - s) * f (v - (s / (1 - s)) • (w - v)))
      (f w - f v - D (w - v)) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const (f w)).add
      (((hasDerivAt_id (0 : ℝ)).const_sub 1).mul hinner) using 1
    · ext s
      simp
    · simp
      ring
  apply nonneg_derivative_of_right_minimum hg
  simpa using hcomp

/-- Final algebraic reduction for the paper's momentum convention.  The
comparison hypothesis is a proof-internal intermediate claim, not an extra
hypothesis of the main theorem. -/
theorem excess_nonneg_of_two_slope_comparison {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (t₀ : I.Points) (w : State m)
    (hreg : regularNearGraph L u 1)
    (hcomp : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      L.value (graphPoint u t₀) ≤
        s * L.value ((t₀ : ℝ), u.state t₀, w) +
        (1 - s) * L.value ((t₀ : ℝ), u.state t₀,
          u.velocity t₀ - (s / (1 - s)) • (w - u.velocity t₀))) :
    0 ≤ excess L u t₀ w := by
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  have hdiff : DifferentiableAt ℝ L.value (graphPoint u t₀) :=
    (hL.differentiableOn (by simp) _ (hu t₀)).differentiableAt (hU.mem_nhds (hu t₀))
  have hpair : HasFDerivAt (fun v => ((t₀ : ℝ), u.state t₀, v))
      (velocityInsertion m) (u.velocity t₀) := by
    convert (hasFDerivAt_const (𝕜 := ℝ) (t₀ : ℝ) (u.velocity t₀)).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) (u.state t₀) (u.velocity t₀)).prodMk
        (hasFDerivAt_id (𝕜 := ℝ) (u.velocity t₀))) using 1 <;> ext v <;> rfl
  have hv := hdiff.hasFDerivAt.comp (u.velocity t₀) hpair
  have he := supporting_inequality_of_two_slope_comparison
    (fun v => L.value ((t₀ : ℝ), u.state t₀, v)) (u.velocity t₀) w _ hv hcomp
  unfold excess
  rw [momentum_eq_total L u t₀ hdiff, InnerProductSpace.toDual_symm_apply]
  exact he

/-- Assembly from the two substantive needle claims: admissibility, and the
normalized action limit.  The source theorem below must establish both
claims, rather than assume them. -/
theorem excess_nonneg_of_triangular_action_limits {I : Interval} {m : ℕ}
    (L : Lagrangian m) (xₐ xᵦ : State m) (u : C1Curve I m)
    (t₀ : I.Points) (w : State m)
    (hmin : piecewiseStrongLocalMinimum L xₐ xᵦ u.state)
    (hreg : regularNearGraph L u 1)
    (hadm : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
      triangularCompetitor u t₀ w s h ∈ piecewiseFixedEndpointClass L xₐ xᵦ)
    (hlim : ∀ᶠ s in 𝓝[>] (0 : ℝ), Tendsto
      (fun h => (piecewiseAction L (triangularCompetitor u t₀ w s h) - action L u) / h)
      (𝓝[>] 0) (𝓝 (s * L.value ((t₀ : ℝ), u.state t₀, w) +
        (1 - s) * L.value ((t₀ : ℝ), u.state t₀,
          u.velocity t₀ - (s / (1 - s)) • (w - u.velocity t₀)) -
        L.value (graphPoint u t₀)))) :
    0 ≤ excess L u t₀ w := by
  apply excess_nonneg_of_two_slope_comparison L u t₀ w hreg
  have hspos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hslt' : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), s < 1 :=
    Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hslt : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < 1 :=
    hslt'.filter_mono nhdsWithin_le_nhds
  filter_upwards [hadm, hlim, hspos, hslt] with s hsadm hslim hspos hslt
  have hnonneg := nonneg_of_piecewise_action_limit L xₐ xᵦ u hmin
    (fun h => triangularCompetitor u t₀ w s h) hsadm
    (triangularCompetitor_tendsto u t₀ w s hspos.le hslt) hslim
  exact sub_nonneg.mp hnonneg

/-- The smooth density on a single affine piece of the perturbation. -/
def affineDensity {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m)
    (d : State m) (P : ℝ → ℝ) (r t : ℝ) : ℝ :=
  L.value (t, stateField I m u t + P t • d, velocityField I m u t + r • d)

/-- At interior points of a smooth piece, the derivative used by the action
agrees with the piece derivative. Endpoints are excluded before integrating. -/
theorem triangular_density_piece {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (t₀ : I.Points) (w : State m)
    (s h c d : ℝ) (_hcd : c < d) (hsub : Icc c d ⊆ Icc I.a I.b)
    (P : ℝ → ℝ) (r : ℝ)
    (hP : ∀ t ∈ Icc c d, HasDerivWithinAt P r (Icc c d) t)
    (heq : ∀ t ∈ Icc c d, triangularProfile t₀ s h t = P t) :
    EqOn (fun t => L.value (t,
      extendState I m (triangularCompetitor u t₀ w s h) t,
      derivWithin (extendState I m (triangularCompetitor u t₀ w s h)) (Icc I.a I.b) t))
      (affineDensity L u (w - u.velocity t₀) P r) (Ioo c d) := by
  intro t ht
  dsimp only
  have htc : t ∈ Icc c d := ⟨ht.1.le, ht.2.le⟩
  have htI := hsub htc
  have hd := triangularCompetitor_hasDerivWithinAt_of_profile u t₀ w s h c d t
    hsub htc P r (hP t htc) heq
  rw [(hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc I.increasing t htI)]
  rw [extendState_triangularCompetitor u t₀ w s h t htI, heq t htc]
  simp [affineDensity, velocityField, extendState, htI]

/-- Exact action cancellation outside the tent. Integrability hypotheses
refer only to the two explicit smooth pieces and the reference density. -/
theorem triangular_action_decomposition {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (t₀ : I.Points) (w : State m)
    (s h : ℝ) (ht₀ : (t₀ : ℝ) ∈ Ioo I.a I.b)
    (hs : 0 < s) (hs' : s < 1) (hh : 0 < h) (hh' : (t₀ : ℝ) + h < I.b)
    (hbase : IntervalIntegrable
      (fun t => L.value (t, stateField I m u t, velocityField I m u t)) volume I.a I.b)
    (hrise : IntervalIntegrable
      (affineDensity L u (w - u.velocity t₀) (fun t => t - t₀) 1)
      volume (t₀ : ℝ) (t₀ + s * h))
    (hfall : IntervalIntegrable
      (affineDensity L u (w - u.velocity t₀)
        (fun t => (s / (1 - s)) * (t₀ + h - t)) (-(s / (1 - s))))
      volume ((t₀ : ℝ) + s * h) (t₀ + h)) :
    piecewiseAction L (triangularCompetitor u t₀ w s h) - action L u =
      (∫ t in (t₀ : ℝ)..t₀ + s * h,
        affineDensity L u (w - u.velocity t₀) (fun t => t - t₀) 1 t) +
      (∫ t in (t₀ : ℝ) + s * h..t₀ + h,
        affineDensity L u (w - u.velocity t₀)
          (fun t => (s / (1 - s)) * (t₀ + h - t)) (-(s / (1 - s))) t) -
      (∫ t in (t₀ : ℝ)..t₀ + h,
        L.value (t, stateField I m u t, velocityField I m u t)) := by
  let F := fun t => L.value (t,
    extendState I m (triangularCompetitor u t₀ w s h) t,
    derivWithin (extendState I m (triangularCompetitor u t₀ w s h)) (Icc I.a I.b) t)
  let B := fun t => L.value (t, stateField I m u t, velocityField I m u t)
  have hleft := ht₀.1
  have hp : (t₀ : ℝ) < t₀ + s * h := by nlinarith
  have hp' : (t₀ : ℝ) + s * h < t₀ + h := by nlinarith
  have h1 : EqOn F B (Ioo I.a (t₀ : ℝ)) := by
    simpa [affineDensity, F, B, EqOn] using triangular_density_piece L u t₀ w s h I.a t₀
      ht₀.1 (Icc_subset_Icc le_rfl t₀.property.2) (fun _ => 0) 0
      (fun _ _ => hasDerivWithinAt_const _ _ _)
      (fun t ht => triangularProfile_eq_zero_left _ _ _ _ ht.2)
  have h2 := triangular_density_piece L u t₀ w s h t₀ (t₀ + s * h) hp
    (Icc_subset_Icc t₀.property.1 (by linarith)) (fun t => t - t₀) 1
    (fun t _ => ((hasDerivAt_id t).sub_const (t₀ : ℝ)).hasDerivWithinAt)
    (fun t ht => triangularProfile_eq_rising _ _ _ _ hs' ht.1 ht.2)
  have h3 := triangular_density_piece L u t₀ w s h (t₀ + s * h) (t₀ + h) hp'
    (Icc_subset_Icc (by linarith) hh'.le)
    (fun t => (s / (1 - s)) * (t₀ + h - t)) (-(s / (1 - s)))
    (fun t _ => by simpa using
      (((hasDerivAt_id t).const_sub ((t₀ : ℝ) + h)).const_mul (s / (1 - s))).hasDerivWithinAt)
    (fun t ht => triangularProfile_eq_falling _ _ _ _ hs.le hs' ht.1 ht.2)
  have h4 : EqOn F B (Ioo ((t₀ : ℝ) + h) I.b) := by
    simpa [affineDensity, F, B, EqOn] using triangular_density_piece L u t₀ w s h (t₀ + h) I.b
      hh' (Icc_subset_Icc (by linarith) le_rfl) (fun _ => 0) 0
      (fun _ _ => hasDerivWithinAt_const _ _ _)
      (fun t ht => triangularProfile_eq_zero_right _ _ _ _ hs.le hs' ht.1)
  have b1 : IntervalIntegrable B volume I.a t₀ :=
    hbase.mono_set (by
      rw [uIcc_of_le ht₀.1.le, uIcc_of_le I.increasing.le]
      exact Icc_subset_Icc le_rfl t₀.property.2)
  have b2 : IntervalIntegrable B volume (t₀ : ℝ) (t₀ + h) :=
    hbase.mono_set (by
      rw [uIcc_of_le (by linarith : (t₀ : ℝ) ≤ t₀ + h), uIcc_of_le I.increasing.le]
      exact Icc_subset_Icc t₀.property.1 hh'.le)
  have b3 : IntervalIntegrable B volume ((t₀ : ℝ) + h) I.b :=
    hbase.mono_set (by
      rw [uIcc_of_le hh'.le, uIcc_of_le I.increasing.le]
      exact Icc_subset_Icc (by linarith [t₀.property.1]) le_rfl)
  have f1 : IntervalIntegrable F volume I.a t₀ :=
    b1.congr_uIoo (by rw [uIoo_of_le ht₀.1.le]; exact h1.symm)
  have f2 : IntervalIntegrable F volume (t₀ : ℝ) (t₀ + s * h) :=
    hrise.congr_uIoo (by rw [uIoo_of_le hp.le]; exact h2.symm)
  have f3 : IntervalIntegrable F volume ((t₀ : ℝ) + s * h) (t₀ + h) :=
    hfall.congr_uIoo (by rw [uIoo_of_le hp'.le]; exact h3.symm)
  have f4 : IntervalIntegrable F volume ((t₀ : ℝ) + h) I.b :=
    b3.congr_uIoo (by rw [uIoo_of_le hh'.le]; exact h4.symm)
  have eqF := intervalIntegral.integral_add_adjacent_intervals
    ((f1.trans f2).trans f3) f4
  rw [← intervalIntegral.integral_add_adjacent_intervals (f1.trans f2) f3,
      ← intervalIntegral.integral_add_adjacent_intervals f1 f2] at eqF
  have eqB := intervalIntegral.integral_add_adjacent_intervals (b1.trans b2) b3
  rw [← intervalIntegral.integral_add_adjacent_intervals b1 b2] at eqB
  change (∫ t in I.a..I.b, F t) - (∫ t in I.a..I.b, B t) = _
  rw [← eqF, ← eqB,
    intervalIntegral.integral_congr_Ioo_of_le ht₀.1.le h1,
    intervalIntegral.integral_congr_Ioo_of_le hp.le h2,
    intervalIntegral.integral_congr_Ioo_of_le hp'.le h3,
    intervalIntegral.integral_congr_Ioo_of_le hh'.le h4]
  ring


/-- A density continuous at the limiting point has the expected average on
any fixed fraction of a shrinking right interval. Only eventual integrability
on those intervals is required; global continuity is unnecessary. -/
theorem tendsto_shrinking_integral (F : ℝ × ℝ → ℝ) (t₀ A B : ℝ)
    (hA : 0 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1)
    (hF : ContinuousAt F (0, t₀))
    (hi : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (fun t => F (h, t)) volume (t₀ + A * h) (t₀ + B * h)) :
    Tendsto (fun h => (∫ t in t₀ + A * h..t₀ + B * h, F (h, t)) / h)
      (𝓝[>] 0) (𝓝 ((B - A) * F (0, t₀))) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hnear := eventually_between_mem_of_continuousAt F t₀ Metric.isOpen_ball hF
    (Metric.mem_ball_self (half_pos hε))
  filter_upwards [hnear, hi, self_mem_nhdsWithin] with h hnear hi hh
  have hpos : 0 < h := hh
  have hab : t₀ + A * h ≤ t₀ + B * h := by nlinarith
  have heq : (∫ t in t₀ + A * h..t₀ + B * h, F (h, t)) / h -
        (B - A) * F (0, t₀) =
      (∫ t in t₀ + A * h..t₀ + B * h, F (h, t) - F (0, t₀)) / h := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [Real.dist_eq, heq, ← Real.norm_eq_abs, norm_div]
  simp only [Real.norm_eq_abs, abs_of_pos hpos]
  apply lt_of_le_of_lt (b := ε / 2) _ (half_lt_self hε)
  apply (div_le_iff₀ hpos).2
  calc
    |∫ t in t₀ + A * h..t₀ + B * h, F (h, t) - F (0, t₀)| ≤
        (ε / 2) * |(t₀ + B * h) - (t₀ + A * h)| := by
      rw [← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hab] at ht
      have ht' : t ∈ Icc t₀ (t₀ + h) := by
        constructor <;> nlinarith [ht.1, ht.2]
      have hbnd := hnear t ht'
      simpa [Metric.mem_ball, dist_eq_norm] using hbnd.le
    _ ≤ (ε / 2) * h := by
      apply mul_le_mul_of_nonneg_left _ (half_pos hε).le
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      nlinarith


theorem affineDensity_shrinking_integral {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (t₀ : I.Points)
    (ht₀ : (t₀ : ℝ) ∈ Ioo I.a I.b)
    {U : Set (ℝ × State m × State m)} (hU : IsOpen U)
    (hL : ContinuousOn L.value U)
    (d : State m) (P : ℝ × ℝ → ℝ) (hP : Continuous P)
    (hPzero : P (0, (t₀ : ℝ)) = 0) (r A B : ℝ)
    (hA : 0 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1)
    (hmem : ((t₀ : ℝ), u.state t₀, u.velocity t₀ + r • d) ∈ U) :
    (∀ᶠ h in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (affineDensity L u d (fun t => P (h, t)) r) volume
      ((t₀ : ℝ) + A * h) (t₀ + B * h)) ∧
    Tendsto (fun h => (∫ t in (t₀ : ℝ) + A * h..t₀ + B * h,
      affineDensity L u d (fun t => P (h, t)) r t) / h)
      (𝓝[>] 0) (𝓝 ((B - A) * L.value ((t₀ : ℝ), u.state t₀,
        u.velocity t₀ + r • d))) := by
  have hz : ContinuousAt (stateField I m u) (t₀ : ℝ) :=
    (stateField_continuousOn I m u).continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hv : ContinuousAt (velocityField I m u) (t₀ : ℝ) :=
    (velocityField_continuousOn I m u).continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  let Q : ℝ × ℝ → ℝ × State m × State m := fun x =>
    (x.2, stateField I m u x.2 + P x • d, velocityField I m u x.2 + r • d)
  have hQ : ContinuousAt Q (0, (t₀ : ℝ)) :=
    continuousAt_snd.prodMk
      (((hz.comp (f := fun x : ℝ × ℝ => x.2) continuousAt_snd).add
        (hP.continuousAt.smul continuousAt_const)).prodMk
      ((hv.comp (f := fun x : ℝ × ℝ => x.2) continuousAt_snd).add continuousAt_const))
  have hQzero : Q (0, (t₀ : ℝ)) =
      ((t₀ : ℝ), u.state t₀, u.velocity t₀ + r • d) := by
    simp [Q, hPzero, stateField, velocityField, extendState, t₀.property.1, t₀.property.2]
  have hQmem : Q (0, (t₀ : ℝ)) ∈ U := hQzero.symm ▸ hmem
  have hnear := eventually_between_mem_of_continuousAt Q t₀ hU hQ hQmem
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < I.b - t₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr ht₀.2))
  have hQon (h : ℝ) : ContinuousOn (fun t => Q (h, t)) (Icc I.a I.b) := by
    exact continuousOn_id.prodMk
      (((stateField_continuousOn I m u).add
        ((hP.comp (continuous_const.prodMk continuous_id)).continuousOn.smul
          continuousOn_const)).prodMk
        ((velocityField_continuousOn I m u).add continuousOn_const))
  have hi : ∀ᶠ h in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (affineDensity L u d (fun t => P (h, t)) r) volume
      ((t₀ : ℝ) + A * h) (t₀ + B * h) := by
    filter_upwards [hnear, hsmall, self_mem_nhdsWithin] with h hnear hsmall hh
    have hpos : 0 < h := hh
    have hab : (t₀ : ℝ) + A * h ≤ t₀ + B * h := by nlinarith
    have hsub : Icc ((t₀ : ℝ) + A * h) (t₀ + B * h) ⊆ Icc I.a I.b := by
      intro t ht
      constructor <;> nlinarith [ht.1, ht.2, ht₀.1, ht₀.2]
    have hsub' : Icc ((t₀ : ℝ) + A * h) (t₀ + B * h) ⊆ Icc (t₀ : ℝ) (t₀ + h) := by
      intro t ht
      constructor <;> nlinarith [ht.1, ht.2]
    exact (hL.comp ((hQon h).mono hsub) (fun t ht => hnear t (hsub' ht))).intervalIntegrable_of_Icc hab
  refine ⟨hi, ?_⟩
  have hLF : ContinuousAt (fun x => L.value (Q x)) (0, (t₀ : ℝ)) :=
    (hL.continuousAt (hU.mem_nhds hQmem)).comp hQ
  have ht := tendsto_shrinking_integral (fun x => L.value (Q x)) t₀ A B hA hAB hB hLF hi
  simpa only [affineDensity, hQzero] using ht


theorem reference_density_intervalIntegrable {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m)
    (hreg : regularNearGraph L u 1) :
    IntervalIntegrable
      (fun t => L.value (t, stateField I m u t, velocityField I m u t)) volume I.a I.b := by
  obtain ⟨U, _, hu, _, hL⟩ := hreg
  have hgraph : ContinuousOn
      (fun t => (t, stateField I m u t, velocityField I m u t)) (Icc I.a I.b) :=
    continuousOn_id.prodMk ((stateField_continuousOn I m u).prodMk
      (velocityField_continuousOn I m u))
  apply (hL.continuousOn.comp hgraph ?_).intervalIntegrable_of_Icc I.increasing.le
  intro t ht
  simpa [stateField, velocityField, extendState, ht, graphPoint] using hu ⟨t, ht⟩



theorem velocityInsertionRegular.triangular_action_limit
    {I : Interval} {m : ℕ} {L : Lagrangian m} {u : C1Curve I m}
    {t₀ : I.Points} {w : State m}
    (hreg : velocityInsertionRegular L u t₀ w)
    (ht₀ : (t₀ : ℝ) ∈ Ioo I.a I.b) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Tendsto
      (fun h => (piecewiseAction L (triangularCompetitor u t₀ w s h) - action L u) / h)
      (𝓝[>] 0) (𝓝 (s * L.value ((t₀ : ℝ), u.state t₀, w) +
        (1 - s) * L.value ((t₀ : ℝ), u.state t₀,
          u.velocity t₀ - (s / (1 - s)) • (w - u.velocity t₀)) -
        L.value (graphPoint u t₀))) := by
  have hbase := reference_density_intervalIntegrable L u hreg.regularNearGraph
  obtain ⟨U, hU, _, hL, hu, δ, hδ, hseg⟩ := hreg
  have hw : ((t₀ : ℝ), u.state t₀, w) ∈ U := by
    simpa using hseg t₀ (by simpa using hδ) 1 (by simp)
  have hratio : ContinuousAt (fun s : ℝ => s / (1 - s)) 0 :=
    continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hret : ContinuousAt (fun s : ℝ =>
      ((t₀ : ℝ), u.state t₀,
        u.velocity t₀ - (s / (1 - s)) • (w - u.velocity t₀))) 0 :=
    continuousAt_const.prodMk
      (continuousAt_const.prodMk
        (continuousAt_const.sub (hratio.smul continuousAt_const)))
  have hzero : ((t₀ : ℝ), u.state t₀,
      u.velocity t₀ - ((0 : ℝ) / (1 - 0)) • (w - u.velocity t₀)) ∈ U := by
    simpa [graphPoint] using hu t₀
  have hreturn := (hret.eventually (hU.mem_nhds hzero)).filter_mono
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hspos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hslt : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hreturn, hspos, hslt] with s hreturn hspos hslt
  have hrise := affineDensity_shrinking_integral L u t₀ ht₀ hU hL.continuousOn
    (w - u.velocity t₀) (fun x => x.2 - (t₀ : ℝ))
    (continuous_snd.sub continuous_const) (by simp) 1 0 s (by norm_num)
    hspos.le hslt.le (by simpa [← add_sub_assoc, add_comm] using hw)
  have hfall := affineDensity_shrinking_integral L u t₀ ht₀ hU hL.continuousOn
    (w - u.velocity t₀) (fun x => (s / (1 - s)) * ((t₀ : ℝ) + x.1 - x.2))
    (continuous_const.mul ((continuous_const.add continuous_fst).sub continuous_snd))
    (by simp) (-(s / (1 - s))) s 1 hspos.le hslt.le le_rfl
    (by
      rw [neg_smul, ← sub_eq_add_neg]
      exact hreturn)
  have hbase' := affineDensity_shrinking_integral L u t₀ ht₀ hU hL.continuousOn
    (0 : State m) (fun _ => 0) continuous_const rfl 0 0 1 (by norm_num)
    (by norm_num) le_rfl (by simpa [graphPoint] using hu t₀)
  have hlim := (hrise.2.add hfall.2).sub hbase'.2
  have hlim' : Tendsto (fun h =>
      ((∫ t in (t₀ : ℝ)..t₀ + s * h,
        affineDensity L u (w - u.velocity t₀) (fun t => t - t₀) 1 t) +
      (∫ t in (t₀ : ℝ) + s * h..t₀ + h,
        affineDensity L u (w - u.velocity t₀)
          (fun t => (s / (1 - s)) * (t₀ + h - t)) (-(s / (1 - s))) t) -
      (∫ t in (t₀ : ℝ)..t₀ + h,
        L.value (t, stateField I m u t, velocityField I m u t))) / h)
      (𝓝[>] 0) (𝓝 (s * L.value ((t₀ : ℝ), u.state t₀, w) +
        (1 - s) * L.value ((t₀ : ℝ), u.state t₀,
          u.velocity t₀ - (s / (1 - s)) • (w - u.velocity t₀)) -
        L.value (graphPoint u t₀))) := by
    simpa only [affineDensity, zero_mul, add_zero, one_mul, sub_zero, smul_zero,
      zero_smul, one_smul, add_sub_cancel, neg_smul, ← sub_eq_add_neg,
      add_div, sub_div, graphPoint] using hlim
  apply hlim'.congr'
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < I.b - t₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr ht₀.2))
  filter_upwards [hrise.1, hfall.1, hsmall, self_mem_nhdsWithin] with h hrise hfall hsmall hh
  rw [triangular_action_decomposition L u t₀ w s h ht₀ hspos hslt hh
    (by linarith) hbase (by simpa using hrise) (by simpa using hfall)]



end Weierstrass

/-- The Weierstrass necessary condition for a strong minimum in the shared
continuous piecewise C¹ class, with regularity local to the tested velocity. -/
theorem weierstrassExcess : Specs.VariationalNotes.Classical.weierstrassExcess := by
  intro I m L xₐ xᵦ u hmin t₀ ht₀ w hreg
  apply Weierstrass.excess_nonneg_of_triangular_action_limits L xₐ xᵦ u t₀ w hmin
    hreg.regularNearGraph
  · exact hreg.eventual_triangular_admissibility ht₀ hmin.1.2.1 hmin.1.2.2
  · exact hreg.triangular_action_limit ht₀

end VariationalNotes.Classical
