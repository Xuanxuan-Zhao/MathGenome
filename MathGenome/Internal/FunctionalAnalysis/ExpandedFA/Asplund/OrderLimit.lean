import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.OrderLimit
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.Iteration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-! The primal order and limit theorem for Asplund's arithmetic and
infimal-convolution iteration. No continuity or completeness is used. -/
namespace ExpandedFA.Asplund.OrderLimit

open Iteration Set Filter
open scoped Topology

noncomputable def theta : Spec.LimitType := Spec.thetaValue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Each splitting bounds the infimal mean, without assuming attainment. -/
theorem infimalMean_le (φ ψ : E → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (hψ : ∀ x, 0 ≤ ψ x) (x y : E) :
    infimalMean E φ ψ x ≤ (φ (x + y) + ψ (x - y)) / 2 := by
  exact div_le_div_of_nonneg_right
    (csInf_le (splitting_bddBelow φ ψ hφ hψ x) (mem_range_self y)) (by norm_num)

/-- Approximate minimizing splittings suffice for convexity. -/
theorem exists_splitting_lt (φ ψ : E → ℝ) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ y, φ (x + y) + ψ (x - y) < 2 * infimalMean E φ ψ x + ε := by
  have h : sInf (range fun y => φ (x + y) + ψ (x - y)) <
      2 * infimalMean E φ ψ x + ε := by
    dsimp [infimalMean]
    linarith
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := exists_lt_of_csInf_lt (range_nonempty _) h
  exact ⟨y, hy⟩

theorem infimalMean_convex (φ ψ : E → ℝ)
    (hφ : ConvexOn ℝ univ φ) (hψ : ConvexOn ℝ univ ψ)
    (hφ₀ : ∀ x, 0 ≤ φ x) (hψ₀ : ∀ x, 0 ≤ ψ x) :
    ConvexOn ℝ univ (infimalMean E φ ψ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  change infimalMean E φ ψ (a • x + b • z) ≤
    a * infimalMean E φ ψ x + b * infimalMean E φ ψ z
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u, hu⟩ := exists_splitting_lt φ ψ x hε
  obtain ⟨v, hv⟩ := exists_splitting_lt φ ψ z hε
  have hp := hφ.2 (mem_univ (x + u)) (mem_univ (z + v)) ha hb hab
  have hq := hψ.2 (mem_univ (x - u)) (mem_univ (z - v)) ha hb hab
  have hle := infimalMean_le φ ψ hφ₀ hψ₀ (a • x + b • z) (a • u + b • v)
  have hplus : (a • x + b • z) + (a • u + b • v) =
      a • (x + u) + b • (z + v) := by module
  have hminus : (a • x + b • z) - (a • u + b • v) =
      a • (x - u) + b • (z - v) := by module
  rw [hplus, hminus] at hle
  simp only [smul_eq_mul] at hp hq
  have hau := mul_le_mul_of_nonneg_left hu.le ha
  have hbv := mul_le_mul_of_nonneg_left hv.le hb
  nlinarith

theorem arithmeticMean_convex (φ ψ : E → ℝ)
    (hφ : ConvexOn ℝ univ φ) (hψ : ConvexOn ℝ univ ψ) :
    ConvexOn ℝ univ (arithmeticMean E φ ψ) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  have hp := hφ.2 hx hz ha hb hab
  have hq := hψ.2 hx hz ha hb hab
  simp only [arithmeticMean, smul_eq_mul] at hp hq ⊢
  linarith

/-- Jensen at the midpoint gives the lower order bound for the infimal mean. -/
theorem le_infimalMean (φ ψ : E → ℝ)
    (hψ : ConvexOn ℝ univ ψ) (horder : ∀ x, ψ x ≤ φ x) (x : E) :
    ψ x ≤ infimalMean E φ ψ x := by
  unfold infimalMean
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply le_csInf (range_nonempty _)
  rintro _ ⟨y, rfl⟩
  have hj := hψ.2 (mem_univ (x + y)) (mem_univ (x - y))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hx : (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y) = x := by module
  rw [hx] at hj
  simp only [smul_eq_mul] at hj
  linarith [horder (x + y)]

theorem mean_order (φ ψ : E → ℝ) (h : InitialData E φ ψ) (x : E) :
    0 ≤ ψ x ∧ ψ x ≤ infimalMean E φ ψ x ∧
    infimalMean E φ ψ x ≤ arithmeticMean E φ ψ x ∧
    arithmeticMean E φ ψ x ≤ φ x := by
  have hφ : ∀ z, 0 ≤ φ z := fun z => (h.2.2.1 z).trans (h.2.2.2.1 z)
  refine ⟨h.2.2.1 x, le_infimalMean φ ψ h.2.1 h.2.2.2.1 x, ?_, ?_⟩
  · simpa only [add_zero, sub_zero, arithmeticMean] using
      infimalMean_le φ ψ hφ h.2.2.1 x 0
  · change (φ x + ψ x) / 2 ≤ φ x
    linarith [h.2.2.2.1 x]

theorem means_initialData (φ ψ : E → ℝ) (h : InitialData E φ ψ) :
    InitialData E (arithmeticMean E φ ψ) (infimalMean E φ ψ) := by
  have hφ : ∀ z, 0 ≤ φ z := fun z => (h.2.2.1 z).trans (h.2.2.2.1 z)
  refine ⟨arithmeticMean_convex φ ψ h.1 h.2.1,
    infimalMean_convex φ ψ h.1 h.2.1 hφ h.2.2.1,
    infimalMean_nonneg φ ψ hφ h.2.2.1,
    fun x => (mean_order φ ψ h x).2.2.1, ?_, ?_⟩
  · change (φ 0 + ψ 0) / 2 = 0
    rw [h.2.2.2.2.1, h.2.2.2.2.2]
    norm_num
  · have hle := (mean_order φ ψ h 0).2.2.1
    have hnonneg := infimalMean_nonneg φ ψ hφ h.2.2.1 (0 : E)
    dsimp [arithmeticMean] at hle
    rw [h.2.2.2.2.1, h.2.2.2.2.2] at hle
    linarith

theorem iterates_properties : Spec.IteratesProperties := by
  intro E _ _ φ₀ ψ₀ h n
  change InitialData E (phi E φ₀ ψ₀ n) (psi E φ₀ ψ₀ n)
  induction n with
  | zero => exact h
  | succ n ih =>
    exact means_initialData (phi E φ₀ ψ₀ n) (psi E φ₀ ψ₀ n) ih

theorem order_chain : Spec.OrderChain := by
  intro E _ _ φ₀ ψ₀ h n x
  exact mean_order (phi E φ₀ ψ₀ n) (psi E φ₀ ψ₀ n)
    (iterates_properties E φ₀ ψ₀ h n) x

theorem monotone_sequences : Spec.MonotoneSequences := by
  intro E _ _ φ₀ ψ₀ h x
  exact ⟨antitone_nat_of_succ_le (fun n => (order_chain E φ₀ ψ₀ h n x).2.2.2),
    monotone_nat_of_le_succ (fun n => (order_chain E φ₀ ψ₀ h n x).2.1)⟩

theorem phi_bddBelow (φ₀ ψ₀ : E → ℝ) (h : InitialData E φ₀ ψ₀) (x : E) :
    BddBelow (range fun n => phi E φ₀ ψ₀ n x) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hn := iterates_properties E φ₀ ψ₀ h n
  exact (hn.2.2.1 x).trans (hn.2.2.2.1 x)

theorem phi_tendsto (φ₀ ψ₀ : E → ℝ) (h : InitialData E φ₀ ψ₀) (x : E) :
    Tendsto (fun n => phi E φ₀ ψ₀ n x) atTop (𝓝 (theta E φ₀ ψ₀ x)) := by
  exact tendsto_atTop_isGLB (monotone_sequences E φ₀ ψ₀ h x).1
    (isGLB_csInf (range_nonempty _) (phi_bddBelow φ₀ ψ₀ h x))

/-- The arithmetic recurrence determines the second limit directly:
ψₙ = 2φₙ₊₁ − φₙ. -/
theorem psi_tendsto (φ₀ ψ₀ : E → ℝ) (h : InitialData E φ₀ ψ₀) (x : E) :
    Tendsto (fun n => psi E φ₀ ψ₀ n x) atTop (𝓝 (theta E φ₀ ψ₀ x)) := by
  have hp := phi_tendsto φ₀ ψ₀ h x
  have hs := (tendsto_add_atTop_iff_nat 1).2 hp
  have hl := (hs.const_mul 2).sub hp
  have heq : (fun n => psi E φ₀ ψ₀ n x) =
      (fun n => 2 * phi E φ₀ ψ₀ (n + 1) x - phi E φ₀ ψ₀ n x) := by
    funext n
    rw [phi_succ]
    ring
  rw [heq]
  have hv : 2 * theta E φ₀ ψ₀ x - theta E φ₀ ψ₀ x = theta E φ₀ ψ₀ x := by ring
  rw [hv] at hl
  exact hl

theorem theta_bounds (φ₀ ψ₀ : E → ℝ) (h : InitialData E φ₀ ψ₀) (n : ℕ) (x : E) :
    psi E φ₀ ψ₀ n x ≤ theta E φ₀ ψ₀ x ∧
    theta E φ₀ ψ₀ x ≤ phi E φ₀ ψ₀ n x := by
  exact ⟨(monotone_sequences E φ₀ ψ₀ h x).2.ge_of_tendsto
      (psi_tendsto φ₀ ψ₀ h x) n,
    csInf_le (phi_bddBelow φ₀ ψ₀ h x) (mem_range_self n)⟩

theorem theta_convex (φ₀ ψ₀ : E → ℝ) (h : InitialData E φ₀ ψ₀) :
    ConvexOn ℝ univ (theta E φ₀ ψ₀) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  change theta E φ₀ ψ₀ (a • x + b • z) ≤ a * theta E φ₀ ψ₀ x + b * theta E φ₀ ψ₀ z
  apply le_of_tendsto_of_tendsto' (phi_tendsto φ₀ ψ₀ h (a • x + b • z))
    (((phi_tendsto φ₀ ψ₀ h x).const_mul a).add ((phi_tendsto φ₀ ψ₀ h z).const_mul b))
  intro n
  exact (iterates_properties E φ₀ ψ₀ h n).1.2 hx hz ha hb hab

theorem common_limit : Spec.CommonLimit := by
  intro E _ _ φ₀ ψ₀ h
  refine ⟨theta_convex φ₀ ψ₀ h, ?_, ?_, theta_bounds φ₀ ψ₀ h, ?_⟩
  · have hb := theta_bounds φ₀ ψ₀ h 0 0
    change ψ₀ 0 ≤ theta E φ₀ ψ₀ 0 ∧ theta E φ₀ ψ₀ 0 ≤ φ₀ 0 at hb
    rw [h.2.2.2.2.1, h.2.2.2.2.2] at hb
    exact le_antisymm hb.2 hb.1
  · intro x
    exact (h.2.2.1 x).trans (theta_bounds φ₀ ψ₀ h 0 x).1
  · intro x
    exact ⟨phi_tendsto φ₀ ψ₀ h x, psi_tendsto φ₀ ψ₀ h x⟩

end ExpandedFA.Asplund.OrderLimit
