import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.FactorFourRate
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.OrderLimit
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.QuadraticSeminorms

/-! Quadratic homogeneity and the factor-four comparison for the arithmetic /
infimal-convolution iteration. All infima below are genuine greatest lower
bounds of nonempty sets bounded below; minimizing splittings are not assumed. -/
namespace ExpandedFA.Asplund.FactorFourRate

open Iteration OrderLimit Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scaling the splitting by a nonzero scalar gives one side of homogeneity. -/
theorem scaled_infimalMean_le (φ ψ : E → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (hψ : ∀ x, 0 ≤ ψ x)
    (hφh : ∀ (a : ℝ) (x : E), φ (a • x) = a ^ 2 * φ x)
    (hψh : ∀ (a : ℝ) (x : E), ψ (a • x) = a ^ 2 * ψ x)
    (a : ℝ) (ha : a ≠ 0) (x : E) :
    a ^ 2 * infimalMean E φ ψ x ≤ infimalMean E φ ψ (a • x) := by
  change a ^ 2 * infimalMean E φ ψ x ≤
    sInf (range fun y => φ (a • x + y) + ψ (a • x - y)) / 2
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply le_csInf (range_nonempty _)
  rintro _ ⟨y, rfl⟩
  dsimp only
  have h := infimalMean_le φ ψ hφ hψ x (a⁻¹ • y)
  have hp : φ (a • x + y) = a ^ 2 * φ (x + a⁻¹ • y) := by
    rw [← hφh a]
    congr 1
    simp [smul_add, smul_smul, ha]
  have hq : ψ (a • x - y) = a ^ 2 * ψ (x - a⁻¹ • y) := by
    rw [← hψh a]
    congr 1
    simp [smul_sub, smul_smul, ha]
  rw [hp, hq]
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg a)]

theorem infimalMean_homogeneous (φ ψ : E → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (hψ : ∀ x, 0 ≤ ψ x)
    (hφh : ∀ (a : ℝ) (x : E), φ (a • x) = a ^ 2 * φ x)
    (hψh : ∀ (a : ℝ) (x : E), ψ (a • x) = a ^ 2 * ψ x)
    (a : ℝ) (x : E) :
    infimalMean E φ ψ (a • x) = a ^ 2 * infimalMean E φ ψ x := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul]
    apply le_antisymm _ (infimalMean_nonneg φ ψ hφ hψ 0)
    have h := infimalMean_le φ ψ hφ hψ (0 : E) 0
    have hp := hφh 0 (0 : E)
    have hq := hψh 0 (0 : E)
    simp only [zero_smul, zero_pow (by decide : 2 ≠ 0), zero_mul] at hp hq
    simpa [hp, hq] using h
  · apply le_antisymm _ (scaled_infimalMean_le φ ψ hφ hψ hφh hψh a ha x)
    have h := scaled_infimalMean_le φ ψ hφ hψ hφh hψh a⁻¹
      (inv_ne_zero ha) (a • x)
    simp only [smul_smul, inv_mul_cancel₀ ha, one_smul] at h
    have hs : a ^ 2 * (a⁻¹) ^ 2 = 1 := by field_simp
    have h' := mul_le_mul_of_nonneg_left h (sq_nonneg a)
    simpa only [← mul_assoc, hs, one_mul] using h'

theorem iterates_homogeneous : Spec.IteratesHomogeneous := by
  intro E _ _ φ₀ ψ₀ h hφh hψh n
  change (∀ a x, phi E φ₀ ψ₀ n (a • x) = a ^ 2 * phi E φ₀ ψ₀ n x) ∧
    (∀ a x, psi E φ₀ ψ₀ n (a • x) = a ^ 2 * psi E φ₀ ψ₀ n x)
  induction n with
  | zero => exact ⟨hφh, hψh⟩
  | succ n ih =>
    have hn := iterates_properties E φ₀ ψ₀ h n
    constructor
    · intro a x
      rw [phi_succ, phi_succ, ih.1, ih.2]
      ring
    · exact infimalMean_homogeneous _ _
        (fun x => (hn.2.2.1 x).trans (hn.2.2.2.1 x)) hn.2.2.1 ih.1 ih.2

theorem theta_homogeneous : Spec.ThetaHomogeneous := by
  intro E _ _ φ₀ ψ₀ h hφh hψh a x
  change theta E φ₀ ψ₀ (a • x) = a ^ 2 * theta E φ₀ ψ₀ x
  apply tendsto_nhds_unique (phi_tendsto φ₀ ψ₀ h (a • x))
  have ht := (phi_tendsto φ₀ ψ₀ h x).const_mul (a ^ 2)
  convert ht using 1
  funext n
  exact (iterates_homogeneous E φ₀ ψ₀ h hφh hψh n).1 a x

/-- The weighted quadratic inequality provides the second lower bound for
the new infimal mean, in addition to its lower bound by `ψ`. -/
theorem two_mul_le_scaled_infimalMean (φ ψ : E → ℝ)
    (h : InitialData E φ ψ)
    (hφh : ∀ (b : ℝ) (x : E), φ (b • x) = b ^ 2 * φ x)
    (a : ℝ) (ha : 1 ≤ a) (hcomp : ∀ x, φ x ≤ a * ψ x) (x : E) :
    2 * φ x ≤ (a + 1) * infimalMean E φ ψ x := by
  have hapos : 0 < a := by linarith
  have hap : 0 < a + 1 := by linarith
  have ht : 0 < 1 / (a + 1) := div_pos (by norm_num) hap
  have ht1 : 1 / (a + 1) < 1 := (div_lt_one hap).2 (by linarith)
  have hquad : QuadraticSeminormsSpec.NonnegativeQuadraticConvex φ :=
    ⟨fun z => (h.2.2.1 z).trans (h.2.2.2.1 z), h.1, hφh⟩
  have hbound : 4 * φ x / (a + 1) ≤
      sInf (range fun y => φ (x + y) + ψ (x - y)) := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨y, rfl⟩
    dsimp only
    have hw := quadratic_weighted_difference hquad x y ht ht1
    have heq : φ (x + y) / (1 / (a + 1)) + φ (x - y) / (1 - 1 / (a + 1)) =
        (a + 1) * φ (x + y) + ((a + 1) / a) * φ (x - y) := by
      field_simp [hapos.ne', hap.ne']
      ring
    rw [heq] at hw
    have hc := mul_le_mul_of_nonneg_left (hcomp (x - y))
      (div_nonneg hap.le hapos.le)
    have hcancel : (a + 1) / a * (a * ψ (x - y)) = (a + 1) * ψ (x - y) := by
      field_simp
    rw [hcancel] at hc
    apply (div_le_iff₀ hap).2
    nlinarith
  have hb := (div_le_iff₀ hap).1 hbound
  dsimp [infimalMean]
  nlinarith

/-- One iteration replaces a comparison constant `a` by `(a+3)/4`. -/
theorem factor_four_step (φ ψ : E → ℝ) (h : InitialData E φ ψ)
    (hφh : ∀ (b : ℝ) (x : E), φ (b • x) = b ^ 2 * φ x)
    (a : ℝ) (ha : 1 ≤ a) (hcomp : ∀ x, φ x ≤ a * ψ x) (x : E) :
    arithmeticMean E φ ψ x ≤ ((a + 3) / 4) * infimalMean E φ ψ x := by
  have hp := two_mul_le_scaled_infimalMean φ ψ h hφh a ha hcomp x
  have hq := le_infimalMean φ ψ h.2.1 h.2.2.2.1 x
  change (φ x + ψ x) / 2 ≤ ((a + 3) / 4) * infimalMean E φ ψ x
  nlinarith

theorem factor_four_bound : Spec.FactorFourBound := by
  intro E _ _ φ₀ ψ₀ h hφh hψh C hC hcomp n
  change ∀ x, phi E φ₀ ψ₀ n x ≤ (1 + C / (4 : ℝ) ^ n) * psi E φ₀ ψ₀ n x
  induction n with
  | zero => simpa using hcomp
  | succ n ih =>
    intro x
    have hn := iterates_properties E φ₀ ψ₀ h n
    have hhom := (iterates_homogeneous E φ₀ ψ₀ h hφh hψh n).1
    have ha : 1 ≤ 1 + C / (4 : ℝ) ^ n := by
      have hd : 0 ≤ C / (4 : ℝ) ^ n := by positivity
      linarith
    have hstep := factor_four_step _ _ hn hhom (1 + C / (4 : ℝ) ^ n) ha ih x
    have heq : ((1 + C / (4 : ℝ) ^ n) + 3) / 4 = 1 + C / (4 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      field_simp
      ring
    rw [heq] at hstep
    exact hstep

end ExpandedFA.Asplund.FactorFourRate
