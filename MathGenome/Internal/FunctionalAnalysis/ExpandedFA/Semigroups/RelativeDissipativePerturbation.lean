import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.RelativeDissipativePerturbation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LumerPhillips

noncomputable section
namespace ExpandedFA.Semigroups.RelativeDissipativePerturbation
open LumerPhillipsSpec

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- The squared Hilbert estimate controls AR by one, rather than the
Banach-space triangle estimate by two. -/
theorem resolvent_generator_bound (A : Unbounded.Operator 𝕜 H H)
    (hd : Dissipative A) (r : ℝ) (hr : 0 < r)
    (R : Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r)) (y : H) :
    ‖A ⟨R.inverse y, R.mem_domain y⟩‖ ≤ ‖y‖ := by
  let x : A.domain := ⟨R.inverse y, R.mem_domain y⟩
  have hx := (LumerPhillips.hilbert_dissipative_iff A).mp hd x
  have heq := LumerPhillips.shift_norm_sq A r hr x
  have hi : shiftMap A r x = y := R.right_inverse y
  rw [hi] at heq
  have hprod : 2 * r * RCLike.re (inner 𝕜 (x : H) (A x)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hx
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg r, sq_nonneg ‖(x : H)‖]

/-- The Hilbert form criterion is additive on the intersection domain. -/
theorem dissipative_add (A B : Unbounded.Operator 𝕜 H H)
    (hA : Dissipative A) (hB : Dissipative B) : Dissipative (A + B) := by
  apply (LumerPhillips.hilbert_dissipative_iff (A + B)).mpr
  intro x
  have h₁ := (LumerPhillips.hilbert_dissipative_iff A).mp hA ⟨x, x.2.1⟩
  have h₂ := (LumerPhillips.hilbert_dissipative_iff B).mp hB ⟨x, x.2.2⟩
  change RCLike.re (inner 𝕜 (x : H) (A ⟨x, x.2.1⟩ + B ⟨x, x.2.2⟩)) ≤ 0
  rw [inner_add_right, map_add]
  exact add_nonpos h₁ h₂

variable [CompleteSpace H]

/-- A Neumann series supplies a positive full-range point for the sum. -/
theorem fullRange_add (A B : Unbounded.Operator 𝕜 H H)
    (hA : Dissipative A) (hs : ∃ r : ℝ, 0 < r ∧ FullRange A r)
    (hAB : A.domain ≤ B.domain) (a b : ℝ) (ha₀ : 0 ≤ a) (ha : a < 1)
    (hb : 0 ≤ b)
    (hbound : ∀ x : A.domain, ‖B ⟨x, hAB x.2⟩‖ ≤ a * ‖A x‖ + b * ‖(x : H)‖) :
    ∃ r : ℝ, 0 < r ∧ FullRange (A + B) r := by
  let r : ℝ := (b + 1) / (1 - a)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrid : r * (1 - a) = b + 1 := by
    dsimp [r]
    exact div_mul_cancel₀ _ (by linarith)
  have hq : a + b / r < 1 := by
    have h : b / r < 1 - a := (div_lt_iff₀ hr).mpr (by nlinarith [hrid])
    linarith
  let R := LumerPhillips.inverseAt A hA r hr (LumerPhillips.fullRange_all A hA hs r hr)
  let f : H →ₗ[𝕜] H := B.toFun.comp ((Submodule.inclusion hAB).comp R.graphLinear)
  have hf (y : H) : ‖f y‖ ≤ (a + b / r) * ‖y‖ := by
    have hx := hbound ⟨R.inverse y, R.mem_domain y⟩
    have hAR := resolvent_generator_bound A hA r hr R y
    have hR : ‖R.inverse y‖ ≤ (1 / r) * ‖y‖ :=
      (R.inverse.le_opNorm y).trans (mul_le_mul_of_nonneg_right
        (LumerPhillips.inverse_norm_le A hA r hr R) (norm_nonneg y))
    change ‖B ⟨R.inverse y, hAB (R.mem_domain y)⟩‖ ≤ _
    calc
      _ ≤ a * ‖A ⟨R.inverse y, R.mem_domain y⟩‖ + b * ‖R.inverse y‖ := hx
      _ ≤ a * ‖y‖ + b * ((1 / r) * ‖y‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hAR ha₀) (mul_le_mul_of_nonneg_left hR hb)
      _ = (a + b / r) * ‖y‖ := by ring
  let C : H →L[𝕜] H := f.mkContinuous (a + b / r) hf
  have hC : ‖C‖ < 1 :=
    (C.opNorm_le_bound (by positivity) hf).trans_lt hq
  have hu : IsUnit (1 - C) := isUnit_one_sub_of_norm_lt_one hC
  have hsur := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2
  refine ⟨r, hr, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := hsur y
  let x : (A + B).domain := ⟨R.inverse z, R.mem_domain z, hAB (R.mem_domain z)⟩
  refine ⟨x, ?_⟩
  have he : shiftMap (A + B) r x = (1 - C) z := by
    change algebraMap ℝ 𝕜 r • R.inverse z -
      (A ⟨R.inverse z, R.mem_domain z⟩ + B ⟨R.inverse z, hAB (R.mem_domain z)⟩) =
      z - B ⟨R.inverse z, hAB (R.mem_domain z)⟩
    calc
      _ = (algebraMap ℝ 𝕜 r • R.inverse z - A ⟨R.inverse z, R.mem_domain z⟩) -
          B ⟨R.inverse z, hAB (R.mem_domain z)⟩ := by abel
      _ = _ := by rw [R.right_inverse z]
  exact he.trans hz

/-- Relative dissipative perturbations preserve contraction generation with
full equality of the generator, including its domain. -/
theorem perturbation : RelativeDissipativePerturbationSpec.PerturbationExpected := by
  intro 𝕜 H _ _ _ _ A B hgen hB hAB a b ha hbound
  obtain ⟨T, hT, hcontract⟩ := hgen
  have hdense : Dense (A.domain : Set H) := by
    rw [← hT]
    exact T.generator_domain_dense
  obtain ⟨hA, hs⟩ := (LumerPhillips.characterization A hdense).mp ⟨T, hT, hcontract⟩
  have hsum := dissipative_add A B hA hB
  have hsumbound : ∀ x : A.domain,
      ‖B ⟨x, hAB x.2⟩‖ ≤ max a 0 * ‖A x‖ + max b 0 * ‖(x : H)‖ := by
    intro x
    exact (hbound x).trans (add_le_add
      (mul_le_mul_of_nonneg_right (le_max_left a 0) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (le_max_left b 0) (norm_nonneg _)))
  have hsrange := fullRange_add A B hA hs hAB (max a 0) (max b 0)
    (le_max_right _ _) (max_lt ha zero_lt_one) (le_max_right _ _) hsumbound
  have hdom : (A + B).domain = A.domain := by
    exact inf_eq_left.mpr hAB
  refine ⟨hdom, (LumerPhillips.maximal_consequences (A + B) hsum hsrange).1, ?_⟩
  apply (LumerPhillips.characterization (A + B) (by rwa [hdom])).mpr
  exact ⟨hsum, hsrange⟩

end ExpandedFA.Semigroups.RelativeDissipativePerturbation
