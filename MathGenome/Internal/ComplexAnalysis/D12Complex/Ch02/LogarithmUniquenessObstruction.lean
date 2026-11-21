import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.LogarithmUniquenessObstruction
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.Exponential
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
Continuous logarithm uniqueness and the circle endpoint obstruction.
We normalize the difference by 2πi, obtaining a continuous map into the
discrete subset of complex integers. Preconnectedness makes it constant,
including on the empty space. The obstruction compares a hypothetical
logarithm along exp(it) with it at t = 0 and t = 2π.
-/

noncomputable section

namespace D12Complex.LogarithmUniquenessObstruction

/-- Continuous lifts of the same exponential differ by a constant period,
on any preconnected topological space, including the empty space. -/
theorem continuous_exp_lifts_difference {A : Type*} [TopologicalSpace A]
    [PreconnectedSpace A] (L₁ L₂ : A → ℂ)
    (h₁ : Continuous L₁) (h₂ : Continuous L₂)
    (hE : ∀ x, E (L₁ x) = E (L₂ x)) :
    ∃ k : ℤ, ∀ x, L₁ x - L₂ x = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ) := by
  let p : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  let g : A → ℂ := fun x => (L₁ x - L₂ x) / p
  have hg : Continuous g := (h₁.sub h₂).div_const p
  have hm : Set.MapsTo g Set.univ (Set.range ((↑) : ℤ → ℂ)) := by
    intro x _
    obtain ⟨k, hk⟩ := Exponential.E_eq_E_iff (L₁ x) (L₂ x) |>.mp (hE x)
    refine ⟨k, ?_⟩
    dsimp [g]
    rw [hk]
    change (k : ℂ) = p * (k : ℂ) / p
    exact (mul_div_cancel_left₀ (k : ℂ) hp).symm
  have hd : IsDiscrete (Set.range ((↑) : ℤ → ℂ)) :=
    Complex.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
  obtain ⟨c, ⟨k, rfl⟩, hc⟩ := isPreconnected_univ.eqOn_const_of_mapsTo
    hd hg.continuousOn hm ⟨0, ⟨0, by simp⟩⟩
  refine ⟨k, fun x => ?_⟩
  have hx : g x = (k : ℂ) := hc (Set.mem_univ x)
  exact (div_eq_iff hp).mp hx |>.trans (mul_comm _ _)

theorem continuous_logarithms_difference :
    Specs.D12Complex.Ch02.LogarithmUniquenessObstruction.continuous_logarithms_difference_type := by
  intro X hX f L₁ L₂ _hf h₁ h₂ hE₁ hE₂
  let : PreconnectedSpace X := isPreconnected_iff_preconnectedSpace.mp hX
  exact continuous_exp_lifts_difference L₁ L₂ h₁ h₂ (fun x => (hE₁ x).trans (hE₂ x).symm)

theorem no_continuous_logarithm :
    Specs.D12Complex.Ch02.LogarithmUniquenessObstruction.no_continuous_logarithm_type := by
  rintro ⟨L, hL, hEL⟩
  let circle : ℝ → {z : ℂ // z ≠ 0} := fun t =>
    ⟨Complex.exp ((t : ℂ) * Complex.I), Complex.exp_ne_zero _⟩
  have hc : Continuous circle :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const Complex.I)).subtype_mk _
  have ht : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.mul_const Complex.I
  obtain ⟨k, hk⟩ := continuous_exp_lifts_difference (L ∘ circle)
    (fun t : ℝ => (t : ℂ) * Complex.I) (hL.comp hc) ht (by
      intro t
      change E (L (circle t)) = E ((t : ℂ) * Complex.I)
      rw [hEL (circle t), Exponential.E_eq_exp])
  have hend : circle (2 * Real.pi) = circle 0 := by
    apply Subtype.ext
    simp [circle, Complex.ofReal_mul, Complex.exp_two_pi_mul_I]
  have hzero := hk 0
  have hfull := hk (2 * Real.pi)
  simp only [Function.comp_apply] at hzero hfull
  rw [hend] at hfull
  simp only [Complex.ofReal_zero, zero_mul, sub_zero] at hzero
  have hperiod : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 0 := by
    exact sub_eq_self.mp (hfull.trans hzero.symm)
  have him := congrArg Complex.im hperiod
  simp at him

end D12Complex.LogarithmUniquenessObstruction
