import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.AbsolutelyContinuousContours
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.RectifiableStieltjes
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcFtc
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace D12Complex.Stieltjes

theorem ac_derivative :
    Specs.D12Complex.Ch03.AbsolutelyContinuousContours.ac_derivative_type := by
  intro a b hab γ hγ
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨by simp, ?_, ?_⟩
    · filter_upwards [] with t ht
      exact (not_lt_of_ge ht.1.le ht.2).elim
    · intro x hx
      have hx' : x = a := le_antisymm hx.2 hx.1
      subst x
      simp
  · have h := (D11.Ch12.AcFtc.ftc_complex γ hab).2.1.mp
        ((D11.Ch12.AcBasic.library_iff hab.le).mpr hγ)
    exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr h.2.1,
      h.1, h.2.2⟩

theorem ac_finite_variation :
    Specs.D12Complex.Ch03.AbsolutelyContinuousContours.ac_finite_variation_type := by
  intro a b hab γ hγ
  rw [totalVariation_eq_eVariationOn γ hab]
  exact lt_top_iff_ne_top.mpr (by simpa [uIcc_of_le hab, BoundedVariationOn] using hγ.boundedVariationOn)

/-- Estimate each cell using its actual primitive increment. No differentiability
of u is required, and the density may be any integrable representative. -/
theorem taggedSum_integral_error {a b : ℝ} (hab : a ≤ b)
    (u γ v : ℝ → ℂ) (hu : ContinuousOn u (Icc a b))
    (hv : IntervalIntegrable v volume a b)
    (hγ : ∀ x ∈ Icc a b, γ x = γ a + ∫ t in a..x, v t)
    (P : Partition a b) (tags : Tags P) {η : ℝ}
    (hosc : ∀ i : Fin P.n, ∀ x ∈ Icc (P.point i.castSucc) (P.point i.succ),
      ‖u (tags i) - u x‖ ≤ η) :
    ‖taggedSum P tags u γ - ∫ t in a..b, u t * v t‖ ≤
      η * ∫ t in a..b, ‖v t‖ := by
  have hmem (i : Fin (P.n + 1)) : P.point i ∈ Icc a b := by
    constructor
    · simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i)
    · simpa only [P.last] using P.strictMono.monotone (Fin.le_last i)
  have hle (i : Fin P.n) : P.point i.castSucc ≤ P.point i.succ :=
    P.strictMono.monotone (Fin.castSucc_le_succ i)
  have hsub (i : Fin P.n) : Icc (P.point i.castSucc) (P.point i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hmem i.castSucc).1 (hmem i.succ).2
  have hvcell (i : Fin P.n) :
      IntervalIntegrable v volume (P.point i.castSucc) (P.point i.succ) :=
    hv.mono_set (by simpa only [uIcc_of_le hab, uIcc_of_le (hle i)] using hsub i)
  have huv : IntervalIntegrable (fun t => u t * v t) volume a b :=
    hv.continuousOn_mul (by simpa only [uIcc_of_le hab] using hu)
  have huvcell (i : Fin P.n) : IntervalIntegrable (fun t => u t * v t) volume
      (P.point i.castSucc) (P.point i.succ) :=
    huv.mono_set (by simpa only [uIcc_of_le hab, uIcc_of_le (hle i)] using hsub i)
  have hvstart (i : Fin (P.n + 1)) : IntervalIntegrable v volume a (P.point i) := by
    apply hv.mono_set
    rw [uIcc_of_le hab, uIcc_of_le (hmem i).1]
    exact Icc_subset_Icc le_rfl (hmem i).2
  have hinc (i : Fin P.n) : γ (P.point i.succ) - γ (P.point i.castSucc) =
      ∫ t in P.point i.castSucc..P.point i.succ, v t := by
    rw [hγ _ (hmem i.succ), hγ _ (hmem i.castSucc), add_sub_add_left_eq_sub]
    exact intervalIntegral.integral_interval_sub_left (hvstart i.succ) (hvstart i.castSucc)
  have hsum := (D12Complex.intervalIntegral_fin_partition P.point _ huvcell).2
  have hnormsum := (D12Complex.intervalIntegral_fin_partition P.point _
      (fun i => (hvcell i).norm)).2
  rw [P.first, P.last] at hsum hnormsum
  rw [taggedSum, ← hsum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin P.n, ‖u (tags i) * (γ (P.point i.succ) - γ (P.point i.castSucc)) -
        ∫ t in P.point i.castSucc..P.point i.succ, u t * v t‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin P.n, η * ∫ t in P.point i.castSucc..P.point i.succ, ‖v t‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [hinc, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
        ((hvcell i).const_mul _) (huvcell i)]
      simp_rw [← sub_mul]
      calc
        _ ≤ ∫ t in P.point i.castSucc..P.point i.succ, η * ‖v t‖ := by
          apply intervalIntegral.norm_integral_le_of_norm_le (hle i)
          · filter_upwards [] with t ht
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hosc i t (Ioc_subset_Icc_self ht)) (norm_nonneg _)
          · exact (hvcell i).norm.const_mul η
        _ = _ := intervalIntegral.integral_const_mul ..
    _ = _ := by rw [← Finset.mul_sum, hnormsum]

theorem hasIntegral_ac :
    Specs.D12Complex.Ch03.AbsolutelyContinuousContours.hasIntegral_ac_type := by
  intro a b hab u γ hu hγ
  obtain ⟨hv, _, hr⟩ := ac_derivative hab γ hγ
  intro ε hε
  let M : ℝ := ∫ t in a..b, ‖deriv γ t‖
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)
  let η : ℝ := ε / (M + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hosc⟩ := SingleVariableAnalysis.Stieltjes.continuous_cell_oscillation u hu hη
  refine ⟨δ, hδ, fun P hP tags => ?_⟩
  have he := taggedSum_integral_error hab u γ (deriv γ) hu hv hr P tags
    (fun i x hx => hosc P hP i (tags i) (tags i).property x hx)
  have hmul : η * M < ε := by
    have heq : η * (M + 1) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  exact he.trans_lt hmul

theorem integral_ac :
    Specs.D12Complex.Ch03.AbsolutelyContinuousContours.integral_ac_type := by
  intro a b hab u γ hu hγ
  exact ⟨(ac_derivative hab γ hγ).1.continuousOn_mul
      (by simpa only [uIcc_of_le hab] using hu),
    integral_eq_of_hasIntegral hab (hasIntegral_ac hab u γ hu hγ)⟩

end D12Complex.Stieltjes

namespace D12Complex

/-- A common Lipschitz constant on adjacent closed intervals works on their union. -/
private theorem lipschitzOnWith_adjacent {f : ℝ → ℂ} {a c b : ℝ} {K : ℝ≥0}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hl : LipschitzOnWith K f (Icc a c)) (hr : LipschitzOnWith K f (Icc c b)) :
    LipschitzOnWith K f (Icc a b) := by
  have ordered (x : ℝ) (hx : x ∈ Icc a b) (y : ℝ) (hy : y ∈ Icc a b)
      (hxy : x ≤ y) : dist (f x) (f y) ≤ K * dist x y := by
    by_cases hyc : y ≤ c
    · exact hl.dist_le_mul x ⟨hx.1, hxy.trans hyc⟩ y ⟨hy.1, hyc⟩
    by_cases hcx : c ≤ x
    · exact hr.dist_le_mul x ⟨hcx, hx.2⟩ y ⟨hcx.trans hxy, hy.2⟩
    have hxc : x ≤ c := le_of_not_ge hcx
    have hcy : c ≤ y := le_of_not_ge hyc
    calc
      dist (f x) (f y) ≤ dist (f x) (f c) + dist (f c) (f y) := dist_triangle ..
      _ ≤ K * dist x c + K * dist c y := add_le_add
        (hl.dist_le_mul x ⟨hx.1, hxc⟩ c ⟨hac, le_rfl⟩)
        (hr.dist_le_mul c ⟨le_rfl, hcb⟩ y ⟨hcy, hy.2⟩)
      _ = K * dist x y := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hxc), abs_of_nonpos (sub_nonpos.mpr hcy),
          abs_of_nonpos (sub_nonpos.mpr hxy)]
        ring
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact ordered x hx y hy hxy
  · simpa only [dist_comm] using ordered y hy x hx hyx

/-- Finitely many closed C1 pieces give one finite Lipschitz constant. -/
theorem lipschitzOnWith_of_finite_C1 (f : ℝ → ℂ) :
    ∀ (n : ℕ) (node : Fin (n + 1) → ℝ), Monotone node →
      (∀ i : Fin n, ContDiffOn ℝ 1 f (Icc (node i.castSucc) (node i.succ))) →
      ∃ K : ℝ≥0, LipschitzOnWith K f (Icc (node 0) (node (Fin.last n))) := by
  intro n
  induction n with
  | zero =>
    intro node _ _
    refine ⟨0, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    have hx' : x = node 0 := le_antisymm hx.2 hx.1
    have hy' : y = node 0 := le_antisymm hy.2 hy.1
    simp [hx', hy']
  | succ n ih =>
    intro node hm hs
    obtain ⟨K, hK⟩ := (hs 0).exists_lipschitzOnWith (by decide)
      (convex_Icc _ _) isCompact_Icc
    obtain ⟨L, hL⟩ := ih (fun i => node i.succ)
      (fun _ _ h => hm (by simpa using h))
      (fun i => by simpa only [Fin.succ_castSucc] using hs i.succ)
    refine ⟨K + L, lipschitzOnWith_adjacent (c := node (Fin.succ 0))
      (hm (Fin.zero_le _)) (hm (Fin.le_last _)) ?_ ?_⟩
    · exact hK.weaken (le_add_of_nonneg_right (show 0 ≤ L from zero_le))
    · exact hL.weaken (le_add_of_nonneg_left (show 0 ≤ K from zero_le))

theorem piecewiseC1_ac :
    Specs.D12Complex.Ch03.AbsolutelyContinuousContours.piecewiseC1_ac_type := by
  intro γ ⟨P⟩
  obtain ⟨K, hK⟩ := lipschitzOnWith_of_finite_C1 γ P.count P.node P.strictMono.monotone P.smooth
  rw [P.first, P.last] at hK
  exact (show LipschitzOnWith K γ (uIcc γ.a γ.b) by
    simpa only [uIcc_of_le γ.ordered] using hK).absolutelyContinuousOnInterval

namespace Stieltjes

theorem contourIntegral_ac :
    Specs.D12Complex.Ch03.AbsolutelyContinuousContours.contourIntegral_ac_type := by
  intro γ hγ f hf
  refine ⟨ac_finite_variation γ.ordered γ hγ, ?_⟩
  exact (integral_ac γ.ordered (f ∘ γ) γ
    (hf.comp γ.continuousOn (fun t ht => ⟨t, ht, rfl⟩)) hγ).2

theorem contourIntegral_piecewiseC1 :
    Specs.D12Complex.Ch03.AbsolutelyContinuousContours.contourIntegral_piecewiseC1_type := by
  intro γ f hf
  obtain ⟨hr, heq⟩ := contourIntegral_ac γ.path (piecewiseC1_ac γ.path γ.property) f hf
  refine ⟨hr, heq.trans ?_⟩
  exact (C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hf).symm

end Stieltjes
end D12Complex
