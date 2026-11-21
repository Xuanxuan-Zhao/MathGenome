import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Abel
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.AccumulationParts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.MonotoneLimits
import Mathlib.Analysis.Complex.RealDeriv

namespace SingleVariableAnalysis.Riemann
open Set
open scoped BigOperators

/-- The Darboux integral of the absolute derivative of a monotone C¹ function
is its endpoint variation. The mean-value tags are used only for real g. -/
theorem integral_abs_derivative {g g' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hgp : ContinuousOn g' (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hm : MonotoneOn g (Icc a b) ∨ AntitoneOn g (Icc a b)) :
    ∃ h : RealIntegrable (fun x => |g' x|) a b,
      realIntegral _ h = |g b - g a| := by
  let hi := realIntegrable_of_continuousOn hab hgp.abs
  refine ⟨hi, ?_⟩
  have hsum (P : Partition a b) : ∃ ξ : Tagging P,
      taggedSum P ξ (fun x => |g' x|) = |g b - g a| := by
    have hcell (i : Fin P.n) : ∃ c ∈ Ioo (P.point i.castSucc) (P.point i.succ),
        g (P.point i.succ) - g (P.point i.castSucc) = g' c * cellLength P i := by
      obtain ⟨c, hc, he⟩ := SingleVariableAnalysis.lagrange_deriv g
        (P.point i.castSucc) (P.point i.succ)
        (P.strictMono (Fin.castSucc_lt_succ (i := i)))
        (hg.mono (Icc_subset_Icc (partition_point_mem P _).1 (partition_point_mem P _).2))
        (fun x hx => (hd x ⟨(partition_point_mem P _).1.trans_lt hx.1,
          hx.2.trans_le (partition_point_mem P _).2⟩).differentiableAt)
      rw [(hd c ⟨(partition_point_mem P _).1.trans_lt hc.1,
        hc.2.trans_le (partition_point_mem P _).2⟩).deriv] at he
      exact ⟨c, hc, he⟩
    choose c hc he using hcell
    let ξ : Tagging P := fun i => ⟨c i, (hc i).1.le, (hc i).2.le⟩
    have hi (i : Fin P.n) : cellLength P i * |g' (ξ i)| =
        |g (P.point i.succ) - g (P.point i.castSucc)| := by
      rw [he i, abs_mul, abs_of_pos (cell_positive P i), mul_comm]
    refine ⟨ξ, ?_⟩
    change (∑ i : Fin P.n, cellLength P i * |g' (ξ i)|) = _
    simp_rw [hi]
    rcases hm with hm | hm
    · simp_rw [abs_of_nonneg (sub_nonneg.mpr (hm (partition_point_mem P _)
        (partition_point_mem P _) (P.strictMono.monotone (Fin.castSucc_le_succ _))))]
      rw [sum_cell_differences (fun j => g (P.point j)), P.last, P.first,
        abs_of_nonneg (sub_nonneg.mpr (hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))]
    · simp_rw [abs_of_nonpos (sub_nonpos.mpr (hm (partition_point_mem P _)
        (partition_point_mem P _) (P.strictMono.monotone (Fin.castSucc_le_succ _))))]
      rw [Finset.sum_neg_distrib, sum_cell_differences (fun j => g (P.point j)),
        P.last, P.first, abs_of_nonpos (sub_nonpos.mpr (hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))]
  by_contra hne
  let ε := abs (realIntegral _ hi - |g b - g a|)
  have hε : 0 < ε := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δ, hδ, ht⟩ := (real_tagged_equivalence _ hab hi.bounded _).mp ⟨hi, rfl⟩ ε hε
  obtain ⟨P, hP⟩ := exists_fine_partition hab δ hδ
  obtain ⟨ξ, he⟩ := hsum P
  have := ht P ξ hP
  change ‖taggedSum P ξ (fun x => |g' x|) - realIntegral _ hi‖ < ε at this
  rw [he, Real.norm_eq_abs] at this
  have hh : ε < ε := by
    change abs (realIntegral _ hi - |g b - g a|) < ε
    rw [abs_sub_comm (realIntegral _ hi)]
    exact this
  exact (lt_irrefl ε) hh

/-- A pointwise real majorant bounds a vector valued fine-mesh limit. -/
theorem FineTaggedLimit.norm_le_of_majorant {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {m : ℝ → ℝ} {a b J : ℝ} {I : E}
    (hab : a ≤ b) (hf : FineTaggedLimit f a b I)
    (hm : FineTaggedLimit m a b J) (hb : ∀ x ∈ Icc a b, ‖f x‖ ≤ m x) :
    ‖I‖ ≤ J := by
  by_contra hn
  have hp : 0 < ‖I‖ - J := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨δf, hδf, hcf⟩ := hf ((‖I‖ - J) / 3) (by positivity)
  obtain ⟨δm, hδm, hcm⟩ := hm ((‖I‖ - J) / 3) (by positivity)
  obtain ⟨P, hP⟩ := exists_fine_partition hab (min δf δm) (lt_min hδf hδm)
  obtain ⟨ξ⟩ := tags_exist P
  have hf' := hcf P ξ (hP.trans_le (min_le_left _ _))
  have hm' := hcm P ξ (hP.trans_le (min_le_right _ _))
  have ht : ‖taggedSum P ξ f‖ ≤ taggedSum P ξ m := by
    apply (norm_taggedSum_le f P ξ).trans
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (hb (ξ i) (cell_subset_interval P i (ξ i).property)) (cell_positive P i).le
  have hl := norm_sub_norm_le I (taggedSum P ξ f)
  rw [norm_sub_rev] at hl
  rw [Real.norm_eq_abs] at hm'
  linarith [(abs_lt.mp hm').2]

/-- The norm estimate after proper integration by parts, valid over either
canonical scalar field, with the same constant in the complex case. -/
theorem abel_parts_bound {K : Type*} [RCLike K]
    {F : ℝ → K} {g g' : ℝ → ℝ} {a b ε B : ℝ} {I J : K}
    (hab : a ≤ b) (hε : 0 ≤ ε)
    (hg : ContinuousOn g (Icc a b)) (hgp : ContinuousOn g' (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hm : MonotoneOn g (Icc a b) ∨ AntitoneOn g (Icc a b))
    (hB : ∀ x ∈ Icc a b, |g x| ≤ B)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ ε)
    (hJ : FineTaggedLimit (fun x => F x * (g' x : K)) a b J)
    (he : I = F b * (g b : K) - J) : ‖I‖ ≤ 3 * B * ε := by
  obtain ⟨hi, hval⟩ := integral_abs_derivative hab hg hgp hd hm
  have ht := ((real_tagged_equivalence _ hab hi.bounded _).mp ⟨hi, rfl⟩).mul ε
  change FineTaggedLimit _ _ _ (ε * realIntegral _ hi) at ht
  rw [hval] at ht
  have hJb : ‖J‖ ≤ ε * |g b - g a| := by
    apply hJ.norm_le_of_majorant hab ht
    intro x hx
    rw [norm_mul, RCLike.norm_ofReal]
    exact mul_le_mul_of_nonneg_right (hF x hx) (abs_nonneg _)
  have hdiff := (abs_sub (g b) (g a)).trans
    (add_le_add (hB b ⟨hab, le_rfl⟩) (hB a ⟨le_rfl, hab⟩))
  rw [he]
  calc
    _ ≤ ‖F b * (g b : K)‖ + ‖J‖ := norm_sub_le _ _
    _ = ‖F b‖ * |g b| + ‖J‖ := by rw [norm_mul, RCLike.norm_ofReal]
    _ ≤ ε * B + ε * (B + B) := add_le_add
      (mul_le_mul (hF b ⟨hab, le_rfl⟩) (hB b ⟨hab, le_rfl⟩) (abs_nonneg _) hε)
      (hJb.trans (mul_le_mul_of_nonneg_left hdiff hε))
    _ = _ := by ring

/-- Abel's quantitative proper-tail estimate. -/
theorem abel_tail_estimate : Specs.SingleVariableAnalysis.Ch10.Abel.tailEstimate := by
  intro k f g g' R S ε B hf hε _hB hg hgp hd hm hb ht
  cases k with
  | real =>
    obtain ⟨H, F, hF, hfg, hFg, he⟩ := real_accumulation_parts f g g' hf hg hgp hd
    refine ⟨hfg, ?_⟩
    apply abel_parts_bound (K := ℝ) (RealIntegrable.ordered hf) hε hg hgp hd hm hb
      (F := F) (J := realIntegral _ hFg)
    · intro x hx
      rw [hF ⟨x, hx⟩]
      exact ht x hx (H ⟨x, hx⟩)
    · exact (real_tagged_equivalence _ (RealIntegrable.ordered hf) (RealIntegrable.bounded hFg) _).mp ⟨hFg, rfl⟩
    · exact he
  | complex =>
    obtain ⟨H, F, hF, hfg, hFg, he⟩ := complex_accumulation_parts f
      (fun x => (g x : ℂ)) (fun x => (g' x : ℂ)) hf
      (Complex.continuous_ofReal.comp_continuousOn hg)
      (Complex.continuous_ofReal.comp_continuousOn hgp)
      (fun x hx => (hd x hx).ofReal_comp)
    refine ⟨hfg, ?_⟩
    apply abel_parts_bound (K := ℂ) (RealIntegrable.ordered hf.1) hε hg hgp hd hm hb
      (F := F) (J := complexIntegral _ hFg)
    · intro x hx
      rw [hF ⟨x, hx⟩]
      exact ht x hx (H ⟨x, hx⟩)
    · exact (complex_tagged_equivalence _ (RealIntegrable.ordered hf.1) (ComplexIntegrable.norm_bound hFg) _).mp ⟨hFg, rfl⟩
    · exact he

/-- Proper integrability of a scalar function is preserved by a continuous
real multiplier on the same compact interval. -/
theorem integrable_weighted (k : ScalarKind) (f : ℝ →
    Specs.SingleVariableAnalysis.Ch10.OneEndpoint.S.scalarValue k)
    (g : ℝ → ℝ) {a b : ℝ} (hf : Integrable k f a b)
    (hg : ContinuousOn g (Icc a b)) :
    Integrable k (Specs.SingleVariableAnalysis.Ch10.Abel.weighted k f g) a b := by
  cases k with
  | real => exact real_product hf (realIntegrable_of_continuousOn (RealIntegrable.ordered hf) hg)
  | complex =>
    have hc := Complex.continuous_ofReal.comp_continuousOn hg
    exact complex_product hf
      ⟨realIntegrable_of_continuousOn (RealIntegrable.ordered hf.1)
        (Complex.continuous_re.comp_continuousOn hc),
       realIntegrable_of_continuousOn (RealIntegrable.ordered hf.1)
        (Complex.continuous_im.comp_continuousOn hc)⟩

/-- Bounded monotonicity also supplies the finite multiplier limit in the
source's explanatory decomposition. No integral limit is interchanged here. -/
theorem abel_multiplier_limit_and_split :
    Specs.SingleVariableAnalysis.Ch10.Abel.multiplierLimitAndSplit := by
  intro g a B hm hb
  have hne : (g '' Ici a).Nonempty := ⟨g a, mem_image_of_mem g (by simp)⟩
  have hup : BddAbove (g '' Ici a) := ⟨B, by
    rintro y ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (hb x hx)⟩
  have hlo : BddBelow (g '' Ici a) := ⟨-B, by
    rintro y ⟨x, hx, rfl⟩
    exact (neg_le_neg (hb x hx)).trans (neg_abs_le _)⟩
  have hfilter : (Filter.atTop : Filter ℝ) ≤ Filter.atTop ⊓ Filter.principal (Ici a) :=
    le_inf le_rfl (Filter.le_principal_iff.mpr (Filter.eventually_ge_atTop a))
  have hlim : ∃ ℓ : ℝ, Filter.Tendsto g Filter.atTop (nhds ℓ) := by
    rcases hm with hm | hm
    · exact ⟨sSup (g '' Ici a),
        (SingleVariableAnalysis.monotoneOn_tendsto_atTop_of_isLUB hm
          (isLUB_csSup hne hup)).mono_left hfilter⟩
    · exact ⟨sInf (g '' Ici a),
        (SingleVariableAnalysis.monotoneOn_tendsto_atTop_of_isLUB
          (β := OrderDual ℝ) hm (isGLB_csInf hne hlo)).mono_left hfilter⟩
  obtain ⟨ℓ, hℓ⟩ := hlim
  refine ⟨ℓ, hℓ, ?_⟩
  intro k f x
  cases k with
  | real =>
    change (show ℝ from f x) * g x = (show ℝ from f x) * ℓ + (show ℝ from f x) * (g x - ℓ)
    ring
  | complex =>
    change (show ℂ from f x) * (g x : ℂ) = (show ℂ from f x) * (ℓ : ℂ) + (show ℂ from f x) * ((g x - ℓ : ℝ) : ℂ)
    rw [Complex.ofReal_sub]
    exact (show ∀ z w t : ℂ, z * w = z * t + z * (w - t) by intros; ring)
      (f x) (g x) ℓ

namespace Improper
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch10.Abel

/-- Abel's test follows from the actual improper Cauchy criterion. The input
integral need only converge conditionally. B = 0 is covered by the same proof. -/
theorem abel_convergence : convergence := by
  intro k f g g' a B hconv hg hgp hd hm hB
  obtain ⟨L, hreg, hL⟩ := hconv
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB a (by simp))
  have hprod : RightRegular k (weighted k f g) a ⊤ := by
    refine ⟨WithTop.coe_lt_top _, fun t => ?_⟩
    exact integrable_weighted k f g (hreg.2 t)
      (hg.mono (fun x hx => hx.1))
  apply (right_cauchy_criterion k (weighted k f g) a ⊤ hprod).mpr
  intro δ hδ
  let ε := δ / (3 * (B + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heq : ε * (3 * (B + 1)) = δ := div_mul_cancel₀ δ (by positivity)
  have hsmall : 3 * B * ε < δ := by nlinarith
  obtain ⟨r, hr⟩ := (right_cauchy_criterion k f a ⊤ hreg).mp ⟨L, hreg, hL⟩ ε hε
  refine ⟨r, fun u v hru huv => ?_⟩
  have hfuv := scalar_integrable_subinterval k f (hreg.2 v) u.property.1.le huv.le le_rfl
  have hsub : Icc u.val v.val ⊆ Ici a := fun x hx => u.property.1.le.trans hx.1
  have hacc : ∀ x ∈ Icc u.val v.val, ∀ hx : I.scalarIntegrableValue k f u.val x,
      ‖I.scalarIntegralValue k f hx‖ ≤ ε := by
    intro x hx hxi
    rcases eq_or_lt_of_le hx.1 with he | hux
    · subst x
      have hz := integral_degenerate k f u.val hxi
      rw [hz]
      cases k with
      | real => change ‖(0 : ℝ)‖ ≤ ε; simpa only [norm_zero] using hε.le
      | complex => change ‖(0 : ℂ)‖ ≤ ε; simpa only [norm_zero] using hε.le
    · let tx : RightIndex a ⊤ := ⟨x, u.property.1.trans hux, WithTop.coe_lt_top _⟩
      obtain ⟨hh, hb⟩ := hr u tx hru hux
      exact hb.le
  obtain ⟨hfg, hb⟩ := abel_tail_estimate k f g g' u.val v.val ε B hfuv hε.le hB0
    (hg.mono hsub) (hgp.mono hsub)
    (fun x hx => hd x (u.property.1.trans hx.1))
    (hm.elim (fun h => Or.inl (h.mono hsub)) (fun h => Or.inr (h.mono hsub)))
    (fun x hx => hB x (hsub hx)) hacc
  exact ⟨hfg, hb.trans_lt hsmall⟩

end Improper
end SingleVariableAnalysis.Riemann
