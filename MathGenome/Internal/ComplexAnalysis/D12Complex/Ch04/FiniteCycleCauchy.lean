import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.FiniteCycleCauchy
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DividedDifferenceRegularity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexProperties
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.Liouville
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.RectifiableTraceNull
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.Locality

/-!
The homological Cauchy theorem for the canonical finite integral cycles.

The parameter integral is differentiated using uniform increment quotients on
the compact active trace. Joint divided-difference regularity supplies one
holomorphic branch on U; the ordinary transform supplies the other on the
open zero-index set. Their agreement gives an entire function, and the ML
estimate at infinity and the preliminary Liouville theorem make it zero.
The zero integral follows by applying the value formula to (z-a)f(z), with
trace avoidance proved from finite-length planar nullity. Local constancy of
the index and the same kernel differentiation give all higher formulas.
-/

noncomputable section
open Set Metric Filter
open scoped Topology BigOperators

namespace D12Complex.FiniteCycleCauchy

/-- Contour integrals depend only on the integrand on the active trace. -/
theorem chain_integral_congr (Γ : IntegralChain) {f g : ℂ → ℂ}
    (h : EqOn f g Γ.trace) : Γ.integral f = Γ.integral g := by
  unfold IntegralChain.integral Finsupp.sum
  apply Finset.sum_congr rfl
  intro γ hγ
  dsimp only
  congr 1
  unfold PiecewiseC1Path.integral C1Partition.integral
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [h (show γ t ∈ Γ.trace from ⟨γ, hγ, t,
    γ.partition.piece_subset i (by simpa [C1Partition.pieceSet, uIcc_of_le (γ.partition.piece_lt i).le] using ht), rfl⟩)]

theorem chain_integral_const_mul (Γ : IntegralChain) (c : ℂ) (f : ℂ → ℂ) :
    Γ.integral (fun z => c * f z) = c * Γ.integral f := by
  unfold IntegralChain.integral Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  dsimp only
  have he : γ.integral (fun z => c * f z) = c * γ.integral f := by
    unfold PiecewiseC1Path.integral C1Partition.integral
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    rw [Finset.mul_sum]
  rw [he]
  ring

theorem chain_integral_sub (Γ : IntegralChain) (f g : ℂ → ℂ)
    (hf : ContinuousOn f Γ.trace) (hg : ContinuousOn g Γ.trace) :
    Γ.integral (fun z => f z - g z) = Γ.integral f - Γ.integral g := by
  unfold IntegralChain.integral Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro γ hγ
  dsimp only
  rw [PiecewiseC1Length.integral_sub γ f g
    (hf.mono (PiecewiseC1Length.trace_subset_chain Γ hγ))
    (hg.mono (PiecewiseC1Length.trace_subset_chain Γ hγ)), mul_sub]

/-- Uniform convergence on the trace permits a contour limit for any filter. -/
theorem chain_integral_tendsto_uniform {α : Type*} {l : Filter α}
    (Γ : IntegralChain) (F : α → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ᶠ x in l, ContinuousOn (F x) Γ.trace) (hf : ContinuousOn f Γ.trace)
    (hu : TendstoUniformlyOn F f l Γ.trace) :
    Tendsto (fun x => Γ.integral (F x)) l (𝓝 (Γ.integral f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hL : 0 < Γ.lengthBound + 1 := by
    linarith [IndexProperties.chain_lengthBound_nonneg Γ]
  have hδ : 0 < ε / (Γ.lengthBound + 1) := div_pos hε hL
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp hu _ hδ] with x hx hu
  rw [dist_eq_norm, ← chain_integral_sub Γ (F x) f hx hf]
  have hb := PiecewiseC1Length.chain_norm_integral_le_mul_bound Γ _ (hx.sub hf)
    (M := ε / (Γ.lengthBound + 1)) (fun z hz => by
      simpa only [dist_eq_norm, Pi.sub_apply, norm_sub_rev] using (hu z hz).le)
  apply hb.trans_lt
  rw [← mul_div_assoc, div_lt_iff₀ hL]
  nlinarith


/-- Joint continuity of a parameter derivative on a compact set makes the
increment quotients uniform in that parameter. -/
theorem uniform_differenceQuotients (U K : Set ℂ) (F D : ℂ → ℂ → ℂ)
    (hU : IsOpen U) (hK : IsCompact K)
    (hD : ContinuousOn (fun p : ℂ × ℂ => D p.1 p.2) (U ×ˢ K))
    (hd : ∀ z ∈ U, ∀ w ∈ K, HasDerivAt (fun t => F t w) (D z w) z)
    (a : ℂ) (ha : a ∈ U) :
    TendstoUniformlyOn (fun h w => (F (a+h) w - F a w) / h)
      (D a) (𝓝[≠] 0) K := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  have hhalf : closedBall a (R/2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hRU
  have huc : UniformContinuousOn (fun p : ℂ × ℂ => D p.1 p.2)
      (closedBall a (R/2) ×ˢ K) :=
    ((isCompact_closedBall a (R/2)).prod hK).uniformContinuousOn_of_continuous
      (hD.mono (prod_mono hhalf (Subset.refl K)))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp huc (ε/2) (half_pos hε)
  have hev : ∀ᶠ h : ℂ in 𝓝[≠] 0, ‖h‖ < min δ (R/2) := by
    apply mem_nhdsWithin_of_mem_nhds
    filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < min δ (R/2) from lt_min hδ (half_pos hR))]
      with h hh
    exact mem_ball_zero_iff.mp hh
  filter_upwards [hev, self_mem_nhdsWithin] with h hh hne
  intro w hw
  have hh0 : h ≠ 0 := hne
  have hnorm : ‖h‖ < R/2 := lt_of_lt_of_le hh (min_le_right _ _)
  have hsmall : ‖h‖ < δ := lt_of_lt_of_le hh (min_le_left _ _)
  have hlocal : closedBall a ‖h‖ ⊆ closedBall a (R/2) :=
    closedBall_subset_closedBall hnorm.le
  have hbound : ∀ t ∈ closedBall a ‖h‖, ‖D t w - D a w‖ ≤ ε/2 := by
    intro t ht
    have hdist : dist (t,w) (a,w) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist t a)] using
        (mem_closedBall.mp ht).trans_lt hsmall
    simpa only [dist_eq_norm] using
      (hu (t,w) ⟨hlocal ht, hw⟩ (a,w) ⟨mem_closedBall_self (by linarith), hw⟩ hdist).le
  have hder : ∀ t ∈ closedBall a ‖h‖,
      HasDerivWithinAt (fun t => F t w - t * D a w)
        (D t w - D a w) (closedBall a ‖h‖) t := by
    intro t ht
    convert ((hd t (hhalf (hlocal ht)) w hw).sub
      ((hasDerivAt_id t).mul_const (D a w))).hasDerivWithinAt using 1 <;> first | rfl | simp
  have hm := (convex_closedBall a ‖h‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (mem_closedBall_self (norm_nonneg h))
    (show a+h ∈ closedBall a ‖h‖ from by simp [mem_closedBall, dist_eq_norm])
  rw [dist_comm, dist_eq_norm]
  have heq : (F (a+h) w - F a w) / h - D a w =
      ((F (a+h) w - (a+h)*D a w) - (F a w - a*D a w)) / h := by
    field_simp
    ring
  rw [heq, norm_div]
  calc
    _ ≤ ε/2 := (div_le_iff₀ (norm_pos_iff.mpr hh0)).mpr
      (by simpa only [add_sub_cancel_left] using hm)
    _ < ε := half_lt_self hε

/-- Differentiation under a finite-chain integral, with its actual derivative. -/
theorem hasDerivAt_chain_integral (Γ : IntegralChain) (U : Set ℂ)
    (F D : ℂ → ℂ → ℂ) (hU : IsOpen U)
    (hF : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (U ×ˢ Γ.trace))
    (hD : ContinuousOn (fun p : ℂ × ℂ => D p.1 p.2) (U ×ˢ Γ.trace))
    (hd : ∀ z ∈ U, ∀ w ∈ Γ.trace, HasDerivAt (fun t => F t w) (D z w) z)
    (a : ℂ) (ha : a ∈ U) :
    HasDerivAt (fun z => Γ.integral (F z)) (Γ.integral (D a)) a := by
  have hFc (z : ℂ) (hz : z ∈ U) : ContinuousOn (F z) Γ.trace :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun w hw => ⟨hz, hw⟩)
  have hDc : ContinuousOn (D a) Γ.trace :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn (fun w hw => ⟨ha, hw⟩)
  have hu := uniform_differenceQuotients U Γ.trace F D hU
    (PiecewiseC1Length.chain_trace_compact Γ) hD hd a ha
  have he : ∀ᶠ h : ℂ in 𝓝[≠] 0, a+h ∈ U :=
    mem_nhdsWithin_of_mem_nhds ((continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using hU.mem_nhds ha))
  have hc : ∀ᶠ h : ℂ in 𝓝[≠] 0,
      ContinuousOn (fun w => (F (a+h) w - F a w) / h) Γ.trace := by
    filter_upwards [he] with h hh
    exact ((hFc (a+h) hh).sub (hFc a ha)).div_const h
  have hi := chain_integral_tendsto_uniform Γ _ (D a) hc hDc hu
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply hi.congr'
  filter_upwards [he] with h hh
  simp only [div_eq_mul_inv, smul_eq_mul]
  rw [show (fun w => (F (a+h) w - F a w) * h⁻¹) =
    (fun w => h⁻¹ * (F (a+h) w - F a w)) from funext (fun w => mul_comm _ _),
    chain_integral_const_mul, chain_integral_sub Γ _ _ (hFc (a+h) hh) (hFc a ha)]


/-- Every rational kernel and its parameter derivative are continuous jointly
away from the active trace. -/
theorem continuousOn_kernel (Γ : IntegralChain) (f : ℂ → ℂ)
    (hf : ContinuousOn f Γ.trace) (n : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => f p.2 / (p.2-p.1)^(n+1))
      (Γ.traceᶜ ×ˢ Γ.trace) := by
  refine (hf.comp continuous_snd.continuousOn (fun p hp => hp.2)).div (by fun_prop) ?_
  intro p hp
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hp.1 (he ▸ hp.2)))

theorem hasDerivAt_kernel (w z : ℂ) (h : w ≠ z) (f : ℂ → ℂ) (n : ℕ) :
    HasDerivAt (fun t => f w / (w-t)^(n+1))
      ((n+1 : ℂ) * (f w / (w-z)^(n+2))) z := by
  have hd := (hasDerivAt_const z w).sub (hasDerivAt_id z)
  have he := (hasDerivAt_const z (f w)).div (hd.pow (n+1))
    (pow_ne_zero _ (sub_ne_zero.mpr h))
  convert he using 1 <;> try rfl
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, zero_sub, mul_neg, zero_mul, sub_neg_eq_add]
  field_simp [sub_ne_zero.mpr h]
  ring

/-- The Cauchy transform is holomorphic at every point off the trace. -/
theorem hasDerivAt_kernel_integral (Γ : IntegralChain) (f : ℂ → ℂ)
    (hf : ContinuousOn f Γ.trace) (n : ℕ) (a : ℂ) (ha : a ∉ Γ.trace) :
    HasDerivAt (fun z => Γ.integral (fun w => f w / (w-z)^(n+1)))
      ((n+1 : ℂ) * Γ.integral (fun w => f w / (w-a)^(n+2))) a := by
  have h := hasDerivAt_chain_integral Γ Γ.traceᶜ
    (fun z w => f w / (w-z)^(n+1))
    (fun z w => (n+1 : ℂ) * (f w / (w-z)^(n+2)))
    (PiecewiseC1Length.chain_trace_compact Γ).isClosed.isOpen_compl
    (continuousOn_kernel Γ f hf n)
    (by simpa only [Nat.add_assoc] using (continuousOn_kernel Γ f hf (n+1)).const_mul (n+1 : ℂ))
    (fun z hz w hw => hasDerivAt_kernel w z (fun he => hz (he ▸ hw)) f n) a ha
  rwa [chain_integral_const_mul] at h

/-- The divided-difference integral stays holomorphic also when the parameter
crosses a contour, by the proved diagonal regularity. -/
theorem holomorphicOn_dividedDifference_integral (Γ : IntegralChain) (U : Set ℂ)
    (f : ℂ → ℂ) (hf : HolomorphicOn U f) (hΓ : Γ.trace ⊆ U) :
    HolomorphicOn U (fun z => Γ.integral (DividedDifferenceRegularity.dividedDifference f z)) := by
  refine ⟨hf.1, fun a ha => ?_⟩
  exact (hasDerivAt_chain_integral Γ U _ _ hf.1
    ((DividedDifferenceRegularity.continuousOn_dividedDifference U f hf).mono
      (prod_mono (Subset.refl U) hΓ))
    ((DividedDifferenceRegularity.continuousOn_partialZ U f hf).mono
      (prod_mono (Subset.refl U) hΓ))
    (fun z hz w hw => DividedDifferenceRegularity.hasDerivAt_slice U f hf z hz w (hΓ hw))
    a ha).differentiableAt

/-- The open set on which the index vanishes and the integral kernel is regular. -/
def zeroIndexSet (Γ : IntegralCycle) : Set ℂ := {z | z ∉ Γ.trace ∧ Γ.index z = 0}

theorem isOpen_zeroIndexSet (Γ : IntegralCycle) : IsOpen (zeroIndexSet Γ) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  filter_upwards [IndexProperties.cycle_index_locally_constant Γ z hz.1] with w hw
  exact ⟨hw.1, hw.2.trans hz.2⟩

theorem union_zeroIndexSet (Γ : IntegralCycle) (U : Set ℂ) (hΓ : Γ.trace ⊆ U)
    (hnull : ∀ w, w ∉ U → Γ.index w = 0) : U ∪ zeroIndexSet Γ = univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hz : z ∈ U
  · exact Or.inl hz
  · exact Or.inr ⟨fun ht => hz (hΓ ht), hnull z hz⟩

/-- The two local formulas agree on their overlap precisely because the
index term vanishes. -/
theorem dividedDifference_integral_eq_transform (Γ : IntegralCycle) (U : Set ℂ)
    (f : ℂ → ℂ) (hf : HolomorphicOn U f) (hΓ : Γ.trace ⊆ U)
    (a : ℂ) (_ha : a ∈ U) (hat : a ∉ Γ.trace) :
    Γ.integral (DividedDifferenceRegularity.dividedDifference f a) =
      Γ.integral (fun w => f w / (w-a)) -
        f a * Γ.integral (fun w => 1 / (w-a)) := by
  have hc : ContinuousOn f Γ.trace := fun w hw =>
    (hf.2 w (hΓ hw)).continuousAt.continuousWithinAt
  have hr := Γ.chain.reciprocal_continuousOn_trace a hat
  have he : Γ.integral (DividedDifferenceRegularity.dividedDifference f a) =
      Γ.integral (fun w => f w * (1 / (w-a)) - f a * (1 / (w-a))) := by
    apply chain_integral_congr
    intro w hw
    rw [DividedDifferenceRegularity.dividedDifference, ite_eq_right (show a ≠ w from fun he => hat (he ▸ hw))]
    ring
  rw [he]
  simp only [IntegralCycle.integral]
  rw [chain_integral_sub Γ.chain (fun w => f w * (1 / (w-a)))
    (fun w => f a * (1 / (w-a))) (hc.mul hr) (hr.const_mul _),
    chain_integral_const_mul]
  congr 1
  apply chain_integral_congr
  intro w _
  ring

/-- Every finite active trace has empty interior, with no injectivity premise. -/
theorem cycle_trace_interior_empty (Γ : IntegralCycle) : interior Γ.trace = ∅ := by
  have he : Γ.trace = ⋃ γ ∈ Γ.chain.support, γ.path.trace := by
    ext z
    simp only [IntegralCycle.trace, IntegralChain.trace, mem_ofPred_eq, mem_iUnion, exists_prop]
    rfl
  rw [he]
  exact RectifiableTrace.finite_union_interior_empty Γ.chain.support
    (fun γ => γ.path) (fun γ _ => (Stieltjes.contourIntegral_piecewiseC1 γ (fun _ => 0) continuousOn_const).1)


/-- The transform tends to zero at infinity, with a uniform bound derived
from the finite total length and a bound on the integrand on the trace. -/
theorem kernel_integral_small_at_infinity (Γ : IntegralChain) (f : ℂ → ℂ)
    (hf : ContinuousOn f Γ.trace) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ a : ℂ, R < ‖a‖ → a ∉ Γ.trace ∧
      ‖Γ.integral (fun w => f w / (w-a))‖ < ε := by
  obtain ⟨R, hR⟩ := (PiecewiseC1Length.chain_trace_compact Γ).isBounded.exists_norm_le
  obtain ⟨M₀, hM₀⟩ := (PiecewiseC1Length.chain_trace_compact Γ).exists_bound_of_continuousOn hf
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ w ∈ Γ.trace, ‖f w‖ ≤ M := fun w hw => (hM₀ w hw).trans (le_max_left _ _)
  let δ := (Γ.lengthBound * M + 1) / ε
  have hL := IndexProperties.chain_lengthBound_nonneg Γ
  have hδ : 0 < δ := div_pos (by positivity) hε
  refine ⟨R+δ, fun a ha => ?_⟩
  have hat : a ∉ Γ.trace := fun ht => by have := hR a ht; linarith
  have hd : ∀ w ∈ Γ.trace, δ ≤ ‖w-a‖ := by
    intro w hw
    have := hR w hw
    have hh := norm_sub_norm_le a w
    rw [norm_sub_rev] at hh
    linarith
  refine ⟨hat, ?_⟩
  have hc : ContinuousOn (fun w => f w / (w-a)) Γ.trace :=
    hf.div (continuousOn_id.sub continuousOn_const)
      (fun w hw => sub_ne_zero.mpr (fun he => hat (he ▸ hw)))
  have hb := PiecewiseC1Length.chain_norm_integral_le_mul_bound Γ _ hc (M := M/δ)
    (fun w hw => by
      rw [norm_div]
      exact div_le_div₀ hM (hbound w hw) hδ (hd w hw))
  apply hb.trans_lt
  rw [← mul_div_assoc, div_lt_iff₀ hδ]
  have he : ε * δ = Γ.lengthBound * M + 1 := mul_div_cancel₀ _ (ne_of_gt hε)
  linarith

/-- A direct consequence of the preliminary Liouville theorem, formulated
with an explicit epsilon-radius condition at infinity. -/
theorem entire_eq_zero_of_small_at_infinity (Q : ℂ → ℂ)
    (hQ : HolomorphicOn univ Q)
    (hsmall : ∀ ε > 0, ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖Q z‖ < ε) :
    ∀ z, Q z = 0 := by
  obtain ⟨R, hR⟩ := hsmall 1 zero_lt_one
  have hc : Continuous Q := continuous_iff_continuousAt.mpr (fun z => (hQ.2 z (mem_univ z)).continuousAt)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hc.continuousOn
  have hbound : ∀ z, ‖Q z‖ ≤ max M 1 := by
    intro z
    by_cases hz : ‖z‖ ≤ R
    · exact (hM z (by simpa using hz)).trans (le_max_left _ _)
    · exact (hR z (lt_of_not_ge hz)).le.trans (le_max_right _ _)
  obtain ⟨c, heq⟩ := Liouville.bounded_entire_constant Q (max M 1) hQ
    (le_trans zero_le_one (le_max_right _ _)) hbound
  have hc0 : c = 0 := by
    apply norm_eq_zero.mp
    by_contra hn
    have hcn : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    obtain ⟨S, hS⟩ := hsmall (‖c‖/2) (half_pos hcn)
    have hs : S < ‖((|S|+1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith [le_abs_self S]
    have := hS ((|S|+1 : ℝ) : ℂ) hs
    rw [heq] at this
    linarith
  intro z
  rw [heq, hc0]

/-- The glued function on the two open sets exists and is entire. -/
theorem exists_entire_gluing (Γ : IntegralCycle) (U : Set ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn U f) (hΓ : Γ.trace ⊆ U)
    (hnull : ∀ w, w ∉ U → Γ.index w = 0) :
    ∃ Q : ℂ → ℂ, HolomorphicOn univ Q ∧
      EqOn Q (fun z => Γ.integral (DividedDifferenceRegularity.dividedDifference f z)) U ∧
      EqOn Q (fun z => Γ.integral (fun w => f w / (w-z))) (zeroIndexSet Γ) := by
  let V : Bool → Set ℂ := fun b => if b then U else zeroIndexSet Γ
  let F : Bool → ℂ → ℂ := fun b => if b then
    (fun z => Γ.integral (DividedDifferenceRegularity.dividedDifference f z)) else
    (fun z => Γ.integral (fun w => f w / (w-z)))
  have hcover : (⋃ b, V b) = univ := by
    apply eq_univ_of_forall
    intro z
    have hz : z ∈ U ∪ zeroIndexSet Γ := by rw [union_zeroIndexSet Γ U hΓ hnull]; trivial
    rcases hz with hz | hz
    · exact mem_iUnion.mpr ⟨true, hz⟩
    · exact mem_iUnion.mpr ⟨false, hz⟩
  have hc : ContinuousOn f Γ.trace := fun w hw =>
    (hf.2 w (hΓ hw)).continuousAt.continuousWithinAt
  have hhol : ∀ b, HolomorphicOn (V b) (F b) := by
    intro b
    cases b
    · refine ⟨isOpen_zeroIndexSet Γ, fun a ha => ?_⟩
      simpa only [F, Bool.false_eq_true, ite_false, IntegralCycle.integral, Nat.zero_add, pow_one] using
        (hasDerivAt_kernel_integral Γ.chain f hc 0 a ha.1).differentiableAt
    · exact holomorphicOn_dividedDifference_integral Γ.chain U f hf hΓ
  have hoverlap (a : ℂ) (ha : a ∈ U) (hH : a ∈ zeroIndexSet Γ) :
      Γ.integral (DividedDifferenceRegularity.dividedDifference f a) =
        Γ.integral (fun w => f w / (w-a)) := by
    rw [dividedDifference_integral_eq_transform Γ U f hf hΓ a ha hH.1]
    have hi := Γ.index_eq_integral a hH.1
    have hp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    rw [hH.2] at hi
    have hzero : Γ.integral (fun w => 1 / (w-a)) = 0 :=
      (mul_eq_zero.mp hi.symm).resolve_left (inv_ne_zero hp)
    rw [hzero, mul_zero, sub_zero]
  have hcompat : ∀ b c, EqOn (F b) (F c) (V b ∩ V c) := by
    intro b c a ha
    cases b <;> cases c
    · rfl
    · exact (hoverlap a ha.2 ha.1).symm
    · exact hoverlap a ha.1 ha.2
    · rfl
  obtain ⟨Q, hQ, heq, _⟩ := holomorphicOn_glue univ V F hcover hhol hcompat
  exact ⟨Q, hQ, heq true, heq false⟩


/-- The full value formula on arbitrary open sets and finite integral cycles. -/
theorem cycle_cauchy_formula :
    Specs.D12Complex.Ch04.FiniteCycleCauchy.cycle_cauchy_formula_type := by
  intro U f Γ hf hΓ hnull a ha hat
  obtain ⟨Q, hQ, hQU, hQH⟩ := exists_entire_gluing Γ U f hf hΓ hnull
  have hc : ContinuousOn f Γ.trace := fun w hw =>
    (hf.2 w (hΓ hw)).continuousAt.continuousWithinAt
  have hsmall : ∀ ε > 0, ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖Q z‖ < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := kernel_integral_small_at_infinity Γ.chain f hc ε hε
    obtain ⟨S, hS⟩ := IndexProperties.cycle_index_zero_outside_ball Γ
    refine ⟨max R S, fun z hz => ?_⟩
    obtain ⟨hzt, hzi⟩ := hR z ((le_max_left _ _).trans_lt hz)
    rw [hQH ⟨hzt, hS z ((le_max_right _ _).trans_lt hz)⟩]
    exact hzi
  have hzero := entire_eq_zero_of_small_at_infinity Q hQ hsmall
  have hi : Γ.integral (fun w => f w / (w-a)) =
      f a * Γ.integral (fun w => 1 / (w-a)) := by
    apply sub_eq_zero.mp
    rw [← dividedDifference_integral_eq_transform Γ U f hf hΓ a ha hat]
    exact (hQU ha).symm.trans (hzero a)
  rw [Γ.index_eq_integral a hat, hi]
  ring

/-- Nonempty open sets contain a point off every finite-length trace. -/
theorem exists_off_cycle_trace (Γ : IntegralCycle) (U : Set ℂ)
    (hU : IsOpen U) (hne : U.Nonempty) : ∃ a ∈ U, a ∉ Γ.trace := by
  by_contra h
  push Not at h
  have hi : U ⊆ interior Γ.trace := interior_maximal h hU
  rw [cycle_trace_interior_empty Γ] at hi
  exact hne.ne_empty (subset_empty_iff.mp hi)

theorem chain_eq_zero_of_trace_eq_empty (Γ : IntegralChain) (h : Γ.trace = ∅) : Γ = 0 := by
  classical
  apply Finsupp.ext
  intro γ
  change Γ γ = 0
  by_contra hn
  obtain ⟨z, hz⟩ := γ.path.trace_nonempty
  have : z ∈ Γ.trace := ⟨γ, Finsupp.mem_support_iff.mpr hn, hz⟩
  rw [h] at this
  exact this

/-- The zero integral conclusion, including the empty-open-set case. -/
theorem cycle_cauchy_theorem :
    Specs.D12Complex.Ch04.FiniteCycleCauchy.cycle_cauchy_theorem_type := by
  intro U f Γ hf hΓ hnull
  by_cases hne : U.Nonempty
  · obtain ⟨a, ha, hat⟩ := exists_off_cycle_trace Γ U hf.1 hne
    have hg : HolomorphicOn U (fun z => (z-a)*f z) :=
      ⟨hf.1, fun z hz => (differentiableAt_id.sub_const a).mul (hf.2 z hz)⟩
    have he := cycle_cauchy_formula U (fun z => (z-a)*f z) Γ hg hΓ hnull a ha hat
    have hcancel : Γ.integral (fun z => (z-a)*f z/(z-a)) = Γ.integral f := by
      apply chain_integral_congr
      intro z hz
      exact mul_div_cancel_left₀ (f z) (sub_ne_zero.mpr (fun he => hat (he ▸ hz)))
    simp only [sub_self, zero_mul, mul_zero, hcancel] at he
    have hp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    exact (mul_eq_zero.mp he.symm).resolve_left (inv_ne_zero hp)
  · have ht : Γ.chain.trace = ∅ := by
      apply subset_empty_iff.mp
      exact hΓ.trans (by rw [Set.not_nonempty_iff_eq_empty.mp hne])
    have he := chain_eq_zero_of_trace_eq_empty Γ.chain ht
    simp [IntegralCycle.integral, he, IntegralChain.integral, Finsupp.sum]

/-- All orders of the index-weighted derivative formula. The index is constant
on a neighborhood of the point at each induction step. -/
theorem cycle_cauchy_derivatives :
    Specs.D12Complex.Ch04.FiniteCycleCauchy.cycle_cauchy_derivatives_type := by
  intro U f Γ hf hΓ hnull a ha hat n
  have hc : ContinuousOn f Γ.trace := fun w hw =>
    (hf.2 w (hΓ hw)).continuousAt.continuousWithinAt
  have hall : ∀ n : ℕ, ∀ a ∈ U, a ∉ Γ.trace →
      Γ.index a * iteratedDeriv n f a =
        (n.factorial : ℂ) / (2 * Real.pi * Complex.I) *
          Γ.integral (fun w => f w / (w-a)^(n+1)) := by
    intro n
    induction n with
    | zero =>
      intro a ha hat
      simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, Nat.zero_add,
        pow_one, one_div] using cycle_cauchy_formula U f Γ hf hΓ hnull a ha hat
    | succ n ih =>
      intro a ha hat
      have heq : (fun z => Γ.index a * iteratedDeriv n f z) =ᶠ[𝓝 a]
          (fun z => (n.factorial : ℂ) / (2 * Real.pi * Complex.I) *
            Γ.integral (fun w => f w / (w-z)^(n+1))) := by
        filter_upwards [hf.1.mem_nhds ha, IndexProperties.cycle_index_locally_constant Γ a hat]
          with z hz hi
        rw [← hi.2]
        exact ih z hz hi.1
      have hl := ((DiskCauchyDerivatives.holomorphicOn_iteratedDeriv U f hf n).2 a ha).const_mul
        (Γ.index a)
      have hr := ((hasDerivAt_kernel_integral Γ.chain f hc n a hat).const_mul
        ((n.factorial : ℂ) / (2 * Real.pi * Complex.I))).congr_of_eventuallyEq heq
      calc
        Γ.index a * iteratedDeriv (n+1) f a = _ := hl.unique hr
        _ = _ := by
          simp only [IntegralCycle.integral, Nat.add_assoc, Nat.reduceAdd,
            Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring
  exact hall n a ha hat

end D12Complex.FiniteCycleCauchy
