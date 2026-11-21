import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.RationalRiemannSums
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.PolygonRepresentation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.AbsolutelyContinuousContours
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace D12Complex.RationalRiemannSums

/-- On an affine segment the chord weights are precisely the signed segment
velocity times the cell length. Thus the sums below specialize to the ordinary
segment Riemann sums, with no change of orientation. -/
theorem pathSum_affine (γ : PiecewiseC1Path) (s : PathSampling γ) (f : ℂ → ℂ)
    (a v : ℂ) (haff : ∀ t ∈ Icc γ.path.a γ.path.b, γ t = a + (t : ℂ) * v)
    (z : ℂ) :
    pathSum γ s f z = ∑ i : Fin s.1.n,
      (f (γ (s.2 i)) * v / (γ (s.2 i) - z)) *
        ((s.1.point i.succ - s.1.point i.castSucc : ℝ) : ℂ) := by
  unfold pathSum Stieltjes.taggedSum
  apply Finset.sum_congr rfl
  intro i _
  have hmem (j : Fin (s.1.n + 1)) : s.1.point j ∈ Icc γ.path.a γ.path.b := by
    constructor
    · simpa only [s.1.first] using s.1.strictMono.monotone (Fin.zero_le j)
    · simpa only [s.1.last] using s.1.strictMono.monotone (Fin.le_last j)
  rw [haff _ (hmem i.succ), haff _ (hmem i.castSucc), Complex.ofReal_sub]
  ring

theorem continuousOn_kernel (K : Set ℂ) (γ : PiecewiseC1Path) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) (hd : Disjoint K γ.trace) :
    ContinuousOn (fun p : ℂ × ℝ => f (γ p.2) / (γ p.2 - p.1))
      (K ×ˢ Icc γ.path.a γ.path.b) := by
  have hg : ContinuousOn (fun p : ℂ × ℝ => γ p.2)
      (K ×ˢ Icc γ.path.a γ.path.b) :=
    γ.path.continuousOn.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  exact (hf.comp hg (fun p hp => ⟨p.2, hp.2, rfl⟩)).div
    (hg.sub continuous_fst.continuousOn) (fun p hp => sub_ne_zero.mpr
      (fun he => disjoint_left.mp hd hp.1 (he ▸ ⟨p.2, hp.2, rfl⟩)))

theorem uniform_path_sums :
    Specs.D12Complex.Ch15.RationalRiemannSums.uniform_path_sums_type := by
  intro K γ f hK hf hd ε hε
  have hγ := piecewiseC1_ac γ.path γ.property
  obtain ⟨hv, _, hr⟩ := Stieltjes.ac_derivative γ.path.ordered γ hγ
  let M : ℝ := ∫ t in γ.path.a..γ.path.b, ‖deriv γ t‖
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg γ.path.ordered
    (fun _ _ => norm_nonneg _)
  let η : ℝ := ε / (M + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hu := (hK.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (continuousOn_kernel K γ f hf hd)
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  refine ⟨δ, hδ, fun P hP tags z hz => ?_⟩
  have hc : ContinuousOn (fun w => f w / (w - z)) γ.trace :=
    hf.div (continuous_id.sub continuous_const).continuousOn
      (fun w hw => sub_ne_zero.mpr (fun he => disjoint_left.mp hd hz (he ▸ hw)))
  have hct : ContinuousOn (fun t => f (γ t) / (γ t - z))
      (Icc γ.path.a γ.path.b) :=
    hc.comp γ.path.continuousOn (fun t ht => ⟨t, ht, rfl⟩)
  have he := Stieltjes.taggedSum_integral_error γ.path.ordered
    (fun t => f (γ t) / (γ t - z)) γ (deriv γ) hct hv hr P tags
    (η := η) (by
      intro i x hx
      have hleft : γ.path.a ≤ P.point i.castSucc := by
        simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i.castSucc)
      have hright : P.point i.succ ≤ γ.path.b := by
        simpa only [P.last] using P.strictMono.monotone (Fin.le_last i.succ)
      have ht := (tags i).property
      have hm := SingleVariableAnalysis.Riemann.cellLength_le_mesh P i
      change P.point i.succ - P.point i.castSucc ≤ Stieltjes.mesh P at hm
      have htx : dist (tags i : ℝ) x < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2, hx.1, hx.2]
      have hh := hosc (z, (tags i : ℝ)) ⟨hz, hleft.trans ht.1, ht.2.trans hright⟩
        (z, x) ⟨hz, hleft.trans hx.1, hx.2.trans hright⟩
        (by simpa using htx)
      exact (by simpa only [dist_eq_norm] using hh.le))
  have hbridge := (Stieltjes.contourIntegral_ac γ.path hγ _ hc).2
  have hpc := (Stieltjes.contourIntegral_piecewiseC1 γ _ hc).2
  have heq : (∫ t in γ.path.a..γ.path.b,
      (f (γ t) / (γ t - z)) * deriv γ t) =
      γ.integral (fun w => f w / (w - z)) := hbridge.symm.trans hpc
  change ‖Stieltjes.taggedSum P tags (fun t => f (γ t) / (γ t - z)) γ - _‖ < ε
  rw [← heq]
  apply he.trans_lt
  have heη : η * (M + 1) = ε := div_mul_cancel₀ ε (by positivity)
  change η * M < ε
  nlinarith

/-- An explicit polynomial quotient, with all its denominator roots in S. -/
private def RationalWithPoles (S : Set ℂ) (g : ℂ → ℂ) : Prop :=
  ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
    (∀ z, Q.eval z = 0 → z ∈ S) ∧
    ∀ z, z ∉ S → g z = P.eval z / Q.eval z

private theorem rational_const (S : Set ℂ) (c : ℂ) :
    RationalWithPoles S (fun _ => c) := by
  exact ⟨Polynomial.C c, 1, one_ne_zero, by simp, by simp⟩

private theorem rational_add {S : Set ℂ} {g h : ℂ → ℂ}
    (hg : RationalWithPoles S g) (hh : RationalWithPoles S h) :
    RationalWithPoles S (fun z => g z + h z) := by
  obtain ⟨P, Q, hQ, hrootQ, hPQ⟩ := hg
  obtain ⟨R, T, hT, hrootT, hRT⟩ := hh
  refine ⟨P * T + R * Q, Q * T, mul_ne_zero hQ hT, ?_, ?_⟩
  · intro z hz
    simp only [Polynomial.eval_mul, mul_eq_zero] at hz
    exact hz.elim (hrootQ z) (hrootT z)
  · intro z hz
    simp only [Polynomial.eval_add, Polynomial.eval_mul]
    rw [hPQ z hz, hRT z hz]
    simpa only [mul_comm] using
      (div_add_div (P.eval z) (R.eval z) (fun he => hz (hrootQ z he))
        (fun he => hz (hrootT z he)))

private theorem rational_const_mul {S : Set ℂ} {g : ℂ → ℂ}
    (hg : RationalWithPoles S g) (c : ℂ) :
    RationalWithPoles S (fun z => c * g z) := by
  obtain ⟨P, Q, hQ, hroot, he⟩ := hg
  refine ⟨Polynomial.C c * P, Q, hQ, hroot, ?_⟩
  intro z hz
  simp only [Polynomial.eval_mul, Polynomial.eval_C, he z hz, mul_div_assoc]

private theorem rational_resolvent {S : Set ℂ} {w : ℂ} (hw : w ∈ S) (c : ℂ) :
    RationalWithPoles S (fun z => c / (w - z)) := by
  refine ⟨Polynomial.C (-c), Polynomial.X - Polynomial.C w,
    Polynomial.X_sub_C_ne_zero w, ?_, ?_⟩
  · intro z hz
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hz
    exact hz ▸ hw
  · intro z _
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [← neg_sub w z, neg_div_neg_eq]

private theorem rational_sum {ι : Type*} (S : Set ℂ) (s : Finset ι)
    (g : ι → ℂ → ℂ) (hg : ∀ i ∈ s, RationalWithPoles S (g i)) :
    RationalWithPoles S (fun z => ∑ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rational_const S 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      rational_add (hg i (Finset.mem_insert_self ..))
        (ih (fun j hj => hg j (Finset.mem_insert_of_mem hj)))

theorem pathSum_rational (S : Set ℂ) (γ : PiecewiseC1Path) (s : PathSampling γ)
    (f : ℂ → ℂ) (hγ : γ.trace ⊆ S) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ (∀ z, Q.eval z = 0 → z ∈ S) ∧
      ∀ z, z ∉ S → pathSum γ s f z = P.eval z / Q.eval z := by
  change RationalWithPoles S (pathSum γ s f)
  unfold pathSum Stieltjes.taggedSum
  apply rational_sum
  intro i _
  have htag := SingleVariableAnalysis.Stieltjes.tag_mem_interval s.1 s.2 i
  have hr := rational_resolvent (hγ ⟨s.2 i, htag, rfl⟩)
    (f (γ (s.2 i)) * (γ (s.1.point i.succ) - γ (s.1.point i.castSucc)))
  convert hr using 1
  funext z
  exact div_mul_eq_mul_div ..

theorem cycleSum_rational (Γ : IntegralCycle) (s : CycleSampling Γ) (f : ℂ → ℂ) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ (∀ z, Q.eval z = 0 → z ∈ Γ.trace) ∧
      ∀ z, z ∉ Γ.trace → cycleSum Γ s f z = P.eval z / Q.eval z := by
  classical
  apply rational_const_mul (c := (2 * Real.pi * Complex.I : ℂ)⁻¹)
  apply rational_sum
  intro γ _
  apply rational_const_mul
  exact pathSum_rational Γ.trace γ.val (s γ) f
    (fun z hz => ⟨γ.val, γ.property, hz⟩)

/-- Subtype sums retain exactly the active integer coefficients. -/
theorem cycle_integral_sum (Γ : IntegralCycle) (g : ℂ → ℂ) :
    Γ.integral g = ∑ γ : {γ : PiecewiseC1Path // γ ∈ Γ.chain.support},
      (Γ.chain γ.val : ℂ) * γ.val.integral g := by
  classical
  exact (Finset.sum_coe_sort Γ.chain.support
    (fun γ => (Γ.chain γ : ℂ) * γ.integral g)).symm

private theorem sup_error_lt (K : Set ℂ) (g : ℂ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hg : ∀ z ∈ K, g z ≤ ε / 2) :
    sSup (g '' K) < ε := by
  by_cases hK : K.Nonempty
  · apply lt_of_le_of_lt (csSup_le (hK.image g) ?_) (by linarith : ε / 2 < ε)
    rintro _ ⟨z, hz, rfl⟩
    exact hg z hz
  · have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
    simp [he, hε]

theorem cycle_sums_approximate :
    Specs.D12Complex.Ch15.RationalRiemannSums.cycle_sums_approximate_type := by
  classical
  intro K Γ f hK hf hd ε hε
  let A := {γ : PiecewiseC1Path // γ ∈ Γ.chain.support}
  let c : ℂ := (2 * Real.pi * Complex.I : ℂ)⁻¹
  let W : ℝ := ∑ γ : A, ‖(Γ.chain γ.val : ℂ)‖
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let τ : ℝ := (ε / 2) / ((‖c‖ + 1) * (W + 1))
  have hτ : 0 < τ := div_pos (half_pos hε) (by positivity)
  have hsample : ∀ γ : A, ∃ s : PathSampling γ.val, ∀ z ∈ K,
      ‖pathSum γ.val s f z - γ.val.integral (fun w => f w / (w - z))‖ < τ := by
    intro γ
    have htrace : γ.val.trace ⊆ Γ.trace := fun z hz => ⟨γ.val, γ.property, hz⟩
    obtain ⟨δ, hδ, hgood⟩ := uniform_path_sums K γ.val f hK
      (hf.mono htrace) (hd.mono_right htrace) τ hτ
    obtain ⟨P, hP⟩ := SingleVariableAnalysis.Stieltjes.exists_mesh_lt γ.val.path.ordered hδ
    obtain ⟨tags⟩ := SingleVariableAnalysis.Riemann.tags_exist P
    exact ⟨⟨P, tags⟩, hgood P hP tags⟩
  choose s hs using hsample
  obtain ⟨P, Q, hQ, hroots, heq⟩ := cycleSum_rational Γ s f
  have hbound : ∀ z ∈ K, ‖cauchyTransform Γ f z - P.eval z / Q.eval z‖ ≤ ε / 2 := by
    intro z hz
    have hzt : z ∉ Γ.trace := fun ht => disjoint_left.mp hd hz ht
    rw [← heq z hzt]
    unfold cauchyTransform cycleSum
    rw [cycle_integral_sum, ← mul_sub, norm_mul, ← Finset.sum_sub_distrib]
    have hsum : ‖∑ γ : A, ((Γ.chain γ.val : ℂ) *
          γ.val.integral (fun w => f w / (w - z)) -
          (Γ.chain γ.val : ℂ) * pathSum γ.val (s γ) f z)‖ ≤ W * τ := by
      calc
        _ ≤ ∑ γ : A, ‖(Γ.chain γ.val : ℂ) *
            γ.val.integral (fun w => f w / (w - z)) -
            (Γ.chain γ.val : ℂ) * pathSum γ.val (s γ) f z‖ := norm_sum_le _ _
        _ ≤ ∑ γ : A, ‖(Γ.chain γ.val : ℂ)‖ * τ := by
          apply Finset.sum_le_sum
          intro γ _
          rw [← mul_sub, norm_mul, norm_sub_rev]
          exact mul_le_mul_of_nonneg_left (hs γ z hz).le (norm_nonneg _)
        _ = W * τ := (Finset.sum_mul ..).symm
    have hscale : ‖c‖ * (W * τ) ≤ ε / 2 := by
      have he : τ * ((‖c‖ + 1) * (W + 1)) = ε / 2 :=
        div_mul_cancel₀ _ (by positivity)
      have hcc : 0 ≤ ‖c‖ := norm_nonneg _
      nlinarith [mul_nonneg hτ.le hW, mul_nonneg hτ.le hcc]
    exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg c)).trans hscale
  exact ⟨s, P, Q, hQ, hroots, heq, hbound, sup_error_lt K _ hε hbound⟩

theorem rational_riemann_approximation :
    Specs.D12Complex.Ch15.RationalRiemannSums.rational_riemann_approximation_type := by
  intro K U f hK hU hKU hf ε hε
  obtain ⟨Γ, hpoly, htrace, hsep, hzero, hrep⟩ :=
    PolygonRepresentation.polygon_representation K U f hK hU hKU hf
  have hd : Disjoint K Γ.trace := disjoint_left.mpr (fun z hz ht => (htrace ht).2 hz)
  have hc : ContinuousOn f Γ.trace := fun z hz =>
    (hf.2 z (htrace hz).1).continuousAt.continuousWithinAt
  obtain ⟨s, P, Q, hQ, hroots, heq, hbound, _⟩ :=
    cycle_sums_approximate K Γ f hK hc hd ε hε
  have hb : ∀ z ∈ K, ‖f z - P.eval z / Q.eval z‖ ≤ ε / 2 := by
    intro z hz
    rw [hrep z hz]
    exact hbound z hz
  exact ⟨Γ, s, P, Q, hpoly, htrace, hsep, hzero, hQ, hroots, heq,
    hb, sup_error_lt K _ hε hb⟩

end D12Complex.RationalRiemannSums
