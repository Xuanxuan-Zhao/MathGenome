import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.PrincipalValues
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.OscillatoryIntegrals
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.FiniteDeletedLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.IndentedHalfDisk
import Mathlib.Analysis.Complex.RemovableSingularity
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter MeasureTheory Metric Asymptotics
open scoped Topology BigOperators

namespace D12Complex.PrincipalValues

abbrev realPoles := Definitions.realPoles
abbrev deletionFilter := Definitions.deletionFilter
abbrev deletedSet := Definitions.deletedSet
abbrev deletedIntegral := Definitions.deletedIntegral
abbrev HasPrincipalValue := Definitions.HasPrincipalValue

lemma denominator_ne_zero (P Q : Polynomial ℂ) (hproper : P.degree < Q.degree) : Q ≠ 0 := by
  intro h
  simp [h] at hproper

lemma mem_realPoles {Q : Polynomial ℂ} (hQ : Q ≠ 0) (x : ℝ) :
    x ∈ realPoles Q ↔ Q.eval (x : ℂ) = 0 := by
  classical
  simp only [realPoles, Definitions.realPoles, Finset.mem_image, Finset.mem_filter,
    Multiset.mem_toFinset, Polynomial.mem_roots hQ, Polynomial.IsRoot]
  constructor
  · rintro ⟨z, ⟨hz, him⟩, hre⟩
    have he : (x : ℂ) = z := by apply Complex.ext <;> simp_all
    simpa [he] using hz
  · intro hx
    exact ⟨(x : ℂ), ⟨hx, by simp⟩, by simp⟩

lemma isCompact_deletedSet (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ) :
    IsCompact (deletedSet s l u ε) := by
  exact isCompact_Icc.diff (isOpen_iUnion fun _ => isOpen_Ioo)

lemma pole_notMem_deletedSet (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ)
    (hε : ∀ a, 0 < ε a) (a : s) : a.val ∉ deletedSet s l u ε := by
  rintro ⟨_, ha⟩
  apply ha
  exact mem_iUnion.mpr ⟨a, by constructor <;> linarith [hε a]⟩

lemma quotient_continuousOn_deletedSet (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (l u : ℝ) (ε : realPoles Q → ℝ) (hε : ∀ a, 0 < ε a) :
    ContinuousOn (fun x : ℝ => P.eval (x : ℂ) / Q.eval (x : ℂ))
      (deletedSet (realPoles Q) l u ε) := by
  apply ((P.continuous.comp Complex.continuous_ofReal).continuousOn).div
    ((Q.continuous.comp Complex.continuous_ofReal).continuousOn)
  intro x hx hzero
  exact pole_notMem_deletedSet (realPoles Q) l u ε hε
    ⟨x, (mem_realPoles hQ x).mpr hzero⟩ hx

lemma oscillatory_integrableOn_deletedSet (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (c l u : ℝ) (ε : realPoles Q → ℝ) (hε : ∀ a, 0 < ε a) :
    IntegrableOn (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * (P.eval (x : ℂ) / Q.eval (x : ℂ)))
      (deletedSet (realPoles Q) l u ε) := by
  apply ContinuousOn.integrableOn_compact (isCompact_deletedSet _ _ _ _)
  exact (by fun_prop : Continuous (fun x : ℝ =>
    Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)))).continuousOn.mul
      (quotient_continuousOn_deletedSet P Q hQ l u ε hε)

end D12Complex.PrincipalValues

namespace D12Complex.PrincipalValues

/-- Upper arc traversed counterclockwise from `a+r` to `a-r`.
The negative of this integral is the clockwise indentation. -/
def upperArcIntegral (f : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..Real.pi,
    f (circleMap a r t) * (circleMap 0 r t * Complex.I)

lemma upperArcIntegral_principal_part (A a : ℂ) (r : ℝ) (hr : r ≠ 0) :
    upperArcIntegral (fun z => A / (z-a)) a r = (Real.pi * Complex.I : ℂ) * A := by
  have h (t : ℝ) :
      A / (circleMap a r t - a) * (circleMap 0 r t * Complex.I) = A * Complex.I := by
    rw [circleMap_sub_center]
    have hn : circleMap 0 r t ≠ 0 := by simpa using (circleMap_ne_center (c := 0) hr (θ := t))
    field_simp
  simp only [upperArcIntegral, h, intervalIntegral.integral_const, sub_zero,
    Complex.real_smul]
  ring

/-- The regular part contributes zero as the indentation shrinks.
Only continuity at the center is needed, not holomorphy. -/
lemma upperArcIntegral_tendsto_zero {h : ℂ → ℂ} {a : ℂ} (hh : ContinuousAt h a) :
    Tendsto (upperArcIntegral h a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp
    (hh.norm.eventually (gt_mem_nhds (lt_add_one ‖h a‖)))
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ‖upperArcIntegral h a r‖ ≤ (‖h a‖ + 1) * r * Real.pi := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with r hr hrδ
    have hrpos : 0 < r := hr
    apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := (‖h a‖ + 1) * r) ?_) ?_
    · intro t _
      rw [norm_mul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
        abs_of_pos hrpos]
      have hz : dist (circleMap a r t) a < δ := by
        simpa only [Complex.dist_eq, circleMap_sub_center, norm_circleMap_zero,
          abs_of_pos hrpos] using (show r < δ from hrδ)
      exact mul_le_mul_of_nonneg_right (le_of_lt (hb hz)) hrpos.le
    · simp only [sub_zero, abs_of_pos Real.pi_pos]
      exact le_rfl
  refine squeeze_zero_norm' hbound ?_
  simpa only [zero_mul, mul_zero, id_eq] using
    ((tendsto_const_nhds (x := ‖h a‖ + 1)).mul
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0))).mul_const Real.pi


open private factor_simple_zero from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueComputation

lemma simple_quotient_decomposition (f p q : ℂ → ℂ) (a : ℂ) (U : Set ℂ)
    (ha : a ∈ U) (hp : HolomorphicOn U p) (hq : HolomorphicOn U q)
    (hq0 : q a = 0) (hq' : deriv q a ≠ 0)
    (hf : ∀ᶠ z in 𝓝[≠] a, f z = p z / q z) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      ∀ᶠ z in 𝓝[≠] a, f z = Residue.residue f a / (z-a) + h z := by
  obtain ⟨q₁, hq₁, hq₁a, heq⟩ := factor_simple_zero q a U ha hq hq0 hq'
  have hpana := (LocalZeroFactorization.holomorphicNear_iff_analyticAt p a).mp ⟨U, ha, hp⟩
  have hq₁ana := (LocalZeroFactorization.holomorphicNear_iff_analyticAt q₁ a).mp hq₁
  let g : ℂ → ℂ := fun z => p z / q₁ z
  have hg : AnalyticAt ℂ g a := hpana.div hq₁ana (by simpa only [hq₁a] using hq')
  obtain ⟨V, haV, hV⟩ := (LocalZeroFactorization.holomorphicNear_iff_analyticAt g a).mpr hg
  have hd : DifferentiableOn ℂ (dslope g a) V :=
    (Complex.differentiableOn_dslope (hV.1.mem_nhds haV)).mpr
      (fun z hz => (hV.2 z hz).differentiableWithinAt)
  have hh : AnalyticAt ℂ (dslope g a) a :=
    (hd.analyticOnNhd hV.1) a haV
  refine ⟨dslope g a, hh, ?_⟩
  have hres := ResidueComputation.residue_simple_quotient f p q a U ha hp hq hq0 hq' hf
  filter_upwards [hf, heq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hfz hqz hza
  rw [hres, dslope_of_ne _ hza, slope_def_field]
  change f z = p a / deriv q a / (z-a) + (g z - g a) / (z-a)
  rw [hfz, hqz]
  dsimp [g]
  rw [hq₁a]
  simp only [div_eq_mul_inv, mul_inv]
  ring

lemma upperArcIntegral_tendsto_of_decomposition
    (f h : ℂ → ℂ) (a A : ℂ) (hh : AnalyticAt ℂ h a)
    (heq : ∀ᶠ z in 𝓝[≠] a, f z = A / (z-a) + h z) :
    Tendsto (upperArcIntegral f a) (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.pi * Complex.I : ℂ) * A)) := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.mem_nhdsWithin_iff.mp heq
  obtain ⟨η, hη, hCont⟩ := Metric.eventually_nhds_iff.mp
    (hh.eventually_analyticAt.mono fun _ hz => hz.continuousAt)
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      upperArcIntegral f a r = (Real.pi * Complex.I : ℂ) * A + upperArcIntegral h a r := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδ),
      nhdsWithin_le_nhds (Iio_mem_nhds hη)] with r hr hrδ hrη
    have hrpos : 0 < r := hr
    have hdist (t : ℝ) : dist (circleMap a r t) a = r := by
      simp [Complex.dist_eq, abs_of_pos hrpos]
    have hident (t : ℝ) :
        f (circleMap a r t) * (circleMap 0 r t * Complex.I) =
          A * Complex.I + h (circleMap a r t) * (circleMap 0 r t * Complex.I) := by
      rw [hEq ⟨mem_ball.mpr (by rw [hdist]; exact hrδ), circleMap_ne_center hrpos.ne'⟩]
      have hn : circleMap 0 r t ≠ 0 := by simpa using circleMap_ne_center (c := 0) hrpos.ne' (θ := t)
      rw [add_mul, circleMap_sub_center]
      congr 1
      field_simp
    have hhc : ContinuousOn (fun t : ℝ => h (circleMap a r t) *
        (circleMap 0 r t * Complex.I)) (uIcc 0 Real.pi) := by
      intro t _
      apply ContinuousAt.continuousWithinAt
      exact ((hCont (by rw [hdist]; exact hrη)).comp
        (continuous_circleMap a r).continuousAt).mul
          ((continuous_circleMap 0 r).continuousAt.mul_const _)
    change (∫ t in (0 : ℝ)..Real.pi, _) = _
    simp_rw [hident]
    rw [intervalIntegral.integral_add (intervalIntegrable_const) hhc.intervalIntegrable,
      intervalIntegral.integral_const]
    simp only [sub_zero, Complex.real_smul]
    congr 1
    ring
  have ht := (tendsto_const_nhds (x := (Real.pi * Complex.I : ℂ) * A)).add
    (upperArcIntegral_tendsto_zero hh.continuousAt)
  simpa only [add_zero] using ht.congr' (EventuallyEq.symm hevent)

/-- A clockwise upper indentation has the minus half-residue sign. -/
lemma clockwise_indentation_tendsto (f p q : ℂ → ℂ) (a : ℂ) (U : Set ℂ)
    (ha : a ∈ U) (hp : HolomorphicOn U p) (hq : HolomorphicOn U q)
    (hq0 : q a = 0) (hq' : deriv q a ≠ 0)
    (hf : ∀ᶠ z in 𝓝[≠] a, f z = p z / q z) :
    Tendsto (fun r => -upperArcIntegral f a r) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi * Complex.I : ℂ) * Residue.residue f a)) := by
  obtain ⟨h, hh, heq⟩ := simple_quotient_decomposition f p q a U ha hp hq hq0 hq' hf
  simpa only [neg_mul] using
    (upperArcIntegral_tendsto_of_decomposition f h a (Residue.residue f a) hh heq).neg

/-- Polynomial quotients at simple real poles satisfy the local decomposition
used for both their principal values and their indentation limits. -/
lemma rational_real_pole_decomposition (P Q : Polynomial ℂ) (c a : ℝ)
    (hQa : Q.eval (a : ℂ) = 0) (hQ'a : Q.derivative.eval (a : ℂ) ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h (a : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (a : ℂ),
        Complex.exp (Complex.I * (c : ℂ) * z) * (P.eval z / Q.eval z) =
          Residue.residue (fun z => Complex.exp (Complex.I * (c : ℂ) * z) *
            (P.eval z / Q.eval z)) (a : ℂ) / (z - (a : ℂ)) + h z := by
  apply simple_quotient_decomposition _
    (fun z => Complex.exp (Complex.I * (c : ℂ) * z) * P.eval z)
    (fun z => Q.eval z) (a : ℂ) univ (mem_univ _)
  · exact ⟨isOpen_univ, by intro z _; fun_prop⟩
  · exact ⟨isOpen_univ, fun z _ => Q.differentiableAt⟩
  · exact hQa
  · simpa only [(Q.hasDerivAt (a : ℂ)).deriv] using hQ'a
  · exact Eventually.of_forall fun z => by ring


lemma symmetric_principal_part_cancel (A : ℂ) (a δ ε : ℝ) :
    (∫ x in (a-δ)..(a-ε), A / ((x : ℂ) - (a : ℂ))) +
      (∫ x in (a+ε)..(a+δ), A / ((x : ℂ) - (a : ℂ))) = 0 := by
  let g : ℝ → ℂ := fun x => A / (x : ℂ)
  have hl := intervalIntegral.integral_comp_sub_right (a := a-δ) (b := a-ε) g a
  have hr := intervalIntegral.integral_comp_sub_right (a := a+ε) (b := a+δ) g a
  have hn := intervalIntegral.integral_comp_neg (a := ε) (b := δ) g
  simp only [g, Complex.ofReal_neg, div_neg, intervalIntegral.integral_neg] at hn
  simp only [g, Complex.ofReal_sub] at hl hr
  simp only [sub_sub_cancel_left, add_sub_cancel_left] at hl hr
  rw [hl, hr, ← hn]
  simp

/-- Local principal-value convergence from a continuous regular remainder.
This statement uses two actual interval integrals, both avoiding the pole. -/
lemma symmetric_deleted_tendsto_of_continuous_remainder
    (f h : ℝ → ℂ) (A : ℂ) (a δ : ℝ) (hδ : 0 < δ)
    (hh : Continuous h)
    (heq : ∀ x ∈ Icc (a-δ) (a+δ), x ≠ a → f x = A / ((x : ℂ)-(a : ℂ)) + h x) :
    Tendsto (fun ε : ℝ => (∫ x in (a-δ)..(a-ε), f x) +
      (∫ x in (a+ε)..(a+δ), f x)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in (a-δ)..(a+δ), h x)) := by
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < δ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
    exact ⟨hε, hεδ⟩
  have hident : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (∫ x in (a-δ)..(a-ε), f x) + (∫ x in (a+ε)..(a+δ), f x) =
        (∫ x in (a-δ)..(a-ε), h x) + (∫ x in (a+ε)..(a+δ), h x) := by
    filter_upwards [hpos] with ε hε
    have hleft : a - δ ≤ a - ε := by linarith [hε.2]
    have hright : a + ε ≤ a + δ := by linarith [hε.2]
    have hle (x : ℝ) (hx : x ∈ uIcc (a-δ) (a-ε)) :
        f x = A / ((x : ℂ) - (a : ℂ)) + h x := by
      rw [uIcc_of_le hleft] at hx
      apply heq x ⟨hx.1, by linarith [hx.2, hε.1]⟩
      linarith [hx.2, hε.1]
    have hre (x : ℝ) (hx : x ∈ uIcc (a+ε) (a+δ)) :
        f x = A / ((x : ℂ) - (a : ℂ)) + h x := by
      rw [uIcc_of_le hright] at hx
      apply heq x ⟨by linarith [hx.1, hε.1], hx.2⟩
      linarith [hx.1, hε.1]
    have hc_left : ContinuousOn (fun x : ℝ => A / ((x : ℂ) - (a : ℂ)))
        (uIcc (a-δ) (a-ε)) := by
      apply continuousOn_const.div (Complex.continuous_ofReal.sub continuous_const).continuousOn
      intro x hx
      rw [uIcc_of_le hleft] at hx
      apply sub_ne_zero.mpr
      intro he
      have he' : x = a := Complex.ofReal_injective he
      linarith [hx.2, hε.1]
    have hc_right : ContinuousOn (fun x : ℝ => A / ((x : ℂ) - (a : ℂ)))
        (uIcc (a+ε) (a+δ)) := by
      apply continuousOn_const.div (Complex.continuous_ofReal.sub continuous_const).continuousOn
      intro x hx
      rw [uIcc_of_le hright] at hx
      apply sub_ne_zero.mpr
      intro he
      have he' : x = a := Complex.ofReal_injective he
      linarith [hx.1, hε.1]
    rw [intervalIntegral.integral_congr hle, intervalIntegral.integral_congr hre,
      intervalIntegral.integral_add hc_left.intervalIntegrable (hh.intervalIntegrable _ _),
      intervalIntegral.integral_add hc_right.intervalIntegrable (hh.intervalIntegrable _ _)]
    linear_combination symmetric_principal_part_cancel A a δ ε
  have hprim : Continuous (fun b => ∫ x in (a-δ)..b, h x) :=
    intervalIntegral.continuous_primitive (fun a b => hh.intervalIntegrable a b) (a-δ)
  have hprim' : Continuous (fun b => ∫ x in (a+δ)..b, h x) :=
    intervalIntegral.continuous_primitive (fun a b => hh.intervalIntegrable a b) (a+δ)
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun ε : ℝ => a-ε) (𝓝[>] 0) (𝓝 a) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := a)).sub heps
  have hr : Tendsto (fun ε : ℝ => a+ε) (𝓝[>] 0) (𝓝 a) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := a)).add heps
  have hlimit := (hprim.tendsto a |>.comp hl).add ((hprim'.tendsto a |>.comp hr).neg)
  simp only [Function.comp_apply, ← intervalIntegral.integral_symm] at hlimit
  rw [intervalIntegral.integral_add_adjacent_intervals (hh.intervalIntegrable _ _)
    (hh.intervalIntegrable _ _)] at hlimit
  exact hlimit.congr' (EventuallyEq.symm hident)

/-- Existence of the local symmetric limit for an actual analytic germ.
The remainder need not be defined continuously away from that germ. -/
lemma local_principal_value_of_decomposition
    (f h : ℂ → ℂ) (a : ℝ) (A : ℂ) (hh : AnalyticAt ℂ h (a : ℂ))
    (heq : ∀ᶠ z in 𝓝[≠] (a : ℂ), f z = A / (z-(a : ℂ)) + h z) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℂ,
      Tendsto (fun ε : ℝ => (∫ x in (a-δ)..(a-ε), f (x : ℂ)) +
        (∫ x in (a+ε)..(a+δ), f (x : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  obtain ⟨η, hη, hCont⟩ := Metric.eventually_nhds_iff.mp
    (hh.eventually_analyticAt.mono fun _ hz => hz.continuousAt)
  obtain ⟨β, hβ, hEq⟩ := Metric.mem_nhdsWithin_iff.mp heq
  let δ := min η β / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ < η := by dsimp [δ]; linarith [min_le_left η β]
  have hδβ : δ < β := by dsimp [δ]; linarith [min_le_right η β]
  have hle : a - δ ≤ a + δ := by linarith
  have hdist (x : ℝ) (hx : x ∈ Icc (a-δ) (a+δ)) :
      dist (x : ℂ) (a : ℂ) ≤ δ := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hhc : ContinuousOn (fun x : ℝ => h (x : ℂ)) (Icc (a-δ) (a+δ)) := by
    intro x hx
    exact ((hCont ((hdist x hx).trans_lt hδη)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  let H : ℝ → ℂ := IccExtend hle (fun x : Icc (a-δ) (a+δ) => h (x.val : ℂ))
  have hH : Continuous H := hhc.domRestrict.Icc_extend'
  have hHeq (x : ℝ) (hx : x ∈ Icc (a-δ) (a+δ)) : H x = h (x : ℂ) :=
    IccExtend_of_mem hle _ hx
  refine ⟨δ, hδ, ∫ x in (a-δ)..(a+δ), H x, ?_⟩
  apply symmetric_deleted_tendsto_of_continuous_remainder (fun x => f (x : ℂ)) H A a δ hδ hH
  intro x hx hxa
  rw [hHeq x hx]
  exact hEq ⟨mem_ball.mpr ((hdist x hx).trans_lt hδβ),
    fun he => hxa (Complex.ofReal_injective he)⟩


lemma principal_value_unique (f : ℝ → ℂ) (s : Finset ℝ) (L M : ℂ)
    (hL : HasPrincipalValue f s L) (hM : HasPrincipalValue f s M) : L = M := by
  classical
  let B := (∑ a ∈ s, |a|) + 1
  have hB : 0 < B := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun a _ => abs_nonneg a) zero_lt_one
  have hbound : ∀ a ∈ s, -B < a ∧ a < B := by
    intro a ha
    have habs := Finset.single_le_sum (fun b (_ : b ∈ s) => abs_nonneg b) ha
    dsimp [B]
    constructor <;> linarith [neg_abs_le a, le_abs_self a]
  obtain ⟨Lm, L0, Lp, hm, h0, hp, hsum⟩ := (hL (-B) B (by linarith) hbound).2.2.2
  obtain ⟨Mm, M0, Mp, hm', h0', hp', hsum'⟩ := (hM (-B) B (by linarith) hbound).2.2.2
  have hem : Lm = Mm := tendsto_nhds_unique hm hm'
  haveI : (Definitions.deletionFilter s).NeBot := by
    apply Filter.pi_neBot.mpr
    intro a
    infer_instance
  have he0 : L0 = M0 := tendsto_nhds_unique h0 h0'
  have hep : Lp = Mp := tendsto_nhds_unique hp hp'
  rw [← hsum, ← hsum', hem, he0, hep]

set_option maxHeartbeats 800000 in
lemma rational_local_principal_value_exists (P Q : Polynomial ℂ) (c a : ℝ)
    (hQa : Q.eval (a : ℂ) = 0) (hQ'a : Q.derivative.eval (a : ℂ) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℂ,
      Tendsto (fun ε : ℝ =>
        (∫ x in (a-δ)..(a-ε), Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ))) +
        (∫ x in (a+ε)..(a+δ), Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ)))) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  obtain ⟨h, hh, heq⟩ := rational_real_pole_decomposition P Q c a hQa hQ'a
  exact local_principal_value_of_decomposition _ h a _ hh heq

/-- Analytic local decompositions supply the finite localization hypotheses. -/
lemma real_local_decomposition (f h : ℂ → ℂ) (a : ℝ) (A : ℂ)
    (hh : AnalyticAt ℂ h (a : ℂ))
    (heq : ∀ᶠ z in 𝓝[≠] (a : ℂ), f z = A / (z-(a : ℂ)) + h z) :
    ∃ δ : ℝ, ∃ H : ℝ → ℂ, 0 < δ ∧ ContinuousOn H (Icc (a-δ) (a+δ)) ∧
      ∀ x ∈ Icc (a-δ) (a+δ), x ≠ a →
        f (x : ℂ) = A / ((x : ℂ)-(a : ℂ)) + H x := by
  obtain ⟨η, hη, hCont⟩ := Metric.eventually_nhds_iff.mp
    (hh.eventually_analyticAt.mono fun _ hz => hz.continuousAt)
  obtain ⟨β, hβ, hEq⟩ := Metric.mem_nhdsWithin_iff.mp heq
  let δ := min η β / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ < η := by dsimp [δ]; linarith [min_le_left η β]
  have hδβ : δ < β := by dsimp [δ]; linarith [min_le_right η β]
  have hdist (x : ℝ) (hx : x ∈ Icc (a-δ) (a+δ)) :
      dist (x : ℂ) (a : ℂ) ≤ δ := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨δ, fun x => h (x : ℂ), hδ, ?_, ?_⟩
  · intro x hx
    exact ((hCont ((hdist x hx).trans_lt hδη)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  · intro x hx hxa
    exact hEq ⟨mem_ball.mpr ((hdist x hx).trans_lt hδβ),
      fun he => hxa (Complex.ofReal_injective he)⟩

lemma rational_middle_limit (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hsimple : ∀ a : ℝ, Q.eval (a : ℂ) = 0 → Q.derivative.eval (a : ℂ) ≠ 0)
    (c l u : ℝ) (hlu : l < u) (hinside : ∀ a ∈ realPoles Q, l < a ∧ a < u) :
    ∃ L : ℂ, Tendsto (deletedIntegral (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * (P.eval (x : ℂ) / Q.eval (x : ℂ)))
        (realPoles Q) l u) (deletionFilter (realPoles Q)) (𝓝 L) := by
  apply (FiniteDeletedLimits.finite_deleted_limits (realPoles Q) l u _ hlu hinside ?_ ?_).2
  · apply (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)))).continuousOn.mul
    apply (P.continuous.comp Complex.continuous_ofReal).continuousOn.div
      (Q.continuous.comp Complex.continuous_ofReal).continuousOn
    intro x hx hzero
    exact hx.2 ((mem_realPoles hQ x).mpr hzero)
  · intro a ha
    have hQa := (mem_realPoles hQ a).mp ha
    obtain ⟨h, hh, heq⟩ := rational_real_pole_decomposition P Q c a hQa (hsimple a hQa)
    obtain ⟨δ, H, hδ, hH, hEq⟩ := real_local_decomposition _ h a _ hh heq
    exact ⟨δ, _, H, hδ, hH, hEq⟩

/-- Integration by parts only requires regularity on the actual interval. -/
lemma integration_by_parts_on (g g' : ℝ → ℂ) (a b c : ℝ) (hc : c ≠ 0)
    (hd : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x)
    (hcont : ContinuousOn g' (uIcc a b)) :
    (∫ x in a..b, Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * g x) =
      (Complex.exp (Complex.I * (c : ℂ) * (b : ℂ)) * g b -
        Complex.exp (Complex.I * (c : ℂ) * (a : ℂ)) * g a -
          ∫ x in a..b, Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * g' x) /
        (Complex.I * (c : ℂ)) := by
  let E : ℝ → ℂ := fun x => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))
  have hg : ContinuousOn g (uIcc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have he : Continuous E := by dsimp [E]; fun_prop
  have hprod := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x (_ : x ∈ uIcc a b) => OscillatoryIntegrals.exp_real_frequency_hasDerivAt c x)
    hd ((he.mul_const (Complex.I * (c : ℂ))).intervalIntegrable a b)
    hcont.intervalIntegrable
  have hint : (∫ x in a..b, E x * (Complex.I * (c : ℂ)) * g x + E x * g' x) =
      (Complex.I * (c : ℂ)) * (∫ x in a..b, E x * g x) +
        (∫ x in a..b, E x * g' x) := by
    rw [intervalIntegral.integral_add
      (f := fun x => E x * (Complex.I * (c : ℂ)) * g x)
      (g := fun x => E x * g' x)
      (((he.mul_const _).continuousOn.mul hg).intervalIntegrable)
      ((he.continuousOn.mul hcont).intervalIntegrable)]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hint] at hprod
  apply (eq_div_iff (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc))).mpr
  change (∫ x in a..b, E x * g x) * (Complex.I * (c : ℂ)) = _
  linear_combination hprod

lemma rational_continuousOn (P Q : Polynomial ℂ) (s : Set ℝ)
    (hs : ∀ x ∈ s, Q.eval (x : ℂ) ≠ 0) :
    ContinuousOn (fun x : ℝ => P.eval (x : ℂ) / Q.eval (x : ℂ)) s :=
  (P.continuous.comp Complex.continuous_ofReal).continuousOn.div
    (Q.continuous.comp Complex.continuous_ofReal).continuousOn hs

set_option maxHeartbeats 2000000 in
lemma rational_tails_outside_poles (P Q : Polynomial ℂ) (hproper : P.degree < Q.degree)
    (c : ℝ) (hc : c ≠ 0) (l u : ℝ)
    (hl : ∀ x ≤ l, Q.eval (x : ℂ) ≠ 0)
    (hu : ∀ x, u ≤ x → Q.eval (x : ℂ) ≠ 0) :
    (∀ a ≤ l, IntervalIntegrable (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * (P.eval (x : ℂ) / Q.eval (x : ℂ))) volume a l) ∧
    (∀ b, u ≤ b → IntervalIntegrable (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * (P.eval (x : ℂ) / Q.eval (x : ℂ))) volume u b) ∧
    ∃ Lminus Lplus : ℂ,
      Tendsto (fun a : ℝ => ∫ x in a..l,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * (P.eval (x : ℂ) / Q.eval (x : ℂ))) atBot (𝓝 Lminus) ∧
      Tendsto (fun b : ℝ => ∫ x in u..b,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * (P.eval (x : ℂ) / Q.eval (x : ℂ))) atTop (𝓝 Lplus) := by
  let g : ℝ → ℂ := fun x => P.eval (x : ℂ) / Q.eval (x : ℂ)
  let g' : ℝ → ℂ := fun x =>
    (P.derivative.eval (x : ℂ) * Q.eval (x : ℂ) -
      P.eval (x : ℂ) * Q.derivative.eval (x : ℂ)) / Q.eval (x : ℂ)^2
  let E : ℝ → ℂ := fun x => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hgl : ContinuousOn g (Iic l) := rational_continuousOn P Q _ hl
  have hgu : ContinuousOn g (Ici u) := rational_continuousOn P Q _ hu
  have hd (x : ℝ) (hx : Q.eval (x : ℂ) ≠ 0) : HasDerivAt g (g' x) x :=
    (((P.hasDerivAt (x : ℂ)).div (Q.hasDerivAt (x : ℂ)) hx).comp_ofReal)
  have hcont (s : Set ℝ) (hs : ∀ x ∈ s, Q.eval (x : ℂ) ≠ 0) : ContinuousOn g' s := by
    apply ContinuousOn.div
    · exact ((P.derivative.continuous.comp Complex.continuous_ofReal).continuousOn.mul
        (Q.continuous.comp Complex.continuous_ofReal).continuousOn).sub
          ((P.continuous.comp Complex.continuous_ofReal).continuousOn.mul
            (Q.derivative.continuous.comp Complex.continuous_ofReal).continuousOn)
    · exact (Q.continuous.comp Complex.continuous_ofReal).continuousOn.pow 2
    · exact fun x hx => pow_ne_zero 2 (hs x hx)
  have hbig : g' =O[cocompact ℝ] (fun x : ℝ => (1+x^2)⁻¹) := by
    simpa only [g', Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow] using
      RationalIntegrals.rational_isBigO_cauchy_kernel (P.derivative * Q - P * Q.derivative) (Q^2)
        (OscillatoryIntegrals.rational_derivative_degree_gap P Q hproper)
  have hil : IntegrableOn g' (Iic l) :=
    ((hcont _ hl).locallyIntegrableOn measurableSet_Iic).integrableOn_of_isBigO_atBot
      (hbig.mono atBot_le_cocompact) (integrable_inv_one_add_sq.integrableAtFilter _)
  have hiu : IntegrableOn g' (Ici u) :=
    ((hcont _ hu).locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
      (hbig.mono atTop_le_cocompact) (integrable_inv_one_add_sq.integrableAtFilter _)
  have hiEl : IntegrableOn (fun x => E x * g' x) (Iic l) := by
    apply hil.bdd_mul (c := 1) hE.aestronglyMeasurable
    exact ae_of_all _ fun x => (OscillatoryIntegrals.norm_exp_real_frequency c x).le
  have hiEu : IntegrableOn (fun x => E x * g' x) (Ioi u) := by
    apply (hiu.mono_set Ioi_subset_Ici_self).bdd_mul (c := 1) hE.aestronglyMeasurable
    exact ae_of_all _ fun x => (OscillatoryIntegrals.norm_exp_real_frequency c x).le
  have hz := OscillatoryIntegrals.rational_tendsto_zero P Q hproper
  have hzm := OscillatoryIntegrals.exp_mul_tendsto_zero (hz.mono_left atBot_le_cocompact) c
  have hzp := OscillatoryIntegrals.exp_mul_tendsto_zero (hz.mono_left atTop_le_cocompact) c
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact (hE.continuousOn.mul (hgl.mono (Icc_subset_Iic_self))).intervalIntegrable_of_Icc ha
  · intro b hb
    exact (hE.continuousOn.mul (hgu.mono (Icc_subset_Ici_self))).intervalIntegrable_of_Icc hb
  · have hm := intervalIntegral_tendsto_integral_Iic l hiEl tendsto_id
    have hp := intervalIntegral_tendsto_integral_Ioi u hiEu tendsto_id
    refine ⟨(E l * g l - ∫ x in Iic l, E x * g' x) / (Complex.I * (c : ℂ)),
      (-(E u * g u) - ∫ x in Ioi u, E x * g' x) / (Complex.I * (c : ℂ)), ?_, ?_⟩
    · have ht := (((tendsto_const_nhds (x := E l * g l)).sub hzm).sub hm).div_const (Complex.I * (c : ℂ))
      simp only [id_eq, sub_zero] at ht
      apply ht.congr'
      filter_upwards [eventually_le_atBot l] with a ha
      symm
      exact integration_by_parts_on g g' a l c hc
        (fun x hx => hd x (hl x (by rw [uIcc_of_le ha] at hx; exact hx.2)))
        ((hcont _ hl).mono (by rw [uIcc_of_le ha]; exact Icc_subset_Iic_self))
    · have ht := ((hzp.sub (tendsto_const_nhds (x := E u * g u))).sub hp).div_const (Complex.I * (c : ℂ))
      simp only [id_eq, zero_sub] at ht
      apply ht.congr'
      filter_upwards [eventually_ge_atTop u] with b hb
      symm
      exact integration_by_parts_on g g' u b c hc
        (fun x hx => hd x (hu x (by rw [uIcc_of_le hb] at hx; exact hx.1)))
        ((hcont _ hu).mono (by rw [uIcc_of_le hb]; exact Icc_subset_Ici_self))

/-- Splitting outside the deletion neighborhoods uses ordinary interval integrals. -/
lemma deletedIntegral_split (f : ℝ → ℂ) (s : Finset ℝ) (L l u U : ℝ)
    (hLl : L ≤ l) (hlu : l ≤ u) (huU : u ≤ U) (ε : s → ℝ)
    (hε : ∀ a, l < a.val - ε a ∧ a.val + ε a < u)
    (hi : IntegrableOn f (deletedSet s L U ε)) :
    deletedIntegral f s L U ε =
      (∫ x in L..l, f x) + deletedIntegral f s l u ε + (∫ x in u..U, f x) := by
  let D := deletedSet s l u ε
  have hleft (x : ℝ) (hx : x ≤ l) : x ∉ ⋃ a : s, Ioo (a.val-ε a) (a.val+ε a) := by
    intro h
    obtain ⟨a, ha⟩ := mem_iUnion.mp h
    linarith [(hε a).1, ha.1]
  have hright (x : ℝ) (hx : u ≤ x) : x ∉ ⋃ a : s, Ioo (a.val-ε a) (a.val+ε a) := by
    intro h
    obtain ⟨a, ha⟩ := mem_iUnion.mp h
    linarith [(hε a).2, ha.2]
  have hpart : deletedSet s L U ε = (Ico L l ∪ D) ∪ Ioc u U := by
    ext x
    constructor
    · intro hx
      by_cases hxl : x < l
      · exact Or.inl (Or.inl ⟨hx.1.1, hxl⟩)
      · by_cases hxu : u < x
        · exact Or.inr ⟨hxu, hx.1.2⟩
        · exact Or.inl (Or.inr ⟨⟨le_of_not_gt hxl, le_of_not_gt hxu⟩, hx.2⟩)
    · rintro ((hx | hx) | hx)
      · exact ⟨⟨hx.1, hx.2.le.trans (hlu.trans huU)⟩, hleft x hx.2.le⟩
      · exact ⟨⟨hLl.trans hx.1.1, hx.1.2.trans huU⟩, hx.2⟩
      · exact ⟨⟨hLl.trans (hlu.trans hx.1.le), hx.2⟩, hright x hx.1.le⟩
  have hd₁ : Disjoint (Ico L l) D := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hy.1.1) hx.2
  have hd₂ : Disjoint (Ico L l ∪ D) (Ioc u U) := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx
    · linarith [hx.2, hy.1]
    · linarith [hx.1.2, hy.1]
  have hi₁ : IntegrableOn f (Ico L l ∪ D) :=
    hi.mono_set (by rw [hpart]; exact subset_union_left)
  have hi₂ : IntegrableOn f (Ioc u U) :=
    hi.mono_set (by rw [hpart]; exact subset_union_right)
  have him : IntegrableOn f D := hi₁.mono_set subset_union_right
  have hil : IntegrableOn f (Ico L l) := hi₁.mono_set subset_union_left
  have hmD : MeasurableSet D := measurableSet_Icc.diff (MeasurableSet.iUnion fun _ => measurableSet_Ioo)
  change (∫ x in deletedSet s L U ε, f x) = _
  rw [hpart, setIntegral_union hd₂ measurableSet_Ioc hi₁ hi₂,
    setIntegral_union hd₁ hmD hil him, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hLl, ← intervalIntegral.integral_of_le huU]
  rfl

lemma upperArcIntegral_eq_semicircle (f : ℂ → ℂ) (r : ℝ)
    (hf : ContinuousOn f (JordanEstimate.upperSemicircle r).trace) :
    upperArcIntegral f 0 r = (JordanEstimate.upperSemicircle r).integral f := by
  rw [PiecewiseC1Path.integral_congr_representative
    (JordanEstimate.upperSemicircle r) (circleMap 0 r) f hf (by intro t _; rfl)]
  simp only [JordanEstimate.upperSemicircle, upperArcIntegral, deriv_circleMap]
  rfl

lemma rational_upperArcIntegral_tendsto (P Q : Polynomial ℂ) (hproper : P.degree < Q.degree)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (upperArcIntegral (fun z => Complex.exp (Complex.I * (c : ℂ) * z) *
      (P.eval z / Q.eval z)) 0) atTop (𝓝 0) := by
  classical
  let q : ℂ → ℂ := fun z => P.eval z / Q.eval z
  let f : ℂ → ℂ := fun z => Complex.exp (Complex.I * (c : ℂ) * z) * q z
  have hQ := denominator_ne_zero P Q hproper
  let A := Q.roots.toFinset
  have hlarge : ∀ᶠ r : ℝ in atTop, 0 < r ∧ ∀ a ∈ A, ‖a‖ < r := by
    filter_upwards [eventually_gt_atTop (∑ a ∈ A, ‖a‖)] with r hr
    exact ⟨(Finset.sum_nonneg (fun a _ => norm_nonneg a)).trans_lt hr,
      fun a ha => (Finset.single_le_sum (fun b _ => norm_nonneg b) ha).trans_lt hr⟩
  obtain ⟨C, _, R, _, hdecay⟩ := OscillatoryIntegrals.rational_linear_decay P Q hproper
  refine squeeze_zero_norm' (a := fun r : ℝ => (Real.pi / c) * (C / r)) ?_ ?_
  · filter_upwards [hlarge, eventually_ge_atTop R] with r hr hR
    have hn (z : ℂ) (hz : z ∈ (JordanEstimate.upperSemicircle r).trace) : ‖z‖ = r := by
      obtain ⟨t, _, rfl⟩ := hz
      change ‖circleMap 0 r t‖ = r
      simp [norm_circleMap_zero, abs_of_pos hr.1]
    have hqarc : ContinuousOn q (JordanEstimate.upperSemicircle r).trace := by
      intro z hz
      apply (P.differentiableAt.div Q.differentiableAt ?_).continuousAt.continuousWithinAt
      intro hzero
      have hzA : z ∈ A := by simp [A, Polynomial.mem_roots hQ, Polynomial.IsRoot, hzero]
      exact (ne_of_lt (hr.2 z hzA)) (hn z hz)
    have hfarc : ContinuousOn f (JordanEstimate.upperSemicircle r).trace :=
      (by fun_prop : Continuous (fun z : ℂ =>
        Complex.exp (Complex.I * (c : ℂ) * z))).continuousOn.mul hqarc
    rw [upperArcIntegral_eq_semicircle f r hfarc]
    exact (JordanEstimate.jordan_estimate r c hr.1 hc q hqarc).trans
      (mul_le_mul_of_nonneg_left
        (OscillatoryIntegrals.semicircle_traceSupNorm_le q C R r hr.1 hR hdecay)
        (div_nonneg Real.pi_pos.le hc.le))
  · simpa only [mul_zero] using
      (tendsto_const_nhds (x := Real.pi / c)).mul
        (tendsto_const_nhds.div_atTop tendsto_id :
          Tendsto (fun r : ℝ => C / r) atTop (𝓝 0))

lemma sum_realPoles (Q : Polynomial ℂ) (F : ℂ → ℂ) :
    (∑ a : realPoles Q, F (a.val : ℂ)) =
      ∑ z ∈ Q.roots.toFinset.filter (fun z => z.im = 0), F z := by
  classical
  rw [Finset.sum_coe_sort (realPoles Q) (fun a : ℝ => F (a : ℂ))]
  change (∑ a ∈ (Q.roots.toFinset.filter (fun z => z.im = 0)).image Complex.re,
    F (a : ℂ)) = _
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z hz
    have him := (Finset.mem_filter.mp hz).2
    congr 1
    apply Complex.ext <;> simp [him]
  · intro z hz w hw he
    apply Complex.ext
    · exact he
    · rw [(Finset.mem_filter.mp hz).2, (Finset.mem_filter.mp hw).2]

set_option maxHeartbeats 2400000 in
/-- The independent deletion limits and the two ordinary tails satisfy the residue formula. -/
theorem principal_value_residues :
    Specs.D12Complex.Ch08.PrincipalValues.principal_value_residues_type := by
  classical
  intro P Q _hcoprime hproper hsimple c hc l u hlu hinside
  let f : ℂ → ℂ := fun z => Complex.exp (Complex.I * (c : ℂ) * z) * (P.eval z / Q.eval z)
  let s := realPoles Q
  let A := Q.roots.toFinset
  let U : ℂ := (2 * Real.pi * Complex.I : ℂ) *
    ∑ a ∈ A.filter (fun a => 0 < a.im), Residue.residue f a
  let V : ℂ := (Real.pi * Complex.I : ℂ) *
    ∑ a ∈ A.filter (fun a => a.im = 0), Residue.residue f a
  have hQ := denominator_ne_zero P Q hproper
  have hroot (z : ℂ) : z ∈ A ↔ Q.eval z = 0 := by
    simp [A, Polynomial.mem_roots hQ, Polynomial.IsRoot]
  have hf : HolomorphicOn (univ \ (A : Set ℂ)) f := by
    refine ⟨isOpen_univ.sdiff A.finite_toSet.isClosed, ?_⟩
    intro z hz
    exact (by fun_prop : DifferentiableAt ℂ
      (fun z : ℂ => Complex.exp (Complex.I * (c : ℂ) * z)) z).mul
        (P.differentiableAt.div Q.differentiableAt (fun h => hz.2 ((hroot z).mpr h)))
  have hl : ∀ x ≤ l, Q.eval (x : ℂ) ≠ 0 := by
    intro x hx hzero
    have hin := (hinside x ((mem_realPoles hQ x).mpr hzero)).1
    linarith
  have hu : ∀ x, u ≤ x → Q.eval (x : ℂ) ≠ 0 := by
    intro x hx hzero
    have hin := (hinside x ((mem_realPoles hQ x).mpr hzero)).2
    linarith
  obtain ⟨hleft, hright, Lminus, Lplus, hm, hp⟩ :=
    rational_tails_outside_poles P Q hproper c hc.ne' l u hl hu
  obtain ⟨Lmiddle, hmid⟩ := rational_middle_limit P Q hQ hsimple c l u hlu hinside
  refine ⟨hleft, hright, fun ε hε => oscillatory_integrableOn_deletedSet P Q hQ c l u ε hε,
    Lminus, Lmiddle, Lplus, hm, hmid, hp, ?_⟩
  haveI : (deletionFilter s).NeBot := Filter.pi_neBot.mpr (fun _ => inferInstance)
  have hsum : Tendsto (fun ε : s → ℝ => ∑ a : s, upperArcIntegral f (a.val : ℂ) (ε a))
      (deletionFilter s) (𝓝 V) := by
    have ht : Tendsto (fun ε : s → ℝ => ∑ a : s, upperArcIntegral f (a.val : ℂ) (ε a))
        (deletionFilter s) (𝓝 (∑ a : s, (Real.pi * Complex.I : ℂ) * Residue.residue f (a.val : ℂ))) := by
      apply tendsto_finsetSum
      intro a _
      have ha := (mem_realPoles hQ a.val).mp a.property
      obtain ⟨h, hh, heq⟩ := rational_real_pole_decomposition P Q c a.val ha (hsimple a.val ha)
      exact (upperArcIntegral_tendsto_of_decomposition f h (a.val : ℂ) _ hh heq).comp
        (tendsto_eval_pi _ a)
    simpa only [← Finset.mul_sum, s, sum_realPoles, V, A] using ht
  have hsmall : ∀ᶠ ε : s → ℝ in deletionFilter s,
      ∀ a : s, 0 < ε a ∧ l < a.val - ε a ∧ a.val + ε a < u := by
    change ∀ᶠ ε : s → ℝ in Filter.pi (fun _ : s => 𝓝[>] (0 : ℝ)), _
    refine eventually_pi (f := fun _ : s => 𝓝[>] (0 : ℝ))
      (p := fun a : s => fun ε : ℝ => 0 < ε ∧ l < a.val - ε ∧ a.val + ε < u) (fun a : s => ?_)
    have ha := hinside a.val a.property
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (sub_pos.mpr ha.1)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (sub_pos.mpr ha.2)).filter_mono nhdsWithin_le_nhds] with ε hε hl hu
    exact ⟨hε, by linarith, by linarith⟩
  have hlarge : ∀ᶠ r : ℝ in atTop,
      0 < r ∧ (∀ a ∈ A, ‖a‖ < r) ∧ -r ≤ l ∧ u ≤ r := by
    filter_upwards [eventually_gt_atTop (∑ a ∈ A, ‖a‖),
      eventually_ge_atTop (-l), eventually_ge_atTop u] with r hr hl hu
    exact ⟨(Finset.sum_nonneg (fun a _ => norm_nonneg a)).trans_lt hr,
      (fun a ha => (Finset.single_le_sum (fun b _ => norm_nonneg b) ha).trans_lt hr),
      by linarith, hu⟩
  have heq : ∀ᶠ r : ℝ in atTop,
      (∫ x in (-r)..l, f (x : ℂ)) + Lmiddle + (∫ x in u..r, f (x : ℂ)) +
        upperArcIntegral f 0 r = U + V := by
    filter_upwards [hlarge] with r hr
    obtain ⟨η, hη, hfinite⟩ := IndentedHalfDisk.finite_indented_half_disk A f r hf hr.1 hr.2.1
    have hevent : ∀ᶠ ε : s → ℝ in deletionFilter s,
        (∫ x in (-r)..l, f (x : ℂ)) + deletedIntegral (fun x => f (x : ℂ)) s l u ε +
          (∫ x in u..r, f (x : ℂ)) + upperArcIntegral f 0 r -
          (∑ a : s, upperArcIntegral f (a.val : ℂ) (ε a)) = U := by
      filter_upwards [hsmall, eventually_pi (fun _ : s =>
        (eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds)] with ε hε hηε
      have hfin := (hfinite ε (fun a => ⟨(hε a).1, hηε a⟩)).2.2.2.2
      change deletedIntegral (fun x => f (x : ℂ)) s (-r) r ε + upperArcIntegral f 0 r -
        (∑ a : s, upperArcIntegral f (a.val : ℂ) (ε a)) = U at hfin
      rw [deletedIntegral_split (fun x => f (x : ℂ)) s (-r) l u r hr.2.2.1 hlu.le hr.2.2.2 ε
        (fun a => (hε a).2)
        (oscillatory_integrableOn_deletedSet P Q hQ c (-r) r ε (fun a => (hε a).1))] at hfin
      exact hfin
    have ht := ((((tendsto_const_nhds (x := ∫ x in (-r)..l, f (x : ℂ))).add hmid).add_const
      (∫ x in u..r, f (x : ℂ))).add_const (upperArcIntegral f 0 r)).sub hsum
    have hid := tendsto_nhds_unique ht (tendsto_const_nhds.congr' (EventuallyEq.symm hevent))
    exact sub_eq_iff_eq_add.mp hid
  have htail : Tendsto (fun r : ℝ => (∫ x in (-r)..l, f (x : ℂ)) + Lmiddle +
      (∫ x in u..r, f (x : ℂ)) + upperArcIntegral f 0 r) atTop
      (𝓝 (Lminus + Lmiddle + Lplus)) := by
    simpa only [add_zero, Function.comp_apply, f] using
      (((hm.comp tendsto_neg_atTop_atBot).add_const Lmiddle).add hp).add
        (rational_upperArcIntegral_tendsto P Q hproper c hc)
  exact tendsto_nhds_unique htail (tendsto_const_nhds.congr' (EventuallyEq.symm heq))

end D12Complex.PrincipalValues
