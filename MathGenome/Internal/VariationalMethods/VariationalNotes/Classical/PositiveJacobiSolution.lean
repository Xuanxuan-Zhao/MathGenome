import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.PositiveJacobiSolution
import MathGenome.ODEDynamics.Topics.D13Unified.Ch07
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

noncomputable section
namespace VariationalNotes.Classical.Jacobi
open Set Filter
open scoped Topology

/-- The linear operator of the momentum system. -/
def systemOperator (P V : ℝ → ℝ) (t : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (P t)⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0) +
    V t • ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ))

@[simp] lemma systemOperator_apply (P V : ℝ → ℝ) (t : ℝ) (x : ℝ × ℝ) :
    systemOperator P V t x = (x.2 / P t, V t * x.1) := by
  simp [systemOperator, div_eq_mul_inv, mul_comm]

lemma continuousOn_systemOperator {a b : ℝ} {P V : ℝ → ℝ}
    (hP : ContinuousOn P (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < P t) :
    ContinuousOn (systemOperator P V) (Icc a b) := by
  have hi := hP.inv₀ (fun t ht => ne_of_gt (hpos t ht))
  exact (hi.smul continuousOn_const).add (hV.smul continuousOn_const)

/-- Arbitrary initial position and momentum on the full interval. -/
theorem exists_unique_solution {a b : ℝ} {P V : ℝ → ℝ} (hab : a < b)
    (hP : ContinuousOn P (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < P t) (ξ : ℝ × ℝ) :
    ∃ Y : ℝ → ℝ × ℝ, IsSolution P V a b Y ∧ Y a = ξ ∧
      ∀ Z : ℝ → ℝ × ℝ, IsSolution P V a b Z → Z a = ξ →
        EqOn Z Y (Icc a b) := by
  let I : D13Unified.TimeInterval :=
    ⟨Icc a b, nonempty_Icc.mpr hab.le, ordConnected_Icc⟩
  obtain ⟨Y, hc, hi, hd, _, _, hu⟩ :=
    D13Unified.Ch07.LinearSystemExistence.existence I (systemOperator P V) a ξ
      (left_mem_Icc.mpr hab.le) (continuousOn_systemOperator hP hV hpos)
  refine ⟨Y, ⟨hc, ?_⟩, hi, ?_⟩
  · intro t ht
    simpa using hd t ht
  · intro Z hZ hZa
    apply hu Z hZ.1 hZa
    intro t ht
    simpa using hZ.2 t ht

/-- A nonvanishing scalar field with positive initial derivative keeps its sign. -/
lemma positive_of_no_zero {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0)
    (hd : HasDerivWithinAt f 1 (Icc a b) a)
    (hnz : ∀ t ∈ Ioc a b, f t ≠ 0) : ∀ t ∈ Ioc a b, 0 < f t := by
  intro t ht
  have hs : Tendsto (slope f a) (𝓝[Ioc a b] a) (𝓝 1) := by
    simpa only [Icc_sdiff_left] using hasDerivWithinAt_iff_tendsto_slope.mp hd
  have : (𝓝[Ioc a t] a).NeBot := left_nhdsWithin_Ioc_neBot ht.1
  have hsp : ∀ᶠ u in 𝓝[Ioc a t] a, 0 < slope f a u :=
    (hs.mono_left (nhdsWithin_mono a (Ioc_subset_Ioc le_rfl ht.2))).eventually
      (eventually_gt_nhds zero_lt_one)
  have hh : ∀ᶠ u in 𝓝[Ioc a t] a, u ∈ Ioc a t ∧ 0 < slope f a u := by
    filter_upwards [self_mem_nhdsWithin, hsp] with u hu hp
    exact ⟨hu, hp⟩
  obtain ⟨c, hc, hcs⟩ := hh.exists
  have hfc : 0 < f c := by
    have hdiv : 0 < (f c - f a) / (c - a) := by
      simpa only [slope_def_field] using hcs
    rw [hfa, sub_zero] at hdiv
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hc.1)).mp hdiv
  by_contra h
  have hft : f t ≤ 0 := le_of_not_gt h
  obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hc.2
    (hf.mono (Icc_subset_Icc hc.1.le ht.2)) ⟨hft, hfc.le⟩
  exact hnz z ⟨hc.1.trans_le hz.1, hz.2.trans ht.2⟩ hfz

/-- Compactness gives one perturbation size valid at every point, including
zeros of f, provided g is positive at those zeros. -/
lemma exists_positive_perturbation {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hn : ∀ x, 0 ≤ f x) (hz : ∀ x, f x = 0 → 0 < g x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < f x + ε * g x := by
  have hF : Continuous (fun x => f x + max (g x) 0) :=
    hf.add (hg.max continuous_const)
  have hFpos (x : X) : 0 < f x + max (g x) 0 := by
    by_cases hx : f x = 0
    · rw [hx, zero_add, max_eq_left (hz x hx).le]
      exact hz x hx
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hn x) (Ne.symm hx))
        (le_max_right _ _)
  obtain ⟨m, hm, hmin⟩ := isCompact_univ.exists_forall_le' hF.continuousOn
    (fun x _ => hFpos x)
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hg.abs.continuousOn
  let ε := m / (2 * (max M 0 + 1))
  have hden : 0 < 2 * (max M 0 + 1) := by positivity
  have he : 0 < ε := div_pos hm hden
  have hem : ε * (max M 0 + 1) = m / 2 := by
    dsimp [ε]
    field_simp
  refine ⟨ε, he, fun x => ?_⟩
  have hgM : |g x| ≤ max M 0 :=
    (hM (mem_image_of_mem (fun x => |g x|) (mem_univ x))).trans (le_max_left _ _)
  by_cases hx : 0 ≤ g x
  · by_cases hfx : f x = 0
    · rw [hfx, zero_add]
      exact mul_pos he (hz x hfx)
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hn x) (Ne.symm hfx))
        (mul_nonneg he.le hx)
  · have hfx : m ≤ f x := by
      simpa only [max_eq_right (le_of_not_ge hx), add_zero] using hmin x (mem_univ x)
    have hlow : -(max M 0) ≤ g x := (abs_le.mp hgM).1
    have hmul := mul_le_mul_of_nonneg_left hlow he.le
    nlinarith [le_max_right M 0]

/-- The velocity of the first coordinate is q/P. -/
lemma IsSolution.hasDerivWithinAt_fst {P V : ℝ → ℝ} {a b t : ℝ}
    {Y : ℝ → ℝ × ℝ} (hY : IsSolution P V a b Y) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => (Y s).1) ((Y t).2 / P t) (Icc a b) t := by
  convert (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t
    (hY.2 t ht) using 1 <;> rfl

/-- The momentum derivative is Vv. -/
lemma IsSolution.hasDerivWithinAt_snd {P V : ℝ → ℝ} {a b t : ℝ}
    {Y : ℝ → ℝ × ℝ} (hY : IsSolution P V a b Y) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => (Y s).2) (V t * (Y t).1) (Icc a b) t := by
  convert (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t
    (hY.2 t ht) using 1 <;> rfl

/-- The second coordinate really is Pv', with the one-sided derivatives at
both endpoints included. -/
lemma IsSolution.momentum_eq {P V : ℝ → ℝ} {a b t : ℝ}
    {Y : ℝ → ℝ × ℝ} (hY : IsSolution P V a b Y) (hab : a < b)
    (hp : ∀ s ∈ Icc a b, 0 < P s) (ht : t ∈ Icc a b) :
    (Y t).2 = P t * derivWithin (fun s => (Y s).1) (Icc a b) t := by
  rw [(hY.hasDerivWithinAt_fst ht).derivWithin (uniqueDiffOn_Icc hab t ht)]
  field_simp [(hp t ht).ne']

/-- Bridge from the state system to the original scalar Jacobi equation. -/
lemma IsSolution.scalar_equation {P V : ℝ → ℝ} {a b t : ℝ}
    {Y : ℝ → ℝ × ℝ} (hY : IsSolution P V a b Y) (hab : a < b)
    (hp : ∀ s ∈ Icc a b, 0 < P s) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => P s * derivWithin (fun r => (Y r).1) (Icc a b) s)
      (V t * (Y t).1) (Icc a b) t := by
  apply (hY.hasDerivWithinAt_snd ht).congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hY.momentum_eq hab hp hs).symm

/-- Continuous coefficients make the state a C¹ curve on the closed interval. -/
lemma IsSolution.contDiffOn {P V : ℝ → ℝ} {a b : ℝ} {Y : ℝ → ℝ × ℝ}
    (hY : IsSolution P V a b Y) (hP : ContinuousOn P (Icc a b))
    (hV : ContinuousOn V (Icc a b)) (hp : ∀ t ∈ Icc a b, 0 < P t) :
    ContDiffOn ℝ 1 Y (Icc a b) := by
  apply D13Unified.Ch07.LinearSystemExistence.regularity _ hY.2
  exact (hY.1.snd.div hP (fun t ht => (hp t ht).ne')).prodMk (hV.mul hY.1.fst)

/-- Under the source's C¹ assumption on P, the scalar Jacobi solution is C². -/
lemma IsSolution.contDiffOn_fst {P V : ℝ → ℝ} {a b : ℝ} {Y : ℝ → ℝ × ℝ}
    (hY : IsSolution P V a b Y) (hP : ContDiffOn ℝ 1 P (Icc a b))
    (hV : ContinuousOn V (Icc a b)) (hp : ∀ t ∈ Icc a b, 0 < P t) :
    ContDiffOn ℝ 2 (fun t => (Y t).1) (Icc a b) := by
  have hvel : ContDiffOn ℝ 1 (fun t => (Y t).2 / P t) (Icc a b) :=
    (hY.contDiffOn hP.continuousOn hV hp).snd.div hP (fun t ht => (hp t ht).ne')
  apply (contDiffOn_succ_iff_hasFDerivWithinAt (n := 1) (by simp)).mpr
  intro t ht
  refine ⟨Icc a b, ?_, by simp, fun r => ContinuousLinearMap.toSpanSingleton ℝ
    ((Y r).2 / P r), fun r hr => (hY.hasDerivWithinAt_fst hr).hasFDerivWithinAt, ?_⟩
  · rw [insert_eq_of_mem ht]
    exact self_mem_nhdsWithin
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).contDiff.comp_contDiffOn hvel

/-- Linearity of the Jacobi equation, retaining the momentum coordinate. -/
lemma IsSolution.add_smul {P V : ℝ → ℝ} {a b : ℝ} {Y W : ℝ → ℝ × ℝ}
    (hY : IsSolution P V a b Y) (hW : IsSolution P V a b W) (ε : ℝ) :
    IsSolution P V a b (fun t => Y t + ε • W t) := by
  refine ⟨hY.1.add (hW.1.const_smul ε), ?_⟩
  intro t ht
  rw [← systemOperator_apply, map_add, map_smul]
  convert (hY.2 t ht).add ((hW.2 t ht).const_smul ε) using 1
  simp only [systemOperator_apply]

/-- The normalized solution and the positive Jacobi solution required by the
source. The auxiliary solution has initial data w(a)=1, w'(a)=0. -/
theorem positiveJacobiSolution :
    Specs.VariationalNotes.Classical.Jacobi.PositiveJacobiSolution := by
  intro a b P V hab hP hV hp
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  obtain ⟨Y₀, hY₀, hY₀a, hu⟩ :=
    exists_unique_solution hab hP.continuousOn hV hp (0, P a)
  have hd : HasDerivWithinAt (fun t => (Y₀ t).1) 1 (Icc a b) a := by
    simpa only [hY₀a, div_self (hp a ha).ne'] using hY₀.hasDerivWithinAt_fst ha
  refine ⟨Y₀, hY₀, hY₀a, hd, hu, ?_⟩
  intro hnz
  have hfa : (Y₀ a).1 = 0 := by rw [hY₀a]
  have hpos := positive_of_no_zero hY₀.1.fst hfa hd hnz
  refine ⟨hpos, ?_⟩
  obtain ⟨W, hW, hWa, _⟩ :=
    exists_unique_solution hab hP.continuousOn hV hp (1, 0)
  have hn : ∀ t : Icc a b, 0 ≤ (Y₀ t).1 := by
    intro t
    rcases eq_or_lt_of_le t.property.1 with heq | hlt
    · simpa only [← heq, hfa] using (le_refl (0 : ℝ))
    · exact (hpos t ⟨hlt, t.property.2⟩).le
  have hz : ∀ t : Icc a b, (Y₀ t).1 = 0 → 0 < (W t).1 := by
    intro t ht
    have hta : (t : ℝ) = a := by
      by_contra hne
      exact hnz t ⟨lt_of_le_of_ne t.property.1 (Ne.symm hne), t.property.2⟩ ht
    simp only [hta, hWa]
    norm_num
  obtain ⟨ε, _, he⟩ := exists_positive_perturbation
    (fun t : Icc a b => (Y₀ t).1) (fun t : Icc a b => (W t).1)
    hY₀.1.fst.domRestrict hW.1.fst.domRestrict hn hz
  refine ⟨fun t => Y₀ t + ε • W t, hY₀.add_smul hW ε, ?_⟩
  intro t ht
  simpa only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] using he ⟨t, ht⟩

end VariationalNotes.Classical.Jacobi
