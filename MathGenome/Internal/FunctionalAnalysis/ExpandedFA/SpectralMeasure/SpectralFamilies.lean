import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.SpectralFamilies
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.NormalSpectralTests
import Mathlib.Algebra.BigOperators.Fin

/-!
The complex spectral-family and Stieltjes conclusions of
`fa2:p2:spectral-corollaries` in the adopted source.

Strong convergence is proved in each vector's finite diagonal measure, so no
separability or common scalar control measure is needed. The tagged sums retain
the lower endpoint atom and their operator norm error is bounded by the mesh,
including repeated vertices and singleton intervals. The real Hilbert-space
conclusions have their separate allocated companion; the shared Specs here stay
unchanged.
-/

noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set Filter
open Classical
namespace ExpandedFA.SpectralMeasure.SpectralFamilies
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded pointwise convergence along a countably generated filter.
This filter form is useful for one-sided real limits of spectral cuts. -/
lemma strong_integral_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (E : ProjectionValuedMeasure S H) (f : S → ℂ) (a : ι → S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (ha : ∀ i, SpectralMeasure.Spec.IsBoundedMeasurable (a i))
    (C : ℝ) (hb : ∀ i s, ‖a i s - f s‖ ≤ C)
    (hl : ∀ s, Tendsto (fun i => a i s) l (nhds (f s))) (x : H) :
    Tendsto (fun i => E.spectralIntegral (a i) x) l (nhds (E.spectralIntegral f x)) := by
  have hi : Tendsto (fun i => ∫ s, ‖a i s - f s‖ ^ 2 ∂E.diagonalMeasure x)
      l (nhds (0 : ℝ)) := by
    have hh : Tendsto (fun i => ∫ s, ‖a i s - f s‖ ^ 2 ∂E.diagonalMeasure x)
        l (nhds (∫ _ : S, (0 : ℝ) ∂E.diagonalMeasure x)) := by
      apply tendsto_integral_filter_of_norm_le_const
      · exact Eventually.of_forall (fun i =>
          (((ha i).1.sub hf.1).norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
      · refine ⟨(max C 0) ^ 2, Eventually.of_forall (fun i => Eventually.of_forall (fun s => ?_))⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((hb i s).trans (le_max_left _ _)) 2
      · exact Eventually.of_forall (fun s => by
          simpa using ((hl s).sub (tendsto_const_nhds (x := f s))).norm.pow 2)
    simpa using hh
  have hsquare : Tendsto (fun i => ‖E.spectralIntegral (a i) x - E.spectralIntegral f x‖ ^ 2)
      l (nhds (0 : ℝ)) := by
    have heq (i : ι) : ‖E.spectralIntegral (a i) x - E.spectralIntegral f x‖ ^ 2 =
        ∫ s, ‖a i s - f s‖ ^ 2 ∂E.diagonalMeasure x := by
      rw [← sub_apply, ← BorelNormSpectrum.integral_sub E (ha i) hf]
      exact E.spectralIntegral_norm_sq_integral _ (BorelNormSpectrum.bounded_sub (ha i) hf) x
    simpa only [heq] using hi
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsquare
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

lemma measurable_cut (A : H →L[ℂ] H) (t : ℝ) : MeasurableSet (Spec.cut A t) :=
  measurableSet_le (Complex.measurable_re.comp measurable_subtype_coe) measurable_const

lemma indicator_bound (B C : Set S) (s : S) :
    ‖B.indicator (fun _ => (1 : ℂ)) s - C.indicator (fun _ => (1 : ℂ)) s‖ ≤ 2 := by
  by_cases hB : s ∈ B <;> by_cases hC : s ∈ C <;> norm_num [hB, hC]

/-- Strong convergence of projections follows from pointwise convergence
of their characteristic functions, using each vector's own finite measure. -/
lemma projections_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (E : ProjectionValuedMeasure S H) (B : ι → Set S) (C : Set S)
    (hB : ∀ i, MeasurableSet (B i)) (hC : MeasurableSet C)
    (hl : ∀ s, Tendsto (fun i => (B i).indicator (fun _ => (1 : ℂ)) s) l
      (nhds (C.indicator (fun _ => (1 : ℂ)) s))) (x : H) :
    Tendsto (fun i => E (B i) x) l (nhds (E C x)) := by
  have hh := strong_integral_tendsto E (C.indicator (fun _ => 1))
    (fun i => (B i).indicator (fun _ => 1))
    (BorelNormSpectrum.bounded_indicator C hC (BorelNormSpectrum.bounded_const 1))
    (fun i => BorelNormSpectrum.bounded_indicator (B i) (hB i) (BorelNormSpectrum.bounded_const 1))
    2 (fun i s => indicator_bound (B i) C s) hl x
  simpa only [BorelNormSpectrum.integral_indicator_one E C hC,
    BorelNormSpectrum.integral_indicator_one E _ (hB _)] using hh

lemma indicator_Iic_right (r t : ℝ) :
    Tendsto (fun q : ℝ => if r ≤ q then (1 : ℂ) else 0) (nhdsWithin t (Ici t))
      (nhds (if r ≤ t then (1 : ℂ) else 0)) := by
  apply tendsto_const_nhds.congr'
  by_cases h : r ≤ t
  · filter_upwards [self_mem_nhdsWithin] with q hq
    simp [h, h.trans hq]
  · have htr : t < r := lt_of_not_ge h
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htr)] with q hq
    simp [h, not_le.mpr (show q < r from hq)]

lemma family_range_mono {A : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) {s t : ℝ} (hst : s ≤ t) :
    LinearMap.range (Spec.family E s).toLinearMap ≤
      LinearMap.range (Spec.family E t).toLinearMap := by
  rintro _ ⟨x, rfl⟩
  refine ⟨Spec.family E s x, ?_⟩
  have h : Spec.cut A t ∩ Spec.cut A s = Spec.cut A s := by
    ext z
    exact and_iff_right_of_imp (fun hz => hz.trans hst)
  have he := E.inter (Spec.cut A t) (Spec.cut A s) (measurable_cut A t) (measurable_cut A s)
  rw [h] at he
  exact congrArg (fun T : H →L[ℂ] H => T x) he

lemma family_right_continuous {A : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) (t : ℝ) (x : H) :
    Tendsto (fun r => Spec.family E r x) (nhdsWithin t (Ici t)) (nhds (Spec.family E t x)) := by
  apply projections_tendsto E _ _ (measurable_cut A) (measurable_cut A t) _ x
  intro z
  simpa only [Set.indicator_apply, Spec.cut, Set.mem_ofPred_eq] using indicator_Iic_right (z : ℂ).re t

lemma family_atBot {A : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) (x : H) :
    Tendsto (fun t => Spec.family E t x) atBot (nhds 0) := by
  have hh := projections_tendsto (l := atBot) E (Spec.cut A) ∅ (measurable_cut A) MeasurableSet.empty
    (fun z => ?_) x
  · simpa [Spec.family] using hh
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (z : ℂ).re] with t ht
  simp [Spec.cut, not_le.mpr ht]

lemma family_atTop {A : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) (x : H) :
    Tendsto (fun t => Spec.family E t x) atTop (nhds x) := by
  have hh := projections_tendsto (l := atTop) E (Spec.cut A) univ (measurable_cut A) MeasurableSet.univ
    (fun z => ?_) x
  · simpa [Spec.family, E.univ] using hh
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (z : ℂ).re] with t ht
  simp [Spec.cut, ht]

theorem spectral_family_properties : Spec.FamilyProperties.{v} := by
  intro H _ _ _ A _ E _
  refine ⟨?_, ?_, family_right_continuous E, family_atBot E, family_atTop E⟩
  · intro t
    exact ⟨E.selfAdjoint _ (measurable_cut A t), E.idempotent _ (measurable_cut A t)⟩
  · intro s t hst
    exact family_range_mono E hst

theorem selfAdjoint_iff_real_spectrum : NormalSpectralTests.Spec.SelfAdjointSpectrum.{v} :=
  NormalSpectralTests.selfAdjoint_iff_real_spectrum

theorem unitary_iff_circle_spectrum : NormalSpectralTests.Spec.UnitarySpectrum.{v} :=
  NormalSpectralTests.unitary_iff_circle_spectrum

theorem eigenprojection : NormalSpectralTests.Spec.Eigenprojection.{v} :=
  NormalSpectralTests.eigenprojection

namespace Spec.TaggedPartition
variable {m M : ℝ} (P : Spec.TaggedPartition m M)

lemma mesh_nonneg : 0 ≤ P.mesh := NNReal.coe_nonneg _

lemma width_le_mesh (i : Fin P.n) : P.point i.succ - P.point i.castSucc ≤ P.mesh := by
  apply le_trans (Real.le_coe_toNNReal _)
  exact_mod_cast (Finset.le_sup (f := fun i : Fin P.n =>
    (P.point i.succ - P.point i.castSucc).toNNReal) (Finset.mem_univ i))

end Spec.TaggedPartition

private def cutoff (r t : ℝ) : ℝ := if r ≤ t then 1 else 0

private def realStep {m M : ℝ} (P : Spec.TaggedPartition m M) (r : ℝ) : ℝ :=
  P.lowerTag * cutoff r m + ∑ i : Fin P.n,
    P.tag i * (cutoff r (P.point i.succ) - cutoff r (P.point i.castSucc))

/-- The finite real-variable estimate underlying the operator mesh bound.
No spectral theorem, integral, or positivity assumption is hidden here. -/
lemma realStep_error {m M : ℝ} (P : Spec.TaggedPartition m M) {r : ℝ}
    (hm : m ≤ r) (hM : r ≤ M) : |realStep P r - r| ≤ P.mesh := by
  have htelescope : (∑ i : Fin P.n,
      (cutoff r (P.point i.succ) - cutoff r (P.point i.castSucc))) = 1 - cutoff r m := by
    have h₁ := Fin.sum_univ_succ (fun i => cutoff r (P.point i))
    have h₂ := Fin.sum_univ_castSucc (fun i => cutoff r (P.point i))
    rw [P.first] at h₁
    rw [P.last] at h₂
    have htop : cutoff r M = 1 := by simp [cutoff, hM]
    rw [htop] at h₂
    rw [Finset.sum_sub_distrib]
    linarith
  have hatom : |(P.lowerTag - r) * cutoff r m| ≤ P.mesh * cutoff r m := by
    by_cases h : r ≤ m
    · have he : r = m := le_antisymm h hm
      subst r
      simp only [cutoff, le_refl, ite_true, mul_one]
      unfold Spec.TaggedPartition.lowerTag
      split_ifs with hn
      · have ht := P.tag_mem ⟨0, hn⟩
        have hw := P.width_le_mesh ⟨0, hn⟩
        have hfirst : P.point (⟨0, hn⟩ : Fin P.n).castSucc = m := by
          simpa using P.first
        rw [hfirst] at ht hw
        rw [abs_le]
        constructor <;> linarith [P.mesh_nonneg]
      · simpa using P.mesh_nonneg
    · simp [cutoff, h]
  have heq : realStep P r - r = (P.lowerTag - r) * cutoff r m + ∑ i : Fin P.n,
      (P.tag i - r) * (cutoff r (P.point i.succ) - cutoff r (P.point i.castSucc)) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htelescope]
    dsimp [realStep]
    ring
  have hterm (i : Fin P.n) :
      |(P.tag i - r) * (cutoff r (P.point i.succ) - cutoff r (P.point i.castSucc))| ≤
        P.mesh * (cutoff r (P.point i.succ) - cutoff r (P.point i.castSucc)) := by
    have hmono : P.point i.castSucc ≤ P.point i.succ := P.mono (by
      simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ]; omega)
    by_cases hl : r ≤ P.point i.castSucc
    · have hr := hl.trans hmono
      simp [cutoff, hl, hr]
    · by_cases hr : r ≤ P.point i.succ
      · simp only [cutoff, ite_eq_left hr, ite_eq_right hl, sub_zero, mul_one]
        rw [abs_le]
        have hw := P.width_le_mesh i
        have ht := P.tag_mem i
        constructor <;> linarith [lt_of_not_ge hl]
      · simp [cutoff, hl, hr]
  rw [heq]
  calc
    |(P.lowerTag - r) * cutoff r m + ∑ i : Fin P.n, (P.tag i - r) *
        (cutoff r (P.point i.succ) - cutoff r (P.point i.castSucc))| ≤
        |(P.lowerTag - r) * cutoff r m| +
        |∑ i : Fin P.n, (P.tag i - r) *
          (cutoff r (P.point i.succ) - cutoff r (P.point i.castSucc))| := abs_add_le _ _
    _ ≤ P.mesh * cutoff r m + ∑ i : Fin P.n,
        |(P.tag i - r) * (cutoff r (P.point i.succ) - cutoff r (P.point i.castSucc))| :=
      add_le_add hatom (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ P.mesh * cutoff r m + ∑ i : Fin P.n, P.mesh *
          (cutoff r (P.point i.succ) - cutoff r (P.point i.castSucc)) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun i _ => hterm i))
    _ = P.mesh := by rw [← Finset.mul_sum, htelescope]; ring


lemma bounded_sum {ι : Type*} (t : Finset ι) (f : ι → S → ℂ)
    (hf : ∀ i ∈ t, SpectralMeasure.Spec.IsBoundedMeasurable (f i)) :
    SpectralMeasure.Spec.IsBoundedMeasurable (∑ i ∈ t, f i) := by
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact BorelNormSpectrum.bounded_const (S := S) 0
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma integral_sum {ι : Type*} (E : ProjectionValuedMeasure S H)
    (t : Finset ι) (f : ι → S → ℂ)
    (hf : ∀ i ∈ t, SpectralMeasure.Spec.IsBoundedMeasurable (f i)) :
    E.spectralIntegral (∑ i ∈ t, f i) = ∑ i ∈ t, E.spectralIntegral (f i) := by
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change E.spectralIntegral (fun _ : S => (0 : ℂ)) = 0
    exact (BorelNormSpectrum.integral_const E 0).trans (zero_smul ℂ _)
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi, E.spectralIntegral_add _ _
      (hf i (Finset.mem_insert_self _ _))
      (bounded_sum t f (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      Finset.sum_insert hi, ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

private def cutIndicator (A : H →L[ℂ] H) (t : ℝ) : spectrum ℂ A → ℂ :=
  (Spec.cut A t).indicator (fun _ => 1)

private lemma bounded_cutIndicator (A : H →L[ℂ] H) (t : ℝ) :
    SpectralMeasure.Spec.IsBoundedMeasurable (cutIndicator A t) :=
  BorelNormSpectrum.bounded_indicator _ (measurable_cut A t) (BorelNormSpectrum.bounded_const 1)

private lemma integral_cutIndicator {A : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) (t : ℝ) :
    E.spectralIntegral (cutIndicator A t) = Spec.family E t :=
  BorelNormSpectrum.integral_indicator_one E _ (measurable_cut A t)

private def complexStep {m M : ℝ} (P : Spec.TaggedPartition m M) (A : H →L[ℂ] H) :
    spectrum ℂ A → ℂ :=
  (P.lowerTag : ℂ) • cutIndicator A m + ∑ i : Fin P.n,
    (P.tag i : ℂ) • (cutIndicator A (P.point i.succ) - cutIndicator A (P.point i.castSucc))

private lemma bounded_complexStep {m M : ℝ} (P : Spec.TaggedPartition m M) (A : H →L[ℂ] H) :
    SpectralMeasure.Spec.IsBoundedMeasurable (complexStep P A) :=
  ((bounded_cutIndicator A m).smul (P.lowerTag : ℂ)).add
    (bounded_sum Finset.univ _ (fun i _ =>
      (BorelNormSpectrum.bounded_sub (bounded_cutIndicator A (P.point i.succ))
        (bounded_cutIndicator A (P.point i.castSucc))).smul (P.tag i : ℂ)))

private lemma complexStep_eq {m M : ℝ} (P : Spec.TaggedPartition m M) (A : H →L[ℂ] H)
    (z : spectrum ℂ A) : complexStep P A z = (realStep P (z : ℂ).re : ℂ) := by
  have hc (t : ℝ) : cutIndicator A t z = (cutoff (z : ℂ).re t : ℂ) := by
    by_cases h : (z : ℂ).re ≤ t <;> simp [cutIndicator, Spec.cut, cutoff, h]
  simp only [complexStep, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply,
    smul_eq_mul, hc, realStep, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sum, Complex.ofReal_sub]

private lemma integral_complexStep {m M : ℝ} (P : Spec.TaggedPartition m M)
    {A : H →L[ℂ] H} (E : ProjectionValuedMeasure (spectrum ℂ A) H) :
    E.spectralIntegral (complexStep P A) = P.operatorSum E := by
  rw [complexStep, E.spectralIntegral_add _ _ ((bounded_cutIndicator A m).smul (P.lowerTag : ℂ))
    (bounded_sum Finset.univ _ (fun i _ =>
      (BorelNormSpectrum.bounded_sub (bounded_cutIndicator A (P.point i.succ))
        (bounded_cutIndicator A (P.point i.castSucc))).smul (P.tag i : ℂ))),
    E.spectralIntegral_smul _ _ (bounded_cutIndicator A m), integral_cutIndicator,
    integral_sum E Finset.univ _ (fun i _ =>
      (BorelNormSpectrum.bounded_sub (bounded_cutIndicator A (P.point i.succ))
        (bounded_cutIndicator A (P.point i.castSucc))).smul (P.tag i : ℂ))]
  unfold Spec.TaggedPartition.operatorSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [E.spectralIntegral_smul _ _ (BorelNormSpectrum.bounded_sub
      (bounded_cutIndicator A (P.point i.succ)) (bounded_cutIndicator A (P.point i.castSucc))),
    BorelNormSpectrum.integral_sub E (bounded_cutIndicator A (P.point i.succ))
      (bounded_cutIndicator A (P.point i.castSucc)), integral_cutIndicator, integral_cutIndicator]

lemma spectral_point_real {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (z : spectrum ℂ A) :
    (z : ℂ) = ((z : ℂ).re : ℂ) := by
  have him := (selfAdjoint_iff_real_spectrum H A hA.isStarNormal).mp hA (z : ℂ) z.property
  exact Complex.ext (by simp) (by simpa using him)

/-- Every tag choice has norm error at most the largest cell width. -/
lemma operatorSum_error {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) (hE : NormalPVM.Spec.Resolves A E)
    {m M : ℝ} (hσ : ∀ z ∈ spectrum ℂ A, m ≤ z.re ∧ z.re ≤ M)
    (P : Spec.TaggedPartition m M) : ‖P.operatorSum E - A‖ ≤ P.mesh := by
  let c : spectrum ℂ A → ℂ := fun z => (z : ℂ)
  have hc : SpectralMeasure.Spec.IsBoundedMeasurable c :=
    NormalPVM.continuous_bounded ((ContinuousMap.id ℂ).restrict (spectrum ℂ A))
  have hid : E.spectralIntegral c = A := NormalPVM.continuousIntegral_coordinate E hE
  have hdiff := BorelNormSpectrum.bounded_sub (bounded_complexStep P A) hc
  have heq : E.spectralIntegral (complexStep P A - c) = P.operatorSum E - A := by
    rw [BorelNormSpectrum.integral_sub E (bounded_complexStep P A) hc, integral_complexStep, hid]
  rw [← heq]
  apply E.spectralIntegral_norm_le _ hdiff _ P.mesh_nonneg
  intro z
  change ‖complexStep P A z - (z : ℂ)‖ ≤ P.mesh
  rw [complexStep_eq, spectral_point_real hA z, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact realStep_error P (hσ z z.property).1 (hσ z z.property).2

lemma cut_lower_eq_singleton {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    {m M : ℝ} (hσ : ∀ z ∈ spectrum ℂ A, m ≤ z.re ∧ z.re ≤ M) :
    Spec.cut A m = {z : spectrum ℂ A | (z : ℂ) = (m : ℂ)} := by
  ext z
  change (z : ℂ).re ≤ m ↔ (z : ℂ) = (m : ℂ)
  constructor
  · intro hz
    rw [spectral_point_real hA z]
    exact congrArg Complex.ofReal (le_antisymm hz (hσ z z.property).1)
  · intro hz
    simpa using congrArg Complex.re hz |>.le

lemma family_below_lower {A : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) {m M t : ℝ}
    (hσ : ∀ z ∈ spectrum ℂ A, m ≤ z.re ∧ z.re ≤ M) (ht : t < m) :
    Spec.family E t = 0 := by
  have hc : Spec.cut A t = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hm := (hσ z z.property).1
    change (z : ℂ).re ≤ t at hz
    linarith
  change E (Spec.cut A t) = 0
  rw [hc, E.map_empty]

lemma family_above_upper {A : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) {m M t : ℝ}
    (hσ : ∀ z ∈ spectrum ℂ A, m ≤ z.re ∧ z.re ≤ M) (ht : M ≤ t) :
    Spec.family E t = 1 := by
  have hc : Spec.cut A t = univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact ((hσ z z.property).2).trans ht
  change E (Spec.cut A t) = 1
  rw [hc, E.univ]

lemma coefficient_operatorSum {m M : ℝ} (P : Spec.TaggedPartition m M)
    {A : H →L[ℂ] H} (E : ProjectionValuedMeasure (spectrum ℂ A) H) (x y : H) :
    ⟪x, P.operatorSum E y⟫_ℂ =
      P.scalarSum (fun t => ⟪x, Spec.family E t y⟫_ℂ) ⟪x, Spec.family E m y⟫_ℂ := by
  simp only [Spec.TaggedPartition.operatorSum, Spec.TaggedPartition.scalarSum,
    add_apply, sum_apply,
    smul_apply, sub_apply,
    inner_add_right, inner_sum, inner_smul_right, inner_sub_right]

lemma coefficient_error {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) (hE : NormalPVM.Spec.Resolves A E)
    {m M : ℝ} (hσ : ∀ z ∈ spectrum ℂ A, m ≤ z.re ∧ z.re ≤ M)
    (P : Spec.TaggedPartition m M) (x y : H) :
    ‖P.scalarSum (fun t => ⟪x, Spec.family E t y⟫_ℂ) ⟪x, Spec.family E m y⟫_ℂ - ⟪x, A y⟫_ℂ‖ ≤
      P.mesh * (‖x‖ * ‖y‖) := by
  rw [← coefficient_operatorSum, ← inner_sub_right, ← sub_apply]
  calc
    ‖⟪x, (P.operatorSum E - A) y⟫_ℂ‖ ≤ ‖x‖ * ‖(P.operatorSum E - A) y‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖P.operatorSum E - A‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((P.operatorSum E - A).le_opNorm y) (norm_nonneg _)
    _ ≤ ‖x‖ * (P.mesh * ‖y‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (operatorSum_error hA E hE hσ P) (norm_nonneg _)) (norm_nonneg _)
    _ = P.mesh * (‖x‖ * ‖y‖) := by ring

theorem stieltjes_approximation : Spec.StieltjesApproximation.{v} := by
  intro H _ _ _ A hA E hE m M hσ
  refine ⟨operatorSum_error hA E hE hσ, ?_, ?_, ?_⟩
  · intro ε hε
    exact ⟨ε, hε, fun P hP => (operatorSum_error hA E hE hσ P).trans_lt hP⟩
  · intro x y ε hε
    let K := ‖x‖ * ‖y‖
    have hK : 0 < K + 1 := by dsimp [K]; positivity
    refine ⟨ε / (K + 1), div_pos hε hK, ?_⟩
    intro P hP
    have hsmall : P.mesh * (K + 1) < ε := (lt_div_iff₀ hK).mp hP
    have hc : Spec.family E m = E {z | (z : ℂ) = (m : ℂ)} :=
      congrArg E (cut_lower_eq_singleton hA hσ)
    rw [← hc]
    have hb := coefficient_error hA E hE hσ P x y
    exact hb.trans_lt (by nlinarith [P.mesh_nonneg])
  · intro he
    subst M
    let c : spectrum ℂ A → ℂ := fun z => (z : ℂ)
    have hf : c = (fun _ => (m : ℂ)) := by
      funext z
      dsimp [c]
      rw [spectral_point_real hA z]
      exact congrArg Complex.ofReal (le_antisymm (hσ z z.property).2 (hσ z z.property).1)
    have hid : E.spectralIntegral c = A := NormalPVM.continuousIntegral_coordinate E hE
    rw [hf, BorelNormSpectrum.integral_const] at hid
    exact hid.symm

end ExpandedFA.SpectralMeasure.SpectralFamilies
