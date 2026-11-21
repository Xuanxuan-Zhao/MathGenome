import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BoundedWeakstarTopology
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SeminormModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu

/-! The bounded weak-star topology on the original continuous scalar-linear dual.
The compact open-cover argument works for incomplete normed spaces as well.
All changes of topology retain the original operator norm on the dual. -/

open Set Filter
open scoped Topology

noncomputable section
namespace ExpandedFA.P1.BoundedWeakstarTopology

open Spec (NullSequence)

def nullSequenceSeminorm : Spec.SeminormType := Spec.SeminormValue

def boundedWeakstarTopology : Spec.TopologyType := Spec.TopologyValue

section Seminorms
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma evaluation_seminorms_bounded (x : NullSequence E) :
    BddAbove (range (fun n : ℕ => (normSeminorm 𝕜 𝕜).comp
      (ContinuousLinearMap.apply 𝕜 𝕜 (x.1 n)).toLinearMap)) := by
  rw [Seminorm.bddAbove_range_iff]
  intro f
  have ht : Tendsto (fun n => ‖f (x.1 n)‖) atTop (𝓝 0) := by
    simpa using (f.continuous.tendsto 0 |>.comp x.2).norm
  exact ht.bddAbove_range

lemma nullSequenceSeminorm_apply (x : NullSequence E) (f : E →L[𝕜] 𝕜) :
    nullSequenceSeminorm 𝕜 E x f = ⨆ n : ℕ, ‖f (x.1 n)‖ := by
  exact Seminorm.iSup_apply (evaluation_seminorms_bounded (𝕜 := 𝕜) x)

lemma evaluation_le_nullSequenceSeminorm (x : NullSequence E)
    (f : E →L[𝕜] 𝕜) (n : ℕ) : ‖f (x.1 n)‖ ≤ nullSequenceSeminorm 𝕜 E x f := by
  exact (le_ciSup (evaluation_seminorms_bounded (𝕜 := 𝕜) x) n) f

/-- A one-point test is one of the allowed null sequences. -/
def singleSequence (x : E) : NullSequence E :=
  ⟨fun n => if n = 0 then x else 0,
    tendsto_atTop_of_eventually_const (i₀ := 1) (fun n hn => by
      simp [show n ≠ 0 from Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)])⟩

lemma nullSequenceSeminorm_separates (f : E →L[𝕜] 𝕜) (hf : f ≠ 0) :
    ∃ x : NullSequence E, nullSequenceSeminorm 𝕜 E x f ≠ 0 := by
  have h : ∃ x : E, f x ≠ 0 := by
    by_contra! hn
    exact hf (ContinuousLinearMap.ext hn)
  obtain ⟨x, hx⟩ := h
  refine ⟨singleSequence x, ne_of_gt (lt_of_lt_of_le (norm_pos_iff.mpr hx) ?_)⟩
  exact evaluation_le_nullSequenceSeminorm (singleSequence x) f 0

end Seminorms

theorem finite_supremum : Spec.FiniteSupremum := by
  intro 𝕜 E _ _ _ x f
  exact ⟨Seminorm.bddAbove_range_iff.mp (evaluation_seminorms_bounded x) f,
    nullSequenceSeminorm_apply x f⟩

theorem topology_construction : Spec.Construction := by
  intro 𝕜 E _ _ _
  obtain ⟨hL, hT, _, hc⟩ := seminorm_topology_construction 𝕜 (E →L[𝕜] 𝕜)
    (NullSequence E) (nullSequenceSeminorm 𝕜 E) nullSequenceSeminorm_separates
  exact ⟨hL, hT, hc⟩

section Agreement
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- On a fixed norm-bounded set the tails are uniformly small. -/
lemma continuous_bounded_inclusion (A : Set (E →L[𝕜] 𝕜)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖f‖ ≤ R) :
    @Continuous A (E →L[𝕜] 𝕜)
      (TopologicalSpace.induced Subtype.val (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E))
      (boundedWeakstarTopology 𝕜 E) Subtype.val := by
  classical
  let : TopologicalSpace (E →L[𝕜] 𝕜) := boundedWeakstarTopology 𝕜 E
  let : TopologicalSpace A := TopologicalSpace.induced Subtype.val
    (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
  have hp : WithSeminorms (nullSequenceSeminorm 𝕜 E) := ⟨rfl⟩
  have hev (y : E) : Continuous (fun f : A => f.1 y) := by
    have hc := (C12WeakStar.weakStarTopology_evaluation_coarsest 𝕜 E
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)).mpr le_rfl y
    exact @Continuous.comp A (E →L[𝕜] 𝕜) 𝕜 _
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) _ _ _ hc continuous_induced_dom
  apply continuous_iff_continuousAt.mpr
  intro f
  rw [ContinuousAt, hp.tendsto_nhds]
  intro x ε hε
  have hM : 0 < 2 * R + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp x.2 ((ε / 2) / (2 * R + 1))
    (div_pos (half_pos hε) hM)
  have hfinite : ∀ᶠ g : A in 𝓝 f,
      ∀ n ∈ Finset.range N, ‖(g.1 - f.1) (x.1 n)‖ < ε / 2 := by
    apply (Finset.range N).eventually_all.mpr
    intro n _
    have ht : Tendsto (fun g : A => ‖(g.1 - f.1) (x.1 n)‖) (𝓝 f) (𝓝 0) := by
      have hc : Continuous (fun g : A => ‖g.1 (x.1 n) - f.1 (x.1 n)‖) :=
        ((hev (x.1 n)).sub continuous_const).norm
      simpa only [sub_apply, sub_self, norm_zero] using hc.tendsto f
    exact (tendsto_order.mp ht).2 _ (half_pos hε)
  filter_upwards [hfinite] with g hg
  rw [nullSequenceSeminorm_apply]
  apply lt_of_le_of_lt (ciSup_le (fun n => ?_)) (half_lt_self hε)
  by_cases hn : n < N
  · exact (hg n (Finset.mem_range.mpr hn)).le
  · have hx : ‖x.1 n‖ < (ε / 2) / (2 * R + 1) := by
      simpa only [dist_zero_right] using hN n (Nat.le_of_not_gt hn)
    calc
      ‖(g.1 - f.1) (x.1 n)‖ ≤ ‖g.1 - f.1‖ * ‖x.1 n‖ :=
        (g.1 - f.1).le_opNorm _
      _ ≤ (2 * R + 1) * ‖x.1 n‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by linarith [hA g.1 g.2, hA f.1 f.2])
      _ ≤ (2 * R + 1) * ((ε / 2) / (2 * R + 1)) :=
        mul_le_mul_of_nonneg_left hx.le hM.le
      _ = ε / 2 := mul_div_cancel₀ _ hM.ne'

lemma boundedWeakstar_le_weakstar : boundedWeakstarTopology 𝕜 E ≤
    C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E := by
  let : TopologicalSpace (E →L[𝕜] 𝕜) := boundedWeakstarTopology 𝕜 E
  apply (C12WeakStar.weakStarTopology_evaluation_coarsest 𝕜 E _).mp
  intro x
  have hp : WithSeminorms (nullSequenceSeminorm 𝕜 E) := ⟨rfl⟩
  let ev : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜 :=
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply WithSeminorms.continuous_of_isBounded hp (norm_withSeminorms 𝕜 𝕜) ev
  intro i
  refine ⟨{singleSequence x}, 1, ?_⟩
  simp only [one_smul, Finset.sup_singleton]
  intro f
  change ‖f x‖ ≤ nullSequenceSeminorm 𝕜 E (singleSequence x) f
  exact evaluation_le_nullSequenceSeminorm (singleSequence x) f 0

theorem bounded_agreement : Spec.BoundedAgreement := by
  intro 𝕜 E _ _ _ A hA
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hA
  apply le_antisymm
  · exact induced_mono boundedWeakstar_le_weakstar
  · exact continuous_iff_le_induced.mp
      (continuous_bounded_inclusion A (max R 0) (le_max_right _ _)
        (fun f hf => (hR f hf).trans (le_max_left _ _)))

end Agreement

section CompactTests
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma exists_large_evaluation (d : E →L[𝕜] 𝕜) (hd : d ≠ 0) :
    ∃ x : E, 1 < ‖d x‖ := by
  obtain ⟨y, hy⟩ : ∃ y : E, d y ≠ 0 := by
    by_contra! h
    exact hd (ContinuousLinearMap.ext h)
  have hp : 0 < ‖d y‖ := norm_pos_iff.mpr hy
  refine ⟨((2 / ‖d y‖ : ℝ) : 𝕜) • y, ?_⟩
  rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (div_pos zero_lt_two hp),
    div_mul_cancel₀ _ hp.ne']
  norm_num

lemma exists_small_test (d : E →L[𝕜] 𝕜) {m : ℝ} (hm : 0 < m) (hd : m < ‖d‖) :
    ∃ x : E, ‖x‖ ≤ m⁻¹ ∧ 1 < ‖d x‖ := by
  by_contra! h
  have hnorm : ‖d‖ ≤ m := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hm.le
    intro y hy
    have ht := h (((m⁻¹ : ℝ) : 𝕜) • y) (by
      simp [norm_smul, abs_of_pos hm, hy])
    rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hm)] at ht
    simpa only [mul_one] using (inv_mul_le_iff₀ hm).mp ht
  exact (not_le_of_gt hd) hnorm

/-- Compactness turns a cover by failing scalar tests into finitely many tests. -/
lemma finite_test_cover (K : Set (E →L[𝕜] 𝕜)) (f₀ : E →L[𝕜] 𝕜) (T : Set E)
    (hK : @IsCompact _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) K)
    (hcover : ∀ f ∈ K, ∃ x ∈ T, 1 < ‖(f - f₀) x‖) :
    ∃ F : Finset E, (∀ x ∈ F, x ∈ T) ∧
      ∀ f ∈ K, ∃ x ∈ F, 1 < ‖(f - f₀) x‖ := by
  classical
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have hev (x : E) : Continuous (fun f : E →L[𝕜] 𝕜 => ‖(f - f₀) x‖) := by
    have he := (C12WeakStar.weakStarTopology_evaluation_coarsest 𝕜 E _).mpr le_rfl x
    exact he.sub continuous_const |>.norm
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover
    (fun x : T => {f | 1 < ‖(f - f₀) x.1‖})
    (fun x => isOpen_lt continuous_const (hev x.1)) (by
      intro f hf
      obtain ⟨x, hx, hg⟩ := hcover f hf
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hg⟩)
  refine ⟨F.image Subtype.val, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  · intro f hf
    obtain ⟨x, hx, hfx⟩ := mem_iUnion₂.mp (hF hf)
    exact ⟨x.1, Finset.mem_image.mpr ⟨x, hx, rfl⟩, hfx⟩

end CompactTests

/-- A countable union of finite sets whose radii tend to zero can be listed
as a null sequence, inserting zeros at unused codes. Repeated values are allowed. -/
lemma nullSequence_of_finsets {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → Finset E)
    (hF : ∀ n : ℕ, n ≠ 0 → ∀ x ∈ F n, ‖x‖ ≤ (n : ℝ)⁻¹) :
    ∃ x : NullSequence E, ∀ n, ∀ y ∈ F n, y ∈ range x.1 := by
  classical
  let I := Σ n : ℕ, ↥(F n)
  let : Encodable I := Encodable.ofCountable I
  let v : ℕ → E := fun n => match Encodable.decode₂ I n with
    | none => 0
    | some i => i.2.1
  have hv : Tendsto v atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((eventually_ge_atTop 1).and ((tendsto_order.mp hlim).2 ε hε))
    let S : Finset I := (Finset.range N).biUnion fun k =>
      (F k).attach.image (fun y => (⟨k, y⟩ : I))
    let B : Finset ℕ := S.image Encodable.encode
    have havoid : ∀ᶠ n : ℕ in atTop, n ∉ B :=
      atTop_le_cofinite B.eventually_cofinite_notMem
    filter_upwards [havoid] with n hn
    cases hd : Encodable.decode₂ I n with
    | none => simpa only [v, hd, dist_self] using hε
    | some i =>
      have hi : Encodable.encode i = n := Encodable.decode₂_eq_some.mp hd
      have hlarge : N ≤ i.1 := by
        by_contra! hsmall
        apply hn
        rw [← hi]
        apply Finset.mem_image.mpr
        refine ⟨i, ?_, rfl⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨i.1, Finset.mem_range.mpr hsmall, ?_⟩
        exact Finset.mem_image.mpr ⟨i.2, Finset.mem_attach _ _, rfl⟩
      have htail := hN i.1 hlarge
      have hnorm := hF i.1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one htail.1))
        i.2.1 i.2.2
      simpa only [v, hd, dist_zero_right] using hnorm.trans_lt htail.2
  refine ⟨⟨v, hv⟩, ?_⟩
  intro n y hy
  let i : I := ⟨n, ⟨y, hy⟩⟩
  refine ⟨Encodable.encode i, ?_⟩
  simp only [v, Encodable.encodek₂]
  rfl

section ClosedSlices
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma compact_translated_slice (C : Set (E →L[𝕜] 𝕜))
    (hC : ∀ r : ℝ, 0 < r → @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (C ∩ {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r}))
    (f₀ : E →L[𝕜] 𝕜) (r : ℝ) (hr : 0 ≤ r) :
    @IsCompact _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (C ∩ {f : E →L[𝕜] 𝕜 | ‖f - f₀‖ ≤ r}) := by
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have hk := C13Alaoglu.weakStar_closedBall_isCompact 𝕜 E f₀ r hr
  have hc := hC (r + ‖f₀‖ + 1) (by positivity)
  convert hk.inter_right hc using 1
  ext f
  constructor
  · rintro ⟨hcf, hf⟩
    refine ⟨hf, hcf, ?_⟩
    have hb : ‖f‖ ≤ ‖f - f₀‖ + ‖f₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (f - f₀) f₀
    change ‖f - f₀‖ ≤ r at hf
    exact hb.trans (by linarith)
  · rintro ⟨hf, hcf, _⟩
    exact ⟨hcf, hf⟩

/-- Every closed-slice set missing f₀ can be excluded by one null-sequence test. -/
lemma nullSequence_excluding_closed_slices (C : Set (E →L[𝕜] 𝕜))
    (hC : ∀ r : ℝ, 0 < r → @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (C ∩ {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r}))
    (f₀ : E →L[𝕜] 𝕜) (hf₀ : f₀ ∉ C) :
    ∃ x : NullSequence E, ∀ f ∈ C, 1 < nullSequenceSeminorm 𝕜 E x (f - f₀) := by
  classical
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  let Good (n : ℕ) (S : Finset E) : Prop :=
    ∀ f ∈ C, ‖f - f₀‖ ≤ (n : ℝ) + 1 → ∃ x ∈ S, 1 < ‖(f - f₀) x‖
  have hbase : ∃ S : Finset E, Good 0 S := by
    obtain ⟨S, _, hS⟩ := finite_test_cover
      (C ∩ {f : E →L[𝕜] 𝕜 | ‖f - f₀‖ ≤ 1}) f₀ univ
      (compact_translated_slice C hC f₀ 1 zero_le_one) (by
        intro f hf
        have hne : f - f₀ ≠ 0 := by
          intro he
          exact hf₀ (sub_eq_zero.mp he ▸ hf.1)
        obtain ⟨x, hx⟩ := exists_large_evaluation (f - f₀) hne
        exact ⟨x, mem_univ _, hx⟩)
    exact ⟨S, fun f hf hb => hS f ⟨hf, by simpa using hb⟩⟩
  have hstep : ∀ (n : ℕ) (S : Finset E), Good n S →
      ∃ F : Finset E, (∀ x ∈ F, ‖x‖ ≤ ((n : ℝ) + 1)⁻¹) ∧ Good (n + 1) (S ∪ F) := by
    intro n S hS
    let K : Set (E →L[𝕜] 𝕜) :=
      (C ∩ {f | ‖f - f₀‖ ≤ (n : ℝ) + 2}) ∩
        {f | ∀ x ∈ S, ‖(f - f₀) x‖ ≤ 1}
    have heval (x : E) : Continuous (fun f : E →L[𝕜] 𝕜 => ‖(f - f₀) x‖) := by
      have he := (C12WeakStar.weakStarTopology_evaluation_coarsest 𝕜 E _).mpr le_rfl x
      exact he.sub continuous_const |>.norm
    have hk : IsCompact K := by
      apply (compact_translated_slice C hC f₀ ((n : ℝ) + 2) (by positivity)).inter_right
      have heq : {f : E →L[𝕜] 𝕜 | ∀ x ∈ S, ‖(f - f₀) x‖ ≤ 1} =
          ⋂ x ∈ S, {f | ‖(f - f₀) x‖ ≤ 1} := by ext f; simp
      rw [heq]
      exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_le (heval x) continuous_const
    obtain ⟨F, hF, hcover⟩ := finite_test_cover K f₀
      {x : E | ‖x‖ ≤ ((n : ℝ) + 1)⁻¹} hk (by
        intro f hf
        have hm : (n : ℝ) + 1 < ‖f - f₀‖ := by
          by_contra! hle
          obtain ⟨x, hx, hfx⟩ := hS f hf.1.1 hle
          exact (not_le_of_gt hfx) (hf.2 x hx)
        exact exists_small_test (f - f₀) (by positivity) hm)
    refine ⟨F, hF, ?_⟩
    intro f hf hb
    by_cases hold : ∃ x ∈ S, 1 < ‖(f - f₀) x‖
    · obtain ⟨x, hx, hfx⟩ := hold
      exact ⟨x, Finset.mem_union_left _ hx, hfx⟩
    · have hin : f ∈ K := by
        refine ⟨⟨hf, ?_⟩, ?_⟩
        · change ‖f - f₀‖ ≤ (n : ℝ) + 2
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hb
        · push Not at hold
          exact hold
      obtain ⟨x, hx, hfx⟩ := hcover f hin
      exact ⟨x, Finset.mem_union_right _ hx, hfx⟩
  let next (n : ℕ) (S : {S : Finset E // Good n S}) :
      {S : Finset E // Good (n + 1) S} :=
    ⟨S.1 ∪ (hstep n S.1 S.2).choose, (hstep n S.1 S.2).choose_spec.2⟩
  let S : ∀ n : ℕ, {S : Finset E // Good n S} :=
    fun n => Nat.rec ⟨hbase.choose, hbase.choose_spec⟩ next n
  let F : ℕ → Finset E := fun n => match n with
    | 0 => (S 0).1
    | k + 1 => (hstep k (S k).1 (S k).2).choose
  have hF : ∀ n : ℕ, n ≠ 0 → ∀ x ∈ F n, ‖x‖ ≤ (n : ℝ)⁻¹ := by
    intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ k => simpa only [F, Nat.cast_add, Nat.cast_one] using
        (hstep k (S k).1 (S k).2).choose_spec.1
  obtain ⟨x, hx⟩ := nullSequence_of_finsets F hF
  have hS : ∀ n : ℕ, ∀ y ∈ (S n).1, y ∈ range x.1 := by
    intro n
    induction n with
    | zero => exact fun y hy => hx 0 y hy
    | succ n ih =>
      intro y hy
      change y ∈ (S n).1 ∪ (hstep n (S n).1 (S n).2).choose at hy
      rcases Finset.mem_union.mp hy with h | h
      · exact ih y h
      · exact hx (n + 1) y h
  refine ⟨x, ?_⟩
  intro f hf
  obtain ⟨n, hn⟩ := exists_nat_gt ‖f - f₀‖
  obtain ⟨y, hy, hfy⟩ := (S n).2 f hf (by linarith)
  obtain ⟨k, hk⟩ := hS n y hy
  rw [← hk] at hfy
  exact hfy.trans_le (evaluation_le_nullSequenceSeminorm x (f - f₀) k)

end ClosedSlices

section FinalTopology
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Relative closedness in a dual ball is ambient weak-star closedness of
its image, because the ball is compact and the weak-star topology is Hausdorff. -/
lemma weakstar_slice_closed_of_relative (C : Set (E →L[𝕜] 𝕜)) (r : ℝ) (hr : 0 ≤ r)
    (hrel : @IsClosed {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r}
      (TopologicalSpace.induced Subtype.val (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E))
      (Subtype.val ⁻¹' C)) :
    @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (C ∩ {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r}) := by
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have he : Topology.IsEmbedding
      (StrongDual.toWeakDual : (E →L[𝕜] 𝕜) → WeakDual 𝕜 E) :=
    ⟨⟨C12WeakStar.weakStarTopology_native 𝕜 E⟩, StrongDual.toWeakDual.injective⟩
  let : T2Space (E →L[𝕜] 𝕜) := he.t2Space
  have hball : IsClosed {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r} := by
    apply IsCompact.isClosed
    simpa only [sub_zero] using
      C13Alaoglu.weakStar_closedBall_isCompact 𝕜 E (0 : E →L[𝕜] 𝕜) r hr
  obtain ⟨D, hD, heq⟩ := isClosed_induced_iff.mp hrel
  have hmem : ∀ f : E →L[𝕜] 𝕜, ‖f‖ ≤ r → (f ∈ D ↔ f ∈ C) := by
    intro f hf
    exact Set.ext_iff.mp heq ⟨f, hf⟩
  convert hD.inter hball using 1
  ext f
  constructor
  · intro hf
    exact ⟨(hmem f hf.2).mpr hf.1, hf.2⟩
  · intro hf
    exact ⟨(hmem f hf.2).mp hf.1, hf.2⟩

lemma closed_of_closed_slices (C : Set (E →L[𝕜] 𝕜))
    (hC : ∀ r : ℝ, 0 < r → @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (C ∩ {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r})) :
    @IsClosed _ (boundedWeakstarTopology 𝕜 E) C := by
  classical
  let : TopologicalSpace (E →L[𝕜] 𝕜) := boundedWeakstarTopology 𝕜 E
  have hp : WithSeminorms (nullSequenceSeminorm 𝕜 E) := ⟨rfl⟩
  apply isOpen_compl_iff.mp
  rw [hp.isOpen_iff_mem_balls]
  intro f₀ hf₀
  obtain ⟨x, hx⟩ := nullSequence_excluding_closed_slices C hC f₀ hf₀
  refine ⟨{x}, 1, zero_lt_one, ?_⟩
  intro f hf hfc
  have hlt : nullSequenceSeminorm 𝕜 E x (f - f₀) < 1 := by
    simpa only [Finset.sup_singleton, Seminorm.mem_ball] using hf
  exact (not_lt_of_gt (hx f hfc)) hlt

end FinalTopology

theorem closed_criterion : Spec.ClosedCriterion := by
  intro 𝕜 E _ _ _ C
  constructor
  · intro hC r hr
    let A : Set (E →L[𝕜] 𝕜) := {f | ‖f‖ ≤ r}
    have hA : Bornology.IsBounded A := by
      exact isBounded_iff_forall_norm_le.mpr ⟨r, fun _ hf => hf⟩
    let : TopologicalSpace (E →L[𝕜] 𝕜) := Spec.TopologyValue 𝕜 E
    have hrel : @IsClosed A
        (TopologicalSpace.induced Subtype.val (Spec.TopologyValue 𝕜 E))
        (Subtype.val ⁻¹' C) := hC.preimage continuous_induced_dom
    rw [bounded_agreement 𝕜 E A hA] at hrel
    exact weakstar_slice_closed_of_relative C r hr.le hrel
  · exact closed_of_closed_slices C

/-- No linear or locally convex condition is imposed on the competing topology. -/
theorem finest_topology : Spec.Finest := by
  intro 𝕜 E _ _ _ t ht U hU
  let : TopologicalSpace (E →L[𝕜] 𝕜) := boundedWeakstarTopology 𝕜 E
  apply isClosed_compl_iff.mp
  apply closed_of_closed_slices Uᶜ
  intro r hr
  let A : Set (E →L[𝕜] 𝕜) := {f | ‖f‖ ≤ r}
  have hA : Bornology.IsBounded A :=
    isBounded_iff_forall_norm_le.mpr ⟨r, fun _ hf => hf⟩
  have hC : @IsClosed _ t Uᶜ :=
    (@isClosed_compl_iff (E →L[𝕜] 𝕜) t U).mpr hU
  have hrel : @IsClosed A (TopologicalSpace.induced Subtype.val t)
      (Subtype.val ⁻¹' Uᶜ) :=
    @IsClosed.preimage A (E →L[𝕜] 𝕜) (TopologicalSpace.induced Subtype.val t) t
      Subtype.val continuous_induced_dom Uᶜ hC
  rw [ht A hA] at hrel
  exact weakstar_slice_closed_of_relative Uᶜ r hr.le hrel

end ExpandedFA.P1.BoundedWeakstarTopology
