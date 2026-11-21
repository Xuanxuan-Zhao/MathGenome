import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HaarUnconditional
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.HaarBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15UnconditionalCriteria
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.Preorder.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Finite Haar multipliers, their uniform weak-(1,1) and L2 estimates,
and the analytic assembly of interior Lp unconditionality.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators unitInterval ComplexConjugate
universe u v
namespace ExpandedFA.P1.HaarUnconditional
open HaarBasis.Spec

abbrev finiteTransform := @Spec.finiteTransform

/-- Each individual finite transform is a continuous linear operator.
This construction alone gives no uniform bound over the finite sets. -/
def finiteTransformCLM (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (S : Finset ℕ) (m : ℕ → 𝕜) :
    Lp 𝕜 p (volume : Measure I) →L[𝕜] Lp 𝕜 p (volume : Measure I) :=
  ∑ n ∈ S, m n • (HaarBasis.haarCoefficientCLM 𝕜 p n).smulRight (haarLp 𝕜 p n)

@[simp] theorem finiteTransformCLM_apply (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : Finset ℕ) (m : ℕ → 𝕜)
    (f : Lp 𝕜 p (volume : Measure I)) :
    finiteTransformCLM 𝕜 p S m f = finiteTransform S m f := by
  simp [finiteTransformCLM, finiteTransform, Spec.finiteTransform, mul_smul]

/-- A finite transform acts diagonally on the actual Haar coordinates. -/
theorem haarCoefficient_finiteTransform {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : Finset ℕ) (m : ℕ → 𝕜)
    (f : Lp 𝕜 p (volume : Measure I)) (i : ℕ) :
    haarCoefficient (finiteTransform S m f) i =
      if i ∈ S then m i * haarCoefficient f i else 0 := by
  classical
  change HaarBasis.haarCoefficientCLM 𝕜 p i _ = _
  simp [finiteTransform, Spec.finiteTransform, map_sum, map_smul,
    HaarBasis.haarCoefficient_haarLp]

/-- Explicit representative of a finite transform, suitable for endpoint
measure estimates and compatibility between different Lp exponents. -/
theorem finiteTransform_ae {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : Finset ℕ) (m : ℕ → 𝕜) (f : Lp 𝕜 p (volume : Measure I)) :
    ⇑(finiteTransform S m f) =ᵐ[volume]
      fun x => ∑ i ∈ S, (m i * haarCoefficient f i) * haarFunction 𝕜 i x := by
  have hterm (i : ℕ) : ⇑((m i * haarCoefficient f i) • haarLp 𝕜 p i) =ᵐ[volume]
      fun x => (m i * haarCoefficient f i) * haarFunction 𝕜 i x :=
    (Lp.coeFn_smul _ _).trans ((HaarBasis.haar_representatives 𝕜 p i).fun_comp
      (fun z => (m i * haarCoefficient f i) * z))
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  filter_upwards [eventuallyEq_sum (s := S) (fun i _ => hterm i)] with x hx
  simpa only [Finset.sum_apply] using hx

/-- Fourier coefficients respect equality of representatives across exponents.
This is needed when treating the L1 and L2 restrictions as one operator. -/
theorem haarCoefficient_eq_of_ae {𝕜 : Type u} [RCLike 𝕜] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp 𝕜 p (volume : Measure I)) (g : Lp 𝕜 q (volume : Measure I))
    (hfg : ⇑f =ᵐ[volume] ⇑g) (i : ℕ) : haarCoefficient f i = haarCoefficient g i := by
  unfold haarCoefficient
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- The same finite polynomial acts on every Lp space: agreement is actual
a.e. equality, rather than an abstract isomorphism of its ranges. -/
theorem finiteTransform_compatible {𝕜 : Type u} [RCLike 𝕜] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (S : Finset ℕ) (m : ℕ → 𝕜)
    (f : Lp 𝕜 p (volume : Measure I)) (g : Lp 𝕜 q (volume : Measure I))
    (hfg : ⇑f =ᵐ[volume] ⇑g) :
    ⇑(finiteTransform S m f) =ᵐ[volume] ⇑(finiteTransform S m g) := by
  apply (finiteTransform_ae S m f).trans
  apply Filter.EventuallyEq.trans _ (finiteTransform_ae S m g).symm
  apply Filter.Eventually.of_forall
  intro x
  apply Finset.sum_congr rfl
  intro i _
  rw [haarCoefficient_eq_of_ae f g hfg i]

/-- A finite collection of dyadic cells, including the root, through M. -/
def dyadicCellsThrough (M : ℕ) : Finset (Set I) := by
  classical
  exact (Finset.range (M + 1)).biUnion fun l =>
    (Finset.range (2 ^ l)).image (dyadicCell l)

theorem mem_dyadicCellsThrough (M : ℕ) (s : Set I) :
    s ∈ dyadicCellsThrough M ↔ ∃ l ≤ M, ∃ k < 2 ^ l, s = dyadicCell l k := by
  classical
  simp only [dyadicCellsThrough, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨l, hl, k, hk, rfl⟩
    exact ⟨l, hl, k, hk, rfl⟩
  · rintro ⟨l, hl, k, hk, rfl⟩
    exact ⟨l, hl, k, hk, rfl⟩

/-- The dyadic family is laminar, even across different levels. -/
theorem dyadicCells_laminar (l m j k : ℕ) :
    dyadicCell l j ⊆ dyadicCell m k ∨ dyadicCell m k ⊆ dyadicCell l j ∨
      Disjoint (dyadicCell l j) (dyadicCell m k) := by
  rcases le_total l m with h | h
  · rcases HaarBasis.dyadicCell_subset_or_disjoint l m j k h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.symm)
  · rcases HaarBasis.dyadicCell_subset_or_disjoint m l k j h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- Finite maximal selection for a laminar family. It covers every member
and is pairwise disjoint. In particular, no infinite stopping-time argument
is needed for any one finite Haar transform. -/
theorem finite_laminar_maximal_cover (C : Finset (Set I))
    (hC : ∀ s ∈ C, ∀ t ∈ C, s ⊆ t ∨ t ⊆ s ∨ Disjoint s t) :
    ∃ D : Finset (Set I), D ⊆ C ∧
      (∀ s ∈ D, Maximal (· ∈ C) s) ∧
      Set.PairwiseDisjoint (D : Set (Set I)) id ∧
      ∀ s ∈ C, ∃ t ∈ D, s ⊆ t := by
  classical
  let D := C.filter fun s => Maximal (· ∈ C) s
  have hD (s : Set I) (hs : s ∈ D) : Maximal (· ∈ C) s :=
    (Finset.mem_filter.mp hs).2
  refine ⟨D, Finset.filter_subset _ _, hD, ?_, ?_⟩
  · intro s hs t ht hst
    have hsC := (hD s hs).1
    have htC := (hD t ht).1
    rcases hC s hsC t htC with h | h | h
    · exact (hst ((hD s hs).eq_of_subset htC h)).elim
    · exact (hst ((hD t ht).eq_of_subset hsC h).symm).elim
    · exact h
  · intro s hs
    obtain ⟨t, hst, ht⟩ := C.exists_le_maximal hs
    exact ⟨t, Finset.mem_filter.mpr ⟨ht.1, ht⟩, hst⟩

/-- The exceptional union of any finite disjoint bad family has the required
L1 measure estimate, including an empty family and a bad root. -/
theorem bad_union_measure_le {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I)) (D : Finset (Set I))
    (hD : Set.PairwiseDisjoint (D : Set (Set I)) id)
    (hDm : ∀ s ∈ D, MeasurableSet s) (t : ℝ) (ht : 0 < t)
    (hbad : ∀ s ∈ D, t * (volume : Measure I).real s ≤ ∫ x in s, ‖f x‖) :
    volume (⋃ s ∈ D, s) ≤ ENNReal.ofReal (‖f‖ / t) := by
  have hi : Integrable (fun x => ‖f x‖) volume := (Lp.memLp f).integrable le_rfl |>.norm
  have hmeasure : (volume : Measure I).real (⋃ s ∈ D, s) =
      ∑ s ∈ D, (volume : Measure I).real s := by
    simpa only [id_eq] using measureReal_biUnion_finset (μ := (volume : Measure I))
      hD hDm (fun _ _ => measure_ne_top _ _)
  have hm : t * (volume : Measure I).real (⋃ s ∈ D, s) ≤ ‖f‖ := by
    rw [hmeasure, Finset.mul_sum, L1.norm_eq_integral_norm]
    calc
      _ ≤ ∑ s ∈ D, ∫ x in s, ‖f x‖ := Finset.sum_le_sum hbad
      _ = ∫ x in ⋃ s ∈ D, s, ‖f x‖ :=
        (integral_biUnion_finset D hDm hD (fun _ _ => hi.integrableOn)).symm
      _ ≤ ∫ x, ‖f x‖ := integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (fun x => norm_nonneg _)) hi
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (div_nonneg (norm_nonneg _) ht.le)]
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm, measureReal_def] using hm

/-- Bad cells at finitely many levels; the test avoids division by a cell
measure and agrees with the usual average test on these positive cells. -/
def badDyadicCells {𝕜 : Type u} [RCLike 𝕜]
    (M : ℕ) (f : Lp 𝕜 1 (volume : Measure I)) (t : ℝ) : Finset (Set I) := by
  classical
  exact (dyadicCellsThrough M).filter fun s =>
    t * (volume : Measure I).real s < ∫ x in s, ‖f x‖

theorem mem_badDyadicCells {𝕜 : Type u} [RCLike 𝕜]
    (M : ℕ) (f : Lp 𝕜 1 (volume : Measure I)) (t : ℝ) (s : Set I) :
    s ∈ badDyadicCells M f t ↔ s ∈ dyadicCellsThrough M ∧
      t * (volume : Measure I).real s < ∫ x in s, ‖f x‖ := by
  classical
  exact Finset.mem_filter

theorem exists_maximal_bad_dyadic_family {𝕜 : Type u} [RCLike 𝕜]
    (M : ℕ) (f : Lp 𝕜 1 (volume : Measure I)) (t : ℝ) :
    ∃ D : Finset (Set I), D ⊆ badDyadicCells M f t ∧
      (∀ s ∈ D, Maximal (· ∈ badDyadicCells M f t) s) ∧
      Set.PairwiseDisjoint (D : Set (Set I)) id ∧
      ∀ s ∈ badDyadicCells M f t, ∃ v ∈ D, s ⊆ v := by
  apply finite_laminar_maximal_cover
  intro s hs v hv
  obtain ⟨l, _, k, _, rfl⟩ := (mem_dyadicCellsThrough M s).mp ((mem_badDyadicCells M f t s).mp hs).1
  obtain ⟨m, _, j, _, rfl⟩ := (mem_dyadicCellsThrough M v).mp ((mem_badDyadicCells M f t v).mp hv).1
  exact dyadicCells_laminar l m k j

/-- The ordinary scalar mean on a measurable cell. -/
def cellMean {𝕜 : Type u} [RCLike 𝕜] (f : I → 𝕜) (s : Set I) : 𝕜 :=
  ((volume : Measure I).real s)⁻¹ • ∫ x in s, f x

theorem cellMean_norm_mul_measure_le {𝕜 : Type u} [RCLike 𝕜]
    (f : I → 𝕜) (s : Set I) (hs : 0 < (volume : Measure I).real s) :
    (volume : Measure I).real s * ‖cellMean f s‖ ≤ ∫ x in s, ‖f x‖ := by
  rw [cellMean, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs),
    ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  exact norm_integral_le_integral_norm _

theorem cellMean_integral {𝕜 : Type u} [RCLike 𝕜]
    (f : I → 𝕜) (s : Set I) (hs : 0 < (volume : Measure I).real s) :
    (∫ x in s, cellMean f s) = ∫ x in s, f x := by
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ]
  change (volume : Measure I).real s • cellMean f s = _
  rw [cellMean, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

/-- A maximal proper bad cell has a good parent, so its mean is at most
2t. The root is excluded by the explicitly stated small-total-mass case;
large total mass is handled directly in the weak estimate. -/
theorem maximal_bad_cell_mean_le {𝕜 : Type u} [RCLike 𝕜]
    (M : ℕ) (f : Lp 𝕜 1 (volume : Measure I)) (t : ℝ) (hft : ‖f‖ ≤ t)
    (l k : ℕ) (hl : l ≤ M) (hk : k < 2 ^ l)
    (hmax : Maximal (· ∈ badDyadicCells M f t) (dyadicCell l k)) :
    ‖cellMean f (dyadicCell l k)‖ ≤ 2 * t := by
  have hfi : Integrable (fun x => ‖f x‖) volume := ((Lp.memLp f).integrable le_rfl).norm
  have hbad := ((mem_badDyadicCells M f t _).mp hmax.1).2
  cases l with
  | zero =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    have hi : (∫ x in dyadicCell 0 0, ‖f x‖) ≤ ‖f‖ := by
      rw [L1.norm_eq_integral_norm]
      exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun _ => norm_nonneg _)) hfi
    rw [HaarBasis.real_volume_dyadicCell 0 0 (by norm_num)] at hbad
    norm_num at hbad
    exact (not_lt_of_ge (hi.trans hft) hbad).elim
  | succ l =>
    have hkp : k / 2 < 2 ^ l := by rw [pow_succ] at hk; omega
    have hsub := HaarBasis.dyadicCell_subset_parent l k
    have hvol : (volume : Measure I).real (dyadicCell l (k / 2)) =
        2 * (volume : Measure I).real (dyadicCell (l + 1) k) := by
      rw [HaarBasis.real_volume_dyadicCell l _ hkp,
        HaarBasis.real_volume_dyadicCell (l + 1) _ hk, pow_succ]
      ring
    have hpos : 0 < (volume : Measure I).real (dyadicCell (l + 1) k) := by
      rw [HaarBasis.real_volume_dyadicCell _ _ hk]
      positivity
    have hne : dyadicCell (l + 1) k ≠ dyadicCell l (k / 2) := by
      intro heq
      have heqv := congrArg (fun s => (volume : Measure I).real s) heq
      nlinarith
    have hparent : (∫ x in dyadicCell l (k / 2), ‖f x‖) ≤
        t * (volume : Measure I).real (dyadicCell l (k / 2)) := by
      by_contra! h
      have hm : dyadicCell l (k / 2) ∈ badDyadicCells M f t :=
        (mem_badDyadicCells M f t _).mpr
          ⟨(mem_dyadicCellsThrough M _).mpr ⟨l, by omega, k / 2, hkp, rfl⟩, h⟩
      exact hne (hmax.eq_of_subset hm hsub)
    have hmono : (∫ x in dyadicCell (l + 1) k, ‖f x‖) ≤
        ∫ x in dyadicCell l (k / 2), ‖f x‖ :=
      integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (ae_of_all _ (fun _ => norm_nonneg _)) hfi.integrableOn
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      _ ≤ ∫ x in dyadicCell (l + 1) k, ‖f x‖ := cellMean_norm_mul_measure_le f _ hpos
      _ ≤ t * (volume : Measure I).real (dyadicCell l (k / 2)) := hmono.trans hparent
      _ = _ := by rw [hvol]; ring

/-- A single centered piece, as an actual L1 element. -/
def cellBadPart {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I)) (s : Set I) (hs : MeasurableSet s) :
    Lp 𝕜 1 (volume : Measure I) :=
  (((Lp.memLp f).sub (memLp_const (cellMean f s))).indicator hs.nullMeasurableSet).toLp
    (s.indicator fun x => f x - cellMean f s)

theorem cellBadPart_ae {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I)) (s : Set I) (hs : MeasurableSet s) :
    ⇑(cellBadPart f s hs) =ᵐ[volume] s.indicator (fun x => f x - cellMean f s) :=
  MemLp.coeFn_toLp _

theorem cellBadPart_mean_zero {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I)) (s : Set I) (hs : MeasurableSet s)
    (hpos : 0 < (volume : Measure I).real s) :
    (∫ x : I, cellBadPart f s hs x) = 0 := by
  rw [integral_congr_ae (cellBadPart_ae f s hs), integral_indicator hs,
    integral_sub ((Lp.memLp f).integrable le_rfl).integrableOn (integrable_const _),
    cellMean_integral f s hpos, sub_self]

/-- At a point of one cell, a sum of indicators of a disjoint family
has precisely that cell's summand. -/
theorem sum_indicators_on_cell {𝕜 : Type u} [RCLike 𝕜]
    (D : Finset (Set I)) (hD : Set.PairwiseDisjoint (D : Set (Set I)) id)
    (a : Set I → I → 𝕜) {s : Set I} (hs : s ∈ D) {x : I} (hx : x ∈ s) :
    (∑ v ∈ D, v.indicator (a v) x) = a s x := by
  classical
  rw [Finset.sum_eq_single s]
  · exact Set.indicator_of_mem hx _
  · intro v hv hvs
    apply Set.indicator_of_notMem
    intro hxv
    exact Set.disjoint_left.mp (hD hv hs hvs) hxv hx
  · exact fun h => (h hs).elim

/-- The finite dyadic good part, prior to its uniform estimates. -/
def cellGoodPart {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I)) (D : Finset (Set I))
    (hDm : ∀ s ∈ D, MeasurableSet s) : Lp 𝕜 1 (volume : Measure I) :=
  f - ∑ s ∈ D.attach, cellBadPart f s.1 (hDm s.1 s.2)

/-- The good part equals the cell mean on each selected cell and equals
the original input outside their union, all with the native representatives. -/
theorem cellGoodPart_ae {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I)) (D : Finset (Set I))
    (hDm : ∀ s ∈ D, MeasurableSet s)
    (hD : Set.PairwiseDisjoint (D : Set (Set I)) id) :
    (∀ᵐ x ∂volume, (∀ s ∈ D, x ∈ s → cellGoodPart f D hDm x = cellMean f s) ∧
      (x ∉ ⋃ s ∈ D, s → cellGoodPart f D hDm x = f x)) := by
  classical
  have hbad : ⇑(∑ s ∈ D.attach, cellBadPart f s.1 (hDm s.1 s.2)) =ᵐ[volume]
      fun x => ∑ s ∈ D, s.indicator (fun y => f y - cellMean f s) x := by
    refine (Lp.coeFn_finsetSum _ _).trans ?_
    have he := eventuallyEq_sum (s := D.attach)
      (fun s _ => cellBadPart_ae f s.1 (hDm s.1 s.2))
    filter_upwards [he] with x hx
    simp only [Finset.sum_apply] at hx
    simpa only [Finset.sum_apply] using
      hx.trans (Finset.sum_attach D (fun s => s.indicator (fun y => f y - cellMean f s) x))
  filter_upwards [Lp.coeFn_sub f (∑ s ∈ D.attach, cellBadPart f s.1 (hDm s.1 s.2)),
    hbad] with x hx hxb
  change cellGoodPart f D hDm x = f x - _ at hx
  rw [hxb] at hx
  constructor
  · intro s hs hxs
    rw [hx, sum_indicators_on_cell D hD _ hs hxs]
    ring
  · intro hnot
    rw [hx]
    have hz : (∑ s ∈ D, s.indicator (fun y => f y - cellMean f s) x) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      apply Set.indicator_of_notMem
      intro hxs
      exact hnot (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, hxs⟩⟩)
    rw [hz, sub_zero]

/-- Averaging on finitely many disjoint cells is an L1 contraction. -/
theorem cellGoodPart_norm_le {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I)) (D : Finset (Set I))
    (hDm : ∀ s ∈ D, MeasurableSet s)
    (hD : Set.PairwiseDisjoint (D : Set (Set I)) id)
    (hpos : ∀ s ∈ D, 0 < (volume : Measure I).real s) :
    ‖cellGoodPart f D hDm‖ ≤ ‖f‖ := by
  let g := cellGoodPart f D hDm
  let B := ⋃ s ∈ D, s
  have hB : MeasurableSet B := Finset.measurableSet_biUnion D hDm
  have hfg := cellGoodPart_ae f D hDm hD
  have hfi : Integrable (fun x => ‖f x‖) volume := ((Lp.memLp f).integrable le_rfl).norm
  have hgi : Integrable (fun x => ‖g x‖) volume := ((Lp.memLp g).integrable le_rfl).norm
  have hcomp : (∫ x in Bᶜ, ‖g x‖) = ∫ x in Bᶜ, ‖f x‖ := by
    apply setIntegral_congr_ae hB.compl
    filter_upwards [hfg] with x hx hxc
    rw [hx.2 hxc]
  have hcell (s : Set I) (hs : s ∈ D) :
      (∫ x in s, ‖g x‖) ≤ ∫ x in s, ‖f x‖ := by
    calc
      _ = ∫ x in s, ‖cellMean f s‖ := by
        apply setIntegral_congr_ae (hDm s hs)
        filter_upwards [hfg] with x hx hxs
        rw [hx.1 s hs hxs]
      _ = (volume : Measure I).real s * ‖cellMean f s‖ := by simp [mul_comm]
      _ ≤ _ := cellMean_norm_mul_measure_le f s (hpos s hs)
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm,
    ← integral_add_compl hB hgi, ← integral_add_compl hB hfi, hcomp]
  apply add_le_add_left
  have hsumg : (∫ x in B, ‖g x‖) = ∑ s ∈ D, ∫ x in s, ‖g x‖ := by
    exact integral_biUnion_finset D hDm hD (fun _ _ => hgi.integrableOn)
  have hsumf : (∫ x in B, ‖f x‖) = ∑ s ∈ D, ∫ x in s, ‖f x‖ := by
    exact integral_biUnion_finset D hDm hD (fun _ _ => hfi.integrableOn)
  rw [hsumg, hsumf]
  exact Finset.sum_le_sum hcell

/-- A complete-level Haar polynomial is constant on every atom at that
level, including the level-zero case. -/
theorem haarPolynomial_constant_on_cell {𝕜 : Type u} [RCLike 𝕜]
    (a : ℕ → 𝕜) (M k : ℕ) :
    ∃ c : 𝕜, ∀ x ∈ dyadicCell M k,
      (∑ i ∈ Finset.range (2 ^ M), a i * haarFunction 𝕜 i x) = c := by
  classical
  have hex (i : ℕ) : ∃ c : 𝕜, ∀ x ∈ dyadicCell M k,
      i < 2 ^ M → haarFunction 𝕜 i x = c := by
    by_cases hi : i = 0
    · subst i
      exact ⟨1, fun _ _ _ => by simp [haarFunction]⟩
    · by_cases hiM : i < 2 ^ M
      · obtain ⟨c, hc⟩ := HaarBasis.haarFunction_constant_on_cell 𝕜 i M k
          ((Nat.log2_lt hi).mpr hiM)
        exact ⟨c, fun x hx _ => hc x hx⟩
      · exact ⟨0, fun _ _ h => (hiM h).elim⟩
  choose c hc using hex
  refine ⟨∑ i ∈ Finset.range (2 ^ M), a i * c i, fun x hx => ?_⟩
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i x hx (Finset.mem_range.mp hi)]

/-- For a complete-level polynomial, outside the selected bad cells the
finest atom is good, and constancy yields the pointwise bound directly.
This avoids any appeal to differentiation or a.e. convergence subsequences. -/
theorem dyadic_polynomial_bound_outside_bad {𝕜 : Type u} [RCLike 𝕜]
    (M : ℕ) (f : Lp 𝕜 1 (volume : Measure I))
    (hfix : haarPartialSum (2 ^ M) f = f) (t : ℝ) (D : Finset (Set I))
    (hcover : ∀ s ∈ badDyadicCells M f t, ∃ v ∈ D, s ⊆ v) :
    ∀ᵐ x ∂volume, x ∉ ⋃ s ∈ D, s → ‖f x‖ ≤ t := by
  classical
  have hrep : ⇑f =ᵐ[volume] fun x =>
      ∑ i ∈ Finset.range (2 ^ M), haarCoefficient f i * haarFunction 𝕜 i x := by
    have hh := HaarBasis.haarSynthesis_ae 𝕜 1 (haarCoefficient f) (2 ^ M)
    change ⇑(haarPartialSum (2 ^ M) f) =ᵐ[volume] _ at hh
    rwa [hfix] at hh
  filter_upwards [hrep, (volume : Measure I).ae_ne (1 : I)] with x hx hx1 hout
  have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 (fun h => hx1 (Subtype.ext h))
  obtain ⟨k, hxk⟩ := HaarBasis.exists_dyadicCell M x hxlt
  have hk := k.isLt
  have hgood : (∫ y in dyadicCell M k, ‖f y‖) ≤
      t * (volume : Measure I).real (dyadicCell M k) := by
    by_contra! hbad
    have hmem : dyadicCell M k ∈ badDyadicCells M f t :=
      (mem_badDyadicCells M f t _).mpr
        ⟨(mem_dyadicCellsThrough M _).mpr ⟨M, le_rfl, k, hk, rfl⟩, hbad⟩
    obtain ⟨v, hv, hsub⟩ := hcover _ hmem
    exact hout (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, hsub hxk⟩⟩)
  obtain ⟨c, hc⟩ := haarPolynomial_constant_on_cell (haarCoefficient f) M k
  have hint : (∫ y in dyadicCell M k, ‖f y‖) =
      (volume : Measure I).real (dyadicCell M k) * ‖c‖ := by
    calc
      _ = ∫ y in dyadicCell M k, ‖c‖ := by
        apply setIntegral_congr_ae (measurableSet_dyadicCell M k)
        filter_upwards [hrep] with y hy hyk
        rw [hy, hc y hyk]
      _ = _ := by simp
  rw [hint] at hgood
  have hpos : 0 < (volume : Measure I).real (dyadicCell M k) := by
    rw [HaarBasis.real_volume_dyadicCell M k hk]
    positivity
  rw [hx, hc x hxk]
  apply (mul_le_mul_iff_right₀ hpos).mp
  simpa only [mul_comm] using hgood

/-- A transform supported in a prefix is unchanged after the corresponding
Haar projection of its input. The empty prefix and empty set are included. -/
theorem finiteTransform_partialSum {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (S : Finset ℕ) (m : ℕ → 𝕜) (N : ℕ)
    (hS : ∀ i ∈ S, i < N) (f : Lp 𝕜 p (volume : Measure I)) :
    finiteTransform S m (haarPartialSum N f) = finiteTransform S m f := by
  apply Finset.sum_congr rfl
  intro i hi
  change (m i * haarCoefficient
    (C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p) (haarCoefficient f) N) i) • _ = _
  rw [HaarBasis.haarCoefficient_partialSum, ite_eq_left (hS i hi)]

/-- Changing the exponent of a finite Haar synthesis preserves its actual
representative. This is a concrete bridge, not an identification of all Lp. -/
theorem haarSynthesis_compatible {𝕜 : Type u} [RCLike 𝕜] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (a : ℕ → 𝕜) (N : ℕ) :
    ⇑(C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p) a N) =ᵐ[volume]
      ⇑(C15Basis.Spec.orderedPartialSum (haarLp 𝕜 q) a N) :=
  (HaarBasis.haarSynthesis_ae 𝕜 p a N).trans (HaarBasis.haarSynthesis_ae 𝕜 q a N).symm

/-- Before estimating a fixed finite transform, an arbitrary L1 input may
be replaced by a complete-level dyadic polynomial with no increase in L1
norm. The same polynomial is an L2 function, and the transforms agree a.e. -/
theorem finiteTransform_dyadic_reduction {𝕜 : Type u} [RCLike 𝕜]
    (S : Finset ℕ) (m : ℕ → 𝕜) (f : Lp 𝕜 1 (volume : Measure I)) :
    ∃ (M : ℕ) (F : Lp 𝕜 1 (volume : Measure I)) (G : Lp 𝕜 2 (volume : Measure I)),
      (∀ i ∈ S, i < 2 ^ M) ∧ F = haarPartialSum (2 ^ M) f ∧
      ‖F‖ ≤ ‖f‖ ∧ ⇑F =ᵐ[volume] ⇑G ∧
      haarPartialSum (2 ^ M) F = F ∧
      finiteTransform S m F = finiteTransform S m f ∧
      ⇑(finiteTransform S m f) =ᵐ[volume] ⇑(finiteTransform S m G) := by
  classical
  let M := S.sup id + 1
  have hS : ∀ i ∈ S, i < 2 ^ M := by
    intro i hi
    exact (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)).trans_le
      (Nat.le_of_lt (Nat.lt_two_pow_self))
  let F := haarPartialSum (2 ^ M) f
  let G := C15Basis.Spec.orderedPartialSum (haarLp 𝕜 2) (haarCoefficient f) (2 ^ M)
  have hFG : ⇑F =ᵐ[volume] ⇑G := haarSynthesis_compatible (haarCoefficient f) _
  have hTF : finiteTransform S m F = finiteTransform S m f :=
    finiteTransform_partialSum S m _ hS f
  refine ⟨M, F, G, hS, rfl, HaarBasis.haar_contractions 𝕜 1 (by simp) _ f,
    hFG, ?_, hTF, ?_⟩
  · simpa only [min_self] using HaarBasis.haarPartialSum_comp (2 ^ M) (2 ^ M) f
  · rw [← hTF]
    exact finiteTransform_compatible S m F G hFG

/-- Consequently a weak estimate need only be proved for complete-level
Haar polynomials. This implication does not assert that estimate. -/
theorem weak_bound_of_dyadic_polynomials {𝕜 : Type u} [RCLike 𝕜]
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (M : ℕ) (S : Finset ℕ) (m : ℕ → 𝕜),
      (∀ i ∈ S, i < 2 ^ M) → (∀ i ∈ S, ‖m i‖ ≤ 1) →
      ∀ F : Lp 𝕜 1 (volume : Measure I), haarPartialSum (2 ^ M) F = F →
      ∀ t : ℝ, 0 < t → volume {x : I | t < ‖finiteTransform S m F x‖} ≤
        ENNReal.ofReal (C * ‖F‖ / t))
    (S : Finset ℕ) (m : ℕ → 𝕜) (hm : ∀ i ∈ S, ‖m i‖ ≤ 1)
    (f : Lp 𝕜 1 (volume : Measure I)) (t : ℝ) (ht : 0 < t) :
    volume {x : I | t < ‖finiteTransform S m f x‖} ≤ ENNReal.ofReal (C * ‖f‖ / t) := by
  obtain ⟨M, F, G, hS, _, hn, _, hfix, heq, _⟩ := finiteTransform_dyadic_reduction S m f
  rw [← heq]
  apply (hb M S m hS hm F hfix t ht).trans
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC) ht.le

/-- Cancellation against any function constant on the support cell. -/
theorem integral_mul_eq_zero_of_cell_constant {𝕜 : Type u} [RCLike 𝕜]
    {b h : I → 𝕜} (l k : ℕ)
    (hb : ∀ᵐ x ∂volume, x ∉ dyadicCell l k → b x = 0)
    (hmean : (∫ x : I, b x) = 0)
    (hc : ∃ c : 𝕜, ∀ x ∈ dyadicCell l k, h x = c) :
    (∫ x : I, b x * h x) = 0 := by
  obtain ⟨c, hc⟩ := hc
  have heq : (fun x => b x * h x) =ᵐ[volume] (fun x => b x * c) := by
    filter_upwards [hb] with x hx
    by_cases hxc : x ∈ dyadicCell l k
    · rw [hc x hxc]
    · rw [hx hxc, zero_mul, zero_mul]
  rw [integral_congr_ae heq, integral_mul_const, hmean, zero_mul]

/-- A mean-zero cell-supported function has no coarser Haar coefficients,
including the coefficient of the constant function. -/
theorem haarCoefficient_eq_zero_of_cell {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : Lp 𝕜 p (volume : Measure I))
    (l k i : ℕ) (hb : ∀ᵐ x ∂volume, x ∉ dyadicCell l k → b x = 0)
    (hmean : (∫ x : I, b x) = 0) (hi : i = 0 ∨ haarLevel i < l) :
    haarCoefficient b i = 0 := by
  have hc : ∃ c : 𝕜, ∀ x ∈ dyadicCell l k, haarFunction 𝕜 i x = c := by
    rcases hi with hi | hi
    · subst i
      exact ⟨1, fun x _ => by simp [haarFunction]⟩
    · exact HaarBasis.haarFunction_constant_on_cell 𝕜 i l k hi
  rw [haarCoefficient, integral_mul_eq_zero_of_cell_constant l k hb hmean hc, mul_zero]

/-- Cancellation localizes every finite Haar transform of a mean-zero bad
piece to the very same dyadic cell. No multiplier bound is needed for support. -/
theorem finiteTransform_supported_in_cell {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : Finset ℕ) (m : ℕ → 𝕜)
    (b : Lp 𝕜 p (volume : Measure I)) (l k : ℕ)
    (hb : ∀ᵐ x ∂volume, x ∉ dyadicCell l k → b x = 0)
    (hmean : (∫ x : I, b x) = 0) :
    ∀ᵐ x ∂volume, x ∉ dyadicCell l k → finiteTransform S m b x = 0 := by
  classical
  filter_upwards [finiteTransform_ae S m b] with x hx hxc
  rw [hx]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = 0 ∨ haarLevel i < l
  · rw [haarCoefficient_eq_zero_of_cell b l k i hb hmean hi, mul_zero, zero_mul]
  · have hi0 : i ≠ 0 := fun h => hi (Or.inl h)
    have hli : l ≤ haarLevel i := by omega
    rcases HaarBasis.dyadicCell_subset_or_disjoint l (haarLevel i) k
      (haarPosition i) hli with hsub | hdisj
    · rw [HaarBasis.haarFunction_eq_zero_of_notMem 𝕜 hi0
        (fun h => hxc (hsub h)), mul_zero]
    · have hpair : (∫ y : I, b y * haarFunction 𝕜 i y) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hb] with y hy
        change b y * haarFunction 𝕜 i y = 0
        by_cases hyc : y ∈ dyadicCell l k
        · rw [HaarBasis.haarFunction_eq_zero_of_notMem 𝕜 hi0
            (fun hyi => Set.disjoint_left.mp hdisj hyi hyc), mul_zero]
        · rw [hy hyc, zero_mul]
      simp only [haarCoefficient, hpair, mul_zero, zero_mul]

/-- Pairing with a finite transform is well defined already for two L1
inputs, since its output is a finite sum of bounded Haar functions. -/
theorem mul_finiteTransform_integrable {𝕜 : Type u} [RCLike 𝕜] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (S : Finset ℕ) (m : ℕ → 𝕜)
    (f : Lp 𝕜 p (volume : Measure I)) (g : Lp 𝕜 q (volume : Measure I)) :
    Integrable (fun x => f x * finiteTransform S m g x) volume := by
  have hi : Integrable
      (fun x => ∑ i ∈ S, (m i * haarCoefficient g i) * (f x * haarFunction 𝕜 i x)) volume :=
    integrable_finsetSum S (fun i _ => (HaarBasis.haarProduct_integrable f i).const_mul _)
  apply hi.congr
  filter_upwards [finiteTransform_ae S m g] with x hx
  rw [hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The bilinear integral pairing used in the accepted scalar-linear Lp
duality makes a Haar multiplier its own transpose. No conjugation is needed
for this bilinear pairing, even when the multipliers are complex. -/
theorem finiteTransform_pairing {𝕜 : Type u} [RCLike 𝕜] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (S : Finset ℕ) (m : ℕ → 𝕜)
    (f : Lp 𝕜 p (volume : Measure I)) (g : Lp 𝕜 q (volume : Measure I)) :
    (∫ x : I, f x * finiteTransform S m g x) =
      ∫ x : I, finiteTransform S m f x * g x := by
  have hformula {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)]
      (v : Lp 𝕜 r (volume : Measure I)) (w : Lp 𝕜 s (volume : Measure I)) :
      (∫ x : I, v x * finiteTransform S m w x) =
        ∑ i ∈ S, m i * (if i = 0 then 1 else (2 : 𝕜) ^ haarLevel i) *
          (∫ x : I, v x * haarFunction 𝕜 i x) *
          (∫ x : I, w x * haarFunction 𝕜 i x) := by
    calc
      _ = ∫ x : I, ∑ i ∈ S,
          (m i * haarCoefficient w i) * (v x * haarFunction 𝕜 i x) := by
        apply integral_congr_ae
        filter_upwards [finiteTransform_ae S m w] with x hx
        rw [hx, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i ∈ S, ∫ x : I,
          (m i * haarCoefficient w i) * (v x * haarFunction 𝕜 i x) :=
        integral_finsetSum S (fun i _ => (HaarBasis.haarProduct_integrable v i).const_mul _)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul, haarCoefficient]
        ring
  rw [hformula]
  calc
    _ = ∑ i ∈ S, m i * (if i = 0 then 1 else (2 : 𝕜) ^ haarLevel i) *
        (∫ x : I, g x * haarFunction 𝕜 i x) *
        (∫ x : I, f x * haarFunction 𝕜 i x) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∫ x : I, g x * finiteTransform S m f x := (hformula g f).symm
    _ = _ := by congr 1; funext x; exact mul_comm _ _

/-- Duality transfers a bound at q to its Hölder conjugate p, with the
same constant and the same multiplier. This uses the scalar-linear pairing,
so it applies to complex multipliers without changing their phases. -/
theorem finiteTransform_bound_of_conjugate_bound {𝕜 : Type} [RCLike 𝕜]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hq : q ≠ ∞)
    (S : Finset ℕ) (m : ℕ → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ g : Lp 𝕜 q (volume : Measure I),
      ‖finiteTransform S m g‖ ≤ C * ‖g‖)
    (f : Lp 𝕜 p (volume : Measure I)) :
    ‖finiteTransform S m f‖ ≤ C * ‖f‖ := by
  open ExpandedFA.FunctionSpaces in
  rw [← lp_pairing_exact_norm volume q p hq (Or.inl inferInstance)
    (finiteTransform S m f)]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg f))
  intro g
  rw [(lp_pairing_integral volume q p (finiteTransform S m f) g).2,
    finiteTransform_pairing S m g f,
    ← (lp_pairing_integral volume q p f (finiteTransform S m g)).2]
  calc
    _ ≤ ‖f‖ * ‖finiteTransform S m g‖ :=
      lp_pairing_apply_bound volume q p f (finiteTransform S m g)
    _ ≤ ‖f‖ * (C * ‖g‖) := mul_le_mul_of_nonneg_left (hb g) (norm_nonneg f)
    _ = (C * ‖f‖) * ‖g‖ := by ring

/-- In particular a uniform family bound passes to conjugate exponents. -/
theorem uniform_bounds_of_conjugate {𝕜 : Type} [RCLike 𝕜]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hq : q ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (S : Finset ℕ) (m : ℕ → 𝕜), (∀ n ∈ S, ‖m n‖ ≤ 1) →
      ∀ g : Lp 𝕜 q (volume : Measure I), ‖finiteTransform S m g‖ ≤ C * ‖g‖) :
    ∀ (S : Finset ℕ) (m : ℕ → 𝕜), (∀ n ∈ S, ‖m n‖ ≤ 1) →
      ∀ f : Lp 𝕜 p (volume : Measure I), ‖finiteTransform S m f‖ ≤ C * ‖f‖ := by
  intro S m hm f
  exact finiteTransform_bound_of_conjugate_bound hq S m hC (hb S m hm) f

/-- Haar functions take real values even over the complex field. -/
theorem conj_haarFunction (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (x : I) :
    conj (haarFunction 𝕜 n x) = haarFunction 𝕜 n x := by
  by_cases hn : n = 0
  · simp [haarFunction, hn]
  · by_cases hl : x ∈ leftCell n <;> by_cases hr : x ∈ rightCell n <;>
      simp [haarFunction, hn, Set.indicator, hl, hr]

/-- The integral orthogonality proved upstream is the actual Hilbert-space
orthogonality on L2; conjugation of the first argument is included. -/
theorem haarLp_inner_eq_zero (𝕜 : Type u) [RCLike 𝕜] {i j : ℕ} (hij : i ≠ j) :
    inner 𝕜 (haarLp 𝕜 2 i) (haarLp 𝕜 2 j) = 0 := by
  rw [L2.inner_def]
  have heq : (fun x : I => inner 𝕜 ((haarLp 𝕜 2 i) x) ((haarLp 𝕜 2 j) x)) =ᵐ[volume]
      (fun x => haarFunction 𝕜 i x * haarFunction 𝕜 j x) := by
    filter_upwards [HaarBasis.haar_representatives 𝕜 2 i,
      HaarBasis.haar_representatives 𝕜 2 j] with x hi hj
    simp [hi, hj, RCLike.inner_apply, conj_haarFunction, mul_comm]
  rw [integral_congr_ae heq]
  exact HaarBasis.haarFunction_integral_mul_of_ne 𝕜 hij

/-- Finite Pythagoras for Haar synthesis, without any normalization choice. -/
theorem haarSynthesis_norm_sq (𝕜 : Type u) [RCLike 𝕜]
    (S : Finset ℕ) (a : ℕ → 𝕜) :
    ‖∑ n ∈ S, a n • haarLp 𝕜 2 n‖ ^ 2 =
      ∑ n ∈ S, ‖a n • haarLp 𝕜 2 n‖ ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have ho : inner 𝕜 (a i • haarLp 𝕜 2 i) (∑ j ∈ S, a j • haarLp 𝕜 2 j) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [inner_smul_left, inner_smul_right,
        haarLp_inner_eq_zero 𝕜 (i := i) (j := j) (fun h => hi (h.symm ▸ hj)), mul_zero, mul_zero]
    rw [Finset.sum_insert hi, Finset.sum_insert hi, norm_add_sq (𝕜 := 𝕜), ho]
    simpa only [map_zero, mul_zero, add_zero] using congrArg (‖a i • haarLp 𝕜 2 i‖ ^ 2 + ·) ih

/-- Uniform contraction for arbitrary finite unit-disk multipliers at p=2.
The comparison is with a containing initial projection, whose contraction
was proved upstream by conditional expectation. -/
theorem l2_contraction : Spec.L2Contraction.{u} := by
  intro 𝕜 _ S m hm f
  classical
  let N := S.sup id + 1
  have hSN : S ⊆ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hsq : ‖finiteTransform S m f‖ ^ 2 ≤ ‖haarPartialSum N f‖ ^ 2 := by
    change ‖∑ n ∈ S, (m n * haarCoefficient f n) • haarLp 𝕜 2 n‖ ^ 2 ≤ _
    rw [haarSynthesis_norm_sq]
    change _ ≤ ‖∑ n ∈ Finset.range N, haarCoefficient f n • haarLp 𝕜 2 n‖ ^ 2
    rw [haarSynthesis_norm_sq]
    apply le_trans (Finset.sum_le_sum fun i hi => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hSN fun i _ _ => sq_nonneg _)
    have hnorm : ‖(m i * haarCoefficient f i) • haarLp 𝕜 2 i‖ ≤
        ‖haarCoefficient f i • haarLp 𝕜 2 i‖ := by
      rw [mul_smul, norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hm i hi)
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hc := HaarBasis.haar_contractions 𝕜 2 (by simp) N f
  nlinarith [norm_nonneg (finiteTransform S m f), norm_nonneg (haarPartialSum N f),
    norm_nonneg f]

theorem finiteTransformCLM_l2_norm_le_one (𝕜 : Type u) [RCLike 𝕜]
    (S : Finset ℕ) (m : ℕ → 𝕜) (hm : ∀ n ∈ S, ‖m n‖ ≤ 1) :
    ‖finiteTransformCLM 𝕜 2 S m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [finiteTransformCLM_apply, one_mul] using l2_contraction 𝕜 S m hm f

/-- Exponents greater than two reduce entirely to the lower interior range.
The scalar universe here matches the accepted duality interface and includes
both manuscript scalar fields, ℝ and ℂ. No lower-range bound is asserted. -/
theorem interior_bounds_of_lower_range {𝕜 : Type} [RCLike 𝕜]
    (hb : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q < 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (m : ℕ → 𝕜),
        (∀ n ∈ S, ‖m n‖ ≤ 1) → ∀ g : Lp 𝕜 q (volume : Measure I),
          ‖finiteTransform S m g‖ ≤ C * ‖g‖)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (m : ℕ → 𝕜),
      (∀ n ∈ S, ‖m n‖ ≤ 1) → ∀ f : Lp 𝕜 p (volume : Measure I),
        ‖finiteTransform S m f‖ ≤ C * ‖f‖ := by
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · exact hb p hp hp2
  · exact ⟨1, zero_lt_one, fun S m hm f => by simpa using l2_contraction 𝕜 S m hm f⟩
  · let q := ENNReal.conjExponent p
    have hq1 : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp
      (lt_top_iff_ne_top.mpr hp_top)
    have hq_top : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp.ne'
    have hq2 : q < 2 := by
      have hsub : 1 < p - 1 := ((ENNReal.cancel_of_ne ENNReal.one_ne_top).lt_tsub_iff_right).mpr (by convert hp2 using 1 <;> norm_num)
      calc
        q = 1 + (p - 1)⁻¹ := rfl
        _ < 1 + 1 := ENNReal.add_lt_add_left ENNReal.one_ne_top (ENNReal.inv_lt_one.mpr hsub)
        _ = 2 := by norm_num
    have : Fact (1 ≤ q) := ⟨hq1.le⟩
    obtain ⟨C, hC, hc⟩ := hb q hq1 hq2
    exact ⟨C, hC, uniform_bounds_of_conjugate hq_top hC.le hc⟩

/-- The actual squared L2 norm is the integral of the pointwise norm
squared; the inner product here is the underlying real inner product. -/
theorem l2_integral_norm_sq {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 2 (volume : Measure I)) :
    (∫ x : I, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  calc
    _ = inner ℝ f f := by simp only [L2.inner_def, real_inner_self_eq_norm_sq]
    _ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f

/-- Chebyshev with the native ENNReal-valued measure, for every L2 input. -/
theorem l2_measure_gt_le {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 2 (volume : Measure I)) (t : ℝ) (ht : 0 < t) :
    volume {x : I | t < ‖f x‖} ≤ ENNReal.ofReal (‖f‖ ^ 2 / t ^ 2) := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (volume : Measure I)) (ae_of_all _ (fun x => sq_nonneg ‖f x‖))
    (Lp.memLp f).norm.integrable_sq (t ^ 2)
  rw [l2_integral_norm_sq] at hmark
  have hsub : (volume : Measure I).real {x : I | t < ‖f x‖} ≤
      (volume : Measure I).real {x : I | t ^ 2 ≤ ‖f x‖ ^ 2} := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    exact pow_le_pow_left₀ ht.le hx.le 2
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  simpa only [mul_comm, measureReal_def] using
    (mul_le_mul_of_nonneg_left hsub (sq_nonneg t)).trans hmark

/-- Once a good part is constructed, its L2 energy bound and the exceptional
measure give the weak estimate with constant 3. The hypotheses are supplied by
the finite dyadic decomposition below. -/
theorem weak_bound_of_good_part {𝕜 : Type u} [RCLike 𝕜]
    (S : Finset ℕ) (m : ℕ → 𝕜) (hm : ∀ i ∈ S, ‖m i‖ ≤ 1)
    (f : Lp 𝕜 1 (volume : Measure I)) (g : Lp 𝕜 2 (volume : Measure I))
    (B : Set I) (t : ℝ) (ht : 0 < t)
    (hB : volume B ≤ ENNReal.ofReal (‖f‖ / t))
    (hg : ‖g‖ ^ 2 ≤ 2 * t * ‖f‖)
    (heq : ∀ᵐ x ∂volume, x ∉ B → finiteTransform S m f x = finiteTransform S m g x) :
    volume {x : I | t < ‖finiteTransform S m f x‖} ≤
      ENNReal.ofReal (3 * ‖f‖ / t) := by
  have hsub : {x : I | t < ‖finiteTransform S m f x‖} ≤ᵐ[volume]
      B ∪ {x : I | t < ‖finiteTransform S m g x‖} := by
    filter_upwards [heq] with x hx
    intro hxf
    by_cases hxb : x ∈ B
    · exact Or.inl hxb
    · right
      change t < ‖finiteTransform S m g x‖
      rw [← hx hxb]
      exact hxf
  have henergy : ‖finiteTransform S m g‖ ^ 2 ≤ 2 * t * ‖f‖ :=
    (pow_le_pow_left₀ (norm_nonneg _) (l2_contraction 𝕜 S m hm g) 2).trans hg
  calc
    _ ≤ volume (B ∪ {x : I | t < ‖finiteTransform S m g x‖}) := measure_mono_ae hsub
    _ ≤ volume B + volume {x : I | t < ‖finiteTransform S m g x‖} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (‖f‖ / t) +
        ENNReal.ofReal (‖finiteTransform S m g‖ ^ 2 / t ^ 2) :=
      add_le_add hB (l2_measure_gt_le _ t ht)
    _ ≤ ENNReal.ofReal (‖f‖ / t) + ENNReal.ofReal (2 * t * ‖f‖ / t ^ 2) := by
      gcongr
    _ = ENNReal.ofReal (3 * ‖f‖ / t) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp
      <;> ring

/-- Uniform coordinate-deletion bounds imply convergence of the finite-subset
net, by applying the bound to the small natural-order remainder. -/
theorem hasSum_of_uniform_bounds {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ (S : Finset ℕ) (m : ℕ → 𝕜), (∀ n ∈ S, ‖m n‖ ≤ 1) →
      ∀ f : Lp 𝕜 p (volume : Measure I), ‖finiteTransform S m f‖ ≤ C * ‖f‖)
    (f : Lp 𝕜 p (volume : Measure I)) :
    HasSum (fun n => haarCoefficient f n • haarLp 𝕜 p n) f := by
  classical
  have ht : C15UnconditionalCriteria.FiniteTailCondition
      (fun n => haarCoefficient f n • haarLp 𝕜 p n) := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (HaarBasis.haar_convergence 𝕜 p hp f)
      (ε / C) (div_pos hε hC)
    refine ⟨N, fun S hS => ?_⟩
    have heq : finiteTransform S (fun _ => (1 : 𝕜)) (f - haarPartialSum N f) =
        ∑ i ∈ S, haarCoefficient f i • haarLp 𝕜 p i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hni : ¬ i < N := Nat.not_lt.mpr (hS i hi)
      have hc := map_sub (HaarBasis.haarCoefficientCLM 𝕜 p i) f (haarPartialSum N f)
      simp only [HaarBasis.haarCoefficientCLM_apply] at hc
      change haarCoefficient (f - haarPartialSum N f) i =
        haarCoefficient f i - haarCoefficient
          (C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p) (haarCoefficient f) N) i at hc
      rw [HaarBasis.haarCoefficient_partialSum, ite_eq_right hni, sub_zero] at hc
      simp only [one_mul, hc]
    change ‖∑ i ∈ S, haarCoefficient f i • haarLp 𝕜 p i‖ < ε
    rw [← heq]
    apply (hbound S (fun _ => 1) (fun _ _ => by simp) _).trans_lt
    have hrem : ‖f - haarPartialSum N f‖ < ε / C := by
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using hN N le_rfl
    exact (mul_lt_mul_of_pos_left hrem hC).trans_eq (mul_div_cancel₀ ε hC.ne')
  exact (C15UnconditionalCriteria.hasUnconditionalSum_iff_hasOrderedSum_of_finiteTailCondition
    ht f).mpr ((C01Banach.hasSequentialSum_iff _ _ _).mpr
      (HaarBasis.haar_convergence 𝕜 p hp f))

/-- The explicit Fourier coefficients identify every ordered expansion. -/
theorem unconditionalBasis_of_uniform_bounds {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ (S : Finset ℕ) (m : ℕ → 𝕜), (∀ n ∈ S, ‖m n‖ ≤ 1) →
      ∀ f : Lp 𝕜 p (volume : Measure I), ‖finiteTransform S m f‖ ≤ C * ‖f‖) :
    C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜
      (Lp 𝕜 p (volume : Measure I)) (haarLp 𝕜 p) := by
  have hraw : C15Unconditional.HasUniqueOrderedExpansions 𝕜
      (Lp 𝕜 p (volume : Measure I)) (haarLp 𝕜 p) := by
    refine ⟨HaarBasis.haar_nonzero 𝕜 p hp, fun f => ?_⟩
    refine ⟨haarCoefficient f, (C01Banach.hasSequentialSum_iff _ _ _).mpr
      (HaarBasis.haar_convergence 𝕜 p hp f), fun a ha => ?_⟩
    exact HaarBasis.haar_expansion_unique 𝕜 p
      ((C01Banach.hasSequentialSum_iff _ _ _).mp ha)
  refine ⟨hraw, fun f a ha => ?_⟩
  have heq : a = haarCoefficient f := HaarBasis.haar_expansion_unique 𝕜 p
    ((C01Banach.hasSequentialSum_iff _ _ _).mp ha)
  subst a
  exact ⟨f, hasSum_of_uniform_bounds hp hC hbound f⟩

/-- The final assembly, conditional on precisely the remaining analytic bound. -/
theorem bounds_imply_unconditional : Spec.BoundsImplyUnconditional.{u} := by
  intro hb
  constructor
  · intro 𝕜 _ p _ hp hp_top f
    obtain ⟨C, hC, hc⟩ := hb 𝕜 p hp hp_top
    exact hasSum_of_uniform_bounds hp_top hC hc f
  · intro 𝕜 _ p _ hp hp_top
    obtain ⟨C, hC, hc⟩ := hb 𝕜 p hp hp_top
    exact unconditionalBasis_of_uniform_bounds hp_top hC hc

/-- The p=2 case is unconditional without any unproved analytic assumption. -/
theorem haar_unconditional_l2 (𝕜 : Type u) [RCLike 𝕜] :
    C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜
      (Lp 𝕜 2 (volume : Measure I)) (haarLp 𝕜 2) := by
  apply unconditionalBasis_of_uniform_bounds (by simp) (C := 1) zero_lt_one
  intro S m hm f
  simpa only [one_mul] using l2_contraction 𝕜 S m hm f


theorem bounded_l1_l2_energy {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I)) (A : ℝ)
    (hf : ∀ᵐ x ∂volume, ‖f x‖ ≤ A) :
    ∃ g : Lp 𝕜 2 (volume : Measure I), ⇑f =ᵐ[volume] ⇑g ∧
      ‖g‖ ^ 2 ≤ A * ‖f‖ := by
  have hg : MemLp (⇑f) 2 volume := MemLp.of_bound (Lp.aestronglyMeasurable f) A hf
  let g := hg.toLp f
  have heq : ⇑g =ᵐ[volume] ⇑f := MemLp.coeFn_toLp hg
  refine ⟨g, heq.symm, ?_⟩
  have hgsq : (∫ x : I, ‖g x‖ ^ 2) = ‖g‖ ^ 2 := by
    calc
      _ = inner ℝ g g := by simp only [L2.inner_def, real_inner_self_eq_norm_sq]
      _ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [← hgsq, L1.norm_eq_integral_norm, ← integral_const_mul]
  refine integral_mono_ae (Lp.memLp g).norm.integrable_sq
    (((Lp.memLp f).integrable le_rfl).norm.const_mul A) ?_
  filter_upwards [heq, hf] with x hx hfx
  rw [hx, pow_two]
  exact mul_le_mul_of_nonneg_right hfx (norm_nonneg _)


/-- A bound for the means and the untouched region bounds the good part. -/
theorem cellGoodPart_ae_norm_le {𝕜 : Type u} [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I)) (D : Finset (Set I))
    (hDm : ∀ s ∈ D, MeasurableSet s)
    (hD : Set.PairwiseDisjoint (D : Set (Set I)) id) (A : ℝ)
    (hmean : ∀ s ∈ D, ‖cellMean f s‖ ≤ A)
    (hout : ∀ᵐ x ∂volume, x ∉ ⋃ s ∈ D, s → ‖f x‖ ≤ A) :
    ∀ᵐ x ∂volume, ‖cellGoodPart f D hDm x‖ ≤ A := by
  filter_upwards [cellGoodPart_ae f D hDm hD, hout] with x hx hxo
  by_cases hxb : x ∈ ⋃ s ∈ D, s
  · obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hxb
    rw [hx.1 s hs hxs]
    exact hmean s hs
  · rw [hx.2 hxb]
    exact hxo hxb

/-- Mean-zero bad pieces remain supported in their original cells. -/
theorem finiteTransform_cellGoodPart_eq_outside {𝕜 : Type u} [RCLike 𝕜]
    (S : Finset ℕ) (m : ℕ → 𝕜)
    (f : Lp 𝕜 1 (volume : Measure I)) (D : Finset (Set I))
    (hDm : ∀ s ∈ D, MeasurableSet s)
    (hcell : ∀ s ∈ D, ∃ l k : ℕ, s = dyadicCell l k)
    (hpos : ∀ s ∈ D, 0 < (volume : Measure I).real s) :
    ∀ᵐ x ∂volume, x ∉ ⋃ s ∈ D, s →
      finiteTransform S m f x = finiteTransform S m (cellGoodPart f D hDm) x := by
  classical
  have hb (s : D) : ∀ᵐ x ∂volume, x ∉ s.1 →
      finiteTransform S m (cellBadPart f s.1 (hDm s.1 s.2)) x = 0 := by
    obtain ⟨l, k, hsc⟩ := hcell s.1 s.2
    have hsupp : ∀ᵐ x ∂volume, x ∉ dyadicCell l k →
        cellBadPart f s.1 (hDm s.1 s.2) x = 0 := by
      filter_upwards [cellBadPart_ae f s.1 (hDm s.1 s.2)] with x hx hxc
      rw [hx]
      exact Set.indicator_of_notMem (by simpa [hsc] using hxc) _
    have ht := finiteTransform_supported_in_cell S m
      (cellBadPart f s.1 (hDm s.1 s.2)) l k hsupp
      (cellBadPart_mean_zero f s.1 (hDm s.1 s.2) (hpos s.1 s.2))
    simpa only [hsc] using ht
  have hmap : finiteTransform S m (cellGoodPart f D hDm) =
      finiteTransform S m f -
        ∑ s ∈ D.attach, finiteTransform S m (cellBadPart f s.1 (hDm s.1 s.2)) := by
    simp only [cellGoodPart, ← finiteTransformCLM_apply, map_sub, map_sum]
  have hball : ∀ᵐ x ∂volume, ∀ s : D, x ∉ s.1 →
      finiteTransform S m (cellBadPart f s.1 (hDm s.1 s.2)) x = 0 :=
    ae_all_iff.mpr hb
  have hsub := Lp.coeFn_sub (finiteTransform S m f)
    (∑ s ∈ D.attach, finiteTransform S m (cellBadPart f s.1 (hDm s.1 s.2)))
  have hsum := Lp.coeFn_finsetSum D.attach
    (fun s => finiteTransform S m (cellBadPart f s.1 (hDm s.1 s.2)))
  rw [← hmap] at hsub
  filter_upwards [hball, hsub, hsum] with x hx hxs hxsum hxb
  rw [hxs]
  simp only [Pi.sub_apply]
  rw [hxsum]
  simp only [Finset.sum_apply]
  change _ = _ - ∑ s ∈ D.attach, _
  have hz : (∑ s ∈ D.attach,
      finiteTransform S m (cellBadPart f s.1 (hDm s.1 s.2)) x) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    apply hx s
    intro hxcell
    exact hxb (Set.mem_iUnion₂.mpr ⟨s.1, s.2, hxcell⟩)
  rw [hz, sub_zero]


/-- The dyadic decomposition gives a uniform weak-(1,1) estimate. -/
theorem weak_bound_dyadic_polynomial {𝕜 : Type u} [RCLike 𝕜]
    (M : ℕ) (S : Finset ℕ) (m : ℕ → 𝕜)
    (hm : ∀ i ∈ S, ‖m i‖ ≤ 1)
    (f : Lp 𝕜 1 (volume : Measure I))
    (hfix : haarPartialSum (2 ^ M) f = f)
    (t : ℝ) (ht : 0 < t) :
    volume {x : I | t < ‖finiteTransform S m f x‖} ≤
      ENNReal.ofReal (3 * ‖f‖ / t) := by
  classical
  by_cases hft : ‖f‖ ≤ t
  · obtain ⟨D, hDC, hmax, hD, hcover⟩ :=
      exists_maximal_bad_dyadic_family M f t
    have hdy (s : Set I) (hs : s ∈ D) :
        ∃ l ≤ M, ∃ k < 2 ^ l, s = dyadicCell l k :=
      (mem_dyadicCellsThrough M s).mp
        ((mem_badDyadicCells M f t s).mp (hDC hs)).1
    have hDm (s : Set I) (hs : s ∈ D) : MeasurableSet s := by
      obtain ⟨l, _, k, _, rfl⟩ := hdy s hs
      exact measurableSet_dyadicCell l k
    have hpos (s : Set I) (hs : s ∈ D) : 0 < (volume : Measure I).real s := by
      obtain ⟨l, _, k, hk, rfl⟩ := hdy s hs
      rw [HaarBasis.real_volume_dyadicCell l k hk]
      positivity
    have hmean (s : Set I) (hs : s ∈ D) : ‖cellMean f s‖ ≤ 2 * t := by
      obtain ⟨l, hl, k, hk, rfl⟩ := hdy s hs
      exact maximal_bad_cell_mean_le M f t hft l k hl hk (hmax _ hs)
    have hout : ∀ᵐ x ∂volume, x ∉ ⋃ s ∈ D, s → ‖f x‖ ≤ 2 * t := by
      filter_upwards [dyadic_polynomial_bound_outside_bad M f hfix t D hcover]
        with x hx hxb
      exact (hx hxb).trans (by linarith)
    have hgBound := cellGoodPart_ae_norm_le f D hDm hD (2 * t) hmean hout
    obtain ⟨g, hfg, henergy⟩ := bounded_l1_l2_energy (cellGoodPart f D hDm) (2 * t) hgBound
    have henergy' : ‖g‖ ^ 2 ≤ 2 * t * ‖f‖ :=
      henergy.trans (mul_le_mul_of_nonneg_left
        (cellGoodPart_norm_le f D hDm hD hpos) (by positivity))
    have hB : volume (⋃ s ∈ D, s) ≤ ENNReal.ofReal (‖f‖ / t) := by
      apply bad_union_measure_le f D hD hDm t ht
      intro s hs
      exact ((mem_badDyadicCells M f t s).mp (hDC hs)).2.le
    have heq : ∀ᵐ x ∂volume, x ∉ ⋃ s ∈ D, s →
        finiteTransform S m f x = finiteTransform S m g x := by
      have hcell (s : Set I) (hs : s ∈ D) : ∃ l k : ℕ, s = dyadicCell l k := by
        obtain ⟨l, _, k, _, h⟩ := hdy s hs
        exact ⟨l, k, h⟩
      filter_upwards [finiteTransform_cellGoodPart_eq_outside S m f D hDm hcell hpos,
        finiteTransform_compatible S m (cellGoodPart f D hDm) g hfg] with x hx hxg hxb
      exact (hx hxb).trans hxg
    exact weak_bound_of_good_part S m hm f g (⋃ s ∈ D, s) t ht hB henergy' heq
  · calc
      _ ≤ volume (Set.univ : Set I) := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (3 * ‖f‖ / t) := by
        apply ENNReal.one_le_ofReal.mpr
        apply (le_div_iff₀ ht).mpr
        have htf := lt_of_not_ge hft
        nlinarith [norm_nonneg f]

/-- The weak estimate applies to every L1 input, uniformly in finite subsets
and scalar multipliers in the closed unit disk. -/
theorem uniform_weak_one : Spec.UniformWeakOne.{u} := by
  refine ⟨3, by norm_num, ?_⟩
  intro 𝕜 _ S m hm f t ht
  apply weak_bound_of_dyadic_polynomials (by norm_num : (0 : ℝ) ≤ 3)
    (fun M S m _ hm f hfix t ht =>
      weak_bound_dyadic_polynomial M S m hm f hfix t ht) S m hm f t ht


-- This uses no interpolation assumption and is valid for every p≥1.
theorem truncation_decomposition {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp 𝕜 p (volume : Measure I))
    (t : ℝ) (ht : 0 < t) :
    ∃ (h : Lp 𝕜 1 (volume : Measure I)) (l : Lp 𝕜 2 (volume : Measure I)),
      (∀ᵐ x ∂volume, f x = h x + l x) ∧
      ‖h‖ = ∫ x in {x : I | t < ‖f x‖}, ‖f x‖ ∧
      (∫ x : I, ‖l x‖ ^ 2) = ∫ x in {x : I | ‖f x‖ ≤ t}, ‖f x‖ ^ 2 := by
  classical
  let s : Set I := {x | t < ‖f x‖}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (Lp.stronglyMeasurable f).measurable.norm
  have hhigh : Integrable (s.indicator f) volume :=
    (Lp.memLp f).integrable (Fact.out : 1 ≤ p) |>.indicator hs
  have hlow : MemLp (sᶜ.indicator f) 2 volume := by
    apply MemLp.of_bound ((Lp.aestronglyMeasurable f).indicator hs.compl) t
    filter_upwards [] with x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_notMem, show x ∉ sᶜ by simpa]
      exact ht.le
    · simpa [Set.indicator_of_mem, show x ∈ sᶜ by simpa] using (not_lt.mp hx)
  have hhighLp := memLp_one_iff_integrable.mpr hhigh
  let h : Lp 𝕜 1 (volume : Measure I) := hhighLp.toLp _
  let l : Lp 𝕜 2 (volume : Measure I) := hlow.toLp _
  refine ⟨h, l, ?_, ?_, ?_⟩
  · filter_upwards [hhighLp.coeFn_toLp, hlow.coeFn_toLp] with x hh hl
    change f x = hhighLp.toLp _ x + hlow.toLp _ x
    rw [hh, hl]
    by_cases hx : x ∈ s <;> simp [hx]
  · rw [L1.norm_eq_integral_norm]
    calc
      (∫ x : I, ‖h x‖) = ∫ x : I, s.indicator (fun x => ‖f x‖) x := by
        apply integral_congr_ae
        filter_upwards [hhighLp.coeFn_toLp] with x hx
        change ‖hhighLp.toLp _ x‖ = _
        rw [hx]
        by_cases hx : x ∈ s <;> simp [hx]
      _ = _ := integral_indicator hs
  · calc
      (∫ x : I, ‖l x‖ ^ 2) = ∫ x : I, sᶜ.indicator (fun x => ‖f x‖ ^ 2) x := by
        apply integral_congr_ae
        filter_upwards [hlow.coeFn_toLp] with x hx
        change ‖hlow.toLp _ x‖ ^ 2 = _
        rw [hx]
        by_cases hx : x ∈ sᶜ <;> simp [hx]
      _ = ∫ x in sᶜ, ‖f x‖ ^ 2 := integral_indicator hs.compl
      _ = _ := by
        have hscompl : sᶜ = {x : I | ‖f x‖ ≤ t} := by ext x; simp [s]
        rw [hscompl]

-- A cross-exponent additive compatibility lemma, extending the saved equality lemma.
theorem finiteTransform_add_ae {𝕜 : Type u} [RCLike 𝕜]
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (S : Finset ℕ) (m : ℕ → 𝕜) (f : Lp 𝕜 p (volume : Measure I))
    (h : Lp 𝕜 q (volume : Measure I)) (l : Lp 𝕜 r (volume : Measure I))
    (hfl : ∀ᵐ x ∂volume, f x = h x + l x) :
    ∀ᵐ x ∂volume, finiteTransform S m f x =
      finiteTransform S m h x + finiteTransform S m l x := by
  classical
  have hcoef (i : ℕ) : haarCoefficient f i = haarCoefficient h i + haarCoefficient l i := by
    rw [haarCoefficient, haarCoefficient, haarCoefficient, ← mul_add]
    congr 1
    rw [← integral_add (ExpandedFA.P1.HaarBasis.haarProduct_integrable h i) (ExpandedFA.P1.HaarBasis.haarProduct_integrable l i)]
    apply integral_congr_ae
    filter_upwards [hfl] with x hx
    simp only [hx, add_mul]
  filter_upwards [finiteTransform_ae S m f, finiteTransform_ae S m h,
    finiteTransform_ae S m l] with x hf hh hl
  rw [hf, hh, hl, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoef]
  ring

-- Tail estimate suited directly for scalar Tonelli integration.
theorem finiteTransform_two_tail {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : Finset ℕ) (m : ℕ → 𝕜) (hm : ∀ n ∈ S, ‖m n‖ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hweak : ∀ (h : Lp 𝕜 1 (volume : Measure I)) (a : ℝ), 0 < a →
      volume {x : I | a < ‖finiteTransform S m h x‖} ≤ ENNReal.ofReal (C * ‖h‖ / a))
    (f : Lp 𝕜 p (volume : Measure I)) (t : ℝ) (ht : 0 < t) :
    volume {x : I | t < ‖finiteTransform S m f x‖} ≤
      ENNReal.ofReal (2 * C / t) *
        (∫⁻ x in {x : I | t < ‖f x‖}, ENNReal.ofReal ‖f x‖) +
      ENNReal.ofReal (4 / t ^ 2) *
        (∫⁻ x in {x : I | ‖f x‖ ≤ t}, ENNReal.ofReal (‖f x‖ ^ 2)) := by
  obtain ⟨h, l, hfl, hnorm, lnorm⟩ := truncation_decomposition f t ht
  have hTl := finiteTransform_add_ae S m f h l hfl
  have hsub : {x : I | t < ‖finiteTransform S m f x‖} ≤ᵐ[volume]
      {x : I | t / 2 < ‖finiteTransform S m h x‖} ∪
      {x : I | t / 2 < ‖finiteTransform S m l x‖} := by
    filter_upwards [hTl] with x hx
    intro hxf
    by_cases hxhigh : t / 2 < ‖finiteTransform S m h x‖
    · exact Or.inl hxhigh
    · right
      have hh := norm_add_le (finiteTransform S m h x) (finiteTransform S m l x)
      rw [hx] at hxf
      have hxh : ‖finiteTransform S m h x‖ ≤ t / 2 := le_of_not_gt hxhigh
      change t / 2 < ‖finiteTransform S m l x‖
      linarith
  have hhighInt : IntegrableOn (fun x : I => ‖f x‖) {x : I | t < ‖f x‖} volume :=
    ((Lp.memLp f).integrable (Fact.out : 1 ≤ p)).norm.integrableOn
  have hlowInt : IntegrableOn (fun x : I => ‖f x‖ ^ 2) {x : I | ‖f x‖ ≤ t} volume := by
    refine (integrable_const (t ^ 2)).mono' ?_ ?_
    · exact (((Lp.stronglyMeasurable f).norm.pow 2).aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem (measurableSet_le (Lp.stronglyMeasurable f).measurable.norm measurable_const)] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f x‖)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hhighnorm : ENNReal.ofReal ‖h‖ =
      ∫⁻ x in {x : I | t < ‖f x‖}, ENNReal.ofReal ‖f x‖ := by
    rw [hnorm]
    exact ofReal_integral_eq_lintegral_ofReal hhighInt (ae_of_all _ (fun _ => norm_nonneg _))
  have hlownorm : ENNReal.ofReal (‖l‖ ^ 2) =
      ∫⁻ x in {x : I | ‖f x‖ ≤ t}, ENNReal.ofReal (‖f x‖ ^ 2) := by
    rw [← l2_integral_norm_sq, lnorm]
    exact ofReal_integral_eq_lintegral_ofReal hlowInt (ae_of_all _ (fun _ => sq_nonneg _))
  have hhighfactor : ENNReal.ofReal (C * ‖h‖ / (t / 2)) =
      ENNReal.ofReal (2 * C / t) * ENNReal.ofReal ‖h‖ := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hlowfactor : ENNReal.ofReal (‖l‖ ^ 2 / (t / 2) ^ 2) =
      ENNReal.ofReal (4 / t ^ 2) * ENNReal.ofReal (‖l‖ ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  calc
    _ ≤ volume ({x : I | t / 2 < ‖finiteTransform S m h x‖} ∪
        {x : I | t / 2 < ‖finiteTransform S m l x‖}) := measure_mono_ae hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * ‖h‖ / (t / 2)) +
        ENNReal.ofReal (‖l‖ ^ 2 / (t / 2) ^ 2) :=
      add_le_add (hweak h (t / 2) (half_pos ht))
        (l2_measure_gt_le (finiteTransform S m l) (t / 2) (half_pos ht) |>.trans <|
          ENNReal.ofReal_le_ofReal <| div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (l2_contraction 𝕜 S m hm l) 2) (sq_nonneg _))
    _ = _ := by rw [hhighfactor, hlowfactor, hhighnorm, hlownorm]

/-- The canonical isometric field embedding of any RCLike field into ℂ. -/
def scalarToComplex (𝕜 : Type u) [RCLike 𝕜] : 𝕜 →+* ℂ where
  toFun := RCLike.map 𝕜 ℂ
  map_zero' := by simp
  map_one' := by simp
  map_add' := map_add (RCLike.map 𝕜 ℂ)
  map_mul' x y := by
    apply Complex.ext <;> simp [RCLike.map_apply, RCLike.mul_re, RCLike.mul_im]

@[simp] theorem scalarToComplex_eq_map (𝕜 : Type u) [RCLike 𝕜] (z : 𝕜) :
    scalarToComplex 𝕜 z = RCLike.map 𝕜 ℂ z := rfl

@[simp] theorem scalarToComplex_norm (𝕜 : Type u) [RCLike 𝕜] (z : 𝕜) :
    ‖scalarToComplex 𝕜 z‖ = ‖z‖ := RCLike.norm_to_complex z

abbrev complexifyLp {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp 𝕜 p (volume : Measure I)) : Lp ℂ p (volume : Measure I) :=
  (RCLike.map 𝕜 ℂ).compLp f

@[simp] theorem complexifyLp_norm {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp 𝕜 p (volume : Measure I)) :
    ‖complexifyLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [(RCLike.map 𝕜 ℂ).coeFn_compLp f] with x hx
  rw [hx]
  exact RCLike.norm_to_complex _

@[simp] theorem scalarToComplex_haarFunction (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (x : I) :
    scalarToComplex 𝕜 (haarFunction 𝕜 n x) = haarFunction ℂ n x := by
  by_cases hn : n = 0
  · simp [haarFunction, hn]
  · by_cases hl : x ∈ leftCell n <;> by_cases hr : x ∈ rightCell n <;>
      simp [haarFunction, hn, Set.indicator, hl, hr]

@[simp] theorem scalarToComplex_haarCoefficient {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp 𝕜 p (volume : Measure I)) (n : ℕ) :
    scalarToComplex 𝕜 (haarCoefficient f n) = haarCoefficient (complexifyLp f) n := by
  unfold haarCoefficient
  rw [map_mul]
  congr 1
  · split_ifs <;> simp only [map_one, map_pow, map_ofNat]
  · change RCLike.map 𝕜 ℂ (∫ x : I, f x * haarFunction 𝕜 n x) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ (HaarBasis.haarProduct_integrable f n)]
    apply integral_congr_ae
    filter_upwards [(RCLike.map 𝕜 ℂ).coeFn_compLp f] with x hx
    rw [hx]
    change scalarToComplex 𝕜 (f x * haarFunction 𝕜 n x) = _
    rw [map_mul, scalarToComplex_haarFunction]
    rfl

@[simp] theorem complexifyLp_finiteTransform {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : Finset ℕ) (m : ℕ → 𝕜)
    (f : Lp 𝕜 p (volume : Measure I)) :
    complexifyLp (finiteTransform S m f) =
      finiteTransform S (fun n => scalarToComplex 𝕜 (m n)) (complexifyLp f) := by
  apply Lp.ext
  filter_upwards [(RCLike.map 𝕜 ℂ).coeFn_compLp (finiteTransform S m f),
    finiteTransform_ae S m f,
    finiteTransform_ae S (fun n => scalarToComplex 𝕜 (m n)) (complexifyLp f)] with x hx hf hg
  rw [hx, hf, hg]
  change scalarToComplex 𝕜 (∑ i ∈ S, (m i * haarCoefficient f i) * haarFunction 𝕜 i x) = _
  simp only [map_sum, map_mul, scalarToComplex_haarCoefficient, scalarToComplex_haarFunction]

/-- A bound over ℂ transfers unchanged to every RCLike field, at every universe. -/
theorem uniform_bound_of_complex_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] {C : ℝ}
    (hb : ∀ (S : Finset ℕ) (m : ℕ → ℂ), (∀ n ∈ S, ‖m n‖ ≤ 1) →
      ∀ f : Lp ℂ p (volume : Measure I), ‖finiteTransform S m f‖ ≤ C * ‖f‖)
    (𝕜 : Type u) [RCLike 𝕜] (S : Finset ℕ) (m : ℕ → 𝕜)
    (hm : ∀ n ∈ S, ‖m n‖ ≤ 1) (f : Lp 𝕜 p (volume : Measure I)) :
    ‖finiteTransform S m f‖ ≤ C * ‖f‖ := by
  have hc := hb S (fun n => scalarToComplex 𝕜 (m n))
    (fun n hn => by simpa using hm n hn) (complexifyLp f)
  rw [← complexifyLp_finiteTransform, complexifyLp_norm, complexifyLp_norm] at hc
  exact hc

/-- The manuscript lower range over ℂ suffices for the complete scalar-polymorphic conclusion. -/
theorem uniformLpBounds_of_complex_lower_range
    (hb : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q < 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (m : ℕ → ℂ),
        (∀ n ∈ S, ‖m n‖ ≤ 1) → ∀ g : Lp ℂ q (volume : Measure I),
          ‖finiteTransform S m g‖ ≤ C * ‖g‖) :
    Spec.UniformLpBounds.{u} := by
  intro 𝕜 _ p _ hp hp_top
  obtain ⟨C, hC, hc⟩ := interior_bounds_of_lower_range hb p hp hp_top
  exact ⟨C, hC, uniform_bound_of_complex_bound hc 𝕜⟩


open Set

lemma power_high_kernel_integral {r a : ℝ} (hr : 1 < r) (ha : 0 ≤ a) :
    ∫⁻ t in Ioi (0 : ℝ), (if t < a then ENNReal.ofReal a * ENNReal.ofReal (t ^ (r-2)) else 0) =
      ENNReal.ofReal (a ^ r / (r-1)) := by
  by_cases ha0 : a = 0
  · subst a
    simp [Real.zero_rpow (show r ≠ 0 by linarith)]
  have hap : 0 < a := ha.lt_of_ne' ha0
  have hi : IntegrableOn (fun t : ℝ => t ^ (r - 2)) (Ioc 0 a) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r-2)).1
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 a)] fun t : ℝ => t ^ (r-2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), (Iio a).indicator
        (fun t => ENNReal.ofReal a * ENNReal.ofReal (t ^ (r-2))) t := by rfl
    _ = ∫⁻ t in Ioo (0 : ℝ) a,
        ENNReal.ofReal a * ENNReal.ofReal (t ^ (r-2)) := by
      rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      rw [show Iio a ∩ Ioi 0 = Ioo 0 a by ext x; simp [and_comm]]
    _ = ∫⁻ t in Ioc (0 : ℝ) a,
        ENNReal.ofReal a * ENNReal.ofReal (t ^ (r-2)) := by
      apply setLIntegral_congr
      exact Ioo_ae_eq_Ioc
    _ = ENNReal.ofReal a * ENNReal.ofReal (∫ t in Ioc (0 : ℝ) a, t ^ (r-2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal hi hn]
    _ = _ := by
      rw [← intervalIntegral.integral_of_le ha,
        integral_rpow (Or.inl (show -1 < r-2 by linarith))]
      have hpow : a * a ^ (r-2+1) = a ^ r := by
        calc
          _ = a ^ (1 : ℝ) * a ^ (r-2+1) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hap]; congr 1; ring
      rw [Real.zero_rpow (show r-2+1 ≠ 0 by linarith), sub_zero,
        ← ENNReal.ofReal_mul ha, ← mul_div_assoc, hpow]
      congr 2
      ring

lemma power_low_kernel_integral {r a : ℝ} (hr : r < 2) (ha : 0 ≤ a) (hr0 : 0 < r) :
    ∫⁻ t in Ioi (0 : ℝ), (if a ≤ t then ENNReal.ofReal (a^2) * ENNReal.ofReal (t ^ (r-3)) else 0) =
      ENNReal.ofReal (a ^ r / (2-r)) := by
  by_cases ha0 : a = 0
  · subst a
    simp [Real.zero_rpow hr0.ne']
  have hap : 0 < a := ha.lt_of_ne' ha0
  have hi := integrableOn_Ioi_rpow_of_lt (show r-3 < -1 by linarith) hap
  have hn : 0 ≤ᵐ[volume.restrict (Ioi a)] fun t : ℝ => t ^ (r-3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hap.trans ht).le _
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), (Ici a).indicator
        (fun t => ENNReal.ofReal (a^2) * ENNReal.ofReal (t ^ (r-3))) t := by rfl
    _ = ∫⁻ t in Ici a,
        ENNReal.ofReal (a^2) * ENNReal.ofReal (t ^ (r-3)) := by
      rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
        inter_eq_left.mpr (show Ici a ⊆ Ioi 0 from fun _ h => hap.trans_le h)]
    _ = ∫⁻ t in Ioi a,
        ENNReal.ofReal (a^2) * ENNReal.ofReal (t ^ (r-3)) := by
      apply setLIntegral_congr
      exact Ioi_ae_eq_Ici.symm
    _ = ENNReal.ofReal (a^2) * ENNReal.ofReal (∫ t in Ioi a, t ^ (r-3)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal hi hn]
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (show r-3 < -1 by linarith) hap,
        ← ENNReal.ofReal_mul (sq_nonneg a)]
      congr 1
      have hpow : a^2 * a ^ (r-3+1) = a ^ r := by
        rw [← Real.rpow_natCast a 2, ← Real.rpow_add hap]
        congr 1
        ring
      rw [← mul_div_assoc, mul_neg, hpow]
      rw [neg_div, ← div_neg]
      congr 1
      ring

lemma power_high_tail_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (f : α → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 1 < r) :
    (∫⁻ t in Ioi (0 : ℝ), (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) *
        ENNReal.ofReal (t ^ (r-2))) =
      ENNReal.ofReal (1/(r-1)) * ∫⁻ x, ENNReal.ofReal (f x ^ r) ∂μ := by
  let H : ℝ → α → ℝ≥0∞ := fun t x =>
    if t < f x then ENNReal.ofReal (f x) * ENNReal.ofReal (t ^ (r-2)) else 0
  have hH : Measurable (Function.uncurry H) := by
    apply Measurable.ite (measurableSet_lt measurable_fst (hf.comp measurable_snd))
    · exact ((hf.comp measurable_snd).ennreal_ofReal).mul
        ((measurable_fst.pow_const _).ennreal_ofReal)
    · exact measurable_const
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, H t x ∂μ := by
      apply lintegral_congr
      intro t
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_indicator (measurableSet_lt measurable_const hf)]
      apply lintegral_congr
      intro x
      by_cases hx : t < f x <;> simp [H, hx]
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), H t x) ∂μ :=
      lintegral_lintegral_swap hH.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal (f x ^ r / (r-1)) ∂μ := by
      congr 1
      funext x
      exact power_high_kernel_integral hr (hn x)
    _ = _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

lemma power_low_tail_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (f : α → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) {r : ℝ}
    (hr : r < 2) (hr0 : 0 < r) :
    (∫⁻ t in Ioi (0 : ℝ), (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x ^ 2) ∂μ) *
        ENNReal.ofReal (t ^ (r-3))) =
      ENNReal.ofReal (1/(2-r)) * ∫⁻ x, ENNReal.ofReal (f x ^ r) ∂μ := by
  let H : ℝ → α → ℝ≥0∞ := fun t x =>
    if f x ≤ t then ENNReal.ofReal (f x ^ 2) * ENNReal.ofReal (t ^ (r-3)) else 0
  have hH : Measurable (Function.uncurry H) := by
    apply Measurable.ite (measurableSet_le (hf.comp measurable_snd) measurable_fst)
    · exact (((hf.comp measurable_snd).pow_const 2).ennreal_ofReal).mul
        ((measurable_fst.pow_const _).ennreal_ofReal)
    · exact measurable_const
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, H t x ∂μ := by
      apply lintegral_congr
      intro t
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_indicator (measurableSet_le hf measurable_const)]
      apply lintegral_congr
      intro x
      by_cases hx : f x ≤ t <;> simp [H, hx]
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), H t x) ∂μ :=
      lintegral_lintegral_swap hH.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal (f x ^ r / (2-r)) ∂μ := by
      congr 1
      funext x
      exact power_low_kernel_integral hr (hn x) hr0
    _ = _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- The integrated distribution-function power is exactly the power of the native Lp norm. -/
theorem lintegral_norm_rpow_eq_norm_rpow {α : Type v} [MeasurableSpace α]
    {E : Type u} [NormedAddCommGroup E] {μ : Measure α}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (f : Lp E p μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.toReal) ∂μ) =
      ENNReal.ofReal (‖f‖ ^ p.toReal) := by
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
    ofReal_norm]
  rw [Lp.enorm_def,
    eLpNorm_eq_eLpNorm' hp0 hptop (Lp.aestronglyMeasurable f)]
  exact lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hptop)

/-- Taking the p-th root of the integrated power bound gives an actual Lp estimate. -/
theorem lp_norm_le_of_lintegral_norm_rpow_le {α : Type v} [MeasurableSpace α]
    {E : Type u} [NormedAddCommGroup E] {μ : Measure α}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (f g : Lp E p μ) {K : ℝ} (hK : 0 ≤ K)
    (h : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p.toReal) ∂μ) ≤
      ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.toReal) ∂μ) :
    ‖g‖ ≤ K ^ (1 / p.toReal) * ‖f‖ := by
  rw [lintegral_norm_rpow_eq_norm_rpow hp0 hptop,
    lintegral_norm_rpow_eq_norm_rpow hp0 hptop,
    ← ENNReal.ofReal_mul hK] at h
  have hr : ‖g‖ ^ p.toReal ≤ K * ‖f‖ ^ p.toReal :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hr' := Real.rpow_le_rpow (z := p.toReal⁻¹) (Real.rpow_nonneg (norm_nonneg g) _)
    hr (inv_nonneg.mpr ENNReal.toReal_nonneg)
  simpa only [one_div, Real.mul_rpow hK (Real.rpow_nonneg (norm_nonneg f) _),
    Real.rpow_rpow_inv (norm_nonneg _) (ENNReal.toReal_pos hp0 hptop).ne'] using hr'

/-- A uniform integrated power estimate supplies a positive uniform transform bound. -/
theorem uniform_lp_bound_of_power_integral_bound {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ∞)
    {K : ℝ} (hK : 0 < K)
    (hb : ∀ (S : Finset ℕ) (m : ℕ → 𝕜), (∀ n ∈ S, ‖m n‖ ≤ 1) →
      ∀ f : Lp 𝕜 p (volume : Measure I),
        (∫⁻ x, ENNReal.ofReal (‖finiteTransform S m f x‖ ^ p.toReal)) ≤
          ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.toReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (m : ℕ → 𝕜),
      (∀ n ∈ S, ‖m n‖ ≤ 1) → ∀ f : Lp 𝕜 p (volume : Measure I),
        ‖finiteTransform S m f‖ ≤ C * ‖f‖ := by
  refine ⟨K ^ (1 / p.toReal), Real.rpow_pos_of_pos hK _, ?_⟩
  intro S m hm f
  exact lp_norm_le_of_lintegral_norm_rpow_le
    (ne_of_gt (lt_trans zero_lt_one hp)) hptop f (finiteTransform S m f) hK.le
    (hb S m hm f)


theorem measurable_high_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun t : ℝ => ∫⁻ x in {x : α | t < f x}, ENNReal.ofReal (f x) ∂μ) := by
  let k : ℝ × α → ℝ≥0∞ :=
    {z : ℝ × α | z.1 < f z.2}.indicator (fun z => ENNReal.ofReal (f z.2))
  have hk : Measurable k :=
    ((hf.comp measurable_snd).ennreal_ofReal).indicator
      (measurableSet_lt measurable_fst (hf.comp measurable_snd))
  have hm : Measurable (fun t : ℝ => ∫⁻ x, k (t, x) ∂μ) := hk.lintegral_prod_right'
  convert hm using 1
  funext t
  symm
  change (∫⁻ x, {x : α | t < f x}.indicator (fun x => ENNReal.ofReal (f x)) x ∂μ) = _
  exact lintegral_indicator (measurableSet_lt measurable_const hf) _

theorem measurable_low_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun t : ℝ => ∫⁻ x in {x : α | f x ≤ t}, ENNReal.ofReal (f x ^ 2) ∂μ) := by
  let k : ℝ × α → ℝ≥0∞ :=
    {z : ℝ × α | f z.2 ≤ z.1}.indicator (fun z => ENNReal.ofReal (f z.2 ^ 2))
  have hk : Measurable k :=
    (((hf.comp measurable_snd).pow_const 2).ennreal_ofReal).indicator
      (measurableSet_le (hf.comp measurable_snd) measurable_fst)
  have hm : Measurable (fun t : ℝ => ∫⁻ x, k (t, x) ∂μ) := hk.lintegral_prod_right'
  convert hm using 1
  funext t
  symm
  change (∫⁻ x, {x : α | f x ≤ t}.indicator (fun x => ENNReal.ofReal (f x ^ 2)) x ∂μ) = _
  exact lintegral_indicator (measurableSet_le hf measurable_const) _

lemma two_tail_power_integral {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp2 : p < 2)
    (S : Finset ℕ) (m : ℕ → 𝕜) (hm : ∀ i ∈ S, ‖m i‖ ≤ 1)
    (f : Lp 𝕜 p (volume : Measure I)) :
    (∫⁻ x, ENNReal.ofReal (‖finiteTransform S m f x‖ ^ p.toReal)) ≤
      ENNReal.ofReal (p.toReal * (6 / (p.toReal - 1) + 4 / (2 - p.toReal))) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.toReal) := by
  let r := p.toReal
  have hptop : p ≠ ∞ := ne_top_of_lt hp2
  have hr1 : 1 < r := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal (by simp) hptop).mpr hp
  have hr2 : r < 2 := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal hptop (by simp)).mpr hp2
  let H : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in {x : I | t < ‖f x‖}, ENNReal.ofReal ‖f x‖
  let L : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in {x : I | ‖f x‖ ≤ t}, ENNReal.ofReal (‖f x‖^2)
  have hH : Measurable H := measurable_high_tail volume (Lp.stronglyMeasurable f).measurable.norm
  have hcoef1 (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (6/t) * H t * ENNReal.ofReal (t^(r-1)) =
        ENNReal.ofReal 6 * (H t * ENNReal.ofReal (t^(r-2))) := by
    have hreal : (6/t) * t^(r-1) = 6 * t^(r-2) := by
      calc
        _ = 6 * (t^(r-1) / t) := by ring
        _ = 6 * t^((r-1)-1) := by rw [Real.rpow_sub ht (r-1) 1, Real.rpow_one]
        _ = _ := by congr 2; ring
    calc
      _ = H t * (ENNReal.ofReal (6/t) * ENNReal.ofReal (t^(r-1))) := by ring
      _ = H t * ENNReal.ofReal (6 * t^(r-2)) := by rw [← ENNReal.ofReal_mul (by positivity), hreal]
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; ring
  have hcoef2 (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (4/t^2) * L t * ENNReal.ofReal (t^(r-1)) =
        ENNReal.ofReal 4 * (L t * ENNReal.ofReal (t^(r-3))) := by
    have hreal : (4/t^2) * t^(r-1) = 4 * t^(r-3) := by
      calc
        _ = 4 * (t^(r-1) / t^2) := by ring
        _ = 4 * t^((r-1)-2) := by rw [Real.rpow_sub ht (r-1) 2, Real.rpow_two]
        _ = _ := by congr 2; ring
    calc
      _ = L t * (ENNReal.ofReal (4/t^2) * ENNReal.ofReal (t^(r-1))) := by ring
      _ = L t * ENNReal.ofReal (4 * t^(r-3)) := by rw [← ENNReal.ofReal_mul (by positivity), hreal]
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; ring
  have htail : ∀ t > 0,
      volume {x : I | t < ‖finiteTransform S m f x‖} * ENNReal.ofReal (t^(r-1)) ≤
        ENNReal.ofReal 6 * (H t * ENNReal.ofReal (t^(r-2))) +
        ENNReal.ofReal 4 * (L t * ENNReal.ofReal (t^(r-3))) := by
    intro t ht
    -- use the established constant 3 directly, avoiding existential constant normalization
    have hb := finiteTransform_two_tail S m hm 3 (by norm_num)
      (fun h a ha => weak_bound_of_dyadic_polynomials (by norm_num : (0:ℝ) ≤ 3)
        (fun M S m _ hm f hfix t ht => weak_bound_dyadic_polynomial M S m hm f hfix t ht)
        S m hm h a ha) f t ht
    have hmul := mul_le_mul_of_nonneg_right hb
      (show 0 ≤ ENNReal.ofReal (t^(r-1)) from bot_le)
    norm_num only [show (2:ℝ) * 3 = 6 by norm_num] at hmul
    change _ ≤ (ENNReal.ofReal (6/t) * H t + ENNReal.ofReal (4/t^2) * L t) *
      ENNReal.ofReal (t^(r-1)) at hmul
    simpa only [add_mul, hcoef1 t ht, hcoef2 t ht] using hmul
  have hAH : Measurable (fun t : ℝ => ENNReal.ofReal 6 * (H t * ENNReal.ofReal (t^(r-2)))) :=
    measurable_const.mul (hH.mul (measurable_id.pow_const _).ennreal_ofReal)
  have hi : (∫⁻ t in Ioi (0 : ℝ),
      volume {x : I | t < ‖finiteTransform S m f x‖} * ENNReal.ofReal (t^(r-1))) ≤
      (ENNReal.ofReal 6 * ENNReal.ofReal (1/(r-1)) +
       ENNReal.ofReal 4 * ENNReal.ofReal (1/(2-r))) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ r) := by
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal 6 * (H t * ENNReal.ofReal (t^(r-2))) +
          ENNReal.ofReal 4 * (L t * ENNReal.ofReal (t^(r-3))) := by
        apply setLIntegral_mono' measurableSet_Ioi
        exact fun t ht => htail t ht
      _ = (ENNReal.ofReal 6 * ∫⁻ t in Ioi (0 : ℝ), H t * ENNReal.ofReal (t^(r-2))) +
          (ENNReal.ofReal 4 * ∫⁻ t in Ioi (0 : ℝ), L t * ENNReal.ofReal (t^(r-3))) := by
        rw [lintegral_add_left hAH,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := by
        rw [power_high_tail_integral volume (fun x => ‖f x‖)
          (Lp.stronglyMeasurable f).measurable.norm (fun x => norm_nonneg _) hr1,
          power_low_tail_integral volume (fun x => ‖f x‖)
          (Lp.stronglyMeasurable f).measurable.norm (fun x => norm_nonneg _) hr2 (by linarith)]
        ring
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume
    (ae_of_all _ (fun x => norm_nonneg _)) (Lp.aestronglyMeasurable _).norm.aemeasurable
    (by exact lt_trans zero_lt_one hr1)]
  apply (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by linarith)]
  congr 2
  ring

/-- The strong lower interior bound obtained from the two endpoint estimates. -/
theorem uniform_lower_lp_bounds {𝕜 : Type u} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (m : ℕ → 𝕜),
      (∀ n ∈ S, ‖m n‖ ≤ 1) → ∀ f : Lp 𝕜 p (volume : Measure I),
        ‖finiteTransform S m f‖ ≤ C * ‖f‖ := by
  have hptop : p ≠ ∞ := ne_top_of_lt hp2
  have hr1 : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by simp) hptop).mpr hp
  have hr2 : p.toReal < 2 := by
    simpa only [ENNReal.toReal_ofNat] using
      (ENNReal.toReal_lt_toReal hptop (by simp)).mpr hp2
  apply uniform_lp_bound_of_power_integral_bound hp hptop
    (K := p.toReal * (6 / (p.toReal - 1) + 4 / (2 - p.toReal)))
  · positivity
  · exact fun S m hm f => two_tail_power_integral hp hp2 S m hm f

/-- Every finite Haar multiplier in the closed scalar unit disk has a bound
at each interior exponent, independently of the finite subset and multiplier. -/
theorem uniform_lp_bounds : Spec.UniformLpBounds.{u} := by
  apply uniformLpBounds_of_complex_lower_range
  intro p _ hp hp2
  exact uniform_lower_lp_bounds p hp hp2

/-- The finite-subset Haar expansion converges to the original Lp element. -/
theorem haar_unconditional_expansion : Spec.HaarUnconditionalExpansion.{u} :=
  (bounds_imply_unconditional uniform_lp_bounds).1

/-- The dyadic Haar basis is unconditional throughout 1 < p < infinity. -/
theorem haar_unconditional_basis : Spec.HaarUnconditionalBasis.{u} :=
  (bounds_imply_unconditional uniform_lp_bounds).2


end ExpandedFA.P1.HaarUnconditional
