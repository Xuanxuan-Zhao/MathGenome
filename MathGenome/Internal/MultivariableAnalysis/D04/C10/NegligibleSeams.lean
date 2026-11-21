import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.NegligibleSeams
import MathGenome.Internal.MultivariableAnalysis.D04.C10.SurfaceAssembly
import MathGenome.Internal.MultivariableAnalysis.D04.C07.NullPreservation

noncomputable section
open Set Filter Topology MeasureTheory Function
open scoped ContDiff ENNReal NNReal BigOperators Classical RealInnerProductSpace
namespace D04.NegligibleSeams
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C10.NegligibleSeams.Model
open D04.NullCovers

/-- The elementary Hausdorff diameter-cover comparison in dimensions 1 and 2.
This uses no area formula: finite length of an interval forces its 2-content
to vanish, and the Lipschitz diameter bound passes this to the image. -/
lemma interval_hausdorff_two_zero (a b : ℝ) :
    Measure.hausdorffMeasure 2 (Icc a b) = 0 := by
  rcases Measure.hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2)
    (Icc a b) with h | h
  · exact h
  · rw [hausdorffMeasure_real] at h
    exact False.elim ((measure_Icc_lt_top : volume (Icc a b) < (⊤ : ℝ≥0∞)).ne h)

lemma lipschitz_curve_hausdorff_two_zero {n : ℕ} (a b : ℝ)
    (γ : ℝ → E n) {L : ℝ≥0} (hγ : LipschitzOnWith L γ (Icc a b)) :
    Measure.hausdorffMeasure 2 (γ '' Icc a b) = 0 :=
  D04.NullPreservation.hausdorff_null_image hγ (by norm_num)
    (interval_hausdorff_two_zero a b)

theorem lipschitz_curve_contentZero :
    Specs.D04.C10.NegligibleSeams.lipschitz_curve_contentZeroType := by
  intro a b γ L hγ
  apply compact_null_contentZero
  · exact isCompact_Icc.image_of_continuousOn hγ.continuousOn
  · exact (D04.NullPreservation.null_iff_hausdorff_zero (by norm_num) _).mpr
      (lipschitz_curve_hausdorff_two_zero a b γ hγ)

lemma curveTrace_compact {n : ℕ} (γ : CompactCurve n) : IsCompact (curveTrace γ) :=
  isCompact_Icc.image_of_continuousOn γ.regular.continuousOn

lemma curveTrace_hausdorff_two_zero {n : ℕ} (γ : CompactCurve n) :
    Measure.hausdorffMeasure 2 (curveTrace γ) = 0 := by
  obtain ⟨L, hL⟩ := γ.regular.exists_lipschitzOnWith (by norm_num)
    (convex_Icc γ.lower γ.upper) isCompact_Icc
  exact lipschitz_curve_hausdorff_two_zero _ _ _ hL

lemma finiteSeam_compact {n : ℕ} {Z : Set (E n)} (hZ : FiniteSeam Z) : IsCompact Z := by
  obtain ⟨m, γ, p, rfl⟩ := hZ
  exact (isCompact_iUnion fun i => curveTrace_compact (γ i)).union p.finite_toSet.isCompact

lemma finiteSeam_hausdorff_two_zero {n : ℕ} {Z : Set (E n)} (hZ : FiniteSeam Z) :
    Measure.hausdorffMeasure 2 Z = 0 := by
  obtain ⟨m, γ, p, rfl⟩ := hZ
  apply measure_union_null
  · exact measure_iUnion_null fun i => curveTrace_hausdorff_two_zero (γ i)
  · letI := Measure.nullSingletonClass_hausdorff (E n) (by norm_num : (0 : ℝ) < 2)
    exact p.finite_toSet.countable.measure_zero _

/-- A C¹ map preserves 2-dimensional Hausdorff nullity on its open domain,
including when source and target have different dimensions. Only local
Lipschitz estimates and countable unions are involved. -/
lemma contDiffOn_hausdorff_two_zero {n k : ℕ} {U S : Set (E n)}
    {F : E n → E k} (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U)
    (hS : Measure.hausdorffMeasure 2 S = 0) :
    Measure.hausdorffMeasure 2 (F '' (S ∩ U)) = 0 := by
  classical
  have hlocal (x : U) : ∃ (L : ℝ≥0) (W : Set (E n)),
      IsOpen W ∧ x.val ∈ W ∧ W ⊆ U ∧ LipschitzOnWith L F W := by
    obtain ⟨L, T, hT, hL⟩ := (hF.contDiffAt (hU.mem_nhds x.property)).exists_lipschitzOnWith
    obtain ⟨W, hWT, hW, hxW⟩ := mem_nhds_iff.mp (inter_mem hT (hU.mem_nhds x.property))
    exact ⟨L, W, hW, hxW, fun y hy => (hWT hy).2,
      hL.mono fun y hy => (hWT hy).1⟩
  choose L W hWo hxW hWU hL using hlocal
  obtain ⟨A, hA, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  let := hA.to_subtype
  apply measure_mono_null (t := ⋃ x : A, F '' (S ∩ W x))
  · rintro y ⟨x, ⟨hxS, hxU⟩, rfl⟩
    have hm : x ∈ ⋃ y : U, W y := mem_iUnion.mpr ⟨⟨x, hxU⟩, hxW ⟨x, hxU⟩⟩
    rw [← hcover] at hm
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hm
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, x, ⟨hxS, hxi⟩, rfl⟩
  · apply measure_iUnion_null
    intro x
    exact D04.NullPreservation.hausdorff_null_image ((hL x).mono inter_subset_right)
      (by norm_num) (measure_mono_null inter_subset_left hS)

/-- Local ambient inverses identify each lifted part of a null seam with a
C¹ image of that seam. Raw chart inverses are never assumed differentiable
off the surface. -/
lemma areaNull_of_hausdorff_two_zero {n : ℕ} {M Z : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (hZ : Measure.hausdorffMeasure 2 Z = 0) :
    AreaNull M Z := by
  classical
  intro c
  have hlocal (u : c.source) : ∃ (O : Set (E n)) (J : E n → E 2),
      IsOpen O ∧ c.toFun u ∈ O ∧ ContDiffOn ℝ 1 J O ∧
      EqOn J c.invFun ((M ∩ c.ambient) ∩ O) :=
    D04.chart_inverse_extension c hM.1 hM.2.1 u u.property
  choose O J hO huO hJ heJ using hlocal
  obtain ⟨A, hA, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  let := hA.to_subtype
  apply null_mono (T := ⋃ u : A, J u '' (Z ∩ O u))
  · rintro v ⟨hv, hvZ⟩
    have hm : c.toFun v ∈ ⋃ u : c.source, O u :=
      mem_iUnion.mpr ⟨⟨v, hv⟩, huO ⟨v, hv⟩⟩
    rw [← hcover] at hm
    obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.mp hm
    refine mem_iUnion.mpr ⟨⟨i, hi⟩, c.toFun v, ⟨hvZ, hvi⟩, ?_⟩
    exact (heJ i ⟨c.map_source hv, hvi⟩).trans (c.left_inv v hv)
  · apply null_iUnion_countable
    intro u
    exact (D04.NullPreservation.null_iff_hausdorff_zero (by norm_num) _).mpr
      (contDiffOn_hausdorff_two_zero (hO u) (hJ u) hZ)

theorem finite_seam_areaNull :
    Specs.D04.C10.NegligibleSeams.finite_seam_areaNullType := by
  intro n M Z hM hZ _hZM
  exact ⟨finiteSeam_compact hZ,
    areaNull_of_hausdorff_two_zero hM (finiteSeam_hausdorff_two_zero hZ)⟩

theorem compact_chart_seam_contentZero :
    Specs.D04.C10.NegligibleSeams.compact_chart_seam_contentZeroType := by
  intro n M Z hM hZ hZM c K hK hKc
  have hs := finite_seam_areaNull hM hZ hZM
  apply compact_null_contentZero
  · exact hK.of_isClosed_subset
      ((c.continuous_toFun.mono hKc).preimage_isClosed_of_isClosed hK.isClosed hs.1.isClosed)
      inter_subset_left
  · exact null_mono (S := K ∩ c.toFun ⁻¹' Z)
      (T := c.source ∩ c.toFun ⁻¹' Z) (fun _ h => ⟨hKc h.1, h.2⟩) (hs.2 c)


namespace Riemann
open Specs.D04.C06.JordanRegions.Model hiding volume
open D04.Darboux
open D04SurfaceAssembly.PieceAssembly

lemma integrable_max {n : ℕ} {Q : Box n} {f g : E n → ℝ}
    (hf : Integrable f Q) (hg : Integrable g Q) :
    Integrable (fun x => max (f x) (g x)) Q := by
  have hd := integrable_add hf (integrable_smul (-1) hg)
  have hi := integrable_smul (1 / 2)
    (integrable_add (integrable_add hf hg) (integrable_abs hd))
  convert hi using 1
  funext x
  rcases le_total (f x) (g x) with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith : f x + -1 * g x ≤ 0)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith : 0 ≤ f x + -1 * g x)]
    ring

/-- Integrability on both sides is retained when an inequality is known only
off a null set. This does not assert arbitrary null-set modifications preserve
Riemann integrability. -/
lemma integral_mono_off_null {Q : Box 2} {f g : E 2 → ℝ}
    (hf : Integrable f Q) (hg : Integrable g Q) {Z : Set (E 2)} (hZ : Null Z)
    (hle : ∀ x ∈ carrier Q, x ∉ Z → f x ≤ g x) :
    integral f Q hf ≤ integral g Q hg := by
  have hm := integrable_max hf hg
  have he := D04.ExceptionalSets.integral_eq_of_eq_off_null (by norm_num : 0 < 2)
    hm hg hZ (fun x hx hZ => max_eq_right (hle x hx hZ))
  exact (integral_mono hf hm (fun x _ => le_max_left _ _)).trans_eq he

/-- A continuous nonnegative majorant of a compact planar null set, with
arbitrarily small actual Riemann integral. Continuity makes its positive
level sets neighborhoods of the exceptional set. -/
lemma compact_null_majorant {K : Set (E 2)} (hK : IsCompact K) (hz : Null K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E 2 → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x ∈ K, 1 ≤ g x) ∧
      openIntegral (fun x : (univ : Set (E 2)) => g x) < ε := by
  classical
  let f : E 2 → ℝ := fun x => if x ∈ K then 1 else 0
  have hsf : tsupport f ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (by simp [f, hn])
  obtain ⟨Q, hQ⟩ := (D04.JordanRegions.encloses_exists_iff_bounded K).mpr hK.isBounded
  obtain ⟨hfi, _⟩ := D04.ExceptionalSets.zero_off_contentZero (by norm_num : 0 < 2)
    (bounded_of_abs_le (h := f) (M := 1) (Q := Q) (fun x _ => by dsimp [f]; split_ifs <;> norm_num))
    (compact_null_contentZero K hK hz) (fun x _ hx => by simp [f, hx])
  obtain ⟨l, g, hl, hg, hlK, hgK, _, _, hfg, _, _, _, hgap⟩ :=
    D04.ContinuousSandwich.continuous_sandwich univ K f isOpen_univ hK (subset_univ _)
      hsf ⟨Q, (closure_mono ((subset_tsupport f).trans hsf)).trans hQ, hfi⟩ ε hε
  have hnon (x : E 2) : 0 ≤ g x :=
    (show 0 ≤ f x by dsimp [f]; split_ifs <;> norm_num).trans (hfg x).2
  refine ⟨g, hg, hgK, hnon, fun x hx => by simpa [f, hx] using (hfg x).2, ?_⟩
  let C := tsupport l ∪ tsupport g
  obtain ⟨R, hR⟩ := (D04.JordanRegions.encloses_exists_iff_bounded C).mpr
    (hlK.union hgK).isBounded
  have hRl : Encloses (support l) R :=
    (closure_mono ((subset_tsupport l).trans subset_union_left)).trans hR
  have hRg : Encloses (support g) R :=
    (closure_mono ((subset_tsupport g).trans subset_union_right)).trans hR
  have hRd : Encloses (support (fun x => g x - l x)) R := by
    apply (closure_mono (t := C) ?_).trans hR
    intro x hx
    by_contra hxc
    have hxl : x ∉ tsupport l := fun h => hxc (Or.inl h)
    have hxg : x ∉ tsupport g := fun h => hxc (Or.inr h)
    exact hx (by change g x - l x = 0; rw [image_eq_zero_of_notMem_tsupport hxl,
      image_eq_zero_of_notMem_tsupport hxg, sub_self])
  have hli := D04.ContinuousSandwich.continuous_integrable l hl R
  have hgi := D04.ContinuousSandwich.continuous_integrable g hg R
  have hni := integrable_smul (-1) hli
  have hdi : Integrable (fun x => g x - l x) R := by
    simpa only [neg_one_mul, sub_eq_add_neg] using integrable_add hgi hni
  have hv : integral (fun x => g x - l x) R hdi = integral g R hgi - integral l R hli := by
    have hh := integral_add hgi hni
      (show Integrable (fun x => g x + -1 * l x) R by simpa only [neg_one_mul, sub_eq_add_neg] using hdi)
    rw [integral_smul (-1) hli hni] at hh
    simpa only [neg_one_mul, sub_eq_add_neg] using hh
  have hl0 : integral l R hli ≤ 0 := by
    simpa only [integral_const R 0, zero_mul] using
      integral_mono_off_null hli (integrable_const R 0) hz
        (fun x _ hx => by simpa [f, hx] using (hfg x).1)
  have hgap' : integral (fun x => g x - l x) R hdi < ε := by
    have he := D04.ContinuousSandwich.restrict_integral_eq isOpen_univ (hg.sub hl)
      (hgK.sub hlK) (subset_univ _) R hRd
    change openIntegral (fun x : (univ : Set (E 2)) => g x - l x) = _ at he
    rw [he] at hgap
    exact hgap
  have he := D04.ContinuousSandwich.restrict_integral_eq isOpen_univ hg hgK (subset_univ _) R hRg
  change openIntegral (fun x : (univ : Set (E 2)) => g x) = _ at he
  rw [he]
  linarith


open Specs.D04.C15.DirectedSubstitution.Model

/-- A compact-null exhaustion criterion for the actual Riemann coefficients.
The exceptional sets N_j allow the harmless multiple values on shared faces.
Neither arbitrary pointwise convergence nor an unbounded tail is sufficient. -/
lemma proper_truncation_convergence {V : Set (E 2)} (a : V → ℝ) (b : ℕ → V → ℝ)
    (ha : ProperIntegrable a) (hb : ∀ j, ProperIntegrable (b j))
    (C K : Set (E 2)) (hC : IsCompact C) (hK : IsCompact K) (hz : Null K)
    (haC : support (zeroExtension a) ⊆ C)
    (hbC : ∀ j, support (zeroExtension (b j)) ⊆ C)
    (N : ℕ → Set (E 2)) (hN : ∀ j, Null (N j))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ j x, x ∉ N j → |zeroExtension a x - zeroExtension (b j) x| ≤ B)
    (hevent : ∀ U : Set (E 2), IsOpen U → K ⊆ U →
      ∀ᶠ j in atTop, ∀ x ∈ C \ U, x ∉ N j → zeroExtension a x = zeroExtension (b j) x) :
    Tendsto (fun j => coefficientIntegral (b j)) atTop (𝓝 (coefficientIntegral a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := 2 * (B + 1)
  have hA : 0 < A := by dsimp [A]; linarith
  obtain ⟨g, hg, hgK, hg0, hgK1, hgiSmall⟩ := compact_null_majorant hK hz (div_pos hε hA)
  let U : Set (E 2) := {x | (1 / 2 : ℝ) < g x}
  have hU : IsOpen U := isOpen_lt continuous_const hg
  have hKU : K ⊆ U := fun x hx => lt_of_lt_of_le (by norm_num) (hgK1 x hx)
  filter_upwards [hevent U hU hKU] with j hj
  obtain ⟨Q, hQ⟩ := (D04.JordanRegions.encloses_exists_iff_bounded (C ∪ tsupport g)).mpr
    (hC.union hgK).isBounded
  have hQa : Encloses (support (zeroExtension a)) Q :=
    (closure_mono (haC.trans subset_union_left)).trans hQ
  have hQb : Encloses (support (zeroExtension (b j))) Q :=
    (closure_mono ((hbC j).trans subset_union_left)).trans hQ
  have hQg : Encloses (support g) Q :=
    (closure_mono ((subset_tsupport g).trans subset_union_right)).trans hQ
  obtain ⟨hai, hva⟩ := coefficientIntegral_eq_on_box ha Q hQa
  obtain ⟨hbi, hvb⟩ := coefficientIntegral_eq_on_box (hb j) Q hQb
  have hgi := D04.ContinuousSandwich.continuous_integrable g hg Q
  have hneg := integrable_smul (-1) hbi
  have hd : Integrable (fun x => zeroExtension a x - zeroExtension (b j) x) Q := by
    simpa only [neg_one_mul, sub_eq_add_neg] using integrable_add hai hneg
  have habs := integrable_abs hd
  have hvd : integral (fun x => zeroExtension a x - zeroExtension (b j) x) Q hd =
      coefficientIntegral a - coefficientIntegral (b j) := by
    rw [hva, hvb]
    have hh := integral_add hai hneg
      (show Integrable (fun x => zeroExtension a x + -1 * zeroExtension (b j) x) Q by
        simpa only [neg_one_mul, sub_eq_add_neg] using hd)
    rw [integral_smul (-1) hbi hneg] at hh
    simpa only [neg_one_mul, sub_eq_add_neg] using hh
  have hmono : integral (fun x => |zeroExtension a x - zeroExtension (b j) x|) Q habs ≤
      A * integral g Q hgi := by
    rw [← integral_smul A hgi (integrable_smul A hgi)]
    apply integral_mono_off_null habs (integrable_smul A hgi) (hN j)
    intro x _ hxN
    by_cases hxC : x ∈ C
    · by_cases hxU : x ∈ U
      · have hgx : (1 / 2 : ℝ) < g x := hxU
        have hBA : B ≤ A * g x := by dsimp [A]; nlinarith [hg0 x]
        exact (hbound j x hxN).trans hBA
      · rw [hj x ⟨hxC, hxU⟩ hxN, sub_self, abs_zero]
        exact mul_nonneg hA.le (hg0 x)
    · have hxa : zeroExtension a x = 0 := notMem_support.mp (fun h => hxC (haC h))
      have hxb : zeroExtension (b j) x = 0 := notMem_support.mp (fun h => hxC (hbC j h))
      rw [hxa, hxb, sub_self, abs_zero]
      exact mul_nonneg hA.le (hg0 x)
  have hgs : integral g Q hgi < ε / A := by
    have he := D04.ContinuousSandwich.restrict_integral_eq isOpen_univ hg hgK (subset_univ _) Q hQg
    change openIntegral (fun x : (univ : Set (E 2)) => g x) = _ at he
    rwa [he] at hgiSmall
  have hab : |coefficientIntegral a - coefficientIntegral (b j)| < ε := by
    calc
      _ = |integral (fun x => zeroExtension a x - zeroExtension (b j) x) Q hd| := congrArg abs hvd.symm
      _ ≤ _ := (integral_abs_bound hd habs).1
      _ ≤ _ := hmono
      _ < A * (ε / A) := mul_lt_mul_of_pos_left hgs hA
      _ = ε := mul_div_cancel₀ ε hA.ne'
  simpa only [Real.dist_eq, abs_sub_comm] using hab


end Riemann

open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C06.JordanRegions.Model hiding volume
open D04SurfaceAssembly.PieceAssembly

/-- The union of all paired-face exceptions in one chart. -/
def overlapException {n : ℕ} {M Z : Set (E n)} (T : SurfaceTruncation M Z)
    (c : EmbeddedChart 1 2 n M) : Set (E 2) :=
  ⋃ q : Fin T.count × Fin T.count,
    if q.1 = q.2 then ∅ else
      c.source ∩ c.toFun ⁻¹' (pieceImage (T.piece q.1) ∩ pieceImage (T.piece q.2))

lemma overlapException_null {n : ℕ} {M Z : Set (E n)} (T : SurfaceTruncation M Z)
    (c : EmbeddedChart 1 2 n M) : Null (overlapException T c) := by
  apply null_iUnion_countable
  intro q
  split_ifs with h
  · exact D04.ExceptionalSets.null_empty
  · exact T.overlaps q.1 q.2 h c

lemma truncation_chart_sum {n : ℕ} {M Z : Set (E n)} (T : SurfaceTruncation M Z)
    (f : M → ℝ) (c : EmbeddedChart 1 2 n M) (w : E n → ℝ)
    (u : c.source) (hu : u.val ∉ overlapException T c) :
    (∑ i, pieceChartCoefficient (T.piece i) f c w u) =
      if c.toFun u ∈ truncationSet T then localizedDensityCoefficient f c w u else 0 := by
  classical
  by_cases hx : c.toFun u ∈ truncationSet T
  · rw [if_pos hx]
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hother (i : Fin T.count) (hij : i ≠ j) : c.toFun u ∉ pieceImage (T.piece i) := by
      intro hi
      apply hu
      exact mem_iUnion.mpr ⟨(i, j), by
        simp only [hij, ite_false, mem_inter_iff, mem_preimage]
        exact ⟨u.property, hi, hj⟩⟩
    rw [Finset.sum_eq_single j]
    · simp only [pieceChartCoefficient, hj, ite_true, localizedDensityCoefficient]
    · intro i _ hij
      simp [pieceChartCoefficient, hother i hij]
    · simp
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro i _
    have hi : c.toFun u ∉ pieceImage (T.piece i) :=
      fun h => hx (mem_iUnion.mpr ⟨i, h⟩)
    simp [pieceChartCoefficient, hi]

lemma chart_truncation_convergence {n : ℕ} {M Z : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (hZ : IsCompact Z) (hz : AreaNull M Z)
    (f : M → ℝ) (hf : Continuous f) (T : ℕ → SurfaceTruncation M Z)
    (hT : ExhaustsComplement T) (c : EmbeddedChart 1 2 n M) (w : E n → ℝ)
    (hw : Continuous w) (hwK : IsCompact (tsupport (fun x : M => w x)))
    (hwc : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    Tendsto (fun j => ∑ i, pieceIntegral ((T j).piece i) (fun x => w x * f x))
      atTop (𝓝 (coefficientIntegral (localizedDensityCoefficient f c w))) := by
  classical
  let a := localizedDensityCoefficient f c w
  let b (j : ℕ) (u : c.source) := ∑ i, pieceChartCoefficient ((T j).piece i) f c w u
  have hai := (D04.ManifoldIntegral.localized_coefficient_integrable c w
    (densityCoefficient f c) hw
    (D04.ManifoldIntegralIndependence.densityCoefficient_continuous hM f hf c) hwK hwc).2.2
  have hbi (j : ℕ) := proper_sum (fun i => pieceChartCoefficient ((T j).piece i) f c w)
    (fun i => (piece_chart_comparison hM ((T j).piece i) f hf c w hw hwK hwc).1)
  have hwcompact := D04.ManifoldIntegral.chart_weight_compact c w hwK hwc
  let C : Set (E 2) := Subtype.val '' tsupport (fun u : c.source => w (c.toFun u))
  have hC : IsCompact C := hwcompact.image continuous_subtype_val
  have hCc : C ⊆ c.source := by rintro _ ⟨u, _, rfl⟩; exact u.property
  let K := C ∩ c.toFun ⁻¹' Z
  have hK : IsCompact K := hC.of_isClosed_subset
    ((c.continuous_toFun.mono hCc).preimage_isClosed_of_isClosed hC.isClosed hZ.isClosed)
    inter_subset_left
  have hKz : Null K := null_mono (T := c.source ∩ c.toFun ⁻¹' Z)
    (fun _ h => ⟨hCc h.1, h.2⟩) (hz c)
  have hweightzero {x : E 2} (hx : x ∉ C) (hxc : x ∈ c.source) : w (c.toFun x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := fun u : c.source => w (c.toFun u))
      (x := ⟨x, hxc⟩)
    intro h
    exact hx ⟨⟨x, hxc⟩, h, rfl⟩
  have haC : support (zeroExtension a) ⊆ C := by
    intro x hx
    by_contra hxc
    apply hx
    by_cases hxs : x ∈ c.source
    · rw [zeroExtension_apply a ⟨x, hxs⟩]
      change w (c.toFun x) * _ = 0
      rw [hweightzero hxc hxs, zero_mul]
    · exact zeroExtension_of_not_mem a hxs
  have hbC (j : ℕ) : support (zeroExtension (b j)) ⊆ C := by
    intro x hx
    by_contra hxc
    apply hx
    by_cases hxs : x ∈ c.source
    · rw [zeroExtension_apply (b j) ⟨x, hxs⟩]
      apply Finset.sum_eq_zero
      intro i _
      dsimp only [pieceChartCoefficient]
      split_ifs <;> simp [hweightzero hxc hxs]
    · exact zeroExtension_of_not_mem (b j) hxs
  obtain ⟨B, hB⟩ := regionBounded_of_proper hai
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hbound (j : ℕ) (x : E 2) (hx : x ∉ overlapException (T j) c) :
      |zeroExtension a x - zeroExtension (b j) x| ≤ max B 0 := by
    by_cases hxs : x ∈ c.source
    · rw [zeroExtension_apply a ⟨x, hxs⟩, zeroExtension_apply (b j) ⟨x, hxs⟩]
      change |a ⟨x, hxs⟩ - ∑ i, pieceChartCoefficient ((T j).piece i) f c w ⟨x, hxs⟩| ≤ _
      rw [truncation_chart_sum (T j) f c w ⟨x, hxs⟩ hx]
      dsimp only [a]
      split_ifs
      · simp only [sub_self, abs_zero]; exact hB0
      · simpa only [sub_zero, Real.norm_eq_abs, localizedDensityCoefficient] using (hB ⟨x, hxs⟩).trans (le_max_left B 0)
    · rw [zeroExtension_of_not_mem a hxs, zeroExtension_of_not_mem (b j) hxs, sub_self, abs_zero]
      exact hB0
  have hev (U : Set (E 2)) (hU : IsOpen U) (hKU : K ⊆ U) :
      ∀ᶠ j in atTop, ∀ x ∈ C \ U, x ∉ overlapException (T j) c →
        zeroExtension a x = zeroExtension (b j) x := by
    let H := c.toFun '' (C \ U)
    have hH : IsCompact H := (hC.diff hU).image_of_continuousOn
      (c.continuous_toFun.mono (diff_subset.trans hCc))
    have hHM : H ⊆ M \ Z := by
      rintro _ ⟨x, ⟨hxC, hxU⟩, rfl⟩
      refine ⟨(c.map_source (hCc hxC)).1, ?_⟩
      intro hxZ
      exact hxU (hKU ⟨hxC, hxZ⟩)
    filter_upwards [hT H hH hHM] with j hj x hx hxn
    have hxs := hCc hx.1
    rw [zeroExtension_apply a ⟨x, hxs⟩, zeroExtension_apply (b j) ⟨x, hxs⟩]
    change a ⟨x, hxs⟩ = ∑ i, pieceChartCoefficient ((T j).piece i) f c w ⟨x, hxs⟩
    rw [truncation_chart_sum (T j) f c w ⟨x, hxs⟩ hxn, if_pos (hj ⟨x, hx, rfl⟩)]
  have hconv := Riemann.proper_truncation_convergence a b hai (fun j => (hbi j).1)
    C K hC hK hKz haC hbC (fun j => overlapException (T j) c)
    (fun j => overlapException_null (T j) c) (max B 0) hB0 hbound hev
  have heq (j : ℕ) : coefficientIntegral (b j) =
      ∑ i, pieceIntegral ((T j).piece i) (fun x => w x * f x) := by
    rw [(hbi j).2]
    exact Finset.sum_congr rfl (fun i _ => (piece_chart_comparison hM ((T j).piece i)
      f hf c w hw hwK hwc).2)
  simpa only [heq] using hconv

/-- Finite chart localization of a regular compact truncation. -/
lemma truncation_partition_formula {n : ℕ} {M Z : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (T : SurfaceTruncation M Z)
    (P : ChartPartition 1 2 M univ) (f : M → ℝ) (hf : Continuous f) :
    truncationIntegral T f = ∑ j, ∑ i,
      pieceIntegral (T.piece i) (fun x => P.weight j x * f x) := by
  classical
  have hs (x : M) (_ : f x ≠ 0) : ∑ j, P.weight j x = 1 := by
    obtain ⟨V, _, hV, hsum⟩ := P.partition.2.2.2.1
    exact hsum x (hV (mem_univ x))
  change (∑ i, pieceIntegral (T.piece i) f) = _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => piece_localization hM (T.piece i) f hf
    P.weight (fun j => (P.partition.1 j).continuous) hs)

theorem seam_truncation_convergence :
    Specs.D04.C10.NegligibleSeams.seam_truncation_convergenceType := by
  intro n M Z hM hc hZ hZM f hf T hT
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hc
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (univ : Set M) isCompact_univ
  obtain ⟨hZK, hZa⟩ := finite_seam_areaNull hM hZ hZM
  rw [D04SurfaceAssembly.scalar_chart_formula hM hc f hf P (subset_univ _)]
  have hconv := tendsto_finset_sum Finset.univ (fun i _ => chart_truncation_convergence
    hM hZK hZa f hf T hT (P.chart i) (P.weight i) (P.partition.1 i).continuous
      (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2)
  simpa only [← truncation_partition_formula hM _ P f hf] using hconv

theorem seam_flux_truncation_convergence :
    Specs.D04.C10.NegligibleSeams.seam_flux_truncation_convergenceType := by
  intro M Z hM hc hZ hZM N F hF T hT
  exact seam_truncation_convergence hM hc hZ hZM (fun x => ⟪F x, N.toFun x⟫)
    (hF.inner N.continuous) T hT


namespace Riemann
open D04.Darboux

lemma integral_sub {Q : Box 2} {f g : E 2 → ℝ} (hf : Integrable f Q) (hg : Integrable g Q) :
    ∃ hi : Integrable (fun x => f x - g x) Q,
      integral (fun x => f x - g x) Q hi = integral f Q hf - integral g Q hg := by
  have hn := integrable_smul (-1) hg
  have hi := integrable_add hf hn
  refine ⟨by simpa only [neg_one_mul, sub_eq_add_neg] using hi, ?_⟩
  have hh := integral_add hf hn hi
  rw [integral_smul (-1) hg hn] at hh
  simpa only [neg_one_mul, sub_eq_add_neg] using hh

lemma coefficient_difference_bound {V : Set (E 2)} (a b c d : V → ℝ)
    (ha : ProperIntegrable a) (hb : ProperIntegrable b)
    (hc : ProperIntegrable c) (hd : ProperIntegrable d)
    (N : Set (E 2)) (hN : Null N) (B : ℝ)
    (hbound : ∀ x, x ∉ N → |zeroExtension a x - zeroExtension b x| ≤
      B * (zeroExtension c x - zeroExtension d x)) :
    |coefficientIntegral a - coefficientIntegral b| ≤
      B * (coefficientIntegral c - coefficientIntegral d) := by
  let S := (support (zeroExtension a) ∪ support (zeroExtension b)) ∪
    (support (zeroExtension c) ∪ support (zeroExtension d))
  obtain ⟨Q, hQ⟩ := (D04.JordanRegions.encloses_exists_iff_bounded S).mpr
    ((ha.1.union hb.1).union (hc.1.union hd.1))
  have hQa : Encloses (support (zeroExtension a)) Q :=
    (closure_mono (subset_union_left.trans subset_union_left)).trans hQ
  have hQb : Encloses (support (zeroExtension b)) Q :=
    (closure_mono (subset_union_right.trans subset_union_left)).trans hQ
  have hQc : Encloses (support (zeroExtension c)) Q :=
    (closure_mono (subset_union_left.trans subset_union_right)).trans hQ
  have hQd : Encloses (support (zeroExtension d)) Q :=
    (closure_mono (subset_union_right.trans subset_union_right)).trans hQ
  obtain ⟨hai, hva⟩ := coefficientIntegral_eq_on_box ha Q hQa
  obtain ⟨hbi, hvb⟩ := coefficientIntegral_eq_on_box hb Q hQb
  obtain ⟨hci, hvc⟩ := coefficientIntegral_eq_on_box hc Q hQc
  obtain ⟨hdi, hvd⟩ := coefficientIntegral_eq_on_box hd Q hQd
  obtain ⟨hab, habv⟩ := integral_sub hai hbi
  obtain ⟨hcd, hcdv⟩ := integral_sub hci hdi
  have habs := integrable_abs hab
  rw [hva, hvb, hvc, hvd, ← habv, ← hcdv,
    ← integral_smul B hcd (integrable_smul B hcd)]
  exact (integral_abs_bound hab habs).1.trans
    (integral_mono_off_null habs (integrable_smul B hcd) hN (fun x _ hx => hbound x hx))
end Riemann

lemma chart_truncation_error_bound {n : ℕ} {M Z : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (T : SurfaceTruncation M Z)
    (f : M → ℝ) (hf : Continuous f) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ B)
    (c : EmbeddedChart 1 2 n M) (w : E n → ℝ) (hw : Continuous w)
    (hw0 : ∀ x : M, 0 ≤ w x)
    (hwK : IsCompact (tsupport (fun x : M => w x)))
    (hwc : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    |coefficientIntegral (localizedDensityCoefficient f c w) -
      ∑ i, pieceIntegral (T.piece i) (fun x => w x * f x)| ≤
    B * (coefficientIntegral (localizedDensityCoefficient (fun _ => 1) c w) -
      ∑ i, pieceIntegral (T.piece i) (fun x => w x * 1)) := by
  classical
  have hai (g : M → ℝ) (hg : Continuous g) :=
    (D04.ManifoldIntegral.localized_coefficient_integrable c w
      (densityCoefficient g c) hw
      (D04.ManifoldIntegralIndependence.densityCoefficient_continuous hM g hg c) hwK hwc).2.2
  have hbi (g : M → ℝ) (hg : Continuous g) :=
    proper_sum (fun i => pieceChartCoefficient (T.piece i) g c w)
      (fun i => (piece_chart_comparison hM (T.piece i) g hg c w hw hwK hwc).1)
  have hv (g : M → ℝ) (hg : Continuous g) :
      coefficientIntegral (fun u => ∑ i, pieceChartCoefficient (T.piece i) g c w u) =
        ∑ i, pieceIntegral (T.piece i) (fun x => w x * g x) := by
    rw [(hbi g hg).2]
    exact Finset.sum_congr rfl (fun i _ => (piece_chart_comparison hM (T.piece i) g hg c w hw hwK hwc).2)
  rw [← hv f hf, ← hv (fun _ => 1) continuous_const]
  apply Riemann.coefficient_difference_bound _ _ _ _ (hai f hf) (hbi f hf).1
    (hai (fun _ => 1) continuous_const) (hbi (fun _ => 1) continuous_const).1
    (overlapException T c) (overlapException_null T c) B
  intro x hx
  by_cases hxs : x ∈ c.source
  · simp only [zeroExtension_apply _ ⟨x, hxs⟩]
    rw [truncation_chart_sum T f c w ⟨x, hxs⟩ hx,
      truncation_chart_sum T (fun _ => 1) c w ⟨x, hxs⟩ hx]
    split_ifs
    · dsimp only [localizedDensityCoefficient, densityCoefficient]
      simp only [sub_self, abs_zero, mul_zero, le_refl]
    · dsimp only [localizedDensityCoefficient, densityCoefficient]
      simp only [sub_zero, one_mul]
      have hwx : 0 ≤ w (c.toFun x) := hw0 (chartPoint c ⟨x, hxs⟩)
      have hJ : 0 ≤ Specs.D04.C14.MetricTopFormsAndDensities.Model.chartDensity c x :=
        (D04MetricDensity.chartDensity_positive c hM.1 x hxs).le
      rw [abs_mul, abs_mul, abs_of_nonneg hwx, abs_of_nonneg hJ]
      nlinarith [mul_le_mul_of_nonneg_left (hbound (chartPoint c ⟨x, hxs⟩))
        (mul_nonneg hwx hJ)]
  · simp only [zeroExtension_of_not_mem _ hxs, sub_self, abs_zero, mul_zero, le_refl]

theorem truncation_error_bound :
    Specs.D04.C10.NegligibleSeams.truncation_error_boundType := by
  intro n M Z hM hc T f hf B hB hbound
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hc
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (univ : Set M) isCompact_univ
  rw [D04SurfaceAssembly.scalar_chart_formula hM hc f hf P (subset_univ _),
    D04SurfaceAssembly.scalar_chart_formula hM hc (fun _ => 1) continuous_const P (subset_univ _),
    truncation_partition_formula hM T P f hf,
    truncation_partition_formula hM T P (fun _ => 1) continuous_const, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |coefficientIntegral (localizedDensityCoefficient f (P.chart i) (P.weight i)) -
      ∑ j, pieceIntegral (T.piece j) (fun x => P.weight i x * f x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, B * (coefficientIntegral (localizedDensityCoefficient (fun _ => 1) (P.chart i) (P.weight i)) -
      ∑ j, pieceIntegral (T.piece j) (fun x => P.weight i x * 1)) := by
        apply Finset.sum_le_sum
        intro i _
        exact chart_truncation_error_bound hM T f hf B hB hbound (P.chart i) (P.weight i)
          (P.partition.1 i).continuous (P.partition.2.1 i)
          (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]


lemma surface_chart_formula_compact_support {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (f : M → ℝ) (hf : Continuous f) (hk : HasCompactSupport f)
    {K : Set M} (P : ChartPartition 1 2 M K) (hs : tsupport f ⊆ K) :
    surfaceIntegral M f = ∑ i, coefficientIntegral
      (localizedDensityCoefficient f (P.chart i) (P.weight i)) := by
  obtain ⟨Q⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport f) hk
  dsimp only [surfaceIntegral]
  rw [dif_pos (show Nonempty (ChartPartition 1 2 M (tsupport f)) from ⟨Q⟩)]
  exact D04.ManifoldIntegralIndependence.density_comparison hM f hf _ P Subset.rfl hs

lemma truncation_partition_formula_support {n : ℕ} {M Z : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (T : SurfaceTruncation M Z)
    (f : M → ℝ) (hf : Continuous f) (P : ChartPartition 1 2 M (tsupport f)) :
    truncationIntegral T f = ∑ j, ∑ i,
      pieceIntegral (T.piece i) (fun x => P.weight j x * f x) := by
  classical
  have hs (x : M) (hx : f x ≠ 0) : ∑ j, P.weight j x = 1 := by
    obtain ⟨V, _, hV, hsum⟩ := P.partition.2.2.2.1
    exact hsum x (hV (subset_tsupport f hx))
  change (∑ i, pieceIntegral (T.piece i) f) = _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => piece_localization hM (T.piece i) f hf
    P.weight (fun j => (P.partition.1 j).continuous) hs)

theorem compact_support_seam_truncation_convergence :
    Specs.D04.C10.NegligibleSeams.compact_support_seam_truncation_convergenceType := by
  intro n M Z hM hZ hZM f hf hk T hT
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport f) hk
  obtain ⟨hZK, hZa⟩ := finite_seam_areaNull hM hZ hZM
  rw [surface_chart_formula_compact_support hM f hf hk P Subset.rfl]
  have hconv := tendsto_finsetSum Finset.univ (fun i _ => chart_truncation_convergence
    hM hZK hZa f hf T hT (P.chart i) (P.weight i) (P.partition.1 i).continuous
      (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2)
  simpa only [← truncation_partition_formula_support hM _ f hf P] using hconv

lemma truncationSet_compact {n : ℕ} {M Z : Set (E n)} (T : SurfaceTruncation M Z) :
    IsCompact (truncationSet T) :=
  isCompact_iUnion fun i => piece_image_compact (T.piece i)

theorem small_area_neighborhoods :
    Specs.D04.C10.NegligibleSeams.small_area_neighborhoodsType := by
  intro n M Z hM hc hZ hZM T hT ε hε
  have hconv := seam_truncation_convergence hM hc hZ hZM (fun _ => 1) continuous_const T hT
  obtain ⟨j, hj⟩ := ((Metric.tendsto_nhds.mp hconv) ε hε).exists
  refine ⟨j, ?_, ?_, ?_, ?_, fun f hf B hB hb => truncation_error_bound hM hc (T j) f hf B hB hb⟩
  · exact (truncationSet_compact (T j)).isClosed.isOpen_compl.preimage continuous_subtype_val
  · intro x hx
    refine ⟨hZM hx, ?_⟩
    intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ((T j).avoids i hi).2 hx
  · have hh := truncation_error_bound hM hc (T j) (fun _ => 0) continuous_const 1
      (by norm_num) (by simp)
    exact (abs_nonneg _).trans (by simpa only [one_mul] using hh)
  · have hh : |surfaceIntegral M (fun _ => 1) - truncationIntegral (T j) (fun _ => 1)| < ε := by
      simpa only [Real.dist_eq, abs_sub_comm] using hj
    exact (le_abs_self _).trans_lt hh

/-- Localized coordinate coefficients of any finite regular truncation. -/
lemma truncation_chart_integral {n : ℕ} {M Z : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (T : SurfaceTruncation M Z)
    (f : M → ℝ) (hf : Continuous f) (c : EmbeddedChart 1 2 n M)
    (w : E n → ℝ) (hw : Continuous w)
    (hwK : IsCompact (tsupport (fun x : M => w x)))
    (hwc : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    ProperIntegrable (fun u => ∑ i, pieceChartCoefficient (T.piece i) f c w u) ∧
    coefficientIntegral (fun u => ∑ i, pieceChartCoefficient (T.piece i) f c w u) =
      ∑ i, pieceIntegral (T.piece i) (fun x => w x * f x) := by
  have h := proper_sum (fun i => pieceChartCoefficient (T.piece i) f c w)
    (fun i => (piece_chart_comparison hM (T.piece i) f hf c w hw hwK hwc).1)
  refine ⟨h.1, h.2.trans ?_⟩
  exact Finset.sum_congr rfl (fun i _ => (piece_chart_comparison hM (T.piece i) f hf c w hw hwK hwc).2)

lemma chart_portion_truncation_convergence {n : ℕ} {M Z : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (hZ : IsCompact Z) (hz : AreaNull M Z)
    (R : SurfaceTruncation M ∅) (f : M → ℝ) (hf : Continuous f)
    (T : ℕ → SurfaceTruncation M Z) (hT : ExhaustsPortion R T)
    (c : EmbeddedChart 1 2 n M) (w : E n → ℝ) (hw : Continuous w)
    (hwK : IsCompact (tsupport (fun x : M => w x)))
    (hwc : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    Tendsto (fun j => ∑ i, pieceIntegral ((T j).piece i) (fun x => w x * f x))
      atTop (𝓝 (∑ i, pieceIntegral (R.piece i) (fun x => w x * f x))) := by
  classical
  let a (u : c.source) := ∑ i, pieceChartCoefficient (R.piece i) f c w u
  let b (j : ℕ) (u : c.source) := ∑ i, pieceChartCoefficient ((T j).piece i) f c w u
  have hai := truncation_chart_integral hM R f hf c w hw hwK hwc
  have hbi (j : ℕ) := truncation_chart_integral hM (T j) f hf c w hw hwK hwc
  let C : Set (E 2) := Subtype.val '' tsupport (fun u : c.source => w (c.toFun u))
  have hC : IsCompact C := (D04.ManifoldIntegral.chart_weight_compact c w hwK hwc).image continuous_subtype_val
  have hCc : C ⊆ c.source := by rintro _ ⟨u, _, rfl⟩; exact u.property
  let K := C ∩ c.toFun ⁻¹' Z
  have hK : IsCompact K := hC.of_isClosed_subset
    ((c.continuous_toFun.mono hCc).preimage_isClosed_of_isClosed hC.isClosed hZ.isClosed)
    inter_subset_left
  have hKz : Null K := null_mono (T := c.source ∩ c.toFun ⁻¹' Z)
    (fun _ h => ⟨hCc h.1, h.2⟩) (hz c)
  have hs {Y : Set (E n)} (S : SurfaceTruncation M Y) :
      support (zeroExtension (fun u => ∑ i, pieceChartCoefficient (S.piece i) f c w u)) ⊆ C := by
    intro x hx
    by_contra hxc
    apply hx
    by_cases hxs : x ∈ c.source
    · rw [zeroExtension_apply _ ⟨x, hxs⟩]
      have hwzero : w (c.toFun x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun u : c.source => w (c.toFun u)) (x := ⟨x, hxs⟩)
        exact fun h => hxc ⟨⟨x, hxs⟩, h, rfl⟩
      apply Finset.sum_eq_zero
      intro i _
      simp [pieceChartCoefficient, hwzero]
    · exact zeroExtension_of_not_mem _ hxs
  let N (j : ℕ) := overlapException R c ∪ overlapException (T j) c
  have hN (j : ℕ) : Null (N j) :=
    D04.JordanRegions.null_union (overlapException_null R c) (overlapException_null (T j) c)
  have hfi := (D04.ManifoldIntegral.localized_coefficient_integrable c w
    (densityCoefficient f c) hw
    (D04.ManifoldIntegralIndependence.densityCoefficient_continuous hM f hf c) hwK hwc).2.2
  obtain ⟨B, hB⟩ := regionBounded_of_proper hfi
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hbound (j : ℕ) (x : E 2) (hx : x ∉ N j) :
      |zeroExtension a x - zeroExtension (b j) x| ≤ max B 0 := by
    have hxR : x ∉ overlapException R c := fun h => hx (Or.inl h)
    have hxT : x ∉ overlapException (T j) c := fun h => hx (Or.inr h)
    by_cases hxs : x ∈ c.source
    · rw [zeroExtension_apply a ⟨x, hxs⟩, zeroExtension_apply (b j) ⟨x, hxs⟩]
      dsimp only [a, b]
      rw [truncation_chart_sum R f c w ⟨x, hxs⟩ hxR,
        truncation_chart_sum (T j) f c w ⟨x, hxs⟩ hxT]
      by_cases ht : c.toFun x ∈ truncationSet (T j)
      · rw [if_pos ht, if_pos (hT.1 j ht), sub_self, abs_zero]; exact hB0
      · rw [if_neg ht, sub_zero]
        split_ifs
        · simpa only [Real.norm_eq_abs, localizedDensityCoefficient] using
            (hB ⟨x, hxs⟩).trans (le_max_left B 0)
        · simpa using hB0
    · rw [zeroExtension_of_not_mem a hxs, zeroExtension_of_not_mem (b j) hxs, sub_self, abs_zero]
      exact hB0
  have hev (U : Set (E 2)) (hU : IsOpen U) (hKU : K ⊆ U) :
      ∀ᶠ j in atTop, ∀ x ∈ C \ U, x ∉ N j → zeroExtension a x = zeroExtension (b j) x := by
    let D := C ∩ c.toFun ⁻¹' truncationSet R
    have hD : IsCompact D := hC.of_isClosed_subset
      ((c.continuous_toFun.mono hCc).preimage_isClosed_of_isClosed hC.isClosed
        (truncationSet_compact R).isClosed) inter_subset_left
    let H := c.toFun '' (D \ U)
    have hH : IsCompact H := (hD.diff hU).image_of_continuousOn
      (c.continuous_toFun.mono (sdiff_subset.trans (inter_subset_left.trans hCc)))
    have hHR : H ⊆ truncationSet R \ Z := by
      rintro _ ⟨x, ⟨hxD, hxU⟩, rfl⟩
      exact ⟨hxD.2, fun hxZ => hxU (hKU ⟨hxD.1, hxZ⟩)⟩
    filter_upwards [hT.2 H hH hHR] with j hj x hx hxn
    have hxs := hCc hx.1
    rw [zeroExtension_apply a ⟨x, hxs⟩, zeroExtension_apply (b j) ⟨x, hxs⟩]
    dsimp only [a, b]
    rw [truncation_chart_sum R f c w ⟨x, hxs⟩ (fun h => hxn (Or.inl h)),
      truncation_chart_sum (T j) f c w ⟨x, hxs⟩ (fun h => hxn (Or.inr h))]
    by_cases hxR : c.toFun x ∈ truncationSet R
    · have hxT := hj ⟨x, ⟨⟨hx.1, hxR⟩, hx.2⟩, rfl⟩
      rw [if_pos hxR, if_pos hxT]
    · have hxT : c.toFun x ∉ truncationSet (T j) := fun h => hxR (hT.1 j h)
      rw [if_neg hxR, if_neg hxT]
  have hconv := Riemann.proper_truncation_convergence a b hai.1 (fun j => (hbi j).1)
    C K hC hK hKz (hs R) (fun j => hs (T j)) N hN (max B 0) hB0 hbound hev
  dsimp only [a, b] at hconv
  simpa only [hai.2, (hbi _).2] using hconv

/-- A partition need only sum to one on the compact region being integrated. -/
lemma truncation_partition_on_region {n : ℕ} {M Z : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (T : SurfaceTruncation M Z)
    (f : M → ℝ) (hf : Continuous f) {K : Set M} (P : ChartPartition 1 2 M K)
    (hTK : ∀ x ∈ truncationSet T, ∀ hxM : x ∈ M, (⟨x, hxM⟩ : M) ∈ K) :
    truncationIntegral T f = ∑ j, ∑ i, pieceIntegral (T.piece i) (fun x => P.weight j x * f x) := by
  classical
  change (∑ i, pieceIntegral (T.piece i) f) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let p := T.piece i
  have ha := piece_own_chart hM p f hf (fun _ => 1) continuous_const
  have hb j := piece_own_chart hM p f hf (P.weight j) (P.partition.1 j).continuous
  have hsum := proper_sum (fun j => pieceChartCoefficient p f p.chart (P.weight j))
    (fun j => (hb j).1)
  have he := proper_integral_eq_off_null ha.1 hsum.1 D04.ExceptionalSets.null_empty (by
    intro x _
    by_cases hx : x ∈ p.chart.source
    · rw [zeroExtension_apply _ ⟨x, hx⟩, zeroExtension_apply _ ⟨x, hx⟩]
      by_cases hI : p.chart.toFun x ∈ pieceImage p
      · have hK := hTK _ (mem_iUnion.mpr ⟨i, hI⟩) (p.chart.map_source hx).1
        obtain ⟨V, _, hV, hp⟩ := P.partition.2.2.2.1
        have hp' := hp (chartPoint p.chart ⟨x, hx⟩) (hV hK)
        change ∑ j, P.weight j (p.chart.toFun x) = 1 at hp'
        simp only [pieceChartCoefficient, hI, ite_true, one_mul]
        rw [← Finset.sum_mul, hp', one_mul]
      · simp [pieceChartCoefficient, hI]
    · rw [zeroExtension_of_not_mem _ hx, zeroExtension_of_not_mem _ hx])
  have hav : coefficientIntegral (pieceChartCoefficient p f p.chart (fun _ => 1)) = pieceIntegral p f := by
    simpa only [one_mul] using ha.2.2
  rw [← hav, he, hsum.2]
  exact Finset.sum_congr rfl (fun j _ => (hb j).2.2)

theorem compact_portion_seam_convergence :
    Specs.D04.C10.NegligibleSeams.compact_portion_seam_convergenceType := by
  intro n M Z hM hZ hZM R f hf T hT
  have hRM : truncationSet R ⊆ M := by
    rintro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (R.avoids i hi).1
  have hRK : IsCompact (Subtype.val ⁻¹' truncationSet R : Set M) :=
    (IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
      (by simpa only [Subtype.range_coe] using hRM)).mpr (truncationSet_compact R)
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM _ hRK
  obtain ⟨hZK, hZa⟩ := finite_seam_areaNull hM hZ hZM
  rw [truncation_partition_on_region hM R f hf P (fun _ hx _ => hx)]
  have hconv := tendsto_finsetSum Finset.univ (fun i _ => chart_portion_truncation_convergence
    hM hZK hZa R f hf T hT (P.chart i) (P.weight i) (P.partition.1 i).continuous
      (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2)
  have he (j : ℕ) := truncation_partition_on_region hM (T j) f hf P
    (fun _ hx _ => hT.1 j hx)
  simpa only [← he] using hconv

theorem compact_portion_flux_convergence :
    Specs.D04.C10.NegligibleSeams.compact_portion_flux_convergenceType := by
  intro M Z hM hZ hZM R N F hF T hT
  exact compact_portion_seam_convergence hM hZ hZM R _ (hF.inner N.continuous) T hT


lemma chart_portion_error_bound {n : ℕ} {M Z : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (R : SurfaceTruncation M ∅) (T : SurfaceTruncation M Z)
    (hTR : truncationSet T ⊆ truncationSet R)
    (f : M → ℝ) (hf : Continuous f) (B : ℝ)
    (hbound : ∀ x : M, (x : E n) ∈ truncationSet R → |f x| ≤ B)
    (c : EmbeddedChart 1 2 n M) (w : E n → ℝ) (hw : Continuous w)
    (hw0 : ∀ x : M, 0 ≤ w x)
    (hwK : IsCompact (tsupport (fun x : M => w x)))
    (hwc : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    |(∑ i, pieceIntegral (R.piece i) (fun x => w x * f x)) -
      ∑ i, pieceIntegral (T.piece i) (fun x => w x * f x)| ≤
    B * ((∑ i, pieceIntegral (R.piece i) (fun x => w x * 1)) -
      ∑ i, pieceIntegral (T.piece i) (fun x => w x * 1)) := by
  classical
  have hR (g : M → ℝ) (hg : Continuous g) := truncation_chart_integral hM R g hg c w hw hwK hwc
  have hT (g : M → ℝ) (hg : Continuous g) := truncation_chart_integral hM T g hg c w hw hwK hwc
  rw [← (hR f hf).2, ← (hT f hf).2,
    ← (hR (fun _ => 1) continuous_const).2, ← (hT (fun _ => 1) continuous_const).2]
  apply Riemann.coefficient_difference_bound _ _ _ _ (hR f hf).1 (hT f hf).1
    (hR (fun _ => 1) continuous_const).1 (hT (fun _ => 1) continuous_const).1
    (overlapException R c ∪ overlapException T c)
    (D04.JordanRegions.null_union (overlapException_null R c) (overlapException_null T c)) B
  intro x hx
  by_cases hxs : x ∈ c.source
  · simp only [zeroExtension_apply _ ⟨x, hxs⟩]
    rw [truncation_chart_sum R f c w ⟨x, hxs⟩ (fun h => hx (Or.inl h)),
      truncation_chart_sum T f c w ⟨x, hxs⟩ (fun h => hx (Or.inr h)),
      truncation_chart_sum R (fun _ => 1) c w ⟨x, hxs⟩ (fun h => hx (Or.inl h)),
      truncation_chart_sum T (fun _ => 1) c w ⟨x, hxs⟩ (fun h => hx (Or.inr h))]
    by_cases ht : c.toFun x ∈ truncationSet T
    · rw [if_pos ht, if_pos (hTR ht), if_pos ht, if_pos (hTR ht)]
      simp only [sub_self, abs_zero, mul_zero, le_refl]
    · rw [if_neg ht, if_neg ht]
      by_cases hr : c.toFun x ∈ truncationSet R
      · rw [if_pos hr, if_pos hr]
        dsimp only [localizedDensityCoefficient, densityCoefficient]
        simp only [sub_zero, one_mul]
        have hwx : 0 ≤ w (c.toFun x) := hw0 (chartPoint c ⟨x, hxs⟩)
        have hJ : 0 ≤ Specs.D04.C14.MetricTopFormsAndDensities.Model.chartDensity c x :=
          (D04MetricDensity.chartDensity_positive c hM.1 x hxs).le
        rw [abs_mul, abs_mul, abs_of_nonneg hwx, abs_of_nonneg hJ]
        nlinarith [mul_le_mul_of_nonneg_left (hbound (chartPoint c ⟨x, hxs⟩) hr)
          (mul_nonneg hwx hJ)]
      · rw [if_neg hr, if_neg hr]
        simp
  · simp only [zeroExtension_of_not_mem _ hxs, sub_self, abs_zero, mul_zero, le_refl]

theorem compact_portion_error_bound :
    Specs.D04.C10.NegligibleSeams.compact_portion_error_boundType := by
  intro n M Z hM R T hTR f hf B _ hbound
  have hRM : truncationSet R ⊆ M := by
    rintro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (R.avoids i hi).1
  have hRK : IsCompact (Subtype.val ⁻¹' truncationSet R : Set M) :=
    (IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
      (by simpa only [Subtype.range_coe] using hRM)).mpr (truncationSet_compact R)
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM _ hRK
  rw [truncation_partition_on_region hM R f hf P (fun _ hx _ => hx),
    truncation_partition_on_region hM T f hf P (fun _ hx _ => hTR hx),
    truncation_partition_on_region hM R (fun _ => 1) continuous_const P (fun _ hx _ => hx),
    truncation_partition_on_region hM T (fun _ => 1) continuous_const P (fun _ hx _ => hTR hx),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(∑ j, pieceIntegral (R.piece j) (fun x => P.weight i x * f x)) -
      ∑ j, pieceIntegral (T.piece j) (fun x => P.weight i x * f x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, B * ((∑ j, pieceIntegral (R.piece j) (fun x => P.weight i x * 1)) -
      ∑ j, pieceIntegral (T.piece j) (fun x => P.weight i x * 1)) := by
        apply Finset.sum_le_sum
        intro i _
        exact chart_portion_error_bound hM R T hTR f hf B hbound (P.chart i) (P.weight i)
          (P.partition.1 i).continuous (P.partition.2.1 i)
          (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]


theorem compact_chart_seam_integral_zero :
    Specs.D04.C10.NegligibleSeams.compact_chart_seam_integral_zeroType := by
  intro n M Z hM hZ hZM c K hK hKc f hf
  let S := K ∩ c.toFun ⁻¹' Z
  have hS : IsCompact S := hK.of_isClosed_subset
    ((c.continuous_toFun.mono hKc).preimage_isClosed_of_isClosed hK.isClosed
      (finiteSeam_compact hZ).isClosed) inter_subset_left
  let q := seamRestrictionCoefficient c K (c.toFun ⁻¹' Z) hKc f
  have hq : Continuous q :=
    (D04.ManifoldIntegralIndependence.densityCoefficient_continuous hM f hf c).comp
      (continuous_subtype_val.subtype_mk (fun u : S => hKc u.property.1))
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hq.continuousOn
  have hqb : RegionBounded q := ⟨B, fun x => hB x (mem_univ _)⟩
  obtain ⟨Q, hQ⟩ := (D04.JordanRegions.encloses_exists_iff_bounded S).mpr hS.isBounded
  obtain ⟨hi, hv⟩ := D04.ExceptionalSets.zero_off_contentZero (by norm_num : 0 < 2)
    (D04.JordanRegions.zeroExtension_bounded q hqb Q)
    (compact_chart_seam_contentZero hM hZ hZM c K hK hKc)
    (fun x _ hx => zeroExtension_of_not_mem q hx)
  have hqi : RegionIntegrable q := ⟨hqb, Q, hQ, hi⟩
  exact ⟨hqi, (D04.JordanRegions.integral_eq_on_enclosing_box q hqi hQ hi).trans hv⟩

theorem compact_portion_small_area_neighborhoods :
    Specs.D04.C10.NegligibleSeams.compact_portion_small_area_neighborhoodsType := by
  intro n M Z hM hZ hZM R T hT ε hε
  have hconv := compact_portion_seam_convergence hM hZ hZM R (fun _ => 1) continuous_const T hT
  obtain ⟨j, hj⟩ := ((Metric.tendsto_nhds.mp hconv) ε hε).exists
  refine ⟨j, ?_, ?_, ?_, ?_, fun f hf B hB hb =>
    compact_portion_error_bound hM R (T j) (hT.1 j) f hf B hB hb⟩
  · exact (truncationSet_compact (T j)).isClosed.isOpen_compl.preimage continuous_subtype_val
  · intro x hx
    refine ⟨hx.2, ?_⟩
    intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ((T j).avoids i hi).2 hx.1
  · have hh := compact_portion_error_bound hM R (T j) (hT.1 j) (fun _ => 0) continuous_const 1
      (by norm_num) (by simp)
    exact (abs_nonneg _).trans (by simpa only [one_mul] using hh)
  · have hh : |truncationIntegral R (fun _ => 1) - truncationIntegral (T j) (fun _ => 1)| < ε := by
      simpa only [Real.dist_eq, abs_sub_comm] using hj
    exact (le_abs_self _).trans_lt hh

end D04.NegligibleSeams
