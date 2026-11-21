import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.SlicingAndMoments
import MathGenome.Internal.MultivariableAnalysis.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.D04.C06.DarbouxFubini
import MathGenome.Internal.MultivariableAnalysis.D04.C01.DistanceFunction
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CompactContinuity

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology
open scoped BigOperators ENNReal
namespace D04.SlicingAndMoments
open Darboux JordanRegions NullCovers

abbrev basePoint := @Specs.D04.C06.SlicingAndMoments.Model.basePoint
abbrev height := @Specs.D04.C06.SlicingAndMoments.Model.height
abbrev stackPoint := @Specs.D04.C06.SlicingAndMoments.Model.stackPoint
abbrev graph := @Specs.D04.C06.SlicingAndMoments.Model.graph
abbrev cylinder := @Specs.D04.C06.SlicingAndMoments.Model.cylinder
abbrev between := @Specs.D04.C06.SlicingAndMoments.Model.between
abbrev sliceBox := @Specs.D04.C06.SlicingAndMoments.Model.sliceBox
abbrev sliceIntegral := @Specs.D04.C06.SlicingAndMoments.Model.sliceIntegral
abbrev closureExtension := @Specs.D04.C06.SlicingAndMoments.Model.closureExtension
abbrev mass := @Specs.D04.C06.SlicingAndMoments.Model.mass
abbrev firstMoment := @Specs.D04.C06.SlicingAndMoments.Model.firstMoment
abbrev center := @Specs.D04.C06.SlicingAndMoments.Model.center
abbrev inertia := @Specs.D04.C06.SlicingAndMoments.Model.inertia

variable {n : ℕ} {S : Set (E n)}

lemma zeroExtension_weight (ρ : S → ℝ) (w : E n → ℝ) :
    zeroExtension (fun x => w x * ρ x) = fun x => w x * zeroExtension ρ x := by
  funext x
  by_cases hx : x ∈ S
  · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]
  · simp [zeroExtension_of_not_mem _ hx]

lemma continuous_box_integrable (w : E n → ℝ) (hw : Continuous w) (Q : Box n) :
    Integrable w Q := by
  cases n with
  | zero => exact (Darboux.zero_dimension Q w).2.1
  | succ n => exact ExceptionalSets.integrable_continuous (Nat.succ_pos _) Q w hw.continuousOn

lemma weighted_integrable (hb : Bornology.IsBounded S) (ρ : S → ℝ)
    (hρ : RegionIntegrable ρ) (w : E n → ℝ) (hw : Continuous w) :
    RegionIntegrable (fun x => w x * ρ x) := by
  have hQ := enclosingBox_encloses hb
  apply (region_integrable_iff_box _ hQ).mpr
  rw [zeroExtension_weight]
  exact integrable_mul (continuous_box_integrable w hw _) ((region_integrable_iff_box _ hQ).mp hρ)

lemma region_nonneg (hb : Bornology.IsBounded S) (f : S → ℝ)
    (hf : RegionIntegrable f) (hn : ∀ x, 0 ≤ f x) : 0 ≤ regionIntegral f := by
  have hQ := enclosingBox_encloses hb
  have hi := (region_integrable_iff_box _ hQ).mp hf
  rw [integral_eq_on_enclosing_box _ hf hQ hi]
  have hle := integral_mono (integrable_const (enclosingBox S) 0) hi (by
    intro x _
    by_cases hx : x ∈ S
    · simpa [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx] using hn ⟨x, hx⟩
    · simp [zeroExtension_of_not_mem _ hx])
  simpa [integral_const] using hle

lemma zeroExtension_smul (f : S → ℝ) (c : ℝ) :
    zeroExtension (fun x => c * f x) = fun x => c * zeroExtension f x := by
  simpa using zeroExtension_weight f (fun _ => c)

lemma zeroExtension_sub (f g : S → ℝ) :
    zeroExtension (fun x => f x - g x) = fun x => zeroExtension f x - zeroExtension g x := by
  funext x
  by_cases hx : x ∈ S
  · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]
  · simp [zeroExtension_of_not_mem _ hx]

lemma region_smul (hb : Bornology.IsBounded S) (f : S → ℝ)
    (hf : RegionIntegrable f) (c : ℝ) :
    RegionIntegrable (fun x => c * f x) ∧
    regionIntegral (fun x => c * f x) = c * regionIntegral f := by
  have hQ := enclosingBox_encloses hb
  have hi := (region_integrable_iff_box _ hQ).mp hf
  have he := zeroExtension_smul f c
  have hh : Integrable (zeroExtension (fun x => c * f x)) (enclosingBox S) := by
    rw [he]; exact integrable_smul c hi
  refine ⟨(region_integrable_iff_box _ hQ).mpr hh, ?_⟩
  change lowerIntegral (zeroExtension (fun x => c * f x)) (enclosingBox S) =
    c * lowerIntegral (zeroExtension f) (enclosingBox S)
  rw [he]
  exact integral_smul c hi (integrable_smul c hi)

lemma region_sub (hb : Bornology.IsBounded S) (f g : S → ℝ)
    (hf : RegionIntegrable f) (hg : RegionIntegrable g) :
    RegionIntegrable (fun x => f x - g x) ∧
    regionIntegral (fun x => f x - g x) = regionIntegral f - regionIntegral g := by
  have hQ := enclosingBox_encloses hb
  have hfi := (region_integrable_iff_box _ hQ).mp hf
  have hgi := (region_integrable_iff_box _ hQ).mp hg
  have he := zeroExtension_sub f g
  have hh : Integrable (zeroExtension (fun x => f x - g x)) (enclosingBox S) := by
    rw [he]; exact integrable_sub hfi hgi
  refine ⟨(region_integrable_iff_box _ hQ).mpr hh, ?_⟩
  change lowerIntegral (zeroExtension (fun x => f x-g x)) (enclosingBox S) =
    lowerIntegral (zeroExtension f) (enclosingBox S) - lowerIntegral (zeroExtension g) (enclosingBox S)
  rw [he]
  exact integral_sub hfi hgi (integrable_sub hfi hgi)

lemma distance_weight_continuous (L : AffineSubspace ℝ (E n))
    (hL : (L : Set (E n)).Nonempty) :
    Continuous (fun x => (distanceToSet (L : Set (E n)) hL (x : E n))^2) := by
  have he : distanceToSet (L : Set (E n)) hL = fun x => Metric.infDist x L := by
    funext x; exact distanceToSet_eq_infDist (L : Set (E n)) hL x
  rw [he]
  exact (Metric.continuous_infDist_pt (L : Set (E n))).pow 2

lemma moments_exist (hS : Jordan S) (ρ : S → ℝ) (hρ : RegionIntegrable ρ)
    (hpos : ∀ x, 0 ≤ ρ x) :
    0 ≤ mass ρ ∧
    (∀ i : Fin n, RegionIntegrable (fun x => (x : E n) i * ρ x)) ∧
    (∀ (L : AffineSubspace ℝ (E n)) (hL : (L : Set (E n)).Nonempty),
      RegionIntegrable (fun x => (distanceToSet (L : Set (E n)) hL (x : E n))^2 * ρ x) ∧ 0 ≤ inertia ρ L hL) := by
  have hb := jordan_bounded hS
  refine ⟨region_nonneg hb ρ hρ hpos, ?_, ?_⟩
  · intro i
    exact weighted_integrable hb ρ hρ _ (PiLp.continuous_apply 2 _ i)
  · intro L hL
    have hi := weighted_integrable hb ρ hρ _ (distance_weight_continuous L hL)
    exact ⟨hi, region_nonneg hb _ hi (fun x => mul_nonneg (sq_nonneg _) (hpos x))⟩

lemma centered_moment (hS : Jordan S) (ρ : S → ℝ) (hρ : RegionIntegrable ρ)
    (_hpos : ∀ x, 0 ≤ ρ x) (hm : 0 < mass ρ) (i : Fin n) :
    RegionIntegrable (fun x => ((x : E n) i - center ρ i) * ρ x) ∧
    regionIntegral (fun x => ((x : E n) i - center ρ i) * ρ x) = 0 := by
  have hb := jordan_bounded hS
  have hmi := weighted_integrable hb ρ hρ (fun x => x i) (PiLp.continuous_apply 2 _ i)
  have hc := region_smul hb ρ hρ (center ρ i)
  have hs := region_sub hb _ _ hmi hc.1
  have he : (fun x : S => ((x : E n) i - center ρ i) * ρ x) =
      (fun x : S => (x : E n) i * ρ x - center ρ i * ρ x) := by
    funext x; ring
  rw [he]
  refine ⟨hs.1, ?_⟩
  rw [hs.2, hc.2]
  change firstMoment ρ i - (firstMoment ρ i / mass ρ) * mass ρ = 0
  rw [div_mul_cancel₀ _ (ne_of_gt hm), sub_self]

lemma base_zero_evaluation (A : Set (E 0)) (g : A → ℝ) :
    RegionIntegrable g ∧ regionIntegral g =
      (if h : (0 : E 0) ∈ A then g ⟨0, h⟩ else 0) := (JordanRegions.zero_dimension A).2.2 g



variable {p : ℕ}

@[simp] lemma basePoint_stackPoint (x : E p) (t : ℝ) :
    basePoint (stackPoint x t) = x := by
  ext i
  exact Fubini.blockPoint_left finSumFinEquiv x (scalarPoint t) i

@[simp] lemma height_stackPoint (x : E p) (t : ℝ) :
    height (stackPoint x t) = t := by
  exact Fubini.blockPoint_right finSumFinEquiv x (scalarPoint t) 0

@[simp] lemma stackPoint_base_height (z : E (p+1)) :
    stackPoint (basePoint z) (height z) = z := by
  ext i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j => exact Fubini.blockPoint_left finSumFinEquiv _ _ j
  | inr j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact Fubini.blockPoint_right finSumFinEquiv _ _ 0

lemma stackPoint_mem_productBox (x : E p) (t : ℝ) (Q : Box p)
    (l u : ℝ) (hlu : l ≤ u) :
    stackPoint x t ∈ carrier (productBox Q (intervalBox l u hlu)) ↔
      x ∈ carrier Q ∧ t ∈ Icc l u := by
  have h := Fubini.blockPoint_mem (p := p) (q := 1) finSumFinEquiv
    (A := Q) (B := intervalBox l u hlu) (x := x) (y := scalarPoint t)
  change (stackPoint x t ∈ carrier (productBox Q (intervalBox l u hlu))) ↔
    x ∈ carrier Q ∧ scalarPoint t ∈ carrier (intervalBox l u hlu) at h
  exact h.trans (and_congr_right (fun _ =>
    ⟨fun ht => ht 0, fun ht i => ht⟩))

lemma productBox_mem_iff (z : E (p+1)) (Q : Box p) (l u : ℝ) (hlu : l ≤ u) :
    z ∈ carrier (productBox Q (intervalBox l u hlu)) ↔
      basePoint z ∈ carrier Q ∧ height z ∈ Icc l u := by
  simpa using stackPoint_mem_productBox (basePoint z) (height z) Q l u hlu

lemma intervalBox_content (l u : ℝ) (hlu : l ≤ u) :
    content (intervalBox l u hlu) = u-l := by
  simp [content, Specs.D04.C06.DarbouxIntegral.Model.content,
    intervalBox, Specs.D04.C06.DarbouxIntegral.Model.intervalBox,
    scalarPoint, Specs.D04.C06.DarbouxIntegral.Model.scalarPoint]

lemma content_productBox {q : ℕ} (Q : Box p) (B : Box q) :
    content (productBox Q B) = content Q * content B := productBox_content Q B

lemma cylinder_contentZero (K : Set (E p)) (l u : ℝ) (hK : ContentZero K) :
    ContentZero (cylinder K l u) := by
  classical
  by_cases hlu : l ≤ u
  · intro ε hε
    let C := u-l+1
    have hC : 0 < C := by dsimp [C]; linarith
    obtain ⟨ι, hι, Q, hcover, hsum⟩ := hK (ε/C) (div_pos hε hC)
    let := Fintype.ofFinite ι
    let R := fun i => productBox (Q i) (intervalBox l u hlu)
    refine ⟨ι, inferInstance, R, ?_, ?_⟩
    · intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz.1)
      exact mem_iUnion.mpr ⟨i, (productBox_mem_iff z (Q i) l u hlu).mpr ⟨hi, hz.2⟩⟩
    · have hs : (∑ i, content (Q i)) < ε/C := by
        rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
          (fun i _ => content_nonneg (Q i))] at hsum
        exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hε hC)).mp hsum
      rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => content_nonneg (R i))]
      apply ENNReal.ofReal_lt_ofReal_iff hε |>.mpr
      have he : (∑ i, content (R i)) = (∑ i, content (Q i)) * (u-l) := by
        simp only [R, content_productBox, intervalBox_content, Finset.sum_mul]
      rw [he]
      have hnon : 0 ≤ ∑ i, content (Q i) := Finset.sum_nonneg fun i _ => content_nonneg _
      calc
        _ ≤ (∑ i, content (Q i)) * C := mul_le_mul_of_nonneg_left (by dsimp [C]; linarith) hnon
        _ < ε := (lt_div_iff₀ hC).mp hs
  · apply contentZero_mono (T := (∅ : Set (E (p+1))))
      (fun z hz => False.elim (hlu (hz.2.1.trans hz.2.2)))
    intro ε hε
    exact ⟨Empty, inferInstance, Empty.elim, by simp, by simpa using ENNReal.ofReal_pos.mpr hε⟩

/-- Uniform continuity gives an explicit finite graph cover. The sum of the
base cell contents is bounded by one enclosing box, independently of mesh. -/
lemma graph_contentZero (K : Set (E p)) (a : E p → ℝ)
    (hK : IsCompact K) (ha : ContinuousOn a K) : ContentZero (graph K a) := by
  classical
  by_cases he : K.Nonempty
  swap
  · intro ε hε
    refine ⟨Empty, inferInstance, Empty.elim, ?_, ?_⟩
    · intro z hz; exact False.elim (he ⟨basePoint z, hz.1⟩)
    · simpa using ENNReal.ofReal_pos.mpr hε
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded K).mpr hK.isBounded
  obtain ⟨x, hx⟩ := he
  have hq : Nondegenerate Q := fun i =>
    ((encloses_open hQ (subset_closure hx) i).1).trans
      ((encloses_open hQ (subset_closure hx) i).2)
  intro ε hε
  let η := ε / (4 * (content Q + 1))
  have hη : 0 < η := div_pos hε (by positivity [content_nonneg Q])
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous ha) η hη
  obtain ⟨P, hP⟩ := fine_grid_exists Q δ hδ
  let J := {c : CellIndex P // (cell P c ∩ K).Nonempty}
  let pick : J → E p := fun c => Classical.choose c.property
  have hpick (c : J) : pick c ∈ cell P c.val ∩ K := Classical.choose_spec c.property
  let R : J → Box (p+1) := fun c => productBox (cellBox P c.val)
    (intervalBox (a (pick c)-η) (a (pick c)+η) (by linarith))
  refine ⟨J, inferInstance, R, ?_, ?_⟩
  · intro z hz
    have hbase := encloses_subset hQ hz.1
    obtain ⟨c, hc⟩ := mem_iUnion.mp (by rw [cells_cover Q hq P] at hbase; exact hbase)
    let j : J := ⟨c, ⟨basePoint z, hc, hz.1⟩⟩
    have hdist : dist (basePoint z) (pick j) < δ := by
      calc
        _ ≤ Metric.diam (cell P c) :=
          Metric.dist_le_diam_of_mem ((carrier_isBounded (cellBox P c))) hc (hpick j).1
        _ ≤ mesh P := cell_diam_le_mesh P c
        _ < δ := hP
    have hv := hcont _ hz.1 _ (hpick j).2 hdist
    rw [Real.dist_eq] at hv
    refine mem_iUnion.mpr ⟨j, ?_⟩
    apply (productBox_mem_iff z (cellBox P c) _ _ _).mpr
    refine ⟨hc, ?_⟩
    have hheight : height z = a (basePoint z) := hz.2
    rw [hheight]
    exact ⟨by linarith [(abs_lt.mp hv).1], by linarith [(abs_lt.mp hv).2]⟩
  · rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun c _ => content_nonneg (R c))]
    apply ENNReal.ofReal_lt_ofReal_iff hε |>.mpr
    have hsum : (∑ c : J, cellContent P c.val) ≤ content Q := by
      rw [← content_partition P]
      exact Finset.sum_le_sum_of_injOn (fun c : J => c.val)
        (fun _ _ _ _ h => Subtype.ext h) (fun _ _ => Finset.mem_univ _)
        (fun _ _ => le_rfl) (fun _ _ _ => cellContent_nonneg P _)
    have he : (∑ c, content (R c)) = (∑ c : J, cellContent P c.val) * (2*η) := by
      simp only [R, content_productBox, intervalBox_content]
      simp_rw [show ∀ t : ℝ, (t+η)-(t-η) = 2*η from fun t => by ring]
      rw [Finset.sum_mul]
      rfl
    rw [he]
    calc
      _ ≤ content Q * (2*η) := mul_le_mul_of_nonneg_right hsum (by positivity)
      _ < ε := by
        dsimp [η]
        have hc := content_nonneg Q
        have hden : 0 < 4 * (content Q+1) := by positivity
        rw [show content Q * (2 * (ε / (4 * (content Q+1)))) =
          (content Q * (2*ε)) / (4 * (content Q+1)) by ring]
        apply (div_lt_iff₀ hden).mpr
        nlinarith



lemma continuous_basePoint : Continuous (@basePoint p) := by
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => PiLp.continuous_apply 2 _ (Fin.castAdd 1 i)))
lemma continuous_height : Continuous (@height p) := PiLp.continuous_apply 2 _ (Fin.last p)
lemma continuous_stackPoint (x : E p) : Continuous (stackPoint x) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  dsimp only [Specs.D04.C06.DarbouxIntegral.Model.scalarPoint, WithLp.toLp_ofLp]
  cases finSumFinEquiv.symm i <;> fun_prop

lemma closure_between_subset (A : Set (E p)) (a b : E p → ℝ)
    (ha : ContinuousOn a (closure A)) (hb : ContinuousOn b (closure A)) :
    closure (between A a b) ⊆
      {z | basePoint z ∈ closure A ∧ a (basePoint z) ≤ height z ∧ height z ≤ b (basePoint z)} := by
  let C : Set (E (p+1)) := basePoint ⁻¹' closure A
  have hC : IsClosed C := isClosed_closure.preimage continuous_basePoint
  have hac : ContinuousOn (fun z : E (p+1) => a (basePoint z)) C :=
    ha.comp continuous_basePoint.continuousOn (fun _ h => h)
  have hbc : ContinuousOn (fun z : E (p+1) => b (basePoint z)) C :=
    hb.comp continuous_basePoint.continuousOn (fun _ h => h)
  have hclosed : IsClosed {z : E (p+1) | basePoint z ∈ closure A ∧
      a (basePoint z) ≤ height z ∧ height z ≤ b (basePoint z)} := by
    convert (hC.isClosed_le hac continuous_height.continuousOn).inter
      (hC.isClosed_le continuous_height.continuousOn hbc) using 1
    ext z; simp only [C, mem_preimage, mem_inter_iff, mem_ofPred_eq]; tauto
  apply closure_minimal _ hclosed
  intro z hz
  exact ⟨subset_closure hz.1, hz.2⟩

lemma between_boundary (A : Set (E p)) (a b : E p → ℝ)
    (ha : ContinuousOn a (closure A)) (hb : ContinuousOn b (closure A))
    (_hab : ∀ x ∈ closure A, a x ≤ b x) (l u : ℝ)
    (hlu : ∀ x ∈ closure A, l ≤ a x ∧ b x ≤ u) :
    frontier (between A a b) ⊆
      cylinder (frontier A) l u ∪ graph (closure A) a ∪ graph (closure A) b := by
  intro z hz
  have hzC := closure_between_subset A a b ha hb hz.1
  by_cases hxa : basePoint z ∈ frontier A
  · exact Or.inl (Or.inl ⟨hxa, (hlu _ hzC.1).1.trans hzC.2.1,
      hzC.2.2.trans (hlu _ hzC.1).2⟩)
  by_cases hza : height z = a (basePoint z)
  · exact Or.inl (Or.inr ⟨hzC.1, hza⟩)
  by_cases hzb : height z = b (basePoint z)
  · exact Or.inr ⟨hzC.1, hzb⟩
  exfalso
  have hxi : basePoint z ∈ interior A := by
    by_contra h
    exact hxa ⟨hzC.1, h⟩
  have hAn : A ∈ 𝓝 (basePoint z) := mem_interior_iff_mem_nhds.mp hxi
  have hCn : closure A ∈ 𝓝 (basePoint z) := mem_of_superset hAn subset_closure
  have hac := (ha _ hzC.1).continuousAt hCn
  have hbc := (hb _ hzC.1).continuousAt hCn
  have hl := (hac.comp continuous_basePoint.continuousAt).eventually_lt
    continuous_height.continuousAt (lt_of_le_of_ne hzC.2.1 (Ne.symm hza))
  have hu := continuous_height.continuousAt.eventually_lt
    (hbc.comp continuous_basePoint.continuousAt) (lt_of_le_of_ne hzC.2.2 hzb)
  have hbase : ∀ᶠ w in 𝓝 z, basePoint w ∈ A := continuous_basePoint.continuousAt hAn
  have hm : between A a b ∈ 𝓝 z := by
    filter_upwards [hbase, hl, hu] with w hw hwl hwu
    exact ⟨hw, hwl.le, hwu.le⟩
  exact hz.2 (mem_interior_iff_mem_nhds.mpr hm)

lemma endpoint_bounds (A : Set (E p)) (hA : Bornology.IsBounded A) (a b : E p → ℝ)
    (ha : ContinuousOn a (closure A)) (hb : ContinuousOn b (closure A)) :
    ∃ R > 0, ∀ x ∈ closure A, -R < a x ∧ b x < R := by
  have hK := hA.isCompact_closure
  obtain ⟨R, hR, hbound⟩ := ((hK.image_of_continuousOn ha).union
    (hK.image_of_continuousOn hb)).isBounded.exists_pos_norm_lt
  refine ⟨R, hR, fun x hx => ?_⟩
  have haa := hbound _ (Or.inl ⟨x, hx, rfl⟩)
  have hbb := hbound _ (Or.inr ⟨x, hx, rfl⟩)
  exact ⟨(abs_lt.mp haa).1, (abs_lt.mp hbb).2⟩

lemma between_bounded (A : Set (E p)) (hA : Bornology.IsBounded A) (a b : E p → ℝ)
    (ha : ContinuousOn a (closure A)) (hb : ContinuousOn b (closure A)) :
    Bornology.IsBounded (between A a b) := by
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded A).mpr hA
  obtain ⟨R, hR, hbound⟩ := endpoint_bounds A hA a b ha hb
  apply (carrier_isBounded (productBox Q (intervalBox (-R) R (by linarith)))).subset
  intro z hz
  apply (productBox_mem_iff z Q (-R) R _).mpr
  exact ⟨encloses_subset hQ hz.1, ((hbound _ (subset_closure hz.1)).1.le.trans hz.2.1),
    hz.2.2.trans (hbound _ (subset_closure hz.1)).2.le⟩

lemma between_jordan (A : Set (E p)) (hA : Jordan A) (a b : E p → ℝ)
    (ha : ContinuousOn a (closure A)) (hb : ContinuousOn b (closure A))
    (hab : ∀ x ∈ closure A, a x ≤ b x) : Jordan (between A a b) := by
  have hbnd := between_bounded A (jordan_bounded hA) a b ha hb
  apply (jordan_iff_boundary (Nat.succ_pos _) _ hbnd).mpr
  obtain ⟨R, hR, hbound⟩ := endpoint_bounds A (jordan_bounded hA) a b ha hb
  have hfront : ContentZero (frontier A) := by
    cases p with
    | zero =>
      have he : frontier A = ∅ := by
        exact (show IsClopen A from ⟨isClosed_discrete _, isOpen_discrete _⟩).frontier_eq
      rw [he]
      intro ε hε
      exact ⟨Empty, inferInstance, Empty.elim, by simp, by simpa using ENNReal.ofReal_pos.mpr hε⟩
    | succ p => exact (jordan_iff_boundary (Nat.succ_pos _) A (jordan_bounded hA)).mp hA
  apply contentZero_mono (between_boundary A a b ha hb hab (-R) R
    (fun x hx => ⟨(hbound x hx).1.le, (hbound x hx).2.le⟩))
  exact contentZero_union
    (contentZero_union (cylinder_contentZero _ _ _ hfront)
      (graph_contentZero _ a (jordan_bounded hA).isCompact_closure ha))
    (graph_contentZero _ b (jordan_bounded hA).isCompact_closure hb)



lemma scalarPoint_coordinate (y : E 1) : scalarPoint (y 0) = y := by
  ext i; fin_cases i; rfl

/-- Extending an integrable interval function by zero to a larger interval
preserves its integral, including a collapsed inner interval. -/
lemma interval_cutoff (v : E 1 → ℝ) (l a b u : ℝ)
    (hla : l < a) (hab : a ≤ b) (hbu : b < u)
    (hi : Integrable v (intervalBox a b hab)) :
    let g : E 1 → ℝ := fun y => if y 0 ∈ Icc a b then v y else 0
    ∃ hg : Integrable g (intervalBox l u (by linarith)),
      integral g (intervalBox l u (by linarith)) hg = integral v (intervalBox a b hab) hi := by
  classical
  dsimp only
  let g : E 1 → ℝ := fun y => if y 0 ∈ Icc a b then v y else 0
  let I := intervalBox a b hab
  let B := intervalBox l u (show l ≤ u by linarith)
  obtain ⟨M, hM, hv⟩ := exists_abs_bound hi.1
  have hgb : Bounded g B := by
    apply bounded_of_abs_le (M := M)
    intro y _
    by_cases hy : y 0 ∈ Icc a b
    · simpa only [g, ite_eq_left hy] using hv y (fun i => by fin_cases i; exact hy)
    · simpa only [g, ite_eq_right hy, abs_zero] using hM
  have hmidEq : EqOn g v (carrier I) := by
    intro y hy; exact ite_eq_left (hy 0)
  have hgi := (integrable_congr hmidEq).mpr hi
  by_cases he : a = b
  · have hsingleton := singleton_contentZero (by decide : 0 < 1) (scalarPoint a)
    obtain ⟨hg, hval⟩ := ExceptionalSets.zero_off_contentZero (by decide : 0 < 1)
      hgb hsingleton (by
        intro y _ hy
        change (if y 0 ∈ Icc a b then v y else 0) = 0
        apply ite_eq_right
        intro h
        apply hy
        apply Set.mem_singleton_iff.mpr
        rw [← scalarPoint_coordinate y]
        congr 1
        exact le_antisymm (by simpa [← he] using h.2) h.1)
    refine ⟨hg, hval.trans ?_⟩
    exact ((degenerate_integrals v I ⟨0, he⟩).1).symm
  · have hab' : a < b := lt_of_le_of_ne hab he
    let P : Grid B := fun _ => threePartition l a b u hla hab' hbu
    let c₀ : CellIndex P := fun _ => (1 : Fin 3)
    have hmid : cellBox P c₀ = I := by apply Subdivision.box_ext <;> ext i <;> rfl
    let Z : Set (E 1) := {scalarPoint a} ∪ {scalarPoint b}
    have hZ : ContentZero Z := contentZero_union
      (singleton_contentZero (by decide) _) (singleton_contentZero (by decide) _)
    have hother (c : CellIndex P) (hc : c ≠ c₀) :
        ∃ hg : Integrable g (cellBox P c), integral g (cellBox P c) hg = 0 := by
      apply ExceptionalSets.zero_off_contentZero (by decide : 0 < 1)
        (bounded_cell g hgb P c) hZ
      intro y hy hyZ
      change (if y 0 ∈ Icc a b then v y else 0) = 0
      apply ite_eq_right
      intro hyab
      have hnotA : y 0 ≠ a := by
        intro h
        apply hyZ
        exact Or.inl (Set.mem_singleton_iff.mpr (by rw [← scalarPoint_coordinate y, h]))
      have hnotB : y 0 ≠ b := by
        intro h
        apply hyZ
        exact Or.inr (Set.mem_singleton_iff.mpr (by rw [← scalarPoint_coordinate y, h]))
      have hc0 : c 0 ≠ (1 : Fin 3) := by
        intro he
        apply hc
        funext i
        fin_cases i
        exact he
      have hy0 := hy 0
      change ![l, a, b, u] (c 0).castSucc ≤ y 0 ∧ y 0 ≤ ![l, a, b, u] (c 0).succ at hy0
      generalize hcc : c 0 = j at hy0 hc0
      fin_cases j
      · norm_num at hy0
        exact hnotA (le_antisymm hy0.2 hyab.1)
      · exact hc0 rfl
      · norm_num at hy0
        exact hnotB (le_antisymm hyab.2 hy0.1)
    have hcells (c : CellIndex P) : Integrable g (cellBox P c) := by
      by_cases hc : c = c₀
      · subst c; rwa [hmid]
      · exact (hother c hc).1
    have hg := (subdivision_integrable g B hgb P).mpr hcells
    refine ⟨hg, ?_⟩
    rw [subdivision_integral g B P hg hcells, Finset.sum_eq_single c₀]
    · change lowerIntegral g (cellBox P c₀) = lowerIntegral v I
      rw [hmid]
      exact lowerIntegral_congr hmidEq
    · intro c _ hc
      exact (hother c hc).2
    · simp



lemma product_encloses_between (A : Set (E p)) (a b : E p → ℝ) (Q : Box p)
    (hQ : Encloses A Q) (l u : ℝ) (hlu : l ≤ u)
    (ha : ContinuousOn a (closure A)) (hb : ContinuousOn b (closure A))
    (hbound : ∀ x ∈ closure A, l < a x ∧ b x < u) :
    Encloses (between A a b) (productBox Q (intervalBox l u hlu)) := by
  let T : Set (E (p+1)) := {z | basePoint z ∈ interior (carrier Q) ∧ height z ∈ Ioo l u}
  have hT : IsOpen T := (isOpen_interior.preimage continuous_basePoint).inter
    (isOpen_Ioo.preimage continuous_height)
  have hsub : T ⊆ carrier (productBox Q (intervalBox l u hlu)) := by
    intro z hz
    exact (productBox_mem_iff z Q l u hlu).mpr
      ⟨interior_subset hz.1, hz.2.1.le, hz.2.2.le⟩
  intro z hz
  apply interior_maximal hsub hT
  have hc := closure_between_subset A a b ha hb hz
  exact ⟨hQ hc.1, (hbound _ hc.1).1.trans_le hc.2.1,
    hc.2.2.trans_lt (hbound _ hc.1).2⟩

lemma slice_integrable (A : Set (E p)) (a b : E p → ℝ)
    (hab : ∀ x ∈ closure A, a x ≤ b x) (f : E (p+1) → ℝ)
    (hf : ContinuousOn f (closure (between A a b))) (x : E p) (hx : x ∈ A) :
    Integrable (fun y => f (productPoint x y)) (sliceBox a b x) := by
  have habx := hab x (subset_closure hx)
  have hbox : sliceBox a b x = intervalBox (a x) (b x) habx := by
    apply Subdivision.box_ext <;> ext i <;>
      simp [sliceBox, Specs.D04.C06.SlicingAndMoments.Model.sliceBox, min_eq_left habx, max_eq_right habx,
        intervalBox, Specs.D04.C06.DarbouxIntegral.Model.intervalBox]
  rw [hbox]
  apply ExceptionalSets.integrable_continuous (by decide : 0 < 1)
  have hmap : Continuous (fun y : E 1 => productPoint x y) := by
    convert (continuous_stackPoint x).comp (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0) using 1
    funext y
    exact congrArg (productPoint x) (scalarPoint_coordinate y).symm
  exact hf.comp hmap.continuousOn (by
    intro y hy
    apply subset_closure
    change basePoint (productPoint x y) ∈ A ∧
      a (basePoint (productPoint x y)) ≤ height (productPoint x y) ∧
      height (productPoint x y) ≤ b (basePoint (productPoint x y))
    have he : productPoint x y = stackPoint x (y 0) :=
      congrArg (productPoint x) (scalarPoint_coordinate y).symm
    rw [he, basePoint_stackPoint, height_stackPoint]
    exact ⟨hx, hy 0⟩)



lemma sliceBox_eq_interval (a b : E p → ℝ) (x : E p) (hab : a x ≤ b x) :
    sliceBox a b x = intervalBox (a x) (b x) hab := by
  apply Subdivision.box_ext <;> ext i <;>
    simp [sliceBox, Specs.D04.C06.SlicingAndMoments.Model.sliceBox, min_eq_left hab, max_eq_right hab,
      intervalBox, Specs.D04.C06.DarbouxIntegral.Model.intervalBox]

lemma productPoint_eq_stackPoint (x : E p) (y : E 1) :
    productPoint x y = stackPoint x (y 0) :=
  congrArg (productPoint x) (scalarPoint_coordinate y).symm

lemma mem_between_product (A : Set (E p)) (a b : E p → ℝ) (x : E p) (y : E 1) :
    productPoint x y ∈ between A a b ↔ x ∈ A ∧ y 0 ∈ Icc (a x) (b x) := by
  rw [productPoint_eq_stackPoint]
  change (basePoint (stackPoint x (y 0)) ∈ A ∧
    a (basePoint (stackPoint x (y 0))) ≤ height (stackPoint x (y 0)) ∧
    height (stackPoint x (y 0)) ≤ b (basePoint (stackPoint x (y 0)))) ↔ _
  rw [basePoint_stackPoint, height_stackPoint]
  rfl

lemma zeroExtension_between_slice (A : Set (E p)) (a b : E p → ℝ)
    (f : E (p+1) → ℝ) (x : E p) (y : E 1) :
    zeroExtension (fun z : between A a b => f z) (productPoint x y) =
      if x ∈ A ∧ y 0 ∈ Icc (a x) (b x) then f (productPoint x y) else 0 := by
  by_cases h : x ∈ A ∧ y 0 ∈ Icc (a x) (b x)
  · have hm := (mem_between_product A a b x y).mpr h
    simp only [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, dite_eq_left hm, ite_eq_left h]
  · have hm : productPoint x y ∉ between A a b := fun hm => h ((mem_between_product A a b x y).mp hm)
    simp only [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, dite_eq_right hm, ite_eq_right h]

lemma slicing (A : Set (E p)) (a b : E p → ℝ) (hA : Jordan A)
    (ha : ContinuousOn a (closure A)) (hb : ContinuousOn b (closure A))
    (hab : ∀ x ∈ closure A, a x ≤ b x) :
    Bornology.IsBounded (between A a b) ∧ Jordan (between A a b) ∧
    ∀ f : E (p+1) → ℝ, ContinuousOn f (closure (between A a b)) →
      RegionIntegrable (fun z : between A a b => f z) ∧
      (∀ x ∈ A, Integrable (fun y => f (productPoint x y)) (sliceBox a b x)) ∧
      RegionIntegrable (fun x : A => sliceIntegral a b f x) ∧
      regionIntegral (fun z : between A a b => f z) =
        regionIntegral (fun x : A => sliceIntegral a b f x) := by
  have hAb := jordan_bounded hA
  have hE := between_jordan A hA a b ha hb hab
  refine ⟨jordan_bounded hE, hE, ?_⟩
  intro f hf
  have hfi := integrable_continuous_on_closure (Nat.succ_pos _) hE
    (fun z : closure (between A a b) => f z)
    (continuousOn_iff_continuous_domRestrict.mp hf)
  have hs := slice_integrable A a b hab f hf
  refine ⟨hfi, hs, ?_⟩
  let Q := enclosingBox A
  have hQ : Encloses A Q := enclosingBox_encloses hAb
  obtain ⟨R, hR, hbound⟩ := endpoint_bounds A hAb a b ha hb
  let B := intervalBox (-R) R (show -R ≤ R by linarith)
  have hQE := product_encloses_between A a b Q hQ (-R) R (by linarith) ha hb hbound
  let F := zeroExtension (fun z : between A a b => f z)
  have hF : Integrable F (productBox Q B) := (region_integrable_iff_box _ hQE).mp hfi
  have hinner (x : E p) : ∃ hi : Integrable (fun y => F (productPoint x y)) B,
      integral (fun y => F (productPoint x y)) B hi =
        zeroExtension (fun x : A => sliceIntegral a b f x) x := by
    by_cases hx : x ∈ A
    · have habx := hab x (subset_closure hx)
      have hsx := hs x hx
      rw [sliceBox_eq_interval a b x habx] at hsx
      obtain ⟨hg, hv⟩ := interval_cutoff (fun y => f (productPoint x y)) (-R) (a x) (b x) R
        (hbound x (subset_closure hx)).1 habx (hbound x (subset_closure hx)).2 hsx
      have he : (fun y => F (productPoint x y)) =
          (fun y : E 1 => if y 0 ∈ Icc (a x) (b x) then f (productPoint x y) else 0) := by
        funext y
        exact (zeroExtension_between_slice A a b f x y).trans (by simp only [hx, true_and])
      have hi : Integrable (fun y => F (productPoint x y)) B := he ▸ hg
      refine ⟨hi, ?_⟩
      have heval : zeroExtension (fun x : A => sliceIntegral a b f x) x = sliceIntegral a b f x :=
        zeroExtension_apply _ ⟨x, hx⟩
      rw [heval]
      change lowerIntegral _ B = lowerIntegral _ (sliceBox a b x)
      rw [sliceBox_eq_interval a b x habx]
      exact (congrArg (fun g => lowerIntegral g B) he).trans hv
    · have he : EqOn (fun y => F (productPoint x y)) (fun _ => 0) (carrier B) := by
        intro y _
        exact (zeroExtension_between_slice A a b f x y).trans (by simp only [hx, false_and, ↓reduceIte])
      obtain ⟨hi, hv⟩ := integrable_eq_zero_on_box he
      exact ⟨hi, hv.trans (zeroExtension_of_not_mem _ hx).symm⟩
  obtain ⟨hout, hval⟩ := fubini_slices Q B F hF
    (fun x _ => (hinner x).1) (zeroExtension (fun x : A => sliceIntegral a b f x))
    (fun x _ => (hinner x).2.symm)
  have houter := (region_integrable_iff_box _ hQ).mpr hout
  refine ⟨houter, ?_⟩
  rw [integral_eq_on_enclosing_box _ hfi hQE hF,
    integral_eq_on_enclosing_box _ houter hQ hout]
  exact hval.symm



lemma between_subset_closed (A : Set (E p)) (a b : E p → ℝ) (il iu : Bool) :
    between A a b il iu ⊆ between A a b := by
  intro z hz
  refine ⟨hz.1, ?_, ?_⟩
  · cases il with
    | false => exact (show a (basePoint z) < height z from hz.2.1).le
    | true => exact hz.2.1
  · cases iu with
    | false => exact (show height z < b (basePoint z) from hz.2.2).le
    | true => exact hz.2.2

lemma between_same_off_graph (A : Set (E p)) (a b : E p → ℝ) (il iu : Bool)
    (z : E (p+1)) (hz : z ∉ graph (closure A) a ∪ graph (closure A) b) :
    z ∈ between A a b il iu ↔ z ∈ between A a b := by
  refine ⟨fun h => between_subset_closed A a b il iu h, fun h => ?_⟩
  have hza : height z ≠ a (basePoint z) := fun he => hz (Or.inl ⟨subset_closure h.1, he⟩)
  have hzb : height z ≠ b (basePoint z) := fun he => hz (Or.inr ⟨subset_closure h.1, he⟩)
  refine ⟨h.1, ?_, ?_⟩
  · cases il with
    | false => exact lt_of_le_of_ne h.2.1 (Ne.symm hza)
    | true => exact h.2.1
  · cases iu with
    | false => exact lt_of_le_of_ne h.2.2 hzb
    | true => exact h.2.2

lemma endpoints (A : Set (E p)) (a b : E p → ℝ) (hA : Jordan A)
    (ha : ContinuousOn a (closure A)) (hb : ContinuousOn b (closure A))
    (hab : ∀ x ∈ closure A, a x ≤ b x) (il iu : Bool) :
    Jordan (between A a b il iu) ∧
    ∀ f : E (p+1) → ℝ, ContinuousOn f (closure (between A a b)) →
      RegionIntegrable (fun z : between A a b il iu => f z) ∧
      regionIntegral (fun z : between A a b il iu => f z) =
        regionIntegral (fun z : between A a b => f z) := by
  classical
  let E₀ := between A a b
  let T := between A a b il iu
  have hE : Jordan E₀ := between_jordan A hA a b ha hb hab
  have hsub : T ⊆ E₀ := between_subset_closed A a b il iu
  let Q := enclosingBox E₀
  have hQ : Encloses E₀ Q := enclosingBox_encloses (jordan_bounded hE)
  have hQT : Encloses T Q := (closure_mono hsub).trans hQ
  let Z := graph (closure A) a ∪ graph (closure A) b
  have hZ : ContentZero Z := contentZero_union
    (graph_contentZero _ a (jordan_bounded hA).isCompact_closure ha)
    (graph_contentZero _ b (jordan_bounded hA).isCompact_closure hb)
  have hsame (z : E (p+1)) (hz : z ∉ Z) : z ∈ T ↔ z ∈ E₀ :=
    between_same_off_graph A a b il iu z hz
  have hind : ∀ z ∈ carrier Q, z ∉ Z → indicator E₀ z = indicator T z := by
    intro z _ hz
    simp only [JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, Set.indicator]
    rw [hsame z hz]
  obtain ⟨hTi, _⟩ := ExceptionalSets.modification_contentZero (Nat.succ_pos _)
    (jordan_integrable_on_box hE hQ) (indicator_bounded T Q) hZ hind
  refine ⟨⟨Q, hQT, hTi⟩, ?_⟩
  intro f hf
  have hfi := (slicing A a b hA ha hb hab).2.2 f hf |>.1
  have hfb := (region_integrable_iff_box _ hQ).mp hfi
  have hbT : RegionBounded (fun z : T => f z) := by
    obtain ⟨M, hM⟩ := hfi.1
    exact ⟨M, fun z => hM ⟨z, hsub z.property⟩⟩
  have heq : ∀ z ∈ carrier Q, z ∉ Z →
      zeroExtension (fun z : E₀ => f z) z = zeroExtension (fun z : T => f z) z := by
    intro z _ hz
    simp only [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension]
    by_cases he : z ∈ E₀
    · have ht := (hsame z hz).mpr he
      simp only [dite_eq_left he, dite_eq_left ht]
    · have ht : z ∉ T := fun ht => he ((hsame z hz).mp ht)
      simp only [dite_eq_right he, dite_eq_right ht]
  obtain ⟨hft, hval⟩ := ExceptionalSets.modification_contentZero (Nat.succ_pos _)
    hfb (zeroExtension_bounded _ hbT Q) hZ heq
  have hri := (region_integrable_iff_box _ hQT).mpr hft
  refine ⟨hri, ?_⟩
  rw [integral_eq_on_enclosing_box _ hri hQT hft, integral_eq_on_enclosing_box _ hfi hQ hfb]
  exact hval

lemma between_volume (A : Set (E p)) (a b : E p → ℝ) (hA : Jordan A)
    (ha : ContinuousOn a (closure A)) (hb : ContinuousOn b (closure A))
    (hab : ∀ x ∈ closure A, a x ≤ b x) :
    RegionIntegrable (fun x : A => b x - a x) ∧
    volume (between A a b) = regionIntegral (fun x : A => b x - a x) := by
  obtain ⟨_, _, hi, hval⟩ := (slicing A a b hA ha hb hab).2.2 (fun _ => 1) continuousOn_const
  have he : (fun x : A => sliceIntegral a b (fun _ => 1) x) = (fun x : A => b x-a x) := by
    funext x
    change lowerIntegral (fun _ => 1) (sliceBox a b x) = _
    rw [sliceBox_eq_interval a b x (hab x (subset_closure x.property))]
    exact (constant_integrals _ 1).1.trans (by rw [one_mul, intervalBox_content])
  rw [he] at hi hval
  exact ⟨hi, (regionIntegral_one _).symm.trans hval⟩

lemma closureExtension_property {S : Set (E n)} (f : closure S → ℝ) :
    (∀ x : closure S, closureExtension f x = f x) ∧
    (Continuous f → ContinuousOn (closureExtension f) (closure S)) := by
  have he (x : closure S) : closureExtension f x = f x := by
    simp only [closureExtension, Specs.D04.C06.SlicingAndMoments.Model.closureExtension,
      dite_eq_left x.property]
  refine ⟨he, fun hf => ?_⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hf using 1
  funext x
  exact he x

/-- The source's original subtype functions on closures are covered without
any ambient extension hypothesis. -/
lemma slicing_closure_data (A : Set (E p)) (hA : Jordan A) (a b : closure A → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ x, a x ≤ b x) :
    let E₀ := between A (closureExtension a) (closureExtension b)
    Bornology.IsBounded E₀ ∧ Jordan E₀ ∧
    ∀ f : closure E₀ → ℝ, Continuous f →
      RegionIntegrable (fun z : E₀ => f ⟨z, subset_closure z.property⟩) ∧
      (∀ x ∈ A, Integrable (fun y => closureExtension f (productPoint x y))
        (sliceBox (closureExtension a) (closureExtension b) x)) ∧
      RegionIntegrable (fun x : A => sliceIntegral (closureExtension a) (closureExtension b)
        (closureExtension f) x) ∧
      regionIntegral (fun z : E₀ => f ⟨z, subset_closure z.property⟩) =
        regionIntegral (fun x : A => sliceIntegral (closureExtension a) (closureExtension b)
          (closureExtension f) x) := by
  have hs := slicing A (closureExtension a) (closureExtension b) hA
    ((closureExtension_property a).2 ha) ((closureExtension_property b).2 hb) (by
      intro x hx
      simpa only [(closureExtension_property a).1 ⟨x, hx⟩,
        (closureExtension_property b).1 ⟨x, hx⟩] using hab ⟨x, hx⟩)
  refine ⟨hs.1, hs.2.1, fun f hf => ?_⟩
  have hh := hs.2.2 (closureExtension f) ((closureExtension_property f).2 hf)
  have he : (fun z : between A (closureExtension a) (closureExtension b) => closureExtension f z) =
      (fun z : between A (closureExtension a) (closureExtension b) => f ⟨z, subset_closure z.property⟩) := by
    funext z
    exact (closureExtension_property f).1 ⟨z, subset_closure z.property⟩
  rwa [he] at hh

end D04.SlicingAndMoments
