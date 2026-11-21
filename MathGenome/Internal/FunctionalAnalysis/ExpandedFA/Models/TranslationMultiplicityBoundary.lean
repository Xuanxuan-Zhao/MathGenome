import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.TranslationMultiplicityBoundary
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.FullTranslationModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.TranslationMultiplicityWarning
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.MultiplicityUniqueness
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.GDelta.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ExpandedFA.Models.TranslationMultiplicityBoundary
open FullTranslationModel
open ExpandedFA.Unbounded
open ExpandedFA.Unbounded.MeasurableSpectralCalculus
open ExpandedFA.VonNeumann.MultiplicityModel.Spec
universe u

/-- A positive-measure compact nowhere dense subset of any nonempty real open set.
Outer regularity covers the rationals by an open set smaller than an interior
interval; inner regularity supplies a compact subset of the remainder. -/
theorem exists_compact_nowhere_dense {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ K : Set ℝ, K ⊆ U ∧ IsCompact K ∧ IsNowhereDense K ∧ 0 < volume K := by
  obtain ⟨a, b, hab, hsub⟩ := hU.exists_Ioo_subset hne
  have hpos : 0 < volume (Ioo a b) := isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hab)
  have hnull : volume (range (fun q : ℚ => (q : ℝ))) = 0 :=
    (countable_range _).measure_zero volume
  obtain ⟨G, hQG, hG, hvol⟩ :=
    (range (fun q : ℚ => (q : ℝ))).exists_isOpen_lt_of_lt (μ := volume)
      (volume (Ioo a b)) (by rw [hnull]; exact hpos)
  have hdense : Dense G := Rat.denseRange_cast.mono hQG
  have hrem : 0 < volume (Ioo a b \ G) := by
    by_contra h
    have hz : volume (Ioo a b \ G) = 0 := le_antisymm (le_of_not_gt h) bot_le
    have hle : volume (Ioo a b) ≤ volume G := by
      calc
        volume (Ioo a b) ≤ volume G + volume (Ioo a b \ G) :=
          measure_mono le_sup_sdiff |>.trans (measure_union_le _ _)
        _ = volume G := by rw [hz, add_zero]
    exact hvol.not_ge hle
  obtain ⟨K, hKsub, hK, hKpos⟩ :=
    (measurableSet_Ioo.diff hG.measurableSet).exists_lt_isCompact hrem
  refine ⟨K, fun x hx => hsub (hKsub hx).1, hK, ?_, hKpos⟩
  exact (isClosed_compl_and_isNowhereDense_compl.mpr ⟨hG, hdense⟩).2.mono
    (fun x hx => (hKsub hx).2)

/-- Construct disjoint positive compact pieces inside an arbitrary sequence of
nonempty open sets. Only finitely many pieces have been used at each stage. -/
theorem disjoint_compact_pieces (U : ℕ → Set ℝ)
    (ho : ∀ n, IsOpen (U n)) (hne : ∀ n, (U n).Nonempty) :
    ∃ K : ℕ → Set ℝ, (∀ n, K n ⊆ U n ∧ IsCompact (K n) ∧ 0 < volume (K n)) ∧
      Pairwise (fun m n => Disjoint (K m) (K n)) := by
  classical
  let State := {S : Set ℝ // IsClosed S ∧ IsNowhereDense S}
  have step (n : ℕ) (S : State) :
      ∃ K : Set ℝ, K ⊆ U n \ S.val ∧ IsCompact K ∧ IsNowhereDense K ∧
        0 < volume K := by
    have hd : Dense S.valᶜ := (isClosed_isNowhereDense_iff_compl.mp S.property).2
    have hn : (U n \ S.val).Nonempty := by
      simpa only [sdiff_eq_compl_inter, inter_comm] using
        hd.inter_open_nonempty (U n) (ho n) (hne n)
    exact exists_compact_nowhere_dense ((ho n).sdiff S.property.1) hn
  choose piece hp using step
  let next (n : ℕ) (S : State) : State :=
    ⟨S.val ∪ piece n S, S.property.1.union (hp n S).2.1.isClosed,
      S.property.2.union (hp n S).2.2.1⟩
  let states : ℕ → State := fun n => Nat.rec ⟨∅, isClosed_empty, isNowhereDense_empty⟩ next n
  have hsucc (n : ℕ) : (states (n + 1)).val = (states n).val ∪ piece n (states n) := rfl
  have hmono : Monotone (fun n => (states n).val) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hsucc]
    exact subset_union_left
  refine ⟨fun n => piece n (states n), fun n =>
    ⟨((hp n (states n)).1.trans sdiff_subset), (hp n (states n)).2.1,
      (hp n (states n)).2.2.2⟩, ?_⟩
  have hdis (m n : ℕ) (hmn : m < n) :
      Disjoint (piece m (states m)) (piece n (states n)) := by
    apply disjoint_left.mpr
    intro x hxm hxn
    have hx : x ∈ (states (m + 1)).val := by rw [hsucc]; exact Or.inr hxm
    exact ((hp n (states n)).1 hxn).2 (hmono hmn hx)
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hdis m n h
  · exact (hdis n m h).symm

/-- The exact local splitting required in the printed counterexample. -/
theorem locally_split_exists : Spec.LocallySplitExists := by
  classical
  let J := {p : ℚ × ℚ // p.1 < p.2}
  have : Nonempty J := ⟨⟨(0, 1), by norm_num⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (J × Bool)
  let U (n : ℕ) : Set ℝ := Ioo ((e n).1.val.1 : ℝ) ((e n).1.val.2 : ℝ)
  have ho (n : ℕ) : IsOpen (U n) := isOpen_Ioo
  have hn (n : ℕ) : (U n).Nonempty := nonempty_Ioo.mpr (by exact_mod_cast (e n).1.property)
  obtain ⟨K, hK, hdis⟩ := disjoint_compact_pieces U ho hn
  let E : Set ℝ := ⋃ n, ⋃ (_ : (e n).2 = true), K n
  have hE : MeasurableSet E := MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => (hK n).2.1.measurableSet
  have hpieces (n : ℕ) :
      ((e n).2 = true → K n ⊆ E) ∧ ((e n).2 = false → K n ⊆ Eᶜ) := by
    constructor
    · intro h x hx
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨h, hx⟩⟩
    · intro hn x hx hxe
      obtain ⟨m, hm, hxm⟩ := mem_iUnion.mp hxe |>.imp fun m h => mem_iUnion.mp h
      have hnm : n ≠ m := by intro h; subst m; simp [hn] at hm
      exact disjoint_left.mp (hdis hnm) hx hxm
  refine ⟨E, hE, ?_⟩
  intro a b hab
  obtain ⟨p, hap, hpb⟩ := exists_rat_btwn hab
  obtain ⟨q, hpq, hqb⟩ := exists_rat_btwn hpb
  have hpq' : p < q := by exact_mod_cast hpq
  let j : J := ⟨(p, q), hpq'⟩
  have hsub (n : ℕ) (hn : (e n).1 = j) : K n ⊆ Ioo a b := by
    apply (hK n).1.trans
    change Ioo ((e n).1.val.1 : ℝ) ((e n).1.val.2 : ℝ) ⊆ Ioo a b
    rw [hn]
    exact Ioo_subset_Ioo hap.le hqb.le
  obtain ⟨n, hen⟩ := he (j, true)
  obtain ⟨m, hem⟩ := he (j, false)
  constructor
  · apply (hK n).2.2.trans_le (measure_mono ?_)
    exact subset_inter ((hpieces n).1 (by rw [hen])) (hsub n (by rw [hen]))
  · apply (hK m).2.2.trans_le (measure_mono ?_)
    exact subset_inter ((hpieces m).2 (by rw [hem])) (hsub m (by rw [hem]))

section ScalarModel
variable {E : Set ℝ} (hE : MeasurableSet E)

def zeroExtend (f : RestrictedL2 E) : L2 ℂ :=
  ((memLp_indicator_iff_restrict hE.nullMeasurableSet).mpr (Lp.memLp f)).toLp
    (E.indicator (fun r => f r))

lemma zeroExtend_ae (f : RestrictedL2 E) :
    (zeroExtend hE f : ℝ → ℂ) =ᵐ[volume] E.indicator (fun r => f r) :=
  MemLp.coeFn_toLp _

lemma zeroExtend_supported (f : RestrictedL2 E) : zeroExtend hE f ∈ scalarSections E := by
  filter_upwards [zeroExtend_ae hE f] with r hr
  intro he
  simp [hr, he]

def zeroExtendLinear : RestrictedL2 E →ₗ[ℂ] scalarSections E where
  toFun f := ⟨zeroExtend hE f, zeroExtend_supported hE f⟩
  map_add' f g := by
    apply Subtype.ext
    apply Lp.ext
    have hadd : E.indicator (fun r => (f + g) r) =ᵐ[volume]
        E.indicator (fun r => f r + g r) :=
      (ae_restrict_iff' hE).mp (Lp.coeFn_add f g) |>.mono fun r hr => by
        by_cases he : r ∈ E
        · simpa only [indicator_of_mem he, Pi.add_apply, Pi.smul_apply] using hr he
        · simp only [indicator_of_notMem he]
    filter_upwards [zeroExtend_ae hE (f + g), zeroExtend_ae hE f,
      zeroExtend_ae hE g, hadd, Lp.coeFn_add (zeroExtend hE f) (zeroExtend hE g)]
      with r h1 h2 h3 h4 h5
    change zeroExtend hE (f + g) r = (zeroExtend hE f + zeroExtend hE g) r
    rw [h1, h5]
    change E.indicator (fun r => (f + g) r) r = zeroExtend hE f r + zeroExtend hE g r
    rw [h2, h3, h4]
    by_cases he : r ∈ E <;> simp [he]
  map_smul' c f := by
    apply Subtype.ext
    apply Lp.ext
    have hsmul : E.indicator (fun r => (c • f) r) =ᵐ[volume]
        E.indicator (fun r => c • f r) :=
      (ae_restrict_iff' hE).mp (Lp.coeFn_smul c f) |>.mono fun r hr => by
        by_cases he : r ∈ E
        · simpa only [indicator_of_mem he, Pi.add_apply, Pi.smul_apply] using hr he
        · simp only [indicator_of_notMem he]
    filter_upwards [zeroExtend_ae hE (c • f), zeroExtend_ae hE f,
      hsmul, Lp.coeFn_smul c (zeroExtend hE f)] with r h1 h2 h3 h4
    change zeroExtend hE (c • f) r = (c • zeroExtend hE f) r
    rw [h1, h4]
    change E.indicator (fun r => (c • f) r) r = c • zeroExtend hE f r
    rw [h2, h3]
    by_cases he : r ∈ E <;> simp [he]

lemma zeroExtend_norm (f : RestrictedL2 E) : ‖zeroExtend hE f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (zeroExtend_ae hE f),
    eLpNorm_indicator_eq_eLpNorm_restrict hE.nullMeasurableSet]

def zeroExtendIsometry : RestrictedL2 E →ₗᵢ[ℂ] scalarSections E where
  toLinearMap := zeroExtendLinear hE
  norm_map' := zeroExtend_norm hE

lemma zeroExtend_surjective : Function.Surjective (zeroExtendIsometry hE) := by
  intro g
  let f : RestrictedL2 E := ((Lp.memLp g.val).restrict E).toLp g.val
  have hf : (f : ℝ → ℂ) =ᵐ[volume.restrict E] g.val := MemLp.coeFn_toLp _
  refine ⟨f, ?_⟩
  apply Subtype.ext
  apply Lp.ext
  have hg := g.property
  filter_upwards [zeroExtend_ae hE f, (ae_restrict_iff' hE).mp hf, hg] with r h1 h2 h3
  change zeroExtend hE f r = g.val r
  by_cases he : r ∈ E
  · simpa [h1, he] using h2 he
  · simp [h1, he, h3 he]

def scalarUnitary : RestrictedL2 E ≃ₗᵢ[ℂ] scalarSections E :=
  LinearIsometryEquiv.ofSurjective (zeroExtendIsometry hE) (zeroExtend_surjective hE)

lemma scalarUnitary_ae (f : RestrictedL2 E) :
    ((scalarUnitary hE f).val : ℝ → ℂ) =ᵐ[volume] E.indicator (fun r => f r) :=
  zeroExtend_ae hE f

lemma scalarUnitary_graph (f g : RestrictedL2 E) : RestrictedCoordinateGraph E f g ↔
    ((scalarUnitary hE g).val : ℝ → ℂ) =ᵐ[volume]
      fun r => (r : ℂ) * (scalarUnitary hE f).val r := by
  constructor
  · intro h
    have hg := (ae_restrict_iff' hE).mp h.2
    filter_upwards [scalarUnitary_ae hE f, scalarUnitary_ae hE g, hg] with r h1 h2 h3
    by_cases he : r ∈ E
    · simpa only [h1, h2, indicator_of_mem he] using h3 he
    · simp only [h1, h2, indicator_of_notMem he, mul_zero]
  · intro h
    have hg : (g : ℝ → ℂ) =ᵐ[volume.restrict E] fun r => (r : ℂ) * f r := by
      apply (ae_restrict_iff' hE).mpr
      filter_upwards [scalarUnitary_ae hE f, scalarUnitary_ae hE g, h] with r h1 h2 h3
      intro he
      simpa [h1, h2, he] using h3
    exact ⟨(memLp_congr_ae hg).mp (Lp.memLp g), hg⟩

theorem scalar_multiplicity_realization : Spec.ScalarMultiplicityRealization := by
  classical
  intro E hE
  refine ⟨?_, ?_, ?_, scalarUnitary hE, scalarUnitary_ae hE, scalarUnitary_graph hE⟩
  · exact measurable_one.ite hE measurable_zero
  · intro r
    by_cases he : r ∈ E
    · rw [scalarFiber, ite_eq_left he, scalarMultiplicity, ite_eq_left he]
      simp
    · rw [scalarFiber, ite_eq_right he, scalarMultiplicity, ite_eq_right he]
      simp
  · intro f
    change (∀ᵐ r ∂volume, r ∉ E → f r = 0) ↔ _
    apply eventually_congr
    filter_upwards [] with r
    by_cases he : r ∈ E <;> simp [scalarFiber, he]

end ScalarModel

lemma cutMeasure_finite (E : Set ℝ) : IsFiniteMeasure (cutMeasure E) := by
  have : IsFiniteMeasure (volume.restrict (E ∩ Icc (-1 : ℝ) 1)) :=
    ⟨lt_of_le_of_lt (by simpa using measure_mono (μ := (volume : Measure ℝ)) (inter_subset_right : E ∩ Icc (-1 : ℝ) 1 ⊆ Icc (-1) 1))
      (by simp : volume (Icc (-1 : ℝ) 1) < ∞)⟩
  exact Measure.isFiniteMeasure_map _ _

lemma cutMeasure_bounded (E : Set ℝ) : BoundedCoordinate (cutMeasure E) := by
  refine ⟨1, ?_⟩
  apply (ae_map_iff (by fun_prop)
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : E ∩ Icc (-1 : ℝ) 1 ⊆ Icc (-1) 1)
    (ae_restrict_mem (μ := volume) measurableSet_Icc)] with r hr
  simpa only [Complex.norm_real, Real.norm_eq_abs, NNReal.coe_one] using abs_le.mpr hr

lemma cutMeasure_not_dominating {E : Set ℝ} (hE : LocallySplit E) :
    ¬ cutMeasure univ ≪ cutMeasure E := by
  let B : Set ℂ := Complex.re ⁻¹' Eᶜ
  have hB : MeasurableSet B := hE.1.compl.preimage Complex.measurable_re
  have hz : cutMeasure E B = 0 := by
    rw [cutMeasure, Measure.map_apply (by fun_prop) hB,
      Measure.restrict_apply (hB.preimage Complex.measurable_ofReal)]
    have hempty : (fun r : ℝ => (r : ℂ)) ⁻¹' B ∩ (E ∩ Icc (-1) 1) = ∅ := by
      ext r
      simp [B]
      tauto
    rw [hempty, measure_empty]
  have hpos : 0 < cutMeasure univ B := by
    rw [cutMeasure, Measure.map_apply (by fun_prop) hB,
      Measure.restrict_apply (hB.preimage Complex.measurable_ofReal)]
    apply (hE.2 (-1) 1 (by norm_num)).2.trans_le (measure_mono ?_)
    intro r hr
    exact ⟨by simpa [B] using hr.1, mem_univ _, hr.2.1.le, hr.2.2.le⟩
  intro h
  exact hpos.ne' (h hz)

/-- Apply the genuine finite-measure spectral multiplicity classification to
these bounded spectral windows. Full topological support never substitutes
for equality of measure classes. -/
theorem bounded_classification_obstruction : Spec.BoundedClassificationObstruction := by
  intro E hE
  refine ⟨cutMeasure_bounded E, cutMeasure_bounded univ, ?_⟩
  intro n hequiv
  let hμ := cutMeasure_bounded E
  let hν := cutMeasure_bounded univ
  have := cutMeasure_finite E
  have := cutMeasure_finite univ
  have hdata := (ExpandedFA.VonNeumann.MultiplicityUniqueness.classification
    (cutMeasure E) (cutMeasure univ) (unitMultiplicity (cutMeasure E)) n hμ hν).mp hequiv
  exact cutMeasure_not_dominating hE hdata.2.1

lemma complement_pos {E : Set ℝ} (hE : LocallySplit E) : 0 < volume Eᶜ :=
  (hE.2 0 1 (by norm_num)).2.trans_le (measure_mono inter_subset_left)

theorem scalar_multiplicity_not_constant : Spec.NonconstantScalarMultiplicity := by
  intro E hE c
  classical
  intro h
  have hnull := ae_iff.mp h
  by_cases hc : c = 0
  · have hz : volume (E ∩ Ioo (0 : ℝ) 1) = 0 := by
      apply measure_mono_null (t := {r | ¬ scalarMultiplicity E r = c}) _ hnull
      intro r hr
      simp [scalarMultiplicity, hr.1, hc]
    exact (hE.2 0 1 (by norm_num)).1.ne' hz
  · have hz : volume Eᶜ = 0 := by
      apply measure_mono_null (t := {r | ¬ scalarMultiplicity E r = c}) _ hnull
      intro r hr
      change ¬ scalarMultiplicity E r = c
      have he : r ∉ E := hr
      rw [scalarMultiplicity, ite_eq_right he]
      exact Ne.symm hc
    exact (complement_pos hE).ne' hz

lemma no_translation_model {E : Set ℝ} (hE : LocallySplit E)
    (A : Operator ℂ (RestrictedL2 E) (RestrictedL2 E))
    (hA : SymmetryAndDeficienciesSpec.selfAdjointValue A)
    (hgraph : ∀ f g, (f, g) ∈ A.graph ↔ RestrictedCoordinateGraph E f g)
    (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [CompleteSpace M] [Nontrivial M] : ¬ OperatorTranslationModel M A := by
  intro h
  obtain ⟨W, hW⟩ := (operator_model_iff (RestrictedL2 E) M A hA).mp h
  apply TranslationMultiplicityWarning.no_coordinate_graph_equivalence hE.1
    (complement_pos hE) (CoordinateMultiplicationModel.restricted_spectral_model E hE.1) M
  exact ⟨W, fun f g => (hgraph f g).symm.trans (hW f g)⟩


lemma indicator_norm_sq {μ : Measure ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hfin : μ S ≠ ∞) :
    ENNReal.ofReal (‖indicatorConstLp 2 hS hfin (1 : ℂ)‖ ^ 2) = μ S := by
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat, one_div]
  rw [show μ.real S ^ (2 : ℝ)⁻¹ = Real.sqrt (μ.real S) by
    rw [Real.sqrt_eq_rpow, one_div], Real.sq_sqrt (by positivity)]
  exact ENNReal.ofReal_toReal hfin

lemma window_scalar_measure {E : Set ℝ}
    (P : ExpandedFA.SpectralMeasure.ProjectionValuedMeasure ℝ (RestrictedL2 E))
    (C : BoundedRealization P)
    (hP : ∀ B : Set ℝ, MeasurableSet B → ∀ f : RestrictedL2 E,
      (P B f : ℝ → ℂ) =ᵐ[volume.restrict E] B.indicator (fun r => f r)) :
    ∃ f : RestrictedL2 E,
      Measure.map (fun r : ℝ => (r : ℂ)) (C.measure f) = cutMeasure E := by
  let μ : Measure ℝ := volume.restrict E
  let I : Set ℝ := Icc (-1) 1
  have hI : MeasurableSet I := measurableSet_Icc
  have hIfin : μ I ≠ ∞ := ne_top_of_le_ne_top measure_Icc_lt_top.ne
    (Measure.restrict_apply_le _ _)
  let f : RestrictedL2 E := indicatorConstLp 2 hI hIfin 1
  have hf : (f : ℝ → ℂ) =ᵐ[μ] I.indicator (fun _ => 1) := indicatorConstLp_coeFn
  have hmeasure : C.measure f = μ.restrict I := by
    ext B hB
    have hfin : μ (B ∩ I) ≠ ∞ := ne_top_of_le_ne_top hIfin (measure_mono inter_subset_right)
    have he : P B f = indicatorConstLp 2 (hB.inter hI) hfin 1 := by
      apply Lp.ext
      filter_upwards [hP B hB f, hf,
        (indicatorConstLp_coeFn (p := 2) (hs := hB.inter hI) (hμs := hfin) (c := (1 : ℂ)))]
        with r h1 h2 h3
      rw [h1, h3]
      by_cases hrB : r ∈ B <;> by_cases hrI : r ∈ I <;> simp [hrB, hrI, h2]
    rw [C.measure_apply f B hB, he, indicator_norm_sq,
      Measure.restrict_apply hB]
  refine ⟨f, ?_⟩
  rw [hmeasure]
  change Measure.map _ ((volume.restrict E).restrict (Icc (-1) 1)) = _
  rw [Measure.restrict_restrict measurableSet_Icc, inter_comm]
  rfl

/-- The actual restricted coordinate PVM has full interval support, and its
maximal self-adjoint coordinate operator has no nonzero full translation model.
The arbitrary-multiplicity exclusion reuses the group/energy-measure argument,
which remains valid even for nonseparable Hilbert multiplicity. -/
theorem selfAdjoint_boundary {E : Set ℝ} (hE : LocallySplit E) :
    Spec.SelfAdjointBoundary.{u} E := by
  obtain ⟨P, C, A, hP, hC, hCA, hA, hgraph, hac, hsupp⟩ :=
    CoordinateMultiplicationModel.restricted_spectral_model E hE.1
  exact ⟨P, C, A, hP, hC, hCA, hA, hgraph, hac,
    fun a b hab => hsupp a b (hE.2 a b hab).1,
    window_scalar_measure P C hP,
    fun M _ _ _ _ => no_translation_model hE A hA hgraph M⟩

/-- The complete stronger counterexample of the adopted translation-model proof. -/
theorem boundary_counterexample : Spec.BoundaryCounterexample.{u} := by
  obtain ⟨E, hE⟩ := locally_split_exists
  exact ⟨E, hE, scalar_multiplicity_realization E hE.1,
    scalar_multiplicity_not_constant E hE,
    bounded_classification_obstruction E hE, selfAdjoint_boundary hE⟩

end ExpandedFA.Models.TranslationMultiplicityBoundary
