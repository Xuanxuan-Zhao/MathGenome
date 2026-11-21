import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.CountableFiberTransport
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open MeasureTheory Set Function
open scoped ENNReal

namespace D12Complex.Ch04.CountableFiberTransport

noncomputable def sourceSet : Specs.D12Complex.Ch04.CountableFiberTransport.sourceSet_type := Specs.D12Complex.Ch04.CountableFiberTransport.sourceSet_value
noncomputable def fiber : Specs.D12Complex.Ch04.CountableFiberTransport.fiber_type := Specs.D12Complex.Ch04.CountableFiberTransport.fiber_value

variable {f : ℝ → ℂ} {μ : Measure ℝ} {ν : Measure ℂ} {P : ℕ → Set ℝ}

/-- Extension by zero of the weight on a single injective parameter piece. -/
noncomputable def pieceWeight {E : Type*} [Zero E] (f : ℝ → ℂ)
    (P : ℕ → Set ℝ) (h : ℝ → E) (n : ℕ) : ℂ → E :=
  Function.extend (fun t : P n => f t) (fun t => h t) (fun _ => 0)

lemma pieceWeight_apply {E : Type*} [Zero E] (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P)
    (h : ℝ → E) (n : ℕ) (t : P n) : pieceWeight f P h n (f t) = h t :=
  (H.injOn n).injective.extend_apply _ _ t

lemma pieceWeight_eq_zero {E : Type*} [Zero E] (h : ℝ → E) (n : ℕ)
    {z : ℂ} (hz : z ∉ f '' P n) : pieceWeight f P h n z = 0 := by
  apply Function.extend_apply'
  simpa only [Set.mem_image, not_exists, Subtype.exists, exists_prop] using hz

lemma pieceWeight_indicator {E : Type*} [Zero E] (h : ℝ → E) (n : ℕ) :
    (f '' P n).indicator (pieceWeight f P h n) = pieceWeight f P h n := by
  classical
  funext z
  by_cases hz : z ∈ f '' P n
  · simp [hz]
  · simp [hz, pieceWeight_eq_zero h n hz]

lemma piece_embedding (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P) (n : ℕ) :
    MeasurableEmbedding (fun t : P n => f t) :=
  ContinuousOn.measurableEmbedding (H.measurableSet n) (H.continuousOn n) (H.injOn n)

lemma piece_map (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P) (n : ℕ) :
    Measure.map (fun t : P n => f t) (Measure.comap Subtype.val μ) =
      ν.restrict (f '' P n) := by
  have hf : AEMeasurable f (μ.restrict (P n)) :=
    (aemeasurable_restrict_iff_comap_subtype (H.measurableSet n)).2
      (piece_embedding H n).measurable.aemeasurable
  rw [← map_comap_subtype_coe (H.measurableSet n)] at hf
  calc
    _ = Measure.map f (Measure.map (Subtype.val : P n → ℝ)
        (Measure.comap Subtype.val μ)) :=
      (hf.map_map_of_aemeasurable measurable_subtype_coe.aemeasurable).symm
    _ = _ := by rw [map_comap_subtype_coe (H.measurableSet n), H.map_eq n]

lemma piece_aemeasurable {E : Type*} [Zero E] [MeasurableSpace E]
    (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P) (h : ℝ → E) (n : ℕ)
    (hh : AEMeasurable h (μ.restrict (P n))) :
    AEMeasurable (pieceWeight f P h n) ν := by
  rw [← pieceWeight_indicator h n, aemeasurable_indicator_iff (H.measurableSet_image n),
    ← piece_map H n, (piece_embedding H n).aemeasurable_map_iff]
  simpa only [Function.comp_def, pieceWeight_apply H] using
    (aemeasurable_restrict_iff_comap_subtype (H.measurableSet n)).1 hh

lemma piece_lintegral (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P) (h : ℝ → ℝ≥0∞) (n : ℕ) :
    ∫⁻ z, pieceWeight f P h n z ∂ν = ∫⁻ t in P n, h t ∂μ := by
  rw [← pieceWeight_indicator h n, lintegral_indicator (H.measurableSet_image n),
    ← piece_map H n, (piece_embedding H n).lintegral_map]
  simp only [pieceWeight_apply H]
  exact lintegral_subtype_comap (H.measurableSet n) h

/-- An active piece determines its unique actual occurrence. -/
noncomputable def indexedOccurrence (z : ℂ) (i : {n // z ∈ f '' P n}) : fiber f P z :=
  ⟨Classical.choose i.property,
    mem_iUnion.mpr ⟨i.val, (Classical.choose_spec i.property).1⟩,
    (Classical.choose_spec i.property).2⟩

lemma indexedOccurrence_bijective (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P)
    (z : ℂ) : Function.Bijective (indexedOccurrence (f := f) (P := P) z) := by
  constructor
  · intro i j hij
    apply Subtype.ext
    by_contra hne
    have heq : Classical.choose i.property = Classical.choose j.property :=
      congrArg Subtype.val hij
    exact Set.disjoint_left.mp (H.disjoint hne)
      (Classical.choose_spec i.property).1
      (heq.symm ▸ (Classical.choose_spec j.property).1)
  · intro t
    obtain ⟨n, hn⟩ := mem_iUnion.mp t.property.1
    let i : {n // z ∈ f '' P n} := ⟨n, ⟨t.val, hn, t.property.2⟩⟩
    refine ⟨i, Subtype.ext ?_⟩
    exact H.injOn n (Classical.choose_spec i.property).1 hn
      ((Classical.choose_spec i.property).2.trans t.property.2.symm)

/-- A pointwise identity: images may overlap, but parameter pieces do not. -/
lemma fiber_sum_eq {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P)
    (h : ℝ → E) (z : ℂ) :
    (∑' t : fiber f P z, h t) = ∑' n, pieceWeight f P h n z := by
  classical
  let e := Equiv.ofBijective _ (indexedOccurrence_bijective H z)
  calc
    (∑' t : fiber f P z, h t) = ∑' i : {n // z ∈ f '' P n}, h (indexedOccurrence z i) :=
      (e.tsum_eq (fun t => h t)).symm
    _ = ∑' i : {n // z ∈ f '' P n}, pieceWeight f P h i z := by
      apply tsum_congr
      intro i
      have heq := pieceWeight_apply H h i.val
        (⟨Classical.choose i.property, (Classical.choose_spec i.property).1⟩ : P i.val)
      simpa only [(Classical.choose_spec i.property).2, indexedOccurrence] using heq.symm
    _ = ∑' n, pieceWeight f P h n z := by
      apply tsum_subtype_eq_of_support_subset (f := fun n => pieceWeight f P h n z)
        (s := {n | z ∈ f '' P n})
      intro n hn
      by_contra hz
      exact hn (pieceWeight_eq_zero h n hz)

theorem unsigned_transport : Specs.D12Complex.Ch04.CountableFiberTransport.unsigned_transport_type := by
  intro f μ ν P H h hh
  have hm (n : ℕ) : AEMeasurable (pieceWeight f P h n) ν :=
    piece_aemeasurable H h n (hh.mono_measure (Measure.restrict_mono (subset_iUnion P n) le_rfl))
  have heq : (fun z => ∑' t : fiber f P z, h t) = (fun z => ∑' n, pieceWeight f P h n z) :=
    funext (fiber_sum_eq H h)
  change AEMeasurable (fun z => ∑' t : fiber f P z, h t) ν ∧
    (∫⁻ z, ∑' t : fiber f P z, h t ∂ν) = ∫⁻ t in ⋃ n, P n, h t ∂μ
  rw [heq]
  refine ⟨AEMeasurable.tsum hm, ?_⟩
  rw [lintegral_tsum hm]
  simp_rw [piece_lintegral H]
  exact (lintegral_iUnion H.measurableSet H.disjoint h).symm

lemma piece_integrable (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P)
    (h : ℝ → ℂ) (n : ℕ) (hh : Integrable h (μ.restrict (P n))) :
    Integrable (pieceWeight f P h n) ν := by
  rw [← pieceWeight_indicator h n, integrable_indicator_iff (H.measurableSet_image n),
    IntegrableOn, ← piece_map H n, (piece_embedding H n).integrable_map_iff]
  simpa only [Function.comp_def, pieceWeight_apply H] using
    (integrableOn_iff_comap_subtypeVal (H.measurableSet n)).1 hh

lemma piece_integral (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P)
    (h : ℝ → ℂ) (n : ℕ) :
    ∫ z, pieceWeight f P h n z ∂ν = ∫ t in P n, h t ∂μ := by
  rw [← pieceWeight_indicator h n, integral_indicator (H.measurableSet_image n),
    ← piece_map H n, (piece_embedding H n).integral_map]
  simp only [pieceWeight_apply H]
  exact integral_subtype_comap (H.measurableSet n) h

lemma pieceWeight_enorm
    (H : Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp f μ ν P)
    (h : ℝ → ℂ) (n : ℕ) (z : ℂ) :
    pieceWeight f P (fun t => ‖h t‖ₑ) n z = ‖pieceWeight f P h n z‖ₑ := by
  by_cases hz : z ∈ f '' P n
  · obtain ⟨t, ht, rfl⟩ := hz
    rw [pieceWeight_apply H _ n ⟨t, ht⟩, pieceWeight_apply H _ n ⟨t, ht⟩]
  · rw [pieceWeight_eq_zero _ n hz, pieceWeight_eq_zero _ n hz, enorm_zero]

theorem signed_transport : Specs.D12Complex.Ch04.CountableFiberTransport.signed_transport_type := by
  intro f μ ν P H h hh
  have hu := unsigned_transport f μ ν P H (fun t => ‖h t‖ₑ) hh.1.enorm
  have hlt : (∫⁻ z, ∑' t : fiber f P z, ‖h t‖ₑ ∂ν) < ∞ :=
    hu.2.trans_lt hh.2
  have hfinite : ∀ᵐ z ∂ν, (∑' t : fiber f P z, ‖h t‖ₑ) < ∞ :=
    ae_lt_top' hu.1 hlt.ne
  have hp (n : ℕ) : Integrable (pieceWeight f P h n) ν :=
    piece_integrable H h n (hh.mono_measure (Measure.restrict_mono (subset_iUnion P n) le_rfl))
  have hnorm (z : ℂ) : (∑' n, ‖pieceWeight f P h n z‖ₑ) =
      ∑' t : fiber f P z, ‖h t‖ₑ := by
    simp_rw [← pieceWeight_enorm H h]
    exact (fiber_sum_eq H _ z).symm
  have hsum_lt : (∫⁻ z, ∑' n, ‖pieceWeight f P h n z‖ₑ ∂ν) < ∞ := by
    simpa only [hnorm] using hlt
  have hsum_int : (∑' n, ∫⁻ z, ‖pieceWeight f P h n z‖ₑ ∂ν) ≠ ∞ := by
    rw [← lintegral_tsum (fun n => (hp n).1.enorm)]
    exact hsum_lt.ne
  have hm : AEStronglyMeasurable (fun z => ∑' t : fiber f P z, h t) ν := by
    have hm' : AEStronglyMeasurable (fun z => ∑' n, pieceWeight f P h n z) ν :=
      AEStronglyMeasurable.tsum (fun n => (hp n).1)
    simpa only [← fiber_sum_eq H h] using hm'
  change (∀ᵐ z ∂ν, (∑' t : fiber f P z, ENNReal.ofReal ‖h t‖) < ∞ ∧
      Summable (fun t : fiber f P z => h t)) ∧
    Integrable (fun z => ∑' t : fiber f P z, h t) ν ∧
    (∫ z, ∑' t : fiber f P z, h t ∂ν) = ∫ t in ⋃ n, P n, h t ∂μ
  refine ⟨?_, ⟨hm, ?_⟩, ?_⟩
  · filter_upwards [hfinite] with z hz
    refine ⟨by simpa only [ofReal_norm] using hz, ?_⟩
    exact ((tsum_enorm_ne_top_iff_summable_norm).mp hz.ne).of_norm
  · exact (lintegral_mono fun z => enorm_tsum_le_tsum_enorm).trans_lt hlt
  · calc
      (∫ z, ∑' t : fiber f P z, h t ∂ν) =
          ∫ z, ∑' n, pieceWeight f P h n z ∂ν := by
        congr 1
        exact funext (fiber_sum_eq H h)
      _ = ∑' n, ∫ z, pieceWeight f P h n z ∂ν :=
        integral_tsum (fun n => (hp n).1) hsum_int
      _ = ∑' n, ∫ t in P n, h t ∂μ := by simp_rw [piece_integral H]
      _ = ∫ t in ⋃ n, P n, h t ∂μ :=
        (integral_iUnion H.measurableSet H.disjoint hh).symm

end D12Complex.Ch04.CountableFiberTransport
