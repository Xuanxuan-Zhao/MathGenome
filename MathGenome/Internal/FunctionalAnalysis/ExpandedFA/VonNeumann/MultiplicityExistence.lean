import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.MultiplicityModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.NormalAlgebraControlMeasure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.ArbitraryCyclicSum
import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Data.Nat.Nth
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace ExpandedFA.VonNeumann.MultiplicityExistence
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Extend a measure on the actual spectrum to a Borel measure on ℂ. -/
def spectrumMeasure (N : H →L[ℂ] H) (μ : Measure (spectrum ℂ N)) : Measure ℂ :=
  μ.map Subtype.val

theorem spectrumMeasure_supported (N : H →L[ℂ] H) (μ : Measure (spectrum ℂ N)) :
    Spec.SpectrumSupported N (spectrumMeasure N μ) := by
  rw [Spec.SpectrumSupported, spectrumMeasure,
    Measure.map_apply measurable_subtype_coe (spectrum.isCompact N).isClosed.measurableSet.compl]
  have h : Subtype.val ⁻¹' (spectrum ℂ N)ᶜ = (∅ : Set (spectrum ℂ N)) := by
    ext z
    simp
  rw [h, measure_empty]

theorem spectrumMeasure_control (N : H →L[ℂ] H)
    (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
    (μ : Measure (spectrum ℂ N))
    (hμ : NormalAlgebraControlMeasure.Spec.IsControlMeasure E μ) :
    Spec.ComplexControlMeasure N E (spectrumMeasure N μ) := by
  intro B hB
  rw [spectrumMeasure, Measure.map_apply measurable_subtype_coe hB]
  exact hμ _ (measurable_subtype_coe hB)

/-- The product bound works also in the zero operator algebra, where the
identity has norm zero. No `NormOneClass` instance is needed. -/
theorem spectrumMeasure_bounded (N : H →L[ℂ] H) (μ : Measure (spectrum ℂ N)) :
    MultiplicityModel.Spec.BoundedCoordinate (spectrumMeasure N μ) := by
  refine ⟨‖N‖₊ * ‖(1 : H →L[ℂ] H)‖₊, ?_⟩
  apply (ae_map_iff measurable_subtype_coe.aemeasurable ?_).mpr
  · exact Filter.Eventually.of_forall fun z => spectrum.norm_le_norm_mul_of_mem z.property
  · exact measurableSet_le measurable_norm measurable_const

theorem finite_complex_control_measure : Spec.FiniteComplexControlMeasure.{u} := by
  intro H _ _ _ _ N hN
  obtain ⟨E, e, μ, hE, hfinite, _, hcontrol⟩ :=
    NormalAlgebraControlMeasure.finite_control_measure H N hN
  let := hfinite
  exact ⟨E, spectrumMeasure N μ, hE, by dsimp [spectrumMeasure]; infer_instance,
    spectrumMeasure_supported N μ, spectrumMeasure_control N E μ hcontrol,
    spectrumMeasure_bounded N μ⟩

/-- Constant multiplicity one is a valid representative for the zero measure;
all of its section classes are nevertheless zero. -/
def zeroMultiplicity : MultiplicityModel.Spec.Multiplicity (0 : Measure ℂ) where
  toFun := fun _ => 1
  measurable_toFun := measurable_const
  positive := by simp

theorem zero_model : Spec.ZeroModel.{u} := by
  intro H _ _ _ _ N
  let m := zeroMultiplicity
  let := MultiplicityModel.zero_measure_sections m
  let U : MultiplicityModel.Spec.DirectIntegral 0 m ≃ₗᵢ[ℂ] H :=
    { LinearEquiv.ofSubsingleton _ _ with
      norm_map' := fun x => by
        rw [Subsingleton.elim x 0, map_zero, norm_zero, norm_zero] }
  refine ⟨m, ⟨0, by simp⟩, U, fun _ => Subsingleton.elim _ _⟩

/-- Number of active cyclic coordinates, including infinity. -/
def activeCount (A : ℕ → Set ℂ) (z : ℂ) : ℕ∞ := {j | z ∈ A j}.encard

theorem activeCount_measurable (A : ℕ → Set ℂ) (hA : ∀ j, MeasurableSet (A j)) :
    Measurable (activeCount A) := by
  apply measurable_encard.comp
  exact measurable_set_iff.mpr fun j => measurableSet_setOfPred.mp (hA j)

/-- The support union being conull gives the required positive multiplicity.
This implication remains valid when μ is zero. -/
def activeMultiplicity (μ : Measure ℂ) (A : ℕ → Set ℂ)
    (hA : ∀ j, MeasurableSet (A j)) (hcover : ∀ᵐ z ∂μ, ∃ j, z ∈ A j) :
    MultiplicityModel.Spec.Multiplicity μ where
  toFun := activeCount A
  measurable_toFun := activeCount_measurable A hA
  positive := hcover.mono fun _ hz => Set.encard_pos.mpr hz

/-- The new coordinate occupied by active index j. Unlike choosing an infinite
enumeration, this finite count works uniformly for finite and infinite fibers. -/
def activeRank (A : ℕ → Set ℂ) (z : ℂ) (j : ℕ) : ℕ := by
  classical
  exact Nat.count (fun i => z ∈ A i) j

theorem activeRank_measurable (A : ℕ → Set ℂ) (hA : ∀ j, MeasurableSet (A j))
    (j : ℕ) : Measurable (fun z => activeRank A z j) := by
  classical
  induction j with
  | zero => simp [activeRank]
  | succ j hj =>
    have hi : Measurable ((A j).piecewise (fun _ : ℂ => (1 : ℕ)) (fun _ => 0)) :=
      measurable_const.piecewise (hA j) measurable_const
    convert hj.add hi using 1
    funext z
    simp [activeRank, Nat.count_succ, Set.piecewise]

/-- Active coordinates never collide under finite-count reordering. -/
theorem activeRank_injective (A : ℕ → Set ℂ) (z : ℂ) {i j : ℕ}
    (hi : z ∈ A i) (hj : z ∈ A j) (h : activeRank A z i = activeRank A z j) : i = j := by
  classical
  exact Nat.count_injective hi hj h

/-- Each matrix entry of the coordinate reordering is measurable: its support
uses membership in A_j and only the first j membership decisions. -/
theorem activeRank_entry_measurable (A : ℕ → Set ℂ)
    (hA : ∀ j, MeasurableSet (A j)) (j k : ℕ) :
    MeasurableSet {z | z ∈ A j ∧ activeRank A z j = k} :=
  (hA j).inter (measurableSet_eq_fun (activeRank_measurable A hA j) measurable_const)

theorem activeRank_lt_activeCount (A : ℕ → Set ℂ) (z : ℂ) {j : ℕ}
    (hj : z ∈ A j) : (activeRank A z j : ℕ∞) < activeCount A z := by
  classical
  by_cases hfin : {i | z ∈ A i}.Finite
  · rw [activeCount, hfin.encard_eq_coe_toFinset_card]
    exact_mod_cast Nat.count_lt_card hfin hj
  · rw [activeCount, Set.Infinite.encard_eq hfin]
    exact ENat.natCast_lt_top _

/-- The inverse enumeration; its default value outside the active fiber is
irrelevant, and both inverse identities below require exactly active indices. -/
def activeIndex (A : ℕ → Set ℂ) (z : ℂ) (k : ℕ) : ℕ :=
  Nat.nth (fun j => z ∈ A j) k

theorem activeIndex_bounds (A : ℕ → Set ℂ) (z : ℂ) {k : ℕ}
    (hk : (k : ℕ∞) < activeCount A z) :
    ∀ hfin : {j | z ∈ A j}.Finite, k < hfin.toFinset.card := by
  intro hfin
  rw [activeCount, hfin.encard_eq_coe_toFinset_card] at hk
  exact_mod_cast hk

theorem activeIndex_mem (A : ℕ → Set ℂ) (z : ℂ) {k : ℕ}
    (hk : (k : ℕ∞) < activeCount A z) : z ∈ A (activeIndex A z k) :=
  Nat.nth_mem _ (activeIndex_bounds A z hk)

theorem activeRank_activeIndex (A : ℕ → Set ℂ) (z : ℂ) {k : ℕ}
    (hk : (k : ℕ∞) < activeCount A z) : activeRank A z (activeIndex A z k) = k := by
  classical
  exact Nat.count_nth (activeIndex_bounds A z hk)

theorem activeIndex_activeRank (A : ℕ → Set ℂ) (z : ℂ) {j : ℕ}
    (hj : z ∈ A j) : activeIndex A z (activeRank A z j) = j := by
  classical
  exact Nat.nth_count hj

theorem activeIndex_eq_iff (A : ℕ → Set ℂ) (z : ℂ) (k : ℕ) {j : ℕ} (hj : j ≠ 0) :
    activeIndex A z k = j ↔ z ∈ A j ∧ activeRank A z j = k := by
  classical
  constructor
  · intro h
    have hnth : Nat.nth (fun i => z ∈ A i) k = j := h
    have hnzero : Nat.nth (fun i => z ∈ A i) k ≠ 0 := by rwa [hnth]
    constructor
    · simpa only [hnth] using Nat.nth_mem_of_ne_zero hnzero
    · change Nat.count (fun i => z ∈ A i) j = k
      rw [← hnth]
      exact Nat.count_nth (Nat.lt_card_toFinset_of_nth_ne_zero hnzero)
  · rintro ⟨hmem, hcount⟩
    rw [← hcount]
    exact activeIndex_activeRank A z hmem

/-- The increasing enumeration is measurable, including its default value
when the requested coordinate does not exist. -/
theorem activeIndex_measurable (A : ℕ → Set ℂ)
    (hA : ∀ j, MeasurableSet (A j)) (k : ℕ) :
    Measurable (fun z => activeIndex A z k) := by
  classical
  have hnonzero (j : ℕ) (hj : j ≠ 0) :
      MeasurableSet {z | activeIndex A z k = j} := by
    simp_rw [activeIndex_eq_iff A _ k hj]
    exact activeRank_entry_measurable A hA j k
  apply measurable_to_countable'
  intro j
  by_cases hj : j = 0
  · subst j
    have heq : (fun z => activeIndex A z k) ⁻¹' {0} =
        (⋃ n : ℕ, {z | activeIndex A z k = n + 1})ᶜ := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro hz ⟨n, hn⟩
        omega
      · intro hz
        by_contra hzero
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
        exact hz ⟨n, hn⟩
    rw [heq]
    exact (MeasurableSet.iUnion fun n => hnonzero (n + 1) (by omega)).compl
  · exact hnonzero j hj

theorem controlMeasure_zero [Subsingleton H] (N : H →L[ℂ] H)
    (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
    (μ : Measure ℂ) (hμ : Spec.ComplexControlMeasure N E μ) : μ = 0 :=
  Measure.measure_univ_eq_zero.mp ((hμ univ MeasurableSet.univ).mp (Subsingleton.elim _ _))

namespace ScalarPushforward

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
  (μ : Measure S) (ι : S → T) (hι : MeasurableEmbedding ι)

/-- Pullback of scalar L² along a measurable embedding, with the pushforward
measure. -/
def pull : Lp ℂ 2 (μ.map ι) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ ι ⟨hι.measurable, rfl⟩

/-- Extension of representatives proves onto-ness, including an empty source
space; no inverse point or positive measure is chosen. -/
theorem pull_surjective : Function.Surjective (pull μ ι hι) := by
  intro f
  let F : T → ℂ := Function.extend ι f (fun _ => 0)
  have hF : StronglyMeasurable F :=
    hι.stronglyMeasurable_extend (Lp.stronglyMeasurable f) stronglyMeasurable_const
  have hcomp : F ∘ ι = f := by
    funext x
    exact hι.injective.extend_apply f (fun _ => 0) x
  have hmem : MemLp F 2 (μ.map ι) :=
    hι.memLp_map_measure_iff.mpr (hcomp ▸ Lp.memLp f)
  refine ⟨hmem.toLp F, ?_⟩
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving (hmem.toLp F)
    (show MeasurePreserving ι μ (μ.map ι) from ⟨hι.measurable, rfl⟩)
  have h2 := ae_of_ae_map hι.measurable.aemeasurable (MemLp.coeFn_toLp hmem)
  filter_upwards [h1, h2] with x h1 h2
  change pull μ ι hι (hmem.toLp F) x = f x
  exact h1.trans (h2.trans (congrFun hcomp x))

/-- This is the actual surjective L² identification needed when moving the
cyclic scalar measures from the spectrum into ℂ. -/
def equivalence : Lp ℂ 2 (μ.map ι) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (pull μ ι hι) (pull_surjective μ ι hι)

theorem equivalence_ae (f : Lp ℂ 2 (μ.map ι)) :
    equivalence μ ι hι f =ᵐ[μ] f ∘ ι :=
  Lp.coeFn_compMeasurePreserving f ⟨hι.measurable, rfl⟩

end ScalarPushforward

/-- The zero vector contributes a zero cyclic summand. This lets a finite or
empty family be padded to a sequence without adding a nonzero-space assumption. -/
theorem cyclicSpace_zero (N : H →L[ℂ] H) :
    SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N 0 = ⊥ := by
  have hr : LinearMap.range
      (SpectralMeasure.ArbitraryCyclicSum.Spec.algebraOrbit N 0) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro x ⟨a, rfl⟩
    change (a : H →L[ℂ] H) 0 = 0
    exact map_zero _
  simp [SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace, hr]

/-- A sequence of mutually orthogonal cyclic spaces with dense sum. Missing
indices of a finite or empty family are filled with the zero vector. -/
theorem countable_cyclic_generators [TopologicalSpace.SeparableSpace H]
    (N : H →L[ℂ] H) (hN : IsStarNormal N) :
    ∃ e : ℕ → H,
      Pairwise (fun i j => SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e i) ⟂
        SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j)) ∧
      (⨆ i, SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e i)).topologicalClosure = ⊤ := by
  classical
  obtain ⟨s, hnonzero, horth, _hred, htotal, _hunitary⟩ :=
    SpectralMeasure.ArbitraryCyclicSum.orthogonal_decomposition H N hN
  have hcount : s.Countable :=
    SeparableAbelianSeparating.orthogonal_set_countable s hnonzero (by
      intro x hx y hy hxy
      exact (horth hx hy hxy).inner_eq
        (SpectralMeasure.ArbitraryCyclicSum.self_mem_cyclicSpace N x)
        (SpectralMeasure.ArbitraryCyclicSum.self_mem_cyclicSpace N y))
  let : Countable s := hcount.to_subtype
  let : Encodable s := Encodable.ofCountable s
  let e : ℕ → H := fun n => (Encodable.decode₂ s n).elim 0 Subtype.val
  have he (x : s) : e (Encodable.encode x) = (x : H) := by
    simp [e, Encodable.decode₂_encode]
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    cases hi : Encodable.decode₂ s i with
    | none => simp [e, hi, cyclicSpace_zero]
    | some x =>
      cases hj : Encodable.decode₂ s j with
      | none => simp [e, hj, cyclicSpace_zero]
      | some y =>
        have hxy : (x : H) ≠ (y : H) := by
          intro h
          have h' : x = y := Subtype.ext h
          have hxi := Encodable.decode₂_eq_some.mp hi
          have hyj := Encodable.decode₂_eq_some.mp hj
          exact hij (hxi.symm.trans ((congrArg Encodable.encode h').trans hyj))
        simpa [e, hi, hj] using horth x.property y.property hxy
  · apply top_unique
    rw [← htotal]
    apply Submodule.topologicalClosure_mono
    apply iSup_le
    intro x
    rw [← he x]
    exact le_iSup (fun i => SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e i)) _

/-- A countable scalar L² sum for the *same* chosen spectral resolution.
The scalar measures remain on the actual spectrum at this stage. The unitary
is specified on every summable family, and its covariance is stated without
choosing a second, potentially incompatible, diagonal operator. -/
theorem countable_scalar_model [TopologicalSpace.SeparableSpace H]
    (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
    (hE : SpectralMeasure.NormalPVM.Spec.Resolves N E) :
    ∃ (e : ℕ → H)
      (U : lp (fun j => Lp ℂ 2 (E.diagonalMeasure (e j))) 2 ≃ₗᵢ[ℂ] H),
      (∀ f g, (∀ j, g j = SpectralMeasure.CyclicModel.Spec.multiplier
        (E.diagonalMeasure (e j)) (SpectralMeasure.CyclicModel.Spec.coordinate N) (f j)) →
        U g = N (U f)) ∧
      (⨆ j, SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j)).topologicalClosure = ⊤ := by
  classical
  obtain ⟨e, horth, htotal⟩ := countable_cyclic_generators N hN
  choose V hV using fun j =>
    SpectralMeasure.ArbitraryCyclicSum.local_cyclic_model N hN E hE (e j)
  let A (j : ℕ) : Lp ℂ 2 (E.diagonalMeasure (e j)) →ₗᵢ[ℂ] H :=
    (SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j)).subtypeₗᵢ.comp
      (V j).toLinearIsometry
  have hA : OrthogonalFamily ℂ (fun j => Lp ℂ 2 (E.diagonalMeasure (e j))) A := by
    intro i j hij x y
    exact (horth hij).inner_eq (V i x).property (V j y).property
  have hrange (j : ℕ) : LinearMap.range (A j).toLinearMap =
      SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j) := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      exact (V j f).property
    · intro hx
      obtain ⟨f, hf⟩ := (V j).surjective ⟨x, hx⟩
      exact ⟨f, congrArg (fun y : SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j) =>
        (y : H)) hf⟩
  let hsum : IsHilbertSum ℂ (fun j => Lp ℂ 2 (E.diagonalMeasure (e j))) A :=
    IsHilbertSum.mk hA (by simp_rw [hrange]; exact le_of_eq htotal.symm)
  refine ⟨e, hsum.linearIsometryEquiv.symm, ?_, htotal⟩
  intro f g hfg
  have hsumN := (hsum.hasSum_linearIsometryEquiv_symm f).map N N.continuous
  rw [← hsumN.tsum_eq, hsum.linearIsometryEquiv_symm_apply]
  apply tsum_congr
  intro j
  rw [hfg j]
  exact hV j (f j)

/-- The scalar cyclic model with its measures on ℂ, rather than an abstract
copy of the spectrum. Covariance is stated by the a.e. multiplication formula,
so it can be combined directly with RN transport and supported L² packing. -/
theorem countable_complex_scalar_model [TopologicalSpace.SeparableSpace H]
    (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
    (hE : SpectralMeasure.NormalPVM.Spec.Resolves N E) :
    ∃ (e : ℕ → H)
      (U : lp (fun j => Lp ℂ 2 (spectrumMeasure N (E.diagonalMeasure (e j)))) 2 ≃ₗᵢ[ℂ] H),
      (∀ f g, (∀ j, g j =ᵐ[spectrumMeasure N (E.diagonalMeasure (e j))]
        fun z => z * f j z) → U g = N (U f)) ∧
      (⨆ j, SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j)).topologicalClosure = ⊤ := by
  classical
  obtain ⟨e, horth, htotal⟩ := countable_cyclic_generators N hN
  choose V hV using fun j =>
    SpectralMeasure.ArbitraryCyclicSum.local_cyclic_model N hN E hE (e j)
  let ν (j : ℕ) := E.diagonalMeasure (e j)
  let P (j : ℕ) : Lp ℂ 2 (spectrumMeasure N (ν j)) ≃ₗᵢ[ℂ] Lp ℂ 2 (ν j) :=
    ScalarPushforward.equivalence (ν j) Subtype.val
      (MeasurableEmbedding.subtype_coe (spectrum.isCompact N).isClosed.measurableSet)
  let W (j : ℕ) := (P j).trans (V j)
  let A (j : ℕ) : Lp ℂ 2 (spectrumMeasure N (ν j)) →ₗᵢ[ℂ] H :=
    (SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j)).subtypeₗᵢ.comp
      (W j).toLinearIsometry
  have hA : OrthogonalFamily ℂ (fun j => Lp ℂ 2 (spectrumMeasure N (ν j))) A := by
    intro i j hij x y
    exact (horth hij).inner_eq (W i x).property (W j y).property
  have hrange (j : ℕ) : LinearMap.range (A j).toLinearMap =
      SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j) := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      exact (W j f).property
    · intro hx
      obtain ⟨f, hf⟩ := (W j).surjective ⟨x, hx⟩
      exact ⟨f, congrArg (fun y : SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j) =>
        (y : H)) hf⟩
  let hsum : IsHilbertSum ℂ (fun j => Lp ℂ 2 (spectrumMeasure N (ν j))) A :=
    IsHilbertSum.mk hA (by simp_rw [hrange]; exact le_of_eq htotal.symm)
  refine ⟨e, hsum.linearIsometryEquiv.symm, ?_, htotal⟩
  intro f g hfg
  have hsumN := (hsum.hasSum_linearIsometryEquiv_symm f).map N N.continuous
  rw [← hsumN.tsum_eq, hsum.linearIsometryEquiv_symm_apply]
  apply tsum_congr
  intro j
  have hP : P j (g j) = SpectralMeasure.CyclicModel.Spec.multiplier (ν j)
      (SpectralMeasure.CyclicModel.Spec.coordinate N) (P j (f j)) := by
    apply Lp.ext
    have hgf : ∀ᵐ (z : spectrum ℂ N) ∂(ν j), g j (z : ℂ) = (z : ℂ) * f j (z : ℂ) :=
      ae_of_ae_map measurable_subtype_coe.aemeasurable (hfg j)
    have hPg := ScalarPushforward.equivalence_ae (ν j) Subtype.val
      (MeasurableEmbedding.subtype_coe (spectrum.isCompact N).isClosed.measurableSet) (g j)
    have hPf := ScalarPushforward.equivalence_ae (ν j) Subtype.val
      (MeasurableEmbedding.subtype_coe (spectrum.isCompact N).isClosed.measurableSet) (f j)
    filter_upwards [hgf, hPg, hPf,
      SpectralMeasure.CyclicModel.multiplier_apply (ν j)
        (SpectralMeasure.CyclicModel.Spec.coordinate N) (P j (f j))] with z hgf hPg hPf hm
    change P j (g j) z = _
    change P j (g j) z = g j (z : ℂ) at hPg
    change P j (f j) z = f j (z : ℂ) at hPf
    change _ = (z : ℂ) * P j (f j) z at hm
    rw [hPf] at hm
    exact hPg.trans (hgf.trans hm.symm)
  change (V j (P j (g j)) : H) = N (V j (P j (f j)) : H)
  rw [hP]
  exact hV j (P j (f j))

/-- A bounded operator commuting with the generated C*-algebra is determined
by its action on any total family of cyclic generators. -/
theorem operator_eq_zero_of_cyclic_generators (N T : H →L[ℂ] H) (e : ℕ → H)
    (htotal : (⨆ j, SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j)).topologicalClosure = ⊤)
    (hcomm : ∀ a : StarAlgebra.elemental ℂ N, Commute T (a : H →L[ℂ] H))
    (he : ∀ j, T (e j) = 0) : T = 0 := by
  have hcyc (j : ℕ) : SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j) ≤ T.ker := by
    apply SpectralMeasure.ArbitraryCyclicSum.cyclicSpace_le N (e j) T.ker T.isClosed_ker (he j)
    intro a x hx
    change T ((a : H →L[ℂ] H) x) = 0
    calc
      T ((a : H →L[ℂ] H) x) = (a : H →L[ℂ] H) (T x) :=
        congrArg (fun S : H →L[ℂ] H => S x) (hcomm a).eq
      _ = 0 := by rw [show T x = 0 from hx, map_zero]
  have hker : (⊤ : Submodule ℂ H) ≤ T.ker := by
    rw [← htotal]
    exact Submodule.topologicalClosure_minimal _ (iSup_le hcyc) T.isClosed_ker
  ext x
  exact hker (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H))

/-- The common null ideal of the cyclic diagonal measures is exactly the
null ideal of the original PVM, not merely an inclusion in one direction. -/
theorem spectralProjection_zero_iff_diagonal (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
    (hE : SpectralMeasure.NormalPVM.Spec.Resolves N E) (e : ℕ → H)
    (htotal : (⨆ j, SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j)).topologicalClosure = ⊤)
    (B : Set (spectrum ℂ N)) (hB : MeasurableSet B) :
    E B = 0 ↔ ∀ j, E.diagonalMeasure (e j) B = 0 := by
  constructor
  · intro hz j
    simp [E.diagonalMeasure_apply (e j) B hB, hz]
  · intro hz
    apply operator_eq_zero_of_cyclic_generators N (E B) e htotal
    · intro a
      have ha : (a : H →L[ℂ] H) ∈ NormalAlgebraControlMeasure.Spec.normalAlgebra N :=
        StarAlgebra.elemental.le_of_mem
          (NormalAlgebraControlMeasure.normalAlgebra_normClosed N)
          (NormalAlgebraControlMeasure.generator_mem N) a.property
      exact NormalAlgebraControlMeasure.normalAlgebra_abelian N hN _
        (NormalAlgebraControlMeasure.spectralProjection_mem hN E hE B hB) _ ha
    · intro j
      have hj := hz j
      rw [E.diagonalMeasure_apply (e j) B hB] at hj
      have hs : ‖E B (e j)‖ ^ 2 = 0 :=
        le_antisymm (ENNReal.ofReal_eq_zero.mp hj) (sq_nonneg _)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)

/-- Every scalar cyclic measure, extended to ℂ, is dominated by any scalar
control measure for this resolution. -/
theorem diagonal_absolutelyContinuous (N : H →L[ℂ] H)
    (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
    (μ : Measure ℂ) (hμ : Spec.ComplexControlMeasure N E μ) (e : H) :
    spectrumMeasure N (E.diagonalMeasure e) ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro B hB hnull
  rw [spectrumMeasure, Measure.map_apply measurable_subtype_coe hB,
    E.diagonalMeasure_apply e _ (measurable_subtype_coe hB), (hμ B hB).mpr hnull]
  simp

/-- The domination above has the necessary converse for a total cyclic
family: a common scalar null set is a control-measure null set. -/
theorem controlMeasure_zero_iff_diagonal (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
    (hE : SpectralMeasure.NormalPVM.Spec.Resolves N E)
    (μ : Measure ℂ) (hμ : Spec.ComplexControlMeasure N E μ) (e : ℕ → H)
    (htotal : (⨆ j, SpectralMeasure.ArbitraryCyclicSum.Spec.cyclicSpace N (e j)).topologicalClosure = ⊤)
    (B : Set ℂ) (hB : MeasurableSet B) :
    μ B = 0 ↔ ∀ j, spectrumMeasure N (E.diagonalMeasure (e j)) B = 0 := by
  rw [← hμ B hB, spectralProjection_zero_iff_diagonal N hN E hE e htotal _
    (measurable_subtype_coe hB)]
  apply forall_congr'
  intro j
  rw [spectrumMeasure, Measure.map_apply measurable_subtype_coe hB]

/-- For finite measures with the same common null ideal, the positive RN
supports of the family cover almost every point. This also covers μ = 0. -/
theorem rnDeriv_support_cover (μ : Measure ℂ) [IsFiniteMeasure μ]
    (ν : ℕ → Measure ℂ) [∀ j, IsFiniteMeasure (ν j)]
    (hac : ∀ j, ν j ≪ μ)
    (hnull : ∀ B : Set ℂ, MeasurableSet B → (∀ j, ν j B = 0) → μ B = 0) :
    ∀ᵐ z ∂μ, ∃ j, 0 < (ν j).rnDeriv μ z := by
  let Z : Set ℂ := {z | ∀ j, (ν j).rnDeriv μ z = 0}
  have hZ : MeasurableSet Z := by
    change MeasurableSet {z | ∀ j, (ν j).rnDeriv μ z = 0}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_eq_fun
      (Measure.measurable_rnDeriv (ν j) μ) (measurable_const (a := (0 : ℝ≥0∞)))
  have hνZ (j : ℕ) : ν j Z = 0 := by
    rw [← Measure.withDensity_rnDeriv_eq (ν j) μ (hac j), withDensity_apply _ hZ]
    exact setLIntegral_eq_zero hZ (fun z hz => hz j)
  have hμZ : μ Z = 0 := hnull Z hZ hνZ
  apply ae_iff.mpr
  simpa [Z, not_lt, le_zero_iff] using hμZ

namespace LpFamily
variable {I : Type*} {E F : I → Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℂ (E j)]
  [∀ j, NormedAddCommGroup (F j)] [∀ j, NormedSpace ℂ (F j)]

def map (T : ∀ j, E j →ₗᵢ[ℂ] F j) : lp E 2 →ₗᵢ[ℂ] lp F 2 where
  toFun x := ⟨fun j => T j (x j), (lp.memℓp x).mono' fun j => (T j).norm_map (x j) |>.le⟩
  map_add' x y := by ext j; exact (T j).map_add (x j) (y j)
  map_smul' c x := by ext j; exact (T j).map_smul c (x j)
  norm_map' x := le_antisymm
    (lp.norm_mono (by norm_num) fun j => (T j).norm_map (x j) |>.le)
    (lp.norm_mono (by norm_num) fun j => (T j).norm_map (x j) |>.ge)

@[simp] theorem map_apply (T : ∀ j, E j →ₗᵢ[ℂ] F j) (x : lp E 2) (j : I) :
    map T x j = T j (x j) := rfl

def productSubmodule (S : ∀ j, Submodule ℂ (F j)) : Submodule ℂ (lp F 2) where
  carrier := {f | ∀ j, f j ∈ S j}
  zero_mem' j := (S j).zero_mem
  add_mem' hf hg j := (S j).add_mem (hf j) (hg j)
  smul_mem' c _f hf j := (S j).smul_mem c (hf j)

def supportedMap (T : ∀ j, E j →ₗᵢ[ℂ] F j) (S : ∀ j, Submodule ℂ (F j))
    (hS : ∀ j x, T j x ∈ S j) : lp E 2 →ₗᵢ[ℂ] productSubmodule S where
  toFun f := ⟨map T f, fun j => hS j (f j)⟩
  map_add' f g := Subtype.ext ((map T).map_add f g)
  map_smul' c f := Subtype.ext ((map T).map_smul c f)
  norm_map' f := (map T).norm_map f

theorem supportedMap_surjective (T : ∀ j, E j →ₗᵢ[ℂ] F j)
    (S : ∀ j, Submodule ℂ (F j)) (hS : ∀ j x, T j x ∈ S j)
    (honto : ∀ j y, y ∈ S j → ∃ x, T j x = y) :
    Function.Surjective (supportedMap T S hS) := by
  intro f
  choose g hg using fun j => honto j (f.val j) (f.property j)
  have hnorm (j : I) : ‖g j‖ = ‖f.val j‖ := by rw [← hg j, (T j).norm_map]
  let x : lp E 2 := ⟨g, (lp.memℓp f.val).mono' fun j => (hnorm j).le⟩
  refine ⟨x, Subtype.ext ?_⟩
  ext j
  exact hg j

def supportedEquivalence (T : ∀ j, E j →ₗᵢ[ℂ] F j)
    (S : ∀ j, Submodule ℂ (F j)) (hS : ∀ j x, T j x ∈ S j)
    (honto : ∀ j y, y ∈ S j → ∃ x, T j x = y) :
    lp E 2 ≃ₗᵢ[ℂ] productSubmodule S :=
  LinearIsometryEquiv.ofSurjective (supportedMap T S hS)
    (supportedMap_surjective T S hS honto)

@[simp] theorem supportedEquivalence_apply (T : ∀ j, E j →ₗᵢ[ℂ] F j)
    (S : ∀ j, Submodule ℂ (F j)) (hS : ∀ j x, T j x ∈ S j)
    (honto : ∀ j y, y ∈ S j → ∃ x, T j x = y) (f : lp E 2) (j : I) :
    (supportedEquivalence T S hS honto f).val j = T j (f j) := rfl
def restrictEquivalence {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (U : X ≃ₗᵢ[ℂ] Y) (S : Submodule ℂ X) (T : Submodule ℂ Y)
    (h : ∀ x, x ∈ S ↔ U x ∈ T) : S ≃ₗᵢ[ℂ] T where
  toFun x := ⟨U x, (h x).mp x.property⟩
  invFun y := ⟨U.symm y, (h (U.symm y)).mpr (by simpa only [LinearIsometryEquiv.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext (U.symm_apply_apply x)
  right_inv y := Subtype.ext (U.apply_symm_apply y)
  map_add' x y := Subtype.ext (U.map_add x y)
  map_smul' c x := Subtype.ext (U.map_smul c x)
  norm_map' x := U.norm_map x

end LpFamily

namespace L2Packing
abbrev Seq := lp (fun _ : ℕ => ℂ) 2
variable (μ : Measure ℂ)

def scalarSingle (j : ℕ) : ℂ →L[ℂ] Seq :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 j

def coord (j : ℕ) : Lp Seq 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j).compLpL 2 μ

lemma coord_ae (j : ℕ) (f : Lp Seq 2 μ) :
    coord μ j f =ᵐ[μ] fun z => f z j :=
  (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j).coeFn_compLp f

def single (j : ℕ) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp Seq 2 μ where
  toLinearMap := (scalarSingle j).compLpₗ 2 μ
  norm_map' f := by
    change ‖(scalarSingle j).compLp f‖ = ‖f‖
    apply le_antisymm
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(scalarSingle j).coeFn_compLp f] with z hz
      rw [hz]
      simp [scalarSingle]
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(scalarSingle j).coeFn_compLp f] with z hz
      rw [hz]
      simp [scalarSingle]

lemma single_ae (j : ℕ) (g : Lp ℂ 2 μ) :
    single μ j g =ᵐ[μ] fun z => lp.single 2 j (g z) :=
  (scalarSingle j).coeFn_compLp g

lemma coord_single (i j : ℕ) (g : Lp ℂ 2 μ) :
    coord μ i (single μ j g) = if i = j then g else 0 := by
  classical
  by_cases h : i = j
  · subst i
    simp only [ite_true]
    apply Lp.ext
    filter_upwards [coord_ae μ j (single μ j g), single_ae μ j g] with z hi hj
    rw [hi, hj]
    simp
  · simp only [ite_eq_right h]
    apply Lp.ext
    filter_upwards [coord_ae μ i (single μ j g), single_ae μ j g,
      Lp.coeFn_zero ℂ 2 μ] with z hi hj h0
    rw [hi, hj, h0]
    simp [lp.single_apply, h]

lemma inner_single (j : ℕ) (g : Lp ℂ 2 μ) (f : Lp Seq 2 μ) :
    inner ℂ (single μ j g) f = inner ℂ g (coord μ j f) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [single_ae μ j g, coord_ae μ j f] with z hj hf
  rw [hj, hf, lp.inner_single_left]

lemma ortho : OrthogonalFamily ℂ (fun _ : ℕ => Lp ℂ 2 μ) (single μ) := by
  intro i j hij f g
  rw [inner_single, coord_single]
  simp [hij]

lemma coordinates_ext (f g : Lp Seq 2 μ)
    (h : ∀ j, coord μ j f = coord μ j g) : f = g := by
  apply Lp.ext
  have hall : ∀ j, ∀ᵐ z ∂μ, f z j = g z j := by
    intro j
    have heq : coord μ j f =ᵐ[μ] coord μ j g := by rw [h j]
    filter_upwards [coord_ae μ j f, coord_ae μ j g, heq] with z hf hg hz
    simpa [hf, hg] using hz
  filter_upwards [ae_all_iff.mpr hall] with z hz
  exact lp.ext (funext hz)

lemma total : (⊤ : Submodule ℂ (Lp Seq 2 μ)) ≤
    (⨆ j, LinearMap.range (single μ j).toLinearMap).topologicalClosure := by
  let K : Submodule ℂ (Lp Seq 2 μ) := ⨆ j, LinearMap.range (single μ j).toLinearMap
  have hbot : Kᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    have hcoords : ∀ j, coord μ j f = 0 := by
      intro j
      have h := Submodule.inner_right_of_mem_orthogonal
        (show single μ j (coord μ j f) ∈ K from
          Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ _)) hf
      rw [inner_single] at h
      exact inner_self_eq_zero.mp h
    apply coordinates_ext μ f 0
    intro j
    simpa using hcoords j
  rw [← K.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]

lemma hilbertSum : IsHilbertSum ℂ (fun _ : ℕ => Lp ℂ 2 μ) (single μ) :=
  IsHilbertSum.mk (ortho μ) (total μ)

def pack : lp (fun _ : ℕ => Lp ℂ 2 μ) 2 ≃ₗᵢ[ℂ] Lp Seq 2 μ :=
  (hilbertSum μ).linearIsometryEquiv.symm

lemma coord_pack (j : ℕ) (x : lp (fun _ : ℕ => Lp ℂ 2 μ) 2) :
    coord μ j (pack μ x) = x j := by
  have hs := (hilbertSum μ).hasSum_linearIsometryEquiv_symm x
  have he := (coord μ j).hasSum hs
  simp only [coord_single] at he
  apply he.unique
  convert hasSum_ite_eq j (x j) using 1
  ext i
  by_cases h : i = j
  · subst i; simp
  · simp [h, Ne.symm h]

lemma pack_ae (x : lp (fun _ : ℕ => Lp ℂ 2 μ) 2) :
    ∀ᵐ z ∂μ, ∀ j, pack μ x z j = x j z := by
  apply ae_all_iff.mpr
  intro j
  have h := coord_ae μ j (pack μ x)
  rw [coord_pack] at h
  exact h.symm

end L2Packing

namespace SupportedSections
abbrev Seq := lp (fun _ : ℕ => ℂ) 2

def scalar (μ : Measure ℂ) (A : Set ℂ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | ∀ᵐ z ∂μ, z ∉ A → f z = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z hz _
    exact hz
  add_mem' {f} {g} hf hg := by
    filter_upwards [hf, hg, Lp.coeFn_add f g] with z hf hg hadd hz
    simp only [hadd, Pi.add_apply, hf hz, hg hz, add_zero]
  smul_mem' c f hf := by
    filter_upwards [hf, Lp.coeFn_smul c f] with z hf hsmul hz
    simp only [hsmul, Pi.smul_apply, hf hz, smul_zero]

def sections (μ : Measure ℂ) (A : ℕ → Set ℂ) : Submodule ℂ (Lp Seq 2 μ) where
  carrier := {f | ∀ᵐ z ∂μ, ∀ j, z ∉ A j → f z j = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero Seq 2 μ] with z hz j _
    rw [hz]
    rfl
  add_mem' {f} {g} hf hg := by
    filter_upwards [hf, hg, Lp.coeFn_add f g] with z hf hg hadd j hz
    change _ = 0
    rw [hadd]
    change f z j + g z j = 0
    rw [hf j hz, hg j hz, add_zero]
  smul_mem' c f hf := by
    filter_upwards [hf, Lp.coeFn_smul c f] with z hf hsmul j hz
    change _ = 0
    rw [hsmul]
    change c • f z j = 0
    rw [hf j hz, smul_zero]
end SupportedSections

namespace ScalarRN
variable {α : Type*} [MeasurableSpace α]
variable (ν μ : Measure α) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
def weight (z : α) : ℝ := Real.sqrt ((ν.rnDeriv μ z).toReal)
omit [IsFiniteMeasure ν] [IsFiniteMeasure μ] in
theorem weight_measurable : Measurable (weight ν μ) :=
  Real.continuous_sqrt.measurable.comp (Measure.measurable_rnDeriv ν μ).ennreal_toReal
omit [IsFiniteMeasure ν] [IsFiniteMeasure μ] in
theorem weight_sq (z : α) : weight ν μ z ^ 2 = (ν.rnDeriv μ z).toReal := by
  exact Real.sq_sqrt ENNReal.toReal_nonneg

omit [IsFiniteMeasure ν] [IsFiniteMeasure μ] in
theorem enorm_weight_sq (z : α) (hz : ν.rnDeriv μ z ≠ ∞) :
    ‖weight ν μ z‖ₑ ^ 2 = ν.rnDeriv μ z := by
  change ‖Real.sqrt ((ν.rnDeriv μ z).toReal)‖ₑ ^ 2 = _
  rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _), ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hz]

theorem eLpNorm_weight_smul (hac : ν ≪ μ) (f : α → ℂ)
    (hf : StronglyMeasurable f) :
    eLpNorm (fun z => weight ν μ z • f z) 2 μ = eLpNorm f 2 ν := by
  have hwf : StronglyMeasurable (fun z => weight ν μ z • f z) :=
    (weight_measurable ν μ).stronglyMeasurable.smul hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hwf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  congr 1
  simp only [ENNReal.toReal_ofNat]
  simp_rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  calc
    ∫⁻ z, ‖weight ν μ z • f z‖ₑ ^ 2 ∂μ =
      ∫⁻ z, ν.rnDeriv μ z * ‖f z‖ₑ ^ 2 ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [Measure.rnDeriv_ne_top ν μ] with z hz
        rw [enorm_smul, mul_pow, enorm_weight_sq ν μ z hz]
    _ = _ := lintegral_rnDeriv_mul hac (hf.enorm.pow_const 2).aemeasurable

omit [IsFiniteMeasure ν] [IsFiniteMeasure μ] in
theorem weight_eq_zero_of_rnDeriv_eq_zero {z : α} (hz : ν.rnDeriv μ z = 0) :
    weight ν μ z = 0 := by simp [weight, hz]

theorem weighted_congr {f g : α → ℂ} (hfg : f =ᵐ[ν] g) :
    (fun z => weight ν μ z • f z) =ᵐ[μ] fun z => weight ν μ z • g z := by
  filter_upwards [Measure.ae_rnDeriv_ne_zero_imp_of_ae μ hfg] with z hz
  by_cases hr : ν.rnDeriv μ z = 0
  · simp [weight_eq_zero_of_rnDeriv_eq_zero ν μ hr]
  · rw [hz hr]

theorem memLp_weight_smul (hac : ν ≪ μ) (f : Lp ℂ 2 ν) :
    MemLp (fun z => weight ν μ z • f z) 2 μ := by
  change eLpNorm _ _ _ < ∞
  rw [eLpNorm_weight_smul ν μ hac f (Lp.stronglyMeasurable f)]
  exact Lp.eLpNorm_lt_top f

def transport (hac : ν ≪ μ) : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_weight_smul ν μ hac f).toLp (fun z => weight ν μ z • f z)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_weight_smul ν μ hac (f+g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_weight_smul ν μ hac f).toLp _) ((memLp_weight_smul ν μ hac g).toLp _),
      (memLp_weight_smul ν μ hac f).coeFn_toLp,
      (memLp_weight_smul ν μ hac g).coeFn_toLp,
      weighted_congr ν μ (Lp.coeFn_add f g)] with z hsum htarget hf hg hfg
    simp only [Pi.add_apply] at htarget
    rw [hsum, htarget, hf, hg]
    exact hfg.trans (smul_add _ _ _)
  map_smul' c f := by
    apply Lp.ext
    simp only [RingHom.id_apply]
    filter_upwards [(memLp_weight_smul ν μ hac (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_weight_smul ν μ hac f).toLp _),
      (memLp_weight_smul ν μ hac f).coeFn_toLp,
      weighted_congr ν μ (Lp.coeFn_smul c f)] with z hcf htarget hf hcf'
    simp only [Pi.smul_apply] at htarget
    rw [hcf, htarget, hf]
    rw [hcf']
    change weight ν μ z • (c • f z) = c • weight ν μ z • f z
    exact smul_comm _ _ _
  norm_map' f := by
    change ‖(memLp_weight_smul ν μ hac f).toLp (fun z => weight ν μ z • f z)‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_weight_smul ν μ hac f (Lp.stronglyMeasurable f), Lp.norm_def]

theorem transport_apply (hac : ν ≪ μ) (f : Lp ℂ 2 ν) :
    transport ν μ hac f =ᵐ[μ] fun z => weight ν μ z • f z :=
  (memLp_weight_smul ν μ hac f).coeFn_toLp

theorem transport_supported (hac : ν ≪ μ) (f : Lp ℂ 2 ν) :
    ∀ᵐ z ∂μ, ν.rnDeriv μ z = 0 → transport ν μ hac f z = 0 := by
  filter_upwards [transport_apply ν μ hac f] with z hz hr
  rw [hz, weight_eq_zero_of_rnDeriv_eq_zero ν μ hr, zero_smul]

omit [IsFiniteMeasure ν] [IsFiniteMeasure μ] in
theorem weight_ne_zero {z : α} (h0 : ν.rnDeriv μ z ≠ 0)
    (htop : ν.rnDeriv μ z ≠ ∞) : weight ν μ z ≠ 0 := by
  exact (Real.sqrt_pos.mpr (ENNReal.toReal_pos h0 htop)).ne'

omit [IsFiniteMeasure μ] in
theorem weighted_inverse_ae (g : Lp ℂ 2 μ)
    (hg : ∀ᵐ z ∂μ, ν.rnDeriv μ z = 0 → g z = 0) :
    (fun z => weight ν μ z • ((weight ν μ z)⁻¹ • g z)) =ᵐ[μ] g := by
  filter_upwards [Measure.rnDeriv_ne_top ν μ, hg] with z hz hg
  by_cases h0 : ν.rnDeriv μ z = 0
  · rw [hg h0, smul_zero, smul_zero]
  · rw [smul_smul, mul_inv_cancel₀ (weight_ne_zero ν μ h0 hz), one_smul]

theorem memLp_inverse_weight_smul (hac : ν ≪ μ) (g : Lp ℂ 2 μ)
    (hg : ∀ᵐ z ∂μ, ν.rnDeriv μ z = 0 → g z = 0) :
    MemLp (fun z => (weight ν μ z)⁻¹ • g z) 2 ν := by
  have hmeas : StronglyMeasurable (fun z => (weight ν μ z)⁻¹ • g z) :=
    (weight_measurable ν μ).inv.stronglyMeasurable.smul (Lp.stronglyMeasurable g)
  change eLpNorm _ _ _ < ∞
  rw [← eLpNorm_weight_smul ν μ hac _ hmeas,
    eLpNorm_congr_ae (weighted_inverse_ae ν μ g hg)]
  exact Lp.eLpNorm_lt_top g

theorem transport_surjective_supported (hac : ν ≪ μ) (g : Lp ℂ 2 μ)
    (hg : ∀ᵐ z ∂μ, ν.rnDeriv μ z = 0 → g z = 0) :
    ∃ f : Lp ℂ 2 ν, transport ν μ hac f = g := by
  let hf := memLp_inverse_weight_smul ν μ hac g hg
  refine ⟨hf.toLp _, ?_⟩
  apply Lp.ext
  exact (transport_apply ν μ hac _).trans
    ((weighted_congr ν μ hf.coeFn_toLp).trans (weighted_inverse_ae ν μ g hg))

theorem transport_mul_iff (hac : ν ≪ μ) (φ : α → ℂ) (f g : Lp ℂ 2 ν) :
    (transport ν μ hac g =ᵐ[μ] fun z => φ z * transport ν μ hac f z) ↔
      g =ᵐ[ν] fun z => φ z * f z := by
  constructor
  · intro h
    filter_upwards [hac.ae_le h, hac.ae_le (transport_apply ν μ hac f),
      hac.ae_le (transport_apply ν μ hac g), Measure.rnDeriv_pos hac,
      hac.ae_le (Measure.rnDeriv_ne_top ν μ)] with z hz hf hg hpos htop
    apply smul_right_injective ℂ (weight_ne_zero ν μ hpos.ne' htop)
    change weight ν μ z • g z = weight ν μ z • (φ z * f z)
    rw [← mul_smul_comm, ← hf, ← hz, hg]
  · intro h
    filter_upwards [transport_apply ν μ hac f, transport_apply ν μ hac g,
      weighted_congr ν μ h] with z hf hg hfg
    rw [hg, hf]
    exact hfg.trans (mul_smul_comm _ _ _).symm
end ScalarRN



namespace SupportedSections
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ComplexConjugate

variable (μ : Measure ℂ) (A : ℕ → Set ℂ)

lemma pack_supported_iff (f : lp (fun _ : ℕ => Lp ℂ 2 μ) 2) :
    f ∈ LpFamily.productSubmodule (fun j => scalar μ (A j)) ↔
      L2Packing.pack μ f ∈ sections μ A := by
  change (∀ j, ∀ᵐ z ∂μ, z ∉ A j → f j z = 0) ↔
    ∀ᵐ z ∂μ, ∀ j, z ∉ A j → L2Packing.pack μ f z j = 0
  constructor
  · intro h
    filter_upwards [ae_all_iff.mpr h, L2Packing.pack_ae μ f] with z hz hp j hj
    rw [hp j]
    exact hz j hj
  · intro h j
    filter_upwards [h, L2Packing.pack_ae μ f] with z hz hp hj
    rw [← hp j]
    exact hz j hj

def packingEquivalence :
    LpFamily.productSubmodule (fun j => scalar μ (A j)) ≃ₗᵢ[ℂ] sections μ A :=
  LpFamily.restrictEquivalence (L2Packing.pack μ)
    (LpFamily.productSubmodule (fun j => scalar μ (A j))) (sections μ A)
    (pack_supported_iff μ A)

lemma packingEquivalence_ae
    (f : LpFamily.productSubmodule (fun j => scalar μ (A j))) :
    ∀ᵐ z ∂μ, ∀ j,
      (packingEquivalence μ A f : Lp Seq 2 μ) z j = f.val j z :=
  L2Packing.pack_ae μ f.val

lemma unpack_ae (f : Lp Seq 2 μ) :
    ∀ᵐ z ∂μ, ∀ j, (L2Packing.pack μ).symm f j z = f z j := by
  have h := L2Packing.pack_ae μ ((L2Packing.pack μ).symm f)
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    h.mono (fun z hz j => (hz j).symm)

lemma packingEquivalence_symm_ae (f : sections μ A) :
    ∀ᵐ z ∂μ, ∀ j,
      ((packingEquivalence μ A).symm f).val j z = (f : Lp Seq 2 μ) z j :=
  unpack_ae μ f.val

lemma pack_covariant (f g : lp (fun _ : ℕ => Lp ℂ 2 μ) 2)
    (h : ∀ j, ∀ᵐ z ∂μ, g j z = z * f j z) :
    L2Packing.pack μ g =ᵐ[μ] fun z => z • L2Packing.pack μ f z := by
  filter_upwards [L2Packing.pack_ae μ f, L2Packing.pack_ae μ g,
    ae_all_iff.mpr h] with z hf hg hz
  apply lp.ext
  funext j
  change L2Packing.pack μ g z j = z * L2Packing.pack μ f z j
  rw [hf j, hg j, hz j]

lemma unpack_covariant (f g : Lp Seq 2 μ)
    (h : g =ᵐ[μ] fun z => z • f z) :
    ∀ j, ∀ᵐ z ∂μ,
      (L2Packing.pack μ).symm g j z = z * (L2Packing.pack μ).symm f j z := by
  intro j
  filter_upwards [unpack_ae μ f, unpack_ae μ g, h] with z hf hg hz
  rw [hg j, hf j, hz]
  rfl

lemma packingEquivalence_covariant
    (f g : LpFamily.productSubmodule (fun j => scalar μ (A j)))
    (h : ∀ j, ∀ᵐ z ∂μ, g.val j z = z * f.val j z) :
    (packingEquivalence μ A g : Lp Seq 2 μ) =ᵐ[μ]
      fun z => z • (packingEquivalence μ A f : Lp Seq 2 μ) z :=
  pack_covariant μ f.val g.val h

lemma packingEquivalence_symm_covariant (f g : sections μ A)
    (h : (g : Lp Seq 2 μ) =ᵐ[μ] fun z => z • (f : Lp Seq 2 μ) z) :
    ∀ j, ∀ᵐ z ∂μ,
      ((packingEquivalence μ A).symm g).val j z =
        z * ((packingEquivalence μ A).symm f).val j z :=
  unpack_covariant μ f.val g.val h

end SupportedSections

namespace RNFamily
variable (μ : Measure ℂ) [IsFiniteMeasure μ]
  (ν : ℕ → Measure ℂ) [∀ j, IsFiniteMeasure (ν j)] (hac : ∀ j, ν j ≪ μ)
def supports (j : ℕ) : Set ℂ := {z | 0 < (ν j).rnDeriv μ z}
theorem transport_supported (j : ℕ) (f : Lp ℂ 2 (ν j)) :
    ScalarRN.transport (ν j) μ (hac j) f ∈ SupportedSections.scalar μ (supports μ ν j) := by
  filter_upwards [ScalarRN.transport_supported (ν j) μ (hac j) f] with z hz hnot
  exact hz (le_zero_iff.mp (le_of_not_gt hnot))
theorem transport_onto (j : ℕ) (g : Lp ℂ 2 μ)
    (hg : g ∈ SupportedSections.scalar μ (supports μ ν j)) :
    ∃ f, ScalarRN.transport (ν j) μ (hac j) f = g := by
  apply ScalarRN.transport_surjective_supported (ν j) μ (hac j) g
  filter_upwards [hg] with z hz hr
  exact hz (by simp [supports, hr])
def equivalence : lp (fun j => Lp ℂ 2 (ν j)) 2 ≃ₗᵢ[ℂ]
    LpFamily.productSubmodule (fun j => SupportedSections.scalar μ (supports μ ν j)) :=
  LpFamily.supportedEquivalence (fun j => ScalarRN.transport (ν j) μ (hac j))
    (fun j => SupportedSections.scalar μ (supports μ ν j))
    (transport_supported μ ν hac) (transport_onto μ ν hac)
@[simp] theorem equivalence_apply (f : lp (fun j => Lp ℂ 2 (ν j)) 2) (j : ℕ) :
    (equivalence μ ν hac f).val j = ScalarRN.transport (ν j) μ (hac j) (f j) := rfl

theorem equivalence_symm_covariant
    (f g : LpFamily.productSubmodule (fun j => SupportedSections.scalar μ (supports μ ν j)))
    (h : ∀ j, g.val j =ᵐ[μ] fun z => z * f.val j z) :
    ∀ j, (equivalence μ ν hac).symm g j =ᵐ[ν j]
      fun z => z * (equivalence μ ν hac).symm f j z := by
  intro j
  apply (ScalarRN.transport_mul_iff (ν j) μ (hac j) (fun z => z) _ _).mp
  simpa only [← equivalence_apply, LinearIsometryEquiv.apply_symm_apply] using h j

end RNFamily

namespace FiberReordering
attribute [local instance] Classical.propDecidable
abbrev Seq := MultiplicityModel.Spec.SequenceSpace

def supported (s : Set ℕ) : Submodule ℂ Seq where
  carrier := {x | ∀ j, j ∉ s → x j = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j hj; change x j + y j = 0; rw [hx j hj, hy j hj, add_zero]
  smul_mem' := by intro c x hx j hj; change c • x j = 0; rw [hx j hj, smul_zero]

def reorderFn {s t : Set ℕ} (e : s ≃ t) (x : Seq) (k : ℕ) : ℂ :=
  if hk : k ∈ t then x (e.symm ⟨k, hk⟩) else 0

theorem reorderFn_mem {s t : Set ℕ} (e : s ≃ t) (x : Seq) :
    Memℓp (reorderFn e x) 2 := by
  classical
  apply memℓp_gen
  have hs : Summable (fun j : s => ‖x j‖ ^ (2 : ℝ≥0∞).toReal) :=
    ((lp.memℓp x).summable (by norm_num)).subtype _
  have ht : Summable (fun k : t => ‖x (e.symm k)‖ ^ (2 : ℝ≥0∞).toReal) :=
    (e.symm.summable_iff).mpr hs
  have htr : Summable (fun k : t => ‖reorderFn e x k‖ ^ (2 : ℝ≥0∞).toReal) := by
    convert ht using 1
    funext k
    simp only [reorderFn, dite_eq_left k.property, Subtype.coe_eta]
  have hh := (summable_subtype_iff_indicator (f := fun k : ℕ => ‖reorderFn e x k‖ ^ (2 : ℝ≥0∞).toReal) (s := t)).mp htr
  convert hh using 1
  ext k
  by_cases hk : k ∈ t
  · simp [Set.indicator_of_mem hk]
  · simp [reorderFn, hk]

def reorder {s t : Set ℕ} (e : s ≃ t) (x : Seq) : Seq :=
  ⟨reorderFn e x, reorderFn_mem e x⟩

@[simp] theorem reorder_apply {s t : Set ℕ} (e : s ≃ t) (x : Seq) (k : ℕ) :
    reorder e x k = if hk : k ∈ t then x (e.symm ⟨k, hk⟩) else 0 := rfl

theorem reorder_supported {s t : Set ℕ} (e : s ≃ t) (x : Seq) :
    reorder e x ∈ supported t := by
  intro k hk
  simp [reorder_apply, hk]

theorem reorder_tsum {s t : Set ℕ} (e : s ≃ t) (x : Seq) :
    (∑' k, ‖reorder e x k‖ ^ (2 : ℝ≥0∞).toReal) =
      ∑' j : s, ‖x j‖ ^ (2 : ℝ≥0∞).toReal := by
  classical
  rw [← tsum_subtype_eq_of_support_subset (s := t) (f := fun k => ‖reorder e x k‖ ^ (2 : ℝ≥0∞).toReal) ?_]
  · convert e.symm.tsum_eq (fun j : s => ‖x j‖ ^ (2 : ℝ≥0∞).toReal) using 1
    apply tsum_congr
    intro k
    simp only [reorder_apply, dite_eq_left k.property, Subtype.coe_eta]
  · intro k hk
    by_contra hkt
    have hzero := reorder_supported e x k hkt
    apply hk
    change ‖reorder e x k‖ ^ (2 : ℝ≥0∞).toReal = 0
    rw [hzero]
    norm_num

theorem reorder_norm_le {s t : Set ℕ} (e : s ≃ t) (x : Seq) :
    ‖reorder e x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x)
  rw [reorder_tsum, lp.norm_rpow_eq_tsum (by norm_num) x]
  exact ((lp.memℓp x).summable (by norm_num)).tsum_subtype_le _ s (fun _ => by positivity)

theorem reorder_norm {s t : Set ℕ} (e : s ≃ t) (x : Seq) (hx : x ∈ supported s) :
    ‖reorder e x‖ = ‖x‖ := by
  have hsum : (∑' j : s, ‖x j‖ ^ (2 : ℝ≥0∞).toReal) =
      ∑' j, ‖x j‖ ^ (2 : ℝ≥0∞).toReal := by
    apply tsum_subtype_eq_of_support_subset (s := s) (f := fun j : ℕ => ‖x j‖ ^ (2 : ℝ≥0∞).toReal)
    intro j hj
    by_contra hjs
    simp [hx j hjs] at hj
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp
  rw [lp.norm_rpow_eq_tsum hp, reorder_tsum, hsum, lp.norm_rpow_eq_tsum hp]


theorem reorder_add {s t : Set ℕ} (e : s ≃ t) (x y : Seq) :
    reorder e (x + y) = reorder e x + reorder e y := by
  ext k
  by_cases hk : k ∈ t
  · simp [reorder_apply, hk]
  · simp [reorder_apply, hk]

theorem reorder_smul {s t : Set ℕ} (e : s ≃ t) (c : ℂ) (x : Seq) :
    reorder e (c • x) = c • reorder e x := by
  ext k
  by_cases hk : k ∈ t
  · simp [reorder_apply, hk]
  · simp [reorder_apply, hk]

def reorderCLM {s t : Set ℕ} (e : s ≃ t) : Seq →L[ℂ] Seq :=
  LinearMap.mkContinuous
    { toFun := reorder e
      map_add' := reorder_add e
      map_smul' := reorder_smul e }
    1 (fun x => by simpa using reorder_norm_le e x)

theorem reorder_inverse {s t : Set ℕ} (e : s ≃ t) (x : Seq) (hx : x ∈ supported s) :
    reorder e.symm (reorder e x) = x := by
  ext j
  by_cases hj : j ∈ s
  · simp [reorder_apply, hj, (e ⟨j, hj⟩).property]
  · simpa [reorder_apply, hj] using (hx j hj).symm


def activeEquiv (A : ℕ → Set ℂ) (z : ℂ) :
    {j | z ∈ A j} ≃ {k : ℕ | (k : ℕ∞) < activeCount A z} where
  toFun j := ⟨activeRank A z j, activeRank_lt_activeCount A z j.property⟩
  invFun k := ⟨activeIndex A z k, activeIndex_mem A z k.property⟩
  left_inv j := Subtype.ext (activeIndex_activeRank A z j.property)
  right_inv k := Subtype.ext (activeRank_activeIndex A z k.property)

def compress (A : ℕ → Set ℂ) (z : ℂ) : Seq →L[ℂ] Seq :=
  reorderCLM (activeEquiv A z)

def expand (A : ℕ → Set ℂ) (z : ℂ) : Seq →L[ℂ] Seq :=
  reorderCLM (activeEquiv A z).symm

@[simp] theorem compress_apply (A : ℕ → Set ℂ) (z : ℂ) (x : Seq) (k : ℕ) :
    compress A z x k = if (k : ℕ∞) < activeCount A z then x (activeIndex A z k) else 0 := rfl

@[simp] theorem expand_apply (A : ℕ → Set ℂ) (z : ℂ) (x : Seq) (j : ℕ) :
    expand A z x j = if z ∈ A j then x (activeRank A z j) else 0 := rfl


theorem stronglyMeasurable_of_coordinates {S : Type*} [MeasurableSpace S]
    {f : S → Seq} (hf : ∀ j, StronglyMeasurable (fun z => f z j)) :
    StronglyMeasurable f := by
  apply stronglyMeasurable_of_tendsto Filter.atTop
    (f := fun n z => ∑ j ∈ Finset.range n, lp.single 2 j (f z j))
  · intro n
    apply (Finset.range n).stronglyMeasurable_fun_sum
    intro j _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 j).continuous.comp_stronglyMeasurable (hf j)
  · exact tendsto_pi_nhds.mpr fun z => (lp.hasSum_single (by norm_num) (f z)).tendsto_sum_nat

theorem stronglyMeasurable_variable_coordinate {f : ℂ → Seq}
    (hf : StronglyMeasurable f) {i : ℂ → ℕ} (hi : Measurable i) :
    StronglyMeasurable (fun z => f z (i z)) := by
  have hcoords (j : ℕ) : Measurable (fun z => f z j) :=
    ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j).continuous.comp_stronglyMeasurable hf).measurable
  have hjoint : Measurable (fun q : ℂ × ℕ => f q.1 q.2) :=
    measurable_from_prod_countable_left hcoords
  exact (hjoint.comp (measurable_id.prodMk hi)).stronglyMeasurable

theorem compress_stronglyMeasurable (A : ℕ → Set ℂ) (hA : ∀ j, MeasurableSet (A j))
    {f : ℂ → Seq} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z => compress A z (f z)) := by
  apply stronglyMeasurable_of_coordinates
  intro k
  simp only [compress_apply]
  exact ((stronglyMeasurable_variable_coordinate hf (activeIndex_measurable A hA k)).measurable.ite
    ((Set.to_countable {d : ℕ∞ | (k : ℕ∞) < d}).measurableSet.preimage (activeCount_measurable A hA)) measurable_const).stronglyMeasurable

theorem expand_stronglyMeasurable (A : ℕ → Set ℂ) (hA : ∀ j, MeasurableSet (A j))
    {f : ℂ → Seq} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z => expand A z (f z)) := by
  apply stronglyMeasurable_of_coordinates
  intro j
  simp only [expand_apply]
  exact ((stronglyMeasurable_variable_coordinate hf (activeRank_measurable A hA j)).measurable.ite
    (hA j) measurable_const).stronglyMeasurable


section Lift
variable (μ : Measure ℂ) (T : ℂ → Seq →L[ℂ] Seq)
    (hTmeas : ∀ f : ℂ → Seq, StronglyMeasurable f → StronglyMeasurable (fun z => T z (f z)))
    (hTnorm : ∀ z x, ‖T z x‖ ≤ ‖x‖)

include hTmeas hTnorm in
theorem liftMem (f : Lp Seq 2 μ) : MemLp (fun z => T z (f z)) 2 μ :=
  (Lp.memLp f).mono (hTmeas f (Lp.stronglyMeasurable f)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hTnorm z (f z))

def lift (f : Lp Seq 2 μ) : Lp Seq 2 μ :=
  (liftMem μ T hTmeas hTnorm f).toLp (fun z => T z (f z))

theorem lift_ae (f : Lp Seq 2 μ) : lift μ T hTmeas hTnorm f =ᵐ[μ] fun z => T z (f z) :=
  (liftMem μ T hTmeas hTnorm f).coeFn_toLp

theorem lift_add (f g : Lp Seq 2 μ) :
    lift μ T hTmeas hTnorm (f + g) = lift μ T hTmeas hTnorm f + lift μ T hTmeas hTnorm g := by
  apply Lp.ext
  filter_upwards [lift_ae μ T hTmeas hTnorm (f + g), lift_ae μ T hTmeas hTnorm f,
    lift_ae μ T hTmeas hTnorm g, Lp.coeFn_add f g,
    Lp.coeFn_add (lift μ T hTmeas hTnorm f) (lift μ T hTmeas hTnorm g)] with z hfg hf hg hsum hout
  simp only [Pi.add_apply] at hsum hout
  rw [hfg, hout, hf, hg, hsum, map_add]

theorem lift_smul (c : ℂ) (f : Lp Seq 2 μ) :
    lift μ T hTmeas hTnorm (c • f) = c • lift μ T hTmeas hTnorm f := by
  apply Lp.ext
  filter_upwards [lift_ae μ T hTmeas hTnorm (c • f), lift_ae μ T hTmeas hTnorm f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (lift μ T hTmeas hTnorm f)] with z hcf hf hsmul hout
  simp only [Pi.smul_apply] at hsmul hout
  rw [hcf, hout, hf, hsmul, map_smul]

def liftLinear (μ : Measure ℂ) : Lp Seq 2 μ →ₗ[ℂ] Lp Seq 2 μ where
  toFun := lift μ T hTmeas hTnorm
  map_add' := lift_add μ T hTmeas hTnorm
  map_smul' := lift_smul μ T hTmeas hTnorm

theorem lift_norm_le (f : Lp Seq 2 μ) : ‖lift μ T hTmeas hTnorm f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [lift_ae μ T hTmeas hTnorm f] with z hz
  rw [hz]
  exact hTnorm z (f z)
end Lift

def compressLp (μ : Measure ℂ) (A : ℕ → Set ℂ) (hA : ∀ j, MeasurableSet (A j)) :
    Lp Seq 2 μ →ₗ[ℂ] Lp Seq 2 μ :=
  liftLinear (compress A) (fun _ => compress_stronglyMeasurable A hA)
    (fun z => reorder_norm_le (activeEquiv A z)) μ

def expandLp (μ : Measure ℂ) (A : ℕ → Set ℂ) (hA : ∀ j, MeasurableSet (A j)) :
    Lp Seq 2 μ →ₗ[ℂ] Lp Seq 2 μ :=
  liftLinear (expand A) (fun _ => expand_stronglyMeasurable A hA)
    (fun z => reorder_norm_le (activeEquiv A z).symm) μ

theorem compressLp_ae (μ : Measure ℂ) (A : ℕ → Set ℂ) (hA : ∀ j, MeasurableSet (A j))
    (f : Lp Seq 2 μ) : compressLp μ A hA f =ᵐ[μ] fun z => compress A z (f z) :=
  lift_ae μ (compress A) (fun _ => compress_stronglyMeasurable A hA)
    (fun z => reorder_norm_le (activeEquiv A z)) f

theorem expandLp_ae (μ : Measure ℂ) (A : ℕ → Set ℂ) (hA : ∀ j, MeasurableSet (A j))
    (f : Lp Seq 2 μ) : expandLp μ A hA f =ᵐ[μ] fun z => expand A z (f z) :=
  lift_ae μ (expand A) (fun _ => expand_stronglyMeasurable A hA)
    (fun z => reorder_norm_le (activeEquiv A z).symm) f


section Equivalence
variable (μ : Measure ℂ) (A : ℕ → Set ℂ) (hA : ∀ j, MeasurableSet (A j))
    (hcover : ∀ᵐ z ∂μ, ∃ j, z ∈ A j)

lemma compressLp_mem (f : Lp Seq 2 μ) :
    compressLp μ A hA f ∈ MultiplicityModel.Spec.directIntegralSubmodule μ (activeMultiplicity μ A hA hcover) := by
  filter_upwards [compressLp_ae μ A hA f] with z hz
  rw [hz]
  exact reorder_supported (activeEquiv A z) (f z)

lemma expandLp_mem (f : Lp Seq 2 μ) : expandLp μ A hA f ∈ SupportedSections.sections μ A := by
  filter_upwards [expandLp_ae μ A hA f] with z hz
  rw [hz]
  exact reorder_supported (activeEquiv A z).symm (f z)

lemma expandLp_compressLp (f : SupportedSections.sections μ A) :
    expandLp μ A hA (compressLp μ A hA f) = f := by
  apply Lp.ext
  filter_upwards [expandLp_ae μ A hA (compressLp μ A hA f), compressLp_ae μ A hA f,
    f.property] with z hexp hcomp hf
  rw [hexp, hcomp]
  exact reorder_inverse (activeEquiv A z) (f.val z) hf

lemma compressLp_expandLp (f : MultiplicityModel.Spec.DirectIntegral μ (activeMultiplicity μ A hA hcover)) :
    compressLp μ A hA (expandLp μ A hA f) = f := by
  apply Lp.ext
  filter_upwards [compressLp_ae μ A hA (expandLp μ A hA f), expandLp_ae μ A hA f,
    f.property] with z hcomp hexp hf
  rw [hcomp, hexp]
  exact reorder_inverse (activeEquiv A z).symm (f.val z) hf

lemma compressLp_norm (f : SupportedSections.sections μ A) :
    ‖compressLp μ A hA f‖ = ‖f‖ := by
  apply le_antisymm
  · exact lift_norm_le μ (compress A) (fun _ => compress_stronglyMeasurable A hA)
      (fun z => reorder_norm_le (activeEquiv A z)) f
  · have h := lift_norm_le μ (expand A) (fun _ => expand_stronglyMeasurable A hA)
      (fun z => reorder_norm_le (activeEquiv A z).symm) (compressLp μ A hA f)
    rw [show lift μ (expand A) (fun _ => expand_stronglyMeasurable A hA)
      (fun z => reorder_norm_le (activeEquiv A z).symm) (compressLp μ A hA f) = f from
        expandLp_compressLp μ A hA f] at h
    exact h

def equivalence : SupportedSections.sections μ A ≃ₗᵢ[ℂ]
    MultiplicityModel.Spec.DirectIntegral μ (activeMultiplicity μ A hA hcover) where
  toFun f := ⟨compressLp μ A hA f, compressLp_mem μ A hA hcover f⟩
  invFun f := ⟨expandLp μ A hA f, expandLp_mem μ A hA f⟩
  left_inv f := Subtype.ext (expandLp_compressLp μ A hA f)
  right_inv f := Subtype.ext (compressLp_expandLp μ A hA hcover f)
  map_add' f g := Subtype.ext ((compressLp μ A hA).map_add f g)
  map_smul' c f := Subtype.ext ((compressLp μ A hA).map_smul c f)
  norm_map' := compressLp_norm μ A hA


theorem equivalence_ae (f : SupportedSections.sections μ A) :
    ((equivalence μ A hA hcover f).val : Lp Seq 2 μ) =ᵐ[μ]
      fun z => compress A z (f.val z) :=
  compressLp_ae μ A hA f

theorem equivalence_symm_ae
    (f : MultiplicityModel.Spec.DirectIntegral μ (activeMultiplicity μ A hA hcover)) :
    (((equivalence μ A hA hcover).symm f).val : Lp Seq 2 μ) =ᵐ[μ]
      fun z => expand A z (f.val z) :=
  expandLp_ae μ A hA f

theorem equivalence_symm_covariant
    (f g : MultiplicityModel.Spec.DirectIntegral μ (activeMultiplicity μ A hA hcover))
    (h : g.val =ᵐ[μ] fun z => z • f.val z) :
    ((equivalence μ A hA hcover).symm g).val =ᵐ[μ]
      fun z => z • ((equivalence μ A hA hcover).symm f).val z := by
  filter_upwards [equivalence_symm_ae μ A hA hcover g,
    equivalence_symm_ae μ A hA hcover f, h] with z hg hf hfg
  rw [hg, hf, hfg, map_smul]

end Equivalence

end FiberReordering

/-- Assemble the countable cyclic model by square-root RN transport,
L² packing, and measurable coordinate compression. -/
theorem multiplicity_existence : Spec.Existence.{u} := by
  intro H _ _ _ _ N hN
  obtain ⟨E, μ, hE, hfinite, hsupp, hcontrol, hbound⟩ :=
    finite_complex_control_measure H N hN
  rcases subsingleton_or_nontrivial H with hzero | _hnonzero
  · let := hzero
    have hμ : μ = 0 := controlMeasure_zero N E μ hcontrol
    refine ⟨E, μ, hE, hfinite, hsupp, hcontrol, ?_⟩
    rw [hμ]
    exact zero_model H N
  · let := hfinite
    obtain ⟨e, U, hU, htotal⟩ := countable_complex_scalar_model N hN E hE
    let ν : ℕ → Measure ℂ := fun j => spectrumMeasure N (E.diagonalMeasure (e j))
    have (j : ℕ) : IsFiniteMeasure (ν j) := by
      dsimp [ν, spectrumMeasure]
      infer_instance
    have hac (j : ℕ) : ν j ≪ μ := diagonal_absolutelyContinuous N E μ hcontrol (e j)
    have hcover : ∀ᵐ z ∂μ, ∃ j, 0 < (ν j).rnDeriv μ z :=
      rnDeriv_support_cover μ ν hac (fun B hB hνB =>
        (controlMeasure_zero_iff_diagonal N hN E hE μ hcontrol e htotal B hB).mpr hνB)
    let A : ℕ → Set ℂ := fun j => {z | 0 < (ν j).rnDeriv μ z}
    have hA (j : ℕ) : MeasurableSet (A j) :=
      measurableSet_lt measurable_const (Measure.measurable_rnDeriv (ν j) μ)
    let m := activeMultiplicity μ A hA hcover
    refine ⟨E, μ, hE, hfinite, hsupp, hcontrol, ?_⟩
    suffices htransport : ∃ V : MultiplicityModel.Spec.DirectIntegral μ m ≃ₗᵢ[ℂ]
        lp (fun j => Lp ℂ 2 (ν j)) 2,
        ∀ f j, V (MultiplicityModel.Spec.coordinateOperatorValue μ m hbound f) j =ᵐ[ν j]
          fun z => z * V f j z by
      obtain ⟨V, hV⟩ := htransport
      exact ⟨m, hbound, V.trans U, fun f =>
        hU (V f) (V (MultiplicityModel.Spec.coordinateOperatorValue μ m hbound f)) (hV f)⟩
    let R := RNFamily.equivalence μ ν hac
    let P := SupportedSections.packingEquivalence μ A
    let C := FiberReordering.equivalence μ A hA hcover
    let V : MultiplicityModel.Spec.DirectIntegral μ m ≃ₗᵢ[ℂ]
        lp (fun j => Lp ℂ 2 (ν j)) 2 := C.symm.trans (P.symm.trans R.symm)
    refine ⟨V, ?_⟩
    intro f j
    have hcoord := MultiplicityModel.coordinate_operator_property μ m hbound f
    have hC := FiberReordering.equivalence_symm_covariant μ A hA hcover f
      (MultiplicityModel.Spec.coordinateOperatorValue μ m hbound f) hcoord
    have hP := SupportedSections.packingEquivalence_symm_covariant μ A
      (C.symm f) (C.symm (MultiplicityModel.Spec.coordinateOperatorValue μ m hbound f)) hC
    exact RNFamily.equivalence_symm_covariant μ ν hac _ _ hP j

end ExpandedFA.VonNeumann.MultiplicityExistence
