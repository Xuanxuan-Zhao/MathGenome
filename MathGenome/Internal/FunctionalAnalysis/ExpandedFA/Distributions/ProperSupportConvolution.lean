import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.ProperSupportConvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionLocalizationAndGluing
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionRegularization
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open Set TopologicalSpace Function
open scoped Distributions Topology ContDiff Pointwise Manifold BoundedContinuousFunction
set_option maxHeartbeats 800000

namespace ExpandedFA.Distributions.ProperSupportConvolution
open Specs.ExpandedFA.Distributions.ProperSupportConvolution

/-- The tensor/cutoff relation for the partial convolution operation. -/
def convolutionRelation : convolutionRelationType := convolutionRelationValue

variable {d : ℕ}

/-- Compactness can be tested after including a subset in the ambient space. -/
private theorem compact_subtype_slice (S T K : Set (Domain d)) :
    IsCompact ((fun p : S ×ˢ T => p.val.1 + p.val.2) ⁻¹' K) ↔
      IsCompact (additionSlice S T K) := by
  rw [Subtype.isCompact_iff]
  have heq : Subtype.val '' ((fun p : S ×ˢ T => p.val.1 + p.val.2) ⁻¹' K) =
      additionSlice S T K := by
    ext p
    simp [additionSlice, and_assoc, and_comm]
  rw [heq]

theorem properness_bridge : propernessBridgeType := by
  intro d S T
  rw [isProperMap_iff_isCompact_preimage]
  constructor
  · intro h
    refine ⟨(continuous_fst.add continuous_snd).comp continuous_subtype_val, ?_⟩
    intro K hK
    exact (compact_subtype_slice S T K).mpr (h K hK)
  · intro h K hK
    exact (compact_subtype_slice S T K).mp (h.2 hK)

theorem additionSlice_swap (S T K : Set (Domain d)) :
    Prod.swap '' additionSlice S T K = additionSlice T S K := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨hq.1.2, hq.1.1⟩, by simpa [add_comm] using hq.2⟩
  · intro hp
    refine ⟨p.swap, ⟨⟨hp.1.2, hp.1.1⟩, ?_⟩, Prod.swap_swap p⟩
    simpa [add_comm] using hp.2

theorem properness_symmetry : propernessSymmetryType := by
  intro d S T
  suffices h : ∀ S T : Set (Domain d), AdditionProper S T → AdditionProper T S from
    ⟨h S T, h T S⟩
  intro S T h K hK
  rw [← additionSlice_swap S T K]
  exact (h K hK).image (continuous_snd.prodMk continuous_fst)

theorem additionProper_of_compact_left {S T : Set (Domain d)}
    (hS : IsCompact S) (hT : IsClosed T) : AdditionProper S T := by
  intro K hK
  have hdiff : IsCompact (K - S) := by
    rw [← sub_image_prod]
    exact (hK.prod hS).image (continuous_fst.sub continuous_snd)
  have hc : IsCompact (S ×ˢ (K - S)) := hS.prod hdiff
  apply hc.of_isClosed_subset
  · exact (hS.isClosed.prod hT).inter
      (hK.isClosed.preimage (continuous_fst.add continuous_snd))
  · rintro p ⟨hp, hsum⟩
    refine ⟨hp.1, ?_⟩
    exact ⟨p.1 + p.2, hsum, p.1, hp.1, add_sub_cancel_left _ _⟩

theorem compact_support_suffices : compactSupportSufficesType := by
  intro d S T hS hT hc
  rcases hc with hc | hc
  · exact additionProper_of_compact_left hc hT
  · exact (properness_symmetry d T S).mp (additionProper_of_compact_left hc hS)

theorem support_closed : supportClosedType := by
  intro 𝕜 _ d u
  have heq : distributionSupport u = (vanishingRegion u)ᶜ := by
    ext x
    simp [distributionSupport]
  rw [heq]
  exact (support_vanishing 𝕜 d ⊤ u).1.isClosed_compl

theorem compact_distribution_suffices : compactDistributionSufficesType := by
  intro 𝕜 _ d u v h
  exact compact_support_suffices d _ _ (support_closed 𝕜 d u) (support_closed 𝕜 d v) h

theorem closed_sum : closedSumType := by
  intro d S T h
  have heq : Set.range (fun p : S ×ˢ T => p.val.1 + p.val.2) = S + T := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val.1, p.property.1, p.val.2, p.property.2, rfl⟩
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨⟨(s, t), hs, ht⟩, rfl⟩
  rw [← heq]
  exact ((properness_bridge d S T).mp h).isClosed_range

theorem properness_monotone : propernessMonotoneType := by
  intro d S T A B h hA hB hAS hBT K hK
  apply (h K hK).of_isClosed_subset
  · exact (hA.prod hB).inter (hK.isClosed.preimage (continuous_fst.add continuous_snd))
  · rintro p ⟨hp, hsum⟩
    exact ⟨⟨hAS hp.1, hBT hp.2⟩, hsum⟩

/-- A compact subset of the product Euclidean space has a smooth compact cutoff. -/
theorem compact_product_cutoff (K : Set (Domain d × Domain d)) (hK : IsCompact K) :
    ∃ (χ : ProductTests ℝ d) (V : Set (Domain d × Domain d)),
      IsOpen V ∧ K ⊆ V ∧ EqOn χ 1 V := by
  obtain ⟨W, hW, hKW, _, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
  obtain ⟨f, hf0, hf1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, Domain d × Domain d)) hW.isClosed_compl hK.isClosed
    (Set.disjoint_left.mpr fun x hx hxK => hx (hKW hxK))
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (f : Domain d × Domain d → ℝ) :=
    contMDiff_iff_contDiff.mp f.contMDiff
  have hfs : tsupport (f : Domain d × Domain d → ℝ) ⊆ closure W := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hf0.self_of_nhdsSet x hn)
  let χ : ProductTests ℝ d := ⟨f, hfc,
    hWc.of_isClosed_subset isClosed_closure hfs, subset_univ _⟩
  obtain ⟨V, hV, hKV, hVf⟩ := eventually_nhdsSet_iff_exists.mp hf1
  exact ⟨χ, V, hV, hKV, hVf⟩

theorem cutoff_existence : cutoffExistenceType := by
  intro 𝕜 _ d u v h ψ
  exact compact_product_cutoff _ (h _ ψ.hasCompactSupport)

/-- Projecting a compact triple slice gives exactly the grouped pair slice. -/
theorem triple_grouped : tripleGroupedType := by
  intro d S T U h K hK
  have heq : (fun p : (Domain d × Domain d) × Domain d =>
      (p.1.1 + p.1.2, p.2)) ''
      (((S ×ˢ T) ×ˢ U) ∩ (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' K) =
      additionSlice (S + T) U K := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨⟨q.1.1, hq.1.1.1, q.1.2, hq.1.1.2, rfl⟩, hq.1.2⟩, hq.2⟩
    · rintro ⟨⟨⟨s, hs, t, ht, hp⟩, hu⟩, hsum⟩
      refine ⟨((s, t), p.2), ⟨⟨⟨hs, ht⟩, hu⟩, ?_⟩, ?_⟩
      · simpa [hp] using hsum
      · exact Prod.ext hp rfl
  rw [← heq]
  exact (h K hK).image
    (((continuous_fst.fst).add (continuous_fst.snd)).prodMk continuous_snd)

theorem triple_pair : triplePairType := by
  intro d S T U hS hT hU h K hK
  obtain ⟨z, hz⟩ := hU
  let L := (fun x : Domain d => x + z) '' K
  have hL : IsCompact L := hK.image (continuous_id.add continuous_const)
  have hc := (h L hL).image
    (continuous_fst : Continuous (Prod.fst : (Domain d × Domain d) × Domain d → _))
  apply hc.of_isClosed_subset
  · exact (hS.prod hT).inter (hK.isClosed.preimage (continuous_fst.add continuous_snd))
  · intro p hp
    exact ⟨(p, z), ⟨⟨hp.1, hz⟩, ⟨p.1 + p.2, hp.2, rfl⟩⟩, rfl⟩

theorem triple_compact : tripleCompactType := by
  intro d S T U hS hT hU K hK
  have hST : IsCompact (S + T) := by
    rw [← add_image_prod]
    exact (hS.prod hT).image (continuous_fst.add continuous_snd)
  have hdiff : IsCompact (K - (S + T)) := by
    rw [← sub_image_prod]
    exact (hK.prod hST).image (continuous_fst.sub continuous_snd)
  apply ((hS.prod hT).prod hdiff).of_isClosed_subset
  · exact ((hS.isClosed.prod hT.isClosed).prod hU).inter
      (hK.isClosed.preimage ((continuous_fst.fst.add continuous_fst.snd).add continuous_snd))
  · rintro p ⟨hp, hsum⟩
    exact ⟨hp.1, ⟨p.1.1 + p.1.2 + p.2, hsum,
      p.1.1 + p.1.2, ⟨p.1.1, hp.1.1, p.1.2, hp.1.2, rfl⟩,
      add_sub_cancel_left _ _⟩⟩

theorem cutoff_agreement : cutoffAgreementType := by
  intro 𝕜 _ d u v ψ χ χ' hχ hχ'
  obtain ⟨V, hV, hSV, hχV⟩ := hχ
  obtain ⟨W, hW, hSW, hχW⟩ := hχ'
  let A : Set (Domain d × Domain d) :=
    (fun p => p.1 + p.2) ⁻¹' (tsupport ψ)ᶜ
  have hA : IsOpen A := isClosed_closure.isOpen_compl.preimage
    (continuous_fst.add continuous_snd)
  refine ⟨(V ∩ W) ∪ A, (hV.inter hW).union hA, ?_, ?_⟩
  · intro p hp
    by_cases hsum : p.1 + p.2 ∈ tsupport ψ
    · exact Or.inl ⟨hSV ⟨hp, hsum⟩, hSW ⟨hp, hsum⟩⟩
    · exact Or.inr hsum
  · intro p hp
    change χ p • ψ (p.1 + p.2) = χ' p • ψ (p.1 + p.2)
    rcases hp with hp | hp
    · rw [hχV hp.1, hχW hp.2]
    · rw [image_eq_zero_of_notMem_tsupport hp, smul_zero, smul_zero]

/-- Every ordered partial derivative of a test retains its support. -/
theorem testPartial_tsupport_subset {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Domain d)}
    (w : List (Fin d)) (φ : Tests 𝕜 Ω) : tsupport (testPartialCLM w φ) ⊆ tsupport φ := by
  induction w with
  | nil => exact Subset.rfl
  | cons i w ih =>
    have heq : ⇑(testPartialCLM (i :: w) φ) =
        fun x => fderiv ℝ (testPartialCLM w φ) x (coordinateVector i) := by
      funext x
      change TestFunction.lineDerivCLM 𝕜 (coordinateVector i) (testPartialCLM w φ) x = _
      rw [TestFunction.lineDerivCLM_eq_fderivCLM,
        TestFunction.fderivCLM_apply_of_le _ (by simp)]
    rw [heq]
    exact (tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans ih

/-- Differentiation shrinks the distribution support, without any order hypothesis. -/
theorem derivative_support : derivativeSupportType := by
  intro 𝕜 _ d u w x hx
  refine ⟨Set.mem_univ x, ?_⟩
  intro hvan
  rcases hvan with ⟨V, ⟨hV, hVO, huV⟩, hxV⟩
  apply hx.2
  refine ⟨V, ⟨hV, hVO, ?_⟩, hxV⟩
  intro φ hφ
  change (-1 : 𝕜) ^ w.length * u (testPartialCLM w φ) = 0
  rw [huV _ ((testPartial_tsupport_subset w φ).trans hφ), mul_zero]

/-- The only distribution with empty support is zero, including in dimension zero. -/
theorem zero_support : zeroSupportType := by
  intro 𝕜 _ d u
  constructor
  · intro hu
    ext φ
    apply (support_vanishing 𝕜 d ⊤ u).2.2
    intro x _
    by_contra hx
    have hs : x ∈ distributionSupport u := ⟨Set.mem_univ x, hx⟩
    rw [hu] at hs
    exact hs
  · rintro rfl
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply hx.2
    exact ⟨Set.univ, ⟨isOpen_univ, subset_univ _, fun φ _ => rfl⟩, Set.mem_univ x⟩

/-- Cyclically permuting the three factors preserves their simultaneous sum. -/
theorem triple_rotation : tripleRotationType := by
  intro d S T U h K hK
  have heq : (fun p : (Domain d × Domain d) × Domain d =>
      ((p.1.2, p.2), p.1.1)) ''
      (((S ×ˢ T) ×ˢ U) ∩ (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' K) =
      (((T ×ˢ U) ×ˢ S) ∩ (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' K) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨⟨hq.1.1.2, hq.1.2⟩, hq.1.1.1⟩, ?_⟩
      simpa only [Set.mem_preimage, add_assoc, add_comm, add_left_comm] using hq.2
    · intro hp
      refine ⟨((p.2, p.1.1), p.1.2), ⟨⟨⟨hp.1.2, hp.1.1.1⟩, hp.1.1.2⟩, ?_⟩, rfl⟩
      simpa only [Set.mem_preimage, add_assoc, add_comm, add_left_comm] using hp.2
  rw [← heq]
  exact (h K hK).image ((continuous_fst.snd.prodMk continuous_snd).prodMk continuous_fst.fst)

theorem two_compact_triple : twoCompactTripleType := by
  intro d S T U hS hT hU h
  rcases h with ⟨hSc, hTc⟩ | ⟨hSc, hUc⟩ | ⟨hTc, hUc⟩
  · exact triple_compact d S T U hSc hTc hU
  · exact triple_rotation d U S T (triple_compact d U S T hUc hSc hT)
  · exact triple_rotation d U S T
      (triple_rotation d T U S (triple_compact d T U S hTc hUc hS))

theorem common_cutoff : commonCutoffType := by
  intro 𝕜 _ d u v h K hK
  obtain ⟨χ, V, hV, hSV, hχV⟩ := compact_product_cutoff _ (h K hK)
  refine ⟨χ, fun ψ hψ => ⟨V, hV, ?_, hχV⟩⟩
  intro p hp
  exact hSV ⟨hp.1, hψ hp.2⟩

theorem derivative_convolvable : derivativeConvolvableType := by
  intro 𝕜 _ d u v w h
  constructor
  · exact properness_monotone d _ _ _ _ h
      (support_closed 𝕜 d _) (support_closed 𝕜 d v) (derivative_support 𝕜 d u w) Subset.rfl
  · exact properness_monotone d _ _ _ _ h
      (support_closed 𝕜 d u) (support_closed 𝕜 d _) Subset.rfl (derivative_support 𝕜 d v w)

theorem convolution_uniqueness : convolutionUniquenessType := by
  intro 𝕜 _ d u v w w' hw hw'
  ext ψ
  obtain ⟨T, hT⟩ := hw.2.1
  obtain ⟨χ, hχ⟩ := cutoff_existence 𝕜 d u v hw.1 ψ
  rw [hw.2.2 T hT ψ χ hχ, hw'.2.2 T hT ψ χ hχ]

section KernelAction
variable {𝕜 : Type} [RCLike 𝕜]

/-- Restrict the bounded translated product function to a vertical section.
This normed model permits differentiation before applying a distribution. -/
def boundedSection {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain d × Domain d → F) (hf : Continuous f) (hs : HasCompactSupport f)
    (x : Domain d) : Domain d →ᵇ F :=
  (boundedReflectedTranslate f hf hs (x, 0)).compContinuous
    ⟨fun y => (0, -y), continuous_const.prodMk continuous_neg⟩

@[simp] theorem boundedSection_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain d × Domain d → F) (hf : Continuous f) (hs : HasCompactSupport f)
    (x y : Domain d) : boundedSection f hf hs x y = f (x, y) := by
  simp [boundedSection, boundedReflectedTranslate_apply]

theorem boundedSection_contDiff {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain d × Domain d → F) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ContDiff ℝ ∞ (boundedSection f hf.continuous hs) := by
  rw [contDiff_infty]
  intro n
  exact (BoundedContinuousFunction.compContinuousCLM F ℝ
    ⟨fun y : Domain d => ((0 : Domain d), -y),
      continuous_const.prodMk continuous_neg⟩).contDiff.comp
    ((boundedReflectedTranslate_contDiff n f hf hs).comp
      (contDiff_id.prodMk contDiff_const))

/-- The actual vertical section is a compactly supported test function. -/
def kernelSection (H : ProductTests 𝕜 d) (x : Domain d) : Tests 𝕜 (⊤ : Opens (Domain d)) where
  toFun y := H (x, y)
  contDiff' := H.contDiff.comp (contDiff_const.prodMk contDiff_id)
  hasCompactSupport' := by
    apply (H.hasCompactSupport.image continuous_snd).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (H.hasCompactSupport.image continuous_snd).isClosed
    intro y hy
    exact ⟨(x, y), subset_tsupport H hy, rfl⟩
  tsupport_subset' := subset_univ _

@[simp] theorem kernelSection_apply (H : ProductTests 𝕜 d) (x y : Domain d) :
    kernelSection H x y = H (x, y) := rfl

theorem kernelSection_tsupport (H : ProductTests 𝕜 d) (x : Domain d) :
    tsupport (kernelSection H x) ⊆ Prod.snd '' tsupport H := by
  apply closure_minimal _ (H.hasCompactSupport.image continuous_snd).isClosed
  intro y hy
  exact ⟨(x, y), subset_tsupport H hy, rfl⟩

/-- Each coordinate jet in y is a smooth, compactly supported function of (x,y). -/
def kernelCoordinate {k : ℕ} (H : ProductTests 𝕜 d) (a : Fin k → Fin d) :
    Domain d × Domain d → 𝕜 :=
  fun p => iteratedFDeriv ℝ k H p (fun j => (0, coordinateVector (a j)))

theorem kernelCoordinate_regular {k : ℕ} (H : ProductTests 𝕜 d) (a : Fin k → Fin d) :
    ContDiff ℝ ∞ (kernelCoordinate H a) ∧ HasCompactSupport (kernelCoordinate H a) := by
  constructor
  · exact (multilinearEvaluation (F := 𝕜)
      (fun j => ((0 : Domain d), coordinateVector (a j)))).contDiff.comp
      (H.contDiff.iteratedFDeriv_right (m := ∞) (by simp))
  · exact (H.hasCompactSupport.iteratedFDeriv k).comp_left
      (g := fun A : (Domain d × Domain d) [×k]→L[ℝ] 𝕜 =>
        A (fun j => (0, coordinateVector (a j)))) (by simp)

/-- A smooth normed-space model of the finite jet of every vertical section. -/
def kernelJet (H : ProductTests 𝕜 d) (m : ℕ) (x : Domain d) : FiniteJet 𝕜 d m :=
  fun a => boundedSection (kernelCoordinate H a.2)
    (kernelCoordinate_regular H a.2).1.continuous (kernelCoordinate_regular H a.2).2 x

theorem kernelJet_contDiff (H : ProductTests 𝕜 d) (m : ℕ) :
    ContDiff ℝ ∞ (kernelJet H m) := by
  apply contDiff_pi.mpr
  intro a
  exact boundedSection_contDiff _ (kernelCoordinate_regular H a.2).1
    (kernelCoordinate_regular H a.2).2

theorem iteratedFDeriv_kernelSection {k : ℕ} (H : ProductTests 𝕜 d)
    (x y : Domain d) (a : Fin k → Fin d) :
    iteratedFDeriv ℝ k (kernelSection H x) y (fun j => coordinateVector (a j)) =
      kernelCoordinate H a (x, y) := by
  let I : Domain d →L[ℝ] Domain d × Domain d :=
    (0 : Domain d →L[ℝ] Domain d).prod (ContinuousLinearMap.id ℝ _)
  have heq : ⇑(kernelSection H x) = (fun p => H ((x, 0) + p)) ∘ I := by
    funext y
    simp [I]
  rw [heq, I.iteratedFDeriv_comp_right (f := fun p => H ((x, 0) + p))
    (H.contDiff.comp (contDiff_const.add contDiff_id)) y (i := k) (by simp)]
  simp [I, iteratedFDeriv_comp_add_left, kernelCoordinate]

theorem kernelJet_eq_finiteJetMap (H : ProductTests 𝕜 d) (m : ℕ)
    (K : Compacts (Domain d)) (x : Domain d) (hx : tsupport (kernelSection H x) ⊆ K) :
    kernelJet H m x = finiteJetMap K m
      (ContDiffMapSupportedIn.of_support_subset (kernelSection H x).contDiff
        ((subset_tsupport _).trans hx)) := by
  ext a y
  rw [finiteJetMap_apply]
  simp only [kernelJet, boundedSection_apply]
  change kernelCoordinate H a.2 (x, y) =
    iteratedFDeriv ℝ a.1.val (kernelSection H x) y (fun j => coordinateVector (a.2 j))
  exact (iteratedFDeriv_kernelSection H x y a.2).symm

/-- Applying an arbitrary distribution to the y section gives a smooth function of x. -/
theorem kernelAction_contDiff (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) : ContDiff ℝ ∞ (fun x => v (kernelSection H x)) := by
  let K : Compacts (Domain d) :=
    ⟨Prod.snd '' tsupport H, H.hasCompactSupport.image continuous_snd⟩
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization v K
  have heq : (fun x => v (kernelSection H x)) = fun x => L (kernelJet H m x) := by
    funext x
    rw [kernelJet_eq_finiteJetMap H m K x (kernelSection_tsupport H x), hL]
    rfl
  rw [heq]
  exact (L.restrictScalars ℝ).contDiff.comp (kernelJet_contDiff H m)

end KernelAction

section Pullback
open WithSeminorms

variable {𝕜 : Type} {E E' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

abbrev pullbackCompact (g : E' ≃L[ℝ] E) (K : Compacts E) : Compacts E' :=
  ⟨g.symm '' K, K.isCompact.image g.symm.continuous⟩

def pullbackStepLM (g : E' ≃L[ℝ] E) (K : Compacts E) :
    ContDiffMapSupportedIn E 𝕜 ⊤ K →ₗ[𝕜]
      ContDiffMapSupportedIn E' 𝕜 ⊤ (pullbackCompact g K) where
  toFun f := ⟨f ∘ g, f.contDiff.comp g.contDiff, by
    intro p hp
    apply f.zero_on_compl
    intro h
    apply hp
    exact ⟨g p, h, g.symm_apply_apply p⟩⟩
  map_add' f h := by ext p; rfl
  map_smul' c f := by ext p; rfl

@[simp] theorem pullbackStepLM_apply (g : E' ≃L[ℝ] E) (K : Compacts E)
    (f : ContDiffMapSupportedIn E 𝕜 ⊤ K) (p : E') :
    pullbackStepLM g K f p = f (g p) := rfl

theorem pullbackStepLM_bound (g : E' ≃L[ℝ] E) (K : Compacts E) (i : ℕ)
    (f : ContDiffMapSupportedIn E 𝕜 ⊤ K) :
    ContDiffMapSupportedIn.seminorm 𝕜 E' 𝕜 ⊤ (pullbackCompact g K) i
        (pullbackStepLM g K f) ≤
      ‖g.toContinuousLinearMap‖ ^ i * ContDiffMapSupportedIn.seminorm 𝕜 E 𝕜 ⊤ K i f := by
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff 𝕜
    (mul_nonneg (pow_nonneg (norm_nonneg _) _) (apply_nonneg _ _)) i _).mpr
  intro x hx
  change ‖iteratedFDeriv ℝ i (f ∘ g.toContinuousLinearMap) x‖ ≤ _
  rw [g.toContinuousLinearMap.iteratedFDeriv_comp_right f.contDiff x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ i f (g x)‖ * ‖g.toContinuousLinearMap‖ ^ i := by
      simpa using (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ i f (g x)) (fun _ => g.toContinuousLinearMap))
    _ ≤ ContDiffMapSupportedIn.seminorm 𝕜 E 𝕜 ⊤ K i f * ‖g.toContinuousLinearMap‖ ^ i :=
      mul_le_mul_of_nonneg_right
        (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜) (by positivity)
    _ = _ := mul_comm _ _

def pullbackStepCLM (g : E' ≃L[ℝ] E) (K : Compacts E) :
    ContDiffMapSupportedIn E 𝕜 ⊤ K →L[𝕜]
      ContDiffMapSupportedIn E' 𝕜 ⊤ (pullbackCompact g K) where
  toLinearMap := pullbackStepLM g K
  cont := by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i => ?_)
    exact ⟨{i}, ‖g.toContinuousLinearMap‖ ^ i, fun f => by
      simpa using pullbackStepLM_bound g K i f⟩


def pullbackTest (g : E' ≃L[ℝ] E)
    (f : TestFunction (⊤ : Opens E) 𝕜 ⊤) : TestFunction (⊤ : Opens E') 𝕜 ⊤ where
  toFun := f ∘ g
  contDiff' := f.contDiff.comp g.contDiff
  hasCompactSupport' := by
    have hc : IsCompact (g.symm '' tsupport f) := f.hasCompactSupport.image g.symm.continuous
    apply hc.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hc.isClosed
    intro p hp
    exact ⟨g p, subset_tsupport f hp, g.symm_apply_apply p⟩
  tsupport_subset' := subset_univ _

@[simp] theorem pullbackTest_apply (g : E' ≃L[ℝ] E)
    (f : TestFunction (⊤ : Opens E) 𝕜 ⊤) (p : E') : pullbackTest g f p = f (g p) := rfl

def pullbackCLM (g : E' ≃L[ℝ] E) :
    TestFunction (⊤ : Opens E) 𝕜 ⊤ →L[𝕜] TestFunction (⊤ : Opens E') 𝕜 ⊤ :=
  TestFunction.limitCLM 𝕜 (pullbackTest g)
    (fun K _ => (TestFunction.ofSupportedInCLM 𝕜 (subset_univ _)).comp (pullbackStepCLM g K))
    (fun K hK f => by ext p; rfl)

@[simp] theorem pullbackCLM_apply (g : E' ≃L[ℝ] E)
    (f : TestFunction (⊤ : Opens E) 𝕜 ⊤) (p : E') : pullbackCLM g f p = f (g p) := rfl


@[simp] theorem pullbackCLM_symm_apply (g : E' ≃L[ℝ] E)
    (f : TestFunction (⊤ : Opens E') 𝕜 ⊤) :
    pullbackCLM g (pullbackCLM g.symm f) = f := by
  ext p
  simp

@[simp] theorem pullbackCLM_apply_symm (g : E' ≃L[ℝ] E)
    (f : TestFunction (⊤ : Opens E) 𝕜 ⊤) :
    pullbackCLM g.symm (pullbackCLM g f) = f := by
  ext p
  simp

section Swap
variable {d : ℕ}

abbrev swapTests (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :
    ProductTests 𝕜 d →L[𝕜] ProductTests 𝕜 d :=
  pullbackCLM (ContinuousLinearEquiv.prodComm ℝ (Domain d) (Domain d))

@[simp] theorem swapTests_apply (f : ProductTests 𝕜 d) (p : Domain d × Domain d) :
    swapTests 𝕜 d f p = f p.swap := rfl

@[simp] theorem swapTests_tensorTest (a b : Tests 𝕜 (⊤ : Opens (Domain d))) :
    swapTests 𝕜 d (tensorTest a b) = tensorTest b a := by
  ext p
  change a p.2 * b p.1 = b p.1 * a p.2
  exact mul_comm _ _

theorem isTensorProduct_swap {u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))}
    {T : ProductTests 𝕜 d →L[𝕜] 𝕜} (hT : IsTensorProduct u v T) :
    IsTensorProduct v u (T.comp (swapTests 𝕜 d)) := by
  intro a b
  change T (swapTests 𝕜 d (tensorTest a b)) = _
  rw [swapTests_tensorTest, hT b a, mul_comm]

theorem admissibleConvolutionCutoff_swap
    {u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))}
    {ψ : Tests 𝕜 (⊤ : Opens (Domain d))} {χ : ProductTests ℝ d}
    (hχ : AdmissibleConvolutionCutoff u v ψ χ) :
    AdmissibleConvolutionCutoff v u ψ (swapTests ℝ d χ) := by
  obtain ⟨V, hV, hSV, hχV⟩ := hχ
  refine ⟨Prod.swap ⁻¹' V, hV.preimage (continuous_snd.prodMk continuous_fst), ?_, ?_⟩
  · intro p hp
    apply hSV
    exact ⟨⟨hp.1.2, hp.1.1⟩, by simpa [add_comm] using hp.2⟩
  · intro p hp
    exact hχV hp

@[simp] theorem swapTests_cutoffAdditionTest
    (χ : ProductTests ℝ d) (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    swapTests 𝕜 d (cutoffAdditionTest (swapTests ℝ d χ) ψ) = cutoffAdditionTest χ ψ := by
  ext p
  change χ p • ψ (p.2 + p.1) = χ p • ψ (p.1 + p.2)
  rw [add_comm p.2 p.1]

theorem convolution_commutativity_aux
    (hsym : Specs.ExpandedFA.Distributions.ProperSupportConvolution.propernessSymmetryType) :
    Specs.ExpandedFA.Distributions.ProperSupportConvolution.convolutionCommutativityType := by
  intro 𝕜 _ d u v w hw
  refine ⟨(hsym d _ _).mp hw.1, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hw.2.1
    exact ⟨T.comp (swapTests 𝕜 d), isTensorProduct_swap hT⟩
  · intro T hT ψ χ hχ
    have ht := hw.2.2 (T.comp (swapTests 𝕜 d)) (isTensorProduct_swap hT)
      ψ (swapTests ℝ d χ) (admissibleConvolutionCutoff_swap hχ)
    simpa using ht

end Swap

end Pullback

theorem convolution_commutativity : convolutionCommutativityType :=
  convolution_commutativity_aux properness_symmetry

open Specs.ExpandedFA.Distributions.ProperSupportConvolution

/-- The exact sum contains the support of every relational convolution. -/
theorem convolution_support : convolutionSupportType := by
  intro 𝕜 _ d u v w hw x hx
  by_contra hsum
  apply hx.2
  let V : Set (Domain d) := (distributionSupport u + distributionSupport v)ᶜ
  have hV : IsOpen V := (closed_sum d _ _ hw.1).isOpen_compl
  refine ⟨V, ⟨hV, subset_univ _, ?_⟩, hsum⟩
  intro ψ hψ
  obtain ⟨T, hT⟩ := hw.2.1
  have hχ : AdmissibleConvolutionCutoff u v ψ (0 : ProductTests ℝ d) := by
    refine ⟨∅, isOpen_empty, ?_, ?_⟩
    · intro p hp
      exact hψ hp.2 ⟨p.1, hp.1.1, p.2, hp.1.2, rfl⟩
    · exact Set.eqOn_empty _ _
  rw [hw.2.2 T hT ψ 0 hχ]
  have hz : cutoffAdditionTest (0 : ProductTests ℝ d) ψ = 0 := by
    ext p
    exact zero_smul ℝ (ψ (p.1 + p.2))
  rw [hz, map_zero]


section CutoffPullback
open WithSeminorms
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

private def additionCLM : (Domain d × Domain d) →L[ℝ] Domain d :=
  ContinuousLinearMap.fst ℝ _ _ + ContinuousLinearMap.snd ℝ _ _

private theorem pullback_derivative_bound (K : Compacts (Domain d))
    (f : Step 𝕜 K) (n : ℕ) (x : Domain d × Domain d) :
    ‖iteratedFDeriv ℝ n (fun p : Domain d × Domain d => f (p.1 + p.2)) x‖ ≤
      ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K n f * ‖additionCLM (d := d)‖ ^ n := by
  change ‖iteratedFDeriv ℝ n (f ∘ additionCLM) x‖ ≤ _
  rw [additionCLM.iteratedFDeriv_comp_right f.contDiff x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simpa using mul_le_mul_of_nonneg_right
    (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜 (f := f))
    (pow_nonneg (norm_nonneg _) n)

private def cutoffStep (χ : ProductTests ℝ d) :
    ContDiffMapSupportedIn (Domain d × Domain d) ℝ ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ :=
  ContDiffMapSupportedIn.of_support_subset χ.contDiff (subset_tsupport χ)

private def cutoffPullbackStepLM (χ : ProductTests ℝ d) (K : Compacts (Domain d)) :
    Step 𝕜 K →ₗ[𝕜] ContDiffMapSupportedIn (Domain d × Domain d) 𝕜 ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ where
  toFun f := ⟨fun p => χ p • f (p.1 + p.2),
    χ.contDiff.smul (f.contDiff.comp (contDiff_fst.add contDiff_snd)), by
      intro p hp
      simp [image_eq_zero_of_notMem_tsupport hp]⟩
  map_add' f g := by
    ext p
    change χ p • (f (p.1+p.2) + g (p.1+p.2)) = χ p • f (p.1+p.2) + χ p • g (p.1+p.2)
    exact smul_add _ _ _
  map_smul' c f := by
    ext p
    change χ p • (c • f (p.1+p.2)) = c • (χ p • f (p.1+p.2))
    exact smul_comm _ _ _

private def cutoffPullbackBound (χ : ProductTests ℝ d) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    ContDiffMapSupportedIn.seminorm ℝ _ _ ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ i (cutoffStep χ) *
      ‖additionCLM (d := d)‖ ^ (n-i)

private theorem cutoffPullbackBound_nonneg (χ : ProductTests ℝ d) (n : ℕ) :
    0 ≤ cutoffPullbackBound χ n := by
  unfold cutoffPullbackBound
  apply Finset.sum_nonneg
  intro i hi
  positivity

private theorem cutoffPullbackStep_bound (χ : ProductTests ℝ d) (K : Compacts (Domain d))
    (f : Step 𝕜 K) (n : ℕ) (x : Domain d × Domain d) :
    ‖iteratedFDeriv ℝ n (cutoffPullbackStepLM χ K f) x‖ ≤
      cutoffPullbackBound χ n *
        ((Finset.Iic n).sup (ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K)) f := by
  let P := ((Finset.Iic n).sup (ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K)) f
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
        ‖iteratedFDeriv ℝ (n-i) (fun p : Domain d × Domain d => f (p.1 + p.2)) x‖ :=
      norm_iteratedFDeriv_smul_le χ.contDiff
        (f.contDiff.comp (contDiff_fst.add contDiff_snd)) x (by simp)
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ContDiffMapSupportedIn.seminorm ℝ _ _ ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ i (cutoffStep χ) *
        (P * ‖additionCLM (d := d)‖ ^ (n-i)) := by
      gcongr with i hi
      · exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ
          (f := cutoffStep χ)
      · exact (pullback_derivative_bound K f (n-i) x).trans
          (mul_le_mul_of_nonneg_right
            (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr (Nat.sub_le n i)))
            (pow_nonneg (norm_nonneg _) _))
    _ = cutoffPullbackBound χ n * P := by
      simp only [cutoffPullbackBound, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private def cutoffPullbackStepCLM (χ : ProductTests ℝ d) (K : Compacts (Domain d)) :
    Step 𝕜 K →L[𝕜] ContDiffMapSupportedIn (Domain d × Domain d) 𝕜 ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ where
  toLinearMap := cutoffPullbackStepLM χ K
  cont := by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun n => ?_)
    refine ⟨Finset.Iic n, cutoffPullbackBound χ n, fun f => ?_⟩
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff 𝕜
      (mul_nonneg (cutoffPullbackBound_nonneg χ n) (apply_nonneg _ _)) _ _).mpr
    intro x hx
    exact cutoffPullbackStep_bound χ K f n x

/-- Fixing a cutoff makes pullback by addition continuous in the LF topology. -/
def cutoffAdditionCLM (χ : ProductTests ℝ d) :
    Tests 𝕜 (⊤ : Opens (Domain d)) →L[𝕜] ProductTests 𝕜 d :=
  TestFunction.mkCLM 𝕜 (cutoffAdditionTest χ)
    (by intro f g; ext p; simp [cutoffAdditionTest, smul_add])
    (by
      intro c f
      ext p
      change χ p • (c • f (p.1+p.2)) = c • (χ p • f (p.1+p.2))
      exact smul_comm _ _ _)
    (by
      intro K hK
      exact (TestFunction.ofSupportedInCLM (Ω := (⊤ : Opens (Domain d × Domain d))) 𝕜
        (show (tsupport χ) ⊆ (⊤ : Opens (Domain d × Domain d)) from subset_univ _)).continuous.comp
        (cutoffPullbackStepCLM χ K).continuous)

@[simp] theorem cutoffAdditionCLM_apply (χ : ProductTests ℝ d)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    cutoffAdditionCLM χ ψ = cutoffAdditionTest χ ψ := rfl

end CutoffPullback

section TensorUniqueness
open MeasureTheory Filter

def splitDomain (d : ℕ) : Domain (d+d) ≃L[ℝ] Domain d × Domain d :=
  ((LinearEquiv.funCongrLeft ℝ ℝ finSumFinEquiv).trans
    (LinearEquiv.sumPiEquivProdPi ℝ (Fin d) (Fin d) (fun _ => ℝ))).toContinuousLinearEquiv

def splitDomainMeasurable (d : ℕ) : Domain (d+d) ≃ᵐ Domain d × Domain d :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin d ⊕ Fin d => ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => ℝ))

lemma splitDomainMeasurable_coe (d : ℕ) :
    (splitDomainMeasurable d : Domain (d+d) → Domain d × Domain d) = splitDomain d := by
  funext z
  apply Prod.ext <;> funext i <;> simp [splitDomainMeasurable, splitDomain, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft', LinearEquiv.funCongrLeft, LinearEquiv.sumPiEquivProdPi]

lemma splitDomain_volume_preserving (d : ℕ) :
    MeasurePreserving (splitDomainMeasurable d) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin d ⊕ Fin d => ℝ) finSumFinEquiv.symm)

def productMollifier {d : ℕ} (ρ : Domain d → ℝ) : Domain (d+d) → ℝ :=
  fun z => ρ (splitDomain d z).1 * ρ (splitDomain d z).2

lemma product_function_hasCompactSupport {d : ℕ} (ρ : Domain d → ℝ)
    (hρ : HasCompactSupport ρ) : HasCompactSupport (fun p : Domain d × Domain d => ρ p.1 * ρ p.2) := by
  apply (hρ.prod hρ).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
  intro p hp
  exact ⟨subset_tsupport ρ (mul_ne_zero_iff.mp hp).1,
    subset_tsupport ρ (mul_ne_zero_iff.mp hp).2⟩

lemma productMollifier_isMollifier {d : ℕ} (ρ : Domain d → ℝ)
    (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ) :
    SmoothApproximateIdentitiesSpec.IsMollifier (productMollifier ρ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hρ.1.comp contDiff_fst).mul (hρ.1.comp contDiff_snd)).comp
      (splitDomain d).contDiff
  · exact (product_function_hasCompactSupport ρ hρ.2.1).comp_isClosedEmbedding
      (splitDomain d).toHomeomorph.isClosedEmbedding
  · intro z
    exact mul_nonneg (hρ.2.2.1 _) (hρ.2.2.1 _)
  · simp only [productMollifier, ← splitDomainMeasurable_coe]
    change (∫ z, (fun p : Domain d × Domain d => ρ p.1 * ρ p.2) (splitDomainMeasurable d z)) = 1
    calc
      _ = ∫ p : Domain d × Domain d, ρ p.1 * ρ p.2 :=
        (splitDomain_volume_preserving d).integral_comp' (fun p => ρ p.1 * ρ p.2)
      _ = 1 := by rw [Measure.volume_eq_prod, integral_prod_mul, hρ.2.2.2, one_mul]

lemma exists_mollifier (d : ℕ) : ∃ ρ : Domain d → ℝ,
    SmoothApproximateIdentitiesSpec.IsMollifier ρ := by
  let b : ContDiffBump (0 : Domain d) := ⟨1, 2, by norm_num, by norm_num⟩
  exact ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed,
    b.nonneg_normed, b.integral_normed⟩


lemma scaledKernel_productMollifier {d : ℕ} (ρ : Domain d → ℝ) (ε : ℝ) (z : Domain (d+d)) :
    SmoothApproximateIdentitiesSpec.ScaledKernelValue (productMollifier ρ) ε z =
      SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε (splitDomain d z).1 *
        SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε (splitDomain d z).2 := by
  simp only [SmoothApproximateIdentitiesSpec.ScaledKernelValue, productMollifier,
    map_smul, Prod.smul_fst, Prod.smul_snd, pow_add, mul_inv_rev]
  ring

lemma reflectedTranslate_productMollifier {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ρ : Domain d → ℝ) (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (ε : ℝ) (hε : ε ≠ 0) (x : Domain (d+d)) :
    pullbackCLM (splitDomain d).symm
      (reflectedTranslate (scaledMollifierTest (productMollifier ρ)
        (productMollifier_isMollifier ρ hρ) ε : Tests 𝕜 ⊤) x) =
      tensorTest (reflectedTranslate (scaledMollifierTest ρ hρ ε : Tests 𝕜 ⊤) (splitDomain d x).1)
        (reflectedTranslate (scaledMollifierTest ρ hρ ε : Tests 𝕜 ⊤) (splitDomain d x).2) := by
  ext p
  simp only [pullbackCLM_apply, reflectedTranslate_apply, tensorTest,
    TestFunction.coe_mk, scaledMollifierTest_apply _ _ ε hε,
    scaledKernel_productMollifier, map_sub, ContinuousLinearEquiv.apply_symm_apply,
    Prod.fst_sub, Prod.snd_sub, map_mul]

lemma tensor_functional_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (W : ProductTests 𝕜 d →L[𝕜] 𝕜)
    (hW : ∀ a b : Tests 𝕜 (⊤ : Opens (Domain d)), W (tensorTest a b) = 0) : W = 0 := by
  obtain ⟨ρ, hρ⟩ := exists_mollifier d
  let U : ScalarDistribution 𝕜 (⊤ : Opens (Domain (d+d))) :=
    W.comp (pullbackCLM (splitDomain d).symm)
  have hconv : ∀ ε : ℝ, 0 < ε → ∀ x : Domain (d+d),
      distributionConvolution U (scaledMollifierTest (productMollifier ρ)
        (productMollifier_isMollifier ρ hρ) ε) x = 0 := by
    intro ε hε x
    change W (pullbackCLM (splitDomain d).symm _) = 0
    rw [reflectedTranslate_productMollifier ρ hρ ε hε.ne']
    exact hW _ _
  have hU : U = 0 := by
    ext ψ
    have ht := distributionConvolution_approximation U (productMollifier ρ)
      (productMollifier_isMollifier ρ hρ) ψ
    have heq : (fun ε => ∫ x, distributionConvolution U
        (scaledMollifierTest (productMollifier ρ) (productMollifier_isMollifier ρ hρ) ε) x * ψ x)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : 𝕜)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [hconv ε hε, zero_mul, integral_zero]
    have hlim : Tendsto (fun _ : ℝ => (0 : 𝕜)) (𝓝[>] (0 : ℝ)) (𝓝 (U ψ)) :=
      ht.congr' heq
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  ext ψ
  have he := congrArg (fun L : ScalarDistribution 𝕜 (⊤ : Opens (Domain (d+d))) =>
    L (pullbackCLM (splitDomain d) ψ)) hU
  change W (pullbackCLM (splitDomain d).symm (pullbackCLM (splitDomain d) ψ)) = 0 at he
  convert he using 1
  congr 1
  ext p
  simp only [pullbackCLM_apply, ContinuousLinearEquiv.apply_symm_apply]

lemma tensor_functional_ext {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T T' : ProductTests 𝕜 d →L[𝕜] 𝕜)
    (h : ∀ a b : Tests 𝕜 (⊤ : Opens (Domain d)), T (tensorTest a b) = T' (tensorTest a b)) :
    T = T' := by
  apply sub_eq_zero.mp
  apply tensor_functional_zero
  intro a b
  exact sub_eq_zero.mpr (h a b)


lemma tensor_product_unique {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (T T' : ProductTests 𝕜 d →L[𝕜] 𝕜)
    (hT : IsTensorProduct u v T) (hT' : IsTensorProduct u v T') : T = T' := by
  apply tensor_functional_ext T T'
  intro a b
  exact (hT a b).trans (hT' a b).symm

end TensorUniqueness

section TensorLocality
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

/-- Only the portion of the kernel support lying above the distribution support
can contribute to an action on vertical sections. -/
def kernelSupportProjection (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) : Set (Domain d) :=
  Prod.fst '' (tsupport H ∩ (Set.univ ×ˢ distributionSupport v))

theorem kernelSupportProjection_compact
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) (H : ProductTests 𝕜 d) :
    IsCompact (kernelSupportProjection v H) :=
  (H.hasCompactSupport.inter_right
    (isClosed_univ.prod (support_closed 𝕜 d v))).image continuous_fst

theorem kernelSection_pairing_eq_zero_off_projection
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) (H : ProductTests 𝕜 d)
    (x : Domain d) (hx : x ∉ kernelSupportProjection v H) :
    v (kernelSection H x) = 0 := by
  let W : Set (Domain d) := (fun y => (x, y)) ⁻¹' (tsupport H)ᶜ
  have hW : IsOpen W := isClosed_closure.isOpen_compl.preimage
    (continuous_const.prodMk continuous_id)
  have hSW : distributionSupport v ⊆ W := by
    intro y hy hp
    apply hx
    exact ⟨(x, y), ⟨hp, Set.mem_univ x, hy⟩, rfl⟩
  have heq := pairing_locality 𝕜 d ⊤ v (kernelSection H x) 0 W hW hSW (by
    intro y hy
    change H (x, y) = 0
    exact image_eq_zero_of_notMem_tsupport hy)
  simpa using heq

theorem kernel_action_tsupport_subset_projection
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) (H : ProductTests 𝕜 d)
    (k : Tests 𝕜 (⊤ : Opens (Domain d)))
    (hk : ∀ x, k x = v (kernelSection H x)) :
    tsupport k ⊆ kernelSupportProjection v H := by
  apply closure_minimal _ (kernelSupportProjection_compact v H).isClosed
  intro x hx
  by_contra hxn
  apply hx
  rw [hk x]
  exact kernelSection_pairing_eq_zero_off_projection v H x hxn

/-- A distribution applied to vertical kernel sections vanishes when the
kernel vanishes near the product of the two distribution supports. This needs
only the actual section pairing formula for the supplied outer test. -/
theorem iterated_kernel_pairing_eq_zero
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) (k : Tests 𝕜 (⊤ : Opens (Domain d)))
    (hk : ∀ x, k x = v (kernelSection H x))
    (V : Set (Domain d × Domain d)) (hV : IsOpen V)
    (hS : distributionSupport u ×ˢ distributionSupport v ⊆ V)
    (hH : EqOn H 0 V) : u k = 0 := by
  have hts : tsupport H ⊆ Vᶜ := by
    apply closure_minimal _ hV.isClosed_compl
    intro p hp hpV
    exact hp (hH hpV)
  have hSA : distributionSupport u ⊆ (kernelSupportProjection v H)ᶜ := by
    intro x hx hA
    obtain ⟨p, ⟨hp, hpv⟩, rfl⟩ := hA
    exact hts hp (hS ⟨hx, hpv.2⟩)
  have heq := pairing_locality 𝕜 d ⊤ u k 0 (kernelSupportProjection v H)ᶜ
    (kernelSupportProjection_compact v H).isClosed.isOpen_compl hSA (by
      intro x hx
      change k x = 0
      rw [hk x]
      exact kernelSection_pairing_eq_zero_off_projection v H x hx)
  simpa using heq


/-- Agreement near the product support gives equality of the iterated pairings. -/
theorem iterated_kernel_pairing_congr
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H H' : ProductTests 𝕜 d) (k k' : Tests 𝕜 (⊤ : Opens (Domain d)))
    (hk : ∀ x, k x = v (kernelSection H x))
    (hk' : ∀ x, k' x = v (kernelSection H' x))
    (V : Set (Domain d × Domain d)) (hV : IsOpen V)
    (hS : distributionSupport u ×ˢ distributionSupport v ⊆ V)
    (hH : EqOn H H' V) : u k = u k' := by
  have hd : ∀ x, (k - k') x = v (kernelSection (H - H') x) := by
    intro x
    change k x - k' x = _
    rw [hk x, hk' x, ← map_sub]
    congr 1
  have hdiff : EqOn (H - H') 0 V := by
    intro p hp
    change H p - H' p = 0
    exact sub_eq_zero.mpr (hH hp)
  have hz := iterated_kernel_pairing_eq_zero u v (H - H') (k - k') hd V hV hS hdiff
  simpa only [map_sub, sub_eq_zero] using hz

end TensorLocality

section TensorConstruction
open Filter
set_option maxHeartbeats 1600000
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

def kernelActionTest (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) : Tests 𝕜 (⊤ : Opens (Domain d)) where
  toFun x := v (kernelSection H x)
  contDiff' := kernelAction_contDiff v H
  hasCompactSupport' := by
    apply (H.hasCompactSupport.image continuous_fst).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (H.hasCompactSupport.image continuous_fst).isClosed
    intro x hx
    by_contra h
    apply hx
    have hsec : kernelSection H x = 0 := by
      ext y
      change H (x,y) = 0
      by_contra hy
      exact h ⟨(x,y), subset_tsupport H hy, rfl⟩
    simp [hsec]
  tsupport_subset' := subset_univ _

@[simp] theorem kernelActionTest_apply (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) (x : Domain d) : kernelActionTest v H x = v (kernelSection H x) := rfl

theorem kernelActionTest_tsupport (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) : tsupport (kernelActionTest v H) ⊆ Prod.fst '' tsupport H := by
  apply closure_minimal _ (H.hasCompactSupport.image continuous_fst).isClosed
  intro x hx
  by_contra h
  apply hx
  have hsec : kernelSection H x = 0 := by
    ext y
    change H (x,y) = 0
    by_contra hy
    exact h ⟨(x,y), subset_tsupport H hy, rfl⟩
  simp [kernelActionTest_apply, hsec]

@[simp] theorem kernelSection_add (H G : ProductTests 𝕜 d) (x : Domain d) :
    kernelSection (H+G) x = kernelSection H x + kernelSection G x := by ext; rfl
@[simp] theorem kernelSection_smul (c : 𝕜) (H : ProductTests 𝕜 d) (x : Domain d) :
    kernelSection (c • H) x = c • kernelSection H x := by ext; rfl

def kernelActionLM (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    ProductTests 𝕜 d →ₗ[𝕜] Tests 𝕜 (⊤ : Opens (Domain d)) where
  toFun := kernelActionTest v
  map_add' H G := by ext; simp
  map_smul' c H := by ext; simp

def kernelDerivX (h : Domain d) : ProductTests 𝕜 d →L[𝕜] ProductTests 𝕜 d :=
  TestFunction.lineDerivCLM 𝕜 (h, 0)

@[simp] theorem kernelDerivX_apply (h : Domain d) (H : ProductTests 𝕜 d)
    (p : Domain d × Domain d) : kernelDerivX h H p = fderiv ℝ H p (h,0) := by
  rw [kernelDerivX, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]

theorem boundedSection_fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain d × Domain d → F) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (x h y : Domain d) :
    fderiv ℝ (boundedSection f hf.continuous hs) x h y = fderiv ℝ f (x,y) (h,0) := by
  let C := BoundedContinuousFunction.compContinuousCLM F ℝ
    ⟨fun y : Domain d => ((0 : Domain d), -y), continuous_const.prodMk continuous_neg⟩
  let I : Domain d →L[ℝ] Domain d × Domain d :=
    (ContinuousLinearMap.id ℝ _).prod 0
  have heq : boundedSection f hf.continuous hs =
      C ∘ (boundedReflectedTranslate f hf.continuous hs) ∘ I := rfl
  have htr := boundedReflectedTranslate_hasFDerivAt f hf hs
    (hf.fderiv_right (m := ∞) (by simp)).continuous (hs.fderiv (𝕜 := ℝ)) (x,0)
  rw [heq]
  rw [(C.hasFDerivAt.comp x (htr.comp x I.hasFDerivAt)).fderiv]
  change fderiv ℝ f ((x,0)-(0,-y)) (h,0) = _
  simp

theorem kernelJet_fderiv (H : ProductTests 𝕜 d) (m : ℕ) (x h : Domain d) :
    fderiv ℝ (kernelJet H m) x h = kernelJet (kernelDerivX h H) m x := by
  have hdiff : ∀ a : FiniteJetIndex d m, DifferentiableAt ℝ
      (fun z => kernelJet H m z a) x := by
    intro a
    exact (boundedSection_contDiff _ (kernelCoordinate_regular H a.2).1
      (kernelCoordinate_regular H a.2).2).differentiable (by simp) x
  rw [show kernelJet H m = (fun z a => kernelJet H m z a) from rfl, fderiv_pi hdiff]
  ext a y
  change fderiv ℝ (boundedSection _ _ _) x h y = _
  rw [boundedSection_fderiv _ (kernelCoordinate_regular H a.2).1]
  change fderiv ℝ (fun z => iteratedFDeriv ℝ a.1.val H z
      (fun j => (0, coordinateVector (a.2 j)))) (x,y) (h,0) = _
  rw [fderiv_iteratedFDeriv_evaluation _ _ H.contDiff]
  change iteratedFDeriv ℝ a.1.val (fun z => fderiv ℝ H z (h,0)) (x,y) _ = _
  have heq : (fun z => fderiv ℝ H z (h,0)) = ⇑(kernelDerivX h H) := by
    funext z; exact (kernelDerivX_apply h H z).symm
  rw [heq]
  simp only [kernelJet, boundedSection_apply, kernelCoordinate]


theorem kernelAction_fderiv (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) (x h : Domain d) :
    fderiv ℝ (kernelActionTest v H) x h = kernelActionTest v (kernelDerivX h H) x := by
  let K : Compacts (Domain d) :=
    ⟨Prod.snd '' tsupport H, H.hasCompactSupport.image continuous_snd⟩
  have hderiv_supp : tsupport (kernelDerivX h H) ⊆ tsupport H := by
    apply (tsupport_fderiv_subset ℝ).trans' ?_
    have heq : ⇑(kernelDerivX h H) =
        (fun A : (Domain d × Domain d) →L[ℝ] 𝕜 => A (h,0)) ∘ fderiv ℝ H := by
      funext z; exact kernelDerivX_apply h H z
    rw [heq]
    exact tsupport_comp_subset (by simp) (fderiv ℝ H)
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization v K
  have heq : ⇑(kernelActionTest v H) = fun x => L (kernelJet H m x) := by
    funext z
    rw [kernelJet_eq_finiteJetMap H m K z (kernelSection_tsupport H z), hL]
    rfl
  rw [heq]
  have hder := (L.restrictScalars ℝ).hasFDerivAt.comp x
    ((kernelJet_contDiff H m).differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ ((L.restrictScalars ℝ) ∘ kernelJet H m) x h = _
  rw [hder.fderiv, ContinuousLinearMap.comp_apply]
  change L (fderiv ℝ (kernelJet H m) x h) = _
  rw [kernelJet_fderiv, kernelJet_eq_finiteJetMap _ m K x
    ((kernelSection_tsupport _ x).trans (Set.image_mono hderiv_supp)), hL]
  rfl


abbrev ProductStep (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Domain d × Domain d)) :=
  ContDiffMapSupportedIn (Domain d × Domain d) 𝕜 ⊤ K

def productStepInclusion (K : Compacts (Domain d × Domain d)) :
    ProductStep 𝕜 K →L[𝕜] ProductTests 𝕜 d :=
  TestFunction.ofSupportedInCLM 𝕜 (subset_univ _)

def productCompactFst (K : Compacts (Domain d × Domain d)) : Compacts (Domain d) :=
  ⟨Prod.fst '' (K : Set (Domain d × Domain d)), K.isCompact.image continuous_fst⟩

def productCompactSnd (K : Compacts (Domain d × Domain d)) : Compacts (Domain d) :=
  ⟨Prod.snd '' (K : Set (Domain d × Domain d)), K.isCompact.image continuous_snd⟩

def kernelActionStepLM (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (K : Compacts (Domain d × Domain d)) :
    ProductStep 𝕜 K →ₗ[𝕜] Step 𝕜 (productCompactFst K) where
  toFun f := ContDiffMapSupportedIn.of_support_subset
    (kernelActionTest v (productStepInclusion K f)).contDiff
    (((subset_tsupport _).trans (kernelActionTest_tsupport _ _)).trans
      (image_mono f.tsupport_subset))
  map_add' f g := by
    ext x
    change kernelActionLM v (productStepInclusion K (f+g)) x = _
    rw [map_add, map_add]
    rfl
  map_smul' c f := by
    ext x
    change kernelActionLM v (productStepInclusion K (c • f)) x = _
    rw [map_smul, map_smul]
    rfl

theorem kernelAction_zero_bound (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (K : Compacts (Domain d × Domain d)) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : ProductStep 𝕜 K) (x : Domain d),
      ‖kernelActionTest v (productStepInclusion K f) x‖ ≤ C *
        ((Finset.range (m+1)).sup
          (ContDiffMapSupportedIn.seminorm 𝕜 (Domain d × Domain d) 𝕜 ⊤ K)) f := by
  classical
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization v (productCompactSnd K)
  refine ⟨m, ‖L‖, norm_nonneg _, fun f x => ?_⟩
  have hs : tsupport (kernelSection (productStepInclusion K f) x) ⊆ productCompactSnd K :=
    (kernelSection_tsupport _ _).trans (image_mono f.tsupport_subset)
  have heq : kernelActionTest v (productStepInclusion K f) x =
      L (kernelJet (productStepInclusion K f) m x) := by
    rw [kernelJet_eq_finiteJetMap _ m _ x hs, hL]
    rfl
  rw [heq]
  apply (L.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr
  intro a
  apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
  intro y
  simp only [kernelJet, boundedSection_apply, kernelCoordinate]
  calc
    _ ≤ ‖iteratedFDeriv ℝ a.1.val (productStepInclusion K f) (x,y)‖ *
        ∏ j, ‖((0 : Domain d), coordinateVector (a.2 j))‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ a.1.val f (x,y)‖ := by
      simp [coordinateVector, Pi.norm_single]
      rfl
    _ ≤ ContDiffMapSupportedIn.seminorm 𝕜 (Domain d × Domain d) 𝕜 ⊤ K a.1.val f :=
      ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜
    _ ≤ _ := Seminorm.le_finset_sup_apply (Finset.mem_range.mpr a.1.isLt)

def boundedKernelActionStepCLM (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (K : Compacts (Domain d × Domain d)) :
    ProductStep 𝕜 K →L[𝕜] (Domain d →ᵇ 𝕜) :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace 𝕜
    (fun f => (kernelActionTest v (productStepInclusion K f) : Domain d →ᵇ 𝕜))
    (fun f g => by ext x; change kernelActionLM v (productStepInclusion K (f+g)) x = _; rw [map_add, map_add]; rfl)
    (fun c f => by ext x; change kernelActionLM v (productStepInclusion K (c • f)) x = _; rw [map_smul, map_smul]; rfl)
    (by
      obtain ⟨m, C, hC, h⟩ := kernelAction_zero_bound v K
      refine ⟨Finset.range (m+1), C, hC, fun f => ?_⟩
      exact (BoundedContinuousFunction.norm_le (mul_nonneg hC (apply_nonneg _ _))).mpr (h f))


def productDirectionEvaluation (h : Domain d × Domain d) :
    ((Domain d × Domain d) →L[ℝ] 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun A => A h
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ‖h‖ (fun A => by simpa [mul_comm] using A.le_opNorm h)

def productStepDerivX (K : Compacts (Domain d × Domain d)) (h : Domain d) :
    ProductStep 𝕜 K →L[𝕜] ProductStep 𝕜 K :=
  (ContDiffMapSupportedIn.postcompCLM (productDirectionEvaluation (𝕜 := 𝕜) (h,0))).comp
    (ContDiffMapSupportedIn.fderivCLM 𝕜 ⊤ ⊤)

@[simp] theorem productStepDerivX_apply (K : Compacts (Domain d × Domain d))
    (h : Domain d) (f : ProductStep 𝕜 K) (p : Domain d × Domain d) :
    productStepDerivX K h f p = fderiv ℝ f p (h,0) := by
  change productDirectionEvaluation (h,0) (ContDiffMapSupportedIn.fderivCLM 𝕜 ⊤ ⊤ f p) = _
  have heq := ContDiffMapSupportedIn.fderivCLM_apply_of_le
    (𝕜 := 𝕜) (n := ⊤) (k := ⊤) f (by simp)
  exact congrArg (fun g => g p (h,0)) heq

@[simp] theorem productStepDerivX_inclusion (K : Compacts (Domain d × Domain d))
    (h : Domain d) (f : ProductStep 𝕜 K) :
    productStepInclusion K (productStepDerivX K h f) = kernelDerivX h (productStepInclusion K f) := by
  ext p
  rw [kernelDerivX_apply]
  change productStepDerivX K h f p = fderiv ℝ f p (h,0)
  exact productStepDerivX_apply K h f p

def kernelWordX : List (Fin d) → ProductTests 𝕜 d →L[𝕜] ProductTests 𝕜 d
  | [] => ContinuousLinearMap.id 𝕜 _
  | i :: w => (kernelDerivX (coordinateVector i)).comp (kernelWordX w)

def productStepWordX (K : Compacts (Domain d × Domain d)) :
    List (Fin d) → ProductStep 𝕜 K →L[𝕜] ProductStep 𝕜 K
  | [] => ContinuousLinearMap.id 𝕜 _
  | i :: w => (productStepDerivX K (coordinateVector i)).comp (productStepWordX K w)

theorem kernelAction_partial (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) (w : List (Fin d)) :
    partialFunction w (kernelActionTest v H) = kernelActionTest v (kernelWordX w H) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (fun x => fderiv ℝ (partialFunction w (kernelActionTest v H)) x
      (coordinateVector i)) = _
    rw [ih]
    funext x
    exact kernelAction_fderiv v (kernelWordX w H) x (coordinateVector i)

@[simp] theorem productStepWordX_inclusion (K : Compacts (Domain d × Domain d))
    (f : ProductStep 𝕜 K) (w : List (Fin d)) :
    productStepInclusion K (productStepWordX K w f) = kernelWordX w (productStepInclusion K f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change productStepInclusion K
      (productStepDerivX K (coordinateVector i) (productStepWordX K w f)) = _
    rw [productStepDerivX_inclusion, ih]
    rfl

theorem coordinateDerivative_kernelActionStep (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (K : Compacts (Domain d × Domain d)) {k : ℕ} (a : Fin k → Fin d) (f : ProductStep 𝕜 K) :
    coordinateDerivative 𝕜 (productCompactFst K) a (kernelActionStepLM v K f) =
      boundedKernelActionStepCLM v K (productStepWordX K (List.ofFn a) f) := by
  ext x
  rw [coordinateDerivative_apply]
  change iteratedFDeriv ℝ k (kernelActionTest v (productStepInclusion K f)) x
      (fun j => coordinateVector (a j)) =
    kernelActionTest v (productStepInclusion K (productStepWordX K (List.ofFn a) f)) x
  rw [← partialFunction_ofFn k a _ (kernelActionTest v (productStepInclusion K f)).contDiff,
    kernelAction_partial, productStepWordX_inclusion]

theorem kernelActionStep_continuous (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (K : Compacts (Domain d × Domain d)) : Continuous (kernelActionStepLM v K) := by
  classical
  apply (step_seminorm_topology 𝕜 d (productCompactFst K)).continuous_of_continuous_comp
  intro m
  unfold stepSeminorm
  rw [SeminormFamily.finset_sup_comp]
  apply Seminorm.continuous_finsetSup
  intro k hk
  change Continuous ((Finset.univ.sup (coordinateSeminorm (k := k) 𝕜
    (productCompactFst K))).comp (kernelActionStepLM v K))
  rw [SeminormFamily.finset_sup_comp]
  apply Seminorm.continuous_finsetSup
  intro a ha
  have heq : (coordinateSeminorm 𝕜 (productCompactFst K) a).comp (kernelActionStepLM v K) =
      (normSeminorm 𝕜 (Domain d →ᵇ 𝕜)).comp
        ((boundedKernelActionStepCLM v K).comp (productStepWordX K (List.ofFn a))).toLinearMap := by
    ext f
    change ‖coordinateDerivative 𝕜 (productCompactFst K) a (kernelActionStepLM v K f)‖ = _
    rw [coordinateDerivative_kernelActionStep]
    rfl
  change Continuous ((coordinateSeminorm 𝕜 (productCompactFst K) a).comp
    (kernelActionStepLM v K))
  rw [heq]
  exact ((boundedKernelActionStepCLM v K).comp (productStepWordX K (List.ofFn a))).continuous.norm


def kernelActionCLM (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    ProductTests 𝕜 d →L[𝕜] Tests 𝕜 (⊤ : Opens (Domain d)) :=
  TestFunction.mkCLM 𝕜 (kernelActionLM v)
    (kernelActionLM v).map_add (fun c f => (kernelActionLM v).map_smul c f)
    (by
      intro K hK
      have h := (TestFunction.continuous_ofSupportedIn (F := 𝕜) (n := ⊤)
        (Ω := (⊤ : Opens (Domain d))) (show (productCompactFst K : Set (Domain d)) ⊆ (⊤ : Opens (Domain d)) from subset_univ _)).comp
          (kernelActionStep_continuous v K)
      exact h)

@[simp] theorem kernelActionCLM_apply (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) : kernelActionCLM v H = kernelActionTest v H := rfl

def iteratedTensor (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    ProductTests 𝕜 d →L[𝕜] 𝕜 := u.comp (kernelActionCLM v)

@[simp] theorem iteratedTensor_apply (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H : ProductTests 𝕜 d) : iteratedTensor u v H = u (kernelActionTest v H) := rfl

theorem iteratedTensor_isTensorProduct (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    IsTensorProduct u v (iteratedTensor u v) := by
  intro a b
  have heq : kernelActionTest v (tensorTest a b) = v b • a := by
    ext x
    change v (kernelSection (tensorTest a b) x) = v b * a x
    have hsec : kernelSection (tensorTest a b) x = a x • b := by ext y; rfl
    rw [hsec, map_smul]
    simp [mul_comm]
  rw [iteratedTensor_apply, heq, map_smul]
  simp [mul_comm]

theorem tensorProduct_exists (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    ∃ T : ProductTests 𝕜 d →L[𝕜] 𝕜, IsTensorProduct u v T :=
  ⟨iteratedTensor u v, iteratedTensor_isTensorProduct u v⟩

end TensorConstruction

section ConvolutionConstruction
open Specs.ExpandedFA.Distributions.ProperSupportConvolution
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
variable {u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))}

/-- Locality sufficient for the cutoff construction, derived from the tensor's actual support. -/
def TensorLocal (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (T : ProductTests 𝕜 d →L[𝕜] 𝕜) : Prop :=
  ∀ (H H' : ProductTests 𝕜 d) (V : Set (Domain d × Domain d)), IsOpen V →
    distributionSupport u ×ˢ distributionSupport v ⊆ V → EqOn H H' V → T H = T H'

private def selectedCutoff (h : Convolvable u v) (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    ProductTests ℝ d := (cutoff_existence 𝕜 d u v h ψ).choose

private theorem selectedCutoff_admissible (h : Convolvable u v)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    AdmissibleConvolutionCutoff u v ψ (selectedCutoff h ψ) :=
  (cutoff_existence 𝕜 d u v h ψ).choose_spec

private def convolutionPairing (h : Convolvable u v) (T : ProductTests 𝕜 d →L[𝕜] 𝕜)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) : 𝕜 :=
  T (cutoffAdditionTest (selectedCutoff h ψ) ψ)

private theorem convolutionPairing_eq (h : Convolvable u v)
    (T : ProductTests 𝕜 d →L[𝕜] 𝕜) (hlocal : TensorLocal u v T)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : AdmissibleConvolutionCutoff u v ψ χ) :
    convolutionPairing h T ψ = T (cutoffAdditionTest χ ψ) := by
  obtain ⟨V, hV, hSV, hEq⟩ := cutoff_agreement 𝕜 d u v ψ _ _
    (selectedCutoff_admissible h ψ) hχ
  exact hlocal _ _ V hV hSV hEq

/-- A local tensor functional gives a continuous scalar pairing by proper cutoff. -/
def convolutionFromTensor (h : Convolvable u v) (T : ProductTests 𝕜 d →L[𝕜] 𝕜)
    (hlocal : TensorLocal u v T) : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) :=
  TestFunction.mkCLM 𝕜 (convolutionPairing h T)
    (by
      intro ψ φ
      let K : Set (Domain d) := tsupport ψ ∪ tsupport φ
      obtain ⟨χ, hχ⟩ := common_cutoff 𝕜 d u v h K (ψ.hasCompactSupport.union φ.hasCompactSupport)
      rw [convolutionPairing_eq h T hlocal _ χ (hχ _ (tsupport_add _ _)),
        convolutionPairing_eq h T hlocal ψ χ (hχ _ subset_union_left),
        convolutionPairing_eq h T hlocal φ χ (hχ _ subset_union_right)]
      change T (cutoffAdditionCLM χ (ψ + φ)) = _
      rw [map_add, map_add]
      rfl)
    (by
      intro c ψ
      obtain ⟨χ, hχ⟩ := common_cutoff 𝕜 d u v h (tsupport ψ) ψ.hasCompactSupport
      rw [convolutionPairing_eq h T hlocal _ χ (hχ _ (by
        change tsupport (fun x => c • ψ x) ⊆ tsupport ψ
        exact tsupport_smul_subset_right (fun _ => c) ψ)),
        convolutionPairing_eq h T hlocal ψ χ (hχ _ Subset.rfl)]
      change T (cutoffAdditionCLM χ (c • ψ)) = _
      rw [map_smul, map_smul]
      rfl)
    (by
      intro K hK
      obtain ⟨χ, hχ⟩ := common_cutoff 𝕜 d u v h K K.isCompact
      let A := (T.comp (cutoffAdditionCLM χ)).comp
        (TestFunction.ofSupportedInCLM 𝕜 hK)
      have heq : convolutionPairing h T ∘ TestFunction.ofSupportedIn hK = A := by
        funext ψ
        exact convolutionPairing_eq h T hlocal _ χ (hχ _ ψ.tsupport_subset)
      rw [heq]
      exact A.continuous)

theorem convolutionFromTensor_pairing (h : Convolvable u v)
    (T : ProductTests 𝕜 d →L[𝕜] 𝕜) (hlocal : TensorLocal u v T)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : AdmissibleConvolutionCutoff u v ψ χ) :
    convolutionFromTensor h T hlocal ψ = T (cutoffAdditionTest χ ψ) :=
  convolutionPairing_eq h T hlocal ψ χ hχ

theorem convolution_exists_of_local_tensor (h : Convolvable u v)
    (T : ProductTests 𝕜 d →L[𝕜] 𝕜) (hT : IsTensorProduct u v T)
    (huniq : ∀ T', IsTensorProduct u v T' → T' = T) (hlocal : TensorLocal u v T) :
    ∃! w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)), IsProperConvolution u v w := by
  refine ⟨convolutionFromTensor h T hlocal, ⟨h, ⟨T, hT⟩, ?_⟩, ?_⟩
  · intro T' hT' ψ χ hχ
    rw [huniq T' hT']
    exact convolutionFromTensor_pairing h T hlocal ψ χ hχ
  · intro w hw
    apply convolution_uniqueness 𝕜 d u v w _ hw
    refine ⟨h, ⟨T, hT⟩, ?_⟩
    intro T' hT' ψ χ hχ
    rw [huniq T' hT']
    exact convolutionFromTensor_pairing h T hlocal ψ χ hχ

theorem iteratedTensor_local (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    TensorLocal u v (iteratedTensor u v) := by
  intro H H' V hV hS hEq
  exact iterated_kernel_pairing_congr u v H H' _ _ (fun _ => rfl) (fun _ => rfl) V hV hS hEq

theorem tensor_existence : tensorExistenceType := by
  intro 𝕜 _ d u v
  refine ⟨iteratedTensor u v, iteratedTensor_isTensorProduct u v, ?_⟩
  intro T hT
  exact tensor_product_unique u v T _ hT (iteratedTensor_isTensorProduct u v)

theorem tensor_local {T : ProductTests 𝕜 d →L[𝕜] 𝕜} (hT : IsTensorProduct u v T) :
    TensorLocal u v T := by
  rw [tensor_product_unique u v T _ hT (iteratedTensor_isTensorProduct u v)]
  exact iteratedTensor_local u v

theorem convolution_existence : convolutionExistenceType := by
  intro 𝕜 _ d u v h
  exact convolution_exists_of_local_tensor h (iteratedTensor u v)
    (iteratedTensor_isTensorProduct u v)
    (fun T hT => tensor_product_unique u v T _ hT (iteratedTensor_isTensorProduct u v))
    (iteratedTensor_local u v)

end ConvolutionConstruction

section ConvolutionOperation
open Specs.ExpandedFA.Distributions.ProperSupportConvolution

/-- Convolution on the domain of pairs with proper addition on their supports. -/
def convolution : convolutionOperationType := convolutionOperationValue

theorem convolution_spec : convolutionOperationSpecType := by
  intro 𝕜 _ d u v h
  exact Classical.epsilon_spec (convolution_existence 𝕜 d u v h).exists

theorem cutoff_independence : cutoffIndependenceType := by
  intro 𝕜 _ d u v h T T' hT hT' ψ χ χ' hχ hχ'
  obtain ⟨w, hw, _⟩ := convolution_existence 𝕜 d u v h
  rw [← hw.2.2 T hT ψ χ hχ, ← hw.2.2 T' hT' ψ χ' hχ']

end ConvolutionOperation

namespace RectangularKernel
open Filter
set_option maxHeartbeats 1600000
variable {p q : ℕ} {𝕜 : Type} [RCLike 𝕜]
abbrev KernelTests (𝕜 : Type) [RCLike 𝕜] (p q : ℕ) :=
  TestFunction (⊤ : Opens (Domain p × Domain q)) 𝕜 ⊤
/-- Restrict the bounded translated product function to a vertical section.
This normed model permits differentiation before applying a distribution. -/
def boundedSection {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain p × Domain q → F) (hf : Continuous f) (hs : HasCompactSupport f)
    (x : Domain p) : Domain q →ᵇ F :=
  (boundedReflectedTranslate f hf hs (x, 0)).compContinuous
    ⟨fun y => (0, -y), continuous_const.prodMk continuous_neg⟩

@[simp] theorem boundedSection_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain p × Domain q → F) (hf : Continuous f) (hs : HasCompactSupport f)
    (x : Domain p) (y : Domain q) : boundedSection f hf hs x y = f (x, y) := by
  simp [boundedSection, boundedReflectedTranslate_apply]

theorem boundedSection_contDiff {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain p × Domain q → F) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ContDiff ℝ ∞ (boundedSection f hf.continuous hs) := by
  rw [contDiff_infty]
  intro n
  exact (BoundedContinuousFunction.compContinuousCLM F ℝ
    ⟨fun y : Domain q => ((0 : Domain p), -y),
      continuous_const.prodMk continuous_neg⟩).contDiff.comp
    ((boundedReflectedTranslate_contDiff n f hf hs).comp
      (contDiff_id.prodMk contDiff_const))

/-- The actual vertical section is a compactly supported test function. -/
def kernelSection (H : KernelTests 𝕜 p q) (x : Domain p) : Tests 𝕜 (⊤ : Opens (Domain q)) where
  toFun y := H (x, y)
  contDiff' := H.contDiff.comp (contDiff_const.prodMk contDiff_id)
  hasCompactSupport' := by
    apply (H.hasCompactSupport.image continuous_snd).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (H.hasCompactSupport.image continuous_snd).isClosed
    intro y hy
    exact ⟨(x, y), subset_tsupport H hy, rfl⟩
  tsupport_subset' := subset_univ _

@[simp] theorem kernelSection_apply (H : KernelTests 𝕜 p q) (x : Domain p) (y : Domain q) :
    kernelSection H x y = H (x, y) := rfl

theorem kernelSection_tsupport (H : KernelTests 𝕜 p q) (x : Domain p) :
    tsupport (kernelSection H x) ⊆ Prod.snd '' tsupport H := by
  apply closure_minimal _ (H.hasCompactSupport.image continuous_snd).isClosed
  intro y hy
  exact ⟨(x, y), subset_tsupport H hy, rfl⟩

/-- Each coordinate jet in y is a smooth, compactly supported function of (x,y). -/
def kernelCoordinate {k : ℕ} (H : KernelTests 𝕜 p q) (a : Fin k → Fin q) :
    Domain p × Domain q → 𝕜 :=
  fun p => iteratedFDeriv ℝ k H p (fun j => (0, coordinateVector (a j)))

theorem kernelCoordinate_regular {k : ℕ} (H : KernelTests 𝕜 p q) (a : Fin k → Fin q) :
    ContDiff ℝ ∞ (kernelCoordinate H a) ∧ HasCompactSupport (kernelCoordinate H a) := by
  constructor
  · exact (multilinearEvaluation (F := 𝕜)
      (fun j => ((0 : Domain p), coordinateVector (a j)))).contDiff.comp
      (H.contDiff.iteratedFDeriv_right (m := ∞) (by simp))
  · exact (H.hasCompactSupport.iteratedFDeriv k).comp_left
      (g := fun A : (Domain p × Domain q) [×k]→L[ℝ] 𝕜 =>
        A (fun j => (0, coordinateVector (a j)))) (by simp)

/-- A smooth normed-space model of the finite jet of every vertical section. -/
def kernelJet (H : KernelTests 𝕜 p q) (m : ℕ) (x : Domain p) : FiniteJet 𝕜 q m :=
  fun a => boundedSection (kernelCoordinate H a.2)
    (kernelCoordinate_regular H a.2).1.continuous (kernelCoordinate_regular H a.2).2 x

theorem kernelJet_contDiff (H : KernelTests 𝕜 p q) (m : ℕ) :
    ContDiff ℝ ∞ (kernelJet H m) := by
  apply contDiff_pi.mpr
  intro a
  exact boundedSection_contDiff _ (kernelCoordinate_regular H a.2).1
    (kernelCoordinate_regular H a.2).2

theorem iteratedFDeriv_kernelSection {k : ℕ} (H : KernelTests 𝕜 p q)
    (x : Domain p) (y : Domain q) (a : Fin k → Fin q) :
    iteratedFDeriv ℝ k (kernelSection H x) y (fun j => coordinateVector (a j)) =
      kernelCoordinate H a (x, y) := by
  let I : Domain q →L[ℝ] Domain p × Domain q :=
    (0 : Domain q →L[ℝ] Domain p).prod (ContinuousLinearMap.id ℝ _)
  have heq : ⇑(kernelSection H x) = (fun p => H ((x, 0) + p)) ∘ I := by
    funext y
    simp [I]
  rw [heq, I.iteratedFDeriv_comp_right (f := fun p => H ((x, 0) + p))
    (H.contDiff.comp (contDiff_const.add contDiff_id)) y (i := k) (by simp)]
  simp [I, iteratedFDeriv_comp_add_left, kernelCoordinate]

theorem kernelJet_eq_finiteJetMap (H : KernelTests 𝕜 p q) (m : ℕ)
    (K : Compacts (Domain q)) (x : Domain p) (hx : tsupport (kernelSection H x) ⊆ K) :
    kernelJet H m x = finiteJetMap K m
      (ContDiffMapSupportedIn.of_support_subset (kernelSection H x).contDiff
        ((subset_tsupport _).trans hx)) := by
  ext a y
  rw [finiteJetMap_apply]
  simp only [kernelJet, boundedSection_apply]
  change kernelCoordinate H a.2 (x, y) =
    iteratedFDeriv ℝ a.1.val (kernelSection H x) y (fun j => coordinateVector (a.2 j))
  exact (iteratedFDeriv_kernelSection H x y a.2).symm

/-- Applying an arbitrary distribution to the y section gives a smooth function of x. -/
theorem kernelAction_contDiff (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) : ContDiff ℝ ∞ (fun x => v (kernelSection H x)) := by
  let K : Compacts (Domain q) :=
    ⟨Prod.snd '' tsupport H, H.hasCompactSupport.image continuous_snd⟩
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization v K
  have heq : (fun x => v (kernelSection H x)) = fun x => L (kernelJet H m x) := by
    funext x
    rw [kernelJet_eq_finiteJetMap H m K x (kernelSection_tsupport H x), hL]
    rfl
  rw [heq]
  exact (L.restrictScalars ℝ).contDiff.comp (kernelJet_contDiff H m)


def kernelActionTest (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) : Tests 𝕜 (⊤ : Opens (Domain p)) where
  toFun x := v (kernelSection H x)
  contDiff' := kernelAction_contDiff v H
  hasCompactSupport' := by
    apply (H.hasCompactSupport.image continuous_fst).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (H.hasCompactSupport.image continuous_fst).isClosed
    intro x hx
    by_contra h
    apply hx
    have hsec : kernelSection H x = 0 := by
      ext y
      change H (x,y) = 0
      by_contra hy
      exact h ⟨(x,y), subset_tsupport H hy, rfl⟩
    simp [hsec]
  tsupport_subset' := subset_univ _

@[simp] theorem kernelActionTest_apply (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) (x : Domain p) : kernelActionTest v H x = v (kernelSection H x) := rfl

theorem kernelActionTest_tsupport (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) : tsupport (kernelActionTest v H) ⊆ Prod.fst '' tsupport H := by
  apply closure_minimal _ (H.hasCompactSupport.image continuous_fst).isClosed
  intro x hx
  by_contra h
  apply hx
  have hsec : kernelSection H x = 0 := by
    ext y
    change H (x,y) = 0
    by_contra hy
    exact h ⟨(x,y), subset_tsupport H hy, rfl⟩
  simp [kernelActionTest_apply, hsec]

@[simp] theorem kernelSection_add (H G : KernelTests 𝕜 p q) (x : Domain p) :
    kernelSection (H+G) x = kernelSection H x + kernelSection G x := by ext; rfl
@[simp] theorem kernelSection_smul (c : 𝕜) (H : KernelTests 𝕜 p q) (x : Domain p) :
    kernelSection (c • H) x = c • kernelSection H x := by ext; rfl

def kernelActionLM (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q))) :
    KernelTests 𝕜 p q →ₗ[𝕜] Tests 𝕜 (⊤ : Opens (Domain p)) where
  toFun := kernelActionTest v
  map_add' H G := by ext; simp
  map_smul' c H := by ext; simp

def kernelDerivX (h : Domain p) : KernelTests 𝕜 p q →L[𝕜] KernelTests 𝕜 p q :=
  TestFunction.lineDerivCLM 𝕜 (h, 0)

@[simp] theorem kernelDerivX_apply (h : Domain p) (H : KernelTests 𝕜 p q)
    (p : Domain p × Domain q) : kernelDerivX h H p = fderiv ℝ H p (h,0) := by
  rw [kernelDerivX, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]

theorem boundedSection_fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain p × Domain q → F) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (x h : Domain p) (y : Domain q) :
    fderiv ℝ (boundedSection f hf.continuous hs) x h y = fderiv ℝ f (x,y) (h,0) := by
  let C := BoundedContinuousFunction.compContinuousCLM F ℝ
    ⟨fun y : Domain q => ((0 : Domain p), -y), continuous_const.prodMk continuous_neg⟩
  let I : Domain p →L[ℝ] Domain p × Domain q :=
    (ContinuousLinearMap.id ℝ _).prod 0
  have heq : boundedSection f hf.continuous hs =
      C ∘ (boundedReflectedTranslate f hf.continuous hs) ∘ I := rfl
  have htr := boundedReflectedTranslate_hasFDerivAt f hf hs
    (hf.fderiv_right (m := ∞) (by simp)).continuous (hs.fderiv (𝕜 := ℝ)) (x,0)
  rw [heq]
  rw [(C.hasFDerivAt.comp x (htr.comp x I.hasFDerivAt)).fderiv]
  change fderiv ℝ f ((x,0)-(0,-y)) (h,0) = _
  simp

theorem kernelJet_fderiv (H : KernelTests 𝕜 p q) (m : ℕ) (x h : Domain p) :
    fderiv ℝ (kernelJet H m) x h = kernelJet (kernelDerivX h H) m x := by
  have hdiff : ∀ a : FiniteJetIndex q m, DifferentiableAt ℝ
      (fun z => kernelJet H m z a) x := by
    intro a
    exact (boundedSection_contDiff _ (kernelCoordinate_regular H a.2).1
      (kernelCoordinate_regular H a.2).2).differentiable (by simp) x
  rw [show kernelJet H m = (fun z a => kernelJet H m z a) from rfl, fderiv_pi hdiff]
  ext a y
  change fderiv ℝ (boundedSection _ _ _) x h y = _
  rw [boundedSection_fderiv _ (kernelCoordinate_regular H a.2).1]
  change fderiv ℝ (fun z => iteratedFDeriv ℝ a.1.val H z
      (fun j => (0, coordinateVector (a.2 j)))) (x,y) (h,0) = _
  rw [fderiv_iteratedFDeriv_evaluation _ _ H.contDiff]
  change iteratedFDeriv ℝ a.1.val (fun z => fderiv ℝ H z (h,0)) (x,y) _ = _
  have heq : (fun z => fderiv ℝ H z (h,0)) = ⇑(kernelDerivX h H) := by
    funext z; exact (kernelDerivX_apply h H z).symm
  rw [heq]
  simp only [kernelJet, boundedSection_apply, kernelCoordinate]


theorem kernelAction_fderiv (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) (x h : Domain p) :
    fderiv ℝ (kernelActionTest v H) x h = kernelActionTest v (kernelDerivX h H) x := by
  let K : Compacts (Domain q) :=
    ⟨Prod.snd '' tsupport H, H.hasCompactSupport.image continuous_snd⟩
  have hderiv_supp : tsupport (kernelDerivX h H) ⊆ tsupport H := by
    apply (tsupport_fderiv_subset ℝ).trans' ?_
    have heq : ⇑(kernelDerivX h H) =
        (fun A : (Domain p × Domain q) →L[ℝ] 𝕜 => A (h,0)) ∘ fderiv ℝ H := by
      funext z; exact kernelDerivX_apply h H z
    rw [heq]
    exact tsupport_comp_subset (by simp) (fderiv ℝ H)
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization v K
  have heq : ⇑(kernelActionTest v H) = fun x => L (kernelJet H m x) := by
    funext z
    rw [kernelJet_eq_finiteJetMap H m K z (kernelSection_tsupport H z), hL]
    rfl
  rw [heq]
  have hder := (L.restrictScalars ℝ).hasFDerivAt.comp x
    ((kernelJet_contDiff H m).differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ ((L.restrictScalars ℝ) ∘ kernelJet H m) x h = _
  rw [hder.fderiv, ContinuousLinearMap.comp_apply]
  change L (fderiv ℝ (kernelJet H m) x h) = _
  rw [kernelJet_fderiv, kernelJet_eq_finiteJetMap _ m K x
    ((kernelSection_tsupport _ x).trans (Set.image_mono hderiv_supp)), hL]
  rfl


abbrev ProductStep (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Domain p × Domain q)) :=
  ContDiffMapSupportedIn (Domain p × Domain q) 𝕜 ⊤ K

def productStepInclusion (K : Compacts (Domain p × Domain q)) :
    ProductStep 𝕜 K →L[𝕜] KernelTests 𝕜 p q :=
  TestFunction.ofSupportedInCLM 𝕜 (subset_univ _)

def productCompactFst (K : Compacts (Domain p × Domain q)) : Compacts (Domain p) :=
  ⟨Prod.fst '' (K : Set (Domain p × Domain q)), K.isCompact.image continuous_fst⟩

def productCompactSnd (K : Compacts (Domain p × Domain q)) : Compacts (Domain q) :=
  ⟨Prod.snd '' (K : Set (Domain p × Domain q)), K.isCompact.image continuous_snd⟩

def kernelActionStepLM (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (K : Compacts (Domain p × Domain q)) :
    ProductStep 𝕜 K →ₗ[𝕜] Step 𝕜 (productCompactFst K) where
  toFun f := ContDiffMapSupportedIn.of_support_subset
    (kernelActionTest v (productStepInclusion K f)).contDiff
    (((subset_tsupport _).trans (kernelActionTest_tsupport _ _)).trans
      (image_mono f.tsupport_subset))
  map_add' f g := by
    ext x
    change kernelActionLM v (productStepInclusion K (f+g)) x = _
    rw [map_add, map_add]
    rfl
  map_smul' c f := by
    ext x
    change kernelActionLM v (productStepInclusion K (c • f)) x = _
    rw [map_smul, map_smul]
    rfl

theorem kernelAction_zero_bound (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (K : Compacts (Domain p × Domain q)) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : ProductStep 𝕜 K) (x : Domain p),
      ‖kernelActionTest v (productStepInclusion K f) x‖ ≤ C *
        ((Finset.range (m+1)).sup
          (ContDiffMapSupportedIn.seminorm 𝕜 (Domain p × Domain q) 𝕜 ⊤ K)) f := by
  classical
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization v (productCompactSnd K)
  refine ⟨m, ‖L‖, norm_nonneg _, fun f x => ?_⟩
  have hs : tsupport (kernelSection (productStepInclusion K f) x) ⊆ productCompactSnd K :=
    (kernelSection_tsupport _ _).trans (image_mono f.tsupport_subset)
  have heq : kernelActionTest v (productStepInclusion K f) x =
      L (kernelJet (productStepInclusion K f) m x) := by
    rw [kernelJet_eq_finiteJetMap _ m _ x hs, hL]
    rfl
  rw [heq]
  apply (L.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr
  intro a
  apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
  intro y
  simp only [kernelJet, boundedSection_apply, kernelCoordinate]
  calc
    _ ≤ ‖iteratedFDeriv ℝ a.1.val (productStepInclusion K f) (x,y)‖ *
        ∏ j, ‖((0 : Domain p), coordinateVector (a.2 j))‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ a.1.val f (x,y)‖ := by
      simp [coordinateVector, Pi.norm_single]
      rfl
    _ ≤ ContDiffMapSupportedIn.seminorm 𝕜 (Domain p × Domain q) 𝕜 ⊤ K a.1.val f :=
      ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜
    _ ≤ _ := Seminorm.le_finset_sup_apply (Finset.mem_range.mpr a.1.isLt)

def boundedKernelActionStepCLM (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (K : Compacts (Domain p × Domain q)) :
    ProductStep 𝕜 K →L[𝕜] (Domain p →ᵇ 𝕜) :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace 𝕜
    (fun f => (kernelActionTest v (productStepInclusion K f) : Domain p →ᵇ 𝕜))
    (fun f g => by ext x; change kernelActionLM v (productStepInclusion K (f+g)) x = _; rw [map_add, map_add]; rfl)
    (fun c f => by ext x; change kernelActionLM v (productStepInclusion K (c • f)) x = _; rw [map_smul, map_smul]; rfl)
    (by
      obtain ⟨m, C, hC, h⟩ := kernelAction_zero_bound v K
      refine ⟨Finset.range (m+1), C, hC, fun f => ?_⟩
      exact (BoundedContinuousFunction.norm_le (mul_nonneg hC (apply_nonneg _ _))).mpr (h f))


def productDirectionEvaluation (h : Domain p × Domain q) :
    ((Domain p × Domain q) →L[ℝ] 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun A => A h
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ‖h‖ (fun A => by simpa [mul_comm] using A.le_opNorm h)

def productStepDerivX (K : Compacts (Domain p × Domain q)) (h : Domain p) :
    ProductStep 𝕜 K →L[𝕜] ProductStep 𝕜 K :=
  (ContDiffMapSupportedIn.postcompCLM (productDirectionEvaluation (𝕜 := 𝕜) (h,0))).comp
    (ContDiffMapSupportedIn.fderivCLM 𝕜 ⊤ ⊤)

@[simp] theorem productStepDerivX_apply (K : Compacts (Domain p × Domain q))
    (h : Domain p) (f : ProductStep 𝕜 K) (p : Domain p × Domain q) :
    productStepDerivX K h f p = fderiv ℝ f p (h,0) := by
  change productDirectionEvaluation (h,0) (ContDiffMapSupportedIn.fderivCLM 𝕜 ⊤ ⊤ f p) = _
  have heq := ContDiffMapSupportedIn.fderivCLM_apply_of_le
    (𝕜 := 𝕜) (n := ⊤) (k := ⊤) f (by simp)
  exact congrArg (fun g => g p (h,0)) heq

@[simp] theorem productStepDerivX_inclusion (K : Compacts (Domain p × Domain q))
    (h : Domain p) (f : ProductStep 𝕜 K) :
    productStepInclusion K (productStepDerivX K h f) = kernelDerivX h (productStepInclusion K f) := by
  ext p
  rw [kernelDerivX_apply]
  change productStepDerivX K h f p = fderiv ℝ f p (h,0)
  exact productStepDerivX_apply K h f p

def kernelWordX : List (Fin p) → KernelTests 𝕜 p q →L[𝕜] KernelTests 𝕜 p q
  | [] => ContinuousLinearMap.id 𝕜 _
  | i :: w => (kernelDerivX (coordinateVector i)).comp (kernelWordX w)

def productStepWordX (K : Compacts (Domain p × Domain q)) :
    List (Fin p) → ProductStep 𝕜 K →L[𝕜] ProductStep 𝕜 K
  | [] => ContinuousLinearMap.id 𝕜 _
  | i :: w => (productStepDerivX K (coordinateVector i)).comp (productStepWordX K w)

theorem kernelAction_partial (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) (w : List (Fin p)) :
    partialFunction w (kernelActionTest v H) = kernelActionTest v (kernelWordX w H) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (fun x => fderiv ℝ (partialFunction w (kernelActionTest v H)) x
      (coordinateVector i)) = _
    rw [ih]
    funext x
    exact kernelAction_fderiv v (kernelWordX w H) x (coordinateVector i)

@[simp] theorem productStepWordX_inclusion (K : Compacts (Domain p × Domain q))
    (f : ProductStep 𝕜 K) (w : List (Fin p)) :
    productStepInclusion K (productStepWordX K w f) = kernelWordX w (productStepInclusion K f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change productStepInclusion K
      (productStepDerivX K (coordinateVector i) (productStepWordX K w f)) = _
    rw [productStepDerivX_inclusion, ih]
    rfl

theorem coordinateDerivative_kernelActionStep (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (K : Compacts (Domain p × Domain q)) {k : ℕ} (a : Fin k → Fin p) (f : ProductStep 𝕜 K) :
    coordinateDerivative 𝕜 (productCompactFst K) a (kernelActionStepLM v K f) =
      boundedKernelActionStepCLM v K (productStepWordX K (List.ofFn a) f) := by
  ext x
  rw [coordinateDerivative_apply]
  change iteratedFDeriv ℝ k (kernelActionTest v (productStepInclusion K f)) x
      (fun j => coordinateVector (a j)) =
    kernelActionTest v (productStepInclusion K (productStepWordX K (List.ofFn a) f)) x
  rw [← partialFunction_ofFn k a _ (kernelActionTest v (productStepInclusion K f)).contDiff,
    kernelAction_partial, productStepWordX_inclusion]

theorem kernelActionStep_continuous (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (K : Compacts (Domain p × Domain q)) : Continuous (kernelActionStepLM v K) := by
  classical
  apply (step_seminorm_topology 𝕜 p (productCompactFst K)).continuous_of_continuous_comp
  intro m
  unfold stepSeminorm
  rw [SeminormFamily.finset_sup_comp]
  apply Seminorm.continuous_finsetSup
  intro k hk
  change Continuous ((Finset.univ.sup (coordinateSeminorm (k := k) 𝕜
    (productCompactFst K))).comp (kernelActionStepLM v K))
  rw [SeminormFamily.finset_sup_comp]
  apply Seminorm.continuous_finsetSup
  intro a ha
  have heq : (coordinateSeminorm 𝕜 (productCompactFst K) a).comp (kernelActionStepLM v K) =
      (normSeminorm 𝕜 (Domain p →ᵇ 𝕜)).comp
        ((boundedKernelActionStepCLM v K).comp (productStepWordX K (List.ofFn a))).toLinearMap := by
    ext f
    change ‖coordinateDerivative 𝕜 (productCompactFst K) a (kernelActionStepLM v K f)‖ = _
    rw [coordinateDerivative_kernelActionStep]
    rfl
  change Continuous ((coordinateSeminorm 𝕜 (productCompactFst K) a).comp
    (kernelActionStepLM v K))
  rw [heq]
  exact ((boundedKernelActionStepCLM v K).comp (productStepWordX K (List.ofFn a))).continuous.norm


def kernelActionCLM (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q))) :
    KernelTests 𝕜 p q →L[𝕜] Tests 𝕜 (⊤ : Opens (Domain p)) :=
  TestFunction.mkCLM 𝕜 (kernelActionLM v)
    (kernelActionLM v).map_add (fun c f => (kernelActionLM v).map_smul c f)
    (by
      intro K hK
      have h := (TestFunction.continuous_ofSupportedIn (F := 𝕜) (n := ⊤)
        (Ω := (⊤ : Opens (Domain p))) (show (productCompactFst K : Set (Domain p)) ⊆ (⊤ : Opens (Domain p)) from subset_univ _)).comp
          (kernelActionStep_continuous v K)
      exact h)

@[simp] theorem kernelActionCLM_apply (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) : kernelActionCLM v H = kernelActionTest v H := rfl

def iteratedTensor (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain p)))
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q))) :
    KernelTests 𝕜 p q →L[𝕜] 𝕜 := u.comp (kernelActionCLM v)

@[simp] theorem iteratedTensor_apply (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain p)))
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) : iteratedTensor u v H = u (kernelActionTest v H) := rfl



def tensorTest (a : Tests 𝕜 (⊤ : Opens (Domain p)))
    (b : Tests 𝕜 (⊤ : Opens (Domain q))) : KernelTests 𝕜 p q where
  toFun z := a z.1 * b z.2
  contDiff' := (a.contDiff.comp contDiff_fst).mul (b.contDiff.comp contDiff_snd)
  hasCompactSupport' := by
    apply (a.hasCompactSupport.prod b.hasCompactSupport).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
    intro z hz
    exact ⟨subset_tsupport a (mul_ne_zero_iff.mp hz).1,
      subset_tsupport b (mul_ne_zero_iff.mp hz).2⟩
  tsupport_subset' := subset_univ _

def IsTensorProduct (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain p)))
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (T : KernelTests 𝕜 p q →L[𝕜] 𝕜) : Prop :=
  ∀ a b, T (tensorTest a b) = u a * v b

theorem iteratedTensor_isTensorProduct (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain p)))
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q))) :
    IsTensorProduct u v (iteratedTensor u v) := by
  intro a b
  have heq : kernelActionTest v (tensorTest a b) = v b • a := by
    ext x
    change v (kernelSection (tensorTest a b) x) = v b * a x
    have hsec : kernelSection (tensorTest a b) x = a x • b := by ext y; rfl
    rw [hsec, map_smul]
    simp [mul_comm]
  rw [iteratedTensor_apply, heq, map_smul]
  simp [mul_comm]

theorem tensorProduct_exists (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain p)))
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q))) :
    ∃ T : KernelTests 𝕜 p q →L[𝕜] 𝕜, IsTensorProduct u v T :=
  ⟨iteratedTensor u v, iteratedTensor_isTensorProduct u v⟩

end RectangularKernel

namespace RectangularTensor
open MeasureTheory Filter

abbrev RectangularTests (𝕜 : Type) [RCLike 𝕜] (p q : ℕ) :=
  TestFunction (⊤ : Opens (Domain p × Domain q)) 𝕜 ⊤

def rectangularTensorTest {𝕜 : Type} [RCLike 𝕜] {p q : ℕ}
    (a : Tests 𝕜 (⊤ : Opens (Domain p)))
    (b : Tests 𝕜 (⊤ : Opens (Domain q))) : RectangularTests 𝕜 p q where
  toFun r := a r.1 * b r.2
  contDiff' := (a.contDiff.comp contDiff_fst).mul (b.contDiff.comp contDiff_snd)
  hasCompactSupport' := by
    apply (a.hasCompactSupport.prod b.hasCompactSupport).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
    intro r hr
    exact ⟨subset_tsupport a (mul_ne_zero_iff.mp hr).1,
      subset_tsupport b (mul_ne_zero_iff.mp hr).2⟩
  tsupport_subset' := subset_univ _

def splitDomain (p q : ℕ) : Domain (p+q) ≃L[ℝ] Domain p × Domain q :=
  ((LinearEquiv.funCongrLeft ℝ ℝ finSumFinEquiv).trans
    (LinearEquiv.sumPiEquivProdPi ℝ (Fin p) (Fin q) (fun _ => ℝ))).toContinuousLinearEquiv

def splitDomainMeasurable (p q : ℕ) : Domain (p+q) ≃ᵐ Domain p × Domain q :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin p ⊕ Fin q => ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ))

lemma splitDomainMeasurable_coe (p q : ℕ) :
    (splitDomainMeasurable p q : Domain (p+q) → Domain p × Domain q) = splitDomain p q := by
  funext z
  apply Prod.ext <;> funext i <;> simp [splitDomainMeasurable, splitDomain, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft', LinearEquiv.funCongrLeft, LinearEquiv.sumPiEquivProdPi]

lemma splitDomain_volume_preserving (p q : ℕ) :
    MeasurePreserving (splitDomainMeasurable p q) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin p ⊕ Fin q => ℝ) finSumFinEquiv.symm)

def productMollifier {p q : ℕ} (ρ : Domain p → ℝ) (σ : Domain q → ℝ) : Domain (p+q) → ℝ :=
  fun z => ρ (splitDomain p q z).1 * σ (splitDomain p q z).2

lemma product_function_hasCompactSupport {p q : ℕ} (ρ : Domain p → ℝ) (σ : Domain q → ℝ)
    (hρ : HasCompactSupport ρ) (hσ : HasCompactSupport σ) :
    HasCompactSupport (fun r : Domain p × Domain q => ρ r.1 * σ r.2) := by
  apply (hρ.prod hσ).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
  intro r hr
  exact ⟨subset_tsupport ρ (mul_ne_zero_iff.mp hr).1,
    subset_tsupport σ (mul_ne_zero_iff.mp hr).2⟩

lemma productMollifier_isMollifier {p q : ℕ} (ρ : Domain p → ℝ) (σ : Domain q → ℝ)
    (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (hσ : SmoothApproximateIdentitiesSpec.IsMollifier σ) :
    SmoothApproximateIdentitiesSpec.IsMollifier (productMollifier ρ σ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hρ.1.comp contDiff_fst).mul (hσ.1.comp contDiff_snd)).comp
      (splitDomain p q).contDiff
  · exact (product_function_hasCompactSupport ρ σ hρ.2.1 hσ.2.1).comp_isClosedEmbedding
      (splitDomain p q).toHomeomorph.isClosedEmbedding
  · intro z
    exact mul_nonneg (hρ.2.2.1 _) (hσ.2.2.1 _)
  · simp only [productMollifier, ← splitDomainMeasurable_coe]
    change (∫ z, (fun r : Domain p × Domain q => ρ r.1 * σ r.2) (splitDomainMeasurable p q z)) = 1
    calc
      _ = ∫ r : Domain p × Domain q, ρ r.1 * σ r.2 :=
        (splitDomain_volume_preserving p q).integral_comp' (fun r => ρ r.1 * σ r.2)
      _ = 1 := by rw [Measure.volume_eq_prod, integral_prod_mul, hρ.2.2.2, hσ.2.2.2, one_mul]

lemma exists_mollifier (d : ℕ) : ∃ ρ : Domain d → ℝ,
    SmoothApproximateIdentitiesSpec.IsMollifier ρ := by
  let b : ContDiffBump (0 : Domain d) := ⟨1, 2, by norm_num, by norm_num⟩
  exact ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed,
    b.nonneg_normed, b.integral_normed⟩

lemma scaledKernel_productMollifier {p q : ℕ} (ρ : Domain p → ℝ) (σ : Domain q → ℝ) (ε : ℝ) (z : Domain (p+q)) :
    SmoothApproximateIdentitiesSpec.ScaledKernelValue (productMollifier ρ σ) ε z =
      SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε (splitDomain p q z).1 *
        SmoothApproximateIdentitiesSpec.ScaledKernelValue σ ε (splitDomain p q z).2 := by
  simp only [SmoothApproximateIdentitiesSpec.ScaledKernelValue, productMollifier,
    map_smul, Prod.smul_fst, Prod.smul_snd, pow_add, mul_inv_rev]
  ring

lemma reflectedTranslate_productMollifier {𝕜 : Type} [RCLike 𝕜] {p q : ℕ}
    (ρ : Domain p → ℝ) (σ : Domain q → ℝ) (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (hσ : SmoothApproximateIdentitiesSpec.IsMollifier σ)
    (ε : ℝ) (hε : ε ≠ 0) (x : Domain (p+q)) :
    pullbackCLM (splitDomain p q).symm
      (reflectedTranslate (scaledMollifierTest (productMollifier ρ σ)
        (productMollifier_isMollifier ρ σ hρ hσ) ε : Tests 𝕜 ⊤) x) =
      rectangularTensorTest (reflectedTranslate (scaledMollifierTest ρ hρ ε : Tests 𝕜 ⊤) (splitDomain p q x).1)
        (reflectedTranslate (scaledMollifierTest σ hσ ε : Tests 𝕜 ⊤) (splitDomain p q x).2) := by
  ext p
  simp only [pullbackCLM_apply, reflectedTranslate_apply, rectangularTensorTest,
    TestFunction.coe_mk, scaledMollifierTest_apply _ _ ε hε,
    scaledKernel_productMollifier, map_sub, ContinuousLinearEquiv.apply_symm_apply,
    Prod.fst_sub, Prod.snd_sub, map_mul]

lemma tensor_functional_zero {𝕜 : Type} [RCLike 𝕜] {p q : ℕ}
    (W : RectangularTests 𝕜 p q →L[𝕜] 𝕜)
    (hW : ∀ (a : Tests 𝕜 (⊤ : Opens (Domain p))) (b : Tests 𝕜 (⊤ : Opens (Domain q))),
      W (rectangularTensorTest a b) = 0) : W = 0 := by
  obtain ⟨ρ, hρ⟩ := exists_mollifier p
  obtain ⟨σ, hσ⟩ := exists_mollifier q
  let U : ScalarDistribution 𝕜 (⊤ : Opens (Domain (p+q))) :=
    W.comp (pullbackCLM (splitDomain p q).symm)
  have hconv : ∀ ε : ℝ, 0 < ε → ∀ x : Domain (p+q),
      distributionConvolution U (scaledMollifierTest (productMollifier ρ σ)
        (productMollifier_isMollifier ρ σ hρ hσ) ε) x = 0 := by
    intro ε hε x
    change W (pullbackCLM (splitDomain p q).symm _) = 0
    rw [reflectedTranslate_productMollifier ρ σ hρ hσ ε hε.ne']
    exact hW _ _
  have hU : U = 0 := by
    ext ψ
    have ht := distributionConvolution_approximation U (productMollifier ρ σ)
      (productMollifier_isMollifier ρ σ hρ hσ) ψ
    have heq : (fun ε => ∫ x, distributionConvolution U
        (scaledMollifierTest (productMollifier ρ σ) (productMollifier_isMollifier ρ σ hρ hσ) ε) x * ψ x)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : 𝕜)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [hconv ε hε, zero_mul, integral_zero]
    have hlim : Tendsto (fun _ : ℝ => (0 : 𝕜)) (𝓝[>] (0 : ℝ)) (𝓝 (U ψ)) :=
      ht.congr' heq
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  ext ψ
  have he := congrArg (fun L : ScalarDistribution 𝕜 (⊤ : Opens (Domain (p+q))) =>
    L (pullbackCLM (splitDomain p q) ψ)) hU
  change W (pullbackCLM (splitDomain p q).symm (pullbackCLM (splitDomain p q) ψ)) = 0 at he
  convert he using 1
  congr 1
  ext p
  simp only [pullbackCLM_apply, ContinuousLinearEquiv.apply_symm_apply]

lemma tensor_functional_ext {𝕜 : Type} [RCLike 𝕜] {p q : ℕ}
    (T T' : RectangularTests 𝕜 p q →L[𝕜] 𝕜)
    (h : ∀ (a : Tests 𝕜 (⊤ : Opens (Domain p))) (b : Tests 𝕜 (⊤ : Opens (Domain q))),
      T (rectangularTensorTest a b) = T' (rectangularTensorTest a b)) :
    T = T' := by
  apply sub_eq_zero.mp
  apply tensor_functional_zero
  intro a b
  exact sub_eq_zero.mpr (h a b)



end RectangularTensor

section TensorDerivatives
open Filter
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}


def tensorLeftPartialCLM (i : Fin d) : ProductTests 𝕜 d →L[𝕜] ProductTests 𝕜 d :=
  TestFunction.lineDerivCLM 𝕜 (coordinateVector i, (0 : Domain d))

def tensorRightPartialCLM (i : Fin d) : ProductTests 𝕜 d →L[𝕜] ProductTests 𝕜 d :=
  TestFunction.lineDerivCLM 𝕜 ((0 : Domain d), coordinateVector i)

lemma lineDeriv_test_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : TestFunction (⊤ : Opens E) 𝕜 ⊤) (v p : E) :
    TestFunction.lineDerivCLM 𝕜 (n := ⊤) (k := ⊤) v φ p = fderiv ℝ φ p v := by
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]

lemma tensorLeftPartialCLM_tensor (i : Fin d) (a b : Tests 𝕜 (⊤ : Opens (Domain d))) :
    tensorLeftPartialCLM i (tensorTest a b) = tensorTest (testPartialCLM [i] a) b := by
  ext p
  rw [tensorLeftPartialCLM, lineDeriv_test_apply]
  have ha := (a.contDiff.differentiable (by simp) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hb := (b.contDiff.differentiable (by simp) p.2).hasFDerivAt.comp p hasFDerivAt_snd
  change fderiv ℝ ((a : Domain d → 𝕜) ∘ Prod.fst * (b : Domain d → 𝕜) ∘ Prod.snd) p
    (coordinateVector i, 0) = _
  rw [(ha.mul hb).fderiv]
  change _ = (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) a) p.1 * b p.2
  rw [lineDeriv_test_apply]
  simp [mul_comm]

lemma tensorRightPartialCLM_tensor (i : Fin d) (a b : Tests 𝕜 (⊤ : Opens (Domain d))) :
    tensorRightPartialCLM i (tensorTest a b) = tensorTest a (testPartialCLM [i] b) := by
  ext p
  rw [tensorRightPartialCLM, lineDeriv_test_apply]
  have ha := (a.contDiff.differentiable (by simp) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hb := (b.contDiff.differentiable (by simp) p.2).hasFDerivAt.comp p hasFDerivAt_snd
  change fderiv ℝ ((a : Domain d → 𝕜) ∘ Prod.fst * (b : Domain d → 𝕜) ∘ Prod.snd) p
    (0, coordinateVector i) = _
  rw [(ha.mul hb).fderiv]
  change _ = a p.1 * (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) b) p.2
  rw [lineDeriv_test_apply]
  simp

lemma tensorLeftPartial_isTensorProduct (i : Fin d)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (T : ProductTests 𝕜 d →L[𝕜] 𝕜) (hT : IsTensorProduct u v T) :
    IsTensorProduct (-u.comp (testPartialCLM [i])) v (-T.comp (tensorLeftPartialCLM i)) := by
  intro a b
  change -T (tensorLeftPartialCLM i (tensorTest a b)) = -u (testPartialCLM [i] a) * v b
  rw [tensorLeftPartialCLM_tensor, hT, neg_mul]

lemma tensorRightPartial_isTensorProduct (i : Fin d)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (T : ProductTests 𝕜 d →L[𝕜] 𝕜) (hT : IsTensorProduct u v T) :
    IsTensorProduct u (-v.comp (testPartialCLM [i])) (-T.comp (tensorRightPartialCLM i)) := by
  intro a b
  change -T (tensorRightPartialCLM i (tensorTest a b)) = u a * -v (testPartialCLM [i] b)
  rw [tensorRightPartialCLM_tensor, hT, mul_neg]


lemma fderiv_addition_apply (ψ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (p ν : Domain d × Domain d) :
    fderiv ℝ (fun q : Domain d × Domain d => ψ (q.1 + q.2)) p ν =
      fderiv ℝ ψ (p.1 + p.2) (ν.1 + ν.2) := by
  have h := (ψ.contDiff.differentiable (by simp) (p.1+p.2)).hasFDerivAt.comp p
    (hasFDerivAt_fst.add hasFDerivAt_snd)
  change fderiv ℝ ((ψ : Domain d → 𝕜) ∘ (Prod.fst + Prod.snd)) p ν = _
  rw [h.fderiv]
  rfl

lemma cutoffAddition_partial_local (i : Fin d) (ν : Domain d × Domain d)
    (hν : ν.1 + ν.2 = coordinateVector i)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : AdmissibleConvolutionCutoff u v ψ χ) :
    ∃ V : Set (Domain d × Domain d), IsOpen V ∧
      (distributionSupport u ×ˢ distributionSupport v) ⊆ V ∧
      EqOn (TestFunction.lineDerivCLM 𝕜 (n := ⊤) (k := ⊤) ν (cutoffAdditionTest χ ψ))
        (cutoffAdditionTest χ (testPartialCLM [i] ψ)) V := by
  obtain ⟨V, hV, hslice, hχV⟩ := hχ
  let O : Set (Domain d × Domain d) := V ∪ (fun p => p.1+p.2) ⁻¹' (tsupport ψ)ᶜ
  have hO : IsOpen O := hV.union ((isClosed_tsupport ψ).isOpen_compl.preimage
    (continuous_fst.add continuous_snd))
  refine ⟨O, hO, ?_, ?_⟩
  · intro p hp
    by_cases h : p.1+p.2 ∈ tsupport ψ
    · exact Or.inl (hslice ⟨hp, h⟩)
    · exact Or.inr h
  · intro p hp
    rw [lineDeriv_test_apply]
    rcases hp with hp | hp
    · have he : (cutoffAdditionTest χ ψ : Domain d × Domain d → 𝕜) =ᶠ[𝓝 p]
          (fun q => ψ (q.1+q.2)) := by
        filter_upwards [hV.mem_nhds hp] with q hq
        change χ q • ψ (q.1+q.2) = _
        simp only [hχV hq, Pi.one_apply, one_smul]
      rw [he.fderiv_eq, fderiv_addition_apply, hν]
      change _ = χ p • (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) ψ) (p.1+p.2)
      simp only [hχV hp, Pi.one_apply, one_smul, lineDeriv_test_apply]
    · have heψ : (fun q : Domain d × Domain d => ψ (q.1+q.2)) =ᶠ[𝓝 p] 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
          ((continuous_fst.add continuous_snd).tendsto p)
      have he : (cutoffAdditionTest χ ψ : Domain d × Domain d → 𝕜) =ᶠ[𝓝 p] 0 := by
        filter_upwards [heψ] with q hq
        change χ q • ψ (q.1+q.2) = 0
        simp only [hq, Pi.zero_apply, smul_zero]
      rw [he.fderiv_eq]
      have hz : (testPartialCLM [i] ψ) (p.1+p.2) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hp (testPartial_tsupport_subset [i] ψ h))
      change _ = χ p • (testPartialCLM [i] ψ) (p.1+p.2)
      rw [hz, smul_zero]
      simp


lemma admissible_cutoff_partial_test (i : Fin d)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : AdmissibleConvolutionCutoff u v ψ χ) :
    AdmissibleConvolutionCutoff u v (testPartialCLM [i] ψ) χ := by
  obtain ⟨V, hV, hSV, hχV⟩ := hχ
  refine ⟨V, hV, ?_, hχV⟩
  intro p hp
  exact hSV ⟨hp.1, testPartial_tsupport_subset [i] ψ hp.2⟩


lemma first_derivative_eq (i : Fin d)
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue 𝕜 d ⊤ [i] u =
      -u.comp (testPartialCLM [i]) := by
  ext φ
  change (-1 : 𝕜) ^ 1 * u (testPartialCLM [i] φ) = -u (testPartialCLM [i] φ)
  rw [pow_one, neg_one_mul]

lemma first_derivative_support (i : Fin d)
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    distributionSupport (-u.comp (testPartialCLM [i])) ⊆ distributionSupport u := by
  rw [← first_derivative_eq]
  exact derivative_support 𝕜 d u [i]

lemma admissible_cutoff_first_derivative_left (i : Fin d)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : AdmissibleConvolutionCutoff u v ψ χ) :
    AdmissibleConvolutionCutoff (-u.comp (testPartialCLM [i])) v ψ χ := by
  obtain ⟨V, hV, hSV, hχV⟩ := hχ
  refine ⟨V, hV, ?_, hχV⟩
  intro p hp
  exact hSV ⟨⟨first_derivative_support i u hp.1.1, hp.1.2⟩, hp.2⟩

lemma convolution_derivative_left_single (i : Fin d)
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (h : IsProperConvolution u v w) :
    IsProperConvolution (-u.comp (testPartialCLM [i])) v (-w.comp (testPartialCLM [i])) := by
  obtain ⟨T, hT⟩ := h.2.1
  let DT : ProductTests 𝕜 d →L[𝕜] 𝕜 := -T.comp (tensorLeftPartialCLM i)
  have hDT : IsTensorProduct (-u.comp (testPartialCLM [i])) v DT :=
    tensorLeftPartial_isTensorProduct i u v T hT
  have hprop : Convolvable (-u.comp (testPartialCLM [i])) v := by
    rw [← first_derivative_eq]
    exact (derivative_convolvable 𝕜 d u v [i] h.1).1
  refine ⟨hprop, ⟨DT, hDT⟩, ?_⟩
  intro T' hT' ψ χ hχ
  rw [tensor_product_unique _ v T' DT hT' hDT]
  obtain ⟨χ₀, hχ₀⟩ := cutoff_existence 𝕜 d u v h.1 ψ
  have hχ₀d := admissible_cutoff_first_derivative_left i u v ψ χ₀ hχ₀
  obtain ⟨V, hV, hSV, hEq⟩ := cutoffAddition_partial_local i (coordinateVector i, 0)
    (by simp) u v ψ χ₀ hχ₀
  have hpartial : T (tensorLeftPartialCLM i (cutoffAdditionTest χ₀ ψ)) =
      T (cutoffAdditionTest χ₀ (testPartialCLM [i] ψ)) :=
    tensor_local hT _ _ V hV hSV hEq
  have hpair := h.2.2 T hT (testPartialCLM [i] ψ) χ₀
    (admissible_cutoff_partial_test i u v ψ χ₀ hχ₀)
  obtain ⟨O, hO, hSO, hcut⟩ := cutoff_agreement 𝕜 d _ v ψ χ₀ χ hχ₀d hχ
  have hDpair : DT (cutoffAdditionTest χ₀ ψ) = DT (cutoffAdditionTest χ ψ) :=
    tensor_local hDT _ _ O hO hSO hcut
  change -w (testPartialCLM [i] ψ) = DT (cutoffAdditionTest χ ψ)
  calc
    _ = -T (cutoffAdditionTest χ₀ (testPartialCLM [i] ψ)) := congrArg Neg.neg hpair
    _ = -T (tensorLeftPartialCLM i (cutoffAdditionTest χ₀ ψ)) := congrArg Neg.neg hpartial.symm
    _ = DT (cutoffAdditionTest χ₀ ψ) := rfl
    _ = _ := hDpair

lemma convolution_derivative_right_single (i : Fin d)
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (h : IsProperConvolution u v w) :
    IsProperConvolution u (-v.comp (testPartialCLM [i])) (-w.comp (testPartialCLM [i])) := by
  apply convolution_commutativity 𝕜 d
  apply convolution_derivative_left_single i v u w
  exact convolution_commutativity 𝕜 d u v w h


theorem convolution_derivatives :
    Specs.ExpandedFA.Distributions.ProperSupportConvolution.convolutionDerivativesType := by
  intro 𝕜 _ d u v w α
  induction α generalizing u v w with
  | nil =>
    intro h
    change IsProperConvolution (distributionDerivative 𝕜 d ⊤ [] u) v
        (distributionDerivative 𝕜 d ⊤ [] w) ∧
      IsProperConvolution u (distributionDerivative 𝕜 d ⊤ [] v)
        (distributionDerivative 𝕜 d ⊤ [] w)
    simpa only [distributionDerivative_nil] using And.intro h h
  | cons i α ih =>
    intro h
    have hl := (ih _ _ _ (convolution_derivative_left_single i u v w h)).1
    have hr := (ih _ _ _ (convolution_derivative_right_single i u v w h)).2
    change IsProperConvolution (distributionDerivative 𝕜 d ⊤ (i :: α) u) v
        (distributionDerivative 𝕜 d ⊤ (i :: α) w) ∧
      IsProperConvolution u (distributionDerivative 𝕜 d ⊤ (i :: α) v)
        (distributionDerivative 𝕜 d ⊤ (i :: α) w)
    rw [distributionDerivative_cons, distributionDerivative_cons, distributionDerivative_cons]
    exact ⟨hl, hr⟩

end TensorDerivatives

namespace RectangularKernel
variable {𝕜 : Type} [RCLike 𝕜] {p q : ℕ}

/-- Only the portion of the kernel support lying above the distribution support
can contribute to an action on vertical sections. -/
def kernelSupportProjection (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) : Set (Domain p) :=
  Prod.fst '' (tsupport H ∩ (Set.univ ×ˢ distributionSupport v))

theorem kernelSupportProjection_compact
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q))) (H : KernelTests 𝕜 p q) :
    IsCompact (kernelSupportProjection v H) :=
  (H.hasCompactSupport.inter_right
    (isClosed_univ.prod (support_closed 𝕜 q v))).image continuous_fst

theorem kernelSection_pairing_eq_zero_off_projection
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q))) (H : KernelTests 𝕜 p q)
    (x : Domain p) (hx : x ∉ kernelSupportProjection v H) :
    v (kernelSection H x) = 0 := by
  let W : Set (Domain q) := (fun y => (x, y)) ⁻¹' (tsupport H)ᶜ
  have hW : IsOpen W := isClosed_closure.isOpen_compl.preimage
    (continuous_const.prodMk continuous_id)
  have hSW : distributionSupport v ⊆ W := by
    intro y hy hp
    apply hx
    exact ⟨(x, y), ⟨hp, Set.mem_univ x, hy⟩, rfl⟩
  have heq := pairing_locality 𝕜 q ⊤ v (kernelSection H x) 0 W hW hSW (by
    intro y hy
    change H (x, y) = 0
    exact image_eq_zero_of_notMem_tsupport hy)
  simpa using heq

theorem kernel_action_tsupport_subset_projection
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q))) (H : KernelTests 𝕜 p q)
    (k : Tests 𝕜 (⊤ : Opens (Domain p)))
    (hk : ∀ x, k x = v (kernelSection H x)) :
    tsupport k ⊆ kernelSupportProjection v H := by
  apply closure_minimal _ (kernelSupportProjection_compact v H).isClosed
  intro x hx
  by_contra hxn
  apply hx
  rw [hk x]
  exact kernelSection_pairing_eq_zero_off_projection v H x hxn

/-- A distribution applied to vertical kernel sections vanishes when the
kernel vanishes near the product of the two distribution supports. This needs
only the actual section pairing formula for the supplied outer test. -/
theorem iterated_kernel_pairing_eq_zero
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain p)))
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H : KernelTests 𝕜 p q) (k : Tests 𝕜 (⊤ : Opens (Domain p)))
    (hk : ∀ x, k x = v (kernelSection H x))
    (V : Set (Domain p × Domain q)) (hV : IsOpen V)
    (hS : distributionSupport u ×ˢ distributionSupport v ⊆ V)
    (hH : EqOn H 0 V) : u k = 0 := by
  have hts : tsupport H ⊆ Vᶜ := by
    apply closure_minimal _ hV.isClosed_compl
    intro p hp hpV
    exact hp (hH hpV)
  have hSA : distributionSupport u ⊆ (kernelSupportProjection v H)ᶜ := by
    intro x hx hA
    obtain ⟨p, ⟨hp, hpv⟩, rfl⟩ := hA
    exact hts hp (hS ⟨hx, hpv.2⟩)
  have heq := pairing_locality 𝕜 p ⊤ u k 0 (kernelSupportProjection v H)ᶜ
    (kernelSupportProjection_compact v H).isClosed.isOpen_compl hSA (by
      intro x hx
      change k x = 0
      rw [hk x]
      exact kernelSection_pairing_eq_zero_off_projection v H x hx)
  simpa using heq


/-- Agreement near the product support gives equality of the iterated pairings. -/
theorem iterated_kernel_pairing_congr
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain p)))
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H H' : KernelTests 𝕜 p q) (k k' : Tests 𝕜 (⊤ : Opens (Domain p)))
    (hk : ∀ x, k x = v (kernelSection H x))
    (hk' : ∀ x, k' x = v (kernelSection H' x))
    (V : Set (Domain p × Domain q)) (hV : IsOpen V)
    (hS : distributionSupport u ×ˢ distributionSupport v ⊆ V)
    (hH : EqOn H H' V) : u k = u k' := by
  have hd : ∀ x, (k - k') x = v (kernelSection (H - H') x) := by
    intro x
    change k x - k' x = _
    rw [hk x, hk' x, ← map_sub]
    congr 1
  have hdiff : EqOn (H - H') 0 V := by
    intro p hp
    change H p - H' p = 0
    exact sub_eq_zero.mpr (hH hp)
  have hz := iterated_kernel_pairing_eq_zero u v (H - H') (k - k') hd V hV hS hdiff
  simpa only [map_sub, sub_eq_zero] using hz


theorem iteratedTensor_locality
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain p)))
    (v : ScalarDistribution 𝕜 (⊤ : Opens (Domain q)))
    (H H' : KernelTests 𝕜 p q) (V : Set (Domain p × Domain q)) (hV : IsOpen V)
    (hS : distributionSupport u ×ˢ distributionSupport v ⊆ V)
    (hH : EqOn H H' V) : iteratedTensor u v H = iteratedTensor u v H' :=
  iterated_kernel_pairing_congr u v H H' _ _ (fun _ => rfl) (fun _ => rfl) V hV hS hH

end RectangularKernel

namespace LocalizedPullback
open WithSeminorms
set_option maxHeartbeats 1600000
variable {𝕜 : Type} [RCLike 𝕜]
  {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

def cutoffTest (L : E' →L[ℝ] E) (χ : TestFunction (⊤ : Opens E') ℝ ⊤)
    (ψ : TestFunction (⊤ : Opens E) 𝕜 ⊤) : TestFunction (⊤ : Opens E') 𝕜 ⊤ where
  toFun x := χ x • ψ (L x)
  contDiff' := χ.contDiff.smul (ψ.contDiff.comp L.contDiff)
  hasCompactSupport' := χ.hasCompactSupport.smul_right
  tsupport_subset' := subset_univ _

private theorem pullback_derivative_bound (L : E' →L[ℝ] E) (K : Compacts (E))
    (f : ContDiffMapSupportedIn E 𝕜 ⊤ K) (n : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ n (fun p : E' => f (L p)) x‖ ≤
      ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K n f * ‖L‖ ^ n := by
  change ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right f.contDiff x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simpa using mul_le_mul_of_nonneg_right
    (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜 (f := f))
    (pow_nonneg (norm_nonneg _) n)

private def cutoffStep (χ : TestFunction (⊤ : Opens E') ℝ ⊤) :
    ContDiffMapSupportedIn (E') ℝ ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ :=
  ContDiffMapSupportedIn.of_support_subset χ.contDiff (subset_tsupport χ)

private def cutoffPullbackStepLM (L : E' →L[ℝ] E) (χ : TestFunction (⊤ : Opens E') ℝ ⊤) (K : Compacts (E)) :
    ContDiffMapSupportedIn E 𝕜 ⊤ K →ₗ[𝕜] ContDiffMapSupportedIn (E') 𝕜 ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ where
  toFun f := ⟨fun p => χ p • f (L p),
    χ.contDiff.smul (f.contDiff.comp L.contDiff), by
      intro p hp
      simp [image_eq_zero_of_notMem_tsupport hp]⟩
  map_add' f g := by
    ext p
    change χ p • (f (L p) + g (L p)) = χ p • f (L p) + χ p • g (L p)
    exact smul_add _ _ _
  map_smul' c f := by
    ext p
    change χ p • (c • f (L p)) = c • (χ p • f (L p))
    exact smul_comm _ _ _

private def cutoffPullbackBound (L : E' →L[ℝ] E) (χ : TestFunction (⊤ : Opens E') ℝ ⊤) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    ContDiffMapSupportedIn.seminorm ℝ _ _ ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ i (cutoffStep χ) *
      ‖L‖ ^ (n-i)

private theorem cutoffPullbackBound_nonneg (L : E' →L[ℝ] E) (χ : TestFunction (⊤ : Opens E') ℝ ⊤) (n : ℕ) :
    0 ≤ cutoffPullbackBound L χ n := by
  unfold cutoffPullbackBound
  apply Finset.sum_nonneg
  intro i hi
  positivity

private theorem cutoffPullbackStep_bound (L : E' →L[ℝ] E) (χ : TestFunction (⊤ : Opens E') ℝ ⊤) (K : Compacts (E))
    (f : ContDiffMapSupportedIn E 𝕜 ⊤ K) (n : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ n (cutoffPullbackStepLM L χ K f) x‖ ≤
      cutoffPullbackBound L χ n *
        ((Finset.Iic n).sup (ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K)) f := by
  let P := ((Finset.Iic n).sup (ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K)) f
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
        ‖iteratedFDeriv ℝ (n-i) (fun p : E' => f (L p)) x‖ :=
      norm_iteratedFDeriv_smul_le χ.contDiff
        (f.contDiff.comp L.contDiff) x (by simp)
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ContDiffMapSupportedIn.seminorm ℝ _ _ ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ i (cutoffStep χ) *
        (P * ‖L‖ ^ (n-i)) := by
      gcongr with i hi
      · exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ
          (f := cutoffStep χ)
      · exact (pullback_derivative_bound L K f (n-i) x).trans
          (mul_le_mul_of_nonneg_right
            (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr (Nat.sub_le n i)))
            (pow_nonneg (norm_nonneg _) _))
    _ = cutoffPullbackBound L χ n * P := by
      simp only [cutoffPullbackBound, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private def cutoffPullbackStepCLM (L : E' →L[ℝ] E) (χ : TestFunction (⊤ : Opens E') ℝ ⊤) (K : Compacts (E)) :
    ContDiffMapSupportedIn E 𝕜 ⊤ K →L[𝕜] ContDiffMapSupportedIn (E') 𝕜 ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ where
  toLinearMap := cutoffPullbackStepLM L χ K
  cont := by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun n => ?_)
    refine ⟨Finset.Iic n, cutoffPullbackBound L χ n, fun f => ?_⟩
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff 𝕜
      (mul_nonneg (cutoffPullbackBound_nonneg L χ n) (apply_nonneg _ _)) _ _).mpr
    intro x hx
    exact cutoffPullbackStep_bound L χ K f n x

/-- Fixing a cutoff makes pullback by addition continuous in the LF topology. -/
def cutoffCLM (L : E' →L[ℝ] E) (χ : TestFunction (⊤ : Opens E') ℝ ⊤) :
    TestFunction (⊤ : Opens E) 𝕜 ⊤ →L[𝕜] TestFunction (⊤ : Opens E') 𝕜 ⊤ :=
  TestFunction.mkCLM 𝕜 (cutoffTest L χ)
    (by intro f g; ext p; simp [cutoffTest, smul_add])
    (by
      intro c f
      ext p
      change χ p • (c • f (L p)) = c • (χ p • f (L p))
      exact smul_comm _ _ _)
    (by
      intro K hK
      exact (TestFunction.ofSupportedInCLM (Ω := (⊤ : Opens (E'))) 𝕜
        (show (tsupport χ) ⊆ (⊤ : Opens (E')) from subset_univ _)).continuous.comp
        (cutoffPullbackStepCLM L χ K).continuous)

@[simp] theorem cutoffCLM_apply (L : E' →L[ℝ] E) (χ : TestFunction (⊤ : Opens E') ℝ ⊤)
    (ψ : TestFunction (⊤ : Opens E) 𝕜 ⊤) :
    cutoffCLM L χ ψ = cutoffTest L χ ψ := rfl


@[simp] theorem cutoffCLM_apply_apply (L : E' →L[ℝ] E)
    (χ : TestFunction (⊤ : Opens E') ℝ ⊤)
    (ψ : TestFunction (⊤ : Opens E) 𝕜 ⊤) (x : E') :
    cutoffCLM L χ ψ x = χ x • ψ (L x) := rfl

end LocalizedPullback

section TripleTensorGrouping
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}


def encodedTensor (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    ScalarDistribution 𝕜 (⊤ : Opens (Domain (d+d))) :=
  (iteratedTensor u v).comp (pullbackCLM (RectangularTensor.splitDomain d d).symm)

def tripleReassoc (d : ℕ) : (Domain (d+d) × Domain d) ≃L[ℝ] (Domain d × Domain (d+d)) :=
  ((RectangularTensor.splitDomain d d).prodCongr (ContinuousLinearEquiv.refl ℝ _)).trans
    ((ContinuousLinearEquiv.prodAssoc ℝ (Domain d) (Domain d) (Domain d)).trans
      ((ContinuousLinearEquiv.refl ℝ _).prodCongr (RectangularTensor.splitDomain d d).symm))

@[simp] theorem tripleReassoc_apply (p : Domain (d+d) × Domain d) :
    tripleReassoc d p = ((RectangularTensor.splitDomain d d p.1).1,
      (RectangularTensor.splitDomain d d).symm ((RectangularTensor.splitDomain d d p.1).2, p.2)) := rfl

@[simp] theorem tripleReassoc_symm_apply (p : Domain d × Domain (d+d)) :
    (tripleReassoc d).symm p =
      ((RectangularTensor.splitDomain d d).symm (p.1, (RectangularTensor.splitDomain d d p.2).1),
        (RectangularTensor.splitDomain d d p.2).2) := rfl

lemma triple_grouping_section
    (F : Tests 𝕜 (⊤ : Opens (Domain (d+d))))
    (c : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) :
    pullbackCLM (RectangularTensor.splitDomain d d).symm
      (RectangularKernel.kernelSection (pullbackCLM (tripleReassoc d).symm
        (RectangularTensor.rectangularTensorTest F c)) x) =
      tensorTest (kernelSection (pullbackCLM (RectangularTensor.splitDomain d d).symm F) x) c := by
  ext p
  simp only [pullbackCLM_apply, RectangularKernel.kernelSection, TestFunction.coe_mk,
    RectangularTensor.rectangularTensorTest, tripleReassoc_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, tensorTest, kernelSection]
  rfl

lemma triple_grouping_kernelAction
    (v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (F : Tests 𝕜 (⊤ : Opens (Domain (d+d))))
    (c : Tests 𝕜 (⊤ : Opens (Domain d))) :
    RectangularKernel.kernelActionTest (encodedTensor v w)
      (pullbackCLM (tripleReassoc d).symm (RectangularTensor.rectangularTensorTest F c)) =
      w c • kernelActionTest v (pullbackCLM (RectangularTensor.splitDomain d d).symm F) := by
  ext x
  change iteratedTensor v w
    (pullbackCLM (RectangularTensor.splitDomain d d).symm
      (RectangularKernel.kernelSection (pullbackCLM (tripleReassoc d).symm
        (RectangularTensor.rectangularTensorTest F c)) x)) = _
  rw [triple_grouping_section, iteratedTensor_isTensorProduct v w]
  change v (kernelSection (pullbackCLM (RectangularTensor.splitDomain d d).symm F) x) * w c =
    w c * v (kernelSection (pullbackCLM (RectangularTensor.splitDomain d d).symm F) x)
  exact mul_comm _ _

theorem triple_tensor_grouping
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    RectangularKernel.iteratedTensor (encodedTensor u v) w =
      (RectangularKernel.iteratedTensor u (encodedTensor v w)).comp (pullbackCLM (tripleReassoc d).symm) := by
  apply RectangularTensor.tensor_functional_ext
  intro F c
  change RectangularKernel.iteratedTensor (encodedTensor u v) w
    (RectangularKernel.tensorTest F c) = _
  rw [RectangularKernel.iteratedTensor_isTensorProduct]
  change iteratedTensor u v (pullbackCLM (RectangularTensor.splitDomain d d).symm F) * w c =
    u (RectangularKernel.kernelActionTest (encodedTensor v w)
      (pullbackCLM (tripleReassoc d).symm (RectangularTensor.rectangularTensorTest F c)))
  rw [triple_grouping_kernelAction, map_smul]
  change u (kernelActionTest v (pullbackCLM (RectangularTensor.splitDomain d d).symm F)) * w c =
    w c * u (kernelActionTest v (pullbackCLM (RectangularTensor.splitDomain d d).symm F))
  exact mul_comm _ _


theorem encodedTensor_support
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) :
    distributionSupport (encodedTensor u v) ⊆
      (RectangularTensor.splitDomain d d) ⁻¹' (distributionSupport u ×ˢ distributionSupport v) := by
  let P := RectangularTensor.splitDomain d d
  let O : Set (Domain (d+d)) := (P ⁻¹' (distributionSupport u ×ˢ distributionSupport v))ᶜ
  have hO : IsOpen O := ((support_closed 𝕜 d u).prod (support_closed 𝕜 d v)).preimage
    P.continuous |>.isOpen_compl
  intro z hz
  by_contra hn
  apply hz.2
  refine mem_sUnion.mpr ⟨O, ⟨hO, subset_univ _, ?_⟩, hn⟩
  intro ψ hψ
  let H := pullbackCLM P.symm ψ
  let V : Set (Domain d × Domain d) := (P '' tsupport ψ)ᶜ
  have hV : IsOpen V := (ψ.hasCompactSupport.image P.continuous).isClosed.isOpen_compl
  have hSV : distributionSupport u ×ˢ distributionSupport v ⊆ V := by
    intro p hp
    rintro ⟨y, hy, hPy⟩
    exact hψ hy (by change P y ∈ distributionSupport u ×ˢ distributionSupport v; rwa [hPy])
  have hH : EqOn H 0 V := by
    intro p hp
    change ψ (P.symm p) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hy
    exact hp ⟨P.symm p, hy, P.apply_symm_apply p⟩
  have he := tensor_local (iteratedTensor_isTensorProduct u v) H 0 V hV hSV hH
  change iteratedTensor u v H = 0
  exact he.trans ((iteratedTensor u v).map_zero)

end TripleTensorGrouping

section AssociativityGeometry
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

theorem associativity_outer_convolvable
    (u v w a b : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (htriple : TripleAdditionProper (distributionSupport u) (distributionSupport v)
      (distributionSupport w))
    (ha : IsProperConvolution u v a) (hb : IsProperConvolution v w b) :
    Convolvable a w ∧ Convolvable u b := by
  constructor
  · exact properness_monotone d _ _ _ _ (triple_grouped d _ _ _ htriple)
      (support_closed 𝕜 d a) (support_closed 𝕜 d w)
      (convolution_support 𝕜 d u v a ha) Subset.rfl
  · have hg : AdditionProper (distributionSupport v + distributionSupport w)
        (distributionSupport u) :=
      triple_grouped d _ _ _ (triple_rotation d _ _ _ htriple)
    exact properness_monotone d _ _ _ _ ((properness_symmetry d _ _).mp hg)
      (support_closed 𝕜 d u) (support_closed 𝕜 d b) Subset.rfl
      (convolution_support 𝕜 d v w b hb)

abbrev TripleTests (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  TestFunction (⊤ : Opens ((Domain d × Domain d) × Domain d)) 𝕜 ⊤

/-- Properness supplies a smooth cutoff on the visible triple support. -/
theorem triple_cutoff_existence
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (htriple : TripleAdditionProper (distributionSupport u) (distributionSupport v)
      (distributionSupport w)) (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    ∃ (χ : TripleTests ℝ d) (V : Set ((Domain d × Domain d) × Domain d)),
      IsOpen V ∧
      (((distributionSupport u ×ˢ distributionSupport v) ×ˢ distributionSupport w) ∩
        (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' tsupport ψ) ⊆ V ∧ EqOn χ 1 V := by
  let K := (((distributionSupport u ×ˢ distributionSupport v) ×ˢ distributionSupport w) ∩
    (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' tsupport ψ)
  have hK : IsCompact K := htriple _ ψ.hasCompactSupport
  obtain ⟨W, hW, hKW, _, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
  obtain ⟨f, hf0, hf1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, (Domain d × Domain d) × Domain d)) hW.isClosed_compl hK.isClosed
    (Set.disjoint_left.mpr fun x hx hxK => hx (hKW hxK))
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (f : (Domain d × Domain d) × Domain d → ℝ) :=
    contMDiff_iff_contDiff.mp f.contMDiff
  have hfs : tsupport (f : (Domain d × Domain d) × Domain d → ℝ) ⊆ closure W := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hf0.self_of_nhdsSet x hn)
  let χ : TripleTests ℝ d := ⟨f, hfc,
    hWc.of_isClosed_subset isClosed_closure hfs, subset_univ _⟩
  obtain ⟨V, hV, hKV, hVf⟩ := eventually_nhdsSet_iff_exists.mp hf1
  exact ⟨χ, V, hV, hKV, hVf⟩


/-- The visible proper slice admits separate cutoffs in its two coordinates. -/
theorem separable_addition_cutoff (S T K : Set (Domain d))
    (hproper : AdditionProper S T) (hK : IsCompact K) :
    ∃ (θ η : Tests ℝ (⊤ : Opens (Domain d))) (V W : Set (Domain d)),
      IsOpen V ∧ IsOpen W ∧ additionSlice S T K ⊆ V ×ˢ W ∧
      EqOn θ 1 V ∧ EqOn η 1 W := by
  have hc := hproper K hK
  obtain ⟨θ, V, hV, hKV, hθ⟩ := ExpandedFA.Distributions.cutoff_existence d ⊤
    (Prod.fst '' additionSlice S T K) (hc.image continuous_fst) (subset_univ _)
  obtain ⟨η, W, hW, hKW, hη⟩ := ExpandedFA.Distributions.cutoff_existence d ⊤
    (Prod.snd '' additionSlice S T K) (hc.image continuous_snd) (subset_univ _)
  exact ⟨θ, η, V, W, hV, hW, fun p hp =>
    ⟨hKV ⟨p, hp, rfl⟩, hKW ⟨p, hp, rfl⟩⟩, hθ, hη⟩

theorem left_grouped_cutoff_one
    (S T U K : Set (Domain d))
    (χ : ProductTests ℝ d) (θ η : Tests ℝ (⊤ : Opens (Domain d)))
    (Vin Vout : Set (Domain d × Domain d))
    (hVin : IsOpen Vin) (hVout : IsOpen Vout)
    (hin : additionSlice S T (tsupport θ) ⊆ Vin) (hχ : EqOn χ 1 Vin)
    (hout : additionSlice (S + T) U K ⊆ Vout)
    (hθη : EqOn (tensorTest θ η) 1 Vout) :
    ∃ V : Set ((Domain d × Domain d) × Domain d), IsOpen V ∧
      (((S ×ˢ T) ×ˢ U) ∩ (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' K) ⊆ V ∧
      EqOn (fun p => χ p.1 * θ (p.1.1 + p.1.2) * η p.2) 1 V := by
  let g : (Domain d × Domain d) × Domain d → Domain d × Domain d :=
    fun p => (p.1.1 + p.1.2, p.2)
  let V := g ⁻¹' Vout ∩ Prod.fst ⁻¹' Vin
  have hg : Continuous g := (continuous_fst.fst.add continuous_fst.snd).prodMk continuous_snd
  refine ⟨V, (hVout.preimage hg).inter (hVin.preimage continuous_fst), ?_, ?_⟩
  · intro p hp
    have ho : g p ∈ Vout := hout
      ⟨⟨⟨p.1.1, hp.1.1.1, p.1.2, hp.1.1.2, rfl⟩, hp.1.2⟩, hp.2⟩
    have hθ : θ (p.1.1 + p.1.2) ≠ 0 := by
      intro hz
      have heq := hθη ho
      change θ (p.1.1 + p.1.2) * η p.2 = 1 at heq
      rw [hz, zero_mul] at heq
      exact zero_ne_one heq
    exact ⟨ho, hin ⟨hp.1.1, subset_tsupport θ hθ⟩⟩
  · intro p hp
    change χ p.1 * θ (p.1.1 + p.1.2) * η p.2 = 1
    rw [hχ hp.2]
    change 1 * _ * _ = 1
    rw [one_mul]
    exact hθη hp.1

theorem right_grouped_cutoff_one
    (S T U K : Set (Domain d))
    (χ : ProductTests ℝ d) (θ η : Tests ℝ (⊤ : Opens (Domain d)))
    (Vin Vout : Set (Domain d × Domain d))
    (hVin : IsOpen Vin) (hVout : IsOpen Vout)
    (hin : additionSlice T U (tsupport η) ⊆ Vin) (hχ : EqOn χ 1 Vin)
    (hout : additionSlice S (T + U) K ⊆ Vout)
    (hθη : EqOn (tensorTest θ η) 1 Vout) :
    ∃ V : Set ((Domain d × Domain d) × Domain d), IsOpen V ∧
      (((S ×ˢ T) ×ˢ U) ∩ (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' K) ⊆ V ∧
      EqOn (fun p => θ p.1.1 * (χ (p.1.2, p.2) * η (p.1.2 + p.2))) 1 V := by
  let g : (Domain d × Domain d) × Domain d → Domain d × Domain d :=
    fun p => (p.1.1, p.1.2 + p.2)
  let q : (Domain d × Domain d) × Domain d → Domain d × Domain d :=
    fun p => (p.1.2, p.2)
  let V := g ⁻¹' Vout ∩ q ⁻¹' Vin
  have hg : Continuous g := continuous_fst.fst.prodMk (continuous_fst.snd.add continuous_snd)
  have hq : Continuous q := continuous_fst.snd.prodMk continuous_snd
  refine ⟨V, (hVout.preimage hg).inter (hVin.preimage hq), ?_, ?_⟩
  · intro p hp
    have ho : g p ∈ Vout := hout
      ⟨⟨hp.1.1.1, ⟨p.1.2, hp.1.1.2, p.2, hp.1.2, rfl⟩⟩,
        by simpa only [Set.mem_preimage, add_assoc] using hp.2⟩
    have hη : η (p.1.2 + p.2) ≠ 0 := by
      intro hz
      have heq := hθη ho
      change θ p.1.1 * η (p.1.2 + p.2) = 1 at heq
      rw [hz, mul_zero] at heq
      exact zero_ne_one heq
    exact ⟨ho, hin ⟨⟨hp.1.1.2, hp.1.2⟩, subset_tsupport η hη⟩⟩
  · intro p hp
    change θ p.1.1 * (χ (p.1.2, p.2) * η (p.1.2 + p.2)) = 1
    rw [hχ hp.2]
    change _ * (1 * _) = 1
    rw [one_mul]
    exact hθη hp.1


def tripleSplit (d : ℕ) : (Domain (d+d) × Domain d) ≃L[ℝ]
    ((Domain d × Domain d) × Domain d) :=
  (RectangularTensor.splitDomain d d).prodCongr (ContinuousLinearEquiv.refl ℝ _)

theorem triple_tensor_raw_locality
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (H H' : TripleTests 𝕜 d) (V : Set ((Domain d × Domain d) × Domain d))
    (hV : IsOpen V)
    (hS : (distributionSupport u ×ˢ distributionSupport v) ×ˢ distributionSupport w ⊆ V)
    (hH : EqOn H H' V) :
    RectangularKernel.iteratedTensor (encodedTensor u v) w (pullbackCLM (tripleSplit d) H) =
      RectangularKernel.iteratedTensor (encodedTensor u v) w (pullbackCLM (tripleSplit d) H') := by
  apply RectangularKernel.iteratedTensor_locality _ _ _ _ ((tripleSplit d) ⁻¹' V)
    (hV.preimage (tripleSplit d).continuous)
  · intro p hp
    have hp12 := encodedTensor_support u v hp.1
    exact hS ⟨hp12, hp.2⟩
  · intro p hp
    exact hH hp

/-- Triple cutoffs give identical tests near the full triple support. -/
theorem triple_cutoff_agreement
    (S T U : Set (Domain d)) (ψ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (f g : (Domain d × Domain d) × Domain d → ℝ)
    (V W : Set ((Domain d × Domain d) × Domain d))
    (hV : IsOpen V) (hW : IsOpen W)
    (hSV : (((S ×ˢ T) ×ˢ U) ∩
      (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' tsupport ψ) ⊆ V)
    (hSW : (((S ×ˢ T) ×ˢ U) ∩
      (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' tsupport ψ) ⊆ W)
    (hf : EqOn f 1 V) (hg : EqOn g 1 W) :
    ∃ O : Set ((Domain d × Domain d) × Domain d), IsOpen O ∧
      ((S ×ˢ T) ×ˢ U) ⊆ O ∧
      EqOn (fun p => f p • ψ ((p.1.1 + p.1.2) + p.2))
        (fun p => g p • ψ ((p.1.1 + p.1.2) + p.2)) O := by
  let A : Set ((Domain d × Domain d) × Domain d) :=
    (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' (tsupport ψ)ᶜ
  have hA : IsOpen A := isClosed_closure.isOpen_compl.preimage
    ((continuous_fst.fst.add continuous_fst.snd).add continuous_snd)
  refine ⟨(V ∩ W) ∪ A, (hV.inter hW).union hA, ?_, ?_⟩
  · intro p hp
    by_cases hs : (p.1.1 + p.1.2) + p.2 ∈ tsupport ψ
    · exact Or.inl ⟨hSV ⟨hp, hs⟩, hSW ⟨hp, hs⟩⟩
    · exact Or.inr hs
  · intro p hp
    change f p • ψ ((p.1.1 + p.1.2) + p.2) = g p • ψ ((p.1.1 + p.1.2) + p.2)
    rcases hp with hp | hp
    · rw [hf hp.1, hg hp.2]
    · have hz : ψ ((p.1.1 + p.1.2) + p.2) = 0 := image_eq_zero_of_notMem_tsupport hp
      rw [hz, smul_zero, smul_zero]

end AssociativityGeometry

section LeftNestedCutoff
set_option maxHeartbeats 1600000
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

def leftGroupedMap (d : ℕ) : Domain (d+d) × Domain d →L[ℝ] Domain d × Domain d :=
  let xy : Domain (d+d) × Domain d →L[ℝ] Domain d × Domain d :=
    (RectangularTensor.splitDomain d d).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ (Domain (d+d)) (Domain d))
  (((ContinuousLinearMap.fst ℝ (Domain d) (Domain d)) +
    (ContinuousLinearMap.snd ℝ (Domain d) (Domain d))).comp xy).prod
      (ContinuousLinearMap.snd ℝ (Domain (d+d)) (Domain d))

@[simp] theorem leftGroupedMap_apply (z : Domain (d+d) × Domain d) :
    leftGroupedMap d z =
      ((RectangularTensor.splitDomain d d z.1).1 + (RectangularTensor.splitDomain d d z.1).2, z.2) := rfl

def leftGroupedCutoff (θ η : Tests ℝ (⊤ : Opens (Domain d)))
    (χ : ProductTests ℝ d) : RectangularKernel.KernelTests ℝ (d+d) d :=
  RectangularKernel.tensorTest (pullbackCLM (RectangularTensor.splitDomain d d)
    (cutoffAdditionTest χ θ)) η

private def localMul (θ : Tests ℝ (⊤ : Opens (Domain d))) :
    Tests 𝕜 (⊤ : Opens (Domain d)) →L[𝕜] Tests 𝕜 (⊤ : Opens (Domain d)) :=
  LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ _) θ

@[simp] private theorem localMul_apply (θ : Tests ℝ (⊤ : Opens (Domain d)))
    (A : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) : localMul θ A x = θ x • A x := rfl

private theorem localMul_tsupport (θ : Tests ℝ (⊤ : Opens (Domain d)))
    (A : Tests 𝕜 (⊤ : Opens (Domain d))) : tsupport (localMul θ A) ⊆ tsupport θ :=
  tsupport_smul_subset_left θ A

private theorem leftGroupedPullback_tensor (θ η : Tests ℝ (⊤ : Opens (Domain d)))
    (χ : ProductTests ℝ d) (A B : Tests 𝕜 (⊤ : Opens (Domain d))) :
    LocalizedPullback.cutoffCLM (leftGroupedMap d) (leftGroupedCutoff θ η χ) (tensorTest A B) =
      RectangularKernel.tensorTest
        (pullbackCLM (RectangularTensor.splitDomain d d) (cutoffAdditionTest χ (localMul θ A)))
        (localMul η B) := by
  ext z
  change ((χ ((RectangularTensor.splitDomain d d) z.1) *
      θ (((RectangularTensor.splitDomain d d) z.1).1 + ((RectangularTensor.splitDomain d d) z.1).2)) * η z.2) •
      (A (((RectangularTensor.splitDomain d d) z.1).1 + ((RectangularTensor.splitDomain d d) z.1).2) * B z.2) =
    (χ ((RectangularTensor.splitDomain d d) z.1) •
      (θ (((RectangularTensor.splitDomain d d) z.1).1 + ((RectangularTensor.splitDomain d d) z.1).2) •
        A (((RectangularTensor.splitDomain d d) z.1).1 + ((RectangularTensor.splitDomain d d) z.1).2))) *
      (η z.2 • B z.2)
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul, map_mul]
  ring

private theorem outerLocalized_tensor (θ η : Tests ℝ (⊤ : Opens (Domain d)))
    (A B : Tests 𝕜 (⊤ : Opens (Domain d))) :
    LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ (Domain d × Domain d))
      (tensorTest θ η) (tensorTest A B) = tensorTest (localMul θ A) (localMul η B) := by
  ext z
  change (θ z.1 * η z.2) • (A z.1 * B z.2) = (θ z.1 • A z.1) * (η z.2 • B z.2)
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul, map_mul]
  ring

/-- A fixed inner cutoff can be moved through the outer tensor functional,
provided it is valid on the support of the separating outer factor. -/
theorem left_nested_cutoff_identity_of_encoding
    (u v w a : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ha : IsProperConvolution u v a)
    (U : ScalarDistribution 𝕜 (⊤ : Opens (Domain (d+d))))
    (hU : ∀ H : ProductTests 𝕜 d,
      U (pullbackCLM (RectangularTensor.splitDomain d d) H) = iteratedTensor u v H)
    (θ η : Tests ℝ (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : ∃ V : Set (Domain d × Domain d), IsOpen V ∧
      additionSlice (distributionSupport u) (distributionSupport v) (tsupport θ) ⊆ V ∧ EqOn χ 1 V) :
    (RectangularKernel.iteratedTensor U w).comp
      (LocalizedPullback.cutoffCLM (leftGroupedMap d) (leftGroupedCutoff θ η χ)) =
    (iteratedTensor a w).comp
      (LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ (Domain d × Domain d))
        (tensorTest θ η)) := by
  apply tensor_functional_ext
  intro A B
  change RectangularKernel.iteratedTensor U w
      (LocalizedPullback.cutoffCLM (leftGroupedMap d) (leftGroupedCutoff θ η χ) (tensorTest A B)) =
    iteratedTensor a w
      (LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ (Domain d × Domain d))
        (tensorTest θ η) (tensorTest A B))
  rw [leftGroupedPullback_tensor, outerLocalized_tensor,
    RectangularKernel.iteratedTensor_isTensorProduct U w, iteratedTensor_isTensorProduct a w, hU]
  have hχA : AdmissibleConvolutionCutoff u v (localMul θ A) χ := by
    obtain ⟨V, hV, hSV, hχV⟩ := hχ
    refine ⟨V, hV, ?_, hχV⟩
    intro z hz
    exact hSV ⟨hz.1, localMul_tsupport θ A hz.2⟩
  rw [← ha.2.2 (iteratedTensor u v) (iteratedTensor_isTensorProduct u v) (localMul θ A) χ hχA]


theorem left_nested_cutoff_identity
    (u v w a : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ha : IsProperConvolution u v a)
    (θ η : Tests ℝ (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : ∃ V : Set (Domain d × Domain d), IsOpen V ∧
      additionSlice (distributionSupport u) (distributionSupport v) (tsupport θ) ⊆ V ∧ EqOn χ 1 V) :
    (RectangularKernel.iteratedTensor (encodedTensor u v) w).comp
      (LocalizedPullback.cutoffCLM (leftGroupedMap d) (leftGroupedCutoff θ η χ)) =
    (iteratedTensor a w).comp
      (LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ (Domain d × Domain d))
        (tensorTest θ η)) := by
  apply left_nested_cutoff_identity_of_encoding u v w a ha (encodedTensor u v)
  intro H
  change iteratedTensor u v (pullbackCLM (RectangularTensor.splitDomain d d).symm
    (pullbackCLM (RectangularTensor.splitDomain d d) H)) = _
  rw [pullbackCLM_apply_symm]
  exact hχ


/-- Localized pullback absorbs a second cutoff which equals one wherever
its first cutoff is nonzero. -/
theorem localizedPullback_absorb
    {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) (J : F →L[ℝ] G)
    (χ : TestFunction (⊤ : Opens E) ℝ ⊤)
    (κ : TestFunction (⊤ : Opens F) ℝ ⊤)
    (h : ∀ x, χ x ≠ 0 → κ (L x) = 1)
    (ψ : TestFunction (⊤ : Opens G) 𝕜 ⊤) :
    LocalizedPullback.cutoffCLM L χ (LocalizedPullback.cutoffCLM J κ ψ) =
      LocalizedPullback.cutoffCLM (J.comp L) χ ψ := by
  ext x
  change χ x • (κ (L x) • ψ (J (L x))) = χ x • ψ (J (L x))
  by_cases hx : χ x = 0
  · simp [hx]
  · rw [h x hx, one_smul]

def additionPairCLM (d : ℕ) : (Domain d × Domain d) →L[ℝ] Domain d :=
  ContinuousLinearMap.fst ℝ _ _ + ContinuousLinearMap.snd ℝ _ _

@[simp] theorem additionPairCLM_apply (z : Domain d × Domain d) :
    additionPairCLM d z = z.1 + z.2 := rfl

theorem leftGroupedCutoff_factor (θ η : Tests ℝ (⊤ : Opens (Domain d)))
    (χ : ProductTests ℝ d) (z : Domain (d+d) × Domain d) :
    leftGroupedCutoff θ η χ z = χ (RectangularTensor.splitDomain d d z.1) *
      tensorTest θ η (leftGroupedMap d z) := by
  change (χ (RectangularTensor.splitDomain d d z.1) *
      θ ((RectangularTensor.splitDomain d d z.1).1 + (RectangularTensor.splitDomain d d z.1).2)) * η z.2 =
    χ (RectangularTensor.splitDomain d d z.1) *
      (θ ((RectangularTensor.splitDomain d d z.1).1 + (RectangularTensor.splitDomain d d z.1).2) * η z.2)
  ring

theorem left_nested_cutoff_pairing
    (u v w a : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ha : IsProperConvolution u v a)
    (θ η : Tests ℝ (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : ∃ V : Set (Domain d × Domain d), IsOpen V ∧
      additionSlice (distributionSupport u) (distributionSupport v) (tsupport θ) ⊆ V ∧ EqOn χ 1 V)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    RectangularKernel.iteratedTensor (encodedTensor u v) w
      (LocalizedPullback.cutoffCLM ((additionPairCLM d).comp (leftGroupedMap d))
        (leftGroupedCutoff θ η χ) ψ) =
      iteratedTensor a w (cutoffAdditionTest (tensorTest θ η) ψ) := by
  obtain ⟨κ, V, hV, hKV, hκ⟩ :=
    compact_product_cutoff (tsupport (tensorTest θ η)) (tensorTest θ η).hasCompactSupport
  have hκeq : ∀ z, tensorTest θ η z ≠ 0 → κ z = 1 := by
    intro z hz
    exact hκ (hKV (subset_tsupport _ hz))
  have hκleft : ∀ z, leftGroupedCutoff θ η χ z ≠ 0 → κ (leftGroupedMap d z) = 1 := by
    intro z hz
    apply hκeq
    intro hzero
    apply hz
    rw [leftGroupedCutoff_factor, hzero, mul_zero]
  have h := congrArg (fun T : ProductTests 𝕜 d →L[𝕜] 𝕜 =>
    T (LocalizedPullback.cutoffCLM (additionPairCLM d) κ ψ))
      (left_nested_cutoff_identity u v w a ha θ η χ hχ)
  change RectangularKernel.iteratedTensor (encodedTensor u v) w
    (LocalizedPullback.cutoffCLM (leftGroupedMap d) (leftGroupedCutoff θ η χ)
      (LocalizedPullback.cutoffCLM (additionPairCLM d) κ ψ)) =
    iteratedTensor a w (LocalizedPullback.cutoffCLM
      (ContinuousLinearMap.id ℝ (Domain d × Domain d)) (tensorTest θ η)
        (LocalizedPullback.cutoffCLM (additionPairCLM d) κ ψ)) at h
  rw [localizedPullback_absorb _ _ _ _ hκleft,
    localizedPullback_absorb _ _ _ _ (fun z hz => hκeq z hz)] at h
  exact h

end LeftNestedCutoff

section RightNestedCutoff
set_option maxHeartbeats 1600000
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

def rightGroupedMap (d : ℕ) : Domain d × Domain (d+d) →L[ℝ] Domain d × Domain d :=
  (ContinuousLinearMap.fst ℝ (Domain d) (Domain (d+d))).prod
    ((((ContinuousLinearMap.fst ℝ (Domain d) (Domain d)) +
      (ContinuousLinearMap.snd ℝ (Domain d) (Domain d))).comp
        (RectangularTensor.splitDomain d d).toContinuousLinearMap).comp
          (ContinuousLinearMap.snd ℝ (Domain d) (Domain (d+d))))

@[simp] theorem rightGroupedMap_apply (z : Domain d × Domain (d+d)) :
    rightGroupedMap d z =
      (z.1, (RectangularTensor.splitDomain d d z.2).1 + (RectangularTensor.splitDomain d d z.2).2) := rfl

def rightGroupedCutoff (θ η : Tests ℝ (⊤ : Opens (Domain d)))
    (χ : ProductTests ℝ d) : RectangularKernel.KernelTests ℝ d (d+d) :=
  RectangularKernel.tensorTest θ (pullbackCLM (RectangularTensor.splitDomain d d)
    (cutoffAdditionTest χ η))

private def rightLocalMul (θ : Tests ℝ (⊤ : Opens (Domain d))) :
    Tests 𝕜 (⊤ : Opens (Domain d)) →L[𝕜] Tests 𝕜 (⊤ : Opens (Domain d)) :=
  LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ _) θ

@[simp] private theorem rightLocalMul_apply (θ : Tests ℝ (⊤ : Opens (Domain d)))
    (A : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) : rightLocalMul θ A x = θ x • A x := rfl

private theorem rightLocalMul_tsupport (θ : Tests ℝ (⊤ : Opens (Domain d)))
    (A : Tests 𝕜 (⊤ : Opens (Domain d))) : tsupport (rightLocalMul θ A) ⊆ tsupport θ :=
  tsupport_smul_subset_left θ A

private theorem rightGroupedPullback_tensor (θ η : Tests ℝ (⊤ : Opens (Domain d)))
    (χ : ProductTests ℝ d) (A B : Tests 𝕜 (⊤ : Opens (Domain d))) :
    LocalizedPullback.cutoffCLM (rightGroupedMap d) (rightGroupedCutoff θ η χ) (tensorTest A B) =
      RectangularKernel.tensorTest (rightLocalMul θ A)
        (pullbackCLM (RectangularTensor.splitDomain d d) (cutoffAdditionTest χ (rightLocalMul η B))) := by
  ext z
  change (θ z.1 * (χ (RectangularTensor.splitDomain d d z.2) *
      η ((RectangularTensor.splitDomain d d z.2).1 + (RectangularTensor.splitDomain d d z.2).2))) •
      (A z.1 * B ((RectangularTensor.splitDomain d d z.2).1 + (RectangularTensor.splitDomain d d z.2).2)) =
    (θ z.1 • A z.1) * (χ (RectangularTensor.splitDomain d d z.2) •
      (η ((RectangularTensor.splitDomain d d z.2).1 + (RectangularTensor.splitDomain d d z.2).2) •
        B ((RectangularTensor.splitDomain d d z.2).1 + (RectangularTensor.splitDomain d d z.2).2)))
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul, map_mul]
  ring

private theorem rightOuterLocalized_tensor (θ η : Tests ℝ (⊤ : Opens (Domain d)))
    (A B : Tests 𝕜 (⊤ : Opens (Domain d))) :
    LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ (Domain d × Domain d))
      (tensorTest θ η) (tensorTest A B) = tensorTest (rightLocalMul θ A) (rightLocalMul η B) := by
  ext z
  change (θ z.1 * η z.2) • (A z.1 * B z.2) =
    (θ z.1 • A z.1) * (η z.2 • B z.2)
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul, map_mul]
  ring

theorem right_nested_cutoff_identity_of_encoding
    (u v w b : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (hb : IsProperConvolution v w b)
    (W : ScalarDistribution 𝕜 (⊤ : Opens (Domain (d+d))))
    (hW : ∀ H : ProductTests 𝕜 d,
      W (pullbackCLM (RectangularTensor.splitDomain d d) H) = iteratedTensor v w H)
    (θ η : Tests ℝ (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : ∃ V : Set (Domain d × Domain d), IsOpen V ∧
      additionSlice (distributionSupport v) (distributionSupport w) (tsupport η) ⊆ V ∧ EqOn χ 1 V) :
    (RectangularKernel.iteratedTensor u W).comp
      (LocalizedPullback.cutoffCLM (rightGroupedMap d) (rightGroupedCutoff θ η χ)) =
    (iteratedTensor u b).comp
      (LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ (Domain d × Domain d))
        (tensorTest θ η)) := by
  apply tensor_functional_ext
  intro A B
  change RectangularKernel.iteratedTensor u W
      (LocalizedPullback.cutoffCLM (rightGroupedMap d) (rightGroupedCutoff θ η χ) (tensorTest A B)) =
    iteratedTensor u b
      (LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ (Domain d × Domain d))
        (tensorTest θ η) (tensorTest A B))
  rw [rightGroupedPullback_tensor, rightOuterLocalized_tensor,
    RectangularKernel.iteratedTensor_isTensorProduct u W, iteratedTensor_isTensorProduct u b, hW]
  have hχB : AdmissibleConvolutionCutoff v w (rightLocalMul η B) χ := by
    obtain ⟨V, hV, hSV, hχV⟩ := hχ
    refine ⟨V, hV, ?_, hχV⟩
    intro z hz
    exact hSV ⟨hz.1, rightLocalMul_tsupport η B hz.2⟩
  rw [← hb.2.2 (iteratedTensor v w) (iteratedTensor_isTensorProduct v w) (rightLocalMul η B) χ hχB]


theorem right_nested_cutoff_identity
    (u v w b : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (hb : IsProperConvolution v w b)
    (θ η : Tests ℝ (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : ∃ V : Set (Domain d × Domain d), IsOpen V ∧
      additionSlice (distributionSupport v) (distributionSupport w) (tsupport η) ⊆ V ∧ EqOn χ 1 V) :
    (RectangularKernel.iteratedTensor u (encodedTensor v w)).comp
      (LocalizedPullback.cutoffCLM (rightGroupedMap d) (rightGroupedCutoff θ η χ)) =
    (iteratedTensor u b).comp
      (LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ (Domain d × Domain d))
        (tensorTest θ η)) := by
  apply right_nested_cutoff_identity_of_encoding u v w b hb (encodedTensor v w)
  intro H
  change iteratedTensor v w (pullbackCLM (RectangularTensor.splitDomain d d).symm
    (pullbackCLM (RectangularTensor.splitDomain d d) H)) = _
  rw [pullbackCLM_apply_symm]
  exact hχ

theorem right_nested_cutoff_pairing
    (u v w b : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (hb : IsProperConvolution v w b)
    (θ η : Tests ℝ (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d)
    (hχ : ∃ V : Set (Domain d × Domain d), IsOpen V ∧
      additionSlice (distributionSupport v) (distributionSupport w) (tsupport η) ⊆ V ∧ EqOn χ 1 V)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    RectangularKernel.iteratedTensor u (encodedTensor v w)
      (LocalizedPullback.cutoffCLM
        (((ContinuousLinearMap.fst ℝ (Domain d) (Domain d)) +
          (ContinuousLinearMap.snd ℝ (Domain d) (Domain d))).comp (rightGroupedMap d))
        (rightGroupedCutoff θ η χ) ψ) =
      iteratedTensor u b (cutoffAdditionTest (tensorTest θ η) ψ) := by
  let outer : ProductTests ℝ d := tensorTest θ η
  obtain ⟨κ, O, hO, hKO, hκO⟩ := compact_product_cutoff (tsupport outer) outer.hasCompactSupport
  let H : ProductTests 𝕜 d := cutoffAdditionTest κ ψ
  have hOuter : LocalizedPullback.cutoffCLM (ContinuousLinearMap.id ℝ (Domain d × Domain d)) outer H =
      cutoffAdditionTest outer ψ := by
    ext p
    change outer p • (κ p • ψ (p.1+p.2)) = outer p • ψ (p.1+p.2)
    by_cases hp : outer p = 0
    · simp [hp]
    · have hk : κ p = 1 := hκO (hKO (subset_tsupport outer hp))
      rw [hk, one_smul]
  have hRight : LocalizedPullback.cutoffCLM (rightGroupedMap d) (rightGroupedCutoff θ η χ) H =
      LocalizedPullback.cutoffCLM
        (((ContinuousLinearMap.fst ℝ (Domain d) (Domain d)) +
          (ContinuousLinearMap.snd ℝ (Domain d) (Domain d))).comp (rightGroupedMap d))
        (rightGroupedCutoff θ η χ) ψ := by
    ext z
    change rightGroupedCutoff θ η χ z •
        (κ (rightGroupedMap d z) • ψ ((rightGroupedMap d z).1 + (rightGroupedMap d z).2)) =
      rightGroupedCutoff θ η χ z • ψ ((rightGroupedMap d z).1 + (rightGroupedMap d z).2)
    by_cases hz : rightGroupedCutoff θ η χ z = 0
    · simp [hz]
    · have ho : outer (rightGroupedMap d z) ≠ 0 := by
        change θ z.1 * η ((RectangularTensor.splitDomain d d z.2).1 +
          (RectangularTensor.splitDomain d d z.2).2) ≠ 0
        change θ z.1 * (χ (RectangularTensor.splitDomain d d z.2) *
          η ((RectangularTensor.splitDomain d d z.2).1 + (RectangularTensor.splitDomain d d z.2).2)) ≠ 0 at hz
        exact mul_ne_zero (mul_ne_zero_iff.mp hz).1
          (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).2).2
      have hk : κ (rightGroupedMap d z) = 1 := hκO (hKO (subset_tsupport outer ho))
      rw [hk, one_smul]
  have he := congrArg (fun L : ProductTests 𝕜 d →L[𝕜] 𝕜 => L H)
    (right_nested_cutoff_identity u v w b hb θ η χ hχ)
  change RectangularKernel.iteratedTensor u (encodedTensor v w)
      (LocalizedPullback.cutoffCLM (rightGroupedMap d) (rightGroupedCutoff θ η χ) H) =
    iteratedTensor u b (LocalizedPullback.cutoffCLM
      (ContinuousLinearMap.id ℝ (Domain d × Domain d)) outer H) at he
  rw [hRight, hOuter] at he
  exact he

end RightNestedCutoff

section Associativity
set_option maxHeartbeats 1600000
open Specs.ExpandedFA.Distributions.ProperSupportConvolution
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

theorem convolution_associativity : convolutionAssociativityType := by
  intro 𝕜 _ d u v w a b ht ha hb
  obtain ⟨hl, hr⟩ := associativity_outer_convolvable u v w a b ht ha hb
  obtain ⟨z, hz, hzu⟩ := convolution_existence 𝕜 d a w hl
  obtain ⟨z', hz', hz'u⟩ := convolution_existence 𝕜 d u b hr
  have heq : z = z' := by
    ext ψ
    let S := distributionSupport u
    let T := distributionSupport v
    let U := distributionSupport w
    have hgl : AdditionProper (S + T) U := triple_grouped d S T U ht
    have hgr : AdditionProper S (T + U) :=
      (properness_symmetry d _ _).mp (triple_grouped d T U S (triple_rotation d S T U ht))
    obtain ⟨θl, ηl, Vl, Wl, hVl, hWl, hSl, hθl, hηl⟩ :=
      separable_addition_cutoff (S + T) U (tsupport ψ) hgl ψ.hasCompactSupport
    obtain ⟨θr, ηr, Vr, Wr, hVr, hWr, hSr, hθr, hηr⟩ :=
      separable_addition_cutoff S (T + U) (tsupport ψ) hgr ψ.hasCompactSupport
    have hθlηl : EqOn (tensorTest θl ηl) 1 (Vl ×ˢ Wl) := by
      intro p hp
      change θl p.1 * ηl p.2 = 1
      have h1 : θl p.1 = 1 := hθl hp.1
      have h2 : ηl p.2 = 1 := hηl hp.2
      rw [h1, h2, one_mul]
    have hθrηr : EqOn (tensorTest θr ηr) 1 (Vr ×ˢ Wr) := by
      intro p hp
      change θr p.1 * ηr p.2 = 1
      have h1 : θr p.1 = 1 := hθr hp.1
      have h2 : ηr p.2 = 1 := hηr hp.2
      rw [h1, h2, one_mul]
    obtain ⟨χl, Vli, hVli, hSli, hχl⟩ := compact_product_cutoff _ (ha.1 _ θl.hasCompactSupport)
    obtain ⟨χr, Vri, hVri, hSri, hχr⟩ := compact_product_cutoff _ (hb.1 _ ηr.hasCompactSupport)
    have hil : ∃ V : Set (Domain d × Domain d), IsOpen V ∧
        additionSlice S T (tsupport θl) ⊆ V ∧ EqOn χl 1 V :=
      ⟨Vli, hVli, hSli, hχl⟩
    have hir : ∃ V : Set (Domain d × Domain d), IsOpen V ∧
        additionSlice T U (tsupport ηr) ⊆ V ∧ EqOn χr 1 V :=
      ⟨Vri, hVri, hSri, hχr⟩
    have hal : AdmissibleConvolutionCutoff a w ψ (tensorTest θl ηl) := by
      refine ⟨Vl ×ˢ Wl, hVl.prod hWl, ?_, hθlηl⟩
      intro p hp
      exact hSl ⟨⟨convolution_support 𝕜 d u v a ha hp.1.1, hp.1.2⟩, hp.2⟩
    have har : AdmissibleConvolutionCutoff u b ψ (tensorTest θr ηr) := by
      refine ⟨Vr ×ˢ Wr, hVr.prod hWr, ?_, hθrηr⟩
      intro p hp
      exact hSr ⟨⟨hp.1.1, convolution_support 𝕜 d v w b hb hp.1.2⟩, hp.2⟩
    obtain ⟨Ol, hOl, hKl, hfl⟩ := left_grouped_cutoff_one S T U (tsupport ψ)
      χl θl ηl Vli (Vl ×ˢ Wl) hVli (hVl.prod hWl) hSli hχl hSl hθlηl
    obtain ⟨Or, hOr, hKr, hfr⟩ := right_grouped_cutoff_one S T U (tsupport ψ)
      χr θr ηr Vri (Vr ×ˢ Wr) hVri (hVr.prod hWr) hSri hχr hSr hθrηr
    obtain ⟨O, hO, hSO, htest⟩ := triple_cutoff_agreement S T U ψ
      (fun p => χl p.1 * θl (p.1.1 + p.1.2) * ηl p.2)
      (fun p => θr p.1.1 * (χr (p.1.2, p.2) * ηr (p.1.2 + p.2)))
      Ol Or hOl hOr hKl hKr hfl hfr
    let Hl : RectangularKernel.KernelTests 𝕜 (d+d) d :=
      LocalizedPullback.cutoffCLM ((additionPairCLM d).comp (leftGroupedMap d))
        (leftGroupedCutoff θl ηl χl) ψ
    let Hr : RectangularKernel.KernelTests 𝕜 d (d+d) :=
      LocalizedPullback.cutoffCLM
        (((ContinuousLinearMap.fst ℝ (Domain d) (Domain d)) +
          (ContinuousLinearMap.snd ℝ (Domain d) (Domain d))).comp (rightGroupedMap d))
        (rightGroupedCutoff θr ηr χr) ψ
    have hraw : EqOn (pullbackCLM (tripleSplit d).symm Hl)
        (pullbackCLM (tripleSplit d).symm (pullbackCLM (tripleReassoc d) Hr)) O := by
      intro p hp
      have he := htest hp
      simpa [Hl, Hr, tripleSplit, leftGroupedCutoff, rightGroupedCutoff,
        RectangularKernel.tensorTest, cutoffAdditionTest, LocalizedPullback.cutoffTest, additionPairCLM, add_assoc] using he
    have hlocal := triple_tensor_raw_locality u v w
      (pullbackCLM (tripleSplit d).symm Hl)
      (pullbackCLM (tripleSplit d).symm (pullbackCLM (tripleReassoc d) Hr)) O hO hSO hraw
    have hmiddle : RectangularKernel.iteratedTensor (encodedTensor u v) w Hl =
        RectangularKernel.iteratedTensor (encodedTensor u v) w (pullbackCLM (tripleReassoc d) Hr) := by
      simpa using hlocal
    calc
      z ψ = iteratedTensor a w (cutoffAdditionTest (tensorTest θl ηl) ψ) :=
        hz.2.2 _ (iteratedTensor_isTensorProduct a w) ψ _ hal
      _ = RectangularKernel.iteratedTensor (encodedTensor u v) w Hl :=
        (left_nested_cutoff_pairing u v w a ha θl ηl χl hil ψ).symm
      _ = RectangularKernel.iteratedTensor (encodedTensor u v) w (pullbackCLM (tripleReassoc d) Hr) :=
        hmiddle
      _ = RectangularKernel.iteratedTensor u (encodedTensor v w) Hr := by
        rw [triple_tensor_grouping]
        change RectangularKernel.iteratedTensor u (encodedTensor v w)
          (pullbackCLM (tripleReassoc d).symm (pullbackCLM (tripleReassoc d) Hr)) = _
        rw [pullbackCLM_apply_symm]
      _ = iteratedTensor u b (cutoffAdditionTest (tensorTest θr ηr) ψ) :=
        right_nested_cutoff_pairing u v w b hb θr ηr χr hir ψ
      _ = z' ψ := (hz'.2.2 _ (iteratedTensor_isTensorProduct u b) ψ _ har).symm
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · rw [heq]
    exact hz'
  · intro y hy
    exact convolution_uniqueness 𝕜 d a w y z hy.1 hz


theorem two_compact_associativity : ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
    ((IsCompact (distributionSupport u) ∧ IsCompact (distributionSupport v)) ∨
      (IsCompact (distributionSupport u) ∧ IsCompact (distributionSupport w)) ∨
      (IsCompact (distributionSupport v) ∧ IsCompact (distributionSupport w))) →
    ∃ a b : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)),
      IsProperConvolution u v a ∧ IsProperConvolution v w b ∧
      ∃! z : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)),
        IsProperConvolution a w z ∧ IsProperConvolution u b z := by
  intro 𝕜 _ d u v w hc
  have ht := two_compact_triple d _ _ _
    (support_closed 𝕜 d u) (support_closed 𝕜 d v) (support_closed 𝕜 d w) hc
  have hpair : Convolvable u v ∧ Convolvable v w := by
    rcases hc with ⟨hu, hv⟩ | ⟨hu, hw⟩ | ⟨hv, hw⟩
    · exact ⟨compact_distribution_suffices 𝕜 d u v (Or.inl hu),
        compact_distribution_suffices 𝕜 d v w (Or.inl hv)⟩
    · exact ⟨compact_distribution_suffices 𝕜 d u v (Or.inl hu),
        compact_distribution_suffices 𝕜 d v w (Or.inr hw)⟩
    · exact ⟨compact_distribution_suffices 𝕜 d u v (Or.inr hv),
        compact_distribution_suffices 𝕜 d v w (Or.inr hw)⟩
  obtain ⟨a, ha, _⟩ := convolution_existence 𝕜 d u v hpair.1
  obtain ⟨b, hb, _⟩ := convolution_existence 𝕜 d v w hpair.2
  exact ⟨a, b, ha, hb, convolution_associativity 𝕜 d u v w a b ht ha hb⟩

end Associativity

end ExpandedFA.Distributions.ProperSupportConvolution
