import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.FugledePutnam
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.FugledeIntertwining
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.BorelNormSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.PolarDecomposition

/-!
Fuglede--Putnam and its full bounded Borel and similarity consequences
(`paper.tex`, `fa2:p2:fuglede-putnam`). The adjoint implication is reused
from the rectangular upstream theorem. Stone--Weierstrass gives continuous
intertwining; uniqueness of finite scalar Radon measures on a common compact
spectral set then gives Borel intertwining. The invertible case uses the
upstream polar factor and its square root's commutation property.
-/

noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set Filter Topology
namespace ExpandedFA.SpectralMeasure.FugledePutnam
universe u v

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem adjoint_intertwining : Spec.AdjointIntertwining.{u, v} :=
  FugledeIntertwining.adjoint_intertwining

/-- Restrict the continuous calculus to a common compact spectral set. -/
def restrictedCalculus (N : H →L[ℂ] H)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (s : Set ℂ) [CompactSpace s] (hs : spectrum ℂ N ⊆ s) :
    C(s, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (NormalPVM.continuousIntegral E).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ (Spec.inclusion N s hs))

lemma restrictedCalculus_continuous (N : H →L[ℂ] H)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (s : Set ℂ) [CompactSpace s] (hs : spectrum ℂ N ⊆ s) :
    Continuous (restrictedCalculus N E s hs) :=
  (NormalPVM.continuousIntegral_continuous E).comp
    (ContinuousMap.compRightAlgHom_continuous ℂ ℂ (Spec.inclusion N s hs))

lemma continuous_intertwining (N : H →L[ℂ] H) (M : K →L[ℂ] K) (T : K →L[ℂ] H)
    (hN : IsStarNormal N) (hM : IsStarNormal M) (hT : N.comp T = T.comp M)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (F : ProjectionValuedMeasure (spectrum ℂ M) K)
    (hE : NormalPVM.Spec.Resolves N E) (hF : NormalPVM.Spec.Resolves M F)
    (s : Set ℂ) [CompactSpace s] (hNs : spectrum ℂ N ⊆ s) (hMs : spectrum ℂ M ⊆ s)
    (f : C(s, ℂ)) :
    (restrictedCalculus N E s hNs f).comp T =
      T.comp (restrictedCalculus M F s hMs f) := by
  let π := restrictedCalculus N E s hNs
  let ρ := restrictedCalculus M F s hMs
  have hcN : π ((ContinuousMap.id ℂ).restrict s) = N :=
    NormalPVM.continuousIntegral_coordinate E hE
  have hcM : ρ ((ContinuousMap.id ℂ).restrict s) = M :=
    NormalPVM.continuousIntegral_coordinate F hF
  change (π f).comp T = T.comp (ρ f)
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have hp : π (ContinuousMap.const s r) = r • 1 := π.commutes r
    have hq : ρ (ContinuousMap.const s r) = r • 1 := ρ.commutes r
    rw [hp, hq]
    ext x
    simp
  | id => rwa [hcN, hcM]
  | star_id =>
    rw [map_star, map_star, hcN, hcM]
    exact adjoint_intertwining H K N M T hN.star_comm_self.eq hM.star_comm_self.eq hT
  | add f g hf hg =>
    rw [map_add, map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hf, hg]
  | mul f g hf hg =>
    rw [map_mul, map_mul]
    change (π f).comp ((π g).comp T) = (T.comp (ρ f)).comp (ρ g)
    rw [hg, ← ContinuousLinearMap.comp_assoc, hf]
  | frequently f hf =>
    have hc : IsClosed {g : C(s, ℂ) | (π g).comp T = T.comp (ρ g)} :=
      isClosed_eq
        ((restrictedCalculus_continuous N E s hNs).clm_comp continuous_const)
        (continuous_const.clm_comp (restrictedCalculus_continuous M F s hMs))
    exact hc.mem_of_frequently_of_tendsto hf tendsto_id

lemma inclusion_embedding (N : H →L[ℂ] H) (s : Set ℂ)
    (hs : spectrum ℂ N ⊆ s) :
    MeasurableEmbedding (Spec.inclusion N s hs) := by
  exact ((Spec.inclusion N s hs).continuous.isClosedEmbedding (by
    intro x y h
    exact Subtype.ext (congrArg (fun z : s => (z : ℂ)) h))).measurableEmbedding

lemma mapped_coefficient_radon (N : H →L[ℂ] H)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (s : Set ℂ) [CompactSpace s] (hs : spectrum ℂ N ⊆ s) (x y : H) :
    FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon
      ((E.coefficientMeasure x y).map (Spec.inclusion N s hs)) := by
  exact ⟨measure_lt_top _ _,
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr inferInstance⟩

/-- Scalar uniqueness transfers continuous intertwining to every bounded
Borel function. The two scalar measures are compared on a common compact
subset of the complex plane; no scalar control measure for the Hilbert space
is used. -/
lemma integral_intertwining (N : H →L[ℂ] H) (M : K →L[ℂ] K) (T : K →L[ℂ] H)
    (hN : IsStarNormal N) (hM : IsStarNormal M) (hT : N.comp T = T.comp M)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (F : ProjectionValuedMeasure (spectrum ℂ M) K)
    (hE : NormalPVM.Spec.Resolves N E) (hF : NormalPVM.Spec.Resolves M F)
    (s : Set ℂ) [CompactSpace s] (hNs : spectrum ℂ N ⊆ s) (hMs : spectrum ℂ M ⊆ s)
    (f : s → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    (E.spectralIntegral (f ∘ Spec.inclusion N s hNs)).comp T =
      T.comp (F.spectralIntegral (f ∘ Spec.inclusion M s hMs)) := by
  let i := Spec.inclusion N s hNs
  let j := Spec.inclusion M s hMs
  have hi := inclusion_embedding N s hNs
  have hj := inclusion_embedding M s hMs
  have hboundN : SpectralMeasure.Spec.IsBoundedMeasurable (f ∘ i) :=
    ⟨hf.1.comp hi.measurable, hf.2.imp (fun C hC z => hC (i z))⟩
  have hboundM : SpectralMeasure.Spec.IsBoundedMeasurable (f ∘ j) :=
    ⟨hf.1.comp hj.measurable, hf.2.imp (fun C hC z => hC (j z))⟩
  have hmeas (x : H) (y : K) :
      (E.coefficientMeasure x (T y)).map i =
        (F.coefficientMeasure (T.adjoint x) y).map j := by
    apply FunctionSpaces.ScalarRieszMarkov.scalarIntegral_injective _ _
      (mapped_coefficient_radon N E s hNs x (T y))
      (mapped_coefficient_radon M F s hMs (T.adjoint x) y)
    intro g
    unfold FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral
    rw [hi.integral_map_vectorMeasure, hj.integral_map_vectorMeasure]
    have hgN : SpectralMeasure.Spec.IsBoundedMeasurable (fun z => g (i z)) :=
      NormalPVM.continuous_bounded (g.toContinuousMap.comp i)
    have hgM : SpectralMeasure.Spec.IsBoundedMeasurable (fun z => g (j z)) :=
      NormalPVM.continuous_bounded (g.toContinuousMap.comp j)
    rw [← E.spectralIntegral_coefficient (fun z => g (i z)) hgN x (T y),
      ← F.spectralIntegral_coefficient (fun z => g (j z)) hgM (T.adjoint x) y,
      ContinuousLinearMap.adjoint_inner_left]
    have he := congrArg (fun A : K →L[ℂ] H => ⟪x, A y⟫_ℂ)
      (continuous_intertwining N M T hN hM hT E F hE hF s hNs hMs g.toContinuousMap)
    exact he
  ext y
  apply ext_inner_left ℂ
  intro x
  change ⟪x, E.spectralIntegral (f ∘ i) (T y)⟫_ℂ =
    ⟪x, T (F.spectralIntegral (f ∘ j) y)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left T (F.spectralIntegral (f ∘ j) y) x,
    E.spectralIntegral_coefficient _ hboundN,
    F.spectralIntegral_coefficient _ hboundM]
  calc
    _ = ((E.coefficientMeasure x (T y)).map i).integral f (ContinuousLinearMap.mul ℝ ℂ) :=
      (hi.integral_map_vectorMeasure (μ := E.coefficientMeasure x (T y))
        (B := ContinuousLinearMap.mul ℝ ℂ) (f := f)).symm
    _ = ((F.coefficientMeasure (T.adjoint x) y).map j).integral f
        (ContinuousLinearMap.mul ℝ ℂ) :=
      congrArg (fun μ : ComplexMeasure s => μ.integral f (ContinuousLinearMap.mul ℝ ℂ))
        (hmeas x y)
    _ = _ := hj.integral_map_vectorMeasure

lemma calculus_eq_integral {S : Type*} [MeasurableSpace S]
    (E : ProjectionValuedMeasure S H) (Φ : (S → ℂ) → H →L[ℂ] H)
    (hΦ : BorelNormSpectrum.Spec.BorelCalculus E Φ)
    (f : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    Φ f = E.spectralIntegral f := by
  obtain ⟨μ, hμ, hint⟩ := hΦ.2.2.2.2.2
  have hm (x y : H) : μ x y = E.coefficientMeasure x y := by
    ext B hB
    exact (hμ x y B hB).trans (E.coefficientMeasure_apply x y B hB).symm
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [hint f hf x y, hm, E.spectralIntegral_coefficient f hf x y]

theorem borel_intertwining : Spec.BorelIntertwining.{u, v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT E F hE hF Φ Ψ hΦ hΨ s _ hNs hMs f hf
  have hbN : SpectralMeasure.Spec.IsBoundedMeasurable (f ∘ Spec.inclusion N s hNs) :=
    ⟨hf.1.comp (Spec.inclusion N s hNs).continuous.measurable,
      hf.2.imp (fun C hC z => hC _)⟩
  have hbM : SpectralMeasure.Spec.IsBoundedMeasurable (f ∘ Spec.inclusion M s hMs) :=
    ⟨hf.1.comp (Spec.inclusion M s hMs).continuous.measurable,
      hf.2.imp (fun C hC z => hC _)⟩
  rw [calculus_eq_integral E Φ hΦ _ hbN, calculus_eq_integral F Ψ hΨ _ hbM]
  exact integral_intertwining N M T hN hM hT E F hE hF s hNs hMs f hf

theorem spectral_projections : Spec.SpectralProjections.{u, v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT E F hE hF B hB
  let s := spectrum ℂ N ∪ spectrum ℂ M
  let : CompactSpace s :=
    isCompact_iff_compactSpace.mp ((spectrum.isCompact N).union (spectrum.isCompact M))
  let f : s → ℂ := (Subtype.val ⁻¹' B).indicator (fun _ => 1)
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f :=
    BorelNormSpectrum.bounded_indicator _ (measurable_subtype_coe hB)
      (BorelNormSpectrum.bounded_const 1)
  have hh := integral_intertwining N M T hN hM hT E F hE hF s
    subset_union_left subset_union_right f hf
  have hfN : f ∘ Spec.inclusion N s subset_union_left =
      (Subtype.val ⁻¹' B).indicator (fun _ : spectrum ℂ N => (1 : ℂ)) := by
    funext z
    rfl
  have hfM : f ∘ Spec.inclusion M s subset_union_right =
      (Subtype.val ⁻¹' B).indicator (fun _ : spectrum ℂ M => (1 : ℂ)) := by
    funext z
    rfl
  rw [hfN, hfM, BorelNormSpectrum.integral_indicator_one E _ (measurable_subtype_coe hB),
    BorelNormSpectrum.integral_indicator_one F _ (measurable_subtype_coe hB)] at hh
  exact hh

/-- The positive factor commutes with M, so cancellation on the dense range
of |T| transfers the original intertwining to the polar factor. -/
theorem similarity_unitary : Spec.SimilarityUnitary.{u, v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT
  have hstar := adjoint_intertwining H K N M T.toContinuousLinearMap
    hN.star_comm_self.eq hM.star_comm_self.eq hT
  have hTs : T.toContinuousLinearMap.adjoint.comp N =
      M.comp T.toContinuousLinearMap.adjoint := by
    have hh := congrArg ContinuousLinearMap.adjoint hstar
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using hh
  have hc : Commute M (T.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap) := by
    change M.comp (T.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap) =
      (T.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap).comp M
    ext x
    change M (T.toContinuousLinearMap.adjoint (T x)) = T.toContinuousLinearMap.adjoint (T (M x))
    calc
      _ = T.toContinuousLinearMap.adjoint (N (T x)) :=
        (congrArg (fun A : H →L[ℂ] K => A (T x)) hTs).symm
      _ = _ := congrArg T.toContinuousLinearMap.adjoint
        (congrArg (fun A : K →L[ℂ] H => A x) hT)
  have hmod : Commute M (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap) :=
    PolarDecomposition.positiveSqrt_commutes _ M hc
  obtain ⟨U, hU, _⟩ := PolarDecomposition.polar_decomposition ℂ K H T.toContinuousLinearMap
  obtain ⟨e, he⟩ := PolarDecomposition.invertible_unitary ℂ K H T U hU
  refine ⟨e, he ▸ hU, ?_⟩
  rw [he]
  apply PolarDecomposition.ext_of_comp_modulus_eq T.toContinuousLinearMap
  · ext x
    have hu (y : K) : U (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap y) = T y :=
      congrArg (fun A : K →L[ℂ] H => A y) hU.2.2.2
    have hm (y : K) : M (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap y) =
        PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap (M y) :=
      congrArg (fun A : K →L[ℂ] K => A y) hmod.eq
    change N (U (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap x)) =
      U (M (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap x))
    rw [hu, hm, hu]
    exact congrArg (fun A : K →L[ℂ] H => A x) hT
  · intro x hx
    have hx0 : x = 0 := T.injective (hx.trans (map_zero T).symm)
    simp [hx0]

end ExpandedFA.SpectralMeasure.FugledePutnam
