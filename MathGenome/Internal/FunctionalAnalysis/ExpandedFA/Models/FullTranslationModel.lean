import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.FullTranslationModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.TranslationWeakDerivative
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.CoordinateMultiplicationModel

/-! Assembly of the full translation representation on arbitrary complex Hilbert
multiplicities. The Fourier transform transports the entire derivative graphs;
composition of the same unitary gives both representation criteria. -/
noncomputable section
open MeasureTheory Filter Topology

namespace ExpandedFA.Models.FullTranslationModel
open Semigroups.Stone Unbounded
universe u v w

section Transport
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A unitary intertwining all times transports both directions of the norm
limit defining the infinitesimal derivative. -/
theorem derivative_iff_of_conjugacy (F : H ≃ₗᵢ[ℂ] K)
    (V : UnitaryGroup H) (W : UnitaryGroup K)
    (hF : ∀ t f, F (V.operators t f) = W.operators t (F f)) (f g : H) :
    HasDerivative V f g ↔ HasDerivative W (F f) (F g) := by
  have he (h : ℝ) : F (differenceQuotient V h f) = differenceQuotient W h (F f) := by
    simp only [differenceQuotient, map_smul, map_sub, hF]
  constructor
  · intro hd
    simpa only [HasDerivative, Function.comp_def, he] using
      (F.continuous.tendsto g).comp hd
  · intro hd
    have he' (h : ℝ) : F.symm (differenceQuotient W h (F f)) = differenceQuotient V h f := by
      rw [← he, F.symm_apply_apply]
    simpa only [HasDerivative, Function.comp_def, he', F.symm_apply_apply] using
      (F.symm.continuous.tendsto (F g)).comp hd

/-- Remove the factor i from both the derivative and the operator value,
without changing the domain. -/
theorem derivative_iff_operator_graph (V : UnitaryGroup H) (A : Operator ℂ H H)
    (hd : DerivativeGraph V A) (f g : H) :
    HasDerivative V f (Complex.I • g) ↔ (f, g) ∈ A.graph := by
  rw [hd]
  constructor
  · intro h
    obtain ⟨hf, he⟩ := (mem_graph_iff (Complex.I • A) _).mp h
    exact (mem_graph_iff A _).mpr ⟨hf, (smul_right_injective H Complex.I_ne_zero) he⟩
  · intro h
    obtain ⟨hf, he⟩ := (mem_graph_iff A _).mp h
    exact (mem_graph_iff (Complex.I • A) _).mpr
      ⟨hf, by change Complex.I • A ⟨f, hf⟩ = Complex.I • g; rw [he]⟩

/-- Conjugacy of the groups identifies the entire operator graphs, including
the necessity and sufficiency of domain membership. -/
theorem operator_graph_iff_of_conjugacy (F : H ≃ₗᵢ[ℂ] K)
    (V : UnitaryGroup H) (W : UnitaryGroup K)
    (A : Operator ℂ H H) (B : Operator ℂ K K)
    (hV : DerivativeGraph V A) (hW : DerivativeGraph W B)
    (hF : ∀ t f, F (V.operators t f) = W.operators t (F f)) (f g : H) :
    (f, g) ∈ A.graph ↔ (F f, F g) ∈ B.graph := by
  rw [← derivative_iff_operator_graph V A hV,
    derivative_iff_of_conjugacy F V W hF, map_smul,
    derivative_iff_operator_graph W B hW]

end Transport

/-- Spatial and coordinate Stone operators, related by the normalized angular
Fourier unitary on every complex Hilbert multiplicity. -/
theorem canonical_models : Spec.CanonicalModels.{u} := by
  intro M _ _ _
  obtain ⟨V, A, hV, hA, hAV, hdA, hgA⟩ := TranslationWeakDerivative.spatial_stone M
  obtain ⟨W, B, hW, hB, hBW, hdB, hgB⟩ := CoordinateMultiplicationModel.coordinate_generator M
  let F : L2 M ≃ₗᵢ[ℂ] L2 M := TranslationFourierModel.angularFourier
  have hF : FourierConjugacy V W F := by
    intro t f
    rw [hV t f]
    change TranslationFourierModel.angularFourier (translate t f) = W.operators t (F f)
    rw [TranslationFourierModel.angularFourier_translation]
    apply Lp.ext
    exact (TranslationFourierModel.modulation_representative t (F f)).trans (hW t (F f)).symm
  exact ⟨V, W, A, B, F, hV, hW, hA, hAV, hdA, hgA, hB, hBW, hdB, hgB,
    TranslationFourierModel.angularFourier_integral, hF,
    operator_graph_iff_of_conjugacy F V W A B hdA hdB hF⟩

section Assembly
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

/-- Compose the witnessing representation with Fourier, in either direction. -/
theorem operator_criterion_of_fourier (F : L2 M ≃ₗᵢ[ℂ] L2 M)
    (hF : ∀ f g, SpatialGraph f g ↔ CoordinateGraph (F f) (F g))
    (A : Operator ℂ H H) : OperatorTranslationModel M A ↔ OperatorLebesgueModel M A := by
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨W.trans F, fun x y => ?_⟩
    exact (hW x y).trans (hF (W x) (W y))
  · rintro ⟨W, hW⟩
    refine ⟨W.trans F.symm, fun x y => ?_⟩
    have hf := hF (F.symm (W x)) (F.symm (W y))
    rw [F.apply_symm_apply, F.apply_symm_apply] at hf
    exact (hW x y).trans hf.symm

/-- All times and all L² vectors are preserved under composition of the
representation with Fourier and its inverse. -/
theorem group_criterion_of_fourier (F : L2 M ≃ₗᵢ[ℂ] L2 M)
    (hF : ∀ t f, (F (translate t f) : ℝ → M) =ᵐ[volume]
      fun r => Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)) • (F f) r)
    (U : UnitaryGroup H) : GroupTranslationModel M U ↔ GroupLebesgueModel M U := by
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨W.trans F, fun t x => ?_⟩
    change (F (W (U.operators t x)) : ℝ → M) =ᵐ[volume] _
    rw [hW t x]
    exact hF t (W x)
  · rintro ⟨W, hW⟩
    refine ⟨W.trans F.symm, fun t x => ?_⟩
    change F.symm (W (U.operators t x)) = translate t (F.symm (W x))
    apply F.injective
    rw [F.apply_symm_apply]
    apply Lp.ext
    exact (hW t x).trans (by simpa only [F.apply_symm_apply] using
      (hF t (F.symm (W x))).symm)

end Assembly

/-- The full graph representation criterion, with no dimension or separability
restriction on the source Hilbert space or its multiplicity. -/
theorem operator_model_iff :
    ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
      (A : Operator ℂ H H), SymmetryAndDeficienciesSpec.selfAdjointValue A →
        (OperatorTranslationModel M A ↔ OperatorLebesgueModel M A) := by
  intro H _ _ _ M _ _ _ A _
  obtain ⟨V, W, A₀, B₀, F, _, _, _, _, _, hgA, _, _, _, hgB, _, _, hF⟩ :=
    canonical_models M
  apply operator_criterion_of_fourier F _ A
  intro f g
  exact (hgA f g).symm.trans ((hF f g).trans (hgB (F f) (F g)))

/-- The full group representation criterion for every strongly continuous
unitary group and every complex Hilbert multiplicity. -/
theorem group_model_iff :
    ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
      (U : UnitaryGroup H), GroupTranslationModel M U ↔ GroupLebesgueModel M U := by
  intro H _ _ _ M _ _ _ U
  apply group_criterion_of_fourier (TranslationFourierModel.angularFourier (M := M)) _ U
  intro t f
  rw [TranslationFourierModel.angularFourier_translation]
  exact TranslationFourierModel.modulation_representative t _

theorem full_translation_model : Spec.FullConclusion.{u, v} :=
  ⟨canonical_models, operator_model_iff, group_model_iff⟩

end ExpandedFA.Models.FullTranslationModel
