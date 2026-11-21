import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealNormalRestrictedResolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.BorelNormSpectrum

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace
open Classical

namespace ExpandedFA.VonNeumann.RealNormalRestrictedResolution
universe u v
open SpectralMeasure

section Restriction
variable {X : Type u} [MeasurableSpace X]
  {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  (E : ProjectionValuedMeasure X G) (S : Submodule ℂ G) [CompleteSpace S]
  (hS : ∀ B, MeasurableSet B → ∀ s : S, E B s ∈ S)

/-- The bounded restriction of a measurable spectral projection. -/
def restrictedProjection (B : Set X) : S →L[ℂ] S :=
  if hB : MeasurableSet B then
    (E B).restrict (fun x hx => hS B hB ⟨x, hx⟩) else 0

omit [CompleteSpace S] in
@[simp] theorem restrictedProjection_coe (B : Set X) (hB : MeasurableSet B) (s : S) :
    (restrictedProjection E S hS B s : G) = E B s := by
  simp [restrictedProjection, hB]

/-- Restriction preserves all PVM axioms, including norm countable additivity. -/
def restrictedPVM : ProjectionValuedMeasure X S where
  toFun := restrictedProjection E S hS
  univ := by
    ext s
    simp [restrictedProjection_coe, E.univ]
  selfAdjoint B hB := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro s t
    change ⟪(restrictedProjection E S hS B s : G), (t : G)⟫_ℂ =
      ⟪(s : G), (restrictedProjection E S hS B t : G)⟫_ℂ
    simp only [restrictedProjection_coe E S hS B hB]
    exact (E.selfAdjoint B hB).isSymmetric s t
  inter B D hB hD := by
    ext s
    change (restrictedProjection E S hS B (restrictedProjection E S hS D s) : G) =
      (restrictedProjection E S hS (B ∩ D) s : G)
    simp only [restrictedProjection_coe E S hS B hB,
      restrictedProjection_coe E S hS D hD,
      restrictedProjection_coe E S hS (B ∩ D) (hB.inter hD)]
    exact congrArg (fun T : G →L[ℂ] G => T s) (E.inter B D hB hD)
  iUnion B hB hd s := by
    apply (S.subtypeₗᵢ.isometry.isEmbedding.isInducing.hasSum_iff
      (g := S.subtypeL) _ _).mp
    change HasSum (fun n => (restrictedProjection E S hS (B n) s : G))
      (restrictedProjection E S hS (⋃ n, B n) s : G)
    simpa only [restrictedProjection_coe E S hS _ (MeasurableSet.iUnion hB),
      restrictedProjection_coe E S hS _ (hB _)] using E.iUnion B hB hd (s : G)

@[simp] theorem restrictedPVM_coe (B : Set X) (hB : MeasurableSet B) (s : S) :
    (restrictedPVM E S hS B s : G) = E B s :=
  restrictedProjection_coe E S hS B hB s

/-- Simple spectral sums agree under the actual subtype inclusion. -/
theorem restrictedPVM_simpleIntegral_coe (f : SimpleFunc X ℂ) (s : S) :
    ((restrictedPVM E S hS).simpleIntegral f s : G) = E.simpleIntegral f s := by
  change ((∑ c ∈ f.range, c • restrictedPVM E S hS (f ⁻¹' {c})) s : G) =
    (∑ c ∈ f.range, c • E (f ⁻¹' {c})) s
  simp only [sum_apply, smul_apply,
    Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro c hc
  rw [restrictedPVM_coe E S hS _ (f.measurableSet_fiber c)]

/-- Passing to operator-norm limits gives the restriction identity for every
bounded Borel symbol, without a cyclicity assumption. -/
theorem restrictedPVM_integral_coe (f : X → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (s : S) :
    ((restrictedPVM E S hS).spectralIntegral f s : G) = E.spectralIntegral f s := by
  obtain ⟨a, ha⟩ := exists_uniform_simple_approx f hf
  have hF := (restrictedPVM E S hS).spectralIntegral_tendsto f hf a ha
  have hE := E.spectralIntegral_tendsto f hf a ha
  have hFs := S.subtypeL.continuous.tendsto
      ((restrictedPVM E S hS).spectralIntegral f s) |>.comp
    ((((ContinuousLinearMap.apply ℂ S) s).continuous.tendsto _).comp hF)
  have hEs := (((ContinuousLinearMap.apply ℂ G) (s : G)).continuous.tendsto _).comp hE
  change Tendsto (fun n => ((restrictedPVM E S hS).simpleIntegral (a n) s : G)) atTop
    (nhds ((restrictedPVM E S hS).spectralIntegral f s : G)) at hFs
  simp_rw [restrictedPVM_simpleIntegral_coe] at hFs
  exact tendsto_nhds_unique hFs hEs

/-- A bounded scalar spectral integral is normal. -/
theorem integral_normal (f : X → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    IsStarNormal (E.spectralIntegral f) := by
  constructor
  change star (E.spectralIntegral f) * E.spectralIntegral f =
    E.spectralIntegral f * star (E.spectralIntegral f)
  rw [← E.spectralIntegral_star f hf,
    ← E.spectralIntegral_mul _ _ hf.star hf,
    ← E.spectralIntegral_mul _ _ hf hf.star]
  congr 1
  exact mul_comm _ _

end Restriction

section RealNormal
open TraceIdeals.RealComplexification
open TraceIdeals.RealComplexification.Spec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := completeSpace
variable {N : H →L[ℝ] H} (C : RealNormalControlMeasure.Spec.AlgebraModel N)
  (S : Submodule ℂ (Space H)) [CompleteSpace S]
  (eS : S) (heS : (eS : Space H) = inclusion C.e)
  (hS : ∀ B, MeasurableSet B → ∀ s : S, C.E B s ∈ S)

include eS heS

/-- The original finite vector measure is preserved by restriction. -/
theorem restricted_vectorMeasure (B : Set (RealNormalControlMeasure.Spec.Spectrum N))
    (hB : MeasurableSet B) :
    C.μ B = ENNReal.ofReal (‖restrictedPVM C.E S hS B eS‖ ^ 2) := by
  rw [C.vectorMeasure B hB]
  congr 2
  rw [← Submodule.norm_coe, restrictedPVM_coe C.E S hS B hB, heS]

/-- Containing the control vector prevents loss of any nonzero spectral
projection, irrespective of spectral multiplicity. -/
theorem restricted_null_iff (B : Set (RealNormalControlMeasure.Spec.Spectrum N))
    (hB : MeasurableSet B) :
    restrictedPVM C.E S hS B = 0 ↔ C.E B = 0 := by
  constructor
  · intro hF
    apply (C.control B hB).mpr
    rw [restricted_vectorMeasure C S eS heS hS B hB, hF]
    simp
  · intro hE
    ext s
    simp only [restrictedPVM_coe C.E S hS B hB, hE,
      zero_apply, ZeroMemClass.coe_zero]

/-- The coordinate integral retains the entire actual complex spectrum. -/
theorem restricted_spectrum :
    spectrum ℂ ((restrictedPVM C.E S hS).spectralIntegral (fun z => (z : ℂ))) =
      RealNormalControlMeasure.Spec.Spectrum N := by
  let f : RealNormalControlMeasure.Spec.Spectrum N → ℂ := fun z => (z : ℂ)
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f :=
    NormalPVM.continuous_bounded ((ContinuousMap.id ℂ).restrict _)
  have hcoord : C.E.spectralIntegral f = operator N :=
    NormalPVM.continuousIntegral_coordinate C.E C.resolves
  rw [BorelNormSpectrum.spectrum_eq_essentialRange _ hf]
  change BorelNormSpectrum.Spec.essentialRange (restrictedPVM C.E S hS) f = _
  change BorelNormSpectrum.Spec.essentialRange (restrictedPVM C.E S hS) f =
    spectrum ℂ (operator N)
  calc
    _ = BorelNormSpectrum.Spec.essentialRange C.E f := by
      ext z
      apply forall_congr'
      intro ε
      apply forall_congr'
      intro hε
      exact not_congr (restricted_null_iff C S eS heS hS _
        (measurableSet_lt (hf.1.sub measurable_const).norm measurable_const))
    _ = spectrum ℂ (operator N) := by
      rw [← hcoord, BorelNormSpectrum.spectrum_eq_essentialRange C.E hf]

end RealNormal

/-- Restrict the actual spectral resolution to any closed invariant subspace
containing the control vector. No cyclic unitary or spectrum identification is
assumed. -/
theorem restricted_resolution : Spec.RestrictedResolution.{u} := by
  intro H _ _ _ N _ C S hclosed
  let : CompleteSpace (TraceIdeals.RealComplexification.Space H) :=
    TraceIdeals.RealComplexification.Spec.completeSpace
  let : CompleteSpace S := hclosed.completeSpace_coe
  intro eS heS hS
  let F := restrictedPVM C.E S hS
  let f : RealNormalControlMeasure.Spec.Spectrum N → ℂ := fun z => (z : ℂ)
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f :=
    NormalPVM.continuous_bounded ((ContinuousMap.id ℂ).restrict _)
  have hcoord : C.E.spectralIntegral f = TraceIdeals.RealComplexification.Spec.operator N :=
    NormalPVM.continuousIntegral_coordinate C.E C.resolves
  refine ⟨F.spectralIntegral f, F, ?_, integral_normal F f hf,
    restricted_spectrum C S eS heS hS, ?_, ?_,
    F.spectralIntegral, BorelNormSpectrum.borel_calculus F, rfl⟩
  · intro s
    exact (restrictedPVM_integral_coe C.E S hS f hf s).trans
      (congrArg (fun T => T (s : TraceIdeals.RealComplexification.Space H)) hcoord)
  · exact restrictedPVM_coe C.E S hS
  · exact restricted_vectorMeasure C S eS heS hS
end ExpandedFA.VonNeumann.RealNormalRestrictedResolution
