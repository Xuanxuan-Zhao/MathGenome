import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.NormalPVM
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.ContinuousNormalCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RepresentationPVM

/-!
The existence/uniqueness part of `fa2:p2:normal-spectral` in the current
adopted manuscript.
Existence applies the representation-to-PVM construction to the isometric
continuous calculus of N. For uniqueness, a competing regular PVM defines its
own continuous integral star homomorphism; the coordinate identity identifies
it with that calculus. Uniqueness of regular representing PVMs then applies.
Neither argument uses a nonzero vector, separability, or a scalar control measure.
-/

noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set

namespace ExpandedFA.SpectralMeasure.NormalPVM
universe u v
variable {S : Type u} {H : Type v} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every continuous scalar function is bounded and Borel measurable. -/
theorem continuous_bounded (f : C(S, ℂ)) : SpectralMeasure.Spec.IsBoundedMeasurable f :=
  ⟨f.continuous.measurable, ‖f‖, f.norm_coe_le_norm⟩

/-- The continuous part of the spectral integral of an arbitrary PVM. -/
def continuousIntegral (E : ProjectionValuedMeasure S H) :
    C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun f := E.spectralIntegral f
  map_one' := E.spectralIntegral_one
  map_mul' f g := E.spectralIntegral_mul f g (continuous_bounded f) (continuous_bounded g)
  map_zero' := by
    have h := E.spectralIntegral_smul 0 (fun _ => 1)
      ⟨measurable_const, 1, fun _ => by simp⟩
    simpa using h
  map_add' f g := E.spectralIntegral_add f g (continuous_bounded f) (continuous_bounded g)
  commutes' c := by
    have hc : ((algebraMap ℂ C(S, ℂ) c) : S → ℂ) = c • (fun _ : S => (1 : ℂ)) := by
      ext s
      simp [Algebra.algebraMap_eq_smul_one]
    change E.spectralIntegral ((algebraMap ℂ C(S, ℂ) c) : S → ℂ) = _
    rw [hc, E.spectralIntegral_smul c _ ⟨measurable_const, 1, fun _ => by simp⟩,
      E.spectralIntegral_one, Algebra.algebraMap_eq_smul_one]
  map_star' f := E.spectralIntegral_star f (continuous_bounded f)

theorem continuousIntegral_norm_le (E : ProjectionValuedMeasure S H) (f : C(S, ℂ)) :
    ‖continuousIntegral E f‖ ≤ ‖f‖ :=
  E.spectralIntegral_norm_le f (continuous_bounded f) ‖f‖ (norm_nonneg _) f.norm_coe_le_norm

theorem continuousIntegral_continuous (E : ProjectionValuedMeasure S H) :
    Continuous (continuousIntegral E) := by
  exact ((continuousIntegral E).toLinearMap.mkContinuous 1
    (fun f => by simpa using continuousIntegral_norm_le E f)).continuous

/-- The regular coefficients in any proposed resolution coincide with the
canonical coefficient measures constructed from its PVM axioms. -/
theorem coefficientMeasure_eq {N : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (μ : H → H → ComplexMeasure (spectrum ℂ N))
    (hμ : ∀ x y B, MeasurableSet B → μ x y B = ⟪x, E B y⟫_ℂ) (x y : H) :
    E.coefficientMeasure x y = μ x y := by
  ext B hB
  exact (E.coefficientMeasure_apply x y B hB).trans (hμ x y B hB).symm

/-- The coordinate continuous map is the subtype inclusion as a function. -/
theorem coordinate_coe (K : Set ℂ) :
    (((ContinuousMap.id ℂ).restrict K) : K → ℂ) = (fun z : K => (z : ℂ)) := by
  ext z
  simp

/-- The coordinate integral condition alone fixes the generator of the
continuous integral homomorphism. -/
theorem continuousIntegral_coordinate {N : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ N) H) (hE : Spec.Resolves N E) :
    continuousIntegral E ((ContinuousMap.id ℂ).restrict (spectrum ℂ N)) = N := by
  obtain ⟨μ, _, hμ, hcoord⟩ := hE
  ext y
  apply ext_inner_left ℂ
  intro x
  change ⟪x, E.spectralIntegral ((ContinuousMap.id ℂ).restrict (spectrum ℂ N)) y⟫_ℂ = _
  rw [E.spectralIntegral_coefficient _
    (continuous_bounded ((ContinuousMap.id ℂ).restrict (spectrum ℂ N))),
    coefficientMeasure_eq E μ hμ x y]
  simpa only [coordinate_coe, FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral]
    using (hcoord x y).2.symm

/-- A proposed resolution represents the actual continuous calculus. -/
theorem resolves_represents {N : H →L[ℂ] H} (hN : IsStarNormal N)
    (π : C(spectrum ℂ N, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Continuous π)
    (hπcoord : π ((ContinuousMap.id ℂ).restrict (spectrum ℂ N)) = N)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H) (hE : Spec.Resolves N E) :
    RepresentationPVM.Spec.Represents E π := by
  have heq : continuousIntegral E = π :=
    CStar.ContinuousNormalCalculus.normal_calculus_unique _ N hN
      (continuousIntegral E) π (continuousIntegral_continuous E) hπ
      (continuousIntegral_coordinate E hE) hπcoord
  obtain ⟨μ, hreg, hμ, _⟩ := hE
  refine ⟨μ, hreg, hμ, ?_⟩
  intro x y f
  refine ⟨?_, ?_⟩
  · exact RepresentationBorelExtension.bounded_borel_integrable _ (hreg x y) f
      (continuous_bounded f)
  · rw [← heq]
    change ⟪x, E.spectralIntegral f y⟫_ℂ = _
    rw [E.spectralIntegral_coefficient f (continuous_bounded f),
      coefficientMeasure_eq E μ hμ x y]
    rfl

/-- Construct the resolution from the actual isometric continuous normal
calculus and the representation-to-PVM theorem. -/
theorem normal_spectral_theorem : Spec.NormalSpectralTheorem.{v} := by
  intro H _ _ _ N hN
  obtain ⟨π, hπiso, hπcoord, _, _⟩ :=
    CStar.ContinuousNormalCalculus.normal_calculus (H →L[ℂ] H) N hN
  obtain ⟨μ, hμ⟩ := RepresentationBorelExtension.scalar_measures (spectrum ℂ N) H π
  let E := RepresentationPVM.pvm π μ hμ
  have hE : Spec.Resolves N E := by
    refine ⟨μ, hμ.1, ?_, ?_⟩
    · intro x y B hB
      exact (RepresentationPVM.projection_coefficient π μ hμ B hB x y).symm
    · intro x y
      simpa only [hπcoord, coordinate_coe] using hμ.2.1 x y
        ((ContinuousMap.id ℂ).restrict (spectrum ℂ N))
  refine ⟨E, hE, ?_⟩
  intro F hF B hB
  exact RepresentationPVM.pvm_unique π μ hμ F
    (resolves_represents hN π hπiso.continuous hπcoord F hF) B hB

/-- The theorem includes the empty spectrum of the zero operator algebra. -/
theorem zero_space : Spec.ZeroSpace.{v} := by
  intro H _ _ _ _ N
  have hN : IsStarNormal N := ⟨by apply Subsingleton.elim⟩
  obtain ⟨E, hE, _⟩ := normal_spectral_theorem H N hN
  exact ⟨spectrum.of_subsingleton (R := ℂ) N, E, hE, fun _ _ => Subsingleton.elim _ _⟩

end ExpandedFA.SpectralMeasure.NormalPVM
