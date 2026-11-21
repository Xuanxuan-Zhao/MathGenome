import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.CyclicModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.NormalPVM
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace ExpandedFA.SpectralMeasure.CyclicModel
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous functions are dense for every finite Borel measure on the
compact metric spectrum, including the zero measure and empty spectrum. -/
theorem continuous_density : Spec.ContinuousDensity.{u} := by
  intro H _ _ _ N μ _
  exact ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)

/-- The Hölder operator in the specification is actual pointwise multiplication. -/
theorem multiplier_apply {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (g : C(S, ℂ)) (u : Lp ℂ 2 μ) :
    Spec.multiplier μ g u =ᵐ[μ] fun s => g s * u s := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    (ContinuousMap.toLp ∞ μ ℂ g) u
  filter_upwards [h, ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) μ g] with s hs hg
  simpa only [Spec.multiplier, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hg] using hs

/-- The L² norm is the integral of the pointwise squared norm. -/
lemma l2_norm_sq {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (u : Lp ℂ 2 μ) : ‖u‖ ^ 2 = ∫ s, ‖u s‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner u u)]
  congr 1
  funext s
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (u s)

/-- The continuous functional calculus agrees with any resolving PVM. -/
lemma continuousIntegral_eq_cfcHom (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (hE : NormalPVM.Spec.Resolves N E) :
    NormalPVM.continuousIntegral E = cfcHom hN := by
  exact CStar.ContinuousNormalCalculus.normal_calculus_unique _ N hN
    _ _ (NormalPVM.continuousIntegral_continuous E)
    (isometry_cfcHom N hN).continuous
    (NormalPVM.continuousIntegral_coordinate E hE) (cfcHom_id hN)

/-- The continuous cyclic orbit map. -/
def orbitMap (N : H →L[ℂ] H) (hN : IsStarNormal N) (e : H) :
    C(spectrum ℂ N, ℂ) →ₗ[ℂ] H where
  toFun f := cfcHom hN f e
  map_add' f g := by simp
  map_smul' c f := by simp

/-- Cyclicity is for the original generated C*-algebra. Its equality with the
range of the continuous calculus supplies density of this orbit. -/
lemma orbitMap_dense (N : H →L[ℂ] H) (hN : IsStarNormal N) (e : H)
    (he : Spec.IsCyclic N e) : DenseRange (orbitMap N hN e) := by
  apply he.mono
  rintro _ ⟨a, rfl⟩
  have ha : (a : H →L[ℂ] H) ∈ (cfcHom (R := ℂ) hN).range := by
    rw [range_cfcHom ℂ hN]
    exact a.property
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, congrArg (fun T : H →L[ℂ] H => T e) hf⟩

/-- The PVM norm-square identity is precisely the L² isometry on continuous
functions. No division by the mass of the cyclic vector occurs. -/
lemma orbitMap_norm (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (hE : NormalPVM.Spec.Resolves N E) (e : H) (f : C(spectrum ℂ N, ℂ)) :
    ‖orbitMap N hN e f‖ = ‖ContinuousMap.toLp 2 (E.diagonalMeasure e) ℂ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have heq : cfcHom hN f = E.spectralIntegral f :=
    congrArg (fun π : C(spectrum ℂ N, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) => π f)
      (continuousIntegral_eq_cfcHom N hN E hE).symm
  change ‖cfcHom hN f e‖ ^ 2 = _
  rw [heq, E.spectralIntegral_norm_sq_integral f (NormalPVM.continuous_bounded f),
    l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (E.diagonalMeasure e) f] with s hs
  rw [hs]

/-- Continuous multiplication agrees with the actual pointwise product in L². -/
lemma multiplier_toLp {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (g f : C(S, ℂ)) :
    Spec.multiplier μ g (ContinuousMap.toLp 2 μ ℂ f) =
      ContinuousMap.toLp 2 μ ℂ (g * f) := by
  apply Lp.ext
  filter_upwards [multiplier_apply μ g (ContinuousMap.toLp 2 μ ℂ f),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ f,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (g * f)] with s hs hf hgf
  simp only [hs, hf, hgf, ContinuousMap.mul_apply]

/-- Extend the isometry between the two dense continuous-function images.
Surjectivity follows from cyclicity, rather than being assumed of an embedding. -/
theorem model_of_cyclic (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (hE : NormalPVM.Spec.Resolves N E) (e : H) (he : Spec.IsCyclic N e) :
    Spec.Model N hN (E.diagonalMeasure e) e := by
  let μ := E.diagonalMeasure e
  let j := (ContinuousMap.toLp 2 μ ℂ : C(spectrum ℂ N, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap
  let v := orbitMap N hN e
  have hj : DenseRange j := continuous_density H N μ
  have hv : DenseRange v := orbitMap_dense N hN e he
  have hn : ∀ f, ‖v f‖ = ‖j f‖ := orbitMap_norm N hN E hE e
  let U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H :=
    (LinearEquiv.refl ℂ C(spectrum ℂ N, ℂ)).extendOfIsometry j v hj hv hn
  have hU (f : C(spectrum ℂ N, ℂ)) : U (ContinuousMap.toLp 2 μ ℂ f) = cfcHom hN f e := by
    exact LinearEquiv.extendOfIsometry_eq _ _ _ hj hv hn f
  have hinter (g : C(spectrum ℂ N, ℂ)) (u : Lp ℂ 2 μ) :
      U (Spec.multiplier μ g u) = cfcHom hN g (U u) := by
    apply congrFun (hj.equalizer
      (U.continuous.comp (Spec.multiplier μ g).continuous)
      ((cfcHom hN g).continuous.comp U.continuous) ?_) u
    funext f
    change U (Spec.multiplier μ g (ContinuousMap.toLp 2 μ ℂ f)) =
      cfcHom hN g (U (ContinuousMap.toLp 2 μ ℂ f))
    rw [multiplier_toLp, hU, hU, map_mul]
    rfl
  refine ⟨U, hU, ?_, ?_, hinter⟩
  · simpa using hU 1
  · intro u
    simpa only [Spec.coordinate, cfcHom_id] using hinter (Spec.coordinate N) u

/-- The cyclic spectral model on the finite diagonal measure. This also
applies when e=0 is cyclic, hence when the represented Hilbert space is zero. -/
theorem cyclic_model : Spec.ResolutionModel.{u} := by
  intro H _ _ _ N hN E hE e he
  refine ⟨E.diagonalMeasure e, inferInstance, ?_, E.diagonalMeasure_univ e,
    continuous_density H N (E.diagonalMeasure e), model_of_cyclic N hN E hE e he⟩
  exact E.diagonalMeasure_apply e

/-- Existence of the resolution is supplied by the normal spectral theorem;
the cyclic hypothesis alone makes the constructed L² isometry onto H. -/
theorem exists_cyclic_model : Spec.CyclicModelTheorem.{u} := by
  intro H _ _ _ N hN e he
  obtain ⟨E, hE, _⟩ := NormalPVM.normal_spectral_theorem H N hN
  exact ⟨E, hE, cyclic_model H N hN E hE e he⟩

/-- The canonical diagonal measure of the zero vector is the zero measure. -/
lemma diagonalMeasure_zero {S : Type*} [MeasurableSpace S]
    (E : ProjectionValuedMeasure S H) : E.diagonalMeasure (0 : H) = 0 := by
  ext B hB
  rw [E.diagonalMeasure_apply 0 B hB]
  simp

/-- Explicit zero representation, with no artificial nonzero-mass condition. -/
theorem zero_representation : Spec.ZeroRepresentation.{u} := by
  intro H _ _ _ _ N hN
  obtain ⟨E, hE, _⟩ := NormalPVM.normal_spectral_theorem H N hN
  have he : Spec.IsCyclic N (0 : H) := by
    apply Function.Surjective.denseRange
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  have hmodel : Spec.Model N hN 0 0 := by
    simpa only [diagonalMeasure_zero] using model_of_cyclic N hN E hE 0 he
  refine ⟨E, hE, ?_, hmodel⟩
  intro B hB
  simp

end ExpandedFA.SpectralMeasure.CyclicModel
