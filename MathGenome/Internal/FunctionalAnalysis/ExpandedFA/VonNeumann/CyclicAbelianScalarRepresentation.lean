import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.CyclicAbelianScalarRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.CyclicModel
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace ZeroAtInfty CStarAlgebra

namespace ExpandedFA.VonNeumann.CyclicAbelianScalarRepresentation
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section CompactModel
variable {X : Type v} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : H)

/-- Evaluate the representation at the prescribed cyclic vector. -/
def continuousOrbit : C(X, ℂ) →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H e).comp { π.toAlgHom.toLinearMap with cont := map_continuous π }

/-- The unnormalized vector functional. -/
def vectorFunctional : C(X, ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ e).comp (continuousOrbit π e)

omit [T2Space X] in
lemma vectorFunctional_square (f : C(X, ℂ)) :
    vectorFunctional π e (star f * f) = ((‖π f e‖ ^ 2 : ℝ) : ℂ) := by
  change inner ℂ e (π (star f * f) e) = _
  rw [map_mul, map_star]
  change inner ℂ e ((π f).adjoint (π f e)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K]
  exact (Complex.ofReal_pow _ _).symm

lemma vectorFunctional_positive (f : C(X, ℂ))
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re) :
    (vectorFunctional π e f).im = 0 ∧ 0 ≤ (vectorFunctional π e f).re := by
  let g : C(X, ℂ) := ⟨fun x => (Real.sqrt (f x).re : ℂ),
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (Complex.continuous_re.comp f.continuous))⟩
  have hfg : star g * g = f := by
    ext x
    change star (Real.sqrt (f x).re : ℂ) * (Real.sqrt (f x).re : ℂ) = f x
    have hs : star (Real.sqrt (f x).re : ℂ) = (Real.sqrt (f x).re : ℂ) := by simp
    rw [hs, ← Complex.ofReal_mul, Real.mul_self_sqrt (hf x).2]
    exact Complex.ext (by simp) (by simp [(hf x).1])
  rw [← hfg, vectorFunctional_square]
  exact ⟨rfl, sq_nonneg ‖π g e‖⟩


variable [MeasurableSpace X] [BorelSpace X]

/-- Riesz--Markov applied to the unnormalized vector functional. -/
lemma exists_vectorMeasure :
    ∃ μ : Measure X, μ.Regular ∧ μ univ < ∞ ∧
      ∀ f : C(X, ℂ), Integrable f μ ∧
        vectorFunctional π e f = ∫ x, f x ∂μ := by
  obtain ⟨q, hq, hqs⟩ := FunctionSpaces.ScalarRieszMarkov.compact_identification X ℂ
  let L : C₀(X, ℂ) →L[ℂ] ℂ :=
    (vectorFunctional π e).comp q.symm.toLinearIsometry.toContinuousLinearMap
  have hL (f : C₀(X, ℂ)) (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re) :
      (L f).im = 0 ∧ 0 ≤ (L f).re := by
    apply vectorFunctional_positive π e (q.symm f)
    intro x
    simpa only [hqs] using hf x
  obtain ⟨μ, hμ, hfinite, hrep, _, _⟩ :=
    FunctionSpaces.ScalarRieszMarkov.complex_positive_representation X L hL
  refine ⟨μ, (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ,
    hfinite, ?_⟩
  intro f
  have hi := (hrep (q f)).1
  have heq := (hrep (q f)).2
  change vectorFunctional π e (q.symm (q f)) = _ at heq
  rw [q.symm_apply_apply] at heq
  have hfun : ⇑(q f) = ⇑f := funext (hq f)
  rw [hfun] at hi heq
  exact ⟨hi, heq⟩

/-- The scalar measure turns the continuous orbit into an L² isometry. -/
lemma continuousOrbit_norm (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ f : C(X, ℂ), Integrable f μ ∧ vectorFunctional π e f = ∫ x, f x ∂μ)
    (f : C(X, ℂ)) :
    ‖continuousOrbit π e f‖ = ‖ContinuousMap.toLp 2 μ ℂ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [SpectralMeasure.CyclicModel.l2_norm_sq]
  have h := congrArg Complex.re ((hμ (star f * f)).2)
  rw [vectorFunctional_square] at h
  change ‖π f e‖ ^ 2 = RCLike.re (∫ x, (star f * f) x ∂μ) at h
  rw [← integral_re (hμ (star f * f)).1] at h
  calc
    ‖continuousOrbit π e f‖ ^ 2 = ∫ x, ((star f * f) x).re ∂μ := by
      exact h
    _ = ∫ x, ‖(ContinuousMap.toLp 2 μ ℂ f) x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ f] with x hx
      rw [hx]
      simp [Complex.sq_norm, Complex.normSq_apply]


/-- Extend the isometry between the dense continuous orbit and the dense
continuous functions in L², then extend intertwining by continuity. -/
theorem compact_scalar_model
    (he : DenseRange (continuousOrbit π e)) :
    ∃ (μ : Measure X) (hμ : IsFiniteMeasure μ), letI := hμ
      ∃ U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ, ∀ f : C(X, ℂ), ∀ x : H,
        U (π f x) = ScalarMultiplicationCommutant.Spec.multiplier μ
          (ContinuousMap.toLp ∞ μ ℂ f) (U x) := by
  obtain ⟨μ, hreg, hfinite, hrep⟩ := exists_vectorMeasure π e
  let : μ.Regular := hreg
  let : IsFiniteMeasure μ := ⟨hfinite⟩
  let j := (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap
  let v := (continuousOrbit π e).toLinearMap
  have hj : DenseRange j := ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)
  have hv : DenseRange v := he
  have hn : ∀ f, ‖v f‖ = ‖j f‖ := continuousOrbit_norm π e μ hrep
  let V : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H :=
    (LinearEquiv.refl ℂ C(X, ℂ)).extendOfIsometry j v hj hv hn
  have hV (f : C(X, ℂ)) : V (ContinuousMap.toLp 2 μ ℂ f) = π f e :=
    LinearEquiv.extendOfIsometry_eq _ _ _ hj hv hn f
  have hinter (g : C(X, ℂ)) (u : Lp ℂ 2 μ) :
      V (ScalarMultiplicationCommutant.Spec.multiplier μ
        (ContinuousMap.toLp ∞ μ ℂ g) u) = π g (V u) := by
    apply congrFun (hj.equalizer
      (V.continuous.comp (ScalarMultiplicationCommutant.Spec.multiplier μ
        (ContinuousMap.toLp ∞ μ ℂ g)).continuous)
      ((π g).continuous.comp V.continuous) ?_) u
    funext f
    change V (SpectralMeasure.CyclicModel.Spec.multiplier μ g
      (ContinuousMap.toLp 2 μ ℂ f)) = π g (V (ContinuousMap.toLp 2 μ ℂ f))
    rw [SpectralMeasure.CyclicModel.multiplier_toLp, hV, hV, map_mul]
    rfl
  refine ⟨μ, inferInstance, V.symm, ?_⟩
  intro f x
  apply V.injective
  rw [V.apply_symm_apply, hinter, V.apply_symm_apply]

end CompactModel

open scoped IsMulCommutative

/-- The original operator norm on the closed abelian algebra supplies its
commutative C*-structure. Gelfand duality supplies a scalar function model;
no measure model or single normal generator is assumed. -/
theorem cyclic_scalar_representation : Spec.CyclicScalarRepresentation.{u} := by
  intro H _ _ _ A hcomm hclosed e he
  let : IsClosed (A : Set (H →L[ℂ] H)) := hclosed
  let : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hcomm a a.property b b.property)⟩⟩
  let X := WeakDual.characterSpace ℂ A
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let g : A ≃⋆ₐ[ℂ] C(X, ℂ) := gelfandStarTransform A
  let π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) := A.subtype.comp g.symm.toStarAlgHom
  have hπ (a : A) : π (g a) = (a : H →L[ℂ] H) := by
    change ((g.symm (g a) : A) : H →L[ℂ] H) = _
    rw [g.symm_apply_apply]
  have hdense : DenseRange (continuousOrbit π e) := by
    apply he.mono
    rintro _ ⟨a, rfl⟩
    exact ⟨g a, congrArg (fun T : H →L[ℂ] H => T e) (hπ a)⟩
  obtain ⟨μ, hμ, U, hU⟩ := compact_scalar_model π e hdense
  let := hμ
  refine ⟨X, inferInstance, μ, hμ, U, ?_⟩
  intro T hT
  refine ⟨ContinuousMap.toLp ∞ μ ℂ (g ⟨T, hT⟩), ?_⟩
  intro x
  simpa only [hπ] using hU (g ⟨T, hT⟩) x

end ExpandedFA.VonNeumann.CyclicAbelianScalarRepresentation
