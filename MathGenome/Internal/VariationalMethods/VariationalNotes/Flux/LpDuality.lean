import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.LpDuality
import MathGenome.FunctionalAnalysis.Topics.ExpandedFA.PartIV
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace VariationalNotes.Flux.LpDuality

/-- A fiberwise real linear isometric equivalence induces one on Bochner Lp. -/
def liftLpIsometry {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (q : ℝ≥0∞) [Fact (1 ≤ q)] (μ : Measure X) :
    Lp E q μ ≃ₗᵢ[ℝ] Lp F q μ where
  toLinearEquiv :=
    { toLinearMap := e.toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ q μ
      invFun := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
      left_inv := by
        intro f
        change e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
          (e.toContinuousLinearEquiv.toContinuousLinearMap.compLp f) = f
        apply Lp.ext
        filter_upwards [e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
          (e.toContinuousLinearEquiv.toContinuousLinearMap.compLp f),
          e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with x hx hy
        simpa only [ContinuousLinearMap.compLpₗ_apply, hy, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.symm_apply_apply] using hx
      right_inv := by
        intro f
        change e.toContinuousLinearEquiv.toContinuousLinearMap.compLp
          (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp f) = f
        apply Lp.ext
        filter_upwards [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
          (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp f),
          e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with x hx hy
        simpa only [ContinuousLinearMap.compLpₗ_apply, hy, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply] using hx }
  norm_map' := by
    intro f
    change ‖e.toContinuousLinearEquiv.toContinuousLinearMap.compLp f‖ = ‖f‖
    simp only [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with x hx
    rw [hx]
    exact e.norm_map (f x)

/-- The induced map agrees a.e. with pointwise application on representatives. -/
theorem liftLpIsometry_ae {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (q : ℝ≥0∞) [Fact (1 ≤ q)] (μ : Measure X)
    (f : Lp E q μ) : liftLpIsometry e q μ f =ᵐ[μ] fun x => e (f x) :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f

/-- Real Hilbert spaces are reflexive for the canonical evaluation map used
by MathGenome's vector-valued duality theorem. -/
theorem hilbert_reflexive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ E := by
  intro L
  let R := InnerProductSpace.toDual ℝ E
  let x := R.symm (L.comp R.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨x, ?_⟩
  ext f
  change f x = L f
  have h := InnerProductSpace.toDual_symm_apply
    (x := R.symm f) (y := L.comp R.toContinuousLinearEquiv.toContinuousLinearMap)
  change inner ℝ x (R.symm f) = L (R (R.symm f)) at h
  rw [R.apply_symm_apply] at h
  rw [← h, real_inner_comm]
  exact (InnerProductSpace.toDual_symm_apply (x := x) (y := f)).symm

/-- Real Euclidean Lp duality on every measurable finite-Lebesgue-measure set.
The Riesz identification is lifted to Lq before applying the public PartIV
vector duality theorem, so the pairing is exactly the real dot product. -/
theorem isometric_duality : VariationalNotes.Flux.LpDualitySpec.Statement := by
  intro d hd Ω hΩ hvol p hp
  let E := EuclideanSpace ℝ (Fin d)
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal (p / (p - 1))
  let μ : Measure E := volume.restrict Ω
  let : ENNReal.HolderConjugate P Q :=
    (Real.HolderConjugate.conjExponent hp).ennrealOfReal
  let : Fact (1 ≤ P) := ⟨ENNReal.HolderConjugate.one_le P Q⟩
  let : Fact (1 ≤ Q) := ⟨ENNReal.HolderConjugate.one_le Q P⟩
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hvol⟩
  obtain ⟨T, hT⟩ := ExpandedFA.PartIV.VectorLpDual.isometric_equivalence
    ℝ (hilbert_reflexive (E := E)) μ P Q ENNReal.ofReal_ne_top
  let R := liftLpIsometry (InnerProductSpace.toDual ℝ E) Q μ
  let S := R.trans T
  have formula (σ : Lp E Q μ) (v : Lp E P μ) :
      Integrable (fun x => inner ℝ (σ x) (v x)) μ ∧
        S σ v = ∫ x, inner ℝ (σ x) (v x) ∂μ := by
    obtain ⟨hint, hform⟩ := hT (R σ) v
    have hae : (fun x => (R σ) x (v x)) =ᵐ[μ]
        (fun x => inner ℝ (σ x) (v x)) := by
      filter_upwards [liftLpIsometry_ae (InnerProductSpace.toDual ℝ E) Q μ σ] with x hx
      change (R σ) x = InnerProductSpace.toDual ℝ E (σ x) at hx
      rw [hx]
      rfl
    exact ⟨hint.congr hae, hform.trans (integral_congr_ae hae)⟩
  refine ⟨S, formula, ?_, ?_⟩
  · intro L
    refine ⟨S.symm L, ⟨?_, ?_⟩, ?_⟩
    · intro v
      simpa only [S.apply_symm_apply] using (formula (S.symm L) v).2
    · exact S.symm.norm_map L
    · intro σ hσ
      apply S.injective
      ext v
      exact (formula σ v).2.trans ((hσ.1 v).symm.trans
        (congrArg (fun M => M v) (S.apply_symm_apply L).symm))
  · intro σ τ
    constructor
    · intro h
      have heq : σ = τ := S.injective (by
        ext v
        exact (formula σ v).2.trans ((h v).trans (formula τ v).2.symm))
      subst τ
      exact Filter.EventuallyEq.rfl
    · intro h v
      exact integral_congr_ae (h.mono (fun x hx => congrArg (fun z => inner ℝ z (v x)) hx))

end VariationalNotes.Flux.LpDuality
