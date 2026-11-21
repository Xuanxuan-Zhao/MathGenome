import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.WeakDerivativeSpaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevCompleteness
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Basic.Real.ConjExponents
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace

namespace ExpandedFA.Sobolev
open ExpandedFA.Distributions ExpandedFA.FunctionSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Definitional bridge from the upstream pairing specification. -/
theorem lpIntegralPairing_apply {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (a b : ℝ≥0∞) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
    [ENNReal.HolderConjugate a b] (g : Lp 𝕜 b μ) (f : Lp 𝕜 a μ) :
    lpIntegralPairing μ a b g f = ∫ x, f x * g x ∂μ :=
  (lp_pairing_integral μ a b g f).2

/-- Hölder makes pairing with any compactly supported smooth test continuous,
including the two endpoint exponents. -/
def lpTestEvaluation (φ : Tests 𝕜 Ω) : DomainLp 𝕜 Ω p →L[𝕜] 𝕜 := by
  let q := ENNReal.conjExponent p
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  exact lpIntegralPairing (volume.restrict (Ω : Set (Domain d))) p q
    (testToDomainLp (p := q) φ)

@[simp] theorem lpTestEvaluation_apply (φ : Tests 𝕜 Ω) (u : DomainLp 𝕜 Ω p) :
    lpTestEvaluation φ u = lpDistribution u φ := by
  let q := ENNReal.conjExponent p
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  change lpIntegralPairing _ p q _ u = _
  rw [lpIntegralPairing_apply _ p q _ u, lpDistribution_apply]
  apply integral_congr_ae
  filter_upwards [testToDomainLp_coe (p := q) φ] with x hx
  rw [hx, mul_comm]

/-- The graph is the intersection of the kernels of these continuous scalar
functionals. This also supplies the equations used in the bidual argument. -/
def derivativeResidual (α : DerivativeIndex d m) (φ : Tests 𝕜 Ω) :
    DerivativeTuple 𝕜 Ω m p →L[𝕜] 𝕜 :=
  (lpTestEvaluation φ).comp (PiLp.proj 1 _ α) -
    ((-1 : 𝕜) ^ (multiIndexWord (natIndex α)).length) •
      (lpTestEvaluation (testPartialCLM (multiIndexWord (natIndex α)) φ)).comp
        (PiLp.proj 1 _ (zeroIndex d m))

theorem mem_derivativeGraph_iff (v : DerivativeTuple 𝕜 Ω m p) :
    v ∈ derivativeGraph 𝕜 Ω m p ↔ ∀ α φ, derivativeResidual α φ v = 0 := by
  change (∀ α, lpDistributionLM (v α) = _) ↔ _
  simp only [ContinuousLinearMap.ext_iff]
  change (∀ α φ, lpDistribution (v α) φ = _) ↔ _
  simp only [derivativeResidual, sub_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    PiLp.proj, PiLp.projₗ, lpTestEvaluation_apply,
    smul_eq_mul, sub_eq_zero,
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue]
  rfl

theorem sobolev_closed_graph : Specs.ExpandedFA.Sobolev.SobolevCompleteness.ClosedGraph := by
  intro 𝕜 _ d Ω m p _
  have heq : (derivativeGraph 𝕜 Ω m p : Set (DerivativeTuple 𝕜 Ω m p)) =
      ⋂ α, ⋂ φ, {v | derivativeResidual α φ v = 0} := by
    ext v
    simp only [mem_iInter, mem_ofPred_eq]
    exact mem_derivativeGraph_iff v
  rw [heq]
  exact isClosed_iInter fun α => isClosed_iInter fun φ =>
    isClosed_eq (derivativeResidual α φ).continuous continuous_const

theorem sobolev_complete : Specs.ExpandedFA.Sobolev.SobolevCompleteness.Banach := by
  intro 𝕜 _ d Ω m p _
  exact (sobolev_closed_graph 𝕜 d Ω m p).completeSpace_coe

theorem sobolev_separable : Specs.ExpandedFA.Sobolev.SobolevCompleteness.Separable := by
  intro 𝕜 _ d Ω m p _ hp
  have : Fact (p ≠ ∞) := ⟨hp.ne⟩
  have : SecondCountableTopology (DomainLp 𝕜 Ω p) := by
    unfold DomainLp
    infer_instance
  change SeparableSpace (derivativeGraph 𝕜 Ω m p)
  infer_instance

/-- Scalar Lp reflexivity follows from the bilinear duality theorem twice;
no conjugate-linear dual is introduced. -/
theorem domainLp_reflexive (hp : 1 < p) (hpt : p < ∞) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 (DomainLp 𝕜 Ω p)) := by
  let q := ENNReal.conjExponent p
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hpt
  have hqt : q < ∞ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp
  let μ := volume.restrict (Ω : Set (Domain d))
  intro B
  let A := lpIntegralPairing (𝕜 := 𝕜) μ p q
  obtain ⟨u, hu⟩ := (lp_pairing_arbitrary_isometric_bijective (𝕜 := 𝕜) μ q p hq hqt.ne).2.2
    (B.comp A)
  refine ⟨u, ?_⟩
  ext L
  obtain ⟨g, rfl⟩ := (lp_pairing_arbitrary_isometric_bijective (𝕜 := 𝕜) μ p q hp hpt.ne).2.2 L
  change lpIntegralPairing μ p q g u = B (A g)
  rw [← show lpIntegralPairing μ q p u g = B (A g) from
    congrArg (fun f : Lp 𝕜 q μ →L[𝕜] 𝕜 => f g) hu]
  rw [lpIntegralPairing_apply μ p q g u, lpIntegralPairing_apply μ q p u g]
  simp only [mul_comm]

/-- Bidual surjectivity passes through continuous linear equivalences. -/
theorem reflexive_of_equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : E ≃L[𝕜] F)
    (hF : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 F)) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E) := by
  intro B
  let r : (F →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) :=
    (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip e.toContinuousLinearMap
  obtain ⟨v, hv⟩ := hF (B.comp r)
  refine ⟨e.symm v, ?_⟩
  ext L
  have h := congrArg (fun f : (F →L[𝕜] 𝕜) →L[𝕜] 𝕜 => f (L.comp e.symm.toContinuousLinearMap)) hv
  have heq : r (L.comp e.symm.toContinuousLinearMap) = L := by
    ext x
    simp [r]
  simp only [NormedSpace.dual_def, ContinuousLinearMap.comp_apply, heq] at h
  exact h

/-- Finite products preserve canonical bidual surjectivity. -/
theorem finitePi_reflexive {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (hE : ∀ i, Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 (E i))) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 (∀ i, E i)) := by
  classical
  intro B
  let r (i : ι) : (E i →L[𝕜] 𝕜) →L[𝕜] ((∀ i, E i) →L[𝕜] 𝕜) :=
    (ContinuousLinearMap.compL 𝕜 (∀ i, E i) (E i) 𝕜).flip (ContinuousLinearMap.proj i)
  choose v hv using fun i => hE i (B.comp (r i))
  refine ⟨v, ?_⟩
  ext L
  have hL : L = ∑ i, r i (L.comp (ContinuousLinearMap.single 𝕜 E i)) := by
    ext x
    simpa [r] using (ContinuousLinearMap.sum_comp_single 𝕜 E L x).symm
  change L v = B L
  conv_rhs => rw [hL]
  rw [map_sum]
  calc
    L v = ∑ i, L.comp (ContinuousLinearMap.single 𝕜 E i) (v i) :=
      (ContinuousLinearMap.sum_comp_single 𝕜 E L v).symm
    _ = _ := Finset.sum_congr rfl fun i _ =>
      congrArg (fun f : (E i →L[𝕜] 𝕜) →L[𝕜] 𝕜 =>
        f (L.comp (ContinuousLinearMap.single 𝕜 E i))) (hv i)

/-- A bidual element of the graph is first realized in the ambient product.
Its residuals vanish, so the realizing tuple belongs to the graph. -/
theorem sobolev_reflexive : Specs.ExpandedFA.Sobolev.SobolevCompleteness.Reflexive := by
  intro 𝕜 _ d Ω m p _ hp hpt
  let E := DerivativeTuple 𝕜 Ω m p
  let S := derivativeGraph 𝕜 Ω m p
  have hE : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E) :=
    reflexive_of_equiv (PiLp.continuousLinearEquiv 1 𝕜 _)
      (finitePi_reflexive fun _ => domainLp_reflexive hp hpt)
  let r : (E →L[𝕜] 𝕜) →L[𝕜] (S →L[𝕜] 𝕜) :=
    (ContinuousLinearMap.compL 𝕜 S E 𝕜).flip S.subtypeL
  intro B
  obtain ⟨v, hv⟩ := hE (B.comp r)
  have hres (α : DerivativeIndex d m) (φ : Tests 𝕜 Ω) :
      r (derivativeResidual α φ) = 0 := by
    ext u
    exact (mem_derivativeGraph_iff u.val).mp u.property α φ
  have hmem : v ∈ S := by
    apply (mem_derivativeGraph_iff v).mpr
    intro α φ
    have h := congrArg (fun f : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 => f (derivativeResidual α φ)) hv
    simpa only [NormedSpace.dual_def, ContinuousLinearMap.comp_apply, hres, map_zero] using h
  refine ⟨⟨v, hmem⟩, ?_⟩
  ext L
  obtain ⟨f, hf, _⟩ := exists_extension_norm_eq S L
  have hrf : r f = L := by
    ext u
    exact hf u
  have h := congrArg (fun F : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 => F f) hv
  change L ⟨v, hmem⟩ = B L
  rw [← hf ⟨v, hmem⟩]
  simpa only [NormedSpace.dual_def, ContinuousLinearMap.comp_apply, hrf] using h

/-- The identity on all derivative components, with the Euclidean product norm
on the target. -/
def sobolevToHilbert (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)) (m : ℕ) :
    SobolevSpace 𝕜 d Ω m 2 ≃L[𝕜] hilbertDerivativeGraph 𝕜 Ω m :=
  ((derivativeTupleToL2 𝕜 Ω m).symm.ofSubmodule' (derivativeGraph 𝕜 Ω m 2)).symm

@[simp] theorem sobolevToHilbert_apply (u : SobolevSpace 𝕜 d Ω m 2)
    (α : DerivativeIndex d m) : (sobolevToHilbert 𝕜 d Ω m u).val α = u.val α := rfl

theorem hilbertDerivativeGraph_complete (𝕜 : Type) [RCLike 𝕜]
    (d : ℕ) (Ω : Opens (Domain d)) (m : ℕ) :
    CompleteSpace (hilbertDerivativeGraph 𝕜 Ω m) := by
  have hclosed : IsClosed (hilbertDerivativeGraph 𝕜 Ω m :
      Set (PiLp 2 (fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω 2))) := by
    change IsClosed ((derivativeTupleToL2 𝕜 Ω m).symm ⁻¹'
      (derivativeGraph 𝕜 Ω m 2 : Set (DerivativeTuple 𝕜 Ω m 2)))
    exact (sobolev_closed_graph 𝕜 d Ω m 2).preimage (derivativeTupleToL2 𝕜 Ω m).symm.continuous
  exact hclosed.completeSpace_coe

theorem sobolev_hilbert_structure :
    Specs.ExpandedFA.Sobolev.SobolevCompleteness.HilbertStructure := by
  intro 𝕜 _ d Ω m
  refine ⟨hilbertDerivativeGraph_complete 𝕜 d Ω m, sobolevToHilbert 𝕜 d Ω m,
    fun _ _ => rfl, ?_, ?_⟩
  · intro u v
    change ⟪(sobolevToHilbert 𝕜 d Ω m u).val,
      (sobolevToHilbert 𝕜 d Ω m v).val⟫_𝕜 = _
    rw [PiLp.inner_apply]
    rfl
  · have hn (u : SobolevSpace 𝕜 d Ω m 2) :
        ‖sobolevToHilbert 𝕜 d Ω m u‖ =
          Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.HilbertNormValue 𝕜 d Ω m u := by
      change ‖(sobolevToHilbert 𝕜 d Ω m u).val‖ = _
      rw [PiLp.norm_eq_of_L2]
      rfl
    exact ⟨hn, fun u => by rw [hn]; exact sobolev_hilbert_norm_equivalent 𝕜 d Ω m u⟩

end ExpandedFA.Sobolev
