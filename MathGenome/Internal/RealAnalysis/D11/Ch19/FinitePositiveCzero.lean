import MathGenome.Internal.RealAnalysis.D11.Ch19.CzeroBanachDensity
import MathGenome.Internal.RealAnalysis.D11.Ch19.RecoverOpenCompactMass
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.FinitePositiveCzero

/-!
Finite positive Radon integration on C0 (paper.tex:5566–5573).
The converse and sharp lower bound use the previously established open-mass
recovery formula. The forward construction is the ordinary bounded integral,
and density gives uniqueness. All scalar arguments apply to both ℝ and ℂ.
-/

open Set MeasureTheory
open Specs.D11.Ch19.FinitePositiveCzero (Positive ExtendsIntegral)

namespace D11.Ch19.FinitePositiveCzero
universe u
noncomputable section

variable {X : Type u} [TopologicalSpace X]
variable (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

/-- Ordinary integration as a bounded map when the total mass is finite. -/
def integralFunctional (μ : Measure X) [IsFiniteMeasure μ] :
    ZeroAtInftyContinuousMap X 𝕜 →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (f.toBCF.integrable μ) (g.toBCF.integrable μ)
      map_smul' := fun a f => integral_smul a f }
    (μ univ).toReal (fun f => f.toBCF.norm_integral_le_mul_norm μ)

lemma integralFunctional_extends (μ : Measure X) [IsFiniteMeasure μ] :
    ExtendsIntegral μ (integralFunctional 𝕜 μ) := fun _ => rfl

lemma integralFunctional_positive (μ : Measure X) [IsFiniteMeasure μ] :
    Positive (integralFunctional 𝕜 μ) := by
  intro f hf
  change 0 ≤ RCLike.re (∫ x, f x ∂μ) ∧ RCLike.im (∫ x, f x ∂μ) = 0
  have hfint : Integrable (fun x => f x) μ := f.toBCF.integrable μ
  rw [← integral_re hfint, ← integral_im hfint]
  exact ⟨integral_nonneg (fun x => (hf x).1),
    by simp only [show (fun x => RCLike.im (f x)) = (fun _ => 0) from
      funext (fun x => (hf x).2), integral_zero]⟩

lemma integralFunctional_norm_le (μ : Measure X) [IsFiniteMeasure μ] :
    ‖integralFunctional 𝕜 μ‖ ≤ (μ univ).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
  intro f
  exact f.toBCF.norm_integral_le_mul_norm μ

/-- Embed a real test into either scalar field without changing its support. -/
def realTest (f : CompactlySupportedContinuousMap X ℝ) :
    CompactlySupportedContinuousMap X 𝕜 :=
  ⟨⟨fun x => (f x : 𝕜), RCLike.continuous_ofReal.comp f.continuous⟩,
    f.hasCompactSupport.comp_left (by simp)⟩

variable [T2Space X] [LocallyCompactSpace X]

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
/-- The open-mass formula controls the total mass by any bounded extension. -/
lemma mass_le_norm (μ : Measure X) (hμ : D11.Ch18.isRadon μ)
    (L : ZeroAtInftyContinuousMap X 𝕜 →L[𝕜] 𝕜) (hL : ExtendsIntegral μ L) :
    μ univ ≤ ENNReal.ofReal ‖L‖ := by
  obtain ⟨I, hI, hrep⟩ := PositiveRieszMarkov.radon_induces_real_functional μ hμ
  rw [RecoverOpenCompactMass.real_open_mass I hI μ hrep univ isOpen_univ]
  refine iSup_le fun f => iSup_le fun hf => iSup_le fun _ => ?_
  apply ENNReal.ofReal_le_ofReal
  have hn : ‖ccInclusion X 𝕜 (realTest 𝕜 f)‖ ≤ 1 := by
    apply (czero_norm_le_iff X 𝕜 _ 1 zero_le_one).mpr
    intro x
    change ‖(f x : 𝕜)‖ ≤ 1
    simpa only [RCLike.norm_ofReal, abs_of_nonneg (hf x).1] using (hf x).2
  have he : L (ccInclusion X 𝕜 (realTest 𝕜 f)) = (I f : 𝕜) := by
    calc
      L (ccInclusion X 𝕜 (realTest 𝕜 f)) = ∫ x, (f x : 𝕜) ∂μ := hL (realTest 𝕜 f)
      _ = (I f : 𝕜) := by
        rw [integral_ofReal]
        congr 1
        exact (hrep.2 f).choose_spec.symm
  calc
    I f ≤ ‖(I f : 𝕜)‖ := by
      rw [RCLike.norm_ofReal]
      exact le_abs_self _
    _ = ‖L (ccInclusion X 𝕜 (realTest 𝕜 f))‖ := congrArg norm he.symm
    _ ≤ ‖L‖ * ‖ccInclusion X 𝕜 (realTest 𝕜 f)‖ := L.le_opNorm _
    _ ≤ ‖L‖ := by simpa using mul_le_mul_of_nonneg_left hn (norm_nonneg L)

theorem extension_unique : Specs.D11.Ch19.FinitePositiveCzero.extension_unique := by
  intro X _ _ _ 𝕜 _ μ L M hL hM
  apply DFunLike.coe_injective
  apply (cc_denseRange X 𝕜).equalizer L.continuous M.continuous
  funext f
  exact (hL f).trans (hM f).symm

theorem bounded_extension_iff : Specs.D11.Ch19.FinitePositiveCzero.bounded_extension_iff := by
  intro X _ _ _ 𝕜 _ _ _ μ hμ
  constructor
  · rintro ⟨L, hL, _⟩
    exact (mass_le_norm 𝕜 μ hμ L hL).trans_lt ENNReal.ofReal_lt_top
  · intro hfin
    let : IsFiniteMeasure μ := ⟨hfin⟩
    exact ⟨integralFunctional 𝕜 μ, integralFunctional_extends 𝕜 μ,
      integralFunctional_positive 𝕜 μ⟩

theorem extension_identification :
    Specs.D11.Ch19.FinitePositiveCzero.extension_identification := by
  intro X _ _ _ 𝕜 _ _ _ μ hμ L hL
  have hb := mass_le_norm 𝕜 μ hμ L hL
  have hfin : μ univ < ⊤ := hb.trans_lt ENNReal.ofReal_lt_top
  let : IsFiniteMeasure μ := ⟨hfin⟩
  have he : L = integralFunctional 𝕜 μ :=
    extension_unique 𝕜 μ L _ hL (integralFunctional_extends 𝕜 μ)
  have hn : ‖L‖ = (μ univ).toReal := by
    apply le_antisymm
    · rw [he]
      exact integralFunctional_norm_le 𝕜 μ
    · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      simpa only [ENNReal.toReal_ofReal (norm_nonneg L)] using h
  refine ⟨hfin, ?_, ?_, hn, ?_⟩
  · rw [he]
    exact integralFunctional_positive 𝕜 μ
  · intro f
    exact ⟨f.continuous.measurable, f.toBCF.integrable μ, by rw [he]; rfl⟩
  · rw [hn, ENNReal.ofReal_toReal hfin.ne]

end
end D11.Ch19.FinitePositiveCzero
