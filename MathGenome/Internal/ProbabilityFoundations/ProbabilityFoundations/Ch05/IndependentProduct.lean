import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.CylinderFramework
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceJointLaws
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.IndependentProduct
import Mathlib.Probability.ProductMeasure

/-!
The arbitrary independent product theorem, paper.tex:1332–1341.
The upstream `cylinderSigma_eq_pi` identifies the measurable structure used
here with the source's cylinder sigma-algebra. Mathlib's infinite product
construction is valid for arbitrary measurable spaces and arbitrary indices.
-/

open MeasureTheory
open ProbabilityFoundations.Ch05.CylinderFramework

namespace ProbabilityFoundations.Ch05.IndependentProduct

universe u v w z

/-- Consistency holds on every pair of nested finite supports. -/
theorem finiteProductConsistency :
    Specs.ProbabilityFoundations.Ch05.IndependentProduct.FiniteProductConsistency.{u,v} := by
  intro I S inst μi hμi E F hEF
  exact (isProjectiveMeasureFamily_pi μi F E hEF).symm

/-- Uniqueness from finite-dimensional laws does not require independence. -/
theorem finiteDimensionalUniqueness :
    Specs.ProbabilityFoundations.Ch05.IndependentProduct.FiniteDimensionalUniqueness.{u,v} := by
  intro I S inst μ ν hμ hν h
  exact IsProjectiveLimit.unique
    (P := fun F => Measure.map (finiteProjection S F) μ)
    (fun _ => rfl) (fun F => (h F).symm)

/-- The constructed probability has independent coordinate maps. -/
theorem infinitePi_independent_coordinates
    {I : Type u} (S : I → Type v) [∀ i, MeasurableSpace (S i)]
    (μi : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μi i)] :
    Ch02.IndependentRandomElements (Measure.infinitePi μi)
      (fun i (x : ProductSpace S) => x i) := by
  apply (Ch02.independentRandomElements_iff_finite_jointLaws_eq_pi
    (Measure.infinitePi μi) _ (fun i => measurable_pi_apply i)).mpr
  intro F
  change Measure.map F.restrict (Measure.infinitePi μi) =
    Measure.pi (fun i : F => Measure.map (fun x : ProductSpace S => x i)
      (Measure.infinitePi μi))
  simp only [Measure.infinitePi_map_eval]
  exact Measure.infinitePi_map_restrict μi

/-- Independence and the prescribed one-dimensional laws are exactly the
finite product-law identities, including the identity on empty support. -/
theorem independenceCharacterization :
    Specs.ProbabilityFoundations.Ch05.IndependentProduct.IndependenceCharacterization.{u,v} := by
  intro I S inst μi hμi ν hν
  change ((∀ i, Measure.map (fun x : ProductSpace S => x i) ν = μi i) ∧
    Ch02.IndependentRandomElements ν (fun i (x : ProductSpace S) => x i)) ↔ _
  constructor
  · rintro ⟨hmarg, hind⟩
    have h := (Ch02.independentRandomElements_iff_finite_jointLaws_eq_pi
      ν _ (fun i => measurable_pi_apply i)).mp hind
    intro F
    have hF := h F
    change Measure.map F.restrict ν =
      Measure.pi (fun i : F => Measure.map (fun x : ProductSpace S => x i) ν) at hF
    change Measure.map F.restrict ν = Measure.pi (fun i : F => μi i)
    simpa only [hmarg] using hF
  · intro h
    have heq : ν = Measure.infinitePi μi := by
      apply finiteDimensionalUniqueness S ν (Measure.infinitePi μi)
      intro F
      exact (h F).trans (Measure.infinitePi_map_restrict μi).symm
    subst ν
    exact ⟨Measure.infinitePi_map_eval μi, infinitePi_independent_coordinates S μi⟩

/-- There is exactly one probability on the cylinder sigma-algebra with the
specified mutually independent coordinates. No assumptions on the index type
exclude the empty product. -/
theorem independentProduct :
    Specs.ProbabilityFoundations.Ch05.IndependentProduct.IndependentProductExistenceUniqueness.{u,v} := by
  intro I S inst μi hμi
  refine ⟨Measure.infinitePi μi, ?_, ?_⟩
  · exact ⟨inferInstance, Measure.infinitePi_map_eval μi,
      infinitePi_independent_coordinates S μi⟩
  · intro ν hν
    obtain ⟨hprob, hmarg, hind⟩ := hν
    have := hprob
    apply finiteDimensionalUniqueness S ν (Measure.infinitePi μi)
    intro F
    exact ((independenceCharacterization S μi ν).mp ⟨hmarg, hind⟩ F).trans
      (Measure.infinitePi_map_restrict μi).symm

/-- Product-valued process laws are determined by all finite subfamily laws,
even when the processes have different underlying probability spaces. -/
theorem processLawDetermination
    {I : Type u} {Ω : Type w} {Ω' : Type z}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (S : I → Type v) [∀ i, MeasurableSpace (S i)]
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ∀ i, Ω → S i) (Y : ∀ i, Ω' → S i)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (h : ∀ F : Finset I,
      Measure.map (fun ω (i : F) => X i ω) P =
        Measure.map (fun ω (i : F) => Y i ω) Q) :
    Measure.map (fun ω i => X i ω) P = Measure.map (fun ω i => Y i ω) Q := by
  have hmX : Measurable (fun ω i => X i ω) := measurable_pi_iff.mpr hX
  have hmY : Measurable (fun ω i => Y i ω) := measurable_pi_iff.mpr hY
  apply finiteDimensionalUniqueness S
    (Measure.map (fun ω i => X i ω) P) (Measure.map (fun ω i => Y i ω) Q)
  intro F
  rw [Measure.map_map (measurable_finiteProjection S F) hmX,
    Measure.map_map (measurable_finiteProjection S F) hmY]
  exact h F

end ProbabilityFoundations.Ch05.IndependentProduct
