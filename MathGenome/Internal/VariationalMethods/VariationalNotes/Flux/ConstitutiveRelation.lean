import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.ConstitutiveRelation
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.DirichletDuality
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Subgradients

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TopologicalSpace Set

namespace VariationalNotes.Flux.ConstitutiveRelation
open Sobolev WeakDivergenceSpec IntegralConjugacySpecs ConstitutiveRelationSpecs

/-- The vector definition is precisely the manuscript's continuous-dual
subdifferential under the Euclidean pairing. -/
theorem mem_fiberSubdifferential_iff {d : ℕ} (f : Vector d → ℝ) (z w : Vector d) :
    w ∈ fiberSubdifferential f z ↔
      innerSL ℝ w ∈ ConvexAnalysis.subdifferential (fun y => (f y : WithTop ℝ)) z := by
  rw [ConvexAnalysis.mem_subdifferential_iff (f := fun y => (f y : WithTop ℝ))
    (x := z) (r := f z) rfl]
  simp only [fiberSubdifferential, mem_ofPred_eq, innerSL_apply_apply, WithTop.coe_le_coe]

/-- Finiteness is essential before taking the real value of the conjugate. -/
theorem pointwise_gap {d : ℕ} (F : Vector d → ℝ) (z w : Vector d)
    (ht : IntegralConjugacySpecs.pointwiseConjugate (fun _ : Unit => F) () w ≠ ⊤)
    (hb : IntegralConjugacySpecs.pointwiseConjugate (fun _ : Unit => F) () w ≠ ⊥) :
    0 ≤ F z + (IntegralConjugacySpecs.pointwiseConjugate (fun _ : Unit => F) () w).toReal - inner ℝ w z ∧
    (F z + (IntegralConjugacySpecs.pointwiseConjugate (fun _ : Unit => F) () w).toReal - inner ℝ w z = 0 ↔
      w ∈ fiberSubdifferential F z) := by
  let C := IntegralConjugacySpecs.pointwiseConjugate (fun _ : Unit => F) () w
  have hC : (C.toReal : EReal) = C := EReal.coe_toReal ht hb
  have hlow : ((inner ℝ w z - F z : ℝ) : EReal) ≤ C :=
    le_iSup (fun y => ((inner ℝ w y - F y : ℝ) : EReal)) z
  rw [← hC] at hlow
  have hlow' := EReal.coe_le_coe_iff.mp hlow
  refine ⟨by dsimp only [C] at *; linarith, ?_⟩
  rw [mem_fiberSubdifferential_iff,
    ConvexAnalysis.subgradient_iff_conjugate_eq (f := fun y => (F y : WithTop ℝ))
      (x := z) (r := F z) rfl]
  change F z + C.toReal - inner ℝ w z = 0 ↔
    ConvexAnalysis.Specs.conjugate (fun y => (F y : WithTop ℝ)) (innerSL ℝ w) =
      ((inner ℝ w z - F z : ℝ) : EReal)
  rw [← pointwise_conjugate_eq (fun _ : Unit => F) () w]
  change F z + C.toReal - inner ℝ w z = 0 ↔ C = ((inner ℝ w z - F z : ℝ) : EReal)
  rw [← hC, EReal.coe_eq_coe_iff]
  simp only [EReal.toReal_coe]
  constructor <;> intro h <;> linarith

end VariationalNotes.Flux.ConstitutiveRelation

namespace VariationalNotes.Flux.ConstitutiveRelation
open Sobolev WeakDivergenceSpec IntegralConjugacySpecs ConstitutiveRelationSpecs

/-- The already proved attainment and equality of values supply the global
step; all pointwise assertions concern the original finite integrand. -/
theorem domain_optimality {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (hp : 1 < p.real) (F : Ω → Vector d → ℝ)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ)
    (hdual : DirichletDualitySpecs.DomainConclusion Ω p hp F ℓ) :
    DomainOptimality Ω p hp F ℓ := by
  obtain ⟨hJ, hC, _, m, u₀, σ₀, hu₀, hmin, hσ₀, hσ₀val, hmax, _, _⟩ := hdual
  let ν : Measure Ω := volume.comap Subtype.val
  have gap_data (u : W1pZero Ω 1 p) (σ : Flux Ω p hp)
      (hσ : AllVariations Ω p hp σ ℓ) :
      Integrable (gap Ω p hp F u σ) ν ∧
      (∀ᵐ x ∂ν, 0 ≤ gap Ω p hp F u σ x) ∧
      (∫ x, gap Ω p hp F u σ x ∂ν) =
        primalValue Ω p F ℓ u - dualValue Ω p hp F σ := by
    have hpair : Integrable
        (fun x : Ω => inner ℝ (σ x.val) (Primal.gradientMap Ω p u x.val)) ν := by
      have hi := (WeakDivergence.adjoint_formula Ω p hp σ u).1
      rw [← DirichletDuality.gradientMap_eq] at hi
      exact (integrableOn_iff_comap_subtypeVal Ω.isOpen.measurableSet).mp hi
    have hpairval : (∫ x : Ω, inner ℝ (σ x.val)
        (Primal.gradientMap Ω p u x.val) ∂ν) = ℓ u := by
      exact (integral_subtype_comap Ω.isOpen.measurableSet
        (fun x : Domain d => inner ℝ (σ x) (Primal.gradientMap Ω p u x))).trans (by
          simpa only [DirichletDuality.gradientMap_eq] using hσ u)
    have hi : Integrable (gap Ω p hp F u σ) ν := ((hJ u).add (hC σ).2).sub hpair
    refine ⟨hi, ?_, ?_⟩
    · filter_upwards [(hC σ).1] with x hx
      exact (pointwise_gap (F x) (Primal.gradientMap Ω p u x.val) (σ x.val) hx.1 hx.2).1
    · calc
        (∫ x, gap Ω p hp F u σ x ∂ν) =
            (∫ x : Ω, F x (Primal.gradientMap Ω p u x.val) +
              (IntegralConjugacySpecs.pointwiseConjugate F x (σ x.val)).toReal ∂ν) -
              (∫ x : Ω, inner ℝ (σ x.val) (Primal.gradientMap Ω p u x.val) ∂ν) :=
          integral_sub ((hJ u).add (hC σ).2) hpair
        _ = _ := by
          have hadd : (∫ x : Ω, F x (Primal.gradientMap Ω p u x.val) +
              (IntegralConjugacySpecs.pointwiseConjugate F x (σ x.val)).toReal ∂ν) =
              (∫ x : Ω, F x (Primal.gradientMap Ω p u x.val) ∂ν) +
              (∫ x : Ω, (IntegralConjugacySpecs.pointwiseConjugate F x (σ x.val)).toReal ∂ν) :=
            integral_add (hJ u) (hC σ).2
          rw [hadd, hpairval]
          unfold primalValue dualValue
          dsimp only [ν]
          ring
  intro u σ hσ
  obtain ⟨hi, hn, he⟩ := gap_data u σ hσ
  have hz : (∫ x, gap Ω p hp F u σ x ∂ν) = 0 ↔
      ∀ᵐ x ∂ν, gap Ω p hp F u σ x = 0 :=
    integral_eq_zero_iff_of_nonneg_ae hn hi
  have hfen : (∫ x, gap Ω p hp F u σ x ∂ν) = 0 ↔
      ∀ᵐ x : Ω ∂ν, F x (Primal.gradientMap Ω p u x.val) +
        (IntegralConjugacySpecs.pointwiseConjugate F x (σ x.val)).toReal =
          inner ℝ (σ x.val) (Primal.gradientMap Ω p u x.val) := by
    simpa only [gap, sub_eq_zero] using hz
  have hsub : (∫ x, gap Ω p hp F u σ x ∂ν) = 0 ↔
      ∀ᵐ x ∂ν, σ x.val ∈ fiberSubdifferential (F x) (Primal.gradientMap Ω p u x.val) := by
    apply hz.trans
    apply Filter.eventually_congr
    filter_upwards [(hC σ).1] with x hx
    exact (pointwise_gap (F x) (Primal.gradientMap Ω p u x.val) (σ x.val) hx.1 hx.2).2
  refine ⟨hi, hn, he, integral_nonneg_of_ae hn, hfen, hsub, ?_⟩
  rw [← hsub, he]
  constructor
  · rintro ⟨humin, hσmax⟩
    have h₁ := humin u₀
    have h₂ := hσmax σ₀ hσ₀
    have h₃ := hmin u
    have h₄ := hmax σ hσ
    change primalValue Ω p F ℓ u₀ = m at hu₀
    change dualValue Ω p hp F σ₀ = m at hσ₀val
    change m ≤ primalValue Ω p F ℓ u at h₃
    change dualValue Ω p hp F σ ≤ m at h₄
    linarith
  · intro hzero
    constructor
    · intro v
      have hb := integral_nonneg_of_ae (gap_data v σ hσ).2.1
      rw [(gap_data v σ hσ).2.2] at hb
      linarith
    · intro τ hτ
      have hb := integral_nonneg_of_ae (gap_data u τ hτ).2.1
      rw [(gap_data u τ hτ).2.2] at hb
      linarith

/-- Proposition `prop:optimal-flux`, general assertion and its complete gap
criterion, under exactly the Dirichlet–flux hypotheses. -/
theorem optimal_flux : ConstitutiveRelationSpecs.OptimalFlux := by
  intro d hd Ω hΩ p hp F ℓ hF a₀ a₁ a h₀ h₁ ha hapos hg hc
  exact domain_optimality Ω p hp F ℓ
    (DirichletDuality.dirichlet_flux hd Ω hΩ p hp F ℓ hF a₀ a₁ a h₀ h₁ ha hapos hg hc)

end VariationalNotes.Flux.ConstitutiveRelation
