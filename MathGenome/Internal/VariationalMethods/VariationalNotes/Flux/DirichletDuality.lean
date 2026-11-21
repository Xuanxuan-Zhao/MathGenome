import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.DirichletDuality
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.PrimalAttainment
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.WeakDivergence
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.IntegralConjugacy
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.BanachFenchel

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Flux
namespace DirichletDuality
open ConvexAnalysis

/-- The load has zero conjugate at -ℓ and infinite conjugate elsewhere. -/
theorem negativeLoad_conjugate : DirichletDualitySpecs.NegativeLoadConjugate.{u} := by
  intro X _ _ ℓ q
  classical
  split_ifs with he
  · subst q
    apply le_antisymm
    · apply iSup₂_le
      intro x hx
      change (((-ℓ x - (-ℓ x) : ℝ)) : EReal) ≤ 0
      simp
    · simpa using (conjugate_finite_lower_bound
        (fun u => ((-ℓ u : ℝ) : WithTop ℝ)) (0 : X) 0 (by simp) (-ℓ))
  · have hn : ∃ x, q x + ℓ x ≠ 0 := by
      by_contra! h
      apply he
      ext x
      simpa using (eq_neg_of_add_eq_zero_left (h x))
    obtain ⟨x, hx⟩ := hn
    apply (EReal.eq_top_iff_forall_lt _).mpr
    intro r
    let t := (r + 1) / (q x + ℓ x)
    have hv : q (t • x) - -ℓ (t • x) = r + 1 := by
      simp only [map_smul, smul_eq_mul, sub_neg_eq_add]
      rw [← mul_add]
      exact div_mul_cancel₀ _ hx
    have h := conjugate_finite_lower_bound
      (fun u => ((-ℓ u : ℝ) : WithTop ℝ)) (t • x) (-ℓ (t • x)) rfl q
    rw [hv] at h
    exact (EReal.coe_lt_coe_iff.mpr (by linarith : r < r + 1)).trans_le h

/-- Finite real convex functions agree with the shared epigraph convention. -/
theorem convex_coe {X : Type*} [AddCommGroup X] [Module ℝ X]
    {G : X → ℝ} (hG : ConvexOn ℝ univ G) :
    IsConvex (fun x => (G x : WithTop ℝ)) := by
  apply (convex_iff_twoPoint _).mpr
  intro x y r s hr hs a b ha hb hab
  have hr' := WithTop.coe_injective hr
  have hs' := WithTop.coe_injective hs
  apply WithTop.coe_le_coe.mpr
  simpa only [hr', hs', smul_eq_mul] using hG.2 (mem_univ x) (mem_univ y) ha hb hab

/-- Qualification needs a finite infimum and continuity of G, with no
minimizing point among its hypotheses. -/
theorem qualified_dual {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (ℓ : X →L[ℝ] ℝ) (G : Y → ℝ)
    (hc : ConvexOn ℝ univ G) (hcont : Continuous G) (m : ℝ)
    (hm : (⨅ x, ((G (A x) - ℓ x : ℝ) : EReal)) = (m : EReal)) :
    ∃ y : Y →L[ℝ] ℝ, y.comp A = ℓ ∧
      -Specs.conjugate (fun z => (G z : WithTop ℝ)) y = (m : EReal) ∧
      ∀ z : Y →L[ℝ] ℝ, z.comp A = ℓ →
        -Specs.conjugate (fun w => (G w : WithTop ℝ)) z ≤ (m : EReal) := by
  let f : X → WithTop ℝ := fun x => (-ℓ x : ℝ)
  let g : Y → WithTop ℝ := fun y => G y
  have hfc : IsConvex f := convex_coe ((-ℓ).toLinearMap.convexOn convex_univ)
  have hgc : IsConvex g := convex_coe hc
  have hi : (⨅ x, Specs.toEReal (f x + g (A x))) = (m : EReal) := by
    convert hm using 1
    congr 1
    funext x
    change ((-ℓ x + G (A x) : ℝ) : EReal) = _
    congr 1
    ring
  obtain ⟨⟨y, hy, hb⟩, _⟩ := Ch04.banach_fenchel A f g
    ⟨0, WithTop.coe_lt_top _⟩ hfc ⟨0, WithTop.coe_lt_top _⟩ hgc
    ⟨0, WithTop.coe_lt_top _, WithTop.coe_lt_top _,
      (WithTop.continuous_coe.comp hcont).continuousAt⟩ m hi
  have he : y.comp A = ℓ := by
    by_contra hn
    have hn' : -(y.comp A) ≠ -ℓ := fun h => hn (neg_injective h)
    have ht := negativeLoad_conjugate ℓ (-(y.comp A))
    rw [ite_eq_right hn'] at ht
    change -Specs.conjugate f (-(y.comp A)) - Specs.conjugate g y = _ at hy
    rw [ht] at hy
    simp at hy
  refine ⟨y, he, ?_, ?_⟩
  · have hz := negativeLoad_conjugate ℓ (-(y.comp A))
    rw [he, ite_eq_left rfl] at hz
    rw [he, hz] at hy
    simpa using hy
  · intro z hz
    have ht := negativeLoad_conjugate ℓ (-(z.comp A))
    rw [hz, ite_eq_left rfl] at ht
    have h := hb z
    rw [hz, ht] at h
    simpa using h


open Sobolev WeakDivergenceSpec

/-- The two upstream interfaces use the same one-row weak gradient. -/
theorem gradientMap_eq {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) :
    Primal.gradientMap Ω p = WeakDivergenceSpec.gradientMap Ω p := by
  have hr : Primal.rowIsometry d = WeakDivergenceSpec.rowIsometry d := by
    ext z j
    rfl
  ext v
  simp only [Primal.gradientMap, WeakDivergenceSpec.gradientMap, hr,
    ContinuousLinearMap.comp_apply]
  rfl

/-- Assembly on restricted Lebesgue measure, before changing to Ω-indexed data. -/
theorem ambient_duality {d : ℕ} (hd : 0 < d) (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent) (hp : 1 < p.real)
    (F : Domain d → Vector d → ℝ) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ)
    (hF : Sobolev.Caratheodory (domainMeasure Ω) F)
    (hg : TwoSidedPGrowth (domainMeasure Ω) p.ennreal F)
    (hc : ∀ᵐ x ∂domainMeasure Ω, ConvexOn ℝ univ (F x)) :
    let J := Primal.objective Ω p F ℓ
    let H := fun σ : Flux Ω p hp =>
      -(∫ x, (IntegralConjugacySpecs.pointwiseConjugate F x (σ x)).toReal ∂domainMeasure Ω)
    (∀ σ : Flux Ω p hp,
      (∀ᵐ x ∂domainMeasure Ω, IntegralConjugacySpecs.pointwiseConjugate F x (σ x) ≠ ⊤ ∧
        IntegralConjugacySpecs.pointwiseConjugate F x (σ x) ≠ ⊥) ∧
      Integrable (fun x => (IntegralConjugacySpecs.pointwiseConjugate F x (σ x)).toReal)
        (domainMeasure Ω)) ∧
    ∃ (u : W1pZero Ω 1 p) (σ : Flux Ω p hp),
      IsGLB (range J) (J u) ∧ AllVariations Ω p hp σ ℓ ∧ H σ = J u ∧
      ∀ τ : Flux Ω p hp, AllVariations Ω p hp τ ℓ → H τ ≤ J u := by
  dsimp only
  let J := Primal.objective Ω p F ℓ
  let G := integralFunctional (p := p.ennreal) (domainMeasure Ω) F
  have hclosed : IsClosed (zeroSubmodule Ω 1 p : Set (W1p Ω 1 p)) :=
    (smoothSubmodule Ω 1 p).isClosed_topologicalClosure
  haveI : IsClosed (zeroSubmodule Ω 1 p : Set (W1p Ω 1 p)) := hclosed
  obtain ⟨a₀, a₁, a, h₀, h₁, ha, hapos, hgr⟩ := hg
  have hgr' : ∀ᵐ x ∂domainMeasure Ω, ∀ z,
      a₀ * ‖z‖ ^ p.real - a x ≤ F x z ∧ F x z ≤ a x + a₁ * ‖z‖ ^ p.real := by
    simpa only [Exponent.toReal] using hgr
  obtain ⟨_, _, _, _, _, _, _, _, u, hu⟩ := primal_attainment_ambient hd Ω hΩ p hp F ℓ
    hF a₀ a₁ a h₀ h₁ ha hapos hgr' hc
  have hg : TwoSidedPGrowth (domainMeasure Ω) p.ennreal F :=
    ⟨a₀, a₁, a, h₀, h₁, ha, hapos, hgr⟩
  letI : Fact (1 ≤ ENNReal.ofReal p.real) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  letI : Fact (1 ≤ ENNReal.ofReal (p.real / (p.real - 1))) :=
    ⟨ENNReal.one_le_ofReal.mpr (Real.HolderConjugate.conjExponent hp).symm.lt.le⟩
  obtain ⟨_, hGc, hGcont, T, hT, hconj⟩ := euclidean_integral_conjugacy d hd
    (Ω : Set (Domain d)) Ω.isOpen.measurableSet hΩ.measure_lt_top p.real hp F hF hg hc
  have hmin : ∀ v, J u ≤ J v := fun v => hu.1 ⟨v, rfl⟩
  have hinf : (⨅ v, ((G (WeakDivergenceSpec.gradientMap Ω p v) - ℓ v : ℝ) : EReal)) =
      (J u : EReal) := by
    have he (v : W1pZero Ω 1 p) : G (WeakDivergenceSpec.gradientMap Ω p v) - ℓ v = J v := by
      rw [← gradientMap_eq]
      rfl
    simp only [he]
    exact le_antisymm (iInf_le _ u) (le_iInf fun v => EReal.coe_le_coe_iff.mpr (hmin v))
  obtain ⟨y, hy, hyval, hybound⟩ := qualified_dual
    (WeakDivergenceSpec.gradientMap Ω p) ℓ G hGc hGcont (J u) hinf
  let σ := T.symm y
  have hTy : T σ = y := T.apply_symm_apply y
  have hadj (τ : Flux Ω p hp) : fluxAdjoint Ω p hp τ = (T τ).comp (WeakDivergenceSpec.gradientMap Ω p) := by
    ext v
    exact (WeakDivergence.adjoint_formula Ω p hp τ v).2.trans (hT τ _).symm
  have hfeas (τ : Flux Ω p hp) : AllVariations Ω p hp τ ℓ ↔
      (T τ).comp (WeakDivergenceSpec.gradientMap Ω p) = ℓ := by
    rw [← hadj]
    exact (WeakDivergence.constraint_equivalences d hd Ω hΩ p hp ℓ τ).1.symm
  have hval (τ : Flux Ω p hp) :
      -Specs.conjugate (fun v => (G v : WithTop ℝ)) (T τ) =
        ((-(∫ x, (IntegralConjugacySpecs.pointwiseConjugate F x (τ x)).toReal
          ∂domainMeasure Ω) : ℝ) : EReal) := by
    exact (congrArg Neg.neg (hconj τ).2.2.2).trans (EReal.coe_neg _).symm
  refine ⟨fun τ => ⟨(hconj τ).2.1, (hconj τ).2.2.1⟩,
    u, σ, hu, (hfeas σ).mpr (by rw [hTy]; exact hy), ?_, ?_⟩
  · apply EReal.coe_injective
    rw [← hval, hTy]
    exact hyval
  · intro τ hτ
    apply EReal.coe_le_coe_iff.mp
    rw [← hval]
    exact hybound (T τ) ((hfeas τ).mp hτ)

/-- Domain assembly for a measurable version of the integrand. -/
private theorem dirichlet_flux_measurable :
  ∀ {d : ℕ}, 0 < d → ∀ (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent) (hp : 1 < p.real)
    (F : Ω → Vector d → ℝ) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ),
    Sobolev.CaratheodorySpecs.Caratheodory (volume.comap Subtype.val) F →
  ∀ (a₀ a₁ : ℝ) (a : Ω → ℝ), 0 < a₀ → 0 ≤ a₁ →
    Integrable a (volume.comap Subtype.val) →
    (∀ᵐ x ∂(volume.comap Subtype.val), 0 ≤ a x) →
    (∀ᵐ x ∂(volume.comap Subtype.val), ∀ z,
      a₀ * ‖z‖ ^ p.real - a x ≤ F x z ∧ F x z ≤ a x + a₁ * ‖z‖ ^ p.real) →
    (∀ᵐ x ∂(volume.comap Subtype.val), ConvexOn ℝ univ (F x)) →
    DirichletDualitySpecs.DomainConclusion Ω p hp F ℓ := by
  classical
  intro d hd Ω hΩ p hp F ℓ hF a₀ a₁ a h₀ h₁ ha hapos hg hc
  let ν : Measure Ω := volume.comap Subtype.val
  let Fₑ := Primal.extendFromDomain Ω F
  let aₑ := Primal.extendFromDomain Ω a
  have hm := Ω.isOpen.measurableSet
  have hEmb := MeasurableEmbedding.subtype_coe hm
  have hmap : Measure.map (fun x : Ω => x.val) ν = domainMeasure Ω :=
    map_comap_subtype_coe hm volume
  have hint (g : Domain d → ℝ) :
      (∫ x : Ω, g x.val ∂ν) = ∫ x, g x ∂domainMeasure Ω :=
    integral_subtype_comap hm g
  have haₑ : Integrable aₑ (domainMeasure Ω) := by
    rw [← hmap]
    apply hEmb.integrable_map_iff.mpr
    change Integrable (fun x : Ω => aₑ x.val) ν
    simpa only [aₑ, extendFromDomain_apply] using ha
  have haposₑ : ∀ᵐ x ∂domainMeasure Ω, 0 ≤ aₑ x := by
    apply (ae_restrict_iff_subtype hm).mpr
    change ∀ᵐ x : Ω ∂ν, 0 ≤ aₑ x.val
    simpa only [aₑ, extendFromDomain_apply] using hapos
  have hgₑ : ∀ᵐ x ∂domainMeasure Ω, ∀ z,
      a₀ * ‖z‖ ^ p.ennreal.toReal - aₑ x ≤ Fₑ x z ∧
      Fₑ x z ≤ aₑ x + a₁ * ‖z‖ ^ p.ennreal.toReal := by
    apply (ae_restrict_iff_subtype hm).mpr
    change ∀ᵐ x : Ω ∂ν, ∀ z,
      a₀ * ‖z‖ ^ p.ennreal.toReal - aₑ x.val ≤ Fₑ x.val z ∧
      Fₑ x.val z ≤ aₑ x.val + a₁ * ‖z‖ ^ p.ennreal.toReal
    simpa only [aₑ, Fₑ, extendFromDomain_apply, Exponent.toReal] using hg
  have hcₑ : ∀ᵐ x ∂domainMeasure Ω, ConvexOn ℝ univ (Fₑ x) := by
    apply (ae_restrict_iff_subtype hm).mpr
    change ∀ᵐ x : Ω ∂ν, ConvexOn ℝ univ (Fₑ x.val)
    simpa only [Fₑ, extendFromDomain_apply] using hc
  have hFₑ := extendFromDomain_caratheodory Ω hF
  have hGrowth : TwoSidedPGrowth (domainMeasure Ω) p.ennreal Fₑ :=
    ⟨a₀, a₁, aₑ, h₀, h₁, haₑ, haposₑ, hgₑ⟩
  obtain ⟨hconj, u, σ, hglb, hσ, hval, hbound⟩ :=
    ambient_duality hd Ω hΩ p hp Fₑ ℓ hFₑ hGrowth hcₑ
  let J := fun v : W1pZero Ω 1 p =>
    (∫ x : Ω, F x (Primal.gradientMap Ω p v x.val) ∂ν) - ℓ v
  let H := fun τ : Flux Ω p hp =>
    -(∫ x : Ω, (IntegralConjugacySpecs.pointwiseConjugate F x (τ x.val)).toReal ∂ν)
  have hJ : Primal.objective Ω p Fₑ ℓ = J := by
    funext v
    change (∫ x, Fₑ x (Primal.gradientMap Ω p v x) ∂domainMeasure Ω) - ℓ v = _
    rw [← hint]
    simp only [Fₑ, extendFromDomain_apply]
    rfl
  have hpoint (x : Ω) (w : Vector d) :
      IntegralConjugacySpecs.pointwiseConjugate Fₑ x.val w =
        IntegralConjugacySpecs.pointwiseConjugate F x w := by
    unfold IntegralConjugacySpecs.pointwiseConjugate
    simp only [Fₑ, extendFromDomain_apply]
  have hH (τ : Flux Ω p hp) :
      -(∫ x, (IntegralConjugacySpecs.pointwiseConjugate Fₑ x (τ x)).toReal
        ∂domainMeasure Ω) = H τ := by
    rw [← hint]
    simp only [hpoint]
    rfl
  rw [hJ] at hglb hval hbound
  simp only [hH] at hval hbound
  unfold DirichletDualitySpecs.DomainConclusion
  dsimp only
  refine ⟨?_, ?_, ?_, J u, u, σ, rfl, fun v => hglb.1 ⟨v, rfl⟩,
    hσ, hval, hbound, hglb, ?_⟩
  · intro v
    let g : Domain d → ℝ := fun x => Fₑ x (Primal.gradientMap Ω p v x)
    have hi : Integrable g (domainMeasure Ω) := integrable_substitution (ne_of_gt (ENNReal.ofReal_pos.mpr p.pos))
      ENNReal.ofReal_ne_top hFₑ hGrowth (Lp.memLp (Primal.gradientMap Ω p v))
    rw [← hmap] at hi
    have hi' := hEmb.integrable_map_iff.mp hi
    change Integrable (fun x : Ω => Fₑ x.val (Primal.gradientMap Ω p v x.val)) ν at hi'
    simpa only [Fₑ, extendFromDomain_apply] using hi'
  · intro τ
    refine ⟨?_, ?_⟩
    · have hf := (ae_restrict_iff_subtype hm).mp (hconj τ).1
      change ∀ᵐ x : Ω ∂ν,
        IntegralConjugacySpecs.pointwiseConjugate Fₑ x.val (τ x.val) ≠ ⊤ ∧
        IntegralConjugacySpecs.pointwiseConjugate Fₑ x.val (τ x.val) ≠ ⊥ at hf
      simpa only [hpoint] using hf
    · let g : Domain d → ℝ := fun x =>
        (IntegralConjugacySpecs.pointwiseConjugate Fₑ x (τ x)).toReal
      have hi : Integrable g (domainMeasure Ω) := (hconj τ).2
      rw [← hmap] at hi
      have hi' := hEmb.integrable_map_iff.mp hi
      change Integrable (fun x : Ω =>
        (IntegralConjugacySpecs.pointwiseConjugate Fₑ x.val (τ x.val)).toReal) ν at hi'
      simpa only [hpoint] using hi'
  · intro τ
    obtain ⟨_, h₁, h₂⟩ := WeakDivergence.constraint_equivalences d hd Ω hΩ p hp ℓ τ
    exact h₁.trans h₂
  · constructor
    · rintro b ⟨τ, hτ, rfl⟩
      exact hbound τ hτ
    · intro b hb
      rw [← hval]
      exact hb ⟨σ, hσ, rfl⟩

/-- The original Dirichlet–flux theorem for Lebesgue-measurable sections.
A single measurable version agrees in every fiber outside one null set. Thus
both objectives, including the pointwise conjugate, remain those of F. -/
theorem dirichlet_flux : DirichletDualitySpecs.DirichletFlux := by
  classical
  intro d hd Ω hΩ p hp F ℓ hF a₀ a₁ a h₀ h₁ ha hapos hg hc
  obtain ⟨G, hm, hcont, hGF⟩ := caratheodory_measurable_version hF.1 hF.2
  have hgG : ∀ᵐ x ∂(volume.comap Subtype.val), ∀ z,
      a₀ * ‖z‖ ^ p.real - a x ≤ G x z ∧ G x z ≤ a x + a₁ * ‖z‖ ^ p.real := by
    filter_upwards [hg, hGF] with x hx hgx
    simpa only [hgx] using hx
  have hcG : ∀ᵐ x ∂(volume.comap Subtype.val), ConvexOn ℝ univ (G x) := by
    filter_upwards [hc, hGF] with x hx hgx
    simpa only [funext hgx] using hx
  have heJ (u : W1pZero Ω 1 p) :
      (fun x : Ω => G x (Primal.gradientMap Ω p u x.val)) =ᵐ[volume.comap Subtype.val]
      (fun x : Ω => F x (Primal.gradientMap Ω p u x.val)) :=
    hGF.mono (fun x hx => hx (Primal.gradientMap Ω p u x.val))
  have heC (σ : Flux Ω p hp) :
      (fun x : Ω => IntegralConjugacySpecs.pointwiseConjugate G x (σ x.val))
        =ᵐ[volume.comap Subtype.val]
      (fun x : Ω => IntegralConjugacySpecs.pointwiseConjugate F x (σ x.val)) := by
    filter_upwards [hGF] with x hx
    unfold IntegralConjugacySpecs.pointwiseConjugate
    simp only [hx]
  have hJ (u : W1pZero Ω 1 p) :
      (∫ x : Ω, G x (Primal.gradientMap Ω p u x.val) ∂(volume.comap Subtype.val)) - ℓ u =
      (∫ x : Ω, F x (Primal.gradientMap Ω p u x.val) ∂(volume.comap Subtype.val)) - ℓ u :=
    congrArg (fun t : ℝ => t - ℓ u) (integral_congr_ae (heJ u))
  have hH (σ : Flux Ω p hp) :
      -(∫ x : Ω, (IntegralConjugacySpecs.pointwiseConjugate G x (σ x.val)).toReal
        ∂(volume.comap Subtype.val)) =
      -(∫ x : Ω, (IntegralConjugacySpecs.pointwiseConjugate F x (σ x.val)).toReal
        ∂(volume.comap Subtype.val)) := by
    apply congrArg Neg.neg
    apply integral_congr_ae
    filter_upwards [heC σ] with x hx
    rw [hx]
  have hresult := dirichlet_flux_measurable hd Ω hΩ p hp G ℓ
    ⟨hm, hcont⟩ a₀ a₁ a h₀ h₁ ha hapos hgG hcG
  unfold DirichletDualitySpecs.DomainConclusion at hresult ⊢
  dsimp only at hresult ⊢
  refine ⟨fun u => (hresult.1 u).congr (heJ u), ?_, hresult.2.2.1, ?_⟩
  · intro σ
    refine ⟨?_, (hresult.2.1 σ).2.congr ((heC σ).fun_comp EReal.toReal)⟩
    filter_upwards [(hresult.2.1 σ).1, heC σ] with x hx he
    simpa only [← he] using hx
  · simpa only [hJ, hH] using hresult.2.2.2

end DirichletDuality
end VariationalNotes.Flux

