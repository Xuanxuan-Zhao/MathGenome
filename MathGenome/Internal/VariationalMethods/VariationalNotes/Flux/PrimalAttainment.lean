import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.PrimalAttainment
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.IntegralRegularity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.SlabPoincare
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.ReflexiveDirectMethod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Sequences

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TopologicalSpace Set Filter
open scoped Topology ENNReal
namespace VariationalNotes.Flux
open Sobolev Primal

theorem scalar_gradient_norm {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (u : W1pZero Ω 1 p) : ‖gradientMap Ω p u‖ = ‖gradient Ω 1 p u.val‖ := by
  simp only [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [((rowIsometry d).toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL
    (gradient Ω 1 p u.val)] with x hx
  rw [show gradientMap Ω p u x = rowIsometry d (gradient Ω 1 p u.val x) from hx]
  exact (rowIsometry d).norm_map _

/-- A positive superlinear power dominates every linear perturbation. -/
theorem tendsto_power_sub_linear {p a₀ : ℝ} (hp : 1 < p) (ha₀ : 0 < a₀)
    (C A : ℝ) : Tendsto (fun t : ℝ => a₀ * t ^ p - C * t - A) atTop atTop := by
  have hpow := (tendsto_rpow_atTop (sub_pos.mpr hp)).const_mul_atTop ha₀
  have hsub : Tendsto (fun t : ℝ => a₀ * t ^ (p-1) - C) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-C) hpow
  have hprod := tendsto_id.atTop_mul_atTop₀ hsub
  have hfinal := tendsto_atTop_add_const_right atTop (-A) hprod
  apply hfinal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht' : t * t ^ (p-1) = t ^ p := by
    calc
      t * t ^ (p-1) = t ^ (1 : ℝ) * t ^ (p-1) := by rw [Real.rpow_one]
      _ = t ^ (1 + (p-1)) := (Real.rpow_add ht _ _).symm
      _ = t ^ p := by congr 1; ring
  dsimp
  rw [mul_sub, ← mul_assoc, mul_comm t a₀, mul_assoc, ht']
  ring

/-- The usual closed-convex-sublevel argument, for finite real objectives. -/
theorem finite_weak_lsc {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {J : X → ℝ} (hc : ConvexOn ℝ univ J) (hJ : Continuous J) :
    ConvexAnalysis.Specs.IsLowerSemicontinuous
      (fun u : WeakSpace ℝ X => (J ((toWeakSpace ℝ X).symm u) : WithTop ℝ)) := by
  apply ConvexAnalysis.convex_normLowerSemicontinuous_isWeaklyLowerSemicontinuous
    (fun x : X => (J x : WithTop ℝ))
  · apply (ConvexAnalysis.convex_iff_twoPoint _).mpr
    intro x y r s hr hs a b ha hb hab
    have hr' : J x = r := WithTop.coe_injective hr
    have hs' : J y = s := WithTop.coe_injective hs
    apply WithTop.coe_le_coe.mpr
    simpa only [hr', hs', smul_eq_mul] using hc.2 (mem_univ x) (mem_univ y) ha hb hab
  · exact (ConvexAnalysis.lowerSemicontinuous_iff_native _).mpr
      ((WithTop.continuous_coe.comp hJ).lowerSemicontinuous)

/-- Apply the accepted reflexive direct method to a finite objective. -/
theorem minimum_of_convex_coercive {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : Existence.Specs.IsReflexive X) (J : X → ℝ)
    (hc : ConvexOn ℝ univ J) (hJ : Continuous J)
    (hb : ∃ b : ℝ, ∀ x, b ≤ J x)
    (hco : Existence.Specs.CoerciveOn (fun x => (J x : WithTop ℝ)) univ) :
    ∃ x, IsGLB (range J) (J x) := by
  have hw := finite_weak_lsc hc hJ
  have hwe : LowerSemicontinuous
      (fun u : WeakSpace ℝ X => (J ((toWeakSpace ℝ X).symm u) : EReal)) := by
    exact WithBot.continuous_coe.comp_lowerSemicontinuous
      ((ConvexAnalysis.lowerSemicontinuous_iff_native _).mp hw)
      (fun _ _ h => WithBot.coe_le_coe.mpr h)
  have hseq : Existence.Specs.WeakSequentialLowerSemicontinuousOn
      (fun x => (J x : WithTop ℝ)) univ := by
    intro a x _ _ ha
    apply (le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
    intro b hb
    exact ha.eventually (hwe (toWeakSpace ℝ X x) b hb)
  obtain ⟨x, _, m, hm, hglb⟩ := Existence.reflexive_direct_method hX
    (fun x => (J x : WithTop ℝ)) univ ⟨0, mem_univ _⟩
    (fun _ _ _ _ => mem_univ _) ⟨⟨0, mem_univ _⟩, WithTop.coe_lt_top _⟩
    (by obtain ⟨b, hb⟩ := hb; exact ⟨b, fun x _ => WithTop.coe_le_coe.mpr (hb x)⟩)
    hco hseq
  have hm' : J x = m := WithTop.coe_injective hm
  refine ⟨x, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    rw [hm']
    exact WithTop.coe_le_coe.mp (hglb.1 ⟨y, mem_univ _, rfl⟩)
  · intro b hb
    rw [hm']
    apply WithTop.coe_le_coe.mp
    apply hglb.2
    rintro _ ⟨y, _, rfl⟩
    exact WithTop.coe_le_coe.mpr (hb ⟨y, rfl⟩)

/-- Bounded openness supplies a coordinate strip and hence a full-norm bound. -/
theorem bounded_gradient_control {d : ℕ} (hd : 0 < d) (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : W1pZero Ω 1 p, ‖u‖ ≤ K * ‖gradientMap Ω p u‖ := by
  obtain ⟨R, hR, hbound⟩ := hΩ.exists_pos_norm_lt
  let j : Fin d := ⟨0, hd⟩
  have hs : InCoordinateStrip Ω j (-R) R := by
    intro x hx
    have hcoord : |x j| < R := (PiLp.norm_apply_le x j).trans_lt (hbound x hx)
    exact abs_lt.mp hcoord
  refine ⟨R - (-R) + 1, by linarith, ?_⟩
  intro u
  rw [scalar_gradient_norm]
  exact (slab_norm_equivalence Ω p j (-R) R (by linarith) hs u).2

/-- The integrated lower growth bound, with the L¹ norm of the error term. -/
theorem integralFunctional_lower_bound {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure S} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {F : S → E → ℝ} (hF : Sobolev.Caratheodory μ F)
    {a₀ a₁ : ℝ} {a : S → ℝ} (h₀ : 0 < a₀) (h₁ : 0 ≤ a₁)
    (ha : Integrable a μ) (hapos : ∀ᵐ x ∂μ, 0 ≤ a x)
    (hg : ∀ᵐ x ∂μ, ∀ z, a₀ * ‖z‖ ^ p.toReal - a x ≤ F x z ∧
      F x z ≤ a x + a₁ * ‖z‖ ^ p.toReal) (v : Lp E p μ) :
    a₀ * ‖v‖ ^ p.toReal - (∫ x, ‖a x‖ ∂μ) ≤ integralFunctional μ F v := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hin := (Lp.memLp v).integrable_norm_rpow hp₀ hp
  have hInt : a₀ * ‖v‖ ^ p.toReal - (∫ x, a x ∂μ) ≤ integralFunctional μ F v := by
    calc
      _ = ∫ x, a₀ * ‖v x‖ ^ p.toReal - a x ∂μ := by
        rw [integral_sub (hin.const_mul a₀) ha, integral_const_mul,
          integral_norm_rpow hp₀ hp]
      _ ≤ _ := integral_mono_ae ((hin.const_mul a₀).sub ha)
        (integrable_substitution hp₀ hp hF ⟨a₀, a₁, a, h₀, h₁, ha, hapos, hg⟩ (Lp.memLp v))
        (hg.mono fun x hx => (hx (v x)).1)
  have haInt : (∫ x, a x ∂μ) ≤ ∫ x, ‖a x‖ ∂μ :=
    integral_mono_ae ha ha.norm (Eventually.of_forall fun x => le_abs_self (a x))
  linarith

/-- The full primal part of the manuscript's Dirichlet–flux theorem. -/
theorem primal_attainment_ambient : PrimalExpected.AmbientAttainment := by
  intro d hd Ω hΩ p hp F ℓ hF a₀ a₁ a h₀ h₁ ha hapos hg hc
  let D := gradientMap Ω p
  let J := objective Ω p F ℓ
  let A := ∫ x, ‖a x‖ ∂domainMeasure Ω
  have hp₀ : p.ennreal ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one
    (Fact.out : 1 ≤ p.ennreal))
  have hpTop : p.ennreal ≠ ∞ := ENNReal.ofReal_ne_top
  have hg' : ∀ᵐ x ∂domainMeasure Ω, ∀ z,
      a₀ * ‖z‖ ^ p.ennreal.toReal - a x ≤ F x z ∧
      F x z ≤ a x + a₁ * ‖z‖ ^ p.ennreal.toReal := by
    simpa only [Exponent.toReal] using hg
  have hGrowth : TwoSidedPGrowth (domainMeasure Ω) p.ennreal F :=
    ⟨a₀, a₁, a, h₀, h₁, ha, hapos, hg'⟩
  have hi (u : W1pZero Ω 1 p) := integrable_substitution hp₀ hpTop hF hGrowth (Lp.memLp (D u))
  have hconvG := convex_integralFunctional hpTop hF hGrowth hc
  have hcontG := continuous_integralFunctional hpTop hF hGrowth hc
  have hconv : ConvexOn ℝ univ J := by
    have hcomp : ConvexOn ℝ univ (fun u => integralFunctional (domainMeasure Ω) F (D u)) := by
      refine ⟨convex_univ, ?_⟩
      intro u _ v _ r s hr hs hrs
      dsimp only
      rw [map_add, map_smul, map_smul]
      exact hconvG.2 (mem_univ _) (mem_univ _) hr hs hrs
    exact hcomp.sub (ℓ.toLinearMap.concaveOn convex_univ)
  have hcont : Continuous J := (hcontG.comp D.continuous).sub ℓ.continuous
  obtain ⟨K, hK, hKbound⟩ := bounded_gradient_control hd Ω hΩ p
  let C := ‖ℓ‖ * K
  have hC : 0 ≤ C := mul_nonneg (ContinuousLinearMap.opNorm_nonneg ℓ) hK.le
  have hbound (u : W1pZero Ω 1 p) :
      a₀ * ‖D u‖ ^ p.real - C * ‖D u‖ - A ≤ J u := by
    have hl := integralFunctional_lower_bound hpTop hF h₀ h₁ ha hapos hg' (D u)
    simp only [Exponent.toReal] at hl
    have hload : ℓ u ≤ C * ‖D u‖ := calc
      ℓ u ≤ ‖ℓ u‖ := le_abs_self _
      _ ≤ ‖ℓ‖ * ‖u‖ := ℓ.le_opNorm u
      _ ≤ ‖ℓ‖ * (K * ‖D u‖) := mul_le_mul_of_nonneg_left (hKbound u) (ContinuousLinearMap.opNorm_nonneg ℓ)
      _ = C * ‖D u‖ := by dsimp [C]; ring
    change _ ≤ integralFunctional (domainMeasure Ω) F (D u) - ℓ u
    linarith
  have hpoly := tendsto_power_sub_linear hp h₀ C A
  have hescape : ∀ b : ℝ, ∃ R : ℝ, ∀ u : W1pZero Ω 1 p, R ≤ ‖u‖ → b ≤ J u := by
    intro b
    obtain ⟨R, hR⟩ := (eventually_atTop.mp (hpoly.eventually_ge_atTop b))
    refine ⟨K * R, ?_⟩
    intro u hu
    have hDu : R ≤ ‖D u‖ := le_of_mul_le_mul_left (hu.trans (hKbound u)) hK
    exact (hR _ hDu).trans (hbound u)
  have hco : Existence.Specs.CoerciveOn (fun u => (J u : WithTop ℝ)) univ := by
    intro b
    obtain ⟨R, hR⟩ := hescape (b + 1)
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R, ?_⟩
    intro u hu
    have hJu : J u ≤ b := WithTop.coe_le_coe.mp hu.2
    by_contra hn
    have := hR u (le_of_not_ge hn)
    linarith
  have hbelow : ∃ b : ℝ, ∀ u : W1pZero Ω 1 p, b ≤ J u := by
    obtain ⟨R, hR⟩ := eventually_atTop.mp (hpoly.eventually_ge_atTop 0)
    refine ⟨-C * max R 0 - A, ?_⟩
    intro u
    by_cases hu : R ≤ ‖D u‖
    · have hnonneg := (hR _ hu).trans (hbound u)
      have hm : 0 ≤ C * max R 0 := mul_nonneg hC (le_max_right _ _)
      have hA : 0 ≤ A := integral_nonneg (fun x => norm_nonneg (a x))
      linarith
    · have hsmall : C * ‖D u‖ ≤ C * max R 0 :=
        mul_le_mul_of_nonneg_left ((le_of_not_ge hu).trans (le_max_left _ _)) hC
      have hpnonneg : 0 ≤ a₀ * ‖D u‖ ^ p.real :=
        mul_nonneg h₀.le (Real.rpow_nonneg (norm_nonneg _) _)
      have := hbound u
      linarith
  have hclosed : IsClosed (zeroSubmodule Ω 1 p : Set (W1p Ω 1 p)) :=
    (smoothSubmodule Ω 1 p).isClosed_topologicalClosure
  haveI : IsClosed (zeroSubmodule Ω 1 p : Set (W1p Ω 1 p)) := hclosed
  have hX : Existence.Specs.IsReflexive (W1pZero Ω 1 p) :=
    ExpandedFA.PartIV.VectorLpReflexive.closed_subspace_reflexive
      (zeroSubmodule Ω 1 p) hclosed (Sobolev.reflexive Ω p hp)
  refine ⟨?_, hconv, hcont, finite_weak_lsc hconv hcont, ⟨C, hC, hbound⟩,
    hescape, hco, hbelow, minimum_of_convex_coercive hX J hconv hcont hbelow hco⟩
  intro u
  refine ⟨hi u, ?_⟩
  have hfinite := lpIntegralEnergy_eq hp₀ hpTop hF hGrowth (D u)
  change Sobolev.lpIntegralEnergy (domainMeasure Ω) F (D u) - (ℓ u : EReal) = (J u : EReal)
  rw [hfinite, ← EReal.coe_sub]
  rfl

@[simp] theorem extendFromDomain_apply {d : ℕ} (Ω : Opens (Domain d))
    {E : Type*} [Zero E] (f : Ω → E) (x : Ω) : extendFromDomain Ω f x.val = f x := by
  classical
  unfold extendFromDomain
  split_ifs with h
  · rfl
  · exact (h x.property).elim

/-- Zero extension of base data imposes no conditions outside the domain. -/
theorem extendFromDomain_caratheodory {d : ℕ} (Ω : Opens (Domain d))
    {F : Ω → Vector d → ℝ}
    (hF : Sobolev.Caratheodory (volume.comap Subtype.val) F) :
    Sobolev.Caratheodory (domainMeasure Ω) (extendFromDomain Ω F) := by
  classical
  refine ⟨?_, ?_⟩
  · intro z
    have h := (hF.1 z).dite
      (show Measurable (fun _ : {x : Domain d // x ∉ Ω} => (0 : ℝ)) from measurable_const)
      Ω.isOpen.measurableSet
    convert h using 1
    funext x
    by_cases hx : x ∈ Ω <;> simp [extendFromDomain, hx]
  · apply (ae_restrict_iff_subtype Ω.isOpen.measurableSet).mpr
    filter_upwards [hF.2] with x hx
    simp only [extendFromDomain_apply]
    convert hx using 1; rfl

/-- Domain transfer for Borel sections, used after constructing a common version. -/
private theorem primal_attainment_measurable {d : ℕ} (hd : 0 < d)
    (Ω : Opens (Domain d)) (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (p : Exponent) (hp : 1 < p.real) (F : Ω → Vector d → ℝ)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ)
    (hF : Sobolev.Caratheodory (volume.comap Subtype.val) F)
    (a₀ a₁ : ℝ) (a : Ω → ℝ) (h₀ : 0 < a₀) (h₁ : 0 ≤ a₁)
    (ha : Integrable a (volume.comap Subtype.val))
    (hapos : ∀ᵐ x ∂(volume.comap Subtype.val), 0 ≤ a x)
    (hg : ∀ᵐ x ∂(volume.comap Subtype.val), ∀ z,
      a₀ * ‖z‖ ^ p.real - a x ≤ F x z ∧ F x z ≤ a x + a₁ * ‖z‖ ^ p.real)
    (hc : ∀ᵐ x ∂(volume.comap Subtype.val), ConvexOn ℝ univ (F x)) :
    PrimalExpected.DomainConclusion Ω p F ℓ a₀ a := by
  classical
  let ν : Measure Ω := volume.comap Subtype.val
  let Fₑ := extendFromDomain Ω F
  let aₑ := extendFromDomain Ω a
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
    simpa only [Function.comp_def, aₑ, extendFromDomain_apply] using ha
  have haposₑ : ∀ᵐ x ∂domainMeasure Ω, 0 ≤ aₑ x := by
    apply (ae_restrict_iff_subtype hm).mpr
    change ∀ᵐ x : Ω ∂ν, 0 ≤ aₑ x.val
    simpa only [aₑ, extendFromDomain_apply] using hapos
  have hgₑ : ∀ᵐ x ∂domainMeasure Ω, ∀ z,
      a₀ * ‖z‖ ^ p.real - aₑ x ≤ Fₑ x z ∧ Fₑ x z ≤ aₑ x + a₁ * ‖z‖ ^ p.real := by
    apply (ae_restrict_iff_subtype hm).mpr
    change ∀ᵐ x : Ω ∂ν, ∀ z,
      a₀ * ‖z‖ ^ p.real - aₑ x.val ≤ Fₑ x.val z ∧
      Fₑ x.val z ≤ aₑ x.val + a₁ * ‖z‖ ^ p.real
    simpa only [aₑ, Fₑ, extendFromDomain_apply] using hg
  have hcₑ : ∀ᵐ x ∂domainMeasure Ω, ConvexOn ℝ univ (Fₑ x) := by
    apply (ae_restrict_iff_subtype hm).mpr
    change ∀ᵐ x : Ω ∂ν, ConvexOn ℝ univ (Fₑ x.val)
    simpa only [Fₑ, extendFromDomain_apply] using hc
  have hnorm : (∫ x, ‖aₑ x‖ ∂domainMeasure Ω) = ∫ x : Ω, ‖a x‖ ∂ν := by
    rw [← hint]
    simp only [aₑ, extendFromDomain_apply]
  obtain ⟨hfinite, hrest⟩ := primal_attainment_ambient hd Ω hΩ p hp Fₑ ℓ
    (extendFromDomain_caratheodory Ω hF) a₀ a₁ aₑ h₀ h₁ haₑ haposₑ hgₑ hcₑ
  rw [hnorm] at hrest
  refine ⟨?_, hrest⟩
  intro u
  constructor
  · let g : Domain d → ℝ := fun x => Fₑ x (gradientMap Ω p u x)
    have hi : Integrable g (domainMeasure Ω) := (hfinite u).1
    rw [← hmap] at hi
    have hi' := hEmb.integrable_map_iff.mp hi
    change Integrable (fun x : Ω => Fₑ x.val (gradientMap Ω p u x.val)) ν at hi'
    simpa only [Fₑ, extendFromDomain_apply] using hi'
  · change (∫ x, Fₑ x (gradientMap Ω p u x) ∂domainMeasure Ω) - ℓ u = _
    rw [← hint]
    simp only [Fₑ, extendFromDomain_apply]
    rfl

/-- Sectionwise a.e. measurable Carathéodory data admit a common measurable version. -/
theorem caratheodory_measurable_version {S E : Type*} [MeasurableSpace S]
    [PseudoMetricSpace E] [SecondCountableTopology E] [Nonempty E]
    {μ : Measure S} {F : S → E → ℝ}
    (hm : ∀ z, AEMeasurable (fun x => F x z) μ)
    (hc : ∀ᵐ x ∂μ, Continuous (F x)) :
    ∃ G : S → E → ℝ, (∀ z, Measurable (fun x => G x z)) ∧
      (∀ᵐ x ∂μ, Continuous (G x)) ∧ (∀ᵐ x ∂μ, ∀ z, G x z = F x z) := by
  classical
  let q : ℕ → E := denseSeq E
  have hq : DenseRange q := denseRange_denseSeq E
  have happrox (z : E) : ∃ k : ℕ → ℕ, Tendsto (q ∘ k) atTop (𝓝 z) := by
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (hq z)
    choose k hk using hv
    refine ⟨k, ?_⟩
    convert hlim using 1
    funext n
    exact hk n
  choose k hk using happrox
  let f : ℕ → S → ℝ := fun n => (hm (q n)).mk (fun x => F x (q n))
  have hf (n) : Measurable (f n) := (hm (q n)).measurable_mk
  have heq : ∀ᵐ x ∂μ, ∀ n, F x (q n) = f n x :=
    ae_all_iff.mpr (fun n => (hm (q n)).ae_eq_mk)
  let G : S → E → ℝ := fun x z => limsup (fun n => f (k z n) x) atTop
  have hGF : ∀ᵐ x ∂μ, ∀ z, G x z = F x z := by
    filter_upwards [heq, hc] with x hx hcx
    intro z
    apply Filter.Tendsto.limsup_eq
    simpa only [Function.comp_def, hx] using (hcx.tendsto z).comp (hk z)
  refine ⟨G, fun z => Measurable.limsup (fun n => hf (k z n)), ?_, hGF⟩
  filter_upwards [hGF, hc] with x hx hcx
  exact (funext hx) ▸ hcx


/-- The original Ω-indexed result, allowing Lebesgue-measurable base sections.
The measurable version agrees outside a single null set for every gradient
value, so the functional and all its properties are those of the original F. -/
theorem primal_attainment : PrimalExpected.Attainment := by
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
  have hj : objective Ω p (extendFromDomain Ω G) ℓ =
      objective Ω p (extendFromDomain Ω F) ℓ := by
    funext u
    apply congrArg (fun t : ℝ => t - ℓ u)
    apply integral_congr_ae
    apply (ae_restrict_iff_subtype Ω.isOpen.measurableSet).mpr
    filter_upwards [hGF] with x hx
    simpa only [extendFromDomain_apply] using hx (gradientMap Ω p u x.val)
  have hresult := primal_attainment_measurable hd Ω hΩ p hp G ℓ
    ⟨hm, hcont⟩ a₀ a₁ a h₀ h₁ ha hapos hgG hcG
  unfold PrimalExpected.DomainConclusion at hresult ⊢
  dsimp only at hresult ⊢
  rw [hj] at hresult
  refine ⟨?_, hresult.2⟩
  intro u
  have heq : (fun x : Ω => G x (gradientMap Ω p u x.val)) =ᵐ[volume.comap Subtype.val]
      (fun x : Ω => F x (gradientMap Ω p u x.val)) :=
    hGF.mono (fun x hx => hx (gradientMap Ω p u x.val))
  refine ⟨(hresult.1 u).1.congr heq, ?_⟩
  rw [(hresult.1 u).2, integral_congr_ae heq]

end VariationalNotes.Flux
