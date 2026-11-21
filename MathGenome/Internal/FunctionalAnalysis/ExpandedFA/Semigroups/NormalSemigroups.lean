import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.NormalSemigroups
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SemigroupGrowthAndGenerator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.GeneratorDeterminesSemigroup
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.MeasurableSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.BorelNormSpectrum
import Mathlib.Analysis.CStarAlgebra.Fuglede
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Filter Topology MeasureTheory
open scoped NNReal

namespace ExpandedFA.Semigroups.NormalSemigroups
open Unbounded Unbounded.MeasurableSpectralCalculus
open Unbounded.UnboundedNormalSpectralTheorem
universe u v

theorem adjoint_commutation : Spec.AdjointCommutation.{u} := by
  intro H _ _ _ T hT s t
  have hc : Commute (T.operators s) (T.operators t) := by
    change (T.operators s).comp (T.operators t) = (T.operators t).comp (T.operators s)
    rw [← T.add_time, ← T.add_time, add_comm]
  exact (hT s).commute_star_left hc

theorem normal_differenceQuotients : Spec.NormalDifferenceQuotients.{u} := by
  intro H _ _ _ T hT h
  letI := hT h.toNNReal
  have hcomm : Commute (T.operators h.toNNReal) (star (1 : H →L[ℂ] H)) := by simp
  have hsub : IsStarNormal (T.operators h.toNNReal - 1) := hcomm.isStarNormal_sub
  letI := hsub
  change IsStarNormal ((algebraMap ℝ ℂ h)⁻¹ • (T.operators h.toNNReal - 1))
  infer_instance

theorem adjoint_semigroup : Spec.AdjointSemigroup.{u} := by
  intro H _ _ _ T hT
  refine ⟨{ operators := fun t => (T.operators t).adjoint
            at_zero := by rw [T.at_zero]; exact ContinuousLinearMap.adjoint_id
            add_time := ?_
            strong_zero := ?_ }, fun _ => rfl⟩
  · intro t s
    rw [add_comm, T.add_time, ContinuousLinearMap.adjoint_comp]
  · intro x
    have hn : ∀ h : ℝ, ‖(T.operators h.toNNReal).adjoint x - x‖ =
        ‖T.operators h.toNNReal x - x‖ := by
      intro h
      let N := T.operators h.toNNReal - 1
      letI := hT h.toNNReal
      have hcomm : Commute (T.operators h.toNNReal) (star (1 : H →L[ℂ] H)) := by simp
      have hN : IsStarNormal N := hcomm.isStarNormal_sub
      have hh := (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp hN) x
      simpa [N, ContinuousLinearMap.adjoint_one] using hh.symm
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp_rw [hn]
    exact tendsto_iff_norm_sub_tendsto_zero.mp (T.strong_zero x)

section AdjointGenerator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real difference quotient commutes with taking adjoints. -/
theorem differenceQuotient_adjoint (T S : C0Semigroup ℂ H)
    (hS : ∀ t, S.operators t = (T.operators t).adjoint) (h : ℝ) :
    C0SemigroupSpec.differenceQuotientValue S h =
      (C0SemigroupSpec.differenceQuotientValue T h).adjoint := by
  simp [C0SemigroupSpec.differenceQuotientValue, hS, map_smulₛₗ,
    ContinuousLinearMap.adjoint_id]

/-- Integrating strongly continuous adjoint orbits preserves the adjoint pairing. -/
theorem integratedOperator_adjoint_pairing (T S : C0Semigroup ℂ H)
    (hS : ∀ t, S.operators t = (T.operators t).adjoint)
    (t : ℝ≥0) (x y : H) :
    inner ℂ (T.integratedOperator t x) y = inner ℂ x (S.integratedOperator t y) := by
  have hi (R : C0Semigroup ℂ H) (a b : H) :
      inner ℂ a (R.integratedOperator t b) =
        ∫ s in (0 : ℝ)..(t : ℝ), inner ℂ a (R.operators s.toNNReal b) := by
    exact ((innerSL ℂ a).intervalIntegral_comp_comm
      ((R.continuous_real_orbit b).intervalIntegrable _ _)).symm
  calc
    inner ℂ (T.integratedOperator t x) y =
        star (inner ℂ y (T.integratedOperator t x)) := (inner_conj_symm _ _).symm
    _ = star (∫ s in (0 : ℝ)..(t : ℝ), inner ℂ y (T.operators s.toNNReal x)) := by rw [hi]
    _ = ∫ s in (0 : ℝ)..(t : ℝ), inner ℂ (T.operators s.toNNReal x) y := by
      change (starRingEnd ℂ) _ = _
      rw [← intervalIntegral.intervalIntegral_conj]
      simp only [inner_conj_symm]
    _ = inner ℂ x (S.integratedOperator t y) := ?_
  rw [hi]
  congr 1
  funext s
  rw [hS, ContinuousLinearMap.adjoint_inner_right]

/-- Whenever the adjoint orbits form a C₀ semigroup, its generator is the
full Hilbert adjoint, with equality of the graphs and their domains. -/
theorem generator_adjoint (T S : C0Semigroup ℂ H)
    (hS : ∀ t, S.operators t = (T.operators t).adjoint) :
    C0SemigroupSpec.generatorValue S =
      HilbertAdjointSpec.adjointValue (C0SemigroupSpec.generatorValue T) := by
  let A := C0SemigroupSpec.generatorValue T
  let B := C0SemigroupSpec.generatorValue S
  apply LinearPMap.eq_of_eq_graph
  ext ⟨y, z⟩
  change (y, z) ∈ B.graph ↔ (y, z) ∈ (hilbertAdjoint A).graph
  rw [mem_hilbertAdjoint_graph_iff A T.generator_domain_dense]
  constructor
  · intro hy
    have hy' := (mem_generator_graph_iff S y z).mp hy
    intro x
    have hx := generator_has_limit T x
    have hleft := hx.inner (𝕜 := ℂ) (tendsto_const_nhds (x := y))
    have hright := (tendsto_const_nhds (x := (x : H))).inner (𝕜 := ℂ) hy'
    apply tendsto_nhds_unique hleft
    convert hright using 1
    funext h
    rw [differenceQuotient_adjoint T S hS, ContinuousLinearMap.adjoint_inner_right]
  · intro hy
    apply (mem_generator_graph_iff S y z).mpr
    apply (S.hasGeneratorLimit_iff_integrated y z).mpr
    intro t
    apply Dense.eq_of_inner_right (𝕜 := ℂ) T.generator_domain_dense
    intro x hx
    rw [inner_sub_right, hS, ContinuousLinearMap.adjoint_inner_right,
      ← inner_sub_left, ← integratedOperator_adjoint_pairing T S hS]
    have hid := T.orbit_integral_identity ⟨x, hx⟩ t
    change T.operators t x - x = T.integratedOperator t (A ⟨x, hx⟩) at hid
    rw [hid]
    have hi (a b : H) :
        inner ℂ (T.integratedOperator t a) b =
          ∫ s in (0 : ℝ)..(t : ℝ), inner ℂ (T.operators s.toNNReal a) b := by
      calc
        inner ℂ (T.integratedOperator t a) b =
            (starRingEnd ℂ) (inner ℂ b (T.integratedOperator t a)) :=
          (inner_conj_symm _ _).symm
        _ = (starRingEnd ℂ) (∫ s in (0 : ℝ)..(t : ℝ),
            inner ℂ b (T.operators s.toNNReal a)) := by
          exact congrArg (starRingEnd ℂ)
            (((innerSL ℂ b).intervalIntegral_comp_comm
              ((T.continuous_real_orbit a).intervalIntegrable _ _)).symm)
        _ = _ := by
          rw [← intervalIntegral.intervalIntegral_conj]
          simp only [inner_conj_symm]
    rw [hi, hi]
    congr 1
    funext s
    have hm := T.hasGeneratorLimit_map s.toNNReal (generator_has_limit T ⟨x, hx⟩)
    have hmem : T.operators s.toNNReal x ∈ A.domain := ⟨_, hm⟩
    have heq : A ⟨T.operators s.toNNReal x, hmem⟩ =
        T.operators s.toNNReal (A ⟨x, hx⟩) :=
      tendsto_nhds_unique (generator_has_limit T _) hm
    rw [← heq]
    exact hy ⟨_, hmem⟩

theorem linear_maps_inner_eq_of_norm_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F G : V →ₗ[ℂ] H) (hn : ∀ x, ‖F x‖ = ‖G x‖) (x y : V) :
    inner ℂ (F x) (F y) = inner ℂ (G x) (G y) := by
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [← map_add, ← map_sub, ← map_smul, hn]

theorem normal_of_domain_eq_and_norm_eq (A : Operator ℂ H H)
    (hd : Dense (A.domain : Set H)) (hc : A.IsClosed)
    (he : A.domain = (HilbertAdjointSpec.adjointValue A).domain)
    (hn : ∀ (x : A.domain) (y : (HilbertAdjointSpec.adjointValue A).domain),
      (x : H) = y → ‖A x‖ = ‖HilbertAdjointSpec.adjointValue A y‖) :
    OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue A) A =
      OperatorDomainsSpec.productValue A (HilbertAdjointSpec.adjointValue A) := by
  let B := hilbertAdjoint A
  have hdB : Dense (B.domain : Set H) := by change Dense ((HilbertAdjointSpec.adjointValue A).domain : Set H); rw [← he]; exact hd
  have hBB : hilbertAdjoint B = A := hilbertAdjoint_hilbertAdjoint_of_closed A hd hc
  let e : A.domain ≃ₗ[ℂ] B.domain :=
    { toFun := fun x => ⟨x, he ▸ x.prop⟩
      invFun := fun x => ⟨x, he.symm ▸ x.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinner (x y : A.domain) : inner ℂ (A x) (A y) = inner ℂ (B (e x)) (B (e y)) :=
    linear_maps_inner_eq_of_norm_eq A.toFun (B.toFun.comp e.toLinearMap)
      (fun x => hn x (e x) rfl) x y
  have hleft (x y : H) :
      (x, y) ∈ (OperatorDomainsSpec.productValue B A).graph ↔
       ∃ hx : x ∈ A.domain, ∀ z : A.domain,
         inner ℂ (A z) (A ⟨x, hx⟩) = inner ℂ (z : H) y := by
    constructor
    · intro h
      obtain ⟨hx, hy⟩ := (mem_graph_iff _ (x,y)).mp h
      obtain ⟨hxa, hxb⟩ := (mem_product_domain_iff B A x).mp hx
      refine ⟨hxa, ?_⟩
      intro z
      have hz := hilbertAdjoint_inner A hd ⟨A ⟨x,hxa⟩, hxb⟩ z
      exact hz.trans (congrArg (inner ℂ (z : H)) hy)
    · rintro ⟨hx, hy⟩
      have hb : (A ⟨x,hx⟩, y) ∈ B.graph := (mem_hilbertAdjoint_graph_iff A hd _ _).mpr hy
      obtain ⟨hb, hval⟩ := (mem_graph_iff B _).mp hb
      exact (mem_graph_iff _ _).mpr ⟨⟨hx, hb⟩, hval⟩
  have hright (x y : H) :
      (x, y) ∈ (OperatorDomainsSpec.productValue A B).graph ↔
       ∃ hx : x ∈ B.domain, ∀ z : B.domain,
         inner ℂ (B z) (B ⟨x, hx⟩) = inner ℂ (z : H) y := by
    constructor
    · intro h
      obtain ⟨hx, hy⟩ := (mem_graph_iff _ (x,y)).mp h
      obtain ⟨hxb, hxa⟩ := (mem_product_domain_iff A B x).mp hx
      refine ⟨hxb, ?_⟩
      intro z
      have hg : (B ⟨x,hxb⟩, A ⟨B ⟨x,hxb⟩,hxa⟩) ∈ (hilbertAdjoint B).graph := by
        rw [hBB]
        exact A.mem_graph_iff.mpr ⟨_, rfl, rfl⟩
      have hz := (mem_hilbertAdjoint_graph_iff B hdB _ _).mp hg z
      exact hz.trans (congrArg (inner ℂ (z : H)) hy)
    · rintro ⟨hx, hy⟩
      have hb : (B ⟨x,hx⟩, y) ∈ (hilbertAdjoint B).graph :=
       (mem_hilbertAdjoint_graph_iff B hdB _ _).mpr hy
      rw [hBB] at hb
      obtain ⟨hb, hval⟩ := (mem_graph_iff A _).mp hb
      exact (mem_graph_iff _ _).mpr ⟨⟨hx, hb⟩, hval⟩
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x,y⟩
  change (x,y) ∈ (OperatorDomainsSpec.productValue B A).graph ↔
    (x,y) ∈ (OperatorDomainsSpec.productValue A B).graph
  rw [hleft, hright]
  constructor
  · rintro ⟨hx, hh⟩
    refine ⟨he ▸ hx, ?_⟩
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    exact (hinner w ⟨x,hx⟩).symm.trans (hh w)
  · rintro ⟨hx, hh⟩
    refine ⟨he.symm ▸ hx, ?_⟩
    intro z
    exact (hinner z ⟨x,he.symm ▸ hx⟩).trans (hh (e z))

end AdjointGenerator

section GeneratorDomains
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Fuglede also makes the difference of any two generator quotients normal. -/
theorem normal_differenceQuotient_differences (T : C0Semigroup ℂ H)
    (hT : IsNormalSemigroup T) (h k : ℝ) :
    IsStarNormal (C0SemigroupSpec.differenceQuotientValue T h -
      C0SemigroupSpec.differenceQuotientValue T k) := by
  letI := normal_differenceQuotients H T hT h
  letI := normal_differenceQuotients H T hT k
  apply Commute.isStarNormal_sub
  have htk : Commute (T.operators h.toNNReal) (star (T.operators k.toNNReal)) :=
    (show Commute (star (T.operators k.toNNReal)) (T.operators h.toNNReal) from
      adjoint_commutation H T hT k.toNNReal h.toNNReal).symm
  have hs : Commute (T.operators h.toNNReal - 1) (star (T.operators k.toNNReal) - 1) :=
    (htk.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  change Commute (((algebraMap ℝ ℂ h)⁻¹) • (T.operators h.toNNReal - 1))
    (star (((algebraMap ℝ ℂ k)⁻¹) • (T.operators k.toNNReal - 1)))
  simpa only [star_smul, star_sub, star_one] using
    (hs.smul_left ((algebraMap ℝ ℂ h)⁻¹)).smul_right (star ((algebraMap ℝ ℂ k)⁻¹))

/-- Equality of all pairwise quotient distances transfers convergence, and
therefore the complete derivative domain, to the adjoint semigroup. -/
theorem generators_domain_and_norm_of_normalQuotients (T S : C0Semigroup ℂ H)
    (hS : ∀ t, S.operators t = (T.operators t).adjoint)
    (hq : ∀ h, IsStarNormal (C0SemigroupSpec.differenceQuotientValue T h))
    (hn : ∀ h k, IsStarNormal (C0SemigroupSpec.differenceQuotientValue T h -
      C0SemigroupSpec.differenceQuotientValue T k)) :
    (C0SemigroupSpec.generatorValue T).domain = (C0SemigroupSpec.generatorValue S).domain ∧
    ∀ (x : (C0SemigroupSpec.generatorValue T).domain)
      (y : (C0SemigroupSpec.generatorValue S).domain), (x : H) = y →
      ‖C0SemigroupSpec.generatorValue T x‖ = ‖C0SemigroupSpec.generatorValue S y‖ := by
  have hdist (h k : ℝ) (x : H) :
      dist (C0SemigroupSpec.differenceQuotientValue S h x)
        (C0SemigroupSpec.differenceQuotientValue S k x) =
      dist (C0SemigroupSpec.differenceQuotientValue T h x)
        (C0SemigroupSpec.differenceQuotientValue T k x) := by
    have he := (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp (hn h k)) x
    simpa only [dist_eq_norm, map_sub, sub_apply,
      differenceQuotient_adjoint T S hS] using he.symm
  have hc (f g : ℝ → H)
      (he : ∀ i j, dist (g i) (g j) = dist (f i) (f j))
      (hf : ∃ y, Tendsto f (𝓝[>] 0) (𝓝 y)) : ∃ z, Tendsto g (𝓝[>] 0) (𝓝 z) := by
    apply cauchy_map_iff_exists_tendsto.mp
    have hh : Cauchy ((𝓝[>] 0).map f) := cauchy_map_iff_exists_tendsto.mpr hf
    rw [cauchy_map_iff', tendsto_uniformity_iff_dist_tendsto_zero] at hh ⊢
    simpa only [he] using hh
  constructor
  · ext x
    constructor
    · intro hx
      change ∃ z, Tendsto (fun h => C0SemigroupSpec.differenceQuotientValue S h x)
        (𝓝[>] 0) (𝓝 z)
      exact hc (fun h => C0SemigroupSpec.differenceQuotientValue T h x)
        (fun h => C0SemigroupSpec.differenceQuotientValue S h x) (fun h k => hdist h k x) hx
    · intro hx
      change ∃ z, Tendsto (fun h => C0SemigroupSpec.differenceQuotientValue T h x)
        (𝓝[>] 0) (𝓝 z)
      exact hc (fun h => C0SemigroupSpec.differenceQuotientValue S h x)
        (fun h => C0SemigroupSpec.differenceQuotientValue T h x) (fun h k => (hdist h k x).symm) hx
  · intro x y hxy
    apply tendsto_nhds_unique (generator_has_limit T x).norm
    convert (generator_has_limit S y).norm using 1
    funext h
    have he := (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp (hq h)) (x : H)
    simpa only [← differenceQuotient_adjoint T S hS, hxy] using he

/-- A normal C₀ semigroup's generator and its full Hilbert adjoint have
identical domains and equal pointwise norms. -/
theorem generator_domain_adjoint_and_norm (T : C0Semigroup ℂ H)
    (hT : IsNormalSemigroup T) :
    let A := C0SemigroupSpec.generatorValue T
    A.domain = (HilbertAdjointSpec.adjointValue A).domain ∧
    ∀ (x : A.domain) (y : (HilbertAdjointSpec.adjointValue A).domain), (x : H) = y →
      ‖A x‖ = ‖HilbertAdjointSpec.adjointValue A y‖ := by
  obtain ⟨S, hS⟩ := adjoint_semigroup H T hT
  have hh := generators_domain_and_norm_of_normalQuotients T S hS
    (normal_differenceQuotients H T hT) (normal_differenceQuotient_differences T hT)
  dsimp only
  rw [← generator_adjoint T S hS]
  exact hh

end GeneratorDomains

/-- Every normal C₀ semigroup has a normal generator on its full domain. -/
theorem generator_normality : Spec.GeneratorNormality.{u} := by
  intro H _ _ _ T hT
  obtain ⟨he, hn⟩ := generator_domain_adjoint_and_norm T hT
  exact normal_of_domain_eq_and_norm_eq (C0SemigroupSpec.generatorValue T)
    T.generator_domain_dense T.generator_graph_closed he hn


section Spectral
variable {S : Type v} {H : Type u} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)

/-- Filter form of strong bounded convergence. Each vector has its own
finite measure; neither a common control measure nor separability is used. -/
theorem strong_convergence_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (g : S → ℂ) (a : ι → S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g)
    (ha : ∀ i, SpectralMeasure.Spec.IsBoundedMeasurable (a i))
    (hb : ∃ M : ℝ, ∀ᶠ i in l, ∀ s, ‖a i s‖ ≤ M)
    (hl : ∀ s, Tendsto (fun i => a i s) l (𝓝 (g s))) (x : H) :
    Tendsto (fun i => C.integral (a i) x) l (𝓝 (C.integral g x)) := by
  haveI := C.finite x
  obtain ⟨M, hM⟩ := hb
  obtain ⟨D, hD0, hD⟩ := hg.nonneg_bound
  let K := max M 0 + D
  have hK : 0 ≤ K := add_nonneg (le_max_right _ _) hD0
  have hdiff (i : ι) : SpectralMeasure.Spec.IsBoundedMeasurable (a i - g) :=
    SpectralMeasure.BorelNormSpectrum.bounded_sub (ha i) hg
  have hi : Tendsto (fun i => ∫ s, ‖a i s - g s‖ ^ 2 ∂C.measure x)
      l (𝓝 (0 : ℝ)) := by
    have hh : Tendsto (fun i => ∫ s, ‖a i s - g s‖ ^ 2 ∂C.measure x)
        l (𝓝 (∫ _ : S, (0 : ℝ) ∂C.measure x)) := by
      apply tendsto_integral_filter_of_norm_le_const
      · exact Eventually.of_forall (fun i =>
          (((ha i).1.sub hg.1).norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
      · refine ⟨K ^ 2, ?_⟩
        filter_upwards [hM] with i hi
        exact Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _)
            ((norm_sub_le _ _).trans (add_le_add ((hi s).trans (le_max_left _ _)) (hD s))) 2
      · exact Eventually.of_forall fun s => by
          simpa using ((hl s).sub (tendsto_const_nhds (x := g s))).norm.pow 2
    simpa using hh
  have hsquare : Tendsto (fun i => ‖C.integral (a i) x - C.integral g x‖ ^ 2)
      l (𝓝 (0 : ℝ)) := by
    have heq (i : ι) : ‖C.integral (a i) x - C.integral g x‖ ^ 2 =
        ∫ s, ‖a i s - g s‖ ^ 2 ∂C.measure x := by
      rw [← sub_apply, ← C.sub _ _ (ha i) hg]
      exact C.norm_sq _ (hdiff i) x
    simpa only [heq] using hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsquare
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

theorem exponentialSymbol_bounded {f : S → ℂ} (hf : Measurable f) {ω : ℝ}
    (hω : ∀ s, (f s).re ≤ ω) (t : ℝ≥0) :
    SpectralMeasure.Spec.IsBoundedMeasurable (fun s => Complex.exp ((t : ℂ) * f s)) := by
  refine ⟨(measurable_const.mul hf).cexp, Real.exp ((t : ℝ) * ω), fun s => ?_⟩
  rw [Complex.norm_exp, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hω s) t.coe_nonneg)

theorem spectral_semigroup : Spec.SpectralSemigroup := by
  intro S H _ _ _ _ E C f hf hbound
  obtain ⟨ω, hω⟩ := hbound
  let a : ℝ≥0 → S → ℂ := fun t s => Complex.exp ((t : ℂ) * f s)
  have ha (t) : SpectralMeasure.Spec.IsBoundedMeasurable (a t) :=
    exponentialSymbol_bounded hf hω t
  have h0 : a 0 = fun _ => 1 := by funext s; simp [a]
  have hadd (t s : ℝ≥0) : a (t+s) = a t * a s := by
    funext z
    simp only [a, NNReal.coe_add, Complex.ofReal_add, add_mul, Complex.exp_add, Pi.mul_apply]
  have hstrong (x : H) : Tendsto (fun h : ℝ => C.integral (a h.toNNReal) x)
      (𝓝[>] 0) (𝓝 x) := by
    have hh := strong_convergence_filter C (l := 𝓝[>] (0 : ℝ))
      (fun _ => 1) (fun h : ℝ => a h.toNNReal)
      (SpectralMeasure.BorelNormSpectrum.bounded_const 1) (fun h => ha _) ?_ ?_ x
    · simpa only [C.one, one_apply_eq_self] using hh
    · refine ⟨Real.exp (max ω 0), ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
      intro s
      change ‖Complex.exp (((h.toNNReal : ℝ) : ℂ) * f s)‖ ≤ _
      rw [Real.toNNReal_of_nonneg hh.1.le, Complex.norm_exp, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      apply Real.exp_le_exp.mpr
      calc
        h * (f s).re ≤ h * max ω 0 :=
          mul_le_mul_of_nonneg_left ((hω s).trans (le_max_left _ _)) hh.1.le
        _ ≤ max ω 0 := by
          simpa using mul_le_mul_of_nonneg_right hh.2.le (le_max_right ω 0)
    · intro s
      have ht : Tendsto (fun h : ℝ => (h.toNNReal : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
        have ht0 := ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
          continuous_real_toNNReal)).tendsto 0).mono_left
            (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
        simpa [Function.comp_def] using ht0
      simpa [a] using (ht.mul_const (f s)).cexp
  let T : C0Semigroup ℂ H :=
    { operators := fun t => C.integral (a t)
      at_zero := by rw [h0, C.one]; rfl
      add_time := fun t s => by rw [hadd, C.mul _ _ (ha t) (ha s)]; rfl
      strong_zero := hstrong }
  refine ⟨T, ?_, fun _ => rfl⟩
  intro t
  constructor
  change star (C.integral (a t)) * C.integral (a t) =
    C.integral (a t) * star (C.integral (a t))
  rw [← C.map_star _ (ha t), ← C.mul _ _ (ha t).star (ha t),
    ← C.mul _ _ (ha t) (ha t).star, mul_comm]

/-- The full-domain bounded integral agrees with the unbounded construction. -/
theorem measurableIntegral_of_bounded {f : S → ℂ}
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    measurableIntegral C f = (C.integral f).toLinearMap.toPMap ⊤ := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, y⟩
  rw [measurableIntegral, mem_limitOperator_graph_iff]
  have ht : Tendsto (fun n => C.integral (truncation f n) x) atTop
      (𝓝 (C.integral f x)) := by
    obtain ⟨M, hM⟩ := hf.2
    obtain ⟨k, hk⟩ := exists_nat_ge M
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    have he : truncation f n = f := by
      funext s
      have hs : ‖f s‖ ≤ (n : ℝ) := (hM s).trans (hk.trans (by exact_mod_cast hn))
      simp [truncation, hs]
    rw [he]
  constructor
  · intro hy
    exact ((C.integral f).toLinearMap.toPMap ⊤).mem_graph_iff.mpr
      ⟨⟨x, Submodule.mem_top⟩, rfl, tendsto_nhds_unique ht hy⟩
  · intro hy
    obtain ⟨z, hz, hzy⟩ := ((C.integral f).toLinearMap.toPMap ⊤).mem_graph_iff.mp hy
    change (z : H) = x at hz
    change C.integral f z = y at hzy
    have heval : C.integral f x = y := by simpa only [hz] using hzy
    simpa only [heval] using ht

/-- On a bounded spectral region, the exponential difference quotient has
uniform remainder at most h n². This avoids domination by exp(|f|). -/
theorem exponential_cutoff_remainder {f : S → ℂ} (n : ℕ) {h : ℝ}
    (hh : 0 < h) (hn : h * (n : ℝ) ≤ 1) (s : S) :
    ‖(cutoffIndicator f n s) *
      ((h : ℂ)⁻¹ * (Complex.exp ((h : ℂ) * f s) - 1) - f s)‖ ≤ h * (n : ℝ) ^ 2 := by
  classical
  by_cases hs : ‖f s‖ ≤ (n : ℝ)
  · have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have hnorm : ‖(h : ℂ) * f s‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      exact (mul_le_mul_of_nonneg_left hs hh.le).trans hn
    have hrem := Complex.norm_exp_sub_one_sub_id_le hnorm
    have hid : (h : ℂ)⁻¹ * (Complex.exp ((h : ℂ) * f s) - 1) - f s =
        (h : ℂ)⁻¹ * (Complex.exp ((h : ℂ) * f s) - 1 - (h : ℂ) * f s) := by
      field_simp
    have hcut : cutoffIndicator f n s = 1 := by simp [cutoffIndicator, hs]
    rw [hcut, one_mul]
    rw [hid, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    calc
      h⁻¹ * ‖Complex.exp ((h : ℂ) * f s) - 1 - (h : ℂ) * f s‖ ≤
          h⁻¹ * ‖(h : ℂ) * f s‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hrem (inv_nonneg.mpr hh.le)
      _ = h * ‖f s‖ ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
        field_simp
      _ ≤ h * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs 2) hh.le
  · have hcut : cutoffIndicator f n s = 0 := by simp [cutoffIndicator, hs]
    rw [hcut, zero_mul, norm_zero]
    positivity

theorem generator_eq_spectralIntegral {f : S → ℂ} (hf : Measurable f) {ω : ℝ}
    (hω : ∀ s, (f s).re ≤ ω) (T : C0Semigroup ℂ H)
    (hT : ∀ t : ℝ≥0, T.operators t = C.integral (fun s => Complex.exp ((t : ℂ) * f s))) :
    C0SemigroupSpec.generatorValue T = measurableIntegral C f := by
  let a : ℝ≥0 → S → ℂ := fun t s => Complex.exp ((t : ℂ) * f s)
  let P := fun n => C.integral (cutoffIndicator f n)
  let R := fun n => C.integral (truncation f n)
  let q : ℝ → S → ℂ := fun h => (h : ℂ)⁻¹ • (a h.toNNReal - 1)
  have ha (t) : SpectralMeasure.Spec.IsBoundedMeasurable (a t) :=
    exponentialSymbol_bounded hf hω t
  have hq (h) : SpectralMeasure.Spec.IsBoundedMeasurable (q h) :=
    (SpectralMeasure.BorelNormSpectrum.bounded_sub (ha h.toNNReal)
      (SpectralMeasure.BorelNormSpectrum.bounded_const 1)).smul _
  have hP (n) := boundedMeasurable_cutoffIndicator hf n
  have hR (n) := boundedMeasurable_truncation hf n
  have hquot (h : ℝ) : C0SemigroupSpec.differenceQuotientValue T h = C.integral (q h) := by
    change (algebraMap ℝ ℂ h)⁻¹ • (T.operators h.toNNReal - 1) = _
    change _ = C.integral ((h : ℂ)⁻¹ • (a h.toNNReal - (fun _ => 1)))
    rw [hT, C.smul _ _ (SpectralMeasure.BorelNormSpectrum.bounded_sub (ha _)
      (SpectralMeasure.BorelNormSpectrum.bounded_const 1)),
      C.sub _ _ (ha _) (SpectralMeasure.BorelNormSpectrum.bounded_const 1), C.one]
    rfl
  have hlocal (n : ℕ) (x : H) :
      C0SemigroupSpec.hasGeneratorLimitValue T (P n x) (R n x) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    let b : ℝ → S → ℂ := fun h => q h * cutoffIndicator f n - truncation f n
    have hb (h) : SpectralMeasure.Spec.IsBoundedMeasurable (b h) :=
      SpectralMeasure.BorelNormSpectrum.bounded_sub ((hq h).mul (hP n)) (hR n)
    have he (h : ℝ) : C0SemigroupSpec.differenceQuotientValue T h (P n x) - R n x =
        C.integral (b h) x := by
      rw [hquot, C.sub _ _ ((hq h).mul (hP n)) (hR n),
        C.mul _ _ (hq h) (hP n)]
      rfl
    change Tendsto (fun h => ‖C0SemigroupSpec.differenceQuotientValue T h (P n x) - R n x‖)
      (𝓝[>] 0) (𝓝 0)
    simp_rw [he]
    apply squeeze_zero_norm' (a := fun h : ℝ => h * (n : ℝ) ^ 2 * ‖x‖)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity)] with h hh
      have hh0 := hh.1
      have hn : h * (n : ℝ) ≤ 1 := by
        have hnn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hh' : h * ((n : ℝ) + 1) < 1 :=
          (lt_div_iff₀ hnn).mp (by simpa using hh.2)
        nlinarith
      have hbn (s : S) : ‖b h s‖ ≤ h * (n : ℝ) ^ 2 := by
        have heq : b h s = cutoffIndicator f n s *
            ((h : ℂ)⁻¹ * (Complex.exp ((h : ℂ) * f s) - 1) - f s) := by
          classical
          by_cases hs : ‖f s‖ ≤ (n : ℝ)
          · simp [b, q, a, cutoffIndicator, truncation, hs, max_eq_left hh0.le]
          · simp [b, cutoffIndicator, truncation, hs]
        rw [heq]
        exact exponential_cutoff_remainder n hh0 hn s
      simpa only [norm_norm] using (C.integral (b h)).le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_right (C.bound _ _ (hb h) (by positivity) hbn) (norm_nonneg _))
    · simpa using (((tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0)).mul_const ((n : ℝ) ^ 2)).mul_const ‖x‖)
  have hcomm (n : ℕ) (h : ℝ) (x : H) :
      P n (C0SemigroupSpec.differenceQuotientValue T h x) =
        C0SemigroupSpec.differenceQuotientValue T h (P n x) := by
    rw [hquot]
    change (C.integral (cutoffIndicator f n) * C.integral (q h)) x =
      (C.integral (q h) * C.integral (cutoffIndicator f n)) x
    rw [← C.mul _ _ (hP n) (hq h), ← C.mul _ _ (hq h) (hP n), mul_comm]
  have hPlim (x : H) : Tendsto (fun n => P n x) atTop (𝓝 x) := C.cutoff_tendsto hf x
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, y⟩
  constructor
  · intro hxy
    have hlim := (mem_generator_graph_iff T x y).mp hxy
    have hval (n : ℕ) : R n x = P n y := by
      have hl := (P n).continuous.tendsto y |>.comp hlim
      exact tendsto_nhds_unique (hlocal n x)
        (hl.congr' (Eventually.of_forall fun h => hcomm n h x))
    rw [measurableIntegral, mem_limitOperator_graph_iff]
    simpa only [← hval] using hPlim y
  · intro hxy
    have hy := (mem_limitOperator_graph_iff _ x y).mp hxy
    apply T.generator_graph_closed.mem_of_tendsto
      ((hPlim x).prodMk_nhds hy)
    exact Eventually.of_forall fun n => (mem_generator_graph_iff T _ _).mpr (hlocal n x)

end Spectral

theorem spectral_generator : Spec.SpectralGenerator := by
  intro S H _ _ _ _ E C f hf hω T hT
  obtain ⟨ω, hω⟩ := hω
  exact generator_eq_spectralIntegral C hf hω T hT

/-- A spectral upper bound suffices on the spectrum. The extension by zero
is used only to apply the bounded calculus; a.e. equality identifies the
result with the actual unbounded exponential symbol on ℂ. -/
theorem converse : Spec.Converse.{u} := by
  intro H _ _ _ A hd hc hn hbound
  obtain ⟨ω, hω⟩ := hbound
  obtain ⟨E, hE⟩ := spectral_existence H A hd hc hn
  have hsupport := (spectral_uniqueness_and_support H A hd hc hn E hE).1
  obtain ⟨C, hC, hdomain⟩ := hE
  let f : ℂ → ℂ := (operatorSpectrum A).indicator id
  have hf : Measurable f := measurable_id.indicator hsupport.1.measurableSet
  have hfbound (z : ℂ) : (f z).re ≤ max ω 0 := by
    classical
    by_cases hz : z ∈ operatorSpectrum A
    · simpa [f, hz] using (hω z hz).trans (le_max_left ω 0)
    · simpa [f, hz] using (le_max_right ω 0)
  have heq (x : H) : f =ᵐ[C.measure x] id := by
    have hnull : C.measure x (operatorSpectrum A)ᶜ = 0 := by
      rw [C.measure_apply x _ hsupport.1.measurableSet.compl, hsupport.2.1]
      simp
    have hmem : ∀ᵐ z ∂C.measure x, z ∈ operatorSpectrum A := ae_iff.mpr hnull
    filter_upwards [hmem] with z hz
    simp [f, hz]
  have hfid : measurableIntegral C f = A :=
    (C.measurableIntegral_congr_ae f id hf measurable_id heq).trans hC
  obtain ⟨T, hnormal, hT⟩ := spectral_semigroup ℂ H E C f hf ⟨max ω 0, hfbound⟩
  refine ⟨T, hnormal, (generator_eq_spectralIntegral C hf hfbound T hT).trans hfid,
    E, C, hC, ?_⟩
  intro t
  calc
    measurableIntegral C (fun z => Complex.exp ((t : ℂ) * z)) =
        measurableIntegral C (fun z => Complex.exp ((t : ℂ) * f z)) := by
      apply C.measurableIntegral_congr_ae
      · exact (measurable_const.mul measurable_id).cexp
      · exact (measurable_const.mul hf).cexp
      · intro x
        filter_upwards [heq x] with z hz
        rw [hz]
        rfl
    _ = (C.integral (fun z => Complex.exp ((t : ℂ) * f z))).toLinearMap.toPMap ⊤ :=
      measurableIntegral_of_bounded C (exponentialSymbol_bounded hf hfbound t)
    _ = (T.operators t).toLinearMap.toPMap ⊤ := by rw [hT]

/-- Once normality and spectral boundedness of a generator are established,
the converse and exact-domain generator uniqueness give the original
semigroup's exponential representation. -/
theorem exponentialRepresentation_of_generator {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : C0Semigroup ℂ H)
    (hn : OperatorDomainsSpec.productValue
        (HilbertAdjointSpec.adjointValue (C0SemigroupSpec.generatorValue T))
        (C0SemigroupSpec.generatorValue T) =
      OperatorDomainsSpec.productValue (C0SemigroupSpec.generatorValue T)
        (HilbertAdjointSpec.adjointValue (C0SemigroupSpec.generatorValue T)))
    (hb : HasSpectralUpperBound (C0SemigroupSpec.generatorValue T)) :
    ExponentialRepresentation (C0SemigroupSpec.generatorValue T) T := by
  obtain ⟨S, _, hS, E, C, hC, hExp⟩ := converse H (C0SemigroupSpec.generatorValue T)
    T.generator_domain_dense T.generator_graph_closed hn hb
  have heq := GeneratorDeterminesSemigroup.generator_determines_semigroup S T hS
  exact ⟨E, C, hC, fun t => by rw [← heq t]; exact hExp t⟩

section SpectralBound
open Set
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Normality removes the constant M from the exponential growth estimate. -/
theorem operators_nsmul_time (T : C0Semigroup ℂ H) (t : ℝ≥0) (n : ℕ) :
    T.operators (n • t) = (T.operators t) ^ n := by
  induction n with
  | zero => simp only [zero_nsmul, pow_zero]; exact T.at_zero
  | succ n ih =>
    rw [succ_nsmul, T.add_time, ih, pow_succ]
    rfl

theorem norm_time_le_exp (T : C0Semigroup ℂ H) (hT : IsNormalSemigroup T)
    {M ω : ℝ} (hbound : C0SemigroupSpec.exponentialBoundValue T M ω)
    (t : ℝ≥0) : ‖T.operators t‖ ≤ Real.exp (ω * (t : ℝ)) := by
  have hp (n : ℕ) (hn : n ≠ 0) :
      ‖T.operators t‖ ^ n ≤ M * (Real.exp (ω * (t : ℝ))) ^ n := by
    rw [← CFC.norm_pow ℂ (T.operators t) n hn (hT t), ← operators_nsmul_time]
    convert hbound.2 (n • t) using 1
    rw [NNReal.coe_nsmul, nsmul_eq_mul, ← Real.exp_nat_mul]
    congr 2
    ring
  by_contra hnot
  have he := Real.exp_pos (ω * (t : ℝ))
  have hq : 1 < ‖T.operators t‖ / Real.exp (ω * (t : ℝ)) :=
    (one_lt_div he).mpr (lt_of_not_ge hnot)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hq
  have hn0 : n ≠ 0 := by
    intro hz
    have hbad : M < 1 := by simpa [hz] using hn
    linarith [hbound.1]
  have hqbound : (‖T.operators t‖ / Real.exp (ω * (t : ℝ))) ^ n ≤ M := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos he n)).mpr (hp n hn0)
  exact (not_le_of_gt hn) hqbound

theorem normal_semigroup_exponential_bound (T : C0Semigroup ℂ H)
    (hT : IsNormalSemigroup T) :
    ∃ ω : ℝ, ∀ t : ℝ≥0, ‖T.operators t‖ ≤ Real.exp (ω * (t : ℝ)) := by
  obtain ⟨M, ω, hbound⟩ := T.exponential_bound
  exact ⟨ω, norm_time_le_exp T hT hbound⟩


theorem generator_numerical_bound (T : C0Semigroup ℂ H) (ω : ℝ)
    (hb : ∀ t : ℝ≥0, ‖T.operators t‖ ≤ Real.exp (ω * (t : ℝ)))
    (x : (C0SemigroupSpec.generatorValue T).domain) :
    (inner ℂ (x : H) (C0SemigroupSpec.generatorValue T x)).re ≤ ω * ‖(x : H)‖ ^ 2 := by
  let A := C0SemigroupSpec.generatorValue T
  have hd := T.hasDerivWithinAt_orbit x 0 le_rfl
  have hdinner := hd.inner ℂ hd
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt 0 hdinner
  have hd' : HasDerivWithinAt (fun h : ℝ => ‖T.operators h.toNNReal x‖ ^ 2)
      (2 * (inner ℂ (x : H) (A x)).re) (Ici 0) 0 := by
    convert hreal using 1
    · ext h; simp only [Function.comp_apply, Complex.reCLM_apply, inner_self_eq_norm_sq_to_K]; norm_cast
    · simp only [Real.toNNReal_zero, T.at_zero, ContinuousLinearMap.id_apply,
        Complex.reCLM_apply, Complex.add_re]
      dsimp [A]
      rw [← inner_conj_symm (generator T x) (x : H)]
      simp only [generator, Complex.conj_re, two_mul]
  have hg : HasDerivAt (fun h : ℝ => Real.exp (2 * ω * h) * ‖(x : H)‖ ^ 2)
      (2 * ω * ‖(x : H)‖ ^ 2) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (2 * ω)).exp.mul_const
      (‖(x : H)‖ ^ 2))
  have hf_lim := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp
    (hd'.mono Ioi_subset_Ici_self)
  have hg_lim := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp
    (hg.hasDerivWithinAt (s := Ioi 0))
  have hle : 2 * (inner ℂ (x : H) (A x)).re ≤ 2 * ω * ‖(x : H)‖ ^ 2 := by
    apply le_of_tendsto_of_tendsto hf_lim hg_lim
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 < h := hh
    have hn : ‖T.operators h.toNNReal x‖ ≤ Real.exp (ω * h) * ‖(x : H)‖ := by
      calc
        _ ≤ ‖T.operators h.toNNReal‖ * ‖(x : H)‖ := (T.operators _).le_opNorm _
        _ ≤ _ := by simpa [Real.coe_toNNReal _ hh0.le] using
          mul_le_mul_of_nonneg_right (hb h.toNNReal) (norm_nonneg (x : H))
    have hsq : ‖T.operators h.toNNReal x‖ ^ 2 ≤ Real.exp (2 * ω * h) * ‖(x : H)‖ ^ 2 := by
      calc
        _ ≤ (Real.exp (ω * h) * ‖(x : H)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = _ := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2; ring
    simp only [slope_def_field, sub_zero, Real.toNNReal_zero, T.at_zero,
      ContinuousLinearMap.id_apply, mul_zero, Real.exp_zero, one_mul]
    exact div_le_div_of_nonneg_right (sub_le_sub_right hsq _) hh0.le
  dsimp [A] at hle
  linarith


open Unbounded.UnboundedNormalSpectralTheorem.SpectralRepresentation

theorem spectral_upper_of_numerical (N : Operator ℂ H H)
    (hd : Dense (N.domain : Set H)) (hc : N.IsClosed)
    (hn : OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue N) N =
      OperatorDomainsSpec.productValue N (HilbertAdjointSpec.adjointValue N))
    (ω : ℝ)
    (hnum : ∀ x : N.domain, (inner ℂ (x : H) (N x)).re ≤ ω * ‖(x : H)‖ ^ 2) :
    ∀ z ∈ operatorSpectrum N, z.re ≤ ω := by
  obtain ⟨E, C, hC, _⟩ := spectral_existence H N hd hc hn
  have hsupp := (spectral_uniqueness_and_support H N hd hc hn E
    (resolves_of_integral_eq N E C hC)).1
  intro z hz
  by_contra hh
  have hgap : 0 < z.re - ω := sub_pos.mpr (lt_of_not_ge hh)
  let r := (z.re - ω) / 2
  have hr : 0 < r := half_pos hgap
  have hP : E (Metric.ball z r) ≠ 0 :=
    (UnboundedNormalSpectralTheorem.mem_spectrum_iff N E hsupp z).mp hz _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨y, hy⟩ : ∃ y : H, E (Metric.ball z r) y ≠ 0 := by
    by_contra hnot
    apply hP
    ext y
    simp only [not_exists, not_not] at hnot
    simpa using hnot y
  let x := E (Metric.ball z r) y
  have hx : x ≠ 0 := hy
  have hfix : E (Metric.closedBall z r) x = x := by
    change (E (Metric.closedBall z r) * E (Metric.ball z r)) y = _
    rw [E.inter _ _ measurableSet_closedBall measurableSet_ball,
      inter_eq_right.mpr Metric.ball_subset_closedBall]
  obtain ⟨a, ha0, haD, hag, hab⟩ := disk_sequence C z r hr.le x hfix
  have hdom : x ∈ N.domain := by simpa [hC, ha0] using haD 0
  have hgraph : (x, z • x + a 1) ∈ N.graph := by simpa [hC, ha0] using hag 0
  have heval : N ⟨x, hdom⟩ = z • x + a 1 :=
    N.mem_graph_snd_inj (N.mem_graph ⟨x, hdom⟩) hgraph rfl
  have hn1 : ‖a 1‖ ≤ r * ‖x‖ := by simpa only [pow_one] using hab 1
  have hn0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have herror : -(r * ‖x‖ ^ 2) ≤ (inner ℂ x (a 1)).re := by
    have hh1 := (abs_le.mp (Complex.abs_re_le_norm (inner ℂ x (a 1)))).1
    have hh2 := norm_inner_le_norm x (a 1) (𝕜 := ℂ)
    have hh3 := mul_le_mul_of_nonneg_left hn1 (norm_nonneg x)
    nlinarith
  have hip : (inner ℂ x (N ⟨x, hdom⟩)).re =
      z.re * ‖x‖ ^ 2 + (inner ℂ x (a 1)).re := by
    rw [heval, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  have hhnum := hnum ⟨x, hdom⟩
  change (inner ℂ x (N ⟨x, hdom⟩)).re ≤ ω * ‖x‖ ^ 2 at hhnum
  rw [hip] at hhnum
  have hr2 : 2 * r = z.re - ω := by dsimp [r]; ring
  nlinarith [sq_pos_of_pos hn0]


theorem normal_generator_spectral_upper_bound (T : C0Semigroup ℂ H)
    (hT : IsNormalSemigroup T)
    (hn : OperatorDomainsSpec.productValue
        (HilbertAdjointSpec.adjointValue (C0SemigroupSpec.generatorValue T))
        (C0SemigroupSpec.generatorValue T) =
      OperatorDomainsSpec.productValue (C0SemigroupSpec.generatorValue T)
        (HilbertAdjointSpec.adjointValue (C0SemigroupSpec.generatorValue T))) :
    HasSpectralUpperBound (C0SemigroupSpec.generatorValue T) := by
  obtain ⟨ω, hb⟩ := normal_semigroup_exponential_bound T hT
  exact ⟨ω, spectral_upper_of_numerical _ T.generator_domain_dense T.generator_graph_closed hn
    ω (generator_numerical_bound T ω hb)⟩

end SpectralBound

/-- Both conclusions use the canonical generator, with its complete right
norm derivative domain, on an arbitrary complex Hilbert space. -/
theorem forward : Spec.Forward.{u} := by
  intro H _ _ _ T hT
  have hn := generator_normality H T hT
  have hb := normal_generator_spectral_upper_bound T hT hn
  exact ⟨T.generator_domain_dense, T.generator_graph_closed, hn, hb,
    exponentialRepresentation_of_generator T hn hb⟩

end ExpandedFA.Semigroups.NormalSemigroups
