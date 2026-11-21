import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.TransferSampling
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.Disintegration
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelRandomization
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.ConditionalGluing

open MeasureTheory ProbabilityTheory Set

namespace ProbabilityFoundations.Ch04
universe u v w x
open Specs.ProbabilityFoundations.Ch04.TransferSampling

/-- Transfer of a joint probability to any realization of its first marginal. -/
theorem transfer_sampling : transferType.{u,v,w} := by
  intro S T mS mT _ hT M _
  obtain ⟨K, hK, hM⟩ := disintegration hT M (M.map Prod.fst) rfl
  have := hK
  obtain ⟨g, hg, hfiber⟩ := exists_kernel_randomization K hT
  refine ⟨g, hg, ?_⟩
  intro Ω mΩ P _ X V hX hV hlawX hlawV hind
  exact (kernel_randomization_jointLaw K g hg hfiber P X V _ hX hV
    hlawX hlawV hind).trans hM.symm

/-- A measurable sampler with any noise space and pointwise prescribed fiber
laws transports a product input law to the measure induced by the kernel. -/
lemma sampling_map_product {S : Type u} {A : Type v} {T : Type w}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace T]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure A) [IsProbabilityMeasure ν]
    (K : Kernel S T) [IsMarkovKernel K]
    (f : S × A → T) (hf : Measurable f)
    (hfiber : ∀ s, ν.map (fun a => f (s, a)) = K s) :
    (μ.prod ν).map (fun p => (p.1, f p)) = μ.compProd K := by
  have hm : Measurable (fun p : S × A => (p.1, f p)) := measurable_fst.prodMk hf
  ext C hC
  rw [Measure.map_apply hm hC, Measure.prod_apply (hm hC), Measure.compProd_apply hC]
  apply lintegral_congr
  intro s
  have hs : Measurable (fun a => f (s, a)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [← hfiber s, Measure.map_apply hs (measurable_prodMk_left hC)]
  rfl

/-- Two independent noise coordinates give the product of the conditional fiber
laws, without any regularity assumption on the first coordinate. -/
lemma two_sampler_jointLaw {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) (L : Kernel S U) [IsMarkovKernel K] [IsMarkovKernel L]
    (g : S × UnitInterval → T) (h : S × UnitInterval → U)
    (hg : Measurable g) (hh : Measurable h)
    (hgK : ∀ s, uniform.map (fun z => g (s, z)) = K s)
    (hhL : ∀ s, uniform.map (fun z => h (s, z)) = L s)
    {Ω : Type x} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (V₁ V₂ : Ω → UnitInterval)
    (hX : Measurable X) (hV₁ : Measurable V₁) (hV₂ : Measurable V₂)
    (hlaw₁ : P.map V₁ = uniform) (hlaw₂ : P.map V₂ = uniform)
    (hindV : IndepFun V₁ V₂ P) (hindX : IndepFun X (fun ω => (V₁ ω, V₂ ω)) P) :
    P.map (fun ω => (X ω, (g (X ω, V₁ ω), h (X ω, V₂ ω)))) =
      (P.map X).compProd (K ×ₖ L) := by
  have : IsProbabilityMeasure uniform := hlaw₁ ▸ inferInstance
  let f : S × (UnitInterval × UnitInterval) → T × U :=
    fun p => (g (p.1, p.2.1), h (p.1, p.2.2))
  have hf : Measurable f :=
    (hg.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      (hh.comp (measurable_fst.prodMk measurable_snd.snd))
  have hfiber : ∀ s, (uniform.prod uniform).map (fun a => f (s, a)) = (K ×ₖ L) s := by
    intro s
    have hgs : Measurable (fun z => g (s, z)) :=
      hg.comp (measurable_const.prodMk measurable_id)
    have hhs : Measurable (fun z => h (s, z)) :=
      hh.comp (measurable_const.prodMk measurable_id)
    rw [Kernel.prod_apply, ← hgK s, ← hhL s,
      Measure.map_prod_map uniform uniform hgs hhs]
    rfl
  have hinput : P.map (fun ω => (X ω, (V₁ ω, V₂ ω))) =
      (P.map X).prod (uniform.prod uniform) := by
    rw [hindX.map_prod_eq_prod_map_map hX.aemeasurable (hV₁.prodMk hV₂).aemeasurable,
      hindV.map_prod_eq_prod_map_map hV₁.aemeasurable hV₂.aemeasurable, hlaw₁, hlaw₂]
  change P.map ((fun p => (p.1, f p)) ∘ (fun ω => (X ω, (V₁ ω, V₂ ω)))) = _
  rw [← Measure.map_map (measurable_fst.prodMk hf) (hX.prodMk (hV₁.prodMk hV₂)), hinput]
  exact sampling_map_product (P.map X) (uniform.prod uniform) (K ×ₖ L) f hf hfiber

/-- The two sampled coordinates realize exactly the unique conditionally
independent gluing of the prescribed joint probabilities. -/
theorem independent_sampling : independentSamplingType.{u,v,w,x} := by
  intro S T U mS mT mU _ _ hT hU μ M N _ _ hM hN
  have : IsProbabilityMeasure μ := hM ▸ inferInstance
  obtain ⟨K, hK, hMK⟩ := disintegration hT M μ hM
  obtain ⟨L, hL, hNL⟩ := disintegration hU N μ hN
  have := hK
  have := hL
  obtain ⟨g, hg, hgK⟩ := exists_kernel_randomization K hT
  obtain ⟨h, hh, hhL⟩ := exists_kernel_randomization L hU
  refine ⟨g, h, hg, hh, ?_⟩
  intro Ω mΩ P _ X V₁ V₂ hX hV₁ hV₂ hlawX hlaw₁ hlaw₂ hindV hindX
  have hQ := two_sampler_jointLaw K L g h hg hh hgK hhL P X V₁ V₂ hX hV₁ hV₂
    hlaw₁ hlaw₂ hindV hindX
  rw [hlawX] at hQ
  have hMK' : M = μ.compProd K := hMK
  have hNL' : N = μ.compProd L := hNL
  constructor
  · exact (conditional_gluing_formula hT hU μ M N K L hMK' hNL' _).mpr hQ
  · intro Λ hΛ
    exact ((conditional_gluing_formula hT hU μ M N K L hMK' hNL' Λ).mp hΛ).trans hQ.symm

/-- Restricted Lebesgue measure on the closed unit interval has mass one. -/
lemma unitUniform_isProbabilityMeasure : IsProbabilityMeasure uniform := by
  have hmap : uniform.map (Subtype.val : UnitInterval → ℝ) =
      (volume : Measure ℝ).restrict (Icc 0 1) :=
    map_comap_subtype_coe measurableSet_Icc volume
  have : IsProbabilityMeasure (uniform.map (Subtype.val : UnitInterval → ℝ)) := by
    rw [hmap]
    exact unitInterval_isProbabilityMeasure
  exact Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable

/-- Two Lebesgue probability coordinates provide the required independent
uniforms while preserving the whole original probability space as a marginal. -/
theorem product_enlargement : enlargementType.{u,v} := by
  intro Ω S mΩ mS P _ X hX
  have : IsProbabilityMeasure uniform := unitUniform_isProbabilityMeasure
  let P' := P.prod (uniform.prod uniform)
  have hfst : P'.map Prod.fst = P := by
    simp [P']
  have hsnd : P'.map Prod.snd = uniform.prod uniform := by
    simp [P']
  have hX' : P'.map (fun p => X p.1) = P.map X := by
    change P'.map (X ∘ Prod.fst) = _
    rw [← Measure.map_map hX measurable_fst, hfst]
  have h₁ : P'.map (fun p => p.2.1) = uniform := by
    change P'.map (Prod.fst ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_fst measurable_snd, hsnd]
    simp
  have h₂ : P'.map (fun p => p.2.2) = uniform := by
    change P'.map (Prod.snd ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_snd measurable_snd, hsnd]
    simp
  refine ⟨inferInstance, hX.comp measurable_fst, measurable_snd.fst,
    measurable_snd.snd, hfst, hX', h₁, h₂, ?_, ?_⟩
  · apply (indepFun_iff_map_prod_eq_prod_map_map
      measurable_snd.fst.aemeasurable measurable_snd.snd.aemeasurable).mpr
    rw [h₁, h₂]
    exact hsnd
  · exact indepFun_prod hX measurable_id

end ProbabilityFoundations.Ch04
