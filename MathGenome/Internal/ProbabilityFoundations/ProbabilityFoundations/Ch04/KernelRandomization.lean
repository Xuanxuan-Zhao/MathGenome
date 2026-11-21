import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelRandomization
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.StandardBorel
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.RealKernelQuantile
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelMeasure
import Mathlib.Probability.Kernel.Composition.MapComap

open MeasureTheory ProbabilityTheory Set

namespace ProbabilityFoundations.Ch04

universe u v w

private noncomputable abbrev uniform := Specs.ProbabilityFoundations.Ch04.KernelRandomization.unitUniform

private theorem uniform_map_coe :
    (uniform).map (Subtype.val : Icc (0 : ℝ) 1 → ℝ) =
      (volume : Measure ℝ).restrict (Icc 0 1) :=
  map_comap_subtype_coe measurableSet_Icc volume

private theorem uniform_probability : IsProbabilityMeasure uniform := by
  have : IsProbabilityMeasure (uniform.map (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) := by
    rw [uniform_map_coe]
    exact unitInterval_isProbabilityMeasure
  exact Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable

/-- A Borel decoder extended to the whole real line gives a measurable sampler.
Its composition with the coding is the identity everywhere, so the transported
fiber law is preserved separately at every base point. -/
theorem exists_kernel_randomization
    {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T] [Nonempty T]
    (K : Kernel S T) [IsMarkovKernel K] (hT : IsStandardBorel T) :
    ∃ g : S × Icc (0 : ℝ) 1 → T, Measurable g ∧
      ∀ s, Measure.map (fun z => g (s, z)) uniform = K s := by
  classical
  obtain ⟨B, hB, ⟨e⟩⟩ := exists_real_coding T hT
  obtain ⟨d, hd, hde⟩ := (MeasurableEmbedding.subtype_coe hB).exists_measurable_extend
    e.symm.measurable (fun _ => inferInstance)
  let c : T → ℝ := fun t => (e t : ℝ)
  have hc : Measurable c := measurable_subtype_coe.comp e.measurable
  have hdc : d ∘ c = id := by
    funext t
    exact (congrFun hde (e t)).trans (e.symm_apply_apply t)
  let L := K.map c
  have : IsMarkovKernel L := Kernel.IsMarkovKernel.map K hc
  let q : S × Icc (0 : ℝ) 1 → ℝ := fun p => realKernelQuantile L p.1 p.2
  have hq : Measurable q := measurable_realKernelQuantile_unitInterval L
  refine ⟨d ∘ q, hd.comp hq, ?_⟩
  intro s
  have hqs : Measurable (realKernelQuantile L s) :=
    (measurable_realKernelQuantile L).comp (measurable_const.prodMk measurable_id)
  have hfiber : uniform.map (fun z : Icc (0 : ℝ) 1 => realKernelQuantile L s z) = L s := by
    rw [← realKernelQuantile_map_uniform L s, ← uniform_map_coe,
      Measure.map_map hqs measurable_subtype_coe]
    rfl
  change uniform.map (d ∘ (fun z : Icc (0 : ℝ) 1 => realKernelQuantile L s z)) = K s
  calc
    _ = (uniform.map (fun z : Icc (0 : ℝ) 1 => realKernelQuantile L s z)).map d :=
      (Measure.map_map hd (hqs.comp measurable_subtype_coe)).symm
    _ = K s := by
      rw [hfiber, Kernel.map_apply K hc s, Measure.map_map hd hc, hdc, Measure.map_id]

/-- Independence supplies the product input law. The fiber identity then
identifies the pushforward on every product-measurable set by section integration. -/
theorem kernel_randomization_jointLaw
    {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (K : Kernel S T) [IsMarkovKernel K]
    (g : S × Icc (0 : ℝ) 1 → T) (hg : Measurable g)
    (hfiber : ∀ s, Measure.map (fun z => g (s, z)) uniform = K s)
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (V : Ω → Icc (0 : ℝ) 1) (μ : Measure S)
    (hX : Measurable X) (hV : Measurable V) (hlawX : P.map X = μ)
    (hlawV : P.map V = uniform) (hind : IndepFun X V P) :
    P.map (fun ω => (X ω, g (X ω, V ω))) = kernelMeasure μ K := by
  have : IsProbabilityMeasure uniform := uniform_probability
  have : IsProbabilityMeasure μ := hlawX ▸ inferInstance
  let f : S × Icc (0 : ℝ) 1 → S × T := fun p => (p.1, g p)
  have hf : Measurable f := measurable_fst.prodMk hg
  have hinput : P.map (fun ω => (X ω, V ω)) = μ.prod uniform := by
    rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hV.aemeasurable, hlawX, hlawV]
  change P.map (f ∘ (fun ω => (X ω, V ω))) = _
  rw [← Measure.map_map hf (hX.prodMk hV), hinput]
  ext C hC
  rw [Measure.map_apply hf hC, Measure.prod_apply (hf hC), kernelMeasure_apply μ K C hC]
  apply lintegral_congr
  intro s
  have hs : Measurable (fun z => g (s, z)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  rw [← hfiber s]
  rw [Measure.map_apply hs (show MeasurableSet {y | (s, y) ∈ C} from
    measurable_prodMk_left hC)]
  rfl

end ProbabilityFoundations.Ch04
