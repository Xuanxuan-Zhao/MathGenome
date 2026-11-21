import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.ConditionalGluing
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.Disintegration
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.DisintegrationUniqueness
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.ConditionalProductCriterion
import Mathlib.Probability.Kernel.Composition.Lemmas

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch04
universe u v w x
open Specs.ProbabilityFoundations.Ch04.ConditionalGluing
open Specs.ProbabilityFoundations.Ch04.ConditionalProductCriterion

noncomputable def gluedLaw : gluedLawType.{u,v,w} := @gluedLawValue
noncomputable def IsConditionalGluing : gluingType.{u,v,w} := @gluingValue

/-- Integrals of a pulled-back kernel over conditioning events are exactly
integrals over the corresponding base events. This uses the original sigma-algebra. -/
lemma kernel_setLIntegral_comap {Ω : Type u} {S : Type v} {T : Type w}
    [F : MeasurableSpace Ω] [mS : MeasurableSpace S] [MeasurableSpace T]
    (P : Measure Ω) (X : Ω → S) (hX : Measurable X)
    (K : Kernel S T) (A : Set S) (hA : MeasurableSet A)
    (B : Set T) (hB : MeasurableSet B) :
    (∫⁻ ω in X ⁻¹' A, K (X ω) B ∂P.trim hX.comap_le) =
      ∫⁻ s in A, K s B ∂P.map X := by
  let G := MeasurableSpace.comap X mS
  have hf : Measurable[G] (fun ω => K (X ω) B) :=
    (K.measurable_coe hB).comp (comap_measurable X)
  rw [← lintegral_indicator (show MeasurableSet[G] (X ⁻¹' A) from
    (comap_measurable X) hA), lintegral_trim hX.comap_le
      (hf.indicator ((comap_measurable X) hA)),
    ← lintegral_indicator hA]
  rw [@lintegral_map Ω S F mS P _ X ((K.measurable_coe hB).indicator hA) hX]
  rfl

/-- A disintegration of a joint law pulls back to a conditional law given σ(X). -/
lemma conditionalLaw_of_jointLaw {Ω : Type u} {S : Type v} {T : Type w}
    [F : MeasurableSpace Ω] [mS : MeasurableSpace S] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (Y : Ω → T) (hX : Measurable X) (hY : Measurable Y)
    (K : Kernel S T) [IsMarkovKernel K]
    (h : P.map (fun ω => (X ω, Y ω)) = (P.map X).compProd K) :
    IsConditionalLaw P (MeasurableSpace.comap X mS) hX.comap_le Y
      (K.comap X (comap_measurable X)) := by
  intro E hE B hB
  obtain ⟨A, hA, rfl⟩ := hE
  change (∫⁻ ω in X ⁻¹' A, K (X ω) B ∂P.trim hX.comap_le) = _
  rw [kernel_setLIntegral_comap P X hX K A hA B hB]
  have := congrArg (fun ν : Measure (S × T) => ν (A ×ˢ B)) h
  rw [Measure.map_apply (hX.prodMk hY) (hA.prod hB),
    Measure.compProd_apply_prod hA hB] at this
  exact this.symm

/-- Conversely, the event identities of a pulled-back conditional law determine
its joint law. -/
lemma jointLaw_of_conditionalLaw {Ω : Type u} {S : Type v} {T : Type w}
    [F : MeasurableSpace Ω] [mS : MeasurableSpace S] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (Y : Ω → T) (hX : Measurable X) (hY : Measurable Y)
    (K : Kernel S T) [IsMarkovKernel K]
    (h : IsConditionalLaw P (MeasurableSpace.comap X mS) hX.comap_le Y
      (K.comap X (comap_measurable X))) :
    P.map (fun ω => (X ω, Y ω)) = (P.map X).compProd K := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply (hX.prodMk hY) (hA.prod hB),
    Measure.compProd_apply_prod hA hB]
  exact (h (X ⁻¹' A) ((comap_measurable X) hA) B hB).symm.trans
    (kernel_setLIntegral_comap P X hX K A hA B hB)

/-- Under conditional independence, the two specified disintegrations determine
all of the triple law. -/
lemma jointLaw_product_of_independent {Ω : Type x} {S : Type u} {T : Type v} {U : Type w}
    [F : MeasurableSpace Ω] [mS : MeasurableSpace S]
    [mT : MeasurableSpace T] [mU : MeasurableSpace U]
    (hT : IsStandardBorel T) (hU : IsStandardBorel U)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (Y : Ω → T) (Z : Ω → U)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (K : Kernel S T) (L : Kernel S U) [IsMarkovKernel K] [IsMarkovKernel L]
    (hKY : P.map (fun ω => (X ω, Y ω)) = (P.map X).compProd K)
    (hLZ : P.map (fun ω => (X ω, Z ω)) = (P.map X).compProd L)
    (hind : IsConditionallyIndependent (MeasurableSpace.comap X mS) P Y Z) :
    P.map (fun ω => (X ω, (Y ω, Z ω))) = (P.map X).compProd (K ×ₖ L) := by
  let G := MeasurableSpace.comap X mS
  let K0 := K.comap X (comap_measurable X)
  let L0 := L.comap X (comap_measurable X)
  let H0 := (K ×ₖ L).comap X (comap_measurable X)
  have hK0 := @conditionalLaw_of_jointLaw Ω S T F mS mT P _ X Y hX hY K _ hKY
  have hL0 := @conditionalLaw_of_jointLaw Ω S U F mS mU P _ X Z hX hZ L _ hLZ
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  let : Nonempty (T × U) := Nonempty.map (fun ω => (Y ω, Z ω)) inferInstance
  obtain ⟨J, hJ, hJlaw⟩ := @conditional_law Ω (T × U) F (mT.prod mU) _ P _ G hX.comap_le
    (standardBorel_binary_product T U hT hU) (fun ω => (Y ω, Z ω)) (hY.prodMk hZ)
  have := hJ
  obtain ⟨E, hE, hzero, heq⟩ := (@conditional_product_criterion Ω T U F mT mU P _ G hX.comap_le
    hT hU Y Z hY hZ K0 L0 J _ _ _ hK0 hL0 hJlaw).mp hind
  apply @jointLaw_of_conditionalLaw Ω S (T × U) F mS (mT.prod mU) P _
    X (fun ω => (Y ω, Z ω)) hX (hY.prodMk hZ) (K ×ₖ L) _
  intro A hA B hB
  have hae : (fun ω => J ω B) =ᵐ[P] (fun ω => H0 ω B) := by
    have hmem : ∀ᵐ ω ∂P, ω ∉ E := by rw [ae_iff]; simpa using hzero
    filter_upwards [hmem] with ω hω
    change J ω B = (K ×ₖ L) (X ω) B
    rw [heq ω hω, Kernel.prod_apply]
    rfl
  have hae' := ae_eq_trim_of_measurable hX.comap_le (J.measurable_coe hB)
    (H0.measurable_coe hB) hae
  exact (lintegral_congr_ae (ae_restrict_of_ae hae')).symm.trans (hJlaw A hA B hB)

/-- The converse direction of the product criterion for a law disintegrated over
an arbitrary measurable first coordinate. -/
lemma independent_of_jointLaw_product {Ω : Type x} {S : Type u} {T : Type v} {U : Type w}
    [F : MeasurableSpace Ω] [mS : MeasurableSpace S]
    [mT : MeasurableSpace T] [mU : MeasurableSpace U]
    (hT : IsStandardBorel T) (hU : IsStandardBorel U)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (Y : Ω → T) (Z : Ω → U)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (K : Kernel S T) (L : Kernel S U) [IsMarkovKernel K] [IsMarkovKernel L]
    (hKY : P.map (fun ω => (X ω, Y ω)) = (P.map X).compProd K)
    (hLZ : P.map (fun ω => (X ω, Z ω)) = (P.map X).compProd L)
    (hH : P.map (fun ω => (X ω, (Y ω, Z ω))) = (P.map X).compProd (K ×ₖ L)) :
    IsConditionallyIndependent (MeasurableSpace.comap X mS) P Y Z := by
  let K0 := K.comap X (comap_measurable X)
  let L0 := L.comap X (comap_measurable X)
  let H0 := (K ×ₖ L).comap X (comap_measurable X)
  apply (conditional_product_criterion P _ hX.comap_le hT hU Y Z hY hZ K0 L0 H0
    (conditionalLaw_of_jointLaw P X Y hX hY K hKY)
    (conditionalLaw_of_jointLaw P X Z hX hZ L hLZ)
    (conditionalLaw_of_jointLaw P X (fun ω => (Y ω, Z ω)) hX (hY.prodMk hZ) (K ×ₖ L) hH)).mpr
  refine ⟨∅, @MeasurableSet.empty Ω (MeasurableSpace.comap X mS), measure_empty, ?_⟩
  intro ω _
  exact Kernel.prod_apply K L (X ω)

lemma gluedLaw_projections {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (K : Kernel S T) (L : Kernel S U) [IsMarkovKernel K] [IsMarkovKernel L] :
    (gluedLaw μ K L).map (fun p => (p.1, p.2.1)) = μ.compProd K ∧
    (gluedLaw μ K L).map (fun p => (p.1, p.2.2)) = μ.compProd L := by
  constructor
  · change ((μ.compProd (K ×ₖ L)).map (Prod.map id Prod.fst)) = _
    rw [← Measure.compProd_map measurable_fst]
    exact congrArg (Measure.compProd μ) ((Kernel.fst_eq _).symm.trans (Kernel.fst_prod K L))
  · change ((μ.compProd (K ×ₖ L)).map (Prod.map id Prod.snd)) = _
    rw [← Measure.compProd_map measurable_snd]
    exact congrArg (Measure.compProd μ) ((Kernel.snd_eq _).symm.trans (Kernel.snd_prod K L))

theorem conditional_gluing_formula : formulaType.{u,v,w} := by
  intro S T U mS mT mU hT hU μ _ M N K L _ _ hM hN Λ
  constructor
  · rintro ⟨hΛ, hΛM, hΛN, hind⟩
    have : IsProbabilityMeasure Λ := hΛ
    have hfst : Λ.map Prod.fst = μ := by
      have h := congrArg (fun ν : Measure (S × T) => ν.map Prod.fst) (hΛM.trans hM)
      rw [Measure.map_map measurable_fst (measurable_fst.prodMk measurable_snd.fst)] at h
      exact h.trans (Measure.fst_compProd μ K)
    have h := jointLaw_product_of_independent hT hU Λ Prod.fst
      (fun p => p.2.1) (fun p => p.2.2) measurable_fst measurable_snd.fst measurable_snd.snd
      K L (by rw [hfst]; exact hΛM.trans hM) (by rw [hfst]; exact hΛN.trans hN) hind
    change Λ = μ.compProd (K ×ₖ L)
    simpa only [show (fun p : S × (T × U) => (p.1, (p.2.1, p.2.2))) = id from rfl,
      Measure.map_id, hfst] using h
  · intro hΛ
    subst Λ
    have hprob : IsProbabilityMeasure (gluedLaw μ K L) := by
      change IsProbabilityMeasure (μ.compProd (K ×ₖ L)); infer_instance
    have hfst : (gluedLaw μ K L).map Prod.fst = μ := Measure.fst_compProd _ _
    obtain ⟨hprojT, hprojU⟩ := gluedLaw_projections μ K L
    refine ⟨hprob, hprojT.trans hM.symm, hprojU.trans hN.symm, ?_⟩
    apply independent_of_jointLaw_product hT hU (gluedLaw μ K L) Prod.fst
      (fun p => p.2.1) (fun p => p.2.2) measurable_fst measurable_snd.fst measurable_snd.snd K L
    · rw [hfst]; exact hprojT
    · rw [hfst]; exact hprojU
    · rw [hfst]
      exact Measure.map_id

theorem conditional_gluing : existenceUniqueType.{u,v,w} := by
  intro S T U mS mT mU hT hU μ M N _ _ hM hN
  have : IsProbabilityMeasure μ := by
    rw [← hM]
    infer_instance
  let : Nonempty (S × T) := nonempty_of_isProbabilityMeasure M
  let : Nonempty (S × U) := nonempty_of_isProbabilityMeasure N
  let : Nonempty T := Nonempty.map Prod.snd (inferInstance : Nonempty (S × T))
  let : Nonempty U := Nonempty.map Prod.snd (inferInstance : Nonempty (S × U))
  obtain ⟨K, hK, hMK⟩ := disintegration hT M μ hM
  obtain ⟨L, hL, hNL⟩ := disintegration hU N μ hN
  have := hK
  have := hL
  refine ⟨gluedLaw μ K L, ?_, ?_⟩
  · exact (conditional_gluing_formula hT hU μ M N K L hMK hNL _).mpr rfl
  · intro Λ hΛ
    exact (conditional_gluing_formula hT hU μ M N K L hMK hNL Λ).mp hΛ

theorem gluedLaw_choice_independent : choiceIndependentType.{u,v,w} := by
  intro S T U mS mT mU hT hU μ _ K K' L L' _ _ _ _ hK hL
  let : StandardBorelSpace T := (isStandardBorel_iff T).mp hT
  let : StandardBorelSpace U := (isStandardBorel_iff U).mp hU
  apply Measure.compProd_congr
  filter_upwards [Kernel.ae_eq_of_compProd_eq hK, Kernel.ae_eq_of_compProd_eq hL] with s hs ht
  simp only [Kernel.prod_apply, hs, ht]

end ProbabilityFoundations.Ch04
