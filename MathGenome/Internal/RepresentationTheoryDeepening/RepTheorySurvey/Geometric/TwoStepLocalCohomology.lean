import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TwoStepLocalCohomology
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConstantSheafComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficientsCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.RealProjectiveHomology
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Algebra.Category.Grp.Injective
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.NilpotentConeChart
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology Filter
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
open scoped ZeroObject unitInterval

namespace RepTheorySurvey.Geometric.TwoStepLocalCohomology

open TwoStepLocalCohomologySpecs NilpotentConeChartSpecs
open Analytic Analytic.ConstantSheafCohomology Analytic.SingularCochains

private theorem radialBasisOnCone (h : NilpotentConeChartSpecs.Expected.RadialNeighborhoods) :
    (nhds coneVertex).HasBasis (fun _ : PositiveRadius ↦ True)
      (fun r ↦ {z : Cone | radialSize z < r.val}) := by
  apply Filter.hasBasis_iff.mpr
  intro U
  constructor
  · intro hU
    obtain ⟨r, hr, hsub⟩ := h.2.2.1 U hU
    exact ⟨⟨r, hr⟩, trivial, hsub⟩
  · rintro ⟨r, -, hr⟩
    exact mem_of_superset (h.2.1 r.val r.property).2 hr

private theorem radialBasisOnChart (c : RadialChart)
    (h : NilpotentConeChartSpecs.Expected.RadialNeighborhoods) :
    (nhds c.vertex).HasBasis (fun _ : PositiveRadius ↦ True)
      (fun r ↦ (c.balls.obj r : Set ChartSpace)) := by
  rw [← c.toLattice.map_nhds_eq]
  convert (radialBasisOnCone h).map c.toLattice using 2
  ext x
  change (radialSize (c.toLattice.symm x) < _ ↔ x ∈ _)
  constructor
  · intro hx
    exact ⟨c.toLattice.symm x, hx, c.toLattice.apply_symm_apply x⟩
  · rintro ⟨z, hz, rfl⟩
    simpa only [Set.mem_ofPred_eq, c.toLattice.symm_apply_apply] using hz

theorem radialNeighborhoodBasis_conditional
    (analytic : NilpotentConeChartSpecs.Expected.AnalyticQuadraticChart)
    (_antipodal : NilpotentConeChartSpecs.Expected.AntipodalQuotientHomeomorphism)
    (_polynomial : NilpotentConeChartSpecs.Expected.PolynomialParametrization)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods)
    (_reduced : NilpotentConeChartSpecs.Expected.ReducedQuadraticChart) :
    TwoStepLocalCohomologySpecs.Expected.RadialNeighborhoodBasis := by
  obtain ⟨_, hopen, e, eL, he, heL, hx⟩ := analytic
  let c : RadialChart := ⟨hopen, eL, fun z ↦ (heL z).trans (congrArg _ (he z)), hx⟩
  have h := radialBasisOnChart c radial
  refine ⟨c, h, ?_⟩
  rw [← c.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq c.vertex]
  exact h.map Subtype.val

private def ballHomeomorph (c : RadialChart) (r : PositiveRadius) :
    RadialBall r.val ≃ₜ (c.balls.obj r) where
  toFun z := ⟨c.toLattice z.val, by
    change radialSize (c.toLattice.symm (c.toLattice z.val)) < r.val
    simpa only [c.toLattice.symm_apply_apply] using z.property⟩
  invFun x := ⟨c.toLattice.symm x.val, x.property⟩
  left_inv z := Subtype.ext (c.toLattice.symm_apply_apply z.val)
  right_inv x := Subtype.ext (c.toLattice.apply_symm_apply x.val)
  continuous_toFun := (c.toLattice.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (c.toLattice.symm.continuous.comp continuous_subtype_val).subtype_mk _

private theorem ballContractible (c : RadialChart)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods) (r : PositiveRadius) :
    ContractibleSpace (c.balls.obj r) := by
  have hr := radial.2.2.2
  obtain ⟨_, _, _, _, _, h, _⟩ := hr
  obtain ⟨H⟩ := h r.val r.property
  letI : ContractibleSpace (RadialBall r.val) :=
    (contractible_iff_id_nullhomotopic _).mpr ⟨_, ⟨H.toHomotopy⟩⟩
  exact (ballHomeomorph c r).symm.contractibleSpace

private theorem openBasis_of_openEmbedding {X Y : TopCat} {f : X → Y}
    (h : IsOpenEmbedding f) (hY : HasContractibleOpenBasis Y) :
    HasContractibleOpenBasis X := by
  intro x U hx
  let W : Opens Y := ⟨f '' (U : Set X), h.isOpenMap _ U.isOpen⟩
  obtain ⟨V, hxV, hVW, hV⟩ := hY (f x) W ⟨x, hx, rfl⟩
  let P : Opens X := ⟨f ⁻¹' (V : Set Y), V.isOpen.preimage h.continuous⟩
  refine ⟨P, hxV, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, hz'⟩ := hVW hy
    exact h.injective hz' ▸ hz
  · have hVr : (V : Set Y) ⊆ Set.range f := fun y hy ↦
      let ⟨z, _, hz⟩ := hVW hy
      ⟨z, hz⟩
    exact (h.isEmbedding.homeomorphOfSubsetRange hVr).contractibleSpace_iff.mpr hV

private theorem comparisonTopology_of_openEmbedding {X Y : TopCat} {f : X → Y}
    (hf : IsOpenEmbedding f) (hY : ComparisonTopology Y) : ComparisonTopology X := by
  obtain ⟨hY₁, hY₂, hY₃, hY₄⟩ := hY
  letI := hY₁
  letI := hY₂
  letI := hY₃
  exact ⟨hf.isInducing.secondCountableTopology, hf.locallyCompactSpace, hf.isEmbedding.t2Space,
    openBasis_of_openEmbedding hf hY₄⟩

private theorem normedOpenBasis (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : HasContractibleOpenBasis (TopCat.of E) := by
  intro x U hx
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  refine ⟨⟨Metric.ball x ε, Metric.isOpen_ball⟩, Metric.mem_ball_self hε, hsub, ?_⟩
  exact (convex_ball x ε).contractibleSpace ⟨x, Metric.mem_ball_self hε⟩

private def nonzeroV : Opens (TopCat.of Cone) :=
  ⟨{z | z.val.2.1 ≠ 0},
    isOpen_ne_fun ((continuous_fst.comp continuous_snd).comp continuous_subtype_val)
      continuous_const⟩

private def nonzeroSecond : Opens (TopCat.of (ℂ × ℂ)) :=
  ⟨{z | z.2 ≠ 0}, isOpen_ne_fun continuous_snd continuous_const⟩

private def coneNonzeroVHomeomorph : nonzeroV ≃ₜ nonzeroSecond where
  toFun z := ⟨(z.val.val.1, z.val.val.2.1), z.property⟩
  invFun z :=
    ⟨⟨(z.val.1, z.val.2, -(z.val.1 ^ 2) / z.val.2), by
      change z.val.1 ^ 2 + z.val.2 * (-(z.val.1 ^ 2) / z.val.2) = 0
      have hz : z.val.2 ≠ 0 := z.property
      field_simp
      ring⟩, z.property⟩
  left_inv z := by
    have h := z.val.property
    change _ ^ 2 + _ * _ = 0 at h
    have hz : z.val.val.2.1 ≠ 0 := z.property
    have hw : -(z.val.val.1 ^ 2) / z.val.val.2.1 = z.val.val.2.2 := by
      apply (div_eq_iff hz).2
      linear_combination -h
    exact Subtype.ext (Subtype.ext (Prod.ext rfl (Prod.ext rfl hw)))
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    let a : nonzeroSecond → ℂ := fun x ↦ x.val.1
    let b : nonzeroSecond → ℂ := fun x ↦ x.val.2
    have ha : Continuous a := continuous_fst.comp continuous_subtype_val
    have hb : Continuous b := continuous_snd.comp continuous_subtype_val
    exact (ha.prodMk (hb.prodMk ((ha.pow 2).neg.div hb fun z ↦ z.property))).subtype_mk
      _ |>.subtype_mk _

private def swapCone : Cone ≃ₜ Cone where
  toFun z := ⟨(z.val.1, z.val.2.2, z.val.2.1), by simpa [mul_comm] using z.property⟩
  invFun z := ⟨(z.val.1, z.val.2.2, z.val.2.1), by simpa [mul_comm] using z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.prodMk ((continuous_snd.comp continuous_snd).prodMk
      (continuous_fst.comp continuous_snd))).comp continuous_subtype_val).subtype_mk
      (fun z ↦ by simpa [Function.comp_def, mul_comm] using z.property)
  continuous_invFun :=
    ((continuous_fst.prodMk ((continuous_snd.comp continuous_snd).prodMk
      (continuous_fst.comp continuous_snd))).comp continuous_subtype_val).subtype_mk
      (fun z ↦ by simpa [Function.comp_def, mul_comm] using z.property)

private def nonzeroVChart : nonzeroSecond → Cone :=
  fun z ↦ (coneNonzeroVHomeomorph.symm z).val

private theorem nonzeroVChart_open : IsOpenEmbedding nonzeroVChart :=
  nonzeroV.isOpen.isOpenEmbedding_subtypeVal.comp coneNonzeroVHomeomorph.symm.isOpenEmbedding

private theorem openBasis_chart (c : RadialChart)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods) :
    HasContractibleOpenBasis ChartSpace := by
  intro x U hx
  by_cases hz : x = c.vertex
  · subst x
    obtain ⟨r, -, hr⟩ := (radialBasisOnChart c radial).mem_iff.mp (U.isOpen.mem_nhds hx)
    have hr' := (radialBasisOnChart c radial).mem_of_mem (i := r) trivial
    exact ⟨c.balls.obj r, mem_of_mem_nhds hr', hr, ballContractible c radial r⟩
  · have hModel : HasContractibleOpenBasis (TopCat.of nonzeroSecond) :=
      openBasis_of_openEmbedding nonzeroSecond.isOpen.isOpenEmbedding_subtypeVal
        (normedOpenBasis (ℂ × ℂ))
    let z := c.toLattice.symm x
    have hz' : z ≠ coneVertex := fun h ↦ hz (c.toLattice.symm_apply_eq.mp h)
    have hlocal (e : Cone ≃ₜ Cone) (hv : (e z).val.2.1 ≠ 0) :
        ∃ V : Opens ChartSpace, x ∈ V ∧ V ≤ U ∧ ContractibleSpace V := by
      let f : nonzeroSecond → ChartSpace := c.toLattice ∘ e.symm ∘ nonzeroVChart
      have hf : IsOpenEmbedding f := c.toLattice.isOpenEmbedding.comp
        (e.symm.isOpenEmbedding.comp nonzeroVChart_open)
      let y : nonzeroSecond := coneNonzeroVHomeomorph ⟨e z, hv⟩
      have hy : f y = x := by
        change c.toLattice (e.symm (coneNonzeroVHomeomorph.symm
          (coneNonzeroVHomeomorph ⟨e z, hv⟩)).val) = x
        rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply,
          c.toLattice.apply_symm_apply]
      let A : Opens (TopCat.of nonzeroSecond) :=
        ⟨f ⁻¹' (U : Set ChartSpace), U.isOpen.preimage hf.continuous⟩
      obtain ⟨W, hw, hwA, hc⟩ := hModel y A (show f y ∈ U from hy.symm ▸ hx)
      let V : Opens ChartSpace := ⟨f '' (W : Set nonzeroSecond), hf.isOpenMap _ W.isOpen⟩
      refine ⟨V, ⟨y, hw, hy⟩, ?_, (hf.isEmbedding.homeomorphImage _).symm.contractibleSpace_iff.mpr hc⟩
      rintro _ ⟨w, hw', rfl⟩
      exact hwA hw'
    by_cases hv : z.val.2.1 = 0
    · apply hlocal swapCone
      show z.val.2.2 ≠ 0
      intro hw
      have h := z.property
      change z.val.1 ^ 2 + z.val.2.1 * z.val.2.2 = 0 at h
      rw [hv, hw, zero_mul, add_zero] at h
      apply hz'
      apply Subtype.ext
      exact Prod.ext (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0) |>.mp h) (Prod.ext hv hw)
    · exact hlocal (Homeomorph.refl _) hv

private theorem chartTopology (c : RadialChart)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods) :
    ComparisonTopology ChartSpace := by
  have hc : IsClosed {z : ℂ × ℂ × ℂ | z.1 ^ 2 + z.2.1 * z.2.2 = 0} :=
    isClosed_eq ((continuous_fst.pow 2).add
      ((continuous_fst.comp continuous_snd).mul (continuous_snd.comp continuous_snd))) continuous_const
  haveI : LocallyCompactSpace Cone := hc.locallyCompactSpace
  refine ⟨c.toLattice.symm.isOpenEmbedding.isInducing.secondCountableTopology, ?_, ?_,
    openBasis_chart c radial⟩
  · exact c.toLattice.locallyCompactSpace_iff.mp inferInstance
  · exact c.toLattice.symm.isEmbedding.t2Space

open private sectionsCohomologyIso sectionsCohomologyIso_naturality from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConstantSheafComparison

private theorem supportedComparison (X : TopCat) (hX : ComparisonTopology X)
    {Z : Set X} (hZ : IsClosed Z) (q : ℤ) :
    Nonempty (singularSupported hZ q ≅ sheafSupported hZ q) := by
  letI := hX.1
  letI := hX.2.1
  letI := hX.2.2.1
  obtain ⟨hn, ha, _, _, hSupport, _, _, φ, hφ, hnat⟩ :=
    ConstantSheafComparison.comparison X hX.2.2.2
  let K : CochainComplex.Plus (Sheaves X) := ⟨sheafComplex X, 0, hn⟩
  let a : rationalComplex X ⟶ K := ObjectProperty.homMk (augmentation X)
  let e : DerivedCategory.Plus.Q.obj K ≅ LocalSheaf.sheafInDegreeZero (rational X) :=
    (asIso (DerivedCategory.Plus.Q.map a)).symm
  let i (U : Opens X) : (withoutClosed hZ).obj U ⟶ U := homOfLE inf_le_left
  let T := LocalSheaf.supportedSectionsOn hZ
  have (U : Opens X) : IsIso ((T U).rightDerivedFunctorPlusUnit.app K) :=
    (hSupport hZ U).1
  have hSupp (U : Opens X) :
      ∃ k : ((T U).mapCochainComplexPlus.obj K).obj ≅ (sectionSequence K.obj (i U)).X₁,
        k.hom ≫ (sectionSequence K.obj (i U)).f =
          ((LocalSheaf.supportedSectionsInclusion hZ U).mapCochainComplexPlus.app K).hom :=
    (hSupport hZ U).2
  choose κ hκ using hSupp
  let ρ {U V : Opens X} (j : U ⟶ V) : T V ⟶ T U :=
    Functor.whiskerLeft _ (LocalSheaf.sectionsRestriction j)
  have hκnat {U V : Opens X} (j : U ⟶ V) :
      ((ρ j).mapCochainComplexPlus.app K).hom ≫ (κ U).hom =
        (κ V).hom ≫ (sectionSequenceRestriction K.obj (i U) (i V)
          j ((withoutClosed hZ).map j)).τ₁ := by
    apply (cancel_mono (sectionSequence K.obj (i U)).f).mp
    simp only [Category.assoc, hκ U, ShortComplex.Hom.comm₁₂]
    rw [← Category.assoc, hκ V]
    ext1 n
    let α := ((LocalSheaf.supportedImageIso hZ).inv ≫ sectionsWithSupportInclusion hZ).app
      (K.obj.X n)
    exact α.hom.naturality j.op
  let S := (openPairs hZ).op ⋙ relativeCochainFunctor ℚ Values.{0}
  let C := HomologicalComplex.homologyFunctor Coeff.{0} (.up ℤ) q
  let η (U : Opens X) : S.obj (op U) ⟶ ((T U).mapCochainComplexPlus.obj K).obj :=
    (φ (i U)).τ₁ ≫ (κ U).inv
  have hη {U V : Opens X} (j : U ⟶ V) :
      S.map j.op ≫ η U = η V ≫ ((ρ j).mapCochainComplexPlus.app K).hom := by
    apply (cancel_mono (κ U).hom).mp
    have h := congrArg ShortComplex.Hom.τ₁ (hnat (i U) (i V) j ((withoutClosed hZ).map j))
    change S.map j.op ≫ (φ (i U)).τ₁ = (φ (i V)).τ₁ ≫ _ at h
    simpa only [η, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc, hκnat] using h
  have hηiso (U : Opens X) : IsIso (C.map (η U)) := by
    have := (hφ (i U)).2.2.1
    change IsIso (C.map ((φ (i U)).τ₁ ≫ (κ U).inv))
    rw [C.map_comp]
    change IsIso (HomologicalComplex.homologyMap (φ (i U)).τ₁ q ≫ C.map (κ U).inv)
    infer_instance
  refine ⟨NatIso.ofComponents (fun U ↦
    (haveI := hηiso U.unop
     asIso (C.map (η U.unop))) ≪≫ sectionsCohomologyIso (T U.unop) K e q) ?_⟩
  intro U V j
  change C.map (S.map j) ≫ (C.map (η V.unop) ≫ _) =
    (C.map (η U.unop) ≫ _) ≫ _
  have hj : S.map j ≫ η V.unop = η U.unop ≫ ((ρ j.unop).mapCochainComplexPlus.app K).hom :=
    hη j.unop
  rw [← Category.assoc, ← C.map_comp, hj, C.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact sectionsCohomologyIso_naturality (ρ j.unop) K e q

theorem radialSheafCohomology_conditional
    (_analytic : NilpotentConeChartSpecs.Expected.AnalyticQuadraticChart)
    (_antipodal : NilpotentConeChartSpecs.Expected.AntipodalQuotientHomeomorphism)
    (_polynomial : NilpotentConeChartSpecs.Expected.PolynomialParametrization)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods)
    (_reduced : NilpotentConeChartSpecs.Expected.ReducedQuadraticChart) :
    TwoStepLocalCohomologySpecs.Expected.RadialSheafCohomology := by
  intro c
  have h := chartTopology c radial
  letI := h.1
  letI := h.2.1
  letI := h.2.2.1
  refine ⟨h, fun r ↦ ⟨?_, ?_⟩, fun q ↦
    ⟨ConstantSheafComparison.absoluteCohomology ChartSpace h.2.2.2 q,
      supportedComparison ChartSpace h c.closedVertex q⟩⟩
  · exact comparisonTopology_of_openEmbedding
      (c.balls.obj r).isOpen.isOpenEmbedding_subtypeVal h
  · exact comparisonTopology_of_openEmbedding
      (c.puncturedBalls.obj r).isOpen.isOpenEmbedding_subtypeVal h

private theorem comparisonTopology_prod {X Y : TopCat} (hX : ComparisonTopology X)
    (hY : ComparisonTopology Y) : ComparisonTopology (TopCat.of (X × Y)) := by
  letI := hX.1
  letI := hX.2.1
  letI := hX.2.2.1
  letI := hY.1
  letI := hY.2.1
  letI := hY.2.2.1
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rintro ⟨x, y⟩ U hxy
  obtain ⟨A, B, hA, hxA, hB, hyB, hAB⟩ :=
    mem_nhds_prod_iff'.mp (U.isOpen.mem_nhds hxy)
  obtain ⟨V, hxV, hVA, hV⟩ := hX.2.2.2 x ⟨A, hA⟩ hxA
  obtain ⟨W, hyW, hWB, hW⟩ := hY.2.2.2 y ⟨B, hB⟩ hyB
  letI := hV
  letI := hW
  refine ⟨⟨(V : Set X) ×ˢ (W : Set Y), V.isOpen.prod W.isOpen⟩, ⟨hxV, hyW⟩,
    fun _ hz ↦ hAB ⟨hVA hz.1, hWB hz.2⟩, ?_⟩
  exact (Homeomorph.Set.prod (V : Set X) (W : Set Y)).contractibleSpace

open LatticeModelSpecs

private def jetConstant : JetRing 2 →+* ℂ :=
  Ideal.Quotient.lift _ PowerSeries.constantCoeff (by
    intro f hf
    rw [jetIdeal, Ideal.mem_span_singleton] at hf
    obtain ⟨g, rfl⟩ := hf
    simp [t])

private theorem jetConstant_eq (z : JetRing 2) : jetConstant z = jetCoefficients 2 z 0 := by
  obtain ⟨f, rfl⟩ :=
    (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk (jetIdeal 2))) z
  rw [show Ideal.Quotient.mk (jetIdeal 2) f = jetReduction 2 f from rfl, jetCoefficients_reduce]
  exact (PowerSeries.coeff_zero_eq_constantCoeff_apply f).symm

private theorem jet_unit_iff (z : JetRing 2) : IsUnit z ↔ jetConstant z ≠ 0 := by
  constructor
  · intro h
    exact (isUnit_iff_ne_zero.mp (h.map jetConstant))
  · obtain ⟨f, rfl⟩ :=
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk (jetIdeal 2))) z
    intro hf
    have hf' : IsUnit (PowerSeries.constantCoeff f) := isUnit_iff_ne_zero.mpr hf
    exact (PowerSeries.isUnit_iff_constantCoeff.mpr hf').map (Ideal.Quotient.mk (jetIdeal 2))

private def jetsHomeomorph : JetRing 2 ≃ₜ (Fin 2 → ℂ) :=
  (jetCoefficients 2).toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

private abbrev Jets := Matrix (Fin 2) (Fin 2) (JetRing 2)
private abbrev ComplexMatrix := Matrix (Fin 2) (Fin 2) ℂ

private def jetMatrixHomeomorph : Jets ≃ₜ (Fin 2 → Fin 2 → Fin 2 → ℂ) :=
  Homeomorph.piCongrRight fun _ ↦ Homeomorph.piCongrRight fun _ ↦ jetsHomeomorph

private def firstCoefficient : JetRing 2 →ₗ[ℂ] ℂ :=
  LinearMap.proj (1 : Fin 2) ∘ₗ (jetCoefficients 2).toLinearMap

private theorem firstCoefficient_mul (x y : JetRing 2) :
    firstCoefficient (x * y) = firstCoefficient x * jetConstant y + jetConstant x * firstCoefficient y := by
  obtain ⟨f, rfl⟩ := (Ideal.Quotient.mk_surjective : Function.Surjective (jetReduction 2)) x
  obtain ⟨g, rfl⟩ := (Ideal.Quotient.mk_surjective : Function.Surjective (jetReduction 2)) y
  rw [← map_mul]
  change PowerSeries.coeff 1 (f * g) =
    PowerSeries.coeff 1 f * PowerSeries.constantCoeff g +
      PowerSeries.constantCoeff f * PowerSeries.coeff 1 g
  rw [PowerSeries.coeff_one_mul, mul_comm (PowerSeries.coeff 1 g)]

private def constantMatrix (A : Jets) : ComplexMatrix := A.map jetConstant
private def firstMatrix (A : Jets) : ComplexMatrix := A.map firstCoefficient

private theorem firstMatrix_mul (A B : Jets) :
    firstMatrix (A * B) = firstMatrix A * constantMatrix B + constantMatrix A * firstMatrix B := by
  ext i j
  simp [firstMatrix, constantMatrix, Matrix.mul_apply, firstCoefficient_mul]
  ring

private theorem firstMatrix_one : firstMatrix (1 : Jets) = 0 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [firstMatrix, Matrix.map_apply, Matrix.one_apply_eq, Matrix.zero_apply]
    change PowerSeries.coeff 1 (1 : O) = 0
    simp
  · simp [firstMatrix, Matrix.one_apply_ne h]

private theorem constantMatrix_continuous : Continuous constantMatrix := by
  have hc : Continuous jetConstant := by
    rw [show (jetConstant : JetRing 2 → ℂ) = (fun p ↦ p (0 : Fin 2)) ∘ jetsHomeomorph from
      funext jetConstant_eq]
    exact (continuous_apply (0 : Fin 2)).comp jetsHomeomorph.continuous
  exact continuous_pi fun i ↦ continuous_pi fun j ↦
    hc.comp ((continuous_apply j).comp (continuous_apply i))

private theorem firstMatrix_continuous : Continuous firstMatrix := by
  have hc : Continuous firstCoefficient :=
    (continuous_apply (1 : Fin 2)).comp jetsHomeomorph.continuous
  exact continuous_pi fun i ↦ continuous_pi fun j ↦
    hc.comp ((continuous_apply j).comp (continuous_apply i))

private def jetUnitOpen : Set Jets := {A | (constantMatrix A).det ≠ 0}

private theorem jetUnitOpen_isOpen : IsOpen jetUnitOpen :=
  isOpen_ne_fun (constantMatrix_continuous.matrix_det) continuous_const

private theorem jetMatrixUnit (A : Jets) : IsUnit A ↔ A ∈ jetUnitOpen := by
  change IsUnit A ↔ (A.map jetConstant).det ≠ 0
  rw [Matrix.isUnit_iff_isUnit_det, jet_unit_iff, RingHom.map_det]
  rfl

private def unitOfJetMatrix (A : jetUnitOpen) : JetGroup :=
  ((jetMatrixUnit A.val).mpr A.property).unit

@[simp] private theorem unitOfJetMatrix_val (A : jetUnitOpen) :
    (unitOfJetMatrix A).val = A.val := IsUnit.unit_spec _

private theorem constantMatrix_inv (u : Jetsˣ) :
    constantMatrix (↑u⁻¹) = (constantMatrix u.val)⁻¹ := by
  have h := Matrix.nonsing_inv_eq_ringInverse (constantMatrix u.val)
  rw [h]
  change ((Units.map (jetConstant.mapMatrix).toMonoidHom u)⁻¹).val =
    Ring.inverse ((Units.map (jetConstant.mapMatrix).toMonoidHom u).val)
  exact (Ring.inverse_unit _).symm

private theorem firstMatrix_inv (u : Jetsˣ) :
    firstMatrix (↑u⁻¹) = -(constantMatrix u.val)⁻¹ * firstMatrix u.val * (constantMatrix u.val)⁻¹ := by
  let A := constantMatrix u.val
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr ((jetMatrixUnit u.val).mp u.isUnit)
  have hc : A * firstMatrix (↑u⁻¹) + firstMatrix u.val * A⁻¹ = 0 := by
    have h := firstMatrix_mul u.val (↑u⁻¹)
    rw [Units.mul_inv, firstMatrix_one, constantMatrix_inv] at h
    simpa only [A, add_comm] using h.symm
  have hh := congrArg (fun B : ComplexMatrix ↦ A⁻¹ * B) hc
  rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul,
    Matrix.mul_zero] at hh
  calc
    firstMatrix (↑u⁻¹) = -(A⁻¹ * (firstMatrix u.val * A⁻¹)) := eq_neg_of_add_eq_zero_left hh
    _ = -A⁻¹ * firstMatrix u.val * A⁻¹ := by simp [Matrix.mul_assoc]

private theorem constantMatrix_nonsingInv_continuous :
    Continuous (fun A : jetUnitOpen ↦ (constantMatrix A.val)⁻¹) := by
  have hc := constantMatrix_continuous.comp
    (continuous_subtype_val : Continuous (Subtype.val : jetUnitOpen → Jets))
  have hd := hc.matrix_det
  have hi := hd.inv₀ (fun A : jetUnitOpen ↦ A.property)
  refine (continuous_congr ?_).mp (hi.smul hc.matrix_adjugate)
  intro A
  change (constantMatrix A.val).det⁻¹ • (constantMatrix A.val).adjugate =
    (constantMatrix A.val)⁻¹
  rw [Matrix.inv_def, Ring.inverse_eq_inv]

private theorem unitOfJetMatrix_continuous : Continuous unitOfJetMatrix := by
  apply Units.continuous_iff.mpr
  refine ⟨?_, ?_⟩
  · change Continuous (fun A : jetUnitOpen ↦ (unitOfJetMatrix A).val)
    simpa only [unitOfJetMatrix_val] using
      (continuous_subtype_val : Continuous (Subtype.val : jetUnitOpen → Jets))
  apply jetMatrixHomeomorph.isInducing.continuous_iff.mpr
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_pi fun k ↦ ?_
  have h0 : Continuous (fun A : jetUnitOpen ↦ constantMatrix (↑(unitOfJetMatrix A)⁻¹)) := by
    simpa only [constantMatrix_inv, unitOfJetMatrix_val] using constantMatrix_nonsingInv_continuous
  have h1 : Continuous (fun A : jetUnitOpen ↦ firstMatrix (↑(unitOfJetMatrix A)⁻¹)) := by
    simpa only [firstMatrix_inv, unitOfJetMatrix_val, Pi.mul_def, Pi.neg_def, Function.comp_def] using
      (constantMatrix_nonsingInv_continuous.neg.mul
        (firstMatrix_continuous.comp continuous_subtype_val)).mul constantMatrix_nonsingInv_continuous
  fin_cases k
  · change Continuous (fun A : jetUnitOpen ↦ jetCoefficients 2 ((↑(unitOfJetMatrix A)⁻¹ : Jets) i j) 0)
    simpa only [constantMatrix, Matrix.map_apply, jetConstant_eq, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply i)).comp h0
  · exact ((continuous_apply j).comp (continuous_apply i)).comp h1

private def jetGroupHomeomorph : JetGroup ≃ₜ jetUnitOpen where
  toFun g := ⟨g.val, (jetMatrixUnit g.val).mp g.isUnit⟩
  invFun := unitOfJetMatrix
  left_inv _ := Units.ext (unitOfJetMatrix_val _)
  right_inv _ := Subtype.ext (unitOfJetMatrix_val _)
  continuous_toFun := Units.continuous_val.subtype_mk _
  continuous_invFun := unitOfJetMatrix_continuous

private theorem jetChartTopology (c : RadialChart) (D : Opens JetGroup)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods) :
    ComparisonTopology (JetChart D) := by
  let E := Fin 2 → Fin 2 → Fin 2 → ℂ
  have hE : ComparisonTopology (TopCat.of E) :=
    ⟨inferInstance, inferInstance, inferInstance, normedOpenBasis E⟩
  have hD : ComparisonTopology (TopCat.of D) := comparisonTopology_of_openEmbedding
    (jetMatrixHomeomorph.isOpenEmbedding.comp (jetUnitOpen_isOpen.isOpenEmbedding_subtypeVal.comp
      (jetGroupHomeomorph.isOpenEmbedding.comp D.isOpen.isOpenEmbedding_subtypeVal))) hE
  exact comparisonTopology_prod hD (chartTopology c radial)

private theorem jetProjectionIsIso (c : RadialChart) (D : Opens JetGroup)
    (hD : ContractibleSpace D) (r : PositiveRadius) (q : ℤ) :
    IsIso ((relativeCohomologyFunctor ℚ Values.{0} q).map (jetPairProjection c D r).op) := by
  letI := hD
  obtain ⟨d, ⟨H⟩⟩ := id_nullhomotopic D
  let P := c.pairs.obj r
  let Q := jetPair c D r
  let π : Q ⟶ P := jetPairProjection c D r
  let j : P ⟶ Q :=
    ⟨TopCat.ofHom ⟨fun x ↦ ⟨(d, x.val), x.property⟩,
        (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩,
      fun _ hx ↦ hx⟩
  have hj : j ≫ π = 𝟙 P := by apply PairMap.ext; ext x; rfl
  have hπ : P202Specs.PrismHomotopy.PairHomotopy (𝟙 Q) (π ≫ j) := by
    let G : C(unitInterval × Q.space, D × ChartSpace) :=
      ⟨fun a ↦ (H (a.1, a.2.val.1), a.2.val.2),
        (H.continuous.comp (continuous_fst.prodMk
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))).prodMk
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))⟩
    refine ⟨⟨⟨fun a ↦ ⟨G a, a.2.property⟩, G.continuous.subtype_mk _⟩, ?_, ?_⟩,
      fun _ x ↦ x.property⟩
    · intro x
      exact Subtype.ext (Prod.ext (H.map_zero_left _) rfl)
    · intro x
      exact Subtype.ext (Prod.ext (H.map_one_left _) rfl)
  let F := relativeCohomologyFunctor ℚ Values.{0} q
  have hi : F.map (𝟙 Q).op = F.map (π ≫ j).op :=
    (P202.CohomologyPairs.homotopy_invariant ℚ Values.{0}).2 hπ q
  change IsIso (F.map π.op)
  refine ⟨⟨F.map j.op, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← op_comp, hj, op_id, F.map_id]
  · rw [← F.map_comp, ← op_comp, ← hi, op_id, F.map_id]

open P202Specs.SingularChains

private abbrev rationalToIntegralCochains :=
  ModuleCat.restrictScalars (Int.castRingHom ℚ)

private def cochainCoordinates (R : Type) [CommRing R] [Module R Values.{0}]
    (X : TopCat) (n : ℕ) :
    (ordinaryCochains R Values.{0} X).X (n : ℤ) ≃+ (Simplex X n → Values.{0}) :=
  (ordinaryCochainsEquiv R Values.{0} X n).toAddEquiv.trans
    (Finsupp.lift Values.{0} R (Simplex X n)).symm

private theorem cochainCoordinates_d (R : Type) [CommRing R] [Module R Values.{0}]
    (X : TopCat) (n : ℕ) (a : (ordinaryCochains R Values.{0} X).X (n : ℤ))
    (s : Simplex X (n + 1)) :
    cochainCoordinates R X (n + 1) ((ordinaryCochains R Values.{0} X).d
        (n : ℤ) ((n + 1 : ℕ) : ℤ) a) s =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • cochainCoordinates R X n a (face i s) := by
  change ordinaryCochainsEquiv R Values.{0} X (n + 1)
    ((ordinaryCochains R Values.{0} X).d (n : ℤ) ((n + 1 : ℕ) : ℤ) a)
      (Finsupp.single s 1) = _
  have h := P202.CohomologyPairs.natural_coboundary R Values.{0} X n
    (ordinaryCochainsEquiv R Values.{0} X n a) (Finsupp.single s 1)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h]
  rw [P202.SingularChains.boundary_single, map_sum]
  simp only [map_zsmul]
  rfl

private def integralCochainIso (X : TopCat) :
    (rationalToIntegralCochains.mapHomologicalComplex (.up ℤ)).obj
      (ordinaryCochains ℚ Values.{0} X) ≅ ordinaryCochains ℤ Values.{0} X := by
  let Q := ordinaryCochains ℚ Values.{0} X
  let Z := ordinaryCochains ℤ Values.{0} X
  let E (n : ℕ) : rationalToIntegralCochains.obj (Q.X (n : ℤ)) ≅ Z.X (n : ℤ) :=
    ((cochainCoordinates ℚ X n).trans
      (cochainCoordinates ℤ X n).symm).toIntLinearEquiv.toModuleIso
  let zeroQ (q : ℤ) (hq : q < 0) : IsZero (rationalToIntegralCochains.obj (Q.X q)) :=
    rationalToIntegralCochains.map_isZero ((P202.CohomologyPairs.negative ℚ Values.{0}).1 X q hq).1
  let zeroZ (q : ℤ) (hq : q < 0) : IsZero (Z.X q) :=
    ((P202.CohomologyPairs.negative ℤ Values.{0}).1 X q hq).1
  let e (q : ℤ) : rationalToIntegralCochains.obj (Q.X q) ≅ Z.X q :=
    if h : q < 0 then (zeroQ q h).iso (zeroZ q h) else
      (eqToIso (congrArg (fun k ↦ rationalToIntegralCochains.obj (Q.X k)) (Int.toNat_of_nonneg
        (le_of_not_gt h)).symm)) ≪≫ E q.toNat ≪≫ (eqToIso (congrArg Z.X (Int.toNat_of_nonneg
          (le_of_not_gt h))))
  have he (n : ℕ) : e (n : ℤ) = E n := by
    simp [e]
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j hij
  by_cases hi : i < 0
  · exact (zeroQ i hi).eq_of_src _ _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hi)
    change (n : ℤ) + 1 = j at hij
    subst j
    change (e (n : ℤ)).hom ≫ Z.d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
      rationalToIntegralCochains.map (Q.d (n : ℤ) ((n + 1 : ℕ) : ℤ)) ≫
        (e ((n + 1 : ℕ) : ℤ)).hom
    rw [he, he]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply (cochainCoordinates ℤ X (n + 1)).injective
    funext s
    change cochainCoordinates ℤ X (n + 1)
      (Z.d (n : ℤ) ((n + 1 : ℕ) : ℤ) ((cochainCoordinates ℤ X n).symm
        (cochainCoordinates ℚ X n a))) s =
      cochainCoordinates ℤ X (n + 1) ((cochainCoordinates ℤ X (n + 1)).symm
        (cochainCoordinates ℚ X (n + 1) (Q.d (n : ℤ) ((n + 1 : ℕ) : ℤ) a))) s
    dsimp only [Z, Q]
    rw [cochainCoordinates_d ℤ X n]
    simp only [AddEquiv.apply_symm_apply]
    exact (cochainCoordinates_d ℚ X n a s).symm

private theorem rationalCoefficientInjective : Module.Injective ℤ Values.{0} := by
  letI : Module.Injective ℤ ℚ := (Module.Baer.of_divisible ℚ).injective
  exact Module.ulift_injective_of_injective ℤ inferInstance

open P202Specs.UniversalCoefficientsCohomology (evaluation actualExt previousDegree)
open P202Specs.UniversalCoefficientsCohomology.AlgebraicExt (Ext resolutionFamily)

private def evaluationEquiv (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Module R Values.{0}] (hI : Module.Injective R Values.{0}) (X : TopCat) (n : ℕ) :
    ordinaryCohomology R Values.{0} X (n : ℤ) ≃ₗ[R]
      (P202Specs.SingularChains.homology R R X (n : ℤ) →ₗ[R] Values.{0}) := by
  let V := P202Specs.SingularChains.homology R R X (previousDegree n)
  let T := resolutionFamily R V
  have hs : Subsingleton (actualExt R Values.{0} (ordinaryComplex R R X) (previousDegree n)) :=
    P103.Ch11.VanishingAndFlatness.ext_injective R V Values.{0} hI T.val T.property 0
  have hb : Function.Bijective (evaluation R Values.{0} (ordinaryComplex R R X) (n : ℤ)) := by
    obtain ⟨a, _, _, he, hsurj, _⟩ :=
      (P202.UniversalCoefficientsCohomology.all_degrees R Values.{0}).1 X n
    refine ⟨fun x y hxy ↦ sub_eq_zero.mp ?_, hsurj⟩
    have h : evaluation R Values.{0} (ordinaryComplex R R X) (n : ℤ) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨u, hu⟩ := (he (x - y)).mp h
    rw [← hu, Subsingleton.elim u 0]
    exact a.map_zero
  exact LinearEquiv.ofBijective _ hb

private def ratCohomologyIntegralEquiv (X : TopCat) (q : ℤ) :
    ordinaryCohomology ℚ Values.{0} X q ≃+ ordinaryCohomology ℤ Values.{0} X q := by
  let C := ordinaryCochains ℚ Values.{0} X
  let H := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (.up ℤ) q
  exact (((C.sc q).mapHomologyIso rationalToIntegralCochains).symm ≪≫
    H.mapIso (integralCochainIso X)).toLinearEquiv.toAddEquiv

private def ratCohomologyEvaluation (X : TopCat) (n : ℕ) :
    ordinaryCohomology ℚ Values.{0} X (n : ℤ) ≃ₗ[ℚ]
      (P202Specs.SingularChains.homology ℤ ℤ X (n : ℤ) →ₗ[ℤ] Values.{0}) := by
  let e := (ratCohomologyIntegralEquiv X (n : ℤ)).trans
    (evaluationEquiv ℤ rationalCoefficientInjective X n).toAddEquiv
  exact { e with map_smul' := map_rat_smul e }

private def ratLinearEquiv {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℚ M] [Module ℚ N] (e : M ≃+ N) : M ≃ₗ[ℚ] N :=
  { e with map_smul' := map_rat_smul e }

private def evalFree {M : ModuleCat ℤ} (e : M ≃ₗ[ℤ] ℤ) :
    (M →ₗ[ℤ] Values.{0}) ≃ₗ[ℚ] ℚ :=
  ratLinearEquiv (((LinearEquiv.arrowCongr e (LinearEquiv.refl ℤ Values.{0})).trans
    (LinearMap.ringLmapEquivSelf ℤ ℤ Values.{0})).toAddEquiv.trans
    (ULift.moduleEquiv (R := ℚ) (M := ℚ)).toAddEquiv)

private theorem linearHomIsZero {M : ModuleCat ℤ} (hM : IsZero M) :
    IsZero (ModuleCat.of ℚ (M →ₗ[ℤ] Values.{0})) := by
  have := ModuleCat.subsingleton_of_isZero hM
  apply ModuleCat.isZero_of_subsingleton _

private theorem linearHomZModTwoIsZero {M : ModuleCat ℤ} (e : M ≃ₗ[ℤ] ZMod 2) :
    IsZero (ModuleCat.of ℚ (M →ₗ[ℤ] Values.{0})) := by
  have h (f : M →ₗ[ℤ] Values.{0}) (x : M) : f x = 0 := by
    have hx : (2 : ℕ) • x = 0 := e.injective (by
      rw [map_nsmul, map_zero]
      exact ZModModule.char_nsmul_eq_zero 2 (e x))
    have hf : (2 : ℕ) • f x = 0 := by rw [← map_nsmul, hx, map_zero]
    have hf' := congrArg ULift.down hf
    change (2 : ℕ) • (f x).down = 0 at hf'
    apply ULift.ext
    change (f x).down = (0 : ℚ)
    rw [two_nsmul] at hf'
    linarith
  haveI : Subsingleton (M →ₗ[ℤ] Values.{0}) :=
    ⟨fun f g ↦ LinearMap.ext fun x ↦ (h f x).trans (h g x).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

private abbrev point := P202Specs.SingularDegreeZero.point.{0}
private abbrev link := P202Specs.RealProjectiveHomology.projective 3

private theorem pointCohomology (q : ℤ) :
    Nonempty (ordinaryCohomology ℚ Values.{0} point q ≅ cohomologyValue {0} q) := by
  by_cases hq : q < 0
  · rw [cohomologyValue, ite_eq_right (by simpa using ne_of_lt hq)]
    exact ⟨((P202.CohomologyPairs.negative ℚ Values.{0}).1 point q hq).2.isoZero⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hq)
  let e := (ratCohomologyEvaluation point n).toModuleIso
  by_cases h : n = 0
  · subst n
    obtain ⟨f⟩ := P202.SingularDegreeZero.pointOrdinaryZero ℤ ℤ
    simpa [cohomologyValue] using (show Nonempty (_ ≅ ModuleCat.of ℚ ℚ) from
      ⟨e ≪≫ (evalFree f).toModuleIso⟩)
  · have hn : (n : ℤ) ≠ 0 := by exact_mod_cast h
    rw [cohomologyValue, ite_eq_right (by simpa using hn)]
    exact ⟨e ≪≫ (linearHomIsZero
      (P202.SingularDegreeZero.pointOrdinaryOther ℤ ℤ (n : ℤ) hn)).isoZero⟩

private theorem linkCohomology (q : ℤ) :
    Nonempty (ordinaryCohomology ℚ Values.{0} link q ≅ cohomologyValue {0, 3} q) := by
  by_cases hq : q < 0
  · rw [cohomologyValue, ite_eq_right (by simp; omega)]
    exact ⟨((P202.CohomologyPairs.negative ℚ Values.{0}).1 link q hq).2.isoZero⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hq)
  let e := (ratCohomologyEvaluation link n).toModuleIso
  obtain ⟨hfree, htors, hzero⟩ := P202.Homology.RealProjectiveHomology.integralHomology 3 n
  by_cases h : n = 0 ∨ n = 3
  · have hn : (n : ℤ) ∈ ({0, 3} : Finset ℤ) := by
      rcases h with rfl | rfl <;> decide
    rw [cohomologyValue, ite_eq_left hn]
    obtain ⟨f⟩ := hfree (h.imp id fun k ↦ ⟨k, by decide⟩)
    exact ⟨e ≪≫ (evalFree f).toModuleIso⟩
  · have hn : (n : ℤ) ∉ ({0, 3} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact_mod_cast h
    rw [cohomologyValue, ite_eq_right hn]
    by_cases ht : 0 < n ∧ n < 3 ∧ Odd n
    · obtain ⟨f⟩ := htors ht
      exact ⟨e ≪≫ (linearHomZModTwoIsZero f).isoZero⟩
    · exact ⟨e ≪≫ (linearHomIsZero (hzero ⟨fun k ↦ h (k.imp id And.left), ht⟩)).isoZero⟩

private abbrev ordinaryH (q : ℤ) := ordinaryCohomologyFunctor ℚ Values.{0} q

private def toPoint (X : TopCat) : X ⟶ point :=
  TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

private theorem ordinaryHomotopyEquivalence {X Y : TopCat} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : TopCat.Homotopy (𝟙 X) (f ≫ g)) (hY : TopCat.Homotopy (𝟙 Y) (g ≫ f))
    (q : ℤ) : IsIso ((ordinaryH q).map f.op) := by
  let F := ordinaryH q
  have hx := (P202.CohomologyPairs.homotopy_invariant ℚ Values.{0}).1 hX q
  have hy := (P202.CohomologyPairs.homotopy_invariant ℚ Values.{0}).1 hY q
  change F.map (𝟙 X).op = F.map (f ≫ g).op at hx
  change F.map (𝟙 Y).op = F.map (g ≫ f).op at hy
  refine ⟨⟨F.map g.op, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← op_comp, ← hy, op_id, F.map_id]
  · rw [← F.map_comp, ← op_comp, ← hx, op_id, F.map_id]

private theorem contractibleToPoint (X : TopCat) (hX : ContractibleSpace X) (q : ℤ) :
    IsIso ((ordinaryH q).map (toPoint X).op) := by
  letI := hX
  obtain ⟨x, ⟨h⟩⟩ := id_nullhomotopic X
  let j : point ⟶ X := TopCat.ofHom (ContinuousMap.const _ x)
  have hj : j ≫ toPoint X = 𝟙 point := by ext p
  exact ordinaryHomotopyEquivalence (toPoint X) j h (hj.symm ▸ TopCat.Homotopy.refl _) q

private theorem contractibleProdProjection (X Y : TopCat) (hX : ContractibleSpace X) (q : ℤ) :
    IsIso ((ordinaryH q).map (TopCat.ofHom
      (⟨Prod.snd, continuous_snd⟩ : C(X × Y, Y))).op) := by
  letI := hX
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let f : TopCat.of (X × Y) ⟶ Y := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
  let g : Y ⟶ TopCat.of (X × Y) :=
    TopCat.ofHom ⟨fun y ↦ (x, y), continuous_const.prodMk continuous_id⟩
  have hg : g ≫ f = 𝟙 Y := by ext y; rfl
  exact ordinaryHomotopyEquivalence f g
    (H.prodMap (ContinuousMap.Homotopy.refl (ContinuousMap.id Y)))
    (hg.symm ▸ TopCat.Homotopy.refl _) q

private def puncturedBallHomeomorph (c : RadialChart) (r : PositiveRadius) :
    PuncturedBall r.val ≃ₜ c.puncturedBalls.obj r :=
  c.toLattice.subtype fun z ↦ by
    change (radialSize z < r.val ∧ z ≠ coneVertex) ↔
      (radialSize (c.toLattice.symm (c.toLattice z)) < r.val ∧
        c.toLattice z ∉ ({c.vertex} : Set ChartSpace))
    simp only [c.toLattice.symm_apply_apply, Set.mem_singleton_iff,
      c.toLattice.injective.eq_iff, RadialChart.vertex]

private abbrev Ball (c : RadialChart) (r : PositiveRadius) := TopCat.of (c.balls.obj r)
private abbrev Punctured (c : RadialChart) (r : PositiveRadius) :=
  TopCat.of (c.puncturedBalls.obj r)

private abbrev LinkProduct (r : PositiveRadius) :=
  TopCat.of (Set.Ioo (0 : ℝ) r.val × ProjectiveLink)

private def linkProjection (r : PositiveRadius) : LinkProduct r ⟶ link :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

private theorem linkProjectionIso (r : PositiveRadius) (q : ℤ) :
    IsIso ((ordinaryH q).map (linkProjection r).op) := by
  have hC : ContractibleSpace (Set.Ioo (0 : ℝ) r.val) :=
    (convex_Ioo _ _).contractibleSpace ⟨r.val / 2, by constructor <;> linarith [r.property]⟩
  exact contractibleProdProjection (TopCat.of (Set.Ioo (0 : ℝ) r.val)) link hC q

private theorem linkToPointIso : IsIso ((ordinaryH 0).map (toPoint link).op) := by
  obtain ⟨ep⟩ := pointCohomology 0
  obtain ⟨el⟩ := linkCohomology 0
  let V := ordinaryCohomology ℚ Values.{0} point 0
  let W := ordinaryCohomology ℚ Values.{0} link 0
  let f : V ⟶ W := (ordinaryH 0).map (toPoint link).op
  let base : P202Specs.SpheresDisks.sphere 3 :=
    ⟨EuclideanSpace.single 0 1, by
      simp⟩
  let sectionPoint : point ⟶ link :=
    TopCat.ofHom (ContinuousMap.const _ (P202Specs.RealProjectiveHomology.quotientMap 3 base))
  have h : sectionPoint ≫ toPoint link = 𝟙 point := by ext p
  have hr : f ≫ (ordinaryH 0).map sectionPoint.op = 𝟙 V := by
    dsimp only [f]
    rw [← Functor.map_comp, ← op_comp, h, op_id]
    exact (ordinaryH 0).map_id (op point)
  haveI : Mono f := mono_of_mono_fac hr
  have eV : V ≅ ModuleCat.of ℚ ℚ := ep ≪≫ eqToIso (by simp [cohomologyValue])
  have eW : W ≅ ModuleCat.of ℚ ℚ := el ≪≫ eqToIso (by simp [cohomologyValue])
  have hf : Module.finrank ℚ V = Module.finrank ℚ W :=
    eV.toLinearEquiv.finrank_eq.trans eW.toLinearEquiv.finrank_eq.symm
  haveI : FiniteDimensional ℚ V :=
    FiniteDimensional.of_injective eV.toLinearEquiv.toLinearMap eV.toLinearEquiv.injective
  haveI : FiniteDimensional ℚ W :=
    FiniteDimensional.of_injective eW.toLinearEquiv.toLinearMap eW.toLinearEquiv.injective
  have hinj : Function.Injective f := (ModuleCat.mono_iff_injective f).mp inferInstance
  exact (ConcreteCategory.isIso_iff_bijective f).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hf).mp hinj⟩

private def constantOrdinaryIso (A : PositiveRadius ⥤ TopCat) (X : TopCat) (q : ℤ)
    (p : ∀ r, A.obj r ⟶ X) (hp : ∀ {r s} (f : r ⟶ s), A.map f ≫ p s = p r)
    (hi : ∀ r, IsIso ((ordinaryH q).map (p r).op)) :
    (Functor.const _).obj ((ordinaryH q).obj (op X)) ≅ A.op ⋙ ordinaryH q :=
  NatIso.ofComponents (fun r ↦ letI := hi r.unop; asIso ((ordinaryH q).map (p r.unop).op))
    (by
      intro r s f
      change 𝟙 _ ≫ (ordinaryH q).map (p s.unop).op =
        (ordinaryH q).map (p r.unop).op ≫ (ordinaryH q).map (A.map f.unop).op
      rw [Category.id_comp, ← (ordinaryH q).map_comp, ← op_comp, hp])

private def ballOrdinaryIso (c : RadialChart)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods) (q : ℤ) :
    c.absolute q ≅ constantValue {0} q :=
  (constantOrdinaryIso (c.balls ⋙ Opens.toTopCat ChartSpace) point q
    (fun r ↦ toPoint (Ball c r)) (fun _ ↦ by ext)
    (fun r ↦ contractibleToPoint _ (ballContractible c radial r) q)).symm ≪≫
    (Functor.const _).mapIso (Classical.choice (pointCohomology q))

private def puncturedProjection (c : RadialChart)
    (f : ∀ r : ℝ, 0 < r → Set.Ioo (0 : ℝ) r × ProjectiveLink ≃ₜ PuncturedBall r)
    (r : PositiveRadius) : Punctured c r ⟶ link :=
  (TopCat.isoOfHomeo ((f r.val r.property).trans (puncturedBallHomeomorph c r))).inv ≫
    linkProjection r

private theorem puncturedProjectionIso (c : RadialChart)
    (f : ∀ r : ℝ, 0 < r → Set.Ioo (0 : ℝ) r × ProjectiveLink ≃ₜ PuncturedBall r)
    (r : PositiveRadius) (q : ℤ) :
    IsIso ((ordinaryH q).map (puncturedProjection c f r).op) := by
  haveI := linkProjectionIso r q
  unfold puncturedProjection
  rw [op_comp, (ordinaryH q).map_comp]
  infer_instance

set_option maxHeartbeats 950000 in
private theorem puncturedProjection_naturality (c : RadialChart)
    (f : ∀ r : ℝ, 0 < r → Set.Ioo (0 : ℝ) r × ProjectiveLink ≃ₜ PuncturedBall r)
    (hf : ∀ (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s)
      (x : Set.Ioo (0 : ℝ) r × ProjectiveLink),
      puncturedInclusion hrs (f r hr x) = f s hs (radialIntervalInclusion hrs x.1, x.2))
    {r s : PositiveRadius} (j : r ⟶ s) :
    (c.puncturedBalls ⋙ Opens.toTopCat ChartSpace).map j ≫ puncturedProjection c f s =
      puncturedProjection c f r := by
  let e (t : PositiveRadius) := (f t.val t.property).trans (puncturedBallHomeomorph c t)
  ext x
  obtain ⟨a, rfl⟩ := (e r).surjective x
  let h : r.val ≤ s.val := leOfHom j
  have hh : (c.puncturedBalls ⋙ Opens.toTopCat ChartSpace).map j (e r a) =
    e s (radialIntervalInclusion h a.1, a.2) := by
    apply Subtype.ext
    exact congrArg (fun z : PuncturedBall s.val ↦ c.toLattice z.val) (hf _ _ _ _ h a)
  change ((e s).symm ((c.puncturedBalls ⋙ Opens.toTopCat ChartSpace).map j (e r a))).2 =
    ((e r).symm (e r a)).2
  rw [hh, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

private def puncturedOrdinaryIso (c : RadialChart)
    (f : ∀ r : ℝ, 0 < r → Set.Ioo (0 : ℝ) r × ProjectiveLink ≃ₜ PuncturedBall r)
    (hf : ∀ (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s)
      (x : Set.Ioo (0 : ℝ) r × ProjectiveLink),
      puncturedInclusion hrs (f r hr x) = f s hs (radialIntervalInclusion hrs x.1, x.2))
    (q : ℤ) : c.punctured q ≅ constantValue {0, 3} q :=
  (constantOrdinaryIso (c.puncturedBalls ⋙ Opens.toTopCat ChartSpace) link q
    (puncturedProjection c f) (puncturedProjection_naturality c f hf)
    (fun r ↦ puncturedProjectionIso c f r q)).symm ≪≫
    (Functor.const _).mapIso (Classical.choice (linkCohomology q))

private theorem restrictionZeroIsIso (c : RadialChart)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods)
    (f : ∀ r : ℝ, 0 < r → Set.Ioo (0 : ℝ) r × ProjectiveLink ≃ₜ PuncturedBall r)
    (r : PositiveRadius) : IsIso (c.restriction 0 r) := by
  let F := ordinaryH 0
  let j : Punctured c r ⟶ Ball c r :=
    (Opens.toTopCat ChartSpace).map (homOfLE inf_le_left)
  haveI : IsIso (F.map (toPoint (Ball c r)).op) :=
    contractibleToPoint _ (ballContractible c radial r) 0
  haveI : IsIso (F.map (puncturedProjection c f r).op) := puncturedProjectionIso c f r 0
  haveI : IsIso (F.map (toPoint link).op) := linkToPointIso
  have h : F.map (toPoint (Ball c r)).op ≫ F.map j.op =
    F.map (toPoint link).op ≫ F.map (puncturedProjection c f r).op := by
    rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
    congr 1
  haveI : IsIso (F.map (toPoint (Ball c r)).op ≫ F.map j.op) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left (F.map (toPoint (Ball c r)).op) (F.map j.op)

private def restrictionNat (c : RadialChart) (q : ℤ) : c.absolute q ⟶ c.punctured q where
  app r := c.restriction q r.unop
  naturality r s j := by
    let F := singularOnOpens ChartSpace q
    change F.map (c.balls.map j.unop).op ≫ F.map (homOfLE inf_le_left).op =
      F.map (homOfLE inf_le_left).op ≫ F.map (c.puncturedBalls.map j.unop).op
    rw [← F.map_comp, ← F.map_comp]
    congr 1

open private singularSequence_shortExact subspaceIso_inclusion subspaceIso_naturality from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConstantSheafComparison

private abbrev radialOpenInclusion (c : RadialChart) (r : PositiveRadius) :
    c.puncturedBalls.obj r ⟶ c.balls.obj r := homOfLE inf_le_left

private abbrev radialSequence (c : RadialChart) (r : PositiveRadius) :=
  cochainSequence ℚ Values.{0} (openPair (radialOpenInclusion c r))

private theorem radialSequenceExact (c : RadialChart) (r : PositiveRadius) :
    (radialSequence c r).ShortExact := singularSequence_shortExact (radialOpenInclusion c r)

private def subspaceCohomologyIso (c : RadialChart) (r : PositiveRadius) (q : ℤ) :
    (radialSequence c r).X₃.homology q ≅ (c.punctured q).obj (op r) :=
  (ordinaryH q).mapIso (subspaceIso (radialOpenInclusion c r)).op

private theorem radialSequence_restriction (c : RadialChart) (r : PositiveRadius) (q : ℤ) :
    HomologicalComplex.homologyMap (radialSequence c r).g q ≫
      (subspaceCohomologyIso c r q).hom = c.restriction q r := by
  let F := ordinaryH q
  let i := radialOpenInclusion c r
  change F.map (openPair i).inclusion.op ≫ F.map (subspaceIso i).hom.op =
    F.map ((Opens.toTopCat ChartSpace).map i).op
  rw [← F.map_comp, ← op_comp, subspaceIso_inclusion]

private theorem radialSequenceRestrictionZeroIsIso (c : RadialChart) (r : PositiveRadius)
    (h : IsIso (c.restriction 0 r)) :
    IsIso (HomologicalComplex.homologyMap (radialSequence c r).g 0) := by
  haveI : IsIso (HomologicalComplex.homologyMap (radialSequence c r).g 0 ≫
      (subspaceCohomologyIso c r 0).hom) := radialSequence_restriction c r 0 ▸ h
  exact IsIso.of_isIso_comp_right _ (subspaceCohomologyIso c r 0).hom

private theorem absoluteIsZero (c : RadialChart)
    (a : ∀ q : ℤ, c.absolute q ≅ constantValue {0} q)
    (r : PositiveRadius) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((radialSequence c r).X₂.homology q) := by
  have e : (radialSequence c r).X₂.homology q ≅ 0 :=
    (a q).app (op r) ≪≫ eqToIso (by simp [cohomologyValue, hq])
  exact (isZero_zero _).of_iso e

private theorem puncturedIsZero (c : RadialChart)
    (b : ∀ q : ℤ, c.punctured q ≅ constantValue {0, 3} q)
    (r : PositiveRadius) (q : ℤ) (hq₀ : q ≠ 0) (hq₃ : q ≠ 3) :
    IsZero ((radialSequence c r).X₃.homology q) := by
  have e : (radialSequence c r).X₃.homology q ≅ 0 :=
    subspaceCohomologyIso c r q ≪≫ (b q).app (op r) ≪≫
      eqToIso (by simp [cohomologyValue, hq₀, hq₃])
  exact (isZero_zero _).of_iso e

private theorem relativeIsZero (c : RadialChart)
    (a : ∀ q : ℤ, c.absolute q ≅ constantValue {0} q)
    (b : ∀ q : ℤ, c.punctured q ≅ constantValue {0, 3} q)
    (r : PositiveRadius) (hi : IsIso (c.restriction 0 r)) (q : ℤ) (hq : q ≠ 4) :
    IsZero ((c.relative q).obj (op r)) := by
  let S := radialSequence c r
  let hS := radialSequenceExact c r
  let h : (ComplexShape.up ℤ).Rel (q - 1) q := by change q - 1 + 1 = q; omega
  haveI := radialSequenceRestrictionZeroIsIso c r hi
  have left : hS.δ (q - 1) q h = 0 := by
    by_cases hq₁ : q = 1
    · subst q
      change hS.δ 0 1 _ = 0
      rw [← cancel_epi (HomologicalComplex.homologyMap S.g 0), comp_zero]
      exact hS.comp_δ 0 1 rfl
    · exact (puncturedIsZero c b r (q - 1) (by omega) (by omega)).eq_of_src _ _
  have right : HomologicalComplex.homologyMap S.f q = 0 := by
    by_cases hq₀ : q = 0
    · subst q
      rw [← cancel_mono (HomologicalComplex.homologyMap S.g 0), zero_comp,
        ← HomologicalComplex.homologyMap_comp, ShortComplex.zero,
        HomologicalComplex.homologyMap_zero]
    · exact (absoluteIsZero c a r q hq₀).eq_of_tgt _ _
  exact (hS.homology_exact₁ (q - 1) q h).isZero_X₂ left right

private theorem connectingIsIso (c : RadialChart)
    (a : ∀ q : ℤ, c.absolute q ≅ constantValue {0} q) (r : PositiveRadius) :
    IsIso ((radialSequenceExact c r).δ 3 4 rfl) := by
  let hS := radialSequenceExact c r
  haveI : Mono (hS.δ 3 4 rfl) :=
    (hS.homology_exact₃ 3 4 rfl).mono_g ((absoluteIsZero c a r 3 (by decide)).eq_of_src _ _)
  haveI : Epi (hS.δ 3 4 rfl) :=
    (hS.homology_exact₁ 3 4 rfl).epi_f ((absoluteIsZero c a r 4 (by decide)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

set_option maxHeartbeats 1200000 in
private def connectingNat (c : RadialChart) : c.punctured 3 ⟶ c.relative 4 where
  app r := (subspaceCohomologyIso c r.unop 3).inv ≫ (radialSequenceExact c r.unop).δ 3 4 rfl
  naturality r s k := by
    let i := radialOpenInclusion c s.unop
    let i' := radialOpenInclusion c r.unop
    let j := c.balls.map k.unop
    let l := c.puncturedBalls.map k.unop
    let m := openPairInclusion i i' j l
    let A := ordinaryH 3
    let R := relativeCohomologyFunctor ℚ Values.{0} 4
    let er := subspaceCohomologyIso c r.unop 3
    let es := subspaceCohomologyIso c s.unop 3
    let hr := radialSequenceExact c r.unop
    let hs := radialSequenceExact c s.unop
    change A.map ((Opens.toTopCat ChartSpace).map l).op ≫ es.inv ≫ hs.δ 3 4 rfl =
      (er.inv ≫ hr.δ 3 4 rfl) ≫ R.map m.op
    have hu : er.hom ≫ A.map ((Opens.toTopCat ChartSpace).map l).op =
        A.map m.restrict.op ≫ es.hom := by
      change A.map (subspaceIso i').hom.op ≫ A.map ((Opens.toTopCat ChartSpace).map l).op =
        A.map m.restrict.op ≫ A.map (subspaceIso i).hom.op
      rw [← A.map_comp, ← A.map_comp, ← op_comp, ← op_comp, subspaceIso_naturality]
    have hd : hr.δ 3 4 rfl ≫ R.map m.op = A.map m.restrict.op ≫ hs.δ 3 4 rfl :=
      HomologicalComplex.HomologySequence.δ_naturality
        (cochainSequenceMap ℚ Values.{0} m) hr hs 3 4 rfl
    apply (cancel_epi er.hom).mp
    rw [← Category.assoc er.hom, hu]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hd]

private def radialRelativeIso (c : RadialChart)
    (a : ∀ q : ℤ, c.absolute q ≅ constantValue {0} q)
    (b : ∀ q : ℤ, c.punctured q ≅ constantValue {0, 3} q)
    (hi : ∀ r : PositiveRadius, IsIso (c.restriction 0 r)) (q : ℤ) :
    c.relative q ≅ constantValue {4} q := by
  by_cases hq : q = 4
  · subst q
    haveI (r : PositiveRadiusᵒᵖ) : IsIso ((connectingNat c).app r) := by
      haveI := connectingIsIso c a r.unop
      change IsIso ((subspaceCohomologyIso c r.unop 3).inv ≫ (radialSequenceExact c r.unop).δ 3 4 rfl)
      infer_instance
    haveI : IsIso (connectingNat c) := NatIso.isIso_of_isIso_app _
    exact (asIso (connectingNat c)).symm ≪≫ b 3 ≪≫
      (Functor.const _).mapIso (eqToIso (by simp [cohomologyValue]))
  · refine NatIso.ofComponents (fun r ↦
      (relativeIsZero c a b r.unop (hi r.unop) q hq).isoZero ≪≫
        eqToIso (by simp [cohomologyValue, hq])) ?_
    intro r s k
    exact (relativeIsZero c a b r.unop (hi r.unop) q hq).eq_of_src _ _

theorem radialSingularCohomology_conditional
    (_analytic : NilpotentConeChartSpecs.Expected.AnalyticQuadraticChart)
    (_antipodal : NilpotentConeChartSpecs.Expected.AntipodalQuotientHomeomorphism)
    (_polynomial : NilpotentConeChartSpecs.Expected.PolynomialParametrization)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods)
    (_reduced : NilpotentConeChartSpecs.Expected.ReducedQuadraticChart) :
    TwoStepLocalCohomologySpecs.Expected.RadialSingularCohomology := by
  intro c
  obtain ⟨_, f, _, _, hf, _, _⟩ := radial.2.2.2
  let a := ballOrdinaryIso c radial
  let b := puncturedOrdinaryIso c f hf
  have hi := restrictionZeroIsIso c radial f
  haveI (r : PositiveRadiusᵒᵖ) : IsIso ((restrictionNat c 0).app r) := hi r.unop
  haveI : IsIso (restrictionNat c 0) := NatIso.isIso_of_isIso_app _
  let a₀ : c.absolute 0 ≅ constantValue {0} 0 :=
    asIso (restrictionNat c 0) ≪≫ b 0 ≪≫ (Functor.const _).mapIso degreeZeroValueIso
  let a' (q : ℤ) : c.absolute q ≅ constantValue {0} q :=
    if hq : q = 0 then hq.symm ▸ a₀ else a q
  refine ⟨a', b, radialRelativeIso c a b hi, fun r ↦ ⟨hi r, ?_⟩⟩
  simp only [a', dite_true]
  rfl

theorem jetProductCohomology_conditional
    (analytic : NilpotentConeChartSpecs.Expected.AnalyticQuadraticChart)
    (antipodal : NilpotentConeChartSpecs.Expected.AntipodalQuotientHomeomorphism)
    (polynomial : NilpotentConeChartSpecs.Expected.PolynomialParametrization)
    (radial : NilpotentConeChartSpecs.Expected.RadialNeighborhoods)
    (reduced : NilpotentConeChartSpecs.Expected.ReducedQuadraticChart) :
    TwoStepLocalCohomologySpecs.Expected.JetProductCohomology := by
  intro c D hD
  have hT := jetChartTopology c D radial
  obtain ⟨_, _, g, _⟩ := radialSingularCohomology_conditional
    analytic antipodal polynomial radial reduced c
  refine ⟨hT, fun q ↦ ⟨supportedComparison (JetChart D) hT (jetSupportClosed c D) q, ?_⟩⟩
  intro r
  haveI := jetProjectionIsIso c D hD r q
  exact ⟨inferInstance, ⟨(asIso ((relativeCohomologyFunctor ℚ Values.{0} q).map
    (jetPairProjection c D r).op)).symm ≪≫ (g q).app (op r)⟩⟩

end RepTheorySurvey.Geometric.TwoStepLocalCohomology

theorem _root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«jetProductCohomology» : _root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomologySpecs».«Expected».«JetProductCohomology» :=
  @_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«jetProductCohomology_conditional» (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«analyticQuadraticChart») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«antipodalQuotientHomeomorphism») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«polynomialParametrization») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«radialNeighborhoods») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«reducedQuadraticChart»)
theorem _root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialNeighborhoodBasis» : _root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomologySpecs».«Expected».«RadialNeighborhoodBasis» :=
  @_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialNeighborhoodBasis_conditional» (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«analyticQuadraticChart») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«antipodalQuotientHomeomorphism») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«polynomialParametrization») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«radialNeighborhoods») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«reducedQuadraticChart»)
theorem _root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSheafCohomology» : _root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomologySpecs».«Expected».«RadialSheafCohomology» :=
  @_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSheafCohomology_conditional» (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«analyticQuadraticChart») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«antipodalQuotientHomeomorphism») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«polynomialParametrization») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«radialNeighborhoods») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«reducedQuadraticChart»)
theorem _root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSingularCohomology» : _root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomologySpecs».«Expected».«RadialSingularCohomology» :=
  @_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSingularCohomology_conditional» (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«analyticQuadraticChart») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«antipodalQuotientHomeomorphism») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«polynomialParametrization») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«radialNeighborhoods») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«reducedQuadraticChart»)
