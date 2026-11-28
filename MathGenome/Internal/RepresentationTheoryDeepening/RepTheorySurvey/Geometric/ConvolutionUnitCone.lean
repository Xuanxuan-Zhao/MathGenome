import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitCone
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianIncidenceTopology
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConstantSheafComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TransverseCone
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionAnalyticCharts
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionFrameQuotient
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitLocality
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Connected
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.ComplexProjectiveHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficientsCohomology
import Mathlib.Algebra.Module.LinearMap.Rat
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace RepTheorySurvey.Geometric.ConvolutionUnitCone

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace Topology
open Analytic LocalSheaf LatticeModelSpecs MinusculeAndTwoStepSpecs ConvolutionBundleSpecs
open ConvolutionUnitConeSpecs
open LinearAlgebraicGroups.Specs.GrassmannianCharts (Pivot Inside Outside)
open scoped Matrix MatrixGroups

open private unitCocone tensorPresheafIso sectionTensorUnit compositionUnit pulledTensorSections
  continuous_frameParameters from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitCone

open private continuous_of_columnRange continuous_fromCharts chartPlane_eq_range
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianIncidenceTopology

private def linePoint (l : P202.ComplexProjective.Space 1) : ProjectivePoints :=
  subspacePoint projectiveBasis projectiveRank l.submodule l.finrank_submodule

private theorem linePoint_plane (l : P202.ComplexProjective.Space 1) :
    firstPlane (linePoint l) = l.submodule :=
  subspacePoint_subspace projectiveBasis projectiveRank _ _

private def projectivePoint (p : ProjectivePoints) : P202.ComplexProjective.Space 1 :=
  Projectivization.mk'' (firstPlane p) (grassmannianSubspace_finrank _ _ p)

private theorem projectivePoint_line (p : ProjectivePoints) :
    (projectivePoint p).submodule = firstPlane p :=
  Projectivization.submodule_mk'' _ _

private theorem continuous_linePoint : Continuous linePoint := by
  apply (P202.ComplexProjective.quotientMap_quotient 1).continuous_iff.mpr
  let M (v : P202.ComplexProjective.NonzeroVectors 1) : Matrix (Fin 2 × Fin 1) (Fin 1) ℂ :=
    Matrix.of fun i _ => projectiveBasis.equivFun v.val i
  have hM : Continuous M := by
    apply continuous_matrix
    intro i j
    exact (continuous_apply i).comp
      (projectiveBasis.equivFun.continuous_of_finiteDimensional.comp continuous_subtype_val)
  apply continuous_of_columnRange projectiveBasis projectiveRank _ M hM
  intro v
  change (firstPlane (linePoint (P202.ComplexProjective.quotientMap 1 v))).map
    projectiveBasis.equivFun.toLinearMap = (M v).mulVecLin.range
  rw [linePoint_plane]
  change (Projectivization.mk ℂ v.val v.property).submodule.map _ = _
  rw [Projectivization.submodule_mk, Submodule.map_span, Set.image_singleton]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro w hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact ⟨fun _ => 1, by ext i; simp [M, Matrix.mulVec, dotProduct]⟩
  · rintro w ⟨z, rfl⟩
    have hz : (M v).mulVecLin z = z 0 • projectiveBasis.equivFun v.val := by
      ext i
      simp [M, Matrix.mulVec, dotProduct, mul_comm]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

private theorem continuous_projectivePoint : Continuous projectivePoint := by
  apply continuous_fromCharts projectiveBasis projectiveRank
  intro I
  classical
  have hI : Fintype.card (Inside I) = 1 := by
    change Fintype.card {i // i ∈ I.val} = 1
    simpa using I.property
  let : Unique (Inside I) := (Fintype.card_eq_one_iff_nonempty_unique.mp hI).some
  let v (D : Matrix (Outside I) (Inside I) ℂ) : V :=
    projectiveBasis.equivFun.symm ((graphMatrix I D).col default)
  have hv (D) : v D ≠ 0 := by
    intro hz
    have hz' := congrArg (fun w => projectiveBasis.equivFun w (default : Inside I).val) hz
    change projectiveBasis.equivFun (projectiveBasis.equivFun.symm
      ((graphMatrix I D).col default)) (default : Inside I).val =
      projectiveBasis.equivFun 0 (default : Inside I).val at hz'
    simp only [LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply, Matrix.col_apply] at hz'
    have hz'' : (1 : ℂ) = 0 := by
      simpa only [graphMatrix, Matrix.of_apply, dite_eq_left (default : Inside I).property,
        ite_true] using hz'
    exact one_ne_zero hz''
  have hc : Continuous v := by
    apply projectiveBasis.equivFun.symm.continuous_of_finiteDimensional.comp
    apply continuous_pi
    intro i
    by_cases hi : i ∈ I.val
    · simpa [Matrix.col, graphMatrix, hi] using
        (continuous_const : Continuous fun _ : Matrix (Outside I) (Inside I) ℂ =>
          (if i = (default : Inside I).val then (1 : ℂ) else 0))
    · simpa [Matrix.col, graphMatrix, hi] using
        (continuous_id.matrix_elem (⟨i, hi⟩ : Outside I) (default : Inside I))
  have he : projectivePoint ∘ grassmannianChartPoint projectiveBasis projectiveRank I =
      fun D => P202.ComplexProjective.quotientMap 1 ⟨v D, hv D⟩ := by
    funext D
    apply Projectivization.submodule_injective
    change (projectivePoint (grassmannianChartPoint projectiveBasis projectiveRank I D)).submodule =
      (Projectivization.mk ℂ (v D) (hv D)).submodule
    rw [projectivePoint_line, Projectivization.submodule_mk]
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      intro w hw
      obtain rfl := Set.mem_singleton_iff.mp hw
      change v D ∈ grassmannianSubspace projectiveBasis projectiveRank
        (grassmannianChartPoint projectiveBasis projectiveRank I D)
      rw [chartPlane_eq_range, LinearMap.range_comp]
      refine ⟨(graphMatrix I D).col default, ?_, rfl⟩
      exact ⟨Pi.single default 1, Matrix.mulVec_single_one _ _⟩
    · have hr := grassmannianSubspace_finrank projectiveBasis projectiveRank
        (grassmannianChartPoint projectiveBasis projectiveRank I D)
      have hs := finrank_span_singleton (K := ℂ) (hv D)
      change Module.finrank ℂ (grassmannianSubspace projectiveBasis projectiveRank
        (grassmannianChartPoint projectiveBasis projectiveRank I D)) ≤
        Module.finrank ℂ (ℂ ∙ v D)
      exact le_of_eq (hr.trans hs.symm)
  rw [he]
  exact (P202.ComplexProjective.quotientMap_continuous 1).comp (hc.subtype_mk hv)

/-- The scheme Grassmannian of first lattice lines has the quotient topology of
the actual complex projective line, via the identical homogeneous subspace. -/
def projectiveLineHomeomorph : projectiveLine ≃ₜ minuscule where
  toFun := linePoint
  invFun := projectivePoint
  left_inv l := Projectivization.submodule_injective <| by
    rw [projectivePoint_line, linePoint_plane]
  right_inv p := grassmannianSubspace_injective projectiveBasis projectiveRank <| by
    change firstPlane (linePoint (projectivePoint p)) = firstPlane p
    rw [linePoint_plane, projectivePoint_line]
  continuous_toFun := continuous_linePoint
  continuous_invFun := continuous_projectivePoint

theorem projectiveLineHomeomorph_plane (l : P202.ComplexProjective.Space 1) :
    firstPlane (projectiveLineHomeomorph l) = l.submodule :=
  linePoint_plane l

section UnitCone

open DerivedCategory.HomologySequence

theorem unitTriangle_distinguished : unitTriangle ∈ distTriang (Derived surface) :=
  unitCocone.choose_spec.choose_spec.choose_spec

private theorem sourceStalk_zero (y : surface) (n : ℤ) (hn : n ≠ -2) :
    IsZero ((stalkCohomology y n).obj unitTriangle.obj₁) := by
  let C := Sheaves surface
  let F := (DerivedCategory.singleFunctor C (-2)).obj (rational surface)
  let e : F ≅ unitTriangle.obj₁ := (coefficientShiftIso surface 2).hom |> asIso |> fun e =>
    (DerivedCategory.Plus.ι (C := C)).mapIso e
  have h : IsZero ((DerivedCategory.homologyFunctor C n).obj F) := by
    rcases lt_or_gt_of_ne hn with h | h
    · exact DerivedCategory.isZero_of_isGE F (-2) n h
    · exact DerivedCategory.isZero_of_isLE F (-2) n h
  have h' := (Analytic.cohomology surface n).mapIso e
  exact (stalk y).map_isZero (h.of_iso h'.symm)

private theorem coneStalk_zero_of_unit (y : surface) (n : ℤ)
    (he : Epi ((stalkCohomology y n).map unit))
    (hm : Mono ((stalkCohomology y (n + 1)).map unit)) :
    IsZero ((stalkCohomology y n).obj unitCone) := by
  let D := unitTriangle
  let K := stalk y
  let H := Analytic.cohomology surface n
  let H' := Analytic.cohomology surface (n + 1)
  have ht := unitTriangle_distinguished
  have : Epi (K.map (H.map D.mor₁)) := he
  have : Mono (K.map (H'.map D.mor₁)) := hm
  have hf : K.map (H.map D.mor₂) = 0 := by
    rw [← cancel_epi (K.map (H.map D.mor₁))]
    rw [← K.map_comp, ← H.map_comp, comp_distTriang_mor_zero₁₂ _ ht]
    simp
  have hg : K.map (δ D n (n + 1)) = 0 := by
    rw [← cancel_mono (K.map (H'.map D.mor₁))]
    rw [← K.map_comp, δ_comp D ht n (n + 1) rfl]
    simp
  exact ((exact₃ D ht n (n + 1) rfl).map K).isZero_X₂ hf hg

private theorem coneStalk_zero_at_exceptional (x : surface) (h : StalkProfile x)
    (n : ℤ) (hn : n ≠ 0) : IsZero ((stalkCohomology x n).obj unitCone) := by
  obtain ⟨_, hv, hi⟩ := h
  apply coneStalk_zero_of_unit
  · by_cases he : n = -2
    · subst n
      let := hi
      infer_instance
    · constructor
      intro Z g k _
      exact (hv n he hn).eq_of_src g k
  · by_cases he : n + 1 = -2
    · rw [he]
      let := hi
      infer_instance
    · constructor
      intro Z g k _
      exact (sourceStalk_zero x (n + 1) he).eq_of_tgt g k

private def exceptionalCohomologyIso (x : surface) (h : StalkProfile x) :
    (stalkCohomology x 0).obj unitCone ≅ scalars := by
  let D := unitTriangle
  let K := stalk x
  let H := Analytic.cohomology surface 0
  have ht := unitTriangle_distinguished
  let f := K.map (H.map D.mor₂)
  haveI : Mono f := ((exact₂ D ht 0).map K).mono_g
    ((sourceStalk_zero x 0 (by decide)).eq_of_src _ _)
  haveI : Epi f := ((exact₃ D ht 0 1).map K).epi_f
    ((sourceStalk_zero x 1 (by decide)).eq_of_tgt _ _)
  haveI : IsIso f := isIso_of_mono_of_epi f
  exact (asIso f).symm ≪≫ (h.1 0 (Or.inr rfl)).some

private theorem coneCohomology_zero (x : surface) (h : StalkProfile x)
    (hU : ∀ (y : surface), y ≠ x → ∀ n : ℤ, IsIso ((stalkCohomology y n).map unit))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((Analytic.cohomology surface n).obj unitCone) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro y
  by_cases hxy : y = x
  · subst y
    exact coneStalk_zero_at_exceptional x h n hn
  · let := hU y hxy n
    let := hU y hxy (n + 1)
    exact coneStalk_zero_of_unit y n inferInstance inferInstance

private theorem coneCohomology_supported (x : surface)
    (hU : ∀ (y : surface), y ≠ x → ∀ n : ℤ, IsIso ((stalkCohomology y n).map unit)) :
    SupportedOn ({x} : Set surface) ((Analytic.cohomology surface 0).obj unitCone) := by
  intro y hy
  have hxy : y ≠ x := hy
  let := hU y hxy 0
  let := hU y hxy (0 + 1)
  exact coneStalk_zero_of_unit y 0 inferInstance inferInstance

/-- Concentration in degree zero identifies a derived object with its
degree-zero cohomology by an isomorphism inducing the identity. -/
private theorem singleCohomologyIso {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (D : DerivedCategory C)
    (hD : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C n).obj D)) :
    let H := DerivedCategory.homologyFunctor C 0
    let S := DerivedCategory.singleFunctor C 0
    let H₀ := H.obj D
    ∃ e : D ≅ S.obj H₀,
      H.map e.hom ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app H₀ =
        𝟙 H₀ := by
  let : D.IsGE 0 := (DerivedCategory.isGE_iff _ _).mpr fun n hn => hD n (ne_of_lt hn)
  let : D.IsLE 0 := (DerivedCategory.isLE_iff _ _).mpr fun n hn => hD n (ne_of_gt hn)
  obtain ⟨A, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D 0
  dsimp only
  let H := DerivedCategory.homologyFunctor C 0
  let S := DerivedCategory.singleFunctor C 0
  let η := DerivedCategory.singleFunctorCompHomologyFunctorIso C 0
  let a := H.mapIso e ≪≫ η.app A
  refine ⟨e ≪≫ S.mapIso a.symm, ?_⟩
  change H.map (e.hom ≫ S.map a.inv) ≫ η.hom.app (H.obj D) = 𝟙 _
  rw [Functor.map_comp, Category.assoc]
  change H.map e.hom ≫ (S ⋙ H).map a.inv ≫ η.hom.app (H.obj D) = 𝟙 _
  rw [η.hom.naturality]
  rw [Functor.id_map, ← Category.assoc]
  exact a.hom_inv_id

end UnitCone

section ProjectiveCohomology

open P202Specs.CohomologyPairs P202Specs.SingularChains
open P202Specs.UniversalCoefficientsCohomology

private abbrev QValues := Analytic.SingularCochains.Values.{0}

private def simplexCochainCoordinates (R : Type) [CommRing R] [Module R QValues]
    (X : TopCat) (n : ℕ) :
    (ordinaryCochains R QValues X).X (n : ℤ) ≃+ (Simplex X n → QValues) :=
  (ordinaryCochainsEquiv R QValues X n).toAddEquiv.trans (Finsupp.lift QValues R _).symm

private lemma simplexCochainCoordinates_d (R : Type) [CommRing R] [Module R QValues]
    (X : TopCat) (n : ℕ) (a : (ordinaryCochains R QValues X).X (n : ℤ)) (s : Simplex X (n+1)) :
    simplexCochainCoordinates R X (n+1)
      ((ordinaryCochains R QValues X).d (n : ℤ) ((n+1 : ℕ) : ℤ) a) s =
      ∑ i : Fin (n+2), (-1 : ℤ) ^ i.val • simplexCochainCoordinates R X n a (face i s) := by
  let e := ordinaryCochainsEquiv R QValues X n
  have h := P202.CohomologyPairs.natural_coboundary R QValues X n
    (e a) (Finsupp.single s 1)
  change ordinaryCochainsEquiv R QValues X (n+1)
    ((ordinaryCochains R QValues X).d (n : ℤ) ((n+1 : ℕ) : ℤ) (e.symm (e a)))
      (Finsupp.single s 1) = _ at h
  rw [e.symm_apply_apply] at h
  change ordinaryCochainsEquiv R QValues X (n+1)
    ((ordinaryCochains R QValues X).d (n : ℤ) ((n+1 : ℕ) : ℤ) a)
      (Finsupp.single s 1) = _
  rw [h]
  rw [P202.SingularChains.boundary_single]
  simp only [map_sum, map_zsmul]
  rfl

private abbrev restrictToIntegers : ModuleCat.{0} ℚ ⥤ ModuleCat.{0} ℤ :=
  ModuleCat.restrictScalars (Int.castRingHom ℚ)

private def cochainRestrictionIsoAt (X : TopCat) (n : ℤ) :
    restrictToIntegers.obj ((ordinaryCochains ℚ QValues X).X n) ≅
      (ordinaryCochains ℤ QValues X).X n := by
  cases n with
  | ofNat k =>
    let e := (simplexCochainCoordinates ℚ X k).trans (simplexCochainCoordinates ℤ X k).symm
    exact (e.toIntLinearEquiv
      (modM := (restrictToIntegers.obj ((ordinaryCochains ℚ QValues X).X (k : ℤ))).isModule)
      (modM₂ := ((ordinaryCochains ℤ QValues X).X (k : ℤ)).isModule)).toModuleIso
  | negSucc k =>
    exact ((restrictToIntegers.map_isZero
      ((P202.CohomologyPairs.negative ℚ QValues).1 X (Int.negSucc k) (by omega)).1).isoZero) ≪≫
      ((P202.CohomologyPairs.negative ℤ QValues).1 X (Int.negSucc k) (by omega)).1.isoZero.symm

private lemma cochainRestrictionIsoAt_hom_apply (X : TopCat) (n : ℕ)
    (a : (ordinaryCochains ℚ QValues X).X (n : ℤ)) :
    simplexCochainCoordinates ℤ X n ((cochainRestrictionIsoAt X n).hom a) =
      simplexCochainCoordinates ℚ X n a := by
  change simplexCochainCoordinates ℤ X n
    ((simplexCochainCoordinates ℤ X n).symm (simplexCochainCoordinates ℚ X n a)) = _
  exact AddEquiv.apply_symm_apply _ _

/-- Comparing coefficients as abelian groups leaves one rational value per
simplex and the same signed face sum for each coboundary. -/
private def cochainRestrictionIso (X : TopCat) :
    (restrictToIntegers.mapHomologicalComplex (.up ℤ)).obj (ordinaryCochains ℚ QValues X) ≅
      ordinaryCochains ℤ QValues X :=
  HomologicalComplex.Hom.isoOfComponents (cochainRestrictionIsoAt X) (by
    intro i j hij
    obtain rfl : j = i + 1 := (show i + 1 = j from hij).symm
    by_cases hi : 0 ≤ i
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      symm
      change _ ≫ (cochainRestrictionIsoAt X ((n+1 : ℕ) : ℤ)).hom = _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change ↑((ordinaryCochains ℚ QValues X).X (n : ℤ)) at a
      apply (simplexCochainCoordinates ℤ X (n+1)).injective
      funext s
      change simplexCochainCoordinates ℤ X (n+1)
        ((cochainRestrictionIsoAt X ((n+1 : ℕ) : ℤ)).hom
          ((ordinaryCochains ℚ QValues X).d (n : ℤ) ((n+1 : ℕ) : ℤ) a)) s =
        simplexCochainCoordinates ℤ X (n+1)
          ((ordinaryCochains ℤ QValues X).d (n : ℤ) ((n+1 : ℕ) : ℤ)
            ((cochainRestrictionIsoAt X n).hom a)) s
      rw [cochainRestrictionIsoAt_hom_apply, simplexCochainCoordinates_d,
        simplexCochainCoordinates_d, cochainRestrictionIsoAt_hom_apply]
    · exact (restrictToIntegers.map_isZero
        ((P202.CohomologyPairs.negative ℚ QValues).1 X i (by omega)).1).eq_of_src _ _)

private def cohomologyRestrictionIso (X : TopCat) (n : ℤ) :
    restrictToIntegers.obj ((singularCohomology n).obj (op X)) ≅
      ordinaryCohomology ℤ QValues X n :=
  (((ordinaryCochains ℚ QValues X).sc n).mapHomologyIso restrictToIntegers).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (cochainRestrictionIso X)

private theorem projectiveHomology_free (n : ℕ) :
    Module.Free ℤ (homology ℤ ℤ projectiveLine (n : ℤ)) := by
  by_cases h : ∃ r ≤ 1, n = 2 * r
  · obtain ⟨e⟩ := (P202.ComplexProjective.homology 1 n).1 h
    exact Module.Free.of_equiv e.symm
  · have := ModuleCat.subsingleton_of_isZero ((P202.ComplexProjective.homology 1 n).2 h)
    exact Module.Free.of_subsingleton _ _

private theorem projectiveEvaluation_bijective (n : ℕ) :
    Function.Bijective (evaluation ℤ QValues (ordinaryComplex ℤ ℤ projectiveLine) (n : ℤ)) := by
  let C := ordinaryComplex ℤ ℤ projectiveLine
  let k := previousDegree n
  have : Module.Free ℤ (C.homology k) := by
    cases n with
    | zero =>
      change Module.Free ℤ ((ordinaryComplex ℤ ℤ projectiveLine).homology (-1))
      have := ModuleCat.subsingleton_of_isZero
        (P202.SingularChains.ordinary_negative_homology ℤ ℤ projectiveLine (-1) (by decide))
      exact Module.Free.of_subsingleton _ _
    | succ n => exact projectiveHomology_free n
  have : Subsingleton (actualExt ℤ QValues C k) :=
    P103.Ch11.VanishingAndFlatness.ext_projective ℤ (C.homology k) QValues Module.Projective.of_free
      (AlgebraicExt.resolutionFamily ℤ (C.homology k)).val
      (AlgebraicExt.resolutionFamily ℤ (C.homology k)).property 0
  obtain ⟨α, _, _, hExact, hSurj, _⟩ :=
    (P202.UniversalCoefficientsCohomology.all_degrees ℤ QValues).1 projectiveLine n
  refine ⟨(injective_iff_map_eq_zero _).mpr ?_, hSurj⟩
  intro z hz
  obtain ⟨w, rfl⟩ := (hExact z).mp hz
  rw [Subsingleton.elim w 0, map_zero]

private def projectiveCohomologyDual (n : ℕ) :
    restrictToIntegers.obj ((singularCohomology (n : ℤ)).obj (op projectiveLine)) ≃ₗ[ℤ]
      (homology ℤ ℤ projectiveLine (n : ℤ) →ₗ[ℤ] QValues) :=
  (cohomologyRestrictionIso projectiveLine n).toLinearEquiv.trans
    (LinearEquiv.ofBijective _ (projectiveEvaluation_bijective n))

private theorem projectiveCohomology_rankOne (n : ℕ) (h : ∃ r ≤ 1, n = 2 * r) :
    Nonempty ((singularCohomology (n : ℤ)).obj (op projectiveLine) ≅ scalars) := by
  obtain ⟨e⟩ := (P202.ComplexProjective.homology 1 n).1 h
  let a := ((projectiveCohomologyDual n).trans
    ((LinearEquiv.arrowCongr e (LinearEquiv.refl ℤ QValues)).trans
      (LinearMap.ringLmapEquivSelf ℤ ℤ QValues))).toAddEquiv
  exact ⟨(LinearEquiv.ofBijective a.toAddMonoidHom.toRatLinearMap a.bijective).toModuleIso⟩

theorem projectiveLineModel : ProjectiveLineModel := by
  refine ⟨projectiveLineHomeomorph, projectiveLineHomeomorph_plane, ?_, ?_⟩
  · rintro n (rfl | rfl)
    · exact projectiveCohomology_rankOne 0 ⟨0, by decide, rfl⟩
    · exact projectiveCohomology_rankOne 2 ⟨1, by decide, rfl⟩
  · intro n h0 h2
    by_cases h : 0 ≤ n
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
      have hk : ¬ ∃ r ≤ 1, k = 2 * r := by
        rintro ⟨r, hr, rfl⟩
        have hr' : r = 0 ∨ r = 1 := by omega
        rcases hr' with rfl | rfl
        · exact h0 rfl
        · exact h2 rfl
      have := ModuleCat.subsingleton_of_isZero ((P202.ComplexProjective.homology 1 k).2 hk)
      have : Subsingleton ((singularCohomology (k : ℤ)).obj (op projectiveLine)) :=
        (projectiveCohomologyDual k).injective.subsingleton
      exact ModuleCat.isZero_of_subsingleton _
    · exact ((P202.CohomologyPairs.negative ℚ QValues).1 projectiveLine n (by omega)).2

end ProjectiveCohomology

section PointSupport

set_option linter.style.haveILetI false

private theorem globalGerm_isIso {Z : TopCat} [Subsingleton Z] (z : Z)
    (P : Z.Presheaf Coeff.{0}) : IsIso (P.Γgerm z) := by
  let terminal : (OpenNhds z)ᵒᵖ := op ⊤
  have h : ∀ U : (OpenNhds z)ᵒᵖ, (⊤ : OpenNhds z) ≤ U.unop := by
    intro U
    change (⊤ : Opens Z) ≤ U.unop.val
    intro y _
    obtain rfl := Subsingleton.elim y z
    exact U.unop.property
  let ht : IsTerminal terminal :=
    IsTerminal.ofUniqueHom (fun U => (homOfLE (h U)).op) (fun _ _ => Subsingleton.elim _ _)
  exact (colimit.isColimit ((OpenNhds.inclusion z).op ⋙ P)).isIso_ι_app_of_isTerminal terminal ht

private def rationalIsoOfPointStalk {Z : TopCat} [Subsingleton Z] (z : Z)
    (F : Sheaves Z) (e : (stalk z).obj F ≅ scalars) : rational Z ≅ F := by
  let adj := constantAdj Z
  letI : IsIso (TopCat.Presheaf.Γgerm F.obj z) := globalGerm_isIso z F.obj
  let germ := asIso (TopCat.Presheaf.Γgerm F.obj z)
  let a : scalars ⟶ (globalSections Z).obj F := e.inv ≫ germ.inv
  let P : Z.Presheaf Coeff.{0} := (Functor.const (Opens Z)ᵒᵖ).obj scalars
  let ψ := CategoryTheory.toSheafify (Opens.grothendieckTopology Z) P
  have hunit : IsIso (adj.unit.app scalars) := by
    change IsIso (ψ.app (op ⊤))
    have hψ : IsIso ((TopCat.Presheaf.stalkFunctor Coeff.{0} z).map ψ) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z Coeff.{0} P
    let G := CategoryTheory.sheafify (Opens.grothendieckTopology Z) P
    letI : IsIso (TopCat.Presheaf.Γgerm G z) := globalGerm_isIso z G
    have h : IsIso (ψ.app (op ⊤) ≫ TopCat.Presheaf.Γgerm G z) := by
      have eq := TopCat.Presheaf.stalkFunctor_map_germ ⊤ z trivial ψ
      letI : IsIso (TopCat.Presheaf.Γgerm P z) := globalGerm_isIso z P
      have h' : IsIso (TopCat.Presheaf.Γgerm P z ≫
          (TopCat.Presheaf.stalkFunctor Coeff.{0} z).map ψ) :=
        ((asIso (TopCat.Presheaf.Γgerm P z)) ≪≫
          @asIso _ _ _ _ ((TopCat.Presheaf.stalkFunctor Coeff.{0} z).map ψ) hψ).isIso_hom
      exact eq ▸ h'
    exact IsIso.of_isIso_comp_right (ψ.app (op ⊤)) (TopCat.Presheaf.Γgerm G z)
  let f : rational Z ⟶ F := (adj.homEquiv _ _).symm a
  have ha : adj.unit.app scalars ≫ (globalSections Z).map f = a := by
    exact (adj.homEquiv_unit scalars F f).symm.trans ((adj.homEquiv _ _).apply_symm_apply a)
  have : IsIso ((globalSections Z).map f) := by
    have : IsIso a := (e.symm ≪≫ germ.symm).isIso_hom
    have : IsIso (adj.unit.app scalars ≫ (globalSections Z).map f) := ha.symm ▸ this
    exact IsIso.of_isIso_comp_left (adj.unit.app scalars) ((globalSections Z).map f)
  have hf : IsIso f := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
    intro w
    letI : IsIso (f.hom.app (op ⊤)) := ‹IsIso ((globalSections Z).map f)›
    letI : IsIso (TopCat.Presheaf.Γgerm (rational Z).obj w) :=
      globalGerm_isIso w (rational Z).obj
    letI : IsIso (TopCat.Presheaf.Γgerm F.obj w) := globalGerm_isIso w F.obj
    have hh : IsIso (TopCat.Presheaf.Γgerm (rational Z).obj w ≫
        (TopCat.Presheaf.stalkFunctor Coeff.{0} w).map f.hom) := by
      have eq := TopCat.Presheaf.stalkFunctor_map_germ ⊤ w trivial f.hom
      have h' : IsIso (f.hom.app (op ⊤) ≫ TopCat.Presheaf.Γgerm F.obj w) :=
        inferInstance
      exact eq.symm ▸ h'
    exact IsIso.of_isIso_comp_left (TopCat.Presheaf.Γgerm (rational Z).obj w)
      ((TopCat.Presheaf.stalkFunctor Coeff.{0} w).map f.hom)
  exact asIso f

private def pointSupportedDerivedIso (x : surface) (hx : IsClosed ({x} : Set surface))
    (F : Sheaves surface) (hF : SupportedOn ({x} : Set surface) F)
    (e : (stalk x).obj F ≅ scalars) :
    (DerivedCategory.singleFunctor (Sheaves surface) 0).obj F ≅ pointSkyscraper x hx := by
  let i := closedInclusion ({x} : Set surface)
  let p : TopCat.of ({x} : Set surface) := ⟨x, rfl⟩
  let G := (inverseImage i).obj F
  let eG := (inverseImageStalkIso i F p).symm ≪≫ e
  let c := rationalIsoOfPointStalk p G eG
  let h := closedInverseDirectUnit_isIso hx F hF
  let d : F ≅ (directImage i).obj (rational (TopCat.of ({x} : Set surface))) :=
    asIso ((inverseDirectAdjunction i).unit.app F) ≪≫ (directImage i).mapIso c.symm
  letI := (extraordinaryAdjunction hx).isLeftAdjoint
  exact (DerivedCategory.singleFunctor (Sheaves surface) 0).mapIso d ≪≫
    ((directImage i).mapDerivedCategorySingleFunctor 0).symm.app _

/-- Once the unit is controlled on stalks, the actual unit triangle has the
asserted skyscraper cone. -/
theorem coneProfile_of_stalks (x : surface) (hx : IsClosed ({x} : Set surface))
    (h : StalkProfile x)
    (hU : ∀ (y : surface), y ≠ x → ∀ n : ℤ, IsIso ((stalkCohomology y n).map unit)) :
    ConeProfile x hx := by
  let H := (Analytic.cohomology surface 0).obj unitCone
  have hv := coneCohomology_zero x h hU
  have hs := coneCohomology_supported x hU
  obtain ⟨e, he⟩ := singleCohomologyIso unitCone hv
  exact ⟨unitTriangle_distinguished, hv, hs, ⟨e, he⟩,
    ⟨e ≪≫ pointSupportedDerivedIso x hx H hs (exceptionalCohomologyIso x h)⟩⟩

end PointSupport

section RadialContractions

open AlgebraicGeometry LinearAlgebraicGroups ConvolutionSurfaceSpecs
open TransverseConeSpecs NilpotentConeChartSpecs
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

private theorem complexPoint_end_eq_id (a : complexPointScheme ⟶ complexPointScheme) :
    a = 𝟙 _ := by
  apply Over.OverMorphism.ext
  have hb : complexPointScheme.hom = 𝟙 _ := by
    rw [algSpec_obj_hom]
    change Spec.map (𝟙 (CommRingCat.of ℂ)) = _
    exact Spec.map_id (CommRingCat.of ℂ)
  have h := Over.w a
  rw [hb, Category.comp_id] at h
  exact h

private theorem section_terminal (x : surface) (s : projectiveScheme ⟶ incidenceScheme)
    (hs : ExceptionalSection x s) (p : ProjectivePoints) :
    p ≫ s ≫ terminalProjection = x := by
  let p₀ : Points projectiveScheme complexAlgebra := p
  change p₀ ≫ s ≫ terminalProjection = x
  have h := hs.2.2.2.1.w
  calc
    p₀ ≫ s ≫ terminalProjection = p₀ ≫ (toComplexPoint projectiveScheme ≫ x) :=
      congrArg (p₀ ≫ ·) h
    _ = (p₀ ≫ toComplexPoint projectiveScheme) ≫ x := (Category.assoc _ _ _).symm
    _ = x := (congrArg (· ≫ x) (complexPoint_end_eq_id
      (p₀ ≫ toComplexPoint projectiveScheme))).trans (Category.id_comp x)

private theorem section_first (x : surface) (s : projectiveScheme ⟶ incidenceScheme)
    (hs : ExceptionalSection x s) (p : ProjectivePoints) :
    (p ≫ s) ≫ firstProjection = p := by
  let p₀ : Points projectiveScheme complexAlgebra := p
  change (p₀ ≫ s) ≫ firstProjection = p₀
  exact (Category.assoc _ _ _).trans
    ((congrArg (p₀ ≫ ·) hs.2.2.1).trans (Category.comp_id p₀))

private def sectionInBall (c : coneScheme ⟶ twoStepScheme)
    (s : projectiveScheme ⟶ incidenceScheme) (hs : ExceptionalSection (conePoint coneVertex ≫ c) s)
    (U : Set Cone) (hU : coneVertex ∈ U) :
    minuscule ⟶ TopCat.of (AnalyticInverseImage c U) :=
  TopCat.ofHom ⟨fun p => ⟨p ≫ s, coneVertex, hU, by
    rw [Category.assoc]; exact section_terminal _ s hs p⟩, by
    apply Continuous.subtype_mk
    apply continuous_induced_rng.mpr
    have hfst : (fun p : ProjectivePoints => (p ≫ s) ≫ firstProjection) = id := by
      funext p
      exact section_first _ s hs p
    have hsnd : (fun p : ProjectivePoints => ((p ≫ s) ≫ terminalProjection) ≫
        twoStepSchemeInGrassmannian) = fun _ => (conePoint coneVertex ≫ c) ≫
          twoStepSchemeInGrassmannian := by
      funext p
      rw [Category.assoc p s terminalProjection, section_terminal _ s hs p]
    have hc₁ : @Continuous ProjectivePoints ProjectivePoints _ _
        (fun p => (p ≫ s) ≫ firstProjection) := by
      rw [hfst]
      exact continuous_id
    have hc₂ : Continuous (fun p : ProjectivePoints => ((p ≫ s) ≫ terminalProjection) ≫
        twoStepSchemeInGrassmannian) := by
      rw [hsnd]
      exact continuous_const
    exact hc₁.prodMk hc₂⟩

/-- The section of an inverse-image ball induces an isomorphism in singular
cohomology via the given fibrewise contraction. -/
theorem fibreCohomology_of_contractions (c : coneScheme ⟶ twoStepScheme)
    (s : projectiveScheme ⟶ incidenceScheme) (hs : ExceptionalSection (conePoint coneVertex ≫ c) s)
    (h : FibrewiseContractions c s) (k : BallCoordinates) (r : ℝ) (hr : 0 < r)
    (hU : coneVertex ∈ coneBall k r) :
    ∃ j : minuscule ⟶ TopCat.of (AnalyticInverseImage c (coneBall k r)),
      (∀ p : ProjectivePoints, (j p).val = p ≫ s) ∧
      ∀ n : ℤ, IsIso ((singularCohomology n).map j.op) := by
  let Z := TopCat.of (AnalyticInverseImage c (coneBall k r))
  let j : minuscule ⟶ Z := sectionInBall c s hs (coneBall k r) hU
  let p : Z ⟶ minuscule := TopCat.ofHom ⟨fun v => firstStageMap v.val,
    firstStageMap.hom.continuous.comp continuous_subtype_val⟩
  have hjp : j ≫ p = 𝟙 minuscule := by
    apply TopCat.ext
    intro v
    exact section_first _ s hs v
  obtain ⟨H, hH, _, _⟩ := h
  let e : TopCat.Homotopy (p ≫ j) (𝟙 Z) := {
    toContinuousMap := H k r hr
    map_zero_left := fun v => Subtype.ext (hH k r hr v).2.1
    map_one_left := fun v => (hH k r hr v).1 }
  refine ⟨j, fun _ => rfl, fun n => ?_⟩
  let F := singularCohomology n
  have h₁ : F.map j.op ≫ F.map p.op = 𝟙 _ := by
    rw [← F.map_comp, ← op_comp,
      (P202.CohomologyPairs.homotopy_invariant ℚ Analytic.SingularCochains.Values.{0}).1 e n,
      op_id, F.map_id]
  have h₂ : F.map p.op ≫ F.map j.op = 𝟙 _ := by
    rw [← F.map_comp, ← op_comp, hjp, op_id, F.map_id]
  exact ⟨⟨F.map p.op, h₁, h₂⟩⟩

end RadialContractions


section OpenRestriction

set_option backward.isDefEq.respectTransparency false

open private stalkPushforward_naturality from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

private def inverseImageStalkNatIso {X Y : TopCat} (f : X ⟶ Y) (y : X) :
    stalk (f y) ≅ inverseImage f ⋙ stalk y := by
  refine NatIso.ofComponents (fun F => inverseImageStalkIso f F y) ?_
  intro F G v
  let A := inverseDirectAdjunction f
  let L := inverseImage f
  let R := directImage f
  let S := stalk (f y)
  change S.map v ≫ (S.map (A.unit.app G) ≫
    TopCat.Presheaf.stalkPushforward Coeff.{0} f (L.obj G).obj y) =
    (S.map (A.unit.app F) ≫
      TopCat.Presheaf.stalkPushforward Coeff.{0} f (L.obj F).obj y) ≫
      (stalk y).map (L.map v)
  have hu : v ≫ A.unit.app G = A.unit.app F ≫ R.map (L.map v) := A.unit.naturality v
  rw [← Category.assoc, ← Functor.map_comp, hu]
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact stalkPushforward_naturality f (L.map v).hom y

private def exactDerivedCohomologyNatIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F := by
  let C₁ := DerivedCategory.homologyFunctor C n
  let D₁ := DerivedCategory.homologyFunctor D n
  let C₀ := HomologicalComplex.homologyFunctor C (.up ℤ) n
  let D₀ := HomologicalComplex.homologyFunctor D (.up ℤ) n
  let Q := DerivedCategory.Q (C := C)
  let M := F.mapHomologicalComplex (.up ℤ)
  have e : M ⋙ D₀ ≅ C₀ ⋙ F := by
    refine NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso F) ?_
    intro K L v
    exact ShortComplex.mapHomologyIso_hom_naturality (HomologicalComplex.shortComplexFunctor C
      (.up ℤ) n |>.map v) F
  refine Localization.liftNatIso Q (HomologicalComplex.quasiIso C (.up ℤ))
    (Q ⋙ (F.mapDerivedCategory ⋙ D₁)) (Q ⋙ (C₁ ⋙ F)) _ _ ?_
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft M (DerivedCategory.homologyFunctorFactors D n) ≪≫ e ≪≫
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm F ≪≫
    Functor.associator _ _ _

private theorem openUnit_stalks (x : surface) (hx : IsClosed ({x} : Set surface))
    (h : OpenUnit x hx) (y : surface) (hy : y ≠ x) (n : ℤ) :
    IsIso ((stalkCohomology y n).map unit) := by
  let U := complementOpen {x} hx
  let j := openInclusion U
  let p : TopCat.of U := ⟨y, hy⟩
  let e₁ := Functor.isoWhiskerLeft (Analytic.cohomology surface n) (inverseImageStalkNatIso j p)
  let e₂ := Functor.isoWhiskerRight (exactDerivedCohomologyNatIso (inverseImage j) n) (stalk p)
  let e := e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫ e₂.symm ≪≫ Functor.associator _ _ _
  apply (NatIso.isIso_map_iff e unit).mpr
  change IsIso (((derivedInverseImage j) ⋙ (Analytic.cohomology (TopCat.of U) n ⋙ stalk p)).map unit)
  let : IsIso ((derivedInverseImage j).map unit) := h
  exact (Analytic.cohomology (TopCat.of U) n ⋙ stalk p).map_isIso ((derivedInverseImage j).map unit)

/-- The open-orbit unit and the exceptional stalk calculation suffice for
the skyscraper statement about this unit triangle. -/
theorem coneProfile_of_openUnit (x : surface) (hx : IsClosed ({x} : Set surface))
    (hU : OpenUnit x hx) (h : StalkProfile x) : ConeProfile x hx :=
  coneProfile_of_stalks x hx h (openUnit_stalks x hx hU)

end OpenRestriction

section TerminalChart

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry LinearAlgebraicGroups ConvolutionSurfaceSpecs TransverseConeSpecs
open NilpotentConeChartSpecs

open private change_basis_points from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep

private theorem surfacePointEquiv :
    ∃ e : surface ≃ₜ TwoStepPoints, ∀ q : surface,
      (e q).val = q ≫ twoStepSchemeInGrassmannian := by
  obtain ⟨e, he⟩ := LatticeModels.stableSchemePointComparison twoStepBasis twoStepRank shift
  have h : IsInducing (fun p : TwoStepPoints => p.val) := IsInducing.subtypeVal
  have hc : IsInducing (fun q : surface => (e q).val) := by
    have heq : (fun q : surface => (e q).val) = fun q => q ≫ twoStepSchemeInGrassmannian := funext he
    rw [heq]
    exact ⟨rfl⟩
  let i : IsEmbedding (fun q : surface => e q) :=
    ⟨(h.of_comp_iff).mp hc, e.injective⟩
  exact ⟨i.toHomeomorphOfSurjective e.surjective, he⟩

private theorem surfaceShortModel :
    ∃ e : surface ≃ₜ ShortStablePoints, ∀ q : surface,
      (grassmannianSubspace (windowBasis 2 0 2)
        (windowDimension_le NilpotentConeChartSpecs.shortDimension) (e q).val).map
          twoStepCoordinates.toLinearMap = secondPlane q := by
  let b := windowBasis 2 0 2
  let hd : 2 ≤ Module.finrank ℂ (Window 2 0 2) := MinusculeAndTwoStepSpecs.shortWindowRank 2
  let f := twoStepCoordinates
  obtain ⟨a, ha⟩ := change_basis_points b f hd twoStepRank
  let A : GrassmannianPoints b hd ≃ₜ GrassmannianPoints twoStepBasis twoStepRank := a
  have ht : shift.comp f.toLinearMap = f.toLinearMap.comp (windowOperator 2 0 2) :=
    LinearMap.ext fun x => (MinusculeAndTwoStep.twoStepStableModel.1 x).symm
  have hiff (p : GrassmannianPoints b hd) : StablePlane b hd (windowOperator 2 0 2) p ↔
      StablePlane twoStepBasis twoStepRank shift (A p) := by
    unfold StablePlane
    have hp : grassmannianSubspace twoStepBasis twoStepRank (A p) =
        (grassmannianSubspace b hd p).map f.toLinearMap := ha p
    rw [hp, ← Submodule.map_comp, ht, Submodule.map_comp,
      Submodule.map_le_map_iff_of_injective f.injective]
  let j : ShortStablePoints ≃ₜ TwoStepPoints := A.subtype hiff
  obtain ⟨e, he⟩ := surfacePointEquiv
  refine ⟨e.trans j.symm, fun q => ?_⟩
  calc
    (grassmannianSubspace b hd (j.symm (e q)).val).map f.toLinearMap =
        grassmannianSubspace twoStepBasis twoStepRank (j (j.symm (e q))).val :=
      (ha (j.symm (e q)).val).symm
    _ = secondPlane q := by rw [j.apply_symm_apply, he]; rfl

private theorem analyticalTerminalChart (c : coneScheme ⟶ twoStepScheme)
    (hS : IsOpen shortChartSet)
    (hChart : ∃ (e : Cone ≃ₜ shortChartSet) (eL : Cone ≃ₜ shortLatticeChartSet),
      (∀ z : Cone, (e z).val.val =
        shortGraphPoint (graphCoefficientMatrix z.val.1 z.val.2.1 z.val.2.2)) ∧
      (∀ z : Cone, latticeSubspace 0 2 (eL z).val.val =
        grassmannianSubspace (windowBasis 2 0 2)
          (windowDimension_le NilpotentConeChartSpecs.shortDimension) (e z).val.val) ∧
      (eL coneVertex).val.val = scalarPoint ∧
      ∀ z : Cone, secondPlane (conePoint z ≫ c) =
        (latticeSubspace 0 2 (eL z).val.val).map twoStepCoordinates.toLinearMap) :
    ∃ (W : Opens surface) (f : Cone ≃ₜ W), ∀ z : Cone, (f z).val = conePoint z ≫ c := by
  obtain ⟨j, hj⟩ := surfaceShortModel
  obtain ⟨e, eL, _, hLat, _, hc⟩ := hChart
  let W : Opens surface := ⟨j ⁻¹' shortChartSet, hS.preimage j.continuous⟩
  let f : W ≃ₜ shortChartSet := j.subtype (fun _ => Iff.rfl)
  refine ⟨W, e.trans f.symm, fun z => ?_⟩
  have hq : j (conePoint z ≫ c) = (e z).val := by
    apply Subtype.ext
    apply grassmannianSubspace_injective _ _
    apply Submodule.map_injective_of_injective twoStepCoordinates.injective
    rw [hj, hc, hLat]
  apply j.injective
  change (f (f.symm (e z))).val = j (conePoint z ≫ c)
  rw [f.apply_symm_apply, hq]


open NilpotentConeChartSpecs.Expected in
/-- The radial neighborhoods in the actual complex-point topology are the
images of the vertex balls under the chart. -/
private theorem terminalRadialNeighborhoods (c : coneScheme ⟶ twoStepScheme)
    (W : Opens surface) (f : Cone ≃ₜ W) (hf : ∀ z : Cone, (f z).val = conePoint z ≫ c)
    (hRad : RadialNeighborhoods) :
    ∃ B : ∀ r : ℝ, 0 < r → Opens surface,
      (∀ (r : ℝ) (hr : 0 < r),
        (conePoint coneVertex ≫ c : surface) ∈ B r hr ∧ (B r hr : Set surface) =
          (fun z => conePoint z ≫ c) '' coneBall .radial r) ∧
      (∀ U : Opens surface, (conePoint coneVertex ≫ c : surface) ∈ U →
        ∃ (r : ℝ) (hr : 0 < r), B r hr ≤ U) := by
  let g : Cone → surface := fun z => conePoint z ≫ c
  have hg : IsOpenEmbedding g := by
    have he : IsOpenEmbedding (Subtype.val ∘ f : Cone → surface) :=
      W.isOpenEmbedding.comp f.isOpenEmbedding
    have heq : (Subtype.val ∘ f : Cone → surface) = g := funext hf
    exact heq ▸ he
  let B (r : ℝ) (hr : 0 < r) : Opens surface :=
    ⟨g '' coneBall .radial r, hg.isOpenMap _ (hRad.2.1 r hr).1⟩
  refine ⟨B, fun r hr => ⟨⟨coneVertex, mem_of_mem_nhds (hRad.2.1 r hr).2, rfl⟩, rfl⟩, ?_⟩
  intro U hU
  have hU' : g ⁻¹' (U : Set surface) ∈ nhds coneVertex :=
    (U.isOpen.preimage hg.continuous).mem_nhds hU
  obtain ⟨r, hr, hle⟩ := hRad.2.2.1 _ hU'
  exact ⟨r, hr, fun _ ⟨z, hz, hq⟩ => hq ▸ hle hz⟩

/-- These are the neighborhoods of the same terminal vertex in the
analytic Schubert surface, with the singular cohomology comparison along
the section in each inverse image. -/
theorem radialNeighborhoods_and_fibreCohomology (h : TransverseCone) :
    ∃ (x : surface) (c : coneScheme ⟶ twoStepScheme) (s : projectiveScheme ⟶ incidenceScheme)
      (B : ∀ r : ℝ, 0 < r → Opens surface),
      IsTerminalConeChart c ∧ ExceptionalSection x s ∧ conePoint coneVertex ≫ c = x ∧
      (∀ (r : ℝ) (hr : 0 < r),
        x ∈ B r hr ∧ (B r hr : Set surface) =
          (fun z => conePoint z ≫ c) '' coneBall .radial r) ∧
      (∀ U : Opens surface, x ∈ U → ∃ (r : ℝ) (hr : 0 < r), B r hr ≤ U) ∧
      ∃ j : ∀ (r : ℝ) (hr : 0 < r),
        minuscule ⟶ TopCat.of ((Opens.map convolutionMap).obj (B r hr)),
        ∀ (r : ℝ) (hr : 0 < r), (∀ p : ProjectivePoints, (j r hr p).val = p ≫ s) ∧
          ∀ n : ℤ, IsIso ((singularCohomology n).map (j r hr).op) := by
  obtain ⟨_, _, _, hRad, _, c, x, s, hc, hs, hcx, ho, _, hChart, _, hFib⟩ := h
  subst x
  obtain ⟨W, f, hf⟩ := analyticalTerminalChart c ho hChart
  obtain ⟨B, hB, hbasis⟩ := terminalRadialNeighborhoods c W f hf hRad
  have hex (r : ℝ) (hr : 0 < r) :
      ∃ j : minuscule ⟶ TopCat.of ((Opens.map convolutionMap).obj (B r hr)),
        (∀ p : ProjectivePoints, (j p).val = p ≫ s) ∧
          ∀ n : ℤ, IsIso ((singularCohomology n).map j.op) := by
    let P : Set ordered := (Opens.map convolutionMap).obj (B r hr)
    let Q : Set ordered := {q | ∃ z ∈ coneBall .radial r, q ≫ terminalProjection = conePoint z ≫ c}
    have heq : Q = P := by
      ext q
      have hmem : convolutionMap q ∈ (B r hr : Set surface) ↔
          convolutionMap q ∈ (fun z => conePoint z ≫ c) '' coneBall .radial r :=
        Iff.of_eq (congrArg (fun S : Set surface => convolutionMap q ∈ S) (hB r hr).2)
      exact (show q ∈ Q ↔
          convolutionMap q ∈ (fun z => conePoint z ≫ c) '' coneBall .radial r from
        ⟨fun ⟨z, hz, hq⟩ => ⟨z, hz, hq.symm⟩, fun ⟨z, hz, hq⟩ => ⟨z, hz, hq.symm⟩⟩).trans hmem.symm
    let E : Q ≃ₜ P := Homeomorph.setCongr heq
    let e := TopCat.isoOfHomeo (X := TopCat.of Q) (Y := TopCat.of P) E
    have hv : coneVertex ∈ coneBall .radial r := mem_of_mem_nhds (hRad.2.1 r hr).2
    obtain ⟨j, hj, hij⟩ := fibreCohomology_of_contractions c s hs hFib .radial r hr hv
    refine ⟨j ≫ e.hom, fun p => hj p, fun n => ?_⟩
    rw [op_comp, Functor.map_comp]
    let : IsIso ((singularCohomology n).map j.op) := hij n
    infer_instance
  choose j hj using hex
  exact ⟨_, c, s, B, hc, hs, rfl, hB, hbasis, j, hj⟩


open private isClosed_fromCharts from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianIncidenceTopology

private theorem chartPoint_injective {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d) :
    Function.Injective (grassmannianChartPoint b hd I) := by
  let C := grassmannianCharts b hd
  let e := LinearAlgebraicGroups.GrassmannianCharts.chartMatrixEquiv I complexAlgebra
  let : IsOpenImmersion (C.chart I).left := C.openChart I
  let : Mono (C.chart I) := Over.mono_of_mono_left _
  intro A B h
  apply e.symm.injective
  exact (cancel_mono (C.chart I)).mp h

private theorem grassmannian_isClosed_singleton {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (p : GrassmannianPoints b hd) :
    IsClosed ({p} : Set (GrassmannianPoints b hd)) := by
  apply isClosed_fromCharts b hd
  intro I
  let f := grassmannianChartPoint b hd I
  by_cases h : p ∈ Set.range f
  · obtain ⟨A, rfl⟩ := h
    have heq : f ⁻¹' ({f A} : Set (GrassmannianPoints b hd)) = {A} := by
      ext B
      change f B = f A ↔ B = A
      exact ⟨fun h => chartPoint_injective b hd I h, fun h => congrArg f h⟩
    rw [heq]
    exact isClosed_singleton
  · change IsClosed (f ⁻¹' {p})
    rw [Set.preimage_singleton_eq_empty.mpr h]
    exact isClosed_empty

/-- The analytic topology on the reduced Schubert scheme has closed points. -/
theorem surface_isClosed_singleton (x : surface) : IsClosed ({x} : Set surface) := by
  obtain ⟨e, he⟩ := surfacePointEquiv
  let f : surface → GrassmannianPoints twoStepBasis twoStepRank := fun q =>
    q ≫ twoStepSchemeInGrassmannian
  have hf : Continuous f := show Continuous f from continuous_induced_dom
  have hi : Function.Injective f := by
    intro y z hs
    apply e.injective
    exact Subtype.ext ((he y).trans (hs.trans (he z).symm))
  have h : f ⁻¹' ({f x} : Set (GrassmannianPoints twoStepBasis twoStepRank)) =
      ({x} : Set surface) := by
    ext y
    change f y = f x ↔ y = x
    exact ⟨fun h => hi h, fun hv => congrArg f hv⟩
  rw [← h]
  exact (grassmannian_isClosed_singleton twoStepBasis twoStepRank (f x)).preimage hf

/-- The scalar terminal point is uniquely determined on the shared scheme. -/
theorem scalarTerminalPoint_unique {x y : surface} (hx : ScalarTerminalPoint x)
    (hy : ScalarTerminalPoint y) : x = y := by
  obtain ⟨e, he⟩ := surfacePointEquiv
  apply e.injective
  apply Subtype.ext
  apply grassmannianSubspace_injective twoStepBasis twoStepRank
  rw [he, he]
  exact hx.2.1.trans hy.2.1.symm

/-- Fibre inclusions into two inverse images agree after including the smaller
open in the larger one, so their singular cohomology maps are compatible. -/
theorem fibreCohomology_restriction (s : projectiveScheme ⟶ incidenceScheme)
    {U V : Opens surface} (i : U ⟶ V)
    (jU : minuscule ⟶ TopCat.of ((Opens.map convolutionMap).obj U))
    (jV : minuscule ⟶ TopCat.of ((Opens.map convolutionMap).obj V))
    (hU : ∀ p : ProjectivePoints, (jU p).val = p ≫ s)
    (hV : ∀ p : ProjectivePoints, (jV p).val = p ≫ s) (n : ℤ) :
    (singularCohomology n).map (((Opens.map convolutionMap ⋙ Opens.toTopCat ordered).map i).op) ≫
      (singularCohomology n).map jU.op = (singularCohomology n).map jV.op := by
  let v := (Opens.map convolutionMap ⋙ Opens.toTopCat ordered).map i
  have h : jU ≫ v = jV := by
    apply TopCat.ext
    intro p
    apply Subtype.ext
    exact (hU p).trans (hV p).symm
  change (singularCohomology n).map v.op ≫ _ = _
  rw [← Functor.map_comp, ← op_comp, h]

end TerminalChart


section StalkComparison

open AlgebraicGeometry LinearAlgebraicGroups
open TransverseConeSpecs NilpotentConeChartSpecs

set_option backward.isDefEq.respectTransparency false

private abbrev inverseImageSingularCohomology (n : ℤ) : surface.Presheaf Coeff.{0} :=
  (Opens.map convolutionMap).op ⋙ (Opens.toTopCat ordered).op ⋙ singularCohomology n

private theorem radialSingularStalk (x : surface) (h : RadialFibreComparison x) (n : ℤ) :
    Nonempty (stalkColimit (inverseImageSingularCohomology n) x ≅
      (singularCohomology n).obj (op minuscule)) := by
  obtain ⟨c, s, B, _, _, _, hB, hbasis, j, hj⟩ := h
  let R := {r : ℝ // 0 < r}
  let N (r : R) : OpenNhds x := ⟨B r.val r.property, (hB r.val r.property).1⟩
  have hN : Monotone N := by
    intro a b hab
    change (B a.val a.property : Set surface) ⊆ (B b.val b.property : Set surface)
    rw [(hB a.val a.property).2, (hB b.val b.property).2]
    exact Set.image_mono (fun z hz => lt_of_lt_of_le hz (show a.val ≤ b.val from hab))
  let : IsCodirectedOrder R := inferInstance
  let : Nonempty R := ⟨⟨1, by norm_num⟩⟩
  let hI : hN.functor.Initial := (hN.initial_functor_iff).mpr (fun U => by
    obtain ⟨r, hr, hle⟩ := hbasis U.val U.property
    exact ⟨⟨r, hr⟩, hle⟩)
  let P := inverseImageSingularCohomology n
  let G := (OpenNhds.inclusion x).op ⋙ P
  let C := (singularCohomology n).obj (op minuscule)
  let I := hN.functor.op
  let : I.Final := Functor.final_op_of_initial hN.functor
  have (r : R) : IsIso ((singularCohomology n).map (j r.val r.property).op) :=
    (hj r.val r.property).2.2.2.2.2 n
  let η : I ⋙ G ≅ (Functor.const Rᵒᵖ).obj C := NatIso.ofComponents
    (fun r => asIso ((singularCohomology n).map (j r.unop.val r.unop.property).op))
    (by
      intro a b f
      let l : B b.unop.val b.unop.property ⟶ B a.unop.val a.unop.property :=
        homOfLE (hN (leOfHom f.unop))
      change (singularCohomology n).map ((Opens.map convolutionMap ⋙
        Opens.toTopCat ordered).map l).op ≫
        (singularCohomology n).map (j b.unop.val b.unop.property).op =
        (singularCohomology n).map (j a.unop.val a.unop.property).op ≫ 𝟙 C
      rw [Category.comp_id]
      exact fibreCohomology_restriction s l _ _ (hj _ _).1 (hj _ _).1 n)
  exact ⟨(Functor.Final.colimitIso I G).symm ≪≫ HasColimit.isoOfNatIso η ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone Rᵒᵖ C)⟩

/-- Use the restriction-natural sheaf comparison on the ordered space, and the
same fibre inclusions in the cofinal radial neighborhoods. -/
private theorem shiftedImageStalk (x : surface) (h : RadialFibreComparison x)
    [SecondCountableTopology ordered] [LocallyCompactSpace ordered] [T2Space ordered]
    (hBasis : Analytic.SingularCochains.HasContractibleOpenBasis ordered) (n : ℤ) :
    Nonempty (((stalkCohomology x n).obj convolution.obj) ≅
      (singularCohomology (n + 2)).obj (op minuscule)) := by
  let F := LocalSheaf.sheafInDegreeZero (rational ordered)
  let D := (directImage convolutionMap).rightDerivedFunctorPlus
  let q := n + 2
  obtain ⟨eS⟩ := DerivedLocalSheaves.higherDirectImageStalk convolutionMap x q F
  obtain ⟨eC⟩ := ConstantSheafComparison.absoluteCohomology ordered hBasis q
  obtain ⟨eR⟩ := radialSingularStalk x h q
  let iY := DerivedCategory.Plus.ι (C := Sheaves ordered)
  let iX := DerivedCategory.Plus.ι (C := Sheaves surface)
  let a : F⟦(2 : ℤ)⟧ ≅ orderedFactor := iY.preimageIso ((iY.commShiftIso (2 : ℤ)).app F)
  let e : convolution.obj ≅ (D.obj F).obj⟦(2 : ℤ)⟧ :=
    iX.mapIso (D.mapIso a.symm ≪≫ (D.commShiftIso (2 : ℤ)).app F) ≪≫
      (iX.commShiftIso (2 : ℤ)).app (D.obj F)
  let eP := Functor.isoWhiskerLeft (Opens.map convolutionMap).op eC.symm
  let J := (OpenNhds.inclusion x).op
  exact ⟨(stalkCohomology x n).mapIso e ≪≫
    (stalk x).mapIso ((shiftCohomology surface n 2).app (D.obj F).obj) ≪≫ eS ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft J eP) ≪≫ eR⟩

/-- The shifted direct image has the two asserted nonzero stalk cohomology
groups once the ordered space meets the comparison hypotheses. -/
theorem shiftedImageStalkDegrees (x : surface) (h : RadialFibreComparison x)
    [SecondCountableTopology ordered] [LocallyCompactSpace ordered] [T2Space ordered]
    (hBasis : Analytic.SingularCochains.HasContractibleOpenBasis ordered) :
    (∀ n : ℤ, (n = -2 ∨ n = 0) →
      Nonempty ((stalkCohomology x n).obj convolution.obj ≅ scalars)) ∧
    (∀ n : ℤ, n ≠ -2 → n ≠ 0 → IsZero ((stalkCohomology x n).obj convolution.obj)) := by
  obtain ⟨_, _, hQ, hZ⟩ := projectiveLineModel
  let P := TopCat.isoOfHomeo projectiveLineHomeomorph
  constructor
  · intro n hn
    obtain ⟨e⟩ := shiftedImageStalk x h hBasis n
    obtain ⟨f⟩ := hQ (n + 2) (by omega)
    exact ⟨e ≪≫ (singularCohomology (n + 2)).mapIso P.op ≪≫ f⟩
  · intro n h1 h2
    obtain ⟨e⟩ := shiftedImageStalk x h hBasis n
    exact (hZ (n + 2) (by omega) (by omega)).of_iso
      (e ≪≫ (singularCohomology (n + 2)).mapIso P.op)


private theorem contractibleOpenBasis_restrict {X : TopCat}
    (h : Analytic.SingularCochains.HasContractibleOpenBasis X) (U : Opens X) :
    Analytic.SingularCochains.HasContractibleOpenBasis (TopCat.of U) := by
  intro x V hx
  let f := openInclusion U
  let A := U.isOpenEmbedding.functor.obj V
  obtain ⟨W, hxW, hWA, hW⟩ := h x.val A ⟨x, hx, rfl⟩
  let W' := (Opens.map f).obj W
  have hsub : (W : Set X) ⊆ Set.range (Subtype.val : U → X) := by
    intro y hy
    obtain ⟨z, _, hz⟩ := hWA hy
    exact ⟨z, hz⟩
  refine ⟨W', hxW, ?_, (IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsub).contractibleSpace_iff.mpr hW⟩
  intro y hy
  obtain ⟨z, hz, heq⟩ := hWA hy
  exact Subtype.ext heq ▸ hz

/-- The topological hypotheses for GS06 pass to all the open inverse images.
The radial basis and the inclusion maps are those of the actual vertex. -/
theorem radialFibreComparison_of_orderedTopology (h : TransverseCone)
    [SecondCountableTopology ordered] [LocallyCompactSpace ordered] [T2Space ordered]
    (hBasis : Analytic.SingularCochains.HasContractibleOpenBasis ordered) :
    ∃ x : surface, ConvolutionSurfaceSpecs.ScalarTerminalPoint x ∧ RadialFibreComparison x := by
  obtain ⟨x, c, s, B, hc, hs, hcx, hB, hbasis, j, hj⟩ :=
    radialNeighborhoods_and_fibreCohomology h
  refine ⟨x, hs.1, c, s, B, hc, hs, hcx, hB, hbasis, j, ?_⟩
  intro r hr
  let U := (Opens.map convolutionMap).obj (B r hr)
  exact ⟨(hj r hr).1, inferInstanceAs (SecondCountableTopology U),
    U.isOpen.locallyCompactSpace, inferInstanceAs (T2Space U),
    contractibleOpenBasis_restrict hBasis U, (hj r hr).2⟩

end StalkComparison

section TwistedDescent

open MonoidalCategory

open ConvolutionConstantDescentSpec (tensorPresheaf coefficientTensor constantSections scalarProduct)
open scoped TensorProduct

open private tensorOfConstants sheafifiedTensorOfConstants_isIso constantPullback_comp
  comparedUnit comparedUnit_sections pullback_constantTransition
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent

section CoefficientDescent

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Pure tensors of constant sections determine maps out of the pulled-back tensor. -/
private theorem tensor_hom_ext {Z X Y : TopCat} (a : Z ⟶ X) (b : Z ⟶ Y)
    {S : Sheaves Z} {u v : pulledBackTensor a b ⟶ S}
    (h : ∀ U, (tensorOfConstants a b).app U ≫
        (sectionTensorUnit ((inverseImage a).obj (rational X))
          ((inverseImage b).obj (rational Y))).app U ≫ u.hom.app U =
      (tensorOfConstants a b).app U ≫
        (sectionTensorUnit ((inverseImage a).obj (rational X))
          ((inverseImage b).obj (rational Y))).app U ≫ v.hom.app U) : u = v := by
  let L := presheafToSheaf (Opens.grothendieckTopology Z) Coeff.{0}
  let A := sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}
  let f := tensorOfConstants a b
  have : IsIso (L.map f) := sheafifiedTensorOfConstants_isIso a b
  apply (cancel_epi (L.map f)).mp
  apply (A.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext U
  exact h U

private theorem coefficientTransition_constants {W X : TopCat} (f g : W ⟶ X)
    (U : (Opens W)ᵒᵖ) :
    (constantSections W U ≫ (constantPullback f).inv.hom.app U) ≫
        (coefficientTransition f g).hom.hom.app U =
      constantSections W U ≫ (constantPullback g).inv.hom.app U := by
  change constantSections W U ≫
      ((constantPullback f).inv ≫ (coefficientTransition f g).hom).hom.app U = _
  simp [coefficientTransition]

/-- Multiplication commutes with the tensor of the actual coefficient maps on the two factors. -/
private theorem coefficientTensorIso_multiplication {W X Y : TopCat}
    (a a' : W ⟶ X) (b b' : W ⟶ Y)
    (μ : pulledBackTensor a b ≅ rational W) (μ' : pulledBackTensor a' b' ≅ rational W)
    (hμ : MultipliesCoefficients a b μ) (hμ' : MultipliesCoefficients a' b' μ') :
    (coefficientTensorIso (coefficientTransition a a') (coefficientTransition b b')).hom ≫
      μ'.hom = μ.hom := by
  let α := coefficientTransition a a'
  let β := coefficientTransition b b'
  let J := Opens.grothendieckTopology W
  let η := (sheafificationAdjunction J Coeff.{0}).unit
  let θ := tensorPresheafIso α β
  apply tensor_hom_ext a b
  intro U
  have hn := NatTrans.congr_app (η.naturality θ.hom) U
  let u := (sectionTensorUnit ((inverseImage a).obj (rational X))
    ((inverseImage b).obj (rational Y))).app U
  let u' := (sectionTensorUnit ((inverseImage a').obj (rational X))
    ((inverseImage b').obj (rational Y))).app U
  change θ.hom.app U ≫ u' = u ≫ (coefficientTensorIso α β).hom.hom.app U at hn
  have he : (tensorOfConstants a b).app U ≫ θ.hom.app U =
      (tensorOfConstants a' b').app U := by
    have h := congrArg₂ (fun v w => v ⊗ₘ w)
      (coefficientTransition_constants a a' U) (coefficientTransition_constants b b' U)
    exact (tensorHom_comp_tensorHom _ _ _ _).trans h
  change (tensorOfConstants a b).app U ≫ u ≫
      (coefficientTensorIso α β).hom.hom.app U ≫ μ'.hom.hom.app U = _
  calc
    _ = (tensorOfConstants a b).app U ≫ θ.hom.app U ≫ u' ≫ μ'.hom.hom.app U := by
      simpa only [Category.assoc] using
        congrArg (fun t => (tensorOfConstants a b).app U ≫ t ≫ μ'.hom.hom.app U) hn.symm
    _ = _ := by
      rw [← Category.assoc (f := (tensorOfConstants a b).app U), he]
      exact (hμ' U).trans (hμ U).symm

private theorem compositionUnit_constants {W Z X : TopCat} (k : W ⟶ Z) (a : Z ⟶ X)
    (U : (Opens Z)ᵒᵖ) :
    (constantSections Z U ≫ (constantPullback a).inv.hom.app U) ≫
        (compositionUnit k a).hom.app U =
      constantSections W ((Opens.map k).op.obj U) ≫
        (constantPullback (k ≫ a)).inv.hom.app ((Opens.map k).op.obj U) := by
  have e :
      (inverseImage k).map (constantPullback a).inv ≫
        (inverseImageComposition k a).inv.app (rational X) ≫
          (constantPullback (k ≫ a)).hom = (constantPullback k).hom := by
    rw [← constantPullback_comp k a]
    simp
  have e' := congrArg ((inverseDirectAdjunction k).homEquiv _ _) e
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at e'
  change (constantPullback a).inv ≫ compositionUnit k a ≫
    (directImage k).map (constantPullback (k ≫ a)).hom = comparedUnit k at e'
  have eq := congrArg (fun t => t.hom.app U) e'
  change (constantPullback a).inv.hom.app U ≫ (compositionUnit k a).hom.app U ≫
    (constantPullback (k ≫ a)).hom.hom.app ((Opens.map k).op.obj U) =
      (comparedUnit k).hom.app U at eq
  rw [← cancel_mono ((constantPullback (k ≫ a)).hom.hom.app ((Opens.map k).op.obj U))]
  simp only [Category.assoc]
  rw [eq, comparedUnit_sections]
  let V := (Opens.map k).op.obj U
  have hinv : (constantPullback (k ≫ a)).inv.hom.app V ≫
      (constantPullback (k ≫ a)).hom.hom.app V = 𝟙 _ :=
    congrArg (fun t : rational W ⟶ rational W => t.hom.app V)
      (constantPullback (k ≫ a)).inv_hom_id
  exact ((Category.assoc _ _ _).trans
    ((congrArg (constantSections W V ≫ ·) hinv).trans (Category.comp_id _))).symm

private theorem pullbackTensorMap_multiplication {W Z X Y : TopCat} (k : W ⟶ Z)
    (a : Z ⟶ X) (b : Z ⟶ Y)
    (μ : pulledBackTensor a b ≅ rational Z) (μ' : pulledBackTensor (k ≫ a) (k ≫ b) ≅ rational W)
    (hμ : MultipliesCoefficients a b μ) (hμ' : MultipliesCoefficients (k ≫ a) (k ≫ b) μ') :
    pullbackTensorMap k a b ≫ μ'.hom = (inverseImage k).map μ.hom ≫ (constantPullback k).hom := by
  let A := inverseDirectAdjunction k
  apply (A.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  have eq : A.homEquiv _ _ (pullbackTensorMap k a b) =
      ((sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}).homEquiv _ _).symm
        (pulledTensorSections k a b) := (A.homEquiv _ _).apply_symm_apply _
  rw [eq]
  apply tensor_hom_ext a b
  intro U
  let η := sectionTensorUnit ((inverseImage a).obj (rational X)) ((inverseImage b).obj (rational Y))
  let adj := sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}
  let E := adj.homEquiv
    (tensorPresheaf ((inverseImage a).obj (rational X)) ((inverseImage b).obj (rational Y)))
    ((directImage k).obj (pulledBackTensor (k ≫ a) (k ≫ b)))
  let t := E.symm (pulledTensorSections k a b)
  have h := E.apply_symm_apply (pulledTensorSections k a b)
  change adj.homEquiv _ _ t = _ at h
  rw [Adjunction.homEquiv_unit] at h
  have he := NatTrans.congr_app h U
  change η.app U ≫ t.hom.app U = (pulledTensorSections k a b).app U at he
  change (tensorOfConstants a b).app U ≫ η.app U ≫ t.hom.app U ≫
      μ'.hom.hom.app ((Opens.map k).op.obj U) =
    (tensorOfConstants a b).app U ≫ η.app U ≫ μ.hom.hom.app U ≫ (comparedUnit k).hom.app U
  let V := (Opens.map k).op.obj U
  have hsections :
      (tensorOfConstants a b).app U ≫ (pulledTensorSections k a b).app U =
        (tensorOfConstants (k ≫ a) (k ≫ b)).app V ≫
          (sectionTensorUnit ((inverseImage (k ≫ a)).obj (rational X))
            ((inverseImage (k ≫ b)).obj (rational Y))).app V := by
    have h := congrArg₂ (fun v w => v ⊗ₘ w)
      (compositionUnit_constants k a U) (compositionUnit_constants k b U)
    have ht := (tensorHom_comp_tensorHom _ _ _ _).trans h
    let ε := (sectionTensorUnit ((inverseImage (k ≫ a)).obj (rational X))
      ((inverseImage (k ≫ b)).obj (rational Y))).app V
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ ε) ht)
  have hZ : (tensorOfConstants a b).app U ≫ η.app U ≫ μ.hom.hom.app U =
      scalarProduct ≫ constantSections Z U := hμ U
  calc
    _ = ((tensorOfConstants a b).app U ≫ (pulledTensorSections k a b).app U) ≫
          μ'.hom.hom.app V := by
      simp only [Category.assoc, ← Category.assoc (f := η.app U), he]
      rfl
    _ = scalarProduct ≫ constantSections W V := by
      rw [hsections, Category.assoc]
      exact hμ' V
    _ = _ := by
      have hc := congrArg (scalarProduct ≫ ·) (comparedUnit_sections k U)
      rw [← hc, ← Category.assoc, ← hZ]
      simp only [Category.assoc]

instance {W Z X Y : TopCat} (k : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) :
    IsIso (pullbackTensorMap k a b) := by
  obtain ⟨μ, hμ⟩ := ConvolutionConstantDescent.tensorMultiplication a b
  obtain ⟨μ', hμ'⟩ := ConvolutionConstantDescent.tensorMultiplication (k ≫ a) (k ≫ b)
  have : IsIso (pullbackTensorMap k a b ≫ μ'.hom) := by
    rw [pullbackTensorMap_multiplication k a b μ μ' hμ hμ']
    infer_instance
  exact IsIso.of_isIso_comp_right _ μ'.hom

end CoefficientDescent
section ShiftedFrameDescent

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

private theorem shiftedConstantPullback_eq {W Z : TopCat} (k : W ⟶ Z) (d : ℕ) :
    shiftedConstantPullback k d =
      (shiftedSinglePullback k d).app (rational Z) ≪≫
        (singleShift W d).mapIso (constantPullback k) := by
  apply Iso.ext
  simp only [shiftedConstantPullback, shiftedSinglePullback,
    Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Functor.map_comp, Functor.comp_map, Category.assoc]

/-- Pull back the shifted tensor via its canonical comparison on sheaves. -/
def shiftedTensorPullback {W Z X Y : TopCat} (k : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) :
    (derivedInverseImage k).obj (shiftedTensor a b) ≅ shiftedTensor (k ≫ a) (k ≫ b) :=
  (shiftedSinglePullback k 2).app (pulledBackTensor a b) ≪≫
    (singleShift W 2).mapIso (asIso (pullbackTensorMap k a b))

private theorem shiftedTensorPullback_multiplication {W Z X Y : TopCat}
    (k : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y)
    (μ : pulledBackTensor a b ≅ rational Z) (μ' : pulledBackTensor (k ≫ a) (k ≫ b) ≅ rational W)
    (hμ : MultipliesCoefficients a b μ) (hμ' : MultipliesCoefficients (k ≫ a) (k ≫ b) μ') :
    shiftedTensorPullback k a b ≪≫ (singleShift W 2).mapIso μ' =
      (derivedInverseImage k).mapIso ((singleShift Z 2).mapIso μ) ≪≫
        shiftedConstantPullback k 2 := by
  have hn := (shiftedSinglePullback k 2).hom.naturality μ.hom
  change (derivedInverseImage k).map ((singleShift Z 2).map μ.hom) ≫
    (shiftedSinglePullback k 2).hom.app (rational Z) =
      (shiftedSinglePullback k 2).hom.app (pulledBackTensor a b) ≫
        (singleShift W 2).map ((inverseImage k).map μ.hom) at hn
  rw [shiftedConstantPullback_eq]
  apply Iso.ext
  simp only [shiftedTensorPullback, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    asIso_hom, Category.assoc]
  rw [← Functor.map_comp, pullbackTensorMap_multiplication k a b μ μ' hμ hμ',
    Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]

/-- On a test space over the frame representatives, pull back the descent comparison
using the tensor pullback, before making any coefficient trivialization. -/
def pullbackDescentIso {W Z X Y : TopCat} (k : W ⟶ Z)
    (a : Z ⟶ X) (b : Z ⟶ Y) (q : Z ⟶ ordered)
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor a b) :
    (derivedInverseImage (k ≫ q)).obj orderedFactor.obj ≅ shiftedTensor (k ≫ a) (k ≫ b) :=
  (derivedInverseImageComposition k q).app orderedFactor.obj ≪≫
    (derivedInverseImage k).mapIso d ≪≫ shiftedTensorPullback k a b

private theorem pullbackDescentIso_multiplication {W Z X Y : TopCat}
    (k : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) (q : Z ⟶ ordered)
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor a b)
    (μ : pulledBackTensor a b ≅ rational Z) (μ' : pulledBackTensor (k ≫ a) (k ≫ b) ≅ rational W)
    (hμ : MultipliesCoefficients a b μ) (hμ' : MultipliesCoefficients (k ≫ a) (k ≫ b) μ')
    (hd : d ≪≫ (singleShift Z 2).mapIso μ = shiftedConstantPullback q 2) :
    pullbackDescentIso k a b q d ≪≫ (singleShift W 2).mapIso μ' =
      shiftedConstantPullback (k ≫ q) 2 := by
  unfold pullbackDescentIso
  simp only [Iso.trans_assoc]
  rw [shiftedTensorPullback_multiplication k a b μ μ' hμ hμ', ← Iso.trans_assoc
    (α := (derivedInverseImage k).mapIso d), ← Functor.mapIso_trans, hd]
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
    ConvolutionConstantDescent.shiftedPullbackComposition k q 2

private theorem shiftedCoefficientTransition_eqToHom {W X : TopCat} {f g : W ⟶ X}
    (h : f = g) (d : ℕ) :
    (shiftedCoefficientTransition f g d).hom =
      eqToHom (congrArg (fun t => (derivedInverseImage t).obj
        (IntersectionComplex.shiftedConstant X d).obj) h) := by
  subst g
  simp [shiftedCoefficientTransition]

private theorem coefficientTransition_eqToHom {W X : TopCat} {f g : W ⟶ X}
    (h : f = g) :
    (coefficientTransition f g).hom = eqToHom
      (congrArg (fun t => (inverseImage t).obj (rational X)) h) := by
  subst g
  simp [coefficientTransition]

private theorem pullbackDescent_transition {W Z X Y : TopCat}
    (k₁ k₀ : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) (q : Z ⟶ ordered)
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor a b)
    (μ : pulledBackTensor a b ≅ rational Z) (hμ : MultipliesCoefficients a b μ)
    (hd : d ≪≫ (singleShift Z 2).mapIso μ = shiftedConstantPullback q 2) :
    (pullbackDescentIso k₁ a b q d).hom ≫
      (shiftedTensorTransition (k₁ ≫ a) (k₀ ≫ a) (k₁ ≫ b) (k₀ ≫ b)).hom =
        (shiftedCoefficientTransition (k₁ ≫ q) (k₀ ≫ q) 2).hom ≫
          (pullbackDescentIso k₀ a b q d).hom := by
  obtain ⟨μ₁, hμ₁⟩ := ConvolutionConstantDescent.tensorMultiplication (k₁ ≫ a) (k₁ ≫ b)
  obtain ⟨μ₀, hμ₀⟩ := ConvolutionConstantDescent.tensorMultiplication (k₀ ≫ a) (k₀ ≫ b)
  let J := singleShift W 2
  apply (cancel_mono (J.map μ₀.hom)).mp
  have h₁ := congrArg Iso.hom (pullbackDescentIso_multiplication k₁ a b q d μ μ₁ hμ hμ₁ hd)
  have h₀ := congrArg Iso.hom (pullbackDescentIso_multiplication k₀ a b q d μ μ₀ hμ hμ₀ hd)
  have hT := congrArg J.map (coefficientTensorIso_multiplication _ _ _ _ μ₁ μ₀ hμ₁ hμ₀)
  change _ ≫ J.map μ₁.hom = _ at h₁
  change _ ≫ J.map μ₀.hom = _ at h₀
  change (_ ≫ J.map _) ≫ J.map μ₀.hom = _
  simp only [Functor.map_comp] at hT
  rw [Category.assoc, hT, h₁, Category.assoc, h₀]
  simp [shiftedCoefficientTransition]

/-- The transport used for a single factor is obtained from its actual
normalized equivariance by pulling back the action and projection. -/
theorem coefficientTransition_from_action {H : AnalyticGroup.{0}} {X W : TopCat}
    (A : AnalyticAction H X) (e : A.Equivariance (IntersectionComplex.shiftedConstant X 1).obj)
    (he : e.iso = shiftedCoefficientTransition A.act (AnalyticAction.projection H X) 1)
    (r : W ⟶ AnalyticAction.Parameters H X) {f g : W ⟶ X}
    (hf : r ≫ A.act = f) (hg : r ≫ AnalyticAction.projection H X = g) :
    pullbackMorphism r hf hg e.iso.hom =
      ((shiftedSinglePullback f 1).app (rational X) ≪≫
        (singleShift W 1).mapIso (coefficientTransition f g) ≪≫
          ((shiftedSinglePullback g 1).app (rational X)).symm).hom := by
  rw [he]
  change pullbackMorphism r hf hg (_ ≪≫ _).hom = _
  rw [pullback_constantTransition]
  simp [shiftedConstantPullback_eq, coefficientTransition]

end ShiftedFrameDescent


open ConvolutionFrameQuotientSpecs (representativeCoordinates)
open scoped Matrix MatrixGroups
open private representative_loop_colength integralRepresentative integralRepresentative_eq
  integralJet_coeff continuous_integralJet continuous_jetMatrix firstLine_jet
  constantMatrix_mul linearMatrix_mul continuous_constantMatrix continuous_linearMatrix
  continuous_jetMatrixVal
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionFrameQuotient
open private positive_fixed colength_smul_of_fixed positive_windowSubspace
  incidenceCoordinates_injective reduce_two_surjective from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle

section FrameActions

private def positiveFrame (g : FrameBasis) : PositiveGL 2 :=
  ⟨positiveGLMap 2 g, g, rfl⟩

private def changeBasisPoint (h : StableStage (PositiveGL 2) (colength 1))
    (z : FrameParameters) : FrameRepresentative :=
  ⟨(z.representative.val.1 * positiveGLMap 2 z.basis,
      positiveGLMap 2 z.basis⁻¹ • z.representative.val.2),
    ⟨_, rfl, by
      rw [mul_smul, ← show (positiveFrame z.basis).val = positiveGLMap 2 z.basis from rfl,
        positive_fixed]
      exact representative_loop_colength z.representative⟩,
    h (positiveFrame z.basis⁻¹) z.representative.property.2⟩

private def leftActionPoint (z : FrameParameters) : FrameRepresentative :=
  ⟨(positiveGLMap 2 z.basis * z.representative.val.1, z.representative.val.2),
    ⟨_, rfl, by
      rw [mul_smul]
      exact (colength_smul_of_fixed _ (positive_fixed (positiveFrame z.basis)) _ 1).mpr
        (representative_loop_colength z.representative)⟩,
    z.representative.property.2⟩

private theorem integralRepresentative_eq_of_map (p : FrameRepresentative)
    (S : Matrix (Fin 2) (Fin 2) O) (hS : S.map inclusion = p.val.1.val) :
    integralRepresentative p = S := by
  apply Matrix.ext
  intro i j
  have he := congrArg (fun M => M i j) ((integralRepresentative_eq p).trans hS.symm)
  exact IsFractionRing.injective O K he

private theorem continuous_mul_jetMatrices {X : Type} [TopologicalSpace X]
    {f g : X → Matrix (Fin 2) (Fin 2) (JetRing 2)} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) := by
  apply continuous_jetMatrix
  · simp only [constantMatrix_mul]
    exact (continuous_constantMatrix.comp hf).matrix_mul (continuous_constantMatrix.comp hg)
  · simp only [linearMatrix_mul]
    exact ((continuous_constantMatrix.comp hf).matrix_mul (continuous_linearMatrix.comp hg)).add
      ((continuous_linearMatrix.comp hf).matrix_mul (continuous_constantMatrix.comp hg))

private theorem continuous_frameCoefficients (f : FrameParameters → FrameRepresentative)
    (hf : Continuous fun z => (integralRepresentative (f z)).map (jetReduction 2).toRingHom) :
    Continuous fun z i j (k : Fin 2) => ((f z).val.1.val i j).coeff (k.val : ℤ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro k
  simp only [← integralJet_coeff]
  exact ((continuous_apply k).comp
    (show Continuous (jetCoefficients 2) from continuous_induced_dom)).comp
      (hf.matrix_elem i j)

private theorem relativeLine_action {hG : IsTopologicalGroup Jets}
    (A : AnalyticAction (jetGroup hG) minuscule)
    (hA : ∀ (g : Jets) (p : ProjectivePoints),
      firstPlane (A.act (g, p)) = (firstPlane p).map (constantJetLinear g))
    (b : representativeSpace ⟶ minuscule)
    (hb : ∀ p : FrameRepresentative, firstPlane (b p) =
      (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap)
    (h : StableStage (PositiveGL 2) (colength 1)) (z : FrameParameters) :
    b (changeBasisPoint h z) = A.act ((frameJet z.basis)⁻¹, b z.representative) := by
  apply grassmannianSubspace_injective projectiveBasis projectiveRank
  change firstPlane (b (changeBasisPoint h z)) =
    firstPlane (A.act ((frameJet z.basis)⁻¹, b z.representative))
  have hact := hA ((frameJet z.basis)⁻¹) (b z.representative)
  refine (hb (changeBasisPoint h z)).trans (?_ : _ = (firstPlane (b z.representative)).map _) |>.trans
    hact.symm
  rw [hb]
  change (latticeSubspace 0 1 (positiveGLMap 2 z.basis⁻¹ • z.representative.val.2)).map
      constantCoordinates.toLinearMap = _
  rw [← map_inv]
  apply firstLine_jet
  exact positive_windowSubspace _ _

def changeFrame (h : StableStage (PositiveGL 2) (colength 1))
    {hG : IsTopologicalGroup Jets} (A : AnalyticAction (jetGroup hG) minuscule)
    (hA : ∀ (g : Jets) (p : ProjectivePoints),
      firstPlane (A.act (g, p)) = (firstPlane p).map (constantJetLinear g))
    (b : representativeSpace ⟶ minuscule)
    (hb : ∀ p : FrameRepresentative, firstPlane (b p) =
      (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap) :
    frameParameters ⟶ representativeSpace := by
  let m := MinusculeAndTwoStep.minusculeProjective.1.choose
  have hm := MinusculeAndTwoStep.minusculeProjective.1.choose_spec.1
  have hmb (p : FrameRepresentative) :
      m (ConvolutionFrameQuotientSpecs.representedSecondStage p) = b p := by
    apply grassmannianSubspace_injective projectiveBasis projectiveRank
    exact (hm _).trans (hb p).symm
  refine TopCat.ofHom ⟨changeBasisPoint h, continuous_induced_rng.mpr
    ((continuous_frameCoefficients _ ?_).prodMk ?_)⟩
  · have eq (z : FrameParameters) :
      integralRepresentative (changeBasisPoint h z) =
        integralRepresentative z.representative * z.basis.val := by
      apply integralRepresentative_eq_of_map
      change inclusion.mapMatrix _ = (z.representative.val.1 * positiveGLMap 2 z.basis).val
      rw [map_mul]
      exact congrArg (fun M => M * (positiveGLMap 2 z.basis).val)
        (integralRepresentative_eq z.representative)
    simp only [eq]
    change Continuous (fun z : FrameParameters =>
      (jetReduction 2).toRingHom.mapMatrix (integralRepresentative z.representative * z.basis.val))
    simp only [map_mul]
    exact continuous_mul_jetMatrices (continuous_integralJet.comp
        (continuous_snd.comp continuous_frameParameters))
      (continuous_jetMatrixVal.comp (continuous_fst.comp continuous_frameParameters))
  · change Continuous (fun z => ConvolutionFrameQuotientSpecs.representedSecondStage
      (changeBasisPoint h z))
    apply m.comp_continuous_iff.mp
    simp only [Function.comp_def, hmb, relativeLine_action A hA b hb]
    exact A.act.hom.continuous.comp (inverseFrameActionParameter hG b).hom.continuous

def leftActFrame : frameParameters ⟶ representativeSpace := by
  refine TopCat.ofHom ⟨leftActionPoint, continuous_induced_rng.mpr
    ((continuous_frameCoefficients _ ?_).prodMk ?_)⟩
  · have eq (z : FrameParameters) :
      integralRepresentative (leftActionPoint z) =
        z.basis.val * integralRepresentative z.representative := by
      apply integralRepresentative_eq_of_map
      change inclusion.mapMatrix _ = (positiveGLMap 2 z.basis * z.representative.val.1).val
      rw [map_mul]
      exact congrArg (fun M => (positiveGLMap 2 z.basis).val * M)
        (integralRepresentative_eq z.representative)
    simp only [eq]
    change Continuous (fun z : FrameParameters =>
      (jetReduction 2).toRingHom.mapMatrix (z.basis.val * integralRepresentative z.representative))
    simp only [map_mul]
    exact continuous_mul_jetMatrices
      (continuous_jetMatrixVal.comp (continuous_fst.comp continuous_frameParameters))
      (continuous_integralJet.comp (continuous_snd.comp continuous_frameParameters))
  · change Continuous (fun z : FrameParameters =>
        ConvolutionFrameQuotientSpecs.representedSecondStage z.representative)
    exact (continuous_snd.comp (show Continuous representativeCoordinates from
      continuous_induced_dom)).comp (continuous_snd.comp continuous_frameParameters)

theorem leftActFrame_apply (z : FrameParameters) :
    (leftActFrame z).val =
      (positiveGLMap 2 z.basis * z.representative.val.1, z.representative.val.2) := rfl

end FrameActions
section FrameDiagrams

open BoundedLatticeSpecs (windowJetLinear)

private theorem frameJet_surjective : Function.Surjective frameJet := reduce_two_surjective

private theorem changeBasis_quotient {h : StableStage (PositiveGL 2) (colength 1)}
    (e : OrderedProduct h ≃ ordered) (q : representativeSpace ⟶ ordered)
    (hq : ∀ p : FrameRepresentative,
      q p = e (Quotient.mk (twistRel (PositiveGL 2) firstStage (colength 1)) p))
    (z : FrameParameters) : q (changeBasisPoint h z) = q z.representative := by
  rw [hq, hq]
  apply congrArg e
  apply Quotient.sound
  refine ⟨(positiveFrame z.basis)⁻¹, ?_, ?_⟩
  · change z.representative.val.1 =
      z.representative.val.1 * positiveGLMap 2 z.basis * (positiveGLMap 2 z.basis)⁻¹
    simp
  · change z.representative.val.2 =
      positiveGLMap 2 z.basis • (positiveGLMap 2 z.basis⁻¹ • z.representative.val.2)
    rw [map_inv, smul_inv_smul]

private theorem basisChange_iff_same_image {h : StableStage (PositiveGL 2) (colength 1)}
    (e : OrderedProduct h ≃ ordered) (q : representativeSpace ⟶ ordered)
    (hq : ∀ p : FrameRepresentative,
      q p = e (Quotient.mk (twistRel (PositiveGL 2) firstStage (colength 1)) p))
    (p p' : FrameRepresentative) :
    q p' = q p ↔ ∃ g : FrameBasis, changeBasisPoint h ⟨g, p⟩ = p' := by
  constructor
  · intro he
    have hx := e.injective ((hq p).symm.trans (he.symm.trans (hq p')))
    obtain ⟨k, hk, hl⟩ := Quotient.exact hx
    obtain ⟨g, hg⟩ := k.property
    refine ⟨g, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change p.val.1 * positiveGLMap 2 g = p'.val.1
      rw [hk, hg]
    · change positiveGLMap 2 g⁻¹ • p.val.2 = p'.val.2
      rw [hl, map_inv]
      exact congrArg (fun x : Loop => x⁻¹ • p.val.2) hg
  · rintro ⟨g, rfl⟩
    exact changeBasis_quotient e q hq ⟨g, p⟩

private theorem leftFrame_second (b : representativeSpace ⟶ minuscule)
    (hb : ∀ p : FrameRepresentative, firstPlane (b p) =
      (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap) :
    leftActFrame ≫ b = frameProjection ≫ b := by
  apply TopCat.ext
  intro z
  apply grassmannianSubspace_injective projectiveBasis projectiveRank
  exact (hb (leftActFrame z)).trans (hb z.representative).symm

private theorem leftFrame_ordered {hG : IsTopologicalGroup Jets}
    (A₁ : AnalyticAction (jetGroup hG) minuscule)
    (A₂ : AnalyticAction (jetGroup hG) ordered)
    (h₁ : ∀ (g : Jets) (p : ProjectivePoints),
      firstPlane (A₁.act (g, p)) = (firstPlane p).map (constantJetLinear g))
    (h₂ : ∀ (g : Jets) (p : ordered),
      firstStageMap (A₂.act (g, p)) = A₁.act (g, firstStageMap p) ∧
      secondPlane (convolutionMap (A₂.act (g, p))) =
        (secondPlane (convolutionMap p)).map (twoTermJetLinear g))
    (q : representativeSpace ⟶ ordered)
    (hq : ∀ p : FrameRepresentative,
      firstPlane (firstStageMap (q p)) =
        (latticeSubspace 0 1 (p.val.1 • standardLattice 2)).map constantCoordinates.toLinearMap ∧
      secondPlane (convolutionMap (q p)) =
        (latticeSubspace 0 2 (p.val.1 • p.val.2)).map twoStepCoordinates.toLinearMap) :
    leftActFrame ≫ q = frameActionParameter q ≫ A₂.act := by
  apply TopCat.ext
  intro z
  let g := frameJet z.basis
  let p := z.representative
  have haction := h₂ g (q p)
  have hfirst := (hq (leftActFrame z)).1
  have hsecond := (hq (leftActFrame z)).2
  change firstPlane (firstStageMap (q (leftActFrame z))) =
      (latticeSubspace 0 1 ((positiveGLMap 2 z.basis * p.val.1) • standardLattice 2)).map
        constantCoordinates.toLinearMap at hfirst
  change secondPlane (convolutionMap (q (leftActFrame z))) =
      (latticeSubspace 0 2 ((positiveGLMap 2 z.basis * p.val.1) • p.val.2)).map
        twoStepCoordinates.toLinearMap at hsecond
  apply incidenceCoordinates_injective
  apply Prod.ext
  · apply grassmannianSubspace_injective projectiveBasis projectiveRank
    change firstPlane (firstStageMap (q (leftActFrame z))) =
      firstPlane (firstStageMap (A₂.act (g, q p)))
    refine hfirst.trans (?_ : _ = (firstPlane (firstStageMap (q p))).map (constantJetLinear g))
      |>.trans ((congrArg firstPlane haction.1).trans (h₁ g _)).symm
    rw [mul_smul, (hq p).1]
    exact firstLine_jet g _ _ (positive_windowSubspace _ _)
  · apply grassmannianSubspace_injective twoStepBasis twoStepRank
    change secondPlane (convolutionMap (q (leftActFrame z))) =
      secondPlane (convolutionMap (A₂.act (g, q p)))
    refine hsecond.trans (?_ : _ = (secondPlane (convolutionMap (q p))).map (twoTermJetLinear g))
      |>.trans haction.2.symm
    rw [mul_smul, (hq p).2, positive_windowSubspace]
    simp only [← Submodule.map_comp, twoTermJetLinear, LinearMap.comp_assoc,
      LinearEquiv.symm_comp, LinearMap.comp_id, g, frameJet]

end FrameDiagrams

section EquivariantDescent

open AnalyticAction (projection)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
theorem equivariantTwistedExteriorDescent :
    ConvolutionUnitConeSpecs.Expected.EquivariantTwistedExteriorDescent := by
  obtain ⟨h, e, b, q, hq, coords⟩ := ConvolutionFrameQuotient.frameQuotient
  obtain ⟨hG, M₁, M₂, hc₁, hc₂, h₁, h₂⟩ := ConvolutionFrameQuotient.jetActions
  let A₁ : AnalyticAction (jetGroup hG) minuscule :=
    { act := TopCat.ofHom ⟨fun p => M₁.smul p.1 p.2, hc₁⟩
      one_act := M₁.one_smul
      mul_act := M₁.mul_smul }
  let A₂ : AnalyticAction (jetGroup hG) ordered :=
    { act := TopCat.ofHom ⟨fun p => M₂.smul p.1 p.2, hc₂⟩
      one_act := M₂.one_smul
      mul_act := M₂.mul_smul }
  obtain ⟨E₁, n₁⟩ := ConvolutionConstantDescent.normalizedEquivariance A₁ 1
  obtain ⟨E₂, n₂⟩ := ConvolutionConstantDescent.normalizedEquivariance A₂ 2
  let a := q ≫ firstStageMap
  obtain ⟨μ, d, hμ, hd, _⟩ := ConvolutionConstantDescent.shiftedDescent a b q
  let right := changeFrame h A₁ h₁ b (fun p => (coords p).2.2.1)
  have hr : right ≫ q = frameProjection ≫ q :=
    TopCat.ext (changeBasis_quotient e q fun p => (coords p).1)
  have hr₂ : inverseFrameActionParameter hG b ≫ A₁.act = right ≫ b :=
    TopCat.ext fun z => (relativeLine_action A₁ h₁ b (fun p => (coords p).2.2.1) h z).symm
  have hl₂ : leftActFrame ≫ b = frameProjection ≫ b :=
    leftFrame_second b (fun p => (coords p).2.2.1)
  have hl : frameActionParameter q ≫ A₂.act = leftActFrame ≫ q :=
    (leftFrame_ordered A₁ A₂ h₁ h₂ q (fun p => ⟨(coords p).2.1, (coords p).2.2.2⟩)).symm
  have hl₁ : frameActionParameter a ≫ A₁.act = leftActFrame ≫ a := by
    apply TopCat.ext
    intro z
    have hp := congrArg (fun f : frameParameters ⟶ ordered => firstStageMap (f z)) hl
    exact (h₂ (frameJet z.basis) (q z.representative)).1.symm.trans hp
  refine ⟨h, e, b, q, hq, coords, μ, d, hμ, hd, hG, A₁, A₂, h₁, h₂, E₁, E₂,
    right, leftActFrame, n₁, n₂, ?_⟩
  refine {
    basis_change := fun _ => ⟨rfl, rfl⟩
    left_multiplication := leftActFrame_apply
    covers_overlaps := basisChange_iff_same_image e q (fun p => (coords p).1)
    covers_jet_parameters := ?_
    right_quotient := hr
    right_second := hr₂
    left_first := hl₁
    left_second := hl₂
    left_quotient := hl
    right_first_coefficients := coefficientTransition_eqToHom (congrArg (· ≫ firstStageMap) hr)
    right_second_coefficients := coefficientTransition_from_action A₁ E₁ n₁ _ hr₂ rfl
    left_first_coefficients := coefficientTransition_from_action A₁ E₁ n₁ _ hl₁ rfl
    left_second_coefficients := coefficientTransition_eqToHom hl₂
    tensor_pullback_isIso := fun _ _ => inferInstance
    on_overlaps := ?_
    intertwines_ordered_action := ?_ }
  · intro x
    obtain ⟨g, hg⟩ := frameJet_surjective x.1
    obtain ⟨p, hp⟩ := hq.surjective x.2
    exact ⟨⟨g, p⟩, Prod.ext hg hp⟩
  · dsimp only
    intro W k₁ k₀ he
    rw [← shiftedCoefficientTransition_eqToHom he 2]
    exact pullbackDescent_transition k₁ k₀ a b q d μ hμ hd
  · have hE : pullbackMorphism (frameActionParameter q) hl rfl E₂.iso.hom =
        (shiftedCoefficientTransition (leftActFrame ≫ q) (frameProjection ≫ q) 2).hom := by
      rw [n₂, pullback_constantTransition]
      rfl
    rw [hE]
    exact pullbackDescent_transition leftActFrame frameProjection a b q d μ hμ hd

private theorem EquivariantTwistedExteriorDescent.toTwistedExteriorDescent
    (h : ConvolutionUnitConeSpecs.Expected.EquivariantTwistedExteriorDescent) :
    TwistedExteriorDescent := by
  obtain ⟨h, e, b, q, hq, coords, μ, d, hμ, hd, hG, A₁, A₂, h₁, h₂, E₁, E₂, _, _, n₁, n₂, _⟩ := h
  refine ⟨h, e, b, q, hq, coords, ⟨μ, d, hμ, hd, ?_⟩, hG, A₁, A₂, h₁, h₂, ⟨E₁, n₁⟩, ⟨E₂, n₂⟩⟩
  intro W k
  have eq := congrArg Iso.hom hd
  change d.hom ≫ ((singleShift representativeSpace 2).mapIso μ).hom =
    (shiftedConstantPullback q 2).hom at eq
  change (derivedInverseImageComposition k q).hom.app orderedFactor.obj ≫
    (derivedInverseImage k).map (d.hom ≫ ((singleShift representativeSpace 2).mapIso μ).hom) ≫
      (shiftedConstantPullback k 2).hom = (shiftedConstantPullback (k ≫ q) 2).hom
  rw [eq]
  exact ConvolutionConstantDescent.shiftedPullbackComposition k q 2

end EquivariantDescent

end TwistedDescent

section Assembly

open ConvolutionSurfaceSpecs

private theorem map_unit_isIso {C : Type*} [Category* C] (F : Derived surface ⥤ C)
    (h : IsIso (F.map (derivedConstantUnit convolutionMap (-2)))) : IsIso (F.map unit) := by
  let I := DerivedCategory.Plus.ι (C := Sheaves surface)
  let a := (coefficientShiftIso surface 2).symm
  let b := (derivedDirectImage convolutionMap).mapIso (coefficientShiftIso ordered 2)
  let := h
  change IsIso (F.map (I.map a.hom ≫ derivedConstantUnit convolutionMap (-2) ≫ I.map b.hom))
  simp only [Functor.map_comp]
  infer_instance

private theorem openUnit_at (x : surface) (hx : IsClosed ({x} : Set surface))
    (hscalar : ScalarTerminalPoint x) : OpenUnit x hx := by
  obtain ⟨e, he, _⟩ := ConvolutionAnalyticCharts.openOrbitHomeomorphism x hscalar
  let U := complementOpen {x} hx
  let f := ConvolutionUnitLocalitySpecs.restrictToOpen convolutionMap U
  have heq : (f : _ → _) = e := funext fun y => Subtype.ext (he y).symm
  have hf : IsHomeomorph f := by rw [heq]; exact e.isHomeomorph
  exact map_unit_isIso _
    (ConvolutionUnitLocality.openUnit convolutionMap (-2) (constantPullback convolutionMap) U hf)

private theorem scalarPoint_mem_range {x : surface} (h : RadialFibreComparison x) :
    x ∈ Set.range convolutionMap := by
  obtain ⟨_, s, _, _, hs, _⟩ := h
  let p := projectiveLineHomeomorph (Classical.choice
    (inferInstanceAs (Nonempty (P202.ComplexProjective.Space 1))))
  exact ⟨p ≫ s, section_terminal x s hs p⟩

private theorem stalkUnit_at (x : surface) (h : RadialFibreComparison x)
    (hline : Nonempty ((stalkCohomology x (-2)).obj convolution.obj ≅ scalars)) :
    IsIso ((stalkCohomology x (-2)).map unit) := by
  obtain ⟨line⟩ := hline
  let F := stalkCohomology x (-2)
  let e := (DerivedCategory.Plus.ι (C := Sheaves surface)).mapIso
    ((derivedDirectImage convolutionMap).mapIso (coefficientShiftIso ordered 2))
  exact map_unit_isIso F (ConvolutionUnitLocality.stalkUnit convolutionMap (-2)
    (constantPullback convolutionMap) x (scalarPoint_mem_range h) ⟨F.mapIso e ≪≫ line⟩)

/-- The normalized minuscule convolution and the skyscraper cone of its unit. -/
theorem convolutionUnitCone : ConvolutionUnitConeSpecs.Expected.ConvolutionUnitCone := by
  obtain ⟨hsc, hlc, ht, hB⟩ := ConvolutionAnalyticCharts.orderedTopology
  let : SecondCountableTopology ordered := hsc
  let : LocallyCompactSpace ordered := hlc
  let : T2Space ordered := ht
  obtain ⟨x, hscalar, hRadial⟩ :=
    radialFibreComparison_of_orderedTopology TransverseCone.transverseCone hB
  have hx := surface_isClosed_singleton x
  have hu := openUnit_at x hx hscalar
  obtain ⟨hline, hzero⟩ := shiftedImageStalkDegrees x hRadial hB
  have hs : StalkProfile x := ⟨hline, hzero, stalkUnit_at x hRadial (hline (-2) (Or.inl rfl))⟩
  exact ⟨EquivariantTwistedExteriorDescent.toTwistedExteriorDescent equivariantTwistedExteriorDescent, projectiveLineModel, x, hx, hscalar, hRadial, hu, hs,
    coneProfile_of_openUnit x hx hu hs⟩

end Assembly

end RepTheorySurvey.Geometric.ConvolutionUnitCone
