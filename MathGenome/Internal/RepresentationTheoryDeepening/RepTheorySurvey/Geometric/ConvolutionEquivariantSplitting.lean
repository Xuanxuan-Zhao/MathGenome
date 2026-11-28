import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionEquivariantSplitting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionProjectionBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionActionComparisons
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionPointCoefficients
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionSplitting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepLocalCohomology
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Topology
open scoped Matrix.Norms.Elementwise

namespace RepTheorySurvey.Geometric.ConvolutionEquivariantSplitting

open Analytic LocalSheaf LatticeModelSpecs BoundedLatticeSpecs ConvolutionBundleSpecs
open ConvolutionEquivariantSplittingSpecs ConvolutionActionComparisonsSpecs
open ConvolutionPointCoefficientsSpecs (productPoint productPoint_closed)
open scoped MatrixGroups

private theorem unitsGroupOfFiniteCoordinates {A E : Type}
    [Ring A] [Algebra ℂ A] [TopologicalSpace A] [TopologicalSpace Aˣ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (e : A ≃ₗ[ℂ] E) (he : IsInducing e)
    (hv : IsInducing (Units.val : Aˣ → A)) :
    IsTopologicalGroup Aˣ := by
  classical
  let : FiniteDimensional ℂ A := FiniteDimensional.of_injective e.toLinearMap e.injective
  let b := Module.finBasis ℂ A
  let M := Matrix (Fin (Module.finrank ℂ A)) (Fin (Module.finrank ℂ A)) ℂ
  let f : A →ₐ[ℂ] M := (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul ℂ A)
  let p : M →ₗ[ℂ] E :=
    e.toLinearMap.comp ((LinearMap.applyₗ (R := ℂ) (1 : A)).comp
      (LinearMap.toMatrixAlgEquiv b).symm.toLinearMap)
  have hp (a : A) : p (f a) = e a := by
    change e ((LinearMap.toMatrixAlgEquiv b).symm
      ((LinearMap.toMatrixAlgEquiv b) (Algebra.lmul ℂ A a)) 1) = e a
    rw [AlgEquiv.symm_apply_apply]
    change e (a * 1) = e a
    rw [mul_one]
  have hf : Continuous f := by
    let f' := f.toLinearMap.comp e.symm.toLinearMap
    exact (f'.continuous_of_finiteDimensional.comp he.continuous).congr
      (fun a => by change f (e.symm (e a)) = f a; rw [LinearEquiv.symm_apply_apply])
  let F : Aˣ →* Mˣ := Units.map f.toMonoidHom
  have hF : Continuous (fun u : Aˣ => (F u).val) := hf.comp hv.continuous
  have recover : ∀ {Y : Type} [TopologicalSpace Y] (g : Y → Aˣ),
      Continuous (fun y => (F (g y)).val) → Continuous g := by
    intro Y _ g hg
    apply (he.comp hv).continuous_iff.mpr
    exact (p.continuous_of_finiteDimensional.comp hg).congr
      (fun y => hp (g y).val)
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply recover (fun v : Aˣ × Aˣ => v.1 * v.2)
    refine ((hF.comp continuous_fst).matrix_mul (hF.comp continuous_snd)).congr ?_
    intro z
    exact congrArg (Units.val : Mˣ → M) (F.map_mul z.1 z.2).symm
  · apply recover (fun v : Aˣ => v⁻¹)
    have hinv : Continuous (fun u : Aˣ => ((F u).val : M)⁻¹) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      have hdet : ((F u).val : M).det ≠ 0 :=
        (Matrix.isUnits_det_units (F u)).ne_zero
      have hscalar : ContinuousAt (Ring.inverse : ℂ → ℂ) ((F u).val : M).det := by
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ hdet
      exact (continuousAt_matrix_inv ((F u).val : M) hscalar).comp
        (f := fun w : Aˣ => (F w).val) (x := u) hF.continuousAt
    refine hinv.congr (fun u => ?_)
    rw [F.map_inv, Matrix.coe_units_inv]

private abbrev JetMatrix (n : ℕ) := Matrix (Fin 2) (Fin 2) (JetRing n)
private abbrev MatrixCoordinates (n : ℕ) := Fin 2 → Fin 2 → Fin n → ℂ

private def matrixCoefficients (n : ℕ) : JetMatrix n ≃ₗ[ℂ] MatrixCoordinates n :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.piCongrRight fun _ => jetCoefficients n

private theorem isInducing_matrixCoefficients (n : ℕ) :
    IsInducing (matrixCoefficients n) :=
  (show IsInducing (jetCoefficients n) from ⟨rfl⟩).matrix_map

private theorem jetIsTopologicalGroup (n : ℕ) (hn : 1 ≤ n) :
    @IsTopologicalGroup (GLJets 2 n hn) (glJetTopology 2 n hn) inferInstance := by
  let : TopologicalSpace (GLJets 2 n hn) := glJetTopology 2 n hn
  apply unitsGroupOfFiniteCoordinates (matrixCoefficients n) (isInducing_matrixCoefficients _)
  exact ⟨rfl⟩

private abbrev jetUnitsTopology (n : ℕ) : TopologicalSpace (JetMatrix n)ˣ :=
  Units.instTopologicalSpaceUnits

/-- In coefficient coordinates the inversion map is continuous, so adjoining
the inverse as a second coordinate gives the same topology on units. -/
private theorem jetUnitsTopology_eq (n : ℕ) (hn : 1 ≤ n) :
    jetUnitsTopology n = glJetTopology 2 n hn := by
  let T := glJetTopology 2 n hn
  have hval : @Continuous (GLJets 2 n hn) (JetMatrix n) T _ Units.val :=
    continuous_induced_dom
  have hinv : @Continuous (GLJets 2 n hn) (GLJets 2 n hn) T T (fun g => g⁻¹) :=
    @continuous_inv _ _ _ (jetIsTopologicalGroup n hn).toContinuousInv
  apply le_antisymm
  · change jetUnitsTopology n ≤ TopologicalSpace.induced (Units.val : (JetMatrix n)ˣ → JetMatrix n) _
    exact continuous_iff_le_induced.mp
      (show @Continuous (JetMatrix n)ˣ (JetMatrix n) (jetUnitsTopology n) _ Units.val from
        Units.continuous_val)
  · have h : @Continuous (GLJets 2 n hn) (GLJets 2 n hn) T (jetUnitsTopology n) id :=
      Units.continuous_iff.mpr ⟨hval, hval.comp hinv⟩
    exact (continuous_iff_le_induced.mp h).trans_eq (@induced_id _ (jetUnitsTopology n))

private theorem higherIsTopologicalGroup {n : ℕ} (hn : 2 ≤ n) :
    IsTopologicalGroup (higherJet hn) :=
  jetIsTopologicalGroup n ((by decide : 1 ≤ 2).trans hn)

private theorem truncateJet_reduction {m n : ℕ} (h : m ≤ n) (a : O) :
    truncateJet h (jetReduction n a) = jetReduction m a := rfl

private theorem continuous_truncateJet {m n : ℕ} (h : m ≤ n) :
    Continuous (truncateJet h) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  let j : Fin n := Fin.castLE h i
  have heq (a : JetRing n) : jetCoefficients m (truncateJet h a) i = jetCoefficients n a j := by
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  change Continuous (fun a => jetCoefficients m (truncateJet h a) i)
  simp only [heq]
  exact (continuous_apply j).comp continuous_induced_dom

private theorem truncateToTwo_continuous {n : ℕ} (hn : 2 ≤ n) :
    Continuous (truncateToTwo hn) := by
  apply continuous_induced_rng.mpr
  exact (show @Continuous (higherJet hn) (JetMatrix n)
    (glJetTopology 2 n ((by decide : 1 ≤ 2).trans hn)) _ Units.val from
    continuous_induced_dom).matrix_map (continuous_truncateJet hn)

theorem truncateToTwo_reduceGL {n : ℕ} (hn : 2 ≤ n) (g : Positive) :
    truncateToTwo hn (reduceGL 2 n ((by decide : 1 ≤ 2).trans hn) g) =
      reduceGL 2 2 (by decide) g :=
  Units.ext (Matrix.ext fun i j => truncateJet_reduction hn (g.val i j))


open MinusculeAndTwoStepSpecs ConvolutionSurfaceSpecs ConvolutionUnitConeSpecs
open NilpotentConeChartSpecs
open Analytic.AnalyticAction (Parameters projection)

section IncidenceGeometry

local instance : TopologicalSpace Jets := glJetTopology 2 2 (by decide)

open private jetStableAct jetStableAct_continuous jetGrassmannianAct_subspace
  windowJetLinear_one windowJetLinear_mul
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
open private secondPlane_injective incidencePoints_ext
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionSurface
open private firstLine_jet termLinear termLinear_apply
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionFrameQuotient

private abbrev shortPlane (p : ShortStablePoints) : Submodule ℂ (Window 2 0 2) :=
  grassmannianSubspace (windowBasis 2 0 2) (windowDimension_le shortDimension) p.val

private abbrev shortJet (g : Jets) (p : ShortStablePoints) : ShortStablePoints :=
  jetStableAct 0 (by decide) (le_refl 2) shortDimension g p

private theorem shortJet_plane (g : Jets) (p : ShortStablePoints) :
    shortPlane (shortJet g p) = (shortPlane p).map (windowJetLinear 0 (le_refl 2) g.val) :=
  jetGrassmannianAct_subspace 0 (by decide) (le_refl 2) shortDimension g p.val

private theorem shortPlane_injective : Function.Injective shortPlane :=
  fun _ _ h => Subtype.ext
    (grassmannianSubspace_injective (windowBasis 2 0 2) (windowDimension_le shortDimension) h)

private theorem shortJet_one (p : ShortStablePoints) : shortJet 1 p = p := by
  apply shortPlane_injective
  rw [shortJet_plane]
  change (shortPlane p).map (windowJetLinear 0 (le_refl 2) 1) = shortPlane p
  rw [windowJetLinear_one, Submodule.map_id]

private theorem shortJet_mul (g h : Jets) (p : ShortStablePoints) :
    shortJet (g * h) p = shortJet g (shortJet h p) := by
  apply shortPlane_injective
  simp only [shortJet_plane, Units.val_mul, windowJetLinear_mul, Submodule.map_comp]

private theorem shortJet_continuous : Continuous
    (fun z : Jets × ShortStablePoints => shortJet z.1 z.2) :=
  jetStableAct_continuous 0 (by decide) (le_refl 2) shortDimension

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
private def terminalActionMap (e : surface ≃ₜ ShortStablePoints) :
    TopCat.of (Jets × surface) ⟶ surface := by
  let p : Jets × surface → Jets × ShortStablePoints := fun z => (z.1, e z.2)
  have hp : Continuous p := continuous_fst.prodMk (e.continuous.comp continuous_snd)
  let act : Jets × surface → surface := e.symm ∘ (fun z => shortJet z.1 z.2) ∘ p
  have hc : Continuous act := (e.symm.continuous.comp shortJet_continuous).comp hp
  exact TopCat.ofHom ⟨act, hc⟩

private theorem terminalActionMap_one (e : surface ≃ₜ ShortStablePoints) (p : surface) :
    terminalActionMap e (1, p) = p := by
  change e.symm (shortJet 1 (e p)) = p
  rw [shortJet_one, e.symm_apply_apply]

private theorem terminalActionMap_mul (e : surface ≃ₜ ShortStablePoints) (g h : Jets) (p : surface) :
    terminalActionMap e (g * h, p) = terminalActionMap e (g, terminalActionMap e (h, p)) := by
  change e.symm (shortJet (g * h) (e p)) =
    e.symm (shortJet g (e (e.symm (shortJet h (e p)))))
  rw [shortJet_mul, e.apply_symm_apply]

private def terminalAction (h : IsTopologicalGroup Jets) (e : surface ≃ₜ ShortStablePoints) :
    AnalyticAction (jetGroup h) surface where
  act := terminalActionMap e
  one_act := terminalActionMap_one e
  mul_act := terminalActionMap_mul e

private theorem terminalAction_plane (h : IsTopologicalGroup Jets) (e : surface ≃ₜ ShortStablePoints)
    (he : ∀ p : surface, (shortPlane (e p)).map twoStepCoordinates.toLinearMap = secondPlane p)
    (g : Jets) (p : surface) :
    secondPlane ((terminalAction h e).act (g, p)) = (secondPlane p).map (twoTermJetLinear g) := by
  change secondPlane (e.symm (shortJet g (e p))) = _
  rw [← he (e.symm _), e.apply_symm_apply, shortJet_plane, ← he p]
  simp only [twoTermJetLinear, ← Submodule.map_comp, LinearMap.comp_assoc,
    LinearEquiv.symm_comp, LinearMap.comp_id]

private theorem orderedPoints_ext {p q : ordered}
    (h₁ : firstPlane (firstStageMap p) = firstPlane (firstStageMap q))
    (h₂ : secondPlane (convolutionMap p) = secondPlane (convolutionMap q)) : p = q :=
  incidencePoints_ext
    (grassmannianSubspace_injective projectiveBasis projectiveRank h₁)
    (secondPlane_injective h₂)

private theorem scalarPlane_map_le (g : Jets) :
    ((⊥ : Submodule ℂ V).prod ⊤).map (twoTermJetLinear g) ≤ (⊥ : Submodule ℂ V).prod ⊤ := by
  rintro _ ⟨⟨a, b⟩, hab, rfl⟩
  have ha : a = 0 := by simpa using hab.1
  subst a
  change termLinear g.val (0, b) ∈ (⊥ : Submodule ℂ V).prod ⊤
  rw [termLinear_apply, Matrix.mulVec_zero]
  exact ⟨Submodule.zero_mem _, Submodule.mem_top⟩

private theorem fixesScalarPoint {h : IsTopologicalGroup Jets}
    {A : AnalyticAction (jetGroup h) surface}
    (hA : ∀ (g : Jets) (p : surface),
      secondPlane (A.act (g, p)) = (secondPlane p).map (twoTermJetLinear g))
    {x : surface} (hx : ScalarTerminalPoint x) (g : Jets) :
    A.act (g, x) = x := by
  apply secondPlane_injective
  apply Submodule.eq_of_le_of_finrank_le
  · rw [hA, hx.2.2]
    exact scalarPlane_map_le g
  · have rank (p : surface) : Module.finrank ℂ (secondPlane p) = 2 :=
      grassmannianSubspace_finrank twoStepBasis twoStepRank (p ≫ twoStepSchemeInGrassmannian)
    exact (rank x).le.trans (rank (A.act (g, x))).ge

private theorem terminalAction_commutes {h : IsTopologicalGroup Jets}
    {A : AnalyticAction (jetGroup h) surface} {B : AnalyticAction (jetGroup h) ordered}
    (hA : ∀ (g : Jets) (p : surface),
      secondPlane (A.act (g, p)) = (secondPlane p).map (twoTermJetLinear g))
    (hB : ∀ (g : Jets) (p : ordered),
      secondPlane (convolutionMap (B.act (g, p))) =
        (secondPlane (convolutionMap p)).map (twoTermJetLinear g)) :
    Commutes A B :=
  fun g p => secondPlane_injective ((hB g p).trans (hA g _).symm)

/-- The incidence action obtained from two jets agrees with the positive-loop
action on the ordered pair of lattices. -/
theorem orderedAction_on_lattices {h : IsTopologicalGroup Jets}
    {B : AnalyticAction (jetGroup h) ordered}
    (hB₁ : ∀ (g : Jets) (p : ordered),
      firstPlane (firstStageMap (B.act (g, p))) =
        (firstPlane (firstStageMap p)).map (constantJetLinear g))
    (hB₂ : ∀ (g : Jets) (p : ordered),
      secondPlane (convolutionMap (B.act (g, p))) =
        (secondPlane (convolutionMap p)).map (twoTermJetLinear g)) :
    ∃ i : Flags ≃ ordered,
      (∀ L : Flags, firstPlane (firstStageMap (i L)) =
        (latticeSubspace 0 1 L.val.1).map constantCoordinates.toLinearMap ∧
        secondPlane (convolutionMap (i L)) =
        (latticeSubspace 0 2 L.val.2).map twoStepCoordinates.toLinearMap) ∧
      ∀ (g : Positive) (L : Flags), (i.symm (B.act (reduceGL 2 2 (by decide) g, i L))).val =
        (positiveGLMap 2 g • L.val.1, positiveGLMap 2 g • L.val.2) := by
  obtain ⟨i, hi⟩ := ConvolutionBundle.latticeIncidence.2.2
  obtain ⟨σ, hσ, hp⟩ := ConvolutionBundle.flagJetAction
  refine ⟨i, hi, fun g L => ?_⟩
  let j := reduceGL 2 2 (by decide) g
  have hi₁ (L : Flags) : firstPlane (firstStageMap (i L)) =
      (latticeSubspace 0 1 L.val.1).map constantCoordinates.toLinearMap := (hi L).1
  have hi₂ (L : Flags) : secondPlane (convolutionMap (i L)) =
      (latticeSubspace 0 2 L.val.2).map twoStepCoordinates.toLinearMap := (hi L).2
  have heq : B.act (j, i L) = i (σ.smul j L) := by
    apply orderedPoints_ext
    · rw [hB₁, hi₁ L, hi₁ (σ.smul j L)]
      exact (firstLine_jet j _ _ (hσ j L).1).symm
    · rw [hB₂, hi₂ L, hi₂ (σ.smul j L), (hσ j L).2]
      simp only [twoTermJetLinear, ← Submodule.map_comp, LinearMap.comp_assoc,
        LinearEquiv.symm_comp, LinearMap.comp_id]
  change (i.symm (B.act (j, i L))).val = _
  rw [heq, i.symm_apply_apply]
  exact hp g L

end IncidenceGeometry


open CategoryTheory.Pretriangulated Opposite TopologicalSpace
open ConvolutionSplittingSpecs
open Analytic.IntersectionComplex (shiftedConstant)
open private plusIsGE_iff from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
open private cohomologyOfShiftedPlus from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepIntersectionComplex

/-- A right derived functor computed by bounded-below injective resolutions
preserves lower cohomology bounds. -/
theorem rightDerivedFunctorPlus_isGE {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] (T : C ⥤ D) [T.Additive]
    (F : DerivedCategory.Plus C) (n : ℤ) [F.IsGE n] :
    (T.rightDerivedFunctorPlus.obj F).IsGE n := by
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso F n
  let K := (T.mapCochainComplexPlus.obj (injectiveComplex I)).obj
  have hK : K.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff] at hI ⊢
    intro q hq
    exact T.map_isZero ((InjectiveObject.ι C).map_isZero (hI q hq))
  let a := T.rightDerivedFunctorPlusUnit.app (injectiveComplex I)
  have : IsIso a := inferInstanceAs (IsIso
    (T.rightDerivedFunctorPlusUnit.app (injectiveComplex I)))
  let b : DerivedCategory.Q.obj K ≅ (T.rightDerivedFunctorPlus.obj F).obj :=
    DerivedCategory.Plus.ι.mapIso (asIso a ≪≫ T.rightDerivedFunctorPlus.mapIso e)
  apply (DerivedCategory.Plus.isGE_ι_obj_iff _ _).mp
  have hK' : (DerivedCategory.Q.obj K).IsGE n := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  exact DerivedCategory.TStructure.t.isGE_of_iso b n

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing on a cofinal family of neighborhoods gives vanishing of the
stalk even without chosen identifications of the neighbourhood cohomology. -/
theorem isZero_stalkColimit_of_cofinal {X : TopCat} (P : X.Presheaf Coeff.{0}) (x : X)
    (h : ∀ U : OpenNhds x, ∃ V : OpenNhds x, V ≤ U ∧ IsZero (P.obj (op V.1))) :
    IsZero (stalkColimit P x) := by
  let Q := (OpenNhds.inclusion x).op ⋙ P
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro U
  obtain ⟨V, hVU, hz⟩ := h U.unop
  let j : U ⟶ op V := (homOfLE hVU).op
  have hι : colimit.ι Q U = Q.map j ≫ colimit.ι Q (op V) := (colimit.w Q j).symm
  have hmap := hz.eq_of_tgt (Q.map j) 0
  have hleg : colimit.ι Q U = 0 := hι.trans (show
      Q.map j ≫ colimit.ι Q (op V) = (0 : Q.obj U ⟶ colimit Q) from by rw [hmap, zero_comp])
  change colimit.ι Q U ≫ 𝟙 _ = colimit.ι Q U ≫ (0 : colimit Q ⟶ colimit Q)
  rw [Category.comp_id, comp_zero, hleg]

/-- Vanishing of supported neighborhood cohomology gives the unshifted
extraordinary restriction bound along the entire closed subspace. -/
theorem isZero_costalkCohomology_of_cofinal {X : TopCat.{0}} {Z : Set X}
    (hZ : IsClosed Z) (F : BoundedBelow X) (q : ℤ)
    (h : ∀ z : Z, ∀ U : OpenNhds z.val, ∃ V : OpenNhds z.val, V ≤ U ∧
      IsZero ((derivedOpenCohomology
        (extraordinaryInverseImage hZ ⋙ directImage (closedInclusion Z)) F q).obj (op V.1))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedExtraordinaryInverseImage hZ).obj F)) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro z
  obtain ⟨e⟩ := DerivedLocalSheaves.costalk hZ z q F
  exact (isZero_stalkColimit_of_cofinal _ _ (h z)).of_iso e

local instance {X Y : TopCat.{0}} (p : X ⟶ Y) :
    (derivedInverseImage p).CommShift ℤ := by
  unfold derivedInverseImage
  infer_instance

local instance {X Y : TopCat.{0}} (p : X ⟶ Y) :
    (derivedInverseImage p).IsTriangulated := by
  unfold derivedInverseImage
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- An ordinary section remains the unique section after pullback whenever
the Hom group into the pulled-back first vertex vanishes. -/
theorem pullbackSection_unique {X : TopCat} (p : X ⟶ surface)
    {x : surface} {hx : IsClosed ({x} : Set surface)}
    (e : unitCone ≅ pointSkyscraper x hx) (s : pointSkyscraper x hx ⟶ convolution.obj)
    (hs : s ≫ quotientMap e = 𝟙 _)
    (h : Subsingleton ((derivedInverseImage p).obj (pointSkyscraper x hx) ⟶
      (derivedInverseImage p).obj unitTriangle.obj₁))
    (s' : (derivedInverseImage p).obj (pointSkyscraper x hx) ⟶
      (derivedInverseImage p).obj convolution.obj)
    (hs' : s' ≫ (derivedInverseImage p).map (quotientMap e) = 𝟙 _) :
    s' = (derivedInverseImage p).map s := by
  let L := derivedInverseImage p
  let T := (derivedInverseImage p).mapTriangle.obj unitTriangle
  have hT : T ∈ distTriang (Derived X) := (derivedInverseImage p).map_distinguished _
    ConvolutionUnitCone.unitTriangle_distinguished
  have hss : L.map s ≫ L.map (quotientMap e) = 𝟙 _ := by rw [← L.map_comp, hs, L.map_id]
  have hzero : (s' - L.map s) ≫ T.mor₂ = 0 := by
    change (s' - L.map s) ≫ L.map unitTriangle.mor₂ = 0
    apply (cancel_mono (L.map e.hom)).mp
    rw [Category.assoc, zero_comp]
    change (s' - L.map s) ≫ (L.map unitTriangle.mor₂ ≫ L.map e.hom) = 0
    rw [← L.map_comp, Preadditive.sub_comp, hs', hss, sub_self]
  obtain ⟨r, hr⟩ := T.coyoneda_exact₂ hT (s' - L.map s) hzero
  rw [h.elim r 0, zero_comp] at hr
  exact sub_eq_zero.mp hr

open TwoStepLocalCohomologySpecs
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open Analytic.SingularCochains (Values)
open private jetGroupHomeomorph jetMatrixHomeomorph jetUnitOpen_isOpen normedOpenBasis
  comparisonTopology_of_openEmbedding comparisonTopology_prod jetChartTopology supportedComparison
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepLocalCohomology

private abbrev JetsUnitsSpace : TopCat :=
  @TopCat.of Jets Units.instTopologicalSpaceUnits

private theorem jetGroup_comparisonTopology : ComparisonTopology JetsUnitsSpace := by
  let E := Fin 2 → Fin 2 → Fin 2 → ℂ
  have hE : ComparisonTopology (TopCat.of E) :=
    ⟨inferInstance, inferInstance, inferInstance, normedOpenBasis E⟩
  exact comparisonTopology_of_openEmbedding
    (jetMatrixHomeomorph.isOpenEmbedding.comp
      (jetUnitOpen_isOpen.isOpenEmbedding_subtypeVal.comp jetGroupHomeomorph.isOpenEmbedding)) hE

private abbrev FullJetChart := JetChart (⊤ : Opens JetGroup)

private def radialProductOpen (c : RadialChart) (D : Opens JetGroup) (r : PositiveRadius) :
    Opens FullJetChart :=
  ⟨{p | p.1.val ∈ D ∧ p.2 ∈ c.balls.obj r},
    (D.isOpen.preimage (continuous_subtype_val.comp continuous_fst)).inter
      ((c.balls.obj r).isOpen.preimage continuous_snd)⟩

private abbrev fullProductSupport (c : RadialChart) :=
  jetSupportClosed c (⊤ : Opens JetGroup)

private def radialProductPairIso (c : RadialChart) (D : Opens JetGroup) (r : PositiveRadius) :
    (openPairs (fullProductSupport c)).obj (radialProductOpen c D r) ≅ jetPair c D r := by
  let P := (openPairs (fullProductSupport c)).obj (radialProductOpen c D r)
  let Q := jetPair c D r
  let u (z : P.space) : Q.space :=
    ⟨(⟨z.val.1.val, z.property.1⟩, z.val.2), z.property.2⟩
  let v (z : Q.space) : P.space :=
    ⟨(⟨z.val.1.val, Set.mem_univ _⟩, z.val.2), z.val.1.property, z.property⟩
  have hu : Continuous u := by
    have h₁ : Continuous (fun z : P.space => (⟨z.val.1.val, z.property.1⟩ : D)) :=
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _
    exact (h₁.prodMk (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  have hv : Continuous v := by
    have h₁ : Continuous (fun z : Q.space =>
        (⟨z.val.1.val, Set.mem_univ _⟩ : (⊤ : Opens JetsUnitsSpace))) :=
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _
    exact (h₁.prodMk (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  refine ⟨⟨TopCat.ofHom ⟨u, hu⟩, fun z hz => ?_⟩,
    ⟨TopCat.ofHom ⟨v, hv⟩, fun z hz => ?_⟩, ?_, ?_⟩
  · exact ⟨(u z).property, hz.2⟩
  · exact ⟨(v z).property, hz.2⟩
  · apply PairMap.ext
    exact TopCat.ext fun _ => rfl
  · apply PairMap.ext
    exact TopCat.ext fun _ => rfl

private theorem radialProductOpen_cofinal (c : RadialChart)
    (hc : (nhds c.vertex).HasBasis (fun _ : PositiveRadius => True)
      (fun r => (c.balls.obj r : Set ChartSpace)))
    (z : FullJetChart) (hz : z.2 = c.vertex) (U : OpenNhds z) :
    ∃ (D : Opens JetGroup) (r : PositiveRadius), ContractibleSpace D ∧
      z ∈ radialProductOpen c D r ∧ radialProductOpen c D r ≤ U.1 := by
  obtain ⟨S,T,hS,hzS,hT,hzT,hST⟩ :=
    mem_nhds_prod_iff'.mp (U.1.isOpen.mem_nhds U.2)
  let V : Opens JetsUnitsSpace :=
    ⟨Subtype.val '' S, isOpen_univ.isOpenMap_subtype_val S hS⟩
  obtain ⟨D, hD, hDV, hcontract⟩ := jetGroup_comparisonTopology.2.2.2 z.1.val V
    ⟨z.1, hzS, rfl⟩
  have hvertex : c.vertex ∈ T := hz ▸ hzT
  obtain ⟨r, _, hr⟩ := hc.mem_iff.mp (hT.mem_nhds hvertex)
  have hrv : c.vertex ∈ c.balls.obj r := mem_of_mem_nhds (hc.mem_of_mem (i := r) trivial)
  have hzV : z.2 ∈ c.balls.obj r := hz.symm ▸ hrv
  refine ⟨D, r, hcontract, ⟨hD, hzV⟩, fun w hw => ?_⟩
  apply hST
  obtain ⟨g, hg, heq⟩ := hDV hw.1
  exact ⟨(Subtype.ext heq : g = w.1) ▸ hg, hr hw.2⟩

set_option maxHeartbeats 450000 in
set_option backward.isDefEq.respectTransparency false in
private theorem chartProductCostalk (c : RadialChart)
    (hc : (nhds c.vertex).HasBasis (fun _ : PositiveRadius => True)
      (fun r => (c.balls.obj r : Set ChartSpace))) (q : ℤ) (hq : q ≠ 4) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedExtraordinaryInverseImage (fullProductSupport c)).obj
        (sheafInDegreeZero (rational FullJetChart)))) := by
  apply isZero_costalkCohomology_of_cofinal
  intro z U
  obtain ⟨D, r, hD, hz, hU⟩ := radialProductOpen_cofinal c hc z.val z.property U
  let V : OpenNhds z.val := ⟨radialProductOpen c D r, hz⟩
  refine ⟨V, hU, ?_⟩
  obtain ⟨_, h⟩ := (TwoStepLocalCohomology.jetProductCohomology c D hD).2 q
  obtain ⟨value⟩ := (h r).2
  have hzq : IsZero (cohomologyValue {4} q) := by
    simpa [cohomologyValue, hq] using (isZero_zero (Coeff.{0}))
  obtain ⟨iso⟩ := supportedComparison FullJetChart
    (jetChartTopology c ⊤ NilpotentConeChart.radialNeighborhoods) (fullProductSupport c) q
  exact hzq.of_iso ((iso.app (op V.1)).symm ≪≫
    (relativeCohomologyFunctor ℚ Values.{0} q).mapIso (radialProductPairIso c D r).symm.op ≪≫ value)


open private colengthHomeomorphShort from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
open private surfaceComparison from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionSplitting
open private rationalRestrictionZero from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepIntersectionComplex
open private closedShriekOpenIso embeddingIsoOfRange embeddingIsoOfRange_comp pullbackStalkIso
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private abbrev relativeCostalk (H : AnalyticGroup.{0}) {x : surface}
    (hx : IsClosed ({x} : Set surface)) :=
  (derivedExtraordinaryInverseImage (productPoint_closed H hx)).obj
    (sheafInDegreeZero (rational (Parameters H surface)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
theorem relativeCostalk_cohomology_zero (hH : IsTopologicalGroup Jets) (x : surface)
    (hx : IsClosed ({x} : Set surface)) (hscalar : ScalarTerminalPoint x)
    (q : ℤ) (hq : q ≠ 4) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      (relativeCostalk (jetGroup hH) hx)) := by
  obtain ⟨h, E, hE⟩ := surfaceComparison x hscalar
  obtain ⟨c, hc, _⟩ := TwoStepLocalCohomology.radialNeighborhoodBasis
  let L := (colengthHomeomorphShort 2).symm
  let f : ChartSpace → surface := fun y => E.symm (L y.val)
  have hf : IsOpenEmbedding f :=
    E.symm.isOpenEmbedding.comp
      (L.isOpenEmbedding.comp c.isOpen.isOpenEmbedding_subtypeVal)
  have hvertex : f c.vertex = x := by
    apply E.injective
    change E (E.symm (L c.vertex.val)) = E x
    rw [E.apply_symm_apply, hE]
    exact Subtype.ext c.vertex_eq
  let H := jetGroup hH
  let X := Parameters H surface
  let Z : Set X := productPoint H x
  let Z' : Set FullJetChart := Prod.snd ⁻¹' ({c.vertex} : Set ChartSpace)
  let g : (⊤ : Opens JetsUnitsSpace) → H.space := Subtype.val
  have hg : IsOpenEmbedding g := by
    change @IsOpenEmbedding (⊤ : Opens JetGroup) Jets _ (glJetTopology 2 2 (by decide)) g
    rw [← jetUnitsTopology_eq 2 (by decide)]
    exact (⊤ : Opens JetsUnitsSpace).isOpen.isOpenEmbedding_subtypeVal
  let k : FullJetChart ⟶ X := TopCat.ofHom
    ⟨fun y => (g y.1, f y.2), (hg.continuous.comp continuous_fst).prodMk
      (hf.continuous.comp continuous_snd)⟩
  have hk : IsOpenEmbedding k := hg.prodMap hf
  let i := closedInclusion (X := X) Z
  let j := closedInclusion (X := FullJetChart) Z'
  have hj : IsEmbedding (j ≫ k) := hk.isEmbedding.comp IsEmbedding.subtypeVal
  have hRange : Set.range i = Set.range (j ≫ k) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨⟨(⟨z.val.1, Set.mem_univ _⟩, c.vertex), rfl⟩, ?_⟩
      change (z.val.1, f c.vertex) = z.val
      exact Prod.ext rfl (hvertex.trans z.property.symm)
    · rintro ⟨v, rfl⟩
      have hv : v.val.2 = c.vertex := v.property
      exact ⟨⟨(j ≫ k) v, (congrArg f hv).trans hvertex⟩, rfl⟩
  let T := embeddingIsoOfRange i (j ≫ k) IsEmbedding.subtypeVal hj hRange
  let F := sheafInDegreeZero (rational X)
  let S := derivedExtraordinaryInverseImage (fullProductSupport c)
  let G := S.obj ((boundedBelowInverseImage k).obj F)
  let D := closedShriekOpenIso (productPoint_closed H hx) (fullProductSupport c)
    k hk T (embeddingIsoOfRange_comp i (j ≫ k) IsEmbedding.subtypeVal hj hRange) F
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro z
  let coho := DerivedCategory.Plus.homologyFunctor (Sheaves (TopCat.of Z)) q
  let z' := T.hom z
  let coho' := DerivedCategory.Plus.homologyFunctor (Sheaves (TopCat.of Z')) q
  have e := (coho ⋙ stalk z).mapIso D ≪≫ pullbackStalkIso T.hom G q z ≪≫
    (coho' ⋙ stalk z').mapIso (S.mapIso (rationalRestrictionZero k))
  exact ((stalk z').map_isZero (chartProductCostalk c hc q hq)).of_iso e

theorem relativeCostalk_global_isGE (hH : IsTopologicalGroup Jets) (x : surface)
    (hx : IsClosed ({x} : Set surface)) (hscalar : ScalarTerminalPoint x) :
    ((globalSections (TopCat.of (productPoint (jetGroup hH) x))).rightDerivedFunctorPlus.obj
      (relativeCostalk (jetGroup hH) hx)).IsGE 4 := by
  have : (relativeCostalk (jetGroup hH) hx).IsGE 4 :=
    (plusIsGE_iff _ _).mpr fun q hq =>
      relativeCostalk_cohomology_zero hH x hx hscalar q (ne_of_lt hq)
  exact rightDerivedFunctorPlus_isGE _ _ _


private def closedExtensionSingleIso {X : TopCat.{0}} {Z : Set X}
    (hZ : IsClosed Z) (F : Sheaves (TopCat.of Z)) :
    (closedExtensionPlus hZ).obj (sheafInDegreeZero F) ≅
      sheafInDegreeZero ((directImage (closedInclusion Z)).obj F) := by
  let _ := (extraordinaryAdjunction hZ).isLeftAdjoint
  apply DerivedCategory.Plus.ι.preimageIso
  exact ((directImage (closedInclusion Z)).mapDerivedCategorySingleFunctor 0).app F

/-- Pulling back a closed extension of a single sheaf is again a closed
extension of a single sheaf, along the inverse image of its support. -/
theorem exists_closedExtensionInverseImage {X Y : TopCat.{0}} (p : Y ⟶ X) {Z : Set X}
    (hZ : IsClosed Z) (F : Sheaves (TopCat.of Z)) :
    ∃ G : Sheaves (TopCat.of (p ⁻¹' Z)),
      Nonempty ((boundedBelowInverseImage p).obj ((closedExtensionPlus hZ).obj (sheafInDegreeZero F)) ≅
        (closedExtensionPlus (hZ.preimage p.hom.continuous)).obj (sheafInDegreeZero G)) := by
  let W := p ⁻¹' Z
  let hW : IsClosed W := hZ.preimage p.hom.continuous
  let i := closedInclusion Z
  let j := closedInclusion W
  let V := (directImage i).obj F
  let S := (inverseImage p).obj V
  have supp : SupportedOn W S := fun y hy =>
    (closedDirectImage_supported hZ F (p y) hy).of_iso ((inverseImageStalkIso p V y).symm)
  obtain ⟨G, ⟨g⟩⟩ := (DerivedLocalSheaves.supportedEssentialImage hW S).mpr supp
  let e : (boundedBelowInverseImage p).obj (sheafInDegreeZero V) ≅ sheafInDegreeZero S :=
    DerivedCategory.Plus.ι.preimageIso
      (((inverseImage p).mapDerivedCategorySingleFunctor 0).app V)
  exact ⟨G, ⟨(boundedBelowInverseImage p).mapIso (closedExtensionSingleIso hZ F) ≪≫ e ≪≫
    (DerivedCategory.Plus.singleFunctor (Sheaves Y) 0).mapIso g.symm ≪≫
    (closedExtensionSingleIso hW G).symm⟩⟩

private def closedShriekShiftedConstantIso {X : TopCat.{0}} {Z : Set X}
    (hZ : IsClosed Z) (d : ℕ) :
    (derivedExtraordinaryInverseImage hZ).obj (shiftedConstant X d) ≅
      ((derivedExtraordinaryInverseImage hZ).obj
        (sheafInDegreeZero (rational X)))⟦(d : ℤ)⟧ := by
  let F := sheafInDegreeZero (rational X)
  let I := DerivedCategory.Plus.ι (C := Sheaves X)
  let e : shiftedConstant X d ≅ F⟦(d : ℤ)⟧ :=
    I.preimageIso ((I.commShiftIso (d : ℤ)).app F).symm
  letI : (derivedExtraordinaryInverseImage hZ).CommShift ℤ := by
    unfold derivedExtraordinaryInverseImage
    infer_instance
  exact (derivedExtraordinaryInverseImage hZ).mapIso e ≪≫
    ((derivedExtraordinaryInverseImage hZ).commShiftIso (d : ℤ)).app F

set_option backward.isDefEq.respectTransparency false in
theorem relativeCostalk_Hom_subsingleton (hH : IsTopologicalGroup Jets) (x : surface)
    (hx : IsClosed ({x} : Set surface)) (hscalar : ScalarTerminalPoint x)
    (d : ℕ) (hd : d < 4) :
    Subsingleton (((derivedInverseImage (projection (jetGroup hH) surface)).obj
      (pointSkyscraper x hx)) ⟶ (shiftedConstant (Parameters (jetGroup hH) surface) d).obj) := by
  let H := jetGroup hH
  let X := Parameters H surface
  let p := projection H surface
  let Z : Set X := p ⁻¹' ({x} : Set surface)
  let hZ : IsClosed Z := hx.preimage p.hom.continuous
  let R := derivedExtraordinaryInverseImage (X := X) (Z := Z) hZ
  let L := closedExtensionPlus (X := X) (Z := Z) hZ
  let a := DerivedLocalSheaves.derivedExtraordinaryAdjunctionData (X := X) (Z := Z) hZ
  let W := TopCat.of ({x} : Set surface)
  let F := shiftedConstant X d
  have hR : (R.obj F).IsGE 1 := (plusIsGE_iff _ _).mpr fun q hq => by
    let G := relativeCostalk H hx
    have e : (DerivedCategory.Plus.homologyFunctor _ q).obj (R.obj F) ≅
        (DerivedCategory.Plus.homologyFunctor _ (q + (d : ℤ))).obj G :=
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso (closedShriekShiftedConstantIso hZ d) ≪≫
        cohomologyOfShiftedPlus G q (d : ℤ)
    exact (relativeCostalk_cohomology_zero hH x hx hscalar _ (by omega)).of_iso e
  obtain ⟨G, ⟨e⟩⟩ := exists_closedExtensionInverseImage p hx (rational W)
  let K : BoundedBelow (TopCat.of Z) := sheafInDegreeZero G
  have hK : K.IsLE 0 := by
    change ((DerivedCategory.Plus.singleFunctor (Sheaves (TopCat.of Z)) 0).obj G).IsLE (0 : ℤ)
    infer_instance
  have : L.Additive := by
    unfold L closedExtensionPlus exactDerivedPlus
    infer_instance
  have allZero (v : (derivedInverseImage p).obj (pointSkyscraper x hx) ⟶ F.obj) : v = 0 := by
    let v' : L.obj K ⟶ F := ObjectProperty.homMk (e.inv.hom ≫ v)
    have hv : v' = 0 := by
      apply (a.homEquiv K F).injective
      rw [a.homAddEquiv_zero]
      exact DerivedCategory.Plus.TStructure.t.zero_of_isLE_of_isGE _ 0 1 (by decide) hK hR
    have hv' : e.inv.hom ≫ v = 0 := congrArg (fun k : L.obj K ⟶ F => k.hom) hv
    apply (cancel_epi e.inv.hom).mp
    rw [hv', comp_zero]
  exact ⟨fun v w => (allZero v).trans (allZero w).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Any isomorphism of the two pulled-back quotients preserves the pulled-back
section when the first-vertex Hom group vanishes. -/
theorem section_intertwines_of_quotient {X : TopCat.{0}} (p a : X ⟶ surface)
    {x : surface} {hx : IsClosed ({x} : Set surface)}
    (e : unitCone ≅ pointSkyscraper x hx) (s : pointSkyscraper x hx ⟶ convolution.obj)
    (hs : s ≫ quotientMap e = 𝟙 _)
    (h : Subsingleton ((derivedInverseImage p).obj (pointSkyscraper x hx) ⟶
      (derivedInverseImage p).obj unitTriangle.obj₁))
    (m : (derivedInverseImage a).obj convolution.obj ≅ (derivedInverseImage p).obj convolution.obj)
    (k : (derivedInverseImage a).obj (pointSkyscraper x hx) ≅
      (derivedInverseImage p).obj (pointSkyscraper x hx))
    (comm : (derivedInverseImage a).map (quotientMap e) ≫ k.hom =
      m.hom ≫ (derivedInverseImage p).map (quotientMap e)) :
    (derivedInverseImage a).map s ≫ m.hom = k.hom ≫ (derivedInverseImage p).map s := by
  let L := derivedInverseImage a
  let R := derivedInverseImage p
  have hq : L.map (quotientMap e) ≫ k.hom = m.hom ≫ R.map (quotientMap e) := comm
  have hc : (k.inv ≫ L.map s ≫ m.hom) ≫ R.map (quotientMap e) = 𝟙 _ := by
    calc
      _ = k.inv ≫ L.map s ≫ (m.hom ≫ R.map (quotientMap e)) := by simp only [Category.assoc]
      _ = k.inv ≫ L.map (s ≫ quotientMap e) ≫ k.hom := by
        simp only [← hq, L.map_comp s (quotientMap e), Category.assoc]
      _ = 𝟙 _ := by rw [hs, L.map_id, Category.id_comp, Iso.inv_hom_id]
  have hu := pullbackSection_unique p e s hs h _ hc
  rw [← hu, Iso.hom_inv_id_assoc]

private theorem pullback_intertwining {W Y X : TopCat.{0}} (k : W ⟶ Y)
    {f g : Y ⟶ X} {f' g' : W ⟶ X} (hf : k ≫ f = f') (hg : k ≫ g = g')
    {F G : Derived X} (v : F ⟶ G)
    (α : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F)
    (β : (derivedInverseImage f).obj G ⟶ (derivedInverseImage g).obj G)
    (h : (derivedInverseImage f).map v ≫ β = α ≫ (derivedInverseImage g).map v) :
    (derivedInverseImage f').map v ≫ pullbackMorphism k hf hg β =
      pullbackMorphism k hf hg α ≫ (derivedInverseImage g').map v := by
  subst f' g'
  let K := derivedInverseImage k
  let c := derivedInverseImageComposition k f
  let d := derivedInverseImageComposition k g
  have hc : (derivedInverseImage (k ≫ f)).map v ≫ c.hom.app G =
      c.hom.app F ≫ K.map ((derivedInverseImage f).map v) := c.hom.naturality v
  have hd : K.map ((derivedInverseImage g).map v) ≫ d.inv.app G =
      d.inv.app F ≫ (derivedInverseImage (k ≫ g)).map v := d.inv.naturality v
  simp only [pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (derivedInverseImage (k ≫ f)).map v ≫ (c.hom.app G ≫ K.map β ≫ d.inv.app G) =
    (c.hom.app F ≫ K.map α ≫ d.inv.app F) ≫ (derivedInverseImage (k ≫ g)).map v
  calc
    _ = c.hom.app F ≫ K.map ((derivedInverseImage f).map v ≫ β) ≫ d.inv.app G := by
      simp only [Functor.map_comp, Category.assoc, reassoc_of% hc]
    _ = c.hom.app F ≫ K.map (α ≫ (derivedInverseImage g).map v) ≫ d.inv.app G := by rw [h]
    _ = _ := by simp only [Functor.map_comp, Category.assoc, hd]

private theorem pullback_normalized_of_splitEpi {W Y X : TopCat.{0}} (k : W ⟶ Y)
    {f g : Y ⟶ X} {p : W ⟶ X} (hf : k ≫ f = p) (hg : k ≫ g = p)
    {F G : Derived X} (v : F ⟶ G) [IsSplitEpi v]
    (α : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F)
    (β : (derivedInverseImage f).obj G ⟶ (derivedInverseImage g).obj G)
    (h : (derivedInverseImage f).map v ≫ β = α ≫ (derivedInverseImage g).map v)
    (hn : pullbackMorphism k hf hg α = 𝟙 _) :
    pullbackMorphism k hf hg β = 𝟙 _ := by
  have e := pullback_intertwining k hf hg v α β h
  apply (cancel_epi ((derivedInverseImage p).map v)).mp
  rw [hn, Category.id_comp] at e
  exact e.trans (Category.comp_id _).symm

open AnalyticAction (identitySection identity_act identity_projection)
open ConvolutionPointCoefficientsSpecs (TrivialPointEquivariance)

set_option backward.isDefEq.respectTransparency false in
/-- Identity normalization on the second vertex forces the cone comparison
to be the identity at the group unit. Connectedness then identifies the
comparison with the trivial one on the closed point. -/
private theorem quotient_intertwines
    {hH : IsTopologicalGroup Jets} {A : AnalyticAction (jetGroup hH) surface}
    {x : surface} {hx : IsClosed ({x} : Set surface)}
    (hscalar : ScalarTerminalPoint x) (fixes : ∀ g : Jets, A.act (g, x) = x)
    {Q : A.Equivariance (shiftedConstant surface 2).obj}
    {M : A.Equivariance convolution.obj}
    {P : A.Equivariance (pointSkyscraper x hx)}
    (hu : Intertwines Q M unit) (hP : TrivialPointEquivariance fixes P)
    (c : unitCone ≅ pointSkyscraper x hx) (hδ : unitTriangle.mor₃ = 0) :
    Intertwines M P (quotientMap c) := by
  let H := jetGroup hH
  let p := projection H surface
  let L := derivedInverseImage A.act
  let R := derivedInverseImage p
  let T := L.mapTriangle.obj unitTriangle
  let U := R.mapTriangle.obj unitTriangle
  have hT : T ∈ distTriang (Derived (Parameters H surface)) :=
    L.map_distinguished _ ConvolutionUnitCone.unitTriangle_distinguished
  have hU : U ∈ distTriang (Derived (Parameters H surface)) :=
    R.map_distinguished _ ConvolutionUnitCone.unitTriangle_distinguished
  let f := completeDistinguishedTriangleMorphism T U hT hU Q.iso.hom M.iso.hom hu
  have hf : IsIso f.hom₃ := isIso₃_of_isIso₁₂ f hT hU
    (show IsIso Q.iso.hom from inferInstance) (show IsIso M.iso.hom from inferInstance)
  let e : L.obj unitCone ≅ R.obj unitCone := asIso f.hom₃
  have hq : L.map unitTriangle.mor₂ ≫ e.hom = M.iso.hom ≫ R.map unitTriangle.mor₂ :=
    f.comm₂
  have : Epi unitTriangle.mor₂ :=
    unitTriangle.epi₂ ConvolutionUnitCone.unitTriangle_distinguished hδ
  have : IsSplitEpi unitTriangle.mor₂ := isSplitEpi_of_epi _
  have he : pullbackMorphism (identitySection H surface) (identity_act A)
      identity_projection e.hom = 𝟙 _ :=
    pullback_normalized_of_splitEpi (identitySection H surface) (identity_act A)
      identity_projection unitTriangle.mor₂ M.iso.hom e.hom hq M.identity
  have htriv := ConvolutionPointCoefficients.normalizedConeComparison hH hscalar fixes hP c e he
  have hP' : P.iso.hom = L.map c.inv ≫ e.hom ≫ R.map c.hom := by
    simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Category.assoc] using (congrArg Iso.hom htriv).symm
  change L.map (unitTriangle.mor₂ ≫ c.hom) ≫ P.iso.hom =
    M.iso.hom ≫ R.map (unitTriangle.mor₂ ≫ c.hom)
  calc
    _ = L.map unitTriangle.mor₂ ≫ e.hom ≫ R.map c.hom := by
      simp only [hP', L.map_comp, Category.assoc, ← L.map_comp_assoc c.hom c.inv,
        c.hom_inv_id, L.map_id, Category.id_comp]
    _ = _ := by rw [reassoc_of% hq, R.map_comp]

private theorem projectionMate_isIso {T : TopCat.{0}} (hT : ComparisonTopology T)
    (a : DerivedAdjunction (productMap T)) (b : DerivedAdjunction convolutionMap) :
    IsIso (projectionMate T a b) := by
  let := hT.1
  let := hT.2.1
  let := hT.2.2.1
  exact ConvolutionProjectionBaseChange.projectionBaseChange T hT.2.2.2 a b

private theorem productHomVanishing (hH : IsTopologicalGroup Jets) (x : surface)
    (hx : IsClosed ({x} : Set surface)) (hscalar : ScalarTerminalPoint x) :
    ProductHomVanishing (jetGroup hH) hx := by
  intro d hd
  let p := projection (jetGroup hH) surface
  let e := shiftedConstantPullback p d
  have h := relativeCostalk_Hom_subsingleton hH x hx hscalar d (by omega)
  exact ⟨fun u v => (cancel_mono e.hom).mp (h.elim (u ≫ e.hom) (v ≫ e.hom))⟩

open private restrictEquivariance from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionActionComparisons

private theorem restrictEquivariance_hom {K H : AnalyticGroup.{0}} {Z : TopCat.{0}}
    (φ : K.space →* H.space) (hc : Continuous φ) (A : AnalyticAction H Z)
    {F : Derived Z} (E : A.Equivariance F) :
    (restrictEquivariance φ hc A E).iso.hom =
      pullbackMorphism (parameterMap φ hc Z) rfl (TopCat.ext (fun _ => rfl)) E.iso.hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem higherEquivariance {H : AnalyticGroup.{0}} {Z : TopCat.{0}}
    {A : AnalyticAction H Z} {F : Derived Z} (E : A.Equivariance F)
    (φ : ∀ {n : ℕ} (hn : 2 ≤ n), higherJet hn →* H.space)
    (hc : ∀ {n : ℕ} (hn : 2 ≤ n), Continuous (φ hn)) :
    PullsBackToHigherJets E φ := by
  intro n hn
  let h : IsTopologicalGroup (higherJet hn) := higherIsTopologicalGroup (n := n) hn
  let K := higherGroup (hn := hn) h
  let φn : K.space →* H.space := φ hn
  let hcn : Continuous φn := hc hn
  refine ⟨h, hc hn, restrictEquivariance (K := K) (H := H) φn hcn A E, ?_⟩
  exact (restrictEquivariance_hom (K := K) (H := H) φn hcn A E).symm

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedConvolutionEquivariance {hH : IsTopologicalGroup Jets}
    {A : AnalyticAction (jetGroup hH) surface} {B : AnalyticAction (jetGroup hH) ordered}
    (comm : Commutes A B) (Q : A.Equivariance (shiftedConstant surface 2).obj)
    (hQ : Q.iso = shiftedConstantPullback A.act 2 ≪≫
      (shiftedConstantPullback (projection (jetGroup hH) surface) 2).symm) :
    ∃ M : A.Equivariance convolution.obj,
      UsesConvolutionMates comm M ∧ Intertwines Q M unit := by
  let H := jetGroup hH
  let a := DerivedLocalSheaves.derivedInverseDirectAdjunctionData (productMap H.space)
  let b := DerivedLocalSheaves.derivedInverseDirectAdjunctionData convolutionMap
  let a₂ := DerivedLocalSheaves.derivedInverseDirectAdjunctionData
    (productMap (TopCat.of (H.space × H.space)))
  have hHtop : ComparisonTopology H.space := by
    change ComparisonTopology (@TopCat.of Jets (glJetTopology 2 2 (by decide)))
    rw [← jetUnitsTopology_eq 2 (by decide)]
    exact jetGroup_comparisonTopology
  have hproj := projectionMate_isIso hHtop a b
  have hproj₂ := projectionMate_isIso (comparisonTopology_prod hHtop hHtop) a₂ b
  have ha := ConvolutionActionComparisons.derivedAdjunction_normalized (productMap H.space)
  have hb := ConvolutionActionComparisons.derivedAdjunction_normalized convolutionMap
  have ha₂ := ConvolutionActionComparisons.derivedAdjunction_normalized
    (productMap (TopCat.of (H.space × H.space)))
  obtain ⟨_, hact, M, hm, _, hu, _⟩ :=
    ConvolutionActionComparisons.actionTransport comm a b a₂ ha hb ha₂ hproj hproj₂
  refine ⟨M, ⟨a, b, ha, hb, hproj, hact, hm⟩, ?_⟩
  exact hu.trans (congrArg
    (fun i => i.hom ≫ (derivedInverseImage (projection H surface)).map unit) hQ.symm)

open private surfaceShortModel from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitCone

set_option backward.isDefEq.respectTransparency false in
/-- The canonical finite-jet comparisons preserve the unit and the unique
section of its skyscraper quotient. -/
theorem convolutionEquivariantSplitting : Expected.ConvolutionEquivariantSplitting := by
  obtain ⟨x, hx, hscalar, ⟨c⟩, _, _, hδ, hsplits, hpQ, hpP, hpM⟩ :=
    ConvolutionSplitting.convolutionSplitting
  obtain ⟨s, hs, huniq, split, hsplitQ, hsplitP⟩ := hsplits c
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hH, A₁, B, h₁, hB, E₁, E₂, _, _, n₁, n₂, _⟩ :=
    ConvolutionUnitCone.equivariantTwistedExteriorDescent
  obtain ⟨e, he⟩ := surfaceShortModel
  let H := jetGroup hH
  let A := terminalAction hH e
  have hA := terminalAction_plane hH e he
  have comm := terminalAction_commutes hA (fun g p => (hB g p).2)
  have fixes := fixesScalarPoint hA hscalar
  obtain ⟨Q, hQ⟩ := ConvolutionConstantDescent.normalizedEquivariance A 2
  obtain ⟨M, hM, hunit⟩ := normalizedConvolutionEquivariance comm Q hQ
  obtain ⟨P, hP⟩ := ConvolutionPointCoefficients.trivialPointCoefficients A hx fixes
  have hquot := quotient_intertwines hscalar fixes hunit hP c hδ
  have hHom := productHomVanishing hH x hx hscalar
  have hsection : Intertwines P M s :=
    section_intertwines_of_quotient (projection H surface) A.act c s hs
      (hHom 2 (Or.inl rfl)) M.iso P.iso hquot
  let φ : ∀ {n : ℕ} (hn : 2 ≤ n), higherJet hn →* H.space := truncateToTwo
  let hc : ∀ {n : ℕ} (hn : 2 ≤ n), Continuous (φ hn) := truncateToTwo_continuous
  exact ⟨{
    topologicalGroup := hH
    firstAction := A₁
    orderedAction := B
    terminalAction := A
    first_action := h₁
    firstStage_equivariant := fun g p => (hB g p).1
    terminal_action := hA
    commutes := comm
    point := x
    closed := hx
    scalar := hscalar
    fixes := fixes
    firstEq := E₁
    orderedEq := E₂
    constantEq := Q
    pointEq := P
    convolutionEq := M
    first_normalized := n₁
    ordered_normalized := n₂
    constant_normalized := hQ
    point_normalized := hP
    convolution_normalized := hM
    unit_equivariant := hunit
    coneIso := c
    quotient_equivariant := hquot
    sectionMap := s
    section_identity := hs
    section_unique := huniq
    section_equivariant := hsection
    splitIso := split
    split_constant := hsplitQ
    split_point := hsplitP
    constant_perverse := hpQ
    point_perverse := hpP
    convolution_perverse := hpM
    product_costalk := relativeCostalk_cohomology_zero hH x hx hscalar
    product_hom_vanishing := hHom
    higher_first := higherEquivariance (H := H) E₁ φ hc
    higher_ordered := higherEquivariance (H := H) E₂ φ hc
    higher_constant := higherEquivariance (H := H) Q φ hc
    higher_point := higherEquivariance (H := H) P φ hc
    higher_convolution := higherEquivariance (H := H) M φ hc
  }⟩

end RepTheorySurvey.Geometric.ConvolutionEquivariantSplitting
