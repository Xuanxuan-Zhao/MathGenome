import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MinusculeFrameDescent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitCone
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionFrameQuotient
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Topology
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.MinusculeFrameDescent

open Analytic
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs
open ConvolutionUnitConeSpecs MinusculeFrameDescentSpecs
open ConvolutionBundleSpecs (firstPlane secondPlane firstStage OrderedProduct)
open ConvolutionEquivariantSplittingSpecs (SplittingData)

section FrameActions

private theorem frameChange
    {h : StableStage (PositiveGL 2) (colength 1)}
    (e : OrderedProduct h ≃ ordered) (q : representativeSpace ⟶ ordered)
    (hq : ∀ p : FrameRepresentative,
      q p = e (Quotient.mk (twistRel (PositiveGL 2) firstStage (colength 1)) p))
    (w : overlap q) :
    ∃ g : GL (Fin 2) O,
      (rightLeg q w).val.1 = (leftLeg q w).val.1 * positiveGLMap 2 g ∧
      (rightLeg q w).val.2 = positiveGLMap 2 g⁻¹ • (leftLeg q w).val.2 := by
  have hw : q (leftLeg q w) = q (rightLeg q w) := w.property
  rw [hq, hq] at hw
  obtain ⟨⟨g, g', rfl⟩, hg, hL⟩ := Quotient.exact (e.injective hw)
  exact ⟨g', hg, by simpa using hL⟩

open AnalyticAction
private def productMap (T : TopCat.{0}) {Y X : TopCat.{0}} (f : Y ⟶ X) :
    TopCat.of (T × Y) ⟶ TopCat.of (T × X) :=
  TopCat.ofHom ⟨fun w ↦ (w.1, f w.2),
    continuous_fst.prodMk (f.hom.continuous.comp continuous_snd)⟩
open ConvolutionFrameQuotientSpecs (representativeCoordinates representedSecondStage)

open private representative_loop_colength integralRepresentative integralRepresentative_eq
  integralJet_coeff continuous_integralJet continuous_jetMatrixVal
  firstLine_jet continuous_jetMatrix constantMatrix linearMatrix constantMatrix_mul linearMatrix_mul
  continuous_constantMatrix continuous_linearMatrix from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionFrameQuotient
open private colength_positive from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
open private latticeSubspace_positive inclusion_injective from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
open private incidencePoints_ext secondPlane_injective from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionSurface

private theorem frameLeftAction (d : SplittingData) :
    let H := jetGroup d.topologicalGroup
    ∃ r₁ : Parameters H representativeSpace ⟶ representativeSpace,
      ∀ w, ∃ g : GL (Fin 2) O,
        reduceGL 2 2 (by decide) g = w.1 ∧
        (r₁ w).val.1 = positiveGLMap 2 g * w.2.val.1 ∧
        (r₁ w).val.2 = w.2.val.2 := by
  classical
  let H := jetGroup d.topologicalGroup
  choose lift hlift using RankTwoSchubertStrata.reduceGL_surjective 2 2 (by decide)
  let r₁ (w : Parameters H representativeSpace) : FrameRepresentative :=
    ⟨(positiveGLMap 2 (lift w.1) * w.2.val.1, w.2.val.2),
      ⟨⟨_, rfl, by
        rw [mul_smul]
        exact (colength_positive (lift w.1) (representative_loop_colength w.2).1).mpr
          (representative_loop_colength w.2)⟩, w.2.property.2⟩⟩
  have hr (w : Parameters H representativeSpace) :
      integralRepresentative (r₁ w) = (lift w.1).val * integralRepresentative w.2 := by
    apply Matrix.ext
    intro i j
    apply inclusion_injective
    change ((integralRepresentative (r₁ w)).map inclusion) i j =
      (((lift w.1).val * integralRepresentative w.2).map inclusion) i j
    rw [integralRepresentative_eq, Matrix.map_mul, integralRepresentative_eq]
    rfl
  have hj (w : Parameters H representativeSpace) :
      (integralRepresentative (r₁ w)).map (jetReduction 2) =
        w.1.val * (integralRepresentative w.2).map (jetReduction 2) := by
    rw [hr, Matrix.map_mul]
    exact congrArg (fun g : Jets ↦ g.val * (integralRepresentative w.2).map (jetReduction 2)) (hlift w.1)
  refine ⟨TopCat.ofHom ⟨r₁, ?_⟩, fun w ↦ ⟨lift w.1, hlift w.1, rfl, rfl⟩⟩
  apply continuous_induced_rng.mpr
  change Continuous (fun w ↦ representativeCoordinates (r₁ w))
  apply Continuous.prodMk
  · let J (w : Parameters H representativeSpace) :=
      w.1.val * (integralRepresentative w.2).map (jetReduction 2)
    have hA : Continuous (fun w : Parameters H representativeSpace ↦ w.1.val) :=
      continuous_jetMatrixVal.comp continuous_fst
    have hB : Continuous (fun w : Parameters H representativeSpace ↦
        (integralRepresentative w.2).map (jetReduction 2)) :=
      continuous_integralJet.comp continuous_snd
    have hJ : Continuous J := by
      apply continuous_jetMatrix
      · simp only [J, constantMatrix_mul]
        exact (continuous_constantMatrix.comp hA).matrix_mul (continuous_constantMatrix.comp hB)
      · simp only [J, linearMatrix_mul]
        exact ((continuous_constantMatrix.comp hA).matrix_mul (continuous_linearMatrix.comp hB)).add
          ((continuous_linearMatrix.comp hA).matrix_mul (continuous_constantMatrix.comp hB))
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply continuous_pi
    intro k
    have hv := (continuous_apply k).comp (continuous_induced_dom :
      Continuous (jetCoefficients 2))
    have hh : Continuous (fun w ↦ jetCoefficients 2 (J w i j) k) :=
      hv.comp ((continuous_apply_apply i j).comp hJ)
    apply hh.congr
    intro w
    dsimp only [J]
    rw [← hj w]
    exact integralJet_coeff (r₁ w) i j k
  · change Continuous (fun w : Parameters H representativeSpace ↦ representedSecondStage w.2)
    exact (continuous_snd.comp (continuous_induced_dom : Continuous representativeCoordinates)).comp
      continuous_snd

private theorem terminalPlane_positive (g : GL (Fin 2) O) (L : GL2Lattice) :
    ((latticeSubspace 0 2 L).map twoStepCoordinates.toLinearMap).map
        (twoTermJetLinear (reduceGL 2 2 (by decide) g)) =
      (latticeSubspace 0 2 (positiveGLMap 2 g • L)).map twoStepCoordinates.toLinearMap := by
  rw [← latticeSubspace_positive 0 (m := 2) (by decide : 1 ≤ 2) (le_refl 2) g L,
    ← Submodule.map_comp, ← Submodule.map_comp]
  apply congrArg (fun T : Window 2 0 2 →ₗ[ℂ] (V × V) ↦ (latticeSubspace 0 2 L).map T)
  simp only [twoTermJetLinear, LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.comp_id]

private theorem firstPlane_positive (g : GL (Fin 2) O) (L : GL2Lattice) :
    ((latticeSubspace 0 1 L).map constantCoordinates.toLinearMap).map
        (constantJetLinear (reduceGL 2 2 (by decide) g)) =
      (latticeSubspace 0 1 (positiveGLMap 2 g • L)).map constantCoordinates.toLinearMap :=
  (firstLine_jet _ _ _ (latticeSubspace_positive 0 (m := 2) (by decide : 1 ≤ 2) (le_refl 2) g L).symm).symm

/-- The continuous left multiplication on representatives projects to the
ordered action and the first factor action while fixing the framed second factor. -/
private theorem frameLeftSquares (d : SplittingData)
    (q : representativeSpace ⟶ ordered) (b : representativeSpace ⟶ minuscule)
    (h₁ : ∀ p, firstPlane (firstStageMap (q p)) =
      (latticeSubspace 0 1 (p.val.1 • standardLattice 2)).map constantCoordinates.toLinearMap)
    (h₂ : ∀ p, secondPlane (convolutionMap (q p)) =
      (latticeSubspace 0 2 (p.val.1 • p.val.2)).map twoStepCoordinates.toLinearMap)
    (hb : ∀ p, firstPlane (b p) = (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap) :
    let H := jetGroup d.topologicalGroup
    let r₀ := projection H representativeSpace
    ∃ r₁ : Parameters H representativeSpace ⟶ representativeSpace,
      productMap H.space q ≫ d.orderedAction.act = r₁ ≫ q ∧
      productMap H.space (q ≫ firstStageMap) ≫ d.firstAction.act = r₁ ≫ q ≫ firstStageMap ∧
      r₁ ≫ b = r₀ ≫ b ∧
      ∀ w, ∃ g : GL (Fin 2) O,
        reduceGL 2 2 (by decide) g = w.1 ∧
        (r₁ w).val.1 = positiveGLMap 2 g * (r₀ w).val.1 ∧
        (r₁ w).val.2 = (r₀ w).val.2 := by
  obtain ⟨r₁, hr⟩ := frameLeftAction d
  have firstEqual (w : Parameters (jetGroup d.topologicalGroup) representativeSpace) :
      d.firstAction.act (w.1, firstStageMap (q w.2)) = firstStageMap (q (r₁ w)) := by
    obtain ⟨g, hg, hg₁, _⟩ := hr w
    apply grassmannianSubspace_injective projectiveBasis projectiveRank
    change firstPlane (d.firstAction.act (w.1, firstStageMap (q w.2))) =
      firstPlane (firstStageMap (q (r₁ w)))
    rw [d.first_action, h₁, h₁, ← hg, hg₁, mul_smul, firstPlane_positive]
  refine ⟨r₁, ?_, ?_, ?_, hr⟩
  · apply TopCat.ext
    intro w
    obtain ⟨g, hg, hg₁, hg₂⟩ := hr w
    change d.orderedAction.act (w.1, q w.2) = q (r₁ w)
    apply incidencePoints_ext
    · change firstStageMap (d.orderedAction.act (w.1, q w.2)) = _
      rw [d.firstStage_equivariant, firstEqual]
      rfl
    · change convolutionMap (d.orderedAction.act (w.1, q w.2)) = convolutionMap (q (r₁ w))
      apply secondPlane_injective
      rw [d.commutes, d.terminal_action, h₂, h₂, ← hg, hg₁, hg₂, mul_smul, terminalPlane_positive]
  · exact TopCat.ext firstEqual
  · apply TopCat.ext
    intro w
    obtain ⟨_, _, _, hw⟩ := hr w
    apply grassmannianSubspace_injective projectiveBasis projectiveRank
    change firstPlane (b (r₁ w)) = firstPlane (b w.2)
    rw [hb, hb, hw]

open private CMatrix JMatrix IntegralMatrix jetConstant jetConstant_eq jetLinear jetLinear_mul
  constantJetLinear_eq chartIntegral chartFrame_integral chartFrame constantLift
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionFrameQuotient
open private loop_stabilizer from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle

private abbrev frameJet (p : FrameRepresentative) : JMatrix :=
  (integralRepresentative p).map (jetReduction 2).toRingHom

/-- A colength-one frame has determinant of order exactly one. -/
private theorem frameJetDet (p : FrameRepresentative) :
    jetConstant (frameJet p).det = 0 ∧ jetLinear (frameJet p).det ≠ 0 := by
  have hp := Set.ext_iff.mp MinusculeAndTwoStep.minusculeOrbit.1 _ |>.mp
    (representative_loop_colength p)
  obtain ⟨⟨_, u, rfl⟩, hu⟩ := hp
  let k := positiveGLMap 2 u * diagonalLoop 2 (pairCoweight minusculePair)
  have hk : k • standardLattice 2 = p.val.1 • standardLattice 2 := by
    dsimp only [k]
    rw [mul_smul, diagonalLoop_smul_standard]
    exact hu
  obtain ⟨v, hv⟩ := loop_stabilizer (k⁻¹ * p.val.1) (by rw [mul_smul, ← hk, inv_smul_smul])
  have he : p.val.1 = k * positiveGLMap 2 v := by rw [hv, ← mul_assoc, mul_inv_cancel, one_mul]
  let D : IntegralMatrix := Matrix.diagonal ![t, 1]
  have hD : D.map inclusion = (diagonalLoop 2 (pairCoweight minusculePair)).val := by
    simpa [D, chartIntegral, chartFrame, constantLift] using
      (chartFrame_integral (1 : GL (Fin 2) ℂ))
  have hI : integralRepresentative p = u.val * D * v.val := by
    apply Matrix.ext
    intro i j
    apply inclusion_injective
    change ((integralRepresentative p).map inclusion) i j = ((u.val * D * v.val).map inclusion) i j
    rw [integralRepresentative_eq, Matrix.map_mul, Matrix.map_mul, hD, he]
    rfl
  let T := jetReduction 2 t
  have hDdet : D.det = t := by simp [D, Matrix.det_diagonal, Fin.prod_univ_two]
  let U := reduceGL 2 2 (by decide) u
  let V := reduceGL 2 2 (by decide) v
  have hdet : (frameJet p).det = (U.val.det * V.val.det) * T := by
    change ((integralRepresentative p).map (jetReduction 2).toRingHom).det = _
    calc
      _ = jetReduction 2 (integralRepresentative p).det :=
        ((jetReduction 2).toRingHom.map_det _).symm
      _ = _ := by
        rw [hI, Matrix.det_mul, Matrix.det_mul, hDdet, map_mul, map_mul]
        have detReduce (g : GL (Fin 2) O) :
            jetReduction 2 g.val.det = (reduceGL 2 2 (by decide) g).val.det :=
          (jetReduction 2).toRingHom.map_det _
        rw [detReduce, detReduce]
        change (U.val.det * T) * V.val.det = _
        ac_rfl
  have hT₀ : jetConstant T = 0 := by
    simp [T, jetConstant_eq, t, PowerSeries.coeff_X]
  have hT₁ : jetLinear T = 1 := by
    simp [T, jetLinear, t, PowerSeries.coeff_X]
  rw [hdet, map_mul, hT₀, mul_zero, jetLinear_mul, hT₀, hT₁, mul_one, mul_zero, add_zero, map_mul]
  exact ⟨rfl, mul_ne_zero (isUnit_iff_ne_zero.mp ((Matrix.isUnits_det_units U).map jetConstant))
    (isUnit_iff_ne_zero.mp ((Matrix.isUnits_det_units V).map jetConstant))⟩

private theorem frameJet_change {p₀ p₁ : FrameRepresentative} {g : GL (Fin 2) O}
    (h : p₀.val.1 = p₁.val.1 * positiveGLMap 2 g) :
    frameJet p₀ = frameJet p₁ * (reduceGL 2 2 (by decide) g).val := by
  have hi : integralRepresentative p₀ = integralRepresentative p₁ * g.val := by
    apply Matrix.ext
    intro i j
    apply inclusion_injective
    change ((integralRepresentative p₀).map inclusion) i j =
      ((integralRepresentative p₁ * g.val).map inclusion) i j
    rw [Matrix.map_mul, integralRepresentative_eq, integralRepresentative_eq, h]
    rfl
  change (integralRepresentative p₀).map (jetReduction 2).toRingHom = _
  rw [hi, Matrix.map_mul]
  rfl

private theorem constantChange_formula {p₀ p₁ : FrameRepresentative} {g : GL (Fin 2) O}
    (h : p₀.val.1 = p₁.val.1 * positiveGLMap 2 g) :
    (jetLinear (frameJet p₁).det)⁻¹ • linearMatrix ((frameJet p₁).adjugate * frameJet p₀) =
      constantMatrix (reduceGL 2 2 (by decide) g).val := by
  have hc := frameJetDet p₁
  let B := (reduceGL 2 2 (by decide) g).val
  rw [frameJet_change h, ← Matrix.mul_assoc, Matrix.adjugate_mul]
  have hsm : ((frameJet p₁).det • (1 : JMatrix)) * B = (frameJet p₁).det • B := by
    rw [Matrix.smul_mul (R := JetRing 2), Matrix.one_mul]
  rw [hsm]
  have hB : linearMatrix ((frameJet p₁).det • B) = jetLinear (frameJet p₁).det • constantMatrix B := by
    apply Matrix.ext
    intro i j
    change jetLinear ((frameJet p₁).det * B i j) = _
    rw [jetLinear_mul, hc.1, zero_mul, zero_add]
    rfl
  rw [hB, smul_smul, inv_mul_cancel₀ hc.2, one_smul]

private theorem linearMatrix_adjugate (G : JMatrix) :
    linearMatrix G.adjugate = (linearMatrix G).adjugate := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, linearMatrix, jetLinear, Matrix.map_apply]

private theorem continuous_frameDetLinear : Continuous (fun p : FrameRepresentative ↦
    jetLinear (frameJet p).det) := by
  have h₀ := continuous_constantMatrix.comp continuous_integralJet
  have h₁ := continuous_linearMatrix.comp continuous_integralJet
  have hsub (z w : JetRing 2) : jetLinear (z - w) = jetLinear z - jetLinear w :=
    congrFun ((jetCoefficients 2).map_sub z w) 1
  simp only [Matrix.det_fin_two, hsub, jetLinear_mul]
  exact (((h₀.matrix_elem 0 0).mul (h₁.matrix_elem 1 1)).add
    ((h₁.matrix_elem 0 0).mul (h₀.matrix_elem 1 1))).sub
    (((h₀.matrix_elem 0 1).mul (h₁.matrix_elem 1 0)).add
      ((h₁.matrix_elem 0 1).mul (h₀.matrix_elem 1 0)))

/-- The inverse frame change seen by the relative minuscule lattice is
continuous, using only the first two coefficients of each frame. -/
private theorem frameOverlapMap (s : SplittingData)
    {h : StableStage (PositiveGL 2) (colength 1)}
    (e : OrderedProduct h ≃ ordered) (q : representativeSpace ⟶ ordered)
    (b : representativeSpace ⟶ minuscule)
    (hq : ∀ p : FrameRepresentative,
      q p = e (Quotient.mk (twistRel (PositiveGL 2) firstStage (colength 1)) p))
    (hb : ∀ p, firstPlane (b p) = (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap) :
    let H := jetGroup s.topologicalGroup
    ∃ γ : overlap q ⟶ Parameters H minuscule,
      γ ≫ s.firstAction.act = rightLeg q ≫ b ∧
      γ ≫ projection H minuscule = leftLeg q ≫ b ∧
      ∀ w : overlap q, ∃ g : GL (Fin 2) O,
        (rightLeg q w).val.1 = (leftLeg q w).val.1 * positiveGLMap 2 g ∧
        (rightLeg q w).val.2 = positiveGLMap 2 g⁻¹ • (leftLeg q w).val.2 ∧
        constantJetLinear (γ w).1 = constantJetLinear (reduceGL 2 2 (by decide) g⁻¹) := by
  classical
  choose g hg hL using frameChange e q hq
  let j (w : overlap q) : Jets := reduceGL 2 2 (by decide) (g w)⁻¹
  let g₀ (w : overlap q) : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map jetConstant (j w)
  let C : ℂ →+* JetRing 2 := (jetReduction 2).toRingHom.comp PowerSeries.C
  let gj (w : overlap q) : Jets := Matrix.GeneralLinearGroup.map C (g₀ w)
  have hC₀ (z : ℂ) : jetConstant (C z) = z := by simp [C, jetConstant_eq, PowerSeries.coeff_C]
  have hC₁ (z : ℂ) : jetLinear (C z) = 0 := by simp [C, jetLinear]
  have hval (w : overlap q) : constantMatrix (gj w).val = (g₀ w).val := by
    apply Matrix.ext
    intro i k
    exact hC₀ _
  have hlin (w : overlap q) : linearMatrix (gj w).val = 0 := by
    apply Matrix.ext
    intro i k
    exact hC₁ _
  have hchange (w : overlap q) :
      (leftLeg q w).val.1 = (rightLeg q w).val.1 * positiveGLMap 2 (g w)⁻¹ := by
    rw [hg, map_inv, mul_assoc, mul_inv_cancel, mul_one]
  have hc : Continuous (fun w : overlap q ↦ (g₀ w).val) := by
    have hG₀ := continuous_integralJet.comp (leftLeg q).hom.continuous
    have hG₁ := continuous_integralJet.comp (rightLeg q).hom.continuous
    have hD := continuous_frameDetLinear.comp (rightLeg q).hom.continuous
    have hD' : Continuous (fun w : overlap q ↦ (jetLinear (frameJet (rightLeg q w)).det)⁻¹) :=
      hD.inv₀ (fun w ↦ (frameJetDet (rightLeg q w)).2)
    have hnum : Continuous (fun w : overlap q ↦
        linearMatrix ((frameJet (rightLeg q w)).adjugate * frameJet (leftLeg q w))) := by
      have hcAdj (G : JMatrix) : constantMatrix G.adjugate = (constantMatrix G).adjugate :=
        jetConstant.map_adjugate G
      simp only [linearMatrix_mul, linearMatrix_adjugate, hcAdj]
      have adj (f : overlap q → CMatrix) (hf : Continuous f) :
          Continuous (fun w ↦ (f w).adjugate) := by
        apply continuous_matrix
        intro i k
        fin_cases i <;> fin_cases k <;> simp [Matrix.adjugate_fin_two] <;> fun_prop
      exact ((adj _ (continuous_constantMatrix.comp hG₁)).matrix_mul
        (continuous_linearMatrix.comp hG₀)).add
        ((adj _ (continuous_linearMatrix.comp hG₁)).matrix_mul
          (continuous_constantMatrix.comp hG₀))
    exact (hD'.smul hnum).congr (fun w ↦ constantChange_formula (hchange w))
  have hj : Continuous gj := by
    apply continuous_induced_rng.mpr
    apply continuous_jetMatrix
    · exact hc.congr (fun w ↦ (hval w).symm)
    · exact continuous_const.congr (fun w ↦ (hlin w).symm)
  have heq (w : overlap q) : constantJetLinear (gj w) = constantJetLinear (j w) := by
    rw [constantJetLinear_eq, constantJetLinear_eq, hval]
    rfl
  let H := jetGroup s.topologicalGroup
  refine ⟨TopCat.ofHom ⟨fun w ↦ (gj w, b (leftLeg q w)), hj.prodMk
    (b.hom.continuous.comp (leftLeg q).hom.continuous)⟩, ?_, rfl,
      fun w ↦ ⟨g w, hg w, hL w, heq w⟩⟩
  apply TopCat.ext
  intro w
  apply grassmannianSubspace_injective projectiveBasis projectiveRank
  change firstPlane (s.firstAction.act (gj w, b (leftLeg q w))) = firstPlane (b (rightLeg q w))
  rw [s.first_action, heq, hb, hb, hL]
  exact firstPlane_positive _ _

end FrameActions

section TensorCoefficients

open CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open scoped TensorProduct
open ConvolutionConstantDescentSpec (tensorPresheaf)
open MinusculeFrameDescentSpecs (tensorMap)
open ConvolutionUnitCone (shiftedTensorPullback)
open private compositionUnit pulledTensorSections from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitCone
open private coefficientTensorIso_multiplication shiftedTensorPullback_multiplication
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitCone

/-- A tensor of coefficient maps preserving the scalar generators
preserves the multiplication trivialization. -/
private theorem tensorMapPreservesMultiplication {W X Y : TopCat.{0}}
    (a₁ a₀ : W ⟶ X) (b₁ b₀ : W ⟶ Y)
    (u : (inverseImage a₁).obj (rational X) ⟶ (inverseImage a₀).obj (rational X))
    (v : (inverseImage b₁).obj (rational Y) ⟶ (inverseImage b₀).obj (rational Y))
    (hu : u ≫ (constantPullback a₀).hom = (constantPullback a₁).hom)
    (hv : v ≫ (constantPullback b₀).hom = (constantPullback b₁).hom)
    (μ₁ : pulledBackTensor a₁ b₁ ≅ rational W)
    (μ₀ : pulledBackTensor a₀ b₀ ≅ rational W)
    (h₁ : MultipliesCoefficients a₁ b₁ μ₁) (h₀ : MultipliesCoefficients a₀ b₀ μ₀) :
    tensorMap u v ≫ μ₀.hom = μ₁.hom := by
  have hu' : u = (coefficientTransition a₁ a₀).hom := by
    apply (cancel_mono (constantPullback a₀).hom).mp
    simpa [coefficientTransition] using hu
  have hv' : v = (coefficientTransition b₁ b₀).hom := by
    apply (cancel_mono (constantPullback b₀).hom).mp
    simpa [coefficientTransition] using hv
  rw [hu', hv']
  exact coefficientTensorIso_multiplication a₁ a₀ b₁ b₀ μ₁ μ₀ h₁ h₀

private theorem tensorMap_sections {W : TopCat.{0}} {F G F' G' : Sheaves W}
    (u : F ⟶ F') (v : G ⟶ G') (U : (Opens W)ᵒᵖ) :
    let s := sheafificationAdjunction (Opens.grothendieckTopology W) Coeff.{0}
    (s.unit.app (tensorPresheaf F G)).app U ≫ (tensorMap u v).hom.app U =
      (u.hom.app U ⊗ₘ v.hom.app U) ≫ (s.unit.app (tensorPresheaf F' G')).app U := by
  unfold tensorMap
  exact (NatTrans.congr_app ((sheafificationAdjunction _ _).unit.naturality _) U).symm

/-- Taking the two adjunction mates identifies the factorized map with
the comparison induced directly by the composed factor units. -/
private theorem ordinaryPullbackTensor_eq {W Z X Y : TopCat.{0}}
    (r : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) :
    inverseTensorMap r ((inverseImage a).obj (rational X)) ((inverseImage b).obj (rational Y)) ≫
      tensorMap ((inverseImageComposition r a).inv.app (rational X))
        ((inverseImageComposition r b).inv.app (rational Y)) =
      ConvolutionUnitConeSpecs.pullbackTensorMap r a b := by
  let F := (inverseImage a).obj (rational X)
  let G := (inverseImage b).obj (rational Y)
  let u := (inverseImageComposition r a).inv.app (rational X)
  let v := (inverseImageComposition r b).inv.app (rational Y)
  let P := ConvolutionConstantDescentSpec.coefficientTensor ((inverseImage r).obj F) ((inverseImage r).obj G)
  let Q := pulledBackTensor (r ≫ a) (r ≫ b)
  let A := inverseDirectAdjunction r
  let S := sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}
  let K := tensorPresheaf F G
  apply (A.homEquiv (pulledBackTensor a b) Q).injective
  rw [Adjunction.homEquiv_naturality_right]
  change A.homEquiv (pulledBackTensor a b) P (inverseTensorMap r F G) ≫
    (directImage r).map (tensorMap u v) = _
  unfold inverseTensorMap ConvolutionUnitConeSpecs.pullbackTensorMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply (S.homEquiv K ((directImage r).obj Q)).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  let V := (Opens.map r).op.obj U
  let η := (sheafificationAdjunction (Opens.grothendieckTopology W) Coeff.{0}).unit
  change ((A.unit.app F).hom.app U ⊗ₘ (A.unit.app G).hom.app U) ≫
      (η.app (tensorPresheaf ((inverseImage r).obj F) ((inverseImage r).obj G))).app V ≫
      (tensorMap u v).hom.app V =
    ((compositionUnit r a).hom.app U ⊗ₘ (compositionUnit r b).hom.app U) ≫
      (η.app (tensorPresheaf ((inverseImage (r ≫ a)).obj (rational X))
        ((inverseImage (r ≫ b)).obj (rational Y)))).app V
  rw [tensorMap_sections, tensorHom_comp_tensorHom_assoc]
  simp only [compositionUnit, Adjunction.homEquiv_unit]
  rfl

private abbrev shiftedSingleIso {W : TopCat.{0}} (d : ℕ) {F G : Sheaves W} (e : F ≅ G) :=
  (shiftFunctor (Derived W) (d : ℤ)).mapIso
    ((DerivedCategory.singleFunctor (Sheaves W) 0).mapIso e)

/-- The comparison in the frame specification uses the same single-complex and
shift isomorphisms as the upstream pullback of the shifted tensor. -/
private theorem shiftedPullbackTensor_eq {W Z X Y : TopCat.{0}}
    (r : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) :
    MinusculeFrameDescentSpecs.pullbackTensorMap r a b = (shiftedTensorPullback r a b).hom := by
  rw [MinusculeFrameDescentSpecs.pullbackTensorMap, ordinaryPullbackTensor_eq]
  simp only [shiftedTensorPullback, shiftedSinglePullback, Iso.trans_hom, NatTrans.comp_app,
    Iso.app_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.mapIso_hom, asIso_hom, Category.assoc]
  rfl

private theorem pullbackTensorMultiplication {W Z X Y : TopCat.{0}}
    (r : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y)
    (μZ : pulledBackTensor a b ≅ rational Z)
    (μW : pulledBackTensor (r ≫ a) (r ≫ b) ≅ rational W)
    (hZ : MultipliesCoefficients a b μZ) (hW : MultipliesCoefficients (r ≫ a) (r ≫ b) μW) :
    MinusculeFrameDescentSpecs.pullbackTensorMap r a b ≫ shiftedSingleMap 2 μW.hom =
      (derivedInverseImage r).map (shiftedSingleMap 2 μZ.hom) ≫
        (shiftedConstantPullback r 2).hom := by
  rw [shiftedPullbackTensor_eq]
  exact congrArg Iso.hom (shiftedTensorPullback_multiplication r a b μZ μW hZ hW)

private theorem pullbackTensorMap_isIso {W Z X Y : TopCat.{0}}
    (r : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) :
    IsIso (MinusculeFrameDescentSpecs.pullbackTensorMap r a b) := by
  rw [shiftedPullbackTensor_eq]
  infer_instance

private theorem constantFactorComparison {W X : TopCat.{0}} (f g : W ⟶ X) (d : ℕ) :
    (pullbackFactorIso f d).hom ≫
        shiftedSingleMap d ((constantPullback f).hom ≫ (constantPullback g).inv) ≫
        (pullbackFactorIso g d).inv =
      ((shiftedConstantPullback f d) ≪≫ (shiftedConstantPullback g d).symm).hom := by
  have h (p : W ⟶ X) :
      pullbackFactorIso p d ≪≫ shiftedSingleIso d (constantPullback p) =
        shiftedConstantPullback p d := by
    apply Iso.ext
    simp only [pullbackFactorIso, shiftedConstantPullback, Iso.trans_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
  rw [← h f, ← h g]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, shiftedSingleMap, Functor.map_comp, Category.assoc]

private theorem constantFactorTransport {W X : TopCat.{0}} {f g : W ⟶ X} (h : f = g) :
    eqToHom (congrArg (fun f => (inverseImage f).obj (rational X)) h) ≫
      (constantPullback g).hom = (constantPullback f).hom := by
  subst g
  simp

private theorem shiftedConstantTransport {W X : TopCat.{0}} {f g : W ⟶ X} (h : f = g) (d : ℕ) :
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj
      (IntersectionComplex.shiftedConstant X d).obj) h) ≫
      (shiftedConstantPullback g d).hom = (shiftedConstantPullback f d).hom := by
  subst g
  simp

/-- Compare the two transitions after identifying each tensor with the
shifted constant complex by scalar multiplication. -/
private theorem tensorDescentSquare {W Z X Y S : TopCat.{0}}
    {a : Z ⟶ X} {b : Z ⟶ Y} {q : Z ⟶ S} {r₀ r₁ : W ⟶ Z}
    {μ : pulledBackTensor a b ≅ rational Z}
    (hμ : MultipliesCoefficients a b μ)
    {e : (derivedInverseImage q).obj (IntersectionComplex.shiftedConstant S 2).obj ≅ shiftedTensor a b}
    (he : e ≪≫ shiftedSingleIso 2 μ = shiftedConstantPullback q 2)
    (v : (derivedInverseImage (r₁ ≫ q)).obj (IntersectionComplex.shiftedConstant S 2).obj ⟶
      (derivedInverseImage (r₀ ≫ q)).obj (IntersectionComplex.shiftedConstant S 2).obj)
    (hv : v ≫ (shiftedConstantPullback (r₀ ≫ q) 2).hom =
      (shiftedConstantPullback (r₁ ≫ q) 2).hom)
    (u₁ : (inverseImage (r₁ ≫ a)).obj (rational X) ⟶ (inverseImage (r₀ ≫ a)).obj (rational X))
    (u₂ : (inverseImage (r₁ ≫ b)).obj (rational Y) ⟶ (inverseImage (r₀ ≫ b)).obj (rational Y))
    (hu₁ : u₁ ≫ (constantPullback (r₀ ≫ a)).hom = (constantPullback (r₁ ≫ a)).hom)
    (hu₂ : u₂ ≫ (constantPullback (r₀ ≫ b)).hom = (constantPullback (r₁ ≫ b)).hom) :
    MinusculeFrameDescentSpecs.pullbackTensorMap r₁ a b ≫ shiftedSingleMap 2 (tensorMap u₁ u₂) =
      ((derivedInverseImage r₁).map e.inv ≫
        (derivedInverseImageComposition r₁ q).inv.app (IntersectionComplex.shiftedConstant S 2).obj ≫
        v ≫ (derivedInverseImageComposition r₀ q).hom.app (IntersectionComplex.shiftedConstant S 2).obj ≫
        (derivedInverseImage r₀).map e.hom) ≫ MinusculeFrameDescentSpecs.pullbackTensorMap r₀ a b := by
  obtain ⟨μ₀, h₀⟩ := ConvolutionConstantDescent.tensorMultiplication (r₀ ≫ a) (r₀ ≫ b)
  obtain ⟨μ₁, h₁⟩ := ConvolutionConstantDescent.tensorMultiplication (r₁ ≫ a) (r₁ ≫ b)
  let R := (IntersectionComplex.shiftedConstant S 2).obj
  let L (r : W ⟶ Z) := (derivedInverseImage r).map (shiftedSingleIso 2 μ).hom ≫
    (shiftedConstantPullback r 2).hom
  let Q (r : W ⟶ Z) := (derivedInverseImageComposition r q).app R ≪≫ (derivedInverseImage r).mapIso e
  have hT := tensorMapPreservesMultiplication _ _ _ _ u₁ u₂ hu₁ hu₂ μ₁ μ₀ h₁ h₀
  have hTs : shiftedSingleMap 2 (tensorMap u₁ u₂) ≫ (shiftedSingleIso 2 μ₀).hom =
      (shiftedSingleIso 2 μ₁).hom := by
    let S := DerivedCategory.singleFunctor (Sheaves W) 0 ⋙ shiftFunctor (Derived W) (2 : ℤ)
    change S.map (tensorMap u₁ u₂) ≫ S.map μ₀.hom = S.map μ₁.hom
    rw [← S.map_comp, hT]
  have hQ (r : W ⟶ Z) : (Q r).hom ≫ L r = (shiftedConstantPullback (r ≫ q) 2).hom := by
    have h := congrArg Iso.hom he
    change e.hom ≫ shiftedSingleMap 2 μ.hom = (shiftedConstantPullback q 2).hom at h
    dsimp only [Q, L, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    rw [Category.assoc, ← Category.assoc ((derivedInverseImage r).map e.hom),
      ← Functor.map_comp, h]
    exact ConvolutionConstantDescent.shiftedPullbackComposition r q 2
  have hP₀ : MinusculeFrameDescentSpecs.pullbackTensorMap r₀ a b ≫ (shiftedSingleIso 2 μ₀).hom = L r₀ :=
    pullbackTensorMultiplication r₀ a b μ μ₀ hμ h₀
  have hP₁ : MinusculeFrameDescentSpecs.pullbackTensorMap r₁ a b ≫ (shiftedSingleIso 2 μ₁).hom = L r₁ :=
    pullbackTensorMultiplication r₁ a b μ μ₁ hμ h₁
  apply (cancel_mono (shiftedSingleIso 2 μ₀).hom).mp
  rw [Category.assoc (MinusculeFrameDescentSpecs.pullbackTensorMap r₁ a b), hTs, hP₁, Category.assoc, hP₀]
  calc
    _ = (Q r₁).inv ≫ v ≫ (Q r₀).hom ≫ L r₀ := by
      rw [hQ, hv, ← hQ r₁, Iso.inv_hom_id_assoc]
    _ = _ := by
      simp only [Q, R, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
        Functor.mapIso_inv, Category.assoc]

end TensorCoefficients

open AnalyticAction
open private pullback_constantTransition from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent

private theorem overlapIdentification (s : SplittingData)
    {q : representativeSpace ⟶ ordered} {b : representativeSpace ⟶ minuscule}
    {h : StableStage (PositiveGL 2) (colength 1)}
    (E : OrderedProduct h ≃ ordered)
    (hq : ∀ p : FrameRepresentative,
      q p = E (Quotient.mk (twistRel (PositiveGL 2) firstStage (colength 1)) p))
    (hb : ∀ p, firstPlane (b p) = (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap)
    {μ : pulledBackTensor (q ≫ firstStageMap) b ≅ rational representativeSpace}
    {e : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor (q ≫ firstStageMap) b}
    (hμ : MultipliesCoefficients (q ≫ firstStageMap) b μ)
    (he : e ≪≫ shiftedSingleIso 2 μ = shiftedConstantPullback q 2) :
    FrameOverlapIdentification s.firstEq q b e := by
  let a := q ≫ firstStageMap
  let r₀ := leftLeg q
  let r₁ := rightLeg q
  have ha : r₁ ≫ a = r₀ ≫ a := by simp only [a, ← Category.assoc, r₀, r₁, commonImage]
  obtain ⟨γ, hb₁, hb₀, hg⟩ := frameOverlapMap s E q b hq hb
  let u₂ := (constantPullback (r₁ ≫ b)).hom ≫ (constantPullback (r₀ ≫ b)).inv
  refine ⟨γ, hb₁, hb₀, hg, pullbackTensorMap_isIso r₁ a b,
    pullbackTensorMap_isIso r₀ a b, u₂, ?_, ?_⟩
  · rw [s.first_normalized, pullback_constantTransition γ hb₁ hb₀ 1]
    exact constantFactorComparison (r₁ ≫ b) (r₀ ≫ b) 1
  · exact tensorDescentSquare hμ he _ (shiftedConstantTransport (commonImage q) 2) _ u₂
      (constantFactorTransport ha) (by
        change u₂ ≫ (constantPullback (r₀ ≫ b)).hom = (constantPullback (r₁ ≫ b)).hom
        simp [u₂])

private theorem actionIdentification (s : SplittingData)
    {q : representativeSpace ⟶ ordered} {b : representativeSpace ⟶ minuscule}
    (h₁ : ∀ p, firstPlane (firstStageMap (q p)) =
      (latticeSubspace 0 1 (p.val.1 • standardLattice 2)).map constantCoordinates.toLinearMap)
    (h₂ : ∀ p, secondPlane (convolutionMap (q p)) =
      (latticeSubspace 0 2 (p.val.1 • p.val.2)).map twoStepCoordinates.toLinearMap)
    (hb : ∀ p, firstPlane (b p) = (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap)
    {μ : pulledBackTensor (q ≫ firstStageMap) b ≅ rational representativeSpace}
    {e : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor (q ≫ firstStageMap) b}
    (hμ : MultipliesCoefficients (q ≫ firstStageMap) b μ)
    (he : e ≪≫ shiftedSingleIso 2 μ = shiftedConstantPullback q 2) :
    FrameActionIdentification s.firstEq s.orderedEq q b e := by
  let a := q ≫ firstStageMap
  let H := jetGroup s.topologicalGroup
  let r₀ := projection H representativeSpace
  let γ₁ := productMap H.space a
  let γq := productMap H.space q
  have ha₀ : γ₁ ≫ projection H minuscule = r₀ ≫ a := rfl
  have hq₀ : γq ≫ projection H ordered = r₀ ≫ q := rfl
  obtain ⟨r₁, hq₁, ha₁, hfix, hg⟩ := frameLeftSquares s q b h₁ h₂ hb
  let u₁ := (constantPullback (r₁ ≫ a)).hom ≫ (constantPullback (r₀ ≫ a)).inv
  refine ⟨r₁, hq₁, ha₁, hfix, hg, pullbackTensorMap_isIso r₁ a b,
    pullbackTensorMap_isIso r₀ a b, u₁, ?_, ?_⟩
  · change (pullbackFactorIso (r₁ ≫ a) 1).hom ≫ shiftedSingleMap 1 u₁ ≫
      (pullbackFactorIso (r₀ ≫ a) 1).inv = pullbackMorphism γ₁ ha₁ ha₀ s.firstEq.iso.hom
    rw [s.first_normalized]
    exact (constantFactorComparison (r₁ ≫ a) (r₀ ≫ a) 1).trans
      (pullback_constantTransition γ₁ ha₁ ha₀ 1).symm
  · have hv : pullbackMorphism γq hq₁ hq₀ s.orderedEq.iso.hom ≫
        (shiftedConstantPullback (r₀ ≫ q) 2).hom = (shiftedConstantPullback (r₁ ≫ q) 2).hom := by
      rw [s.ordered_normalized]
      have ht := pullback_constantTransition γq hq₁ hq₀ 2
      change pullbackMorphism γq hq₁ hq₀
        ((shiftedConstantPullback s.orderedAction.act 2) ≪≫
          (shiftedConstantPullback (projection H ordered) 2).symm).hom =
        ((shiftedConstantPullback (r₁ ≫ q) 2) ≪≫ (shiftedConstantPullback (r₀ ≫ q) 2).symm).hom at ht
      rw [ht]
      simp
    exact tensorDescentSquare hμ he _ hv u₁ _ (by
      change u₁ ≫ (constantPullback (r₀ ≫ a)).hom = (constantPullback (r₁ ≫ a)).hom
      simp [u₁]) (constantFactorTransport hfix)

/-- The two minuscule factors descend with the specified equivariance on the
actual ordered convolution quotient. -/
theorem minusculeFrameDescent : Expected.MinusculeFrameDescent := by
  intro s
  obtain ⟨h, E, b, q, hquot, hcoords⟩ := ConvolutionFrameQuotient.frameQuotient
  obtain ⟨μ, e, hμ, he, _⟩ := ConvolutionConstantDescent.shiftedDescent (q ≫ firstStageMap) b q
  exact ⟨h, E, b, q, hquot, hcoords, μ, e, hμ, he,
    overlapIdentification s E (fun p ↦ (hcoords p).1) (fun p ↦ (hcoords p).2.2.1) hμ he,
    actionIdentification s (fun p ↦ (hcoords p).2.1) (fun p ↦ (hcoords p).2.2.2)
      (fun p ↦ (hcoords p).2.2.1) hμ he⟩

end RepTheorySurvey.Geometric.MinusculeFrameDescent
