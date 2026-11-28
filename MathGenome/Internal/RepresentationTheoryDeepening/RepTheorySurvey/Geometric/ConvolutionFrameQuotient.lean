import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionFrameQuotient
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianIncidenceTopology
import Batteries.Tactic.OpenPrivate

namespace RepTheorySurvey.Geometric.ConvolutionFrameQuotient

noncomputable section

open CategoryTheory Topology
open LinearAlgebraicGroups (Points)
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs
open ConvolutionBundleSpecs ConvolutionFrameQuotientSpecs
open scoped Matrix MatrixGroups

private def jetConstant : JetRing 2 →+* ℂ :=
  Ideal.Quotient.lift _ PowerSeries.constantCoeff (by
    change jetIdeal 2 ≤ RingHom.ker PowerSeries.constantCoeff
    rw [jetIdeal, Ideal.span_le]
    rintro v (rfl : v = t ^ 2)
    simp [RingHom.mem_ker])

private theorem jetConstant_eq (z : JetRing 2) : jetConstant z = jetCoefficients 2 z 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (congrFun PowerSeries.coeff_zero_eq_constantCoeff f).symm

private abbrev jetLinear (z : JetRing 2) : ℂ := jetCoefficients 2 z 1

private theorem jetLinear_mul (z w : JetRing 2) :
    jetLinear (z * w) = jetConstant z * jetLinear w + jetLinear z * jetConstant w := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective w
  change jetLinear (jetReduction 2 (f * g)) =
    jetConstant (jetReduction 2 f) * jetLinear (jetReduction 2 g) +
    jetLinear (jetReduction 2 f) * jetConstant (jetReduction 2 g)
  simp only [jetLinear, jetConstant_eq, jetCoefficients_reduce]
  change PowerSeries.coeff 1 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
    PowerSeries.coeff 1 f * PowerSeries.coeff 0 g
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ (n := 0)]
  simp

private abbrev CMatrix := Matrix (Fin 2) (Fin 2) ℂ
private abbrev JMatrix := Matrix (Fin 2) (Fin 2) (JetRing 2)

private abbrev constantMatrix (A : JMatrix) : CMatrix := A.map jetConstant
private abbrev linearMatrix (A : JMatrix) : CMatrix := A.map jetLinear

private theorem constantMatrix_mul (A B : JMatrix) :
    constantMatrix (A * B) = constantMatrix A * constantMatrix B :=
  jetConstant.mapMatrix.map_mul A B

private theorem linearMatrix_mul (A B : JMatrix) :
    linearMatrix (A * B) = constantMatrix A * linearMatrix B + linearMatrix A * constantMatrix B := by
  ext i j
  change jetCoefficients 2 (∑ k, A i k * B k j) 1 = _
  simp only [map_sum, Finset.sum_apply, jetLinear_mul, Finset.sum_add_distrib,
    Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply]

private theorem continuous_jetConstant : Continuous jetConstant := by
  simp only [funext jetConstant_eq]
  exact (continuous_apply (0 : Fin 2)).comp
    (continuous_induced_dom : Continuous (jetCoefficients 2))

private theorem continuous_jetLinear : Continuous jetLinear :=
  (continuous_apply (1 : Fin 2)).comp
    (continuous_induced_dom : Continuous (jetCoefficients 2))

private theorem continuous_jetMatrixVal : Continuous (fun g : Jets ↦ g.val) :=
  continuous_induced_dom

private theorem continuous_jetMatrix {X : Type} [TopologicalSpace X] (f : X → JMatrix)
    (h₀ : Continuous (fun x ↦ constantMatrix (f x)))
    (h₁ : Continuous (fun x ↦ linearMatrix (f x))) : Continuous f := by
  apply continuous_matrix
  intro i j
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  fin_cases k
  · have hk : (⟨0, by decide⟩ : Fin 2) = 0 := rfl
    exact hk ▸ (by simpa only [Matrix.map_apply, jetConstant_eq, Function.comp_def]
      using h₀.matrix_elem i j)
  · exact h₁.matrix_elem i j

private theorem continuous_constantMatrix : Continuous constantMatrix :=
  continuous_id.matrix_map continuous_jetConstant

private theorem continuous_linearMatrix : Continuous linearMatrix :=
  continuous_id.matrix_map continuous_jetLinear

private def constantUnit (g : Jets) : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map jetConstant g

private theorem constantMatrix_inv (g : Jets) :
    constantMatrix (g⁻¹ : Jets).val = (constantMatrix g.val)⁻¹ :=
  (congrArg Units.val ((Matrix.GeneralLinearGroup.map jetConstant).map_inv g)).trans
    (Matrix.GeneralLinearGroup.coe_inv (constantUnit g))

private theorem linearMatrix_inv (g : Jets) :
    linearMatrix (g⁻¹ : Jets).val =
      -(constantMatrix (g⁻¹ : Jets).val * linearMatrix g.val * constantMatrix (g⁻¹ : Jets).val) := by
  have h₁ : linearMatrix (1 : JMatrix) = 0 := by
    ext i j
    have hone : jetLinear 1 = 0 := by
      change jetLinear (jetReduction 2 1) = 0
      exact (jetCoefficients_reduce 2 1 1).trans (PowerSeries.coeff_one 1)
    change jetLinear (if i = j then 1 else 0) = 0
    by_cases h : i = j
    · rw [ite_eq_left h, hone]
    · rw [ite_eq_right h]
      exact congrFun ((jetCoefficients 2).map_zero) 1
  have h := linearMatrix_mul g.val (g⁻¹ : Jets).val
  rw [g.mul_inv, h₁, eq_comm, add_eq_zero_iff_eq_neg] at h
  have hc := constantMatrix_mul (g⁻¹ : Jets).val g.val
  rw [g.inv_mul, show constantMatrix 1 = 1 from jetConstant.mapMatrix.map_one] at hc
  calc
    linearMatrix (g⁻¹ : Jets).val = constantMatrix (g⁻¹ : Jets).val *
        (constantMatrix g.val * linearMatrix (g⁻¹ : Jets).val) := by
      rw [← mul_assoc, ← hc, one_mul]
    _ = _ := by rw [h, mul_neg, mul_assoc]

/-- Multiplication and inversion are continuous in the two matrix coefficients. -/
private theorem jetsTopologicalGroup : IsTopologicalGroup Jets := by
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply continuous_induced_rng.mpr
    apply continuous_jetMatrix
    · change Continuous (fun p : Jets × Jets ↦ constantMatrix (p.1.val * p.2.val))
      simp only [constantMatrix_mul]
      exact ((continuous_constantMatrix.comp continuous_jetMatrixVal).comp continuous_fst).matrix_mul
        ((continuous_constantMatrix.comp continuous_jetMatrixVal).comp continuous_snd)
    · change Continuous (fun p : Jets × Jets ↦ linearMatrix (p.1.val * p.2.val))
      simp only [linearMatrix_mul]
      exact (((continuous_constantMatrix.comp continuous_jetMatrixVal).comp continuous_fst).matrix_mul
        ((continuous_linearMatrix.comp continuous_jetMatrixVal).comp continuous_snd)).add
        (((continuous_linearMatrix.comp continuous_jetMatrixVal).comp continuous_fst).matrix_mul
          ((continuous_constantMatrix.comp continuous_jetMatrixVal).comp continuous_snd))
  · apply continuous_induced_rng.mpr
    have h₀ : Continuous (fun g : Jets ↦ constantMatrix (g⁻¹ : Jets).val) := by
      simp only [constantMatrix_inv]
      refine continuous_iff_continuousAt.mpr (fun g ↦ ?_)
      have hdet := Matrix.isUnits_det_units (constantUnit g)
      have hc : ContinuousAt (fun g : Jets ↦ constantMatrix g.val) g :=
        (continuous_constantMatrix.comp continuous_jetMatrixVal).continuousAt
      have hinv : ContinuousAt (fun A : CMatrix ↦ A⁻¹) (constantMatrix g.val) := by
        apply continuousAt_matrix_inv
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp hdet)
      exact hinv.comp (f := fun g : Jets ↦ constantMatrix g.val) hc
    apply continuous_jetMatrix _ h₀
    simp only [linearMatrix_inv]
    exact ((h₀.matrix_mul (continuous_linearMatrix.comp continuous_jetMatrixVal)).matrix_mul h₀).neg

open LinearAlgebraicGroups.Specs.GrassmannianCharts (Pivot Inside Outside)
open private truncateJet_self from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle
open private grassmannianChart_isOpenEmbedding windowJetLinear_coords
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
open private continuous_of_columnRange continuous_graphMatrix chartPlane_eq_range
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianIncidenceTopology

/-- A continuous family of linear maps gives a continuous family of image planes
when the image dimension is constant. -/
private theorem continuous_mapped_plane
    {X E F ι κ : Type} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ E) (c : Module.Basis κ ℂ F)
    {d e : ℕ} (hd : d ≤ Module.finrank ℂ E) (he : e ≤ Module.finrank ℂ F)
    (f : X → GrassmannianPoints b hd) (hf : Continuous f)
    (g : X → GrassmannianPoints c he) (T : X → E →ₗ[ℂ] F)
    (hT : Continuous (fun x ↦ (c.equivFun.toLinearMap.comp
      ((T x).comp b.equivFun.symm.toLinearMap)).toMatrix'))
    (hg : ∀ x, grassmannianSubspace c he (g x) =
      (grassmannianSubspace b hd (f x)).map (T x)) : Continuous g := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨I, A, hA⟩ := grassmannianChartPoint_cover b hd (f x)
  let q := grassmannianChartPoint b hd I
  have hq := grassmannianChart_isOpenEmbedding b hd I
  let U := f ⁻¹' Set.range q
  have hU : IsOpen U := hq.isOpen_range.preimage hf
  have hx : x ∈ U := ⟨A, hA⟩
  let a : U → Matrix (Outside I) (Inside I) ℂ :=
    fun y ↦ hq.isEmbedding.toHomeomorph.symm ⟨f y, y.property⟩
  have ha : Continuous a := hq.isEmbedding.toHomeomorph.symm.continuous.comp
    ((hf.comp continuous_subtype_val).subtype_mk _)
  have haq (y : U) : q (a y) = f y :=
    congrArg Subtype.val (hq.isEmbedding.toHomeomorph.apply_symm_apply ⟨f y, y.property⟩)
  apply (continuousWithinAt_iff_continuousAt (hU.mem_nhds hx)).mp
  apply (continuousWithinAt_iff_continuousAt_domRestrict g hx).mpr
  let M (y : U) := (c.equivFun.toLinearMap.comp
    ((T y).comp b.equivFun.symm.toLinearMap)).toMatrix' * graphMatrix I (a y)
  have hM : Continuous M :=
    (hT.comp continuous_subtype_val).matrix_mul ((continuous_graphMatrix I).comp ha)
  apply Continuous.continuousAt
  apply continuous_of_columnRange c he _ M hM
  intro y
  change (grassmannianSubspace c he (g y)).map c.equivFun.toLinearMap = _
  rw [hg, ← haq y, chartPlane_eq_range, ← Submodule.map_comp,
    ← LinearMap.range_comp, Matrix.mulVecLin_mul]
  simp [← Matrix.toLin'_apply', LinearMap.comp_assoc]

private def termLinear (G : JMatrix) : (V × V) →ₗ[ℂ] (V × V) :=
  twoStepCoordinates.toLinearMap.comp
    ((windowJetLinear 0 (le_refl 2) G).comp twoStepCoordinates.symm.toLinearMap)

private theorem termLinear_apply (G : JMatrix) (x y : V) :
    termLinear G (x, y) =
      (constantMatrix G *ᵥ x, constantMatrix G *ᵥ y + linearMatrix G *ᵥ x) := by
  let w := twoStepCoordinates.symm (x, y)
  let z := windowJets 2 0 2 w
  have hz₀ (i : Fin 2) : jetConstant (z i) = x i := by
    rw [jetConstant_eq]
    exact congrFun (congrArg Prod.fst (twoStepCoordinates.apply_symm_apply (x, y))) i
  have hz₁ (i : Fin 2) : jetLinear (z i) = y i :=
    congrFun (congrArg Prod.snd (twoStepCoordinates.apply_symm_apply (x, y))) i
  change twoStepCoordinates (windowJetLinear 0 (le_refl 2) G w) = _
  have hv : windowJets 2 0 2 (windowJetLinear 0 (le_refl 2) G w) = G *ᵥ z := by
    rw [windowJetLinear_coords, truncateJet_self]
    simp [z, Matrix.map_id]
  apply Prod.ext <;> funext i
  · change jetCoefficients 2 (windowJets 2 0 2 (windowJetLinear 0 (le_refl 2) G w) i) 0 = _
    rw [hv, ← jetConstant_eq]
    simp [Matrix.mulVec, dotProduct, hz₀]
  · change jetLinear (windowJets 2 0 2 (windowJetLinear 0 (le_refl 2) G w) i) = _
    rw [hv]
    change jetCoefficients 2 (∑ j, G i j * z j) 1 = _
    simp only [map_sum, Finset.sum_apply, jetLinear_mul, hz₀, hz₁, Finset.sum_add_distrib,
      Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]


private theorem constantJetLinear_eq (g : Jets) :
    constantJetLinear g = Matrix.toLin' (constantMatrix g.val) := by
  apply congrArg Matrix.toLin'
  apply Matrix.ext
  intro i j
  exact (jetConstant_eq _).symm

private theorem constantJetLinear_injective (g : Jets) :
    Function.Injective (constantJetLinear g) := by
  rw [constantJetLinear_eq]
  exact ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ V)
    (Matrix.GeneralLinearGroup.toLin (constantUnit g))).injective

private theorem constantJetLinear_one : constantJetLinear 1 = LinearMap.id := by
  rw [constantJetLinear_eq]
  change Matrix.toLin' (jetConstant.mapMatrix 1) = _
  rw [map_one]
  exact Matrix.toLin'_one

private theorem constantJetLinear_mul (g h : Jets) :
    constantJetLinear (g * h) = (constantJetLinear g).comp (constantJetLinear h) := by
  simp only [constantJetLinear_eq, Matrix.toLin'_apply']
  change (constantMatrix (g.val * h.val)).mulVecLin = _
  rw [constantMatrix_mul, Matrix.mulVecLin_mul]

private def firstJetPoint (g : Jets) (p : ProjectivePoints) : ProjectivePoints :=
  subspacePoint projectiveBasis projectiveRank
    ((firstPlane p).map (constantJetLinear g))
    (((firstPlane p).equivMapOfInjective _ (constantJetLinear_injective g)).finrank_eq.symm.trans
      (grassmannianSubspace_finrank projectiveBasis projectiveRank p))

private theorem firstJetPoint_plane (g : Jets) (p : ProjectivePoints) :
    firstPlane (firstJetPoint g p) = (firstPlane p).map (constantJetLinear g) :=
  subspacePoint_subspace _ _ _ _

@[instance_reducible] private def firstJetAction : MulAction Jets ProjectivePoints where
  smul := firstJetPoint
  one_smul p := by
    apply grassmannianSubspace_injective projectiveBasis projectiveRank
    change firstPlane (firstJetPoint 1 p) = firstPlane p
    rw [firstJetPoint_plane, constantJetLinear_one, Submodule.map_id]
  mul_smul g h p := by
    apply grassmannianSubspace_injective projectiveBasis projectiveRank
    change firstPlane (firstJetPoint (g * h) p) = firstPlane (firstJetPoint g (firstJetPoint h p))
    simp only [firstJetPoint_plane, constantJetLinear_mul, Submodule.map_comp]

private theorem continuous_of_evaluations
    {X E F ι κ : Type} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ E) (c : Module.Basis κ ℂ F)
    (T : X → E →ₗ[ℂ] F) (hT : ∀ v, Continuous fun x ↦ T x v) :
    Continuous (fun x ↦ (c.equivFun.toLinearMap.comp
      ((T x).comp b.equivFun.symm.toLinearMap)).toMatrix') := by
  let := Module.Finite.of_basis c
  apply continuous_matrix
  intro i j
  simp only [LinearMap.toMatrix'_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (continuous_apply i).comp
    (c.equivFun.toLinearMap.continuous_of_finiteDimensional.comp (hT _))

private theorem continuous_termLinear {X : Type} [TopologicalSpace X]
    (G : X → JMatrix) (hG : Continuous G) (v : V × V) :
    Continuous fun x ↦ termLinear (G x) v := by
  have h₀ := continuous_constantMatrix.comp hG
  have h₁ := continuous_linearMatrix.comp hG
  rcases v with ⟨u,v⟩
  simp only [termLinear_apply]
  exact (h₀.matrix_mulVec continuous_const).prodMk
    ((h₀.matrix_mulVec continuous_const).add (h₁.matrix_mulVec continuous_const))

open private firstLine_mem secondSubspace_mem longCoefficients_fst
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle

private theorem firstLine_eq_map (L : GL2Lattice) :
    (latticeSubspace 0 1 L).map constantCoordinates.toLinearMap =
      ((latticeSubspace 0 2 L).map twoStepCoordinates.toLinearMap).map (LinearMap.fst ℂ V V) := by
  ext v
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := (firstLine_mem L v).mp h
    exact ⟨_, (secondSubspace_mem L _).mpr ⟨x, hx, rfl⟩, longCoefficients_fst x⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (secondSubspace_mem L w).mp hw
    exact (firstLine_mem L _).mpr ⟨x, hx, (longCoefficients_fst x).symm⟩

private theorem firstLine_jet (g : Jets) (L M : GL2Lattice)
    (h : latticeSubspace 0 2 M =
      (latticeSubspace 0 2 L).map (windowJetLinear 0 (le_refl 2) g.val)) :
    (latticeSubspace 0 1 M).map constantCoordinates.toLinearMap =
      ((latticeSubspace 0 1 L).map constantCoordinates.toLinearMap).map (constantJetLinear g) := by
  rw [firstLine_eq_map M, firstLine_eq_map L, h]
  simp only [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro w
  have hw := termLinear_apply g.val (twoStepCoordinates w).1 (twoStepCoordinates w).2
  rw [Prod.mk.eta] at hw
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.fst_apply,
    constantJetLinear_eq, Matrix.toLin'_apply]
  simpa only [termLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    using congrArg Prod.fst hw

theorem jetActions : JetActions := by
  obtain ⟨e, he⟩ := ConvolutionBundle.latticeIncidence.2.2
  obtain ⟨A, hA, _⟩ := ConvolutionBundle.flagJetAction
  let B : MulAction Jets ordered := {
    smul g p := e (A.smul g (e.symm p))
    one_smul p := by
      change e (A.smul 1 (e.symm p)) = p
      exact (congrArg e (A.one_smul (e.symm p))).trans (e.apply_symm_apply p)
    mul_smul g h p := by
      change e (A.smul (g * h) (e.symm p)) = e (A.smul g (e.symm (e (A.smul h (e.symm p)))))
      refine (congrArg e (A.mul_smul g h (e.symm p))).trans ?_
      exact congrArg (fun z ↦ e (A.smul g z)) (e.symm_apply_apply _).symm }
  have hcoords (g : Jets) (p : ordered) :
      firstPlane (B.smul g p ≫ ConvolutionBundleSpecs.firstProjection) =
          (firstPlane (p ≫ ConvolutionBundleSpecs.firstProjection)).map (constantJetLinear g) ∧
      secondPlane (B.smul g p ≫ terminalProjection) =
          (secondPlane (p ≫ terminalProjection)).map (twoTermJetLinear g) := by
    have hp := he (e.symm p)
    rw [e.apply_symm_apply] at hp
    change firstPlane (e (A.smul g (e.symm p)) ≫ ConvolutionBundleSpecs.firstProjection) = _ ∧
      secondPlane (e (A.smul g (e.symm p)) ≫ terminalProjection) = _
    constructor
    · rw [(he _).1, hp.1]
      exact firstLine_jet g _ _ (hA g (e.symm p)).1
    · rw [(he _).2, hp.2, (hA g (e.symm p)).2]
      simp only [← Submodule.map_comp, twoTermJetLinear, LinearMap.comp_assoc,
        LinearEquiv.symm_comp, LinearMap.comp_id]
  have hI : Continuous incidenceCoordinates := continuous_induced_dom
  refine ⟨jetsTopologicalGroup, firstJetAction, B, ?_, ?_, firstJetPoint_plane, ?_⟩
  · apply continuous_mapped_plane projectiveBasis projectiveBasis projectiveRank projectiveRank
      Prod.snd continuous_snd _ (fun z ↦ constantJetLinear z.1)
    · apply continuous_of_evaluations
      intro v
      simp only [constantJetLinear_eq, Matrix.toLin'_apply]
      exact ((continuous_constantMatrix.comp continuous_jetMatrixVal).comp continuous_fst).matrix_mulVec
        continuous_const
    · exact fun z ↦ firstJetPoint_plane z.1 z.2
  · apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · apply continuous_mapped_plane projectiveBasis projectiveBasis projectiveRank projectiveRank
        (fun z : Jets × ordered ↦ z.2 ≫ ConvolutionBundleSpecs.firstProjection)
        ((continuous_fst.comp hI).comp continuous_snd) _ (fun z ↦ constantJetLinear z.1)
      · apply continuous_of_evaluations
        intro v
        simp only [constantJetLinear_eq, Matrix.toLin'_apply]
        exact ((continuous_constantMatrix.comp continuous_jetMatrixVal).comp continuous_fst).matrix_mulVec
          continuous_const
      · exact fun z ↦ (hcoords z.1 z.2).1
    · apply continuous_mapped_plane twoStepBasis twoStepBasis twoStepRank twoStepRank
        (fun z : Jets × ordered ↦ z.2 ≫ terminalProjection ≫ twoStepSchemeInGrassmannian)
        ((continuous_snd.comp hI).comp continuous_snd) _ (fun z ↦ twoTermJetLinear z.1)
      · apply continuous_of_evaluations
        exact continuous_termLinear _ (continuous_jetMatrixVal.comp continuous_fst)
      · exact fun z ↦ (hcoords z.1 z.2).2
  · intro g p
    refine ⟨grassmannianSubspace_injective projectiveBasis projectiveRank ?_, (hcoords g p).2⟩
    exact (hcoords g p).1.trans (firstJetPoint_plane _ _).symm

open private standard_eq_scalar_zero loop_smul_val shifted_zero_apply
  longCoefficients stdQ stdQ_surjective windowJets_stdQ secondSubspace_first std_transport fixed_of_coset_eq
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle

private abbrev IntegralMatrix := Matrix (Fin 2) (Fin 2) O
private abbrev Standard := (scalarLattice 2 0).val

private theorem integral_frame (g : Loop) (hg : (g • standardLattice 2).val ≤ Standard) :
    ∃ G : IntegralMatrix, G.map inclusion = g.val := by
  have h (j : Fin 2) : g.val.col j ∈ Standard := by
    apply hg
    rw [loop_smul_val]
    refine ⟨Pi.single j 1, ?_, ?_⟩
    · change Pi.single j 1 ∈ (coordinateInclusion 2).range
      refine ⟨Pi.single j 1, ?_⟩
      ext i
      by_cases hi : i = j <;> simp [coordinateInclusion, hi]
    · change g.val *ᵥ Pi.single j 1 = g.val.col j
      rw [Matrix.mulVec_single_one]
  let G : IntegralMatrix := Matrix.of (fun i j ↦ ((shiftedCoordinates 2 0).symm ⟨g.val.col j, h j⟩) i)
  refine ⟨G, Matrix.ext fun i j ↦ ?_⟩
  have hj := congrArg (fun x : Standard ↦ x.val i)
    ((shiftedCoordinates 2 0).apply_symm_apply ⟨g.val.col j, h j⟩)
  change inclusion (((shiftedCoordinates 2 0).symm ⟨g.val.col j, h j⟩) i) = g.val i j
  rw [shiftedCoordinates_coe, shifted_zero_apply] at hj
  exact hj

private abbrev integralJet (G : IntegralMatrix) : JMatrix := G.map (jetReduction 2).toRingHom

private abbrev shortWindowPoint (x : Fin 2 → O) := stdQ 2 (shiftedCoordinates 2 0 x)

set_option maxRecDepth 1500 in
private theorem longCoefficients_mulVec (G : IntegralMatrix) (x : Fin 2 → O) :
    longCoefficients (shiftedCoordinates 2 0 (G *ᵥ x)) =
      termLinear (integralJet G) (longCoefficients (shiftedCoordinates 2 0 x)) := by
  change twoStepCoordinates (shortWindowPoint (G *ᵥ x)) =
    termLinear (integralJet G) (twoStepCoordinates (shortWindowPoint x))
  simp only [termLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  apply congrArg twoStepCoordinates
  apply (windowJets 2 0 2).injective
  rw [windowJetLinear_coords, truncateJet_self,
    show (⇑(RingHom.id (JetRing 2))) = id from rfl, Matrix.map_id]
  simp only [shortWindowPoint, windowJets_stdQ, windowReduction, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact funext ((jetReduction 2).toRingHom.map_mulVec G x)

set_option maxRecDepth 1500 in
/-- Reduction of a lattice transformed by an integral frame is the image under
the frame's truncated matrix. The matrix need not be invertible modulo t². -/
private theorem frame_second_map (g : Loop) (G : IntegralMatrix) (hG : G.map inclusion = g.val)
    (L : GL2Lattice) (hL : L.val ≤ Standard) :
    (latticeSubspace 0 2 (g • L)).map twoStepCoordinates.toLinearMap =
      ((latticeSubspace 0 2 L).map twoStepCoordinates.toLinearMap).map (termLinear (integralJet G)) := by
  have hmul (x : Fin 2 → O) :
      loopLinearEquiv 2 g (shiftedCoordinates 2 0 x).val =
        (shiftedCoordinates 2 0 (G *ᵥ x)).val := by
    simp only [shiftedCoordinates_coe, shifted_zero_apply, loopLinearEquiv_apply, ← hG]
    exact (funext (inclusion.map_mulVec G x)).symm
  ext w
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := (secondSubspace_mem (g • L) w).mp h
    rw [loop_smul_val] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨z, hz⟩ := (shiftedCoordinates 2 0).surjective ⟨x, hL hx⟩
    have hzx : (shiftedCoordinates 2 0 z).val = x := congrArg Subtype.val hz
    refine ⟨longCoefficients (shiftedCoordinates 2 0 z),
      (secondSubspace_mem L _).mpr ⟨_, hzx ▸ hx, rfl⟩, ?_⟩
    rw [← longCoefficients_mulVec]
    apply congrArg longCoefficients
    apply Subtype.ext
    rw [← hmul, hzx]
    exact hxy
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (secondSubspace_mem L w).mp hw
    obtain ⟨z, rfl⟩ := (shiftedCoordinates 2 0).surjective x
    apply (secondSubspace_mem (g • L) _).mpr
    exact ⟨_, ⟨_, hx, hmul z⟩, longCoefficients_mulVec G z⟩

private theorem frame_first_map (g : Loop) (G : IntegralMatrix) (hG : G.map inclusion = g.val) :
    (latticeSubspace 0 1 (g • standardLattice 2)).map constantCoordinates.toLinearMap =
      (constantMatrix (integralJet G)).mulVecLin.range := by
  rw [firstLine_eq_map, frame_second_map _ _ hG _ (by rw [standard_eq_scalar_zero]),
    ← Submodule.map_comp]
  have htop : (latticeSubspace 0 2 (standardLattice 2)).map twoStepCoordinates.toLinearMap = ⊤ := by
    rw [standard_eq_scalar_zero]
    apply top_le_iff.mp
    intro w _
    obtain ⟨x, rfl⟩ := twoStepCoordinates.surjective w
    obtain ⟨y, rfl⟩ := stdQ_surjective 2 x
    exact (secondSubspace_mem (scalarLattice 2 0) _).mpr ⟨y, y.property, rfl⟩
  rw [htop, Submodule.map_top]
  have hc : (LinearMap.fst ℂ V V).comp (termLinear (integralJet G)) =
      (constantMatrix (integralJet G)).mulVecLin.comp (LinearMap.fst ℂ V V) := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact congrArg Prod.fst (termLinear_apply _ x y)
  rw [hc, LinearMap.range_comp, Submodule.range_fst, Submodule.map_top]

private theorem representative_loop_colength (p : FrameRepresentative) :
    p.val.1 • standardLattice 2 ∈ colength 1 := by
  obtain ⟨g, hg, hcol⟩ := p.property.1
  rwa [← fixed_of_coset_eq hg]

private def integralRepresentative (p : FrameRepresentative) : IntegralMatrix :=
  (integral_frame p.val.1 (representative_loop_colength p).1).choose

private theorem integralRepresentative_eq (p : FrameRepresentative) :
    (integralRepresentative p).map inclusion = p.val.1.val :=
  (integral_frame p.val.1 (representative_loop_colength p).1).choose_spec

private theorem integralJet_coeff (p : FrameRepresentative) (i j k : Fin 2) :
    jetCoefficients 2 (integralJet (integralRepresentative p) i j) k =
      (p.val.1.val i j).coeff (k.val : ℤ) := by
  rw [← integralRepresentative_eq p]
  exact (LaurentSeries.coeff_coe_powerSeries (integralRepresentative p i j) k.val).symm

private theorem continuous_integralJet :
    Continuous (fun p : FrameRepresentative ↦ integralJet (integralRepresentative p)) := by
  have hc : Continuous representativeCoordinates := continuous_induced_dom
  apply continuous_matrix
  intro i j
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  change Continuous (fun p : FrameRepresentative ↦
    jetCoefficients 2 (integralJet (integralRepresentative p) i j) k)
  simp only [integralJet_coeff]
  exact (continuous_apply k).comp
    ((continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp hc)))


private abbrev ThreePlaneRank : 3 ≤ Module.finrank ℂ (V × V) := by
  simp [V, Module.finrank_prod]

private def extendedFirst (p : ProjectivePoints) : GrassmannianPoints twoStepBasis ThreePlaneRank :=
  subspacePoint twoStepBasis ThreePlaneRank ((firstPlane p).prod ⊤) (by
    rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, finrank_top]
    change Module.finrank ℂ (grassmannianSubspace projectiveBasis projectiveRank p) + _ = 3
    rw [grassmannianSubspace_finrank]
    simp [V])

private theorem extendedFirst_plane (p : ProjectivePoints) :
    grassmannianSubspace twoStepBasis ThreePlaneRank (extendedFirst p) = (firstPlane p).prod ⊤ :=
  subspacePoint_subspace _ _ _ _

private theorem continuous_extendedFirst : Continuous extendedFirst := by
  let e : (V × V) ≃ₗ[ℂ] V × (V × (Fin 0 → ℂ)) :=
    (LinearEquiv.refl ℂ V).prodCongr ((LinearEquiv.prodUnique : (V × (Fin 0 → ℂ)) ≃ₗ[ℂ] V)).symm
  have hdim : 3 = 1 + Module.finrank ℂ V := by simp [V]
  refine (GrassmannianIncidenceTopology.incidenceClosedEmbedding projectiveBasis twoStepBasis e
    projectiveRank ThreePlaneRank hdim extendedFirst ?_).1.continuous
  intro p w
  rw [extendedFirst_plane]
  have hz : (e w).2.2 = 0 := Subsingleton.elim _ _
  simp only [Submodule.mem_prod, Submodule.mem_top, and_true, hz]
  rfl

private theorem continuous_representative_to_ordered (q : FrameRepresentative → ordered)
    (hq : ∀ p,
      firstPlane (q p ≫ ConvolutionBundleSpecs.firstProjection) =
        (latticeSubspace 0 1 (p.val.1 • standardLattice 2)).map constantCoordinates.toLinearMap ∧
      secondPlane (q p ≫ terminalProjection) =
        (latticeSubspace 0 2 (p.val.1 • p.val.2)).map twoStepCoordinates.toLinearMap) :
    Continuous q := by
  classical
  let G (p : FrameRepresentative) := integralJet (integralRepresentative p)
  have hG : Continuous G := continuous_integralJet
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · let T := projectiveBasis.equivFun.toLinearMap
    let M (p : FrameRepresentative) := T.toMatrix' * constantMatrix (G p)
    have hM : Continuous M := continuous_const.matrix_mul (continuous_constantMatrix.comp hG)
    apply continuous_of_columnRange projectiveBasis projectiveRank _ M hM
    intro p
    change (firstPlane (q p ≫ ConvolutionBundleSpecs.firstProjection)).map T = _
    rw [(hq p).1, frame_first_map _ _ (integralRepresentative_eq p), ← LinearMap.range_comp]
    simp only [M, G, Matrix.mulVecLin_mul, ← Matrix.toLin'_apply' T.toMatrix', Matrix.toLin'_toMatrix']
  · obtain ⟨e, he, _⟩ := MinusculeAndTwoStep.minusculeProjective.1
    let f (p : FrameRepresentative) := extendedFirst (e (representedSecondStage p))
    have hf : Continuous f :=
      continuous_extendedFirst.comp (e.continuous.comp
        (continuous_snd.comp (continuous_induced_dom : Continuous representativeCoordinates)))
    apply continuous_mapped_plane twoStepBasis twoStepBasis ThreePlaneRank twoStepRank f hf _
      (fun p ↦ termLinear (G p))
    · exact continuous_of_evaluations twoStepBasis twoStepBasis _ (continuous_termLinear G hG)
    · intro p
      change secondPlane (q p ≫ terminalProjection) =
        (grassmannianSubspace twoStepBasis ThreePlaneRank (f p)).map (termLinear (G p))
      rw [(hq p).2, frame_second_map _ _ (integralRepresentative_eq p) _
        (show p.val.2.val ≤ Standard from (representedSecondStage p).property.1)]
      congr 1
      rw [show grassmannianSubspace twoStepBasis ThreePlaneRank (f p) =
        (firstPlane (e (representedSecondStage p))).prod ⊤ from extendedFirst_plane _]
      change (latticeSubspace 0 2 (representedSecondStage p).val).map twoStepCoordinates.toLinearMap = _
      exact (secondSubspace_first MinusculeAndTwoStep.minusculeOrbit (representedSecondStage p)).trans
        (congrArg (fun S : Submodule ℂ V ↦ S.prod ⊤) (he (representedSecondStage p)).symm)


private abbrev D₀ : CMatrix := Matrix.diagonal ![0, 1]
private abbrev D₁ : CMatrix := Matrix.diagonal ![1, 0]
private abbrev D : IntegralMatrix := Matrix.diagonal ![t, 1]

private def constantLift (b : GL (Fin 2) ℂ) : Positive :=
  Matrix.GeneralLinearGroup.map PowerSeries.C b

private def chartFrame (b : GL (Fin 2) ℂ) : Loop :=
  positiveGLMap 2 (constantLift b) * diagonalLoop 2 (pairCoweight minusculePair)

private abbrev chartIntegral (B : CMatrix) : IntegralMatrix := B.map PowerSeries.C * D

private theorem chartFrame_integral (b : GL (Fin 2) ℂ) :
    (chartIntegral b.val).map inclusion = (chartFrame b).val := by
  change _ = (b.val.map PowerSeries.C).map inclusion *
    (diagonalLoop 2 (pairCoweight minusculePair)).val
  rw [Matrix.map_mul]
  congr 1
  apply Matrix.ext
  intro i j
  change inclusion (D i j) = (Matrix.diagonal (fun k ↦ monomial (pairCoweight minusculePair k))) i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    fin_cases i
    · change inclusion t = monomial 1
      rw [monomial_eq_zpow, zpow_one]
    · exact (monomial_nat 0).symm
  · simp [D, Matrix.diagonal_apply_ne _ h]

private theorem chartFrame_colength (b : GL (Fin 2) ℂ) :
    chartFrame b • standardLattice 2 ∈ colength 1 := by
  rw [MinusculeAndTwoStep.minusculeOrbit.1]
  refine ⟨⟨_, constantLift b, rfl⟩, ?_⟩
  change positiveGLMap 2 (constantLift b) • diagonalLattice (pairCoweight minusculePair) =
    chartFrame b • standardLattice 2
  rw [chartFrame, mul_smul, diagonalLoop_smul_standard]

private theorem chartIntegral_coefficients (B : CMatrix) :
    constantMatrix (integralJet (chartIntegral B)) = B * D₀ ∧
      linearMatrix (integralJet (chartIntegral B)) = B * D₁ := by
  have hmul (i j : Fin 2) : chartIntegral B i j = PowerSeries.C (B i j) * ![t, 1] j :=
    Matrix.mul_diagonal _ _ _ _
  constructor <;> apply Matrix.ext <;> intro i j
  · change jetConstant (jetReduction 2 (chartIntegral B i j)) = _
    rw [jetConstant_eq, jetCoefficients_reduce, hmul, Matrix.mul_diagonal]
    fin_cases j <;> simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  · change jetLinear (jetReduction 2 (chartIntegral B i j)) = _
    simp only [jetLinear, jetCoefficients_reduce]
    rw [hmul, Matrix.mul_diagonal]
    fin_cases j <;> simp

private theorem continuous_chartFrame_coefficients {X : Type} [TopologicalSpace X]
    (b : X → GL (Fin 2) ℂ) (hb : Continuous fun x ↦ (b x).val) :
    Continuous (fun x i j (k : Fin 2) ↦ ((chartFrame (b x)).val i j).coeff (k.val : ℤ)) := by
  have hcoeff (x : X) (i j k : Fin 2) :
      ((chartFrame (b x)).val i j).coeff (k.val : ℤ) =
        jetCoefficients 2 (integralJet (chartIntegral (b x).val) i j) k := by
    rw [← chartFrame_integral]
    exact LaurentSeries.coeff_coe_powerSeries _ _
  simp only [hcoeff]
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro k
  fin_cases k
  · change Continuous (fun x ↦ jetCoefficients 2 (integralJet (chartIntegral (b x).val) i j) 0)
    simp only [← jetConstant_eq]
    exact ((hb.matrix_mul continuous_const).matrix_elem i j).congr
      (fun x ↦ (congrFun (congrFun (chartIntegral_coefficients (b x).val).1 i) j).symm)
  · change Continuous (fun x ↦ jetLinear (integralJet (chartIntegral (b x).val) i j))
    exact ((hb.matrix_mul continuous_const).matrix_elem i j).congr
      (fun x ↦ (congrFun (congrFun (chartIntegral_coefficients (b x).val).2 i) j).symm)

/-- In the basis with frame matrix B diag(t, 1), the constant coordinates in
the original standard lattice are the second entry of B⁻¹x and the first entry
of B⁻¹y, put back in their original order. -/
private def relativeLineMap (B : CMatrix) : (V × V) →ₗ[ℂ] V :=
  ((D₀ * B⁻¹).mulVecLin.comp (LinearMap.fst ℂ V V)) +
    ((D₁ * B⁻¹).mulVecLin.comp (LinearMap.snd ℂ V V))

private theorem relativeLineMap_chart (b : GL (Fin 2) ℂ) :
    (relativeLineMap b.val).comp (termLinear (integralJet (chartIntegral b.val))) =
      LinearMap.fst ℂ V V := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hi := Matrix.nonsing_inv_mul b.val (Matrix.isUnits_det_units b)
  have hc := chartIntegral_coefficients b.val
  simp only [LinearMap.comp_apply, termLinear_apply, hc.1, hc.2, relativeLineMap,
    LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_add, Matrix.mulVec_mulVec]
  have h₀ : D₀ * b.val⁻¹ * (b.val * D₀) = D₀ := by
    rw [mul_assoc, ← mul_assoc b.val⁻¹, hi, one_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [D₀, Matrix.mul_diagonal]
  have h₁ : D₁ * b.val⁻¹ * (b.val * D₀) = 0 := by
    rw [mul_assoc, ← mul_assoc b.val⁻¹, hi, one_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [D₀, D₁, Matrix.mul_diagonal]
  have h₂ : D₁ * b.val⁻¹ * (b.val * D₁) = D₁ := by
    rw [mul_assoc, ← mul_assoc b.val⁻¹, hi, one_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [D₁, Matrix.mul_diagonal]
  rw [h₀, h₁, h₂, Matrix.zero_mulVec, zero_add]
  rw [← Matrix.add_mulVec, show D₀ + D₁ = 1 by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [D₀, D₁]]
  exact Matrix.one_mulVec x

private theorem continuous_relativeLineMap {X : Type} [TopologicalSpace X]
    (b : X → GL (Fin 2) ℂ) (hb : Continuous fun x ↦ (b x).val) (v : V × V) :
    Continuous fun x ↦ relativeLineMap (b x).val v := by
  have hi : Continuous (fun x ↦ ((b x).val : CMatrix)⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro x
    have h : ContinuousAt (fun B : CMatrix ↦ B⁻¹) (b x).val := by
      apply continuousAt_matrix_inv
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (b x).det_ne_zero
    exact h.comp (f := fun x ↦ (b x).val) hb.continuousAt
  exact ((continuous_const.matrix_mul hi).matrix_mulVec continuous_const).add
    ((continuous_const.matrix_mul hi).matrix_mulVec continuous_const)


private theorem projectiveBasis_coordinate (v : V) (i : Fin 2 × Fin 1) :
    projectiveBasis.equivFun v i = v i.1 := by
  rw [show projectiveBasis.equivFun = constantCoordinates.symm ≪≫ₗ windowCoordinates 2 0 1 by
    apply LinearEquiv.ext
    intro x
    funext j
    simp only [projectiveBasis, Module.Basis.equivFun_apply, Module.Basis.map_repr,
      LinearEquiv.trans_apply, windowBasis, Module.Basis.ofEquivFun_repr_apply]]
  rw [LinearEquiv.trans_apply]
  rw [show i = (i.1, 0) from Prod.ext rfl (Subsingleton.elim _ _)]
  change constantCoordinates (constantCoordinates.symm v) i.1 = _
  rw [LinearEquiv.apply_symm_apply]

private theorem chartFrames (I : Pivot (Fin 2 × Fin 1) 1) :
    ∃ b : Matrix (Outside I) (Inside I) ℂ → GL (Fin 2) ℂ,
      Continuous (fun a ↦ (b a).val) ∧
      ∀ a, firstPlane (grassmannianChartPoint projectiveBasis projectiveRank I a) =
        (((b a).val : CMatrix) * D₀).mulVecLin.range := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp I.property
  let j : Inside I := ⟨i, hi.symm ▸ Finset.mem_singleton_self i⟩
  have huniq (k : Inside I) : k = j := Subtype.ext (Finset.mem_singleton.mp (hi ▸ k.property))
  let v (a : Matrix (Outside I) (Inside I) ℂ) : V :=
    projectiveBasis.equivFun.symm (graphMatrix I a *ᵥ (fun _ ↦ 1))
  have hv : Continuous v :=
    projectiveBasis.equivFun.symm.toLinearMap.continuous_of_finiteDimensional.comp
      ((continuous_graphMatrix I).matrix_mulVec continuous_const)
  have hvj (a) : v a i.1 = 1 := by
    rw [← projectiveBasis_coordinate (v a) i]
    change projectiveBasis.equivFun (projectiveBasis.equivFun.symm
      (graphMatrix I a *ᵥ (fun _ ↦ 1))) j.val = 1
    rw [LinearEquiv.apply_symm_apply]
    exact graphMatrix_inside I a _ j
  let B (a : Matrix (Outside I) (Inside I) ℂ) : CMatrix :=
    Matrix.of fun k l ↦ if l = 1 then v a k else if k = i.1 then 0 else 1
  have hB : Continuous B := by
    apply continuous_matrix
    intro k l
    by_cases hl : l = 1
    · simpa only [B, Matrix.of_apply, hl, ite_true, Function.comp_def] using (continuous_apply k).comp hv
    · simpa only [B, Matrix.of_apply, hl, ite_false] using
        (continuous_const : Continuous fun _ : Matrix (Outside I) (Inside I) ℂ ↦
          if k = i.1 then (0 : ℂ) else 1)
  have hBdet (a) : IsUnit (B a).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_fin_two]
    by_cases hi₀ : i.1 = 0
    · have hn : v a 0 = 1 := hi₀ ▸ hvj a
      simp [B, hi₀, hn]
    · have hi₁ : i.1 = 1 := by omega
      have hn : v a 1 = 1 := hi₁ ▸ hvj a
      simp [B, hi₁, hn]
  let b (a : Matrix (Outside I) (Inside I) ℂ) := Matrix.GeneralLinearGroup.mk'' (B a) (hBdet a)
  refine ⟨b, hB, ?_⟩
  intro a
  have hmul (x : V) : ((B a) * D₀) *ᵥ x = x 1 • v a := by
    funext k
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_diagonal, D₀, B, mul_comm]
  change grassmannianSubspace projectiveBasis projectiveRank
    (grassmannianChartPoint projectiveBasis projectiveRank I a) = ((B a) * D₀).mulVecLin.range
  rw [chartPlane_eq_range]
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Pi.single 1 (u j), ?_⟩
    rw [Matrix.mulVecLin_apply, hmul, Pi.single_eq_same]
    have hu : u = u j • (fun _ ↦ (1 : ℂ)) := by
      funext k
      rw [huniq k]
      simp
    rw [hu]
    simp [v]
  · rintro ⟨u, rfl⟩
    rw [Matrix.mulVecLin_apply, hmul]
    exact ⟨u 1 • (fun _ ↦ 1), by simp [v]⟩


private theorem isQuotientMap_of_localSections {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (q : X → Y) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hlocal : ∀ y : Y, ∃ (U : Set Y), IsOpen U ∧ y ∈ U ∧
      ∃ s : U → X, Continuous s ∧ ∀ z : U, q (s z) = z.val) : IsQuotientMap q := by
  refine ⟨isCoinducing_iff.mpr ?_, hsurj⟩
  intro S
  refine ⟨?_, fun hS ↦ hS.preimage hq⟩
  intro hS
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨U, hU, hyU, s, hs, hqs⟩ := hlocal y
  let W := s ⁻¹' (q ⁻¹' S)
  have hW : IsOpen W := hS.preimage hs
  let V := (Subtype.val : U → Y) '' W
  have hV : IsOpen V := hU.isOpenEmbedding_subtypeVal.isOpenMap W hW
  have hyV : y ∈ V := ⟨⟨y, hyU⟩, by change q (s ⟨y, hyU⟩) ∈ S; rwa [hqs], rfl⟩
  refine Filter.mem_of_superset (hV.mem_nhds hyV) ?_
  rintro _ ⟨z, hz, rfl⟩
  change q (s z) ∈ S at hz
  rwa [hqs] at hz

set_option maxHeartbeats 800000 in
/-- A pivot chart on the first line supplies a continuous local choice of frame
and hence a local section of the representative map. -/
private theorem frameLocalSections
    (e : Flags ≃ₜ Points incidenceScheme complexAlgebra)
    (he : ∀ L : Flags,
      firstPlane (e L ≫ ConvolutionBundleSpecs.firstProjection) =
        (latticeSubspace 0 1 L.val.1).map constantCoordinates.toLinearMap ∧
      secondPlane (e L ≫ terminalProjection) =
        (latticeSubspace 0 2 L.val.2).map twoStepCoordinates.toLinearMap)
    (q : FrameRepresentative → ordered)
    (hq : ∀ p, (e.symm (q p)).val = (p.val.1 • standardLattice 2, p.val.1 • p.val.2)) :
    ∀ y : ordered, ∃ (U : Set ordered), IsOpen U ∧ y ∈ U ∧
      ∃ s : U → FrameRepresentative, Continuous s ∧ ∀ z : U, q (s z) = z.val := by
  classical
  intro y
  let f (p : ordered) : ProjectivePoints := p ≫ ConvolutionBundleSpecs.firstProjection
  have hI : Continuous incidenceCoordinates := continuous_induced_dom
  have hf : Continuous f := continuous_fst.comp hI
  obtain ⟨I, a₀, ha₀⟩ := grassmannianChartPoint_cover projectiveBasis projectiveRank (f y)
  let c := grassmannianChartPoint projectiveBasis projectiveRank I
  let hc := grassmannianChart_isOpenEmbedding projectiveBasis projectiveRank I
  let U := f ⁻¹' Set.range c
  have hU : IsOpen U := hc.isOpen_range.preimage hf
  have hyU : y ∈ U := ⟨a₀, ha₀⟩
  let a (z : U) := hc.isEmbedding.toHomeomorph.symm ⟨f z.val, z.property⟩
  have ha : Continuous a := hc.isEmbedding.toHomeomorph.symm.continuous.comp
    ((hf.comp continuous_subtype_val).subtype_mk _)
  have hca (z : U) : c (a z) = f z.val :=
    congrArg Subtype.val (hc.isEmbedding.toHomeomorph.apply_symm_apply ⟨f z.val, z.property⟩)
  obtain ⟨b, hb, hbc⟩ := chartFrames I
  obtain ⟨m, hm, _⟩ := MinusculeAndTwoStep.minusculeProjective.1
  let g (z : U) := chartFrame (b (a z))
  let F (z : U) := e.symm z.val
  have h₁ (z : U) : g z • standardLattice 2 = (F z).val.1 := by
    have hfz := (he (F z)).1
    rw [show e (F z) = z.val from e.apply_symm_apply z.val] at hfz
    have hplane : (latticeSubspace 0 1 (g z • standardLattice 2)).map constantCoordinates.toLinearMap =
        (latticeSubspace 0 1 (F z).val.1).map constantCoordinates.toLinearMap := by
      rw [frame_first_map _ _ (chartFrame_integral (b (a z))),
        (chartIntegral_coefficients (b (a z)).val).1, ← hbc]
      change firstPlane (c (a z)) = _
      rw [hca]
      exact hfz
    have heq : m ⟨g z • standardLattice 2, chartFrame_colength _⟩ =
        m ⟨(F z).val.1, (F z).property.1⟩ := by
      apply grassmannianSubspace_injective projectiveBasis projectiveRank
      rw [hm, hm]
      exact hplane
    exact congrArg Subtype.val (m.injective heq)
  let L (z : U) := (g z)⁻¹ • (F z).val.2
  have h₂ (z : U) : g z • L z = (F z).val.2 := smul_inv_smul _ _
  have hL (z : U) : L z ∈ colength 1 := (std_transport (g z) (L z) 1).mp (by
    rw [h₁, h₂]
    exact (F z).property.2)
  let s (z : U) : FrameRepresentative :=
    ⟨(g z, L z), ⟨g z, rfl, chartFrame_colength _⟩, hL z⟩
  have hs (z : U) : q (s z) = z.val := by
    apply e.symm.injective
    apply Subtype.ext
    exact (hq (s z)).trans (Prod.ext (h₁ z) (h₂ z))
  refine ⟨U, hU, hyU, s, ?_, hs⟩
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · exact continuous_chartFrame_coefficients (b ∘ a) (hb.comp ha)
  · have hsecond : Continuous (fun z : U ↦ z.val ≫ terminalProjection ≫ twoStepSchemeInGrassmannian) :=
      (continuous_snd.comp hI).comp continuous_subtype_val
    have hmL : Continuous (fun z : U ↦ m (representedSecondStage (s z))) := by
      apply continuous_mapped_plane twoStepBasis projectiveBasis twoStepRank projectiveRank
        _ hsecond _ (fun z ↦ relativeLineMap (b (a z)).val)
      · apply continuous_of_evaluations
        exact continuous_relativeLineMap (b ∘ a) (hb.comp ha)
      · intro z
        change firstPlane (m (representedSecondStage (s z))) =
          (secondPlane (z.val ≫ terminalProjection)).map (relativeLineMap (b (a z)).val)
        have hfz := (he (F z)).2
        rw [show e (F z) = z.val from e.apply_symm_apply z.val, ← h₂ z] at hfz
        have hbnd : (L z).val ≤ Standard := (hL z).1
        rw [hfz, frame_second_map _ _ (chartFrame_integral (b (a z))) _ hbnd,
          ← Submodule.map_comp, relativeLineMap_chart]
        exact (hm (representedSecondStage (s z))).trans (firstLine_eq_map (L z))
    have hmL' := m.symm.continuous.comp hmL
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hmL'

theorem frameQuotient : FrameQuotient := by
  obtain ⟨h, E, hE, _⟩ := ConvolutionBundle.twistedFlags
  obtain ⟨e, he⟩ := ConvolutionBundle.latticeIncidence.2.2
  obtain ⟨m, hm, _⟩ := MinusculeAndTwoStep.minusculeProjective.1
  let Q : OrderedProduct h ≃ ordered := E.trans e.toEquiv
  let q (p : FrameRepresentative) := Q (Quotient.mk _ p)
  have hvals (p : FrameRepresentative) :
      (e.symm (q p)).val = (p.val.1 • standardLattice 2, p.val.1 • p.val.2) := by
    change (e.symm (e (E (Quotient.mk _ p)))).val = _
    rw [Homeomorph.symm_apply_apply, hE]
  have hcoords (p : FrameRepresentative) :
      firstPlane (q p ≫ ConvolutionBundleSpecs.firstProjection) =
        (latticeSubspace 0 1 (p.val.1 • standardLattice 2)).map constantCoordinates.toLinearMap ∧
      secondPlane (q p ≫ terminalProjection) =
        (latticeSubspace 0 2 (p.val.1 • p.val.2)).map twoStepCoordinates.toLinearMap := by
    have hp := he (e.symm (q p))
    rw [e.apply_symm_apply, hvals] at hp
    exact hp
  have hc := continuous_representative_to_ordered q hcoords
  have hsurj : Function.Surjective q := Q.surjective.comp Quotient.mk_surjective
  have hq : IsQuotientMap q :=
    isQuotientMap_of_localSections q hc hsurj (frameLocalSections e he q hvals)
  let b : representativeSpace ⟶ minuscule := TopCat.ofHom
    ⟨fun p ↦ m (representedSecondStage p), m.continuous.comp
      (continuous_snd.comp (continuous_induced_dom : Continuous representativeCoordinates))⟩
  exact ⟨h, Q, b, TopCat.ofHom ⟨q, hc⟩, hq,
    fun p ↦ ⟨rfl, (hcoords p).1, hm (representedSecondStage p), (hcoords p).2⟩⟩

end

end RepTheorySurvey.Geometric.ConvolutionFrameQuotient
