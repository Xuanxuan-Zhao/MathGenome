import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterDynamics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.Parabolics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Filter IsDedekindDomain Topology UniformSpace
open scoped Matrix LaurentPolynomial NumberField
open LinearAlgebraicGroups.Specs hiding coordinateMap

universe u v

namespace LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation

open AdelicGroups
open LinearAlgebraicGroups.CocharacterDynamics
open Specs.Arithmetic.LocalCocharacterEvaluation
open Specs.AdjointRepresentation (conjugate GroupPoints TangentCoordinates)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralModels (MatrixRealization)
open Specs.StandardGroups (generalLinearPoints)
open Specs.Unipotent (baseChangedAlgebraicGroup Index)

open private matrixPresentation continuous_glEvaluation glVal_isEmbedding
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private coordinateMap coordinateMap_spec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private radicalIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private conjugationEnd conjugationLinear conjugationLinear_spec conjugationTransformation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.AdjointRepresentation
open private unitPointHom evalLaurent orbit_eval
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

private abbrev BF (F : Type u) [Field F] := CommAlgCat.of F F

private def scalarPointsIso {k F : Type u} [Field k] [Field F] [Algebra k F]
    (G : GroupScheme k) :
    (groupPointsFunctor F).obj ((groupBaseChange k F).obj G) ≅
      restrictTestAlgebra k F ⋙ (groupPointsFunctor k).obj G :=
  NatIso.ofComponents (fun R ↦ (baseChangePointGroupEquiv F G R).toGrpIso) (by
    intro R S a
    apply GrpCat.ext
    intro p
    exact baseChangePointsNaturality k F G.X a p)

private def scalarMatrixIso {k F : Type u} [Field k] [Field F] [Algebra k F]
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    (restrictTestAlgebra k F) ⋙ generalLinearPoints k ι ≅ generalLinearPoints F ι :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)

theorem completionPointTopology : CompletionPointTopology.{u} := by
  intro k F _ _ _ _ G i
  let j : MatrixRealization (baseChangedAlgebraicGroup F G) :=
    { size := i.size
      ambient := baseChangedAlgebraicGroup F i.ambient
      matrix := scalarPointsIso i.ambient.val ≪≫
        Functor.isoWhiskerLeft (restrictTestAlgebra k F) i.matrix ≪≫
        scalarMatrixIso (Index.{u} i.size)
      embedding := (groupBaseChange k F).map i.embedding
      closed := by
        letI := i.closed
        change IsClosedImmersion ((baseChange k F).map i.embedding.hom.hom).left
        exact MorphismProperty.of_isPullback
          (baseChangeMapPullback (K := F) i.embedding.hom.hom).flip i.closed }
  let f : PointsIn j F → PointsIn i F := baseChangePoint k F G.val.X (BF F)
  have hf : Function.Bijective f := baseChangePoints k F G.val.X (BF F)
  refine ⟨j, isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨⟨?_⟩, hf.1⟩, hf.2⟩⟩
  change TopologicalSpace.induced (asMatrix j F) _ =
    TopologicalSpace.induced (fun y : PointsIn j F ↦
      (baseChangePoint k F G.val.X (BF F) y : PointsIn i F)) (TopologicalSpace.induced (asMatrix i F) _)
  rw [induced_compose]
  congr 1
  funext y
  have h := baseChangePointsSchemeNaturality k F i.embedding.hom.hom (BF F) y
  let R := (restrictTestAlgebra k F).obj (BF F)
  let Q := CommAlgCat.of k F
  let f : R ⟶ Q := ConcreteCategory.ofHom (C := CommAlgCat k) (X := R) (Y := Q)
    (@AlgHom.mk k R Q _ _ _ R.algebra Q.algebra (RingHom.id F) (fun _ ↦ rfl))
  let p := baseChangePoint k F G.val.X (BF F) y ≫ i.embedding.hom.hom
  have h₁ : asMatrix j F y = (i.matrix.hom.app R).hom p := by
    change (i.matrix.hom.app R).hom
      (baseChangePoint k F i.ambient.val.X (BF F)
        (y ≫ (baseChange k F).map i.embedding.hom.hom)) = _
    exact congrArg ((i.matrix.hom.app R).hom) h
  refine h₁.trans ?_
  have h₂ : mapPoints f p = (show Points i.ambient.val.X Q from p) := by
    apply Over.OverMorphism.ext
    simp only [mapPoints, Over.comp_left, algSpec_map_left]
    change Spec.map (𝟙 (CommRingCat.of F)) ≫ p.left = p.left
    simp
  have hm := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (i.matrix.hom.naturality f)) p
  change (i.matrix.hom.app Q).hom (mapPoints f p) =
    Matrix.GeneralLinearGroup.map (RingHom.id F) ((i.matrix.hom.app R).hom p) at hm
  rw [h₂] at hm
  have hid (M : Matrix.GeneralLinearGroup (Index.{u} i.size) F) :
      Matrix.GeneralLinearGroup.map (RingHom.id F) M = M := by
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    rfl
  rw [hid] at hm
  exact hm.symm

set_option synthInstance.maxHeartbeats 100000 in
theorem padicCompletionScalars : PadicCompletionScalars.{u} := by
  intro K _ _ w
  let v : HeightOneSpectrum (𝓞 ℚ) := {
    asIdeal := Ideal.under (𝓞 ℚ) w.asIdeal
    isPrime := (Ideal.isMaximal_under_of_isIntegral_of_isMaximal w.asIdeal).isPrime
    ne_bot := Ideal.IsIntegral.under_ne_bot (𝓞 ℚ) w.ne_bot }
  letI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  refine ⟨v, inferInstance, ?_⟩
  let A := v.adicCompletion ℚ
  let F := w.adicCompletion K
  let eA := HeightOneSpectrum.adicCompletion.equiv ℚ v
  let eF := HeightOneSpectrum.adicCompletion.equiv K w
  let f := algebraMap (WithVal (v.valuation ℚ)) (WithVal (w.valuation K))
  have hf : Continuous f := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver ℚ K v w).continuous
  let ψ : A →+* F := eF.symm.toRingHom.comp ((Completion.mapRingHom f hf).comp eA.toRingHom)
  have hψ : Continuous ψ := by
    exact (HeightOneSpectrum.adicCompletion.uniformEquiv K w).symm.continuous.comp
      (Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.uniformEquiv ℚ v).continuous)
  letI : Algebra A F := ψ.toAlgebra
  haveI : ContinuousSMul A F := by
    constructor
    change Continuous ((fun r : A × F ↦ ψ r.1 * r.2))
    exact (hψ.comp continuous_fst).mul continuous_snd
  haveI : IsScalarTower ℚ A F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional A F := inferInstanceAs
    (FiniteDimensional (v.adicCompletion ℚ) (w.adicCompletion K))
  let p := Rat.HeightOneSpectrum.primesEquiv v
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  let P := Padic p
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  letI : Algebra P A := e.symm.toRingEquiv.toRingHom.toAlgebra
  let a : Algebra P F := (ψ.comp e.symm.toRingEquiv.toRingHom).toAlgebra
  letI := a
  haveI : IsScalarTower P A F := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FiniteDimensional P A :=
    Module.Finite.of_surjective (Algebra.linearMap P A) e.symm.surjective
  exact ⟨a, Module.Finite.trans A F, hψ.comp e.symm.continuous⟩

private theorem realAlgebraOfEquiv {F : Type u} [Field F] [TopologicalSpace F]
    {L : Type} [Field L] [TopologicalSpace L] [Algebra ℝ L] [FiniteDimensional ℝ L]
    (e : F ≃+* L) (he : Continuous e.symm) (hL : Continuous (algebraMap ℝ L)) :
    ∃ a : Algebra ℝ F, letI := a; FiniteDimensional ℝ F ∧ Continuous (algebraMap ℝ F) := by
  let a : Algebra ℝ F := (e.symm.toRingHom.comp (algebraMap ℝ L)).toAlgebra
  letI := a
  let f : L →ₗ[ℝ] F := {
    toFun := e.symm
    map_add' := map_add e.symm
    map_smul' := fun x y ↦ by
      change e.symm (x • y) = e.symm (algebraMap ℝ L x) * e.symm y
      rw [Algebra.smul_def, map_mul] }
  exact ⟨a, Module.Finite.of_surjective f e.symm.surjective, he.comp hL⟩

private theorem continuousRingEquivSymm {F L : Type*} [Field F] [Field L]
    [PseudoMetricSpace F] [PseudoMetricSpace L] (e : F ≃+* L) (he : Isometry e) :
    Continuous e.symm := (show Isometry e.symm from fun x y ↦ by
      simpa using (he.edist_eq (e.symm x) (e.symm y)).symm).continuous

theorem archimedeanCompletionScalars : ArchimedeanCompletionScalars.{u} := by
  intro K _ w
  rcases w.isReal_or_isComplex with h | h
  · obtain ⟨e, he⟩ := numberRealCompletion w h
    exact realAlgebraOfEquiv e (continuousRingEquivSymm e he) continuous_id
  · obtain ⟨e, he⟩ := numberComplexCompletion w h
    exact realAlgebraOfEquiv e (continuousRingEquivSymm e he) Complex.continuous_ofReal

private theorem evaluation_continuous {F : Type u} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] {G : AffineAlgebraicGroup F} (i : MatrixRealization G)
    (A : TestAlgebra F) (e : (testSpec F).obj (op A) ≅ G.val.X) (x : A) :
    Continuous (fun g : PointsIn i F ↦ (coordinateMap (k := F) (g ≫ e.inv)).hom x) := by
  obtain ⟨a, ha, he⟩ := matrixPresentation A e i
  obtain ⟨y, rfl⟩ := ha x
  have h : (fun g : PointsIn i F ↦ (coordinateMap (k := F) (g ≫ e.inv)).hom (a.hom y)) =
      (fun g : PointsIn i F ↦ glEvaluation (asMatrix i F g) y) :=
    funext fun g => (congrArg (fun f => f y) (he F g)).symm
  rw [h]
  exact (continuous_glEvaluation y).comp continuous_induced_dom

private abbrev matrixTransformation {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (i : MatrixRealization G) :=
  (groupPointsFunctor F).map i.embedding ≫ i.matrix.hom

private theorem matrix_naturality {F : Type u} [Field F] {G : GroupScheme F}
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (α : (groupPointsFunctor F).obj G ⟶ generalLinearPoints F ι)
    {A R : TestAlgebra F} (a : A ⟶ R) (p : GroupPoints G A) (i j : ι) :
    ((α.app R).hom (mapPoints a p)).val i j =
      a.hom (((α.app A).hom p).val i j) := by
  exact congrArg (fun x : Matrix.GeneralLinearGroup ι R ↦ x.val i j)
    (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (α.naturality a)) p)

private theorem matrix_entry_continuous {F : Type u} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] {G : AffineAlgebraicGroup F} (i : MatrixRealization G)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (α : (groupPointsFunctor F).obj G.val ⟶ generalLinearPoints F ι) (j l : ι) :
    Continuous (fun g : PointsIn i F ↦ ((α.app (BF F)).hom g).val j l) := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.property.1
  let p : GroupPoints G.val A.unop := e.hom
  let x : A.unop := ((α.app A.unop).hom p).val j l
  convert evaluation_continuous i A.unop e x using 1
  funext g
  have h : mapPoints (coordinateMap (k := F) (g ≫ e.inv)) p = g := by
    change (testSpec F).map (coordinateMap (k := F) (g ≫ e.inv)).op ≫ e.hom = g
    rw [coordinateMap_spec]
    simp
  let a := coordinateMap (k := F) (g ≫ e.inv)
  exact (congrArg (fun z : GroupPoints G.val (BF F) ↦ ((α.app (BF F)).hom z).val j l) h).symm.trans
    (matrix_naturality α a p j l)

theorem adjointEvaluation : AdjointEvaluation.{u, v} := by
  classical
  intro F _ _ _ G i c s
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W⟩ := existsAdjointWeightBasis G c s
  let J := ULift.{u} (Fin W.dimension)
  let V := Lie F G.val
  letI : SMul F V := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  let e := W.basis.equivFun
  let α := conjugationTransformation W.coordinates
  let f : PointsIn i F →* LinearMap.GeneralLinearGroup F (J → F) :=
    (conjugationEnd (R := BF F) W.coordinates).toHomUnits
  let ρ : PointsIn i F →* (V ≃ₗ[F] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e.symm).toMonoidHom.comp f)
  have hc (g : PointsIn i F) (v : V) :
      e (ρ g v) = conjugationLinear (R := BF F) W.coordinates g (e v) := by
    change e (e.symm (conjugationLinear (R := BF F) W.coordinates g (e v))) = _
    exact e.apply_symm_apply _
  have hcont (v : V) (j : J) : Continuous (fun g ↦ W.basis.coord j (ρ g v)) := by
    have h (g : PointsIn i F) :
        W.basis.coord j (ρ g v) = (((α.app (BF F)).hom g).val *ᵥ e v) j := by
      change e (ρ g v) j = _
      rw [hc]
      exact (congrFun (LinearMap.toMatrix'_mulVec
        (conjugationLinear (R := BF F) W.coordinates g) (e v)) j).symm
    simp_rw [h, Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ (fun l _ ↦ (matrix_entry_continuous i α j l).mul continuous_const)
  have hw (t : Fˣ) (j : J) :
      ρ (cocharacterPoint c (BF F) t) (W.basis j) = ((t : F) ^ W.weight j) • W.basis j := by
    apply e.injective
    rw [hc, e.map_smul]
    apply (W.coordinates.equiv (BF F)).injective
    apply Subtype.ext
    change (W.coordinates.equiv (BF F)
      (conjugationLinear (R := BF F) W.coordinates (cocharacterPoint c (BF F) t) (e (W.basis j)))).toMul.val =
      (W.coordinates.equiv (BF F) (_ • e (W.basis j))).toMul.val
    rw [conjugationLinear_spec, ← W.diagonal]
    apply congrArg (fun x ↦ (W.coordinates.equiv (BF F) x).toMul.val)
    funext l
    change (↑(t ^ W.weight l) : F) * e (W.basis j) l =
      ((t : F) ^ W.weight j) * e (W.basis j) l
    change (↑(t ^ W.weight l) : F) * W.basis.repr (W.basis j) l =
      ((t : F) ^ W.weight j) * W.basis.repr (W.basis j) l
    rw [Module.Basis.repr_self]
    obtain rfl | h := eq_or_ne j l
    · rw [Units.val_zpow_eq_zpow_val]
    · rw [show (Finsupp.single j (1 : F)) l = 0 from Finsupp.single_eq_of_ne h.symm]
      simp
  refine ⟨W, ρ, ?_, hcont, hw, ?_⟩
  · intro g v
    have h := conjugationLinear_spec (R := BF F) W.coordinates g (e v)
    have hv : W.coordinates.equiv (BF F) (e v) = v := Subtype.ext (W.coordinates.at_base v)
    rw [← hc] at h
    rw [hv] at h
    exact (W.coordinates.at_base (ρ g v)).symm.trans h
  · intro E _ _ _ _ ι _ d hEF
    letI : ContinuousSMul E F := ⟨by
      simp only [Algebra.smul_def]
      exact (hEF.comp continuous_fst).mul continuous_snd⟩
    haveI : FiniteDimensional E F := Module.Finite.of_basis d
    letI : Module E V := Module.compHom V (algebraMap E F)
    letI : IsScalarTower E F V := IsScalarTower.of_algebraMap_smul (R := E) (A := F) (M := V) fun _ _ ↦ rfl
    dsimp only
    let σ : PointsIn i F →* (V ≃ₗ[E] V) :=
      { toFun := fun g ↦ (ρ g).restrictScalars E
        map_one' := LinearEquiv.ext (fun v ↦ congrArg (fun f : V ≃ₗ[F] V ↦ f v) (map_one ρ))
        map_mul' := fun g h ↦ LinearEquiv.ext (fun v ↦
          congrArg (fun f : V ≃ₗ[F] V ↦ f v) (map_mul ρ g h)) }
    refine ⟨σ, fun _ _ ↦ rfl, ?_, ?_⟩
    · intro v j
      change Continuous (fun g ↦ (d.smulTower W.basis).repr (ρ g v) j)
      rw [show (fun g ↦ (d.smulTower W.basis).repr (ρ g v) j) =
        (d.coord j.1) ∘ (fun g ↦ W.basis.coord j.2 (ρ g v)) from by
        funext g; exact Module.Basis.smulTower_repr _ _ _ _]
      exact (d.coord j.1).continuous_of_finiteDimensional.comp (hcont v j.2)
    · intro t j
      let z := Units.map (algebraMap E F).toMonoidHom t
      change ρ (cocharacterPoint c (BF F) z) ((d.smulTower W.basis) j) =
        ((t : E) ^ W.weight j.2) • (d.smulTower W.basis) j
      have hs : (z : F) ^ W.weight j.2 = algebraMap E F ((t : E) ^ W.weight j.2) := by
        exact (map_zpow₀ (algebraMap E F) (t : E) _).symm
      calc
        _ = d j.1 • ρ (cocharacterPoint c (BF F) z) (W.basis j.2) := by
          rw [Module.Basis.smulTower_apply, (ρ _).map_smul]
        _ = d j.1 • (((z : F) ^ W.weight j.2) • W.basis j.2) :=
          congrArg (d j.1 • ·) (hw z j.2)
        _ = ((t : E) ^ W.weight j.2) • (d.smulTower W.basis) j := by
          rw [hs, smul_comm, IsScalarTower.algebraMap_smul, Module.Basis.smulTower_apply]

theorem normSeparatesWeights : NormSeparatesWeights.{v} := by
  intro E _ t ht m n h
  simp only [norm_zpow] at h
  exact zpow_right_injective₀ (norm_pos_iff.mpr t.ne_zero) ht h

theorem contractingScalarExists : ContractingScalarExists.{v} := by
  intro E _
  obtain ⟨t, hpos, hlt⟩ := NormedField.exists_norm_lt_one E
  exact ⟨Units.mk0 t (norm_pos_iff.mp hpos), hlt⟩

private theorem matrix_specialization_continuous {F : Type u} [Field F] [TopologicalSpace F]
    [IsTopologicalDivisionRing F] {G : AffineAlgebraicGroup F} (i : MatrixRealization G)
    (p : GroupPoints G.val (polynomialAlgebra (BF F))) :
    @Continuous F (PointsIn i F) _ _ (fun x ↦ mapPoints (polynomialEvaluate (BF F) x) p) := by
  have hM := (glVal_isEmbedding (R := F) (ι := Index.{u} i.size)).isInducing.comp
    (show IsInducing (asMatrix i F) from ⟨rfl⟩)
  apply hM.continuous_iff.mpr
  apply continuous_pi
  intro j
  apply continuous_pi
  intro l
  let q := (((matrixTransformation i).app (polynomialAlgebra (BF F))).hom p).val j l
  change Continuous (fun x : F ↦ (asMatrix i F (mapPoints (polynomialEvaluate (BF F) x) p)).val j l)
  have h : (fun x : F ↦ (asMatrix i F (mapPoints (polynomialEvaluate (BF F) x) p)).val j l) =
      (fun x : F ↦ q.eval x) :=
    funext fun x => matrix_naturality (matrixTransformation i) (polynomialEvaluate (BF F) x) p j l
  rw [h]
  exact Polynomial.continuous _

private theorem evalLaurent_comp {F : Type u} [Field F] (t : Fˣ) :
    polynomialToLaurent (BF F) ≫ evalLaurent (𝟙 (BF F)) t = polynomialEvaluate (BF F) t := by
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change LaurentPolynomial.eval₂ (RingHom.id F) t (Polynomial.toLaurent Polynomial.X) =
    Polynomial.aevalTower (AlgHom.id F F) (t : F) Polynomial.X
  rw [Polynomial.toLaurent_X, LaurentPolynomial.eval₂_T, zpow_one, Polynomial.aevalTower_X]

private def cocharacterHom {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (i : MatrixRealization G) (c : Cocharacter G.val) : Fˣ →* PointsIn i F :=
  ((((groupPointsFunctor F).map c).app (BF F)).hom).comp
    (unitPointHom (BF F))

theorem contractingEvaluation : ContractingEvaluation.{u, v} := by
  intro F _ _ _ G i c D E _ _ hEF t ht g hg
  obtain ⟨p, hp, hp0⟩ := (D.contracting_points (BF F) g).mpr hg
  let a := cocharacterHom i c (Units.map (algebraMap E F).toMonoidHom t)
  let z := Units.map (algebraMap E F).toMonoidHom t
  have hzero : Tendsto (fun n : ℕ ↦ ((z ^ n : Fˣ) : F)) atTop (𝓝 0) := by
    have he : (fun n : ℕ ↦ ((z ^ n : Fˣ) : F)) = (algebraMap E F) ∘ (fun n : ℕ ↦ (t : E)^n) := by
      funext n
      calc
        ((z ^ n : Fˣ) : F) = (algebraMap E F t)^n := Units.val_pow_eq_pow_val _ _
        _ = algebraMap E F ((t : E)^n) := (map_pow _ _ _).symm
    rw [he, ← map_zero (algebraMap E F)]
    exact (hEF.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht)
  let curve : F → PointsIn i F := fun x ↦ mapPoints (polynomialEvaluate (BF F) x) p
  have hcurve : Continuous curve := matrix_specialization_continuous i p
  have h := (hcurve.tendsto 0).comp hzero
  change Tendsto (fun n : ℕ ↦ a ^ n * g * (a ^ n)⁻¹) atTop (𝓝 1)
  have hp0' : curve 0 = (1 : PointsIn i F) := hp0
  rw [hp0'] at h
  have hseq : (fun n : ℕ ↦ a ^ n * g * (a ^ n)⁻¹) =
      curve ∘ (fun n : ℕ ↦ ((z ^ n : Fˣ) : F)) := by
    funext n
    have he := congrArg (mapPoints (X := G.val.X) (evalLaurent (𝟙 (BF F)) (z ^ n))) hp
    rw [← mapPoints_comp, evalLaurent_comp, orbit_eval] at he
    change (mapPoints (polynomialEvaluate (BF F) (z ^ n : Fˣ)) p : PointsIn i F) =
      cocharacterHom i c (z ^ n) * (show PointsIn i F from mapPoints (𝟙 (BF F)) g) *
        (cocharacterHom i c (z ^ n))⁻¹ at he
    have hid : (show PointsIn i F from mapPoints (𝟙 (BF F)) g) = g := by
      change (testSpec F).map ((𝟙 (BF F)).op) ≫ g = g
      simp
    rw [map_pow, hid] at he
    exact he.symm
  rw [hseq]
  exact h

theorem parabolicRadicalEvaluation : ParabolicRadicalEvaluation.{u, v} := by
  intro F _ _ _ G i P hP
  obtain ⟨c, D, e, U, iU, L, j, he, hi, _, _, _, _, hD, hU, _⟩ :=
    Relative.Parabolics.rationalParabolics.1 G P hP
  have hSame : RankOneFlag.SameSubgroup P D.parabolic :=
    ⟨⟨e.hom, he⟩, ⟨e.inv, by rw [← he, Iso.inv_hom_id_assoc]⟩⟩
  refine ⟨c, D, hSame, hD, ?_, fun h t ht g hg ↦ contractingEvaluation G i c D h t ht g hg⟩
  intro V hV
  obtain ⟨f, hf⟩ := radicalIso hV hU
  refine ⟨f ≪≫ iU, ?_⟩
  change (f.hom ≫ iU.hom) ≫ D.contracting.inclusion = V.inclusion ≫ P.inclusion
  rw [Category.assoc, ← D.contracting_in_G, ← Category.assoc iU.hom, hi,
    Category.assoc U.inclusion, he, ← Category.assoc f.hom, hf]

theorem openCocompactContainsRadicals : OpenCocompactContainsRadicals.{u, v} := by
  intro F _ _ _ G i E _ _ hEF H _ hH
  have : DiscreteTopology (PointsIn i F ⧸ H) := QuotientGroup.discreteTopology_iff.mpr hH
  have : Finite (PointsIn i F ⧸ H) := finite_of_compact_of_discrete
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hCore : IsOpen (H.normalCore : Set (PointsIn i F)) :=
    H.normalCore.isOpen_of_isClosed_of_finiteIndex (H.normalCore_isClosed
      (OpenSubgroup.mk H hH).isClosed)
  refine ⟨inferInstance, ?_⟩
  intro P hP U hU g hg
  obtain ⟨c, D, _, _, hRad, hcon⟩ := parabolicRadicalEvaluation G i P hP
  obtain ⟨e, he⟩ := hRad U hU
  obtain ⟨y, hy⟩ := hg
  have hg' : g ∈ ((((groupPointsFunctor F).map D.contracting.inclusion).app (BF F)).hom).range := by
    refine ⟨(((groupPointsFunctor F).map e.hom).app (BF F)).hom y, ?_⟩
    rw [← hy, ← he, Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
  obtain ⟨t, ht⟩ := contractingScalarExists (E := E)
  have hlim := hcon hEF t ht g hg'
  obtain ⟨n, hn⟩ := (hlim.eventually (hCore.mem_nhds H.normalCore.one_mem)).exists
  let a : PointsIn i F := cocharacterPoint c (BF F) (Units.map (algebraMap E F).toMonoidHom t)
  let x : PointsIn i F := g
  change a ^ n * x * (a ^ n)⁻¹ ∈ H.normalCore at hn
  change x ∈ H
  apply H.normalCore_le
  have h := (inferInstance : H.normalCore.Normal).conj_mem _ hn (a ^ n)⁻¹
  simpa only [mul_assoc, inv_mul_cancel_left, inv_inv, inv_mul_cancel, mul_one] using h

open private gm unitEquiv unitEquiv_unitPoint unitPointHom_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private connected_of_geometricallyConnected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private closedSubgroup_iso_of_smooth_lie_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj BigOperators

private theorem gm_affine (F : Type u) [Field F] : IsAffine (gm F).X.left := by
  change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)))
  infer_instance

private def splitCoordinateTransform {F : Type u} [Field F]
    {J : Type u} [Fintype J] [DecidableEq J] (j : J) :
    (groupPointsFunctor F).obj (gm F) ⟶ Specs.StandardGroups.multiplicativePowerPoints F J where
  app R := GrpCat.ofHom ((MonoidHom.mulSingle (fun _ : J ↦ Rˣ) j).comp (unitEquiv R).toMonoidHom)
  naturality := by
    intro R S a
    apply GrpCat.ext
    intro r
    obtain ⟨t, rfl⟩ := (unitEquiv R).symm.surjective r
    have ht : (unitEquiv R).symm t = unitPoint R t := unitPointHom_apply R t
    symm
    change (fun l ↦ Units.map a.hom.toMonoidHom (Pi.mulSingle (M := fun _ : J ↦ Rˣ) j (unitEquiv R ((unitEquiv R).symm t)) l)) =
      Pi.mulSingle (M := fun _ : J ↦ Sˣ) j (unitEquiv S (mapPoints a ((unitEquiv R).symm t)))
    rw [MulEquiv.apply_symm_apply, ht, mapPoints_unitPoint, unitEquiv_unitPoint]
    funext l
    obtain rfl | h := eq_or_ne l j
    · simp
    · simp [Pi.mulSingle_eq_of_ne h]

private def splitCoordinate {F : Type u} [Field F] {H : GroupScheme F}
    {J : Type u} [Fintype J] [DecidableEq J]
    (e : (groupPointsFunctor F).obj H ≅ Specs.StandardGroups.multiplicativePowerPoints F J)
    (j : J) : Cocharacter H :=
  (groupHomEquiv (gm F) H (gm_affine F)).symm (splitCoordinateTransform j ≫ e.inv)

private theorem splitCoordinate_eval {F : Type u} [Field F] {H : GroupScheme F}
    {J : Type u} [Fintype J] [DecidableEq J]
    (e : (groupPointsFunctor F).obj H ≅ Specs.StandardGroups.multiplicativePowerPoints F J)
    (j : J) (R : TestAlgebra F) (t : Rˣ) :
    cocharacterPoint (splitCoordinate e j) R t = e.inv.app R (Pi.mulSingle j t) := by
  have he := (groupHomEquiv (gm F) H (gm_affine F)).apply_symm_apply
    (splitCoordinateTransform j ≫ e.inv)
  change (groupPointsFunctor F).map (splitCoordinate e j) = _ at he
  unfold cocharacterPoint
  rw [he, NatTrans.comp_app, GrpCat.comp_apply]
  change e.inv.app R (Pi.mulSingle j (unitEquiv R (unitPoint R t))) = _
  rw [unitEquiv_unitPoint]

private theorem noncentral_cocharacter {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (S : ClosedSubgroup G.val) (hS : GeometricRadicals.IsSplitTorus S.group)
    (hc : ¬ CentralFrobeniusDescent.IsCentral S.inclusion) :
    ∃ c : Cocharacter S.group, ¬ CentralFrobeniusDescent.IsCentral (c ≫ S.inclusion) := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := hS
  let J := ULift.{u} (Fin r)
  let E := (groupPointsFunctor F).mapIso e ≪≫ LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso F J
  by_contra! h
  apply hc
  suffices h1 : Centralizes S.inclusion (𝟙 G.val.X) by
    intro Y g
    apply (centralizes_iff S.inclusion g).mpr
    intro U t s
    simpa only [Category.comp_id] using
      (centralizes_iff S.inclusion (𝟙 G.val.X)).mp h1 U (t ≫ g) s
  unfold Centralizes
  have ha : IsAffine (S.group.X ⊗ G.val.X).left := by
    change IsAffine (pullback S.group.X.hom G.val.X.hom)
    letI : IsAffine S.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup S).property.1
    letI : IsAffine G.val.X.left := G.property.1
    letI : IsAffine (Spec (CommRingCat.of F)) := inferInstance
    infer_instance
  apply hom_ext_of_points ha
  intro R p
  let x : GroupPoints S.group R := p ≫ fst _ _
  let g : GroupPoints G.val R := p ≫ snd _ _
  let toG : (J → Rˣ) →* GroupPoints G.val R :=
    (((groupPointsFunctor F).map S.inclusion).app R).hom.comp (E.inv.app R).hom
  let v : J → Rˣ := E.hom.app R x
  let C : Subgroup (J → Rˣ) := (Subgroup.centralizer {g}).comap toG
  have hv : v ∈ C := by
    rw [← Finset.univ_prod_mulSingle v]
    apply C.prod_mem
    intro j _
    change toG (Pi.mulSingle j (v j)) ∈ Subgroup.centralizer {g}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hj := (centralizes_iff (splitCoordinate E j ≫ S.inclusion) (𝟙 G.val.X)).mp
      (h (splitCoordinate E j) _ (𝟙 _)) _ g (unitPoint R (v j))
    change Commute (g ≫ 𝟙 _) (cocharacterPoint (splitCoordinate E j) R (v j) ≫
      S.inclusion.hom.hom) at hj
    rw [Category.comp_id, splitCoordinate_eval] at hj
    exact hj.eq.symm
  change toG v ∈ Subgroup.centralizer {g} at hv
  rw [Subgroup.mem_centralizer_singleton_iff] at hv
  have hx : (E.inv.app R).hom (E.hom.app R x) = x := GrpCat.inv_hom_apply (E.app R) x
  change (show GroupPoints G.val R from (E.inv.app R).hom (E.hom.app R x) ≫ S.inclusion.hom.hom) * g =
    g * (show GroupPoints G.val R from (E.inv.app R).hom (E.hom.app R x) ≫ S.inclusion.hom.hom) at hv
  rw [hx] at hv
  simp only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id]
  exact mul_inv_eq_iff_eq_mul.mpr hv.symm

private theorem opposite_comp {F : Type u} [Field F] {H G : GroupScheme F}
    (c : Cocharacter H) (i : H ⟶ G) :
    oppositeCocharacter (c ≫ i) = oppositeCocharacter c ≫ i := by
  exact (Category.assoc _ _ _).symm

theorem nonzeroContractingLie : NonzeroContractingLie.{u} := by
  classical
  intro F _ G hG S hS hcentral
  obtain ⟨c, hc⟩ := noncentral_cocharacter G S hS hcentral
  let cG := c ≫ S.inclusion
  let := hG.1
  let := connected_of_geometricallyConnected hG.2.1
  obtain ⟨D, Dneg, _, _, hsm, _⟩ := cocharacterDynamics G cG
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W, _, hpos, hcent⟩ := lieWeights G cG D s
  have hnonzero : ∃ j, W.weight j ≠ 0 := by
    by_contra! hz
    have hsurj : Function.Surjective (mapPointKernel D.centralizer.inclusion) := by
      intro x
      change x ∈ lieImage D.centralizer
      rw [hcent]
      intro j hj
      exact (hj (hz j)).elim
    let := closedSubgroup_iso_of_smooth_lie_surjective G hG D.centralizer hsm hsurj
    apply hc
    intro X g
    exact (D.centralizer_points X g).mpr
      ⟨g ≫ (inv D.centralizer.inclusion).hom.hom, by
        change g ≫ (inv D.centralizer.inclusion ≫ D.centralizer.inclusion).hom.hom = g
        rw [IsIso.inv_hom_id]
        exact Category.comp_id _⟩
  obtain ⟨j, hj⟩ := hnonzero
  have hcoords (l : ULift.{u} (Fin W.dimension)) (hne : l ≠ j) :
      W.basis.equivFun (W.basis j) l = 0 := by
    rw [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne]
  rcases lt_or_gt_of_ne hj with hj | hj
  · refine ⟨oppositeCocharacter c, opposite_comp c S.inclusion ▸ Dneg, W.basis j, ?_, W.basis.ne_zero j⟩
    have h₁ := (relativeOppositeContractingWeights G cG Dneg s W (BF F)
      (W.basis.equivFun (W.basis j))).mpr fun l hl ↦ hcoords l (by
        rintro rfl
        exact (not_le_of_gt hj) hl)
    obtain ⟨q, hq⟩ := h₁
    exact ⟨q, Subtype.ext (hq.trans (W.coordinates.at_base (W.basis j)))⟩
  · refine ⟨c, D, W.basis j, ?_, W.basis.ne_zero j⟩
    rw [hpos]
    intro l hl
    exact hcoords l (by rintro rfl; exact (not_le_of_gt hj) hl)

open private reductive_of_semisimple dimension_of_subgroup_le finite_group_dimension_le_zero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private factor_group_through_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

theorem isotropicContractingLie : IsotropicContractingLie.{u} := by
  intro F _ G hG hrank
  have hred := reductive_of_semisimple G hG
  obtain ⟨⟨S, hS⟩, hdim⟩ := Descent.RelativeRank.maximalSplitDimension G hred
  refine ⟨S, hS, nonzeroContractingLie G hred S hS.1 ?_⟩
  intro hcentral
  obtain ⟨Z, hZ, _⟩ := Reductive.CentralDerived.centralTorusExists G hred
  have hfinite := (Reductive.CentralDerived.semisimpleIffFiniteCentre G hred Z hZ).mp hG
  have hSZ : SchemeDerivedGroup.IsSubgroupOf S Z := by
    have hc : Centralizes (𝟙 G.val) S.inclusion.hom.hom := by
      apply (centralizes_iff _ _).mpr
      intro X s g
      have h := (centralizes_iff S.inclusion (𝟙 G.val.X)).mp
        (hcentral G.val.X (𝟙 _)) X g s
      change Commute (s ≫ S.inclusion.hom.hom) (g ≫ 𝟙 G.val.X)
      simpa only [Category.comp_id] using h.symm
    obtain ⟨z, hz⟩ := (hZ S.group.X S.inclusion.hom.hom).mp hc
    exact factor_group_through_subgroup Z S.inclusion z hz
  have h := (dimension_of_subgroup_le hSZ).trans
    (finite_group_dimension_le_zero (Specs.Unipotent.closedSubgroupAlgebraicGroup Z) hfinite)
  exact hrank.not_ge ((hdim S hS).symm.trans_le h)

end

end LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
