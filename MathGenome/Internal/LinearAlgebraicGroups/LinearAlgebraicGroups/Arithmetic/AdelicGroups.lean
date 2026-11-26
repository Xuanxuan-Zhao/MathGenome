import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology Filter
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open scoped RestrictedProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AdelicGroups

open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (Index)
open Specs.StandardGroups (GLCoordinates genericDeterminant universalMatrix)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}

instance completionTopologicalDivisionRing (D : GlobalFieldData.{u, v} K) (w : D.Place) :
    IsTopologicalDivisionRing (D.Completion w) := by
  cases w with
  | inl w =>
    change IsTopologicalDivisionRing (D.FiniteCompletion w)
    infer_instance
  | inr w =>
    cases D with
    | number h =>
      change IsTopologicalDivisionRing w.Completion
      infer_instance
    | function F t => exact w.elim

instance completionT2Space (D : GlobalFieldData.{u, v} K) (w : D.Place) :
    T2Space (D.Completion w) := by
  cases w with
  | inl w =>
    cases D with
    | number h =>
      letI := h
      change T2Space (w.adicCompletion K)
      infer_instance
    | function F t =>
      change T2Space w.Completion
      infer_instance
  | inr w =>
    cases D with
    | number h =>
      change T2Space w.Completion
      infer_instance
    | function F t => exact w.elim


open private glEvaluation glCoordinates_ext glEvaluation_entry matrixEvaluation
  isUnit_matrixEvaluation_det matrixEvaluation_mapMatrix
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

open private affineGroupIsoOfPoints affineGroupIsoOfPoints_map coordinateMap coordinateMap_spec
  specMap_surjective glPoint_eval gl_mem_range_of_entries_and_inverse
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels

private theorem glEvaluation_algebraMap {R ι : Type u} [CommRing R] [Algebra K R]
    [Fintype ι] [DecidableEq ι] (M : Matrix.GeneralLinearGroup ι R)
    (p : MvPolynomial (ι × ι) K) :
    glEvaluation M (algebraMap (MvPolynomial (ι × ι) K) (GLCoordinates K ι) p) =
      matrixEvaluation M.val p :=
  IsLocalization.Away.lift_eq (S := GLCoordinates K ι) (genericDeterminant K ι)
    (g := (matrixEvaluation M.val).toRingHom) (isUnit_matrixEvaluation_det M) p

private theorem glEvaluation_fraction {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : GLCoordinates K ι) :
    ∃ (p : MvPolynomial (ι × ι) K) (n : ℕ),
      ∀ (R : Type u) [CommRing R] [Algebra K R] (M : Matrix.GeneralLinearGroup ι R),
        glEvaluation M a = matrixEvaluation M.val p * (M⁻¹.val.det)^n := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (genericDeterminant K ι) a
  refine ⟨p, n, fun R _ _ M ↦ ?_⟩
  have hdet : matrixEvaluation M.val (genericDeterminant K ι) = M.val.det :=
    ((matrixEvaluation M.val).map_det _).trans
      (congrArg Matrix.det (matrixEvaluation_mapMatrix M.val))
  have he := congrArg (glEvaluation M) hp
  simp only [map_mul, map_pow, glEvaluation_algebraMap, hdet] at he
  have hinv : M.val.det * M⁻¹.val.det = 1 := by
    rw [← Matrix.det_mul]
    change (M.val * M.inv).det = 1
    rw [M.val_inv, Matrix.det_one]
  calc
    glEvaluation M a = glEvaluation M a * (M.val.det * M⁻¹.val.det)^n := by rw [hinv, one_pow, mul_one]
    _ = (glEvaluation M a * M.val.det ^ n) * M⁻¹.val.det ^ n := by rw [mul_pow, mul_assoc]
    _ = _ := by rw [he]

private theorem continuous_glEvaluation {R ι : Type u} [CommRing R] [Algebra K R]
    [TopologicalSpace R] [IsTopologicalRing R] [Fintype ι] [DecidableEq ι]
    (a : GLCoordinates K ι) :
    Continuous (fun M : Matrix.GeneralLinearGroup ι R ↦ glEvaluation M a) := by
  obtain ⟨p, n, h⟩ := glEvaluation_fraction a
  simp_rw [h R]
  have hm : Continuous (fun M : Matrix.GeneralLinearGroup ι R ↦ matrixEvaluation M.val p) := by
    change Continuous (fun M : Matrix.GeneralLinearGroup ι R ↦
      MvPolynomial.aeval (fun ij : ι × ι ↦ M.val ij.1 ij.2) p)
    clear h
    induction p using MvPolynomial.induction_on with
    | C x => simp only [MvPolynomial.aeval_C]; exact continuous_const
    | add p q hp hq => simp only [map_add]; exact hp.add hq
    | mul_X p ij hp =>
      simp only [map_mul, MvPolynomial.aeval_X]
      exact hp.mul ((continuous_apply ij.2).comp
        (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id ij.1))
  exact hm.mul ((Units.continuous_val.comp continuous_inv).matrix_det.pow n)

/-- The coordinate map of a matrix realization, in any affine presentation of the group. -/
private theorem matrixPresentation (A : TestAlgebra K) (e : (testSpec K).obj (op A) ≅ G.val.X)
    (i : MatrixRealization G) :
    ∃ a : CommAlgCat.of K (GLCoordinates K (Index.{u} i.size)) ⟶ A,
      Function.Surjective a.hom ∧
      ∀ (R : Type u) [CommRing R] [Algebra K R] (g : PointsIn i R),
        glEvaluation (asMatrix i R g) =
          (a ≫ coordinateMap (k := K) (g ≫ e.inv)).hom := by
  let L := StandardGroups.generalLinearGroup K (Index.{u} i.size)
  let m := StandardGroups.generalLinearGroupPointsIso K (Index.{u} i.size)
  let E : i.ambient.val ≅ L.val :=
    affineGroupIsoOfPoints i.ambient.prop.1 L.prop.1 (i.matrix ≪≫ m.symm)
  let f := e.hom ≫ i.embedding.hom.hom ≫ E.hom.hom.hom
  let a := coordinateMap (k := K) (A := A)
    (B := CommAlgCat.of K (GLCoordinates K (Index.{u} i.size))) f
  refine ⟨a, ?_, ?_⟩
  · have hf : IsClosedImmersion f.left := by
      letI := i.closed
      change IsClosedImmersion (e.hom.left ≫ i.embedding.hom.hom.left ≫ E.hom.hom.hom.left)
      let FG := Grp.forget (SchemeOver K) ⋙ Over.forget _
      haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
      haveI : IsIso E.hom.hom.hom.left := inferInstanceAs (IsIso (FG.map E.hom))
      infer_instance
    have hf' := congrArg Over.Hom.left (coordinateMap_spec f)
    rw [algSpec_map_left] at hf'
    exact specMap_surjective _ (hf' ▸ (show IsClosedImmersion f.left from hf))
  · intro R _ _ g
    let T := CommAlgCat.of K R
    let q : Points ((testSpec K).obj (op A)) T := g ≫ e.inv
    let p : A ⟶ T := coordinateMap q
    have he : (testSpec K).map (a ≫ p).op = g ≫ i.embedding.hom.hom ≫ E.hom.hom.hom := by
      rw [CategoryTheory.op_comp, Functor.map_comp, coordinateMap_spec,
        show (testSpec K).map a.op = f from coordinateMap_spec f]
      simp [q, f]
    let x : Points i.ambient.val.X T := g ≫ i.embedding.hom.hom
    have hh := affineGroupIsoOfPoints_map i.ambient.prop.1 L.prop.1 (i.matrix ≪≫ m.symm)
    have hh' := congrArg (fun α => α.app T x) hh
    change x ≫ E.hom.hom.hom = (i.matrix.hom.app T ≫ m.inv.app T) x at hh'
    have hm : m.hom.app T (g ≫ i.embedding.hom.hom ≫ E.hom.hom.hom) = asMatrix i R g := by
      rw [← Category.assoc, show g ≫ i.embedding.hom.hom = x from rfl, hh', GrpCat.comp_apply]
      exact GrpCat.hom_inv_apply (m.app T) (i.matrix.hom.app T x)
    apply glCoordinates_ext
    intro s t
    rw [glEvaluation_entry, ← glPoint_eval, he, hm]


private theorem coordinateMap_of_map {A B : TestAlgebra K} (f : A ⟶ B) :
    coordinateMap ((testSpec K).map f.op) = f := by
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of K)).map_injective
  exact coordinateMap_spec _

private theorem asMatrix_isClosedEmbedding (i : MatrixRealization G)
    (R : Type u) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] : IsClosedEmbedding (asMatrix i R) := by
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨a, ha, hm⟩ := matrixPresentation B.unop e i
  refine ⟨⟨.induced _, ?_⟩, ?_⟩
  · intro x y h
    have he := (hm R x).symm.trans ((congrArg glEvaluation h).trans (hm R y))
    have hp : coordinateMap (k := K) (x ≫ e.inv) = coordinateMap (k := K) (y ≫ e.inv) := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro b
      obtain ⟨c, rfl⟩ := ha b
      exact congrArg (fun f : GLCoordinates K (Index.{u} i.size) →ₐ[K] R => f c) he
    have hf := congrArg (fun z => (testSpec K).map z.op) hp
    simpa only [coordinateMap_spec, cancel_mono] using hf
  · have hr : Set.range (asMatrix i R) =
        ⋂ c : RingHom.ker a.hom, {m | glEvaluation m (c : GLCoordinates K (Index.{u} i.size)) = 0} := by
      ext m
      simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨g, rfl⟩ c
        rw [hm R g]
        change (coordinateMap (k := K) (g ≫ e.inv)).hom (a.hom c) = 0
        rw [RingHom.mem_ker.mp c.2, map_zero]
      · intro hz
        let ea := Ideal.quotientKerAlgEquivOfSurjective ha
        let f := Ideal.Quotient.liftₐ (RingHom.ker a.hom) (glEvaluation m)
          (fun c hc => hz ⟨c, hc⟩)
        let p := CommAlgCat.ofHom (f.comp ea.symm.toAlgHom)
        let g : PointsIn i R := (testSpec K).map p.op ≫ e.hom
        have hp : coordinateMap (k := K) (g ≫ e.inv) = p := by
          change coordinateMap (((testSpec K).map p.op ≫ e.hom) ≫ e.inv) = p
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, coordinateMap_of_map]
        refine ⟨g, ?_⟩
        have he : glEvaluation (asMatrix i R g) = glEvaluation (k := K) m := by
          rw [hm R g, hp]
          apply AlgHom.ext
          intro c
          have h₁ : ea (Ideal.Quotient.mk (RingHom.ker a.hom) c) = a.hom c := rfl
          change f (ea.symm (a.hom c)) = glEvaluation m c
          rw [← h₁, AlgEquiv.symm_apply_apply]
          rfl
        apply Matrix.GeneralLinearGroup.ext
        intro l n
        simpa only [glEvaluation_entry] using congrArg
          (fun f : GLCoordinates K (Index.{u} i.size) →ₐ[K] R => f (universalMatrix K _ l n)) he
    rw [hr]
    exact isClosed_iInter fun c => isClosed_singleton.preimage (continuous_glEvaluation c.1)

theorem localMatrixEmbedding : Specs.AdelicGroups.localMatrixEmbedding.{u, v} :=
  fun D i w => asMatrix_isClosedEmbedding i (D.Completion w)

private theorem glVal_isEmbedding {R ι : Type u} [Field R] [Fintype ι] [DecidableEq ι]
    [TopologicalSpace R] [IsTopologicalDivisionRing R] :
    IsEmbedding (Units.val : Matrix.GeneralLinearGroup ι R → Matrix ι ι R) := by
  let U := Matrix.GeneralLinearGroup ι R
  let f : U → Matrix ι ι R := Units.val
  let s : TopologicalSpace U := inferInstance
  let t : TopologicalSpace U := TopologicalSpace.induced f inferInstance
  have hst : s ≤ t := (@continuous_iff_le_induced U (Matrix ι ι R) f s _).mp
    Units.continuous_val
  have hf : @Continuous U (Matrix ι ι R) t _ f := continuous_induced_dom
  have h : @Continuous U U t s id := by
    refine Units.continuous_iff.mpr ⟨hf, ?_⟩
    simp only [id_eq, Matrix.coe_units_inv]
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx : (f x).det ≠ 0 := (Matrix.GeneralLinearGroup.det x).ne_zero
    have hi : ContinuousAt Ring.inverse (f x).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hx
    exact (continuousAt_matrix_inv _ hi).comp hf.continuousAt
  have hts : t ≤ s := by
    simpa only [@induced_id U s] using (@continuous_iff_le_induced U U id t s).mp h
  exact @IsEmbedding.mk U (Matrix ι ι R) s _ f
    (@IsInducing.mk U (Matrix ι ι R) s _ f (le_antisymm hst hts)) Units.val_injective

theorem usualLocalTopology : Specs.AdelicGroups.usualLocalTopology.{u, v} :=
  fun D i w => glVal_isEmbedding.comp (localMatrixEmbedding D i w).isEmbedding

instance pointsInTopologicalGroup (i : MatrixRealization G) (R : Type u)
    [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalGroup (PointsIn i R) :=
  IsInducing.isTopologicalGroup (asMatrix i R) (.induced _)

private theorem glIntegral_iff {R ι : Type u} [Field R] [Fintype ι] [DecidableEq ι]
    (O : ValuationSubring R) (m : Matrix.GeneralLinearGroup ι R) :
    m ∈ (Matrix.GeneralLinearGroup.map O.subtype).range ↔
      (∀ s t, m.val s t ∈ O) ∧ (∀ s t, m⁻¹.val s t ∈ O) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun s t => (x.val s t).2, fun s t => (x⁻¹.val s t).2⟩
  · rintro ⟨hm, hn⟩
    exact gl_mem_range_of_entries_and_inverse Subtype.val_injective m
      (fun s t => ⟨⟨_, hm s t⟩, rfl⟩) (fun s t => ⟨⟨_, hn s t⟩, rfl⟩)

private theorem glIntegral_compactOpen {R ι : Type u} [Field R] [Fintype ι] [DecidableEq ι]
    [TopologicalSpace R] [T2Space R] [IsTopologicalRing R] (O : ValuationSubring R)
    (hc : IsCompact (O : Set R)) (ho : IsOpen (O : Set R)) :
    IsCompact (Set.range (Matrix.GeneralLinearGroup.map (n := ι) O.subtype)) ∧
      IsOpen (Set.range (Matrix.GeneralLinearGroup.map (n := ι) O.subtype)) := by
  letI : CompactSpace O := isCompact_iff_compactSpace.mp hc
  letI : CompactSpace (Matrix ι ι O) := inferInstanceAs (CompactSpace (ι → ι → O))
  letI : IsTopologicalRing O := inferInstanceAs (IsTopologicalRing O.toSubring)
  refine ⟨isCompact_range (Continuous.generalLinearGroup_map continuous_subtype_val), ?_⟩
  have he : Set.range (Matrix.GeneralLinearGroup.map (n := ι) O.subtype) =
      (⋂ s, ⋂ t, {m | m.val s t ∈ O}) ∩ (⋂ s, ⋂ t, {m | m⁻¹.val s t ∈ O}) := by
    ext m
    simpa only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, MonoidHom.mem_range, Set.mem_range] using
      glIntegral_iff O m
  rw [he]
  refine (isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t => ?_).inter
    (isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t => ?_)
  · exact ho.preimage ((continuous_apply t).comp (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id s))
  · exact ho.preimage ((continuous_apply t).comp (Matrix.GeneralLinearGroup.continuous_apply _ continuous_inv s))

theorem integralCompactOpen : Specs.AdelicGroups.integralCompactOpen.{u, v} := by
  intro K _ G D i w
  obtain ⟨hc, ho, _⟩ := D.integers_properties w
  obtain ⟨hgc, hgo⟩ := glIntegral_compactOpen (ι := Index.{u} i.size) (D.integers w) hc ho
  have he := localMatrixEmbedding D i (.inl w)
  exact ⟨he.isCompact_preimage hgc, hgo.preimage he.continuous⟩

theorem localSubgroup_open (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place) :
    IsOpen (localSubgroup D i w : Set (LocalPoints D i w)) := by
  cases w with
  | inl w => exact (integralCompactOpen D i w).2
  | inr w => exact isOpen_univ

instance (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place) :
    IsTopologicalGroup (Adeles D i S) := by
  letI : Fact (∀ w : Outside D S, IsOpen (localSubgroup D i w.1 : Set (LocalPoints D i w.1))) :=
    ⟨fun w => localSubgroup_open D i w.1⟩
  exact RestrictedProduct.isTopologicalGroup _

theorem adelicTopology : Specs.AdelicGroups.adelicTopology.{u, v} :=
  fun _D _i _S => inferInstance


private theorem eventually_outside (D : GlobalFieldData.{u, v} K) (S : Finset D.Place)
    {p : D.Place → Prop} (hf : ∀ᶠ w : D.FinitePlace in cofinite, p (.inl w))
    (hi : ∀ w : D.InfinitePlace, p (.inr w)) :
    ∀ᶠ w : Outside D S in cofinite, p w.1 := by
  rw [eventually_cofinite] at hf ⊢
  refine ((hf.image (Sum.inl : D.FinitePlace → D.Place)).preimage
    (Subtype.val_injective.injOn)).subset ?_
  rintro ⟨w, hw⟩ hn
  cases w with
  | inl w => exact ⟨w, hn, rfl⟩
  | inr w => exact (hn (hi w)).elim

@[simp]
theorem localPoint_matrix (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (w : D.Place) (g : RationalPoints G) :
    asMatrix i (D.Completion w) (localPoint D i w g) =
      Matrix.GeneralLinearGroup.map (D.embedding w) (i.onPoints g) := by
  let α := ((groupPointsFunctor K).map i.embedding) ≫ i.matrix.hom
  let f := CommAlgCat.ofHom (Algebra.ofId K (D.Completion w))
  exact congrArg (fun a => a g) (α.naturality f)

private theorem localPoint_eventually (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S : Finset D.Place) (g : RationalPoints G) :
    ∀ᶠ w : Outside D S in cofinite, localPoint D i w.1 g ∈ localSubgroup D i w.1 := by
  apply eventually_outside D S (p := fun w => localPoint D i w g ∈ localSubgroup D i w)
  · let m := i.onPoints g
    have h (x : K) : ∀ᶠ w : D.FinitePlace in cofinite,
        D.embedding (.inl w) x ∈ D.integers w :=
      eventually_cofinite.mpr (D.finite_nonintegral x)
    have h₁ : ∀ᶠ w : D.FinitePlace in cofinite, ∀ s t, D.embedding (.inl w) (m.val s t) ∈ D.integers w :=
      eventually_all.mpr fun s => eventually_all.mpr fun t => h _
    have h₂ : ∀ᶠ w : D.FinitePlace in cofinite, ∀ s t, D.embedding (.inl w) (m⁻¹.val s t) ∈ D.integers w :=
      eventually_all.mpr fun s => eventually_all.mpr fun t => h _
    filter_upwards [h₁, h₂] with w h₁ h₂
    change asMatrix i (D.Completion (.inl w)) (localPoint D i (.inl w) g) ∈
      (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range
    rw [localPoint_matrix, glIntegral_iff]
    exact ⟨h₁, h₂⟩
  · intro w
    exact Subgroup.mem_top _

/-- The canonical diagonal of rational points in the adelic group away from S. -/
def diagonal : Specs.AdelicGroups.diagonalType.{u, v} :=
  fun D i S ↦
    { toFun := fun g => ⟨fun w => localPoint D i w.1 g, localPoint_eventually D i S g⟩
      map_one' := RestrictedProduct.ext _ _ (fun w => map_one (localPoint D i w.1))
      map_mul' := fun g h => RestrictedProduct.ext _ _ (fun w => map_mul (localPoint D i w.1) g h) }

theorem diagonalCoordinates : Specs.AdelicGroups.diagonalCoordinates diagonal :=
  fun _ _ _ _ _ => rfl


private theorem changeOfCoordinates (i j : MatrixRealization G) (l m : Index.{u} j.size) :
    ∃ a : GLCoordinates K (Index.{u} i.size),
      ∀ (R : Type u) [CommRing R] [Algebra K R] (g : PointsIn i R),
        glEvaluation (asMatrix i R g) a =
          (asMatrix j R (changePoints i j R g)).val l m := by
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨a, ha, hia⟩ := matrixPresentation B.unop e i
  obtain ⟨b, _, hjb⟩ := matrixPresentation B.unop e j
  obtain ⟨c, hc⟩ := ha (b.hom (universalMatrix K _ l m))
  refine ⟨c, fun R _ _ g ↦ ?_⟩
  rw [← glEvaluation_entry (k := K) (asMatrix j R (changePoints i j R g)) l m, hia R, hjb R]
  exact congrArg (coordinateMap (k := K) (g ≫ e.inv)).hom hc

theorem continuous_changePoints (i j : MatrixRealization G) (R : Type u)
    [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (changePoints i j R) := by
  refine (IsInducing.induced (asMatrix j R)).continuous_iff.mpr ?_
  have h₁ : Continuous (fun g : PointsIn i R ↦ (asMatrix j R (changePoints i j R g)).val) := by
    refine continuous_matrix fun l m => ?_
    obtain ⟨a, h⟩ := changeOfCoordinates i j l m
    simp_rw [← h R]
    exact (continuous_glEvaluation a).comp continuous_induced_dom
  refine Units.continuous_iff.mpr ⟨h₁, ?_⟩
  have he : (fun g : PointsIn i R => (asMatrix j R (changePoints i j R g))⁻¹.val) =
      (fun g : PointsIn i R => (asMatrix j R (changePoints i j R g⁻¹)).val) := by
    funext g
    rw [map_inv, map_inv]
  simp only [Function.comp_apply]
  rw [he]
  exact h₁.comp continuous_inv

private theorem matrixEvaluation_eventually (D : GlobalFieldData.{u, v} K) {ι : Type u}
    (p : MvPolynomial (ι × ι) K) :
    ∀ᶠ w : D.FinitePlace in cofinite, ∀ M : Matrix ι ι (D.Completion (.inl w)),
      (∀ l m, M l m ∈ D.integers w) → matrixEvaluation M p ∈ D.integers w := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have he : ∀ᶠ w : D.FinitePlace in cofinite, D.embedding (.inl w) c ∈ D.integers w :=
      eventually_cofinite.mpr (D.finite_nonintegral c)
    filter_upwards [he] with w hc M _
    change MvPolynomial.aeval (fun lm : ι × ι ↦ M lm.1 lm.2) (MvPolynomial.C c) ∈ D.integers w
    rwa [MvPolynomial.aeval_C]
  | add p q hp hq =>
    filter_upwards [hp, hq] with w hp hq M hM
    rw [map_add]
    exact (D.integers w).add_mem _ _ (hp M hM) (hq M hM)
  | mul_X p lm hp =>
    filter_upwards [hp] with w hp M hM
    rw [map_mul]
    refine (D.integers w).mul_mem _ _ (hp M hM) ?_
    change MvPolynomial.aeval (fun lm : ι × ι ↦ M lm.1 lm.2) (MvPolynomial.X lm) ∈ D.integers w
    rw [MvPolynomial.aeval_X]
    exact hM _ _

private theorem glEvaluation_eventually (D : GlobalFieldData.{u, v} K) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (a : GLCoordinates K ι) :
    ∀ᶠ w : D.FinitePlace in cofinite, ∀ M : Matrix.GeneralLinearGroup ι (D.Completion (.inl w)),
      M ∈ (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range →
        glEvaluation M a ∈ D.integers w := by
  obtain ⟨p, n, h⟩ := glEvaluation_fraction a
  filter_upwards [matrixEvaluation_eventually D p] with w hw M hM
  obtain ⟨y, rfl⟩ := hM
  let f := (D.integers w).subtype
  rw [h (D.Completion (.inl w))]
  refine (D.integers w).mul_mem _ _ (hw _ (fun s t => (y.val s t).2)) ?_
  apply pow_mem
  change (f.mapMatrix (y⁻¹.val)).det ∈ D.integers w
  rw [← RingHom.map_det]
  exact (y⁻¹.val.det).2

private theorem change_integral_eventually (D : GlobalFieldData.{u, v} K)
    (i j : MatrixRealization G) :
    ∀ᶠ w : D.FinitePlace in cofinite,
      Set.MapsTo (changePoints i j (D.Completion (.inl w)))
        (integralPoints D i w) (integralPoints D j w) := by
  have h (l m : Index.{u} j.size) : ∀ᶠ w : D.FinitePlace in cofinite,
      ∀ g : LocalPoints D i (.inl w), g ∈ integralPoints D i w →
        (asMatrix j (D.Completion (.inl w)) (changePoints i j (D.Completion (.inl w)) g)).val l m
          ∈ D.integers w := by
    obtain ⟨a, ha⟩ := changeOfCoordinates i j l m
    filter_upwards [glEvaluation_eventually D a] with w hw g hg
    rw [← ha]
    exact hw _ hg
  have h' := eventually_all.mpr fun l => eventually_all.mpr (h l)
  filter_upwards [h'] with w hw g hg
  change asMatrix j _ (changePoints i j _ g) ∈ (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range
  refine (glIntegral_iff _ _).mpr ⟨fun l m => hw l m g hg, fun l m => ?_⟩
  change (asMatrix j (D.Completion (.inl w)) (changePoints i j (D.Completion (.inl w)) g))⁻¹.val l m ∈
    D.integers w
  have he : asMatrix j (D.Completion (.inl w)) (changePoints i j (D.Completion (.inl w)) g⁻¹) =
      (asMatrix j (D.Completion (.inl w)) (changePoints i j (D.Completion (.inl w)) g))⁻¹ := by
    rw [map_inv, map_inv]
  rw [← he]
  exact hw l m g⁻¹ ((integralPoints D i w).inv_mem hg)

private theorem change_localSubgroup_eventually (D : GlobalFieldData.{u, v} K)
    (i j : MatrixRealization G) (S : Finset D.Place) :
    ∀ᶠ w : Outside D S in cofinite, Set.MapsTo (changePoints i j (D.Completion w.1))
      (localSubgroup D i w.1) (localSubgroup D j w.1) :=
  eventually_outside D S (p := fun w => Set.MapsTo (changePoints i j (D.Completion w))
    (localSubgroup D i w) (localSubgroup D j w))
    (change_integral_eventually D i j) (fun _ _ _ => Subgroup.mem_top _)

/-- Change of realization keeps every local point and is continuous in both directions. -/
def changeRealization (D : GlobalFieldData.{u, v} K) (i j : MatrixRealization G)
    (S : Finset D.Place) : Adeles D i S ≃ₜ* Adeles D j S := by
  let forward := RestrictedProduct.map (𝓕 := cofinite)
    (fun w : Outside D S => changePoints i j (D.Completion w.1))
    (change_localSubgroup_eventually D i j S)
  let backward := RestrictedProduct.map (𝓕 := cofinite)
    (fun w : Outside D S => changePoints j i (D.Completion w.1))
    (change_localSubgroup_eventually D j i S)
  refine
    { toFun := forward
      invFun := backward
      left_inv := fun x => RestrictedProduct.ext _ _ (fun _ => rfl)
      right_inv := fun x => RestrictedProduct.ext _ _ (fun _ => rfl)
      map_mul' := fun x y => RestrictedProduct.ext _ _ (fun w => map_mul (changePoints i j (D.Completion w.1)) _ _)
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact RestrictedProduct.mapAlong_continuous _ _ id tendsto_id _ (change_localSubgroup_eventually D i j S)
      (fun w => continuous_changePoints i j (D.Completion w.1))
  · exact RestrictedProduct.mapAlong_continuous _ _ id tendsto_id _ (change_localSubgroup_eventually D j i S)
      (fun w => continuous_changePoints j i (D.Completion w.1))

theorem independence : Specs.AdelicGroups.independence.{u, v} := by
  intro K _ G D i j S
  refine ⟨changeRealization D i j S, fun _ _ => rfl, fun e he => ?_⟩
  exact ContinuousMulEquiv.ext fun x => RestrictedProduct.ext _ _ (he x)

@[simp]
theorem changeRealization_diagonal (D : GlobalFieldData.{u, v} K) (i j : MatrixRealization G)
    (S : Finset D.Place) (g : RationalPoints G) :
    changeRealization D i j S (diagonal D i S g) = diagonal D j S g :=
  RestrictedProduct.ext _ _ (fun _ => rfl)


theorem adelicBasis : Specs.AdelicGroups.adelicBasis.{u, v} := by
  classical
  intro K _ G D i S
  let R (w : Outside D S) := LocalPoints D i w.1
  let A (w : Outside D S) : Set (R w) := localSubgroup D i w.1
  have hA (w : Outside D S) : IsOpen (A w) := localSubgroup_open D i w.1
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨T, U, ho, hU, rfl⟩
    have hbox : box D i S U =
        {x : Adeles D i S | ∀ w ∈ T, x w ∈ U w} ∩
          {x : Adeles D i S | ∀ w ∉ T, x w ∈ A w} := by
      ext x
      constructor
      · intro hx
        refine ⟨fun w _ => hx w, fun w hw => ?_⟩
        change x w ∈ (localSubgroup D i w.1 : Set (R w))
        rw [← hU w hw]
        exact hx w
      · rintro ⟨hx, hy⟩ w
        by_cases hw : w ∈ T
        · exact hx w hw
        · show x w ∈ U w
          rw [hU w hw]
          exact hy w hw
    rw [hbox]
    refine ((isOpen_set_pi T.finite_toSet (fun w _ => ho w)).preimage
      (RestrictedProduct.continuous_coe (R := R) (A := A))).inter ?_
    exact RestrictedProduct.isOpen_forall_imp_mem hA
  · intro x O hx ho
    let W : Set (Outside D S) := {w | x w ∈ A w}
    have hxW : W ∈ (cofinite : Filter (Outside D S)) := x.eventually
    have hW : cofinite ≤ 𝓟 W := le_principal_iff.mpr hxW
    let inc := RestrictedProduct.inclusion R A hW
    let y : Πʳ w, [R w, A w]_[𝓟 W] := ⟨x.1, mem_principal.mpr Set.Subset.rfl⟩
    let f : (Πʳ w, [R w, A w]_[𝓟 W]) → (∀ w, R w) := fun a => a
    have hind : IsEmbedding f :=
      RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
    obtain ⟨V, hVo, hV⟩ := hind.isInducing.isOpen_iff.mp
      (ho.preimage (RestrictedProduct.continuous_inclusion hW))
    have hy : f y ∈ V := by
      change y ∈ f ⁻¹' V
      rw [hV]
      exact hx
    obtain ⟨_, ⟨U, F, hU, rfl⟩, hB, hBV⟩ :=
      (isTopologicalBasis_pi fun w : Outside D S =>
        TopologicalSpace.isTopologicalBasis_opens (α := R w)).exists_subset_of_mem_open hy hVo
    have hfin : Wᶜ.Finite := mem_cofinite.mp hxW
    let T := F ∪ hfin.toFinset
    let U' (w : Outside D S) : Set (R w) :=
      (if w ∈ F then U w else Set.univ) ∩ (if w ∈ W then A w else Set.univ)
    have hU'o (w : Outside D S) : IsOpen (U' w) := by
      dsimp only [U']
      apply IsOpen.inter
      · split_ifs with hw
        · exact hU w hw
        · exact isOpen_univ
      · split_ifs
        · exact hA w
        · exact isOpen_univ
    have hU'eq (w : Outside D S) (hw : w ∉ T) : U' w = A w := by
      simp only [T, Finset.mem_union, hfin.mem_toFinset, Set.mem_compl_iff, not_or, not_not] at hw
      simp [U', hw.1, hw.2]
    refine ⟨box D i S U', ⟨T, U', hU'o, hU'eq, rfl⟩, ?_, ?_⟩
    · intro w
      constructor
      · split_ifs with hw
        · exact Set.mem_pi.mp hB w hw
        · exact Set.mem_univ _
      · split_ifs with hw
        · exact hw
        · exact Set.mem_univ _
    · intro z hz
      have hzW : ∀ w ∈ W, z w ∈ A w := by
        intro w hw
        have h := (hz w).2
        simpa only [ite_eq_left hw] using h
      let z' : Πʳ w, [R w, A w]_[𝓟 W] := ⟨z.1, mem_principal.mpr hzW⟩
      have hzF : f z' ∈ (↑F : Set (Outside D S)).pi U := by
        refine Set.mem_pi.mpr fun w hw => ?_
        have h := (hz w).1
        have hw' : w ∈ F := hw
        change z w ∈ U w
        simpa only [ite_eq_left hw'] using h
      have h : z' ∈ f ⁻¹' V := hBV hzF
      rw [hV] at h
      exact h

theorem canonicalDiagonal : Specs.AdelicGroups.canonicalDiagonal.{u, v} := by
  intro K _ G D i S
  refine ⟨diagonal D i S, fun _ _ => rfl, fun d hd => MonoidHom.ext fun g => ?_⟩
  exact RestrictedProduct.ext _ _ (hd g)

theorem strongApproximationDensity : Specs.AdelicGroups.strongApproximationDensity.{u, v} := by
  intro K _ G D i S d hd
  have h : {x : Adeles D i S | ∃ g : RationalPoints G, ∀ w : Outside D S,
      x w = localPoint D i w.1 g} = Set.range d := by
    ext x
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, RestrictedProduct.ext _ _ fun w => (hd g w).trans (hg w).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, hd g⟩
  change Dense _ ↔ Dense _
  rw [h]

theorem strongApproximation_iff (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S : Finset D.Place) :
    StrongApproximation D i S ↔ DenseRange (diagonal D i S) :=
  strongApproximationDensity D i S (diagonal D i S) (diagonalCoordinates D i S)

end LinearAlgebraicGroups.Arithmetic.AdelicGroups
