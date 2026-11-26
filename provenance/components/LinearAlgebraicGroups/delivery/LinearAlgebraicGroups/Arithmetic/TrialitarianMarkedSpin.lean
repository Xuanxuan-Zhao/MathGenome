import Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianMarkedSpin
import LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent
import LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
import LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
import LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
import LinearAlgebraicGroups.Albert.FrameParameters
import LinearAlgebraicGroups.Albert.Triality
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.Galois.Infinite

/-! The marked Clifford spin comparison for a cubic stabilizer. -/

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianMarkedSpin

universe u w
set_option autoImplicit false
set_option maxRecDepth 800

section MarkedFrameCharts

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open TrialitySpecification (Model modelOp mapModel modelBaseChange)
open SplitSpecification (ParaQuadratic)
open TrialitarianAlbertDescent (cubicStabilizerAction cubicStabilizerAction_natural
  cubicStabilizerAction_faithful splitChart_cubicDiagonalRange cubicStabilizerPoints_equiv_frameStabilizer)
open private modelBaseChange_tmul mapModel_unit mapModel_smul mapModel_add mapModel_comp
  from LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent
open scoped CategoryTheory.MonObj TensorProduct

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {J : AlbertModel F} {B : CubicStabilizer J E}
  {n : (E →ₐ[F] S) ≃ Fin 3}

variable (t : S ⊗[F] J.V ≃ₗ[S] Model S)
variable (hu : t (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit)
variable (hop : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
variable (hd : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => n.symm i e, 0))

private abbrev restrictField (F : Type u) [Field F] (R : TestAlgebra S) [Algebra F S] :=
  (restrictTestAlgebra F S).obj R

private noncomputable def markedChart (R : TestAlgebra S) :
    (restrictField F R ⊗[F] J.V) ≃ₗ[R] Model R :=
  let : Algebra F R := inferInstanceAs (Algebra F (restrictField F R))
  let : IsScalarTower F S R := IsScalarTower.of_algebraMap_eq' rfl
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange F S R R J.V).symm.trans
    (t.baseChange S R _ _)).trans (modelBaseChange S R)

private abbrev extendToTest (R : TestAlgebra S) : S →ₐ[F] restrictField F R :=
  { toRingHom := algebraMap S R, commutes' := fun _ => rfl }

private theorem markedChart_tmul (R : TestAlgebra S)
    (r : R) (v : J.V) :
    markedChart t R (r ⊗ₜ[F] v) = r • mapModel (algebraMap S R) (t (1 ⊗ₜ[F] v)) := by
  unfold markedChart
  simp only [LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, modelBaseChange_tmul]

private theorem markedChart_extend (R : TestAlgebra S)
    (z : S ⊗[F] J.V) :
    markedChart t R (TensorProduct.map (extendToTest (F := F) R).toLinearMap LinearMap.id z) =
      mapModel (algebraMap S R) (t z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s v =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      markedChart_tmul]
    have h : (s ⊗ₜ[F] v : S ⊗[F] J.V) = s • (1 ⊗ₜ[F] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, mapModel_smul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, mapModel_add]

private theorem markedChart_natural {R T : TestAlgebra S}
    (f : R ⟶ T) (x : restrictField F R ⊗[F] J.V) :
    let g := (restrictTestAlgebra F S).map f
    mapModel f.hom.toRingHom (markedChart t R x) =
      markedChart t T (TensorProduct.map g.hom.toLinearMap LinearMap.id x) := by
  intro g
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      markedChart_tmul, markedChart_tmul, mapModel_smul, ← mapModel_comp]
    have hf : f.hom.toRingHom.comp (algebraMap S R) = algebraMap S T := f.hom.comp_algebraMap
    rw [hf]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, mapModel_add]

include hu in
private theorem markedChart_unit (R : TestAlgebra S) :
    markedChart t R (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit := by
  rw [markedChart_tmul, one_smul, hu, mapModel_unit]

include hd in
private theorem markedChart_diagonal (R : TestAlgebra S) (e : E) :
    markedChart t R (1 ⊗ₜ[F] B.diagonal e) =
      (fun i => algebraMap S R (n.symm i e), 0) := by
  rw [markedChart_tmul, one_smul, hd]
  apply Prod.ext
  · rfl
  · funext i
    change ZornSpecification.mapCoordinates (algebraMap S R) (0 : Zorn S) = 0
    simp [ZornSpecification.mapCoordinates]

private theorem nativeModel_op (R : TestAlgebra S) (x y : R ⊗[S] Model S)
    (J : _root_.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan S (Model S))
    (h : ∀ (T : Type u) [CommRing T] [Algebra S T] (x y : T ⊗[S] Model S),
      HermitianSpecification.coordinatesBaseChange T (J.op T x y) =
        QuadraticOperatorSpecification.applyOperator (Specification.normBaseChange T (ZornSpecification.norm S))
          (LowerRankSpecification.untwisted T)
          (HermitianSpecification.coordinatesBaseChange T x)
          (HermitianSpecification.coordinatesBaseChange T y)) :
    modelBaseChange S R (J.op R x y) = modelOp (modelBaseChange S R x) (modelBaseChange S R y) := by
  obtain ⟨b, hb, hform⟩ := (LowerRank.native_base_changes S R).2.2.2
  have hb' : b.toLinearMap = (ZornSpecification.baseChange S R).toLinearMap := by
    ext z
    have ht := hb z
    simpa only [LinearEquiv.coe_coe, LinearMap.id_apply, LinearMap.baseChange_id] using ht
  have hop := hform.2.2.2.2.1 (HermitianSpecification.coordinatesBaseChange R x)
    (HermitianSpecification.coordinatesBaseChange R y)
  rw [hb'] at hop
  change LowerRankSpecification.mapBlocks (ZornSpecification.baseChange S R).toLinearMap
      (HermitianSpecification.coordinatesBaseChange R (J.op R x y)) = _
  rw [h R x y]
  exact hop.symm

include hu hop in
set_option maxHeartbeats 850000 in
private theorem markedChart_law (R : TestAlgebra S)
    (x y : restrictField F R ⊗[F] J.V) :
    markedChart t R (J.law.op (restrictField F R) x y) =
      modelOp (markedChart t R x) (markedChart t R y) := by
  obtain ⟨Jsplit, hJu, hJop, hR, _, _⟩ := (LowerRank.restricted_models S).2.2.2
  let A := J.law.baseChange S
  let B := ParaQuadratic.ofJordan Jsplit
  have h : A.IsIso B t := (ParaQuadratic.isIso_iff_ground A B _).2 ⟨hu.trans hJu.symm,
    fun v w => by
      rw [ParaQuadratic.groundOp_baseChange, hop]
      exact (hJop _ _).symm⟩
  let e := _root_.Specs.LinearAlgebraicGroups.Albert.iteratedTensorEquiv
    (R := F) (S := S) (M := J.V) R
  let tR := t.baseChange S R _ _
  obtain ⟨v, rfl⟩ := e.surjective x
  obtain ⟨w, rfl⟩ := e.surjective y
  have h₁ : e (A.op R v w) = J.law.op (restrictField F R) (e v) (e w) :=
    J.law.extendedOp_apply S R v w
  have h₂ : tR (A.op R v w) = Jsplit.op R (tR v) (tR w) := h.2 R v w
  have h₃ (v : R ⊗[S] (S ⊗[F] J.V)) : markedChart t R (e v) = modelBaseChange S R (tR v) := by
    change modelBaseChange S R (tR (e.symm (e v))) = _
    rw [e.symm_apply_apply]
  rw [← h₁, h₃, h₃, h₃, h₂]
  exact nativeModel_op R (tR v) (tR w) Jsplit @hR

include hu hop hd in
private theorem geometricFramePoints [Module.Finite F E]
    (degree : Module.finrank F E = 3) :
    ∃ p : ∀ R : TestAlgebra S, Points B.stabilizer.group.X (restrictField F R) ≃*
        TrialitySpecification.frameStabilizer (R := R),
      (∀ R g x, (p R g).val (markedChart t R x) =
        markedChart t R (cubicStabilizerAction B (restrictField F R) g x)) ∧
      ∀ {R T : TestAlgebra S} (f : R ⟶ T) (a : Points B.stabilizer.group.X (restrictField F R))
        (x : Model R),
        let g := (restrictTestAlgebra F S).map f
        mapModel f.hom.toRingHom ((p R a).val x) = (p T (mapPoints g a)).val (mapModel f.hom.toRingHom x) := by
  have he (R : TestAlgebra S) :
      ∃ p : Points B.stabilizer.group.X (restrictField F R) ≃*
          TrialitySpecification.frameStabilizer (R := R),
        ∀ g x, (p g).val (markedChart t R x) =
          markedChart t R (cubicStabilizerAction B (restrictField F R) g x) := by
    let : Algebra F R := inferInstanceAs (Algebra F (restrictField F R))
    let : IsScalarTower F S R := IsScalarTower.of_algebraMap_eq' rfl
    exact cubicStabilizerPoints_equiv_frameStabilizer B (restrictField F R) (markedChart t R)
      (markedChart_unit t hu R) (markedChart_law t hu hop R)
      (splitChart_cubicDiagonalRange B (restrictField F R) degree n (markedChart t R) (markedChart_diagonal t hd R))
  choose p hp using he
  refine ⟨p, hp, ?_⟩
  intro R T f a x g
  obtain ⟨y, rfl⟩ := (markedChart t R).surjective x
  rw [hp, markedChart_natural, markedChart_natural, hp,
    cubicStabilizerAction_natural]

end MarkedFrameCharts

section ScalarTrialityComparison

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open TrialitySpecification (Model modelOp mapModel modelBaseChange)
open Composition.ZornSpecification (norm)
open SpinSpecification (ScalarClifford vectors coefficientMap spinUnits)
open CliffordSpecification (coefficientForm)
open LinearAlgebraicGroups.Specs.Arithmetic.SpinScalarExtension (restricted vectorComparison)
open private cliffordComparison cliffordComparison_vector cliffordComparison_spin cliffordComparison_natural
  from LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
open private scalarIsometryClifford scalarIsometryClifford_vectors scalarIsometryClifford_spin
  from LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
open private spinPoints zornBasis spinRelatedEquiv spinRelated_naturality spinRelated_spec
  extendedClifford extendedClifford_vector clifford_vector_injective from LinearAlgebraicGroups.Albert.Triality

noncomputable section

variable {E S V : Type u} {I : Type w} [Field E] [Field S] [Algebra E S]
  [AddCommGroup V] [Module E V] [LinearOrder I]
  {q : QuadraticForm E V} {b : Module.Basis I E V}

private def cliffordToOctonions (e : (coefficientForm S q b).IsometryEquiv (norm S))
    (R : TestAlgebra S) : ScalarClifford q (restricted E R) ≃ₐ[R] ScalarClifford (norm S) R :=
  (cliffordComparison q b R).trans (scalarIsometryClifford e R)

private theorem cliffordToOctonions_spin (e : (coefficientForm S q b).IsometryEquiv (norm S))
    (R : TestAlgebra S) (a : (ScalarClifford q (restricted E R))ˣ) :
    Units.map (cliffordToOctonions e R).toMonoidHom a ∈ spinUnits (norm S) R ↔
      a ∈ spinUnits q (restricted E R) := by
  change Units.map (scalarIsometryClifford e R).toMonoidHom
    (Units.map (cliffordComparison q b R).toMonoidHom a) ∈ spinUnits (norm S) R ↔ _
  rw [scalarIsometryClifford_spin, cliffordComparison_spin]

private theorem cliffordToOctonions_natural (e : (coefficientForm S q b).IsometryEquiv (norm S))
    {R T : TestAlgebra S} (f : R ⟶ T) (a : ScalarClifford q (restricted E R)) :
    cliffordToOctonions e T (coefficientMap q (restricted E R) ((restrictTestAlgebra E S).map f).hom a) =
      coefficientMap (norm S) R f.hom (cliffordToOctonions e R a) := by
  change scalarIsometryClifford e T (cliffordComparison q b T _) =
    coefficientMap (norm S) R f.hom (scalarIsometryClifford e R (cliffordComparison q b R a))
  rw [cliffordComparison_natural]
  generalize cliffordComparison q b R a = y
  induction y using TensorProduct.inductionOn with
  | tmul r c => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private def testOctonionCoordinates (e : S ⊗[E] V ≃ₗ[S] Zorn S)
    (R : TestAlgebra S) : (restricted E R ⊗[E] V) ≃ₗ[R] Zorn R :=
  ((vectorComparison R).symm.trans (e.baseChange S R _ _)).trans (Zorn.baseChange S R)

private theorem cliffordToOctonions_vectors (e : (coefficientForm S q b).IsometryEquiv (norm S))
    (R : TestAlgebra S) (x : restricted E R ⊗[E] V) :
    (extendedClifford S R) (cliffordToOctonions e R (vectors q (restricted E R) x)) =
      CliffordAlgebra.ι (norm R) (testOctonionCoordinates e.toLinearEquiv R x) := by
  obtain ⟨y, rfl⟩ := (vectorComparison (K := E) (V := V) R).surjective x
  change extendedClifford S R (scalarIsometryClifford e R (cliffordComparison q b R _)) = _
  rw [cliffordComparison_vector, scalarIsometryClifford_vectors, extendedClifford_vector]
  change _ = CliffordAlgebra.ι (norm R) (Zorn.baseChange S R
    (e.toLinearEquiv.baseChange S R _ _ ((vectorComparison (K := E) (V := V) R).symm
      (vectorComparison (K := E) (V := V) R y))))
  rw [LinearEquiv.symm_apply_apply]

private def scalarSpinOctonions (e : (coefficientForm S q b).IsometryEquiv (norm S)) (R : TestAlgebra S) :
    SpinFunctor.Spin q (restricted E R) b ≃* spinPoints S R := by
  let H := SpinFunctor.spinSubgroup q (restricted E R) b
  let H' := SpinFunctor.spinSubgroup (norm S) R (zornBasis S)
  let a := Units.mapEquiv (cliffordToOctonions e R).toMulEquiv
  have h : H.map a.toMonoidHom = H' := by
    ext z
    change z ∈ H.map a.toMonoidHom ↔ z ∈ spinUnits (norm S) R
    obtain ⟨w, rfl⟩ := a.surjective z
    rw [show a w = Units.map (cliffordToOctonions e R).toMonoidHom w from rfl, cliffordToOctonions_spin]
    constructor
    · rintro ⟨v, hv, hvw⟩
      have h' : v = w := a.injective hvw
      exact h' ▸ hv
    · intro hw
      exact ⟨w, hw, rfl⟩
  exact (a.subgroupMap H).trans (MulEquiv.subgroupCongr h)

private theorem scalarSpinOctonions_val (e : (coefficientForm S q b).IsometryEquiv (norm S))
    (R : TestAlgebra S) (s : SpinFunctor.Spin q (restricted E R) b) :
    (scalarSpinOctonions e R s).val = Units.map (cliffordToOctonions e R).toMonoidHom s.val := rfl

private def spinFrameComparison (e : (coefficientForm S q b).IsometryEquiv (norm S)) (R : TestAlgebra S) :
    SpinFunctor.Spin q (restricted E R) b ≃* TrialitySpecification.frameStabilizer (R := R) :=
  (scalarSpinOctonions e R).trans ((spinRelatedEquiv S R).trans (Triality.frameTriality R).choose)

private theorem spinFrameComparison_apply (e : (coefficientForm S q b).IsometryEquiv (norm S))
    (R : TestAlgebra S) (s : SpinFunctor.Spin q (restricted E R) b) (x : Model R) :
    (spinFrameComparison e R s).val x =
      (x.1, fun i => (spinRelatedEquiv S R (scalarSpinOctonions e R s)).val i (x.2 i)) :=
  (Triality.frameTriality R).choose_spec _ x

private theorem spinFrameComparison_natural (e : (coefficientForm S q b).IsometryEquiv (norm S))
    {R T : TestAlgebra S} (f : R ⟶ T) (s : SpinFunctor.Spin q (restricted E R) b) (x : Model R) :
    let g := (restrictTestAlgebra E S).map f
    mapModel f.hom.toRingHom ((spinFrameComparison e R s).val x) =
      (spinFrameComparison e T (SpinFunctor.map q b g.hom s)).val (mapModel f.hom.toRingHom x) := by
  intro g
  let s' := scalarSpinOctonions e R s
  let t := SpinFunctor.map q b g.hom s
  let t' := SpinFunctor.map (norm S) (zornBasis S) f.hom s'
  have ht : scalarSpinOctonions e T t = t' := by
    apply Subtype.ext
    apply Units.ext
    rw [scalarSpinOctonions_val]
    exact cliffordToOctonions_natural e f s.val.val
  rw [spinFrameComparison_apply, spinFrameComparison_apply, show SpinFunctor.map q b g.hom s = t from rfl, ht]
  apply Prod.ext
  · rfl
  · funext i
    change ZornSpecification.mapCoordinates f.hom.toRingHom
        ((spinRelatedEquiv S R s').val i (x.2 i)) =
      (spinRelatedEquiv S T t').val i (ZornSpecification.mapCoordinates f.hom.toRingHom (x.2 i))
    exact spinRelated_naturality S f.hom s' i (x.2 i)

private theorem spinFrameComparison_vector (e : (coefficientForm S q b).IsometryEquiv (norm S))
    (R : TestAlgebra S) (s : SpinFunctor.Spin q (restricted E R) b)
    (x : restricted E R ⊗[E] V) :
    testOctonionCoordinates e.toLinearEquiv R (SpinFunctor.vectorAction q (restricted E R) b s x) =
      ((spinFrameComparison e R s).val
        (CubicSpecification.singleBlockCoordinates (1 : Fin 3) (testOctonionCoordinates e.toLinearEquiv R x))).2 1 := by
  let C := (cliffordToOctonions e R).trans (extendedClifford S R)
  let s' := scalarSpinOctonions e R s
  let y := SpinFunctor.vectorAction q (restricted E R) b s x
  let d := testOctonionCoordinates e.toLinearEquiv R
  let h := spinRelatedEquiv S R s'
  let v := Units.map (extendedClifford S R).toMonoidHom s'.val
  have hv : v = Units.map C.toMonoidHom s.val := rfl
  have hx := (spinRelated_spec S R s').2 (d x)
  have hy := SpinFunctor.vectorAction_characterization q (restricted E R) b s x
  have hy' := congrArg C hy
  change C (vectors q (restricted E R) y) =
    C (s.val.val * vectors q (restricted E R) x * ↑s.val⁻¹) at hy'
  rw [map_mul, map_mul] at hy'
  have hC (z : restricted E R ⊗[E] V) : C (vectors q (restricted E R) z) = CliffordAlgebra.ι _ (d z) :=
    cliffordToOctonions_vectors e R z
  rw [hC, hC] at hy'
  change CliffordAlgebra.ι _ (d y) = (v : CliffordAlgebra (norm R)) *
    CliffordAlgebra.ι _ (d x) * (↑v⁻¹ : CliffordAlgebra (norm R)) at hy'
  change (v : CliffordAlgebra (norm R)) * CliffordAlgebra.ι _ (d x) =
    CliffordAlgebra.ι _ (h.val 1 (d x)) * (v : CliffordAlgebra (norm R)) at hx
  rw [hx, mul_assoc, Units.mul_inv, mul_one] at hy'
  have hi : Function.Injective (CliffordAlgebra.ι (norm R)) :=
    fun _ _ h => clifford_vector_injective CliffordModel.octonionEquiv CliffordModel.octonionEquiv_ι h
  rw [spinFrameComparison_apply]
  change d y = h.val 1 ((Pi.single (M := fun _ : Fin 3 => Zorn R) 1 (d x)) 1)
  rw [Pi.single_eq_same]
  exact hi hy'

open SpinFunctor (Spin vectorAction)

private theorem spinFrameComparison_block
    (d : (coefficientForm S q b).IsometryEquiv (norm S))
    (R : TestAlgebra S) (s : Spin q (restricted E R) b)
    (x : restricted E R ⊗[E] V) :
    (spinFrameComparison d R s).val (CubicSpecification.singleBlockCoordinates 1 (testOctonionCoordinates d.toLinearEquiv R x)) =
      CubicSpecification.singleBlockCoordinates 1
        (testOctonionCoordinates d.toLinearEquiv R (vectorAction q (restricted E R)
          b s x)) := by
  classical
  apply Prod.ext
  · rw [spinFrameComparison_apply]
    rfl
  · funext i
    by_cases h : i = 1
    · subst i
      change _ = Pi.single (M := fun _ : Fin 3 => Zorn R) 1 _ 1
      rw [Pi.single_eq_same]
      exact (spinFrameComparison_vector d R s x).symm
    · rw [spinFrameComparison_apply]
      change (spinRelatedEquiv S R (scalarSpinOctonions d R s)).val i (Pi.single (M := fun _ : Fin 3 => Zorn R) 1 _ i) = Pi.single (M := fun _ : Fin 3 => Zorn R) 1 _ i
      rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]


end

end ScalarTrialityComparison

section ActualCubicAction

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Albert
open TrialitarianAlbertDescent (cubicStabilizerAction cubicStabilizerAction_natural)
open SpinSpecification (SchemePoints)

noncomputable section

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {G : AffineAlgebraicGroup F} {J : AlbertModel F} {B : CubicStabilizer J E}
variable (r : G.val ≅ B.stabilizer.group)
variable (j₀ : (Fin 8 → E) →ₗ[E] E ⊗[F] J.V)

private def actualCubicPoints (R : TestAlgebra E) :
    SchemePoints ((groupBaseChange F E).obj G.val) R ≃*
      Points B.stabilizer.group.X ((restrictTestAlgebra F E).obj R) := by
  let R₀ := (restrictTestAlgebra F E).obj R
  let e := ((groupPointsFunctor F).mapIso r).app R₀
  exact (baseChangePointGroupEquiv E G.val R).trans (e.groupIsoToMulEquiv)

private theorem actualCubicPoints_apply (R : TestAlgebra E)
    (x : SchemePoints ((groupBaseChange F E).obj G.val) R) :
    actualCubicPoints r R x = baseChangePoint F E G.val.X R x ≫ r.hom.hom.hom := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem actualCubicPoints_natural {R T : TestAlgebra E}
    (f : R ⟶ T) (x : SchemePoints ((groupBaseChange F E).obj G.val) R) :
    actualCubicPoints r T (mapPoints f x) =
      mapPoints ((restrictTestAlgebra F E).map f) (actualCubicPoints r R x) := by
  rw [actualCubicPoints_apply, actualCubicPoints_apply, baseChangePointsNaturality]
  exact Category.assoc _ _ _

private def cubicMarkedInclusion (R : TestAlgebra E) :
    (R ⊗[E] (Fin 8 → E)) →ₗ[R] (((restrictTestAlgebra F E).obj R) ⊗[F] J.V) :=
  let R₀ := (restrictTestAlgebra F E).obj R
  letI : Algebra F R := inferInstanceAs (Algebra F R₀)
  letI : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq' rfl
  (TensorProduct.AlgebraTensorModule.cancelBaseChange F E R R J.V).toLinearMap ∘ₗ
    (j₀.baseChange R)

private def cubicVectorAction (R : TestAlgebra E)
    (g : SchemePoints ((groupBaseChange F E).obj G.val) R) :=
  TrialitarianAlbertDescent.cubicStabilizerAction B ((restrictTestAlgebra F E).obj R)
    (actualCubicPoints r R g)

private theorem cubicVectorAction_natural {R T : TestAlgebra E}
    (f : R ⟶ T) (x : SchemePoints ((groupBaseChange F E).obj G.val) R)
    (v : ((restrictTestAlgebra F E).obj R) ⊗[F] J.V) :
    let i := TensorProduct.map ((restrictTestAlgebra F E).map f).hom.toLinearMap LinearMap.id
    i (cubicVectorAction r R x v) = cubicVectorAction r T (mapPoints f x) (i v) := by
  intro i
  unfold cubicVectorAction
  rw [actualCubicPoints_natural]
  exact cubicStabilizerAction_natural B ((restrictTestAlgebra F E).map f) (actualCubicPoints r R x) v

end

end ActualCubicAction

section SpinDescentUniqueness

open CategoryTheory

open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinInnerDescent (IsRegular)
open LinearAlgebraicGroups.Albert
open SpinSpecification (ScalarClifford coefficientMap)
open SpinFunctor (Spin vectorAction)
open private scalar_tensor_injective from LinearAlgebraicGroups.Albert.SpinFunctor
open scoped TensorProduct

private theorem spin_eq_of_vector_and_specialization {K V L : Type u} {I : Type w}
    [Field K] [AddCommGroup V] [Module K V] [LinearOrder I] [Fintype I]
    {R : TestAlgebra K} [IsDomain R] [Field L] [Algebra K L]
    (q : QuadraticForm K V) (hq : IsRegular q) (c : Module.Basis I K V)
    (a b : Spin q R c) (ha : vectorAction q R c a = vectorAction q R c b)
    (f : R ⟶ CommAlgCat.of K L)
    (hf : SpinFunctor.map q c f.hom a = SpinFunctor.map q c f.hom b) : a = b := by
  let v := a * b⁻¹
  have hv : vectorAction q R c v = 1 := by simp [v, ha]
  obtain ⟨t, ⟨ht, ht'⟩, _⟩ := (SpinFunctor.regular_vectorKernel q R c hq v).mp hv
  have hmap : SpinFunctor.map q c f.hom v = 1 := by simp [v, hf]
  have hs : f.hom t = 1 := by
    apply scalar_tensor_injective q L c
    have h := congrArg (fun x : Spin q L c => x.val.val) hmap
    change coefficientMap q R f.hom v.val.val = 1 at h
    rw [ht'] at h
    exact h
  have hsign : t = 1 ∨ t = -1 := by
    have h : (t - 1) * (t + 1) = 0 := by linear_combination ht
    exact (mul_eq_zero.mp h).imp (fun h => sub_eq_zero.mp h) (fun h => eq_neg_of_add_eq_zero_left h)
  have ht₁ : t = 1 := by
    rcases hsign with h | h
    · exact h
    · have hn : -(1 : L) = 1 := by simpa [h] using hs
      have hn₀ : -(1 : K) = 1 := (algebraMap K L).injective (by simpa using hn)
      exact h.trans (by simpa using congrArg (algebraMap K R) hn₀)
  have h₁ : v = 1 := by
    apply Subtype.ext
    apply Units.ext
    change v.val.val = 1
    rw [ht', ht₁, map_one]
  exact mul_inv_eq_one.mp h₁

end SpinDescentUniqueness

section SplitComparison

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open TrialitySpecification (Model modelOp mapModel)
open ZornSpecification (norm)
open SpinSpecification (SchemePoints)
open SpinFunctor (Spin vectorAction)
open CliffordSpecification (coefficientForm)
open Specs.Arithmetic.SpinScalarExtension (restricted vectorComparison)
open TrialitarianAlbertDescent (framePermutation framePermutation_unit framePermutation_operator
  framePermutation_diagonal)
open private framePermutation_block blockPermutation from
  LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent

noncomputable section

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [aFS : Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {G : AffineAlgebraicGroup F} {J : AlbertModel F} {B : CubicStabilizer J E}

private def markRotation (i : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.addRight (1 - i)

private theorem markRotation_apply (i : Fin 3) : markRotation i i = 1 := by
  fin_cases i <;> decide

private theorem markRotation_sign (i : Fin 3) : Equiv.Perm.sign (markRotation i) = 1 := by
  fin_cases i <;> decide

private theorem markRotation_block (i : Fin 3) (x : Zorn S) :
    framePermutation (markRotation i) (CubicSpecification.singleBlockCoordinates i x) = CubicSpecification.singleBlockCoordinates 1 x := by
  apply Prod.ext
  · funext j
    obtain ⟨a, rfl⟩ := (markRotation i).surjective j
    exact framePermutation_diagonal _ _ a
  · funext j
    obtain ⟨a, rfl⟩ := (markRotation i).surjective j
    rw [framePermutation_block]
    simp only [blockPermutation, markRotation_sign, ite_true]
    change Pi.single (M := fun _ : Fin 3 => Zorn S) i x a = Pi.single (M := fun _ : Fin 3 => Zorn S) 1 x (markRotation i a)
    by_cases h : a = i
    · subst a
      simp [markRotation_apply]
    · have h' : markRotation i a ≠ 1 := fun ha =>
        h ((markRotation i).injective (ha.trans (markRotation_apply i).symm))
      rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

private theorem mapModel_singleBlock (R : TestAlgebra S) (i : Fin 3) (z : Zorn S) :
    mapModel (algebraMap S R) (CubicSpecification.singleBlockCoordinates i z) =
      CubicSpecification.singleBlockCoordinates i (ZornSpecification.mapCoordinates (algebraMap S R) z) := by
  classical
  apply Prod.ext
  · funext j
    exact map_zero (algebraMap S R)
  · funext j
    by_cases h : j = i
    · subst j
      simp [mapModel, CubicSpecification.singleBlockCoordinates]
    · simp [mapModel, CubicSpecification.singleBlockCoordinates, Pi.single_eq_of_ne h,
        ZornSpecification.mapCoordinates]

private def blockInclusion (R : Type u) [CommRing R] (i : Fin 3) : Zorn R →ₗ[R] Model R where
  toFun := CubicSpecification.singleBlockCoordinates i
  map_add' x y := by classical simp [CubicSpecification.singleBlockCoordinates, Pi.single_add]
  map_smul' r x := by classical simp [CubicSpecification.singleBlockCoordinates, Pi.single_smul]

private theorem testOctonionCoordinates_tmul (d : S ⊗[E] (Fin 8 → E) ≃ₗ[S] Zorn S)
    (R : TestAlgebra S) (a : R) (v : Fin 8 → E) :
    testOctonionCoordinates d R (a ⊗ₜ[E] v) =
      a • ZornSpecification.mapCoordinates (algebraMap S R) (d (1 ⊗ₜ[E] v)) := by
  change Zorn.baseChange S R
    (d.baseChange S R _ _ ((vectorComparison R).symm (a ⊗ₜ[E] v))) = _
  unfold vectorComparison
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
    Zorn.baseChange_tmul]

set_option maxHeartbeats 1500000 in
private theorem splitComparison [Module.Finite F E] (degree : Module.finrank F E = 3)
    (n : (E →ₐ[F] S) ≃ Fin 3) (r : G.val ≅ B.stabilizer.group)
    (t : S ⊗[F] J.V ≃ₗ[S] Model S) (hu : t (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit)
    (hop : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (hd : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => n.symm i e, 0))
    (q : QuadraticForm E (Fin 8 → E)) (j₀ : (Fin 8 → E) →ₗ[E] E ⊗[F] J.V)
    (d : (coefficientForm S q (Pi.basisFun E (Fin 8))).IsometryEquiv (norm S))
    (hm : ∀ v, t (TensorProduct.map (IsScalarTower.toAlgHom F E S).toLinearMap
        LinearMap.id (j₀ v)) = CubicSpecification.singleBlockCoordinates (n (IsScalarTower.toAlgHom F E S)) (d (1 ⊗ₜ[E] v))) :
    ∃ P : ∀ R : TestAlgebra S, SchemePoints ((groupBaseChange F E).obj G.val) (restricted E R) ≃*
        Spin q (restricted E R) (Pi.basisFun E (Fin 8)),
      (∀ {R T : TestAlgebra S} (f : R ⟶ T) g,
        let a := (restrictTestAlgebra E S).map f
        P T (mapPoints a g) = SpinFunctor.map q (Pi.basisFun E (Fin 8)) a.hom (P R g)) ∧
      ∀ (R : TestAlgebra S) g x,
        cubicMarkedInclusion j₀ (restricted E R)
          (vectorAction q (restricted E R) (Pi.basisFun E (Fin 8)) (P R g) x) =
          cubicVectorAction r (restricted E R) g (cubicMarkedInclusion j₀ (restricted E R) x) := by
  have hFS : aFS = ((algebraMap E S).comp (algebraMap F E)).toAlgebra :=
    Algebra.algebra_ext _ _ (IsScalarTower.algebraMap_apply F E S)
  subst aFS
  letI : Algebra F S := ((algebraMap E S).comp (algebraMap F E)).toAlgebra
  letI : IsScalarTower F E S := IsScalarTower.of_algebraMap_eq' rfl
  let i := n (IsScalarTower.toAlgHom F E S)
  let p := markRotation i
  let t' := t.trans (framePermutation p)
  let n' := n.trans p
  have hu' : t' (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit := by
    change framePermutation p (t _) = _
    rw [hu, framePermutation_unit]
  have hop' (x y) : t' (J.law.op S x y) = modelOp (t' x) (t' y) := by
    change framePermutation p (t _) = modelOp (framePermutation p (t x)) (framePermutation p (t y))
    rw [hop, framePermutation_operator]
  have hd' (e : E) : t' (1 ⊗ₜ[F] B.diagonal e) = (fun i => n'.symm i e, 0) := by
    change framePermutation p (t _) = _
    rw [hd]
    apply Prod.ext <;> funext j <;> obtain ⟨k, rfl⟩ := p.surjective j
    · rw [framePermutation_diagonal]
      change n.symm k e = n.symm (p.symm (p k)) e
      rw [Equiv.symm_apply_apply]
    · rw [framePermutation_block]
      exact map_zero _
  have hm' (v : Fin 8 → E) : t' (TensorProduct.map (IsScalarTower.toAlgHom F E S).toLinearMap
        LinearMap.id (j₀ v)) = CubicSpecification.singleBlockCoordinates 1 (d (1 ⊗ₜ[E] v)) := by
    change framePermutation p (t _) = _
    rw [hm]
    exact markRotation_block i _
  have hIncl (R : TestAlgebra S) (x : restricted E R ⊗[E] (Fin 8 → E)) :
    markedChart t' R (cubicMarkedInclusion j₀ (restricted E R) x) =
      CubicSpecification.singleBlockCoordinates 1 (testOctonionCoordinates d.toLinearEquiv R x) := by
    letI : Algebra F (restricted E R) := inferInstanceAs (Algebra F (restricted F (restricted E R)))
    letI : IsScalarTower F E (restricted E R) := IsScalarTower.of_algebraMap_eq' rfl
    change markedChart t' R (cubicMarkedInclusion j₀ (restricted E R) x) =
      blockInclusion R 1 (testOctonionCoordinates d.toLinearEquiv R x)
    induction x using TensorProduct.inductionOn with
    | tmul a v =>
      rw [testOctonionCoordinates_tmul, map_smul]
      have h (w : E ⊗[F] J.V) :
          markedChart t' R
            (TensorProduct.AlgebraTensorModule.cancelBaseChange F E (restricted E R) (restricted E R)
              J.V (a ⊗ₜ[E] w)) =
            a • markedChart t' R (TensorProduct.map (extendToTest (F := F) R).toLinearMap
              LinearMap.id (TensorProduct.map (IsScalarTower.toAlgHom F E S).toLinearMap
                LinearMap.id w)) := by
        induction w using TensorProduct.inductionOn with
        | tmul b z =>
          rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
            AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, markedChart_tmul, markedChart_tmul]
          rw [smul_smul, mul_comm]
          rfl
        | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz, smul_add]
      change markedChart t' R
          (TensorProduct.AlgebraTensorModule.cancelBaseChange F E (restricted E R) (restricted E R)
            J.V (j₀.baseChange (restricted E R) (a ⊗ₜ[E] v))) = _
      rw [LinearMap.baseChange_tmul, h, markedChart_extend, hm', mapModel_singleBlock]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

  obtain ⟨C, hC, hCn⟩ := geometricFramePoints t' hu' hop' hd' degree
  let P (R : TestAlgebra S) := (actualCubicPoints r (restricted E R)).trans
    ((C R).trans (spinFrameComparison d R).symm)
  have hP (R : TestAlgebra S) (g : SchemePoints ((groupBaseChange F E).obj G.val) (restricted E R)) :
      spinFrameComparison d R (P R g) = C R (actualCubicPoints r (restricted E R) g) :=
    (spinFrameComparison d R).apply_symm_apply _
  refine ⟨P, ?_, ?_⟩
  · intro R T f g a
    letI : Algebra F R := inferInstanceAs (Algebra F (restrictField F R))
    letI : Algebra F T := inferInstanceAs (Algebra F (restrictField F T))
    apply (spinFrameComparison d T).injective
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    obtain ⟨y, rfl⟩ := (markedChart t' T).surjective z
    rw [hP, actualCubicPoints_natural]
    induction y using TensorProduct.inductionOn with
    | tmul b v =>
      have hz := markedChart_natural t' f (1 ⊗ₜ[F] v)
      dsimp only at hz
      rw [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply, map_one] at hz
      have hs : markedChart t' T (b ⊗ₜ[F] v) =
          b • mapModel f.hom.toRingHom (markedChart t' R (1 ⊗ₜ[F] v)) := by
        rw [hz, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, ← hCn f, ← spinFrameComparison_natural d f, hP]
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro R g x
    apply (markedChart t' R).injective
    rw [hIncl, ← spinFrameComparison_block d,
      ← hIncl, hP]
    exact hC R _ _

end

end SplitComparison

section Descent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.MonObj
open Specs (AffineAlgebraicGroup GroupScheme)
open Specs.AutomorphismSequence (relativePoints restrictIso)
open Specs.RelativeFormComparison (fieldTest fieldMap HopfConjugates)
open Specs.OctonionEquivariantAutomorphisms (affineTest)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.AdjointCocharacters (coordinateHopfIso)
open Specs.Arithmetic.SpinScalarExtension (restricted)
open Specs.Arithmetic.OddSpinInnerDescent (IsRegular)
open LinearAlgebraicGroups.Albert
open SpinSpecification (SchemePoints ScalarClifford spinUnits IsSpinPointRepresentation coefficientMap)
open SpinFunctor (Spin vectorAction)
open private mapVector fieldAlgebraInclusion relativeHom_ext_of_iso coordinateTest
  coordinateUniversalIso from LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
open private exists_relativeIso restrictIso_affine_apply galoisHom
  from LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
open private relativeSectionEquiv from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private extendedGroupIso extendedSpecIso_hom_fst extendedSpecIso_natural
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private schemeIsoEquiv schemeIsoEquiv_apply schemeIsoEquiv_ground
  from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private descend_standard_iso from LinearAlgebraicGroups.Descent.Forms

noncomputable section

variable {k K W : Type u} {I : Type w} [Field k] [Field K] [Algebra k K]
  [AddCommGroup W] [Module k W] [LinearOrder I] [Fintype I]
  {q : QuadraticForm k W} {b : Module.Basis I k W}

/-- Regard a test algebra with a specified scalar map as a test over the larger field. -/
private def scalarTest {R : TestAlgebra k} (f : CommAlgCat.of k K ⟶ R) : TestAlgebra K :=
  letI : Algebra K R := f.hom.toRingHom.toAlgebra
  CommAlgCat.of K R

private def scalarTestIso {R : TestAlgebra k} (f : CommAlgCat.of k K ⟶ R) :
    R ≅ restricted k (scalarTest f) :=
  let h : R ≃ₐ[k] restricted k (scalarTest f) :=
    { RingEquiv.refl R with commutes' := fun x => (f.hom.commutes x).symm }
  CommAlgCat.isoMk h

private def scalarTestMap {R T : TestAlgebra k} (f : CommAlgCat.of k K ⟶ R) (a : R ⟶ T) :
    scalarTest f ⟶ scalarTest (f ≫ a) :=
  ConcreteCategory.ofHom (C := CommAlgCat K)
    ({ a.hom.toRingHom with commutes' := fun _ => rfl } :
      scalarTest f →ₐ[K] scalarTest (f ≫ a))

private theorem scalarTest_naturality {R T : TestAlgebra k} (f : CommAlgCat.of k K ⟶ R)
    (a : R ⟶ T) :
    (scalarTestIso f).hom ≫ (restrictTestAlgebra k K).map (scalarTestMap f a) =
      a ≫ (scalarTestIso (f ≫ a)).hom := by
  apply CommAlgCat.hom_ext
  ext x
  rfl

private def mapTestEquiv (G : GroupScheme k) {R T : TestAlgebra k} (i : R ≅ T) :
    SchemePoints G R ≃* SchemePoints G T :=
  (((groupPointsFunctor k).obj G).mapIso i).groupIsoToMulEquiv

private def spinTestEquiv (q : QuadraticForm k W) (b : Module.Basis I k W)
    {R T : TestAlgebra k} (i : R ≅ T) : Spin q R b ≃* Spin q T b :=
  { SpinFunctor.map q b i.hom.hom with
    invFun := SpinFunctor.map q b i.inv.hom
    left_inv := fun x => by
      apply Subtype.ext
      apply Units.ext
      change coefficientMap q T i.inv.hom (coefficientMap q R i.hom.hom x.val.val) = x.val.val
      induction x.val.val using TensorProduct.inductionOn with
      | tmul r c =>
        change i.inv.hom (i.hom.hom r) ⊗ₜ[k] c = r ⊗ₜ[k] c
        rw [show i.inv.hom (i.hom.hom r) = r from ConcreteCategory.congr_hom i.hom_inv_id r]
      | add x y hx hy => simp only [map_add, hx, hy]
    right_inv := fun x => by
      apply Subtype.ext
      apply Units.ext
      change coefficientMap q R i.hom.hom (coefficientMap q T i.inv.hom x.val.val) = x.val.val
      induction x.val.val using TensorProduct.inductionOn with
      | tmul r c =>
        change i.hom.hom (i.inv.hom r) ⊗ₜ[k] c = r ⊗ₜ[k] c
        rw [show i.hom.hom (i.inv.hom r) = r from ConcreteCategory.congr_hom i.inv_hom_id r]
      | add x y hx hy => simp only [map_add, hx, hy] }

private theorem spinMap_comp {R T U : TestAlgebra k} (a : R ⟶ T) (c : T ⟶ U)
    (s : Spin q R b) :
    SpinFunctor.map q b (a ≫ c).hom s = SpinFunctor.map q b c.hom (SpinFunctor.map q b a.hom s) := by
  exact SpinFunctor.map_comp q b a.hom c.hom s

private def compareTest (G : GroupScheme k)
    (P : ∀ R : TestAlgebra K, SchemePoints G (restricted k R) ≃* Spin q (restricted k R) b)
    (R : TestAlgebra k) (f : CommAlgCat.of k K ⟶ R) :
    SchemePoints G R ≃* Spin q R b :=
  (mapTestEquiv G (scalarTestIso f)).trans ((P (scalarTest f)).trans (spinTestEquiv q b (scalarTestIso f)).symm)

private theorem compareTest_natural (G : GroupScheme k)
    (P : ∀ R : TestAlgebra K, SchemePoints G (restricted k R) ≃* Spin q (restricted k R) b)
    (hP : ∀ {R T : TestAlgebra K} (f : R ⟶ T) g,
        let a := (restrictTestAlgebra k K).map f
        P T (mapPoints a g) = SpinFunctor.map q b a.hom (P R g))
    {R T : TestAlgebra k} (f : CommAlgCat.of k K ⟶ R) (a : R ⟶ T)
    (g : SchemePoints G R) :
    compareTest G P T (f ≫ a) (mapPoints a g) =
      SpinFunctor.map q b a.hom (compareTest G P R f g) := by
  let i := scalarTestIso f
  let j := scalarTestIso (f ≫ a)
  let c := scalarTestMap f a
  let c₀ := (restrictTestAlgebra k K).map c
  apply (spinTestEquiv q b j).injective
  change (spinTestEquiv q b j)
      ((spinTestEquiv q b j).symm (P _ (mapPoints j.hom (mapPoints a g)))) =
    SpinFunctor.map q b j.hom.hom (SpinFunctor.map q b a.hom (compareTest G P R f g))
  rw [MulEquiv.apply_symm_apply, ← spinMap_comp, ← scalarTest_naturality f a, spinMap_comp]
  have hp : SpinFunctor.map q b i.hom.hom (compareTest G P R f g) =
      P _ (mapPoints i.hom g) := (spinTestEquiv q b i).apply_symm_apply _
  rw [hp, ← CocharacterDynamics.mapPoints_comp, ← scalarTest_naturality f a, CocharacterDynamics.mapPoints_comp]
  exact hP c _

private theorem markedInclusion_natural {F : Type u} [Field F] [Algebra F k]
    {J : TrialitarianAlbertDescentSpecification.AlbertModel F}
    (j₀ : (Fin 8 → k) →ₗ[k] k ⊗[F] J.V)
    {R T : TestAlgebra k} (a : R ⟶ T) (x : R ⊗[k] (Fin 8 → k)) :
    mapVector ((restrictTestAlgebra F k).map a) J.V (cubicMarkedInclusion j₀ R x) =
      cubicMarkedInclusion j₀ T (mapVector a _ x) := by
  letI : Algebra F R := inferInstanceAs (Algebra F (restricted F R))
  letI : Algebra F T := inferInstanceAs (Algebra F (restricted F T))
  letI : IsScalarTower F k R := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F k T := IsScalarTower.of_algebraMap_eq' rfl
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    simp only [cubicMarkedInclusion, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
      mapVector, TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply]
    induction j₀ v using TensorProduct.inductionOn with
    | tmul s w =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply, AlgHom.toLinearMap_apply]
      change a.hom (s • r) ⊗ₜ[F] w = (s • a.hom r) ⊗ₜ[F] w
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem mapVector_injective {R T : TestAlgebra k} (a : R ⟶ T)
    (ha : Function.Injective a.hom) (V : Type u) [AddCommGroup V] [Module k V] :
    Function.Injective (mapVector a V) :=
  Module.Flat.rTensor_preserves_injective_linearMap a.hom.toLinearMap ha

private theorem spinPointEquiv (H : GroupScheme k)
    (h : ∀ R : TestAlgebra k, SchemePoints H R →* (ScalarClifford q R)ˣ)
    (hh : IsSpinPointRepresentation q H h) (R : TestAlgebra k) :
    ∃ E : SchemePoints H R ≃* Spin q R b, ∀ x, (E x).val = h R x := by
  let e : SchemePoints H R →* Spin q R b :=
    (h R).codRestrict (SpinFunctor.spinSubgroup q R b) (fun x => by
      change h R x ∈ spinUnits q R
      rw [← (hh.1 R).2]
      exact ⟨x, rfl⟩)
  refine ⟨MulEquiv.ofBijective e ⟨fun x y hxy => (hh.1 R).1 (congrArg Subtype.val hxy), ?_⟩, fun x => rfl⟩
  intro s
  have hs : s.val ∈ spinUnits q R := s.property
  rw [← (hh.1 R).2] at hs
  obtain ⟨x, hx⟩ := hs
  exact ⟨x, Subtype.ext hx⟩

private theorem compareTest_vector {F : Type u} [Field F] [Algebra F k]
    {J : TrialitarianAlbertDescentSpecification.AlbertModel F}
    {B : TrialitarianAlbertDescentSpecification.CubicStabilizer J k}
    {G : AffineAlgebraicGroup F} (r : G.val ≅ B.stabilizer.group)
    (j₀ : (Fin 8 → k) →ₗ[k] k ⊗[F] J.V)
    (q : QuadraticForm k (Fin 8 → k)) (b : Module.Basis I k (Fin 8 → k))
    (P : ∀ R : TestAlgebra K, SchemePoints ((groupBaseChange F k).obj G.val) (restricted k R) ≃*
      Spin q (restricted k R) b)
    (hP : ∀ (R : TestAlgebra K) (g : SchemePoints ((groupBaseChange F k).obj G.val) (restricted k R))
        (x : restricted k R ⊗[k] (Fin 8 → k)), cubicMarkedInclusion j₀ (restricted k R)
        (vectorAction q (restricted k R) b (P R g) x) =
      cubicVectorAction r (restricted k R) g (cubicMarkedInclusion j₀ (restricted k R) x))
    (R : TestAlgebra k) (f : CommAlgCat.of k K ⟶ R) (g : SchemePoints ((groupBaseChange F k).obj G.val) R)
    (x : R ⊗[k] (Fin 8 → k)) :
    cubicMarkedInclusion j₀ R (vectorAction q R b (compareTest _ P R f g) x) =
      cubicVectorAction r R g (cubicMarkedInclusion j₀ R x) := by
  let i := scalarTestIso f
  let g' := mapPoints i.hom g
  let a := (restrictTestAlgebra F k).map i.hom
  apply mapVector_injective a (fun _ _ h => h) J.V
  have hnat := cubicVectorAction_natural r i.hom g (cubicMarkedInclusion j₀ R x)
  change mapVector a J.V _ =
    cubicVectorAction r (restricted k (scalarTest f)) g'
      (mapVector a J.V (cubicMarkedInclusion j₀ R x)) at hnat
  rw [markedInclusion_natural, hnat, markedInclusion_natural]
  have hmap : SpinFunctor.map q b i.hom.hom (compareTest _ P R f g) = P (scalarTest f) g' :=
    (spinTestEquiv q b i).apply_symm_apply _
  rw [show mapVector i.hom _ (vectorAction q R b _ x) = _ from
    SpinFunctor.vectorAction_naturality q b i.hom.hom _ x, hmap]
  exact hP _ _ _

private theorem markedInclusion_injective {F : Type u} [Field F] [Algebra F k]
    {J : TrialitarianAlbertDescentSpecification.AlbertModel F}
    (j₀ : (Fin 8 → k) →ₗ[k] k ⊗[F] J.V) (hj : Function.Injective j₀) (R : TestAlgebra k) :
    Function.Injective (cubicMarkedInclusion j₀ R) := by
  letI : Algebra F R := inferInstanceAs (Algebra F ((restrictTestAlgebra F k).obj R))
  letI : IsScalarTower F k R := IsScalarTower.of_algebraMap_eq' rfl
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange F k R R J.V).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap j₀ hj)

open private affineTest_hom from LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms

set_option backward.isDefEq.respectTransparency false in
private theorem universal_specializes (H : AffineAlgebraicGroup k) :
    let R := coordinateTest (S := K) (Specs.AdjointCocharacters.coordinateHopf H)
    let f := fieldAlgebraInclusion (k := k) R
    let U := affineTest f
    let x := relativeSectionEquiv U H.val.X (coordinateUniversalIso H).hom
    ∃ a : restricted k R ⟶ CommAlgCat.of k K, mapPoints a x = 1 := by
  intro R f U x
  let V := affineTest (𝟙 (CommAlgCat.of k K))
  let F := (fieldTest k K).iteratedSliceEquiv.functor
  let e := coordinateUniversalIso (S := K) H
  let v : V ⟶ U := F.preimage ((relativeSectionEquiv V H.val.X).symm 1 ≫ e.inv)
  obtain ⟨a, ha, _⟩ := affineTest_hom v
  refine ⟨a, ?_⟩
  change ((testSpec k).map a.op) ≫ x = 1
  rw [← ha]
  apply Over.OverMorphism.ext
  change (F.map v).left ≫ e.hom.left ≫ pullback.fst H.val.X.hom (fieldSpecMap k K) = _
  rw [Functor.map_preimage, Over.comp_left, Category.assoc]
  have he : e.inv.left ≫ e.hom.left ≫ pullback.fst H.val.X.hom (fieldSpecMap k K) =
      pullback.fst H.val.X.hom (fieldSpecMap k K) := by
    rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  rw [he]
  exact pullback.lift_fst ..

open private extendedIso from LinearAlgebraicGroups.Descent.Forms
open private hopfSchemeIso induced_iff from LinearAlgebraicGroups.Descent.RelativeFormComparison

private theorem descendRelativeIso [IsGalois k K] (G H : AffineAlgebraicGroup k)
    (i : relativePoints G.val (fieldTest k K) ≅ relativePoints H.val (fieldTest k K))
    (hi : ∀ σ : Gal(K/k), restrictIso (fieldMap k K σ) i = i) :
    ∃ j : G.val ≅ H.val, ∀ (U : Over (fieldTest k K)) (x : U.left ⟶ G.val.X),
      (i.hom.app (op U)).hom x = x ≫ j.hom.hom.hom := by
  let t := extendedGroupIso (k := k) K
  have ht : LinearAlgebraicGroups.Descent.Forms.IsScalarExtensionComparison t :=
    fun A => extendedSpecIso_hom_fst K A
  obtain ⟨e, he, heq⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.hopfIsomorphismComparison
    t ht (coordinateHopfIso G) (coordinateHopfIso H)
  let f := e.symm i
  have hf : e f = i := e.apply_symm_apply _
  have hf' (σ : Gal(K/k)) : HopfConjugates σ f f := by
    apply (heq σ f f).2
    rw [hf, hi]
  obtain ⟨f₀, h₀⟩ := descend_standard_iso f hf'
  let j := (coordinateHopfIso G).symm ≪≫ LinearAlgebraicGroups.Descent.Forms.spectrumIso f₀ ≪≫ coordinateHopfIso H
  have hf₀ : extendedIso K f₀ = f := Iso.ext h₀
  have hn : LinearAlgebraicGroups.Descent.Forms.spectrumIso f ≪≫ t _ =
      t _ ≪≫ (groupBaseChange k K).mapIso (LinearAlgebraicGroups.Descent.Forms.spectrumIso f₀) := by
    apply Iso.ext
    apply Grp.hom_ext
    rw [← hf₀]
    exact extendedSpecIso_natural K f₀.inv
  have hbase : hopfSchemeIso t (coordinateHopfIso G) (coordinateHopfIso H) f =
      (groupBaseChange k K).mapIso j := by
    change (t _ ≪≫ (groupBaseChange k K).mapIso (coordinateHopfIso G)).symm ≪≫
      LinearAlgebraicGroups.Descent.Forms.spectrumIso f ≪≫ t _ ≪≫
      (groupBaseChange k K).mapIso (coordinateHopfIso H) = _
    rw [← Iso.trans_assoc (LinearAlgebraicGroups.Descent.Forms.spectrumIso f), hn]
    simp [j, Iso.trans_assoc, Functor.mapIso_trans, Functor.mapIso_symm]
  have hind := (he f i).2 hf
  change Specs.RelativeFormComparison.IsInduced k K
      (hopfSchemeIso t (coordinateHopfIso G) (coordinateHopfIso H) f) i at hind
  rw [hbase] at hind
  have hi' := (induced_iff _ _).mp hind
  rw [schemeIsoEquiv_ground] at hi'
  refine ⟨j, ?_⟩
  intro U x
  rw [← hi']
  rfl

private theorem descendSpin [IsGalois k K] (G H : AffineAlgebraicGroup k)
    (h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford q R)ˣ)
    (hh : IsSpinPointRepresentation q H.val h)
    (qreg : IsRegular q)
    (hdomain : IsDomain (coordinateTest (S := K) (Specs.AdjointCocharacters.coordinateHopf G)))
    (P : ∀ (R : TestAlgebra k), (CommAlgCat.of k K ⟶ R) → SchemePoints G.val R ≃* Spin q R b)
    (hP : ∀ {R T : TestAlgebra k} (f : CommAlgCat.of k K ⟶ R) (a : R ⟶ T) (g : SchemePoints G.val R),
      P T (f ≫ a) (mapPoints a g) = SpinFunctor.map q b a.hom (P R f g))
    (hvec : ∀ (R : TestAlgebra k) (f g : CommAlgCat.of k K ⟶ R) (x : SchemePoints G.val R),
      vectorAction q R b (P R f x) = vectorAction q R b (P R g x)) :
    ∃ p : ∀ R : TestAlgebra k, SchemePoints G.val R →* (ScalarClifford q R)ˣ,
      IsSpinPointRepresentation q G.val p ∧
      ∀ R f x, p R x = (P R f x).val := by
  choose h' hh' using (spinPointEquiv (b := b) H.val h hh)
  have h'n {R T : TestAlgebra k} (a : R ⟶ T) (g : SchemePoints H.val R) :
      h' T (mapPoints a g) = SpinFunctor.map q b a.hom (h' R g) := by
    apply Subtype.ext
    rw [hh', show (SpinFunctor.map q b a.hom (h' R g)).val =
        Units.map (coefficientMap q R a.hom).toMonoidHom (h' R g).val from rfl, hh']
    exact hh.2 a g
  obtain ⟨i, hi⟩ := exists_relativeIso G.property.1 H.property.1
    (fun R f => (P R f).trans (h' R).symm) (by
      intro R T f a x
      apply (h' T).injective
      change h' T ((h' T).symm (P T (f ≫ a) (mapPoints a x))) =
        h' T (mapPoints a ((h' R).symm (P R f x)))
      rw [MulEquiv.apply_symm_apply, h'n, MulEquiv.apply_symm_apply, hP])
  have hinv (σ : Gal(K/k)) : restrictIso (fieldMap k K σ) i = i := by
    let R := coordinateTest (S := K) (Specs.AdjointCocharacters.coordinateHopf G)
    letI : IsDomain (restricted k R) := hdomain
    let f := fieldAlgebraInclusion (k := k) R
    let U := affineTest f
    let x := relativeSectionEquiv U G.val.X (coordinateUniversalIso G).hom
    obtain ⟨a, ha⟩ := universal_specializes (K := K) G
    apply Iso.ext
    apply relativeHom_ext_of_iso U (coordinateUniversalIso G)
    change ((restrictIso (fieldMap k K σ) i).hom.app (op (affineTest f))).hom x =
      (i.hom.app (op (affineTest f))).hom x
    rw [restrictIso_affine_apply, hi, hi]
    apply congrArg (h' (restricted k R)).symm
    refine spin_eq_of_vector_and_specialization (R := restricted k R)
      (L := K) q qreg b _ _ (hvec _ _ _ _) a ?_
    have evaluate (g : CommAlgCat.of k K ⟶ restricted k R) :=
      (hP g a x).symm.trans ((congrArg (P _ (g ≫ a)) ha).trans (map_one (P _ (g ≫ a))))
    exact (evaluate (galoisHom σ ≫ f)).trans (evaluate f).symm
  obtain ⟨j, hj⟩ := descendRelativeIso G H i hinv
  let C := (groupPointsFunctor k).mapIso j
  let c (R : TestAlgebra k) : SchemePoints G.val R ≃* SchemePoints H.val R := (C.app R).groupIsoToMulEquiv
  let p (R : TestAlgebra k) := (h R).comp (c R).toMonoidHom
  have hC (R : TestAlgebra k) (x : SchemePoints G.val R) : c R x = x ≫ j.hom.hom.hom := rfl
  refine ⟨p, ⟨fun R => ⟨(hh.1 R).1.comp ((c R).injective), ?_⟩, ?_⟩, ?_⟩
  · change Set.range (h R ∘ c R) = spinUnits q R
    rw [Set.range_comp, (c R).surjective.range_eq, Set.image_univ, (hh.1 R).2]
  · intro R T a x
    change h T (c T (mapPoints a x)) =
      Units.map (coefficientMap q R a.hom).toMonoidHom (h R (c R x))
    rw [hC, hC, mapPoints, Category.assoc]
    exact hh.2 a _
  · intro R f x
    change h R (c R x) = _
    rw [hC, ← hj (affineTest f), hi, ← hh', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

end

end Descent

section MarkedSpin

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.MonObj
open Specs (AffineAlgebraicGroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.Arithmetic.SpinScalarExtension (restricted)
open TrialitarianAlbertDescentSpecification
open Albert
open SpinSpecification (SchemePoints ScalarClifford vectors conjugate)
open private spin_scheme_of_form coordinateTest coordinateUniversalIso mapVector fieldAlgebraInclusion
  from LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
open private irreducible_of_geometricallyConnected from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private schemeIsoEquiv from LinearAlgebraicGroups.Descent.RelativeFormComparison

noncomputable section

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {G : AffineAlgebraicGroup F}

/-- The affine universal test of the split presentation has an integral coordinate ring. -/
private theorem markedCoordinateDomain (D : DiagramPresentation G E S) :
    IsDomain (coordinateTest (S := S) (Specs.AdjointCocharacters.coordinateHopf (baseChangedAlgebraicGroup E G))) := by
  let H := baseChangedAlgebraicGroup E G
  let L := baseChangedAlgebraicGroup S D.pinned.pair.G
  haveI : Smooth D.pinned.pair.G.val.X.hom := D.semisimple.1
  haveI : GeometricallyConnected D.pinned.pair.G.val.X.hom := D.semisimple.2.1
  haveI : Smooth L.val.X.hom :=
    inferInstanceAs (Smooth (pullback.snd D.pinned.pair.G.val.X.hom (fieldSpecMap F S)))
  haveI : GeometricallyConnected L.val.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd D.pinned.pair.G.val.X.hom (fieldSpecMap F S)))
  haveI : LocallyOfFiniteType L.val.X.hom := L.property.2.1
  haveI : QuasiCompact L.val.X.hom := L.property.2.2
  haveI : IrreducibleSpace L.val.X.left := irreducible_of_geometricallyConnected L.val
  haveI : IsReduced L.val.X.left := isReduced_of_smooth_over_field L.val.X.hom
  haveI : IsIntegral L.val.X.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have hm : fieldSpecMap E S ≫ fieldSpecMap F E = fieldSpecMap F S := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq F E S).symm
  let a : ((baseChange E S).obj H.val.X).left ≅ ((baseChange F S).obj G.val.X).left :=
    pullbackLeftPullbackSndIso G.val.X.hom (fieldSpecMap F E) (fieldSpecMap E S) ≪≫
      pullback.congrHom rfl hm
  let i := (schemeIsoEquiv S D.pinned.pair.G.val G.val).symm D.form
  let e : Spec (CommRingCat.of (coordinateTest (S := S) (Specs.AdjointCocharacters.coordinateHopf H))) ≅
      L.val.X.left :=
    (Over.forget _).mapIso (coordinateUniversalIso (S := S) H) ≪≫ a ≪≫
    (Over.forget _).mapIso ((Grp.forget _).mapIso i.symm)
  exact (affine_isIntegral_iff _).mp (IsIntegral.of_isIso e.inv)

set_option maxHeartbeats 1300000 in
theorem markedSpinComparison :
    Specs.Arithmetic.TrialitarianMarkedSpin.MarkedSpinComparison.{u} := by
  intro F E S _ _ _ _ _ _ _ _ _ _ degree G D J B r t hu hop hd q hq j₀ hj d hm
  letI : IsSepClosure E S :=
    ⟨IsSepClosure.sep_closed F, Algebra.isSeparable_tower_top_of_isSeparable F E S⟩
  let H := baseChangedAlgebraicGroup E G
  let b := Pi.basisFun E (Fin 8)
  obtain ⟨P, hPn, hPv⟩ := splitComparison degree D.numbering r t hu hop hd q j₀ d hm
  obtain ⟨Q, h, hh⟩ := spin_scheme_of_form q (b.reindex (Equiv.ulift.{u}).symm)
  let C := compareTest H.val P
  have hc (R : TestAlgebra E) (f : CommAlgCat.of E S ⟶ R)
      (g : SchemePoints H.val R) (x : R ⊗[E] (Fin 8 → E)) :
      cubicMarkedInclusion j₀ R (SpinFunctor.vectorAction q R b (C R f g) x) =
        cubicVectorAction r R g (cubicMarkedInclusion j₀ R x) :=
    compareTest_vector r j₀ q b P hPv R f g x
  obtain ⟨p, hp, hpC⟩ := descendSpin H Q h hh (Or.inl hq) (markedCoordinateDomain D) C
    (compareTest_natural H.val P hPn) (by
      intro R f f' g
      apply LinearEquiv.ext
      intro x
      exact markedInclusion_injective j₀ hj R ((hc R f g x).trans (hc R f' g x).symm))
  refine ⟨p, hp, ?_⟩
  intro R g
  dsimp only
  intro x
  let s : SpinFunctor.Spin q R b := ⟨p R g, by
    change p R g ∈ SpinSpecification.spinUnits q R
    rw [← (hp.1 R).2]
    exact ⟨g, rfl⟩⟩
  let y := SpinFunctor.vectorAction q R b s x
  have hact : cubicMarkedInclusion j₀ R y = cubicVectorAction r R g (cubicMarkedInclusion j₀ R x) := by
    let R' : TestAlgebra E := CommAlgCat.of E (S ⊗[E] R)
    let f : CommAlgCat.of E S ⟶ R' := CommAlgCat.ofHom
      (Algebra.TensorProduct.includeLeft : S →ₐ[E] S ⊗[E] R)
    let a : R ⟶ R' := CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight : R →ₐ[E] S ⊗[E] R)
    have ha : Function.Injective a.hom :=
      Algebra.TensorProduct.includeRight_injective (B := R) (algebraMap E S).injective
    let a₀ := (restrictTestAlgebra F E).map a
    apply mapVector_injective a₀ ha J.V
    have hn := cubicVectorAction_natural r a g (cubicMarkedInclusion j₀ R x)
    change mapVector a₀ J.V _ =
      cubicVectorAction r R' (mapPoints a g) (mapVector a₀ J.V (cubicMarkedInclusion j₀ R x)) at hn
    rw [markedInclusion_natural, hn, markedInclusion_natural]
    have hsa : SpinFunctor.map q b a.hom s = C R' f (mapPoints a g) := by
      apply Subtype.ext
      change Units.map (SpinSpecification.coefficientMap q R a.hom).toMonoidHom (p R g) = _
      rw [← hp.2 a g, hpC R' f]
    change cubicMarkedInclusion j₀ R' (mapVector a _ (SpinFunctor.vectorAction q R b s x)) = _
    rw [show mapVector a _ (SpinFunctor.vectorAction q R b s x) = _ from
      SpinFunctor.vectorAction_naturality q b a.hom s x, hsa]
    exact hc R' f _ _
  exact ⟨y, hact, SpinFunctor.vectorAction_characterization q R b s x⟩

end

end MarkedSpin

end LinearAlgebraicGroups.Arithmetic.TrialitarianMarkedSpin
