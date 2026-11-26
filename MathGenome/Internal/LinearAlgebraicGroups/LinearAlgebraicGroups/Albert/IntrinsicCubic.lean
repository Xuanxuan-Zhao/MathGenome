import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntrinsicCubic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.Tactic.ComputeDegree
import Mathlib.LinearAlgebra.Contraction

namespace LinearAlgebraicGroups.Albert

open IntrinsicCubicSpecification SplitSpecification HermitianSpecification
open LowerRankSpecification (untwisted)
open QuadraticOperatorSpecification (applyOperator)
open _root_.Specs.LinearAlgebraicGroups.Albert
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open _root_.LinearAlgebraicGroups.Composition TensorProduct
open scoped DualNumber

noncomputable section

universe u v

set_option linter.style.haveILetI false
set_option maxHeartbeats 900000

open private adjoint_coefficients opSquare cross_add cross_smul ground_operator tensorOperator_apply from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators
open private adjointCross_comm next_zero next_one next_two prev_zero prev_one prev_two from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CubicIdentities

section CharacteristicIdentity
variable {R : Type u} [CommRing R] {A : Type v} [NonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  {n : QuadraticForm R A} (γ : Fin 3 → Rˣ)

private theorem coordinate_characteristic (h : IsOctonionNorm n) (x : Coordinates R A) :
    applyOperator n γ x x =
      CubicSpecification.linearTrace n γ x • applyOperator n γ x CubicSpecification.cubicUnit -
        CubicSpecification.quadraticTrace n γ x • x + CubicSpecification.cubicNorm n γ x • (CubicSpecification.cubicUnit : Coordinates R A) := by
  let e : Coordinates R A := CubicSpecification.cubicUnit
  have hc := (adjoint_coefficients γ h x e).1
  change CubicSpecification.adjointCross n γ (CubicSpecification.cubicAdjoint n γ x) (CubicSpecification.adjointCross n γ x e) =
    CubicSpecification.cubicNorm n γ x • e + CubicSpecification.quadraticTrace n γ x • x at hc
  have he := (cubic_unit_identities (n := n) γ).2.2 x
  have hcomm (a b : Coordinates R A) :
      CubicSpecification.adjointCross n γ a b = CubicSpecification.adjointCross n γ b a :=
    adjointCross_comm γ a b
  have hadd (a b c : Coordinates R A) :
      CubicSpecification.adjointCross n γ a (b + c) =
        CubicSpecification.adjointCross n γ a b + CubicSpecification.adjointCross n γ a c :=
    cross_add γ a b c
  have hsmul (a b : Coordinates R A) (s : R) :
      CubicSpecification.adjointCross n γ a (s • b) = s • CubicSpecification.adjointCross n γ a b :=
    cross_smul γ a b s
  rw [hcomm x e] at hc
  change CubicSpecification.adjointCross n γ e x = CubicSpecification.linearTrace n γ x • e - x at he
  have he' : CubicSpecification.adjointCross n γ e (CubicSpecification.cubicAdjoint n γ x) =
      CubicSpecification.quadraticTrace n γ x • e - CubicSpecification.cubicAdjoint n γ x :=
    (cubic_unit_identities (n := n) γ).2.2 _
  rw [he, sub_eq_add_neg, hadd, hsmul, ← neg_one_smul R x, hsmul,
    neg_one_smul, hcomm (CubicSpecification.cubicAdjoint n γ x) e,
    he'] at hc
  have hdiag := quadraticTrace_polar (n := n) γ x x
  have hs : CubicSpecification.quadraticTrace n γ (x + x) = (4 : R) * CubicSpecification.quadraticTrace n γ x := by
    rw [← two_smul R x]
    obtain ⟨q, hq, _⟩ := cubicAdjoint_isQuadratic (n := n) γ
    simp only [CubicSpecification.quadraticTrace, ← hq, QuadraticMap.map_smul, map_smul,
      smul_eq_mul]
    ring
  change CubicSpecification.quadraticTrace n γ (x + x) - CubicSpecification.quadraticTrace n γ x - CubicSpecification.quadraticTrace n γ x =
    CubicSpecification.linearTrace n γ x * CubicSpecification.linearTrace n γ x - CubicSpecification.tracePairing n γ x x at hdiag
  rw [hs] at hdiag
  have hT : CubicSpecification.tracePairing n γ x x =
      CubicSpecification.linearTrace n γ x * CubicSpecification.linearTrace n γ x - 2 * CubicSpecification.quadraticTrace n γ x := by
    linear_combination hdiag
  rw [show applyOperator n γ x CubicSpecification.cubicUnit = _ from opSquare γ x]
  change CubicSpecification.tracePairing n γ x x • x - CubicSpecification.adjointCross n γ (CubicSpecification.cubicAdjoint n γ x) x =
    CubicSpecification.linearTrace n γ x • (CubicSpecification.cubicAdjoint n γ x + CubicSpecification.linearTrace n γ x • x -
      CubicSpecification.quadraticTrace n γ x • e) - CubicSpecification.quadraticTrace n γ x • x + CubicSpecification.cubicNorm n γ x • e
  rw [hT]
  change CubicSpecification.linearTrace n γ x • (CubicSpecification.quadraticTrace n γ x • e - CubicSpecification.cubicAdjoint n γ x) +
    -CubicSpecification.adjointCross n γ (CubicSpecification.cubicAdjoint n γ x) x =
    CubicSpecification.cubicNorm n γ x • e + CubicSpecification.quadraticTrace n γ x • x at hc
  have heq := eq_sub_of_add_eq' hc
  rw [sub_eq_add_neg, heq]
  module

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem coordinate_square_diagonal (x : Coordinates R A) (i : Fin 3) :
    (applyOperator n γ x CubicSpecification.cubicUnit).1 i =
      x.1 i ^ 2 +
      (CubicSpecification.blockWeight γ (HermitianSpecification.cyclicNext i) * n (x.2 (HermitianSpecification.cyclicNext i)) +
       CubicSpecification.blockWeight γ (HermitianSpecification.cyclicPrev i) * n (x.2 (HermitianSpecification.cyclicPrev i))) := by
  rw [show applyOperator n γ x CubicSpecification.cubicUnit = _ from opSquare γ x]
  have ht := linearTrace_apply (n := n) γ x
  have hs : CubicSpecification.quadraticTrace n γ x = ∑ j, (CubicSpecification.cubicAdjoint n γ x).1 j :=
    linearTrace_apply γ _
  simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, ht, hs,
    CubicSpecification.cubicUnit, mul_one, CubicSpecification.cubicAdjoint]
  have hi : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases hi i with rfl | rfl | rfl <;>
    simp only [Fin.sum_univ_three, next_zero, next_one, next_two, prev_zero, prev_one, prev_two] <;>
    ring

end CharacteristicIdentity

section SplitCoordinates

variable {B C : Type u} [CommRing B] [CommRing C]

private abbrev Model (B : Type u) [CommRing B] := SplitRank.octonion.Model B
private abbrev modelNorm (B : Type u) [CommRing B] := SplitRank.norm B .octonion

private def mapModel (f : B →+* C) (x : Model B) : Model C :=
  (fun i => f (x.1 i), fun i => ZornSpecification.mapCoordinates f (x.2 i))

private theorem mapModel_add (f : B →+* C) (x y : Model B) :
    mapModel f (x + y) = mapModel f x + mapModel f y := by
  apply Prod.ext
  · funext i; exact map_add f _ _
  · funext i
    apply (Zorn.coordinates C).injective
    simp [mapModel, ZornSpecification.mapCoordinates, Function.comp_def, Pi.add_def]

private theorem mapModel_unit (f : B →+* C) :
    mapModel f (CubicSpecification.cubicUnit : Model B) = (CubicSpecification.cubicUnit : Model C) := by
  apply Prod.ext
  · funext i; exact map_one f
  · funext i
    apply (Zorn.coordinates C).injective
    simp [mapModel, ZornSpecification.mapCoordinates, CubicSpecification.cubicUnit,
      Function.comp_def, Pi.zero_def]

variable [Algebra B C]

variable (B C) in
private def modelBaseChange : (C ⊗[B] Model B) ≃ₗ[C] Model C :=
  (coordinatesBaseChange C).trans ((LinearEquiv.refl C (Fin 3 → C)).prodCongr
    (LinearEquiv.piCongrRight fun _ => Zorn.baseChange B C))

private theorem modelBaseChange_tmul (a : C) (x : Model B) :
    modelBaseChange B C (a ⊗ₜ[B] x) = a • mapModel (algebraMap B C) x := by
  unfold modelBaseChange
  rw [LinearEquiv.trans_apply, coordinatesBaseChange_tmul]
  exact Prod.ext rfl (funext fun i => Zorn.baseChange_tmul a (x.2 i))

open private zorn_hermitian_transport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitModel

private theorem modelBaseChange_operator (x y : C ⊗[B] Model B) :
    modelBaseChange B C ((weightedHermitianJordan (untwisted B) (Zorn.isOctonion B)).op C x y) =
      applyOperator (modelNorm C) (untwisted C) (modelBaseChange B C x) (modelBaseChange B C y) := by
  let H := Zorn.baseChange B C
  let q := Composition.Specification.normBaseChange C (Zorn.norm B)
  let G : Model C ≃ₗ[C] Coordinates C (C ⊗[B] Zorn B) :=
    (LinearEquiv.refl C (Fin 3 → C)).prodCongr (LinearEquiv.piCongrRight fun _ => H.symm)
  let F : Composition.PeirceSpecification.ZornIsomorphism q :=
    ⟨H.symm,
      H.symm_apply_eq.mpr (Zorn.baseChange_one (R := B) (S := C)).symm,
      fun a b => H.injective (by
        rw [H.apply_symm_apply, Zorn.baseChange_mul, H.apply_symm_apply, H.apply_symm_apply]),
      fun a => by
        exact (DFunLike.congr_fun (Zorn.baseChange_norm (R := B) (S := C)) (H.symm a)).trans
          (congrArg (Zorn.norm C) (H.apply_symm_apply a))⟩
  have w : HermitianSpecification.baseChangedWeights C (untwisted B) = untwisted C := by
    funext i
    exact map_one (Units.map (algebraMap B C).toMonoidHom)
  have h := (zorn_hermitian_transport F (untwisted C)).2
    (modelBaseChange B C x) (modelBaseChange B C y)
  have hF (z : C ⊗[B] Model B) :
      G (modelBaseChange B C z) = coordinatesBaseChange C z := by
    apply Prod.ext
    · rfl
    · funext i
      exact H.symm_apply_apply ((coordinatesBaseChange C z).2 i)
  change G
    (applyOperator (modelNorm C) (untwisted C) (modelBaseChange B C x) (modelBaseChange B C y)) =
      applyOperator q (untwisted C) (G (modelBaseChange B C x))
        (G (modelBaseChange B C y)) at h
  apply (G).injective
  rw [h, hF, hF, hF, ← w]
  exact tensorOperator_apply (untwisted B) (Zorn.isOctonion B) C x y

end SplitCoordinates

section ChartExtensions

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {J : ParaQuadratic R M}
  {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

private abbrev pointMap (f : B →ₐ[R] C) := f.toLinearMap.rTensor M

private theorem pointMap_smul (f : B →ₐ[R] C) (b : B) (x : B ⊗[R] M) :
    pointMap (M := M) f (b • x) = f b • pointMap (M := M) f x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

private theorem pointMap_comp {D : Type u} [CommRing D] [Algebra R D]
    (g : C →ₐ[R] D) (f : B →ₐ[R] C) (x : B ⊗[R] M) :
    pointMap (M := M) g (pointMap (M := M) f x) = pointMap (M := M) (g.comp f) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy => simp [hx, hy]

private theorem pointMap_id (x : B ⊗[R] M) :
    pointMap (M := M) (AlgHom.id R B) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy => simp [hx, hy]

private theorem baseChange_cancel_op {B C : Type u} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [aRC : Algebra R C] [IsScalarTower R B C]
    (x y : C ⊗[B] (B ⊗[R] M)) :
    let E := AlgebraTensorModule.cancelBaseChange R B C C M
    E ((J.baseChange B).op C x y) = J.op C (E x) (E y) := by
  have ha : aRC = towerAlgebra R B C :=
    Algebra.algebra_ext _ _ (fun r => IsScalarTower.algebraMap_apply R B C r)
  subst aRC
  exact J.extendedOp_apply B C x y

private def extendChart (c : SplitChart J B) (f : B →ₐ[R] C) :
    SplitChart J C := by
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let E := AlgebraTensorModule.cancelBaseChange R B C C M
  let K := weightedHermitianJordan (untwisted B) (Zorn.isOctonion B)
  let H := c.coordinates.baseChange B C _ _
  let G := E.symm.trans (H.trans (modelBaseChange B C))
  have hg : (J.baseChange B).IsGroundIso (ParaQuadratic.ofJordan K) c.coordinates := by
    refine ⟨?_, fun x y => ?_⟩
    · exact c.unit
    · rw [ParaQuadratic.groundOp_baseChange]
      exact (c.op x y).trans (ground_operator _ _ _ _).symm
  have hi := ((J.baseChange B).isIso_iff_ground (ParaQuadratic.ofJordan K) c.coordinates).2 hg
  have hop (x y : C ⊗[B] (B ⊗[R] M)) :
      E ((J.baseChange B).op C x y) = J.op C (E x) (E y) := by
    exact baseChange_cancel_op x y
  have hunit : E (1 ⊗ₜ[B] (1 ⊗ₜ[R] J.unit)) = 1 ⊗ₜ[R] J.unit := by
    simp [E, AlgebraTensorModule.cancelBaseChange_tmul]
  refine ⟨G, ?_, fun x y => ?_⟩
  · change modelBaseChange B C (H (E.symm (1 ⊗ₜ[R] J.unit))) = CubicSpecification.cubicUnit
    rw [← hunit, E.symm_apply_apply, LinearEquiv.baseChange_tmul, c.unit,
      modelBaseChange_tmul, one_smul, mapModel_unit]
  · obtain ⟨x, rfl⟩ := E.surjective x
    obtain ⟨y, rfl⟩ := E.surjective y
    simp only [G, LinearEquiv.trans_apply, E.symm_apply_apply]
    rw [← hop, E.symm_apply_apply]
    change modelBaseChange B C (H ((J.baseChange B).op C x y)) = _
    rw [show H ((J.baseChange B).op C x y) = K.op C (H x) (H y) from hi.2 C x y]
    exact modelBaseChange_operator _ _

private theorem extendChart_apply (c : SplitChart J B) (f : B →ₐ[R] C) (x : B ⊗[R] M) :
    (extendChart c f).coordinates (pointMap (M := M) f x) =
      mapModel f.toRingHom (c.coordinates x) := by
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let E := AlgebraTensorModule.cancelBaseChange R B C C M
  have h : E (1 ⊗ₜ[B] x) = pointMap (M := M) f x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      rw [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul,
        Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
  change modelBaseChange B C (c.coordinates.baseChange B C _ _
    (E.symm (pointMap (M := M) f x))) = _
  rw [← h, E.symm_apply_apply, LinearEquiv.baseChange_tmul, modelBaseChange_tmul, one_smul]
  rfl

end ChartExtensions

section Coefficients

open Polynomial

variable {B E : Type u} [CommRing B] [CommRing E]

private def splitCoefficients (x : Model B) : B × B × B :=
  (CubicSpecification.linearTrace (modelNorm B) (untwisted B) x,
    CubicSpecification.quadraticTrace (modelNorm B) (untwisted B) x,
    CubicSpecification.cubicNorm (modelNorm B) (untwisted B) x)

private theorem mapModel_coefficients (f : B →+* E) (x : Model B) :
    splitCoefficients (mapModel f x) = Prod.map f (Prod.map f f) (splitCoefficients x) := by
  have hn (a : Zorn B) :
      modelNorm E (ZornSpecification.mapCoordinates f a) = f (modelNorm B a) :=
    Zorn.mapCoordinates_norm f a
  have ht (a : Zorn B) :
      Composition.AdjointSpecification.trace (modelNorm E) (ZornSpecification.mapCoordinates f a) =
        f (Composition.AdjointSpecification.trace (modelNorm B) a) := by
    simp only [Composition.AdjointSpecification.trace, LinearMap.flip_apply,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    have h1 : ZornSpecification.mapCoordinates f (1 : Zorn B) = 1 := by
      apply (Zorn.coordinates E).injective
      simp [ZornSpecification.mapCoordinates, Function.comp_def, Specification.zornUnit, Pi.zero_def]
    have ha : ZornSpecification.mapCoordinates f (a + 1) =
        ZornSpecification.mapCoordinates f a + 1 := by
      rw [← h1]
      apply (Zorn.coordinates E).injective
      simp [ZornSpecification.mapCoordinates, Function.comp_def, Pi.add_def]
    rw [← ha, ← h1, hn, hn, hn, map_sub, map_sub]
  have hw (D : Type u) [CommRing D] (i : Fin 3) :
      CubicSpecification.blockWeight (untwisted D) i = 1 := by
    simp [CubicSpecification.blockWeight, LowerRankSpecification.untwisted]
  have hp (D : Type u) [CommRing D] :
      CubicSpecification.weightProduct (untwisted D) = 1 := by
    simp [CubicSpecification.weightProduct, LowerRankSpecification.untwisted]
  apply Prod.ext
  · simp [splitCoefficients, linearTrace_apply, mapModel, map_sum]
  · apply Prod.ext
    · simp only [splitCoefficients, Prod.map_snd, Prod.map_fst,
        CubicSpecification.quadraticTrace, linearTrace_apply, CubicSpecification.cubicAdjoint,
        hw, one_mul, mapModel, hn, map_sum, map_sub, map_mul]
    · simp only [splitCoefficients, Prod.map_snd, CubicSpecification.cubicNorm, hw, hp, one_mul,
        mapModel, hn, ← Zorn.mapCoordinates_mul, ht, map_sum, map_add, map_sub, map_mul]

private theorem monic_diagonal_determinant [Nontrivial B] (a b c k l m : B) :
    Monic
      (((X + C b - C a) *
          ((X ^ 2 + C c) ^ 2 + C m - ((C a) ^ 2 + C k))) -
        ((X ^ 2 + C c - C a) *
          ((X + C b) ^ 2 + C l - ((C a) ^ 2 + C k)))) := by
  have h₁ : IsMonicOfDegree (X + C b - C a) 1 := by
    rw [add_sub_assoc, ← map_sub]
    exact isMonicOfDegree_X_add_one (b - a)
  have h₂ : IsMonicOfDegree ((X ^ 2 + C c) ^ 2 + C m - ((C a) ^ 2 + C k)) 4 := by
    have h : IsMonicOfDegree (X ^ 2 + C c) 2 :=
      (isMonicOfDegree_X_pow B 2).add_right (by simp)
    rw [add_sub_assoc]
    apply (h.pow 2).add_right
    have he : C m - ((C a) ^ 2 + C k) = C (m - (a ^ 2 + k)) := by simp
    rw [he, natDegree_C]
    decide
  have h₃ : ((X ^ 2 + C c - C a) *
          ((X + C b) ^ 2 + C l - ((C a) ^ 2 + C k))).natDegree < 5 := by
    have h : ((X ^ 2 + C c - C a) *
          ((X + C b) ^ 2 + C l - ((C a) ^ 2 + C k))).natDegree ≤ 4 := by
      compute_degree!
    exact h.trans_lt (by decide)
  exact ((h₁.mul h₂).sub h₃).monic

private def diagonalPerturbation : Model B[X] :=
  CubicSpecification.diagonalCoordinates ![0, X, X ^ 2]

private theorem perturbed_independent (x : Model B) (r s t : B[X]) :
    let z := mapModel (C : B →+* B[X]) x + diagonalPerturbation
    r • applyOperator (modelNorm B[X]) (untwisted B[X]) z CubicSpecification.cubicUnit + s • z +
      t • (CubicSpecification.cubicUnit : Model B[X]) = 0 → r = 0 ∧ s = 0 ∧ t = 0 := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  dsimp only
  set z := mapModel (C : B →+* B[X]) x + diagonalPerturbation
  let a := x.1 0
  let b := x.1 1
  let c := x.1 2
  let k := modelNorm B (x.2 1) + modelNorm B (x.2 2)
  let l := modelNorm B (x.2 2) + modelNorm B (x.2 0)
  let m := modelNorm B (x.2 0) + modelNorm B (x.2 1)
  let u₀ : B[X] := C a
  let u₁ : B[X] := X + C b
  let u₂ : B[X] := X ^ 2 + C c
  have h₀ : z.1 0 = u₀ := by simp [z, mapModel, diagonalPerturbation, CubicSpecification.diagonalCoordinates, u₀, a, Matrix.vecHead]
  have h₁ : z.1 1 = u₁ := by simp [z, mapModel, diagonalPerturbation, CubicSpecification.diagonalCoordinates, u₁, b, add_comm, Matrix.vecHead, Matrix.vecTail]
  have h₂ : z.1 2 = u₂ := by simp [z, mapModel, diagonalPerturbation, CubicSpecification.diagonalCoordinates, u₂, c, add_comm, Matrix.vecHead, Matrix.vecTail]
  have hn (i : Fin 3) : modelNorm B[X] (z.2 i) = C (modelNorm B (x.2 i)) := by
    change Zorn.norm B[X] (ZornSpecification.mapCoordinates (C : B →+* B[X]) (x.2 i) + 0) = _
    rw [add_zero, Zorn.mapCoordinates_norm]
    rfl
  have hw (i : Fin 3) : CubicSpecification.blockWeight (untwisted B[X]) i = 1 := by
    simp [CubicSpecification.blockWeight, LowerRankSpecification.untwisted]
  let q := applyOperator (modelNorm B[X]) (untwisted B[X]) z CubicSpecification.cubicUnit
  have q₀ : q.1 0 = u₀ ^ 2 + C k := by
    rw [coordinate_square_diagonal, next_zero, prev_zero, h₀, hn, hn, hw, hw]
    simp [k]
  have q₁ : q.1 1 = u₁ ^ 2 + C l := by
    rw [coordinate_square_diagonal, next_one, prev_one, h₁, hn, hn, hw, hw]
    simp [l]
  have q₂ : q.1 2 = u₂ ^ 2 + C m := by
    rw [coordinate_square_diagonal, next_two, prev_two, h₂, hn, hn, hw, hw]
    simp [m]
  intro hz
  have hi (i : Fin 3) : r * q.1 i + s * z.1 i + t = 0 := by
    simpa [q, CubicSpecification.cubicUnit] using congrArg (fun w : Model B[X] => w.1 i) hz
  have e₀ := hi 0
  have e₁ := hi 1
  have e₂ := hi 2
  rw [q₀, h₀] at e₀
  rw [q₁, h₁] at e₁
  rw [q₂, h₂] at e₂
  have hd := monic_diagonal_determinant a b c k l m
  change Monic ((u₁ - u₀) * (u₂ ^ 2 + C m - (u₀ ^ 2 + C k)) -
     (u₂ - u₀) * (u₁ ^ 2 + C l - (u₀ ^ 2 + C k))) at hd
  have hr : r = 0 := by
    apply hd.isRegular.left
    linear_combination (u₁ - u₀) * e₂ - (u₂ - u₀) * e₁ + (u₂ - u₁) * e₀
  have hm : Monic (u₁ - u₀) := by
    change (X + C b - C a).Monic
    rw [add_sub_assoc, ← map_sub]
    exact (isMonicOfDegree_X_add_one (b - a)).monic
  have hs : s = 0 := by
    apply hm.isRegular.left
    linear_combination e₁ - e₀ - (u₁ ^ 2 + C l - (u₀ ^ 2 + C k)) * hr
  exact ⟨hr, hs, by simpa [hr, hs] using e₀⟩

end Coefficients

section Uniqueness

open Polynomial

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {J : ParaQuadratic R M}
  {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

private def chartCoefficients (c : SplitChart J B) (x : B ⊗[R] M) : B × B × B :=
  splitCoefficients (c.coordinates x)

private def lawCoefficients (F : Coefficients R M) (x : B ⊗[R] M) : B × B × B :=
  (F.trace.eval B x, F.quadraticTrace.eval B x, F.norm.eval B x)

private def characteristicAt (x : B ⊗[R] M) (a : B × B × B) : Prop :=
  J.op B x x = a.1 • J.op B x (1 ⊗ₜ[R] J.unit) - a.2.1 • x +
    a.2.2 • (1 ⊗ₜ[R] J.unit)

private theorem chart_characteristic (c : SplitChart J B) (x : B ⊗[R] M) :
    characteristicAt (J := J) x (chartCoefficients c x) := by
  unfold characteristicAt
  apply c.coordinates.injective
  simp only [map_add, map_sub, map_smul, c.op, c.unit]
  exact coordinate_characteristic (untwisted B) (Zorn.isOctonion B) (c.coordinates x)

private theorem chart_extend_coefficients (c : SplitChart J B) (f : B →ₐ[R] C) (x : B ⊗[R] M) :
    chartCoefficients (extendChart c f) (pointMap (M := M) f x) =
      Prod.map f (Prod.map f f) (chartCoefficients c x) := by
  unfold chartCoefficients
  rw [extendChart_apply]
  exact mapModel_coefficients f.toRingHom _

private theorem law_coefficients_natural (F : Coefficients R M) (f : B →ₐ[R] C) (x : B ⊗[R] M) :
    lawCoefficients F (pointMap (M := M) f x) = Prod.map f (Prod.map f f) (lawCoefficients F x) := by
  simp [lawCoefficients, F.trace.natural, F.quadraticTrace.natural, F.norm.natural]

private def evalPolynomial (b : B) : B[X] →ₐ[R] B :=
  eval₂AlgHom (AlgHom.id R B) b (fun _ => Commute.all _ _)

private theorem evalPolynomial_comp_C (b : B) :
    (evalPolynomial (R := R) b).comp CAlgHom = AlgHom.id R B := by
  ext a
  simp [evalPolynomial]

/-- Perturb any given point by the diagonal (0, X, X²). At this point the
three coefficient vectors are independent, and evaluation at zero recovers the given point. -/
private theorem polynomial_test (c : SplitChart J B) (x : B ⊗[R] M) :
    ∃ y : B[X] ⊗[R] M, pointMap (M := M) (evalPolynomial 0) y = x ∧
      ∀ a b : B[X] × B[X] × B[X],
        characteristicAt (J := J) y a → characteristicAt (J := J) y b → a = b := by
  let f : B →ₐ[R] B[X] := CAlgHom
  let g : B[X] →ₐ[R] B := evalPolynomial 0
  let d := extendChart c f
  let p : Model B[X] := diagonalPerturbation
  let y := pointMap (M := M) f x + d.coordinates.symm p
  have hz : d.coordinates y = mapModel (C : B →+* B[X]) (c.coordinates x) + p := by
    dsimp only [y]
    rw [map_add, extendChart_apply, LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨y, ?_, ?_⟩
  · have hp : pointMap (M := M) g (d.coordinates.symm p) = 0 := by
      apply (extendChart d g).coordinates.injective
      rw [extendChart_apply, LinearEquiv.apply_symm_apply, map_zero]
      apply Prod.ext
      · funext i
        fin_cases i <;> simp [p, diagonalPerturbation, CubicSpecification.diagonalCoordinates, mapModel, g,
          evalPolynomial]
      · funext i
        apply (Zorn.coordinates B).injective
        simp [p, diagonalPerturbation, CubicSpecification.diagonalCoordinates, mapModel,
          ZornSpecification.mapCoordinates, Function.comp_def, Pi.zero_def]
    simp only [y, map_add, hp, add_zero, pointMap_comp, g, f, evalPolynomial_comp_C, pointMap_id]
  · intro a b ha hb
    have ha' := congrArg d.coordinates ha
    have hb' := congrArg d.coordinates hb
    let z := d.coordinates y
    let q := applyOperator (modelNorm B[X]) (untwisted B[X]) z CubicSpecification.cubicUnit
    have he :
        (a.1 - b.1) • q + (b.2.1 - a.2.1) • z +
          (a.2.2 - b.2.2) • (CubicSpecification.cubicUnit : Model B[X]) = 0 := by
      unfold characteristicAt at ha hb
      change d.coordinates (J.op B[X] y y) = _ at ha' hb'
      simp only [map_add, map_sub, map_smul, d.op, d.unit] at ha' hb'
      have hh := ha'.symm.trans hb'
      change a.1 • q - a.2.1 • z + a.2.2 • (CubicSpecification.cubicUnit : Model B[X]) =
        b.1 • q - b.2.1 • z + b.2.2 • (CubicSpecification.cubicUnit : Model B[X]) at hh
      rw [← sub_eq_zero] at hh
      rw [← hh]
      module
    change (a.1 - b.1) • applyOperator (modelNorm B[X]) (untwisted B[X]) (d.coordinates y) CubicSpecification.cubicUnit +
      (b.2.1 - a.2.1) • d.coordinates y + (a.2.2 - b.2.2) • (CubicSpecification.cubicUnit : Model B[X]) = 0 at he
    rw [hz] at he
    obtain ⟨h₁, h₂, h₃⟩ := perturbed_independent (c.coordinates x) _ _ _ he
    exact Prod.ext (sub_eq_zero.mp h₁)
      (Prod.ext (sub_eq_zero.mp h₂).symm (sub_eq_zero.mp h₃))

private theorem charts_agree (c d : SplitChart J B) (x : B ⊗[R] M) :
    chartCoefficients c x = chartCoefficients d x := by
  obtain ⟨y, hy, hu⟩ := polynomial_test c x
  let g : B[X] →ₐ[R] B := evalPolynomial 0
  let c' := extendChart (extendChart c (CAlgHom (R := R))) g
  let d' := extendChart (extendChart d (CAlgHom (R := R))) g
  have ret (e : SplitChart J B) (w : B ⊗[R] M) :
      (extendChart (extendChart e (CAlgHom (R := R))) g).coordinates w = e.coordinates w := by
    have h : pointMap (M := M) g (pointMap (M := M) (CAlgHom (R := R)) w) = w := by
      rw [pointMap_comp, show g.comp CAlgHom = _ from evalPolynomial_comp_C _, pointMap_id]
    conv_lhs => rw [← h, extendChart_apply, extendChart_apply]
    apply Prod.ext
    · funext i
      simp [mapModel, g, evalPolynomial]
    · funext i
      apply (Zorn.coordinates B).injective
      simp [mapModel, ZornSpecification.mapCoordinates, g, evalPolynomial, Function.comp_def]
  have h := hu _ _
    (chart_characteristic (extendChart c (CAlgHom (R := R))) y)
    (chart_characteristic (extendChart d (CAlgHom (R := R))) y)
  have h' := congrArg (Prod.map g (Prod.map g g)) h
  rw [← chart_extend_coefficients, ← chart_extend_coefficients, show pointMap (M := M) g y = x from hy] at h'
  change chartCoefficients c' x = chartCoefficients d' x at h'
  simpa only [chartCoefficients, c', d', ret] using h'

private theorem law_agrees_chart (F : Coefficients R M) (hF : IsCharacteristic J F)
    (c : SplitChart J B) (x : B ⊗[R] M) :
    lawCoefficients F x = chartCoefficients c x := by
  obtain ⟨y, hy, hu⟩ := polynomial_test c x
  let g : B[X] →ₐ[R] B := evalPolynomial 0
  have hF' : characteristicAt (J := J) y (lawCoefficients F y) := hF (B[X]) y
  have h := hu (lawCoefficients F y) _ hF'
    (chart_characteristic (extendChart c (CAlgHom (R := R))) y)
  have h' := congrArg (Prod.map g (Prod.map g g)) h
  rw [← law_coefficients_natural, ← chart_extend_coefficients,
    show pointMap (M := M) g y = x from hy] at h'
  exact h'.trans (charts_agree _ _ x)

end Uniqueness

section Descent

open Algebra.TensorProduct (includeLeft includeRight)

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {J : ParaQuadratic R M} {S B C : Type u} [CommRing S] [CommRing B] [CommRing C]
  [Algebra R S] [Algebra R B] [Algebra R C]

private theorem cover_point_injective [Module.Flat R M] [Module.FaithfullyFlat R S] :
    Function.Injective (pointMap (M := M) (includeLeft : B →ₐ[R] B ⊗[R] S)) := by
  apply Module.Flat.rTensor_preserves_injective_linearMap
  exact FaithfulSMul.algebraMap_injective B (B ⊗[R] S)

private def coverCoefficients (c : SplitChart J S) (x : B ⊗[R] M) :
    (B ⊗[R] S) × (B ⊗[R] S) × (B ⊗[R] S) :=
  chartCoefficients (extendChart c (includeRight : S →ₐ[R] B ⊗[R] S))
    (pointMap (M := M) (includeLeft : B →ₐ[R] B ⊗[R] S) x)

private theorem coverCoefficients_natural (c : SplitChart J S) (f : B →ₐ[R] C) (x : B ⊗[R] M) :
    coverCoefficients c (pointMap (M := M) f x) =
      let g := Algebra.TensorProduct.map f (AlgHom.id R S)
      Prod.map g (Prod.map g g) (coverCoefficients c x) := by
  let g := Algebra.TensorProduct.map f (AlgHom.id R S)
  let i : B →ₐ[R] B ⊗[R] S := includeLeft
  let j : C →ₐ[R] C ⊗[R] S := includeLeft
  let d := extendChart c (includeRight : S →ₐ[R] B ⊗[R] S)
  have h : g.comp i = j.comp f := by
    ext b; simp [g, i, j]
  change chartCoefficients (extendChart c includeRight) (pointMap (M := M) j (pointMap (M := M) f x)) =
    Prod.map g (Prod.map g g) (chartCoefficients d (pointMap (M := M) i x))
  rw [← chart_extend_coefficients, pointMap_comp, pointMap_comp, h]
  exact charts_agree _ _ _

/-- Compare the two pullbacks to the double cover using uniqueness in split charts. -/
private theorem coverCoefficients_descend [Module.FaithfullyFlat R S]
    (c : SplitChart J S) (x : B ⊗[R] M) :
    ∃ a : B × B × B, Prod.map (algebraMap B (B ⊗[R] S))
      (Prod.map (algebraMap B (B ⊗[R] S)) (algebraMap B (B ⊗[R] S))) a = coverCoefficients c x := by
  let E := B ⊗[R] S
  let i : E →ₐ[R] E ⊗[B] E := includeLeft
  let j : E →ₐ[R] E ⊗[B] E :=
    { toRingHom := (includeRight : E →ₐ[B] E ⊗[B] E).toRingHom
      commutes' r := by
        change (1 : E) ⊗ₜ[B] algebraMap R E r = algebraMap R E r ⊗ₜ[B] (1 : E)
        exact (Algebra.TensorProduct.algebraMap_apply' (algebraMap R B r)).symm }
  let a : B →ₐ[R] E := includeLeft
  let d := extendChart c (includeRight : S →ₐ[R] E)
  have h : i.comp a = j.comp a := by
    ext b
    exact Algebra.TensorProduct.algebraMap_apply' b
  have he :
      Prod.map i (Prod.map i i) (coverCoefficients c x) =
        Prod.map j (Prod.map j j) (coverCoefficients c x) := by
    change Prod.map i (Prod.map i i) (chartCoefficients d (pointMap (M := M) a x)) =
      Prod.map j (Prod.map j j) (chartCoefficients d (pointMap (M := M) a x))
    rw [← chart_extend_coefficients, ← chart_extend_coefficients, pointMap_comp, pointMap_comp, h]
    exact charts_agree _ _ _
  have recover (z : E) (hz : i z = j z) : ∃ b : B, algebraMap B E b = z := by
    apply (Algebra.IsEffective.of_faithfullyFlat B E z).mp
    exact sub_eq_zero.mpr hz
  obtain ⟨t, ht⟩ := recover _ (congrArg Prod.fst he)
  obtain ⟨s, hs⟩ := recover _ (congrArg (fun p => p.2.1) he)
  obtain ⟨n, hn⟩ := recover _ (congrArg (fun p => p.2.2) he)
  exact ⟨(t, s, n), Prod.ext ht (Prod.ext hs hn)⟩

private def descendedValues [Module.FaithfullyFlat R S] (c : SplitChart J S)
    (x : B ⊗[R] M) : B × B × B := (coverCoefficients_descend c x).choose

private theorem descendedValues_spec [Module.FaithfullyFlat R S] (c : SplitChart J S)
    (x : B ⊗[R] M) :
    let i := algebraMap B (B ⊗[R] S)
    Prod.map i (Prod.map i i) (descendedValues c x) = coverCoefficients c x :=
  (coverCoefficients_descend c x).choose_spec

private theorem descendedValues_natural [Module.FaithfullyFlat R S] (c : SplitChart J S)
    (f : B →ₐ[R] C) (x : B ⊗[R] M) :
    descendedValues c (pointMap (M := M) f x) = Prod.map f (Prod.map f f) (descendedValues c x) := by
  let g := Algebra.TensorProduct.map f (AlgHom.id R S)
  have h := (descendedValues_spec c (pointMap (M := M) f x)).trans (coverCoefficients_natural c f x)
  rw [← descendedValues_spec c x] at h
  have hi := FaithfulSMul.algebraMap_injective C (C ⊗[R] S)
  apply Prod.ext
  · apply hi
    simpa [g, Algebra.TensorProduct.algebraMap_apply] using congrArg Prod.fst h
  · apply Prod.ext
    · apply hi
      simpa [g, Algebra.TensorProduct.algebraMap_apply] using congrArg (fun p => p.2.1) h
    · apply hi
      simpa [g, Algebra.TensorProduct.algebraMap_apply] using congrArg (fun p => p.2.2) h

private def descendCoefficients [Module.FaithfullyFlat R S] (c : SplitChart J S) : Coefficients R M where
  trace := ⟨fun _ _ _ x => (descendedValues c x).1,
    fun f x => congrArg Prod.fst (descendedValues_natural c f x)⟩
  quadraticTrace := ⟨fun _ _ _ x => (descendedValues c x).2.1,
    fun f x => congrArg (fun p => p.2.1) (descendedValues_natural c f x)⟩
  norm := ⟨fun _ _ _ x => (descendedValues c x).2.2,
    fun f x => congrArg (fun p => p.2.2) (descendedValues_natural c f x)⟩

private theorem descended_characteristic [Module.Flat R M] [Module.FaithfullyFlat R S]
    (c : SplitChart J S) : IsCharacteristic J (descendCoefficients c) := by
  intro B _ _ x
  let i : B →ₐ[R] B ⊗[R] S := includeLeft
  let d := extendChart c (includeRight : S →ₐ[R] B ⊗[R] S)
  have h := chart_characteristic d (pointMap (M := M) i x)
  have hval := descendedValues_spec c x
  change Prod.map i (Prod.map i i) (descendedValues c x) = chartCoefficients d (pointMap (M := M) i x) at hval
  change characteristicAt (J := J) x (descendedValues c x)
  unfold characteristicAt at *
  rw [← hval] at h
  apply (cover_point_injective (S := S))
  simpa only [map_add, map_sub, pointMap_smul, J.natural, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, map_one, Prod.map_fst, Prod.map_snd] using h

private theorem scalarLaw_ext {a b : ScalarLaw R M}
    (h : ∀ (B : Type u) [CommRing B] [Algebra R B] (x : B ⊗[R] M), a.eval B x = b.eval B x) :
    a = b := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      have e : a = b := by
        funext B hB hA x
        exact @h B hB hA x
      subst b
      rfl

private theorem characteristic_unique [Module.FaithfullyFlat R S]
    (c : SplitChart J S) (F G : Coefficients R M)
    (hF : IsCharacteristic J F) (hG : IsCharacteristic J G) : F = G := by
  have h (B : Type u) [CommRing B] [Algebra R B] (x : B ⊗[R] M) :
      lawCoefficients F x = lawCoefficients G x := by
    let i : B →ₐ[R] B ⊗[R] S := includeLeft
    let d := extendChart c (includeRight : S →ₐ[R] B ⊗[R] S)
    have he := (law_agrees_chart F hF d (pointMap (M := M) i x)).trans
      (law_agrees_chart G hG d (pointMap (M := M) i x)).symm
    rw [law_coefficients_natural, law_coefficients_natural] at he
    have hi := FaithfulSMul.algebraMap_injective B (B ⊗[R] S)
    exact Prod.ext (hi (congrArg Prod.fst he))
      (Prod.ext (hi (congrArg (fun p => p.2.1) he)) (hi (congrArg (fun p => p.2.2) he)))
  have ht : F.trace = G.trace := scalarLaw_ext (fun B _ _ x => congrArg Prod.fst (h B x))
  have hs : F.quadraticTrace = G.quadraticTrace := scalarLaw_ext (fun B _ _ x => congrArg (fun p => p.2.1) (h B x))
  have hn : F.norm = G.norm := scalarLaw_ext (fun B _ _ x => congrArg (fun p => p.2.2) (h B x))
  cases F
  cases G
  cases ht
  cases hs
  cases hn
  rfl

theorem intrinsic_coefficients : IntrinsicCoefficientsType.{u, v} := by
  intro R _ M _ _ J hJ
  obtain ⟨S, _, _, hf, e, he, hop⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  letI := hf
  letI := (freudenthal_finite_projective J hJ.1).2
  let c : SplitChart J S := ⟨e, he, hop⟩
  refine ⟨⟨descendCoefficients c, descended_characteristic c, ?_⟩, ?_⟩
  · intro F hF
    exact characteristic_unique c F _ hF (descended_characteristic c)
  · intro F hF B _ _ d x
    have h := law_agrees_chart F hF d x
    exact ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h, congrArg (fun p => p.2.2) h⟩

end Descent

section Recovery

open Algebra.TensorProduct (includeLeft includeRight)

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {J : ParaQuadratic R M} (F : Coefficients R M)
  {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

private theorem adjoint_natural (f : B →ₐ[R] C) (x : B ⊗[R] M) :
    pointMap (M := M) f (adjoint J F B x) = adjoint J F C (pointMap (M := M) f x) := by
  simp only [adjoint, map_add, map_sub, pointMap_smul, J.natural, F.trace.natural, F.quadraticTrace.natural,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

private theorem pairing_natural (f : B →ₐ[R] C) (x y : B ⊗[R] M) :
    f (pairing F B x y) = pairing F C (pointMap (M := M) f x) (pointMap (M := M) f y) := by
  simp only [pairing, map_sub, map_mul, ← F.trace.natural, ← F.quadraticTrace.natural, map_add]

variable {F} (hF : IsCharacteristic J F)

include hF in
private theorem chart_adjoint (c : SplitChart J B) (x : B ⊗[R] M) :
    c.coordinates (adjoint J F B x) =
      CubicSpecification.cubicAdjoint (modelNorm B) (untwisted B) (c.coordinates x) := by
  have h := law_agrees_chart F hF c x
  have ht : F.trace.eval B x = CubicSpecification.linearTrace (modelNorm B) (untwisted B) (c.coordinates x) :=
    congrArg Prod.fst h
  have hs : F.quadraticTrace.eval B x = CubicSpecification.quadraticTrace (modelNorm B) (untwisted B) (c.coordinates x) :=
    congrArg (fun p => p.2.1) h
  simp only [adjoint, map_add, map_sub, map_smul, c.op, c.unit, ht, hs]
  rw [show applyOperator (modelNorm B) (untwisted B) (c.coordinates x) CubicSpecification.cubicUnit = _
    from opSquare (untwisted B) (c.coordinates x)]
  abel

include hF in
private theorem chart_pairing (c : SplitChart J B) (x y : B ⊗[R] M) :
    pairing F B x y = CubicSpecification.tracePairing (modelNorm B) (untwisted B) (c.coordinates x) (c.coordinates y) := by
  have ht (z : B ⊗[R] M) : F.trace.eval B z =
      CubicSpecification.linearTrace (modelNorm B) (untwisted B) (c.coordinates z) :=
    congrArg Prod.fst (law_agrees_chart F hF c z)
  have hs (z : B ⊗[R] M) : F.quadraticTrace.eval B z =
      CubicSpecification.quadraticTrace (modelNorm B) (untwisted B) (c.coordinates z) :=
    congrArg (fun p => p.2.1) (law_agrees_chart F hF c z)
  simp only [pairing, ht, hs, map_add]
  have he := quadraticTrace_polar (n := modelNorm B) (untwisted B) (c.coordinates x) (c.coordinates y)
  linear_combination -he

include hF in
private theorem chart_norm (c : SplitChart J B) (x : B ⊗[R] M) :
    F.norm.eval B x = CubicSpecification.cubicNorm (modelNorm B) (untwisted B) (c.coordinates x) :=
  congrArg (fun p => p.2.2) (law_agrees_chart F hF c x)

private theorem perfect_of_baseChange {B E V : Type*} [CommRing B] [CommRing E]
    [Algebra B E] [AddCommGroup V] [Module B V] [Module.Finite B V] [Module.Projective B V]
    [Module.FaithfullyFlat B E] (T : LinearMap.BilinForm B V)
    (T' : LinearMap.BilinForm E (E ⊗[B] V)) (hp : T'.IsPerfPair)
    (h : ∀ x y : V, T' (1 ⊗ₜ[B] x) (1 ⊗ₜ[B] y) = algebraMap B E (T x y)) :
    T.IsPerfPair := by
  apply LinearMap.IsPerfPair.of_bijective
  apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective B E T).mp
  let D : E ⊗[B] Module.Dual B V ≃ₗ[B] Module.Dual E (E ⊗[B] V) :=
    ((TensorProduct.comm B E _).trans (dualTensorHomEquiv B V E)).trans
      ((LinearMap.liftBaseChangeEquiv E).restrictScalars B)
  have he : D.toLinearMap ∘ₗ T.lTensor E = T'.restrictScalars B := by
    apply TensorProduct.ext'
    intro a x
    change D (a ⊗ₜ[B] T x) = T' (a ⊗ₜ[B] x)
    apply LinearMap.ext
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul b y =>
      have hD : D (a ⊗ₜ[B] T x) (b ⊗ₜ[B] y) = b * (algebraMap B E (T x y) * a) := by
        simp [D, LinearMap.liftBaseChange_tmul, Algebra.smul_def, smul_eq_mul]
      rw [hD, ← h]
      have ha : a • (1 ⊗ₜ[B] x : E ⊗[B] V) = a ⊗ₜ[B] x := by simp [smul_tmul', smul_eq_mul]
      have hb : b • (1 ⊗ₜ[B] y : E ⊗[B] V) = b ⊗ₜ[B] y := by simp [smul_tmul', smul_eq_mul]
      rw [← ha, ← hb, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    | add z w hz hw => simp only [map_add, hz, hw]
  apply (D.bijective.of_comp_iff' (T.lTensor E)).mp
  change Function.Bijective (D.toLinearMap ∘ₗ T.lTensor E)
  rw [he]
  exact hp.bijective_left

theorem intrinsic_cubic_recovery : CubicRecoveryType.{u, v} := by
  intro R _ M _ _ J F hJ hF B _ _
  obtain ⟨S, _, _, hf, e, he, hop⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  letI := hf
  obtain ⟨hFinite, hProjective⟩ := freudenthal_finite_projective J hJ.1
  letI := hFinite
  letI := hProjective
  let E := B ⊗[R] S
  let i : B →ₐ[R] E := includeLeft
  let d := extendChart (⟨e, he, hop⟩ : SplitChart J S) (includeRight : S →ₐ[R] E)
  let P := pointMap (M := M) i
  let T₀ := CubicSpecification.tracePairing (modelNorm E) (untwisted E)
  let V := B ⊗[R] M
  let u : V := 1 ⊗ₜ[R] J.unit
  let uE : E ⊗[R] M := 1 ⊗ₜ[R] J.unit
  have hP : Function.Injective P := cover_point_injective
  have hi : Function.Injective i := FaithfulSMul.algebraMap_injective B E
  have hu : P u = uE := by simp [P, u, uE]
  have hunit : d.coordinates uE = CubicSpecification.cubicUnit := d.unit
  have hT (x y : V) : i (pairing F B x y) = T₀ (d.coordinates (P x)) (d.coordinates (P y)) :=
    (pairing_natural F i x y).trans (chart_pairing hF d _ _)
  have hA (x : V) : d.coordinates (P (adjoint J F B x)) =
      CubicSpecification.cubicAdjoint (modelNorm E) (untwisted E) (d.coordinates (P x)) := by
    dsimp only [P]
    rw [adjoint_natural, chart_adjoint hF]
  have hN (x : V) : i (F.norm.eval B x) =
      CubicSpecification.cubicNorm (modelNorm E) (untwisted E) (d.coordinates (P x)) :=
    (F.norm.natural i x).symm.trans (chart_norm hF d _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let T : LinearMap.BilinForm B V :=
      LinearMap.mk₂ B (pairing F B)
        (by intro x y z; apply hi; simp only [map_add, hT, LinearMap.add_apply])
        (by
          intro a x y
          apply hi
          rw [smul_eq_mul, map_mul, hT, hT]
          have hPa : P (a • x) = i a • P x := pointMap_smul i a x
          rw [hPa, map_smul, LinearMap.map_smul₂, smul_eq_mul])
        (by intro x y z; apply hi; simp only [map_add, hT])
        (by
          intro a x y
          apply hi
          rw [smul_eq_mul, map_mul, hT, hT]
          have hPa : P (a • y) = i a • P y := pointMap_smul i a y
          rw [hPa, map_smul, map_smul, smul_eq_mul])
    refine ⟨T, ?_, fun _ _ => rfl⟩
    let H := AlgebraTensorModule.cancelBaseChange R B E E M
    let L := H.trans d.coordinates
    let T' : LinearMap.BilinForm E (E ⊗[B] V) := T₀.compl₁₂ L.toLinearMap L.toLinearMap
    have hp' : T'.IsPerfPair := by
      have hp₀ : T₀.IsPerfPair := tracePairing_perfect (untwisted E) (Zorn.isOctonion E).perfect
      letI := hp₀
      exact LinearMap.IsPerfPair.of_bijective _ <| (LinearEquiv.congrLeft E E L.symm).bijective.comp
        (hp₀.bijective_left.comp L.bijective)
    apply perfect_of_baseChange T T' hp'
    intro x y
    have hH (z : V) : H (1 ⊗ₜ[B] z) = P z := by
      induction z using TensorProduct.inductionOn with
      | tmul a m => simp [H, P, i, AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def]; rfl
      | add x y hx hy => simp [tmul_add, hx, hy]
    change T₀ (d.coordinates (H (1 ⊗ₜ[B] x))) (d.coordinates (H (1 ⊗ₜ[B] y))) =
      i (pairing F B x y)
    rw [hH, hH, hT]
  · apply hi
    rw [hN u, hu, hunit, map_one]
    exact (cubic_unit_identities (n := modelNorm E) (untwisted E)).1
  · apply hP
    apply d.coordinates.injective
    change d.coordinates (P (adjoint J F B u)) = d.coordinates (P u)
    rw [hA, hu, hunit]
    exact (cubic_unit_identities (n := modelNorm E) (untwisted E)).2.1
  · intro x
    apply hi
    have ht := congrArg Prod.fst (law_agrees_chart F hF d (P x))
    change F.trace.eval E (P x) = CubicSpecification.linearTrace (modelNorm E) (untwisted E) (d.coordinates (P x)) at ht
    change i (F.trace.eval B x) = i (pairing F B x u)
    rw [← F.trace.natural i x, hT, hu, hunit]
    exact ht
  · intro x
    apply hi
    rw [← F.quadraticTrace.natural i x, ← F.trace.natural i (adjoint J F B x)]
    have hs := congrArg (fun p => p.2.1) (law_agrees_chart F hF d (P x))
    have ht := congrArg Prod.fst (law_agrees_chart F hF d (P (adjoint J F B x)))
    change F.quadraticTrace.eval E (P x) = CubicSpecification.quadraticTrace (modelNorm E) (untwisted E) (d.coordinates (P x)) at hs
    change F.trace.eval E (P (adjoint J F B x)) = CubicSpecification.linearTrace (modelNorm E) (untwisted E)
      (d.coordinates (P (adjoint J F B x))) at ht
    rw [hs, ht, hA]
    rfl
  · intro x y r
    apply hi
    simp only [map_add, map_mul, map_pow, hN, hT, hA]
    have hy : P (r • y) = i r • P y := pointMap_smul i r y
    rw [hy, map_smul]
    exact cubicNorm_add_smul (untwisted E) (Zorn.isOctonion E).toNormLaws _ _ _
  · intro x y
    apply hP
    apply d.coordinates.injective
    have hop' : P (J.op B x y) = J.op E (P x) (P y) := J.natural i x y
    have hp' (r : B) (z : V) : P (r • z) = i r • P z := pointMap_smul i r z
    simp only [hop', map_add, map_sub, map_smul, hp', hT, hA]
    exact d.op (P x) (P y)

end Recovery

section Automorphisms

open Polynomial
open private baseChange_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {J : ParaQuadratic R M} {F : Coefficients R M}

private def precomposeLaw (L : ScalarLaw R M) (g : Module.End R M) : ScalarLaw R M where
  eval B _ _ x := L.eval B (g.baseChange B x)
  natural f x := by rw [← baseChange_natural f, L.natural]

private def precomposeCoefficients (F : Coefficients R M) (g : Module.End R M) : Coefficients R M :=
  ⟨precomposeLaw F.trace g, precomposeLaw F.quadraticTrace g, precomposeLaw F.norm g⟩

private theorem preserves_coefficients (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (g : M ≃ₗ[R] M) (hg : J.IsIso J g) :
    precomposeCoefficients F g.toLinearMap = F := by
  have h : IsCharacteristic J (precomposeCoefficients F g.toLinearMap) := by
    intro B _ _ x
    let G := g.baseChange R B M M
    have hG : G (1 ⊗ₜ[R] J.unit) = 1 ⊗ₜ[R] J.unit := by
      rw [LinearEquiv.baseChange_tmul, hg.1]
    apply G.injective
    change G (J.op B x x) = G (F.trace.eval B (G x) • J.op B x (1 ⊗ₜ[R] J.unit) -
      F.quadraticTrace.eval B (G x) • x + F.norm.eval B (G x) • (1 ⊗ₜ[R] J.unit))
    have hop (x y : B ⊗[R] M) : G (J.op B x y) = J.op B (G x) (G y) := hg.2 B x y
    simpa only [map_add, map_sub, map_smul, hop, hG] using hF B (G x)
  obtain ⟨L, -, hu⟩ := (intrinsic_coefficients J hJ).1
  exact (hu _ h).trans (hu F hF).symm

private theorem pairing_symmetric {B : Type u} [CommRing B] [Algebra R B]
    (x y : B ⊗[R] M) : pairing F B x y = pairing F B y x := by
  simp only [pairing, add_comm x y]
  ring

/-- Compare the coefficient of X in the norm on lines over the polynomial test algebra. -/
private theorem directional_preserved (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (g : Module.End R M) (hg : PreservesNorm J F g)
    {B : Type u} [CommRing B] [Algebra R B] (x y : B ⊗[R] M) :
    pairing F B (adjoint J F B (g.baseChange B x)) (g.baseChange B y) =
      pairing F B (adjoint J F B x) y := by
  let f : B →ₐ[R] B[X] := CAlgHom
  let q := pointMap (M := M) f
  let L := g.baseChange B
  have h := hg.2 (B[X]) (q x + (X : B[X]) • q y)
  have he (x y : B ⊗[R] M) :
      F.norm.eval (B[X]) (q x + (X : B[X]) • q y) =
        C (F.norm.eval B x) +
        X * C (pairing F B (adjoint J F B x) y) +
        X ^ 2 * C (pairing F B (adjoint J F B y) x) + X ^ 3 * C (F.norm.eval B y) := by
    rw [(intrinsic_cubic_recovery J F hJ hF (B[X])).2.2.2.2.2.1]
    have ha (a : B ⊗[R] M) : F.norm.eval (B[X]) (q a) = C (F.norm.eval B a) :=
      F.norm.natural f a
    have hb (a b : B ⊗[R] M) :
        pairing F (B[X]) (adjoint J F (B[X]) (q a)) (q b) =
          C (pairing F B (adjoint J F B a) b) := by
      rw [← show q (adjoint J F B a) = _ from adjoint_natural F f a]
      exact (pairing_natural F f _ _).symm
    rw [ha, ha, hb, hb]
  have hg' (z : B ⊗[R] M) : g.baseChange (B[X]) (q z) = q (L z) :=
    (baseChange_natural f g z).symm
  simp only [map_add, map_smul, hg', he] at h
  have h' := congrArg (fun p : B[X] => p.coeff 1) h
  simpa [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow] using h'

theorem intrinsic_norm_automorphisms : AutomorphismType.{u, v} := by
  intro R _ M _ _ J F hJ hF g
  constructor
  · intro hg
    refine ⟨hg.1, fun B _ _ x => ?_⟩
    exact congrArg (fun H : Coefficients R M => H.norm.eval B x) (preserves_coefficients hJ hF g hg)
  · intro hg
    refine ⟨hg.1, ?_⟩
    intro B _ _ x y
    let G := g.baseChange R B M M
    let e : B ⊗[R] M := 1 ⊗ₜ[R] J.unit
    have hG : G e = e := by
      change G (1 ⊗ₜ[R] J.unit) = 1 ⊗ₜ[R] J.unit
      rw [LinearEquiv.baseChange_tmul, show g J.unit = J.unit from hg.1]
    obtain ⟨⟨T, hperfect, hT⟩, _, hau, htrace, hspur, _, hop⟩ :=
      intrinsic_cubic_recovery J F hJ hF B
    have hd (x y : B ⊗[R] M) :
        pairing F B (adjoint J F B (G x)) (G y) = pairing F B (adjoint J F B x) y :=
      directional_preserved hJ hF g.toLinearMap hg x y
    have ht (x : B ⊗[R] M) : F.trace.eval B (G x) = F.trace.eval B x := by
      have h := hd e x
      rw [hG, show adjoint J F B e = e from hau, pairing_symmetric e (G x), pairing_symmetric e x] at h
      exact (htrace _).trans (h.trans (htrace x).symm)
    have hs (x : B ⊗[R] M) : F.quadraticTrace.eval B (G x) = F.quadraticTrace.eval B x := by
      have h := hd x e
      rw [hG] at h
      exact (hspur _).trans ((htrace _).trans (h.trans ((htrace _).symm.trans (hspur x).symm)))
    have hGpair (x y : B ⊗[R] M) : pairing F B (G x) (G y) = pairing F B x y := by
      simp only [pairing, ht, ← map_add, hs]
    have hA (x : B ⊗[R] M) : G (adjoint J F B x) = adjoint J F B (G x) := by
      apply hperfect.bijective_left.injective
      apply LinearMap.ext
      intro w
      obtain ⟨z, rfl⟩ := G.surjective w
      rw [hT, hT, hGpair, hd]
    change G (J.op B x y) = J.op B (G x) (G y)
    rw [hop, hop]
    simp only [map_add, map_sub, map_smul, hA, hGpair]

end Automorphisms

section BaseChange

open Algebra.TensorProduct (includeRight)
open private towerScalars from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {J : ParaQuadratic R M} {F : Coefficients R M}
  {B : Type u} [CommRing B] [Algebra R B]

private theorem albert_baseChange (hJ : IsAlbert J) : IsAlbert (J.baseChange B) := by
  obtain ⟨S, _, _, hf, e, he, hop⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  letI := hf
  let E := B ⊗[R] S
  let H := AlgebraTensorModule.cancelBaseChange R B E E M
  let c := extendChart (⟨e, he, hop⟩ : SplitChart J S) (includeRight : S →ₐ[R] E)
  apply (albert_iff_split_octonion_after_cover (J.baseChange B)).mpr
  refine ⟨E, inferInstance, inferInstance, inferInstance, H.trans c.coordinates, ?_, ?_⟩
  · change c.coordinates (H (1 ⊗ₜ[B] (1 ⊗ₜ[R] J.unit))) = _
    rw [show H (1 ⊗ₜ[B] (1 ⊗ₜ[R] J.unit)) = (1 ⊗ₜ[R] J.unit) by
      simp [H, AlgebraTensorModule.cancelBaseChange_tmul]]
    exact c.unit
  · intro x y
    change c.coordinates (H ((J.baseChange B).op E x y)) = _
    rw [show H ((J.baseChange B).op E x y) = J.op E (H x) (H y) from baseChange_cancel_op x y]
    exact c.op (H x) (H y)

private theorem characteristic_baseChange (hF : IsCharacteristic J F) :
    IsCharacteristic (J.baseChange B) (F.changeScalars B) := by
  intro T _ _ x
  letI := towerAlgebra R B T
  letI := towerScalars R B T
  let H := iteratedTensorEquiv (R := R) (S := B) (M := M) T
  have he : H (1 ⊗ₜ[B] (1 ⊗ₜ[R] J.unit)) = 1 ⊗ₜ[R] J.unit := by
    simp [H, AlgebraTensorModule.cancelBaseChange_tmul]
  apply H.injective
  have h := hF T (H x)
  unfold IsCharacteristic at hF
  change H ((J.baseChange B).op T x x) =
    H (F.trace.eval T (H x) • (J.baseChange B).op T x (1 ⊗ₜ[B] (1 ⊗ₜ[R] J.unit)) -
      F.quadraticTrace.eval T (H x) • x + F.norm.eval T (H x) • (1 ⊗ₜ[B] (1 ⊗ₜ[R] J.unit)))
  simp only [map_add, map_sub, map_smul, show ∀ x y, H ((J.baseChange B).op T x y) =
    J.op T (H x) (H y) from J.extendedOp_apply B T, he]
  exact h

private theorem changeScalars_norm_eval {T : Type u} [CommRing T]
    [Algebra B T] [aRT : Algebra R T] [IsScalarTower R B T] (x : T ⊗[B] (B ⊗[R] M)) :
    (F.changeScalars B).norm.eval T x = F.norm.eval T (AlgebraTensorModule.cancelBaseChange R B T T M x) := by
  have ha : aRT = towerAlgebra R B T :=
    Algebra.algebra_ext _ _ (fun r => IsScalarTower.algebraMap_apply R B T r)
  subst aRT
  rfl

theorem intrinsic_norm_stabilizer : NormStabilizerType.{u, v} := by
  intro R _ M _ _ J F hJ hF B _ _ g
  let K := (ParaQuadratic.ofJordan J).baseChange B
  let G := LinearMap.GeneralLinearGroup.toLinearEquiv g
  have hK : IsAlbert K := albert_baseChange hJ
  have hFc : IsCharacteristic K (F.changeScalars B) := characteristic_baseChange hF
  have h : PreservesQuadratic J B g.val ↔ K.IsGroundIso K G := by
    unfold PreservesQuadratic ParaQuadratic.IsGroundIso
    have hg (x y : B ⊗[R] M) : K.groundOp x y = J.op B x y :=
      (ParaQuadratic.ofJordan J).groundOp_baseChange B x y
    simp only [hg]
    rfl
  exact (mem_quadraticStabilizer J B g).trans (h.trans
    ((K.isIso_iff_ground K G).symm.trans (intrinsic_norm_automorphisms K _ hK hFc G)))

end BaseChange

section Tangent

open private baseChange_natural infinitesimalUnit infinitesimal_fixes infinitesimal_quadratic_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme
open private towerScalars from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {J : QuadraticJordan R M} {F : Coefficients R M}

private theorem infinitesimal_transport (D : Module.End R M) {T : Type u}
    [CommRing T] [Algebra (DualNumber R) T] [Algebra R T]
    [IsScalarTower R (DualNumber R) T]
    (x : T ⊗[DualNumber R] (DualNumber R ⊗[R] M)) :
    let H := AlgebraTensorModule.cancelBaseChange R (DualNumber R) T T M
    H ((infinitesimal D).baseChange T x) = H x +
      (algebraMap (DualNumber R) T ε) • D.baseChange T (H x) := by
  let H := AlgebraTensorModule.cancelBaseChange R (DualNumber R) T T M
  change H (((1 + (ε : DualNumber R) • D.baseChange (DualNumber R)).baseChange T) x) = _
  rw [LinearMap.baseChange_add, LinearMap.baseChange_one, LinearMap.baseChange_smul,
    LinearMap.baseChange_baseChange]
  rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, map_add]
  change H x + H ((ε : DualNumber R) • (H.symm (D.baseChange T (H x)))) = _
  rw [← algebraMap_smul T (ε : DualNumber R), map_smul, H.apply_symm_apply]

private theorem transported_norm_iff (D : Module.End R M) :
    PreservesNorm ((ParaQuadratic.ofJordan J).baseChange (DualNumber R))
      (F.changeScalars (DualNumber R)) (infinitesimal D) ↔
    D J.unit = 0 ∧
      ∀ (T : Type u) [CommRing T] [Algebra R T]
        (f : DualNumber R →ₐ[R] T) (x : T ⊗[R] M),
        F.norm.eval T (x + f ε • D.baseChange T x) = F.norm.eval T x := by
  constructor
  · intro h
    refine ⟨(infinitesimal_fixes D J.unit).mp h.1, ?_⟩
    intro T _ _ f x
    letI : Algebra (DualNumber R) T := f.toAlgebra
    letI : IsScalarTower R (DualNumber R) T := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    let H := AlgebraTensorModule.cancelBaseChange R (DualNumber R) T T M
    obtain ⟨z, rfl⟩ := H.surjective x
    have he := h.2 T z
    rw [changeScalars_norm_eval, changeScalars_norm_eval, infinitesimal_transport] at he
    exact he
  · intro h
    refine ⟨(infinitesimal_fixes D J.unit).mpr h.1, ?_⟩
    intro T _ _ x
    letI := towerAlgebra R (DualNumber R) T
    letI := towerScalars R (DualNumber R) T
    let H := AlgebraTensorModule.cancelBaseChange R (DualNumber R) T T M
    rw [changeScalars_norm_eval, changeScalars_norm_eval, infinitesimal_transport]
    exact h.2 T (IsScalarTower.toAlgHom R (DualNumber R) T) (H x)

private theorem norm_infinitesimal_iff (hJ : IsAlbert (ParaQuadratic.ofJordan J))
    (hF : IsCharacteristic (ParaQuadratic.ofJordan J) F) (D : Module.End R M) :
    PreservesNorm ((ParaQuadratic.ofJordan J).baseChange (DualNumber R))
      (F.changeScalars (DualNumber R)) (infinitesimal D) ↔
    NormTangentEquations (ParaQuadratic.ofJordan J) F D := by
  let K := ParaQuadratic.ofJordan J
  rw [transported_norm_iff]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro B _ _ x
    let E := DualNumber B
    let i : B →ₐ[R] E := TrivSqZeroExt.inlAlgHom R B B
    let f : DualNumber R →ₐ[R] E := DualNumber.lift
      ⟨(Algebra.ofId R E, ε), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩
    have hf : f ε = (ε : E) := DualNumber.lift_apply_eps _
    let z := pointMap (M := M) i x
    have he := h.2 E f z
    rw [hf, (intrinsic_cubic_recovery K F hJ hF E).2.2.2.2.2.1] at he
    have h₃ : (ε : E) ^ 3 = 0 := by rw [pow_succ, DualNumber.eps_pow_two, zero_mul]
    have h₂ : (ε : E) ^ 2 = 0 := DualNumber.eps_pow_two
    simp only [h₂, h₃, zero_mul, add_zero] at he
    have hz : (ε : E) * pairing F E (adjoint K F E z) (D.baseChange E z) = 0 :=
      add_left_cancel (he.trans (add_zero _).symm)
    clear he
    have hD : D.baseChange E z = pointMap (M := M) i (D.baseChange B x) :=
      (baseChange_natural i D x).symm
    rw [hD, ← show pointMap (M := M) i (adjoint K F B x) = adjoint K F E z
      from adjoint_natural F i x, ← pairing_natural] at hz
    have hcoeff := congrArg TrivSqZeroExt.snd hz
    change ((ε : DualNumber B) * TrivSqZeroExt.inl
      (pairing F B (adjoint K F B x) (D.baseChange B x))).snd = 0 at hcoeff
    simpa only [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, one_mul, zero_add] using hcoeff
  · intro h
    refine ⟨h.1, ?_⟩
    intro T _ _ f x
    have h₂ : (f ε) ^ 2 = 0 := by rw [← map_pow, DualNumber.eps_pow_two, map_zero]
    have h₃ : (f ε) ^ 3 = 0 := by rw [pow_succ, h₂, zero_mul]
    rw [(intrinsic_cubic_recovery K F hJ hF T).2.2.2.2.2.1, h.2 T x, h₂, h₃]
    simp

theorem intrinsic_norm_tangent : TangentEquationsType.{u, v} := by
  intro R _ M _ _ J F hJ hF D
  let g := infinitesimalUnit D
  have h₁ := (infinitesimal_quadratic_iff J D).symm
  have h₂ := (mem_quadraticStabilizer J (DualNumber R) g).symm
  have h₃ := intrinsic_norm_stabilizer J F hJ hF (DualNumber R) g
  exact h₁.trans (h₂.trans (h₃.trans (norm_infinitesimal_iff hJ hF D)))

end Tangent

end
end LinearAlgebraicGroups.Albert
