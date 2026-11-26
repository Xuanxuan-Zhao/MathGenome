import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GeometricReductivity
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.MaximalToriExist
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CostandardExtensions
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SteinbergFrobeniusPushforward
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.AlgebraicGeometry.Morphisms.Flat

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open scoped BigOperators Matrix Kronecker TensorProduct CategoryTheory.MonObj

universe u

noncomputable section

namespace LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricReductivity
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootWeightAction (Representation act extendVector)

variable {k I J : Type u} [Field k] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

private theorem linearPolynomial_homogeneous {R : Type u} [CommRing R] (v : J → R) :
    (linearPolynomial v).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  rw [smul_eq_C_mul]
  exact isHomogeneous_C_mul_X (v i) i

private theorem map_linearPolynomial {A R : Type u} [CommRing A] [CommRing R]
    (f : A →+* R) (v : J → A) :
    MvPolynomial.map f (linearPolynomial v) = linearPolynomial (fun j ↦ f (v j)) := by
  simp [linearPolynomial, smul_eq_C_mul, map_sum]

private theorem polynomialAction_linearPolynomial {R : Type u} [CommRing R]
    (M : Matrix J J R) (v : J → R) :
    polynomialAction M (linearPolynomial v) = linearPolynomial (M.mulVec v) := by
  simp only [polynomialAction, linearPolynomial, map_sum, map_smul, bind₁_X_right,
    Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, mul_comm]

private theorem eval_linearPolynomial (q : (J → k) →ₗ[k] k) (v : J → k) :
    MvPolynomial.eval (fun j ↦ q (Pi.single j 1)) (linearPolynomial v) = q v := by
  have h : (∑ i, v i • Pi.single i (1 : k)) = v := by
    ext j
    simp [Pi.single_apply, Pi.smul_apply]
  calc
    _ = ∑ j, v j • q (Pi.single j 1) := by
      simp [linearPolynomial, smul_eq_C_mul, map_sum]
    _ = q (∑ j, v j • Pi.single j 1) := by simp only [map_sum, map_smul]
    _ = q v := congrArg q h

private theorem det_homogeneous {R : Type u} [CommRing R]
    (M : Matrix I I (MvPolynomial J R)) (h : ∀ i j, (M i j).IsHomogeneous 1) :
    M.det.IsHomogeneous (Fintype.card I) := by
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ _
  have hp : (∏ i, M (σ i) i).IsHomogeneous (Fintype.card I) := by
    simpa using IsHomogeneous.prod Finset.univ (fun i ↦ M (σ i) i) (fun _ ↦ 1)
      (fun i _ ↦ h _ _)
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R]
  exact (homogeneousSubmodule J R (Fintype.card I)).smul_mem _ hp

private theorem polynomial_matrix_conjugation {R : Type u} [CommRing R]
    (A B : Matrix I I R) (F E : Matrix I I (J → R))
    (h : ∀ l, Matrix.of (fun i j ↦ E i j l) = A * Matrix.of (fun i j ↦ F i j l) * B) :
    Matrix.of (fun i j ↦ linearPolynomial (E i j)) =
      A.map MvPolynomial.C * Matrix.of (fun i j ↦ linearPolynomial (F i j)) *
        B.map MvPolynomial.C := by
  let entry (T : Matrix I I (J → R)) (l : J) : Matrix I I R :=
    Matrix.of (fun i j ↦ T i j l)
  have hsum (T : Matrix I I (J → R)) :
      Matrix.of (fun i j ↦ linearPolynomial (T i j)) =
        ∑ l, (X l : MvPolynomial J R) • (entry T l).map MvPolynomial.C := by
    apply Matrix.ext
    intro i j
    simp [linearPolynomial, entry, Matrix.sum_apply, Matrix.smul_apply, smul_eq_C_mul, mul_comm]
  rw [hsum E, hsum F, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun T : Matrix I I R ↦ (X l : MvPolynomial J R) • T.map MvPolynomial.C) (h l)

/-- The image of the determinant gives a homogeneous invariant with value one
whenever evaluation at the identity lifts equivariantly. -/
theorem invariant_of_endomorphism_lift {H : AffineAlgebraicGroup k}
    (ρ : Representation H.val J) (S : Representation H.val I)
    (q : (J → k) →ₗ[k] k) (F : Matrix I I (J → k))
    (h : IsEndomorphismLift ρ S q F) :
    ∃ f : MvPolynomial J k, f.IsHomogeneous (Fintype.card I) ∧
      SymmetricFixed ρ f ∧ MvPolynomial.eval (fun j ↦ q (Pi.single j 1)) f = 1 := by
  let M : Matrix I I (MvPolynomial J k) := Matrix.of (fun i j ↦ linearPolynomial (F i j))
  refine ⟨M.det, det_homogeneous M (fun i j ↦ linearPolynomial_homogeneous (F i j)), ?_, ?_⟩
  · intro R g
    let B := (S.app R g).val
    let A := ((S.app R g)⁻¹).val
    let N : Matrix I I (MvPolynomial J R) :=
      Matrix.of (fun i j ↦ linearPolynomial (extendVector R (F i j)))
    have hmap : M.map (MvPolynomial.map (algebraMap k R)) = N := by
      apply Matrix.ext
      intro i j
      exact map_linearPolynomial (algebraMap k R) (F i j)
    have hact : N.map (polynomialAction (ρ.app R g).val) =
        A.map MvPolynomial.C * N * B.map MvPolynomial.C := by
      calc
        _ = Matrix.of (fun i j ↦ linearPolynomial (act ρ R g (extendVector R (F i j)))) := by
          apply Matrix.ext
          intro i j
          exact polynomialAction_linearPolynomial _ _
        _ = _ := polynomial_matrix_conjugation A B _ _ (h.2 R g)
    rw [RingHom.map_det]
    change polynomialAction (ρ.app R g).val (M.map (MvPolynomial.map (algebraMap k R))).det =
      (M.map (MvPolynomial.map (algebraMap k R))).det
    rw [hmap, AlgHom.map_det]
    change (N.map (polynomialAction (ρ.app R g).val)).det = N.det
    rw [hact, Matrix.det_mul_comm _ (B.map MvPolynomial.C), ← Matrix.mul_assoc]
    have hBA : B.map MvPolynomial.C * A.map MvPolynomial.C =
        (1 : Matrix I I (MvPolynomial J R)) := by
      rw [← Matrix.map_mul, show B * A = 1 from congrArg Units.val (mul_inv_cancel (S.app R g)),
        Matrix.map_one _ (map_zero MvPolynomial.C) (map_one MvPolynomial.C)]
    rw [hBA, one_mul]
  · rw [RingHom.map_det]
    have heval : M.map (MvPolynomial.eval (fun j ↦ q (Pi.single j 1))) = 1 := by
      apply Matrix.ext
      intro i j
      exact (eval_linearPolynomial q (F i j)).trans (h.1 i j)
    change (M.map (MvPolynomial.eval (fun j ↦ q (Pi.single j 1)))).det = 1
    rw [heval, Matrix.det_one]

private theorem extend_basis (R : TestAlgebra k) (j : I) :
    extendVector R (Pi.single j 1) = Pi.single j 1 := by
  ext a
  by_cases h : a = j <;> simp [extendVector, h]

private theorem linear_map_in_basis {V : Type u} [AddCommGroup V] [Module k V]
    (s : (I → k) →ₗ[k] V) (w : I → k) :
    s w = ∑ j, w j • s (Pi.single j 1) := by
  have h : (∑ j, w j • Pi.single j (1 : k)) = w := by
    ext a
    simp [Pi.single_apply, Pi.smul_apply]
  calc
    s w = s (∑ j, w j • Pi.single j 1) := congrArg s h.symm
    _ = ∑ j, w j • s (Pi.single j 1) := by simp only [map_sum, map_smul]

private theorem equivariant_apply_over_algebra {H : AffineAlgebraicGroup k}
    {D : Type u} [Fintype D] [DecidableEq D]
    {S : Representation H.val I} {T : Representation H.val D}
    (s : (I → k) →ₗ[k] (D → k)) (hs : PrimitiveLine.IsEquivariant S T s)
    (R : TestAlgebra k) (g : GroupPoints H.val R) (v : I → k) (d : D) :
    act T R g (extendVector R (s v)) d =
      ∑ a, algebraMap k R (s (Pi.single a 1) d) * act S R g (extendVector R v) a := by
  let x := act T R g (extendVector R (s v)) d
  let y := ∑ a, algebraMap k R (s (Pi.single a 1) d) * act S R g (extendVector R v) a
  change x = y
  by_contra h
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k (sub_ne_zero.mpr h)
  apply hℓ
  rw [map_sub, sub_eq_zero]
  have hℓ' := congrFun (hs R g ℓ v) d
  rw [linear_map_in_basis s (PrimitiveLine.orbitCoefficient S R g ℓ v)] at hℓ'
  change ℓ x = ℓ y
  unfold y
  simp only [map_sum, ← Algebra.smul_def, map_smul]
  simpa only [PrimitiveLine.orbitCoefficient, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm] using hℓ'.symm

private theorem polynomialAction_map {R S : Type u} [CommRing R] [CommRing S]
    (a : R →+* S) (M : Matrix J J R) (f : MvPolynomial J R) :
    MvPolynomial.map a (polynomialAction M f) =
      polynomialAction (M.map a) (f.map a) := by
  unfold polynomialAction
  rw [map_bind₁]
  have h : (fun j ↦ MvPolynomial.map a (linearPolynomial (fun i ↦ M i j))) =
      (fun j ↦ linearPolynomial (fun i ↦ (M.map a) i j)) := by
    funext j
    exact map_linearPolynomial a (fun i ↦ M i j)
  rw [h]

private theorem repMatrix_mapPoints {G : GroupScheme k}
    (ρ : Representation G J) {R S : TestAlgebra k} (a : R ⟶ S) (g : GroupPoints G R) :
    (ρ.app S (mapPoints a g)).val = (ρ.app R g).val.map a.hom.toRingHom := by
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality a)) g
  have h' := congrArg (fun M : Matrix.GeneralLinearGroup J S ↦ M.val) h
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at h'
  exact h'

private def kroneckerHom (R : Type u) [CommRing R] :
    Matrix I I R × Matrix J J R →* Matrix (I × J) (I × J) R where
  toFun p := p.1 ⊗ₖ p.2
  map_one' := Matrix.one_kronecker_one
  map_mul' p q := Matrix.mul_kronecker_mul p.1 q.1 p.2 q.2

/-- The diagonal tensor action, in the product of the two finite bases. -/
def tensorRepresentation {H : AffineAlgebraicGroup k}
    (S : Representation H.val I) (ρ : Representation H.val J) : Representation H.val (I × J) where
  app R := GrpCat.ofHom
    ((Units.map (kroneckerHom R)).comp
      ((MulEquiv.prodUnits).symm.toMonoidHom.comp
        ((S.app R).hom.prod (ρ.app R).hom)))
  naturality {R T} a := by
    apply GrpCat.ext
    intro g
    apply Units.ext
    apply Matrix.ext
    intro i j
    have hs := congrFun (congrFun (repMatrix_mapPoints S a g) i.1) j.1
    have hρ := congrFun (congrFun (repMatrix_mapPoints ρ a g) i.2) j.2
    change (S.app T (mapPoints a g)).val i.1 j.1 * (ρ.app T (mapPoints a g)).val i.2 j.2 =
      a.hom ((S.app R g).val i.1 j.1 * (ρ.app R g).val i.2 j.2)
    exact (congrArg₂ (· * ·) hs hρ).trans (map_mul a.hom _ _).symm

@[simp] theorem tensorRepresentation_apply {H : AffineAlgebraicGroup k}
    (S : Representation H.val I) (ρ : Representation H.val J)
    (R : TestAlgebra k) (g : GroupPoints H.val R) (i a : I) (l b : J) :
    ((tensorRepresentation S ρ).app R g).val (i, l) (a, b) =
      (S.app R g).val i a * (ρ.app R g).val l b := rfl

/-- Tensor a scalar-valued linear map with the identity of the first module. -/
def tensorQuotient (q : (J → k) →ₗ[k] k) : (I × J → k) →ₗ[k] (I → k) where
  toFun z i := q (fun j ↦ z (i, j))
  map_add' x y := funext fun i ↦ q.map_add (fun j ↦ x (i, j)) (fun j ↦ y (i, j))
  map_smul' c x := funext fun i ↦ q.map_smul c (fun j ↦ x (i, j))

theorem tensorQuotient_surjective (q : (J → k) →ₗ[k] k) (hq : Function.Surjective q) :
    Function.Surjective (tensorQuotient (I := I) q) := by
  obtain ⟨u, hu⟩ := hq 1
  intro x
  refine ⟨fun ij ↦ x ij.1 * u ij.2, funext fun i ↦ ?_⟩
  change q (x i • u) = x i
  rw [map_smul, hu, smul_eq_mul, mul_one]

theorem tensorQuotient_equivariant {H : AffineAlgebraicGroup k}
    (S : Representation H.val I) (ρ : Representation H.val J)
    (q : (J → k) →ₗ[k] k) (hq : IsTrivialQuotient ρ q) :
    PrimitiveLine.IsEquivariant (tensorRepresentation S ρ) S (tensorQuotient q) := by
  intro R g ℓ z
  funext i
  let B := (S.app R g).val
  let zR := extendVector R z
  let a (j : J) := q (Pi.single j 1)
  have h (a' : I) :
      ∑ j, algebraMap k R (a j) * (act ρ R g (fun b ↦ zR (a', b))) j =
        algebraMap k R (q (fun b ↦ z (a', b))) := by
    rw [hq.2 R g]
    have hb := linear_map_in_basis q (fun b ↦ z (a', b))
    rw [hb, map_sum]
    simp only [zR, extendVector, smul_eq_mul, map_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  change q (fun j ↦ ℓ (act (tensorRepresentation S ρ) R g zR (i, j))) =
    ℓ (act S R g (extendVector R (tensorQuotient q z)) i)
  rw [linear_map_in_basis q (fun j ↦ ℓ (act (tensorRepresentation S ρ) R g zR (i, j)))]
  simp only [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorRepresentation_apply,
    mul_assoc, ← Finset.mul_sum] at ⊢
  change ∑ j, ℓ (∑ a', B i a' * (act ρ R g (fun b ↦ zR (a', b))) j) • a j =
    ℓ (∑ a', B i a' * algebraMap k R (q (fun b ↦ z (a', b))))
  have hcoef (c : k) (x : R) : ℓ x • c = ℓ (algebraMap k R c * x) := by
    rw [← Algebra.smul_def, map_smul]
    exact mul_comm _ _
  simp only [hcoef, ← map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a' _
  rw [← h a', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A section of the tensor quotient gives a lift from the dual endomorphism
module, by taking the coefficients of the section on the basis vectors. -/
theorem endomorphism_lift_of_tensor_section {H : AffineAlgebraicGroup k}
    (ρ : Representation H.val J) (S : Representation H.val I)
    (q : (J → k) →ₗ[k] k) (s : (I → k) →ₗ[k] (I × J → k))
    (hsection : (tensorQuotient q).comp s = LinearMap.id)
    (hs : PrimitiveLine.IsEquivariant S (tensorRepresentation S ρ) s) :
    ∃ F : Matrix I I (J → k), IsEndomorphismLift ρ S q F := by
  let F : Matrix I I (J → k) := Matrix.of (fun i j l ↦ s (Pi.single j 1) (i, l))
  refine ⟨F, ?_, ?_⟩
  · intro i j
    have h := congrFun (LinearMap.congr_fun hsection (Pi.single j 1)) i
    simpa [F, tensorQuotient, Pi.single_apply, Matrix.one_apply, eq_comm] using h
  intro R g l
  let B := (S.app R g).val
  let A := ((S.app R g)⁻¹).val
  let U : Matrix I I R := Matrix.of (fun i j ↦ act ρ R g (extendVector R (F i j)) l)
  let V : Matrix I I R := Matrix.of (fun i j ↦ algebraMap k R (F i j l))
  change U = A * V * B
  have hcomm : B * U = V * B := by
    apply Matrix.ext
    intro i j
    have h := equivariant_apply_over_algebra s hs R g (Pi.single j 1) (i, l)
    rw [extend_basis, show act S R g (Pi.single j 1) = fun a ↦ B a j from
      Matrix.mulVec_single_one B j] at h
    change ((tensorRepresentation S ρ).app R g).val.mulVec (extendVector R (s (Pi.single j 1))) (i, l) =
      ∑ a, V i a * B a j at h
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorRepresentation_apply, mul_assoc,
      ← Finset.mul_sum] at h
    simpa only [Matrix.mul_apply, U, B, F, act, extendVector, Matrix.of_apply, Matrix.mulVec,
      dotProduct] using h
  have hAB : A * B = 1 := congrArg Units.val (inv_mul_cancel (S.app R g))
  calc
    U = (A * B) * U := by rw [hAB, one_mul]
    _ = A * (V * B) := by rw [Matrix.mul_assoc, hcomm]
    _ = A * V * B := (Matrix.mul_assoc _ _ _).symm

/-- An equivariant retraction of the kernel of a surjective map determines an
equivariant section of the quotient. -/
theorem section_of_equivariant_retraction {H : AffineAlgebraicGroup k}
    {D : Type u} [Fintype D] [DecidableEq D]
    {S : Representation H.val I} {T : Representation H.val J} {N : Representation H.val D}
    {i : (D → k) →ₗ[k] (J → k)} {q : (J → k) →ₗ[k] (I → k)}
    (hq : PrimitiveLine.IsEquivariant T S q) (hExact : Function.Exact i q)
    (hSurj : Function.Surjective q)
    (r : (J → k) →ₗ[k] (D → k)) (hr : PrimitiveLine.IsEquivariant T N r)
    (hret : r.comp i = LinearMap.id) :
    ∃ s : (I → k) →ₗ[k] (J → k), PrimitiveLine.IsEquivariant S T s ∧
      q.comp s = LinearMap.id := by
  obtain ⟨t, ht⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hSurj)
  let s := t - i.comp (r.comp t)
  have hqv (x : I → k) : q (s x) = x := by
    have hqi : q (i (r (t x))) = 0 := (hExact _).mpr ⟨_, rfl⟩
    have htx : q (t x) = x := LinearMap.congr_fun ht x
    simp only [s, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hqi, htx, sub_zero]
  have hrv (x : I → k) : r (s x) = 0 := by
    have hri : r (i (r (t x))) = r (t x) := LinearMap.congr_fun hret _
    simp only [s, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hri, sub_self]
  have unique (x y : J → k) (eq_q : q x = q y) (eq_r : r x = r y) : x = y := by
    obtain ⟨z, hz⟩ := (hExact (x - y)).mp (by simp [eq_q])
    have hz0 : z = 0 := by
      calc
        z = r (i z) := (LinearMap.congr_fun hret z).symm
        _ = 0 := by rw [hz, map_sub, eq_r, sub_self]
    exact sub_eq_zero.mp (by rw [← hz, hz0, map_zero])
  refine ⟨s, ?_, LinearMap.ext hqv⟩
  intro R g ℓ v
  apply unique
  · rw [hqv, hq, hqv]
  · rw [hrv, hr, hrv]
    funext j
    simp [PrimitiveLine.orbitCoefficient, act, extendVector, Matrix.mulVec, dotProduct]

private theorem liftPoint_after_injective_extension {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (hf : Flat f.hom.hom.left) (hs : Surjective f.hom.hom.left)
    (R : TestAlgebra k) (g : GroupPoints H.val R) :
    ∃ (S : TestAlgebra k) (a : R ⟶ S) (x : GroupPoints G.val S),
      Function.Injective a.hom ∧ x ≫ f.hom.hom = mapPoints a g := by
  let X := (testSpec k).obj (op R)
  let g' : X ⟶ H.val.X := g
  let f' := f.hom.hom
  let P := pullback f' g'
  let pr := pullback.snd f' g'
  have hpb : IsPullback (pullback.fst f' g').left pr.left f'.left g'.left :=
    (IsPullback.of_hasPullback f' g').map (Over.forget (Spec (CommRingCat.of k)))
  have : IsAffine (pullback f'.left g'.left) :=
    @AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _ _
      f'.left g'.left G.property.1 (inferInstanceAs (IsAffine (Spec (CommRingCat.of R))))
      H.property.1
  have haff : IsAffine P.left := IsAffine.of_isIso hpb.isoPullback.hom
  obtain ⟨S, ⟨e⟩⟩ := essImage_algSpec.mpr haff
  let a : R ⟶ S.unop := (AlgebraicGeometry.algSpec.fullyFaithful.preimage (e.hom ≫ pr)).unop
  have ha : (testSpec k).map a.op = e.hom ≫ pr :=
    AlgebraicGeometry.algSpec.fullyFaithful.map_preimage _
  have : Flat pr.left := MorphismProperty.of_isPullback hpb hf
  have : Surjective pr.left := MorphismProperty.of_isPullback hpb hs
  have hsmap : Spec.map (CommRingCat.ofHom a.hom.toRingHom) = e.hom.left ≫ pr.left :=
    congrArg Over.Hom.left ha
  have hflat : Flat (Spec.map (CommRingCat.ofHom a.hom.toRingHom)) :=
    hsmap ▸ (show Flat (e.hom.left ≫ pr.left) from inferInstance)
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom a.hom.toRingHom)) :=
    hsmap ▸ (show Surjective (e.hom.left ≫ pr.left) from inferInstance)
  refine ⟨S.unop, a, e.hom ≫ pullback.fst f' g',
    ((flat_and_surjective_SpecMap_iff _).mp ⟨hflat, hsurj⟩).injective, ?_⟩
  change (e.hom ≫ pullback.fst f' g') ≫ f' = (testSpec k).map a.op ≫ g'
  rw [ha, Category.assoc, Category.assoc, pullback.condition]

/-- Restriction along a central isogeny preserves and reflects scheme
invariance of a homogeneous polynomial. -/
theorem symmetricFixed_pullback_iff {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (hf : CentralIsogenies.IsCentralIsogeny f)
    (ρ : Representation H.val J) (v : MvPolynomial J k) :
    SymmetricFixed ((groupPointsFunctor k).map f ≫ ρ) v ↔ SymmetricFixed ρ v := by
  refine ⟨?_, fun hv R g ↦ hv R (g ≫ f.hom.hom)⟩
  intro hv R g
  obtain ⟨S, a, x, ha, hx⟩ := liftPoint_after_injective_extension f hf.2.1 hf.2.2.1 R g
  apply (MvPolynomial.map_injective (f := a.hom.toRingHom) ha)
  rw [polynomialAction_map, ← repMatrix_mapPoints ρ a g, ← hx]
  have hmap : (MvPolynomial.map a.hom.toRingHom)
      (MvPolynomial.map (algebraMap k R) v) = MvPolynomial.map (algebraMap k S) v := by
    have hcomp : a.hom.toRingHom.comp (algebraMap k R) = algebraMap k S :=
      RingHom.ext a.hom.commutes
    rw [MvPolynomial.map_map, hcomp]
  rw [hmap]
  exact hv S x

section Coefficients

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

private def coefficientLinearMap (l : B →ₗ[A] C) :
    MvPolynomial J B →ₗ[A] MvPolynomial J C where
  toFun f := AddMonoidAlgebra.ofCoeff (f.coeff.mapRange l l.map_zero)
  map_add' f g := by
    ext m
    change l ((f + g).coeff m) = l (f.coeff m) + l (g.coeff m)
    simp
  map_smul' a f := by
    ext m
    change l ((a • f).coeff m) = a • l (f.coeff m)
    simp

private theorem coeff_coefficientLinearMap (l : B →ₗ[A] C) (f : MvPolynomial J B)
    (m : J →₀ ℕ) : (coefficientLinearMap l f).coeff m = l (f.coeff m) := rfl

private theorem coefficientLinearMap_monomial
    (l : B →ₗ[A] C) (d : J →₀ ℕ) (b : B) :
    coefficientLinearMap l (monomial d b) = monomial d (l b) := by
  ext m
  by_cases h : d = m <;> simp [coeff_coefficientLinearMap, coeff_monomial, h]

private theorem coefficientLinearMap_polynomialAction
    (l : B →ₗ[A] A) (M : Matrix J J A) (f : MvPolynomial J B) :
    coefficientLinearMap l (polynomialAction (M.map (algebraMap A B)) f) =
      polynomialAction M (coefficientLinearMap l f) := by
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial d b =>
    let P : MvPolynomial J A := ∏ i ∈ d.support, linearPolynomial (fun j ↦ M j i) ^ d i
    have hP : (∏ i ∈ d.support,
        linearPolynomial (fun j ↦ M.map (algebraMap A B) j i) ^ d i) =
          P.map (algebraMap A B) := by
      simp only [P, map_prod, map_pow, map_linearPolynomial, Matrix.map_apply]
    rw [coefficientLinearMap_monomial]
    unfold polynomialAction
    rw [bind₁_monomial, bind₁_monomial, hP]
    ext m
    change (coefficientLinearMap l (MvPolynomial.C b * P.map (algebraMap A B))).coeff m =
      (MvPolynomial.C (l b) * P).coeff m
    simp only [coeff_coefficientLinearMap, coeff_C_mul, coeff_map]
    rw [mul_comm b, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

private theorem coefficientLinearMap_eval
    (l : B →ₗ[A] A) (a : J → A) (f : MvPolynomial J B) :
    l (MvPolynomial.eval (fun j ↦ algebraMap A B (a j)) f) =
      MvPolynomial.eval a (coefficientLinearMap l f) := by
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial d b =>
    simp only [coefficientLinearMap_monomial, eval_monomial, Finsupp.prod, ← map_pow, ← map_prod]
    rw [mul_comm b, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

end Coefficients

section ScalarExtension

variable {K : Type u} [Field K] [Algebra k K]

private def baseChangedRepresentation {H : AffineAlgebraicGroup k}
    (ρ : Representation H.val J) : Representation ((groupBaseChange k K).obj H.val) J :=
  let e : (groupPointsFunctor K).obj ((groupBaseChange k K).obj H.val) ≅
      restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj H.val :=
    NatIso.ofComponents (fun R ↦ (baseChangePointGroupEquiv K H.val R).toGrpIso)
      (by
        intro R S f
        apply GrpCat.ext
        intro x
        exact baseChangePointsNaturality k K H.val.X f x)
  let e' : restrictTestAlgebra k K ⋙ StandardGroups.generalLinearPoints k J ≅
      StandardGroups.generalLinearPoints K J :=
    NatIso.ofComponents (fun R ↦ Iso.refl (GrpCat.of (Matrix.GeneralLinearGroup J R)))
      (by intro R S f; simp; rfl)
  e.hom ≫ Functor.whiskerLeft (restrictTestAlgebra k K) ρ ≫ e'.hom

private theorem baseChangedRepresentation_matrix {H : AffineAlgebraicGroup k}
    (ρ : Representation H.val J) (R : TestAlgebra K)
    (g : GroupPoints ((groupBaseChange k K).obj H.val) R) :
    ((baseChangedRepresentation (K := K) ρ).app R g).val =
      (ρ.app ((restrictTestAlgebra k K).obj R) (baseChangePointGroupEquiv K H.val R g)).val :=
  rfl

/-- A normalized homogeneous invariant obtained over a field extension descends
in the same degree. The descent projects coefficients along a linear retraction
of the scalar inclusion. -/
private theorem descend_invariant {H : AffineAlgebraicGroup k}
    (ρ : Representation H.val J) (a : J → k) {d : ℕ} (f : MvPolynomial J K)
    (hdegree : f.IsHomogeneous d)
    (hfixed : SymmetricFixed (H := Unipotent.baseChangedAlgebraicGroup K H)
      (baseChangedRepresentation ρ) f)
    (hvalue : MvPolynomial.eval (fun j ↦ algebraMap k K (a j)) f = 1) :
    ∃ g : MvPolynomial J k, g.IsHomogeneous d ∧ SymmetricFixed ρ g ∧
      MvPolynomial.eval a g = 1 := by
  obtain ⟨l, hl⟩ := (Algebra.linearMap k K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k K).injective)
  have hl1 : l 1 = 1 := by simpa using LinearMap.congr_fun hl 1
  refine ⟨coefficientLinearMap l f, ?_, ?_, ?_⟩
  · intro m hm
    apply hdegree
    intro hz
    exact hm (by rw [coeff_coefficientLinearMap, hz, map_zero])
  · intro R g
    letI : Algebra K (R ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    let T := CommAlgCat.of K (R ⊗[k] K)
    let R' := (restrictTestAlgebra k K).obj T
    let i : R ⟶ R' := ConcreteCategory.ofHom (C := CommAlgCat k) (X := R) (Y := R')
      (@AlgHom.mk k R R' _ _ _ R.algebra R'.algebra (algebraMap R (R ⊗[k] K))
        (fun x ↦ RingHom.congr_fun
          (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := k) (A := R) (B := K)) x))
    let g' : GroupPoints ((groupBaseChange k K).obj H.val) T :=
      (baseChangePointGroupEquiv K H.val T).symm (mapPoints i g)
    let L : (R ⊗[k] K) →ₗ[R] R :=
      (TensorProduct.AlgebraTensorModule.rid k R R).toLinearMap.comp (l.baseChange R)
    have hm : ((baseChangedRepresentation (K := K) ρ).app T g').val =
        (ρ.app R g).val.map (algebraMap R (R ⊗[k] K)) := by
      rw [baseChangedRepresentation_matrix]
      change (ρ.app R' ((baseChangePointGroupEquiv K H.val T)
        ((baseChangePointGroupEquiv K H.val T).symm (mapPoints i g)))).val = _
      rw [MulEquiv.apply_symm_apply, repMatrix_mapPoints]
      rfl
    have hc : coefficientLinearMap L (f.map (algebraMap K (R ⊗[k] K))) =
        (coefficientLinearMap l f).map (algebraMap k R) := by
      ext m
      simp only [coeff_coefficientLinearMap, coeff_map]
      change L ((1 : R) ⊗ₜ[k] f.coeff m) = algebraMap k R (l (f.coeff m))
      simp [L, Algebra.smul_def]
    have h := hfixed T g'
    change polynomialAction ((baseChangedRepresentation (K := K) ρ).app T g').val
        (f.map (algebraMap K (R ⊗[k] K))) = f.map (algebraMap K (R ⊗[k] K)) at h
    rw [hm] at h
    have hh := congrArg (coefficientLinearMap L) h
    rw [coefficientLinearMap_polynomialAction, hc] at hh
    exact hh
  · rw [← coefficientLinearMap_eval, hvalue, hl1]

private def baseChangedQuotient (q : (J → k) →ₗ[k] k) : (J → K) →ₗ[K] K where
  toFun v := ∑ j, algebraMap k K (q (Pi.single j 1)) * v j
  map_add' u v := by simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem baseChangedQuotient_basis (q : (J → k) →ₗ[k] k) (j : J) :
    baseChangedQuotient (K := K) q (Pi.single j 1) = algebraMap k K (q (Pi.single j 1)) := by
  change (∑ i, algebraMap k K (q (Pi.single i 1)) * (Pi.single j 1 : J → K) i) = _
  simp [Pi.single_apply]

private theorem baseChangedQuotient_isTrivial {H : AffineAlgebraicGroup k}
    (ρ : Representation H.val J) (q : (J → k) →ₗ[k] k) (hq : IsTrivialQuotient ρ q) :
    IsTrivialQuotient (H := Unipotent.baseChangedAlgebraicGroup K H)
      (baseChangedRepresentation ρ) (baseChangedQuotient q) := by
  constructor
  · obtain ⟨x, hx⟩ := hq.1 1
    have hxsum : (∑ j, q (Pi.single j 1) * x j) = 1 := by
      calc
        _ = MvPolynomial.eval (fun j ↦ q (Pi.single j 1)) (linearPolynomial x) := by
          simp [linearPolynomial, smul_eq_C_mul, map_sum, mul_comm]
        _ = 1 := (eval_linearPolynomial q x).trans hx
    have hxK : baseChangedQuotient (K := K) q (extendVector (CommAlgCat.of k K) x) = 1 := by
      change (∑ j, algebraMap k K (q (Pi.single j 1)) * algebraMap k K (x j)) = 1
      simp only [← map_mul, ← map_sum, hxsum, map_one]
    intro t
    refine ⟨t • extendVector (CommAlgCat.of k K) x, ?_⟩
    rw [map_smul, hxK, smul_eq_mul, mul_one]
  · intro R g x
    let R₀ := (restrictTestAlgebra k K).obj R
    let g₀ := baseChangePointGroupEquiv K H.val R g
    simp only [baseChangedQuotient_basis]
    have hrow (j : J) : algebraMap K R (algebraMap k K (q (Pi.single j 1))) =
        algebraMap k R₀ (q (Pi.single j 1)) := rfl
    simp only [hrow]
    change (∑ j, algebraMap k R₀ (q (Pi.single j 1)) *
      (((baseChangedRepresentation (K := K) ρ).app R g).val.mulVec x) j) = _
    rw [baseChangedRepresentation_matrix (K := K) ρ R g]
    exact hq.2 R₀ g₀ x

end ScalarExtension

section Reduction

open Specs.GeometricRadicals (GeometricGroup)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)

/-- Reduction to the endomorphism lift over an algebraically closed field,
using semisimple base change and the split simply connected cover. -/
theorem invariantLifting_of_simplyConnected
    (semisimpleBaseChange : RadicalBaseChange.SemisimpleFieldExtension.{u})
    (maximalToriExist : MaximalToriExist.GeometricallyMaximalTorusExists.{u})
    (splitOverAlgClosed : ∀ {K : Type u} [Field K] [IsAlgClosed K]
      {G : AffineAlgebraicGroup K} (T : ClosedSubgroup G.val), GeometricRadicals.IsTorus T.group →
      GeometricRadicals.IsSplitTorus T.group)
    (reductiveOfSemisimple : ∀ {K : Type u} [Field K] (G : AffineAlgebraicGroup K),
      Specs.GeometricRadicals.IsSemisimple G → GeometricRadicals.IsReductive G)
    (attachedDatum : AbstractPairing.Statement.{u})
    (splitCover : SimplyConnectedLattice.SplitCover.{u})
    (lift : ∀ {K : Type u} [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
      (G : AffineAlgebraicGroup K), Specs.GeometricRadicals.IsSemisimple G → GeometricallySimplyConnected G →
      ∀ {J : Type u} [Fintype J] [DecidableEq J] (ρ : Representation G.val J)
        (q : (J → K) →ₗ[K] K), IsTrivialQuotient ρ q →
        ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (_ : Nonempty I)
          (S : Representation G.val I) (F : Matrix I I (J → K)), IsEndomorphismLift ρ S q F) :
    InvariantLifting.{u} := by
  intro k _ p _ _ H hH J _ _ ρ q hq
  let K := AlgebraicClosure k
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let G := GeometricGroup H
  have hG : Specs.GeometricRadicals.IsSemisimple G :=
    (semisimpleBaseChange H hH.1 hH.2.1).mpr hH
  letI := hG.2.1
  obtain ⟨T, ht, htmax⟩ := maximalToriExist G
    hG.1 (GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom)
  have hsplit := splitOverAlgClosed T ht
  obtain ⟨comm, ⟨D⟩⟩ := attachedDatum
    G (reductiveOfSemisimple G hG) T hsplit htmax
  letI := comm
  obtain ⟨P, _, coverHom, _, hP, hsc, hCover, _⟩ :=
    splitCover G hG T hsplit htmax D
  let ρK := baseChangedRepresentation (K := K) ρ
  let qK := baseChangedQuotient (K := K) q
  let ρ' : Representation P.G.val J := (groupPointsFunctor K).map coverHom ≫ ρK
  have hqK : IsTrivialQuotient (H := G) ρK qK := baseChangedQuotient_isTrivial ρ q hq
  have hq' : IsTrivialQuotient ρ' qK :=
    ⟨hqK.1, fun R g x ↦ hqK.2 R (g ≫ coverHom.hom.hom) x⟩
  obtain ⟨I, hI, dI, nI, S, F, hF⟩ := lift p P.G hP hsc ρ' qK hq'
  letI := hI
  letI := dI
  letI := nI
  obtain ⟨f, hf, hfix, hv⟩ := invariant_of_endomorphism_lift ρ' S qK F hF
  have hfixK : SymmetricFixed (H := G) ρK f :=
    (symmetricFixed_pullback_iff coverHom hCover ρK f).mp hfix
  have hvK : MvPolynomial.eval (fun j ↦ algebraMap k K (q (Pi.single j 1))) f = 1 := by
    simpa only [qK, baseChangedQuotient_basis] using hv
  obtain ⟨v, hvd, hvfix, hvval⟩ := descend_invariant ρ _ f hf hfixK hvK
  exact ⟨Fintype.card I, v, Fintype.card_pos, hvd, hvfix, hvval⟩

end Reduction

end LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry CategoryTheory.MonObj BigOperators
namespace LinearAlgebraicGroups.Arithmetic.GeometricReductivity
open _root_.LinearAlgebraicGroups.Specs
open Specs.FlagLineBundle (OppositeBorelPair AssociatedBundle)
open Specs.QuotientEmbedding (Presentation)
open Specs.AssociatedFlagLineSheaves (groundScalars SectionRealization)
open Specs.SteinbergFrobeniusPushforward (freeModule freeGenerator)
open Specs.LinePushforwardProjection (structureModule)
open Scheme.Modules
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private irreducible_of_geometricallyConnected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem groundScalars_surjective {k : Type u} [Field k] [IsAlgClosed k]
    (Y : SchemeOver k) [IsIntegral Y.left] [UniversallyClosed Y.hom] :
    Function.Surjective (groundScalars Y) := by
  letI : Algebra k Γ(Y.left, ⊤) := (groundScalars Y).hom.toAlgebra
  haveI : Algebra.IsIntegral k Γ(Y.left, ⊤) := by
    constructor
    change (groundScalars Y).hom.IsIntegral
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed Y.hom
  letI : IsDomain Γ(Y.left, ⊤) := inferInstance
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral.surjective

private theorem flag_integral {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) (Q : Presentation P.negative) (h : Smooth Q.scheme.hom) :
    IsIntegral Q.scheme.left := by
  letI : QuasiCompact G.val.X.hom := G.property.2.2
  letI : Smooth G.val.X.hom := P.reductive.1
  letI : GeometricallyConnected G.val.X.hom := P.reductive.2.1
  letI : IrreducibleSpace G.val.X.left := irreducible_of_geometricallyConnected G.val
  letI : IrreducibleSpace Q.scheme.left :=
    Q.surjective.surj.irreducibleSpace Q.projection.left.continuous
  letI : IsReduced Q.scheme.left := isReduced_of_smooth_over_field Q.scheme.hom
  exact isIntegral_of_irreducibleSpace_of_isReduced _

private theorem freeSections_sum {X : Scheme.{u}} {I : Type u} [Fintype I]
    (s : Γ(freeModule X I, ⊤)) :
    ∃ a : I → Γ(X, ⊤), s = ∑ i, a i • freeGenerator X i := by
  classical
  let U := structureModule X
  let F := freeModule X I
  let j (i : I) : U ⟶ F := SheafOfModules.ιFree i
  let p (i : I) : F ⟶ U :=
    Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan I)
      (fun h ↦ if h = i then 𝟙 U else 0)
  have hp (i h : I) : j h ≫ p i = if h = i then 𝟙 U else 0 :=
    Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan I) _ h
  have hsum : (∑ i, p i ≫ j i) = 𝟙 F := by
    apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I)
    intro h
    change j h ≫ (∑ i, p i ≫ j i) = j h ≫ 𝟙 F
    simp [Preadditive.comp_sum, ← Category.assoc, hp, ite_comp, Finset.sum_ite_eq]
  let c (i : I) : Γ(X, ⊤) := (p i).app ⊤ s
  refine ⟨c, ?_⟩
  have hs := congrArg (fun f : F ⟶ F ↦ f.app ⊤ s) hsum
  change _ = s at hs
  calc
    s = (∑ i, p i ≫ j i).app ⊤ s := hs.symm
    _ = ∑ i, c i • freeGenerator X i := by
      let ev : (F ⟶ F) →+ Γ(F, ⊤) :=
        { toFun := fun h ↦ h.app ⊤ s
          map_zero' := by simp
          map_add' := by intros; simp [Hom.add_app] }
      change ev (∑ i, p i ≫ j i) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (j i).app ⊤ (c i) = c i • (j i).app ⊤ (1 : Γ(X, ⊤))
      rw [← Hom.app_smul, smul_eq_mul, mul_one]


open Specs.GeometricRadicals (IsSemisimple IsUnipotentRadical)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.SteinbergDimension (IsHalfPositiveRootSum)
open Specs.CharacterDescent (Character)
open Specs.SimpleClassification (SocleModel)
open Specs.FlagRelativeFrobeniusAtlas (twist)
open FlagRelativeFrobeniusAtlas (relativeFrobenius relativeFrobenius_formula)
open LinearAlgebraicGroups.AssociatedFlagLineSheaves (realizeSections globalCovariantSections)
open private exists_associatedBundle from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private coordinate_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
open private linePointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle
open Specs.FlagLineBundle (linePoint)
open private socleInclusion from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylModules

/-- The actual socle inclusion of the Steinberg module is onto the induced
module. Global sections of the free Frobenius direct image are spanned by
the socle evaluations because the flag has only scalar global functions. -/
private theorem steinbergSocle_surjective {k : Type u} [Field k] [IsAlgClosed k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] (hr : 1 ≤ r)
    {G : AffineAlgebraicGroup k} (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (U : ClosedSubgroup P.positive.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (ρ : Character P.torus.group) (hρ : IsHalfPositiveRootSum P ρ)
    (S : SocleModel P U (Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ))) :
    Function.Surjective (socleInclusion S) := by
  classical
  let σ := Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)
  obtain ⟨_, ⟨Q⟩, hQ⟩ := LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P
  obtain ⟨hs, hp, _, _, _, _, _, a, _, _, ha⟩ := hQ Q
  obtain ⟨L⟩ := exists_associatedBundle Q S.projection σ a ha
  let M := realizeSections L
  letI : Module k Γ(M.sheaf, ⊤) := Module.compHom _ (groundScalars Q.scheme).hom
  obtain ⟨E, hE⟩ := globalCovariantSections M S.groupIso S.borelIso S.restriction S.character
    S.restriction_spec S.character_spec S.coordinate S.coordinate_spec
  let Y := (twist p r).obj Q.scheme
  let F := (relativeFrobenius p r).app Q.scheme
  obtain ⟨e, he⟩ := LinearAlgebraicGroups.SteinbergFrobeniusPushforward.steinbergEvaluationIso
    p r hr hG hsc P U hU ρ hρ S M F (relativeFrobenius_formula p r Q.scheme)
  haveI : IsIntegral Y.left := flag_integral P Q hs
  haveI : UniversallyClosed Y.hom := by
    letI := hp
    let iso := (iterateFrobeniusEquiv k p r).symm.toRingHom
    haveI : IsIso (CommRingCat.ofHom iso) :=
      (iterateFrobeniusEquiv k p r).symm.toCommRingCatIso.isIso_hom
    change UniversallyClosed (Q.scheme.hom ≫ Spec.map (CommRingCat.ofHom iso))
    infer_instance
  have hg := groundScalars_surjective Y
  let N := (pushforward F.left).obj M.sheaf
  have hscalar (c : k) : F.left.appTop (groundScalars Y c) = groundScalars Q.scheme c := by
    have hh := congrArg Scheme.Hom.appTop (Over.w F)
    rw [Scheme.Hom.comp_appTop] at hh
    exact congrArg (fun f ↦ f ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) hh
  let vgen (i : S.J) : Γ(M.sheaf, ⊤) := e.hom.app ⊤ (freeGenerator Y.left i)
  have hEgen (i : S.J) :
      S.inducedBasis.equivFun (E (e.hom.app ⊤ (freeGenerator Y.left i))) =
        socleInclusion S (Pi.single i 1) := by
    have h := (hE (e.hom.app ⊤ (freeGenerator Y.left i))).symm.trans (he i)
    have hc := coordinate_unique L (𝟙 G.val.X) _ _ (Over.OverMorphism.ext h)
    have hh := (cancel_epi S.groupIso.inv.hom.hom).mp hc
    have hval := (linePointEquiv (CommAlgCat.of k S.A)).injective hh
    have heq : E (e.hom.app ⊤ (freeGenerator Y.left i)) =
        S.inducedBasis.equivFun.symm (S.socleBasis i : S.I → k) :=
      Subtype.ext hval
    rw [heq, LinearEquiv.apply_symm_apply]
    change (S.socleBasis i : S.I → k) = (S.socleBasis.equivFun.symm (Pi.single i 1) : S.socle)
    apply congrArg Subtype.val
    apply S.socleBasis.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    ext j
    simp [Pi.single_apply, eq_comm]
  intro v
  let x := E.symm (S.inducedBasis.equivFun.symm v)
  obtain ⟨c, hc⟩ := freeSections_sum (e.inv.app ⊤ x)
  choose b hb using fun i ↦ hg (c i)
  refine ⟨b, ?_⟩
  have hx : x = ∑ i, (b i : k) • vgen i := by
    have heq : e.hom.app ⊤ (e.inv.app ⊤ x) = x := by
      exact congrArg (fun f : N ⟶ N ↦ f.app ⊤ x) e.inv_hom_id
    calc
      x = e.hom.app ⊤ (e.inv.app ⊤ x) := heq.symm
      _ = ∑ i, (b i : k) • vgen i := by
        rw [hc, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hm := Hom.app_smul e.hom (c i) (freeGenerator Y.left i)
        calc
          _ = c i • e.hom.app ⊤ (freeGenerator Y.left i) := hm
          _ = (groundScalars Y (b i)) • e.hom.app ⊤ (freeGenerator Y.left i) :=
            congrArg (fun d : Γ(Y.left, ⊤) ↦ d • e.hom.app ⊤ (freeGenerator Y.left i)) (hb i).symm
          _ = _ := congrArg (fun d : Γ(Q.scheme.left, ⊤) ↦ d • vgen i) (hscalar (b i))
  have hx' := congrArg (fun s ↦ S.inducedBasis.equivFun (E s)) hx
  simp only [x, LinearEquiv.apply_symm_apply, map_sum, _root_.map_smul, vgen, hEgen] at hx'
  rw [hx']
  calc
    socleInclusion S b = socleInclusion S (∑ i, b i • Pi.single i 1) := by
      congr 1
      symm
      simpa [Pi.basisFun_apply] using (Pi.basisFun k S.J).sum_repr b
    _ = _ := by simp only [map_sum, _root_.map_smul]
end LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open AlgebraicGeometry CategoryTheory
open scoped BigOperators Matrix Kronecker CategoryTheory.MonObj
namespace LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricReductivity (IsTrivialQuotient IsEndomorphismLift)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootWeightAction (Representation act actLinear extendVector)
open Specs.PrimitiveLine (IsEquivariant)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.CharacterPairing (characterValue)
open Specs.CharacterDescent (Character)
open Specs.SimpleClassification (SocleModel)
open Specs.WeylModules (IsDual)
open private extendFunctional extendFunctional_apply retract_of_character evaluationAtOne
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CostandardExtensions
open private isDual_exists isDual_symm dotDual dotDual_apply transposeMap transposeMap_dot
  transposeMap_equivariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylModules

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Matrices

variable {k I J : Type u} [Field k]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private def extendMap (R : TestAlgebra k) (f : (I → k) →ₗ[k] (J → k)) :
    (I → R) →ₗ[R] (J → R) :=
  LinearMap.pi (fun j ↦ extendFunctional R ((LinearMap.proj j).comp f))

private theorem extendMap_apply (R : TestAlgebra k) (f : (I → k) →ₗ[k] (J → k))
    (x : I → R) (j : J) :
    extendMap R f x j = ∑ i, algebraMap k R (f (Pi.single i 1) j) * x i := by
  simp [extendMap, extendFunctional, Pi.basisFun_apply, Algebra.smul_def]

private theorem extendMap_ground (R : TestAlgebra k) (f : (I → k) →ₗ[k] (J → k))
    (x : I → k) :
    extendMap R f (extendVector R x) = extendVector R (f x) :=
  funext fun j ↦ extendFunctional_apply R ((LinearMap.proj j).comp f) x

private theorem extendMap_natural {R A : TestAlgebra k} (a : R ⟶ A)
    (f : (I → k) →ₗ[k] (J → k)) (x : I → R) :
    extendMap A f (fun i ↦ a.hom (x i)) = fun j ↦ a.hom (extendMap R f x j) := by
  funext j
  simp only [extendMap_apply, map_sum, map_mul, AlgHom.commutes]

private theorem scalarExtension_ext (R : TestAlgebra k) {V : Type u}
    [AddCommGroup V] [Module R V] {f g : (I → R) →ₗ[R] V}
    (h : ∀ x : I → k, f (extendVector R x) = g (extendVector R x)) : f = g := by
  apply (Pi.basisFun R I).ext
  intro i
  simpa only [extend_basis, Pi.basisFun_apply] using h (Pi.single i 1)

private theorem extendMap_equivariant {H : AffineAlgebraicGroup k}
    {S : Representation H.val I} {T : Representation H.val J}
    (f : (I → k) →ₗ[k] (J → k)) (hf : IsEquivariant S T f)
    (R : TestAlgebra k) (g : GroupPoints H.val R) (x : I → R) :
    extendMap R f (act S R g x) = act T R g (extendMap R f x) := by
  have he : (extendMap R f).comp (actLinear S R g) =
      (actLinear T R g).comp (extendMap R f) := by
    apply scalarExtension_ext
    intro v
    change extendMap R f (act S R g (extendVector R v)) =
      act T R g (extendMap R f (extendVector R v))
    rw [extendMap_ground]
    funext j
    rw [extendMap_apply]
    exact (equivariant_apply_over_algebra f hf R g v j).symm
  exact LinearMap.congr_fun he x

private def tensorVector {R : Type u} [CommRing R] (x : I → R) (y : J → R) :
    I × J → R := fun ij ↦ x ij.1 * y ij.2

private theorem act_tensorVector {H : AffineAlgebraicGroup k}
    (S : Representation H.val I) (ρ : Representation H.val J)
    (R : TestAlgebra k) (g : GroupPoints H.val R) (x : I → R) (y : J → R) :
    act (tensorRepresentation S ρ) R g (tensorVector x y) =
      tensorVector (act S R g x) (act ρ R g y) := by
  funext a
  rcases a with ⟨a, b⟩
  simp only [tensorVector, act, Matrix.mulVec, dotProduct,
    Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [tensorRepresentation_apply S ρ R g a i b j]
  ring

private theorem tensor_dual {H : AffineAlgebraicGroup k}
    {S S' : Representation H.val I} {ρ τ : Representation H.val J}
    (hs : IsDual S S') (hρ : IsDual ρ τ) :
    IsDual (tensorRepresentation S ρ) (tensorRepresentation S' τ) := by
  intro R g
  rw [← (tensorRepresentation S ρ).app R |>.hom.map_inv]
  ext ⟨i, j⟩ ⟨a, b⟩
  simp only [Matrix.transpose_apply, tensorRepresentation_apply, hs R g, hρ R g]
  rw [(S.app R).hom.map_inv, (ρ.app R).hom.map_inv]

private theorem dotProduct_dual {H : AffineAlgebraicGroup k}
    {ρ τ : Representation H.val J} (h : IsDual ρ τ)
    (R : TestAlgebra k) (g : GroupPoints H.val R) (x y : J → R) :
    act ρ R g x ⬝ᵥ act τ R g y = x ⬝ᵥ y := by
  simp only [act, h R g, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec]
  rw [show ((ρ.app R g)⁻¹).val * (ρ.app R g).val = 1 from
    congrArg Units.val (inv_mul_cancel (ρ.app R g)), Matrix.one_mulVec, dotProduct_comm]

private def tensorFunctional (f : (I → k) →ₗ[k] (J → k)) :
    (I × J → k) →ₗ[k] k :=
  ∑ a : I × J, f (Pi.single a.1 1) a.2 • LinearMap.proj a

private theorem tensorFunctional_basis (f : (I → k) →ₗ[k] (J → k)) (a : I × J) :
    tensorFunctional f (Pi.single a 1) = f (Pi.single a.1 1) a.2 := by
  simp [tensorFunctional, Pi.single_apply, Finset.sum_ite_eq, eq_comm]

private theorem extendTensorFunctional_apply (R : TestAlgebra k)
    (f : (I → k) →ₗ[k] (J → k)) (x : I → R) (y : J → R) :
    extendFunctional R (tensorFunctional f) (tensorVector x y) =
      extendMap R f x ⬝ᵥ y := by
  simp only [extendFunctional, Pi.basisFun_apply, tensorFunctional_basis, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, dotProduct, extendMap_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  unfold tensorVector
  ring

private theorem transposeTensorQuotient (q : (J → k) →ₗ[k] k) (x : I → k) :
    transposeMap (tensorQuotient q) x = tensorVector x (fun j ↦ q (Pi.single j 1)) := by
  funext a
  have he := transposeMap_dot (tensorQuotient q) x (Pi.single a 1)
  rw [dotProduct_single_one] at he
  rw [he]
  simp only [tensorQuotient, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, tensorVector]
  have eq (i : I) : (fun j : J ↦ (Pi.single a (1 : k) : I × J → k) (i, j)) =
      if i = a.1 then Pi.single a.2 1 else 0 := by
    rcases a with ⟨a, b⟩
    ext j
    by_cases hi : i = a <;> simp [Pi.single_apply, hi, eq_comm]
  simp only [eq, apply_ite q, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- Frobenius reciprocity applied to a lift of the evaluation functional on
the opposite Borel, followed by duality on the tensor inclusion. -/
private theorem endomorphismLift_of_borelMap {H : AffineAlgebraicGroup k}
    {P : OppositeBorelPair H} {U : ClosedSubgroup P.positive.group}
    {χ : Character P.torus.group} (S : SocleModel P U χ)
    (ρ : Representation H.val J) (q : (J → k) →ₗ[k] k) (hq : IsTrivialQuotient ρ q)
    (f : (S.I → k) →ₗ[k] (J → k)) (hfq : q.comp f = evaluationAtOne S)
    (hf : ∀ (R : TestAlgebra k) (b : GroupPoints P.negative.group R) (x : S.I → R),
      extendMap R f (act S.inducedAction R (b ≫ P.negative.inclusion.hom.hom) x) =
        characterValue χ R (b ≫ S.projection.projection.hom.hom) •
          act ρ R (b ≫ P.negative.inclusion.hom.hom) (extendMap R f x)) :
    ∃ (S' : Representation H.val S.I) (F : Matrix S.I S.I (J → k)), IsEndomorphismLift ρ S' q F := by
  obtain ⟨S', hS'⟩ := isDual_exists S.A S.groupIso S.inducedAction
  obtain ⟨τ, hτ⟩ := isDual_exists S.A S.groupIso ρ
  let i := transposeMap (tensorQuotient (I := S.I) q)
  have hi : IsEquivariant S.inducedAction (tensorRepresentation S.inducedAction τ) i :=
    transposeMap_equivariant (tensor_dual (isDual_symm hS') hτ) (isDual_symm hS')
      (tensorQuotient_equivariant S' ρ q hq)
  let l := tensorFunctional f
  have hl : l.comp i = evaluationAtOne S := by
    apply LinearMap.ext
    intro x
    change l (i x) = evaluationAtOne S x
    rw [show i x = tensorVector x (fun j ↦ q (Pi.single j 1)) from transposeTensorQuotient q x]
    have h := extendTensorFunctional_apply (CommAlgCat.of k k) f x
      (fun j ↦ q (Pi.single j 1))
    rw [show extendMap (CommAlgCat.of k k) f x = f x from extendMap_ground _ f x] at h
    rw [show extendFunctional (CommAlgCat.of k k) (tensorFunctional f)
        (tensorVector x (fun j ↦ q (Pi.single j 1))) = l (tensorVector x (fun j ↦ q (Pi.single j 1)))
      from extendFunctional_apply (CommAlgCat.of k k) l _] at h
    rw [h, ← LinearMap.congr_fun hfq x]
    change f x ⬝ᵥ _ = q (f x)
    rw [linear_map_in_basis q (f x)]
    rfl
  have hc (R : TestAlgebra k) (b : GroupPoints P.negative.group R) (z : S.I × J → R) :
      extendFunctional R l (act (tensorRepresentation S.inducedAction τ) R
        (b ≫ P.negative.inclusion.hom.hom) z) =
      characterValue χ R (b ≫ S.projection.projection.hom.hom) * extendFunctional R l z := by
    let g := b ≫ P.negative.inclusion.hom.hom
    let c := characterValue χ R (b ≫ S.projection.projection.hom.hom)
    have h : (extendFunctional R l).comp (actLinear
        (tensorRepresentation S.inducedAction τ) R g) = c • extendFunctional R l := by
      apply (Pi.basisFun R (S.I × J)).ext
      intro a
      have ha : Pi.basisFun R (S.I × J) a = tensorVector (Pi.single a.1 1) (Pi.single a.2 1) := by
        ext z
        rcases a with ⟨i, j⟩
        rcases z with ⟨u, v⟩
        by_cases hi : u = i <;> by_cases hj : v = j <;>
          simp [Pi.basisFun_apply, tensorVector, hi, hj]
      rw [ha]
      change extendFunctional R l (act (tensorRepresentation S.inducedAction τ) R g
        (tensorVector _ _)) = c * extendFunctional R l (tensorVector _ _)
      rw [act_tensorVector, extendTensorFunctional_apply, extendTensorFunctional_apply,
        hf R b, show characterValue χ R (b ≫ S.projection.projection.hom.hom) = c from rfl]
      simp only [smul_dotProduct, smul_eq_mul]
      rw [dotProduct_dual hτ]
    exact LinearMap.congr_fun h z
  obtain ⟨r, hr, hri⟩ := retract_of_character S _ i hi l hl hc
  let s := transposeMap r
  have hse : IsEquivariant S' (tensorRepresentation S' ρ) s :=
    transposeMap_equivariant (tensor_dual hS' (isDual_symm hτ)) hS' hr
  have hs : (tensorQuotient q).comp s = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply dotDual.injective
    apply LinearMap.ext
    intro w
    change tensorQuotient q (s v) ⬝ᵥ w = v ⬝ᵥ w
    calc
      _ = w ⬝ᵥ tensorQuotient q (s v) := dotProduct_comm _ _
      _ = i w ⬝ᵥ s v := (transposeMap_dot _ _ _).symm
      _ = s v ⬝ᵥ i w := dotProduct_comm _ _
      _ = v ⬝ᵥ r (i w) := transposeMap_dot _ _ _
      _ = _ := congrArg (fun x ↦ v ⬝ᵥ x) (LinearMap.congr_fun hri w)
  obtain ⟨F, hF⟩ := endomorphism_lift_of_tensor_section ρ S' q s hs hse
  exact ⟨S', F, hF⟩

end Matrices
end LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open scoped AlgebraicGeometry CategoryTheory.MonObj BigOperators Matrix TensorProduct
namespace LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootWeightAction (Representation act extendVector weightSpace mem_weightSpace)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.RootGroups (rootPoint HasScalarAction)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.SteinbergDistributions (RootCoordinates orderedPoint)
open private rootPoint_natural act_extend_natural act_smul act_mul characterValue_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open private orderedPoint_conjugate characterValueHom characterValueHom_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SteinbergDistributions

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section OrbitPolynomials

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
variable {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T} {l : List (Root T)}
variable {I : Type u} [Fintype I] [DecidableEq I]

private theorem map_orderedPoint (x : RootCoordinates U l) {R S : TestAlgebra k}
    (f : R ⟶ S) (a : Fin l.length → R) :
    mapPoints f (orderedPoint x R a) = orderedPoint x S (fun i ↦ f.hom (a i)) := by
  let m := (((groupPointsFunctor k).obj G.val).map f).hom
  change m (List.ofFn _).prod = _
  rw [map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i ↦ rootPoint_natural _ f (a i)))

private def orbitPolynomials (x : RootCoordinates U l) (ρ : Representation G.val I)
    (v : I → k) : I → MvPolynomial (Fin l.length) k :=
  let R := CommAlgCat.of k (MvPolynomial (Fin l.length) k)
  act ρ R (orderedPoint x R X) (extendVector R v)

private theorem orbitPolynomials_eval (x : RootCoordinates U l) (ρ : Representation G.val I)
    (v : I → k) (R : TestAlgebra k) (a : Fin l.length → R) :
    (fun i ↦ aeval a (orbitPolynomials x ρ v i)) =
      act ρ R (orderedPoint x R a) (extendVector R v) := by
  let A := CommAlgCat.of k (MvPolynomial (Fin l.length) k)
  let f : A ⟶ R := CommAlgCat.ofHom (aeval a)
  have h := act_extend_natural ρ f (orderedPoint x A X) v
  rw [map_orderedPoint] at h
  simpa only [f, A, CommAlgCat.hom_ofHom, aeval_X, orbitPolynomials] using h.symm

private theorem coeff_aeval_scaled {n : ℕ} (R : TestAlgebra k) (c : Fin n → R)
    (P : MvPolynomial (Fin n) k) (d : Fin n →₀ ℕ) :
    (aeval (fun i ↦ C (c i) * X i : Fin n → MvPolynomial (Fin n) R) P).coeff d =
      algebraMap k R (P.coeff d) * ∏ i, c i ^ d i := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
    have hf :
        aeval (fun i ↦ C (c i) * X i : Fin n → MvPolynomial (Fin n) R)
          (monomial e a) = monomial e (algebraMap k R a * ∏ i, c i ^ e i) := by
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
      simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, monomial_eq,
        ← Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_mul]
      ac_rfl
    rw [hf, coeff_monomial, coeff_monomial]
    split
    · rename_i h
      subst e
      rfl
    · simp
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_mul]

private theorem orbitCoefficient_weight (x : RootCoordinates U l) (ρ : Representation G.val I)
    (h : ∀ i, HasScalarAction T (l.get i).val
      ((x.groupIso i).hom ≫ (U (l.get i)).val.inclusion))
    {χ : Character T.group} {v : I → k} (hv : v ∈ weightSpace ρ T χ)
    (d : Fin l.length →₀ ℕ) :
    (fun i ↦ (orbitPolynomials x ρ v i).coeff d) ∈
      weightSpace ρ T (χ * ∏ i : Fin l.length, (l.get i).val ^ d i) := by
  apply mem_weightSpace.mpr
  intro R t
  let B := CommAlgCat.of k (MvPolynomial (Fin l.length) R)
  let f : R ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R B)
  let tB := mapPoints f t
  let tG := t ≫ T.inclusion.hom.hom
  let tBG := tB ≫ T.inclusion.hom.hom
  let y := orderedPoint x B X
  let c (i : Fin l.length) := characterValue (l.get i).val R t
  let y' := orderedPoint x B (fun i ↦ C (c i) * X i)
  have hc (ψ : Character T.group) : characterValue ψ B tB = C (characterValue ψ R t) :=
    characterValue_natural ψ f t
  have hy : tBG * y = y' * tBG := by
    have hcj := orderedPoint_conjugate x B tB h (fun i ↦ X i)
    simp only [hc] at hcj
    change tBG * y * tBG⁻¹ = y' at hcj
    calc
      tBG * y = (tBG * y * tBG⁻¹) * tBG := by simp [mul_assoc]
      _ = y' * tBG := congrArg (· * tBG) hcj
  have he : act ρ B tBG (act ρ B y (extendVector B v)) =
      (C (characterValue χ R t) : B) • act ρ B y' (extendVector B v) := by
    rw [← act_mul, hy, act_mul]
    have ht := mem_weightSpace.mp hv B tB
    change act ρ B tBG (extendVector B v) = _ at ht
    rw [ht, hc, act_smul]
  rw [← orbitPolynomials_eval x ρ v B (fun i ↦ X i),
    ← orbitPolynomials_eval x ρ v B (fun i ↦ C (c i) * X i)] at he
  have hm : (ρ.app B tBG).val = (ρ.app R tG).val.map (C : R →+* MvPolynomial (Fin l.length) R) := by
    have e := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality f)) tG
    have h' := congrArg (fun M : Matrix.GeneralLinearGroup I B ↦ M.val) e
    simp only [GrpCat.hom_comp] at h'
    exact h'
  have hm' (j : I) :
      aeval (fun i : Fin l.length ↦ (X i : MvPolynomial _ R)) (orbitPolynomials x ρ v j) =
        (orbitPolynomials x ρ v j).map (algebraMap k R) := by
    have he : (aeval (fun i : Fin l.length ↦ (X i : MvPolynomial _ R))) =
        MvPolynomial.mapAlgHom (Algebra.ofId k R) := by
      apply MvPolynomial.algHom_ext
      simp
    rw [he]
    rfl
  funext i
  have eq := congrArg (fun z : I → MvPolynomial (Fin l.length) R ↦ (z i).coeff d) he
  simp only [act, hm, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
    smul_eq_mul] at eq
  change (∑ j, C ((ρ.app R tG).val i j) *
    aeval (fun s : Fin l.length ↦ (X s : MvPolynomial _ R)) (orbitPolynomials x ρ v j)).coeff d =
    (C (characterValue χ R t) *
      aeval (fun s : Fin l.length ↦ (C (c s) * X s : MvPolynomial _ R))
        (orbitPolynomials x ρ v i)).coeff d at eq
  rw [coeff_sum, coeff_C_mul, coeff_aeval_scaled] at eq
  simp_rw [coeff_C_mul, hm', coeff_map] at eq
  have hprod : characterValue (χ * ∏ j : Fin l.length, (l.get j).val ^ d j) R t =
      characterValue χ R t * ∏ j, c j ^ d j := by
    simp only [← characterValueHom_apply, map_mul, map_prod, map_pow, c]
  rw [hprod]
  change _ = (characterValue χ R t * ∏ j, c j ^ d j) *
    algebraMap k R ((orbitPolynomials x ρ v i).coeff d)
  exact eq.trans (by ring)

end OrbitPolynomials
section TruncatedOrbit

open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.SimpleClassification (SocleModel)
open Specs.GeometricRadicals (IsSemisimple IsUnipotentRadical)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.SteinbergDistributions (KernelPresentation powersIdeal)
open Specs.SteinbergDimension (IsHalfPositiveRootSum)
open Specs.InducedNonvanishing (Dominant)
open Specs.CharacterPairing (pairing)
open Specs.AbstractPairing (IsAttachedCoroot)
open Specs.OrderedRootProducts (Enumerates)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.RootWeightAction (SimpleRoot)
open LinearAlgebraicGroups.FiniteDistributions (Dist)
open LinearAlgebraicGroups.RationalRepresentations (tensorCoordinate)
open private truncatedBasis truncatedCoefficient truncatedMonomial truncatedBasis_apply
  truncatedCoefficient_monomial exponent
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SteinbergDistributions
open private negativeKernel_cyclic negativeAction negativeAction_coordinate negativeRestriction
  negativeRestriction_spec orbitCoordinate length_of_enumerates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SteinbergDimension
open private affinePoint affinePoint_specGroupMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} [IsAlgClosed k]

private theorem truncate_coord {n q : ℕ} (f : MvPolynomial (Fin n) k) (d : Fin n → Fin q) :
    (truncatedBasis k n q).coord d (Ideal.Quotient.mk _ f) = f.coeff (exponent d) := by
  let b := truncatedBasis k n q
  have h : b.coord d = truncatedCoefficient d := by
    apply b.ext
    intro j
    rw [Module.Basis.coord_apply, b.repr_self, show b j = truncatedMonomial j from truncatedBasis_apply j,
      truncatedCoefficient_monomial]
    by_cases he : j = d <;> simp [Finsupp.single_apply, he, eq_comm]
  exact congrArg (fun a ↦ a (Ideal.Quotient.mk (powersIdeal k (Fin n) q) f)) h

/-- The coefficients with exponents below the Frobenius power in each
ordered negative root coordinate form a basis of the Steinberg module. -/
private theorem truncatedSteinbergOrbit (p r : ℕ) [Fact p.Prime] [CharP k p]
    (hr : 1 ≤ r) (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (ω : Character P.torus.group) (hω : IsHalfPositiveRootSum P ω)
    {U : ClosedSubgroup P.positive.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (S : SocleModel P U (Additive.toMul ((p ^ r - 1) • Additive.ofMul ω)))
    (N : ClosedSubgroup P.negative.group)
    (hN : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.negative) N)
    (PN : KernelPresentation p r N.group)
    {family : RootSubgroupFamily P.torus} {l : List (Root P.torus)}
    (lpos : List (Root P.torus)) (hlen : l.length = lpos.length)
    (hlpos : Enumerates lpos (subgroupRoots P.torus P.positive))
    (x : RootCoordinates family l)
    (e : (MvPolynomial (Fin l.length) k ⧸ powersIdeal k (Fin l.length) (p ^ r)) ≃ₐ[k] PN.hopf)
    (hchart : ∀ (R : TestAlgebra k) (a : PN.hopf →ₐ[k] R),
      affinePoint R a ≫ PN.inclusion ≫ (N.inclusion ≫ P.negative.inclusion).hom.hom =
        orderedPoint x R (fun i ↦ a (e (Ideal.Quotient.mk _ (MvPolynomial.X i))))) :
    ∃ B : Module.Basis (Fin l.length → Fin (p ^ r)) k (S.J → k),
      ∀ d j, B d j =
        (orbitPolynomials x S.socleAction (S.socleBasis.equivFun S.highestVector) j).coeff (exponent d) := by
  classical
  let q := p ^ r
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos r
  have hp := LinearAlgebraicGroups.Representation.SteinbergDimension.steinbergWeight_pairing P ω hω q
  have hdom : Dominant P (Additive.toMul ((q - 1) • Additive.ofMul ω)) := by
    intro a c hc
    rw [hp a c hc]
    exact Int.natCast_nonneg _
  have hsmall (a : SimpleRoot P.torus P.positive) (c : Specs.CharacterDescent.Cocharacter P.torus.group)
      (hc : IsAttachedCoroot P.torus a.val c) :
      pairing P.torus.group (Additive.toMul ((q - 1) • Additive.ofMul ω)) c < (q : ℤ) := by
    rw [hp a c hc]
    omega
  let b := (truncatedBasis k l.length q).map e.toLinearEquiv
  letI : FiniteDimensional k PN.hopf := Module.Finite.of_basis b
  letI : HopfAlgebra k PN.hopf := CommHopfAlgCat.hopfAlgebra PN.hopf
  let A := negativeAction S N PN
  let f : Module.Dual k PN.hopf →ₗ[k] S.socle :=
    (A.toLinearMap.flip S.highestVector).comp (WithConv.linearEquiv k (Module.Dual k PN.hopf)).symm.toLinearMap
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨a, ha⟩ := negativeKernel_cyclic hr S hU hdom hsmall N hN PN v
    exact ⟨a.ofConv, by simpa [f, A] using ha⟩
  have hdim : Module.finrank k (Module.Dual k PN.hopf) = Module.finrank k S.socle := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis b,
      LinearAlgebraicGroups.Representation.SteinbergDimension.dimension p r hr hG hsc P ω hω U hU S,
      ← length_of_enumerates hlpos, ← hlen]
    simp [q]
  have hf : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  let E := (LinearEquiv.ofBijective f ⟨hf, hsurj⟩).trans S.socleBasis.equivFun
  let B := b.dualBasis.map E
  refine ⟨B, fun d j ↦ ?_⟩
  let C := CommAlgCat.of k PN.hopf
  let a : MvPolynomial (Fin l.length) k →ₐ[k] C :=
    e.toAlgHom.comp (Ideal.Quotient.mkₐ k (powersIdeal k (Fin l.length) q))
  let v := S.socleBasis.equivFun S.highestVector
  let pol := orbitPolynomials x S.socleAction v j
  have ha : a pol = (negativeRestriction S N PN).hom.toAlgHom
      (tensorCoordinate S.socleBasis j (S.socleCoaction.coaction S.highestVector)) := by
    have hav : a = aeval (fun i ↦ a (X i)) := aeval_unique a
    have ho := congrFun (orbitPolynomials_eval x S.socleAction v C (fun i ↦ a (X i))) j
    change aeval (fun i ↦ a (X i)) pol = _ at ho
    rw [← hav] at ho
    have hp := hchart C (AlgHom.id k PN.hopf)
    change _ = orderedPoint x C (fun i ↦ a (X i)) at hp
    rw [← hp, ← negativeRestriction_spec S N PN, ← Category.assoc,
      affinePoint_specGroupMap] at ho
    rw [orbitCoordinate S] at ho
    exact ho
  rw [show B d = E (b.coord d) by simp [B]]
  change S.socleBasis.equivFun (negativeAction S N PN (WithConv.toConv (b.coord d))
    S.highestVector) j = _
  rw [negativeAction_coordinate S N PN, ← ha]
  change ((truncatedBasis k l.length q).map e.toLinearEquiv).coord d
    (e.toLinearEquiv (Ideal.Quotient.mk _ pol)) = _
  rw [Module.Basis.coord_apply, Module.Basis.map_repr, LinearEquiv.trans_apply]
  have hh := e.toLinearEquiv.symm_apply_apply
    (Ideal.Quotient.mk (powersIdeal k (Fin l.length) q) pol)
  rw [hh]
  exact truncate_coord pol d

end TruncatedOrbit

end LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open scoped AlgebraicGeometry CategoryTheory.MonObj BigOperators Matrix
namespace LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootWeightAction (Representation act actLinear extendVector weightSpace mem_weightSpace)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.RootGroups (HasScalarAction)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.SteinbergDistributions (RootCoordinates orderedPoint)
open Specs.FlagLineBundle (OppositeBorelPair)
open private exponent from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SteinbergDistributions
open private weightProjection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CyclicHighestWeight
open private weightSpacesIndependent from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {k I J : Type u} [Field k]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {G : AffineAlgebraicGroup k}

private theorem map_weight_from_basis {T : ClosedSubgroup G.val}
    (S : Representation G.val I) (ρ : Representation G.val J) (χ : Character T.group)
    {A : Type*} [Fintype A] (B : Module.Basis A k (I → k))
    (mu : A → Character T.group) (f : (I → k) →ₗ[k] (J → k))
    (hS : ∀ a, B a ∈ weightSpace S T (χ * mu a))
    (hρ : ∀ a, f (B a) ∈ weightSpace ρ T (mu a))
    (ν : Character T.group) {v : I → k} (hv : v ∈ weightSpace S T (χ * ν)) :
    f v ∈ weightSpace ρ T ν := by
  classical
  obtain ⟨P, hP⟩ := weightProjection S T (χ * ν)
  have hPv : P v = v := by rw [hP _ _ hv, ite_eq_left rfl]
  rw [← hPv, ← B.sum_repr v]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.smul_mem
  by_cases ha : mu a = ν
  · simpa [hP _ _ (hS a), ha] using hρ a
  · have hne : χ * mu a ≠ χ * ν := fun h ↦ ha (mul_left_cancel h)
    rw [hP _ _ (hS a), ite_eq_right hne, map_zero]
    exact Submodule.zero_mem _

private theorem weights_bounded_below (P : OppositeBorelPair G)
    (ρ : Representation G.val J) (height : Additive (Character P.torus.group) →ₗ[ℤ] ℤ) :
    ∃ N : ℕ, ∀ mu, weightSpace ρ P.torus mu ≠ ⊥ → -(N : ℤ) ≤ height (Additive.ofMul mu) := by
  classical
  let s := (Submodule.finite_ne_bot_of_iSupIndep (weightSpacesIndependent P ρ)).toFinset
  let N := ∑ mu ∈ s, (height (Additive.ofMul mu)).natAbs
  refine ⟨N, fun mu hm ↦ ?_⟩
  have hmem : mu ∈ s := by simpa [s] using hm
  have hle : (height (Additive.ofMul mu)).natAbs ≤ N :=
    Finset.single_le_sum (f := fun mu ↦ (height (Additive.ofMul mu)).natAbs)
      (fun _ _ ↦ Nat.zero_le _) hmem
  omega

private theorem height_of_large_exponent {T : ClosedSubgroup G.val}
    (height : Additive (Character T.group) →ₗ[ℤ] ℤ) {n : ℕ}
    (α : Fin n → Character T.group) (hα : ∀ i, height (Additive.ofMul (α i)) ≤ -1)
    (d : Fin n →₀ ℕ) (i : Fin n) :
    height (Additive.ofMul (∏ j, α j ^ d j)) ≤ -(d i : ℤ) := by
  rw [ofMul_prod, map_sum]
  simp only [ofMul_pow, map_nsmul, nsmul_eq_mul]
  calc
    (∑ j, (d j : ℤ) * height (Additive.ofMul (α j))) ≤ ∑ j, -(d j : ℤ) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [mul_neg_one] using mul_le_mul_of_nonneg_left (hα j) (Int.natCast_nonneg (d j))
    _ ≤ _ := by
      rw [Finset.sum_neg_distrib, neg_le_neg_iff]
      exact Finset.single_le_sum (fun j _ ↦ Int.natCast_nonneg (d j)) (Finset.mem_univ i)

private theorem extendMap_coeff {n : ℕ} (f : (I → k) →ₗ[k] (J → k))
    (x : I → MvPolynomial (Fin n) k) (d : Fin n →₀ ℕ) (j : J) :
    (extendMap (CommAlgCat.of k (MvPolynomial (Fin n) k)) f x j).coeff d =
      f (fun i ↦ (x i).coeff d) j := by
  rw [extendMap_apply, linear_map_in_basis f]
  change (∑ i, C (f (Pi.single i 1) j) * x i).coeff d = _
  simp only [coeff_sum, coeff_C_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- Once the cutoff is past the lowest target weight, the linear map between
truncated orbit coefficients intertwines the entire ordered root orbit. -/
private theorem map_of_truncated_orbits
    {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T} {l : List (Root T)}
    (x : RootCoordinates U l)
    (h : ∀ i, HasScalarAction T (l.get i).val ((x.groupIso i).hom ≫ (U (l.get i)).val.inclusion))
    (S : Representation G.val I) (ρ : Representation G.val J)
    (χ : Character T.group) {v : I → k} {w : J → k}
    (hv : v ∈ weightSpace S T χ) (hw : w ∈ weightSpace ρ T 1)
    (N q : ℕ) (hq : N < q)
    (height : Additive (Character T.group) →ₗ[ℤ] ℤ)
    (hneg : ∀ i : Fin l.length, height (Additive.ofMul (l.get i).val) ≤ -1)
    (hbound : ∀ mu, weightSpace ρ T mu ≠ ⊥ → -(N : ℤ) ≤ height (Additive.ofMul mu))
    (B : Module.Basis (Fin l.length → Fin q) k (I → k))
    (hB : ∀ d i, B d i = (orbitPolynomials x S v i).coeff (exponent d)) :
    ∃ f : (I → k) →ₗ[k] (J → k),
      (∀ mu, ∀ v' ∈ weightSpace S T (χ * mu), f v' ∈ weightSpace ρ T mu) ∧
      (∀ (R : TestAlgebra k) (a : Fin l.length → R),
        extendMap R f (act S R (orderedPoint x R a) (extendVector R v)) =
          act ρ R (orderedPoint x R a) (extendVector R w)) := by
  classical
  let mu (d : Fin l.length →₀ ℕ) : Character T.group := ∏ i, (l.get i).val ^ d i
  let vfun (d : Fin l.length →₀ ℕ) : I → k := fun i ↦ (orbitPolynomials x S v i).coeff d
  let wfun (d : Fin l.length →₀ ℕ) : J → k := fun i ↦ (orbitPolynomials x ρ w i).coeff d
  let f := B.constr k (fun d ↦ wfun (exponent d))
  have hvb (d) : vfun (exponent d) = B d := funext (fun i ↦ (hB d i).symm)
  have hfb (d) : f (B d) = wfun (exponent d) := B.constr_basis k _ d
  have hvs (d) : vfun d ∈ weightSpace S T (χ * mu d) := orbitCoefficient_weight x S h hv d
  have hws (d) : wfun d ∈ weightSpace ρ T (mu d) := by
    simpa only [one_mul] using orbitCoefficient_weight x ρ h hw d
  have hweight (ν) (z) (hz : z ∈ weightSpace S T (χ * ν)) :
      f z ∈ weightSpace ρ T ν :=
    map_weight_from_basis S ρ χ B (fun d ↦ mu (exponent d)) f
      (fun d ↦ hvb d ▸ hvs _) (fun d ↦ (hfb d).symm ▸ hws _) ν hz
  refine ⟨f, hweight, ?_⟩
  have hcoeff (d) : f (vfun d) = wfun d := by
    by_cases hd : ∀ i, d i < q
    · let b : Fin l.length → Fin q := fun i ↦ ⟨d i, hd i⟩
      have hbd : exponent b = d := by ext i; rfl
      rw [← hbd, hvb, hfb]
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      have hlt := height_of_large_exponent height (fun i ↦ (l.get i).val) hneg d i
      have hbot : weightSpace ρ T (mu d) = ⊥ := by
        by_contra hn
        have hlow := hbound (mu d) hn
        change height (Additive.ofMul (mu d)) ≤ -(d i : ℤ) at hlt
        omega
      have ha := hweight (mu d) (vfun d) (hvs d)
      have hb := hws d
      rw [hbot, Submodule.mem_bot] at ha hb
      rw [ha, hb]
  let A := CommAlgCat.of k (MvPolynomial (Fin l.length) k)
  have hp : extendMap A f (orbitPolynomials x S v) = orbitPolynomials x ρ w := by
    funext j
    ext d
    rw [extendMap_coeff]
    exact congrFun (hcoeff d) j
  intro R a
  have hnat := extendMap_natural (CommAlgCat.ofHom (aeval a) : A ⟶ R) f (orbitPolynomials x S v)
  rw [hp] at hnat
  change extendMap R f (fun i ↦ aeval a (orbitPolynomials x S v i)) =
    (fun j ↦ aeval a (orbitPolynomials x ρ w j)) at hnat
  rwa [orbitPolynomials_eval, orbitPolynomials_eval] at hnat

end LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial WithConv
open scoped AlgebraicGeometry CategoryTheory.MonObj BigOperators Matrix TensorProduct
namespace LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootWeightAction (Representation act actLinear extendVector weightSpace mem_weightSpace)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.RootGroups (HasScalarAction)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.SteinbergDistributions (RootCoordinates orderedPoint)
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection)
open Specs.SimpleClassification (SocleModel)
open Specs.GeometricReductivity (IsTrivialQuotient)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private exponent characterValueHom characterValueHom_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SteinbergDistributions
open private splitPoint pointMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open private act_mul act_smul act_extend_natural characterValue_natural characterValue_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open private kBorel_smooth_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private coordinateReduced from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private pointCoordinates map_universalPoint algHom_points_ext split_weight_sum
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RestrictedSimplicity
open private evaluationLinear evaluationLinear_act evaluationLinear_extend evaluationLinear_subgroup pointIso
  TranslatedEvaluation IsLeftTranslation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle
open private realizes_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
open private evaluationAtOne borel_character_value extendFunctional extendFunctional_apply extendFunctional_contract
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CostandardExtensions

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {k I J : Type u} [Field k] [IsAlgClosed k]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {G : AffineAlgebraicGroup k}
local notation "K₀" => CommAlgCat.of k k

set_option maxHeartbeats 500000 in
private theorem linearMap_eq_on_orbit {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T}
    {l : List (Root T)} (x : RootCoordinates U l) (S : Representation G.val I) (v : I → k)
    {q : ℕ} (B : Module.Basis (Fin l.length → Fin q) k (I → k))
    (hB : ∀ d i, B d i = (orbitPolynomials x S v i).coeff (exponent d))
    {V : Type u} [AddCommGroup V] [Module k V] (f g : (I → k) →ₗ[k] V)
    (h : ∀ a : Fin l.length → k, f (act S K₀ (orderedPoint x K₀ a) v) =
      g (act S K₀ (orderedPoint x K₀ a) v)) : f = g := by
  apply B.ext
  intro d
  by_contra hn
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k (sub_ne_zero.mpr hn)
  let u := ℓ.comp (f - g)
  have hu (a : Fin l.length → k) : u (act S K₀ (orderedPoint x K₀ a) v) = 0 := by
    simp only [u, LinearMap.comp_apply, LinearMap.sub_apply, h, sub_self, map_zero]
  let A := CommAlgCat.of k (MvPolynomial (Fin l.length) k)
  let t : (I → k) →ₗ[k] (ULift.{u} Unit → k) := LinearMap.pi (fun _ ↦ u)
  let j : ULift.{u} Unit := ⟨()⟩
  let pol : MvPolynomial (Fin l.length) k := extendMap A t (orbitPolynomials x S v) j
  have hp : pol = 0 := by
    apply MvPolynomial.funext
    intro a
    have he := extendMap_natural (CommAlgCat.ofHom (aeval a) : A ⟶ K₀) t (orbitPolynomials x S v)
    change extendMap K₀ t (fun i ↦ aeval a (orbitPolynomials x S v i)) =
      (fun j ↦ aeval a (extendMap A t (orbitPolynomials x S v) j)) at he
    rw [orbitPolynomials_eval x S v K₀ a] at he
    change extendMap K₀ t (extendVector K₀ (act S K₀ (orderedPoint x K₀ a) v)) = _ at he
    rw [extendMap_ground] at he
    rw [map_zero (MvPolynomial.eval a)]
    exact (congrFun he j).symm.trans (hu a)
  have hvd : (fun i ↦ (orbitPolynomials x S v i).coeff (exponent d)) = B d :=
    (funext (hB d)).symm
  have he := extendMap_coeff t (orbitPolynomials x S v) (exponent d) j
  rw [hvd] at he
  change pol.coeff (exponent d) = u (B d) at he
  rw [hp] at he
  exact hℓ he.symm


private theorem induced_evaluation_covariance
    {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    {χ : Character P.torus.group} (S : SocleModel P U χ)
    (b : GroupPoints P.negative.group K₀) (v : S.I → k) :
    evaluationAtOne S (act S.inducedAction K₀ (b ≫ P.negative.inclusion.hom.hom) v) =
      characterValue χ K₀ (b ≫ S.projection.projection.hom.hom) * evaluationAtOne S v := by
  have hρ := realizes_unique S.groupIso S.inducedBasis S.inducedCoaction
    S.inducedAction S.inducedAction_spec
  let h := LinearAlgebraicGroups.FlagLineBundle.covariantCoaction S.restriction S.coordinate
  have htrans : IsLeftTranslation S.inducedCoaction := by
    intro R g a w
    have h₁ := LinearMap.congr_fun S.leftTranslation w
    have h₂ := LinearMap.congr_fun h.choose_spec.1 w
    simp only [LinearMap.comp_apply] at h₁ h₂
    rw [h₁, ← h₂]
    exact h.choose_spec.2 R g a w
  have hact : TranslatedEvaluation S.groupIso S.inducedBasis S.inducedAction := by
    rw [hρ]
    exact evaluationLinear_act S.inducedBasis S.inducedCoaction (pointIso S.groupIso) htrans
  let a := (pointIso S.borelIso).inv.app K₀ b
  have hb : (pointIso S.borelIso).hom.app K₀ a = b :=
    ((pointIso S.borelIso).app K₀).inv_hom_id_apply b
  have he := evaluationLinear_subgroup S.groupIso S.borelIso S.restriction_spec S.inducedBasis
    S.inducedAction hact K₀ b v
  have hEval (z : S.I → k) :
      evaluationLinear S.inducedBasis K₀ z = evaluationAtOne S z :=
    evaluationLinear_extend S.inducedBasis K₀ z
  change evaluationLinear S.inducedBasis K₀
      (act S.inducedAction K₀ (b ≫ P.negative.inclusion.hom.hom) v) =
      a.ofConv S.coordinate * evaluationLinear S.inducedBasis K₀ v at he
  rw [hEval, hEval] at he
  have hc := borel_character_value S K₀ a
  rw [hb] at hc
  rw [hc]
  exact he

private theorem quotient_lift_weight_one (P : OppositeBorelPair G)
    (ρ : Representation G.val J) (q : (J → k) →ₗ[k] k) (hq : IsTrivialQuotient ρ q) (z : k) :
    ∃ w ∈ weightSpace ρ P.torus (1 : Character P.torus.group), q w = z := by
  classical
  have hzero (mu : Character P.torus.group) (hne : mu ≠ 1) (v : J → k)
      (hv : v ∈ weightSpace ρ P.torus mu) : q v = 0 := by
    by_contra hqv
    apply hne
    apply LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters P.split
    intro R t
    have he := hq.2 R (t ≫ P.torus.inclusion.hom.hom) (extendVector R v)
    rw [mem_weightSpace.mp hv R t] at he
    simp only [Pi.smul_apply, smul_eq_mul] at he
    have hsum :
        (∑ j, algebraMap k R (q (Pi.single j 1)) * (characterValue mu R t * extendVector R v j)) =
        characterValue mu R t * ∑ j, algebraMap k R (q (Pi.single j 1)) * extendVector R v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_left_comm _ _ _
    rw [hsum] at he
    have ht : (∑ j, algebraMap k R (q (Pi.single j 1)) * extendVector R v j) =
        algebraMap k R (q v) := by
      rw [linear_map_in_basis q v, map_sum]
      simp only [extendVector, smul_eq_mul, map_mul, mul_comm]
    rw [ht] at he
    rw [characterValue_one]
    exact (IsUnit.mul_left_inj ((isUnit_iff_ne_zero.mpr hqv).map (algebraMap k R))).mp
      (he.trans (one_mul _).symm)
  obtain ⟨y, hy⟩ := hq.1 z
  obtain ⟨s, w, hs, hw⟩ := split_weight_sum ρ P.torus P.split y
  simp only [← hy, ← hs, map_sum]
  by_cases h : (1 : Character P.torus.group) ∈ s
  · refine ⟨w 1, hw 1 h, ?_⟩
    refine (Finset.sum_eq_single_of_mem 1 h (fun mu hm hn ↦ hzero mu hn (w mu) (hw mu hm))).symm
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [map_zero]
    exact (Finset.sum_eq_zero (fun mu hm ↦ hzero mu (fun e ↦ h (e ▸ hm)) (w mu) (hw mu hm))).symm

private theorem borel_covariance_of_ground
    {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    {χ : Character P.torus.group} (S : SocleModel P U χ)
    (ρ : Representation G.val J) (f : (S.I → k) →ₗ[k] (J → k))
    (h : ∀ (b : GroupPoints P.negative.group K₀) (v : S.I → k),
      f (act S.inducedAction K₀ (b ≫ P.negative.inclusion.hom.hom) v) =
        characterValue χ K₀ (b ≫ S.projection.projection.hom.hom) •
          act ρ K₀ (b ≫ P.negative.inclusion.hom.hom) (f v)) :
    ∀ (R : TestAlgebra k) (b : GroupPoints P.negative.group R) (x : S.I → R),
      extendMap R f (act S.inducedAction R (b ≫ P.negative.inclusion.hom.hom) x) =
        characterValue χ R (b ≫ S.projection.projection.hom.hom) •
          act ρ R (b ≫ P.negative.inclusion.hom.hom) (extendMap R f x) := by
  obtain ⟨hft, hred⟩ := coordinateReduced (closedSubgroupAlgebraicGroup P.negative)
    S.D S.borelIso (kBorel_smooth_connected G P.negative P.negativeBorel).1
  letI : Algebra.FiniteType k S.D := hft
  letI : _root_.IsReduced (AlgebraicClosure k ⊗[k] S.D) := hred
  letI : _root_.IsReduced S.D :=
    isReduced_of_injective (Algebra.TensorProduct.includeRight : S.D →ₐ[k] AlgebraicClosure k ⊗[k] S.D)
      (Algebra.TensorProduct.includeRight_injective (algebraMap k (AlgebraicClosure k)).injective)
  let D := CommAlgCat.of k S.D
  let u : GroupPoints P.negative.group D := S.borelIso.hom.hom.hom
  intro R b x
  let g := b ≫ P.negative.inclusion.hom.hom
  let c := characterValue χ R (b ≫ S.projection.projection.hom.hom)
  have e : (extendMap R f).comp (actLinear S.inducedAction R g) =
      c • (actLinear ρ R g).comp (extendMap R f) := by
    apply scalarExtension_ext
    intro v
    change extendMap R f (act S.inducedAction R g (extendVector R v)) =
      c • act ρ R g (extendMap R f (extendVector R v))
    rw [extendMap_ground]
    let lhs (R : TestAlgebra k) (b : GroupPoints P.negative.group R) :=
      extendMap R f (act S.inducedAction R (b ≫ P.negative.inclusion.hom.hom) (extendVector R v))
    let rhs (R : TestAlgebra k) (b : GroupPoints P.negative.group R) :=
      characterValue χ R (b ≫ S.projection.projection.hom.hom) •
        act ρ R (b ≫ P.negative.inclusion.hom.hom) (extendVector R (f v))
    change lhs R b = rhs R b
    have hl {B : TestAlgebra k} (a : S.D →ₐ[k] B) :
        lhs B (pointCoordinates S.borelIso B a) = fun j ↦ a (lhs D u j) := by
      unfold lhs
      rw [← map_universalPoint]
      change extendMap B f (act S.inducedAction B
        (mapPoints (CommAlgCat.ofHom a) (u ≫ P.negative.inclusion.hom.hom))
        (extendVector B v)) = _
      rw [act_extend_natural, extendMap_natural]
      rfl
    have hr {B : TestAlgebra k} (a : S.D →ₐ[k] B) :
        rhs B (pointCoordinates S.borelIso B a) = fun j ↦ a (rhs D u j) := by
      unfold rhs
      rw [← map_universalPoint]
      change characterValue χ B
          (mapPoints (CommAlgCat.ofHom a) (u ≫ S.projection.projection.hom.hom)) •
        act ρ B (mapPoints (CommAlgCat.ofHom a) (u ≫ P.negative.inclusion.hom.hom))
          (extendVector B (f v)) = _
      rw [characterValue_natural, act_extend_natural]
      funext j
      exact (map_mul a _ _).symm
    have hu : lhs D u = rhs D u := by
      funext j
      apply algHom_points_ext
      intro a
      rw [← congrFun (hl (B := K₀) a) j, ← congrFun (hr (B := K₀) a) j]
      let g₀ : GroupPoints G.val K₀ :=
        pointCoordinates S.borelIso K₀ a ≫ P.negative.inclusion.hom.hom
      change extendMap K₀ f (extendVector K₀ (act S.inducedAction K₀ g₀ v)) j = _
      rw [extendMap_ground]
      exact congrFun (h (pointCoordinates S.borelIso K₀ a) v) j
    obtain ⟨a, rfl⟩ := (pointCoordinates S.borelIso R).surjective b
    rw [hl, hr, hu]
  exact LinearMap.congr_fun e x

open private characterValue_eq_unit characterUnitOnPoints
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private kernel_point pointMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction

/-- Intertwining an orbit that spans the domain verifies equivariance for the
radical. The weight comparison supplies the torus action and the quotient
identities follow by evaluating the two lifts on the same orbit. -/
private theorem borelMap_of_orbit
    {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    {χ : Character P.torus.group} (S : SocleModel P U χ)
    {family : RootSubgroupFamily P.torus} {l : List (Root P.torus)}
    (x : RootCoordinates family l)
    (hx : ∀ i, HasScalarAction P.torus (l.get i).val
      ((x.groupIso i).hom ≫ (family (l.get i)).val.inclusion))
    (u : (Fin l.length → k) → GroupPoints S.projection.radical.group K₀)
    (hu : Function.Surjective u)
    (hpoint : ∀ a, pointMap (S.projection.radical.inclusion ≫ P.negative.inclusion) K₀ (u a) =
      orderedPoint x K₀ a)
    (ρ : Representation G.val J) (q : (J → k) →ₗ[k] k) (hq : IsTrivialQuotient ρ q)
    {v : S.I → k} (hv : v ∈ weightSpace S.inducedAction P.torus χ)
    (w : J → k) (hqw : q w = evaluationAtOne S v)
    {n : ℕ} (B : Module.Basis (Fin l.length → Fin n) k (S.I → k))
    (hB : ∀ d i, B d i = (orbitPolynomials x S.inducedAction v i).coeff (exponent d))
    (f : (S.I → k) →ₗ[k] (J → k))
    (hweight : ∀ mu, ∀ z ∈ weightSpace S.inducedAction P.torus (χ * mu),
      f z ∈ weightSpace ρ P.torus mu)
    (hOrbit : ∀ a : Fin l.length → k, f (act S.inducedAction K₀ (orderedPoint x K₀ a) v) =
      act ρ K₀ (orderedPoint x K₀ a) w) :
    q.comp f = evaluationAtOne S ∧
      ∀ (R : TestAlgebra k) (b : GroupPoints P.negative.group R) (z : S.I → R),
        extendMap R f (act S.inducedAction R (b ≫ P.negative.inclusion.hom.hom) z) =
          characterValue χ R (b ≫ S.projection.projection.hom.hom) •
            act ρ R (b ≫ P.negative.inclusion.hom.hom) (extendMap R f z) := by
  let p := S.projection
  let ug := pointMap (p.radical.inclusion ≫ P.negative.inclusion) K₀
  have hTor (t : GroupPoints P.torus.group K₀) (z : S.I → k) :
      f (act S.inducedAction K₀ (t ≫ P.torus.inclusion.hom.hom) z) =
        characterValue χ K₀ t • act ρ K₀ (t ≫ P.torus.inclusion.hom.hom) (f z) := by
    let g : GroupPoints G.val K₀ := t ≫ P.torus.inclusion.hom.hom
    let c := characterValue χ K₀ t
    have h : f.comp (actLinear S.inducedAction K₀ g) =
        c • (actLinear ρ K₀ g).comp f := by
      apply B.ext
      intro d
      let mu : Character P.torus.group := ∏ i : Fin l.length, (l.get i).val ^ exponent d i
      have hs : B d ∈ weightSpace S.inducedAction P.torus (χ * mu) := by
        rw [show B d = _ from funext (hB d)]
        exact orbitCoefficient_weight x S.inducedAction hx hv (exponent d)
      have ht := hweight mu _ hs
      change f (act S.inducedAction K₀ g (B d)) = c • act ρ K₀ g (f (B d))
      have hst := mem_weightSpace.mp hs K₀ t
      have htt := mem_weightSpace.mp ht K₀ t
      change act S.inducedAction K₀ g (B d) = _ at hst
      change act ρ K₀ g (f (B d)) = _ at htt
      rw [hst, htt, map_smul, smul_smul]
      simp only [c, ← characterValueHom_apply, map_mul]
      rfl
    exact LinearMap.congr_fun h z
  have hRad (b : GroupPoints p.radical.group K₀) (z : S.I → k) :
      f (act S.inducedAction K₀ (ug b) z) = act ρ K₀ (ug b) (f z) := by
    have h : f.comp (actLinear S.inducedAction K₀ (ug b)) =
        (actLinear ρ K₀ (ug b)).comp f := by
      apply linearMap_eq_on_orbit x S.inducedAction v B hB
      intro a
      change f (act S.inducedAction K₀ (ug b) (act S.inducedAction K₀ (orderedPoint x K₀ a) v)) =
        act ρ K₀ (ug b) (f (act S.inducedAction K₀ (orderedPoint x K₀ a) v))
      obtain ⟨a', ha'⟩ := hu (b * u a)
      let y : GroupPoints G.val K₀ := orderedPoint x K₀ a
      let y' : GroupPoints G.val K₀ := orderedPoint x K₀ a'
      have hex : ug b * y = y' := by
        dsimp only [y, y']
        rw [← hpoint a, ← hpoint a']
        change ug b * ug (u a) = ug (u a')
        rw [ha', map_mul]
      rw [hOrbit, ← act_mul, ← act_mul]
      change f (act S.inducedAction K₀ (ug b * y) v) = act ρ K₀ (ug b * y) w
      rw [hex]
      exact hOrbit a'
    exact LinearMap.congr_fun h z
  constructor
  · apply linearMap_eq_on_orbit x S.inducedAction v B hB
    intro a
    change q (f (act S.inducedAction K₀ (orderedPoint x K₀ a) v)) = _
    rw [hOrbit]
    have hqact := hq.2 K₀ (orderedPoint x K₀ a) w
    have hqapply (z : J → k) : q z = ∑ j, q (Pi.single j 1) * z j := by
      conv_lhs => rw [linear_map_in_basis q z]
      simp [mul_comm, smul_eq_mul]
    change ∑ j, q (Pi.single j 1) * act ρ K₀ (orderedPoint x K₀ a) w j =
      ∑ j, q (Pi.single j 1) * w j at hqact
    rw [← hqapply, ← hqapply] at hqact
    rw [hqact, hqw]
    rw [← hpoint a]
    have he := induced_evaluation_covariance S (pointMap p.radical.inclusion K₀ (u a)) v
    rw [show (pointMap p.radical.inclusion K₀ (u a) ≫ p.projection.hom.hom) = 1 from
      kernel_point p.radical p.projection p.isKernel K₀ (u a)] at he
    have hOne : characterValue χ K₀ 1 = 1 := by
      rw [characterValue_eq_unit]
      exact congrArg Units.val (map_one (characterUnitOnPoints χ K₀))
    rw [hOne, one_mul] at he
    exact he.symm
  · apply borel_covariance_of_ground S ρ f
    intro b z
    obtain ⟨c, hc⟩ := splitPoint p.radical p.inclusion p.projection p.section_projection
      p.isKernel K₀ b
    have hm := congrArg (pointMap P.negative.inclusion K₀) hc
    rw [map_mul, ← pointMap_comp, ← pointMap_comp, p.inclusion_comp] at hm
    let tG : GroupPoints G.val K₀ :=
      (b ≫ p.projection.hom.hom) ≫ P.torus.inclusion.hom.hom
    change b ≫ P.negative.inclusion.hom.hom = tG * ug c at hm
    rw [hm, act_mul, hTor, hRad, act_mul]

end LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open scoped AlgebraicGeometry CategoryTheory.MonObj BigOperators Matrix
namespace LinearAlgebraicGroups.Arithmetic.GeometricReductivity

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootWeightAction (Representation act actLinear extendVector weightSpace mem_weightSpace)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.SimpleClassification (SocleModel)
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.OrderedRootProducts (rootProduct)
open Specs.SteinbergDistributions (orderedPoint)
open Specs.GeometricReductivity (InvariantLifting IsEndomorphismLift IsTrivialQuotient)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.InducedNonvanishing (Dominant)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (pairing)
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private isSplitTorus_of_isAlgClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
open private oppositePositiveSystem from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private socleInclusion socleInclusion_injective socleInclusion_equivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylModules
open private exponent rootTupleEquiv orderedPoint_eval
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SteinbergDistributions
open private scalar_action_of_normalized_tangent from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private radicalProductFor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
open private pointMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open private evaluationAtOne from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CostandardExtensions

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

private theorem oppositePairExists {k : Type u} [Field k] [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hG : Specs.GeometricRadicals.IsSemisimple G) :
    Nonempty (OppositeBorelPair G) := by
  letI := hG.2.1
  obtain ⟨T, hT, hmax⟩ := LinearAlgebraicGroups.MaximalToriExist.geometricallyMaximalTorusExists
    G hG.1 (GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom)
  have hs := isSplitTorus_of_isAlgClosed T hT
  have hr := reductive_of_semisimple G hG
  obtain ⟨comm, D, _, hB, hW, _, _⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity G hr T hs hmax
  obtain ⟨S, hS⟩ := hW.1
  obtain ⟨B, hpos, hTB, hb⟩ := hB.2.1 S hS
  obtain ⟨Bn, hneg, hTBn, hn⟩ := hB.2.1 Sᶜ (oppositePositiveSystem hS)
  exact ⟨⟨T, B, Bn, hr, hs, hmax, hpos, hneg, hTB, hTBn, hn.trans (congrArg Set.compl hb.symm)⟩⟩

private theorem negativeRootHeight {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X] (D : Datum P.torus) :
    ∃ height : Additive (Character P.torus.group) →ₗ[ℤ] ℤ,
      ∀ α ∈ subgroupRoots P.torus P.negative, height (Additive.ofMul α.val) ≤ -1 := by
  obtain ⟨c, _, hc, _, hpos⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
      G P.reductive P.torus P.split P.maximal).1 P.positive P.positiveBorel P.inPositive
  refine ⟨Specs.SimpleRoots.evaluate D c, fun α hα ↦ ?_⟩
  change D.rootDatum.toLinearMap (Additive.ofMul α.val) (Additive.ofMul c) ≤ _
  rw [D.pairing_eq]
  rw [P.opposite, Set.mem_compl_iff, hpos] at hα
  change ¬ 0 < pairing P.torus.group α.val c at hα
  have hne := hc α
  omega

/-- For a large Steinberg weight, the radical orbit determines an
equivariant lift of evaluation onto the trivial quotient. -/
private theorem endomorphismLift_over_simplyConnected
    {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k) (hG : Specs.GeometricRadicals.IsSemisimple G)
    (hsc : GeometricallySimplyConnected G) {J : Type u} [Fintype J] [DecidableEq J]
    (ρ : Representation G.val J) (q : (J → k) →ₗ[k] k) (hq : IsTrivialQuotient ρ q) :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (_ : Nonempty I)
      (S : Representation G.val I) (F : Matrix I I (J → k)), IsEndomorphismLift ρ S q F := by
  classical
  obtain ⟨P⟩ := oppositePairExists G hG
  obtain ⟨comm, D, _, _, _, _, dec⟩ := LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity
    G P.reductive P.torus P.split P.maximal
  letI := comm
  obtain ⟨height, hheight⟩ := negativeRootHeight P D
  obtain ⟨bound, hbound⟩ := weights_bounded_below P ρ height
  let r := bound + 1
  let n := p ^ r
  have hr : 1 ≤ r := Nat.succ_pos _
  have hn : bound < n := (Nat.lt_succ_self _).trans
    (Nat.lt_pow_self (n := r) (Fact.out : p.Prime).one_lt)
  obtain ⟨U, hU⟩ := LinearAlgebraicGroups.GeometricRadicals.unipotentRadicalExists
    (closedSubgroupAlgebraicGroup P.positive)
  obtain ⟨ω, hω⟩ := LinearAlgebraicGroups.Representation.SteinbergDimension.halfSumExists hG hsc P
  let χ := Additive.toMul ((n - 1) • Additive.ofMul ω)
  have hdom : Dominant P χ := by
    intro α c hc
    change 0 ≤ pairing P.torus.group (Additive.toMul ((n - 1) • Additive.ofMul ω)) c
    rw [LinearAlgebraicGroups.Representation.SteinbergDimension.steinbergWeight_pairing
      P ω hω n α c hc]
    exact Int.natCast_nonneg _
  obtain ⟨S, _⟩ := (LinearAlgebraicGroups.Representation.SimpleClassification.classification G P U hU).2.2
    χ hdom
  obtain ⟨N, hN, ⟨PN⟩, ⟨family⟩, ⟨l, hl⟩, hcoord⟩ :=
    LinearAlgebraicGroups.Representation.SteinbergDistributions.orderedNegativeDistributions
      (k := k) p r hr G P.reductive P.torus P.positive P.negative P.split P.maximal
      P.positiveBorel P.negativeBorel P.inPositive P.inNegative P.opposite
  obtain ⟨lpos, hlpos, hlen, x, hx⟩ := hcoord PN family l hl
  obtain ⟨e, he, _⟩ := hx x
  obtain ⟨B, hB⟩ := truncatedSteinbergOrbit p r hr hG hsc P ω hω hU S N hN PN
    lpos hlen hlpos x e he
  let W := LinearEquiv.ofBijective (socleInclusion S)
    ⟨socleInclusion_injective S, steinbergSocle_surjective p r hr hG hsc P U hU ω hω S⟩
  let B' := B.map W
  let v := (S.highestVector : S.I → k)
  have hv : v ∈ weightSpace S.inducedAction P.torus χ := S.highest_primitive.2.2
  let A := CommAlgCat.of k (MvPolynomial (Fin l.length) k)
  have horb : extendMap A (socleInclusion S)
      (orbitPolynomials x S.socleAction (S.socleBasis.equivFun S.highestVector)) =
      orbitPolynomials x S.inducedAction v := by
    unfold orbitPolynomials
    change extendMap A (socleInclusion S)
      (act S.socleAction A (orderedPoint x A X)
        (extendVector A (S.socleBasis.equivFun S.highestVector))) = _
    rw [extendMap_equivariant _ (socleInclusion_equivariant S), extendMap_ground]
    have heq : socleInclusion S (S.socleBasis.equivFun S.highestVector) = v := by
      simp only [socleInclusion, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, v]
      rfl
    rw [heq]
  have hB' (d : Fin l.length → Fin n) (i : S.I) :
      B' d i = (orbitPolynomials x S.inducedAction v i).coeff (exponent d) := by
    rw [← horb, extendMap_coeff]
    change socleInclusion S (B d) i = _
    rw [show B d = _ from funext (hB d)]
  obtain ⟨w, hw, hqw⟩ := quotient_lift_weight_one P ρ q hq (evaluationAtOne S v)
  have hscalar := fun i : Fin l.length ↦ scalar_action_of_normalized_tangent P.torus
    (family (l.get i)).val P.split (l.get i).val (family (l.get i)).prop (x.line i) (x.groupIso i)
  obtain ⟨f, hfweight, hOrb⟩ := map_of_truncated_orbits x hscalar S.inducedAction ρ χ hv hw
    bound n hn height (fun i ↦ hheight _ ((hl.2 _).mp (List.get_mem l i))) hbound B' hB'
  let K := CommAlgCat.of k k
  have hOrb' (a : Fin l.length → k) : f (act S.inducedAction K (orderedPoint x K a) v) =
      act ρ K (orderedPoint x K a) w := by
    have h := hOrb K a
    change extendMap K f (extendVector K (act S.inducedAction K (orderedPoint x K a) v)) = _ at h
    rw [extendMap_ground] at h
    exact h
  obtain ⟨V, _, _, hV, _, _, _, _, _, chart⟩ := dec P.negative P.negativeBorel P.inNegative
  obtain ⟨E, hE⟩ := radicalProductFor family l S.projection.isRadical hV (chart family l hl)
  let u (a : Fin l.length → k) : GroupPoints S.projection.radical.group K :=
    rootTupleEquiv family K l x a ≫ E.hom
  have hu : Function.Surjective u := by
    intro z
    refine ⟨(rootTupleEquiv family K l x).symm (z ≫ E.inv), ?_⟩
    simp [u]
  have hpoint (a : Fin l.length → k) :
      pointMap (S.projection.radical.inclusion ≫ P.negative.inclusion) K (u a) =
        orderedPoint x K a := by
    change (rootTupleEquiv family K l x a ≫ E.hom) ≫
      S.projection.radical.inclusion.hom.hom ≫ P.negative.inclusion.hom.hom = _
    rw [Category.assoc, hE]
    exact orderedPoint_eval family K l x a
  obtain ⟨hfq, hfb⟩ := borelMap_of_orbit S x hscalar u hu hpoint ρ q hq hv w hqw B' hB' f
    hfweight hOrb'
  have hnonempty : Nonempty S.I := by
    by_contra h
    letI : IsEmpty S.I := not_nonempty_iff.mp h
    exact S.highest_primitive.1 (Subsingleton.elim _ _)
  obtain ⟨S', F, hF⟩ := endomorphismLift_of_borelMap S ρ q hq f hfq hfb
  exact ⟨S.I, inferInstance, inferInstance, hnonempty, S', F, hF⟩

/-- Geometric reductivity in the invariant-lifting form for a connected
semisimple group over a field of positive characteristic. -/
theorem invariantLifting : InvariantLifting.{u} :=
  invariantLifting_of_simplyConnected
    LinearAlgebraicGroups.Reductive.RadicalBaseChange.semisimpleFieldExtension
    LinearAlgebraicGroups.MaximalToriExist.geometricallyMaximalTorusExists
    (fun T hT ↦ isSplitTorus_of_isAlgClosed T hT)
    reductive_of_semisimple
    LinearAlgebraicGroups.RootData.AbstractPairing.abstractPairing
    LinearAlgebraicGroups.Classification.SimplyConnectedLattice.splitCover
    endomorphismLift_over_simplyConnected

end LinearAlgebraicGroups.Arithmetic.GeometricReductivity
