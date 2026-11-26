import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLieWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped Matrix TensorProduct LaurentPolynomial

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup Lie IdentityLieStructure)
open Specs.AdjointRepresentation
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open RationalRepresentations

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme k}

section Basis

variable {V I J : Type u} [AddCommGroup V] [Module k V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] (b : Module.Basis I k V) (d : Module.Basis J k V)

/-- Change of coordinates from d to b after scalar extension. -/
private def basisChange (R : TestAlgebra k) : (J → R) ≃ₗ[R] (I → R) :=
  ((d.baseChange R).equivFun).symm.trans (b.baseChange R).equivFun

omit [DecidableEq I] [DecidableEq J] in
private theorem basisChange_apply (R : TestAlgebra k) (v : J → R) (i : I) :
    basisChange b d R v i = ∑ j, v j * algebraMap k R (b.equivFun (d j) i) := by
  have h := (d.baseChange R).sum_equivFun ((d.baseChange R).equivFun.symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  change (b.baseChange R).equivFun ((d.baseChange R).equivFun.symm v) i = _
  rw [← h, map_sum, Finset.sum_apply]
  congr 1
  ext j
  rw [map_smul]
  change v j * (b.baseChange R).repr (d.baseChange R j) i = _
  rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

omit [DecidableEq I] [DecidableEq J] in
private theorem basisChange_base (p : V) :
    basisChange b d (CommAlgCat.of k k) (d.equivFun p) = b.equivFun p := by
  ext i
  rw [basisChange_apply]
  have h := congrArg (fun x => b.equivFun x i) (d.sum_equivFun p)
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Algebra.algebraMap_self_apply] using h

end Basis

private def rebaseCoordinates {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [AddCommGroup (Lie k G)] [Module k (Lie k G)]
    {b : Module.Basis I k (Lie k G)} (T : TangentCoordinates G I b)
    (d : Module.Basis J k (Lie k G)) : TangentCoordinates G J d where
  equiv R := (basisChange b d R).toAddEquiv.trans (T.equiv R)
  smul R r v := by
    change (T.equiv R (basisChange b d R (r • v))).toMul.val = _
    rw [map_smul]
    exact T.smul R r _
  naturality {R S} a v := by
    change (T.equiv S (basisChange b d S (fun j => a.hom (v j)))).toMul.val =
      mapPoints (dualMap a) (T.equiv R (basisChange b d R v)).toMul.val
    have h : basisChange b d S (fun j => a.hom (v j)) =
        fun i => a.hom (basisChange b d R v i) := by
      funext i
      simp only [basisChange_apply, map_sum, map_mul, AlgHom.commutes]
    rw [h]
    exact T.naturality a _
  at_base p :=
    (congrArg (fun v => (T.equiv (CommAlgCat.of k k) v).toMul.val)
      (basisChange_base b d p)).trans (T.at_base p)

section Weights

variable {V I : Type u} [AddCommGroup V] [Module k V] [Fintype I] [DecidableEq I]

private theorem matrix_on_weight
    (b : Module.Basis I k V) (L : GroupScheme k)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k I)
    (f : (Specs.DiagonalizableGroups.diagonalGroup k IntegerCharacters).val ⟶ L)
    (ρ : RightComodule k (groupAlgebra k IntegerCharacters) V)
    (hρ : coefficients (groupAlgebra k IntegerCharacters) b ρ =
      universalMatrix (groupAlgebra k IntegerCharacters)
        ⟨_, (Specs.DiagonalizableGroups.diagonalGroup k IntegerCharacters).property.1⟩ L
        (hopfSpecPointIso _) l f)
    (R : TestAlgebra k) (t : Rˣ) (x : V) (m : IntegerCharacters)
    (hx : x ∈ WeightDecomposition.weightSpace ρ m) :
    let M := (l.hom.app R).hom (((groupPointsFunctor k).map f).app R (unitPoint R t))
    M.val *ᵥ (fun i => algebraMap k R (b.equivFun x i)) =
      (↑(t ^ Multiplicative.toAdd m.down) : R) • (fun i => algebraMap k R (b.equivFun x i)) := by
  let A := groupAlgebra k IntegerCharacters
  let g : A →ₐ[k] R := unitCoordinates R t
  let M := (l.hom.app R).hom (((groupPointsFunctor k).map f).app R (unitPoint R t))
  let coord : R ⊗[k] V ≃ₗ[R] (I → R) := (b.baseChange R).equivFun
  have hcoord (r : R) (y : V) (i : I) :
      coord (r ⊗ₜ[k] y) i = algebraMap k R (b.equivFun y i) * r := by
    change (b.baseChange R).repr (r ⊗ₜ[k] y) i = _
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
    rfl
  let inc : V →ₗ[k] R ⊗[k] V := (TensorProduct.mk k R V) 1
  have hmat :
      (coord.toLinearMap.restrictScalars k).comp
        ((TensorProduct.comm k V R).toLinearMap.comp (evaluate A ρ g)) =
      ((Matrix.mulVecLin M.val).restrictScalars k).comp
        ((coord.toLinearMap.restrictScalars k).comp inc) := by
    apply b.ext
    intro j
    have h := evaluationComparison A b
      ⟨_, (Specs.DiagonalizableGroups.diagonalGroup k IntegerCharacters).property.1⟩ L
        (hopfSpecPointIso A) l f ρ hρ R g j
    change evaluate A ρ g (b j) = ∑ i, b i ⊗ₜ[k] M.val i j at h
    change coord ((TensorProduct.comm k V R) (evaluate A ρ g (b j))) =
      M.val *ᵥ coord (1 ⊗ₜ[k] b j)
    rw [h, map_sum, map_sum]
    have hb (i : I) : coord (1 ⊗ₜ[k] b i) = Pi.single i 1 := by
      rw [← Module.Basis.baseChange_apply]
      funext h
      simpa only [Pi.single_apply, eq_comm] using (b.baseChange R).equivFun_self i h
    rw [hb]
    funext i
    simp only [TensorProduct.comm_tmul, Finset.sum_apply, hcoord, Matrix.mulVec_single_one,
      Matrix.col_apply, Module.Basis.equivFun_self]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  have he := congrArg (fun F : V →ₗ[k] (I → R) => F x) hmat
  change coord ((TensorProduct.comm k V R) (evaluate A ρ g x)) = M.val *ᵥ coord (1 ⊗ₜ[k] x) at he
  have hx' : ρ.coaction x = x ⊗ₜ[k] MonoidAlgebra.of k IntegerCharacters m :=
    WeightDecomposition.mem_weightSpace.mp hx
  have hg : g (MonoidAlgebra.of k IntegerCharacters m) =
      (↑(t ^ Multiplicative.toAdd m.down) : R) := by
    change MonoidAlgebra.lift k R IntegerCharacters _ (MonoidAlgebra.single m 1) = _
    rw [MonoidAlgebra.lift_single, one_smul]
    rfl
  change coord ((TensorProduct.comm k V R) ((g.toLinearMap.lTensor V) (ρ.coaction x))) = _ at he
  rw [hx', LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.comm_tmul, hg] at he
  have hbase : coord (1 ⊗ₜ[k] x) = fun i => algebraMap k R (b.equivFun x i) := by
    funext i
    rw [hcoord, mul_one]
  rw [hbase] at he
  funext i
  exact (congrFun he.symm i).trans ((hcoord _ _ _).trans (mul_comm _ _))

end Weights

theorem existsAdjointWeightBasis : Specs.CocharacterDynamics.ExistsAdjointWeightBasis.{u} := by
  classical
  intro k _ G cochar s
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, b, T, L, l, Ad, hAd, _, _⟩ := adjointRepresentation k G s
  let A := groupAlgebra k IntegerCharacters
  let M := Specs.DiagonalizableGroups.diagonalGroup k IntegerCharacters
  let F : AffineGroupCategory k := ⟨M.val, M.property.1⟩
  let f : F.val ⟶ L.val := cochar ≫ Ad
  obtain ⟨E, hE⟩ := representationCoactionComparison A b F L.val (hopfSpecPointIso A) l
  let ρ := E f
  have := b.finiteDimensional_of_finite
  obtain ⟨J, hJ, d, w, hw⟩ := DiagonalizableFixedLocus.existsWeightBasis ρ
  let := Fintype.ofFinite J
  let e : J ≃ ULift.{u} (Fin (Fintype.card J)) :=
    (Fintype.equivFin J).trans Equiv.ulift.symm
  let d' := d.reindex e
  let weight j := Multiplicative.toAdd (w (e.symm j)).down
  let T' := rebaseCoordinates T d'
  refine ⟨⟨Fintype.card J, d', T', weight, ?_⟩⟩
  intro R t v
  change (T.equiv R (basisChange b d' R (fun j => (↑(t ^ weight j) : R) * v j))).toMul.val =
    conjugate (cocharacterPoint cochar R t) (T.equiv R (basisChange b d' R v))
  rw [← hAd R (cocharacterPoint cochar R t) (basisChange b d' R v)]
  apply congrArg (fun w => (T.equiv R w).toMul.val)
  let Q := (l.hom.app R).hom (((groupPointsFunctor k).map f).app R (unitPoint R t))
  have hQ : Q = (l.hom.app R).hom
      (((groupPointsFunctor k).map Ad).app R (cocharacterPoint cochar R t)) := by
    dsimp only [Q, f, cocharacterPoint]
    rw [Functor.map_comp, NatTrans.comp_app]
    rfl
  rw [← hQ]
  let col (j : ULift.{u} (Fin (Fintype.card J))) (i : ULift.{u} (Fin n)) : R :=
    algebraMap k R (b.equivFun (d' j) i)
  have cols (z : ULift.{u} (Fin (Fintype.card J)) → R) :
      basisChange b d' R z = ∑ j, z j • col j := by
    ext i
    simp [basisChange_apply, col, Finset.sum_apply]
  have eigen (j : ULift.{u} (Fin (Fintype.card J))) :
      Q.val *ᵥ col j = (↑(t ^ weight j) : R) • col j := by
    have hx : d' j ∈ WeightDecomposition.weightSpace ρ (w (e.symm j)) := by
      simpa only [d', Module.Basis.reindex_apply] using hw (e.symm j)
    exact matrix_on_weight b L.val l f ρ (hE f) R t _ _ hx
  rw [cols, cols]
  change (∑ j, ((↑(t ^ weight j) : R) * v j) • col j) =
    Matrix.mulVecLin Q.val (∑ j, v j • col j)
  simp only [map_sum, map_smul]
  congr 1
  funext j
  change _ = v j • (Q.val *ᵥ col j)
  rw [eigen, smul_smul, mul_comm (v j)]

section DualFamilies

open private polynomialConstants evalLaurent evalLaurent_constants evalLaurent_parameter
  orbit_eval centralizes_onAlgebras from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private abbrev dual (R : TestAlgebra k) : TestAlgebra k :=
  CommAlgCat.of k (DualNumber R)

private theorem dualMap_inl {R S : TestAlgebra k} (a : R ⟶ S) (r : R) :
    (dualMap a).hom (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (a.hom r) :=
  TrivSqZeroExt.ext rfl (map_zero a.hom)

private theorem dualMap_eps {R S : TestAlgebra k} (a : R ⟶ S) :
    (dualMap a).hom (DualNumber.eps : DualNumber R) = DualNumber.eps :=
  TrivSqZeroExt.ext (map_zero a.hom) (map_one a.hom)

private theorem dualSource_ext {R S : TestAlgebra k} {a b : dual R ⟶ S}
    (h : ∀ r, a.hom (TrivSqZeroExt.inl r) = b.hom (TrivSqZeroExt.inl r))
    (he : a.hom DualNumber.eps = b.hom DualNumber.eps) : a = b := by
  apply CommAlgCat.hom_ext
  apply AlgHom.toRingHom_injective
  exact DualNumber.ringHom_ext (RingHom.ext h) he

/-- Move dual-number coefficients outside the polynomial variable. -/
private def dualPolynomial (R : TestAlgebra k) :
    polynomialAlgebra (dual R) ⟶ dual (polynomialAlgebra R) :=
  CommAlgCat.ofHom <| Polynomial.aevalTower (dualMap (polynomialConstants R)).hom
    (TrivSqZeroExt.inl Polynomial.X)

private def dualLaurent (R : TestAlgebra k) :
    laurentAlgebra (dual R) ⟶ dual (laurentAlgebra R) :=
  evalLaurent (dualMap (laurentConstants R))
    (Units.map (constants (laurentAlgebra R)).hom.toMonoidHom (laurentParameter R))

/-- Insert a square-zero parameter into the coefficient ring. -/
private def liftDual {R S : TestAlgebra k} (a : R ⟶ S) (e : S) (he : e * e = 0) :
    dual R ⟶ S :=
  CommAlgCat.ofHom (DualNumber.lift ⟨(a.hom, e), he, fun _ => Commute.all _ _⟩)

@[simp] private theorem liftDual_inl {R S : TestAlgebra k} (a : R ⟶ S) (e : S)
    (he : e * e = 0) (r : R) :
    (liftDual a e he).hom (TrivSqZeroExt.inl r) = a.hom r :=
  DualNumber.lift_apply_inl _ _

@[simp] private theorem liftDual_eps {R S : TestAlgebra k} (a : R ⟶ S) (e : S)
    (he : e * e = 0) :
    (liftDual a e he).hom DualNumber.eps = e :=
  DualNumber.lift_apply_eps _

private def polynomialDual (R : TestAlgebra k) :
    dual (polynomialAlgebra R) ⟶ polynomialAlgebra (dual R) :=
  liftDual (mapPolynomial (constants R)) (Polynomial.C DualNumber.eps)
    (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero])

private def laurentDual (R : TestAlgebra k) :
    dual (laurentAlgebra R) ⟶ laurentAlgebra (dual R) :=
  liftDual (mapLaurent (constants R)) (LaurentPolynomial.C DualNumber.eps)
    (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero])

private theorem dualPolynomial_restrict (R : TestAlgebra k) :
    dualPolynomial R ≫ dualMap (polynomialToLaurent R) =
      polynomialToLaurent (dual R) ≫ dualLaurent R := by
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext'
  · apply AlgHom.ext
    intro x
    change (dualMap (polynomialToLaurent R)).hom ((dualPolynomial R).hom (Polynomial.C x)) =
      (dualLaurent R).hom ((Polynomial.C x).toLaurent)
    change (dualMap (polynomialToLaurent R)).hom
      (Polynomial.aevalTower (dualMap (polynomialConstants R)).hom
        (TrivSqZeroExt.inl Polynomial.X) (Polynomial.C x)) =
      LaurentPolynomial.eval₂ (dualMap (laurentConstants R)).hom.toRingHom _
        ((Polynomial.C x).toLaurent)
    rw [Polynomial.aevalTower_C, Polynomial.toLaurent_C, LaurentPolynomial.eval₂_C]
    exact TrivSqZeroExt.ext (Polynomial.toLaurent_C x.fst) (Polynomial.toLaurent_C x.snd)
  · change (dualMap (polynomialToLaurent R)).hom
        (Polynomial.aevalTower (dualMap (polynomialConstants R)).hom
          (TrivSqZeroExt.inl Polynomial.X) Polynomial.X) =
      LaurentPolynomial.eval₂ (dualMap (laurentConstants R)).hom.toRingHom _
        Polynomial.X.toLaurent
    rw [Polynomial.aevalTower_X, dualMap_inl, Polynomial.toLaurent_X,
      LaurentPolynomial.eval₂_T, zpow_one]
    exact congrArg TrivSqZeroExt.inl Polynomial.toLaurent_X

private theorem dualPolynomial_zero (R : TestAlgebra k) :
    dualPolynomial R ≫ dualMap (polynomialEvaluate R 0) = polynomialEvaluate (dual R) 0 := by
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext'
  · apply AlgHom.ext
    intro x
    change (dualMap (polynomialEvaluate R 0)).hom
        (Polynomial.aevalTower (dualMap (polynomialConstants R)).hom
          (TrivSqZeroExt.inl Polynomial.X) (Polynomial.C x)) =
      Polynomial.aevalTower (AlgHom.id k (dual R)) 0 (Polynomial.C x)
    rw [Polynomial.aevalTower_C, Polynomial.aevalTower_C]
    exact TrivSqZeroExt.ext (Polynomial.aevalTower_C _ _ x.fst)
      (Polynomial.aevalTower_C _ _ x.snd)
  · change (dualMap (polynomialEvaluate R 0)).hom
        (Polynomial.aevalTower (dualMap (polynomialConstants R)).hom
          (TrivSqZeroExt.inl Polynomial.X) Polynomial.X) =
      Polynomial.aevalTower (AlgHom.id k (dual R)) 0 Polynomial.X
    rw [Polynomial.aevalTower_X, Polynomial.aevalTower_X, dualMap_inl]
    exact congrArg TrivSqZeroExt.inl (Polynomial.aevalTower_X _ _)

private theorem polynomialDual_restrict (R : TestAlgebra k) :
    polynomialDual R ≫ polynomialToLaurent (dual R) =
      dualMap (polynomialToLaurent R) ≫ laurentDual R := by
  apply dualSource_ext
  · intro p
    change (Polynomial.toLaurent ((polynomialDual R).hom (TrivSqZeroExt.inl p))) =
      (laurentDual R).hom ((dualMap (polynomialToLaurent R)).hom (TrivSqZeroExt.inl p))
    rw [dualMap_inl]
    change _ = (laurentDual R).hom (TrivSqZeroExt.inl p.toLaurent)
    unfold polynomialDual laurentDual
    rw [liftDual_inl, liftDual_inl]
    exact DFunLike.congr_fun
      (congrArg (fun f => f.hom) (polynomialToLaurent_naturality (constants R))) p
  · change ((polynomialDual R).hom DualNumber.eps).toLaurent =
      (laurentDual R).hom ((dualMap (polynomialToLaurent R)).hom DualNumber.eps)
    unfold polynomialDual laurentDual
    rw [dualMap_eps, liftDual_eps, liftDual_eps, Polynomial.toLaurent_C]

private theorem polynomialDual_zero (R : TestAlgebra k) :
    polynomialDual R ≫ polynomialEvaluate (dual R) 0 = dualMap (polynomialEvaluate R 0) := by
  apply dualSource_ext
  · intro p
    change (polynomialEvaluate (dual R) 0).hom ((polynomialDual R).hom (TrivSqZeroExt.inl p)) =
      (dualMap (polynomialEvaluate R 0)).hom (TrivSqZeroExt.inl p)
    rw [dualMap_inl]
    unfold polynomialDual
    rw [liftDual_inl]
    exact DFunLike.congr_fun
      (congrArg (fun f => f.hom) (polynomialEvaluate_zero_naturality (constants R))) p
  · change (polynomialEvaluate (dual R) 0).hom ((polynomialDual R).hom DualNumber.eps) =
      (dualMap (polynomialEvaluate R 0)).hom DualNumber.eps
    unfold polynomialDual
    rw [dualMap_eps, liftDual_eps]
    exact Polynomial.aevalTower_C (AlgHom.id k (dual R)) 0 DualNumber.eps

private theorem laurentDual_constants (R : TestAlgebra k) :
    dualMap (laurentConstants R) ≫ laurentDual R = laurentConstants (dual R) := by
  apply dualSource_ext
  · intro r
    change (laurentDual R).hom ((dualMap (laurentConstants R)).hom (TrivSqZeroExt.inl r)) = _
    rw [dualMap_inl]
    unfold laurentDual
    rw [liftDual_inl]
    exact DFunLike.congr_fun
      (congrArg (fun f => f.hom) (laurentConstants_naturality (constants R))) r
  · change (laurentDual R).hom ((dualMap (laurentConstants R)).hom DualNumber.eps) =
      LaurentPolynomial.C DualNumber.eps
    unfold laurentDual
    rw [dualMap_eps, liftDual_eps]

private theorem laurentDual_parameter (R : TestAlgebra k) :
    Units.map (laurentDual R).hom.toMonoidHom
      (Units.map (constants (laurentAlgebra R)).hom.toMonoidHom (laurentParameter R)) =
      laurentParameter (dual R) := by
  apply Units.ext
  change (laurentDual R).hom (TrivSqZeroExt.inl (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1
  unfold laurentDual
  rw [liftDual_inl]
  exact congrArg Units.val (mapLaurent_parameter (constants R))

private theorem mapPoints_one (R S : TestAlgebra k) (a : R ⟶ S) :
    mapPoints (X := G.X) a (1 : GroupPoints G R) = (1 : GroupPoints G S) :=
  map_one (((groupPointsFunctor k).obj G).map a).hom

private theorem laurentDual_orbit (cochar : Cocharacter G) (R : TestAlgebra k)
    (x : GroupPoints G (dual R)) :
    mapPoints (laurentDual R) (mapPoints (dualLaurent R) (orbit cochar x)) = orbit cochar x := by
  let t := Units.map (constants (laurentAlgebra R)).hom.toMonoidHom (laurentParameter R)
  let f := (((groupPointsFunctor k).obj G).map (laurentDual R)).hom
  have ht : f (cocharacterPoint cochar (dual (laurentAlgebra R)) t) =
      cocharacterPoint cochar (laurentAlgebra (dual R)) (laurentParameter (dual R)) :=
    (mapPoints_cocharacterPoint (laurentDual R) cochar t).trans
      (congrArg (cocharacterPoint cochar _) (laurentDual_parameter R))
  have hx : f (mapPoints (dualMap (laurentConstants R)) x) =
      mapPoints (laurentConstants (dual R)) x := by
    change mapPoints (laurentDual R) (mapPoints (dualMap (laurentConstants R)) x) = _
    rw [← mapPoints_comp, laurentDual_constants]
  unfold dualLaurent
  rw [orbit_eval]
  change f (_ * (show GroupPoints G (dual (laurentAlgebra R)) from mapPoints _ x) * _) = _
  rw [map_mul, map_mul, map_inv, ht, hx]
  rfl

private theorem laurentParameter_zpow (R : TestAlgebra k) (n : ℤ) :
    (↑(laurentParameter R ^ n) : LaurentPolynomial R) = LaurentPolynomial.T n := by
  cases n with
  | ofNat n =>
    change (↑(laurentParameter R ^ (n : ℤ)) : LaurentPolynomial R) = LaurentPolynomial.T (n : ℤ)
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T 1 : LaurentPolynomial R) ^ n = _
    rw [LaurentPolynomial.T_pow, mul_one]
  | negSucc n =>
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      zpow_neg, ← inv_zpow, zpow_natCast, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T (-1) : LaurentPolynomial R) ^ (n + 1) = _
    rw [LaurentPolynomial.T_pow, mul_neg_one]

private theorem dualLaurent_constant (R : TestAlgebra k) :
    laurentConstants (dual R) ≫ dualLaurent R = dualMap (laurentConstants R) :=
  evalLaurent_constants _ _

private theorem dualLaurent_orbit {cochar : Cocharacter G} {s : IdentityLieStructure G}
    (W : AdjointWeightBasis cochar s) (R : TestAlgebra k)
    (v : ULift.{u} (Fin W.dimension) → R) :
    letI := s.lieRing
    letI := s.lieAlgebra
    mapPoints (dualLaurent R) (orbit cochar (W.coordinates.equiv R v).toMul.val) =
      (W.coordinates.equiv (laurentAlgebra R) (fun j =>
        LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (v j))).toMul.val := by
  let := s.lieRing
  let := s.lieAlgebra
  change _ = _
  unfold dualLaurent
  rw [orbit_eval, ← W.coordinates.naturality]
  have h := W.diagonal (laurentAlgebra R) (laurentParameter R)
    (fun j => (laurentConstants R).hom (v j))
  have hpow (j : ULift.{u} (Fin W.dimension)) :
      (↑(laurentParameter R ^ W.weight j) : laurentAlgebra R) =
        LaurentPolynomial.T (W.weight j) := laurentParameter_zpow R (W.weight j)
  simp only [hpow] at h
  rw [← mapPoints_cocharacterPoint (constants (laurentAlgebra R))]
  exact h.symm

private theorem coordinates_of_orbit_extension
    {J : Type u} [Fintype J] [DecidableEq J] [AddCommGroup (Lie k G)] [Module k (Lie k G)]
    {b : Module.Basis J k (Lie k G)} (T : TangentCoordinates G J b)
    (ha : IsAffine G.X.left) {R : TestAlgebra k}
    (x : GroupPoints G (laurentAlgebra (dual R))) (w : J → LaurentPolynomial R)
    (hx : mapPoints (dualLaurent R) x = (T.equiv (laurentAlgebra R) w).toMul.val)
    (f : GroupPoints G (polynomialAlgebra (dual R)))
    (hf : mapPoints (polynomialToLaurent (dual R)) f = x) :
    ∃ p : J → Polynomial R, (∀ j, (p j).toLaurent = w j) ∧
      (T.equiv (polynomialAlgebra R) p).toMul.val = mapPoints (dualPolynomial R) f := by
  let F : GroupPoints G (dual (polynomialAlgebra R)) := mapPoints (dualPolynomial R) f
  have hF : mapPoints (dualMap (polynomialToLaurent R)) F =
      (T.equiv (laurentAlgebra R) w).toMul.val := by
    rw [show F = mapPoints (dualPolynomial R) f from rfl, ← mapPoints_comp,
      dualPolynomial_restrict, mapPoints_comp, hf, hx]
  have hred : reduction (polynomialAlgebra R) ≫ polynomialToLaurent R =
      dualMap (polynomialToLaurent R) ≫ reduction (laurentAlgebra R) := rfl
  have h1 : mapPoints (reduction (polynomialAlgebra R)) F =
      (1 : GroupPoints G (polynomialAlgebra R)) := by
    apply polynomialFamily_injective ha
    rw [← mapPoints_comp, hred, mapPoints_comp, hF, mapPoints_one (G := G)]
    exact (T.equiv (laurentAlgebra R) w).toMul.property
  let y : RelativeTangent G (polynomialAlgebra R) := Additive.ofMul ⟨F, h1⟩
  obtain ⟨p, hp⟩ := (T.equiv (polynomialAlgebra R)).surjective y
  have hp' : (T.equiv (polynomialAlgebra R) p).toMul.val = F :=
    congrArg (fun q : RelativeTangent G (polynomialAlgebra R) => q.toMul.val) hp
  refine ⟨p, fun j => ?_, hp'⟩
  have h := (T.naturality (polynomialToLaurent R) p).trans
    ((congrArg (mapPoints (dualMap (polynomialToLaurent R))) hp').trans hF)
  exact congrFun ((T.equiv (laurentAlgebra R)).injective (Subtype.ext h)) j

private theorem orbit_extension_from_coordinates
    {cochar : Cocharacter G} {s : IdentityLieStructure G}
    (W : AdjointWeightBasis cochar s) {R : TestAlgebra k}
    (v : ULift.{u} (Fin W.dimension) → R) (p : ULift.{u} (Fin W.dimension) → Polynomial R)
    (hp : ∀ j, (p j).toLaurent = LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (v j)) :
    letI := s.lieRing
    letI := s.lieAlgebra
    HasLimit cochar (W.coordinates.equiv R v).toMul.val
      (W.coordinates.equiv R (fun j => (polynomialEvaluate R 0).hom (p j))).toMul.val := by
  let := s.lieRing
  let := s.lieAlgebra
  let F := (W.coordinates.equiv (polynomialAlgebra R) p).toMul.val
  refine ⟨mapPoints (polynomialDual R) F, ?_, ?_⟩
  · rw [← mapPoints_comp, polynomialDual_restrict, mapPoints_comp]
    change mapPoints (laurentDual R)
      (mapPoints (dualMap (polynomialToLaurent R)) (W.coordinates.equiv _ p).toMul.val) = _
    rw [← W.coordinates.naturality, show (fun j => (polynomialToLaurent R).hom (p j)) =
      (fun j => LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (v j)) from funext hp,
      ← dualLaurent_orbit W R v, laurentDual_orbit]
  · rw [← mapPoints_comp, polynomialDual_zero]
    exact (W.coordinates.naturality (polynomialEvaluate R 0) p).symm

private theorem orbit_constant_iff {cochar : Cocharacter G} {R : TestAlgebra k}
    (x : GroupPoints G R) :
    Centralizes cochar x ↔ orbit cochar x = mapPoints (laurentConstants R) x := by
  rw [centralizes_onAlgebras]
  constructor
  · intro h
    let t := cocharacterPoint cochar (laurentAlgebra R) (laurentParameter R)
    let a : GroupPoints G (laurentAlgebra R) := mapPoints (laurentConstants R) x
    have hh : a * t = t * a := h (laurentAlgebra R) (laurentConstants R) (laurentParameter R)
    change t * a * t⁻¹ = a
    rw [← hh, mul_inv_cancel_right]
  · intro h S a t
    have hh := congrArg (mapPoints (evalLaurent a t)) h
    rw [orbit_eval, ← mapPoints_comp, evalLaurent_constants] at hh
    let z : GroupPoints G S := mapPoints a x
    let c : GroupPoints G S := cocharacterPoint cochar S t
    change c * z * c⁻¹ = z at hh
    change z * c = c * z
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem constant_orbit_coordinates {cochar : Cocharacter G} {s : IdentityLieStructure G}
    (W : AdjointWeightBasis cochar s) (R : TestAlgebra k)
    (v : ULift.{u} (Fin W.dimension) → R) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Centralizes cochar (W.coordinates.equiv R v).toMul.val ↔
      ∀ j, LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (v j) =
        LaurentPolynomial.C (v j) := by
  let := s.lieRing
  let := s.lieAlgebra
  rw [orbit_constant_iff]
  constructor
  · intro h
    have hc := congrArg (mapPoints (dualLaurent R)) h
    rw [dualLaurent_orbit W R v, ← mapPoints_comp, dualLaurent_constant,
      ← W.coordinates.naturality] at hc
    exact congrFun ((W.coordinates.equiv (laurentAlgebra R)).injective (Subtype.ext hc))
  · intro h
    rw [← laurentDual_orbit cochar R, dualLaurent_orbit W R v]
    change mapPoints (laurentDual R) (W.coordinates.equiv _
      (fun j => LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (v j))).toMul.val = _
    rw [show (fun j => LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (v j)) =
        (fun j => (laurentConstants R).hom (v j)) from funext h,
      W.coordinates.naturality, ← mapPoints_comp, laurentDual_constants]

end DualFamilies

section Subgroups

open private pointHom_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem tangent_image_iff (S : ClosedSubgroup G) (R : TestAlgebra k)
    (x : RelativeTangent G R) :
    x ∈ relativeLieImage S R ↔
      ∃ q : GroupPoints S.group (dual R),
        ((groupPointsFunctor k).map S.inclusion).app (dual R) q = x.toMul.val := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.toMul.val, hq⟩
  · rintro ⟨q, hq⟩
    have hred : mapPoints (reduction R) q = (1 : GroupPoints S.group R) := by
      apply pointHom_injective S R
      have h := congrArg (mapPoints (reduction R)) hq
      change (testSpec k).map (reduction R).op ≫
        (q ≫ S.inclusion.hom.hom) = _ at h
      rw [← Category.assoc] at h
      refine h.trans ?_
      exact x.toMul.property.trans
        (map_one (((groupPointsFunctor k).map S.inclusion).app R).hom).symm
    exact ⟨Additive.ofMul ⟨q, hred⟩, hq⟩

private theorem monomial_coeff {R : Type u} [CommRing R] (a : R) (n j : ℤ) :
    (LaurentPolynomial.T n * LaurentPolynomial.C a).coeff j = if j = n then a else 0 := by
  rw [mul_comm, ← LaurentPolynomial.single_eq_C_mul_T]
  change (Finsupp.single n a) j = _
  rw [Finsupp.single_apply]
  by_cases h : j = n
  · simp [h]
  · simp [h, Ne.symm h]

private theorem zero_of_negative {R : Type u} [CommRing R] {p : Polynomial R}
    {a : R} {n : ℤ} (hp : p.toLaurent = LaurentPolynomial.T n * LaurentPolynomial.C a)
    (hn : n < 0) : a = 0 := by
  have h := congrArg (fun f : LaurentPolynomial R => f.coeff n) hp
  simpa only [coeff_toLaurent_neg p hn, monomial_coeff, ite_true, eq_self] using h.symm

private theorem polynomial_value {R : TestAlgebra k} {p : Polynomial R} {a : R} {n : ℤ}
    (hp : p.toLaurent = LaurentPolynomial.T n * LaurentPolynomial.C a) :
    (polynomialEvaluate R 0).hom p = if n = 0 then a else 0 := by
  have h := congrArg (fun f : LaurentPolynomial R => f.coeff 0) hp
  change (p.toLaurent).coeff (0 : ℕ) = _ at h
  rw [coeff_toLaurent_nat, monomial_coeff] at h
  change p.coeff 0 = _ at h
  change p.eval₂ (RingHom.id R) 0 = _
  rw [Polynomial.eval₂_id, ← Polynomial.coeff_zero_eq_eval_zero]
  simpa only [eq_comm] using h

private def orbitPolynomial {R : Type u} [CommRing R] (n : ℤ) (a : R) : Polynomial R :=
  if 0 ≤ n then Polynomial.monomial n.toNat a else 0

private theorem orbitPolynomial_toLaurent {R : Type u} [CommRing R] (n : ℤ) (a : R)
    (ha : n < 0 → a = 0) :
    (orbitPolynomial n a).toLaurent = LaurentPolynomial.T n * LaurentPolynomial.C a := by
  by_cases hn : 0 ≤ n
  · rw [orbitPolynomial, ite_eq_left hn, ← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.toLaurent_C_mul_X_pow, Int.toNat_of_nonneg hn, mul_comm]
  · rw [ha (lt_of_not_ge hn), orbitPolynomial, ite_eq_right hn, map_zero, map_zero, mul_zero]

theorem relativeLieWeights : Specs.CocharacterDynamics.RelativeLieWeights.{u} := by
  intro k _ G cochar D s W
  let := s.lieRing
  let := s.lieAlgebra
  intro R v
  let x := W.coordinates.equiv R v
  let V := ULift.{u} (Fin W.dimension)
  have parabolic : x ∈ relativeLieImage D.parabolic R ↔ HasExtension cochar x.toMul.val :=
    (tangent_image_iff D.parabolic R x).trans (D.parabolic_points (dual R) x.toMul.val).symm
  have contracting : x ∈ relativeLieImage D.contracting R ↔ HasLimit cochar x.toMul.val 1 :=
    (tangent_image_iff D.contracting R x).trans (D.contracting_points (dual R) x.toMul.val).symm
  have centralizer : x ∈ relativeLieImage D.centralizer R ↔ Centralizes cochar x.toMul.val :=
    (tangent_image_iff D.centralizer R x).trans (D.centralizer_points _ x.toMul.val).symm
  have extend (f : GroupPoints G.val (polynomialAlgebra (dual R)))
      (hf : mapPoints (polynomialToLaurent (dual R)) f = orbit cochar x.toMul.val) :=
    coordinates_of_orbit_extension W.coordinates G.property.1 _ _ (dualLaurent_orbit W R v) f hf
  have construct (hn : ∀ j, W.weight j < 0 → v j = 0) :
      let p : V → Polynomial R := fun j => orbitPolynomial (W.weight j) (v j)
      (∀ j, (p j).toLaurent = LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (v j)) ∧
        HasLimit cochar x.toMul.val
          (W.coordinates.equiv R (fun j => (polynomialEvaluate R 0).hom (p j))).toMul.val := by
    let p : V → Polynomial R := fun j => orbitPolynomial (W.weight j) (v j)
    have hp (j : V) := orbitPolynomial_toLaurent (W.weight j) (v j) (hn j)
    exact ⟨hp, orbit_extension_from_coordinates W v p hp⟩
  refine ⟨parabolic.trans ⟨?_, ?_⟩, contracting.trans ⟨?_, ?_⟩,
    centralizer.trans ((constant_orbit_coordinates W R v).trans ⟨?_, ?_⟩)⟩
  · rintro ⟨z, f, hLaurent, _⟩
    obtain ⟨p, hp, _⟩ := extend f hLaurent
    exact fun j hj => zero_of_negative (hp j) hj
  · intro h
    exact ⟨_, (construct h).2⟩
  · rintro ⟨f, hLaurent, hZero⟩
    obtain ⟨p, hp, hF⟩ := extend f hLaurent
    have hzero := W.coordinates.naturality (polynomialEvaluate R 0) p
    rw [hF, ← mapPoints_comp, dualPolynomial_zero, hZero] at hzero
    have hv : (fun j => (polynomialEvaluate R 0).hom (p j)) = 0 := by
      apply (W.coordinates.equiv R).injective
      apply Subtype.ext
      rw [map_zero]
      exact hzero
    intro j hj
    rcases lt_or_eq_of_le hj with hj | hj
    · exact zero_of_negative (hp j) hj
    · simpa only [polynomial_value (hp j), hj, ite_true, eq_self, Pi.zero_apply] using (congrFun hv j)
  · intro h
    obtain ⟨hp, hlim⟩ := construct (fun j hj => h j hj.le)
    have hz : (fun j => (polynomialEvaluate R 0).hom (orbitPolynomial (W.weight j) (v j))) = 0 := by
      ext j
      rw [polynomial_value (hp j)]
      split
      · rename_i h0
        exact h j h0.le
      · rfl
    rw [hz, map_zero] at hlim
    exact hlim
  · intro h j hj
    have hc := congrArg (fun f : LaurentPolynomial R => f.coeff (W.weight j)) (h j)
    simpa only [monomial_coeff, ite_true, eq_self, LaurentPolynomial.C_apply, ite_eq_right hj] using hc
  · intro h j
    by_cases hj : W.weight j = 0
    · rw [hj, LaurentPolynomial.T_zero, one_mul]
    · rw [h j hj, map_zero, mul_zero]

open private opposite_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

theorem relativeOppositeContractingWeights :
    Specs.CocharacterDynamics.RelativeOppositeContractingWeights.{u} := by
  intro k _ G cochar D s W
  let := s.lieRing
  let := s.lieAlgebra
  let Wop : AdjointWeightBasis (oppositeCocharacter cochar) s := {
    dimension := W.dimension
    basis := W.basis
    coordinates := W.coordinates
    weight j := -W.weight j
    diagonal R t v := by
      rw [opposite_point]
      simpa only [inv_zpow'] using W.diagonal R t⁻¹ v }
  intro R v
  have h := (relativeLieWeights G (oppositeCocharacter cochar) D s Wop R v).2.1
  change W.coordinates.equiv R v ∈ relativeLieImage D.contracting R ↔
    (∀ j, -W.weight j ≤ 0 → v j = 0) at h
  simpa only [neg_nonpos] using h

theorem lieWeights : Specs.CocharacterDynamics.LieWeights.{u} := by
  intro k _ G cochar D s
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨W⟩ := existsAdjointWeightBasis G cochar s
  refine ⟨W, ?_, ?_, ?_⟩
  all_goals
    ext p
    have h (S : ClosedSubgroup G.val) :
        p ∈ lieImage S ↔ W.coordinates.equiv (CommAlgCat.of k k) (W.basis.equivFun p) ∈
          relativeLieImage S (CommAlgCat.of k k) := by
      change (∃ q : Lie k S.group, mapPointKernel S.inclusion q = p) ↔ _
      have he : W.coordinates.equiv (CommAlgCat.of k k) (W.basis.equivFun p) = p :=
        Subtype.ext (W.coordinates.at_base p)
      rw [he]
      change (∃ q : Lie k S.group, mapPointKernel S.inclusion q = p) ↔
        ∃ q : Lie k S.group, (mapPointKernel S.inclusion q).toMul.val = p.toMul.val
      exact ⟨fun ⟨q, hq⟩ => ⟨q, congrArg (fun z : Lie k G.val => z.toMul.val) hq⟩,
        fun ⟨q, hq⟩ => ⟨q, Subtype.ext hq⟩⟩
    obtain ⟨hP, hU, hZ⟩ := relativeLieWeights G cochar D s W
      (CommAlgCat.of k k) (W.basis.equivFun p)
    first | exact (h D.parabolic).trans hP | exact (h D.contracting).trans hU |
      exact (h D.centralizer).trans hZ

end Subgroups

end

end LinearAlgebraicGroups.CocharacterDynamics
