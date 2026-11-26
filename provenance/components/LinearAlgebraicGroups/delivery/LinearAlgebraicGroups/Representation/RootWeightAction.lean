import Specs.LinearAlgebraicGroups.Representation.RootWeightAction
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import LinearAlgebraicGroups.Affine.Stabilizers
import LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.RootData.BorelPositivity
import LinearAlgebraicGroups.RootData.DatumAndWeyl
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj DirectSum TensorProduct
open WithConv

universe u

namespace LinearAlgebraicGroups.Representation.RootWeightAction

open _root_.LinearAlgebraicGroups.Specs
open Specs.RootWeightAction
open Specs.AbstractPairing (Datum Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (characterValue)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters integerGenerator)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open private comp_conjugateFamily from LinearAlgebraicGroups.Affine.Stabilizers
open private tensorCoordinate_tmul tensor_eq_sum_basis pointMatrix pointMatrix_isCoactionMatrix
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private weightProjection sum_projections projection_mem
  from LinearAlgebraicGroups.Multiplicative.WeightDecomposition

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {G : AffineAlgebraicGroup k}

private def pointMap {H L : GroupScheme k} (f : H ⟶ L) (R : TestAlgebra k) :
    GroupPoints H R →* GroupPoints L R :=
  (((groupPointsFunctor k).map f).app R).hom

private theorem pointMap_comp {A B C : GroupScheme k} (f : A ⟶ B) (g : B ⟶ C)
    (R : TestAlgebra k) (p : GroupPoints A R) :
    pointMap (f ≫ g) R p = pointMap g R (pointMap f R p) := rfl

private theorem pointMap_id {H : GroupScheme k} (R : TestAlgebra k) (p : GroupPoints H R) :
    pointMap (𝟙 H) R p = p := by
  change p ≫ 𝟙 H.X = p
  exact Category.comp_id (p : Points H.X R)

private def scalarPoint {H : GroupScheme k} (R : TestAlgebra k)
    (g : GroupPoints H (CommAlgCat.of k k)) : GroupPoints H R :=
  mapPoints (CommAlgCat.ofHom (Algebra.ofId k R) : CommAlgCat.of k k ⟶ R) g

private theorem scalarPoint_inv {H : GroupScheme k} (R : TestAlgebra k)
    (g : GroupPoints H (CommAlgCat.of k k)) :
    scalarPoint R g⁻¹ = (scalarPoint R g)⁻¹ := GrpObj.comp_inv _ _

@[simp] private theorem actLinear_apply {H : GroupScheme k} (ρ : Representation H I)
    (R : TestAlgebra k) (g : GroupPoints H R) (v : I → R) :
    actLinear ρ R g v = act ρ R g v := rfl

private theorem act_mul {H : GroupScheme k} (ρ : Representation H I) (R : TestAlgebra k)
    (g h : GroupPoints H R) (v : I → R) :
    act ρ R (g * h) v = act ρ R g (act ρ R h v) := by
  have e : (ρ.app R (g * h) : Matrix.GeneralLinearGroup I R) = (ρ.app R g) * (ρ.app R h) :=
    (ρ.app R).hom.map_mul g h
  unfold act
  erw [e, Units.val_mul, Matrix.mulVec_mulVec]

private theorem act_one {H : GroupScheme k} (ρ : Representation H I) (R : TestAlgebra k)
    (v : I → R) : act ρ R 1 v = v := by
  have e : (ρ.app R 1 : Matrix.GeneralLinearGroup I R) = 1 := (ρ.app R).hom.map_one
  unfold act
  erw [e, Units.val_one, Matrix.one_mulVec]

private theorem act_smul {H : GroupScheme k} (ρ : Representation H I) (R : TestAlgebra k)
    (g : GroupPoints H R) (a : R) (v : I → R) :
    act ρ R g (a • v) = a • act ρ R g v :=
  (actLinear ρ R g).map_smul a v

private theorem act_natural {H : GroupScheme k} (ρ : Representation H I)
    {R S : TestAlgebra k} (a : R ⟶ S) (g : GroupPoints H R) (v : I → R) :
    act ρ S (mapPoints a g) (fun i ↦ a.hom (v i)) = fun i ↦ a.hom (act ρ R g v i) := by
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality a)) g
  have hm := congrArg (fun a : Matrix.GeneralLinearGroup I S ↦ a.val) h.symm
  change (a.hom.toRingHom.mapMatrix (ρ.app R g).val) = (ρ.app S (mapPoints a g)).val at hm
  funext i
  simp only [act, ← hm, Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
    AlgHom.toRingHom_eq_coe, map_sum, map_mul]
  rfl

private theorem act_extend_natural {H : GroupScheme k} (ρ : Representation H I)
    {R S : TestAlgebra k} (a : R ⟶ S) (g : GroupPoints H R) (v : I → k) :
    act ρ S (mapPoints a g) (extendVector S v) =
      fun i ↦ a.hom (act ρ R g (extendVector R v) i) := by
  rw [← act_natural]
  congr 1
  funext i
  exact (a.hom.commutes (v i)).symm

private def algebraPoint (A : HopfAlgebraCategory k) (R : TestAlgebra k) (f : A →ₐ[k] R) :
    GroupPoints (specGroup A) R :=
  (hopfSpecPointIso A).hom.app R (toConv f)

private theorem algebraPoint_natural (A : HopfAlgebraCategory k) {R S : TestAlgebra k}
    (a : R ⟶ S) (f : A →ₐ[k] R) :
    mapPoints a (algebraPoint A R f) = algebraPoint A S (a.hom.comp f) := by
  exact (DFunLike.congr_fun (congrArg GrpCat.Hom.hom ((hopfSpecPointIso A).hom.naturality a))
    (toConv f)).symm

local notation "GmAlg" => groupAlgebra k IntegerCharacters

private theorem characterValue_eq_eval {T : GroupScheme k} (chi : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue chi R t =
      ((hopfSpecPointIso GmAlg).inv.app R (t ≫ chi.hom.hom)).ofConv
        (MonoidAlgebra.single integerGenerator 1) := by
  let e := hopfSpecPointIso GmAlg
  let x : GroupPoints (specGroup GmAlg) R := t ≫ chi.hom.hom
  let f := e.inv.app R x
  have he : e.hom.app R f = x := (e.app R).inv_hom_id_apply x
  change (testSpec k).map (CommAlgCat.ofHom f.ofConv).op = x at he
  unfold characterValue
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x).unop.hom _ = _
  rw [← he, Functor.FullyFaithful.preimage_map]
  rfl

private theorem characterValue_natural {T : GroupScheme k} (chi : Character T)
    {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T R) :
    characterValue chi S (mapPoints a t) = a.hom (characterValue chi R t) := by
  let x : GroupPoints (specGroup GmAlg) R := t ≫ chi.hom.hom
  let e := hopfSpecPointIso GmAlg
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.inv.naturality a)) x
  have hh : (e.inv.app S (mapPoints a x)).ofConv = a.hom.comp (e.inv.app R x).ofConv :=
    congrArg WithConv.ofConv h
  rw [characterValue_eq_eval, characterValue_eq_eval]
  change (e.inv.app S ((mapPoints a t) ≫ chi.hom.hom)).ofConv
      (MonoidAlgebra.single integerGenerator 1) = _
  erw [Category.assoc]
  exact DFunLike.congr_fun hh _

private theorem characterValue_mul {T : GroupScheme k} (chi psi : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue (chi * psi) R t = characterValue chi R t * characterValue psi R t := by
  let e := (hopfSpecPointIso GmAlg).inv.app R
  let x : GroupPoints (specGroup GmAlg) R := t ≫ chi.hom.hom
  let y : GroupPoints (specGroup GmAlg) R := t ≫ psi.hom.hom
  have h : t ≫ (chi * psi).hom.hom = x * y := MonObj.comp_mul t _ _
  rw [characterValue_eq_eval, characterValue_eq_eval, characterValue_eq_eval]
  change (e (t ≫ (chi * psi).hom.hom)).ofConv (MonoidAlgebra.single integerGenerator 1) = _
  erw [h]
  change (e (x * y)).ofConv (MonoidAlgebra.single integerGenerator 1) =
    (e x).ofConv (MonoidAlgebra.single integerGenerator 1) *
      (e y).ofConv (MonoidAlgebra.single integerGenerator 1)
  rw [e.hom.map_mul x y]
  erw [AlgHom.convMul_apply, MonoidAlgebra.comul_single]
  simp

private theorem characterValue_one {T : GroupScheme k} (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue (1 : Character T) R t = 1 := by
  let e := (hopfSpecPointIso GmAlg).inv.app R
  rw [characterValue_eq_eval]
  change (e (t ≫ (1 : Character T).hom.hom)).ofConv (MonoidAlgebra.single integerGenerator 1) = 1
  have h : t ≫ (1 : Character T).hom.hom = (1 : GroupPoints (specGroup GmAlg) R) :=
    MonObj.comp_one _
  rw [h]
  erw [e.hom.map_one, AlgHom.convOne_apply, MonoidAlgebra.counit_single]
  exact map_one (algebraMap k R)

private theorem rootPoint_natural {A : AdditiveLine k} {H : GroupScheme k}
    (x : A.group ⟶ H) {R S : TestAlgebra k} (a : R ⟶ S) (c : R) :
    mapPoints a (rootPoint x R c) = rootPoint x S (a.hom c) := by
  letI := A.operations.hopf
  let C := CommHopfAlgCat.of k (Polynomial k)
  change mapPoints a (algebraPoint C R (Polynomial.aeval c) ≫ x.hom.hom) =
    algebraPoint C S (Polynomial.aeval (a.hom c)) ≫ x.hom.hom
  have he : mapPoints a (algebraPoint C R (Polynomial.aeval c)) =
      algebraPoint C S (Polynomial.aeval (a.hom c)) := by
    rw [algebraPoint_natural]
    congr 1
    apply Polynomial.algHom_ext
    simp
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ x.hom.hom) he)

private theorem rootPoint_zero {A : AdditiveLine k} {H : GroupScheme k}
    (x : A.group ⟶ H) (R : TestAlgebra k) :
    rootPoint x R (0 : R) = 1 := by
  letI := A.operations.hopf
  let C := CommHopfAlgCat.of k (Polynomial k)
  have h : (Polynomial.aeval (0 : R) : Polynomial k →ₐ[k] R) =
      (1 : WithConv (Polynomial k →ₐ[k] R)).ofConv := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    change 0 = (1 : WithConv (Polynomial k →ₐ[k] R)) Polynomial.X
    rw [AlgHom.convOne_apply]
    change 0 = algebraMap k R (A.operations.epsilon Polynomial.X)
    rw [A.counit, map_zero]
  change pointMap x R (algebraPoint C R (Polynomial.aeval (0 : R))) = 1
  rw [h]
  change pointMap x R ((hopfSpecPointIso C).hom.app R 1) = 1
  erw [(hopfSpecPointIso C).hom.app R |>.hom.map_one, map_one]

private theorem characterValue_pow {T : GroupScheme k} (chi : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) (n : ℕ) :
    characterValue (chi ^ n) R t = characterValue chi R t ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact characterValue_one R t
  | succ n ih => rw [pow_succ, characterValue_mul, ih, pow_succ]

private theorem groupHom_comp {A B C : GroupScheme k} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.hom = f.hom.hom ≫ g.hom.hom := rfl

private theorem characterValue_comp {T H : GroupScheme k} (f : T ⟶ H) (chi : Character H)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue (f ≫ chi) R t = characterValue chi R (t ≫ f.hom.hom) := by
  unfold characterValue
  dsimp only
  erw [Category.assoc, groupHom_comp f chi]

private theorem coeff_aeval_scaled {R : Type u} [CommRing R] [Algebra k R]
    (a : R) (p : Polynomial k) (n : ℕ) :
    (Polynomial.aeval (Polynomial.C a * Polynomial.X) p : Polynomial R).coeff n =
      a ^ n * algebraMap k R (p.coeff n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, hp, hq, mul_add]
  | monomial m c =>
    rw [Polynomial.aeval_monomial, mul_pow, ← Polynomial.C_pow]
    change (Polynomial.C (algebraMap k R c) * (Polynomial.C (a ^ m) * Polynomial.X ^ m)).coeff n = _
    rw [← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
    by_cases h : m = n
    · subst m
      simp [mul_comm]
    · simp [h, Ne.symm h]

private theorem rootOrbit (ρ : Representation G.val I) (T : ClosedSubgroup G.val) :
    RootOrbit ρ T := by
  intro alpha H _ A x h mu v
  let f := x.hom ≫ H.inclusion
  let P := CommAlgCat.of k (Polynomial k)
  let p := act ρ P (rootPoint f P Polynomial.X) (extendVector P v)
  have heval (R : TestAlgebra k) (c : R) :
      act ρ R (rootPoint f R c) (extendVector R v) = fun i ↦ Polynomial.aeval c (p i) := by
    let a : P ⟶ R := CommAlgCat.ofHom (Polynomial.aeval c)
    have eq := act_extend_natural ρ a (rootPoint f P Polynomial.X) v
    rw [rootPoint_natural] at eq
    change act ρ R (rootPoint f R (Polynomial.aeval c Polynomial.X)) (extendVector R v) =
      (fun i ↦ Polynomial.aeval c (p i)) at eq
    rw [Polynomial.aeval_X] at eq
    exact eq
  refine ⟨p, ?_, ?_, heval⟩
  · have eq := heval (CommAlgCat.of k k) 0
    rw [rootPoint_zero, act_one] at eq
    funext i
    have hc := congrFun eq i
    change v.val i = (Polynomial.aeval (0 : k) (p i) : k) at hc
    simpa [Polynomial.aeval_def, Polynomial.eval₂_at_zero] using hc.symm
  · intro j hj
    apply mem_weightSpace.mpr
    intro R t
    let S := CommAlgCat.of k (Polynomial R)
    let a : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R S)
    let ts : GroupPoints T.group S := mapPoints a t
    let gs : GroupPoints G.val S := ts ≫ T.inclusion.hom.hom
    let z : S := Polynomial.X
    have hconj : gs * rootPoint f S z = rootPoint f S (characterValue alpha.val S ts * z) * gs := by
      have eq : gs * rootPoint f S z * gs⁻¹ =
          rootPoint f S (characterValue alpha.val S ts * z) := h S ts z
      exact (inv_mul_cancel_right (gs * rootPoint f S z) gs).symm.trans (congrArg (· * gs) eq)
    have heq := congrArg (fun g ↦ act ρ S g (extendVector S v)) hconj
    simp only [act_mul, heval] at heq
    have hv := mem_weightSpace.mp v.property S ts
    change act ρ S gs (extendVector S v) = characterValue mu S ts • extendVector S v at hv
    rw [hv, act_smul, heval] at heq
    have hmu := characterValue_natural mu a t
    have halpha := characterValue_natural alpha.val a t
    change characterValue mu S ts = Polynomial.C (characterValue mu R t) at hmu
    change characterValue alpha.val S ts = Polynomial.C (characterValue alpha.val R t) at halpha
    have hm := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality a))
      (t ≫ T.inclusion.hom.hom)
    have hm' := congrArg (fun a : Matrix.GeneralLinearGroup I S ↦ a.val) hm.symm
    change (Polynomial.C.mapMatrix (ρ.app R (t ≫ T.inclusion.hom.hom)).val) =
      (ρ.app S gs).val at hm'
    funext i
    have hcoeff := congrArg (fun f : I → S ↦ (f i : Polynomial R).coeff j) heq
    simp only [act, ← hm', Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
      Pi.smul_apply, smul_eq_mul, hmu, halpha, z] at hcoeff
    change (∑ l, Polynomial.C ((ρ.app R (t ≫ T.inclusion.hom.hom)).val i l) *
      (Polynomial.aeval (Polynomial.X : Polynomial R) (p l) : Polynomial R)).coeff j =
      (Polynomial.C (characterValue mu R t) *
        (Polynomial.aeval (Polynomial.C (characterValue alpha.val R t) * Polynomial.X)
          (p i) : Polynomial R)).coeff j at hcoeff
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.aeval_X_left_eq_map,
      Polynomial.coeff_map, coeff_aeval_scaled] at hcoeff
    change (∑ l, (ρ.app R (t ≫ T.inclusion.hom.hom)).val i l *
      algebraMap k R ((p l).coeff j)) =
      characterValue (mu * alpha.val ^ j) R t * algebraMap k R ((p i).coeff j)
    rw [characterValue_mul, characterValue_pow, mul_assoc]
    exact hcoeff

private theorem act_point_over_base {H : GroupScheme k} (ρ : Representation H I)
    (R : TestAlgebra k) (g : GroupPoints H (CommAlgCat.of k k)) (v : I → k) :
    act ρ R (scalarPoint R g) (extendVector R v) =
      extendVector R (act ρ (CommAlgCat.of k k) g v) := by
  let a : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have h : extendVector (CommAlgCat.of k k) v = v := by
    funext p
    exact RingHom.id_apply _
  have ha := act_extend_natural ρ a g v
  rw [h] at ha
  exact ha

private theorem weylTransport (ρ : Representation G.val I) {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} (e : DatumAndWeyl.Identification D) :
    WeylTransport ρ e := by
  intro w n hn mu
  let K := CommAlgCat.of k k
  let g : GroupPoints G.val K := pointMap e.normalizer.inclusion K n
  let a := e.image.conjugation (e.labelEquiv w)
  let nu := (e.labelEquiv w).val mu
  have hnu : nu = a.inv ≫ mu := e.image.characterAction _ _
  have hconj (R : TestAlgebra k) (t : GroupPoints T.group R) :
      scalarPoint R g * pointMap T.inclusion R t * (scalarPoint R g)⁻¹ =
        pointMap T.inclusion R (pointMap a.hom R t) := by
    let b : K ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    let y := (testSpec k).map b.op
    have eq := congrArg (fun z ↦ lift t y ≫ z) (e.image.conjugates _ n _ hn)
    have hright : lift t y ≫ fst T.group.X _ ≫ (a.hom ≫ T.inclusion).hom.hom =
        t ≫ (a.hom ≫ T.inclusion).hom.hom := lift_fst_assoc t y _
    change lift t y ≫ conjugateFamily T.inclusion (n ≫ e.normalizer.inclusion.hom.hom) =
      _ at eq
    erw [hright, comp_conjugateFamily, lift_fst_assoc, lift_snd_assoc] at eq
    have hg : scalarPoint R g = y ≫ n ≫ e.normalizer.inclusion.hom.hom := rfl
    have ht : pointMap T.inclusion R t = t ≫ T.inclusion.hom.hom := rfl
    calc
      _ = t ≫ (a.hom ≫ T.inclusion).hom.hom := by
        erw [hg, ht]
        simpa only [Category.assoc] using eq
      _ = _ := (Category.assoc (t : Points T.group.X R) a.hom.hom.hom T.inclusion.hom.hom).symm
  have hforward (v : weightSpace ρ T mu) : act ρ K g v ∈ weightSpace ρ T nu := by
    apply mem_weightSpace.mpr
    intro R t
    let t' := pointMap a.inv R t
    have h := hconj R t'
    have ht : pointMap a.hom R t' = t := by
      rw [show t' = pointMap a.inv R t from rfl, ← pointMap_comp, Iso.inv_hom_id, pointMap_id]
    rw [ht] at h
    have hcomm : pointMap T.inclusion R t * scalarPoint R g =
        scalarPoint R g * pointMap T.inclusion R t' := by
      rw [← h, inv_mul_cancel_right]
    change act ρ R (pointMap T.inclusion R t) (extendVector R (act ρ K g v)) = _
    have hv : act ρ R (pointMap T.inclusion R t') (extendVector R v) =
        characterValue mu R t' • extendVector R v := mem_weightSpace.mp v.property R t'
    rw [← act_point_over_base, ← act_mul, hcomm, act_mul, hv, act_smul, hnu,
      characterValue_comp, act_point_over_base]
    rfl
  have hbackward (v : weightSpace ρ T nu) : act ρ K g⁻¹ v ∈ weightSpace ρ T mu := by
    apply mem_weightSpace.mpr
    intro R t
    let t' := pointMap a.hom R t
    have h := hconj R t
    change scalarPoint R g * pointMap T.inclusion R t * (scalarPoint R g)⁻¹ =
      pointMap T.inclusion R t' at h
    have hcomm : pointMap T.inclusion R t * (scalarPoint R g)⁻¹ =
        (scalarPoint R g)⁻¹ * pointMap T.inclusion R t' := by
      rw [← h, ← mul_assoc, inv_mul_cancel_left]
    have ht : pointMap a.inv R t' = t := by
      rw [show t' = pointMap a.hom R t from rfl, ← pointMap_comp, Iso.hom_inv_id, pointMap_id]
    have hv : act ρ R (pointMap T.inclusion R t') (extendVector R v) =
        characterValue nu R t' • extendVector R v := mem_weightSpace.mp v.property R t'
    have hval : characterValue nu R t' = characterValue mu R t := by
      rw [hnu, characterValue_comp]
      exact congrArg (characterValue mu R) ht
    change act ρ R (pointMap T.inclusion R t) (extendVector R (act ρ K g⁻¹ v)) = _
    rw [← act_point_over_base, scalarPoint_inv, ← act_mul, hcomm, act_mul, hv, act_smul,
      hval, ← scalarPoint_inv, act_point_over_base]
  let f : weightSpace ρ T mu →ₗ[k] weightSpace ρ T nu :=
    ((actLinear ρ K g).comp (weightSpace ρ T mu).subtype).codRestrict _ hforward
  let f' : weightSpace ρ T nu →ₗ[k] weightSpace ρ T mu :=
    ((actLinear ρ K g⁻¹).comp (weightSpace ρ T nu).subtype).codRestrict _ hbackward
  refine ⟨LinearEquiv.ofLinearMap f f' ?_ ?_, fun _ ↦ rfl⟩
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    change act ρ K g (act ρ K g⁻¹ v) = v.val
    rw [← act_mul, mul_inv_cancel, act_one]
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    change act ρ K g⁻¹ (act ρ K g v) = v.val
    rw [← act_mul, inv_mul_cancel, act_one]

private theorem lift_kernel {T B : GroupScheme k} (U : ClosedSubgroup B)
    (q : B ⟶ T) (hq : IsPullback U.inclusion.hom.hom (toUnit _) q.hom.hom η[T.X])
    (R : TestAlgebra k) (b : GroupPoints B R) (hb : pointMap q R b = 1) :
    ∃ u : GroupPoints U.group R, pointMap U.inclusion R u = b :=
  ⟨hq.lift b (toUnit _) hb, hq.lift_fst _ _ hb⟩

private theorem kernel_point {T B : GroupScheme k} (U : ClosedSubgroup B)
    (q : B ⟶ T) (hq : IsPullback U.inclusion.hom.hom (toUnit _) q.hom.hom η[T.X])
    (R : TestAlgebra k) (u : GroupPoints U.group R) :
    pointMap q R (pointMap U.inclusion R u) = 1 := by
  change (u ≫ U.inclusion.hom.hom) ≫ q.hom.hom = _
  erw [Category.assoc, hq.w, ← Category.assoc, comp_toUnit]
  rfl

private theorem splitPoint {T B : GroupScheme k} (U : ClosedSubgroup B)
    (j : T ⟶ B) (q : B ⟶ T) (hj : j ≫ q = 𝟙 T)
    (hq : IsPullback U.inclusion.hom.hom (toUnit _) q.hom.hom η[T.X])
    (R : TestAlgebra k) (b : GroupPoints B R) :
    ∃ u : GroupPoints U.group R, b =
      pointMap j R (pointMap q R b) * pointMap U.inclusion R u := by
  let t := pointMap j R (pointMap q R b)
  have ht : pointMap q R t = pointMap q R b := by
    rw [show t = _ from rfl, ← pointMap_comp, hj, pointMap_id]
  have hk : pointMap q R (t⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, ht, inv_mul_cancel]
  obtain ⟨u, hu⟩ := lift_kernel U q hq R (t⁻¹ * b) hk
  exact ⟨u, by change b = t * _; rw [hu, mul_inv_cancel_left]⟩

private theorem primitiveLine (ρ : Representation G.val I) (T B : ClosedSubgroup G.val)
    (U : ClosedSubgroup B.group) (j : T.group ⟶ B.group) (q : B.group ⟶ T.group)
    (hj : j ≫ B.inclusion = T.inclusion) (hs : j ≫ q = 𝟙 T.group)
    (hq : IsPullback U.inclusion.hom.hom (toUnit _) q.hom.hom η[T.group.X])
    (mu : Character T.group) (v : I → k) (hv : IsPrimitive ρ T B U mu v)
    (R : TestAlgebra k) (b : GroupPoints B.group R) :
    act ρ R (b ≫ B.inclusion.hom.hom) (extendVector R v) =
      characterValue mu R (b ≫ q.hom.hom) • extendVector R v := by
  let t := pointMap q R b
  obtain ⟨u, e⟩ := splitPoint U j q hs hq R b
  have eq := congrArg (pointMap B.inclusion R) e
  rw [map_mul, ← pointMap_comp j, ← pointMap_comp U.inclusion, hj] at eq
  have hU : act ρ R (pointMap (U.inclusion ≫ B.inclusion) R u) (extendVector R v) =
      extendVector R v := mem_fixedSpace.mp hv.2.1 R u
  change act ρ R (pointMap B.inclusion R b) (extendVector R v) = _
  rw [eq, act_mul, hU]
  exact mem_weightSpace.mp hv.2.2 R t

private def charactersOfIso {A B : GroupScheme k} (i : A ≅ B) :
    Character A ≃ Character B where
  toFun chi := i.inv ≫ chi
  invFun chi := i.hom ≫ chi
  left_inv chi := by simp
  right_inv chi := by simp

private theorem characterValue_monomial {M : Type u} [CommGroup M]
    (R : TestAlgebra k) (f : MonoidAlgebra k M →ₐ[k] R) (m : M) :
    characterValue
      (specGroupMap (groupAlgebraMap k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)))
      R (algebraPoint (groupAlgebra k M) R f) = f (MonoidAlgebra.single m 1) := by
  let chi := specGroupMap (groupAlgebraMap k
    ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom))
  let g := MonoidAlgebra.mapDomainBialgHom k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)
  let x : GroupPoints (specGroup GmAlg) R :=
    algebraPoint (groupAlgebra k M) R f ≫ chi.hom.hom
  have hx : x = algebraPoint GmAlg R (f.comp g.toAlgHom) := by
    change (testSpec k).map (CommAlgCat.ofHom f).op ≫
        (testSpec k).map (CommAlgCat.ofHom g.toAlgHom).op =
      (testSpec k).map (CommAlgCat.ofHom (f.comp g.toAlgHom)).op
    rw [← Functor.map_comp]
    rfl
  rw [characterValue_eq_eval]
  change ((hopfSpecPointIso GmAlg).inv.app R x).ofConv _ = _
  rw [hx]
  have h := (hopfSpecPointIso GmAlg).app R |>.hom_inv_id_apply (toConv (f.comp g.toAlgHom))
  change ((hopfSpecPointIso GmAlg).inv.app R
    (algebraPoint GmAlg R (f.comp g.toAlgHom))) = toConv (f.comp g.toAlgHom) at h
  rw [h]
  change f (g (MonoidAlgebra.single integerGenerator 1)) = _
  rw [MonoidAlgebra.mapDomainBialgHom_single]
  change f (MonoidAlgebra.single (m ^ (1 : ℤ)) 1) = _
  rw [zpow_one]

private theorem universal_torus_character {M : Type u} [CommGroup M]
    {T : GroupScheme k} (i : specGroup (groupAlgebra k M) ≅ T)
    (chi : M ≃* Character (specGroup (groupAlgebra k M)))
    (hchi : ∀ m, chi m = specGroupMap (groupAlgebraMap k
      ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom))) (m : M) :
    let A := groupAlgebra k M
    let P := CommAlgCat.of k (MonoidAlgebra k M)
    let t := pointMap i.hom P (algebraPoint A P (AlgHom.id k A))
    characterValue (charactersOfIso i (chi m)) P t = MonoidAlgebra.of k M m := by
  dsimp only
  let P := CommAlgCat.of k (MonoidAlgebra k M)
  let x := algebraPoint (groupAlgebra k M) P (AlgHom.id k (MonoidAlgebra k M))
  change characterValue (charactersOfIso i (chi m)) P (pointMap i.hom P x) = _
  rw [show charactersOfIso i (chi m) = i.inv ≫ chi m from rfl, characterValue_comp]
  change characterValue (chi m) P (pointMap i.inv P (pointMap i.hom P x)) = _
  rw [← pointMap_comp i.hom i.inv, Iso.hom_inv_id, pointMap_id, hchi]
  change characterValue _ P (algebraPoint (groupAlgebra k M) P
    (AlgHom.id k (MonoidAlgebra k M))) = _
  rw [characterValue_monomial]
  rfl

private theorem torusPoint_weights {M : Type u} [CommGroup M]
    {T : ClosedSubgroup G.val} (ρ : Representation G.val I)
    (i : specGroup (groupAlgebra k M) ≅ T.group)
    (chi : M ≃* Character (specGroup (groupAlgebra k M)))
    (hchi : ∀ m, chi m = specGroupMap (DiagonalizableGroups.groupAlgebraMap k
      ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom))) :
    ∃ c : RightComodule k (groupAlgebra k M) (I → k),
      ∀ m, weightSpace ρ T ((charactersOfIso i) (chi m)) =
        LinearAlgebraicGroups.WeightDecomposition.weightSpace c m := by
  classical
  let A := groupAlgebra k M
  let b := Pi.basisFun k I
  let e := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso i
  let rep := e.hom ≫ (groupPointsFunctor k).map T.inclusion ≫ ρ
  let c := LinearAlgebraicGroups.RationalRepresentations.pointsCoactionEquiv A b rep
  let P := CommAlgCat.of k (MonoidAlgebra k M)
  let t : GroupPoints T.group P :=
    algebraPoint (groupAlgebra k M) P (AlgHom.id k (MonoidAlgebra k M)) ≫ i.hom.hom.hom
  let Q := (ρ.app P (t ≫ T.inclusion.hom.hom)).val
  let coords := LinearAlgebraicGroups.RationalRepresentations.tensorCoordinate (C := MonoidAlgebra k M) b
  have hQ : LinearAlgebraicGroups.RationalRepresentations.coefficients A b c = Q := by
    change LinearAlgebraicGroups.RationalRepresentations.coefficients A b
      (LinearAlgebraicGroups.RationalRepresentations.coactionOfMatrix A b
        (pointMatrix A rep) (pointMatrix_isCoactionMatrix A rep)) = Q
    exact LinearAlgebraicGroups.RationalRepresentations.coefficients_coactionOfMatrix A b
      (pointMatrix A rep) (pointMatrix_isCoactionMatrix A rep)
  have hcoords (v : I → k) (j : I) : coords j (c.coaction v) =
      act ρ P (t ≫ T.inclusion.hom.hom) (extendVector P v) j := by
    let L : (I → k) →ₗ[k] P := (LinearMap.proj j).comp
      (((actLinear ρ P (t ≫ T.inclusion.hom.hom)).restrictScalars k).comp (extendLinear P))
    have eq : (coords j).comp c.coaction = L := by
      apply b.ext
      intro l
      change LinearAlgebraicGroups.RationalRepresentations.coefficients A b c j l =
        act ρ P (t ≫ T.inclusion.hom.hom) (extendVector P (b l)) j
      rw [hQ]
      simp [act, extendVector, b, Pi.basisFun_apply, Matrix.mulVec, dotProduct, Pi.single_apply,
        apply_ite, Q, eq_comm]
    exact DFunLike.congr_fun eq v
  have hvalue (m : M) : characterValue ((charactersOfIso i) (chi m)) P t =
      MonoidAlgebra.of k M m := universal_torus_character i chi hchi m
  have scalar_mul (m : M) (z : k) :
      (MonoidAlgebra.of k M m : MonoidAlgebra k M) * algebraMap k (MonoidAlgebra k M) z =
        z • MonoidAlgebra.of k M m := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have hcompare (m : M) (v : I → k) (j : I) :
      coords j (v ⊗ₜ[k] MonoidAlgebra.of k M m) =
        (characterValue ((charactersOfIso i) (chi m)) P t • extendVector P v) j := by
    rw [hvalue]
    change LinearAlgebraicGroups.RationalRepresentations.tensorCoordinate b j
      (v ⊗ₜ[k] MonoidAlgebra.of k M m) =
      (MonoidAlgebra.of k M m : MonoidAlgebra k M) * algebraMap k (MonoidAlgebra k M) (v j)
    rw [tensorCoordinate_tmul, scalar_mul]
    rfl
  refine ⟨c, fun m ↦ ?_⟩
  ext v
  rw [mem_weightSpace, LinearAlgebraicGroups.WeightDecomposition.mem_weightSpace]
  constructor
  · intro hv
    have heq := hv P t
    rw [← tensor_eq_sum_basis b (c.coaction v), ← tensor_eq_sum_basis b
      (v ⊗ₜ[k] MonoidAlgebra.of k M m)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    change b j ⊗ₜ[k] coords j (c.coaction v) =
      b j ⊗ₜ[k] coords j (v ⊗ₜ[k] MonoidAlgebra.of k M m)
    rw [hcoords, hcompare]
    exact congrArg (fun a ↦ b j ⊗ₜ[k] a) (congrFun heq j)
  · intro hv R s
    have hP : act ρ P (t ≫ T.inclusion.hom.hom) (extendVector P v) =
        characterValue ((charactersOfIso i) (chi m)) P t • extendVector P v := by
      funext j
      rw [← hcoords, hv, hcompare]
    let f := (e.inv.app R) s
    let a : P ⟶ R := CommAlgCat.ofHom f.ofConv
    have ha : mapPoints a t = s := by
      have hpt : mapPoints a t =
          algebraPoint A R f.ofConv ≫ i.hom.hom.hom := by
        have heal := algebraPoint_natural A a (AlgHom.id k A)
        change mapPoints a (algebraPoint A P (AlgHom.id k A)) = algebraPoint A R f.ofConv at heal
        exact (Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ i.hom.hom.hom) heal)
      exact hpt.trans ((e.app R).inv_hom_id_apply s)
    have hg := act_extend_natural ρ a (t ≫ T.inclusion.hom.hom) v
    rw [hP] at hg
    have hc := characterValue_natural ((charactersOfIso i) (chi m)) a t
    rw [ha] at hc
    change act ρ R (mapPoints a t ≫ T.inclusion.hom.hom) (extendVector R v) = _ at hg
    rw [ha] at hg
    funext j
    simpa only [Pi.smul_apply, smul_eq_mul, map_mul, ← hc, extendVector, AlgHom.commutes]
      using congrFun hg j

private theorem torusPoint_preserves_fixed (ρ : Representation G.val I)
    (T B : ClosedSubgroup G.val) (U : ClosedSubgroup B.group)
    (j : T.group ⟶ B.group) (q : B.group ⟶ T.group)
    (hj : j ≫ B.inclusion = T.inclusion)
    (hq : IsPullback U.inclusion.hom.hom (toUnit _) q.hom.hom η[T.group.X])
    (v : fixedSpace ρ (U.inclusion ≫ B.inclusion))
    (R : TestAlgebra k) (t : GroupPoints T.group R) (u : GroupPoints U.group R) :
    act ρ R (u ≫ (U.inclusion ≫ B.inclusion).hom.hom)
        (act ρ R (t ≫ T.inclusion.hom.hom) (extendVector R v)) =
      act ρ R (t ≫ T.inclusion.hom.hom) (extendVector R v) := by
  let tB := pointMap j R t
  let uB := pointMap U.inclusion R u
  let c := tB⁻¹ * uB * tB
  have hc : pointMap q R c = 1 := by
    simp only [c, map_mul, map_inv, uB, kernel_point U q hq R u, mul_one, inv_mul_cancel]
  obtain ⟨u', hu'⟩ := lift_kernel U q hq R c hc
  have hc' : uB * tB = tB * pointMap U.inclusion R u' := by
    rw [hu']
    change uB * tB = tB * (tB⁻¹ * uB * tB)
    group
  have e := congrArg (pointMap B.inclusion R) hc'
  simp only [map_mul, uB, tB, ← pointMap_comp, hj] at e
  change act ρ R (pointMap (U.inclusion ≫ B.inclusion) R u)
    (act ρ R (pointMap T.inclusion R t) (extendVector R v)) = _
  have hv : act ρ R (pointMap (U.inclusion ≫ B.inclusion) R u') (extendVector R v) =
      extendVector R v := mem_fixedSpace.mp v.property R u'
  rw [← act_mul, e, act_mul, hv]
  rfl

private theorem weight_components_fixed (ρ : Representation G.val I)
    (T B : ClosedSubgroup G.val) (U : ClosedSubgroup B.group)
    (j : T.group ⟶ B.group) (q : B.group ⟶ T.group)
    (hj : j ≫ B.inclusion = T.inclusion)
    (hq : IsPullback U.inclusion.hom.hom (toUnit _) q.hom.hom η[T.group.X])
    {M : Type u} [CommGroup M] (i : specGroup (groupAlgebra k M) ≅ T.group)
    (chi : M ≃* Character (specGroup (groupAlgebra k M)))
    (hchi : ∀ m, chi m = specGroupMap (DiagonalizableGroups.groupAlgebraMap k
      ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)))
    (v : fixedSpace ρ (U.inclusion ≫ B.inclusion)) (s : Finset M) (w : M → I → k)
    (hw : ∀ m, w m ∈ weightSpace ρ T ((charactersOfIso i) (chi m)))
    (hs : ∑ m ∈ s, w m = v.val) :
    ∀ m ∈ s, w m ∈ fixedSpace ρ (U.inclusion ≫ B.inclusion) := by
  classical
  intro m hm
  apply mem_fixedSpace.mpr
  intro R u
  let A := MonoidAlgebra k M
  let P := CommAlgCat.of k A
  let S := CommAlgCat.of k (A ⊗[k] R)
  let l : P ⟶ S := CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft)
  let r : R ⟶ S := CommAlgCat.ofHom (Algebra.TensorProduct.includeRight)
  let t : GroupPoints T.group P := algebraPoint (groupAlgebra k M) P (AlgHom.id k A) ≫ i.hom.hom.hom
  let tS := mapPoints l t
  let uS := mapPoints r u
  have hchar (a : M) : characterValue ((charactersOfIso i) (chi a)) S tS =
      (MonoidAlgebra.single a (1 : k) : A) ⊗ₜ[k] (1 : R) := by
    have hbase : characterValue ((charactersOfIso i) (chi a)) P t =
        (MonoidAlgebra.single a (1 : k) : A) := universal_torus_character i chi hchi a
    rw [characterValue_natural, hbase]
    rfl
  have ht : act ρ S (tS ≫ T.inclusion.hom.hom) (extendVector S v) =
      ∑ a ∈ s, characterValue ((charactersOfIso i) (chi a)) S tS • extendVector S (w a) := by
    let L := ((actLinear ρ S (tS ≫ T.inclusion.hom.hom)).restrictScalars k).comp
      (extendLinear S)
    change L v.val = _
    rw [← hs, map_sum]
    exact Finset.sum_congr rfl fun a _ ↦ mem_weightSpace.mp (hw a) S tS
  let g := u ≫ (U.inclusion ≫ B.inclusion).hom.hom
  let gS := uS ≫ (U.inclusion ≫ B.inclusion).hom.hom
  have he := torusPoint_preserves_fixed ρ T B U j q hj hq v S tS uS
  change actLinear ρ S gS (act ρ S (tS ≫ T.inclusion.hom.hom) (extendVector S v)) =
    act ρ S (tS ≫ T.inclusion.hom.hom) (extendVector S v) at he
  rw [ht, map_sum] at he
  simp only [map_smul, actLinear_apply, hchar] at he
  have hn (a : M) : act ρ S gS (extendVector S (w a)) =
      fun p ↦ r.hom (act ρ R g (extendVector R (w a)) p) :=
    act_extend_natural ρ r g (w a)
  have hExt (a : M) (p : I) : extendVector S (w a) p = r.hom (extendVector R (w a) p) :=
    (r.hom.commutes (w a p)).symm
  simp only [hn] at he
  funext p
  let coefficient : S →ₗ[k] R :=
    (TensorProduct.lid k (R : Type u)).toLinearMap.comp
      (((Finsupp.lapply m : (M →₀ k) →ₗ[k] k).comp
        (MonoidAlgebra.coeffLinearEquiv (R := k) (S := k) (M := M)).toLinearMap).rTensor (R : Type u))
  have hmono (a : M) (z : R) :
      coefficient (((MonoidAlgebra.single a (1 : k) : A) ⊗ₜ[k] (1 : R)) * r.hom z) =
        if a = m then z else 0 := by
    change coefficient (((MonoidAlgebra.single a (1 : k) : A) ⊗ₜ[k] (1 : R)) *
      ((1 : A) ⊗ₜ[k] z)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    change (Finsupp.single a (1 : k) m) • z = _
    by_cases h : a = m <;> simp [h]
  have hp := congrArg coefficient (congrFun he p)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hExt, map_sum, hmono,
    Finset.sum_ite_eq', hm, ite_true] at hp
  exact hp

private theorem fixed_weight_decomposition (ρ : Representation G.val I)
    (T B : ClosedSubgroup G.val) (U : ClosedSubgroup B.group)
    (j : T.group ⟶ B.group) (q : B.group ⟶ T.group)
    (hj : j ≫ B.inclusion = T.inclusion)
    (hq : IsPullback U.inclusion.hom.hom (toUnit _) q.hom.hom η[T.group.X])
    (hT : GeometricRadicals.IsSplitTorus T.group) :
    let _ : DecidableEq (Character T.group) := Classical.decEq _
    let L := fixedSpace ρ (U.inclusion ≫ B.inclusion)
    TorusStable ρ T L ∧
      DirectSum.IsInternal (fun chi : Character T.group ↦ (weightSpace ρ T chi).comap L.subtype) := by
  classical
  dsimp only
  let L := fixedSpace ρ (U.inclusion ≫ B.inclusion)
  obtain ⟨n, ⟨iT⟩⟩ := hT
  obtain ⟨iA⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) n
  let i := iA ≪≫ iT.symm
  letI : DecidableEq (StandardLattice.{u} n) := Classical.decEq _
  obtain ⟨chi, _, hchi, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) n
  obtain ⟨c, hc⟩ := torusPoint_weights ρ i chi hchi
  let E := chi.toEquiv.trans (charactersOfIso i)
  have hindep : iSupIndep (weightSpace ρ T) := by
    apply iSupIndep.comp' (f := E) _ E.surjective
    change iSupIndep (fun m ↦ weightSpace ρ T (E m))
    have he : (fun m ↦ weightSpace ρ T (E m)) =
        LinearAlgebraicGroups.WeightDecomposition.weightSpace c := funext hc
    rw [he]
    exact (LinearAlgebraicGroups.WeightDecomposition.weightDecomposition c).submodule_iSupIndep
  have hdecomp (v : L) :
      ∃ (s : Finset (StandardLattice.{u} n)) (w : StandardLattice.{u} n → I → k),
        (∑ a ∈ s, w a) = v.val ∧
        (∀ a, w a ∈ weightSpace ρ T (E a)) ∧ ∀ a ∈ s, w a ∈ L := by
    obtain ⟨s, hs⟩ := sum_projections c v.val
    let w := fun m ↦ weightProjection c m v.val
    have hw (m) : w m ∈ weightSpace ρ T (E m) := by
      rw [show weightSpace ρ T (E m) = _ from hc m]
      exact projection_mem c m v.val
    exact ⟨s, w, hs, hw, weight_components_fixed ρ T B U j q hj hq i chi hchi v s w hw hs⟩
  refine ⟨?_, DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_⟩
  · intro R t v
    obtain ⟨s, w, hs, hw, hf⟩ := hdecomp v
    let F := ((actLinear ρ R (t ≫ T.inclusion.hom.hom)).restrictScalars k).comp (extendLinear R)
    change F v.val ∈ _
    rw [← hs, map_sum]
    refine Submodule.sum_mem _ fun a ha ↦ ?_
    change act ρ R (t ≫ T.inclusion.hom.hom) (extendVector R (w a)) ∈ _
    rw [mem_weightSpace.mp (hw a) R t]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨w a, hf a ha⟩, rfl⟩)
  · intro m
    rw [Submodule.disjoint_def]
    intro v hv hrest
    have hrest' : v.val ∈ ⨆ a, ⨆ (_ : a ≠ m), weightSpace ρ T a := by
      have hle : (⨆ a, ⨆ (_ : a ≠ m), (weightSpace ρ T a).comap L.subtype) ≤
          (⨆ a, ⨆ (_ : a ≠ m), weightSpace ρ T a).comap L.subtype :=
        iSup_le fun a ↦ iSup_le fun ha ↦ Submodule.comap_mono (le_iSup₂ (f := fun a _ ↦ weightSpace ρ T a) a ha)
      exact hle hrest
    apply Subtype.ext
    exact Submodule.disjoint_def.mp (hindep m) v.val hv hrest'
  · apply top_unique
    intro v _
    obtain ⟨s, w, hs, hw, hf⟩ := hdecomp v
    let y : (a : s) → L := fun a ↦ ⟨w a, hf _ a.property⟩
    have hsum : (∑ a : s, y a) = v := by
      apply Subtype.ext
      change L.subtype (∑ a : s, y a) = v.val
      rw [map_sum]
      change (∑ a : s, w a.val) = v.val
      rwa [Finset.sum_coe_sort]
    rw [← hsum]
    exact Submodule.sum_mem _ fun a _ ↦
      Submodule.mem_iSup_of_mem (E a) (hw a)

theorem rootWeightAction_conditional :
    BorelPositivity.Statement.{u} → DatumAndWeyl.Statement.{u} →
      Specs.RootWeightAction.Statement.{u} := by
  intro borel _ k _ G hG T B hT hmax hB hTB
  obtain ⟨hcomm, D, ⟨e⟩, _, _, _, hrad⟩ := borel G hG T hT hmax
  letI := hcomm
  obtain ⟨U, j, q, hU, _, hj, hs, hq, _, _⟩ := hrad B hB hTB
  refine ⟨hcomm, D, e, U, q, hU, ⟨j, hj, hs, hq⟩, ?_⟩
  intro I _ _ ρ
  exact ⟨rootOrbit ρ T, weylTransport ρ e, primitiveLine ρ T B U j q hj hs hq,
    fixed_weight_decomposition ρ T B U j q hj hq hT⟩

end

end LinearAlgebraicGroups.Representation.RootWeightAction

universe v8_closure_3a14a5c1a56de908_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«RootWeightAction».«rootWeightAction» : _root_.«LinearAlgebraicGroups».«Specs».«RootWeightAction».«Statement».{v8_closure_3a14a5c1a56de908_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«RootWeightAction».«rootWeightAction_conditional».{v8_closure_3a14a5c1a56de908_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelPositivity».«borelPositivity».{v8_closure_3a14a5c1a56de908_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«DatumAndWeyl».«datumAndWeyl».{v8_closure_3a14a5c1a56de908_u0})
