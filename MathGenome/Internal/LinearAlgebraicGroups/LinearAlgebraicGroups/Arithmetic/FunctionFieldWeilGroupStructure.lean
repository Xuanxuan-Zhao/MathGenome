import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilGroupStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Pi
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilGroupStructure

open Specs.FunctionFieldWeilGroupStructure
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The adjunction induced by whiskering preserves pointwise trivial maps
in the direction from the scalar-extended domain to the represented functor. -/
private theorem whiskering_mate_trivial {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] {F : C ⥤ D} {U : D ⥤ C}
    (adj : F ⊣ U) {P : C ⥤ GrpCat.{u}} {Q : D ⥤ GrpCat.{u}}
    (a : U ⋙ P ⟶ Q) (ha : ∀ d (x : P.obj (U.obj d)), a.app d x = 1)
    (c : C) (x : P.obj c) :
    ((adj.whiskerLeft GrpCat.{u}).homEquiv P Q a).app c x = 1 := by
  rw [Adjunction.homEquiv_unit]
  exact ha _ _

section Common

variable {k : Type u} [Field k]

private def groupHomOfPoints {D H : GroupScheme k} (hD : IsAffine D.X.left)
    (α : (groupPointsFunctor k).obj D ⟶ (groupPointsFunctor k).obj H) : D ⟶ H :=
  (groupHomEquiv D H hD).symm α

@[simp] private theorem groupHomOfPoints_map {D H : GroupScheme k} (hD : IsAffine D.X.left)
    (α : (groupPointsFunctor k).obj D ⟶ (groupPointsFunctor k).obj H) :
    (groupPointsFunctor k).map (groupHomOfPoints hD α) = α :=
  (groupHomEquiv D H hD).apply_symm_apply α

private theorem groupHom_ext {D H : GroupScheme k} (hD : IsAffine D.X.left)
    {f g : D ⟶ H} (h : (groupPointsFunctor k).map f = (groupPointsFunctor k).map g) :
    f = g :=
  (groupHomComparison k D H hD).injective h

private theorem points_map_zero {D H : GroupScheme k} (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj D).obj R) :
    ((groupPointsFunctor k).map (0 : D ⟶ H)).app R x = 1 := by
  change x ≫ (1 : D.X ⟶ H.X) = 1
  exact MonObj.comp_one x

private def groupIsoOfPoints {D H : GroupScheme k} (hD : IsAffine D.X.left) (hH : IsAffine H.X.left)
    (α : (groupPointsFunctor k).obj D ≅ (groupPointsFunctor k).obj H) : D ≅ H where
  hom := groupHomOfPoints hD α.hom
  inv := groupHomOfPoints hH α.inv
  hom_inv_id := groupHom_ext hD (by simp)
  inv_hom_id := groupHom_ext hH (by simp)

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private abbrev extScalars := WeilRestriction.extendScalars k K
private abbrev resScalars := WeilRestriction.restrictScalars k K

private def tensorAlgHomEquiv (R : CommAlgCat k) (S : CommAlgCat K) :
    ((extScalars k K).obj R ⟶ S) ≃ (R ⟶ (resScalars k K).obj S) := by
  let : Algebra k S := ((resScalars k K).obj S).algebra
  let : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  let c := Algebra.TensorProduct.commRight k K R
  let e := Algebra.TensorProduct.liftEquivRight k K R S
  exact {
    toFun := fun f => CommAlgCat.ofHom (e.symm (f.hom.comp c.toAlgHom))
    invFun := fun g => CommAlgCat.ofHom ((e g.hom).comp c.symm.toAlgHom)
    left_inv := by
      intro f
      apply CommAlgCat.hom_ext
      change (e (e.symm (f.hom.comp c.toAlgHom))).comp c.symm.toAlgHom = f.hom
      rw [Equiv.apply_symm_apply]
      ext x
      simp
    right_inv := by
      intro g
      apply CommAlgCat.hom_ext
      change e.symm (((e g.hom).comp c.symm.toAlgHom).comp c.toAlgHom) = g.hom
      rw [AlgHom.comp_assoc]
      simp }

private theorem tensorAlgHomEquiv_symm_tmul (R : CommAlgCat k) (S : CommAlgCat K)
    (f : R ⟶ (resScalars k K).obj S) (r : R) (x : K) :
    ((tensorAlgHomEquiv k K R S).symm f).hom (r ⊗ₜ[k] x) = f.hom r * algebraMap K S x := by
  simp [tensorAlgHomEquiv, Algebra.TensorProduct.liftEquivRight, mul_comm]

/-- Extension on the right tensor factor is left adjoint to forgetting the extension scalars. -/
private def tensorScalarsAdjunction : extScalars k K ⊣ resScalars k K :=
  Adjunction.mkOfHomEquiv {
    homEquiv := tensorAlgHomEquiv k K
    homEquiv_naturality_left_symm := by
      intro R' R S f g
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul r x =>
        change ((tensorAlgHomEquiv k K R' S).symm (f ≫ g)).hom (r ⊗ₜ[k] x) =
          ((tensorAlgHomEquiv k K R S).symm g).hom (f.hom r ⊗ₜ[k] x)
        rw [tensorAlgHomEquiv_symm_tmul, tensorAlgHomEquiv_symm_tmul]
        rfl
      | add u v hu hv => simp only [map_add, hu, hv]
    homEquiv_naturality_right := by
      intro R S T f g
      apply (tensorAlgHomEquiv k K R T).symm.injective
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      rw [Equiv.symm_apply_apply]
      induction z using TensorProduct.inductionOn with
      | tmul r x =>
        have ht := tensorAlgHomEquiv_symm_tmul k K R S ((tensorAlgHomEquiv k K R S) f) r x
        rw [Equiv.symm_apply_apply] at ht
        change g.hom (f.hom (r ⊗ₜ[k] x)) =
          ((tensorAlgHomEquiv k K R T).symm ((tensorAlgHomEquiv k K R S) f ≫ (resScalars k K).map g)).hom
            (r ⊗ₜ[k] x)
        rw [tensorAlgHomEquiv_symm_tmul, ht, map_mul, AlgHom.commutes]
        rfl
      | add u v hu hv => simp only [map_add, hu, hv] }

/-- Base change restricts the point functor to algebras over the extension. -/
private def groupBaseChangePointsIso (D : GroupScheme k) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj D) ≅
      resScalars k K ⋙ (groupPointsFunctor k).obj D :=
  NatIso.ofComponents
    (fun R => (baseChangePointGroupEquiv K D R).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro p
      exact baseChangePointsNaturality k K D.X f p)

set_option maxHeartbeats 700000 in
private theorem restriction_zero_iff {D W : AffineAlgebraicGroup k} {G : AffineAlgebraicGroup K}
    (ρ : (groupPointsFunctor k).obj W.val ≅ extScalars k K ⋙ (groupPointsFunctor K).obj G.val)
    (c : D.val ⟶ W.val) :
    ∃ d : (groupBaseChange k K).obj D.val ⟶ G.val, d = 0 → c = 0 := by
  let U := (groupPointsFunctor k).obj D.val
  let V := (groupPointsFunctor K).obj G.val
  let β := groupBaseChangePointsIso k K D.val
  let adj := Adjunction.whiskerLeft GrpCat.{u} (tensorScalarsAdjunction k K)
  let e : ((resScalars k K ⋙ U) ⟶ V) ≃ (U ⟶ extScalars k K ⋙ V) := adj.homEquiv U V
  let c' := (groupPointsFunctor k).map c ≫ ρ.hom
  let α := e.symm c'
  let d := groupHomOfPoints (baseChangedAlgebraicGroup K D).property.1 (β.hom ≫ α)
  refine ⟨d, fun hd => ?_⟩
  apply groupHom_ext D.property.1
  apply (cancel_mono ρ.hom).mp
  change c' = (groupPointsFunctor k).map 0 ≫ ρ.hom
  have hα : ∀ (R : TestAlgebra K) (x : (resScalars k K ⋙ U).obj R), α.app R x = 1 := by
    intro R x
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (groupHomOfPoints_map (baseChangedAlgebraicGroup K D).property.1 (β.hom ≫ α)) R)
      ((β.inv.app R) x)
    change ((groupPointsFunctor K).map d).app R (β.inv.app R x) =
      α.app R (β.hom.app R (β.inv.app R x)) at h
    rw [hd, points_map_zero] at h
    have hx : β.hom.app R (β.inv.app R x) = x := GrpCat.hom_inv_apply (β.app R) x
    exact (congrArg (fun y => α.app R y) hx).symm.trans h.symm
  rw [← e.apply_symm_apply c']
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  change (e α).app R x = (ρ.hom.app R) (((groupPointsFunctor k).map 0).app R x)
  rw [points_map_zero, map_one]
  exact whiskering_mate_trivial (tensorScalarsAdjunction k K) α hα R x

end Common

section Anisotropy

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private abbrev unitGroup (k : Type u) [Field k] := StandardGroups.multiplicativeGroup k

private def unitDiagonal (I : Type u) :
    Specs.StandardGroups.multiplicativePoints k ⟶ Specs.StandardGroups.multiplicativePowerPoints k I where
  app R := GrpCat.ofHom (MonoidHom.pi (fun _ : I => MonoidHom.id Rˣ))
  naturality {R S} f := by
    apply GrpCat.ext
    intro p
    rfl

private def singletonUnitsIso :
    Specs.StandardGroups.multiplicativePoints k ≅
      Specs.StandardGroups.multiplicativePowerPoints k (ULift.{u} (Fin 1)) :=
  NatIso.ofComponents (fun R => ((MulEquiv.piUnique
      (fun _ : ULift.{u} (Fin 1) => Rˣ)).symm).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro x
    rfl)

private def unitRankOneIso :
    (unitGroup k).val ≅ (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin 1))).val :=
  groupIsoOfPoints (unitGroup k).property.1
    (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin 1))).property.1
    (StandardGroups.multiplicativeGroupPointsIso k ≪≫ singletonUnitsIso ≪≫
      (StandardGroups.multiplicativePowerGroupPointsIso k (ULift.{u} (Fin 1))).symm)

private def baseChangeUnitIso :
    ((groupBaseChange k K).obj (unitGroup k).val) ≅ (unitGroup K).val :=
  groupIsoOfPoints (baseChangedAlgebraicGroup K (unitGroup k)).property.1 (unitGroup K).property.1
    (groupBaseChangePointsIso k K (unitGroup k).val ≪≫
      Functor.isoWhiskerLeft (resScalars k K) (StandardGroups.multiplicativeGroupPointsIso k) ≪≫
      NatIso.ofComponents (fun _ => Iso.refl _) (by intro R S f; rfl) ≪≫
      (StandardGroups.multiplicativeGroupPointsIso K).symm)

private theorem nontrivial_cocharacter_of_split_subgroup {W : AffineAlgebraicGroup k}
    (S : ClosedSubgroup W.val) {r : ℕ} (hr : 0 < r)
    (e : S.group ≅ (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val) :
    ∃ c : (unitGroup k).val ⟶ W.val, c ≠ 0 := by
  let I := ULift.{u} (Fin r)
  let U := unitGroup k
  let P := Specs.StandardGroups.multiplicativePowerGroup k I
  let α := StandardGroups.multiplicativeGroupPointsIso k
  let β := StandardGroups.multiplicativePowerGroupPointsIso k I
  let δ : (groupPointsFunctor k).obj U.val ⟶ (groupPointsFunctor k).obj P.val := α.hom ≫ unitDiagonal I ≫ β.inv
  let d := groupHomOfPoints U.property.1 δ
  let c : U.val ⟶ W.val := d ≫ e.inv ≫ S.inclusion
  refine ⟨c, fun hc => ?_⟩
  let R := CommAlgCat.of k (LaurentPolynomial k)
  let t : Rˣ := (LaurentPolynomial.isUnit_T 1).unit
  have ht : t ≠ 1 := by
    intro h
    have hT : LaurentPolynomial.T (R := k) 1 = 1 :=
      (LaurentPolynomial.isUnit_T 1).unit_spec.symm.trans (congrArg Units.val h)
    rw [← LaurentPolynomial.T_zero] at hT
    have hd := congrArg LaurentPolynomial.degree hT
    rw [LaurentPolynomial.degree_T, LaurentPolynomial.degree_T] at hd
    exact Int.one_ne_zero (WithBot.coe_injective hd)
  let z := α.inv.app R t
  have hh : ((groupPointsFunctor k).map c).app R z =
      ((groupPointsFunctor k).map c).app R 1 := by
    rw [hc, points_map_zero, points_map_zero]
  have := S.isClosedImmersion
  have : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  have : IsIso e.inv.hom.hom := (Grp.forget (SchemeOver k)).map_isIso e.inv
  change ((z ≫ d.hom.hom) ≫ e.inv.hom.hom) ≫ S.inclusion.hom.hom =
    (((1 : (groupPointsFunctor k).obj U.val |>.obj R) ≫ d.hom.hom) ≫ e.inv.hom.hom) ≫
      S.inclusion.hom.hom at hh
  have he := (cancel_mono e.inv.hom.hom).mp ((cancel_mono S.inclusion.hom.hom).mp hh)
  change ((groupPointsFunctor k).map d).app R z =
    ((groupPointsFunctor k).map d).app R 1 at he
  rw [groupHomOfPoints_map] at he
  have hz (x : ((groupPointsFunctor k).obj U.val).obj R) :
      β.hom.app R (δ.app R x) (⟨⟨0, hr⟩⟩ : I) = α.hom.app R x := by
    change (β.app R).hom ((β.app R).inv ((unitDiagonal I).app R (α.hom.app R x)))
        (⟨⟨0, hr⟩⟩ : I) = _
    rw [GrpCat.hom_inv_apply]
    rfl
  have h := congrArg (fun x => β.hom.app R x (⟨⟨0, hr⟩⟩ : I)) he
  rw [hz, hz, map_one] at h
  exact ht ((GrpCat.hom_inv_apply (α.app R) t).symm.trans h)

end Anisotropy

section CocharacterImage

open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra)
open private specIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

variable {k : Type u} [Field k]

/-- A nonzero cocharacter has a closed image with a rank-one character lattice. -/
private theorem cocharacterImage {G : AffineAlgebraicGroup k} (c : Cocharacter G.val)
    (hc : c ≠ 0) :
    ∃ S : ClosedSubgroup G.val,
      Nonempty (S.group ≅ (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin 1))).val) := by
  let z : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  haveI : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := z.symm.toMonoidHom) z.symm.surjective
  let D := DiagonalizableGroups.diagonalGroup k IntegerCharacters.{u}
  obtain ⟨F, p, i, h, _, _⟩ := schemeImageFactorization D G c
  obtain ⟨M, ⟨a, _⟩, _⟩ :=
    (DiagonalizableGroups.diagonalFaithfullyFlatQuotients k IntegerCharacters.{u}
      ⟨F.val, F.property.1⟩ p).mp ⟨h.2.1, h.2.2.1⟩
  have hM : Nontrivial M := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    apply hc
    have hp : p = 0 := by
      apply groupHom_ext D.property.1
      apply NatTrans.ext
      funext R
      apply GrpCat.ext
      intro x
      let b := (groupPointsFunctor k).mapIso a.symm ≪≫ DiagonalizableGroups.groupAlgebraPointsIso k M
      apply (b.app R).groupIsoToMulEquiv.injective
      have hchars : Subsingleton (M →* Rˣ) :=
        ⟨fun f g => MonoidHom.ext fun m => by rw [hs.elim m 1, map_one, map_one]⟩
      exact hchars.elim _ _
    rw [← h.1, hp, zero_comp]
  haveI : IsCyclic IntegerCharacters.{u} := z.isCyclic.mpr inferInstance
  haveI : Infinite IntegerCharacters.{u} := Infinite.of_injective z.symm z.symm.injective
  haveI : IsCyclic M := Subgroup.isCyclic M
  let t : IntegerCharacters.{u} ≃* M := z.trans (intCyclicMulEquiv (G := M))
  let e := specIso (A := groupAlgebra k IntegerCharacters.{u}) (B := groupAlgebra k M)
    (MonoidAlgebra.domCongrBialgEquiv k k t)
  exact ⟨⟨F.val, i, h.2.2.2.2.2⟩,
    ⟨a.symm ≪≫ e ≪≫ DiagonalizableGroups.multiplicativeGroupIso k ≪≫ unitRankOneIso⟩⟩

end CocharacterImage

section ScalarProduct

variable {k K E I : Type u} [Field k] [Field K] [Algebra k K] [Field E] [Algebra k E]

open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private def scalarEmbedding (e : E ⊗[k] K ≃ₐ[E] (I → E)) (i : I) : K →+* E :=
  (Pi.evalRingHom (fun _ : I => E) i).comp
    (e.toRingHom.comp (includeRight : K →ₐ[k] E ⊗[k] K).toRingHom)

private abbrev factorScalars (σ : K →+* E) : TestAlgebra E ⥤ TestAlgebra K :=
  letI : Algebra K E := σ.toAlgebra
  resScalars K E

private abbrev scalarFactor (σ : K →+* E) (G : AffineAlgebraicGroup K) :
    AffineAlgebraicGroup E :=
  letI : Algebra K E := σ.toAlgebra
  baseChangedAlgebraicGroup E G

private def scalarFactorPoints (σ : K →+* E) (G : GroupScheme K) :
    letI : Algebra K E := σ.toAlgebra
    (groupPointsFunctor E).obj ((groupBaseChange K E).obj G) ≅
      factorScalars σ ⋙ (groupPointsFunctor K).obj G :=
  letI : Algebra K E := σ.toAlgebra
  groupBaseChangePointsIso K E G

variable [Fintype I] [DecidableEq I]

private def scalarProductEquiv (e : E ⊗[k] K ≃ₐ[E] (I → E)) (R : TestAlgebra E) :
    ((resScalars k E).obj R) ⊗[k] K ≃ₐ[K] (∀ i, (factorScalars (scalarEmbedding e i)).obj R) := by
  let _ : Algebra k R := ((resScalars k E).obj R).algebra
  let _ : IsScalarTower k E R := IsScalarTower.of_algebraMap_eq' rfl
  let a := Algebra.TensorProduct.cancelBaseChange k E E R K
  let b := Algebra.TensorProduct.congr (AlgEquiv.refl (R := E) (A₁ := R)) e
  let c := Algebra.TensorProduct.piScalarRight E E R I
  refine { (a.symm.trans (b.trans c)).toRingEquiv with commutes' := ?_ }
  intro x
  ext i
  change (a.symm.trans (b.trans c)) ((1 : R) ⊗ₜ[k] x) i =
    algebraMap E R (e ((1 : E) ⊗ₜ[k] x) i)
  simp [a, b, c, Algebra.TensorProduct.congr_apply, Algebra.smul_def]

private theorem scalarProductEquiv_tmul (e : E ⊗[k] K ≃ₐ[E] (I → E)) (R : TestAlgebra E)
    (r : R) (x : K) (i : I) :
    let _ : Algebra k R := ((resScalars k E).obj R).algebra
    scalarProductEquiv e R (r ⊗ₜ[k] x) i =
      algebraMap E R (e ((1 : E) ⊗ₜ[k] x) i) * r := by
  let _ : Algebra k R := ((resScalars k E).obj R).algebra
  let _ : IsScalarTower k E R := IsScalarTower.of_algebraMap_eq' rfl
  change (Algebra.TensorProduct.piScalarRight E E R I)
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := E) (A₁ := R)) e
    ((Algebra.TensorProduct.cancelBaseChange k E E R K).symm (r ⊗ₜ[k] x))) i = _
  simp [Algebra.TensorProduct.congr_apply, Algebra.smul_def]

private def scalarProjection (e : E ⊗[k] K ≃ₐ[E] (I → E)) (i : I) :
    resScalars k E ⋙ extScalars k K ⟶ factorScalars (scalarEmbedding e i) where
  app R := by
    let C (j : I) := (factorScalars (scalarEmbedding e j)).obj R
    let _ (j : I) : Algebra K (C j) := (C j).algebra
    exact ConcreteCategory.ofHom (C := CommAlgCat K) (Y := C i)
      ((Pi.evalAlgHom K (fun j => C j) i).comp (scalarProductEquiv e R).toAlgHom)
  naturality {R S} f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      change scalarProductEquiv e S (f.hom r ⊗ₜ[k] x) i =
        f.hom (scalarProductEquiv e R (r ⊗ₜ[k] x) i)
      rw [scalarProductEquiv_tmul, scalarProductEquiv_tmul, map_mul, AlgHom.commutes]
    | add z t hz ht => rw [map_add, map_add, hz, ht]

private theorem groupFunctor_productEquiv {k I : Type u} [Field k]
    (V : TestAlgebra k ⥤ GrpCat.{u}) (A : TestAlgebra k)
    (E : coyoneda.obj (op A) ≅ V ⋙ forget GrpCat)
    (C : I → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra k (C i)] :
    ∃ e : V.obj (CommAlgCat.of k (∀ i, C i)) ≃* (∀ i, V.obj (CommAlgCat.of k (C i))),
      ∀ g i, e g i = (V.map (CommAlgCat.ofHom (Pi.evalAlgHom k C i))).hom g := by
  let P := CommAlgCat.of k (∀ i, C i)
  let T (i : I) := CommAlgCat.of k (C i)
  let π (i : I) : P ⟶ T i := CommAlgCat.ofHom (Pi.evalAlgHom k C i)
  let φ : V.obj P →* (∀ i, V.obj (T i)) := MonoidHom.pi fun i => (V.map (π i)).hom
  suffices hφ : Function.Bijective φ from ⟨MulEquiv.ofBijective φ hφ, fun _ _ => rfl⟩
  let e (R : TestAlgebra k) : (A ⟶ R) ≃ V.obj R := (E.app R).toEquiv
  have he (i : I) (a : A ⟶ P) :
      e (T i) (a ≫ π i) = (V.map (π i)).hom (e P a) :=
    ConcreteCategory.congr_hom (E.hom.naturality (π i)) a
  constructor
  · intro a b hab
    apply (e P).symm.injective
    apply CommAlgCat.hom_ext
    ext x i
    have hh : e (T i) ((e P).symm a ≫ π i) = e (T i) ((e P).symm b ≫ π i) := by
      rw [he, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact congrFun hab i
    exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom ((e (T i)).injective hh)) x
  · intro b
    let a : A ⟶ P := CommAlgCat.ofHom (AlgHom.pi fun i => ((e (T i)).symm (b i)).hom)
    refine ⟨e P a, funext fun i => ?_⟩
    change (V.map (π i)).hom (e P a) = b i
    rw [← he, ← (e (T i)).apply_symm_apply (b i)]
    congr 1

/-- Affine group points on a product of test algebras are the product of
the point groups with the coordinate maps induced by evaluation. -/
private theorem exists_groupPoints_productEquiv {k I : Type u} [Field k] (G : Specs.AffineAlgebraicGroup k)
    (C : I → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra k (C i)] :
    let V := (groupPointsFunctor k).obj G.val
    ∃ e : V.obj (CommAlgCat.of k (∀ i, C i)) ≃* (∀ i, V.obj (CommAlgCat.of k (C i))),
      ∀ g i, e g i = (V.map (CommAlgCat.ofHom (Pi.evalAlgHom k C i))).hom g := by
  obtain ⟨A, ⟨j⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.property.1
  exact groupFunctor_productEquiv ((groupPointsFunctor k).obj G.val) A.unop
    (WeilRestriction.spectrumPoints A.unop G.val.X j) C

private def weilProductProjection {G : AffineAlgebraicGroup K} {W : AffineAlgebraicGroup k}
    (ρ : (groupPointsFunctor k).obj W.val ≅ extScalars k K ⋙ (groupPointsFunctor K).obj G.val)
    (e : E ⊗[k] K ≃ₐ[E] (I → E)) (i : I) :
    (groupPointsFunctor E).obj (baseChangedAlgebraicGroup E W).val ⟶
      (groupPointsFunctor E).obj (scalarFactor (scalarEmbedding e i) G).val :=
  (groupBaseChangePointsIso k E W.val).hom ≫
    Functor.whiskerLeft (resScalars k E) ρ.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (scalarProjection e i) ((groupPointsFunctor K).obj G.val) ≫
    (scalarFactorPoints (scalarEmbedding e i) G.val).inv

private theorem weilProductProjection_bijective {G : AffineAlgebraicGroup K}
    {W : AffineAlgebraicGroup k}
    (ρ : (groupPointsFunctor k).obj W.val ≅ extScalars k K ⋙ (groupPointsFunctor K).obj G.val)
    (e : E ⊗[k] K ≃ₐ[E] (I → E)) (R : TestAlgebra E) :
    let U := (groupPointsFunctor E).obj (baseChangedAlgebraicGroup E W).val
    Function.Bijective (fun (x : U.obj R) i => (weilProductProjection ρ e i).app R x) := by
  let V := (groupPointsFunctor K).obj G.val
  let C (i : I) := (factorScalars (scalarEmbedding e i)).obj R
  let iso := CommAlgCat.isoMk (scalarProductEquiv e R)
  let a := ((groupBaseChangePointsIso k E W.val).app R ≪≫
    ρ.app ((resScalars k E).obj R) ≪≫ V.mapIso iso).groupIsoToMulEquiv
  let b (i : I) := ((scalarFactorPoints (scalarEmbedding e i) G.val).app R).symm.groupIsoToMulEquiv
  let _ (i : I) : Algebra K (C i) := (C i).algebra
  obtain ⟨p, hp⟩ := exists_groupPoints_productEquiv G (fun i => C i)
  have h := (Equiv.piCongrRight fun i => (b i).toEquiv).bijective.comp
    (p.bijective.comp a.bijective)
  convert h using 2
  rename_i x
  funext i
  change _ = b i (p (a x) i)
  rw [hp]
  change _ = b i ((V.map (CommAlgCat.ofHom (Pi.evalAlgHom K (fun i => C i) i)))
    ((V.map iso.hom) _))
  rw [← GrpCat.comp_apply, ← Functor.map_comp]
  have hm : (scalarProjection e i).app R =
      iso.hom ≫ CommAlgCat.ofHom (Pi.evalAlgHom K (fun i => C i) i) := by
    apply CommAlgCat.hom_ext
    rfl
  rw [← hm]
  rfl

end ScalarProduct

section Products

open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private productOptionIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

variable {E : Type u} [Field E]

private theorem affine_finite_product (I : Type u) [Finite I] (X : I → SchemeOver E)
    (hX : ∀ i, IsAffine (X i).left) : IsAffine (∏ᶜ X).left := by
  classical
  cases nonempty_fintype I
  revert X
  refine Fintype.induction_empty_option
    (P := fun I [Fintype I] => ∀ X : I → SchemeOver E,
      (∀ i, IsAffine (X i).left) → IsAffine (∏ᶜ X).left)
    ?_ ?_ ?_ I
  · intro α β _ e ih X hX
    have : Finite α := Finite.of_equiv β e.symm
    have h := ih (X ∘ e) (fun i => hX (e i))
    let a := Pi.reindex e X
    have : IsIso a.inv.left := ((Over.forget _).mapIso a).isIso_inv
    exact IsAffine.of_isIso a.inv.left
  · intro X _
    let e : (∏ᶜ X) ≅ 𝟙_ (SchemeOver E) :=
      ⟨toUnit _, Pi.lift (fun i => PEmpty.elim i),
        Pi.hom_ext _ _ (fun i => PEmpty.elim i), toUnit_unique _ _⟩
    have : IsAffine (𝟙_ (SchemeOver E)).left := inferInstanceAs (IsAffine (Spec _))
    have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
    exact IsAffine.of_isIso e.hom.left
  · intro α _ ih X hX
    have := hX none
    have := ih (fun i => X (some i)) (fun i => hX (some i))
    have : IsAffine (X none ⊗ (∏ᶜ fun i => X (some i))).left :=
      inferInstanceAs (IsAffine (pullback (X none).hom (∏ᶜ fun i => X (some i)).hom))
    let e := productOptionIso X
    have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
    exact IsAffine.of_isIso e.hom.left

variable {I : Type u} {H : AffineAlgebraicGroup E} {J : I → AffineAlgebraicGroup E}

private abbrev productPointMap (q : ∀ i, H.val ⟶ (J i).val) (R : TestAlgebra E) :=
  fun (x : ((groupPointsFunctor E).obj H.val).obj R) i =>
    ((groupPointsFunctor E).map (q i)).app R x

private def productSchemeIso [Finite I] (q : ∀ i, H.val ⟶ (J i).val)
    (hq : ∀ R, Function.Bijective (productPointMap q R)) :
    H.val.X ≅ ∏ᶜ (fun i => (J i).val.X) := by
  let X (i : I) := (J i).val.X
  let Y := ∏ᶜ X
  let f : H.val.X ⟶ Y := Pi.lift (fun i => (q i).hom.hom)
  have hY : IsAffine Y.left := affine_finite_product I X (fun i => (J i).property.1)
  have hA := essImage_algSpec.mpr hY
  let A := hA.choose
  let a := Classical.choice hA.choose_spec
  have hlift := (hq A.unop).2 (fun i => a.hom ≫ Pi.π X i)
  let p : (testSpec E).obj A ⟶ H.val.X := hlift.choose
  have hp (i : I) : p ≫ (q i).hom.hom = a.hom ≫ Pi.π X i :=
    congrFun hlift.choose_spec i
  have hf (i : I) : f ≫ Pi.π X i = (q i).hom.hom := Pi.lift_comp_π _ i
  have hpf : p ≫ f = a.hom := by
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, hf]
    exact hp i
  refine ⟨f, a.inv ≫ p, ?_, ?_⟩
  · have he : (f ≫ a.inv ≫ p) ≫ f = f := by
      rw [Category.assoc, Category.assoc, hpf, a.inv_hom_id, Category.comp_id]
    apply hom_ext_of_points H.property.1
    intro R x
    apply (hq R).1
    funext i
    change (x ≫ f ≫ a.inv ≫ p) ≫ (q i).hom.hom = (x ≫ 𝟙 _) ≫ (q i).hom.hom
    rw [Category.comp_id, ← hf i]
    simpa only [Category.assoc] using congrArg (fun m => x ≫ m ≫ Pi.π X i) he
  · rw [Category.assoc, hpf, a.inv_hom_id]

private theorem productProjectionSection (q : ∀ i, H.val ⟶ (J i).val)
    (hq : ∀ R, Function.Bijective (productPointMap q R)) (i : I) :
    ∃ s : (J i).val ⟶ H.val, s ≫ q i = 𝟙 _ := by
  classical
  let V := groupPointsFunctor E
  let U := V.obj H.val
  let T (j : I) := V.obj (J j).val
  let e (R : TestAlgebra E) : U.obj R ≃* (∀ j, (T j).obj R) :=
    MulEquiv.ofBijective
      (MonoidHom.pi fun j => ((V.map (q j)).app R).hom) (hq R)
  let F : T i ⟶ U :=
    { app := fun R => GrpCat.ofHom
        ((e R).symm.toMonoidHom.comp (MonoidHom.mulSingle (fun j => (T j).obj R) i))
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro x
        apply (e S).injective
        funext j
        have hh := ConcreteCategory.congr_hom ((V.map (q j)).naturality f)
          ((e R).symm (Pi.mulSingle i x))
        let xₛ : (T i).obj S := (T i).map f x
        let singleₛ : ∀ j, (T j).obj S := Pi.mulSingle i xₛ
        have hx : (e S) ((e S).symm singleₛ) j = singleₛ j :=
          congrFun ((e S).apply_symm_apply singleₛ) j
        change (e S) ((e S).symm singleₛ) j = _
        rw [hx]
        let single : ∀ j, (T j).obj R := Pi.mulSingle i x
        have hr : ((V.map (q j)).app R) ((e R).symm single) = single j :=
          congrFun ((e R).apply_symm_apply single) j
        change _ = ((V.map (q j)).app S) ((U.map f) ((e R).symm (Pi.mulSingle i x)))
        change ((T j).map f) (((V.map (q j)).app R) ((e R).symm (Pi.mulSingle i x))) =
          ((V.map (q j)).app S) ((U.map f) ((e R).symm (Pi.mulSingle i x))) at hh
        rw [← hh]
        change _ = (T j).map f (((V.map (q j)).app R) ((e R).symm single))
        rw [hr]
        by_cases h : j = i
        · subst j
          simp [single, singleₛ, xₛ]
        · simp [single, singleₛ, Pi.mulSingle_eq_of_ne h] }
  refine ⟨groupHomOfPoints (J i).property.1 F, groupHom_ext (J i).property.1 ?_⟩
  rw [Functor.map_comp]
  rw [(groupPointsFunctor E).map_id, groupHomOfPoints_map]
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  change (e R) ((e R).symm (Pi.mulSingle i x)) i = x
  rw [(e R).apply_symm_apply, Pi.mulSingle_eq_same]

end Products

section Radicals

open Specs.GeometricRadicals (GeometricGroup IsSemisimple IsSmoothConnectedNormal
  IsTrivialSubgroup geometricSolvableRadical)
open Specs.SchemeDerivedGroup (IsSolvable)
open LinearAlgebraicGroups.Specs (IsImageFactorization subgroupConjugation)
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private exists_section_lift geometricallyConnected_of_connected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private solvable_iff_sections trivial_of_subsingleton_sections rationalMap rationalSections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private trivial_baseChange_iff smooth_baseChange_iff connected_baseChange_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private tensorHom_property from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components

variable {E : Type u} [Field E]

private theorem projected_image_normal {H J F : AffineAlgebraicGroup E}
    {N : ClosedSubgroup H.val} (q : H.val ⟶ J.val) (s : J.val ⟶ H.val) (hs : s ≫ q = 𝟙 _)
    (hN : IsNormalSubgroup N.inclusion)
    (p : N.group ⟶ F.val) (i : F.val ⟶ J.val)
    (hp : IsImageFactorization (N.inclusion ≫ q) p i)
    (hJ : Smooth J.val.X.hom) (hF : Smooth F.val.X.hom) : IsNormalSubgroup i := by
  let Y := J.val.X ⊗ N.group.X
  let X := J.val.X ⊗ F.val.X
  let l : Y ⟶ X := 𝟙 _ ⊗ₘ p.hom.hom
  have : Surjective l.left := tensorHom_property _ _ @Surjective inferInstance hp.2.2.1
  have := hJ
  have := hF
  have : Smooth X.hom := by
    change Smooth (J.val.X ⊗ F.val.X).hom
    rw [Over.tensorObj_hom]
    infer_instance
  have : IsReduced X.left := isReduced_of_smooth_over_field X.hom
  obtain ⟨b, hb⟩ := normalSubgroup_conjugate_sections hN
    (fst J.val.X N.group.X ≫ s.hom.hom) (snd J.val.X N.group.X)
  have hi' : p.hom.hom ≫ i.hom.hom = N.inclusion.hom.hom ≫ q.hom.hom :=
    congrArg (fun f : N.group ⟶ J.val => f.hom.hom) hp.1
  have hs' : s.hom.hom ≫ q.hom.hom = 𝟙 _ :=
    congrArg (fun f : J.val ⟶ J.val => f.hom.hom) hs
  have he : l ≫ subgroupConjugation i = (b ≫ p.hom.hom) ≫ i.hom.hom := by
    simp only [l, subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
      tensorHom_fst, tensorHom_snd_assoc, Category.comp_id, hi']
    have h := congrArg (fun t => t ≫ q.hom.hom) hb
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hs', Category.comp_id] at h
    exact h.symm
  let g := subgroupConjugation i
  let j := i.hom.hom
  let r := pullback.fst g j
  let v := pullback.snd g j
  let w := pullback.lift l (b ≫ p.hom.hom) he
  have hw : w ≫ r = l := pullback.lift_fst _ _ _
  have hcart : IsPullback r.left v.left g.left j.left :=
    (IsPullback.of_hasPullback g j).map (Over.forget _)
  have : IsClosedImmersion r.left :=
    MorphismProperty.of_isPullback hcart.flip hp.2.2.2.2.2
  have : Surjective r.left := ⟨fun x => by
    obtain ⟨y, hy⟩ := l.left.surjective x
    refine ⟨w.left y, ?_⟩
    exact (congrArg (fun f : Y ⟶ X => f.left y) hw).trans hy⟩
  have : IsIso ((Over.forget _).map r) := isIso_of_isClosedImmersion_of_surjective r.left
  have : IsIso r := isIso_of_reflects_iso r (Over.forget _)
  refine ⟨inv r ≫ v, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

variable [IsAlgClosed E]

private theorem semisimple_kills_projected_radical {H J : AffineAlgebraicGroup E}
    (hJ : IsSemisimple J) (q : H.val ⟶ J.val) (s : J.val ⟶ H.val) (hs : s ≫ q = 𝟙 _)
    (N : ClosedSubgroup H.val) (hN : IsSmoothConnectedNormal (G := H) N)
    (hsolv : IsSolvable N.group) : N.inclusion ≫ q = 0 := by
  let A := closedSubgroupAlgebraicGroup N
  obtain ⟨F, p, i, hp, _, _⟩ := schemeImageFactorization A J (N.inclusion ≫ q)
  let I : ClosedSubgroup J.val := ⟨F.val, i, hp.2.2.2.2.2⟩
  have : IsAffine A.val.X.left := A.property.1
  have : IsAffine F.val.X.left := F.property.1
  have hAs : Smooth A.val.X.hom := hN.1
  have : IsReduced A.val.X.left := isReduced_of_smooth_over_field A.val.X.hom
  have hfaith := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine p.hom.hom.left).mp
    ⟨hp.2.1, hp.2.2.1⟩
  have : _root_.IsReduced Γ(F.val.X.left, ⊤) :=
    isReduced_of_injective p.hom.hom.left.appTop.hom hfaith.injective
  have : IsReduced F.val.X.left := isReduced_of_isAffine_isReduced _
  have := F.property.2.1
  have hFs := smoothOfReducedOverPerfectField E F.val inferInstance
  have : Surjective p.hom.hom.left := hp.2.2.1
  have : ConnectedSpace A.val.X.left := hN.2.1
  have hFc : ConnectedSpace F.val.X.left :=
    p.hom.hom.left.surjective.connectedSpace p.hom.hom.left.continuous
  have hFn := projected_image_normal q s hs hN.2.2 p i hp hJ.1 hFs
  have : Group.IsSolvable (rationalSections A.val) :=
    (solvable_iff_sections A hN.1 hN.2.1).mp hsolv
  have := A.property.2.1
  have hsurj : Function.Surjective (rationalMap p) := by
    intro x
    exact exists_section_lift p.hom.hom x (p.hom.hom.left.surjective _)
  have hFsolv : IsSolvable F.val := (solvable_iff_sections F hFs hFc).mpr
    (Group.isSolvable_of_surjective (f := rationalMap p) hsurj)
  obtain ⟨M, hM, m, _⟩ :=
    Reductive.RadicalBaseChange.solvableRadicalPerfectDescent J hJ.1 hJ.2.1
  obtain ⟨t⟩ := hJ.2.2
  obtain ⟨e⟩ := (trivial_baseChange_iff (K := AlgebraicClosure E) M.group).mp ⟨m ≪≫ t⟩
  obtain ⟨j, hj⟩ := hM.2.2 I ⟨hFs, hFc, hFn⟩ hFsolv
  have hj₀ : j = 0 := IsZero.eq_of_tgt ((Grp.isZero_trivial _).of_iso e) _ _
  change j ≫ M.inclusion = i at hj
  rw [hj₀, zero_comp] at hj
  rw [← hp.1, ← hj, comp_zero]

end Radicals

section Preservation

open Specs.GeometricRadicals (GeometricGroup IsSemisimple IsSmoothConnectedNormal
  IsTrivialSubgroup geometricSolvableRadical)
open private geometricallyConnected_of_connected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private smooth_baseChange_iff connected_baseChange_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private trivial_of_subsingleton_sections rationalSections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

/-- The finite separable scalar algebra splits over the algebraic closure.
Each projection uses the associated embedding of the original scalar field. -/
theorem weilRestrictionPreservesSemisimplicity : WeilRestrictionPreservesSemisimplicity.{u} := by
  intro k K _ _ _ _ _ G W ρ hG
  classical
  let E := AlgebraicClosure k
  let B := E ⊗[k] K
  let I := PrimeSpectrum B
  have : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
  have : IsArtinianRing B := isArtinian_of_tower E inferInstance
  letI : Fintype I := Fintype.ofFinite I
  let e : B ≃ₐ[E] (I → E) := Algebra.FormallyEtale.equivPiOfIsSepClosed E B
  let H := GeometricGroup W
  let J (i : I) := scalarFactor (scalarEmbedding e i) G
  have hJ (i : I) : IsSemisimple (J i) := by
    letI : Algebra K E := (scalarEmbedding e i).toAlgebra
    exact (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := E) G hG.1 hG.2.1).mpr hG
  let q (i : I) : H.val ⟶ (J i).val := groupHomOfPoints H.property.1 (weilProductProjection ρ e i)
  have hq (R : TestAlgebra E) : Function.Bijective (productPointMap q R) := by
    convert weilProductProjection_bijective ρ e R using 2
    rename_i x
    funext i
    dsimp only [productPointMap, q]
    rw [groupHomOfPoints_map]
  let j := productSchemeIso q hq
  obtain ⟨hp, hc, _⟩ := WordDomainGeometry.smoothConnectedGroupFiniteProduct I J
    (fun i => ⟨(hJ i).1,
      by
        have := (hJ i).2.1
        exact GeometricallyConnected.connectedSpace_of_subsingleton (J i).val.X.hom⟩)
  have : IsIso j.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map j.hom))
  have hHs : Smooth H.val.X.hom := by
    rw [← Over.w j.hom]
    have := hp
    infer_instance
  have hHc : ConnectedSpace H.val.X.left := by
    have := hc
    exact j.hom.left.homeomorph.connectedSpace_iff.mpr inferInstance
  have hWs : Smooth W.val.X.hom := (smooth_baseChange_iff (K := E) W.val.X).mp hHs
  have : ConnectedSpace W.val.X.left := (connected_baseChange_iff (K := E) W).mp hHc
  refine ⟨hWs, geometricallyConnected_of_connected W, ?_⟩
  let N := geometricSolvableRadical W
  have hN := GeometricRadicals.geometricSolvableRadicalLargest W
  have hzero (i : I) : N.inclusion ≫ q i = 0 := by
    obtain ⟨s, hs⟩ := productProjectionSection q hq i
    exact semisimple_kills_projected_radical (hJ i) (q i) s hs N hN.1 hN.2.1
  have hincl : N.inclusion = 0 := by
    apply groupHom_ext (closedSubgroupAlgebraicGroup N).property.1
    apply NatTrans.ext
    funext R
    apply GrpCat.ext
    intro x
    apply (hq R).1
    funext i
    change
      ((groupPointsFunctor E).map (q i)).app R
          (((groupPointsFunctor E).map N.inclusion).app R x) =
        ((groupPointsFunctor E).map (q i)).app R
          (((groupPointsFunctor E).map (0 : N.group ⟶ H.val)).app R x)
    simp only [points_map_zero, map_one]
    rw [← GrpCat.comp_apply, ← NatTrans.comp_app, ← Functor.map_comp, hzero i, points_map_zero]
  have := N.isClosedImmersion
  have : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have : Subsingleton (rationalSections (closedSubgroupAlgebraicGroup N).val) := ⟨fun x y => by
    apply (cancel_mono N.inclusion.hom.hom).mp
    simp only [hincl]
    exact (MonObj.comp_one x).trans (MonObj.comp_one y).symm⟩
  exact trivial_of_subsingleton_sections (closedSubgroupAlgebraicGroup N) hN.1.1

open Specs.CharacterDescent (Cocharacter)

theorem weilRestrictionPreservesAnisotropy : WeilRestrictionPreservesAnisotropy.{u} := by
  intro k K _ _ _ _ _ G W ρ hG
  rintro ⟨S, r, hr, ⟨e⟩⟩
  obtain ⟨c, hc⟩ := nontrivial_cocharacter_of_split_subgroup S hr e
  obtain ⟨d, hdc⟩ := restriction_zero_iff k K ρ c
  let a := DiagonalizableGroups.multiplicativeGroupIso K ≪≫ (baseChangeUnitIso (k := k) (K := K)).symm
  let l : Cocharacter G.val := a.hom ≫ d
  have hl : l ≠ 0 := by
    intro h
    apply hc
    apply hdc
    exact (cancel_epi a.hom).mp (by simpa only [comp_zero] using h)
  exact hG (by
    obtain ⟨T, t⟩ := cocharacterImage l hl
    exact ⟨T, 1, Nat.zero_lt_one, t⟩)

end Preservation

end

end LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilGroupStructure
