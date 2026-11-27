import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CompleteIntersectionTangent
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CompleteIntersectionConormal
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedHom
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace

open CategoryTheory Opposite

universe u z

namespace DerivedFormalization.Affine.CompleteIntersectionTangent

open Specs.DerivedFormalization.Affine.CompleteIntersectionTangent
open Specs.DerivedFormalization.Affine.CompleteIntersectionConormal
open Specs.DerivedFormalization.Affine.CotangentComplex (oneObject)
open Specs.DerivedFormalization.Affine.Tensor (regular)
open Specs.DerivedFormalization.DG.HomComplex (component)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)
open Specs.DerivedFormalization.DG.Derived (homotopyCategory)
open CommutativeAlgebraNotes (MarkedDeformation)
open HomologicalComplex

noncomputable section

variable {k : Type u} [Field k] [CharZero k] {s r : ℕ} (f : Fin r → Polynomial k s)

omit [CharZero k] in
private theorem quotientIdeal_eq :
    AdvCommAlg.Koszul.listIdeal (List.ofFn f) =
      Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.J f := by
  unfold AdvCommAlg.Koszul.listIdeal Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.J
  congr 1
  ext p
  exact List.mem_ofFn

attribute [local instance] RingHomInvPair.of_ringEquiv

private def coefficients {d : ℕ} (e : Quotient f ≃ₐ[k] Marked.B f) :
    (Fin d → Quotient f) ≃ₛₗ[(e.toRingEquiv : Quotient f →+* Marked.B f)] (Fin d → Marked.B f) where
  toEquiv := Equiv.piCongrRight (fun _ => e.toEquiv)
  map_add' a b := funext fun i => e.map_add (a i) (b i)
  map_smul' c a := funext fun i => e.map_mul c (a i)

omit [CharZero k] in
private theorem transpose_comm (e : Quotient f ≃ₐ[k] Marked.B f)
    (he : ∀ p, e (quotientClass f p) = Marked.q f p) (a : Fin s → Quotient f) :
    coefficients f e (transposeJacobian f a) = Marked.jacobian f (coefficients f e a) := by
  funext i
  change e (∑ j, quotientClass f (MvPolynomial.pderiv j (f i)) * a j) =
    ∑ j, Marked.q f (MvPolynomial.pderiv j (f i)) * e (a j)
  simp only [map_sum, map_mul, he]

omit [CharZero k] in
private theorem map_range_transpose (e : Quotient f ≃ₐ[k] Marked.B f)
    (he : ∀ p, e (quotientClass f p) = Marked.q f p) :
    (transposeJacobian f).range.map (coefficients f (d := r) e).toLinearMap =
      (Marked.jacobian f).range := by
  ext b
  rw [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨coefficients f e a, (transpose_comm f e he a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := (coefficients f e).surjective a
    exact ⟨_, ⟨a', rfl⟩, transpose_comm f e he a'⟩

/-- The quotient presentations give the same transposed Jacobian on polynomial classes. -/
theorem quotientComparison : QuotientComparisonExists.{u} := by
  intro k _ _ s r f
  let e : Quotient f ≃ₐ[k] Marked.B f := Ideal.quotientEquivAlgOfEq k (quotientIdeal_eq f)
  have he (p : Polynomial k s) : e (quotientClass f p) = Marked.q f p :=
    Ideal.quotientEquivAlgOfEq_mk k (quotientIdeal_eq f) p
  let c := Submodule.Quotient.equiv (transposeJacobian f).range (Marked.jacobian f).range
    (coefficients f e) (map_range_transpose f e he)
  let cₖ : JacobianCokernel f ≃ₗ[k] Marked.JacobianCokernel f :=
    { toAddEquiv := c.toAddEquiv
      map_smul' a x := by
        change c (a • x) = a • c x
        calc
          c (a • x) = c (algebraMap k (Quotient f) a • x) :=
            congrArg c (IsScalarTower.algebraMap_smul (Quotient f) a x).symm
          _ = algebraMap k (Marked.B f) a • c x := by
            rw [map_smulₛₗ]
            exact congrArg (· • c x) (e.commutes a)
          _ = a • c x := IsScalarTower.algebraMap_smul (Marked.B f) a (c x) }
  exact ⟨⟨e, he, cₖ, fun _ => rfl⟩⟩

section Cohomology

open RightDGModule (homotopyClass homotopyClass_surjective toHomotopyCategory)

variable {f}

private def representativeMap {M N : RightDGModule.K (category f)} (g : M ⟶ N) : RightDGModuleHomModel M N :=
  (homotopyClass_surjective g).choose

private theorem representativeMap_class {M N : RightDGModule.K (category f)} (g : M ⟶ N) :
    homotopyClass (representativeMap g) = g :=
  (homotopyClass_surjective g).choose_spec

private theorem representative_homologyMap {M N : RightDGModule.K (category f)}
    {g : RightDGModuleHomModel M N} {a : M ⟶ N}
    (h : homotopyClass g = a) :
    homologyMap ((representativeMap a).app ()) 1 = homologyMap (g.app ()) 1 :=
  RightDGModule.homologyMap_eq_of_homotopyClass_eq
    ((representativeMap_class a).trans h.symm) () 1

private def cohomologyOnHomotopy (f : Fin r → Polynomial k s) :
    RightDGModule.K (category f) ⥤ ModuleCat.{u} k where
  obj M := ((show (quotientCDGA f).Module from M).complex ()).homology 1
  map g := homologyMap ((representativeMap g).app ()) 1
  map_id M := by
    refine (representative_homologyMap (a := 𝟙 M)
      (g := 𝟙 (show (quotientCDGA f).Module from M)) rfl).trans ?_
    apply homologyMap_id
  map_comp g h := by
    have hg : (toHomotopyCategory (category f)).map (representativeMap g) = g :=
      representativeMap_class g
    have hh : (toHomotopyCategory (category f)).map (representativeMap h) = h :=
      representativeMap_class h
    have he : (toHomotopyCategory (category f)).map
        (representativeMap g ≫ representativeMap h) = g ≫ h := by
      rw [Functor.map_comp, hg, hh]
      rfl
    rw [representative_homologyMap he]
    apply homologyMap_comp

private theorem cohomologyOnHomotopy_inverts (f : Fin r → Polynomial k s) :
    (RightDGModule.quasiIsomorphisms (category f)).IsInvertedBy (cohomologyOnHomotopy f) := by
  intro M N g hg
  obtain ⟨a, ha, hq⟩ := hg
  change IsIso (homologyMap ((representativeMap g).app ()) 1)
  rw [representative_homologyMap ha]
  let := hq ()
  infer_instance

private def degreeOneCohomology (h : laws f) : DegreeOneCohomology h := by
  let q := RightDGModule.Q (category f) h
  letI : q.IsLocalization (RightDGModule.quasiIsomorphisms (category f)) :=
    RightDGModule.Q_isLocalization (category f) h
  let F := cohomologyOnHomotopy f
  let hi := cohomologyOnHomotopy_inverts f
  let G := Localization.lift F hi q
  let e := Localization.fac F hi q
  refine ⟨G, fun M => e.app M, ?_⟩
  intro M N a
  have hn := e.hom.naturality ((toHomotopyCategory (category f)).map a)
  change G.map (localizedMap h a) ≫ (e.app N).hom =
    (e.app M).hom ≫ homologyMap ((representativeMap (homotopyClass a)).app ()) 1 at hn
  rw [representative_homologyMap (g := a) rfl] at hn
  exact hn

end Cohomology

open Specs.DerivedFormalization.Affine.CotangentComplex (ComparisonSystem localizedModel)
open Specs.DerivedFormalization.Affine.DerivedHom (algebraCategory)

private theorem derivedHom_computes (h : laws f) :
    ComputesDerivedHom (h := h) (DerivedHom.rHom (algebra f)) :=
  fun p hp hP N => ⟨DerivedHom.modelComparison p hp hP N⟩

/-- Degree-one derived Hom identifies with marked flat deformations over the dual numbers. -/
theorem tangentSpace : TangentSpace.{u,z} := by
  intro k _ _ s r f hreg
  obtain ⟨P, O, T, h, C, E, _, ⟨b, hb⟩, ⟨I⟩⟩ :=
    CompleteIntersectionConormal.conormalModel f hreg
  obtain ⟨J⟩ := quotientComparison f
  obtain ⟨F₀, act, U, R, G₀, hF, ha, hR, hG, e₀, he₀, hz⟩ :=
    CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.tangentSpace.{u,z} f hreg
  let G : MarkedCoordinates.{u,z} f := ⟨F₀, act, U, R, G₀, hF, ha, hR, hG⟩
  let M := (P.model O).module T
  let N := regular (algebra f)
  let H := degreeOneCohomology h
  let : Category (LocalizedCategory h) := derivedCategoryInstance (category f) h
  let F : (LocalizedCategory h)ᵒᵖ × LocalizedCategory h ⥤ LocalizedCategory h :=
    DerivedHom.rHom (algebra f)
  let hP := (C.properties (P.model O)).1
  have hid : RightDGModule.IsQuasiIso (𝟙 M) := fun _ => by
    change QuasiIso (𝟙 _)
    infer_instance
  let a := F.mapIso ((C.derivedIso (P.model O) C.chosen).op.prod
      (Iso.refl (localizedModule h N))) ≪≫
    DerivedHom.modelComparison (A := algebra f) (𝟙 M) hid hP N
  refine ⟨P, O, T, h, C, E, H, F, derivedHom_computes f h, a, b, J, I, G, hb, ?_⟩
  let := G₀.addCommGroup
  let := G₀.addEquiv.module k
  let e₁ := (cohomologyIso H a b).toLinearEquiv
  let e₂ : ordinaryCohomology f ≃ₗ[k] JacobianCokernel f :=
    { toAddEquiv := I.iso.toAddEquiv
      map_smul' c x := by
        let y : (conormalHom f).homology 1 := x
        exact (I.iso.map_smul (algebraMap k (Quotient f) c) y).trans
          (IsScalarTower.algebraMap_smul (Quotient f) c (I.iso y)) }
  let e := (e₁.trans e₂).trans (J.cokernelIso.trans e₀.symm)
  refine ⟨e, ?_, ?_⟩
  · change e₀.symm (J.cokernelIso (e₂ (e₁ 0))) = _
    rw [map_zero, map_zero, map_zero]
    exact e₀.symm_apply_eq.mpr hz.symm
  · intro v
    let w : ordinaryCohomology f := (conormalHom f).homologyπ 1 v
    change G₀ (e (e₁.symm w)) = J.cokernelIso (e₂ w)
    have heval (x : Marked.DeformationClasses.{u,z} f) : G₀ x = e₀ x :=
      congrArg (fun (g : Marked.DeformationClasses.{u,z} f ≃ Marked.JacobianCokernel f) => g x)
        he₀.symm
    calc
      G₀ (e (e₁.symm w)) = e₀ (e (e₁.symm w)) := heval _
      _ = J.cokernelIso (e₂ (e₁ (e₁.symm w))) := e₀.apply_symm_apply _
      _ = J.cokernelIso (e₂ w) := congrArg (fun x => J.cokernelIso (e₂ x)) (e₁.apply_symm_apply w)

end

end DerivedFormalization.Affine.CompleteIntersectionTangent
