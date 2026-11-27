import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentAmitsurModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.OrdinaryStalkComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.OrdinaryDGHomComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.OrdinaryDGTensorComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurRingTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.PerfectHomBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.AmbientDerived
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Exact
import Batteries.Tactic.OpenPrivate

/-! Compatible ordinary and dg models for cotangent descent. -/

open CategoryTheory
open scoped TensorProduct

namespace DerivedFormalization.Affine.CotangentAmitsurModels

open Specs.DerivedFormalization.Affine.CotangentAmitsurModels

noncomputable section

universe u v w t x y

theorem ringPowers : RingPowers.{u,v,w} := by
  intro A B C _ _ _ _ _ _
  have flatPower : ∀ p : ℕ, Module.Flat A (CP A C p) := by
    intro p
    induction p with
    | zero =>
      obtain ⟨e, _, _⟩ := Descent.AmitsurAlgebras.onePower A C
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
    | succ p hp =>
      let : Module.Flat A (CP A C p) := hp
      have : Module.Flat A (CP A C 0) := by
        obtain ⟨e, _, _⟩ := Descent.AmitsurAlgebras.onePower A C
        exact Module.Flat.of_linearEquiv e.toLinearEquiv
      obtain ⟨e, _⟩ := Descent.AmitsurAlgebras.appendPowers A C (p + 1) 1
      exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  refine ⟨inferInstance, ?_, ?_⟩
  · intro p
    let _ := flatPower p
    exact ⟨flatPower p, inferInstance⟩
  · obtain ⟨e, onFactor, natural⟩ := Descent.AmitsurAlgebras.baseChangePowers A C B
    refine ⟨fun p => e (p + 1), ?_, ?_, ?_⟩
    · intro p i b c
      exact onFactor i b c
    · intro p
      exact Subsingleton.elim _ _
    · intro p q f
      exact natural f

section Representatives

open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange (extend scalarExtension)

variable {R : Type v} {S : Type w} {R' S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S']
variable (eR : R ≃+* R') (eS : S ≃+* S')

local instance ringEquivInvPair {T U : Type*} [Ring T] [Ring U] (e : T ≃+* U) :
    RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e

private def algebraSemilinearEquiv (h : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r)) : S ≃ₛₗ[eR.toRingHom] S' where
  __ := eS
  map_smul' r s := by
    change eS (r • s) = eR r • eS s
    simp only [Algebra.smul_def, map_mul, h]


private def sameCarrier (M : ModuleCat.{t} R) :
    M ≃ₛₗ[eR.toRingHom] ((ModuleCat.restrictScalars.{t} eR.symm.toRingHom).obj M) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r z := by
    change r • z = eR.symm (eR r) • z
    rw [RingEquiv.symm_apply_apply]


private def extensionTermEquiv (h : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (M : ModuleCat.{max v w x t} R) :
    (ModuleCat.restrictScalars.{max v w x t} eS.symm.toRingHom).obj ((scalarExtension.{v,w,max v w x t} R S).obj M) ≃ₗ[S']
      (scalarExtension.{x,x,max v w x t} R' S').obj ((ModuleCat.restrictScalars.{max v w x t} eR.symm.toRingHom).obj M) := by
  let e := TensorProduct.congr (algebraSemilinearEquiv eR eS h) (sameCarrier eR M)
  let L : (ModuleCat.restrictScalars.{max v w x t} eS.symm.toRingHom).obj
      ((scalarExtension.{v,w,max v w x t} R S).obj M) →ₗ[S']
      (scalarExtension.{x,x,max v w x t} R' S').obj
        ((ModuleCat.restrictScalars.{max v w x t} eR.symm.toRingHom).obj M) :=
    { toFun := fun z => e z
      map_add' := fun a b => e.map_add a b
      map_smul' := by
        intro r z
        change e (eS.symm r • z) = r • e z
        induction z using TensorProduct.inductionOn with
        | add x y hx hy =>
          calc
            e (eS.symm r • (x + y)) = e (eS.symm r • x + eS.symm r • y) :=
              congrArg e (smul_add (eS.symm r) x y)
            _ = e (eS.symm r • x) + e (eS.symm r • y) := e.map_add _ _
            _ = r • e (x + y) := (congrArg₂ (· + ·) hx hy).trans (by
              rw [e.map_add]
              exact (smul_add r (e x) (e y)).symm)
        | tmul s z =>
          change eS (eS.symm r * s) ⊗ₜ[R'] _ = (r * eS s) ⊗ₜ[R'] _
          rw [map_mul, RingEquiv.apply_symm_apply] }
  exact LinearEquiv.ofBijective L e.bijective

private theorem extensionTermEquiv_tmul (h : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (M : ModuleCat.{max v w x t} R) (s : S) (m : M) :
    extensionTermEquiv.{v,w,t,x} eR eS h M (s ⊗ₜ[R] m) =
      eS s ⊗ₜ[R'] (show (ModuleCat.restrictScalars.{max v w x t} eR.symm.toRingHom).obj M from m) :=
  rfl

private def extensionModuleIso (h : ∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r)) :
    scalarExtension.{v,w,max v w x t} R S ⋙ ModuleCat.restrictScalars.{max v w x t} eS.symm.toRingHom ≅ ModuleCat.restrictScalars.{max v w x t} eR.symm.toRingHom ⋙
      scalarExtension.{x,x,max v w x t} R' S' :=
  NatIso.ofComponents (fun M => (extensionTermEquiv.{v,w,t,x} eR eS h M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
    | tmul s z => rfl)

theorem extensionOfRepresentatives : ExtensionOfRepresentatives.{v,w,t,x} := by
  intro R S R' S' _ _ _ _ _ _ eR eS h
  let a := extensionModuleIso.{v,w,t,x} eR eS h
  refine ⟨NatIso.ofComponents (fun P => HomologicalComplex.Hom.isoOfComponents
    (fun i => a.app (P.X i)) (fun i j _ => (a.hom.naturality (P.d i j)).symm))
    (fun f => HomologicalComplex.hom_ext _ _ (fun i => a.hom.naturality (f.f i))), ?_⟩
  intro P i s z
  exact extensionTermEquiv_tmul.{v,w,t,x} eR eS h (P.X i) s z

end Representatives

section ProjectiveModels

open Specs.DerivedFormalization.Cochains (compValue qValue qhValue quotientValue)
open Specs.DerivedFormalization.CochainModels (isKProjectiveValue)
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange (extend scalarExtension)
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

/-- The finite-projective hypothesis gives K-projectivity in the original-ring
cochain category at any level containing the ring. -/
theorem isKProjectiveOfFiniteProjective {B : Type v} [CommRing B]
    (P : compValue.{max v t} B) (hP : FiniteProjective P) : isKProjectiveValue P := by
  obtain ⟨⟨L, U, hU⟩, _, hPr⟩ := hP
  have hBound : P.IsStrictlyLE U := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact ModuleCat.isZero_iff_subsingleton.mpr (hU i (Or.inr hi))
  have hProjective (i : ℤ) : Projective (P.X i) :=
    (IsProjective.iff_projective (P.X i)).mp (hPr i)
  exact CochainComplex.isKProjective_of_projective P U

/-- Lift a prescribed derived isomorphism as a strict quasi-isomorphism from
the K-projective representative. -/
theorem chainRepresentativeOfIso {B : Type v} [CommRing B] {P L : compValue.{t} B}
    (hP : isKProjectiveValue P) (α : (qValue B).obj P ≅ (qValue B).obj L) :
    ∃ c : P ⟶ L, QuasiIso c ∧ (qValue B).map c = α.hom := by
  obtain ⟨f, hf⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P ((quotientValue B).obj L)).surjective
    α.hom
  have hquot : (quotientValue.{t} B).Full := by
    unfold quotientValue
    infer_instance
  obtain ⟨c, hc⟩ := (quotientValue B).map_surjective f
  have heq : (qValue B).map c = α.hom := by
    change (qhValue B).map ((quotientValue B).map c) = α.hom
    rw [hc]
    exact hf
  have hq : IsIso ((qValue B).map c) := by rw [heq]; infer_instance
  exact ⟨c, (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat B) c).mp hq, heq⟩

/-- Flat ordinary scalar extension on the actual F08a model preserves
quasi-isomorphisms in every degree. -/
theorem quasiIso_extend {B : Type v} {S : Type w} [CommRing B] [CommRing S]
    [Algebra B S] [Module.Flat B S] {P L : compValue.{t} B} (c : P ⟶ L)
    (hc : QuasiIso c) : QuasiIso ((extend B S).map c) := by
  let F := scalarExtension.{v,w,t} B S
  have hF : F.PreservesHomology := by
    apply CategoryTheory.Functor.preservesHomology_of_map_exact
    intro E hE
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker, eq_comm, ← LinearMap.exact_iff] at hE ⊢
    exact Module.Flat.lTensor_exact S (f := E.f.hom) (g := E.g.hom) hE
  exact HomologicalComplex.quasiIso_map_of_preservesHomology c F

theorem isKProjective_extend {B S : Type v} [CommRing B] [CommRing S] [Algebra B S]
    (P : compValue.{max v t} B) (hP : FiniteProjective P) :
    isKProjectiveValue ((extend B S).obj P) := by
  obtain ⟨⟨L, U, hU⟩, _, hPr⟩ := hP
  let Q := (extend.{v,v,max v t} B S).obj P
  have hBound : CochainComplex.IsStrictlyLE Q U := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have := hU i (Or.inr hi)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (S ⊗[B] P.X i)
    infer_instance
  have hProjective (i : ℤ) : Projective (Q.X i) := by
    apply (IsProjective.iff_projective (Q.X i)).mp
    have := hPr i
    change Module.Projective S (S ⊗[B] P.X i)
    infer_instance
  exact CochainComplex.isKProjective_of_projective Q U

/-- Neither boundedness nor the finite-projective terms are changed by the
same-ring coefficient lift used on the original ordinary inputs. -/
theorem finiteProjective_lift {B : Type v} [CommRing B] (P : compValue.{w} B)
    (hP : FiniteProjective P) : FiniteProjective (liftComplex.{v,w,t} P) := by
  obtain ⟨⟨L, U, hz⟩, hFin, hPr⟩ := hP
  let e (i : ℤ) := Specs.DerivedFormalization.CochainCoefficientLift.termEquiv.{t,w} P i
  refine ⟨⟨L, U, fun i hi => ?_⟩, fun i => ?_, fun i => ?_⟩
  · have := hz i hi
    exact (e i).symm.injective.subsingleton
  · have := hFin i
    exact Module.Finite.of_surjective (e i).toLinearMap (e i).surjective
  · have := hPr i
    exact Module.Projective.of_split (e i).symm.toLinearMap (e i).toLinearMap
      (LinearMap.ext fun z => (e i).apply_symm_apply z)

section AmitsurComparisons

open Specs.DerivedFormalization.Descent.PerfectHomBaseChange (changeCoefficients)

/-- The maps that change the coefficient of a pure tensor are natural in
the complex being extended. -/
theorem changeCoefficients_natural {B S T : Type v} [CommRing B] [CommRing S] [CommRing T]
    [Algebra B S] [Algebra B T] (φ : S →ₐ[B] T)
    {P L : compValue.{max v t} B} (c : P ⟶ L) :
    letI : Algebra S T := φ.toRingHom.toAlgebra
    letI : IsScalarTower B S T := IsScalarTower.of_algHom φ
    let RS := Specs.DerivedFormalization.Descent.PerfectHomBaseChange.restrict.{v,v,max v t} B S
    let RT := Specs.DerivedFormalization.Descent.PerfectHomBaseChange.restrict.{v,v,max v t} B T
    RS.map ((extend B S).map c) ≫ changeCoefficients B S T L =
      changeCoefficients B S T P ≫ RT.map ((extend B T).map c) := by
  let : Algebra S T := φ.toRingHom.toAlgebra
  let : IsScalarTower B S T := IsScalarTower.of_algHom φ
  ext1 i
  apply ModuleCat.hom_ext
  refine LinearMap.ext ?_
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  | tmul s z =>
    change (changeCoefficients B S T L).f i (s ⊗ₜ[B] c.f i z) =
      (c.f i).hom.baseChange T ((changeCoefficients B S T P).f i (s ⊗ₜ[B] z))
    rw [Descent.changeCoefficients_apply B S T φ L i s (c.f i z),
      Descent.changeCoefficients_apply B S T φ P i s z]
    rfl

open Specs.DerivedFormalization.Affine.CotangentComplex (Model)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor)

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra A B] [Algebra A C] [IsScalarTower k A B]

/-- Using the same strict map in every column represents the prescribed
isomorphism and commutes with all coefficient maps. -/
theorem compatibleColumns_represents [Module.FaithfullyFlat A C]
    {T : ModuleTensor.{u,max v t} k}
    {M : Model (liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B))}
    {E : RingBridge.{u,v,t} k B} {F : ∀ p : ℕ, RingBridge.{u,v,t} k (BP A B C p)}
    (D : CompatibleColumns T M E F) : D.Represents := by
  intro P hP α
  have hp := isKProjectiveOfFiniteProjective.{v,t} P hP
  obtain ⟨c, hc, hh⟩ := chainRepresentativeOfIso hp α
  refine ⟨c, hp, hc, hh, ?_, ?_⟩
  · intro p
    have : Module.Flat B (BP A B C p) := ((ringPowers A B C).2.1 p).2
    exact ⟨isKProjective_extend.{v,t} P hP, quasiIso_extend c hc⟩
  · intro p q f
    exact changeCoefficients_natural.{v,t} (columnMap (A := A) (B := B) (C := C) f) c

theorem compatibleColumns_originalInputs [Module.FaithfullyFlat A C]
    {T : ModuleTensor.{u,max v (max u w x t)} k}
    {M : Model (liftedBaseMap.{u,v,max u w x t} (k := k) (A := A) (B := B))}
    {E : RingBridge.{u,v,max u w x t} k B} {F : ∀ p : ℕ, RingBridge.{u,v,max u w x t} k (BP A B C p)}
    (D : CompatibleColumns T M E F) : CompatibleColumns.OriginalInputs.{u,v,w,t,x} D := by
  intro P₀ X₀ hp₀
  let P := liftComplex.{v,w,max u v x t} P₀
  let X := liftComplex.{v,x,max u v w t} X₀
  have hp : FiniteProjective P := finiteProjective_lift P₀ hp₀
  refine ⟨hp, ?_⟩
  intro α
  obtain ⟨c, hP, hc, hh, hcolumns, _⟩ := compatibleColumns_represents.{u,v,max u w x t} D P hp α
  exact ⟨c, hP, hc, hh, fun p => ⟨(hcolumns p).1, (hcolumns p).2,
    Descent.homBaseChange_isIso B (BP A B C p) P X hp.1 hp.2.1 hp.2.2⟩⟩

end AmitsurComparisons

end ProjectiveModels

section StrictLocalization

open Specs.DerivedFormalization.Cochains (compValue derivedValue homotopyValue qhValue quotientValue)
open Specs.DerivedFormalization.Affine.CotangentComplex (oneObject)
open RightDGModule (homotopyClass toHomotopyCategory homotopyCriterion homotopyClass_surjective
  quasiIsomorphisms quasiIsomorphisms_homotopyClass)
attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R]
variable {G : DGCategory.{u,t,w} k} (F : compValue.{x} R ≌ RightDGModule G)

private abbrev ordinaryQ := HomotopyCategory.quotient (ModuleCat.{x} R) (ComplexShape.up ℤ)

private def compareHomotopy
    (hh : ∀ {X Y : compValue.{x} R} (f g : X ⟶ Y),
      Nonempty (Homotopy f g) ↔ homotopyClass (F.functor.map f) = homotopyClass (F.functor.map g)) :
    homotopyValue.{x} R ⥤ RightDGModule.K G :=
  CategoryTheory.Quotient.lift (_root_.homotopic (ModuleCat.{x} R) (.up ℤ))
    (F.functor ⋙ toHomotopyCategory G) (fun _ _ f g h => (hh f g).mp h)

private theorem compareHomotopy_map
    (hh : ∀ {X Y : compValue.{x} R} (f g : X ⟶ Y),
      Nonempty (Homotopy f g) ↔ homotopyClass (F.functor.map f) = homotopyClass (F.functor.map g))
    {X Y : compValue.{x} R} (f : X ⟶ Y) :
    (compareHomotopy F hh).map (ordinaryQ.map f) = homotopyClass (F.functor.map f) :=
  rfl

private theorem compareHomotopy_equivalence
    (hh : ∀ {X Y : compValue.{x} R} (f g : X ⟶ Y),
      Nonempty (Homotopy f g) ↔ homotopyClass (F.functor.map f) = homotopyClass (F.functor.map g)) :
    (compareHomotopy F hh).IsEquivalence where
  faithful := ⟨by
    rintro ⟨X⟩ ⟨Y⟩ f g e
    obtain ⟨f', rfl⟩ := (ordinaryQ (R := R)).map_surjective f
    obtain ⟨g', rfl⟩ := (ordinaryQ (R := R)).map_surjective g
    rw [compareHomotopy_map, compareHomotopy_map] at e
    obtain ⟨h⟩ := (hh f' g').mpr e
    exact HomotopyCategory.eq_of_homotopy f' g' h⟩
  full := ⟨by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨g, rfl⟩ := homotopyClass_surjective f
    obtain ⟨c, hc⟩ := F.functor.map_surjective g
    refine ⟨ordinaryQ.map c, ?_⟩
    exact (compareHomotopy_map F hh c).trans (congrArg homotopyClass hc)⟩
  essSurj := ⟨fun M => ⟨ordinaryQ.obj (F.inverse.obj M),
    ⟨(toHomotopyCategory G).mapIso (F.counitIso.app M)⟩⟩⟩

private theorem compareHomotopy_quasiIso
    (hh : ∀ {X Y : compValue.{x} R} (f g : X ⟶ Y),
      Nonempty (Homotopy f g) ↔ homotopyClass (F.functor.map f) = homotopyClass (F.functor.map g))
    (hq : ∀ {X Y : compValue.{x} R} (f : X ⟶ Y),
      QuasiIso f ↔ RightDGModule.IsQuasiIso (F.functor.map f))
    {X Y : homotopyValue.{x} R} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso (ModuleCat R) (.up ℤ) f ↔
      quasiIsomorphisms G ((compareHomotopy F hh).map f) := by
  cases X
  cases Y
  obtain ⟨g, rfl⟩ := (ordinaryQ (R := R)).map_surjective f
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff g).trans
    ((hq g).trans (quasiIsomorphisms_homotopyClass (F.functor.map g)).symm)

set_option maxHeartbeats 800000 in
private theorem compareLocalizations
    (hG : Specs.DerivedFormalization.DG.Derived.HomotopyCategoryLaws G)
    (hh : ∀ {X Y : compValue.{x} R} (f g : X ⟶ Y),
      Nonempty (Homotopy f g) ↔ homotopyClass (F.functor.map f) = homotopyClass (F.functor.map g))
    (hq : ∀ {X Y : compValue.{x} R} (f : X ⟶ Y),
      QuasiIso f ↔ RightDGModule.IsQuasiIso (F.functor.map f)) :
    ∃ (H : homotopyValue.{x} R ≌ RightDGModule.K G) (L : derivedValue.{x} R ≌ RightDGModule.D G hG)
      (a : ∀ X : compValue.{x} R, H.functor.obj (ordinaryQ.obj X) ≅ (F.functor.obj X : RightDGModule.K G)),
      (∀ {X Y : compValue.{x} R} (f : X ⟶ Y), H.functor.map (ordinaryQ.map f) ≫ (a Y).hom =
        (a X).hom ≫ homotopyClass (F.functor.map f)) ∧
      Nonempty (qhValue R ⋙ L.functor ≅ H.functor ⋙ RightDGModule.Q G hG) := by
  let W := HomotopyCategory.quasiIso (ModuleCat.{x} R) (.up ℤ)
  let H := compareHomotopy F hh
  have : H.IsEquivalence := compareHomotopy_equivalence F hh
  let Φ : LocalizerMorphism W (quasiIsomorphisms G) :=
    ⟨H, fun _ _ f hf => (compareHomotopy_quasiIso F hh hq f).mp hf⟩
  have : Φ.functor.IsEquivalence := ‹H.IsEquivalence›
  have : Φ.IsLocalizedEquivalence := by
    apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
    intro X Y f hf
    obtain ⟨g, rfl⟩ := homotopyClass_surjective f
    let eX := F.counitIso.app X
    let eY := F.counitIso.app Y
    let g' := eX.hom ≫ g ≫ eY.inv
    obtain ⟨c, hc⟩ := F.functor.map_surjective g'
    have hg : RightDGModule.IsQuasiIso g := (quasiIsomorphisms_homotopyClass g).mp hf
    have hg' : RightDGModule.IsQuasiIso g' := by
      intro a
      let V := RightDGModuleModel.eval (A := G) a
      have h₁ : QuasiIso (V.map g) := hg a
      have h₂ : IsIso (V.map eX.hom) := inferInstance
      have h₃ : IsIso (V.map eY.inv) := inferInstance
      change QuasiIso (V.map g')
      rw [show g' = eX.hom ≫ g ≫ eY.inv from rfl, V.map_comp, V.map_comp]
      infer_instance
    refine ⟨ordinaryQ.obj (F.inverse.obj X), ordinaryQ.obj (F.inverse.obj Y), ordinaryQ.map c,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff c).mpr ((hq c).mpr (hc ▸ hg')), ?_⟩
    refine ⟨Arrow.isoMk ((toHomotopyCategory G).mapIso eX) ((toHomotopyCategory G).mapIso eY) ?_⟩
    change (toHomotopyCategory G).map eX.hom ≫ (toHomotopyCategory G).map g =
      H.map (ordinaryQ.map c) ≫ (toHomotopyCategory G).map eY.hom
    have hm : H.map (ordinaryQ.map c) = (toHomotopyCategory G).map g' :=
      (compareHomotopy_map F hh c).trans (congrArg homotopyClass hc)
    let J := toHomotopyCategory G
    have he : eX.hom ≫ g = g' ≫ eY.hom := by simp [g']
    calc
      _ = J.map (eX.hom ≫ g) := (J.map_comp _ _).symm
      _ = J.map (g' ≫ eY.hom) := congrArg J.map he
      _ = J.map g' ≫ J.map eY.hom := J.map_comp _ _
      _ = _ := congrArg (fun a => a ≫ J.map eY.hom) hm.symm
  have : (qhValue.{x} R).IsLocalization W := by
    change (DerivedCategory.Qh (C := ModuleCat.{x} R)).IsLocalization _
    infer_instance
  have := RightDGModule.Q_isLocalization G hG
  let L := Φ.localizedFunctor (qhValue R) (RightDGModule.Q G hG)
  refine ⟨H.asEquivalence, L.asEquivalence, fun _ => Iso.refl _, ?_, ?_⟩
  · intro X Y f
    let qf : H.obj (ordinaryQ.obj X) ⟶ H.obj (ordinaryQ.obj Y) := homotopyClass (F.functor.map f)
    change H.map (ordinaryQ.map f) ≫ 𝟙 _ = 𝟙 _ ≫ qf
    exact (Category.comp_id _).trans ((compareHomotopy_map F hh f).trans (Category.id_comp qf).symm)
  · exact ⟨(Φ.catCommSq (qhValue R) (RightDGModule.Q G hG)).iso.symm⟩

set_option maxHeartbeats 800000 in
theorem nativeLocalization : NativeLocalization.{u,v} := by
  intro k _ _ R _ _ E h
  let G := oneObject (ordinary k R)
  let F := E.strict.trans (DG.AmbientDerived.strictEquivalence.{u,v,0,0} G).symm
  change ∃ (K₁ : homotopyValue.{v} R ≌ RightDGModule.K G) (D₁ : derivedValue.{v} R ≌ RightDGModule.D G h)
    (a : ∀ X : compValue.{v} R, K₁.functor.obj (ordinaryQ.obj X) ≅ (F.functor.obj X : RightDGModule.K G)),
      (∀ {X Y : compValue.{v} R} (f : X ⟶ Y), K₁.functor.map (ordinaryQ.map f) ≫ (a Y).hom =
        (a X).hom ≫ homotopyClass (F.functor.map f)) ∧
      Nonempty (qhValue R ⋙ D₁.functor ≅ K₁.functor ⋙ RightDGModule.Q G h)
  apply compareLocalizations F h
  · intro X Y f g
    rw [← DG.AmbientDerived.transport_homotopy_iff.{u,v,0,0}]
    change Nonempty (Homotopy f g) ↔
      homotopyClass (E.strict.functor.map f) = homotopyClass (E.strict.functor.map g)
    exact (E.homotopy f g).trans (homotopyCriterion _ _).symm
  · intro X Y f
    exact E.quasiIso f

/-- The common ambient localization is induced by the strict comparison. -/
theorem ambientLocalization {k : Type u} [Field k] [CharZero k] {R : Type v}
    [CommRing R] [Algebra k R] (E : RingBridge.{u,v,t} k R)
    (h : Specs.DerivedFormalization.DG.Derived.HomotopyCategoryLaws
      (oneObject (transported.{u,v,t} k R))) :
    let G := oneObject (transported.{u,v,t} k R)
    ∃ (H : homotopyValue.{max v t} R ≌ RightDGModule.K G)
      (D' : derivedValue.{max v t} R ≌ RightDGModule.D G h)
      (a : ∀ X : compValue.{max v t} R, H.functor.obj (ordinaryQ.obj X) ≅
        (E.strict.functor.obj X : RightDGModule.K G)),
      (∀ {X Y : compValue.{max v t} R} (f : X ⟶ Y),
        H.functor.map (ordinaryQ.map f) ≫ (a Y).hom =
          (a X).hom ≫ homotopyClass (E.strict.functor.map f)) ∧
      Nonempty (qhValue R ⋙ D'.functor ≅ H.functor ⋙ RightDGModule.Q G h) :=
  compareLocalizations E.strict h
    (fun f g => (E.homotopy f g).trans (homotopyCriterion _ _).symm) (fun f => E.quasiIso f)

end StrictLocalization

section RingComparisons

open Specs.DerivedFormalization.Affine.CotangentComplex (oneObject)
open Specs.DerivedFormalization.Affine.OrdinaryDGHomComparison (StrictComparison StrictHom)

variable {k : Type u} [Field k] [CharZero k] {R : Type v} [CommRing R] [Algebra k R]

/-- The strict comparison used as input to the signed Hom construction. -/
private def homInput (E : RingBridge.{u,v,t} k R) : StrictComparison.{u,v,t} k R where
  scalar := E.scalar
  scalar_apply := E.scalar_apply
  strict := E.strict
  terms := E.terms
  terms_natural := E.terms_natural
  action := E.action

private def homComparison (E : RingBridge.{u,v,t} k R) :
    StrictHom (homInput E) where
  iso := E.hom
  evaluation := E.evaluation
  naturality := E.hom_natural

set_option maxHeartbeats 800000 in
private theorem localizesRingBridge (E : RingBridge.{u,v,t} k R)
    (h : Specs.DerivedFormalization.DG.Derived.HomotopyCategoryLaws
      (oneObject (transported.{u,v,t} k R))) : E.Localizes h := by
  obtain ⟨K, D', a, ha, ⟨τ⟩⟩ := ambientLocalization E h
  refine ⟨K, D', a, τ, ha, ?_⟩
  exact OrdinaryDGHomComparison.localizedHomComparison.{u,v,t}
    (homInput E) (homComparison E) h K D' a τ ha (fun X => (E.projective X).mp)

set_option maxHeartbeats 800000 in
theorem ordinaryBridge : OrdinaryBridge.{u,v,t} := by
  intro k _ _ R _ _
  obtain ⟨E⟩ := OrdinaryStalkComparison.comparison.{u,v,t} k R
  let H : StrictComparison.{u,v,t} k R :=
    { scalar := E.scalar
      scalar_apply := E.scalar_apply
      strict := E.strict
      terms := E.terms.app
      terms_natural := fun f => E.terms.hom.naturality f
      action := E.action }
  obtain ⟨I⟩ := OrdinaryDGHomComparison.strictHomComparison.{u,v,t} H
  let F : RingBridge.{u,v,t} k R :=
    { scalar := E.scalar
      scalar_apply := E.scalar_apply
      strict := E.strict
      additive := E.additive
      terms := E.terms.app
      terms_natural := fun f => E.terms.hom.naturality f
      action := E.action
      homotopy := E.homotopy
      quasiIso := fun f => E.quasiIso f
      projective := E.projective
      hom := I.iso
      evaluation := I.evaluation
      hom_natural := I.naturality }
  exact ⟨F, localizesRingBridge F⟩

open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.Affine.Tensor (dgCat ModuleTensor regular)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange (extend)
open Specs.DerivedFormalization.Affine.OrdinaryDGTensorComparison (ExtensionComparison scalarMap)

local instance transportedCommRing :
    CommRing (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instCommRingDegreeZero _

local instance transportedAlgebra :
    Algebra k (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instAlgebraDegreeZero _

private theorem tensorBridge (E : RingBridge.{u,v,t} k R) (T : ModuleTensor.{u,max v t} k)
    (hT : ∀ N, T.Formulas (𝟙 (transported.{u,v,t} k R).toCommDGAlgebra) N) :
    TensorBridge.{u,v,t} E T := by
  obtain ⟨U⟩ := CochainTensorTransport.adequateModel E.scalar.toRingEquiv
  obtain ⟨e, he, _, _⟩ := OrdinaryDGTensorComparison.internalTensor.{u,v,t} E.tensorInput T U hT
  exact ⟨U, e, he, OrdinaryDGTensorComparison.localizedTensor.{u,v,t} E.tensorInput T e
    (fun X => (E.projective X).mp) he⟩

variable {S : Type v} [CommRing S] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

private def extensionBridge (E : RingBridge.{u,v,t} k R) (F : RingBridge.{u,v,t} k S)
    (T : ModuleTensor.{u,max v t} k)
    (hT : T.Formulas (scalarMap.{u,v,t} k R S) (regular (transported.{u,v,t} k S).toCommDGAlgebra)) :
    ExtensionBridge.{u,v,t} E F T :=
  let e := Classical.choice (OrdinaryDGTensorComparison.scalarExtension.{u,v,t}
    E.tensorInput F.tensorInput T hT)
  ⟨e.iso, e.on_tmul⟩

private theorem extension_localized (E : RingBridge.{u,v,t} k R) (F : RingBridge.{u,v,t} k S)
    (T : ModuleTensor.{u,max v t} k) (e : ExtensionBridge.{u,v,t} E F T)
    (hR : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k R)))
    (hS : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k S)))
    (W : Specs.DerivedFormalization.Affine.DerivedTensor.ScalarExtension T
      (scalarMap.{u,v,t} k R S) hR hS) :
    e.Localized E F T hR hS W :=
  OrdinaryDGTensorComparison.localizedExtension.{u,v,t} E.tensorInput F.tensorInput T
    e.tensorInput hR hS W (fun X => (E.projective X).mp)

open private scalarMap_comp tower_square from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.OrdinaryDGTensorComparison

private theorem extension_unit (E : RingBridge.{u,v,t} k R) (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionBridge.{u,v,t} E E T) (hT : T.Comparisons) :
    e.Unit E T :=
  OrdinaryDGTensorComparison.scalarExtensionUnit.{u,v,t} E.tensorInput T e.tensorInput hT

variable {V : Type v} [CommRing V] [Algebra k V] [Algebra R V] [Algebra S V]
  [IsScalarTower k R V] [IsScalarTower k S V] [IsScalarTower R S V]

private theorem extension_composition (E : RingBridge.{u,v,t} k R) (F : RingBridge.{u,v,t} k S)
    (G : RingBridge.{u,v,t} k V) (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionBridge.{u,v,t} E F T) (f : ExtensionBridge.{u,v,t} F G T)
    (g : ExtensionBridge.{u,v,t} E G T)
    (hT : T.Formulas (scalarMap.{u,v,t} k S V) (regular (transported.{u,v,t} k V).toCommDGAlgebra))
    (hc : T.Comparisons) : ExtensionBridge.Composition E F G T e f g :=
  OrdinaryDGTensorComparison.scalarExtensionTower.{u,v,t} E.tensorInput F.tensorInput G.tensorInput T
    e.tensorInput f.tensorInput g.tensorInput hT hc

open Specs.DerivedFormalization.Affine.DerivedTensor (ScalarExtension ExtensionCompositionLaws)
open Tensor (moduleTensorModel)
open private scalarExtensionModel scalarExtensionModel_onProjective_hom baseChange_projective
  baseChangeComp_natural represented localizeMap from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedTensor

/-- Use the same signed tensor for A08, A09b, and the ADerivedTensor
localizations. -/
private theorem extensionFamily
    (h : ∀ U : CommDGAlgebra.{u,v} k, HomotopyCategoryLaws (dgCat U)) :
    ∃ W : ∀ {U U' : CommDGAlgebra.{u,v} k} (a : U ⟶ U'),
        ScalarExtension (moduleTensorModel.{u,v} k) a (h U) (h U'),
      ∀ {U U' U'' : CommDGAlgebra.{u,v} k} (f : U ⟶ U') (g : U' ⟶ U''),
        ExtensionCompositionLaws (moduleTensorModel.{u,v} k) f g (h U) (h U') (h U'')
          (W f) (W g) (W (f ≫ g)) := by
  refine ⟨fun f => scalarExtensionModel f, ?_⟩
  intro U U' U'' f g
  refine ⟨NatIso.ofComponents (Tensor.baseChangeComp f g) (fun a => baseChangeComp_natural f g a),
    DerivedTensor.extensionComp f g, Tensor.baseChangeComp_pure f g, ?_⟩
  intro P hP
  refine ⟨baseChange_projective f P hP, ?_⟩
  let := Specs.DerivedFormalization.DG.DerivedKProjective.derivedCategoryInstance (dgCat U') (h U')
  let := Specs.DerivedFormalization.DG.DerivedKProjective.derivedCategoryInstance (dgCat U'') (h U'')
  change (DerivedTensor.extensionComp f g).hom.app (represented P) ≫
      ((scalarExtensionModel (f ≫ g)).onProjective P hP).hom =
    (DerivedTensor.derivedExtension g).map ((scalarExtensionModel f).onProjective P hP).hom ≫
      ((scalarExtensionModel g).onProjective ((Tensor.baseChange f).obj P)
        (baseChange_projective f P hP)).hom ≫
      localizeMap (Tensor.baseChangeComp f g P).hom
  rw [scalarExtensionModel_onProjective_hom (f ≫ g) P hP,
    scalarExtensionModel_onProjective_hom f P hP,
    scalarExtensionModel_onProjective_hom g ((Tensor.baseChange f).obj P) (baseChange_projective f P hP)]
  exact DerivedTensor.extensionComp_onProjective f g P hP

set_option backward.isDefEq.respectTransparency false in
private theorem extension_derivedComposition (E : RingBridge.{u,v,t} k R) (F : RingBridge.{u,v,t} k S)
    (G : RingBridge.{u,v,t} k V) (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionBridge.{u,v,t} E F T) (f : ExtensionBridge.{u,v,t} F G T)
    (g : ExtensionBridge.{u,v,t} E G T)
    (h : ∀ U : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat U))
    (W : ∀ {U U' : CommDGAlgebra.{u,max v t} k} (a : U ⟶ U'), ScalarExtension T a (h U) (h U'))
    (hs : T.Formulas (scalarMap.{u,v,t} k S V) (regular (transported.{u,v,t} k V).toCommDGAlgebra))
    (hlaw : ∀ {U U' U'' : CommDGAlgebra.{u,max v t} k} (r : U ⟶ U') (s : U' ⟶ U''),
      ExtensionCompositionLaws T r s (h U) (h U') (h U'') (W r) (W s) (W (r ≫ s))) :
    ExtensionBridge.DerivedComposition E F G T e f g h W := by
  obtain ⟨a,b,ha,hb⟩ := hlaw (scalarMap.{u,v,t} k R S) (scalarMap.{u,v,t} k S V)
  refine ⟨scalarMap_comp, a, b, ?_, hb⟩
  intro X
  exact tower_square E.tensorInput F.tensorInput G.tensorInput T
    e.tensorInput f.tensorInput g.tensorInput hs X _ (ha _)

end RingComparisons

section Columns

open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.Affine.CotangentComplex (Model LiftedModel)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor dgCat regular term restrictFunctor)
open Specs.DerivedFormalization.Affine.OrdinaryDGTensorComparison (scalarMap)
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange (extend)
open Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram (Diagram)
open Tensor (moduleTensorModel)

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra A B] [Algebra A C] [IsScalarTower k A B]

set_option backward.isDefEq.respectTransparency false in
private theorem compatibleHomColumns
    (E : RingBridge.{u,v,t} k B) (F : ∀ p : ℕ, RingBridge.{u,v,t} k (BP A B C p)) :
    Nonempty (CompatibleHomColumns E F) := by
  let : Algebra k C := ((algebraMap A C).comp (algebraMap k A)).toAlgebra
  let : IsScalarTower k A C := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨H⟩ := OrdinaryDGHomComparison.amitsurHomComparison.{u,v,t} (A := A) (C := C)
    (homInput E) (homComparison E) (fun p => homInput (F p)) (fun p => homComparison (F p))
  exact ⟨{
    augmentation := H.augmentation
    augmentation_ordinary := H.augmentation_ordinary
    map := H.map
    map_id := H.map_id
    map_comp := H.map_comp
    augmentation_comp := H.augmentation_comp
    ordinary := H.map_ordinary
    evaluation := H.map_evaluation
    baseChangeIso := fun P X hP p =>
      Descent.homBaseChange_isIso B (BP A B C p) P X hP.1 hP.2.1 hP.2.2 }⟩

set_option backward.isDefEq.respectTransparency false in
private theorem coherentExtensions
    {M : Model (liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B))}
    {E : RingBridge.{u,v,t} k B} {F : ∀ p : ℕ, RingBridge.{u,v,t} k (BP A B C p)}
    (D : CompatibleColumns (moduleTensorModel.{u,max v t} k) M E F) : D.CoherentExtensions := by
  let T := moduleTensorModel.{u,max v t} k
  have comparisons : T.Comparisons := Tensor.moduleTensor_comparisons
  refine ⟨?_, ?_, ?_⟩
  · let e := extensionBridge E E T (Tensor.moduleTensor_formulas _ _)
    exact ⟨e, extension_unit E T e comparisons⟩
  · intro p
    let e := extensionBridge (F p) (F p) T (Tensor.moduleTensor_formulas _ _)
    exact ⟨e, extension_unit (F p) T e comparisons⟩
  · intro h
    obtain ⟨W, hw⟩ := extensionFamily.{u,max v t} h
    refine ⟨W, ?_, ?_⟩
    · intro p
      exact extension_localized E (F p) T (D.extension p) (h _) (h _) (W (scalarMap.{u,v,t} k B (BP A B C p)))
    · intro p q f
      let φ : BP A B C p →ₐ[B] BP A B C q := columnMap f
      let : Algebra (BP A B C p) (BP A B C q) := φ.toRingHom.toAlgebra
      let : IsScalarTower B (BP A B C p) (BP A B C q) := IsScalarTower.of_algHom φ
      let : IsScalarTower k (BP A B C p) (BP A B C q) :=
        IsScalarTower.of_algHom (φ.restrictScalars k)
      let e := extensionBridge (F p) (F q) T (Tensor.moduleTensor_formulas _ _)
      refine ⟨e, ?_, ?_, ?_⟩
      · exact extension_composition E (F p) (F q) T (D.extension p) e (D.extension q)
          (Tensor.moduleTensor_formulas _ _) comparisons
      · exact extension_localized (F p) (F q) T e (h _) (h _)
          (W (scalarMap.{u,v,t} k (BP A B C p) (BP A B C q)))
      · exact extension_derivedComposition E (F p) (F q) T (D.extension p) e (D.extension q) h W
          (Tensor.moduleTensor_formulas _ _) hw

set_option backward.isDefEq.respectTransparency false in
private def ofFlatColumn
    {T : ModuleTensor.{u,max v t} k}
    {M : Model (liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B))}
    (p : ℕ) (D : Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram.Column (C := C) T M p) :
    FlatColumn (C := C) T M p :=
  ⟨D.model, D.resolutionMap, D.resolutionPushout, D.ordinaryPushout, D.augmentation_comm,
    D.comparison, D.symbols⟩

private def ofFlatColumnMap
    {T : ModuleTensor.{u,max v t} k}
    {M : Model (liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B))}
    {p q : ℕ}
    {P : Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram.Column (C := C) T M p}
    {Q : Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram.Column (C := C) T M q}
    {f : Fin (p + 1) → Fin (q + 1)}
    (D : Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram.ColumnMap P Q f) :
    FlatColumnMap (ofFlatColumn p P) (ofFlatColumn q Q) f :=
  ⟨D.algebraMap, D.fromResolution, D.fromBase, D.overTarget, D.cotangentMap, D.symbols⟩

open Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram (targetMap ColumnMap)
open private transportedMap_scalar from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.OrdinaryDGTensorComparison

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
private def assembleColumns
    {T : ModuleTensor.{u,max v t} k}
    {M : Model (liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B))}
    (E : RingBridge.{u,v,t} k B) (F : ∀ p : ℕ, RingBridge.{u,v,t} k (BP A B C p))
    (D : Diagram (C := C) T M)
    (forms : ∀ {U V : CommDGAlgebra.{u,max v t} k} (f : U ⟶ V) (N : V.Module), T.Formulas f N) :
    CompatibleColumns T M E F := by
  let L := E.strict.inverse.obj (M.module T)
  let γ := E.strict.counitIso.app (M.module T)
  let e (p : ℕ) := extensionBridge E (F p) T (forms _ _)
  refine {
    L := L
    global := γ
    column := fun p => ofFlatColumn p (D.column p)
    extension := e
    coface := fun f => ofFlatColumnMap (D.map f)
    coface_id := D.resolutionId
    coface_comp := D.resolutionComp
    natural := ?_ }
  intro p q f i s x
  let bp (j : ℕ) : (transported.{u,v,t} k B).toCommDGAlgebra ⟶
      (transported.{u,v,t} k (BP A B C j)).toCommDGAlgebra :=
    transportedMap (bpMap (k := k) (A := A) (B := B) (C := C) j)
  let φ : BP A B C p →ₐ[B] BP A B C q := columnMap f
  let d : (transported.{u,v,t} k (BP A B C p)).toCommDGAlgebra ⟶
        (transported.{u,v,t} k (BP A B C q)).toCommDGAlgebra := targetMap f
  let w := (γ.hom.app ()).f i ((E.terms L).hom.f i x)
  let η (j : ℕ) :=
    (e j).iso.app L ≪≫ (T.baseChange (bp j)).mapIso γ ≪≫ (D.column j).comparison
  let z (j : ℕ) (b : BP A B C j) :=
    T.tmul (bp j) (N := regular _) i 0 i (add_zero i) w ((F j).scalar b)
  have pure (j : ℕ) (b : BP A B C j) :
      ((η j).hom.app ()).f i (((F j).terms (extColumn L j)).hom.f i (b ⊗ₜ[B] x)) =
        (((D.column j).comparison.hom.app ()).f i) (z j b) := by
    change (((D.column j).comparison.hom.app ()).f i)
      ((((T.baseChange (bp j)).map γ.hom).app ()).f i
        ((((e j).iso.app L).hom.app ()).f i
          (((F j).terms (extColumn L j)).hom.f i (b ⊗ₜ[B] x)))) = _
    have h := (e j).on_tmul L i b x
    exact congrArg (((D.column j).comparison.hom.app ()).f i : _ → _)
      ((congrArg (fun y => (((T.baseChange (bp j)).map γ.hom).app ()).f i y) h).trans
        ((forms (bp j) (regular _)).first γ.hom i 0 i (add_zero i)
          ((E.terms L).hom.f i x) ((F j).scalar b)))
  have hs : (d.chainMap.f 0) ((F p).scalar s) = (F q).scalar (φ s) :=
    transportedMap_scalar (F p).tensorInput (F q).tensorInput (φ.restrictScalars k) s
  have hz : (((D.map f).extensionMap.app ()).f i) (z p s) = z q (φ s) := by
    refine (D.extensionPures f i 0 i (add_zero i) w ((F p).scalar s)).trans ?_
    exact congrArg (fun r => T.tmul (bp q) (N := regular _) i 0 i (add_zero i) w r) hs
  have hsq : (D.map f).extensionMap ≫ (restrictFunctor d).map (D.column q).comparison.hom =
      (D.column p).comparison.hom ≫ (D.map f).cotangentMap := by
    let R := restrictFunctor d
    have h := (D.map f).naturality
    change (D.column p).associator.hom ≫ (D.map f).normalizedMap ≫
      R.map ((D.column q).associator.inv ≫ (D.column q).comparison.hom) = _ at h
    change ((D.column p).associator.hom ≫ (D.map f).normalizedMap ≫
      R.map (D.column q).associator.inv) ≫ R.map (D.column q).comparison.hom = _
    rw [R.map_comp] at h
    simpa only [Category.assoc] using h
  have hsq' : ((D.map f).cotangentMap.app ()).f i (((D.column p).comparison.hom.app ()).f i (z p s)) =
    (((D.column q).comparison.hom.app ()).f i) (z q (φ s)) :=
    (congrArg (fun (g : _ ⟶ _) => (g.app ()).f i (z p s)) hsq).symm.trans
      (congrArg (((D.column q).comparison.hom.app ()).f i : _ → _) hz)
  have hφ : (ordinaryColumnMap (A := A) (C := C) L f).f i (s ⊗ₜ[B] x) = φ s ⊗ₜ[B] x :=
    Descent.changeCoefficients_apply B (BP A B C p) (BP A B C q) φ L i s x
  exact (congrArg (fun y => ((D.map f).cotangentMap.app ()).f i y) (pure p s)).trans
    (hsq'.trans ((pure q (φ s)).symm.trans
      (congrArg (fun y => ((η q).hom.app ()).f i
        (((F q).terms (extColumn L q)).hom.f i y)) hφ.symm)))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem commonCotangentModels : CommonCotangentModels.{u,v,w,t,x} := by
  intro k _ _ A B C _ _ _ _ _ _ _ _
  intro _ T₀ hT₀ M
  let T := moduleTensorModel.{u,max u v w x t} k
  obtain ⟨U⟩ := CotangentComplex.modelEnlargement.{u,v,max u w x t}
    M T₀ T hT₀ Tensor.moduleTensor_formulas
  obtain ⟨E, hE⟩ := ordinaryBridge.{u,v,max u w x t} k B
  have ex (p : ℕ) := ordinaryBridge.{u,v,max u w x t} k (BP A B C p)
  choose F hF using ex
  let : Algebra k C := ((algebraMap A C).comp (algebraMap k A)).toAlgebra
  let : IsScalarTower k A C := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨D⟩ := FlatCotangentAmitsurDiagram.flatCotangentDiagram.{u,v,max u w x t}
    (C := C) T Tensor.moduleTensor_formulas U.model
  let D' := assembleColumns E F D Tensor.moduleTensor_formulas
  exact ⟨T, U, E, F, Tensor.moduleTensor_formulas, hE, hF,
    tensorBridge E T (Tensor.moduleTensor_formulas _),
    fun p => tensorBridge (F p) T (Tensor.moduleTensor_formulas _),
    compatibleHomColumns E F, D', compatibleColumns_represents D', coherentExtensions D',
    compatibleColumns_originalInputs.{u,v,w,t,x} D'⟩

end Columns

section MixedRings

open Specs.DerivedFormalization.Descent.AmitsurRingTransport
  (changeDerivedRepresentative quotientSquare)

set_option maxHeartbeats 800000 in
theorem ringDiagramTransport : RingDiagramTransport.{u,v,t,x,y} := by
  intro k _ _ A B C _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨A', B', C', eA, eB, eC, f, g, hf, hg, h⟩ :=
    Descent.AmitsurRingTransport.ringDiagramTransport.{u,v,t,x,y,0,0} k A B C
  refine ⟨A', B', C', eA, eB, eC, f, g, hf, hg, ?_⟩
  let : Algebra A' B' := f.toRingHom.toAlgebra
  let : Algebra A' C' := g.toRingHom.toAlgebra
  let : IsScalarTower k A' B' := IsScalarTower.of_algHom f
  let : IsScalarTower k A' C' := IsScalarTower.of_algHom g
  obtain ⟨hflat, eCP, eBP, hfactor, _, _, htensor, hbase, _, hcoface, ⟨D⟩⟩ := h
  refine ⟨hflat, eCP, eBP, hfactor, htensor, hbase, hcoface, ?_⟩
  have := D.localizationEquivalence
  exact ⟨{
    d := (changeDerivedRepresentative eB.toRingEquiv).asEquivalence
    quotient := quotientSquare eB.toRingEquiv
    originalModel := D.originalModel
    extendIso := D.extendIso
    extend_tmul := D.extend_tmul
    homIso := D.homIso
    hom_evaluation := D.hom_evaluation
    homColumnIso := D.homColumnIso
    homColumn_evaluation := D.homColumn_evaluation
    augmentation := D.augmentation
    cofaces := D.cofaces }⟩

open Specs.DerivedFormalization.Cochains (compValue qValue quotientValue)
open Specs.DerivedFormalization.Affine.CotangentComplex (oneObject)
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange (extend)
attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
/-- The mixed-ring comparison uses the cotangent model and its column
identifications from the assembled strict diagram. -/
theorem originalCotangentComparison : OriginalCotangentComparison.{u,v,w,t,y} := by
  intro k _ _ A B C _ _ _ _ _ _ _ _ R _ S _ _
  intro e eS f O T M E F D h
  let G := oneObject (transported.{u,v,max w y t} k B)
  let Q := RightDGModule.Q G h
  obtain ⟨L, c, aL, haL⟩ := O.originalModel D.L
  obtain ⟨K, I, a, ha, ⟨τ⟩⟩ := ambientLocalization E h
  let l := I.functor.mapIso aL ≪≫ τ.app ((quotientValue B).obj D.L) ≪≫
    Q.mapIso (a D.L) ≪≫ Q.mapIso ((RightDGModule.toHomotopyCategory G).mapIso D.global)
  refine ⟨L, c, K, I, a, τ, l, ha, ?_, ?_, ?_⟩
  · change l.hom = _
    simp only [l, Iso.trans_hom, Functor.mapIso_hom, haL]
    rfl
  · intro p
    let Gp := extend.{v,v,max v w y t} B (BP A B C p)
    exact ⟨(F p).strict.functor.mapIso ((O.extendIso p).app L ≪≫ Gp.mapIso c) ≪≫
      D.identification p, rfl⟩
  · intro P hP α
    have hprojective := isKProjectiveOfFiniteProjective.{y,max v w t} P hP
    obtain ⟨g, hg, hα⟩ := chainRepresentativeOfIso hprojective α
    exact ⟨g, hprojective, hg, hα⟩

end MixedRings

end

end DerivedFormalization.Affine.CotangentAmitsurModels
