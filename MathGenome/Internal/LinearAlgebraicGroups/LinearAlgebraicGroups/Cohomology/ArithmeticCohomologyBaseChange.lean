import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ClosedImmersionCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.FlatPullback
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.AffineAcyclicity
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ArithmeticCohomologyBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped TensorProduct ChangeOfRings
open CategoryTheory.Preadditive TopologicalSpace

set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

namespace LinearAlgebraicGroups.Cohomology.ArithmeticCohomologyBaseChange

noncomputable section

open Specs.ArithmeticCohomologyBaseChange
open Specs.OrderedCechComparison

/-- A quasi-compact separated scheme has an ordered finite affine cover
whose nonempty finite intersections are affine. -/
theorem finiteAffineCover {X : Scheme.{u}} [CompactSpace X]
    [IsSeparated (terminal.from X)] :
    ∃ (Idx : Type u) (_ : LinearOrder Idx) (_ : Fintype Idx) (U : Idx → X.Opens),
      IsFiniteAffineCover U := by
  classical
  let cover := X.affineCover.finiteSubcover
  let U : cover.I₀ → X.Opens := fun i => (cover.f i).opensRange
  have ha (i : cover.I₀) : IsAffineOpen (U i) := isAffineOpen_opensRange (cover.f i)
  let e := Fintype.equivFin cover.I₀
  let ord : LinearOrder cover.I₀ := LinearOrder.lift' e e.injective
  refine ⟨cover.I₀, ord, inferInstance, U, cover.iSup_opensRange, ?_⟩
  intro n e
  exact IsAffineOpen.iInf (fun i : Fin (n + 1) => ha (e i))

/-- The preimage of an affine open in an arbitrary affine-base change is affine. -/
theorem isAffineOpen_fibrePreimage {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : SchemeOverRing A) {U : X.left.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (fibreProjection φ X ⁻¹ᵁ U) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have : IsAffineHom (fibreProjection φ X) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback X.hom g).flip (isAffineHom_of_isAffine g)
  exact hU.preimage (fibreProjection φ X)

section AffineFibre

variable {A B : Type u} [CommRing A] [CommRing B]
  (φ : A →+* B) (X : SchemeOverRing A)

local notation "Y" => (changeBase φ).obj X
local notation "j" => fibreProjection φ X

private theorem appLE_top_hom {A : Type u} [CommRing A] (X : SchemeOverRing A)
    (U : X.left.Opens) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ X.hom.appLE ⊤ U (by simp) =
      CommRingCat.ofHom (groundRingHomOpen X U) := by
  apply CommRingCat.hom_ext
  change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    X.hom.appTop ≫ X.left.presheaf.map U.leTop.op).hom = _
  rw [← Category.assoc]
  rfl

/-- The base-change square on the rings of sections of an affine open and its
inverse image. All four ring maps are induced by the scheme morphisms. -/
theorem affineFibreRingPushout {U : X.left.Opens} (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (groundRingHomOpen X U)) (CommRingCat.ofHom φ)
      ((j).app U) (CommRingCat.ofHom (groundRingHomOpen Y (j ⁻¹ᵁ U))) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have H : IsPullback j (Y).hom X.hom g := IsPullback.of_hasPullback X.hom g
  have hV : j ⁻¹ᵁ U = j ⁻¹ᵁ U ⊓ (Y).hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of B)).Opens) := by
    simp
  have hi := isIso_pushoutSection_of_isAffineOpen H
    (UT := ⊤) (US := ⊤) (by simp) (by simp) hV
    (isAffineOpen_top (Spec (CommRingCat.of A))) (isAffineOpen_top (Spec (CommRingCat.of B))) hU
  have hp := (isIso_pushoutSection_iff H (UT := ⊤) (US := ⊤)
    (by simp) (by simp) hV).mp hi
  refine hp.of_iso' (Scheme.ΓSpecIso (CommRingCat.of A)).symm (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of B)).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using appLE_top_hom X U
  · change (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        g.appLE ⊤ (g ⁻¹ᵁ ⊤) le_rfl = _
    rw [g.appLE_eq_app]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (j).appLE_eq_app
  · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
      appLE_top_hom (Y) (j ⁻¹ᵁ U)

/-- Flatness of the structural morphism gives flatness of the coordinate ring
of every affine open over the base. -/
theorem flat_groundRingHomOpen [Flat X.hom] {U : X.left.Opens} (hU : IsAffineOpen U) :
    (groundRingHomOpen X U).Flat := by
  have h := X.hom.flat_appLE (isAffineOpen_top (Spec (CommRingCat.of A))) hU (by simp)
  rw [← CommRingCat.hom_ofHom (groundRingHomOpen X U), ← appLE_top_hom, CommRingCat.hom_comp]
  exact (RingHom.Flat.of_bijective (f := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv)).comp h

end AffineFibre

/-- Flat scalar extension commutes with homology of a cochain complex. -/
def flatExtensionHomologyIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat) (C : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars.{u,u,u} φ).obj (C.homology n) ≅
      ((ModuleCat.extendScalars.{u,u,u} φ).mapHomologicalComplex _ |>.obj C).homology n := by
  let E := ModuleCat.extendScalars.{u,u,u} φ
  letI : PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  change (E).obj ((C.sc n).homology) ≅ ((C.sc n).map E).homology
  exact ((C.sc n).mapHomologyIso E).symm

section Flat
/-- Tensoring a principal reduction sequence identifies the quotient by the
scalar with the extension of scalars. -/
theorem moduleReduction
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] (a : A)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {a}) :
    Function.Exact (a • · : M → M) (fun x : M => (1 : B) ⊗ₜ[A] x) ∧
      Function.Surjective (fun x : M => (1 : B) ⊗ₜ[A] x) := by
  let m : A →ₗ[A] A := LinearMap.mulLeft A a
  let q : A →ₗ[A] B := Algebra.linearMap A B
  have he : Function.Exact m q := by
    intro x
    change algebraMap A B x = 0 ↔ ∃ y, a * y = x
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  let e := TensorProduct.lid A M
  have hm (x : M) : (m.rTensor M) (e.symm x) = e.symm (a • x) := by
    change (m.rTensor M) ((TensorProduct.lid A M).symm x) =
      (TensorProduct.lid A M).symm (a • x)
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul]
    change (a * 1) ⊗ₜ[A] x = (1 : A) ⊗ₜ[A] (a • x)
    rw [mul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hq (x : M) : (q.rTensor M) (e.symm x) = (1 : B) ⊗ₜ[A] x := by
    change (q.rTensor M) ((TensorProduct.lid A M).symm x) = _
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul]
    change (algebraMap A B 1) ⊗ₜ[A] x = _
    rw [map_one]
  have hqs : Function.Surjective q := hsurj
  have hr := rTensor_exact M he hqs
  constructor
  · intro x
    change (1 : B) ⊗ₜ[A] x = 0 ↔ ∃ y : M, a • y = x
    rw [← hq, hr]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := e.symm.surjective y
      exact ⟨z, e.symm.injective ((hm z).symm.trans hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, hm y⟩
  · intro z
    obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective M hqs z
    obtain ⟨x, rfl⟩ := e.symm.surjective y
    exact ⟨x, (hq x).symm.trans hy⟩

end Flat

section Cech
variable {A : Type u} [CommRing A] {D : Type v} [CompleteLattice D]
  {I : Type u} [Preorder I] {U : I → D}
  {P P' : Dᵒᵖ ⥤ ModuleCat.{u} A}

/-- Exactness of reduction on the tuple intersections gives a short exact
sequence of the ordered Čech complexes. -/
theorem shortExactCechReduction (a : A) (q : P ⟶ P')
    (hinj : ∀ (n : ℕ) (e : Fin (n + 1) ↪o I),
      Function.Injective (fun x : P.obj (op (tupleOpen U e)) => a • x))
    (hex : ∀ (n : ℕ) (e : Fin (n + 1) ↪o I),
      Function.Exact (fun x : P.obj (op (tupleOpen U e)) => a • x)
        (q.app (op (tupleOpen U e))))
    (hsurj : ∀ (n : ℕ) (e : Fin (n + 1) ↪o I),
      Function.Surjective (q.app (op (tupleOpen U e)))) :
    ∃ hq : (a • 𝟙 (cechComplex U P)) ≫ cechMap U q = 0,
      (ShortComplex.mk (a • 𝟙 (cechComplex U P)) (cechMap U q) hq).ShortExact := by
  classical
  have hzero : (a • 𝟙 (cechComplex U P)) ≫ cechMap U q = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    change q.app (op (tupleOpen U e)) (a • x e) = 0
    exact (hex n e).apply_apply_eq_zero _
  refine ⟨hzero, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change (fun e => q.app (op (tupleOpen U e)) (x e)) = 0 ↔
      ∃ y : (cechComplex U P).X n, (fun e => a • y e) = x
    constructor
    · intro h
      have hpre e := (hex n e _).mp (congrFun h e)
      exact ⟨fun e => (hpre e).choose, funext fun e => (hpre e).choose_spec⟩
    · rintro ⟨y, rfl⟩
      exact funext fun e => (hex n e).apply_apply_eq_zero (y e)
  · intro x y h
    exact funext fun e => hinj n e (congrFun h e)
  · intro x
    exact ⟨fun e => (hsurj n e (x e)).choose, funext fun e => (hsurj n e (x e)).choose_spec⟩

end Cech

section Algebra
variable {A : Type u} [CommRing A]

private theorem homologyMap_mul (C : CochainComplex (ModuleCat.{u} A) ℕ) (a : A) (i : ℕ) :
    homologyMap (a • 𝟙 C) i = a • 𝟙 (C.homology i) := by
  change (ShortComplex.homologyFunctor (ModuleCat A)).map
      ((shortComplexFunctor (ModuleCat A) (.up ℕ) i).map (a • 𝟙 C)) = _
  rw [show (shortComplexFunctor (ModuleCat A) (.up ℕ) i).map (a • 𝟙 C) =
      a • 𝟙 (C.sc i) by
    ext <;> rfl]
  change _ = a • 𝟙 ((ShortComplex.homologyFunctor (ModuleCat A)).obj (C.sc i))
  rw [Functor.map_smul]
  exact congrArg (a • ·) ((ShortComplex.homologyFunctor (ModuleCat A)).map_id (C.sc i))

end Algebra


section Reduction

variable {A : Type u} [CommRing A]
variable {H H' K : ModuleCat.{u} A}

/-- Factor the middle two maps in the long exact sequence through the
multiplication cokernel and kernel. -/
theorem reductionOfLongExact (a : A) (r : H ⟶ K) (δ : K ⟶ H')
    (hr : LinearMap.range (a • 𝟙 H : H ⟶ H).hom = LinearMap.ker r.hom)
    (hrδ : Function.Exact r δ)
    (hδ : LinearMap.range δ.hom = LinearMap.ker (a • 𝟙 H' : H' ⟶ H').hom) :
    ∃ (f : H ⧸ LinearMap.range (a • 𝟙 H : H ⟶ H).hom →ₗ[A] K)
      (g : K →ₗ[A] LinearMap.ker (a • 𝟙 H' : H' ⟶ H').hom),
      (∀ x : H, f ((LinearMap.range (a • 𝟙 H : H ⟶ H).hom).mkQ x) = r x) ∧
      (∀ y : K, (g y).val = δ y) ∧
      Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g := by
  let m : H ⟶ H := a • 𝟙 H
  let m' : H' ⟶ H' := a • 𝟙 H'
  let f := (LinearMap.range m.hom).liftQ r.hom hr.le
  let g := δ.hom.codRestrict (LinearMap.ker m'.hom) fun x => hδ.le ⟨x, rfl⟩
  have hf : ∀ x : H, f ((LinearMap.range m.hom).mkQ x) = r x := fun _ => rfl
  refine ⟨f, g, hf, fun _ => rfl, ?_, ?_, ?_⟩
  · apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := (LinearMap.range m.hom).mkQ_surjective y
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [hr]
    exact hy
  · intro y
    change (g y = 0) ↔ _
    rw [← Subtype.val_inj]
    change (δ y = 0) ↔ _
    rw [hrδ y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(LinearMap.range m.hom).mkQ x, hf x⟩
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := (LinearMap.range m.hom).mkQ_surjective z
      exact ⟨x, (hf x).symm.trans hz⟩
  · intro x
    obtain ⟨y, hy⟩ := hδ.ge x.property
    exact ⟨y, Subtype.ext hy⟩

end Reduction

section AffineSpectrum

variable {R S : CommRingCat.{u}} (ρ : R ⟶ S)

local notation "j" => Spec.map ρ
local notation "P" => Scheme.Modules.pushforward j
local notation "L" => Scheme.Modules.pullback j
local notation "ΓR" => moduleSpecΓFunctor (R := R)
local notation "ΓS" => moduleSpecΓFunctor (R := S)
local notation "η" => (Scheme.Modules.pullbackPushforwardAdjunction j).unit
local notation "β" => FlatCohomology.affinePushforwardSections ρ
local notation "E" => ModuleCat.extendScalars ρ.hom
local notation "adj" => ModuleCat.extendRestrictScalarsAdj ρ.hom

/-- The adjoint to the restriction of sections along a map of spectra. -/
def spectrumSectionsBaseChangeMap (F : (Spec R).Modules) :
    (E).obj ((ΓR).obj F) ⟶ (ΓS).obj ((L).obj F) :=
  ((adj).homEquiv _ _).symm ((ΓR).map ((η).app F) ≫ (β).hom.app ((L).obj F))

private lemma spectrumSectionsBaseChangeMap_natural
    {F G : (Spec R).Modules} (f : F ⟶ G) :
    (E).map ((ΓR).map f) ≫ spectrumSectionsBaseChangeMap ρ G =
      spectrumSectionsBaseChangeMap ρ F ≫ (ΓS).map ((L).map f) := by
  apply ((adj).homEquiv _ _).injective
  rw [(adj).homEquiv_naturality_left, (adj).homEquiv_naturality_right]
  simp only [spectrumSectionsBaseChangeMap, Equiv.apply_symm_apply]
  have hη : f ≫ (η).app G = (η).app F ≫ (P).map ((L).map f) :=
    (η).naturality f
  have hβ : (ΓR).map ((P).map ((L).map f)) ≫ (β).hom.app ((L).obj G) =
      (β).hom.app ((L).obj F) ≫ (ModuleCat.restrictScalars ρ.hom).map ((ΓS).map ((L).map f)) :=
    (β).hom.naturality ((L).map f)
  rw [← Category.assoc, ← (ΓR).map_comp, hη, (ΓR).map_comp, Category.assoc, hβ, Category.assoc]

theorem isIso_spectrumSectionsBaseChangeMap (F : (Spec R).Modules) [F.IsQuasicoherent] :
    IsIso (spectrumSectionsBaseChangeMap ρ F) := by
  let M := (ΓR).obj F
  let T := (tilde.functor R).obj M
  let a : T ⟶ F := F.fromTildeΓ
  haveI : IsIso a := inferInstanceAs (IsIso F.fromTildeΓ)
  obtain ⟨e, he⟩ := LinearAlgebraicGroups.FlatCohomology.affinePullback ρ
  let b := e.hom.app M
  let t := (tilde.adjunction (R := R)).unit.app M
  let v := (tilde.adjunction (R := S)).unit.app ((E).obj M)
  have hb : (E).map t ≫ spectrumSectionsBaseChangeMap ρ T ≫ (ΓS).map b = v := by
    apply ((adj).homEquiv _ _).injective
    rw [(adj).homEquiv_naturality_left, (adj).homEquiv_naturality_right]
    have ht := ((adj).homEquiv ((ΓR).obj T) ((ΓS).obj ((L).obj T))).apply_symm_apply
      ((ΓR).map ((η).app T) ≫ (β).hom.app ((L).obj T))
    change ((adj).homEquiv ((ΓR).obj T) ((ΓS).obj ((L).obj T)))
      (spectrumSectionsBaseChangeMap ρ T) = _ at ht
    change (t ≫ ((adj).homEquiv ((ΓR).obj T) ((ΓS).obj ((L).obj T)))
      (spectrumSectionsBaseChangeMap ρ T) ≫
      (ModuleCat.restrictScalars ρ.hom).map ((ΓS).map b)) = _
    rw [ht]
    have h := he M
    rw [(tilde.adjunction (R := R)).homEquiv_unit,
      (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv_unit] at h
    have hb' : (β).hom.app ((L).obj T) ≫
        (ModuleCat.restrictScalars ρ.hom).map ((ΓS).map b) =
          (ΓR).map ((P).map b) ≫ (β).hom.app _ :=
      ((β).hom.naturality b).symm
    rw [Category.assoc ((ΓR).map _) _ _, hb', ← Category.assoc ((ΓR).map _) _ _,
      ← (ΓR).map_comp, ← Category.assoc]
    change (_ ≫ _) ≫ _ = _
    rw [h]
    have hh : (β).inv.app _ ≫ (β).hom.app ((ModuleCat.extendScalars ρ.hom ⋙ tilde.functor S).obj M) =
        𝟙 _ := (β).inv_hom_id_app _
    change _ ≫ ((β).inv.app _ ≫ (β).hom.app _) = _
    simp only [Iso.inv_hom_id_app, Category.comp_id]
    rfl
  haveI : IsIso t := inferInstanceAs (IsIso ((tilde.toTildeΓNatIso (R := R)).hom.app M))
  haveI : IsIso v := inferInstanceAs (IsIso ((tilde.toTildeΓNatIso (R := S)).hom.app ((E).obj M)))
  haveI : IsIso ((E).map t ≫ spectrumSectionsBaseChangeMap ρ T ≫ (ΓS).map b) := hb.symm ▸ inferInstance
  haveI : IsIso (spectrumSectionsBaseChangeMap ρ T ≫ (ΓS).map b) :=
    IsIso.of_isIso_comp_left ((E).map t) _
  haveI : IsIso (spectrumSectionsBaseChangeMap ρ T) :=
    IsIso.of_isIso_comp_right _ ((ΓS).map b)
  haveI : IsIso (spectrumSectionsBaseChangeMap ρ T ≫ (ΓS).map ((L).map a)) := inferInstance
  haveI : IsIso ((E).map ((ΓR).map a) ≫ spectrumSectionsBaseChangeMap ρ F) :=
    (spectrumSectionsBaseChangeMap_natural ρ a).symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left ((E).map ((ΓR).map a)) _

theorem spectrumPullback_isQuasicoherent (F : (Spec R).Modules) [F.IsQuasicoherent] :
    ((L).obj F).IsQuasicoherent := by
  let eF := asIso F.fromTildeΓ
  let e := (LinearAlgebraicGroups.FlatCohomology.affinePullback ρ).choose
  let i := ((L).mapIso eF).symm ≪≫ e.app ((ΓR).obj F)
  exact (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso i.symm
    (inferInstanceAs ((tilde.functor S).obj ((E).obj ((ΓR).obj F))).IsQuasicoherent)

end AffineSpectrum

section PullbackUnits

open Scheme.Modules

private abbrev pullbackUnit {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) :
    F ⟶ (pushforward f).obj ((Scheme.Modules.pullback f).obj F) :=
  (pullbackPushforwardAdjunction f).unit.app F

private theorem pullbackUnit_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (F : X.Modules) :
    pullbackUnit (g ≫ f) F =
      pullbackUnit f F ≫ (pushforward f).map (pullbackUnit g ((Scheme.Modules.pullback f).obj F)) ≫
        (pushforwardComp g f).hom.app _ ≫
        (pushforward (g ≫ f)).map ((pullbackComp g f).hom.app F) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp
    (pullbackPushforwardAdjunction g)) (pullbackPushforwardAdjunction (g ≫ f))
    (pullbackComp g f).inv F
  rw [conjugateEquiv_pullbackComp_inv] at h
  change (pullbackUnit f F ≫ (pushforward f).map (pullbackUnit g ((Scheme.Modules.pullback f).obj F))) ≫
    (pushforwardComp g f).hom.app _ =
    pullbackUnit (g ≫ f) F ≫ (pushforward (g ≫ f)).map ((pullbackComp g f).inv.app F) at h
  rw [Category.assoc] at h
  rw [reassoc_of% h, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [(pushforward (g ≫ f)).map_id, Category.comp_id]

private theorem isIso_pullbackUnit_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (F : X.Modules) (W : X.Opens) (hW : W ≤ f.opensRange) :
    IsIso ((pullbackUnit f F).app W) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f)
    (pullbackPushforwardAdjunction f) F
  change (restrictAdjunction f).unit.app F ≫ (pushforward f).map
    ((restrictFunctorIsoPullback f).hom.app F) = pullbackUnit f F at h
  have hu : IsIso (((restrictAdjunction f).unit.app F).app W) := by
    rw [restrictAdjunction_unit_app_app]
    have heq : f ''ᵁ (f ⁻¹ᵁ W) = W := by
      rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
    have hi : IsIso (homOfLE (f.image_preimage_le W)).op := by
      rw [show homOfLE (f.image_preimage_le W) = eqToHom heq from Subsingleton.elim _ _]
      infer_instance
    exact Functor.map_isIso _ _
  rw [← h, Hom.comp_app]
  exact IsIso.comp_isIso' hu
    (inferInstanceAs (IsIso (((pushforward f).mapIso
      ((restrictFunctorIsoPullback f).app F)).hom.app W)))

/-- Inverse image on an affine open is computed by inverse image between the
spectra of the two coordinate rings. -/
def affineOpenPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X) {W : X.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen (f ⁻¹ᵁ W)) (F : X.Modules) :
    (Scheme.Modules.pullback hV.fromSpec).obj ((Scheme.Modules.pullback f).obj F) ≅
      (Scheme.Modules.pullback (Spec.map (f.app W))).obj ((Scheme.Modules.pullback hW.fromSpec).obj F) :=
  (pullbackComp hV.fromSpec f).app F ≪≫
    (pullbackCongr (show hV.fromSpec ≫ f = Spec.map (f.app W) ≫ hW.fromSpec by
      rw [← f.appLE_eq_app]
      exact (hW.SpecMap_appLE_fromSpec f hV le_rfl).symm)).app F ≪≫
    ((pullbackComp (Spec.map (f.app W)) hW.fromSpec).app F).symm

private def toTopSections {X : Scheme.{u}} (F : X.Modules) {V : X.Opens}
    (hV : V = ⊤) (s : Γ(F, V)) : Γ(F, ⊤) :=
  F.presheaf.map (eqToHom hV.symm).op s

private theorem toTopSections_bijective {X : Scheme.{u}} (F : X.Modules) {V : X.Opens}
    (hV : V = ⊤) : Function.Bijective (toTopSections F hV) := by
  subst V
  have hid : ∀ s : Γ(F, ⊤), toTopSections F rfl s = s := by
    intro s
    unfold toTopSections
    rw [show (eqToHom (Eq.symm (rfl : (⊤ : X.Opens) = ⊤))).op = 𝟙 _ from rfl,
      F.presheaf.map_id]
    rfl
  exact (funext hid).symm ▸ Function.bijective_id

private theorem toTopSections_natural {X : Scheme.{u}} {F G : X.Modules} (b : F ⟶ G)
    {V : X.Opens} (hV : V = ⊤) (s : Γ(F, V)) :
    toTopSections G hV (b.app V s) = b.app ⊤ (toTopSections F hV s) :=
  (PresheafOfModules.naturality_apply b.val (eqToHom hV.symm).op s).symm

private def pullbackTopUnit {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    (W : X.Opens) (hW : f ⁻¹ᵁ W = ⊤) (s : Γ(F, W)) :
    Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
  toTopSections _ hW ((pullbackUnit f F).app W s)

private theorem pullbackTopUnit_top {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    (s : Γ(F, ⊤)) :
    pullbackTopUnit f F ⊤ (by simp) s = (pullbackUnit f F).app ⊤ s := by
  simp [pullbackTopUnit, toTopSections]

private theorem pullbackTopUnit_congr {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (F : X.Modules) (W : X.Opens) (hf : f ⁻¹ᵁ W = ⊤) (hg : g ⁻¹ᵁ W = ⊤) (s : Γ(F, W)) :
    ((pullbackCongr h).hom.app F).app ⊤ (pullbackTopUnit f F W hf s) =
      pullbackTopUnit g F W hg s := by
  subst g
  simp [pullbackCongr]

private theorem pullbackTopUnit_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (F : X.Modules) (W : X.Opens) (hW : (g ≫ f) ⁻¹ᵁ W = ⊤) (s : Γ(F, W)) :
    pullbackTopUnit (g ≫ f) F W hW s =
      ((pullbackComp g f).hom.app F).app ⊤
        (pullbackTopUnit g ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ W) hW
          ((pullbackUnit f F).app W s)) := by
  unfold pullbackTopUnit
  have h := congrArg (fun b : F ⟶ _ => b.app W s) (pullbackUnit_comp f g F)
  rw [h]
  change toTopSections _ hW
    (((pullbackComp g f).hom.app F).app ((g ≫ f) ⁻¹ᵁ W)
      ((pullbackUnit g ((Scheme.Modules.pullback f).obj F)).app (f ⁻¹ᵁ W)
        ((pullbackUnit f F).app W s))) = _
  exact toTopSections_natural _ hW _

private theorem fromSpec_preimage_self {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ⁻¹ᵁ W = ⊤ := by
  let p := hW.fromSpec
  change p ⁻¹ᵁ W = ⊤
  calc
    p ⁻¹ᵁ W = p ⁻¹ᵁ p.opensRange := congrArg (p ⁻¹ᵁ ·) hW.opensRange_fromSpec.symm
    _ = ⊤ := p.preimage_opensRange

private theorem pullbackTopUnit_fromSpec_smul {X : Scheme.{u}} {W : X.Opens}
    (hW : IsAffineOpen W) (F : X.Modules) (r : Γ(X, W)) (s : Γ(F, W)) :
    pullbackTopUnit hW.fromSpec F W (fromSpec_preimage_self hW) (r • s) =
      (Scheme.ΓSpecIso Γ(X, W)).inv r •
        pullbackTopUnit hW.fromSpec F W (fromSpec_preimage_self hW) s := by
  let p := hW.fromSpec
  let M := (Scheme.Modules.pullback p).obj F
  let h := fromSpec_preimage_self hW
  change M.val.map (eqToHom h.symm).op ((pullbackUnit p F).app W (r • s)) = _
  let z : M.val.obj (op (p ⁻¹ᵁ W)) := (pullbackUnit p F).app W s
  have hm : (pullbackUnit p F).app W (r • s) =
      (p.app W r : Γ(Spec Γ(X, W), p ⁻¹ᵁ W)) • z :=
    ((pullbackUnit p F).val.app (op W)).hom.map_smul r s
  rw [hm, M.val.map_smul]
  have hr := hW.fromSpec_app_self
  change p.app W = _ at hr
  have he : p.app W ≫ (Spec Γ(X, W)).presheaf.map (eqToHom h.symm).op =
      (Scheme.ΓSpecIso Γ(X, W)).inv := by
    rw [hr, Category.assoc, ← Functor.map_comp]
    rw [show _ ≫ _ = 𝟙 (op (⊤ : (Spec Γ(X, W)).Opens)) from Subsingleton.elim _ _]
    simp
  let t : M.val.obj (op ⊤) := M.val.map (eqToHom h.symm).op z
  exact congrArg (fun a : Γ(Spec Γ(X, W), ⊤) => a • t)
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) r)

/-- The unit of restriction to the spectrum of an affine open, evaluated on
that open, identifies its sections with global sections of the restriction. -/
def affineSectionsRestriction {X : Scheme.{u}} {W : X.Opens}
    (hW : IsAffineOpen W) (F : X.Modules) :
    F.val.obj (op W) ≅ (moduleSpecΓFunctor (R := Γ(X, W))).obj
      ((Scheme.Modules.pullback hW.fromSpec).obj F) := by
  let p := hW.fromSpec
  let M := (Scheme.Modules.pullback p).obj F
  let h := fromSpec_preimage_self hW
  let N := (moduleSpecΓFunctor (R := Γ(X, W))).obj M
  let f : F.val.obj (op W) ⟶ N :=
    ModuleCat.ofHom (X := F.val.obj (op W)) (Y := N) {
      toFun := pullbackTopUnit p F W h
      map_add' := fun x y => by
        change M.val.map (eqToHom h.symm).op ((pullbackUnit p F).app W (x + y)) =
          M.val.map (eqToHom h.symm).op ((pullbackUnit p F).app W x) +
            M.val.map (eqToHom h.symm).op ((pullbackUnit p F).app W y)
        rw [map_add, map_add]
      map_smul' := pullbackTopUnit_fromSpec_smul hW F }
  have hi : IsIso ((pullbackUnit p F).app W) :=
    isIso_pullbackUnit_app p F W hW.opensRange_fromSpec.ge
  have hf : Function.Bijective f := by
    change Function.Bijective (pullbackTopUnit p F W h)
    exact (toTopSections_bijective M h).comp (ConcreteCategory.bijective_of_isIso ((pullbackUnit p F).app W))
  letI : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr hf
  exact asIso f

private theorem pullbackTopUnit_change_open {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    {W : X.Opens} (h : W = ⊤) (hW : f ⁻¹ᵁ W = ⊤) (s : Γ(F, W)) :
    pullbackTopUnit f F W hW s = (pullbackUnit f F).app ⊤ (toTopSections F h s) := by
  subst W
  rw [pullbackTopUnit_top]
  change _ = (pullbackUnit f F).app ⊤ (F.presheaf.map (𝟙 (op ⊤)) s)
  rw [F.presheaf.map_id]
  rfl

private theorem affineOpenPullbackIso_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    {W : X.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen (f ⁻¹ᵁ W))
    (F : X.Modules) (s : Γ(F, W)) :
    ((affineOpenPullbackIso f hW hV F).hom).app ⊤
      ((affineSectionsRestriction hV ((Scheme.Modules.pullback f).obj F)).hom
        ((pullbackUnit f F).app W s)) =
      (pullbackUnit (Spec.map (f.app W)) ((Scheme.Modules.pullback hW.fromSpec).obj F)).app ⊤
        ((affineSectionsRestriction hW F).hom s) := by
  let p := hW.fromSpec
  let q := hV.fromSpec
  let v := Spec.map (f.app W)
  have h : q ≫ f = v ≫ p := by
    change hV.fromSpec ≫ f = Spec.map (f.app W) ≫ hW.fromSpec
    rw [← f.appLE_eq_app]
    exact (hW.SpecMap_appLE_fromSpec f hV le_rfl).symm
  let hp : p ⁻¹ᵁ W = ⊤ := fromSpec_preimage_self hW
  let hq : q ⁻¹ᵁ (f ⁻¹ᵁ W) = ⊤ := fromSpec_preimage_self hV
  have hv : (v ≫ p) ⁻¹ᵁ W = ⊤ := by
    change v ⁻¹ᵁ (p ⁻¹ᵁ W) = ⊤
    rw [hp, Scheme.Hom.preimage_top]
  have hc := pullbackTopUnit_congr h F W hq hv s
  rw [pullbackTopUnit_comp f q, pullbackTopUnit_comp p v, pullbackTopUnit_change_open v _ hp] at hc
  let a := (pullbackComp q f).hom.app F
  let b := (pullbackCongr h).hom.app F
  let c := (pullbackComp v p).app F
  let s' := pullbackTopUnit q ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ W) hq
    ((pullbackUnit f F).app W s)
  let t' := (pullbackUnit v ((Scheme.Modules.pullback p).obj F)).app ⊤
    (pullbackTopUnit p F W hp s)
  have hh : (a ≫ b).app ⊤ s' = c.hom.app ⊤ t' := hc
  change ((a ≫ b) ≫ c.inv).app ⊤ s' = t'
  change c.inv.app ⊤ ((a ≫ b).app ⊤ s') = t'
  rw [hh]
  have he : (c.hom ≫ c.inv).app ⊤ t' = t' := by simp
  exact he

/-- On an affine open with affine inverse image, the adjoint of the unit on
sections is an isomorphism over the coordinate rings. -/
theorem isIso_affineSectionsBaseChangeMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    {W : X.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen (f ⁻¹ᵁ W))
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (((ModuleCat.extendRestrictScalarsAdj (f.app W).hom).homEquiv
      (F.val.obj (op W)) (((Scheme.Modules.pullback f).obj F).val.obj (op (f ⁻¹ᵁ W)))).symm
        ((pullbackUnit f F).val.app (op W))) := by
  let A := ModuleCat.extendRestrictScalarsAdj (f.app W).hom
  let E := ModuleCat.extendScalars (f.app W).hom
  let MF := (Scheme.Modules.pullback hW.fromSpec).obj F
  let G := (Scheme.Modules.pullback f).obj F
  let e := affineSectionsRestriction hW F
  let d := affineSectionsRestriction hV G ≪≫
    moduleSpecΓFunctor.mapIso (affineOpenPullbackIso f hW hV F)
  let q : F.val.obj (op W) ⟶ _
      := (pullbackUnit f F).val.app (op W)
  let b := (A.homEquiv _ _).symm q
  haveI : MF.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, W)).ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback hW.fromSpec).app F)
      (inferInstanceAs ((restrictFunctor hW.fromSpec).obj F).IsQuasicoherent)
  have hb : b ≫ d.hom = E.map e.hom ≫ spectrumSectionsBaseChangeMap (f.app W) MF := by
    apply (A.homEquiv _ _).injective
    rw [A.homEquiv_naturality_right, A.homEquiv_naturality_left]
    have h := (A.homEquiv _ _).apply_symm_apply q
    change A.homEquiv _ _ b = q at h
    rw [h]
    apply ModuleCat.hom_ext
    ext s : 1
    change d.hom (q s) = ((A.homEquiv _ _ (spectrumSectionsBaseChangeMap (f.app W) MF)) (e.hom s))
    have hsp := (A.homEquiv (moduleSpecΓFunctor.obj MF) _).apply_symm_apply
      (moduleSpecΓFunctor.map (pullbackUnit (Spec.map (f.app W)) MF) ≫
        (FlatCohomology.affinePushforwardSections (f.app W)).hom.app _)
    change A.homEquiv _ _ (spectrumSectionsBaseChangeMap (f.app W) MF) = _ at hsp
    rw [hsp]
    exact affineOpenPullbackIso_unit f hW hV F s
  letI : IsIso (spectrumSectionsBaseChangeMap (f.app W) MF) :=
    isIso_spectrumSectionsBaseChangeMap _ _
  letI : IsIso (b ≫ d.hom) := hb.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right b d.hom

end PullbackUnits

section Quasicoherence

open Scheme.Modules

private theorem isQuasicoherent_pullback_open {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj F).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback f).app F)
    (inferInstanceAs (F.restrict f).IsQuasicoherent)

/-- Quasi-coherence can be checked after restricting to spectra of affine opens
in any covering family. -/
private theorem isQuasicoherent_of_affineRestrictions {X : Scheme.{u}}
    (F : X.Modules) {I : Type u} (U : I → X.Opens) (hU : IsOpenCover U)
    (hAff : ∀ i, IsAffineOpen (U i))
    (hF : ∀ i, (F.restrict (hAff i).fromSpec).IsQuasicoherent) :
    F.IsQuasicoherent := by
  suffices d : SheafOfModules.QuasicoherentData.{u,u,u,u} (R := X.ringCatSheaf) F from
    d.isQuasicoherent
  refine
    { I := I
      X := U
      coversTop := (Opens.coversTop_iff _ U).mpr hU
      presentation := fun i => ?_ }
  let h := hAff i
  let p := h.fromSpec
  let R := Γ(X, U i)
  let N : (Spec R).Modules := F.restrict p
  letI : N.IsQuasicoherent := hF i
  let M := (moduleSpecΓFunctor (R := R)).obj N
  let s : Set M := Set.univ
  let t : Submodule R (s →₀ R) := LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M))
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R) N) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let pres : N.Presentation := (presentationTilde (M := M) s (by simp [s])
    (t : Set (s →₀ R)) (Submodule.span_eq t)).ofIsIso (Scheme.Modules.fromTildeΓ (R := R) N)
  let q := h.isoSpec.hom
  let P := restrictFunctor q
  letI : P.IsLeftAdjoint := (restrictAdjunction q).isLeftAdjoint
  let eP : SheafOfModules.unit.{u} (U i).toScheme.ringCatSheaf ≅
      P.obj (SheafOfModules.unit.{u} (Spec R).ringCatSheaf) := (restrictUnitIso q).symm
  let e : P.obj N ≅ F.restrict (U i).ι :=
    ((restrictFunctorComp q p).app F).symm ≪≫
      (restrictFunctorCongr (h.isoSpec_hom_fromSpec)).app F
  let E := (overEquiv (U i)).inverse
  letI : E.IsEquivalence := inferInstanceAs (overEquiv (U i)).inverse.IsEquivalence
  let eE := ((U i).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let o := ((overFunctorEquiv (U i)).app F)
  have eo : E.obj (F.restrict (U i).ι) ≅ F.over (U i) :=
    (E.mapIso o).symm ≪≫ ((overEquiv (U i)).unitIso.app _).symm
  exact ((pres.map P eP).ofIsIso e.hom |>.map E eE).ofIsIso eo.hom

private theorem isQuasicoherent_pullback_of_affine {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj F).IsQuasicoherent := by
  let I := {W : X.Opens // IsAffineOpen W}
  let U : I → Y.Opens := fun i => f ⁻¹ᵁ i.val
  have hU : IsOpenCover U := by
    apply top_unique
    intro y _
    obtain ⟨_, ⟨W, hW, rfl⟩, hy, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show f y ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).2
    exact Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hy⟩
  let hAff (i : I) : IsAffineOpen (U i) := i.property.preimage f
  apply isQuasicoherent_of_affineRestrictions _ U hU hAff
  intro i
  let h := i.property
  let e := (restrictFunctorIsoPullback (hAff i).fromSpec).app ((Scheme.Modules.pullback f).obj F) ≪≫
    affineOpenPullbackIso f h (hAff i) F
  letI := isQuasicoherent_pullback_open h.fromSpec F
  exact (SheafOfModules.isQuasicoherent (Spec Γ(Y, U i)).ringCatSheaf).prop_of_iso e.symm
    (spectrumPullback_isQuasicoherent (f.app i.val) ((Scheme.Modules.pullback h.fromSpec).obj F))

/-- A cokernel of a morphism of quasi-coherent sheaves is quasi-coherent. -/
private theorem isQuasicoherent_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    S.X₃.IsQuasicoherent := by
  let I := {W : X.Opens // IsAffineOpen W}
  let U : I → X.Opens := fun i => i.val
  have hU : IsOpenCover U := by
    apply top_unique
    intro x _
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).2
    exact Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hx⟩
  apply isQuasicoherent_of_affineRestrictions _ U hU (fun i => i.property)
  intro i
  let p := i.property.fromSpec
  let R := Γ(X, U i)
  let L := restrictFunctor p
  let T := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  let N₁ := L.obj S.X₁
  let N₂ := L.obj S.X₂
  let N₃ := L.obj S.X₃
  let e₁ : T.obj (G.obj N₁) ≅ N₁ := asIso (S.X₁.restrict p).fromTildeΓ
  let e₂ : T.obj (G.obj N₂) ≅ N₂ := asIso (S.X₂.restrict p).fromTildeΓ
  let a := G.map (L.map S.f)
  let q := cokernel.π a
  have hq : T.map a ≫ T.map q = 0 := by rw [← T.map_comp, cokernel.condition, T.map_zero]
  let M := CokernelCofork.ofπ (T.map q) hq
  have hM : IsColimit M :=
    CokernelCofork.mapIsColimit _ (cokernelIsCokernel a) T
  let b := e₂.inv ≫ T.map q
  have he : e₁.hom ≫ L.map S.f = T.map a ≫ e₂.hom :=
    ((tilde.adjunction (R := R)).counit.naturality (L.map S.f)).symm
  have hb : L.map S.f ≫ b = 0 := by
    rw [← cancel_epi e₁.hom, comp_zero, ← Category.assoc, he, Category.assoc]
    simp [b, hq]
  let M' := CokernelCofork.ofπ b hb
  have hM' : IsColimit M' :=
    IsCokernel.ofIso _ hM M' e₁ e₂ (Iso.refl _) he (by simp [M, M', b])
  let N := CokernelCofork.ofπ (L.map S.g) (by rw [← L.map_comp, S.zero, L.map_zero])
  have hN : IsColimit N := CokernelCofork.mapIsColimit _ hS.gIsCokernel L
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso hM' hN)
    (inferInstanceAs (T.obj (cokernel a)).IsQuasicoherent)

end Quasicoherence

section AffineSectionBaseChange

variable {A B : Type u} [CommRing A] [CommRing B]
  (φ : A →+* B) (X : SchemeOverRing A) (F : X.left.Modules)

local notation "Y" => (changeBase φ).obj X
local notation "j" => fibreProjection φ X
local notation "G" => fibreSheaf φ X F

/-- On sections over an open, the base-change map is adjoint to the unit
of inverse and direct image evaluated on that open. -/
def localSectionsBaseChangeMap (W : X.left.Opens) :
    (ModuleCat.extendScalars.{u,u,u} φ).obj (localSections F W) ⟶
      localSections (X := (Y)) G (j ⁻¹ᵁ W) :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm
    ((coefficientPullback φ j (fibreProjection_over φ X) (fibreCoefficientMap φ X F)).app (op W))

@[simp]
theorem localSectionsBaseChangeMap_one_tmul (W : X.left.Opens) (x : localSections F W) :
    localSectionsBaseChangeMap φ X F W ((1 : B) ⊗ₜ[A,φ] x) =
      (fibreCoefficientMap φ X F).app W x := by
  let q := (coefficientPullback φ j (fibreProjection_over φ X)
    (fibreCoefficientMap φ X F)).app (op W)
  let a := ModuleCat.extendRestrictScalarsAdj φ
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((a.homEquiv _ _).apply_symm_apply q)) x

theorem isIso_localSectionsBaseChangeMap [F.IsQuasicoherent]
    {W : X.left.Opens} (hW : IsAffineOpen W) :
    IsIso (localSectionsBaseChangeMap φ X F W) := by
  let V := j ⁻¹ᵁ W
  let R := Γ(X.left, W)
  let S := Γ((Y).left, V)
  let r := groundRingHomOpen X W
  let s := groundRingHomOpen (Y) V
  let ρ := ((j).app W).hom
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A R := r.toAlgebra
  letI : Algebra B S := s.toAlgebra
  letI : Algebra R S := ρ.toAlgebra
  letI : Algebra A S := (s.comp φ).toAlgebra
  letI : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq'
    (groundRingHomOpen_over φ j (fibreProjection_over φ X) W).symm
  letI : Algebra.IsPushout A B R S := CommRingCat.isPushout_iff_isPushout.mp
    (affineFibreRingPushout φ X hW).flip
  let M : ModuleCat.{u} R := F.val.obj (op W)
  let N : ModuleCat.{u} S := (G).val.obj (op V)
  let M' : ModuleCat.{u} A := localSections F W
  letI : Module A M := M'.isModule
  letI : IsScalarTower A R M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let b := ((ModuleCat.extendRestrictScalarsAdj ρ).homEquiv M N).symm
    ((fibreCoefficientMap φ X F).val.app (op W))
  letI : IsIso b := isIso_affineSectionsBaseChangeMap j hW (isAffineOpen_fibrePreimage φ X hW) F
  let e : (ModuleCat.extendScalars φ).obj M' ≅
      (ModuleCat.restrictScalars s).obj ((ModuleCat.extendScalars ρ).obj M) :=
    (Algebra.IsPushout.cancelBaseChange A B R S M).symm.toModuleIso
  have hb : localSectionsBaseChangeMap φ X F W = e.hom ≫ (ModuleCat.restrictScalars s).map b := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rw [localSectionsBaseChangeMap_one_tmul]
    change (fibreCoefficientMap φ X F).app W x =
      b ((Algebra.IsPushout.cancelBaseChange A B R S M).symm ((1 : B) ⊗ₜ[A] (x : M)))
    rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]
    let ad := ModuleCat.extendRestrictScalarsAdj ρ
    have h := (ad.homEquiv M N).apply_symm_apply ((fibreCoefficientMap φ X F).val.app (op W))
    exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x).symm
  rw [hb]
  infer_instance

end AffineSectionBaseChange

private theorem intersectionAcyclic_of_affineOpens
    {A : Type u} [CommRing A] {X : SchemeOverRing A}
    {I : Type u} [Preorder I] (U : I → X.left.Opens)
    (hU : ∀ n (e : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen U e))
    (F : X.left.Modules) [F.IsQuasicoherent] : IntersectionAcyclic U F := by
  intro n e q hq
  exact LinearAlgebraicGroups.Cohomology.isZero_rightDerived_evaluation_of_isAffineOpen
    (hU n e) F q hq

section SheafExactness

open TopCat.Presheaf

/-- A short complex of module sheaves that is short exact on sections over each
affine open is short exact as a complex of sheaves. -/
theorem shortExact_of_affineSections {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hinj : ∀ U : X.Opens, IsAffineOpen U → Function.Injective (S.f.app U))
    (hex : ∀ U : X.Opens, IsAffineOpen U → Function.Exact (S.f.app U) (S.g.app U))
    (hsurj : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (S.g.app U)) :
    S.ShortExact := by
  let F : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := SheafOfModules.toSheaf X.ringCatSheaf
  haveI : F.PreservesZeroMorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms
  letI : F.Faithful := inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Faithful
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful F
  let T := S.map F
  let M₁ : TopCat.Presheaf AddCommGrpCat.{u} X := T.X₁.obj
  let M₂ : TopCat.Presheaf AddCommGrpCat.{u} X := T.X₂.obj
  let M₃ : TopCat.Presheaf AddCommGrpCat.{u} X := T.X₃.obj
  have hT₁ : Mono T.f := by
    apply (TopCat.Presheaf.mono_iff_stalk_mono T.f).mpr
    intro x
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    exact stalkFunctor_map_injective_of_isBasis X.isBasis_affineOpens (fun U hU => hinj U hU) x
  have hT₂ : Epi T.g := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi T.g).mp
    apply (locally_surjective_iff_surjective_on_stalks T.g.hom).mpr
    intro x t
    obtain ⟨U, hx, hU, s, rfl⟩ := exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens
      M₃ x t
    obtain ⟨r, hr⟩ := hsurj U hU s
    refine ⟨M₂.germ U x hx r, ?_⟩
    rw [stalkFunctor_map_germ_apply]
    exact congrArg (M₃.germ U x hx) hr
  refine { exact := ?_, mono_f := hT₁, epi_g := hT₂ }
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact T).mpr
  intro x
  apply (ShortComplex.ab_exact_iff _).mpr
  intro t ht
  obtain ⟨U, hx, hU, s, rfl⟩ := exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens
    M₂ x t
  change (stalkFunctor _ x).map T.g.hom (M₂.germ U x hx s) = 0 at ht
  rw [stalkFunctor_map_germ_apply] at ht
  have hz₀ : M₃.germ U x hx (0 : M₃.obj (op U)) = 0 := map_zero _
  rw [← hz₀] at ht
  obtain ⟨V, hxV, hV, hVU, _, hres⟩ := germ_eq_of_isBasis X.isBasis_affineOpens
    M₃ x hx hx ht
  rw [map_zero, ← T.g.hom.naturality_apply] at hres
  have hz : S.g.app V (M₂.map (homOfLE hVU).op s) = 0 := hres
  obtain ⟨r, hr⟩ := (hex V hV _).mp hz
  refine ⟨M₁.germ V x hxV r, ?_⟩
  change (stalkFunctor _ x).map T.f.hom (M₁.germ V x hxV r) = _
  rw [stalkFunctor_map_germ_apply]
  change M₂.germ V x hxV (S.f.app V r) = _
  rw [hr]
  exact M₂.germ_res_apply (homOfLE hVU) x hxV s

end SheafExactness

section ShortExactResolutions

open CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

private abbrev extendCochainsToInt (C : Type*) [Category* C] [HasZeroMorphisms C] [HasZeroObject C] :=
  intEmbedding.extendFunctor C

private abbrev restrictCochainsToNat (C : Type*) [Category* C] [HasZeroMorphisms C] :=
  intEmbedding.restrictionFunctor C

private theorem restrictionQuasiIso {K L : CochainComplex C ℤ}
    [K.IsStrictlySupported intEmbedding] [L.IsStrictlySupported intEmbedding]
    (f : K ⟶ L) [QuasiIso f] : QuasiIso ((restrictCochainsToNat C).map f) := by
  let e := intEmbedding
  have h (T : CochainComplex C ℤ) [T.IsStrictlySupported e] :
      IsIso (T.restrictionToTruncGE' e) := by
    suffices ∀ i, IsIso ((T.restrictionToTruncGE' e).f i) from Hom.isIso_of_components _
    intro i
    have : IsIso ((HomologicalComplex.πTruncGE T e).f (e.f i)) := inferInstance
    rwa [show HomologicalComplex.πTruncGE T e = e.liftExtend (T.restrictionToTruncGE' e) _ from rfl,
      e.isIso_liftExtend_f_iff _ _ (rfl : e.f i = e.f i)] at this
  letI : IsIso (K.restrictionToTruncGE' e) := h K
  letI : IsIso (L.restrictionToTruncGE' e) := h L
  letI : QuasiIso (K.restrictionToTruncGE' e) := inferInstance
  letI : QuasiIso (L.restrictionToTruncGE' e) := inferInstance
  have hq : QuasiIso (truncGE'Map f e) := by
    apply (quasiIso_extendMap_iff (truncGE'Map f e) e).mp
    exact (quasiIso_truncGEMap_iff f e).mpr fun _ _ _ => inferInstance
  rw [← quasiIso_iff_comp_right ((restrictCochainsToNat C).map f) (L.restrictionToTruncGE' e)]
  have hn : (restrictCochainsToNat C).map f ≫ L.restrictionToTruncGE' e =
      K.restrictionToTruncGE' e ≫ truncGE'Map f e :=
    (e.restrictionToTruncGE'NatTrans C).naturality f
  rw [hn]
  exact (quasiIso_iff_comp_left _ _).mpr hq

private def restrictedSingleIso (X : C) :
    ((restrictCochainsToNat C).obj ((CochainComplex.singleFunctor C 0).obj X)) ≅ (single₀ C).obj X := by
  let e := intEmbedding
  let s := extendSingleIso e X (0 : ℕ) (0 : ℤ) rfl
  let f := e.homRestrict s.inv
  letI : ∀ n, IsIso (f.f n) := fun n => by
    change IsIso ((e.homRestrict s.inv).f n)
    rw [e.homRestrict_f s.inv (rfl : e.f n = e.f n)]
    infer_instance
  letI : IsIso f := Hom.isIso_of_components f
  exact asIso f

private theorem restrictedSingleIso_naturality_zero {X Y : C} (f : X ⟶ Y) :
    ((restrictCochainsToNat C).map ((CochainComplex.singleFunctor C 0).map f)).f 0 ≫
        (restrictedSingleIso Y).hom.f 0 =
      (restrictedSingleIso X).hom.f 0 ≫ ((single₀ C).map f).f 0 := by
  change ((CochainComplex.singleFunctor C 0).map f).f 0 ≫
      (intEmbedding.homRestrict (extendSingleIso intEmbedding Y (0 : ℕ) (0 : ℤ) rfl).inv).f 0 =
    (intEmbedding.homRestrict (extendSingleIso intEmbedding X (0 : ℕ) (0 : ℤ) rfl).inv).f 0 ≫
      ((single₀ C).map f).f 0
  have he (W : C) :
      (intEmbedding.homRestrict (extendSingleIso intEmbedding W (0 : ℕ) (0 : ℤ) rfl).inv).f 0 =
        (singleObjXSelf (.up ℤ) 0 W).hom ≫ (singleObjXSelf (.up ℕ) 0 W).inv := by
    rw [intEmbedding.homRestrict_f _ (rfl : intEmbedding.f 0 = (0 : ℤ))]
    have h := extendSingleIso_inv_f intEmbedding W (0 : ℕ) (0 : ℤ) rfl
    erw [h]
    simp [restrictionXIso, Category.assoc]
  rw [he X, he Y]
  simp only [CochainComplex.singleFunctor, CochainComplex.single₀, single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]

private theorem strictlySupported_single (X : C) :
    ((CochainComplex.singleFunctor C 0).obj X).IsStrictlySupported intEmbedding :=
  ⟨fun j hj => isZero_single_obj_X (.up ℤ) 0 X j (fun h => hj 0 h.symm)⟩

private def restrictResolution {X : C} (K : CochainComplex C ℤ)
    [K.IsStrictlySupported intEmbedding] (hK : ∀ n, Injective (K.X n))
    (a : (CochainComplex.singleFunctor C 0).obj X ⟶ K) [QuasiIso a] :
    InjectiveResolution X where
  cocomplex := (restrictCochainsToNat C).obj K
  injective n := hK (intEmbedding.f n)
  ι := (restrictedSingleIso X).inv ≫ (restrictCochainsToNat C).map a
  quasiIso := by
    letI := strictlySupported_single X
    letI := restrictionQuasiIso a
    infer_instance

private theorem restrictResolution_comm {X Y : C}
    (K L : CochainComplex C ℤ) [K.IsStrictlySupported intEmbedding]
    [L.IsStrictlySupported intEmbedding]
    (hK : ∀ n, Injective (K.X n)) (hL : ∀ n, Injective (L.X n))
    (a : (CochainComplex.singleFunctor C 0).obj X ⟶ K) [QuasiIso a]
    (b : (CochainComplex.singleFunctor C 0).obj Y ⟶ L) [QuasiIso b]
    (f : X ⟶ Y) (l : K ⟶ L) (w : a ≫ l = (CochainComplex.singleFunctor C 0).map f ≫ b) :
    (restrictResolution K hK a).ι.f 0 ≫ ((restrictCochainsToNat C).map l).f 0 =
      ((single₀ C).map f).f 0 ≫ (restrictResolution L hL b).ι.f 0 := by
  have h := congrArg (fun t => ((restrictCochainsToNat C).map t).f 0) w
  rw [Functor.map_comp, Functor.map_comp, comp_f, comp_f] at h
  let eX := HomologicalComplex.Hom.isoApp (restrictedSingleIso X) 0
  let eY := HomologicalComplex.Hom.isoApp (restrictedSingleIso Y) 0
  change (eX.inv ≫ ((restrictCochainsToNat C).map a).f 0) ≫ ((restrictCochainsToNat C).map l).f 0 =
    ((single₀ C).map f).f 0 ≫ eY.inv ≫ ((restrictCochainsToNat C).map b).f 0
  rw [Category.assoc, h]
  apply (cancel_epi eX.hom).mp
  have hw : ((restrictCochainsToNat C).map ((CochainComplex.singleFunctor C 0).map f)).f 0 ≫ eY.hom =
      eX.hom ≫ ((single₀ C).map f).f 0 := restrictedSingleIso_naturality_zero f
  simp only [Iso.hom_inv_id_assoc, ← reassoc_of% hw]

private theorem integralResolutionInjective {X : C} (I : InjectiveResolution X) (n : ℤ) :
    Injective (((extendCochainsToInt C).obj I.cocomplex).X n) := by
  by_cases h : ∃ i : ℕ, intEmbedding.f i = n
  · obtain ⟨i, hi⟩ := h
    exact Injective.of_iso (I.cocomplex.extendXIso intEmbedding hi).symm (I.injective i)
  · exact (I.cocomplex.isZero_extend_X intEmbedding n (fun i hi => h ⟨i, hi⟩)).injective

theorem exists_shortExactResolution [EnoughInjectives C] {S : ShortComplex C}
    (hS : S.ShortExact) : Nonempty (ShortExactResolution S) := by
  let I := injectiveResolution S.X₁
  let J := injectiveResolution S.X₃
  let e := intEmbedding
  let K := (extendCochainsToInt C).obj I.cocomplex
  let L := (extendCochainsToInt C).obj J.cocomplex
  letI : K.IsStrictlySupported intEmbedding := inferInstanceAs ((I.cocomplex.extend intEmbedding).IsStrictlySupported intEmbedding)
  letI : L.IsStrictlySupported intEmbedding := inferInstanceAs ((J.cocomplex.extend intEmbedding).IsStrictlySupported intEmbedding)
  let i : (CochainComplex.singleFunctor C 0).obj S.X₁ ⟶ K :=
    (extendSingleIso e S.X₁ (0 : ℕ) (0 : ℤ) rfl).inv ≫ extendMap I.ι e
  let j : (CochainComplex.singleFunctor C 0).obj S.X₃ ⟶ L :=
    (extendSingleIso e S.X₃ (0 : ℕ) (0 : ℤ) rfl).inv ≫ extendMap J.ι e
  haveI : QuasiIso (extendMap I.ι e) := (quasiIso_extendMap_iff _ _).mpr inferInstance
  haveI : QuasiIso (extendMap J.ι e) := (quasiIso_extendMap_iff _ _).mpr inferInstance
  haveI : QuasiIso i := by
    change QuasiIso ((extendSingleIso e S.X₁ (0 : ℕ) (0 : ℤ) rfl).inv ≫ extendMap I.ι e)
    infer_instance
  haveI : QuasiIso j := by
    change QuasiIso ((extendSingleIso e S.X₃ (0 : ℕ) (0 : ℤ) rfl).inv ≫ extendMap J.ι e)
    infer_instance
  have hK : Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe.BoundedInjective K :=
    ⟨⟨0, fun n hn => I.cocomplex.isZero_extend_X e n (fun m hm => by
      have hmn : (m : ℤ) = n := by simpa [e, intEmbedding, ComplexShape.embeddingUpIntGE] using hm
      omega)⟩, integralResolutionInjective I⟩
  have hL : Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe.BoundedInjective L :=
    ⟨⟨0, fun n hn => J.cocomplex.isZero_extend_X e n (fun m hm => by
      have hmn : (m : ℤ) = n := by simpa [e, intEmbedding, ComplexShape.embeddingUpIntGE] using hm
      omega)⟩, integralResolutionInjective J⟩
  obtain ⟨R, hR⟩ := AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe.exists_horseshoe C S hS
    K L i j inferInstance inferInstance hK hL
  letI : QuasiIso R.augmentation := hR.2.2.1
  letI : R.middle.IsStrictlySupported e := ⟨fun n hn => by
    have hKn := I.cocomplex.isZero_extend_X e n hn
    have hLn := J.cocomplex.isZero_extend_X e n hn
    let spl := (hR.2.2.2 n).some
    rw [IsZero.iff_id_eq_zero]
    have hf0 : (R.row.map (HomologicalComplex.eval C (.up ℤ) n)).f = 0 :=
      hKn.eq_of_src _ _
    have hg0 : (R.row.map (HomologicalComplex.eval C (.up ℤ) n)).g = 0 :=
      hLn.eq_of_tgt _ _
    simpa only [hf0, hg0, comp_zero, zero_comp, add_zero] using! spl.id.symm⟩
  refine ⟨{
    I₁ := restrictResolution K hK.2 i
    I₂ := restrictResolution R.middle hR.2.1.2 R.augmentation
    I₃ := restrictResolution L hL.2 j
    f := (restrictCochainsToNat C).map R.inclusion
    g := (restrictCochainsToNat C).map R.projection
    zero := by rw [← Functor.map_comp, R.zero, Functor.map_zero]
    comm_f := restrictResolution_comm K R.middle _ _ i R.augmentation _ _ R.comm_left
    comm_g := restrictResolution_comm R.middle L _ _ R.augmentation j _ _ R.comm_right
    splitting := fun n => hR.2.2.2 (intEmbedding.f n) }⟩

end ShortExactResolutions

private theorem intEmbedding_f (n : ℕ) : intEmbedding.f n = (n : ℤ) := by
  simp [intEmbedding]

private theorem shortExact_extend {C : Type*} [Category* C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℕ)} (hS : S.ShortExact) :
    (S.map (extendCochainsToInt C)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases h : ∃ n : ℕ, intEmbedding.f n = i
  · obtain ⟨n, hn⟩ := h
    let e : (S.map (extendCochainsToInt C)).map (HomologicalComplex.eval C (.up ℤ) i) ≅
        S.map (HomologicalComplex.eval C (.up ℕ) n) :=
      ShortComplex.isoMk (S.X₁.extendXIso intEmbedding hn) (S.X₂.extendXIso intEmbedding hn)
        (S.X₃.extendXIso intEmbedding hn)
        (by change _ ≫ S.f.f n = (extendMap S.f intEmbedding).f i ≫ _
            rw [extendMap_f _ _ hn]
            simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
        (by change _ ≫ S.g.f n = (extendMap S.g intEmbedding).f i ≫ _
            rw [extendMap_f _ _ hn]
            simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    exact ShortComplex.shortExact_of_iso e.symm (hS.map_of_exact _)
  · let T := (S.map (extendCochainsToInt C)).map (HomologicalComplex.eval C (.up ℤ) i)
    let hZ (K : CochainComplex C ℕ) := K.isZero_extend_X intEmbedding i (fun _ hi => h ⟨_, hi⟩)
    exact { exact := ShortComplex.exact_of_isZero_X₂ T (hZ S.X₂)
            mono_f := (hZ S.X₁).mono T.f
            epi_g := (hZ S.X₃).epi T.g }

private theorem extendOpcyclesIso_hom_natural {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℕ} (f : K ⟶ L) (i : ℕ) :
    opcyclesMap (extendMap f intEmbedding) (i : ℤ) ≫ (L.extendOpcyclesIso intEmbedding (intEmbedding_f i)).hom =
      (K.extendOpcyclesIso intEmbedding (intEmbedding_f i)).hom ≫ opcyclesMap f i := by
  apply (cancel_epi ((K.extend intEmbedding).pOpcycles (i : ℤ))).mp
  simp only [p_opcyclesMap_assoc, pOpcycles_extendOpcyclesIso_hom, Category.assoc,
    pOpcycles_extendOpcyclesIso_hom_assoc, p_opcyclesMap, extendMap_f f intEmbedding (intEmbedding_f i),
    Iso.inv_hom_id_assoc]

private theorem extendOpcyclesToCycles {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℕ) (i j : ℕ) :
    (K.extendOpcyclesIso intEmbedding (intEmbedding_f i)).hom ≫ K.opcyclesToCycles i j =
      (K.extend intEmbedding).opcyclesToCycles (i : ℤ) (j : ℤ) ≫
        (K.extendCyclesIso intEmbedding (intEmbedding_f j)).hom := by
  apply (cancel_epi ((K.extend intEmbedding).pOpcycles (i : ℤ))).mp
  apply (cancel_mono (K.iCycles j)).mp
  simp only [Category.assoc, opcyclesToCycles_iCycles, extendCyclesIso_hom_iCycles,
    pOpcycles_extendOpcyclesIso_hom_assoc, p_fromOpcycles, opcyclesToCycles_iCycles_assoc,
    p_fromOpcycles_assoc, extend_d_eq K intEmbedding (intEmbedding_f i) (intEmbedding_f j),
    Iso.inv_hom_id, Category.comp_id]

/-- Extension by zero respects the connecting map at degrees in the embedding. -/
private theorem delta_extend {C : Type*} [Category* C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℕ)} (hS : S.ShortExact) (i j : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j) (hij' : (ComplexShape.up ℤ).Rel (i : ℤ) (j : ℤ)) :
    (shortExact_extend hS).δ (i : ℤ) (j : ℤ) hij' ≫
        (S.X₁.extendHomologyIso intEmbedding (intEmbedding_f j)).hom =
      (S.X₃.extendHomologyIso intEmbedding (intEmbedding_f i)).hom ≫ hS.δ i j hij := by
  let input₁ := HomologicalComplex.HomologySequence.snakeInput (shortExact_extend hS)
    (i : ℤ) (j : ℤ) hij'
  let input₂ := HomologicalComplex.HomologySequence.snakeInput hS i j hij
  let f : input₁ ⟶ input₂ :=
    { f₀ :=
        { τ₁ := (S.X₁.extendHomologyIso intEmbedding (intEmbedding_f i)).hom
          τ₂ := (S.X₂.extendHomologyIso intEmbedding (intEmbedding_f i)).hom
          τ₃ := (S.X₃.extendHomologyIso intEmbedding (intEmbedding_f i)).hom
          comm₁₂ := (extendHomologyIso_hom_naturality S.f intEmbedding (intEmbedding_f i)).symm
          comm₂₃ := (extendHomologyIso_hom_naturality S.g intEmbedding (intEmbedding_f i)).symm }
      f₁ :=
        { τ₁ := (S.X₁.extendOpcyclesIso intEmbedding (intEmbedding_f i)).hom
          τ₂ := (S.X₂.extendOpcyclesIso intEmbedding (intEmbedding_f i)).hom
          τ₃ := (S.X₃.extendOpcyclesIso intEmbedding (intEmbedding_f i)).hom
          comm₁₂ := (extendOpcyclesIso_hom_natural S.f i).symm
          comm₂₃ := (extendOpcyclesIso_hom_natural S.g i).symm }
      f₂ :=
        { τ₁ := (S.X₁.extendCyclesIso intEmbedding (intEmbedding_f j)).hom
          τ₂ := (S.X₂.extendCyclesIso intEmbedding (intEmbedding_f j)).hom
          τ₃ := (S.X₃.extendCyclesIso intEmbedding (intEmbedding_f j)).hom
          comm₁₂ := (extendCyclesIso_hom_naturality S.f intEmbedding (intEmbedding_f j)).symm
          comm₂₃ := (extendCyclesIso_hom_naturality S.g intEmbedding (intEmbedding_f j)).symm }
      f₃ :=
        { τ₁ := (S.X₁.extendHomologyIso intEmbedding (intEmbedding_f j)).hom
          τ₂ := (S.X₂.extendHomologyIso intEmbedding (intEmbedding_f j)).hom
          τ₃ := (S.X₃.extendHomologyIso intEmbedding (intEmbedding_f j)).hom
          comm₁₂ := (extendHomologyIso_hom_naturality S.f intEmbedding (intEmbedding_f j)).symm
          comm₂₃ := (extendHomologyIso_hom_naturality S.g intEmbedding (intEmbedding_f j)).symm }
      comm₀₁ := by
        ext : 1
        all_goals exact extendHomologyIso_hom_homologyι _ intEmbedding (intEmbedding_f i)
      comm₁₂ := by
        ext : 1
        all_goals exact extendOpcyclesToCycles _ i j
      comm₂₃ := by
        ext : 1
        all_goals exact (homologyπ_extendHomologyIso_hom _ intEmbedding (intEmbedding_f j)).symm }
  exact ShortComplex.SnakeInput.naturality_δ f

private def splittingOfIso {C : Type*} [Category* C] [Preadditive C] {S T : ShortComplex C}
    (e : S ≅ T) (h : T.Splitting) : S.Splitting where
  r := e.hom.τ₂ ≫ h.r ≫ e.inv.τ₁
  s := e.hom.τ₃ ≫ h.s ≫ e.inv.τ₂
  f_r := by
    rw [← ShortComplex.Hom.comm₁₂_assoc, h.f_r_assoc]
    exact congrArg ShortComplex.Hom.τ₁ e.hom_inv_id
  s_g := by
    simp only [Category.assoc, ShortComplex.Hom.comm₂₃, h.s_g_assoc]
    exact congrArg ShortComplex.Hom.τ₃ e.hom_inv_id
  id := by
    simp only [Category.assoc, e.inv.comm₁₂, ← e.hom.comm₂₃_assoc]
    rw [← comp_add]
    simp only [← Category.assoc, ← add_comp, h.id, Category.id_comp]
    exact congrArg ShortComplex.Hom.τ₂ e.hom_inv_id

section CechTotal

variable {A : Type u} [CommRing A]

private abbrev totalInt (A : Type u) [CommRing A] :=
  HomologicalComplex₂.totalFunctor (ModuleCat.{u} A) (.up ℤ) (.up ℤ) (.up ℤ)

private instance : (totalInt A).PreservesZeroMorphisms where
  map_zero K L := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change _ ≫ (HomologicalComplex₂.total.map (0 : K ⟶ L) (.up ℤ)).f n =
      K.ιTotal (.up ℤ) p q n hpq ≫ 0
    rw [HomologicalComplex₂.ιTotal_map]
    simp

private abbrev doubleEvalInt (A : Type u) [CommRing A] (p q : ℤ) :
    HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ) ⥤ ModuleCat.{u} A :=
  (HomologicalComplex.eval _ _ p) ⋙ HomologicalComplex.eval _ _ q

private theorem shortExact_totalInt
    (S : ShortComplex (HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ)))
    (hS : ∀ p q : ℤ, Nonempty (S.map (doubleEvalInt A p q)).Splitting) :
    (S.map (totalInt A)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let h p q := (hS p q).some
  let T := (S.map (totalInt A)).map (HomologicalComplex.eval _ _ n)
  let r : (S.X₂.total (.up ℤ)).X n ⟶ (S.X₁.total (.up ℤ)).X n := S.X₂.totalDesc (fun p q hpq =>
    (h p q).r ≫ S.X₁.ιTotal (.up ℤ) p q n hpq)
  let s : (S.X₃.total (.up ℤ)).X n ⟶ (S.X₂.total (.up ℤ)).X n := S.X₃.totalDesc (fun p q hpq =>
    (h p q).s ≫ S.X₂.ιTotal (.up ℤ) p q n hpq)
  let sp : T.Splitting :=
    { r := r
      s := s
      f_r := by
        apply HomologicalComplex₂.total.hom_ext
        intro p q hpq
        change _ ≫ (HomologicalComplex₂.total.map S.f (.up ℤ)).f n ≫ r =
          S.X₁.ιTotal (.up ℤ) p q n hpq ≫ 𝟙 _
        rw [HomologicalComplex₂.ιTotal_map_assoc]
        dsimp only [r]
        rw [HomologicalComplex₂.ι_totalDesc, ← Category.assoc]
        have hfr : (S.f.f p).f q ≫ (h p q).r = 𝟙 _ := (h p q).f_r
        rw [hfr, Category.id_comp, Category.comp_id]
      s_g := by
        apply HomologicalComplex₂.total.hom_ext
        intro p q hpq
        change _ ≫ s ≫ (HomologicalComplex₂.total.map S.g (.up ℤ)).f n =
          S.X₃.ιTotal (.up ℤ) p q n hpq ≫ 𝟙 _
        dsimp only [s]
        rw [HomologicalComplex₂.ι_totalDesc_assoc, Category.assoc,
          HomologicalComplex₂.ιTotal_map, ← Category.assoc]
        have hsg : (h p q).s ≫ (S.g.f p).f q = 𝟙 ((S.X₃.X p).X q) := (h p q).s_g
        rw [hsg, Category.id_comp, Category.comp_id]
      id := by
        apply HomologicalComplex₂.total.hom_ext
        intro p q hpq
        change _ ≫ (r ≫ (HomologicalComplex₂.total.map S.f (.up ℤ)).f n +
          (HomologicalComplex₂.total.map S.g (.up ℤ)).f n ≫ s) =
          S.X₂.ιTotal (.up ℤ) p q n hpq ≫ 𝟙 _
        rw [comp_add]
        dsimp only [r, s]
        rw [HomologicalComplex₂.ι_totalDesc_assoc, Category.assoc, HomologicalComplex₂.ιTotal_map_assoc,
          HomologicalComplex₂.ιTotal_map, HomologicalComplex₂.ι_totalDesc]
        let r' : (S.X₂.X p).X q ⟶ (S.X₁.X p).X q := (h p q).r
        let s' : (S.X₃.X p).X q ⟶ (S.X₂.X p).X q := (h p q).s
        have hsum : r' ≫ (S.f.f p).f q + (S.g.f p).f q ≫ s' = 𝟙 _ := (h p q).id
        simp only [← Category.assoc, ← add_comp, Category.comp_id]
        change (r' ≫ (S.f.f p).f q + (S.g.f p).f q ≫ s') ≫ _ = _
        rw [hsum, Category.id_comp] }
  exact sp.shortExact

variable {X : SchemeOverRing A} {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens)

private instance flipFunctor_additive :
    (HomologicalComplex₂.flipFunctor (ModuleCat.{u} A) (.up ℕ) (.up ℕ)).Additive where
  map_add := by intros; ext i j; rfl

private abbrev doubleCechFunctor :
    CochainComplex X.left.Modules ℕ ⥤ HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ) :=
  ((sheafCechFunctor U).mapHomologicalComplex (.up ℕ)) ⋙
    HomologicalComplex₂.flipFunctor (ModuleCat.{u} A) (.up ℕ) (.up ℕ)

private abbrev extendInner (A : Type u) [CommRing A] :=
  (extendCochainsToInt (ModuleCat.{u} A)).mapHomologicalComplex (.up ℕ)

private abbrev extendDoubleFunctor (A : Type u) [CommRing A] :=
  extendInner A ⋙ extendCochainsToInt (CochainComplex (ModuleCat.{u} A) ℤ)

private theorem extendedDoubleMap_components {K L : CochainComplex X.left.Modules ℕ}
    (f : K ⟶ L) (p q : ℕ) :
    ((((doubleCechFunctor U ⋙ extendDoubleFunctor A).map f).f (p : ℤ)).f (q : ℤ)) ≫
        (doubleComponentIso (resolutionDouble U L) p q).hom =
      (doubleComponentIso (resolutionDouble U K) p q).hom ≫
        ((sheafCechFunctor U).map (f.f q)).f p := by
  let a := (doubleCechFunctor U).map f
  let b := (extendInner A).map a
  change ((extendMap b intEmbedding).f (p : ℤ)).f (q : ℤ) ≫ _ = _
  rw [extendMap_f b intEmbedding (intEmbedding_f p)]
  simp only [comp_f, doubleComponentIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.eval_map, Category.assoc]
  change _ ≫ (extendMap (a.f p) intEmbedding).f (q : ℤ) ≫ _ = _
  rw [extendMap_f (a.f p) intEmbedding (intEmbedding_f q)]
  let o (T : CochainComplex X.left.Modules ℕ) :=
    (HomologicalComplex.eval _ _ (q : ℤ)).mapIso
      (((extendInner A).obj (resolutionDouble U T)).extendXIso intEmbedding (intEmbedding_f p))
  let t (T : CochainComplex X.left.Modules ℕ) :=
    ((resolutionDouble U T).X p).extendXIso intEmbedding (intEmbedding_f q)
  change (o K).hom ≫ ((t K).hom ≫ (a.f p).f q ≫ (t L).inv) ≫
      (o L).inv ≫ (o L).hom ≫ (t L).hom =
    (o K).hom ≫ (t K).hom ≫ ((sheafCechFunctor U).map (f.f q)).f p
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem splits_extendedDouble (S : ShortComplex (CochainComplex X.left.Modules ℕ))
    (hS : ∀ q : ℕ, Nonempty (S.map (HomologicalComplex.eval _ _ q)).Splitting) :
    ∀ p q : ℤ, Nonempty
      (((S.map (doubleCechFunctor U ⋙ extendDoubleFunctor A)).map (doubleEvalInt A p q)).Splitting) := by
  intro p q
  let D := doubleCechFunctor U ⋙ extendDoubleFunctor A
  let T := (S.map D).map (doubleEvalInt A p q)
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    by_cases hq : 0 ≤ q
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      let E := (sheafCechFunctor U) ⋙ HomologicalComplex.eval _ _ p
      let P := (S.map (HomologicalComplex.eval _ _ q)).map E
      let e : T ≅ P := ShortComplex.isoMk
        (doubleComponentIso (resolutionDouble U S.X₁) p q)
        (doubleComponentIso (resolutionDouble U S.X₂) p q)
        (doubleComponentIso (resolutionDouble U S.X₃) p q)
        (extendedDoubleMap_components U S.f p q).symm
        (extendedDoubleMap_components U S.g p q).symm
      exact ⟨splittingOfIso e ((hS q).some.map E)⟩
    · have hZ (K : CochainComplex X.left.Modules ℕ) : IsZero (((D.obj K).X (p : ℤ)).X q) :=
        let e := (HomologicalComplex.eval _ _ q).mapIso
          (((extendInner A).obj (resolutionDouble U K)).extendXIso intEmbedding (intEmbedding_f p))
        (((resolutionDouble U K).X p).isZero_extend_X intEmbedding q
          (fun k hk => by rw [intEmbedding_f] at hk; omega)).of_iso e
      exact ⟨{
        r := 0
        s := 0
        f_r := (hZ S.X₁).eq_of_src _ _
        s_g := (hZ S.X₃).eq_of_src _ _
        id := (hZ S.X₂).eq_of_src _ _ }⟩
  · have hZ (K : CochainComplex X.left.Modules ℕ) : IsZero (((D.obj K).X p).X q) :=
      (HomologicalComplex.eval _ _ q).map_isZero
        (((extendInner A).obj (resolutionDouble U K)).isZero_extend_X intEmbedding p
          (fun k hk => by rw [intEmbedding_f] at hk; omega))
    exact ⟨{
      r := 0
      s := 0
      f_r := (hZ S.X₁).eq_of_src _ _
      s_g := (hZ S.X₃).eq_of_src _ _
      id := (hZ S.X₂).eq_of_src _ _ }⟩

private abbrev extendedCechFunctor := doubleCechFunctor U ⋙ extendDoubleFunctor A

private abbrev totalCechFunctor := extendedCechFunctor U ⋙ totalInt A

private theorem shortExact_totalCech
    (S : ShortComplex (CochainComplex X.left.Modules ℕ))
    (hS : ∀ q : ℕ, Nonempty (S.map (HomologicalComplex.eval _ _ q)).Splitting) :
    (S.map (totalCechFunctor U)).ShortExact :=
  shortExact_totalInt _ (splits_extendedDouble U S hS)

end CechTotal

section CechConnectingMap

variable {A : Type u} [CommRing A] (X : SchemeOverRing A)
  {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens)

private abbrev sectionsOnCochains := (sectionsFunctor X).mapHomologicalComplex (.up ℕ)
private abbrev extendModuleCochains := extendCochainsToInt (ModuleCat.{u} A)
private abbrev cechResolutionTotal := totalCechFunctor U

private theorem totalMap_on_summand {K L : CochainComplex X.left.Modules ℕ}
    (l : K ⟶ L) (p q n : ℕ) (h : (p : ℤ) + (q : ℤ) = n) :
    (doubleComponentIso (resolutionDouble U K) p q).inv ≫
      (extendDouble (resolutionDouble U K)).ιTotal (.up ℤ) (p : ℤ) (q : ℤ) (n : ℤ) h ≫
      ((cechResolutionTotal X U).map l).f (n : ℤ) =
      ((sheafCechFunctor U).map (l.f q)).f p ≫
        (doubleComponentIso (resolutionDouble U L) p q).inv ≫
        (extendDouble (resolutionDouble U L)).ιTotal (.up ℤ) (p : ℤ) (q : ℤ) (n : ℤ) h := by
  let t : extendDouble (resolutionDouble U K) ⟶ extendDouble (resolutionDouble U L) :=
    (extendedCechFunctor U).map l
  change _ ≫ _ ≫ (HomologicalComplex₂.total.map t (.up ℤ)).f (n : ℤ) = _
  erw [HomologicalComplex₂.ιTotal_map]
  let D := extendDouble (resolutionDouble U L)
  let oK := doubleComponentIso (resolutionDouble U K) p q
  let oL := doubleComponentIso (resolutionDouble U L) p q
  let i := D.ιTotal (.up ℤ) (p : ℤ) (q : ℤ) (n : ℤ) h
  suffices H : oK.inv ≫ (t.f (p : ℤ)).f (q : ℤ) =
      ((sheafCechFunctor U).map (l.f q)).f p ≫ oL.inv by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ i) H).trans (Category.assoc _ _ _))
  apply (cancel_mono oL.hom).mp
  have ht : (t.f (p : ℤ)).f (q : ℤ) ≫ oL.hom =
      oK.hom ≫ ((sheafCechFunctor U).map (l.f q)).f p :=
    extendedDoubleMap_components U l p q
  rw [Category.assoc, Category.assoc, ht, oK.inv_hom_id_assoc, oL.inv_hom_id]
  exact (Category.comp_id _).symm

private theorem map_augmentations {F G : X.left.Modules}
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (f : F ⟶ G) (l : I.cocomplex ⟶ J.cocomplex)
    (hl : I.ι.f 0 ≫ l.f 0 = f ≫ J.ι.f 0)
    (a : extendModuleCochains.obj ((sectionsOnCochains X).obj I.cocomplex) ⟶ (cechResolutionTotal X U).obj I.cocomplex)
    (b : extendModuleCochains.obj (SheafCech U F) ⟶ (cechResolutionTotal X U).obj I.cocomplex)
    (a' : extendModuleCochains.obj ((sectionsOnCochains X).obj J.cocomplex) ⟶ (cechResolutionTotal X U).obj J.cocomplex)
    (b' : extendModuleCochains.obj (SheafCech U G) ⟶ (cechResolutionTotal X U).obj J.cocomplex)
    (ha : ∀ q : ℕ, a.f (q : ℤ) =
      (((sectionsOnCochains X).obj I.cocomplex).extendXIso intEmbedding (intEmbedding_f q)).hom ≫
        sectionAugmentation U (I.cocomplex.X q) ≫
        (doubleComponentIso (resolutionDouble U I.cocomplex) 0 q).inv ≫
        (extendDouble (resolutionDouble U I.cocomplex)).ιTotal (.up ℤ) 0 (q : ℤ) (q : ℤ)
          (zero_add _))
    (ha' : ∀ q : ℕ, a'.f (q : ℤ) =
      (((sectionsOnCochains X).obj J.cocomplex).extendXIso intEmbedding (intEmbedding_f q)).hom ≫
        sectionAugmentation U (J.cocomplex.X q) ≫
        (doubleComponentIso (resolutionDouble U J.cocomplex) 0 q).inv ≫
        (extendDouble (resolutionDouble U J.cocomplex)).ιTotal (.up ℤ) 0 (q : ℤ) (q : ℤ)
          (zero_add _))
    (hb : ∀ p : ℕ, b.f (p : ℤ) =
      ((SheafCech U F).extendXIso intEmbedding (intEmbedding_f p)).hom ≫
        ((sheafCechFunctor U).map (I.ι.f 0)).f p ≫
        (doubleComponentIso (resolutionDouble U I.cocomplex) p 0).inv ≫
        (extendDouble (resolutionDouble U I.cocomplex)).ιTotal (.up ℤ) (p : ℤ) 0 (p : ℤ)
          (add_zero _))
    (hb' : ∀ p : ℕ, b'.f (p : ℤ) =
      ((SheafCech U G).extendXIso intEmbedding (intEmbedding_f p)).hom ≫
        ((sheafCechFunctor U).map (J.ι.f 0)).f p ≫
        (doubleComponentIso (resolutionDouble U J.cocomplex) p 0).inv ≫
        (extendDouble (resolutionDouble U J.cocomplex)).ιTotal (.up ℤ) (p : ℤ) 0 (p : ℤ)
          (add_zero _)) :
    a ≫ (cechResolutionTotal X U).map l = extendModuleCochains.map ((sectionsOnCochains X).map l) ≫ a' ∧
    b ≫ (cechResolutionTotal X U).map l = extendModuleCochains.map ((sheafCechFunctor U).map f) ≫ b' := by
  constructor
  · apply HomologicalComplex.hom_ext
    intro q
    by_cases hq : 0 ≤ q
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      change a.f (q : ℤ) ≫ ((cechResolutionTotal X U).map l).f (q : ℤ) =
        (extendMap ((sectionsOnCochains X).map l) intEmbedding).f (q : ℤ) ≫ a'.f (q : ℤ)
      rw [ha q, ha' q, extendMap_f _ _ (intEmbedding_f q)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      erw [totalMap_on_summand X U l 0 q q (zero_add _)]
      rw [← Category.assoc (sectionAugmentation U _) _ _]
      rw [(sectionAugmentation_naturality U (l.f q)).symm]
      rfl
    · exact (((sectionsOnCochains X).obj I.cocomplex).isZero_extend_X intEmbedding q
        (fun i hi => by rw [intEmbedding_f] at hi; omega)).eq_of_src _ _
  · apply HomologicalComplex.hom_ext
    intro p
    by_cases hp : 0 ≤ p
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      change b.f (p : ℤ) ≫ ((cechResolutionTotal X U).map l).f (p : ℤ) =
        (extendMap ((sheafCechFunctor U).map f) intEmbedding).f (p : ℤ) ≫ b'.f (p : ℤ)
      rw [hb p, hb' p, extendMap_f _ _ (intEmbedding_f p)]
      simp only [Category.assoc]
      erw [totalMap_on_summand X U l p 0 p (add_zero _)]
      have hw := congrArg (fun k => ((sheafCechFunctor U).map k).f p) hl
      simp only [Functor.map_comp, comp_f] at hw
      rw [reassoc_of% hw]
      erw [Iso.inv_hom_id_assoc]
      rfl
    · exact ((SheafCech U F).isZero_extend_X intEmbedding p
        (fun i hi => by rw [intEmbedding_f] at hi; omega)).eq_of_src _ _

private theorem succCochainRel (n : ℕ) :
    (ComplexShape.up ℤ).Rel (n : ℤ) ((n + 1 : ℕ) : ℤ) := by
  change (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ)
  simp

set_option maxHeartbeats 1000000 in
/-- The two augmentations into the Čech totalization identify the connecting maps. -/
private theorem orderedCech_connectingMap (S : ShortComplex X.left.Modules)
    (R : ShortExactResolution S) (n : ℕ)
    (e₁ : (cohomology X (n + 1)).obj S.X₁ ≅ (SheafCech U S.X₁).homology (n + 1))
    (e₂ : (cohomology X n).obj S.X₂ ≅ (SheafCech U S.X₂).homology n)
    (e₃ : (cohomology X n).obj S.X₃ ≅ (SheafCech U S.X₃).homology n)
    (he₁ : IsComparisonFromResolution U R.I₁ (n + 1) e₁)
    (he₂ : IsComparisonFromResolution U R.I₂ n e₂)
    (he₃ : IsComparisonFromResolution U R.I₃ n e₃)
    (hC : (S.map (sheafCechFunctor U)).ShortExact) :
    ∃ hΓ : (R.row.map (sectionsOnCochains X)).ShortExact,
      e₃.hom ≫ hC.δ n (n + 1) rfl ≫ e₁.inv =
        (R.I₃.isoRightDerivedObj (sectionsFunctor X) n).hom ≫ hΓ.δ n (n + 1) rfl ≫
          (R.I₁.isoRightDerivedObj (sectionsFunctor X) (n + 1)).inv := by
  have hΓ : (R.row.map (sectionsOnCochains X)).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro q
    exact ((R.splitting q).some.map (sectionsFunctor X)).shortExact
  refine ⟨hΓ, ?_⟩
  let C := S.map (sheafCechFunctor U)
  let G := R.row.map (sectionsOnCochains X)
  let T := R.row.map (cechResolutionTotal X U)
  have hT : T.ShortExact := shortExact_totalCech U R.row R.splitting
  obtain ⟨a₁, b₁, _, hb₁q, ha₁, hb₁, he₁⟩ := he₁
  obtain ⟨a₂, b₂, _, _, ha₂, hb₂, _⟩ := he₂
  obtain ⟨a₃, b₃, _, _, ha₃, hb₃, he₃⟩ := he₃
  obtain ⟨hA₁, hB₁⟩ := map_augmentations X U R.I₁ R.I₂ S.f R.f
    (by simpa only [CochainComplex.single₀_map_f_zero] using R.comm_f)
    a₁ b₁ a₂ b₂ ha₁ ha₂ hb₁ hb₂
  obtain ⟨hA₂, hB₂⟩ := map_augmentations X U R.I₂ R.I₃ S.g R.g
    (by simpa only [CochainComplex.single₀_map_f_zero] using R.comm_g)
    a₂ b₂ a₃ b₃ ha₂ ha₃ hb₂ hb₃
  let α : G.map extendModuleCochains ⟶ T :=
    { τ₁ := a₁
      τ₂ := a₂
      τ₃ := a₃
      comm₁₂ := hA₁
      comm₂₃ := hA₂ }
  let β : C.map extendModuleCochains ⟶ T :=
    { τ₁ := b₁
      τ₂ := b₂
      τ₃ := b₃
      comm₁₂ := hB₁
      comm₂₃ := hB₂ }
  let i := (n : ℤ)
  let j := ((n + 1 : ℕ) : ℤ)
  let hij := succCochainRel n
  let dC := (shortExact_extend hC).δ i j hij
  let dG := (shortExact_extend hΓ).δ i j hij
  let dT := hT.δ i j hij
  let HA1 := homologyMap a₁ j
  let HB1 := homologyMap b₁ j
  let HA3 := homologyMap a₃ i
  let HB3 := homologyMap b₃ i
  have hA : dG ≫ HA1 = HA3 ≫ dT :=
    HomologicalComplex.HomologySequence.δ_naturality α (shortExact_extend hΓ) hT i j hij
  have hB : dC ≫ HB1 = HB3 ≫ dT :=
    HomologicalComplex.HomologySequence.δ_naturality β (shortExact_extend hC) hT i j hij
  let c₁ := C.X₁.extendHomologyIso intEmbedding (intEmbedding_f (n + 1))
  let c₃ := C.X₃.extendHomologyIso intEmbedding (intEmbedding_f n)
  let g₁ := G.X₁.extendHomologyIso intEmbedding (intEmbedding_f (n + 1))
  let g₃ := G.X₃.extendHomologyIso intEmbedding (intEmbedding_f n)
  let r₁ := R.I₁.isoRightDerivedObj (sectionsFunctor X) (n + 1)
  let r₃ := R.I₃.isoRightDerivedObj (sectionsFunctor X) n
  let u₁ := e₁ ≪≫ c₁.symm
  let u₃ := e₃ ≪≫ c₃.symm
  let v₁ := r₁ ≪≫ g₁.symm
  let v₃ := r₃ ≪≫ g₃.symm
  have h₁ : u₁.hom ≫ HB1 = v₁.hom ≫ HA1 := he₁
  have h₃ : u₃.hom ≫ HB3 = v₃.hom ≫ HA3 := he₃
  have hd : u₃.hom ≫ dC = v₃.hom ≫ dG ≫ v₁.inv ≫ u₁.hom := by
    letI : QuasiIso b₁ := hb₁q
    letI : IsIso HB1 := inferInstanceAs (IsIso (homologyMap b₁ j))
    apply (cancel_mono HB1).mp
    simp only [Category.assoc]
    erw [hB, reassoc_of% h₃, ← hA, h₁, v₁.inv_hom_id_assoc]
  have hc : dC ≫ c₁.hom = c₃.hom ≫ hC.δ n (n + 1) rfl :=
    delta_extend hC n (n + 1) rfl hij
  have hg : dG ≫ g₁.hom = g₃.hom ≫ hΓ.δ n (n + 1) rfl :=
    delta_extend hΓ n (n + 1) rfl hij
  have h := congrArg (fun t => t ≫ c₁.hom ≫ e₁.inv) hd
  simpa only [u₁, u₃, v₁, v₃, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id, reassoc_of% hc, reassoc_of% hg] using h

end CechConnectingMap

section ReductionComparison

variable {A : Type u} [CommRing A]

private theorem exact_of_module_isos {P Q R P₁ Q₁ R₁ : ModuleCat.{u} A}
    (eP : P ≅ P₁) (eQ : Q ≅ Q₁) (eR : R ≅ R₁)
    {f : P ⟶ Q} {g : Q ⟶ R} {f₁ : P₁ ⟶ Q₁} {g₁ : Q₁ ⟶ R₁}
    (hf : f ≫ eQ.hom = eP.hom ≫ f₁) (hg : g ≫ eR.hom = eQ.hom ≫ g₁)
    (hex : Function.Exact f₁ g₁) : Function.Exact f g := by
  intro x
  have ha (z : P) : eQ.hom (f z) = f₁ (eP.hom z) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hf) z
  have hb : eR.hom (g x) = g₁ (eQ.hom x) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hg) x
  have hi (M N : ModuleCat A) (e : M ≅ N) : Function.Injective e.hom :=
    e.toLinearEquiv.injective
  constructor
  · intro hz
    have hy : g₁ (eQ.hom x) = 0 := by rw [← hb, hz, map_zero]
    obtain ⟨y, hy⟩ := (hex _).mp hy
    obtain ⟨z, rfl⟩ := eP.toLinearEquiv.surjective y
    exact ⟨z, hi _ _ eQ ((ha z).trans hy)⟩
  · rintro ⟨z, rfl⟩
    apply hi _ _ eR
    rw [map_zero, hb, ha, hex.apply_apply_eq_zero]

private theorem smul_id_comm {P Q : ModuleCat.{u} A} (a : A) (f : P ⟶ Q) :
    (a • 𝟙 P : P ⟶ P) ≫ f = f ≫ (a • 𝟙 Q : Q ⟶ Q) := by
  apply ModuleCat.hom_ext
  ext x
  change f (a • x) = a • f x
  exact f.hom.map_smul a x

variable {B : Type u} [CommRing B] (φ : A →+* B) (a : A) (X : SchemeOverRing A)
    (F : X.left.Modules)

local notation "j" => fibreProjection φ X
local notation "G" => fibreSheaf φ X F
local notation "P" => (Scheme.Modules.pushforward j).obj G
local notation "η" => fibreCoefficientMap φ X F

/-- Assemble principal reduction from the short exact coefficient sequence
and its exactness on affine sections. -/
theorem cohomologyReduction_of_affineSections [IsClosedImmersion j]
    (hzero : multiply X a F ≫ η = 0)
    (hinj : ∀ U : X.left.Opens, IsAffineOpen U → Function.Injective
      ((multiply X a F).app U))
    (hex : ∀ U : X.left.Opens, IsAffineOpen U → Function.Exact
      ((multiply X a F).app U) ((η).app U))
    (hsurj : ∀ U : X.left.Opens, IsAffineOpen U → Function.Surjective ((η).app U))
    (hF : ∀ {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens),
      IsFiniteAffineCover U → IntersectionAcyclic U F)
    (hP : ∀ {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens),
      IsFiniteAffineCover U → IntersectionAcyclic U P) :
    CohomologyReduction φ a X F := by
  let S := ShortComplex.mk (multiply X a F) η hzero
  have hSheaves : S.ShortExact := shortExact_of_affineSections S hinj hex hsurj
  refine ⟨hzero, hSheaves, exists_shortExactResolution hSheaves, ?_⟩
  intro Idx _ _ U hU
  let unit : F ⟶ P := η
  obtain ⟨hq, hred⟩ := shortExactCechReduction
    (U := U) a (coefficientPresheafMap unit)
    (fun n e => by
      exact hinj (tupleOpen U e) (hU.2 n e))
    (fun n e => by
      exact hex (tupleOpen U e) (hU.2 n e))
    (fun n e => hsurj (tupleOpen U e) (hU.2 n e))
  have hmul : (sheafCechFunctor U).map S.f = a • 𝟙 (SheafCech U F) := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    rfl
  have hS : (S.map (sheafCechFunctor U)).ShortExact := by
    change (ShortComplex.mk ((sheafCechFunctor U).map S.f)
      ((sheafCechFunctor U).map unit) _).ShortExact
    revert hred
    revert hq
    rw [← hmul]
    intro _ hred
    exact hred
  refine ⟨hmul, hS, fun n => ?_⟩
  obtain ⟨cmp, hc, hnat, _⟩ :=
    LinearAlgebraicGroups.OrderedCechComparison.orderedCechComparison.{u}
  obtain ⟨cFull, hcFull⟩ :=
    LinearAlgebraicGroups.ClosedImmersionCohomology.comparison φ j (fibreProjection_over φ X) n
  let c := cFull.app G
  let e₀ := cmp X U hU.1 F (hF U hU) n
  let e₁ := cmp X U hU.1 F (hF U hU) (n + 1)
  let d := cmp X U hU.1 P (hP U hU) n
  let eK := c.symm ≪≫ d
  let r := (cohomology X n).map unit ≫ c.hom
  let δ := c.inv ≫ d.hom ≫ hS.δ n (n + 1) rfl ≫ e₁.inv
  let q := homologyMap ((sheafCechFunctor U).map unit) n
  let b := hS.δ n (n + 1) rfl
  have hr : r ≫ eK.hom = e₀.hom ≫ q := by
    simpa only [r, eK, e₀, d, q, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc] using hnat X U hU.1 unit (hF U hU) (hP U hU) n
  have hb : δ ≫ e₁.hom = eK.hom ≫ b := by
    simp [δ, eK, b]
  have hm (i : ℕ) : homologyMap ((sheafCechFunctor U).map S.f) i =
      a • 𝟙 ((SheafCech U F).homology i) :=
    (congrArg (fun k : SheafCech U F ⟶ SheafCech U F => homologyMap k i) hmul).trans
      (homologyMap_mul (SheafCech U F) a i)
  have h₀ : Function.Exact (a • 𝟙 ((SheafCech U F).homology n) : _ ⟶ _) q := by
    have := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.homology_exact₂ n)
    change Function.Exact (homologyMap ((sheafCechFunctor U).map S.f) n) q at this
    simpa only [hm n] using! this
  have h₁ : Function.Exact q b :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ n (n + 1) rfl)
  have h₂ : Function.Exact b (a • 𝟙 ((SheafCech U F).homology (n + 1)) : _ ⟶ _) := by
    have := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ n (n + 1) rfl)
    change Function.Exact b (homologyMap ((sheafCechFunctor U).map S.f) (n + 1)) at this
    simpa only [hm (n + 1)] using! this
  have h₀' := exact_of_module_isos e₀ e₀ eK (smul_id_comm a e₀.hom) hr h₀
  have h₁' := exact_of_module_isos e₀ eK e₁ hr hb h₁
  have h₂' := exact_of_module_isos eK e₁ e₁ hb (smul_id_comm a e₁.hom) h₂
  have range_ker {M N O : ModuleCat.{u} A} {f : M ⟶ N} {g : N ⟶ O}
      (h : Function.Exact f g) : LinearMap.range f.hom = LinearMap.ker g.hom := by
    ext x
    exact (h x).symm
  obtain ⟨inc, conn, hinc, hconn, hi, he, hs⟩ :=
    reductionOfLongExact a r δ (range_ker h₀') h₁' (range_ker h₂')
  have hBoundary : IsCohomologyBoundary X S n (d.hom ≫ hS.δ n (n + 1) rfl ≫ e₁.inv) := by
    intro R
    exact orderedCech_connectingMap X U S R n e₁ e₀ d
      (hc X U hU.1 F (hF U hU) R.I₁ (n + 1))
      (hc X U hU.1 F (hF U hU) R.I₂ n)
      (hc X U hU.1 P (hP U hU) R.I₃ n) hS
  exact ⟨c, e₁, d, inc, conn,
    (fun J I => ⟨(hcFull G J I).1, fun l hl => ((hcFull G J I).2 l hl).2⟩),
    (fun I => hc X U hU.1 F (hF U hU) I (n + 1)),
    (fun J => hc X U hU.1 P (hP U hU) J n),
    hBoundary, hinc, hconn, hi, he, hs⟩

end ReductionComparison

section FlatComparison

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

private abbrev extension := ModuleCat.extendScalars.{u,u,u} φ
private abbrev restriction := ModuleCat.restrictScalars.{u} φ
private abbrev scalarAdjunction := ModuleCat.extendRestrictScalarsAdj.{u,u,u} φ

/-- Scalar-extension adjunction on cochain maps, defined componentwise. -/
def extendCochainMap {C : CochainComplex (ModuleCat.{u} A) ℕ}
    {D : CochainComplex (ModuleCat.{u} B) ℕ}
    (t : C ⟶ ((restriction φ).mapHomologicalComplex (.up ℕ)).obj D) :
    ((extension φ).mapHomologicalComplex (.up ℕ)).obj C ⟶ D where
  f i := ((scalarAdjunction φ).homEquiv _ _).symm (t.f i)
  comm' i j _ := by
    apply ((scalarAdjunction φ).homEquiv (C.X i) (D.X j)).injective
    change (scalarAdjunction φ).homEquiv _ _
        (((scalarAdjunction φ).homEquiv (C.X i) (D.X i)).symm (t.f i) ≫ D.d i j) =
      (scalarAdjunction φ).homEquiv _ _
        ((extension φ).map (C.d i j) ≫
          ((scalarAdjunction φ).homEquiv (C.X j) (D.X j)).symm (t.f j))
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact t.comm i j

private theorem extendCochainMap_adj {C : CochainComplex (ModuleCat.{u} A) ℕ}
    {D : CochainComplex (ModuleCat.{u} B) ℕ}
    (t : C ⟶ ((restriction φ).mapHomologicalComplex (.up ℕ)).obj D) (i : ℕ) :
    (scalarAdjunction φ).homEquiv (C.X i) (D.X i) ((extendCochainMap φ t).f i) = t.f i :=
  Equiv.apply_symm_apply _ _

private theorem identityHomologyIso {C : Type*} [Category* C] [Abelian C]
    (T : ShortComplex C) : (T.mapHomologyIso (𝟭 C)).hom = 𝟙 T.homology := by
  let L := T.homologyData.left
  let M := L.map (𝟭 C)
  change M.homologyIso.hom = _
  apply (cancel_epi (T.map (𝟭 C)).homologyπ).mp
  change _ ≫ M.homologyIso.hom = (T.map (𝟭 C)).homologyπ ≫ 𝟙 _
  rw [Category.comp_id, M.homologyπ_comp_homologyIso_hom]
  have hc : M.cyclesIso.hom = L.cyclesIso.hom := by
    apply (cancel_mono M.i).mp
    exact M.cyclesIso_hom_comp_i.trans L.cyclesIso_hom_comp_i.symm
  rw [hc]
  change L.cyclesIso.hom ≫ L.π = T.homologyπ
  have hh : L.homologyIso.hom = 𝟙 T.homology := T.leftHomologyIso.inv_hom_id
  exact L.homologyπ_comp_homologyIso_hom.symm.trans (by rw [hh, Category.comp_id])

/-- The adjunction on cochain maps induces the same adjunction on homology
when scalar extension is exact. -/
theorem homology_extendCochainMap (hφ : φ.Flat)
    {C : CochainComplex (ModuleCat.{u} A) ℕ} {D : CochainComplex (ModuleCat.{u} B) ℕ}
    (t : C ⟶ ((restriction φ).mapHomologicalComplex (.up ℕ)).obj D) (n : ℕ) :
    (scalarAdjunction φ).homEquiv _ _
        ((flatExtensionHomologyIso φ hφ C n).hom ≫ homologyMap (extendCochainMap φ t) n) =
      homologyMap t n ≫ (restrictCohomologyIso φ D n).inv := by
  let E := extension φ
  let R := restriction φ
  let a := scalarAdjunction φ
  letI : PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  let T := C.sc n
  let W := D.sc n
  let e := (shortComplexFunctor (ModuleCat.{u} B) (.up ℕ) n).map (extendCochainMap φ t)
  let q := (shortComplexFunctor (ModuleCat.{u} A) (.up ℕ) n).map t
  have hq : T.mapNatTrans a.unit ≫ R.mapShortComplex.map e = q := by
    ext : 1
    all_goals
      exact (a.homEquiv_unit _ _ _).symm.trans (extendCochainMap_adj φ t _)
  change a.homEquiv _ _ ((T.mapHomologyIso E).inv ≫ ShortComplex.homologyMap e) =
    ShortComplex.homologyMap q ≫ (W.mapHomologyIso R).hom
  rw [← hq, ShortComplex.homologyMap_comp, Category.assoc,
    ShortComplex.mapHomologyIso_hom_naturality, ShortComplex.homologyMap_mapNatTrans,
    identityHomologyIso, a.homEquiv_unit, R.map_comp]
  let M := (T.homologyData.left.map E).map R
  let N := T.homologyData.left.map (E ⋙ R)
  have hc : M.cyclesIso.hom = N.cyclesIso.hom := by
    apply (cancel_mono N.i).mp
    exact M.cyclesIso_hom_comp_i.trans N.cyclesIso_hom_comp_i.symm
  have hh : M.homologyIso.hom = N.homologyIso.hom := by
    apply (cancel_epi (T.map (E ⋙ R)).homologyπ).mp
    erw [M.homologyπ_comp_homologyIso_hom, N.homologyπ_comp_homologyIso_hom]
    rw [hc]
    rfl
  have h := congrArg Iso.hom ((T.homologyData.left.map E).mapHomologyIso_eq R)
  change ((T.map E).mapHomologyIso R).hom =
    M.homologyIso.hom ≫ R.map (T.mapHomologyIso E).inv at h
  rw [hh] at h
  simp only [Category.assoc]
  erw [h]
  change a.unit.app T.homology ≫ R.map (T.mapHomologyIso E).inv ≫
      R.map (ShortComplex.homologyMap e) =
    a.unit.app T.homology ≫ (T.mapHomologyIso (E ⋙ R)).inv ≫
      (T.mapHomologyIso (E ⋙ R)).hom ≫ R.map (T.mapHomologyIso E).inv ≫
      R.map (ShortComplex.homologyMap e)
  rw [Iso.inv_hom_id_assoc]

variable (X : SchemeOverRing A) (F : X.left.Modules)
  {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens)

local notation "Y" => (changeBase φ).obj X
local notation "j" => fibreProjection φ X
local notation "G" => fibreSheaf φ X F
local notation "V" => pullbackCover j U
local notation "η" => fibreCoefficientMap φ X F
local notation "hf" => fibreProjection_over φ X

private theorem isIso_extendCechPullback [F.IsQuasicoherent] (hU : IsFiniteAffineCover U) :
    IsIso (extendCochainMap φ (cechPullback φ j hf U η)) := by
  classical
  let t := cechPullback φ j hf U η
  suffices ∀ n, IsIso ((extendCochainMap φ t).f n) from
    HomologicalComplex.Hom.isIso_of_components _
  intro n
  let J := Fin (n + 1) ↪o I
  let M (e : J) := localSections F (tupleOpen U e)
  let N (e : J) := localSections (X := Y) G (tupleOpen V e)
  letI : Finite J := Finite.of_injective (fun e : J => (e : Fin (n + 1) → I))
    DFunLike.coe_injective
  letI : Fintype J := Fintype.ofFinite J
  letI : Algebra A B := φ.toAlgebra
  let d (e : J) : (extension φ).obj (M e) ≅ N e := by
    let d₁ := localSectionsBaseChangeMap φ X F (tupleOpen U e)
    letI : IsIso d₁ := isIso_localSectionsBaseChangeMap φ X F (hU.2 n e)
    let d₂ := (coefficientPresheaf (X := Y) G).map (pullbackToIntersection j U e).op
    letI : IsIso (pullbackToIntersection j U e) :=
      inferInstanceAs (IsIso (eqToHom (tupleOpen_pullback j U e)))
    letI : IsIso d₂ := Functor.map_isIso _ _
    exact asIso d₁ ≪≫ asIso d₂
  let e : (extension φ).obj ((SheafCech U F).X n) ≅ (SheafCech V G).X n :=
    (TensorProduct.piRight A B B (fun e => M e) ≪≫ₗ
      LinearEquiv.piCongrRight (fun e => (d e).toLinearEquiv)).toModuleIso
  have he : (extendCochainMap φ t).f n = e.hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    funext k
    have ht := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (extendCochainMap_adj φ t n)) x
    change (extendCochainMap φ t).f n ((1 : B) ⊗ₜ[A,φ] x) = t.f n x at ht
    refine (congrFun ht k).trans ?_
    rw [cechPullback_apply]
    change _ = (d k).hom (TensorProduct.piRight A B B (fun e => M e)
      ((1 : B) ⊗ₜ[A] x) k)
    rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    change _ = (coefficientPresheaf (X := Y) G).map (pullbackToIntersection j U k).op
      (localSectionsBaseChangeMap φ X F (tupleOpen U k) ((1 : B) ⊗ₜ[A,φ] (x k)))
    rw [localSectionsBaseChangeMap_one_tmul]
    rfl
  exact he.symm ▸ inferInstance

private theorem cohomologyBaseChange_of_cover (hφ : φ.Flat)
    [F.IsQuasicoherent] (hU : IsFiniteAffineCover U) :
    CohomologyBaseChange φ X F := by
  let g := Spec.map (CommRingCat.ofHom φ)
  letI : Flat g := Flat.SpecMap_iff.mpr hφ
  letI : Flat j := MorphismProperty.pullback_fst _ _ (inferInstance : Flat g)
  letI : IsAffineHom j := MorphismProperty.pullback_fst _ _ (isAffineHom_of_isAffine g)
  letI : (G).IsQuasicoherent := isQuasicoherent_pullback_of_affine j F
  have hV : (⨆ i, V i) = ⊤ := (j).iSup_preimage_eq_top hU.1
  have hF : IntersectionAcyclic U F := intersectionAcyclic_of_affineOpens U hU.2 F
  have hG : IntersectionAcyclic V G := by
    apply intersectionAcyclic_of_affineOpens _ _ G
    intro n e
    rw [tupleOpen_pullback]
    exact isAffineOpen_fibrePreimage φ X (hU.2 n e)
  obtain ⟨c, _, _, hnat⟩ :=
    LinearAlgebraicGroups.OrderedCechComparison.orderedCechComparison.{u}
  intro n
  let E := extension φ
  let R := restriction φ
  let a := scalarAdjunction φ
  let cX := c X U hU.1 F hF n
  let cY := c Y V hV G hG n
  let t := cechPullback φ j hf U η
  letI : IsIso (extendCochainMap φ t) := isIso_extendCechPullback φ X F U hU
  let cH := flatExtensionHomologyIso φ hφ (SheafCech U F) n ≪≫
    homologyMapIso (asIso (extendCochainMap φ t)) n
  obtain ⟨m, hm, _⟩ := LinearAlgebraicGroups.FlatCohomology.flatCohomologyMap φ j hf η n
  have hm' : IsCohomologyMap φ j hf η n m := fun I J =>
    ⟨(hm I J).1, fun l hl => (hm I J).2 l hl⟩
  let JX := injectiveResolution F
  let JY := injectiveResolution G
  obtain ⟨l, hl⟩ := (hm' JX JY).1
  have h := hnat (X := X) («Y» := Y) U hU.1 φ j hf η hF hG JX JY l hl n
  change derivedMapOfLift φ j hf JX JY l n ≫ R.map cY.hom =
    cX.hom ≫ homologyMap t n ≫ (restrictCohomologyIso φ (SheafCech V G) n).inv at h
  rw [← (hm' JX JY).2 l hl] at h
  let e := E.mapIso cX ≪≫ cH ≪≫ cY.symm
  refine ⟨e, ?_⟩
  suffices H : a.homEquiv _ _ e.hom = m from H.symm ▸ hm'
  apply (cancel_mono (R.map cY.hom)).mp
  rw [h]
  change a.homEquiv _ _ (E.map cX.hom ≫ cH.hom ≫ cY.inv) ≫ R.map cY.hom = _
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right, Category.assoc, Category.assoc,
    ← R.map_comp, cY.inv_hom_id, R.map_id, Category.comp_id]
  exact congrArg (cX.hom ≫ ·) (homology_extendCochainMap φ hφ t n)

end FlatComparison

/-- Flat base change for the actual pullback of a quasi-coherent sheaf. -/
theorem flatBaseChange : FlatBaseChange.{u} := by
  intro A B _ _ φ hφ X _ _ F hF
  letI : F.IsQuasicoherent := hF
  obtain ⟨I, _, _, U, hU⟩ := finiteAffineCover (X := X.left)
  exact cohomologyBaseChange_of_cover φ X F U hφ hU

section PrincipalReduction

open Scheme.Modules

variable {A B : Type u} [CommRing A] [CommRing B]
  (φ : A →+* B) (a : A) (X : SchemeOverRing A) (F : X.left.Modules)

local notation "j" => fibreProjection φ X
local notation "G" => fibreSheaf φ X F
local notation "η" => fibreCoefficientMap φ X F

private theorem injective_multiply_sections [Flat X.hom]
    (ha : Function.Injective (a * · : A → A)) (hF : IsLocallyFree F)
    (W : X.left.Opens) : Function.Injective ((multiply X a F).app W) := by
  intro s t hst
  apply F.isSheaf.section_ext
  intro x hxW
  obtain ⟨U, hxU, K, ⟨e⟩⟩ := hF x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ W ⊓ U⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ W ⊓ U from ⟨hxW, hxU⟩) (W ⊓ U).2
  let hVW : V ≤ W := hVU.trans inf_le_left
  let q := hV.fromSpec
  let v := hV.isoSpec.inv ≫ X.left.homOfLE (hVU.trans inf_le_right)
  have hv : v ≫ U.ι = q := by
    rw [Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
  let e₁ := (restrictFunctorIsoPullback U.ι).app F
  let e₂ : (Scheme.Modules.pullback q).obj F ≅ SheafOfModules.free K :=
    (pullbackCongr hv).symm.app F ≪≫ (pullbackComp v U.ι).symm.app F ≪≫
      (Scheme.Modules.pullback v).mapIso (e₁.symm ≪≫ e) ≪≫
      (by
        haveI : (Opens.map v.base).IsRightAdjoint := v.opensFunctorAdjunction.isRightAdjoint
        exact SheafOfModules.pullbackObjFreeIso v.toRingCatSheafHom K)
  let R := Γ(X.left, V)
  let L := moduleSpecΓFunctor (R := R)
  let M : ModuleCat.{u} R := F.val.obj (op V)
  let M' : ModuleCat.{u} A := localSections F V
  let e₃ : M ≅ ModuleCat.of R (K →₀ R) :=
    affineSectionsRestriction hV F ≪≫ L.mapIso (e₂ ≪≫ (tildeFinsupp K).symm) ≪≫
      ((tilde.toTildeΓNatIso (R := R)).app (ModuleCat.of R (K →₀ R))).symm
  letI : Module.Flat R M := Module.Flat.of_linearEquiv e₃.toLinearEquiv
  letI : Algebra A R := (groundRingHomOpen X V).toAlgebra
  letI : Module.Flat A R := flat_groundRingHomOpen X hV
  letI : Module A M := M'.isModule
  letI : IsScalarTower A R M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Flat A M := Module.Flat.trans A R M
  have hreg : IsRegular a := isLeftRegular_iff_isRegular.mp ha
  have hi : Function.Injective (a • · : M' → M') :=
    Module.Flat.isSMulRegular_of_isRegular (M := M) hreg
  refine ⟨V, hVW, hxV, ?_⟩
  change localRestriction F (homOfLE hVW) s = localRestriction F (homOfLE hVW) t
  apply hi
  change a • (localRestriction F (homOfLE hVW) s) =
    a • (localRestriction F (homOfLE hVW) t)
  rw [← _root_.map_smul, ← _root_.map_smul]
  exact congrArg (localRestriction F (homOfLE hVW)) hst

private theorem multiply_comp_fibreCoefficientMap (ha : φ a = 0) :
    multiply X a F ≫ η = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext s : 1
  let z : (G).val.obj (op (j ⁻¹ᵁ W.unop)) := (η).val.app W s
  let r := groundRingHomOpen X W.unop a
  have hr : ((j).app W.unop) r = 0 := by
    have h := DFunLike.congr_fun (groundRingHomOpen_over φ j (fibreProjection_over φ X) W.unop) a
    exact h.trans (by simp [ha])
  change (η).val.app W (r • s) = 0
  have h := ((η).val.app W).hom.map_smul r s
  change (η).val.app W (r • s) = ((j).app W.unop) r • z at h
  rw [h, hr, zero_smul]

/-- Principal reduction for a flat scheme and a locally free quasi-coherent sheaf. -/
theorem principalReduction : PrincipalReduction.{u} := by
  intro A B _ _ φ a ha hsurj hker X _ _ _ F hF hl
  letI : F.IsQuasicoherent := hF
  let g := Spec.map (CommRingCat.ofHom φ)
  let J := fibreProjection φ X
  let G' := fibreSheaf φ X F
  let P' := (Scheme.Modules.pushforward J).obj G'
  let η' := fibreCoefficientMap φ X F
  letI : IsClosedImmersion g := IsClosedImmersion.spec_of_surjective _ hsurj
  letI : IsClosedImmersion J := MorphismProperty.pullback_fst _ _ (inferInstance : IsClosedImmersion g)
  have ha0 : φ a = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton a)
  have hzero := multiply_comp_fibreCoefficientMap φ a X F ha0
  have hinj := injective_multiply_sections a X F ha hl
  have hred (W : X.left.Opens) (hW : IsAffineOpen W) :
      Function.Exact ((multiply X a F).app W) (η'.app W) ∧
        Function.Surjective (η'.app W) := by
    letI : Algebra A B := φ.toAlgebra
    let M := localSections F W
    let q (x : M) : (ModuleCat.extendScalars φ).obj M := (1 : B) ⊗ₜ[A,φ] x
    let e := localSectionsBaseChangeMap φ X F W
    letI : IsIso e := isIso_localSectionsBaseChangeMap φ X F hW
    have hb := ConcreteCategory.bijective_of_isIso e
    have hq (x : M) : e (q x) = η'.app W x :=
      localSectionsBaseChangeMap_one_tmul φ X F W x
    have ⟨hex, hqs⟩ := moduleReduction (M := M) a hsurj hker
    refine ⟨fun x => ?_, ?_⟩
    · change η'.app W x = 0 ↔ ∃ y : M, a • y = x
      rw [← hq, map_eq_zero_iff _ hb.injective]
      exact hex x
    · intro z
      obtain ⟨y, hy⟩ := hb.surjective z
      obtain ⟨x, hx⟩ := hqs y
      change q x = y at hx
      exact ⟨x, (hq x).symm.trans ((congrArg e hx).trans hy)⟩
  have hex (W : X.left.Opens) (hW : IsAffineOpen W) := (hred W hW).1
  have hsur (W : X.left.Opens) (hW : IsAffineOpen W) := (hred W hW).2
  let S := ShortComplex.mk (multiply X a F) η' hzero
  letI : P'.IsQuasicoherent :=
    isQuasicoherent_of_shortExact (S := S)
      (shortExact_of_affineSections S (fun W _ => hinj W) hex hsur)
  exact cohomologyReduction_of_affineSections φ a X F hzero (fun W _ => hinj W) hex hsur
    (fun U hU => intersectionAcyclic_of_affineOpens U hU.2 F)
    (fun U hU => intersectionAcyclic_of_affineOpens U hU.2 P')

end PrincipalReduction

section LocalizedIntegers

variable {m : ℤ} {p : ℕ}

@[simp]
private theorem rationalMap_algebraMap (hm : m ≠ 0) (z : ULift.{u} ℤ) :
    rationalMap hm (algebraMap (ULift.{u} ℤ) (IntegerAway.{u} m) z) =
      ULift.up (z.down : ℚ) := by
  unfold rationalMap
  rw [IsLocalization.Away.lift_eq]
  rfl

@[simp]
private theorem primeMap_algebraMap [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ m)
    (z : ULift.{u} ℤ) :
    primeMap hp (algebraMap (ULift.{u} ℤ) (IntegerAway.{u} m) z) =
      ULift.up (z.down : ZMod p) := by
  unfold primeMap
  rw [IsLocalization.Away.lift_eq]
  rfl

/-- The rational specialization uses the fraction field of the actual base ring. -/
theorem rationalMap_isFractionRing (hm : m ≠ 0) :
    letI : Algebra (IntegerAway.{u} m) (ULift.{u} ℚ) := (rationalMap hm).toAlgebra
    IsFractionRing (IntegerAway.{u} m) (ULift.{u} ℚ) := by
  letI : Algebra (IntegerAway.{u} m) (ULift.{u} ℚ) := (rationalMap hm).toAlgebra
  have hinj : Function.Injective (rationalMap.{u} hm) := by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (ULift.up m))]
    intro x y
    refine ⟨congrArg (rationalMap hm), fun h => ?_⟩
    rw [rationalMap_algebraMap, rationalMap_algebraMap] at h
    have hz := Int.cast_injective (α := ℚ) (congrArg ULift.down h)
    exact congrArg (algebraMap (ULift.{u} ℤ) (IntegerAway.{u} m)) (ULift.ext hz)
  letI : FaithfulSMul (IntegerAway.{u} m) (ULift.{u} ℚ) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field (IntegerAway m) (ULift ℚ) fun z => ?_
  refine ⟨algebraMap (ULift.{u} ℤ) (IntegerAway m) (ULift.up z.down.num),
    algebraMap (ULift.{u} ℤ) (IntegerAway m) (ULift.up (z.down.den : ℤ)), ?_⟩
  apply ULift.ext
  change z.down = (rationalMap hm (algebraMap (ULift.{u} ℤ) _ (ULift.up z.down.num))).down /
    (rationalMap hm (algebraMap (ULift.{u} ℤ) _ (ULift.up (z.down.den : ℤ)))).down
  rw [rationalMap_algebraMap, rationalMap_algebraMap]
  change z.down = (z.down.num : ℚ) / ((z.down.den : ℤ) : ℚ)
  simpa only [Int.cast_natCast] using z.down.num_div_den.symm

private theorem primeMap_surjective [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ m) :
    Function.Surjective (primeMap.{u} hp) := by
  intro z
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective z.down
  exact ⟨algebraMap (ULift.{u} ℤ) (IntegerAway m) (ULift.up n), by
    rw [primeMap_algebraMap]
    exact ULift.ext hn⟩

private theorem ker_primeMap [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ m) :
    RingHom.ker (primeMap.{u} hp) = Ideal.span {(p : IntegerAway.{u} m)} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, z, hz⟩ := IsLocalization.Away.surj (ULift.up.{u} m) x
    have hres := congrArg (primeMap hp) hz
    simp only [map_mul, RingHom.mem_ker.mp hx, zero_mul, primeMap_algebraMap] at hres
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z.down p).mp
      (congrArg ULift.down hres.symm)
    have hz' : z = (p : ULift.{u} ℤ) * ULift.up y := ULift.ext hy
    rw [hz', map_mul, map_natCast] at hz
    let a : IntegerAway.{u} m := algebraMap (ULift.{u} ℤ) (IntegerAway m) (ULift.up m)
    change x * a ^ n = _ at hz
    obtain ⟨b, hb⟩ := IsLocalization.Away.algebraMap_isUnit (S := IntegerAway.{u} m) (ULift.up m)
    rw [Ideal.mem_span_singleton]
    refine ⟨algebraMap (ULift.{u} ℤ) (IntegerAway m) (ULift.up y) * ↑((b ^ n)⁻¹), ?_⟩
    calc
      x = (x * ↑(b ^ n)) * ↑((b ^ n)⁻¹) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by
        rw [Units.val_pow_eq_pow_val, show (b : IntegerAway m) = a from hb, hz, mul_assoc]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    apply RingHom.mem_ker.mpr
    change (primeMap hp) (p : IntegerAway m) = 0
    rw [map_natCast]
    apply ULift.ext
    exact ZMod.natCast_self p

private theorem prime_regular [Fact p.Prime] (hm : m ≠ 0) :
    Function.Injective ((p : IntegerAway.{u} m) * · : IntegerAway.{u} m → IntegerAway.{u} m) := by
  letI : IsDomain (ULift.{u} ℤ) := Function.Injective.isDomain
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) ULift.ringEquiv.injective
  letI : IsDomain (IntegerAway.{u} m) :=
    Localization.Away.isDomain (show ULift.up.{u} m ≠ 0 from fun e => hm (congrArg ULift.down e))
  have hp : (p : IntegerAway.{u} m) ≠ 0 := by
    intro he
    have he' := congrArg (rationalMap hm) he
    rw [map_natCast, map_zero] at he'
    exact (Fact.out : p.Prime).ne_zero
      (Nat.cast_eq_zero.mp (congrArg ULift.down he' : (p : ℚ) = 0))
  intro x y h
  exact mul_left_cancel₀ hp h

/-- Generic and prime base change over the localization of the integers. -/
theorem arithmeticBaseChange : ArithmeticBaseChange.{u} := by
  intro m hm X _ _ F hF hl
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsSeparated (terminal.from X.left) := by
    rw [← terminal.comp_from X.hom]
    infer_instance
  have hflat : (rationalMap.{u} hm).Flat := by
    letI : Algebra (IntegerAway.{u} m) (ULift.{u} ℚ) := (rationalMap hm).toAlgebra
    letI := rationalMap_isFractionRing.{u} hm
    exact IsLocalization.flat (ULift.{u} ℚ) (nonZeroDivisors (IntegerAway.{u} m))
  refine ⟨flatBaseChange (rationalMap hm) hflat X F hF, ?_⟩
  intro p _ hp
  let φ := primeMap.{u} hp
  have hsurj := primeMap_surjective.{u} hp
  have hker := ker_primeMap.{u} hp
  let e := (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  refine ⟨⟨e, fun x => ?_⟩,
    principalReduction φ (p : IntegerAway m) (prime_regular hm) hsurj hker X F hF hl⟩
  change φ.quotientKerEquivOfSurjective hsurj
    (Ideal.quotEquivOfEq hker.symm (Ideal.Quotient.mk _ x)) = φ x
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

end LocalizedIntegers

end

end LinearAlgebraicGroups.Cohomology.ArithmeticCohomologyBaseChange
