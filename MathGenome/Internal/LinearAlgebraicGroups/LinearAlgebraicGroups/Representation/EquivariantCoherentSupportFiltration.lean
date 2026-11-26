import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantCoherentSupportFiltration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Support
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Pointwise

universe u

namespace LinearAlgebraicGroups.Representation.EquivariantCoherentSupportFiltration

open Specs.EquivariantAffineModules EquivariantAffineModules
open EquivariantCoherentClosedImage
open Specs.EquivariantCoherentSupportFiltration

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem pow_smul_eq_bot_of_support_subset
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I.FG)
    (hsupp : Module.support A M ⊆ PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ n : ℕ, I ^ n • (⊤ : Submodule A M) = ⊥ := by
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hsupp
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hsupp hI
  exact ⟨n, Submodule.le_annihilator_iff.mp (by rwa [Submodule.annihilator_top])⟩

private theorem classOf_mem_of_filtration
    {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k} {a : ModObj T.X X}
    (S : Submodule (CharacterRing T) (GZero a))
    (term quotient : ℕ → EquivariantCoherent a) (n : ℕ)
    (hzero : IsZero (term n).sheaf)
    (hadd : ∀ m < n, classOf (term m) = classOf (term (m + 1)) + classOf (quotient m))
    (hquot : ∀ m < n, classOf (quotient m) ∈ S) : classOf (term 0) ∈ S := by
  induction n generalizing term quotient with
  | zero => simpa only [classOf_isZero _ hzero] using S.zero_mem
  | succ n ih =>
    rw [hadd 0 (Nat.zero_lt_succ n)]
    exact S.add_mem (ih (fun m => term (m + 1)) (fun m => quotient (m + 1)) hzero
      (fun m hm => hadd (m + 1) (Nat.succ_lt_succ hm))
      (fun m hm => hquot (m + 1) (Nat.succ_lt_succ hm))) (hquot 0 (Nat.zero_lt_succ n))

/-- Evaluation of module sheaves as modules over the ring of the given open. -/
private abbrev ev {X : Scheme.{u}} (U : X.Opens) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, U) := SheafOfModules.evaluation _ (op U)

private theorem isIso_of_basis_app {X : Scheme.{u}} {F H : X.Modules} (m : F ⟶ H)
    {ι : Type u} (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (hm : ∀ z, IsIso ((ev (B z)).map m)) : IsIso m := by
  let G := SheafOfModules.toSheaf X.ringCatSheaf
  have h : IsIso (G.map m) := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (B := B) hB (φ := G.map m) ?_
    intro z
    let := hm z
    exact (forget₂ (ModuleCat Γ(X, B z)) Ab).map_isIso ((ev (B z)).map m)
  apply (isIso_iff_of_reflects_iso m (Scheme.Modules.toPresheaf X)).mp
  exact (TopCat.Sheaf.forget Ab X.carrier).map_isIso (G.map m)

private theorem tilde_map_on_basicOpen {R : CommRingCat.{u}}
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (r : R) :
    ((modulesSpecToSheaf.map (tilde.map f)).1.app (op (PrimeSpectrum.basicOpen r))).hom =
      IsLocalizedModule.map (Submonoid.powers r)
        (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
        (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom f.hom := by
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom
  ext x
  exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (tilde.toOpen_map_app f (PrimeSpectrum.basicOpen r))) x).trans
    (IsLocalizedModule.map_apply (Submonoid.powers r)
      (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
      (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom f.hom x).symm

private def tilde_map_ker_isLimit {R : CommRingCat.{u}}
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    IsLimit (KernelFork.ofι ((tilde.functor R).map (ModuleCat.kernelCone f).ι)
      (by rw [← Functor.map_comp, (ModuleCat.kernelCone f).condition, Functor.map_zero]) :
        KernelFork ((tilde.functor R).map f)) := by
  let K := ModuleCat.kernelCone f
  let L := tilde.functor R
  let w : L.map K.ι ≫ L.map f = 0 := by
    rw [← L.map_comp, K.condition, L.map_zero]
  let m := kernel.lift (L.map f) (L.map K.ι) w
  have hm : IsIso m := by
    apply isIso_of_basis_app m (fun r : R => PrimeSpectrum.basicOpen r)
      (by simpa only [Set.range_id] using (PrimeSpectrum.isBasis_basic_opens (R := R)))
    intro r
    let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
    let G := ev U
    have : PreservesFiniteLimits G := inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)))
    have hn : Function.Injective (G.map (L.map K.ι)) := by
      change Function.Injective ((modulesSpecToSheaf.map (tilde.map K.ι)).1.app
        (op (PrimeSpectrum.basicOpen r))).hom
      rw [tilde_map_on_basicOpen]
      exact IsLocalizedModule.map_injective _ _ _ _
        Subtype.val_injective
    have he : Function.Exact (G.map (L.map K.ι)).hom (G.map (L.map f)).hom := by
      change Function.Exact ((modulesSpecToSheaf.map (tilde.map K.ι)).1.app
        (op (PrimeSpectrum.basicOpen r))).hom
        ((modulesSpecToSheaf.map (tilde.map f)).1.app (op (PrimeSpectrum.basicOpen r))).hom
      rw [tilde_map_on_basicOpen, tilde_map_on_basicOpen]
      exact IsLocalizedModule.map_exact _ _ _ _ _ _ (LinearMap.exact_subtype_ker_map f.hom)
    have hG : IsLimit (KernelFork.ofι (G.map (L.map K.ι))
        (show G.map (L.map K.ι) ≫ G.map (L.map f) = 0 by
          rw [← G.map_comp, w, G.map_zero])) :=
      ModuleCat.isLimitKernelFork _ _ he hn
    have hG' := isLimitForkMapOfIsLimit' G (kernel.condition (L.map f)) (kernelIsKernel _)
    let iso := hG.conePointUniqueUpToIso hG'
    have heq : iso.hom = G.map m := by
      apply (cancel_mono (G.map (kernel.ι (L.map f)))).mp
      calc
        _ = G.map (L.map K.ι) :=
          IsLimit.conePointUniqueUpToIso_hom_comp hG hG' WalkingParallelPair.zero
        _ = _ := (congrArg G.map (kernel.lift_ι (L.map f) (L.map K.ι) w)).symm.trans
          (G.map_comp m (kernel.ι (L.map f)))
    change IsIso (G.map m)
    rw [← heq]
    infer_instance
  exact IsLimit.ofIsoLimit (kernelIsKernel _) (Fork.ext (asIso m).symm (by
    change (asIso m).inv ≫ L.map K.ι = kernel.ι (L.map f)
    apply (cancel_epi m).mp
    change (asIso m).hom ≫ (asIso m).inv ≫ L.map K.ι = _
    rw [Iso.hom_inv_id_assoc, kernel.lift_ι]))

section ClosedUnit

open scoped TensorProduct

private def quotientTensorEquivOfSurjective {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars.{u,u,u} φ ⋙ ModuleCat.restrictScalars φ).obj M) ≃ₗ[R]
      (M ⧸ (RingHom.ker φ • (⊤ : Submodule R M))) := by
  let : Algebra R S := φ.toAlgebra
  let e := RingHom.quotientKerEquivOfSurjective hφ
  let e' : (R ⧸ RingHom.ker φ) ≃ₐ[R] S :=
    { e with commutes' := RingHom.quotientKerEquivOfSurjective_apply_mk hφ }
  change (S ⊗[R] M) ≃ₗ[R] _
  exact TensorProduct.congr e'.symm.toLinearEquiv (LinearEquiv.refl R M) ≪≫ₗ
    TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker φ)

private theorem quotientTensorEquivOfSurjective_unit {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (M : ModuleCat.{u} R) (x : M) :
    quotientTensorEquivOfSurjective φ hφ M ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M x) =
      Submodule.Quotient.mk x := by
  let : Algebra R S := φ.toAlgebra
  let e : (R ⧸ RingHom.ker φ) ≃ₐ[R] S :=
    { RingHom.quotientKerEquivOfSurjective hφ with
      commutes' := RingHom.quotientKerEquivOfSurjective_apply_mk hφ }
  change (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker φ))
    (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl R M) (1 ⊗ₜ[R] x)) = _
  simp

open private affine_pullbackSections from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage

private abbrev adjunctionUnit {X Z : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules) :
    F ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F

private theorem affine_closedUnit {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (F : X.Modules) [F.IsQuasicoherent] :
    Function.Surjective ((ev (⊤ : X.Opens)).map (adjunctionUnit i F)) ∧
      LinearMap.ker ((ev (⊤ : X.Opens)).map (adjunctionUnit i F)).hom =
        RingHom.ker i.appTop.hom • (⊤ : Submodule Γ(X, ⊤) Γ(F, ⊤)) := by
  let P := Scheme.Modules.pullback i
  let Q := Scheme.Modules.pushforward i
  let M := (ev (⊤ : X.Opens)).obj F
  let N := (ModuleCat.restrictScalars i.appTop.hom).obj ((ev (⊤ : Z.Opens)).obj (P.obj F))
  let g := (ev (⊤ : X.Opens)).map (adjunctionUnit i F)
  let φ := i.appTop.hom
  have hφ : Function.Surjective φ := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  obtain ⟨e, he⟩ := affine_pullbackSections i F
  let e₀ : (ev (⊤ : X.Opens)).obj (Q.obj (P.obj F)) ≃ₗ[Γ(X, ⊤)] N :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e₁ := e₀.toModuleIso
  let e₂ := (ModuleCat.restrictScalars φ).mapIso e
  let e₃ := quotientTensorEquivOfSurjective φ hφ M
  let E := (e₁ ≪≫ e₂).toLinearEquiv ≪≫ₗ e₃
  have h (x : M) : E (g x) = Submodule.Quotient.mk x := by
    change e₃ (e.hom (pullSection i F x)) = _
    rw [he]
    exact quotientTensorEquivOfSurjective_unit φ hφ M x
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (RingHom.ker φ • (⊤ : Submodule Γ(X, ⊤) M)) (E y)
    exact ⟨x, E.injective ((h x).trans hx)⟩
  · ext x
    change g x = 0 ↔ _
    rw [← E.map_eq_zero_iff, h, Submodule.Quotient.mk_eq_zero]

end ClosedUnit

section CoherentKernels

open Scheme.Modules SheafOfModules

open private pullback_open_isQuasicoherent finitePresentation_on_affine_open from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage

private theorem flatPullback_preservesFiniteLimits {X Y : Scheme.{u}} (p : Y ⟶ X)
    [Flat p] : PreservesFiniteLimits (Scheme.Modules.pullback p) := by
  have := FlatCohomology.flatPullbackExact p
  exact Functor.preservesFiniteLimits_of_preservesHomology _

private theorem spec_kernel_isQuasicoherent {R : CommRingCat.{u}}
    {F H : (Spec R).Modules} [F.IsQuasicoherent] [H.IsQuasicoherent]
    (f : F ⟶ H) : (kernel f).IsQuasicoherent := by
  let G := moduleSpecΓFunctor (R := R)
  let eF : tilde (G.obj F) ≅ F := asIso F.fromTildeΓ
  let eH : tilde (G.obj H) ≅ H := asIso H.fromTildeΓ
  let e : Arrow.mk ((tilde.functor R).map (G.map f)) ≅ Arrow.mk f :=
    Arrow.isoMk eF eH ((tilde.adjunction (R := R)).counit.naturality f).symm
  let K := tilde_map_ker_isLimit (G.map f)
  let E := KernelFork.mapIsoOfIsLimit K (kernelIsKernel f) e
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso E
    (inferInstanceAs ((tilde (ModuleCat.kernelCone (G.map f)).pt).IsQuasicoherent))

private theorem affine_kernel_isQuasicoherent {X : Scheme.{u}} [IsAffine X]
    {F H : X.Modules} [F.IsQuasicoherent] [H.IsQuasicoherent]
    (f : F ⟶ H) : (kernel f).IsQuasicoherent := by
  let p := X.isoSpec.inv
  let q := X.isoSpec.hom
  let P := Scheme.Modules.pullback p
  let Q := Scheme.Modules.pullback q
  let := flatPullback_preservesFiniteLimits p
  let := pullback_open_isQuasicoherent p F
  let := pullback_open_isQuasicoherent p H
  let l := isLimitForkMapOfIsLimit' P (kernel.condition f) (kernelIsKernel f)
  let e : P.obj (kernel f) ≅ kernel (P.map f) :=
    l.conePointUniqueUpToIso (limit.isLimit (parallelPair (P.map f) 0))
  have h := spec_kernel_isQuasicoherent (P.map f)
  let eq : Q.obj (P.obj (kernel f)) ≅ kernel f :=
    ((Scheme.Modules.pullbackComp q p).app _) ≪≫
    ((Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id).app _) ≪≫
    ((Scheme.Modules.pullbackId X).app _)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Q.mapIso e).symm ≪≫ eq) (pullback_open_isQuasicoherent q (kernel (P.map f)))

private theorem coherent_kernel {X : Scheme.{u}} [IsLocallyNoetherian X]
    {F H : X.Modules} [F.IsFinitePresentation] [H.IsFinitePresentation]
    (f : F ⟶ H) : (kernel f).IsFinitePresentation := by
  let K := kernel f
  have h (U : X.affineOpens) : ∃ P : (K.over U.val).Presentation, P.IsFinite := by
    let p := U.val.ι
    let P := Scheme.Modules.pullback p
    let := flatPullback_preservesFiniteLimits p
    let : IsAffine U.val.toScheme := U.property
    let := pullback_open_isQuasicoherent p F
    let := pullback_open_isQuasicoherent p H
    let l := isLimitForkMapOfIsLimit' P (kernel.condition f) (kernelIsKernel f)
    let e : P.obj K ≅ kernel (P.map f) := l.conePointUniqueUpToIso (limit.isLimit (parallelPair (P.map f) 0))
    have hQ : (kernel (P.map f)).IsQuasicoherent := affine_kernel_isQuasicoherent (P.map f)
    let hKP : (K.restrict p).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent U.val.toScheme.ringCatSheaf).prop_of_iso
        (e.symm ≪≫ ((restrictFunctorIsoPullback p).app K).symm) hQ
    let G := ev U.val
    let : PreservesFiniteLimits G := inferInstanceAs
      (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op U.val)))
    let : IsNoetherianRing Γ(X, U.val) := IsLocallyNoetherian.component_noetherian U
    let : Module.Finite Γ(X, U.val) (G.obj F) :=
      ProjectiveFiniteness.finite_sections_of_isAffineOpen F U.property
    let hfin : Module.Finite Γ(X, U.val) Γ(K, U.val) :=
      Module.Finite.of_injective (G.map (kernel.ι f)).hom
        ((ModuleCat.mono_iff_injective _).mp (inferInstanceAs (Mono (G.map (kernel.ι f)))))
    exact finitePresentation_on_affine_open K U.property
  choose P hP using h
  let D : K.QuasicoherentData :=
    { I := X.affineOpens
      X := Subtype.val
      coversTop := (Opens.coversTop_iff _ _).mpr (iSup_affineOpens_eq_top X)
      presentation := P }
  have hD : D.IsFinitePresentation := by
    constructor
    intro z
    exact hP z
  exact SheafOfModules.IsFinitePresentation.mk (M := K) ⟨D, hD⟩

end CoherentKernels

section LocalFiltration

open Scheme.Modules
open private pullback_open_isQuasicoherent from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage

private abbrev closedChartIdeal {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) :
    Ideal Γ(U.toScheme, ⊤) := RingHom.ker (i ∣_ U).appTop.hom

private theorem closedUnit_on_affine_open {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (F : X.Modules) [F.IsFinitePresentation]
    {U : X.Opens} (hU : IsAffineOpen U) :
    let G := Scheme.Modules.pullback U.ι ⋙ ev (⊤ : U.toScheme.Opens)
    Function.Surjective (G.map (adjunctionUnit i F)) ∧
      LinearMap.ker (G.map (adjunctionUnit i F)).hom =
        closedChartIdeal i U • (⊤ : Submodule Γ(U.toScheme, ⊤) (G.obj F)) := by
  dsimp only
  let p := U.ι
  let P := Scheme.Modules.pullback p
  let G := ev (⊤ : U.toScheme.Opens)
  let i' := i ∣_ U
  let sq : IsPullback i' (i ⁻¹ᵁ U).ι p i := isPullback_morphismRestrict i U
  let : IsAffine U.toScheme := hU
  let : IsAffine (i ⁻¹ᵁ U).toScheme := hU.preimage i
  let : (P.obj F).IsQuasicoherent := pullback_open_isQuasicoherent p F
  let : ((Scheme.Modules.pullback i).obj F).IsFinitePresentation :=
    pullback_finitePresentation i F
  let e := directImageBaseChange sq.w ((Scheme.Modules.pullback i).obj F)
  let : IsIso e := affineDirectImageBaseChange_isIso sq _
  let d := (pushforward i').map (pullbackSquareIso sq.w F).hom
  let : IsIso d := inferInstance
  have h := congrArg G.map (directImageBaseChange_unit sq.w F)
  have hh : G.map (P.map (adjunctionUnit i F)) ≫ G.map e =
      G.map (adjunctionUnit i' (P.obj F)) ≫ G.map d := by
    simpa only [Functor.map_comp] using h
  obtain ⟨hs, hk⟩ := affine_closedUnit i' (P.obj F)
  have hinjE := (ConcreteCategory.bijective_of_isIso (G.map e)).1
  have hbijD := ConcreteCategory.bijective_of_isIso (G.map d)
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := hbijD.2 (G.map e y)
    obtain ⟨x, hx⟩ := hs v
    refine ⟨x, hinjE ?_⟩
    exact (ConcreteCategory.congr_hom hh x).trans ((congrArg (G.map d) hx).trans hv)
  · rw [← hk]
    ext x
    change G.map (P.map (adjunctionUnit i F)) x = 0 ↔ G.map (adjunctionUnit i' (P.obj F)) x = 0
    rw [← (G.map e).hom.map_eq_zero_iff hinjE, ← (G.map d).hom.map_eq_zero_iff hbijD.1]
    exact Iff.of_eq (congrArg (· = 0) (ConcreteCategory.congr_hom hh x))

private theorem closedUnit_epi {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (F : X.Modules) [F.IsFinitePresentation] :
    Epi (adjunctionUnit i F) := by
  constructor
  intro A g h e
  let B : X.affineOpens → X.Opens := Subtype.val
  have hb : Opens.IsBasis (Set.range B) := by simpa [B] using X.isBasis_affineOpens
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext (B := B) _ _ hb
  intro U
  let R := Scheme.Modules.pullback U.val.ι
  let G := R ⋙ ev (⊤ : U.val.toScheme.Opens)
  have he : Epi (G.map (adjunctionUnit i F)) :=
    (ModuleCat.epi_iff_surjective _).2 (closedUnit_on_affine_open i F U.property).1
  have heq : G.map g = G.map h := by
    apply (cancel_epi (G.map (adjunctionUnit i F))).1
    simpa only [Functor.map_comp] using congrArg G.map e
  let eq := (restrictFunctorIsoPullback U.val.ι).hom
  have hR : (ev (⊤ : U.val.toScheme.Opens)).map ((restrictFunctor U.val.ι).map g) =
      (ev (⊤ : U.val.toScheme.Opens)).map ((restrictFunctor U.val.ι).map h) := by
    apply (cancel_mono ((ev (⊤ : U.val.toScheme.Opens)).map (eq.app A))).1
    let E := ev (⊤ : U.val.toScheme.Opens)
    have hg := congrArg E.map (eq.naturality g)
    have hh := congrArg E.map (eq.naturality h)
    simp only [Functor.map_comp] at hg hh
    rw [hg, hh]
    exact congrArg (E.map (eq.app _) ≫ ·) heq
  ext x
  have hh := ConcreteCategory.congr_hom hR
  -- Sections of the restriction on its top open are sections on the original open.
  have htop := U.val.ι_image_top
  change g.app U.val x = h.app U.val x
  have aux : ∀ V : X.Opens, U.val.ι ''ᵁ ⊤ = V → ∀ s : Γ((pushforward i).obj ((Scheme.Modules.pullback i).obj F), V),
      g.app V s = h.app V s := by
    intro V hV
    subst V
    exact hh
  exact aux U.val htop x

private def supportTerm {X Z : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules) :
    ℕ → X.Modules
  | 0 => F
  | n + 1 => kernel (adjunctionUnit i (supportTerm i F n))

private def supportInclusion {X Z : Scheme.{u}} (i : Z ⟶ X)
    (F : X.Modules) : (n : ℕ) → supportTerm i F n ⟶ F
  | 0 => 𝟙 _
  | n + 1 => kernel.ι (adjunctionUnit i (supportTerm i F n)) ≫ supportInclusion i F n

private theorem supportTerm_coherent {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (F : X.Modules) [F.IsFinitePresentation] (n : ℕ) :
    (supportTerm i F n).IsFinitePresentation := by
  induction n with
  | zero => exact inferInstanceAs F.IsFinitePresentation
  | succ n h =>
    let : ((Scheme.Modules.pullback i).obj (supportTerm i F n)).IsFinitePresentation :=
      pullback_finitePresentation i (supportTerm i F n)
    let : ((pushforward i).obj ((Scheme.Modules.pullback i).obj
        (supportTerm i F n))).IsFinitePresentation := closedPushforward_finitePresentation i _
    exact coherent_kernel (adjunctionUnit i (supportTerm i F n))

private theorem supportInclusion_mono {X Z : Scheme.{u}} (i : Z ⟶ X)
    (F : X.Modules) (n : ℕ) : Mono (supportInclusion i F n) := by
  induction n with
  | zero => exact inferInstanceAs (Mono (𝟙 F))
  | succ n h =>
    exact inferInstanceAs (Mono (kernel.ι (adjunctionUnit i (supportTerm i F n)) ≫
      supportInclusion i F n))

private theorem supportInclusion_range {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (F : X.Modules) [F.IsFinitePresentation]
    {U : X.Opens} (hU : IsAffineOpen U) (n : ℕ) :
    let G := Scheme.Modules.pullback U.ι ⋙ ev (⊤ : U.toScheme.Opens)
    LinearMap.range (G.map (supportInclusion i F n)).hom =
      (closedChartIdeal i U) ^ n • (⊤ : Submodule Γ(U.toScheme, ⊤) (G.obj F)) := by
  let G := Scheme.Modules.pullback U.ι ⋙ ev (⊤ : U.toScheme.Opens)
  let := flatPullback_preservesFiniteLimits U.ι
  let : PreservesFiniteLimits (ev (⊤ : U.toScheme.Opens)) := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤)))
  let : G.Additive := by infer_instance
  let : PreservesFiniteLimits G := by infer_instance
  change LinearMap.range (G.map (supportInclusion i F n)).hom =
    (closedChartIdeal i U) ^ n • (⊤ : Submodule Γ(U.toScheme, ⊤) (G.obj F))
  induction n with
  | zero =>
    simp [supportInclusion, ModuleCat.hom_id]
  | succ n ih =>
    let A := supportTerm i F n
    let : A.IsFinitePresentation := supportTerm_coherent i F n
    let m := adjunctionUnit i A
    have hk := isLimitForkMapOfIsLimit' G (kernel.condition m) (kernelIsKernel m)
    let S := (ShortComplex.mk (kernel.ι m) m (kernel.condition m)).map G
    have hS : S.Exact := S.exact_of_f_is_kernel hk
    have he : Function.Exact (G.map (kernel.ι m)).hom (G.map m).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS
    have hr : LinearMap.range (G.map (kernel.ι m)).hom = LinearMap.ker (G.map m).hom :=
      he.linearMap_ker_eq.symm
    change LinearMap.range (G.map (kernel.ι m ≫ supportInclusion i F n)).hom = _
    rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.range_comp, hr,
      (closedUnit_on_affine_open i A hU).2, Submodule.map_smul'', Submodule.map_top, ih,
      ← Submodule.mul_smul, ← pow_succ']

end LocalFiltration

section Vanishing

open Scheme.Modules
open private sectionsIsoSpec pullback_open_isQuasicoherent from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage

private theorem isZero_pullback_of_range {X Y W : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (p : W ⟶ X) (h : Set.range p ⊆ Set.range j) (F : X.Modules)
    (hF : IsZero ((Scheme.Modules.pullback j).obj F)) :
    IsZero ((Scheme.Modules.pullback p).obj F) := by
  let q := IsOpenImmersion.lift j p h
  let e := Scheme.Modules.pullbackComp q j ≪≫
    Scheme.Modules.pullbackCongr (IsOpenImmersion.lift_fac j p h)
  exact ((Scheme.Modules.pullback q).map_isZero hF).of_iso (e.app F).symm

private theorem zero_sections_of_zero_pullback {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsOpenImmersion p] (F : X.Modules) (h : IsZero ((Scheme.Modules.pullback p).obj F))
    (V : Y.Opens) : Subsingleton Γ(F, p ''ᵁ V) := by
  have hz := h.of_iso ((restrictFunctorIsoPullback p).app F)
  let G := ev V
  let : G.Additive := by infer_instance
  exact ModuleCat.subsingleton_of_isZero (M := G.obj ((restrictFunctor p).obj F))
    (G.map_isZero hz)

private theorem chart_support_subset {X Y Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : Y ⟶ X) [IsOpenImmersion j] (hj : Set.range j = (Set.range i)ᶜ)
    (F : X.Modules) [F.IsFinitePresentation] (hF : IsZero ((Scheme.Modules.pullback j).obj F))
    {U : X.Opens} (hU : IsAffineOpen U) :
    let G := Scheme.Modules.pullback U.ι ⋙ ev (⊤ : U.toScheme.Opens)
    Module.support Γ(U.toScheme, ⊤) (G.obj F) ⊆
      PrimeSpectrum.zeroLocus (closedChartIdeal i U : Set Γ(U.toScheme, ⊤)) := by
  let W := U.toScheme
  let V := (i ⁻¹ᵁ U).toScheme
  let hW : IsAffine W := hU
  let hV : IsAffine V := hU.preimage i
  let R := Γ(W, ⊤)
  let P := (Scheme.Modules.pullback U.ι).obj F
  let q := W.isoSpec.inv
  let Q := (Scheme.Modules.pullback q).obj P
  let M := (moduleSpecΓFunctor (R := R)).obj Q
  let e := sectionsIsoSpec W P
  let : P.IsQuasicoherent := pullback_open_isQuasicoherent U.ι F
  let : Q.IsQuasicoherent := pullback_open_isQuasicoherent q P
  let E : tilde M ≅ Q := asIso Q.fromTildeΓ
  change Module.support R ((ev (⊤ : W.Opens)).obj P) ⊆
    PrimeSpectrum.zeroLocus (closedChartIdeal i U : Set R)
  intro x hx r hr
  by_contra hxr
  let D : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let p := D.ι ≫ q ≫ U.ι
  have hDisjoint : Set.range p ⊆ Set.range j := by
    rw [hj]
    rintro _ ⟨z, rfl⟩ ⟨y, he⟩
    let w := q (D.ι z)
    have hyw : i y = U.ι w := by simpa only [p, w, Scheme.Hom.comp_apply] using he
    obtain ⟨v, hv, hw⟩ :=
      Scheme.exists_preimage_of_isPullback (isPullback_morphismRestrict i U).flip y w hyw
    let i' := i ∣_ U
    have hspec : Spec.map i'.appTop (V.isoSpec.hom v) = D.ι z := by
      apply q.isOpenEmbedding.injective
      change (Spec.map i'.appTop ≫ q) (V.isoSpec.hom v) = w
      rw [Scheme.isoSpec_inv_naturality]
      change (V.isoSpec.hom ≫ V.isoSpec.inv ≫ i') v = w
      simpa only [Iso.hom_inv_id_assoc] using hw
    have hz : D.ι z ∈ PrimeSpectrum.zeroLocus (closedChartIdeal i U : Set R) := by
      rw [← range_comap_of_surjective _ _ (IsClosedImmersion.isAffine_surjective_of_isAffine i').2]
      exact ⟨V.isoSpec.hom v, hspec⟩
    exact z.2 (hz hr)
  have hp := isZero_pullback_of_range j p hDisjoint F hF
  have hPQ : IsZero ((Scheme.Modules.pullback D.ι).obj Q) := by
    let iso := Scheme.Modules.pullbackComp D.ι q
    let iso' := Scheme.Modules.pullbackComp (D.ι ≫ q) U.ι
    let iso'' := Scheme.Modules.pullbackCongr (Category.assoc D.ι q U.ι)
    let e' := (iso.app P) ≪≫ (iso'.app F) ≪≫ (iso''.app F)
    exact hp.of_iso e'
  have hQsec : Subsingleton Γ(Q, D) := by
    have h := zero_sections_of_zero_pullback D.ι Q hPQ ⊤
    rwa [D.ι_image_top] at h
  have hMsec : Subsingleton Γ(tilde M, D) :=
    Function.Injective.subsingleton (ConcreteCategory.bijective_of_isIso (E.hom.app D)).1
  have hM : ∀ m : M, ∃ s ∈ Submonoid.powers r, s • m = 0 :=
    (IsLocalizedModule.subsingleton_iff (Submonoid.powers r) (tilde.toOpen M D).hom).1 hMsec
  have hnot : x ∉ Module.support R ((ev (⊤ : W.Opens)).obj P) := by
    rw [Module.notMem_support_iff']
    intro m
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hM (e.hom m)
    refine ⟨r ^ n, fun hn' => hxr (Ideal.IsPrime.mem_of_pow_mem x.isPrime n hn'), ?_⟩
    exact (ConcreteCategory.bijective_of_isIso e.hom).1 (by
      simpa only [_root_.map_smul, map_zero] using hn)
  exact hnot hx

private theorem isZero_of_zeroSections_on_cover {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hzero : ∀ z, IsZero ((Scheme.Modules.pullback (U z).ι).obj M)) : IsZero M := by
  let B : Set X.Opens := {V | ∃ z, V ≤ U z}
  have hb : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨z, hz⟩ := hU.exists_mem x
    exact ⟨W ⊓ U z, ⟨z, inf_le_right⟩, ⟨hx, hz⟩, inf_le_left⟩
  let B' : B → X.Opens := Subtype.val
  have hb' : Opens.IsBasis (Set.range B') := by simpa [B'] using hb
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext (B := B') _ _ hb'
  intro z
  obtain ⟨w, hz⟩ := z.property
  let p := (U w).ι
  let V : (U w).toScheme.Opens := p ⁻¹ᵁ z.val
  have zero := zero_sections_of_zero_pullback p M (hzero w) V
  have hv : p ''ᵁ V = z.val := by
    change p ''ᵁ p ⁻¹ᵁ z.val = z.val
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hz]
  have hz' : Subsingleton Γ(M, z.val) := hv ▸ zero
  ext x
  change (𝟙 M : M ⟶ M).app z.val x = (0 : M ⟶ M).app z.val x
  exact @Subsingleton.elim Γ(M, z.val) hz' _ _

private theorem affine_isZero_of_top {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] (h : Subsingleton Γ(F, ⊤)) : IsZero F := by
  let p := X.isoSpec.inv
  let q := X.isoSpec.hom
  let P := Scheme.Modules.pullback p
  let Q := Scheme.Modules.pullback q
  let R := Γ(X, ⊤)
  let M := (moduleSpecΓFunctor (R := R)).obj (P.obj F)
  let e := sectionsIsoSpec X F
  let : Subsingleton Γ(F, ⊤) := h
  have hM : IsZero M :=
    ModuleCat.isZero_iff_subsingleton.mpr
      ⟨fun x y => (ConcreteCategory.bijective_of_isIso e.inv).1 (h.elim _ _)⟩
  let : (P.obj F).IsQuasicoherent := pullback_open_isQuasicoherent p F
  have hP : IsZero (P.obj F) :=
    ((tilde.functor R).map_isZero hM).of_iso (asIso (P.obj F).fromTildeΓ).symm
  let e' := Scheme.Modules.pullbackComp q p ≪≫
    Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id ≪≫ Scheme.Modules.pullbackId X
  exact (Q.map_isZero hP).of_iso (e'.app F).symm

private theorem supportTerm_eventually_zero {X Y Z : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : Y ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j = (Set.range i)ᶜ)
    (F : X.Modules) [F.IsFinitePresentation] (hF : IsZero ((Scheme.Modules.pullback j).obj F)) :
    ∃ n : ℕ, IsZero (supportTerm i F n) := by
  classical
  have h (U : X.affineOpens) : ∃ n : ℕ,
      let G := Scheme.Modules.pullback U.val.ι ⋙ ev (⊤ : U.val.toScheme.Opens)
      closedChartIdeal i U.val ^ n •
        (⊤ : Submodule Γ(U.val.toScheme, ⊤) (G.obj F)) = ⊥ := by
    let P := Scheme.Modules.pullback U.val.ι
    let : IsAffine U.val.toScheme := U.property
    let : IsLocallyNoetherian U.val.toScheme := inferInstance
    let : (P.obj F).IsFinitePresentation := pullback_finitePresentation U.val.ι F
    let : IsNoetherianRing Γ(U.val.toScheme, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
    let : Module.Finite Γ(U.val.toScheme, ⊤)
        ((P ⋙ ev (⊤ : U.val.toScheme.Opens)).obj F) :=
      ProjectiveFiniteness.finite_sections_of_isAffineOpen (P.obj F) (isAffineOpen_top _)
    exact pow_smul_eq_bot_of_support_subset (closedChartIdeal i U.val)
      (IsNoetherian.noetherian _) (chart_support_subset i j hj F hF U.property)
  choose n hn using h
  obtain ⟨s, hs⟩ := X.isBasis_affineOpens.isOpenCover.exists_finite_of_compactSpace
  let N := s.sup n
  refine ⟨N, isZero_of_zeroSections_on_cover _ _ hs ?_⟩
  intro z
  let U : X.Opens := z.val.val
  let P := Scheme.Modules.pullback U.ι
  let G := P ⋙ ev (⊤ : U.toScheme.Opens)
  let : IsAffine U.toScheme := z.val.property
  let : (supportTerm i F N).IsFinitePresentation := supportTerm_coherent i F N
  let : (P.obj (supportTerm i F N)).IsQuasicoherent :=
    pullback_open_isQuasicoherent U.ι (supportTerm i F N)
  let : PreservesFiniteLimits P := flatPullback_preservesFiniteLimits U.ι
  let : PreservesFiniteLimits (ev (⊤ : U.toScheme.Opens)) := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤)))
  let : PreservesFiniteLimits G := by infer_instance
  let : Mono (supportInclusion i F N) := supportInclusion_mono i F N
  let m := G.map (supportInclusion i F N)
  have hr : LinearMap.range m.hom = ⊥ := by
    rw [supportInclusion_range i F z.val.property]
    exact le_antisymm
      ((Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.le_sup z.property))).trans_eq
        (hn z.val)) bot_le
  have hm : m.hom = 0 := LinearMap.range_eq_bot.mp hr
  apply affine_isZero_of_top
  exact (subsingleton_iff_forall_eq 0).mpr fun x =>
    ((ModuleCat.mono_iff_injective m).mp inferInstance) (by
      change m.hom x = m.hom 0
      rw [hm, LinearMap.zero_apply, LinearMap.zero_apply])

end Vanishing

section FlatKernels

private def mapKernelFork {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (P : C ⥤ D) [P.Additive]
    {A B : C} {f : A ⟶ B} (K : KernelFork f) : KernelFork (P.map f) :=
  KernelFork.ofι (P.map K.ι) (by rw [← P.map_comp, K.condition, P.map_zero])

private def flatPullbackKernel {X Y : Scheme.{u}} (p : Y ⟶ X) [Flat p]
    {F H K : X.Modules} {f : F ⟶ H} {m : K ⟶ F} (w : m ≫ f = 0)
    (h : IsLimit (KernelFork.ofι m w)) :
    IsLimit (mapKernelFork (Scheme.Modules.pullback p) (KernelFork.ofι m w)) := by
  let := flatPullback_preservesFiniteLimits p
  exact isLimitForkMapOfIsLimit' (Scheme.Modules.pullback p) w h

end FlatKernels

section LinearizedKernels

open scoped CategoryTheory.MonObj

open private actOn_precomp actOn_inv_cancel actOn_cancel_inv overPullback_left projection_isPullback
  transport_naturality transport_precomp from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage
open private comparePull pullCongr_naturality pullCongr_refl from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y Z : SchemeOver k}
  {a : ModObj T.X X}

local notation "P" f => Scheme.Modules.pullback (Over.Hom.left f)

private theorem projection_flat (A B : SchemeOver k) : Flat (snd A B).left := by
  change Flat (pullback.snd A.hom B.hom)
  infer_instance

private theorem action_flat (a : ModObj T.X X) : Flat a.smul.left := by
  let D := T.X ⊗ X
  let t := fst T.X X
  let x := snd T.X X
  let e : D ≅ D :=
    { hom := lift t (actOn a t x)
      inv := lift t (actOn a t⁻¹ x)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext
        · simp [t]
        · simp [t, x, actOn_precomp, GrpObj.comp_inv, actOn_inv_cancel]
          exact Category.id_comp _
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext
        · simp [t]
        · simp [t, x, actOn_precomp, actOn_cancel_inv]
          exact Category.id_comp _ }
  have he : e.hom ≫ x = a.smul := by
    change lift t (actOn a t x) ≫ snd T.X X = a.smul
    rw [lift_snd]
    simp [actOn, t, x]
  let : Flat x.left := projection_flat T.X X
  let : IsIso e.hom := e.isIso_hom
  let : IsIso e.hom.left := (Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
  rw [← he]
  exact inferInstanceAs (Flat (e.hom.left ≫ x.left))

private theorem productMap_flat {A B : SchemeOver k} (f : A ⟶ B) [Flat f.left] :
    Flat (𝟙 T.X ⊗ₘ f).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((overPullback_left (projection_isPullback (T := T) f)).flip) inferInstance

private theorem comparison_congr {F : X.left.Modules} (v : Y ⟶ Z)
    {f g : Z ⟶ X} {f' g' : Y ⟶ X} (h : f = g) (hf : v ≫ f = f')
    (hg : v ≫ g = g') (h' : f' = g') :
    (P v).map (pullCongr F h).hom ≫ (comparePull F v g hg).hom =
      (comparePull F v f hf).hom ≫ (pullCongr F h').hom := by
  subst g f' g'
  simp [comparePull, pullCongr_refl]

@[reassoc]
private theorem transport_precomp_named {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (v : Y ⟶ Z)
    (t : Z ⟶ T.X) (x : Z ⟶ X) {t' : Y ⟶ T.X} {x' : Y ⟶ X}
    (ht : v ≫ t = t') (hx : v ≫ x = x')
    (hact : v ≫ actOn a t x = actOn a t' x') :
    (P v).map (transport a θ t x).hom ≫ (comparePull F v (actOn a t x) hact).hom =
      (comparePull F v x hx).hom ≫ (transport a θ t' x').hom := by
  subst t'
  exact transport_precomp θ v t x hx

private theorem actOn_unit_eq (a : ModObj T.X X) (x : Y ⟶ X) :
    actOn a (1 : Y ⟶ T.X) x = x := by
  let := a
  exact one_smul (Y ⟶ T.X) x

private theorem actOn_mul_eq (a : ModObj T.X X) (s t : Y ⟶ T.X) (x : Y ⟶ X) :
    actOn a s (actOn a t x) = actOn a (s * t) x := by
  let := a
  exact (mul_smul s t x).symm

/-- Compose the two transports and identify the endpoint along the given equality. -/
private def transportPath {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    {S : SchemeOver k} (s t : S ⟶ T.X) (x : S ⟶ X) {z : S ⟶ X}
    (w : actOn a s (actOn a t x) = z) : Pull x F ⟶ Pull z F :=
  (transport a θ t x).hom ≫ (transport a θ s (actOn a t x)).hom ≫ (pullCongr F w).hom

private def TransportCompositionAt {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    {S : SchemeOver k} (s t r : S ⟶ T.X) (x : S ⟶ X)
    (w : actOn a s (actOn a t x) = actOn a r x) : Prop :=
  transportPath θ s t x w = (transport a θ r x).hom

private theorem unit_from_universal {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    (h : (transport a θ 1 (𝟙 X)).hom ≫ (pullCongr F (actOn_unit_eq a (𝟙 X))).hom = 𝟙 _) :
    ∀ (Y : SchemeOver k) (x : Y ⟶ X), (transport a θ 1 x).hom ≫
      (pullCongr F (actOn_unit_eq a x)).hom = 𝟙 _ := by
  intro Y x
  let h₀ := actOn_unit_eq a (𝟙 X)
  let h₁ := actOn_unit_eq a x
  have hx : x ≫ 𝟙 X = x := Category.comp_id x
  have ha : x ≫ actOn a 1 (𝟙 X) = actOn a 1 x := by rw [actOn_precomp, MonObj.comp_one, hx]
  have he := transport_precomp_named θ x 1 (𝟙 X) (MonObj.comp_one x) hx ha
  have hc := comparison_congr x h₀ ha hx h₁ (F := F)
  apply (cancel_epi (comparePull F x (𝟙 X) hx).hom).mp
  calc
    _ = (P x).map (transport a θ 1 (𝟙 X)).hom ≫
        (comparePull F x (actOn a 1 (𝟙 X)) ha).hom ≫ (pullCongr F h₁).hom := by
      rw [← reassoc_of% he]
    _ = _ := by
      rw [← hc, ← Functor.map_comp_assoc, h, (P x).map_id, Category.id_comp, Category.comp_id]

private theorem composesTo_of_mapped_squares
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B E H : C} {A' B' E' H' : D}
    (e₀ : G.obj A ≅ A') (e₁ : G.obj B ≅ B') (e₂ : G.obj E ≅ E') (e₃ : G.obj H ≅ H')
    {f : A ⟶ B} {g : B ⟶ E} {h : E ⟶ H} {r : A ⟶ H}
    {f' : A' ⟶ B'} {g' : B' ⟶ E'} {h' : E' ⟶ H'} {r' : A' ⟶ H'}
    (hf : G.map f ≫ e₁.hom = e₀.hom ≫ f')
    (hg : G.map g ≫ e₂.hom = e₁.hom ≫ g')
    (hh : G.map h ≫ e₃.hom = e₂.hom ≫ h')
    (hr : G.map r ≫ e₃.hom = e₀.hom ≫ r')
    (w : ComposesTo f g h r) : ComposesTo f' g' h' r' := by
  unfold ComposesTo at w ⊢
  apply (cancel_epi e₀.hom).mp
  calc
    e₀.hom ≫ f' ≫ g' ≫ h' = (G.map f ≫ G.map g ≫ G.map h) ≫ e₃.hom := by
      simp only [Category.assoc, hh, reassoc_of% hg, reassoc_of% hf]
    _ = e₀.hom ≫ r' := by rw [← G.map_comp, ← G.map_comp, w, hr]

private theorem actOn_precomp_eq (v : Y ⟶ Z) (t : Z ⟶ T.X) (x : Z ⟶ X)
    {t' : Y ⟶ T.X} {x' : Y ⟶ X} (ht : v ≫ t = t') (hx : v ≫ x = x') :
    v ≫ actOn a t x = actOn a t' x' := by
  subst t' x'
  exact actOn_precomp v t x

private theorem transportComposition_precomp {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    (v : Y ⟶ Z) (s t r : Z ⟶ T.X) (x : Z ⟶ X)
    (s' t' r' : Y ⟶ T.X) (x' : Y ⟶ X)
    (hs : v ≫ s = s') (ht : v ≫ t = t') (hr : v ≫ r = r') (hx : v ≫ x = x')
    (w : actOn a s (actOn a t x) = actOn a r x)
    (w' : actOn a s' (actOn a t' x') = actOn a r' x')
    (h : TransportCompositionAt θ s t r x w) :
    TransportCompositionAt θ s' t' r' x' w' := by
  have ht₀ := actOn_precomp_eq (a := a) v t x ht hx
  have hs₀ := actOn_precomp_eq (a := a) v s (actOn a t x) hs ht₀
  have hr₀ := actOn_precomp_eq (a := a) v r x hr hx
  exact @composesTo_of_mapped_squares Z.left.Modules Y.left.Modules _ _ (P v)
    (Pull x F) (Pull (actOn a t x) F) (Pull (actOn a s (actOn a t x)) F) (Pull (actOn a r x) F)
    (Pull x' F) (Pull (actOn a t' x') F) (Pull (actOn a s' (actOn a t' x')) F) (Pull (actOn a r' x') F)
    (comparePull F v x hx) (comparePull F v (actOn a t x) ht₀)
    (comparePull F v (actOn a s (actOn a t x)) hs₀) (comparePull F v (actOn a r x) hr₀)
    (transport a θ t x).hom (transport a θ s (actOn a t x)).hom
    (pullCongr F w).hom (transport a θ r x).hom
    (transport a θ t' x').hom (transport a θ s' (actOn a t' x')).hom
    (pullCongr F w').hom (transport a θ r' x').hom
    (transport_precomp_named θ v t x ht hx ht₀)
    (transport_precomp_named θ v s (actOn a t x) hs ht₀ hs₀)
    (comparison_congr v w hs₀ hr₀ w') (transport_precomp_named θ v r x hr hx hr₀) h

private def mulUniversalT : T.X ⊗ (T.X ⊗ X) ⟶ T.X :=
  snd T.X (T.X ⊗ X) ≫ fst T.X X

private def mulUniversalX : T.X ⊗ (T.X ⊗ X) ⟶ X :=
  snd T.X (T.X ⊗ X) ≫ snd T.X X

private theorem mulUniversal_endpoint_flat (a : ModObj T.X X) :
    Flat (actOn a (fst T.X (T.X ⊗ X) * mulUniversalT (T := T) (X := X))
      (mulUniversalX (T := T) (X := X))).left := by
  let : Flat a.smul.left := action_flat a
  have he : actOn a (fst T.X (T.X ⊗ X) * mulUniversalT (T := T) (X := X))
      (mulUniversalX (T := T) (X := X)) = (𝟙 T.X ⊗ₘ a.smul) ≫ a.smul := by
    rw [← actOn_mul_eq]
    unfold actOn mulUniversalT mulUniversalX
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
    congr 1
  rw [he]
  let := productMap_flat (T := T) a.smul
  exact inferInstanceAs (Flat ((𝟙 T.X ⊗ₘ a.smul).left ≫ a.smul.left))

private theorem unit_of_compatible {K F : X.left.Modules}
    (θ : Pull (snd T.X X) K ≅ Pull a.smul K) (L : Linearization a F)
    (m : K ⟶ F)
    (hm : θ.hom ≫ (P a.smul).map m = (P (snd T.X X)).map m ≫ L.iso.hom)
    [Mono ((P (𝟙 X)).map m)] (Y : SchemeOver k) (x : Y ⟶ X) :
    (transport a θ 1 x).hom ≫ (pullCongr K (actOn_unit_eq a x)).hom = 𝟙 _ := by
  apply unit_from_universal θ _ Y x
  let w := actOn_unit_eq a (𝟙 X)
  have ht := transport_naturality θ L.iso m hm 1 (𝟙 X)
  have hL : (transport a L.iso 1 (𝟙 X)).hom ≫ (pullCongr F w).hom = 𝟙 _ :=
    (L.unit X (𝟙 X)).choose_spec
  apply (cancel_mono ((P (𝟙 X)).map m)).mp
  simp only [Category.assoc, pullCongr_naturality, reassoc_of% ht, hL,
    Category.comp_id, Category.id_comp]

private theorem transport_natural_square {K F : X.left.Modules}
    (θ : Pull (snd T.X X) K ≅ Pull a.smul K)
    (ψ : Pull (snd T.X X) F ≅ Pull a.smul F) (m : K ⟶ F)
    (hm : θ.hom ≫ (P a.smul).map m = (P (snd T.X X)).map m ≫ ψ.hom)
    {S : SchemeOver k} (t : S ⟶ T.X) (x : S ⟶ X) :
    CommSq (transport a θ t x).hom ((P x).map m) ((P (actOn a t x)).map m)
      (transport a ψ t x).hom :=
  ⟨transport_naturality θ ψ m hm t x⟩

private theorem pullCongr_natural_square {K F : X.left.Modules}
    (m : K ⟶ F) {S : SchemeOver k} {y z : S ⟶ X} (w : y = z) :
    CommSq (pullCongr K w).hom ((P y).map m) ((P z).map m) (pullCongr F w).hom :=
  ⟨pullCongr_naturality w m⟩

private theorem transport_path_square {K F : X.left.Modules}
    (θ : Pull (snd T.X X) K ≅ Pull a.smul K)
    (ψ : Pull (snd T.X X) F ≅ Pull a.smul F) (m : K ⟶ F)
    (hm : θ.hom ≫ (P a.smul).map m = (P (snd T.X X)).map m ≫ ψ.hom)
    {S : SchemeOver k} (s t : S ⟶ T.X) (x : S ⟶ X) {z : S ⟶ X}
    (w : actOn a s (actOn a t x) = z) :
    CommSq (transportPath θ s t x w) ((P x).map m) ((P z).map m) (transportPath ψ s t x w) :=
  (transport_natural_square θ ψ m hm t x).horiz_comp
    ((transport_natural_square θ ψ m hm s (actOn a t x)).horiz_comp (pullCongr_natural_square m w))

private theorem comp_transport_path_eq {F : X.left.Modules}
    (ψ : Pull (snd T.X X) F ≅ Pull a.smul F) {S : SchemeOver k}
    (s t r : S ⟶ T.X) (x : S ⟶ X) (w : actOn a s (actOn a t x) = actOn a r x)
    (h : TransportCompositionAt ψ s t r x w)
    {A : S.left.Modules} (m : A ⟶ Pull x F) :
    m ≫ transportPath ψ s t x w = m ≫ (transport a ψ r x).hom :=
  congrArg (fun g : Pull x F ⟶ Pull (actOn a r x) F => m ≫ g) h

private theorem mul_comp_after_inclusion {K F : X.left.Modules}
    (θ : Pull (snd T.X X) K ≅ Pull a.smul K)
    (ψ : Pull (snd T.X X) F ≅ Pull a.smul F) (m : K ⟶ F)
    (hm : θ.hom ≫ (P a.smul).map m = (P (snd T.X X)).map m ≫ ψ.hom)
    {S : SchemeOver k} (s t r : S ⟶ T.X) (x : S ⟶ X)
    (w : actOn a s (actOn a t x) = actOn a r x)
    (h : TransportCompositionAt ψ s t r x w) :
    transportPath θ s t x w ≫ (P (actOn a r x)).map m =
      (transport a θ r x).hom ≫ (P (actOn a r x)).map m := by
  calc
    _ = (P x).map m ≫ transportPath ψ s t x w := (transport_path_square θ ψ m hm s t x w).w
    _ = (P x).map m ≫ (transport a ψ r x).hom := comp_transport_path_eq ψ s t r x w h ((P x).map m)
    _ = _ := (transport_naturality θ ψ m hm r x).symm

private theorem mul_of_compatible_at {K F : X.left.Modules}
    (θ : Pull (snd T.X X) K ≅ Pull a.smul K)
    (ψ : Pull (snd T.X X) F ≅ Pull a.smul F) (m : K ⟶ F)
    (hm : θ.hom ≫ (P a.smul).map m = (P (snd T.X X)).map m ≫ ψ.hom)
    {S : SchemeOver k} (s t r : S ⟶ T.X) (x : S ⟶ X)
    (w : actOn a s (actOn a t x) = actOn a r x)
    (h : TransportCompositionAt ψ s t r x w)
    (hmono : Mono ((P (actOn a r x)).map m)) :
    TransportCompositionAt θ s t r x w :=
  hmono.right_cancellation (transportPath θ s t x w) (transport a θ r x).hom
    (mul_comp_after_inclusion θ ψ m hm s t r x w h)

private theorem linearization_composition_at {F : X.left.Modules}
    (L : Linearization a F) {S : SchemeOver k} (s t : S ⟶ T.X) (x : S ⟶ X)
    (w : actOn a s (actOn a t x) = actOn a (s * t) x) :
    TransportCompositionAt L.iso s t (s * t) x w := by
  have h : TransportComposition L.iso s t x w := (L.mul S s t x).choose_spec
  exact h

private theorem transportComposition_of_at {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    {S : SchemeOver k} (s t : S ⟶ T.X) (x : S ⟶ X)
    (w : actOn a s (actOn a t x) = actOn a (s * t) x)
    (h : TransportCompositionAt θ s t (s * t) x w) :
    TransportComposition θ s t x w := h

private theorem mul_of_compatible {K F : X.left.Modules}
    (θ : Pull (snd T.X X) K ≅ Pull a.smul K) (L : Linearization a F)
    (m : K ⟶ F)
    (hm : θ.hom ≫ (P a.smul).map m = (P (snd T.X X)).map m ≫ L.iso.hom)
    {S : SchemeOver k} (s t : S ⟶ T.X) (x : S ⟶ X)
    (hmono : Mono ((P (actOn a (s * t) x)).map m)) :
    TransportCompositionAt θ s t (s * t) x (actOn_mul_eq a s t x) := by
  let w := actOn_mul_eq a s t x
  exact mul_of_compatible_at θ L.iso m hm s t (s * t) x w
    (linearization_composition_at L s t x w) hmono

private theorem mul_from_universal {K : X.left.Modules}
    (θ : Pull (snd T.X X) K ≅ Pull a.smul K)
    (hm : let s₀ := fst T.X (T.X ⊗ X)
      let t₀ := mulUniversalT (T := T) (X := X)
      let x₀ := mulUniversalX (T := T) (X := X)
      TransportCompositionAt θ s₀ t₀ (s₀ * t₀) x₀ (actOn_mul_eq a s₀ t₀ x₀)) :
    ∀ (Y : SchemeOver k) (s t : Y ⟶ T.X) (x : Y ⟶ X),
      TransportComposition θ s t x (actOn_mul_eq a s t x) := by
  intro Y s t x
  let S := T.X ⊗ (T.X ⊗ X)
  let s₀ := fst T.X (T.X ⊗ X)
  let t₀ := mulUniversalT (T := T) (X := X)
  let x₀ := mulUniversalX (T := T) (X := X)
  let v : Y ⟶ S := lift s (lift t x)
  have hv₁ : v ≫ s₀ = s := by simp [v, s₀]
  have hv₂ : v ≫ t₀ = t := by simp [v, t₀, mulUniversalT]
  have hv₃ : v ≫ x₀ = x := by simp [v, x₀, mulUniversalX]
  have hv₄ : v ≫ (s₀ * t₀) = s * t :=
    (MonObj.comp_mul v s₀ t₀).trans (congrArg₂ (· * ·) hv₁ hv₂)
  let w := actOn_mul_eq a s t x
  have h : TransportCompositionAt θ s t (s * t) x w :=
    transportComposition_precomp θ v s₀ t₀ (s₀ * t₀) x₀ s t (s * t) x
      hv₁ hv₂ hv₄ hv₃ (actOn_mul_eq a s₀ t₀ x₀) w hm
  exact transportComposition_of_at θ s t x w h

private theorem kernel_map_mono {F H : X.left.Modules} (m : F ⟶ H)
    {S : SchemeOver k} (z : S ⟶ X) [Flat z.left] :
    Mono ((P z).map (kernel.ι m)) := by
  let := flatPullback_preservesFiniteLimits z.left
  infer_instance

set_option maxHeartbeats 500000 in
private def kernelLinearization {F H : X.left.Modules}
    (L : Linearization a F) (M : Linearization a H) {m : F ⟶ H}
    (hm : IsLinearizedMap L M m) :
    {K : Linearization a (kernel m) // IsLinearizedMap K L (kernel.ι m)} := by
  let p := snd T.X X
  let q := a.smul
  letI : Flat p.left := projection_flat T.X X
  letI : Flat q.left := action_flat a
  let Kp := flatPullbackKernel p.left (kernel.condition m) (kernelIsKernel m)
  let Kq := flatPullbackKernel q.left (kernel.condition m) (kernelIsKernel m)
  let e : Arrow.mk ((P p).map m) ≅ Arrow.mk ((P q).map m) :=
    Arrow.isoMk L.iso M.iso hm
  let θ : Pull p (kernel m) ≅ Pull q (kernel m) := KernelFork.mapIsoOfIsLimit Kp Kq e
  have hc : θ.hom ≫ (P q).map (kernel.ι m) = (P p).map (kernel.ι m) ≫ L.iso.hom :=
    KernelFork.mapOfIsLimit_ι (mapKernelFork (P p) (KernelFork.ofι (kernel.ι m) (kernel.condition m)))
      Kq e.hom
  letI : Flat (𝟙 X : X ⟶ X).left := inferInstanceAs (Flat (𝟙 X.left))
  letI : Mono ((P (𝟙 X)).map (kernel.ι m)) := kernel_map_mono m (𝟙 X)
  let s₀ := fst T.X (T.X ⊗ X)
  let t₀ := mulUniversalT (T := T) (X := X)
  let x₀ := mulUniversalX (T := T) (X := X)
  -- The universal composite action is flat, so it preserves the kernel inclusion.
  letI : Flat (actOn a (s₀ * t₀) x₀).left := mulUniversal_endpoint_flat a
  have hmono : Mono ((P (actOn a (s₀ * t₀) x₀)).map (kernel.ι m)) :=
    kernel_map_mono m (actOn a (s₀ * t₀) x₀)
  refine ⟨⟨θ, fun Y x => ⟨actOn_unit_eq a x, unit_of_compatible θ L (kernel.ι m) hc Y x⟩, ?_⟩, hc⟩
  intro Y s t x
  exact ⟨actOn_mul_eq a s t x, mul_from_universal θ
    (mul_of_compatible θ L (kernel.ι m) hc s₀ t₀ x₀ hmono) Y s t x⟩

end LinearizedKernels

section Filtration

open Specs.EquivariantCoherentClosedImage (ClosedImageData)

variable {k : Type u} [Field k] {T : GroupScheme k} {X Z Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Z} {i : Z ⟶ X}
  [IsLocallyNoetherian X.left] [IsClosedImmersion i.left]

private def canonicalClosedImage (hi : IsEquivariantMap a b i) : ClosedImageData i a b where
  pushCoherent H := (pushCoherent hi H).coherent
  pushLinearization H := (pushCoherent hi H).lin
  pullCoherent F := (pullCoherent hi F).coherent
  pullLinearization F := (pullCoherent hi F).lin
  pushClasses := pushClasses hi

private theorem equivariant_closedUnit (hi : IsEquivariantMap a b i)
    (F : EquivariantCoherent a) :
    EquivariantHom (F := F) (H := pushCoherent hi (pullCoherent hi F)) (adjunctionUnit i.left F.sheaf) := by
  let : (Pull i F.sheaf).IsFinitePresentation := (pullCoherent hi F).coherent
  exact directImageLinearization_unit hi F.lin

private def nextTerm (hi : IsEquivariantMap a b i) (F : EquivariantCoherent a) :
    {K : EquivariantCoherent a // K.sheaf = kernel (adjunctionUnit i.left F.sheaf)} := by
  let H := pushCoherent hi (pullCoherent hi F)
  let : F.sheaf.IsFinitePresentation := F.coherent
  let : H.sheaf.IsFinitePresentation := H.coherent
  let m : F.sheaf ⟶ H.sheaf := adjunctionUnit i.left F.sheaf
  let L := kernelLinearization F.lin H.lin (equivariant_closedUnit hi F)
  exact ⟨⟨kernel m, coherent_kernel m, L.val⟩, rfl⟩

private def equivariantSupportTerm (hi : IsEquivariantMap a b i)
    (F : EquivariantCoherent a) : ℕ → EquivariantCoherent a
  | 0 => F
  | n + 1 => (nextTerm hi (equivariantSupportTerm hi F n)).val

private theorem equivariantSupportTerm_sheaf (hi : IsEquivariantMap a b i) (F : EquivariantCoherent a)
    (n : ℕ) : (equivariantSupportTerm hi F n).sheaf = supportTerm i.left F.sheaf n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [equivariantSupportTerm, (nextTerm hi (equivariantSupportTerm hi F n)).property, hn]
    rfl

private theorem nextTerm_exact (hi : IsEquivariantMap a b i) (F : EquivariantCoherent a) :
    let K := (nextTerm hi F).val
    let H := pushCoherent hi (pullCoherent hi F)
    let m := adjunctionUnit i.left F.sheaf
    ∃ (f : K.sheaf ⟶ F.sheaf) (w : f ≫ m = 0),
      EquivariantHom (F := K) (H := F) f ∧ EquivariantHom (F := F) (H := H) m ∧
        (ShortComplex.mk f m w).ShortExact := by
  let H := pushCoherent hi (pullCoherent hi F)
  let : F.sheaf.IsFinitePresentation := F.coherent
  let m : F.sheaf ⟶ H.sheaf := adjunctionUnit i.left F.sheaf
  let L := kernelLinearization F.lin H.lin (equivariant_closedUnit hi F)
  let := closedUnit_epi i.left F.sheaf
  let S := ShortComplex.mk (kernel.ι m) m (kernel.condition m)
  exact ⟨kernel.ι m, kernel.condition m, L.property, equivariant_closedUnit hi F,
    ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel (kernelIsKernel m)) inferInstance inferInstance⟩

private theorem supportFiltration_of_zero_open [CompactSpace X.left] (hi : IsEquivariantMap a b i)
    (j : Y ⟶ X) [IsOpenImmersion j.left] (hj : Set.range j.left = (Set.range i.left)ᶜ)
    (F : EquivariantCoherent a) (hF : IsZero (Pull j F.sheaf)) :
    HasSupportFiltration (canonicalClosedImage hi) F := by
  let := F.coherent
  obtain ⟨n, hn⟩ := supportTerm_eventually_zero i.left j.left hj F.sheaf hF
  let term := equivariantSupportTerm hi F
  let D := canonicalClosedImage hi
  let quotient := fun m => D.push (D.pull (term m))
  have hz : IsZero (term n).sheaf := (equivariantSupportTerm_sheaf hi F n).symm ▸ hn
  refine ⟨n, term, rfl, hz, fun m _ => ?_, ?_⟩
  · exact nextTerm_exact hi (term m)
  · apply classOf_mem_of_filtration (LinearMap.range D.pushClasses) term quotient n hz
    · intro m hm
      obtain ⟨f, w, hf, hg, he⟩ := nextTerm_exact hi (term m)
      exact classOf_exact w hf hg he
    · intro m hm
      exact ⟨classOf (D.pull (term m)), pushClasses_classOf hi (D.pull (term m))⟩

/-- The iterated kernels of the canonical closed adjunction units provide a
finite equivariant coherent filtration of every sheaf supported on the closed
subscheme. Its exact sequences express the ambient class as a closed image. -/
theorem supportFiltration : SupportFiltration.{u} := by
  intro k _ T X Z Y a b c i j _ hX _ hcompact _ hci hoj hi _ hj
  let : LocallyOfFiniteType X.hom := hX
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := hcompact
  let : IsClosedImmersion i.left := hci
  let : IsOpenImmersion j.left := hoj
  exact ⟨canonicalClosedImage hi, pullCoherent_isEquivariantPullback hi,
    pushCoherent_isEquivariantPushforward hi, pushClasses_classOf hi,
    supportFiltration_of_zero_open hi j hj⟩

end Filtration

end

end LinearAlgebraicGroups.Representation.EquivariantCoherentSupportFiltration
