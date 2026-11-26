import Specs.LinearAlgebraicGroups.Cohomology.ArithmeticProjectiveFiniteness
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Module.LocalizedModule.Away
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Representation.FlagCohomology
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs.FlagCohomology
open LinearAlgebraicGroups.Specs.ArithmeticProjectiveFiniteness

universe u v w

namespace LinearAlgebraicGroups.Cohomology.ArithmeticProjectiveFiniteness

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The localization of the integers used for the arithmetic model is Noetherian. -/
theorem baseRing_noetherian (m : ℕ) : IsNoetherianRing (BaseRing.{u} m) := by
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  infer_instance

section ProjectiveCover

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The open chart obtained by making the indicated homogeneous coordinate invertible. -/
abbrev coordinateOpen (i : Fin (n + 1)) : (projectiveSpace A n).left.Opens :=
  Proj.basicOpen (homogeneousGrading A n) (MvPolynomial.X i)

theorem coordinateOpen_isAffine (i : Fin (n + 1)) :
    IsAffineOpen (coordinateOpen A n i) :=
  Proj.isAffineOpen_basicOpen (homogeneousGrading A n) _
    (MvPolynomial.isHomogeneous_X A i) Nat.one_pos

private theorem homogeneousVariables_generate :
    Algebra.adjoin (homogeneousGrading A n 0)
      (Set.range (MvPolynomial.X (R := A) (σ := Fin (n + 1)))) = ⊤ := by
  rw [eq_top_iff]
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a => exact Subalgebra.algebraMap_mem _ (homogeneousConstants A n a)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

theorem iSup_coordinateOpen : (⨆ i, coordinateOpen A n i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1, MvPolynomial.isHomogeneous_X A i⟩)
    (homogeneousVariables_generate A n)

private theorem homogeneousConstants_bijective :
    Function.Bijective (homogeneousConstants A n) := by
  constructor
  · intro a b h
    have hc := congrArg (fun f : homogeneousGrading A n 0 =>
      (f : MvPolynomial (Fin (n + 1)) A).coeff 0) h
    change (MvPolynomial.C a : MvPolynomial (Fin (n + 1)) A).coeff 0 =
      (MvPolynomial.C b : MvPolynomial (Fin (n + 1)) A).coeff 0 at hc
    simpa only [MvPolynomial.coeff_zero_C] using hc
  · intro f
    have hf := f.property
    change (f : MvPolynomial (Fin (n + 1)) A) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A 0 at hf
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at hf
    obtain ⟨a, ha⟩ := hf
    exact ⟨a, Subtype.ext ha⟩

/-- The structural morphism of the ambient projective space is proper over any base ring. -/
theorem projectiveSpace_proper : IsProper (projectiveSpace A n).hom := by
  classical
  have : Algebra.FiniteType (homogeneousGrading A n 0) (MvPolynomial (Fin (n + 1)) A) :=
    ⟨⟨Finset.univ.image MvPolynomial.X, by simpa using homogeneousVariables_generate A n⟩⟩
  have : IsIso (CommRingCat.ofHom (homogeneousConstants A n)) :=
    (RingEquiv.ofBijective _ (homogeneousConstants_bijective A n)).toCommRingCatIso.isIso_hom
  change IsProper (Proj.toSpecZero (homogeneousGrading A n) ≫ Spec.map _)
  infer_instance

variable {A n} {Y : SchemeOverRing A} (j : Y ⟶ projectiveSpace A n)

/-- The inverse images of the homogeneous coordinate charts on a projective subscheme. -/
abbrev projectiveCover (i : ULift.{u} (Fin (n + 1))) : Y.left.Opens :=
  j.left ⁻¹ᵁ coordinateOpen A n i.down

theorem iSup_projectiveCover : (⨆ i, projectiveCover j i) = ⊤ :=
  j.left.iSup_preimage_eq_top (by
    rw [← iSup_coordinateOpen A n]
    exact Equiv.ulift.iSup_congr (fun _ => rfl))

theorem projectiveCover_intersection_isAffine (hj : IsClosedImmersion j.left)
    (s : Finset (ULift.{u} (Fin (n + 1)))) (hs : s.Nonempty) :
    IsAffineOpen (⨅ i ∈ (s : Set (ULift.{u} (Fin (n + 1)))), projectiveCover j i) := by
  let : IsClosedImmersion j.left := hj
  have : Scheme.IsSeparated (projectiveSpace A n).left :=
    inferInstanceAs (Scheme.IsSeparated (Proj (homogeneousGrading A n)))
  let : IsSeparated (terminal.from Y.left) := by
    rw [← terminal.comp_from j.left]
    infer_instance
  exact IsAffineOpen.biInf _ s.finite_toSet hs
    (fun i _ => (coordinateOpen_isAffine A n i.down).preimage j.left)

/-- The rings on the affine chart intersections of the closed subscheme are Noetherian
over a Noetherian base. -/
theorem noetherian_of_isAffineOpen [IsNoetherianRing A]
    (hj : IsClosedImmersion j.left) (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsNoetherianRing Γ(Y.left, U) := by
  have : IsClosedImmersion j.left := hj
  have : IsProper (projectiveSpace A n).hom := projectiveSpace_proper A n
  have : IsProper Y.hom := by
    rw [← Over.w j]
    infer_instance
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  exact IsLocallyNoetherian.component_noetherian ⟨U, hU⟩

end ProjectiveCover

section Cech

variable {A : Type u} [CommRing A] {D : Type*} [CompleteLattice D]
  {I : Type u} [Preorder I] [Fintype I] (U : I → D) (P : Dᵒᵖ ⥤ ModuleCat.{u} A)

/-- An ordered Čech complex has zero homology in degrees at least the number of charts.
This holds over an arbitrary commutative coefficient ring. -/
theorem cechHomology_isZero_of_card_le (i : ℕ) (hi : Fintype.card I ≤ i) :
    IsZero ((cechComplex U P).homology i) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  have : IsEmpty (Fin (i + 1) ↪o I) := ⟨fun e => by
    have h := Fintype.card_le_of_injective e e.injective
    simp only [Fintype.card_fin] at h
    omega⟩
  rw [IsZero.iff_id_eq_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  funext e
  exact isEmptyElim e

end Cech

/-- The standard projective cover on a closed subscheme bounds the derived cohomology
of every quasi-coherent sheaf, with the original ring of scalars. -/
theorem cohomology_isZero_above_dimension
    (comparison : AffineCechComparison.{u})
    {A : Type u} [CommRing A] {Y : SchemeOverRing A} {n : ℕ}
    (j : Y ⟶ projectiveSpace A n) (hj : IsClosedImmersion j.left)
    (F : Y.left.Modules) (hF : (F : SheafOfModules Y.left.ringCatSheaf).IsQuasicoherent)
    (i : ℕ) (hi : n < i) :
    IsZero ((cohomology Y i).obj F) := by
  obtain ⟨e, _⟩ := comparison Y (projectiveCover j) (iSup_projectiveCover j)
    (projectiveCover_intersection_isAffine j hj) i
  apply IsZero.of_iso _ (e F hF)
  exact cechHomology_isZero_of_card_le (projectiveCover j) (coefficientPresheaf F) i (by
    simpa using hi)

section AffineLine

open Scheme.Modules

private theorem finite_sections_of_trivialization {X : Scheme.{u}}
    (F : X.Modules) (U : X.Opens) (h : Nonempty (F.restrict U.ι ≅ structureModule U.toScheme)) :
    Module.Finite Γ(X, U) Γ(F, U) := by
  obtain ⟨e⟩ := h
  have aux (W : X.Opens) (hW : U.ι ''ᵁ ⊤ = W) : Module.Finite Γ(X, W) Γ(F, W) := by
    subst W
    let V : U.toScheme.Opens := ⊤
    let b := F.restrictAppIso U.ι V
    let x := b.hom (e.inv.app V (1 : Γ(U.toScheme, V)))
    apply Module.Finite.of_surjective (LinearMap.toSpanSingleton Γ(X, U.ι ''ᵁ V) _ x)
    intro y
    let z : Γ(U.toScheme, V) := e.hom.app V (b.inv y)
    refine ⟨(U.ι.appIso V).inv z, ?_⟩
    have hh := e.inv.app_smul (U := V) z (1 : Γ(U.toScheme, V))
    change e.inv.app V (z * 1 : Γ(U.toScheme, V)) =
      z • e.inv.app V (1 : Γ(U.toScheme, V)) at hh
    rw [mul_one] at hh
    change (U.ι.appIso V).inv z • b.hom (e.inv.app V (1 : Γ(U.toScheme, V))) = y
    rw [← F.smul_restrictAppIso_hom_apply U.ι V z, ← hh]
    change b.hom (e.inv.app V (e.hom.app V (b.inv y))) = y
    have heq : e.hom.app V ≫ e.inv.app V = 𝟙 _ := by
      rw [← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
    have he (w : Γ(F.restrict U.ι, V)) : e.inv.app V (e.hom.app V w) = w := by
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
        congrArg (fun f : Γ(F.restrict U.ι, V) ⟶ Γ(F.restrict U.ι, V) => f w) heq
    rw [he, Iso.inv_hom_id_apply]
  exact aux U U.ι_image_top

/-- On an affine scheme, the global module of a quasi-coherent line is finite.
The scalar action is the original affine coordinate ring action. -/
theorem finite_affineLine_sections {R : CommRingCat.{u}} (F : (Spec R).Modules)
    (hF : F.IsQuasicoherent)
    (hline : ∀ x : Spec R, ∃ U : (Spec R).Opens, x ∈ U ∧
      Nonempty (F.restrict U.ι ≅ structureModule U.toScheme)) :
    Module.Finite R (moduleSpecΓFunctor.obj F) := by
  let := hF
  let U₀ (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let t : Set R := { r | Nonempty (F.restrict (U₀ r).ι ≅ structureModule (U₀ r).toScheme) }
  have hcover : (⨆ r : t, PrimeSpectrum.basicOpen r.val) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨U, hxU, ⟨e⟩⟩ := hline x
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen _ ≤ U⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    let V := U₀ r
    have hVU : V ≤ U := hrU
    let j := (Spec R).homOfLE hVU
    have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion ((Spec R).homOfLE hVU))
    have hj : j ≫ U.ι = V.ι := Scheme.homOfLE_ι _ _
    have hr : r ∈ t :=
      ⟨(restrictFunctorCongr hj).symm.app F ≪≫ (restrictFunctorComp j U.ι).app F ≪≫
        (restrictFunctor j).mapIso e ≪≫ restrictUnitIso j⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hxr⟩
  have ht : Ideal.span t = ⊤ := by
    simpa only [Subtype.range_val] using PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hcover
  let M := (modulesSpecToSheaf (R := R)).obj F
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing F).mp inferInstance
  let f (r : t) : (moduleSpecΓFunctor.obj F) →ₗ[R] Γ(F, U₀ r.val) :=
    (M.obj.map (U₀ r.val).leTop.op).hom
  have : ∀ r : t, IsLocalizedModule.Away r.val (f r) := fun r => hloc r.val
  exact Module.Finite.of_localizationSpan' t ht f
    fun r => finite_sections_of_trivialization F (U₀ r.val) r.property

private theorem line_trivialOn_restrict {X W : Scheme.{u}} (f : W ⟶ X)
    [IsOpenImmersion f] (F : X.Modules)
    (hF : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (F.restrict U.ι ≅ structureModule U.toScheme)) :
    ∀ x : W, ∃ V : W.Opens, x ∈ V ∧
      Nonempty ((F.restrict f).restrict V.ι ≅ structureModule V.toScheme) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hF (f x)
  let V := f ⁻¹ᵁ U
  let g : V.toScheme ⟶ U.toScheme := f ∣_ U
  have : IsOpenImmersion g := inferInstanceAs (IsOpenImmersion (f ∣_ U))
  have hw : g ≫ U.ι = V.ι ≫ f := morphismRestrict_ι f U
  exact ⟨V, hx, ⟨((restrictFunctorComp V.ι f).app F).symm ≪≫
    (restrictFunctorCongr hw.symm).app F ≪≫ (restrictFunctorComp g U.ι).app F ≪≫
    (restrictFunctor g).mapIso e ≪≫ restrictUnitIso g⟩⟩

/-- Sections of a quasi-coherent line on an affine open are finite over the ring of
that open. -/
theorem finite_line_sections_of_isAffineOpen {X : Scheme.{u}} (F : X.Modules)
    (hF : F.IsQuasicoherent)
    (hline : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty (F.restrict V.ι ≅ structureModule V.toScheme))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(F, U) := by
  let := hF
  let R := Γ(X, U)
  let f := hU.fromSpec
  have htop : f ''ᵁ ⊤ = U := f.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have : IsOpenImmersion f := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hF' : (F.restrict f).IsQuasicoherent :=
    inferInstanceAs (((restrictFunctor f).obj F).IsQuasicoherent)
  have : Module.Finite R (moduleSpecΓFunctor.obj (F.restrict f)) :=
    finite_affineLine_sections _ hF' (line_trivialOn_restrict f F hline)
  have aux (V : X.Opens) (hV : f ''ᵁ ⊤ = V) : Module.Finite Γ(X, V) Γ(F, V) := by
    subst V
    let e := F.restrictAppIso f ⊤
    let σ := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
    have hsmul (r : R) (m : Γ(F.restrict f, ⊤)) : e.hom (r • m) = σ r • e.hom m := by
      rw [smul_Spec_def]
      have hr : (Spec R).presheaf.map (TopologicalSpace.Opens.leTop ⊤).op
          ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso R).inv r := by
        have h : (TopologicalSpace.Opens.leTop (⊤ : (Spec R).Opens)).op = 𝟙 _ :=
          Subsingleton.elim _ _
        have hm := (Spec R).presheaf.map_id (op ⊤)
        rw [h]
        exact (congrArg (fun k : Γ(Spec R, ⊤) ⟶ Γ(Spec R, ⊤) =>
          k ((Scheme.ΓSpecIso R).inv r)) hm).trans (ConcreteCategory.id_apply _)
      rw [hr]
      exact F.smul_restrictAppIso_hom_apply f ⊤ _ m
    let l : (moduleSpecΓFunctor.obj (F.restrict f)) →ₛₗ[σ] Γ(F, f ''ᵁ ⊤) :=
      { toFun := fun m => e.hom m
        map_add' := fun m n => e.hom.hom.map_add m n
        map_smul' := fun r m => hsmul r m }
    apply Module.Finite.of_surjective l
    intro x
    exact ⟨e.inv x, Iso.inv_hom_id_apply e x⟩
  exact aux U htop

end AffineLine

/-- A line on a finite scheme over the affine base has finitely generated global
sections over the same base. -/
theorem finite_sections_of_finite {A : Type u} [CommRing A] (Y : SchemeOverRing A)
    (hY : IsFinite Y.hom) (F : Y.left.Modules) (hF : IsLineBundleOn A Y F) :
    Module.Finite A ((sectionsFunctor Y).obj F) := by
  let := hY
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  let R := Γ(Y.left, ⊤)
  have hR := Y.hom.finite_appTop
  have h : (groundRingHom Y).Finite := hR.comp
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv).surjective)
  let : Algebra A R := (groundRingHom Y).toAlgebra
  have : Module.Finite A R := h
  have : Module.Finite R Γ(F, ⊤) :=
    finite_line_sections_of_isAffineOpen F hF.1 hF.2 ⊤ (isAffineOpen_top Y.left)
  let : Module A Γ(F, ⊤) := Module.compHom _ (groundRingHom Y)
  have : IsScalarTower A R Γ(F, ⊤) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change @Module.Finite A Γ(F, ⊤) _ _ (Module.compHom _ (groundRingHom Y))
  exact @Module.Finite.trans A R Γ(F, ⊤) _ _ (show Algebra A R from inferInstance).toModule
    _ (Module.compHom _ (groundRingHom Y)) _ ‹IsScalarTower A R Γ(F, ⊤)› ‹Module.Finite A R›
    ‹Module.Finite R Γ(F, ⊤)›

/-- Finiteness in all degrees for closed subschemes of relative projective zero-space. -/
theorem finite_cohomology_of_closedImmersion_projectiveZero
    (comparison : AffineCechComparison.{u}) {A : Type u} [CommRing A]
    {Y : SchemeOverRing A} (j : Y ⟶ projectiveSpace A 0) (hj : IsClosedImmersion j.left)
    (F : Y.left.Modules) (hF : IsLineBundleOn A Y F) (i : ℕ) :
    Module.Finite A ((cohomology Y i).obj F) := by
  cases i with
  | zero =>
    have htop : coordinateOpen A 0 0 = ⊤ := by
      rw [← iSup_coordinateOpen A 0]
      exact le_antisymm (le_iSup (coordinateOpen A 0) 0)
        (iSup_le fun j => (Fin.eq_zero j) ▸ le_rfl)
    have hAff : IsAffineOpen (⊤ : (projectiveSpace A 0).left.Opens) :=
      htop ▸ coordinateOpen_isAffine A 0 0
    have : IsAffine ((⊤ : (projectiveSpace A 0).left.Opens).toScheme) := hAff
    have : IsAffine (projectiveSpace A 0).left :=
      IsAffine.of_isIso (Scheme.topIso (projectiveSpace A 0).left).inv
    have : IsProper (projectiveSpace A 0).hom := projectiveSpace_proper A 0
    have : IsFinite (projectiveSpace A 0).hom :=
      IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
    have : IsClosedImmersion j.left := hj
    have hY : IsFinite Y.hom := by
      rw [← Over.w j]
      infer_instance
    have : Module.Finite A ((sectionsFunctor Y).obj F) := finite_sections_of_finite Y hY F hF
    exact Module.Finite.equiv ((cohomologyZero Y).symm.app F).toLinearEquiv
  | succ i =>
    have hz := cohomology_isZero_above_dimension comparison j hj F hF.1 (i + 1) (by omega)
    have : Subsingleton ((cohomology Y (i + 1)).obj F) := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

section FiniteHomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

private theorem finite_of_exact {S : ShortComplex (ModuleCat.{u} A)} (hS : S.Exact)
    [Module.Finite A S.X₁] [Module.Finite A S.X₃] : Module.Finite A S.X₂ := by
  have : IsNoetherian A S.X₂ :=
    isNoetherian_of_range_eq_ker S.f.hom S.g.hom hS.moduleCat_range_eq_ker
  infer_instance

/-- Finiteness in the middle of a segment of the cohomology long exact sequence. -/
theorem finite_homology_of_shortExact
    {S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ)} (hS : S.ShortExact) (i : ℕ)
    (h₂ : Module.Finite A (S.X₂.homology i))
    (h₁ : Module.Finite A (S.X₁.homology (i + 1))) :
    Module.Finite A (S.X₃.homology i) := by
  exact finite_of_exact (hS.homology_exact₃ i (i + 1) rfl)

/-- Descending induction for a class of bounded complexes with short exact
presentations. Only the left term of each presentation needs to remain in the class
and only the middle term needs to have finitely generated cohomology. -/
theorem finite_homology_of_presentations
    (P : CochainComplex (ModuleCat.{u} A) ℕ → Prop) (N : ℕ)
    (bounded : ∀ C, P C → ∀ i ≥ N, IsZero (C.homology i))
    (presentation : ∀ C, P C →
      ∃ (S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ)),
        S.ShortExact ∧ P S.X₁ ∧ (∀ i, Module.Finite A (S.X₂.homology i)) ∧
          Nonempty (S.X₃ ≅ C)) :
    ∀ C, P C → ∀ i, Module.Finite A (C.homology i) := by
  suffices ∀ (d i : ℕ), N ≤ i + d → ∀ C, P C → Module.Finite A (C.homology i) by
    intro C hC i
    exact this N i (Nat.le_add_left N i) C hC
  intro d
  induction d with
  | zero =>
    intro i hi C hC
    have : Subsingleton (C.homology i) :=
      ModuleCat.isZero_iff_subsingleton.mp (bounded C hC i (by simpa using hi))
    infer_instance
  | succ d ih =>
    intro i hi C hC
    obtain ⟨S, hS, h₁, h₂, ⟨e⟩⟩ := presentation C hC
    have : Module.Finite A (S.X₃.homology i) :=
      finite_homology_of_shortExact hS i (h₂ i) (ih (i + 1) (by omega) S.X₁ h₁)
    let e' : S.X₃.homology i ≅ C.homology i :=
      (HomologicalComplex.homologyFunctor _ _ i).mapIso e
    exact Module.Finite.equiv e'.toLinearEquiv

end FiniteHomology

section MonomialCochains

open scoped BigOperators

variable {I : Type v} [LinearOrder I] {A : Type u} [CommRing A]

private def position (s : Finset I) (a : I) : ℕ := (s.filter (· < a)).card

private theorem position_insert (s : Finset I) (a b : I) (ha : a ∉ s) :
    position (insert a s) b = position s b + if a < b then 1 else 0 := by
  unfold position
  rw [Finset.filter_insert]
  by_cases hab : a < b
  · rw [ite_eq_left hab, ite_eq_left hab, Finset.card_insert_of_notMem]
    exact fun h => ha (Finset.mem_filter.mp h).1
  · simp [hab]

private theorem position_erase (s : Finset I) (a b : I) (ha : a ∈ s) :
    position s b = position (s.erase a) b + if a < b then 1 else 0 := by
  simpa only [Finset.insert_erase ha] using
    position_insert (s.erase a) a b (Finset.notMem_erase a s)

private def faceSign (A : Type u) [CommRing A] (s : Finset I) (a : I) : A :=
  (-1 : A) ^ position s a

private theorem faceSign_sq (s : Finset I) (a : I) :
    faceSign A s a * faceSign A s a = 1 := by
  unfold faceSign
  rw [← mul_pow]
  simp

/-- The signed deletion differential written on finite subsets of the ordered chart set.
Here the value at the empty set is included to allow an augmentation. -/
def monomialDifferential (f : Finset I → A) (s : Finset I) : A :=
  ∑ a ∈ s, faceSign A s a * f (s.erase a)

/-- Insertion of an index on which the monomial has a nonnegative exponent. -/
def monomialCone (c : I) (f : Finset I → A) (s : Finset I) : A :=
  if c ∈ s then 0 else faceSign A s c * f (insert c s)

private theorem faceSign_insert_self (s : Finset I) (c : I) (hc : c ∉ s) :
    faceSign A (insert c s) c = faceSign A s c := by
  simp [faceSign, position_insert s c c hc]

private theorem faceSign_erase_mul (s : Finset I) (a c : I) (ha : a ∈ s) (hc : c ∉ s) :
    faceSign A s a * faceSign A (s.erase a) c =
      -(faceSign A s c * faceSign A (insert c s) a) := by
  unfold faceSign
  rw [position_insert s c a hc, position_erase s a c ha]
  have hac : a ≠ c := fun h => hc (h ▸ ha)
  rcases lt_or_gt_of_ne hac with h | h
  · simp [h, h.not_gt, pow_succ, mul_comm]
  · simp [h, h.not_gt, pow_succ, mul_comm]

/-- The insertion homotopy for a monomial, with the same signs as ordered deletion. -/
theorem monomialDifferential_cone (c : I) (f : Finset I → A) (s : Finset I) :
    monomialDifferential (monomialCone c f) s +
      monomialCone c (monomialDifferential f) s = f s := by
  by_cases hc : c ∈ s
  · rw [monomialCone, ite_eq_left hc, add_zero, monomialDifferential]
    rw [Finset.sum_eq_single c]
    · rw [monomialCone, ite_eq_right (Finset.notMem_erase _ _), Finset.insert_erase hc,
        ← faceSign_insert_self (s.erase c) c (Finset.notMem_erase _ _),
        Finset.insert_erase hc, ← mul_assoc, faceSign_sq, one_mul]
    · intro a ha hac
      simp [monomialCone, Finset.mem_erase.mpr ⟨Ne.symm hac, hc⟩]
    · exact fun h => (h hc).elim
  · rw [monomialCone, ite_eq_right hc, monomialDifferential, monomialDifferential,
      Finset.sum_insert hc, Finset.erase_insert hc, faceSign_insert_self s c hc,
      mul_add, ← mul_assoc, faceSign_sq, one_mul, Finset.mul_sum]
    have hsum :
        (∑ a ∈ s, faceSign A s a * monomialCone c f (s.erase a)) =
          -(∑ a ∈ s, faceSign A s c * (faceSign A (insert c s) a * f ((insert c s).erase a))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have hac : a ≠ c := fun h => hc (h ▸ ha)
      rw [monomialCone, ite_eq_right (fun h => hc (Finset.mem_of_mem_erase h)),
        Finset.erase_insert_of_ne hac.symm, ← mul_assoc, ← mul_assoc, faceSign_erase_mul s a c ha hc,
        neg_mul]
    rw [hsum]
    abel

/-- Inserting a coordinate outside the negative support preserves the allowed supports. -/
theorem monomialCone_eq_zero_of_not_subset (negative : Finset I) {c : I}
    (hc : c ∉ negative) (f : Finset I → A) (hf : ∀ s, ¬ negative ⊆ s → f s = 0)
    (s : Finset I) (hs : ¬ negative ⊆ s) : monomialCone c f s = 0 := by
  by_cases hcs : c ∈ s
  · simp [monomialCone, hcs]
  · have hn : ¬ negative ⊆ insert c s := by
      refine fun h => hs fun a ha => ?_
      exact (Finset.mem_insert.mp (h ha)).resolve_left fun e => hc (e ▸ ha)
    simp [monomialCone, hcs, hf _ hn]

variable [Fintype I]

/-- Integer exponent vectors of the fixed Laurent degree. -/
abbrev LaurentExponents (I : Type v) [Fintype I] (d : ℤ) :=
  { e : I → ℤ // ∑ i, e i = d }

/-- These are precisely the two types of exponent vectors that are not eliminated
by the insertion homotopy in the unaugmented projective Čech complex. -/
def isExceptionalExponent {d : ℤ} (e : LaurentExponents I d) : Prop :=
  (∀ i, 0 ≤ e.val i) ∨ (∀ i, e.val i < 0)

omit [LinearOrder I] in
/-- There are only finitely many nonnegative or strictly negative exponent vectors
of a fixed total degree. -/
theorem finite_exceptionalExponents (d : ℤ) :
    Finite {e : LaurentExponents I d // isExceptionalExponent e} := by
  let B := (|d| : ℤ)
  have bound (e : LaurentExponents I d) (he : isExceptionalExponent e) (i : I) :
      e.val i ∈ Set.Icc (-B) B := by
    obtain h | h := he
    · have hi : e.val i ≤ ∑ j, e.val j := Finset.single_le_sum (fun j _ => h j) (Finset.mem_univ i)
      rw [e.property] at hi
      exact ⟨(neg_nonpos.mpr (abs_nonneg d)).trans (h i), hi.trans (le_abs_self d)⟩
    · have hi : -e.val i ≤ ∑ j, -e.val j :=
        Finset.single_le_sum (fun j _ => neg_nonneg.mpr (h j).le) (Finset.mem_univ i)
      rw [Finset.sum_neg_distrib, e.property] at hi
      exact ⟨(neg_abs_le d).trans (by simpa only [neg_neg] using neg_le_neg hi),
        (h i).le.trans (abs_nonneg d)⟩
  let toBox (e : {e : LaurentExponents I d // isExceptionalExponent e}) :
      I → Set.Icc (-B) B :=
    fun i => ⟨e.val.val i, bound e.val e.property i⟩
  exact Finite.of_injective toBox fun e f h =>
    Subtype.ext (Subtype.ext (funext fun i => congrArg (fun a => (a i).val) h))

/-- Indices for which the indicated Laurent monomial needs a denominator. -/
def negativeSupport {d : ℤ} (e : LaurentExponents I d) : Finset I :=
  Finset.univ.filter fun i => e.val i < 0

/-- In the Laurent model of the ordered Čech complex, every cocycle becomes
supported on the exceptional exponent vectors after subtracting one coboundary.
The primitive uses finitely supported Laurent coefficients on every intersection. -/
theorem laurent_cocycle_reduce_to_exceptional {d : ℤ} (n : ℕ)
    (f : Finset I → LaurentExponents I d →₀ A)
    (hf : ∀ s e, (s.card ≠ n + 1 ∨ ¬ negativeSupport e ⊆ s) → f s e = 0)
    (closed : ∀ s e, s.card = n + 2 → monomialDifferential (fun t => f t e) s = 0) :
    ∃ g : Finset I → LaurentExponents I d →₀ A,
      (∀ s e, (s.card ≠ n ∨ ¬ negativeSupport e ⊆ s) → g s e = 0) ∧
      g ∅ = 0 ∧
      ∀ s e, ¬ isExceptionalExponent e →
        f s e = monomialDifferential (fun t => g t e) s := by
  classical
  have noNegative (e : LaurentExponents I d) (he : ¬isExceptionalExponent e) :
      (negativeSupport e).Nonempty := by
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => he (Or.inl h))
    exact ⟨i, by simp [negativeSupport, lt_of_not_ge hi]⟩
  have hasPivot (e : LaurentExponents I d) (he : ¬isExceptionalExponent e) :
      ∃ i, i ∉ negativeSupport e := by
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => he (Or.inr h))
    exact ⟨i, by simpa [negativeSupport] using hi⟩
  choose pivot hpivot using hasPivot
  let T : Finset (LaurentExponents I d) := Finset.univ.biUnion fun s => (f s).support
  have allZero (e : LaurentExponents I d) (he : e ∉ T) (s : Finset I) :
      f s e = 0 := by
    apply Finsupp.notMem_support_iff.mp
    exact fun h => he (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, h⟩)
  let primitive (s : Finset I) (e : LaurentExponents I d) : A :=
    if he : isExceptionalExponent e then 0 else monomialCone (pivot e he) (fun t => f t e) s
  have primitive_finite (s : Finset I) (e : LaurentExponents I d) :
      primitive s e ≠ 0 → e ∈ T := by
    intro h
    by_contra he
    exact h (by simp [primitive, monomialCone, allZero e he])
  let g (s : Finset I) : LaurentExponents I d →₀ A :=
    Finsupp.onFinset T (primitive s) (primitive_finite s)
  have g_eval (s : Finset I) (e : LaurentExponents I d) : g s e = primitive s e := rfl
  have g_support (s : Finset I) (e : LaurentExponents I d)
      (hs : s.card ≠ n ∨ ¬negativeSupport e ⊆ s) : g s e = 0 := by
    rw [g_eval]
    by_cases he : isExceptionalExponent e
    · simp [primitive, he]
    · simp only [primitive, dite_eq_right he]
      rcases hs with hcard | hsub
      · by_cases hb : pivot e he ∈ s
        · simp [monomialCone, hb]
        · have hwrong : (insert (pivot e he) s).card ≠ n + 1 := by
            rw [Finset.card_insert_of_notMem hb]
            omega
          simp [monomialCone, hb, hf _ _ (Or.inl hwrong)]
      · exact monomialCone_eq_zero_of_not_subset _ (hpivot e he) _
          (fun t ht => hf t e (Or.inr ht)) s hsub
  have dg_const (s : Finset I) (e : LaurentExponents I d) :
      monomialDifferential (fun t => f t e) s = 0 := by
    by_cases hs : s.card = n + 2
    · exact closed s e hs
    · apply Finset.sum_eq_zero
      intro a ha
      have hcard : (s.erase a).card ≠ n + 1 := by
        have := Finset.card_erase_add_one ha
        omega
      simp [hf _ _ (Or.inl hcard)]
  refine ⟨g, g_support, ?_, ?_⟩
  · ext e
    by_cases he : isExceptionalExponent e
    · simp [g_eval, primitive, he]
    · apply g_support
      exact Or.inr fun h => by
        obtain ⟨a, ha⟩ := noNegative e he
        exact Finset.notMem_empty a (h ha)
  · intro s e he
    have hgp (t : Finset I) :
        g t e = monomialCone (pivot e he) (fun w => f w e) t := by
      simp [g_eval, primitive, he]
    have hh := monomialDifferential_cone (pivot e he) (fun t => f t e) s
    simpa only [dg_const, monomialCone, mul_zero, ite_self, add_zero,
      ← funext hgp] using hh.symm

end MonomialCochains

section LaurentModel

variable {I : Type v} {A : Type u} [LinearOrder I] [Fintype I] [CommRing A] {d : ℤ}

/-- Laurent cochains with the prescribed number of indices and allowed denominators. -/
def laurentCochains (A : Type u) [CommRing A] (I : Type v) [LinearOrder I] [Fintype I]
    (d : ℤ) (k : ℕ) : Submodule A (Finset I → LaurentExponents I d →₀ A) where
  carrier := {f | ∀ s e, (s.card ≠ k ∨ ¬negativeSupport e ⊆ s) → f s e = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' hf hg := fun s e h => by simp [hf s e h, hg s e h]
  smul_mem' a _ hf := fun s e h => by simp [hf s e h]

private theorem finite_homology_of_representatives
    (S : ShortComplex (ModuleCat.{u} A)) (V : Submodule A (LinearMap.ker S.g.hom))
    [Module.Finite A V]
    (hV : ∀ x : LinearMap.ker S.g.hom, ∃ v : V, x - v.val ∈ S.moduleCatToCycles.range) :
    Module.Finite A S.homology := by
  let Q := S.moduleCatToCycles.range
  have h : Module.Finite A (LinearMap.ker S.g.hom ⧸ Q) := by
    apply Module.Finite.of_surjective (Q.mkQ.comp V.subtype)
    intro z
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective z
    obtain ⟨v, hv⟩ := hV x
    exact ⟨v, ((Submodule.Quotient.eq Q).mpr hv).symm⟩
  have : Module.Finite A S.moduleCatLeftHomologyData.H := h
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

/-- A complex with the term and differential identifications of the Laurent model has
finite homology. This packages the monomial computation independently of the Proj charts. -/
theorem finite_homology_of_laurent_model [IsNoetherianRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ)
    (coord : ∀ k, C.X k ≃ₗ[A] laurentCochains A I d (k + 1))
    (differential : ∀ (k : ℕ) (x : C.X k) (s : Finset I) (e : LaurentExponents I d),
      s.card = k + 2 →
      (coord (k + 1) (C.d k (k + 1) x)).val s e =
        monomialDifferential (fun t => (coord k x).val t e) s)
    (i : ℕ) : Module.Finite A (C.homology i) := by
  classical
  let S := C.sc' (i - 1) i (i + 1)
  suffices h : Module.Finite A S.homology by
    let e := (ShortComplex.homologyFunctor _).mapIso
      (C.isoSc' (i := i - 1) (j := i) (k := i + 1) (by cases i <;> simp) (by simp))
    have : Module.Finite A ((ShortComplex.homologyFunctor (ModuleCat.{u} A)).obj S) := h
    change Module.Finite A ((ShortComplex.homologyFunctor (ModuleCat.{u} A)).obj (C.sc i))
    exact Module.Finite.equiv e.symm.toLinearEquiv
  let Q := LinearMap.ker S.g.hom
  let E : Q →ₗ[A] (Finset I → LaurentExponents I d →₀ A) :=
    (laurentCochains A I d (i + 1)).subtype.comp ((coord i).toLinearMap.comp Q.subtype)
  let V : Submodule A Q :=
    { carrier := {x | ∀ s e, ¬isExceptionalExponent e → E x s e = 0}
      zero_mem' := by intro s e _; simp only [map_zero, Pi.zero_apply, Finsupp.zero_apply]
      add_mem' := fun {x y} hx hy s e he => by
        simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx s e he, hy s e he, add_zero]
      smul_mem' := fun a x hx s e he => by
        simp only [map_smul, Pi.smul_apply, Finsupp.smul_apply, hx s e he, smul_zero] }
  let K := {e : LaurentExponents I d // isExceptionalExponent e}
  let : Finite K := finite_exceptionalExponents d
  let l : V →ₗ[A] (Finset I → K → A) :=
    { toFun := fun v s e => E v.val s e.val
      map_add' := by
        intros
        funext s e
        simp only [Submodule.coe_add, map_add, Pi.add_apply, Finsupp.add_apply]
      map_smul' := by
        intros
        funext s e
        simp only [RingHom.id_apply, Submodule.coe_smul, map_smul, Pi.smul_apply,
          Finsupp.smul_apply] }
  have hl : Function.Injective l := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply (coord i).injective
    apply Subtype.ext
    funext s
    ext e
    by_cases he : isExceptionalExponent e
    · exact congrFun (congrFun h s) (⟨e, he⟩ : K)
    · exact (x.property s e he).trans (y.property s e he).symm
  have : IsNoetherian A V := isNoetherian_of_injective l hl
  apply finite_homology_of_representatives S V
  intro x
  let f := (coord i x.val).val
  have hclosed (s : Finset I) (e : LaurentExponents I d) (hs : s.card = i + 2) :
      monomialDifferential (fun t => f t e) s = 0 := by
    rw [← differential i x.val s e hs]
    have hx : C.d i (i + 1) x.val = 0 := x.property
    simp [hx]
  obtain ⟨g, hg, hg₀, hred⟩ :=
    laurent_cocycle_reduce_to_exceptional i f (coord i x.val).property hclosed
  cases i with
  | zero =>
    have hz (s : Finset I) (e : LaurentExponents I d) : g s e = 0 := by
      by_cases hs : s.card = 0
      · rw [Finset.card_eq_zero.mp hs, hg₀]
        rfl
      · exact hg s e (Or.inl hs)
    have hx : x ∈ V := fun s e he => by
      change f s e = 0
      simpa [monomialDifferential, hz] using hred s e he
    exact ⟨⟨x, hx⟩, by simp⟩
  | succ i =>
    let y : C.X i := (coord i).symm ⟨g, hg⟩
    let b : Q := S.moduleCatToCycles y
    have hb (s : Finset I) (e : LaurentExponents I d) (hs : s.card = i + 2) :
        (coord (i + 1) b.val).val s e =
          monomialDifferential (fun t => g t e) s := by
      change (coord (i + 1) (C.d i (i + 1) y)).val s e = _
      simpa [y] using differential i y s e hs
    have hx : x - b ∈ V := by
      intro s e he
      simp only [map_sub, Pi.sub_apply, Finsupp.sub_apply, sub_eq_zero]
      change (coord (i + 1) x.val).val s e = (coord (i + 1) b.val).val s e
      by_cases hs : s.card = i + 2
      · exact (hred s e he).trans (hb s e hs).symm
      · exact ((coord (i + 1) x.val).property s e (Or.inl hs)).trans
          ((coord (i + 1) b.val).property s e (Or.inl hs)).symm
    refine ⟨⟨x - b, hx⟩, ?_⟩
    change x - (x - b) ∈ S.moduleCatToCycles.range
    have heq : x - (x - b) = b := by abel
    rw [heq]
    exact ⟨y, rfl⟩


end LaurentModel

section OrderedTuples

variable {I : Type v} [LinearOrder I]

/-- The finite subset of indices enumerated by an ordered tuple. -/
def tupleFinset {k : ℕ} (e : Fin k ↪o I) : Finset I :=
  Finset.univ.map e.toEmbedding

@[simp]
theorem card_tupleFinset {k : ℕ} (e : Fin k ↪o I) : (tupleFinset e).card = k := by
  simp [tupleFinset]

@[simp]
theorem mem_tupleFinset {k : ℕ} (e : Fin k ↪o I) (a : I) :
    a ∈ tupleFinset e ↔ a ∈ Set.range e := by
  simp [tupleFinset, Set.mem_range, RelEmbedding.coe_toEmbedding]

@[simp]
theorem orderEmbOfFin_tupleFinset {k : ℕ} (e : Fin k ↪o I) :
    (tupleFinset e).orderEmbOfFin (card_tupleFinset e) = e :=
  (Finset.orderEmbOfFin_unique' _ (fun j => (mem_tupleFinset e _).mpr ⟨j, rfl⟩)).symm

@[simp]
theorem tupleFinset_orderEmbOfFin (s : Finset I) {k : ℕ} (h : s.card = k) :
    tupleFinset (s.orderEmbOfFin h) = s := by
  ext a
  rw [mem_tupleFinset, Finset.range_orderEmbOfFin]
  rfl

private theorem tupleFinset_delete {k : ℕ} (e : Fin (k + 1) ↪o I) (i : Fin (k + 1)) :
    tupleFinset (i.succAboveOrderEmb.trans e) = (tupleFinset e).erase (e i) := by
  ext a
  simp only [mem_tupleFinset, Finset.mem_erase, Set.mem_range, RelEmbedding.trans_apply,
    Fin.succAboveOrderEmb_apply]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne i j (e.injective h), ⟨_, rfl⟩⟩
  · rintro ⟨h, j, rfl⟩
    have hj : j ∈ Set.range i.succAbove := by
      rw [Fin.range_succAbove]
      exact fun he => h (congrArg e he)
    obtain ⟨r, hr⟩ := hj
    exact ⟨r, congrArg e hr⟩

private theorem card_filter_tupleFinset_lt {k : ℕ} (e : Fin k ↪o I) (j : Fin k) :
    ((tupleFinset e).filter (· < e j)).card = (j : ℕ) := by
  rw [tupleFinset, Finset.filter_map (p := fun a => a < e j)]
  rw [Finset.card_map]
  have h : Finset.univ.filter ((· < e j) ∘ e.toEmbedding) =
      Finset.univ.filter (fun i : Fin k => (i : ℕ) < j.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change e i < e j ↔ (i : ℕ) < j.val
    exact e.lt_iff_lt
  rw [h, Fin.card_filter_val_lt, min_eq_right j.isLt.le]


end OrderedTuples

section LaurentPolynomials

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

variable {I : Type v} [Fintype I] [DecidableEq I]
variable {A : Type u} [CommRing A]

/-- A Laurent monomial's exponent on one coordinate. -/
private def unitExponent (i : I) : I → ℤ := Pi.single i 1

private def chartExponent (s : Finset I) : I → ℤ := ∑ i ∈ s, unitExponent i

private theorem chartExponent_apply (s : Finset I) (i : I) :
    chartExponent s i = if i ∈ s then 1 else 0 := by
  simp [chartExponent, unitExponent, Pi.single_apply]

private theorem sum_chartExponent (s : Finset I) : ∑ i, chartExponent s i = (s.card : ℤ) := by
  simp [chartExponent_apply, Finset.sum_ite_mem]

private theorem sum_unitExponent (i : I) : ∑ j, unitExponent i j = 1 := by
  simp [unitExponent, Pi.single_apply]

/-- Laurent polynomials in the homogeneous coordinates. -/
abbrev LaurentPolynomial (A : Type u) (I : Type v) [CommRing A] := AddMonoidAlgebra A (I → ℤ)

private abbrev laurentMonomial (e : I → ℤ) : LaurentPolynomial A I :=
  AddMonoidAlgebra.single e 1

private theorem laurentMonomial_add (e f : I → ℤ) :
    (laurentMonomial (A := A) (e + f)) = laurentMonomial e * laurentMonomial f := by
  rw [AddMonoidAlgebra.single_mul_single, mul_one]

private theorem laurentMonomial_nsmul (k : ℕ) (e : I → ℤ) :
    laurentMonomial (A := A) (k • e) = laurentMonomial e ^ k := by
  induction k with
  | zero =>
    rw [zero_nsmul, pow_zero]
    rfl
  | succ k h => rw [succ_nsmul, laurentMonomial_add, h, pow_succ]

private theorem isUnit_laurentMonomial (e : I → ℤ) :
    IsUnit (laurentMonomial (A := A) e) := by
  refine isUnit_iff_exists_inv.mpr ⟨laurentMonomial (-e), ?_⟩
  rw [← laurentMonomial_add, add_neg_cancel]
  rfl

private def polynomialExponent : (I →₀ ℕ) →+ (I → ℤ) where
  toFun e i := e i
  map_zero' := rfl
  map_add' e f := by ext; simp

private theorem polynomialExponent_injective : Function.Injective (polynomialExponent (I := I)) := by
  intro e f h
  ext i
  exact Int.ofNat_inj.mp (congrFun h i)

private def polynomialToLaurent : MvPolynomial I A →ₐ[A] LaurentPolynomial A I :=
  AddMonoidAlgebra.mapDomainAlgHom A A polynomialExponent

private theorem polynomialToLaurent_injective :
    Function.Injective (polynomialToLaurent (I := I) (A := A)) :=
  AddMonoidAlgebra.mapDomain_injective polynomialExponent_injective

@[simp]
private theorem polynomialToLaurent_monomial (e : I →₀ ℕ) (a : A) :
    polynomialToLaurent (MvPolynomial.monomial e a) =
      AddMonoidAlgebra.single (polynomialExponent e) a :=
  AddMonoidAlgebra.mapDomain_single

@[simp]
private theorem polynomialToLaurent_X (i : I) :
    polynomialToLaurent (MvPolynomial.X (R := A) i) = laurentMonomial (unitExponent i) := by
  rw [MvPolynomial.X, polynomialToLaurent_monomial]
  congr 1
  ext j
  simp [polynomialExponent, Pi.single_apply, unitExponent, Finsupp.single_apply, eq_comm]

/-- The homogeneous polynomial cutting out the complement of a chart intersection. -/
def chartProduct (A : Type u) [CommRing A] (s : Finset I) : MvPolynomial I A :=
  ∏ i ∈ s, MvPolynomial.X i

private theorem chartProduct_mem (s : Finset I) :
    chartProduct A s ∈ MvPolynomial.homogeneousSubmodule I A s.card := by
  induction s using Finset.induction_on with
  | empty =>
    change (1 : MvPolynomial I A) ∈ MvPolynomial.homogeneousSubmodule I A 0
    exact MvPolynomial.isHomogeneous_C I (1 : A)
  | insert i s hi h =>
    rw [chartProduct, Finset.prod_insert hi, Finset.card_insert_of_notMem hi, add_comm]
    exact SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X A i) h

@[simp]
private theorem polynomialToLaurent_chartProduct (s : Finset I) :
    polynomialToLaurent (chartProduct A s) = laurentMonomial (chartExponent s) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [chartProduct, chartExponent]
    rfl
  | insert i s hi h =>
    rw [chartProduct, Finset.prod_insert hi, map_mul, polynomialToLaurent_X, ← chartProduct, h]
    rw [show chartExponent (insert i s) = unitExponent i + chartExponent s by
      simp only [chartExponent, Finset.sum_insert hi], laurentMonomial_add]

/-- A monomial of degree `d` whose only denominators are coordinates in `s`. -/
def AllowedExponent (s : Finset I) (d : ℤ) (e : I → ℤ) : Prop :=
  (∑ i, e i) = d ∧ ∀ i ∉ s, 0 ≤ e i

/-- Degree and denominator conditions on the finite Laurent support. -/
def HasAllowedExponents (s : Finset I) (d : ℤ) (f : LaurentPolynomial A I) : Prop :=
  ∀ e, f.coeff e ≠ 0 → AllowedExponent s d e

private theorem allowedExponent_add {s : Finset I} {a b : ℤ} {e f : I → ℤ}
    (he : AllowedExponent s a e) (hf : AllowedExponent s b f) :
    AllowedExponent s (a + b) (e + f) := by
  refine ⟨by simp [Finset.sum_add_distrib, he.1, hf.1], fun i hi => add_nonneg (he.2 i hi) (hf.2 i hi)⟩

private theorem allowedExponents_add {s : Finset I} {d : ℤ} {f g : LaurentPolynomial A I}
    (hf : HasAllowedExponents s d f) (hg : HasAllowedExponents s d g) :
    HasAllowedExponents s d (f + g) := by
  intro e h
  by_contra he
  exact h (by simp [show f.coeff e = 0 from not_not.mp (fun hn => he (hf e hn)),
    show g.coeff e = 0 from not_not.mp (fun hn => he (hg e hn))])

private theorem allowedExponents_smul {s : Finset I} {d : ℤ} {f : LaurentPolynomial A I}
    (hf : HasAllowedExponents s d f) (a : A) : HasAllowedExponents s d (a • f) := by
  intro e h
  apply hf
  intro hz
  exact h (by simp [hz])

private theorem allowedExponents_single {s : Finset I} {d : ℤ} {e : I → ℤ}
    (he : AllowedExponent s d e) (a : A) :
    HasAllowedExponents s d (AddMonoidAlgebra.single e a) := by
  classical
  intro f hf
  by_cases h : e = f
  · simpa only [← h] using he
  · exact (hf (by simp [h])).elim

private theorem allowedExponents_mul {s : Finset I} {a b : ℤ} {f g : LaurentPolynomial A I}
    (hf : HasAllowedExponents s a f) (hg : HasAllowedExponents s b g) :
    HasAllowedExponents s (a + b) (f * g) := by
  classical
  intro e h
  rw [AddMonoidAlgebra.coeff_mul] at h
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  change (if x + y = e then f.coeff x * g.coeff y else 0) ≠ 0 at hy
  by_cases hxy : x + y = e
  · rw [ite_eq_left hxy] at hy
    rw [← hxy]
    exact allowedExponent_add (hf x (left_ne_zero_of_mul hy)) (hg y (right_ne_zero_of_mul hy))
  · exact (hy (ite_eq_right hxy)).elim

/-- The degree zero Laurent polynomials on a chart intersection. -/
def laurentChartRing (A : Type u) [CommRing A] (s : Finset I) :
    Subalgebra A (LaurentPolynomial A I) where
  carrier := {f | HasAllowedExponents s 0 f}
  mul_mem' {f g} hf hg := by
    change HasAllowedExponents s 0 (f * g)
    simpa only [add_zero] using allowedExponents_mul hf hg
  add_mem' := allowedExponents_add
  algebraMap_mem' a := allowedExponents_single ⟨by simp, fun i _ => le_rfl⟩ a

/-- The degree-`d` pieces of the Laurent rings are modules over the degree-zero part. -/
def laurentChartModule (A : Type u) [CommRing A] (s : Finset I) (d : ℤ) :
    Submodule (laurentChartRing A s) (LaurentPolynomial A I) where
  carrier := {f | HasAllowedExponents s d f}
  zero_mem' := fun _ h => (h rfl).elim
  add_mem' := allowedExponents_add
  smul_mem' a f hf := by
    change HasAllowedExponents s d (a.val * f)
    simpa only [zero_add] using allowedExponents_mul a.property hf

theorem laurentChartAllowed_mono {s t : Finset I} {d : ℤ} {f : LaurentPolynomial A I}
    (h : s ⊆ t) (hf : HasAllowedExponents s d f) : HasAllowedExponents t d f :=
  fun e he => ⟨(hf e he).1, fun i hi => (hf e he).2 i (fun hs => hi (h hs))⟩

/-- Restriction along inclusion of the sets of inverted variables. -/
def laurentChartRestrict {s t : Finset I} (h : s ⊆ t) :
    laurentChartRing A s →ₐ[A] laurentChartRing A t :=
  Subalgebra.inclusion (fun _ hf => laurentChartAllowed_mono h hf)


private abbrev degreeGrading (A : Type u) [CommRing A] (I : Type v) :=
  MvPolynomial.homogeneousSubmodule I A

private theorem chartProduct_unit (s : Finset I)
    (y : Submonoid.powers (chartProduct A s)) : IsUnit (polynomialToLaurent y.val) := by
  obtain ⟨k, hk⟩ := y.property
  rw [← hk, map_pow, polynomialToLaurent_chartProduct]
  exact (isUnit_laurentMonomial _).pow k

private def awayToLaurent (s : Finset I) :
    Localization.Away (chartProduct A s) →+* LaurentPolynomial A I :=
  IsLocalization.lift (chartProduct_unit s)

private theorem awayToLaurent_injective (s : Finset I) :
    Function.Injective (awayToLaurent (A := A) s) :=
  (IsLocalization.lift_injective_iff _).mpr fun x y => ⟨fun h => by
    have h' := congrArg (awayToLaurent (A := A) s) h
    simpa only [awayToLaurent, IsLocalization.lift_eq] using h', fun h => by
      rw [polynomialToLaurent_injective h]⟩

private def homogeneousToLaurent (s : Finset I) :
    HomogeneousLocalization.Away (degreeGrading A I) (chartProduct A s) →+*
      LaurentPolynomial A I :=
  (awayToLaurent s).comp (algebraMap _ _)

private theorem homogeneousToLaurent_injective (s : Finset I) :
    Function.Injective (homogeneousToLaurent (A := A) s) :=
  (awayToLaurent_injective s).comp (HomogeneousLocalization.val_injective _)

private theorem homogeneousToLaurent_mk (s : Finset I) (k : ℕ) (f : MvPolynomial I A)
    (hf : f ∈ degreeGrading A I (k • s.card)) :
    homogeneousToLaurent s (HomogeneousLocalization.Away.mk _ (chartProduct_mem s) k f hf) =
      polynomialToLaurent f * laurentMonomial (-(k • chartExponent s)) := by
  change awayToLaurent s (HomogeneousLocalization.val
    (HomogeneousLocalization.Away.mk _ (chartProduct_mem s) k f hf)) = _
  simp only [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
  change polynomialToLaurent f = polynomialToLaurent (chartProduct A s ^ k) * _
  rw [map_pow, polynomialToLaurent_chartProduct, ← laurentMonomial_nsmul, mul_left_comm,
    ← laurentMonomial_add, add_neg_cancel]
  exact (mul_one _).symm

private theorem polynomialToLaurent_coeff_nonzero (f : MvPolynomial I A) (e : I → ℤ)
    (he : (polynomialToLaurent f).coeff e ≠ 0) :
    ∃ a : I →₀ ℕ, polynomialExponent a = e ∧ f.coeff a ≠ 0 := by
  change Finsupp.mapDomain polynomialExponent f.coeff e ≠ 0 at he
  obtain ⟨a, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero he
  rw [Finsupp.mapDomain_apply_of_injective polynomialExponent_injective] at he
  exact ⟨a, rfl, he⟩

private theorem homogeneousToLaurent_mem (s : Finset I)
    (x : HomogeneousLocalization.Away (degreeGrading A I) (chartProduct A s)) :
    HasAllowedExponents s 0 (homogeneousToLaurent s x) := by
  obtain ⟨k, f, hf, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (chartProduct_mem s) x
  rw [homogeneousToLaurent_mk]
  intro e he
  rw [AddMonoidAlgebra.coeff_mul_single_apply, mul_one, neg_neg] at he
  obtain ⟨a, ha, hc⟩ := polynomialToLaurent_coeff_nonzero f _ he
  have haSum : a.degree = k • s.card := by
    by_contra h
    exact hc ((show MvPolynomial.IsHomogeneous f _ from hf).coeff_eq_zero h)
  rw [Finsupp.degree_eq_sum] at haSum
  have hsum : (∑ i, polynomialExponent a i) = (k : ℤ) * s.card := by
    change (∑ i, (a i : ℤ)) = _
    exact_mod_cast haSum
  refine ⟨?_, fun i hi => ?_⟩
  · have h := congrArg (fun b : I → ℤ => ∑ i, b i) ha
    change (∑ i, polynomialExponent a i) = ∑ i, (e i + (k : ℤ) * chartExponent s i) at h
    rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, sum_chartExponent] at h
    omega
  · have h := congrFun ha i
    change (a i : ℤ) = e i + (k : ℤ) * chartExponent s i at h
    rw [chartExponent_apply, ite_eq_right hi, mul_zero, add_zero] at h
    rw [← h]
    exact Int.natCast_nonneg _

private theorem single_mem_homogeneousToLaurent_range (s : Finset I) (e : I → ℤ)
    (he : AllowedExponent s 0 e) (a : A) :
    AddMonoidAlgebra.single e a ∈ (homogeneousToLaurent (A := A) s).range := by
  let k := ∑ i, (-e i).toNat
  have hk (i : I) : 0 ≤ e i + (k : ℤ) * chartExponent s i := by
    by_cases hi : i ∈ s
    · rw [chartExponent_apply, ite_eq_left hi, mul_one]
      have h₁ : (-e i).toNat ≤ k :=
        Finset.single_le_sum (f := fun j => (-e j).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · simpa [chartExponent_apply, hi] using he.2 i hi
  let b : I →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (e i + (k : ℤ) * chartExponent s i).toNat
  have hb : polynomialExponent b = e + k • chartExponent s := by
    funext i
    exact Int.toNat_of_nonneg (hk i)
  have hd : b.degree = k • s.card := by
    rw [Finsupp.degree_eq_sum]
    have h := congrArg (fun x : I → ℤ => ∑ i, x i) hb
    change (∑ i, (b i : ℤ)) = ∑ i, (e i + (k : ℤ) * chartExponent s i) at h
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, he.1, sum_chartExponent, zero_add] at h
    exact_mod_cast h
  have hpoly : MvPolynomial.monomial b a ∈ degreeGrading A I (k • s.card) :=
    MvPolynomial.isHomogeneous_monomial a hd
  refine ⟨HomogeneousLocalization.Away.mk _ (chartProduct_mem s) k _ hpoly, ?_⟩
  rw [homogeneousToLaurent_mk s k _ hpoly, polynomialToLaurent_monomial,
    AddMonoidAlgebra.single_mul_single, hb, add_neg_cancel_right, mul_one]

/-- The homogeneous localization identifies the chart ring with Laurent polynomials
of degree zero, allowing denominators only at inverted coordinates. -/
def homogeneousChartRingEquiv (s : Finset I) :
    HomogeneousLocalization.Away (degreeGrading A I) (chartProduct A s) ≃+*
      laurentChartRing A s := by
  let f : HomogeneousLocalization.Away (degreeGrading A I) (chartProduct A s) →+*
      laurentChartRing A s :=
    (homogeneousToLaurent s).codRestrict (laurentChartRing A s).toSubring
      (homogeneousToLaurent_mem s)
  refine RingEquiv.ofBijective f ⟨fun x y h =>
    homogeneousToLaurent_injective s (congrArg Subtype.val h), ?_⟩
  intro x
  have hx : x.val ∈ (homogeneousToLaurent (A := A) s).range := by
    rw [← AddMonoidAlgebra.sum_coeff_single x.val, Finsupp.sum]
    exact sum_mem (fun e he => single_mem_homogeneousToLaurent_range s e
      (x.property e (Finsupp.mem_support_iff.mp he)) (x.val.coeff e))
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩


private theorem allowedExponent_zsmul_unit {s : Finset I} {i : I} (hi : i ∈ s) (d : ℤ) :
    AllowedExponent s d (d • unitExponent i) := by
  constructor
  · change ∑ j, d * unitExponent i j = d
    rw [← Finset.mul_sum, sum_unitExponent, mul_one]
  · intro j hj
    have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
    simp [unitExponent, hji]

private theorem allowedExponent_ratio {s : Finset I} {j : I} (hj : j ∈ s) (i : I) :
    AllowedExponent s 0 (unitExponent i - unitExponent j) := by
  constructor
  · simp [Finset.sum_sub_distrib, sum_unitExponent]
  · intro k hk
    have hkj : k ≠ j := fun h => hk (h.symm ▸ hj)
    simp only [Pi.sub_apply, unitExponent, Pi.single_apply, ite_eq_right hkj, sub_zero]
    split <;> omega

/-- The ratio of the (i)th and (j)th coordinates, on a chart where (j) is inverted. -/
def coordinateRatio {s : Finset I} (i j : I) (hj : j ∈ s) : laurentChartRing A s :=
  ⟨laurentMonomial (unitExponent i - unitExponent j),
    allowedExponents_single (allowedExponent_ratio hj i) 1⟩

private theorem coordinateRatio_self {s : Finset I} (j : I) (hj : j ∈ s) :
    coordinateRatio (A := A) j j hj = 1 := by
  apply Subtype.ext
  change laurentMonomial (unitExponent j - unitExponent j) = _
  rw [sub_self]
  rfl

private theorem coordinateRatio_mul {s : Finset I} (i j k : I) (hj : j ∈ s) (hk : k ∈ s) :
    coordinateRatio (A := A) i j hj * coordinateRatio j k hk = coordinateRatio i k hk := by
  apply Subtype.ext
  change laurentMonomial (unitExponent i - unitExponent j) *
    laurentMonomial (unitExponent j - unitExponent k) = laurentMonomial (unitExponent i - unitExponent k)
  rw [← laurentMonomial_add, sub_add_sub_cancel]

theorem isUnit_coordinateRatio {s : Finset I} {i j : I} (hi : i ∈ s) (hj : j ∈ s) :
    IsUnit (coordinateRatio (A := A) i j hj) :=
  isUnit_iff_exists_inv.mpr ⟨coordinateRatio j i hi,
    (coordinateRatio_mul i j i hj hi).trans (coordinateRatio_self i hi)⟩

@[simp]
theorem laurentChartRestrict_coordinateRatio {s t : Finset I} (h : s ⊆ t) (i j : I) (hj : j ∈ s) :
    laurentChartRestrict (A := A) h (coordinateRatio i j hj) = coordinateRatio i j (h hj) := rfl

/-- A basis monomial of the twist on every chart intersection containing the given index. -/
def twistGenerator {s : Finset I} {i : I} (hi : i ∈ s) (d : ℤ) :
    laurentChartModule A s d :=
  ⟨laurentMonomial (d • unitExponent i), allowedExponents_single (allowedExponent_zsmul_unit hi d) 1⟩

private theorem twistGenerator_change {s : Finset I} {i j : I} (hi : i ∈ s) (hj : j ∈ s) (k : ℕ) :
    twistGenerator (A := A) hj (-(k : ℤ)) =
      coordinateRatio (A := A) i j hj ^ k • twistGenerator hi (-(k : ℤ)) := by
  apply Subtype.ext
  change laurentMonomial (-(k : ℤ) • unitExponent j) =
    laurentMonomial (unitExponent i - unitExponent j) ^ k *
      laurentMonomial (-(k : ℤ) • unitExponent i)
  rw [← laurentMonomial_nsmul, ← laurentMonomial_add]
  congr 1
  rw [neg_smul, neg_smul, ← Nat.cast_smul_eq_nsmul ℤ, smul_sub]
  abel

/-- Trivialization of the Laurent twist on a chart containing (i), by multiplication by (X_i^d). -/
def twistTrivialization {s : Finset I} {i : I} (hi : i ∈ s) (d : ℤ) :
    laurentChartRing A s ≃ₗ[laurentChartRing A s] laurentChartModule A s d :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (laurentChartRing A s) _ (twistGenerator (A := A) hi d)) (by
    let invMonomial : LaurentPolynomial A I := laurentMonomial (-d • unitExponent i)
    have hunit : (twistGenerator (A := A) hi d).val * invMonomial = 1 := by
      change laurentMonomial (d • unitExponent i) * laurentMonomial (-d • unitExponent i) = 1
      rw [← laurentMonomial_add, neg_smul, add_neg_cancel]
      rfl
    refine ⟨?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      have h' : x.val * (twistGenerator hi d).val = y.val * (twistGenerator hi d).val :=
        congrArg Subtype.val h
      rw [← mul_one x.val, ← mul_one y.val, ← hunit, ← mul_assoc, ← mul_assoc, h']
    · intro x
      have hx : HasAllowedExponents s 0 (x.val * invMonomial) := by
        have hinv : HasAllowedExponents s (-d) invMonomial :=
          (twistGenerator hi (-d)).property
        simpa only [add_neg_cancel] using allowedExponents_mul x.property hinv
      refine ⟨⟨x.val * invMonomial, hx⟩, Subtype.ext ?_⟩
      change x.val * invMonomial * (twistGenerator hi d).val = x.val
      rw [mul_assoc, mul_comm invMonomial, hunit, mul_one])

@[simp]
theorem twistTrivialization_apply {s : Finset I} {i : I} (hi : i ∈ s) (d : ℤ)
    (r : laurentChartRing A s) :
    twistTrivialization hi d r = r • twistGenerator hi d := rfl



private theorem chartProduct_sdiff {s t : Finset I} (hst : s ⊆ t) :
    chartProduct A t = chartProduct A s * chartProduct A (t \ s) := by
  rw [mul_comm]
  exact (Finset.prod_sdiff hst).symm

private theorem chartExponent_sdiff {s t : Finset I} (hst : s ⊆ t) :
    chartExponent t = chartExponent s + chartExponent (t \ s) := by
  rw [add_comm]
  exact (Finset.sum_sdiff hst).symm

private theorem homogeneousToLaurent_awayMap {s t : Finset I} (hst : s ⊆ t)
    (x : HomogeneousLocalization.Away (degreeGrading A I) (chartProduct A s)) :
    homogeneousToLaurent t (HomogeneousLocalization.awayMap (degreeGrading A I)
      (chartProduct_mem (t \ s)) (chartProduct_sdiff hst) x) = homogeneousToLaurent s x := by
  obtain ⟨k, f, hf, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (chartProduct_mem s) x
  rw [HomogeneousLocalization.awayMap_mk]
  have ht : f * chartProduct A (t \ s) ^ k ∈ degreeGrading A I (k • t.card) := by
    rw [← Finset.card_sdiff_add_card_eq_card hst, add_comm ((t \ s).card), smul_add]
    exact SetLike.mul_mem_graded hf (SetLike.pow_mem_graded _ (chartProduct_mem _))
  have heq :
      HomogeneousLocalization.Away.mk (degreeGrading A I)
        ((chartProduct_sdiff (A := A) hst) ▸ SetLike.mul_mem_graded (chartProduct_mem s)
          (chartProduct_mem (t \ s))) k (f * chartProduct A (t \ s) ^ k)
        (by rw [smul_add]; exact SetLike.mul_mem_graded hf (SetLike.pow_mem_graded _ (chartProduct_mem _))) =
      HomogeneousLocalization.Away.mk (degreeGrading A I) (chartProduct_mem t) k _ ht := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk]
  rw [heq, homogeneousToLaurent_mk, homogeneousToLaurent_mk,
    map_mul, map_pow, polynomialToLaurent_chartProduct, ← laurentMonomial_nsmul,
    mul_assoc, ← laurentMonomial_add, chartExponent_sdiff hst, smul_add]
  congr 2
  abel

end LaurentPolynomials

section ProjectiveChartRings

open scoped BigOperators

variable (A : Type u) [CommRing A] (n : ℕ)

private abbrev projectiveScheme : Scheme.{u} := (projectiveSpace A n).left

local notation "P" => (projectiveScheme A n)
local notation "G" => homogeneousGrading A n
local notation "I" => Fin (n + 1)

/-- The standard projective open on which the coordinates in `s` are invertible. -/
abbrev standardOpen (s : Finset I) : Scheme.Opens P :=
  Proj.basicOpen G (chartProduct A s)

theorem mem_standardOpen (s : Finset I) (x : ↑(P : Scheme.{u})) :
    x ∈ standardOpen A n s ↔ ∀ i ∈ s, x ∈ coordinateOpen A n i := by
  induction s using Finset.induction_on with
  | empty => simp [standardOpen, chartProduct, Proj.basicOpen_one]
  | insert i s hi h =>
    have hprod : chartProduct A (insert i s) = MvPolynomial.X i * chartProduct A s :=
      Finset.prod_insert hi
    change x ∈ Proj.basicOpen G (chartProduct A (insert i s)) ↔ _
    rw [hprod, Proj.basicOpen_mul, TopologicalSpace.Opens.mem_inf, Finset.forall_mem_insert]
    exact and_congr_right (fun _ => h)

private theorem standardOpen_antitone : Antitone (standardOpen A n) := by
  intro s t hst x hx
  exact (mem_standardOpen A n s x).mpr (fun i hi => (mem_standardOpen A n t x).mp hx i (hst hi))

theorem standardOpen_isAffine {s : Finset I} (hs : s.Nonempty) :
    IsAffineOpen (standardOpen A n s) :=
  Proj.isAffineOpen_basicOpen G _ (chartProduct_mem s) hs.card_pos

private abbrev projectiveChartAwayIso {s : Finset I} (hs : s.Nonempty) :
    CommRingCat.of (HomogeneousLocalization.Away G (chartProduct A s)) ≅ Γ(P, standardOpen A n s) :=
  Proj.basicOpenIsoAway G _ (chartProduct_mem s) hs.card_pos

/-- The projective chart ring, in homogeneous Laurent coordinates. -/
def projectiveChartRingEquiv {s : Finset I} (hs : s.Nonempty) :
    Γ(P, standardOpen A n s) ≃+* laurentChartRing A s :=
  (projectiveChartAwayIso A n hs).symm.commRingCatIsoToRingEquiv.trans
    (homogeneousChartRingEquiv s)

theorem projectiveChartRingEquiv_restrict {s t : Finset I} (hst : s ⊆ t) (hs : s.Nonempty)
    (x : Γ(P, standardOpen A n s)) :
    projectiveChartRingEquiv A n (hs.mono hst)
      (((P : Scheme.{u}).presheaf).map (homOfLE (standardOpen_antitone A n hst)).op x) =
      laurentChartRestrict hst (projectiveChartRingEquiv A n hs x) := by
  let e := projectiveChartAwayIso A n hs
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).surjective x
  have h := Proj.awayMap_awayToSection G (chartProduct_mem (t \ s)) (chartProduct_sdiff hst)
  have h' := congrArg (fun f : CommRingCat.of (HomogeneousLocalization.Away G (chartProduct A s)) ⟶
    Γ(P, standardOpen A n t) => f y) h
  have hy : ((P : Scheme.{u}).presheaf).map (homOfLE (standardOpen_antitone A n hst)).op (e.hom y) =
      (projectiveChartAwayIso A n (hs.mono hst)).hom
        (HomogeneousLocalization.awayMap G (chartProduct_mem (t \ s)) (chartProduct_sdiff hst) y) :=
    h'.symm
  rw [hy]
  apply Subtype.ext
  change homogeneousToLaurent t ((projectiveChartAwayIso A n (hs.mono hst)).inv
      ((projectiveChartAwayIso A n (hs.mono hst)).hom _)) =
    homogeneousToLaurent s (e.inv (e.hom y))
  simp only [Iso.hom_inv_id_apply, homogeneousToLaurent_awayMap hst]


end ProjectiveChartRings


section CechComparisons

open scoped BigOperators Simplicial
open CategoryTheory.Preadditive

open private differential orderedCochains coface mapTerm tupleOpen_le from
  Specs.LinearAlgebraicGroups.Representation.FlagCohomology

section CechCoordinates

variable {A : Type u} [CommRing A] {D : Type v} [CompleteLattice D]
  {I : Type u} [Preorder I] (U : I → D) (P : Dᵒᵖ ⥤ ModuleCat.{u} A)

/-- The Čech differential on an ordered tuple is the alternating sum of the
restrictions from its ordered faces. -/
theorem cechDifferential_apply (k : ℕ) (x : (cechComplex U P).X k) (e : Fin (k + 2) ↪o I) :
    (cechComplex U P).d k (k + 1) x e =
      ∑ j : Fin (k + 2), (-1 : ℤ) ^ (j : ℕ) •
        P.map (homOfLE (tupleOpen_le U e j.succAboveOrderEmb)).op
          (x (j.succAboveOrderEmb.trans e)) := by
  let T (q : ℕ) := (orderedCochains U P).obj ⦋q⦌ₛ
  let eval : (T k ⟶ T (k + 1)) →+ P.obj (op (tupleOpen U e)) :=
    { toFun := fun f => f x e
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let term (j : Fin (k + 2)) : T k ⟶ T (k + 1) :=
    (-1 : ℤ) ^ (j : ℕ) • (orderedCochains U P).map (coface j)
  have hd : (cechComplex U P).d k (k + 1) = ∑ j, term j := by
    simp only [cechComplex, CochainComplex.of_d, differential, term]
  change eval ((cechComplex U P).d k (k + 1)) = _
  rw [hd, map_sum eval]
  apply Finset.sum_congr rfl
  intro j _
  let m : T k ⟶ T (k + 1) := (orderedCochains U P).map (coface j)
  calc
    eval (term j) = (-1 : ℤ) ^ (j : ℕ) • eval m := map_zsmul eval _ m
    _ = _ := rfl

/-- An isomorphism of coefficient presheaves induces an isomorphism of Čech complexes. -/
def cechIsoOfNatIso {Q : Dᵒᵖ ⥤ ModuleCat.{u} A} (e : P ≅ Q) :
    cechComplex U P ≅ cechComplex U Q where
  hom := cechMap U e.hom
  inv := cechMap U e.inv
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    exact Iso.hom_inv_id_apply (e.app (op (tupleOpen U t))) (x t)
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    exact Iso.inv_hom_id_apply (e.app (op (tupleOpen U t))) (x t)

variable {D' : Type w} [CompleteLattice D']

/-- Reindexing the presheaf along a map that sends the ordered intersections to
the corresponding ordered intersections preserves the Čech complex. -/
def cechReindexIso (U' : I → D') (f : D'ᵒᵖ ⥤ Dᵒᵖ)
    (h : ∀ (k : ℕ) (e : Fin (k + 1) ↪o I), f.obj (op (tupleOpen U' e)) = op (tupleOpen U e)) :
    cechComplex U' (f ⋙ P) ≅ cechComplex U P := by
  let E (k : ℕ) (e : Fin (k + 1) ↪o I) := P.mapIso (eqToIso (h k e))
  let equiv (k : ℕ) :
      (cechComplex U' (f ⋙ P)).X k ≃ₗ[A] (cechComplex U P).X k :=
    LinearEquiv.piCongrRight fun e => (E k e).toLinearEquiv
  refine HomologicalComplex.Hom.isoOfComponents (fun k => (equiv k).toModuleIso) ?_
  intro k l hkl
  change k + 1 = l at hkl
  subst l
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext e
  change (cechComplex U P).d k (k + 1) (equiv k x) e =
    (E (k + 1) e).hom (((cechComplex U' (f ⋙ P)).d k (k + 1) x) e)
  rw [cechDifferential_apply, cechDifferential_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  congr 1
  let e' := j.succAboveOrderEmb.trans e
  let m := (homOfLE (tupleOpen_le U e j.succAboveOrderEmb)).op
  let m' := (homOfLE (tupleOpen_le U' e j.succAboveOrderEmb)).op
  change P.map m (P.map (eqToHom (h k e')) (x e')) =
    P.map (eqToHom (h (k + 1) e)) (P.map (f.map m') (x e'))
  simp only [← ModuleCat.comp_apply, ← Functor.map_comp]
  congr 2

end CechCoordinates

end CechComparisons


section ChartModuleDiagrams

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [CommRing A] {I : Type} [Fintype I] [DecidableEq I]

/-- Modules on the intersections of coordinate charts, with the indicated
semilinear restrictions. -/
structure ChartModules (A : Type u) [CommRing A] (I : Type) [Fintype I] [DecidableEq I] where
  obj : (s : Finset I) → ModuleCat.{u} (laurentChartRing A s)
  res {s t : Finset I} (h : s ⊆ t) : obj s →ₛₗ[(laurentChartRestrict (A := A) h).toRingHom] obj t
  res_id (s : Finset I) (x : obj s) : res (fun _ h => h : s ⊆ s) x = x
  res_comp {s t w : Finset I} (h : s ⊆ t) (h' : t ⊆ w) (x : obj s) :
    res h' (res h x) = res (h.trans h') x

namespace ChartModules

attribute [simp] res_id res_comp

variable (M : ChartModules A I)

instance (s : Finset I) : Module A (M.obj s) :=
  Module.compHom _ (algebraMap A (laurentChartRing A s))

instance (s : Finset I) : IsScalarTower A (laurentChartRing A s) (M.obj s) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

@[simp]
theorem res_smul {s t : Finset I} (h : s ⊆ t) (r : laurentChartRing A s) (x : M.obj s) :
    M.res h (r • x) = laurentChartRestrict h r • M.res h x :=
  (M.res h).map_smulₛₗ r x

@[simp]
theorem res_ratio_pow_smul {s t : Finset I} (h : s ⊆ t) (i j : I) (hj : j ∈ s)
    (k : ℕ) (x : M.obj s) :
    M.res h (coordinateRatio (A := A) i j hj ^ k • x) =
      coordinateRatio (A := A) i j (h hj) ^ k • M.res h x := by
  rw [res_smul, map_pow, laurentChartRestrict_coordinateRatio]

/-- A map of chart modules preserves scalar multiplication and commutes with restrictions. -/
structure Map (M N : ChartModules A I) where
  app (s : Finset I) : M.obj s →ₗ[laurentChartRing A s] N.obj s
  naturality {s t : Finset I} (h : s ⊆ t) (x : M.obj s) :
    app t (M.res h x) = N.res h (app s x)

variable {M N : ChartModules A I}

/-- The pointwise kernel of a map of chart modules. -/
def Map.ker (f : Map M N) : ChartModules A I where
  obj s := ModuleCat.of _ (LinearMap.ker (f.app s))
  res h :=
    { toFun := fun x => ⟨M.res h x.val, by
        change f.app _ (M.res h x.val) = 0
        rw [f.naturality, LinearMap.mem_ker.mp x.property, map_zero]⟩
      map_add' := fun x y => Subtype.ext ((M.res h).map_add x.val y.val)
      map_smul' := fun a x => Subtype.ext (M.res_smul h a x.val) }
  res_id s x := Subtype.ext (M.res_id s x.val)
  res_comp h h' x := Subtype.ext (M.res_comp h h' x.val)

/-- The usual kernel inclusion. -/
def Map.kerι (f : Map M N) : Map f.ker M where
  app s := (LinearMap.ker (f.app s)).subtype
  naturality _ _ := rfl

/-- The two denominator-clearing properties of a localization map. In the target
of each restriction the scalar in question is already a unit. -/
structure IsLocalizing (M : ChartModules A I) : Prop where
  numerator {s : Finset I} (i j : I) (hj : j ∈ s) (x : M.obj (insert i s)) :
    ∃ k : ℕ, ∃ y : M.obj s,
      M.res (Finset.subset_insert i s) y =
        coordinateRatio (A := A) i j (show j ∈ insert i s from Finset.mem_insert_of_mem hj) ^ k • x
  annihilator {s : Finset I} (i j : I) (hj : j ∈ s) (y : M.obj s)
      (h : M.res (Finset.subset_insert i s) y = 0) :
    ∃ k : ℕ, coordinateRatio (A := A) i j hj ^ k • y = 0

theorem Map.ker_isLocalizing (f : Map M N) (hM : M.IsLocalizing) (hN : N.IsLocalizing) :
    f.ker.IsLocalizing where
  numerator := by
    intro s i j hj x
    obtain ⟨a, y, hy⟩ := hM.numerator i j hj x.val
    have hfy : N.res (Finset.subset_insert i s) (f.app s y) = 0 := by
      rw [← f.naturality, hy, map_smul, LinearMap.mem_ker.mp x.property, smul_zero]
    obtain ⟨b, hb⟩ := hN.annihilator i j hj (f.app s y) hfy
    refine ⟨b + a, ⟨coordinateRatio (A := A) i j hj ^ b • y, ?_⟩, ?_⟩
    · exact LinearMap.mem_ker.mpr (by rw [map_smul, hb])
    · apply Subtype.ext
      change M.res (Finset.subset_insert i s) (coordinateRatio (A := A) i j hj ^ b • y) =
        coordinateRatio (A := A) i j (show j ∈ insert i s from Finset.mem_insert_of_mem hj) ^ (b + a) • x.val
      rw [res_ratio_pow_smul, hy, smul_smul, pow_add]
  annihilator := by
    intro s i j hj y hy
    have hz := congrArg Subtype.val hy
    obtain ⟨k, hk⟩ := hM.annihilator i j hj y.val hz
    exact ⟨k, Subtype.ext hk⟩

/-- A map between localizing diagrams which is surjective on coordinate charts
is surjective on each nonempty intersection. -/
theorem Map.surjective_of_singletons (f : Map M N) (hN : N.IsLocalizing)
    (h : ∀ i : I, Function.Surjective (f.app {i})) :
    ∀ s : Finset I, s.Nonempty → Function.Surjective (f.app s) := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    intro _
    rcases s.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
    · exact h i
    · intro x
      obtain ⟨k, y, hy⟩ := hN.numerator i j hj x
      obtain ⟨z, hz⟩ := ih ⟨j, hj⟩ y
      have hu := (isUnit_coordinateRatio (A := A) (Finset.mem_insert_self i s)
        (show j ∈ insert i s from Finset.mem_insert_of_mem hj)).pow k
      obtain ⟨a, ha⟩ := hu.exists_left_inv
      refine ⟨a • M.res (Finset.subset_insert i s) z, ?_⟩
      rw [map_smul, f.naturality, hz, hy, smul_smul, ha, one_smul]

/-- The diagram of the Laurent twists with the same exponents on restriction. -/
def twist (d : ℤ) : ChartModules A I where
  obj s := ModuleCat.of _ (laurentChartModule A s d)
  res h :=
    { toFun := fun x => ⟨x.val, laurentChartAllowed_mono h x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  res_id _ _ := rfl
  res_comp _ _ _ := rfl

@[simp]
theorem twist_res_generator {s t : Finset I} (h : s ⊆ t) {i : I} (hi : i ∈ s) (d : ℤ) :
    (twist (A := A) d).res h (twistGenerator hi d) = twistGenerator (h hi) d := rfl

private theorem twist_obj_eq_zero_empty (d : ℤ) (hd : d < 0) (x : (twist (A := A) (I := I) d).obj ∅) :
    x = 0 := by
  apply Subtype.ext
  apply AddMonoidAlgebra.ext
  ext e
  by_contra he
  have h := x.property e he
  have hsum : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => h.2 i (Finset.notMem_empty i)
  exact (not_le_of_gt hd) (h.1 ▸ hsum)


section Extension


private abbrev singletonInPair (j l : I) : ({j} : Finset I) ⊆ insert l {j} :=
  Finset.subset_insert l _

private abbrev otherSingletonInPair (j l : I) : ({l} : Finset I) ⊆ insert l {j} :=
  Finset.singleton_subset_iff.mpr (Finset.mem_insert_self l _)

set_option maxHeartbeats 800000 in
private theorem one_generator_extends (M : ChartModules A I) (hM : M.IsLocalizing)
    (i : I) (x : M.obj {i}) :
    ∃ k : ℕ, 0 < k ∧ ∃ y : ∀ j : I, M.obj {j}, y i = x ∧
      ∀ (j l : I), M.res (singletonInPair j l) (y j) =
        coordinateRatio (A := A) l j (singletonInPair j l (Finset.mem_singleton_self j)) ^ k •
          M.res (otherSingletonInPair j l) (y l) := by
  have localLift (j : I) := hM.numerator i j (Finset.mem_singleton_self j)
    (M.res (otherSingletonInPair j i) x)
  choose a z hz using localLift
  let n := ∑ j, a j
  have ha (j : I) : a j ≤ n :=
    Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let y (j : I) : M.obj {j} :=
    coordinateRatio (A := A) i j (Finset.mem_singleton_self j) ^ (n - a j) • z j
  have hy (j : I) : M.res (singletonInPair j i) (y j) =
      coordinateRatio (A := A) i j (singletonInPair j i (Finset.mem_singleton_self j)) ^ n •
        M.res (otherSingletonInPair j i) x := by
    dsimp only [y]
    rw [res_ratio_pow_smul, hz j, smul_smul, ← pow_add, Nat.sub_add_cancel (ha j)]
  have hyi : y i = x := by
    apply sub_eq_zero.mp
    have hz' : M.res (singletonInPair i i) (y i - x) = 0 := by
      have hh := hy i
      rw [coordinateRatio_self, one_pow, one_smul] at hh
      rw [map_sub, hh, sub_self]
    obtain ⟨b, hb⟩ := hM.annihilator i i (Finset.mem_singleton_self i) (y i - x) hz'
    simpa only [coordinateRatio_self, one_pow, one_smul] using hb
  let diff (j l : I) : M.obj (insert l {j}) :=
    M.res (singletonInPair j l) (y j) -
      coordinateRatio (A := A) l j (singletonInPair j l (Finset.mem_singleton_self j)) ^ n •
        M.res (otherSingletonInPair j l) (y l)
  have diff_zero (j l : I) :
      M.res (Finset.subset_insert i (insert l {j})) (diff j l) = 0 := by
    let s := insert l ({j} : Finset I)
    let w := insert i s
    have hj : j ∈ w := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hl : l ∈ w := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hi : ({i} : Finset I) ⊆ w := Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    have hsubj : insert i {j} ⊆ w := Finset.insert_subset_insert i (singletonInPair j l)
    have hsubl : insert i {l} ⊆ w := Finset.insert_subset_insert i (otherSingletonInPair j l)
    have hjEq : M.res (Finset.singleton_subset_iff.mpr hj) (y j) =
        coordinateRatio (A := A) i j hj ^ n • M.res hi x := by
      rw [← M.res_comp (singletonInPair j i) hsubj, hy, res_ratio_pow_smul, M.res_comp]
    have hlEq : M.res (Finset.singleton_subset_iff.mpr hl) (y l) =
        coordinateRatio (A := A) i l hl ^ n • M.res hi x := by
      rw [← M.res_comp (singletonInPair l i) hsubl, hy, res_ratio_pow_smul, M.res_comp]
    change M.res (Finset.subset_insert i s)
      (M.res (singletonInPair j l) (y j) -
        coordinateRatio (A := A) l j (singletonInPair j l (Finset.mem_singleton_self j)) ^ n •
          M.res (otherSingletonInPair j l) (y l)) = 0
    rw [map_sub, M.res_ratio_pow_smul (Finset.subset_insert i s) l j
      (singletonInPair j l (Finset.mem_singleton_self j)) n, res_comp, res_comp, hjEq, hlEq,
      smul_smul, ← mul_pow, mul_comm (coordinateRatio (A := A) l j hj), coordinateRatio_mul, sub_self]
  have annihilator (j l : I) :=
    hM.annihilator i j (singletonInPair j l (Finset.mem_singleton_self j)) (diff j l) (diff_zero j l)
  choose b hb using annihilator
  let N := (∑ jl : I × I, b jl.1 jl.2) + 1
  have hbN (j l : I) : b j l ≤ N :=
    (Finset.single_le_sum (f := fun jl : I × I => b jl.1 jl.2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (j, l))).trans (Nat.le_succ _)
  let Y (j : I) : M.obj {j} := coordinateRatio (A := A) i j (Finset.mem_singleton_self j) ^ N • y j
  refine ⟨n + N, by dsimp [N]; omega, Y, ?_, ?_⟩
  · dsimp only [Y]
    rw [coordinateRatio_self, one_pow, one_smul, hyi]
  · intro j l
    let s := insert l ({j} : Finset I)
    have hj : j ∈ s := singletonInPair j l (Finset.mem_singleton_self j)
    have hl : l ∈ s := otherSingletonInPair j l (Finset.mem_singleton_self l)
    let r (a b : I) (h : b ∈ s) : laurentChartRing A s := coordinateRatio (A := A) a b h
    have hpow : r i j hj ^ N • diff j l = 0 := by
      rw [← Nat.sub_add_cancel (hbN j l), pow_add, mul_smul, hb j l, smul_zero]
    dsimp only [diff] at hpow
    rw [smul_sub, sub_eq_zero, smul_smul] at hpow
    simp only [Y, res_ratio_pow_smul, smul_smul]
    change r i j hj ^ N • M.res (singletonInPair j l) (y j) =
      (r l j hj ^ (n + N) * r i l hl ^ N) • M.res (otherSingletonInPair j l) (y l)
    have hcoeff : r i j hj ^ N * r l j hj ^ n = r l j hj ^ (n + N) * r i l hl ^ N := by
      have hmul : r i l hl * r l j hj = r i j hj := coordinateRatio_mul i l j hl hj
      rw [← hmul, mul_pow, pow_add (r l j hj) n N]
      generalize r i l hl ^ N = R
      generalize r l j hj ^ N = S
      generalize r l j hj ^ n = T
      exact ((mul_right_comm R S T).trans (congrArg (· * S) (mul_comm R T))).trans
        (mul_right_comm T R S)
    exact hpow.trans (congrArg (· • M.res (otherSingletonInPair j l) (y l)) hcoeff)

/-- A section on a coordinate chart extends to a morphism from a sufficiently
negative twist. On that chart its basis monomial maps to the original section. -/
theorem exists_map_from_twist (M : ChartModules A I) (hM : M.IsLocalizing)
    (i : I) (x : M.obj {i}) :
    ∃ k : ℕ, ∃ f : Map (twist (A := A) (I := I) (-(k : ℤ))) M,
      f.app {i} (twistGenerator (Finset.mem_singleton_self i) (-(k : ℤ))) = x := by
  classical
  obtain ⟨k, hk, y, hy, hyCompat⟩ := one_generator_extends M hM i x
  let d : ℤ := -(k : ℤ)
  let loc {s : Finset I} (a : I) (ha : a ∈ s) : M.obj s :=
    M.res (Finset.singleton_subset_iff.mpr ha) (y a)
  let φ (s : Finset I) : (twist (A := A) (I := I) d).obj s →ₗ[laurentChartRing A s] M.obj s :=
    if hs : s.Nonempty then
      (LinearMap.toSpanSingleton _ _ (loc hs.choose hs.choose_spec)).comp
        (twistTrivialization hs.choose_spec d).symm.toLinearMap
    else 0
  have hgen (s : Finset I) (a : I) (ha : a ∈ s) :
      φ s (twistGenerator ha d) = loc a ha := by
    have hs : s.Nonempty := ⟨a, ha⟩
    let b := hs.choose
    have hb : b ∈ s := hs.choose_spec
    have hab : insert b {a} ⊆ s :=
      Finset.insert_subset_iff.mpr ⟨hb, Finset.singleton_subset_iff.mpr ha⟩
    have hloc : loc a ha = coordinateRatio (A := A) b a ha ^ k • loc b hb := by
      have hh := congrArg (M.res hab) (hyCompat a b)
      simpa only [res_comp, res_ratio_pow_smul, loc] using hh
    simp only [φ, dite_eq_left hs]
    have heq : twistGenerator (A := A) ha d =
        coordinateRatio (A := A) b a ha ^ k • twistGenerator hb d :=
      twistGenerator_change hb ha k
    rw [heq, map_smul, hloc]
    congr 1
    change (LinearMap.toSpanSingleton _ _ (loc b hb))
      ((twistTrivialization hb d).symm (twistGenerator hb d)) = loc b hb
    have he : twistTrivialization hb d 1 = twistGenerator (A := A) hb d := by
      simp only [twistTrivialization_apply, one_smul]
    rw [← he, LinearEquiv.symm_apply_apply]
    exact one_smul _ _
  let f : Map (twist (A := A) (I := I) d) M :=
    { app := φ
      naturality := by
        intro s t h z
        rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
        · rw [twist_obj_eq_zero_empty d (by dsimp [d]; exact neg_neg_of_pos (Int.natCast_pos.mpr hk)) z,
            map_zero, map_zero, map_zero, map_zero]
        · obtain ⟨r, rfl⟩ := (twistTrivialization (A := A) ha d).surjective z
          rw [twistTrivialization_apply, res_smul, twist_res_generator, map_smul, map_smul,
            res_smul, hgen, hgen]
          dsimp only [loc]
          rw [res_comp] }
  refine ⟨k, f, ?_⟩
  change φ {i} (twistGenerator (Finset.mem_singleton_self i) d) = x
  rw [hgen]
  dsimp only [loc]
  rw [res_id, hy]

end Extension


end ChartModules

end ChartModuleDiagrams


section TwistPresentations

namespace ChartModules

open scoped BigOperators

variable {A : Type u} [CommRing A] {I : Type} [Fintype I] [DecidableEq I]

set_option backward.isDefEq.respectTransparency false

/-- The Laurent twist restrictions are localizations by the coordinate ratio. -/
theorem twist_isLocalizing (d : ℤ) : (twist (A := A) (I := I) d).IsLocalizing where
  numerator := by
    classical
    intro s i j hj x
    let t := insert i s
    let r := coordinateRatio (A := A) i j (show j ∈ t from Finset.mem_insert_of_mem hj)
    let k := ∑ e ∈ x.val.coeff.support, (-e i).toNat
    let y := r ^ k • x
    have hy : y.val = x.val * laurentMonomial (k • (unitExponent i - unitExponent j)) := by
      change (laurentMonomial (unitExponent i - unitExponent j)) ^ k * x.val = _
      rw [laurentMonomial_nsmul, mul_comm]
    have hys : HasAllowedExponents s d y.val := by
      intro e he
      have h := y.property e he
      refine ⟨h.1, fun a ha => ?_⟩
      by_cases hai : a = i
      · subst a
        have hij : i ≠ j := fun h => ha (h.symm ▸ hj)
        rw [hy, AddMonoidAlgebra.coeff_mul_single_apply, mul_one] at he
        have hb : (-(e + -(k • (unitExponent i - unitExponent j))) i).toNat ≤ k :=
          Finset.single_le_sum (f := fun b : I → ℤ => (-b i).toNat) (fun _ _ => Nat.zero_le _)
            (Finsupp.mem_support_iff.mpr he)
        change (-(e i + -(↑k * (unitExponent i i - unitExponent j i)))).toNat ≤ k at hb
        simp only [unitExponent, Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero, mul_one] at hb
        omega
      · exact h.2 a (fun hm => (Finset.mem_insert.mp hm).elim hai ha)
    exact ⟨k, ⟨y.val, hys⟩, rfl⟩
  annihilator := by
    intro s i j hj y h
    apply_fun (fun x : (twist (A := A) (I := I) d).obj (insert i s) => x.val) at h
    have hy : y = 0 := Subtype.ext h
    exact ⟨0, by rw [hy, smul_zero]⟩

variable {J : Type u}

/-- Products of the chart modules and their coordinatewise restrictions. -/
def pi (M : J → ChartModules A I) : ChartModules A I where
  obj s := ModuleCat.of _ (∀ j, (M j).obj s)
  res h :=
    { toFun := fun x j => (M j).res h (x j)
      map_add' := fun x y => funext fun j => map_add ((M j).res h) (x j) (y j)
      map_smul' := fun a x => funext fun j => (M j).res_smul h a (x j) }
  res_id s x := funext fun j => (M j).res_id s (x j)
  res_comp h h' x := funext fun j => (M j).res_comp h h' (x j)

theorem pi_isLocalizing [Fintype J] (M : J → ChartModules A I)
    (hM : ∀ j, (M j).IsLocalizing) : (pi M).IsLocalizing where
  numerator := by
    intro s i j hj x
    let N (a : J) := (hM a).numerator i j hj (x a)
    choose k y hy using N
    let k₀ := ∑ a, k a
    have hle (a : J) : k a ≤ k₀ :=
      Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    refine ⟨k₀, fun a => coordinateRatio (A := A) i j hj ^ (k₀ - k a) • y a, ?_⟩
    funext a
    let r := coordinateRatio (A := A) i j (show j ∈ insert i s from Finset.mem_insert_of_mem hj)
    change (M a).res (Finset.subset_insert i s)
        (coordinateRatio (A := A) i j hj ^ (k₀ - k a) • y a) = r ^ k₀ • x a
    rw [res_ratio_pow_smul, hy, smul_smul, ← pow_add, Nat.sub_add_cancel (hle a)]
  annihilator := by
    intro s i j hj x hx
    have hx' (a : J) : (M a).res (Finset.subset_insert i s) (x a) = 0 := congrFun hx a
    choose k hk using fun a => (hM a).annihilator i j hj (x a) (hx' a)
    let k₀ := ∑ a, k a
    have hle (a : J) : k a ≤ k₀ :=
      Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    refine ⟨k₀, ?_⟩
    funext a
    change coordinateRatio (A := A) i j hj ^ k₀ • x a = 0
    rw [← Nat.sub_add_cancel (hle a), pow_add, mul_smul, hk, smul_zero]

variable {M : ChartModules A I}

/-- Sum of a finite family of maps, as a map from a product. -/
def Map.sum [Fintype J] {N : J → ChartModules A I} (f : ∀ j, Map (N j) M) :
    Map (pi N) M where
  app s := ∑ j, (f j).app s ∘ₗ LinearMap.proj j
  naturality h x := by
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (f j).naturality h (x j)

@[simp]
theorem Map.sum_apply [Fintype J] {N : J → ChartModules A I} (f : ∀ j, Map (N j) M)
    (s : Finset I) (x : (pi N).obj s) :
    (Map.sum f).app s x = ∑ j, (f j).app s (x j) := by
  simp only [Map.sum, LinearMap.sum_apply, LinearMap.comp_apply]
  rfl

/-- Finite generators on the coordinate charts give a surjection from a finite
sum of twists on every nonempty chart intersection. -/
theorem exists_finite_twist_presentation (M : ChartModules A I)
    (hM : M.IsLocalizing) (hfin : ∀ i : I, Module.Finite (laurentChartRing A {i}) (M.obj {i})) :
    ∃ (J : Type u) (_ : Fintype J) (d : J → ℤ) (f : Map (pi fun j => twist (d j)) M),
      ∀ s : Finset I, s.Nonempty → Function.Surjective (f.app s) := by
  classical
  have hgens (i : I) : ∃ k : ℕ, ∃ x : Fin k → M.obj {i},
      Submodule.span (laurentChartRing A {i}) (Set.range x) = ⊤ := by
    let _ := hfin i
    exact Module.Finite.exists_fin (R := laurentChartRing A {i}) (M := M.obj {i})
  choose k x hx using hgens
  let J := ULift.{u} (Σ i : I, Fin (k i))
  have hext (j : J) := exists_map_from_twist M hM j.down.1 (x j.down.1 j.down.2)
  choose a f hf using hext
  let d : J → ℤ := fun j => -(a j : ℤ)
  let p : Map (pi fun j => twist (d j)) M := Map.sum f
  refine ⟨J, inferInstance, d, p, p.surjective_of_singletons hM ?_⟩
  intro i
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← hx i, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  let j : J := ⟨⟨i, l⟩⟩
  let b := twistGenerator (A := A) (Finset.mem_singleton_self i) (d j)
  refine ⟨Pi.single j b, ?_⟩
  change (Map.sum f).app {i} (Pi.single j b) = _
  rw [Map.sum_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · rw [Pi.single_eq_same]
    exact hf j
  · intro a _ ha
    rw [Pi.single_eq_of_ne ha, map_zero]

end ChartModules

end TwistPresentations


section AffineDenominators

open Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000 in
/-- Clearing denominators for sections of a quasi-coherent sheaf on an affine
open and the smaller basic open. The scalar map is the actual restriction. -/
theorem affineModule_denominators {X : Scheme.{u}} (F : X.Modules)
    (hF : (F : SheafOfModules X.ringCatSheaf).IsQuasicoherent)
    {U V : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) (h : V = X.basicOpen r) (hVU : V ≤ U) :
    (∀ x : Γ(F, V), ∃ (k : ℕ) (y : Γ(F, U)),
      F.presheaf.map (homOfLE hVU).op y =
        (X.presheaf.map (homOfLE hVU).op r) ^ k • x) ∧
    (∀ y : Γ(F, U), F.presheaf.map (homOfLE hVU).op y = 0 → ∃ k : ℕ, r ^ k • y = 0) := by
  let _ := hF
  let R := Γ(X, U)
  let f := hU.fromSpec
  have : IsOpenImmersion f := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  let M := F.restrict f
  have : M.IsQuasicoherent := inferInstanceAs (((restrictFunctor f).obj F).IsQuasicoherent)
  let W : (Spec R).Opens := PrimeSpectrum.basicOpen r
  have hu : f ''ᵁ (⊤ : (Spec R).Opens) = U :=
    f.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have hv : f ''ᵁ W = V := by
    change f ''ᵁ PrimeSpectrum.basicOpen r = V
    rw [← hU.fromSpec_preimage_basicOpen, f.image_preimage_eq_opensRange_inf,
      hU.opensRange_fromSpec, inf_eq_right.mpr (X.basicOpen_le r), h]
  let e (W' : (Spec R).Opens) (Z : X.Opens) (he : f ''ᵁ W' = Z) :
      Γ(M,W') ≅ Γ(F,Z) :=
    F.restrictAppIso f W' ≪≫ F.presheaf.mapIso (eqToIso he.symm).op
  have eNaturality :
      M.presheaf.map W.leTop.op ≫ (e W V hv).hom =
        (e ⊤ U hu).hom ≫ F.presheaf.map (homOfLE hVU).op := by
    simp only [M, e, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc,
      map_restrictAppIso_hom_assoc, ← Functor.map_comp]
    congr 2
  have eScalar (W' : (Spec R).Opens) (Z : X.Opens) (he : f ''ᵁ W' = Z)
      (hZU : Z ≤ U) (a : R) (x : Γ(M,W')) :
      (e W' Z he).hom (a • x) = (X.presheaf.map (homOfLE hZU).op a) • (e W' Z he).hom x := by
    let wLe : W' ≤ f ⁻¹ᵁ U := le_top.trans_eq hU.fromSpec_preimage_self.symm
    have happ : f.appLE U W' wLe =
        (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map W'.leTop.op := by
      rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      rfl
    have hrw : (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map W'.leTop.op ≫
          (f.appIso W').inv ≫ X.presheaf.map (eqToHom he.symm).op =
        X.presheaf.map (homOfLE hZU).op := by
      rw [← Category.assoc (Scheme.ΓSpecIso R).inv, ← happ, Scheme.Hom.appLE_appIso_inv_assoc,
        ← Functor.map_comp]
      rfl
    change (F.presheaf.map (eqToHom he.symm).op)
      ((F.restrictAppIso f W').hom (a • x)) = _
    rw [smul_Spec_def]
    let b : Γ(Spec R,W') := (Spec R).presheaf.map W'.leTop.op ((Scheme.ΓSpecIso R).inv a)
    have hs := F.smul_restrictAppIso_hom_apply f W' b x
    change (F.presheaf.map (eqToHom he.symm).op) ((F.restrictAppIso f W').hom (b • x)) = _
    refine (congrArg (fun v : Γ(F, f ''ᵁ W') => F.presheaf.map (eqToHom he.symm).op v) hs).trans ?_
    have hh := F.val.map_smul (eqToHom he.symm).op
      ((f.appIso W').inv ((Spec R).presheaf.map W'.leTop.op ((Scheme.ΓSpecIso R).inv a)))
      ((F.restrictAppIso f W').hom x)
    refine hh.trans ?_
    exact congrArg (fun b : Γ(X,Z) => b • (e W' Z he).hom x)
      (congrArg (fun l : Γ(X,U) ⟶ Γ(X,Z) => l a) hrw)
  have eScalarTop (a : R) (x : Γ(M,⊤)) : (e ⊤ U hu).hom (a • x) = a • (e ⊤ U hu).hom x := by
    have h := eScalar ⊤ U hu le_rfl a x
    have hId : X.presheaf.map (homOfLE (le_refl U)).op = 𝟙 _ :=
      X.presheaf.map_id (op U)
    rw [hId] at h
    exact h
  let l : (moduleSpecΓFunctor.obj M) →ₗ[R] Γ(M, W) :=
    ((modulesSpecToSheaf.obj M).obj.map W.leTop.op).hom
  have hloc : IsLocalizedModule.Away r l :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance r
  have comm (x : Γ(M,⊤)) :
      (e W V hv).hom (l x) = F.presheaf.map (homOfLE hVU).op ((e ⊤ U hu).hom x) :=
    congrArg (fun φ : Γ(M,⊤) ⟶ Γ(F,V) => φ x) eNaturality
  constructor
  · intro x
    obtain ⟨k, z, hz⟩ := IsLocalizedModule.Away.surj l r ((e W V hv).inv x)
    refine ⟨k, (e ⊤ U hu).hom z, ?_⟩
    have hz' := congrArg (fun y : Γ(M,W) => (e W V hv).hom y) hz
    rw [eScalar W V hv hVU, Iso.inv_hom_id_apply, map_pow, comm] at hz'
    exact hz'.symm
  · intro y hy
    have hy' : l ((e ⊤ U hu).inv y) = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (e W V hv).hom).injective
      rw [comm, Iso.inv_hom_id_apply, hy, map_zero]
    obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (r := r) (f := l)
      (hy'.trans (map_zero l).symm)
    refine ⟨k, ?_⟩
    have hk' := congrArg (fun x : Γ(M,⊤) => (e ⊤ U hu).hom x) hk
    simpa only [smul_zero, map_zero, eScalarTop, Iso.inv_hom_id_apply] using hk'

end AffineDenominators


section ChartGeometry

open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false


section ProjectiveScalars

variable (A : Type u) [CommRing A] (n : ℕ)

local notation "P" => (projectiveScheme A n)
local notation "G" => homogeneousGrading A n
local notation "I" => Fin (n + 1)

/-- The map from homogeneous Laurent polynomials of degree zero to chart sections. -/
def projectiveChartScalar (s : Finset I) :
    laurentChartRing A s →+* Γ(P, standardOpen A n s) :=
  (Proj.awayToSection G (chartProduct A s)).hom.comp
    (homogeneousChartRingEquiv (A := A) s).symm.toRingHom

theorem projectiveChartScalar_natural {s t : Finset I} (h : s ⊆ t)
    (r : laurentChartRing A s) :
    ((P : Scheme.{u}).presheaf.map (homOfLE (standardOpen_antitone A n h)).op)
      (projectiveChartScalar A n s r) =
      projectiveChartScalar A n t (laurentChartRestrict h r) := by
  let g := homogeneousChartRingEquiv (A := A) s
  let g' := homogeneousChartRingEquiv (A := A) t
  obtain ⟨x, rfl⟩ := g.surjective r
  let a := HomogeneousLocalization.awayMap G (chartProduct_mem (t \ s)) (chartProduct_sdiff h)
  have h₁ : g' (a x) = laurentChartRestrict h (g x) :=
    Subtype.ext (homogeneousToLaurent_awayMap h x)
  change ((P : Scheme.{u}).presheaf.map (homOfLE (standardOpen_antitone A n h)).op)
      (Proj.awayToSection G (chartProduct A s) (g.symm (g x))) =
    Proj.awayToSection G (chartProduct A t) (g'.symm (laurentChartRestrict h (g x)))
  rw [g.symm_apply_apply, ← h₁, g'.symm_apply_apply]
  exact (congrArg (fun f : CommRingCat.of (HomogeneousLocalization.Away G (chartProduct A s)) ⟶
    Γ(P, standardOpen A n t) => f x)
    (Proj.awayMap_awayToSection G (chartProduct_mem (t \ s)) (chartProduct_sdiff h))).symm

private def coordinateRatioFraction {s : Finset I} (i j : I) (hj : j ∈ s) :
    HomogeneousLocalization.Away G (chartProduct A s) :=
  HomogeneousLocalization.Away.mk G (chartProduct_mem s) 1
    (MvPolynomial.X i * chartProduct A (s.erase j)) (by
      simpa only [one_nsmul, Nat.add_comm 1 (s.erase j).card, Finset.card_erase_add_one hj] using
        SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X A i) (chartProduct_mem (A := A) (s.erase j)))

private theorem coordinateRatioFraction_eq {s : Finset I} (i j : I) (hj : j ∈ s) :
    homogeneousChartRingEquiv (A := A) s (coordinateRatioFraction A n i j hj) =
      coordinateRatio (A := A) i j hj := by
  apply Subtype.ext
  change homogeneousToLaurent s (coordinateRatioFraction A n i j hj) =
    laurentMonomial (unitExponent i - unitExponent j)
  have hexp : chartExponent s = unitExponent j + chartExponent (s.erase j) := by
    have h := Finset.sum_erase_add s unitExponent hj
    exact h.symm.trans (add_comm _ _)
  rw [coordinateRatioFraction, homogeneousToLaurent_mk, one_nsmul, map_mul,
    polynomialToLaurent_X, polynomialToLaurent_chartProduct, ← laurentMonomial_add,
    ← laurentMonomial_add, hexp]
  congr 1
  abel

/-- Inverting a coordinate ratio on a standard chart gives the indicated
smaller standard open. -/
theorem basicOpen_projectiveChartRatio {s : Finset I} (i j : I) (hj : j ∈ s) :
    (P : Scheme.{u}).basicOpen (projectiveChartScalar A n s (coordinateRatio (A := A) i j hj)) =
      standardOpen A n (insert i s) := by
  let f := chartProduct A s
  let z := coordinateRatioFraction A n i j hj
  let r := projectiveChartScalar A n s (coordinateRatio (A := A) i j hj)
  have hr : r = Proj.awayToSection G f z := by
    change projectiveChartScalar A n s (coordinateRatio (A := A) i j hj) = _
    rw [← coordinateRatioFraction_eq A n i j hj]
    exact congrArg (fun x => Proj.awayToSection G f x)
      ((homogeneousChartRingEquiv (A := A) s).symm_apply_apply z)
  change (P : Scheme.{u}).basicOpen r = _
  rw [hr]
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  change x ∈ (P : Scheme.{u}).basicOpen (Proj.awayToSection G f z) ↔
    x ∈ standardOpen A n (insert i s)
  have hx' : x ∈ standardOpen A n (insert i s) ↔
      x ∈ standardOpen A n s ∧ x ∈ coordinateOpen A n i := by
    rw [mem_standardOpen A n (insert i s), mem_standardOpen A n s, Finset.forall_mem_insert, and_comm]
  rw [hx']
  by_cases hx : x ∈ standardOpen A n s
  · simp only [hx, true_and]
    rw [Scheme.mem_basicOpen _ _ x hx]
    have h := ProjectiveSpectrum.Proj.awayToSection_germ G f x hx
    have hval := congrArg (fun g => g z) h
    change IsUnit (((ProjectiveSpectrum.Proj.structureSheaf G).presheaf.germ _ x hx)
      (Proj.awayToSection G f z)) ↔ _
    let incl : Submonoid.powers f ≤ x.asHomogeneousIdeal.toIdeal.primeCompl :=
      Submonoid.powers_le.mpr hx
    rw [show ((ProjectiveSpectrum.Proj.structureSheaf G).presheaf.germ _ x hx)
      (Proj.awayToSection G f z) =
      (AlgebraicGeometry.Proj.stalkIso' G x).symm (HomogeneousLocalization.mapId G incl z)
      from hval]
    rw [isUnit_map_iff, ← HomogeneousLocalization.isUnit_iff_isUnit_val]
    have hh : (HomogeneousLocalization.mapId G incl z).val =
        Localization.mk (MvPolynomial.X i * chartProduct A (s.erase j))
          (show x.asHomogeneousIdeal.toIdeal.primeCompl from ⟨f, hx⟩) := by
      change (HomogeneousLocalization.mapId G incl (coordinateRatioFraction A n i j hj)).val = _
      simp only [coordinateRatioFraction, HomogeneousLocalization.Away.mk,
        HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, GradedRingHom.id_apply]
      congr 1
      exact Subtype.ext (pow_one f)
    rw [hh, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    change MvPolynomial.X i * chartProduct A (s.erase j) ∉ x.asHomogeneousIdeal.toIdeal ↔
      MvPolynomial.X i ∉ x.asHomogeneousIdeal.toIdeal
    have hden : chartProduct A (s.erase j) ∉ x.asHomogeneousIdeal.toIdeal :=
      standardOpen_antitone A n (Finset.erase_subset j s) hx
    exact ⟨fun h hp => h (Ideal.mul_mem_right _ _ hp), fun h hp =>
      ((show (x.asHomogeneousIdeal.toIdeal : Ideal (MvPolynomial I A)).IsPrime from inferInstance).mem_or_mem hp).elim h hden⟩
  · simp only [hx, false_and, iff_false]
    exact fun h => hx ((P : Scheme.{u}).basicOpen_le _ h)



private theorem homogeneousChartRingEquiv_constants (s : Finset I) (a : A) :
    homogeneousChartRingEquiv (A := A) s
      (HomogeneousLocalization.fromZeroRingHom G _ (homogeneousConstants A n a)) =
        algebraMap A (laurentChartRing A s) a := by
  apply Subtype.ext
  change homogeneousToLaurent s
    (HomogeneousLocalization.fromZeroRingHom G _ (homogeneousConstants A n a)) =
      algebraMap A (LaurentPolynomial A I) a
  have hval : (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers (chartProduct A s))
      (homogeneousConstants A n a)).val = algebraMap (MvPolynomial I A) _ (MvPolynomial.C a) := by
    rfl
  have h1 := congrArg (awayToLaurent (A := A) s) hval
  have h2 : awayToLaurent (A := A) s
      (algebraMap (MvPolynomial I A) (Localization.Away (chartProduct A s)) (MvPolynomial.C a)) =
      polynomialToLaurent (MvPolynomial.C a) :=
    IsLocalization.lift_eq (chartProduct_unit s) (MvPolynomial.C a)
  exact h1.trans (h2.trans ((polynomialToLaurent (A := A)).commutes a))

private theorem opens_ι_appTop (U : (P : Scheme.{u}).Opens) :
    U.ι.appTop ≫ U.topIso.hom = (P : Scheme.{u}).presheaf.map U.leTop.op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  rfl

/-- The chart ring comparison respects the structural maps from the base ring. -/
theorem projectiveChartScalar_const (s : Finset I) (a : A) :
    projectiveChartScalar A n s (algebraMap A (laurentChartRing A s) a) =
      groundRingHomOpen (projectiveSpace A n) (standardOpen A n s) a := by
  let U := standardOpen A n s
  let f := chartProduct A s
  let α := CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers f))
  let β := CommRingCat.ofHom (homogeneousConstants A n)
  have hstruct : U.ι ≫ (projectiveSpace A n).hom =
      Proj.basicOpenToSpec G f ≫ Spec.map (β ≫ α) := by
    have ht : Proj.basicOpen G (1 : MvPolynomial I A) = ⊤ := Proj.basicOpen_one G
    have hl : U ≤ Proj.basicOpen G (1 : MvPolynomial I A) := ht.symm ▸ le_top
    have hpref : U.ι ≫ (Scheme.topIso P).inv ≫ (Scheme.isoOfEq P ht).inv =
        (P : Scheme.{u}).homOfLE hl := by
      rw [← Category.assoc, Iso.comp_inv_eq]
      simp only [Iso.comp_inv_eq]
      simp only [Scheme.topIso_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]
    have hf : f = 1 * f := (one_mul f).symm
    let q := CommRingCat.ofHom (HomogeneousLocalization.awayMap G (chartProduct_mem s) hf)
    let α₁ := CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom G
      (Submonoid.powers (1 : MvPolynomial I A)))
    have hq : α₁ ≫ q = α := by
      ext a
      exact congrArg HomogeneousLocalization.val
        (HomogeneousLocalization.awayMap_fromZeroRingHom G (chartProduct_mem s) hf a)
    have hm := Proj.basicOpenToSpec_SpecMap_awayMap G (chartProduct_mem s) hf
    let suffix := Proj.basicOpenToSpec G (1 : MvPolynomial I A) ≫ Spec.map α₁ ≫ Spec.map β
    have hprefix_comp := congrArg (fun m => m ≫ suffix) hpref
    simp only [Category.assoc] at hprefix_comp
    have hmap : Proj.basicOpenToSpec G f ≫ Spec.map q =
        (P : Scheme.{u}).homOfLE hl ≫ Proj.basicOpenToSpec G 1 := hm
    change U.ι ≫ (Scheme.topIso P).inv ≫ (Scheme.isoOfEq P ht).inv ≫ suffix = _
    rw [hprefix_comp]
    dsimp only [suffix]
    rw [← reassoc_of% hmap]
    simp only [Category.assoc, ← Spec.map_comp, hq]
  have h := congrArg Scheme.Hom.appTop hstruct
  have hh : (Proj.basicOpenToSpec G f).appTop = (Scheme.ΓSpecIso _).hom ≫
      Proj.awayToSection G f ≫ U.topIso.inv := Proj.basicOpenToSpec_app_top G f
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, hh] at h
  have hm := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g ≫ U.topIso.hom) h
  simp only [Category.assoc, opens_ι_appTop, Iso.inv_hom_id, Category.comp_id] at hm
  have hscalar : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (projectiveSpace A n).hom.appTop ≫
        (P : Scheme.{u}).presheaf.map U.leTop.op =
      β ≫ α ≫ Proj.awayToSection G f := by
    rw [hm, ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc, Category.assoc]
  have ha := congrArg (fun h : CommRingCat.of A ⟶ Γ(P, U) => h a) hscalar
  change projectiveChartScalar A n s (algebraMap A (laurentChartRing A s) a) = _
  rw [← homogeneousChartRingEquiv_constants A n s a]
  change Proj.awayToSection G f
    ((homogeneousChartRingEquiv (A := A) s).symm
      (homogeneousChartRingEquiv s (HomogeneousLocalization.fromZeroRingHom G _
        (homogeneousConstants A n a)))) = _
  rw [RingEquiv.symm_apply_apply]
  exact ha.symm

end ProjectiveScalars

end ChartGeometry


section ChartCechCohomology

namespace ChartModules

open scoped BigOperators Simplicial
open CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {A : Type u} [CommRing A] {I : Type} [Fintype I] [LinearOrder I]

/-- The intersection poset, where larger sets of indices mean smaller opens. -/
abbrev ChartPoset (I : Type) := (Set I)ᵒᵈ

/-- The finite set of inverted coordinates belonging to a chart intersection. -/
def chartSet (S : ChartPoset I) : Finset I := (Set.toFinite (OrderDual.ofDual S)).toFinset

@[simp]
theorem mem_chartSet (S : ChartPoset I) (i : I) :
    i ∈ chartSet S ↔ i ∈ (OrderDual.ofDual S : Set I) := Set.Finite.mem_toFinset _

theorem chartSet_antitone : Antitone (chartSet : ChartPoset I → Finset I) :=
  fun _ _ h => Set.Finite.toFinset_mono h

private def resLinear (M : ChartModules A I) {s t : Finset I} (h : s ⊆ t) :
    M.obj s →ₗ[A] M.obj t where
  toFun := M.res h
  map_add' := map_add (M.res h)
  map_smul' a x := by
    change M.res h ((algebraMap A (laurentChartRing A s)) a • x) =
      (algebraMap A (laurentChartRing A t)) a • M.res h x
    rw [res_smul, AlgHom.commutes]

/-- Underlying presheaf of modules over the coefficient ring. -/
def presheaf (M : ChartModules A I) : (ChartPoset I)ᵒᵖ ⥤ ModuleCat.{u} A where
  obj S := ModuleCat.of A (M.obj (chartSet S.unop))
  map f := ModuleCat.ofHom (M.resLinear (chartSet_antitone (leOfHom f.unop)))
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact M.res_id _
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (M.res_comp _ _ x).symm

variable {M N : ChartModules A I}

/-- A map on the underlying presheaves over the coefficient ring. -/
def Map.presheafMap (f : Map M N) : M.presheaf ⟶ N.presheaf where
  app S := ModuleCat.ofHom ((f.app (chartSet S.unop)).restrictScalars A)
  naturality := by
    intro S T g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact f.naturality (chartSet_antitone (leOfHom g.unop))

/-- The chart indexed by a single coordinate. -/
def singletonChart (i : ULift.{u} I) : ChartPoset I := OrderDual.toDual {i.down}

/-- The ordered Čech complex of a chart module diagram. -/
abbrev complex (M : ChartModules A I) : CochainComplex (ModuleCat.{u} A) ℕ :=
  cechComplex singletonChart M.presheaf

/-- The map of ordered Čech complexes associated to a map of chart diagrams. -/
abbrev Map.complexMap (f : Map M N) : M.complex ⟶ N.complex :=
  cechMap singletonChart f.presheafMap

private def uliftDownOrderEmbedding : ULift.{u} I ↪o I where
  toFun := ULift.down
  inj' := ULift.down_injective
  map_rel_iff' := Iff.rfl

private def uliftUpOrderEmbedding : I ↪o ULift.{u} I where
  toFun := ULift.up
  inj' := ULift.up_injective
  map_rel_iff' := Iff.rfl

/-- The coordinates appearing in the tuple, seen as a finite subset. -/
def tupleIndices {k : ℕ} (e : Fin k ↪o ULift.{u} I) : Finset I :=
  tupleFinset (e.trans uliftDownOrderEmbedding)

@[simp]
theorem card_tupleIndices {k : ℕ} (e : Fin k ↪o ULift.{u} I) :
    (tupleIndices e).card = k := card_tupleFinset _

private def tupleAt (s : Finset I) {k : ℕ} (h : s.card = k) : Fin k ↪o ULift.{u} I :=
  (s.orderEmbOfFin h).trans uliftUpOrderEmbedding

@[simp]
private theorem tupleIndices_tupleAt (s : Finset I) {k : ℕ} (h : s.card = k) :
    tupleIndices (tupleAt s h) = s :=
  tupleFinset_orderEmbOfFin s h

@[simp]
private theorem tupleAt_tupleIndices {k : ℕ} (e : Fin k ↪o ULift.{u} I) :
    tupleAt (tupleIndices e) (card_tupleIndices e) = e := by
  change ((tupleFinset (e.trans uliftDownOrderEmbedding)).orderEmbOfFin _).trans
    uliftUpOrderEmbedding = e
  rw [orderEmbOfFin_tupleFinset]
  ext j
  rfl

private theorem chartSet_tupleOpen {k : ℕ} (e : Fin (k + 1) ↪o ULift.{u} I) :
    chartSet (tupleOpen singletonChart e) = tupleIndices e := by
  ext i
  rw [mem_chartSet, tupleIndices, mem_tupleFinset]
  change i ∈ ⋃ j, ({(e j).down} : Set I) ↔ ∃ j, (e j).down = i
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, eq_comm]

private theorem chartSet_tupleOpen_nonempty {k : ℕ} (e : Fin (k + 1) ↪o ULift.{u} I) :
    (chartSet (tupleOpen singletonChart e)).Nonempty := by
  rw [chartSet_tupleOpen, ← Finset.card_pos, card_tupleIndices]
  exact Nat.succ_pos _

/-- Comparison with the chart indexed by the image of the tuple. -/
def sectionEquiv (M : ChartModules A I) (k : ℕ) (e : Fin (k + 1) ↪o ULift.{u} I) :
    M.presheaf.obj (op (tupleOpen singletonChart e)) ≃ₗ[A] M.obj (tupleIndices e) :=
  (eqToIso (congrArg (fun s => ModuleCat.of A (M.obj s)) (chartSet_tupleOpen e))).toLinearEquiv


private theorem tupleIndices_delete {k : ℕ} (e : Fin (k + 1) ↪o ULift.{u} I) (j : Fin (k + 1)) :
    tupleIndices (j.succAboveOrderEmb.trans e) = (tupleIndices e).erase (e j).down :=
  tupleFinset_delete (e.trans uliftDownOrderEmbedding) j

private theorem tupleIndices_face_subset {k : ℕ} (e : Fin (k + 1) ↪o ULift.{u} I) (j : Fin (k + 1)) :
    tupleIndices (j.succAboveOrderEmb.trans e) ⊆ tupleIndices e := by
  rw [tupleIndices_delete]
  exact Finset.erase_subset _ _

private theorem resLinear_eqToIso (M : ChartModules A I) {s t S T : Finset I} (hs : s = S) (ht : t = T)
    (h : s ⊆ t) (H : S ⊆ T) (x : M.obj s) :
    (eqToIso (congrArg (fun q => ModuleCat.of A (M.obj q)) ht)).hom (M.resLinear h x) =
      M.resLinear H ((eqToIso (congrArg (fun q => ModuleCat.of A (M.obj q)) hs)).hom x) := by
  subst S T
  rfl

/-- The differential on the chart diagram, written on the finite image of each
ordered tuple. -/
theorem complex_d_apply (M : ChartModules A I) (k : ℕ) (x : M.complex.X k)
    (e : Fin (k + 2) ↪o ULift.{u} I) :
    M.sectionEquiv (k + 1) e (M.complex.d k (k + 1) x e) =
      ∑ j : Fin (k + 2), (-1 : ℤ) ^ (j : ℕ) •
        M.res (tupleIndices_face_subset e j)
          (M.sectionEquiv k (j.succAboveOrderEmb.trans e) (x (j.succAboveOrderEmb.trans e))) := by
  rw [cechDifferential_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  congr 1
  exact M.resLinear_eqToIso (chartSet_tupleOpen _) (chartSet_tupleOpen _) _
    (tupleIndices_face_subset e j) _

/-- Degree-`d` Laurent coefficients on an intersection, indexed by all exponents
of that degree and zero on exponents with other denominators. -/
private def twistCoefficients (s : Finset I) (d : ℤ) :
    (twist (A := A) (I := I) d).obj s →ₗ[A] LaurentExponents I d →₀ A where
  toFun x := Finsupp.subtypeDomain _ x.val.coeff
  map_add' _ _ := Finsupp.subtypeDomain_add
  map_smul' a x := by
    ext e
    change (algebraMap A (LaurentPolynomial A I) a * x.val).coeff e.val = a * x.val.coeff e.val
    rw [← Algebra.smul_def, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]

private theorem twistCoefficients_outside (s : Finset I) (d : ℤ) (x : (twist (A := A) (I := I) d).obj s)
    (e : LaurentExponents I d) (h : ¬negativeSupport e ⊆ s) :
    twistCoefficients s d x e = 0 := by
  by_contra hc
  have ht := x.property e.val hc
  exact h fun i hi => by
    by_contra hni
    exact (not_lt_of_ge (ht.2 i hni)) (Finset.mem_filter.mp hi).2

private theorem twistCoefficients_injective (s : Finset I) (d : ℤ) :
    Function.Injective (twistCoefficients (A := A) s d) := by
  intro x y h
  apply Subtype.ext
  apply AddMonoidAlgebra.ext
  ext e
  by_cases he : ∑ i, e i = d
  · exact congrArg (fun f : LaurentExponents I d →₀ A => f ⟨e, he⟩) h
  · have hx : x.val.coeff e = 0 := by
      by_contra hn
      exact he (x.property e hn).1
    have hy : y.val.coeff e = 0 := by
      by_contra hn
      exact he (y.property e hn).1
    exact hx.trans hy.symm

private def fromTwistCoefficients (s : Finset I) (d : ℤ) (f : LaurentExponents I d →₀ A)
    (hf : ∀ e, ¬negativeSupport e ⊆ s → f e = 0) :
    (twist (A := A) (I := I) d).obj s := by
  classical
  let emb : LaurentExponents I d ↪ (I → ℤ) := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.embDomain emb f), ?_⟩
  intro e he
  change (Finsupp.embDomain emb f) e ≠ 0 at he
  obtain ⟨z, rfl⟩ : e ∈ Set.range emb := by
    by_contra hn
    exact he (Finsupp.embDomain_of_notMem_range _ _ _ hn)
  rw [Finsupp.embDomain_apply_self] at he
  refine ⟨z.property, fun i hi => ?_⟩
  by_contra hneg
  exact he (hf z (fun h => hi (h (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, lt_of_not_ge hneg⟩))))

@[simp]
private theorem twistCoefficients_fromTwistCoefficients (s : Finset I) (d : ℤ)
    (f : LaurentExponents I d →₀ A) (hf : ∀ e, ¬negativeSupport e ⊆ s → f e = 0) :
    twistCoefficients s d (fromTwistCoefficients s d f hf) = f := by
  ext e
  exact Finsupp.embDomain_apply_self _ _ e

private def complexCoordinates (d : ℤ) (k : ℕ) :
    (twist (A := A) (I := I) d).complex.X k →ₗ[A] laurentCochains A I d (k + 1) := by
  let W := twist (A := A) (I := I) d
  let f (s : Finset I) : W.complex.X k →ₗ[A] (LaurentExponents I d →₀ A) :=
    if hs : s.card = k + 1 then
      let e := tupleAt s hs
      let t := (eqToIso (congrArg (fun s => ModuleCat.of A (W.obj s))
        (tupleIndices_tupleAt s hs))).toLinearEquiv
      (twistCoefficients s d).comp (t.toLinearMap.comp
        ((W.sectionEquiv k e).toLinearMap.comp (LinearMap.proj e)))
    else 0
  refine (LinearMap.pi f).codRestrict _ ?_
  intro x s a ha
  by_cases hs : s.card = k + 1
  · simp only [LinearMap.pi_apply, f, dite_eq_left hs, LinearMap.comp_apply]
    exact twistCoefficients_outside s d _ a (ha.resolve_left (fun h => h hs))
  · simp [f, hs]

private theorem twistCoefficients_transport (d : ℤ) {s t : Finset I} (h : s = t)
    (x : (twist (A := A) (I := I) d).obj s) :
    twistCoefficients t d
      ((eqToIso (congrArg (fun q => ModuleCat.of A ((twist (A := A) (I := I) d).obj q)) h)).hom x) =
      twistCoefficients s d x := by
  subst t
  rfl

private theorem complexCoordinates_on_tuple (d : ℤ) (k : ℕ)
    (x : (twist (A := A) (I := I) d).complex.X k) (e : Fin (k + 1) ↪o ULift.{u} I) :
    (complexCoordinates d k x).val (tupleIndices e) =
      twistCoefficients _ d ((twist (A := A) (I := I) d).sectionEquiv k e (x e)) := by
  simp only [complexCoordinates, LinearMap.codRestrict_apply, LinearMap.pi_apply,
    dite_eq_left (card_tupleIndices e), LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  let W := twist (A := A) (I := I) d
  let t := tupleAt (tupleIndices e) (card_tupleIndices e)
  have ht : tupleIndices t = tupleIndices e := tupleIndices_tupleAt _ _
  let e₀ := eqToIso (congrArg (fun q => ModuleCat.of A (W.obj q)) ht)
  change twistCoefficients _ d (e₀.hom (W.sectionEquiv k t (x t))) = _
  refine (twistCoefficients_transport d ht (W.sectionEquiv k t (x t))).trans ?_
  have he : t = e := tupleAt_tupleIndices e
  exact congrArg (fun z => twistCoefficients (tupleIndices z) d (W.sectionEquiv k z (x z))) he

private def complexCoordinatesEquiv (d : ℤ) (k : ℕ) :
    (twist (A := A) (I := I) d).complex.X k ≃ₗ[A] laurentCochains A I d (k + 1) :=
  LinearEquiv.ofBijective (complexCoordinates d k) (by
    let W := twist (A := A) (I := I) d
    refine ⟨?_, ?_⟩
    · intro x y h
      funext e
      apply (W.sectionEquiv k e).injective
      apply twistCoefficients_injective _ d
      rw [← complexCoordinates_on_tuple, ← complexCoordinates_on_tuple, h]
    · intro f
      let x : W.complex.X k := fun e =>
        (W.sectionEquiv k e).symm (fromTwistCoefficients _ d (f.val (tupleIndices e))
          (fun a ha => f.property _ _ (Or.inr ha)))
      refine ⟨x, Subtype.ext (funext fun s => ?_)⟩
      by_cases hs : s.card = k + 1
      · have h := complexCoordinates_on_tuple d k x (tupleAt s hs)
        rw [sectionEquiv, ← sectionEquiv, show W.sectionEquiv k (tupleAt s hs)
          (x (tupleAt s hs)) = fromTwistCoefficients _ d (f.val (tupleIndices (tupleAt s hs)))
            (fun a ha => f.property _ _ (Or.inr ha)) from
              (W.sectionEquiv k _).apply_symm_apply _,
          twistCoefficients_fromTwistCoefficients, tupleIndices_tupleAt] at h
        exact h
      · ext a
        exact ((complexCoordinates d k x).property s a (Or.inl hs)).trans
          (f.property s a (Or.inl hs)).symm)


private theorem complexCoordinates_differential_at_tuple (d : ℤ) (k : ℕ)
    (x : (twist (A := A) (I := I) d).complex.X k)
    (e : Fin (k + 2) ↪o ULift.{u} I) (a : LaurentExponents I d) :
    (complexCoordinates d (k + 1) ((twist (A := A) (I := I) d).complex.d k (k + 1) x)).val
        (tupleIndices e) a =
      monomialDifferential (fun t => (complexCoordinates d k x).val t a) (tupleIndices e) := by
  let W := twist (A := A) (I := I) d
  rw [complexCoordinates_on_tuple]
  let coefficient := (Finsupp.lapply a : (LaurentExponents I d →₀ A) →ₗ[A] A).comp
    (twistCoefficients (A := A) (tupleIndices e) d)
  change coefficient (W.sectionEquiv (k + 1) e (W.complex.d k (k + 1) x e)) = _
  rw [complex_d_apply, map_sum]
  have sum_over_tuple (f : I → A) :
      (∑ i ∈ tupleIndices e, f i) = ∑ j : Fin (k + 2), f ((e j).down) :=
    Finset.sum_map Finset.univ (e.trans uliftDownOrderEmbedding).toEmbedding f
  rw [monomialDifferential, sum_over_tuple]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul, ← tupleIndices_delete, complexCoordinates_on_tuple]
  have hpos : position (tupleIndices e) (e j).down = (j : ℕ) :=
    card_filter_tupleFinset_lt (e.trans uliftDownOrderEmbedding) j
  rw [faceSign, hpos]
  change ((-1 : ℤ) ^ (j : ℕ)) •
      (twistCoefficients _ d (W.sectionEquiv k _ (x (j.succAboveOrderEmb.trans e))) a) =
    (-1 : A) ^ (j : ℕ) *
      (twistCoefficients _ d (W.sectionEquiv k _ (x (j.succAboveOrderEmb.trans e))) a)
  rw [← Int.cast_smul_eq_zsmul A, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul]

/-- All cohomology modules of the Laurent twist complex are finite. -/
theorem finite_homology_twist [IsNoetherianRing A] (d : ℤ) (i : ℕ) :
    Module.Finite A ((twist (A := A) (I := I) d).complex.homology i) := by
  refine finite_homology_of_laurent_model _ (complexCoordinatesEquiv d) ?_ i
  intro k x s a hs
  have h := complexCoordinates_differential_at_tuple d k x (tupleAt s hs) a
  rw [tupleIndices_tupleAt] at h
  exact h

private def Map.complexShortComplex (f : Map M N) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ) :=
  ShortComplex.mk f.kerι.complexMap f.complexMap (by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    change f.app (chartSet (tupleOpen singletonChart e)) (x e).val = 0
    exact (x e).property)

theorem Map.complexShortComplex_shortExact (f : Map M N)
    (hf : ∀ s : Finset I, s.Nonempty → Function.Surjective (f.app s)) :
    f.complexShortComplex.ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change (fun e => f.app (chartSet (tupleOpen singletonChart e)) (x e)) = 0 ↔ _
    constructor
    · intro hx
      refine ⟨fun e => ⟨x e, LinearMap.mem_ker.mpr (congrFun hx e)⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact funext fun e => LinearMap.mem_ker.mp (y e).property
  · intro x y h
    exact funext fun e => Subtype.ext (congrFun h e)
  · intro x
    have H (e : Fin (k + 1) ↪o ULift.{u} I) := hf _
      (chartSet_tupleOpen_nonempty e) (x e)
    exact ⟨fun e => (H e).choose, funext fun e => (H e).choose_spec⟩

variable {J : Type u}

/-- The projections from a product of chart modules. -/
def projMap (N : J → ChartModules A I) (j : J) : Map (pi N) (N j) where
  app _ := LinearMap.proj j
  naturality _ _ := rfl

private def complexProductFan (N : J → ChartModules A I) : Fan (fun j => (N j).complex) :=
  Fan.mk (pi N).complex (fun j => (projMap N j).complexMap)

private def complexProductIsLimit (N : J → ChartModules A I) : IsLimit (complexProductFan N) := by
  apply HomologicalComplex.isLimitOfEval
  intro k
  refine
    { lift := fun s => ModuleCat.ofHom (LinearMap.pi fun e => LinearMap.pi fun j =>
        LinearMap.proj e ∘ₗ (s.π.app ⟨j⟩).hom)
      fac := ?_
      uniq := ?_ }
  · rintro s ⟨j⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    rfl
  · intro s m hm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e j
    exact congrArg (fun h => h x e) (hm ⟨j⟩)

private theorem finite_homology_pi [Finite J] (N : J → ChartModules A I) (i : ℕ)
    (hN : ∀ j, Module.Finite A ((N j).complex.homology i)) :
    Module.Finite A ((pi N).complex.homology i) := by
  let C := CochainComplex (ModuleCat.{u} A) ℕ
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℕ) i
  let X : J → C := fun j => (N j).complex
  let e : (pi N).complex ≅ ∏ᶜ X :=
    (complexProductIsLimit N).conePointUniqueUpToIso (limit.isLimit _)
  let e' : ((pi N).complex).homology i ≅ ModuleCat.of A (∀ j, (N j).complex.homology i) :=
    H.mapIso e ≪≫ PreservesProduct.iso H X ≪≫ ModuleCat.piIsoPi _
  let _ := hN
  exact Module.Finite.equiv e'.toLinearEquiv.symm

set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 95000 in
/-- Over Noetherian chart rings, finite localizing diagrams have finite Čech
cohomology. The induction uses finite twist presentations and their kernels. -/
theorem finite_homology_of_finite_charts [IsNoetherianRing A]
    (hA : ∀ i : I, IsNoetherianRing (laurentChartRing A {i}))
    (M : ChartModules A I) (hM : M.IsLocalizing)
    (hfin : ∀ i : I, Module.Finite (laurentChartRing A {i}) (M.obj {i})) (i : ℕ) :
    Module.Finite A (M.complex.homology i) := by
  let C := CochainComplex (ModuleCat.{u} A) ℕ
  let P (K : C) :=
    ∃ M' : ChartModules A I, M'.IsLocalizing ∧
      (∀ j : I, Module.Finite (laurentChartRing A {j}) (M'.obj {j})) ∧ Nonempty (M'.complex ≅ K)
  apply finite_homology_of_presentations P (Fintype.card (ULift.{u} I)) ?_ ?_ _
    ⟨M, hM, hfin, ⟨Iso.refl _⟩⟩ i
  · rintro K ⟨M', _, _, ⟨e⟩⟩ n hn
    have h := cechHomology_isZero_of_card_le singletonChart M'.presheaf n hn
    exact IsZero.of_iso h ((HomologicalComplex.homologyFunctor _ _ n).mapIso e).symm
  · rintro K ⟨M', hloc, hfinite, ⟨e⟩⟩
    obtain ⟨J, instJ, d, f, hf⟩ := exists_finite_twist_presentation M' hloc hfinite
    let _ := instJ
    have hlocalizing : (pi fun j => twist (d j) : ChartModules A I).IsLocalizing :=
      pi_isLocalizing _ fun _ => twist_isLocalizing _
    refine ⟨f.complexShortComplex, f.complexShortComplex_shortExact hf,
      ⟨f.ker, f.ker_isLocalizing hlocalizing hloc, ?_, ⟨Iso.refl _⟩⟩, ?_, ⟨e⟩⟩
    · intro j
      let _ := hA j
      let _ : Module.Finite (laurentChartRing A {j}) (laurentChartRing A {j}) := Module.Finite.self _
      have hfree (t : J) : Module.Finite (laurentChartRing A {j})
          ((twist (A := A) (I := I) (d t)).obj {j}) :=
        Module.Finite.equiv (twistTrivialization (Finset.mem_singleton_self j) (d t))
      let _ := hfree
      have : Module.Finite (laurentChartRing A {j}) ((pi fun t => twist (d t) : ChartModules A I).obj {j}) :=
        inferInstanceAs (Module.Finite (laurentChartRing A {j}) (∀ t : J,
          (twist (A := A) (I := I) (d t)).obj {j}))
      change Module.Finite (laurentChartRing A {j}) (LinearMap.ker (f.app {j}))
      infer_instance
    · intro n
      exact finite_homology_pi (fun t => twist (d t)) n (fun t => finite_homology_twist (d t) n)

end ChartModules

end ChartCechCohomology


section ProjectiveCohomology

open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false

section Geometry

variable {A : Type u} [CommRing A] {n : ℕ} {Y : SchemeOverRing A}
    (j : Y ⟶ projectiveSpace A n)

local notation "I" => Fin (n + 1)

private abbrev subschemeChart (s : Finset I) : Y.left.Opens :=
  j.left ⁻¹ᵁ standardOpen A n s

private theorem subschemeChart_antitone : Antitone (subschemeChart j) :=
  fun _ _ h => j.left.preimage_mono (standardOpen_antitone A n h)

private def subschemeChartScalar (s : Finset I) :
    laurentChartRing A s →+* Γ(Y.left, subschemeChart j s) :=
  (j.left.app (standardOpen A n s)).hom.comp (projectiveChartScalar A n s)

private theorem subschemeChartScalar_natural {s t : Finset I} (h : s ⊆ t)
    (r : laurentChartRing A s) :
    Y.left.presheaf.map (homOfLE (subschemeChart_antitone j h)).op
      (subschemeChartScalar j s r) = subschemeChartScalar j t (laurentChartRestrict h r) := by
  have h' := congrArg (fun f : Γ(projectiveScheme A n, standardOpen A n s) ⟶
      Γ(Y.left, subschemeChart j t) => f (projectiveChartScalar A n s r))
    (j.left.naturality (homOfLE (standardOpen_antitone A n h)).op)
  change Y.left.presheaf.map (homOfLE (subschemeChart_antitone j h)).op
      ((j.left.app (standardOpen A n s)) (projectiveChartScalar A n s r)) =
    (j.left.app (standardOpen A n t)) (projectiveChartScalar A n t (laurentChartRestrict h r))
  rw [← projectiveChartScalar_natural A n h r]
  exact h'.symm

private theorem groundRingHomOpen_appLE (X : SchemeOverRing A) (U : X.left.Opens) :
    groundRingHomOpen X U =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ X.hom.appLE ⊤ U (by simp)).hom := rfl

private theorem groundRingHomOpen_over (U : (projectiveSpace A n).left.Opens) (a : A) :
    j.left.app U (groundRingHomOpen (projectiveSpace A n) U a) =
      groundRingHomOpen Y (j.left ⁻¹ᵁ U) a := by
  rw [groundRingHomOpen_appLE, groundRingHomOpen_appLE]
  have hw : j.left ≫ (projectiveSpace A n).hom = Y.hom := Over.w j
  have h := j.left.appLE_comp_appLE (projectiveSpace A n).hom ⊤ U (j.left ⁻¹ᵁ U)
    (by simp) le_rfl
  rw [← Scheme.Hom.app_eq_appLE j.left] at h
  have h' : (projectiveSpace A n).hom.appLE ⊤ U (by simp) ≫ j.left.app U =
      Y.hom.appLE ⊤ (j.left ⁻¹ᵁ U) (by simp) := by
    exact h.trans (by rw [hw])
  exact congrArg (fun g : Γ(Spec (CommRingCat.of A), ⊤) ⟶ Γ(Y.left, j.left ⁻¹ᵁ U) =>
    g ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) h'

private theorem subschemeChartScalar_const (s : Finset I) (a : A) :
    subschemeChartScalar j s (algebraMap A (laurentChartRing A s) a) =
      groundRingHomOpen Y (subschemeChart j s) a := by
  change (j.left.app (standardOpen A n s))
      (projectiveChartScalar A n s (algebraMap A (laurentChartRing A s) a)) = _
  rw [projectiveChartScalar_const]
  exact groundRingHomOpen_over j _ _

/-- The actual local sections of the sheaf on the projective coordinate charts. -/
def chartSections (F : Y.left.Modules) : ChartModules A I where
  obj s := (ModuleCat.restrictScalars (subschemeChartScalar j s)).obj
    (F.val.obj (op (subschemeChart j s)))
  res h :=
    { toFun := fun x => F.val.map (homOfLE (subschemeChart_antitone j h)).op x
      map_add' := map_add (F.val.map _).hom
      map_smul' := by
        intro r x
        let k := (homOfLE (subschemeChart_antitone j h)).op
        change (F.val.map k (subschemeChartScalar j _ r •
          (show Γ(F, subschemeChart j _) from x)) : Γ(F, subschemeChart j _)) =
          subschemeChartScalar j _ (laurentChartRestrict h r) •
            (show Γ(F, subschemeChart j _) from F.val.map k x)
        have h' := F.val.map_smul k (subschemeChartScalar j _ r) x
        rw [← subschemeChartScalar_natural j h]
        exact h' }
  res_id _ x := by
    change F.val.map (𝟙 _) x = x
    rw [F.val.map_id]
    rfl
  res_comp {s t w} h h' x := by
    let a := (homOfLE (subschemeChart_antitone j h)).op
    let b := (homOfLE (subschemeChart_antitone j h')).op
    change F.val.map b (F.val.map a x) = F.val.map (a ≫ b) x
    exact (F.val.map_comp_apply a b x).symm

private theorem chartSections_isLocalizing (hj : IsClosedImmersion j.left)
    (F : Y.left.Modules) (hF : (F : SheafOfModules Y.left.ringCatSheaf).IsQuasicoherent) :
    (chartSections j F).IsLocalizing := by
  let _ := hj
  have localize {s : Finset I} (i l : I) (hl : l ∈ s) :
      subschemeChart j (insert i s) =
        Y.left.basicOpen (subschemeChartScalar j s (coordinateRatio (A := A) i l hl)) := by
    change j.left ⁻¹ᵁ _ = _
    rw [← basicOpen_projectiveChartRatio A n i l hl, Scheme.preimage_basicOpen]
    rfl
  have affine {s : Finset I} (hs : s.Nonempty) : IsAffineOpen (subschemeChart j s) :=
    (standardOpen_isAffine A n hs).preimage j.left
  constructor
  · intro s i l hl x
    let r := coordinateRatio (A := A) i l hl
    let h := Finset.subset_insert i s
    obtain ⟨k, y, hy⟩ := (affineModule_denominators F hF (affine ⟨l, hl⟩)
      (subschemeChartScalar j s r) (localize i l hl) (subschemeChart_antitone j h)).1 x
    refine ⟨k, y, ?_⟩
    change (F.val.map (homOfLE (subschemeChart_antitone j h)).op y : Γ(F, subschemeChart j (insert i s))) =
      subschemeChartScalar j (insert i s) ((laurentChartRestrict h r) ^ k) •
        (show Γ(F, subschemeChart j (insert i s)) from x)
    rw [map_pow, ← subschemeChartScalar_natural j h r]
    exact hy
  · intro s i l hl y hy
    let r := coordinateRatio (A := A) i l hl
    obtain ⟨k, hk⟩ := (affineModule_denominators F hF (affine ⟨l, hl⟩)
      (subschemeChartScalar j s r) (localize i l hl)
      (subschemeChart_antitone j (Finset.subset_insert i s))).2 y hy
    refine ⟨k, ?_⟩
    change subschemeChartScalar j s (r ^ k) • (show Γ(F, subschemeChart j s) from y) = 0
    rw [map_pow]
    exact hk

private theorem projectiveChartScalar_surjective {s : Finset I} (hs : s.Nonempty) :
    Function.Surjective (projectiveChartScalar A n s) :=
  (ConcreteCategory.bijective_of_isIso (projectiveChartAwayIso A n hs).hom).surjective.comp
    (homogeneousChartRingEquiv (A := A) s).symm.surjective

private theorem chartSections_finite (hj : IsClosedImmersion j.left) (F : Y.left.Modules)
    (hF : IsLineBundleOn A Y F) {s : Finset I} (hs : s.Nonempty) :
    Module.Finite (laurentChartRing A s) ((chartSections j F).obj s) := by
  let _ := hj
  let R := Γ(Y.left, subschemeChart j s)
  let φ := subschemeChartScalar j s
  let _ : Algebra (laurentChartRing A s) R := φ.toAlgebra
  have hU := standardOpen_isAffine A n hs
  have hφ : Function.Surjective φ :=
    (j.left.app_surjective _ hU).comp (projectiveChartScalar_surjective (A := A) (n := n) hs)
  have hR : Module.Finite (laurentChartRing A s) R := RingHom.Finite.of_surjective _ hφ
  have hM : Module.Finite R Γ(F, subschemeChart j s) :=
    finite_line_sections_of_isAffineOpen F hF.1 hF.2 _ (hU.preimage j.left)
  let _ : Module (laurentChartRing A s) Γ(F, subschemeChart j s) := Module.compHom _ φ
  have hT : IsScalarTower (laurentChartRing A s) R Γ(F, subschemeChart j s) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change @Module.Finite (laurentChartRing A s) Γ(F, subschemeChart j s) _ _ (Module.compHom _ φ)
  exact @Module.Finite.trans (laurentChartRing A s) R Γ(F, subschemeChart j s) _ _ _
    _ (Module.compHom _ φ) _ hT hR hM

private theorem projectiveChartRing_noetherian [IsNoetherianRing A] (s : Finset I) (hs : s.Nonempty) :
    IsNoetherianRing (laurentChartRing A s) := by
  let _ := projectiveSpace_proper A n
  have : IsLocallyNoetherian (projectiveSpace A n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpace A n).hom
  have : IsNoetherianRing Γ((projectiveSpace A n).left, standardOpen A n s) :=
    IsLocallyNoetherian.component_noetherian ⟨_, standardOpen_isAffine A n hs⟩
  exact isNoetherianRing_of_ringEquiv _ (projectiveChartRingEquiv A n hs)

end Geometry

section CechComparison

open ChartModules

variable {A : Type u} [CommRing A] {n : ℕ} {Y : SchemeOverRing A}
    (j : Y ⟶ projectiveSpace A n) (F : Y.left.Modules)

private def chartOpenFunctor : ChartPoset (Fin (n + 1)) ⥤ Y.left.Opens :=
  (show Monotone (fun s => subschemeChart j (chartSet s)) from
    fun _ _ h => subschemeChart_antitone j (chartSet_antitone h)).functor

private def chartSections_presheafIso :
    (chartSections j F).presheaf ≅ (chartOpenFunctor j).op ⋙ coefficientPresheaf F := by
  let E (s : (ChartPoset (Fin (n + 1)))ᵒᵖ) :
      (chartSections j F).presheaf.obj s ≃ₗ[A]
         ((chartOpenFunctor j).op ⋙ coefficientPresheaf F).obj s :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        let t := chartSet s.unop
        change subschemeChartScalar j t (algebraMap A (laurentChartRing A t) a) •
            (show Γ(F, subschemeChart j t) from x) =
          groundRingHomOpen Y (subschemeChart j t) a •
            (show Γ(F, subschemeChart j t) from x)
        rw [subschemeChartScalar_const] }
  exact NatIso.ofComponents (fun s => (E s).toModuleIso) (by
    intro s t g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

private theorem chartOpenFunctor_tupleOpen (k : ℕ)
    (e : Fin (k + 1) ↪o ULift.{u} (Fin (n + 1))) :
    (chartOpenFunctor j).op.obj (op (tupleOpen (singletonChart (I := Fin (n + 1))) e)) =
      op (tupleOpen (projectiveCover j) e) := by
  apply congrArg op
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  let S := tupleOpen (singletonChart (I := Fin (n + 1))) e
  change j.left x ∈ standardOpen A n (chartSet S) ↔ x ∈ (tupleOpen (D := Y.left.Opens) (projectiveCover j) e : Set Y.left)
  rw [mem_standardOpen]
  have hS (i : Fin (n + 1)) : i ∈ chartSet S ↔ ∃ a, (e a).down = i := by
    rw [mem_chartSet]
    change i ∈ ⋃ a, ({(e a).down} : Set (Fin (n + 1))) ↔ _
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, eq_comm]
  simp only [hS, tupleOpen, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact ⟨fun h a => h _ ⟨a, rfl⟩, fun h i ⟨a, ha⟩ => ha ▸ h a⟩

private def chartSectionsCechIso :
    (chartSections j F).complex ≅ cechComplex (projectiveCover j) (coefficientPresheaf F) :=
  cechIsoOfNatIso singletonChart _ (chartSections_presheafIso j F) ≪≫
    cechReindexIso (projectiveCover j) (coefficientPresheaf F) singletonChart (chartOpenFunctor j).op (chartOpenFunctor_tupleOpen j)

end CechComparison

/-- Coherent cohomology finiteness for a line on a closed subscheme of
finite-dimensional projective space over a Noetherian base. -/
theorem finite_cohomology_of_closedImmersion_projective
    (comparison : AffineCechComparison.{u}) {A : Type u} [CommRing A] [IsNoetherianRing A]
    {Y : SchemeOverRing A} {n : ℕ} (j : Y ⟶ projectiveSpace A n) (hj : IsClosedImmersion j.left)
    (F : Y.left.Modules) (hF : IsLineBundleOn A Y F) (i : ℕ) :
    Module.Finite A ((cohomology Y i).obj F) := by
  let M := chartSections j F
  let _ : Module.Finite A ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℕ) i).obj M.complex) :=
    ChartModules.finite_homology_of_finite_charts
      (fun a => projectiveChartRing_noetherian {a} ⟨a, Finset.mem_singleton_self a⟩)
      M (chartSections_isLocalizing j hj F hF.1)
      (fun a => chartSections_finite j hj F hF ⟨a, Finset.mem_singleton_self a⟩) i
  obtain ⟨e, _⟩ := comparison Y (projectiveCover j) (iSup_projectiveCover j)
    (projectiveCover_intersection_isAffine j hj) i
  let cohomologyIso := (e F hF.1) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℕ) i).mapIso
      (chartSectionsCechIso j F).symm
  exact Module.Finite.equiv cohomologyIso.toLinearEquiv.symm

end ProjectiveCohomology


/-- Arithmetic projective finiteness from the ordered frozen flag cohomology premises. -/
theorem arithmeticProjectiveFiniteness_conditional.{z}
    (comparison : AffineCechComparison.{z})
    (_cechBounded : CechBounded.{z,z})
    (_cechDegreeZeroComparison : CechDegreeZeroComparison.{z})
    (_centralCohomologyComparison : CentralCohomologyComparison.{z})
    (_centralCohomologyIsomorphism : CentralCohomologyIsomorphism.{z})
    (_centralCohomologyScalarAction : CentralCohomologyScalarAction.{z})
    (_centralScalarAction : CentralScalarAction.{z})
    (_centralSectionComparison : CentralSectionComparison.{z})
    (_centralTranslationOnCohomology : CentralTranslationOnCohomology.{z})
    (_eulerCharacteristicBound : EulerCharacteristicBound.{z})
    (_finiteAffineCover : FiniteAffineCover.{z})
    (_flagCechBaseChange : FlagCechBaseChange.{z})
    (_flagCohomologyBaseChange : FlagCohomologyBaseChange.{z})
    (_flagCohomologyFinite : FlagCohomologyFinite.{z})
    (_flagCohomologyRepresentation : FlagCohomologyRepresentation.{z})
    (_flagCohomologyZeroBaseChange : FlagCohomologyZeroBaseChange.{z})
    (_flagLineSheafIdentification : FlagLineSheafIdentification.{z})
    (_flagTranslationCohomologyMap : FlagTranslationCohomologyMap.{z})
    : LinearAlgebraicGroups.Specs.ArithmeticProjectiveFiniteness.Statement.{z} := by
  intro m _ Y n j hj F hF i
  let _ := baseRing_noetherian.{z} m
  exact finite_cohomology_of_closedImmersion_projective comparison j hj F hF i

end

end LinearAlgebraicGroups.Cohomology.ArithmeticProjectiveFiniteness

universe v8_closure_6ef8d167f9f622bb_u0
theorem _root_.«LinearAlgebraicGroups».«Cohomology».«ArithmeticProjectiveFiniteness».«arithmeticProjectiveFiniteness» : _root_.«LinearAlgebraicGroups».«Specs».«ArithmeticProjectiveFiniteness».«Statement».{v8_closure_6ef8d167f9f622bb_u0} :=
  @_root_.«LinearAlgebraicGroups».«Cohomology».«ArithmeticProjectiveFiniteness».«arithmeticProjectiveFiniteness_conditional».{v8_closure_6ef8d167f9f622bb_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«affineCechComparison».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«cechBounded».{v8_closure_6ef8d167f9f622bb_u0, v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«cechDegreeZeroComparison».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«centralCohomologyComparison».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«centralCohomologyIsomorphism».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«centralCohomologyScalarAction».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«centralScalarAction».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«centralSectionComparison».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«centralTranslationOnCohomology».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«eulerCharacteristicBound».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«finiteAffineCover».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«flagCechBaseChange».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«flagCohomologyBaseChange».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«flagCohomologyFinite».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«flagCohomologyRepresentation».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«flagCohomologyZeroBaseChange».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«flagLineSheafIdentification».{v8_closure_6ef8d167f9f622bb_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«FlagCohomology».«flagTranslationCohomologyMap».{v8_closure_6ef8d167f9f622bb_u0})
