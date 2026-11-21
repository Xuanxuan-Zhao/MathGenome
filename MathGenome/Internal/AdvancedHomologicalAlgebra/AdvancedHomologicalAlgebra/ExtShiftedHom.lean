import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.StandardHeart
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.BoundedKModels
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions

/-!
HA-R11. Cohomology classes in the cochain Hom complex become morphisms to
shifts in the homotopy category. Localization is bijective for either supplied
bounded model, and inversion of its augmentation gives the comparison in D.

For modules, the supplied P103 resolution itself is a categorical projective
resolution. The map from its actual cycles to Ext is surjective, with kernel
the actual P103 boundaries. This compares the quotient groups directly;
the signed and unsigned Hom complexes need not be identified. Naturality is
checked on representatives and degree zero uses the original augmentation.
For independently sized carriers, linear maps are transported by the carrier
equivalences. This gives an equivalence on the original P103 quotients and
matches the signed cocycles in the common derived category.
-/

set_option linter.checkUnivs false
set_option maxHeartbeats 800000
universe w v u z v' z' l
open CategoryTheory CategoryTheory.Limits
open CochainComplex HomComplex
open Specs.AdvancedHomologicalAlgebra.StandardHeart
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

namespace AdvancedHomologicalAlgebra.ExtShiftedHom

noncomputable def ext : extType := fun _ _ _ _ => Ext

noncomputable def homologyClass : homologyClassType :=
  fun _ _ _ K L n => HomComplex.homologyAddEquiv K L n

noncomputable def injectiveCoordinates : injectiveCoordinatesType :=
  fun _ _ _ _ _ n => Cochain.fromSingleEquiv (zero_add n)

noncomputable def projectiveCoordinates : projectiveCoordinatesType :=
  fun _ _ _ _ _ n => Cochain.toSingleEquiv (neg_add_cancel n)

theorem zero : zeroType := by
  intro A _ _ _ X Y
  let h : (X ⟶ Y) →+ Ext X Y 0 :=
    { toFun := zeroHom
      map_zero' := by simp [zeroHom]
      map_add' := by intros; simp [zeroHom, Preadditive.add_comp] }
  have hh : Function.Bijective h := by
    let h₁ := (Functor.FullyFaithful.ofFullyFaithful (stalk A)).homEquiv (X := X) (Y := Y)
    let h₂ : ((stalk A).obj X ⟶ (stalk A).obj Y) ≃ Ext X Y 0 := ((shiftFunctorZero (DerivedCategory A) ℤ).symm.app ((stalk A).obj Y)).homToEquiv
    exact h₂.bijective.comp h₁.bijective
  exact ⟨AddEquiv.ofBijective h hh, fun _ => rfl⟩

theorem zero_natural : zeroNaturalType := by
  intro A _ _ _ X X' Y Y' a b f
  simp only [zeroHom, extMap, Functor.map_comp, Category.assoc]
  rw [← NatTrans.naturality]
  simp

theorem negative : negativeType := by
  exact AdvancedHomologicalAlgebra.StandardHeart.negativeHoms

theorem injective_differential : injectiveDifferentialType := by
  intro A _ _ X I n f
  exact Cochain.δ_fromSingleMk f (zero_add n) (n+1) (n+1) (zero_add (n+1))

theorem projective_differential : projectiveDifferentialType := by
  intro A _ _ Y P n f
  exact Cochain.δ_toSingleMk f (neg_add_cancel n) (n+1) (-(n+1))
    (neg_add_cancel (n+1))

section Models
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Conjugating the localization map by its comparison isomorphisms. -/
lemma classToDerived_bijective (K L : CochainComplex A ℤ) (n : ℤ)
    (h : Function.Bijective (_root_.DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient A _).obj K ⟶
        (HomotopyCategory.quotient A _).obj (L⟦n⟧)) → _)) :
    Function.Bijective (classToDerived K L n) := by
  let eK := (_root_.DerivedCategory.quotientCompQhIso A).app K
  let eL := (_root_.DerivedCategory.quotientCompQhIso A).app (L⟦n⟧) ≪≫
    (_root_.DerivedCategory.Q.commShiftIso n).app L
  exact (Iso.homCongr eK eL).bijective.comp
    (h.comp (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).bijective)

noncomputable def classDerivedEquivInjective (K I : CochainComplex A ℤ) (n : ℤ)
    [I.IsKInjective] :
    CohomologyClass K I n ≃+ (_root_.DerivedCategory.Q.obj K ⟶
      (_root_.DerivedCategory.Q.obj I)⟦n⟧) :=
  AddEquiv.ofBijective (classToDerived K I n)
    (classToDerived_bijective K I n
      (CochainComplex.IsKInjective.Qh_map_bijective _ _))

noncomputable def classDerivedEquivProjective (P L : CochainComplex A ℤ) (n : ℤ)
    [P.IsKProjective] :
    CohomologyClass P L n ≃+ (_root_.DerivedCategory.Q.obj P ⟶
      (_root_.DerivedCategory.Q.obj L)⟦n⟧) :=
  AddEquiv.ofBijective (classToDerived P L n)
    (classToDerived_bijective P L n
      (CochainComplex.IsKProjective.Qh_map_bijective _ _))

lemma classToDerived_mk {K L : CochainComplex A ℤ} {n : ℤ} (z : Cocycle K L n) :
    classToDerived K L n (CohomologyClass.mk z) =
      _root_.DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
        (_root_.DerivedCategory.Q.commShiftIso n).hom.app L := by
  simp [classToDerived, CohomologyClass.toHom_mk]

lemma classToDerived_mk_natural {K K' L L' : CochainComplex A ℤ}
    {n : ℤ} (z : Cocycle K L n) (a : K' ⟶ K) (b : L ⟶ L') :
    classToDerived K' L' n (CohomologyClass.mk ((z.precomp a).postcomp b)) =
      _root_.DerivedCategory.Q.map a ≫ classToDerived K L n (CohomologyClass.mk z) ≫
        (CategoryTheory.shiftFunctor _ n).map (_root_.DerivedCategory.Q.map b) := by
  simp only [classToDerived_mk, Cocycle.equivHomShift_symm_postcomp,
    Cocycle.equivHomShift_symm_precomp, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]


/-- A derived morphism with a K-injective target has an actual cochain representative. -/
lemma exists_cochain_map_to_injective (K L : CochainComplex A ℤ) [L.IsKInjective]
    (f : _root_.DerivedCategory.Q.obj K ⟶ _root_.DerivedCategory.Q.obj L) :
    ∃ g : K ⟶ L, _root_.DerivedCategory.Q.map g = f := by
  let eK := (_root_.DerivedCategory.quotientCompQhIso A).app K
  let eL := (_root_.DerivedCategory.quotientCompQhIso A).app L
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A _).obj K) L).surjective (eK.hom ≫ f ≫ eL.inv)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A _).map_surjective g
  refine ⟨g, ?_⟩
  have hh := congrArg (fun t => eK.inv ≫ t ≫ eL.hom) hg
  simpa [eK, eL, Category.assoc] using hh

lemma homotopy_of_map_eq_to_injective {K L : CochainComplex A ℤ} [L.IsKInjective]
    (f g : K ⟶ L) (h : _root_.DerivedCategory.Q.map f = _root_.DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq _ _
    ((CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A _).obj K) L).injective ?_)⟩
  rw [← cancel_mono ((_root_.DerivedCategory.quotientCompQhIso A).hom.app L)]
  simp only [_root_.DerivedCategory.quotientCompQhIso_hom_naturality, h]

/-- Consequently every coefficient map admits the homotopy-commutative lift
used in `injective_natural`; no strict commutativity is required. -/
lemma injective_lift (Y Y' : A) (I J : CochainComplex A ℤ) [J.IsKInjective]
    (ι : (CochainComplex.singleFunctor A 0).obj Y ⟶ I)
    (ι' : (CochainComplex.singleFunctor A 0).obj Y' ⟶ J) [QuasiIso ι]
    (b : Y ⟶ Y') :
    ∃ g : I ⟶ J, Nonempty (Homotopy (ι ≫ g)
      ((CochainComplex.singleFunctor A 0).map b ≫ ι')) := by
  obtain ⟨g, hg⟩ := exists_cochain_map_to_injective I J
    (inv (_root_.DerivedCategory.Q.map ι) ≫
      _root_.DerivedCategory.Q.map ((CochainComplex.singleFunctor A 0).map b) ≫
        _root_.DerivedCategory.Q.map ι')
  refine ⟨g, homotopy_of_map_eq_to_injective _ _ ?_⟩
  simp [Functor.map_comp, hg]

/-- The dual cochain representative statement uses only K-projectivity. -/
lemma exists_cochain_map_from_projective (K L : CochainComplex A ℤ) [K.IsKProjective]
    (f : _root_.DerivedCategory.Q.obj K ⟶ _root_.DerivedCategory.Q.obj L) :
    ∃ g : K ⟶ L, _root_.DerivedCategory.Q.map g = f := by
  let eK := (_root_.DerivedCategory.quotientCompQhIso A).app K
  let eL := (_root_.DerivedCategory.quotientCompQhIso A).app L
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient A _).obj L)).surjective (eK.hom ≫ f ≫ eL.inv)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A _).map_surjective g
  refine ⟨g, ?_⟩
  have hh := congrArg (fun t => eK.inv ≫ t ≫ eL.hom) hg
  simpa [eK, eL, Category.assoc] using hh

lemma homotopy_of_map_eq_from_projective {K L : CochainComplex A ℤ} [K.IsKProjective]
    (f g : K ⟶ L) (h : _root_.DerivedCategory.Q.map f = _root_.DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq _ _
    ((CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient A _).obj L)).injective ?_)⟩
  rw [← cancel_mono ((_root_.DerivedCategory.quotientCompQhIso A).hom.app L)]
  simp only [_root_.DerivedCategory.quotientCompQhIso_hom_naturality, h]

lemma projective_lift (X X' : A) (P P' : CochainComplex A ℤ) [P'.IsKProjective]
    (π : P ⟶ (CochainComplex.singleFunctor A 0).obj X)
    (π' : P' ⟶ (CochainComplex.singleFunctor A 0).obj X') [QuasiIso π]
    (a : X' ⟶ X) :
    ∃ g : P' ⟶ P, Nonempty (Homotopy (g ≫ π)
      (π' ≫ (CochainComplex.singleFunctor A 0).map a)) := by
  obtain ⟨g, hg⟩ := exists_cochain_map_from_projective P' P
    (_root_.DerivedCategory.Q.map π' ≫
      _root_.DerivedCategory.Q.map ((CochainComplex.singleFunctor A 0).map a) ≫
        inv (_root_.DerivedCategory.Q.map π))
  refine ⟨g, homotopy_of_map_eq_from_projective _ _ ?_⟩
  simp [Functor.map_comp, hg]


end Models

theorem injective_comparison : injectiveType := by
  intro A _ _ _ X Y I ι hι hb hinj n
  let := hι
  obtain ⟨b, hb⟩ := hb
  let : I.IsKInjective := (BoundedKModels.kInjective_iff A I).mp
    (BoundedKModels.boundedBelow_injective A I b hb hinj)
  let e₁ := HomComplex.homologyAddEquiv ((CochainComplex.singleFunctor A 0).obj X) I n
  let e₂ := classDerivedEquivInjective ((CochainComplex.singleFunctor A 0).obj X) I n
  let e₃ : (_root_.DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj X) ⟶
      (_root_.DerivedCategory.Q.obj I)⟦n⟧) ≃+ Ext X Y n :=
    { toEquiv := ((CategoryTheory.shiftFunctor _ n).mapIso
        (asIso (_root_.DerivedCategory.Q.map ι))).symm.homToEquiv
      map_add' := by intros; simp [Preadditive.add_comp] }
  refine ⟨e₁.trans (e₂.trans e₃), ?_⟩
  intro x
  change e₃ (e₂ (e₁ (e₁.symm x))) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

theorem projective_comparison : projectiveType := by
  intro A _ _ _ X Y P π hπ hb hproj n
  let := hπ
  obtain ⟨b, hb⟩ := hb
  let : P.IsKProjective := (BoundedKModels.kProjective_iff A P).mp
    (BoundedKModels.boundedAbove_projective A P b hb hproj)
  let e₁ := HomComplex.homologyAddEquiv P ((CochainComplex.singleFunctor A 0).obj Y) n
  let e₂ := classDerivedEquivProjective P ((CochainComplex.singleFunctor A 0).obj Y) n
  let e₃ : (_root_.DerivedCategory.Q.obj P ⟶
      (_root_.DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj Y))⟦n⟧) ≃+ Ext X Y n :=
    { toEquiv := (asIso (_root_.DerivedCategory.Q.map π)).homFromEquiv
      map_add' := by intros; simp [Preadditive.comp_add] }
  refine ⟨e₁.trans (e₂.trans e₃), ?_⟩
  intro x
  change e₃ (e₂ (e₁ (e₁.symm x))) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

theorem injective_natural : injectiveNaturalType := by
  intro A _ _ _ X X' Y Y' I J ι ι' hι hι' a b g hg n z
  let := hι
  let := hι'
  have h : _root_.DerivedCategory.Q.map g ≫ inv (_root_.DerivedCategory.Q.map ι') =
      inv (_root_.DerivedCategory.Q.map ι) ≫ (stalk A).map b := by
    rw [← cancel_epi (_root_.DerivedCategory.Q.map ι)]
    simp only [← Functor.map_comp_assoc]
    rw [_root_.DerivedCategory.Q_map_eq_of_homotopy A hg.some]
    simp [Functor.map_comp]
    rfl
  simp only [injectiveClassMap, extMap, classToDerived_mk_natural, Category.assoc]
  congr 2
  rw [← Functor.map_comp, h, Functor.map_comp]

theorem projective_natural : projectiveNaturalType := by
  intro A _ _ _ X X' Y Y' P P' π π' hπ hπ' a b g hg n z
  let := hπ
  let := hπ'
  have h : inv (_root_.DerivedCategory.Q.map π') ≫ _root_.DerivedCategory.Q.map g =
      (stalk A).map a ≫ inv (_root_.DerivedCategory.Q.map π) := by
    rw [← cancel_mono (_root_.DerivedCategory.Q.map π)]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [_root_.DerivedCategory.Q_map_eq_of_homotopy A hg.some]
    simp [Functor.map_comp]
    rfl
  simp only [projectiveClassMap, extMap, classToDerived_mk_natural, Category.assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rfl

theorem module_differential : moduleDifferentialType := by
  intro R _ C Y n f
  rfl

namespace P103Bridge

open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions

variable {R : Type u} [Ring R] {X : ModuleCat.{max u v} R}

/-- The augmentation of the actual P103 complex, with its terms unchanged. -/
noncomputable def augmentation (P : LeftResolution R X) :
    P.complex ⟶ (ChainComplex.single₀ _).obj X :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom P.ε, by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (P.exact_zero ▸ (LinearMap.mem_range_self (P.complex.d 1 0).hom x) :
      (P.complex.d 1 0).hom x ∈ LinearMap.ker P.ε)⟩

@[simp] lemma augmentation_f_zero (P : LeftResolution R X) :
    (augmentation P).f 0 = ModuleCat.ofHom P.ε := rfl

instance augmentation_quasiIso (P : LeftResolution R X) : QuasiIso (augmentation P) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine ⟨?_, (ModuleCat.epi_iff_surjective _).mpr P.surjective⟩
      exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr P.exact_zero
    · simp
    · rfl
    · simp
      rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _
      (ChainComplex.exactAt_succ_single_obj _ _)]
    rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
    exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr (P.exact_succ n)

/-- The supplied module-projective resolution, as a categorical resolution.
No choice of a replacement resolution is made. -/
noncomputable def resolution (P : LeftResolution R X) (hP : P.IsProjective) :
    ProjectiveResolution X where
  complex := P.complex
  projective n := by
    let := hP n
    infer_instance
  π := augmentation P


lemma cycle_condition (P : LeftResolution R X) (Y : ModuleCat.{max u v} R)
    (n : ℕ) (z : cycles (homComplex P.complex Y) n) :
    z.val.comp (P.complex.d (n+1) n).hom = 0 := by
  have hz := z.property
  change ((homComplex P.complex Y).d n ((ComplexShape.up ℕ).next n)).hom z.val = 0 at hz
  rw [CochainComplex.next] at hz
  exact hz

variable [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

local instance moduleHasExt : HasExt.{w} (ModuleCat.{max u v} R) :=
  hasExt_of_hasDerivedCategory _

/-- An unsigned P103 cocycle gives the same class in the signed cochain Hom
complex: its incoming differential vanishes in either convention. -/
noncomputable def cycleToExt (P : LeftResolution R X) (hP : P.IsProjective)
    (Y : ModuleCat.{max u v} R) (n : ℕ) :
    cycles (homComplex P.complex Y) n →+ Abelian.Ext.{w} X Y n where
  toFun z := (resolution P hP).extMk (ModuleCat.ofHom z.val) (n+1) rfl
    (ModuleCat.hom_ext (cycle_condition P Y n z))
  map_zero' := by apply ProjectiveResolution.extMk_zero
  map_add' z t := ((resolution P hP).add_extMk (ModuleCat.ofHom z.val)
    (ModuleCat.ofHom t.val) (n+1) rfl _ _).symm

lemma cycleToExt_surjective (P : LeftResolution R X) (hP : P.IsProjective)
    (Y : ModuleCat.{max u v} R) (n : ℕ) :
    Function.Surjective (cycleToExt P hP Y n) := by
  intro x
  obtain ⟨f, hf, rfl⟩ := (resolution P hP).extMk_surjective x (n+1) rfl
  refine ⟨⟨f.hom, ?_⟩, rfl⟩
  change ((homComplex P.complex Y).d n ((ComplexShape.up ℕ).next n)).hom f.hom = 0
  rw [CochainComplex.next]
  exact congrArg ModuleCat.Hom.hom hf

/-- Equality of the actual boundary subgroup with the kernel of the class map.
The nonzero scalar sign in cochain Hom is absorbed into its preimage. -/
lemma cycleToExt_kernel_succ (P : LeftResolution R X) (hP : P.IsProjective)
    (Y : ModuleCat.{max u v} R) (n : ℕ) :
    (cycleBoundaries (homComplex P.complex Y) (n+1)).toAddSubgroup =
      (cycleToExt P hP Y (n+1)).ker := by
  ext z
  change (∃ f : (homComplex P.complex Y).X ((ComplexShape.up ℕ).prev (n+1)),
    ((homComplex P.complex Y).d ((ComplexShape.up ℕ).prev (n+1)) (n+1)).hom f = z.val) ↔
      (cycleToExt P hP Y (n+1)) z = 0
  rw [CochainComplex.prev_nat_succ]
  change (∃ f : P.complex.X n →ₗ[R] Y, f.comp (P.complex.d (n+1) n).hom = z.val) ↔
    (resolution P hP).extMk (ModuleCat.ofHom z.val) (n+1+1) rfl
      (ModuleCat.hom_ext (cycle_condition P Y (n+1) z)) = 0
  rw [ProjectiveResolution.extMk_eq_zero_iff _ _ _ _ _ n rfl]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨ModuleCat.ofHom f, ModuleCat.hom_ext hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.hom, congrArg ModuleCat.Hom.hom hf⟩

/-- Direct quotient comparison in positive degrees, on the supplied resolution. -/
noncomputable def quotientExtEquiv (P : LeftResolution R X) (hP : P.IsProjective)
    (Y : ModuleCat.{max u v} R) (n : ℕ) :
    ExtWith P Y (n+1) ≃+ Abelian.Ext.{w} X Y (n+1) :=
  QuotientAddGroup.liftEquiv _ (cycleToExt_surjective P hP Y (n+1))
    (cycleToExt_kernel_succ P hP Y n)

@[simp] lemma quotientExtEquiv_class (P : LeftResolution R X) (hP : P.IsProjective)
    (Y : ModuleCat.{max u v} R) (n : ℕ) (z : cycles (homComplex P.complex Y) (n+1)) :
    quotientExtEquiv P hP Y n (P103.Specs.Ch10.Complexes.homologyClass _ _ z) = cycleToExt P hP Y (n+1) z := rfl

/-- The zero-degree comparison comes directly from the actual augmentation. -/
noncomputable def zeroEquiv (P : LeftResolution R X) (Y : ModuleCat.{max u v} R) :
    ExtWith P Y 0 ≃+ Ext X Y 0 :=
  (P103.Ch11.ExtTorDefinitions.extZero P Y).trans
    (ModuleCat.homAddEquiv.symm.trans (Classical.choose (zero _ X Y)))

/-- The family of comparisons uses P103's actual quotient groups in every degree. -/
noncomputable def moduleEquiv (P : LeftResolution R X) (hP : P.IsProjective)
    (Y : ModuleCat.{max u v} R) : ∀ n : ℕ, ExtWith P Y n ≃+ Ext X Y (n : ℤ)
  | 0 => zeroEquiv P Y
  | n+1 => (quotientExtEquiv P hP Y n).trans Abelian.Ext.homAddEquiv

lemma zeroEquiv_apply (X Y : ModuleCat.{max u v} R)
    (P : LeftResolution R X) (x : ExtWith P Y 0) :
    zeroEquiv P Y x =
      zeroHom (ModuleCat.ofHom (P103.Ch11.ExtTorDefinitions.extZero P Y x)) := by
  exact Classical.choose_spec (zero _ X Y) _

lemma zeroEquiv_natural (X X' Y Y' : ModuleCat.{max u v} R)
    (P : LeftResolution R X) (P' : LeftResolution R X')
    (a : X' ⟶ X) (b : Y ⟶ Y') (g : P'.complex ⟶ P.complex)
    (hg : ChainLift P' P a.hom g) (x : ExtWith P Y 0) :
    zeroEquiv P' Y'
      (homologyMap (homPreMap g Y ≫ homPostMap P'.complex b.hom) 0 x) =
    extMap a b 0 (zeroEquiv P Y x) := by
  rw [zeroEquiv_apply, zeroEquiv_apply]
  rw [P103.Ch11.ExtTorDefinitions.ext_zero_natural R X X' P P' Y Y' a.hom b.hom g hg
    (P103.Ch11.ExtTorDefinitions.extZero P Y) (P103.Ch11.ExtTorDefinitions.extZero P' Y')
    (P103.Ch11.ExtTorDefinitions.extZero_class P Y)
    (P103.Ch11.ExtTorDefinitions.extZero_class P' Y') x]
  exact zero_natural _ X X' Y Y' a b _

lemma zeroEquiv_class (X Y : ModuleCat.{max u v} R)
    (P : LeftResolution R X) (z : cycles (homComplex P.complex Y) 0) (f : X ⟶ Y)
    (hf : f.hom.comp P.ε = z.val) :
    zeroEquiv P Y (P103.Specs.Ch10.Complexes.homologyClass _ 0 z) = zeroHom f := by
  rw [zeroEquiv_apply]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  obtain ⟨s, rfl⟩ := P.surjective t
  have h := P103.Ch11.ExtTorDefinitions.extZero_class P Y z
  exact LinearMap.congr_fun (h.trans hf.symm) s

/-- An augmented P103 lift is a morphism of the same categorical resolutions. -/
noncomputable def resolutionHom (X X' : ModuleCat.{max u v} R)
    (P : LeftResolution R X) (P' : LeftResolution R X')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (a : X' ⟶ X) (g : P'.complex ⟶ P.complex)
    (hg : ChainLift P' P a.hom g) :
    ProjectiveResolution.Hom (resolution P' hP') (resolution P hP) a where
  hom := g
  hom_f_zero_comp_π_f_zero := by
    apply ModuleCat.hom_ext
    exact hg

lemma cycleToExt_natural (X X' Y Y' : ModuleCat.{max u v} R)
    (P : LeftResolution R X) (P' : LeftResolution R X')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (a : X' ⟶ X) (b : Y ⟶ Y') (g : P'.complex ⟶ P.complex)
    (hg : ChainLift P' P a.hom g) (n : ℕ) (z : cycles (homComplex P.complex Y) n) :
    cycleToExt P' hP' Y' n
      (cyclesMap (homPreMap g Y ≫ homPostMap P'.complex b.hom) n z) =
      ((Abelian.Ext.mk₀ a).comp (cycleToExt P hP Y n z) (zero_add n)).comp
        (Abelian.Ext.mk₀ b) (add_zero n) := by
  symm
  change ((Abelian.Ext.mk₀ a).comp
    ((resolution P hP).extMk (ModuleCat.ofHom z.val) (n+1) rfl
      (ModuleCat.hom_ext (cycle_condition P Y n z))) (zero_add n)).comp
    (Abelian.Ext.mk₀ b) (add_zero n) = _
  rw [ProjectiveResolution.mk₀_comp_extMk _ _ _ _ (resolutionHom X X' P P' hP hP' a g hg)]
  rw [ProjectiveResolution.extMk_comp_mk₀]
  rfl

lemma quotientExtEquiv_natural (X X' Y Y' : ModuleCat.{max u v} R)
    (P : LeftResolution R X) (P' : LeftResolution R X')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (a : X' ⟶ X) (b : Y ⟶ Y') (g : P'.complex ⟶ P.complex)
    (hg : ChainLift P' P a.hom g) (n : ℕ) (x : ExtWith P Y (n+1)) :
    quotientExtEquiv P' hP' Y' n
      (homologyMap (homPreMap g Y ≫ homPostMap P'.complex b.hom) (n+1) x) =
      ((Abelian.Ext.mk₀ a).comp (quotientExtEquiv P hP Y n x) (zero_add (n+1))).comp
        (Abelian.Ext.mk₀ b) (add_zero (n+1)) := by
  obtain ⟨z, rfl⟩ := (cycleBoundaries (homComplex P.complex Y) (n+1)).mkQ_surjective x
  exact cycleToExt_natural X X' Y Y' P P' hP hP' a b g hg (n+1) z

lemma moduleEquiv_natural (X X' Y Y' : ModuleCat.{max u v} R)
    (P : LeftResolution R X) (P' : LeftResolution R X')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (a : X' ⟶ X) (b : Y ⟶ Y') (g : P'.complex ⟶ P.complex)
    (hg : ChainLift P' P a.hom g) (n : ℕ) (x : ExtWith P Y n) :
    moduleEquiv P' hP' Y' n
      (homologyMap (homPreMap g Y ≫ homPostMap P'.complex b.hom) n x) =
      extMap a b (n : ℤ) (moduleEquiv P hP Y n x) := by
  cases n with
  | zero => exact zeroEquiv_natural X X' Y Y' P P' a b g hg x
  | succ n =>
    change Abelian.Ext.homAddEquiv (quotientExtEquiv P' hP' Y' n
      (homologyMap (homPreMap g Y ≫ homPostMap P'.complex b.hom) (n+1) x)) =
        extMap a b ((n+1 : ℕ) : ℤ) (Abelian.Ext.homAddEquiv (quotientExtEquiv P hP Y n x))
    rw [quotientExtEquiv_natural X X' Y Y' P P' hP hP' a b g hg n x]
    simp only [Abelian.Ext.homAddEquiv_apply, Abelian.Ext.comp_hom,
      Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
      extMap, Category.assoc]


end P103Bridge

theorem module_comparison : moduleType := by
  intro R _ _
  refine ⟨{
    equiv := fun X Y P hP n => P103Bridge.moduleEquiv P hP Y n
    natural := fun X X' Y Y' P P' hP hP' a b g hg n x =>
      P103Bridge.moduleEquiv_natural X X' Y Y' P P' hP hP' a b g hg n x
    zero := fun X Y P _ z f hf => P103Bridge.zeroEquiv_class X Y P z f hf
  }⟩

namespace LiftedP103

open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions



private abbrev originalHom {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) := homComplex P.complex Y
private abbrev ambientHom.{U,V,Z,L} {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) :=
  homComplex (liftedChain.{U,V,Z,L} R P) ((secondLift.{U,V,Z,L} R).obj Y)

/-- The cochain map given by conjugating linear maps by the carrier equivalences. -/
def liftCochainEquiv.{U,V,Z,L} {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ) :
    (originalHom P Y).X n ≃+ (ambientHom.{U,V,Z,L} P Y).X n :=
  LinearEquiv.arrowCongrAddEquiv ULift.moduleEquiv.symm ULift.moduleEquiv.symm

@[simp] lemma liftCochainEquiv_apply.{U,V,Z,L} {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ) (f : (originalHom P Y).X n) :
    liftCochainEquiv.{U,V,Z,L} P Y n f = (liftCochain.{U,V,Z,L} R P Y n f).hom := by
  apply LinearMap.ext
  intro t
  rfl

private lemma liftCochainEquiv_d.{U,V,Z,L} {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (i j : ℕ) (f : (originalHom P Y).X i) :
    liftCochainEquiv.{U,V,Z,L} P Y j (((originalHom P Y).d i j).hom f) =
      ((ambientHom.{U,V,Z,L} P Y).d i j).hom (liftCochainEquiv.{U,V,Z,L} P Y i f) := by
  apply LinearMap.ext
  intro t
  rfl

theorem liftCochain_bijective.{U,V,Z,L} {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ) :
    Function.Bijective (liftCochain.{U,V,Z,L} R P Y n) := by
  let e : (P.complex.X n →ₗ[R] Y) ≃+
      ((termLift.{U,V,Z,L} R).obj (P.complex.X n) ⟶ (secondLift.{U,V,Z,L} R).obj Y) :=
    (liftCochainEquiv.{U,V,Z,L} P Y n).trans ModuleCat.homAddEquiv.symm
  exact e.bijective

theorem liftCochain_d.{U,V,Z,L} {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ) (f : P.complex.X n →ₗ[R] Y) :
    liftCochain.{U,V,Z,L} R P Y (n+1) (((homComplex P.complex Y).d n (n+1)).hom f) =
      (termLift.{U,V,Z,L} R).map (P.complex.d (n+1) n) ≫
        liftCochain.{U,V,Z,L} R P Y n f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rfl

private lemma liftCochain_mem_cycles.{U,V,Z,L} {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ) (f : (originalHom P Y).X n) :
    liftCochainEquiv.{U,V,Z,L} P Y n f ∈ cycles (ambientHom.{U,V,Z,L} P Y) n ↔
      f ∈ cycles (originalHom P Y) n := by
  let j := (ComplexShape.up ℕ).next n
  change ((ambientHom.{U,V,Z,L} P Y).d n j).hom _ = 0 ↔
    ((originalHom P Y).d n j).hom _ = 0
  rw [← liftCochainEquiv_d, ← (liftCochainEquiv.{U,V,Z,L} P Y j).map_zero]
  exact (liftCochainEquiv.{U,V,Z,L} P Y j).injective.eq_iff

/-- Restrict transport on cochains to the kernels of the differentials. -/
def liftCyclesEquiv.{U,V,Z,L} {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ) :
    cycles (originalHom P Y) n ≃+ cycles (ambientHom.{U,V,Z,L} P Y) n where
  toEquiv := (liftCochainEquiv.{U,V,Z,L} P Y n).toEquiv.subtypeEquiv
    (fun f => (liftCochain_mem_cycles.{U,V,Z,L} P Y n f).symm)
  map_add' x y := Subtype.ext ((liftCochainEquiv.{U,V,Z,L} P Y n).map_add x.val y.val)

abbrev liftCycle.{U,V,Z,L} (R : Type U) [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ)
    (x : cycles (originalHom P Y) n) : cycles (ambientHom.{U,V,Z,L} P Y) n :=
  liftCyclesEquiv.{U,V,Z,L} P Y n x

@[simp] lemma liftCycle_val.{U,V,Z,L} (R : Type U) [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ)
    (x : cycles (originalHom P Y) n) :
    (liftCycle.{U,V,Z,L} R P Y n x).val = (liftCochain.{U,V,Z,L} R P Y n x.val).hom :=
  liftCochainEquiv_apply P Y n x.val

private lemma liftCycle_mem_boundaries.{U,V,Z,L} {R : Type U} [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ) (x : cycles (originalHom P Y) n) :
    liftCycle.{U,V,Z,L} R P Y n x ∈ cycleBoundaries (ambientHom.{U,V,Z,L} P Y) n ↔
      x ∈ cycleBoundaries (originalHom P Y) n := by
  let i := (ComplexShape.up ℕ).prev n
  let e := liftCochainEquiv.{U,V,Z,L} P Y n
  change (∃ f : (ambientHom.{U,V,Z,L} P Y).X i,
    ((ambientHom.{U,V,Z,L} P Y).d i n).hom f = e x.val) ↔
    ∃ f : (originalHom P Y).X i, ((originalHom P Y).d i n).hom f = x.val
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨g, rfl⟩ := (liftCochainEquiv.{U,V,Z,L} P Y i).surjective f
    rw [← liftCochainEquiv_d] at hf
    exact ⟨g, e.injective hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨liftCochainEquiv.{U,V,Z,L} P Y i f, (liftCochainEquiv_d P Y i n f).symm.trans
      (congrArg e hf)⟩

/-- Carrier transport on the original P103 quotient of cycles by boundaries. -/
noncomputable def liftExtEquiv.{U,V,Z,L} (R : Type U) [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ) :
    ExtWith P Y n ≃+ Homology (ambientHom.{U,V,Z,L} P Y) n :=
  QuotientAddGroup.congr _ _ (liftCyclesEquiv.{U,V,Z,L} P Y n) (by
    ext y
    obtain ⟨x, rfl⟩ := (liftCyclesEquiv.{U,V,Z,L} P Y n).surjective y
    constructor
    · rintro ⟨x', hx', h⟩
      have : x' = x := (liftCyclesEquiv.{U,V,Z,L} P Y n).injective h
      subst x'
      exact (liftCycle_mem_boundaries P Y n x).mpr hx'
    · intro hx
      exact ⟨x, (liftCycle_mem_boundaries P Y n x).mp hx, rfl⟩)

@[simp] lemma liftExtEquiv_class.{U,V,Z,L} (R : Type U) [Ring R] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (Y : ModuleCat.{Z} R) (n : ℕ)
    (x : cycles (originalHom P Y) n) :
    liftExtEquiv.{U,V,Z,L} R P Y n (P103.Specs.Ch10.Complexes.homologyClass _ n x) =
      P103.Specs.Ch10.Complexes.homologyClass _ n (liftCycle.{U,V,Z,L} R P Y n x) := rfl

end LiftedP103

theorem lifted_module_cochains : liftedCochainsType := by
  intro R _ X P Y
  exact ⟨LiftedP103.liftCochain_bijective P Y, LiftedP103.liftCochain_d P Y⟩

namespace LiftedP103

open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes

universe a b c

private lemma liftLinearMap_range_eq_ker
    {R : Type*} [Ring R] {A : Type*} {B : Type*} {C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range (liftLinearMap f : ULift.{a} A →ₗ[R] ULift.{b} B) =
      LinearMap.ker (liftLinearMap g : ULift.{b} B →ₗ[R] ULift.{c} C) := by
  ext ⟨x⟩
  change (∃ y : ULift.{a} A, ULift.up (f y.down) = ULift.up x) ↔ ULift.up (g x) = 0
  constructor
  · rintro ⟨y, hy⟩
    have hx : x ∈ LinearMap.range f := ⟨y.down, congrArg ULift.down hy⟩
    have hx' : x ∈ LinearMap.ker g := h ▸ hx
    exact congrArg ULift.up hx'
  · intro hx
    have hx' : x ∈ LinearMap.ker g := congrArg ULift.down hx
    obtain ⟨y, hy⟩ := h.symm ▸ hx'
    exact ⟨ULift.up y, congrArg ULift.up hy⟩

/-- The given augmented resolution after applying the carrier lifts over the same ring. -/
noncomputable def leftResolution.{U,V,Z,L} (R : Type U) [Ring R]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) :
    LeftResolution R ((firstLift.{U,V,Z,L} R).obj X) where
  complex := liftedChain.{U,V,Z,L} R P
  ε := (liftAugmentation.{U,V,Z,L} R P).hom
  surjective := by
    rintro ⟨x⟩
    obtain ⟨y, rfl⟩ := P.surjective x
    exact ⟨ULift.up y, rfl⟩
  exact_zero := liftLinearMap_range_eq_ker _ _ P.exact_zero
  exact_succ n := liftLinearMap_range_eq_ker _ _ (P.exact_succ n)

lemma leftResolution_isProjective.{U,V,Z,L} (R : Type U) [Ring R]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) (hP : P.IsProjective) :
    (leftResolution.{U,V,Z,L} R P).IsProjective := by
  intro n
  let := hP n
  exact Module.Projective.of_equiv' ULift.moduleEquiv.symm

noncomputable def resolution.{U,V,Z,L} (R : Type U) [Ring R]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) (hP : P.IsProjective) :
    ProjectiveResolution ((firstLift.{U,V,Z,L} R).obj X) :=
  P103Bridge.resolution.{max V Z L,U} (leftResolution.{U,V,Z,L} R P)
    (leftResolution_isProjective.{U,V,Z,L} R P hP)

@[simp] lemma resolution_π_f_zero.{U,V,Z,L} (R : Type U) [Ring R]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) (hP : P.IsProjective) :
    (resolution.{U,V,Z,L} R P hP).π.f 0 = liftAugmentation.{U,V,Z,L} R P := rfl

lemma chainLift_map.{U,V,Z,L} (R : Type U) [Ring R]
    {X X' : ModuleCat.{V} R} (P : LeftResolution R X) (P' : LeftResolution R X')
    (a : X' ⟶ X) (g : P'.complex ⟶ P.complex) (hg : ChainLift P' P a.hom g) :
    ChainLift (leftResolution.{U,V,Z,L} R P') (leftResolution.{U,V,Z,L} R P)
      ((firstLift.{U,V,Z,L} R).map a).hom
      (((termLift.{U,V,Z,L} R).mapHomologicalComplex (.down ℕ)).map g) := by
  apply LinearMap.ext
  rintro ⟨s⟩
  exact congrArg ULift.up (LinearMap.congr_fun hg s)

lemma embeddingUpIntLE_zero_eq_embeddingDownNat :
    ComplexShape.embeddingUpIntLE 0 = ComplexShape.embeddingDownNat := by
  have h : (ComplexShape.embeddingUpIntLE 0).f = ComplexShape.embeddingDownNat.f := by
    funext n
    change 0 - (n : ℤ) = -(n : ℤ)
    simp
  generalize ComplexShape.embeddingUpIntLE 0 = e at h ⊢
  generalize ComplexShape.embeddingDownNat = e' at h ⊢
  cases e
  cases e'
  cases h
  rfl

/-- The augmentation on the extension along an embedding with index map `n ↦ -n`. -/
noncomputable def extendedAugmentation {C : Type*} [Category C] [Abelian C]
    {X : C} (Q : ProjectiveResolution X)
    (e : ComplexShape.Embedding (.down ℕ) (.up ℤ)) (he : e = ComplexShape.embeddingDownNat) :
    Q.complex.extend e ⟶ (CochainComplex.singleFunctor C 0).obj X := by
  subst e
  exact Q.π'

lemma extendedAugmentation_quasiIso {C : Type*} [Category C] [Abelian C]
    {X : C} (Q : ProjectiveResolution X)
    (e : ComplexShape.Embedding (.down ℕ) (.up ℤ)) (he : e = ComplexShape.embeddingDownNat) :
    QuasiIso (extendedAugmentation Q e he) := by
  subst e
  change QuasiIso Q.π'
  infer_instance

lemma extendedAugmentation_f_zero {C : Type*} [Category C] [Abelian C]
    {X : C} (Q : ProjectiveResolution X)
    (e : ComplexShape.Embedding (.down ℕ) (.up ℤ)) (he : e = ComplexShape.embeddingDownNat)
    (h : e.f 0 = 0) :
    (extendedAugmentation Q e he).f 0 ≫
      (HomologicalComplex.singleObjXSelf (c := .up ℤ) 0 X).hom =
      (Q.complex.extendXIso e h).hom ≫ Q.π.f 0 := by
  subst e
  change Q.π'.f 0 ≫ _ = _
  rw [ProjectiveResolution.π'_f_zero]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end LiftedP103

universe t

section ProjectiveCocycles
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] [HasExt.{t} A] {X Y : A}

lemma projectiveExtClass_mk (Q : ProjectiveResolution X) (n : ℕ)
    (z : Cocycle Q.cochainComplex ((singleFunctor A 0).obj Y) (n : ℤ)) :
    (Q.extEquivCohomologyClass.symm (.mk z)).hom =
      projectiveClassMap X Y Q.cochainComplex Q.π' inferInstance (n : ℤ) (.mk z) := by
  rw [Q.extEquivCohomologyClass_symm_mk_hom, projectiveClassMap, classToDerived_mk]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, ShiftedHom.mk₀_comp]
  congr 1
  exact ShiftedHom.comp_mk₀_id _ (0 : ℤ) rfl

lemma projectiveExtMk_hom_eq_class (Q : ProjectiveResolution X) (n : ℕ)
    (f : Q.complex.X n ⟶ Y) (hf : Q.complex.d (n+1) n ≫ f = 0) :
    ∃ z : Cocycle Q.cochainComplex ((singleFunctor A 0).obj Y) (n : ℤ),
      z.val = Cochain.toSingleMk ((Q.cochainComplexXIso (-(n : ℤ)) n rfl).hom ≫ f)
        (neg_add_cancel (n : ℤ)) ∧
      (Q.extMk f (n+1) rfl hf).hom =
        projectiveClassMap X Y Q.cochainComplex Q.π' inferInstance (n : ℤ) (.mk z) := by
  let z := Cocycle.toSingleMk ((Q.cochainComplexXIso (-(n : ℤ)) n rfl).hom ≫ f)
    (neg_add_cancel (n : ℤ)) (-((n+1 : ℕ) : ℤ)) (by lia)
    (by simp only [Q.cochainComplex_d _ _ (n+1) n rfl rfl, Category.assoc,
      Iso.inv_hom_id_assoc, hf, comp_zero])
  exact ⟨z, rfl, projectiveExtClass_mk Q n z⟩

lemma projectiveExtMk_hom_eq_extended_class (Q : ProjectiveResolution X)
    (e : ComplexShape.Embedding (.down ℕ) (.up ℤ)) (he : e = ComplexShape.embeddingDownNat)
    (n : ℕ) (hi : e.f n = -(n : ℤ))
    (f : Q.complex.X n ⟶ Y) (hf : Q.complex.d (n + 1) n ≫ f = 0) :
    ∃ z : Cocycle (Q.complex.extend e) ((singleFunctor A 0).obj Y) (n : ℤ),
      z.val = Cochain.toSingleMk ((Q.complex.extendXIso e hi).hom ≫ f)
        (neg_add_cancel (n : ℤ)) ∧
      (Q.extMk f (n + 1) rfl hf).hom =
        projectiveClassMap X Y _ (LiftedP103.extendedAugmentation Q e he)
          (LiftedP103.extendedAugmentation_quasiIso Q e he) (n : ℤ) (.mk z) := by
  subst e
  exact projectiveExtMk_hom_eq_class Q n f hf

set_option backward.isDefEq.respectTransparency false in
lemma projectiveExtMk_zero_hom (Q : ProjectiveResolution X) (f : X ⟶ Y)
    (hf : Q.complex.d 1 0 ≫ Q.π.f 0 ≫ f = 0) :
    (Q.extMk (Q.π.f 0 ≫ f) 1 rfl hf).hom = zeroHom f := by
  obtain ⟨z, hz, hm⟩ := projectiveExtMk_hom_eq_class Q 0 (Q.π.f 0 ≫ f) hf
  rw [hm, projectiveClassMap, classToDerived_mk]
  have hz' : z = Cocycle.ofHom (Q.π' ≫ (singleFunctor A 0).map f) := by
    apply Subtype.ext
    rw [hz]
    apply (Cochain.toSingleEquiv (neg_add_cancel (0 : ℤ))).injective
    rw [Cochain.toSingleEquiv_toSingleMk]
    simp only [Cochain.toSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, Cocycle.ofHom_coe]
    change _ = (Cochain.ofHom (Q.π' ≫ (singleFunctor A 0).map f)).v
        0 0 (add_zero 0) ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom
    erw [Cochain.ofHom_v, HomologicalComplex.comp_f, Q.π'_f_zero,
      Category.assoc, Category.assoc, Category.assoc]
    change (Q.cochainComplexXIso 0 0 rfl).hom ≫ Q.π.f 0 ≫ f =
      (Q.cochainComplexXIso 0 0 rfl).hom ≫ Q.π.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫
          ((HomologicalComplex.single A (.up ℤ) 0).map f).f 0 ≫
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom
    rw [HomologicalComplex.single_map_f_self]
    simp [Category.assoc]
  rw [hz']
  have hshift (g : Q.cochainComplex ⟶ (singleFunctor A 0).obj Y) :
      Cocycle.equivHomShift.symm (Cocycle.ofHom g) = ShiftedHom.mk₀ 0 rfl g := by
    ext i
    simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f, Cochain.rightShift_v,
      ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f,
      CochainComplex.shiftFunctorObjXIso]
    rfl
  change inv (DerivedCategory.Q.map Q.π') ≫ ShiftedHom.map
    (Cocycle.equivHomShift.symm (Cocycle.ofHom (Q.π' ≫ (singleFunctor A 0).map f)))
    DerivedCategory.Q = _
  rw [hshift]
  rw [ShiftedHom.map_mk₀]
  simp [ShiftedHom.mk₀, Functor.map_comp, zeroHom, Category.assoc,
    CategoryTheory.shiftFunctorZero']
  rfl

end ProjectiveCocycles

namespace P103Bridge
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions

variable {R : Type u} [Ring R] {X : ModuleCat.{max u v} R}
  [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

local instance : HasExt.{w} (ModuleCat.{max u v} R) := hasExt_of_hasDerivedCategory _

lemma moduleEquiv_class_hom (P : LeftResolution R X) (hP : P.IsProjective)
    (Y : ModuleCat.{max u v} R) (n : ℕ) (x : cycles (homComplex P.complex Y) n) :
    moduleEquiv P hP Y n (P103.Specs.Ch10.Complexes.homologyClass _ n x) =
      (cycleToExt P hP Y n x).hom := by
  cases n with
  | succ n => rfl
  | zero =>
    let f : X ⟶ Y := ModuleCat.ofHom (P103.Ch11.ExtTorDefinitions.extZero P Y
      (P103.Specs.Ch10.Complexes.homologyClass _ 0 x))
    have hfx : f.hom.comp P.ε = x.val := P103.Ch11.ExtTorDefinitions.extZero_class P Y x
    have hx : (resolution P hP).π.f 0 ≫ f = ModuleCat.ofHom x.val :=
      ModuleCat.hom_ext hfx
    have hzero : (resolution P hP).complex.d 1 0 ≫ (resolution P hP).π.f 0 ≫ f = 0 := by
      rw [hx]
      exact ModuleCat.hom_ext (cycle_condition P Y 0 x)
    change zeroEquiv P Y _ = ((resolution P hP).extMk (ModuleCat.ofHom x.val) 1 rfl
      (ModuleCat.hom_ext (cycle_condition P Y 0 x))).hom
    rw [zeroEquiv_class X Y P x f hfx]
    have hz := projectiveExtMk_zero_hom (resolution P hP) f hzero
    let Q := resolution P hP
    let g : {z : Q.complex.X 0 ⟶ Y // Q.complex.d 1 0 ≫ z = 0} → Ext X Y 0 :=
      fun z => (Q.extMk z.val 1 rfl z.property).hom
    have heq : (⟨Q.π.f 0 ≫ f, hzero⟩ : {z : Q.complex.X 0 ⟶ Y //
        Q.complex.d 1 0 ≫ z = 0}) = ⟨ModuleCat.ofHom x.val,
        ModuleCat.hom_ext (cycle_condition P Y 0 x)⟩ := Subtype.ext hx
    change g ⟨Q.π.f 0 ≫ f, hzero⟩ = _ at hz
    change _ = g ⟨ModuleCat.ofHom x.val, ModuleCat.hom_ext (cycle_condition P Y 0 x)⟩
    rw [← heq]
    exact hz.symm

end P103Bridge

namespace LiftedP103

open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions

/-- Rescale the unsigned resolution model to the signed cochain convention. -/
def resolutionSign (n : ℕ) : ℤ := (-1) ^ (n * (n + 1) / 2)

private def resolutionSignEquiv (n : ℕ) (G : Type*) [AddCommGroup G] : G ≃+ G :=
  DistribMulAction.toAddEquiv G ((-1 : ℤˣ) ^ (n * (n + 1) / 2))

private lemma resolutionSignEquiv_apply (n : ℕ) {G : Type*} [AddCommGroup G] (x : G) :
    resolutionSignEquiv n G x = resolutionSign n • x := by
  simp [resolutionSignEquiv, resolutionSign, Units.smul_def]

lemma extMap_zsmul {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {X X' Y Y' : A} (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℤ) (m : ℤ) (e : Ext X Y n) :
    extMap a b n (m • e) = m • extMap a b n e := by
  simp only [extMap, Preadditive.comp_zsmul, Preadditive.zsmul_comp]

noncomputable def signedModuleEquiv.{U,V,Z,L,W} (R : Type U) [Ring R]
    [HasDerivedCategory.{W} (ModuleCat.{max U V Z L} R)] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (hP : P.IsProjective) (Y : ModuleCat.{Z} R) (n : ℕ) :
    ExtWith P Y n ≃+
      Ext ((firstLift.{U,V,Z,L} R).obj X) ((secondLift.{U,V,Z,L} R).obj Y) (n : ℤ) :=
  ((liftExtEquiv.{U,V,Z,L} R P Y n).trans
    (P103Bridge.moduleEquiv.{W,max V Z L,U} (leftResolution.{U,V,Z,L} R P)
      (leftResolution_isProjective.{U,V,Z,L} R P hP) ((secondLift.{U,V,Z,L} R).obj Y) n)).trans
    (resolutionSignEquiv n _)

lemma signedModuleEquiv_apply.{U,V,Z,L,W} (R : Type U) [Ring R]
    [HasDerivedCategory.{W} (ModuleCat.{max U V Z L} R)] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (hP : P.IsProjective) (Y : ModuleCat.{Z} R) (n : ℕ)
    (x : ExtWith P Y n) :
    signedModuleEquiv.{U,V,Z,L,W} R P hP Y n x = resolutionSign n •
      P103Bridge.moduleEquiv.{W,max V Z L,U} (leftResolution.{U,V,Z,L} R P)
        (leftResolution_isProjective.{U,V,Z,L} R P hP) ((secondLift.{U,V,Z,L} R).obj Y) n
        (liftExtEquiv.{U,V,Z,L} R P Y n x) :=
  resolutionSignEquiv_apply _ _

lemma signedModuleEquiv_zero.{U,V,Z,L,W} (R : Type U) [Ring R]
    [HasDerivedCategory.{W} (ModuleCat.{max U V Z L} R)] {X : ModuleCat.{V} R}
    (P : LeftResolution R X) (hP : P.IsProjective) (Y : ModuleCat.{Z} R)
    (x : cycles (homComplex P.complex Y) 0) (f : X →ₗ[R] Y)
    (hf : f.comp P.ε = x.val) :
    signedModuleEquiv.{U,V,Z,L,W} R P hP Y 0 (P103.Specs.Ch10.Complexes.homologyClass _ 0 x) =
      zeroHom (ModuleCat.ofHom (liftLinearMap f)) := by
  rw [signedModuleEquiv_apply, liftExtEquiv_class]
  simp only [resolutionSign, Nat.zero_mul, Nat.zero_div, pow_zero, one_smul]
  apply P103Bridge.zeroEquiv_class.{W,max V Z L,U}
  apply LinearMap.ext
  intro t
  exact congrArg ULift.up (LinearMap.congr_fun hf t.down)

end LiftedP103

namespace LiftedP103

open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions

lemma signedModuleEquiv_natural.{U,V,Z,L,W} (R : Type U) [Ring R]
    [HasDerivedCategory.{W} (ModuleCat.{max U V Z L} R)]
    (X X' : ModuleCat.{V} R) (Y Y' : ModuleCat.{Z} R)
    (P : LeftResolution R X) (P' : LeftResolution R X')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (a : X' ⟶ X) (b : Y ⟶ Y') (g : P'.complex ⟶ P.complex)
    (hg : ChainLift P' P a.hom g) (n : ℕ) (x : ExtWith P Y n) :
    signedModuleEquiv.{U,V,Z,L,W} R P' hP' Y' n
      (homologyMap (homPreMap g Y ≫ homPostMap P'.complex b.hom) n x) =
      extMap ((firstLift.{U,V,Z,L} R).map a) ((secondLift.{U,V,Z,L} R).map b) (n : ℤ)
        (signedModuleEquiv.{U,V,Z,L,W} R P hP Y n x) := by
  let P₁ := leftResolution.{U,V,Z,L} R P
  let P₂ := leftResolution.{U,V,Z,L} R P'
  let Y₁ := (secondLift.{U,V,Z,L} R).obj Y
  let Y₂ := (secondLift.{U,V,Z,L} R).obj Y'
  let a₁ := (firstLift.{U,V,Z,L} R).map a
  let b₁ := (secondLift.{U,V,Z,L} R).map b
  let g₁ := ((termLift.{U,V,Z,L} R).mapHomologicalComplex (.down ℕ)).map g
  have hg₁ : ChainLift P₂ P₁ a₁.hom g₁ := chainLift_map.{U,V,Z,L} R P P' a g hg
  have h := P103Bridge.moduleEquiv_natural.{W,max V Z L,U} _ _ Y₁ Y₂ P₁ P₂
    (leftResolution_isProjective.{U,V,Z,L} R P hP)
    (leftResolution_isProjective.{U,V,Z,L} R P' hP') a₁ b₁ g₁ hg₁ n
    (liftExtEquiv.{U,V,Z,L} R P Y n x)
  rw [signedModuleEquiv_apply, signedModuleEquiv_apply, extMap_zsmul, ← h]
  congr 2
  obtain ⟨c, rfl⟩ := (cycleBoundaries (homComplex P.complex Y) n).mkQ_surjective x
  change liftExtEquiv.{U,V,Z,L} R P' Y' n
      (P103.Specs.Ch10.Complexes.homologyClass _ n
        (cyclesMap (homPreMap g Y ≫ homPostMap P'.complex b.hom) n c)) =
    homologyMap (homPreMap g₁ Y₁ ≫ homPostMap P₂.complex b₁.hom) n
      (liftExtEquiv.{U,V,Z,L} R P Y n (P103.Specs.Ch10.Complexes.homologyClass _ n c))
  rw [liftExtEquiv_class, liftExtEquiv_class]
  change P103.Specs.Ch10.Complexes.homologyClass _ n _ =
    P103.Specs.Ch10.Complexes.homologyClass _ n
      (cyclesMap (homPreMap g₁ Y₁ ≫ homPostMap P₂.complex b₁.hom) n
        (liftCycle.{U,V,Z,L} R P Y n c))
  apply congrArg (P103.Specs.Ch10.Complexes.homologyClass _ n)
  apply Subtype.ext
  apply LinearMap.ext
  intro t
  rfl

end LiftedP103

namespace LiftedP103

open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions

local instance liftedModuleHasExt.{U,V,W} {R : Type U} [Ring R]
    [HasDerivedCategory.{W} (ModuleCat.{V} R)] : HasExt.{W} (ModuleCat.{V} R) :=
  hasExt_of_hasDerivedCategory _

set_option backward.isDefEq.respectTransparency false in
private lemma signedModuleEquiv_class.{U,V,Z,L,W} (R : Type U) [Ring R]
    [HasDerivedCategory.{W} (ModuleCat.{max U V Z L} R)]
    {X : ModuleCat.{V} R} (P : LeftResolution R X) (hP : P.IsProjective)
    (Y : ModuleCat.{Z} R) (n : ℕ) (x : cycles (homComplex P.complex Y) n) :
    let Q := resolution.{U,V,Z,L} R P hP
    let e := ComplexShape.embeddingUpIntLE 0
    let he := embeddingUpIntLE_zero_eq_embeddingDownNat
    ∃ y : Cocycle (liftedResolution.{U,V,Z,L} R P)
        ((CochainComplex.singleFunctor _ 0).obj ((secondLift.{U,V,Z,L} R).obj Y)) (n : ℤ),
      y.val = resolutionSign n • Cochain.toSingleMk
        ((liftedTerm.{U,V,Z,L} R P n).hom ≫ liftCochain.{U,V,Z,L} R P Y n x.val)
        (neg_add_cancel (n : ℤ)) ∧
      signedModuleEquiv.{U,V,Z,L,W} R P hP Y n (P103.Specs.Ch10.Complexes.homologyClass _ n x) =
        projectiveClassMap _ _ _ (extendedAugmentation Q e he)
          (extendedAugmentation_quasiIso Q e he) (n : ℤ) (CohomologyClass.mk y) := by
  dsimp only
  let P₁ := leftResolution.{U,V,Z,L} R P
  let hP₁ := leftResolution_isProjective.{U,V,Z,L} R P hP
  let Y₁ := (secondLift.{U,V,Z,L} R).obj Y
  let c : cycles (homComplex P₁.complex Y₁) n :=
    resolutionSign n • liftCycle.{U,V,Z,L} R P Y n x
  let Q := resolution.{U,V,Z,L} R P hP
  let f : Q.complex.X n ⟶ Y₁ := ModuleCat.ofHom c.val
  have hf : Q.complex.d (n+1) n ≫ f = 0 :=
    ModuleCat.hom_ext (P103Bridge.cycle_condition.{max V Z L,U} P₁ Y₁ n c)
  obtain ⟨y, hy, h⟩ := projectiveExtMk_hom_eq_extended_class Q
    (ComplexShape.embeddingUpIntLE 0) embeddingUpIntLE_zero_eq_embeddingDownNat n
    (by simp) f hf
  refine ⟨y, ?_, ?_⟩
  · have hf' : f = resolutionSign n • liftCochain.{U,V,Z,L} R P Y n x.val := by
      apply ModuleCat.hom_ext
      change resolutionSign n • (liftCycle.{U,V,Z,L} R P Y n x).val =
        resolutionSign n • (liftCochain.{U,V,Z,L} R P Y n x.val).hom
      exact congrArg (resolutionSign n • ·) (liftCycle_val R P Y n x)
    rw [hy, hf']
    change Cochain.toSingleMk ((liftedTerm.{U,V,Z,L} R P n).hom ≫
        (resolutionSign n • liftCochain.{U,V,Z,L} R P Y n x.val)) (neg_add_cancel (n : ℤ)) =
      resolutionSign n • Cochain.toSingleMk
        ((liftedTerm.{U,V,Z,L} R P n).hom ≫ liftCochain.{U,V,Z,L} R P Y n x.val) (neg_add_cancel (n : ℤ))
    rw [Preadditive.comp_zsmul, Cochain.toSingleMk_smul]
  · rw [signedModuleEquiv_apply, liftExtEquiv_class]
    let e₁ := P103Bridge.moduleEquiv.{W,max V Z L,U} P₁ hP₁ Y₁ n
    let cl := P103.Specs.Ch10.Complexes.homologyClass (homComplex P₁.complex Y₁) n
    let c₀ : cycles (homComplex P₁.complex Y₁) n := liftCycle.{U,V,Z,L} R P Y n x
    change resolutionSign n • e₁ (cl c₀) = _
    rw [← map_zsmul e₁, ← map_zsmul cl]
    change e₁ (cl c) = _
    exact (P103Bridge.moduleEquiv_class_hom.{W,max V Z L,U} P₁ hP₁ Y₁ n c).trans h

noncomputable def independentComparison.{U,V,Z,L,W} (R : Type U) [Ring R]
    [HasDerivedCategory.{W} (ModuleCat.{max U V Z L} R)] :
    IndependentModuleComparison.{U,V,Z,L,W} R where
  equiv _ Y P hP n := signedModuleEquiv.{U,V,Z,L,W} R P hP Y n
  cocycle_formula X P hP := by
    let Q := resolution.{U,V,Z,L} R P hP
    let e := ComplexShape.embeddingUpIntLE 0
    let he := embeddingUpIntLE_zero_eq_embeddingDownNat
    refine ⟨extendedAugmentation Q e he, extendedAugmentation_quasiIso Q e he,
      extendedAugmentation_f_zero Q e he rfl, ?_⟩
    intro Y n x
    exact signedModuleEquiv_class.{U,V,Z,L,W} R P hP Y n x
  natural := signedModuleEquiv_natural.{U,V,Z,L,W} R
  zero _ Y P hP x f hf := signedModuleEquiv_zero.{U,V,Z,L,W} R P hP Y x f hf

end LiftedP103

theorem module_independent_universes : independentModuleType := by
  intro R _ _
  exact ⟨LiftedP103.independentComparison R⟩

namespace LiftedP103

open P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions

/-- Transport a lifted chain map back to its original resolution terms. -/
def originalComponent.{U,V,V',Z,Z',L} {R : Type U} [Ring R]
    {X : ModuleCat.{V} R} {X' : ModuleCat.{V'} R}
    {P : LeftResolution R X} {P' : LeftResolution R X'}
    (g : liftedChain.{U,V',Z',max V Z L} R P' ⟶
      liftedChain.{U,V,Z,max V' Z' L} R P) (n : ℕ) :
    P'.complex.X n →ₗ[R] P.complex.X n :=
  ULift.moduleEquiv.toLinearMap.comp
    ((g.f n).hom.comp ULift.moduleEquiv.symm.toLinearMap)

section Heterogeneous
universe U V V' Z Z' L

variable {R : Type U} [Ring R]
variable {X : ModuleCat.{V} R} {X' : ModuleCat.{V'} R}
variable {Y : ModuleCat.{Z} R} {Y' : ModuleCat.{Z'} R}
variable {P : LeftResolution R X} {P' : LeftResolution R X'}

lemma originalComponent_comm
    (g : liftedChain.{U,V',Z',max V Z L} R P' ⟶
      liftedChain.{U,V,Z,max V' Z' L} R P) (n : ℕ) (s : P'.complex.X (n + 1)) :
    (originalComponent.{U,V,V',Z,Z',L} g n) ((P'.complex.d (n + 1) n).hom s) =
      (P.complex.d (n + 1) n).hom ((originalComponent.{U,V,V',Z,Z',L} g (n+1)) s) := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (g.comm (n+1) n))
    (ULift.up s)
  exact (congrArg ULift.down h).symm

/-- Precomposition on the original resolution terms followed by
postcomposition with the original coefficient morphism. -/
def transportCycle
    (g : liftedChain.{U,V',Z',max V Z L} R P' ⟶
      liftedChain.{U,V,Z,max V' Z' L} R P) (b : Y →ₗ[R] Y') (n : ℕ)
    (x : cycles (homComplex P.complex Y) n) :
    cycles (homComplex P'.complex Y') n :=
  ⟨b.comp (x.val.comp (originalComponent.{U,V,V',Z,Z',L} g n)), by
    change ((homComplex P'.complex Y').d n ((ComplexShape.up ℕ).next n)).hom
      (b.comp (x.val.comp (originalComponent.{U,V,V',Z,Z',L} g n))) = 0
    rw [CochainComplex.next]
    apply LinearMap.ext
    intro s
    change b ((show P.complex.X n →ₗ[R] Y from x.val) ((originalComponent.{U,V,V',Z,Z',L} g n)
        ((P'.complex.d (n+1) n).hom s))) = 0
    rw [originalComponent_comm]
    have hx := x.property
    change ((homComplex P.complex Y).d n ((ComplexShape.up ℕ).next n)).hom x.val = 0 at hx
    rw [CochainComplex.next] at hx
    change x.val.comp (P.complex.d (n+1) n).hom = 0 at hx
    have ht := LinearMap.congr_fun hx
      ((originalComponent.{U,V,V',Z,Z',L} g (n+1)) s)
    exact (congrArg b ht).trans (map_zero b)⟩

end Heterogeneous

end LiftedP103

namespace LiftedP103

open P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions

section Heterogeneous
universe U V V' Z Z' L W

variable {R : Type U} [Ring R]
variable {X : ModuleCat.{V} R} {X' : ModuleCat.{V'} R}
variable {Y : ModuleCat.{Z} R} {Y' : ModuleCat.{Z'} R}
variable {P : LeftResolution R X} {P' : LeftResolution R X'}

lemma liftCycle_transportCycle
    (g : liftedChain.{U,V',Z',max V Z L} R P' ⟶
      liftedChain.{U,V,Z,max V' Z' L} R P) (b : Y →ₗ[R] Y') (n : ℕ)
    (x : cycles (homComplex P.complex Y) n) :
    liftCycle.{U,V',Z',max V Z L} R P' Y' n
        (transportCycle.{U,V,V',Z,Z',L} g b n x) =
      cyclesMap (homPreMap g ((secondLift.{U,V,Z,max V' Z' L} R).obj Y) ≫
        homPostMap (liftedChain.{U,V',Z',max V Z L} R P')
          (liftLinearMap b)) n (liftCycle.{U,V,Z,max V' Z' L} R P Y n x) := by
  apply Subtype.ext
  rw [liftCycle_val]
  change (liftCochain.{U,V',Z',max V Z L} R P' Y' n
    (transportCycle.{U,V,V',Z,Z',L} g b n x).val).hom = _
  apply LinearMap.ext
  rintro ⟨s⟩
  simp only [P103.Specs.Ch10.Complexes.cyclesMap, LinearMap.codRestrict_apply,
    LinearMap.comp_apply, Submodule.coe_subtype, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, liftCycle_val]
  rfl

/-- The quotient map induced by a lifted resolution map and an original
coefficient map, transferred to both original P103 quotients. -/
noncomputable def transportExt
    (g : liftedChain.{U,V',Z',max V Z L} R P' ⟶
      liftedChain.{U,V,Z,max V' Z' L} R P) (b : Y →ₗ[R] Y') (n : ℕ) :
    ExtWith P Y n →+ ExtWith P' Y' n :=
  (liftExtEquiv.{U,V',Z',max V Z L} R P' Y' n).symm.toAddMonoidHom.comp
    ((homologyMap (homPreMap g ((secondLift.{U,V,Z,max V' Z' L} R).obj Y) ≫
      homPostMap (liftedChain.{U,V',Z',max V Z L} R P') (liftLinearMap b)) n).toAddMonoidHom.comp
      (liftExtEquiv.{U,V,Z,max V' Z' L} R P Y n).toAddMonoidHom)

lemma transportExt_class
    (g : liftedChain.{U,V',Z',max V Z L} R P' ⟶
      liftedChain.{U,V,Z,max V' Z' L} R P) (b : Y →ₗ[R] Y') (n : ℕ)
    (x : cycles (homComplex P.complex Y) n) :
    transportExt.{U,V,V',Z,Z',L} g b n (P103.Specs.Ch10.Complexes.homologyClass _ n x) =
      P103.Specs.Ch10.Complexes.homologyClass _ n (transportCycle.{U,V,V',Z,Z',L} g b n x) := by
  apply (liftExtEquiv.{U,V',Z',max V Z L} R P' Y' n).injective
  change (liftExtEquiv.{U,V',Z',max V Z L} R P' Y' n)
      ((liftExtEquiv.{U,V',Z',max V Z L} R P' Y' n).symm
        (homologyMap _ n (liftExtEquiv.{U,V,Z,max V' Z' L} R P Y n
          (P103.Specs.Ch10.Complexes.homologyClass _ n x)))) = _
  rw [AddEquiv.apply_symm_apply, liftExtEquiv_class, liftExtEquiv_class,
    liftCycle_transportCycle]
  rfl

variable [HasDerivedCategory.{W} (ModuleCat.{max U V Z V' Z' L} R)]

lemma signedModuleEquiv_transportExt
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (a : X' →ₗ[R] X) (b : Y →ₗ[R] Y')
    (g : liftedChain.{U,V',Z',max V Z L} R P' ⟶ liftedChain.{U,V,Z,max V' Z' L} R P)
    (hg : g.f 0 ≫ liftAugmentation.{U,V,Z,max V' Z' L} R P =
      liftAugmentation.{U,V',Z',max V Z L} R P' ≫
        ModuleCat.ofHom (liftLinearMap a))
    (n : ℕ) (x : ExtWith P Y n) :
    signedModuleEquiv.{U,V',Z',max V Z L,W} R P' hP' Y' n
      (transportExt.{U,V,V',Z,Z',L} g b n x) =
    extMap (ModuleCat.ofHom (liftLinearMap a)) (ModuleCat.ofHom (liftLinearMap b)) (n : ℤ)
      (signedModuleEquiv.{U,V,Z,max V' Z' L,W} R P hP Y n x) := by
  let a' : (firstLift.{U,V',Z',max V Z L} R).obj X' ⟶
      (firstLift.{U,V,Z,max V' Z' L} R).obj X := ModuleCat.ofHom (liftLinearMap a)
  let b' : (secondLift.{U,V,Z,max V' Z' L} R).obj Y ⟶
      (secondLift.{U,V',Z',max V Z L} R).obj Y' := ModuleCat.ofHom (liftLinearMap b)
  let Q := leftResolution.{U,V,Z,max V' Z' L} R P
  let Q' := leftResolution.{U,V',Z',max V Z L} R P'
  have hg' : ChainLift Q' Q a'.hom g := congrArg ModuleCat.Hom.hom hg
  rw [signedModuleEquiv_apply, signedModuleEquiv_apply]
  change resolutionSign n •
    P103Bridge.moduleEquiv.{W,max V Z V' Z' L,U} Q'
      (leftResolution_isProjective.{U,V',Z',max V Z L} R P' hP')
      ((secondLift.{U,V',Z',max V Z L} R).obj Y') n
      (liftExtEquiv.{U,V',Z',max V Z L} R P' Y' n
        ((liftExtEquiv.{U,V',Z',max V Z L} R P' Y' n).symm
          (homologyMap (homPreMap g ((secondLift.{U,V,Z,max V' Z' L} R).obj Y) ≫
            homPostMap (liftedChain.{U,V',Z',max V Z L} R P') b'.hom) n (liftExtEquiv.{U,V,Z,max V' Z' L} R P Y n x)))) = _
  rw [AddEquiv.apply_symm_apply]
  refine (congrArg (resolutionSign n • ·)
    (P103Bridge.moduleEquiv_natural.{W,max V Z V' Z' L,U} _ _ _ _ Q Q'
      (leftResolution_isProjective.{U,V,Z,max V' Z' L} R P hP)
      (leftResolution_isProjective.{U,V',Z',max V Z L} R P' hP') a' b' g hg' n
      (liftExtEquiv.{U,V,Z,max V' Z' L} R P Y n x))).trans ?_
  exact (extMap_zsmul a' b' (n : ℤ) _ _).symm

/-- Compatible lifts of the same original map give the same map of original quotients. -/
lemma transportExt_eq_of_compatible
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (a : X' →ₗ[R] X) (b : Y →ₗ[R] Y')
    (g₁ g₂ : liftedChain.{U,V',Z',max V Z L} R P' ⟶ liftedChain.{U,V,Z,max V' Z' L} R P)
    (hg₁ : g₁.f 0 ≫ liftAugmentation.{U,V,Z,max V' Z' L} R P =
      liftAugmentation.{U,V',Z',max V Z L} R P' ≫ ModuleCat.ofHom (liftLinearMap a))
    (hg₂ : g₂.f 0 ≫ liftAugmentation.{U,V,Z,max V' Z' L} R P =
      liftAugmentation.{U,V',Z',max V Z L} R P' ≫ ModuleCat.ofHom (liftLinearMap a))
    (n : ℕ) :
    transportExt.{U,V,V',Z,Z',L} g₁ b n = transportExt.{U,V,V',Z,Z',L} g₂ b n := by
  ext x
  apply (signedModuleEquiv.{U,V',Z',max V Z L,W} R P' hP' Y' n).injective
  exact (signedModuleEquiv_transportExt.{U,V,V',Z,Z',L,W} hP hP' a b g₁ hg₁ n x).trans
    (signedModuleEquiv_transportExt.{U,V,V',Z,Z',L,W} hP hP' a b g₂ hg₂ n x).symm

end Heterogeneous

end LiftedP103

theorem module_heterogeneous_naturality : heterogeneousModuleType.{w,v,u,z,v',z',l} := by
  intro R _ _
  let C := LiftedP103.independentComparison.{u,v,z,max v' z' l,w} R
  let C' := LiftedP103.independentComparison.{u,v',z',max v z l,w} R
  refine ⟨C, C', ?_⟩
  intro X X' Y Y' P P' hP hP' a b a' b' aug aug'
  refine ⟨?_, ?_⟩
  · let A := LiftedP103.leftResolution.{u,v,z,max v' z' l} R P
    let A' := LiftedP103.leftResolution.{u,v',z',max v z l} R P'
    obtain ⟨g, hg⟩ := P103.Ch10.Comparison.chain_exists.{u,max u v z v' z' l}
      R _ _ A' A (LiftedP103.leftResolution_isProjective.{u,v',z',max v z l} R P' hP') a'.hom
    exact ⟨g, ModuleCat.hom_ext hg⟩
  · intro g hg n
    refine ⟨LiftedP103.transportExt.{u,v,v',z,z',l} g b n, ?_, ?_⟩
    · intro x
      exact ⟨LiftedP103.transportCycle.{u,v,v',z,z',l} g b n x, fun _ => rfl,
        LiftedP103.transportExt_class.{u,v,v',z,z',l} g b n x⟩
    · intro x
      exact LiftedP103.signedModuleEquiv_transportExt.{u,v,v',z,z',l,w} hP hP' a b g hg n x

end AdvancedHomologicalAlgebra.ExtShiftedHom
