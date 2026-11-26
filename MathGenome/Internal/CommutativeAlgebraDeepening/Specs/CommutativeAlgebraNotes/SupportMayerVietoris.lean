import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.RingTheory.Noetherian.Defs

/-! The Mayer–Vietoris sequence on derived ideal torsion. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Specs.CommutativeAlgebraNotes.SupportMayerVietoris

open IdealTorsion (idealTorsion idealTorsionFunctor localCohomology)

universe u v

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

private theorem torsion_le (M : ModuleCat.{v} R) {A B : Ideal R} (h : A ≤ B) :
    idealTorsion B M ≤ idealTorsion A M := by
  intro x hx
  simp only [idealTorsion, Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff,
    SetCoe.forall, SetLike.mem_coe] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, fun a ha => hn a (pow_le_pow_left' h n ha)⟩

private abbrev inclusionApp {A B : Ideal R} (h : A ≤ B) (M : ModuleCat.{v} R) :
    (idealTorsionFunctor B).obj M ⟶ (idealTorsionFunctor A).obj M :=
  ModuleCat.ofHom (Submodule.inclusion (torsion_le M h))

@[simp]
private lemma inclusionApp_apply {A B : Ideal R} (h : A ≤ B) (M : ModuleCat.{v} R)
    (x : idealTorsion B M) : Subtype.val ((inclusionApp h M).hom x) = x.val := by
  change (Submodule.inclusion (torsion_le M h) x).val = x.val
  rw [Submodule.inclusion_apply]

@[simp]
private lemma torsionMap_apply (A : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (x : idealTorsion A M) : Subtype.val (((idealTorsionFunctor A).map f).hom x) = f.hom x.val := rfl

/-- The inclusion of sections with supports coming from a larger ideal. -/
def inclusion {A B : Ideal R} (h : A ≤ B) :
    idealTorsionFunctor.{v} B ⟶ idealTorsionFunctor.{v} A where
  app := inclusionApp h
  naturality M N f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, inclusionApp_apply, torsionMap_apply]

@[simp]
theorem inclusion_app_val {A B : Ideal R} (h : A ≤ B) (M : ModuleCat.{v} R)
    (x : idealTorsion B M) : Subtype.val (((inclusion h).app M).hom x) = x.val :=
  inclusionApp_apply h M x

@[simp, reassoc]
theorem inclusion_comp {A B C : Ideal R} (h : A ≤ B) (k : B ≤ C)
    (M : ModuleCat.{v} R) :
    (inclusion k).app M ≫ (inclusion h).app M = (inclusion (h.trans k)).app M := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, inclusion, inclusionApp_apply]

theorem inclusion_comp_ambient {A B : Ideal R} (h : A ≤ B) (M : ModuleCat.{v} R) :
    (inclusion h).app M ≫ (IdealTorsion.idealTorsionInclusion A).app M =
      (IdealTorsion.idealTorsionInclusion B).app M := by
  let hle := torsion_le M h
  change ModuleCat.ofHom (Submodule.inclusion hle) ≫
      ModuleCat.ofHom (idealTorsion A M).subtype = ModuleCat.ofHom (idealTorsion B M).subtype
  rw [← ModuleCat.ofHom_comp, Submodule.subtype_comp_inclusion]

abbrev Cochains (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{v} R) ℕ
abbrev torsionCochains (A : Ideal R) : Cochains.{u,v} R ⥤ Cochains.{u,v} R :=
  (idealTorsionFunctor A).mapHomologicalComplex (.up ℕ)

abbrev cochainInclusion {A B : Ideal R} (h : A ≤ B) :
    torsionCochains.{u,v} B ⟶ torsionCochains.{u,v} A :=
  (inclusion h).mapHomologicalComplex (.up ℕ)

/-- The diagonal and the first inclusion minus the second inclusion, on supported cochains. -/
abbrev cochainRow (I J : Ideal R) (K : Cochains.{u,v} R) :
    ShortComplex (Cochains.{u,v} R) :=
  ShortComplex.mk
    (biprod.lift ((cochainInclusion (le_sup_left : I ≤ I ⊔ J)).app K)
      ((cochainInclusion (le_sup_right : J ≤ I ⊔ J)).app K))
    (biprod.desc ((cochainInclusion (inf_le_left : I ⊓ J ≤ I)).app K)
      (-((cochainInclusion (inf_le_right : I ⊓ J ≤ J)).app K))) (by
    rw [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg]
    apply sub_eq_zero.mpr
    apply HomologicalComplex.hom_ext
    intro n
    simp only [comp_f, NatTrans.mapHomologicalComplex_app_f, inclusion_comp])

/-- The pointwise direct sum of two module-valued functors. -/
def sumFunctor (F G : ModuleCat.{v} R ⥤ ModuleCat.{v} R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := F.obj M ⊞ G.obj M
  map f := biprod.map (F.map f) (G.map f)
  map_id M := by
    apply biprod.hom_ext <;> simp [biprod.map_fst, biprod.map_snd]
  map_comp f g := by
    apply biprod.hom_ext <;> simp [biprod.map_fst, biprod.map_snd, Category.assoc]

variable [Small.{v} R]

abbrev H (I : Ideal R) (n : ℕ) := localCohomology.{v} I (n : ℤ)
abbrev resolutionRow (I J : Ideal R) (M : ModuleCat.{v} R) :=
  cochainRow I J (injectiveResolution M).cocomplex

/-- The canonical comparison of derived torsion with torsion on the chosen resolution. -/
def compare (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    (H I n).obj M ≅ (homologyFunctor (ModuleCat.{v} R) (.up ℕ) n).obj
      ((torsionCochains I).obj (injectiveResolution M).cocomplex) :=
  (injectiveResolution M).isoRightDerivedObj (idealTorsionFunctor I) n

instance (n : ℕ) :
    PreservesBinaryBiproducts (homologyFunctor (ModuleCat.{v} R) (.up ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- The comparison on the middle term, using preservation of the binary biproduct. -/
def compareSum (I J : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    (sumFunctor (H I n) (H J n)).obj M ≅
      (homologyFunctor (ModuleCat.{v} R) (.up ℕ) n).obj (resolutionRow I J M).X₂ :=
  biprod.mapIso (compare I M n) (compare J M n) ≪≫
    ((homologyFunctor (ModuleCat.{v} R) (.up ℕ) n).mapBiprod
      ((torsionCochains I).obj (injectiveResolution M).cocomplex)
      ((torsionCochains J).obj (injectiveResolution M).cocomplex)).symm

/-- The natural long exact sequence, with the maps specified through the cohomology
sequence of the supported cochain row and the standard cochain connecting morphism. -/
def MayerVietoris : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R] (I J : Ideal R),
    ∃ (α : ∀ n, H (I ⊔ J) n ⟶ sumFunctor (H I n) (H J n))
      (β : ∀ n, sumFunctor (H I n) (H J n) ⟶ H (I ⊓ J) n)
      (δ : ∀ n, H (I ⊓ J) n ⟶ H (I ⊔ J) (n + 1)),
      ∀ M : ModuleCat.{v} R,
        Mono ((α 0).app M) ∧
        ∃ h : (resolutionRow I J M).ShortExact,
          ∀ n,
            (α n).app M ≫ (compareSum I J M n).hom =
              (compare (I ⊔ J) M n).hom ≫ homologyMap (resolutionRow I J M).f n ∧
            (β n).app M ≫ (compare (I ⊓ J) M n).hom =
              (compareSum I J M n).hom ≫ homologyMap (resolutionRow I J M).g n ∧
            (δ n).app M ≫ (compare (I ⊔ J) M (n + 1)).hom =
              (compare (I ⊓ J) M n).hom ≫ h.δ n (n + 1) rfl ∧
            (ComposableArrows.mk₅ ((α n).app M) ((β n).app M) ((δ n).app M)
              ((α (n + 1)).app M) ((β (n + 1)).app M)).Exact

section OpenComplements

open AlgebraicGeometry TopologicalSpace
open CechCohomologyOfOpenComplement (complement sections restrict toSections)

variable (S : CommRingCat.{u})

/-- The sections of an associated module sheaf over an open, applied degreewise. -/
abbrev openCochains (U : (Spec S).Opens) : Cochains.{u,u} S ⥤ Cochains.{u,u} S :=
  (tilde.functor S ⋙ sections S U).mapHomologicalComplex (.up ℕ)

/-- Restriction from the ambient affine spectrum, identifying its sections with the module. -/
def toOpenCochains (U : (Spec S).Opens) : 𝟭 (Cochains.{u,u} S) ⟶ openCochains S U :=
  (Functor.mapHomologicalComplexIdIso _ (.up ℕ)).inv ≫
    (toSections S U).mapHomologicalComplex (.up ℕ)

def ambientInclusion (I : Ideal S) : torsionCochains.{u,u} I ⟶ 𝟭 (Cochains.{u,u} S) :=
  (IdealTorsion.idealTorsionInclusion I).mapHomologicalComplex (.up ℕ) ≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℕ)).hom

variable {S}

/-- Inclusion of the open complements of nested closed subsets. -/
theorem complement_mono {A B : Ideal S} (h : A ≤ B) : complement S A ≤ complement S B :=
  Set.compl_subset_compl.mpr (PrimeSpectrum.zeroLocus_anti_mono_ideal h)

/-- The strict fibre sequences used by support Mayer–Vietoris, with maps given by
the actual restrictions on the open complements. -/
def OpenComplementKernels : Prop :=
  ∀ (S : CommRingCat.{u}) [IsNoetherianRing S],
    (∀ I J : Ideal S, complement S (I ⊔ J) = complement S I ⊔ complement S J ∧
      complement S (I ⊓ J) = complement S I ⊓ complement S J) ∧
    ∀ (K : Cochains.{u,u} S), (∀ n, Injective (K.X n)) →
      ∃ z : ∀ I : Ideal S, (ambientInclusion S I).app K ≫
          (toOpenCochains S (complement S I)).app K = 0,
        let row := fun I => ShortComplex.mk _ _ (z I)
        (∀ I, (row I).ShortExact) ∧
        ∀ (A B : Ideal S) (h : A ≤ B),
          ∃ φ : row B ⟶ row A,
            φ.τ₁ = (cochainInclusion h).app K ∧ φ.τ₂ = 𝟙 K ∧
              φ.τ₃ = (NatTrans.mapHomologicalComplex
                (Functor.whiskerLeft (tilde.functor S) (restrict S (complement_mono h)))
                (.up ℕ)).app K

end OpenComplements

end Specs.CommutativeAlgebraNotes.SupportMayerVietoris
