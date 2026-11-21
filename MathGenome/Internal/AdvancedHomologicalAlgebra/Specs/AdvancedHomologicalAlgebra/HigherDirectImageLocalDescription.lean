import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomology
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! HA-H06, local description and acyclicity (3733–3740, 3749–3759).
A ringed-space map consists of a continuous map f and its actual map φ of
structure sheaves. We allow arbitrary sheaves of rings, as in HA-H00.
Local cohomology is represented by the presheaf cohomology of any injective
resolution, with restrictions induced by that same complex. In particular,
the module structures are over S(V), via φ(V), not just over global rings.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe u

namespace AdvancedHomologicalAlgebra.HigherDirectImageLocalTheory
variable {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
  (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)

abbrev directImage : Modules R ⥤ Modules S := SheafOfModules.pushforward φ

instance directImageAdditive : (directImage R S f φ).Additive where
  map_add := by intros; ext V x; rfl

/-- The classical right derived functor, using the shared D⁺ construction. -/
def higherDirectImage (q : ℕ) : Modules R ⥤ Modules S := by
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (Modules S)
  exact rightValue (directImage R S f φ) q

/-- Sections on f⁻¹V with scalars restricted along the given ring map φ(V). -/
def localValue (F : Modules R) (q : ℕ) (V : Opens Y) : ModuleCat.{u} (sectionRing S V) :=
  (ModuleCat.restrictScalars (φ.hom.app (op V)).hom).obj
    ((sectionCohomology R ((Opens.map f).obj V) q).obj F)

/-- Presheaf cohomology of the complex V ↦ I(f⁻¹V), with the actual
S-action and the restrictions induced on cohomology. For an injective
resolution I this is the usual local-cohomology presheaf. -/
def localPresheaf (I : CochainComplex (Modules R) ℤ) (q : ℕ) :
    PresheafOfModules.{u} S.obj :=
  (((directImage R S f φ ⋙ SheafOfModules.forget S).mapHomologicalComplex (.up ℤ)).obj I).homology (q : ℤ)

abbrev associate : PresheafOfModules.{u} S.obj ⥤ Modules S :=
  PresheafOfModules.sheafification (𝟙 S.obj)

end AdvancedHomologicalAlgebra.HigherDirectImageLocalTheory

namespace Specs.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
open AdvancedHomologicalAlgebra.HigherDirectImageLocalTheory

/-- Pushforward preserves flasqueness, without any flatness hypothesis. -/
def pushforwardFlasqueType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R) (F : Modules R),
    IsFlasque R F → IsFlasque S ((directImage R S f φ).obj F)

def injectivePushforwardFlasqueType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R) (I : Modules R),
    Injective I → IsFlasque S ((directImage R S f φ).obj I)

def injectivePushforwardAcyclicType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R) (I : Modules R),
    Injective I → ∀ (V : Opens Y) (n : ℕ),
      IsZero ((sectionCohomology S V (n+1)).obj ((directImage R S f φ).obj I))

/-- Every injective resolution gives both the local values over the correct
rings and the required sheafification. There is no chosen-resolution hypothesis
on F, and the separate existence statement below supplies such a resolution. -/
def localDescriptionOnResolutionType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R) (F : Modules R)
    (I : CochainComplex (Modules R) ℤ) [I.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj F ⟶ I),
    QuasiIso ι → (∀ k : ℤ, Injective (I.X k)) → ∀ q : ℕ,
    (∀ V : Opens Y, Nonempty ((localPresheaf R S f φ I q).obj (op V) ≅
      localValue R S f φ F q V)) ∧
    Nonempty ((higherDirectImage R S f φ q).obj F ≅
      (associate S).obj (localPresheaf R S f φ I q))

/-- The local description for every sheaf, with no extra hypotheses.
The existential resolution records the usual definition of the restriction
maps in the presheaf V ↦ H^q(f⁻¹V,F). -/
def localDescriptionType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R) (F : Modules R),
    ∃ (I : CochainComplex (Modules R) ℤ)
      (ι : (CochainComplex.singleFunctor (Modules R) 0).obj F ⟶ I),
      I.IsStrictlyGE 0 ∧ QuasiIso ι ∧ (∀ k : ℤ, Injective (I.X k)) ∧
      ∀ q : ℕ,
        (∀ V : Opens Y, Nonempty ((localPresheaf R S f φ I q).obj (op V) ≅
          localValue R S f φ F q V)) ∧
        Nonempty ((higherDirectImage R S f φ q).obj F ≅
          (associate S).obj (localPresheaf R S f φ I q))

end Specs.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
