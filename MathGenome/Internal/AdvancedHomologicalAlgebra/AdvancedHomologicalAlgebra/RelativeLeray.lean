import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RelativeLeray
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedSectionsComposition
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GrothendieckEdges

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 150000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.HigherDirectImageLocalTheory
open AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
open AdvancedHomologicalAlgebra.GrothendieckEdges
open AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality
open Specs.AdvancedHomologicalAlgebra.RelativeLeray

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AdvancedHomologicalAlgebra.RelativeLeray

/-- Pushforwards of injectives are acyclic for any second direct image. -/
theorem injectivePushforwardAcyclic : Acyclicity.{u} := by
  intro X Y Z R S T f g φ ψ I hI
  let G := directImage S T g ψ
  let M := (directImage R S f φ).obj I
  letI : PreservesFiniteLimits G := (DerivedSectionsComposition.leftExact S T g ψ).1
  apply (AcyclicTermComparison.rightVanishing (Modules S) (Modules T) G M).mpr
  intro n
  obtain ⟨J, ι, _, _, _, hJ⟩ := HigherDirectImageLocalDescription.localDescription S T g ψ M
  obtain ⟨e⟩ := (hJ (n+1)).2
  apply IsZero.of_iso _ e
  apply (associate T).map_isZero
  apply (IsZero.iff_id_eq_zero _).2
  apply PresheafOfModules.hom_ext
  intro U
  let V := (Opens.map g).obj (unop U)
  let Res := ModuleCat.restrictScalars (ψ.hom.app U).hom
  have hz := HigherDirectImageLocalDescription.injectivePushforwardAcyclic R S f φ I hI V n
  obtain ⟨eU⟩ := (hJ (n+1)).1 (unop U)
  exact ((Res.map_isZero hz).of_iso eU).eq_of_src _ _

/-- The canonical composition map is an isomorphism on D⁺. -/
theorem canonicalComposition : CanonicalComposition.{u} := by
  intro X Y Z R S T f g φ ψ
  let F := directImage R S f φ
  let G := directImage S T g ψ
  letI : PreservesFiniteLimits F := (DerivedSectionsComposition.leftExact R S f φ).1
  letI : PreservesFiniteLimits G := (DerivedSectionsComposition.leftExact S T g ψ).1
  letI := (RightDerivedComposition.comparisonIsoIff (Modules R) (Modules S) (Modules T) F G).mpr
    (injectivePushforwardAcyclic R S T f g φ ψ)
  letI : IsIso (_root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G) :=
    NatIso.isIso_of_isIso_app _
  unfold compositionMap
  infer_instance

/-- First-quadrant support propagates from the second page by page homology. -/
private lemma quadrantOfSecond {C : Type*} [Category C] [Abelian C] (D : RowDiagram C)
    (h : ∀ p n : ℤ, p < 0 ∨ n < p → IsZero (D.page 0 p n)) :
    ∀ (r : ℕ) (p n : ℤ), p < 0 ∨ n < p → IsZero (D.page r p n) := by
  intro r
  induction r with
  | zero => exact h
  | succ r ih =>
    intro p n hpn
    let a := p - ((r : ℤ) + 2)
    have hp : a + ((r : ℤ) + 2) = p := by dsimp [a]; omega
    have hn : n - 1 + 1 = n := by omega
    have hzero : IsZero ((D.pageComplex r a (n - 1)).X₂) := by
      change IsZero (D.page r (a + ((r : ℤ) + 2)) (n - 1 + 1))
      rw [hp, hn]
      exact ih p n hpn
    have hz := IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _ hzero)
      (D.nextIso r a (n - 1))
    rwa [hp, hn] at hz

section Abutment

variable {X Y Z : TopCat.{u}} {R : RingSheaf X} {S : RingSheaf Y} {T : RingSheaf Z}
  {f : X ⟶ Y} {g : Y ⟶ Z}
  {φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R}
  {ψ : T ⟶ (TopCat.Sheaf.pushforward RingCat.{u} g).obj S}
  (L : Data R S T f g φ ψ)

local notation "F₀" => directImage R S f φ
local notation "G₀" => directImage S T g ψ
local notation "FG₀" => compositeDirectImage R S T f g φ ψ

/-- The comparison on the abutment is cohomology of the inverse of the
canonical relative composition map, in the iterated derived coordinates. -/
theorem Data.targetIso_canonical (n : ℤ) :
    letI := L.composition_isIso
    L.targetIso n = L.package.iteratedIso n ≪≫
      isoWhiskerRight (asIso (compositionMap R S T f g φ ψ)).symm
        (DerivedCategory.Plus.homologyFunctor (Modules T) n) := by
  letI := L.package.comparison_isIso
  letI : IsIso (_root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F₀ G₀) :=
    NatIso.isIso_of_isIso_app _
  letI := L.composition_isIso
  have hcomp :
      (derivedPushforwardIso R S T f g φ ψ).symm ≪≫
        asIso (_root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F₀ G₀) =
      asIso (compositionMap R S T f g φ ψ) := Iso.ext (by rfl)
  rw [Data.targetIso, L.package.canonical n, Iso.trans_assoc, pushforwardComparison,
    ← isoWhiskerRight_trans, ← hcomp]
  rfl

/-- The diagram transitions give the decreasing filtration on the relative abutment. -/
theorem Data.filtration_decreasing (K : DerivedCategory.Plus (Modules R)) (p n : ℤ) :
    L.filtration K (p + 1) n ≤ L.filtration K p n := by
  letI := L.package.inclusion_mono K p n
  letI := L.package.inclusion_mono K (p + 1) n
  dsimp only [Data.filtration]
  exact Subobject.mk_le_mk_of_comm (((sequence F₀ G₀ L.package.row).obj K).down p n)
    (by rw [← Category.assoc, L.package.down_inclusion])

/-- Morphisms in D⁺ preserve the transported abutment filtration. -/
theorem Data.filtration_natural {K K' : DerivedCategory.Plus (Modules R)} (a : K ⟶ K')
    (p n : ℤ) :
    (L.filtration K' p n).Factors ((L.filtration K p n).arrow ≫
      ((FG₀).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor (Modules T) n).map a) := by
  letI := L.package.inclusion_mono K p n
  letI := L.package.inclusion_mono K' p n
  let U := sequence F₀ G₀ L.package.row
  dsimp only [Data.filtration]
  refine ⟨(Subobject.underlyingIso _).hom ≫ (U.map a).step p n, ?_⟩
  change _ ≫ (U.obj K').inclusion p n ≫ (L.targetIso n).hom.app K' = _
  simp only [Category.assoc]
  change (Subobject.underlyingIso _).hom ≫ (U.map a).step p n ≫
      (U.obj K').inclusion p n ≫ (L.targetIso n).hom.app K' = _
  rw [← Category.assoc ((U.map a).step p n), (U.map a).inclusion_comm]
  have hn :
      (U.map a).target n ≫ (L.targetIso n).hom.app K' =
        (L.targetIso n).hom.app K ≫
          ((FG₀).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor (Modules T) n).map a :=
    (L.targetIso n).hom.naturality a
  rw [Category.assoc ((U.obj K).inclusion p n), hn, ← Category.assoc ((U.obj K).inclusion p n)]
  exact Subobject.underlyingIso_hom_comp_eq_mk_assoc _ _

/-- The diagram's graded piece is the quotient of consecutive subobjects of the
actual relative abutment. -/
def Data.filtrationQuotientIso (K : DerivedCategory.Plus (Modules R)) (p n : ℤ) :
    cokernel (((sequence F₀ G₀ L.package.row).obj K).down p n) ≅
      cokernel (Subobject.ofLE _ _ (L.filtration_decreasing K p n)) := by
  letI := L.package.inclusion_mono K p n
  letI := L.package.inclusion_mono K (p + 1) n
  dsimp only [Data.filtration]
  exact cokernel.mapIso _ _ (Subobject.underlyingIso _).symm (Subobject.underlyingIso _).symm
    (Subobject.eq_of_comp_arrow_eq (by
      simp only [Category.assoc, Iso.symm_hom, Subobject.ofLE_arrow, Subobject.underlyingIso_arrow]
      rw [← Category.assoc, L.package.down_inclusion]))

/-- The stabilized pages give the associated graded of the relative abutment
in each total degree. -/
theorem Data.filtration_convergence (K : DerivedCategory.Plus (Modules R)) (n : ℤ) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → ∀ p : ℤ,
      ((sequence F₀ G₀ L.package.row).obj K).differential r p n = 0 ∧
      Nonempty (((sequence F₀ G₀ L.package.row).obj K).page r p n ≅
        cokernel (Subobject.ofLE _ _ (L.filtration_decreasing K p n))) := by
  obtain ⟨N, hN⟩ := L.package.convergence K n
  refine ⟨N, fun r hr p => ?_⟩
  obtain ⟨hd, ⟨e⟩⟩ := hN r hr p
  exact ⟨hd, ⟨e ≪≫ L.filtrationQuotientIso K p n⟩⟩

end Abutment

/-- Relative Leray on D⁺ and its sheaf specialization with their common
degreewise finite filtration. -/
theorem relativeLeray : SpectralSequence.{u} := by
  intro X Y Z R S T f g φ ψ
  let F := directImage R S f φ
  let G := directImage S T g ψ
  letI : PreservesFiniteLimits F := (DerivedSectionsComposition.leftExact R S f φ).1
  letI : PreservesFiniteLimits G := (DerivedSectionsComposition.leftExact S T g ψ).1
  obtain ⟨P, ⟨E⟩⟩ := grothendieck_edges (Modules R) (Modules S) (Modules T) F G
    (injectivePushforwardAcyclic R S T f g φ ψ)
  let L : Data R S T f g φ ψ :=
    { package := P
      edges := E
      composition_isIso := canonicalComposition R S T f g φ ψ
      sheaf_quadrant := fun M => quadrantOfSecond _ (E.objectCase.quadrant M) }
  refine ⟨L, L.filtration_decreasing, ?_⟩
  intro K n
  obtain ⟨a, b, ha, hb⟩ := P.finite K n
  refine ⟨a, b, ?_, ?_⟩
  · intro p hp
    letI := L.package.inclusion_mono K p n
    letI := ha p hp
    dsimp only [Data.filtration]
    exact Subobject.mk_eq_top_of_isIso _
  · intro p hp
    letI := L.package.inclusion_mono K p n
    dsimp only [Data.filtration]
    exact Subobject.mk_eq_bot_iff_zero.mpr ((hb p hp).eq_of_src _ _)

end AdvancedHomologicalAlgebra.RelativeLeray
