import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExhaustiveChainConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.PageCohomology
import Mathlib.Algebra.Order.Archimedean.Basic

/-! HA-S02. Reverse chain and filtration indices to obtain all finite pages
from HA-F03/04. The concrete bridge identifies their actual cycle and boundary
subobjects. The limit proof uses the degreewise lower bound only for cycles,
and exhaustivity only for the union of boundaries and the target filtration.
The canonical quotient comparison is determined on closed representatives.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe u v
namespace AdvancedHomologicalAlgebra
namespace ExhaustiveChain
variable {R : Type u} [Ring R] {M N : ModuleCat.{v} R}

@[simp]
lemma moduleSubobject_mk (S : Submodule R M) :
    ModuleCat.subobjectModule M (Subobject.mk (ModuleCat.ofHom S.subtype)) = S :=
  (ModuleCat.subobjectModule M).apply_symm_apply S

@[simp]
lemma moduleSubobject_inf (S T : Subobject M) :
    ModuleCat.subobjectModule M (S ⊓ T) =
      ModuleCat.subobjectModule M S ⊓ ModuleCat.subobjectModule M T :=
  (ModuleCat.subobjectModule M).map_inf S T

@[simp]
lemma moduleSubobject_image (f : M ⟶ N) :
    ModuleCat.subobjectModule N (imageSubobject f) = LinearMap.range f.hom := by
  change LinearMap.range (imageSubobject f).arrow.hom = _
  have hh := congrArg (fun g : M ⟶ N => LinearMap.range g.hom)
    (imageSubobject_arrow_comp f)
  rw [ModuleCat.hom_comp, LinearMap.range_comp,
    ModuleCat.range_eq_top_of_epi (factorThruImageSubobject f), Submodule.map_top] at hh
  exact hh

lemma subobject_factors_of_range_le (S : Subobject N) (f : M ⟶ N)
    (h : LinearMap.range f.hom ≤ ModuleCat.subobjectModule N S) : S.Factors f := by
  let e : (S : ModuleCat R) ≃ₗ[R] ModuleCat.subobjectModule N S :=
    LinearEquiv.ofInjective S.arrow.hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  let g := e.symm.toLinearMap.comp (f.hom.codRestrict _ (fun x => h ⟨x, rfl⟩))
  apply (Subobject.factors_iff S f).2
  refine ⟨ModuleCat.ofHom g, ?_⟩
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f.hom x, h ⟨x, rfl⟩⟩)

@[simp]
lemma moduleSubobject_pullback (f : M ⟶ N) (S : Subobject N) :
    ModuleCat.subobjectModule M ((Subobject.pullback f).obj S) =
      (ModuleCat.subobjectModule N S).comap f.hom := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.pullbackπ f S).hom x, ?_⟩
    exact congrArg (fun g : ((Subobject.pullback f).obj S : ModuleCat R) ⟶ N => g.hom x)
      (Subobject.isPullback f S).w
  · let U := (ModuleCat.subobjectModule N S).comap f.hom
    have h : S.Factors (ModuleCat.ofHom U.subtype ≫ f) := by
      apply subobject_factors_of_range_le
      rintro _ ⟨x, rfl⟩
      exact x.2
    have h' := pullback_factors f S (ModuleCat.ofHom U.subtype) h
    have hh : Subobject.mk (ModuleCat.ofHom U.subtype) ≤ (Subobject.pullback f).obj S :=
      Subobject.mk_le_of_comm _ (Subobject.factorThru_arrow _ _ h')
    simpa only [moduleSubobject_mk] using (ModuleCat.subobjectModule M).monotone hh
end ExhaustiveChain
namespace ExhaustiveChain.Filtration
variable {R : Type u} [Ring R]
variable {C : ChainComplex (ModuleCat.{v} R) ℤ} (F : ExhaustiveChain.Filtration C)


/-- The source of the categorical filtration transition, in chain notation. -/
def cochainLowerStepIso (p n : ℤ) : (F.cochainFiltration.step (p+1)).X n ≅
    ModuleCat.of R (F.piece (-p-1) (-n)) :=
  F.cochainStepIso (p+1) n ≪≫
    (LinearEquiv.ofEq (F.piece (-(p+1)) (-n)) (F.piece (-p-1) (-n))
      (by rw [show -(p+1) = -p-1 by omega])).toModuleIso

abbrev cochainInclusion (p n : ℤ) :
    F.piece (-p-1) (-n) →ₗ[R] F.piece (-p) (-n) :=
  Submodule.inclusion (F.increasing (-n) (by omega))

@[reassoc (attr := simp)]
lemma cochainStepIso_subtype (p n : ℤ) :
    (F.cochainStepIso p n).hom ≫ ModuleCat.ofHom (F.piece (-p) (-n)).subtype =
      (F.cochainFiltration.piece p n).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

@[reassoc (attr := simp)]
lemma cochainLowerStepIso_subtype (p n : ℤ) :
    (F.cochainLowerStepIso p n).hom ≫ ModuleCat.ofHom (F.piece (-p-1) (-n)).subtype =
      (F.cochainFiltration.piece (p+1) n).arrow := by
  rw [← F.cochainStepIso_subtype (p+1) n]
  dsimp only [cochainLowerStepIso, Iso.trans_hom]
  rw [Category.assoc]
  congr 1

lemma cochainTransition_square (p n : ℤ) :
    (F.cochainFiltration.transition p).f n ≫ (F.cochainStepIso p n).hom =
      (F.cochainLowerStepIso p n).hom ≫ ModuleCat.ofHom (F.cochainInclusion p n) := by
  apply (cancel_mono (ModuleCat.ofHom (F.piece (-p) (-n)).subtype)).1
  rw [Category.assoc, cochainStepIso_subtype, Category.assoc]
  change Subobject.ofLE _ _ _ ≫ (F.cochainFiltration.piece p n).arrow = _
  rw [Subobject.ofLE_arrow]
  rw [← F.cochainLowerStepIso_subtype p n]
  rfl

/-- The concrete graded quotient is the categorical cokernel used upstream. -/
def cochainGradedIso (p n : ℤ) :
    ModuleCat.of R (F.graded (-p) (-n)) ≅ (F.cochainFiltration.graded p).X n :=
  (Submodule.quotEquivOfEq _ _
    (Submodule.range_inclusion (F.piece (-p-1) (-n)) (F.piece (-p) (-n))
      (F.increasing (-n) (by omega)))).symm.toModuleIso ≪≫
  (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom (F.cochainInclusion p n))).symm ≪≫
  (cokernel.mapIso ((F.cochainFiltration.transition p).f n)
    (ModuleCat.ofHom (F.cochainInclusion p n))
    (F.cochainLowerStepIso p n) (F.cochainStepIso p n)
    (F.cochainTransition_square p n)).symm

@[reassoc]
lemma cochainGradedIso_inv_projection (p n : ℤ) :
    (F.cochainFiltration.projection p).f n ≫ (F.cochainGradedIso p n).inv =
      (F.cochainStepIso p n).hom ≫ ModuleCat.ofHom (F.gradedProjection (-p) (-n)) := by
  change cokernel.π ((F.cochainFiltration.transition p).f n) ≫ _ = _
  simp only [cochainGradedIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    cokernel.mapIso_hom, cokernel.map, cokernel.π_desc_assoc]
  simp only [← Category.assoc, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  ext x
  rfl

@[reassoc]
lemma cochainGradedIso_projection (p n : ℤ) :
    ModuleCat.ofHom (F.gradedProjection (-p) (-n)) ≫ (F.cochainGradedIso p n).hom =
      (F.cochainStepIso p n).inv ≫ (F.cochainFiltration.projection p).f n := by
  apply (cancel_mono (F.cochainGradedIso p n).inv).1
  rw [Category.assoc, Iso.hom_inv_id, comp_id, Category.assoc,
    F.cochainGradedIso_inv_projection, Iso.inv_hom_id_assoc]

/-- Projection of a categorical subobject agrees with projection of its
concrete submodule. This supplies the required bridge, rather than merely an
abstract isomorphism between unrelated pages. -/
lemma gradedImage_bridge (p n : ℤ) (S : Subobject (F.cochain.X n))
    (hS : S ≤ F.cochainFiltration.piece p n) :
    (F.gradedImage (-p) (-n) (ModuleCat.subobjectModule _ S)).map
      (F.cochainGradedIso p n).hom.hom =
      ModuleCat.subobjectModule _ (imageSubobject
        (FilteredPage.gradedRepresentative F.cochainFiltration p n S hS)) := by
  let j := Subobject.ofLE _ _ hS ≫ (F.cochainStepIso p n).hom
  have hj : j ≫ ModuleCat.ofHom (F.piece (-p) (-n)).subtype = S.arrow := by
    simp only [j, Category.assoc, cochainStepIso_subtype, Subobject.ofLE_arrow]
  have hr : LinearMap.range j.hom =
      (ModuleCat.subobjectModule _ S).comap (F.piece (-p) (-n)).subtype := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      exact (congrArg (fun g : (S : ModuleCat R) ⟶ C.X (-n) => g.hom y) hj).symm
    · rintro ⟨y, hy⟩
      refine ⟨y, Subtype.ext ?_⟩
      exact (congrArg (fun g : (S : ModuleCat R) ⟶ C.X (-n) => g.hom y) hj).trans hy
  rw [moduleSubobject_image]
  change (((ModuleCat.subobjectModule _ S).comap (F.piece (-p) (-n)).subtype).map
      (F.gradedProjection (-p) (-n))).map _ = _
  rw [← hr, ← LinearMap.range_comp, ← LinearMap.range_comp]
  change LinearMap.range ((j ≫ ModuleCat.ofHom (F.gradedProjection (-p) (-n)) ≫
    (F.cochainGradedIso p n).hom).hom) = _
  rw [F.cochainGradedIso_projection]
  simp only [j, Category.assoc, Iso.hom_inv_id_assoc]

lemma cochainAlmost_submodule (r : ℕ) (p n : ℤ) :
    ModuleCat.subobjectModule (C.X (-n)) (FilteredPage.almost F.cochainFiltration (r:ℤ) p n) =
      F.almost r (-p) (-n) := by
  rw [moduleSubobject_inf, moduleSubobject_pullback]
  dsimp only [cochainFiltration, cochain]
  rw [moduleSubobject_mk, moduleSubobject_mk]
  unfold almost d
  have hn : -(n+1) = -n-1 := by omega
  have hp : -(p+(r:ℤ)) = -p-(r:ℤ) := by omega
  change F.piece (-p) (-n) ⊓
    (F.piece (-(p+(r:ℤ))) (-(n+1))).comap (C.d (-n) (-(n+1))).hom = _
  rw [hn, hp]

lemma cochainBoundarySource_submodule (r : ℕ) (p n : ℤ) :
    ModuleCat.subobjectModule (C.X (-n)) (FilteredPage.boundarySource F.cochainFiltration (r:ℤ) p n) =
      F.boundarySource r (-p) (-n) := by
  rw [moduleSubobject_inf, moduleSubobject_image, ModuleCat.hom_comp, LinearMap.range_comp]
  change ModuleCat.subobjectModule _ (F.cochainFiltration.piece p n) ⊓
    (ModuleCat.subobjectModule _ (F.cochainFiltration.piece (p-(r:ℤ)+1) (n-1))).map _ = _
  dsimp only [cochainFiltration, cochain]
  rw [moduleSubobject_mk, moduleSubobject_mk]
  unfold boundarySource
  have hn : -(n-1) = -n+1 := by omega
  have hp : -(p-(r:ℤ)+1) = -p+(r:ℤ)-1 := by omega
  change F.piece (-p) (-n) ⊓
    (F.piece (-(p-(r:ℤ)+1)) (-(n-1))).map (C.d (-(n-1)) (-n)).hom = _
  rw [hn, hp]

lemma cochain_cycles_formula (r : ℕ) (p n : ℤ) :
    (F.pageCycles r (-p) (-n)).map (F.cochainGradedIso p n).hom.hom =
      ModuleCat.subobjectModule _ (FilteredPage.cycles F.cochainFiltration (r:ℤ) p n) := by
  change (F.gradedImage (-p) (-n) (F.almost r (-p) (-n))).map _ = _
  rw [← F.cochainAlmost_submodule r p n]
  exact F.gradedImage_bridge p n (FilteredPage.almost F.cochainFiltration (r:ℤ) p n) inf_le_left

lemma cochain_boundaries_formula (r : ℕ) (p n : ℤ) :
    (F.pageBoundaries r (-p) (-n)).map (F.cochainGradedIso p n).hom.hom =
      ModuleCat.subobjectModule _ (FilteredPage.boundaries F.cochainFiltration (r:ℤ) p n) := by
  change (F.gradedImage (-p) (-n) (F.boundarySource r (-p) (-n))).map _ = _
  rw [← F.cochainBoundarySource_submodule r p n]
  exact F.gradedImage_bridge p n (FilteredPage.boundarySource F.cochainFiltration (r:ℤ) p n) inf_le_left

/-- The lower bound in degree `n-1` kills the differential of an almost cycle. -/
theorem almost_eventually (hF : F.BoundedBelow) (a n : ℤ) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, F.almost r a n = F.filteredCycles a n := by
  obtain ⟨l, hl⟩ := hF (n-1)
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℕ, a-l < (r₀:ℤ) := exists_nat_gt (a-l)
  refine ⟨r₀, fun r hr => ?_⟩
  have hf : F.piece (a-(r:ℤ)) (n-1) = ⊥ := hl _ (by omega)
  ext x
  simp [almost, filteredCycles, hf, cycles, LinearMap.mem_ker]

theorem pageCycles_eventually (hF : F.BoundedBelow) (a n : ℤ) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, F.pageCycles r a n = F.limitCycles a n := by
  obtain ⟨r₀, hr₀⟩ := F.almost_eventually hF a n
  exact ⟨r₀, fun r hr => congrArg (F.gradedImage a n) (hr₀ r hr)⟩

theorem boundarySource_mono (a n : ℤ) : Monotone (fun r : ℕ => F.boundarySource r a n) := by
  intro r s hrs
  apply inf_le_inf_left
  apply Submodule.map_mono
  apply F.increasing
  omega

theorem pageBoundaries_mono (a n : ℤ) : Monotone (fun r : ℕ => F.pageBoundaries r a n) := by
  intro r s hrs
  exact Submodule.map_mono (Submodule.comap_mono (F.boundarySource_mono a n hrs))

theorem boundarySource_le_filteredCycles (r : ℕ) (a n : ℤ) :
    F.boundarySource r a n ≤ F.filteredCycles a n := by
  rintro x ⟨hx, hy⟩
  exact ⟨hx, F.boundaries_le_cycles n (LinearMap.map_le_range hy)⟩

theorem pageBoundaries_le_limitCycles (r : ℕ) (a n : ℤ) :
    F.pageBoundaries r a n ≤ F.limitCycles a n :=
  Submodule.map_mono (Submodule.comap_mono (F.boundarySource_le_filteredCycles r a n))

theorem limitBoundaries_le_limitCycles (a n : ℤ) : F.limitBoundaries a n ≤ F.limitCycles a n :=
  iSup_le (fun r => F.pageBoundaries_le_limitCycles r a n)

/-- Each boundary preimage occurs at some finite filtration step. -/
theorem boundarySource_union (hF : F.Exhaustive) (a n : ℤ) :
    (⨆ r : ℕ, F.boundarySource r a n) = F.piece a n ⊓ F.boundaries n := by
  apply le_antisymm
  · refine iSup_le (fun r => ?_)
    exact inf_le_inf_left _ LinearMap.map_le_range
  · rintro x ⟨hx, y, rfl⟩
    obtain ⟨k, hk⟩ := hF (n+1) y
    obtain ⟨r, hr⟩ : ∃ r : ℕ, k-a+1 ≤ (r:ℤ) := exists_nat_ge (k-a+1)
    exact Submodule.mem_iSup_of_mem r ⟨hx, y, F.increasing _ (by omega) hk, rfl⟩

/-- Directed union commutes with projection to the graded module. -/
theorem limitBoundaries_eq (hF : F.Exhaustive) (a n : ℤ) :
    F.limitBoundaries a n = F.gradedImage a n (F.piece a n ⊓ F.boundaries n) := by
  apply le_antisymm
  · refine iSup_le (fun r => ?_)
    apply Submodule.map_mono
    apply Submodule.comap_mono
    exact inf_le_inf_left _ LinearMap.map_le_range
  · rintro z ⟨x, hx, rfl⟩
    have hx' : x.1 ∈ ⨆ r : ℕ, F.boundarySource r a n := by
      rw [F.boundarySource_union hF a n]
      exact hx
    obtain ⟨r, hr⟩ := (Submodule.mem_iSup_of_directed _
      (F.boundarySource_mono a n).directed_le).1 hx'
    exact Submodule.mem_iSup_of_mem r ⟨x, hr, rfl⟩

theorem homologyFiltration_mono (n : ℤ) : Monotone (fun a => F.homologyFiltration a n) := by
  intro a b hab
  exact Submodule.map_mono (Submodule.comap_mono (F.increasing n hab))

theorem homologyFiltration_boundedBelow (hF : F.BoundedBelow) (n : ℤ) :
    ∃ l : ℤ, ∀ a < l, F.homologyFiltration a n = ⊥ := by
  obtain ⟨l, hl⟩ := hF n
  refine ⟨l, fun a ha => ?_⟩
  apply le_antisymm _ bot_le
  rintro x ⟨z, hz, rfl⟩
  have hz' : z.1 = 0 := by simpa [hl a ha] using hz
  have : z = 0 := Subtype.ext hz'
  simp [this]

theorem homologyFiltration_exhaustive (hF : F.Exhaustive) (n : ℤ) (x : F.homology n) :
    ∃ a : ℤ, x ∈ F.homologyFiltration a n := by
  obtain ⟨z, rfl⟩ := (F.cycleBoundary n).mkQ_surjective x
  obtain ⟨a, ha⟩ := hF n z.1
  exact ⟨a, z, ha, rfl⟩

/-- A class in the eventual numerator has a closed representative in `F_a`. -/
theorem toInfinity_surjective (a n : ℤ) : Function.Surjective (F.toInfinity a n) := by
  intro z
  obtain ⟨z, rfl⟩ := ((F.limitBoundaries a n).comap (F.limitCycles a n).subtype).mkQ_surjective z
  obtain ⟨x, hx, he⟩ := z.2
  refine ⟨⟨x.1, hx⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk z
  congr 1
  exact Subtype.ext he

theorem toHomologyGraded_surjective (a n : ℤ) :
    Function.Surjective (F.toHomologyGraded a n) := by
  intro z
  obtain ⟨z, rfl⟩ := ((F.homologyFiltration (a-1) n).comap
    (F.homologyFiltration a n).subtype).mkQ_surjective z
  obtain ⟨x, hx, he⟩ := z.2
  refine ⟨⟨x.1, hx, x.2⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk z
  congr 1
  exact Subtype.ext he

/-- Both quotient constructions have precisely the same relation on closed
representatives: changing the representative by a lower cycle and a boundary. -/
theorem toInfinity_eq_zero_iff (hF : F.Exhaustive) (a n : ℤ)
    (x : F.filteredCycles a n) :
    F.toInfinity a n x = 0 ↔ ∃ z : F.cycles n,
      z.1 ∈ F.piece (a-1) n ∧ x.1-z.1 ∈ F.boundaries n := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change F.gradedProjection a n ⟨x.1, x.2.1⟩ ∈ F.limitBoundaries a n ↔ _
  rw [F.limitBoundaries_eq hF a n]
  constructor
  · rintro ⟨y, hy, he⟩
    have hxy : x.1-y.1 ∈ F.piece (a-1) n := by
      have hh := (Submodule.Quotient.eq (F.lower a n)).1 he
      change y.1-x.1 ∈ F.piece (a-1) n at hh
      simpa only [neg_sub] using (F.piece (a-1) n).neg_mem hh
    have hyc := F.boundaries_le_cycles n hy.2
    refine ⟨⟨x.1-y.1, (F.cycles n).sub_mem x.2.2 hyc⟩, hxy, ?_⟩
    simpa only [sub_sub_cancel] using (show y.1 ∈ F.boundaries n from hy.2)
  · rintro ⟨z, hz, hb⟩
    have hza : z.1 ∈ F.piece a n := F.increasing n (by omega) hz
    refine ⟨⟨x.1-z.1, (F.piece a n).sub_mem x.2.1 hza⟩,
      ⟨(F.piece a n).sub_mem x.2.1 hza, hb⟩, ?_⟩
    apply (Submodule.Quotient.eq (F.lower a n)).2
    change (x.1-z.1)-x.1 ∈ F.piece (a-1) n
    simpa only [sub_sub_cancel_left] using (F.piece (a-1) n).neg_mem hz

theorem toHomologyGraded_eq_zero_iff (a n : ℤ) (x : F.filteredCycles a n) :
    F.toHomologyGraded a n x = 0 ↔ ∃ z : F.cycles n,
      z.1 ∈ F.piece (a-1) n ∧ x.1-z.1 ∈ F.boundaries n := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change F.classMap n ⟨x.1, x.2.2⟩ ∈ F.homologyFiltration (a-1) n ↔ _
  constructor
  · rintro ⟨z, hz, he⟩
    refine ⟨z, hz, ?_⟩
    have hh := (Submodule.Quotient.eq (F.cycleBoundary n)).1 he
    change z.1-x.1 ∈ F.boundaries n at hh
    simpa only [neg_sub] using (F.boundaries n).neg_mem hh
  · rintro ⟨z, hz, hb⟩
    refine ⟨z, hz, ?_⟩
    apply (Submodule.Quotient.eq (F.cycleBoundary n)).2
    change z.1-x.1 ∈ F.boundaries n
    simpa only [neg_sub] using (F.boundaries n).neg_mem hb

theorem limit_kernel_eq (hF : F.Exhaustive) (a n : ℤ) :
    LinearMap.ker (F.toInfinity a n) = LinearMap.ker (F.toHomologyGraded a n) := by
  ext x
  exact (F.toInfinity_eq_zero_iff hF a n x).trans (F.toHomologyGraded_eq_zero_iff a n x).symm

/-- Canonical convergence isomorphism. The lower bound is needed for eventual
cycles, whereas this quotient identification itself only uses exhaustivity. -/
def convergenceIso (hF : F.Exhaustive) (a n : ℤ) :
    F.infinity a n ≃ₗ[R] F.homologyGraded a n :=
  ((F.toInfinity a n).quotKerEquivOfSurjective (F.toInfinity_surjective a n)).symm |>.trans
    ((Submodule.quotEquivOfEq _ _ (F.limit_kernel_eq hF a n)).trans
      ((F.toHomologyGraded a n).quotKerEquivOfSurjective (F.toHomologyGraded_surjective a n)))

@[simp]
theorem convergenceIso_representative (hF : F.Exhaustive) (a n : ℤ)
    (x : F.filteredCycles a n) :
    F.convergenceIso hF a n (F.toInfinity a n x) = F.toHomologyGraded a n x := by
  simp [convergenceIso]

def limitData (hb : F.BoundedBelow) (he : F.Exhaustive) : F.LimitData where
  eventual_cycles := F.pageCycles_eventually hb
  increasing_boundaries := F.pageBoundaries_mono
  boundary_union := F.limitBoundaries_eq he
  boundary_containment := F.limitBoundaries_le_limitCycles
  homology_increasing := F.homologyFiltration_mono
  homology_boundedBelow := F.homologyFiltration_boundedBelow hb
  homology_exhaustive := F.homologyFiltration_exhaustive he
  iso := F.convergenceIso he
  representative_formula := F.convergenceIso_representative he

variable {D : ChainComplex (ModuleCat.{v} R) ℤ} (G : ExhaustiveChain.Filtration D)

lemma map_boundary (f : C ⟶ D) (n : ℤ) {x : C.X n} (hx : x ∈ F.boundaries n) :
    (f.f n).hom x ∈ G.boundaries n := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(f.f (n+1)).hom y, ?_⟩
  exact congrArg (fun g : C.X (n+1) ⟶ D.X n => g.hom y) (f.comm (n+1) n)

lemma homologyGraded_map_kernel (f : C ⟶ D)
    (hf : ∀ a n, F.piece a n ≤ (G.piece a n).comap (f.f n).hom) (a n : ℤ) :
    LinearMap.ker (F.toHomologyGraded a n) ≤
      LinearMap.ker ((G.toHomologyGraded a n).comp (closedMap F G f hf a n)) := by
  intro x hx
  obtain ⟨z, hz, hb⟩ := (F.toHomologyGraded_eq_zero_iff a n x).1 hx
  let w := closedMap F G f hf (a-1) n ⟨z.1, hz, z.2⟩
  apply (G.toHomologyGraded_eq_zero_iff a n _).2
  refine ⟨⟨w.1, w.2.2⟩, w.2.1, ?_⟩
  simpa only [w, closedMap, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.coe_subtype, map_sub] using F.map_boundary G f n hb

end ExhaustiveChain.Filtration

theorem exhaustive_chain_pages : S02Specs.FinitePages.{u,v} := by
  intro R _ C F
  obtain ⟨D, ⟨N⟩⟩ := filtered_page_cohomology F.cochainFiltration
  exact ⟨{
    pages := D
    next := N
    gradedIso := F.cochainGradedIso
    projection_formula := F.cochainGradedIso_projection
    cycles_formula := F.cochain_cycles_formula
    boundaries_formula := F.cochain_boundaries_formula }⟩

theorem exhaustive_chain_limit : S02Specs.LimitStatement.{u,v} := by
  intro R _ C F hb he
  exact ⟨F.limitData hb he⟩

theorem exhaustive_chain_limit_natural : S02Specs.Naturality.{u,v} := by
  intro R _ C D F G f hf LF LG a n
  let g := (G.toHomologyGraded a n).comp (ExhaustiveChain.closedMap F G f hf a n)
  let h : F.homologyGraded a n →ₗ[R] G.homologyGraded a n :=
    (F.toHomologyGraded a n).liftOfSurjective (F.toHomologyGraded_surjective a n)
      ⟨g, F.homologyGraded_map_kernel G f hf a n⟩
  have hh (x : F.filteredCycles a n) : h (F.toHomologyGraded a n x) =
      G.toHomologyGraded a n (ExhaustiveChain.closedMap F G f hf a n x) :=
    LinearMap.equivOfSurjective_apply (F.toHomologyGraded_surjective a n) _
  let i : F.infinity a n →ₗ[R] G.infinity a n :=
    (LG.iso a n).symm.toLinearMap.comp (h.comp (LF.iso a n).toLinearMap)
  refine ⟨i, h, ?_, hh, ?_⟩
  · intro x
    apply (LG.iso a n).injective
    simpa only [i, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LF.representative_formula, LG.representative_formula] using hh x
  · intro x
    exact (LG.iso a n).apply_symm_apply _

/-- HA-S02: all homological pages, eventual cycle numerators, union of
boundaries, natural graded homology identification, and target filtration bounds. -/
theorem exhaustive_chain_convergence : S02Specs.FullStatement.{u,v} :=
  ⟨exhaustive_chain_pages, exhaustive_chain_limit, exhaustive_chain_limit_natural⟩

end AdvancedHomologicalAlgebra
