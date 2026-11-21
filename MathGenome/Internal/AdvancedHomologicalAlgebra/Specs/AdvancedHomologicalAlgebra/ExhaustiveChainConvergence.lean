import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.PageCohomology
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Span.Basic

/-! HA-S02 (source lines 455–498). All module structures are left module
structures over an arbitrary, possibly noncommutative, ring. The total chain
degree is `n`; the complementary page degree is `b = n-a`.

The concrete homology below is the ordinary cycles modulo boundaries. Finite
page numerators and boundaries are submodules of `F_a C_n / F_(a-1) C_n`.
No boundary stabilization, separation, completeness, or uniform bounds occur.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe u v
namespace AdvancedHomologicalAlgebra
namespace ExhaustiveChain
variable {R : Type u} [Ring R]

structure Filtration (C : ChainComplex (ModuleCat.{v} R) ℤ) where
  piece : ∀ a n : ℤ, Submodule R (C.X n)
  increasing : ∀ n, Monotone (fun a => piece a n)
  preserved : ∀ a n, piece a n ≤ (piece a (n-1)).comap (C.d n (n-1)).hom

variable {C : ChainComplex (ModuleCat.{v} R) ℤ}

namespace Filtration
variable (F : Filtration C)

def BoundedBelow : Prop := ∀ n, ∃ l : ℤ, ∀ a < l, F.piece a n = ⊥
def Exhaustive : Prop := ∀ n (x : C.X n), ∃ a : ℤ, x ∈ F.piece a n

abbrev d (_F : Filtration C) (n : ℤ) := (C.d n (n-1)).hom
abbrev cycles (n : ℤ) : Submodule R (C.X n) := LinearMap.ker (F.d n)
abbrev boundaries (_F : Filtration C) (n : ℤ) : Submodule R (C.X n) := LinearMap.range (C.d (n+1) n).hom

theorem boundaries_le_cycles (n : ℤ) : F.boundaries n ≤ F.cycles n := by
  rintro _ ⟨x, rfl⟩
  change (C.d n (n-1)).hom ((C.d (n+1) n).hom x) = 0
  have h := congrArg (fun f : C.X (n+1) ⟶ C.X (n-1) => f.hom x) (C.d_comp_d (n+1) n (n-1))
  exact h

abbrev cycleBoundary (n : ℤ) : Submodule R (F.cycles n) :=
  (F.boundaries n).comap (F.cycles n).subtype
abbrev homology (n : ℤ) := F.cycles n ⧸ F.cycleBoundary n
abbrev classMap (n : ℤ) : F.cycles n →ₗ[R] F.homology n := (F.cycleBoundary n).mkQ
abbrev filteredCycles (a n : ℤ) := F.piece a n ⊓ F.cycles n
abbrev homologyFiltration (a n : ℤ) : Submodule R (F.homology n) :=
  ((F.piece a n).comap (F.cycles n).subtype).map (F.classMap n)

abbrev lower (a n : ℤ) : Submodule R (F.piece a n) :=
  (F.piece (a-1) n).comap (F.piece a n).subtype
abbrev graded (a n : ℤ) := F.piece a n ⧸ F.lower a n
abbrev gradedProjection (a n : ℤ) : F.piece a n →ₗ[R] F.graded a n := (F.lower a n).mkQ

abbrev almost (r : ℕ) (a n : ℤ) : Submodule R (C.X n) :=
  F.piece a n ⊓ (F.piece (a-(r:ℤ)) (n-1)).comap (F.d n)
abbrev boundarySource (r : ℕ) (a n : ℤ) : Submodule R (C.X n) :=
  F.piece a n ⊓ (F.piece (a+(r:ℤ)-1) (n+1)).map (C.d (n+1) n).hom
abbrev gradedImage (a n : ℤ) (S : Submodule R (C.X n)) : Submodule R (F.graded a n) :=
  (S.comap (F.piece a n).subtype).map (F.gradedProjection a n)
abbrev pageCycles (r : ℕ) (a n : ℤ) := F.gradedImage a n (F.almost r a n)
abbrev pageBoundaries (r : ℕ) (a n : ℤ) := F.gradedImage a n (F.boundarySource r a n)
abbrev limitCycles (a n : ℤ) := F.gradedImage a n (F.filteredCycles a n)
abbrev limitBoundaries (a n : ℤ) : Submodule R (F.graded a n) := ⨆ r : ℕ, F.pageBoundaries r a n
abbrev infinity (a n : ℤ) := F.limitCycles a n ⧸
  (F.limitBoundaries a n).comap (F.limitCycles a n).subtype
abbrev homologyGraded (a n : ℤ) := F.homologyFiltration a n ⧸
  (F.homologyFiltration (a-1) n).comap (F.homologyFiltration a n).subtype

/-- The common closed-representative map into the limiting page. -/
def toInfinity (a n : ℤ) : F.filteredCycles a n →ₗ[R] F.infinity a n :=
  ((F.limitBoundaries a n).comap (F.limitCycles a n).subtype).mkQ.comp
    (LinearMap.codRestrict (F.limitCycles a n)
      ((F.gradedProjection a n).comp (Submodule.inclusion inf_le_left)) (fun x =>
        ⟨⟨x.1, x.2.1⟩, x.2, rfl⟩))

/-- The same closed representative, in the associated graded of homology. -/
def toHomologyGraded (a n : ℤ) : F.filteredCycles a n →ₗ[R] F.homologyGraded a n :=
  ((F.homologyFiltration (a-1) n).comap (F.homologyFiltration a n).subtype).mkQ.comp
    (LinearMap.codRestrict (F.homologyFiltration a n)
      ((F.classMap n).comp (Submodule.inclusion inf_le_right)) (fun x =>
        ⟨⟨x.1, x.2.2⟩, x.2.1, rfl⟩))

/-- Reverse both degree and filtration indices, with no sign change to `d`. -/
def cochain (_F : Filtration C) : CochainComplex (ModuleCat.{v} R) ℤ where
  X n := C.X (-n)
  d i j := C.d (-i) (-j)
  shape i j h := C.shape _ _ (by
    change ¬ (i+1=j) at h
    change ¬ (-j)+1 = -i
    omega)
  d_comp_d' i j k _ _ := C.d_comp_d _ _ _

def cochainFiltration : AdvancedHomologicalAlgebra.Filtration F.cochain where
  piece p n := Subobject.mk (ModuleCat.ofHom (F.piece (-p) (-n)).subtype)
  decreasing p n := Subobject.mk_le_mk_of_comm
    (ModuleCat.ofHom (Submodule.inclusion (F.increasing (-n) (by omega : -(p+1) ≤ -p)))) rfl
  preserved p i j := by
    by_cases h : i+1=j
    · subst j
      let f : F.piece (-p) (-i) →ₗ[R] F.piece (-p) (-(i+1)) :=
        ((C.d (-i) (-(i+1))).hom.comp (F.piece (-p) (-i)).subtype).codRestrict _ (by
          intro x
          have hx := F.preserved (-p) (-i) x.2
          change (C.d (-i) (-(i+1))).hom x.1 ∈ F.piece (-p) (-(i+1))
          rw [show -(i+1) = -i-1 by omega]
          exact hx)
      refine ⟨(Subobject.underlyingIso _).hom ≫ ModuleCat.ofHom f ≫
        (Subobject.underlyingIso _).inv, ?_⟩
      simp only [Category.assoc, Subobject.underlyingIso_arrow]
      rw [← Subobject.underlyingIso_hom_comp_eq_mk
        (ModuleCat.ofHom (F.piece (-p) (-i)).subtype)]
      rfl
    · refine ⟨0, ?_⟩
      rw [F.cochain.shape i j h, comp_zero, zero_comp]

/-- Canonical identification of a categorical filtration step with its
concrete submodule. The intermediate form avoids casts in the ambient degree. -/
def cochainStepIso (p n : ℤ) : (F.cochainFiltration.step p).X n ≅
    ModuleCat.of R (F.piece (-p) (-n)) :=
  Subobject.underlyingIso (ModuleCat.ofHom (F.piece (-p) (-n)).subtype)

/-- The homological spectral sequence, using exactly the upstream categorical
pages after reversing indices. The two submodule equations identify its cycle
numerators and boundaries with the concrete formulas used for the limit. -/
structure SpectralSequence where
  pages : F03Specs.PageData F.cochainFiltration
  next : PageCohomology.Data F.cochainFiltration pages
  gradedIso : ∀ p n, ModuleCat.of R (F.graded (-p) (-n)) ≅ (F.cochainFiltration.graded p).X n
  projection_formula : ∀ p n,
    ModuleCat.ofHom (F.gradedProjection (-p) (-n)) ≫ (gradedIso p n).hom =
      (F.cochainStepIso p n).inv ≫ (F.cochainFiltration.projection p).f n
  cycles_formula : ∀ (r : ℕ) p n,
    (F.pageCycles r (-p) (-n)).map (gradedIso p n).hom.hom =
      ModuleCat.subobjectModule _ (FilteredPage.cycles F.cochainFiltration (r:ℤ) p n)
  boundaries_formula : ∀ (r : ℕ) p n,
    (F.pageBoundaries r (-p) (-n)).map (gradedIso p n).hom.hom =
      ModuleCat.subobjectModule _ (FilteredPage.boundaries F.cochainFiltration (r:ℤ) p n)

namespace SpectralSequence
variable {F} (S : F.SpectralSequence)

/-- Actual homological bidegrees: `E^r_(a,b)` has total degree `a+b`. -/
abbrev page (r : ℕ) (a b : ℤ) : ModuleCat.{v} R :=
  PageCohomology.object F.cochainFiltration S.pages (r:ℤ) (-a) (-(a+b))

/-- The upstream differential, explicitly reindexed to `(-r,r-1)`. -/
def differential (r : ℕ) (a b : ℤ) :
    S.page r a b ⟶ S.page r (a-(r:ℤ)) (b+(r:ℤ)-1) :=
  S.pages.differential (r:ℤ) (Int.natCast_nonneg r) (-a) (-(a+b)) ≫
    eqToHom (congrArg₂ (fun p n => PageCohomology.object F.cochainFiltration S.pages (r:ℤ) p n)
      (by omega : -a+(r:ℤ) = -(a-(r:ℤ)))
      (by omega : -(a+b)+1 = -((a-(r:ℤ))+(b+(r:ℤ)-1))))
end SpectralSequence

/-- The full limit assertion, with a canonical representative formula. -/
structure LimitData where
  eventual_cycles : ∀ a n, ∃ r₀ : ℕ, ∀ r ≥ r₀, F.pageCycles r a n = F.limitCycles a n
  increasing_boundaries : ∀ a n, Monotone (fun r : ℕ => F.pageBoundaries r a n)
  boundary_union : ∀ a n, F.limitBoundaries a n = F.gradedImage a n (F.piece a n ⊓ F.boundaries n)
  boundary_containment : ∀ a n, F.limitBoundaries a n ≤ F.limitCycles a n
  homology_increasing : ∀ n, Monotone (fun a => F.homologyFiltration a n)
  homology_boundedBelow : ∀ n, ∃ l : ℤ, ∀ a < l, F.homologyFiltration a n = ⊥
  homology_exhaustive : ∀ n (x : F.homology n), ∃ a, x ∈ F.homologyFiltration a n
  iso : ∀ a n, F.infinity a n ≃ₗ[R] F.homologyGraded a n
  representative_formula : ∀ a n (x : F.filteredCycles a n),
    iso a n (F.toInfinity a n x) = F.toHomologyGraded a n x

end Filtration
variable {D : ChainComplex (ModuleCat.{v} R) ℤ}

/-- Restriction of a filtered chain map to closed representatives. -/
def closedMap (F : Filtration C) (G : Filtration D) (f : C ⟶ D)
    (hf : ∀ a n, F.piece a n ≤ (G.piece a n).comap (f.f n).hom) (a n : ℤ) :
    F.filteredCycles a n →ₗ[R] G.filteredCycles a n :=
  ((f.f n).hom.comp (F.filteredCycles a n).subtype).codRestrict _ (by
    intro x
    refine ⟨hf a n x.2.1, ?_⟩
    change (D.d n (n-1)).hom ((f.f n).hom x.1) = 0
    have h := congrArg (fun g : C.X n ⟶ D.X (n-1) => g.hom x.1) (f.comm n (n-1))
    change (D.d n (n-1)).hom ((f.f n).hom x.1) = (f.f (n-1)).hom ((C.d n (n-1)).hom x.1) at h
    rw [h, show (C.d n (n-1)).hom x.1 = 0 from x.2.2, map_zero])

end ExhaustiveChain

namespace S02Specs
open ExhaustiveChain

def FinitePages : Prop := ∀ {R : Type u} [Ring R]
  {C : ChainComplex (ModuleCat.{v} R) ℤ} (F : ExhaustiveChain.Filtration C), Nonempty F.SpectralSequence

def LimitStatement : Prop := ∀ {R : Type u} [Ring R]
  {C : ChainComplex (ModuleCat.{v} R) ℤ} (F : ExhaustiveChain.Filtration C),
  F.BoundedBelow → F.Exhaustive → Nonempty F.LimitData

/-- Naturality is required for every canonical identification, since the
representative equation determines each identification uniquely. The two
induced maps are characterized by their values on all closed representatives. -/
def Naturality : Prop := ∀ {R : Type u} [Ring R]
  {C D : ChainComplex (ModuleCat.{v} R) ℤ} (F : ExhaustiveChain.Filtration C) (G : ExhaustiveChain.Filtration D)
  (f : C ⟶ D) (hf : ∀ a n, F.piece a n ≤ (G.piece a n).comap (f.f n).hom)
  (LF : F.LimitData) (LG : G.LimitData) (a n : ℤ),
  ∃ (i : F.infinity a n →ₗ[R] G.infinity a n)
    (h : F.homologyGraded a n →ₗ[R] G.homologyGraded a n),
    (∀ x, i (F.toInfinity a n x) = G.toInfinity a n (closedMap F G f hf a n x)) ∧
    (∀ x, h (F.toHomologyGraded a n x) = G.toHomologyGraded a n (closedMap F G f hf a n x)) ∧
    (∀ x, LG.iso a n (i x) = h (LF.iso a n x))

def FullStatement : Prop := FinitePages.{u,v} ∧ LimitStatement.{u,v} ∧ Naturality.{u,v}
end S02Specs

end AdvancedHomologicalAlgebra
