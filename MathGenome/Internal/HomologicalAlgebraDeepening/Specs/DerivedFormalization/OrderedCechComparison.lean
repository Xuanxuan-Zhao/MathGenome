import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Fin

/-! The full and increasing Čech complexes with the original coefficient modules. -/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.Cech AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.CechSequenceOriginal

namespace Specs.DerivedFormalization.OrderedCechComparison

universe u r v w

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
  {U : Opens X} {I : Type v} [LinearOrder I] (c : Cover U I)
  (F : PresheafOfModules.{w} R.obj)

/-- A degree-`p` ordered index consists of `p+1` strictly increasing vertices. -/
abbrev IncreasingTuple (I : Type v) [LinearOrder I] (p : ℕ) :=
  { t : Fin (p + 1) → I // StrictMono t }

/-- Sections on the intersections of increasing tuples, over the section ring of `U`. -/
abbrev IncreasingCochains (p : ℕ) :=
  (t : IncreasingTuple I p) →
    localSections R F U (tupleOpen c t.1) (tupleOpen_le c t.1)

def projectionComponent (p : ℕ) :
    Cochains R F c p →ₗ[sectionRing R U] IncreasingCochains R c F p :=
  LinearMap.pi fun t => LinearMap.proj t.1

private def extendByZero (p : ℕ) :
    IncreasingCochains R c F p →ₗ[sectionRing R U] Cochains R F c p :=
  LinearMap.pi fun t => if h : StrictMono t then LinearMap.proj (⟨t, h⟩ : IncreasingTuple I p) else 0

/-- Alternate restriction along the faces of each increasing tuple. Every face
is again increasing, so the zero extension contributes only those face values. -/
def increasingDifferential (p : ℕ) :
    IncreasingCochains R c F p →ₗ[sectionRing R U] IncreasingCochains R c F (p + 1) :=
  (projectionComponent R c F (p + 1)).comp
    ((differential R F c p).comp (extendByZero R c F p))

theorem increasingDifferential_apply (p : ℕ) (x : IncreasingCochains R c F p)
    (t : IncreasingTuple I (p + 1)) :
    increasingDifferential R c F p x t =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val •
        localRestriction R F U (tupleOpen_le c t.1)
          (tupleOpen_le c (t.1 ∘ i.succAbove)) (tupleOpen_reindex_le c i.succAbove t.1)
          (x ⟨t.1 ∘ i.succAbove, t.2.comp i.strictMono_succAbove⟩) := by
  simp only [increasingDifferential, LinearMap.comp_apply, projectionComponent,
    LinearMap.pi_apply, LinearMap.proj_apply, differential, LinearMap.sum_apply,
    Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : StrictMono (t.1 ∘ i.succAbove) := t.2.comp i.strictMono_succAbove
  simp [reindex, extendByZero, h]

theorem projectionComponent_surjective (p : ℕ) :
    Function.Surjective (projectionComponent R c F p) := by
  intro x
  refine ⟨extendByZero R c F p x, ?_⟩
  funext t
  simp [projectionComponent, extendByZero, t.2]

theorem projection_comm (p : ℕ) :
    (increasingDifferential R c F p).comp (projectionComponent R c F p) =
      (projectionComponent R c F (p + 1)).comp (differential R F c p) := by
  ext x t
  simp only [increasingDifferential, LinearMap.comp_apply, projectionComponent,
    LinearMap.pi_apply, LinearMap.proj_apply, differential, LinearMap.sum_apply,
    Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : StrictMono (t.1 ∘ i.succAbove) := t.2.comp i.strictMono_succAbove
  simp [reindex, extendByZero, h]

theorem projection_comm_apply (p : ℕ) (x : Cochains R F c p) :
    increasingDifferential R c F p (projectionComponent R c F p x) =
      projectionComponent R c F (p + 1) (differential R F c p x) :=
  LinearMap.congr_fun (projection_comm R c F p) x

/-- The increasing-index Čech complex in ordinary nonnegative cochain degrees. -/
def increasingComplex : CochainComplex (ModuleCat.{max w v} (sectionRing R U)) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of _ (IncreasingCochains R c F p))
    (fun p => ModuleCat.ofHom (increasingDifferential R c F p)) (by
      intro p
      have h := (orderedCochainComplex R c F).d_comp_d p (p + 1) (p + 2)
      rw [orderedCochainComplex_d, orderedCochainComplex_d] at h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := projectionComponent_surjective R c F p x
      change increasingDifferential R c F (p + 1)
          (increasingDifferential R c F p (projectionComponent R c F p y)) = 0
      rw [projection_comm_apply, projection_comm_apply]
      have hy := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) y
      change differential R F c (p + 1) (differential R F c p y) = 0 at hy
      rw [hy, map_zero])

@[simp]
theorem increasingComplex_d (p : ℕ) :
    (increasingComplex R c F).d p (p + 1) = ModuleCat.ofHom (increasingDifferential R c F p) := by
  simp only [increasingComplex, CochainComplex.of_d]

/-- Restrict a full cochain to increasing tuples. Its source is the raw complex
used in MathGenome's acyclic-cover comparison. -/
def projection : orderedCochainComplex R c F ⟶ increasingComplex R c F :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (projectionComponent R c F p)) (by
    intro p
    rw [orderedCochainComplex_d]
    simp only [increasingComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact projection_comm R c F p)

theorem tupleOpen_sort {p : ℕ} (t : Fin (p + 1) → I) :
    tupleOpen c t ≤ tupleOpen c (t ∘ Tuple.sort t) :=
  tupleOpen_reindex_le c (Tuple.sort t) t

/-- Extend an increasing cochain by the sign of the sorting permutation.
At tuples with any repeated entry the extension is zero, over every ring. -/
def signedExtensionComponent (p : ℕ) :
    IncreasingCochains R c F p →ₗ[sectionRing R U] Cochains R F c p :=
  LinearMap.pi fun t =>
    if ht : Function.Injective t then
      let e : IncreasingTuple I p :=
        ⟨t ∘ Tuple.sort t, (Tuple.monotone_sort t).strictMono_of_injective
          (ht.comp (Tuple.sort t).injective)⟩
      (↑(Equiv.Perm.sign (Tuple.sort t)) : ℤ) •
        (localRestriction R F U (tupleOpen_le c t) (tupleOpen_le c e.1)
          (tupleOpen_sort c t)).comp (LinearMap.proj e)
    else 0

variable {F} {G : PresheafOfModules.{w} R.obj}

/-- The coefficient map on an increasing cochain is the map on each section. -/
def increasingMapComponent (f : F ⟶ G) (p : ℕ) :
    IncreasingCochains R c F p →ₗ[sectionRing R U] IncreasingCochains R c G p :=
  (projectionComponent R c G p).comp
    ((orderedCochainComponent R c f p).comp (extendByZero R c F p))

theorem increasingMap_projection (f : F ⟶ G) (p : ℕ) :
    (increasingMapComponent R c f p).comp (projectionComponent R c F p) =
      (projectionComponent R c G p).comp (orderedCochainComponent R c f p) := by
  ext x t
  simp [increasingMapComponent, projectionComponent, orderedCochainComponent,
    extendByZero, t.2]
  rfl

theorem increasingMap_projection_apply (f : F ⟶ G) (p : ℕ) (x : Cochains R F c p) :
    increasingMapComponent R c f p (projectionComponent R c F p x) =
      projectionComponent R c G p (orderedCochainComponent R c f p x) :=
  LinearMap.congr_fun (increasingMap_projection R c f p) x

def increasingMap (f : F ⟶ G) :
    increasingComplex R c F ⟶ increasingComplex R c G :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (increasingMapComponent R c f p)) (by
    intro p
    have h := (orderedCochainMap R c f).comm p (p + 1)
    rw [orderedCochainComplex_d, orderedCochainComplex_d] at h
    simp only [increasingComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := projectionComponent_surjective R c F p x
    change increasingDifferential R c G p
        (increasingMapComponent R c f p (projectionComponent R c F p y)) =
      increasingMapComponent R c f (p + 1)
        (increasingDifferential R c F p (projectionComponent R c F p y))
    rw [increasingMap_projection_apply, projection_comm_apply, projection_comm_apply,
      increasingMap_projection_apply]
    exact congrArg (projectionComponent R c G (p + 1))
      (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) y))

/-- The specified maps give a coefficient-natural deformation retraction.
The homotopy is natural in every morphism of coefficient presheaves. -/
def Comparison : Prop :=
  ∃ (s : ∀ F : PresheafOfModules.{w} R.obj,
          increasingComplex R c F ⟶ orderedCochainComplex R c F),
    (∀ F p, (s F).f p = ModuleCat.ofHom (signedExtensionComponent R c F p)) ∧
    (∀ F, s F ≫ projection R c F = 𝟙 _) ∧
    (∀ (F G : PresheafOfModules.{w} R.obj) (f : F ⟶ G),
      orderedCochainMap R c f ≫ projection R c G =
        projection R c F ≫ increasingMap R c f) ∧
    (∀ (F G : PresheafOfModules.{w} R.obj) (f : F ⟶ G),
      increasingMap R c f ≫ s G = s F ≫ orderedCochainMap R c f) ∧
    ∃ H : ∀ F, Homotopy (𝟙 _) (projection R c F ≫ s F),
      ∀ F G (f : F ⟶ G) p q,
        (orderedCochainMap R c f).f p ≫ (H G).hom p q =
          (H F).hom p q ≫ (orderedCochainMap R c f).f q

def comparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {I : Type v}
    [LinearOrder I] [Finite I] (c : Cover U I), Comparison.{u,r,v,w} R c

end Specs.DerivedFormalization.OrderedCechComparison
