import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.Basic

open CategoryTheory Opposite

universe u v

namespace LinearAlgebraicGroups.Specs.ProjectiveFiniteChartPresentations

/-- Nonempty coordinate sets, with arrows in the direction of restriction. -/
abbrev Chart (ι : Type v) := ({s : Finset ι // s.Nonempty}ᵒᵈ)ᵒᵖ

namespace Chart

variable {ι : Type v}

def indices (S : Chart ι) : Finset ι := S.unop.ofDual.val

theorem nonempty (S : Chart ι) : S.indices.Nonempty := S.unop.ofDual.property

def ofFinset (s : Finset ι) (h : s.Nonempty) : Chart ι := op (OrderDual.toDual ⟨s, h⟩)

def single (i : ι) : Chart ι := ofFinset {i} (Finset.singleton_nonempty i)

theorem mem_single (i : ι) : i ∈ (single i).indices := Finset.mem_singleton_self i

def hom {S T : Chart ι} (h : S.indices ⊆ T.indices) : S ⟶ T := (homOfLE h).op

theorem subset {S T : Chart ι} (f : S ⟶ T) : S.indices ⊆ T.indices := f.unop.le

def adjoin [DecidableEq ι] (S : Chart ι) (i : ι) : Chart ι :=
  ofFinset (insert i S.indices) ⟨i, Finset.mem_insert_self _ _⟩

def toAdjoin [DecidableEq ι] (S : Chart ι) (i : ι) : S ⟶ S.adjoin i :=
  hom (Finset.subset_insert _ _)

theorem mem_adjoin [DecidableEq ι] (S : Chart ι) (i : ι) :
    i ∈ (S.adjoin i).indices := Finset.mem_insert_self _ _

def fromSingle {S : Chart ι} {i : ι} (hi : i ∈ S.indices) : single i ⟶ S :=
  hom (Finset.singleton_subset_iff.mpr hi)

end Chart

/-- The rings of the intersections, their structural scalars, and coordinate ratios. -/
structure ChartRings (k : Type u) [CommRing k] (ι : Type v) [DecidableEq ι] where
  rings : Chart ι ⥤ CommRingCat.{u}
  scalars : (Functor.const (Chart ι)).obj (CommRingCat.of k) ⟶ rings
  noetherian (i : ι) : IsNoetherianRing (rings.obj (Chart.single i))
  ratio (S : Chart ι) (i j : ι) (hj : j ∈ S.indices) : rings.obj S
  ratio_self (S : Chart ι) (j : ι) (hj : j ∈ S.indices) : ratio S j j hj = 1
  ratio_mul (S : Chart ι) (i j l : ι) (hj : j ∈ S.indices) (hl : l ∈ S.indices) :
    ratio S i j hj * ratio S j l hl = ratio S i l hl
  ratio_map {S T : Chart ι} (f : S ⟶ T) (i j : ι) (hj : j ∈ S.indices) :
    rings.map f (ratio S i j hj) = ratio T i j (Chart.subset f hj)
  localizes (S : Chart ι) (i j : ι) (hj : j ∈ S.indices) :
    letI := (rings.map (S.toAdjoin i)).hom.toAlgebra
    IsLocalization.Away (ratio S i j hj) (rings.obj (S.adjoin i))

namespace ChartRings

variable {k : Type u} [CommRing k] {ι : Type v} [DecidableEq ι]

abbrev Modules (D : ChartRings k ι) := PresheafOfModules.{u} (D.rings ⋙ forget₂ _ RingCat.{u})

def ratioUnit (D : ChartRings k ι) (S : Chart ι) {i j : ι}
    (hi : i ∈ S.indices) (hj : j ∈ S.indices) : (D.rings.obj S)ˣ where
  val := D.ratio S i j hj
  inv := D.ratio S j i hi
  val_inv := (D.ratio_mul S i j i hj hi).trans (D.ratio_self S i hi)
  inv_val := (D.ratio_mul S j i j hi hj).trans (D.ratio_self S j hj)

def Localizes (D : ChartRings k ι) (M : D.Modules) : Prop :=
  ∀ (S : Chart ι) (i j : ι) (hj : j ∈ S.indices),
    IsLocalizedModule.Away (D.ratio S i j hj) (M.map (S.toAdjoin i)).hom

def FiniteOnSingletons (D : ChartRings k ι) (M : D.Modules) : Prop :=
  ∀ i : ι, Module.Finite (D.rings.obj (Chart.single i)) (M.obj (Chart.single i))

end ChartRings

/-- The basis at an inverted coordinate trivializes the twist on that chart and
on each of its restrictions. On a common restriction the bases differ by the
indicated integer power of the coordinate ratio. -/
structure Twists {k : Type u} [CommRing k] {ι : Type v} [DecidableEq ι]
    (D : ChartRings k ι) where
  diagram (d : ℤ) : D.Modules
  basis (d : ℤ) (S : Chart ι) (i : ι) (hi : i ∈ S.indices) :
    D.rings.obj S ≃ₗ[D.rings.obj S] (diagram d).obj S
  basis_map (d : ℤ) {S T : Chart ι} (f : S ⟶ T) (i : ι) (hi : i ∈ S.indices) :
    (diagram d).map f (basis d S i hi 1) = basis d T i (Chart.subset f hi) 1
  basis_transition (d : ℤ) (S : Chart ι) (i j : ι) (hi : i ∈ S.indices) (hj : j ∈ S.indices) :
    basis d S i hi 1 = ((D.ratioUnit S hi hj ^ d : (D.rings.obj S)ˣ) : D.rings.obj S) •
      basis d S j hj 1
  localizes (d : ℤ) : D.Localizes (diagram d)

section Pointwise

variable {k : Type u} [CommRing k] {ι : Type v} [DecidableEq ι] {D : ChartRings k ι}

set_option backward.isDefEq.respectTransparency false in
/-- The diagram with the product modules and componentwise restrictions. -/
noncomputable def product {A : Type} (M : A → D.Modules) : D.Modules where
  obj S := ModuleCat.of _ ((a : A) → (M a).obj S)
  map {S T} f := ModuleCat.ofHom
    (X := ModuleCat.of (D.rings.obj S) ((a : A) → (M a).obj S))
    (Y := (ModuleCat.restrictScalars (D.rings.map f).hom).obj
      (ModuleCat.of (D.rings.obj T) ((a : A) → (M a).obj T)))
    { toFun := fun x a => (M a).map f (x a)
      map_add' := fun x y => funext fun a => map_add ((M a).map f).hom _ _
      map_smul' := fun r x => funext fun a => (M a).map_smul f r (x a) }
  map_id S := by
    ext x
    funext a
    change (M a).map (𝟙 S) (x a) = x a
    rw [PresheafOfModules.map_id]
    rfl
  map_comp f g := by
    ext x
    funext a
    exact (M a).map_comp_apply f g (x a)

@[simp]
theorem product_map_apply {A : Type} (M : A → D.Modules) {S T : Chart ι} (f : S ⟶ T)
    (x : (product M).obj S) (a : A) :
    (product M).map f x a = (M a).map f (x a) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The diagram of actual linear kernels with the restrictions induced by the
source diagram. -/
noncomputable def kernel {P M : D.Modules} (q : P ⟶ M) : D.Modules where
  obj S := ModuleCat.of _ (LinearMap.ker (q.app S).hom)
  map {S T} f := ModuleCat.ofHom
    (X := ModuleCat.of (D.rings.obj S) (LinearMap.ker (q.app S).hom))
    (Y := (ModuleCat.restrictScalars (D.rings.map f).hom).obj
      (ModuleCat.of (D.rings.obj T) (LinearMap.ker (q.app T).hom)))
    { toFun := fun x => ⟨P.map f x.1, by
        change q.app T (P.map f x.1) = 0
        rw [PresheafOfModules.naturality_apply]
        exact (congrArg (M.map f) x.2).trans (map_zero (M.map f).hom)⟩
      map_add' := fun x y => Subtype.ext (map_add (P.map f).hom _ _)
      map_smul' := fun r x => Subtype.ext (P.map_smul f r x.1) }
  map_id S := by
    ext x
    apply Subtype.ext
    change P.map (𝟙 S) x.1 = x.1
    rw [PresheafOfModules.map_id]
    rfl
  map_comp f g := by
    ext x
    exact Subtype.ext (P.map_comp_apply f g x.1)

set_option backward.isDefEq.respectTransparency false in
/-- The kernel inclusion is given by the submodule inclusions. -/
noncomputable def kernelι {P M : D.Modules} (q : P ⟶ M) : kernel q ⟶ P where
  app S := ModuleCat.ofHom (LinearMap.ker (q.app S).hom).subtype
  naturality f := by ext x; rfl

end Pointwise

/-- An arbitrary finite-on-charts module diagram admits a termwise surjection
from a finite product of the twists, with a finite-on-charts localizing kernel. -/
def FiniteChartPresentations : Prop :=
  ∀ (k : Type u) [CommRing k] (ι : Type v) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (D : ChartRings k ι) (L : Twists D) (M : D.Modules),
    D.FiniteOnSingletons M → D.Localizes M →
    ∃ (n : ℕ) (d : Fin n → ℤ) (q : product (fun a => L.diagram (d a)) ⟶ M),
      (∀ S, Function.Surjective (q.app S)) ∧
      (∀ S, Function.Injective ((kernelι q).app S)) ∧
      (∀ S, Function.Exact ((kernelι q).app S) (q.app S)) ∧
      D.FiniteOnSingletons (kernel q) ∧ D.Localizes (kernel q)

end LinearAlgebraicGroups.Specs.ProjectiveFiniteChartPresentations
