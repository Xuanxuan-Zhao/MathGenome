import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fin.SuccPred

/-!
Independent interfaces for HA-H02 (source lines 3607–3627).
No finiteness or nonemptiness is required of the index set or the opens.
The structure sheaf is the same arbitrary ring sheaf as in HA-H00.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory

universe u r v w

namespace AdvancedHomologicalAlgebra.Cech

variable {X : TopCat.{u}}

/-- An indexed cover of the specified open, allowing arbitrary index sets. -/
structure Cover (U : Opens X) (I : Type v) where
  opens : I → Opens X
  le : ∀ i, opens i ≤ U
  covers : iSup opens = U

/-- Intersection indexed by every position of the tuple. Repetitions are retained. -/
def tupleOpen {U : Opens X} {I : Type v} (c : Cover U I) :
    {p : ℕ} → (Fin (p + 1) → I) → Opens X
  | 0, t => c.opens (t 0)
  | _p + 1, t => c.opens (t 0) ⊓ tupleOpen c (t ∘ Fin.succ)

lemma tupleOpen_eq_iInf {U : Opens X} {I : Type v} (c : Cover U I) {p : ℕ}
    (t : Fin (p + 1) → I) : tupleOpen c t = ⨅ a, c.opens (t a) := by
  induction p with
  | zero => simp [tupleOpen]
  | succ p ih =>
    rw [tupleOpen, ih]
    apply le_antisymm
    · refine le_iInf (Fin.cases inf_le_left (fun a ↦ ?_))
      exact inf_le_right.trans (iInf_le _ a)
    · exact le_inf (iInf_le _ 0) (le_iInf fun a ↦ iInf_le _ a.succ)

lemma tupleOpen_le {U : Opens X} {I : Type v} (c : Cover U I) {p : ℕ}
    (t : Fin (p + 1) → I) : tupleOpen c t ≤ U := by
  rw [tupleOpen_eq_iInf]
  exact (iInf_le _ 0).trans (c.le _)

lemma tupleOpen_reindex_le {U : Opens X} {I : Type v} (c : Cover U I)
    {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (t : Fin (q + 1) → I) :
    tupleOpen c t ≤ tupleOpen c (t ∘ f) := by
  simp only [tupleOpen_eq_iInf]
  exact le_iInf fun a ↦ iInf_le _ (f a)

variable (R : X.Sheaf RingCat.{r}) (F : PresheafOfModules.{w} R.obj) (U : Opens X)

/-- Scalars act through the actual map from `R(U)` to `R(W)`. -/
abbrev localSections (W : Opens X) (h : W ≤ U) : ModuleCat.{w} (sectionRing R U) :=
  (ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom).obj (F.obj (op W))

/-- Restriction regarded as a linear map over the common section ring. -/
def localRestriction {V W : Opens X} (hV : V ≤ U) (hW : W ≤ U) (h : V ≤ W) :
    localSections R F U W hW →ₗ[sectionRing R U] localSections R F U V hV where
  toFun := F.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r s := by
    change F.map (homOfLE h).op ((R.obj.map (homOfLE hW).op) r • s) =
      (R.obj.map (homOfLE hV).op) r • F.map (homOfLE h).op s
    rw [F.map_smul]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp]
    rfl

variable {U} {I : Type v} (c : Cover U I)

/-- The full unnormalized product; no ordering, distinctness, or support condition. -/
abbrev Cochains (p : ℕ) :=
  (t : Fin (p + 1) → I) → localSections R F U (tupleOpen c t) (tupleOpen_le c t)

/-- Pull back positions in a tuple, then restrict to its full intersection. -/
def reindex {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    Cochains R F c p →ₗ[sectionRing R U] Cochains R F c q where
  toFun s t := localRestriction R F U (tupleOpen_le c t)
    (tupleOpen_le c (t ∘ f)) (tupleOpen_reindex_le c f t) (s (t ∘ f))
  map_add' s s' := by funext t; exact map_add _ _ _
  map_smul' r s := by
    funext t
    exact (localRestriction R F U (tupleOpen_le c t)
      (tupleOpen_le c (t ∘ f)) (tupleOpen_reindex_le c f t)).map_smul r _

/-- Alternating omission of each position, with signs starting at plus. -/
def differential (p : ℕ) : Cochains R F c p →ₗ[sectionRing R U] Cochains R F c (p + 1) :=
  ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) • reindex R F c a.succAbove

/-- Restrict a section over the covered open to every one-entry tuple. -/
def augmentation : F.obj (op U) →ₗ[sectionRing R U] Cochains R F c 0 where
  toFun s t := F.map (homOfLE (tupleOpen_le c t)).op s
  map_add' s s' := by funext t; exact map_add _ _ _
  map_smul' r s := by
    funext t
    exact F.map_smul _ _ _

/-- Kernel as a module over `R(U)`. -/
abbrev zeroCocycles := LinearMap.ker (differential R F c 0)

end AdvancedHomologicalAlgebra.Cech

namespace Specs.AdvancedHomologicalAlgebra.CechCochains

open AdvancedHomologicalAlgebra.Cech
variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (F : PresheafOfModules.{w} R.obj)
  {U : Opens X} {I : Type v} (c : Cover U I)

/-- Expected value and type of the full product construction. -/
def cochainsValue := Cochains R F c
def cochainsType := ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
  (_F : PresheafOfModules.{w} R.obj) {U : Opens X} {I : Type v} (_c : Cover U I),
  ℕ → Type (max v w)

def differentialValue := differential R F c
def differentialType := ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
  (F : PresheafOfModules.{w} R.obj) {U : Opens X} {I : Type v} (c : Cover U I)
  (p : ℕ), Cochains R F c p →ₗ[sectionRing R U] Cochains R F c (p + 1)

def augmentationValue := augmentation R F c
def augmentationType := ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
  (F : PresheafOfModules.{w} R.obj) {U : Opens X} {I : Type v} (c : Cover U I),
  F.obj (op U) →ₗ[sectionRing R U] Cochains R F c 0

/-- The differential squares to zero for every presheaf. -/
def differentialSquared : Prop := ∀ p : ℕ,
  (differential R F c (p + 1)).comp (differential R F c p) = 0

/-- The augmentation lands in the kernel without any sheaf assumption. -/
def augmentationClosed : Prop :=
  (differential R F c 0).comp (augmentation R F c) = 0

/-- Full sheaf gluing, with uniqueness, onto the actual kernel of `d⁰`. -/
def sectionsKernel (M : SheafOfModules.{w} R) : Prop :=
  ∃ e : M.val.obj (op U) ≃ₗ[sectionRing R U] zeroCocycles R M.val c,
    ∀ s, (e s).val = augmentation R M.val c s

/-- Closed types for comparison with the public universally quantified declarations. -/
def differentialSquaredType : Prop := ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
  (F : PresheafOfModules.{w} R.obj) {U : Opens X} {I : Type v} (c : Cover U I),
  differentialSquared R F c

def augmentationClosedType : Prop := ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
  (F : PresheafOfModules.{w} R.obj) {U : Opens X} {I : Type v} (c : Cover U I),
  augmentationClosed R F c

def sectionsKernelType : Prop := ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
  {U : Opens X} {I : Type v} (c : Cover U I) (M : SheafOfModules.{w} R),
  sectionsKernel R c M

end Specs.AdvancedHomologicalAlgebra.CechCochains
