import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Basic

/-! Canonical objects and independent expected values for HA-F01.
The filtration and morphism conditions are factorization through actual subobjects,
not conditions on elements or an assumption that an induced complex exists.
All indices range over ℤ; the ambient category is an arbitrary abelian category.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A decreasing filtration of a cochain complex by degreewise subobjects. -/
structure Filtration (K : CochainComplex A ℤ) where
  piece : (p n : ℤ) → Subobject (K.X n)
  decreasing : ∀ p n, piece (p + 1) n ≤ piece p n
  preserved : ∀ p i j, ∃ δ : (piece p i : A) ⟶ (piece p j : A),
    δ ≫ (piece p j).arrow = (piece p i).arrow ≫ K.d i j

namespace Filtration
variable {K : CochainComplex A ℤ}

/-- The source's condition on successive degrees suffices for our all-pairs API. -/
def ofSuccessive (P : (p n : ℤ) → Subobject (K.X n))
    (dec : ∀ p n, P (p + 1) n ≤ P p n)
    (pres : ∀ p n, ∃ δ : (P p n : A) ⟶ (P p (n + 1) : A),
      δ ≫ (P p (n + 1)).arrow = (P p n).arrow ≫ K.d n (n + 1)) :
    Filtration K where
  piece := P
  decreasing := dec
  preserved p i j := by
    by_cases h : i + 1 = j
    · subst j; exact pres p i
    · refine ⟨0, ?_⟩
      rw [K.shape i j h, comp_zero, zero_comp]

/-- The unique restriction of the ambient differential. -/
def differential (F : Filtration K) (p i j : ℤ) :
    (F.piece p i : A) ⟶ (F.piece p j : A) :=
  (F.preserved p i j).choose

@[reassoc (attr := simp)]
theorem differential_arrow (F : Filtration K) (p i j : ℤ) :
    F.differential p i j ≫ (F.piece p j).arrow =
      (F.piece p i).arrow ≫ K.d i j :=
  (F.preserved p i j).choose_spec

/-- The subcomplex with terms `F^p K^n`. -/
def step (F : Filtration K) (p : ℤ) : CochainComplex A ℤ where
  X n := F.piece p n
  d := F.differential p
  shape i j h := by
    apply (cancel_mono (F.piece p j).arrow).1
    simp [K.shape i j h]
  d_comp_d' i j k _ _ := by
    apply (cancel_mono (F.piece p k).arrow).1
    simp [Category.assoc]

/-- Inclusion of a filtration step into the ambient complex. -/
def inclusion (F : Filtration K) (p : ℤ) : F.step p ⟶ K where
  f n := (F.piece p n).arrow
  comm' i j _ := (F.differential_arrow p i j).symm

/-- Inclusion of the next filtration step. -/
def transition (F : Filtration K) (p : ℤ) : F.step (p + 1) ⟶ F.step p where
  f n := Subobject.ofLE _ _ (F.decreasing p n)
  comm' i j _ := by
    apply (cancel_mono (F.piece p j).arrow).1
    simp [step, Category.assoc]

/-- The degreewise quotient differential, descended through the cokernel. -/
def gradedDifferential (F : Filtration K) (p i j : ℤ) :
    cokernel ((F.transition p).f i) ⟶ cokernel ((F.transition p).f j) :=
  cokernel.map _ _ ((F.step (p + 1)).d i j) ((F.step p).d i j)
    ((F.transition p).comm i j)

@[reassoc (attr := simp)]
theorem π_gradedDifferential (F : Filtration K) (p i j : ℤ) :
    cokernel.π ((F.transition p).f i) ≫ F.gradedDifferential p i j =
      (F.step p).d i j ≫ cokernel.π ((F.transition p).f j) := by
  simp [gradedDifferential]

/-- The associated graded complex, literally the degreewise quotients. -/
def graded (F : Filtration K) (p : ℤ) : CochainComplex A ℤ where
  X n := cokernel ((F.transition p).f n)
  d := F.gradedDifferential p
  shape i j h := by
    apply (cancel_epi (cokernel.π ((F.transition p).f i))).1
    simp [(F.step p).shape i j h]
  d_comp_d' i j k _ _ := by
    apply (cancel_epi (cokernel.π ((F.transition p).f i))).1
    simp only [F.π_gradedDifferential_assoc, F.π_gradedDifferential,
      ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp, comp_zero]

/-- The quotient cochain map `F^p K ⟶ gr^p K`. -/
def projection (F : Filtration K) (p : ℤ) : F.step p ⟶ F.graded p where
  f n := cokernel.π ((F.transition p).f n)
  comm' i j _ := F.π_gradedDifferential p i j
end Filtration

/-- A filtered complex includes its ambient cochain complex. -/
structure FilteredComplex (A : Type u) [Category.{v} A] [Abelian A] where
  complex : CochainComplex A ℤ
  filtration : Filtration complex

/-- A filtered map is precisely a cochain map preserving each subobject. -/
structure FilteredMap (X Y : FilteredComplex A) where
  hom : X.complex ⟶ Y.complex
  preserves : ∀ p n, ∃ f : (X.filtration.piece p n : A) ⟶ (Y.filtration.piece p n : A),
    f ≫ (Y.filtration.piece p n).arrow = (X.filtration.piece p n).arrow ≫ hom.f n

namespace FilteredMap
variable {X Y Z : FilteredComplex A}

def id (X : FilteredComplex A) : FilteredMap X X where
  hom := 𝟙 X.complex
  preserves p n := ⟨𝟙 _, by simp⟩

def comp (f : FilteredMap X Y) (g : FilteredMap Y Z) : FilteredMap X Z where
  hom := f.hom ≫ g.hom
  preserves p n := ⟨(f.preserves p n).choose ≫ (g.preserves p n).choose, by
    change ((f.preserves p n).choose ≫ (g.preserves p n).choose) ≫ _ =
      _ ≫ (f.hom.f n ≫ g.hom.f n)
    rw [Category.assoc, (g.preserves p n).choose_spec, ← Category.assoc,
      (f.preserves p n).choose_spec, Category.assoc]⟩

/-- The degreewise restriction of a filtered cochain map. -/
def component (f : FilteredMap X Y) (p n : ℤ) :
    (X.filtration.piece p n : A) ⟶ (Y.filtration.piece p n : A) :=
  (f.preserves p n).choose

@[reassoc (attr := simp)]
theorem component_arrow (f : FilteredMap X Y) (p n : ℤ) :
    f.component p n ≫ (Y.filtration.piece p n).arrow =
      (X.filtration.piece p n).arrow ≫ f.hom.f n :=
  (f.preserves p n).choose_spec

/-- The induced cochain map on each filtration step. -/
def stepMap (f : FilteredMap X Y) (p : ℤ) :
    X.filtration.step p ⟶ Y.filtration.step p where
  f n := f.component p n
  comm' i j _ := by
    apply (cancel_mono (Y.filtration.piece p j).arrow).1
    change (f.component p i ≫ Y.filtration.differential p i j) ≫ _ =
      (X.filtration.differential p i j ≫ f.component p j) ≫ _
    rw [Category.assoc, Y.filtration.differential_arrow, ← Category.assoc,
      f.component_arrow, Category.assoc, f.hom.comm i j, ← Category.assoc,
      ← X.filtration.differential_arrow]
    simp only [Category.assoc, component_arrow]

@[reassoc]
theorem transition_naturality (f : FilteredMap X Y) (p : ℤ) :
    X.filtration.transition p ≫ f.stepMap p =
      f.stepMap (p + 1) ≫ Y.filtration.transition p := by
  ext n
  apply (cancel_mono (Y.filtration.piece p n).arrow).1
  change (Subobject.ofLE _ _ _ ≫ f.component p n) ≫ _ =
    (f.component (p + 1) n ≫ Subobject.ofLE _ _ _) ≫ _
  rw [Category.assoc, f.component_arrow, ← Category.assoc, Subobject.ofLE_arrow,
    Category.assoc, Subobject.ofLE_arrow, f.component_arrow]

/-- The induced map on the associated graded complexes. -/
def gradedMap (f : FilteredMap X Y) (p : ℤ) :
    X.filtration.graded p ⟶ Y.filtration.graded p where
  f n := cokernel.map _ _ ((f.stepMap (p + 1)).f n) ((f.stepMap p).f n)
    (congrArg (fun h => HomologicalComplex.Hom.f h n) (f.transition_naturality p))
  comm' i j _ := by
    apply (cancel_epi (cokernel.π ((X.filtration.transition p).f i))).1
    dsimp [Filtration.graded]
    simp only [cokernel.map, cokernel.π_desc, cokernel.π_desc_assoc,
      Filtration.π_gradedDifferential, Filtration.π_gradedDifferential_assoc,
      Category.assoc]
    rw [← Category.assoc, (f.stepMap p).comm i j, Category.assoc]
end FilteredMap
namespace Filtration
variable {K : CochainComplex A ℤ}

/-- The cochain map induced by a map annihilating the next filtration step. -/
def quotientDesc (F : Filtration K) (p : ℤ) {L : CochainComplex A ℤ}
    (g : F.step p ⟶ L) (h : F.transition p ≫ g = 0) : F.graded p ⟶ L where
  f n := cokernel.desc _ (g.f n) (HomologicalComplex.congr_hom h n)
  comm' i j _ := by
    apply (cancel_epi (cokernel.π ((F.transition p).f i))).1
    change cokernel.π _ ≫ (cokernel.desc _ _ _ ≫ L.d i j) =
      cokernel.π _ ≫ (F.gradedDifferential p i j ≫ cokernel.desc _ _ _)
    rw [← Category.assoc, cokernel.π_desc, π_gradedDifferential_assoc,
      cokernel.π_desc]
    · exact g.comm i j
    all_goals exact HomologicalComplex.congr_hom h _
end Filtration

namespace F01Specs

-- These are closed types/values, so binding checks include all universes and
-- arbitrary abelian categories, rather than a single chosen category.
def StepType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ}, Filtration K → ℤ → CochainComplex A ℤ
def StepValue : StepType.{v,u} := fun F p => F.step p

def GradedType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ}, Filtration K → ℤ → CochainComplex A ℤ
def GradedValue : GradedType.{v,u} := fun F p => F.graded p

def InclusionType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p : ℤ), F.step p ⟶ K
def InclusionValue : InclusionType.{v,u} := fun F p => F.inclusion p

def TransitionType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p : ℤ), F.step (p + 1) ⟶ F.step p
def TransitionValue : TransitionType.{v,u} := fun F p => F.transition p

def ProjectionType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p : ℤ), F.step p ⟶ F.graded p
def ProjectionValue : ProjectionType.{v,u} := fun F p => F.projection p

def StepMapType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {X Y : FilteredComplex A}, FilteredMap X Y →
  ∀ p : ℤ, X.filtration.step p ⟶ Y.filtration.step p
def StepMapValue : StepMapType.{v,u} := fun f p => f.stepMap p

def GradedMapType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {X Y : FilteredComplex A}, FilteredMap X Y →
  ∀ p : ℤ, X.filtration.graded p ⟶ Y.filtration.graded p
def GradedMapValue : GradedMapType.{v,u} := fun f p => f.gradedMap p

def QuotientDescType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p : ℤ) {L : CochainComplex A ℤ}
  (g : F.step p ⟶ L), F.transition p ≫ g = 0 → (F.graded p ⟶ L)
def QuotientDescValue : QuotientDescType.{v,u} := fun {_} [_] [_] {_} F p {_} g h => F.quotientDesc p g h

/-- Both induced maps preserve identities and compositions. -/
def Functoriality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A],
  (∀ (X : FilteredComplex A) (p : ℤ),
    (FilteredMap.id X).stepMap p = 𝟙 (X.filtration.step p)) ∧
  (∀ {X Y Z : FilteredComplex A} (f : FilteredMap X Y) (g : FilteredMap Y Z) (p : ℤ),
    (f.comp g).stepMap p = f.stepMap p ≫ g.stepMap p) ∧
  (∀ (X : FilteredComplex A) (p : ℤ),
    (FilteredMap.id X).gradedMap p = 𝟙 (X.filtration.graded p)) ∧
  (∀ {X Y Z : FilteredComplex A} (f : FilteredMap X Y) (g : FilteredMap Y Z) (p : ℤ),
    (f.comp g).gradedMap p = f.gradedMap p ≫ g.gradedMap p)

/-- Inclusion and quotient maps commute with filtered maps. -/
def Naturality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {X Y : FilteredComplex A} (f : FilteredMap X Y) (p : ℤ),
  (f.stepMap p ≫ Y.filtration.inclusion p = X.filtration.inclusion p ≫ f.hom) ∧
  (X.filtration.transition p ≫ f.stepMap p =
    f.stepMap (p + 1) ≫ Y.filtration.transition p) ∧
  (X.filtration.projection p ≫ f.gradedMap p =
    f.stepMap p ≫ Y.filtration.projection p)

/-- The step is a subcomplex and the graded complex has the quotient universal property. -/
def SubcomplexAndQuotient : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p : ℤ),
  Mono (F.inclusion p) ∧ Mono (F.transition p) ∧ Epi (F.projection p) ∧
  F.transition p ≫ F.projection p = 0 ∧
  (∀ {L : CochainComplex A ℤ} (g : F.step p ⟶ L) (_h : F.transition p ≫ g = 0),
    ∃! q : F.graded p ⟶ L, F.projection p ≫ q = g)

/-- Explicit differential formulas, including the square-zero assertions. -/
def DifferentialFormulas : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p i j k : ℤ),
  ((F.step p).d i j ≫ (F.piece p j).arrow = (F.piece p i).arrow ≫ K.d i j) ∧
  ((F.step p).d i j ≫ (F.step p).d j k = 0) ∧
  (cokernel.π ((F.transition p).f i) ≫ (F.graded p).d i j =
    (F.step p).d i j ≫ cokernel.π ((F.transition p).f j)) ∧
  ((F.graded p).d i j ≫ (F.graded p).d j k = 0)
end F01Specs
end AdvancedHomologicalAlgebra
