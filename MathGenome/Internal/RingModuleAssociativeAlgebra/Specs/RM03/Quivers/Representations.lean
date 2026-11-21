import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.PathAlgebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.PathCategory.Basic

/-! Specifications for quiver representations and their vertexwise morphisms. -/

open CategoryTheory

namespace RM03.QuiverRepresentationSpec

/-- Representations on vector spaces in universe `d`. -/
abbrev Carrier.{u, v, w, d} (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] :=
  Paths Q ⥤ ModuleCat.{d} k

set_option linter.checkUnivs false in
abbrev CarrierSignature.{u, v, w, d} :=
  ∀ (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q], Type (max u v w (d + 1))

/-- Arbitrary vertex spaces and arbitrary linear maps on the arrows. -/
abbrev ObjectData.{u, v, w, d} (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] :=
  Σ spaces : Q → ModuleCat.{d} k, ∀ {i j : Q}, Quiver.Hom i j → (spaces i →ₗ[k] spaces j)

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]

abbrev vertex (F : Carrier.{u, v, w, d} k Q) (i : Q) : ModuleCat.{d} k :=
  F.obj i

def mapPath (F : Carrier.{u, v, w, d} k Q) {i j : Q} (p : Quiver.Path i j) :
    vertex F i →ₗ[k] vertex F j :=
  (F.map p).hom

def arrow (F : Carrier.{u, v, w, d} k Q) {i j : Q} (a : Quiver.Hom i j) :
    vertex F i →ₗ[k] vertex F j :=
  mapPath F a.toPath

def ofArrows (spaces : Q → ModuleCat.{d} k)
    (arrows : ∀ {i j : Q}, Quiver.Hom i j → (spaces i →ₗ[k] spaces j)) :
    Carrier.{u, v, w, d} k Q :=
  Paths.lift { obj := spaces, map := fun a => ModuleCat.ofHom (arrows a) }

def data (F : Carrier.{u, v, w, d} k Q) : ObjectData.{u, v, w, d} k Q :=
  ⟨vertex F, fun a => arrow F a⟩

def component {F G : Carrier.{u, v, w, d} k Q} (f : F ⟶ G) (i : Q) :
    vertex F i →ₗ[k] vertex G i :=
  (f.app i).hom

section Signatures

-- The field, vertex, arrow and vector space universes vary independently.
set_option linter.checkUnivs false

abbrev VertexSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q],
    Carrier.{u, v, w, d} k Q → Q → ModuleCat.{d} k

abbrev MapPathSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (F : Carrier.{u, v, w, d} k Q) {i j : Q},
    Quiver.Path i j → (vertex F i →ₗ[k] vertex F j)

abbrev ArrowSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (F : Carrier.{u, v, w, d} k Q) {i j : Q},
    Quiver.Hom i j → (vertex F i →ₗ[k] vertex F j)

abbrev OfArrowsSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (spaces : Q → ModuleCat.{d} k),
    (∀ {i j : Q}, Quiver.Hom i j → (spaces i →ₗ[k] spaces j)) → Carrier.{u, v, w, d} k Q

abbrev DataSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q],
    Carrier.{u, v, w, d} k Q → ObjectData.{u, v, w, d} k Q

abbrev ComponentSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    {F G : Carrier.{u, v, w, d} k Q}, (F ⟶ G) → ∀ i : Q, vertex F i →ₗ[k] vertex G i

end Signatures

def DataOfArrows : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (D : ObjectData.{u, v, w, d} k Q),
    data (ofArrows D.1 D.2) = D

def OfArrowsOfData : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (F : Carrier.{u, v, w, d} k Q),
    ofArrows (data F).1 (data F).2 = F

def PathIdentity : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (F : Carrier.{u, v, w, d} k Q) (i : Q),
    mapPath F (Quiver.Path.nil : Quiver.Path i i) = LinearMap.id

def PathAppendArrow : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (F : Carrier.{u, v, w, d} k Q)
    {i j l : Q} (p : Quiver.Path i j) (a : Quiver.Hom j l),
    mapPath F (p.cons a) = (arrow F a).comp (mapPath F p)

def PathComposition : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (F : Carrier.{u, v, w, d} k Q)
    {i j l : Q} (p : Quiver.Path i j) (q : Quiver.Path j l),
    mapPath F (p.comp q) = (mapPath F q).comp (mapPath F p)

abbrev Components (F G : Carrier.{u, v, w, d} k Q) :=
  ∀ i : Q, vertex F i →ₗ[k] vertex G i

def CommutesOnArrows {F G : Carrier.{u, v, w, d} k Q} (f : Components F G) : Prop :=
  ∀ ⦃i j : Q⦄ (a : Quiver.Hom i j), (f j).comp (arrow F a) = (arrow G a).comp (f i)

def CommutesOnPaths {F G : Carrier.{u, v, w, d} k Q} (f : Components F G) : Prop :=
  ∀ ⦃i j : Q⦄ (p : Quiver.Path i j), (f j).comp (mapPath F p) = (mapPath G p).comp (f i)

def PathNaturality : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : Carrier.{u, v, w, d} k Q}
    (f : Components F G), CommutesOnPaths f ↔ CommutesOnArrows f

def MorphismData : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : Carrier.{u, v, w, d} k Q}
    (f : Components F G), CommutesOnArrows f ↔ ∃! η : F ⟶ G, ∀ i, component η i = f i

def ComponentIdentity : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (F : Carrier.{u, v, w, d} k Q) (i : Q),
    component (𝟙 F) i = LinearMap.id

def ComponentComposition : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G H : Carrier.{u, v, w, d} k Q}
    (f : F ⟶ G) (g : G ⟶ H) (i : Q),
    component (f ≫ g) i = (component g i).comp (component f i)

def ComponentAddition : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : Carrier.{u, v, w, d} k Q}
    (f g : F ⟶ G) (i : Q), component (f + g) i = component f i + component g i

def ComponentScalarMultiplication : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : Carrier.{u, v, w, d} k Q}
    (c : k) (f : F ⟶ G) (i : Q), component (c • f) i = c • component f i

end RM03.QuiverRepresentationSpec
