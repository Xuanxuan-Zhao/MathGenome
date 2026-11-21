import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.Representations

/-! Quiver representations as functors from the path category to vector spaces. -/

open CategoryTheory

namespace RM03

/-- A representation over `k` on vertex spaces in universe `d`. -/
abbrev QuiverRepresentation.{u, v, w, d} (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] :=
  QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q

universe u v w d

namespace QuiverRepresentation

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]

variable {F G H : QuiverRepresentation.{u, v, w, d} k Q}

/-- The vector space at a vertex. -/
abbrev vertex (F : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) : ModuleCat.{d} k :=
  QuiverRepresentationSpec.vertex F i

/-- The linear map obtained by traversing a path. -/
abbrev mapPath (F : QuiverRepresentation.{u, v, w, d} k Q) {i j : Q} (p : Quiver.Path i j) :
    F.vertex i →ₗ[k] F.vertex j :=
  QuiverRepresentationSpec.mapPath F p

/-- The linear map of an arrow. -/
abbrev arrow (F : QuiverRepresentation.{u, v, w, d} k Q) {i j : Q} (a : Quiver.Hom i j) :
    F.vertex i →ₗ[k] F.vertex j :=
  QuiverRepresentationSpec.arrow F a

/-- Extend vertex spaces and arrow maps to a representation. -/
abbrev ofArrows (spaces : Q → ModuleCat.{d} k)
    (arrows : ∀ {i j : Q}, Quiver.Hom i j → (spaces i →ₗ[k] spaces j)) :
    QuiverRepresentation.{u, v, w, d} k Q :=
  QuiverRepresentationSpec.ofArrows spaces arrows

/-- Extract the vertex spaces and arrow maps of a representation. -/
abbrev data (F : QuiverRepresentation.{u, v, w, d} k Q) :
    QuiverRepresentationSpec.ObjectData.{u, v, w, d} k Q :=
  QuiverRepresentationSpec.data F

/-- The vertex component of a morphism of representations. -/
abbrev component (f : F ⟶ G) (i : Q) : F.vertex i →ₗ[k] G.vertex i :=
  QuiverRepresentationSpec.component f i

@[simp]
theorem mapPath_nil (F : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) :
    F.mapPath (Quiver.Path.nil : Quiver.Path i i) = LinearMap.id :=
  congrArg ModuleCat.Hom.hom (F.map_id (i : Paths Q))

@[simp]
theorem mapPath_comp (F : QuiverRepresentation.{u, v, w, d} k Q) {i j l : Q}
    (p : Quiver.Path i j) (q : Quiver.Path j l) :
    F.mapPath (p.comp q) = (F.mapPath q).comp (F.mapPath p) :=
  congrArg ModuleCat.Hom.hom (F.map_comp (X := (i : Paths Q)) (Y := j) (Z := l) p q)

@[simp]
theorem mapPath_cons (F : QuiverRepresentation.{u, v, w, d} k Q) {i j l : Q}
    (p : Quiver.Path i j) (a : Quiver.Hom j l) :
    F.mapPath (p.cons a) = (F.arrow a).comp (F.mapPath p) :=
  F.mapPath_comp p a.toPath

theorem mapPath_toPath (F : QuiverRepresentation.{u, v, w, d} k Q) {i j : Q}
    (a : Quiver.Hom i j) : F.mapPath a.toPath = F.arrow a :=
  rfl

section OfArrows

variable (spaces : Q → ModuleCat.{d} k)
  (arrows : ∀ {i j : Q}, Quiver.Hom i j → (spaces i →ₗ[k] spaces j))

@[simp]
theorem vertex_ofArrows (i : Q) : (ofArrows spaces arrows).vertex i = spaces i :=
  rfl

@[simp]
theorem arrow_ofArrows {i j : Q} (a : Quiver.Hom i j) :
    (ofArrows spaces arrows).arrow a = arrows a := by
  let A : Q ⥤q ModuleCat.{d} k :=
    { obj := spaces, map := fun a => ModuleCat.ofHom (arrows a) }
  change ((Paths.lift A).map a.toPath).hom = arrows a
  rw [Paths.lift_toPath]
  rfl

end OfArrows

theorem data_ofArrows (D : QuiverRepresentationSpec.ObjectData.{u, v, w, d} k Q) :
    data (ofArrows D.1 D.2) = D := by
  rcases D with ⟨spaces, arrows⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  change (fun {i j : Q} (a : Quiver.Hom i j) => (ofArrows spaces arrows).arrow a) = @arrows
  funext i j a
  exact arrow_ofArrows spaces arrows a

theorem ofArrows_data (F : QuiverRepresentation.{u, v, w, d} k Q) :
    ofArrows (data F).1 (data F).2 = F := by
  refine Paths.ext_functor (F := ofArrows (data F).1 (data F).2) (G := F) rfl ?_
  intro i j a
  let p : Quiver.Path i j := a.toPath
  change (ofArrows (data F).1 (data F).2).map p =
    𝟙 (F.obj (i : Paths Q)) ≫ F.map p ≫ 𝟙 (F.obj (j : Paths Q))
  rw [Category.comp_id, Category.id_comp]
  exact ModuleCat.hom_ext (arrow_ofArrows (data F).1 (data F).2 a)

/-- Naturality along a path, expressed in linear maps. -/
theorem naturality (f : F ⟶ G) {i j : Q} (p : Quiver.Path i j) :
    (component f j).comp (F.mapPath p) = (G.mapPath p).comp (component f i) :=
  congrArg ModuleCat.Hom.hom (f.naturality (X := (i : Paths Q)) (Y := j) p)

open QuiverRepresentationSpec (Components CommutesOnArrows CommutesOnPaths)

theorem commutes_on_paths_iff_arrows (f : Components F G) :
    CommutesOnPaths f ↔ CommutesOnArrows f := by
  constructor
  · intro h i j a
    exact h a.toPath
  · intro h i j p
    induction p with
    | nil =>
      change (f i).comp (F.mapPath Quiver.Path.nil) = (G.mapPath Quiver.Path.nil).comp (f i)
      simp
    | @cons j l p a ih =>
      change (f l).comp (F.mapPath (p.cons a)) = (G.mapPath (p.cons a)).comp (f i)
      rw [mapPath_cons, mapPath_cons, ← LinearMap.comp_assoc, h a, LinearMap.comp_assoc,
        ih, ← LinearMap.comp_assoc]

/-- Construct a morphism from linear maps commuting with the arrows. -/
def homMk (f : Components F G) (h : CommutesOnArrows f) : F ⟶ G where
  app i := ModuleCat.ofHom (f i)
  naturality _ _ p := ModuleCat.hom_ext ((commutes_on_paths_iff_arrows f).2 h p)

@[simp]
theorem homMk_component (f : Components F G) (h : CommutesOnArrows f) (i : Q) :
    component (homMk f h) i = f i :=
  rfl

@[ext]
theorem hom_ext {f g : F ⟶ G} (h : ∀ i : Q, component f i = component g i) : f = g :=
  NatTrans.ext (funext fun i => ModuleCat.hom_ext (h i))

theorem morphism_data (f : Components F G) :
    CommutesOnArrows f ↔ ∃! η : F ⟶ G, ∀ i, component η i = f i := by
  constructor
  · intro h
    refine ⟨homMk f h, fun i => homMk_component f h i, ?_⟩
    intro η hη
    exact hom_ext hη
  · rintro ⟨η, hη, _⟩ i j a
    rw [← hη i, ← hη j]
    exact naturality η a.toPath

@[simp]
theorem component_id (F : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) :
    component (𝟙 F) i = LinearMap.id :=
  rfl

@[simp]
theorem component_comp (f : F ⟶ G) (g : G ⟶ H) (i : Q) :
    component (f ≫ g) i = (component g i).comp (component f i) :=
  rfl

@[simp]
theorem component_add (f g : F ⟶ G) (i : Q) :
    component (f + g) i = component f i + component g i :=
  rfl

@[simp]
theorem component_smul (c : k) (f : F ⟶ G) (i : Q) :
    component (c • f) i = c • component f i :=
  rfl

end QuiverRepresentation
end RM03
