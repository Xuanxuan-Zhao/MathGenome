import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.ReflectionEquivalence
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.Forms
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.SimpleReflections
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Reflection at a sink or source, with its inverse obtained from the exact vertex sequence. -/

open CategoryTheory CategoryTheory.Limits
open RM03 (QuiverRepresentation)
open scoped BigOperators Matrix

namespace RepTheorySurvey.Quiver.ReflectionEquivalence

open ReflectionEquivalenceSpec

noncomputable section

set_option linter.checkUnivs false

universe u v w d
variable {Q : Type u} {k : Type w} [Field k]
variable {q r : Quiver.{v} Q} {i : Q}

section Coordinates

variable [Finite (Port q i)]
variable {B C : Away i → ModuleCat.{d} k} {M N : ModuleCat.{d} k}

@[simp] theorem coord_index (B : Away i → ModuleCat.{d} k) (a : Index q i) :
    coord B (indexEquiv q i a) = ModuleCat.ofHom (LinearMap.proj a) := by
  have step {b c : Index q i} (h : b = c) :
      ModuleCat.ofHom (LinearMap.proj b) ≫
        eqToHom (congrArg (fun t => B (indexEquiv q i t).1) h) =
        ModuleCat.ofHom (LinearMap.proj c : Total (q := q) B →ₗ[k] _) := by subst c; simp
  exact step ((indexEquiv q i).symm_apply_apply a)

@[simp] theorem insert_index (B : Away i → ModuleCat.{d} k) (a : Index q i) :
    includeCoordinate B (indexEquiv q i a) = ModuleCat.ofHom (LinearMap.single k
      (fun b : Index q i => B (indexEquiv q i b).1) a) := by
  have step {b c : Index q i} (h : b = c) :
      eqToHom (congrArg (fun t => B (indexEquiv q i t).1) h.symm) ≫
        ModuleCat.ofHom (LinearMap.single k (fun t => B (indexEquiv q i t).1) b) =
        ModuleCat.ofHom (LinearMap.single k (fun t => B (indexEquiv q i t).1) c) := by subst c; simp
  exact step ((indexEquiv q i).symm_apply_apply a)

theorem hom_ext_from_total {f g : ModuleCat.of k (Total (q := q) B) ⟶ M}
    (h : ∀ a, includeCoordinate B a ≫ f = includeCoordinate B a ≫ g) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.pi_ext'
  intro a
  simpa only [insert_index, ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
    congrArg ModuleCat.Hom.hom (h (indexEquiv q i a))

theorem hom_ext_to_total {f g : M ⟶ ModuleCat.of k (Total (q := q) B)}
    (h : ∀ a, f ≫ coord B a = g ≫ coord B a) : f = g := by
  apply ModuleCat.hom_ext
  ext x a
  simpa using DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (h (indexEquiv q i a))) x

@[simp, reassoc] theorem insert_sumArrows (f : ∀ a : Port q i, B a.1 ⟶ M) (a : Port q i) :
    includeCoordinate B a ≫ ModuleCat.ofHom (sumArrows f) = f a := by
  obtain ⟨a, rfl⟩ := (indexEquiv q i).surjective a
  rw [insert_index]
  apply ModuleCat.hom_ext
  ext x
  exact LinearMap.lsum_piSingle k _ k (fun a => (f (indexEquiv q i a)).hom) a x

@[simp, reassoc] theorem tupleArrows_coord (g : ∀ a : Port q i, M ⟶ B a.1) (a : Port q i) :
    ModuleCat.ofHom (tupleArrows g) ≫ coord B a = g a := by
  obtain ⟨a, rfl⟩ := (indexEquiv q i).surjective a
  rw [coord_index]
  rfl

@[simp, reassoc] theorem totalMap_coord (f : ∀ j, B j ⟶ C j) (a : Port q i) :
    ModuleCat.ofHom (totalMap (q := q) f) ≫ coord C a = coord B a ≫ f a.1 := by
  obtain ⟨a, rfl⟩ := (indexEquiv q i).surjective a
  rw [coord_index, coord_index]
  rfl

@[simp, reassoc] theorem insert_totalMap (f : ∀ j, B j ⟶ C j) (a : Port q i) :
    includeCoordinate B a ≫ ModuleCat.ofHom (totalMap (q := q) f) = f a.1 ≫ includeCoordinate C a := by
  obtain ⟨a, rfl⟩ := (indexEquiv q i).surjective a
  rw [insert_index, insert_index]
  apply ModuleCat.hom_ext
  ext x b
  by_cases h : b = a
  · subst b
    simp [totalMap]
  · simp [totalMap, Pi.single_eq_of_ne h]

end Coordinates

section Assembly

variable {S T : Spaces.{u, w, d} k i}
variable {V W : Rep.{u, v, w, d} k q}

/-- Coordinates at the center and away from the center. -/
structure VertexFrame (V : Rep.{u, v, w, d} k q) (S : Spaces.{u, w, d} k i) where
  center : vertex V i ≅ S.center
  away : ∀ j : Away i, vertex V j ≅ S.away j

def VertexFrame.read (V : Rep.{u, v, w, d} k q) (i : Q) : VertexFrame V (Spaces.read V i) :=
  ⟨Iso.refl _, fun _ => Iso.refl _⟩

@[reassoc] theorem arrow_naturality (f : V ⟶ W) {j l : Q} (a : q.Hom j l) :
    arrowHom V a ≫ component f l = component f j ≫ arrowHom W a := by
  let := q
  apply ModuleCat.hom_ext
  exact QuiverRepresentation.naturality f a.toPath

theorem rep_hom_ext {f g : V ⟶ W} (h : ∀ j, component f j = component g j) : f = g :=
  @QuiverRepresentation.hom_ext k Q _ q V W f g (fun j => congrArg ModuleCat.Hom.hom (h j))

namespace VertexFrame

def inArrow (P : VertexFrame V S) (j : Away i) (a : q.Hom j i) : S.away j ⟶ S.center :=
  (P.away j).inv ≫ arrowHom V a ≫ P.center.hom

def outArrow (P : VertexFrame V S) (j : Away i) (a : q.Hom i j) : S.center ⟶ S.away j :=
  P.center.inv ≫ arrowHom V a ≫ (P.away j).hom

def offArrow (P : VertexFrame V S) (j l : Away i) (a : q.Hom j l) : S.away j ⟶ S.away l :=
  (P.away j).inv ≫ arrowHom V a ≫ (P.away l).hom

def homAt (P : VertexFrame V S) (R : VertexFrame W T) (f : V ⟶ W) : S.center ⟶ T.center :=
  P.center.inv ≫ component f i ≫ R.center.hom

def homAway (P : VertexFrame V S) (R : VertexFrame W T) (f : V ⟶ W) (j : Away i) :
    S.away j ⟶ T.away j :=
  (P.away j).inv ≫ component f j ≫ (R.away j).hom

@[simp] theorem homAt_read (f : V ⟶ W) :
    homAt (read V i) (read W i) f = component f i := by simp [homAt, read]

@[simp] theorem homAway_read (f : V ⟶ W) (j : Away i) :
    homAway (read V i) (read W i) f j = component f j := by simp [homAway, read]

@[simp] theorem inArrow_read (j : Away i) (a : q.Hom j i) :
    (read V i).inArrow j a = arrowHom V a := by simp [inArrow, read]

@[simp] theorem outArrow_read (j : Away i) (a : q.Hom i j) :
    (read V i).outArrow j a = arrowHom V a := by simp [outArrow, read]

@[simp] theorem offArrow_read (j l : Away i) (a : q.Hom j l) :
    (read V i).offArrow j l a = arrowHom V a := by simp [offArrow, read]

variable (P : VertexFrame V S) (R : VertexFrame W T)

theorem hom_ext {f g : V ⟶ W} (h : P.homAt R f = P.homAt R g)
    (ha : ∀ j, P.homAway R f j = P.homAway R g j) : f = g := by
  apply rep_hom_ext
  intro j
  by_cases e : j = i
  · subst j
    have hh := congrArg (fun z => P.center.hom ≫ z ≫ R.center.inv) h
    simpa [homAt] using hh
  · have hh := congrArg (fun z => (P.away ⟨j, e⟩).hom ≫ z ≫ (R.away ⟨j, e⟩).inv) (ha ⟨j, e⟩)
    simpa [homAway] using hh

def buildComponent (f : S.center ⟶ T.center) (g : ∀ j, S.away j ⟶ T.away j)
    (j : Q) : vertex V j ⟶ vertex W j := by
  by_cases h : j = i
  · subst j
    exact P.center.hom ≫ f ≫ R.center.inv
  · exact (P.away ⟨j, h⟩).hom ≫ g ⟨j, h⟩ ≫ (R.away ⟨j, h⟩).inv

@[simp] theorem buildComponent_center (f : S.center ⟶ T.center)
    (g : ∀ j, S.away j ⟶ T.away j) :
    P.buildComponent R f g i = P.center.hom ≫ f ≫ R.center.inv := by simp [buildComponent]

@[simp] theorem buildComponent_away (f : S.center ⟶ T.center)
    (g : ∀ j, S.away j ⟶ T.away j) {j : Q} (h : j ≠ i) :
    P.buildComponent R f g j = (P.away ⟨j, h⟩).hom ≫ g ⟨j, h⟩ ≫ (R.away ⟨j, h⟩).inv := by
  simp [buildComponent, h]

/-- A morphism between representations assembled from commuting maps at the vertices. -/
def buildHom (loopless : IsEmpty (q.Hom i i))
    (f : S.center ⟶ T.center) (g : ∀ j, S.away j ⟶ T.away j)
    (hi : ∀ j a, P.inArrow j a ≫ f = g j ≫ R.inArrow j a)
    (ho : ∀ j a, P.outArrow j a ≫ g j = f ≫ R.outArrow j a)
    (ha : ∀ j l a, P.offArrow j l a ≫ g l = g j ≫ R.offArrow j l a) : V ⟶ W := by
  letI := q
  refine QuiverRepresentation.homMk (fun j => (P.buildComponent R f g j).hom) ?_
  intro j l a
  suffices h : arrowHom V a ≫ P.buildComponent R f g l =
      P.buildComponent R f g j ≫ arrowHom W a from congrArg ModuleCat.Hom.hom h
  by_cases hj : j = i
  · subst j
    by_cases hl : l = i
    · subst l
      exact (loopless.false a).elim
    · rw [buildComponent_center, buildComponent_away _ _ _ _ (by assumption)]
      have h := congrArg (fun z => P.center.hom ≫ z ≫ (R.away ⟨l, hl⟩).inv) (ho ⟨l, hl⟩ a)
      simpa [outArrow] using h
  · by_cases hl : l = i
    · subst l
      rw [buildComponent_center, buildComponent_away _ _ _ _ (by assumption)]
      have h := congrArg (fun z => (P.away ⟨j, hj⟩).hom ≫ z ≫ R.center.inv) (hi ⟨j, hj⟩ a)
      simpa [inArrow] using h
    · rw [buildComponent_away _ _ _ _ hj, buildComponent_away _ _ _ _ hl]
      have h := congrArg (fun z => (P.away ⟨j, hj⟩).hom ≫ z ≫ (R.away ⟨l, hl⟩).inv)
        (ha ⟨j, hj⟩ ⟨l, hl⟩ a)
      simpa [offArrow] using h

@[simp] theorem homAt_buildHom (loopless : IsEmpty (q.Hom i i))
    (f : S.center ⟶ T.center) (g : ∀ j, S.away j ⟶ T.away j) (hi ho ha) :
    P.homAt R (P.buildHom R loopless f g hi ho ha) = f := by
  change P.center.inv ≫ P.buildComponent R f g i ≫ R.center.hom = f
  simp

@[simp] theorem homAway_buildHom (loopless : IsEmpty (q.Hom i i))
    (f : S.center ⟶ T.center) (g : ∀ j, S.away j ⟶ T.away j) (hi ho ha) (j : Away i) :
    P.homAway R (P.buildHom R loopless f g hi ho ha) j = g j := by
  change (P.away j).inv ≫ P.buildComponent R f g j ≫ (R.away j).hom = g j
  simp [buildComponent_away _ _ _ _ j.property]

end VertexFrame

variable (S) (loopless : IsEmpty (q.Hom i i))
    (incoming : ∀ j : Away i, q.Hom j i → (S.away j ⟶ S.center))
    (outgoing : ∀ j : Away i, q.Hom i j → (S.center ⟶ S.away j))
    (off : ∀ j l : Away i, q.Hom j l → (S.away j ⟶ S.away l))

def assembleFrame : VertexFrame (assemble S loopless incoming outgoing off) S :=
  ⟨S.centerIso, S.awayIso⟩

@[simp] theorem assembleFrame_inArrow (j : Away i) (a : q.Hom j i) :
    (assembleFrame S loopless incoming outgoing off).inArrow j a = incoming j a := by
  let := q
  simp only [assembleFrame, VertexFrame.inArrow, arrowHom, arrow, assemble,
    QuiverRepresentation.arrow_ofArrows, j.property, ↓reduceDIte]
  change (S.awayIso j).inv ≫ ((S.awayIso j).hom ≫ incoming j a ≫ S.centerIso.inv) ≫ S.centerIso.hom = incoming j a
  simp

@[simp] theorem assembleFrame_outArrow (j : Away i) (a : q.Hom i j) :
    (assembleFrame S loopless incoming outgoing off).outArrow j a = outgoing j a := by
  let := q
  simp only [assembleFrame, VertexFrame.outArrow, arrowHom, arrow, assemble,
    QuiverRepresentation.arrow_ofArrows, j.property, ↓reduceDIte]
  change S.centerIso.inv ≫ (S.centerIso.hom ≫ outgoing j a ≫ (S.awayIso j).inv) ≫ (S.awayIso j).hom = outgoing j a
  simp

@[simp] theorem assembleFrame_offArrow (j l : Away i) (a : q.Hom j l) :
    (assembleFrame S loopless incoming outgoing off).offArrow j l a = off j l a := by
  let := q
  simp only [assembleFrame, VertexFrame.offArrow, arrowHom, arrow, assemble,
    QuiverRepresentation.arrow_ofArrows, j.property, l.property, ↓reduceDIte]
  change (S.awayIso j).inv ≫ ((S.awayIso j).hom ≫ off j l a ≫ (S.awayIso l).inv) ≫ (S.awayIso l).hom = off j l a
  simp

end Assembly

section Squares

variable {s : Quiver.{v} Q} {S T U : Spaces.{u, w, d} k i}
variable {V W X : Rep.{u, v, w, d} k s}

namespace VertexFrame

variable (P : VertexFrame V S) (R : VertexFrame W T) (J : VertexFrame X U)

@[simp] theorem homAt_id : P.homAt P (𝟙 V) = 𝟙 S.center := by simp [homAt, component]
@[simp] theorem homAway_id (j : Away i) : P.homAway P (𝟙 V) j = 𝟙 (S.away j) := by
  simp [homAway, component]

@[simp] theorem homAt_comp (f : V ⟶ W) (g : W ⟶ X) :
    P.homAt J (f ≫ g) = P.homAt R f ≫ R.homAt J g := by
  change P.center.inv ≫ (component f i ≫ component g i) ≫ J.center.hom = _
  simp [homAt]

@[simp] theorem homAway_comp (f : V ⟶ W) (g : W ⟶ X) (j : Away i) :
    P.homAway J (f ≫ g) j = P.homAway R f j ≫ R.homAway J g j := by
  change (P.away j).inv ≫ (component f j ≫ component g j) ≫ (J.away j).hom = _
  simp [homAway]

theorem inArrow_naturality (f : V ⟶ W) (j : Away i) (a : s.Hom j i) :
    P.inArrow j a ≫ P.homAt R f = P.homAway R f j ≫ R.inArrow j a := by
  simp only [inArrow, homAt, homAway, Category.assoc, Iso.hom_inv_id_assoc]
  rw [arrow_naturality_assoc]

theorem outArrow_naturality (f : V ⟶ W) (j : Away i) (a : s.Hom i j) :
    P.outArrow j a ≫ P.homAway R f j = P.homAt R f ≫ R.outArrow j a := by
  simp only [outArrow, homAt, homAway, Category.assoc, Iso.hom_inv_id_assoc]
  rw [arrow_naturality_assoc]

theorem offArrow_naturality (f : V ⟶ W) (j l : Away i) (a : s.Hom j l) :
    P.offArrow j l a ≫ P.homAway R f l = P.homAway R f j ≫ R.offArrow j l a := by
  simp only [offArrow, homAway, Category.assoc, Iso.hom_inv_id_assoc]
  rw [arrow_naturality_assoc]

variable [Finite (Port q i)]

abbrev totalHom (f : V ⟶ W) :
    ModuleCat.of k (Total (q := q) S.away) ⟶ ModuleCat.of k (Total (q := q) T.away) :=
  ModuleCat.ofHom (totalMap (P.homAway R f))

@[simp] theorem totalHom_id : P.totalHom (q := q) P (𝟙 V) = 𝟙 _ := by
  apply hom_ext_to_total
  intro a
  simp

theorem totalHom_comp (f : V ⟶ W) (g : W ⟶ X) :
    P.totalHom (q := q) J (f ≫ g) = P.totalHom R f ≫ R.totalHom J g := by
  apply hom_ext_to_total
  intro a
  simp only [totalHom, Category.assoc, totalMap_coord, totalMap_coord_assoc]
  rw [P.homAway_comp R J]

def totalIso (P : VertexFrame V S) :
    ModuleCat.of k (Total (q := q) (Spaces.read V i).away) ≅
      ModuleCat.of k (Total (q := q) S.away) where
  hom := (read V i).totalHom P (𝟙 V)
  inv := P.totalHom (read V i) (𝟙 V)
  hom_inv_id := by rw [← totalHom_comp, Category.id_comp, totalHom_id]
  inv_hom_id := by rw [← totalHom_comp, Category.id_comp, totalHom_id]

@[simp] theorem homAt_read_id : (read V i).homAt P (𝟙 V) = P.center.hom := by
  simp [homAt, read, component]

@[simp] theorem homAt_id_read : P.homAt (read V i) (𝟙 V) = P.center.inv := by
  simp [homAt, read, component]

@[simp] theorem homAway_read_id (j : Away i) :
    (read V i).homAway P (𝟙 V) j = (P.away j).hom := by
  simp [homAway, read, component]

@[simp] theorem homAway_id_read (j : Away i) :
    P.homAway (read V i) (𝟙 V) j = (P.away j).inv := by
  simp [homAway, read, component]

@[reassoc] theorem include_totalIso (a : Port q i) :
    includeCoordinate (Spaces.read V i).away a ≫ (P.totalIso (q := q)).hom =
      (P.away a.1).hom ≫ includeCoordinate S.away a := by
  change includeCoordinate _ a ≫ ModuleCat.ofHom (totalMap ((read V i).homAway P (𝟙 V))) = _
  rw [insert_totalMap, homAway_read_id]

@[reassoc] theorem totalIso_inv_coord (a : Port q i) :
    (P.totalIso (q := q)).inv ≫ coord (Spaces.read V i).away a =
      coord S.away a ≫ (P.away a.1).inv := by
  change ModuleCat.ofHom (totalMap (P.homAway (read V i) (𝟙 V))) ≫ coord _ a = _
  rw [totalMap_coord, homAway_id_read]

end VertexFrame

variable [Finite (Port q i)]

abbrev packedIn {V : Rep.{u, v, w, d} k q} (P : VertexFrame V S) :
    ModuleCat.of k (Total (q := q) S.away) ⟶ S.center :=
  ModuleCat.ofHom (sumArrows (fun a => P.inArrow a.1 a.2))

abbrev packedOut {V : Rep.{u, v, w, d} k r} (A : ArrowReversal q r i) (P : VertexFrame V S) :
    S.center ⟶ ModuleCat.of k (Total (q := q) S.away) :=
  ModuleCat.ofHom (tupleArrows (fun a => P.outArrow a.1 (A.incident a.1 a.2)))

@[simp] theorem packedIn_read (V : Rep.{u, v, w, d} k q) :
    packedIn (VertexFrame.read V i) = ModuleCat.ofHom (incomingMap (i := i) V) := by
  apply hom_ext_from_total
  intro a
  simp [incomingMap]

@[simp] theorem packedOut_read (A : ArrowReversal q r i) (V : Rep.{u, v, w, d} k r) :
    packedOut A (VertexFrame.read V i) = ModuleCat.ofHom (outgoingMap A V) := by
  apply hom_ext_to_total
  intro a
  simp [outgoingMap]

@[reassoc] theorem packedIn_naturality {V W : Rep.{u, v, w, d} k q}
    (P : VertexFrame V S) (R : VertexFrame W T) (f : V ⟶ W) :
    packedIn P ≫ P.homAt R f = P.totalHom R f ≫ packedIn R := by
  apply hom_ext_from_total
  intro a
  simp only [packedIn, VertexFrame.totalHom, insert_sumArrows_assoc,
    insert_totalMap_assoc, insert_sumArrows]
  exact P.inArrow_naturality R f a.1 a.2

@[reassoc] theorem packedOut_naturality (A : ArrowReversal q r i) {V W : Rep.{u, v, w, d} k r}
    (P : VertexFrame V S) (R : VertexFrame W T) (f : V ⟶ W) :
    packedOut A P ≫ P.totalHom R f = P.homAt R f ≫ packedOut A R := by
  apply hom_ext_to_total
  intro a
  simp only [packedOut, VertexFrame.totalHom, Category.assoc, totalMap_coord,
    tupleArrows_coord_assoc, tupleArrows_coord]
  exact P.outArrow_naturality R f a.1 (A.incident a.1 a.2)

end Squares

section Reflection

variable [Finite (Port q i)] (A : ArrowReversal q r i)

def sinkFrame (V : Rep.{u, v, w, d} k q) :
    VertexFrame (reflectSink A V) (kernelSpaces (i := i) V) := assembleFrame _ _ _ _ _

def sourceFrame (V : Rep.{u, v, w, d} k r) :
    VertexFrame (reflectSource A V) (quotientSpaces A V) := assembleFrame _ _ _ _ _

abbrev kerInclusion (V : Rep.{u, v, w, d} k q) :
    (kernelSpaces (i := i) V).center ⟶
      ModuleCat.of k (Total (q := q) (Spaces.read V i).away) :=
  ModuleCat.ofHom (LinearMap.ker (incomingMap (i := i) V)).subtype

abbrev quotientProjection (V : Rep.{u, v, w, d} k r) :
    ModuleCat.of k (Total (q := q) (Spaces.read V i).away) ⟶ (quotientSpaces A V).center :=
  ModuleCat.ofHom (LinearMap.range (outgoingMap A V)).mkQ

@[simp] theorem sinkFrame_outArrow (V : Rep.{u, v, w, d} k q) (j : Away i) (a : r.Hom i j) :
    (sinkFrame A V).outArrow j a = kerInclusion V ≫ coord _ ⟨j, (A.incident j).symm a⟩ := by
  exact assembleFrame_outArrow (kernelSpaces (i := i) V) _ _ _ _ j a

@[simp] theorem sinkFrame_offArrow (V : Rep.{u, v, w, d} k q) (j l : Away i) (a : r.Hom j l) :
    (sinkFrame A V).offArrow j l a = arrowHom V ((A.away j l).symm a) := by
  exact assembleFrame_offArrow (kernelSpaces (i := i) V) _ _ _ _ j l a

@[simp] theorem sourceFrame_inArrow (V : Rep.{u, v, w, d} k r) (j : Away i) (a : q.Hom j i) :
    (sourceFrame A V).inArrow j a = includeCoordinate _ ⟨j, a⟩ ≫ quotientProjection A V := by
  exact assembleFrame_inArrow (quotientSpaces A V) _ _ _ _ j a

@[simp] theorem sourceFrame_offArrow (V : Rep.{u, v, w, d} k r) (j l : Away i) (a : q.Hom j l) :
    (sourceFrame A V).offArrow j l a = arrowHom V (A.away j l a) := by
  exact assembleFrame_offArrow (quotientSpaces A V) _ _ _ _ j l a

@[simp] theorem packedOut_sinkFrame (V : Rep.{u, v, w, d} k q) :
    packedOut A (sinkFrame A V) = kerInclusion (i := i) V := by
  apply hom_ext_to_total
  rintro ⟨j, a⟩
  simp only [packedOut, tupleArrows_coord, sinkFrame_outArrow]
  have h := (A.incident j).symm_apply_apply a
  rw [h]

@[simp] theorem packedIn_sourceFrame (V : Rep.{u, v, w, d} k r) :
    packedIn (sourceFrame A V) = quotientProjection A V := by
  apply hom_ext_from_total
  intro a
  simp

variable {A}

theorem incomingMap_naturality {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W) :
    (incomingMap (i := i) W).comp (totalMap (q := q) (fun j => component f j)) =
      (component f i).hom.comp (incomingMap (i := i) V) := by
  have h := packedIn_naturality (VertexFrame.read V i) (VertexFrame.read W i) f
  simp only [packedIn_read, VertexFrame.homAt_read, VertexFrame.totalHom] at h
  exact congrArg ModuleCat.Hom.hom h.symm

theorem outgoingMap_naturality {V W : Rep.{u, v, w, d} k r} (f : V ⟶ W) :
    (totalMap (q := q) (fun j => component f j)).comp (outgoingMap A V) =
      (outgoingMap A W).comp (component f i).hom := by
  have h := packedOut_naturality A (VertexFrame.read V i) (VertexFrame.read W i) f
  simp only [packedOut_read, VertexFrame.homAt_read, VertexFrame.totalHom] at h
  exact congrArg ModuleCat.Hom.hom h

def mapKernel {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W) :
    (kernelSpaces (i := i) V).center ⟶ (kernelSpaces (i := i) W).center :=
  ModuleCat.ofHom <| ((totalMap (q := q) (fun j => component f j)).comp
    (kerInclusion (i := i) V).hom).codRestrict (LinearMap.ker (incomingMap (i := i) W)) (by
      intro x
      have h := LinearMap.congr_fun (incomingMap_naturality (i := i) f) x.1
      simpa [LinearMap.mem_ker.mp x.2] using h)

def mapQuotient {V W : Rep.{u, v, w, d} k r} (f : V ⟶ W) :
    (quotientSpaces A V).center ⟶ (quotientSpaces A W).center :=
  ModuleCat.ofHom <| (LinearMap.range (outgoingMap A V)).mapQ (LinearMap.range (outgoingMap A W))
    (totalMap (q := q) (fun j => component f j)) (by
      rintro x ⟨y, rfl⟩
      exact ⟨component f i y, (LinearMap.congr_fun (outgoingMap_naturality (A := A) f) y).symm⟩)

@[simp, reassoc] theorem mapKernel_square {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W) :
    mapKernel (i := i) f ≫ kerInclusion W =
      kerInclusion V ≫ ModuleCat.ofHom (totalMap (q := q) (fun j => component f j)) := rfl

@[simp, reassoc] theorem mapQuotient_square {V W : Rep.{u, v, w, d} k r} (f : V ⟶ W) :
    quotientProjection A V ≫ mapQuotient (A := A) f =
      ModuleCat.ofHom (totalMap (q := q) (fun j => component f j)) ≫ quotientProjection A W := by
  apply ModuleCat.hom_ext
  ext x
  rfl

variable (A)

def reflectSinkHom {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W) :
    reflectSink A V ⟶ reflectSink A W :=
  (sinkFrame A V).buildHom (sinkFrame A W) (A.source i) (mapKernel f) (fun j => component f j)
    (fun j a => ((A.source j).false a).elim)
    (by intro j a; simp only [sinkFrame_outArrow, Category.assoc, mapKernel_square_assoc, totalMap_coord])
    (by intro j l a; simpa using arrow_naturality f ((A.away j l).symm a))

def reflectSourceHom {V W : Rep.{u, v, w, d} k r} (f : V ⟶ W) :
    reflectSource A V ⟶ reflectSource A W :=
  (sourceFrame A V).buildHom (sourceFrame A W) (A.sink i) (mapQuotient f) (fun j => component f j)
    (by intro j a; simp only [sourceFrame_inArrow, Category.assoc, mapQuotient_square, insert_totalMap_assoc])
    (fun j a => ((A.sink j).false a).elim)
    (by intro j l a; simpa using arrow_naturality f (A.away j l a))


@[simp] theorem reflectSinkHom_center {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W) :
    (sinkFrame A V).homAt (sinkFrame A W) (reflectSinkHom A f) = mapKernel f := by
  simp [reflectSinkHom]

@[simp] theorem reflectSinkHom_away {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W) (j : Away i) :
    (sinkFrame A V).homAway (sinkFrame A W) (reflectSinkHom A f) j = component f j := by
  simp [reflectSinkHom]

@[simp] theorem reflectSourceHom_center {V W : Rep.{u, v, w, d} k r} (f : V ⟶ W) :
    (sourceFrame A V).homAt (sourceFrame A W) (reflectSourceHom A f) = mapQuotient f := by
  simp [reflectSourceHom]

@[simp] theorem reflectSourceHom_away {V W : Rep.{u, v, w, d} k r} (f : V ⟶ W) (j : Away i) :
    (sourceFrame A V).homAway (sourceFrame A W) (reflectSourceHom A f) j = component f j := by
  simp [reflectSourceHom]

instance kerInclusion_mono (V : Rep.{u, v, w, d} k q) :
    Mono (kerInclusion (i := i) V) :=
  (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

instance quotientProjection_epi (V : Rep.{u, v, w, d} k r) :
    Epi (quotientProjection A V) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

def reflectSinkFunctor : Rep.{u, v, w, d} k q ⥤ Rep.{u, v, w, d} k r where
  obj := reflectSink A
  map := reflectSinkHom A
  map_id V := by
    apply (sinkFrame A V).hom_ext (sinkFrame A V)
    · simp only [reflectSinkHom_center, VertexFrame.homAt_id]
      rw [← cancel_mono (kerInclusion (i := i) V), mapKernel_square, Category.id_comp]
      change kerInclusion V ≫ (VertexFrame.read V i).totalHom (VertexFrame.read V i) (𝟙 V) = _
      simp
    · intro j
      simp [component]
  map_comp {V W X} f g := by
    apply (sinkFrame A V).hom_ext (sinkFrame A X)
    · simp only [reflectSinkHom_center, VertexFrame.homAt_comp _ (sinkFrame A W) _]
      rw [← cancel_mono (kerInclusion (i := i) X), mapKernel_square, Category.assoc,
        mapKernel_square, mapKernel_square_assoc]
      change kerInclusion V ≫ (VertexFrame.read V i).totalHom (VertexFrame.read X i) (f ≫ g) =
        kerInclusion V ≫ (VertexFrame.read V i).totalHom (VertexFrame.read W i) f ≫
          (VertexFrame.read W i).totalHom (VertexFrame.read X i) g
      simp only [VertexFrame.totalHom_comp _ (VertexFrame.read W i) _]
    · intro j
      rw [VertexFrame.homAway_comp _ (sinkFrame A W) _]
      simp [component]

def reflectSourceFunctor : Rep.{u, v, w, d} k r ⥤ Rep.{u, v, w, d} k q where
  obj := reflectSource A
  map := reflectSourceHom A
  map_id V := by
    apply (sourceFrame A V).hom_ext (sourceFrame A V)
    · simp only [reflectSourceHom_center, VertexFrame.homAt_id]
      rw [← cancel_epi (quotientProjection A V), mapQuotient_square, Category.comp_id]
      change (VertexFrame.read V i).totalHom (VertexFrame.read V i) (𝟙 V) ≫ quotientProjection A V = _
      simp
    · intro j
      simp [component]
  map_comp {V W X} f g := by
    apply (sourceFrame A V).hom_ext (sourceFrame A X)
    · simp only [reflectSourceHom_center, VertexFrame.homAt_comp _ (sourceFrame A W) _]
      rw [← cancel_epi (quotientProjection A V), mapQuotient_square, mapQuotient_square_assoc,
        mapQuotient_square]
      change (VertexFrame.read V i).totalHom (VertexFrame.read X i) (f ≫ g) ≫ quotientProjection A X =
        (VertexFrame.read V i).totalHom (VertexFrame.read W i) f ≫
          (VertexFrame.read W i).totalHom (VertexFrame.read X i) g ≫ quotientProjection A X
      simp only [VertexFrame.totalHom_comp _ (VertexFrame.read W i) _, Category.assoc]
    · intro j
      rw [VertexFrame.homAway_comp _ (sourceFrame A W) _]
      simp [component]

end Reflection

section LinearFunctors

variable [Finite (Port q i)] (A : ArrowReversal q r i)

private theorem totalMap_add {B C : Away i → ModuleCat.{d} k}
    (f g : ∀ j, B j ⟶ C j) :
    totalMap (q := q) (fun j => f j + g j) = totalMap f + totalMap g := by
  ext x a
  rfl

private theorem totalMap_smul {B C : Away i → ModuleCat.{d} k}
    (c : k) (f : ∀ j, B j ⟶ C j) :
    totalMap (q := q) (fun j => c • f j) = c • totalMap f := by
  ext x a
  rfl

@[simp] private theorem component_add {s : Quiver.{v} Q}
    {V W : Rep.{u, v, w, d} k s} (f g : V ⟶ W) (j : Q) :
    component (f + g) j = component f j + component g j := rfl

@[simp] private theorem component_smul {s : Quiver.{v} Q}
    {V W : Rep.{u, v, w, d} k s} (c : k) (f : V ⟶ W) (j : Q) :
    component (c • f) j = c • component f j := rfl

@[simp] private theorem homAt_add {s : Quiver.{v} Q} {V W : Rep.{u, v, w, d} k s}
    {S T : Spaces.{u, w, d} k i} (P : VertexFrame V S) (R : VertexFrame W T)
    (f g : V ⟶ W) : P.homAt R (f + g) = P.homAt R f + P.homAt R g := by
  simp [VertexFrame.homAt, Preadditive.add_comp, Preadditive.comp_add]

@[simp] private theorem homAway_add {s : Quiver.{v} Q} {V W : Rep.{u, v, w, d} k s}
    {S T : Spaces.{u, w, d} k i} (P : VertexFrame V S) (R : VertexFrame W T)
    (f g : V ⟶ W) (j : Away i) :
    P.homAway R (f + g) j = P.homAway R f j + P.homAway R g j := by
  simp [VertexFrame.homAway, Preadditive.add_comp, Preadditive.comp_add]

@[simp] private theorem homAt_smul {s : Quiver.{v} Q} {V W : Rep.{u, v, w, d} k s}
    {S T : Spaces.{u, w, d} k i} (P : VertexFrame V S) (R : VertexFrame W T)
    (c : k) (f : V ⟶ W) : P.homAt R (c • f) = c • P.homAt R f := by
  simp [VertexFrame.homAt, Linear.comp_smul, Linear.smul_comp]

@[simp] private theorem homAway_smul {s : Quiver.{v} Q} {V W : Rep.{u, v, w, d} k s}
    {S T : Spaces.{u, w, d} k i} (P : VertexFrame V S) (R : VertexFrame W T)
    (c : k) (f : V ⟶ W) (j : Away i) : P.homAway R (c • f) j = c • P.homAway R f j := by
  simp [VertexFrame.homAway, Linear.comp_smul, Linear.smul_comp]

instance reflectSinkFunctor_additive : (reflectSinkFunctor (k := k) A).Additive where
  map_add {V W} f g := by
    change reflectSinkHom A (f + g) = reflectSinkHom A f + reflectSinkHom A g
    apply (sinkFrame A V).hom_ext (sinkFrame A W)
    · simp only [homAt_add, reflectSinkHom_center]
      rw [← cancel_mono (kerInclusion (i := i) W)]
      simp only [Preadditive.add_comp, mapKernel_square, component_add, totalMap_add]
      rfl
    · intro j
      simp

instance reflectSourceFunctor_additive : (reflectSourceFunctor (k := k) A).Additive where
  map_add {V W} f g := by
    change reflectSourceHom A (f + g) = reflectSourceHom A f + reflectSourceHom A g
    apply (sourceFrame A V).hom_ext (sourceFrame A W)
    · simp only [homAt_add, reflectSourceHom_center]
      rw [← cancel_epi (quotientProjection A V)]
      simp only [Preadditive.comp_add, mapQuotient_square, component_add, totalMap_add]
      rfl
    · intro j
      simp

instance reflectSinkFunctor_linear : (reflectSinkFunctor (k := k) A).Linear k where
  map_smul {V W} f c := by
    change reflectSinkHom A (c • f) = c • reflectSinkHom A f
    apply (sinkFrame A V).hom_ext (sinkFrame A W)
    · simp only [homAt_smul, reflectSinkHom_center]
      rw [← cancel_mono (kerInclusion (i := i) W)]
      simp only [Linear.smul_comp, mapKernel_square, component_smul, totalMap_smul]
      rfl
    · intro j
      simp

instance reflectSourceFunctor_linear : (reflectSourceFunctor (k := k) A).Linear k where
  map_smul {V W} f c := by
    change reflectSourceHom A (c • f) = c • reflectSourceHom A f
    apply (sourceFrame A V).hom_ext (sourceFrame A W)
    · simp only [homAt_smul, reflectSourceHom_center]
      rw [← cancel_epi (quotientProjection A V)]
      simp only [Linear.comp_smul, mapQuotient_square, component_smul, totalMap_smul]
      rfl
    · intro j
      simp

theorem reflectSinkHom_formula {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W) :
    SinkMapFormula A f (reflectSinkHom A f) := by
  refine ⟨reflectSinkHom_away A f, ?_⟩
  change (sinkFrame A V).homAt (sinkFrame A W) (reflectSinkHom A f) ≫ kerInclusion W = _
  rw [reflectSinkHom_center, mapKernel_square]

theorem reflectSourceHom_formula {V W : Rep.{u, v, w, d} k r} (f : V ⟶ W) :
    SourceMapFormula A f (reflectSourceHom A f) := by
  refine ⟨reflectSourceHom_away A f, ?_⟩
  change quotientProjection A V ≫
    (sourceFrame A V).homAt (sourceFrame A W) (reflectSourceHom A f) = _
  rw [reflectSourceHom_center, mapQuotient_square]

end LinearFunctors

theorem sinkFunctor_exists : SinkFunctorStatement.{u, v, w, d} := by
  intro Q k _ q r i _ A
  refine ⟨reflectSinkFunctor A, fun _ => rfl, inferInstance, inferInstance, ?_⟩
  intro V W f
  change SinkMapFormula A f (𝟙 _ ≫ reflectSinkHom A f ≫ 𝟙 _)
  simpa using reflectSinkHom_formula A f

theorem sourceFunctor_exists : SourceFunctorStatement.{u, v, w, d} := by
  intro Q k _ q r i _ A
  refine ⟨reflectSourceFunctor A, fun _ => rfl, inferInstance, inferInstance, ?_⟩
  intro V W f
  change SourceMapFormula A f (𝟙 _ ≫ reflectSourceHom A f ≫ 𝟙 _)
  simpa using reflectSourceHom_formula A f

section Recovery

variable [Finite (Port q i)] (A : ArrowReversal q r i)

@[reassoc] theorem outgoingMap_reflectSink (V : Rep.{u, v, w, d} k q) :
    ModuleCat.ofHom (outgoingMap A (reflectSink A V)) ≫ (sinkFrame A V).totalIso.hom =
      (sinkFrame A V).center.hom ≫ kerInclusion V := by
  have h := packedOut_naturality A (VertexFrame.read (reflectSink A V) i) (sinkFrame A V)
    (𝟙 (reflectSink A V))
  simpa only [packedOut_read, packedOut_sinkFrame, VertexFrame.homAt_read_id, VertexFrame.totalIso] using h

@[reassoc] theorem totalIso_incomingMap_reflectSource (V : Rep.{u, v, w, d} k r) :
    (sourceFrame A V).totalIso.hom ≫ quotientProjection A V =
      ModuleCat.ofHom (incomingMap (i := i) (reflectSource A V)) ≫ (sourceFrame A V).center.hom := by
  have h := packedIn_naturality (VertexFrame.read (reflectSource A V) i) (sourceFrame A V)
    (𝟙 (reflectSource A V))
  simpa only [packedIn_read, packedIn_sourceFrame, VertexFrame.homAt_read_id, VertexFrame.totalIso] using h.symm

theorem outgoingMap_reflectSink_injective (V : Rep.{u, v, w, d} k q) :
    Function.Injective (outgoingMap A (reflectSink A V)) := by
  have h := congrArg ModuleCat.Hom.hom (outgoingMap_reflectSink A V)
  have hh : Function.Injective
      ((LinearMap.ker (incomingMap (i := i) V)).subtype.comp (sinkFrame A V).center.hom.hom) :=
    Subtype.val_injective.comp (sinkFrame A V).center.toLinearEquiv.injective
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  rw [← h] at hh
  intro x y hxy
  apply hh
  exact congrArg (fun z => (sinkFrame A V).totalIso.hom z) hxy

theorem incomingMap_reflectSource_surjective (V : Rep.{u, v, w, d} k r) :
    Function.Surjective (incomingMap (i := i) (reflectSource A V)) := by
  have h := congrArg ModuleCat.Hom.hom (totalIso_incomingMap_reflectSource A V)
  have hh : Function.Surjective
      ((LinearMap.range (outgoingMap A V)).mkQ.comp (sourceFrame A V).totalIso.hom.hom) :=
    (Submodule.mkQ_surjective _).comp ((sourceFrame A V).totalIso (q := q)).toLinearEquiv.surjective
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  rw [h] at hh
  intro z
  obtain ⟨x, hx⟩ := hh ((sourceFrame A V).center.hom z)
  exact ⟨x, (sourceFrame A V).center.toLinearEquiv.injective hx⟩

private theorem kernel_at_sink (V : Rep.{u, v, w, d} k q) :
    LinearMap.range (outgoingMap A (reflectSink A V)) =
      LinearMap.ker ((sinkFrame A V).totalIso.hom ≫ ModuleCat.ofHom (incomingMap (i := i) V)).hom := by
  let P := sinkFrame A V
  let E := P.totalIso (q := q)
  have hs (z : vertex (reflectSink A V) i) :
      E.hom (outgoingMap A (reflectSink A V) z) = (P.center.hom z).1 :=
    congrArg (fun f => f z) (outgoingMap_reflectSink A V)
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change incomingMap (i := i) V (E.hom (outgoingMap A (reflectSink A V) z)) = 0
    rw [hs]
    exact (P.center.hom z).2
  · intro hx
    let y : LinearMap.ker (incomingMap (i := i) V) := ⟨E.hom x, hx⟩
    let z := P.center.inv y
    refine ⟨z, E.toLinearEquiv.injective ?_⟩
    rw [show E.toLinearEquiv (outgoingMap A (reflectSink A V) z) = (P.center.hom z).1 from hs z]
    change (P.center.hom (P.center.inv y)).1 = E.hom x
    rw [← ModuleCat.comp_apply, P.center.inv_hom_id, ModuleCat.id_apply]

private theorem range_at_source (V : Rep.{u, v, w, d} k r) :
    LinearMap.range (ModuleCat.ofHom (outgoingMap A V) ≫ (sourceFrame A V).totalIso.inv).hom =
      LinearMap.ker (incomingMap (i := i) (reflectSource A V)) := by
  let P := sourceFrame A V
  let E := P.totalIso (q := q)
  have hs (x : Total (q := q) (Spaces.read (reflectSource A V) i).away) :
      quotientProjection A V (E.hom x) = P.center.hom (incomingMap (i := i) (reflectSource A V) x) :=
    congrArg (fun f => f x) (totalIso_incomingMap_reflectSource A V)
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply P.center.toLinearEquiv.injective
    rw [map_zero]
    change P.center.hom (incomingMap (i := i) (reflectSource A V)
      (E.inv (outgoingMap A V z))) = 0
    rw [← hs]
    rw [← ModuleCat.comp_apply E.inv E.hom, E.inv_hom_id, ModuleCat.id_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
  · intro hx
    have hx' : quotientProjection A V (E.hom x) = 0 := by
      rw [hs, LinearMap.mem_ker.mp hx, map_zero]
    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range (outgoingMap A V))).mp hx'
    refine ⟨z, ?_⟩
    change E.inv (outgoingMap A V z) = x
    rw [hz, ← ModuleCat.comp_apply, E.hom_inv_id, ModuleCat.id_apply]

def sinkCenterRecovery (V : Rep.{u, v, w, d} k q) (h : Function.Surjective (incomingMap (i := i) V)) :
    (quotientSpaces A (reflectSink A V)).center ≅ vertex V i :=
  let f := ((sinkFrame A V).totalIso.hom ≫ ModuleCat.ofHom (incomingMap (i := i) V)).hom
  ((Submodule.quotEquivOfEq _ _ (kernel_at_sink A V)).trans
    (f.quotKerEquivOfSurjective (h.comp ((sinkFrame A V).totalIso (q := q)).toLinearEquiv.surjective))).toModuleIso

@[reassoc] theorem sinkCenterRecovery_quotient (V : Rep.{u, v, w, d} k q) (h) :
    quotientProjection A (reflectSink A V) ≫ (sinkCenterRecovery A V h).hom =
      (sinkFrame A V).totalIso.hom ≫ ModuleCat.ofHom (incomingMap (i := i) V) := by
  apply ModuleCat.hom_ext
  ext x
  simp [sinkCenterRecovery, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

def sourceCenterRecovery (V : Rep.{u, v, w, d} k r) (h : Function.Injective (outgoingMap A V)) :
    vertex V i ≅ (kernelSpaces (i := i) (reflectSource A V)).center := by
  let f := (ModuleCat.ofHom (outgoingMap A V) ≫ (sourceFrame A V).totalIso.inv).hom
  have he : LinearMap.range f = LinearMap.ker (incomingMap (i := i) (reflectSource A V)) :=
    range_at_source A V
  exact ((LinearEquiv.ofInjective f
    (((sourceFrame A V).totalIso (q := q)).symm.toLinearEquiv.injective.comp h)).trans
      (LinearEquiv.ofEq _ _ he)).toModuleIso

@[reassoc] theorem sourceCenterRecovery_inclusion (V : Rep.{u, v, w, d} k r) (h) :
    (sourceCenterRecovery A V h).hom ≫ kerInclusion (i := i) (reflectSource A V) =
      ModuleCat.ofHom (outgoingMap A V) ≫ (sourceFrame A V).totalIso.inv := by
  apply ModuleCat.hom_ext
  ext x
  rfl

end Recovery

section Equivalence

variable [Finite (Port q i)] (A : ArrowReversal q r i)

private theorem isIso_buildHom {s : Quiver.{v} Q} {V W : Rep.{u, v, w, d} k s}
    {S T : Spaces.{u, w, d} k i} (P : VertexFrame V S) (R : VertexFrame W T)
    (h : IsEmpty (s.Hom i i)) (e : S.center ≅ T.center) (g : ∀ j, S.away j ≅ T.away j)
    (hi ho ha) : IsIso (P.buildHom R h e.hom (fun j => (g j).hom) hi ho ha) := by
  let := s
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro j
  let x : Q := j
  change IsIso (P.buildComponent R e.hom (fun j => (g j).hom) x)
  by_cases hj : x = i
  · rw [hj, VertexFrame.buildComponent_center]
    infer_instance
  · rw [VertexFrame.buildComponent_away _ _ _ _ hj]
    infer_instance

theorem finite_reflectSink : SinkFiniteStatement.{u, v, w, d} := by
  intro Q k _ q r i _ A V h j
  let P := sinkFrame A V
  let (a : Index q i) : Module.Finite k (vertex V (indexEquiv q i a).1) := h _
  by_cases hj : j = i
  · subst j
    have : Module.Finite k (LinearMap.ker (incomingMap (i := i) V)) := inferInstance
    exact Module.Finite.equiv P.center.toLinearEquiv.symm
  · have : Module.Finite k (vertex V j) := h j
    exact Module.Finite.equiv (P.away ⟨j, hj⟩).toLinearEquiv.symm

theorem finite_reflectSource : SourceFiniteStatement.{u, v, w, d} := by
  intro Q k _ q r i _ A V h j
  let P := sourceFrame A V
  let (a : Index q i) : Module.Finite k (vertex V (indexEquiv q i a).1) := h _
  by_cases hj : j = i
  · subst j
    have : Module.Finite k (Total (q := q) (Spaces.read V i).away ⧸
        LinearMap.range (outgoingMap A V)) := inferInstance
    exact Module.Finite.equiv P.center.toLinearEquiv.symm
  · have : Module.Finite k (vertex V j) := h j
    exact Module.Finite.equiv (P.away ⟨j, hj⟩).toLinearEquiv.symm

/-- Reassemble the sink representation after taking the kernel and then the quotient. -/
def recoverSinkHom (V : Rep.{u, v, w, d} k q)
    (h : Function.Surjective (incomingMap (i := i) V)) : reflectSource A (reflectSink A V) ⟶ V :=
  (sourceFrame A (reflectSink A V)).buildHom (VertexFrame.read V i) (A.sink i)
    (sinkCenterRecovery A V h).hom (fun j => ((sinkFrame A V).away j).hom)
    (by
      intro j a
      simp only [sourceFrame_inArrow, VertexFrame.inArrow_read, Category.assoc,
        sinkCenterRecovery_quotient, VertexFrame.include_totalIso_assoc]
      have hc : includeCoordinate (Spaces.read V i).away ⟨j, a⟩ ≫
          ModuleCat.ofHom (incomingMap (i := i) V) = arrowHom V a :=
        insert_sumArrows (B := (Spaces.read V i).away) (fun b : Port q i => arrowHom V b.2) ⟨j, a⟩
      rw [hc])
    (fun j a => ((A.sink j).false a).elim)
    (by
      intro j l a
      simp only [sourceFrame_offArrow, VertexFrame.offArrow_read]
      have e := (sinkFrame A V).offArrow_naturality (VertexFrame.read (reflectSink A V) i)
        (𝟙 _) j l (A.away j l a)
      simp only [VertexFrame.homAway_id_read, VertexFrame.offArrow_read, sinkFrame_offArrow] at e
      have ee := (A.away j l).symm_apply_apply a
      rw [ee] at e
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
        using congrArg (fun z => ((sinkFrame A V).away j).hom ≫ z ≫ ((sinkFrame A V).away l).hom) e.symm)

instance recoverSinkHom_isIso (V : Rep.{u, v, w, d} k q) (h) : IsIso (recoverSinkHom A V h) :=
  isIso_buildHom (sourceFrame A (reflectSink A V)) (VertexFrame.read V i) _ (sinkCenterRecovery A V h)
    (fun j => (sinkFrame A V).away j) _ _ _

/-- Reassemble the source representation after taking the quotient and then the kernel. -/
def recoverSourceHom (V : Rep.{u, v, w, d} k r)
    (h : Function.Injective (outgoingMap A V)) : V ⟶ reflectSink A (reflectSource A V) :=
  (VertexFrame.read V i).buildHom (sinkFrame A (reflectSource A V)) (A.source i)
    (sourceCenterRecovery A V h).hom (fun j => ((sourceFrame A V).away j).inv)
    (fun j a => ((A.source j).false a).elim)
    (by
      intro j a
      simp only [VertexFrame.outArrow_read, sinkFrame_outArrow,
        sourceCenterRecovery_inclusion_assoc]
      rw [VertexFrame.totalIso_inv_coord, ← Category.assoc (ModuleCat.ofHom (outgoingMap A V)),
        outgoingMap, tupleArrows_coord]
      have ee := (A.incident j).apply_symm_apply a
      rw [ee])
    (by
      intro j l a
      simp only [sinkFrame_offArrow, VertexFrame.offArrow_read]
      have e := (VertexFrame.read (reflectSource A V) i).offArrow_naturality (sourceFrame A V)
        (𝟙 _) j l ((A.away j l).symm a)
      simp only [VertexFrame.homAway_read_id, VertexFrame.offArrow_read, sourceFrame_offArrow] at e
      have ee := (A.away j l).apply_symm_apply a
      rw [ee] at e
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
        using congrArg (fun z => ((sourceFrame A V).away j).inv ≫ z ≫ ((sourceFrame A V).away l).inv) e.symm)

instance recoverSourceHom_isIso (V : Rep.{u, v, w, d} k r) (h) : IsIso (recoverSourceHom A V h) :=
  isIso_buildHom (VertexFrame.read V i) (sinkFrame A (reflectSource A V)) _ (sourceCenterRecovery A V h)
    (fun j => ((sourceFrame A V).away j).symm) _ _ _

private theorem sink_hom_ext_of_away {V W : Rep.{u, v, w, d} k q}
    (hs : Function.Surjective (incomingMap (i := i) V)) {f g : V ⟶ W}
    (h : ∀ j : Away i, component f j = component g j) : f = g := by
  apply rep_hom_ext
  intro j
  by_cases e : j = i
  · subst j
    have : Epi (ModuleCat.ofHom (incomingMap (i := i) V)) :=
      (ModuleCat.epi_iff_surjective _).mpr hs
    have h₁ := packedIn_naturality (VertexFrame.read V i) (VertexFrame.read W i) f
    have h₂ := packedIn_naturality (VertexFrame.read V i) (VertexFrame.read W i) g
    simp only [VertexFrame.totalHom, VertexFrame.homAt_read, packedIn_read] at h₁ h₂
    exact (cancel_epi (ModuleCat.ofHom (incomingMap (i := i) V))).mp
      (h₁.trans ((congrArg (fun z => ModuleCat.ofHom (totalMap (q := q) z) ≫
        ModuleCat.ofHom (incomingMap (i := i) W)) (funext h)).trans h₂.symm))
  · exact h ⟨j, e⟩

private theorem source_hom_ext_of_away {V W : Rep.{u, v, w, d} k r}
    (hs : Function.Injective (outgoingMap A W)) {f g : V ⟶ W}
    (h : ∀ j : Away i, component f j = component g j) : f = g := by
  apply rep_hom_ext
  intro j
  by_cases e : j = i
  · subst j
    have : Mono (ModuleCat.ofHom (outgoingMap A W)) :=
      (ModuleCat.mono_iff_injective _).mpr hs
    have h₁ := packedOut_naturality A (VertexFrame.read V i) (VertexFrame.read W i) f
    have h₂ := packedOut_naturality A (VertexFrame.read V i) (VertexFrame.read W i) g
    simp only [VertexFrame.totalHom, VertexFrame.homAt_read, packedOut_read] at h₁ h₂
    exact (cancel_mono (ModuleCat.ofHom (outgoingMap A W))).mp
      (h₁.symm.trans ((congrArg (fun z => ModuleCat.ofHom (outgoingMap A V) ≫
        ModuleCat.ofHom (totalMap (q := q) z)) (funext h)).trans h₂))
  · exact h ⟨j, e⟩

def sinkRestriction :
    (SinkObjects.{u, v, w, d} k q i).FullSubcategory ⥤
      (SourceObjects k A).FullSubcategory :=
  (SourceObjects k A).lift ((SinkObjects k q i).ι ⋙ reflectSinkFunctor A)
    (fun V => ⟨finite_reflectSink A V.obj V.property.1, outgoingMap_reflectSink_injective A V.obj⟩)

def sourceRestriction :
    (SourceObjects.{u, v, w, d} k A).FullSubcategory ⥤
      (SinkObjects k q i).FullSubcategory :=
  (SinkObjects k q i).lift ((SourceObjects k A).ι ⋙ reflectSourceFunctor A)
    (fun V => ⟨finite_reflectSource A V.obj V.property.1, incomingMap_reflectSource_surjective A V.obj⟩)

instance sinkRestriction_additive : (sinkRestriction (k := k) A).Additive where
  map_add {V W f g} := by
    apply (SourceObjects k A).ι.map_injective
    exact (reflectSinkFunctor A).map_add (f := f.hom) (g := g.hom)

instance sourceRestriction_additive : (sourceRestriction (k := k) A).Additive where
  map_add {V W f g} := by
    apply (SinkObjects k q i).ι.map_injective
    exact (reflectSourceFunctor A).map_add (f := f.hom) (g := g.hom)

instance sinkRestriction_linear : (sinkRestriction (k := k) A).Linear k where
  map_smul f c := by
    apply (SourceObjects k A).ι.map_injective
    exact (reflectSinkFunctor A).map_smul c f.hom

instance sourceRestriction_linear : (sourceRestriction (k := k) A).Linear k where
  map_smul f c := by
    apply (SinkObjects k q i).ι.map_injective
    exact (reflectSourceFunctor A).map_smul c f.hom

private theorem recoverSink_naturality {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W)
    (hV : Function.Surjective (incomingMap (i := i) V)) (hW : Function.Surjective (incomingMap (i := i) W)) :
    reflectSourceHom A (reflectSinkHom A f) ≫ recoverSinkHom A W hW = recoverSinkHom A V hV ≫ f := by
  apply sink_hom_ext_of_away (incomingMap_reflectSource_surjective A (reflectSink A V))
  intro j
  let P := sourceFrame A (reflectSink A V)
  let R := sourceFrame A (reflectSink A W)
  have e : P.homAway (VertexFrame.read W i) (reflectSourceHom A (reflectSinkHom A f) ≫ recoverSinkHom A W hW) j =
      P.homAway (VertexFrame.read W i) (recoverSinkHom A V hV ≫ f) j := by
    rw [VertexFrame.homAway_comp _ R _, VertexFrame.homAway_comp _ (VertexFrame.read V i) _]
    change (sourceFrame A (reflectSink A V)).homAway (sourceFrame A (reflectSink A W))
      (reflectSourceHom A (reflectSinkHom A f)) j ≫
      (sourceFrame A (reflectSink A W)).homAway (VertexFrame.read W i) (recoverSinkHom A W hW) j = _
    simp only [P, reflectSourceHom_away, recoverSinkHom, VertexFrame.homAway_buildHom, VertexFrame.homAway_read]
    have h := reflectSinkHom_away A f j
    simpa [VertexFrame.homAway] using congrArg (fun z => ((sinkFrame A V).away j).hom ≫ z) h
  simpa [VertexFrame.homAway, VertexFrame.read] using congrArg (fun z => (P.away j).hom ≫ z) e

private theorem recoverSource_naturality {V W : Rep.{u, v, w, d} k r} (f : V ⟶ W)
    (hV : Function.Injective (outgoingMap A V)) (hW : Function.Injective (outgoingMap A W)) :
    f ≫ recoverSourceHom A W hW = recoverSourceHom A V hV ≫ reflectSinkHom A (reflectSourceHom A f) := by
  apply source_hom_ext_of_away A (outgoingMap_reflectSink_injective A (reflectSource A W))
  intro j
  let P := sinkFrame A (reflectSource A V)
  let R := sinkFrame A (reflectSource A W)
  have e : (VertexFrame.read V i).homAway R (f ≫ recoverSourceHom A W hW) j =
      (VertexFrame.read V i).homAway R (recoverSourceHom A V hV ≫ reflectSinkHom A (reflectSourceHom A f)) j := by
    rw [VertexFrame.homAway_comp _ (VertexFrame.read W i) _, VertexFrame.homAway_comp _ P _]
    change _ = (VertexFrame.read V i).homAway (sinkFrame A (reflectSource A V)) (recoverSourceHom A V hV) j ≫
      (sinkFrame A (reflectSource A V)).homAway (sinkFrame A (reflectSource A W))
        (reflectSinkHom A (reflectSourceHom A f)) j
    simp only [R, reflectSinkHom_away, recoverSourceHom, VertexFrame.homAway_buildHom, VertexFrame.homAway_read]
    have h := reflectSourceHom_away A f j
    simpa [VertexFrame.homAway] using congrArg (fun z => z ≫ ((sourceFrame A W).away j).inv) h.symm
  simpa [VertexFrame.homAway, VertexFrame.read] using congrArg (fun z => z ≫ (R.away j).inv) e

def aggregateReflectionEquivalence :
    (SinkObjects.{u, v, w, d} k q i).FullSubcategory ≌
      (SourceObjects k A).FullSubcategory :=
  CategoryTheory.Equivalence.mk (sinkRestriction A) (sourceRestriction A)
    (NatIso.ofComponents (F := sinkRestriction A ⋙ sourceRestriction A) (G := 𝟭 _)
      (fun V => by
        exact ObjectProperty.isoMk (SinkObjects k q i)
          (@asIso _ _ _ _ (recoverSinkHom A V.obj V.property.2) (recoverSinkHom_isIso A V.obj V.property.2)))
      (by
        intro V W f
        apply (SinkObjects k q i).ι.map_injective
        exact recoverSink_naturality A f.hom V.property.2 W.property.2)).symm
    (NatIso.ofComponents (F := 𝟭 _) (G := sourceRestriction A ⋙ sinkRestriction A)
      (fun V => by
        exact ObjectProperty.isoMk (SourceObjects k A)
          (@asIso _ _ _ _ (recoverSourceHom A V.obj V.property.2) (recoverSourceHom_isIso A V.obj V.property.2)))
      (by
        intro V W f
        apply (SourceObjects k A).ι.map_injective
        exact recoverSource_naturality A f.hom V.property.2 W.property.2)).symm

end Equivalence

theorem reflectionEquivalence_exists : EquivalenceStatement.{u, v, w, d} := by
  intro Q k _ q r i _ A
  refine ⟨aggregateReflectionEquivalence A, fun _ => rfl, fun _ => rfl,
    sinkRestriction_additive A, sinkRestriction_linear A, sourceRestriction_additive A,
    sourceRestriction_linear A, ?_, ?_⟩
  · intro V W f
    change SinkMapFormula A f.hom (𝟙 _ ≫ reflectSinkHom A f.hom ≫ 𝟙 _)
    simpa using reflectSinkHom_formula A f.hom
  · intro V W f
    change SourceMapFormula A f.hom (𝟙 _ ≫ reflectSourceHom A f.hom ≫ 𝟙 _)
    simpa using reflectSourceHom_formula A f.hom

section Dimensions

variable [Finite (Port q i)] (A : ArrowReversal q r i)

private def incomingPorts (h : IsEmpty (q.Hom i i)) : Port q i ≃ Σ j : Q, q.Hom j i where
  toFun a := ⟨a.1, a.2⟩
  invFun := fun ⟨j, a⟩ => ⟨⟨j, fun he => h.false (he ▸ a)⟩, a⟩
  left_inv := by rintro ⟨⟨j, hj⟩, a⟩; rfl
  right_inv := by rintro ⟨j, a⟩; rfl

private def outgoingPorts : Port q i ≃ Σ j : Q, r.Hom i j where
  toFun a := ⟨a.1, A.incident a.1 a.2⟩
  invFun := fun ⟨j, a⟩ => ⟨⟨j, fun he => (A.source i).false (he ▸ a)⟩, (A.incident _).symm a⟩
  left_inv := by
    rintro ⟨⟨j, hj⟩, a⟩
    change (⟨⟨j, hj⟩, (A.incident ⟨j, hj⟩).symm (A.incident ⟨j, hj⟩ a)⟩ : Port q i) = _
    rw [(A.incident ⟨j, hj⟩).symm_apply_apply]
  right_inv := by
    rintro ⟨j, a⟩
    have hj : j ≠ i := fun he => (A.source i).false (he ▸ a)
    change (⟨j, A.incident ⟨j, hj⟩ ((A.incident ⟨j, hj⟩).symm a)⟩ : Σ j : Q, r.Hom i j) = _
    rw [(A.incident ⟨j, hj⟩).apply_symm_apply]

private theorem finrank_total [Fintype Q] {F : Q → ModuleCat.{d} k}
    (hF : ∀ j, Module.Finite k (F j)) {β : Q → Type v}
    (e : Port q i ≃ Σ j : Q, β j) (he : ∀ a, (e a).1 = a.1) :
    Module.finrank k (Total (q := q) (i := i) (fun j => F j)) =
      ∑ j : Q, Nat.card (β j) * Module.finrank k (F j) := by
  classical
  let (a : Index q i) : Module.Finite k (F (indexEquiv q i a).1) := hF _
  let : Finite (Σ j, β j) := Finite.of_equiv (Port q i) e
  let (j : Q) : Finite (β j) := Finite.of_injective (Sigma.mk j) sigma_mk_injective
  let (j : Q) : Fintype (β j) := Fintype.ofFinite _
  rw [Module.finrank_pi_fintype]
  calc
    _ = ∑ a : Σ j : Q, β j, Module.finrank k (F a.1) :=
      Fintype.sum_equiv ((indexEquiv q i).trans e) _ _ (fun a => by rw [Equiv.trans_apply, he])
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      change (∑ _ : β j, Module.finrank k (F j)) = _
      simp [Finset.sum_const, Nat.card_eq_fintype_card]

private theorem simpleReflection_self_of_noLoop (s : Quiver.{v} Q) [Fintype Q]
    (h : IsEmpty (s.Hom i i)) (x : Q → ℤ) :
    @SimpleReflectionsSpec.simpleReflection Q s _ ℤ _ i x i =
      -x i + ∑ j, (@FormsSpec.edgeMultiplicity Q s i j : ℤ) * x j := by
  classical
  let := s
  have hz : FormsSpec.edgeMultiplicity i i = 0 := by
    let := h
    simp [FormsSpec.edgeMultiplicity]
  have hrow (j : Q) :
      Forms.polarizationMatrix ℤ i j * x j =
        (if j = i then 2 * x i else 0) - (FormsSpec.edgeMultiplicity i j : ℤ) * x j := by
    by_cases hj : j = i
    · subst j
      simp [Forms.polarizationMatrix_apply_self, hz]
    · rw [Forms.polarizationMatrix_apply_of_ne (Ne.symm hj)]
      simp [hj]
  rw [SimpleReflections.simpleReflection_apply]
  change x i - ((Pi.single i (1 : ℤ)) ⬝ᵥ (Forms.polarizationMatrix ℤ *ᵥ x)) *
    (Pi.single i (1 : ℤ) : Q → ℤ) i = _
  rw [single_one_dotProduct, Pi.single_eq_same, mul_one]
  simp only [Matrix.mulVec, dotProduct, hrow, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem reflectSink_dimensionVector : SinkDimensionStatement.{u, v, w, d} := by
  intro Q k _ q r i _ _ A V
  refine ⟨finite_reflectSink A V.obj V.property.1, ?_⟩
  funext j
  let x := @FormsSpec.dimensionVector k Q _ q ⟨V.obj, V.property.1⟩
  change (Module.finrank k (vertex (reflectSink A V.obj) j) : ℤ) =
    @SimpleReflectionsSpec.simpleReflection Q q _ ℤ _ i x j
  by_cases hj : j = i
  · subst j
    rw [simpleReflection_self_of_noLoop q (A.sink i)]
    have hcenter := (sinkFrame A V.obj).center.toLinearEquiv.finrank_eq
    change Module.finrank k (vertex (reflectSink A V.obj) i) =
      Module.finrank k (LinearMap.ker (incomingMap (i := i) V.obj)) at hcenter
    rw [hcenter]
    let (a : Index q i) : Module.Finite k (vertex V.obj (indexEquiv q i a).1) := V.property.1 _
    have f := (incomingMap (i := i) V.obj).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr V.property.2, finrank_top] at f
    have hd := finrank_total V.property.1 (incomingPorts (A.sink i)) (fun _ => rfl)
    have hsum (j : Q) : @FormsSpec.edgeMultiplicity Q q i j = Nat.card (q.Hom j i) := by
      let := A.sink j
      change Nat.card (q.Hom i j) + Nat.card (q.Hom j i) = _
      simp
    simp only [hsum]
    have hx : ∀ j, x j = (Module.finrank k (vertex V.obj j) : ℤ) := fun _ => rfl
    simp only [hx]
    rw [hd] at f
    exact_mod_cast (show (Module.finrank k (LinearMap.ker (incomingMap (i := i) V.obj)) : ℤ) =
      -(Module.finrank k (vertex V.obj i) : ℤ) +
        ∑ j, (Nat.card (q.Hom j i) : ℤ) * (Module.finrank k (vertex V.obj j) : ℤ) by
      exact (eq_neg_add_of_add_eq (by exact_mod_cast f)))
  · have h := @SimpleReflections.simpleReflection_apply_ne Q q _ ℤ _ i j hj x
    rw [h]
    exact congrArg (fun n : ℕ => (n : ℤ)) ((sinkFrame A V.obj).away ⟨j, hj⟩).toLinearEquiv.finrank_eq

theorem reflectSource_dimensionVector : SourceDimensionStatement.{u, v, w, d} := by
  intro Q k _ q r i _ _ A V
  refine ⟨finite_reflectSource A V.obj V.property.1, ?_⟩
  funext j
  let x := @FormsSpec.dimensionVector k Q _ r ⟨V.obj, V.property.1⟩
  change (Module.finrank k (vertex (reflectSource A V.obj) j) : ℤ) =
    @SimpleReflectionsSpec.simpleReflection Q r _ ℤ _ i x j
  by_cases hj : j = i
  · subst j
    rw [simpleReflection_self_of_noLoop r (A.source i)]
    have hcenter := (sourceFrame A V.obj).center.toLinearEquiv.finrank_eq
    change Module.finrank k (vertex (reflectSource A V.obj) i) =
      Module.finrank k (_ ⧸ LinearMap.range (outgoingMap A V.obj)) at hcenter
    rw [hcenter]
    let (a : Index q i) : Module.Finite k (vertex V.obj (indexEquiv q i a).1) := V.property.1 _
    have f := (LinearMap.range (outgoingMap A V.obj)).finrank_quotient_add_finrank
    rw [← (LinearEquiv.ofInjective (outgoingMap A V.obj) V.property.2).finrank_eq] at f
    have hd := finrank_total V.property.1 (outgoingPorts A) (fun _ => rfl)
    have hsum (j : Q) : @FormsSpec.edgeMultiplicity Q r i j = Nat.card (r.Hom i j) := by
      let := A.source j
      change Nat.card (r.Hom i j) + Nat.card (r.Hom j i) = _
      simp
    simp only [hsum]
    have hx : ∀ j, x j = (Module.finrank k (vertex V.obj j) : ℤ) := fun _ => rfl
    simp only [hx]
    rw [hd] at f
    have hf : (Module.finrank k (vertex V.obj i) : ℤ) +
        (Module.finrank k (_ ⧸ LinearMap.range (outgoingMap A V.obj)) : ℤ) =
        ∑ j, (Nat.card (r.Hom i j) : ℤ) * (Module.finrank k (vertex V.obj j) : ℤ) := by
      exact_mod_cast (add_comm _ _).trans f
    exact eq_neg_add_of_add_eq hf
  · have h := @SimpleReflections.simpleReflection_apply_ne Q r _ ℤ _ i j hj x
    rw [h]
    exact congrArg (fun n : ℕ => (n : ℤ)) ((sourceFrame A V.obj).away ⟨j, hj⟩).toLinearEquiv.finrank_eq

theorem isolated_criterion : IsolatedCriterion.{u, v, w, d} := by
  intro Q k _ q r i _ A h
  have totalSubsingleton (B : Away i → ModuleCat.{d} k) : Subsingleton (Total (q := q) B) :=
    ⟨fun _ _ => funext fun a => (h.false (indexEquiv q i a)).elim⟩
  refine ⟨fun V => ?_, fun V => ?_⟩
  · have hs := totalSubsingleton (Spaces.read V i).away
    exact ⟨fun e => e.subsingleton, fun hV x => ⟨0, hV.elim _ _⟩⟩
  · have hs := totalSubsingleton (Spaces.read V i).away
    exact ⟨fun e => e.subsingleton, fun hV _ _ _ => hV.elim _ _⟩

end Dimensions

section SimpleSummands

private theorem summand_iff_retract {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] [HasKernels C] (S V : C) :
    (∃ W, Nonempty (V ≅ S ⊞ W)) ↔ ∃ (f : S ⟶ V) (g : V ⟶ S), f ≫ g = 𝟙 S := by
  constructor
  · rintro ⟨W, ⟨e⟩⟩
    exact ⟨biprod.inl ≫ e.inv, e.hom ≫ biprod.fst, by simp⟩
  · rintro ⟨f, g, h⟩
    let p := kernel.lift g (𝟙 V - g ≫ f) (by simp [Preadditive.sub_comp, h])
    have hp : p ≫ kernel.ι g = 𝟙 V - g ≫ f := kernel.lift_ι _ _ _
    have hfp : f ≫ p = 0 := by
      rw [← cancel_mono (kernel.ι g), Category.assoc, hp, zero_comp]
      simp [Preadditive.comp_sub, reassoc_of% h]
    let X := ShortComplex.mk f p hfp
    have E : X.Splitting :=
      { r := g
        s := kernel.ι g
        f_r := h
        s_g := by
          change kernel.ι g ≫ p = 𝟙 _
          rw [← cancel_mono (kernel.ι g), Category.assoc, hp]
          simp [Preadditive.comp_sub, ← Category.assoc]
        id := by
          change g ≫ f + p ≫ kernel.ι g = 𝟙 V
          rw [hp, add_sub_cancel] }
    exact ⟨kernel g, ⟨E.isoBinaryBiproduct⟩⟩

private abbrev simpleAt (s : Quiver.{v} Q) (i : Q) : Rep.{u, v, w, max w d} k s :=
  @FormsSpec.vertexSimple.{u, v, w, d} k Q _ s i

private def simpleCenter (s : Quiver.{v} Q) (i : Q) :
    vertex (simpleAt (k := k) s i : Rep.{u, v, w, max w d} k s) i ≃ₗ[k] k :=
  (eqToIso (@Forms.vertexSimple_vertex_self k Q _ s i)).toLinearEquiv.trans ULift.moduleEquiv

@[simp] private theorem simple_arrow {s : Quiver.{v} Q} (i : Q) {j l : Q} (a : s.Hom j l) :
    arrowHom (simpleAt (k := k) s i : Rep.{u, v, w, max w d} k s) a = 0 := by
  apply ModuleCat.hom_ext
  exact @Forms.vertexSimple_arrow k Q _ s i j l a

private theorem simpleOff_zero (s : Quiver.{v} Q) {i j : Q} (hj : j ≠ i) :
    IsZero (vertex (simpleAt (k := k) s i : Rep.{u, v, w, max w d} k s) j) := by
  rw [show vertex (simpleAt (k := k) s i : Rep.{u, v, w, max w d} k s) j =
    ModuleCat.of k PUnit.{max w d + 1} from @Forms.vertexSimple_vertex_of_ne k Q _ s i j hj]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

private theorem simpleCenter_id_ne_zero (s : Quiver.{v} Q) (i : Q) :
    (𝟙 (vertex (simpleAt (k := k) s i : Rep.{u, v, w, max w d} k s) i)) ≠ 0 := by
  intro h
  let e := simpleCenter (k := k) s i
  have hz := congrArg (fun f => e (f (e.symm 1))) h
  simp at hz

set_option maxHeartbeats 400000 in
private theorem simple_retract_of_vector {s : Quiver.{v} Q} (V : Rep.{u, v, w, max w d} k s)
    (h : IsEmpty (s.Hom i i)) (x : vertex V i) (ℓ : vertex V i →ₗ[k] k) (hℓ : ℓ x = 1)
    (hi : ∀ (j : Away i) (a : s.Hom j i) (y : vertex V j), ℓ (arrow V a y) = 0)
    (ho : ∀ (j : Away i) (a : s.Hom i j), arrow V a x = 0) :
    ∃ (f : simpleAt s i ⟶ V) (g : V ⟶ simpleAt s i), f ≫ g = 𝟙 (simpleAt s i) := by
  let S : Rep.{u, v, w, max w d} k s := simpleAt s i
  let P := VertexFrame.read S i
  let R := VertexFrame.read V i
  let e : vertex S i ≃ₗ[k] k := simpleCenter s i
  let c : vertex S i ⟶ vertex V i := ModuleCat.ofHom (e.toLinearMap.smulRight x)
  let p : vertex V i ⟶ vertex S i := ModuleCat.ofHom (e.symm.toLinearMap.comp ℓ)
  let f : S ⟶ V := P.buildHom R h c (fun _ => 0)
    (by intro j a; simp [P, R, S])
    (by
      intro j a
      simp only [R, P, S, VertexFrame.outArrow_read, simple_arrow, zero_comp]
      apply ModuleCat.hom_ext
      ext y
      change 0 = arrow V a (e y • x)
      rw [map_smul, ho j a, smul_zero])
    (by intro j l a; simp)
  let g : V ⟶ S := R.buildHom P h p (fun _ => 0)
    (by
      intro j a
      simp only [R, P, S, VertexFrame.inArrow_read, simple_arrow, zero_comp]
      apply ModuleCat.hom_ext
      ext y
      change e.symm (ℓ (arrow V a y)) = 0
      rw [hi j a, map_zero])
    (by intro j a; simp [R, P, S])
    (by intro j l a; simp)
  refine ⟨f, g, ?_⟩
  apply P.hom_ext P
  · rw [VertexFrame.homAt_comp _ R _, VertexFrame.homAt_id]
    simp only [f, g, VertexFrame.homAt_buildHom]
    apply ModuleCat.hom_ext
    ext y
    change e.symm (ℓ (e y • x)) = y
    simp [hℓ]
  · intro j
    exact (simpleOff_zero s j.property).eq_of_src _ _

private theorem incomingMap_simple [Finite (Port q i)] :
    incomingMap (i := i) (simpleAt (k := k) q i : Rep.{u, v, w, max w d} k q) = 0 := by
  have h : (fun a : Port q i => arrowHom (simpleAt (k := k) q i :
      Rep.{u, v, w, max w d} k q) a.2) = fun _ => 0 := by
    funext a
    exact simple_arrow i a.2
  change sumArrows (B := (Spaces.read (simpleAt q i : Rep.{u, v, w, max w d} k q) i).away)
    (fun a => arrowHom (simpleAt q i) a.2) = 0
  rw [h]
  exact (LinearMap.lsum k _ k).map_zero

private theorem outgoingMap_simple [Finite (Port q i)] (A : ArrowReversal q r i) :
    outgoingMap A (simpleAt (k := k) r i : Rep.{u, v, w, max w d} k r) = 0 := by
  apply LinearMap.ext
  intro x
  funext a
  change (arrowHom (simpleAt r i) (A.incident _ (indexEquiv q i a).2)) x = 0
  rw [simple_arrow]
  rfl

theorem sink_noSimpleSummand_iff : SinkCriterionStatement.{u, v, w, d} := by
  classical
  intro Q k _ q i _ hs V
  let := q
  unfold NoSimpleSummand
  rw [summand_iff_retract]
  constructor
  · intro hn
    by_contra h
    change ¬ ∀ y, ∃ x, incomingMap (i := i) V x = y at h
    push Not at h
    obtain ⟨x, hx⟩ := h
    let M := LinearMap.range (incomingMap (i := i) V)
    obtain ⟨ℓ, hzero, hℓ⟩ :=
      LinearMap.exists_extend_of_notMem (0 : M →ₗ[k] k) (show x ∉ M from fun ⟨z, hz⟩ => hx z hz) 1
    apply hn
    apply simple_retract_of_vector V (hs i) x ℓ hℓ
    · intro j a y
      have hn' := LinearMap.congr_fun hzero
        ⟨arrow V a y, ⟨includeCoordinate (Spaces.read V i).away ⟨j, a⟩ y,
          congrArg (fun f => f y) (insert_sumArrows (B := (Spaces.read V i).away)
            (fun b : Port q i => arrowHom V b.2) ⟨j, a⟩)⟩⟩
      exact hn'
    · intro j a
      exact ((hs j).false a).elim
  · intro h ⟨f, g, hfg⟩
    have he := incomingMap_naturality (i := i) g
    rw [incomingMap_simple, LinearMap.zero_comp] at he
    have hz : component g i = 0 := by
      apply ModuleCat.hom_ext
      ext y
      obtain ⟨x, rfl⟩ := h y
      exact (LinearMap.congr_fun he x).symm
    have hc := congrArg (fun f => component f i) hfg
    change component f i ≫ component g i = 𝟙 _ at hc
    rw [hz, comp_zero] at hc
    exact simpleCenter_id_ne_zero q i hc.symm

theorem source_noSimpleSummand_iff : SourceCriterionStatement.{u, v, w, d} := by
  classical
  intro Q k _ q r i _ A V
  let := r
  unfold NoSimpleSummand
  rw [summand_iff_retract]
  constructor
  · intro hn
    by_contra h
    rw [← LinearMap.ker_eq_bot, LinearMap.ker (outgoingMap A V) |>.eq_bot_iff] at h
    push Not at h
    obtain ⟨x, hx, hx0⟩ := h
    obtain ⟨ℓ, _, hℓ⟩ := LinearMap.exists_extend_of_notMem
      (0 : (⊥ : Submodule k (vertex V i)) →ₗ[k] k) (by simpa using hx0) 1
    apply hn
    apply simple_retract_of_vector V (A.source i) x ℓ hℓ
    · intro j a
      exact ((A.source j).false a).elim
    · intro j a
      have ht := congrArg (fun t => coord (Spaces.read V i).away ⟨j, (A.incident j).symm a⟩ t)
        (LinearMap.mem_ker.mp hx)
      rw [map_zero] at ht
      have hh := congrArg (fun (f : vertex V i ⟶ vertex V j) => f x)
        (tupleArrows_coord (B := (Spaces.read V i).away)
          (fun b : Port q i => arrowHom V (A.incident b.1 b.2)) ⟨j, (A.incident j).symm a⟩)
      rw [(A.incident j).apply_symm_apply a] at hh
      exact hh.symm.trans ht
  · intro h ⟨f, g, hfg⟩
    have he := outgoingMap_naturality (A := A) f
    rw [outgoingMap_simple, LinearMap.comp_zero] at he
    have hz : component f i = 0 := by
      apply ModuleCat.hom_ext
      ext y
      apply h
      change outgoingMap A V (component f i y) = outgoingMap A V 0
      rw [map_zero]
      exact (LinearMap.congr_fun he y).symm
    have hc := congrArg (fun f => component f i) hfg
    change component f i ≫ component g i = 𝟙 _ at hc
    rw [hz, zero_comp] at hc
    exact simpleCenter_id_ne_zero r i hc.symm

theorem summandFreeEquivalence_exists : SummandFreeEquivalenceStatement.{u, v, w, d} := by
  intro Q k _ q r i _ A
  have hq : WithoutSimple.{u, v, w, d} k q i = SinkObjects.{u, v, w, max w d} k q i := by
    funext V
    exact propext (and_congr_right fun _ => sink_noSimpleSummand_iff (A.sink) V)
  have hr : WithoutSimple.{u, v, w, d} k r i = SourceObjects.{u, v, w, max w d} k A := by
    funext V
    exact propext (and_congr_right fun _ => source_noSimpleSummand_iff A V)
  let hasEquivalence (P : ObjectProperty (Rep.{u, v, w, max w d} k q))
      (R : ObjectProperty (Rep.{u, v, w, max w d} k r)) : Prop :=
    ∃ E : P.FullSubcategory ≌ R.FullSubcategory,
      ∃ (h₁ : ∀ V, (E.functor.obj V).obj = reflectSink A V.obj)
        (h₂ : ∀ V, (E.inverse.obj V).obj = reflectSource A V.obj),
        E.functor.Additive ∧ E.functor.Linear k ∧ E.inverse.Additive ∧ E.inverse.Linear k ∧
        (∀ (V W : P.FullSubcategory) (f : V ⟶ W),
          SinkMapFormula A f.hom (eqToHom (h₁ V).symm ≫ (E.functor.map f).hom ≫ eqToHom (h₁ W))) ∧
        (∀ (V W : R.FullSubcategory) (f : V ⟶ W),
          SourceMapFormula A f.hom (eqToHom (h₂ V).symm ≫ (E.inverse.map f).hom ≫ eqToHom (h₂ W)))
  change hasEquivalence (WithoutSimple k q i) (WithoutSimple k r i)
  rw [hq, hr]
  exact reflectionEquivalence_exists A

end SimpleSummands

section Indecomposables

variable [Finite (Port q i)] (A : ArrowReversal q r i)

private theorem sinkObjects_of_retract {V W : Rep.{u, v, w, d} k q} (f : W ⟶ V) (g : V ⟶ W)
    (hg : f ≫ g = 𝟙 W) (hV : SinkObjects k q i V) : SinkObjects k q i W := by
  let := q
  refine ⟨Forms.finite_of_retract f g hg hV.1, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hV.2 (component f i y)
  let φ := totalMap (q := q) (B := (Spaces.read V i).away) (C := (Spaces.read W i).away)
    (fun j => component g j)
  refine ⟨φ x, ?_⟩
  have h := LinearMap.congr_fun (incomingMap_naturality (i := i) g) x
  change incomingMap (i := i) W (φ x) =
    component g i (incomingMap (i := i) V x) at h
  rw [h, hx]
  exact congrArg (fun m => component m i y) hg

private theorem sourceObjects_of_retract {V W : Rep.{u, v, w, d} k r} (f : W ⟶ V) (g : V ⟶ W)
    (hg : f ≫ g = 𝟙 W) (hV : SourceObjects k A V) : SourceObjects k A W := by
  let := r
  refine ⟨Forms.finite_of_retract f g hg hV.1, ?_⟩
  intro x y h
  have ht (z : vertex W i) : totalMap (q := q) (fun j => component f j) (outgoingMap A W z) =
      outgoingMap A V (component f i z) :=
    LinearMap.congr_fun (outgoingMap_naturality (A := A) f) z
  have he := hV.2 ((ht x).symm.trans ((congrArg
    (fun z => totalMap (q := q) (fun j => component f j) z) h).trans (ht y)))
  have hg' (z : vertex W i) : component g i (component f i z) = z :=
    congrArg (fun m => component m i z) hg
  rw [← hg' x, ← hg' y, he]

private theorem indecomposable_of_iso {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {X Y : C} (e : X ≅ Y) (hX : Indecomposable X) : Indecomposable Y :=
  ⟨fun hy => hX.1 (hy.of_iso e), fun U V h => hX.2 U V (e.trans h)⟩

/-- Recovery on an object and its summands transfers its ambient indecomposability. -/
private theorem indecomposable_of_inverse {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    {P : ObjectProperty D} {X : C} (hX : Indecomposable X) (hFX : P (F.obj X))
    (eX : G.obj (F.obj X) ≅ X)
    (recover : ∀ Y, P Y → Nonempty (F.obj (G.obj Y) ≅ Y))
    (retract : ∀ {Y Z} (f : Y ⟶ Z) (g : Z ⟶ Y), f ≫ g = 𝟙 Y → P Z → P Y) :
    Indecomposable (F.obj X) := by
  let := preservesBinaryBiproducts_of_preservesBiproducts G
  constructor
  · intro h
    exact hX.1 ((G.map_isZero h).of_iso eX.symm)
  · intro Y Z e
    have hY := retract (biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst) (by simp) hFX
    have hZ := retract (biprod.inr ≫ e.inv) (e.hom ≫ biprod.snd) (by simp) hFX
    have h := hX.2 (G.obj Y) (G.obj Z)
      (eX.symm.trans ((G.mapIso e).trans (G.mapBiprod Y Z)))
    obtain ⟨eY⟩ := recover Y hY
    obtain ⟨eZ⟩ := recover Z hZ
    exact h.imp (fun hy => (F.map_isZero hy).of_iso eY.symm) (fun hz => (F.map_isZero hz).of_iso eZ.symm)

private theorem reflectSink_indec (V : (SinkObjects.{u, v, w, d} k q i).FullSubcategory)
    (h : Indecomposable V.obj) : Indecomposable (reflectSink A V.obj) := by
  apply indecomposable_of_inverse (reflectSinkFunctor A) (reflectSourceFunctor A) h
    ((sinkRestriction A).obj V).property
  · exact @asIso _ _ _ _ (recoverSinkHom A V.obj V.property.2) (recoverSinkHom_isIso A V.obj V.property.2)
  · intro W hW
    exact ⟨(@asIso _ _ _ _ (recoverSourceHom A W hW.2) (recoverSourceHom_isIso A W hW.2)).symm⟩
  · exact sourceObjects_of_retract A

private theorem reflectSource_indec (V : (SourceObjects.{u, v, w, d} k A).FullSubcategory)
    (h : Indecomposable V.obj) : Indecomposable (reflectSource A V.obj) := by
  apply indecomposable_of_inverse (reflectSourceFunctor A) (reflectSinkFunctor A) h
    ((sourceRestriction A).obj V).property
  · exact (@asIso _ _ _ _ (recoverSourceHom A V.obj V.property.2) (recoverSourceHom_isIso A V.obj V.property.2)).symm
  · intro W hW
    exact ⟨@asIso _ _ _ _ (recoverSinkHom A W hW.2) (recoverSinkHom_isIso A W hW.2)⟩
  · exact sinkObjects_of_retract

end Indecomposables

theorem reflectSink_indecomposable_iff : SinkIndecomposableStatement.{u, v, w, d} := by
  intro Q k _ q r i _ A V
  refine ⟨fun h => ?_, reflectSink_indec A V⟩
  exact indecomposable_of_iso
    (@asIso _ _ _ _ (recoverSinkHom A V.obj V.property.2) (recoverSinkHom_isIso A V.obj V.property.2))
    (reflectSource_indec A ((sinkRestriction A).obj V) h)

theorem reflectSource_indecomposable_iff : SourceIndecomposableStatement.{u, v, w, d} := by
  intro Q k _ q r i _ A V
  refine ⟨fun h => ?_, reflectSource_indec A V⟩
  exact indecomposable_of_iso
    (@asIso _ _ _ _ (recoverSourceHom A V.obj V.property.2) (recoverSourceHom_isIso A V.obj V.property.2)).symm
    (reflectSink_indec A ((sourceRestriction A).obj V) h)

section Orientations

private def arrowsOverPairs (s : Quiver.{v} Q) :
    @RM03.Arrow Q s ≃ Σ p : Q × Q, s.Hom p.1 p.2 where
  toFun a := ⟨(a.1, a.2.1), a.2.2⟩
  invFun a := ⟨a.1.1, a.1.2, a.2⟩
  left_inv := by rintro ⟨j, l, a⟩; rfl
  right_inv := by rintro ⟨⟨j, l⟩, a⟩; rfl

private def reverseEndpoints (i : Q) : Equiv.Perm (Q × Q) := by
  classical
  let f (p : Q × Q) := if p.1 = i ∨ p.2 = i then p.swap else p
  refine Function.Involutive.toPerm f ?_
  rintro ⟨j, l⟩
  by_cases h : j = i ∨ l = i
  · have h' : l = i ∨ j = i := h.symm
    simp [f, h, h']
  · simp [f, h]

private theorem reverseEndpoints_incident {j l : Q} (h : j = i ∨ l = i) :
    reverseEndpoints i (j, l) = (l, j) := by
  classical
  change (if j = i ∨ l = i then (l, j) else (j, l)) = _
  rw [ite_eq_left h]

private theorem reverseEndpoints_away {j l : Q} (hj : j ≠ i) (hl : l ≠ i) :
    reverseEndpoints i (j, l) = (j, l) := by
  classical
  change (if j = i ∨ l = i then (l, j) else (j, l)) = _
  rw [ite_eq_right (not_or.mpr ⟨hj, hl⟩)]

private def reverseArrowEquiv (s : Quiver.{v} Q) (i : Q) :
    @RM03.Arrow Q (reverseAt s i) ≃ @RM03.Arrow Q s :=
  (arrowsOverPairs (reverseAt s i)).trans
    ((Equiv.sigmaCongr (reverseEndpoints i) fun p => Equiv.cast (by
        classical
        rcases p with ⟨j, l⟩
        change (if j = i ∨ l = i then s.Hom l j else s.Hom j l) =
          s.Hom (reverseEndpoints i (j, l)).1 (reverseEndpoints i (j, l)).2
        by_cases h : j = i ∨ l = i
        · rw [ite_eq_left h, reverseEndpoints_incident h]
        · rw [ite_eq_right h, reverseEndpoints_away (not_or.mp h).1 (not_or.mp h).2])).trans
      (arrowsOverPairs s).symm)

theorem finite_reverseAt : ReversalFinite.{u, v} := by
  intro Q s _ i
  exact Finite.of_equiv _ (reverseArrowEquiv s i).symm

theorem finitePort_of_source : SourcePortFinite.{u, v} := by
  intro Q q r i A _
  let f := @Sigma.mk Q (fun j : Q => Σ l : Q, r.Hom j l) i
  have hf : Function.Injective f := sigma_mk_injective
  exact Finite.of_injective _ (hf.comp (outgoingPorts A).injective)

private theorem path_from_sink (s : Quiver.{v} Q) (h : IsSink s i)
    {l : Q} (p : @Quiver.Path Q s i l) : l = i ∧ p.length = 0 := by
  induction p with
  | nil => exact ⟨rfl, rfl⟩
  | @cons j l p a ih =>
    obtain ⟨rfl, _⟩ := ih
    exact ((h l).false a).elim

private theorem path_to_source_stays_away (s : Quiver.{v} Q) (h : IsSource s i)
    {j l : Q} (hj : j ≠ i) (p : @Quiver.Path Q s j l) : l ≠ i := by
  cases p with
  | nil => exact hj
  | @cons y l p a =>
    rintro rfl
    exact (h y).false a

private theorem transport_path_away (s t : Quiver.{v} Q)
    (hs : IsSink s i ∨ IsSource s i)
    (f : ∀ a b : Away i, s.Hom a b → t.Hom a b)
    {j l : Q} (hj : j ≠ i) (p : @Quiver.Path Q s j l) (hl : l ≠ i) :
    ∃ p' : @Quiver.Path Q t j l, @Quiver.Path.length Q t j l p' = @Quiver.Path.length Q s j l p := by
  induction p with
  | nil => exact ⟨@Quiver.Path.nil Q t j, rfl⟩
  | @cons y l p a ih =>
    have hy : y ≠ i := by
      rcases hs with h | h
      · rintro rfl
        exact (h l).false a
      · exact path_to_source_stays_away s h hj p
    obtain ⟨p', hp'⟩ := ih hy
    exact ⟨@Quiver.Path.cons Q t j y l p' (f ⟨y, hy⟩ ⟨l, hl⟩ a), congrArg (· + 1) hp'⟩

private theorem acyclic_of_away (s t : Quiver.{v} Q) (hs : IsSink s i ∨ IsSource s i)
    (f : ∀ a b : Away i, s.Hom a b → t.Hom a b)
    (ht : ¬ @RM03.HasOrientedCycle Q t) : ¬ @RM03.HasOrientedCycle Q s := by
  have acs := @RM03.hasOrientedCycle_iff_exists_closed_path Q s
  have act := @RM03.hasOrientedCycle_iff_exists_closed_path Q t
  intro hc
  obtain ⟨j, p, hp⟩ := acs.mp hc
  have hj : j ≠ i := by
    rintro rfl
    rcases hs with h | h
    · exact (Nat.ne_of_gt hp) (path_from_sink s h p).2
    · cases p with
      | nil => exact (Nat.lt_irrefl _ hp)
      | @cons y _ p a => exact (h y).false a
  obtain ⟨p', hp'⟩ := transport_path_away s t hs f hj p hj
  exact ht (act.mpr ⟨j, p', hp'.symm ▸ hp⟩)

theorem acyclic_reverseAt : ReversalAcyclic.{u, v} := by
  intro Q q i h hq
  rcases h with hs | hs
  · let A := reversalAtSink q i hs
    exact acyclic_of_away (reverseAt q i) q (.inr A.source) (fun j l => (A.away j l).symm) hq
  · let A := reversalAtSource q i hs
    exact acyclic_of_away (reverseAt q i) q (.inl A.sink) (fun j l => A.away j l) hq

private def reversalFiber (A : ArrowReversal q r i) (p : Q × Q) :
    q.Hom p.1 p.2 ≃ r.Hom (reverseEndpoints i p).1 (reverseEndpoints i p).2 := by
  rcases p with ⟨j, l⟩
  by_cases hj : j = i
  · subst j
    rw [reverseEndpoints_incident (Or.inl rfl : i = i ∨ l = i)]
    let := A.sink l
    let := A.source l
    exact Equiv.equivOfIsEmpty _ _
  · by_cases hl : l = i
    · subst l
      rw [reverseEndpoints_incident (Or.inr rfl : j = i ∨ i = i)]
      exact A.incident ⟨j, hj⟩
    · rw [reverseEndpoints_away hj hl]
      exact A.away ⟨j, hj⟩ ⟨l, hl⟩

private def reversalArrows (A : ArrowReversal q r i) : @RM03.Arrow Q q ≃ @RM03.Arrow Q r :=
  (arrowsOverPairs q).trans ((Equiv.sigmaCongr (reverseEndpoints i) (reversalFiber A)).trans
    (arrowsOverPairs r).symm)

private theorem titsForm_reversal [Fintype Q] [Fintype (@RM03.Arrow Q q)]
    [Fintype (@RM03.Arrow Q r)] (A : ArrowReversal q r i) (x : Q → ℤ) :
    @FormsSpec.titsForm Q q _ _ ℤ _ x = @FormsSpec.titsForm Q r _ _ ℤ _ x := by
  unfold FormsSpec.titsForm FormsSpec.eulerForm
  congr 1
  apply Fintype.sum_equiv (reversalArrows A)
  rintro ⟨j, l, a⟩
  change x j * x l = x (reverseEndpoints i (j, l)).1 * x (reverseEndpoints i (j, l)).2
  by_cases h : j = i ∨ l = i
  · rw [reverseEndpoints_incident h, mul_comm]
  · rw [reverseEndpoints_away (not_or.mp h).1 (not_or.mp h).2]

end Orientations

theorem reflectSink_titsForm : SinkTitsFormStatement.{u, v, w, d} := by
  intro Q k _ q r i _ _ _ _ A hq V
  obtain ⟨h, hd⟩ := reflectSink_dimensionVector A V
  refine ⟨h, ?_⟩
  rw [hd, ← titsForm_reversal A]
  let := q
  exact SimpleReflections.simpleReflection_preservesTitsForm hq i _

theorem reflectSource_titsForm : SourceTitsFormStatement.{u, v, w, d} := by
  intro Q k _ q r i _ _ _ _ A hr V
  obtain ⟨h, hd⟩ := reflectSource_dimensionVector A V
  refine ⟨h, ?_⟩
  rw [hd, titsForm_reversal A]
  let := r
  exact SimpleReflections.simpleReflection_preservesTitsForm hr i _

-- Canonical constructions exported as the implementation-facing interface.
def IsSink : IsSinkType.{u, v} := @ReflectionEquivalenceSpec.IsSink.{u, v}
def IsSource : IsSourceType.{u, v} := @ReflectionEquivalenceSpec.IsSource.{u, v}
@[instance_reducible]
def reverseAt : ReverseAtType.{u, v} := @ReflectionEquivalenceSpec.reverseAt.{u, v}
def reversalAtSink : ReversalAtSinkType.{u, v} := @ReflectionEquivalenceSpec.reversalAtSink.{u, v}
def reversalAtSource : ReversalAtSourceType.{u, v} := @ReflectionEquivalenceSpec.reversalAtSource.{u, v}
def noSimpleSummand : NoSimpleSummandType.{u, v, w, d} :=
  @ReflectionEquivalenceSpec.NoSimpleSummand.{u, v, w, d}
def incomingMap : IncomingMapType.{u, v, w, d} := @ReflectionEquivalenceSpec.incomingMap.{u, v, w, d}
def outgoingMap : OutgoingMapType.{u, v, w, d} := @ReflectionEquivalenceSpec.outgoingMap.{u, v, w, d}
def reflectSink : ReflectSinkType.{u, v, w, d} := @ReflectionEquivalenceSpec.reflectSink.{u, v, w, d}
def reflectSource : ReflectSourceType.{u, v, w, d} := @ReflectionEquivalenceSpec.reflectSource.{u, v, w, d}

end
end RepTheorySurvey.Quiver.ReflectionEquivalence
