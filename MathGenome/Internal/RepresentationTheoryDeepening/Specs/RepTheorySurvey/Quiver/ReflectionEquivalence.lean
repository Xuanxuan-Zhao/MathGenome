import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.SimpleReflections
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms

/-! Sink and source reflection for the pinned category of representations. -/

open CategoryTheory CategoryTheory.Limits
open RM03 (QuiverRepresentation)
open scoped BigOperators

namespace RepTheorySurvey.Quiver.ReflectionEquivalenceSpec

noncomputable section

set_option linter.checkUnivs false

universe u v w d

variable {Q : Type u} {k : Type w} [Field k]

abbrev Rep (k : Type w) [Field k] (q : Quiver.{v} Q) :=
  @QuiverRepresentation.{u, v, w, d} k Q _ q

abbrev vertex {q : Quiver.{v} Q} (V : Rep.{u, v, w, d} k q) (j : Q) :=
  @QuiverRepresentation.vertex k Q _ q V j

abbrev arrow {q : Quiver.{v} Q} (V : Rep.{u, v, w, d} k q) {j l : Q} (a : q.Hom j l) :=
  @QuiverRepresentation.arrow k Q _ q V j l a

abbrev component {q : Quiver.{v} Q} {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W) (j : Q) :
    vertex V j ⟶ vertex W j :=
  ModuleCat.ofHom (@QuiverRepresentation.component k Q _ q V W f j)

abbrev arrowHom {q : Quiver.{v} Q} (V : Rep.{u, v, w, d} k q) {j l : Q} (a : q.Hom j l) :
    vertex V j ⟶ vertex V l := ModuleCat.ofHom (arrow V a)

abbrev Away (i : Q) := {j : Q // j ≠ i}

def IsSink (q : Quiver.{v} Q) (i : Q) : Prop := ∀ j, IsEmpty (q.Hom i j)
def IsSource (q : Quiver.{v} Q) (i : Q) : Prop := ∀ j, IsEmpty (q.Hom j i)

/-- Reverse exactly those arrows incident to the given vertex. -/
@[instance_reducible]
def reverseAt (q : Quiver.{v} Q) (i : Q) : Quiver.{v} Q := by
  classical
  exact ⟨fun j l => if j = i ∨ l = i then q.Hom l j else q.Hom j l⟩

/-- The same incident arrow indices in the two orientations, and the unchanged off-vertex arrows. -/
structure ArrowReversal (q r : Quiver.{v} Q) (i : Q) where
  sink : IsSink q i
  source : IsSource r i
  incident : ∀ j : Away i, q.Hom j i ≃ r.Hom i j
  away : ∀ j l : Away i, q.Hom j l ≃ r.Hom j l

def reversalAtSink (q : Quiver.{v} Q) (i : Q) (h : IsSink q i) :
    ArrowReversal q (reverseAt q i) i where
  sink := h
  source j := by
    classical
    change IsEmpty (if j = i ∨ i = i then q.Hom i j else q.Hom j i)
    simpa using h j
  incident j := Equiv.cast (by
    classical
    change q.Hom j i = (if i = i ∨ (j : Q) = i then q.Hom j i else q.Hom i j)
    simp)
  away j l := Equiv.cast (by
    classical
    change q.Hom j l = (if (j : Q) = i ∨ (l : Q) = i then q.Hom l j else q.Hom j l)
    simp [j.property, l.property])

def reversalAtSource (r : Quiver.{v} Q) (i : Q) (h : IsSource r i) :
    ArrowReversal (reverseAt r i) r i where
  sink j := by
    classical
    change IsEmpty (if i = i ∨ j = i then r.Hom j i else r.Hom i j)
    simpa using h j
  source := h
  incident j := Equiv.cast (by
    classical
    change (if (j : Q) = i ∨ i = i then r.Hom i j else r.Hom j i) = r.Hom i j
    simp)
  away j l := Equiv.cast (by
    classical
    change (if (j : Q) = i ∨ (l : Q) = i then r.Hom l j else r.Hom j l) = r.Hom j l
    simp [j.property, l.property])

variable {q r : Quiver.{v} Q} {i : Q}

/-- Incoming arrows at the sink, including each parallel arrow separately. -/
abbrev Port (q : Quiver.{v} Q) (i : Q) := Σ j : Away i, q.Hom j i

instance [Finite (@RM03.Arrow Q q)] : Finite (Port q i) :=
  Finite.of_injective (fun a => (⟨a.1, i, a.2⟩ : @RM03.Arrow Q q)) (by
    rintro ⟨⟨j, hj⟩, a⟩ ⟨⟨l, hl⟩, b⟩ e
    have h : j = l := congrArg Sigma.fst e
    subst l
    cases e
    rfl)

section Coordinates

variable [Finite (Port q i)]

/-- A finite indexing type in the universe of natural numbers, so reflection keeps the
universe of the vertex spaces. -/
abbrev Index (q : Quiver.{v} Q) (i : Q) := Fin (Nat.card (Port q i))

def indexEquiv (q : Quiver.{v} Q) (i : Q) [Finite (Port q i)] :
    Index q i ≃ Port q i := by
  letI := Fintype.ofFinite (Port q i)
  exact (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := Port q i)).symm).symm

abbrev Total (B : Away i → ModuleCat.{d} k) := ∀ a : Index q i, B (indexEquiv q i a).1

def coordinateIso (B : Away i → ModuleCat.{d} k) (a : Port q i) :
    B (indexEquiv q i ((indexEquiv q i).symm a)).1 ≅ B a.1 :=
  eqToIso (congrArg (fun p : Port q i => B p.1) ((indexEquiv q i).apply_symm_apply a))

def coord (B : Away i → ModuleCat.{d} k) (a : Port q i) :
    ModuleCat.of k (Total (q := q) B) ⟶ B a.1 :=
  ModuleCat.ofHom (LinearMap.proj ((indexEquiv q i).symm a)) ≫ (coordinateIso B a).hom

def includeCoordinate (B : Away i → ModuleCat.{d} k) (a : Port q i) :
    B a.1 ⟶ ModuleCat.of k (Total (q := q) B) :=
  (coordinateIso B a).inv ≫ ModuleCat.ofHom (LinearMap.single k
    (fun b : Index q i => B (indexEquiv q i b).1) ((indexEquiv q i).symm a))

def totalMap {B C : Away i → ModuleCat.{d} k} (f : ∀ j, B j ⟶ C j) :
    Total (q := q) B →ₗ[k] Total (q := q) C :=
  LinearMap.pi fun a => (f (indexEquiv q i a).1).hom.comp (LinearMap.proj a)

def sumArrows {B : Away i → ModuleCat.{d} k} {M : ModuleCat.{d} k}
    (f : ∀ a : Port q i, B a.1 ⟶ M) : Total (q := q) B →ₗ[k] M :=
  LinearMap.lsum k _ k (fun a => (f (indexEquiv q i a)).hom)

def tupleArrows {B : Away i → ModuleCat.{d} k} {M : ModuleCat.{d} k}
    (f : ∀ a : Port q i, M ⟶ B a.1) : M →ₗ[k] Total (q := q) B :=
  LinearMap.pi fun a => (f (indexEquiv q i a)).hom

end Coordinates

/-- The center and the spaces away from the center, before assembly into one vertex family. -/
structure Spaces (k : Type w) [Field k] (i : Q) where
  center : ModuleCat.{d} k
  away : Away i → ModuleCat.{d} k

namespace Spaces

def vertex (S : Spaces.{u, w, d} k i) (j : Q) : ModuleCat.{d} k := by
  classical
  exact if h : j = i then S.center else S.away ⟨j, h⟩

def centerIso (S : Spaces.{u, w, d} k i) : S.vertex i ≅ S.center :=
  eqToIso (by simp [vertex])

def awayIso (S : Spaces.{u, w, d} k i) (j : Away i) : S.vertex j ≅ S.away j :=
  eqToIso (by simp [vertex, j.property])

abbrev read (V : Rep.{u, v, w, d} k q) (i : Q) : Spaces.{u, w, d} k i :=
  ⟨ReflectionEquivalenceSpec.vertex V i, fun j => ReflectionEquivalenceSpec.vertex V j⟩

end Spaces

/-- Assemble maps on the three possible kinds of non-loop arrow at the chosen vertex. -/
def assemble (S : Spaces.{u, w, d} k i) (loopless : IsEmpty (q.Hom i i))
    (incoming : ∀ j : Away i, q.Hom j i → (S.away j ⟶ S.center))
    (outgoing : ∀ j : Away i, q.Hom i j → (S.center ⟶ S.away j))
    (off : ∀ j l : Away i, q.Hom j l → (S.away j ⟶ S.away l)) : Rep.{u, v, w, d} k q :=
  @QuiverRepresentation.ofArrows k Q _ q S.vertex fun {j l} a => ModuleCat.Hom.hom (by
    by_cases hj : j = i
    · subst j
      by_cases hl : l = i
      · subst l
        exact (loopless.false a).elim
      · exact S.centerIso.hom ≫ outgoing ⟨l, hl⟩ a ≫ (S.awayIso ⟨l, hl⟩).inv
    · by_cases hl : l = i
      · subst l
        exact (S.awayIso ⟨j, hj⟩).hom ≫ incoming ⟨j, hj⟩ a ≫ S.centerIso.inv
      · exact (S.awayIso ⟨j, hj⟩).hom ≫ off ⟨j, hj⟩ ⟨l, hl⟩ a ≫ (S.awayIso ⟨l, hl⟩).inv)

/-- The aggregate map for a sink. -/
def incomingMap [Finite (Port q i)] (V : Rep.{u, v, w, d} k q) :
    Total (q := q) (Spaces.read V i).away →ₗ[k] ReflectionEquivalenceSpec.vertex V i :=
  sumArrows fun a => ModuleCat.ofHom (arrow V a.2)

/-- The aggregate map for the reversed source, using the very same arrow indices. -/
def outgoingMap [Finite (Port q i)] (A : ArrowReversal q r i) (V : Rep.{u, v, w, d} k r) :
    ReflectionEquivalenceSpec.vertex V i →ₗ[k] Total (q := q) (Spaces.read V i).away :=
  tupleArrows fun a => ModuleCat.ofHom (arrow V (A.incident a.1 a.2))

abbrev kernelSpaces [Finite (Port q i)] (V : Rep.{u, v, w, d} k q) : Spaces.{u, w, d} k i :=
  ⟨ModuleCat.of k (LinearMap.ker (incomingMap (i := i) V)), (Spaces.read V i).away⟩

abbrev quotientSpaces [Finite (Port q i)] (A : ArrowReversal q r i)
    (V : Rep.{u, v, w, d} k r) : Spaces.{u, w, d} k i :=
  ⟨ModuleCat.of k (_ ⧸ LinearMap.range (outgoingMap A V)), (Spaces.read V i).away⟩

/-- The sink reflection, before restricting objects to the summand-free subcategory. -/
def reflectSink [Finite (Port q i)] (A : ArrowReversal q r i) (V : Rep.{u, v, w, d} k q) :
    Rep.{u, v, w, d} k r :=
  assemble (kernelSpaces (i := i) V) (A.source i)
    (fun j a => ((A.source j).false a).elim)
    (fun j a => (ModuleCat.ofHom (R := k) (LinearMap.ker (incomingMap (i := i) V)).subtype :
        (kernelSpaces (i := i) V).center ⟶ ModuleCat.of k (Total (q := q) (kernelSpaces (i := i) V).away)) ≫
      coord _ ⟨j, (A.incident j).symm a⟩)
    (fun j l a => ModuleCat.ofHom (arrow V ((A.away j l).symm a)))

/-- The source reflection, using the quotient by the image of the outgoing map. -/
def reflectSource [Finite (Port q i)] (A : ArrowReversal q r i) (V : Rep.{u, v, w, d} k r) :
    Rep.{u, v, w, d} k q :=
  assemble (quotientSpaces A V) (A.sink i)
    (fun j a => includeCoordinate _ ⟨j, a⟩ ≫ ModuleCat.ofHom (LinearMap.range (outgoingMap A V)).mkQ)
    (fun j a => ((A.sink j).false a).elim)
    (fun j l a => ModuleCat.ofHom (arrow V (A.away j l a)))

/-- Finite dimensionality is the pinned vertexwise condition. -/
abbrev finiteRep {q : Quiver.{v} Q} (V : Rep.{u, v, w, d} k q) :=
  @RM03.QuiverModuleEquivalenceSpec.finiteRepresentations k Q _ q V

def NoSimpleSummand {q : Quiver.{v} Q} (i : Q) (V : Rep.{u, v, w, max w d} k q) : Prop := by
  letI := q
  exact ¬ ∃ W : Rep.{u, v, w, max w d} k q,
    Nonempty (V ≅ (@FormsSpec.vertexSimple.{u, v, w, d} k Q _ q i) ⊞ W)

def WithoutSimple (k : Type w) [Field k] (q : Quiver.{v} Q) (i : Q) :
    ObjectProperty (Rep.{u, v, w, max w d} k q) :=
  fun V => finiteRep V ∧ NoSimpleSummand.{u, v, w, d} i V

def SinkObjects (k : Type w) [Field k] (q : Quiver.{v} Q) (i : Q) [Finite (Port q i)] :
    ObjectProperty (Rep.{u, v, w, d} k q) :=
  fun V => finiteRep V ∧ Function.Surjective (incomingMap (i := i) V)

def SourceObjects (k : Type w) [Field k] (A : ArrowReversal q r i) [Finite (Port q i)] :
    ObjectProperty (Rep.{u, v, w, d} k r) :=
  fun V => finiteRep V ∧ Function.Injective (outgoingMap A V)

section Statements

variable [Finite (Port q i)] (A : ArrowReversal q r i)

abbrev SinkSummandCriterion : Prop :=
  IsSink q i → ∀ (V : Rep.{u, v, w, max w d} k q),
    NoSimpleSummand.{u, v, w, d} i V ↔ Function.Surjective (incomingMap (i := i) V)

abbrev SourceSummandCriterion : Prop :=
  ∀ (V : Rep.{u, v, w, max w d} k r),
    NoSimpleSummand.{u, v, w, d} i V ↔ Function.Injective (outgoingMap A V)

/-- The kernel map is the restriction of the direct sum of the component maps. -/
def SinkMapFormula {V W : Rep.{u, v, w, d} k q} (f : V ⟶ W)
    (g : reflectSink A V ⟶ reflectSink A W) : Prop :=
  let S := kernelSpaces (i := i) V
  let T := kernelSpaces (i := i) W
  (∀ j : Away i, (S.awayIso j).inv ≫ component g j ≫ (T.awayIso j).hom = component f j) ∧
  (S.centerIso.inv ≫ component g i ≫ T.centerIso.hom) ≫
      ModuleCat.ofHom (LinearMap.ker (incomingMap (i := i) W)).subtype =
    ModuleCat.ofHom (LinearMap.ker (incomingMap (i := i) V)).subtype ≫
      ModuleCat.ofHom (totalMap (q := q) (fun j => component f j))

/-- The cokernel map is the map induced by the direct sum of the component maps. -/
def SourceMapFormula {V W : Rep.{u, v, w, d} k r} (f : V ⟶ W)
    (g : reflectSource A V ⟶ reflectSource A W) : Prop :=
  let S := quotientSpaces A V
  let T := quotientSpaces A W
  (∀ j : Away i, (S.awayIso j).inv ≫ component g j ≫ (T.awayIso j).hom = component f j) ∧
  ModuleCat.ofHom (LinearMap.range (outgoingMap A V)).mkQ ≫
      (S.centerIso.inv ≫ component g i ≫ T.centerIso.hom) =
    ModuleCat.ofHom (totalMap (q := q) (fun j => component f j)) ≫
      ModuleCat.ofHom (LinearMap.range (outgoingMap A W)).mkQ

abbrev SinkFunctorExists : Prop :=
  ∃ (F : Rep.{u, v, w, d} k q ⥤ Rep.{u, v, w, d} k r)
    (obj : ∀ V, F.obj V = reflectSink A V),
    F.Additive ∧ F.Linear k ∧
      ∀ (V W : Rep.{u, v, w, d} k q) (f : V ⟶ W),
        SinkMapFormula A f (eqToHom (obj V).symm ≫ F.map f ≫ eqToHom (obj W))

abbrev SourceFunctorExists : Prop :=
  ∃ (F : Rep.{u, v, w, d} k r ⥤ Rep.{u, v, w, d} k q)
    (obj : ∀ V, F.obj V = reflectSource A V),
    F.Additive ∧ F.Linear k ∧
      ∀ (V W : Rep.{u, v, w, d} k r) (f : V ⟶ W),
        SourceMapFormula A f (eqToHom (obj V).symm ≫ F.map f ≫ eqToHom (obj W))

abbrev ReflectionEquivalenceExists : Prop :=
  ∃ E : (SinkObjects.{u, v, w, d} k q i).FullSubcategory ≌ (SourceObjects k A).FullSubcategory,
    ∃ (h₁ : ∀ V, (E.functor.obj V).obj = reflectSink A V.obj)
      (h₂ : ∀ V, (E.inverse.obj V).obj = reflectSource A V.obj),
      E.functor.Additive ∧ E.functor.Linear k ∧ E.inverse.Additive ∧ E.inverse.Linear k ∧
      (∀ (V W : (SinkObjects.{u, v, w, d} k q i).FullSubcategory) (f : V ⟶ W),
        SinkMapFormula A f.hom (eqToHom (h₁ V).symm ≫ (E.functor.map f).hom ≫ eqToHom (h₁ W))) ∧
      (∀ (V W : (SourceObjects.{u, v, w, d} k A).FullSubcategory) (f : V ⟶ W),
        SourceMapFormula A f.hom (eqToHom (h₂ V).symm ≫ (E.inverse.map f).hom ≫ eqToHom (h₂ W)))

/-- The equivalence on the full subcategories specified by the absence of a simple summand. -/
abbrev SummandFreeEquivalenceExists : Prop :=
  ∃ E : (WithoutSimple.{u, v, w, d} k q i).FullSubcategory ≌
      (WithoutSimple.{u, v, w, d} k r i).FullSubcategory,
    ∃ (h₁ : ∀ V, (E.functor.obj V).obj = reflectSink A V.obj)
      (h₂ : ∀ V, (E.inverse.obj V).obj = reflectSource A V.obj),
      E.functor.Additive ∧ E.functor.Linear k ∧ E.inverse.Additive ∧ E.inverse.Linear k ∧
      (∀ (V W : (WithoutSimple.{u, v, w, d} k q i).FullSubcategory) (f : V ⟶ W),
        SinkMapFormula A f.hom (eqToHom (h₁ V).symm ≫ (E.functor.map f).hom ≫ eqToHom (h₁ W))) ∧
      (∀ (V W : (WithoutSimple.{u, v, w, d} k r i).FullSubcategory) (f : V ⟶ W),
        SourceMapFormula A f.hom (eqToHom (h₂ V).symm ≫ (E.inverse.map f).hom ≫ eqToHom (h₂ W)))

abbrev SinkFinite : Prop :=
  ∀ V : Rep.{u, v, w, d} k q, finiteRep V → finiteRep (reflectSink A V)

abbrev SourceFinite : Prop :=
  ∀ V : Rep.{u, v, w, d} k r, finiteRep V → finiteRep (reflectSource A V)

abbrev SinkIndecomposables : Prop :=
  ∀ V : (SinkObjects.{u, v, w, d} k q i).FullSubcategory,
    Indecomposable (reflectSink A V.obj) ↔ Indecomposable V.obj

abbrev SourceIndecomposables : Prop :=
  ∀ V : (SourceObjects.{u, v, w, d} k A).FullSubcategory,
    Indecomposable (reflectSource A V.obj) ↔ Indecomposable V.obj

/-- Dimension vectors of reflected objects, in the original vertex coordinates. -/
abbrev SinkDimension [Fintype Q] : Prop :=
  ∀ (V : (SinkObjects.{u, v, w, d} k q i).FullSubcategory),
    ∃ (h : finiteRep (reflectSink A V.obj)),
      @FormsSpec.dimensionVector k Q _ r ⟨reflectSink A V.obj, h⟩ =
        @SimpleReflectionsSpec.simpleReflection Q q _ ℤ _ i
          (@FormsSpec.dimensionVector k Q _ q ⟨V.obj, V.property.1⟩)

abbrev SourceDimension [Fintype Q] : Prop :=
  ∀ (V : (SourceObjects.{u, v, w, d} k A).FullSubcategory),
    ∃ (h : finiteRep (reflectSource A V.obj)),
      @FormsSpec.dimensionVector k Q _ q ⟨reflectSource A V.obj, h⟩ =
        @SimpleReflectionsSpec.simpleReflection Q r _ ℤ _ i
          (@FormsSpec.dimensionVector k Q _ r ⟨V.obj, V.property.1⟩)

abbrev SinkTitsForm [Fintype Q] [Fintype (@RM03.Arrow Q q)] [Fintype (@RM03.Arrow Q r)] : Prop :=
  ¬ @RM03.HasOrientedCycle Q q →
    ∀ V : (SinkObjects.{u, v, w, d} k q i).FullSubcategory,
      ∃ (h : finiteRep (reflectSink A V.obj)),
        @FormsSpec.titsForm Q r _ _ ℤ _
          (@FormsSpec.dimensionVector k Q _ r ⟨reflectSink A V.obj, h⟩) =
        @FormsSpec.titsForm Q q _ _ ℤ _
          (@FormsSpec.dimensionVector k Q _ q ⟨V.obj, V.property.1⟩)

abbrev SourceTitsForm [Fintype Q] [Fintype (@RM03.Arrow Q q)] [Fintype (@RM03.Arrow Q r)] : Prop :=
  ¬ @RM03.HasOrientedCycle Q r →
    ∀ V : (SourceObjects.{u, v, w, d} k A).FullSubcategory,
      ∃ (h : finiteRep (reflectSource A V.obj)),
        @FormsSpec.titsForm Q q _ _ ℤ _
          (@FormsSpec.dimensionVector k Q _ q ⟨reflectSource A V.obj, h⟩) =
        @FormsSpec.titsForm Q r _ _ ℤ _
          (@FormsSpec.dimensionVector k Q _ r ⟨V.obj, V.property.1⟩)

end Statements

/-- These bridges give both canonical orientations under the original finiteness and
acyclicity assumptions. -/
abbrev ReversalFinite : Prop :=
  ∀ {Q : Type u} (q : Quiver.{v} Q) [Finite (@RM03.Arrow Q q)] (i : Q),
    Finite (@RM03.Arrow Q (reverseAt q i))

abbrev ReversalAcyclic : Prop :=
  ∀ {Q : Type u} (q : Quiver.{v} Q) (i : Q),
    IsSink q i ∨ IsSource q i →
    ¬ @RM03.HasOrientedCycle Q q → ¬ @RM03.HasOrientedCycle Q (reverseAt q i)

abbrev SourcePortFinite : Prop :=
  ∀ {Q : Type u} {q r : Quiver.{v} Q} {i : Q},
    ArrowReversal q r i → [Finite (@RM03.Arrow Q r)] → Finite (Port q i)

abbrev NoSimpleSummandType :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q : Quiver.{v} Q},
    Q → Rep.{u, v, w, max w d} k q → Prop

abbrev IsSinkType := ∀ {Q : Type u}, Quiver.{v} Q → Q → Prop

abbrev IsSourceType := ∀ {Q : Type u}, Quiver.{v} Q → Q → Prop

abbrev IsolatedCriterion : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), IsEmpty (Port q i) →
      (∀ V : Rep.{u, v, w, d} k q,
        Function.Surjective (incomingMap (i := i) V) ↔ Subsingleton (vertex V i)) ∧
      (∀ V : Rep.{u, v, w, d} k r,
        Function.Injective (outgoingMap A V) ↔ Subsingleton (vertex V i))

abbrev ReverseAtType := ∀ {Q : Type u}, Quiver.{v} Q → Q → Quiver.{v} Q

abbrev ReversalAtSinkType :=
  ∀ {Q : Type u} (q : Quiver.{v} Q) (i : Q), IsSink q i → ArrowReversal q (reverseAt q i) i

abbrev ReversalAtSourceType :=
  ∀ {Q : Type u} (r : Quiver.{v} Q) (i : Q), IsSource r i → ArrowReversal (reverseAt r i) r i

abbrev IncomingMapType :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (V : Rep.{u, v, w, d} k q), Total (q := q) (Spaces.read V i).away →ₗ[k] vertex V i

abbrev OutgoingMapType :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (_ : ArrowReversal q r i) (V : Rep.{u, v, w, d} k r),
    vertex V i →ₗ[k] Total (q := q) (Spaces.read V i).away

abbrev ReflectSinkType :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)],
    ArrowReversal q r i → Rep.{u, v, w, d} k q → Rep.{u, v, w, d} k r

abbrev ReflectSourceType :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)],
    ArrowReversal q r i → Rep.{u, v, w, d} k r → Rep.{u, v, w, d} k q

abbrev SinkCriterionStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q : Quiver.{v} Q} {i : Q} [Finite (Port q i)],
    SinkSummandCriterion.{u, v, w, d} (k := k) (q := q) (i := i)

abbrev SourceCriterionStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), SourceSummandCriterion.{u, v, w, d} (k := k) A

abbrev SinkFunctorStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), SinkFunctorExists.{u, v, w, d} (k := k) A

abbrev SourceFunctorStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), SourceFunctorExists.{u, v, w, d} (k := k) A

abbrev EquivalenceStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), ReflectionEquivalenceExists.{u, v, w, d} (k := k) A

abbrev SummandFreeEquivalenceStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), SummandFreeEquivalenceExists.{u, v, w, d} (k := k) A

abbrev SinkFiniteStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), SinkFinite.{u, v, w, d} (k := k) A

abbrev SourceFiniteStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), SourceFinite.{u, v, w, d} (k := k) A

abbrev SinkIndecomposableStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), SinkIndecomposables.{u, v, w, d} (k := k) A

abbrev SourceIndecomposableStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)]
    (A : ArrowReversal q r i), SourceIndecomposables.{u, v, w, d} (k := k) A

abbrev SinkDimensionStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)] [Fintype Q]
    (A : ArrowReversal q r i), SinkDimension.{u, v, w, d} (k := k) A

abbrev SourceDimensionStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)] [Fintype Q]
    (A : ArrowReversal q r i), SourceDimension.{u, v, w, d} (k := k) A

abbrev SinkTitsFormStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)] [Fintype Q]
    [Fintype (@RM03.Arrow Q q)] [Fintype (@RM03.Arrow Q r)] (A : ArrowReversal q r i),
    SinkTitsForm.{u, v, w, d} (k := k) A

abbrev SourceTitsFormStatement : Prop :=
  ∀ {Q : Type u} {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)] [Fintype Q]
    [Fintype (@RM03.Arrow Q q)] [Fintype (@RM03.Arrow Q r)] (A : ArrowReversal q r i),
    SourceTitsForm.{u, v, w, d} (k := k) A


-- Compare the exported values in the universe order of the canonical definitions.
def expectedNoSimpleSummand := @NoSimpleSummand.{u, v, w, d}
def expectedIncomingMap := @incomingMap.{u, v, w, d}
def expectedOutgoingMap := @outgoingMap.{u, v, w, d}
def expectedReflectSink := @reflectSink.{u, v, w, d}
def expectedReflectSource := @reflectSource.{u, v, w, d}

end
end RepTheorySurvey.Quiver.ReflectionEquivalenceSpec
