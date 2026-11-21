import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SubgroupCoverConstruction
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.Monodromy

/-! Independent statements for paper.tex, Theorem 1.9, lines 373–433.
The covering and fundamental group are the canonical upstream objects. The
unpointed quotient below forgets the distinguished point: its relation only
asks for a homeomorphism over the base. All connected coverings have a point
over the fixed basepoint by surjectivity, so these are also representatives
of the ordinary unpointed isomorphism classes. -/
namespace P202Specs.Topology
universe u v w
noncomputable section

variable {E : Type u} {D : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace D] [TopologicalSpace B]

/-- A pointed isomorphism over B, with its actual homeomorphism. -/
def PointedCoverIsomorphic {e : E} {d : D} {b : B}
    (p : PointedMap E B e b) (q : PointedMap D B d b) : Prop :=
  ∃ F : E ≃ₜ D, F e = d ∧ ∀ x, q.map (F x) = p.map x

/-- A homeomorphism over B, without a condition on distinguished points. -/
def CoverIsomorphic (p : C(E, B)) (q : C(D, B)) : Prop :=
  ∃ F : E ≃ₜ D, ∀ x, q (F x) = p x

/-- `g⁻¹ H g`, expressed by its membership test `g a g⁻¹ ∈ H`. -/
def conjugateSubgroup {G : Type*} [Group G] (H : Subgroup G) (g : G) : Subgroup G :=
  H.comap (MulAut.conj g).toMonoidHom

def SubgroupsConjugate {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  ∃ g, K = conjugateSubgroup H g

/-- Bundled representatives in one universe, with the given total-space topology.
The canonicalRepresentative theorem below puts every cover, even one whose
total space lives in another universe, into this collection up to pointed
homeomorphism. -/
structure ConnectedPointedCover (B : Type u) [TopologicalSpace B] (b : B) where
  total : Type u
  topology : TopologicalSpace total
  connected : @ConnectedSpace total topology
  point : total
  projection : @PointedMap total B topology _ point b
  covering : @Covering total B topology _ projection.map

attribute [instance] ConnectedPointedCover.topology ConnectedPointedCover.connected

namespace ConnectedPointedCover
variable {B : Type u} [TopologicalSpace B] {b : B}

def imageSubgroup (C : ConnectedPointedCover B b) : Subgroup (Pi1 B b) :=
  C.projection.induced.range

def pointedSetoid (B : Type u) [TopologicalSpace B] (b : B) :
    Setoid (ConnectedPointedCover B b) where
  r C D := PointedCoverIsomorphic C.projection D.projection
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro C
      exact ⟨Homeomorph.refl _, rfl, fun _ => rfl⟩
    · rintro C D ⟨F, hpoint, hover⟩
      refine ⟨F.symm, ?_, fun y => ?_⟩
      · rw [← hpoint, F.symm_apply_apply]
      · exact (hover (F.symm y)).symm.trans (congrArg D.projection.map (F.apply_symm_apply y))
    · rintro C D A ⟨F, hF, hpF⟩ ⟨K, hK, hpK⟩
      exact ⟨F.trans K, (congrArg K hF).trans hK,
        fun x => (hpK (F x)).trans (hpF x)⟩

def unpointedSetoid (B : Type u) [TopologicalSpace B] (b : B) :
    Setoid (ConnectedPointedCover B b) where
  r C D := CoverIsomorphic C.projection.map D.projection.map
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro C
      exact ⟨Homeomorph.refl _, fun _ => rfl⟩
    · rintro C D ⟨F, hover⟩
      exact ⟨F.symm, fun y => (hover (F.symm y)).symm.trans
        (congrArg D.projection.map (F.apply_symm_apply y))⟩
    · rintro C D A ⟨F, hpF⟩ ⟨K, hpK⟩
      exact ⟨F.trans K, fun x => (hpK (F x)).trans (hpF x)⟩

abbrev PointedClasses (B : Type u) [TopologicalSpace B] (b : B) :=
  Quotient (pointedSetoid B b)
abbrev UnpointedClasses (B : Type u) [TopologicalSpace B] (b : B) :=
  Quotient (unpointedSetoid B b)

def forgetPoint : PointedClasses B b → UnpointedClasses B b :=
  Quotient.map id (fun _ _ ⟨F, _, hF⟩ => ⟨F, hF⟩)
end ConnectedPointedCover

/-- The usual conjugacy relation on subgroups, independently of coverings. -/
def subgroupConjugacySetoid (G : Type*) [Group G] : Setoid (Subgroup G) where
  r := SubgroupsConjugate
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro H
      exact ⟨1, by ext x; simp [conjugateSubgroup]⟩
    · rintro H K ⟨g, rfl⟩
      refine ⟨g⁻¹, ?_⟩
      ext x
      simp [conjugateSubgroup, MulAut.conj_apply, mul_assoc]
    · rintro H K L ⟨g, rfl⟩ ⟨h, rfl⟩
      refine ⟨g * h, ?_⟩
      ext x
      simp [conjugateSubgroup, MulAut.conj_apply, mul_assoc]

abbrev SubgroupConjugacyClasses (G : Type*) [Group G] :=
  Quotient (subgroupConjugacySetoid G)

namespace ClassificationExpected

def connectedCoverLocallyPathConnected : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [LocallyPathConnectedSpace B] (p : E → B), Covering p → LocallyPathConnectedSpace E

def connectedCoverPathConnected : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] [LocallyPathConnectedSpace B] (p : E → B),
    Covering p → PathConnectedSpace E

/-- The pairwise criterion is valid even without semilocal simple connectivity. -/
def pointedIsomorphismCriterion : Prop :=
  ∀ (E : Type u) (D : Type v) (B : Type w)
    [TopologicalSpace E] [TopologicalSpace D] [TopologicalSpace B]
    [ConnectedSpace E] [ConnectedSpace D] [LocallyPathConnectedSpace B]
    (e : E) (d : D) (b : B) (p : PointedMap E B e b) (q : PointedMap D B d b),
    Covering p.map → Covering q.map →
      (p.induced.range = q.induced.range ↔ PointedCoverIsomorphic p q)

def pointChangeConjugacy : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)), Covering p → ∀ b (e : Fiber p b) (g : Pi1 B b),
      fiberSubgroup p b (fiberAction p b e g) = conjugateSubgroup (fiberSubgroup p b e) g

def unpointedIsomorphismCriterion : Prop :=
  ∀ (E : Type u) (D : Type v) (B : Type w)
    [TopologicalSpace E] [TopologicalSpace D] [TopologicalSpace B]
    [ConnectedSpace E] [ConnectedSpace D] [PathConnectedSpace B] [LocallyPathConnectedSpace B]
    (e : E) (d : D) (b : B) (p : PointedMap E B e b) (q : PointedMap D B d b),
    Covering p.map → Covering q.map →
      (CoverIsomorphic p.map q.map ↔ SubgroupsConjugate p.induced.range q.induced.range)

/-- Every connected pointed cover, in any universe, is isomorphic to the
canonical representative in the base's universe. Thus the universe of the
bundled representatives does not restrict the isomorphism classes classified. -/
def canonicalRepresentative : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] [PathConnectedSpace B] [LocallyPathConnectedSpace B],
    SemilocallySimplyConnected B → ∀ (e : E) (b : B) (p : PointedMap E B e b),
    Covering p.map →
    ∃ F : E ≃ₜ SubgroupCover b p.induced.range,
      F e = SubgroupCover.basepoint p.induced.range ∧
      ∀ x, SubgroupCover.endpoint p.induced.range (F x) = p.map x

/-- An actual bijection of pointed homeomorphism classes, with the image formula. -/
def pointedClassification : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B], SemilocallySimplyConnected B → ∀ b : B,
    ∃ F : ConnectedPointedCover.PointedClasses B b ≃ Subgroup (Pi1 B b),
      ∀ C : ConnectedPointedCover B b, F (Quotient.mk _ C) = C.imageSubgroup

/-- The unpointed bijection, explicitly compatible with forgetting the point. -/
def unpointedClassification : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B], SemilocallySimplyConnected B → ∀ b : B,
    ∃ F : ConnectedPointedCover.UnpointedClasses B b ≃ SubgroupConjugacyClasses (Pi1 B b),
      ∀ C : ConnectedPointedCover B b,
        F (ConnectedPointedCover.forgetPoint (Quotient.mk _ C)) =
          Quotient.mk _ C.imageSubgroup

/-- The trivial-subgroup representative retains simple connectivity and the
unique pointed map to each connected pointed covering, in any universe. -/
def universalCover : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B], SemilocallySimplyConnected B → ∀ b : B,
    Covering (SubgroupCover.endpoint (⊥ : Subgroup (Pi1 B b))) ∧
    SimplyConnectedSpace (SubgroupCover b (⊥ : Subgroup (Pi1 B b))) ∧
    ∀ (E : Type v) [TopologicalSpace E] [ConnectedSpace E] (e : E)
      (p : PointedMap E B e b), Covering p.map →
      ∃! L : C(SubgroupCover b (⊥ : Subgroup (Pi1 B b)), E),
        (∀ x, p.map (L x) = SubgroupCover.endpoint ⊥ x) ∧
        L (SubgroupCover.basepoint ⊥) = e

end ClassificationExpected
end
end P202Specs.Topology
