import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.ModularBlocks
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.BrauerHomomorphism
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.CentralTraceIdeals

open scoped MonoidAlgebra

namespace RepTheorySurvey.Modular.DefectGroupsSpec

universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G]

/-- The Sylow subgroup of a centralizer, regarded as a subgroup of the ambient group. -/
abbrev sylowImage {p : ℕ} {x : G}
    (S : Sylow p (Subgroup.centralizer ({x} : Set G))) : Subgroup G :=
  (S : Subgroup _).map (Subgroup.centralizer ({x} : Set G)).subtype

/-- The Brauer projection of the block idempotent at a subgroup. -/
noncomputable def brauerImage (b : BlockIdempotent k G) (P : Subgroup G) :
    BrauerHomomorphismSpec.CentralizerAlgebra k P :=
  BrauerHomomorphismSpec.projection k P
    ⟨b.element, fun g => CentralTraceIdealsSpec.conjugation_center k (g : G) b.val⟩

set_option linter.checkUnivs false in
def brauerImageType :=
  ∀ {k : Type u} [Field k] {G : Type v} [Group G],
    BlockIdempotent k G → (P : Subgroup G) → BrauerHomomorphismSpec.CentralizerAlgebra k P

/-- A defect group is an inclusion-maximal (p)-subgroup with nonzero Brauer image. -/
def isDefectGroup (p : ℕ) (b : BlockIdempotent k G) (D : Subgroup G) : Prop :=
  Maximal (fun P : Subgroup G => IsPGroup p P ∧ brauerImage b P ≠ 0) D

set_option linter.checkUnivs false in
def isDefectGroupType :=
  ∀ {k : Type u} [Field k] {G : Type v} [Group G],
    ℕ → BlockIdempotent k G → Subgroup G → Prop

/-- The support contains an element whose centralizer supplies a defect group.
Its image controls every Brauer projection, and its order dominates the Sylow
orders from the entire support. The block belongs to the trace ideal of this group. -/
def existsSupportSylowType : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP k p] (b : BlockIdempotent k G),
    ∃ (x : G) (S : Sylow p (Subgroup.centralizer ({x} : Set G))),
      b.element.coeff x ≠ 0 ∧
      b.val ∈ CentralTraceIdealsSpec.traceIdeal k (sylowImage S) ∧
      isDefectGroup p b (sylowImage S) ∧
      (∀ (P : Subgroup G), IsPGroup p P →
        (brauerImage b P ≠ 0 ↔ ∃ g : G, P ≤ (sylowImage S).map (MulAut.conj g).toMonoidHom)) ∧
      (∀ (y : G), b.element.coeff y ≠ 0 →
        ∀ T : Sylow p (Subgroup.centralizer ({y} : Set G)), Nat.card T ≤ Nat.card S)

/-- The set of defect groups is a nonempty conjugacy class. -/
def defectGroupsConjugacyType : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP k p] (b : BlockIdempotent k G),
    ∃ D : Subgroup G, isDefectGroup p b D ∧
      ∀ P : Subgroup G, isDefectGroup p b P ↔ ∃ g : G, P = D.map (MulAut.conj g).toMonoidHom

end RepTheorySurvey.Modular.DefectGroupsSpec
