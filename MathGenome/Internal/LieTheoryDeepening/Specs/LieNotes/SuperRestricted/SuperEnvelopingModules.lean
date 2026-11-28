import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperEnveloping

namespace LieNotes.SuperRestricted.SuperEnvelopingModules.Definitions

open SuperEnveloping.Construction (Enveloping ι piece)

universe u v w z

variable {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)] [AddCommGroup V] [Module k V]

/-- A unital action of the enveloping algebra compatible with the fixed parity grading. -/
structure EnvelopingModule (L : LieSuperalgebra k V)
    {M : Type w} [AddCommGroup M] [Module k M] (G : Grading k M) where
  act : Enveloping L →ₐ[k] Module.End k M
  act_mem : ∀ ⦃i j : ZMod 2⦄ ⦃a : Enveloping L⦄ ⦃m : M⦄,
    a ∈ piece L i → m ∈ G.piece j → act a m ∈ G.piece (i + j)

/-- A parity-preserving linear intertwiner between unital enveloping actions. -/
structure EnvelopingModule.Hom {L : LieSuperalgebra k V}
    {M : Type w} [AddCommGroup M] [Module k M] {G : Grading k M}
    {N : Type z} [AddCommGroup N] [Module k N] {H : Grading k N}
    (A : EnvelopingModule L G) (B : EnvelopingModule L H) where
  toLinearMap : M →ₗ[k] N
  map_piece : ∀ ⦃i⦄ ⦃m : M⦄, m ∈ G.piece i → toLinearMap m ∈ H.piece i
  intertwines : ∀ (a : Enveloping L) (m : M), toLinearMap (A.act a m) = B.act a (toLinearMap m)

end LieNotes.SuperRestricted.SuperEnvelopingModules.Definitions

namespace Specs.LieNotes.SuperRestricted.SuperEnvelopingModules

open _root_.LieNotes.SuperRestricted
open _root_.LieNotes.SuperRestricted.SuperEnveloping.Construction (Enveloping ι)
open _root_.LieNotes.SuperRestricted.SuperEnvelopingModules.Definitions (EnvelopingModule)

universe u v w z

set_option linter.checkUnivs false in
def envelopingModuleType :=
  ∀ {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)] [AddCommGroup V] [Module k V]
    (_ : LieSuperalgebra k V) {M : Type w} [AddCommGroup M] [Module k M] (_ : Grading k M),
    Type (max u v w)

def envelopingModuleValue := @EnvelopingModule

set_option linter.checkUnivs false in
def envelopingModuleHomType :=
  ∀ {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)] [AddCommGroup V] [Module k V]
    {L : LieSuperalgebra k V} {M : Type w} [AddCommGroup M] [Module k M] {G : Grading k M}
    {N : Type z} [AddCommGroup N] [Module k N] {H : Grading k N}
    (_ : EnvelopingModule L G) (_ : EnvelopingModule L H), Type (max w z)

def envelopingModuleHomValue := @EnvelopingModule.Hom

/-- An intertwining equation on all generators is equivalent to the equation on the quotient. -/
def intertwinesIffOnGeneratorsType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)] [AddCommGroup V] [Module k V]
    {L : LieSuperalgebra k V} {M : Type w} [AddCommGroup M] [Module k M] {G : Grading k M}
    {N : Type z} [AddCommGroup N] [Module k N] {H : Grading k N}
    (A : EnvelopingModule L G) (B : EnvelopingModule L H) (f : M →ₗ[k] N),
    (∀ (a : Enveloping L) (m : M), f (A.act a m) = B.act a (f m)) ↔
      (∀ (x : V) (m : M), f (A.act (ι L x) m) = B.act (ι L x) (f m))

/-- Extension and restriction are inverse, with the same underlying graded spaces and maps. -/
def gradedModulesAgreeType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)] [AddCommGroup V] [Module k V]
    (L : LieSuperalgebra k V) {M : Type w} [AddCommGroup M] [Module k M] (G : Grading k M)
    {N : Type z} [AddCommGroup N] [Module k N] (H : Grading k N),
    ∃ (eG : GradedModule L G ≃ EnvelopingModule L G)
      (eH : GradedModule L H ≃ EnvelopingModule L H),
      (∀ A x, (eG A).act (ι L x) = A.act x) ∧
      (∀ B x, (eH B).act (ι L x) = B.act x) ∧
      (∀ A x, (eG.symm A).act x = A.act (ι L x)) ∧
      (∀ B x, (eH.symm B).act x = B.act (ι L x)) ∧
      ∀ (A : GradedModule L G) (B : GradedModule L H),
        ∃ e : GradedModule.Hom A B ≃ EnvelopingModule.Hom (eG A) (eH B),
          ∀ f, (e f).toLinearMap = f.toLinearMap

end Specs.LieNotes.SuperRestricted.SuperEnvelopingModules
