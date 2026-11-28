import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient

namespace RepTheorySurvey.Modular.RelativeTraceSpec

universe u v

variable (k : Type u) [Field k] {G : Type v} [Group G]

/-- Conjugation on the group algebra, induced by conjugation on the basis group. -/
noncomputable def conjugation : G →* (MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G) :=
  (MonoidAlgebra.domCongrAut (R := k) (A := k)).comp MulAut.conj

theorem conjugation_mul_apply (g h : G) (a : MonoidAlgebra k G) :
    conjugation k (g * h) a = conjugation k g (conjugation k h a) := by
  rw [map_mul]
  rfl

/-- The subalgebra of elements fixed under conjugation by every element of `P`. -/
def fixedSubalgebra (P : Subgroup G) : Subalgebra k (MonoidAlgebra k G) where
  carrier := {a | ∀ g : P, conjugation k (g : G) a = a}
  zero_mem' _ := map_zero _
  one_mem' _ := map_one _
  add_mem' ha hb g := by simp only [map_add, ha g, hb g]
  mul_mem' ha hb g := by simp only [map_mul, ha g, hb g]
  algebraMap_mem' r g := (conjugation k (g : G)).commutes r

/-- Left cosets of the restriction of `Q` to `P`. -/
abbrev LeftCosets (Q P : Subgroup G) := P ⧸ Q.subgroupOf P

/-- The conjugate in a trace summand, evaluated using a representative of its left coset. -/
noncomputable def cosetConjugate {Q P : Subgroup G} (a : fixedSubalgebra k Q)
    (c : LeftCosets Q P) : MonoidAlgebra k G :=
  conjugation k (c.out : G) a

private theorem conjugation_eq_of_coset_eq {Q P : Subgroup G} (a : fixedSubalgebra k Q)
    {g h : P} (heq : (QuotientGroup.mk g : LeftCosets Q P) = QuotientGroup.mk h) :
    conjugation k (g : G) a = conjugation k (h : G) a := by
  have hmem : (g : G)⁻¹ * (h : G) ∈ Q :=
    QuotientGroup.eq (s := Q.subgroupOf P) |>.mp heq
  have hfix : conjugation k ((g : G)⁻¹ * (h : G)) a = a :=
    a.property ⟨_, hmem⟩
  calc
    conjugation k (g : G) a =
        conjugation k (g : G) (conjugation k ((g : G)⁻¹ * (h : G)) a) := by rw [hfix]
    _ = conjugation k (h : G) a := by
      rw [← conjugation_mul_apply, mul_inv_cancel_left]

theorem cosetConjugate_eq_of_mk_eq {Q P : Subgroup G} (a : fixedSubalgebra k Q)
    (c : LeftCosets Q P) (g : P) (hg : QuotientGroup.mk g = c) :
    cosetConjugate k a c = conjugation k (g : G) a :=
  conjugation_eq_of_coset_eq k a ((QuotientGroup.out_eq' c).trans hg.symm)

private theorem conjugation_cosetConjugate {Q P : Subgroup G} (a : fixedSubalgebra k Q)
    (g : P) (c : LeftCosets Q P) :
    conjugation k (g : G) (cosetConjugate k a c) = cosetConjugate k a (g • c) := by
  have hg : (QuotientGroup.mk (g * c.out) : LeftCosets Q P) = g • c := by
    rw [← smul_eq_mul, MulAction.Quotient.mk_smul_out]
  rw [cosetConjugate_eq_of_mk_eq k a _ _ hg]
  exact (conjugation_mul_apply k (g : G) (c.out : G) a).symm

variable [Finite G]

noncomputable local instance (Q P : Subgroup G) : Fintype (LeftCosets Q P) :=
  Fintype.ofFinite _

private noncomputable def traceToAlgebra (Q P : Subgroup G) :
    fixedSubalgebra k Q →ₗ[k] MonoidAlgebra k G :=
  ∑ c : LeftCosets Q P, (conjugation k (c.out : G)).toLinearMap.comp
    (fixedSubalgebra k Q).val.toLinearMap

private theorem traceToAlgebra_apply {Q P : Subgroup G} (a : fixedSubalgebra k Q) :
    traceToAlgebra k Q P a = ∑ c : LeftCosets Q P, cosetConjugate k a c := by
  simp only [traceToAlgebra, LinearMap.sum_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Subalgebra.val_apply, AlgEquiv.toLinearMap_apply, cosetConjugate]

private theorem traceToAlgebra_mem {Q P : Subgroup G} (a : fixedSubalgebra k Q) :
    traceToAlgebra k Q P a ∈ fixedSubalgebra k P := by
  intro g
  rw [traceToAlgebra_apply, map_sum]
  simp_rw [conjugation_cosetConjugate]
  exact Equiv.sum_comp (MulAction.toPerm g) (cosetConjugate k a)

/-- The sum over the left cosets of `Q` in `P`, with codomain restricted to `P`-invariants. -/
noncomputable def relativeTrace {Q P : Subgroup G} (_hQP : Q ≤ P) :
    fixedSubalgebra k Q →ₗ[k] fixedSubalgebra k P :=
  (traceToAlgebra k Q P).codRestrict (fixedSubalgebra k P).toSubmodule (traceToAlgebra_mem k)

theorem relativeTrace_apply {Q P : Subgroup G} (hQP : Q ≤ P) (a : fixedSubalgebra k Q) :
    (relativeTrace k hQP a : MonoidAlgebra k G) = ∑ c : LeftCosets Q P, cosetConjugate k a c :=
  traceToAlgebra_apply k a

section DefinitionTypes

-- These definitions return types which retain both independent universe parameters.
set_option linter.checkUnivs false

def conjugationType :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G],
    G →* (MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G)

def fixedSubalgebraType :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G], Subgroup G →
    Subalgebra k (MonoidAlgebra k G)

def LeftCosetsType :=
  ∀ {G : Type v} [Group G], Subgroup G → Subgroup G → Type v

def cosetConjugateType :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] {Q P : Subgroup G},
    fixedSubalgebra k Q → LeftCosets Q P → MonoidAlgebra k G

def relativeTraceType :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G] {Q P : Subgroup G},
    Q ≤ P → fixedSubalgebra k Q →ₗ[k] fixedSubalgebra k P

end DefinitionTypes

def conjugationSingle : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] (g x : G) (r : k),
    conjugation k g (MonoidAlgebra.single x r) =
      MonoidAlgebra.single (g * x * g⁻¹) r

def memFixedSubalgebraIff : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] (P : Subgroup G) (a : MonoidAlgebra k G),
    a ∈ fixedSubalgebra k P ↔ ∀ g : P, conjugation k (g : G) a = a

def cosetConjugateEqOfMkEq : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] {Q P : Subgroup G}
    (a : fixedSubalgebra k Q) (c : LeftCosets Q P) (g : P),
    QuotientGroup.mk g = c → cosetConjugate k a c = conjugation k (g : G) a

def conjugationEqOfCosetEq : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] {Q P : Subgroup G}
    (a : fixedSubalgebra k Q) {g h : P},
    (QuotientGroup.mk g : LeftCosets Q P) = QuotientGroup.mk h →
    conjugation k (g : G) a = conjugation k (h : G) a

def relativeTraceApply : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G] {Q P : Subgroup G}
    (hQP : Q ≤ P) (a : fixedSubalgebra k Q),
    (relativeTrace k hQP a : MonoidAlgebra k G) = ∑ c : LeftCosets Q P, cosetConjugate k a c

def relativeTraceEqSum : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G] {Q P : Subgroup G}
    (hQP : Q ≤ P) (a : fixedSubalgebra k Q) (rep : LeftCosets Q P → P),
    (∀ c, QuotientGroup.mk (rep c) = c) →
    (relativeTrace k hQP a : MonoidAlgebra k G) =
      ∑ c : LeftCosets Q P, conjugation k (rep c : G) a

def sumCosetConjugateInvariant : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G] {Q P : Subgroup G}
    (_hQP : Q ≤ P) (a : fixedSubalgebra k Q) (g : P),
    conjugation k (g : G) (∑ c : LeftCosets Q P, cosetConjugate k a c) =
      ∑ c : LeftCosets Q P, cosetConjugate k a c

def relativeTraceTrans : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G] {R Q P : Subgroup G}
    (hRQ : R ≤ Q) (hQP : Q ≤ P),
    relativeTrace k (hRQ.trans hQP) =
      (relativeTrace k hQP).comp (relativeTrace k hRQ)

end RepTheorySurvey.Modular.RelativeTraceSpec
