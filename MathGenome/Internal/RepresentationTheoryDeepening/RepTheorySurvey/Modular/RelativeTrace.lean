import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.RelativeTrace
import Mathlib.Data.Fintype.BigOperators

namespace RepTheorySurvey.Modular.RelativeTrace

universe u v

variable (k : Type u) [Field k] {G : Type v} [Group G]

/-- The action on the group algebra obtained by conjugating the basis. -/
noncomputable def conjugation : G →* (MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G) :=
  RelativeTraceSpec.conjugation k

@[simp]
theorem conjugation_single (g x : G) (r : k) :
    conjugation k g (MonoidAlgebra.single x r) =
      MonoidAlgebra.single (g * x * g⁻¹) r :=
  MonoidAlgebra.domCongr_single (R := k) (A := k) (MulAut.conj g) x r

/-- The subalgebra fixed under conjugation by `P`. -/
def fixedSubalgebra (P : Subgroup G) : Subalgebra k (MonoidAlgebra k G) :=
  RelativeTraceSpec.fixedSubalgebra k P

@[simp]
theorem mem_fixedSubalgebra_iff (P : Subgroup G) (a : MonoidAlgebra k G) :
    a ∈ fixedSubalgebra k P ↔ ∀ g : P, conjugation k (g : G) a = a :=
  Iff.rfl

/-- Left cosets of `Q` inside `P`. -/
abbrev LeftCosets (Q P : Subgroup G) := RelativeTraceSpec.LeftCosets Q P

/-- The conjugate attached to a left coset, evaluated on an invariant element. -/
noncomputable def cosetConjugate {Q P : Subgroup G} (a : fixedSubalgebra k Q)
    (c : LeftCosets Q P) : MonoidAlgebra k G :=
  RelativeTraceSpec.cosetConjugate k a c

theorem cosetConjugate_eq_of_mk_eq {Q P : Subgroup G} (a : fixedSubalgebra k Q)
    (c : LeftCosets Q P) (g : P) (hg : QuotientGroup.mk g = c) :
    cosetConjugate k a c = conjugation k (g : G) a :=
  RelativeTraceSpec.cosetConjugate_eq_of_mk_eq k a c g hg

@[simp]
theorem cosetConjugate_mk {Q P : Subgroup G} (a : fixedSubalgebra k Q) (g : P) :
    cosetConjugate k a (QuotientGroup.mk g : LeftCosets Q P) = conjugation k (g : G) a :=
  cosetConjugate_eq_of_mk_eq k a _ _ rfl

theorem conjugation_eq_of_coset_eq {Q P : Subgroup G} (a : fixedSubalgebra k Q)
    {g h : P} (heq : (QuotientGroup.mk g : LeftCosets Q P) = QuotientGroup.mk h) :
    conjugation k (g : G) a = conjugation k (h : G) a := by
  rw [← cosetConjugate_mk k a (P := P) g, ← cosetConjugate_mk k a (P := P) h, heq]

/-- Reinterpret the cosets in the copy of `Q` inside `P` as cosets in `Q`. -/
private def restrictedCosetEquiv {R Q P : Subgroup G} (hQP : Q ≤ P) :
    Q.subgroupOf P ⧸ (R.subgroupOf P).subgroupOf (Q.subgroupOf P) ≃ LeftCosets R Q :=
  Quotient.congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv (fun _ _ => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    rfl)

private noncomputable def cosetsEquivProd {R Q P : Subgroup G} (hRQ : R ≤ Q) (hQP : Q ≤ P) :
    LeftCosets R P ≃ LeftCosets Q P × LeftCosets R Q :=
  (Subgroup.quotientEquivProdOfLE (Subgroup.subgroupOf_mono P hRQ)).trans
    (Equiv.prodCongr (Equiv.refl _) (restrictedCosetEquiv hQP))

private theorem cosetsEquivProd_symm_apply {R Q P : Subgroup G} (hRQ : R ≤ Q) (hQP : Q ≤ P)
    (c : LeftCosets Q P) (d : LeftCosets R Q) :
    (cosetsEquivProd hRQ hQP).symm (c, d) =
      QuotientGroup.mk (c.out * Subgroup.inclusion hQP d.out) := by
  calc
    (cosetsEquivProd hRQ hQP).symm (c, d) =
        (cosetsEquivProd hRQ hQP).symm (c, QuotientGroup.mk d.out) :=
      congrArg (fun q => (cosetsEquivProd hRQ hQP).symm (c, q))
        (QuotientGroup.out_eq' d).symm
    _ = _ := rfl

variable [Finite G]

noncomputable local instance (Q P : Subgroup G) : Fintype (LeftCosets Q P) :=
  Fintype.ofFinite _

/-- The relative trace from `Q`-invariants to `P`-invariants. -/
noncomputable def relativeTrace {Q P : Subgroup G} (hQP : Q ≤ P) :
    fixedSubalgebra k Q →ₗ[k] fixedSubalgebra k P :=
  RelativeTraceSpec.relativeTrace k hQP

theorem relativeTrace_apply {Q P : Subgroup G} (hQP : Q ≤ P) (a : fixedSubalgebra k Q) :
    (relativeTrace k hQP a : MonoidAlgebra k G) = ∑ c : LeftCosets Q P, cosetConjugate k a c :=
  RelativeTraceSpec.relativeTrace_apply k hQP a

/-- The quotient sum can be computed with any section of the coset projection. -/
theorem relativeTrace_eq_sum {Q P : Subgroup G} (hQP : Q ≤ P) (a : fixedSubalgebra k Q)
    (rep : LeftCosets Q P → P) (hrep : ∀ c, QuotientGroup.mk (rep c) = c) :
    (relativeTrace k hQP a : MonoidAlgebra k G) =
      ∑ c : LeftCosets Q P, conjugation k (rep c : G) a := by
  rw [relativeTrace_apply]
  exact Finset.sum_congr rfl fun c _ => cosetConjugate_eq_of_mk_eq k a c (rep c) (hrep c)

theorem sum_cosetConjugate_invariant {Q P : Subgroup G} (hQP : Q ≤ P)
    (a : fixedSubalgebra k Q) (g : P) :
    conjugation k (g : G) (∑ c : LeftCosets Q P, cosetConjugate k a c) =
      ∑ c : LeftCosets Q P, cosetConjugate k a c := by
  rw [← relativeTrace_apply k hQP a]
  exact (relativeTrace k hQP a).property g

/-- Relative traces compose along a chain of subgroups. -/
theorem relativeTrace_trans {R Q P : Subgroup G} (hRQ : R ≤ Q) (hQP : Q ≤ P) :
    relativeTrace k (hRQ.trans hQP) =
      (relativeTrace k hQP).comp (relativeTrace k hRQ) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change (relativeTrace k (hRQ.trans hQP) a : MonoidAlgebra k G) =
    (relativeTrace k hQP (relativeTrace k hRQ a) : MonoidAlgebra k G)
  rw [relativeTrace_apply, relativeTrace_apply]
  let e := cosetsEquivProd hRQ hQP
  calc
    (∑ c : LeftCosets R P, cosetConjugate k a c) =
        ∑ cd : LeftCosets Q P × LeftCosets R Q, cosetConjugate k a (e.symm cd) :=
      (e.symm.sum_comp (cosetConjugate k a)).symm
    _ = ∑ c : LeftCosets Q P, ∑ d : LeftCosets R Q, cosetConjugate k a (e.symm (c, d)) :=
      Fintype.sum_prod_type _
    _ = ∑ c : LeftCosets Q P, cosetConjugate k (relativeTrace k hRQ a) c := by
      apply Finset.sum_congr rfl
      intro c _
      change _ = conjugation k (c.out : G) (relativeTrace k hRQ a : MonoidAlgebra k G)
      rw [relativeTrace_apply, map_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [show e.symm (c, d) = _ from cosetsEquivProd_symm_apply hRQ hQP c d,
        cosetConjugate_mk]
      exact RelativeTraceSpec.conjugation_mul_apply k (c.out : G) (d.out : G) a

end RepTheorySurvey.Modular.RelativeTrace
