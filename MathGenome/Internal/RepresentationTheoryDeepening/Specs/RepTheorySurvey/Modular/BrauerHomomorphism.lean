import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.RelativeTrace
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace RepTheorySurvey.Modular.BrauerHomomorphismSpec

open RelativeTraceSpec

universe u v

variable (k : Type u) [Field k] {G : Type v} [Group G]

/-- The group algebra of the subgroup of elements centralizing `P`. -/
abbrev CentralizerAlgebra (P : Subgroup G) :=
  MonoidAlgebra k (Subgroup.centralizer (P : Set G))

/-- Restrict coefficients to the centralizer. -/
noncomputable def projection (P : Subgroup G) :
    fixedSubalgebra k P →ₗ[k] CentralizerAlgebra k P where
  toFun a := MonoidAlgebra.comapDomain Subtype.val Subtype.val_injective a.val
  map_add' a b := MonoidAlgebra.comapDomain_add _ _ a.val b.val
  map_smul' r a := by
    apply MonoidAlgebra.coeff_injective
    ext x
    rfl

set_option linter.checkUnivs false in
def projectionType :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] (P : Subgroup G),
    fixedSubalgebra k P →ₗ[k] CentralizerAlgebra k P

def projectionAlgebraHom : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP k p] (P : Subgroup G), IsPGroup p P →
    ∃ f : fixedSubalgebra k P →ₐ[k] CentralizerAlgebra k P,
      f.toLinearMap = projection k P

def projectionSurjective : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] (P : Subgroup G),
    Function.Surjective (projection k P)

def projectionKernel : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP k p] (P : Subgroup G), IsPGroup p P →
    LinearMap.ker (projection k P) =
      ⨆ Q : {Q : Subgroup G // Q < P}, LinearMap.range (relativeTrace k Q.property.le)

def centerLeFixedSubalgebra : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] (P : Subgroup G),
    Subalgebra.center k (MonoidAlgebra k G) ≤ fixedSubalgebra k P

def projectionMapsCenter : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] (P : Subgroup G)
    (a : fixedSubalgebra k P), a.val ∈ Subalgebra.center k (MonoidAlgebra k G) →
    projection k P a ∈ Subalgebra.center k (CentralizerAlgebra k P)

/-- Conjugation, restricted to the centralizers of a subgroup and its conjugate. -/
noncomputable def centralizerConjugation (g : G) (P : Subgroup G) :
    Subgroup.centralizer (P : Set G) ≃*
      Subgroup.centralizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  let e := MulAut.conj g
  refine (e.subgroupMap (Subgroup.centralizer (P : Set G))).trans (MulEquiv.subgroupCongr ?_)
  ext z
  constructor
  · exact fun hz => Subgroup.map_centralizer_le_centralizer_image (P : Set G) e.toMonoidHom hz
  · intro hz
    refine ⟨e.symm z, Subgroup.mem_centralizer_iff.mpr (fun x hx => e.injective ?_),
      e.apply_symm_apply z⟩
    simpa only [map_mul, e.apply_symm_apply] using
      (Subgroup.mem_centralizer_iff.mp hz) (e x) ⟨x, hx, rfl⟩

def projectionConjugation : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] (g : G) (P : Subgroup G)
    (a : fixedSubalgebra k P),
    ∃ b : fixedSubalgebra k (P.map (MulAut.conj g).toMonoidHom),
      b.val = conjugation k g a.val ∧
      projection k _ b =
        MonoidAlgebra.domCongr k k (centralizerConjugation g P) (projection k P a)

end RepTheorySurvey.Modular.BrauerHomomorphismSpec
