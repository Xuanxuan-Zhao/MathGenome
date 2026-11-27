import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.RingTheory.Norm.Transitivity

namespace GaloisFormalization.GH.CyclicDegreeTwo

open scoped BigOperators
open GaloisFormalization.GH.Model

universe u v

noncomputable section

section Cyclic

variable {C : Type u} [Group C] [Finite C]
variable {A : Type v} [AddCommGroup A] [DistribMulAction C A]

/-- Enumerate a finite cyclic group by the powers of its specified generator. -/
def powerEquiv (s : C) (hs : Subgroup.zpowers s = ⊤) : Fin (orderOf s) ≃ C :=
  Equiv.ofBijective (fun i => s ^ (i : ℕ)) (by
    classical
    constructor
    · intro i j h
      exact Fin.ext (pow_injOn_Iio_orderOf i.isLt j.isLt h)
    · intro g
      have hg : g ∈ Subgroup.zpowers s := hs ▸ Subgroup.mem_top g
      obtain ⟨i, hi, h⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hg)
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, h⟩)

@[simp]
theorem powerEquiv_apply (s : C) (hs : Subgroup.zpowers s = ⊤) (i : Fin (orderOf s)) :
    powerEquiv s hs i = s ^ (i : ℕ) := rfl

/-- The invariant subgroup of the given module. -/
abbrev Invariants (C : Type u) (A : Type v) [Group C] [AddCommGroup A]
    [DistribMulAction C A] := fixedCoefficients C A ⊤

/-- The cyclic norm, defined by the sum over the powers of the generator. -/
def norm (s : C) (hs : Subgroup.zpowers s = ⊤) : A →ₗ[ℤ] Invariants C A :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun a => ⟨∑ i : Fin (orderOf s), s ^ (i : ℕ) • a, by
        classical
        let := Fintype.ofFinite C
        have reindex :
            (∑ i : Fin (orderOf s), s ^ (i : ℕ) • a) = ∑ g : C, g • a :=
          Fintype.sum_equiv (powerEquiv s hs) _ _ (fun _ => rfl)
        rw [reindex, mem_fixedCoefficients]
        intro g _
        rw [Finset.smul_sum]
        simp only [smul_smul]
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)⟩
      map_zero' := by
        apply Subtype.ext
        change (∑ i : Fin (orderOf s), s ^ (i : ℕ) • (0 : A)) = 0
        simp
      map_add' := by
        intro a b
        apply Subtype.ext
        change (∑ i : Fin (orderOf s), s ^ (i : ℕ) • (a + b)) =
          (∑ i : Fin (orderOf s), s ^ (i : ℕ) • a) +
            (∑ i : Fin (orderOf s), s ^ (i : ℕ) • b)
        simp only [smul_add, Finset.sum_add_distrib] }

@[simp]
theorem norm_val (s : C) (hs : Subgroup.zpowers s = ⊤) (a : A) :
    (norm s hs a : A) = ∑ i : Fin (orderOf s), s ^ (i : ℕ) • a := rfl

/-- The invariant coefficients modulo the image of the cyclic norm. -/
abbrev NormQuotient (s : C) (hs : Subgroup.zpowers s = ⊤) (A : Type v)
    [AddCommGroup A] [DistribMulAction C A] :=
  Invariants C A ⧸ LinearMap.range (norm (A := A) s hs)

variable [TopologicalSpace C] [DiscreteTopology C]
variable [TopologicalSpace A] [DiscreteTopology A]

/-- The degree-two cochain which records the carry when adding the two exponent representatives. -/
def carryCochain (s : C) (hs : Subgroup.zpowers s = ⊤) (a : Invariants C A) :
    continuousCochains C A 2 :=
  cochainTwo (fun p => if ((powerEquiv s hs).symm p.1 : ℕ) +
      ((powerEquiv s hs).symm p.2 : ℕ) < orderOf s then 0 else a.val)
    continuous_of_discreteTopology

theorem carryCochain_apply_pow (s : C) (hs : Subgroup.zpowers s = ⊤)
    (a : Invariants C A) (i j : Fin (orderOf s)) :
    (carryCochain s hs a).val ![s ^ (i : ℕ), s ^ (j : ℕ)] =
      if (i : ℕ) + (j : ℕ) < orderOf s then 0 else a.val := by
  change (if ((powerEquiv s hs).symm (s ^ (i : ℕ)) : ℕ) +
      ((powerEquiv s hs).symm (s ^ (j : ℕ)) : ℕ) < orderOf s then 0 else a.val) = _
  rw [← powerEquiv_apply s hs i, ← powerEquiv_apply s hs j, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

end Cyclic

namespace Specification

private abbrev declarationType {α : Sort _} (_ : α) := α

abbrev NormType := declarationType (@norm.{u, v})
abbrev CarryCochainType := declarationType (@carryCochain.{u, v})

/-- For every generator, the inverse isomorphism takes an invariant to its carry class. -/
def EquivalenceWithCarry : Prop :=
  ∀ (C : Type u) (A : Type v) [Group C] [Finite C] [AddCommGroup A] [DistribMulAction C A]
    [TopologicalSpace C] [DiscreteTopology C] [TopologicalSpace A] [DiscreteTopology A]
    (s : C) (hs : Subgroup.zpowers s = ⊤),
    ∃ e : ContinuousH C A 2 ≃+ NormQuotient s hs A,
      ∀ a : Invariants C A,
        ∃ c : continuousCocycles C A 2,
          c.val = carryCochain s hs a ∧
          e.symm ((LinearMap.range (norm s hs)).mkQ a) = continuousClass C A 2 c

/-- For the group of order one both sides of the cyclic formula are trivial. -/
def OrderOneTriviality : Prop :=
  ∀ (C : Type u) (A : Type v) [Group C] [Finite C] [AddCommGroup A] [DistribMulAction C A]
    [TopologicalSpace C] [DiscreteTopology C] [TopologicalSpace A] [DiscreteTopology A]
    (s : C) (hs : Subgroup.zpowers s = ⊤), orderOf s = 1 →
    Subsingleton (ContinuousH C A 2) ∧ Subsingleton (NormQuotient s hs A)

end Specification

section Fields

variable (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]

/-- The field norm on unit groups. -/
abbrev fieldUnitNorm : Eˣ →* kˣ := Units.map (Algebra.norm k)

open scoped Algebra

/-- The finite Galois group is endowed with the discrete topology. -/
scoped instance galoisGroupTopology : TopologicalSpace (E ≃ₐ[k] E) := ⊥

scoped instance galoisGroupDiscrete : DiscreteTopology (E ≃ₐ[k] E) :=
  discreteTopology_bot _

/-- Coefficient units carry the discrete topology, as in the chapter conventions. -/
scoped instance coefficientUnitsTopology : TopologicalSpace Eˣ := ⊥

scoped instance coefficientUnitsDiscrete : DiscreteTopology Eˣ := discreteTopology_bot _

end Fields

namespace Specification

/-- The field form uses the natural action on units and the multiplicative field norm. -/
def FieldEquivalence : Prop :=
  ∀ (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    [IsGalois k E] [IsCyclic (E ≃ₐ[k] E)],
    Nonempty (ContinuousMulH (E ≃ₐ[k] E) Eˣ 2 ≃* (kˣ ⧸ (fieldUnitNorm k E).range))

end Specification

end

end GaloisFormalization.GH.CyclicDegreeTwo
