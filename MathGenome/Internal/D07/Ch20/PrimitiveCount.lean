import MathGenome.Internal.Specs.D07.Ch20.PrimitiveCount
import MathGenome.Internal.D07.Ch13.MultiplicativeCyclic
import MathGenome.Internal.D07.Ch13.PrimitivePolynomials
import MathGenome.Internal.D07.Ch20.PrimitiveCountMaximalOrderForcesIrreducible
import Mathlib.FieldTheory.Finite.GaloisField

universe u v
namespace D07.Ch20.PrimitiveCount
open Polynomial IntermediateField
open Specs.D07.Ch20.PrimitiveCount

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [Finite K] [Finite L]

/-- The cardinality hypothesis gives the extension degree, including degree one. -/
lemma finrank_eq (n : ℕ) (hcard : Nat.card L = Nat.card K ^ n) :
    Module.finrank K L = n := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  apply Nat.pow_right_injective hq
  exact (Module.natCard_eq_pow_finrank (K := K) (V := L)).symm.trans hcard

/-- A multiplicative generator has a monic minimal polynomial of the full degree. -/
lemma generator_minpoly (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card L = Nat.card K ^ n) (a : Lˣ)
    (ha : Subgroup.zpowers a = ⊤) :
    Ch13.PrimitivePolynomials.IsPrimitive K L n (minpoly K (a : L)) := by
  have hi : IsIntegral K (a : L) := Algebra.IsIntegral.isIntegral _
  have hg := Ch13.PrimitiveDistinction.multiplicativeGenerator_is_fieldGenerator K L a ha
  have hd := IntermediateField.adjoin.finrank hi
  rw [hg, IntermediateField.finrank_top', finrank_eq n hcard] at hd
  exact ⟨hn, minpoly.monic hi, hd.symm, minpoly.irreducible hi, a, minpoly.aeval K _, ha⟩

/-- The map whose fibers consist of the n conjugate primitive roots. -/
noncomputable def generatorMinpoly (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card L = Nat.card K ^ n) :
    {a : Lˣ // Subgroup.zpowers a = ⊤} →
      {f : K[X] // Ch13.PrimitivePolynomials.IsPrimitive K L n f} :=
  fun a => ⟨minpoly K (a.val : L), generator_minpoly n hn hcard a.val a.property⟩

lemma generatorMinpoly_surjective (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card L = Nat.card K ^ n) :
    Function.Surjective (generatorMinpoly (K := K) (L := L) n hn hcard) := by
  rintro ⟨f, hf⟩
  obtain ⟨_, hm, _, hi, a, ha, hag⟩ := hf
  refine ⟨⟨a, hag⟩, Subtype.ext ?_⟩
  exact (minpoly.eq_of_irreducible_of_monic hi ha hm).symm

theorem primitive_polynomials_finite : PrimitivePolynomialsFinite.{u,v} := by
  intro K L _ _ _ _ _ n hn hcard
  exact Finite.of_surjective _ (generatorMinpoly_surjective n hn hcard)

omit [Finite L] in
/-- There are exactly degree(f) roots: the Frobenius orbit has no repetitions. -/
lemma card_roots (f : K[X]) (hf : Irreducible f) (a : L) (ha : aeval a f = 0) :
    Nat.card {b : L // aeval b f = 0} = f.natDegree := by
  let r : Fin f.natDegree → {b : L // aeval b f = 0} := fun i =>
    ⟨a ^ (Nat.card K ^ i.val), (Ch13.FrobeniusRoots.roots_eq_orbit f a hf ha _).mpr ⟨i, rfl⟩⟩
  have hr : Function.Bijective r := by
    constructor
    · intro i j h
      exact Ch13.FrobeniusRoots.orbit_injective f a hf ha (congrArg Subtype.val h)
    · intro b
      obtain ⟨i, hi⟩ := (Ch13.FrobeniusRoots.roots_eq_orbit f a hf ha b.val).mp b.property
      exact ⟨i, Subtype.ext hi.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective r hr)).symm.trans (Nat.card_fin _)

/-- Each fiber of the minimal-polynomial map is the complete root set. -/
noncomputable def fiberEquivRoots (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card L = Nat.card K ^ n)
    (f : {f : K[X] // Ch13.PrimitivePolynomials.IsPrimitive K L n f}) :
    {a // generatorMinpoly (K := K) (L := L) n hn hcard a = f} ≃
      {b : L // aeval b f.val = 0} := by
  let r : {a // generatorMinpoly (K := K) (L := L) n hn hcard a = f} →
      {b : L // aeval b f.val = 0} := fun a => ⟨a.val.val, by
    have heq := congrArg Subtype.val a.property
    change minpoly K (a.val.val : L) = f.val at heq
    rw [← heq]
    exact minpoly.aeval K _⟩
  exact Equiv.ofBijective r ⟨by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact Units.ext (congrArg Subtype.val h), by
    intro b
    obtain ⟨_, hm, _, hi, hgen⟩ := f.property
    obtain ⟨a, hab, hag⟩ :=
      (Ch13.PrimitivePolynomials.root_generator_iff f.val hi b.val b.property).mp hgen
    refine ⟨⟨⟨a, hag⟩, Subtype.ext ?_⟩, Subtype.ext hab⟩
    change minpoly K (a : L) = f.val
    rw [hab]
    exact (minpoly.eq_of_irreducible_of_monic hi b.property hm).symm⟩

theorem primitive_count_product : PrimitiveCountProduct.{u,v} := by
  intro K L _ _ _ _ _ n hn hcard
  classical
  let P := {f : K[X] // Ch13.PrimitivePolynomials.IsPrimitive K L n f}
  let G := {a : Lˣ // Subgroup.zpowers a = ⊤}
  let m : G → P := generatorMinpoly n hn hcard
  have : Finite P := primitive_polynomials_finite K L n hn hcard
  let := Fintype.ofFinite P
  have hfiber (f : P) : Nat.card {a // m a = f} = n := by
    rw [Nat.card_congr (fiberEquivRoots n hn hcard f)]
    obtain ⟨_, _, hd, hi, a, ha, _⟩ := f.property
    rw [card_roots f.val hi (a : L) ha, hd]
  have htotal : Nat.card G = Nat.card P * n := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv m), Nat.card_sigma]
    simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  have hgen := (Ch13.MultiplicativeCyclic.finite_field_units L (Nat.card L) rfl).2.2
  rw [hcard] at hgen
  exact (Nat.mul_comm n (Nat.card P)).trans (htotal.symm.trans hgen)

theorem primitive_count : PrimitiveCount.{u,v} := by
  intro K L _ _ _ _ _ n hn hcard
  have h := primitive_count_product K L n hn hcard
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hn.ne')).mpr
  have h' := congrArg (fun m : ℕ => (m : ℚ)) h
  simpa only [Nat.cast_mul, mul_comm] using h'

/-- Equal extension and polynomial degrees provide a root in the specified L. -/
lemma exists_root_of_degree (n : ℕ) (hcard : Nat.card L = Nat.card K ^ n)
    (f : K[X]) (hf : Irreducible f) (hd : f.natDegree = n) :
    ∃ a : L, aeval a f = 0 := by
  let : Fact (Irreducible f) := ⟨hf⟩
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := K) (K := AdjoinRoot f) (L := L) (by
      rw [show Module.finrank K (AdjoinRoot f) = f.natDegree from
        finrank_quotient_span_eq_natDegree, hd, finrank_eq n hcard])
  refine ⟨φ (AdjoinRoot.root f), ?_⟩
  rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

theorem order_criterion : OrderCriterion.{u,v} := by
  intro K L _ _ _ _ _ n f hn hcard hm hd hf0
  constructor
  · rintro ⟨_, _, _, hf, a, ha, hag⟩
    have ho := PolynomialOrder.root_order K f hf (hd ▸ hn) hf0 L (a : L) ha
    change Specs.D07.Ch20.PolynomialOrder.orderValue K f = orderOf (a : L) at ho
    rw [ho, orderOf_units, orderOf_eq_card_of_zpowers_eq_top hag, Nat.card_units, hcard]
  · intro ho
    obtain ⟨hf, hall⟩ :=
      PrimitiveCountMaximalOrderForcesIrreducible.maximal_order_forces_irreducible
        K n f hn hm hd hf0 ho
    obtain ⟨a, ha⟩ := exists_root_of_degree n hcard f hf hd
    obtain ⟨z, hza, hz⟩ := hall L hcard a ha
    exact ⟨hn, hm, hd, hf, z, hza.symm ▸ ha, hz⟩

theorem maximal_order_forces_irreducible : MaximalOrderForcesIrreducible.{u,v} :=
  PrimitiveCountMaximalOrderForcesIrreducible.maximal_order_forces_irreducible

end D07.Ch20.PrimitiveCount
