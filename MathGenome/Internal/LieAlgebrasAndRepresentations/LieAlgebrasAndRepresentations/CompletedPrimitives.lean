import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompletedPrimitives
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FreeLie
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.EnvelopingHopf
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWGraded

noncomputable section
namespace LieAlgebrasAndRepresentations.CompletedPrimitives
open scoped TensorProduct
open TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v
open scoped DirectSum

/-- Mark the homogeneous degree by the formal parameter. -/
def markDegrees {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
    (D : ℕ → Submodule k A) [GradedAlgebra D] : (⨁ n, D n) →ₐ[k] PowerSeries A :=
  DirectSum.toAlgebra k (fun n => D n)
    (fun n => ((PowerSeries.monomial n).restrictScalars k).comp (D n).subtype)
    (by change PowerSeries.monomial 0 (1 : A) = 1; simp)
    (by
      intro i j a b
      change PowerSeries.monomial (i+j) (a.val*b.val) =
        PowerSeries.monomial i a.val * PowerSeries.monomial j b.val
      exact (PowerSeries.monomial_mul_monomial _ _ _ _).symm)

theorem markDegrees_coeff {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
    (D : ℕ → Submodule k A) [GradedAlgebra D] (s : ⨁ n, D n) (n : ℕ) :
    PowerSeries.coeff n (markDegrees D s) = (s n : A) := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    have hm : markDegrees D (DirectSum.of (fun n => D n) i x) =
        PowerSeries.monomial i x.val :=
      DirectSum.toAddMonoid_of
        (fun n => (((PowerSeries.monomial n).restrictScalars k).comp (D n).subtype).toAddMonoidHom) i x
    rw [hm]
    change PowerSeries.coeff n (PowerSeries.monomial i x.val) =
      ((DirectSum.of (fun n => D n) i x) n : A)
    rw [PowerSeries.coeff_monomial]
    by_cases h : n = i
    · subst i; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ h]; simp [h]
  | add a b ha hb => simpa only [map_add, DirectSum.add_apply, Submodule.coe_add] using congrArg₂ (·+·) ha hb

/-- A map preserving the generator spaces preserves every homogeneous piece. -/
theorem map_mem_power {k A B : Type*} [CommRing k] [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] (G : Submodule k A) (H : Submodule k B)
    (f : A →ₐ[k] B) (h : G.map f.toLinearMap ≤ H) (n : ℕ)
    {x : A} (hx : x ∈ G ^ n) : f x ∈ H ^ n := by
  have hm : (G ^ n).map f.toLinearMap ≤ H ^ n := by
    rw [Submodule.map_pow]
    exact pow_le_pow_left' h n
  exact hm (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

/-- Coefficientwise extension to degree completions. -/
def completionMap {k A B : Type*} [CommRing k] [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] (G : Submodule k A) (H : Submodule k B)
    (f : A →ₐ[k] B) (h : G.map f.toLinearMap ≤ H) :
    degreeSeries G →ₐ[k] degreeSeries H :=
  ((PowerSeries.mapAlgHom f).comp (degreeSeries G).val).codRestrict (degreeSeries H)
    (fun p n => by
      change PowerSeries.coeff n (PowerSeries.map f.toRingHom p.val) ∈ H ^ n
      rw [PowerSeries.coeff_map]
      exact map_mem_power G H f h n (p.property n))

@[simp] theorem completionMap_coeff {k A B : Type*} [CommRing k] [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] (G : Submodule k A) (H : Submodule k B)
    (f : A →ₐ[k] B) (h : G.map f.toLinearMap ≤ H) (p : degreeSeries G) (n : ℕ) :
    PowerSeries.coeff n (completionMap G H f h p).val = f (PowerSeries.coeff n p.val) :=
  PowerSeries.coeff_map f.toRingHom n p.val

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

/-- The algebra map given by homogeneous decomposition, including all scalars. -/
def ordinaryInclusion : A k V →ₐ[k] Completion k V :=
  ((markDegrees (degree k V)).comp (DirectSum.decomposeAlgEquiv (degree k V)).toAlgHom).codRestrict
    (degreeSeries (generators k V)) (fun x n => by
      rw [AlgHom.comp_apply, markDegrees_coeff]
      exact (DirectSum.decompose (degree k V) x n).property)

theorem ordinaryInclusion_eq (x : A k V) :
    ordinaryInclusion k V x = ordinarySeries k V x := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n (markDegrees (degree k V)
    (DirectSum.decompose (degree k V) x)) = _
  rw [markDegrees_coeff]
  exact (PowerSeries.coeff_mk n (fun n => (DirectSum.decompose (degree k V) x n : A k V))).symm

@[simp] theorem ordinaryInclusion_coeff (x : A k V) (n : ℕ) :
    PowerSeries.coeff n (ordinaryInclusion k V x).val =
      (DirectSum.decompose (degree k V) x n : A k V) :=
  markDegrees_coeff _ _ _

theorem ordinaryInclusion_injective : Function.Injective (ordinaryInclusion k V) := by
  intro x y h
  apply (DirectSum.decompose (degree k V)).injective
  ext n
  simpa only [ordinaryInclusion_coeff] using
    congrArg (fun p : Completion k V => PowerSeries.coeff n p.val) h

@[simp] theorem tensorCoproduct_generator (v : V) :
    tensorCoproduct k V (TensorAlgebra.ι k v) =
      TensorAlgebra.ι k v ⊗ₜ[k] 1 + 1 ⊗ₜ[k] TensorAlgebra.ι k v :=
  TensorAlgebra.lift_ι_apply _ _

theorem coproduct_generators :
    (generators k V).map (tensorCoproduct k V).toLinearMap ≤ squareGenerators k V := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  change tensorCoproduct k V (TensorAlgebra.ι k v) ∈ squareGenerators k V
  rw [tensorCoproduct_generator]
  apply Submodule.add_mem
  · apply (show (generators k V).map
        (Algebra.TensorProduct.includeLeft : A k V →ₐ[k] _).toLinearMap ≤
          squareGenerators k V from le_sup_left)
    exact Submodule.mem_map.mpr ⟨_, LinearMap.mem_range_self _ v, rfl⟩
  · apply (show (generators k V).map
        (Algebra.TensorProduct.includeRight : A k V →ₐ[k] _).toLinearMap ≤
          squareGenerators k V from le_sup_right)
    exact Submodule.mem_map.mpr ⟨_, LinearMap.mem_range_self _ v, rfl⟩

/-- The actual completed coproduct, with values in the completed total-degree
tensor square. Its multiplicativity follows from coefficientwise extension. -/
def completedCoproduct : Completion k V →ₐ[k] CompletedSquare k V :=
  completionMap _ _ (tensorCoproduct k V) (coproduct_generators k V)

def completedLeft : Completion k V →ₐ[k] CompletedSquare k V :=
  completionMap _ _ Algebra.TensorProduct.includeLeft le_sup_left

def completedRight : Completion k V →ₐ[k] CompletedSquare k V :=
  completionMap _ _ Algebra.TensorProduct.includeRight le_sup_right

@[simp] theorem completedLeft_coeff (p : Completion k V) (n : ℕ) :
    PowerSeries.coeff n (completedLeft k V p).val = PowerSeries.coeff n p.val ⊗ₜ[k] 1 :=
  PowerSeries.coeff_map (Algebra.TensorProduct.includeLeft : A k V →ₐ[k] A k V ⊗[k] A k V).toRingHom n p.val

@[simp] theorem completedRight_coeff (p : Completion k V) (n : ℕ) :
    PowerSeries.coeff n (completedRight k V p).val = 1 ⊗ₜ[k] PowerSeries.coeff n p.val :=
  PowerSeries.coeff_map (Algebra.TensorProduct.includeRight : A k V →ₐ[k] A k V ⊗[k] A k V).toRingHom n p.val

theorem completed_primitive_iff (p : Completion k V) :
    IsCompletedPrimitive k V p ↔
      completedCoproduct k V p = completedLeft k V p + completedRight k V p := by
  constructor
  · intro h
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (completedCoproduct k V p).val =
      PowerSeries.coeff n ((completedLeft k V p).val + (completedRight k V p).val)
    simpa only [IsPrimitive, map_add, completedCoproduct, completedLeft_coeff, completedRight_coeff,
      completionMap_coeff, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply] using h n
  · intro h n
    have hn := congrArg (fun q : CompletedSquare k V => PowerSeries.coeff n q.val) h
    simpa only [IsPrimitive, completedCoproduct, completedLeft_coeff, completedRight_coeff,
      Subalgebra.coe_add, map_add, completionMap_coeff,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] using hn

theorem tmul_mem_squareDegree {i j : ℕ} {a b : A k V}
    (ha : a ∈ degree k V i) (hb : b ∈ degree k V j) :
    a ⊗ₜ[k] b ∈ squareDegree k V (i+j) := by
  have hl := map_mem_power (generators k V) (squareGenerators k V)
    (Algebra.TensorProduct.includeLeft : A k V →ₐ[k] A k V ⊗[k] A k V) le_sup_left i ha
  have hr := map_mem_power (generators k V) (squareGenerators k V)
    (Algebra.TensorProduct.includeRight : A k V →ₐ[k] A k V ⊗[k] A k V) le_sup_right j hb
  change _ ∈ squareGenerators k V ^ (i+j)
  rw [pow_add]
  simpa only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using Submodule.mul_mem_mul hl hr

private theorem totalSquare_left_generator (v : V) {n : ℕ}
    {x : A k V ⊗[k] A k V} (hx : x ∈ totalSquareDegree k V n) :
    (TensorAlgebra.ι k v ⊗ₜ[k] 1) * x ∈ totalSquareDegree k V (1+n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, a, ha, b, hb, rfl⟩ := hx
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    apply Submodule.subset_span
    refine ⟨1+i, j, by omega, TensorAlgebra.ι k v * a, ?_, b, hb, rfl⟩
    change _ ∈ generators k V ^ (1+i)
    rw [pow_add]
    exact Submodule.mul_mem_mul (by simpa using LinearMap.mem_range_self (TensorAlgebra.ι k) v) ha
  | zero => simpa using (totalSquareDegree k V (1+n)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [mul_add] using (totalSquareDegree k V (1+n)).add_mem ihx ihy
  | smul r x hx ih =>
    simpa only [Algebra.mul_smul_comm] using (totalSquareDegree k V (1+n)).smul_mem r ih

private theorem totalSquare_right_generator (v : V) {n : ℕ}
    {x : A k V ⊗[k] A k V} (hx : x ∈ totalSquareDegree k V n) :
    (1 ⊗ₜ[k] TensorAlgebra.ι k v) * x ∈ totalSquareDegree k V (1+n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, a, ha, b, hb, rfl⟩ := hx
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    apply Submodule.subset_span
    refine ⟨i, 1+j, by omega, a, ha, TensorAlgebra.ι k v * b, ?_, rfl⟩
    change _ ∈ generators k V ^ (1+j)
    rw [pow_add]
    exact Submodule.mul_mem_mul (by simpa using LinearMap.mem_range_self (TensorAlgebra.ι k) v) hb
  | zero => simpa using (totalSquareDegree k V (1+n)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [mul_add] using (totalSquareDegree k V (1+n)).add_mem ihx ihy
  | smul r x hx ih =>
    simpa only [Algebra.mul_smul_comm] using (totalSquareDegree k V (1+n)).smul_mem r ih

set_option maxHeartbeats 800000 in
/-- The chosen homogeneous pieces of the completed square are exactly the usual
total-degree pieces, not the image of the coproduct or a smaller subspace. -/
theorem squareDegree_eq_total (n : ℕ) : squareDegree k V n = totalSquareDegree k V n := by
  apply le_antisymm
  · intro x hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      apply Submodule.subset_span
      refine ⟨0, 0, rfl, algebraMap k (A k V) r, ?_, 1, ?_, ?_⟩
      · exact Submodule.algebraMap_mem r
      · simpa using (Submodule.algebraMap_mem (1 : k) :
          algebraMap k (A k V) 1 ∈ (1 : Submodule k (A k V)))
      · exact (Algebra.TensorProduct.algebraMap_apply r).symm
    | add x y i hx hy ihx ihy => exact (totalSquareDegree k V i).add_mem ihx ihy
    | mem_mul m hm i x hx ih =>
      obtain ⟨l, hl, r, hr, rfl⟩ := Submodule.mem_sup.mp hm
      obtain ⟨_, ⟨v, rfl⟩, rfl⟩ := hl
      obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hr
      rw [add_mul]
      simpa only [AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Nat.succ_eq_add_one, Nat.add_comm] using
        (totalSquareDegree k V (1+i)).add_mem
          (totalSquare_left_generator k V v ih) (totalSquare_right_generator k V w ih)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, j, hij, a, ha, b, hb, rfl⟩
    subst n
    exact tmul_mem_squareDegree k V ha hb

theorem completion_coefficients_surjective (s : ∀ n, degree k V n) :
    ∃ p : Completion k V, ∀ n, PowerSeries.coeff n p.val = (s n : A k V) := by
  refine ⟨⟨PowerSeries.mk (fun n => (s n : A k V)), ?_⟩, ?_⟩
  · intro n; simpa using (s n).property
  · intro n; exact PowerSeries.coeff_mk n (fun n => (s n : A k V))

theorem construction_spec :
    Specs.LieAlgebrasAndRepresentations.CompletedPrimitives.constructionExpected.{u,v} := by
  intro k V _ _ _
  refine ⟨ordinaryInclusion k V, completedCoproduct k V, completedLeft k V,
    completedRight k V, ordinaryInclusion_eq k V, ordinaryInclusion_injective k V, ?_,
    completedLeft_coeff k V, completedRight_coeff k V, completed_primitive_iff k V,
    squareDegree_eq_total k V, completion_coefficients_surjective k V⟩
  intro p n
  exact completionMap_coeff _ _ _ _ _ _

/-- The primitives form a Lie subalgebra; this direction uses no characteristic
assumption and no PBW theorem. -/
def primitiveLie : LieSubalgebra k (A k V) where
  carrier := {p | IsPrimitive k V p}
  zero_mem' := by simp [IsPrimitive]
  add_mem' := by
    intro a b ha hb
    change IsPrimitive k V (a + b)
    dsimp only [IsPrimitive]
    rw [map_add, ha, hb, add_tmul, tmul_add]
    abel
  smul_mem' := by
    intro r a ha
    change IsPrimitive k V (r • a)
    dsimp only [IsPrimitive]
    rw [map_smul, ha, smul_add, smul_tmul', tmul_smul]
  lie_mem' := by
    intro a b ha hb
    change tensorCoproduct k V (a*b-b*a) = (a*b-b*a) ⊗ₜ[k] 1 + 1 ⊗ₜ[k] (a*b-b*a)
    rw [map_sub, map_mul, map_mul, ha, hb]
    simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      sub_tmul, tmul_sub]
    abel

theorem tensorLie_le_primitives : tensorLie k V ≤ primitiveLie k V := by
  apply LieSubalgebra.lieSpan_le.mpr
  rintro _ ⟨v, rfl⟩
  exact tensorCoproduct_generator k V v

theorem primitive_of_mem_tensorLie {p : A k V} (hp : p ∈ tensorLie k V) :
    IsPrimitive k V p := tensorLie_le_primitives k V hp

theorem ordinaryInclusion_coeff_homogeneous {i : ℕ} {x : A k V}
    (hx : x ∈ degree k V i) (n : ℕ) :
    PowerSeries.coeff n (ordinaryInclusion k V x).val = if n = i then x else 0 := by
  rw [ordinaryInclusion_coeff]
  split_ifs with h
  · subst n; exact DirectSum.decompose_of_mem_same _ hx
  · exact DirectSum.decompose_of_mem_ne _ hx (Ne.symm h)

theorem generator_mem_degree_one (v : V) : TensorAlgebra.ι k v ∈ degree k V 1 := by
  simpa using LinearMap.mem_range_self (TensorAlgebra.ι k) v

/-- Brackets and linear combinations of homogeneous generators have all their
homogeneous components in the generated Lie algebra. -/
theorem tensorLie_homogeneous {x : A k V} (hx : x ∈ tensorLie k V) :
    ∀ n, PowerSeries.coeff n (ordinaryInclusion k V x).val ∈ tensorLie k V := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    intro n
    rw [ordinaryInclusion_coeff_homogeneous k V (generator_mem_degree_one k V v)]
    split_ifs
    · exact LieSubalgebra.subset_lieSpan (Set.mem_range_self v)
    · exact (tensorLie k V).zero_mem
  | zero => intro n; simp
  | add x y hx hy ihx ihy =>
    intro n
    simpa only [map_add, Subalgebra.coe_add] using (tensorLie k V).add_mem (ihx n) (ihy n)
  | smul r x hx ih =>
    intro n
    simpa only [map_smul, Subalgebra.coe_smul, PowerSeries.coeff_smul] using (tensorLie k V).smul_mem r (ih n)
  | lie x y hx hy ihx ihy =>
    intro n
    change PowerSeries.coeff n (ordinaryInclusion k V (x*y-y*x)).val ∈ tensorLie k V
    rw [map_sub, map_mul, map_mul, Subalgebra.coe_sub, Subalgebra.coe_mul,
      Subalgebra.coe_mul, map_sub, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    rw [← Finset.Nat.sum_antidiagonal_swap (f := fun ij =>
      PowerSeries.coeff ij.1 (ordinaryInclusion k V y).val *
        PowerSeries.coeff ij.2 (ordinaryInclusion k V x).val)]
    rw [← Finset.sum_sub_distrib]
    apply (tensorLie k V).toSubmodule.sum_mem
    intro ij hij
    exact (tensorLie k V).lie_mem (ihx ij.1) (ihy ij.2)

theorem tensorLie_constant_zero {x : A k V} (hx : x ∈ tensorLie k V) :
    PowerSeries.coeff 0 (ordinaryInclusion k V x).val = 0 := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [ordinaryInclusion_coeff_homogeneous k V (generator_mem_degree_one k V v)]
    rfl
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add, Subalgebra.coe_add, ihx, ihy, add_zero]
  | smul r x hx ih => simp [ih]
  | lie x y hx hy ihx ihy =>
    change PowerSeries.coeff 0 (ordinaryInclusion k V (x*y-y*x)).val = 0
    simp only [map_sub, map_mul, Subalgebra.coe_sub, Subalgebra.coe_mul,
      PowerSeries.coeff_zero_eq_constantCoeff, map_sub, map_mul] at *
    simp [ihx, ihy]

/-- The closure definition of the completed free Lie algebra agrees with the
product of its homogeneous pieces. This is proved before any converse theorem
about primitives is used. -/
theorem completedLie_iff_coeff (p : Completion k V) :
    InCompletedLie k V p ↔ ∀ n, PowerSeries.coeff n p.val ∈ tensorLie k V := by
  constructor
  · intro h n
    obtain ⟨x, hx, heq⟩ := h n
    rw [← heq n le_rfl, ← ordinaryInclusion_eq]
    exact tensorLie_homogeneous k V hx n
  · intro h N
    refine ⟨∑ n ∈ Finset.range (N+1), PowerSeries.coeff n p.val,
      (tensorLie k V).toSubmodule.sum_mem (fun n _ => h n), ?_⟩
    intro n hn
    rw [← ordinaryInclusion_eq]
    have hs : (ordinaryInclusion k V (∑ i ∈ Finset.range (N+1), PowerSeries.coeff i p.val)).val =
        ∑ i ∈ Finset.range (N+1), (ordinaryInclusion k V (PowerSeries.coeff i p.val)).val := by
      rw [map_sum]
      exact map_sum (degreeSeries (generators k V)).val _ _
    rw [hs, map_sum]
    simp_rw [ordinaryInclusion_coeff_homogeneous k V (p.property _)]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b hb hbn; simp [Ne.symm hbn]
    · intro hn'; exact (hn' (Finset.mem_range.mpr (by omega))).elim

theorem completedLie_positive {p : Completion k V} (hp : InCompletedLie k V p) :
    Positive k V p := by
  have h := tensorLie_constant_zero k V ((completedLie_iff_coeff k V p).mp hp 0)
  rw [ordinaryInclusion_coeff_homogeneous k V (p.property 0) 0, ite_eq_left rfl] at h
  exact h

/-- Only the ordinary classification remains as input in the passage to the
completion. This is a reduction lemma, not an assumed proof of that input. -/
theorem completed_classification_of_ordinary
    (h : ∀ x : A k V, IsPrimitive k V x ↔ x ∈ tensorLie k V) (p : Completion k V) :
    IsCompletedPrimitive k V p ↔ Positive k V p ∧ InCompletedLie k V p := by
  have heq : IsCompletedPrimitive k V p ↔ InCompletedLie k V p := by
    rw [completedLie_iff_coeff]
    exact forall_congr' (fun n => h (PowerSeries.coeff n p.val))
  exact heq.trans ⟨fun hp => ⟨completedLie_positive k V hp, hp⟩, And.right⟩

/-- The coproduct agrees with the upstream enveloping coproduct under A07.
This bridge is proved on all free Lie elements using the Lie homomorphism
property, rather than just asserted on the original vector generators. -/
theorem coproduct_tensorMap_of_generators
    (Δ : Shared.Lie.U k (FreeLie.Free k V) →ₐ[k]
      Shared.Lie.U k (FreeLie.Free k V) ⊗[k] Shared.Lie.U k (FreeLie.Free k V))
    (hΔ : ∀ y, Δ (Shared.Lie.inclusion k (FreeLie.Free k V) y) =
      Shared.Lie.inclusion k (FreeLie.Free k V) y ⊗ₜ[k] 1 +
        1 ⊗ₜ[k] Shared.Lie.inclusion k (FreeLie.Free k V) y)
    (x : Shared.Lie.U k (FreeLie.Free k V)) :
    tensorCoproduct k V (FreeLie.tensorMap k V x) =
      Algebra.TensorProduct.map (FreeLie.tensorMap k V) (FreeLie.tensorMap k V)
        (Δ x) := by
  have h : (tensorCoproduct k V).comp (FreeLie.tensorMap k V) =
      (Algebra.TensorProduct.map (FreeLie.tensorMap k V) (FreeLie.tensorMap k V)).comp
        Δ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply FreeLie.linear_hom_ext k V
    ext v
    change tensorCoproduct k V (FreeLie.tensorMap k V
      (Shared.Lie.inclusion k (FreeLie.Free k V) (FreeLie.generator k V v))) =
      Algebra.TensorProduct.map (FreeLie.tensorMap k V) (FreeLie.tensorMap k V)
        (Δ
          (Shared.Lie.inclusion k (FreeLie.Free k V) (FreeLie.generator k V v)))
    simp only [FreeLie.tensorMap_inclusion, FreeLie.tensorLieMap_generator_apply,
      tensorCoproduct_generator, hΔ,
      map_add, Algebra.TensorProduct.map_tmul, map_one]
  exact DFunLike.congr_fun h x

theorem coproduct_tensorMap (x : Shared.Lie.U k (FreeLie.Free k V)) :
    tensorCoproduct k V (FreeLie.tensorMap k V x) =
      Algebra.TensorProduct.map (FreeLie.tensorMap k V) (FreeLie.tensorMap k V)
        (EnvelopingHopf.coproduct k (FreeLie.Free k V) x) :=
  coproduct_tensorMap_of_generators k V _ (EnvelopingHopf.coproduct_inclusion k _) x

/-- Transport an ordinary enveloping primitive theorem to the tensor algebra.
Together with `reduction_spec`, this isolates the sole remaining proof input. -/
theorem tensor_recognition_of_enveloping
    (h : ∀ x : Shared.Lie.U k (FreeLie.Free k V),
      EnvelopingHopf.coproduct k (FreeLie.Free k V) x = x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x ↔
        ∃ y : FreeLie.Free k V, Shared.Lie.inclusion k (FreeLie.Free k V) y = x)
    (p : A k V) : IsPrimitive k V p ↔ p ∈ tensorLie k V := by
  obtain ⟨x, rfl⟩ := (FreeLie.tensorEquiv k V).surjective p
  change IsPrimitive k V (FreeLie.tensorMap k V x) ↔ _
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (FreeLie.tensorMap k V) (FreeLie.tensorMap k V)) :=
    (Algebra.TensorProduct.congr (FreeLie.tensorEquiv k V) (FreeLie.tensorEquiv k V)).injective
  have hp : IsPrimitive k V (FreeLie.tensorMap k V x) ↔
      EnvelopingHopf.coproduct k (FreeLie.Free k V) x = x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x := by
    dsimp only [IsPrimitive]
    rw [coproduct_tensorMap]
    rw [← hinj.eq_iff]
    simp only [map_add, Algebra.TensorProduct.map_tmul, map_one]
  rw [hp, h x]
  constructor
  · rintro ⟨y, rfl⟩
    change FreeLie.tensorMap k V (Shared.Lie.inclusion k (FreeLie.Free k V) y) ∈ tensorLie k V
    rw [FreeLie.tensorMap_inclusion]
    change (FreeLie.tensorLieMap k V) y ∈ LieSubalgebra.lieSpan k (A k V) _
    rw [← FreeLie.tensorLieMap_range]
    exact ⟨y, rfl⟩
  · intro hx
    have hr : FreeLie.tensorMap k V x ∈ (FreeLie.tensorLieMap k V).range := by
      rw [FreeLie.tensorLieMap_range]
      exact hx
    obtain ⟨y, hy⟩ := hr
    refine ⟨y, (FreeLie.tensorEquiv k V).injective ?_⟩
    change FreeLie.tensorMap k V (Shared.Lie.inclusion k (FreeLie.Free k V) y) =
      FreeLie.tensorMap k V x
    rw [FreeLie.tensorMap_inclusion]
    exact hy

/-- Algebraic assembly of the two ordinary proof ingredients: primitives in the
symmetric algebra and a PBW coalgebra equivalence. Neither ingredient is assumed
by the construction or installed as a global theorem. -/
theorem enveloping_recognition_of_symmetric
    (g : Type*) [LieRing g] [LieAlgebra k g]
    (Δ : Shared.Lie.U k g →ₐ[k] Shared.Lie.U k g ⊗[k] Shared.Lie.U k g)
    (e : SymmetricAlgebra k g ≃ₗ[k] Shared.Lie.U k g)
    (h1 : e 1 = 1)
    (hι : ∀ y, e (SymmetricAlgebra.ι k g y) = Shared.Lie.inclusion k g y)
    (hΔ : ∀ q, Δ (e q) = TensorProduct.map e.toLinearMap e.toLinearMap (Coalgebra.comul q))
    (hs : ∀ q : SymmetricAlgebra k g,
      Coalgebra.comul q = q ⊗ₜ[k] 1 + 1 ⊗ₜ[k] q ↔
        ∃ y : g, SymmetricAlgebra.ι k g y = q)
    (p : Shared.Lie.U k g) :
    Δ p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p ↔ ∃ y : g, Shared.Lie.inclusion k g y = p := by
  obtain ⟨q, rfl⟩ := e.surjective p
  have hinj : Function.Injective (TensorProduct.map e.toLinearMap e.toLinearMap) :=
    (TensorProduct.congr e e).injective
  have hc : Δ (e q) = e q ⊗ₜ[k] 1 + 1 ⊗ₜ[k] e q ↔
      Coalgebra.comul q = q ⊗ₜ[k] 1 + 1 ⊗ₜ[k] q := by
    rw [hΔ]
    constructor
    · intro h
      apply hinj
      simpa only [map_add, TensorProduct.map_tmul, LinearEquiv.coe_coe, h1] using h
    · intro h
      rw [h]
      simp only [map_add, TensorProduct.map_tmul, LinearEquiv.coe_coe, h1]
  rw [hc, hs q]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (hι y).symm.trans (congrArg e hy)⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, e.injective ((hι y).trans hy)⟩

/-! In characteristic zero the doubling endomorphism of a polynomial algebra
acts on degree n by 2^n. A primitive is an eigenvector with eigenvalue 2, so
only degree one can occur, even for an infinite set of variables. -/
namespace SymmetricPrimitives
open MvPolynomial
variable {k I : Type*} [Field k] [CharZero k]

omit [CharZero k] in
theorem scale_monomial (d : I →₀ ℕ) (a : k) :
    MvPolynomial.aeval (fun i : I => (2 : k) • (X i : MvPolynomial I k)) (monomial d a) =
      (2 : k) ^ d.sum (fun _ n => n) • monomial d a := by
  classical
  rw [aeval_monomial, monomial_eq]
  simp only [smul_eq_C_mul, Finsupp.prod, Finsupp.sum, mul_pow]
  rw [Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
  simp only [algebraMap_eq, ← map_pow, ← map_prod]
  ring

omit [CharZero k] in
theorem coeff_scale (p : MvPolynomial I k) (d : I →₀ ℕ) :
    (MvPolynomial.aeval (fun i : I => (2 : k) • (X i : MvPolynomial I k)) p).coeff d =
      (2 : k) ^ d.sum (fun _ n => n) * p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [scale_monomial, coeff_smul]
    simp only [smul_eq_mul, coeff_monomial]
    split_ifs with h
    · subst e
      rfl
    · simp
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

variable {M : Type*} [AddCommGroup M] [Module k M]

omit [CharZero k] in
theorem primitive_scaling (b : Module.Basis I k M) (q : SymmetricAlgebra k M)
    (hq : Coalgebra.comul q = q ⊗ₜ[k] 1 + 1 ⊗ₜ[k] q) :
    MvPolynomial.aeval (fun i : I => (2 : k) • (X i : MvPolynomial I k))
      (SymmetricAlgebra.equivMvPolynomial b q) =
        (2 : k) • SymmetricAlgebra.equivMvPolynomial b q := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  let m : (SymmetricAlgebra k M ⊗[k] SymmetricAlgebra k M) →ₐ[k] MvPolynomial I k :=
    Algebra.TensorProduct.lift e.toAlgHom e.toAlgHom (fun _ _ => Commute.all _ _)
  have hm : m.comp (Bialgebra.comulAlgHom k (SymmetricAlgebra k M)) =
      (MvPolynomial.aeval (fun i : I => (2 : k) • (X i : MvPolynomial I k))).comp
        e.toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply b.ext
    intro i
    change m (Coalgebra.comul (SymmetricAlgebra.ι k M (b i))) =
      (MvPolynomial.aeval (fun i : I => (2 : k) • (X i : MvPolynomial I k)))
        (e (SymmetricAlgebra.ι k M (b i)))
    simp [m, e, two_smul]
  have hh := congrArg m hq
  change (m.comp (Bialgebra.comulAlgHom k (SymmetricAlgebra k M))) q = _ at hh
  rw [hm] at hh
  simpa [m, e, two_smul] using hh

theorem primitive_iff_with_basis (b : Module.Basis I k M) (q : SymmetricAlgebra k M) :
    Coalgebra.comul q = q ⊗ₜ[k] 1 + 1 ⊗ₜ[k] q ↔
      ∃ y : M, SymmetricAlgebra.ι k M y = q := by
  classical
  constructor
  · intro hq
    let e := SymmetricAlgebra.equivMvPolynomial b
    let p := e q
    have hs := primitive_scaling b q hq
    have hd : ∀ d ∈ p.support, d.sum (fun _ n => n) = 1 := by
      intro d hdp
      have hc := congrArg (fun r : MvPolynomial I k => r.coeff d) hs
      rw [coeff_scale, coeff_smul] at hc
      change (2 : k) ^ d.sum (fun _ n => n) * p.coeff d = 2 * p.coeff d at hc
      have he : (2 : k) ^ d.sum (fun _ n => n) = 2 :=
        mul_right_cancel₀ (MvPolynomial.mem_support_iff.mp hdp) hc
      have hn : (2 : ℕ) ^ d.sum (fun _ n => n) = 2 := by exact_mod_cast he
      exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
        (hn.trans (pow_one (2 : ℕ)).symm)
    let f : M →ₗ[k] MvPolynomial I k := e.toLinearMap.comp (SymmetricAlgebra.ι k M)
    have hr : p ∈ f.range := by
      rw [← MvPolynomial.support_sum_monomial_coeff p]
      apply Submodule.sum_mem
      intro d hdp
      obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff d).mp (hd d hdp)
      subst d
      have hm : (monomial (Finsupp.single i 1)) (p.coeff (Finsupp.single i 1)) =
          p.coeff (Finsupp.single i 1) • (X i : MvPolynomial I k) := by
        simp [MvPolynomial.X, MvPolynomial.smul_monomial]
      rw [hm]
      apply Submodule.smul_mem
      exact ⟨b i, by simp [f, e]⟩
    obtain ⟨y, hy⟩ := hr
    exact ⟨y, e.injective hy⟩
  · rintro ⟨y, rfl⟩
    exact SymmetricAlgebra.comul_ι k M y

theorem primitive_iff (q : SymmetricAlgebra k M) :
    Coalgebra.comul q = q ⊗ₜ[k] 1 + 1 ⊗ₜ[k] q ↔
      ∃ y : M, SymmetricAlgebra.ι k M y = q :=
  primitive_iff_with_basis (Module.Free.chooseBasis k M) q

end SymmetricPrimitives

/-! Ordered PBW is a coalgebra equivalence: each term of the coproduct
is indexed by complementary sorted subwords. This holds in every characteristic. -/
namespace PBWBridge
attribute [local instance 100] LieRing.ofAssociativeRing

def splits {ι : Type*} : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | i :: l => (splits l).map (fun p => (i :: p.1, p.2)) ++
      (splits l).map (fun p => (p.1, i :: p.2))

theorem split_sublists {ι : Type*} {l : List ι} {p : List ι × List ι}
    (hp : p ∈ splits l) : p.1.Sublist l ∧ p.2.Sublist l := by
  induction l generalizing p with
  | nil => simp [splits] at hp; subst p; exact ⟨List.Sublist.refl _, List.Sublist.refl _⟩
  | cons i l ih =>
    simp only [splits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨(ih hq).1.cons_cons i, (ih hq).2.cons i⟩
    · exact ⟨(ih hq).1.cons i, (ih hq).2.cons_cons i⟩

variable {k A ι : Type*} [CommRing k] [Ring A] [Algebra k A]

theorem word_coproduct (f : ι → A) (Δ : A →ₐ[k] A ⊗[k] A)
    (hΔ : ∀ i, Δ (f i) = f i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] f i) (l : List ι) :
    Δ (l.map f).prod = ((splits l).map (fun p =>
      (p.1.map f).prod ⊗ₜ[k] (p.2.map f).prod)).sum := by
  induction l with
  | nil => simp [splits, Algebra.TensorProduct.one_def]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, hΔ, ih, splits,
      List.map_append, List.sum_append, List.map_map, Function.comp_def,
      List.map_cons, List.prod_cons, add_mul]
    congr 1
    · rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    · rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

open Shared.Lie.PBW Shared.Lie.PBW.Graded
variable {g : Type*} [LieRing g] [LieAlgebra k g] [LinearOrder ι]

noncomputable def e (b : Module.Basis ι k g) :
    SymmetricAlgebra k g ≃ₗ[k] Shared.Lie.U k g :=
  (orderedSymmetricBasis b).equiv (orderedBasis b) (Equiv.refl _)

theorem e_word (b : Module.Basis ι k g) (l : List ι) (hl : l.Pairwise (· ≤ ·)) :
    e b (symmetricWord (l.map b)) = monomial b l := by
  have he := Module.Basis.equiv_apply (orderedSymmetricBasis b) (⟨l, hl⟩ : OrderedWord ι)
    (orderedBasis b) (Equiv.refl _)
  simpa only [orderedSymmetricBasis_apply, orderedBasis_apply, Equiv.refl_apply,
    orderedMonomial, e] using he

theorem e_one (b : Module.Basis ι k g) : e b 1 = 1 := by
  simpa only [symmetricWord, List.map_nil, List.prod_nil, monomial_nil] using
    e_word b [] List.Pairwise.nil

theorem e_inclusion (b : Module.Basis ι k g) (x : g) :
    e b (SymmetricAlgebra.ι k g x) = Shared.Lie.inclusion k g x := by
  have hh : (e b).toLinearMap.comp (SymmetricAlgebra.ι k g) =
      (Shared.Lie.inclusion k g).toLinearMap := by
    apply b.ext
    intro i
    simpa [symmetricWord, monomial, Shared.Lie.word] using
      e_word b [i] (List.pairwise_singleton _ _)
  exact LinearMap.congr_fun hh x

theorem e_coproduct (b : Module.Basis ι k g)
    (Δ : Shared.Lie.U k g →ₐ[k] Shared.Lie.U k g ⊗[k] Shared.Lie.U k g)
    (hΔ : ∀ x, Δ (Shared.Lie.inclusion k g x) =
      Shared.Lie.inclusion k g x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Shared.Lie.inclusion k g x)
    (q : SymmetricAlgebra k g) :
    Δ (e b q) = TensorProduct.map (e b).toLinearMap (e b).toLinearMap (Coalgebra.comul q) := by
  suffices hh : Δ.toLinearMap.comp (e b).toLinearMap =
      (TensorProduct.map (e b).toLinearMap (e b).toLinearMap).comp Coalgebra.comul by
    exact LinearMap.congr_fun hh q
  apply (orderedSymmetricBasis b).ext
  intro l
  change Δ (e b (orderedSymmetricBasis b l)) = _
  rw [orderedSymmetricBasis_apply, e_word b l.val l.property]
  rw [show monomial b l.val = (l.val.map (fun i => Shared.Lie.inclusion k g (b i))).prod from by
    simp [monomial, Shared.Lie.word, List.map_map, Function.comp_def]]
  rw [word_coproduct _ Δ (fun i => hΔ (b i))]
  change _ = TensorProduct.map (e b).toLinearMap (e b).toLinearMap
    ((Bialgebra.comulAlgHom k (SymmetricAlgebra k g)) (symmetricWord (l.val.map b)))
  rw [show symmetricWord (l.val.map b) = (l.val.map (fun i => SymmetricAlgebra.ι k g (b i))).prod from by
    simp [symmetricWord, List.map_map, Function.comp_def]]
  rw [word_coproduct _ (Bialgebra.comulAlgHom k (SymmetricAlgebra k g))
    (fun i => SymmetricAlgebra.comul_ι k g (b i))]
  rw [map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  dsimp only [Function.comp_apply]
  rw [TensorProduct.map_tmul]
  have hs := split_sublists hp
  have h₁ := e_word b p.1 (List.Pairwise.sublist hs.1 l.property)
  have h₂ := e_word b p.2 (List.Pairwise.sublist hs.2 l.property)
  simpa only [symmetricWord, monomial, Shared.Lie.word, List.map_map,
    Function.comp_def, LinearEquiv.coe_coe] using congrArg₂
      (fun a c => a ⊗ₜ[k] c) h₁.symm h₂.symm

end PBWBridge

/-- Tensor primitive recognition gives the ordinary statement in the original
enveloping algebra, with the exact canonical inclusion. -/
theorem enveloping_recognition_of_tensor
    (h : ∀ p : A k V, IsPrimitive k V p ↔ p ∈ tensorLie k V)
    (x : Shared.Lie.U k (FreeLie.Free k V)) :
    IsPrimitive k V (FreeLie.tensorMap k V x) ↔
      ∃ y : FreeLie.Free k V, Shared.Lie.inclusion k (FreeLie.Free k V) y = x := by
  constructor
  · intro hp
    have hr : FreeLie.tensorMap k V x ∈ (FreeLie.tensorLieMap k V).range := by
      rw [FreeLie.tensorLieMap_range]
      exact (h _).mp hp
    obtain ⟨y, hy⟩ := hr
    refine ⟨y, (FreeLie.tensorEquiv k V).injective ?_⟩
    change FreeLie.tensorMap k V (Shared.Lie.inclusion k (FreeLie.Free k V) y) =
      FreeLie.tensorMap k V x
    rw [FreeLie.tensorMap_inclusion]
    exact hy
  · rintro ⟨y, rfl⟩
    rw [FreeLie.tensorMap_inclusion]
    apply primitive_of_mem_tensorLie
    change (FreeLie.tensorLieMap k V) y ∈ LieSubalgebra.lieSpan k (A k V) _
    rw [← FreeLie.tensorLieMap_range]
    exact ⟨y, rfl⟩

theorem reduction_spec :
    Specs.LieAlgebrasAndRepresentations.CompletedPrimitives.reductionExpected.{u,v} := by
  intro h
  constructor
  · intro k V _ _ _ _
    refine ⟨h k V, ?_, enveloping_recognition_of_tensor k V (h k V), ?_⟩
    · intro p hp
      rw [← ordinaryInclusion_eq]
      exact tensorLie_constant_zero k V ((h k V p).mp hp)
    · intro Δ ε S hL x
      exact coproduct_tensorMap_of_generators k V Δ hL.1 x
  · intro k V _ _ _ _
    refine ⟨?_, completed_classification_of_ordinary k V (h k V), completedLie_iff_coeff k V⟩
    intro p hp
    exact ((completed_classification_of_ordinary k V (h k V) p).mp hp).1


/-- Ordinary recognition in the enveloping algebra follows from the ordered
PBW coalgebra equivalence and symmetric primitive recognition. -/
theorem enveloping_primitive_iff [CharZero k]
    (g : Type*) [LieRing g] [LieAlgebra k g]
    (Δ : Shared.Lie.U k g →ₐ[k] Shared.Lie.U k g ⊗[k] Shared.Lie.U k g)
    (hΔ : ∀ x, Δ (Shared.Lie.inclusion k g x) =
      Shared.Lie.inclusion k g x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Shared.Lie.inclusion k g x)
    (p : Shared.Lie.U k g) :
    Δ p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p ↔ ∃ y : g, Shared.Lie.inclusion k g y = p := by
  let : LinearOrder (Module.Free.ChooseBasisIndex k g) :=
    IsWellOrder.linearOrder WellOrderingRel
  let b := Module.Free.chooseBasis k g
  exact enveloping_recognition_of_symmetric k g Δ (PBWBridge.e b)
    (PBWBridge.e_one b) (PBWBridge.e_inclusion b) (PBWBridge.e_coproduct b Δ hΔ)
    SymmetricPrimitives.primitive_iff p

/-- Primitives in the tensor algebra are exactly its generated free Lie algebra. -/
theorem recognition_spec :
    Specs.LieAlgebrasAndRepresentations.CompletedPrimitives.recognitionExpected.{u,v} := by
  intro k V _ _ _ _ p
  exact tensor_recognition_of_enveloping k V
    (enveloping_primitive_iff k (FreeLie.Free k V) _
      (EnvelopingHopf.coproduct_inclusion k _)) p

theorem ordinary_spec :
    Specs.LieAlgebrasAndRepresentations.CompletedPrimitives.ordinaryExpected.{u,v} :=
  (reduction_spec recognition_spec).1

theorem completed_spec :
    Specs.LieAlgebrasAndRepresentations.CompletedPrimitives.completedExpected.{u,v} :=
  (reduction_spec recognition_spec).2

end LieAlgebrasAndRepresentations.CompletedPrimitives
