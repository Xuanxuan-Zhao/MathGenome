import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2Model
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

universe u v w

namespace LieAlgebrasAndRepresentations.Sl2SimpleModules

open Module

attribute [local instance] LieRing.ofAssociativeRing
open Specs.LieAlgebrasAndRepresentations.Sl2Model
open Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules

variable (k : Type u) [Field k]

/-- Bridge from the actual trace-zero matrices to Mathlib's ladder API. -/
theorem standardTriple : IsSl2Triple (H k) (E k) (F k) where
  h_ne_zero := by
    intro hh
    have := congrArg (fun x : Model k => x.val 0 0) hh
    simp [H, Matrix.single] at this
  lie_e_f := (sl2_relations k).2.2
  lie_h_e_nsmul := by simpa [two_smul] using (sl2_relations k).1
  lie_h_f_nsmul := by
    simpa [two_smul, neg_smul] using (sl2_relations k).2.1

variable {k}
variable (M : Type v) [AddCommGroup M] [Module k M]
  [LieRingModule (Model k) M] [LieModule k (Model k) M]

/-- The lowering string is defined using powers of the actual action of f. -/
def loweringString (v : M) (j : ℕ) : M :=
  (LieModule.toEnd k (Model k) M (F k) ^ j) v

@[simp] theorem loweringString_zero (v : M) : loweringString (k := k) M v 0 = v := rfl

theorem loweringString_succ (v : M) (j : ℕ) :
    loweringString (k := k) M v (j + 1) = ⁅F k, loweringString (k := k) M v j⁆ := by
  simp [loweringString, pow_succ']

/-- Existence of a highest vector with natural highest weight. -/
theorem exists_highest_vector [CharZero k] [IsAlgClosed k] [Nontrivial M]
    [FiniteDimensional k M] :
    ∃ (n : ℕ) (v : M), (standardTriple k).HasPrimitiveVectorWith v (n : k) := by
  obtain ⟨μ, v, _, hv⟩ := (standardTriple k).exists_hasPrimitiveVectorWith (R := k) (M := M)
  obtain ⟨n, rfl⟩ := hv.exists_nat
  exact ⟨n, v, hv⟩

variable {M}

theorem loweringString_h {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k)) (j : ℕ) :
    ⁅H k, loweringString (k := k) M v j⁆ =
      ((n : k) - 2 * (j : k)) • loweringString (k := k) M v j :=
  hv.lie_h_pow_toEnd_f j

theorem loweringString_e_succ {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k)) (j : ℕ) :
    ⁅E k, loweringString (k := k) M v (j + 1)⁆ =
      (((j : k) + 1) * ((n : k) - (j : k))) • loweringString (k := k) M v j :=
  hv.lie_e_pow_succ_toEnd_f j

theorem loweringString_ne_zero [CharZero k] {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k))
    {j : ℕ} (hj : j ≤ n) : loweringString (k := k) M v j ≠ 0 :=
  hv.pow_toEnd_f_ne_zero_of_eq_nat rfl hj

theorem loweringString_end [CharZero k] [FiniteDimensional k M] {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k)) :
    loweringString (k := k) M v (n + 1) = 0 :=
  hv.pow_toEnd_f_eq_zero_of_eq_nat rfl

/-- The nonzero lowering string consists of distinct h-eigenvectors. -/
theorem loweringString_linearIndependent [CharZero k] {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k)) :
    LinearIndependent k (fun j : Fin (n + 1) => loweringString (k := k) M v j.val) := by
  apply (LieModule.toEnd k (Model k) M (H k)).eigenvectors_linearIndependent'
    (fun j : Fin (n + 1) => (n : k) - 2 * (j.val : k))
  · intro i j hij
    apply Fin.ext
    have hij' : (i.val : k) = (j.val : k) := by
      have htwo : (2 : k) ≠ 0 := by norm_num
      exact (mul_left_cancel₀ htwo) (sub_right_injective hij)
    exact_mod_cast hij'
  · intro j
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨loweringString_h hv j.val, loweringString_ne_zero hv (by omega)⟩

/-- The string span is invariant under e, f and h, hence under every actual
trace-zero matrix. This proves generation without assuming a PBW certificate. -/
def stringSubmodule [CharZero k] [FiniteDimensional k M] {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k)) :
    LieSubmodule k (Model k) M where
  __ := Submodule.span k (Set.range (fun j : Fin (n + 1) =>
    loweringString (k := k) M v j.val))
  lie_mem := by
    let S := Submodule.span k (Set.range (fun j : Fin (n + 1) =>
      loweringString (k := k) M v j.val))
    have hmem (j : Fin (n + 1)) : loweringString (k := k) M v j.val ∈ S :=
      Submodule.subset_span ⟨j, rfl⟩
    intro x m hm
    change ⁅x, m⁆ ∈ S
    have hgen (j : Fin (n + 1)) : ⁅x, loweringString (k := k) M v j.val⁆ ∈ S := by
      have he : ⁅E k, loweringString (k := k) M v j.val⁆ ∈ S := by
        rcases j with ⟨j, hj⟩
        cases j with
        | zero => simp [hv.lie_e]
        | succ j =>
          rw [loweringString_e_succ hv]
          exact S.smul_mem _ (hmem ⟨j, by omega⟩)
      have hf : ⁅F k, loweringString (k := k) M v j.val⁆ ∈ S := by
        rw [← loweringString_succ]
        by_cases hj : j.val < n
        · exact hmem ⟨j.val + 1, by omega⟩
        · have hlast : j.val = n := by omega
          rw [hlast, loweringString_end hv]
          exact S.zero_mem
      have hh : ⁅H k, loweringString (k := k) M v j.val⁆ ∈ S := by
        rw [loweringString_h hv]
        exact S.smul_mem _ (hmem j)
      rw [sl2_expansion k x, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
      exact S.add_mem (S.add_mem (S.smul_mem _ he) (S.smul_mem _ hf)) (S.smul_mem _ hh)
    induction hm using Submodule.span_induction with
    | mem z hz => obtain ⟨j, rfl⟩ := hz; exact hgen j
    | zero => simp [hv.lie_e]
    | add a b ha hb iha ihb => simpa only [lie_add] using S.add_mem iha ihb
    | smul a b hb ih => simpa only [lie_smul] using S.smul_mem a ih

theorem stringSubmodule_eq_top [CharZero k] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (Model k) M] {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k)) :
    stringSubmodule hv = ⊤ := by
  apply (IsSimpleOrder.eq_bot_or_eq_top (stringSubmodule hv)).resolve_left
  intro hbot
  have hmem : v ∈ stringSubmodule hv :=
    Submodule.subset_span ⟨(0 : Fin (n + 1)), rfl⟩
  rw [hbot] at hmem
  exact hv.ne_zero hmem

/-- A basis obtained from a highest vector, with no choice of normalization. -/
def highestWeightBasis [CharZero k] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (Model k) M] {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k)) :
    Basis (Fin (n + 1)) k M :=
  Basis.mk (loweringString_linearIndependent hv) (by
    change ⊤ ≤ (stringSubmodule hv).toSubmodule
    rw [stringSubmodule_eq_top hv]
    exact le_rfl)

@[simp] theorem highestWeightBasis_apply [CharZero k] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (Model k) M] {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k)) (j : Fin (n + 1)) :
    highestWeightBasis hv j = loweringString (k := k) M v j.val :=
  Basis.mk_apply _ _ _

theorem highestWeightBasis_isStandard [CharZero k] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (Model k) M] {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k)) :
    IsStandardBasis (highestWeightBasis hv) := by
  intro j
  refine ⟨?_, ?_, ?_⟩
  · simpa using loweringString_h hv j.val
  · simp only [highestWeightBasis_apply, ← loweringString_succ, basisVector]
    split_ifs with hj
    · simp
    · have hjn : j.val = n := by omega
      rw [hjn, loweringString_end hv]
  · rcases j with ⟨j, hj⟩
    cases j with
    | zero => simp [hv.lie_e]
    | succ j =>
      simp only [highestWeightBasis_apply, loweringString_e_succ hv,
        Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, basisVector]
      rw [dite_eq_left (by omega)]
      congr 1
      ring

omit [LieRingModule (Model k) M] [LieModule k (Model k) M] in
theorem standardBasis_parameter {n m : ℕ}
    (b : Basis (Fin (n + 1)) k M) (c : Basis (Fin (m + 1)) k M) : n = m := by
  have hb := Module.finrank_eq_card_basis b
  have hc := Module.finrank_eq_card_basis c
  simp only [Fintype.card_fin] at hb hc
  omega

theorem classification_spec : classificationExpected.{u,v} := by
  intro k _ _ _ M _ _ _ _ _ _ _
  obtain ⟨n, v, hv⟩ := exists_highest_vector (k := k) M
  refine ⟨n, ⟨highestWeightBasis hv, highestWeightBasis_isStandard hv⟩, ?_⟩
  rintro m ⟨b, _⟩
  exact standardBasis_parameter b (highestWeightBasis hv)

theorem distinct_spec : distinctExpected.{u,v,w} := by
  intro k _ M N _ _ _ _ _ _ _ _ n m b c hnm
  refine ⟨fun φ => hnm ?_⟩
  have hb := Module.finrank_eq_card_basis b
  have hc := Module.finrank_eq_card_basis c
  have hφ := φ.toLinearEquiv.finrank_eq
  simp only [Fintype.card_fin] at hb hc
  omega

theorem equivalence_spec : equivalenceExpected.{u,v,w} := by
  intro k _ M N _ _ _ _ _ _ _ _ n b c hb hc
  let φ := b.equiv c (Equiv.refl (Fin (n + 1)))
  have hφ (j : Fin (n + 1)) : φ (b j) = c j := by simp [φ]
  have hφv (j : ℕ) : φ (basisVector b j) = basisVector c j := by
    simp only [basisVector]
    split_ifs <;> simp [hφ]
  have hh (m : M) : φ ⁅H k, m⁆ = ⁅H k, φ m⁆ := by
    have hmaps : φ.toLinearMap.comp (LieModule.toEnd k (Model k) M (H k)) =
        (LieModule.toEnd k (Model k) N (H k)).comp φ.toLinearMap := by
      apply b.ext
      intro j
      change φ ⁅H k, b j⁆ = ⁅H k, φ (b j)⁆
      rw [hφ, (hb j).1, (hc j).1, map_smul, hφ]
    exact LinearMap.congr_fun hmaps m
  have hf (m : M) : φ ⁅F k, m⁆ = ⁅F k, φ m⁆ := by
    have hmaps : φ.toLinearMap.comp (LieModule.toEnd k (Model k) M (F k)) =
        (LieModule.toEnd k (Model k) N (F k)).comp φ.toLinearMap := by
      apply b.ext
      intro j
      change φ ⁅F k, b j⁆ = ⁅F k, φ (b j)⁆
      rw [hφ, (hb j).2.1, (hc j).2.1, hφv]
    exact LinearMap.congr_fun hmaps m
  have he (m : M) : φ ⁅E k, m⁆ = ⁅E k, φ m⁆ := by
    have hmaps : φ.toLinearMap.comp (LieModule.toEnd k (Model k) M (E k)) =
        (LieModule.toEnd k (Model k) N (E k)).comp φ.toLinearMap := by
      apply b.ext
      intro j
      change φ ⁅E k, b j⁆ = ⁅E k, φ (b j)⁆
      rw [hφ, (hb j).2.2, (hc j).2.2, map_smul, hφv]
    exact LinearMap.congr_fun hmaps m
  refine ⟨{ φ with map_lie' := ?_ }, hφ⟩
  intro x m
  change φ ⁅x, m⁆ = ⁅x, φ m⁆
  rw [sl2_expansion k x]
  simp only [add_lie, smul_lie, map_add, map_smul, sl2_e, sl2_f, sl2_h, he, hf, hh]

/-- A coordinate of e.v; the nonzero terms in the raising operator cannot cancel. -/
theorem standard_e_coordinate {n : ℕ} (b : Basis (Fin (n + 1)) k M)
    (hb : IsStandardBasis b) (v : M) (i : ℕ) (hi : i < n) :
    b.repr ⁅E k, v⁆ ⟨i, by omega⟩ =
      (((i : k) + 1) * ((n : k) - (i : k))) *
        b.repr v ⟨i + 1, by omega⟩ := by
  classical
  let i' : Fin (n + 1) := ⟨i, by omega⟩
  let j' : Fin (n + 1) := ⟨i + 1, by omega⟩
  have heq : ⁅E k, v⁆ = ∑ j : Fin (n + 1),
      b.repr v j • (((j.val : k) * ((n : k) - (j.val : k) + 1)) •
        basisVector b (j.val - 1)) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [lie_sum, lie_smul, (hb _).2.2]
  rw [heq, map_sum, Finsupp.finsetSum_apply]
  change (∑ j : Fin (n + 1),
    (b.repr (b.repr v j • ((j.val : k) * ((n : k) - (j.val : k) + 1)) •
      basisVector b (j.val - 1))) i') = _
  rw [Finset.sum_eq_single j']
  · simp only [basisVector, j', Nat.add_sub_cancel]
    rw [dite_eq_left (by omega)]
    simp only [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply,
      i', ↓reduceIte, smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    ring
  · intro j _ hj
    by_cases hj0 : j.val = 0
    · simp [hj0]
    have hpred : j.val - 1 < n + 1 := by omega
    have hij : (⟨j.val - 1, hpred⟩ : Fin (n + 1)) ≠ i' := by
      intro h
      apply hj
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [i', j'] at *
      omega
    simp [basisVector, hpred, hij]
  · simp

theorem standard_e_kernel {n : ℕ} (b : Basis (Fin (n + 1)) k M)
    [CharZero k] (hb : IsStandardBasis b) {v : M} (hv : ⁅E k, v⁆ = 0) :
    v = b.repr v 0 • b 0 := by
  have hcoord (j : Fin (n + 1)) (hj : j ≠ 0) : b.repr v j = 0 := by
    have hj0 : j.val ≠ 0 := by
      intro h
      exact hj (Fin.ext h)
    have hlt : j.val - 1 < n := by omega
    have heq := standard_e_coordinate b hb v (j.val - 1) hlt
    simp only [hv, map_zero, Finsupp.zero_apply] at heq
    have hj' : (⟨j.val - 1 + 1, by omega⟩ : Fin (n + 1)) = j := by
      apply Fin.ext
      dsimp
      omega
    rw [hj'] at heq
    have hc : (((j.val - 1 : ℕ) : k) + 1) * ((n : k) - ((j.val - 1 : ℕ) : k)) ≠ 0 := by
      apply mul_ne_zero
      · exact Nat.cast_add_one_ne_zero _
      · exact sub_ne_zero.mpr (by exact_mod_cast (by omega : n ≠ j.val - 1))
    exact (mul_eq_zero.mp heq.symm).resolve_left hc
  apply b.repr.injective
  ext j
  by_cases hj : j = 0
  · subst j; simp
  · simp [hcoord j hj, hj]

/-- Any module with the displayed basis is simple. A highest vector in a nonzero
submodule lies in ker(e)=k v₀; applying f then recovers every basis vector. -/
theorem isIrreducible_of_standardBasis [CharZero k] [IsAlgClosed k]
    {n : ℕ} (b : Basis (Fin (n + 1)) k M) (hb : IsStandardBasis b) :
    LieModule.IsIrreducible k (Model k) M := by
  let : FiniteDimensional k M := Module.Finite.of_basis b
  let : Nontrivial M := b.linearIndependent.nontrivial
  apply LieModule.IsIrreducible.mk
  intro N hN
  let : Nontrivial N := (LieSubmodule.nontrivial_iff_ne_bot k (Model k) M).mpr hN
  obtain ⟨μ, w, hw, hp⟩ :=
    (standardTriple k).exists_hasPrimitiveVectorWith (R := k) (M := N)
  have hw0 : (w : M) ≠ 0 := by
    intro h
    exact hw (Subtype.ext h)
  have he : ⁅E k, (w : M)⁆ = 0 := congrArg Subtype.val hp.lie_e
  have hform := standard_e_kernel b hb he
  have hc : b.repr (w : M) 0 ≠ 0 := by
    intro hc
    rw [hform, hc, zero_smul] at hw0
    exact hw0 rfl
  have hb0 : b 0 ∈ N := by
    apply (N.toSubmodule.smul_mem_iff hc).mp
    rw [← hform]
    exact w.property
  have hbmem (j : ℕ) (hj : j < n + 1) : b ⟨j, hj⟩ ∈ N := by
    induction j with
    | zero => exact hb0
    | succ j ih =>
      have hm := N.lie_mem (x := F k) (ih (by omega))
      rw [(hb ⟨j, by omega⟩).2.1, basisVector, dite_eq_left hj] at hm
      exact hm
  apply top_unique
  intro m _
  rw [← b.sum_repr m]
  exact N.toSubmodule.sum_mem (fun j _ => N.smul_mem _ (hbmem j.val j.isLt))

/-- A basis identified with a lowering string inherits all three formulas,
including the zero vectors at the endpoints. -/
theorem standardBasis_of_string [CharZero k] [FiniteDimensional k M] {n : ℕ} {v : M}
    (hv : (standardTriple k).HasPrimitiveVectorWith v (n : k))
    (b : Basis (Fin (n + 1)) k M)
    (hb : ∀ j, b j = loweringString (k := k) M v j.val) : IsStandardBasis b := by
  intro j
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hb] using loweringString_h hv j.val
  · simp only [hb, ← loweringString_succ, basisVector]
    split_ifs with hj
    · rfl
    · have hjn : j.val = n := by omega
      rw [hjn, loweringString_end hv]
  · rcases j with ⟨j, hj⟩
    cases j with
    | zero => simp [hb, hv.lie_e]
    | succ j =>
      simp only [hb, loweringString_e_succ hv, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel, basisVector]
      rw [dite_eq_left (by omega)]
      congr 1
      ring

section Operators

variable (k M)
omit [LieRingModule (Model k) M] [LieModule k (Model k) M]

def operatorAction (e f h : Module.End k M) : Model k →ₗ[k] Module.End k M where
  toFun x := x.val 0 1 • e + x.val 1 0 • f + x.val 0 0 • h
  map_add' x y := by
    change (x.val 0 1 + y.val 0 1) • e + (x.val 1 0 + y.val 1 0) • f +
      (x.val 0 0 + y.val 0 0) • h = _
    simp only [add_smul]
    abel
  map_smul' a x := by
    change (a * x.val 0 1) • e + (a * x.val 1 0) • f + (a * x.val 0 0) • h = _
    simp only [smul_add, mul_smul, RingHom.id_apply]

@[simp] theorem operatorAction_e (e f h : Module.End k M) :
    operatorAction k M e f h (E k) = e := by simp [operatorAction, E, Matrix.single]

@[simp] theorem operatorAction_f (e f h : Module.End k M) :
    operatorAction k M e f h (F k) = f := by simp [operatorAction, F, Matrix.single]

@[simp] theorem operatorAction_h (e f h : Module.End k M) :
    operatorAction k M e f h (H k) = h := by simp [operatorAction, H, Matrix.single]

/-- A representation of the actual matrix algebra from three operators obeying
the three relations. No nonzero-operator condition excludes the trivial model. -/
def representationOfOperators (e f h : Module.End k M)
    (he : ⁅h, e⁆ = (2 : k) • e) (hf : ⁅h, f⁆ = (-2 : k) • f)
    (hef : ⁅e, f⁆ = h) : Model k →ₗ⁅k⁆ Module.End k M where
  __ := operatorAction k M e f h
  map_lie' {x y} := by
    have hem : ⁅H k, E k⁆ = (2 : k) • E k := (sl2_relations k).1
    have hfm : ⁅H k, F k⁆ = (-2 : k) • F k := (sl2_relations k).2.1
    have hefm : ⁅E k, F k⁆ = H k := (sl2_relations k).2.2
    have ehm : ⁅E k, H k⁆ = -((2 : k) • E k) := by rw [← lie_skew, hem]
    have fhm : ⁅F k, H k⁆ = -((-2 : k) • F k) := by rw [← lie_skew, hfm]
    have fem : ⁅F k, E k⁆ = -H k := by rw [← lie_skew, hefm]
    have eh : ⁅e, h⁆ = -((2 : k) • e) := by rw [← lie_skew, he]
    have fh : ⁅f, h⁆ = -((-2 : k) • f) := by rw [← lie_skew, hf]
    have fe : ⁅f, e⁆ = -h := by rw [← lie_skew, hef]
    change operatorAction k M e f h ⁅x, y⁆ =
      ⁅operatorAction k M e f h x, operatorAction k M e f h y⁆
    conv_lhs => rw [sl2_expansion k x, sl2_expansion k y]
    conv_rhs => rw [sl2_expansion k x, sl2_expansion k y]
    simp only [add_lie, lie_add, smul_lie, lie_smul, map_add, map_smul,
      sl2_e, sl2_f, sl2_h, lie_self, hem, hfm, hefm, ehm, fhm, fem,
      map_zero, map_neg, operatorAction_e, operatorAction_f, operatorAction_h,
      he, hf, hef, eh, fh, fe]

end Operators

section PolynomialModel

open MvPolynomial

variable (k)

def monomialIndex (n : ℕ) (j : Fin (n + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (n - j.val) + Finsupp.single 1 j.val

@[simp] theorem monomialIndex_zero (n : ℕ) (j : Fin (n + 1)) :
    monomialIndex n j 0 = n - j.val := by simp [monomialIndex]

@[simp] theorem monomialIndex_one (n : ℕ) (j : Fin (n + 1)) :
    monomialIndex n j 1 = j.val := by simp [monomialIndex]

theorem monomialIndex_injective (n : ℕ) : Function.Injective (monomialIndex n) := by
  intro i j hij
  apply Fin.ext
  simpa using congrArg (fun d => d 1) hij

def rawMonomial (n : ℕ) (j : Fin (n + 1)) : MvPolynomial (Fin 2) k :=
  X 0 ^ (n - j.val) * X 1 ^ j.val

theorem rawMonomial_eq (n : ℕ) (j : Fin (n + 1)) :
    rawMonomial k n j = monomial (monomialIndex n j) (1 : k) := by
  simp [rawMonomial, X_pow_eq_monomial, monomial_mul_monomial, monomialIndex]

def rawVector (n : ℕ) (j : Fin (n + 1)) : Homogeneous k n :=
  ⟨rawMonomial k n j, by
    have := (isHomogeneous_X_pow (R := k) (0 : Fin 2) (n - j.val)).mul
      (isHomogeneous_X_pow (R := k) (1 : Fin 2) j.val)
    change (rawMonomial k n j).IsHomogeneous n
    simpa only [rawMonomial, Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)] using this⟩

theorem rawVector_linearIndependent (n : ℕ) :
    LinearIndependent k (rawVector k n) := by
  apply LinearIndependent.of_comp (Homogeneous k n).subtype
  simpa only [Function.comp_def, rawVector, rawMonomial_eq, coe_basisMonomials, Submodule.subtype_apply] using
    (basisMonomials (Fin 2) k).linearIndependent.comp (monomialIndex n)
      (monomialIndex_injective n)

theorem rawVector_span (n : ℕ) :
    ⊤ ≤ Submodule.span k (Set.range (rawVector k n)) := by
  intro p hpTop
  clear hpTop
  obtain ⟨p, hp⟩ := p
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => exact Submodule.zero_mem _
  | add p q hp hq ihp ihq => exact Submodule.add_mem _ ihp ihq
  | monomial d r hr =>
    have hd : d 0 + d 1 = n := by
      have hd : d.degree = n := by
        rw [Finsupp.degree_eq_weight_one]
        exact hr
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
    let j : Fin (n + 1) := ⟨d 1, by omega⟩
    have hindex : monomialIndex n j = d := by
      ext i
      fin_cases i <;> simp [monomialIndex, j]
      omega
    have hm : (⟨monomial d r, isWeightedHomogeneous_monomial _ _ _ hr⟩ : Homogeneous k n) = r • rawVector k n j := by
      apply Subtype.ext
      simp [rawVector, rawMonomial_eq, hindex, smul_monomial]
    rw [hm]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl⟩)

def rawPolynomialBasis (n : ℕ) : Basis (Fin (n + 1)) k (Homogeneous k n) :=
  Basis.mk (rawVector_linearIndependent k n) (rawVector_span k n)

@[simp] theorem rawPolynomialBasis_apply (n : ℕ) (j : Fin (n + 1)) :
    rawPolynomialBasis k n j = rawVector k n j := Basis.mk_apply _ _ _

def normalization (n : ℕ) (j : ℕ) : k :=
  (n.factorial : k) / ((n - j).factorial : k)

theorem normalization_ne_zero [CharZero k] (n j : ℕ) : normalization k n j ≠ 0 := by
  apply div_ne_zero <;> exact_mod_cast Nat.factorial_ne_zero _

def polynomialBasis [CharZero k] (n : ℕ) : Basis (Fin (n + 1)) k (Homogeneous k n) :=
  (rawPolynomialBasis k n).isUnitSMul (fun j =>
    isUnit_iff_ne_zero.mpr (normalization_ne_zero k n j.val))

theorem polynomialBasis_apply [CharZero k] (n : ℕ) (j : Fin (n + 1)) :
    (polynomialBasis k n j).val = normalizedMonomial k n j := by
  simp [polynomialBasis, Basis.isUnitSMul_apply, rawVector, rawMonomial,
    normalizedMonomial, normalization]

/-- Each vector field X_i ∂_j preserves total degree, including degree zero. -/
theorem operator_mem (n : ℕ) (i j : Fin 2) (p : Homogeneous k n) :
    (X i * pderiv j p.val).IsHomogeneous n := by
  cases n with
  | zero =>
    have hp : p.val.IsHomogeneous 0 := p.property
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp, pderiv_C, mul_zero]
    exact isHomogeneous_zero (R := k) (σ := Fin 2) _
  | succ n =>
    have hp := (isHomogeneous_X (R := k) i).mul
      (MvPolynomial.IsHomogeneous.pderiv (i := j) p.property)
    simpa [Nat.add_comm] using hp

def polynomialOperator (n : ℕ) (i j : Fin 2) : Module.End k (Homogeneous k n) where
  toFun p := ⟨X i * pderiv j p.val, operator_mem k n i j p⟩
  map_add' p q := by apply Subtype.ext; simp [mul_add]
  map_smul' a p := by apply Subtype.ext; simp

theorem polynomialOperator_lie (n : ℕ) (i j r s : Fin 2) :
    ⁅polynomialOperator k n i j, polynomialOperator k n r s⁆ =
      (if j = r then polynomialOperator k n i s else 0) -
      (if s = i then polynomialOperator k n r j else 0) := by
  have hcalc (p : Homogeneous k n) :
      X i * pderiv j (X r * pderiv s p.val) -
        X r * pderiv s (X i * pderiv j p.val) =
        (if j = r then X i * pderiv s p.val else 0) -
        (if s = i then X r * pderiv j p.val else 0) := by
    rw [pderiv_mul, pderiv_mul, pderiv_comm j s]
    by_cases hjr : j = r <;> by_cases hsi : s = i <;>
      simp [pderiv_X, hjr, hsi, eq_comm] <;> ring
  by_cases hjr : j = r <;> by_cases hsi : s = i
  all_goals
    simp only [hjr, hsi, ↓reduceIte] at hcalc ⊢
    ext p : 1
    exact Subtype.ext (hcalc p)

def polynomialE (n : ℕ) := polynomialOperator k n 0 1
def polynomialF (n : ℕ) := polynomialOperator k n 1 0
def polynomialH (n : ℕ) := polynomialOperator k n 0 0 - polynomialOperator k n 1 1

theorem polynomial_relations (n : ℕ) :
    ⁅polynomialH k n, polynomialE k n⁆ = (2 : k) • polynomialE k n ∧
    ⁅polynomialH k n, polynomialF k n⁆ = (-2 : k) • polynomialF k n ∧
    ⁅polynomialE k n, polynomialF k n⁆ = polynomialH k n := by
  have general {V : Type u} [AddCommGroup V] [Module k V]
      (a b e f : Module.End k V)
      (hae : ⁅a, e⁆ = e) (hbe : ⁅b, e⁆ = -e)
      (haf : ⁅a, f⁆ = -f) (hbf : ⁅b, f⁆ = f) (hef : ⁅e, f⁆ = a - b) :
      ⁅a - b, e⁆ = (2 : k) • e ∧ ⁅a - b, f⁆ = (-2 : k) • f ∧ ⁅e, f⁆ = a - b := by
    refine ⟨?_, ?_, hef⟩
    · simp [sub_lie, hae, hbe, two_smul]
    · simp [sub_lie, haf, hbf, neg_smul, two_smul]
      abel
  apply general (polynomialOperator k n 0 0) (polynomialOperator k n 1 1)
    (polynomialE k n) (polynomialF k n)
  · change ⁅polynomialOperator k n 0 0, polynomialOperator k n 0 1⁆ = _
    refine (polynomialOperator_lie k n 0 0 0 1).trans ?_
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    exact sub_zero (polynomialOperator k n 0 1)
  · change ⁅polynomialOperator k n 1 1, polynomialOperator k n 0 1⁆ = _
    refine (polynomialOperator_lie k n 1 1 0 1).trans ?_
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    exact zero_sub (polynomialOperator k n 0 1)
  · change ⁅polynomialOperator k n 0 0, polynomialOperator k n 1 0⁆ = _
    refine (polynomialOperator_lie k n 0 0 1 0).trans ?_
    simp only [show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte]
    exact zero_sub (polynomialOperator k n 1 0)
  · change ⁅polynomialOperator k n 1 1, polynomialOperator k n 1 0⁆ = _
    refine (polynomialOperator_lie k n 1 1 1 0).trans ?_
    simp only [show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte]
    exact sub_zero (polynomialOperator k n 1 0)
  · exact polynomialOperator_lie k n 0 1 1 0

def polynomialRepresentation (n : ℕ) :
    Model k →ₗ⁅k⁆ Module.End k (Homogeneous k n) :=
  representationOfOperators k (Homogeneous k n) (polynomialE k n)
    (polynomialF k n) (polynomialH k n)
    (polynomial_relations k n).1 (polynomial_relations k n).2.1
    (polynomial_relations k n).2.2

instance polynomialLieRingModule (n : ℕ) : LieRingModule (Model k) (Homogeneous k n) :=
  LieRingModule.compLieHom (Homogeneous k n) (polynomialRepresentation k n)

instance polynomialLieModule (n : ℕ) : LieModule k (Model k) (Homogeneous k n) :=
  LieModule.compLieHom (Homogeneous k n) (polynomialRepresentation k n)

@[simp] theorem polynomial_e_apply (n : ℕ) (p : Homogeneous k n) :
    (⁅E k, p⁆).val = X 0 * pderiv 1 p.val := by
  change ((operatorAction k (Homogeneous k n) (polynomialE k n)
    (polynomialF k n) (polynomialH k n) (E k)) p).val = _
  rw [operatorAction_e]
  rfl

@[simp] theorem polynomial_f_apply (n : ℕ) (p : Homogeneous k n) :
    (⁅F k, p⁆).val = X 1 * pderiv 0 p.val := by
  change ((operatorAction k (Homogeneous k n) (polynomialE k n)
    (polynomialF k n) (polynomialH k n) (F k)) p).val = _
  rw [operatorAction_f]
  rfl

@[simp] theorem polynomial_h_apply (n : ℕ) (p : Homogeneous k n) :
    (⁅H k, p⁆).val = X 0 * pderiv 0 p.val - X 1 * pderiv 1 p.val := by
  change ((operatorAction k (Homogeneous k n) (polynomialE k n)
    (polynomialF k n) (polynomialH k n) (H k)) p).val = _
  rw [operatorAction_h]
  rfl

theorem normalization_eq_descFactorial [CharZero k] (n j : ℕ) (hj : j ≤ n) :
    normalization k n j = (n.descFactorial j : k) := by
  unfold normalization
  apply (div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero (n - j))).mpr
  exact_mod_cast (Nat.factorial_mul_descFactorial hj).symm.trans (mul_comm _ _)

@[simp] theorem normalization_zero [CharZero k] (n : ℕ) : normalization k n 0 = 1 := by
  rw [normalization_eq_descFactorial k n 0 (Nat.zero_le n)]
  simp

theorem normalization_succ [CharZero k] (n j : ℕ) (hj : j < n) :
    normalization k n (j + 1) = ((n - j : ℕ) : k) * normalization k n j := by
  rw [normalization_eq_descFactorial k n (j + 1) (by omega),
    normalization_eq_descFactorial k n j (by omega), Nat.descFactorial_succ, Nat.cast_mul]

theorem polynomialBasis_zero [CharZero k] (n : ℕ) :
    polynomialBasis k n 0 = rawVector k n 0 := by
  apply Subtype.ext
  rw [polynomialBasis_apply]
  change normalization k n 0 • (X 0 ^ (n - 0) * X 1 ^ 0) = _
  simp [rawVector, rawMonomial]

theorem polynomial_highest [CharZero k] (n : ℕ) :
    (standardTriple k).HasPrimitiveVectorWith (rawVector k n 0) (n : k) where
  ne_zero := (rawVector_linearIndependent k n).ne_zero 0
  lie_e := by
    apply Subtype.ext
    rw [polynomial_e_apply]
    simp [rawVector, rawMonomial, pderiv_X]
  lie_h := by
    apply Subtype.ext
    rw [polynomial_h_apply]
    have hv : (rawVector k n 0).val = X 0 ^ n := by
      simp [rawVector, rawMonomial]
    change X 0 * pderiv 0 (rawVector k n 0).val -
      X 1 * pderiv 1 (rawVector k n 0).val = (n : k) • (rawVector k n 0).val
    rw [hv]
    simp only [pderiv_pow, pderiv_X, Pi.single_apply, show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte,
      mul_one, mul_zero, zero_mul, sub_zero]
    by_cases hn : n = 0
    · subst n; simp
    · rw [MvPolynomial.smul_eq_C_mul]
      have hpow : X (R := k) (0 : Fin 2) ^ n = X 0 ^ (n - 1) * X 0 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      simp only [map_natCast]
      ring

/-- Differentiation of the normalized monomials gives exactly the unit-step f
action. The descending factorial identity supplies the required normalization. -/
theorem polynomial_f_basis_succ [CharZero k] (n j : ℕ) (hj : j < n) :
    ⁅F k, polynomialBasis k n ⟨j, by omega⟩⁆ = polynomialBasis k n ⟨j + 1, by omega⟩ := by
  apply Subtype.ext
  rw [polynomial_f_apply, polynomialBasis_apply, polynomialBasis_apply]
  change X 1 * pderiv 0 (normalization k n j • (X 0 ^ (n - j) * X 1 ^ j)) =
    normalization k n (j + 1) • (X 0 ^ (n - (j + 1)) * X 1 ^ (j + 1))
  rw [normalization_succ k n j hj]
  rw [(pderiv (R := k) (0 : Fin 2)).map_smul (normalization k n j)]
  simp only [pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply, show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte,
    mul_one, mul_zero, add_zero]
  have hsub : n - j - 1 = n - (j + 1) := by omega
  rw [hsub]
  simp only [smul_eq_C_mul, map_mul, map_natCast, pow_succ]
  ring

theorem polynomialBasis_eq_string [CharZero k] (n : ℕ) (j : Fin (n + 1)) :
    polynomialBasis k n j = loweringString (k := k) (Homogeneous k n) (rawVector k n 0) j.val := by
  obtain ⟨j, hj⟩ := j
  induction j with
  | zero => exact polynomialBasis_zero k n
  | succ j ih =>
    rw [loweringString_succ, ← ih (by omega)]
    exact (polynomial_f_basis_succ k n j (by omega)).symm

theorem polynomialBasis_isStandard [CharZero k] (n : ℕ) :
    IsStandardBasis (polynomialBasis k n) := by
  let : FiniteDimensional k (Homogeneous k n) := Module.Finite.of_basis (polynomialBasis k n)
  exact standardBasis_of_string (polynomial_highest k n) (polynomialBasis k n)
    (polynomialBasis_eq_string k n)

theorem polynomial_spec : polynomialExpected.{u} := by
  intro k _ _ _ n
  refine ⟨polynomialLieRingModule k n, polynomialLieModule k n, polynomialBasis k n,
    polynomialBasis_isStandard k n, polynomialBasis_apply k n, ?_, ?_⟩
  · intro p
    exact ⟨polynomial_e_apply k n p, polynomial_f_apply k n p, polynomial_h_apply k n p⟩
  · exact isIrreducible_of_standardBasis (polynomialBasis k n) (polynomialBasis_isStandard k n)

/-- The standard coefficient-space model L_n, obtained by coordinates in the
normalized polynomial basis. -/
def standardRepresentation [CharZero k] (n : ℕ) :
    Model k →ₗ⁅k⁆ Module.End k (Fin (n + 1) → k) :=
  (polynomialBasis k n).equivFun.lieConj.toLieHom.comp (polynomialRepresentation k n)

instance standardLieRingModule [CharZero k] (n : ℕ) :
    LieRingModule (Model k) (Fin (n + 1) → k) :=
  LieRingModule.compLieHom (Fin (n + 1) → k) (standardRepresentation k n)

instance standardLieModule [CharZero k] (n : ℕ) :
    LieModule k (Model k) (Fin (n + 1) → k) :=
  LieModule.compLieHom (Fin (n + 1) → k) (standardRepresentation k n)

def standardPolynomialEquiv [CharZero k] (n : ℕ) :
    Homogeneous k n ≃ₗ⁅k, Model k⁆ (Fin (n + 1) → k) where
  __ := (polynomialBasis k n).equivFun
  map_lie' {x p} := by
    change (polynomialBasis k n).equivFun ((polynomialRepresentation k n x) p) =
      ((polynomialBasis k n).equivFun.conj (polynomialRepresentation k n x))
        ((polynomialBasis k n).equivFun p)
    simp

theorem standardPolynomialEquiv_basis [CharZero k] (n : ℕ) (j : Fin (n + 1)) :
    standardPolynomialEquiv k n (polynomialBasis k n j) = Pi.basisFun k (Fin (n + 1)) j := by
  ext i
  change (polynomialBasis k n).equivFun (polynomialBasis k n j) i = _
  simp [Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]

theorem standardBasis_isStandard [CharZero k] (n : ℕ) :
    IsStandardBasis (Pi.basisFun k (Fin (n + 1))) := by
  let φ := standardPolynomialEquiv k n
  let b := polynomialBasis k n
  let c := Pi.basisFun k (Fin (n + 1))
  have hφ (j : Fin (n + 1)) : φ (b j) = c j := standardPolynomialEquiv_basis k n j
  have hφv (j : ℕ) : φ (basisVector b j) = basisVector c j := by
    simp only [basisVector]
    split_ifs <;> simp [hφ]
  have hb := polynomialBasis_isStandard k n
  intro j
  change ⁅H k, c j⁆ = _ ∧ ⁅F k, c j⁆ = _ ∧ ⁅E k, c j⁆ = _
  have hmap (x : Model k) (p : Homogeneous k n) : φ ⁅x, p⁆ = ⁅x, φ p⁆ :=
    φ.map_lie x p
  rw [← hφ j, ← hmap, ← hmap, ← hmap]
  exact ⟨by rw [(hb j).1, map_smul, hφ],
    by rw [(hb j).2.1, hφv], by rw [(hb j).2.2, map_smul, hφv]⟩

theorem models_spec : modelsExpected.{u} := by
  intro k _ _ _ n
  refine ⟨standardLieRingModule k n, standardLieModule k n, standardBasis_isStandard k n, ?_⟩
  exact isIrreducible_of_standardBasis (Pi.basisFun k (Fin (n + 1))) (standardBasis_isStandard k n)

theorem realization_spec : realizationExpected.{u,v} := by
  intro k _ _ _ M _ _ _ _ n b hb
  obtain ⟨φ, hφ⟩ := equivalence_spec k M (Homogeneous k n) n b (polynomialBasis k n)
    hb (polynomialBasis_isStandard k n)
  refine ⟨polynomialLieRingModule k n, polynomialLieModule k n, φ, ?_, ?_⟩
  · intro j
    rw [hφ j, polynomialBasis_apply]
  · intro p
    exact ⟨polynomial_e_apply k n p, polynomial_f_apply k n p, polynomial_h_apply k n p⟩

end PolynomialModel

end LieAlgebrasAndRepresentations.Sl2SimpleModules
