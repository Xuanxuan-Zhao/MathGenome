import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClebschGordan
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2SimpleModules
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompleteReducibility
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace LieAlgebrasAndRepresentations.ClebschGordan
open Module
open Specs.LieAlgebrasAndRepresentations.Sl2Model
open Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
open Specs.LieAlgebrasAndRepresentations.ClebschGordan
open Sl2SimpleModules
open scoped DirectSum TensorProduct

/-- The source's radical definition of semisimplicity holds for the actual
matrix algebra, rather than being an extra representation hypothesis. -/
lemma sl2_semisimple (k : Type u) [Field k] [CharZero k] :
    Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k (Model k) := by
  letI := sl2_simple k
  exact LieAlgebra.radical_eq_bot (R := k) (L := Model k)

lemma sl2_finite (k : Type u) [Field k] : FiniteDimensional k (Model k) :=
  (sl2Coordinates k).symm.finiteDimensional

theorem finite_standard_decomposition : finite_standard_decomposition_type.{u,v} := by
  intro k _ _ _ M _ _ _ _ _
  letI := sl2_finite k
  obtain ⟨S, hS, hsimp, hint⟩ := CompleteReducibility.finite_simple_decomposition
    k (Model k) M (sl2_semisimple k)
  refine ⟨S, hS, hint, ?_⟩
  intro W hW
  letI := hsimp W hW
  letI : Nontrivial W := (LieSubmodule.nontrivial_iff k (Model k) W).mp inferInstance
  obtain ⟨n, ⟨b, hb⟩, _⟩ := classification_spec k W
  exact ⟨n, b, hb⟩

section TensorWeights
variable {k : Type u} [Field k] [CharZero k]
variable {M : Type v} {N : Type w}
  [AddCommGroup M] [Module k M] [LieRingModule (Model k) M] [LieModule k (Model k) M]
  [AddCommGroup N] [Module k N] [LieRingModule (Model k) N] [LieModule k (Model k) N]
variable {m n : ℕ} (b : Basis (Fin (m + 1)) k M) (c : Basis (Fin (n + 1)) k N)

/-- The s-th diagonal in the tensor basis, for s ≤ min(m,n). -/
def diagonalTensor (s : ℕ) (hm : s ≤ m) (hn : s ≤ n) (i : Fin (s + 1)) : M ⊗[k] N :=
  b ⟨i.val, by omega⟩ ⊗ₜ[k] c ⟨s - i.val, by omega⟩

def diagonalSpace (s : ℕ) (hm : s ≤ m) (hn : s ≤ n) : Submodule k (M ⊗[k] N) :=
  Submodule.span k (Set.range (diagonalTensor b c s hm hn))

lemma diagonalTensor_linearIndependent (s : ℕ) (hm : s ≤ m) (hn : s ≤ n) :
    LinearIndependent k (diagonalTensor b c s hm hn) := by
  let f : Fin (s + 1) → Fin (m + 1) × Fin (n + 1) :=
    fun i => (⟨i.val, by omega⟩, ⟨s - i.val, by omega⟩)
  have hf : Function.Injective f := by
    intro i j h
    exact Fin.ext (congrArg (fun p : Fin (m + 1) × Fin (n + 1) => p.1.val) h)
  change LinearIndependent k (fun i : Fin (s + 1) =>
    b ⟨i.val, by omega⟩ ⊗ₜ[k] c ⟨s - i.val, by omega⟩)
  have h := (b.tensorProduct c).linearIndependent.comp f hf
  simpa only [Function.comp_def, Basis.tensorProduct_apply', f] using h

lemma diagonalSpace_finrank (s : ℕ) (hm : s ≤ m) (hn : s ≤ n) :
    finrank k (diagonalSpace b c s hm hn) = s + 1 := by
  exact (finrank_span_eq_card (diagonalTensor_linearIndependent b c s hm hn)).trans
    (Fintype.card_fin (s + 1))

lemma diagonalSpace_weight (hb : IsStandardBasis b) (hc : IsStandardBasis c)
    (s : ℕ) (hm : s ≤ m) (hn : s ≤ n) :
    diagonalSpace b c s hm hn ≤
      (LieModule.toEnd k (Model k) (M ⊗[k] N) (H k)).eigenspace
        ((m : k) + (n : k) - 2 * (s : k)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply Module.End.mem_eigenspace_iff.mpr
  change ⁅H k, diagonalTensor b c s hm hn i⁆ = _
  simp only [diagonalTensor, TensorProduct.LieModule.lie_tmul_right,
    (hb _).1, (hc _).1, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rw [← add_smul]
  congr 1
  rw [Nat.cast_sub (by omega : i.val ≤ s)]
  ring

/-- Raising takes the (s+1)-st tensor diagonal into the s-th diagonal. -/
lemma raising_diagonal (hb : IsStandardBasis b) (hc : IsStandardBasis c)
    (s : ℕ) (hm : s + 1 ≤ m) (hn : s + 1 ≤ n) :
    ∀ v ∈ diagonalSpace b c (s + 1) hm hn,
      ⁅E k, v⁆ ∈ diagonalSpace b c s (by omega) (by omega) := by
  let D := diagonalSpace b c s (by omega : s ≤ m) (by omega : s ≤ n)
  have hmem (i : Fin (s + 1)) : diagonalTensor b c s (by omega) (by omega) i ∈ D :=
    Submodule.subset_span ⟨i, rfl⟩
  have hgen (i : Fin (s + 1 + 1)) :
      ⁅E k, diagonalTensor b c (s + 1) hm hn i⁆ ∈ D := by
    simp only [diagonalTensor, TensorProduct.LieModule.lie_tmul_right,
      (hb _).2.2, (hc _).2.2, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    apply D.add_mem
    · by_cases hi : i.val = 0
      · simp [hi]
      · apply D.smul_mem
        have heq : basisVector b (i.val - 1) ⊗ₜ[k] c ⟨s + 1 - i.val, by omega⟩ =
            diagonalTensor b c s (by omega) (by omega) ⟨i.val - 1, by omega⟩ := by
          simp only [basisVector, dite_eq_left (by omega : i.val - 1 < m + 1),
            diagonalTensor]
          congr 2
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [heq]
        exact hmem _
    · by_cases hi : i.val = s + 1
      · simp [hi]
      · apply D.smul_mem
        have heq : b ⟨i.val, by omega⟩ ⊗ₜ[k] basisVector c (s + 1 - i.val - 1) =
            diagonalTensor b c s (by omega) (by omega) ⟨i.val, by omega⟩ := by
          simp only [basisVector, dite_eq_left (by omega : s + 1 - i.val - 1 < n + 1),
            diagonalTensor]
          congr 2
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [heq]
        exact hmem _
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨i, rfl⟩ := hv; exact hgen i
  | zero => simpa using D.zero_mem
  | add v w hv hw ihv ihw => simpa only [lie_add] using D.add_mem ihv ihw
  | smul a v hv ih => simpa only [lie_smul] using D.smul_mem a ih

/-- There are s+1 source vectors and only s possible raised vectors, so
there is a nonzero highest vector of weight m+n-2s. -/
lemma tensor_highest_vector (hb : IsStandardBasis b) (hc : IsStandardBasis c)
    (s : ℕ) (hm : s ≤ m) (hn : s ≤ n) :
    ∃ v : M ⊗[k] N,
      (standardTriple k).HasPrimitiveVectorWith v ((m + n - 2 * s : ℕ) : k) := by
  letI := b.finiteDimensional_of_finite
  letI := c.finiteDimensional_of_finite
  have hex : ∃ v ∈ diagonalSpace b c s hm hn, v ≠ 0 ∧ ⁅E k, v⁆ = 0 := by
    cases s with
    | zero =>
      refine ⟨diagonalTensor b c 0 hm hn 0, Submodule.subset_span ⟨0, rfl⟩,
        (diagonalTensor_linearIndependent b c 0 hm hn).ne_zero 0, ?_⟩
      simp [diagonalTensor, TensorProduct.LieModule.lie_tmul_right,
        (hb (0 : Fin (m + 1))).2.2, (hc (0 : Fin (n + 1))).2.2]
    | succ s =>
      let D := diagonalSpace b c (s + 1) hm hn
      let D' := diagonalSpace b c s (by omega : s ≤ m) (by omega : s ≤ n)
      let e : D →ₗ[k] D' :=
        ((LieModule.toEnd k (Model k) (M ⊗[k] N) (E k)).comp D.subtype).codRestrict D'
          (fun v => raising_diagonal b c hb hc s hm hn v v.property)
      have hdim : finrank k D' < finrank k D := by
        dsimp [D, D']
        rw [diagonalSpace_finrank, diagonalSpace_finrank]
        omega
      obtain ⟨v, hv, hv0⟩ := (LinearMap.ker e).ne_bot_iff.mp
        (LinearMap.ker_ne_bot_of_finrank_lt hdim)
      refine ⟨v.val, v.property, ?_, ?_⟩
      · exact fun h => hv0 (Subtype.ext h)
      · exact congrArg Subtype.val (LinearMap.mem_ker.mp hv)
  obtain ⟨v, hv, hv0, he⟩ := hex
  refine ⟨v, hv0, ?_, he⟩
  have hw := diagonalSpace_weight b c hb hc s hm hn hv
  rw [Module.End.mem_eigenspace_iff] at hw
  change ⁅H k, v⁆ = ((m : k) + (n : k) - 2 * (s : k)) • v at hw
  simpa only [Nat.cast_sub (by omega : 2 * s ≤ m + n), Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat] using hw

end TensorWeights

section Strings
variable {k : Type u} [Field k] [CharZero k]
variable {M : Type v} [AddCommGroup M] [Module k M]
  [LieRingModule (Model k) M] [LieModule k (Model k) M] [FiniteDimensional k M]
variable {r : ℕ} {v : M} (hv : (standardTriple k).HasPrimitiveVectorWith v (r : k))

/-- The independent lowering string is a basis of its invariant span. -/
def stringBasis : Basis (Fin (r + 1)) k (stringSubmodule hv) :=
  Basis.span (loweringString_linearIndependent hv)

@[simp] lemma stringBasis_val (j : Fin (r + 1)) :
    (stringBasis hv j : M) = loweringString (k := k) M v j.val :=
  Basis.coe_span_apply _ _

lemma stringBasis_standard : IsStandardBasis (stringBasis hv) := by
  intro j
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · change ⁅H k, (stringBasis hv j : M)⁆ =
      ((r : k) - 2 * (j.val : k)) • (stringBasis hv j : M)
    simpa only [stringBasis_val] using loweringString_h hv j.val
  · change ⁅F k, (stringBasis hv j : M)⁆ =
      (basisVector (stringBasis hv) (j.val + 1)).val
    rw [stringBasis_val, ← loweringString_succ]
    simp only [basisVector]
    split_ifs with hj
    · exact (stringBasis_val hv ⟨j.val + 1, hj⟩).symm
    · have hjr : j.val = r := by omega
      rw [hjr, loweringString_end hv]
      rfl
  · change ⁅E k, (stringBasis hv j : M)⁆ =
      ((j.val : k) * ((r : k) - (j.val : k) + 1)) •
        (basisVector (stringBasis hv) (j.val - 1)).val
    rw [stringBasis_val]
    rcases j with ⟨j, hj⟩
    cases j with
    | zero => simp [hv.lie_e]
    | succ j =>
      rw [loweringString_e_succ hv]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, basisVector,
        dite_eq_left (by omega : j < r + 1), stringBasis_val]
      congr 1
      ring

/-- Twice the usual Casimir, written directly as an endomorphism. -/
def casimirOperator : Module.End k M :=
  let h := LieModule.toEnd k (Model k) M (H k)
  let e := LieModule.toEnd k (Model k) M (E k)
  let f := LieModule.toEnd k (Model k) M (F k)
  h * h + (2 : k) • h + (4 : k) • (f * e)

include hv in
lemma casimir_loweringString (j : ℕ) :
    casimirOperator (k := k) (M := M) (loweringString (k := k) M v j) =
      ((r : k) * ((r : k) + 2)) • loweringString (k := k) M v j := by
  change ⁅H k, ⁅H k, loweringString (k := k) M v j⁆⁆ +
    (2 : k) • ⁅H k, loweringString (k := k) M v j⁆ +
    (4 : k) • ⁅F k, ⁅E k, loweringString (k := k) M v j⁆⁆ = _
  cases j with
  | zero =>
    simp only [loweringString_zero, hv.lie_h, hv.lie_e, lie_smul, lie_zero,
      smul_zero, add_zero, smul_smul, ← add_smul]
    congr 1
    ring
  | succ j =>
    rw [loweringString_h hv, lie_smul, loweringString_h hv,
      loweringString_e_succ hv, lie_smul,
      ← loweringString_succ]
    simp only [smul_smul, ← add_smul, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

lemma stringSubmodule_le_casimir_eigenspace :
    (stringSubmodule hv).toSubmodule ≤
      (casimirOperator (k := k) (M := M)).eigenspace ((r : k) * ((r : k) + 2)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr (casimir_loweringString hv j.val)

end Strings

/-- The Casimir eigenvalues for the proposed summands are distinct in every
characteristic-zero field. -/
lemma casimir_parameters_injective (k : Type u) [Field k] [CharZero k] (m n : ℕ) :
    Function.Injective (fun j : Fin (min m n + 1) =>
      ((m + n - 2 * j.val : ℕ) : k) * (((m + n - 2 * j.val : ℕ) : k) + 2)) := by
  intro i j hij
  have heq : (m + n - 2 * i.val) * (m + n - 2 * i.val + 2) =
      (m + n - 2 * j.val) * (m + n - 2 * j.val + 2) := by
    change ((m + n - 2 * i.val : ℕ) : k) * (((m + n - 2 * i.val : ℕ) : k) + 2) =
      ((m + n - 2 * j.val : ℕ) : k) * (((m + n - 2 * j.val : ℕ) : k) + 2) at hij
    exact_mod_cast hij
  have hr : m + n - 2 * i.val = m + n - 2 * j.val := by nlinarith
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have hminm := min_le_left m n
  have hminn := min_le_right m n
  omega

lemma sum_string_dimensions_aux (t a : ℕ) (ha : 2 * a ≤ t) :
    (∑ j ∈ Finset.range (a + 1), (t - 2 * j + 1)) = (a + 1) * (t + 1 - a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 := Nat.sub_add_cancel (show a ≤ t + 1 by omega)
    have h2 := Nat.sub_add_cancel (show a + 1 ≤ t + 1 by omega)
    have h3 := Nat.sub_add_cancel ha
    nlinarith

lemma sum_string_dimensions (m n : ℕ) :
    (∑ j : Fin (min m n + 1), (m + n - 2 * j.val + 1)) = (m + 1) * (n + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => m + n - 2 * j + 1), sum_string_dimensions_aux (m + n) (min m n)
    (by omega)]
  by_cases h : m ≤ n
  · rw [min_eq_left h]
    have : m + n + 1 - m = n + 1 := by omega
    rw [this]
  · rw [min_eq_right (by omega : n ≤ m)]
    have : m + n + 1 - n = m + 1 := by omega
    rw [this, Nat.mul_comm]

/-- The lowering strings fill the entire tensor product. -/
theorem clebsch_gordan : clebsch_gordan_type.{u,v,w} := by
  intro k _ _ _ M N _ _ _ _ _ _ _ _ m n b c hb hc
  classical
  letI := b.finiteDimensional_of_finite
  letI := c.finiteDimensional_of_finite
  have hvec (j : Fin (min m n + 1)) : ∃ v : M ⊗[k] N,
      (standardTriple k).HasPrimitiveVectorWith v ((m + n - 2 * j.val : ℕ) : k) :=
    tensor_highest_vector b c hb hc j.val
      (by have := j.isLt; omega) (by have := j.isLt; omega)
  choose v hv using hvec
  let W (j : Fin (min m n + 1)) := stringSubmodule (hv j)
  have hle (j : Fin (min m n + 1)) : (W j).toSubmodule ≤
      (casimirOperator (k := k) (M := M ⊗[k] N)).eigenspace
        (((m + n - 2 * j.val : ℕ) : k) * (((m + n - 2 * j.val : ℕ) : k) + 2)) :=
    stringSubmodule_le_casimir_eigenspace (hv j)
  have hind : iSupIndep (fun j => (W j).toSubmodule) :=
    ((casimirOperator (k := k) (M := M ⊗[k] N)).eigenspaces_iSupIndep.comp
      (casimir_parameters_injective k m n)).mono hle
  have hdim : finrank k (DirectSum (Fin (min m n + 1)) (fun j => ↥(W j))) = finrank k (M ⊗[k] N) := by
    rw [Module.finrank_directSum, Module.finrank_tensorProduct]
    have hj (j : Fin (min m n + 1)) : finrank k (W j) = m + n - 2 * j.val + 1 :=
      (Module.finrank_eq_card_basis (stringBasis (hv j))).trans (Fintype.card_fin _)
    simp_rw [hj]
    rw [sum_string_dimensions, Module.finrank_eq_card_basis b,
      Module.finrank_eq_card_basis c, Fintype.card_fin, Fintype.card_fin]
  have hinj : Function.Injective (DirectSum.coeLinearMap (fun j => (W j).toSubmodule)) :=
    hind.dfinsupp_lsum_injective
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨W, ⟨hinj, hsurj⟩, ?_⟩
  intro j
  exact ⟨stringBasis (hv j), stringBasis_standard (hv j)⟩

/-- Identify an internal sum of standard submodules with the direct sum of
the coordinate models constructed in the rank-one classification. -/
private theorem standardSummands_equiv {k : Type u} [Field k] [CharZero k]
    {M : Type v} [AddCommGroup M] [Module k M]
    [LieRingModule (Model k) M] [LieModule k (Model k) M]
    {ι : Type w} [DecidableEq ι] (W : ι → LieSubmodule k (Model k) M) (r : ι → ℕ)
    (hW : DirectSum.IsInternal (fun i => (W i).toSubmodule))
    (hb : ∀ i, ∃ b : Basis (Fin (r i + 1)) k (W i), IsStandardBasis b) :
    Nonempty (M ≃ₗ⁅k, Model k⁆ ⨁ i, (Fin (r i + 1) → k)) := by
  choose b hb using hb
  have component_equiv (i : ι) : Nonempty (W i ≃ₗ⁅k, Model k⁆ (Fin (r i + 1) → k)) := by
    obtain ⟨e, _⟩ := equivalence_spec k (W i) (Fin (r i + 1) → k) (r i)
      (b i) (Pi.basisFun k _) (hb i) (standardBasis_isStandard k (r i))
    exact ⟨e⟩
  let e (i : ι) := (component_equiv i).some
  let components : (⨁ i, W i) ≃ₗ⁅k, Model k⁆ ⨁ i, (Fin (r i + 1) → k) :=
    { DFinsupp.mapRange.linearEquiv (fun i => (e i).toLinearEquiv) with
      map_lie' := fun {x m} => by
        apply DFinsupp.ext
        intro i
        simpa only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
          DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_apply,
          DirectSum.lie_module_bracket_apply, LieModuleEquiv.coe_toLinearEquiv,
          LieModuleEquiv.coe_toLieModuleHom] using
          (e i).map_lie x (m i) }
  let sum : (⨁ i, W i) →ₗ[k] M := DirectSum.coeLinearMap (fun i => (W i).toSubmodule)
  have sum_of (i : ι) (m : W i) :
      sum (DirectSum.lieModuleOf k ι (Model k) (fun i => W i) i m) = m.val :=
    DirectSum.coeLinearMap_lof (fun i => (W i).toSubmodule) i m
  have sum_lie (x : Model k) (m : ⨁ i, W i) : sum ⁅x, m⁆ = ⁅x, sum m⁆ := by
    induction m using DirectSum.induction_on with
    | zero => simp
    | of i m =>
      let incl := DirectSum.lieModuleOf k ι (Model k) (fun i => W i) i
      change sum ⁅x, incl m⁆ = ⁅x, sum (incl m)⁆
      rw [← incl.map_lie]
      exact (sum_of i ⁅x, m⁆).trans (congrArg (fun v : M => ⁅x, v⁆) (sum_of i m)).symm
    | add m n hm hn => rw [lie_add, map_add, hm, hn, map_add, lie_add]
  let inclusion : (⨁ i, W i) ≃ₗ⁅k, Model k⁆ M :=
    { LinearEquiv.ofBijective sum hW with map_lie' := fun {x m} => sum_lie x m }
  exact ⟨inclusion.symm.trans components⟩

/-- In the finite-dimensional decomposition, each summand is an actual
coordinate model `L_(r i)`. -/
theorem finite_standard_decomposition_equiv (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (M : Type v) [AddCommGroup M] [Module k M]
    [LieRingModule (Model k) M] [LieModule k (Model k) M] [FiniteDimensional k M] :
    ∃ (S : Set (LieSubmodule k (Model k) M)) (r : S → ℕ), S.Finite ∧
      Nonempty (M ≃ₗ⁅k, Model k⁆ ⨁ i : S, (Fin (r i + 1) → k)) := by
  classical
  obtain ⟨S, hfinite, hsum, hb⟩ := finite_standard_decomposition k M
  choose r b hb using fun i : S => hb i.val i.property
  exact ⟨S, r, hfinite, standardSummands_equiv (fun i : S => i.val) r hsum
    (fun i => ⟨b i, hb i⟩)⟩

/-- Formula (3.8) for the upstream coordinate models of the simple modules. -/
theorem clebsch_gordan_equiv (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (m n : ℕ) :
    Nonempty (((Fin (m + 1) → k) ⊗[k] (Fin (n + 1) → k)) ≃ₗ⁅k, Model k⁆
      ⨁ j : Fin (min m n + 1), (Fin (m + n - 2 * j.val + 1) → k)) := by
  obtain ⟨W, hsum, hb⟩ := clebsch_gordan k (Fin (m + 1) → k) (Fin (n + 1) → k)
    m n (Pi.basisFun k _) (Pi.basisFun k _)
    (standardBasis_isStandard k m) (standardBasis_isStandard k n)
  exact standardSummands_equiv W (fun j => m + n - 2 * j.val) hsum hb

end LieAlgebrasAndRepresentations.ClebschGordan
