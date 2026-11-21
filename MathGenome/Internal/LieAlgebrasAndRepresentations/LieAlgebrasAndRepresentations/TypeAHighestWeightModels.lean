import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalMatrixCartans
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ComplexClassification
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompleteReducibility
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.TensorDualHom
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Batteries.Tactic.OpenPrivate

noncomputable section

open scoped Classical TensorProduct Matrix

namespace LieAlgebrasAndRepresentations.TypeAHighestWeightModels

open Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSpace_value)
open LieAlgebrasAndRepresentations.ClassicalRootsA

open private lieIdealOrderIso from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ComplexClassification

variable {n : ℕ}

local notation "matrixCoroot" => Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.coroot

private theorem direction_root (i j : Fin (n + 1)) :
    direction n (root n i j) = (j.val : ℝ) - (i.val : ℝ) := by
  change (root n i j (orderingElement n)).re = _
  simp only [root_apply, orderingElement, Matrix.diagonal_apply_eq,
    Complex.sub_re, Complex.neg_re, Complex.natCast_re]
  ring

theorem positive_roots : positive_roots_type := by
  intro n _
  constructor
  · intro α hα
    obtain ⟨i, j, hij, rfl⟩ := (root_set n α).mp hα
    rw [direction_root]
    exact sub_ne_zero.mpr (by exact_mod_cast (show j.val ≠ i.val from fun h => hij (Fin.ext h.symm)))
  · ext α
    constructor
    · rintro ⟨hα, hpos⟩
      obtain ⟨i, j, _, rfl⟩ := (root_set n α).mp hα
      rw [direction_root, sub_pos] at hpos
      exact ⟨i, j, by exact_mod_cast hpos, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨(root_set n _).mpr ⟨i, j, ne_of_lt hij, rfl⟩, by
        rw [direction_root, sub_pos]
        exact_mod_cast hij⟩

private theorem positive_iff (hn : 1 ≤ n) (α : Module.Dual ℂ (cartan n)) :
    α ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive (cartan n) (direction n)
      ↔ ∃ i j : Fin (n + 1), i < j ∧ α = root n i j :=
  Set.ext_iff.mp (positive_roots n hn).2 α

theorem simple_roots : simple_roots_type := by
  intro n hn
  ext α
  change (_ ∧ _) ↔ _
  constructor
  · rintro ⟨hα, hs⟩
    obtain ⟨i, j, hij, rfl⟩ := (positive_iff hn α).mp hα
    have hlt : i.val < j.val := hij
    let t : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have ht : j.val = i.val + 1 := by
      by_contra h
      have h₁ : i < t := Nat.lt_succ_self _
      have h₂ : t < j := by change i.val + 1 < j.val; omega
      exact hs _ ((positive_iff hn _).mpr ⟨i, t, h₁, rfl⟩)
        _ ((positive_iff hn _).mpr ⟨t, j, h₂, rfl⟩) (by unfold root; abel)
    let p : Fin n := ⟨i.val, by omega⟩
    exact ⟨p, congrArg₂ (root n) (Fin.ext rfl) (Fin.ext ht)⟩
  · rintro ⟨i, rfl⟩
    refine ⟨(positive_iff hn _).mpr ⟨i.castSucc, i.succ, Nat.lt_succ_self _, rfl⟩, ?_⟩
    intro β hβ γ hγ h
    obtain ⟨p, q, hpq, rfl⟩ := (positive_iff hn _).mp hβ
    obtain ⟨r, s, hrs, rfl⟩ := (positive_iff hn _).mp hγ
    have hit := congrArg (direction n) h
    rw [map_add, direction_root, direction_root, direction_root] at hit
    have hpq' : (p.val : ℝ) + 1 ≤ q.val := by exact_mod_cast (show p.val + 1 ≤ q.val from hpq)
    have hrs' : (r.val : ℝ) + 1 ≤ s.val := by exact_mod_cast (show r.val + 1 ≤ s.val from hrs)
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hit
    linarith

private theorem coroot_entry (i j a : Fin (n + 1)) :
    (matrixCoroot n i j).val.val a a = (if i = a then 1 else 0) - (if j = a then 1 else 0) := by
  change ((Matrix.single i i (1 : ℂ) - Matrix.single j j 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) a a = _
  simp [Matrix.single_apply]

private theorem omega_apply (k : ℕ) (h : cartan n) :
    omega n k h = ∑ i : Fin (n + 1), if i.val < k then h.val.val i i else 0 := by
  rw [omega, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

private theorem omega_one : omega n 1 = epsilon n 0 := by
  ext h
  change omega n 1 h = h.val.val 0 0
  simp [omega_apply, Fin.val_eq_zero_iff]

theorem fundamental_weights : fundamental_weights_type := by
  intro n k _ _ i
  rw [omega_apply]
  have he (a : Fin (n + 1)) :
      (if a.val < k then (matrixCoroot n i.castSucc i.succ).val.val a a else 0) =
      (if i.castSucc = a then (if a.val < k then (1 : ℂ) else 0) else 0) -
      (if i.succ = a then (if a.val < k then (1 : ℂ) else 0) else 0) := by
    rw [coroot_entry]
    split_ifs <;> simp_all
  simp_rw [he, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fin.val_castSucc, Fin.val_succ]
  by_cases h : i.val + 1 = k
  · simp [h, show i.val < k by omega]
  · by_cases h' : i.val + 1 < k
    · simp [h, h', show i.val < k by omega]
    · simp [h, h', show ¬ i.val < k by omega]

private theorem basis_lie (A : sl n) (i j : Fin (n + 1)) :
    ⁅A, vectorBasis n j⁆ i = A.val i j := by
  change (A.val *ᵥ vectorBasis n j) i = _
  rw [Pi.basisFun_apply, Matrix.mulVec_single_one]
  rfl

private theorem root_lie_basis (i j : Fin (n + 1)) (hij : i ≠ j) (l : Fin (n + 1)) :
    ⁅rootVector n i j hij, vectorBasis n l⁆ =
      if j = l then vectorBasis n i else 0 := by
  ext a
  rw [basis_lie]
  change Matrix.single i j (1 : ℂ) a l = _
  by_cases h : j = l <;> simp [Matrix.single_apply, Pi.basisFun_apply, Pi.single_apply, h, eq_comm]

private theorem cartan_lie_basis (h : cartan n) (j : Fin (n + 1)) :
    ⁅(h : sl n), vectorBasis n j⁆ = epsilon n j h • vectorBasis n j := by
  ext a
  rw [basis_lie]
  by_cases ha : a = j
  · subst a
    simp [Pi.basisFun_apply, show epsilon n j h = h.val.val j j from rfl]
  · simpa [Pi.basisFun_apply, Pi.single_apply, ha] using h.property ha

section WeightComponents

variable {L : Type} [LieRing L] [LieAlgebra ℂ L]
variable {V : Type} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

/-- Project onto individual weights by using their independence in the
quotient by the invariant subspace. -/
private theorem weight_components_mem (H : LieSubalgebra ℂ L) [LieRing.IsNilpotent H] (W : LieSubmodule ℂ L V)
    {ι : Type} (s : Finset ι) (χ : ι → H → ℂ)
    (hinj : Set.InjOn χ (s : Set ι)) (v : ι → V)
    (hv : ∀ i ∈ s, ∀ h : H, ⁅(h : L), v i⁆ = χ i h • v i)
    (hs : (∑ i ∈ s, v i) ∈ W) :
    ∀ i ∈ s, v i ∈ W := by
  let Q := V ⧸ W
  let p : V →ₗ⁅ℂ,L⁆ Q := LieSubmodule.Quotient.mk' W
  let P (i : {i // i ∈ s}) := (LieModule.weightSpace Q (χ i.val)).toSubmodule
  have hP : iSupIndep P := by
    have hi := (LieSubmodule.iSupIndep_toSubmodule.mpr
      (LieModule.iSupIndep_genWeightSpace ℂ H Q)).comp
      (show Function.Injective (fun i : {i // i ∈ s} => χ i.val) from
        fun i j he => Subtype.ext (hinj i.property j.property he))
    apply hi.mono
    exact fun i => LieModule.weightSpace_le_genWeightSpace Q (χ i.val)
  have hmem (i : {i // i ∈ s}) : p (v i.val) ∈ P i := by
    change p (v i.val) ∈ LieModule.weightSpace Q (χ i.val)
    rw [LieModule.mem_weightSpace]
    intro h
    change ⁅(h : L), p (v i.val)⁆ = χ i.val h • p (v i.val)
    rw [← LieModuleHom.map_lie, hv i.val i.property, map_smul]
  have hsum : (∑ i : {i // i ∈ s}, p (v i.val)) = 0 := by
    rw [← Finset.attach_eq_univ]
    calc
      _ = ∑ i ∈ s, p (v i) := Finset.sum_attach s (fun i => p (v i))
      _ = p (∑ i ∈ s, v i) := (map_sum p (fun i => v i) s).symm
      _ = 0 := (LieSubmodule.Quotient.mk_eq_zero W).mpr hs
  have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero P).mp hP Finset.univ
    (fun i => p (v i.val)) (fun i _ => hmem i) hsum
  intro i hi
  exact (LieSubmodule.Quotient.mk_eq_zero W).mp (hz ⟨i, hi⟩ (Finset.mem_univ _))

omit [LieAlgebra ℂ L] [LieModule ℂ L V] in
private theorem eq_top_of_basis_mem (W : LieSubmodule ℂ L V) {ι : Type}
    (b : Module.Basis ι ℂ V) (h : ∀ i, b i ∈ W) : W = ⊤ := by
  apply top_unique
  change (⊤ : Submodule ℂ V) ≤ W.toSubmodule
  rw [← b.span_eq]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr h)

end WeightComponents

private theorem root_eigen (h : cartan n) {i j : Fin (n + 1)} (hij : i ≠ j) :
    ⁅(h : sl n), rootVector n i j hij⁆ = root n i j h • rootVector n i j hij :=
  (LieAlgebrasAndRepresentations.mem_rootSpace _ _ _).mp (rootVector_mem i j hij) h

private theorem adjoint_simple (hn : 1 ≤ n) : IsSimpleOrder (LieIdeal ℂ (sl n)) := by
  letI := (ComplexClassification.models_simple (.A n hn)).2
  obtain ⟨e⟩ := ComplexClassification.classical_a n hn
  exact (lieIdealOrderIso (sl n) e).isSimpleOrder_iff.mp inferInstance

open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)

local instance {χ : U (borel_value (cartan n) (direction n)) →ₐ[ℂ] ℂ} :
    LieRingModule (sl n) (induced_value (cartan n) (direction n) χ) :=
  inducedLieRingModule (cartan n) (direction n) χ

local instance {χ : U (borel_value (cartan n) (direction n)) →ₐ[ℂ] ℂ} :
    LieModule ℂ (sl n) (induced_value (cartan n) (direction n) χ) :=
  inducedLieModule (cartan n) (direction n) χ

section Label

private theorem label_of_simple (hn : 1 ≤ n)
    {V : Type} [AddCommGroup V] [Module ℂ V] [LieRingModule (sl n) V] [LieModule ℂ (sl n) V]
    [IsSimpleOrder (LieSubmodule ℂ (sl n) V)] (lam : Module.Dual ℂ (cartan n)) (v : V)
    (hv : v ≠ 0) (hwt : ∀ h : cartan n, ⁅(h : sl n), v⁆ = lam h • v)
    (hupper : ∀ (i j : Fin (n + 1)) (hij : i < j), ⁅rootVector n i j hij.ne, v⁆ = 0) :
    HasLabel n lam V := by
  letI := cartan_isCartan n
  have hss := (ClassicalMatrixCartans.type_a n).1
  have hd := (positive_roots n hn).1
  have hs (a : simple (cartan n) (direction n)) :
      ∃ i j : Fin (n + 1), ∃ hij : i < j,
        ∃ e : sl n, e = rootVector n i j hij.ne ∧
          e ∈ rootSpace_value (cartan n) a.val ∧ e ≠ 0 := by
    obtain ⟨i, j, hij, he⟩ := (positive_iff hn a.val).mp a.property.1
    exact ⟨i, j, hij, rootVector n i j hij.ne, rfl, he ▸ rootVector_mem i j hij.ne,
      rootVector_ne_zero i j hij.ne⟩
  choose i j hij e he hm hnz using hs
  have hraise : RaisingVectors (cartan n) (direction n) e := fun a => ⟨hm a, hnz a⟩
  have hcyc : LieSubmodule.lieSpan ℂ (sl n) ({v} : Set V) = ⊤ := by
    apply (eq_bot_or_eq_top _).resolve_left
    intro h
    exact hv ((LieSubmodule.mem_bot _).mp (h ▸
      LieSubmodule.subset_lieSpan (R := ℂ) (L := sl n) (Set.mem_singleton v)))
  obtain ⟨χ, hχ, _, hsimple, qv⟩ :=
    SimpleHighestWeightQuotient.exists_simple_quotient hss (cartan n) (direction n) hd lam e hraise
  have hhw : IsHighestWeight e lam v :=
    ⟨hv, hwt, fun a => he a ▸ hupper (i a) (j a) (hij a), hcyc⟩
  obtain ⟨f, hf, _⟩ :=
    SimpleHighestWeightQuotient.highest_weight_surjects hss (cartan n) (direction n) hd
      lam χ hχ e hraise V v hhw
  have hinj : Function.Injective f := by
    apply (LieModuleHom.ker_eq_bot _).mp
    apply (eq_bot_or_eq_top _).resolve_right
    intro ht
    exact qv.1 (hf.1 ▸ LieModuleHom.mem_ker.mp (ht ▸ LieSubmodule.mem_top v))
  let F := LinearEquiv.ofBijective (f : V →ₗ[ℂ] simpleQuotient_value (cartan n) (direction n) χ)
    ⟨hinj, hf.2⟩
  exact ⟨χ, hχ, ⟨⟨f, F.symm, F.left_inv, F.right_inv⟩⟩⟩

end Label

private theorem defining_simple : IsSimpleOrder (LieSubmodule ℂ (sl n) (Vector n)) := by
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  obtain ⟨x, hx, hne⟩ : ∃ x : Vector n, x ∈ W ∧ x ≠ 0 := by
    contrapose! hW
    exact le_bot_iff.mp (fun x hx => (LieSubmodule.mem_bot _).mpr (hW x hx))
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    contrapose! hne
    exact funext hne
  have hv (a b : Fin (n + 1)) (hab : a ≠ b) :
      ⁅rootVector n a b hab, x⁆ = x b • vectorBasis n a := by
    ext z
    change (Matrix.single a b (1 : ℂ) *ᵥ x) z = _
    change (∑ v, Matrix.single a b (1 : ℂ) z v * x v) = _
    by_cases haz : a = z <;> simp [Matrix.single_apply, Pi.basisFun_apply, Pi.single_apply, haz]
  have hm (i : Fin (n + 1)) (hij : i ≠ j) : vectorBasis n i ∈ W := by
    have hi := W.lie_mem (x := rootVector n i j hij) hx
    rw [hv] at hi
    exact (W.toSubmodule.smul_mem_iff hj).mp hi
  apply eq_top_of_basis_mem W (vectorBasis n)
  intro i
  by_cases hij : i = j
  · subst i
    by_cases h : ∃ a : Fin (n + 1), a ≠ j
    · obtain ⟨a, ha⟩ := h
      have hi := W.lie_mem (x := rootVector n j a ha.symm) (hm a ha)
      rw [root_lie_basis, ite_eq_left rfl] at hi
      exact hi
    · push Not at h
      have he : x = x j • vectorBasis n j := by
        ext a
        rw [h a]
        simp [Pi.basisFun_apply]
      exact (W.toSubmodule.smul_mem_iff hj).mp (he ▸ hx)
  · exact hm i hij

theorem defining : defining_type := by
  intro n hn
  letI := defining_simple (n := n)
  apply label_of_simple hn (omega n 1) (vectorBasis n 0)
    ((vectorBasis n).ne_zero _)
  · rw [omega_one]
    exact fun h => cartan_lie_basis h 0
  · intro i j hij
    have hj : j ≠ 0 := by intro h; subst j; exact (Fin.not_lt_zero _) hij
    rw [root_lie_basis, ite_eq_right hj]

private def coordinateWeight (c : Fin (n + 1) → ℂ) : Module.Dual ℂ (cartan n) :=
  ∑ i, c i • epsilon n i

private theorem coordinateWeight_apply (c : Fin (n + 1) → ℂ) (h : cartan n) :
    coordinateWeight c h = ∑ i, c i * h.val.val i i := by
  simp only [coordinateWeight, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

private theorem coordinateWeight_coroot (c : Fin (n + 1) → ℂ) (i j : Fin (n + 1)) :
    coordinateWeight c (matrixCoroot n i j) = c i - c j := by
  rw [coordinateWeight_apply]
  simp only [coroot_entry, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp [eq_comm]

private theorem coordinateWeight_inj {c d : Fin (n + 1) → ℂ}
    (hsum : ∑ i, c i = ∑ i, d i) (h : coordinateWeight c = coordinateWeight d) : c = d := by
  have hc (i : Fin (n + 1)) : c i - d i = c 0 - d 0 := by
    have hi := congrArg (fun α : Module.Dual ℂ (cartan n) => α (matrixCoroot n i 0)) h
    rw [coordinateWeight_coroot, coordinateWeight_coroot] at hi
    linear_combination hi
  have hz : c 0 - d 0 = 0 := by
    have hS : ∑ i, (c i - d i) = 0 := by rw [Finset.sum_sub_distrib, hsum, sub_self]
    simp_rw [hc] at hS
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
    exact (mul_eq_zero.mp hS).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)
  exact funext fun i => sub_eq_zero.mp ((hc i).trans hz)

private theorem omega_eq_coordinateWeight (k : ℕ) :
    omega n k = coordinateWeight (fun i : Fin (n + 1) => if i.val < k then 1 else 0) := by
  unfold omega coordinateWeight
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k <;> simp [hi]

/-- In a weight basis with distinct weights, a nonzero submodule contains
a basis vector of maximal weight for the standard upper triangular
positive system. If each basis vector except one has a nonzero raising
operator, every nonzero submodule contains that distinguished vector. -/
private theorem simple_of_weight_basis
    {V : Type} [AddCommGroup V] [Module ℂ V] [LieRingModule (sl n) V] [LieModule ℂ (sl n) V]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ V) (t : ι)
    (χ : ι → Module.Dual ℂ (cartan n)) (hχ : Function.Injective χ)
    (hwt : ∀ (i : ι) (h : cartan n), ⁅(h : sl n), b i⁆ = χ i h • b i)
    (hstep : ∀ i : ι, i ≠ t → ∃ p q : Fin (n + 1), ∃ hpq : p < q,
      ⁅rootVector n p q hpq.ne, b i⁆ ≠ 0) :
    IsSimpleOrder (LieSubmodule ℂ (sl n) V) := by
  letI : Nontrivial V := ⟨⟨b t, 0, b.ne_zero t⟩⟩
  letI : FiniteDimensional ℂ V := Module.Finite.of_basis b
  have hrepr (h : cartan n) (v : V) (i : ι) :
      b.repr ⁅(h : sl n), v⁆ i = χ i h * b.repr v i := by
    have eq : (b.coord i).comp (LieModule.toEnd ℂ (sl n) V (h : sl n)) =
        χ i h • b.coord i := by
      apply b.ext
      intro j
      change (b.coord i) ⁅(h : sl n), b j⁆ = χ i h * b.coord i (b j)
      rw [hwt, map_smul, smul_eq_mul]
      by_cases hij : j = i <;> simp [Module.Basis.coord_apply, Finsupp.single_apply, hij]
    exact LinearMap.congr_fun eq v
  have hcomponent (W : LieSubmodule ℂ (sl n) V) {v : V} (hv : v ∈ W)
      (i : ι) (hi : b.repr v i ≠ 0) : b i ∈ W := by
    have hs : (∑ j, b.repr v j • b j) ∈ W := by rwa [b.sum_repr v]
    have hp := weight_components_mem (cartan n) W (Finset.univ : Finset ι)
      (fun j => (χ j : cartan n → ℂ)) (DFunLike.coe_injective.comp hχ).injOn
      (fun j => b.repr v j • b j)
      (fun j _ h => by rw [lie_smul, hwt, smul_comm]) hs i (Finset.mem_univ i)
    exact (W.toSubmodule.smul_mem_iff hi).mp hp
  have hw (W : LieSubmodule ℂ (sl n) V) (hW : W ≠ ⊥) : b t ∈ W := by
    let s : Finset ι := Finset.univ.filter (fun i => b i ∈ W)
    obtain ⟨v, hv, hne⟩ : ∃ v : V, v ∈ W ∧ v ≠ 0 := by
      contrapose! hW
      exact le_bot_iff.mp (fun x hx => (LieSubmodule.mem_bot _).mpr (hW x hx))
    have hindex {y : V} (hy : y ≠ 0) : ∃ i, b.repr y i ≠ 0 := by
      contrapose! hy
      exact b.repr.map_eq_zero_iff.mp (Finsupp.ext hy)
    obtain ⟨i, hi⟩ := hindex hne
    have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomponent W hv i hi⟩⟩
    obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => direction n (χ j)) hs
    by_cases hit : i = t
    · exact hit ▸ (Finset.mem_filter.mp hi).2
    obtain ⟨p, q, hpq, hraised⟩ := hstep i hit
    let A := rootVector n p q hpq.ne
    let y : V := ⁅A, b i⁆
    have hyW : y ∈ W := W.lie_mem (Finset.mem_filter.mp hi).2
    have hywt (h : cartan n) : ⁅(h : sl n), y⁆ = (χ i + root n p q) h • y := by
      change ⁅(h : sl n), ⁅A, b i⁆⁆ = _
      rw [leibniz_lie, hwt]
      change ⁅⁅(h : sl n), rootVector n p q hpq.ne⁆, b i⁆ + _ = _
      rw [root_eigen, smul_lie, lie_smul, LinearMap.add_apply, add_smul, add_comm]
    obtain ⟨j, hj⟩ := hindex hraised
    have hχj : χ j = χ i + root n p q := by
      ext h
      have eq := hrepr h y j
      rw [hywt, map_smul, Finsupp.smul_apply, smul_eq_mul] at eq
      exact (mul_right_cancel₀ hj eq).symm
    have hj' : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomponent W hyW j hj⟩
    have hpos : 0 < direction n (root n p q) := by
      rw [direction_root, sub_pos]
      exact_mod_cast hpq
    have hh := hmax j hj'
    rw [hχj, map_add] at hh
    exact (not_le.mpr (lt_add_of_pos_right _ hpos) hh).elim
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  obtain ⟨C, hC⟩ := CompleteReducibility.invariant_complement ℂ (sl n) V
    (ClassicalMatrixCartans.type_a n).1 W
  by_contra hne
  have hCne : C ≠ ⊥ := by
    rintro rfl
    exact hne (by simpa using hC.sup_eq_top)
  have hb : b t ∈ W ⊓ C := ⟨hw W hW, hw C hCne⟩
  rw [hC.inf_eq_bot] at hb
  exact b.ne_zero t ((LieSubmodule.mem_bot _).mp hb)

section Symmetric

open MvPolynomial
open private polynomialGenerator polynomialDerivation_generator
  from MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels

private theorem polynomialGenerator_basis (i : Fin (n + 1)) :
    polynomialGenerator n (vectorBasis n i) = X i := by
  simp [polynomialGenerator]

private theorem root_lie_polynomial (i j : Fin (n + 1)) (hij : i ≠ j)
    (p : MvPolynomial (Fin (n + 1)) ℂ) : ⁅rootVector n i j hij, p⁆ = X i * pderiv j p := by
  rw [polynomial_lie]
  have eq : polynomialDerivation (rootVector n i j hij) =
      (X i : MvPolynomial (Fin (n + 1)) ℂ) • pderiv j := by
    apply MvPolynomial.derivation_ext
    intro l
    rw [polynomialDerivation_X, root_lie_basis, Derivation.smul_apply, pderiv_X]
    by_cases h : j = l
    · subst l
      rw [ite_eq_left rfl, polynomialGenerator_basis, Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [ite_eq_right h, map_zero, Pi.single_eq_of_ne (Ne.symm h), smul_zero]
  exact DFunLike.congr_fun eq p

private theorem cartan_lie_monomial (h : cartan n) (d : Fin (n + 1) →₀ ℕ) :
    ⁅(h : sl n), monomial d (1 : ℂ)⁆ =
      coordinateWeight (fun i => (d i : ℂ)) h • monomial d 1 := by
  let P := MvPolynomial (Fin (n + 1)) ℂ
  have he : polynomialDerivation (h : sl n) =
      ∑ i : Fin (n + 1), (epsilon n i h • (X i : P)) • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro l
    rw [polynomialDerivation_X, cartan_lie_basis, map_smul, polynomialGenerator_basis]
    change _ = Derivation.coeFnAddMonoidHom (∑ i, (epsilon n i h • (X i : P)) • pderiv i) (X l)
    rw [map_sum, Finset.sum_apply]
    simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, pderiv_X]
    simp only [Pi.single_apply, smul_ite, smul_zero]
    simp
  rw [polynomial_lie, he]
  change Derivation.coeFnAddMonoidHom (∑ i, (epsilon n i h • (X i : P)) • pderiv i)
    (monomial d 1) = _
  rw [map_sum, Finset.sum_apply, coordinateWeight_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  change (epsilon n i h • (X i : P)) * pderiv i (monomial d 1) =
    ((d i : ℂ) * h.val.val i i) • monomial d 1
  rw [Algebra.smul_mul_assoc, X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]
  rfl

private abbrev Degree (n a : ℕ) := {d : Fin (n + 1) →₀ ℕ // d.degree = a}

noncomputable local instance (n a : ℕ) : Fintype (Degree n a) :=
  (Finsupp.finite_of_degree_eq (σ := Fin (n + 1)) a).fintype

private def symmetricBasis (n a : ℕ) : Module.Basis (Degree n a) ℂ (symmetricPower n a) :=
  (MvPolynomial.basisRestrictSupport ℂ {d : Fin (n + 1) →₀ ℕ | d.degree = a}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported _ _ a).symm)

private theorem symmetricBasis_coe {a : ℕ} (d : Degree n a) :
    (symmetricBasis n a d : MvPolynomial (Fin (n + 1)) ℂ) = monomial d.val 1 := by
  rw [symmetricBasis, Module.Basis.map_apply]
  erw [LinearEquiv.coe_ofEq_apply]
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) {d : Fin (n + 1) →₀ ℕ | d.degree = a}).symm
      (Finsupp.single d 1) : (Fin (n + 1) →₀ ℕ) →₀ ℂ)) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

private def symmetricTop (n a : ℕ) : Degree n a :=
  ⟨Finsupp.single 0 a, Finsupp.degree_single _ _⟩

private theorem exists_other_variable {a : ℕ} (d : Degree n a) (hd : d ≠ symmetricTop n a) :
    ∃ j : Fin (n + 1), j ≠ 0 ∧ d.val j ≠ 0 := by
  by_contra! hh
  apply hd
  apply Subtype.ext
  ext j
  by_cases hj : j = 0
  · subst j
    have h : d.val 0 = d.val.degree := by
      rw [Finsupp.degree_eq_sum, Finset.sum_eq_single 0 (fun j _ hj => hh j hj)]
      simp
    simpa [symmetricTop] using h.trans d.property
  · simp [symmetricTop, Finsupp.single_eq_of_ne hj, hh j hj]

private theorem symmetric_cartan {a : ℕ} (d : Degree n a) (h : cartan n) :
    ⁅(h : sl n), symmetricBasis n a d⁆ =
      coordinateWeight (fun i => (d.val i : ℂ)) h • symmetricBasis n a d := by
  apply Subtype.ext
  change ⁅(h : sl n), (symmetricBasis n a d : MvPolynomial (Fin (n + 1)) ℂ)⁆ =
    _ • (symmetricBasis n a d : MvPolynomial (Fin (n + 1)) ℂ)
  rw [symmetricBasis_coe, cartan_lie_monomial]

theorem symmetric : symmetric_type := by
  intro n hn a
  let b := symmetricBasis n a
  let t := symmetricTop n a
  let χ : Degree n a → Module.Dual ℂ (cartan n) :=
    fun d => coordinateWeight (fun i => (d.val i : ℂ))
  have hinj : Function.Injective χ := by
    intro d e h
    have hsum : (∑ i, (d.val i : ℂ)) = ∑ i, (e.val i : ℂ) := by
      exact_mod_cast (show (∑ i, d.val i) = ∑ i, e.val i by
        rw [← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, d.property, e.property])
    have hce := coordinateWeight_inj hsum h
    apply Subtype.ext
    ext i
    exact_mod_cast congrFun hce i
  have hstep (d : Degree n a) (hd : d ≠ t) :
      ∃ i j : Fin (n + 1), ∃ hij : i < j,
        ⁅rootVector n i j hij.ne, b d⁆ ≠ 0 := by
    obtain ⟨j, hj, hdj⟩ := exists_other_variable d hd
    have h0j : (0 : Fin (n + 1)) < j := Fin.pos_iff_ne_zero.mpr hj
    refine ⟨0, j, h0j, fun he => ?_⟩
    have h := congrArg (fun p : symmetricPower n a => (p : MvPolynomial (Fin (n + 1)) ℂ)) he
    change ⁅rootVector n 0 j h0j.ne, (b d : MvPolynomial (Fin (n + 1)) ℂ)⁆ = 0 at h
    rw [root_lie_polynomial, symmetricBasis_coe, pderiv_monomial, one_mul, X,
      monomial_mul_monomial, one_mul, monomial_eq_zero] at h
    exact hdj (by exact_mod_cast h)
  let := simple_of_weight_basis b t χ hinj (fun d h => symmetric_cartan d h) hstep
  apply label_of_simple hn ((a : ℂ) • omega n 1) (b t) (b.ne_zero t)
  · intro h
    have he : χ t = (a : ℂ) • omega n 1 := by
      unfold χ t symmetricTop coordinateWeight
      rw [omega_one]
      simp [Finsupp.single_apply, eq_comm]
    simpa only [← he] using symmetric_cartan t h
  · intro i j hij
    have hj : j ≠ 0 := by intro h; subst j; exact (Fin.not_lt_zero _) hij
    apply Subtype.ext
    change ⁅rootVector n i j hij.ne, (b t : MvPolynomial (Fin (n + 1)) ℂ)⁆ = 0
    rw [root_lie_polynomial, symmetricBasis_coe, pderiv_monomial]
    simp [t, symmetricTop, Ne.symm hj]

open _root_.D05.M15.SymmetricDerivation (induced induced_generator induced_scalar induced_mul)

private theorem symmetricDerivation_polynomial (A : sl n)
    (x : SymmetricAlgebra ℂ (Vector n)) :
    SymmetricAlgebra.equivMvPolynomial (vectorBasis n)
      (induced (LieModule.toEnd ℂ (sl n) (Vector n) A) x) =
    polynomialDerivation A (SymmetricAlgebra.equivMvPolynomial (vectorBasis n) x) := by
  let e := SymmetricAlgebra.equivMvPolynomial (vectorBasis n)
  have hgen (v : Vector n) : e (SymmetricAlgebra.ι ℂ (Vector n) v) = polynomialGenerator n v := by
    change SymmetricAlgebra.lift ((vectorBasis n).constr ℂ (MvPolynomial.X (R := ℂ)))
      (SymmetricAlgebra.ι ℂ (Vector n) v) = _
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl
  change e (induced (LieModule.toEnd ℂ (sl n) (Vector n) A) x) = polynomialDerivation A (e x)
  induction x using SymmetricAlgebra.induction with
  | algebraMap c => rw [induced_scalar, map_zero, e.commutes, Derivation.map_algebraMap]
  | ι v =>
    rw [induced_generator, hgen, hgen, polynomialDerivation_generator]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | mul x y hx hy =>
    rw [induced_mul, map_add, map_mul, map_mul, hx, hy, map_mul, Derivation.leibniz]
    change _ = e x * polynomialDerivation A (e y) + e y * polynomialDerivation A (e x)
    ring

theorem symmetric_quotient : symmetric_quotient_type := by
  intro n a hn
  let E : SymmetricQuotient n a ≃ₗ⁅ℂ,sl n⁆ symmetricPower n a :=
    { symmetricPolynomialEquiv n a with
      map_lie' := by
        intro A q
        change symmetricPolynomialEquiv n a ⁅A, q⁆ = ⁅A, symmetricPolynomialEquiv n a q⁆
        rw [symmetricQuotient_lie, LinearEquiv.apply_symm_apply] }
  obtain ⟨χ, hχ, ⟨e⟩⟩ := symmetric n hn a
  refine ⟨⟨χ, hχ, ⟨E.trans e⟩⟩, fun A q => ?_⟩
  apply (SymmetricAlgebra.equivMvPolynomial (vectorBasis n)).injective
  rw [symmetricDerivation_polynomial]
  exact congrArg (fun p : symmetricPower n a => (p : MvPolynomial (Fin (n + 1)) ℂ))
    (E.toLieModuleHom.map_lie A q)

end Symmetric

section Exterior

open Set.powersetCard
open _root_.D05.M15.ExteriorDerivation (induced_word)

private abbrev Subsets (n k : ℕ) := ↥(Set.powersetCard (Fin (n + 1)) k)

private abbrev wedgeBasis (n k : ℕ) : Module.Basis (Subsets n k) ℂ (exteriorPower n k) :=
  (vectorBasis n).exteriorPower k

private abbrev enumerate {k : ℕ} (s : Subsets n k) : Fin k ↪o Fin (n + 1) :=
  ofFinEmbEquiv.symm s

private def wedgeTop (n k : ℕ) (hk : k ≤ n + 1) : Subsets n k :=
  ⟨Finset.univ.filter (fun i : Fin (n + 1) => i.val < k), by
    change (Finset.univ.filter (fun i : Fin (n + 1) => i.val < k)).card = k
    rw [Fin.card_filter_val_lt, min_eq_right hk]⟩

private theorem wedgeTop_mem {k : ℕ} {hk : k ≤ n + 1} (i : Fin (n + 1)) :
    i ∈ wedgeTop n k hk ↔ i.val < k := by
  rw [← mem_coe_iff]
  simp [wedgeTop]

private theorem wedge_basis_lie {k : ℕ} (s : Subsets n k) (A : sl n) :
    ((⁅A, wedgeBasis n k s⁆ : exteriorPower n k) : ExteriorAlgebra ℂ (Vector n)) =
      ∑ l : Fin k, ExteriorAlgebra.ιMulti ℂ k
        (Function.update (vectorBasis n ∘ enumerate s) l ⁅A, vectorBasis n (enumerate s l)⁆) := by
  change ⁅A, ((vectorBasis n).exteriorPower k s : ExteriorAlgebra ℂ (Vector n))⁆ = _
  rw [_root_.exteriorPower.basis_apply]
  exact induced_word (LieModule.toEnd ℂ (sl n) (Vector n) A) k (vectorBasis n ∘ enumerate s)

private theorem wedge_zero_if_right_absent {k : ℕ} (s : Subsets n k)
    {i j : Fin (n + 1)} (hij : i ≠ j) (hj : j ∉ s) :
    ⁅rootVector n i j hij, wedgeBasis n k s⁆ = 0 := by
  apply Subtype.ext
  rw [wedge_basis_lie]
  change (∑ l : Fin k, ExteriorAlgebra.ιMulti ℂ k
    (Function.update (vectorBasis n ∘ enumerate s) l
      ⁅rootVector n i j hij, vectorBasis n (enumerate s l)⁆)) = 0
  apply Finset.sum_eq_zero
  intro l _
  have hne : j ≠ enumerate s l := by
    intro he
    exact hj ((mem_range_ofFinEmbEquiv_symm_iff_mem s j).mp ⟨l, he.symm⟩)
  rw [root_lie_basis, ite_eq_right hne, AlternatingMap.map_update_zero]

private theorem wedge_replace {k : ℕ} (s : Subsets n k)
    {i j : Fin (n + 1)} (hij : i ≠ j) {l : Fin k} (hl : enumerate s l = j) :
    ((⁅rootVector n i j hij, wedgeBasis n k s⁆ : exteriorPower n k) :
      ExteriorAlgebra ℂ (Vector n)) =
      ExteriorAlgebra.ιMulti ℂ k (vectorBasis n ∘ Function.update (⇑(enumerate s)) l i) := by
  rw [wedge_basis_lie, Finset.sum_eq_single l]
  · rw [root_lie_basis, hl, ite_eq_left rfl]
    congr 1
    funext t
    by_cases ht : t = l
    · subst t
      simp [Function.update_self]
    · simp [Function.update_of_ne ht]
  · intro t _ htl
    have hne : j ≠ enumerate s t := by
      intro he
      exact htl ((enumerate s).injective (he.symm.trans hl.symm))
    rw [root_lie_basis, ite_eq_right hne, AlternatingMap.map_update_zero]
  · simp

private theorem wedge_of_basis_ne_zero {k : ℕ} {f : Fin k → Fin (n + 1)}
    (hf : Function.Injective f) :
    ExteriorAlgebra.ιMulti ℂ k (vectorBasis n ∘ f) ≠ 0 := by
  intro he
  have hw : _root_.exteriorPower.ιMulti ℂ k (vectorBasis n ∘ f) = 0 := Subtype.ext he
  let form := _root_.exteriorPower.pairingDual ℂ (Vector n) k
    (_root_.exteriorPower.ιMulti ℂ k (fun i => (vectorBasis n).coord (f i)))
  have hval : form (_root_.exteriorPower.ιMulti ℂ k (vectorBasis n ∘ f)) = 1 := by
    dsimp only [form]
    rw [_root_.exteriorPower.pairingDual_ιMulti_ιMulti]
    suffices heq : Matrix.of (fun i j : Fin k => (vectorBasis n).coord (f j)
        ((vectorBasis n ∘ f) i)) = 1 by rw [heq, Matrix.det_one]
    ext i j
    simp [Matrix.one_apply, Module.Basis.coord_apply, Pi.single_apply, hf.eq_iff, eq_comm]
  rw [hw, map_zero] at hval
  exact zero_ne_one hval

private theorem wedge_nonzero_replacement {k : ℕ} (s : Subsets n k)
    {i j : Fin (n + 1)} (hij : i ≠ j) (hi : i ∉ s) (hj : j ∈ s) :
    ⁅rootVector n i j hij, wedgeBasis n k s⁆ ≠ 0 := by
  obtain ⟨l, hl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s j).mpr hj
  have hf : Function.Injective (Function.update (⇑(enumerate s)) l i) := by
    have hne (t : Fin k) : i ≠ enumerate s t := by
      intro he
      exact hi ((mem_range_ofFinEmbEquiv_symm_iff_mem s i).mp ⟨t, he.symm⟩)
    intro a b hab
    by_cases ha : a = l <;> by_cases hb : b = l
    · exact ha.trans hb.symm
    · subst a
      rw [Function.update_self, Function.update_of_ne hb] at hab
      exact (hne b hab).elim
    · subst b
      rw [Function.update_self, Function.update_of_ne ha] at hab
      exact (hne a hab.symm).elim
    · apply (enumerate s).injective
      simpa only [Function.update_of_ne ha, Function.update_of_ne hb] using hab
  intro hz
  have h := congrArg (fun p : exteriorPower n k => (p : ExteriorAlgebra ℂ (Vector n))) hz
  rw [wedge_replace s hij hl] at h
  exact wedge_of_basis_ne_zero hf h

private theorem wedge_zero_if_both_present {k : ℕ} (s : Subsets n k)
    {i j : Fin (n + 1)} (hij : i ≠ j) (hi : i ∈ s) (hj : j ∈ s) :
    ⁅rootVector n i j hij, wedgeBasis n k s⁆ = 0 := by
  obtain ⟨l, hl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s j).mpr hj
  obtain ⟨t, ht⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr hi
  have htl : t ≠ l := by
    intro he
    subst t
    exact hij (ht.symm.trans hl)
  apply Subtype.ext
  rw [wedge_replace s hij hl]
  apply (ExteriorAlgebra.ιMulti ℂ k).map_eq_zero_of_eq (i := l) (j := t) _ _ (Ne.symm htl)
  simp [Function.comp_apply, Function.update_self, Function.update_of_ne htl, ht]

private def wedgeWeight {k : ℕ} (s : Subsets n k) : Module.Dual ℂ (cartan n) :=
  coordinateWeight (fun i => if i ∈ s.val then 1 else 0)

private theorem wedgeWeight_apply {k : ℕ} (s : Subsets n k) (h : cartan n) :
    wedgeWeight s h = ∑ i ∈ s.val, h.val.val i i := by
  rw [wedgeWeight, coordinateWeight_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

private theorem wedge_cartan {k : ℕ} (s : Subsets n k) (h : cartan n) :
    ⁅(h : sl n), wedgeBasis n k s⁆ = wedgeWeight s h • wedgeBasis n k s := by
  apply Subtype.ext
  rw [wedge_basis_lie]
  simp_rw [cartan_lie_basis, ← Function.comp_apply (f := ⇑(vectorBasis n)) (g := ⇑(enumerate s)),
    AlternatingMap.map_update_smul, Function.update_eq_self, ← Finset.sum_smul]
  have he : (wedgeBasis n k s : ExteriorAlgebra ℂ (Vector n)) =
      ExteriorAlgebra.ιMulti ℂ k (vectorBasis n ∘ enumerate s) := by
    change ((vectorBasis n).exteriorPower k s : ExteriorAlgebra ℂ (Vector n)) = _
    rw [_root_.exteriorPower.basis_apply]
    rfl
  rw [← he]
  change (∑ l : Fin k, epsilon n (enumerate s l) h) •
    (wedgeBasis n k s : ExteriorAlgebra ℂ (Vector n)) =
      wedgeWeight s h • (wedgeBasis n k s : ExteriorAlgebra ℂ (Vector n))
  congr 1
  rw [wedgeWeight_apply]
  have himage : Finset.univ.image (⇑(enumerate s)) = s.val := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact (mem_range_ofFinEmbEquiv_symm_iff_mem s i).trans mem_coe_iff.symm
  rw [← himage, Finset.sum_image (enumerate s).injective.injOn]
  rfl

theorem exterior : exterior_type := by
  intro n k hkpos hk
  have hn : 1 ≤ n := hkpos.trans hk
  let b := wedgeBasis n k
  let t := wedgeTop n k (by omega)
  have hinj : Function.Injective (wedgeWeight (n := n) (k := k)) := by
    intro s q he
    have hsum (s : Subsets n k) :
        (∑ i : Fin (n + 1), if i ∈ s.val then (1 : ℂ) else 0) = k := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      simp
    have ht := coordinateWeight_inj ((hsum s).trans (hsum q).symm) he
    apply Subtype.ext
    ext i
    have hi := congrFun ht i
    by_cases hs : i ∈ s.val <;> by_cases hq : i ∈ q.val <;> simp_all
  have hstep (s : Subsets n k) (hs : s ≠ t) :
      ∃ i j : Fin (n + 1), ∃ hij : i < j,
        ⁅rootVector n i j hij.ne, b s⁆ ≠ 0 := by
    obtain ⟨i, hit, his⟩ := (exists_mem_notMem_iff_ne t s).mp hs.symm
    obtain ⟨j, hjs, hjt⟩ := (exists_mem_notMem_iff_ne s t).mp hs
    have hij : i < j := by
      change i.val < j.val
      exact lt_of_lt_of_le ((wedgeTop_mem i).mp hit) (le_of_not_gt ((wedgeTop_mem j).not.mp hjt))
    exact ⟨i, j, hij, wedge_nonzero_replacement s hij.ne his hjs⟩
  let := simple_of_weight_basis b t wedgeWeight hinj (fun s h => wedge_cartan s h) hstep
  apply label_of_simple hn (omega n k) (b t) (b.ne_zero t)
  · intro h
    have hw : wedgeWeight t = omega n k := by
      rw [omega_eq_coordinateWeight, wedgeWeight]
      congr 1
      funext i
      have hi : i ∈ t.val ↔ i.val < k := mem_coe_iff.trans (wedgeTop_mem i)
      by_cases h : i.val < k <;> simp [hi, h]
    rw [← hw]
    exact wedge_cartan t h
  · intro i j hij
    by_cases hj : j ∈ t
    · exact wedge_zero_if_both_present t hij.ne
        ((wedgeTop_mem i).mpr (lt_trans hij ((wedgeTop_mem j).mp hj))) hj
    · exact wedge_zero_if_right_absent t hij.ne hj

end Exterior

section TensorWithDual

private abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℂ

private def flipTensor : TensorWithDual ≃ₗ⁅ℂ,sl 2⁆
    (Module.Dual ℂ (Vector 2) ⊗[ℂ] Vector 2) where
  __ := TensorProduct.comm ℂ _ _
  map_lie' := by
    intro A x
    change TensorProduct.comm ℂ _ _ ⁅A, x⁆ = ⁅A, TensorProduct.comm ℂ _ _ x⁆
    induction x using TensorProduct.inductionOn with
    | tmul v f =>
        let C := TensorProduct.comm ℂ (Vector 2) (Module.Dual ℂ (Vector 2))
        have hv := TensorProduct.LieModule.lie_tmul_right (R := ℂ) A v f
        have hf := TensorProduct.LieModule.lie_tmul_right (R := ℂ) A f v
        change C ⁅A, v ⊗ₜ[ℂ] f⁆ = ⁅A, C (v ⊗ₜ[ℂ] f)⁆
        calc
          _ = C (⁅A, v⁆ ⊗ₜ[ℂ] f + v ⊗ₜ[ℂ] ⁅A, f⁆) := congrArg C hv
          _ = ⁅A, f⁆ ⊗ₜ[ℂ] v + f ⊗ₜ[ℂ] ⁅A, v⁆ := by
            simp only [C, map_add, TensorProduct.comm_tmul]
            exact add_comm _ _
          _ = _ := hf.symm
    | add x y hx hy => simp only [lie_add, map_add, hx, hy]

attribute [local instance 100] LieRing.ofAssociativeRing

private def endMatrix : (Vector 2 →ₗ[ℂ] Vector 2) ≃ₗ⁅ℂ,sl 2⁆ Matrix3 where
  __ := LinearMap.toMatrix'
  map_lie' := by
    intro A f
    let E : Module.End ℂ (Vector 2) ≃ₗ⁅ℂ⁆ Matrix3 := lieEquivMatrix'
    change E ⁅A, f⁆ = ⁅(A : Matrix3), E f⁆
    have H : ⁅A, f⁆ = ⁅E.symm (A : Matrix3), f⁆ := by
      ext v i
      rfl
    rw [H, LieEquiv.map_lie, E.apply_symm_apply]

private def meanTrace : Matrix3 →ₗ[ℂ] ℂ :=
  (3 : ℂ)⁻¹ • Matrix.traceLinearMap (Fin 3) ℂ ℂ

private theorem trace_mean_scalar (a : ℂ) :
    meanTrace (a • (1 : Matrix3)) = a := by
  change (3 : ℂ)⁻¹ * Matrix.trace (a • (1 : Matrix3)) = a
  rw [Matrix.trace_smul, Matrix.trace_one]
  norm_num [smul_eq_mul]
  ring

private theorem trace_mean (X : Matrix3) :
    Matrix.trace (meanTrace X • (1 : Matrix3)) = Matrix.trace X := by
  rw [Matrix.trace_smul, Matrix.trace_one]
  change ((3 : ℂ)⁻¹ * Matrix.trace X) * ↑(Fintype.card (Fin 3)) = Matrix.trace X
  norm_num
  ring

private def tracelessPart (X : Matrix3) : sl 2 :=
  ⟨X - meanTrace X • 1, by
    change Matrix.trace (X - meanTrace X • 1) = 0
    rw [Matrix.trace_sub, trace_mean, sub_self]⟩

private def traceSplit : Matrix3 ≃ₗ⁅ℂ,sl 2⁆ (Scalar × sl 2) where
  toFun X := ((TrivialLieModule.equiv ℂ (sl 2) ℂ).symm (meanTrace X), tracelessPart X)
  invFun p := (p.2 : Matrix3) + (TrivialLieModule.equiv ℂ (sl 2) ℂ p.1) • 1
  left_inv X := by
    change X - meanTrace X • (1 : Matrix3) + meanTrace X • 1 = X
    exact sub_add_cancel _ _
  right_inv p := by
    have hzero : meanTrace (p.2 : Matrix3) = 0 := by
      change (3 : ℂ)⁻¹ * Matrix.trace (p.2 : Matrix3) = 0
      rw [show Matrix.trace (p.2 : Matrix3) = 0 from p.2.property, mul_zero]
    let a := TrivialLieModule.equiv ℂ (sl 2) ℂ p.1
    let A : Matrix3 := p.2
    have hmean : meanTrace (A + a • 1) = a := by
      rw [map_add, trace_mean_scalar, hzero, zero_add]
    apply Prod.ext
    · change (TrivialLieModule.equiv ℂ (sl 2) ℂ).symm (meanTrace (A + a • 1)) = _
      rw [hmean]
      exact (TrivialLieModule.equiv ℂ (sl 2) ℂ).symm_apply_apply p.1
    · apply Subtype.ext
      change A + a • 1 - meanTrace (A + a • 1) • 1 = A
      rw [hmean, add_sub_cancel_right]
  map_add' X Y := by
    apply Prod.ext
    · change (TrivialLieModule.equiv ℂ (sl 2) ℂ).symm (meanTrace (X + Y)) = _
      rw [map_add, map_add]
      rfl
    · apply Subtype.ext
      change X + Y - meanTrace (X + Y) • 1 = (X - meanTrace X • 1) + (Y - meanTrace Y • 1)
      rw [map_add, add_smul]
      abel
  map_smul' z X := by
    apply Prod.ext
    · change (TrivialLieModule.equiv ℂ (sl 2) ℂ).symm (meanTrace (z • X)) = _
      rw [map_smul, map_smul]
      rfl
    · apply Subtype.ext
      change z • X - meanTrace (z • X) • 1 = z • (X - meanTrace X • 1)
      rw [map_smul, smul_sub, smul_smul, smul_eq_mul]
  map_lie' := by
    intro A X
    have hz : meanTrace (A.val * X - X * A.val) = 0 := by
      change (3 : ℂ)⁻¹ * Matrix.trace (A.val * X - X * A.val) = 0
      rw [Matrix.trace_sub, Matrix.trace_mul_comm (A.val) X, sub_self, mul_zero]
    apply Prod.ext
    · change (TrivialLieModule.equiv ℂ (sl 2) ℂ).symm
        (meanTrace (A.val * X - X * A.val)) = 0
      rw [hz, map_zero]
    · apply Subtype.ext
      change (A.val * X - X * A.val) - meanTrace (A.val * X - X * A.val) • 1 =
        A.val * (X - meanTrace X • 1) - (X - meanTrace X • 1) * A.val
      rw [hz, zero_smul, sub_zero, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
      abel

private theorem sl3_label : HasLabel 2 (omega 2 1 + omega 2 2) (sl 2) := by
  letI := adjoint_simple (n := 2) (by decide)
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  apply label_of_simple (by decide) (omega 2 1 + omega 2 2)
    (rootVector 2 0 2 h02) (rootVector_ne_zero 0 2 h02)
  · intro h
    have hw : root 2 0 2 h = (omega 2 1 + omega 2 2) h := by
      have ht : (∑ i : Fin 3, h.val.val i i) = 0 := h.val.property
      rw [Fin.sum_univ_three] at ht
      have hw₂ : omega 2 2 h = h.val.val 0 0 + h.val.val 1 1 := by
        rw [omega_apply]
        change (∑ i : Fin 3, if i.val < 2 then h.val.val i i else 0) = _
        rw [Fin.sum_univ_three]
        have h0 : (0 : Fin 3).val < 2 := by decide
        have h1 : (1 : Fin 3).val < 2 := by decide
        have h2 : ¬ (2 : Fin 3).val < 2 := by decide
        rw [ite_eq_left h0, ite_eq_left h1, ite_eq_right h2, add_zero]
      rw [root_apply, LinearMap.add_apply, omega_one, hw₂]
      change h.val.val 0 0 - h.val.val 2 2 = h.val.val 0 0 + (h.val.val 0 0 + h.val.val 1 1)
      linear_combination -ht
    rw [root_eigen, hw]
  · intro i j hij
    have hj0 : j ≠ 0 := by
      intro h
      subst j
      exact (Fin.not_lt_zero _) hij
    have hi2 : (2 : Fin 3) ≠ i := by
      intro he
      have hi : i.val < j.val := hij
      have h₁ := congrArg Fin.val he
      have h₂ := j.isLt
      change 2 = i.val at h₁
      omega
    apply Subtype.ext
    change Matrix.single i j (1 : ℂ) * Matrix.single 0 2 1 -
      Matrix.single 0 2 1 * Matrix.single i j 1 = 0
    rw [Matrix.single_mul_single_of_ne 1 i j 0 hj0,
      Matrix.single_mul_single_of_ne 1 0 2 i hi2, sub_zero]

theorem tensor_with_dual : tensor_with_dual_type := by
  refine ⟨sl3_label, ?_, ?_⟩
  · letI : FiniteDimensional ℂ Scalar := Module.Finite.of_surjective
      (TrivialLieModule.equiv ℂ (sl 2) ℂ).symm.toLinearMap
      (TrivialLieModule.equiv ℂ (sl 2) ℂ).symm.surjective
    have ht := traceSplit.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, Module.finrank_matrix] at ht
    have hscalar : Module.finrank ℂ Scalar = 1 := (TrivialLieModule.equiv ℂ (sl 2) ℂ).finrank_eq.trans
      (Module.finrank_self ℂ)
    rw [hscalar] at ht
    norm_num at ht
    omega
  · let T := TensorDualHom.finiteDualTensorHom (k := ℂ) (g := sl 2) (M := Vector 2) (N := Vector 2)
    let e := (flipTensor.trans T).trans (endMatrix.trans traceSplit)
    refine ⟨e, fun v f => ?_⟩
    have he : endMatrix (T (flipTensor (v ⊗ₜ[ℂ] f))) =
        Matrix.vecMulVec v (fun i => f (vectorBasis 2 i)) := by
      change LinearMap.toMatrix' (dualTensorHom _ _ _ (TensorProduct.comm ℂ _ _ (v ⊗ₜ[ℂ] f))) = _
      rw [TensorProduct.comm_tmul]
      ext i j
      rw [LinearMap.toMatrix'_apply, dualTensorHom_apply, Matrix.vecMulVec_apply]
      rw [Pi.smul_apply, smul_eq_mul]
      rw [Pi.basisFun_apply]
      exact mul_comm _ _
    have ht : meanTrace (Matrix.vecMulVec v (fun i => f (vectorBasis 2 i))) = f v / 3 := by
      change (3 : ℂ)⁻¹ * Matrix.trace (Matrix.vecMulVec v (fun i => f (vectorBasis 2 i))) = _
      have hf : Matrix.trace (Matrix.vecMulVec v (fun i => f (vectorBasis 2 i))) = f v := by
        rw [Matrix.trace]
        simp only [Matrix.diag_apply, Matrix.vecMulVec_apply, ← smul_eq_mul, ← map_smul, ← map_sum]
        exact congrArg f ((vectorBasis 2).sum_repr v)
      rw [hf, div_eq_mul_inv, mul_comm]
    constructor
    · change meanTrace (endMatrix (T (flipTensor (v ⊗ₜ[ℂ] f)))) = _
      rw [he, ht]
    · change (endMatrix (T (flipTensor (v ⊗ₜ[ℂ] f)))) -
        meanTrace (endMatrix (T (flipTensor (v ⊗ₜ[ℂ] f)))) • 1 = _
      rw [he, ht]

end TensorWithDual

end LieAlgebrasAndRepresentations.TypeAHighestWeightModels
