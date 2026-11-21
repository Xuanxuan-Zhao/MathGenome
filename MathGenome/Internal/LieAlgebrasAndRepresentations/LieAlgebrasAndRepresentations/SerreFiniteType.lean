import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreFiniteType
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreTriangularConstruction
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Push

/-! LA-F03-Finite: finite type for the actual Serre quotient. Local nilpotence
and terminating exponential automorphisms precede the root-support height
descent and finite-dimensionality argument. -/
noncomputable section
namespace LieAlgebrasAndRepresentations.Serre

section Derivations
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- A pointwise nilpotence bound also kills every higher iterate. -/
theorem derivation_pow_eq_zero_of_le (D : LieDerivation ℂ L L) {x : L} {m n : ℕ}
    (hx : (D.toLinearMap ^ m) x = 0) (hmn : m ≤ n) :
    (D.toLinearMap ^ n) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm m k, pow_add, Module.End.mul_apply, hx, map_zero]

/-- The general Leibniz rule makes pointwise nilpotence closed under brackets. -/
theorem derivation_pow_lie_eq_zero (D : LieDerivation ℂ L L) {x y : L} {m n : ℕ}
    (hx : (D.toLinearMap ^ m) x = 0) (hy : (D.toLinearMap ^ n) y = 0) :
    (D.toLinearMap ^ (m+n)) ⁅x,y⁆ = 0 := by
  rw [Module.End.pow_apply]
  change D^[m+n] ⁅x,y⁆ = 0
  rw [D.iterate_apply_lie]
  apply Finset.sum_eq_zero
  intro ij hij
  have hij' := Finset.mem_antidiagonal.mp hij
  by_cases hm : m ≤ ij.1
  · have hz := derivation_pow_eq_zero_of_le D hx hm
    rw [Module.End.pow_apply] at hz
    change D^[ij.1] x = 0 at hz
    rw [hz, zero_lie, smul_zero]
  · have hn : n ≤ ij.2 := by omega
    have hz := derivation_pow_eq_zero_of_le D hy hn
    rw [Module.End.pow_apply] at hz
    change D^[ij.2] y = 0 at hz
    rw [hz, lie_zero, smul_zero]

/-- The locally nilpotent vectors of any derivation form a Lie subalgebra. -/
def nilpotentVectors (D : LieDerivation ℂ L L) : LieSubalgebra ℂ L where
  carrier := {x | ∃ n : ℕ, (D.toLinearMap ^ n) x = 0}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    rw [map_add, derivation_pow_eq_zero_of_le D hm (le_max_left _ _),
      derivation_pow_eq_zero_of_le D hn (le_max_right _ _), add_zero]
  smul_mem' := by
    rintro c x ⟨n, hn⟩
    exact ⟨n, by rw [map_smul, hn, smul_zero]⟩
  lie_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m+n, derivation_pow_lie_eq_zero D hm hn⟩

/-- Equivalent bracket-iterate formulation for an inner derivation. -/
theorem mem_nilpotentVectors_ad (z x : L) :
    x ∈ nilpotentVectors (LieDerivation.ad ℂ L z) ↔
      ∃ n, iterBracket z n x = 0 := by
  change (∃ n, ((LieDerivation.ad ℂ L z).toLinearMap ^ n) x = 0) ↔ _
  simp only [LieDerivation.coe_ad_apply_eq_ad_apply, iterBracket_eq_pow]

end Derivations

universe u
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

/-- An inner derivation is locally nilpotent everywhere if it is so on all
three families in the presentation. -/
theorem locally_nilpotent_of_generators (z : Algebra A)
    (hE : ∀ j, ∃ n, iterBracket z n (e A j) = 0)
    (hF : ∀ j, ∃ n, iterBracket z n (f A j) = 0)
    (hH : ∀ j, ∃ n, iterBracket z n (h A j) = 0) :
    ∀ x : Algebra A, ∃ n, iterBracket z n x = 0 := by
  have htop : nilpotentVectors (LieDerivation.ad ℂ (Algebra A) z) = ⊤ := by
    apply generators_generate A
    · intro j; exact (mem_nilpotentVectors_ad z (e A j)).mpr (hE j)
    · intro j; exact (mem_nilpotentVectors_ad z (f A j)).mpr (hF j)
    · intro j; exact (mem_nilpotentVectors_ad z (h A j)).mpr (hH j)
  intro x
  apply (mem_nilpotentVectors_ad z x).mp
  rw [htop]
  trivial

/-- The positive simple generators act locally nilpotently, directly from the
native Serre relations, including the redundant diagonal relation. -/
theorem e_locally_nilpotent (i : ι) (x : Algebra A) :
    ∃ n, iterBracket (e A i) n x = 0 := by
  apply locally_nilpotent_of_generators A (e A i) _ _ _ x
  · intro j
    refine ⟨(-A i j).toNat + 1, ?_⟩
    rw [iterBracket_add]
    exact native_serre_e A i j
  · intro j
    by_cases hij : i = j
    · subst j
      refine ⟨3, ?_⟩
      simp only [iterBracket, ef, ite_true]
      rw [← lie_skew (e A i) (h A i), he, lie_neg, lie_zsmul, lie_self, smul_zero, neg_zero]
    · refine ⟨1, ?_⟩
      simpa [iterBracket] using (ef A i j).trans (ite_eq_right hij)
  · intro j
    refine ⟨2, ?_⟩
    simp only [iterBracket]
    rw [← lie_skew (e A i) (h A j), he, lie_neg, lie_zsmul, lie_self, smul_zero, neg_zero]

/-- The negative simple generators also act locally nilpotently on the whole
quotient, without invoking its as-yet unproved finite dimensionality. -/
theorem f_locally_nilpotent (i : ι) (x : Algebra A) :
    ∃ n, iterBracket (f A i) n x = 0 := by
  apply locally_nilpotent_of_generators A (f A i) _ _ _ x
  · intro j
    by_cases hij : i = j
    · subst j
      refine ⟨3, ?_⟩
      simp only [iterBracket]
      rw [← lie_skew (f A i) (e A i), ef, ite_eq_left rfl, lie_neg]
      rw [← lie_skew (f A i) (h A i), hf]
      simp only [neg_neg, lie_neg, lie_zsmul, lie_self, smul_zero, neg_zero]
    · refine ⟨1, ?_⟩
      simp only [iterBracket]
      rw [← lie_skew (f A i) (e A j), ef, ite_eq_right (Ne.symm hij), neg_zero]
  · intro j
    refine ⟨(-A i j).toNat + 1, ?_⟩
    rw [iterBracket_add]
    exact native_serre_f A i j
  · intro j
    refine ⟨2, ?_⟩
    simp only [iterBracket]
    rw [← lie_skew (f A i) (h A j), hf]
    simp only [neg_neg, lie_zsmul, lie_self, smul_zero]

theorem locallyNilpotent_spec :
    Specs.LieAlgebrasAndRepresentations.SerreFiniteType.locallyNilpotentExpected.{u} := by
  intro ι _ A i x
  exact ⟨e_locally_nilpotent A i x, f_locally_nilpotent A i x⟩


/-- Bracketing joint eigenvectors adds their weights. -/
theorem lie_mem_weightSpace {χ ψ : ι → ℂ} {x y : Algebra A}
    (hx : x ∈ weightSpace A χ) (hy : y ∈ weightSpace A ψ) :
    ⁅x,y⁆ ∈ weightSpace A (χ + ψ) := by
  intro i
  rw [leibniz_lie, hx i, hy i, smul_lie, lie_smul, ← add_smul]
  rfl

/-- The Cartan span is contained in the ordinary zero weight space. -/
theorem cartan_le_zero_weightSpace : cartan A ≤ weightSpace A 0 := by
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩ i
  simpa using hh A i j

theorem e_mem_weightSpace (j : ι) :
    e A j ∈ weightSpace A (fun i => (A i j : ℂ)) := by
  intro i
  rw [he, Int.cast_smul_eq_zsmul]

theorem f_mem_weightSpace (j : ι) :
    f A j ∈ weightSpace A (fun i => -(A i j : ℂ)) := by
  intro i
  rw [hf, neg_smul, Int.cast_smul_eq_zsmul]

/-- The span of all ordinary weight spaces is closed under brackets. -/
def weightSpan : LieSubalgebra ℂ (Algebra A) where
  __ := Submodule.span ℂ {x | ∃ χ, x ∈ weightSpace A χ}
  lie_mem' := by
    intro x y hx hy
    change ⁅x,y⁆ ∈ Submodule.span ℂ {x | ∃ χ, x ∈ weightSpace A χ}
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨χ, hx⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨ψ, hy⟩ := hy
        exact Submodule.subset_span ⟨χ + ψ, lie_mem_weightSpace A hx hy⟩
      | zero => simpa only [lie_zero] using Submodule.zero_mem _
      | add y z _ _ hy hz => simpa only [lie_add] using Submodule.add_mem _ hy hz
      | smul r y _ hy => simpa only [lie_smul] using Submodule.smul_mem _ r hy
    | zero => simpa only [zero_lie] using Submodule.zero_mem _
    | add x z _ _ hx hz => simpa only [add_lie] using Submodule.add_mem _ hx hz
    | smul r x _ hx => simpa only [smul_lie] using Submodule.smul_mem _ r hx

/-- Simultaneous ordinary eigenspaces already span the entire presented
algebra, even before its root support or dimension has been determined. -/
theorem weightSpace_iSup_eq_top : (⨆ χ : ι → ℂ, weightSpace A χ) = ⊤ := by
  have htop : weightSpan A = ⊤ := by
    apply generators_generate A
    · intro j
      exact Submodule.subset_span ⟨_, e_mem_weightSpace A j⟩
    · intro j
      exact Submodule.subset_span ⟨_, f_mem_weightSpace A j⟩
    · intro j
      exact Submodule.subset_span ⟨0, cartan_le_zero_weightSpace A
        (Submodule.subset_span ⟨j, rfl⟩)⟩
  have hle : (weightSpan A).toSubmodule ≤ ⨆ χ, weightSpace A χ := by
    apply Submodule.span_le.mpr
    rintro x ⟨χ, hx⟩
    exact (le_iSup (fun χ => weightSpace A χ) χ) hx
  apply top_unique
  rw [htop] at hle
  exact hle

/-- The Cartan dimension follows directly from the proved triangular basis. -/
theorem cartan_finrank [Fintype ι] (hA : CartanConditions A) :
    Module.finrank ℂ (cartan A) = Fintype.card ι := by
  obtain ⟨b, _⟩ := (triangular_of_cartanConditions A hA).2.1
  exact Module.finrank_eq_card_basis b


/-- With Cartan rows indexing coroots, the reflection on all complex weights
is an involution. No support or reality of the weight is assumed. -/
theorem reflectWeight_involutive (i : ι) (hii : A i i = 2) (χ : ι → ℂ) :
    reflectWeight A i (reflectWeight A i χ) = χ := by
  funext j
  simp only [reflectWeight, hii, Int.cast_ofNat]
  ring

/-- An actual Lie automorphism with the displayed Cartan action transports
ordinary weight vectors by the reflection, even for arbitrary complex weights. -/
theorem map_mem_weightSpace_of_cartan_reflection (i : ι) (hii : A i i = 2)
    (n : Algebra A ≃ₗ⁅ℂ⁆ Algebra A)
    (hn : ∀ j, n (h A j) = h A j - (A j i : ℂ) • h A i)
    {χ : ι → ℂ} {x : Algebra A} (hx : x ∈ weightSpace A χ) :
    n x ∈ weightSpace A (reflectWeight A i χ) := by
  have hpre (j : ι) : n (h A j - (A j i : ℂ) • h A i) = h A j := by
    rw [map_sub, map_smul, hn j, hn i, hii]
    simp only [Int.cast_ofNat]
    module
  intro j
  rw [← hpre j, ← n.map_lie, sub_lie, smul_lie, hx j, hx i,
    map_sub, map_smul, map_smul, map_smul]
  dsimp [reflectWeight]
  module

/-- Equality of actual subspaces, as needed for transporting multiplicities. -/
theorem weightSpace_map_of_cartan_reflection (i : ι) (hii : A i i = 2)
    (n : Algebra A ≃ₗ⁅ℂ⁆ Algebra A)
    (hn : ∀ j, n (h A j) = h A j - (A j i : ℂ) • h A i) (χ : ι → ℂ) :
    (weightSpace A χ).map n.toLinearEquiv.toLinearMap =
      weightSpace A (reflectWeight A i χ) := by
  have hinv (j : ι) : n.symm (h A j) = h A j - (A j i : ℂ) • h A i := by
    apply n.injective
    change n (n.symm (h A j)) = n (h A j - (A j i : ℂ) • h A i)
    rw [n.apply_symm_apply, map_sub, map_smul, hn j, hn i, hii]
    simp only [Int.cast_ofNat]
    module
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact map_mem_weightSpace_of_cartan_reflection A i hii n hn hx
  · intro y hy
    refine ⟨n.symm y, ?_, n.apply_symm_apply y⟩
    have hm := map_mem_weightSpace_of_cartan_reflection A i hii n.symm hinv hy
    rwa [reflectWeight_involutive A i hii] at hm

/-- The real-root realization in joint Cartan coordinates is faithful. -/
theorem rootWeight_injective {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : Module.Basis ι ℝ E) :
    Function.Injective (rootWeight b) := by
  intro a a' haa'
  apply InnerProductSpace.ext_inner_right_basis b
  intro i
  have heq : rootCartan a (b i) = rootCartan a' (b i) := by
    have heq := congrFun haa' i
    exact Complex.ofReal_injective heq
  dsimp [rootCartan] at heq
  have hi : inner ℝ (b i) (b i) ≠ 0 := _root_.inner_self_ne_zero.mpr (b.ne_zero i)
  have heq' := (div_left_inj' hi).mp heq
  linarith

section LocalFiniteness
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- The lowering commutator, without assuming that the initial vector is
annihilated by the lowering operator. -/
theorem lowering_iterBracket_general (H E F X : L) (a : ℂ)
    (hE : ⁅H,E⁆ = (2 : ℂ) • E) (hX : ⁅H,X⁆ = a • X)
    (hFE : ⁅F,E⁆ = -H) (n : ℕ) :
    ⁅F,iterBracket E (n+1) X⁆ = iterBracket E (n+1) ⁅F,X⁆ -
      ((n+1 : ℕ) * (a+n) : ℂ) • iterBracket E n X := by
  induction n with
  | zero =>
    simp only [iterBracket, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
      zero_add, add_zero, one_mul]
    rw [leibniz_lie, hFE, neg_lie, hX]
    abel
  | succ n ih =>
    change ⁅F,⁅E,iterBracket E (n+1) X⁆⁆ = _
    rw [leibniz_lie, hFE, neg_lie,
      bracket_iterBracket_weight H E X 2 a hE hX, ih, lie_sub, lie_smul]
    change -((a + (n+1 : ℕ) * 2) • iterBracket E (n+1) X) +
      (iterBracket E (n+1+1) ⁅F,X⁆ -
        ((n+1 : ℕ) * (a+n) : ℂ) • iterBracket E (n+1) X) = _
    have hc : (a + (n+1 : ℕ) * 2) + ((n+1 : ℕ) * (a+n)) =
        ((n+1+1 : ℕ) * (a+(n+1 : ℕ)) : ℂ) := by push_cast; ring
    rw [← hc, add_smul]
    module

/-- For an sl₂ triple acting by brackets, local nilpotence of the two
root operators makes every Cartan eigenvector lie in a finite invariant
space. The rectangle of vectors E^a F^b X supplies an explicit space. -/
theorem finite_invariant_of_weight (H E F X : L) (a : ℂ)
    (hHE : ⁅H,E⁆ = (2 : ℂ) • E) (hHF : ⁅H,F⁆ = (-2 : ℂ) • F)
    (hFE : ⁅F,E⁆ = -H) (hX : ⁅H,X⁆ = a • X)
    (hE : ∀ y : L, ∃ m, iterBracket E m y = 0)
    (hF : ∃ n, iterBracket F n X = 0) :
    ∃ S : Submodule ℂ L, Module.Finite ℂ S ∧ X ∈ S ∧
      ∀ y ∈ S, ⁅E,y⁆ ∈ S ∧ ⁅F,y⁆ ∈ S ∧ ⁅H,y⁆ ∈ S := by
  classical
  obtain ⟨n, hn⟩ := hF
  choose m hm using fun b : Fin (n+1) => hE (iterBracket F b.val X)
  let M := (Finset.univ.sup m) + 1
  have hM (b : Fin (n+1)) : m b ≤ M :=
    (Finset.le_sup (f := m) (Finset.mem_univ b)).trans (Nat.le_succ _)
  have hkill (b : ℕ) (hb : b < n+1) : iterBracket E M (iterBracket F b X) = 0 := by
    have hk := derivation_pow_eq_zero_of_le (LieDerivation.ad ℂ L E)
      (x := iterBracket F b X) (m := m ⟨b,hb⟩) (n := M)
    simp only [LieDerivation.coe_ad_apply_eq_ad_apply, ← iterBracket_eq_pow] at hk
    exact hk (hm ⟨b,hb⟩) (hM ⟨b,hb⟩)
  let V : Fin M × Fin (n+1) → L := fun p =>
    iterBracket E p.1.val (iterBracket F p.2.val X)
  let S := Submodule.span ℂ (Set.range V)
  have hmem (c b : ℕ) (hc : c < M) (hb : b < n+1) :
      iterBracket E c (iterBracket F b X) ∈ S :=
    Submodule.subset_span ⟨(⟨c,hc⟩, ⟨b,hb⟩), rfl⟩
  refine ⟨S, Module.Finite.span_of_finite ℂ (Set.finite_range V), ?_, ?_⟩
  · exact hmem 0 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨c,b⟩, rfl⟩ := hy
      have hEy : ⁅E, V (c,b)⁆ ∈ S := by
        change iterBracket E (c.val+1) (iterBracket F b.val X) ∈ S
        by_cases hc : c.val+1 < M
        · exact hmem _ _ hc b.isLt
        · have heq : c.val+1 = M := by omega
          rw [heq, hkill b.val b.isLt]
          exact S.zero_mem
      have hHy : ⁅H, V (c,b)⁆ ∈ S := by
        change ⁅H, iterBracket E c.val (iterBracket F b.val X)⁆ ∈ S
        rw [bracket_iterBracket_weight H E _ 2 (a + b.val * (-2)) hHE
          (bracket_iterBracket_weight H F X (-2) a hHF hX b.val)]
        exact S.smul_mem _ (hmem _ _ c.isLt b.isLt)
      refine ⟨hEy, ?_, hHy⟩
      have hnext : iterBracket E c.val (iterBracket F (b.val+1) X) ∈ S := by
        by_cases hb : b.val+1 < n+1
        · exact hmem _ _ c.isLt hb
        · have heq : b.val = n := by omega
          rw [heq, iterBracket, hn, lie_zero]
          simp only [iterBracket_eq_pow, map_zero]
          exact S.zero_mem
      cases hc : c.val with
      | zero => simpa only [V, hc, iterBracket] using hnext
      | succ k =>
        change ⁅F, iterBracket E c.val (iterBracket F b.val X)⁆ ∈ S
        rw [hc, lowering_iterBracket_general H E F _ (a + b.val * (-2)) hHE
          (bracket_iterBracket_weight H F X (-2) a hHF hX b.val) hFE]
        apply S.sub_mem
        · simpa only [iterBracket, hc] using hnext
        · apply S.smul_mem
          exact hmem k b.val (by omega) b.isLt
    | zero => simp only [lie_zero]; exact ⟨S.zero_mem, S.zero_mem, S.zero_mem⟩
    | add y z _ _ hy hz =>
      simp only [lie_add]
      exact ⟨S.add_mem hy.1 hz.1, S.add_mem hy.2.1 hz.2.1,
        S.add_mem hy.2.2 hz.2.2⟩
    | smul r y _ hy =>
      simp only [lie_smul]
      exact ⟨S.smul_mem r hy.1, S.smul_mem r hy.2.1, S.smul_mem r hy.2.2⟩

/-- Vectors contained in finite-dimensional spaces invariant under three
specified adjoint operators form a submodule. -/
def finiteInvariantVectors (H E F : L) : Submodule ℂ L where
  carrier := {x | ∃ S : Submodule ℂ L, Module.Finite ℂ S ∧ x ∈ S ∧
    ∀ y ∈ S, ⁅E,y⁆ ∈ S ∧ ⁅F,y⁆ ∈ S ∧ ⁅H,y⁆ ∈ S}
  zero_mem' := ⟨⊥, inferInstance, by simp, by
    intro y hy
    have : y = 0 := hy
    subst y
    simp⟩
  add_mem' := by
    rintro x y ⟨S, hS, hx, hIS⟩ ⟨T, hT, hy, hIT⟩
    letI := hS
    letI := hT
    refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup hx hy, ?_⟩
    intro z hz
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hz
    simp only [lie_add]
    exact ⟨Submodule.add_mem_sup (hIS s hs).1 (hIT t ht).1,
      Submodule.add_mem_sup (hIS s hs).2.1 (hIT t ht).2.1,
      Submodule.add_mem_sup (hIS s hs).2.2 (hIT t ht).2.2⟩
  smul_mem' := by
    rintro c x ⟨S, hS, hx, hIS⟩
    exact ⟨S, hS, S.smul_mem c hx, hIS⟩

end LocalFiniteness

/-- Each simple rank-one triple acts locally finitely on the entire actual
Serre quotient. This precedes, and does not assume, finite type. -/
theorem rankOne_locally_finite (hA : CartanConditions A) : RankOneLocallyFinite A := by
  intro i x
  let S := finiteInvariantVectors (h A i) (e A i) (f A i)
  have hle (χ : ι → ℂ) : weightSpace A χ ≤ S := by
    intro y hy
    apply finite_invariant_of_weight (h A i) (e A i) (f A i) y (χ i)
    · rw [he, hA.1 i, ← Int.cast_smul_eq_zsmul ℂ]
      norm_num
    · rw [hf, hA.1 i, ← Int.cast_smul_eq_zsmul ℂ]
      norm_num
    · rw [← lie_skew (f A i) (e A i), ef, ite_eq_left rfl]
    · exact hy i
    · exact e_locally_nilpotent A i
    · exact f_locally_nilpotent A i y
  have ht : S = ⊤ := top_unique (by
    rw [← weightSpace_iSup_eq_top A]
    exact iSup_le hle)
  have hx : x ∈ S := by rw [ht]; trivial
  exact hx

section LocallyNilpotentExponential
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A truncated exponential polynomial in a linear operator. -/
def expPolynomial (D : Module.End ℂ V) (n : ℕ) : Module.End ℂ V :=
  ∑ k ∈ Finset.range n, ((k.factorial : ℂ)⁻¹) • D ^ k

theorem end_pow_apply_eq_zero_of_le (D : Module.End ℂ V) {x : V} {m n : ℕ}
    (hx : (D ^ m) x = 0) (hmn : m ≤ n) : (D ^ n) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm m k, pow_add, Module.End.mul_apply, hx, map_zero]

/-- Exponential cutoffs agree as soon as they annihilate the vector. -/
theorem expPolynomial_apply_eq_of_le (D : Module.End ℂ V) {x : V} {m n : ℕ}
    (hx : (D ^ m) x = 0) (hmn : m ≤ n) :
    expPolynomial D n x = expPolynomial D m x := by
  rw [expPolynomial, expPolynomial, ← Finset.sum_range_add_sum_Ico _ hmn,
    LinearMap.add_apply]
  suffices (∑ k ∈ Finset.Ico m n, ((k.factorial : ℂ)⁻¹) • D ^ k) x = 0 by
    rw [this, add_zero]
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [LinearMap.smul_apply,
    end_pow_apply_eq_zero_of_le D hx (Finset.mem_Ico.mp hk).1, smul_zero]

/-- The pointwise exponential, with a separately chosen nilpotence cutoff
for each vector. -/
def localExpValue (D : Module.End ℂ V) (hD : ∀ x : V, ∃ n, (D ^ n) x = 0)
    (x : V) : V := expPolynomial D (hD x).choose x

theorem localExpValue_eq (D : Module.End ℂ V)
    (hD : ∀ x : V, ∃ n, (D ^ n) x = 0) {x : V} {n : ℕ}
    (hx : (D ^ n) x = 0) : localExpValue D hD x = expPolynomial D n x := by
  dsimp [localExpValue]
  rcases le_total (hD x).choose n with h | h
  · exact (expPolynomial_apply_eq_of_le D (hD x).choose_spec h).symm
  · exact expPolynomial_apply_eq_of_le D hx h

/-- Local nilpotence suffices for a linear exponential; no uniform bound
on the ambient vector space is used. -/
def localExp (D : Module.End ℂ V) (hD : ∀ x : V, ∃ n, (D ^ n) x = 0) :
    Module.End ℂ V where
  toFun := localExpValue D hD
  map_add' x y := by
    obtain ⟨m, hm⟩ := hD x
    obtain ⟨n, hn⟩ := hD y
    have hx := end_pow_apply_eq_zero_of_le D hm (le_max_left m n)
    have hy := end_pow_apply_eq_zero_of_le D hn (le_max_right m n)
    have hxy : (D ^ max m n) (x+y) = 0 := by rw [map_add, hx, hy, add_zero]
    rw [localExpValue_eq D hD hxy, localExpValue_eq D hD hx,
      localExpValue_eq D hD hy, map_add]
  map_smul' c x := by
    obtain ⟨n, hn⟩ := hD x
    have hcx : (D ^ n) (c • x) = 0 := by rw [map_smul, hn, smul_zero]
    rw [localExpValue_eq D hD hcx, localExpValue_eq D hD hn, map_smul]
    rfl

theorem localExp_eq (D : Module.End ℂ V)
    (hD : ∀ x : V, ∃ n, (D ^ n) x = 0) {x : V} {n : ℕ}
    (hx : (D ^ n) x = 0) : localExp D hD x = expPolynomial D n x :=
  localExpValue_eq D hD hx

/-- Naturality against any globally nilpotent source operator. This allows
the library's finite nilpotent exponential identities to be used on
invariant kernels, without assuming a global bound on the target. -/
theorem localExp_comp_of_nilpotent {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module ℚ W] [IsScalarTower ℚ ℂ W]
    (D : Module.End ℂ V) (hD : ∀ x : V, ∃ n, (D ^ n) x = 0)
    (f : Module.End ℂ W) (hf : IsNilpotent f) (g : W →ₗ[ℂ] V)
    (h : D ∘ₗ g = g ∘ₗ f) :
    localExp D hD ∘ₗ g = g ∘ₗ IsNilpotent.exp f := by
  obtain ⟨n, hn⟩ := hf
  have hp (k : ℕ) (w : W) : (D ^ k) (g w) = g ((f ^ k) w) :=
    LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h k) w
  ext w
  have hz : (D ^ n) (g w) = 0 := by rw [hp, hn, LinearMap.zero_apply, map_zero]
  rw [LinearMap.comp_apply, localExp_eq D hD hz, LinearMap.comp_apply,
    IsNilpotent.exp_eq_sum hn]
  simp only [expPolynomial, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_rat_smul, hp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Rat.cast_smul_eq_qsmul ℂ]
  simp

/-- The kernel of a power is invariant under the operator. -/
theorem end_mapsTo_ker_pow (D : Module.End ℂ V) (n : ℕ) :
    ∀ x ∈ LinearMap.ker (D ^ n), D x ∈ LinearMap.ker (D ^ n) := by
  intro x hx
  change (D ^ n) (D x) = 0
  change (D ^ n) x = 0 at hx
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hx, map_zero]

/-- A locally nilpotent map has genuinely nilpotent restrictions to the
kernels of its powers, with a uniform bound on each such kernel. -/
def kernelRestriction (D : Module.End ℂ V) (n : ℕ) :
    Module.End ℂ (LinearMap.ker (D ^ n)) :=
  D.restrict (end_mapsTo_ker_pow D n)

theorem kernelRestriction_isNilpotent (D : Module.End ℂ V) (n : ℕ) :
    IsNilpotent (kernelRestriction D n) := by
  refine ⟨n, ?_⟩
  ext x
  change (((D.restrict (end_mapsTo_ker_pow D n)) ^ n) x : V) = 0
  rw [Module.End.pow_restrict]
  exact x.property

theorem neg_locally_nilpotent (D : Module.End ℂ V)
    (hD : ∀ x : V, ∃ n, (D ^ n) x = 0) :
    ∀ x : V, ∃ n, ((-D) ^ n) x = 0 := by
  intro x
  obtain ⟨n, hn⟩ := hD x
  refine ⟨n, ?_⟩
  rw [neg_pow, Module.End.mul_apply, hn, map_zero]

theorem localExp_neg_comp (D : Module.End ℂ V)
    (hD : ∀ x : V, ∃ n, (D ^ n) x = 0)
    (hneg : ∀ x : V, ∃ n, ((-D) ^ n) x = 0) :
    localExp (-D) hneg ∘ₗ localExp D hD = LinearMap.id := by
  letI := Module.restrictScalars ℚ ℂ V
  letI := IsScalarTower.restrictScalars ℚ ℂ V
  ext x
  obtain ⟨n, hn⟩ := hD x
  let S := LinearMap.ker (D ^ n)
  let f := kernelRestriction D n
  have hf : IsNilpotent f := kernelRestriction_isNilpotent D n
  have hp := localExp_comp_of_nilpotent D hD f hf S.subtype (by ext; rfl)
  have hm := localExp_comp_of_nilpotent (-D) hneg (-f) hf.neg S.subtype (by ext; rfl)
  have hx : x ∈ S := hn
  have hp' := LinearMap.congr_fun hp (⟨x,hx⟩ : S)
  have hm' := LinearMap.congr_fun hm (IsNilpotent.exp f (⟨x,hx⟩ : S))
  change localExp (-D) hneg (localExp D hD x) = x
  change localExp D hD x = S.subtype (IsNilpotent.exp f ⟨x,hx⟩) at hp'
  rw [hp']
  change localExp (-D) hneg (S.subtype (IsNilpotent.exp f ⟨x,hx⟩)) =
    S.subtype ((IsNilpotent.exp (-f) * IsNilpotent.exp f) ⟨x,hx⟩) at hm'
  rw [hm', hf.exp_neg_mul_exp_self]
  rfl

/-- The inverse of the pointwise exponential is the exponential of the
negative operator, proved on actual invariant nilpotent kernels. -/
def localExpEquiv (D : Module.End ℂ V)
    (hD : ∀ x : V, ∃ n, (D ^ n) x = 0) : V ≃ₗ[ℂ] V where
  toLinearMap := localExp D hD
  invFun := localExp (-D) (neg_locally_nilpotent D hD)
  left_inv x := LinearMap.congr_fun
    (localExp_neg_comp D hD (neg_locally_nilpotent D hD)) x
  right_inv x := by
    have hh := localExp_neg_comp (-D) (neg_locally_nilpotent D hD)
      (by simpa only [neg_neg] using hD)
    simp only [neg_neg] at hh
    exact LinearMap.congr_fun hh x

end LocallyNilpotentExponential

section LieExponential
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The exponential of a locally nilpotent derivation preserves the Lie
bracket. On two invariant kernels the Leibniz rule intertwines the bracket
with the sum of the two commuting tensor operators. -/
theorem localExp_map_lie (D : LieDerivation ℂ L L)
    (hD : ∀ x : L, ∃ n, (D.toLinearMap ^ n) x = 0) (x y : L) :
    localExp D.toLinearMap hD ⁅x,y⁆ =
      ⁅localExp D.toLinearMap hD x, localExp D.toLinearMap hD y⁆ := by
  letI := Module.restrictScalars ℚ ℂ L
  letI := IsScalarTower.restrictScalars ℚ ℂ L
  obtain ⟨m, hm⟩ := hD x
  obtain ⟨n, hn⟩ := hD y
  let S := LinearMap.ker (D.toLinearMap ^ m)
  let T := LinearMap.ker (D.toLinearMap ^ n)
  let fS : Module.End ℂ S := kernelRestriction D.toLinearMap m
  let fT : Module.End ℂ T := kernelRestriction D.toLinearMap n
  have hfS : IsNilpotent fS := kernelRestriction_isNilpotent D.toLinearMap m
  have hfT : IsNilpotent fT := kernelRestriction_isNilpotent D.toLinearMap n
  let DL : Module.End ℂ (S ⊗[ℂ] T) := fT.lTensor S
  let DR : Module.End ℂ (S ⊗[ℂ] T) := fS.rTensor T
  have hDL : IsNilpotent DL := hfT.map (Module.End.lTensorAlgHom ℂ T S)
  have hDR : IsNilpotent DR := hfS.map (Module.End.rTensorAlgHom ℂ S T)
  have hc : Commute DL DR := by ext; simp [DL, DR]
  let g : S ⊗[ℂ] T →ₗ[ℂ] L := TensorProduct.lift
    ((LieAlgebra.ad ℂ L).toLinearMap.compl₁₂ S.subtype T.subtype)
  have hg : D.toLinearMap ∘ₗ g = g ∘ₗ (DL + DR) := by
    ext s t
    simp [g, DL, DR, fS, fT, kernelRestriction, D.apply_lie_eq_add]
  have he := localExp_comp_of_nilpotent D.toLinearMap hD (DL+DR)
    (hc.isNilpotent_add hDL hDR) g hg
  have hL : IsNilpotent.exp DL = (IsNilpotent.exp fT).lTensor S := by
    obtain ⟨k, hk⟩ := hfT
    have hkt : DL ^ k = 0 := by simp only [DL, LinearMap.lTensor_pow, hk, LinearMap.lTensor_zero]
    rw [IsNilpotent.exp_eq_sum hkt, IsNilpotent.exp_eq_sum hk]
    change _ = LinearMap.lTensorHom S (∑ j ∈ Finset.range k, (j.factorial : ℚ)⁻¹ • fT ^ j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Rat.cast_smul_eq_qsmul ℂ, ← Rat.cast_smul_eq_qsmul ℂ, map_smul]
    simp only [LinearMap.coe_lTensorHom, DL, LinearMap.lTensor_pow]
  have hR : IsNilpotent.exp DR = (IsNilpotent.exp fS).rTensor T := by
    obtain ⟨k, hk⟩ := hfS
    have hkt : DR ^ k = 0 := by simp only [DR, LinearMap.rTensor_pow, hk, LinearMap.rTensor_zero]
    rw [IsNilpotent.exp_eq_sum hkt, IsNilpotent.exp_eq_sum hk]
    change _ = LinearMap.rTensorHom T (∑ j ∈ Finset.range k, (j.factorial : ℚ)⁻¹ • fS ^ j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Rat.cast_smul_eq_qsmul ℂ, ← Rat.cast_smul_eq_qsmul ℂ, map_smul]
    simp only [LinearMap.coe_rTensorHom, DR, LinearMap.rTensor_pow]
  have hpS := localExp_comp_of_nilpotent D.toLinearMap hD fS hfS S.subtype
    (by ext; rfl)
  have hpT := localExp_comp_of_nilpotent D.toLinearMap hD fT hfT T.subtype
    (by ext; rfl)
  have hx : x ∈ S := hm
  have hy : y ∈ T := hn
  have he' := LinearMap.congr_fun he ((⟨x,hx⟩ : S) ⊗ₜ[ℂ] (⟨y,hy⟩ : T))
  rw [IsNilpotent.exp_add_of_commute hc hDL hDR, hL, hR] at he'
  simp only [LinearMap.comp_apply, Module.End.mul_apply,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul] at he'
  simp only [g, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
    LieHom.coe_toLinearMap, LieAlgebra.ad_apply, Submodule.subtype_apply] at he'
  change localExp D.toLinearMap hD ⁅x,y⁆ =
    ⁅(IsNilpotent.exp fS (⟨x,hx⟩ : S) : L),
      (IsNilpotent.exp fT (⟨y,hy⟩ : T) : L)⁆ at he'
  have hpS' : localExp D.toLinearMap hD x =
      (IsNilpotent.exp fS (⟨x,hx⟩ : S) : L) := LinearMap.congr_fun hpS ⟨x,hx⟩
  have hpT' : localExp D.toLinearMap hD y =
      (IsNilpotent.exp fT (⟨y,hy⟩ : T) : L) := LinearMap.congr_fun hpT ⟨y,hy⟩
  rw [← hpS', ← hpT'] at he'
  exact he'

/-- An actual Lie automorphism attached to any locally nilpotent complex
Lie derivation, defined without finite-dimensionality assumptions. -/
def localLieExp (D : LieDerivation ℂ L L)
    (hD : ∀ x : L, ∃ n, (D.toLinearMap ^ n) x = 0) : L ≃ₗ⁅ℂ⁆ L :=
  { localExpEquiv D.toLinearMap hD with
    map_lie' := fun {x y} => localExp_map_lie D hD x y }

/-- The terminating adjoint exponential as a Lie automorphism. -/
def innerExp (z : L) (hz : ∀ x : L, ∃ n, iterBracket z n x = 0) : L ≃ₗ⁅ℂ⁆ L :=
  localLieExp (LieDerivation.ad ℂ L z) (by
    simpa only [LieDerivation.coe_ad_apply_eq_ad_apply, ← iterBracket_eq_pow] using hz)

theorem innerExp_eq_expSum (z : L) (hz : ∀ x : L, ∃ n, iterBracket z n x = 0)
    {x : L} {n : ℕ} (hx : iterBracket z n x = 0) :
    innerExp z hz x = expSum z n x := by
  change localExp (LieDerivation.ad ℂ L z).toLinearMap _ x = _
  have hx' : ((LieDerivation.ad ℂ L z).toLinearMap ^ n) x = 0 := by
    simpa only [LieDerivation.coe_ad_apply_eq_ad_apply, ← iterBracket_eq_pow] using hx
  rw [localExp_eq _ _ hx']
  simp only [expPolynomial, LinearMap.sum_apply, LinearMap.smul_apply,
    LieDerivation.coe_ad_apply_eq_ad_apply, ← iterBracket_eq_pow, expSum]

theorem innerExp_apply_of_square_zero (z : L)
    (hz : ∀ x : L, ∃ n, iterBracket z n x = 0) {x : L}
    (hx : ⁅z,⁅z,x⁆⁆ = 0) : innerExp z hz x = x + ⁅z,x⁆ := by
  have hx' : iterBracket z 2 x = 0 := hx
  rw [innerExp_eq_expSum z hz hx']
  simp [expSum, Finset.sum_range_succ, iterBracket]

theorem innerExp_apply_of_cube_zero (z : L)
    (hz : ∀ x : L, ∃ n, iterBracket z n x = 0) {x : L}
    (hx : ⁅z,⁅z,⁅z,x⁆⁆⁆ = 0) :
    innerExp z hz x = x + ⁅z,x⁆ + (2 : ℂ)⁻¹ • ⁅z,⁅z,x⁆⁆ := by
  have hx' : iterBracket z 3 x = 0 := hx
  rw [innerExp_eq_expSum z hz hx']
  simp [expSum, Finset.sum_range_succ, iterBracket]

theorem neg_iterBracket_locally_nilpotent (z : L)
    (hz : ∀ x : L, ∃ n, iterBracket z n x = 0) :
    ∀ x : L, ∃ n, iterBracket (-z) n x = 0 := by
  have hz' : ∀ x : L, ∃ n, (LieAlgebra.ad ℂ L z ^ n) x = 0 := by
    simpa only [← iterBracket_eq_pow] using hz
  simpa only [iterBracket_eq_pow, map_neg] using neg_locally_nilpotent _ hz'

end LieExponential

/-- The two actual exponential automorphisms used in a simple reflection. -/
def positiveExp (i : ι) : Algebra A ≃ₗ⁅ℂ⁆ Algebra A :=
  innerExp (e A i) (e_locally_nilpotent A i)

def negativeExp (i : ι) : Algebra A ≃ₗ⁅ℂ⁆ Algebra A :=
  innerExp (-(f A i))
    (neg_iterBracket_locally_nilpotent (f A i) (f_locally_nilpotent A i))

theorem positiveExp_cartan (i j : ι) :
    positiveExp A i (h A j) = h A j - (A j i : ℂ) • e A i := by
  rw [positiveExp, innerExp_apply_of_square_zero]
  · rw [← lie_skew (e A i) (h A j), he, ← Int.cast_smul_eq_zsmul ℂ]
    module
  · rw [← lie_skew (e A i) (h A j), he, lie_neg, lie_zsmul, lie_self,
      smul_zero, neg_zero]

theorem positiveExp_self (i : ι) : positiveExp A i (e A i) = e A i := by
  rw [positiveExp, innerExp_apply_of_square_zero]
  · simp
  · simp

theorem negativeExp_cartan (i j : ι) :
    negativeExp A i (h A j) = h A j - (A j i : ℂ) • f A i := by
  rw [negativeExp, innerExp_apply_of_square_zero]
  · rw [neg_lie, ← lie_skew (f A i) (h A j), hf,
      neg_neg, ← Int.cast_smul_eq_zsmul ℂ]
    module
  · rw [neg_lie, neg_lie, ← lie_skew (f A i) (h A j), hf]
    simp only [neg_neg, lie_neg, neg_lie, lie_zsmul, lie_self, smul_zero, neg_zero]

theorem negativeExp_opposite (i : ι) (hii : A i i = 2) :
    negativeExp A i (e A i) = e A i + h A i - f A i := by
  have hfe : ⁅-(f A i), e A i⁆ = h A i := by
    rw [neg_lie, ← lie_skew (f A i) (e A i), ef, ite_eq_left rfl, neg_neg]
  have hfh : ⁅-(f A i), h A i⁆ = -(2 : ℂ) • f A i := by
    rw [neg_lie, ← lie_skew (f A i) (h A i), hf, neg_neg, hii,
      ← Int.cast_smul_eq_zsmul ℂ]
    norm_num
  rw [negativeExp, innerExp_apply_of_cube_zero]
  · rw [hfe, hfh]
    module
  · rw [hfe, hfh, lie_smul, neg_lie, lie_self, neg_zero, smul_zero]

/-- The product of terminating exponentials has precisely the source's
Cartan reflection action, with rows indexing coroots. -/
theorem exponential_reflection_cartan (i : ι) (hii : A i i = 2) (j : ι) :
    ((positiveExp A i).trans (negativeExp A i) |>.trans (positiveExp A i)) (h A j) =
      h A j - (A j i : ℂ) • h A i := by
  change positiveExp A i (negativeExp A i (positiveExp A i (h A j))) = _
  rw [positiveExp_cartan, map_sub, map_smul, negativeExp_cartan,
    negativeExp_opposite A i hii]
  have heq : h A j - (A j i : ℂ) • f A i -
      (A j i : ℂ) • (e A i + h A i - f A i) =
      h A j - (A j i : ℂ) • (e A i + h A i) := by module
  rw [heq, map_sub, map_smul, map_add, positiveExp_cartan,
    positiveExp_self, positiveExp_cartan, hii]
  norm_num
  module

/-- Local finiteness and the required genuine reflection automorphisms,
including their action on every complex weight space. -/
theorem reflections_spec :
    Specs.LieAlgebrasAndRepresentations.SerreFiniteType.reflectionsExpected.{u} := by
  intro ι _ A hA
  refine ⟨rankOne_locally_finite A hA, ?_⟩
  intro i
  refine ⟨positiveExp A i, negativeExp A i, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨n, hn⟩ := e_locally_nilpotent A i x
    exact ⟨n, hn, innerExp_eq_expSum _ _ hn⟩
  · intro x
    obtain ⟨n, hn⟩ := neg_iterBracket_locally_nilpotent (f A i)
      (f_locally_nilpotent A i) x
    exact ⟨n, hn, innerExp_eq_expSum _ _ hn⟩
  · constructor
    · exact exponential_reflection_cartan A i (hA.1 i)
    · exact weightSpace_map_of_cartan_reflection A i (hA.1 i) _
        (exponential_reflection_cartan A i (hA.1 i))

end LieAlgebrasAndRepresentations.Serre

noncomputable section
namespace LieAlgebrasAndRepresentations.Serre
universe u
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

/-- Distinct ordinary joint weights give independent subspaces without a
finite-dimensionality assumption. -/
theorem weightSpace_iSupIndep : iSupIndep (weightSpace A) := by
  let H : ι → Module.End ℂ (Algebra A) := fun i => LieAlgebra.ad ℂ (Algebra A) (h A i)
  have heq (χ : ι → ℂ) : weightSpace A χ = ⨅ i, (H i).eigenspace (χ i) := by
    ext x
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    rfl
  have hi := iSupIndep.iInf (fun i μ => (H i).eigenspace μ)
    (fun i => (H i).eigenspaces_iSupIndep)
  exact hi.mono (fun χ => (heq χ).le)

/-- A nonzero ordinary weight in a span of selected weight spaces is one
of the selected weights. -/
theorem weight_mem_of_le_iSup {T : Set (ι → ℂ)} {χ : ι → ℂ}
    (hne : weightSpace A χ ≠ ⊥)
    (hle : weightSpace A χ ≤ ⨆ ψ ∈ T, weightSpace A ψ) : χ ∈ T := by
  by_contra hn
  have hdis := weightSpace_iSupIndep A χ
  have he : (⨆ ψ ∈ T, weightSpace A ψ) ≤ ⨆ ψ ≠ χ, weightSpace A ψ := by
    apply iSup₂_le
    intro ψ hψ
    exact le_iSup₂_of_le ψ (by rintro rfl; exact hn hψ) le_rfl
  have hh := hdis.mono_right (hle.trans he)
  exact hne (disjoint_self.mp hh)

end LieAlgebrasAndRepresentations.Serre

noncomputable section
namespace LieAlgebrasAndRepresentations
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A property of simple roots that is preserved by simple reflections holds
for every root. This is valid for the empty root system as well. -/
theorem root_property_of_simple_reflections {R : Set E} (hR : IsRootSystem R)
    {z : E} (hz : RootRegular R z) (P : E → Prop)
    (hbase : ∀ a ∈ simpleRoots R z, P a)
    (hstep : ∀ a ∈ simpleRoots R z, ∀ x, P x → P (rootReflection a x)) :
    ∀ x ∈ R, P x := by
  have hw : ∀ w ∈ simpleWeylGroup R z, ∀ x, P x ↔ P (w x) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, rfl⟩ := hw
      intro x
      simp only [rootReflectionEquiv_apply]
      exact ⟨hstep a ha x, fun hx => by simpa using hstep a ha (rootReflection a x) hx⟩
    | one => intro x; rfl
    | mul w v hw hv ihw ihv =>
      intro x
      exact (ihv x).trans (ihw (v x))
    | inv w hw ih =>
      intro x
      simpa using (ih (w.symm x)).symm
  intro x hx
  obtain ⟨w, a, ha, hwa⟩ := root_simple_orbit hR hz hx
  exact hwa ▸ (hw w w.property a).mp (hbase a ha)

end LieAlgebrasAndRepresentations

noncomputable section
open scoped DirectSum
namespace LieAlgebrasAndRepresentations.Serre
universe u v
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

theorem weightSpace_finrank_of_cartan_reflection (i : ι) (hii : A i i = 2)
    (n : Algebra A ≃ₗ⁅ℂ⁆ Algebra A)
    (hn : ∀ j, n (h A j) = h A j - (A j i : ℂ) • h A i) (χ : ι → ℂ) :
    Module.finrank ℂ (weightSpace A (reflectWeight A i χ)) =
      Module.finrank ℂ (weightSpace A χ) := by
  rw [← weightSpace_map_of_cartan_reflection A i hii n hn χ]
  exact n.toLinearEquiv.finrank_map_eq _

theorem weightSpace_ne_bot_of_cartan_reflection (i : ι) (hii : A i i = 2)
    (n : Algebra A ≃ₗ⁅ℂ⁆ Algebra A)
    (hn : ∀ j, n (h A j) = h A j - (A j i : ℂ) • h A i) (χ : ι → ℂ) :
    weightSpace A (reflectWeight A i χ) ≠ ⊥ ↔ weightSpace A χ ≠ ⊥ := by
  rw [← weightSpace_map_of_cartan_reflection A i hii n hn χ]
  exact Submodule.map_ne_bot_iff

/-- Pure assembly from exact root support and multiplicities; this does not
assume finite dimensionality of the whole Serre algebra. -/
theorem finite_dimensional_of_weight_data
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (R : Set E) (hR : IsRootSystem R) (b : Module.Basis ι ℝ E)
    (hA : CartanConditions A)
    (hInd : iSupIndep (weightSpace A))
    (hsupport : ∀ χ : ι → ℂ, χ ≠ 0 →
      (weightSpace A χ ≠ ⊥ ↔ ∃ a ∈ R, χ = rootWeight b a))
    (hmult : ∀ a ∈ R, Module.finrank ℂ (weightSpace A (rootWeight b a)) = 1)
    (hzero : weightSpace A 0 = cartan A) :
    Module.Finite ℂ (Algebra A) ∧
      Module.finrank ℂ (Algebra A) = Fintype.card ι + Nat.card R := by
  classical
  letI : Fintype R := hR.finite.fintype
  let χ : Option R → (ι → ℂ) := fun o => o.elim 0 (fun a => rootWeight b a.val)
  have hw0 : rootWeight b (0 : E) = 0 := by
    ext i
    simp [rootWeight, rootCartan]
  have hnz (a : R) : rootWeight b a.val ≠ 0 := by
    intro ha
    have hz : a.val = 0 := rootWeight_injective b (ha.trans hw0.symm)
    exact hR.nonzero a.val a.property hz
  have hχ : Function.Injective χ := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some a => exact False.elim (hnz a hxy.symm)
    | some a =>
      cases y with
      | none => exact False.elim (hnz a hxy)
      | some c =>
        congr 1
        exact Subtype.ext (rootWeight_injective b hxy)
  let W : Option R → Submodule ℂ (Algebra A) := fun o => weightSpace A (χ o)
  have hi : iSupIndep W := hInd.comp hχ
  have htop : (⨆ o, W o) = ⊤ := by
    apply top_unique
    rw [← weightSpace_iSup_eq_top A]
    apply iSup_le
    intro ψ
    by_cases hψ : ψ = 0
    · subst ψ
      exact le_iSup W none
    · by_cases hbot : weightSpace A ψ = ⊥
      · rw [hbot]; exact bot_le
      · obtain ⟨a, ha, rfl⟩ := (hsupport ψ hψ).mp hbot
        exact le_iSup W (some ⟨a, ha⟩)
  have hW (o : Option R) : Module.Finite ℂ (W o) := by
    cases o with
    | none =>
      change Module.Finite ℂ (weightSpace A 0)
      rw [hzero]
      obtain ⟨bc, _⟩ := (triangular_of_cartanConditions A hA).2.1
      exact Module.Finite.of_basis bc
    | some a =>
      exact Module.finite_of_finrank_eq_succ (hmult a.val a.property)
  letI : ∀ o, Module.Finite ℂ (W o) := hW
  let e : (Π₀ o, W o) ≃ₗ[ℂ] Algebra A := hi.linearEquiv htop
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  change Module.finrank ℂ (⨁ o, W o) = _
  rw [Module.finrank_directSum, Fintype.sum_option]
  change Module.finrank ℂ (weightSpace A 0) +
      ∑ a : R, Module.finrank ℂ (weightSpace A (rootWeight b a.val)) = _
  have hdim0 : Module.finrank ℂ (weightSpace A 0) = Fintype.card ι := by
    rw [hzero]
    exact cartan_finrank A hA
  rw [hdim0]
  simp only [hmult _ (Subtype.property _),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card]

end LieAlgebrasAndRepresentations.Serre

noncomputable section
namespace LieAlgebrasAndRepresentations.Serre

/-- A nonempty bracket word in a family of generators. -/
inductive BracketWord (ι : Type*)
  | generator : ι → BracketWord ι
  | bracket : BracketWord ι → BracketWord ι → BracketWord ι

namespace BracketWord
variable {ι L : Type*} [LieRing L] [LieAlgebra ℂ L]

def evaluate (E : ι → L) : BracketWord ι → L
  | generator i => E i
  | bracket u v => ⁅evaluate E u, evaluate E v⁆

variable [DecidableEq ι]
def degree : BracketWord ι → (ι →₀ ℕ)
  | generator i => Finsupp.single i 1
  | bracket u v => degree u + degree v

theorem degree_ne_zero (w : BracketWord ι) : w.degree ≠ 0 := by
  induction w with
  | generator i => simp [degree]
  | bracket u v hu hv =>
    intro h
    exact hu (add_eq_zero.mp h).1

theorem span_evaluate_lie_closed (E : ι → L) {x y : L}
    (hx : x ∈ Submodule.span ℂ (Set.range (evaluate E)))
    (hy : y ∈ Submodule.span ℂ (Set.range (evaluate E))) :
    ⁅x,y⁆ ∈ Submodule.span ℂ (Set.range (evaluate E)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact Submodule.subset_span ⟨bracket u v, rfl⟩
    | zero => simpa only [lie_zero] using Submodule.zero_mem _
    | add y z _ _ hy hz => simpa only [lie_add] using Submodule.add_mem _ hy hz
    | smul c y _ hy => simpa only [lie_smul] using Submodule.smul_mem _ c hy
  | zero => simpa only [zero_lie] using Submodule.zero_mem _
  | add x z _ _ hx hz => simpa only [add_lie] using Submodule.add_mem _ hx hz
  | smul c x _ hx => simpa only [smul_lie] using Submodule.smul_mem _ c hx

/-- Words span precisely the Lie algebra generated by their letters. -/
theorem span_evaluate_eq_lieSpan (E : ι → L) :
    Submodule.span ℂ (Set.range (evaluate E)) =
      (LieSubalgebra.lieSpan ℂ L (Set.range E)).toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    induction w with
    | generator i => exact LieSubalgebra.subset_lieSpan ⟨i, rfl⟩
    | bracket u v hu hv => exact (LieSubalgebra.lieSpan ℂ L (Set.range E)).lie_mem hu hv
  · let S : LieSubalgebra ℂ L :=
      { Submodule.span ℂ (Set.range (evaluate E)) with
        lie_mem' := span_evaluate_lie_closed E }
    change LieSubalgebra.lieSpan ℂ L (Set.range E) ≤ S
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨generator i, rfl⟩

/-- The scalar weight of a word is the same sum, with repeated letters counted. -/
def wordWeight (A : Matrix ι ι ℤ) : BracketWord ι → (ι → ℂ)
  | generator i => fun j => (A j i : ℂ)
  | bracket u v => wordWeight A u + wordWeight A v

variable (A : Matrix ι ι ℤ)

theorem positive_weight (w : BracketWord ι) :
    w.evaluate (e A) ∈ weightSpace A (w.wordWeight A) := by
  induction w with
  | generator i =>
    intro j
    change ⁅h A j, e A i⁆ = (A j i : ℂ) • e A i
    rw [he, Int.cast_smul_eq_zsmul]
  | bracket u v hu hv =>
    intro i
    change ⁅h A i, ⁅u.evaluate (e A), v.evaluate (e A)⁆⁆ =
      ((u.wordWeight A) i + (v.wordWeight A) i) • _
    simpa only [evaluate] using (show ⁅h A i, ⁅u.evaluate (e A), v.evaluate (e A)⁆⁆ = _ from by
      rw [leibniz_lie, hu i, hv i, smul_lie, lie_smul, add_smul])

theorem negative_weight (w : BracketWord ι) :
    w.evaluate (f A) ∈ weightSpace A (-w.wordWeight A) := by
  induction w with
  | generator i =>
    intro j
    change ⁅h A j, f A i⁆ = -(A j i : ℂ) • f A i
    rw [hf, neg_smul, Int.cast_smul_eq_zsmul]
  | bracket u v hu hv =>
    intro i
    change ⁅h A i, ⁅u.evaluate (f A), v.evaluate (f A)⁆⁆ =
      -((u.wordWeight A) i + (v.wordWeight A) i) • _
    simpa only [evaluate, Pi.neg_apply] using (show ⁅h A i, ⁅u.evaluate (f A), v.evaluate (f A)⁆⁆ = _ from by
      rw [leibniz_lie, hu i, hv i, smul_lie, lie_smul, neg_add, add_smul]
      rfl)

/-- A word using a single letter evaluates either to that letter or to zero. -/
theorem evaluate_eq_generator_or_zero (E : ι → L) (i : ι) (w : BracketWord ι)
    (hw : ∀ j, j ≠ i → w.degree j = 0) :
    w.evaluate E = E i ∨ w.evaluate E = 0 := by
  induction w with
  | generator j =>
    have hji : j = i := by
      by_contra hji
      have := hw j hji
      simpa [degree] using this
    subst j
    exact Or.inl rfl
  | bracket u v hu hv =>
    have hdu : ∀ j, j ≠ i → u.degree j = 0 := by
      intro j hji
      exact (Nat.add_eq_zero_iff.mp (hw j hji)).1
    have hdv : ∀ j, j ≠ i → v.degree j = 0 := by
      intro j hji
      exact (Nat.add_eq_zero_iff.mp (hw j hji)).2
    right
    rcases hu hdu with hu | hu <;> rcases hv hdv with hv | hv <;>
      simp [evaluate, hu, hv]

/-- A surviving word supported on one letter has that letter's single degree. -/
theorem degree_eq_single_of_evaluate_ne_zero (E : ι → L) (i : ι) (w : BracketWord ι)
    (hw : ∀ j, j ≠ i → w.degree j = 0) (hne : w.evaluate E ≠ 0) :
    w.degree = Finsupp.single i 1 := by
  cases w with
  | generator j =>
    have hji : j = i := by
      by_contra hji
      have := hw j hji
      simpa [degree] using this
    subst j
    rfl
  | bracket u v =>
    have hdu : ∀ j, j ≠ i → u.degree j = 0 := by
      intro j hji
      exact (Nat.add_eq_zero_iff.mp (hw j hji)).1
    have hdv : ∀ j, j ≠ i → v.degree j = 0 := by
      intro j hji
      exact (Nat.add_eq_zero_iff.mp (hw j hji)).2
    exfalso
    apply hne
    rcases u.evaluate_eq_generator_or_zero E i hdu with hu | hu <;>
      rcases v.evaluate_eq_generator_or_zero E i hdv with hv | hv <;>
      simp [evaluate, hu, hv]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rootVector (b : ι → E) : BracketWord ι → E
  | generator i => b i
  | bracket u v => rootVector b u + rootVector b v

theorem rootVector_repr (b : Module.Basis ι ℝ E) (w : BracketWord ι) (i : ι) :
    b.repr (w.rootVector b) i = (w.degree i : ℝ) := by
  induction w with
  | generator j =>
    by_cases h : j = i
    · subst j; simp [rootVector, degree, Module.Basis.repr_self]
    · simp [rootVector, degree, Module.Basis.repr_self, Finsupp.single_apply, h]
  | bracket u v hu hv => simp [rootVector, degree, map_add, hu, hv]

theorem rootVector_ne_zero (b : Module.Basis ι ℝ E) (w : BracketWord ι) :
    w.rootVector b ≠ 0 := by
  intro hw
  have hd : w.degree = 0 := by
    ext i
    have hi := rootVector_repr b w i
    rw [hw, map_zero, Finsupp.zero_apply] at hi
    exact_mod_cast hi.symm
  exact w.degree_ne_zero hd

theorem rootVector_weight (b : ι → E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) (w : BracketWord ι) :
    rootWeight b (w.rootVector b) = w.wordWeight A := by
  induction w with
  | generator j =>
    funext i
    change (rootCartan (b j) (b i) : ℂ) = (A i j : ℂ)
    exact_mod_cast (hA i j).symm
  | bracket u v hu hv =>
    funext i
    change (rootCartan (u.rootVector b + v.rootVector b) (b i) : ℂ) =
      u.wordWeight A i + v.wordWeight A i
    rw [rootCartan_add, Complex.ofReal_add]
    rw [← congrFun hu i, ← congrFun hv i]
    rfl

end BracketWord

variable {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℤ)

def positiveWordSpace (χ : ι → ℂ) : Submodule ℂ (Algebra A) :=
  Submodule.span ℂ {x | ∃ w : BracketWord ι,
    w.wordWeight A = χ ∧ w.evaluate (e A) = x}

def negativeWordSpace (χ : ι → ℂ) : Submodule ℂ (Algebra A) :=
  Submodule.span ℂ {x | ∃ w : BracketWord ι,
    -w.wordWeight A = χ ∧ w.evaluate (f A) = x}

def signedWordSpace (χ : ι → ℂ) : Submodule ℂ (Algebra A) := by
  classical
  exact negativeWordSpace A χ ⊔ ((if χ = 0 then cartan A else ⊥) ⊔ positiveWordSpace A χ)

theorem positiveWordSpace_le (χ : ι → ℂ) :
    positiveWordSpace A χ ≤ weightSpace A χ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl, rfl⟩
  exact w.positive_weight A

theorem negativeWordSpace_le (χ : ι → ℂ) :
    negativeWordSpace A χ ≤ weightSpace A χ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl, rfl⟩
  exact w.negative_weight A

theorem signedWordSpace_le (χ : ι → ℂ) :
    signedWordSpace A χ ≤ weightSpace A χ := by
  classical
  unfold signedWordSpace
  apply sup_le (negativeWordSpace_le A χ)
  apply sup_le _ (positiveWordSpace_le A χ)
  split_ifs with hχ
  · subst χ
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩ i
    simpa using hh A i j
  · exact bot_le

theorem signedWordSpace_iSup_eq_top : (⨆ χ, signedWordSpace A χ) = ⊤ := by
  apply top_unique
  rw [← triangularSpan_eq_top A]
  apply sup_le
  · change (LieSubalgebra.lieSpan ℂ (Algebra A) (Set.range (f A))).toSubmodule ≤ _
    rw [← BracketWord.span_evaluate_eq_lieSpan (f A)]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    apply (le_iSup (fun χ => signedWordSpace A χ) (-w.wordWeight A))
    exact (show negativeWordSpace A (-w.wordWeight A) ≤
      signedWordSpace A (-w.wordWeight A) from le_sup_left)
        (Submodule.subset_span ⟨w, rfl, rfl⟩)
  · apply sup_le
    · apply le_trans _ (le_iSup (fun χ => signedWordSpace A χ) 0)
      simp only [signedWordSpace, if_pos rfl]
      exact le_sup_right.trans' le_sup_left
    · change (LieSubalgebra.lieSpan ℂ (Algebra A) (Set.range (e A))).toSubmodule ≤ _
      rw [← BracketWord.span_evaluate_eq_lieSpan (e A)]
      apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      apply (le_iSup (fun χ => signedWordSpace A χ) (w.wordWeight A))
      exact (show positiveWordSpace A (w.wordWeight A) ≤
        signedWordSpace A (w.wordWeight A) from le_sup_right.trans' le_sup_right)
          (Submodule.subset_span ⟨w, rfl, rfl⟩)

/-- Independence of ordinary eigenspaces isolates the words of each weight. -/
theorem weightSpace_eq_signedWordSpace
    (hind : iSupIndep (weightSpace A)) (χ : ι → ℂ) :
    weightSpace A χ = signedWordSpace A χ := by
  have h := (hind.le_iff_eq_of_iSup_eq_top (signedWordSpace_iSup_eq_top A)).mp
    (signedWordSpace_le A)
  exact (congrFun h χ).symm


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rootWeight_zero (b : ι → E) : rootWeight b 0 = 0 := by
  funext i
  simp [rootWeight, rootCartan]

theorem rootWeight_neg (b : ι → E) (a : E) : rootWeight b (-a) = -rootWeight b a := by
  funext i
  simp [rootWeight, rootCartan, neg_div]

theorem wordWeight_ne_zero (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) (w : BracketWord ι) :
    w.wordWeight A ≠ 0 := by
  intro hw
  apply w.rootVector_ne_zero b
  apply rootWeight_injective b
  rw [w.rootVector_weight A b hA, hw, rootWeight_zero]

theorem positiveWordSpace_zero_eq_bot (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) :
    positiveWordSpace A 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  exact False.elim (wordWeight_ne_zero A b hA w hw)

theorem negativeWordSpace_zero_eq_bot (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) :
    negativeWordSpace A 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  exact False.elim (wordWeight_ne_zero A b hA w (neg_eq_zero.mp hw))

theorem zero_weightSpace_eq_cartan (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) :
    weightSpace A 0 = cartan A := by
  rw [weightSpace_eq_signedWordSpace A (weightSpace_iSupIndep A)]
  simp [signedWordSpace, positiveWordSpace_zero_eq_bot A b hA,
    negativeWordSpace_zero_eq_bot A b hA]

theorem positiveWordSpace_simple_le (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) (i : ι) :
    positiveWordSpace A (rootWeight b (b i)) ≤ Submodule.span ℂ {e A i} := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  have hr : w.rootVector b = b i := by
    apply rootWeight_injective b
    rwa [w.rootVector_weight A b hA]
  have hd : ∀ j, j ≠ i → w.degree j = 0 := by
    intro j hji
    have hc := w.rootVector_repr b j
    rw [hr] at hc
    simpa [Module.Basis.repr_self, hji] using hc.symm
  rcases w.evaluate_eq_generator_or_zero (e A) i hd with hw | hw
  · rw [hw]
    exact Submodule.subset_span (Set.mem_singleton _)
  · rw [hw]
    exact Submodule.zero_mem _

theorem negativeWordSpace_simple_eq_bot (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) (i : ι) :
    negativeWordSpace A (rootWeight b (b i)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  have hr : -w.rootVector b = b i := by
    apply rootWeight_injective b
    rwa [rootWeight_neg, w.rootVector_weight A b hA]
  have hc := w.rootVector_repr b i
  have hc' : b.repr (-w.rootVector b) i = 1 := by rw [hr]; simp
  rw [map_neg, Finsupp.neg_apply, hc] at hc'
  have hnonneg : (0 : ℝ) ≤ (w.degree i : ℝ) := Nat.cast_nonneg _
  linarith

theorem simple_weightSpace_eq_span (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) (i : ι) :
    weightSpace A (rootWeight b (b i)) = Submodule.span ℂ {e A i} := by
  have hi : rootWeight b (b i) ≠ 0 := by
    intro hi
    apply b.ne_zero i
    apply rootWeight_injective b
    rw [hi, rootWeight_zero]
  apply le_antisymm
  · rw [weightSpace_eq_signedWordSpace A (weightSpace_iSupIndep A)]
    simp only [signedWordSpace, negativeWordSpace_simple_eq_bot A b hA i,
      ite_eq_right hi, bot_sup_eq]
    exact positiveWordSpace_simple_le A b hA i
  · apply Submodule.span_le.mpr
    rintro _ rfl
    have hw := (BracketWord.generator i).rootVector_weight A b hA
    change rootWeight b (b i) = (fun j => (A j i : ℂ)) at hw
    rw [hw]
    exact e_mem_weightSpace A i


theorem nonzero_weight_word (χ : ι → ℂ) (hχ : χ ≠ 0)
    (hne : weightSpace A χ ≠ ⊥) :
    ∃ w : BracketWord ι,
      (χ = w.wordWeight A ∧ w.evaluate (e A) ≠ 0) ∨
      (χ = -w.wordWeight A ∧ w.evaluate (f A) ≠ 0) := by
  classical
  have hor : positiveWordSpace A χ ≠ ⊥ ∨ negativeWordSpace A χ ≠ ⊥ := by
    by_contra! hh
    apply hne
    rw [weightSpace_eq_signedWordSpace A (weightSpace_iSupIndep A)]
    simp [signedWordSpace, hh.1, hh.2, hχ]
  rcases hor with hp | hn
  · have hh : ∃ w : BracketWord ι, χ = w.wordWeight A ∧ w.evaluate (e A) ≠ 0 := by
      by_contra! hwords
      apply hp
      apply Submodule.span_eq_bot.mpr
      rintro _ ⟨w, hw, rfl⟩
      exact hwords w hw.symm
    obtain ⟨w, hw⟩ := hh
    exact ⟨w, Or.inl hw⟩
  · have hh : ∃ w : BracketWord ι, χ = -w.wordWeight A ∧ w.evaluate (f A) ≠ 0 := by
      by_contra! hwords
      apply hn
      apply Submodule.span_eq_bot.mpr
      rintro _ ⟨w, hw, rfl⟩
      exact hwords w hw.symm
    obtain ⟨w, hw⟩ := hh
    exact ⟨w, Or.inr hw⟩

theorem BracketWord.axis_scalar_eq_one (b : Module.Basis ι ℝ E)
    (G : ι → Algebra A) (i : ι) (w : BracketWord ι) (c : ℝ)
    (hw : w.rootVector b = c • b i) (hne : w.evaluate G ≠ 0) : c = 1 := by
  have hsupport : ∀ j, j ≠ i → w.degree j = 0 := by
    intro j hji
    have hc := w.rootVector_repr b j
    rw [hw] at hc
    simpa [map_smul, Module.Basis.repr_self, hji] using hc.symm
  have hd := w.degree_eq_single_of_evaluate_ne_zero G i hsupport hne
  have hc := w.rootVector_repr b i
  rw [hw, hd] at hc
  simpa using hc

theorem weight_axis_scalar (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) (i : ι) (c : ℝ)
    (hc : c ≠ 0) (hne : weightSpace A (rootWeight b (c • b i)) ≠ ⊥) :
    c = 1 ∨ c = -1 := by
  have hχ : rootWeight b (c • b i) ≠ 0 := by
    intro hz
    have hv : c • b i = 0 := by
      apply rootWeight_injective b
      rw [hz, rootWeight_zero]
    exact (smul_ne_zero hc (b.ne_zero i)) hv
  obtain ⟨w, ⟨hw, he⟩ | ⟨hw, hf⟩⟩ := nonzero_weight_word A _ hχ hne
  · left
    apply w.axis_scalar_eq_one A b (e A) i c _ he
    apply rootWeight_injective b
    rw [w.rootVector_weight A b hA]
    exact hw.symm
  · right
    have hv : w.rootVector b = (-c) • b i := by
      apply rootWeight_injective b
      rw [neg_smul, rootWeight_neg, w.rootVector_weight A b hA, hw, neg_neg]
    have hminus := w.axis_scalar_eq_one A b (f A) i (-c) hv hf
    linarith

theorem weight_axis_nat_eq_one (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) (i : ι) (n : ℕ)
    (hne : weightSpace A (rootWeight b ((n : ℝ) • b i)) ≠ ⊥ ∨
      weightSpace A (rootWeight b (-((n : ℝ) • b i))) ≠ ⊥)
    (hn : n ≠ 0) : n = 1 := by
  rcases hne with hp | hm
  · rcases weight_axis_scalar A b hA i (n : ℝ) (by exact_mod_cast hn) hp with hh | hh
    · exact_mod_cast hh
    · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
  · have hm' : weightSpace A (rootWeight b ((-(n : ℝ)) • b i)) ≠ ⊥ := by
      simpa only [neg_smul] using hm
    rcases weight_axis_scalar A b hA i (-(n : ℝ)) (neg_ne_zero.mpr (by exact_mod_cast hn)) hm' with hh | hh
    · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
    · have hh' : (n : ℝ) = 1 := by linarith
      exact_mod_cast hh'


theorem BracketWord.rootVector_eq_sum [Fintype ι]
    (b : Module.Basis ι ℝ E) (w : BracketWord ι) :
    w.rootVector b = ∑ i, (w.degree i : ℝ) • b i := by
  apply b.repr.injective
  ext j
  rw [w.rootVector_repr b j]
  simp [Finset.sum_apply, Finsupp.single_apply]

/-- Every actual nonzero complex weight is a signed positive lattice weight. -/
theorem weight_signed_lattice [Fintype ι] (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    (χ : ι → ℂ) (hχ : χ ≠ 0) (hne : weightSpace A χ ≠ ⊥) :
    ∃ c : ι → ℕ,
      χ = rootWeight b (∑ i, (c i : ℝ) • b i) ∨
      χ = rootWeight b (-(∑ i, (c i : ℝ) • b i)) := by
  obtain ⟨w, ⟨hw, he⟩ | ⟨hw, hf⟩⟩ := nonzero_weight_word A χ hχ hne
  · refine ⟨w.degree, Or.inl ?_⟩
    rw [← w.rootVector_eq_sum b, w.rootVector_weight A b hA]
    exact hw
  · refine ⟨w.degree, Or.inr ?_⟩
    rw [← w.rootVector_eq_sum b, rootWeight_neg, w.rootVector_weight A b hA]
    exact hw

end LieAlgebrasAndRepresentations.Serre

noncomputable section
open scoped BigOperators
open Module
namespace LieAlgebrasAndRepresentations
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

def natLatticeVector (b : Basis ι ℝ E) (c : ι → ℕ) : E :=
  ∑ i, (c i : ℝ) • b i

@[simp] lemma repr_natLatticeVector (b : Basis ι ℝ E) (c : ι → ℕ) (j : ι) :
    b.repr (natLatticeVector b c) j = (c j : ℝ) := by
  simp [natLatticeVector, Finset.sum_apply, Finsupp.single_apply]

lemma natLatticeVector_eq_zero_iff (b : Basis ι ℝ E) (c : ι → ℕ) :
    natLatticeVector b c = 0 ↔ c = 0 := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun x => b.repr x i) h
    simpa using hi
  · rintro rfl
    simp [natLatticeVector]

lemma natLatticeVector_inner_pos (b : Basis ι ℝ E) (c : ι → ℕ)
    (hc : natLatticeVector b c ≠ 0) :
    ∃ i, 0 < inner ℝ (natLatticeVector b c) (b i) := by
  by_contra! h
  have hp := real_inner_self_pos.mpr hc
  have heq : inner ℝ (natLatticeVector b c) (natLatticeVector b c) =
      ∑ i, (c i : ℝ) * inner ℝ (natLatticeVector b c) (b i) := by
    conv_lhs => rhs; unfold natLatticeVector
    simp only [inner_sum, real_inner_smul_right]
  have hn : ∑ i, (c i : ℝ) * inner ℝ (natLatticeVector b c) (b i) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (h i))
  linarith

/-- An arbitrary reflection-stable set of signed positive lattice vectors
with only simple roots on its positive coordinate axes has no additional vectors. -/
theorem root_mem_of_signed_lattice_reflection_of_neg
    {R : Set E} (hR : IsRootSystem R) {z : E}
    (b : Basis ι ℝ E) (hb : IsSimpleBasis R z b) (P : E → Prop)
    (hsign : ∀ x, P x → x ≠ 0 →
      ∃ c : ι → ℕ, x = natLatticeVector b c ∨ x = -natLatticeVector b c)
    (hreflect : ∀ i x, P x → P (rootReflection (b i) x))
    (haxis : ∀ (i : ι) (n : ℕ), P ((n : ℝ) • b i) → n ≠ 0 → n = 1)
    (hneg : ∀ x, P x → P (-x))
    {x : E} (hx : P x) (hxne : x ≠ 0) : x ∈ R := by
  have hpos : ∀ n : ℕ, ∀ c : ι → ℕ, (∑ i, c i) = n →
      P (natLatticeVector b c) → natLatticeVector b c ≠ 0 → natLatticeVector b c ∈ R := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc hPc hcne
      obtain ⟨i, hi⟩ := natLatticeVector_inner_pos b c hcne
      by_cases hsingle : ∀ j, j ≠ i → c j = 0
      · have hvec : natLatticeVector b c = (c i : ℝ) • b i := by
          unfold natLatticeVector
          exact Finset.sum_eq_single i (fun j _ hji => by simp [hsingle j hji]) (by simp)
        have hci : c i ≠ 0 := by
          intro hzero
          exact hcne (by simp [hvec, hzero])
        rw [hvec, haxis i (c i) (hvec ▸ hPc) hci]
        simpa using hb.root_mem i
      · push Not at hsingle
        obtain ⟨j, hji', hj'⟩ := hsingle
        let y := rootReflection (b i) (natLatticeVector b c)
        have hyP : P y := hreflect i _ hPc
        have hyne : y ≠ 0 := by
          intro hy
          apply hcne
          calc
            natLatticeVector b c = rootReflection (b i) y := (reflection_involutive _ _).symm
            _ = 0 := by rw [hy]; simp [rootReflection]
        obtain ⟨d, hd | hd⟩ := hsign y hyP hyne
        · have hcart : 0 < rootCartan (natLatticeVector b c) (b i) :=
            div_pos (mul_pos two_pos hi) (real_inner_self_pos.mpr (b.ne_zero i))
          have heq : (∑ k, (d k : ℝ)) = (∑ k, (c k : ℝ)) -
              rootCartan (natLatticeVector b c) (b i) := by
            have hm := congrArg (fun v : E => ∑ k, b.repr v k) hd
            simpa [y, rootReflection, rootCartan, map_sub, map_smul, Finset.sum_sub_distrib,
              Finsupp.single_apply] using hm.symm
          have hlt : (∑ k, d k) < n := by
            have hlt' : (∑ k, (d k : ℝ)) < ∑ k, (c k : ℝ) := by linarith
            have hnat : (∑ k, d k) < ∑ k, c k := by exact_mod_cast hlt'
            simpa [hc] using hnat
          have hyd : natLatticeVector b d ∈ R := ih _ hlt d rfl (hd ▸ hyP) (hd ▸ hyne)
          have hm := hR.reflection_mem (b i) (hb.root_mem i) _ hyd
          simpa [← hd, y, reflection_involutive] using hm
        · have heq := congrArg (fun v : E => b.repr v j) hd
          have hn : (c j : ℝ) = -(d j : ℝ) := by
            simpa [y, rootReflection, map_sub, map_smul, hji', Finsupp.single_apply,
              Ne.symm hji'] using heq
          have hcj : 0 < (c j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj'
          have hdj : 0 ≤ (d j : ℝ) := Nat.cast_nonneg _
          linarith
  obtain ⟨c, hc | hc⟩ := hsign x hx hxne
  · exact hc ▸ hpos _ c rfl (hc ▸ hx) (hc ▸ hxne)
  · have hc' : -x = natLatticeVector b c := by rw [hc, neg_neg]
    have hm : -x ∈ R := hc' ▸ hpos _ c rfl (hc' ▸ hneg x hx) (hc' ▸ neg_ne_zero.mpr hxne)
    simpa using hR.toRootAxioms.neg_mem hm

/-- Version requiring axis control on both signs, with no negation stability. -/
theorem root_mem_of_signed_lattice_reflection
    {R : Set E} (hR : IsRootSystem R) {z : E}
    (b : Basis ι ℝ E) (hb : IsSimpleBasis R z b) (P : E → Prop)
    (hsign : ∀ x, P x → x ≠ 0 →
      ∃ c : ι → ℕ, x = natLatticeVector b c ∨ x = -natLatticeVector b c)
    (hreflect : ∀ i x, P x → P (rootReflection (b i) x))
    (haxis : ∀ (i : ι) (n : ℕ),
      (P ((n : ℝ) • b i) ∨ P (-((n : ℝ) • b i))) → n ≠ 0 → n = 1)
    {x : E} (hx : P x) (hxne : x ≠ 0) : x ∈ R := by
  apply root_mem_of_signed_lattice_reflection_of_neg hR b hb (fun a => P a ∨ P (-a))
    (x := x) (hx := Or.inl hx) (hxne := hxne)
  · intro a ha hane
    rcases ha with ha | ha
    · exact hsign a ha hane
    · obtain ⟨c, hc | hc⟩ := hsign (-a) ha (neg_ne_zero.mpr hane)
      · exact ⟨c, Or.inr (by rw [← hc, neg_neg])⟩
      · exact ⟨c, Or.inl (by simpa using congrArg Neg.neg hc)⟩
  · intro i a ha
    rcases ha with ha | ha
    · exact Or.inl (hreflect i a ha)
    · right
      have hm := hreflect i (-a) ha
      have hneg : rootReflection (b i) (-a) = -rootReflection (b i) a := by
        simpa using reflection_smul (b i) a (-1 : ℝ)
      rwa [hneg] at hm
  · exact haxis
  · intro a ha
    simpa [or_comm] using ha

end LieAlgebrasAndRepresentations

namespace LieAlgebrasAndRepresentations.Serre
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma rootCartan_reflection (a x c : E) :
    rootCartan (rootReflection a x) c = rootCartan x c - rootCartan x a * rootCartan a c := by
  simp only [rootReflection, rootCartan, inner_sub_left, real_inner_smul_left]
  ring

lemma rootWeight_reflection (A : Matrix ι ι ℤ) (b : Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) (i : ι) (x : E) :
    rootWeight b (rootReflection (b i) x) = reflectWeight A i (rootWeight b x) := by
  ext j
  simp only [rootWeight, reflectWeight, rootCartan_reflection, Complex.ofReal_sub,
    Complex.ofReal_mul]
  have hc : (A j i : ℂ) = (rootCartan (b i) (b j) : ℂ) := by
    exact_mod_cast hA j i
  rw [hc]
  ring

end LieAlgebrasAndRepresentations.Serre

namespace LieAlgebrasAndRepresentations.Serre
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

/-- Height descent excludes all additional complex weights once triangular
signed support and the pure-one-generator multidegrees have been established. -/
theorem nonzero_weight_is_root_of_lattice_data
    (A : Matrix ι ι ℤ) (hCartan : CartanConditions A)
    {R : Set E} (hR : IsRootSystem R) {z : E}
    (b : Basis ι ℝ E) (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    (hsigned : ∀ χ : ι → ℂ, χ ≠ 0 → weightSpace A χ ≠ ⊥ →
      ∃ c : ι → ℕ,
        χ = rootWeight b (natLatticeVector b c) ∨
        χ = rootWeight b (-natLatticeVector b c))
    (haxis : ∀ (i : ι) (n : ℕ),
      (weightSpace A (rootWeight b ((n : ℝ) • b i)) ≠ ⊥ ∨
       weightSpace A (rootWeight b (-((n : ℝ) • b i))) ≠ ⊥) → n ≠ 0 → n = 1)
    {χ : ι → ℂ} (hχ : χ ≠ 0) (hws : weightSpace A χ ≠ ⊥) :
    ∃ a ∈ R, χ = rootWeight b a := by
  have hw0 : rootWeight b (0 : E) = 0 := by
    ext i
    simp [rootWeight, rootCartan]
  have hnz : ∀ a : E, a ≠ 0 → rootWeight b a ≠ 0 := by
    intro a ha hzero
    exact ha (rootWeight_injective b (hzero.trans hw0.symm))
  have hroot : ∀ a : E, a ≠ 0 → weightSpace A (rootWeight b a) ≠ ⊥ → a ∈ R := by
    intro a ha hPa
    apply root_mem_of_signed_lattice_reflection hR b hb
      (fun v => weightSpace A (rootWeight b v) ≠ ⊥) (x := a) (hx := hPa) (hxne := ha)
    · intro v hv hvne
      obtain ⟨c, hc | hc⟩ := hsigned (rootWeight b v) (hnz v hvne) hv
      · exact ⟨c, Or.inl (rootWeight_injective b hc)⟩
      · exact ⟨c, Or.inr (rootWeight_injective b hc)⟩
    · intro i v hv
      rw [rootWeight_reflection A b hA]
      obtain ⟨ep, fm, _, _, hcart, hmap⟩ := (reflections_spec A hCartan).2 i
      rw [← hmap]
      exact Submodule.map_ne_bot_iff.mpr hv
    · exact haxis
  obtain ⟨c, hc | hc⟩ := hsigned χ hχ hws
  · have hne : natLatticeVector b c ≠ 0 := by
      intro hz
      exact hχ (hc.trans (hz ▸ hw0))
    exact ⟨natLatticeVector b c, hroot _ hne (hc ▸ hws), hc⟩
  · have hne : -natLatticeVector b c ≠ 0 := by
      intro hz
      exact hχ (hc.trans (hz ▸ hw0))
    exact ⟨-natLatticeVector b c, hroot _ hne (hc ▸ hws), hc⟩

end LieAlgebrasAndRepresentations.Serre

noncomputable section
namespace LieAlgebrasAndRepresentations.Serre
variable {ι E : Type*} [DecidableEq ι] (A : Matrix ι ι ℤ) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem simple_weightSpace_finrank (b : Module.Basis ι ℝ E)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    (hC : CartanConditions A) (i : ι) :
    Module.finrank ℂ (weightSpace A (rootWeight b (b i))) = 1 := by
  rw [simple_weightSpace_eq_span A b hA i]
  exact finrank_span_singleton ((triangular_of_cartanConditions A hC).2.2.2.2 i).1

end LieAlgebrasAndRepresentations.Serre

noncomputable section
namespace LieAlgebrasAndRepresentations.Serre
universe u v
variable {E : Type v} {ι : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [DecidableEq ι]

/-- Simple-root multiplicity one propagates to every prescribed root by the
actual terminating exponential Lie automorphisms. -/
theorem root_space_finrank_one_of_simple (A : Matrix ι ι ℤ)
    (R : Set E) (hR : IsRootSystem R) (z : E) (hz : RootRegular R z)
    (b : Module.Basis ι ℝ E) (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    (hsimple : ∀ i, Module.finrank ℂ (weightSpace A (rootWeight b (b i))) = 1) :
    ∀ a ∈ R, Module.finrank ℂ (weightSpace A (rootWeight b a)) = 1 := by
  have hC : CartanConditions A := cartanConditions_spec R hR z hz b hb A hA
  apply root_property_of_simple_reflections hR hz
    (fun a => Module.finrank ℂ (weightSpace A (rootWeight b a)) = 1)
  · intro a ha
    obtain ⟨i, rfl⟩ := hb.symm ▸ ha
    exact hsimple i
  · intro a ha x hx
    obtain ⟨i, rfl⟩ := hb.symm ▸ ha
    let n := ((positiveExp A i).trans (negativeExp A i)).trans (positiveExp A i)
    have hdim := weightSpace_finrank_of_cartan_reflection A i (hC.1 i) n
      (exponential_reflection_cartan A i (hC.1 i)) (rootWeight b x)
    rw [← rootWeight_reflection A b hA i x] at hdim
    exact hdim.trans hx

/-- Every prescribed root has multiplicity one in the actual Serre algebra. -/
theorem root_space_finrank_one (A : Matrix ι ι ℤ)
    (R : Set E) (hR : IsRootSystem R) (z : E) (hz : RootRegular R z)
    (b : Module.Basis ι ℝ E) (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) :
    ∀ a ∈ R, Module.finrank ℂ (weightSpace A (rootWeight b a)) = 1 := by
  exact root_space_finrank_one_of_simple A R hR z hz b hb hA
    (simple_weightSpace_finrank A b hA (cartanConditions_spec R hR z hz b hb A hA))

/-- Prescribed roots really occur as ordinary weights once the simple-root
lines and genuine reflection actions have been established. -/
theorem root_space_ne_bot (A : Matrix ι ι ℤ)
    (R : Set E) (hR : IsRootSystem R) (z : E) (hz : RootRegular R z)
    (b : Module.Basis ι ℝ E) (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    (a : E) (ha : a ∈ R) : weightSpace A (rootWeight b a) ≠ ⊥ := by
  intro hbot
  have hdim := root_space_finrank_one A R hR z hz b hb hA a ha
  rw [hbot] at hdim
  simp at hdim

end LieAlgebrasAndRepresentations.Serre

namespace LieAlgebrasAndRepresentations.Serre
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

/-- Every nonzero ordinary joint weight of the finite-type Serre presentation
is a root of the prescribed Euclidean root system. -/
theorem nonzero_weight_is_root
    (A : Matrix ι ι ℤ) {R : Set E} (hR : IsRootSystem R)
    {z : E} (hz : RootRegular R z) (b : Module.Basis ι ℝ E) (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    {χ : ι → ℂ} (hχ : χ ≠ 0) (hws : weightSpace A χ ≠ ⊥) :
    ∃ a ∈ R, χ = rootWeight b a := by
  apply nonzero_weight_is_root_of_lattice_data A
    (cartanConditions_spec R hR z hz b hb A hA) hR b hb hA
    (hχ := hχ) (hws := hws)
  · intro ψ hψ hne
    simpa only [natLatticeVector] using weight_signed_lattice A b hA ψ hψ hne
  · exact weight_axis_nat_eq_one A b hA

end LieAlgebrasAndRepresentations.Serre

noncomputable section
namespace LieAlgebrasAndRepresentations.Serre
universe u v

/-- Finite type for the actual Serre presentation, including all ordinary
complex weights, multiplicities, the zero space, and the total dimension. -/
theorem finiteType_spec :
    Specs.LieAlgebrasAndRepresentations.SerreFiniteType.finiteTypeExpected.{u,v} := by
  intro E _ _ ι _ _ R hR z hz b hb A hA
  have hC : CartanConditions A := cartanConditions_spec R hR z hz b hb A hA
  have hmult := root_space_finrank_one A R hR z hz b hb hA
  have hzero := zero_weightSpace_eq_cartan A b hA
  have hsupport : ∀ χ : ι → ℂ, χ ≠ 0 →
      (weightSpace A χ ≠ ⊥ ↔ ∃ a ∈ R, χ = rootWeight b a) := by
    intro χ hχ
    constructor
    · intro hne
      exact nonzero_weight_is_root A hR hz b hb hA hχ hne
    · rintro ⟨a, ha, rfl⟩
      exact root_space_ne_bot A R hR z hz b hb hA a ha
  obtain ⟨hfinite, hdim⟩ := finite_dimensional_of_weight_data A R hR b hC
    (weightSpace_iSupIndep A) hsupport hmult hzero
  exact ⟨hfinite, weightSpace_iSup_eq_top A, hsupport, hmult,
    hzero, cartan_finrank A hC, hdim⟩

end LieAlgebrasAndRepresentations.Serre
