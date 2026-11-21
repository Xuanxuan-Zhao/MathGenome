import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Aesop

/-! The complete matrix root calculation for the symplectic Lie algebra (LA-D08-C). -/

namespace LieAlgebrasAndRepresentations.ClassicalRootsC
open Matrix
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC

noncomputable section
attribute [local instance] LieRing.ofAssociativeRing

theorem block_form : block_form_type := by
  intro n A B C D
  simp only [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    Matrix.J, Matrix.mul_neg, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero, neg_neg, neg_zero]
  constructor
  · rintro ⟨hC, hA, hD, hB⟩
    exact ⟨hC, neg_injective hB, hA.symm⟩
  · rintro ⟨hC,hB,hD⟩
    subst D
    simp [hC,hB]

theorem diagonal_mem : diagonal_mem_type := by
  intro n t
  have h : Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t =
      Matrix.fromBlocks (Matrix.diagonal t) 0 0 (-Matrix.diagonal t) := by
    rw [Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
    rfl
  rw [h, block_form]
  simp

theorem bracket_diagonal (n : ℕ) (t : V n) (X : Mat n) (a b : Fin n ⊕ Fin n) :
    ⁅Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t, X⁆ a b = (signed a t - signed b t) * X a b := by
  simp only [Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal, Ring.lie_def, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  have hs (a : Fin n ⊕ Fin n) : Sum.elim t (-t) a = signed a t := by
    cases a <;> rfl
  rw [hs a, hs b]
  ring

theorem rootSpace_entries : rootSpace_entries_type := by
  intro n α X
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun a b hX => LinearMap.ext fun t => ?_⟩
    have he := congrArg (fun M : Mat n => M a b) (h t)
    rw [bracket_diagonal] at he
    change (signed a t - signed b t) * X a b = α t * X a b at he
    exact (mul_right_cancel₀ hX he).symm
  · rintro ⟨hx,h⟩
    refine ⟨hx, fun t => ?_⟩
    ext a b
    rw [bracket_diagonal]
    change (signed a t - signed b t) * X a b = α t * X a b
    by_cases hX : X a b = 0
    · simp [hX]
    · rw [h a b hX]
      rfl

/-- All simultaneous weight spaces have disjoint entry supports. This also
proves independence of arbitrary finite sums, not just pairwise disjointness. -/
theorem independent : independent_type := by
  intro n α
  rw [Submodule.disjoint_def]
  intro X hx hy
  ext a b
  by_contra hn
  have hw := (rootSpace_entries n α X).mp hx |>.2 a b hn
  have hz : ∀ Y ∈ (⨆ (β : Weight n) (_ : β ≠ α), rootSpace β), Y a b = 0 := by
    have hle : (⨆ (β : Weight n) (_ : β ≠ α), rootSpace β) ≤
        LinearMap.ker ((Matrix.entryLinearMap ℂ ℂ a b)) := by
      refine iSup_le fun β => iSup_le fun hβα => ?_
      intro Y hY
      change Y a b = 0
      by_contra hne
      exact hβα (((rootSpace_entries n β Y).mp hY).2 a b hne |>.trans hw.symm)
    intro Y hY
    exact hle hY
  exact hn (hz X hy)

/-- The symplectic equation relates the two Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal blocks. -/
theorem block_relations {n : ℕ} (X : Mat n) (hX : X ∈ sp n) :
    X.toBlocks₂₁ᵀ = X.toBlocks₂₁ ∧ X.toBlocks₁₂ᵀ = X.toBlocks₁₂ ∧
      X.toBlocks₂₂ = -X.toBlocks₁₁ᵀ := by
  apply (block_form n _ _ _ _).mp
  simpa only [Matrix.fromBlocks_toBlocks] using hX

private theorem centralizer_isDiag {n : ℕ} (X : Mat n)
    (hX : ∀ t : V n, ⁅Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t, X⁆ = 0) : X.IsDiag := by
  have h : ∀ a b, X a b ≠ 0 → ∀ t : V n,
      (0 : ℂ) = signed a t - signed b t := by
    intro a b hab t
    have he := congrArg (fun M : Mat n => M a b) (hX t)
    rw [bracket_diagonal] at he
    exact (mul_eq_zero.mp he).resolve_right hab |>.symm
  intro a b hab
  by_contra hne
  rcases a with a | a <;> rcases b with b | b
  · have hn : a ≠ b := fun e => hab (congrArg Sum.inl e)
    have he := h _ _ hne (Pi.single a 1)
    simpa [signed, eps, Pi.single_apply, hn] using he
  · have he := h _ _ hne (Pi.single a 1)
    by_cases hn : a = b <;> norm_num [signed, eps, Pi.single_apply, hn] at he
  · have he := h _ _ hne (Pi.single a 1)
    by_cases hn : a = b <;> norm_num [signed, eps, Pi.single_apply, hn] at he
  · have hn : a ≠ b := fun e => hab (congrArg Sum.inr e)
    have he := h _ _ hne (Pi.single a 1)
    simpa [signed, eps, Pi.single_apply, hn] using he

theorem zero_space : zero_space_type := by
  intro n
  ext X
  constructor
  · rintro ⟨hx, h⟩
    have hd := centralizer_isDiag X (by simpa using h)
    refine ⟨fun i => X (Sum.inl i) (Sum.inl i), ?_⟩
    have hD := (block_relations X hx).2.2
    have hd' := hd.diagonal_diag
    ext a b
    rw [← hd']
    cases a with
    | inl a => cases b with
      | inl b => simp [diagonalMap, Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal, Matrix.diagonal, Matrix.diag]
      | inr b => simp [diagonalMap, Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal, Matrix.diagonal]
    | inr a => cases b with
      | inl b => simp [diagonalMap, Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal, Matrix.diagonal]
      | inr b =>
        have hb := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a a) hD
        simp only [Matrix.toBlocks₂₂, Matrix.toBlocks₁₁, Matrix.neg_apply,
          Matrix.transpose_apply, Matrix.of_apply] at hb
        simp [diagonalMap, Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal, Matrix.diagonal, Matrix.diag, hb]
  · rintro ⟨t,rfl⟩
    refine ⟨diagonal_mem n t, fun u => ?_⟩
    ext a b
    rw [bracket_diagonal]
    change (signed a u - signed b u) * Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t a b = (0 : ℂ) * Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t a b
    by_cases hab : a = b
    · subst b
      simp
    · simp [Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal, Matrix.diagonal, hab]

private theorem long_weight {n : ℕ} (i : Fin n) (a b : Fin n ⊕ Fin n) :
    signed a - signed b = (2:ℂ) • eps i ↔ a = Sum.inl i ∧ b = Sum.inr i := by
  constructor
  · intro h
    have hi := congrArg (fun f : Weight n => f (Pi.single i 1)) h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        by_cases ha : a=i <;> by_cases hb : b=i <;>
          simp [signed, eps, ha, hb] at hi <;> try norm_num at hi
      | inr b =>
        by_cases ha : a=i <;> by_cases hb : b=i <;>
          simp [signed, eps, ha, hb] at hi <;> try norm_num at hi
        exact ⟨congrArg Sum.inl ha, congrArg Sum.inr hb⟩
    | inr a =>
      cases b with
      | inl b =>
        by_cases ha : a=i <;> by_cases hb : b=i <;>
          simp [signed, eps, ha, hb] at hi <;> try norm_num at hi
      | inr b =>
        by_cases ha : a=i <;> by_cases hb : b=i <;>
          simp [signed, eps, ha, hb] at hi <;> try norm_num at hi
  · rintro ⟨rfl, rfl⟩
    simp [signed, two_smul]

private theorem diff_weight {n : ℕ} (i j : Fin n) (hij : i≠j) (a b : Fin n ⊕ Fin n) :
    signed a - signed b = eps i - eps j ↔
      (a = Sum.inl i ∧ b = Sum.inl j) ∨ (a = Sum.inr j ∧ b = Sum.inr i) := by
  constructor
  · intro h
    have hi := congrArg (fun f : Weight n => f (Pi.single i 1)) h
    have hj := congrArg (fun f : Weight n => f (Pi.single j 1)) h
    rcases a with a|a <;> rcases b with b|b <;>
      by_cases hai : a=i <;> by_cases hbi : b=i <;>
      by_cases haj : a=j <;> by_cases hbj : b=j <;>
      simp [signed,eps,hai,hbi,haj,hbj,hij,hij.symm] at hi hj ⊢ <;>
      try norm_num at hi <;> try norm_num at hj
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [signed]
    abel

private theorem sum_weight {n : ℕ} (i j : Fin n) (hij : i≠j) (a b : Fin n ⊕ Fin n) :
    signed a - signed b = eps i + eps j ↔
      (a = Sum.inl i ∧ b = Sum.inr j) ∨ (a = Sum.inl j ∧ b = Sum.inr i) := by
  constructor
  · intro h
    have hi := congrArg (fun f : Weight n => f (Pi.single i 1)) h
    have hj := congrArg (fun f : Weight n => f (Pi.single j 1)) h
    rcases a with a|a <;> rcases b with b|b <;>
      by_cases hai : a=i <;> by_cases hbi : b=i <;>
      by_cases haj : a=j <;> by_cases hbj : b=j <;>
      simp [signed,eps,hai,hbi,haj,hbj,hij,hij.symm] at hi hj ⊢ <;>
      try norm_num at hi <;> try norm_num at hj
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [signed]
    abel

private theorem entry_relations {n : ℕ} (X : Mat n) (hx : X∈sp n) :
    (∀ i j, X (Sum.inr i) (Sum.inr j) = -X (Sum.inl j) (Sum.inl i)) ∧
    (∀ i j, X (Sum.inl i) (Sum.inr j) = X (Sum.inl j) (Sum.inr i)) ∧
    (∀ i j, X (Sum.inr i) (Sum.inl j) = X (Sum.inr j) (Sum.inl i)) := by
  have hf := (block_form n X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂).mp
    (by simpa only [Matrix.fromBlocks_toBlocks] using hx)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hf.2.2
  · intro i j
    exact (congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hf.2.1).symm
  · intro i j
    exact (congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hf.1).symm

private theorem transpose_sp {n : ℕ} (X : Mat n) (hx : X∈sp n) : Xᵀ∈sp n := by
  have hf := (block_form n X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂).mp
    (by simpa only [Matrix.fromBlocks_toBlocks] using hx)
  rw [← Matrix.fromBlocks_toBlocks X, Matrix.fromBlocks_transpose]
  apply (block_form n _ _ _ _).mpr
  exact ⟨by simpa using hf.2.1.symm, by simpa using hf.1.symm,
    by rw [hf.2.2]; simp⟩

private theorem transpose_rootSpace {n : ℕ} (α : Weight n) (X : Mat n) :
    Xᵀ ∈ rootSpace (-α) ↔ X∈rootSpace α := by
  have hdir : ∀ (β : Weight n) (Y : Mat n), Y∈rootSpace β → Yᵀ∈rootSpace (-β) := by
    intro β Y hY
    rw [rootSpace_entries] at hY ⊢
    refine ⟨transpose_sp Y hY.1, ?_⟩
    intro a b h
    have he := hY.2 b a h
    rw [he]
    abel
  constructor
  · intro h
    simpa using hdir (-α) Xᵀ h
  · exact hdir α X

private theorem a_mem {n : ℕ} (i j : Fin n) (hij : i≠j) :
    aRoot i j ∈ rootSpace (eps i - eps j) := by
  rw [rootSpace_entries]
  refine ⟨?_, ?_⟩
  · apply (block_form n _ _ _ _).mpr
    simp [aRoot, Matrix.transpose_single]
  · intro a b h
    apply Eq.symm
    apply (diff_weight i j hij a b).mpr
    rcases a with a|a <;> rcases b with b|b <;>
      simp [aRoot, Matrix.single_apply] at h ⊢
    · exact ⟨h.1.symm, h.2.symm⟩
    · exact ⟨h.1.symm, h.2.symm⟩

private theorem b_mem {n : ℕ} (i j : Fin n) (hij : i≠j) :
    bRoot i j ∈ rootSpace (eps i + eps j) := by
  rw [rootSpace_entries]
  refine ⟨?_, ?_⟩
  · apply (block_form n _ _ _ _).mpr
    simp [bRoot, Matrix.transpose_single, add_comm]
  · intro a b h
    apply Eq.symm
    apply (sum_weight i j hij a b).mpr
    rcases a with a|a <;> rcases b with b|b <;>
      simp [bRoot, Matrix.single_apply] at h ⊢
    by_cases hai : i=a <;> by_cases hbj : j=b <;>
      by_cases haj : j=a <;> by_cases hbi : i=b <;> simp_all

private theorem bLong_mem {n : ℕ} (i : Fin n) :
    bLong i ∈ rootSpace ((2:ℂ) • eps i) := by
  rw [rootSpace_entries]
  refine ⟨?_, ?_⟩
  · apply (block_form n _ _ _ _).mpr
    simp [bLong, Matrix.transpose_single]
  · intro a b h
    apply Eq.symm
    apply (long_weight i a b).mpr
    rcases a with a|a <;> rcases b with b|b <;>
      simp [bLong, Matrix.single_apply] at h ⊢
    exact ⟨h.1.symm, h.2.symm⟩

theorem a_space : a_space_type := by
  intro n i j hij
  apply le_antisymm
  · intro X hx
    rw [Submodule.mem_span_singleton]
    refine ⟨X (Sum.inl i) (Sum.inl j), ?_⟩
    have hr := (rootSpace_entries n _ X).mp hx
    have hb := (entry_relations X hr.1).1 j i
    have hs : ∀ a b, X a b ≠ 0 →
        (a = Sum.inl i ∧ b = Sum.inl j) ∨ (a = Sum.inr j ∧ b = Sum.inr i) :=
      fun a b h => (diff_weight i j hij a b).mp (hr.2 a b h).symm
    have hgen := (rootSpace_entries n _ _).mp (a_mem i j hij)
    have hsg : ∀ a b, aRoot i j a b ≠ 0 →
        (a = Sum.inl i ∧ b = Sum.inl j) ∨ (a = Sum.inr j ∧ b = Sum.inr i) :=
      fun a b h => (diff_weight i j hij a b).mp (hgen.2 a b h).symm
    ext a b
    by_cases h1 : a=Sum.inl i ∧ b=Sum.inl j
    · rcases h1 with ⟨rfl,rfl⟩
      simp [aRoot, Matrix.smul_apply]
    by_cases h2 : a=Sum.inr j ∧ b=Sum.inr i
    · rcases h2 with ⟨rfl,rfl⟩
      simp [aRoot, Matrix.smul_apply, hb]
    have hz : X a b=0 := by
      by_contra h
      exact (hs a b h).elim h1 h2
    have hgz : aRoot i j a b=0 := by
      by_contra h
      exact (hsg a b h).elim h1 h2
    simp [Matrix.smul_apply, hz, hgz]
  · exact Submodule.span_le.mpr (by simpa using a_mem i j hij)

theorem b_space : b_space_type := by
  intro n i j hij
  apply le_antisymm
  · intro X hx
    rw [Submodule.mem_span_singleton]
    refine ⟨X (Sum.inl i) (Sum.inr j), ?_⟩
    have hr := (rootSpace_entries n _ X).mp hx
    have hb := (entry_relations X hr.1).2.1 i j
    have hs : ∀ a b, X a b ≠ 0 →
        (a = Sum.inl i ∧ b = Sum.inr j) ∨ (a = Sum.inl j ∧ b = Sum.inr i) :=
      fun a b h => (sum_weight i j hij a b).mp (hr.2 a b h).symm
    have hgen := (rootSpace_entries n _ _).mp (b_mem i j hij)
    have hsg : ∀ a b, bRoot i j a b ≠ 0 →
        (a = Sum.inl i ∧ b = Sum.inr j) ∨ (a = Sum.inl j ∧ b = Sum.inr i) :=
      fun a b h => (sum_weight i j hij a b).mp (hgen.2 a b h).symm
    ext a b
    by_cases h1 : a=Sum.inl i ∧ b=Sum.inr j
    · rcases h1 with ⟨rfl,rfl⟩
      simp [bRoot, Matrix.smul_apply, hij, hij.symm]
    by_cases h2 : a=Sum.inl j ∧ b=Sum.inr i
    · rcases h2 with ⟨rfl,rfl⟩
      simp [bRoot, Matrix.smul_apply, hij, hij.symm, hb]
    have hz : X a b=0 := by
      by_contra h
      exact (hs a b h).elim h1 h2
    have hgz : bRoot i j a b=0 := by
      by_contra h
      exact (hsg a b h).elim h1 h2
    simp [Matrix.smul_apply, hz, hgz]
  · exact Submodule.span_le.mpr (by simpa using b_mem i j hij)

theorem b_long_space : b_long_space_type := by
  intro n i
  apply le_antisymm
  · intro X hx
    rw [Submodule.mem_span_singleton]
    refine ⟨X (Sum.inl i) (Sum.inr i), ?_⟩
    have hr := (rootSpace_entries n _ X).mp hx
    have hs : ∀ a b, X a b ≠ 0 → a=Sum.inl i ∧ b=Sum.inr i :=
      fun a b h => (long_weight i a b).mp (hr.2 a b h).symm
    have hgen := (rootSpace_entries n _ _).mp (bLong_mem i)
    have hsg : ∀ a b, bLong i a b ≠ 0 → a=Sum.inl i ∧ b=Sum.inr i :=
      fun a b h => (long_weight i a b).mp (hgen.2 a b h).symm
    ext a b
    by_cases h1 : a=Sum.inl i ∧ b=Sum.inr i
    · rcases h1 with ⟨rfl,rfl⟩
      simp [bLong, Matrix.smul_apply]
    have hz : X a b=0 := by
      by_contra h
      exact h1 (hs a b h)
    have hgz : bLong i a b=0 := by
      by_contra h
      exact h1 (hsg a b h)
    simp [Matrix.smul_apply, hz, hgz]
  · exact Submodule.span_le.mpr (by simpa using bLong_mem i)

theorem c_space : c_space_type := by
  intro n i j hij
  ext X
  rw [← transpose_rootSpace (-(eps i + eps j)) X, neg_neg,
    b_space n i j hij, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor <;> rintro ⟨c,hc⟩ <;> refine ⟨c, ?_⟩
  · have h := congrArg Matrix.transpose hc
    simpa [cRoot] using h
  · have h := congrArg Matrix.transpose hc
    simpa [cRoot] using h

theorem c_long_space : c_long_space_type := by
  intro n i
  ext X
  rw [← transpose_rootSpace (-((2:ℂ) • eps i)) X, neg_neg,
    b_long_space n i, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor <;> rintro ⟨c,hc⟩ <;> refine ⟨c, ?_⟩
  · have h := congrArg Matrix.transpose hc
    simpa [cLong] using h
  · have h := congrArg Matrix.transpose hc
    simpa [cLong] using h

private def weightComponent {n : ℕ} (X : Mat n) (α : Weight n) : Mat n := by
  classical
  exact fun a b => if α = signed a - signed b then X a b else 0

private theorem weightComponent_mem {n : ℕ} (X : Mat n) (hx : X∈sp n) (α : Weight n) :
    weightComponent X α ∈ rootSpace α := by
  classical
  rw [rootSpace_entries]
  have hf := (block_form n X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂).mp
    (by simpa only [Matrix.fromBlocks_toBlocks] using hx)
  constructor
  · rw [← Matrix.fromBlocks_toBlocks (weightComponent X α)]
    apply (block_form n _ _ _ _).mpr
    refine ⟨?_,?_,?_⟩
    · ext i j
      have hr := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hf.1
      change X (Sum.inr j) (Sum.inl i) = X (Sum.inr i) (Sum.inl j) at hr
      change (if α = signed (Sum.inr j) - signed (Sum.inl i) then X (Sum.inr j) (Sum.inl i) else 0) =
        (if α = signed (Sum.inr i) - signed (Sum.inl j) then X (Sum.inr i) (Sum.inl j) else 0)
      have hw : signed (Sum.inr j) - signed (Sum.inl i) = signed (Sum.inr i) - signed (Sum.inl j) := by
        simp [signed]; abel
      rw [hw, hr]
    · ext i j
      have hr := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hf.2.1
      change X (Sum.inl j) (Sum.inr i) = X (Sum.inl i) (Sum.inr j) at hr
      change (if α = signed (Sum.inl j) - signed (Sum.inr i) then X (Sum.inl j) (Sum.inr i) else 0) =
        (if α = signed (Sum.inl i) - signed (Sum.inr j) then X (Sum.inl i) (Sum.inr j) else 0)
      have hw : signed (Sum.inl j) - signed (Sum.inr i) = signed (Sum.inl i) - signed (Sum.inr j) := by
        simp [signed]; abel
      rw [hw, hr]
    · ext i j
      have hr := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hf.2.2
      change X (Sum.inr i) (Sum.inr j) = -X (Sum.inl j) (Sum.inl i) at hr
      change (if α = signed (Sum.inr i) - signed (Sum.inr j) then X (Sum.inr i) (Sum.inr j) else 0) =
        -(if α = signed (Sum.inl j) - signed (Sum.inl i) then X (Sum.inl j) (Sum.inl i) else 0)
      have hw : signed (Sum.inr i) - signed (Sum.inr j) = signed (Sum.inl j) - signed (Sum.inl i) := by
        simp [signed]; abel
      rw [hw, hr]
      split_ifs <;> simp
  · intro a b hab
    by_cases h : α = signed a - signed b
    · exact h
    · simp [weightComponent, h] at hab

theorem spanning : spanning_type := by
  intro n
  apply le_antisymm
  · apply iSup_le
    intro α X hx
    exact hx.1
  · intro X hx
    classical
    let W : Finset (Weight n) := Finset.univ.image
      (fun p : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) => signed p.1 - signed p.2)
    have hsum : (∑ α∈W, weightComponent X α) = X := by
      ext a b
      have hw : signed a - signed b ∈ W := Finset.mem_image.mpr ⟨(a,b), Finset.mem_univ _, rfl⟩
      simp [weightComponent, Matrix.sum_apply, hw]
    rw [← hsum]
    apply Submodule.sum_mem
    intro α hα
    exact (le_iSup rootSpace α) (weightComponent_mem X hx α)

private theorem listed_neg {n : ℕ} {α : Weight n} (hα : α∈listedRoots n) : -α∈listedRoots n := by
  rcases hα with ⟨i,h|h⟩ | ⟨i,j,hij,h|h|h|h⟩
  · subst α; exact Or.inl ⟨i, Or.inr rfl⟩
  · subst α; exact Or.inl ⟨i, Or.inl (neg_neg _)⟩
  · subst α; exact Or.inr ⟨i,j,hij,Or.inr (Or.inl rfl)⟩
  · subst α; exact Or.inr ⟨i,j,hij,Or.inl (neg_neg _)⟩
  · subst α; exact Or.inr ⟨i,j,hij,Or.inr (Or.inr (Or.inr rfl))⟩
  · subst α; exact Or.inr ⟨i,j,hij,Or.inr (Or.inr (Or.inl (neg_neg _)))⟩

private theorem listed_diff {n : ℕ} (i j : Fin n) (hij : i≠j) : eps i-eps j∈listedRoots n := by
  rcases lt_or_gt_of_ne hij with hij|hji
  · exact Or.inr ⟨i,j,hij,Or.inl rfl⟩
  · exact Or.inr ⟨j,i,hji,Or.inr (Or.inl (by abel))⟩

private theorem listed_sum {n : ℕ} (i j : Fin n) : eps i+eps j∈listedRoots n := by
  by_cases hij : i=j
  · subst j
    exact Or.inl ⟨i,Or.inl (by simp [two_smul])⟩
  · rcases lt_or_gt_of_ne hij with hij|hji
    · exact Or.inr ⟨i,j,hij,Or.inr (Or.inr (Or.inl rfl))⟩
    · exact Or.inr ⟨j,i,hji,Or.inr (Or.inr (Or.inl (add_comm _ _)))⟩

private theorem listed_entry {n : ℕ} (a b : Fin n⊕Fin n)
    (hne : signed a-signed b≠0) : signed a-signed b∈listedRoots n := by
  rcases a with a|a <;> rcases b with b|b
  · apply listed_diff
    intro h
    subst b
    exact hne (sub_self _)
  · simpa only [signed,sub_neg_eq_add] using listed_sum a b
  · convert listed_neg (listed_sum a b) using 1 <;> simp only [signed] <;> abel
  · have hab : b≠a := by
      intro h
      subst b
      exact hne (sub_self _)
    convert listed_diff b a hab using 1 <;> simp only [signed] <;> abel

private theorem roots_subset (n : ℕ) : rootSet n ⊆ listedRoots n := by
  intro α hα
  obtain ⟨X,hX,hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  obtain ⟨a,b,hab⟩ : ∃ a b, X a b≠0 := by
    by_contra! h
    apply hX0
    ext a b
    exact h a b
  have he := ((rootSpace_entries n α X).mp hX).2 a b hab
  rw [he]
  apply listed_entry
  exact he ▸ hα.1

private theorem root_of_entry {n : ℕ} (α : Weight n) (g : Mat n)
    (hg : g∈rootSpace α) (a b : Fin n⊕Fin n) (hab : a≠b) (hentry : g a b≠0) :
    α∈rootSet n := by
  constructor
  · intro hα
    subst α
    have hd := centralizer_isDiag g (fun t => by simpa using hg.2 t)
    exact hentry (hd hab)
  · intro hbot
    have hz : g=0 := by simpa [hbot] using hg
    exact hentry (by simp [hz])

private theorem root_neg {n : ℕ} {α : Weight n} (hα : α∈rootSet n) : -α∈rootSet n := by
  refine ⟨neg_ne_zero.mpr hα.1, ?_⟩
  obtain ⟨X,hX,hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  intro hbot
  have hxT := (transpose_rootSpace α X).mpr hX
  have hz : Xᵀ=0 := by simpa [hbot] using hxT
  apply hX0
  simpa using congrArg Matrix.transpose hz

private theorem root_long {n : ℕ} (i : Fin n) : (2:ℂ) • eps i∈rootSet n := by
  apply root_of_entry _ (bLong i) (bLong_mem i) (Sum.inl i) (Sum.inr i) (by simp)
  simp [bLong]

private theorem root_diff {n : ℕ} (i j : Fin n) (hij : i≠j) : eps i-eps j∈rootSet n := by
  apply root_of_entry _ (aRoot i j) (a_mem i j hij) (Sum.inl i) (Sum.inl j) (by simpa)
  simp [aRoot]

private theorem root_sum {n : ℕ} (i j : Fin n) (hij : i≠j) : eps i+eps j∈rootSet n := by
  apply root_of_entry _ (bRoot i j) (b_mem i j hij) (Sum.inl i) (Sum.inr j) (by simp)
  simp [bRoot, hij, hij.symm]

private theorem roots_superset (n : ℕ) : listedRoots n ⊆ rootSet n := by
  intro α hα
  rcases hα with ⟨i,h|h⟩ | ⟨i,j,hij,h|h|h|h⟩
  · subst α; exact root_long i
  · subst α; exact root_neg (root_long i)
  · subst α; exact root_diff i j hij.ne
  · subst α; exact root_neg (root_diff i j hij.ne)
  · subst α; exact root_sum i j hij.ne
  · subst α; exact root_neg (root_sum i j hij.ne)

theorem roots : roots_type := by
  intro n
  exact Set.Subset.antisymm (roots_subset n) (roots_superset n)

/-- At rank zero, the symplectic Lie algebra is zero and there are no roots. -/
theorem rank_zero : Subsingleton (sp 0) ∧ rootSet 0 = ∅ := by
  refine ⟨inferInstance, ?_⟩
  rw [roots 0]
  ext α
  simp [listedRoots]


lemma coordinates_eps {n : ℕ} (i : Fin n) : coordinates (eps i) = Pi.single i (1:ℂ) := by
  ext k
  simp [coordinates, eps, Pi.single_apply, eq_comm]

lemma coordinates_add {n : ℕ} (α β : Weight n) : coordinates (α+β) = coordinates α + coordinates β := by
  ext i; simp [coordinates]

lemma coordinates_sub {n : ℕ} (α β : Weight n) : coordinates (α-β) = coordinates α - coordinates β := by
  ext i; simp [coordinates]

lemma coordinates_smul {n : ℕ} (c : ℂ) (α : Weight n) : coordinates (c • α) = c • coordinates α := by
  ext i; simp [coordinates]

lemma euclidean_a {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    euclidean (eps i - eps j) (eps i - eps j) = 2 := by
  simp only [euclidean, coordinates_sub, coordinates_eps, Pi.sub_apply]
  norm_num [sub_mul, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, hij, hij.symm]

lemma euclidean_b {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    euclidean (eps i + eps j) (eps i + eps j) = 2 := by
  simp only [euclidean, coordinates_add, coordinates_eps, Pi.add_apply]
  norm_num [add_mul, mul_add, Finset.sum_add_distrib, Pi.single_apply, hij, hij.symm]

lemma euclidean_long {n : ℕ} (i : Fin n) :
    euclidean ((2:ℂ) • eps i) ((2:ℂ) • eps i) = 4 := by
  norm_num [euclidean, coordinates_smul, coordinates_eps, Pi.single_apply]

lemma coroot_a_formula {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    coroot (eps i - eps j) = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal (Pi.single i (1:ℂ) - Pi.single j (1:ℂ)) := by
  simp [coroot, euclidean_a i j hij, coordinates_sub, coordinates_eps]
  rfl

lemma coroot_b_formula {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    coroot (eps i + eps j) = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal (Pi.single i (1:ℂ) + Pi.single j (1:ℂ)) := by
  simp [coroot, euclidean_b i j hij, coordinates_add, coordinates_eps]
  rfl

lemma coroot_long_formula {n : ℕ} (i : Fin n) :
    coroot ((2:ℂ) • eps i) = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal (Pi.single i (1:ℂ)) := by
  unfold coroot
  rw [euclidean_long, coordinates_smul, coordinates_eps]
  congr 1
  ext k
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma neg_coroot : neg_coroot_type := by
  intro n α
  unfold coroot
  have he : euclidean (-α) (-α) = euclidean α α := by
    simp [euclidean, coordinates]
  rw [he]
  simp only [coordinates, LinearMap.neg_apply, mul_neg]
  ext (i | i) (j | j) <;> simp [Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal, Matrix.diagonal] <;> split_ifs <;> aesop

lemma diagonal_as_blocks {n : ℕ} (t : V n) :
    Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t = Matrix.fromBlocks (Matrix.diagonal t) 0 0 (-Matrix.diagonal t) := by
  unfold Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal
  rw [Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  rfl

lemma a_bracket {n : ℕ} (i j : Fin n) :
    ⁅aRoot i j, aRoot j i⁆ = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal (Pi.single i (1:ℂ) - Pi.single j (1:ℂ)) := by
  rw [diagonal_as_blocks]
  simp only [Ring.lie_def, aRoot, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    Matrix.single_mul_single_same, one_mul]
  have hd : Matrix.diagonal (Pi.single i (1:ℂ) - Pi.single j (1:ℂ)) =
      Matrix.single i i (1:ℂ) - Matrix.single j j (1:ℂ) := by
    ext k l
    by_cases h : k = l
    · subst l
      simp [Matrix.single, Matrix.diagonal, Pi.single_apply, eq_comm]
    · simp [Matrix.single, Matrix.diagonal, Pi.single_apply, h]
      split_ifs <;> aesop
  rw [hd]
  ext (k|k) (l|l) <;> simp [Matrix.fromBlocks, neg_sub]

lemma b_bracket {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ⁅bRoot i j, cRoot i j⁆ = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal (Pi.single i (1:ℂ) + Pi.single j (1:ℂ)) := by
  rw [diagonal_as_blocks]
  simp only [Ring.lie_def, bRoot, cRoot, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, Matrix.transpose_add, Matrix.transpose_single,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same, one_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    ]
  have hd : Matrix.diagonal (Pi.single i (1:ℂ) + Pi.single j (1:ℂ)) =
      Matrix.single i i (1:ℂ) + Matrix.single j j (1:ℂ) := by
    ext k l
    by_cases h : k = l
    · subst l
      simp [Matrix.single, Matrix.diagonal, Pi.single_apply, eq_comm]
    · simp [Matrix.single, Matrix.diagonal, Pi.single_apply, h]
      split_ifs <;> aesop
  rw [hd]
  ext (k|k) (l|l) <;> simp [Matrix.fromBlocks, add_comm]

lemma long_bracket {n : ℕ} (i : Fin n) :
    ⁅bLong i, cLong i⁆ = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal (Pi.single i (1:ℂ)) := by
  rw [diagonal_as_blocks]
  simp only [Ring.lie_def, bLong, cLong, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, Matrix.transpose_single, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.single_mul_single_same, one_mul, Matrix.diagonal_single]
  ext (k|k) (l|l) <;> simp [Matrix.fromBlocks]

lemma a_coroot : a_coroot_type := by
  intro n i j hij
  exact ⟨(a_bracket i j).trans (coroot_a_formula i j hij).symm, coroot_a_formula i j hij⟩

lemma b_coroot : b_coroot_type := by
  intro n i j hij
  exact ⟨(b_bracket i j hij).trans (coroot_b_formula i j hij).symm, coroot_b_formula i j hij⟩

lemma long_coroot : long_coroot_type := by
  intro n i
  exact ⟨(long_bracket i).trans (coroot_long_formula i).symm, coroot_long_formula i⟩


private theorem diagonal_comm {n : ℕ} (t u : V n) : ⁅Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t, Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal u⁆ = 0 := by
  ext a b
  rw [bracket_diagonal]
  by_cases hab : a = b
  · subst b; simp
  · simp [Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal, Matrix.diagonal, hab]

theorem cartan_transport : cartan_transport_type := by
  intro n
  let D : V n →ₗ[ℂ] sp n :=
    { toFun := fun t => ⟨Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t, diagonal_mem n t⟩
      map_add' := fun t u => Subtype.ext ((diagonalMap n).map_add t u)
      map_smul' := fun c t => Subtype.ext ((diagonalMap n).map_smul c t) }
  have hD : Function.Injective D := by
    intro t u h
    ext i
    have hi := congrArg (fun X : sp n => (X : Mat n) (Sum.inl i) (Sum.inl i)) h
    simpa [D, Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal] using hi
  have hcomm (t u : V n) : ⁅D t, D u⁆ = 0 := by
    apply Subtype.ext
    exact diagonal_comm t u
  let H : LieSubalgebra ℂ (sp n) :=
    { D.range with
      lie_mem' := by
        rintro X Y ⟨t,rfl⟩ ⟨u,rfl⟩
        rw [hcomm]
        exact D.range.zero_mem }
  let e : V n ≃ₗ[ℂ] H := LinearEquiv.ofInjective D hD
  have he (t : V n) : ((e t : sp n) : Mat n) = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t := rfl
  have hHcomm (x y : H) : ⁅x,y⁆ = 0 := by
    obtain ⟨t,ht⟩ := e.surjective x
    obtain ⟨u,hu⟩ := e.surjective y
    rw [← ht, ← hu]
    apply Subtype.ext
    exact hcomm t u
  let : IsLieAbelian H := ⟨hHcomm⟩
  have hCartan : H.IsCartanSubalgebra := by
    refine ⟨inferInstance, le_antisymm ?_ H.le_normalizer⟩
    intro X hx
    have hx' := (H.mem_normalizer_iff' X).mp hx
    have hz : (X : Mat n) ∈ rootSpace (0 : Weight n) := by
      refine ⟨X.property, fun t => ?_⟩
      have hm := hx' (D t) (show D t ∈ H from ⟨t,rfl⟩)
      obtain ⟨u, hu⟩ := hm
      have hbr : ⁅Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t, (X : Mat n)⁆ = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal u := by
        exact (congrArg (fun Y : sp n => (Y : Mat n)) hu).symm
      have hu0 : u = 0 := by
        ext i
        have hii := congrArg (fun Y : Mat n => Y (Sum.inl i) (Sum.inl i)) hbr
        rw [bracket_diagonal] at hii
        simpa [Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal] using hii.symm
      rw [hu0] at hbr
      simpa [Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal] using hbr
    rw [zero_space] at hz
    obtain ⟨t, ht⟩ := hz
    refine ⟨t, Subtype.ext ht⟩
  refine ⟨H, hCartan, e, he, fun α => ?_⟩
  ext X
  constructor
  · rintro ⟨Y,hY,rfl⟩
    refine ⟨Y.property, fun t => ?_⟩
    have ht := (LieModule.mem_weightSpace _ Y).mp hY (e t)
    have ht' := congrArg (fun Y : sp n => (Y : Mat n)) ht
    change ⁅((e t : sp n) : Mat n), (Y : Mat n)⁆ = α (e.symm (e t)) • (Y : Mat n) at ht'
    change ⁅Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t, (Y : Mat n)⁆ = α t • (Y : Mat n)
    rw [he, LinearEquiv.symm_apply_apply] at ht'
    exact ht'
  · rintro ⟨hx,hx'⟩
    refine ⟨⟨X,hx⟩, ?_, rfl⟩
    apply (LieModule.mem_weightSpace (fun h : H => α (e.symm h)) (⟨X,hx⟩ : sp n)).mpr
    intro h
    apply Subtype.ext
    have heh : ((h : sp n) : Mat n) = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal (e.symm h) := by
      rw [← he, e.apply_symm_apply]
    change ⁅((h : sp n) : Mat n), X⁆ = α (e.symm h) • X
    rw [heh]
    exact hx' (e.symm h)


end
end LieAlgebrasAndRepresentations.ClassicalRootsC
