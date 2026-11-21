import MathGenome.Internal.D07.Ch21.RegularDecomposition
import MathGenome.Internal.Specs.D07.Ch21.MultiplicityClassification
import Mathlib.LinearAlgebra.DirectSum.Basis

namespace D07.Ch21.MultiplicityClassification
universe u r v w x t s
noncomputable section
open Specs.D07.Ch21.MultiplicityClassification
open Specs.D07.Ch17.Characters Specs.D07.Ch21.HomPairing
open scoped Classical

section Sum
variable {G : Type u} [Group G] {J : Type t} {K : Type s}
  [Fintype J] [Fintype K] {A : J → Type v} {B : K → Type w}
  [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
  [∀ k, AddCommGroup (B k)] [∀ k, Module ℂ (B k)]

/-- Relabeling a finite external sum and replacing each summand by an equivalent one. -/
def sumEquiv (α : ∀ j, Representation ℂ G (A j))
    (β : ∀ k, Representation ℂ G (B k)) (e : K ≃ J)
    (f : ∀ k, (α (e k)).Equiv (β k)) :
    (Representation.directSum α).Equiv (Representation.directSum β) := by
  let dA : (DirectSum J A) ≃ₗ[ℂ] (∀ j, A j) := DFinsupp.linearEquivFunOnFintype
  let dB : (DirectSum K B) ≃ₗ[ℂ] (∀ k, B k) := DFinsupp.linearEquivFunOnFintype
  let re := (LinearEquiv.piCongrLeft ℂ A e).symm
  let fe := LinearEquiv.piCongrRight (fun k => (f k).toLinearEquiv)
  refine Representation.Equiv.mk (dA.trans (re.trans (fe.trans dB.symm))) ?_
  intro g
  apply LinearMap.ext
  intro a
  apply dB.injective
  ext k
  change f k (α (e k) g (a (e k))) = β k g (f k (a (e k)))
  exact Representation.IntertwiningMap.isIntertwining _ _ (f k).toIntertwiningMap g _

end Sum

section CharacterSum
variable {G : Type u} [Group G] {J : Type t} [Fintype J]
  {A : J → Type v} [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
  [∀ j, FiniteDimensional ℂ (A j)]

lemma character_sum (α : ∀ j, Representation ℂ G (A j)) (g : G) :
    LinearMap.trace ℂ (DirectSum J A) (Representation.directSum α g) =
      ∑ j, characterValue ℂ G (A j) (α j) g := by
  classical
  let b (j : J) := Module.finBasis ℂ (A j)
  let B := DFinsupp.basis b
  change LinearMap.trace ℂ (Π₀ j, A j) _ = ∑ j, LinearMap.trace ℂ (A j) (α j g)
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [show LinearMap.trace ℂ (A j) (α j g) =
    Matrix.trace (LinearMap.toMatrix (b j) (b j) (α j g)) from
      LinearMap.trace_eq_matrix_trace ℂ (b j) _]
  apply Finset.sum_congr rfl
  intro k _
  change (B.repr ((Representation.directSum α g) (B ⟨j,k⟩))) ⟨j,k⟩ = _
  simp [B, DFinsupp.basis, Module.Basis.coe_ofRepr, Representation.directSum,
    DirectSum.lmap, LinearMap.toMatrix_apply, DFinsupp.mapRange.linearMap]
  change (b j).repr (α j g ((DFinsupp.single j (b j k)) j)) k = _
  rw [DFinsupp.single_eq_same]

end CharacterSum

section Family
variable {G : Type u} [Group G] [Fintype G] {I : Type r} [Fintype I]
  {V : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (ρ : ∀ i, Representation ℂ G (V i))
  (hi : ∀ i, Representation.IsIrreducible (ρ i))
  (hne : ∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j)))
  (hc : Specs.D07.Ch21.RegularDecomposition.IsComplete ρ)

include hc in
lemma decomposition_exists {W : Type w} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (τ : Representation ℂ G W) :
    ∃ m : I → ℕ, Decomposes ρ τ m := by
  classical
  have hm : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  obtain ⟨n, U, e, hU, _⟩ :=
    D07.Ch17.CompleteReducibility.equivariant_decomposition ℂ G W hm τ
  have hh (j : Fin n) : ∃ i, Nonempty ((U j).toRepresentation.Equiv (ρ i)) := by
    obtain ⟨i, ⟨f⟩⟩ := RegularDecomposition.completeness_universal G I V ρ hc
      (U j).toSubmodule (U j).toRepresentation (hU j)
    exact ⟨i, ⟨f.symm⟩⟩
  choose a ha using hh
  let m (i : I) := Fintype.card {j : Fin n // a j = i}
  let q : (Σ i, Fin (m i)) ≃ Fin n :=
    (Equiv.sigmaCongrRight fun i => (Fintype.equivFin {j : Fin n // a j = i}).symm).trans
      (Equiv.sigmaFiberEquiv a)
  have hq (p : Σ i, Fin (m i)) : a (q p) = p.1 :=
    ((Fintype.equivFin {j : Fin n // a j = p.1}).symm p.2).property
  let fs (p : Σ i, Fin (m i)) : (U (q p)).toRepresentation.Equiv (ρ p.1) := by
    have hf := ha (q p)
    rw [hq p] at hf
    exact hf.some
  exact ⟨m, ⟨e.symm.trans (sumEquiv (fun j => (U j).toRepresentation)
    (fun p : Σ i, Fin (m i) => ρ p.1) q fs)⟩⟩

lemma character_expansion {W : Type w} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (τ : Representation ℂ G W) (m : I → ℕ)
    (h : Decomposes ρ τ m) (g : G) :
    characterValue ℂ G W τ g = ∑ i, (m i : ℂ) * characterValue ℂ G (V i) (ρ i) g := by
  classical
  obtain ⟨e⟩ := h
  change LinearMap.trace ℂ W (τ g) = _
  rw [← LinearMap.trace_conj' (τ g) e.toLinearEquiv, e.conj_apply_self g]
  rw [character_sum, Fintype.sum_sigma]
  change (∑ i, ∑ _ : Fin (m i), characterValue ℂ G (V i) (ρ i) g) = _
  simp

include hi hne in
lemma row_pairing (i j : I) :
    pairingValue G (characterValue ℂ G (V i) (ρ i))
      (characterValue ℂ G (V j) (ρ j)) = if i = j then 1 else 0 := by
  classical
  rw [MatrixOrthogonality.character_orthogonality G (V i) (V j) (ρ i) (ρ j) (hi i) (hi j)]
  by_cases h : i = j
  · subst j
    simp [show Nonempty ((ρ i).Equiv (ρ i)) from ⟨Representation.Equiv.refl _⟩]
  · simp [h, hne i j h]

lemma pairing_expansion_left (m : I → ℕ) (f : I → G → ℂ) (k : G → ℂ) :
    pairingValue G (fun g => ∑ i, (m i : ℂ) * f i g) k =
      ∑ i, (m i : ℂ) * pairingValue G (f i) k := by
  simp only [pairingValue, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro g _
  ring

lemma pairing_expansion_right (m : I → ℕ) (f : I → G → ℂ) (k : G → ℂ) :
    pairingValue G k (fun g => ∑ i, (m i : ℂ) * f i g) =
      ∑ i, (m i : ℂ) * pairingValue G k (f i) := by
  simp only [pairingValue, map_sum, map_mul, map_natCast, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro g _
  ring

include hi hne in
lemma multiplicity_formula {W : Type w} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (τ : Representation ℂ G W) (m : I → ℕ)
    (h : Decomposes ρ τ m) (j : I) :
    (m j : ℂ) = pairingValue G (characterValue ℂ G W τ)
      (characterValue ℂ G (V j) (ρ j)) := by
  classical
  rw [show characterValue ℂ G W τ =
    (fun g => ∑ i, (m i : ℂ) * characterValue ℂ G (V i) (ρ i) g) from
      funext (character_expansion ρ τ m h)]
  rw [pairing_expansion_left]
  simp only [row_pairing ρ hi hne, mul_ite, mul_one, mul_zero]
  simp

include hi hne in
lemma norm_formula {W : Type w} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (τ : Representation ℂ G W) (m : I → ℕ)
    (h : Decomposes ρ τ m) :
    pairingValue G (characterValue ℂ G W τ) (characterValue ℂ G W τ) =
      (∑ i, (m i)^2 : ℕ) := by
  conv_lhs => arg 3; rw [show characterValue ℂ G W τ =
    (fun g => ∑ i, (m i : ℂ) * characterValue ℂ G (V i) (ρ i) g) from
      funext (character_expansion ρ τ m h)]
  rw [pairing_expansion_right]
  simp only [← multiplicity_formula ρ hi hne τ m h, ← pow_two, Nat.cast_sum, Nat.cast_pow]

include hi hne in
lemma multiplicities_unique {W : Type w} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (τ : Representation ℂ G W) (m n : I → ℕ)
    (hm : Decomposes ρ τ m) (hn : Decomposes ρ τ n) : m = n := by
  funext j
  apply Nat.cast_injective (R := ℂ)
  rw [multiplicity_formula ρ hi hne τ m hm, multiplicity_formula ρ hi hne τ n hn]

include hi hne hc in
lemma equivalence_iff {W : Type w} {Z : Type x} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ W] [FiniteDimensional ℂ Z]
    (τ : Representation ℂ G W) (σ : Representation ℂ G Z) :
    Nonempty (τ.Equiv σ) ↔ characterValue ℂ G W τ = characterValue ℂ G Z σ := by
  constructor
  · exact D07.Ch17.Characters.character_equivalence ℂ G W Z τ σ
  · intro he
    obtain ⟨m, hm⟩ := decomposition_exists ρ hc τ
    obtain ⟨n, hn⟩ := decomposition_exists ρ hc σ
    have hmn : m = n := by
      funext j
      apply Nat.cast_injective (R := ℂ)
      rw [multiplicity_formula ρ hi hne τ m hm,
        multiplicity_formula ρ hi hne σ n hn, he]
    subst n
    exact ⟨hm.some.trans hn.some.symm⟩

include hi hne in
lemma hom_dimension {W : Type w} {Z : Type x} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ W] [FiniteDimensional ℂ Z]
    (τ : Representation ℂ G W) (σ : Representation ℂ G Z) (m n : I → ℕ)
    (hm : Decomposes ρ τ m) (hn : Decomposes ρ σ n) :
    Module.finrank ℂ (Representation.IntertwiningMap τ σ) = ∑ i, m i * n i := by
  apply Nat.cast_injective (R := ℂ)
  rw [← HomPairing.character_hom_pairing G W Z τ σ]
  conv_lhs => arg 3; rw [show characterValue ℂ G W τ =
    (fun g => ∑ i, (m i : ℂ) * characterValue ℂ G (V i) (ρ i) g) from
      funext (character_expansion ρ τ m hm)]
  rw [pairing_expansion_right]
  simp only [← multiplicity_formula ρ hi hne σ n hn, Nat.cast_sum, Nat.cast_mul]

/-- Transport of simplicity uses the actual group-algebra linear equivalence. -/
lemma irreducible_of_equiv {W : Type w} {Z : Type x} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup Z] [Module ℂ Z] {τ : Representation ℂ G W}
    {σ : Representation ℂ G Z} (e : τ.Equiv σ) (hσ : Representation.IsIrreducible σ) :
    Representation.IsIrreducible τ := by
  let q := Representation.IntertwiningMap.equivLinearMapAsModule τ σ e.toIntertwiningMap
  let f : τ.asModule ≃ₗ[MonoidAlgebra ℂ G] σ.asModule :=
    LinearEquiv.ofBijective q e.toLinearEquiv.bijective
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at hσ ⊢
  exact f.isSimpleModule_iff.mpr hσ

include hi hne hc in
lemma irreducible_iff_norm_one {W : Type w} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (τ : Representation ℂ G W) :
    Representation.IsIrreducible τ ↔
      pairingValue G (characterValue ℂ G W τ) (characterValue ℂ G W τ) = 1 := by
  classical
  constructor
  · intro hτ
    rw [MatrixOrthogonality.character_orthogonality G W W τ τ hτ hτ]
    simp [show Nonempty (τ.Equiv τ) from ⟨Representation.Equiv.refl _⟩]
  · intro hnorm
    obtain ⟨m, hm⟩ := decomposition_exists ρ hc τ
    have hs : ∑ i, (m i)^2 = 1 := by
      apply Nat.cast_injective (R := ℂ)
      rw [← norm_formula ρ hi hne τ m hm, hnorm, Nat.cast_one]
    obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
      by_contra! hz
      simp [hz] at hs
    have hsplit : m j ^ 2 + ∑ i ∈ Finset.univ.erase j, m i ^ 2 = 1 := by
      exact (Finset.add_sum_erase Finset.univ (fun i => m i ^ 2) (Finset.mem_univ j)).trans hs
    have hjpos : 0 < m j := Nat.pos_of_ne_zero hj
    have hsq : m j ^ 2 ≤ 1 := by omega
    have hmj : m j = 1 := Nat.le_antisymm ((sq_le_one_iff₀ (Nat.zero_le _)).mp hsq) hjpos
    have hrest : ∑ i ∈ Finset.univ.erase j, m i ^ 2 = 0 := by
      rw [hmj] at hsplit
      omega
    have hothers (i : I) (hij : i ≠ j) : m i = 0 := by
      have hz : m i ^ 2 = 0 := (Finset.sum_eq_zero_iff.mp hrest) i (by simp [hij])
      nlinarith
    have he : characterValue ℂ G W τ = characterValue ℂ G (V j) (ρ j) := by
      funext g
      rw [character_expansion ρ τ m hm, Finset.sum_eq_single j]
      · simp [hmj]
      · intro i _ hij
        simp [hothers i hij]
      · simp
    obtain ⟨e⟩ := (equivalence_iff ρ hi hne hc τ (ρ j)).mpr he
    exact irreducible_of_equiv e (hi j)

include hi hne hc in
lemma zero_space {W : Type w} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Subsingleton W] (τ : Representation ℂ G W) :
    characterValue ℂ G W τ = 0 ∧
    pairingValue G (characterValue ℂ G W τ) (characterValue ℂ G W τ) = 0 ∧
    ¬ Representation.IsIrreducible τ ∧ Decomposes ρ τ (fun _ => 0) ∧
    ∀ m, Decomposes ρ τ m → m = fun _ => 0 := by
  have hz : characterValue ℂ G W τ = 0 := by
    funext g
    change LinearMap.trace ℂ W (τ g) = 0
    rw [Subsingleton.elim (τ g) 0, map_zero]
  have hnorm : pairingValue G (characterValue ℂ G W τ)
      (characterValue ℂ G W τ) = 0 := by simp [hz, pairingValue]
  have hmzero (m : I → ℕ) (hm : Decomposes ρ τ m) : m = fun _ => 0 := by
    funext i
    apply Nat.cast_injective (R := ℂ)
    rw [multiplicity_formula ρ hi hne τ m hm]
    simp [hz, pairingValue]
  obtain ⟨m, hm⟩ := decomposition_exists ρ hc τ
  refine ⟨hz, hnorm, ?_, ?_, hmzero⟩
  · intro h
    have ho := (irreducible_iff_norm_one ρ hi hne hc τ).mp h
    rw [hnorm] at ho
    exact zero_ne_one ho
  · rwa [← hmzero m hm]

end Family

theorem classification : Classification.{u,r,v,w,x} := by
  intro G _ _ I _ V _ _ ρ hi hne hc
  have hfd : ∀ i, FiniteDimensional ℂ (V i) := fun i =>
    (RegularDecomposition.irreducible_finite G (V i) (ρ i) (hi i)).1
  refine ⟨hfd, ?_⟩
  letI := hfd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W _ _ _ τ
    exact decomposition_exists ρ hc τ
  · intro W _ _ _ τ m hm
    exact ⟨character_expansion ρ τ m hm, multiplicity_formula ρ hi hne τ m hm,
      norm_formula ρ hi hne τ m hm⟩
  · intro W _ _ _ τ m n hm hn
    exact multiplicities_unique ρ hi hne τ m n hm hn
  · intro W Z _ _ _ _ _ _ τ σ
    exact equivalence_iff ρ hi hne hc τ σ
  · intro W _ _ _ τ
    exact irreducible_iff_norm_one ρ hi hne hc τ
  · intro W Z _ _ _ _ _ _ τ σ m n hm hn
    exact hom_dimension ρ hi hne τ σ m n hm hn
  · intro W _ _ _ _ τ
    exact zero_space ρ hi hne hc τ

end
end D07.Ch21.MultiplicityClassification
