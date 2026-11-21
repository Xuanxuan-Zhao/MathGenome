import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SubmoduleTheorem
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.DominanceMultiplicity
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CycleTypes
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtClassification
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
open scoped BigOperators
universe u
namespace AdvancedFiniteGroupRepresentations

abbrev InheritedSpechtAction := @Specs.AdvancedFiniteGroupRepresentations.InheritedSpechtAction

theorem classification_irreducible {n : ℕ} (p : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hσ : InheritedSpechtAction p σ) : σ.IsIrreducible :=
  specht_irreducible p σ hσ

/-- An equivalence followed by the target inclusion is a nonzero map into M^q. -/
theorem dominance_of_specht_equiv {n : ℕ} (p q : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (τ : Representation ℂ (SymmetricGroup n) (SpechtModule q))
    (hσ : InheritedSpechtAction p σ) (hτ : InheritedSpechtAction q τ)
    (e : σ.Equiv τ) : dominates p q := by
  let f : SpechtHom p q := ⟨(spechtSpan q).subtype.comp e.toLinearMap, by
    intro g v w hw
    have he : w = σ g v := Subtype.ext (hw.trans (hσ g v).symm)
    subst w
    change (e (σ g v)).val = permutationRepresentation q g (e v).val
    exact (congrArg Subtype.val
      (Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap g v)).trans (hτ g (e v))⟩
  have hf : f ≠ 0 := by
    intro hz
    have h := congrArg (fun k : SpechtHom p q =>
      k.val (spechtPolytabloid (canonicalTableau p))) hz
    have hv : e (spechtPolytabloid (canonicalTableau p)) = 0 := Subtype.ext h
    have hz' : spechtPolytabloid (canonicalTableau p) = 0 := e.injective (by simpa using hv)
    exact polytabloid_ne_zero _ (congrArg Subtype.val hz')
  letI : Nontrivial (SpechtHom p q) := nontrivial_of_ne f 0 hf
  exact dominance_of_nonzero_hom p q inferInstance

theorem classification_distinct {n : ℕ} (p q : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (τ : Representation ℂ (SymmetricGroup n) (SpechtModule q))
    (hσ : InheritedSpechtAction p σ) (hτ : InheritedSpechtAction q τ)
    (he : Nonempty (σ.Equiv τ)) : p = q := by
  obtain ⟨e⟩ := he
  exact dominance_antisymm p q (dominance_of_specht_equiv p q σ τ hσ hτ e)
    (dominance_of_specht_equiv q p τ σ hτ hσ e.symm)

/-- Ordinary characters as functions on the conjugacy quotient. -/
private def classCharacter {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : ConjClasses G → ℂ :=
  Quotient.lift ρ.character (by
    intro g h hgh
    obtain ⟨s, hs⟩ := isConj_iff.mp hgh
    rw [← hs]
    exact (ρ.char_conj g s).symm)

@[simp] private theorem classCharacter_mk {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (g : G) :
    classCharacter ρ (ConjClasses.mk g) = ρ.character g := rfl

/-- The complex-linear pairing against a fixed character, using inverses. -/
private def characterPair {G : Type*} [Group G] [Fintype G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    (ConjClasses G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Nat.card G : ℂ)⁻¹ * ∑ g : G, f (ConjClasses.mk g) * ρ.character g⁻¹
  map_add' f h := by
    simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' a f := by
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

private abbrev canonicalSpecht {n : ℕ} (p : Partition n) :=
  (spechtSubrepresentation p).toRepresentation

private theorem canonicalSpecht_inherited {n : ℕ} (p : Partition n) :
    InheritedSpechtAction p (canonicalSpecht p) := fun _ _ => rfl

private theorem specht_character_pair {n : ℕ} (p q : Partition n) :
    characterPair (canonicalSpecht q) (classCharacter (canonicalSpecht p)) =
      if p = q then 1 else 0 := by
  classical
  haveI hp : (canonicalSpecht p).IsIrreducible :=
    classification_irreducible p (canonicalSpecht p) (canonicalSpecht_inherited p)
  haveI hq : (canonicalSpecht q).IsIrreducible :=
    classification_irreducible q (canonicalSpecht q) (canonicalSpecht_inherited q)
  letI : Invertible (Nat.card (SymmetricGroup n) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have he : Nonempty ((canonicalSpecht q).Equiv (canonicalSpecht p)) ↔ p = q := by
    constructor
    · intro h
      exact (classification_distinct q p _ _ (canonicalSpecht_inherited q)
        (canonicalSpecht_inherited p) h).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simpa only [characterPair, LinearMap.coe_mk, AddHom.coe_mk,
    classCharacter_mk, he] using
    Representation.char_orthonormal (canonicalSpecht p) (canonicalSpecht q)

private theorem specht_characters_independent (n : ℕ) :
    LinearIndependent ℂ (fun p : Partition n => classCharacter (canonicalSpecht p)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha q
  have h := congrArg (characterPair (canonicalSpecht q)) ha
  simpa only [map_sum, map_smul, specht_character_pair, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, map_zero] using h

/-- There are as many independent Specht characters as conjugacy classes. -/
private def spechtCharacterBasis (n : ℕ) :
    Module.Basis (Partition n) ℂ (ConjClasses (SymmetricGroup n) → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun p => classCharacter (canonicalSpecht p)) (specht_characters_independent n) (by
      rw [Module.finrank_fintype_fun_eq_card]
      exact (Fintype.card_congr (Equiv.ofBijective _
        (conjugacyCyclePartition_bijective n))).symm)

private theorem spechtCharacterBasis_apply (n : ℕ) (p : Partition n) :
    spechtCharacterBasis n p = classCharacter (canonicalSpecht p) :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) p

/-- Completeness follows from orthogonality and the dimension of class functions;
no completeness hypothesis on the constructed Specht family is used. -/
theorem classification_exhaustive {n : ℕ} (V : Type u) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (SymmetricGroup n) V)
    (hρ : ρ.IsIrreducible) : ∃! p : Partition n,
      ∃ σ : Representation ℂ (SymmetricGroup n) (SpechtModule p),
        InheritedSpechtAction p σ ∧ Nonempty (σ.Equiv ρ) := by
  classical
  haveI := hρ
  letI : Invertible (Nat.card (SymmetricGroup n) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have hex : ∃ p : Partition n, Nonempty ((canonicalSpecht p).Equiv ρ) := by
    by_contra! hn
    have hz (p : Partition n) :
        characterPair ρ (classCharacter (canonicalSpecht p)) = 0 := by
      haveI hp : (canonicalSpecht p).IsIrreducible :=
        classification_irreducible p (canonicalSpecht p) (canonicalSpecht_inherited p)
      have he : ¬ Nonempty (ρ.Equiv (canonicalSpecht p)) :=
        fun ⟨e⟩ => (hn p).false e.symm
      simpa only [characterPair, LinearMap.coe_mk, AddHom.coe_mk,
        classCharacter_mk, he, ite_false, Nat.cast_zero] using
        Representation.char_orthonormal (canonicalSpecht p) ρ
    have h := congrArg (characterPair ρ) ((spechtCharacterBasis n).sum_repr (classCharacter ρ))
    have hself : characterPair ρ (classCharacter ρ) = 1 := by
      simpa only [characterPair, LinearMap.coe_mk, AddHom.coe_mk,
        classCharacter_mk, show Nonempty (ρ.Equiv ρ) from ⟨.refl ρ⟩, ite_true,
        Nat.cast_one] using Representation.char_orthonormal ρ ρ
    simp only [map_sum, map_smul, spechtCharacterBasis_apply, hz, smul_zero,
      Finset.sum_const_zero, hself] at h
    exact zero_ne_one h
  obtain ⟨p, ⟨e⟩⟩ := hex
  refine ⟨p, ⟨canonicalSpecht p, canonicalSpecht_inherited p, ⟨e⟩⟩, ?_⟩
  rintro q ⟨τ, hτ, ⟨f⟩⟩
  exact classification_distinct q p τ _ hτ (canonicalSpecht_inherited p) ⟨f.trans e.symm⟩

/-- A scalar orbit of a polytabloid gives an explicit coordinate on Specht.
The coordinate is its original tabloid coefficient, normalized to send e_t to 1. -/
theorem specht_line_of_scalar_orbit {n : ℕ} {p : Partition n} (t : Tableau p)
    (χ : SymmetricGroup n → ℂ)
    (hχ : ∀ g, permutationRepresentation p g (polytabloid t) = χ g • polytabloid t)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hσ : InheritedSpechtAction p σ) :
    ∃ e : SpechtModule p ≃ₗ[ℂ] ℂ, ∀ g v, e (σ g v) = χ g * e v := by
  classical
  have hv (x : PermutationModule p) (hx : x ∈ spechtSpan p) :
      x = x.coeff (tabloid t) • polytabloid t := by
    rw [specht_cyclic t] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      dsimp only
      rw [hχ g]
      simp
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul] using congrArg₂ (· + ·) ihx ihy
    | smul a x hx ih =>
      simpa only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, smul_smul] using
        congrArg (a • ·) ih
  let e : SpechtModule p ≃ₗ[ℂ] ℂ :=
    { toFun v := v.val.coeff (tabloid t)
      invFun a := ⟨a • polytabloid t, (spechtSpan p).smul_mem a (polytabloid_mem_specht t)⟩
      left_inv v := Subtype.ext (hv v.val v.property).symm
      right_inv a := by simp
      map_add' v w := by simp
      map_smul' a v := by simp }
  refine ⟨e, ?_⟩
  intro g v
  change (σ g v).val.coeff (tabloid t) = χ g * v.val.coeff (tabloid t)
  rw [hσ, hv v.val v.property, map_smul, hχ, smul_smul]
  simp [mul_comm]

private theorem parts_indiscrete {n : ℕ} (hn : 0 < n) :
    parts (Nat.Partition.indiscrete n) = [n] := by
  rw [parts_eq_sorted_multiset, Nat.Partition.indiscrete_parts hn.ne']
  exact Multiset.sort_singleton n (· ≥ ·)

private theorem row_cell_first {n : ℕ} (hn : 0 < n)
    (c : Cell (Nat.Partition.indiscrete n)) : c.val.1 = 0 := by
  have h := (cell_iff _ _ _).mp c.property
  rw [rowLength_eq_getD, parts_indiscrete hn] at h
  cases hi : c.val.1 with
  | zero => rfl
  | succ i => simp [hi] at h

private theorem row_permutation_fixed {n : ℕ} (hn : 0 < n)
    (g : SymmetricGroup n) (x : PermutationModule (Nat.Partition.indiscrete n)) :
    permutationRepresentation _ g x = x := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact map_zero _
  | add x y hx hy => simp only [map_add, hx, hy]
  | single q z =>
    rw [permutationRepresentation_basis]
    congr 1
    induction q using Quotient.inductionOn with
    | _ t =>
      change tabloid (g • t) = tabloid t
      apply Quotient.sound
      funext a
      exact (row_cell_first hn ((g • t).symm a)).trans (row_cell_first hn (t.symm a)).symm

theorem classification_row (n : ℕ) (hn : 0 < n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule (Nat.Partition.indiscrete n)))
    (hσ : InheritedSpechtAction _ σ) :
    ∃ e : SpechtModule (Nat.Partition.indiscrete n) ≃ₗ[ℂ] ℂ,
      ∀ g v, e (σ g v) = e v := by
  obtain ⟨e, he⟩ := specht_line_of_scalar_orbit (canonicalTableau _) (fun _ => 1)
    (by intro g; simpa using row_permutation_fixed hn g (polytabloid (canonicalTableau _))) σ hσ
  exact ⟨e, by intro g v; simpa using he g v⟩

private theorem column_cell_first {n : ℕ} (hn : 0 < n)
    (c : Cell (transpose (Nat.Partition.indiscrete n))) : c.val.2 = 0 := by
  have h := (cell_iff_column _ _ _).mp c.property
  rw [transpose_columnLength, rowLength_eq_getD, parts_indiscrete hn] at h
  cases hi : c.val.2 with
  | zero => rfl
  | succ i => simp [hi] at h

theorem classification_column (n : ℕ) (hn : 0 < n)
    (σ : Representation ℂ (SymmetricGroup n)
      (SpechtModule (transpose (Nat.Partition.indiscrete n))))
    (hσ : InheritedSpechtAction _ σ) :
    ∃ e : SpechtModule (transpose (Nat.Partition.indiscrete n)) ≃ₗ[ℂ] ℂ,
      ∀ g v, e (σ g v) = permutationSign g * e v := by
  let t := canonicalTableau (transpose (Nat.Partition.indiscrete n))
  apply specht_line_of_scalar_orbit t permutationSign ?_ σ hσ
  intro g
  have hg : g ∈ columnSubgroup t := by
    intro a
    exact (column_cell_first hn (t.symm (g a))).trans (column_cell_first hn (t.symm a)).symm
  exact column_action_polytabloid t ⟨g, hg⟩

theorem classification_empty
    (σ : Representation ℂ (SymmetricGroup 0) (SpechtModule emptyPartition))
    (hσ : InheritedSpechtAction _ σ) :
    ∃ e : SpechtModule emptyPartition ≃ₗ[ℂ] ℂ,
      ∀ g v, e (σ g v) = e v := by
  obtain ⟨e, he⟩ := specht_line_of_scalar_orbit emptyTableau (fun _ => 1)
    (by intro g; rw [zero_labels_trivial g]; simp) σ hσ
  exact ⟨e, by intro g v; simpa using he g v⟩

end AdvancedFiniteGroupRepresentations
