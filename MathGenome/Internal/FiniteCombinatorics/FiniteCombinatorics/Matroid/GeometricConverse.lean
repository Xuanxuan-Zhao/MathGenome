import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GeometricConverse
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.LatticeRank
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.FromRank
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.FlatLattice

namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {L : Type u} [CompleteLattice L]

@[simp] theorem atomJoin_empty : atomJoin (∅ : Set (LatticeAtom L)) = ⊥ := by
  simp [atomJoin]

@[simp] theorem atomJoin_insert (a : LatticeAtom L) (A : Set (LatticeAtom L)) :
    atomJoin (insert a A) = a.1 ⊔ atomJoin A := by
  exact iSup_insert

@[simp] theorem atomJoin_singleton (a : LatticeAtom L) : atomJoin {a} = a.1 := by
  simp [atomJoin]

theorem atomJoin_mono : Monotone (atomJoin (L := L)) := by
  intro A B h
  exact iSup_le fun a => iSup_le fun ha => le_iSup_of_le a (le_iSup_of_le (h ha) le_rfl)

theorem atomJoin_union (A B : Set (LatticeAtom L)) :
    atomJoin (A ∪ B) = atomJoin A ⊔ atomJoin B := by
  simp [atomJoin, iSup_or, iSup_sup_eq]

theorem atomJoin_atomsBelow (hL : GeometricLattice L) (x : L) :
    atomJoin (atomsBelow x) = x := by
  have hx := hL.2.1 x
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact (show a.1 ≤ sSup {a : L | IsAtom a ∧ a ≤ x} from le_sSup ⟨a.2, ha⟩).trans_eq hx
  · calc
      x = sSup {a : L | IsAtom a ∧ a ≤ x} := hx.symm
      _ ≤ atomJoin (atomsBelow x) := by
        apply sSup_le
        rintro a ⟨ha, hax⟩
        exact le_iSup_of_le (⟨a, ha⟩ : LatticeAtom L)
          (le_iSup_of_le (show (⟨a, ha⟩ : LatticeAtom L) ∈ atomsBelow x from hax) le_rfl)

theorem atomJoin_le_iff (A : Set (LatticeAtom L)) (x : L) :
    atomJoin A ≤ x ↔ A ⊆ atomsBelow x := by
  change (⨆ a ∈ A, a.1) ≤ x ↔ ∀ ⦃a⦄, a ∈ A → a.1 ≤ x
  simp only [iSup_le_iff]

/-- The semimodular height inequality gives the rank axioms on atoms. -/
theorem atomRankPresentation (hL : GeometricLattice L) :
    RankPresentation (univ : Set (LatticeAtom L)) atomRank := by
  have : Finite L := hL.1
  have : IsUpperModularLattice L := ⟨fun {a b} h => hL.2.2 a b h⟩
  refine ⟨?_, ?_, ?_⟩
  · change (latticeHeight (atomJoin (∅ : Set (LatticeAtom L))) : ℤ) = 0
    simp [latticeHeightBot]
  · intro A _ a _
    change 0 ≤ (latticeHeight (atomJoin (insert a A)) : ℤ) -
      (latticeHeight (atomJoin A) : ℤ) ∧
      (latticeHeight (atomJoin (insert a A)) : ℤ) -
      (latticeHeight (atomJoin A) : ℤ) ≤ 1
    rw [atomJoin_insert, sup_comm a.1]
    exact latticeAtomIncrement (atomJoin A) a.1 a.2
  · intro A _ B _
    have hi : atomJoin (A ∩ B) ≤ atomJoin A ⊓ atomJoin B :=
      le_inf (atomJoin_mono inter_subset_left) (atomJoin_mono inter_subset_right)
    have hm := latticeHeightMonotone hi
    have hs := latticeHeightSubmodular (atomJoin A) (atomJoin B)
    change (latticeHeight (atomJoin (A ∪ B)) : ℤ) +
      (latticeHeight (atomJoin (A ∩ B)) : ℤ) ≤
      (latticeHeight (atomJoin A) : ℤ) + (latticeHeight (atomJoin B) : ℤ)
    rw [atomJoin_union]
    exact_mod_cast (show latticeHeight (atomJoin A ⊔ atomJoin B) +
      latticeHeight (atomJoin (A ∩ B)) ≤
      latticeHeight (atomJoin A) + latticeHeight (atomJoin B) by omega)

/-- Rank preservation forces exactly the lattice-theoretic closure. -/
theorem geometricClosure (hL : GeometricLattice L)
    (M : _root_.Matroid (LatticeAtom L)) [M.Finite]
    (hE : M.E = univ) (hr : ∀ A, rank M A = atomRank A)
    (A : Set (LatticeAtom L)) (a : LatticeAtom L) :
    a ∈ M.closure A ↔ a.1 ≤ atomJoin A := by
  have : Finite L := hL.1
  have : IsUpperModularLattice L := ⟨fun {a b} h => hL.2.2 a b h⟩
  rw [closureRank M A (by simp [hE]) a (by simp [hE]), hr, hr]
  constructor
  · intro he
    change (latticeHeight (atomJoin (insert a A)) : ℤ) =
      (latticeHeight (atomJoin A) : ℤ) at he
    have hn : latticeHeight (atomJoin (insert a A)) = latticeHeight (atomJoin A) := by
      exact_mod_cast he
    have hj : atomJoin (insert a A) = atomJoin A := by
      by_contra hne
      have hl := latticeHeightStrictMono
        (lt_of_le_of_ne (atomJoin_mono (subset_insert a A)) (Ne.symm hne))
      omega
    rw [atomJoin_insert] at hj
    exact sup_eq_right.mp hj
  · intro ha
    have hj : atomJoin (insert a A) = atomJoin A := by
      rw [atomJoin_insert, sup_eq_right.mpr ha]
    simp only [atomRank, hj]

/-- A closure formula on atoms implies simplicity and the stated description
of every flat; no representability assumption is involved. -/
theorem geometricRealizationOfRank (hL : GeometricLattice L)
    (M : _root_.Matroid (LatticeAtom L)) [M.Finite]
    (hE : M.E = univ) (hr : ∀ A, rank M A = atomRank A) :
    GeometricRealization M := by
  have hc := geometricClosure hL M hE hr
  have hclosed : ∀ A, M.closure A = atomsBelow (atomJoin A) :=
    fun A => Set.ext (hc A)
  have hflat : ∀ F, M.IsFlat F ↔ ∃ x : L, F = atomsBelow x := by
    intro F
    constructor
    · intro hF
      exact ⟨atomJoin F, hF.closure.symm.trans (hclosed F)⟩
    · rintro ⟨x, rfl⟩
      apply M.isFlat_iff_closure_eq.mpr
      rw [hclosed, atomJoin_atomsBelow hL]
  have hs : ∀ a : LatticeAtom L, M.Indep {a} := by
    intro a
    have hn : a ∉ M.closure ∅ := by
      rw [hc, atomJoin_empty]
      exact fun h => a.2.ne_bot (le_bot_iff.mp h)
    simpa using (M.empty_indep.insert_indep_iff).mpr (Or.inl ⟨by simp [hE], hn⟩)
  refine ⟨hE, inferInstance, hr, ?_, hc, hflat, ?_⟩
  · intro a b
    by_cases hab : a = b
    · simpa [hab] using hs b
    apply ((hs b).insert_indep_iff).mpr
    left
    refine ⟨by simp [hE], ?_⟩
    rw [hc, atomJoin_singleton]
    intro hle
    exact hab (Subtype.ext ((b.2.le_iff_eq a.2.ne_bot).mp hle))
  · let e : L ≃o Flat M := {
      toFun := fun x => ⟨atomsBelow x, (hflat _).mpr ⟨x, rfl⟩⟩
      invFun := fun F => atomJoin F.1
      left_inv := atomJoin_atomsBelow hL
      right_inv := fun F => by
        apply Subtype.ext
        exact (hclosed F.1).symm.trans F.2.closure
      map_rel_iff' := by
        intro x y
        change atomsBelow x ⊆ atomsBelow y ↔ x ≤ y
        constructor
        · intro h
          have hj := atomJoin_mono h
          rwa [atomJoin_atomsBelow hL, atomJoin_atomsBelow hL] at hj
        · exact fun h a ha => ha.trans h }
    exact ⟨e, fun _ => rfl, fun _ => rfl⟩

/-- The finite geometric lattice determines one and only one matroid on
its atoms, with all rank, closure and flat-lattice identifications. -/
theorem existsUniqueGeometricMatroid (hL : GeometricLattice L) :
    ∃! M : _root_.Matroid (LatticeAtom L), GeometricRealization M := by
  have : Finite L := hL.1
  obtain ⟨M, hE, hM, hi, hr⟩ := existsMatroidFromRank
    (univ : Set (LatticeAtom L)) (Set.toFinite _) atomRank (atomRankPresentation hL)
  have := hM
  have hr' : ∀ A, rank M A = atomRank A := fun A => hr A (subset_univ A)
  refine ⟨M, geometricRealizationOfRank hL M hE hr', ?_⟩
  intro N hN
  obtain ⟨hNE, hNfin, hNr, _⟩ := hN
  have := hNfin
  apply _root_.Matroid.ext_indep (hNE.trans hE.symm)
  intro I _
  rw [← rankRecovery N I, ← rankRecovery M I]
  change (I ⊆ N.E ∧ rank N I = _) ↔ (I ⊆ M.E ∧ rank M I = _)
  have hNr' : ∀ A, rank N A = atomRank A := hNr
  rw [hNE, hE, hNr', hr']

end FiniteCombinatorics.Matroid
