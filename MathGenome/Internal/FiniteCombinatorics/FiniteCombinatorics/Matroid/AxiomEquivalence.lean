import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.AxiomEquivalence
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ForwardPresentations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.FromBases
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.FromRank
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.FromCircuits
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.FromClosure

/-! The complete five-presentation equivalence (W64).
Existence and exact recovery use the four independent reconstruction theorems.
Uniqueness follows from equality of the ground and the independent sets, so all
presentations describe the same canonical Mathlib matroid. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u}

/-- Equality of independent sets on a fixed ground determines the matroid. -/
private lemma sameMatroid {E : Set α} {P : Set α → Prop}
    {M N : _root_.Matroid α} (hM : M.E = E) (hN : N.E = E)
    (hiM : ∀ I, M.Indep I ↔ P I) (hiN : ∀ I, N.Indep I ↔ P I) : M = N :=
  _root_.Matroid.ext_indep (hM.trans hN.symm) (fun {I} _ => (hiM I).trans (hiN I).symm)

/-- Finite cardinal augmentation for the canonical independence system. -/
lemma fromMatroidAugmentation (M : _root_.Matroid α) [M.Finite] :
    Augmentation (fromMatroid M) := by
  intro I J hI hJ hc
  have hi : M.Indep I := hI
  have hj : M.Indep J := hJ
  apply hi.exists_insert_of_encard_lt hj
  rw [← (M.ground_finite.subset hi.subset_ground).cast_ncard_eq,
    ← (M.ground_finite.subset hj.subset_ground).cast_ncard_eq]
  exact_mod_cast hc

theorem independenceAxiomEquivalence : Expected.independenceAxiomEquivalence.{u} := by
  intro α E S
  constructor
  · intro h
    refine ⟨ofAugmentation S h,
      ⟨groundPreserved E S h, finiteConstruction E S h, indepPreserved E S h⟩, ?_⟩
    intro N hN
    exact sameMatroid hN.1 (groundPreserved E S h) hN.2.2 (indepPreserved E S h)
  · rintro ⟨M, hM, _⟩
    have := hM.2.1
    intro I J hI hJ hc
    have hi := (hM.2.2 I).mpr hI
    have hj := (hM.2.2 J).mpr hJ
    obtain ⟨e, he, hie⟩ := fromMatroidAugmentation M hi hj hc
    exact ⟨e, he, (hM.2.2 _).mp hie⟩

theorem basisAxiomEquivalence : Expected.basisAxiomEquivalence.{u} := by
  intro α E hE B
  constructor
  · intro hB
    obtain ⟨M, hM⟩ := existsMatroidOfBases E hE B hB
    refine ⟨M, hM, ?_⟩
    intro N hN
    exact sameMatroid hN.1 hM.1 hN.2.2.1 hM.2.2.1
  · rintro ⟨M, hM, _⟩
    have := hM.2.1
    have hB : B = {D | M.IsBase D} := by
      ext D
      exact (hM.2.2.2 D).symm
    rw [hB, ← hM.1]
    exact basesPresentation M

theorem rankAxiomEquivalence : Expected.rankAxiomEquivalence.{u} := by
  intro α E hE r
  constructor
  · intro hr
    obtain ⟨M, hM⟩ := existsMatroidFromRank E hE r hr
    refine ⟨M, hM, ?_⟩
    intro N hN
    exact sameMatroid hN.1 hM.1 hN.2.choose_spec.1 hM.2.choose_spec.1
  · rintro ⟨M, ⟨hME, hM, hi, hr⟩, _⟩
    have := hM
    have hA : ∀ A, A ⊆ E → A ⊆ M.E := fun A h => hME.symm ▸ h
    have hri := rankIncrements M
    have hrs := rankSubmodular M
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr ∅ (empty_subset E)]
      exact rankEmpty M
    · intro A hAE e he
      rw [← hr (insert e A) (insert_subset he hAE), ← hr A hAE]
      exact hri A (hA A hAE) e (hME.symm ▸ he)
    · intro A hAE B hBE
      rw [← hr (A ∪ B) (union_subset hAE hBE),
        ← hr (A ∩ B) (inter_subset_left.trans hAE), ← hr A hAE, ← hr B hBE]
      exact hrs A B (hA A hAE) (hA B hBE)

theorem circuitAxiomEquivalence : Expected.circuitAxiomEquivalence.{u} := by
  intro α E hE C
  constructor
  · intro hC
    obtain ⟨M, hM⟩ := matroidFromCircuits E hE C hC
    refine ⟨M, hM, ?_⟩
    intro N hN
    exact sameMatroid hN.1 hM.1 hN.2.2.1 hM.2.2.1
  · rintro ⟨M, hM, _⟩
    have := hM.2.1
    have hC : C = {D | M.IsCircuit D} := by
      ext D
      exact (hM.2.2.2 D).symm
    rw [hC, ← hM.1]
    exact circuitsPresentation M

theorem closureAxiomEquivalence : Expected.closureAxiomEquivalence.{u} := by
  intro α E hE c
  constructor
  · intro hc
    obtain ⟨M, hM⟩ := closureRealization E hE c hc
    refine ⟨M, hM, ?_⟩
    intro N hN
    exact sameMatroid hN.1 hM.1 hN.2.2.1 hM.2.2.1
  · rintro ⟨M, hM, _⟩
    have := hM.2.1
    have hc := hM.2.2.2
    have hA : ∀ A, A ⊆ E → A ⊆ M.E := fun A h => hM.1.symm ▸ h
    have hrange : ∀ A, A ⊆ E → c A ⊆ E := by
      intro A hAE
      rw [← hc A hAE, ← hM.1]
      exact M.closure_subset_ground A
    refine ⟨hrange, ?_, ?_, ?_, ?_⟩
    · intro A hAE
      rw [← hc A hAE]
      exact M.subset_closure A (hA A hAE)
    · intro A hAE B hBE hAB
      rw [← hc A hAE, ← hc B hBE]
      exact M.closure_subset_closure hAB
    · intro A hAE
      rw [← hc (c A) (hrange A hAE), ← hc A hAE]
      exact M.closure_closure A
    · intro A hAE x hx y hy h
      rw [← hc (insert x A) (insert_subset hx hAE), ← hc A hAE] at h
      rw [← hc (insert y A) (insert_subset hy hAE)]
      exact (M.closure_exchange h).1

theorem presentationRoundTrips : Expected.presentationRoundTrips.{u} := by
  intro α M hM
  have hI : IndependenceRealization (Expected.fromMatroid M) M :=
    ⟨rfl, hM, fun _ => Iff.rfl⟩
  have hB : BasisRealization M.E {B | M.IsBase B} M :=
    ⟨rfl, hM, fun I => (basisRecovery M I).symm, fun _ => Iff.rfl⟩
  have hr : RankRealization M.E (Expected.rank M) M :=
    ⟨rfl, hM, fun I => (rankRecovery M I).symm, fun _ _ => rfl⟩
  have hC : CircuitRealization M.E {C | M.IsCircuit C} M :=
    ⟨rfl, hM, fun I => (circuitRecovery M I).symm, fun _ => Iff.rfl⟩
  have hc : ClosureRealization M.E M.closure M :=
    ⟨rfl, hM, fun I => (closureRecovery M I).symm, fun _ _ => rfl⟩
  refine ⟨?_, basesPresentation M, rankPresentation M, circuitsPresentation M,
    closurePresentation M, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fromMatroidAugmentation M, ?_⟩
    exact sameMatroid (groundPreserved M.E (fromMatroid M) (fromMatroidAugmentation M))
      rfl (indepPreserved M.E (fromMatroid M) (fromMatroidAugmentation M))
      (fun _ => Iff.rfl)
  · intro N hN
    exact sameMatroid hN.1 hI.1 hN.2.2 hI.2.2
  · intro N hN
    exact sameMatroid hN.1 hB.1 hN.2.2.1 hB.2.2.1
  · intro N hN
    exact sameMatroid hN.1 hr.1 hN.2.choose_spec.1 hr.2.choose_spec.1
  · intro N hN
    exact sameMatroid hN.1 hC.1 hN.2.2.1 hC.2.2.1
  · intro N hN
    exact sameMatroid hN.1 hc.1 hN.2.2.1 hc.2.2.1

theorem fivePresentationEquivalence : Expected.fivePresentationEquivalence.{u} :=
  ⟨independenceAxiomEquivalence, basisAxiomEquivalence, rankAxiomEquivalence,
    circuitAxiomEquivalence, closureAxiomEquivalence, presentationRoundTrips⟩

end FiniteCombinatorics.Matroid
