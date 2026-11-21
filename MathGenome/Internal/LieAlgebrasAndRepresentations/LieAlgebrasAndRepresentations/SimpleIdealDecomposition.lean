import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.KillingCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleIdealDecomposition

/-! LA-B06: finite decomposition into nonabelian simple ideals, with the
source's vanishing-radical hypothesis. The factors are the atoms in the lattice
of ideals. Supremum of ideals is their linear sum. -/

universe u v
open scoped Classical
namespace LieAlgebrasAndRepresentations

variable (k : Type u) (L : Type v) [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

/-- Bridge from the source definition to the direct-sum definition. -/
theorem semisimple_structure (h : IsSemisimple k L) : LieAlgebra.IsSemisimple k L := by
  have : LieAlgebra.HasTrivialRadical k L := ⟨h⟩
  infer_instance

theorem ideal_isCompl_killingCompl (h : IsSemisimple k L) (I : LieIdeal k L) :
    IsCompl I I.killingCompl := by
  have : LieAlgebra.HasTrivialRadical k L := ⟨h⟩
  exact I.isCompl_killingCompl

theorem semisimple_center_eq_bot (h : IsSemisimple k L) :
    LieAlgebra.center k L = ⊥ := by
  have : LieAlgebra.HasTrivialRadical k L := ⟨h⟩
  exact LieAlgebra.center_eq_bot k L

theorem semisimple_perfect (h : IsSemisimple k L) :
    ⁅(⊤ : LieIdeal k L), (⊤ : LieIdeal k L)⁆ = ⊤ := by
  have := semisimple_structure k L h
  apply top_unique
  conv_lhs => rw [← LieAlgebra.IsSemisimple.sSup_atoms_eq_top (R := k) (L := L)]
  apply sSup_le
  intro I hI
  rw [← lie_eq_self_of_isAtom_of_nonabelian I hI
    (LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI)]
  exact LieSubmodule.mono_lie le_top le_top

theorem simple_ideal_decomposition (h : IsSemisimple k L) :
    ∃ S : Set (LieIdeal k L), S.Finite ∧ S = {I | IsAtom I} ∧
      (∀ I ∈ S, LieAlgebra.IsSimple k I) ∧
      DirectSum.IsInternal (fun I : S => I.val.toSubmodule) := by
  have := semisimple_structure k L h
  refine ⟨{I | IsAtom I}, ?_, rfl, ?_, ?_⟩
  · exact WellFoundedGT.finite_of_sSupIndep
      LieAlgebra.IsSemisimple.sSupIndep_isAtom
  · exact fun I hI => LieAlgebra.IsSemisimple.isSimple_of_isAtom I hI
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact LieSubmodule.iSupIndep_toSubmodule.mpr
        ((sSupIndep_iff _).mp LieAlgebra.IsSemisimple.sSupIndep_isAtom)
    · rw [LieSubmodule.iSup_toSubmodule_eq_top]
      simpa only [sSup_eq_iSup, iSup_subtype] using
        (LieAlgebra.IsSemisimple.sSup_atoms_eq_top (R := k) (L := L))

/-- The canonical sum map preserves brackets because distinct simple ideals
commute. Its bijectivity is precisely the internal direct-sum assertion. -/
theorem simple_ideal_lie_decomposition (h : IsSemisimple k L) :
    ∃ S : Set (LieIdeal k L), S.Finite ∧ S = {I | IsAtom I} ∧
      (∀ I ∈ S, LieAlgebra.IsSimple k I) ∧
      ∃ e : DirectSum S (fun I => ↥I.val) ≃ₗ⁅k⁆ L,
        ∀ (I : S) (x : I.val),
          e (DirectSum.of (fun J : S => ↥J.val) I x) = (x : L) := by
  obtain ⟨S, hfin, hS, hsimp, hinternal⟩ := simple_ideal_decomposition k L h
  have hcomm : Pairwise (fun i j : S => ∀ (x : i.val) (y : j.val),
      ⁅(x : L), (y : L)⁆ = 0) := by
    intro i j hij x y
    have hi : IsAtom i.val := by simpa only [hS, Set.mem_ofPred_eq] using i.property
    have hj : IsAtom j.val := by simpa only [hS, Set.mem_ofPred_eq] using j.property
    have hd : Disjoint i.val j.val := hi.disjoint_of_ne hj
      (fun he => hij (Subtype.ext he))
    have hm : ⁅(x : L), (y : L)⁆ ∈ i.val ⊓ j.val :=
      ⟨lie_mem_left k L i.val x y x.property, lie_mem_right k L j.val x y y.property⟩
    rw [hd.eq_bot] at hm
    simpa only [LieSubmodule.mem_bot] using hm
  let f : DirectSum S (fun I => ↥I.val) →ₗ⁅k⁆ L :=
    DirectSum.toLieAlgebra L (fun I : S => I.val.incl) hcomm
  have hf : Function.Bijective f := hinternal
  refine ⟨S, hfin, hS, hsimp, LieEquiv.ofBijective f hf, ?_⟩
  intro I x
  change DirectSum.toModule k S L (fun J : S => J.val.incl.toLinearMap)
    (DirectSum.of (fun J : S => ↥J.val) I x) = (x : L)
  exact DirectSum.coeLinearMap_of (fun J : S => J.val.toSubmodule) I x

theorem every_ideal_unique_sum (h : IsSemisimple k L) (I : LieIdeal k L) :
    ∃! T : Set (LieIdeal k L), T ⊆ {J | IsAtom J} ∧ sSup T = I := by
  have := semisimple_structure k L h
  let B := LieAlgebra.IsSemisimple.booleanGenerators k L
  obtain ⟨T, hT, hIT⟩ := B.atomistic I (by
    rw [LieAlgebra.IsSemisimple.sSup_atoms_eq_top]; exact le_top)
  refine ⟨T, ⟨hT, hIT.symm⟩, ?_⟩
  intro U hU
  apply Set.Subset.antisymm
  · apply (B.sSup_le_sSup_iff_of_atoms U T hU.1 hT).mp
    rw [hU.2, ← hIT]
  · apply (B.sSup_le_sSup_iff_of_atoms T U hT hU.1).mp
    rw [hU.2, ← hIT]

theorem simple_factors_empty_iff (h : IsSemisimple k L) :
    {I : LieIdeal k L | IsAtom I} = ∅ ↔ Subsingleton L := by
  have := semisimple_structure k L h
  constructor
  · intro he
    have ht : (⊤ : LieIdeal k L) = ⊥ := by
      rw [← LieAlgebra.IsSemisimple.sSup_atoms_eq_top (R := k) (L := L), he, sSup_empty]
    exact (LieSubmodule.subsingleton_iff k L L).mp (subsingleton_of_top_eq_bot ht)
  · intro hs
    have := hs
    ext I
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hI
    exact hI.1 (Subsingleton.elim I ⊥)

end LieAlgebrasAndRepresentations
