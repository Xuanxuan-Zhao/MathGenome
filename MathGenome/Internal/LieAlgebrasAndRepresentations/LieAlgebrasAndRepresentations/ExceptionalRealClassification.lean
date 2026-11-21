import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExceptionalRealClassification
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalInnerInvolutions
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactRealForm
import Batteries.Tactic.OpenPrivate

namespace LieAlgebrasAndRepresentations.ExceptionalRealClassification

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.ExceptionalRealClassification
open Specs.LieAlgebrasAndRepresentations.ExceptionalInnerInvolutions
open Specs.LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions
  (diagramInvolution e6Cartan Coloring vertexColor HasColor)
open Specs.LieAlgebrasAndRepresentations.StableCartanVoganData
  (DiagramData Presents evaluation)
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact involutionConjugation)
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
  (complexFixed killingSignature)
open Specs.LieAlgebrasAndRepresentations.VoganEquivalence
  (RootIsom colorSign)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple positive)
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.MaximalTori (IsMaximalToral_value)
open RealForms Module
open private sandwich compact_intertwiner from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
open scoped BigOperators

noncomputable section

universe u

private def rowSums (D : Diagram) : ℕ → Vertex D → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun i => ∑ j, cartan D i j * rowSums D n j

private theorem rowSums_perm {D : Diagram} {p : Equiv.Perm (Vertex D)}
    (hp : IsDiagramPerm p) (n : ℕ) (i : Vertex D) :
    rowSums D n (p i) = rowSums D n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    change (∑ j, cartan D (p i) j * rowSums D n j) = _
    rw [← Equiv.sum_comp p]
    simp only [show ∀ j, cartan D (p i) (p j) = cartan D i j from hp i, ih]
    rfl

private def profile (D : Diagram) (i : Vertex D) : ℤ × ℤ × ℤ :=
  (rowSums D 1 i, rowSums D 2 i, rowSums D 3 i)

private theorem profile_perm {D : Diagram} {p : Equiv.Perm (Vertex D)}
    (hp : IsDiagramPerm p) (i : Vertex D) :
    profile D (p i) = profile D i := by
  simp only [profile, rowSums_perm hp]

private theorem profile_G2 : Function.Injective (profile .G2) := by decide
private theorem profile_F4 : Function.Injective (profile .F4) := by decide
private theorem profile_E7 : Function.Injective (profile .E7) := by decide
private theorem profile_E8 : Function.Injective (profile .E8) := by decide

private theorem e6_first_vertex :
    ∀ i : Vertex .E6, profile .E6 i = profile .E6 0 → i = 0 ∨ i = 4 := by decide

private theorem e6_profile_with_first :
    ∀ i j : Vertex .E6, profile .E6 i = profile .E6 j →
      cartan .E6 0 i = cartan .E6 0 j → i = j := by decide

private theorem e6_profile_with_last :
    ∀ i j : Vertex .E6, profile .E6 i = profile .E6 j →
      cartan .E6 4 i = cartan .E6 0 j → i = diagramInvolution j := by decide

private theorem diagramInvolution_moves : diagramInvolution (0 : Fin 6) ≠ 0 := by decide

theorem exceptionalDiagramPermutations : exceptionalDiagramPermutationsType := by
  intro D p hp
  cases D with
  | G2 => exact Or.inl (fun i => profile_G2 (profile_perm hp i))
  | F4 => exact Or.inl (fun i => profile_F4 (profile_perm hp i))
  | E7 => exact Or.inl (fun i => profile_E7 (profile_perm hp i))
  | E8 => exact Or.inl (fun i => profile_E8 (profile_perm hp i))
  | E6 =>
    rcases e6_first_vertex (p 0) (profile_perm hp 0) with h | h
    · exact Or.inl (fun i => e6_profile_with_first (p i) i (profile_perm hp i)
        (by simpa only [h] using hp 0 i))
    · refine Or.inr ⟨rfl, Equiv.ext (fun i => ?_)⟩
      exact e6_profile_with_last (p i) i (profile_perm hp i) (by simpa only [h] using hp 0 i)

section Numbering

open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open private direction_vector vector_regular from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open private complexWeyl_of_real positiveSimpleEquiv liftSimpleEquiv liftSimpleEquiv_apply
  pullbackDirection pullback_regular from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VoganEquivalence

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

/-- Two regular choices of positive roots in a Cartan differ by a Weyl action. -/
private theorem positive_system_transport (hss : IsSemisimple_value ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral_value H)
    (ψ φ : Direction H) (hψ : Regular H ψ) (hφ : Regular H φ) :
    ∃ g : RootIsom H H, ∀ α, α ∈ positive H ψ ↔ g.linear α ∈ positive H φ := by
  let d := RealRootSpace.realization_of_maximalToral hss H hH
  letI : Fact (Realization H) := ⟨d⟩
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  obtain ⟨x, hx⟩ := direction_vector d ψ
  obtain ⟨v, hv⟩ := direction_vector d φ
  have hx' := vector_regular d ψ hx hψ
  have hv' := vector_regular d φ hv hφ
  obtain ⟨w, hw⟩ := exists_weyl_into_simpleChamber d.root_system hv' hx'
  obtain ⟨g, _, hg⟩ := complexWeyl_of_real hss hH d w
  let r : RootIsom H H := ⟨g.val, g.property.1, g.property.2⟩
  refine ⟨r, fun α => ?_⟩
  by_cases ha : α ∈ rootSet_value H
  · let y := rootRestriction H α
    have hy : y ∈ realRoots H := ⟨α, ha, rfl⟩
    have hy' := (rootWeylGroup_mem_iff d.root_system.toRootAxioms w.property y).mp hy
    have hj : d.j y = α := d.extension_root α ha
    have hsign : 0 < inner ℝ (w.val x) (w.val y) ↔ 0 < inner ℝ v (w.val y) := by
      constructor
      · intro hp
        rcases positive_or_neg_positive d.root_system.toRootAxioms hv' hy' with hh | hh
        · exact hh.2
        · have hn := simpleChamber_pairing_positive d.root_system.toRootAxioms hw hh
          rw [inner_neg_right] at hn
          linarith
      · exact fun hp => simpleChamber_pairing_positive d.root_system.toRootAxioms hw ⟨hy', hp⟩
    change (α ∈ rootSet_value H ∧ 0 < ψ α) ↔
      (r.linear α ∈ rootSet_value H ∧ 0 < φ (r.linear α))
    rw [r.roots, and_iff_right ha, and_iff_right ha, ← hj]
    change (0 < ψ (d.j y)) ↔ 0 < φ (g.val (d.j y))
    rw [hg, hx, hv, ← rootWeylGroup_inner w.property x y]
    exact hsign
  · exact iff_of_false (fun h => ha h.1) (fun h => ha ((r.roots _).mp h.1))

/-- The source numbering can be transported to any maximal torus and
regular positive system, including those from the Vogan encoding. -/
private theorem number_simple_roots {D : Diagram} (hss : IsSemisimple_value ℂ L)
    (q : NumberedCartan D L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral_value H)
    (φ : Direction H) (hφ : Regular H φ) :
    ∃ s : Vertex D ≃ simple H φ,
      ∀ i j, (s j).val (coroot_value H (s i).val) = (cartan D i j : ℂ) := by
  have hHC := (isCartan_iff_maximal_toral hss H).mpr hH
  have hqC := (isCartan_iff_maximal_toral hss q.subalgebra).mpr q.maximalToral
  obtain ⟨g, _, hg⟩ := cartan_conjugacy L hss H q.subalgebra hHC hqC
  let r := VoganEquivalence.rootIsomOfTransport hss hH q.maximalToral g hg
  let ψ := pullbackDirection r q.direction
  obtain ⟨w, hw⟩ := positive_system_transport hss H hH φ ψ hφ (pullback_regular r q.regular)
  let e := positiveSimpleEquiv w.linear hw
  let f := liftSimpleEquiv r q.direction
  let s := q.number.trans (e.trans f).symm
  refine ⟨s, fun i j => ?_⟩
  have hs (k : Vertex D) : r.linear (w.linear (s k).val) = (q.number k).val :=
    congrArg Subtype.val ((e.trans f).apply_symm_apply (q.number k))
  rw [← q.entries i j, ← hs i, ← hs j]
  have hroot (i : Vertex D) := (s i).property.1.1
  exact (w.pairing _ (hroot i) _ (hroot j)).symm.trans
    (r.pairing _ ((w.roots _).mpr (hroot i)) _ ((w.roots _).mpr (hroot j))).symm

end Numbering

section Outer

open _root_.LieAlgebrasAndRepresentations.Serre
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open private serre_reindex relations_reindex numbered_compact_cartan
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalInnerInvolutions
open private compact_pinning from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VoganEquivalence
open private serrePresentation from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem e6_matrix : cartan .E6 = e6Cartan := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem e6_nonpos : ∀ i j, i ≠ j → e6Cartan i j ≤ 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private theorem reindex_e6_presentation {I : Type*} [DecidableEq I]
    (A : Matrix I I ℤ) (s : Fin 6 ≃ I)
    (hA : ∀ i j, A (s i) (s j) = e6Cartan i j)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (E F C : I → L)
    (hp : Presents A E F C) :
    Presents e6Cartan (E ∘ s) (F ∘ s) (C ∘ s) := by
  obtain ⟨p, hE, hF, hC⟩ := hp
  let e' := serre_reindex e6Cartan A s hA e6_nonpos
  have e'_apply (x : Algebra e6Cartan) :
      e' x = lift e6Cartan e6_nonpos _ _ _ (relations_reindex e6Cartan A s hA hoff) x := rfl
  refine ⟨e'.trans p, ?_, ?_, ?_⟩
  all_goals
    intro i
    simp [LieEquiv.trans_apply, e'_apply, hE, hF, hC, Function.comp_apply]

private theorem exists_compatible_e6_presentation (hss : IsSemisimple_value ℂ L)
    (q : NumberedCartan .E6 L) (ω : Conjugation L) (hω : IsCompact ω) :
    ∃ E F C : Fin 6 → L, Presents e6Cartan E F C ∧
      ∃ (H : LieSubalgebra ℂ L) (hH : IsMaximalToral_value H)
        (φ : Direction H) (hφ : Regular H φ) (s : Fin 6 ≃ simple H φ),
        (∀ x ∈ H, ω.map x ∈ H) ∧
        (∃ e f : simple H φ → L, Normalized H φ e f ∧
          E = e ∘ s ∧ F = f ∘ s) ∧
        (∀ i, C i = (coroot_value H (s i).val : L)) ∧
        (∀ i, ω.map (E i) = -F i ∧ ω.map (F i) = -E i ∧ ω.map (C i) = -C i) ∧
        ∀ i j, (e6Cartan i j : ℂ) = (s j).val (coroot_value H (s i).val) := by
  classical
  obtain ⟨⟨H, hH, φ, hφ, s, hs⟩, hwH⟩ := numbered_compact_cartan hss q ω hω
  obtain ⟨e, f, hn, hw⟩ := compact_pinning hss ω hω H hH hwH φ
  obtain ⟨c, _, A, hc, hA, hoff, T, he, hf, hh⟩ := serrePresentation hss hH hφ e f hn
  have hc' (i) : (c i : L) = (coroot_value H i.val : L) := congrArg Subtype.val (hc i).1
  have hE (i j : Fin 6) : (e6Cartan i j : ℂ) = (s j).val (coroot_value H (s i).val) := by
    rw [← e6_matrix, hs]
  have hA' (i j : Fin 6) : A (s i) (s j) = e6Cartan i j := by
    exact Int.cast_injective (α := ℂ) (by rw [hA, (hc _).1, hE])
  refine ⟨e ∘ s, f ∘ s, (fun i => (c i : L)) ∘ s,
    reindex_e6_presentation A s hA' hoff _ _ _ ⟨T, he, hf, hh⟩,
    H, hH, φ, hφ, s, hwH, ⟨e, f, hn, rfl, rfl⟩, (fun i => hc' _), ?_, hE⟩
  intro i
  change ω.map (e (s i)) = -f (s i) ∧ ω.map (f (s i)) = -e (s i) ∧
    ω.map (c (s i) : L) = -(c (s i) : L)
  have hfω : ω.map (f (s i)) = -e (s i) := by
    have he := congrArg ω.map (hw (s i))
    rw [ω.involutive, map_neg] at he
    exact neg_eq_iff_eq_neg.mp he.symm
  refine ⟨hw _, hfω, ?_⟩
  rw [hc', ← (hn (s i)).2.2.2.2, ω.map.map_lie, hw, hfω, lie_neg, neg_lie,
    neg_neg, ← lie_skew]

/-- The actual Vogan encoding in any Cartan transfers to the source E₆ numbering. -/
private theorem outer_datum (D : Diagram) (hss : IsSemisimple_value ℂ L)
    (q : NumberedCartan D L) (ω : Conjugation L) (hω : IsCompact ω)
    (a : L ≃ₗ⁅ℂ⁆ L) (ha : Intertwines ω ω a) (hi : Function.Involutive a)
    (hout : a.toLinearEquiv ∉ Specs.LieAlgebrasAndRepresentations.CartanConjugacy.innerAutomorphisms_value L) :
    D = .E6 ∧ ∃ (E F C : Fin 6 → L) (b : Coloring),
      Presents e6Cartan E F C ∧
      (∀ i, ω.map (E i) = -F i ∧ ω.map (F i) = -E i ∧ ω.map (C i) = -C i) ∧
      HasColor E F C b a := by
  classical
  obtain ⟨H, hH, z, hz, A, d, E, F, hP, hoff, hA, _, hN, hωE, hact⟩ :=
    StableCartanVoganData.encode hss ω hω a ha hi
  obtain ⟨s, hs⟩ := number_simple_roots hss q H hH.toral _ hz.regular
  have hentries (i j : Vertex D) : A (s i) (s j) = cartan D i j :=
    Int.cast_injective (α := ℂ) ((hA (s i) (s j)).trans (hs i j))
  let p := (s.trans d.perm).trans s.symm
  have hp (i : Vertex D) : s (p i) = d.perm (s i) := s.apply_symm_apply _
  have hperm : IsDiagramPerm p := by
    intro i j
    rw [← hentries, hp, hp, d.preserves, hentries]
  rcases exceptionalDiagramPermutations D p hperm with h | ⟨rfl, h⟩
  · refine False.elim (hout ?_)
    apply (VoganEquivalence.normalizedInnerIffFixesCartan hss ω H hH.toral hH.compact_stable
      _ hz.regular E F hN (fun i => (hωE i).1) A d a hA hact).1.mpr
    apply (VoganEquivalence.normalizedInnerIffFixesCartan hss ω H hH.toral hH.compact_stable
      _ hz.regular E F hN (fun i => (hωE i).1) A d a hA hact).2.mpr
    intro i
    obtain ⟨j, rfl⟩ := s.surjective i
    rw [← hp, h]
  · have h : p = diagramInvolution := by simpa only [cast_eq] using h
    letI : DecidableEq (simple H (evaluation H z)) := Classical.decEq _
    let C (i : simple H (evaluation H z)) : L := coroot_value H i.val
    let b : Coloring := (if d.sign (s 2) = 1 then 0 else 1,
      if d.sign (s 5) = 1 then 0 else 1)
    have hb (i : Fin 6) : colorSign (vertexColor b i) = d.sign (s i) := by
      have hpaired (j : Fin 6) (hj : diagramInvolution j ≠ j) : d.sign (s j) = 1 :=
        d.paired _ (fun he => hj (s.injective (by rw [← h, hp, he])))
      have sgn (x : ℂ) (hx : x = 1 ∨ x = -1) :
          colorSign (if x = 1 then 0 else 1) = x := by
        rcases hx with rfl | rfl <;> norm_num [colorSign]
      fin_cases i
      · simp [vertexColor, colorSign, hpaired 0 (by decide)]
      · simp [vertexColor, colorSign, hpaired 1 (by decide)]
      · simpa [vertexColor, b] using sgn (d.sign (s 2)) (d.sign_cases (s 2))
      · simp [vertexColor, colorSign, hpaired 3 (by decide)]
      · simp [vertexColor, colorSign, hpaired 4 (by decide)]
      · simpa [vertexColor, b] using sgn (d.sign (s 5)) (d.sign_cases (s 5))
    refine ⟨rfl, E ∘ s, F ∘ s, C ∘ s, b,
      reindex_e6_presentation A s (by simpa only [e6_matrix] using hentries) hoff _ _ _ hP,
      (fun i => hωE (s i)), fun i => ?_⟩
    have hed : s (diagramInvolution i) = d.perm (s i) := by rw [← h, hp]
    simpa only [Function.comp_apply, hb, hed, C] using hact (s i)

end Outer

section SplitForm

open Specs.LieAlgebrasAndRepresentations.ChevalleyBasis (Root)
open Specs.LieAlgebrasAndRepresentations.CompactConjugation (PositiveRoot asRoot opposite)
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
  (compactPart noncompactPart compactEigenspace mulI)
open private coordinateConjugation coordinateConjugation_basis coordinateConjugation_lie
  involutive_of_basis span_eq_fixed opposite_involutive rootPairs rootPairs_pos rootPairs_neg
  compactComplexBasis compactComplexBasis_cartan compactComplexBasis_difference
  compactComplexBasis_sum from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactConjugation
open private toConjugation from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactRealForm
open private finrank_fixed_of_signs from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalInnerInvolutions
open Complex

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem fixed_rank_of_root_planes {S P : Type*} [Fintype P] [Fintype S]
    (a : L ≃ₗ⁅ℂ⁆ L) (d : Basis (S ⊕ (P ⊕ P)) ℂ L)
    (hS : ∀ i, a (d (.inl i)) = -d (.inl i))
    (hP : ∀ i, a (d (.inr (.inl i))) = d (.inr (.inl i)))
    (hN : ∀ i, a (d (.inr (.inr i))) = -d (.inr (.inr i))) :
    finrank ℂ (complexFixed a) = Fintype.card P := by
  classical
  let A (i : S ⊕ (P ⊕ P)) : Submodule ℂ L := ℂ ∙ d i
  let ε : S ⊕ (P ⊕ P) → ℂ
    | .inr (.inl _) => 1
    | _ => -1
  have hA : DirectSum.IsInternal A := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      d.linearIndependent.iSupIndep_span_singleton ?_
    apply top_unique
    rw [← d.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (le_iSup A i) (Submodule.subset_span (Set.mem_singleton _))
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    rintro (i | (i | i)) <;> simp [ε]
  have hv : ∀ i, a (d i) = ε i • d i := by
    rintro (i | (i | i))
    · simpa [ε] using hS i
    · simpa [ε] using hP i
    · simpa [ε] using hN i
  have hl (i) (x : L) (hx : x ∈ A i) : a x = ε i • x := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hv, smul_comm]
  let Good := {i // ε i = 1}
  let f (i : P) : Good := ⟨.inr (.inl i), rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact Sum.inl.inj (Sum.inr.inj (congrArg Subtype.val h))
    · rintro ⟨i | (i | i), hi⟩
      · exact False.elim (by norm_num [ε] at hi)
      · exact ⟨i, rfl⟩
      · exact False.elim (by norm_num [ε] at hi)
  let e := Equiv.ofBijective f hf
  have h := finrank_fixed_of_signs a A hA ε hε hl
  have hr (i : Good) : finrank ℂ (A i.val) = 1 := finrank_span_singleton (d.ne_zero _)
  rw [h]
  simp only [hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact Fintype.card_congr e.symm

set_option maxHeartbeats 0 in
theorem splitChevalley : splitChevalleyType.{u} := by
  classical
  intro D L _ _ _ hss q
  let H := q.subalgebra
  let φ := q.direction
  obtain ⟨negRoot, x, b, τ, hτ, _, hx, hbr, hbH, hbx, hbInt, hi, hτH, hτx, _, _, _, _,
    hneg, _, _, _⟩ := CompactConjugation.construction hss H q.maximalToral φ q.regular
  let s := coordinateConjugation b
  have hs (i) : s (b i) = b i := coordinateConjugation_basis b i
  let σ : Conjugation L := toConjugation s (coordinateConjugation_lie b hbInt)
    (involutive_of_basis b s (fun i => by rw [hs, hs]))
  let ω : Conjugation L := toConjugation τ hτ hi
  have hω : IsCompact ω := hneg
  have hσb (i) : σ.map (b i) = b i := hs i
  have hτb (i) : s (τ (b i)) = τ (b i) := by
    rcases i with i | α
    · rw [hbH, hτH, ← hbH, map_neg, hs]
    · rw [hbx, hτx, ← hbx, map_neg, hs]
  have hsw (z : L) : σ.map (ω.map z) = ω.map (σ.map z) := by
    have h : s.comp τ = τ.comp s := by
      apply b.ext
      intro i
      change s (τ (b i)) = τ (s (b i))
      rw [hs, hτb]
    exact LinearMap.congr_fun h z
  let a : L ≃ₗ⁅ℂ⁆ L := sandwich ω σ LieEquiv.refl
  have happ (v : L) : a v = ω.map (σ.map v) := rfl
  have ha : Intertwines ω ω a := by
    intro v
    rw [happ, happ, ω.involutive, hsw, ω.involutive]
  have ha2 : Function.Involutive a := by
    intro v
    rw [happ, happ, hsw, ω.involutive, σ.involutive]
  have hform : involutionConjugation ω a ha ha2 = σ := by
    apply Conjugation.ext_map
    ext v
    change a (ω.map v) = σ.map v
    rw [happ, hsw, ω.involutive]
  let E := Equiv.sumCongr (Equiv.refl (simple H φ)) (rootPairs q.regular negRoot)
  let bp := b.reindex E.symm
  let d := compactComplexBasis bp
  have hdH (i : simple H φ) : d (.inl i) = I • (coroot_value H i.val : L) := by
    rw [compactComplexBasis_cartan]
    simpa [bp, E] using congrArg (I • ·) (hbH i)
  have hbplus (α : PositiveRoot H φ) : bp (.inr (.inl α)) = x (asRoot α) := by
    simp only [bp, Basis.reindex_apply, E, Equiv.symm_symm, Equiv.sumCongr_apply, Sum.map_inr]
    rw [rootPairs_pos q.regular negRoot α, hbx]
  have hbminus (α : PositiveRoot H φ) :
      bp (.inr (.inr α)) = x (opposite negRoot (asRoot α)) := by
    simp only [bp, Basis.reindex_apply, E, Equiv.symm_symm, Equiv.sumCongr_apply, Sum.map_inr]
    rw [rootPairs_neg q.regular negRoot α, hbx]
  have hdDiff (α : PositiveRoot H φ) :
      d (.inr (.inl α)) = x (asRoot α) - x (opposite negRoot (asRoot α)) := by
    rw [compactComplexBasis_difference, hbplus, hbminus]
  have hdSum (α : PositiveRoot H φ) :
      d (.inr (.inr α)) = I • (x (asRoot α) + x (opposite negRoot (asRoot α))) := by
    rw [compactComplexBasis_sum, hbplus, hbminus]
  have haH (i : simple H φ) : a (d (.inl i)) = -d (.inl i) := by
    rw [hdH, map_smul, happ, ← hbH, hσb, hbH]
    change I • τ (coroot_value H i.val : L) = -(I • (coroot_value H i.val : L))
    rw [hτH, smul_neg]
  have hσx (α) : σ.map (x α) = x α := by rw [← hbx, hσb]
  have hax (α) : a (x α) = -x (opposite negRoot α) := by
    rw [happ, hσx]
    exact hτx α
  have hDiff (α : PositiveRoot H φ) : a (d (.inr (.inl α))) = d (.inr (.inl α)) := by
    rw [hdDiff, map_sub, hax, hax, opposite_involutive]
    abel
  have hSum (α : PositiveRoot H φ) : a (d (.inr (.inr α))) = -d (.inr (.inr α)) := by
    rw [hdSum, map_smul, map_add, hax, hax, opposite_involutive, add_comm
      (-(x (opposite negRoot (asRoot α)))), ← neg_add, smul_neg]
  letI : Fintype (PositiveRoot H φ) := ((rootSet_finite H q.maximalToral.1).subset
    (fun _ h => h.1)).fintype
  letI : Fintype (simple H φ) := ((rootSet_finite H q.maximalToral.1).subset
    (fun _ h => h.1.1)).fintype
  have hK := fixed_rank_of_root_planes a d haH hDiff hSum
  have hL := Module.finrank_eq_card_basis d
  have hS : Fintype.card (simple H φ) = D.rank :=
    (Fintype.card_congr q.number.symm).trans (Fintype.card_fin _)
  simp only [Fintype.card_sum] at hL
  rw [hS] at hL
  have hsig := CartanDecompositionSignature.killing_signature ω a ha ha2 hω
  rw [hform, hK, hL] at hsig
  refine ⟨σ, negRoot, x, b, fixed_isRealForm σ, (fun α => ⟨(hx α).1, (hx α).2, hbr α⟩),
    hbH, hbx, hbInt, hσb, span_eq_fixed b s (coordinateConjugation_lie b hbInt) hs,
    ?_, by change killingSignature σ.fixed = _ at hsig; rw [hsig]; push_cast; ring⟩
  intro α
  let p := x (asRoot α) + x (opposite negRoot (asRoot α))
  let n := d (.inr (.inl α))
  have hwn : ω.map n = n := by
    change τ (d (.inr (.inl α))) = d (.inr (.inl α))
    rw [hdDiff, map_sub, hτx, hτx, opposite_involutive]
    abel
  have hwp : ω.map (d (.inr (.inr α))) = d (.inr (.inr α)) := by
    rw [hdSum, ω.antilinear, star_def, conj_I, map_add]
    change (-I) • (τ (x (asRoot α)) + τ (x (opposite negRoot (asRoot α)))) = _
    rw [hτx, hτx, opposite_involutive, ← neg_add, smul_neg, neg_smul, neg_neg, add_comm]
  have hnp : I • (-d (.inr (.inr α))) = p := by
    rw [hdSum, smul_neg, smul_smul, ← pow_two, I_sq, neg_smul, one_smul, neg_neg]
  let ρ := involutionConjugation ω a ha ha2
  have hnm : n ∈ compactEigenspace ω a 1 := ⟨hwn, by simpa [n] using hDiff α⟩
  have hpm : -d (.inr (.inr α)) ∈ compactEigenspace ω a (-1) := by
    refine ⟨by rw [map_neg, hwp], ?_⟩
    rw [map_neg, hSum, neg_smul, one_smul]
  have hnρ : n ∈ ρ.fixed := by
    change a (ω.map n) = n
    rw [hwn, hDiff]
  have hpρ : p ∈ ρ.fixed := by
    rw [← hnp]
    change a (ω.map (I • -d (.inr (.inr α)))) = I • -d (.inr (.inr α))
    rw [ω.antilinear, star_def, conj_I, hpm.1, map_smul, hpm.2, smul_smul, mul_neg_one, neg_neg]
  let pn : ρ.fixed := ⟨n, hnρ⟩
  let pp : ρ.fixed := ⟨p, hpρ⟩
  have hnpart : pn ∈ compactPart ω a ha ha2 := hnm
  have hppart : pp ∈ noncompactPart ω a ha ha2 :=
    Submodule.mem_map.mpr ⟨-d (.inr (.inr α)), hpm, hnp⟩
  obtain ⟨hneg', hpos', _⟩ := CartanDecompositionSignature.cartan_killing ω a ha ha2 hω
  have hneN : pn ≠ 0 := fun h => d.ne_zero _ (congrArg Subtype.val h)
  have hneP : pp ≠ 0 := by
    intro h
    have hh : p = 0 := congrArg Subtype.val h
    rw [← hnp, smul_eq_zero] at hh
    exact hh.elim I_ne_zero (fun h => d.ne_zero _ (neg_eq_zero.mp h))
  have hP := hpos' ⟨pp, hppart⟩ hneP
  have hN := hneg' ⟨pn, hnpart⟩ hneN
  change ∃ p' n' : σ.fixed, (p' : L) = p ∧ (n' : L) = _ ∧ _
  rw [← hform]
  exact ⟨pp, pn, rfl, hdDiff α, hP, hN⟩

end SplitForm

section Classification

open _root_.LieAlgebrasAndRepresentations.Serre
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open Specs.LieAlgebrasAndRepresentations.CartanConjugacy (innerAutomorphisms_value)
open private outerDiagram killingSignature_equiv
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem normalized_outer_not_inner (hss : IsSemisimple_value ℂ L)
    (ω : Conjugation L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral_value H)
    (φ : Direction H) (hφ : Regular H φ) (s : Fin 6 ≃ simple H φ)
    (hwH : ∀ x ∈ H, ω.map x ∈ H)
    (E F : simple H φ → L) (hN : Normalized H φ E F)
    (hω : ∀ i, ω.map (E i) = -F i)
    (hA : ∀ i j, (e6Cartan i j : ℂ) = (s j).val (coroot_value H (s i).val))
    (b : Coloring) (a : L ≃ₗ⁅ℂ⁆ L)
    (ha : HasColor (E ∘ s) (F ∘ s) ((fun i => (coroot_value H i.val : L)) ∘ s) b a) :
    a.toLinearEquiv ∉ innerAutomorphisms_value L := by
  classical
  let A : Matrix (simple H φ) (simple H φ) ℤ := fun i j => e6Cartan (s.symm i) (s.symm j)
  let d₀ := outerDiagram b
  let d : DiagramData A :=
    { perm := (s.symm.trans diagramInvolution).trans s
      involutive := fun i => by
        change s (diagramInvolution (s.symm (s (diagramInvolution (s.symm i))))) = i
        have h : Function.Involutive diagramInvolution := diagramInvolution.left_inv
        rw [s.symm_apply_apply, h, s.apply_symm_apply]
      preserves := fun i j => by
        simpa [A, d₀, outerDiagram] using d₀.preserves (s.symm i) (s.symm j)
      sign := fun i => d₀.sign (s.symm i)
      sign_cases := fun i => d₀.sign_cases (s.symm i)
      paired := fun i hi => d₀.paired (s.symm i) (fun h => hi (by
        change s (diagramInvolution (s.symm i)) = i
        change diagramInvolution (s.symm i) = s.symm i at h
        rw [h, s.apply_symm_apply])) }
  have hA' (i j) : (A i j : ℂ) = j.val (coroot_value H i.val) := by
    simpa [A] using hA (s.symm i) (s.symm j)
  have ha' (i) : a (E i) = d.sign i • E (d.perm i) ∧
      a (F i) = d.sign i • F (d.perm i) ∧
      a (coroot_value H i.val : L) = coroot_value H (d.perm i).val := by
    simpa [d, d₀, outerDiagram, Function.comp_apply] using ha (s.symm i)
  intro hn
  obtain ⟨hfix, hperm⟩ :=
    VoganEquivalence.normalizedInnerIffFixesCartan hss ω H hH hwH φ hφ E F hN hω A d a hA' ha'
  have he := hperm.mp (hfix.mp hn) (s 0)
  exact diagramInvolution_moves (s.injective (by simpa [d] using he))

/-- Changing matched pinnings transports a normalized datum of a given color. -/
private theorem transport_outer_forms (ω : Conjugation L)
    (E F C E' F' C' : Fin 6 → L)
    (hP : Presents e6Cartan E F C) (hP' : Presents e6Cartan E' F' C')
    (hw : ∀ i, ω.map (E i) = -F i ∧ ω.map (F i) = -E i ∧ ω.map (C i) = -C i)
    (hw' : ∀ i, ω.map (E' i) = -F' i ∧ ω.map (F' i) = -E' i ∧ ω.map (C' i) = -C' i)
    (b : Coloring) (a a' : L ≃ₗ⁅ℂ⁆ L)
    (ha : HasColor E F C b a) (ha' : HasColor E' F' C' b a')
    (hc : Intertwines ω ω a) (hc' : Intertwines ω ω a')
    (hi : Function.Involutive a) (hi' : Function.Involutive a') :
    Nonempty ((involutionConjugation ω a hc hi).fixed ≃ₗ⁅ℝ⁆
      (involutionConjugation ω a' hc' hi').fixed) := by
  obtain ⟨p, pe, pf, ph⟩ := hP
  obtain ⟨q, qe, qf, qh⟩ := hP'
  let g := p.symm.trans q
  have hgen (i : Fin 6) : g (E i) = E' i ∧ g (F i) = F' i ∧ g (C i) = C' i := by
    simp [g, ← pe i, ← pf i, ← ph i, qe, qf, qh]
  let j := sandwich ω ω g
  have hj : j.toLieHom.comp p.toLieHom = g.toLieHom.comp p.toLieHom := by
    apply hom_ext e6Cartan <;> intro i
    · change ω.map (g (ω.map (p (e e6Cartan i)))) = g (p (e e6Cartan i))
      rw [pe, (hw i).1, map_neg, (hgen i).2.1, map_neg, (hw' i).2.1, neg_neg, (hgen i).1]
    · change ω.map (g (ω.map (p (f e6Cartan i)))) = g (p (f e6Cartan i))
      rw [pf, (hw i).2.1, map_neg, (hgen i).1, map_neg, (hw' i).1, neg_neg, (hgen i).2.1]
    · change ω.map (g (ω.map (p (h e6Cartan i)))) = g (p (h e6Cartan i))
      rw [ph, (hw i).2.2, map_neg, (hgen i).2.2, map_neg, (hw' i).2.2, neg_neg]
  have hgw : Intertwines ω ω g := by
    intro x
    obtain ⟨y, hy⟩ := p.surjective (ω.map x)
    have h := LieHom.congr_fun hj y
    change ω.map (g (ω.map (p y))) = g (p y) at h
    change p y = ω.map x at hy
    rwa [hy, ω.involutive] at h
  have heq : a'.toLieHom.comp (g.toLieHom.comp p.toLieHom) =
      g.toLieHom.comp (a.toLieHom.comp p.toLieHom) := by
    apply hom_ext e6Cartan <;> intro i
    · change a' (g (p (e e6Cartan i))) = g (a (p (e e6Cartan i)))
      rw [pe, (hgen i).1, (ha' i).1, (ha i).1, map_smul, (hgen _).1]
    · change a' (g (p (f e6Cartan i))) = g (a (p (f e6Cartan i)))
      rw [pf, (hgen i).2.1, (ha' i).2.1, (ha i).2.1, map_smul, (hgen _).2.1]
    · change a' (g (p (h e6Cartan i))) = g (a (p (h e6Cartan i)))
      rw [ph, (hgen i).2.2, (ha' i).2.2, (ha i).2.2, (hgen _).2.2]
  apply (forms_isomorphic_iff _ _).mpr
  refine ⟨g, fun x => ?_⟩
  change a' (ω.map (g x)) = g (a (ω.map x))
  rw [hgw]
  obtain ⟨y, hy⟩ := p.surjective (ω.map x)
  rw [← hy]
  exact LieHom.congr_fun heq y

private def outerColor (k : Bool) : Coloring := if k then (1, 0) else 0

private theorem outerColor_zero (k : Bool) : outerColor k = 0 ↔ k = false := by
  cases k <;> decide

private theorem outer_representatives (hss : IsSemisimple_value ℂ L)
    (q : NumberedCartan .E6 L) (ω : Conjugation L) (hω : IsCompact ω) :
    ∃ (a : Bool → L ≃ₗ⁅ℂ⁆ L) (ha : ∀ k, Intertwines ω ω (a k))
      (hi : ∀ k, Function.Involutive (a k)),
      (∀ k, Matches (.inr (⟨rfl⟩, k) : RowIndex .E6) ω (a k) (ha k) (hi k)) ∧
      (∀ k, (a k).toLinearEquiv ∉ innerAutomorphisms_value L) ∧
      ∀ (t : L ≃ₗ⁅ℂ⁆ L) (ht : Intertwines ω ω t) (hit : Function.Involutive t),
        t.toLinearEquiv ∉ innerAutomorphisms_value L →
        ∃ k, Nonempty ((involutionConjugation ω t ht hit).fixed ≃ₗ⁅ℝ⁆
          (involutionConjugation ω (a k) (ha k) (hi k)).fixed) := by
  classical
  obtain ⟨E, F, C, hP, H, hH, φ, hφ, s, hwH, ⟨e₀, f₀, hN, rfl, rfl⟩, hC, hw, hA⟩ :=
    exists_compatible_e6_presentation hss q ω hω
  choose a hcolor ha hi using ExceptionalOuterInvolutions.realizeOuter ω _ _ _ hP hw
  obtain ⟨hclass, hmatches⟩ := ExceptionalOuterInvolutions.outerClassification ω hω _ _ _ hP hw
  refine ⟨(fun k => a (outerColor k)), (fun k => ha _), (fun k => hi _), ?_, ?_, ?_⟩
  · intro k
    have h := hmatches _ _ (hcolor (outerColor k)) (ha _) (hi _)
    cases k
    · simpa [outerColor, Matches] using h
    · have hne : outerColor true ≠ 0 := by decide
      simpa only [hne, ite_false, Matches] using h
  · intro k
    apply normalized_outer_not_inner hss ω H hH φ hφ s hwH e₀ f₀ hN
      (fun i => by simpa using (hw (s.symm i)).1) hA (outerColor k)
    intro i
    simpa only [Function.comp_apply, hC] using hcolor (outerColor k) i
  · intro t ht hit hout
    obtain ⟨_, E', F', C', b, hP', hw', hcolor'⟩ := outer_datum .E6 hss q ω hω t ht hit hout
    have he := transport_outer_forms ω E' F' C' _ _ _ hP' hP hw' hw
      b t (a b) hcolor' (hcolor b) ht (ha b) hit (hi b)
    let k := decide (b ≠ 0)
    have hk : (b = 0 ↔ outerColor k = 0) := by
      rw [outerColor_zero]
      simp [k]
    obtain ⟨e₁⟩ := he
    obtain ⟨e₂⟩ := (hclass b (outerColor k) (a b) (a (outerColor k))
      (hcolor b) (hcolor (outerColor k)) (ha b) (hi b) (ha _) (hi _)).2 hk
    exact ⟨k, ⟨e₁.trans e₂⟩⟩

private theorem signature_injective (D : Diagram) :
    Function.Injective (signature (D := D)) := by
  rintro (r | ⟨⟨h⟩, b⟩) (t | ⟨⟨h'⟩, c⟩) hs
  · rcases r with ⟨r, hr⟩
    rcases t with ⟨t, ht⟩
    cases D <;> simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr ht
    all_goals
      rcases hr with rfl | rfl | rfl | rfl <;>
        rcases ht with rfl | rfl | rfl | rfl <;>
        first | rfl | (dsimp [signature] at hs; exact (absurd hs (by decide)))
  · subst D
    rcases r with ⟨r, hr⟩
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
    cases c <;> rcases hr with rfl | rfl | rfl <;> norm_num [signature] at hs
  · subst D
    rcases t with ⟨t, ht⟩
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at ht
    cases b <;> rcases ht with rfl | rfl | rfl <;> norm_num [signature] at hs
  · subst D
    cases b <;> cases c <;> first | rfl | norm_num [signature] at hs

private theorem signature_of_matches {D : Diagram} (r : RowIndex D)
    (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) (ha : Intertwines ω ω a)
    (hi : Function.Involutive a) (h : Matches r ω a ha hi) :
    killingSignature (involutionConjugation ω a ha hi).fixed = signature r := by
  rcases r with r | ⟨_, b⟩
  · exact h.2.2
  · cases b <;> exact h.2.2

private theorem compact_index_has_signature (D : Diagram) (ω : Conjugation L)
    (hω : IsCompact ω) (a : L ≃ₗ⁅ℂ⁆ L) (ha : Intertwines ω ω a)
    (hi : Function.Involutive a) (hm : Matches (compactIndex D) ω a ha hi) :
    killingSignature ω.fixed = signature (compactIndex D) := by
  let idL : L ≃ₗ⁅ℂ⁆ L := LieEquiv.refl
  have hid : complexFixed idL = ⊤ := by
    ext x
    simp [complexFixed, idL]
  have hd : Module.finrank ℂ (complexFixed idL) = Module.finrank ℂ L := by
    change Module.finrank ℂ (complexFixed idL).toSubmodule = _
    rw [hid, LieSubalgebra.top_toSubmodule, finrank_top]
  have hsig := CartanDecompositionSignature.killing_signature ω a ha hi hω
  have hr := signature_of_matches (compactIndex D) ω a ha hi hm
  have hdim : (Module.finrank ℂ (complexFixed a) : ℤ) = -signature (compactIndex D) := by
    have h := hm.2.1
    cases D <;> norm_num [compactIndex, signature, rows] at h ⊢ <;> exact_mod_cast h
  change killingSignature _ = (Module.finrank ℂ L : ℤ) -
    2 * (Module.finrank ℂ (complexFixed a) : ℤ) at hsig
  rw [hr, hdim] at hsig
  have hσ := CartanDecompositionSignature.killing_signature ω idL (fun _ => rfl) (fun _ => rfl) hω
  have hωid : involutionConjugation ω idL (fun _ => rfl) (fun _ => rfl) = ω := by
    apply Conjugation.ext_map
    rfl
  change killingSignature (involutionConjugation ω idL _ _).fixed =
    (Module.finrank ℂ L : ℤ) - 2 * (Module.finrank ℂ (complexFixed idL) : ℤ) at hσ
  rw [hωid, hd] at hσ
  linarith

set_option maxHeartbeats 0 in
theorem exceptionalRealForms : exceptionalRealFormsType.{u} := by
  classical
  intro D L _ _ _ hss q
  refine ⟨?_, ?_⟩
  · obtain ⟨ω, _, hω⟩ := CompactRealForm.compact_real_form hss
    exact ⟨ω, hω⟩
  intro ω hω
  obtain ⟨_, a₀, ha₀, _, _, _, hrows, hcover, _⟩ :=
    ExceptionalInnerInvolutions.innerInvolutionClasses D hss q ω hω
  have hout :
      ∀ h : D = .E6, ∃ (a : Bool → L ≃ₗ⁅ℂ⁆ L) (ha : ∀ k, Intertwines ω ω (a k))
        (hi : ∀ k, Function.Involutive (a k)),
        (∀ k, Matches (.inr (⟨h⟩, k) : RowIndex D) ω (a k) (ha k) (hi k)) ∧
        (∀ k, (a k).toLinearEquiv ∉ innerAutomorphisms_value L) ∧
        ∀ (b : L ≃ₗ⁅ℂ⁆ L) (hb : Intertwines ω ω b) (hib : Function.Involutive b),
          b.toLinearEquiv ∉ innerAutomorphisms_value L →
          ∃ k, Nonempty ((involutionConjugation ω b hb hib).fixed ≃ₗ⁅ℝ⁆
            (involutionConjugation ω (a k) (ha k) (hi k)).fixed) := by
    rintro rfl
    exact outer_representatives hss q ω hω
  choose a₁ ha₁ hi₁ hrows₁ hnot₁ hcover₁ using hout
  let a : RowIndex D → L ≃ₗ⁅ℂ⁆ L
    | .inl r => a₀ r
    | .inr (⟨h⟩, k) => a₁ h k
  have ha : ∀ r, Intertwines ω ω (a r)
    | .inl r => (ha₀ r).commutes
    | .inr (⟨h⟩, k) => ha₁ h k
  have hi : ∀ r, Function.Involutive (a r)
    | .inl r => (ha₀ r).involutive
    | .inr (⟨h⟩, k) => hi₁ h k
  let S := fun r => (involutionConjugation ω (a r) (ha r) (hi r)).fixed
  have hreal (r) : IsRealForm (S r) := fixed_isRealForm _
  have hmatch : ∀ r, Matches r ω (a r) (ha r) (hi r)
    | .inl r => hrows r
    | .inr (⟨h⟩, k) => hrows₁ h k
  have hs (r) : killingSignature (S r) = signature r :=
    signature_of_matches r ω (a r) (ha r) (hi r) (hmatch r)
  have hInner (r) : (a r).toLinearEquiv ∈ innerAutomorphisms_value L ↔
      ∃ t : TableRow D, r = .inl t := by
    rcases r with r | ⟨⟨h⟩, k⟩
    · exact ⟨fun _ => ⟨r, rfl⟩, fun _ => (ha₀ r).inner⟩
    · exact ⟨fun hn => False.elim (hnot₁ h k hn), by simp⟩
  have hdistinct (r t) : Nonempty (S r ≃ₗ⁅ℝ⁆ S t) ↔ r = t := by
    constructor
    · rintro ⟨e⟩
      exact signature_injective D ((hs r).symm.trans ((killingSignature_equiv e).trans (hs t)))
    · rintro rfl
      exact ⟨LieEquiv.refl⟩
  have form_of_conjugacy (b c : L ≃ₗ⁅ℂ⁆ L) (hb : Intertwines ω ω b)
      (hc : Intertwines ω ω c) (hib : Function.Involutive b) (hic : Function.Involutive c)
      (h : CompactConjugate ω b c) :
      Nonempty ((involutionConjugation ω b hb hib).fixed ≃ₗ⁅ℝ⁆
        (involutionConjugation ω c hc hic).fixed) := by
    obtain ⟨g, hgw, hg⟩ := h
    apply (forms_isomorphic_iff _ _).mpr
    refine ⟨g, fun x => ?_⟩
    change c (ω.map (g x)) = g (b (ω.map x))
    rw [hgw, hg]
  have hreduced (b : L ≃ₗ⁅ℂ⁆ L) (hb : Intertwines ω ω b) (hib : Function.Involutive b) :
      ∃ r, Nonempty ((involutionConjugation ω b hb hib).fixed ≃ₗ⁅ℝ⁆ S r) := by
    by_cases hn : b.toLinearEquiv ∈ innerAutomorphisms_value L
    · obtain ⟨r, hg, _⟩ := hcover b ⟨hn, hb, hib⟩
      exact ⟨.inl r, (form_of_conjugacy _ _ (ha₀ r).commutes hb
        (ha₀ r).involutive hib hg).map LieEquiv.symm⟩
    · obtain ⟨h, _⟩ := outer_datum D hss q ω hω b hb hib hn
      obtain ⟨k, hf⟩ := hcover₁ h b hb hib hn
      exact ⟨.inr (⟨h⟩, k), hf⟩
  have hinvolutions (b : L ≃ₗ⁅ℂ⁆ L) (hb : Intertwines ω ω b) (hib : Function.Involutive b) :
      ∃! r : RowIndex D, CompactConjugate ω b (a r) := by
    obtain ⟨r, ⟨e⟩⟩ := hreduced b hb hib
    obtain ⟨g, hg⟩ := (forms_isomorphic_iff _ _).mp ⟨e⟩
    refine ⟨r, compact_intertwiner ω hω b (a r) hb (ha r) hib (hi r) g hg, ?_⟩
    intro t ht
    obtain ⟨f⟩ := form_of_conjugacy b (a t) hb (ha t) hib (hi t) ht
    exact (hdistinct t r).mp ⟨f.symm.trans e⟩
  have hcover' (U : LieSubalgebra ℝ L) (hU : IsRealForm U) :
      ∃ r, Nonempty (U ≃ₗ⁅ℝ⁆ S r) := by
    obtain ⟨_, b, hb, hib, _, _, ⟨e⟩⟩ := PolarRealStructures.real_form_reduction ω hω U hU
    obtain ⟨r, ⟨f⟩⟩ := hreduced b hb hib
    exact ⟨r, ⟨e.trans f⟩⟩
  have hsig (U : LieSubalgebra ℝ L) (hU : IsRealForm U) (r : RowIndex D) :
      Nonempty (U ≃ₗ⁅ℝ⁆ S r) ↔ killingSignature U = signature r := by
    refine ⟨fun ⟨e⟩ => (killingSignature_equiv e).trans (hs r), fun he => ?_⟩
    obtain ⟨t, ⟨f⟩⟩ := hcover' U hU
    have ht : r = t := signature_injective D (he.symm.trans ((killingSignature_equiv f).trans (hs t)))
    exact ht ▸ ⟨f⟩
  have hcompact := (hsig ω.fixed (fixed_isRealForm ω) (compactIndex D)).mpr
    (compact_index_has_signature D ω hω _ _ _ (hmatch (compactIndex D)))
  refine ⟨a, ha, hi, (fun r => ⟨hreal r, hmatch r⟩), hInner, hdistinct,
    hinvolutions, hcompact.map LieEquiv.symm, ?_, hsig, ?_⟩
  · intro U hU
    obtain ⟨r, ⟨e⟩⟩ := hcover' U hU
    exact ⟨r, ⟨e⟩, fun t ⟨f⟩ => (hdistinct t r).mp ⟨f.symm.trans e⟩⟩
  · obtain ⟨σ, _, x, b, hσ, hx, hbH, hbx, hbInt, hfix, _, _, hsσ⟩ := splitChevalley D hss q
    refine ⟨σ.fixed, hσ, ⟨b, hbH, (fun α => by rw [hbx]; exact (hx α).1), hbInt, hfix⟩, ?_⟩
    intro V hV
    refine ⟨fun ⟨e⟩ => (killingSignature_equiv e).trans hsσ, fun hv => ?_⟩
    obtain ⟨r, ⟨e⟩⟩ := hcover' σ.fixed hσ
    have h := (hsig σ.fixed hσ r).mp ⟨e⟩
    obtain ⟨f⟩ := (hsig V hV r).mpr (hv.trans (hsσ.symm.trans h))
    exact ⟨f.trans e.symm⟩

end Classification

end

end LieAlgebrasAndRepresentations.ExceptionalRealClassification
