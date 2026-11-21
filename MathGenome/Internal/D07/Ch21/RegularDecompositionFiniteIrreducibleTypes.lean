import MathGenome.Internal.D07.Ch21.GroupAlgebra
import MathGenome.Internal.D07.Ch17.CompleteReducibility
import MathGenome.Internal.D07.Ch17.SchurNonscalar
import MathGenome.Internal.Specs.D07.Ch21.RegularDecompositionFiniteIrreducibleTypes
import Mathlib.Data.Fintype.Quotient

namespace D07.Ch21.RegularDecompositionFiniteIrreducibleTypes

universe u v
noncomputable section
open Specs.D07.Ch21.RegularDecompositionFiniteIrreducibleTypes

variable {G : Type u} {V : Type v} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V]

/-- The linear extension of the orbit map at a vector. -/
def orbitEvaluation (ρ : Representation ℂ G V) (v : V) : MonoidAlgebra ℂ G →ₗ[ℂ] V :=
  (LinearMap.applyₗ (R := ℂ) (M₂ := V) v).comp ρ.asAlgebraHom.toLinearMap

@[simp] lemma orbitEvaluation_apply (ρ : Representation ℂ G V) (v : V)
    (a : MonoidAlgebra ℂ G) : orbitEvaluation ρ v a = ρ.asAlgebraHom a v := rfl

@[simp] lemma orbitEvaluation_single (ρ : Representation ℂ G V) (v : V) (g : G) :
    orbitEvaluation ρ v (MonoidAlgebra.single g 1) = ρ g v := by
  simp

lemma orbitEvaluation_intertwining (ρ : Representation ℂ G V) (v : V) :
    (Representation.leftRegular ℂ G).IsIntertwiningMap ρ (orbitEvaluation ρ v) := by
  constructor
  intro g a
  have h : Representation.leftRegular ℂ G g a = MonoidAlgebra.single g 1 * a := by
    have h' := Representation.asAlgebraHom_ofMulAction_smul_eq_mul
      (k := ℂ) (G := G) (MonoidAlgebra.single g 1) a
    simpa using h'
  simp only [h, orbitEvaluation_apply, map_mul, Representation.asAlgebraHom_single_one]
  rfl

lemma orbitEvaluation_surjective (ρ : Representation ℂ G V)
    (hρ : Representation.IsIrreducible ρ) (v : V) (hv : v ≠ 0) :
    Function.Surjective (orbitEvaluation ρ v) := by
  let q : (Representation.leftRegular ℂ G).IntertwiningMap ρ :=
    ⟨orbitEvaluation ρ v,
      fun g => LinearMap.ext ((orbitEvaluation_intertwining ρ v).isIntertwining g)⟩
  haveI := hρ
  rcases eq_bot_or_eq_top q.range with h | h
  · have hmem : v ∈ q.range := by
      refine ⟨MonoidAlgebra.single 1 1, ?_⟩
      change orbitEvaluation ρ v (MonoidAlgebra.single 1 1) = v
      simp
    rw [h] at hmem
    exact False.elim (hv hmem)
  · exact LinearMap.range_eq_top.mp (congrArg Subrepresentation.toSubmodule h)

theorem cyclic_quotient : CyclicQuotient.{u,v} := by
  intro G V _ _ _ _ ρ hρ v hv
  refine ⟨orbitEvaluation ρ v, ?_, orbitEvaluation_single ρ v,
    orbitEvaluation_intertwining ρ v, orbitEvaluation_surjective ρ hρ v hv⟩
  exact fun a => (GroupAlgebra.extension_formula G V ρ).2.1 a v

theorem dimension_bound : DimensionBound.{u,v} := by
  intro G V _ _ _ _ ρ hρ
  haveI := D07.Ch17.IrreducibleDefinition.irreducible_nontrivial hρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hq := orbitEvaluation_surjective ρ hρ v hv
  haveI := (GroupAlgebra.dimension G).1
  refine ⟨Module.Finite.of_surjective (orbitEvaluation ρ v) hq, ?_⟩
  exact (LinearMap.finrank_le_finrank_of_surjective hq).trans_eq
    (GroupAlgebra.dimension G).2

/-- A quotient onto an irreducible is nonzero on some member of an internal
irreducible decomposition. Schur identifies that member with the quotient. -/
lemma complete_of_decomposition {n : ℕ}
    (U : Fin n → Subrepresentation (Representation.leftRegular ℂ G))
    (hU : ∀ i, Representation.IsIrreducible (U i).toRepresentation)
    (hi : DirectSum.IsInternal (fun i => (U i).toSubmodule))
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    ∃ i, Nonempty ((U i).toRepresentation.Equiv ρ) := by
  classical
  haveI := D07.Ch17.IrreducibleDefinition.irreducible_nontrivial hρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let q := orbitEvaluation ρ v
  let f (i : Fin n) := q.comp (U i).toSubmodule.subtype
  have hnonzero : ∃ i, f i ≠ 0 := by
    by_contra! h
    have hk : (⨆ i, (U i).toSubmodule) ≤ LinearMap.ker q := by
      apply iSup_le
      intro i x hx
      change q x = 0
      exact LinearMap.congr_fun (h i) ⟨x, hx⟩
    rw [hi.submodule_iSup_eq_top] at hk
    have hz : q (MonoidAlgebra.single 1 1) = 0 := hk (by trivial)
    exact hv (by simpa [q] using hz)
  obtain ⟨i, hfi⟩ := hnonzero
  have hfi' : (U i).toRepresentation.IsIntertwiningMap ρ (f i) := by
    constructor
    intro g x
    exact (orbitEvaluation_intertwining ρ v).isIntertwining g x.val
  obtain ⟨e, _⟩ := D07.Ch17.SchurNonscalar.nonzero_intertwiner_equivalence
    ℂ G (U i).toSubmodule V (U i).toRepresentation ρ (f i) (hU i) hρ hfi' hfi
  exact ⟨i, ⟨e⟩⟩

theorem regular_summands_complete : RegularSummandsComplete.{u,v} := by
  intro G _ _
  haveI := (GroupAlgebra.dimension G).1
  have hm : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  obtain ⟨n, U, hU, hi⟩ := D07.Ch17.CompleteReducibility.internal_decomposition
    ℂ G (MonoidAlgebra ℂ G) hm (Representation.leftRegular ℂ G)
  exact ⟨n, U, hU, hi, fun V _ _ ρ hρ => complete_of_decomposition U hU hi ρ hρ⟩

theorem finite_complete_family : FiniteCompleteFamily.{u,v} := by
  classical
  intro G _ _
  obtain ⟨n, U, hU, hi, hc⟩ := regular_summands_complete.{u,v} G
  have hn : Nonempty (Fin n) := by
    by_contra h
    haveI : IsEmpty (Fin n) := not_nonempty_iff.mp h
    have hh := hi.submodule_iSup_eq_top
    have hb : (⊥ : Submodule ℂ (MonoidAlgebra ℂ G)) = ⊤ := by simpa using hh
    exact bot_ne_top hb
  let R : Setoid (Fin n) := {
    r := fun i j => Nonempty ((U i).toRepresentation.Equiv (U j).toRepresentation)
    iseqv := ⟨fun i => ⟨Representation.Equiv.refl _⟩,
      fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩
  }
  let s : Finset (Subrepresentation (Representation.leftRegular ℂ G)) :=
    Finset.univ.image (fun a : Quotient R => U a.out)
  have hmem (a : Quotient R) : U a.out ∈ s :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  refine ⟨s, ⟨U (Quotient.mk R (Classical.choice hn)).out, hmem _⟩, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hA
    exact hU a.out
  · intro A hA B hB hAB ⟨e⟩
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hB
    have hab : a = b := by
      have heq : Quotient.mk R a.out = Quotient.mk R b.out := Quotient.sound ⟨e⟩
      simpa using heq
    exact hAB (congrArg (fun a : Quotient R => U a.out) hab)
  · intro V _ _ ρ hρ
    obtain ⟨i, ⟨e⟩⟩ := hc V ρ hρ
    let a : Quotient R := Quotient.mk R i
    have hai : R a.out i := Quotient.mk_out i
    obtain ⟨f⟩ := hai
    exact ⟨U a.out, hmem a, ⟨f.trans e⟩⟩

theorem trivial_group_type : TrivialGroupType.{u,v} := by
  intro G V _ _ _ _ _ ρ hρ
  have hf := (dimension_bound G V ρ hρ).1
  haveI := hf
  haveI := D07.Ch17.IrreducibleDefinition.irreducible_nontrivial hρ
  have hd : Module.finrank ℂ V = 1 := by
    have hb := (dimension_bound G V ρ hρ).2
    have hp : 0 < Module.finrank ℂ V := Module.finrank_pos
    have hc : Fintype.card G = 1 :=
      Nat.le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)
        Fintype.card_pos
    exact Nat.le_antisymm (hc ▸ hb) hp
  let e : V ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq V ℂ (by simpa using hd)
  refine ⟨hf, hd, ⟨Representation.Equiv.mk e ?_⟩⟩
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  subst g
  ext x
  simp

end
end D07.Ch21.RegularDecompositionFiniteIrreducibleTypes
