import MathGenome.Internal.Specs.D07.Ch21.InductionCosetModel
import MathGenome.Internal.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence
import Mathlib.Logic.Equiv.Fin.Basic

namespace D07.Ch21.InductionCosetModel

universe u v
noncomputable section
open Representation
open scoped TensorProduct
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.InductionCosetModel
open D07.Ch21.InductionCosetModelInductionConventionBridge

/-- Restriction retains the original vector space and scalar action. -/
def restrict : RestrictionType.{u,v} :=
  fun _ _ H _ _ _ ρ => ρ.comp H.subtype

theorem restriction_laws : RestrictionLaws.{u,v} := by
  intro G _ _ H V _ _ ρ
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · exact map_one (ρ.comp H.subtype)
  · intro h k
    exact map_mul (ρ.comp H.subtype) h k
  · intro h v
    exact ⟨Representation.inv_self_apply (ρ.comp H.subtype) h v,
      Representation.self_inv_apply (ρ.comp H.subtype) h v⟩

theorem induced_construction : InducedConstruction.{u,v} := by
  intro G _ _ H V _ _ ρ
  refine ⟨fun k _ hx => relations_invariant H ρ k hx,
    notesRep H ρ, notesRep_quotient H ρ, notesRep_mk H ρ, notes_balance H ρ, ?_⟩
  intro k x
  exact ⟨(notesRep H ρ).inv_self_apply k x, (notesRep H ρ).self_inv_apply k x⟩

theorem coset_decomposition : CosetDecomposition.{u} :=
  D07.Ch21.InductionCosetModelCosetCoordinateEquivalence.transversal_decomposition

theorem coset_construction : CosetConstruction.{u,v} :=
  D07.Ch21.InductionCosetModelCosetCoordinateEquivalence.coordinate_construction

theorem dimension : Dimension.{u,v} :=
  D07.Ch21.InductionCosetModelCosetCoordinateEquivalence.induction_dimension

theorem representative_independence : RepresentativeIndependence.{u,v} :=
  D07.Ch21.InductionCosetModelCosetCoordinateEquivalence.representative_change

theorem zero_induction : ZeroInduction.{u,v} := by
  intro G _ _ H V _ _ _ ρ
  infer_instance

section Full

variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- Evaluation [g,v] ↦ ρ(g)v is balanced for the full subgroup. -/
def fullEvaluation : NotesInd (⊤ : Subgroup G) (ρ.comp (⊤ : Subgroup G).subtype) →ₗ[ℂ] V :=
  notesLift _ _ (fun g => ρ g) (by
    intro g h v
    exact congrArg (fun f : Module.End ℂ V => f v) (map_mul ρ g (h : G)))

@[simp] lemma fullEvaluation_mk (g : G) (v : V) :
    fullEvaluation ρ (notesMk ⊤ (ρ.comp (⊤ : Subgroup G).subtype) g v) = ρ g v :=
  notesLift_mk _ _ _ _ _ _

/-- Evaluation and v ↦ [1,v] are inverse on all vectors. -/
def fullLinearEquiv : NotesInd (⊤ : Subgroup G) (ρ.comp (⊤ : Subgroup G).subtype) ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinearMap (fullEvaluation ρ)
    (notesMk ⊤ (ρ.comp (⊤ : Subgroup G).subtype) 1)
    (by
      ext v
      simp)
    (by
      apply notes_hom_ext
      intro g v
      change notesMk ⊤ (ρ.comp (⊤ : Subgroup G).subtype) 1
        (fullEvaluation ρ (notesMk ⊤ (ρ.comp (⊤ : Subgroup G).subtype) g v)) = _
      rw [fullEvaluation_mk]
      simpa using (notes_balance (⊤ : Subgroup G) (ρ.comp (⊤ : Subgroup G).subtype)
        1 ⟨g, Subgroup.mem_top g⟩ v).symm)

/-- The full-subgroup identification is an equivalence of G-representations. -/
def fullRepresentationEquiv :
    (notesRep (⊤ : Subgroup G) (ρ.comp (⊤ : Subgroup G).subtype)).Equiv ρ :=
  Representation.Equiv.mk (fullLinearEquiv ρ) (by
    intro k
    apply notes_hom_ext
    intro g v
    change fullEvaluation ρ
      (notesRep ⊤ (ρ.comp (⊤ : Subgroup G).subtype) k
        (notesMk ⊤ (ρ.comp (⊤ : Subgroup G).subtype) g v)) =
      ρ k (fullEvaluation ρ (notesMk ⊤ (ρ.comp (⊤ : Subgroup G).subtype) g v))
    rw [notesRep_mk, fullEvaluation_mk, fullEvaluation_mk]
    exact congrArg (fun f : Module.End ℂ V => f v) (map_mul ρ k g))

end Full

theorem full_subgroup : FullSubgroup.{u,v} := by
  intro G _ _ V _ _ ρ
  refine ⟨notesRep ⊤ (ρ.comp (⊤ : Subgroup G).subtype),
    fullRepresentationEquiv ρ, notesRep_mk _ _, ?_, ?_⟩
  · intro g v
    exact fullEvaluation_mk ρ g v
  · intro v
    rfl

section Trivial

variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (⊥ : Subgroup G) V)

lemma trivial_relations_eq_bot : relations ⊥ ρ = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, h, v⟩, rfl⟩
  have hh : h = 1 := Subsingleton.elim _ _
  simp [hh]

/-- With no nonzero relations, the quotient is the original tensor product. -/
def trivialLinearEquiv : NotesInd ⊥ ρ ≃ₗ[ℂ] TensorProduct ℂ (MonoidAlgebra ℂ G) V :=
  (relations ⊥ ρ).quotEquivOfEqBot (trivial_relations_eq_bot ρ)

@[simp] lemma trivialLinearEquiv_quotient (x : TensorProduct ℂ (MonoidAlgebra ℂ G) V) :
    trivialLinearEquiv ρ ((relations ⊥ ρ).mkQ x) = x :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ x

def trivialRepresentationEquiv :
    (notesRep ⊥ ρ).Equiv (tensorAction (G := G) (V := V)) :=
  Representation.Equiv.mk (trivialLinearEquiv ρ) (by
    intro k
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    change trivialLinearEquiv ρ (notesRep ⊥ ρ k ((relations ⊥ ρ).mkQ x)) =
      tensorAction k (trivialLinearEquiv ρ ((relations ⊥ ρ).mkQ x))
    rw [notesRep_quotient, trivialLinearEquiv_quotient, trivialLinearEquiv_quotient])

end Trivial

theorem trivial_relations : TrivialRelations.{u,v} := by
  intro G _ _ V _ _ ρ
  exact trivial_relations_eq_bot ρ

theorem trivial_subgroup : TrivialSubgroup.{u,v} := by
  intro G _ _ V _ _ ρ
  refine ⟨notesRep ⊥ ρ, trivialRepresentationEquiv ρ, notesRep_mk _ _, ?_, ?_⟩
  · intro g v
    exact trivialLinearEquiv_quotient ρ (MonoidAlgebra.single g 1 ⊗ₜ[ℂ] v)
  · intro x
    rfl

theorem proper_subgroup_dimension_finite : FiniteProperSubgroupDimension.{u,v} := by
  intro G _ _ H V _ _ _ _ ρ hH
  have hd := (dimension G H V ρ).2
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hlt : Module.finrank ℂ V < Module.finrank ℂ (NotesInd H ρ) := by
    rw [hd]
    simpa using Nat.mul_lt_mul_of_pos_right (H.one_lt_index_of_ne_top hH) hpos
  refine ⟨hlt, ?_⟩
  rintro ⟨e⟩
  exact (ne_of_gt hlt) e.finrank_eq

/-- Finite-index induction need not increase infinite dimension. In particular,
for a nontrivial finite group and H = 1, this disproves the unrestricted final
sentence of the source. The countably infinite-dimensional space is nonzero. -/
theorem countable_induction_same_space {G : Type} [Group G] [Finite G]
    (H : Subgroup G) (ρ : Representation ℂ H (ℕ →₀ ℂ)) :
    Nonempty (NotesInd H ρ ≃ₗ[ℂ] (ℕ →₀ ℂ)) := by
  let e := D07.Ch21.InductionCosetModelCosetCoordinateEquivalence.coordinateEquiv
    H ρ Quotient.out QuotientGroup.out_eq'
  apply nonempty_linearEquiv_of_rank_eq
  rw [← e.rank_eq]
  change Module.rank ℂ ((G ⧸ H) →₀ (ℕ →₀ ℂ)) = Module.rank ℂ (ℕ →₀ ℂ)
  simp only [rank_finsupp, Module.rank_self, Cardinal.lift_id, Cardinal.mk_nat, mul_one]
  exact Cardinal.mul_eq_right le_rfl Cardinal.mk_le_aleph0 (Cardinal.mk_ne_zero _)


/-- The dimension obstruction also rules out representation equivalence with
any action on the original finite-dimensional space. -/
theorem finite_representation_obstruction : FiniteRepresentationObstruction.{u,v} := by
  intro G _ _ H V _ _ _ _ ρ hH σ τ he
  obtain ⟨e⟩ := he
  exact (proper_subgroup_dimension_finite G H V ρ hH).2 ⟨e.toLinearEquiv⟩

section Counterexample

open Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence
open D07.Ch21.InductionCosetModelCosetCoordinateEquivalence

/-- The cosets of the identity subgroup are the two group elements. -/
def counterexampleCosetIndex : (CounterexampleGroup ⧸ (⊥ : Subgroup CounterexampleGroup)) ≃ Fin 2 :=
  (QuotientGroup.quotientBot.toEquiv.trans Multiplicative.toAdd).trans
    (ZMod.finEquiv 2).symm.toEquiv

/-- Interleave the two countable bases: (i,n) goes to 2n+i. -/
def counterexampleIndex :
    ((CounterexampleGroup ⧸ (⊥ : Subgroup CounterexampleGroup)) × ℕ) ≃ ℕ :=
  ((Equiv.prodCongr counterexampleCosetIndex (Equiv.refl ℕ)).trans
    (Equiv.prodComm (Fin 2) ℕ)).trans (Nat.divModEquiv 2).symm

lemma counterexampleIndex_mk (i : Fin 2) (n : ℕ) :
    counterexampleIndex (QuotientGroup.mk (Multiplicative.ofAdd (ZMod.finEquiv 2 i)), n) =
      2 * n + i.val := by
  change n * 2 + i.val = 2 * n + i.val
  rw [Nat.mul_comm n 2]

/-- The representative of each identity-subgroup coset is its unique element. -/
def counterexampleRepresentatives :
    CounterexampleGroup ⧸ (⊥ : Subgroup CounterexampleGroup) → CounterexampleGroup :=
  QuotientGroup.quotientBot

lemma counterexampleRepresentatives_transversal :
    IsTransversal (⊥ : Subgroup CounterexampleGroup) counterexampleRepresentatives := by
  intro q
  change QuotientGroup.quotientBot.symm (QuotientGroup.quotientBot q) = q
  exact QuotientGroup.quotientBot.symm_apply_apply q

/-- First use the shared quotient-to-coset coordinates, then uncurry the
finitely supported coefficients and interleave their even/odd indices. -/
def counterexampleLinearEquiv :
    NotesInd ⊥ counterexampleInput ≃ₗ[ℂ] CounterexampleSpace :=
  ((coordinateEquiv ⊥ counterexampleInput counterexampleRepresentatives
    counterexampleRepresentatives_transversal).symm.trans
      (Finsupp.curryLinearEquiv ℂ).symm).trans (Finsupp.domLCongr counterexampleIndex)

lemma counterexampleLinearEquiv_mk (i : Fin 2) (n : ℕ) (c : ℂ) :
    counterexampleLinearEquiv
      (notesMk ⊥ counterexampleInput (Multiplicative.ofAdd (ZMod.finEquiv 2 i))
        (Finsupp.single n c)) = Finsupp.single (2 * n + i.val) c := by
  simp only [counterexampleLinearEquiv, LinearEquiv.trans_apply,
    coordinateEquiv_symm_mk, counterexampleInput, trivial_apply]
  change Finsupp.domLCongr counterexampleIndex
    (Finsupp.uncurry (Finsupp.single _ (Finsupp.single n c))) = _
  rw [Finsupp.uncurry_single, Finsupp.domLCongr_single, counterexampleIndex_mk]

/-- Conjugating the quotient action by the explicit interleaving equivalence
constructs an action on the original countably infinite-dimensional space. -/
def counterexampleAction : Representation ℂ CounterexampleGroup CounterexampleSpace :=
  counterexampleLinearEquiv.conjRingEquiv.toMonoidHom.comp (notesRep ⊥ counterexampleInput)

/-- This identification intertwines the actual quotient action. -/
def counterexampleRepresentationEquiv :
    (notesRep ⊥ counterexampleInput).Equiv counterexampleAction :=
  Representation.Equiv.mk counterexampleLinearEquiv (by
    intro k
    apply LinearMap.ext
    intro x
    change counterexampleLinearEquiv (notesRep ⊥ counterexampleInput k x) =
      counterexampleLinearEquiv (notesRep ⊥ counterexampleInput k
        (counterexampleLinearEquiv.symm (counterexampleLinearEquiv x)))
    rw [LinearEquiv.symm_apply_apply])

/-- Every action restricts to the unique action of the identity subgroup. -/
lemma counterexampleAction_restrict :
    counterexampleAction.comp (⊥ : Subgroup CounterexampleGroup).subtype =
      counterexampleInput := by
  ext h v
  have hh : h = 1 := Subsingleton.elim _ _
  simp [hh, counterexampleInput]

lemma counterexampleSubgroup_proper : (⊥ : Subgroup CounterexampleGroup) ≠ ⊤ :=
  bot_ne_top

/-- The reviewed source boundary, with the prescribed even/odd formula,
equivalent transported representation, and equality of cardinal dimensions. -/
theorem cyclic_two_counterexample : CyclicTwoCounterexample := by
  refine ⟨counterexampleSubgroup_proper, inferInstance,
    notesRep ⊥ counterexampleInput, counterexampleAction,
    counterexampleRepresentationEquiv, notesRep_mk _ _, ?_,
    counterexampleAction_restrict, counterexampleLinearEquiv.rank_eq⟩
  exact counterexampleLinearEquiv_mk

/-- Refutation of the printed unrestricted dimension-growth/same-space claim. -/
theorem unrestricted_obstruction_refuted : UnrestrictedObstructionRefuted := by
  intro h
  exact (h CounterexampleGroup (⊥ : Subgroup CounterexampleGroup) CounterexampleSpace
    counterexampleInput counterexampleSubgroup_proper).2 ⟨counterexampleLinearEquiv⟩

end Counterexample

end
end D07.Ch21.InductionCosetModel
