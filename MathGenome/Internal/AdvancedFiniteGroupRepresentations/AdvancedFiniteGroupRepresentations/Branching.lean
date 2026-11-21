import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.RestrictionFiltration
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtClassification
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Branching
import MathGenome.Internal.AlgebraCore.P103.Ch08.FourierTransform
import MathGenome.Internal.AlgebraCore.P103.Ch08.Maschke
import Mathlib.LinearAlgebra.Projection
import MathGenome.Internal.AlgebraCore.P103.Ch09.FrobeniusCharacters
import Batteries.Tactic.OpenPrivate

noncomputable section
open scoped BigOperators Classical
namespace AdvancedFiniteGroupRepresentations

abbrev branchingSumRepresentation := @Specs.AdvancedFiniteGroupRepresentations.branchingSumRepresentation
abbrev RestrictionBranchingSum := @Specs.AdvancedFiniteGroupRepresentations.RestrictionBranchingSum
abbrev InductionBranchingSum := @Specs.AdvancedFiniteGroupRepresentations.InductionBranchingSum

/-- Erasing two different members of a finite set cannot give the same set. -/
theorem deleted_shapes_distinct {n : ℕ} (p : Partition (n + 1)) :
    Function.Injective (deleteCell p) := by
  intro c d h
  apply Subtype.ext
  by_contra hne
  have he := congrArg cells h
  rw [deleteCell_cells, deleteCell_cells] at he
  have hc : c.val ∈ (cells p).erase d.val :=
    Finset.mem_erase.mpr ⟨hne, c.property.1⟩
  rw [← he] at hc
  exact Finset.notMem_erase _ _ hc

/-- Inserting two different new cells cannot give the same diagram. -/
theorem adjoined_shapes_distinct {m : ℕ} (p : Partition m) :
    Function.Injective (addCell p) := by
  intro c d h
  apply Subtype.ext
  have he := congrArg cells h
  rw [addCell_cells, addCell_cells] at he
  have hc : c.val ∈ insert d.val (cells p) := by rw [← he]; exact Finset.mem_insert_self _ _
  exact (Finset.mem_insert.mp hc).resolve_right c.property.1

@[instance] theorem addableCell_finite {m : ℕ} (p : Partition m) : Finite (AddableCell p) :=
  Finite.of_injective (addCell p) (adjoined_shapes_distinct p)

/-- Character additivity on finite direct sums in the product realization. -/
theorem branchingSum_character {G ι : Type*} [Group G] [Fintype ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (g : G) :
    (branchingSumRepresentation ρ).character g = ∑ i, (ρ i).character g :=
  P103.Ch08.FourierTransform.trace_pi (fun i => ρ i g)

/-- Maschke splits every surjective intertwiner. The kernel and its complement
carry the actual inherited actions, and the complement maps isomorphically
onto the target. -/
theorem split_surjective_intertwiner {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    Nonempty (ρ.Equiv (f.ker.toRepresentation.prod σ)) := by
  let K := f.ker
  obtain ⟨C, hC⟩ := P103.Ch08.Maschke.invariant_complement ρ
    (by exact_mod_cast Nat.card_pos.ne') K
  let fc : C.toSubmodule →ₗ[ℂ] W := f.toLinearMap.comp C.toSubmodule.subtype
  have hfc : Function.Bijective fc := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply le_antisymm
      · intro x hx
        have hxk : x.val ∈ K.toSubmodule := hx
        have hx0 : x.val ∈ (⊥ : Submodule ℂ V) := by
          rw [← hC.inf_eq_bot]
          exact ⟨hxk, x.property⟩
        exact Subtype.ext (show x.val = 0 from hx0)
      · exact bot_le
    · intro w
      obtain ⟨v, hv⟩ := hf w
      obtain ⟨x, hx⟩ := (K.toSubmodule.prodEquivOfIsCompl C.toSubmodule hC).surjective v
      refine ⟨x.2, ?_⟩
      have hfx : f x.1.val = 0 := x.1.property
      change f x.2.val = w
      rw [← hv, ← hx]
      change f x.2.val = f (x.1.val + x.2.val)
      rw [map_add, hfx, zero_add]
  let eC : C.toRepresentation.Equiv σ := Representation.Equiv.mk
    (LinearEquiv.ofBijective fc hfc) (by
      intro g
      apply LinearMap.ext
      intro v
      exact Representation.IntertwiningMap.isIntertwining ρ σ f g v.val)
  let e : (K.toRepresentation.prod C.toRepresentation).Equiv ρ :=
    Representation.Equiv.mk (K.toSubmodule.prodEquivOfIsCompl C.toSubmodule hC) (by
      intro g
      apply LinearMap.ext
      intro v
      exact (map_add (ρ g) v.1.val v.2.val).symm)
  let e' : (K.toRepresentation.prod C.toRepresentation).Equiv
      (K.toRepresentation.prod σ) :=
    Representation.Equiv.mk ((LinearEquiv.refl ℂ K.toSubmodule).prodCongr eC.toLinearEquiv) (by
      intro g
      apply LinearMap.ext
      intro v
      apply Prod.ext
      · rfl
      · exact Representation.IntertwiningMap.isIntertwining _ _ eC.toIntertwiningMap g v.2)
  exact ⟨e.symm.trans e'⟩

/-- Character additivity for an equivariant short exact sequence. -/
theorem character_of_surjective_intertwiner {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (g : G) :
    ρ.character g = f.ker.toRepresentation.character g + σ.character g := by
  obtain ⟨e⟩ := split_surjective_intertwiner ρ σ f hf
  rw [Representation.char_iso e]
  exact LinearMap.trace_prodMap' _ _

/-- The canonical action already constructed on the original Specht subspace. -/
abbrev branchingSpecht {n : ℕ} (p : Partition n) :=
  (spechtSubrepresentation p).toRepresentation

/-- The original fixed-last-label action on each filtration term. -/
abbrev filtrationSubrepresentation {n : ℕ} (p : Partition (n + 1)) (i : ℕ) :
    Subrepresentation ((permutationRepresentation p).comp (symmetricGroupEmbedding n)) where
  toSubmodule := restrictionFiltration p i
  apply_mem_toSubmodule g v hv := restrictionFiltration_invariant p i g v hv

abbrev filtrationRepresentation {n : ℕ} (p : Partition (n + 1)) (i : ℕ) :=
  (filtrationSubrepresentation p i).toRepresentation

/-- Deletion is a surjective intertwiner at the current filtration step. -/
def stepDeletionIntertwiner {n : ℕ} {p : Partition (n + 1)} (c : RemovableCell p) :
    (filtrationRepresentation p (cornerIndex p c + 1)).IntertwiningMap
      (branchingSpecht (deleteCell p c)) where
  toLinearMap := restrictionStepDeletion c
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact tabloidDeletion_equivariant c g v.val

/-- The preceding filtration term is exactly the kernel, with its inherited action. -/
def stepKernelEquiv {n : ℕ} {p : Partition (n + 1)} (c : RemovableCell p) :
    (filtrationRepresentation p (cornerIndex p c)).Equiv
      (stepDeletionIntertwiner c).ker.toRepresentation := by
  let j : restrictionFiltration p (cornerIndex p c) →ₗ[ℂ]
      (stepDeletionIntertwiner c).ker.toSubmodule :=
    { toFun v := ⟨⟨v.val, restrictionFiltration_mono p (by omega) v.property⟩, by
        change restrictionStepDeletion c _ = 0
        apply Subtype.ext
        exact tabloidDeletion_filtration_zero c _ le_rfl v.val v.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hj : Function.Bijective j := by
    constructor
    · intro v w h
      exact Subtype.ext (congrArg (fun x => x.val.val) h)
    · intro v
      have hv : v.val.val ∈ restrictionFiltration p (cornerIndex p c) := by
        have hh : restrictionStepDeletion c v.val = 0 := v.property
        have hh' : v.val ∈ LinearMap.ker (restrictionStepDeletion c) := hh
        rw [restrictionStepDeletion_ker] at hh'
        exact hh' 
      exact ⟨⟨v.val.val, hv⟩, rfl⟩
  exact Representation.Equiv.mk (LinearEquiv.ofBijective j hj) (by intro g; ext v; rfl)

/-- Each successive character difference is the smaller Specht character. -/
theorem filtration_character_step {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (g : SymmetricGroup n) :
    (filtrationRepresentation p (cornerIndex p c + 1)).character g =
      (filtrationRepresentation p (cornerIndex p c)).character g +
      (branchingSpecht (deleteCell p c)).character g := by
  rw [character_of_surjective_intertwiner _ _ (stepDeletionIntertwiner c)
    (restrictionStepDeletion_surjective c), ← Representation.char_iso (stepKernelEquiv c)]

/-- Telescoping the finite filtration counts each corner once. -/
theorem filtration_character {n : ℕ} (p : Partition (n + 1)) (g : SymmetricGroup n)
    (i : ℕ) (hi : i ≤ cornerCount p) :
    letI := Fintype.ofFinite (RemovableCell p)
    (filtrationRepresentation p i).character g =
      ∑ c : RemovableCell p, if cornerIndex p c < i then
        (branchingSpecht (deleteCell p c)).character g else 0 := by
  letI := Fintype.ofFinite (RemovableCell p)
  induction i with
  | zero =>
    haveI : Subsingleton (restrictionFiltration p 0) := by
      rw [restrictionFiltration_zero]
      infer_instance
    have hz : (filtrationRepresentation p 0) g = 0 := Subsingleton.elim _ _
    simp [Representation.character, hz]
  | succ i ih =>
    obtain ⟨c, hc, _⟩ := (cornerIndex_order p).2 ⟨i, by omega⟩
    change cornerIndex p c = i at hc
    rw [show i + 1 = cornerIndex p c + 1 by omega, filtration_character_step,
      show cornerIndex p c = i from hc, ih (by omega)]
    have hs (d : RemovableCell p) :
        (if cornerIndex p d < i + 1 then
          (branchingSpecht (deleteCell p d)).character g else 0) =
        (if cornerIndex p d < i then
          (branchingSpecht (deleteCell p d)).character g else 0) +
        (if d = c then (branchingSpecht (deleteCell p d)).character g else 0) := by
      by_cases hd : d = c
      · subst d
        simp [hc]
      · have hne : cornerIndex p d ≠ i := fun h => hd (cornerIndex_injective p (h.trans hc.symm))
        have hiff : cornerIndex p d < i + 1 ↔ cornerIndex p d < i := by omega
        simp [hd, hiff]
    simp_rw [hs]
    rw [Finset.sum_add_distrib]
    simp

/-- The terminal filtration term is the original restricted Specht module. -/
def filtrationTopEquiv {n : ℕ} (p : Partition (n + 1)) :
    Representation.Equiv (filtrationRepresentation p (cornerCount p))
      ((branchingSpecht p).comp (symmetricGroupEmbedding n)) :=
  Representation.Equiv.mk (LinearEquiv.ofEq _ _ (restrictionFiltration_top p))
    (by intro g; apply LinearMap.ext; intro v; rfl)

/-- The character form of restriction, proved from the actual deletion filtration. -/
theorem restriction_character {n : ℕ} (p : Partition (n + 1)) (g : SymmetricGroup n) :
    letI := Fintype.ofFinite (RemovableCell p)
    (branchingSpecht p).character (extendPermutation g) =
      ∑ c : RemovableCell p, (branchingSpecht (deleteCell p c)).character g := by
  letI := Fintype.ofFinite (RemovableCell p)
  have h := filtration_character p g (cornerCount p) le_rfl
  rw [Representation.char_iso (filtrationTopEquiv p)] at h
  change (branchingSpecht p).character (extendPermutation g) = _ at h
  simpa only [cornerIndex_lt_count, ite_true] using h

/-- An inherited Specht action is uniquely determined by the tabloid action. -/
private theorem inheritedSpechtAction_eq {n : ℕ} {p : Partition n}
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hσ : InheritedSpechtAction p σ) : σ = branchingSpecht p := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  exact Subtype.ext (hσ g v)

/-- FR-B05, restriction. Character classification supplies the actual equivariant
linear equivalence after the character identity is proved. -/
theorem restriction_branching : Specs.AdvancedFiniteGroupRepresentations.restriction_branchingType := by
  intro n p σ hσ τ hτ
  letI := Fintype.ofFinite (RemovableCell p)
  have hs := inheritedSpechtAction_eq σ hσ
  have ht : τ = fun c => branchingSpecht (deleteCell p c) := by
    funext c
    exact inheritedSpechtAction_eq (τ c) (hτ c)
  subst σ τ
  apply (P103.Ch08.RegularMultiplicity.character_classification _ _).mpr
  funext g
  change (branchingSpecht p).character (extendPermutation g) =
    (branchingSumRepresentation (fun c : RemovableCell p => branchingSpecht (deleteCell p c))).character g
  rw [branchingSum_character]
  exact restriction_character p g

/-- Equality of the underlying cell sets determines a partition. -/
theorem partition_eq_of_cells_eq {n : ℕ} {p q : Partition n}
    (h : cells p = cells q) : p = q := by
  apply (diagramEquiv n).injective
  apply Subtype.ext
  apply YoungDiagram.ext
  exact h

/-- Adding and deleting a box are inverse incidence relations on shapes. -/
theorem delete_exists_iff_add_exists {m : ℕ} (p : Partition m) (q : Partition (m + 1)) :
    (∃ c : RemovableCell q, deleteCell q c = p) ↔
      (∃ d : AddableCell p, addCell p d = q) := by
  constructor
  · rintro ⟨c, hc⟩
    let d : AddableCell p := ⟨c.val, hc ▸ deleted_cell_addable q c⟩
    refine ⟨d, partition_eq_of_cells_eq ?_⟩
    rw [addCell_cells]
    change insert c.val (cells p) = cells q
    rw [← hc, deleteCell_cells]
    exact Finset.insert_erase c.property.1
  · rintro ⟨d, hd⟩
    let c : RemovableCell q := ⟨d.val, hd ▸ adjoined_cell_removable p d⟩
    refine ⟨c, partition_eq_of_cells_eq ?_⟩
    rw [deleteCell_cells]
    change (cells q).erase d.val = cells p
    rw [← hd, addCell_cells]
    exact Finset.erase_insert d.property.1

/-- A repetition-free finite family has indicator sum either zero or one. -/
theorem sum_shape_indicator {ι α : Type*} [Fintype ι] [DecidableEq α] (f : ι → α)
    (hf : Function.Injective f) (a : α) :
    (∑ i, if f i = a then (1 : ℂ) else 0) = if ∃ i, f i = a then 1 else 0 := by
  by_cases h : ∃ i, f i = a
  · obtain ⟨j, hj⟩ := h
    rw [if_pos ⟨j, hj⟩]
    have he (i : ι) : f i = a ↔ i = j := by rw [← hj, hf.eq_iff]
    simp [he]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg (fun hi => h ⟨i, hi⟩)

/-- The embedding is an isomorphism onto exactly the subgroup fixing the last label. -/
def lastLabelEquiv (m : ℕ) : SymmetricGroup m ≃* lastLabelSubgroup m :=
  MulEquiv.ofBijective
    ((symmetricGroupEmbedding m).codRestrict (lastLabelSubgroup m)
      (fun g => extendPermutation_last g))
    ⟨by intro g h he; exact extendPermutation_injective m (congrArg Subtype.val he),
      by
        intro h
        obtain ⟨g, hg⟩ := (lastLabelSubgroup_eq_range h.val).mp h.property
        exact ⟨g, Subtype.ext hg⟩⟩

@[simp] theorem lastLabelEquiv_apply {m : ℕ} (g : SymmetricGroup m) :
    (lastLabelEquiv m g).val = extendPermutation g := rfl

open private classCharacter classCharacter_mk characterPair spechtCharacterBasis
  spechtCharacterBasis_apply specht_character_pair from
  MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtClassification

/-- Pairing against the complete Specht character basis detects equality.
Completeness here is the independently proved classification, not an assumption
that the induction formula holds. -/
theorem character_eq_of_specht_pairings {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (SymmetricGroup n) V)
    (σ : Representation ℂ (SymmetricGroup n) W)
    (h : ∀ p : Partition n,
      characterPair (branchingSpecht p) (classCharacter ρ) =
        characterPair (branchingSpecht p) (classCharacter σ)) :
    ρ.character = σ.character := by
  have coord (f : ConjClasses (SymmetricGroup n) → ℂ) (p : Partition n) :
      characterPair (branchingSpecht p) f = (spechtCharacterBasis n).repr f p := by
    have hh := congrArg (characterPair (branchingSpecht p)) ((spechtCharacterBasis n).sum_repr f)
    simpa only [map_sum, map_smul, spechtCharacterBasis_apply, specht_character_pair,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using hh.symm
  have he : classCharacter ρ = classCharacter σ := by
    apply (spechtCharacterBasis n).repr.injective
    ext p
    rw [← coord, ← coord]
    exact h p
  funext g
  exact congrFun he (ConjClasses.mk g)

/-- The first-linear character pairing, expressed in the inverse convention
used for the Specht character basis. -/
theorem characterPair_eq_functionPairing {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (SymmetricGroup n) V)
    (σ : Representation ℂ (SymmetricGroup n) W) :
    characterPair σ (classCharacter ρ) =
      P103.Ch08.UnitaritySpecs.functionPairingValue ρ.character σ.character := by
  unfold characterPair P103.Ch08.UnitaritySpecs.functionPairingValue
  simp only [LinearMap.coe_mk, AddHom.coe_mk, classCharacter_mk, Nat.card_eq_fintype_card]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (ρ.character g * ·) (P103.Ch08.character_inverse_conjugate σ g)

private theorem functionPairing_sum_right {G ι : Type*} [Fintype G] [Fintype ι]
    (f : G → ℂ) (h : ι → G → ℂ) :
    P103.Ch08.UnitaritySpecs.functionPairingValue f (∑ i, h i) =
      ∑ i, P103.Ch08.UnitaritySpecs.functionPairingValue f (h i) := by
  unfold P103.Ch08.UnitaritySpecs.functionPairingValue
  simp only [Finset.sum_apply, star_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem functionPairing_equiv {G H : Type*} [Fintype G] [Fintype H]
    (e : G ≃ H) (f : G → ℂ) (h : H → ℂ) :
    P103.Ch08.UnitaritySpecs.functionPairingValue (fun a => f (e.symm a)) h =
      P103.Ch08.UnitaritySpecs.functionPairingValue f (fun g => h (e g)) := by
  unfold P103.Ch08.UnitaritySpecs.functionPairingValue
  rw [Fintype.card_congr e]
  congr 1
  symm
  exact Fintype.sum_equiv e _ _ (by intro g; simp)

private theorem specht_functionPairing {n : ℕ} (p q : Partition n) :
    P103.Ch08.UnitaritySpecs.functionPairingValue
      (branchingSpecht p).character (branchingSpecht q).character =
      if p = q then 1 else 0 := by
  rw [← characterPair_eq_functionPairing]
  exact specht_character_pair p q

/-- Frobenius reciprocity and restriction compute the actual induced character's
coefficient at every Specht type. -/
theorem induced_specht_pairing {m : ℕ} (p : Partition m) (q : Partition (m + 1)) :
    letI := P103.Ch09.rightSubgroupModule (k := ℂ) (lastLabelSubgroup m)
    let ρ := (branchingSpecht p).comp (lastLabelEquiv m).symm.toMonoidHom
    letI := P103.Ch09.inducedAlgebraModule (lastLabelSubgroup m) ρ
    letI := P103.Ch09.inducedScalarModule (lastLabelSubgroup m) ρ
    letI := Fintype.ofFinite (RemovableCell q)
    characterPair (branchingSpecht q)
      (classCharacter (P103.Ch09.induction (lastLabelSubgroup m) ρ)) =
      ∑ c : RemovableCell q, if deleteCell q c = p then 1 else 0 := by
  letI := P103.Ch09.rightSubgroupModule (k := ℂ) (lastLabelSubgroup m)
  let ρ : Representation ℂ (lastLabelSubgroup m) (SpechtModule p) :=
    (branchingSpecht p).comp (lastLabelEquiv m).symm.toMonoidHom
  letI := P103.Ch09.inducedAlgebraModule (lastLabelSubgroup m) ρ
  letI := P103.Ch09.inducedScalarModule (lastLabelSubgroup m) ρ
  letI := Fintype.ofFinite (RemovableCell q)
  change characterPair (branchingSpecht q)
    (classCharacter (P103.Ch09.induction (lastLabelSubgroup m) ρ)) = _
  rw [characterPair_eq_functionPairing]
  have hrec := (P103.Ch09.FrobeniusCharacters.character_reciprocity
    (lastLabelSubgroup m) ρ (branchingSpecht q)
    (P103.Ch09.inductionData _ _) (P103.Ch09.functionModelData _ _)).2
  change P103.Ch08.UnitaritySpecs.functionPairingValue
      (P103.Ch09.induction (lastLabelSubgroup m) ρ).character (branchingSpecht q).character =
    P103.Ch08.UnitaritySpecs.functionPairingValue ρ.character
      (fun h : lastLabelSubgroup m => (branchingSpecht q).character h.val) at hrec
  rw [hrec]
  change P103.Ch08.UnitaritySpecs.functionPairingValue
    (fun h : lastLabelSubgroup m => (branchingSpecht p).character ((lastLabelEquiv m).symm h))
    (fun h : lastLabelSubgroup m => (branchingSpecht q).character h.val) = _
  trans P103.Ch08.UnitaritySpecs.functionPairingValue (branchingSpecht p).character
    (fun g : SymmetricGroup m => (branchingSpecht q).character (lastLabelEquiv m g).val)
  · exact functionPairing_equiv (lastLabelEquiv m).toEquiv _ _
  have hr : (fun g : SymmetricGroup m =>
      (branchingSpecht q).character (lastLabelEquiv m g).val) =
      ∑ c : RemovableCell q, (branchingSpecht (deleteCell q c)).character := by
    funext g
    simpa only [lastLabelEquiv_apply, Finset.sum_apply] using restriction_character q g
  rw [hr, functionPairing_sum_right]
  simp_rw [specht_functionPairing]
  apply Finset.sum_congr rfl
  intro c _
  simp only [eq_comm]

/-- The class function of a finite direct sum is the sum of its class functions. -/
private theorem branchingSum_classCharacter {n : ℕ} {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (SymmetricGroup n) (V i)) :
    classCharacter (branchingSumRepresentation ρ) = ∑ i, classCharacter (ρ i) := by
  funext a
  induction a using Quotient.inductionOn with
  | _ g =>
    change (branchingSumRepresentation ρ).character g =
      (∑ i, classCharacter (ρ i)) (ConjClasses.mk g)
    simp only [Finset.sum_apply, classCharacter_mk]
    exact branchingSum_character ρ g

/-- The proposed induction sum has a single copy of each addable shape. -/
theorem adjoined_sum_pairing {m : ℕ} (p : Partition m) (q : Partition (m + 1)) :
    letI := Fintype.ofFinite (AddableCell p)
    characterPair (branchingSpecht q)
      (classCharacter (branchingSumRepresentation (fun d : AddableCell p =>
        branchingSpecht (addCell p d)))) =
      ∑ d : AddableCell p, if addCell p d = q then 1 else 0 := by
  letI := Fintype.ofFinite (AddableCell p)
  rw [branchingSum_classCharacter, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  exact specht_character_pair (addCell p d) q

/-- FR-B05, induction in the canonical balanced left tensor model. -/
theorem induction_branching : Specs.AdvancedFiniteGroupRepresentations.induction_branchingType := by
  intro m p σ hσ τ hτ
  have hs := inheritedSpechtAction_eq σ hσ
  have ht : τ = fun d => branchingSpecht (addCell p d) := by
    funext d
    exact inheritedSpechtAction_eq (τ d) (hτ d)
  subst σ τ
  refine ⟨lastLabelEquiv m, fun _ => rfl, ?_⟩
  letI := P103.Ch09.rightSubgroupModule (k := ℂ) (lastLabelSubgroup m)
  let ρ : Representation ℂ (lastLabelSubgroup m) (SpechtModule p) :=
    (branchingSpecht p).comp (lastLabelEquiv m).symm.toMonoidHom
  letI := P103.Ch09.inducedAlgebraModule (lastLabelSubgroup m) ρ
  letI := P103.Ch09.inducedScalarModule (lastLabelSubgroup m) ρ
  letI := P103.Ch09.TensorCoordinates.induced_finiteDimensional (lastLabelSubgroup m) ρ
  letI := Fintype.ofFinite (AddableCell p)
  change Nonempty (Representation.Equiv (P103.Ch09.induction (lastLabelSubgroup m) ρ)
    (branchingSumRepresentation (fun d : AddableCell p => branchingSpecht (addCell p d))))
  apply (P103.Ch08.RegularMultiplicity.character_classification _ _).mpr
  apply character_eq_of_specht_pairings
  intro q
  letI := Fintype.ofFinite (RemovableCell q)
  calc
    _ = ∑ c : RemovableCell q, if deleteCell q c = p then 1 else 0 :=
      induced_specht_pairing p q
    _ = if ∃ c : RemovableCell q, deleteCell q c = p then 1 else 0 :=
      by simpa only using sum_shape_indicator _ (deleted_shapes_distinct q) p
    _ = if ∃ d : AddableCell p, addCell p d = q then 1 else 0 := by
      simp only [delete_exists_iff_add_exists]
    _ = ∑ d : AddableCell p, if addCell p d = q then 1 else 0 :=
      by simpa only using (sum_shape_indicator _ (adjoined_shapes_distinct p) q).symm
    _ = _ := (adjoined_sum_pairing p q).symm

end AdvancedFiniteGroupRepresentations
