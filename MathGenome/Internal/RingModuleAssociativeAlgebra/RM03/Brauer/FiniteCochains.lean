import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.FiniteCochains

/-! Finite-stage reduction for continuous scalar cochains on an absolute Galois group. -/

namespace RM03.Brauer

open Topology

universe w

variable {k S : Type*} [Field k] [Field S] [Algebra k S]

local instance : TopologicalSpace Sˣ := ⊥
local instance : DiscreteTopology Sˣ := ⟨rfl⟩

private noncomputable abbrev restrictTuple {r : ℕ} (E : FiniteGaloisIntermediateField k S)
    (g : Fin r → Gal(S/k)) : Fin r → Gal(E/k) :=
  fun j => AlgEquiv.restrictNormalHom E.toIntermediateField (g j)

private theorem restrictTuple_eq_of_le {r : ℕ} {E F : FiniteGaloisIntermediateField k S}
    (hEF : E ≤ F) {g h : Fin r → Gal(S/k)}
    (heq : restrictTuple F g = restrictTuple F h) :
    restrictTuple E g = restrictTuple E h := by
  funext j
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  let xF : F := ⟨x, hEF x.property⟩
  simpa only [restrictTuple, AlgEquiv.restrictNormalHom_apply] using
    congrArg (fun σ : Gal(F/k) => (σ xF : S)) (congrFun heq j)

variable [IsSepClosure k S]

/-- Normal restriction to every finite Galois stage is a quotient map. -/
theorem restrictionQuotient (E : FiniteGaloisIntermediateField k S) :
    IsQuotientMap (AlgEquiv.restrictNormalHom E.toIntermediateField : Gal(S/k) →* Gal(E/k)) :=
  IsOpenMap.isQuotientMap (fun _ _ => isOpen_discrete _)
    (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)
    (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := E.toIntermediateField) S)

/-- The range of a continuous scalar cochain is finite. -/
theorem finiteCochainRange (r : ℕ) (f : (Fin r → Gal(S/k)) → Sˣ) (hf : Continuous f) :
    (Set.range f).Finite :=
  (isCompact_range hf).finite_of_discrete

private theorem exists_stage_constant_on_fibers {r : ℕ} (f : (Fin r → Gal(S/k)) → Sˣ)
    (hf : Continuous f) :
    ∃ E : FiniteGaloisIntermediateField k S,
      ∀ g h, restrictTuple E g = restrictTuple E h → f g = f h := by
  -- Cover the compact set of pairs with distinct values by finite-stage separation sets.
  let D := Fin r → Gal(S/k)
  let bad : Set (D × D) := {p | f p.1 ≠ f p.2}
  let separated (E : FiniteGaloisIntermediateField k S) : Set (D × D) :=
    {p | restrictTuple E p.1 ≠ restrictTuple E p.2}
  have hcompact : IsCompact bad := by
    have hclosed : IsClosed {p : Sˣ × Sˣ | p.1 ≠ p.2} := isClosed_discrete _
    exact (hclosed.preimage ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd))).isCompact
  have hopen (E : FiniteGaloisIntermediateField k S) : IsOpen (separated E) := by
    have hc : Continuous (restrictTuple (r := r) E) :=
      continuous_pi fun j =>
        (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField).comp (continuous_apply j)
    exact isOpen_ne_fun (hc.comp continuous_fst) (hc.comp continuous_snd)
  have hcover : bad ⊆ ⋃ E, separated E := by
    intro p hp
    have hne : p.1 ≠ p.2 := fun h => hp (congrArg f h)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    obtain ⟨x, hx⟩ := DFunLike.exists_ne hj
    let E := FiniteGaloisIntermediateField.adjoin k ({x} : Set S)
    have hxE : x ∈ E.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin k {x} (Set.mem_singleton x)
    refine Set.mem_iUnion.mpr ⟨E, fun heq => hx ?_⟩
    simpa only [restrictTuple, AlgEquiv.restrictNormalHom_apply] using
      congrArg (fun σ : Gal(E/k) => (σ ⟨x, hxE⟩ : S)) (congrFun heq j)
  have hmono : Monotone separated := fun _ _ hEF _ hp hEq =>
    hp (restrictTuple_eq_of_le hEF hEq)
  obtain ⟨E, hE⟩ := hcompact.elim_directed_cover separated hopen hcover
    (fun E F => ⟨E ⊔ F, hmono le_sup_left, hmono le_sup_right⟩)
  refine ⟨E, ?_⟩
  intro g h heq
  by_contra hne
  have hp : (g, h) ∈ bad := hne
  have hs : (g, h) ∈ separated E := hE hp
  exact hs heq

private theorem exists_cochain_stage {r : ℕ} (f : (Fin r → Gal(S/k)) → Sˣ) (hf : Continuous f) :
    ∃ E : FiniteGaloisIntermediateField k S,
      (∀ g h, restrictTuple E g = restrictTuple E h → f g = f h) ∧
      (∀ g, (f g : S) ∈ E.toIntermediateField) := by
  obtain ⟨E, hE⟩ := exists_stage_constant_on_fibers f hf
  let values : Set S := (fun u : Sˣ => (u : S)) '' Set.range f
  have hfinite : values.Finite := (finiteCochainRange r f hf).image _
  let : Finite values := hfinite
  let F := FiniteGaloisIntermediateField.adjoin k values
  refine ⟨E ⊔ F, fun g h heq => hE g h (restrictTuple_eq_of_le le_sup_left heq), fun g => ?_⟩
  have hg : (f g : S) ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin k values ⟨f g, Set.mem_range_self g, rfl⟩
  exact (show F ≤ E ⊔ F from le_sup_right) hg

/-- A finite family, potentially of different arities, factors through one stage above a
prescribed finite Galois intermediate field. -/
theorem commonCochainFactorization (ι : Type w) [Finite ι] (r : ι → ℕ)
    (f : ∀ i, (Fin (r i) → Gal(S/k)) → Sˣ) (hf : ∀ i, Continuous (f i))
    (E₀ : FiniteGaloisIntermediateField k S) :
    ∃ E : FiniteGaloisIntermediateField k S, E₀ ≤ E ∧
      ∃ fE : ∀ i, (Fin (r i) → Gal(E/k)) → Eˣ,
        ∀ i g, Units.map E.toIntermediateField.val.toMonoidHom
          (fE i (fun j => AlgEquiv.restrictNormalHom E.toIntermediateField (g j))) = f i g := by
  classical
  let := Fintype.ofFinite ι
  choose stage hconstant hvalues using fun i => exists_cochain_stage (f i) (hf i)
  let E := E₀ ⊔ Finset.univ.sup stage
  have hstage (i : ι) : stage i ≤ E :=
    (Finset.le_sup (f := stage) (Finset.mem_univ i)).trans le_sup_right
  -- Lift each coordinate using surjectivity. Constancy on fibers gives the desired equality.
  let lift : Gal(E/k) → Gal(S/k) := (restrictionQuotient E).surjective.hasRightInverse.choose
  have hlift (σ : Gal(E/k)) : AlgEquiv.restrictNormalHom E.toIntermediateField (lift σ) = σ :=
    (restrictionQuotient E).surjective.hasRightInverse.choose_spec σ
  refine ⟨E, le_sup_left, fun i t => Units.mk0
      ⟨f i (fun j => lift (t j)), hstage i (hvalues i _)⟩ ?_, ?_⟩
  · intro heq
    exact (f i (fun j => lift (t j))).ne_zero (congrArg Subtype.val heq)
  · intro i g
    apply Units.ext
    change (f i (fun j => lift (restrictTuple E g j)) : S) = (f i g : S)
    apply congrArg Units.val
    apply hconstant i
    apply restrictTuple_eq_of_le (hstage i)
    exact funext fun j => hlift (restrictTuple E g j)

/-- A continuous cochain descends along group restriction and coefficient inclusion. -/
theorem finiteCochainFactorization (r : ℕ) (f : (Fin r → Gal(S/k)) → Sˣ) (hf : Continuous f) :
    ∃ (E : FiniteGaloisIntermediateField k S) (fE : (Fin r → Gal(E/k)) → Eˣ),
      ∀ g, Units.map E.toIntermediateField.val.toMonoidHom
        (fE (fun j => AlgEquiv.restrictNormalHom E.toIntermediateField (g j))) = f g := by
  obtain ⟨E, _, fE, hE⟩ :=
    commonCochainFactorization Unit (fun _ => r) (fun _ => f) (fun _ => hf) ⊥
  exact ⟨E, fE (), hE ()⟩

/-- A unit stabilizer contains the open subgroup fixing a finite Galois field containing the unit. -/
theorem openUnitStabilizers (u : Sˣ) :
    (∃ E : FiniteGaloisIntermediateField k S,
      (u : S) ∈ E.toIntermediateField ∧
        E.toIntermediateField.fixingSubgroup ≤ MulAction.stabilizer Gal(S/k) u) ∧
    IsOpen (MulAction.stabilizer Gal(S/k) u : Set Gal(S/k)) := by
  let E := FiniteGaloisIntermediateField.adjoin k ({(u : S)} : Set S)
  have hu : (u : S) ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin k _ (Set.mem_singleton _)
  have hle : E.toIntermediateField.fixingSubgroup ≤ MulAction.stabilizer Gal(S/k) u := by
    intro σ hσ
    apply Units.ext
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ u hu
  exact ⟨⟨E, hu, hle⟩, Subgroup.isOpen_mono hle E.toIntermediateField.fixingSubgroup_isOpen⟩

/-- The natural action on the discrete unit group is jointly continuous. -/
theorem continuousUnitAction : ContinuousSMul Gal(S/k) Sˣ :=
  continuousSMul_iff_stabilizer_isOpen.mpr (fun u => (openUnitStabilizers (k := k) u).2)

end RM03.Brauer
