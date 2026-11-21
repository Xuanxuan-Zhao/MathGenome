import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtClassification
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.TensorActions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorEvaluation
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.Dimension.Constructions
import Batteries.Tactic.OpenPrivate

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct DirectSum BigOperators MonoidAlgebra
universe u
namespace AdvancedFiniteGroupRepresentations

abbrev tensorMultiplicitySpace := @Specs.AdvancedFiniteGroupRepresentations.tensorMultiplicitySpace
abbrev TensorMultiplicity := @Specs.AdvancedFiniteGroupRepresentations.TensorMultiplicity
abbrev TensorEvaluationSum := @Specs.AdvancedFiniteGroupRepresentations.TensorEvaluationSum
abbrev tensorMultiplicityOperator := @Specs.AdvancedFiniteGroupRepresentations.tensorMultiplicityOperator
abbrev tensorEvaluationSummand := @Specs.AdvancedFiniteGroupRepresentations.tensorEvaluationSummand
abbrev tensorEvaluationMap := @Specs.AdvancedFiniteGroupRepresentations.tensorEvaluationMap
abbrev tensorEvaluationOperator := @Specs.AdvancedFiniteGroupRepresentations.tensorEvaluationOperator

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

@[simp] theorem tensorMultiplicityOperator_apply {n : ℕ} (p : Partition n)
    (g : LinearGroup V) (f : TensorMultiplicity V p) (v : SpechtModule p) :
    (tensorMultiplicityOperator V p g f).val v = diagonalOperator V n g (f.val v) := rfl

@[simp] theorem tensorMultiplicityOperator_one {n : ℕ} (p : Partition n) :
    tensorMultiplicityOperator V p 1 = 1 := by
  ext f v
  change diagonalOperator V n 1 (f.val v) = f.val v
  rw [diagonal_one]
  rfl

theorem tensorMultiplicityOperator_mul {n : ℕ} (p : Partition n) (g h : LinearGroup V) :
    tensorMultiplicityOperator V p (g * h) =
      tensorMultiplicityOperator V p g * tensorMultiplicityOperator V p h := by
  ext f v
  change diagonalOperator V n (g * h) (f.val v) =
    diagonalOperator V n g (diagonalOperator V n h (f.val v))
  rw [diagonal_mul]
  rfl

/-- The general linear group representation on the actual equivariant Hom space. -/
def tensorMultiplicityRepresentation {n : ℕ} (p : Partition n) :
    Representation ℂ (LinearGroup V) (TensorMultiplicity V p) where
  toFun := tensorMultiplicityOperator V p
  map_one' := tensorMultiplicityOperator_one V p
  map_mul' := tensorMultiplicityOperator_mul V p

@[simp] theorem tensorEvaluationMap_pure {n : ℕ} (p : Partition n)
    (v : SpechtModule p) (f : TensorMultiplicity V p) :
    tensorEvaluationMap V n (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f)) = f.val v := by
  change DirectSum.toModule ℂ _ _ _ _ = _
  rw [DirectSum.toModule_lof]
  rfl

/-- A single canonical restricted action, on the original Specht space. -/
def canonicalSpechtRepresentation {n : ℕ} (p : Partition n) :
    Representation ℂ (SymmetricGroup n) (SpechtModule p) :=
  (spechtSubrepresentation p).toRepresentation

instance canonicalSpechtRepresentation_irreducible {n : ℕ} (p : Partition n) :
    (canonicalSpechtRepresentation p).IsIrreducible :=
  classification_irreducible p _ (fun _ _ => rfl)

/-- The inclusion-based definition of equivariance is the usual intertwining space. -/
def tensorMultiplicityEquivIntertwining {n : ℕ} (p : Partition n) :
    TensorMultiplicity V p ≃ₗ[ℂ]
      Representation.IntertwiningMap (canonicalSpechtRepresentation p) (slotRepresentation V n) where
  toFun f := f.val.intertwiningMap_of_isIntertwiningMap _ _
    (fun g v => f.property g v _ rfl)
  invFun f := ⟨f.toLinearMap, by
    intro g v w hw
    have he : w = canonicalSpechtRepresentation p g v := Subtype.ext hw
    subst w
    exact Representation.IntertwiningMap.isIntertwining _ _ f g v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open private classCharacter classCharacter_mk characterPair spechtCharacterBasis
  spechtCharacterBasis_apply specht_character_pair canonicalSpecht from
  MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtClassification

/-- Completeness of Specht characters determines all multiplicity dimensions.
This also applies when the target representation is zero. -/
theorem specht_multiplicity_dimension {n : ℕ} (X : Type u) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (ρ : Representation ℂ (SymmetricGroup n) X) :
    (∑ p : Partition n, Module.finrank ℂ (SpechtModule p) *
      Module.finrank ℂ (Representation.IntertwiningMap (canonicalSpechtRepresentation p) ρ)) =
      Module.finrank ℂ X := by
  classical
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have hc (p : Partition n) :
      (spechtCharacterBasis n).repr (classCharacter ρ) p =
        (Module.finrank ℂ (Representation.IntertwiningMap (canonicalSpechtRepresentation p) ρ) : ℂ) := by
    have h := congrArg (characterPair (canonicalSpecht p))
      ((spechtCharacterBasis n).sum_repr (classCharacter ρ))
    simp only [map_sum, map_smul, spechtCharacterBasis_apply,
      specht_character_pair,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at h
    rw [h]
    exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank _ _
  have h := congrFun ((spechtCharacterBasis n).sum_repr (classCharacter ρ)) (ConjClasses.mk 1)
  simp only [Finset.sum_apply, Pi.smul_apply, spechtCharacterBasis_apply,
    classCharacter_mk, Representation.char_one, smul_eq_mul, hc] at h
  change (∑ p : Partition n,
    (Module.finrank ℂ (Representation.IntertwiningMap (canonicalSpechtRepresentation p) ρ) : ℂ) *
    (Module.finrank ℂ (SpechtModule p) : ℂ)) = (Module.finrank ℂ X : ℂ) at h
  have he : ((∑ p : Partition n, Module.finrank ℂ (SpechtModule p) *
      Module.finrank ℂ (Representation.IntertwiningMap (canonicalSpechtRepresentation p) ρ)) : ℂ) =
        (Module.finrank ℂ X : ℂ) := by
    simpa only [Nat.cast_sum, Nat.cast_mul, mul_comm] using h
  exact_mod_cast he

/-- Every simple submodule is the image of a map from one Specht module. -/
theorem specht_images_span {n : ℕ} (X : Type u) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (ρ : Representation ℂ (SymmetricGroup n) X)
    (W : Submodule ℂ X)
    (hW : ∀ (p : Partition n)
      (f : Representation.IntertwiningMap (canonicalSpechtRepresentation p) ρ)
      (v : SpechtModule p), f v ∈ W) : W = ⊤ := by
  classical
  let : NeZero (Nat.card (SymmetricGroup n) : ℂ) :=
    ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  have htop := IsSemisimpleModule.sSup_simples_eq_top (GroupAlgebra n) ρ.asModule
  have hle : sSup (Submodule.restrictScalars ℂ ''
      {m : Submodule (GroupAlgebra n) ρ.asModule | IsSimpleModule (GroupAlgebra n) m}) ≤
      W.comap ρ.asModuleEquiv.toLinearMap := by
    apply sSup_le
    rintro _ ⟨m, hm, rfl⟩
    let : IsSimpleModule (GroupAlgebra n) m := hm
    let τ := Representation.ofModule (k := ℂ) (G := SymmetricGroup n) m
    have hτ : τ.IsIrreducible :=
      (Representation.isSimpleModule_iff_irreducible_ofModule m).mp hm
    let inc : Representation.IntertwiningMap τ ρ :=
      { toLinearMap :=
          { toFun := fun x => ρ.asModuleEquiv (RestrictScalars.addEquiv ℂ (GroupAlgebra n) m x).val
            map_add' := by intros; rfl
            map_smul' := by
              intro a x
              change ρ.asModuleEquiv (algebraMap ℂ (GroupAlgebra n) a • _) = _
              simp
              rfl }
        isIntertwining' := by
          intro g
          ext x
          change ρ.asModuleEquiv ((MonoidAlgebra.single g (1 : ℂ)) •
            (RestrictScalars.addEquiv ℂ (GroupAlgebra n) m x).val) = _
          simp
          rfl }
    have : FiniteDimensional ℂ (RestrictScalars ℂ (GroupAlgebra n) m) := by
      exact Module.Finite.of_injective inc.toLinearMap (by
        intro x y h
        apply (RestrictScalars.addEquiv ℂ (GroupAlgebra n) m).injective
        apply Subtype.ext
        exact ρ.asModuleEquiv.injective h)
    obtain ⟨p, ⟨σ, hσ, ⟨e⟩⟩, _⟩ := classification_exhaustive _ τ hτ
    have heq : σ = canonicalSpechtRepresentation p := by
      apply MonoidHom.ext
      intro g
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact hσ g v
    subst σ
    intro x hx
    obtain ⟨v, hv⟩ := e.surjective ((RestrictScalars.addEquiv ℂ (GroupAlgebra n) m).symm ⟨x, hx⟩)
    have hv' : e v = (RestrictScalars.addEquiv ℂ (GroupAlgebra n) m).symm ⟨x, hx⟩ := hv
    have h := hW p (inc.comp e.toIntertwiningMap) v
    change inc (e v) ∈ W at h
    rw [hv'] at h
    exact h
  rw [← Submodule.restrictScalars_sSup, htop, Submodule.restrictScalars_top] at hle
  apply top_unique
  intro x _
  obtain ⟨v, rfl⟩ := ρ.asModuleEquiv.surjective x
  exact hle (by trivial)

/-- Surjectivity follows from Maschke and the completeness of the Specht family. -/
theorem tensorEvaluationMap_surjective [FiniteDimensional ℂ V] (n : ℕ) :
    Function.Surjective (tensorEvaluationMap V n) := by
  apply LinearMap.range_eq_top.mp
  apply specht_images_span (TensorPower V n) (slotRepresentation V n)
  intro p f v
  let F := (tensorMultiplicityEquivIntertwining V p).symm f
  refine ⟨DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] F), ?_⟩
  rw [tensorEvaluationMap_pure]
  rfl

/-- Evaluation has the correct dimension without removing zero multiplicity spaces. -/
theorem tensorEvaluationSum_finrank [FiniteDimensional ℂ V] (n : ℕ) :
    Module.finrank ℂ (TensorEvaluationSum V n) = Module.finrank ℂ (TensorPower V n) := by
  have (p : Partition n) : Module.Free ℂ (TensorMultiplicity V p) :=
    Module.Free.of_divisionRing ℂ (TensorMultiplicity V p)
  have (p : Partition n) : Module.Free ℂ (SpechtModule p ⊗[ℂ] TensorMultiplicity V p) :=
    Module.Free.of_divisionRing ℂ (SpechtModule p ⊗[ℂ] TensorMultiplicity V p)
  have (p : Partition n) : FiniteDimensional ℂ (SpechtModule p ⊗[ℂ] TensorMultiplicity V p) := inferInstance
  rw [Module.finrank_directSum]
  simp only [Module.finrank_tensorProduct]
  simp_rw [(tensorMultiplicityEquivIntertwining V _).finrank_eq]
  exact specht_multiplicity_dimension _ (slotRepresentation V n)

theorem tensorEvaluationMap_bijective [FiniteDimensional ℂ V] (n : ℕ) :
    Function.Bijective (tensorEvaluationMap V n) := by
  have hs := tensorEvaluationMap_surjective V n
  have hd := LinearMap.finrank_range_add_finrank_ker
    (K := ℂ) (V := TensorEvaluationSum V n) (V₂ := TensorPower V n) (tensorEvaluationMap V n)
  rw [LinearMap.range_eq_top.mpr hs, finrank_top,
    tensorEvaluationSum_finrank V n] at hd
  have hz : Module.finrank ℂ (LinearMap.ker (tensorEvaluationMap V n)) = 0 :=
    Nat.add_left_cancel (hd.trans (Nat.add_zero _).symm)
  exact ⟨LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz), hs⟩

/-- The canonical isomorphism whose forward map is evaluation. -/
def tensorEvaluationEquiv [FiniteDimensional ℂ V] (n : ℕ) :
    TensorEvaluationSum V n ≃ₗ[ℂ] TensorPower V n :=
  LinearEquiv.ofBijective (tensorEvaluationMap V n) (tensorEvaluationMap_bijective V n)

@[simp] theorem tensorEvaluationEquiv_pure [FiniteDimensional ℂ V] {n : ℕ}
    (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p) :
    tensorEvaluationEquiv V n (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f)) = f.val v :=
  tensorEvaluationMap_pure V p v f

theorem tensorEvaluation_equivariant {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hσ : ∀ p, InheritedSpechtAction p (σ p))
    (s : SymmetricGroup n) (g : LinearGroup V) (x : TensorEvaluationSum V n) :
    tensorEvaluationMap V n (tensorEvaluationOperator V σ s g x) =
      slotOperator V n s (diagonalOperator V n g (tensorEvaluationMap V n x)) := by
  suffices h : (tensorEvaluationMap V n).comp (tensorEvaluationOperator V σ s g) =
      (slotOperator V n s).comp ((diagonalOperator V n g).comp (tensorEvaluationMap V n)) from
    DFunLike.congr_fun h x
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext
  ext v f
  change tensorEvaluationMap V n
      (tensorEvaluationOperator V σ s g (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f))) = _
  rw [tensorEvaluationOperator, Specs.AdvancedFiniteGroupRepresentations.tensorEvaluationOperator,
    DirectSum.lmap_lof, TensorProduct.map_tmul, tensorEvaluationMap_pure]
  change diagonalOperator V n g (f.val (σ p s v)) =
    slotOperator V n s (diagonalOperator V n g
      (tensorEvaluationMap V n (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f))))
  rw [tensorEvaluationMap_pure]
  rw [f.property s v (σ p s v) (hσ p s v)]
  exact (congrArg (fun k : Module.End ℂ (TensorPower V n) => k (f.val v))
    (tensor_actions_commute V n s g).eq).symm

theorem tensorMultiplicity_zero_dimension [FiniteDimensional ℂ V] (n : ℕ)
    (hn : 0 < n) (hd : Module.finrank ℂ V = 0) (p : Partition n) :
    Subsingleton (TensorMultiplicity V p) := by
  let := tensorPower_zero_dimension V n hn hd
  infer_instance

/-- The empty-shape multiplicity is a trivial complex line for every V,
including the zero vector space. -/
theorem tensorMultiplicity_empty_line :
    ∃ e : TensorMultiplicity V emptyPartition ≃ₗ[ℂ] ℂ,
      ∀ (g : LinearGroup V) (f : TensorMultiplicity V emptyPartition),
        e (tensorMultiplicityOperator V emptyPartition g f) = e f := by
  obtain ⟨a, ha⟩ := classification_empty (canonicalSpechtRepresentation emptyPartition)
    (fun _ _ => rfl)
  let b := tensorPowerZeroEquiv V
  let v₀ := a.symm 1
  have hv (v : SpechtModule emptyPartition) : v = a v • v₀ := by
    apply a.injective
    simp [v₀]
  let e : TensorMultiplicity V emptyPartition ≃ₗ[ℂ] ℂ :=
    { toFun := fun f => b (f.val v₀)
      invFun := fun z =>
        ⟨b.symm.toLinearMap.comp (z • a.toLinearMap), by
          intro s v w hw
          have he : w = v := by
            apply Subtype.ext
            rw [zero_labels_trivial s] at hw
            simpa using hw
          subst w
          change _ = slotOperator V 0 s _
          rw [slot_zero]
          rfl⟩
      left_inv := by
        intro f
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        change b.symm (b (f.val v₀) • a v) = f.val v
        rw [hv v, map_smul]
        apply b.injective
        simp [smul_eq_mul, mul_comm, v₀]
      right_inv := by
        intro z
        change b (b.symm (z • a v₀)) = z
        simp [v₀]
      map_add' := by intros; exact map_add b _ _
      map_smul' := by intros; exact map_smul b _ _ }
  refine ⟨e, ?_⟩
  intro g f
  change b (diagonalOperator V 0 g (f.val v₀)) = b (f.val v₀)
  rw [diagonal_zero]
  rfl

/-- Identity and multiplication for the product action on the evaluation sum. -/
theorem tensorEvaluationOperator_one {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)) :
    tensorEvaluationOperator V σ 1 1 = 1 := by
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro f
  change tensorEvaluationOperator V σ 1 1 (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f)) = _
  simp [tensorEvaluationOperator, Specs.AdvancedFiniteGroupRepresentations.tensorEvaluationOperator,
    tensorMultiplicityOperator_one]

theorem tensorEvaluationOperator_mul {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (s t : SymmetricGroup n) (g h : LinearGroup V) :
    tensorEvaluationOperator V σ (s * t) (g * h) =
      tensorEvaluationOperator V σ s g * tensorEvaluationOperator V σ t h := by
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro f
  change tensorEvaluationOperator V σ (s * t) (g * h)
      (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f)) =
    tensorEvaluationOperator V σ s g
      (tensorEvaluationOperator V σ t h (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f)))
  simp only [tensorEvaluationOperator, Specs.AdvancedFiniteGroupRepresentations.tensorEvaluationOperator,
    DirectSum.lmap_lof, TensorProduct.map_tmul, map_mul, tensorMultiplicityOperator_mul,
    Module.End.mul_apply]

/-- A bundled representation of S_n × GL(V) on the evaluation sum. -/
def tensorEvaluationRepresentation {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)) :
    Representation ℂ (SymmetricGroup n × LinearGroup V) (TensorEvaluationSum V n) where
  toFun z := tensorEvaluationOperator V σ z.1 z.2
  map_one' := tensorEvaluationOperator_one V σ
  map_mul' z w := tensorEvaluationOperator_mul V σ z.1 w.1 z.2 w.2

theorem tensorEvaluation_isomorphism [FiniteDimensional ℂ V] (n : ℕ) :
    ∃ e : TensorEvaluationSum V n ≃ₗ[ℂ] TensorPower V n,
      e.toLinearMap = tensorEvaluationMap V n ∧
      ∀ (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)),
        (∀ p, InheritedSpechtAction p (σ p)) →
        ∀ (s : SymmetricGroup n) (g : LinearGroup V) (x : TensorEvaluationSum V n),
          e (tensorEvaluationOperator V σ s g x) =
            slotOperator V n s (diagonalOperator V n g (e x)) := by
  refine ⟨tensorEvaluationEquiv V n, rfl, ?_⟩
  exact tensorEvaluation_equivariant V

end AdvancedFiniteGroupRepresentations
