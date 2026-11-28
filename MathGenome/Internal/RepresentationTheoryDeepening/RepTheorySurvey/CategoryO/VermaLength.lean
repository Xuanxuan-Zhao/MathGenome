import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.VermaLength
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.Category
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightExactness
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CentralCharacters
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Batteries.Tactic.OpenPrivate

noncomputable section

open Module UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights (weightWeylGroup)
open Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism (rhoValue)
open scoped Classical ModuleCat.Algebra

namespace RepTheorySurvey.CategoryO

attribute [local instance 100] LieRing.ofAssociativeRing

open private finite_weightWeylGroup from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ChevalleyRestriction
open private lieHom_map_enveloping_smul from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal

universe u

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g) (lam : D.Weight)

local notation "X" => M D lam
local notation "W" => weightSpace D.cartan (M D lam)

private theorem verma_weight_data :
    DirectSum.IsInternal W ∧
      (∀ μ, FiniteDimensional ℂ (W μ)) ∧ (∀ μ, W μ ≠ ⊥ → lam - μ ∈ QPlus D) := by
  classical
  obtain ⟨hinternal, hfinite, hsupport, _⟩ :=
    _root_.LieAlgebrasAndRepresentations.VermaWeightsUniversal.verma_weights
      D.semisimple D.cartan D.direction D.regular lam (character D lam)
      (character_unique D lam).1
  exact ⟨hinternal, hfinite, fun μ hμ => (hsupport μ).mp hμ⟩

/-- Every simple root increases the direction by a uniform positive amount.
The extra index in the minimum accommodates the empty root system. -/
private theorem exists_root_increment : ∃ ε : ℝ, 0 < ε ∧ ∀ i : D.Simple, ε ≤ D.direction (D.alpha i) := by
  let : Finite D.Simple := finite_simple_roots D
  let step : Option D.Simple → ℝ := fun i => i.elim 1 (fun j => D.direction (D.alpha j))
  obtain ⟨i, _, hi⟩ := Set.exists_min_image Set.univ step Set.finite_univ ⟨none, Set.mem_univ _⟩
  refine ⟨step i, ?_, fun j => hi (some j) (Set.mem_univ _)⟩
  cases i with
  | none => exact zero_lt_one
  | some j => exact j.property.1.2

private theorem direction_nonnegative {μ : D.Weight} (h : μ ∈ QPlus D) : 0 ≤ D.direction μ := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact le_of_lt i.property.1.2
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_nonneg hx hy
  | smul n x _ hx => simpa only [map_nsmul] using nsmul_nonneg hx n

private theorem exists_weight_vector_outside
    (hinternal : DirectSum.IsInternal W) {A B : Submodule (U g) X} (hab : A < B) :
    ∃ μ, ∃ x ∈ W μ, x ∈ B ∧ x ∉ A := by
  let : LieRingModule g X := restrictedLieRingModule X (g := g)
  let : LieModule ℂ g X := restrictedLieModule X (g := g)
  let S : LieSubmodule ℂ D.cartan X :=
    { B.restrictScalars ℂ with
      lie_mem := fun {h x} hx => B.smul_mem (ι ℂ (h : g)) hx }
  have hspan : (⨆ μ, B.restrictScalars ℂ ⊓ W μ) = B.restrictScalars ℂ :=
    (WeightExactness.stableSubspace S hinternal).2.2
  by_contra! hn
  apply hab.not_ge
  intro x hx
  change x ∈ A.restrictScalars ℂ
  have hle : (⨆ μ, B.restrictScalars ℂ ⊓ W μ) ≤ A.restrictScalars ℂ :=
    iSup_le fun μ _ hx => hn μ _ hx.2 hx.1
  rw [hspan] at hle
  exact hle hx

/-- In a strict submodule interval, a weight vector of minimal distance to the
top in the positive direction becomes highest weight modulo the smaller module. -/
private theorem exists_highest_weight_vector_mod
    (hinternal : DirectSum.IsInternal W)
    (hsupport : ∀ μ, W μ ≠ ⊥ → lam - μ ∈ QPlus D)
    {A B : Submodule (U g) X} (hab : A < B) :
    ∃ μ, ∃ x ∈ W μ, x ∈ B ∧ x ∉ A ∧ ∀ i : D.Simple, (ι ℂ (D.e i)) • x ∈ A := by
  classical
  obtain ⟨ε, hε, hstep⟩ := exists_root_increment D
  let distance (μ : D.Weight) : ℝ := D.direction (lam - μ) / ε
  let height (μ : D.Weight) : ℕ := ⌊distance μ⌋₊
  let eligible (μ : D.Weight) := ∃ x ∈ W μ, x ∈ B ∧ x ∉ A
  have hnonempty : ∃ n : ℕ, ∃ μ, height μ = n ∧ eligible μ := by
    obtain ⟨μ, hμ⟩ := exists_weight_vector_outside D lam hinternal hab
    exact ⟨height μ, μ, rfl, hμ⟩
  obtain ⟨μ, hμ, x, hx, hxB, hxA⟩ := Nat.find_spec hnonempty
  refine ⟨μ, x, hx, hxB, hxA, fun i => ?_⟩
  by_contra hraised
  let : LieRingModule g X := restrictedLieRingModule X (g := g)
  let : LieModule ℂ g X := restrictedLieModule X (g := g)
  let ν := μ + D.alpha i
  have hweight : (ι ℂ (D.e i)) • x ∈ W ν := by
    change (ι ℂ (D.e i)) • x ∈ W (μ + D.alpha i)
    exact _root_.LieAlgebrasAndRepresentations.HighestWeight.root_action
        X D.cartan (D.alpha i) μ (D.e i) x (D.triple i).e_mem hx
  have helig : eligible ν := ⟨_, hweight, B.smul_mem _ hxB, hraised⟩
  have hν : W ν ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hweight
    exact hraised (hweight.symm ▸ A.zero_mem)
  have hnonneg : 0 ≤ distance ν := div_nonneg (direction_nonnegative D (hsupport ν hν)) hε.le
  have hdist : distance ν + 1 ≤ distance μ := by
    unfold distance
    rw [show lam - ν = (lam - μ) - D.alpha i by dsimp [ν]; abel, map_sub, sub_div]
    have hi : 1 ≤ D.direction (D.alpha i) / ε := (one_le_div hε).mpr (hstep i)
    linarith
  have hstrict : height ν < height μ := by
    have hfloor := Nat.floor_le_floor hdist
    rw [Nat.floor_add_one hnonneg] at hfloor
    exact hfloor
  exact (Nat.find_min hnonempty (hstrict.trans_eq hμ)) ⟨ν, rfl, helig⟩

/-- A nonzero highest-weight vector in a quotient compares its Verma central
character with that of the original module. -/
private theorem centralCharacter_eq_of_highest_mod
    (χ : D.Weight → Subalgebra.center ℂ (U g) →ₐ[ℂ] ℂ)
    (hscalar : ∀ μ z, ∀ y : M D μ, z.val • y = χ μ z • y)
    {A : Submodule (U g) X} {μ : D.Weight} {x : X}
    (hx : x ∈ W μ) (hxA : x ∉ A)
    (hkill : ∀ i : D.Simple, (ι ℂ (D.e i)) • x ∈ A) :
    χ lam = χ μ := by
  let V := X ⧸ A
  let : LieRingModule g V := restrictedLieRingModule V (g := g)
  let : LieModule ℂ g V := restrictedLieModule V (g := g)
  let q : X →ₗ[U g] V := A.mkQ
  let w : V := q x
  have hqzero (y : X) : q y = 0 ↔ y ∈ A := Submodule.Quotient.mk_eq_zero A
  have hw : w ≠ 0 := fun h => hxA ((hqzero x).mp h)
  have hwμ (h : D.cartan) : ⁅(h : g), w⁆ = μ h • w := by
    change (ι ℂ (h : g)) • q x = μ h • q x
    rw [← q.map_smul, ← q.map_smul_of_tower, (mem_weightSpace D.cartan X μ x).mp hx h]
  have hwe (i : D.Simple) : ⁅D.e i, w⁆ = 0 := by
    change (ι ℂ (D.e i)) • q x = 0
    rw [← q.map_smul]
    exact (hqzero _).mpr (hkill i)
  obtain ⟨⟨f, hf, _⟩, _⟩ :=
    _root_.LieAlgebrasAndRepresentations.VermaWeightsUniversal.verma_universal
      D.semisimple D.cartan D.direction D.regular μ (character D μ)
      (character_unique D μ).1 D.e
      (fun i => ⟨(D.triple i).e_mem, (D.triple i).e_ne_zero⟩) V w hwμ hwe
  let v := highestVector_value D.cartan D.direction (character D μ)
  ext z
  have hleft : z.val • w = χ lam z • w := by
    change z.val • q x = χ lam z • q x
    rw [← q.map_smul, hscalar lam z x, q.map_smul_of_tower]
  have hright : z.val • w = χ μ z • w := calc
    z.val • w = f (z.val • v) := by
      rw [lieHom_map_enveloping_smul D.cartan D.direction (character D μ) V
        (fun _ _ => rfl) f, hf]
    _ = f (χ μ z • v) := congrArg f (hscalar μ z v)
    _ = χ μ z • w := by rw [map_smul, hf]
  exact (smul_left_injective ℂ hw) (hleft.symm.trans hright)

private theorem finite_length_of_weight_detection
    {S : Type u} [Finite S] (weights : S → D.Weight)
    (hfinite : ∀ μ, FiniteDimensional ℂ (W μ))
    (hdetect : ∀ {A B : Submodule (U g) X}, A < B →
      ∃ s, ∃ x ∈ W (weights s), x ∈ B ∧ x ∉ A) :
    IsFiniteLength (U g) X := by
  let P : Submodule ℂ X := ⨆ s, W (weights s)
  let : ∀ s, FiniteDimensional ℂ (W (weights s)) := fun s => hfinite (weights s)
  have : FiniteDimensional ℂ P := Submodule.finiteDimensional_iSup _
  let restrict (A : Submodule (U g) X) : Submodule ℂ P :=
    (A.restrictScalars ℂ).comap P.subtype
  have hstrict : StrictMono restrict := by
    intro A B hab
    obtain ⟨s, x, hx, hxB, hxA⟩ := hdetect hab
    let y : P := ⟨x, Submodule.mem_iSup_of_mem s hx⟩
    refine lt_of_le_not_ge (fun _ hy => hab.le hy) (fun h => ?_)
    exact hxA (h (show y ∈ restrict B from hxB))
  have : WellFoundedGT (Submodule ℂ P) := isNoetherian_iff.mp inferInstance
  have : WellFoundedLT (Submodule ℂ P) := (inferInstance : IsArtinian ℂ P)
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_iff.mpr hstrict.wellFoundedGT, hstrict.wellFoundedLT⟩

/-- Every Verma module for the fixed triangular decomposition has finite length
as a left module over the enveloping algebra. -/
theorem verma_finite_length : Specs.RepTheorySurvey.CategoryO.verma_finite_length_type.{u} := by
  intro g _ _ _ D lam
  obtain ⟨hinternal, hfinite, hsupport⟩ := verma_weight_data D lam
  obtain ⟨_, _, _, χ, _, _, _, hχ, horbit, _⟩ :=
    _root_.LieAlgebrasAndRepresentations.CentralCharacters.central_characters.{u, u}
      D.semisimple D.cartan D.direction D.regular
  have hscalar (μ : D.Weight) (z : Subalgebra.center ℂ (U g)) (y : M D μ) :
      z.val • y = χ μ z • y :=
    (hχ μ (character D μ) (character_unique D μ).1 z).1 y
  let : Finite (weightWeylGroup D.cartan) := finite_weightWeylGroup D.cartan D.semisimple
  let ρ := rhoValue D.cartan D.direction
  apply finite_length_of_weight_detection D lam
    (fun w : weightWeylGroup D.cartan => w.val (lam + ρ) - ρ) hfinite
  intro A B hab
  obtain ⟨μ, x, hx, hxB, hxA, hkill⟩ :=
    exists_highest_weight_vector_mod D lam hinternal hsupport hab
  have heq := centralCharacter_eq_of_highest_mod D lam χ hscalar hx hxA hkill
  obtain ⟨w, hw⟩ := (horbit lam μ).mp heq
  refine ⟨w, x, ?_, hxB, hxA⟩
  rw [← hw, add_sub_cancel_right]
  exact hx

end RepTheorySurvey.CategoryO
