import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.PrimePowerTowerExample
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.OpenSubgroupClassification
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.OpenFiniteIndex
import Mathlib.Data.Nat.Prime.Infinite

/-! # The prime power tower in the fixed algebraic closure (FT-E09) -/
universe u v
noncomputable section
namespace AdvancedFieldTheory.FiniteFields
open ProfiniteIntegers
open Specs.AdvancedFieldTheory.OpenSubgroups
open Specs.AdvancedFieldTheory.PrimePowerTower

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]

/-- The supremum is proved below to be the literal increasing union. -/
abbrev primePowerTower (ℓ : ℕ) : IntermediateField k Ω := tower k Ω ℓ

/-- The intersection of the multiplication images ℓʳ Zhat, including r = 0. -/
abbrev primePowerResidues (ℓ : ℕ) : AddSubgroup Zhat := residues ℓ

theorem primePowerLayers_monotone (ℓ : ℕ) :
    Monotone (fun r : ℕ => finiteRootField k Ω (ℓ ^ r)) := by
  intro r t h
  exact finiteRootField_le_of_dvd k Ω (pow_dvd_pow ℓ h)

theorem primePowerTower_union (ℓ : ℕ) :
    (primePowerTower k Ω ℓ : Set Ω) =
      ⋃ r : ℕ, (finiteRootField k Ω (ℓ ^ r) : Set Ω) := by
  exact IntermediateField.coe_iSup_of_directed (primePowerLayers_monotone k Ω ℓ).directed_le

theorem mem_primePowerTower (ℓ : ℕ) (x : Ω) :
    x ∈ primePowerTower k Ω ℓ ↔ ∃ r : ℕ, x ∈ finiteRootField k Ω (ℓ ^ r) := by
  rw [← SetLike.mem_coe, primePowerTower_union, Set.mem_iUnion]
  rfl

variable [IsAlgClosure k Ω]

/-- The degrees of the contained layers contradict any finite degree of the union. -/
theorem primePowerTower_infinite_degree (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ¬ FiniteDimensional k (primePowerTower k Ω ℓ) := by
  intro h
  let := h
  let d := Module.finrank k (primePowerTower k Ω ℓ)
  have hb : ℓ ^ d ≤ d := by
    have hh := IntermediateField.finrank_le_of_le_right
      (show finiteRootField k Ω (ℓ ^ d) ≤ primePowerTower k Ω ℓ from
        le_iSup (fun r : ℕ => Specs.AdvancedFieldTheory.rootField k Ω (ℓ ^ r)) d)
    rwa [finiteRootField_finrank k Ω (ℓ ^ d) (pow_pos hℓ.pos _)] at hh
  exact (not_le_of_gt (Nat.lt_pow_self hℓ.one_lt)) hb

set_option maxHeartbeats 1000000 in
/-- A finite layer contained in this increasing union is contained in one stage.
Here the base field is finite, so the entire finite layer can be bounded. -/
theorem finiteRootField_le_primePowerTower_stage (ℓ s : ℕ) (hs : 0 < s)
    (h : finiteRootField k Ω s ≤ primePowerTower k Ω ℓ) :
    ∃ r : ℕ, finiteRootField k Ω s ≤ finiteRootField k Ω (ℓ ^ r) := by
  classical
  let : Finite (finiteRootField k Ω s) :=
    (Nat.card_pos_iff.mp (by
      rw [finiteRootField_card k Ω s hs]
      exact pow_pos Fintype.card_pos s)).2
  have hx (x : finiteRootField k Ω s) :
      ∃ r : ℕ, (x : Ω) ∈ finiteRootField k Ω (ℓ ^ r) :=
    (mem_primePowerTower k Ω ℓ x).mp (h x.property)
  choose r hr using hx
  obtain ⟨R, hR⟩ := (Set.finite_range r).bddAbove
  refine ⟨R, ?_⟩
  intro x hx
  have hb : r ⟨x, hx⟩ ≤ R := hR (Set.mem_range_self (f := r) ⟨x, hx⟩)
  exact primePowerLayers_monotone k Ω ℓ hb (hr ⟨x, hx⟩)

/-- Every prime layer of different prime degree is excluded. -/
theorem primePowerTower_excludes_prime (ℓ : ℕ) (hℓ : ℓ.Prime)
    (s : ℕ) (hs : s.Prime) (hne : s ≠ ℓ) :
    ¬ finiteRootField k Ω s ≤ primePowerTower k Ω ℓ := by
  intro h
  obtain ⟨r, hr⟩ := finiteRootField_le_primePowerTower_stage k Ω ℓ s hs.pos h
  exact hne (Nat.prime_eq_prime_of_dvd_pow hs hℓ
    ((finiteRootField_le_iff k Ω s (ℓ ^ r) hs.pos (pow_pos hℓ.pos _)).mp hr))

theorem primePowerTower_fieldProperties :
    Specs.AdvancedFieldTheory.PrimePowerTower.fieldProperties_type.{u,v} := by
  intro k Ω _ _ _ _ _ ℓ hℓ
  obtain ⟨s, hls, hs⟩ := Nat.exists_infinite_primes (ℓ + 1)
  have hne : s ≠ ℓ := by omega
  have hex := primePowerTower_excludes_prime k Ω ℓ hℓ s hs hne
  refine ⟨primePowerLayers_monotone k Ω ℓ, primePowerTower_union k Ω ℓ,
    ?_, (primePowerTower k Ω ℓ).algebraMap_mem, primePowerTower_infinite_degree k Ω ℓ hℓ,
    primePowerTower_excludes_prime k Ω ℓ hℓ, ⟨s, hs, hne, hex⟩, ?_⟩
  · simpa using finiteRootField_one k Ω
  · intro htop
    apply hex
    change finiteRootField k Ω s ≤ tower k Ω ℓ
    rw [htop]
    exact le_top

omit [IsAlgClosure k Ω] in
/-- Fixing the literal union means fixing every layer. -/
theorem primePowerTower_fixingSubgroup (ℓ : ℕ) :
    (primePowerTower k Ω ℓ).fixingSubgroup =
      ⨅ r : ℕ, (finiteRootField k Ω (ℓ ^ r)).fixingSubgroup := by
  ext σ
  simp only [Subgroup.mem_iInf, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h r x hx
    exact h x ((mem_primePowerTower k Ω ℓ x).mpr ⟨r, hx⟩)
  · intro h x hx
    obtain ⟨r, hr⟩ := (mem_primePowerTower k Ω ℓ x).mp hx
    exact h r x hr

/-- E08 applied at every positive prime-power modulus. -/
theorem primePowerResidues_kernels (ℓ : ℕ) (hℓ : ℓ.Prime) :
    primePowerResidues ℓ = ⨅ r : ℕ, (π ⟨ℓ ^ r, pow_pos hℓ.pos r⟩).ker := by
  apply iInf_congr
  intro r
  exact (ker_π ⟨ℓ ^ r, pow_pos hℓ.pos r⟩).symm

theorem primePowerTower_subgroupProperties :
    Specs.AdvancedFieldTheory.PrimePowerTower.subgroupProperties_type.{u,v} := by
  intro k Ω _ _ _ _ _ ℓ hℓ coords e he
  let : IsGalois k Ω := algebraicClosure_isGalois k Ω
  have hp : pullback e (primePowerResidues ℓ) = (primePowerTower k Ω ℓ).fixingSubgroup := by
    rw [primePowerResidues_kernels ℓ hℓ, primePowerTower_fixingSubgroup]
    calc
      pullback e (⨅ r : ℕ, (π ⟨ℓ ^ r, pow_pos hℓ.pos r⟩).ker) =
          ⨅ r : ℕ, pullback e (π ⟨ℓ ^ r, pow_pos hℓ.pos r⟩).ker := by
        ext σ
        change ((e σ).toAdd ∈ ⨅ r : ℕ, (π ⟨ℓ ^ r, pow_pos hℓ.pos r⟩).ker) ↔ _
        simp only [AddSubgroup.mem_iInf, Subgroup.mem_iInf]
        rfl
      _ = _ := iInf_congr fun r => kernel_pullback k Ω coords e he
        ⟨ℓ ^ r, pow_pos hℓ.pos r⟩
  have hc : IsClosed ((primePowerTower k Ω ℓ).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    fixingSubgroup_isClosed k Ω _
  have hn : ¬ IsOpen ((primePowerTower k Ω ℓ).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) := by
    intro h
    exact primePowerTower_infinite_degree k Ω ℓ hℓ
      ((fixingSubgroup_isOpen_iff_finiteDimensional k Ω _).mp h)
  have hz : (primePowerTower k Ω ℓ).fixingSubgroup.index = 0 := by
    apply Subgroup.not_finiteIndex_iff.mp
    intro hi
    exact hn ((closed_subgroup_isOpen_iff_finiteIndex _ hc).mpr hi)
  have hrc : IsClosed (primePowerResidues ℓ : Set Zhat) := by
    rw [primePowerResidues_kernels ℓ hℓ, AddSubgroup.coe_iInf]
    exact isClosed_iInter fun r => (clopen_ker_π ⟨ℓ ^ r, pow_pos hℓ.pos r⟩).isClosed
  have hrn : ¬ IsOpen (primePowerResidues ℓ : Set Zhat) := by
    intro h
    apply hn
    rw [← hp]
    exact h.preimage e.continuous
  have hrz : (primePowerResidues ℓ).index = 0 := by
    have hidx := Subgroup.index_comap_of_surjective
      (primePowerResidues ℓ).toSubgroup (f := e.toMonoidHom) e.surjective
    rw [AddSubgroup.index_toSubgroup] at hidx
    change (pullback e (primePowerResidues ℓ)).index = _ at hidx
    rw [hp, hz] at hidx
    exact hidx.symm
  exact ⟨primePowerTower_fixingSubgroup k Ω ℓ, hp, hc, hn,
    Subgroup.index_eq_zero_iff_infinite.mp hz, hz, hrc, hrn,
    AddSubgroup.index_eq_zero_iff_infinite.mp hrz, hrz⟩

/-- Instantiate the correspondence with the arithmetic Frobenius map Θ of E06. -/
theorem primePowerTower_arithmeticExample :
    Specs.AdvancedFieldTheory.PrimePowerTower.arithmeticExample_type.{u,v} := by
  intro k Ω _ _ _ _ _ ℓ hℓ
  obtain ⟨coords, hc, e, he, _⟩ := AbsoluteGalois.absoluteGaloisGroup k Ω
  exact ⟨coords, hc, e, he.1, he.2,
    primePowerTower_subgroupProperties k Ω ℓ hℓ coords e he.1⟩

end AdvancedFieldTheory.FiniteFields
