import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightData
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VermaModules
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Ordinary complex Cartan weights and the character ring of LA-H01. The order on
exponents is the reverse dominance order, so descending weight supports are
partially well ordered in the Hahn-series convention. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.FormalCharacters

open Module SerreRelations VermaModules HighestWeightData RootForm
open scoped BigOperators Classical Pointwise

universe u v w z

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

/-- A type synonym for the full complex Cartan dual, with its reverse dominance order. -/
def Exponent (_φ : Direction H) := Module.Dual ℂ H

instance : AddCommGroup (Exponent H φ) := inferInstanceAs (AddCommGroup (Module.Dual ℂ H))

abbrev exponent : Module.Dual ℂ H ≃+ Exponent H φ := AddEquiv.refl _

abbrev cone := positiveRootCone_value (fun i : simple H φ => i.val)

private theorem positive_direction {a : Module.Dual ℂ H} (ha : a ∈ cone H φ) :
    a = 0 ∨ 0 < φ a := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Or.inr i.property.1.2
  | zero => exact Or.inl rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | hx
    · simpa using hy
    rcases hy with rfl | hy
    · simpa using Or.inr hx
    exact Or.inr (by rw [map_add]; exact add_pos hx hy)
  | smul n x _ hx =>
    rcases hx with rfl | hx
    · simp
    cases n with
    | zero => simp
    | succ n =>
      exact Or.inr (by rw [map_nsmul, nsmul_eq_mul]; exact mul_pos (by positivity) hx)

private theorem cone_antisymm {a b : Module.Dual ℂ H}
    (h₁ : a - b ∈ cone H φ) (h₂ : b - a ∈ cone H φ) : a = b := by
  rcases positive_direction H φ h₁ with h | h
  · exact sub_eq_zero.mp h
  rcases positive_direction H φ h₂ with h' | h'
  · exact (sub_eq_zero.mp h').symm
  · simp only [map_sub] at h h'
    exact (not_lt_of_gt (sub_pos.mp h) (sub_pos.mp h')).elim

instance : PartialOrder (Exponent H φ) where
  le a b := (a : Module.Dual ℂ H) - b ∈ cone H φ
  le_refl a := by
    rw [sub_self]
    exact (cone H φ).zero_mem
  le_trans a b c h₁ h₂ := by
    exact sub_add_sub_cancel a b c ▸ (cone H φ).add_mem h₁ h₂
  le_antisymm a b h₁ h₂ := cone_antisymm H φ h₁ h₂

theorem exponent_le_iff (a b : Module.Dual ℂ H) :
    exponent H φ a ≤ exponent H φ b ↔ a - b ∈ cone H φ := Iff.rfl

instance : IsOrderedCancelAddMonoid (Exponent H φ) where
  add_le_add_left a b h c := by
    change (a : Module.Dual ℂ H) + c - (b + c) ∈ cone H φ
    exact add_sub_add_right_eq_sub a b c ▸ h
  le_of_add_le_add_left a b c h := by
    change (a : Module.Dual ℂ H) + b - (a + c) ∈ cone H φ at h
    change (b : Module.Dual ℂ H) - c ∈ cone H φ
    simpa only [add_sub_add_left_eq_sub] using h

abbrev Series := HahnSeries (Exponent H φ) ℤ

/-- The support is contained in finitely many translates of the negative cone. -/
def Bounded (f : Exponent H φ → ℤ) : Prop :=
  ∃ bounds : Finset (Exponent H φ), ∀ x, f x ≠ 0 → ∃ a ∈ bounds, a ≤ x

/-- The series ring in LA-H01. The convolution comes from Hahn series. -/
def boundedRing : Subring (Series H φ) where
  carrier := {f | Bounded H φ f.coeff}
  zero_mem' := ⟨∅, by simp⟩
  one_mem' := ⟨{0}, by
    intro x hx
    have h : x = 0 := by
      by_contra h
      simp [HahnSeries.coeff_one, h] at hx
    subst x
    exact ⟨0, Finset.mem_singleton_self _, le_rfl⟩⟩
  neg_mem' := by
    rintro f ⟨s, hs⟩
    exact ⟨s, fun x hx => hs x (by simpa using hx)⟩
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, fun x hx => ?_⟩
    by_cases hf : f.coeff x = 0
    · obtain ⟨a, ha, hax⟩ := ht x (by simpa [hf] using hx)
      exact ⟨a, Finset.mem_union_right _ ha, hax⟩
    · obtain ⟨a, ha, hax⟩ := hs x hf
      exact ⟨a, Finset.mem_union_left _ ha, hax⟩
  mul_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s + t, fun x hx => ?_⟩
    have hx' : x ∈ (f * g).support := hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp (HahnSeries.support_mul_subset hx')
    obtain ⟨a, ha, hay⟩ := hs y hy
    obtain ⟨b, hb, hbz⟩ := ht z hz
    exact ⟨a + b, Finset.add_mem_add ha hb, add_le_add hay hbz⟩

abbrev Completion := ↥(boundedRing H φ)

def coeff (f : Completion H φ) (a : Module.Dual ℂ H) : ℤ :=
  f.val.coeff (exponent H φ a)

variable [FiniteDimensional ℂ L] in
abbrev integralWeights := integralWeights_value (fun i : simple H φ => coroot_value H i.val)

/-- The subring of series supported on the integral weight lattice. -/
def integralRing [FiniteDimensional ℂ L] : Subring (Completion H φ) where
  carrier := {f | ∀ a : Module.Dual ℂ H, coeff H φ f a ≠ 0 → a ∈ integralWeights H φ}
  zero_mem' := by simp [coeff]
  one_mem' := by
    intro a ha
    have h : a = 0 := by
      by_contra h
      simp [coeff, HahnSeries.coeff_one, h] at ha
    exact h ▸ (integralWeights H φ).zero_mem
  add_mem' := by
    intro f g hf hg a ha
    by_cases h : coeff H φ f a = 0
    · apply hg a
      change coeff H φ f a + coeff H φ g a ≠ 0 at ha
      simpa [h] using ha
    · exact hf a h
  neg_mem' := by
    intro f hf a ha
    exact hf a (by simpa [coeff] using ha)
  mul_mem' := by
    intro f g hf hg a ha
    have ha' : exponent H φ a ∈ (f.val * g.val).support := ha
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_add.mp (HahnSeries.support_mul_subset ha')
    change (y : Module.Dual ℂ H) + z = a at hyz
    exact hyz ▸ (integralWeights H φ).add_mem (hf y hy) (hg z hz)

/-- The symbol e^a has coefficient one at exactly a. -/
def monomial (a : Module.Dual ℂ H) : Completion H φ :=
  ⟨HahnSeries.single (exponent H φ a) 1, ⟨{exponent H φ a}, by
    intro x hx
    have h : x = exponent H φ a := by
      by_contra h
      simp [h] at hx
    subst x
    exact ⟨_, Finset.mem_singleton_self _, le_rfl⟩⟩⟩

/-- Coefficients of the finite or infinite character of a weight module. -/
def multiplicity (V : Type v) [AddCommGroup V] [Module ℂ V]
    [LieRingModule L V] [LieModule ℂ L V] (a : Module.Dual ℂ H) : ℤ :=
  Module.finrank ℂ (weightSpace_value V H a)

abbrev GroupRing := AddMonoidAlgebra ℤ (Module.Dual ℂ H)
variable [FiniteDimensional ℂ L] in
abbrev IntegralGroupRing := AddMonoidAlgebra ℤ (integralWeights H φ)


section FiniteCharacter

variable [H.IsCartanSubalgebra]
variable (V : Type v) [AddCommGroup V] [Module ℂ V]
  [LieRingModule L V] [LieModule ℂ L V]

theorem weightSpaces_independent : iSupIndep (weightSpace_value V H) := by
  have h := (LieSubmodule.iSupIndep_toSubmodule.mpr
    (LieModule.iSupIndep_genWeightSpace ℂ H V)).comp
      (show Function.Injective (fun a : Module.Dual ℂ H => (a : H → ℂ)) from DFunLike.coe_injective)
  exact h.mono fun a => LieModule.weightSpace_le_genWeightSpace V a

theorem multiplicity_finiteSupport [FiniteDimensional ℂ V] :
    (Function.support (multiplicity H V)).Finite := by
  apply (WellFoundedGT.finite_ne_bot_of_iSupIndep (weightSpaces_independent H V)).subset
  intro a ha hb
  exact ha (by simp [multiplicity, hb])

/-- The ordinary finite character extended to all complex Cartan weights. -/
def finiteCharacter [FiniteDimensional ℂ V] : GroupRing H :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (multiplicity H V) (multiplicity_finiteSupport H V))

/-- The same finite character as an element of the actual group ring of P. -/
def character [FiniteDimensional ℂ L] [FiniteDimensional ℂ V] : IntegralGroupRing H φ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.subtypeDomain (fun a => a ∈ integralWeights H φ) (finiteCharacter H V).coeff)

end FiniteCharacter

def boundedRing_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H),
    Subring (Series H φ)

def integralRing_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (H : LieSubalgebra ℂ L) (φ : Direction H) [FiniteDimensional ℂ L],
    Subring (Completion H φ)

def monomial_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H),
    Module.Dual ℂ H → Completion H φ

def coeff_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H),
    Completion H φ → Module.Dual ℂ H → ℤ

def finiteCharacter_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V], GroupRing H

def character_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H)
    [H.IsCartanSubalgebra]
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ L] [FiniteDimensional ℂ V], IntegralGroupRing H φ

end Specs.LieAlgebrasAndRepresentations.FormalCharacters
