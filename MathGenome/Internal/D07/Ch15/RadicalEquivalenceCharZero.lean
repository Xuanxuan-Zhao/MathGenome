import MathGenome.Internal.Specs.D07.Ch15.RadicalEquivalenceCharZero
import MathGenome.Internal.D07.Ch15.RadicalsImplySolvable
import MathGenome.Internal.D07.Ch15.SolvableGroups
import MathGenome.Internal.D07.Ch14.BaseChange
import Mathlib.FieldTheory.KummerExtension

/-!
The converse uses the field R of all elements in finite radical towers.
Finite composita make R a field and appending one radical step makes it
closed under extraction of roots. After base change to R, a finite solvable
Galois group must be trivial: a nontrivial solvable group has a nontrivial
cyclic quotient, whose fixed field would be a cyclic extension of R.
Kummer's theorem makes this extension radical and hence trivial. This is
an alternative to choosing one common exponent for an entire subnormal
series; it gives the same finite-tower conclusion for each root.
-/

noncomputable section
universe u v w
namespace D07.Ch15.RadicalEquivalenceCharZero
open Polynomial IntermediateField Specs.D07.Ch15.RadicalDefinition

section RadicalField
variable (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω]

/-- All elements that belong to some finite radical tower, with inherited operations. -/
def radicalField : IntermediateField K Ω where
  carrier := {x | solvableByRadicalsValue K Ω x}
  zero_mem' := by simpa using RadicalDefinition.base_solvable K Ω 0
  one_mem' := by simpa using RadicalDefinition.base_solvable K Ω 1
  add_mem' := by
    rintro x y ⟨E, hE, hx⟩ ⟨F, hF, hy⟩
    exact ⟨E ⊔ F, RadicalComposita.radical_compositum K Ω E F hE hF,
      add_mem ((show E ≤ E ⊔ F from le_sup_left) hx) ((show F ≤ E ⊔ F from le_sup_right) hy)⟩
  mul_mem' := by
    rintro x y ⟨E, hE, hx⟩ ⟨F, hF, hy⟩
    exact ⟨E ⊔ F, RadicalComposita.radical_compositum K Ω E F hE hF,
      mul_mem ((show E ≤ E ⊔ F from le_sup_left) hx) ((show F ≤ E ⊔ F from le_sup_right) hy)⟩
  inv_mem' := by
    rintro x ⟨E, hE, hx⟩
    exact ⟨E, hE, inv_mem hx⟩
  algebraMap_mem' := RadicalDefinition.base_solvable K Ω

/-- Appending one generator proves radical closure without postulating it. -/
theorem radicalField_rad_mem {x : Ω} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ radicalField K Ω) : x ∈ radicalField K Ω := by
  obtain ⟨E, hE, hx⟩ := hx
  exact ⟨adjoin K ((E : Set Ω) ∪ {x}),
    RadicalComposita.radical_extension_step hE ⟨x, n, hn, hx, rfl⟩,
    subset_adjoin K _ (Or.inr rfl)⟩

/-- Characteristic zero supplies primitive roots of every positive order in R. -/
theorem radicalField_primitiveRoots [IsAlgClosed Ω] [CharZero K]
    (n : ℕ) (hn : 0 < n) : (primitiveRoots n (radicalField K Ω)).Nonempty := by
  obtain ⟨ζ, hζ⟩ := RootsUnity.primitive_root_exists K Ω n hn (by exact_mod_cast hn.ne')
  have hzmem : ζ ∈ radicalField K Ω := radicalField_rad_mem K Ω hn
    (by rw [hζ.pow_eq_one]; exact one_mem _)
  refine ⟨⟨ζ, hzmem⟩, (mem_primitiveRoots hn).mpr ?_⟩
  exact hζ.of_map_of_injective (radicalField K Ω).val.injective

end RadicalField

/-- A radical-closed field has no nontrivial finite solvable Galois extension
inside a field in which its radical closure property holds. -/
theorem surjective_of_solvable_of_radical_closed
    (B : Type u) (L : Type v) [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L] [Group.IsSolvable (L ≃ₐ[B] L)]
    (hroots : ∀ n : ℕ, 0 < n → (primitiveRoots n B).Nonempty)
    (hrad : ∀ (x : L) (n : ℕ), 0 < n →
      x ^ n ∈ Set.range (algebraMap B L) → x ∈ Set.range (algebraMap B L)) :
    Function.Surjective (algebraMap B L) := by
  have htriv : Subsingleton (L ≃ₐ[B] L) := by
    by_contra h
    let : Nontrivial (L ≃ₐ[B] L) := not_subsingleton_iff_nontrivial.mp h
    obtain ⟨M, hM, hnormal, hcyclic, _⟩ :=
      SolvableGroups.exists_prime_cyclic_quotient (L ≃ₐ[B] L)
    let := hnormal
    let := hcyclic
    let E := fixedField M
    let : IsCyclic (E ≃ₐ[B] E) :=
      isCyclic_of_surjective (IsGalois.normalAutEquivQuotient M)
        (IsGalois.normalAutEquivQuotient M).surjective
    obtain ⟨a, ha, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic B E
      (hroots (Module.finrank B E) Module.finrank_pos)
    have haL : (a : L) ^ Module.finrank B E ∈ Set.range (algebraMap B L) := by
      obtain ⟨b, hb⟩ := ha
      exact ⟨b, congrArg Subtype.val hb⟩
    obtain ⟨b, hb⟩ := hrad (a : L) (Module.finrank B E) Module.finrank_pos haL
    have habot : a ∈ (⊥ : IntermediateField B E) :=
      mem_bot.mpr ⟨b, Subtype.ext hb⟩
    have hEt : (⊤ : IntermediateField B E) = ⊥ := by
      rw [← hgen]
      exact eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr habot))
    have hEbot : E = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have : (⟨x, hx⟩ : E) ∈ (⊥ : IntermediateField B E) := hEt ▸ mem_top
      obtain ⟨b, hb⟩ := mem_bot.mp this
      exact mem_bot.mpr ⟨b, congrArg Subtype.val hb⟩
    apply hM
    change fixedField M = ⊥ at hEbot
    rw [← fixingSubgroup_fixedField M, hEbot, fixingSubgroup_bot]
  intro x
  exact (IsGalois.mem_range_algebraMap_iff_fixed x).mpr fun σ =>
    congrArg (fun τ : L ≃ₐ[B] L => τ x) (Subsingleton.elim σ 1)

/-- Every finite solvable Galois subextension is contained in the field of
finite-tower radical elements. No normality hypothesis on that radical field
is required for the restriction injection. -/
theorem solvable_galois_le_radicalField
    (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] [CharZero K]
    (S : IntermediateField K Ω) [FiniteDimensional K S] [IsGalois K S]
    [Group.IsSolvable (S ≃ₐ[K] S)] : S ≤ radicalField K Ω := by
  let R := radicalField K Ω
  let N := S ⊔ R
  letI : Algebra S N := (inclusion le_sup_left).toAlgebra
  letI : Algebra R N := (inclusion le_sup_right).toAlgebra
  let : IsScalarTower K S N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower K R N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨hfin, hgal⟩ := D07.Ch14.BaseChange.finite_galois_base_change K Ω S R
  let := hfin
  let := hgal
  let ρ := restrictRestrictAlgEquivMapHom K S R N
  have hρ : Function.Injective ρ := D07.Ch14.BaseChange.restriction_injective S R
  let : Group.IsSolvable (N ≃ₐ[R] N) :=
    Group.isSolvable_of_isSolvable_injective (f := ρ) hρ
  have hsurj : Function.Surjective (algebraMap R N) :=
    surjective_of_solvable_of_radical_closed R N
      (radicalField_primitiveRoots K Ω) (by
        intro x n hn hx
        obtain ⟨b, hb⟩ := hx
        have hp : (x : Ω) ^ n ∈ R := by
          have heq := congrArg Subtype.val hb
          change (b : Ω) = (x : Ω) ^ n at heq
          exact heq ▸ b.property
        have hr := radicalField_rad_mem K Ω hn hp
        exact ⟨⟨x.val, hr⟩, Subtype.ext rfl⟩)
  intro x hx
  obtain ⟨b, hb⟩ := hsurj (inclusion (show S ≤ N from le_sup_left) ⟨x, hx⟩)
  have heq := congrArg Subtype.val hb
  change (b : Ω) = x at heq
  exact heq ▸ b.property

/-- The characteristic-zero equivalence for every nonzero polynomial,
with all roots taken in the specified algebraic closure. -/
theorem radical_equivalence :
    Specs.D07.Ch15.RadicalEquivalenceCharZero.RadicalEquivalence.{u, v} := by
  intro K Ω _ _ _ _ _ _ f hf
  constructor
  · exact RadicalsImplySolvable.all_radical_roots_group K Ω f
  · intro hsolv
    change Group.IsSolvable (f.SplittingField ≃ₐ[K] f.SplittingField) at hsolv
    let := hsolv
    let S := adjoin K (f.rootSet Ω)
    let : IsSplittingField K S f :=
      adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    let : FiniteDimensional K S := Polynomial.IsSplittingField.finiteDimensional S f
    let : Normal K S := Normal.of_isSplittingField f
    let : IsGalois K S := ⟨⟩
    let e := (IsSplittingField.algEquiv S f).autCongr
    let : Group.IsSolvable (S ≃ₐ[K] S) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    intro a ha
    exact solvable_galois_le_radicalField K Ω S
      (subset_adjoin K _ ((mem_rootSet_of_ne hf).mpr ha))

end D07.Ch15.RadicalEquivalenceCharZero
