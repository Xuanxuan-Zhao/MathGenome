import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.FiniteCharacters

noncomputable section
open scoped BigOperators
open P203Specs.FiniteCharacters

namespace P203.FiniteCharacters

theorem finiteness : finitenessType := by
  intro G _ _
  infer_instance

theorem cardinality : cardinalityType := by
  intro G _ _
  rw [Nat.card_congr (dualEquiv G).toEquiv, Nat.card_eq_fintype_card]

/-- A character on a subgroup extends to the ambient finite abelian group. -/
theorem extend_character {G : Type*} [CommGroup G] [Finite G]
    (H : Subgroup G) (ψ : H →* Circle) :
    ∃ χ : Dual G, χ.domRestrict H = ψ := by
  obtain ⟨χ, hχ⟩ := MonoidHom.domRestrict_surjective (M := Circle) H
    (toUnits.toMonoidHom.comp ψ)
  refine ⟨toUnits.symm.toMonoidHom.comp χ, ?_⟩
  apply MonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hχ x
  simpa using congrArg toUnits.symm hx

/-- Prescribe any permissible value at one element by extending from its cyclic subgroup. -/
theorem exists_value {G : Type*} [CommGroup G] [Finite G]
    (g : G) (z : Circle) (hz : z ^ orderOf g = 1) :
    ∃ χ : Dual G, χ g = z := by
  let H := Subgroup.zpowers g
  let a : H := ⟨g, Subgroup.mem_zpowers g⟩
  have ha : ∀ x : H, x ∈ Subgroup.zpowers a := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Subtype.ext hn⟩
  have hord : orderOf a = orderOf g := (orderOf_submonoid a).symm
  let ψ : H →* Circle := monoidHomOfForallMemZpowers ha
    (hord.symm ▸ orderOf_dvd_of_pow_eq_one hz)
  obtain ⟨χ, hχ⟩ := extend_character H ψ
  refine ⟨χ, ?_⟩
  have heq := DFunLike.congr_fun hχ a
  exact heq.trans (monoidHomOfForallMemZpowers_apply_gen ha _)

/-- Every character value is an appropriate root of unity. -/
theorem value_pow {G : Type*} [CommGroup G] [Finite G]
    (g : G) (χ : Dual G) : (χ g : ℂ) ^ orderOf g = 1 := by
  change (Circle.coeHom.comp χ) g ^ orderOf g = 1
  rw [← map_pow, pow_orderOf_eq_one, map_one]

theorem values : valuesType := by
  intro G _ _ g ω
  constructor
  · rintro ⟨χ, rfl⟩
    exact value_pow g χ
  · intro hω
    let z : Circle := ⟨ω, mem_sphere_zero_iff_norm.mpr
      (Complex.norm_eq_one_of_pow_eq_one hω (orderOf_pos g).ne')⟩
    have hz : z ^ orderOf g = 1 := Subtype.ext hω
    obtain ⟨χ, hχ⟩ := exists_value g z hz
    exact ⟨χ, congrArg (fun w : Circle => (w : ℂ)) hχ⟩

/-- Evaluation into the full group of complex roots of unity. -/
def evaluation {G : Type*} [CommGroup G] [Finite G] (g : G) :
    Dual G →* rootsOfUnity (orderOf g) ℂ where
  toFun χ := ⟨Circle.toUnits (χ g), by
    apply (mem_rootsOfUnity _ _).mpr
    apply Units.ext
    exact value_pow g χ⟩
  map_one' := by apply Subtype.ext; apply Units.ext; rfl
  map_mul' χ ψ := by apply Subtype.ext; apply Units.ext; rfl

@[simp] theorem evaluation_coe {G : Type*} [CommGroup G] [Finite G]
    (g : G) (χ : Dual G) : ((evaluation g χ).val : ℂ) = (χ g : ℂ) := rfl

theorem evaluation_surjective {G : Type*} [CommGroup G] [Fintype G] (g : G) :
    Function.Surjective (evaluation g) := by
  intro ω
  obtain ⟨χ, hχ⟩ := (values G g (ω.val : ℂ)).mpr (by
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) ω.prop)
  exact ⟨χ, Subtype.ext (Units.ext hχ)⟩

theorem multiplicity : multiplicityType := by
  intro G _ _ g ω hω
  have hn : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
  let z : rootsOfUnity (orderOf g) ℂ :=
    ⟨Units.mk0 ω (by
      intro h
      rw [h, zero_pow (orderOf_pos g).ne'] at hω
      exact zero_ne_one hω), by
      apply (mem_rootsOfUnity _ _).mpr
      exact Units.ext hω⟩
  have he : {χ : Dual G // (χ g : ℂ) = ω} ≃ (evaluation g) ⁻¹' {z} :=
    Equiv.subtypeEquivRight (fun χ => by
      change (χ g : ℂ) = ω ↔ evaluation g χ = z
      exact ⟨fun h => Subtype.ext (Units.ext h), fun h =>
        congrArg (fun w : rootsOfUnity (orderOf g) ℂ => (w.val : ℂ)) h⟩)
  rw [Nat.card_congr he,
    Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective (evaluation_surjective g) z)]
  have hc := Subgroup.card_ker_mul_card_of_surjective (evaluation_surjective g)
  rw [Complex.card_rootsOfUnity, cardinality G] at hc
  exact Nat.eq_div_of_mul_eq_left (orderOf_pos g).ne' hc

/-- The sum of a nontrivial complex-valued group homomorphism vanishes. -/
theorem sum_hom_eq_zero {A : Type*} [Group A] [Fintype A]
    (χ : A →* ℂ) (hχ : χ ≠ 1) : ∑ a : A, χ a = 0 := by
  classical
  have hex : ∃ x : A, χ x ≠ 1 := by
    by_contra! h
    apply hχ
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hex
  refine eq_zero_of_mul_eq_self_left hx ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun y => (map_mul χ x y).symm

theorem nontrivialSum : nontrivialSumType := by
  intro G _ _ χ hχ
  apply sum_hom_eq_zero (Circle.coeHom.comp χ)
  intro he
  apply hχ
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  exact DFunLike.congr_fun he g

/-- Characters separate distinct elements. -/
theorem exists_separating {G : Type*} [CommGroup G] [Finite G]
    (g : G) (hg : g ≠ 1) : ∃ χ : Dual G, χ g ≠ 1 := by
  obtain ⟨χ, hχ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G Circle hg
  refine ⟨toUnits.symm.toMonoidHom.comp χ, ?_⟩
  intro h
  apply hχ
  exact toUnits.symm.injective (by simpa using h)

theorem average : averageType := by
  intro G _ _ g
  classical
  by_cases hg : g = 1
  · subst g
    simp only [map_one, Circle.coe_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ite_true]
    have hc : Fintype.card (Dual G) = Fintype.card G := by
      simpa only [Nat.card_eq_fintype_card] using cardinality G
    rw [hc]
    exact one_div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · rw [ite_eq_right hg]
    have hsum : ∑ χ : Dual G, (χ g : ℂ) = 0 := by
      let e : Dual G →* ℂ :=
        { toFun := fun χ => (χ g : ℂ)
          map_one' := rfl
          map_mul' := fun χ ψ => rfl }
      apply sum_hom_eq_zero e
      intro he
      obtain ⟨χ, hχ⟩ := exists_separating g hg
      apply hχ
      apply Subtype.ext
      exact DFunLike.congr_fun he χ
    rw [hsum, mul_zero]

end P203.FiniteCharacters
