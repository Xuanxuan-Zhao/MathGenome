import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.FrobeniusCharacters
import MathGenome.Internal.AlgebraCore.P103.Ch09.InducedCharacter
import MathGenome.Internal.AlgebraCore.P103.Ch08.UnitarityPairing
import MathGenome.Internal.AlgebraCore.P103.Ch08.RegularMultiplicity

noncomputable section
open scoped BigOperators Classical
universe u v w
namespace P103.Ch09.FrobeniusCharacters
open Ch08 Ch08.RegularMultiplicitySpecs

/-- Reindex the inner conjugacy sum and use conjugacy invariance of the
second argument. The first argument need not itself be a class function. -/
theorem conjugacy_sum {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (ψ : H → ℂ) (θ : G → ℂ) (hθ : ∀ a g, θ (a * g * a⁻¹) = θ g) (x : G) :
    (∑ g : G, (if h : x⁻¹ * g * x ∈ H then ψ ⟨x⁻¹ * g * x, h⟩ else 0) *
      star (θ g)) = ∑ h : H, ψ h * star (θ h) := by
  classical
  have hreindex :
      (∑ g : G, (if h : x⁻¹ * g * x ∈ H then ψ ⟨x⁻¹ * g * x, h⟩ else 0) *
        star (θ g)) =
      ∑ g : G, if h : g ∈ H then ψ ⟨g, h⟩ * star (θ g) else 0 := by
    apply Fintype.sum_equiv (MulAut.conj x⁻¹).toEquiv
    intro g
    have he : θ (x⁻¹ * g * x) = θ g := by simpa using hθ x⁻¹ g
    have hx : (MulAut.conj x⁻¹).toEquiv g = x⁻¹ * g * x := by
      change x⁻¹ * g * x⁻¹⁻¹ = _
      rw [inv_inv]
    rw [hx]
    split_ifs <;> simp_all
  rw [hreindex]
  exact Finset.sum_congr_set (H : Set G) _ (fun h : H => ψ h * star (θ h))
    (by intro g hg; change g ∈ H at hg; simp [hg])
    (by intro g hg; change g ∉ H at hg; simp [hg])

/-- The finite conjugacy formula is adjoint to evaluation on the subgroup. -/
theorem function_reciprocity {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (ψ : H → ℂ) (θ : G → ℂ) (hθ : ∀ a g, θ (a * g * a⁻¹) = θ g) :
    UnitaritySpecs.functionPairingValue (InducedCharacterSpecs.inductionValue H ψ) θ =
      UnitaritySpecs.functionPairingValue ψ (fun h : H => θ h) := by
  classical
  unfold UnitaritySpecs.functionPairingValue InducedCharacterSpecs.inductionValue
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [mul_assoc (Nat.card H : ℂ)⁻¹, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [conjugacy_sum H ψ θ hθ]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card]
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = ((Fintype.card G : ℂ)⁻¹ * (Fintype.card G : ℂ)) *
        ((Fintype.card H : ℂ)⁻¹ * ∑ h : H, ψ h * star (θ h)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hG, one_mul]

/-- Ordinary complex class functions, with the fixed pairing orientation. -/
theorem class_function_reciprocity : FrobeniusCharactersSpecs.classFunctionReciprocityType.{u} := by
  intro G _ _ H ψ θ
  exact function_reciprocity H ψ θ θ.2

/-- Character reciprocity on every realization of the shared balanced tensor. -/
theorem character_reciprocity : FrobeniusCharactersSpecs.characterReciprocityType.{u,v,w} := by
  intro G _ _ H V _ _ _ W _ _ _ ρ σ D E
  have hc := induced_character H ρ D E
  letI := D.module
  letI : FiniteDimensional ℂ (Induced H ρ) := hc.1
  refine ⟨inferInstance, ?_⟩
  have hi : CharacterSpecs.characterValue D.representation =
      InducedCharacterSpecs.inductionValue H (CharacterSpecs.characterValue ρ) :=
    funext hc.2.1
  rw [hi]
  exact function_reciprocity H (CharacterSpecs.characterValue ρ)
    (CharacterSpecs.characterValue σ) (fun a g => character_conjugate σ g a)

/-- Hom dimensions in the first-variable-linear pairing agree; in particular
these are the multiplicities whenever the source and target are irreducible. -/
theorem multiplicity_reciprocity : FrobeniusCharactersSpecs.multiplicityReciprocityType.{u,v,w} := by
  intro G _ _ H V _ _ _ W _ _ _ ρ σ D E _hρ _hσ
  letI := D.module
  have hc := character_reciprocity H ρ σ D E
  letI : FiniteDimensional ℂ (Induced H ρ) := hc.1
  have hl := character_pairing D.representation σ
  have hr := character_pairing ρ (restrict H σ)
  have he : (Module.finrank ℂ (σ.IntertwiningMap D.representation) : ℂ) =
      (Module.finrank ℂ (ρ.IntertwiningMap (restrict H σ)) : ℂ) :=
    hl.1.symm.trans (hc.2.trans (hr.1.trans hr.2))
  exact_mod_cast he

/-- Reciprocity counts summands in any decompositions of the actual induced
and restricted modules. Completeness ensures that the original irreducibles
are among the representatives, and semisimplicity supplies decompositions. -/
theorem decomposition_reciprocity : FrobeniusCharactersSpecs.decompositionReciprocityType.{u,v,w} := by
  intro G _ _ H V _ _ _ W _ _ _ ρ σ D E hρ hσ
  have hfA : ∃ A : Ch08.RegularMultiplicitySpecs.Family H,
      Ch08.RegularMultiplicitySpecs.Valid A ∧
      Ch08.RegularMultiplicitySpecs.Exhaustive.{u,u} A :=
    RegularMultiplicity.finite_family
  have hfB : ∃ B : Ch08.RegularMultiplicitySpecs.Family G,
      Ch08.RegularMultiplicitySpecs.Valid B ∧
      Ch08.RegularMultiplicitySpecs.Exhaustive.{u,u} B :=
    RegularMultiplicity.finite_family
  obtain ⟨A, hA, hAex⟩ := hfA
  obtain ⟨B, hB, hBex⟩ := hfB
  have hAρ : Exhaustive.{u,v} A :=
    RegularMultiplicity.exhaustive_from_regular A hAex
  have hAres : Exhaustive.{u,w} A :=
    RegularMultiplicity.exhaustive_from_regular A hAex
  have hBσ : Exhaustive.{u,w} B :=
    RegularMultiplicity.exhaustive_from_regular B hBex
  have hBind : Exhaustive.{u,max u v} B :=
    RegularMultiplicity.exhaustive_from_regular B hBex
  letI := D.module
  have hc := character_reciprocity H ρ σ D E
  letI : FiniteDimensional ℂ (Induced H ρ) := hc.1
  obtain ⟨i, ⟨ei⟩⟩ := hAρ ρ hρ
  obtain ⟨j, ⟨ej⟩⟩ := hBσ σ hσ
  have hdi := RegularMultiplicity.multiplicity_decomposition B hB hBind D.representation
  have hdr := RegularMultiplicity.multiplicity_decomposition A hA hAres (restrict H σ)
  refine ⟨A, B, hA, hAex, hB, hBex, i, j, ⟨ei⟩, ⟨ej⟩, hdi.1, hdr.1, ?_⟩
  intro m n hm hn
  have hm' := hdi.2 m hm j
  have hn' := hdr.2 n hn i
  rw [RegularMultiplicity.character_of_equiv ej] at hm'
  rw [RegularMultiplicity.character_of_equiv ei] at hn'
  have hp := character_pairing ρ (restrict H σ)
  have hq := character_pairing (restrict H σ) ρ
  have hswap := hp.1.trans (hp.2.trans hq.1.symm)
  have he : (m j : ℂ) = (n i : ℂ) := hm'.trans (hc.2.trans (hswap.trans hn'.symm))
  exact_mod_cast he

end P103.Ch09.FrobeniusCharacters
