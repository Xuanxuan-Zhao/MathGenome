import MathGenome.Internal.D07.Ch17.Definition
import MathGenome.Internal.Specs.D07.Ch17.SubrepresentationsQuotients

/-!
K07.17.subrepresentations_quotients (paper.tex:4643–4659).
The inverse group element supplies surjectivity on every invariant subspace.
Restriction and descent use the original linear operations and additive cosets.
-/
namespace D07.Ch17.SubrepresentationsQuotients

universe u v w

abbrev IsInvariant :
    Specs.D07.Ch17.SubrepresentationsQuotients.InvariantPredicateType.{u, v, w} :=
  Specs.D07.Ch17.SubrepresentationsQuotients.invariantValue

abbrev restriction :
    Specs.D07.Ch17.SubrepresentationsQuotients.RestrictionType.{u, v, w} :=
  Specs.D07.Ch17.SubrepresentationsQuotients.restrictionValue

abbrev quotient :
    Specs.D07.Ch17.SubrepresentationsQuotients.QuotientType.{u, v, w} :=
  Specs.D07.Ch17.SubrepresentationsQuotients.quotientValue

theorem invariance_characterization :
    Specs.D07.Ch17.SubrepresentationsQuotients.InvarianceCharacterization.{u, v, w} := by
  intro K G V _ _ _ _ ρ U
  constructor
  · intro h g x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact h g y hy
  · intro h g x hx
    exact h g (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

theorem invariant_image_eq :
    Specs.D07.Ch17.SubrepresentationsQuotients.InvariantImageEquality.{u, v, w} := by
  intro K G V _ _ _ _ ρ U h g
  apply le_antisymm
  · exact (invariance_characterization K G V ρ U).mp h g
  · intro x hx
    refine Submodule.mem_map.mpr ⟨ρ g⁻¹ x, h g⁻¹ x hx, ?_⟩
    exact ρ.self_inv_apply g x

theorem restriction_laws :
    Specs.D07.Ch17.SubrepresentationsQuotients.RestrictionLaws.{u, v, w} := by
  intro K G V _ _ _ _ ρ U h
  obtain ⟨h1, hm, hi⟩ :=
    Definition.endomorphism_laws K G U (restriction K G V ρ U h)
  exact ⟨fun _ _ => rfl, h1, hm, hi⟩

theorem restriction_automorphisms :
    Specs.D07.Ch17.SubrepresentationsQuotients.RestrictionAutomorphisms.{u, v, w} := by
  intro K G V _ _ _ _ ρ U h
  obtain ⟨e, he, _, hi⟩ := Definition.automorphism_correspondence K G U
  exact ⟨e (restriction K G V ρ U h), he _, hi _⟩

theorem quotient_well_defined :
    Specs.D07.Ch17.SubrepresentationsQuotients.QuotientWellDefined.{u, v, w} := by
  intro K G V _ _ _ _ ρ U h g x y hxy
  have hm : ρ g x - ρ g y ∈ U := by
    rw [← map_sub]
    exact h g (x - y) hxy
  exact ⟨hm, (Submodule.Quotient.eq U).mpr hm⟩

theorem quotient_laws :
    Specs.D07.Ch17.SubrepresentationsQuotients.QuotientLaws.{u, v, w} := by
  intro K G V _ _ _ _ ρ U h
  let q := quotient K G V ρ U h
  obtain ⟨h1, hm, hi⟩ := Definition.endomorphism_laws K G (V ⧸ U) q
  exact ⟨fun _ _ => rfl, fun g x y => (q g).map_add x y,
    fun g a x => (q g).map_smul a x, h1, hm, hi⟩

theorem quotient_automorphisms :
    Specs.D07.Ch17.SubrepresentationsQuotients.QuotientAutomorphisms.{u, v, w} := by
  intro K G V _ _ _ _ ρ U h
  obtain ⟨e, he, _, hi⟩ := Definition.automorphism_correspondence K G (V ⧸ U)
  exact ⟨e (quotient K G V ρ U h), he _, hi _⟩

theorem inclusion_quotient_equivariant :
    Specs.D07.Ch17.SubrepresentationsQuotients.InclusionQuotientEquivariance.{u, v, w} := by
  intro K G V _ _ _ _ ρ U h
  constructor
  · intro g
    ext x
    rfl
  · intro g
    ext x
    rfl

/-- Natural numbers act by their scalar multiplication. The element 0 sends
the invariant full subspace ℚ to zero, a proper subspace. -/
theorem monoid_counterexample :
    Specs.D07.Ch17.SubrepresentationsQuotients.MonoidCounterexample := by
  let ρ : Representation ℚ ℕ ℚ :=
    (Nat.castRingHom (Module.End ℚ ℚ)).toMonoidHom
  refine ⟨ρ, ⊤, fun _ _ _ => Submodule.mem_top, 0, ?_⟩
  intro heq
  have hm : (1 : ℚ) ∈ (⊤ : Submodule ℚ ℚ).map (ρ 0) := by
    rw [heq]
    exact Submodule.mem_top
  obtain ⟨x, _, hx⟩ := Submodule.mem_map.mp hm
  simp [ρ] at hx

end D07.Ch17.SubrepresentationsQuotients
