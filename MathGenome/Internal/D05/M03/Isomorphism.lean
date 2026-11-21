import MathGenome.Internal.D05.M03.InjectiveSurjective
import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M03.Isomorphism

/-! K05.03.isomorphism: linear inverses and transport of arbitrary indexed bases. -/

namespace D05.M03.Isomorphism

/-- Linear isomorphisms use the canonical linear-equivalence structure. -/
abbrev isomorphism (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] := V ≃ₗ[K] W

theorem isomorphism_iff_bijective :
    Specs.D05.M03.Isomorphism.isomorphism_iff_bijective := by
  intro K V W _ _ _ _ _ T
  constructor
  · rintro ⟨e, rfl⟩
    exact e.bijective
  · intro hT
    -- The set-theoretic inverse is supplied by bijectivity. Only the given
    -- forward linearity is needed to construct a `LinearEquiv`.
    exact ⟨{ T, Equiv.ofBijective T hT with }, rfl⟩

theorem inverse_laws : Specs.D05.M03.Isomorphism.inverse_laws := by
  intro K V W _ _ _ _ _ T
  exact ⟨T.symm_comp, T.comp_symm⟩

theorem inverse_of_bijective :
    Specs.D05.M03.Isomorphism.inverse_of_bijective := by
  intro K V W _ _ _ _ _ T hT
  obtain ⟨e, rfl⟩ := (isomorphism_iff_bijective T).mpr hT
  refine ⟨e.symm.toLinearMap, inverse_laws e, ?_⟩
  rintro S ⟨hleft, _⟩
  apply LinearMap.ext
  intro y
  have h := congrArg (fun f : V →ₗ[K] V => f (e.symm y)) hleft
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h

theorem inverse_linear_combination :
    Specs.D05.M03.Isomorphism.inverse_linear_combination := by
  intro K V W _ _ _ _ _ T a b y z
  rw [map_add, T.symm.map_smul, T.symm.map_smul]

theorem identity_isomorphism : Specs.D05.M03.Isomorphism.identity_isomorphism := by
  intro K V _ _ _
  exact ⟨LinearEquiv.refl K V, rfl⟩

theorem composition_isomorphism :
    Specs.D05.M03.Isomorphism.composition_isomorphism := by
  intro K V W U _ _ _ _ _ _ _ T S hT hS
  apply (isomorphism_iff_bijective (S.comp T)).mpr
  exact ⟨hS.1.comp hT.1, hS.2.comp hT.2⟩

theorem inverse_identity : Specs.D05.M03.Isomorphism.inverse_identity := by
  intro K V _ _ _
  rfl

theorem inverse_composition : Specs.D05.M03.Isomorphism.inverse_composition := by
  intro K V W U _ _ _ _ _ _ _ T S
  rfl

theorem map_basis : Specs.D05.M03.Isomorphism.map_basis := by
  intro K V W I _ _ _ _ _ T b
  exact ⟨b.map T, fun i => b.map_apply T i⟩

theorem map_basis_independent_span :
    Specs.D05.M03.Isomorphism.map_basis_independent_span := by
  intro K V W I _ _ _ _ _ T b
  exact (D05.M02.Basis.basis_iff_independent_span (fun i => T (b i))).mp
    (map_basis T b)

end D05.M03.Isomorphism
