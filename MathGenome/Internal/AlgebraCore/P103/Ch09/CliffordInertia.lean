import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.CliffordInertia
import MathGenome.Internal.AlgebraCore.P103.Ch09.CliffordRestriction
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionModels

noncomputable section
universe u v
namespace P103.Ch09.CliffordInertia
open P103.Ch08 CliffordRestrictionSpecs CliffordRestriction CliffordInertiaSpecs
open scoped MonoidAlgebra

variable {G : Type u} [Group G] (A : Subgroup G) [A.Normal]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V)

/-- Intrinsic isotypic components are A-invariant. -/
theorem component_stable (C : RegularMultiplicitySpecs.Family A) (i : Fin C.n)
    (a : A) : (component A C ρ i).map (ρ a) ≤ component A C ρ i := by
  unfold component CentralIdempotentSpecs.isotypic
  simp_rw [Submodule.map_iSup]
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  refine (show U.toSubmodule.map (ρ a) ≤ U.toSubmodule from ?_).trans
    (le_iSup_of_le U (le_iSup_of_le hU le_rfl))
  rintro _ ⟨v, hv, rfl⟩
  exact U.apply_mem_toSubmodule a hv

/-- The normal subgroup lies in the stabilizer of each isotypic component. -/
theorem contains_normal : containsType.{u,v} := by
  intro G _ A _ C V _ _ ρ i a ha
  change (component A C ρ i).map (ρ a) = component A C ρ i
  apply le_antisymm (component_stable A ρ C i ⟨a, ha⟩)
  intro x hx
  refine ⟨ρ a⁻¹ x, component_stable A ρ C i ⟨a⁻¹, A.inv_mem ha⟩ ⟨x, hx, rfl⟩, ?_⟩
  exact ρ.self_inv_apply a x

section Projections
variable [Finite G] [Fintype A]
variable (C : RegularMultiplicitySpecs.Family A)
variable (hC : RegularMultiplicitySpecs.Valid C)
variable (hEx : RegularMultiplicitySpecs.Exhaustive.{u,u} C)

/-- The central idempotent acts on V as the canonical isotypic projection. -/
def projector (i : Fin C.n) : V →ₗ[ℂ] V :=
  (restriction A ρ).asAlgebraHom (CentralIdempotentSpecs.idempotent (fourierFamily A C) i)

include hC hEx

theorem projector_range (i : Fin C.n) :
    LinearMap.range (projector A ρ C i) = component A C ρ i :=
  (CentralIdempotents.isotypic_projection (fourierFamily A C)
    (family_valid A C hC) (family_complete A C hEx) (restriction A ρ) i).1

theorem projector_fixed (i : Fin C.n) (x : V) (hx : x ∈ component A C ρ i) :
    projector A ρ C i x = x :=
  (CentralIdempotents.isotypic_projection (fourierFamily A C)
    (family_valid A C hC) (family_complete A C hEx) (restriction A ρ) i).2.2.1 x hx

/-- A translate outside the inertia subgroup is annihilated by this projection. -/
theorem projector_translate_zero (i : Fin C.n) (g : G)
    (hg : g ∉ inertia ρ (component A C ρ i))
    (x : V) (hx : x ∈ component A C ρ i) :
    projector A ρ C i (ρ g x) = 0 := by
  have hn : ¬ Nonempty
      ((conjugate A g (RegularMultiplicitySpecs.idealRepresentation (C.space i))).Equiv
        (RegularMultiplicitySpecs.idealRepresentation (C.space i))) := by
    intro he
    exact hg (transport A C hC hEx ρ g i i he)
  exact translate_le_kernel A ρ C hC hEx g i i hn ⟨x, hx, rfl⟩

/-- A nonzero I-invariant subspace of the whole component has translates
spanning V. Projection back to the component then forces that subspace to be U. -/
theorem component_irreducible (hρ : Irreducible ℂ G V ρ)
    (i : Fin C.n) (hi : component A C ρ i ≠ ⊥) :
    Irreducible ℂ (inertia ρ (component A C ρ i)) (component A C ρ i)
      (inertiaRepresentation ρ (component A C ρ i)) := by
  classical
  let U := component A C ρ i
  let I := inertia ρ U
  let τ := inertiaRepresentation ρ U
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hi, fun W => ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  let M : Submodule ℂ V := W.toSubmodule.map U.subtype
  have hM : M ≠ ⊥ := by
    intro hm
    apply hW
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.map_injective_of_injective U.subtype_injective
    change W.toSubmodule.map U.subtype = (⊥ : Submodule ℂ U).map U.subtype
    simpa only [Submodule.map_bot] using hm
  have hMU : M ≤ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hpM (g : G) : (M.map (ρ g)).map (projector A ρ C i) ≤ M := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    by_cases hg : g ∈ I
    · obtain ⟨z, hz, rfl⟩ := hx
      have hw := W.apply_mem_toSubmodule (⟨g, hg⟩ : I) hz
      have hgu : ρ g (z : V) ∈ U := (show U.map (ρ g) = U from hg).le
        ⟨z, z.property, rfl⟩
      change projector A ρ C i (ρ g (z : V)) ∈ M
      rw [projector_fixed A ρ C hC hEx i _ hgu]
      exact ⟨τ ⟨g, hg⟩ z, hw, rfl⟩
    · rw [projector_translate_zero A ρ C hC hEx i g hg x (hMU hx)]
      exact M.zero_mem
  have hUM : U ≤ M := by
    have hm : (⊤ : Submodule ℂ V).map (projector A ρ C i) ≤ M := by
      rw [← translates_span ρ hρ M hM, Submodule.map_iSup]
      exact iSup_le hpM
    rwa [Submodule.map_top, projector_range A ρ C hC hEx i] at hm
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro x _
  obtain ⟨z, hz, he⟩ := hUM x.property
  have hxz : z = x := Subtype.ext he
  exact hxz ▸ hz

end Projections

/-- The full A-isotypic component is irreducible under its inertia subgroup. -/
theorem irreducible_inertia : irreducibleType.{u,v} := by
  intro G _ _ A _ C hC hEx V _ _ ρ hρ i hi
  letI : Fintype A := Fintype.ofFinite A
  exact component_irreducible A ρ C hC hEx hρ i hi

section InducedMap
attribute [local instance] rightSubgroupModule inducedAlgebraModule inducedScalarModule

/-- The sum of the actual translates on a set of left-coset representatives. -/
def orbitSum (U : Submodule ℂ V) (T : Set G) : (T →₀ U) →ₗ[ℂ] V :=
  Finsupp.lsum ℂ (fun t : T => (ρ (t : G)).comp U.subtype)

@[simp] theorem orbitSum_single (U : Submodule ℂ V) (T : Set G) (t : T) (z : U) :
    orbitSum ρ U T (Finsupp.single t z) = ρ (t : G) (z : V) := by
  simp [orbitSum]

/-- Use the established balanced-tensor coordinates to construct evaluation. -/
def inductionEvaluation (U : Submodule ℂ V) {T : Set G}
    (hT : Subgroup.IsComplement T (inertia ρ U : Set G)) :
    Induced (inertia ρ U) (inertiaRepresentation ρ U) →ₗ[ℂ] V :=
  (orbitSum ρ U T).comp
    (TensorCoordinates.coordinates (inertia ρ U) (inertiaRepresentation ρ U) hT)

theorem inductionEvaluation_basis (U : Submodule ℂ V) {T : Set G}
    (hT : Subgroup.IsComplement T (inertia ρ U : Set G)) (g : G) (z : U) :
    inductionEvaluation ρ U hT
      (tensor (inertia ρ U) (inertiaRepresentation ρ U) (MonoidAlgebra.single g 1) z) =
      ρ g (z : V) := by
  classical
  unfold inductionEvaluation
  rw [LinearMap.comp_apply, TensorCoordinates.coordinates_tensor,
    TensorCoordinates.coordinateLinear_single, one_smul, orbitSum_single]
  change ρ ((hT.equiv g).1 : G) (ρ ((hT.equiv g).2 : G) (z : V)) = ρ g (z : V)
  rw [← Module.End.mul_apply, ← map_mul, hT.equiv_fst_mul_equiv_snd]

/-- Evaluation respects the induced G-action. -/
theorem inductionEvaluation_equivariant (U : Submodule ℂ V) {T : Set G}
    (hT : Subgroup.IsComplement T (inertia ρ U : Set G)) (g : G) :
    (inductionEvaluation ρ U hT).comp
        (induction (inertia ρ U) (inertiaRepresentation ρ U) g) =
      (ρ g).comp (inductionEvaluation ρ U hT) := by
  apply induced_hom_ext
  intro t z
  simp only [LinearMap.comp_apply, induction_tensor, MonoidAlgebra.single_mul_single,
    one_mul, inductionEvaluation_basis]
  rw [map_mul, Module.End.mul_apply]

/-- Irreducibility implies surjectivity, since the image contains every translate of U. -/
theorem inductionEvaluation_surjective (hρ : Irreducible ℂ G V ρ)
    (U : Submodule ℂ V) (hU : U ≠ ⊥) {T : Set G}
    (hT : Subgroup.IsComplement T (inertia ρ U : Set G)) :
    Function.Surjective (inductionEvaluation ρ U hT) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← translates_span ρ hρ U hU]
  apply iSup_le
  intro g
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨tensor (inertia ρ U) (inertiaRepresentation ρ U)
    (MonoidAlgebra.single g 1) ⟨x, hx⟩, inductionEvaluation_basis ρ U hT g ⟨x, hx⟩⟩

/-- Two different transversal elements differ by an element outside I. -/
theorem transversal_difference {I : Subgroup G} {T : Set G}
    (hT : Subgroup.IsComplement T (I : Set G)) (s t : T) (hst : s ≠ t) :
    (t : G)⁻¹ * (s : G) ∉ I := by
  intro h
  have he : (⟨t, ⟨(t : G)⁻¹ * (s : G), h⟩⟩ : T × (I : Set G)) =
      ⟨s, ⟨1, I.one_mem⟩⟩ := hT.1 (by simp)
  exact hst (congrArg Prod.fst he).symm

section Injectivity
variable [Finite G] [Fintype A]
variable (C : RegularMultiplicitySpecs.Family A)
variable (hC : RegularMultiplicitySpecs.Valid C)
variable (hEx : RegularMultiplicitySpecs.Exhaustive.{u,u} C)
include hC hEx

/-- Translate back and project to recover each direct-sum coordinate. -/
theorem orbitSum_coordinate (i : Fin C.n) {T : Set G}
    (hT : Subgroup.IsComplement T (inertia ρ (component A C ρ i) : Set G))
    (f : T →₀ component A C ρ i) (t : T) :
    projector A ρ C i (ρ (t : G)⁻¹ (orbitSum ρ (component A C ρ i) T f)) =
      (f t : V) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, Finsupp.add_apply, Submodule.coe_add, hf, hf']
  | single s z =>
    rw [orbitSum_single]
    by_cases hst : s = t
    · subst s
      rw [ρ.inv_self_apply]
      simpa only [Finsupp.single_eq_same] using projector_fixed A ρ C hC hEx i z z.property
    · have hm : ρ (t : G)⁻¹ (ρ (s : G) (z : V)) =
          ρ ((t : G)⁻¹ * (s : G)) (z : V) := by
        rw [map_mul, Module.End.mul_apply]
      rw [hm,
        projector_translate_zero A ρ C hC hEx i _ (transversal_difference hT s t hst) z z.property]
      simp [Ne.symm hst]

theorem orbitSum_injective (i : Fin C.n) {T : Set G}
    (hT : Subgroup.IsComplement T (inertia ρ (component A C ρ i) : Set G)) :
    Function.Injective (orbitSum ρ (component A C ρ i) T) := by
  intro f f' he
  ext t
  have hp := congrArg (fun x => projector A ρ C i (ρ (t : G)⁻¹ x)) he
  simpa only [orbitSum_coordinate A ρ C hC hEx i hT] using hp

/-- Evaluation is injective on the actual balanced tensor, via its established
transversal equivalence and coordinate recovery by central projections. -/
theorem inductionEvaluation_injective (i : Fin C.n) {T : Set G}
    (hT : Subgroup.IsComplement T (inertia ρ (component A C ρ i) : Set G)) :
    Function.Injective (inductionEvaluation ρ (component A C ρ i) hT) := by
  apply (orbitSum_injective A ρ C hC hEx i hT).comp
  exact (TensorCoordinates.transversalEquiv (inertia ρ (component A C ρ i))
    (inertiaRepresentation ρ (component A C ρ i)) hT).symm.injective

end Injectivity
end InducedMap

/-- The canonical map g ⊗ u ↦ gu is a G-equivariant isomorphism. -/
theorem induction_isomorphism : inductionType.{u,v} := by
  intro G _ _ A _ C hC hEx V _ _ ρ hρ i hi
  classical
  letI : Fintype A := Fintype.ofFinite A
  let U := component A C ρ i
  let I := inertia ρ U
  let τ := inertiaRepresentation ρ U
  obtain ⟨T, hT, _⟩ := I.exists_isComplement_left 1
  letI := inducedScalarModule I τ
  let e : Induced I τ ≃ₗ[ℂ] V := LinearEquiv.ofBijective (inductionEvaluation ρ U hT)
    ⟨inductionEvaluation_injective A ρ C hC hEx i hT,
      inductionEvaluation_surjective ρ hρ U hi hT⟩
  refine ⟨inductionData I τ, ⟨Representation.Equiv.mk e ?_, ?_⟩⟩
  · intro g
    exact inductionEvaluation_equivariant ρ U hT g
  · intro g z
    exact inductionEvaluation_basis ρ U hT g z

/-- If I = G, restriction to A is isotypic. -/
theorem isotypic_of_inertia_top : isotypicType.{u,v} := by
  intro G _ _ A _ C V _ _ ρ hρ i hi hI
  have hspan := translates_span ρ hρ (component A C ρ i) hi
  have he (g : G) : (component A C ρ i).map (ρ g) = component A C ρ i := by
    have hg : g ∈ inertia ρ (component A C ρ i) := by rw [hI]; trivial
    exact hg
  simpa only [he, iSup_const] using hspan

/-- Retain the complete restriction statement, including the actual
semisimple decomposition, the single orbit, and equal multiplicities. -/
theorem restriction_conclusions : cliffordType.{u,v} := clifford_restriction

/-- Clifford restriction and inertia, including all occurring components,
the single conjugacy orbit, equal multiplicities, and the case I = G. -/
theorem clifford_inertia : cliffordInertiaType.{u,v} :=
  ⟨restriction_conclusions, contains_normal, irreducible_inertia,
    induction_isomorphism, isotypic_of_inertia_top⟩

end P103.Ch09.CliffordInertia
