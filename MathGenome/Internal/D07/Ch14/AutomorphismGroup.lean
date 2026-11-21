import MathGenome.Internal.D07.Ch01.AutomorphismGroups
import MathGenome.Internal.D07.Ch12.ExtensionDefinition
import MathGenome.Internal.Specs.D07.Ch14.AutomorphismGroup

/-! Base-fixing field automorphisms, K07.14.automorphism_group.
All field extensions are allowed, with their specified scalar map.
-/

universe u v

namespace D07.Ch14.AutomorphismGroup

/-- Field automorphisms fixing the chosen image of K pointwise. -/
abbrev Aut (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :=
  L ≃ₐ[K] L

/-- Forgetting the base gives a homomorphism into the full field automorphism group. -/
def forget (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Aut K L →* RingAut L where
  toFun := AlgEquiv.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The subgroup of the full field automorphism group fixing the base. -/
def baseFixingSubgroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Subgroup (RingAut L) :=
  (forget K L).range

theorem group_laws (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Ch01.GroupDefinition.groupAxioms (Aut K L) (· * ·) 1 Inv.inv :=
  Ch01.GroupDefinition.group_laws (Aut K L)

theorem operations (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    (∀ (σ τ : Aut K L) (x : L), (σ * τ) x = σ (τ x)) ∧
    (1 : Aut K L) = AlgEquiv.refl ∧
    (∀ σ : Aut K L, σ⁻¹ = σ.symm) :=
  ⟨fun _ _ _ => rfl, rfl, fun _ => rfl⟩

theorem fixes_base (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (σ : Aut K L) (k : K) : σ (algebraMap K L k) = algebraMap K L k :=
  σ.commutes k

theorem automorphism_iff (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : RingAut L) :
    (∃ σ : Aut K L, σ.toRingEquiv = f) ↔
      ∀ k : K, f (algebraMap K L k) = algebraMap K L k := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact σ.commutes
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv h, rfl⟩

theorem forget_injective (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Function.Injective (forget K L) :=
  AlgEquiv.toRingEquiv_injective

theorem subgroup_carrier (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    (baseFixingSubgroup K L : Set (RingAut L)) =
      {f | ∀ k : K, f (algebraMap K L k) = algebraMap K L k} := by
  ext f
  exact automorphism_iff K L f

theorem subgroup_identification (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] :
    ∃ e : Aut K L ≃* baseFixingSubgroup K L,
      ∀ σ : Aut K L, (e σ : RingAut L) = σ.toRingEquiv := by
  exact ⟨MonoidHom.ofInjective (forget_injective K L), fun _ => rfl⟩

end D07.Ch14.AutomorphismGroup
