import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Derivations

/-! Relative derivations and the assertions of KD-01. -/
namespace AdvCommAlg.Differentials

universe u v w z

/-- The canonical A-derivations of B with values in its module M. -/
abbrev RelativeDerivation (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M] := Derivation A B M

theorem linear_characterization :
    Specs.AdvCommAlg.Differentials.linearCharacterization := by
  intro A B M _ _ _ _ _ _ _ f
  constructor
  · rintro ⟨D, hD, _⟩ x y
    simpa only [← hD, Derivation.coeFn_coe] using D.leibniz x y
  · intro h
    refine ⟨Derivation.mk' f h, rfl, ?_⟩
    intro E hE
    apply Derivation.ext
    intro x
    exact congrArg (fun L : B →ₗ[A] M => L x) hE

theorem additive_characterization :
    Specs.AdvCommAlg.Differentials.additiveCharacterization := by
  intro A B M _ _ _ _ _ _ _ f
  constructor
  · rintro ⟨D, rfl, _⟩
    exact ⟨D.map_add, D.leibniz, D.map_algebraMap⟩
  · rintro ⟨hadd, hmul, hbase⟩
    let L : B →ₗ[A] M :=
      { toFun := f
        map_add' := hadd
        map_smul' := fun a x => by
          rw [Algebra.smul_def, hmul, hbase, smul_zero, add_zero,
            IsScalarTower.algebraMap_smul]
          rfl }
    refine ⟨Derivation.mk' L hmul, rfl, ?_⟩
    intro E hE
    apply Derivation.ext
    exact congrFun hE

theorem vanishes_on_base :
    Specs.AdvCommAlg.Differentials.vanishesOnBase := by
  intro A B M _ _ _ _ _ _ _ D
  exact ⟨D.map_one_eq_zero, D.map_algebraMap⟩

theorem pointwise_operations :
    Specs.AdvCommAlg.Differentials.pointwiseOperations := by
  intro A B M _ _ _ _ _ _ _
  exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- B-linear postcomposition on the canonical derivation modules. -/
def postcompose : Specs.AdvCommAlg.Differentials.postcomposeType.{u,v,w,z} :=
  fun {_ _ _ _} _ _ _ _ _ _ _ _ _ _ _ f => f.compDer

theorem postcompose_apply :
    Specs.AdvCommAlg.Differentials.postcomposeApply.{u,v,w,z} := by
  intro A B M N _ _ _ _ _ _ _ _ _ _ _ f D x
  rfl

theorem ext_on_generators :
    Specs.AdvCommAlg.Differentials.extOnGenerators := by
  intro A B M _ _ _ _ _ _ _ s hs D E h
  exact Derivation.ext_of_adjoin_eq_top s hs h

theorem ext_on_family :
    Specs.AdvCommAlg.Differentials.extOnFamily.{u,v,w,z} := by
  intro A B M _ _ _ _ _ _ _ ι g hg D E h
  apply Derivation.ext_of_adjoin_eq_top (Set.range g) hg
  rintro _ ⟨i, rfl⟩
  exact h i

end AdvCommAlg.Differentials
