import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Derivations
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal

/-! The canonical universal differential and its free-module relation model (KD-02). -/
namespace AdvCommAlg.Differentials

universe u v w z
noncomputable section

abbrev Omega : Specs.AdvCommAlg.Differentials.omegaType.{u,v} :=
  fun A B _ _ _ => KaehlerDifferential A B

def universalDerivation : Specs.AdvCommAlg.Differentials.universalDerivationType.{u,v} :=
  fun A B _ _ _ => KaehlerDifferential.D A B

def universalEquiv : Specs.AdvCommAlg.Differentials.universalEquivType.{u,v,w} :=
  fun A B M _ _ _ _ _ _ _ => KaehlerDifferential.linearMapEquivDerivation A B

theorem universalEquiv_apply : Specs.AdvCommAlg.Differentials.universalEquivApply := by
  intro A B M _ _ _ _ _ _ _ f
  rfl

theorem universal_naturality : Specs.AdvCommAlg.Differentials.universalNaturality := by
  intro A B M N _ _ _ _ _ _ _ _ _ _ _ g f
  rfl

theorem differentials_span : Specs.AdvCommAlg.Differentials.differentialsSpan := by
  intro A B _ _ _
  exact KaehlerDifferential.span_range_derivation A B

open Specs.AdvCommAlg.Differentials (differentialRelations)

/-- The paper uses the negatives of Mathlib's first two sets of generators. -/
theorem differentialRelations_eq_kerTotal (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] :
    differentialRelations A B = KaehlerDifferential.kerTotal A B := by
  classical
  apply le_antisymm
  · rw [differentialRelations, Submodule.span_le]
    rintro _ ((⟨⟨x,y⟩, rfl⟩ | ⟨⟨x,y⟩, rfl⟩) | ⟨a, rfl⟩)
    · have h : Finsupp.single x 1 + Finsupp.single y 1 - Finsupp.single (x+y) 1 ∈
          KaehlerDifferential.kerTotal A B :=
        Submodule.subset_span (Or.inl (Or.inl (Set.mem_range_self (x,y))))
      change _ ∈ KaehlerDifferential.kerTotal A B
      convert (KaehlerDifferential.kerTotal A B).neg_mem h using 1 <;> abel
    · have h : Finsupp.single y x + Finsupp.single x y - Finsupp.single (x*y) 1 ∈
          KaehlerDifferential.kerTotal A B :=
        Submodule.subset_span (Or.inl (Or.inr (Set.mem_range_self (x,y))))
      change _ ∈ KaehlerDifferential.kerTotal A B
      convert (KaehlerDifferential.kerTotal A B).neg_mem h using 1 <;>
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one] <;> abel
    · exact Submodule.subset_span (Or.inr (Set.mem_range_self a))
  · rw [KaehlerDifferential.kerTotal, Submodule.span_le]
    rintro _ ((⟨⟨x,y⟩, rfl⟩ | ⟨⟨x,y⟩, rfl⟩) | ⟨a, rfl⟩)
    · have h : Finsupp.single (x+y) 1 - Finsupp.single x 1 - Finsupp.single y 1 ∈
          differentialRelations A B :=
        Submodule.subset_span (Or.inl (Or.inl (Set.mem_range_self (x,y))))
      change _ ∈ differentialRelations A B
      convert (differentialRelations A B).neg_mem h using 1 <;> abel
    · have h : Finsupp.single (x*y) 1 - x • Finsupp.single y 1 - y • Finsupp.single x 1 ∈
          differentialRelations A B :=
        Submodule.subset_span (Or.inl (Or.inr (Set.mem_range_self (x,y))))
      change _ ∈ differentialRelations A B
      convert (differentialRelations A B).neg_mem h using 1 <;>
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one] <;> abel
    · exact Submodule.subset_span (Or.inr (Set.mem_range_self a))

theorem relation_kernel : Specs.AdvCommAlg.Differentials.relationKernel := by
  intro A B _ _ _
  exact (differentialRelations_eq_kerTotal A B).trans (KaehlerDifferential.kerTotal_eq A B).symm

theorem relation_model : Specs.AdvCommAlg.Differentials.relationModel := by
  intro A B _ _ _
  let e := (Submodule.quotEquivOfEq _ _ (differentialRelations_eq_kerTotal A B)).trans
    (KaehlerDifferential.quotKerTotalEquiv A B)
  refine ⟨e, ?_⟩
  intro b
  simp [e, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    KaehlerDifferential.quotKerTotalEquiv]

theorem unique_universal_pair : Specs.AdvCommAlg.Differentials.uniqueUniversalPair := by
  intro A B U V _ _ _ _ _ _ _ _ _ _ _ δ ε hUU hUV hVU hVV
  obtain ⟨f, hf⟩ := hUV.surjective ε
  obtain ⟨g, hg⟩ := hVU.surjective δ
  have hgf : g.comp f = LinearMap.id := hUU.injective (by
    ext b
    change g (f (δ b)) = δ b
    rw [show f (δ b) = ε b from congrArg (fun D : Derivation A B V => D b) hf]
    exact congrArg (fun D : Derivation A B U => D b) hg)
  have hfg : f.comp g = LinearMap.id := hVV.injective (by
    ext b
    change f (g (ε b)) = ε b
    rw [show g (ε b) = δ b from congrArg (fun D : Derivation A B U => D b) hg]
    exact congrArg (fun D : Derivation A B V => D b) hf)
  let e : U ≃ₗ[B] V :=
    { f with
      invFun := g
      left_inv := fun x => congrArg (fun L : U →ₗ[B] U => L x) hgf
      right_inv := fun x => congrArg (fun L : V →ₗ[B] V => L x) hfg }
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply LinearEquiv.toLinearMap_injective
  exact hUV.injective (he'.trans hf.symm)

end
end AdvCommAlg.Differentials
