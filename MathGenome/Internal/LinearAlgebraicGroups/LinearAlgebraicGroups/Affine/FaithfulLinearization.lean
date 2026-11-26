import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.FaithfulLinearization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ComoduleFiniteness

open AlgebraicGeometry CategoryTheory Coalgebra Opposite WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

open RationalRepresentations

variable {k : Type u} [Field k]

/-- Applying the counit to the ambient vector factor recovers a basis vector
of a subcomodule of the regular coaction from its matrix coefficients. -/
private theorem basis_vector_eq_sum_coefficients {ι : Type u} [Fintype ι]
    (A : HopfAlgebraCategory k) (W : Submodule k A) (b : Module.Basis ι k W)
    (σ : RightComodule k A W)
    (hσ : (W.subtype.rTensor A).comp σ.coaction = Coalgebra.comul.comp W.subtype)
    (j : ι) :
    (b j : A) = ∑ i, Coalgebra.counit (R := k) (b i : A) • coefficients A b σ i j := by
  have h := DFunLike.congr_fun hσ (b j)
  change W.subtype.rTensor A (σ.coaction (b j)) = Coalgebra.comul (R := k) (b j : A) at h
  rw [coaction_apply_basis A b σ, map_sum] at h
  have he := congrArg (fun t : A ⊗[k] A ↦
    TensorProduct.lid k A ((Coalgebra.counit (R := k)).rTensor A t)) h
  simpa only [map_sum, LinearMap.rTensor_tmul, Submodule.subtype_apply,
    TensorProduct.lid_tmul, Coalgebra.rTensor_counit_comul, one_smul] using he.symm

private theorem surjective_of_coefficients {ι B : Type u} [Fintype ι] [CommRing B] [Algebra k B]
    (A : HopfAlgebraCategory k) (s : Finset A)
    (hs : Algebra.adjoin k (s : Set A) = ⊤)
    (W : Submodule k A) (hsW : (s : Set A) ⊆ W) (b : Module.Basis ι k W)
    (σ : RightComodule k A W)
    (hσ : (W.subtype.rTensor A).comp σ.coaction = Coalgebra.comul.comp W.subtype)
    (q : B →ₐ[k] A) (hq : ∀ i j, coefficients A b σ i j ∈ q.range) :
    Function.Surjective q := by
  apply (AlgHom.range_eq_top q).mp
  apply top_le_iff.mp
  rw [← hs]
  apply Algebra.adjoin_le
  intro a ha
  let x : W := ⟨a, hsW ha⟩
  have hb (j : ι) : (b j : A) ∈ q.range := by
    rw [basis_vector_eq_sum_coefficients A W b σ hσ j]
    exact q.range.toSubmodule.sum_mem fun i _ ↦ q.range.toSubmodule.smul_mem _ (hq i j)
  change (x : A) ∈ q.range
  rw [← b.sum_repr x]
  change W.subtype (∑ i, b.repr x i • b i) ∈ q.range
  rw [map_sum]
  exact q.range.toSubmodule.sum_mem fun i _ ↦ by
    rw [map_smul]
    exact q.range.toSubmodule.smul_mem _ (hb i)

private theorem spectrum_faithfulLinearization (A : HopfAlgebraCategory k)
    [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (L : Specs.AffineAlgebraicGroup k),
      Nonempty ((groupPointsFunctor k).obj L.val ≅
        Specs.StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))) ∧
      ∃ f : ((affineHopfSpec k).obj (op A)).val ⟶ L.val,
        IsClosedImmersion f.hom.hom.left := by
  classical
  let ρ : RightComodule k A A := RightComodule.regular
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k A).out
  obtain ⟨W₀, hsW⟩ := ρ.exists_finiteSubcomodule_containing (s : Set A) s.finite_toSet
  let W := W₀.val
  let : FiniteDimensional k W := W₀.property.2
  obtain ⟨σ, hσ⟩ := (ρ.isSubcomodule_iff_exists_coaction W).mp W₀.property.1
  let n := Module.finrank k W
  let ι := ULift.{u} (Fin n)
  let b : Module.Basis ι k W := (Module.finBasis k W).reindex Equiv.ulift.symm
  let G := (affineHopfSpec k).obj (op A)
  obtain ⟨e, he, _⟩ := hopfSpecPoints k
  let B := Specs.StandardGroups.GLCoordinates k ι
  obtain ⟨h, _, _, _, _, _, _, hL⟩ := StandardGroups.generalLinearGroupSpecification k ι
  let := h.hopf
  let L := Specs.StandardGroups.spectrum k B
  obtain ⟨d, hd, l, hl⟩ := hL
  obtain ⟨E, hE⟩ := representationCoactionComparison A b G L.val (e A) l
  let f := E.symm σ
  have hcoeff : coefficients A b σ = universalMatrix A G L.val (e A) l f := by
    simpa only [f, Equiv.apply_symm_apply] using hE f
  refine ⟨n, L, ⟨l⟩, f, ?_⟩
  let R := CommAlgCat.of k A
  let p := (e A).hom.app R (toConv (AlgHom.id k A))
  let y := ((groupPointsFunctor k).map f).app R p
  let q : B →ₐ[k] A := (d.inv.app R y).ofConv
  have hy : d.hom.app R (toConv q) = y := by
    change d.hom.app R (d.inv.app R y) = y
    rw [← GrpCat.comp_apply, d.inv_hom_id_app]
    rfl
  have hf : f.hom.hom.left = Spec.map (CommRingCat.ofHom q.toRingHom) := by
    have hp : (p : Points G.val.X R).left = 𝟙 (Spec (CommRingCat.of A)) := by
      rw [he A R (toConv (AlgHom.id k A))]
      exact Spec.map_id _
    have hy' := congrArg (fun z : Points L.val.X R ↦ z.left) hy
    rw [hd R q] at hy'
    change Spec.map (CommRingCat.ofHom q.toRingHom) =
      (p : Points G.val.X R).left ≫ f.hom.hom.left at hy'
    rw [hp] at hy'
    exact (hy'.trans (Category.id_comp f.hom.hom.left)).symm
  have hq (i j : ι) : coefficients A b σ i j ∈ q.range := by
    refine ⟨Specs.StandardGroups.universalMatrix k ι i j, ?_⟩
    have hm := hl R q
    rw [hy] at hm
    exact (congrArg (fun M : Matrix ι ι A ↦ M i j) (hcoeff.trans hm)).symm
  rw [hf]
  exact IsClosedImmersion.spec_of_surjective _
    (surjective_of_coefficients A s hs W hsW b σ hσ q hq)

/-- Finite-dimensional faithful linearization over an arbitrary field. -/
theorem faithfulLinearization : Specs.FaithfulLinearization.{u} := by
  intro k _ G
  let e := finiteTypeHopfEquivalence k
  let B := (e.inverse.obj G).unop
  let i : ((finiteTypeHopfSpec k).obj (op B)) ≅ G := e.counitIso.app G
  let j := (inducedFunctor
    (Subtype.val : Specs.AffineAlgebraicGroup k → Specs.GroupScheme k)).mapIso i
  let j' := (Grp.forget (SchemeOver k)).mapIso j
  let j'' := (Over.forget (Spec (CommRingCat.of k))).mapIso j'
  let : Algebra.FiniteType k B.val := B.property
  obtain ⟨n, L, l, f, hf⟩ := spectrum_faithfulLinearization B.val
  refine ⟨n, L, l, j.inv ≫ f, ?_⟩
  change IsClosedImmersion (j''.inv ≫ f.hom.hom.left)
  exact @IsClosedImmersion.comp _ _ _ j''.inv f.hom.hom.left inferInstance hf

end
end LinearAlgebraicGroups
