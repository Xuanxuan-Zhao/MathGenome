import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Algebra.Field.ULift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Reductive.RadicalBaseChange

noncomputable section

noncomputable section

open MvPolynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

private theorem automorphism_of_adjoin {E : IntermediateField F K} [IsAlgClosed K]
    [Algebra.IsAlgebraic E K] (e : E ≃ₐ[F] E) :
    ∃ σ : K ≃ₐ[F] K, ∀ x : E, σ x = (e x : K) := by
  obtain ⟨f, hf⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := F) (L := E)
    (M := K) (E := K) ((IntermediateField.val E).comp e.toAlgHom)
  obtain ⟨g, hg⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := F) (L := E)
    (M := K) (E := K) ((IntermediateField.val E).comp e.symm.toAlgHom)
  have hfle (x : E) : f x = (e x : K) := DFunLike.congr_fun hf x
  have hgle (x : E) : g x = (e.symm x : K) := DFunLike.congr_fun hg x
  let fg : K →ₐ[E] K :=
    { (f.comp g).toRingHom with
      commutes' := fun x ↦ by change f (g (x : K)) = (x : K); rw [hgle, hfle]; simp }
  have hsurj : Function.Surjective f :=
    Function.Surjective.of_comp (Algebra.IsAlgebraic.algHom_bijective fg).2
  exact ⟨AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩, hfle⟩

private def translateVariable {ι : Type*} [DecidableEq ι] (i : ι) (c : F) :
    MvPolynomial ι F →ₐ[F] MvPolynomial ι F :=
  aeval fun j ↦ X j + if j = i then C c else 0

private theorem translateVariable_comp {ι : Type*} [DecidableEq ι] (i : ι) (c : F) :
    (translateVariable i c).comp (translateVariable i (-c)) =
      AlgHom.id F (MvPolynomial ι F) := by
  apply MvPolynomial.algHom_ext
  intro j
  by_cases h : j = i <;> simp [translateVariable, h]

private theorem translated_independent {ι : Type*} [DecidableEq ι] {x : ι → K}
    (hx : AlgebraicIndependent F x) (i : ι) :
    AlgebraicIndependent F (fun j ↦ x j + if j = i then 1 else 0) := by
  let e := AlgEquiv.ofAlgHom (translateVariable i (1 : F)) (translateVariable i (-1 : F))
    (translateVariable_comp i 1) (by simpa using translateVariable_comp i (-1 : F))
  rw [algebraicIndependent_iff_injective_aeval] at hx ⊢
  have he : (aeval x).comp e.toAlgHom = aeval (fun j ↦ x j + if j = i then 1 else 0) := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases h : j = i <;>
      simp [e, translateVariable, h, AlgEquiv.ofAlgHom_apply, aeval_X]
  rw [← he]
  exact hx.comp e.injective

set_option maxHeartbeats 1200000 in
private theorem fixed_field_of_algClosed [IsAlgClosed F] [IsAlgClosed K] (a : K)
    (h : ∀ σ : K ≃ₐ[F] K, σ a = a) : a ∈ Set.range (algebraMap F K) := by
  classical
  by_contra ha
  have ht : Transcendental F a := by
    intro halg
    exact ha (minpoly.natDegree_eq_one_iff.mp
      ((IsAlgClosed.splits (minpoly F a)).natDegree_eq_one_of_irreducible
        (minpoly.irreducible halg.isIntegral)))
  have hsingle : AlgebraicIndepOn F id ({a} : Set K) := by
    change AlgebraicIndependent F (fun x : ({a} : Set K) ↦ (x : K))
    rwa [algebraicIndependent_singleton_iff (⟨a, by simp⟩ : ({a} : Set K))]
  obtain ⟨s, has, hs⟩ := exists_isTranscendenceBasis_superset hsingle
  let x : s → K := Subtype.val
  let i : s := ⟨a, has (by simp)⟩
  let y : s → K := fun j ↦ x j + if j = i then 1 else 0
  have hy : AlgebraicIndependent F y := translated_independent hs.1 i
  let E := IntermediateField.adjoin F (Set.range x)
  let J := IntermediateField.adjoin F (Set.range y)
  have heq : J = E := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨j, rfl⟩
      have hj : x j ∈ E := IntermediateField.subset_adjoin F _ (Set.mem_range_self j)
      change y j ∈ E
      by_cases hji : j = i
      · simpa [y, hji] using E.add_mem hj E.one_mem
      · simpa [y, hji] using hj
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨j, rfl⟩
      have hj : y j ∈ J := IntermediateField.subset_adjoin F _ (Set.mem_range_self j)
      by_cases hji : j = i
      · have he : x j = y j - 1 := by simp [y, hji]
        rw [he]
        exact J.sub_mem hj (J.one_mem)
      · simpa [y, hji] using hj
  let e : E ≃ₐ[F] E :=
    hs.1.aevalEquivField.symm.trans (hy.aevalEquivField.trans (IntermediateField.equivOfEq heq))
  have : Algebra.IsAlgebraic E K :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mpr hs.isAlgebraic
  obtain ⟨σ, hσ⟩ := automorphism_of_adjoin e
  let p := algebraMap (MvPolynomial s F) (FractionRing (MvPolynomial s F)) (X i)
  have hx : (hs.1.aevalEquivField p : K) = a := by
    rw [hs.1.aevalEquivField_algebraMap_apply_coe, aeval_X]
  have hmove : σ a = a + 1 := by
    conv_lhs => rw [← hx, hσ]
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
      IntermediateField.equivOfEq_apply]
    change (hy.aevalEquivField p : K) = a + 1
    rw [hy.aevalEquivField_algebraMap_apply_coe, aeval_X]
    simp [y, x, i]
  exact one_ne_zero (add_left_cancel (hmove.symm.trans ((h σ).trans (add_zero a).symm)))

private theorem fixed_field_of_perfect [PerfectField F] (a : AlgebraicClosure F)
    (h : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ a = a) :
    a ∈ Set.range (algebraMap F (AlgebraicClosure F)) := by
  have : IsGalois F (AlgebraicClosure F) := {}
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed a).2 h
end

noncomputable section

open Module
open scoped TensorProduct

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

private def scalarAction (σ : K ≃ₐ[F] K) (V : Type*) [AddCommGroup V] [Module F V] :
    K ⊗[F] V →ₗ[F] K ⊗[F] V :=
  TensorProduct.map σ.toLinearMap LinearMap.id

private theorem scalarAction_smul {V : Type*} [AddCommGroup V] [Module F V]
    (σ : K ≃ₐ[F] K) (a : K) (x : K ⊗[F] V) :
    scalarAction σ V (a • x) = σ a • scalarAction σ V x := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    simp [scalarAction, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

private theorem span_includeRight {V : Type*} [AddCommGroup V] [Module F V] :
    Submodule.span K (Set.range (TensorProduct.mk F K V 1)) = ⊤ := by
  apply top_unique
  intro x _
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_range_self v))
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

private theorem stable_subspace_descends {V : Type*} [AddCommGroup V] [Module F V]
    (hfixed : ∀ a : K, (∀ σ : K ≃ₐ[F] K, σ a = a) → a ∈ Set.range (algebraMap F K))
    (U : Submodule K (K ⊗[F] V))
    (hstable : ∀ (σ : K ≃ₐ[F] K) x, x ∈ U → scalarAction σ V x ∈ U) :
    (U.restrictScalars F |>.comap (TensorProduct.mk F K V 1)).baseChange K = U := by
  classical
  let W := (K ⊗[F] V) ⧸ U
  let inc := TensorProduct.mk F K V 1
  let q : K ⊗[F] V →ₗ[K] W := U.mkQ
  let d := (q.restrictScalars F).comp inc
  have hspan : Submodule.span K (Set.range d) = ⊤ := by
    change Submodule.span K (Set.range (q ∘ inc)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, span_includeRight, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr U.mkQ_surjective
  let b := Basis.ofSpan hspan.ge
  have hb (j : _) : b j ∈ Set.range d :=
    Basis.ofSpan_subset hspan.ge (Set.mem_range_self j)
  choose v hv using hb
  let T := (U.restrictScalars F).comap inc
  let U₀ := T.baseChange K
  have hU₀ : U₀ ≤ U := by
    rw [show U₀ = T.baseChange K from rfl, Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  let actionQ (σ : K ≃ₐ[F] K) : W →ₗ[F] W :=
    (U.restrictScalars F).liftQ ((q.restrictScalars F).comp (scalarAction σ V)) <| by
      intro z hz
      exact (Submodule.Quotient.mk_eq_zero U).mpr (hstable σ z hz)
  have hactionQ (σ : K ≃ₐ[F] K) (z : K ⊗[F] V) :
      actionQ σ (q z) = q (scalarAction σ V z) := rfl
  have hfix (σ : K ≃ₐ[F] K) (z : V) : actionQ σ (d z) = d z := by
    change actionQ σ (q (1 ⊗ₜ[F] z)) = q (1 ⊗ₜ[F] z)
    rw [hactionQ]
    simp [scalarAction]
  have hsmul (σ : K ≃ₐ[F] K) (c : K) (w : W) :
      actionQ σ (c • w) = σ c • actionQ σ w := by
    obtain ⟨z, rfl⟩ := U.mkQ_surjective w
    change actionQ σ (c • q z) = σ c • actionQ σ (q z)
    rw [← map_smul, hactionQ, scalarAction_smul, map_smul, hactionQ]
  have hcoeff (z : V) (j : _) : b.repr (d z) j ∈ Set.range (algebraMap F K) := by
    apply hfixed
    intro σ
    let c := b.repr (d z)
    have hs : d z = c.sum (fun i a ↦ a • b i) := (b.linearCombination_repr (d z)).symm.trans
      (Finsupp.linearCombination_apply K c)
    have hleft : actionQ σ (d z) = ∑ i ∈ c.support, σ (c i) • b i := by
      conv_lhs => rw [hs]
      simp only [Finsupp.sum, map_sum, hsmul, ← hv, hfix]
    rw [hfix] at hleft
    have hh := congrArg (fun w : W => b.repr w j) hleft
    by_cases hj : j ∈ c.support
    · simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Basis.repr_self,
        smul_eq_mul, Finsupp.smul_single, mul_one, Finsupp.single_apply,
        Finset.sum_ite_eq', hj, ite_true] at hh
      exact hh.symm
    · have hz : c j = 0 := Finsupp.notMem_support_iff.mp hj
      change σ (c j) = c j
      simp [hz]
  choose coeff hcoeff using hcoeff
  let lift : W →ₗ[K] K ⊗[F] V := b.constr K (fun j ↦ inc (v j))
  have hlift (j : _) : lift (b j) = inc (v j) := b.constr_basis K _ j
  let projection := LinearMap.id - lift.comp q
  have hproj (z : V) : projection (inc z) ∈ U₀ := by
    let c := b.repr (d z)
    let z' := ∑ i ∈ c.support, coeff z i • v i
    have hl : lift (d z) = inc z' := by
      conv_lhs => rw [← b.linearCombination_repr (d z), Finsupp.linearCombination_apply]
      simp only [Finsupp.sum, map_sum, map_smul, hlift, z']
      apply Finset.sum_congr rfl
      intro j _
      rw [← hcoeff z j]
      exact algebraMap_smul K (coeff z j) (inc (v j))
    have hdz : d z = d z' := by
      have := congrArg q hl
      change q (lift (d z)) = d z' at this
      rw [← this]
      have hqid : q.comp lift = LinearMap.id := by
        apply b.ext
        intro j
        change q (lift (b j)) = b j
        rw [hlift]
        exact hv j
      exact (DFunLike.congr_fun hqid (d z)).symm
    have hmem : z - z' ∈ T := by
      change inc (z - z') ∈ U
      apply (Submodule.Quotient.mk_eq_zero U).mp
      change d (z - z') = 0
      rw [map_sub, hdz, sub_self]
    have hp : projection (inc z) = inc (z - z') := by
      change inc z - lift (d z) = inc (z - z')
      rw [hl, map_sub]
    rw [hp]
    change inc (z - z') ∈ T.baseChange K
    rw [Submodule.baseChange_eq_span, Submodule.map_coe]
    exact Submodule.subset_span (Set.mem_image_of_mem inc hmem)
  have hrange : LinearMap.range projection ≤ U₀ := by
    apply LinearMap.range_le_iff_comap.mpr
    apply top_unique
    apply (span_includeRight (F := F) (K := K) (V := V)).ge.trans
    exact Submodule.span_le.mpr (by rintro _ ⟨z, rfl⟩; exact hproj z)
  refine le_antisymm hU₀ ?_
  intro x hx
  refine hrange ⟨x, ?_⟩
  change x - lift (q x) = x
  have hqx : q x = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hx
  rw [hqx, map_zero, sub_zero]
end

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

open private tensorAlong tensorAlong_tmul tensorAlong_injective
  comparison_counit_base from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups
open private tensorQuotient_ker from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem extended_ideal_comap (A : HopfAlgebraCategory k) (I : Ideal A) :
    (Specs.extendedIdeal K I).comap
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) = I := by
  unfold Specs.extendedIdeal
  rw [← tensorQuotient_ker (k := k) (K := K) I]
  ext x
  change (Algebra.TensorProduct.map (AlgHom.id k K) (Ideal.Quotient.mkₐ k I))
    (1 ⊗ₜ[k] x) = 0 ↔ x ∈ I
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change (Algebra.TensorProduct.includeRight : A ⧸ I →ₐ[k] K ⊗[k] (A ⧸ I))
    (Ideal.Quotient.mk I x) = 0 ↔ x ∈ I
  rw [← map_zero (Algebra.TensorProduct.includeRight : A ⧸ I →ₐ[k] K ⊗[k] (A ⧸ I)),
    (Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective).eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

set_option maxHeartbeats 800000 in
private theorem hopf_ideal_of_extension (A : HopfAlgebraCategory k) (I : Ideal A)
    [hI : (Specs.extendedIdeal K I).IsHopfIdeal K] : I.IsHopfIdeal k := by
  let E := extendedHopf K A
  let J := Specs.extendedIdeal K I
  have hJ : J.IsHopfIdeal K := hI
  let B := hopfQuotient E J
  let q : E →ₐ[K] B := (hopfQuotientMap E J).hom.toAlgHom
  let i : A →ₐ[k] E := Algebra.TensorProduct.includeRight
  let Q := A ⧸ I
  let p : A →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  let j : Q →ₐ[k] B := Ideal.Quotient.liftₐ I ((q.restrictScalars k).comp i)
    (fun x hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem i hx))
  have hji (x : A) : j (p x) = q (i x) := rfl
  let lift : K ⊗[k] Q →ₐ[K] B := (AlgHom.liftEquiv k K Q B) j
  let pK : E →ₐ[k] K ⊗[k] Q := Algebra.TensorProduct.map (AlgHom.id k K) p
  have hcomp : (lift.restrictScalars k).comp pK = (q.restrictScalars k) := by
    apply Algebra.TensorProduct.ext
    · ext r
      change lift (r ⊗ₜ[k] p 1) = q (r ⊗ₜ[k] (1 : A))
      rw [map_one]
      exact (lift.commutes r).trans (q.commutes r).symm
    · ext x
      change lift (1 ⊗ₜ[k] p x) = q (i x)
      change (1 : K) • j (p x) = q (i x)
      simpa only [one_smul] using hji x
  have hlift : Function.Injective (j.toLinearMap.liftBaseChange K) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro b hb
    have hs : Function.Surjective pK := Algebra.TensorProduct.map_surjective
      (AlgHom.id k K) p Function.surjective_id Ideal.Quotient.mk_surjective
    obtain ⟨a, rfl⟩ := hs b
    have hq : q a = 0 := (DFunLike.congr_fun hcomp a).symm.trans hb
    have ha : a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hq
    exact (show a ∈ RingHom.ker pK from (tensorQuotient_ker (k := k) (K := K) I).symm ▸ ha)
  rw [Ideal.isHopfIdeal_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    have hx' : i x ∈ J := Ideal.mem_map_of_mem i hx
    have h := Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars K) hx'
    change counit (R := K) (1 ⊗ₜ[k] x : K ⊗[k] A) = 0 at h
    rw [comparison_counit_base] at h
    exact (algebraMap k K).injective (h.trans (map_zero _).symm)
  · intro x hx
    have hx' : i x ∈ J := Ideal.mem_map_of_mem i hx
    have h := Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := J.restrictScalars K) hx'
    have h' : Algebra.TensorProduct.map q q (comul (R := K) (1 ⊗ₜ[k] x)) = 0 := h
    have hcomul : Algebra.TensorProduct.map q q (comul (R := K) (1 ⊗ₜ[k] x)) =
        tensorAlong (K := K) ((q.restrictScalars k).comp i)
          ((q.restrictScalars k).comp i) (comul (R := k) x) := by
      rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
      generalize comul (R := k) x = t
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          Algebra.TensorProduct.map_tmul, tensorAlong_tmul, AlgHom.comp_apply,
          AlgHom.restrictScalars_apply, i]
        rfl
      | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    rw [hcomul] at h'
    change TensorProduct.map p.toLinearMap p.toLinearMap (comul (R := k) x) = 0
    apply tensorAlong_injective j j hlift hlift
    rw [map_zero, ← h']
    have he : (tensorAlong (K := K) j j).toLinearMap.comp
        (TensorProduct.map p.toLinearMap p.toLinearMap) =
        (tensorAlong (K := K) ((q.restrictScalars k).comp i)
          ((q.restrictScalars k).comp i)).toLinearMap := by
      ext a b
      simp [tensorAlong_tmul, hji]
    exact DFunLike.congr_fun he (comul (R := k) x)
  · intro x hx
    have h := Ideal.IsHopfIdeal.antipode_mem (R := K) (I := J) (Ideal.mem_map_of_mem i hx : i x ∈ J)
    change antipode K (1 ⊗ₜ[k] x : K ⊗[k] A) ∈ J at h
    rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
      HopfAlgebra.antipode_one] at h
    rw [← extended_ideal_comap (K := K) A I]
    exact h


end

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Specs.GeometricRadicals (IsSmoothConnectedNormal IsTrivialSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup IsUnipotent)

open private factor_of_baseChange baseChangeProjection_naturality
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
open private geometricallyConnected_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isMonHom_of_factor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private abbrev fpqc : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact

private theorem fieldSpecMap_fpqc : fpqc (fieldSpecMap k K) := by
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap k K))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  exact ⟨⟨hsurj, hflat⟩, inferInstanceAs (QuasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))⟩

private theorem smooth_baseChange_iff (X : SchemeOver k) :
    Smooth ((baseChange k K).obj X).hom ↔ Smooth X.hom :=
  MorphismProperty.pullback_snd_iff (P := @Smooth)
    (fieldSpecMap_fpqc (k := k) (K := K))

private theorem connected_baseChange_iff (G : AffineAlgebraicGroup k) :
    ConnectedSpace (baseChangedAlgebraicGroup K G).val.X.left ↔ ConnectedSpace G.val.X.left := by
  constructor
  · intro h
    have : Surjective (fieldSpecMap k K) := (fieldSpecMap_fpqc (k := k) (K := K)).1.1
    have : ConnectedSpace ↥(pullback G.val.X.hom (fieldSpecMap k K)) := h
    exact (pullback.fst G.val.X.hom (fieldSpecMap k K)).surjective.connectedSpace
      (pullback.fst G.val.X.hom (fieldSpecMap k K)).continuous
  · intro h
    exact (geometricallyConnected_of_connected G).geometrically_connectedSpace _ _ _
      (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K))

private def extendSubgroup (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (N : ClosedSubgroup G) : ClosedSubgroup ((groupBaseChange k K).obj G) :=
  Specs.GeometricRadicals.baseChangedSubgroup K N
    (baseChangeClosedSubgroup k K N.inclusion N.isClosedImmersion)

private theorem subgroup_baseChange_iff {G : GroupScheme k} (H N : ClosedSubgroup G) :
    IsSubgroupOf (extendSubgroup K H) (extendSubgroup K N) ↔ IsSubgroupOf H N := by
  constructor
  · rintro ⟨j, hj⟩
    have hN := N.isClosedImmersion
    have : Mono N.inclusion.hom.hom.left := inferInstance
    have : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
    obtain ⟨i, hi⟩ := factor_of_baseChange K H.inclusion.hom.hom N.inclusion.hom.hom
      j.hom.hom (congrArg (Grp.forget (SchemeOver K)).map hj)
    have := isMonHom_of_factor H.inclusion N.inclusion i hi
    exact ⟨Grp.homMk i, Grp.hom_ext _ _ hi⟩
  · rintro ⟨j, hj⟩
    exact ⟨(groupBaseChange k K).map j, by
      change (groupBaseChange k K).map j ≫ (groupBaseChange k K).map N.inclusion =
        (groupBaseChange k K).map H.inclusion
      rw [← Functor.map_comp, hj]⟩

private theorem eligible_baseChange_iff {G : AffineAlgebraicGroup k} (H : ClosedSubgroup G.val) :
    IsSmoothConnectedNormal (G := baseChangedAlgebraicGroup K G) (extendSubgroup K H) ↔
      IsSmoothConnectedNormal H :=
  and_congr (smooth_baseChange_iff H.group.X)
    (and_congr (connected_baseChange_iff (closedSubgroupAlgebraicGroup H))
      (baseChangeNormalSubgroupIff k K H.inclusion H.isClosedImmersion))

private theorem trivial_baseChange_iff (G : GroupScheme k) :
    Nonempty ((groupBaseChange k K).obj G ≅ Grp.trivial (SchemeOver K)) ↔
      Nonempty (G ≅ Grp.trivial (SchemeOver k)) := by
  have ht (E : Type u) [Field E] (H : GroupScheme E) :
      Nonempty (H ≅ Grp.trivial (SchemeOver E)) ↔ IsIso H.X.hom := by
    constructor
    · rintro ⟨e⟩
      have h : IsIso e.hom.hom.hom.left :=
        (Grp.forget (SchemeOver E) ⋙ Over.forget _).map_isIso e.hom
      have he := Over.w e.hom.hom.hom
      change _ ≫ 𝟙 _ = _ at he
      rw [Category.comp_id] at he
      exact he ▸ h
    · intro h
      let e : H ⟶ Grp.trivial (SchemeOver E) := default
      have he := Over.w e.hom.hom
      change _ ≫ 𝟙 _ = _ at he
      rw [Category.comp_id] at he
      have hh : IsIso e.hom.hom.left := he.symm ▸ h
      have := isIso_of_schemeIso e
      exact ⟨asIso e⟩
  rw [ht, ht]
  change IsIso (pullback.snd G.X.hom (fieldSpecMap k K)) ↔ IsIso G.X.hom
  exact MorphismProperty.pullback_snd_iff (P := MorphismProperty.isomorphisms Scheme.{u})
    (fieldSpecMap_fpqc (k := k) (K := K))

private def groupBaseChangeTower (L : Type u) [Field L] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] : groupBaseChange k L ≅ groupBaseChange k K ⋙ groupBaseChange K L := by
  have h : fieldSpecMap K L ≫ fieldSpecMap k K = fieldSpecMap k L := by
    change Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq k K L).symm
  let e : baseChange k L ≅ baseChange k K ⋙ baseChange K L :=
    eqToIso (congrArg (fun f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) ↦
      Over.pullback f) h.symm) ≪≫ Over.pullbackComp _ _
  exact Functor.mapGrpNatIso e ≪≫ Functor.mapGrpCompIso

end
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Specs.GeometricRadicals (IsRadical IsSmoothConnectedNormal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup IsUnipotent)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private def transportSubgroup {G G' : GroupScheme k} (e : G ≅ G') (N : ClosedSubgroup G) :
    ClosedSubgroup G' := by
  have hi := N.isClosedImmersion
  have he : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
  exact ⟨N.group, N.inclusion ≫ e.hom, IsClosedImmersion.comp _ _⟩

open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient

private theorem transport_normal {G G' : GroupScheme k} (e : G ≅ G') (N : ClosedSubgroup G)
    (hN : IsNormalSubgroup N.inclusion) : IsNormalSubgroup (transportSubgroup e N).inclusion :=
  normalSubgroup_of_iso e.symm (Iso.refl _) (by
    change (N.inclusion ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ N.inclusion
    simp) hN

private theorem radical_transport {G G' : AffineAlgebraicGroup k} (e : G.val ≅ G'.val)
    (P : AffineAlgebraicGroup k → Prop) (hP : ∀ {H : ClosedSubgroup G.val} {J : ClosedSubgroup G'.val},
      (H.group ≅ J.group) → IsSmoothConnectedNormal H → IsSmoothConnectedNormal J →
        (P (closedSubgroupAlgebraicGroup H) ↔ P (closedSubgroupAlgebraicGroup J))) (N : ClosedSubgroup G.val) (hN : IsRadical G P N) :
    IsRadical G' P (transportSubgroup e N) := by
  have ht : IsSmoothConnectedNormal (transportSubgroup e N) :=
    ⟨hN.1.1, hN.1.2.1, transport_normal e N hN.1.2.2⟩
  refine ⟨ht, (hP (Iso.refl _) hN.1 ht).mp hN.2.1, ?_⟩
  intro H hH hHP
  let H' := transportSubgroup e.symm H
  have hH' : IsSmoothConnectedNormal H' :=
    ⟨hH.1, hH.2.1, transport_normal e.symm H hH.2.2⟩
  obtain ⟨j, hj⟩ := hN.2.2 H' hH' ((hP (Iso.refl _) hH' hH).mpr hHP)
  refine ⟨j, ?_⟩
  change j ≫ (N.inclusion ≫ e.hom) = H.inclusion
  rw [← Category.assoc, hj]
  change (H.inclusion ≫ e.inv) ≫ e.hom = H.inclusion
  simp

private theorem smoothConnectedNormal_inclusionIso {G : AffineAlgebraicGroup k}
    {M N : ClosedSubgroup G.val} (e : M.group ≅ N.group)
    (he : e.hom ≫ N.inclusion = M.inclusion) :
    IsSmoothConnectedNormal M ↔ IsSmoothConnectedNormal N := by
  have hforward {X Y : ClosedSubgroup G.val} (d : X.group ≅ Y.group)
      (hd : d.hom ≫ Y.inclusion = X.inclusion) :
      IsSmoothConnectedNormal Y → IsSmoothConnectedNormal X := by
    rintro ⟨hs, hc, hn⟩
    let f := d.hom.hom.hom.left
    have : IsIso f := (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso d.hom
    have : Smooth f := inferInstance
    have hcomp : Smooth (f ≫ Y.group.X.hom) := inferInstance
    have hsm : Smooth X.group.X.hom := (Over.w d.hom.hom.hom) ▸ hcomp
    exact ⟨hsm, f.homeomorph.connectedSpace_iff.mpr hc,
      normalSubgroup_of_iso (Iso.refl _) d (by simpa using hd.symm) hn⟩
  exact ⟨hforward e.symm (by
    change e.inv ≫ M.inclusion = N.inclusion
    rw [← he, Iso.inv_hom_id_assoc]), hforward e he⟩

private theorem radical_of_extended_radical {G : AffineAlgebraicGroup k}
    {P : AffineAlgebraicGroup k → Prop} {Q : AffineAlgebraicGroup K → Prop}
    (hP : ∀ M : ClosedSubgroup G.val, IsSmoothConnectedNormal M →
      (Q (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K G) (extendSubgroup K M)) ↔
        P (closedSubgroupAlgebraicGroup M)))
    (hQ : ∀ {X Y : ClosedSubgroup (baseChangedAlgebraicGroup K G).val},
      (X.group ≅ Y.group) → IsSmoothConnectedNormal X → IsSmoothConnectedNormal Y →
        (Q (closedSubgroupAlgebraicGroup X) ↔ Q (closedSubgroupAlgebraicGroup Y)))
    {M : ClosedSubgroup G.val} {N : ClosedSubgroup (baseChangedAlgebraicGroup K G).val}
    (hN : IsRadical (baseChangedAlgebraicGroup K G) Q N)
    (e : (extendSubgroup K M).group ≅ N.group)
    (he : e.hom ≫ N.inclusion = (extendSubgroup K M).inclusion) :
    IsRadical G P M := by
  have hm := (smoothConnectedNormal_inclusionIso
    (G := baseChangedAlgebraicGroup K G) e he).mpr hN.1
  have hmq := (hQ e hm hN.1).mpr hN.2.1
  have hm' := (eligible_baseChange_iff M).mp hm
  refine ⟨hm', (hP M hm').mp hmq, ?_⟩
  intro H hH hPH
  obtain ⟨j, hj⟩ := hN.2.2 (extendSubgroup K H) ((eligible_baseChange_iff H).mpr hH)
    ((hP H hH).mpr hPH)
  apply (subgroup_baseChange_iff (K := K) H M).mp
  refine ⟨j ≫ e.inv, ?_⟩
  rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, hj]

set_option maxHeartbeats 600000 in
private theorem radical_baseChange_of_descent {G : AffineAlgebraicGroup k}
    {P : AffineAlgebraicGroup k → Prop} {Q : AffineAlgebraicGroup K → Prop}
    (hP : ∀ M : ClosedSubgroup G.val, IsSmoothConnectedNormal M →
      (Q (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K G) (extendSubgroup K M)) ↔
        P (closedSubgroupAlgebraicGroup M)))
    (hQ : ∀ {X Y : ClosedSubgroup (baseChangedAlgebraicGroup K G).val},
      (X.group ≅ Y.group) → IsSmoothConnectedNormal X → IsSmoothConnectedNormal Y →
        (Q (closedSubgroupAlgebraicGroup X) ↔ Q (closedSubgroupAlgebraicGroup Y)))
    {M R : ClosedSubgroup G.val} {N : ClosedSubgroup (baseChangedAlgebraicGroup K G).val}
    (hN : IsRadical (baseChangedAlgebraicGroup K G) Q N)
    (e : (extendSubgroup K M).group ≅ N.group)
    (he : e.hom ≫ N.inclusion = (extendSubgroup K M).inclusion)
    (hR : IsRadical G P R) :
    IsRadical (baseChangedAlgebraicGroup K G) Q (extendSubgroup K R) := by
  have hm := radical_of_extended_radical hP hQ hN e he
  obtain ⟨d, hd, _⟩ := GeometricRadicals.radicalUnique G P hR hm
  let c := (groupBaseChange k K).mapIso d ≪≫ e
  have hc : c.hom ≫ N.inclusion = (extendSubgroup K R).inclusion := by
    change ((groupBaseChange k K).map d.hom ≫ e.hom) ≫ N.inclusion = _
    rw [Category.assoc, he]
    change (groupBaseChange k K).map d.hom ≫ (groupBaseChange k K).map M.inclusion = _
    rw [← Functor.map_comp, hd]
    rfl
  have hR' := (smoothConnectedNormal_inclusionIso
    (G := baseChangedAlgebraicGroup K G) (M := extendSubgroup K R) c hc).mpr hN.1
  refine ⟨hR', (hQ c hR' hN.1).mpr hN.2.1, ?_⟩
  intro H hH hQH
  obtain ⟨j, hj⟩ := hN.2.2 H hH hQH
  exact ⟨j ≫ c.inv, by rw [Category.assoc, ← hc, Iso.inv_hom_id_assoc, hj]⟩

private theorem unipotent_of_iso {G H : AffineAlgebraicGroup k} (e : G.val ≅ H.val) :
    IsUnipotent G ↔ IsUnipotent H := by
  constructor
  · rintro ⟨A, ⟨d⟩, hA⟩
    exact ⟨A, ⟨d ≪≫ e⟩, hA⟩
  · rintro ⟨A, ⟨d⟩, hA⟩
    exact ⟨A, ⟨d ≪≫ e.symm⟩, hA⟩

private theorem unipotent_subgroup_baseChange_iff {G : AffineAlgebraicGroup k} (H : ClosedSubgroup G.val) :
    IsUnipotent (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K G)
      (extendSubgroup K H)) ↔ IsUnipotent (closedSubgroupAlgebraicGroup H) :=
  Unipotent.unipotenceFieldExtension (closedSubgroupAlgebraicGroup H)


end

section IdealDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem stable_hopf_ideal_descends (A : HopfAlgebraCategory k)
    (J : Ideal (extendedHopf K A)) [J.IsHopfIdeal K]
    (hfixed : ∀ a : K, (∀ σ : K ≃ₐ[k] K, σ a = a) → a ∈ Set.range (algebraMap k K))
    (hstable : ∀ (σ : K ≃ₐ[k] K) x, x ∈ J → scalarAction σ A x ∈ J) :
    ∃ I : Ideal A, I.IsHopfIdeal k ∧ Specs.extendedIdeal K I = J := by
  let I : Ideal A := J.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
  have h : (I.restrictScalars k).baseChange K = J.restrictScalars K :=
    stable_subspace_descends hfixed (J.restrictScalars K) hstable
  have hI : Specs.extendedIdeal K I = J := by
    apply Submodule.restrictScalars_injective K _ _
    rw [← h]
    exact (TensorProduct.AlgebraTensorModule.range_lTensor_idealMap K K I).symm
  have : (Specs.extendedIdeal K I).IsHopfIdeal K := hI.symm ▸ inferInstance
  exact ⟨I, hopf_ideal_of_extension (K := K) A I, hI⟩

end IdealDescent

section Solvability

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.FiniteWordClosure (wordDomain evaluate)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup IsNormalClosure FactorsThrough IsSubgroupOf DerivedSeries
  IsSolvable commutatorMap)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

open private baseChangeProjection_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private commutatorWordClosure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private affine_tensor affine_power ker_comp_eq liftClosed liftClosed_fac
  isMonHom_of_factor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem baseChange_commutator {G : GroupScheme k} :
    let F := baseChange k K
    (prodComparisonIso F G.X G.X).inv ≫ F.map (commutatorMap (𝟙 G) (𝟙 G)) =
      commutatorMap (𝟙 ((groupBaseChange k K).obj G)) (𝟙 ((groupBaseChange k K).obj G)) := by
  let F := baseChange k K
  let e := prodComparisonIso F G.X G.X
  change e.inv ≫ F.map (commutatorMap (𝟙 G) (𝟙 G)) = _
  have he₁ : e.inv ≫ F.map (fst G.X G.X) = fst (F.obj G.X) (F.obj G.X) := by
    rw [← CartesianMonoidalCategory.prodComparison_fst, ← prodComparisonIso_hom,
      Iso.inv_hom_id_assoc]
  have he₂ : e.inv ≫ F.map (snd G.X G.X) = snd (F.obj G.X) (F.obj G.X) := by
    rw [← CartesianMonoidalCategory.prodComparison_snd, ← prodComparisonIso_hom,
      Iso.inv_hom_id_assoc]
  unfold commutatorMap
  simp only [Grp.id_hom_hom, Category.comp_id, F.map_mul, F.map_inv',
    MonObj.comp_mul, GrpObj.comp_inv, he₁, he₂]
  rfl

private theorem evaluate_factors_after_baseChange {G : GroupScheme k} {X : SchemeOver k}
    (f : X ⟶ G.X) (N : ClosedSubgroup ((groupBaseChange k K).obj G))
    (t : (baseChange k K).obj X ⟶ N.group.X)
    (ht : t ≫ N.inclusion.hom.hom = (baseChange k K).map f)
    (n : ℕ) {T : SchemeOver k} (p : T ⟶ wordDomain X n) :
    FactorsThrough N ((baseChange k K).map (evaluate f n p)) := by
  let F := baseChange k K
  induction n with
  | zero =>
    change FactorsThrough N (F.map 1)
    rw [F.map_one]
    exact (Specs.SubgroupSections N (F.obj T)).one_mem
  | succ n ih =>
    have hf (r : T ⟶ X) : FactorsThrough N (F.map (r ≫ f)) := by
      refine ⟨F.map r ≫ t, ?_⟩
      change (F.map r ≫ t) ≫ N.inclusion.hom.hom = F.map (r ≫ f)
      rw [Category.assoc, ht, F.map_comp]
    change F.map (evaluate f (n + 1) p) ∈ Specs.SubgroupSections N (F.obj T)
    simp only [evaluate, F.map_mul, F.map_inv']
    exact (Specs.SubgroupSections N _).mul_mem
      ((Specs.SubgroupSections N _).mul_mem (hf _)
        ((Specs.SubgroupSections N _).inv_mem (hf _))) (ih _)

private theorem baseChange_dominant {X Y : SchemeOver k} (f : X ⟶ Y)
    [QuasiCompact f.left] [IsSchemeTheoreticallyDominant f.left] :
    IsSchemeTheoreticallyDominant ((baseChange k K).map f).left := by
  have : Flat (fieldSpecMap k K) := (fieldSpecMap_fpqc (k := k) (K := K)).1.2
  have : Flat (pullback.fst Y.hom (fieldSpecMap k K)) := by infer_instance
  have h : IsPullback (pullback.fst X.hom (fieldSpecMap k K)) ((baseChange k K).map f).left
      f.left (pullback.fst Y.hom (fieldSpecMap k K)) := by
    apply IsPullback.flip
    refine IsPullback.of_right ?_ (baseChangeProjection_naturality K f)
      (IsPullback.of_hasPullback Y.hom (fieldSpecMap k K)).flip
    have hw := Over.w ((baseChange k K).map f)
    change ((baseChange k K).map f).left ≫ pullback.snd Y.hom (fieldSpecMap k K) =
      pullback.snd X.hom (fieldSpecMap k K) at hw
    rw [hw, Over.w f]
    exact (IsPullback.of_hasPullback X.hom (fieldSpecMap k K)).flip
  exact IsSchemeTheoreticallyDominant.of_isPullback h

private theorem baseChange_derived [PerfectField k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (D : ClosedSubgroup G.val) (hD : IsDerivedSubgroup D) :
    IsDerivedSubgroup (extendSubgroup K D) := by
  let f := commutatorMap (𝟙 G.val) (𝟙 G.val)
  let F := baseChange k K
  let e := prodComparisonIso F G.val.X G.val.X
  refine ⟨baseChangeNormalSubgroup k K D.inclusion hD.1, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hD.2.1
    change t ≫ D.inclusion.hom.hom = f at ht
    refine ⟨e.inv ≫ F.map t, ?_⟩
    change (e.inv ≫ F.map t) ≫ F.map D.inclusion.hom.hom = _
    rw [Category.assoc, ← F.map_comp, ht]
    exact baseChange_commutator
  · intro N _ hN
    obtain ⟨t, ht⟩ := hN
    have ht' : (e.hom ≫ t) ≫ N.inclusion.hom.hom = F.map f := by
      change t ≫ N.inclusion.hom.hom = _ at ht
      rw [Category.assoc, ht, ← baseChange_commutator (K := K) (G := G.val)]
      exact e.hom_inv_id_assoc _
    have hn : IsNormalSubgroup (𝟙 G.val) :=
      ⟨Specs.subgroupConjugation (𝟙 G.val), by simp⟩
    obtain ⟨n, w, ha, _, hdom, _, hw⟩ := commutatorWordClosure G G (𝟙 G.val) hn hs hc hs hc hD
    have hg : IsAffine D.group.X.left := (closedSubgroupAlgebraicGroup D).property.1
    have hqc : QuasiCompact w.left := inferInstance
    have hwd : IsSchemeTheoreticallyDominant (F.map w).left := baseChange_dominant w
    have hw' := hw _ (𝟙 _)
    simp only [Category.id_comp] at hw'
    obtain ⟨a, ha⟩ := evaluate_factors_after_baseChange f N (e.hom ≫ t) ht' n (𝟙 _)
    change a ≫ N.inclusion.hom.hom = F.map (evaluate f n (𝟙 _)) at ha
    rw [← hw', F.map_comp] at ha
    have hker : N.inclusion.hom.hom.left.ker ≤
        (extendSubgroup K D).inclusion.hom.hom.left.ker := by
      have hle := a.left.le_ker_comp N.inclusion.hom.hom.left
      rw [← Over.comp_left, ha, ker_comp_eq (F.map w) (F.map D.inclusion.hom.hom)] at hle
      exact hle
    have hi : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
    let j := liftClosed N.inclusion.hom.hom (extendSubgroup K D).inclusion.hom.hom hker
    have hj := liftClosed_fac N.inclusion.hom.hom (extendSubgroup K D).inclusion.hom.hom hker
    have hm : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
    have hmon := isMonHom_of_factor (extendSubgroup K D).inclusion N.inclusion j hj
    exact ⟨Grp.homMk j, Grp.hom_ext _ _ hj⟩


open private derivedSeries_sections rationalSections rationalMap solvable_iff_sections
  trivial_of_subsingleton_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

private theorem baseChange_derivedSeries [PerfectField k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    {n : ℕ} {H : GroupScheme k} (h : DerivedSeries G.val n H) :
    (∃ J : AffineAlgebraicGroup k, J.val = H) ∧
      Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
      DerivedSeries (baseChangedAlgebraicGroup K G).val n ((groupBaseChange k K).obj H) := by
  induction h with
  | zero => exact ⟨⟨G, rfl⟩, hs, hc, DerivedSeries.zero⟩
  | @succ n H prev D hD ih =>
    obtain ⟨⟨J, hJ⟩, hsm, hconn, hseries⟩ := ih
    subst H
    have hn : IsNormalSubgroup (𝟙 J.val) := ⟨Specs.subgroupConjugation (𝟙 J.val), by simp⟩
    obtain ⟨_, _, _, _, _, hdsm, _⟩ :=
      commutatorWordClosure J J (𝟙 J.val) hn hsm hconn hsm hconn hD
    have hdc := SchemeDerivedGroup.derivedSubgroup_connected J D hD
    exact ⟨⟨closedSubgroupAlgebraicGroup D, rfl⟩, hdsm, hdc,
      DerivedSeries.succ hseries (extendSubgroup K D) (baseChange_derived J hsm hconn D hD)⟩

private theorem solvable_baseChange_iff [PerfectField k] [IsAlgClosed K]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    IsSolvable (baseChangedAlgebraicGroup K G).val ↔ IsSolvable G.val := by
  let W := baseChangedAlgebraicGroup K G
  have hWs : Smooth W.val.X.hom := (smooth_baseChange_iff G.val.X).mpr hs
  have hWc : ConnectedSpace W.val.X.left := (connected_baseChange_iff G).mpr hc
  constructor
  · rintro ⟨n, T, hT, ⟨e⟩⟩
    obtain ⟨i, _, _, _, hr⟩ := derivedSeries_sections W hWs hWc hT
    have hn : derivedSeries (rationalSections W.val) n = ⊥ := by
      rw [← hr]
      apply bot_unique
      rintro _ ⟨p, rfl⟩
      rw [Subgroup.mem_bot, ← (rationalMap i).map_one]
      congr 1
      exact (cancel_mono e.hom.hom.hom).mp
        ((isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _)
    obtain ⟨J, hJ⟩ := SchemeDerivedGroup.derivedSeriesExists G n
    obtain ⟨_, _, _, hJK⟩ := baseChange_derivedSeries (K := K) G hs hc hJ
    obtain ⟨j, hj, hsm, _, him⟩ := derivedSeries_sections W hWs hWc hJK
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    let J' := baseChangedAlgebraicGroup K J
    have hp (p : rationalSections J'.val) : rationalMap j p = 1 :=
      Subgroup.mem_bot.mp ((him.trans hn) ▸ (show rationalMap j p ∈ (rationalMap j).range
        from ⟨p, rfl⟩))
    have : Subsingleton (rationalSections J'.val) :=
      ⟨fun p q ↦ (cancel_mono j.hom.hom).mp ((hp p).trans (hp q).symm)⟩
    exact ⟨n, J.val, hJ, (trivial_baseChange_iff J.val).mp
      (trivial_of_subsingleton_sections J' hsm)⟩
  · rintro ⟨n, H, hH, he⟩
    have hd := (baseChange_derivedSeries (K := K) G hs hc hH).2.2.2
    exact ⟨n, _, hd, (trivial_baseChange_iff H).mpr he⟩

private theorem solvable_of_iso [IsAlgClosed k] {G H : AffineAlgebraicGroup k}
    (e : G.val ≅ H.val) (hsG : Smooth G.val.X.hom) (hcG : ConnectedSpace G.val.X.left)
    (hsH : Smooth H.val.X.hom) (hcH : ConnectedSpace H.val.X.left) :
    IsSolvable G.val ↔ IsSolvable H.val := by
  rw [solvable_iff_sections G hsG hcG, solvable_iff_sections H hsH hcH]
  have hs {X Y : AffineAlgebraicGroup k} (d : X.val ≅ Y.val)
      (h : Group.IsSolvable (rationalSections X.val)) :
      Group.IsSolvable (rationalSections Y.val) := by
    apply Group.isSolvable_of_surjective (f := rationalMap d.hom)
    intro p
    refine ⟨p ≫ d.inv.hom.hom, ?_⟩
    change (p ≫ d.inv.hom.hom) ≫ d.hom.hom.hom = p
    exact (Category.assoc _ _ _).trans (by rw [← Grp.comp_hom_hom, d.inv_hom_id]; simp)
  exact ⟨hs (X := G) (Y := H) e, hs (X := H) (Y := G) e.symm⟩

end Solvability


section AlgebraicClosureComparison

open Specs.GeometricRadicals (IsRadical IsSmoothConnectedNormal GeometricGroup)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

set_option backward.isDefEq.respectTransparency false

private theorem radical_trivial_of_fieldExtension {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom)
    (hc : GeometricallyConnected G.val.X.hom)
    (P : ∀ {F : Type u} [Field F], AffineAlgebraicGroup F → Prop)
    (hiso : ∀ {F : Type u} [Field F] [IsAlgClosed F] {X Y : AffineAlgebraicGroup F},
      (X.val ≅ Y.val) →
      Smooth X.val.X.hom → ConnectedSpace X.val.X.left →
      Smooth Y.val.X.hom → ConnectedSpace Y.val.X.left → (P X ↔ P Y))
    (hBC : ∀ {F L : Type u} [Field F] [Field L] [Algebra F L]
      [IsAlgClosed F] [IsAlgClosed L] (X : AffineAlgebraicGroup F),
      Smooth X.val.X.hom → GeometricallyConnected X.val.X.hom →
      ∀ (N : ClosedSubgroup X.val), IsRadical X P N →
        IsRadical (baseChangedAlgebraicGroup L X) P (extendSubgroup L N))
    {N : ClosedSubgroup (GeometricGroup G).val}
    {M : ClosedSubgroup (GeometricGroup (baseChangedAlgebraicGroup K G)).val}
    (hN : IsRadical (GeometricGroup G) P N)
    (hM : IsRadical (GeometricGroup (baseChangedAlgebraicGroup K G)) P M) :
    Nonempty (M.group ≅ Grp.trivial (SchemeOver (AlgebraicClosure K))) ↔
      Nonempty (N.group ≅ Grp.trivial (SchemeOver (AlgebraicClosure k))) := by
  let F := AlgebraicClosure k
  let L := AlgebraicClosure K
  let f : F →ₐ[k] L := IsAlgClosed.lift
  let : Algebra F L := f.toRingHom.toAlgebra
  have : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (f.commutes a).symm)
  let X := GeometricGroup G
  let XL := baseChangedAlgebraicGroup L X
  let Y := GeometricGroup (baseChangedAlgebraicGroup K G)
  have hXs : Smooth X.val.X.hom := (smooth_baseChange_iff G.val.X).mpr hs
  have hXc : GeometricallyConnected X.val.X.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k F)) hc
  have hNL := hBC (L := L) X hXs hXc N hN
  let e : XL.val ≅ Y.val := ((groupBaseChangeTower (K := F) L).app G.val).symm ≪≫
    (groupBaseChangeTower (K := K) L).app G.val
  have ht := radical_transport e P
    (fun d hX hY ↦ hiso d hX.1 hX.2.1 hY.1 hY.2.1)
    (extendSubgroup L N) hNL
  obtain ⟨d, _, _⟩ := GeometricRadicals.radicalUnique Y P hM ht
  exact ⟨fun ⟨q⟩ ↦ (trivial_baseChange_iff (K := L) N.group).mp ⟨d.symm ≪≫ q⟩,
    fun h ↦ let ⟨q⟩ := (trivial_baseChange_iff (K := L) N.group).mpr h
      ⟨d ≪≫ q⟩⟩

end AlgebraicClosureComparison


section FieldAutomorphism

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.GeometricRadicals (IsRadical IsSmoothConnectedNormal)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup IsUnipotent)

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private def fieldAutomorphismSpec (σ : K ≃ₐ[k] K) :
    Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of K) where
  hom := Spec.map (CommRingCat.ofHom σ.toRingHom)
  inv := Spec.map (CommRingCat.ofHom σ.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]
    congr 2
    ext x
    exact σ.apply_symm_apply x
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]
    congr 2
    ext x
    exact σ.symm_apply_apply x

private abbrev twist (σ : K ≃ₐ[k] K) : SchemeOver K ⥤ SchemeOver K :=
  Over.pullback (fieldAutomorphismSpec σ).hom

private def twistAffineGroup (σ : K ≃ₐ[k] K) (G : AffineAlgebraicGroup K) :
    AffineAlgebraicGroup K := by
  let g := (fieldAutomorphismSpec σ).hom
  have : IsAffine G.val.X.left := G.property.1
  have : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have : QuasiCompact G.val.X.hom := G.property.2.2
  exact ⟨(twist σ).mapGrp.obj G.val, inferInstanceAs (IsAffine (pullback G.val.X.hom g)),
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.val.X.hom g)),
    inferInstanceAs (QuasiCompact (pullback.snd G.val.X.hom g))⟩

private theorem twist_connected (σ : K ≃ₐ[k] K) {X : SchemeOver K}
    (h : ConnectedSpace X.left) : ConnectedSpace ((twist σ).obj X).left := by
  let g := (fieldAutomorphismSpec σ).hom
  have : IsIso (pullback.fst X.hom g) :=
    (IsPullback.of_hasPullback X.hom g).isIso_fst_of_isIso
  exact (pullback.fst X.hom g).homeomorph.connectedSpace_iff.mpr h

private theorem twist_smooth (σ : K ≃ₐ[k] K) {X : SchemeOver K}
    (h : Smooth X.hom) : Smooth ((twist σ).obj X).hom :=
  MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback X.hom (fieldAutomorphismSpec σ).hom) h

private theorem twist_closed (σ : K ≃ₐ[k] K) {X Y : SchemeOver K} (f : X ⟶ Y)
    (h : IsClosedImmersion f.left) : IsClosedImmersion ((twist σ).map f).left := by
  let g := (fieldAutomorphismSpec σ).hom
  have hx : IsIso (pullback.fst X.hom g) := (IsPullback.of_hasPullback X.hom g).isIso_fst_of_isIso
  have hy : IsIso (pullback.fst Y.hom g) := (IsPullback.of_hasPullback Y.hom g).isIso_fst_of_isIso
  have he : ((twist σ).map f).left ≫ pullback.fst Y.hom g = pullback.fst X.hom g ≫ f.left :=
    pullback.lift_fst _ _ _
  apply (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)
    ((twist σ).map f).left (pullback.fst Y.hom g)).mp
  rw [he]
  infer_instance

private theorem twist_normal (σ : K ≃ₐ[k] K) {G H : GroupScheme K}
    (i : H ⟶ G) (h : IsNormalSubgroup i) : IsNormalSubgroup ((twist σ).mapGrp.map i) := by
  obtain ⟨c, hc⟩ := h
  let F := twist σ
  let e := prodComparisonIso F G.X H.X
  have he₁ : e.inv ≫ F.map (fst G.X H.X) = fst (F.obj G.X) (F.obj H.X) := by
    rw [← CartesianMonoidalCategory.prodComparison_fst, ← prodComparisonIso_hom,
      Iso.inv_hom_id_assoc]
  have he₂ : e.inv ≫ F.map (snd G.X H.X) = snd (F.obj G.X) (F.obj H.X) := by
    rw [← CartesianMonoidalCategory.prodComparison_snd, ← prodComparisonIso_hom,
      Iso.inv_hom_id_assoc]
  refine ⟨e.inv ≫ F.map c, ?_⟩
  change (e.inv ≫ F.map c) ≫ F.map i.hom.hom = _
  rw [Category.assoc, ← F.map_comp, hc]
  unfold Specs.subgroupConjugation
  simp only [F.map_mul, F.map_inv', F.map_comp, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, he₁, he₂]
  rfl

private abbrev liftField (K : Type u) := ULift.{u, u} K

private abbrev liftAlgebra (K : Type u) [Field K] : Algebra K (liftField K) :=
  (ULift.ringEquiv.symm : K ≃+* liftField K).toRingHom.toAlgebra

private abbrev twistAlgebra (σ : K ≃ₐ[k] K) : Algebra K (liftField K) :=
  ((ULift.ringEquiv.symm : K ≃+* liftField K).toRingHom.comp σ.toRingHom).toAlgebra

private def twistComparison (σ : K ≃ₐ[k] K) (G : GroupScheme K) :
    (@groupBaseChange K _ (liftField K) _ (twistAlgebra σ)).obj G ≅
    (@groupBaseChange K _ (liftField K) _ (liftAlgebra K)).obj ((twist σ).mapGrp.obj G) := by
  let L := liftField K
  let b₁ := @fieldSpecMap K _ L _ (liftAlgebra K)
  let b₂ := @fieldSpecMap K _ L _ (twistAlgebra σ)
  have hb : b₁ ≫ (fieldAutomorphismSpec σ).hom = b₂ := by
    change Spec.map (CommRingCat.ofHom (ULift.ringEquiv.symm : K ≃+* L).toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom) =
      Spec.map (CommRingCat.ofHom ((ULift.ringEquiv.symm : K ≃+* L).toRingHom.comp σ.toRingHom))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  let e : Over.pullback b₂ ≅ Over.pullback (fieldAutomorphismSpec σ).hom ⋙ Over.pullback b₁ :=
    eqToIso (congrArg (fun f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) ↦
      Over.pullback f) hb.symm) ≪≫ Over.pullbackComp _ _
  exact (Functor.mapGrpNatIso e ≪≫ Functor.mapGrpCompIso).app G

private theorem unipotent_twist (σ : K ≃ₐ[k] K) (G : AffineAlgebraicGroup K) :
    IsUnipotent (twistAffineGroup σ G) ↔ IsUnipotent G := by
  let L := liftField K
  let a₁ := liftAlgebra K
  let a₂ := twistAlgebra σ
  let H := twistAffineGroup σ G
  let G₂ := @baseChangedAlgebraicGroup K _ L _ a₂ G
  let H₁ := @baseChangedAlgebraicGroup K _ L _ a₁ H
  exact (@Unipotent.unipotenceFieldExtension K L _ _ a₁ H).symm.trans
    ((unipotent_of_iso (G := G₂) (H := H₁) (twistComparison σ G.val)).symm.trans
      (@Unipotent.unipotenceFieldExtension K L _ _ a₂ G))

private theorem solvable_twist [IsAlgClosed K] (σ : K ≃ₐ[k] K) (G : AffineAlgebraicGroup K)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    Specs.SchemeDerivedGroup.IsSolvable (twistAffineGroup σ G).val ↔
      Specs.SchemeDerivedGroup.IsSolvable G.val := by
  let L := liftField K
  have hL : IsAlgClosed L := IsAlgClosed.of_ringEquiv K L (ULift.ringEquiv.symm : K ≃+* L)
  let a₁ := liftAlgebra K
  let a₂ := twistAlgebra σ
  let H := twistAffineGroup σ G
  let G₂ := @baseChangedAlgebraicGroup K _ L _ a₂ G
  let H₁ := @baseChangedAlgebraicGroup K _ L _ a₁ H
  have hHs : Smooth H.val.X.hom := twist_smooth σ hs
  have hHc : ConnectedSpace H.val.X.left := twist_connected σ hc
  have hG₂s : Smooth G₂.val.X.hom := (@smooth_baseChange_iff K L _ _ a₂ G.val.X).mpr hs
  have hG₂c : ConnectedSpace G₂.val.X.left := (@connected_baseChange_iff K L _ _ a₂ G).mpr hc
  have hH₁s : Smooth H₁.val.X.hom := (@smooth_baseChange_iff K L _ _ a₁ H.val.X).mpr hHs
  have hH₁c : ConnectedSpace H₁.val.X.left := (@connected_baseChange_iff K L _ _ a₁ H).mpr hHc
  exact (@solvable_baseChange_iff K L _ _ a₁ _ _ H hHs hHc).symm.trans
    ((solvable_of_iso (G := G₂) (H := H₁) (twistComparison σ G.val)
      hG₂s hG₂c hH₁s hH₁c).symm.trans (@solvable_baseChange_iff K L _ _ a₂ _ _ G hs hc))


private theorem fieldAutomorphismSpec_over (σ : K ≃ₐ[k] K) :
    (fieldAutomorphismSpec σ).hom ≫ fieldSpecMap k K = fieldSpecMap k K := by
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k K)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : σ.toRingHom.comp (algebraMap k K) = algebraMap k K :=
    RingHom.ext σ.commutes
  rw [h]

private theorem twistBaseChangeSquare (σ : K ≃ₐ[k] K) (X : SchemeOver k) :
    let Y := (baseChange k K).obj X
    let g := (fieldAutomorphismSpec σ).hom
    IsPullback (pullback.fst Y.hom g ≫ pullback.fst X.hom (fieldSpecMap k K))
      (pullback.snd Y.hom g) X.hom (fieldSpecMap k K) := by
  let Y := (baseChange k K).obj X
  let g := (fieldAutomorphismSpec σ).hom
  let P (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :=
    IsPullback (pullback.fst Y.hom g ≫ pullback.fst X.hom (fieldSpecMap k K))
      (pullback.snd Y.hom g) X.hom f
  exact (congrArg P (fieldAutomorphismSpec_over σ)).mp
    ((IsPullback.of_hasPullback Y.hom g).paste_horiz (IsPullback.of_hasPullback X.hom (fieldSpecMap k K)))

open private baseChangeProjection_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private def twistBaseChangeComponent (σ : K ≃ₐ[k] K) (X : SchemeOver k) :
    (baseChange k K ⋙ twist σ).obj X ≅ (baseChange k K).obj X :=
  Over.isoMk (twistBaseChangeSquare σ X).isoPullback (twistBaseChangeSquare σ X).isoPullback_hom_snd

set_option maxHeartbeats 800000 in
private def twistBaseChangeIso (σ : K ≃ₐ[k] K) : baseChange k K ⋙ twist σ ≅ baseChange k K :=
  NatIso.ofComponents (twistBaseChangeComponent σ) (by
    intro X Y f
    let B := baseChange k K
    let F := twist σ
    let g := (fieldAutomorphismSpec σ).hom
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change ((F.map (B.map f)).left ≫ (twistBaseChangeSquare σ Y).isoPullback.hom) ≫
        pullback.fst Y.hom (fieldSpecMap k K) =
        ((twistBaseChangeSquare σ X).isoPullback.hom ≫ (B.map f).left) ≫
          pullback.fst Y.hom (fieldSpecMap k K)
      simp only [Category.assoc, IsPullback.isoPullback_hom_fst]
      have h : (F.map (B.map f)).left ≫ pullback.fst (B.obj Y).hom g =
          pullback.fst (B.obj X).hom g ≫ (B.map f).left := pullback.lift_fst _ _ _
      rw [← Category.assoc, h, Category.assoc, baseChangeProjection_naturality,
        ← Category.assoc (twistBaseChangeSquare σ X).isoPullback.hom,
        IsPullback.isoPullback_hom_fst, Category.assoc]
    · let a := (B ⋙ F).map f ≫ (twistBaseChangeComponent σ Y).hom
      let b := (twistBaseChangeComponent σ X).hom ≫ B.map f
      exact (Over.w a).trans (Over.w b).symm)

private def twistGroupBaseChangeIso (σ : K ≃ₐ[k] K) :
    groupBaseChange k K ⋙ (twist σ).mapGrp ≅ groupBaseChange k K :=
  Functor.mapGrpCompIso.symm ≪≫ Functor.mapGrpNatIso (twistBaseChangeIso σ)

/-- The scalar automorphism of the underlying base-changed scheme. -/
private def scalarSchemeMap (σ : K ≃ₐ[k] K) (X : SchemeOver k) :
    ((baseChange k K).obj X).left ⟶ ((baseChange k K).obj X).left :=
  ((twistBaseChangeIso σ).app X).inv.left ≫
    pullback.fst ((baseChange k K).obj X).hom (fieldAutomorphismSpec σ).hom

private theorem scalarSchemeMap_fst (σ : K ≃ₐ[k] K) (X : SchemeOver k) :
    scalarSchemeMap σ X ≫ pullback.fst X.hom (fieldSpecMap k K) =
      pullback.fst X.hom (fieldSpecMap k K) := by
  exact (twistBaseChangeSquare σ X).isoPullback_inv_fst

private theorem scalarSchemeMap_snd (σ : K ≃ₐ[k] K) (X : SchemeOver k) :
    scalarSchemeMap σ X ≫ pullback.snd X.hom (fieldSpecMap k K) =
      pullback.snd X.hom (fieldSpecMap k K) ≫ (fieldAutomorphismSpec σ).hom := by
  let d := ((twistBaseChangeIso σ).app X).inv
  change (d.left ≫ pullback.fst ((baseChange k K).obj X).hom
    (fieldAutomorphismSpec σ).hom) ≫ ((baseChange k K).obj X).hom = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ (fieldAutomorphismSpec σ).hom) (Over.w d)

private theorem scalarSchemeMap_naturality (σ : K ≃ₐ[k] K) {X Y : SchemeOver k} (f : X ⟶ Y) :
    scalarSchemeMap σ X ≫ ((baseChange k K).map f).left =
      ((baseChange k K).map f).left ≫ scalarSchemeMap σ Y := by
  let B := baseChange k K
  let F := twist σ
  let g := (fieldAutomorphismSpec σ).hom
  have h : (F.map (B.map f)).left ≫ pullback.fst (B.obj Y).hom g =
      pullback.fst (B.obj X).hom g ≫ (B.map f).left := pullback.lift_fst _ _ _
  have he := congrArg (fun a : B.obj X ⟶ F.obj (B.obj Y) ↦ a.left)
    ((twistBaseChangeIso σ).inv.naturality f)
  change (B.map f).left ≫ ((twistBaseChangeIso σ).app Y).inv.left =
    ((twistBaseChangeIso σ).app X).inv.left ≫ (F.map (B.map f)).left at he
  unfold scalarSchemeMap
  rw [Category.assoc, ← h, ← Category.assoc, ← he, Category.assoc]


open private extendedSpecIso extendedSpecIso_hom_fst extendedSpecIso_natural extendedGroupIso
  specGroupMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private def scalarRingMap (σ : K ≃ₐ[k] K) (A : HopfAlgebraCategory k) :
    K ⊗[k] A →ₐ[k] K ⊗[k] A :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)

private theorem scalarRingMap_apply (σ : K ≃ₐ[k] K) (A : HopfAlgebraCategory k)
    (x : K ⊗[k] A) : scalarRingMap σ A x = scalarAction σ A x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem scalarRingMap_inverse (σ : K ≃ₐ[k] K) (A : HopfAlgebraCategory k)
    (x : K ⊗[k] A) : scalarRingMap σ.symm A (scalarRingMap σ A x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [scalarRingMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem scalarSchemeMap_spec (σ : K ≃ₐ[k] K) (A : HopfAlgebraCategory k) :
    let e := (extendedSpecIso K A).hom.left
    e ≫ scalarSchemeMap σ (specGroup A).X =
      Spec.map (CommRingCat.ofHom (scalarRingMap σ A).toRingHom) ≫ e := by
  let e := (extendedSpecIso K A).hom.left
  let f := Spec.map (CommRingCat.ofHom (scalarRingMap σ A).toRingHom)
  let i : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let q := pullback.snd (specGroup A).X.hom (fieldSpecMap k K)
  change e ≫ scalarSchemeMap σ (specGroup A).X = f ≫ e
  apply pullback.hom_ext
  · have h : (scalarRingMap σ A).toRingHom.comp i.toRingHom = i.toRingHom := by
      ext a
      change (scalarRingMap σ A) (1 ⊗ₜ[k] a) = 1 ⊗ₜ[k] a
      simp [scalarRingMap]
    simp only [Category.assoc, scalarSchemeMap_fst, extendedSpecIso_hom_fst, e]
    change Spec.map (CommRingCat.ofHom i.toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom i.toRingHom)
    unfold f
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  · have hq : e ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A))) :=
      Over.w (extendedSpecIso K A).hom
    have h : (scalarRingMap σ A).toRingHom.comp (algebraMap K (K ⊗[k] A)) =
        (algebraMap K (K ⊗[k] A)).comp σ.toRingHom := by
      ext a
      change (scalarRingMap σ A) (a ⊗ₜ[k] (1 : A)) = σ a ⊗ₜ[k] (1 : A)
      simp [scalarRingMap]
    rw [Category.assoc, Category.assoc]
    change e ≫ (scalarSchemeMap σ (specGroup A).X ≫ q) = f ≫ (e ≫ q)
    rw [scalarSchemeMap_snd, ← Category.assoc, hq]
    unfold f
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) =
      Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, h]

private theorem radical_inclusion_factors_through_scalar (G : AffineAlgebraicGroup k)
    {P : AffineAlgebraicGroup K → Prop}
    (htwist : ∀ (σ : K ≃ₐ[k] K) (H : AffineAlgebraicGroup K),
      Smooth H.val.X.hom → ConnectedSpace H.val.X.left → P H → P (twistAffineGroup σ H))
    (N : ClosedSubgroup (baseChangedAlgebraicGroup K G).val)
    (hN : IsRadical (baseChangedAlgebraicGroup K G) P N) (σ : K ≃ₐ[k] K) :
    ∃ a : N.group.X.left ⟶ N.group.X.left,
      N.inclusion.hom.hom.left = a ≫ N.inclusion.hom.hom.left ≫ scalarSchemeMap σ G.val.X := by
  let F := twist σ
  let Y := (baseChangedAlgebraicGroup K G).val
  let e := (twistGroupBaseChangeIso σ).app G.val
  let i := F.mapGrp.map N.inclusion
  have hi : IsClosedImmersion i.hom.hom.left := twist_closed σ _ N.isClosedImmersion
  have he : IsIso e.hom.hom.hom.left := (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso e.hom
  let T : ClosedSubgroup Y := ⟨_, i ≫ e.hom, IsClosedImmersion.comp _ _⟩
  have ht : IsSmoothConnectedNormal (G := baseChangedAlgebraicGroup K G) T :=
    ⟨twist_smooth σ hN.1.1, twist_connected σ hN.1.2.1,
      transport_normal e ⟨_, i, hi⟩ (twist_normal σ _ hN.1.2.2)⟩
  have hp : P (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K G) T) :=
    htwist σ (closedSubgroupAlgebraicGroup N) hN.1.1 hN.1.2.1 hN.2.1
  obtain ⟨j, hj⟩ := hN.2.2 T ht hp
  let g := (fieldAutomorphismSpec σ).hom
  let v := pullback.fst N.group.X.hom g
  let w := pullback.fst Y.X.hom g
  have hv : IsIso v := (IsPullback.of_hasPullback N.group.X.hom g).isIso_fst_of_isIso
  have h := congrArg (Grp.forget (SchemeOver K) ⋙ Over.forget _).map hj
  change j.hom.hom.left ≫ N.inclusion.hom.hom.left = i.hom.hom.left ≫ e.hom.hom.hom.left at h
  refine ⟨inv v ≫ j.hom.hom.left, ?_⟩
  change N.inclusion.hom.hom.left = (inv v ≫ j.hom.hom.left) ≫
    N.inclusion.hom.hom.left ≫ e.inv.hom.hom.left ≫ w
  have he' := ((Grp.forget (SchemeOver K) ⋙ Over.forget _).mapIso e).hom_inv_id
  change e.hom.hom.hom.left ≫ e.inv.hom.hom.left = 𝟙 _ at he'
  have hi' : i.hom.hom.left ≫ w = v ≫ N.inclusion.hom.hom.left := pullback.lift_fst _ _ _
  rw [Category.assoc, ← Category.assoc j.hom.hom.left, h, Category.assoc,
    ← Category.assoc e.hom.hom.hom.left, he', Category.id_comp, hi', IsIso.inv_hom_id_assoc]

open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

set_option maxHeartbeats 800000 in
private theorem radical_descends {P : AffineAlgebraicGroup K → Prop}
    (hfixed : ∀ a : K, (∀ σ : K ≃ₐ[k] K, σ a = a) → a ∈ Set.range (algebraMap k K))
    (htwist : ∀ (σ : K ≃ₐ[k] K) (H : AffineAlgebraicGroup K),
      Smooth H.val.X.hom → ConnectedSpace H.val.X.left → P H → P (twistAffineGroup σ H))
    (G : AffineAlgebraicGroup k) (N : ClosedSubgroup (baseChangedAlgebraicGroup K G).val)
    (hN : IsRadical (baseChangedAlgebraicGroup K G) P N) :
    ∃ M : ClosedSubgroup G.val, ∃ d : (extendSubgroup K M).group ≅ N.group,
      d.hom ≫ N.inclusion = (extendSubgroup K M).inclusion := by
  obtain ⟨A, _, ⟨eA⟩⟩ := groupPresentation G
  let E := extendedHopf K A
  let F := groupBaseChange k K
  let eG := extendedGroupIso K A ≪≫ F.mapIso eA
  have hi := N.isClosedImmersion
  have heG : IsIso eG.inv.hom.hom.left := (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso eG.inv
  have hi' : IsClosedImmersion (N.inclusion ≫ eG.inv).hom.hom.left := by
    change IsClosedImmersion (N.inclusion.hom.hom.left ≫ eG.inv.hom.hom.left)
    infer_instance
  obtain ⟨J, ⟨hJ, eN, heN⟩, _⟩ :=
    (closedSubgroupClassification K E _ _).mp hi'
  let q := hopfQuotientMap E J
  let D := hopfQuotient E J
  let s := specGroupMap q
  have hinclusion : eN.hom ≫ s ≫ eG.hom = N.inclusion := by
    rw [← Category.assoc]
    change (eN.hom ≫ specGroupMap (hopfQuotientMap E J)) ≫ eG.hom = _
    rw [heN, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hstable (σ : K ≃ₐ[k] K) (x : E) (hx : x ∈ J) : scalarAction σ A x ∈ J := by
    obtain ⟨a, ha⟩ := radical_inclusion_factors_through_scalar G htwist N hN σ.symm
    let U := Grp.forget (SchemeOver K) ⋙ Over.forget _
    have hs : U.map s ≫ U.map eG.hom = U.map eN.inv ≫ U.map N.inclusion := by
      rw [← U.map_comp, ← U.map_comp, ← hinclusion, Iso.inv_hom_id_assoc]
    have hm : U.map eG.hom ≫ scalarSchemeMap σ.symm G.val.X =
        Spec.map (CommRingCat.ofHom (scalarRingMap σ.symm A).toRingHom) ≫ U.map eG.hom := by
      change ((extendedSpecIso K A).hom.left ≫ ((baseChange k K).map eA.hom.hom.hom).left) ≫ _ =
        _ ≫ ((extendedSpecIso K A).hom.left ≫ ((baseChange k K).map eA.hom.hom.hom).left)
      rw [Category.assoc, ← scalarSchemeMap_naturality, ← Category.assoc, scalarSchemeMap_spec,
        Category.assoc]
    let b := U.map eN.inv ≫ a ≫ U.map eN.hom
    have hne : U.map eN.hom ≫ U.map eN.inv = 𝟙 _ := (U.mapIso eN).hom_inv_id
    have hb : b ≫ U.map eN.inv = U.map eN.inv ≫ a := by
      simp only [b, Category.assoc, hne]
      exact congrArg (U.map eN.inv ≫ ·) (Category.comp_id a)
    have hfact : U.map s = b ≫ U.map s ≫
        Spec.map (CommRingCat.ofHom (scalarRingMap σ.symm A).toRingHom) := by
      apply (cancel_mono (U.map eG.hom)).mp
      symm
      calc
        _ = b ≫ (U.map s ≫ U.map eG.hom) ≫ scalarSchemeMap σ.symm G.val.X := by
          simp only [Category.assoc, ← hm]
        _ = (b ≫ U.map eN.inv) ≫ U.map N.inclusion ≫ scalarSchemeMap σ.symm G.val.X := by
          simp only [hs, Category.assoc]
        _ = U.map eN.inv ≫ U.map N.inclusion := by
          rw [hb, Category.assoc]
          exact congrArg (U.map eN.inv ≫ ·) ha.symm
        _ = U.map s ≫ U.map eG.hom := hs.symm
    change Spec.map (CommRingCat.ofHom q.hom.toAlgHom.toRingHom) = _ at hfact
    have hq := congrArg Spec.preimage hfact
    change Spec.preimage (Spec.map (CommRingCat.ofHom q.hom.toAlgHom.toRingHom)) =
      Spec.preimage (b ≫ Spec.map (CommRingCat.ofHom q.hom.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (scalarRingMap σ.symm A).toRingHom)) at hq
    simp only [Spec.preimage_comp, Spec.preimage_map] at hq
    have hxq := ConcreteCategory.congr_hom hq (scalarRingMap σ A x)
    change q.hom (scalarRingMap σ A x) =
      (Spec.preimage b).hom (q.hom (scalarRingMap σ.symm A (scalarRingMap σ A x))) at hxq
    rw [scalarRingMap_inverse] at hxq
    have hz : q.hom x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    rw [hz, map_zero, scalarRingMap_apply] at hxq
    exact Ideal.Quotient.eq_zero_iff_mem.mp hxq
  obtain ⟨I, hI, hIJ⟩ := stable_hopf_ideal_descends A J hfixed hstable
  let j := specGroupMap (hopfQuotientMap A I)
  have hj : IsClosedImmersion j.hom.hom.left := (hopfMapClosedImmersion k _).mpr
    Ideal.Quotient.mk_surjective
  have heA : IsIso eA.hom.hom.hom.left := (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso eA.hom
  let M : ClosedSubgroup G.val := ⟨_, j ≫ eA.hom, IsClosedImmersion.comp _ _⟩
  refine ⟨M, ?_⟩
  subst J
  obtain ⟨r, hr⟩ := extendedHopfQuotient k K A I
  let rS := (hopfSpec (CommRingCat.of K)).mapIso r.op
  let eM := rS.symm ≪≫ extendedGroupIso K (hopfQuotient A I)
  have hme : s ≫ (extendedGroupIso K A).hom = eM.hom ≫ F.map j := by
    have ht := congrArg (fun f ↦ (specGroupMap f).hom.hom) hr
    rw [specGroupMap_comp] at ht
    apply Grp.hom_ext
    have hn := extendedSpecIso_natural K (hopfQuotientMap A I)
    change s.hom.hom ≫ (extendedSpecIso K A).hom =
      rS.inv.hom.hom ≫ (extendedSpecIso K (hopfQuotient A I)).hom ≫ (baseChange k K).map j.hom.hom
    rw [← hn]
    change s.hom.hom ≫ _ = rS.inv.hom.hom ≫ _
    change rS.hom.hom.hom ≫ s.hom.hom =
      (specGroupMap (extendedHopfMap K (hopfQuotientMap A I))).hom.hom at ht
    rw [← ht, Category.assoc]
    exact (Iso.inv_hom_id_assoc ((Grp.forget (SchemeOver K)).mapIso rS) _).symm
  exact ⟨eM.symm ≪≫ eN.symm, by
    change (eM.inv ≫ eN.inv) ≫ N.inclusion = F.map (j ≫ eA.hom)
    rw [Category.assoc, ← hinclusion, Iso.inv_hom_id_assoc]
    change eM.inv ≫ s ≫ (extendedGroupIso K A).hom ≫ (F.mapIso eA).hom = _
    rw [← Category.assoc s, hme, Category.assoc, Iso.inv_hom_id_assoc, F.map_comp]
    rfl⟩

end FieldAutomorphism


section GeometricRadicals

open Specs.GeometricRadicals (GeometricGroup IsRadical IsReductive IsSemisimple
  IsSmoothConnectedNormal IsTrivialSubgroup geometricUnipotentRadical geometricSolvableRadical)
open Specs.Unipotent (IsUnipotent baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsSolvable)

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem solvable_subgroup_baseChange [PerfectField k] [IsAlgClosed K]
    {G : AffineAlgebraicGroup k} (H : ClosedSubgroup G.val) (hH : IsSmoothConnectedNormal H) :
    IsSolvable (extendSubgroup K H).group ↔ IsSolvable H.group :=
  solvable_baseChange_iff (closedSubgroupAlgebraicGroup H) hH.1 hH.2.1

private theorem unipotent_subgroup_iso {G : AffineAlgebraicGroup k}
    {H N : ClosedSubgroup G.val} (e : H.group ≅ N.group) :
    IsUnipotent (closedSubgroupAlgebraicGroup H) ↔ IsUnipotent (closedSubgroupAlgebraicGroup N) :=
  unipotent_of_iso (G := closedSubgroupAlgebraicGroup H) (H := closedSubgroupAlgebraicGroup N) e

private theorem solvable_subgroup_iso [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {H N : ClosedSubgroup G.val} (e : H.group ≅ N.group)
    (hH : IsSmoothConnectedNormal H) (hN : IsSmoothConnectedNormal N) :
    IsSolvable H.group ↔ IsSolvable N.group :=
  solvable_of_iso (G := closedSubgroupAlgebraicGroup H) (H := closedSubgroupAlgebraicGroup N)
    e hH.1 hH.2.1 hN.1 hN.2.1

theorem unipotentRadicalBaseChange : Specs.RadicalBaseChange.UnipotentRadicalBaseChange.{u} := by
  intro k K _ _ _ _ _ G _ _ R hR
  obtain ⟨N, hN⟩ := GeometricRadicals.unipotentRadicalExists (baseChangedAlgebraicGroup K G)
  obtain ⟨M, e, he⟩ := radical_descends fixed_field_of_algClosed
    (fun σ H _ _ ↦ (unipotent_twist σ H).mpr) G N hN
  refine ⟨baseChangeClosedSubgroup k K R.inclusion R.isClosedImmersion, ?_⟩
  exact radical_baseChange_of_descent (fun H _ ↦ unipotent_subgroup_baseChange_iff H)
    (fun d _ _ ↦ unipotent_subgroup_iso d) hN e he hR

theorem solvableRadicalBaseChange : Specs.RadicalBaseChange.SolvableRadicalBaseChange.{u} := by
  intro k K _ _ _ _ _ G _ _ R hR
  obtain ⟨N, hN⟩ := GeometricRadicals.solvableRadicalExists (baseChangedAlgebraicGroup K G)
  obtain ⟨M, e, he⟩ := radical_descends fixed_field_of_algClosed
    (fun σ H hs hc ↦ (solvable_twist σ H hs hc).mpr) G N hN
  refine ⟨baseChangeClosedSubgroup k K R.inclusion R.isClosedImmersion, ?_⟩
  exact radical_baseChange_of_descent (fun H hH ↦ solvable_subgroup_baseChange H hH)
    (fun d hx hy ↦ solvable_subgroup_iso d hx hy) hN e he hR

theorem unipotentRadicalPerfectDescent : Specs.RadicalBaseChange.UnipotentRadicalPerfectDescent.{u} := by
  intro k _ _ G _ _
  let N := geometricUnipotentRadical G
  have hN := GeometricRadicals.geometricUnipotentRadicalLargest G
  obtain ⟨H, e, he⟩ := radical_descends fixed_field_of_perfect
    (fun σ A _ _ ↦ (unipotent_twist σ A).mpr) G N hN
  exact ⟨H, radical_of_extended_radical (fun M _ ↦ unipotent_subgroup_baseChange_iff M)
    (fun d _ _ ↦ unipotent_subgroup_iso d) hN e he, e, he⟩

theorem solvableRadicalPerfectDescent : Specs.RadicalBaseChange.SolvableRadicalPerfectDescent.{u} := by
  intro k _ _ G _ _
  let N := geometricSolvableRadical G
  have hN := GeometricRadicals.geometricSolvableRadicalLargest G
  obtain ⟨H, e, he⟩ := radical_descends fixed_field_of_perfect
    (fun σ A hs hc ↦ (solvable_twist σ A hs hc).mpr) G N hN
  exact ⟨H, radical_of_extended_radical (fun M hM ↦ solvable_subgroup_baseChange M hM)
    (fun d hx hy ↦ solvable_subgroup_iso d hx hy) hN e he, e, he⟩

theorem reductiveFieldExtension : Specs.RadicalBaseChange.ReductiveFieldExtension.{u} := by
  intro k K _ _ _ G hs hc
  let G' := baseChangedAlgebraicGroup K G
  have hs' : Smooth G'.val.X.hom := (smooth_baseChange_iff G.val.X).mpr hs
  have hc' : GeometricallyConnected G'.val.X.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hc
  have h := radical_trivial_of_fieldExtension (K := K) G hs hc
    (fun X ↦ IsUnipotent X)
    (fun {_ _ _ X Y} e _ _ _ _ ↦ unipotent_of_iso (G := X) (H := Y) e)
    (by
      intro F L _ _ _ _ _ X hX cX J hJ
      obtain ⟨_, hJK⟩ := unipotentRadicalBaseChange (k := F) (K := L) X hX cX J hJ
      exact hJK)
    (GeometricRadicals.geometricUnipotentRadicalLargest G)
    (GeometricRadicals.geometricUnipotentRadicalLargest G')
  exact ⟨fun a ↦ ⟨hs, hc, h.mp a.2.2⟩, fun a ↦ ⟨hs', hc', h.mpr a.2.2⟩⟩

theorem semisimpleFieldExtension : Specs.RadicalBaseChange.SemisimpleFieldExtension.{u} := by
  intro k K _ _ _ G hs hc
  let G' := baseChangedAlgebraicGroup K G
  have hs' : Smooth G'.val.X.hom := (smooth_baseChange_iff G.val.X).mpr hs
  have hc' : GeometricallyConnected G'.val.X.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hc
  have h := radical_trivial_of_fieldExtension (K := K) G hs hc
    (fun X ↦ IsSolvable X.val)
    (fun {_ _ _ X Y} e hx hcx hy hcy ↦ solvable_of_iso (G := X) (H := Y) e hx hcx hy hcy)
    (by
      intro F L _ _ _ _ _ X hX cX J hJ
      obtain ⟨_, hJK⟩ := solvableRadicalBaseChange (k := F) (K := L) X hX cX J hJ
      exact hJK)
    (GeometricRadicals.geometricSolvableRadicalLargest G)
    (GeometricRadicals.geometricSolvableRadicalLargest G')
  exact ⟨fun a ↦ ⟨hs, hc, h.mp a.2.2⟩, fun a ↦ ⟨hs', hc', h.mpr a.2.2⟩⟩

end GeometricRadicals

end
end LinearAlgebraicGroups.Reductive.RadicalBaseChange
