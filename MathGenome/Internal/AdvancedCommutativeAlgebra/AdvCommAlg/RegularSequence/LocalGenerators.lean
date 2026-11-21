import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.LocalGenerators
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Functoriality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.DegreeOneConverse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open Module CategoryTheory
open scoped TensorProduct Pointwise
universe u v w
namespace AdvCommAlg.RegularSequence
variable {R : Type u} [CommRing R]

/-- Local permutation invariance includes the empty list. -/
theorem local_permutation : Specs.localPermutation.{u,v} := by
  intro R _ _ _ M _ _ _ _ x y _ hx hp
  exact IsLocalRing.isRegular_of_perm hx hp

omit [CommRing R] in
private theorem otherEntries (x : List R) (i : Fin x.length) :
    x.get '' {i}ᶜ = {a | a ∈ x.eraseIdx i.val} := by
  ext a
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.val, j.isLt, (fun h => hj (Fin.ext h)), rfl⟩
  · rintro ⟨j, hj, hji, hja⟩
    exact ⟨⟨j, hj⟩, (fun h => hji (congrArg Fin.val h)), hja⟩

/-- A redundant last entry acts by zero on a nonzero quotient. -/
theorem regular_minimal : Specs.regularMinimal.{u,v} := by
  intro R _ _ _ M _ _ _ _ x _ hx
  refine ⟨rfl, ?_⟩
  intro i hi
  rw [otherEntries] at hi
  have hp : x.Perm (x.eraseIdx i.val ++ [x.get i]) :=
    (List.getElem_cons_eraseIdx_perm i.isLt).symm.trans (by
      simpa using (List.perm_append_comm (l₁ := [x.get i]) (l₂ := x.eraseIdx i.val)))
  have hr := IsLocalRing.isRegular_of_perm hx hp
  have hlast := (RingTheory.Sequence.isWeaklyRegular_append_iff M _ _).mp hr.toIsWeaklyRegular
  have hinj := (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mp
    hlast.2
  let Q := M ⧸ (Ideal.ofList (x.eraseIdx i.val) • ⊤ : Submodule R M)
  have hn : Nontrivial Q := by
    have h := regular_prefix_quotient_nonzero M _ hr (x.eraseIdx i.val).length
    simpa [Q, PrefixQuotient, prefixIdeal] using h
  have hz : ∀ q : Q, x.get i • q = 0 := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
    change Submodule.Quotient.mk (x.get i • m) = (0 : Q)
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.smul_mem_smul hi (Submodule.mem_top : m ∈ (⊤ : Submodule R M))
  have hs : Subsingleton Q := ⟨fun a b => hinj ((hz a).trans (hz b).symm)⟩
  exact not_nontrivial Q hn

section Residue
variable [IsLocalRing R]
variable {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
variable {ι : Type w} (z : ι → N)

/-- Nakayama: a family generates precisely when its residue images do. -/
theorem residue_span_iff :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range (fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] z i)) = ⊤ ↔
    Submodule.span R (Set.range z) = ⊤ := by
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top (R := R), Submodule.map_span]
  rw [← Submodule.restrictScalars_eq_top_iff R]
  rw [Submodule.restrictScalars_span R (IsLocalRing.ResidueField R)
    IsLocalRing.residue_surjective]
  simp only [← Set.range_comp, Function.comp_def, TensorProduct.mk_apply]

/-- Over a field, an irredundant spanning family is a basis; Nakayama
identifies irredundancy before and after reduction. -/
theorem residue_linearIndependent (hspan : Submodule.span R (Set.range z) = ⊤)
    (hirr : Irredundant (R := R) z) :
    LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] z i) := by
  rw [linearIndependent_iff_notMem_span]
  intro i hi
  have hsp : Submodule.span (IsLocalRing.ResidueField R)
      (Set.range (fun j : {j // j ≠ i} =>
        (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] z j.val)) = ⊤ := by
    have hall := (residue_span_iff z).mpr hspan
    apply top_unique
    rw [← hall]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      have he : Set.range (fun j : {j // j ≠ i} =>
          (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] z j.val) =
          (fun j => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] z j) '' (Set.univ \ {i}) := by
        ext a
        simp [Set.mem_range, Set.mem_image]
      rwa [he]
    · exact Submodule.subset_span ⟨⟨j, hji⟩, rfl⟩
  have htop := (residue_span_iff (fun j : {j // j ≠ i} => z j.val)).mp hsp
  apply hirr i
  have hz : z i ∈ Submodule.span R (Set.range (fun j : {j // j ≠ i} => z j.val)) :=
    htop ▸ Submodule.mem_top
  have he : Set.range (fun j : {j // j ≠ i} => z j.val) = z '' {i}ᶜ := by
    ext a
    simp [Set.mem_range, Set.mem_image]
  rwa [he] at hz
end Residue

/-- The entries generate their ideal as a module, not just as an ideal. -/
theorem idealEntries_span (x : List R) :
    Submodule.span R (Set.range (idealEntries x)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (Ideal.ofList x) _).mpr
  congr 1
  ext a
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  exact List.mem_iff_get.symm

/-- An irredundant list remains irredundant as a family in its ideal. -/
theorem idealEntries_irredundant (x : List R) (h : Irredundant (R := R) x.get) :
    Irredundant (R := R) (idealEntries x) := by
  intro i hi
  apply h i
  have hm := Submodule.mem_map_of_mem (f := (Ideal.ofList x).subtype) hi
  rw [Submodule.map_span, ← Set.image_comp] at hm
  exact hm

/-- The concrete residue-field basis of I/mI attached to minimal generators. -/
theorem minimal_residue_basis : Specs.minimalResidueBasis.{u} := by
  intro R _ _ _ x hx
  let z := idealEntries x
  have hz := idealEntries_span x
  have hi := idealEntries_irredundant x hx.2
  exact ⟨Basis.mk (residue_linearIndependent z hz hi)
    (le_of_eq ((residue_span_iff z).mpr hz).symm), fun _ => by simp [z]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The same basis in the literal quotient I/mI, with its canonical action. -/
theorem minimal_quotient_basis : Specs.minimalQuotientBasis.{u} := by
  intro R _ _ _ x hx
  obtain ⟨b, hb⟩ := minimal_residue_basis x hx
  let : Module (IsLocalRing.ResidueField R)
      ((Ideal.ofList x) ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Ideal.ofList x)))) :=
    inferInstanceAs (Module (R ⧸ IsLocalRing.maximalIdeal R) _)
  let : IsScalarTower R (IsLocalRing.ResidueField R)
      ((Ideal.ofList x) ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Ideal.ofList x)))) :=
    inferInstanceAs (IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) _)
  let e : (IsLocalRing.ResidueField R ⊗[R] Ideal.ofList x) ≃ₗ[IsLocalRing.ResidueField R]
      ((Ideal.ofList x) ⧸ (IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R (Ideal.ofList x)))) :=
    (TensorProduct.quotTensorEquivQuotSMul (Ideal.ofList x) (IsLocalRing.maximalIdeal R)).extendScalarsOfSurjective
      IsLocalRing.residue_surjective
  refine ⟨b.map e, fun i => ?_⟩
  rw [Basis.map_apply, hb]
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ _

section Change
variable [IsLocalRing R]
variable {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
variable {ι κ : Type w} [Fintype ι] [Fintype κ]

/-- The presentation map of a finite family. -/
def generatorMap (z : ι → N) : (ι → R) →ₗ[R] N := (Pi.basisFun R ι).constr R z

omit [IsLocalRing R] [Module.Finite R N] in
@[simp] theorem generatorMap_basis (z : ι → N) (i : ι) :
    generatorMap (R := R) z (Pi.basisFun R ι i) = z i := (Pi.basisFun R ι).constr_basis R z i

/-- A minimal presentation becomes an isomorphism over the residue field. -/
theorem generatorMap_residue_bijective (z : ι → N)
    (hspan : Submodule.span R (Set.range z) = ⊤) (hirr : Irredundant (R := R) z) :
    Function.Bijective ((generatorMap (R := R) z).baseChange (IsLocalRing.ResidueField R)) := by
  let k := IsLocalRing.ResidueField R
  let b := Basis.mk (residue_linearIndependent z hspan hirr)
    (le_of_eq ((residue_span_iff z).mpr hspan).symm)
  let e := ((Pi.basisFun R ι).baseChange k).equiv b (Equiv.refl ι)
  have he : (generatorMap (R := R) z).baseChange k = e.toLinearMap := by
    apply ((Pi.basisFun R ι).baseChange k).ext
    intro i
    change _ = (((Pi.basisFun R ι).baseChange k).equiv b (Equiv.refl ι))
      (((Pi.basisFun R ι).baseChange k) i)
    rw [Basis.equiv_apply, Basis.baseChange_apply, LinearMap.baseChange_tmul, generatorMap_basis]
    simp [b]
  rw [he]
  exact e.bijective

/-- Nakayama lifts surjectivity of a map from its reduction. -/
theorem surjective_of_residue_surjective {P : Type*} [AddCommGroup P] [Module R P]
    (f : P →ₗ[R] N)
    (hf : Function.Surjective (f.baseChange (IsLocalRing.ResidueField R))) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  apply (IsLocalRing.map_tensorProduct_mk_eq_top (R := R)).mp
  apply top_unique
  intro t _
  obtain ⟨s, rfl⟩ := hf t
  obtain ⟨p, rfl⟩ := TensorProduct.mk_surjective R P (IsLocalRing.ResidueField R)
    IsLocalRing.residue_surjective s
  exact Submodule.mem_map_of_mem (f := TensorProduct.mk R (IsLocalRing.ResidueField R) N 1)
    (LinearMap.mem_range_self f p)

/-- Minimal presentations differ by an invertible matrix. Reduction identifies
both presentations with bases of N/mN; Nakayama and split injectivity lift this. -/
theorem minimal_family_change (z : ι → N) (w : κ → N)
    (hz : Submodule.span R (Set.range z) = ⊤) (hw : Submodule.span R (Set.range w) = ⊤)
    (hiz : Irredundant (R := R) z) (hiw : Irredundant (R := R) w) :
    ∃ e : (ι → R) ≃ₗ[R] (κ → R), (generatorMap (R := R) w).comp e.toLinearMap = generatorMap (R := R) z := by
  have hws : Function.Surjective (generatorMap (R := R) w) := by
    rw [← LinearMap.range_eq_top, generatorMap, Basis.constr_range, hw]
  choose a ha using fun i => hws (z i)
  let f : (ι → R) →ₗ[R] (κ → R) := (Pi.basisFun R ι).constr R a
  have hf : (generatorMap (R := R) w).comp f = generatorMap (R := R) z := by
    apply (Pi.basisFun R ι).ext
    intro i
    change (generatorMap (R := R) w)
      ((Pi.basisFun R ι).constr R a (Pi.basisFun R ι i)) = generatorMap (R := R) z (Pi.basisFun R ι i)
    rw [Basis.constr_basis, generatorMap_basis]
    exact ha i
  let k := IsLocalRing.ResidueField R
  have hzr := generatorMap_residue_bijective z hz hiz
  have hwr := generatorMap_residue_bijective w hw hiw
  have hfr : Function.Bijective (f.baseChange k) := by
    have hcomp := congrArg (fun l => l.baseChange k) hf
    rw [LinearMap.baseChange_comp] at hcomp
    have hpoint (a) := LinearMap.congr_fun hcomp a
    exact ⟨fun a b hab => hzr.1 (by
      rw [← hpoint a, ← hpoint b]
      exact congrArg ((generatorMap (R := R) w).baseChange k) hab), by
      intro b
      obtain ⟨a, ha⟩ := hzr.2 ((generatorMap (R := R) w).baseChange k b)
      exact ⟨a, hwr.1 ((hpoint a).trans ha)⟩⟩
  have hfs : Function.Surjective f := surjective_of_residue_surjective f hfr.2
  obtain ⟨g, hg⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hfr.1
  have hfi : Function.Injective f := Function.HasLeftInverse.injective
    ⟨g, fun a => LinearMap.congr_fun hg a⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hfi, hfs⟩, hf⟩
end Change

/-- The coordinate change is built from the residue bases, with no assumed
regularity of the replacement list. -/
theorem minimal_change_coordinates : Specs.minimalChangeCoordinates.{u} := by
  intro R _ _ _ I x y hx hy
  let z : Fin x.length → I := fun i =>
    ⟨x.get i, hx.1 ▸ Ideal.subset_span (List.get_mem ..)⟩
  let w : Fin y.length → I := fun i =>
    ⟨y.get i, hy.1 ▸ Ideal.subset_span (List.get_mem ..)⟩
  have hz : Submodule.span R (Set.range z) = ⊤ := by
    apply (Submodule.span_range_subtype_eq_top_iff I _).mpr
    convert hx.1 using 2
    ext a
    exact List.mem_iff_get.symm
  have hw : Submodule.span R (Set.range w) = ⊤ := by
    apply (Submodule.span_range_subtype_eq_top_iff I _).mpr
    convert hy.1 using 2
    ext a
    exact List.mem_iff_get.symm
  have hiz : Irredundant (R := R) z := by
    intro i hi
    apply hx.2 i
    have hm := Submodule.mem_map_of_mem (f := I.subtype) hi
    rw [Submodule.map_span, ← Set.image_comp] at hm
    exact hm
  have hiw : Irredundant (R := R) w := by
    intro i hi
    apply hy.2 i
    have hm := Submodule.mem_map_of_mem (f := I.subtype) hi
    rw [Submodule.map_span, ← Set.image_comp] at hm
    exact hm
  obtain ⟨e, he⟩ := minimal_family_change z w hz hw hiz hiw
  have hwform : I.subtype.comp (generatorMap (R := R) w) = Koszul.listForm y := by
    apply (Pi.basisFun R (Fin y.length)).ext
    intro i
    simp only [LinearMap.comp_apply, generatorMap_basis, Koszul.listForm_basis]
    rfl
  refine ⟨e, fun i => ?_⟩
  have h := congrArg (fun n : I => (n : R))
    (LinearMap.congr_fun he (Pi.basisFun R (Fin x.length) i))
  change (I.subtype.comp (generatorMap (R := R) w))
    (e (Pi.basisFun R (Fin x.length) i)) = _ at h
  rw [hwform, Koszul.listForm_apply] at h
  simpa only [generatorMap_basis] using h.symm

/-- The concrete matrix is invertible, including the empty 0-by-0 case. -/
theorem minimal_change_matrix : Specs.minimalChangeMatrix.{u} := by
  intro R _ _ _ I x y hx hy
  obtain ⟨e, he⟩ := minimal_change_coordinates I x y hx hy
  have hlen : x.length = y.length := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using e.finrank_eq
  let p := finCongr hlen
  let bx := Pi.basisFun R (Fin x.length)
  let by' := (Pi.basisFun R (Fin y.length)).reindex p.symm
  let A := LinearMap.toMatrix bx by' e.toLinearMap
  have hA : IsUnit A.det := by
    apply Matrix.isUnit_det_of_left_inverse (B := LinearMap.toMatrix by' bx e.symm.toLinearMap)
    rw [← LinearMap.toMatrix_comp]
    have hid : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro a
      exact e.symm_apply_apply a
    rw [hid, LinearMap.toMatrix_id]
  refine ⟨hlen, A, hA, fun i => ?_⟩
  rw [he i]
  symm
  calc
    ∑ j, A j i * y.get (finCongr hlen j) =
        ∑ j, (e (Pi.basisFun R (Fin x.length) i)) (p j) * y.get (p j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [A, bx, by', LinearMap.toMatrix_apply, p]
    _ = ∑ j, (e (Pi.basisFun R (Fin x.length) i)) j * y.get j :=
      p.sum_comp (fun j => (e (Pi.basisFun R (Fin x.length) i)) j * y.get j)

/-- All minimal generating lists of the ideal of a regular list are regular
on the original module. -/
theorem replacement_regular : Specs.replacementRegular.{u,v} := by
  intro R _ _ _ M _ _ _ _ x y hxm hx hy
  obtain ⟨e, he⟩ := minimal_change_coordinates (Ideal.ofList x) x y
    (regular_minimal M x hxm hx) hy
  have hforms := Koszul.listForm_coordinate_change x y e he
  let iso := Koszul.coefficientComplexIso M x y e hforms
  let hi := HomologicalComplex.homologyMapIso iso 1
  have hx₁ : Subsingleton (Koszul.homology M x 1) :=
    Koszul.weaklyRegular_acyclic M x hx.toIsWeaklyRegular 1 (by decide)
  let : Subsingleton ((Koszul.coefficientComplex M x).homology 1) := hx₁
  have hy₁ : Subsingleton (Koszul.homology M y 1) := by
    apply Function.Injective.subsingleton (f := hi.inv.hom)
    exact (ModuleCat.mono_iff_injective hi.inv).mp inferInstance
  have hym : ∀ a ∈ y, a ∈ IsLocalRing.maximalIdeal R := by
    intro a ha
    have hIx : Ideal.ofList x ≤ IsLocalRing.maximalIdeal R := Ideal.span_le.mpr hxm
    exact hIx (hy.1 ▸ Ideal.subset_span ha)
  have hyj : ∀ a ∈ y, a ∈ (⊥ : Ideal R).jacobson := by
    simpa only [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] using hym
  exact Koszul.degreeOne_converse_regular M y hyj hy₁

end AdvCommAlg.RegularSequence
