import Specs.LinearAlgebraicGroups.Representation.SteinbergTensorStep
import LinearAlgebraicGroups.Representation.RestrictedSimplicity
import Mathlib.RingTheory.FiniteStability
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Coalgebra WithConv
open scoped TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.Representation.SteinbergTensorStep

open LinearAlgebraicGroups.Specs
open Specs.SteinbergTensorStep
open RationalRepresentations
open FiniteDistributions
open Specs.RelativeFrobenius (scalarTensor extendAlong)
open private counit_tmul from LinearAlgebraicGroups.Affine.RelativeFrobenius

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

private theorem scalarTensor_one_surjective {K : Type u} [Field K]
    (f : k →+* K) (hf : Function.Surjective f) (A : HopfAlgebraCategory k) :
    Function.Surjective (scalarTensor f A 1) := by
  letI := f.toAlgebra
  intro x
  change ∃ a : A, (1 : K) ⊗ₜ[k] a = (show K ⊗[k] A from x)
  induction (show K ⊗[k] A from x) using TensorProduct.inductionOn with
  | tmul c a =>
    obtain ⟨d, hd⟩ := hf c
    refine ⟨d • a, ?_⟩
    rw [← TensorProduct.smul_tmul]
    congr 1
    change f d * 1 = c
    rw [mul_one, hd]
  | add _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add ..⟩

private theorem extendAlong_finiteType {K : Type u} [Field K]
    (f : k →+* K) (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] :
    Algebra.FiniteType K (extendAlong f A) := by
  letI := f.toAlgebra
  change Algebra.FiniteType K (K ⊗[k] A)
  infer_instance

theorem frobeniusFiniteFaithfullyFlat : FrobeniusFiniteFaithfullyFlat.{u} := by
  intro k _ _ p _ _ A _ _ F hF
  let B := twistCoordinates k p 1 A
  let a : B →ₐ[k] A := F.hom.toAlgHom
  letI : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
  letI : CharP A p := CharP.of_ringHom_of_ne_zero (algebraMap k A) p
    (Fact.out : p.Prime).ne_zero
  have hsurj : Function.Surjective (iterateFrobenius k p 1) := by
    rw [iterateFrobenius_one]
    exact surjective_frobenius k p
  have hpow (x : A) : a (scalarTensor (iterateFrobenius k p 1) A 1 x) = x ^ p := by
    change F.hom _ = _
    simpa only [pow_one, one_smul] using hF 1 x
  have hinj : Function.Injective a := by
    intro x y h
    obtain ⟨x', rfl⟩ := scalarTensor_one_surjective _ hsurj A x
    obtain ⟨y', rfl⟩ := scalarTensor_one_surjective _ hsurj A y
    rw [hpow, hpow] at h
    exact congrArg _ (frobenius_inj A p h)
  letI : Algebra B A := a.toRingHom.toAlgebra
  haveI : IsScalarTower k B A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (a.commutes r).symm
  haveI : Algebra.FiniteType k B := extendAlong_finiteType _ A
  refine ⟨?_, hopfFaithfulFlatness k F hinj⟩
  rw [RingHom.finite_iff_isIntegral_and_finiteType]
  refine ⟨?_, Algebra.FiniteType.of_restrictScalars_finiteType k B A⟩
  intro x
  apply IsIntegral.of_pow (Fact.out : p.Prime).pos
  rw [← hpow x]
  exact isIntegral_algebraMap

section Twist

variable (p : ℕ) [Fact p.Prime] [CharP k p]
  {A : HopfAlgebraCategory k} {V I : Type u} [AddCommGroup V] [Module k V]
  [Fintype I] [DecidableEq I]

private theorem frobenius_matrix (C : Matrix I I A) (h : IsCoactionMatrix A C) :
    IsCoactionMatrix A (fun i j ↦ C i j ^ p) := by
  letI : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
  letI : Nontrivial (A ⊗[k] A) :=
    (Bialgebra.counitAlgHom k (A ⊗[k] A)).toRingHom.domain_nontrivial
  haveI : CharP A p := CharP.of_ringHom_of_ne_zero (algebraMap k A) p
    (Fact.out : p.Prime).ne_zero
  haveI : CharP (A ⊗[k] A) p := CharP.of_ringHom_of_ne_zero
    (algebraMap k (A ⊗[k] A)) p (Fact.out : p.Prime).ne_zero
  constructor
  · intro i j
    change Bialgebra.comulAlgHom k A (C i j ^ p) = _
    rw [map_pow, show Bialgebra.comulAlgHom k A (C i j) = _ from h.comul i j,
      ← frobenius_def, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    change (C i l ⊗ₜ[k] C l j) ^ p = _
    exact Algebra.TensorProduct.tmul_pow ..
  · intro i j
    change Bialgebra.counitAlgHom k A (C i j ^ p) = _
    rw [map_pow, show Bialgebra.counitAlgHom k A (C i j) = _ from h.counit i j]
    by_cases h' : i = j <;> simp [Matrix.one_apply, h', (Fact.out : p.Prime).ne_zero]

/-- The first Frobenius twist in a basis, with the coefficients raised to the
characteristic power. -/
def twistCoaction (b : Module.Basis I k V) (ρ : RightComodule k A V) :
    RightComodule k A V :=
  coactionOfMatrix A b (fun i j ↦ coefficients A b ρ i j ^ p)
    (frobenius_matrix p _ (coefficients_isCoactionMatrix A b ρ))

theorem twistCoaction_spec (b : Module.Basis I k V) (ρ : RightComodule k A V) :
    IsFirstTwist p A b ρ (twistCoaction p b ρ) := by
  intro i j
  unfold twistCoaction
  rw [coefficients_coactionOfMatrix]

private theorem kernel_twist_tmul (F : twistCoordinates k p 1 A ⟶ A)
    (hF : FrobeniusFormula k p 1 A F) [(kernelIdeal F).IsHopfIdeal k]
    (b : Module.Basis I k V) (ρ : RightComodule k A V) (v : V) :
    let Q := hopfQuotient A (kernelIdeal F)
    let q := hopfQuotientMap A (kernelIdeal F)
    q.hom.toAlgHom.toLinearMap.lTensor V ((twistCoaction p b ρ).coaction v) =
      v ⊗ₜ[k] (1 : Q) := by
  dsimp only
  let Q := hopfQuotient A (kernelIdeal F)
  let q := hopfQuotientMap A (kernelIdeal F)
  have hc (a : A) : q.hom (a ^ p) = algebraMap k Q ((Coalgebra.counit a) ^ p) := by
    let B := twistCoordinates k p 1 A
    let x : B := scalarTensor (iterateFrobenius k p 1) A 1 a
    let c : k := (Coalgebra.counit a) ^ p
    have hx : x - algebraMap k B c ∈ augmentationIdeal B := by
      change Bialgebra.counitAlgHom k B (x - algebraMap k B c) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_eq_zero]
      exact (counit_tmul (iterateFrobenius k p 1) A a).trans
        (iterateFrobenius_one_apply k p _)
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem F.hom.toAlgHom hx)
    change q.hom (F.hom (x - algebraMap k B c)) = 0 at hzero
    rw [map_sub, AlgHomClass.commutes, map_sub, AlgHomClass.commutes, sub_eq_zero] at hzero
    rw [show F.hom x = a ^ p from by simpa only [pow_one, one_smul] using hF 1 a] at hzero
    exact hzero
  suffices he : (q.hom.toAlgHom.toLinearMap.lTensor V).comp
      (twistCoaction p b ρ).coaction = (TensorProduct.mk k V Q).flip 1 by
    exact LinearMap.congr_fun he v
  apply b.ext
  intro j
  simp only [LinearMap.comp_apply, coaction_apply_basis A b, map_sum, LinearMap.lTensor_tmul,
    AlgHom.toLinearMap_apply]
  rw [Finset.sum_eq_single j]
  · change b j ⊗ₜ[k] q.hom (coefficients A b (twistCoaction p b ρ) j j) = b j ⊗ₜ[k] (1 : Q)
    rw [twistCoaction_spec p b ρ j j, hc, (coefficients_isCoactionMatrix A b ρ).counit]
    simp
  · intro i _ hij
    change b i ⊗ₜ[k] q.hom (coefficients A b (twistCoaction p b ρ) i j) = (0 : V ⊗[k] Q)
    rw [twistCoaction_spec p b ρ i j, hc, (coefficients_isCoactionMatrix A b ρ).counit]
    simp [hij, (Fact.out : p.Prime).ne_zero]
  · simp

open private isCoactionMatrix_extension
  from LinearAlgebraicGroups.Affine.RationalRepresentations

private theorem extendedMatrix {K : Type u} [Field K] (f : k →+* K)
    (C : Matrix I I A) (hC : IsCoactionMatrix A C) :
    IsCoactionMatrix (extendAlong f A) (fun i j ↦ scalarTensor f A 1 (C i j)) := by
  letI := f.toAlgebra
  exact isCoactionMatrix_extension A K hC

theorem relativeTwist : RelativeTwist.{u} := by
  intro k V I _ _ _ _ _ p _ _ A F hF b ρ σ hσ
  let B := twistCoordinates k p 1 A
  let f := iterateFrobenius k p 1
  let C : Matrix I I B := fun i j ↦ scalarTensor f A 1 (coefficients A b ρ i j)
  have hC : IsCoactionMatrix B C := extendedMatrix f _ (coefficients_isCoactionMatrix A b ρ)
  let δ := coactionOfMatrix B b C hC
  have hδ : coefficients B b δ = C := coefficients_coactionOfMatrix B b C hC
  refine ⟨δ, fun i j ↦ congrArg (fun M : Matrix I I B ↦ M i j) hδ, ?_, ?_⟩
  · apply b.ext
    intro j
    rw [coaction_apply_basis A b σ, LinearMap.comp_apply, coaction_apply_basis B b δ, hδ, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.lTensor_tmul, hσ i j]
    have h : F.hom (C i j) = coefficients A b ρ i j ^ p := by
      simpa only [C, f, pow_one, one_smul] using hF 1 (coefficients A b ρ i j)
    change b i ⊗ₜ[k] (coefficients A b ρ i j ^ p) = b i ⊗ₜ[k] F.hom (C i j)
    rw [h]
  · have he : σ = twistCoaction p b ρ := by
      apply coefficients_injective A b
      ext i j
      exact (hσ i j).trans (twistCoaction_spec p b ρ i j).symm
    subst σ
    intro h
    letI := h
    exact kernel_twist_tmul p F hF b ρ

end Twist

section TensorSimplicity

open private pointDistribution pair_lTensor basis_pair_apply
  from LinearAlgebraicGroups.Representation.RestrictedCyclicity
open private pair_rTensor from LinearAlgebraicGroups.Representation.FiniteDistributions
open private rationalAction from LinearAlgebraicGroups.Representation.RestrictedSimplicity
open private eq_zero_of_algHom_eq_zero
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private coords_injective from LinearAlgebraicGroups.Representation.PrimitiveLine

variable {A B : HopfAlgebraCategory k} {V W : Type u}
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

omit [FiniteDimensional k V] in
private theorem action_mem (ρ : RightComodule k A V) {N : Submodule k V}
    (hN : ρ.IsSubcomodule N) (d : Dist k A) {x : V} (hx : x ∈ N) :
    toAction ρ d x ∈ N := by
  obtain ⟨t, ht⟩ := hN ⟨x, hx⟩
  rw [toAction_pairs, ← ht, pair_rTensor]
  exact Submodule.coe_mem _

private theorem subcomodule_of_points [IsAlgClosed k] [Algebra.FiniteType k A] [IsReduced A]
    (ρ : RightComodule k A V) (N : Submodule k V)
    (hN : ∀ (g : A →ₐ[k] k) (x : N), toAction ρ (pointDistribution (toConv g)) x ∈ N) :
    ρ.IsSubcomodule N := by
  classical
  intro x
  rw [← rTensor_mkQ, LinearMap.mem_ker]
  let t := N.mkQ.rTensor A (ρ.coaction (x : V))
  let b := Module.Basis.ofVectorSpace k (V ⧸ N)
  apply coords_injective b (CommAlgCat.of k A)
  funext i
  change tensorCoordinate b i t = tensorCoordinate b i 0
  rw [map_zero]
  apply eq_zero_of_algHom_eq_zero (F := k)
  intro g
  change g.toLinearMap (tensorCoordinate b i t) = 0
  rw [← basis_pair_apply b g.toLinearMap t i]
  dsimp only [t]
  rw [pair_rTensor]
  have h : N.mkQ (pair (toConv g.toLinearMap) (ρ.coaction (x : V))) = 0 := by
    change (Submodule.Quotient.mk _ : V ⧸ N) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (toAction_pairs ρ (pointDistribution (toConv g)) x) ▸ hN g x
  rw [h, map_zero]
  rfl

private theorem action_surjective [IsAlgClosed k] [Module.Finite k B]
    (ρ : RightComodule k B V) (hρ : SimpleCoaction ρ) :
    Function.Surjective (toAction ρ) := by
  classical
  let R := Dist k B
  let a := toAction ρ
  let act := moduleStructure a
  letI : Module R V := act.module
  letI : IsScalarTower k R V := act.tower
  letI : Nontrivial V := (Submodule.nontrivial_iff k).mp (nontrivial_of_ne _ _ hρ.1)
  haveI : IsSimpleModule R V := (isSimpleModule_iff R V).mpr ⟨fun N ↦ by
    have hsub : ρ.IsSubcomodule (N.restrictScalars k) :=
      (subobjectComparison ρ a (toAction_pairs ρ) _).mpr (fun d x ↦ N.smul_mem d x.property)
    rcases hρ.2 _ hsub with h | h
    · left
      exact Submodule.restrictScalars_injective k R V h
    · right
      exact Submodule.restrictScalars_injective k R V h⟩
  let b := Module.Basis.ofVectorSpace k V
  intro f
  let f' : Module.End (Module.End R V) V :=
    { toAddHom := f.toAddHom
      map_smul' := fun c v ↦ by
        obtain ⟨x, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
          (A := R) (V := V) k).surjective c
        change f (x • v) = x • f v
        exact f.map_smul x v }
  obtain ⟨d, hd⟩ := jacobson_density f' (Finset.univ.image b)
  refine ⟨d, b.ext fun i ↦ ?_⟩
  exact (hd (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).symm

omit [FiniteDimensional k V] [FiniteDimensional k W] in
private theorem tensor_restrict_coaction (q : A ⟶ B)
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (τ : RightComodule k A (V ⊗[k] W))
    (hτ : τ.coaction = tensorCoactionMap A ρ σ)
    (v : V) (w : W) :
    q.hom.toAlgHom.toLinearMap.lTensor (V ⊗[k] W) (τ.coaction (v ⊗ₜ[k] w)) =
      (LinearMap.mul' k B).lTensor (V ⊗[k] W)
        (TensorProduct.tensorTensorTensorComm k V B W B
          (q.hom.toAlgHom.toLinearMap.lTensor V (ρ.coaction v) ⊗ₜ[k]
            q.hom.toAlgHom.toLinearMap.lTensor W (σ.coaction w))) := by
  rw [hτ]
  simp only [tensorCoactionMap, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe]
  generalize ρ.coaction v = t
  generalize σ.coaction w = s
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
    induction s using TensorProduct.inductionOn with
    | tmul y b =>
      simp [LinearMap.mul'_apply]
    | add s t hs ht => simp [TensorProduct.tmul_add, hs, ht]
  | add s t hs ht => simp [TensorProduct.add_tmul, hs, ht]

omit [FiniteDimensional k V] [FiniteDimensional k W] in
private theorem action_tensor_trivial (q : A ⟶ B)
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (ρB : RightComodule k B V) (hρB : ρB.coaction = q.hom.toAlgHom.toLinearMap.lTensor V ∘ₗ ρ.coaction)
    (τ : RightComodule k A (V ⊗[k] W))
    (hτ : τ.coaction = tensorCoactionMap A ρ σ)
    (hσ : ∀ w, q.hom.toAlgHom.toLinearMap.lTensor W (σ.coaction w) = w ⊗ₜ[k] (1 : B))
    (d : Dist k B) :
    toAction τ (distributionMap q.hom.toCoalgHom d) =
      (TensorProduct.map (toAction ρB d) LinearMap.id : (V ⊗[k] W) →ₗ[k] _) := by
  apply TensorProduct.ext'
  intro v w
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  rw [toAction_pairs, toAction_pairs]
  change pair (toConv (d.ofConv.comp q.hom.toAlgHom.toLinearMap)) _ = _
  rw [← pair_lTensor, tensor_restrict_coaction q ρ σ τ hτ, hσ, hρB, LinearMap.comp_apply]
  generalize q.hom.toAlgHom.toLinearMap.lTensor V (ρ.coaction v) = t
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
    simp [LinearMap.mul'_apply, TensorProduct.smul_tmul']
  | add s t hs ht => simp [TensorProduct.add_tmul, hs, ht]

omit [FiniteDimensional k V] [FiniteDimensional k W] in
private theorem action_tensor_point
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (τ : RightComodule k A (V ⊗[k] W)) (hτ : τ.coaction = tensorCoactionMap A ρ σ)
    (g : A →ₐ[k] k) (v : V) (w : W) :
    toAction τ (pointDistribution (toConv g)) (v ⊗ₜ[k] w) =
      toAction ρ (pointDistribution (toConv g)) v ⊗ₜ[k]
      toAction σ (pointDistribution (toConv g)) w := by
  rw [toAction_pairs, toAction_pairs, toAction_pairs, hτ]
  simp only [tensorCoactionMap, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe]
  generalize ρ.coaction v = t
  generalize σ.coaction w = s
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
    induction s using TensorProduct.inductionOn with
    | tmul y b =>
      simp [pointDistribution, LinearMap.mul'_apply, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul, smul_smul, mul_comm]
    | add s t hs ht => simp [TensorProduct.tmul_add, hs, ht]
  | add s t hs ht => simp [TensorProduct.add_tmul, hs, ht]

/-- Matrix units coming from the restricted action extract the multiplicity
space of every submodule. Invertibility of the first factor's point action
then shows that the multiplicity space is stable under the second factor. -/
private theorem simple_tensor [IsAlgClosed k] [Algebra.FiniteType k A] [IsReduced A]
    [Module.Finite k B] (q : A ⟶ B)
    (ρ : RightComodule k A V) (σ : RightComodule k A W) (ρB : RightComodule k B V)
    (hρB : ρB.coaction = q.hom.toAlgHom.toLinearMap.lTensor V ∘ₗ ρ.coaction)
    (hρ : SimpleCoaction ρB) (hσ : SimpleCoaction σ)
    (htriv : ∀ w, q.hom.toAlgHom.toLinearMap.lTensor W (σ.coaction w) = w ⊗ₜ[k] (1 : B))
    (τ : RightComodule k A (V ⊗[k] W)) (hτ : τ.coaction = tensorCoactionMap A ρ σ) :
    SimpleCoaction τ := by
  classical
  let c := Module.Basis.ofVectorSpace k V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) c
  haveI : Nontrivial V := (Submodule.nontrivial_iff k).mp (nontrivial_of_ne _ _ hρ.1)
  obtain ⟨i₀⟩ := c.index_nonempty
  let v₀ := c i₀
  have hcoord : c.repr v₀ i₀ = 1 := by simp [v₀]
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := (⊤ : Submodule k W).ne_bot_iff.mp hσ.1
    intro h
    have ht : v₀ ⊗ₜ[k] w = 0 := (Submodule.mem_bot k).mp (h ▸ Submodule.mem_top)
    have he := congrArg (fun z ↦ e z i₀) ht
    exact hw.2 (by simpa [e, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, hcoord] using he)
  intro N hN
  let D := N.comap (TensorProduct.mk k V W v₀)
  have hmat (f : V →ₗ[k] V) (x : V ⊗[k] W) (hx : x ∈ N) :
      TensorProduct.map f (LinearMap.id : W →ₗ[k] W) x ∈ N := by
    obtain ⟨d, rfl⟩ := action_surjective ρB hρ f
    rw [← action_tensor_trivial q ρ σ ρB hρB τ hτ htriv]
    exact action_mem τ hN _ hx
  have liftTo (w : W) (hw : w ∈ D) (v : V) : v ⊗ₜ[k] w ∈ N := by
    let f := (LinearMap.toSpanSingleton k V v).comp (c.coord i₀)
    have hf : f v₀ = v := by
      change c.repr v₀ i₀ • v = v
      rw [hcoord, one_smul]
    change v₀ ⊗ₜ[k] w ∈ N at hw
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply, hf] using hmat f _ hw
  have slice (x : V ⊗[k] W) (hx : x ∈ N) (i : _) : e x i ∈ D := by
    let f := (LinearMap.toSpanSingleton k V v₀).comp (c.coord i)
    have hf : (TensorProduct.mk k V W v₀).comp (Finsupp.lapply i ∘ₗ e.toLinearMap) =
        TensorProduct.map f (LinearMap.id : W →ₗ[k] W) := by
      apply TensorProduct.ext'
      intro v w
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply, e,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, TensorProduct.mk_apply,
        TensorProduct.map_tmul, LinearMap.id_apply]
      change v₀ ⊗ₜ[k] (c.repr v i • w) = (c.repr v i • v₀) ⊗ₜ[k] w
      exact TensorProduct.tmul_smul .. |>.trans (TensorProduct.smul_tmul' ..).symm
    change TensorProduct.mk k V W v₀ (e x i) ∈ N
    exact LinearMap.congr_fun hf x ▸ hmat f x hx
  have hD : σ.IsSubcomodule D := by
    apply subcomodule_of_points σ D
    intro g w
    letI := convolutionGroup A (CommAlgCat.of k k)
    let a := rationalAction ρ (toConv g)
    have h := action_mem τ hN (pointDistribution (toConv g)) (liftTo w w.property (a.symm v₀))
    rw [action_tensor_point ρ σ τ hτ] at h
    change a (a.symm v₀) ⊗ₜ[k] _ ∈ N at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  rcases hσ.2 D hD with h | h
  · left
    apply le_bot_iff.mp
    intro x hx
    suffices e x = 0 from (Submodule.mem_bot k).mpr (e.map_eq_zero_iff.mp this)
    ext i
    exact (Submodule.mem_bot k).mp (h ▸ slice x hx i)
  · right
    suffices hall : ∀ x : V ⊗[k] W, x ∈ N from top_unique (fun x _ ↦ hall x)
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul v w => exact liftTo w (h.symm ▸ Submodule.mem_top) v
    | add x y hx hy => exact N.add_mem hx hy

end TensorSimplicity

section MatrixPoints

open private basis_pair_apply pointDistribution
  from LinearAlgebraicGroups.Representation.RestrictedCyclicity
open private tensorCoordinate_evaluation
  from LinearAlgebraicGroups.Affine.RationalRepresentations

variable {A : HopfAlgebraCategory k} {V I : Type u}
  [AddCommGroup V] [Module k V] [Fintype I]

private def matrixAction (b : Module.Basis I k V) (ρ : RightComodule k A V)
    {R : TestAlgebra k} (g : A →ₐ[k] R) (v : V) (i : I) : R :=
  ∑ j, g (coefficients A b ρ i j) * algebraMap k R (b.equivFun v j)

private theorem matrixAction_eq_evaluate (b : Module.Basis I k V) (ρ : RightComodule k A V)
    {R : TestAlgebra k} (g : A →ₐ[k] R) (v : V) (i : I) :
    matrixAction b ρ g v i = tensorCoordinate b i (evaluate A ρ g v) := by
  classical
  rw [evaluate, LinearMap.comp_apply, tensorCoordinate_evaluation]
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Algebra.smul_def, mul_comm]
  rfl

private theorem matrixAction_eq_action (b : Module.Basis I k V) (ρ : RightComodule k A V)
    (g : A →ₐ[k] k) (v : V) (i : I) :
    matrixAction b ρ (R := CommAlgCat.of k k) g v i =
      b.equivFun (toAction ρ (pointDistribution (toConv g)) v) i := by
  rw [matrixAction_eq_evaluate, toAction_pairs]
  change tensorCoordinate b i (g.toLinearMap.lTensor V (ρ.coaction v)) =
    b.equivFun (pair (toConv g.toLinearMap) (ρ.coaction v)) i
  rw [basis_pair_apply, tensorCoordinate_evaluation]

variable (p : ℕ) [Fact p.Prime] [CharP k p] [DecidableEq I]

/-- Coordinates of the base-twisted vector in its scalar-twisted basis. -/
private def twistVector (b : Module.Basis I k V) (v : V) : V :=
  b.equivFun.symm (fun i ↦ frobenius k p (b.equivFun v i))

omit [DecidableEq I] in
private theorem twistVector_bijective [IsAlgClosed k] (b : Module.Basis I k V) :
    Function.Bijective (twistVector p b) := by
  change Function.Bijective (b.equivFun.symm ∘
    (fun v : I → k ↦ fun i ↦ frobenius k p (v i)) ∘ b.equivFun)
  let e : (I → k) ≃ (I → k) := Equiv.piCongrRight fun _ ↦ (frobeniusEquiv k p).toEquiv
  exact b.equivFun.symm.bijective.comp (e.bijective.comp b.equivFun.bijective)

private theorem matrixAction_twist (b : Module.Basis I k V) (ρ : RightComodule k A V)
    {R : TestAlgebra k} (g : A →ₐ[k] R) (v : V) (i : I) :
    matrixAction b (twistCoaction p b ρ) g (twistVector p b v) i =
      matrixAction b ρ g v i ^ p := by
  cases subsingleton_or_nontrivial R with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    letI : Nontrivial R := h
    letI : CharP R p := CharP.of_ringHom_of_ne_zero (algebraMap k R) p
      (Fact.out : p.Prime).ne_zero
    rw [← frobenius_def]
    simp only [matrixAction, map_sum, twistVector,
      LinearEquiv.apply_symm_apply, frobenius_def, map_pow, mul_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [twistCoaction_spec p b ρ i j, map_pow]

private theorem pointAction_twist (b : Module.Basis I k V) (ρ : RightComodule k A V)
    (g : A →ₐ[k] k) (v : V) :
    toAction (twistCoaction p b ρ) (pointDistribution (toConv g)) (twistVector p b v) =
      twistVector p b (toAction ρ (pointDistribution (toConv g)) v) := by
  apply b.equivFun.injective
  funext i
  rw [← matrixAction_eq_action, matrixAction_twist, matrixAction_eq_action]
  simp only [twistVector, LinearEquiv.apply_symm_apply, frobenius_def]

private theorem twist_simple [IsAlgClosed k] [Algebra.FiniteType k A] [IsReduced A]
    [FiniteDimensional k V] (b : Module.Basis I k V) (ρ : RightComodule k A V)
    (hρ : SimpleCoaction ρ) : SimpleCoaction (twistCoaction p b ρ) := by
  refine ⟨hρ.1, fun N hN ↦ ?_⟩
  let f := twistVector p b
  have hf := twistVector_bijective p b
  have hf0 : f 0 = 0 := by simp [f, twistVector]
  let D : Submodule k V :=
    { carrier := {v | f v ∈ N}
      zero_mem' := by change f 0 ∈ N; rw [hf0]; exact N.zero_mem
      add_mem' := fun {v w} hv hw ↦ by
        change f (v + w) ∈ N
        have he : f (v + w) = f v + f w := by
          apply b.equivFun.injective
          funext i
          simp only [f, twistVector, LinearEquiv.apply_symm_apply, map_add, Pi.add_apply]
        rw [he]
        exact N.add_mem hv hw
      smul_mem' := fun c v hv ↦ by
        change f (c • v) ∈ N
        have he : f (c • v) = frobenius k p c • f v := by
          apply b.equivFun.injective
          funext i
          simp only [f, twistVector, LinearEquiv.apply_symm_apply, map_smul,
            Pi.smul_apply, smul_eq_mul, map_mul]
        rw [he]
        exact N.smul_mem _ hv }
  have hD : ρ.IsSubcomodule D := by
    apply subcomodule_of_points ρ D
    intro g v
    change twistVector p b (toAction ρ (pointDistribution (toConv g)) (v : V)) ∈ N
    rw [← pointAction_twist p b ρ]
    exact action_mem _ hN _ v.property
  rcases hρ.2 D hD with he | he
  · left
    apply le_bot_iff.mp
    intro v hv
    obtain ⟨w, rfl⟩ := hf.surjective v
    have hw : w ∈ D := hv
    rw [he, Submodule.mem_bot] at hw
    change f w ∈ (⊥ : Submodule k V)
    rw [hw, hf0]
    exact Submodule.zero_mem _
  · right
    apply top_unique
    intro v _
    obtain ⟨w, rfl⟩ := hf.surjective v
    exact (show w ∈ D from he.symm ▸ Submodule.mem_top)

end MatrixPoints

section Realization

open Specs.SimpleClassification (SocleModel Realizes HasHighestWeight)
open Specs.RootWeightAction (Representation IsPrimitive act extendVector mem_fixedSpace
  mem_weightSpace)
open Specs.CharacterPairing (characterValue)
open Specs.AdjointRepresentation (GroupPoints)
open private fromCoaction toCoaction stable_iff
  from LinearAlgebraicGroups.Representation.PrimitiveLine
open private realizedCoaction_transport realizes_fromCoaction coactionComparison
  from LinearAlgebraicGroups.Representation.SimpleClassification
open private pointIso from LinearAlgebraicGroups.Representation.InducedSocle
open private pointCoordinates
  from LinearAlgebraicGroups.Representation.RestrictedSimplicity
open private affinePoint affinePoint_specGroupMap
  from LinearAlgebraicGroups.Representation.FlagLineBundle
open private tensorCoefficients tensorCoaction_eq
  from LinearAlgebraicGroups.Representation.TensorAndDual
open private characterEvaluation characterValue_eq_unit
  from LinearAlgebraicGroups.RootData.RootGroups
open private hopfPreimage specGroupMap_hopfPreimage
  from LinearAlgebraicGroups.Reductive.CentralTorus
open private coordinateReduced
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private finite_kernel_of_formula
  from LinearAlgebraicGroups.Representation.FiniteDistributions

variable {G : AffineAlgebraicGroup k} {A B : HopfAlgebraCategory k}
  {V W I J : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private theorem simpleCoaction_transport (e : V ≃ₗ[k] W)
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (he : (e.toLinearMap.rTensor A).comp ρ.coaction = σ.coaction.comp e.toLinearMap)
    (hρ : SimpleCoaction ρ) : SimpleCoaction σ := by
  classical
  letI : Nontrivial V := (Submodule.nontrivial_iff k).mp (nontrivial_of_ne _ _ hρ.1)
  letI : Nontrivial W := e.injective.nontrivial
  refine ⟨top_ne_bot, fun N hN ↦ ?_⟩
  let D := N.comap e.toLinearMap
  let f : N →ₗ[k] D := (e.symm.toLinearMap.comp N.subtype).codRestrict D (fun n ↦ by
    change e (e.symm n) ∈ N
    rw [LinearEquiv.apply_symm_apply]
    exact n.property)
  have hD : ρ.IsSubcomodule D := by
    intro x
    let y : N := ⟨e x, x.property⟩
    obtain ⟨t, ht⟩ := hN y
    refine ⟨f.rTensor A t, ?_⟩
    apply (LinearEquiv.rTensor A e).injective
    change (e.toLinearMap.rTensor A) (D.subtype.rTensor A (f.rTensor A t)) =
      (e.toLinearMap.rTensor A) (ρ.coaction x)
    have hf : e.toLinearMap.comp (D.subtype.comp f) = N.subtype := by
      ext n
      exact e.apply_symm_apply n
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← LinearMap.comp_apply,
      ← LinearMap.rTensor_comp, LinearMap.comp_assoc, hf, ht]
    exact (LinearMap.congr_fun he x).symm
  rcases hρ.2 D hD with h | h
  · left
    apply (Submodule.comap_injective_of_surjective e.surjective)
    rw [Submodule.comap_bot, LinearMap.ker_eq_bot.mpr e.injective]
    exact h
  · right
    apply (Submodule.comap_injective_of_surjective e.surjective)
    rwa [Submodule.comap_top]

private theorem realizes_simple (e : specGroup A ≅ G.val)
    (b : Module.Basis I k V) (δ : RightComodule k A V)
    (r : Representation G.val I) (hr : Realizes e b δ r) :
    SimpleCoaction δ ↔ PrimitiveLine.IsSimple r := by
  let d := toCoaction (pointIso e) (Pi.basisFun k I) r
  have ht := realizedCoaction_transport e b δ r hr
  have ht' : (b.equivFun.toLinearMap.rTensor A).comp δ.coaction =
      d.coaction.comp b.equivFun.toLinearMap := by
    apply LinearMap.ext
    intro v
    apply (LinearEquiv.rTensor A b.equivFun.symm).injective
    change b.equivFun.symm.toLinearMap.rTensor A
        (b.equivFun.toLinearMap.rTensor A (δ.coaction v)) =
      b.equivFun.symm.toLinearMap.rTensor A (d.coaction (b.equivFun v))
    have he : b.equivFun.symm.toLinearMap.comp b.equivFun.toLinearMap = LinearMap.id :=
      LinearMap.ext b.equivFun.symm_apply_apply
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, he, LinearMap.rTensor_id,
      LinearMap.id_apply]
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      using (LinearMap.congr_fun ht (b.equivFun v)).symm
  have hs (N : Submodule k (I → k)) : PrimitiveLine.IsStable r N ↔ d.IsSubcomodule N :=
    stable_iff coactionComparison r A (pointIso e) N
  constructor
  · intro h
    obtain ⟨hn, hm⟩ := simpleCoaction_transport b.equivFun δ d ht' h
    exact ⟨hn, fun N hN ↦ hm N ((hs N).mp hN)⟩
  · intro h
    exact simpleCoaction_transport b.equivFun.symm d δ ht
      ⟨h.1, fun N hN ↦ h.2 N ((hs N).mpr hN)⟩

private theorem realizes_restrict (a : B ⟶ A)
    (eA : specGroup A ≅ G.val) (eB : specGroup B ≅ G.val)
    (ha : specGroupMap a ≫ eB.hom = eA.hom)
    (b : Module.Basis I k V) (ρ : RightComodule k B V) (σ : RightComodule k A V)
    (hσ : σ.coaction = a.hom.toAlgHom.toLinearMap.lTensor V ∘ₗ ρ.coaction)
    (r : Representation G.val I) (hr : Realizes eB b ρ r) : Realizes eA b σ r := by
  intro R g v i
  have hp : affinePoint R g ≫ eA.hom.hom.hom =
      affinePoint R (g.comp a.hom.toAlgHom) ≫ eB.hom.hom.hom := by
    rw [← ha]
    change affinePoint R g ≫ (specGroupMap a).hom.hom ≫ eB.hom.hom.hom = _
    rw [← Category.assoc, affinePoint_specGroupMap]
  change act r R (affinePoint R g ≫ eA.hom.hom.hom) (extendVector R v) i = _
  rw [hp]
  have h := hr R (g.comp a.hom.toAlgHom) v i
  change act r R (affinePoint R (g.comp a.hom.toAlgHom) ≫ eB.hom.hom.hom)
    (extendVector R v) i = _ at h
  refine h.trans ?_
  simp only [evaluate, hσ, LinearMap.comp_apply, ← LinearMap.lTensor_comp_apply]
  rfl

private theorem act_realizes (e : specGroup A ≅ G.val)
    (b : Module.Basis I k V) (δ : RightComodule k A V)
    (r : Representation G.val I) (hr : Realizes e b δ r)
    (R : TestAlgebra k) (g : A →ₐ[k] R) (v : V) (i : I) :
    act r R (pointCoordinates e R g) (extendVector R (b.equivFun v)) i =
      matrixAction b δ g v i := by
  rw [matrixAction_eq_evaluate]
  have h := hr R g (b.equivFun v) i
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

private theorem matrixAction_tensor (b : Module.Basis I k V) (c : Module.Basis J k W)
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (R : TestAlgebra k) (g : A →ₐ[k] R) (v : V) (w : W) (i : I) (j : J) :
    matrixAction (b.tensorProduct c) (tensorCoaction A b c ρ σ) g (v ⊗ₜ[k] w) (i, j) =
      matrixAction b ρ g v i * matrixAction c σ g w j := by
  classical
  unfold matrixAction
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
  rw [tensorCoefficients, show (b.tensorProduct c).equivFun (v ⊗ₜ[k] w) (l, m) =
      c.equivFun w m * b.equivFun v l from Module.Basis.tensorProduct_repr_tmul_apply b c v w l m]
  simp only [map_mul]
  ac_rfl

private theorem tmul_ne_zero (b : Module.Basis I k V) {v : V} {w : W}
    (hv : v ≠ 0) (hw : w ≠ 0) : v ⊗ₜ[k] w ≠ 0 := by
  intro ht
  apply hv
  apply b.equivFun.injective
  funext i
  have he := congrArg (fun x ↦ TensorProduct.equivFinsuppOfBasisLeft b x i) ht
  simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_zero, Finsupp.zero_apply] at he
  simpa only [map_zero, Pi.zero_apply, Module.Basis.equivFun_apply] using
    (smul_eq_zero.mp he).resolve_right hw

private theorem tensor_twist_scalar (p : ℕ) [Fact p.Prime] [CharP k p]
    (e : specGroup A ≅ G.val) (b : Module.Basis I k V) (c : Module.Basis J k W)
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (r₁ : Representation G.val I) (r₂ : Representation G.val J)
    (h₁ : Realizes e b ρ r₁) (h₂ : Realizes e c σ r₂)
    (r : Representation G.val (I × J))
    (hr : Realizes e (b.tensorProduct c) (tensorCoaction A b c ρ (twistCoaction p c σ)) r)
    (R : TestAlgebra k) (g : GroupPoints G.val R) (v : V) (w : W) (x y : R)
    (hx : act r₁ R g (extendVector R (b.equivFun v)) = x • extendVector R (b.equivFun v))
    (hy : act r₂ R g (extendVector R (c.equivFun w)) = y • extendVector R (c.equivFun w)) :
    act r R g (extendVector R ((b.tensorProduct c).equivFun (v ⊗ₜ[k] twistVector p c w))) =
      (x * y ^ p) • extendVector R
        ((b.tensorProduct c).equivFun (v ⊗ₜ[k] twistVector p c w)) := by
  obtain ⟨a, rfl⟩ := (pointCoordinates e R).surjective g
  funext ij
  obtain ⟨i, j⟩ := ij
  rw [act_realizes e _ _ r hr, matrixAction_tensor, matrixAction_twist,
    ← act_realizes e b ρ r₁ h₁ R, ← act_realizes e c σ r₂ h₂ R, hx, hy]
  have hc : c.equivFun (twistVector p c w) j = (c.equivFun w j) ^ p := by
    simp only [twistVector, LinearEquiv.apply_symm_apply, frobenius_def]
  have ht : (b.tensorProduct c).equivFun (v ⊗ₜ[k] twistVector p c w) (i, j) =
      c.equivFun (twistVector p c w) j * b.equivFun v i :=
    Module.Basis.tensorProduct_repr_tmul_apply b c _ _ i j
  change (x * algebraMap k R (b.equivFun v i)) * (y * algebraMap k R (c.equivFun w j)) ^ p =
      (x * y ^ p) * algebraMap k R ((b.tensorProduct c).equivFun (v ⊗ₜ[k] twistVector p c w) (i, j))
  rw [ht, hc, map_mul, map_pow, mul_pow]
  ac_rfl

theorem oneStep : OneStep.{u} := by
  classical
  intro k _ _ p _ _ G _ _ P U hU η μ hη hμ hrestricted S M
  let A := S.A
  let a : M.A ⟶ A := hopfPreimage (S.groupIso.hom ≫ M.groupIso.inv)
  have ha : specGroupMap a ≫ M.groupIso.hom = S.groupIso.hom := by
    rw [show specGroupMap a = S.groupIso.hom ≫ M.groupIso.inv
      from specGroupMap_hopfPreimage _, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let ρ := restrictCoaction a M.socleCoaction
  let σ := twistCoaction p M.socleBasis ρ
  let b := S.socleBasis
  let c := M.socleBasis
  let τ := tensorCoaction A b c S.socleCoaction σ
  let r := fromCoaction (pointIso S.groupIso) (b.tensorProduct c) τ
  have hρ := restrictCoaction_coaction a M.socleCoaction
  have hM := realizes_restrict a S.groupIso M.groupIso ha c M.socleCoaction ρ hρ
    M.socleAction M.socleAction_spec
  have hτ : τ.coaction = tensorCoactionMap A S.socleCoaction σ := tensorCoaction_eq A b c _ _
  have hr : Realizes S.groupIso (b.tensorProduct c) τ r := realizes_fromCoaction S.groupIso _ _
  have hMs : SimpleCoaction ρ := (realizes_simple _ _ _ _ hM).mpr M.simple
  obtain ⟨hft, hred⟩ := coordinateReduced G A S.groupIso P.reductive.1
  letI : Algebra.FiniteType k A := hft
  letI : _root_.IsReduced (AlgebraicClosure k ⊗[k] A) := hred
  letI : _root_.IsReduced A :=
    isReduced_of_injective (Algebra.TensorProduct.includeRight : A →ₐ[k] AlgebraicClosure k ⊗[k] A)
      (Algebra.TensorProduct.includeRight_injective (algebraMap k (AlgebraicClosure k)).injective)
  let F := frobeniusPullback p 1 A
  have hF := frobeniusPullback_formula p 1 A
  letI hI : (kernelIdeal F).IsHopfIdeal k := hopfKernelIdeal k F
  let Q := hopfQuotient A (kernelIdeal F)
  let q := hopfQuotientMap A (kernelIdeal F)
  letI : Module.Finite k Q := finite_kernel_of_formula p 1 A F hF hft
  have hrestrict (α : Specs.RootWeightAction.SimpleRoot P.torus P.positive)
      (d : Specs.CharacterDescent.Cocharacter P.torus.group)
      (hd : Specs.AbstractPairing.IsAttachedCoroot P.torus α.val d) :
      Specs.CharacterPairing.pairing P.torus.group η d < (↑(p ^ 1) : ℤ) := by
    simpa only [pow_one] using hrestricted α d hd
  obtain ⟨δ, hδ, hn, hs⟩ := RestrictedSimplicity.simplicity p 1 Nat.one_pos P U hU η hη
    hrestrict S F hF hI
  have hσs : SimpleCoaction σ := twist_simple p c ρ hMs
  have hsτ : SimpleCoaction τ :=
    simple_tensor q S.socleCoaction σ δ hδ ⟨hn, hs⟩ hσs
      (kernel_twist_tmul p F hF c ρ) τ hτ
  have hrs : PrimitiveLine.IsSimple r := (realizes_simple _ _ _ _ hr).mp hsτ
  let v := S.highestVector
  let w := M.highestVector
  have hv : v ≠ 0 := fun h ↦ S.primitive.1 (by rw [show S.highestVector = 0 from h, map_zero])
  have hw : w ≠ 0 := fun h ↦ M.primitive.1 (by rw [show M.highestVector = 0 from h, map_zero])
  have hw' : twistVector p c w ≠ 0 := by
    intro hz
    apply hw
    apply (twistVector_bijective p c).injective
    rw [hz]
    simp [twistVector]
  have hscalar := tensor_twist_scalar p S.groupIso b c S.socleCoaction ρ
    S.socleAction M.socleAction S.socleAction_spec hM r hr
  have hprim : IsPrimitive r P.torus P.positive U (η * μ ^ p)
      ((b.tensorProduct c).equivFun (v ⊗ₜ[k] twistVector p c w)) := by
    refine ⟨fun h ↦ tmul_ne_zero b hv hw' ((b.tensorProduct c).equivFun.map_eq_zero_iff.mp h),
      mem_fixedSpace.mpr ?_, mem_weightSpace.mpr ?_⟩
    · intro R g
      have h₁ := mem_fixedSpace.mp S.primitive.2.1 R g
      have h₂ := mem_fixedSpace.mp M.primitive.2.1 R g
      have h := hscalar R (g ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom) v w 1 1
        (by simpa only [one_smul] using h₁) (by simpa only [one_smul] using h₂)
      simpa only [one_pow, mul_one, one_smul] using h
    · intro R g
      have h₁ := mem_weightSpace.mp S.primitive.2.2 R g
      have h₂ := mem_weightSpace.mp M.primitive.2.2 R g
      have h := hscalar R (g ≫ P.torus.inclusion.hom.hom) v w _ _ h₁ h₂
      have hval : characterValue (η * μ ^ p) R g =
          characterValue η R g * characterValue μ R g ^ p := by
        rw [characterValue_eq_unit, characterValue_eq_unit, characterValue_eq_unit]
        change ((characterEvaluation R g (η * μ ^ p) : Rˣ) : R) =
          ((characterEvaluation R g η : Rˣ) : R) * ((characterEvaluation R g μ : Rˣ) : R) ^ p
        simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
      rw [hval]
      exact h
  have hwt : HasHighestWeight P U r (η * μ ^ p) := ⟨_, hprim⟩
  have hclass := SimpleClassification.classification G P U hU
  obtain ⟨L, hL⟩ := hclass.2.2 (η * μ ^ p) (hclass.2.1 r hrs _ hwt)
  have hff := frobeniusFiniteFaithfullyFlat p A F hF
  exact ⟨a, ρ, σ, τ, r, ha, hρ, ⟨F, hF, hff⟩, twistCoaction_spec p c ρ,
    hτ, hr, hrs, hwt, L, (hL r hrs).mpr hwt⟩

end Realization

end LinearAlgebraicGroups.Representation.SteinbergTensorStep
