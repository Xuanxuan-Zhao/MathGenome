import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.KoszulFlatDeformationModels
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalArtinAlgebras
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Basis.Prod
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Resolution

/-! Flat polynomial models of complete intersections over local Artin algebras. -/

universe u v

namespace CommutativeAlgebraNotes.KoszulFlatDeformationModels

open KoszulFlatDeformationModelsSpec
open scoped TensorProduct

noncomputable section

private theorem coefficient_baseChange_tmul {k : Type u} [Field k]
    (A : LocalArtinAlgebra.{u,v} k) (n : ℕ)
    (c : k) (p : MvPolynomial (Fin n) A) :
    MvPolynomial.algebraTensorAlgEquiv A k (c ⊗ₜ[A] p) =
      c • MvPolynomial.map A.residue.toRingHom p :=
  MvPolynomial.algebraTensorAlgEquiv_tmul A k c p

/-- Tensoring the presentation with the residue field reduces the equations coefficientwise. -/
theorem canonicalSpecialFibre : CanonicalSpecialFibre.{u,v} := by
  intro k _ A n g f hf
  let e : k ⊗[A] MvPolynomial (Fin n) A ≃ₐ[k] MvPolynomial (Fin n) k :=
    MvPolynomial.algebraTensorAlgEquiv A k
  let i : MvPolynomial (Fin n) A →ₐ[A] k ⊗[A] MvPolynomial (Fin n) A :=
    Algebra.TensorProduct.includeRight
  have he : ((Ideal.ofList g).map i).map (e : _ →+* _) = Ideal.ofList f := by
    change ((Ideal.ofList g).map i.toRingHom).map e.toRingHom = _
    rw [Ideal.map_map, Ideal.map_ofList, ← hf]
    congr 1
    apply List.map_congr_left
    intro p _
    change e (1 ⊗ₜ[A] p) = _
    rw [show e (1 ⊗ₜ[A] p) = _ from coefficient_baseChange_tmul A n 1 p, one_smul]
  refine ⟨(Algebra.TensorProduct.tensorQuotientEquiv k (MvPolynomial (Fin n) A) k
    (Ideal.ofList g)).trans (Ideal.quotientEquivAlg _ _ e he.symm), ?_⟩
  intro c p
  rw [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk]
  rw [show e (c ⊗ₜ[A] p) = c • MvPolynomial.map A.residue.toRingHom p from
    coefficient_baseChange_tmul A n c p]
  rfl

/-- Reduction along a surjective algebra map kills exactly the kernel-ideal multiple. -/
private theorem ker_mk_one {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (hs : Function.Surjective (algebraMap R S)) :
    LinearMap.ker (TensorProduct.mk R S M 1) =
      RingHom.ker (algebraMap R S) • (⊤ : Submodule R M) := by
  let I := RingHom.ker (algebraMap R S)
  let e : (R ⧸ I) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hs
  let E := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  have h : E.toLinearMap.comp (TensorProduct.mk R (R ⧸ I) M 1) =
      TensorProduct.mk R S M 1 := by
    ext x
    change e 1 ⊗ₜ[R] x = 1 ⊗ₜ[R] x
    rw [map_one]
  rw [← h, LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr E.injective, Submodule.comap_bot,
    LinearMap.ker_tensorProductMk]

private theorem span_eq_top_of_residue {k : Type u} [Field k]
    (A : LocalArtinAlgebra.{u,v} k) {M V : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup V] [Module A V]
    (q : M →ₗ[A] V)
    (hq : LinearMap.ker q = IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))
    (N : Submodule A M) (hN : N.map q = ⊤) : N = ⊤ := by
  let m := IsLocalRing.maximalIdeal A
  have hnil : IsNilpotent m := by
    change IsNilpotent (IsLocalRing.maximalIdeal A)
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  have htop : (⊤ : Submodule A M) ≤ N ⊔ m • ⊤ := by
    intro x _
    have hx : q x ∈ N.map q := hN.symm ▸ Submodule.mem_top
    obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp hx
    have hz : x - y ∈ m • (⊤ : Submodule A M) := by
      rw [← hq, LinearMap.mem_ker, map_sub, he, sub_self]
    exact Submodule.mem_sup.mpr ⟨y, hy, x-y, hz, by abel⟩
  have hpow (j : ℕ) : (⊤ : Submodule A M) ≤ N ⊔ m ^ j • ⊤ := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Submodule.mul_smul]
      calc
        ⊤ ≤ N ⊔ m ^ j • (⊤ : Submodule A M) := ih
        _ ≤ N ⊔ m ^ j • (N ⊔ m • ⊤) :=
          sup_le_sup_left (Submodule.smul_mono le_rfl htop) _
        _ ≤ N ⊔ m ^ j • (m • ⊤) := by
          rw [Submodule.smul_sup, ← sup_assoc]
          exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _
  obtain ⟨j, hj⟩ := hnil
  have H := hpow j
  simpa [hj] using H

private theorem exists_lifted_basis {k : Type u} [Field k]
    (A : LocalArtinAlgebra.{u,v} k) {M V ι : Type*} [AddCommGroup M] [Module A M]
    [Module.Flat A M] [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower A k V]
    (q : M →ₗ[A] V) (hq : Function.Surjective q)
    (hker : LinearMap.ker q = IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))
    (b : Module.Basis ι k V) (x : ι → M) (hx : ∀ i, q (x i) = b i) :
    ∃ B : Module.Basis ι A M, ∀ i, B i = x i := by
  let r := TensorProduct.mk A (IsLocalRing.ResidueField A) M 1
  have hr : Function.Surjective r :=
    TensorProduct.mk_surjective _ _ _ Ideal.Quotient.mk_surjective
  have hrk : LinearMap.ker r = LinearMap.ker q :=
    (LinearMap.ker_tensorProductMk (Q := M)).trans hker.symm
  let e : IsLocalRing.ResidueField A ⊗[A] M ≃ₗ[A] V :=
    (LinearMap.quotKerEquivOfSurjective r hr).symm.trans
      ((Submodule.quotEquivOfEq _ _ hrk).trans (LinearMap.quotKerEquivOfSurjective q hq))
  let : Algebra (IsLocalRing.ResidueField A) k := A.residueEquiv.toRingHom.toAlgebra
  let : Module (IsLocalRing.ResidueField A) V :=
    Module.compHom V A.residueEquiv.toRingHom
  let : IsScalarTower (IsLocalRing.ResidueField A) k V :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower A (IsLocalRing.ResidueField A) V :=
    IsScalarTower.of_algebraMap_smul fun a z => by
      change A.residueEquiv (IsLocalRing.residue A a) • z = a • z
      rw [LocalArtinAlgebra.residueEquiv_residue, ← algebraMap_smul k a z]
      rfl
  let ek := e.extendScalarsOfSurjective (S := IsLocalRing.ResidueField A)
    IsLocalRing.residue_surjective
  have he (y : M) : ek (r y) = q y := by
    change e (r y) = q y
    rw [← LinearMap.quotKerEquivOfSurjective_apply_mk r hr y]
    simp [e]
  have hli : LinearIndependent (IsLocalRing.ResidueField A) (r ∘ x) := by
    apply LinearIndependent.of_comp ek.toLinearMap
    have hh : ek.toLinearMap ∘ (r ∘ x) = b := funext fun i => (he _).trans (hx i)
    rw [hh]
    exact b.linearIndependent.restrict_scalars
      (show Function.Injective (fun a : IsLocalRing.ResidueField A => a • (1 : k)) by
        rw [show (fun a : IsLocalRing.ResidueField A => a • (1 : k)) = A.residueEquiv from
          funext fun a => mul_one (A.residueEquiv a)]
        exact A.residueEquiv.injective)
  have hsp : Submodule.span A (Set.range x) = ⊤ := by
    apply span_eq_top_of_residue A q hker
    rw [Submodule.map_span, ← Set.range_comp, show q ∘ x = b from funext hx,
      ← Submodule.restrictScalars_span A k A.residue_surjective, b.span_eq]
    rfl
  let B := Module.Basis.mk (Module.IsLocalRing.linearIndependent_of_flat x hli) hsp.ge
  exact ⟨B, Module.Basis.mk_apply _ _⟩

/-- When all residual cycles lift to cycles, a split residual differential
lifts to a map with free cokernel over the Artin algebra. -/
private theorem free_quotient_range {k : Type u} [Field k]
    (A : LocalArtinAlgebra.{u,v} k) {M N M₀ N₀ : Type*}
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    [AddCommGroup N] [Module A N] [Module.Flat A N]
    [AddCommGroup M₀] [Module k M₀] [Module A M₀] [IsScalarTower A k M₀]
    [AddCommGroup N₀] [Module k N₀] [Module A N₀] [IsScalarTower A k N₀]
    (d : M →ₗ[A] N) (d₀ : M₀ →ₗ[k] N₀)
    (q : M →ₗ[A] M₀) (r : N →ₗ[A] N₀)
    (hq : Function.Surjective q) (hr : Function.Surjective r)
    (hqk : LinearMap.ker q = IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))
    (hrk : LinearMap.ker r = IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))
    (hcomm : ∀ x, r (d x) = d₀ (q x))
    (hcycles : ∀ x, d₀ x = 0 → ∃ y, q y = x ∧ d y = 0) :
    Module.Free A (N ⧸ LinearMap.range d) := by
  classical
  obtain ⟨C, hC⟩ := (LinearMap.ker d₀).exists_isCompl
  let bC := Module.Free.chooseBasis k C
  let bK := Module.Free.chooseBasis k (LinearMap.ker d₀)
  let bM := (bC.prod bK).map (C.prodEquivOfIsCompl _ hC.symm)
  choose x hx using fun i => hq (bC i)
  choose z hz hdz using fun i => hcycles (bK i) (bK i).property
  have hbM : ∀ i, q (Sum.elim x z i) = bM i := by
    intro i
    cases i <;> simp [bM, Submodule.coe_prodEquivOfIsCompl', hx, hz]
  obtain ⟨BM, hBM⟩ := exists_lifted_basis A q hq hqk bM (Sum.elim x z) hbM
  have hdC : Function.Injective (d₀.comp C.subtype) := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro a ha
    have h : (a : M₀) = 0 :=
      Submodule.disjoint_def.mp hC.disjoint (a : M₀) ha a.property
    exact (Submodule.mem_bot _).mpr (Subtype.ext h)
  let y := (d₀.comp C.subtype) ∘ bC
  have hy : LinearIndependent k y := bC.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hdC)
  obtain ⟨W, hW⟩ := (Submodule.span k (Set.range y)).exists_isCompl
  let eN := (Submodule.span k (Set.range y)).prodEquivOfIsCompl W hW
  let bW := Module.Free.chooseBasis k W
  let bN := ((Module.Basis.span hy).prod bW).map eN
  choose w hw using fun i => hr (bW i)
  have hbN : ∀ i, r (Sum.elim (d ∘ x) w i) = bN i := by
    intro i
    change r (Sum.elim (d ∘ x) w i) =
      (((Module.Basis.span hy).prod bW i).1 : N₀) +
        (((Module.Basis.span hy).prod bW i).2 : N₀)
    cases i with
    | inl i =>
      rw [Sum.elim_inl, Function.comp_apply, hcomm, hx, Module.Basis.prod_apply_inl_fst,
        Module.Basis.prod_apply_inl_snd, Submodule.coe_zero, add_zero,
        Module.Basis.coe_span_apply]
      rfl
    | inr i =>
      rw [Sum.elim_inr, hw, Module.Basis.prod_apply_inr_fst,
        Module.Basis.prod_apply_inr_snd, Submodule.coe_zero, zero_add]
  obtain ⟨BN, hBN⟩ := exists_lifted_basis A r hr hrk bN (Sum.elim (d ∘ x) w) hbN
  have hRange : LinearMap.range d = Submodule.span A (Set.range (d ∘ x)) := by
    apply le_antisymm
    · rw [← Submodule.map_top, ← BM.span_eq, Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [hBM i]
      cases i with
      | inl i => exact Submodule.subset_span ⟨i, rfl⟩
      | inr i =>
        change d (z i) ∈ Submodule.span A (Set.range (d ∘ x))
        rw [hdz]
        exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨x i, rfl⟩
  have hLeft : BN '' Set.range Sum.inl = Set.range (d ∘ x) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => hBN (Sum.inl i))
  have hcompl := BN.linearIndependent.isCompl_span_image BN.span_eq Set.isCompl_range_inl_range_inr
  rw [hLeft, ← hRange] at hcompl
  let BN' := Module.Basis.span (BN.linearIndependent.comp Sum.inr Sum.inr_injective)
  have hRight : Set.range (BN ∘ Sum.inr) = BN '' Set.range Sum.inr := Set.range_comp _ _
  let e := (LinearMap.range d).quotientEquivOfIsCompl _ hcompl
  have : Module.Free A (Submodule.span A (Set.range (BN ∘ Sum.inr))) :=
    Module.Free.of_basis BN'
  rw [hRight] at this
  exact Module.Free.of_equiv e.symm

/-- Restrict a linear map using the specified scalar towers on its two modules. -/
private def restrictLinearMap (R : Type*) {S M N : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    (source : IsScalarTower R S M) (target : IsScalarTower R S N) (f : M →ₗ[S] N) :
    M →ₗ[R] N := by
  letI := source
  letI := target
  exact f.restrictScalars R

section KoszulReduction

open AdvCommAlg.Koszul CategoryTheory
open scoped exteriorPower

variable {k : Type u} [Field k]
variable (A : LocalArtinAlgebra.{u,v} k) (n : ℕ)

local notation "P" => MvPolynomial (Fin n) A
local notation "P₀" => MvPolynomial (Fin n) k

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem polynomialReduction_surjective : Function.Surjective (algebraMap P P₀) :=
  MvPolynomial.map_surjective _ A.residue_surjective

private theorem polynomialReduction_ker :
    RingHom.ker (algebraMap P P₀) =
      (IsLocalRing.maximalIdeal A).map (algebraMap A P) := by
  let e : k ⊗[A] P ≃ₐ[k] P₀ := MvPolynomial.algebraTensorAlgEquiv A k
  let q := TensorProduct.mk A k P 1
  have h (p : P) : e (q p) = algebraMap P P₀ p := by
    rw [MvPolynomial.algebraMap_def]
    exact (coefficient_baseChange_tmul A n 1 p).trans (one_smul _ _)
  ext p
  rw [RingHom.mem_ker, ← h, map_eq_zero_iff e e.injective,
    ← LinearMap.mem_ker, ker_mk_one A.residue_surjective]
  change p ∈ RingHom.ker A.residue.toRingHom • (⊤ : Submodule A P) ↔ _
  rw [show RingHom.ker A.residue.toRingHom = _ from A.ker_residue, Ideal.smul_top_eq_map]
  rfl

private abbrev KoszulTerm {R : Type*} [CommRing R] (g : List R) (j : ℕ) :=
  ⋀[R]^j (Fin g.length → R)

variable {A n}

private abbrev reduceList (g : List P) : List P₀ :=
  g.map (algebraMap P P₀)

local instance polynomialExteriorModule (R : Type*) [CommRing R] (n s j : ℕ) :
    Module R (⋀[MvPolynomial (Fin n) R]^j (Fin s → MvPolynomial (Fin n) R)) :=
  Module.restrictScalars R (MvPolynomial (Fin n) R) _

local instance polynomialExteriorTower (R : Type*) [CommRing R] (n s j : ℕ) :
    IsScalarTower R (MvPolynomial (Fin n) R)
      (⋀[MvPolynomial (Fin n) R]^j (Fin s → MvPolynomial (Fin n) R)) :=
  IsScalarTower.restrictScalars R (MvPolynomial (Fin n) R) _

private abbrev ResidualTerm (g : List P) (j : ℕ) :=
  P₀ ⊗[P] KoszulTerm g j

private def reduceTerm (g : List P) (j : ℕ) :
    KoszulTerm g j →ₗ[A] ResidualTerm (A := A) (n := n) g j :=
  restrictLinearMap A (polynomialExteriorTower A n g.length j) inferInstance
    (TensorProduct.mk P P₀ (KoszulTerm g j) 1)

private theorem reduceTerm_surjective (g : List P) (j : ℕ) :
    Function.Surjective (reduceTerm g j) :=
  TensorProduct.mk_surjective P (KoszulTerm g j) P₀ (polynomialReduction_surjective A n)

private theorem reduceTerm_ker (g : List P) (j : ℕ) :
    LinearMap.ker (reduceTerm g j) =
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A (KoszulTerm g j)) := by
  let tower := polynomialExteriorTower A n g.length j
  let restrict : Submodule P (KoszulTerm g j) → Submodule A (KoszulTerm g j) :=
    @Submodule.restrictScalars A P (KoszulTerm g j) _ _ _ _ _ _ tower
  change restrict (LinearMap.ker (TensorProduct.mk P P₀ (KoszulTerm g j) 1)) = _
  rw [ker_mk_one (polynomialReduction_surjective A n), polynomialReduction_ker]
  exact @Ideal.smul_restrictScalars A P (KoszulTerm g j) _ _ _ _ _ _ tower
    (IsLocalRing.maximalIdeal A) ⊤

private def residualDifferential (g : List P) (j : ℕ) :
    ResidualTerm (A := A) (n := n) g (j+1) →ₗ[k] ResidualTerm (A := A) (n := n) g j :=
  (TensorProduct.AlgebraTensorModule.lTensor P₀ P₀
    (differential (listForm g) j)).restrictScalars k

private theorem residualDifferential_comm (g : List P) (j : ℕ)
    (x : ResidualTerm (A := A) (n := n) g (j+1)) :
    TensorProduct.comm P P₀ (KoszulTerm g j) (residualDifferential g j x) =
      coefficientDifferential P₀ g j (TensorProduct.comm P P₀ (KoszulTerm g (j+1)) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p x =>
    rw [TensorProduct.comm_tmul]
    change TensorProduct.comm P P₀ (KoszulTerm g j) (p ⊗ₜ[P] differential (listForm g) j x) =
      coefficientDifferential P₀ g j (x ⊗ₜ[P] p)
    rw [TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => simp [hx, hy]

private theorem termFlat (g : List P) (j : ℕ) :
    Module.Flat A (KoszulTerm g j) := by
  let : Module.Free P (KoszulTerm g j) := Module.Free.of_basis (listBasis g j)
  exact @Module.Flat.trans A P (KoszulTerm g j) _ _ _ _ _ _
    (polynomialExteriorTower A n g.length j) inferInstance inferInstance

private theorem freeModelOfReduction (g : List P)
    (h : RingTheory.Sequence.IsRegular P₀ (reduceList g)) :
    Module.Free A (Model g) := by
  let D (j : ℕ) : KoszulTerm g (j + 1) →ₗ[A] KoszulTerm g j :=
    restrictLinearMap A (polynomialExteriorTower A n g.length (j + 1))
      (polynomialExteriorTower A n g.length j) (differential (listForm g) j)
  let : Module.Flat A (KoszulTerm g 0) := termFlat g 0
  let : Module.Flat A (KoszulTerm g 1) := termFlat g 1
  have hweak : AdvCommAlg.RegularSequence.WeaklyRegular P₀ g :=
    (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff P₀ P₀ g).mp h.toIsWeaklyRegular
  have hcycles (x : ResidualTerm (A := A) (n := n) g 1) (hx : residualDifferential g 0 x = 0) :
      ∃ y, reduceTerm g 1 y = x ∧ D 0 y = 0 := by
    let C := coefficientComplex P₀ g
    have hex : C.ExactAt 1 := (HomologicalComplex.exactAt_iff_isZero_homology C 1).mpr
      (ModuleCat.isZero_iff_subsingleton.mpr (weaklyRegular_acyclic P₀ g hweak 1 (by decide)))
    have hprev : (ComplexShape.down ℕ).prev 1 = 2 := ComplexShape.prev_eq' _ (by rfl)
    have hnext : (ComplexShape.down ℕ).next 1 = 0 := ComplexShape.next_eq' _ (by rfl)
    have hex' : (C.sc' 2 1 0).Exact := (C.exactAt_iff' 2 1 0 hprev hnext).mp hex
    have hx' : coefficientDifferential P₀ g 0 (TensorProduct.comm P P₀ (KoszulTerm g 1) x) = 0 := by
      rw [← residualDifferential_comm, hx, map_zero]
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex'
      (TensorProduct.comm P P₀ (KoszulTerm g 1) x) hx'
    change KoszulTerm g 2 ⊗[P] P₀ at z
    change coefficientDifferential P₀ g 1 z = _ at hz
    obtain ⟨w, hw⟩ := reduceTerm_surjective g 2 (TensorProduct.comm P (KoszulTerm g 2) P₀ z)
    refine ⟨D 1 w, ?_, ?_⟩
    · apply (TensorProduct.comm P P₀ (KoszulTerm g 1)).injective
      change TensorProduct.comm P P₀ (KoszulTerm g 1)
        (residualDifferential g 1 (reduceTerm g 2 w)) = _
      rw [residualDifferential_comm, hw]
      change coefficientDifferential P₀ g 1
        ((TensorProduct.comm P P₀ (KoszulTerm g 2))
          ((TensorProduct.comm P P₀ (KoszulTerm g 2)).symm z)) = _
      rw [LinearEquiv.apply_symm_apply, hz]
    · change differential (listForm g) 0 (differential (listForm g) 1 w) = 0
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun (differential_comp (listForm g) 0) w
  have hfree := free_quotient_range A (D 0) (residualDifferential g 0)
    (reduceTerm g 1) (reduceTerm g 0)
    (reduceTerm_surjective g 1) (reduceTerm_surjective g 0)
    (reduceTerm_ker g 1) (reduceTerm_ker g 0) (fun _ => rfl) hcycles
  let a : KoszulTerm g 0 →ₗ[P] Model g := (augmentationZero g).hom
  let aug := restrictLinearMap A (polynomialExteriorTower A n g.length 0) inferInstance a
  have ha : LinearMap.range (D 0) = LinearMap.ker aug := by
    have he := (augmentation_exact g).moduleCat_range_eq_ker
    change LinearMap.range (differential (listForm g) 0) = LinearMap.ker a at he
    ext x
    change x ∈ LinearMap.range (differential (listForm g) 0) ↔ x ∈ LinearMap.ker a
    rw [he]
  let e := (Submodule.quotEquivOfEq _ _ ha).trans
    (LinearMap.quotKerEquivOfSurjective aug (augmentationZero_surjective g))
  exact Module.Free.of_equiv e

end KoszulReduction

/-- A lifted regular presentation gives a free module over the Artin base. -/
theorem freeModel : FreeModel.{u,v} := by
  intro k _ A n g f hf h
  subst f
  exact freeModelOfReduction g h

/-- In particular, the lifted presentation is flat over the Artin base. -/
theorem flatModel : FlatModel.{u,v} := by
  intro k _ A n g f hf h
  let : Module.Free A (Model g) := freeModel A g f hf h
  infer_instance

end

end CommutativeAlgebraNotes.KoszulFlatDeformationModels
