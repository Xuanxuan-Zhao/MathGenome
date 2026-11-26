import Specs.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis

open scoped TensorProduct
open Module

namespace LinearAlgebraicGroups.Descent.SemilinearAction

universe u v w x y

variable {k : Type u} {K : Type v} {V : Type w} {W : Type x}
variable [Field k] [Field K] [Algebra k K]
variable [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
variable [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]
variable (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W)

@[simp] theorem mem_fixed (a : V) : a ∈ ρ.fixed ↔ ∀ g, ρ.act g a = a := Iff.rfl

@[simp] theorem descentMap_tmul (r : K) (a : ρ.fixed) :
    ρ.descentMap (r ⊗ₜ[k] a) = r • (a : V) := rfl

@[simp] theorem scalarExtension_act_tmul (U : Type x) [AddCommGroup U] [Module k U]
    (g : Gal(K/k)) (r : K) (a : U) :
    (scalarExtension (k := k) (K := K) U).act g (r ⊗ₜ[k] a) = g r ⊗ₜ[k] a := rfl

@[simp] theorem tensorComparison_tmul (a : ρ.fixed) (b : τ.fixed) :
    (ρ.tensorComparison τ (a ⊗ₜ[k] b) : V ⊗[K] W) = (a : V) ⊗ₜ[K] (b : W) := rfl

@[simp] theorem unitComparison_apply (a : k) :
    (unitComparison (K := K) a : K) = algebraMap k K a := rfl

variable [FiniteDimensional k K]

/-- The sum of the Galois translates of any vector is fixed. -/
private theorem sum_act_mem_fixed (a : V) : (∑ g : Gal(K/k), ρ.act g a) ∈ ρ.fixed := by
  classical
  intro h
  rw [map_sum]
  simp only [← ρ.mul_act]
  exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)

/-- Artin independence implies that the fixed vectors span over the extension field. -/
theorem span_fixed_eq_top : Submodule.span K (ρ.fixed : Set V) = ⊤ := by
  classical
  let S := Submodule.span K (ρ.fixed : Set V)
  by_contra h
  obtain ⟨ℓ, hℓ, hS⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (p := S) (lt_top_iff_ne_top.mpr h) inferInstance
  have kills_fixed (a : V) (ha : a ∈ ρ.fixed) : ℓ a = 0 := by
    have hm := Submodule.mem_map_of_mem (f := ℓ) (Submodule.subset_span (R := K) ha)
    change ℓ a ∈ S.map ℓ at hm
    simpa only [hS, Submodule.mem_bot] using hm
  have independent : LinearIndependent K (fun g : Gal(K/k) => (g : K → K)) :=
    (linearIndependent_monoidHom K K).comp (fun g : Gal(K/k) => g.toMonoidHom)
      (fun _ _ h => AlgEquiv.ext fun a => DFunLike.congr_fun h a)
  apply hℓ
  ext a
  have vanishes (r : K) : ∑ g : Gal(K/k), ℓ (ρ.act g a) * g r = 0 := by
    have hz := kills_fixed _ (ρ.sum_act_mem_fixed (r • a))
    simpa only [map_sum, ρ.map_smul, _root_.map_smul, smul_eq_mul, mul_comm] using hz
  have coeff := (Fintype.linearIndependent_iff.mp independent) (fun g => ℓ (ρ.act g a))
    (funext fun r => by simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using vanishes r)
  simpa only [ρ.one_act, LinearMap.zero_apply] using coeff 1

/-- There is an extension-field basis consisting of fixed vectors. -/
theorem exists_fixed_basis : ∃ (s : Set V) (b : Basis s K V), ∀ i, b i ∈ ρ.fixed := by
  let b := Basis.ofSpan ρ.span_fixed_eq_top.ge
  exact ⟨_, b, fun i => Basis.ofSpan_subset ρ.span_fixed_eq_top.ge (Set.mem_range_self i)⟩

omit [FiniteDimensional k K] in
private theorem repr_act {ι : Type y} (b : Basis ι K V) (hb : ∀ i, b i ∈ ρ.fixed)
    (g : Gal(K/k)) (a : V) (i : ι) : b.repr (ρ.act g a) i = g (b.repr a i) := by
  classical
  let σ : K ≃+* K := g
  let := RingHomInvPair.of_ringEquiv σ
  let := RingHomInvPair.of_ringEquiv_symm σ
  let coord : V →ₗ[K] K := b.coord i
  let σMap : K →ₛₗ[(σ : K →+* K)] K :=
    { σ.toAddMonoidHom with map_smul' := fun r x => map_mul σ r x }
  have commute : coord.comp (ρ.operator g) = σMap.comp coord := by
    apply b.ext
    intro j
    change coord (ρ.act g (b j)) = g (coord (b j))
    rw [(hb j) g]
    by_cases h : j = i
    · subst j
      simp [coord]
    · simp [coord, Basis.coord_apply, Ne.symm h]
  exact LinearMap.congr_fun commute a

variable [IsGalois k K]

/-- A basis consisting of fixed vectors gives a basis of the fixed space
over the base field, with the same underlying vectors. -/
noncomputable def fixedBasis {ι : Type y} (b : Basis ι K V) (hb : ∀ i, b i ∈ ρ.fixed) :
    Basis ι k ρ.fixed := by
  classical
  let v : ι → ρ.fixed := fun i => ⟨b i, hb i⟩
  refine Basis.mk (v := v)
    (LinearIndependent.of_comp ρ.fixed.subtype (b.linearIndependent.restrict_scalars' k)) ?_
  intro a _
  have hbase (i : ι) : ∃ r : k, algebraMap k K r = b.repr (a : V) i := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro g
    rw [← ρ.repr_act b hb g, a.property g]
  choose r hr using hbase
  have hexpand : a = ∑ i ∈ (b.repr (a : V)).support, r i • v i := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    refine (b.linearCombination_repr (a : V)).symm.trans (Finset.sum_congr rfl ?_)
    intro i _
    change b.repr (a : V) i • b i = r i • b i
    rw [← hr, IsScalarTower.algebraMap_smul K]
  refine hexpand.symm ▸ Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))

@[simp] theorem fixedBasis_apply {ι : Type y} (b : Basis ι K V) (hb : ∀ i, b i ∈ ρ.fixed)
    (i : ι) : (ρ.fixedBasis b hb i : V) = b i := by
  simp [fixedBasis, Basis.mk_apply]

/-- The canonical scalar-extension map is bijective in arbitrary dimension. -/
theorem descent_bijective : Function.Bijective ρ.descentMap := by
  obtain ⟨_, b, hb⟩ := ρ.exists_fixed_basis
  let c := (ρ.fixedBasis b hb).baseChange K
  let e := c.equiv b (Equiv.refl _)
  have he : ρ.descentMap = e.toLinearMap := by
    apply c.ext
    intro i
    rw [LinearEquiv.coe_coe, Basis.equiv_apply]
    simp [c]
  rw [he]
  exact e.bijective

/-- The canonical descent equivalence. -/
noncomputable def descentEquiv : (K ⊗[k] ρ.fixed) ≃ₗ[K] V :=
  LinearEquiv.ofBijective ρ.descentMap ρ.descent_bijective

@[simp] theorem descentEquiv_tmul (r : K) (a : ρ.fixed) :
    ρ.descentEquiv (r ⊗ₜ[k] a) = r • (a : V) := rfl

omit [FiniteDimensional k K] [IsGalois k K] in
/-- Descent intertwines the original action with the canonical scalar-extension action. -/
theorem descent_equivariant :
    (scalarExtension ρ.fixed).Equivariant ρ ρ.descentMap := by
  intro g a
  induction a using TensorProduct.inductionOn with
  | tmul r a => simp only [scalarExtension_act_tmul, descentMap_tmul, ρ.map_smul, a.property g]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [FiniteDimensional k K] [IsGalois k K] in
/-- Base change of a linear map commutes with the coefficient action. -/
theorem scalarExtension_equivariant {U : Type w} {T : Type x}
    [AddCommGroup U] [Module k U] [AddCommGroup T] [Module k T] (f : U →ₗ[k] T) :
    (scalarExtension U).Equivariant (scalarExtension T) (f.baseChange K) := by
  intro g a
  induction a using TensorProduct.inductionOn with
  | tmul r a => simp only [scalarExtension_act_tmul, LinearMap.baseChange_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [FiniteDimensional k K] [IsGalois k K] in
/-- The canonical descent maps commute with restriction and then scalar extension. -/
theorem descent_natural (f : V →ₗ[K] W) (hf : ρ.Equivariant τ f) :
    f.comp ρ.descentMap = τ.descentMap.comp ((ρ.restrict τ f hf).baseChange K) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro r a
  change f (r • (a : V)) = r • f (a : V)
  exact f.map_smul r (a : V)

/-- Extension of a map of fixed spaces, transported by the canonical descent isomorphisms. -/
noncomputable def extend (f : ρ.fixed →ₗ[k] τ.fixed) : V →ₗ[K] W :=
  τ.descentMap.comp ((f.baseChange K).comp ρ.descentEquiv.symm.toLinearMap)

theorem extend_comp_descent (f : ρ.fixed →ₗ[k] τ.fixed) :
    (ρ.extend τ f).comp ρ.descentMap = τ.descentMap.comp (f.baseChange K) := by
  apply LinearMap.ext
  intro a
  change τ.descentMap (f.baseChange K (ρ.descentEquiv.symm (ρ.descentEquiv a))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem extend_equivariant (f : ρ.fixed →ₗ[k] τ.fixed) : ρ.Equivariant τ (ρ.extend τ f) := by
  have h (a : K ⊗[k] ρ.fixed) :
      ρ.extend τ f (ρ.descentMap a) = τ.descentMap (f.baseChange K a) :=
    LinearMap.congr_fun (ρ.extend_comp_descent τ f) a
  intro g a
  obtain ⟨b, rfl⟩ := ρ.descent_bijective.surjective a
  rw [← ρ.descent_equivariant g b, h, scalarExtension_equivariant f g,
    τ.descent_equivariant, h]

/-- Equivariant linear maps correspond precisely to linear maps of fixed spaces. -/
noncomputable def homEquiv :
    {f : V →ₗ[K] W // ρ.Equivariant τ f} ≃ (ρ.fixed →ₗ[k] τ.fixed) where
  toFun f := ρ.restrict τ f.1 f.2
  invFun f := ⟨ρ.extend τ f, ρ.extend_equivariant τ f⟩
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    obtain ⟨b, rfl⟩ := ρ.descent_bijective.surjective a
    exact LinearMap.congr_fun
      ((ρ.extend_comp_descent τ _).trans (ρ.descent_natural τ f.1 f.2).symm) b
  right_inv f := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change ρ.extend τ f (a : V) = (f a : W)
    have h := LinearMap.congr_fun (ρ.extend_comp_descent τ f) (1 ⊗ₜ[k] a)
    simpa only [LinearMap.comp_apply, descentMap_tmul, LinearMap.baseChange_tmul, one_smul]
      using h

theorem hom_equivalence :
    ∃ e : {f : V →ₗ[K] W // ρ.Equivariant τ f} ≃ (ρ.fixed →ₗ[k] τ.fixed),
      (∀ f, e f = ρ.restrict τ f.1 f.2) ∧
      ∀ f, (e.symm f).1.comp ρ.descentMap = τ.descentMap.comp (f.baseChange K) :=
  ⟨ρ.homEquiv τ, fun _ => rfl, ρ.extend_comp_descent τ⟩

/-- Taking fixed vectors of a coefficient action recovers the original space. -/
theorem scalarExtension_bijective (U : Type x) [AddCommGroup U] [Module k U] :
    Function.Bijective (scalarExtensionComparison (k := k) (K := K) U) := by
  let b := Module.Free.chooseBasis k U
  let σ := scalarExtension (k := k) (K := K) U
  have hb (i : _) : b.baseChange K i ∈ σ.fixed := by
    intro g
    simp [σ]
  let c := σ.fixedBasis (b.baseChange K) hb
  let e := b.equiv c (Equiv.refl _)
  have he : scalarExtensionComparison (k := k) (K := K) U = e.toLinearMap := by
    apply b.ext
    intro i
    rw [LinearEquiv.coe_coe, Basis.equiv_apply]
    apply Subtype.ext
    change (1 : K) ⊗ₜ[k] b i = (c i : K ⊗[k] U)
    simp [c]
  rw [he]
  exact e.bijective

/-- The comparison to fixed vectors in the tensor product is an isomorphism. -/
theorem tensor_bijective : Function.Bijective (ρ.tensorComparison τ) := by
  obtain ⟨_, b, hb⟩ := ρ.exists_fixed_basis
  obtain ⟨_, c, hc⟩ := τ.exists_fixed_basis
  have hbc (ij : _) : b.tensorProduct c ij ∈ (ρ.tensor τ).fixed := by
    intro g
    rw [Basis.tensorProduct_apply', tensor_act_tmul, (hb ij.1) g, (hc ij.2) g]
  let fixedTensorBasis := (ρ.tensor τ).fixedBasis (b.tensorProduct c) hbc
  let tensorOfFixedBases := (ρ.fixedBasis b hb).tensorProduct (τ.fixedBasis c hc)
  let e := tensorOfFixedBases.equiv fixedTensorBasis (Equiv.refl _)
  have he : ρ.tensorComparison τ = e.toLinearMap := by
    apply tensorOfFixedBases.ext
    intro ij
    rw [LinearEquiv.coe_coe, Basis.equiv_apply]
    apply Subtype.ext
    simp only [tensorOfFixedBases, fixedTensorBasis, Basis.tensorProduct_apply',
      tensorComparison_tmul, fixedBasis_apply, Equiv.refl_apply]
  rw [he]
  exact e.bijective

/-- The fixed vectors in the tensor unit are exactly the embedded base field. -/
theorem unit_bijective : Function.Bijective (unitComparison (k := k) (K := K)) := by
  constructor
  · intro a b hab
    exact (algebraMap k K).injective (congrArg Subtype.val hab)
  · intro a
    obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (a : K)).mpr a.property
    exact ⟨r, Subtype.ext hr⟩

/-- In finite dimension, descent preserves the dimension of the space. -/
theorem finiteDimensional_fixed [FiniteDimensional K V] :
    FiniteDimensional k ρ.fixed ∧ finrank k ρ.fixed = finrank K V := by
  obtain ⟨_, b, hb⟩ := ρ.exists_fixed_basis
  let c := ρ.fixedBasis b hb
  have := b.linearIndependent.finite
  exact ⟨c.finiteDimensional_of_finite,
    (Module.finrank_eq_nat_card_basis c).trans (Module.finrank_eq_nat_card_basis b).symm⟩

/-- The canonical equivalence between the tensor of fixed spaces and the fixed
space of the tensor. -/
noncomputable def tensorEquiv : (ρ.fixed ⊗[k] τ.fixed) ≃ₗ[k] (ρ.tensor τ).fixed :=
  LinearEquiv.ofBijective (ρ.tensorComparison τ) (ρ.tensor_bijective τ)

/-- The base field identifies with the fixed vectors of the tensor unit. -/
noncomputable def unitEquiv : k ≃ₗ[k] (unit (k := k) (K := K)).fixed :=
  LinearEquiv.ofBijective unitComparison unit_bijective

/-- Descent applies to every extension-field vector space, using its
canonical restriction of scalars. -/
theorem descent_restrictScalars
    {A : Type w} [AddCommGroup A] [Module K A] (σ : SemilinearAction k K A) :
    letI := Module.compHom A (algebraMap k K)
    letI := IsScalarTower.of_compHom k K A
    Function.Bijective σ.descentMap :=
  letI := Module.compHom A (algebraMap k K)
  letI := IsScalarTower.of_compHom k K A
  σ.descent_bijective

omit [FiniteDimensional k K] [IsGalois k K]

/-- Restriction to fixed spaces preserves identity morphisms. -/
theorem restrict_id :
    ρ.restrict ρ LinearMap.id (fun _ _ => rfl) = LinearMap.id :=
  LinearMap.ext fun _ => Subtype.ext rfl

variable {X : Type y} [AddCommGroup X] [Module K X] [Module k X] [IsScalarTower k K X]

/-- Restriction to fixed spaces preserves composition. -/
theorem restrict_comp (υ : SemilinearAction k K X)
    (f : V →ₗ[K] W) (hf : ρ.Equivariant τ f) (g : W →ₗ[K] X) (hg : τ.Equivariant υ g) :
    ρ.restrict υ (g.comp f) (fun s a => by simp only [LinearMap.comp_apply, hf s a, hg s (f a)]) =
      (τ.restrict υ g hg).comp (ρ.restrict τ f hf) :=
  LinearMap.ext fun _ => Subtype.ext rfl

/-- The canonical comparison from a base space to coefficient-action fixed
vectors is natural in the base space. -/
theorem scalarExtensionComparison_natural {U : Type w} {T : Type x}
    [AddCommGroup U] [Module k U] [AddCommGroup T] [Module k T] (f : U →ₗ[k] T)
    (hf : (scalarExtension (K := K) U).Equivariant (scalarExtension T) (f.baseChange K)) :
    ((scalarExtension (K := K) U).restrict (scalarExtension T) (f.baseChange K) hf).comp
        (scalarExtensionComparison U) =
      (scalarExtensionComparison T).comp f := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact LinearMap.baseChange_tmul f (1 : K) a

universe z
variable {Y : Type z} [AddCommGroup Y] [Module K Y] [Module k Y] [IsScalarTower k K Y]

omit [Module k V] [IsScalarTower k K V] [Module k W] [IsScalarTower k K W]
  [Module k X] [IsScalarTower k K X] [Module k Y] [IsScalarTower k K Y] in
/-- Tensoring equivariant maps gives an equivariant map for the diagonal actions. -/
theorem tensor_equivariant (υ : SemilinearAction k K X) (ω : SemilinearAction k K Y)
    (f : V →ₗ[K] X) (hf : ρ.Equivariant υ f) (g : W →ₗ[K] Y) (hg : τ.Equivariant ω g) :
    (ρ.tensor τ).Equivariant (υ.tensor ω) (TensorProduct.map f g) := by
  intro s a
  induction a using TensorProduct.inductionOn with
  | tmul a b => simp only [tensor_act_tmul, TensorProduct.map_tmul, hf s a, hg s b]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The tensor comparison commutes with the induced maps of fixed spaces. -/
theorem tensor_natural (υ : SemilinearAction k K X) (ω : SemilinearAction k K Y)
    (f : V →ₗ[K] X) (hf : ρ.Equivariant υ f) (g : W →ₗ[K] Y) (hg : τ.Equivariant ω g)
    (hfg : (ρ.tensor τ).Equivariant (υ.tensor ω) (TensorProduct.map f g)) :
    ((ρ.tensor τ).restrict (υ.tensor ω) (TensorProduct.map f g) hfg).comp
        (ρ.tensorComparison τ) =
      (υ.tensorComparison ω).comp (TensorProduct.map (ρ.restrict υ f hf) (τ.restrict ω g hg)) := by
  apply TensorProduct.ext'
  intro a b
  apply Subtype.ext
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, tensorComparison_tmul]
  exact TensorProduct.map_tmul f g (a : V) (b : W)

/-- The tensor comparison respects the reassociation of three factors. -/
theorem tensorComparison_assoc (υ : SemilinearAction k K X)
    (a : (ρ.fixed ⊗[k] τ.fixed) ⊗[k] υ.fixed) :
    TensorProduct.assoc K V W X
      (↑((ρ.tensor τ).tensorComparison υ (TensorProduct.map (ρ.tensorComparison τ)
        LinearMap.id a))) =
    (↑(ρ.tensorComparison (τ.tensor υ) (TensorProduct.map LinearMap.id
      (τ.tensorComparison υ) (TensorProduct.assoc k ρ.fixed τ.fixed υ.fixed a))) :
        V ⊗[K] (W ⊗[K] X)) := by
  induction a using TensorProduct.inductionOn with
  | tmul ab c =>
    induction ab using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorComparison_tmul,
        TensorProduct.assoc_tmul]
    | add a b ha hb =>
      simp only [TensorProduct.add_tmul, map_add, Submodule.coe_add, ha, hb]
  | add a b ha hb =>
    simp only [map_add, Submodule.coe_add, ha, hb]

/-- The tensor comparison respects the left unit identification. -/
theorem tensorComparison_lid (a : k ⊗[k] ρ.fixed) :
    TensorProduct.lid K V
      (↑((unit (k := k) (K := K)).tensorComparison ρ
        (TensorProduct.map unitComparison LinearMap.id a))) =
    ((TensorProduct.lid k ρ.fixed) a : V) := by
  induction a using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorComparison_tmul,
      TensorProduct.lid_tmul, unitComparison_apply, Submodule.coe_smul_of_tower,
      IsScalarTower.algebraMap_smul]
  | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]

/-- The tensor comparison respects the right unit identification. -/
theorem tensorComparison_rid (a : ρ.fixed ⊗[k] k) :
    TensorProduct.rid K V
      (↑(ρ.tensorComparison (unit (k := k) (K := K))
        (TensorProduct.map LinearMap.id unitComparison a))) =
    ((TensorProduct.rid k ρ.fixed) a : V) := by
  induction a using TensorProduct.inductionOn with
  | tmul a r =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorComparison_tmul,
      TensorProduct.rid_tmul, unitComparison_apply, Submodule.coe_smul_of_tower,
      IsScalarTower.algebraMap_smul]
  | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]

end LinearAlgebraicGroups.Descent.SemilinearAction
