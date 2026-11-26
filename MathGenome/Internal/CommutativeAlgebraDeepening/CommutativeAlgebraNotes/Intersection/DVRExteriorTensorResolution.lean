import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.DVRExteriorTensorResolution
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorExactness
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Ideal
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Nakayama
import MathGenome.Internal.AlgebraCore.P103.Ch10.TotalComplexConstruction
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Exterior tensor resolutions over a discrete valuation ring

Coefficient reduction commutes with the exterior tensor construction and with
the signed total complex. Separate exactness over the residue field and
Nakayama's lemma give exactness of the total in positive degrees.
-/

namespace CommutativeAlgebraNotes.Intersection.DVRExteriorTensorResolution

open ExteriorTensorProduct IsLocalRing TensorProduct
open scoped ExteriorTensorProduct TensorProduct Pointwise DirectSum

noncomputable section

variable (V : Type*) [CommRing V] [IsLocalRing V]

theorem reduce_surjective (σ : Type*) : Function.Surjective (reduce V σ) := by
  intro f
  choose g hg using fun i => residue_surjective (R := V) (MvPowerSeries.coeff i f)
  exact ⟨g, MvPowerSeries.ext hg⟩

theorem reductionRing : Spec.ReductionRing := by
  intro V _ _ _ π hπ σ
  refine ⟨reduce_surjective V σ, ?_⟩
  have h : RingHom.ker (residue V) = Ideal.span {π} := by
    rw [ker_residue, ← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
  rw [reduce, MvPowerSeries.ker_map_of_fg _ (by rw [h]; exact Submodule.fg_span (Set.finite_singleton _)),
    h, Ideal.map_span, Set.image_singleton]

section Quotient

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (r : A) (M : Type*) [AddCommGroup M] [Module A M]
variable (hs : Function.Surjective (algebraMap A B))
variable (hk : RingHom.ker (algebraMap A B) = Ideal.span {r})

/-- A surjective scalar extension with principal kernel computes the module quotient. -/
def quotientBaseChange : QuotSMulTop r M ≃ₗ[A] B ⊗[A] M :=
  QuotSMulTop.equivQuotTensor r M ≪≫ₗ
    TensorProduct.congr
      (LinearEquiv.ofBijective
        { toFun := Ideal.Quotient.lift _ (algebraMap A B)
            (fun x hx => RingHom.mem_ker.mp (show x ∈ RingHom.ker (algebraMap A B) by rwa [hk]))
          map_add' := map_add _
          map_smul' := fun a x => by
            obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
            simp [Algebra.smul_def, ← map_mul] }
        ⟨by
          intro x y
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
          intro hab
          apply Ideal.Quotient.eq.mpr
          rw [← hk, RingHom.mem_ker, map_sub, sub_eq_zero]
          exact hab,
        fun y => by
          obtain ⟨a, rfl⟩ := hs y
          exact ⟨Ideal.Quotient.mk _ a, rfl⟩⟩)
      (LinearEquiv.refl A M)

@[simp]
theorem quotientBaseChange_mk (m : M) :
    quotientBaseChange r M hs hk (Submodule.Quotient.mk m) = 1 ⊗ₜ[A] m := by
  simp [quotientBaseChange, QuotSMulTop.equivQuotTensor]
  change (algebraMap A B 1) ⊗ₜ[A] m = _
  rw [map_one]

end Quotient

theorem fibreQuotient : Spec.FibreQuotient := by
  intro V _ _ _ π hπ σ M _ _
  obtain ⟨hs, hk⟩ := reductionRing V π hπ σ
  exact ⟨quotientBaseChange (MvPowerSeries.C π) M hs hk, quotientBaseChange_mk _ _ _ _⟩

section ExteriorBaseChange

variable (a b : ℕ)

local notation "k" => ResidueField V
local notation "A" => X V a
local notation "B" => Y V b
local notation "C" => S V a b
local notation "Ak" => X k a
local notation "Bk" => Y k b
local notation "Ck" => S k a b

local instance : Algebra A Ck :=
  ((reduce V (Fin a ⊕ YIndex b)).comp (includeX V a b).toRingHom).toAlgebra

local instance : Algebra B Ck :=
  ((reduce V (Fin a ⊕ YIndex b)).comp (includeY V a b).toRingHom).toAlgebra

local instance : IsScalarTower A C Ck :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance : IsScalarTower B C Ck :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance : IsScalarTower A Ak Ck :=
  IsScalarTower.of_algebraMap_eq fun f => (MvPowerSeries.rename_map (f := Sum.inl) (residue V) f).symm

local instance : IsScalarTower B Bk Ck :=
  IsScalarTower.of_algebraMap_eq fun f => (MvPowerSeries.rename_map (f := Sum.inr) (residue V) f).symm

variable (M N : Type*) [AddCommGroup M] [Module (X V a) M] [AddCommGroup N] [Module (Y V b) N]

local notation "Mk" => Fibre V (Fin a) M
local notation "Nk" => Fibre V (YIndex b) N

/-- Base change of the joint ring and of both input modules commutes with exterior tensor. -/
def exteriorFibreEquiv :
    Fibre V (Fin a ⊕ YIndex b) (Product V a b M N) ≃ₗ[Ck] Product k a b Mk Nk :=
  (AlgebraTensorModule.assoc B C Ck Ck (C ⊗[A] M) N).symm ≪≫ₗ
    AlgebraTensorModule.congr
      (AlgebraTensorModule.cancelBaseChange A C Ck Ck M ≪≫ₗ
        (AlgebraTensorModule.cancelBaseChange A Ak Ck Ck M).symm)
      (LinearEquiv.refl B N) ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange B Bk Ck (Ck ⊗[Ak] Mk) N).symm

@[simp]
theorem exteriorFibreEquiv_tmul (s : C) (m : M) (n : N) :
    exteriorFibreEquiv V a b M N (fibreMk V (Fin a ⊕ YIndex b) ((s ⊗ₜ[A] m) ⊗ₜ[B] n)) =
      ((reduce V _ s) ⊗ₜ[Ak] fibreMk V (Fin a) m) ⊗ₜ[Bk] fibreMk V (YIndex b) n := by
  simp [exteriorFibreEquiv, Algebra.smul_def]
  rfl

end ExteriorBaseChange

theorem exteriorFibre : Spec.ExteriorFibre := by
  intro V _ _ a b M N _ _ _ _
  exact ⟨exteriorFibreEquiv V a b M N, exteriorFibreEquiv_tmul V a b M N⟩

set_option backward.isDefEq.respectTransparency false in
theorem specialFibre : Spec.SpecialFibre := by
  intro V _ _ _ π hπ a b M N _ _ _ _
  let C := S V a b
  let Ck := S (ResidueField V) a b
  let σ := Fin a ⊕ YIndex b
  let T := Product V a b M N
  let Tk := Product (ResidueField V) a b (Fibre V (Fin a) M) (Fibre V (YIndex b) N)
  letI : Module C Tk := Module.compHom Tk (reduce V σ)
  let r : C := MvPowerSeries.C π
  obtain ⟨e, he⟩ := fibreQuotient V π hπ σ T
  let F := exteriorFibreEquiv V a b M N
  let E : QuotSMulTop r T ≃ₗ[C] Tk :=
    { toAddEquiv := e.toAddEquiv.trans F.toAddEquiv
      map_smul' := fun s x => by
        change F (e (s • x)) = (reduce V σ s) • F (e x)
        rw [e.map_smul, ← IsScalarTower.algebraMap_smul Ck, F.map_smul]
        rfl }
  refine ⟨E, fun s m n => ?_⟩
  change F (e (Submodule.Quotient.mk _)) = _
  rw [he]
  exact exteriorFibreEquiv_tmul V a b M N s m n

section ExteriorMaps

variable (a b : ℕ)

local notation "k" => ResidueField V
local notation "A" => X V a
local notation "B" => Y V b
local notation "C" => S V a b
local notation "Ak" => X (ResidueField V) a
local notation "Bk" => Y (ResidueField V) b
local notation "Ck" => S (ResidueField V) a b

variable {M M' N N' : Type*}
  [AddCommGroup M] [Module (X V a) M] [AddCommGroup M'] [Module (X V a) M']
  [AddCommGroup N] [Module (Y V b) N] [AddCommGroup N'] [Module (Y V b) N']

theorem exteriorFibreEquiv_natural (f : M →ₗ[A] M') (g : N →ₗ[B] N') :
    (exteriorFibreEquiv V a b M' N').toLinearMap ∘ₗ
        (ExteriorTensorProduct.map f g).baseChange Ck =
      ExteriorTensorProduct.map (f.baseChange Ak) (g.baseChange Bk) ∘ₗ
        (exteriorFibreEquiv V a b M N).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro r t
  rw [tmul_eq_smul_one_tmul r t]
  simp only [map_smul]
  congr 1
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul x n =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [add_tmul, tmul_add, map_add] using congrArg₂ (· + ·) hx hy
    | tmul s m =>
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, ExteriorTensorProduct.map_tmul]
      change exteriorFibreEquiv V a b M' N' (fibreMk V _ _) =
        ExteriorTensorProduct.map (f.baseChange Ak) (g.baseChange Bk)
          (exteriorFibreEquiv V a b M N (fibreMk V _ ((s ⊗ₜ[A] m) ⊗ₜ[B] n)))
      rw [exteriorFibreEquiv_tmul, exteriorFibreEquiv_tmul]
      rfl

omit [IsLocalRing V] in
private theorem rightExact_in_left
    {L : Type*} [AddCommGroup L] [Module (X V a) L]
    (f : L →ₗ[A] M) (g : M →ₗ[A] M') (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (ExteriorTensorProduct.map f (LinearMap.id : N →ₗ[B] N))
      (ExteriorTensorProduct.map g (LinearMap.id : N →ₗ[B] N)) ∧
    Function.Surjective (ExteriorTensorProduct.map g (LinearMap.id : N →ₗ[B] N)) := by
  let fB := (f.baseChange C).restrictScalars B
  let gB := (g.baseChange C).restrictScalars B
  have hfB : Function.Exact fB gB := lTensor_exact C hfg hg
  have hgB : Function.Surjective gB := g.baseChange_surjective C hg
  have h₁ : (ExteriorTensorProduct.map f (LinearMap.id : N →ₗ[B] N) : _ → _) = fB.rTensor N :=
    AlgebraTensorModule.coe_rTensor (f.baseChange C)
  have h₂ : (ExteriorTensorProduct.map g (LinearMap.id : N →ₗ[B] N) : _ → _) = gB.rTensor N :=
    AlgebraTensorModule.coe_rTensor (g.baseChange C)
  rw [h₁, h₂]
  exact ⟨rTensor_exact N hfB hgB, gB.rTensor_surjective N hgB⟩

omit [IsLocalRing V] in
private theorem rightExact_in_right
    {L : Type*} [AddCommGroup L] [Module (Y V b) L]
    (f : L →ₗ[B] N) (g : N →ₗ[B] N') (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) f)
      (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) g) ∧
    Function.Surjective (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) g) := by
  have h₁ : (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) f : _ → _) =
      f.lTensor (C ⊗[A] M) := by
    unfold ExteriorTensorProduct.map
    rw [LinearMap.baseChange_id]
    exact AlgebraTensorModule.coe_lTensor f
  have h₂ : (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) g : _ → _) =
      g.lTensor (C ⊗[A] M) := by
    unfold ExteriorTensorProduct.map
    rw [LinearMap.baseChange_id]
    exact AlgebraTensorModule.coe_lTensor g
  rw [h₁, h₂]
  exact ⟨lTensor_exact _ hfg hg, g.lTensor_surjective _ hg⟩

end ExteriorMaps

section PrincipalQuotients

variable {R : Type*} [CommRing R]
variable {L M N : Type*} [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
variable {r : R} {f : L →ₗ[R] M} {g : M →ₗ[R] N}

private theorem quotient_mk_zero_iff {U : Type*} [AddCommGroup U] [Module R U] (u : U) :
    (Submodule.Quotient.mk u : QuotSMulTop r U) = 0 ↔ ∃ v : U, r • v = u := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- A short exact sequence stays left exact modulo an element regular on the cokernel. -/
theorem quotientMap_injective (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hr : Function.Injective (fun n : N => r • n)) :
    Function.Injective (QuotSMulTop.map r f) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change (Submodule.Quotient.mk (f x) : QuotSMulTop r M) = 0 at hq
  obtain ⟨y, hy⟩ := (quotient_mk_zero_iff _).mp hq
  have hgfx := hfg.apply_apply_eq_zero x
  rw [← hy, map_smul] at hgfx
  have hgy : g y = 0 := hr (hgfx.trans (smul_zero _).symm)
  obtain ⟨z, hz⟩ := (hfg y).mp hgy
  exact (quotient_mk_zero_iff _).mpr ⟨z, hf (by rw [map_smul, hz, hy])⟩

/-- A regular element stays regular on the cokernel when the first map stays injective modulo it. -/
theorem coker_smul_injective (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hr : Function.Injective (fun m : M => r • m))
    (hf : Function.Injective (QuotSMulTop.map r f)) :
    Function.Injective (fun n : N => r • n) := by
  change Function.Injective (LinearMap.lsmul R N r)
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro n hn
  obtain ⟨x, rfl⟩ := hg n
  have hz : g (r • x) = 0 := by rw [map_smul]; exact hn
  obtain ⟨y, hy⟩ := (hfg (r • x)).mp hz
  have hyq : QuotSMulTop.map r f (Submodule.Quotient.mk y) = 0 := by
    rw [QuotSMulTop.map_apply_mk, hy]
    exact (quotient_mk_zero_iff _).mpr ⟨x, rfl⟩
  have hyq' : (Submodule.Quotient.mk y : QuotSMulTop r L) = 0 :=
    hf (hyq.trans (map_zero _).symm)
  obtain ⟨z, hz⟩ := (quotient_mk_zero_iff _).mp hyq'
  have hx : f z = x := hr (show r • f z = r • x by rw [← map_smul, hz, hy])
  rw [← hx]
  exact hfg.apply_apply_eq_zero z

end PrincipalQuotients

section FibreMaps

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {L M N : Type*} [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]
variable {r : A} (hs : Function.Surjective (algebraMap A B))
  (hk : RingHom.ker (algebraMap A B) = Ideal.span {r})
variable (f : L →ₗ[A] M) (g : M →ₗ[A] N)

theorem quotientBaseChange_natural :
    (quotientBaseChange r M hs hk).toLinearMap ∘ₗ QuotSMulTop.map r f =
      (f.baseChange B).restrictScalars A ∘ₗ (quotientBaseChange r L hs hk).toLinearMap := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp

include hs hk in
theorem quotientMap_injective_iff_baseChange :
    Function.Injective (QuotSMulTop.map r f) ↔ Function.Injective (f.baseChange B) := by
  have h := congrArg DFunLike.coe (quotientBaseChange_natural hs hk f)
  change (quotientBaseChange r M hs hk) ∘ QuotSMulTop.map r f =
    (f.baseChange B) ∘ (quotientBaseChange r L hs hk) at h
  constructor
  · intro hf
    apply Function.Injective.of_comp_right (g := quotientBaseChange r L hs hk) _ (quotientBaseChange r L hs hk).surjective
    rw [← h]
    exact (quotientBaseChange r M hs hk).injective.comp hf
  · intro hf
    apply Function.Injective.of_comp (f := quotientBaseChange r M hs hk)
    rw [h]
    exact hf.comp (quotientBaseChange r L hs hk).injective

end FibreMaps

section Regularity

variable {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
variable (π : D) (hπ : Irreducible π) (a b : ℕ)

local notation "k" => ResidueField D
local notation "A" => X D a
local notation "B" => Y D b
local notation "C" => S D a b
local notation "Ak" => X (ResidueField D) a
local notation "Bk" => Y (ResidueField D) b
local notation "Ck" => S (ResidueField D) a b
local notation "πA" => (MvPowerSeries.C π : A)
local notation "πB" => (MvPowerSeries.C π : B)
local notation "πC" => (MvPowerSeries.C π : C)

variable {L M M' N N' : Type*}
  [AddCommGroup M] [Module (X D a) M] [AddCommGroup M'] [Module (X D a) M']
  [AddCommGroup N] [Module (Y D b) N] [AddCommGroup N'] [Module (Y D b) N']

set_option backward.isDefEq.respectTransparency false in
include hπ in
private theorem reducedLeft_injective [AddCommGroup L] [Module (X D a) L]
    [Module.Finite A L] [Module.Finite A M] [Module.Finite A M'] [Module.Finite B N]
    (f : L →ₗ[A] M) (g : M →ₗ[A] M') (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hr : IsSMulRegular M' πA) :
    Function.Injective (QuotSMulTop.map (M := Product D a b L N) (M' := Product D a b M N) πC
      (ExteriorTensorProduct.map f (LinearMap.id : N →ₗ[B] N))) := by
  obtain ⟨hsa, hka⟩ := reductionRing D π hπ (Fin a)
  obtain ⟨hsc, hkc⟩ := reductionRing D π hπ (Fin a ⊕ YIndex b)
  have hir := (quotientMap_injective_iff_baseChange hsa hka f).mp (quotientMap_injective hf hfg hr)
  have hgr := g.baseChange_surjective Ak hg
  have he := lTensor_exact Ak hfg hg
  have hp := (ExteriorTensorExactness.exactLeft k a b
    (Fibre D (Fin a) L) (Fibre D (Fin a) M) (Fibre D (Fin a) M') (Fibre D (YIndex b) N)
      (f.baseChange Ak) (g.baseChange Ak) ⟨hir, he, hgr⟩).1
  apply (quotientMap_injective_iff_baseChange hsc hkc _).mpr
  have h := exteriorFibreEquiv_natural D a b f (LinearMap.id : N →ₗ[B] N)
  rw [LinearMap.baseChange_id] at h
  intro x y hxy
  apply (exteriorFibreEquiv D a b L N).injective
  apply hp
  exact (DFunLike.congr_fun h x).symm.trans
    ((congrArg (exteriorFibreEquiv D a b M N) hxy).trans (DFunLike.congr_fun h y))

set_option backward.isDefEq.respectTransparency false in
include hπ in
private theorem reducedRight_injective [AddCommGroup L] [Module (Y D b) L]
    [Module.Finite A M] [Module.Finite B L] [Module.Finite B N] [Module.Finite B N']
    (f : L →ₗ[B] N) (g : N →ₗ[B] N') (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hr : IsSMulRegular N' πB) :
    Function.Injective (QuotSMulTop.map (M := Product D a b M L) (M' := Product D a b M N) πC
      (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) f)) := by
  obtain ⟨hsb, hkb⟩ := reductionRing D π hπ (YIndex b)
  obtain ⟨hsc, hkc⟩ := reductionRing D π hπ (Fin a ⊕ YIndex b)
  have hir := (quotientMap_injective_iff_baseChange hsb hkb f).mp (quotientMap_injective hf hfg hr)
  have hgr := g.baseChange_surjective Bk hg
  have he := lTensor_exact Bk hfg hg
  have hp := (ExteriorTensorExactness.exactRight k a b
    (Fibre D (Fin a) M) (Fibre D (YIndex b) L) (Fibre D (YIndex b) N) (Fibre D (YIndex b) N')
      (f.baseChange Bk) (g.baseChange Bk) ⟨hir, he, hgr⟩).1
  apply (quotientMap_injective_iff_baseChange hsc hkc _).mpr
  have h := exteriorFibreEquiv_natural D a b (LinearMap.id : M →ₗ[A] M) f
  rw [LinearMap.baseChange_id] at h
  intro x y hxy
  apply (exteriorFibreEquiv D a b M L).injective
  apply hp
  exact (DFunLike.congr_fun h x).symm.trans
    ((congrArg (exteriorFibreEquiv D a b M N) hxy).trans (DFunLike.congr_fun h y))

include hπ in
private theorem freeProduct_regular [Module.Free A M] [Module.Free B N] :
    IsSMulRegular (Product D a b M N) πC :=
  IsSMulRegular.of_ne_zero (fun h => hπ.ne_zero (MvPowerSeries.C_injective (h.trans MvPowerSeries.C.map_zero.symm)))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
include hπ in
/-- The exterior tensor product of finite modules regular for the uniformizer is
regular for the same uniformizer. The intermediate presentations have finite free middle terms. -/
theorem product_regular [Module.Finite A M] [Module.Finite B N]
    (hm : IsSMulRegular M πA) (hn : IsSMulRegular N πB) :
    IsSMulRegular (Product D a b M N) πC := by
  obtain ⟨i, f, hf⟩ := Module.Finite.exists_fin' A M
  obtain ⟨j, g, hg⟩ := Module.Finite.exists_fin' B N
  let F := Fin i → A
  let G := Fin j → B
  have hF : IsSMulRegular (Product D a b F G) πC := freeProduct_regular π hπ a b
  have hfx := LinearMap.exact_subtype_ker_map f
  have hgx := LinearMap.exact_subtype_ker_map g
  obtain ⟨hef, hsf⟩ := rightExact_in_left D a b (N := G) f.ker.subtype f hfx hf
  have hrf := reducedLeft_injective π hπ a b (N := G) f.ker.subtype f
    f.ker.injective_subtype hfx hf hm
  have hG : IsSMulRegular (Product D a b M G) πC :=
    coker_smul_injective (R := C) (L := Product D a b f.ker G)
      (M := Product D a b F G) (N := Product D a b M G) (r := πC)
      (f := ExteriorTensorProduct.map f.ker.subtype (LinearMap.id : G →ₗ[B] G))
      (g := ExteriorTensorProduct.map f (LinearMap.id : G →ₗ[B] G)) hef hsf hF hrf
  obtain ⟨heg, hsg⟩ := rightExact_in_right D a b (M := M) g.ker.subtype g hgx hg
  have hrg := reducedRight_injective π hπ a b (M := M) g.ker.subtype g
    g.ker.injective_subtype hgx hg hn
  exact coker_smul_injective (R := C) (L := Product D a b M g.ker)
    (M := Product D a b M G) (N := Product D a b M N) (r := πC)
    (f := ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) g.ker.subtype)
    (g := ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) g) heg hsg hG hrg

end Regularity

theorem uniformizerInjective : Spec.UniformizerInjective := by
  intro D _ _ _ _ π hπ a M N _ _ _ _ _ _ _ _ hm hn
  exact product_regular π hπ a a hm hn

/-- The uniformizer on the second module is carried to the same constant in the
right-variable copy. -/
theorem diagonalUniformizerInjective : Spec.DiagonalUniformizerInjective := by
  intro V _ _ _ _ π hπ a M N _ _ _ _ _ _ _ _ hm hn
  have hc : xToY V a (MvPowerSeries.C π) = MvPowerSeries.C π :=
    (xToY V a).commutes π
  have hnY : IsSMulRegular (OnY N) (MvPowerSeries.C π : Y V a) := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := (toY_bijective (P := N)).surjective x
    obtain ⟨y, rfl⟩ := (toY_bijective (P := N)).surjective y
    apply congrArg toY
    apply hn
    apply (toY_bijective (P := N)).injective
    simpa only [toY_smul, hc] using hxy
  exact product_regular π hπ a a hm hnY

section ExactReduction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {L M N : Type*} [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]
variable {r : A} (hs : Function.Surjective (algebraMap A B))
  (hk : RingHom.ker (algebraMap A B) = Ideal.span {r})
variable (f : L →ₗ[A] M) (g : M →ₗ[A] N)

include hs hk in
theorem reduction_exact_iff :
    Function.Exact (f.baseChange B) (g.baseChange B) ↔
      Function.Exact (QuotSMulTop.map r f) (QuotSMulTop.map r g) := by
  exact Function.Exact.iff_of_ladder_linearEquiv (quotientBaseChange_natural hs hk f).symm
    (quotientBaseChange_natural hs hk g).symm

variable [IsNoetherian A M]

/-- Exactness lifts across reduction by an element in the Jacobson radical
if the following module is regular for that element. -/
theorem exact_of_quotient_exact (hr : r ∈ (⊥ : Ideal A).jacobson)
    (hreg : IsSMulRegular N r) (hzero : g.comp f = 0)
    (hred : Function.Exact (QuotSMulTop.map r f) (QuotSMulTop.map r g)) :
    Function.Exact f g := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {r})
      (IsNoetherian.noetherian _) ((Ideal.span_singleton_le_iff_mem (I := (⊥ : Ideal A).jacobson)).mpr hr)
    rw [Submodule.ideal_span_singleton_smul]
    intro x hx
    have hx' : g x = 0 := hx
    have hqr : QuotSMulTop.map r g (Submodule.Quotient.mk x) = 0 := by
      simp [hx']
    obtain ⟨yq, hyq⟩ := (hred _).mp hqr
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yq
    rw [QuotSMulTop.map_apply_mk] at hyq
    have hq : (Submodule.Quotient.mk (x - f y) : QuotSMulTop r M) = 0 := by
      rw [Submodule.Quotient.mk_sub, hyq, sub_self]
    obtain ⟨z, hz⟩ := (quotient_mk_zero_iff _).mp hq
    have hz' : z ∈ LinearMap.ker g := by
      have hgf : g (f y) = 0 := DFunLike.congr_fun hzero y
      have : r • g z = 0 := by
        rw [← map_smul, hz, map_sub, hx', hgf, sub_zero]
      exact hreg.right_eq_zero_of_smul this
    apply Submodule.mem_sup.mpr
    exact ⟨f y, ⟨y, rfl⟩, r • z, Submodule.smul_mem_pointwise_smul z r _ hz', by rw [hz]; abel⟩
  · rintro x ⟨y, rfl⟩
    exact DFunLike.congr_fun hzero y

end ExactReduction

section ReducedResolution

open CategoryTheory CategoryTheory.Limits

universe u v

set_option backward.isDefEq.respectTransparency false in
theorem reducedResolution : Spec.ReducedResolution.{u,v} := by
  intro V _ _ _ π hπ σ M hM P e h
  obtain ⟨hs, hk⟩ := reductionRing V π hπ σ
  let A := MvPowerSeries σ V
  let B := MvPowerSeries σ (ResidueField V)
  let r : A := MvPowerSeries.C π
  let F := ModuleCat.extendScalars.{u,u,v} (reduce V σ)
  have hπA : r ≠ 0 := fun hz =>
    hπ.ne_zero (MvPowerSeries.C_injective (hz.trans MvPowerSeries.C.map_zero.symm))
  have reg (n : ℤ) : IsSMulRegular (P.X n) r := by
    letI := h.free n
    exact IsSMulRegular.of_ne_zero hπA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    letI := h.free i
    change Module.Free B (B ⊗[A] (P.X i))
    infer_instance
  · intro i
    letI := h.finite i
    change Module.Finite B (B ⊗[A] (P.X i))
    infer_instance
  · intro i hi
    exact F.map_isZero (h.nonnegative i hi)
  · obtain ⟨i, hi⟩ := h.bounded
    exact ⟨i, fun j hj => F.map_isZero (hi j hj)⟩
  · intro i hi
    change Function.Exact ((P.d (i + 1) i).hom.baseChange B) ((P.d i (i - 1)).hom.baseChange B)
    apply (reduction_exact_iff hs hk _ _).mpr
    by_cases h1 : i = 1
    · subst i
      exact QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
        (h.exact_pos 1 (by norm_num)) h.exact_zero hM
    · have hsub : 0 < i - 1 := by omega
      have hex := h.exact_pos (i - 1) hsub
      rw [show i - 1 + 1 = i by omega] at hex
      exact QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
        (h.exact_pos i hi) hex (reg (i - 1 - 1))
  · change Function.Exact ((P.d 1 0).hom.baseChange B) (e.hom.baseChange B)
    exact lTensor_exact B h.exact_zero h.surjective
  · change Function.Surjective (e.hom.baseChange B)
    exact e.hom.baseChange_surjective B h.surjective

end ReducedResolution

section TotalBaseChange

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Ch10.TotalComplexAssembly

universe u₁ u₂ v₁ v₂

local notation "down" => ComplexShape.down ℤ

variable {A : Type u₁} {B : Type u₂} [CommRing A] [CommRing B]
variable (F : ModuleCat.{v₁} A ⥤ ModuleCat.{v₂} B) [F.Additive]
  [PreservesColimitsOfSize.{0,0} F]
variable (K : ChainBicomplex.{u₁,v₁} A) (L : ChainBicomplex.{u₂,v₂} B)
variable (e : ∀ i j, F.obj ((K.X i).X j) ≅ (L.X i).X j)

private def componentIso (n : ℤ) :
    F.obj ((K.total down).X n) ≅ (L.total down).X n :=
  (asIso (sigmaComparison F (diagonalFamily K n))).symm ≪≫
    Sigma.mapIso (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} => e p.val.1 p.val.2)

@[reassoc]
private theorem componentIso_ι (i j n : ℤ) (h : i + j = n) :
    F.map (K.ιTotal down i j n h) ≫ (componentIso F K L e n).hom =
      (e i j).hom ≫ L.ιTotal down i j n h := by
  change F.map (Sigma.ι (diagonalFamily K n) ⟨(i, j), h⟩) ≫
    inv (sigmaComparison F (diagonalFamily K n)) ≫
      (Sigma.mapIso _).hom = (e i j).hom ≫ Sigma.ι (diagonalFamily L n) ⟨(i, j), h⟩
  rw [map_ι_comp_inv_sigmaComparison_assoc]
  exact Sigma.ι_mapIso_hom _ _

set_option backward.isDefEq.respectTransparency false in
private def totalIso
    (eh : ∀ i i' j, (e i j).hom ≫ (L.d i i').f j =
      F.map ((K.d i i').f j) ≫ (e i' j).hom)
    (ev : ∀ i j j', (e i j).hom ≫ (L.X i).d j j' =
      F.map ((K.X i).d j j') ≫ (e i j').hom) :
    (F.mapHomologicalComplex down).obj (K.total down) ≅ L.total down := by
  refine HomologicalComplex.Hom.isoOfComponents (componentIso F K L e) ?_
  intro n m hnm
  change m + 1 = n at hnm
  let cmp := sigmaComparison F (diagonalFamily K n)
  have : IsIso cmp := by dsimp [cmp]; infer_instance
  have : Epi cmp := inferInstance
  apply (cancel_epi cmp).mp
  apply Sigma.hom_ext
  rintro ⟨⟨i, j⟩, hij⟩
  change i + j = n at hij
  have hc : Sigma.ι (fun x => F.obj (diagonalFamily K n x)) ⟨(i, j), hij⟩ ≫ cmp =
      F.map (K.ιTotal down i j n hij) := ι_comp_sigmaComparison F _ _
  change (Sigma.ι (fun x => F.obj (diagonalFamily K n x)) ⟨(i,j),hij⟩ ≫
      cmp ≫ (componentIso F K L e n).hom ≫ (L.total down).d n m) =
    Sigma.ι (fun x => F.obj (diagonalFamily K n x)) ⟨(i,j),hij⟩ ≫
      cmp ≫ F.map ((K.total down).d n m) ≫ (componentIso F K L e m).hom
  rw [reassoc_of% hc, reassoc_of% hc]
  change (F.map (K.ιTotal down i j n hij) ≫
      (componentIso F K L e n).hom ≫ (L.total down).d n m) =
    F.map (K.ιTotal down i j n hij) ≫ F.map ((K.total down).d n m) ≫
      (componentIso F K L e m).hom
  rw [componentIso_ι_assoc, ← F.map_comp_assoc]
  change (e i j).hom ≫ (totalInclusion L i j n hij ≫ (total L).d n m) =
    F.map (totalInclusion K i j n hij ≫ (total K).d n m) ≫ (componentIso F K L e m).hom
  rw [chain_totalInclusion_d, chain_totalInclusion_d]
  have hi : i - 1 + j = m := by omega
  have hj : i + (j - 1) = m := by omega
  rw [K.ιTotalOrZero_eq _ _ _ _ hi, K.ιTotalOrZero_eq _ _ _ _ hj,
    L.ιTotalOrZero_eq _ _ _ _ hi, L.ιTotalOrZero_eq _ _ _ _ hj]
  simp only [Preadditive.comp_add, Functor.map_add, Preadditive.add_comp,
    Linear.comp_units_smul, Functor.map_units_smul, Linear.units_smul_comp,
    Functor.map_comp, Category.assoc, componentIso_ι]
  rw [← Category.assoc (e i j).hom, eh]
  rw [← Category.assoc (e i j).hom, ev]
  simp only [Category.assoc]

end TotalBaseChange

section ReducedTotal

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option backward.isDefEq.respectTransparency false in
theorem reducedExteriorComplex : Spec.ReducedExteriorComplex.{u,v,w} := by
  intro V _ _ a b P Q
  let F := ModuleCat.extendScalars.{u,u,max u v w} (reduce V (Fin a ⊕ YIndex b))
  let K := exteriorBicomplex V a b P Q
  let L := exteriorBicomplex (ResidueField V) a b
    (reduceComplex V (Fin a) P) (reduceComplex V (YIndex b) Q)
  letI : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v w,u,u} (reduce V (Fin a ⊕ YIndex b))).isLeftAdjoint
  letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  let e (i j : ℤ) : F.obj ((K.X i).X j) ≅ (L.X i).X j :=
    (exteriorFibreEquiv V a b (P.X i) (Q.X j)).toModuleIso
  refine ⟨totalIso F K L e ?_ ?_⟩
  · intro i i' j
    apply ModuleCat.hom_ext
    have h := (exteriorFibreEquiv_natural V a b (P.d i i').hom (LinearMap.id :
      (Q.X j) →ₗ[Y V b] (Q.X j))).symm
    rw [LinearMap.baseChange_id] at h
    exact h
  · intro i j j'
    apply ModuleCat.hom_ext
    have h := (exteriorFibreEquiv_natural V a b (LinearMap.id :
      (P.X i) →ₗ[X V a] (P.X i)) (Q.d j j').hom).symm
    rw [LinearMap.baseChange_id] at h
    exact h

end ReducedTotal

section FieldTotal

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open private map_left_injective map_right_injective from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorExactness

universe u v w
local notation "down" => ComplexShape.down ℤ

private theorem chain_exactAt_iff {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) :
    K.ExactAt i ↔ Function.Exact (K.d (i + 1) i).hom (K.d i (i - 1)).hom := by
  have hprev : (ComplexShape.down ℤ).prev i = i + 1 := ComplexShape.prev_eq' _ (by rfl)
  have hnext : (ComplexShape.down ℤ).next i = i - 1 := ComplexShape.next_eq' _ (by
    change i - 1 + 1 = i
    omega)
  rw [HomologicalComplex.exactAt_iff' K _ _ _ hprev hnext]
  exact (K.sc' (i+1) i (i-1)).moduleCat_exact_iff_range_eq_ker.trans
    (eq_comm.trans LinearMap.exact_iff.symm)

private theorem homologyMapToSingle_isIso {R : Type u} [CommRing R]
    {K : ChainComplex (ModuleCat.{v} R) ℤ} {M : ModuleCat.{v} R}
    (e : K.X 0 ⟶ M) (z : ∀ i, (ComplexShape.down ℤ).Rel i 0 → K.d i 0 ≫ e = 0)
    (hneg : IsZero (K.X (-1)))
    (hex : Function.Exact (K.d 1 0).hom e.hom) (hs : Function.Surjective e.hom) :
    IsIso (homologyMap (mkHomToSingle (K := K) (j := 0) e z) 0) := by
  let α := (shortComplexFunctor' (ModuleCat R) down 1 0 (-1)).map (mkHomToSingle e z)
  have hf : (K.sc' 1 0 (-1)).g = 0 := hneg.eq_of_tgt _ _
  have h₁ : ((single (ModuleCat R) down 0).obj M |>.sc' 1 0 (-1)).f = 0 := by
    exact (isZero_single_obj_X down 0 M 1 (by norm_num)).eq_of_src _ _
  have h₂ : ((single (ModuleCat R) down 0).obj M |>.sc' 1 0 (-1)).g = 0 := by
    exact (isZero_single_obj_X down 0 M (-1) (by norm_num)).eq_of_tgt _ _
  apply (quasiIsoAt_iff_isIso_homologyMap _ _).mp
  apply (quasiIsoAt_iff' _ 1 0 (-1)
    (ComplexShape.prev_eq' _ (by rfl)) (ComplexShape.next_eq' _ (by rfl))).mpr
  apply (ShortComplex.quasiIso_iff_of_zeros' α hf h₁ h₂).mpr
  have hα : α.τ₂ = e ≫ (singleObjXSelf down 0 M).inv := by
    change (mkHomToSingle e z).f 0 = _
    exact mkHomToSingle_f e z
  let ι := (singleObjXSelf down 0 M).inv
  have hi : Function.Injective ι.hom := (ModuleCat.mono_iff_injective ι).mp inferInstance
  have hsurj : Function.Surjective ι.hom := (ModuleCat.epi_iff_surjective ι).mp inferInstance
  have hei : Function.Exact (K.d 1 0).hom α.τ₂.hom := by
    rw [hα]
    exact hi.comp_exact_iff_exact.mpr hex
  have hsi : Function.Surjective α.τ₂.hom := by
    rw [hα]
    exact hsurj.comp hs
  exact ⟨ModuleCat.shortComplex_exact _ hei, (ModuleCat.epi_iff_surjective α.τ₂).mpr hsi⟩

private theorem exteriorIsZeroLeft {D : Type u} [CommRing D] (a b : ℕ)
    {M : ModuleCat.{v} (X D a)} (N : ModuleCat.{w} (Y D b)) (h : IsZero M) :
    IsZero (exteriorModule D a b M N) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← exteriorHom_id D a b M N, h.eq_of_src (𝟙 M) 0, exteriorHom_zero_left]

private theorem exteriorIsZeroRight {D : Type u} [CommRing D] (a b : ℕ)
    (M : ModuleCat.{v} (X D a)) {N : ModuleCat.{w} (Y D b)} (h : IsZero N) :
    IsZero (exteriorModule D a b M N) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← exteriorHom_id D a b M N, h.eq_of_src (𝟙 N) 0, exteriorHom_zero_right]

section FieldExactness

variable (k : Type u) [Field k] (a b : ℕ)

private theorem fieldExactLeft
    {L M M' : Type*} [AddCommGroup L] [Module (X k a) L] [Module.Finite (X k a) L]
    [AddCommGroup M] [Module (X k a) M] [Module.Finite (X k a) M]
    [AddCommGroup M'] [Module (X k a) M'] [Module.Finite (X k a) M']
    (N : Type*) [AddCommGroup N] [Module (Y k b) N] [Module.Finite (Y k b) N]
    (f : L →ₗ[X k a] M) (g : M →ₗ[X k a] M') (hfg : Function.Exact f g) :
    Function.Exact (ExteriorTensorProduct.map f (LinearMap.id : N →ₗ[Y k b] N))
      (ExteriorTensorProduct.map g (LinearMap.id : N →ₗ[Y k b] N)) := by
  let idN : N →ₗ[Y k b] N := LinearMap.id
  have h1 : Function.Exact f g.rangeRestrict :=
    g.range.injective_subtype.comp_exact_iff_exact.mp hfg
  have hT := (rightExact_in_left k a b (N := N) f g.rangeRestrict h1
    g.surjective_rangeRestrict).1
  have hi := map_left_injective k a b g.range.subtype g.range.injective_subtype (N := N)
  have he : ExteriorTensorProduct.map g idN =
      (ExteriorTensorProduct.map g.range.subtype idN).comp
        (ExteriorTensorProduct.map g.rangeRestrict idN) := by
    rw [← ExteriorTensorProduct.map_comp]
    simp [idN]
  change Function.Exact (ExteriorTensorProduct.map f idN) (ExteriorTensorProduct.map g idN)
  rw [he]
  exact hi.comp_exact_iff_exact.mpr hT

private theorem fieldExactRight
    {L N N' : Type*} [AddCommGroup L] [Module (Y k b) L] [Module.Finite (Y k b) L]
    [AddCommGroup N] [Module (Y k b) N] [Module.Finite (Y k b) N]
    [AddCommGroup N'] [Module (Y k b) N'] [Module.Finite (Y k b) N']
    (M : Type*) [AddCommGroup M] [Module (X k a) M] [Module.Finite (X k a) M]
    (f : L →ₗ[Y k b] N) (g : N →ₗ[Y k b] N') (hfg : Function.Exact f g) :
    Function.Exact (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[X k a] M) f)
      (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[X k a] M) g) := by
  let idM : M →ₗ[X k a] M := LinearMap.id
  have h1 : Function.Exact f g.rangeRestrict :=
    g.range.injective_subtype.comp_exact_iff_exact.mp hfg
  have hT := (rightExact_in_right k a b (M := M) f g.rangeRestrict h1
    g.surjective_rangeRestrict).1
  have hi := map_right_injective k a b g.range.subtype g.range.injective_subtype (M := M)
  have he : ExteriorTensorProduct.map idM g =
      (ExteriorTensorProduct.map idM g.range.subtype).comp
        (ExteriorTensorProduct.map idM g.rangeRestrict) := by
    rw [← ExteriorTensorProduct.map_comp]
    simp [idM]
  change Function.Exact (ExteriorTensorProduct.map idM f) (ExteriorTensorProduct.map idM g)
  rw [he]
  exact hi.comp_exact_iff_exact.mpr hT

end FieldExactness

section OneVariableComplex

variable (D : Type u) [CommRing D] (a b : ℕ)
variable (P : ChainComplex (ModuleCat.{v} (X D a)) ℤ) (N : ModuleCat.{w} (Y D b))

private def exteriorLeftComplex : ChainComplex (ModuleCat.{max u v w} (S D a b)) ℤ where
  X i := exteriorModule D a b (P.X i) N
  d i j := exteriorHom D a b (P.d i j) (𝟙 N)
  shape i j h := by rw [P.shape _ _ h]; simp
  d_comp_d' i j l _ _ := by
    rw [← exteriorHom_comp, P.d_comp_d]
    simp

end OneVariableComplex

open AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
private theorem fieldTotal_quasiIso
    (k : Type u) [Field k] (a b : ℕ)
    {M : ModuleCat.{v} (X k a)} {N : ModuleCat.{w} (Y k b)}
    [Module.Finite (X k a) M] [Module.Finite (Y k b) N]
    {P : ChainComplex (ModuleCat.{v} (X k a)) ℤ}
    {Q : ChainComplex (ModuleCat.{w} (Y k b)) ℤ}
    {eP : P.X 0 ⟶ M} {eQ : Q.X 0 ⟶ N}
    (hP : IsFiniteFreeResolution P eP) (hQ : IsFiniteFreeResolution Q eQ) :
    ∃ f : exteriorTotal k a b P Q ⟶ (single _ down 0).obj (exteriorModule k a b M N),
      QuasiIso f := by
  let K := exteriorBicomplex k a b P Q
  let L := exteriorLeftComplex k a b P N
  let T := exteriorModule k a b M N
  let α : K.flip.X 0 ⟶ L :=
    { f := fun i => exteriorHom k a b (𝟙 (P.X i)) eQ
      comm' := fun i j _ => by
        change exteriorHom k a b _ eQ ≫ exteriorHom k a b (P.d i j) _ =
          exteriorHom k a b (P.d i j) _ ≫ exteriorHom k a b _ eQ
        simp only [← exteriorHom_comp, Category.id_comp, Category.comp_id] }
  have hk i j (h : i < 0 ∨ j < 0) : IsZero ((K.X i).X j) := by
    rcases h with h | h
    · exact exteriorIsZeroLeft a b (Q.X j) (hP.nonnegative i h)
    · exact exteriorIsZeroRight a b (P.X i) (hQ.nonnegative j h)
  have hz i j (h : (ComplexShape.down ℤ).Rel j 0) : (K.X i).d j 0 ≫ α.f i = 0 := by
    have : j = 1 := by change 0 + 1 = j at h; omega
    subst j
    have hh : Q.d 1 0 ≫ eQ = 0 := ModuleCat.hom_ext hQ.exact_zero.linearMap_comp_eq_zero
    change exteriorHom k a b _ (Q.d 1 0) ≫ exteriorHom k a b _ eQ = 0
    rw [← exteriorHom_comp, hh, exteriorHom_zero_right]
  have hzero i : IsIso (homologyMap (mkHomToSingle (K := K.X i) (j := 0) (α.f i) (hz i)) 0) := by
    letI := hP.finite i
    obtain ⟨he, hs⟩ := rightExact_in_right k a b (M := P.X i)
      (Q.d 1 0).hom eQ.hom hQ.exact_zero hQ.surjective
    exact homologyMapToSingle_isIso _ _ (hk i (-1) (Or.inr (by norm_num))) he hs
  have hpos i j (hj : 0 < j) : IsZero ((K.X i).homology j) := by
    apply ExactAt.isZero_homology
    apply (chain_exactAt_iff _ _).mpr
    letI := hP.finite i
    letI := hQ.finite (j + 1)
    letI := hQ.finite j
    letI := hQ.finite (j - 1)
    exact fieldExactRight k a b (P.X i) _ _ (hQ.exact_pos j hj)
  obtain ⟨f, hf, _⟩ := chain_column_assembly K hk L α hz hzero hpos
  let β : L.X 0 ⟶ T := exteriorHom k a b eP (𝟙 N)
  have hzβ i (h : (ComplexShape.down ℤ).Rel i 0) : L.d i 0 ≫ β = 0 := by
    have : i = 1 := by change 0 + 1 = i at h; omega
    subst i
    have hh : P.d 1 0 ≫ eP = 0 := ModuleCat.hom_ext hP.exact_zero.linearMap_comp_eq_zero
    change exteriorHom k a b (P.d 1 0) _ ≫ exteriorHom k a b eP _ = 0
    rw [← exteriorHom_comp, hh, exteriorHom_zero_left]
  let g := mkHomToSingle (j := 0) β hzβ
  have hg : QuasiIso g := by
    rw [quasiIso_iff]
    intro i
    by_cases hi : i = 0
    · subst i
      apply (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
      obtain ⟨he, hs⟩ := rightExact_in_left k a b (N := N)
        (P.d 1 0).hom eP.hom hP.exact_zero hP.surjective
      exact homologyMapToSingle_isIso β hzβ (exteriorIsZeroLeft a b N
        (hP.nonnegative (-1) (by norm_num))) he hs
    · apply (quasiIsoAt_iff_exactAt' _ _ (exactAt_single_obj _ _ T i hi)).mpr
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact ExactAt.of_isZero (exteriorIsZeroLeft a b N (hP.nonnegative i hi))
      · apply (chain_exactAt_iff _ _).mpr
        letI := hP.finite (i + 1)
        letI := hP.finite i
        letI := hP.finite (i - 1)
        exact fieldExactLeft k a b N _ _ (hP.exact_pos i hi)
  exact ⟨f ≫ g, inferInstance⟩

end FieldTotal

section TotalTerms

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Ch10.TotalComplexAssembly

universe u v

local notation "down" => ComplexShape.down ℤ

variable {R : Type u} [CommRing R] (K : ChainBicomplex.{u,v} R)

private theorem totalIsZero (n : ℤ)
    (h : ∀ i j, i + j = n → IsZero ((K.X i).X j)) : IsZero ((K.total down).X n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply total_hom_ext K
  intro i j hij
  exact (h i j hij).eq_of_src _ _

private theorem totalFree (n : ℤ) (h : ∀ i j, Module.Free R ((K.X i).X j)) :
    Module.Free R ((K.total down).X n) := by
  letI (p : {p : ℤ × ℤ // p.1 + p.2 = n}) : Module.Free R (diagonalFamily K n p) :=
    h p.val.1 p.val.2
  exact Module.Free.of_equiv (totalTermEquiv K n).symm

private theorem totalFinite (n : ℤ)
    (hfin : ∀ i j, Module.Finite R ((K.X i).X j))
    (hneg : ∀ i j, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) :
    Module.Finite R ((K.total down).X n) := by
  classical
  let I := {p : ℤ × ℤ // p.1 + p.2 = n}
  let J := {p : I // 0 ≤ p.val.1 ∧ 0 ≤ p.val.2}
  let E (p : J) : Type v := diagonalFamily K n p.val
  have hfinite : Finite J := Finite.of_injective
    (fun p : J => (⟨p.val.val.1.toNat, by
      have hp := p.val.property
      have h₁ := p.property.1
      have h₂ := p.property.2
      omega⟩ : Fin (n.toNat + 1)))
    (by
      intro x y hxy
      have he := congrArg Fin.val hxy
      change x.val.val.1.toNat = y.val.val.1.toNat at he
      have hx := x.val.property
      have hy := y.val.property
      have hx₀ := x.property.1
      have hy₀ := y.property.1
      exact Subtype.ext (Subtype.ext (Prod.ext (by omega) (by omega))))
  letI := Fintype.ofFinite J
  letI (p : J) : Module.Finite R (E p) := hfin _ _
  let f : (⨁ p : J, E p) →ₗ[R] (⨁ p : I, diagonalFamily K n p) :=
    DirectSum.toModule R J _ fun p => DirectSum.lof R I (fun p => ↥(diagonalFamily K n p)) p.val
  apply Module.Finite.of_surjective ((totalTermEquiv K n).symm.toLinearMap ∘ₗ f)
  apply (totalTermEquiv K n).symm.surjective.comp
  intro z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero f⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add f _ _⟩
  | of p x =>
    by_cases hp : 0 ≤ p.val.1 ∧ 0 ≤ p.val.2
    · exact ⟨DirectSum.lof R J E ⟨p, hp⟩ x, DirectSum.toModule_lof _ _ _⟩
    · haveI : Subsingleton (diagonalFamily K n p) :=
        ModuleCat.isZero_iff_subsingleton.mp (hneg p.val.1 p.val.2 (by omega))
      rw [Subsingleton.elim x 0, map_zero]
      exact ⟨0, map_zero f⟩

set_option backward.isDefEq.respectTransparency false in
private def totalZeroIso
    (hneg : ∀ i j, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) :
    (K.X 0).X 0 ≅ (K.total down).X 0 where
  hom := totalInclusion K 0 0 0 (by rfl)
  inv := totalProjection K 0 0 0 (by rfl)
  hom_inv_id := totalInclusion_projection_self K 0 0 0 rfl
  inv_hom_id := by
    change totalProjection K 0 0 0 rfl ≫ totalInclusion K 0 0 0 rfl = 𝟙 ((total K).X 0)
    apply total_hom_ext K
    intro i j hij
    by_cases h : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp [← Category.assoc, totalInclusion_projection_self]
    · exact (hneg i j (by omega)).eq_of_src _ _

end TotalTerms

section Augmentation

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Ch10.TotalComplexAssembly

universe u v w
local notation "down" => ComplexShape.down ℤ

variable (D : Type u) [CommRing D] (a b : ℕ)
variable {M : ModuleCat.{v} (X D a)} {N : ModuleCat.{w} (Y D b)}
variable {P : ChainComplex (ModuleCat.{v} (X D a)) ℤ}
variable {Q : ChainComplex (ModuleCat.{w} (Y D b)) ℤ}
variable (eP : P.X 0 ⟶ M) (eQ : Q.X 0 ⟶ N)
variable (hP : IsFiniteFreeResolution P eP) (hQ : IsFiniteFreeResolution Q eQ)

local notation "K" => exteriorBicomplex D a b P Q

include hP hQ in
private theorem exteriorBicomplex_nonnegative (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero (((K).X i).X j) := by
  rcases h with h | h
  · exact exteriorIsZeroLeft a b (Q.X j) (hP.nonnegative i h)
  · exact exteriorIsZeroRight a b (P.X i) (hQ.nonnegative j h)

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency false in
include hP hQ in
private theorem exteriorTotal_augmentation :
    ∃ e : (exteriorTotal D a b P Q).X 0 ⟶ exteriorModule D a b M N,
      Function.Exact ((exteriorTotal D a b P Q).d 1 0).hom e.hom ∧
      Function.Surjective e.hom ∧ (K).ιTotal down 0 0 0 rfl ≫ e = exteriorHom D a b eP eQ := by
  let Z := totalZeroIso K (exteriorBicomplex_nonnegative D a b eP eQ hP hQ)
  let e := Z.inv ≫ exteriorHom D a b eP eQ
  have he : (K).ιTotal down 0 0 0 rfl ≫ e = exteriorHom D a b eP eQ := by
    change Z.hom ≫ Z.inv ≫ _ = _
    simp
  let i10 := (K).ιTotal down 1 0 1 rfl
  let i01 := (K).ιTotal down 0 1 1 rfl
  let d := (exteriorTotal D a b P Q).d 1 0
  have hd10 : i10 ≫ d = exteriorHom D a b (P.d 1 0) (𝟙 (Q.X 0)) ≫ Z.hom := by
    change totalInclusion K 1 0 1 rfl ≫ (total K).d 1 0 = _
    rw [chain_totalInclusion_d]
    rw [(K).ιTotalOrZero_eq _ _ _ _ (show (1 : ℤ) - 1 + 0 = 0 by norm_num)]
    have hz : ((K).X 1).d 0 (0 - 1) = 0 :=
      (exteriorBicomplex_nonnegative D a b eP eQ hP hQ 1 (0 - 1) (Or.inr (by norm_num))).eq_of_tgt _ _
    rw [hz, zero_comp, smul_zero, add_zero]
    rfl
  have hd01 : i01 ≫ d = exteriorHom D a b (𝟙 (P.X 0)) (Q.d 1 0) ≫ Z.hom := by
    change totalInclusion K 0 1 1 rfl ≫ (total K).d 1 0 = _
    rw [chain_totalInclusion_d]
    rw [(K).ιTotalOrZero_eq _ _ _ _ (show (0 : ℤ) + (1 - 1) = 0 by norm_num)]
    have hz : ((K).d 0 (0 - 1)).f 1 = 0 :=
      (exteriorBicomplex_nonnegative D a b eP eQ hP hQ (0 - 1) 1 (Or.inl (by norm_num))).eq_of_tgt _ _
    rw [hz, zero_comp, zero_add, Int.negOnePow_zero, one_smul]
    rfl
  have hPz : P.d 1 0 ≫ eP = 0 := ModuleCat.hom_ext hP.exact_zero.linearMap_comp_eq_zero
  have hQz : Q.d 1 0 ≫ eQ = 0 := ModuleCat.hom_ext hQ.exact_zero.linearMap_comp_eq_zero
  have hde : d ≫ e = 0 := by
    apply total_hom_ext K
    intro i j hij
    by_cases h₁ : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h₁
      change i10 ≫ d ≫ e = i10 ≫ _
      rw [← Category.assoc i10, hd10, Category.assoc]
      change _ ≫ ((K).ιTotal down 0 0 0 rfl ≫ e) = _
      rw [he, ← exteriorHom_comp, hPz, exteriorHom_zero_left, comp_zero]
    by_cases h₂ : i = 0 ∧ j = 1
    · obtain ⟨rfl, rfl⟩ := h₂
      change i01 ≫ d ≫ e = i01 ≫ _
      rw [← Category.assoc i01, hd01, Category.assoc]
      change _ ≫ ((K).ιTotal down 0 0 0 rfl ≫ e) = _
      rw [he, ← exteriorHom_comp, hQz, exteriorHom_zero_right, comp_zero]
    exact (exteriorBicomplex_nonnegative D a b eP eQ hP hQ i j (by omega)).eq_of_src _ _
  let f0 := (exteriorHom D a b eP (𝟙 (Q.X 0))).hom
  let f1 := (exteriorHom D a b eP (𝟙 (Q.X 1))).hom
  let g := (exteriorHom D a b (𝟙 M) eQ).hom
  let p := (exteriorHom D a b (P.d 1 0) (𝟙 (Q.X 0))).hom
  let q := (exteriorHom D a b (𝟙 (P.X 0)) (Q.d 1 0)).hom
  let q' := (exteriorHom D a b (𝟙 M) (Q.d 1 0)).hom
  have hef0 : Function.Exact p f0 := (rightExact_in_left D a b (N := Q.X 0)
    (P.d 1 0).hom eP.hom hP.exact_zero hP.surjective).1
  have hsf0 : Function.Surjective f0 := (rightExact_in_left D a b (N := Q.X 0)
    (P.d 1 0).hom eP.hom hP.exact_zero hP.surjective).2
  have hsf1 : Function.Surjective f1 := (rightExact_in_left D a b (N := Q.X 1)
    (P.d 1 0).hom eP.hom hP.exact_zero hP.surjective).2
  have ⟨heg, hsg⟩ : Function.Exact q' g ∧ Function.Surjective g :=
    rightExact_in_right D a b (M := M) (Q.d 1 0).hom eQ.hom hQ.exact_zero hQ.surjective
  have hgf : g.comp f0 = e.hom.comp Z.hom.hom := by
    apply congrArg ModuleCat.Hom.hom
    change _ ≫ _ = (K).ιTotal down 0 0 0 rfl ≫ e
    rw [he, ← exteriorHom_comp, Category.comp_id, Category.id_comp]
  have hfq : f0.comp q = q'.comp f1 := by
    apply congrArg ModuleCat.Hom.hom
    change exteriorHom D a b _ _ ≫ exteriorHom D a b _ _ =
        exteriorHom D a b _ _ ≫ exteriorHom D a b _ _
    simp only [← exteriorHom_comp, Category.comp_id, Category.id_comp]
  refine ⟨e, ?_, ?_, he⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨x0, rfl⟩ := Z.toLinearEquiv.surjective x
      change ↥(exteriorModule D a b (P.X 0) (Q.X 0)) at x0
      have hgx : g (f0 x0) = 0 := (DFunLike.congr_fun hgf x0).trans hx
      obtain ⟨y', hy'⟩ := (heg _).mp hgx
      obtain ⟨y, rfl⟩ := hsf1 y'
      change q' (f1 y) = f0 x0 at hy'
      have hres : f0 (x0 - q y) = 0 := by
        rw [map_sub, show f0 (q y) = q' (f1 y) from DFunLike.congr_fun hfq y, hy', sub_self]
      obtain ⟨z, hz⟩ := (hef0 _).mp hres
      have h₁ : d.hom (i10.hom z) = Z.hom.hom (p z) :=
        DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hd10) z
      have h₂ : d.hom (i01.hom y) = Z.hom.hom (q y) :=
        DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hd01) y
      refine ⟨i10.hom z + i01.hom y, ?_⟩
      rw [map_add, h₁, h₂, hz, ← map_add, sub_add_cancel]
      rfl
    · rintro ⟨y, rfl⟩
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hde) y
  · have h : Function.Surjective (e.hom.comp Z.hom.hom) := hgf ▸ hsg.comp hsf0
    exact Function.Surjective.of_comp h

end Augmentation

section Resolution

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P103.Ch10.TotalComplexAssembly

universe u v w

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
theorem exteriorResolution : Spec.ExteriorResolution.{u,v,w} := by
  intro V _ _ _ _ π hπ a M N _ _ _ _ hM hN P Q eP eQ hP hQ
  let K := exteriorBicomplex V a a P Q
  let D := exteriorTotal V a a P Q
  let A := S V a a
  let Ak := S (ResidueField V) a a
  let σ := Fin a ⊕ YIndex a
  let r : A := MvPowerSeries.C π
  have hreg : r ≠ 0 := by
    intro hz
    exact hπ.ne_zero (MvPowerSeries.C_injective (hz.trans MvPowerSeries.C.map_zero.symm))
  have hbase : π ∈ maximalIdeal V := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hrad : r ∈ (⊥ : Ideal A).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simpa [r, IsLocalRing.mem_maximalIdeal] using hbase
  have hquadrant := exteriorBicomplex_nonnegative V a a eP eQ hP hQ
  have hfree (n : ℤ) : Module.Free A (D.X n) := by
    apply totalFree K n
    intro i j
    letI := hP.free i
    letI := hQ.free j
    change Module.Free A (Product V a a (P.X i) (Q.X j))
    infer_instance
  have hfinite (n : ℤ) : Module.Finite A (D.X n) := by
    refine totalFinite K n (fun i j => ?_) hquadrant
    letI := hP.finite i
    letI := hQ.finite j
    change Module.Finite A (Product V a a (P.X i) (Q.X j))
    infer_instance
  have hneg (n : ℤ) (hn : n < 0) : IsZero (D.X n) :=
    totalIsZero K n (fun i j hij => hquadrant i j (by omega))
  have hbound : ∃ b : ℕ, ∀ n : ℤ, (b : ℤ) < n → IsZero (D.X n) := by
    obtain ⟨bP, hbP⟩ := hP.bounded
    obtain ⟨bQ, hbQ⟩ := hQ.bounded
    refine ⟨bP + bQ, fun n hn => totalIsZero K n (fun i j hij => ?_)⟩
    by_cases hi : (bP : ℤ) < i
    · exact exteriorIsZeroLeft a a (Q.X j) (hbP i hi)
    · exact exteriorIsZeroRight a a (P.X i) (hbQ j (by omega))
  have hPk := reducedResolution V π hπ (Fin a) M hM P eP hP
  have hQk := reducedResolution V π hπ (YIndex a) N hN Q eQ hQ
  let Mk := (ModuleCat.extendScalars.{u,u,v} (reduce V (Fin a))).obj M
  let Nk := (ModuleCat.extendScalars.{u,u,w} (reduce V (YIndex a))).obj N
  letI : Module.Finite (X (ResidueField V) a) Mk := by
    change Module.Finite (X (ResidueField V) a) (Fibre V (Fin a) M)
    infer_instance
  letI : Module.Finite (Y (ResidueField V) a) Nk := by
    change Module.Finite (Y (ResidueField V) a) (Fibre V (YIndex a) N)
    infer_instance
  obtain ⟨f, hf⟩ := fieldTotal_quasiIso (ResidueField V) a a (M := Mk) (N := Nk) hPk hQk
  obtain ⟨eI⟩ := reducedExteriorComplex V a a P Q
  obtain ⟨hs, hk⟩ := reductionRing V π hπ σ
  obtain ⟨e, he, hse, hformula⟩ := exteriorTotal_augmentation V a a eP eQ hP hQ
  refine ⟨e, ⟨hfree, hfinite, hneg, hbound, ?_, he, hse⟩, hformula, ?_⟩
  swap
  · have hz (i : ℤ) (hi : (ComplexShape.down ℤ).Rel i 0) : D.d i 0 ≫ e = 0 := by
      have : i = 1 := by change 0 + 1 = i at hi; omega
      subst i
      exact ModuleCat.hom_ext he.linearMap_comp_eq_zero
    let g := mkHomToSingle (K := D) (j := 0) e hz
    have : IsIso (homologyMap g 0) :=
      homologyMapToSingle_isIso e hz (hneg (-1) (by norm_num)) he hse
    exact ⟨asIso (homologyMap g 0) ≪≫ singleObjHomologySelfIso _ _ _⟩
  intro i hi
  have hqi : QuasiIsoAt (eI.hom ≫ f) i := inferInstance
  have hz := exactAt_single_obj (ComplexShape.down ℤ) 0 (exteriorModule (ResidueField V) a a Mk Nk)
    i (ne_of_gt hi)
  have hfibre := (quasiIsoAt_iff_exactAt' (eI.hom ≫ f) i hz).mp hqi
  have hred : Function.Exact ((D.d (i + 1) i).hom.baseChange Ak)
      ((D.d i (i - 1)).hom.baseChange Ak) :=
    (chain_exactAt_iff _ _).mp hfibre
  letI := hfinite i
  letI := hfree (i - 1)
  exact exact_of_quotient_exact (D.d (i + 1) i).hom (D.d i (i - 1)).hom
    hrad (IsSMulRegular.of_ne_zero hreg)
    (congrArg ModuleCat.Hom.hom (D.d_comp_d (i + 1) i (i - 1)))
    ((reduction_exact_iff hs hk _ _).mp hred)

end Resolution

end

end CommutativeAlgebraNotes.Intersection.DVRExteriorTensorResolution
