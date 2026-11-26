import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import Mathlib.RingTheory.Finiteness.Small

noncomputable section

open CategoryTheory IsLocalRing
open scoped BigOperators TensorProduct Pointwise
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
  (Tor torLeftEquiv tor_finite_length_of_tensor)
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
  (intersectionEuler regularLocalDimension ringKrullDim_eq_regularLocalDimension)
open P103.Specs.Ch10.Comparison (LeftResolution)
open P103.Specs.Ch12.TorBaseChange (coefficientComplex)
open P103.Ch12.TorBaseChange (extendedResolution extendedResolution_projective homologyIso
  flat_base_change)

namespace CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion

open _root_.CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion.Specs
  (CompletedRing CompletedModule completedModuleCat)
universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The canonical scalar-extension model of the completion of a finite module. -/
def completionTensorEquiv (L : Type v) [AddCommGroup L] [Module R L] [Module.Finite R L] :
    CompletedRing R ⊗[R] L ≃ₗ[CompletedRing R] CompletedModule R L := by
  let A := CompletedRing R
  let : Small.{u} L := Module.Finite.small.{u} R L
  let e : Shrink.{u} L ≃ₗ[R] L := Shrink.linearEquiv R L
  let : Module.Finite R (Shrink.{u} L) := Module.Finite.equiv e.symm
  let f := AdvCommAlg.CohenMacaulay.completion_tensor_comparison R (Shrink.{u} L)
  let comm := AdvCommAlg.RegularSequence.rightTensorComm (R := R) (S := A) (Shrink.{u} L) A
  let equiv := (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e.symm).trans
    (comm.symm.trans (f.choose.trans (AdicCompletion.congr (maximalIdeal R) e)))
  have he : equiv.toLinearMap = AdicCompletion.ofTensorProduct (maximalIdeal R) L := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a l
    change AdicCompletion.congr (maximalIdeal R) e (f.choose (e.symm l ⊗ₜ[R] a)) =
      a • AdicCompletion.of (maximalIdeal R) L l
    rw [f.choose_spec, map_smul, AdicCompletion.congr_apply, AdicCompletion.map_of,
      LinearEquiv.coe_coe, e.apply_symm_apply]
  refine LinearEquiv.ofBijective (AdicCompletion.ofTensorProduct (maximalIdeal R) L) ?_
  rw [← he]
  exact equiv.bijective

theorem completion_tensor_comparison (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (L : Type v) [AddCommGroup L] [Module R L] [Module.Finite R L] :
    ∃ e : CompletedRing R ⊗[R] L ≃ₗ[CompletedRing R] CompletedModule R L,
      ∀ (a : CompletedRing R) (l : L), e (a ⊗ₜ[R] l) = a • AdicCompletion.of (maximalIdeal R) L l :=
  ⟨completionTensorEquiv L, fun _ _ => rfl⟩

theorem completion_module_finite (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (L : Type v) [AddCommGroup L] [Module R L] [Module.Finite R L] :
    Module.Finite (CompletedRing R) (CompletedModule R L) :=
  Module.Finite.equiv (completionTensorEquiv (R := R) L)

theorem completion_module_dimension (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (L : Type v) [AddCommGroup L] [Module R L] [Module.Finite R L] :
    Module.supportDim (CompletedRing R) (CompletedModule R L) = Module.supportDim R L := by
  let : Small.{u} L := Module.Finite.small.{u} R L
  let e : Shrink.{u} L ≃ₗ[R] L := Shrink.linearEquiv R L
  let : Module.Finite R (Shrink.{u} L) := Module.Finite.equiv e.symm
  rw [← Module.supportDim_eq_of_equiv (AdicCompletion.congr (maximalIdeal R) e),
    AdvCommAlg.CohenMacaulay.completion_dimension R (Shrink.{u} L),
    Module.supportDim_eq_of_equiv e]

theorem completion_ring_dimension (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim (CompletedRing R) = ringKrullDim R := by
  have h := AdvCommAlg.CohenMacaulay.completion_dimension R R
  change Module.supportDim (CompletedRing R) (CompletedRing R) = Module.supportDim R R at h
  simpa only [Module.supportDim_self_eq_ringKrullDim] using h

theorem completion_regular_local (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (CompletedRing R) := by
  let : IsNoetherianRing (CompletedRing R) :=
    AdvCommAlg.CohenMacaulay.Specs.completionNoetherian R
  apply (IsRegularLocalRing.iff_finrank_cotangentSpace (CompletedRing R)).mpr
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, AdicCompletion.spanFinrank_maximalIdeal_eq,
    completion_ring_dimension]
  exact IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)

section PowerQuotient

variable (R)
variable (L : Type v) [AddCommGroup L] [Module R L]

/-- Evaluation gives the same quotients before and after completion. -/
def completionPowerQuotientEquiv (n : ℕ) :
    (CompletedModule R L ⧸ (maximalIdeal (CompletedRing R) ^ n •
      (⊤ : Submodule (CompletedRing R) (CompletedModule R L)))) ≃ₗ[R]
      (L ⧸ (maximalIdeal R ^ n • (⊤ : Submodule R L))) := by
  let Q : Submodule (CompletedRing R) (CompletedModule R L) := maximalIdeal (CompletedRing R) ^ n • ⊤
  have hQ : Q.restrictScalars R = (AdicCompletion.eval (maximalIdeal R) L n).ker := by
    dsimp [Q]
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top, AdicCompletion.pow_smul_top_eq_ker_eval
        (maximalIdeal R).fg_of_isNoetherianRing]
  exact (Submodule.Quotient.restrictScalarsEquiv R Q).symm.trans
    ((Submodule.quotEquivOfEq _ _ hQ).trans
      ((AdicCompletion.eval (maximalIdeal R) L n).quotKerEquivOfSurjective
        (AdicCompletion.eval_surjective (maximalIdeal R) L n)))

theorem completion_power_quotient (n : ℕ) :
    Nonempty
      ((CompletedModule R L ⧸ (maximalIdeal (CompletedRing R) ^ n •
        (⊤ : Submodule (CompletedRing R) (CompletedModule R L)))) ≃ₗ[R]
        (L ⧸ (maximalIdeal R ^ n • (⊤ : Submodule R L)))) :=
  ⟨completionPowerQuotientEquiv R L n⟩

end PowerQuotient

section Length

variable (R)
variable (L : Type v) [AddCommGroup L] [Module R L]

/-- A scalar from the completion agrees with one from the original ring
on any completed-ring module killed by the given power of the maximal ideal. -/
private theorem completion_scalar_approximation (X : Type v) [AddCommGroup X]
    [Module (CompletedRing R) X] [Module R X] [IsScalarTower R (CompletedRing R) X]
    {n : ℕ} (h : maximalIdeal R ^ n ≤ Module.annihilator R X)
    (a : CompletedRing R) : ∃ r : R, ∀ x : X, a • x = r • x := by
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (maximalIdeal R) R n a)
  refine ⟨r, fun x => ?_⟩
  have hd : a - algebraMap R (CompletedRing R) r ∈
      (maximalIdeal R ^ n).map (algebraMap R (CompletedRing R)) := by
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing]
    change AdicCompletion.eval (maximalIdeal R) R n
      (a - AdicCompletion.of (maximalIdeal R) R r) = 0
    rw [map_sub, AdicCompletion.eval_of]
    exact sub_eq_zero.mpr hr.symm
  have hann : (maximalIdeal R ^ n).map (algebraMap R (CompletedRing R)) ≤
      Module.annihilator (CompletedRing R) X := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact Module.mem_annihilator.mpr fun y => by
      rw [algebraMap_smul]
      exact Module.mem_annihilator.mp (h hs) y
  have hx := Module.mem_annihilator.mp (hann hd) x
  rwa [sub_smul, algebraMap_smul, sub_eq_zero] at hx

private theorem length_eq_of_completion_scalars (X : Type v) [AddCommGroup X]
    [Module (CompletedRing R) X] [Module R X] [IsScalarTower R (CompletedRing R) X]
    {n : ℕ} (h : maximalIdeal R ^ n ≤ Module.annihilator R X) :
    Module.length (CompletedRing R) X = Module.length R X := by
  let e : Submodule (CompletedRing R) X ≃o Submodule R X :=
    { toFun := fun P => P.restrictScalars R
      invFun := fun P =>
        { P.toAddSubmonoid with
          smul_mem' := fun a x hx => by
            obtain ⟨r, hr⟩ := completion_scalar_approximation R X h a
            rw [hr]
            exact P.smul_mem r hx }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length, Order.krullDim_eq_of_orderIso e]

/-- Completing a finite-length module preserves its length. -/
theorem completion_base_change_length (h : IsFiniteLength R L) :
    Module.length (CompletedRing R) (CompletedRing R ⊗[R] L) = Module.length R L := by
  obtain ⟨n, hn⟩ := P103.Ch06.FiniteColength.finite_length_power R L h
  let : IsNoetherian R L := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
  let e := completionTensorEquiv (R := R) L
  have hTensor : maximalIdeal R ^ n ≤ Module.annihilator R (CompletedRing R ⊗[R] L) := by
    intro r hr
    apply Module.mem_annihilator.mpr
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a l => rw [← TensorProduct.tmul_smul, Module.mem_annihilator.mp (hn hr) l,
        TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  have hCompletion : maximalIdeal R ^ n ≤ Module.annihilator R (CompletedModule R L) := by
    intro r hr
    apply Module.mem_annihilator.mpr
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    change r • (e.restrictScalars R) y = 0
    rw [← (e.restrictScalars R).map_smul, Module.mem_annihilator.mp (hTensor hr), map_zero]
  have hker : (AdicCompletion.eval (maximalIdeal R) L n).ker = ⊥ := by
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing,
      ← Submodule.le_annihilator_iff, Submodule.annihilator_top]
    exact hCompletion
  have hquot : maximalIdeal R ^ n • (⊤ : Submodule R L) = ⊥ := by
    rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]
    exact hn
  let evalEquiv := LinearEquiv.ofBijective (AdicCompletion.eval (maximalIdeal R) L n)
    ⟨LinearMap.ker_eq_bot.mp hker, AdicCompletion.eval_surjective (maximalIdeal R) L n⟩
  rw [length_eq_of_completion_scalars R _ hTensor]
  exact ((e.restrictScalars R).trans (evalEquiv.trans
    (Submodule.quotEquivOfEqBot _ hquot))).length_eq

end Length

section Tor

/-- The completed Tor comparison, using the extension of an ordinary
projective resolution and the canonical tensor comparisons for its two arguments. -/
def completionTorEquiv (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℕ) :
    CompletedRing R ⊗[R] Tor M N i ≃ₗ[CompletedRing R]
      Tor (completedModuleCat M) (completedModuleCat N) i := by
  let A := CompletedRing R
  let : Module.FaithfullyFlat R A := AdvCommAlg.CohenMacaulay.completion_faithfullyFlat R
  let P := P103.Ch11.ExtTorDefinitions.resolutionFamily R M
  let Q := extendedResolution (S := A) P.val
  let eM := completionTensorEquiv (R := R) M
  let eN := completionTensorEquiv (R := R) N
  let Q' : LeftResolution A (completedModuleCat M) :=
    { complex := Q.complex
      ε := eM.toLinearMap.comp Q.ε
      surjective := eM.surjective.comp Q.surjective
      exact_zero := Q.exact_zero.trans (eM.ker_comp Q.ε).symm
      exact_succ := Q.exact_succ }
  have hQ' : Q'.IsProjective := extendedResolution_projective P.val P.property
  let eC : coefficientComplex (S := A) Q.complex (A ⊗[R] N) ≅
      coefficientComplex (S := A) Q'.complex (completedModuleCat N) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun j => (TensorProduct.congr eN (LinearEquiv.refl A (Q.complex.X j))).toModuleIso)
      (by
        intro j k _
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        rfl)
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
    (torLeftEquiv M N P.val P.property i)).trans
      (((flat_base_change.{u,v,w} R A).some.second P.val N i).trans
        ((homologyIso eC i).trans
          (torLeftEquiv (completedModuleCat M) (completedModuleCat N) Q' hQ' i).symm))

theorem completion_tor (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℕ) :
    Nonempty (CompletedRing R ⊗[R] Tor M N i ≃ₗ[CompletedRing R]
      Tor (completedModuleCat M) (completedModuleCat N) i) :=
  ⟨completionTorEquiv M N i⟩

theorem completion_tensor_finite_length (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] (h : IsFiniteLength R (M ⊗[R] N)) :
    IsFiniteLength (CompletedRing R) (CompletedModule R M ⊗[CompletedRing R] CompletedModule R N) := by
  let e := (TensorProduct.AlgebraTensorModule.distribBaseChange R (CompletedRing R) M N).trans
    (TensorProduct.congr (completionTensorEquiv (R := R) M) (completionTensorEquiv (R := R) N))
  apply Module.length_ne_top_iff.mp
  rw [← e.length_eq, completion_base_change_length R _ h]
  exact Module.length_ne_top_iff.mpr h

end Tor

theorem completion_euler {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] (h : IsFiniteLength R (M ⊗[R] N)) :
    ∃ hreg : IsRegularLocalRing (CompletedRing R),
      letI := hreg
      intersectionEuler (completedModuleCat M) (completedModuleCat N) = intersectionEuler M N := by
  let hreg := completion_regular_local R
  refine ⟨hreg, ?_⟩
  let := hreg
  have hd : regularLocalDimension (CompletedRing R) = regularLocalDimension R := by
    exact_mod_cast (ringKrullDim_eq_regularLocalDimension (CompletedRing R)).symm.trans
      ((completion_ring_dimension R).trans (ringKrullDim_eq_regularLocalDimension R))
  change IsolatedIntersectionEuler.Specs.cutoffEuler (completedModuleCat M) (completedModuleCat N)
      (regularLocalDimension (CompletedRing R)) =
    IsolatedIntersectionEuler.Specs.cutoffEuler M N (regularLocalDimension R)
  rw [hd]
  unfold IsolatedIntersectionEuler.Specs.cutoffEuler
  apply Finset.sum_congr rfl
  intro i _
  rw [← (completionTorEquiv M N i).length_eq,
    completion_base_change_length R _ (tor_finite_length_of_tensor M N h i)]

end CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion
