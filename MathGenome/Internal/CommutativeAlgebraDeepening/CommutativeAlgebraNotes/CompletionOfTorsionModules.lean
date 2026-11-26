import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.IdealTorsion

/-! Passage of maximal-ideal power-torsion modules to the completion. -/

open scoped TensorProduct

namespace CommutativeAlgebraNotes.CompletionOfTorsionModules

universe u v w

open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
  (Completion IsPowerTorsion Extends exists_killing_power representative mk_representative ker_eval)

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {T : Type v} [AddCommGroup T] [Module R T]
variable {U : Type w} [AddCommGroup U] [Module R U]

local notation "𝔪" => IsLocalRing.maximalIdeal R
local notation "S" => Completion R

/-- Reduction identifies the (n)-th quotients of the completion and of the base ring. -/
noncomputable abbrev completionQuotientEquiv (n : ℕ) :
    (S ⧸ (IsLocalRing.maximalIdeal S ^ n)) ≃ₐ[R] (R ⧸ (𝔪 ^ n)) :=
  Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules.completionQuotientEquiv n

@[simp]
theorem completionQuotientEquiv_mk (n : ℕ) (s : S) :
    completionQuotientEquiv n (Ideal.Quotient.mk _ s) = AdicCompletion.evalₐ 𝔪 n s := by
  rw [completionQuotientEquiv,
    Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules.completionQuotientEquiv,
    AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The completed module structure on a maximal-ideal power-torsion module. -/
noncomputable abbrev completionModule (h : IsPowerTorsion R T) : Module S T :=
  Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules.completionModule h

theorem completionModule_smul (h : IsPowerTorsion R T) :
    letI := completionModule h
    ∀ {n : ℕ} {x : T}, (∀ a ∈ 𝔪 ^ n, a • x = 0) →
      ∀ {s : S} {r : R}, Ideal.Quotient.mk (𝔪 ^ n) r = AdicCompletion.evalₐ 𝔪 n s →
        s • x = r • x := by
  intro n x hx s r hr
  exact Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules.scalar_eq_of_eval h hx hr

theorem completionScalarTower (h : IsPowerTorsion R T) :
    letI := completionModule h
    IsScalarTower R S T :=
  Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules.completionScalarTower h

theorem completionModule_extends (h : IsPowerTorsion R T) : Extends (completionModule h) :=
  Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules.scalar_algebraMap h

/-- In any compatible module, the action on an element killed by (mathfrak m^n)
only depends on the image of the scalar in (R/mathfrak m^n). -/
private theorem smul_eq_of_eval_eq [Module S T] [IsScalarTower R S T]
    {n : ℕ} {x : T} (hx : ∀ a ∈ 𝔪 ^ n, a • x = 0) {s t : S}
    (h : AdicCompletion.evalₐ 𝔪 n s = AdicCompletion.evalₐ 𝔪 n t) :
    s • x = t • x := by
  have hsub : s - t ∈ RingHom.ker (AdicCompletion.evalₐ 𝔪 n) := by
    change AdicCompletion.evalₐ 𝔪 n (s - t) = 0
    rw [map_sub, h, sub_self]
  have hsub' : s - t ∈ 𝔪 ^ n • (⊤ : Submodule R S) := by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow,
      ← AdicCompletion.maximalIdeal_eq_map, ← ker_eval]
    exact hsub
  have hz : (s - t) • x = 0 := by
    refine Submodule.smul_induction_on hsub' ?_ ?_
    · intro a ha b _
      rw [smul_assoc, smul_comm a b, hx a ha, smul_zero]
    · intro a b ha hb
      rw [add_smul, ha, hb, add_zero]
  rwa [sub_smul, sub_eq_zero] at hz

/-- An action extending the original action agrees with the completed action. -/
theorem completionModule_unique (h : IsPowerTorsion R T) (A : Module S T)
    (hA : Extends A) : A = completionModule h := by
  refine Module.ext' _ _ fun s x => ?_
  let := A
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul hA
  obtain ⟨n, hx⟩ := exists_killing_power h x
  let r := representative s n
  have hr : Ideal.Quotient.mk (𝔪 ^ n) r = AdicCompletion.evalₐ 𝔪 n s :=
    mk_representative s n
  calc
    s • x = algebraMap R S r • x :=
      smul_eq_of_eval_eq hx (by simpa [AdicCompletion.algebraMap_apply] using hr.symm)
    _ = r • x := hA r x
    _ = _ := (completionModule_smul h hx hr).symm

/-- The completed tensor multiplication map. -/
noncomputable abbrev completionTensorMap (h : IsPowerTorsion R T) :
    letI := completionModule h
    S ⊗[R] T →ₗ[S] T :=
  Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules.completionTensorMap h

@[simp]
theorem completionTensorMap_tmul (h : IsPowerTorsion R T) :
    letI := completionModule h
    ∀ (s : S) (x : T), completionTensorMap h (s ⊗ₜ[R] x) = s • x :=
  fun _ _ => rfl

private theorem tmul_eq_one_tmul (h : IsPowerTorsion R T) (s : S) (x : T) :
    s ⊗ₜ[R] x = (1 : S) ⊗ₜ[R] completionTensorMap h (s ⊗ₜ[R] x) := by
  let := completionModule h
  obtain ⟨n, hx⟩ := exists_killing_power h x
  let r := representative s n
  have hr : Ideal.Quotient.mk (𝔪 ^ n) r = AdicCompletion.evalₐ 𝔪 n s :=
    mk_representative s n
  have hy : ∀ a ∈ 𝔪 ^ n, a • ((1 : S) ⊗ₜ[R] x) = 0 := by
    intro a ha
    change (a • (1 : S)) ⊗ₜ[R] x = 0
    rw [TensorProduct.smul_tmul, hx a ha, TensorProduct.tmul_zero]
  have he : AdicCompletion.evalₐ 𝔪 n s = AdicCompletion.evalₐ 𝔪 n (algebraMap R S r) := by
    simpa [AdicCompletion.algebraMap_apply] using hr.symm
  calc
    s ⊗ₜ[R] x = s • ((1 : S) ⊗ₜ[R] x) := TensorProduct.tmul_eq_smul_one_tmul s x
    _ = algebraMap R S r • ((1 : S) ⊗ₜ[R] x) := smul_eq_of_eval_eq hy he
    _ = (1 : S) ⊗ₜ[R] (r • x) := by
      rw [algebraMap_smul S]
      exact TensorProduct.smul_tmul r (1 : S) x
    _ = _ := by rw [completionTensorMap_tmul, completionModule_smul h hx hr]

theorem completionTensorMap_bijective (h : IsPowerTorsion R T) :
    Function.Bijective (completionTensorMap h) := by
  let := completionModule h
  let := completionScalarTower h
  let unit : T →ₗ[R] S ⊗[R] T := TensorProduct.mk R S T 1
  have hleft : Function.LeftInverse unit (completionTensorMap h) := by
    change ∀ z, (unit.comp ((completionTensorMap h).restrictScalars R)) z = z
    have hid : unit.comp ((completionTensorMap h).restrictScalars R) = LinearMap.id := by
      apply TensorProduct.ext'
      intro s x
      exact (tmul_eq_one_tmul h s x).symm
    intro z
    rw [hid, LinearMap.id_apply]
  exact ⟨hleft.injective, fun x => ⟨unit x, by simp [unit, completionTensorMap_tmul]⟩⟩

/-- The natural isomorphism (\widehat R \otimes_R T \cong T). -/
noncomputable def completionTensorEquiv (h : IsPowerTorsion R T) :
    letI := completionModule h
    S ⊗[R] T ≃ₗ[S] T :=
  LinearEquiv.ofBijective (completionTensorMap h) (completionTensorMap_bijective h)

@[simp]
theorem completionTensorEquiv_tmul (h : IsPowerTorsion R T) :
    letI := completionModule h
    ∀ (s : S) (x : T), completionTensorEquiv h (s ⊗ₜ[R] x) = s • x :=
  completionTensorMap_tmul h

@[simp]
theorem completionTensorEquiv_symm_apply (h : IsPowerTorsion R T) (x : T) :
    (completionTensorEquiv h).symm x = (1 : S) ⊗ₜ[R] x := by
  let := completionModule h
  apply (completionTensorEquiv h).injective
  rw [LinearEquiv.apply_symm_apply]
  change x = completionTensorMap h ((1 : S) ⊗ₜ[R] x)
  rw [completionTensorMap_tmul, one_smul]

theorem completionSubmodule_smul_mem (h : IsPowerTorsion R T) :
    letI := completionModule h
    ∀ (P : Submodule R T) (s : S) {x : T}, x ∈ P → s • x ∈ P := by
  let := completionModule h
  intro P s x hx
  obtain ⟨n, hn⟩ := exists_killing_power h x
  rw [completionModule_smul h hn (mk_representative s n)]
  exact P.smul_mem _ hx

/-- An original submodule is stable under the completed action. -/
def completionSubmodule (h : IsPowerTorsion R T) (P : Submodule R T) :
    letI := completionModule h
    Submodule S T := by
  letI := completionModule h
  exact {
    carrier := P
    zero_mem' := P.zero_mem
    add_mem' := P.add_mem
    smul_mem' := fun s _ hx => completionSubmodule_smul_mem h P s hx }

theorem completionLinearMap_smul (hT : IsPowerTorsion R T) (hU : IsPowerTorsion R U) :
    letI := completionModule hT
    letI := completionModule hU
    ∀ (f : T →ₗ[R] U) (s : S) (x : T), f (s • x) = s • f x := by
  let := completionModule hT
  let := completionModule hU
  intro f s x
  obtain ⟨n, hx⟩ := exists_killing_power hT x
  have hy : ∀ a ∈ 𝔪 ^ n, a • f x = 0 := by
    intro a ha
    rw [← f.map_smul, hx a ha, f.map_zero]
  have hr := mk_representative s n
  rw [completionModule_smul hT hx hr, completionModule_smul hU hy hr, f.map_smul]

/-- An original linear map is linear for the completed module structures. -/
def completionLinearMap (hT : IsPowerTorsion R T) (hU : IsPowerTorsion R U) (f : T →ₗ[R] U) :
    letI := completionModule hT
    letI := completionModule hU
    T →ₗ[S] U := by
  letI := completionModule hT
  letI := completionModule hU
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := completionLinearMap_smul hT hU f }

theorem completionTensorMap_naturality (hT : IsPowerTorsion R T) (hU : IsPowerTorsion R U)
    (f : T →ₗ[R] U) (z : S ⊗[R] T) :
    f (completionTensorMap hT z) = completionTensorMap hU (f.baseChange S z) := by
  let := completionModule hT
  let := completionModule hU
  let := completionScalarTower hU
  have hcomp : (completionLinearMap hT hU f).comp (completionTensorMap hT) =
      (completionTensorMap hU).comp (f.baseChange S) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
      completionTensorMap_tmul, completionTensorMap_tmul]
    change f (s • x) = s • f x
    exact completionLinearMap_smul hT hU f s x
  exact LinearMap.congr_fun hcomp z

/-- The extended action is power torsion for the maximal ideal of the completion. -/
theorem completion_powerTorsion (h : IsPowerTorsion R T) :
    letI := completionModule h
    IsPowerTorsion S T := by
  let := completionModule h
  intro x
  obtain ⟨n, hn, hx⟩ := (mem_idealTorsion 𝔪 x).mp (h x)
  refine (mem_idealTorsion (IsLocalRing.maximalIdeal S) x).mpr ⟨n, hn, ?_⟩
  intro s hs
  have he : AdicCompletion.evalₐ 𝔪 n s = 0 := by
    change s ∈ RingHom.ker (AdicCompletion.evalₐ 𝔪 n)
    rwa [ker_eval]
  exact (completionModule_smul h hx (r := 0) (by rw [map_zero, he])).trans (zero_smul R x)

/-- Power torsion over the completion remains power torsion after restriction. -/
theorem powerTorsion_restrictScalars [Module S T] [IsScalarTower R S T]
    (h : IsPowerTorsion S T) : IsPowerTorsion R T := by
  intro x
  obtain ⟨n, hn, hx⟩ := (mem_idealTorsion (IsLocalRing.maximalIdeal S) x).mp (h x)
  refine (mem_idealTorsion 𝔪 x).mpr ⟨n, hn, ?_⟩
  intro r hr
  have hmap : algebraMap R S r ∈ IsLocalRing.maximalIdeal S ^ n := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  rw [← algebraMap_smul S]
  exact hx _ hmap

end CommutativeAlgebraNotes.CompletionOfTorsionModules
