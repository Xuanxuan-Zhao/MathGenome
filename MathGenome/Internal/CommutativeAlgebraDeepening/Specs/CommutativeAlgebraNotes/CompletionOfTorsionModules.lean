import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! The action of the maximal-ideal completion on a power-torsion module. -/

open scoped TensorProduct

namespace Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules

universe u v w

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The completion with respect to the maximal ideal of the original ring. -/
abbrev Completion := AdicCompletion (IsLocalRing.maximalIdeal R) R

/-- Power torsion for the maximal ideal, using the common ideal torsion submodule. -/
abbrev IsPowerTorsion (T : Type v) [AddCommGroup T] [Module R T] : Prop :=
  ∀ x : T, x ∈ IdealTorsion.idealTorsion (IsLocalRing.maximalIdeal R) T

variable {R} [IsNoetherianRing R]

local notation "𝔪" => IsLocalRing.maximalIdeal R
local notation "S" => Completion R

section Quotients

/-- The kernel of reduction modulo the (n)-th power of the maximal ideal. -/
theorem ker_eval (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ 𝔪 n) = IsLocalRing.maximalIdeal S ^ n := by
  have h₁ : 𝔪 ^ n ≤ 𝔪 ^ n • (⊤ : Ideal R) := by simp
  have h₂ : 𝔪 ^ n • (⊤ : Ideal R) ≤ 𝔪 ^ n := by simp
  ext s
  change AdicCompletion.evalₐ 𝔪 n s = 0 ↔ _
  have h : AdicCompletion.evalₐ 𝔪 n s = 0 ↔ AdicCompletion.eval 𝔪 R n s = 0 := by
    constructor
    · intro hs
      rw [← AdicCompletion.factor_evalₐ_eq_eval 𝔪 s h₁, hs, map_zero]
    · intro hs
      rw [← AdicCompletion.factor_eval_eq_evalₐ 𝔪 s h₂, hs, map_zero]
  rw [h, ← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing 𝔪),
    Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow,
    AdicCompletion.maximalIdeal_eq_map]

end Quotients

section Action

variable {T : Type v} [AddCommGroup T] [Module R T]

omit [IsNoetherianRing R] in
theorem exists_killing_power (h : IsPowerTorsion R T) (x : T) :
    ∃ n : ℕ, ∀ a ∈ 𝔪 ^ n, a • x = 0 := by
  simpa only [IdealTorsion.idealTorsion, Ideal.primaryComponent_mem,
    Submodule.mem_torsionBySet_iff, SetCoe.forall, SetLike.mem_coe] using h x

noncomputable def representative (s : S) (n : ℕ) : R :=
  (Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔪 n s)).choose

omit [IsNoetherianRing R] in
theorem mk_representative (s : S) (n : ℕ) :
    Ideal.Quotient.mk (𝔪 ^ n) (representative s n) = AdicCompletion.evalₐ 𝔪 n s :=
  (Ideal.Quotient.mk_surjective _).choose_spec

private theorem eval_eq_of_le {s t : S} {m n : ℕ} (hmn : m ≤ n)
    (h : AdicCompletion.evalₐ 𝔪 n s = AdicCompletion.evalₐ 𝔪 n t) :
    AdicCompletion.evalₐ 𝔪 m s = AdicCompletion.evalₐ 𝔪 m t := by
  have hker : s - t ∈ RingHom.ker (AdicCompletion.evalₐ 𝔪 n) := by
    simpa [RingHom.mem_ker, map_sub, sub_eq_zero] using h
  have hm : s - t ∈ RingHom.ker (AdicCompletion.evalₐ 𝔪 m) := by
    rw [ker_eval] at hker ⊢
    exact Ideal.pow_le_pow_right hmn hker
  simpa [RingHom.mem_ker, map_sub, sub_eq_zero] using hm

/-- The completed scalar acts through a representative modulo a killing power. -/
noncomputable def scalar (h : IsPowerTorsion R T) (s : S) (x : T) : T :=
  representative s (exists_killing_power h x).choose • x

theorem scalar_eq_of_eval (h : IsPowerTorsion R T) {n : ℕ} {x : T}
    (hx : ∀ a ∈ 𝔪 ^ n, a • x = 0) {s : S} {r : R}
    (hr : Ideal.Quotient.mk (𝔪 ^ n) r = AdicCompletion.evalₐ 𝔪 n s) :
    scalar h s x = r • x := by
  let m := (exists_killing_power h x).choose
  have hm : ∀ a ∈ 𝔪 ^ m, a • x = 0 := (exists_killing_power h x).choose_spec
  let t := representative s (max m n)
  have ht (k : ℕ) (hk : k ≤ max m n) :
      Ideal.Quotient.mk (𝔪 ^ k) t = AdicCompletion.evalₐ 𝔪 k s := by
    have e := eval_eq_of_le hk
      (show AdicCompletion.evalₐ 𝔪 (max m n) (algebraMap R S t) =
        AdicCompletion.evalₐ 𝔪 (max m n) s by
        rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply,
          AdicCompletion.evalₐ_of]
        exact mk_representative s (max m n))
    simpa [AdicCompletion.algebraMap_apply] using e
  have same (k : ℕ) (hk : ∀ a ∈ 𝔪 ^ k, a • x = 0) {a b : R}
      (e : Ideal.Quotient.mk (𝔪 ^ k) a = Ideal.Quotient.mk (𝔪 ^ k) b) :
      a • x = b • x := by
    have e' := hk (a - b) ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp e)
    rwa [sub_smul, sub_eq_zero] at e'
  exact (same m hm ((mk_representative s m).trans (ht m (le_max_left _ _)).symm)).trans
    (same n hx ((ht n (le_max_right _ _)).trans hr.symm))


/-- The completion module structure defined by reduction at each torsion element. -/
@[instance_reducible]
noncomputable def completionModule (h : IsPowerTorsion R T) : Module S T where
  smul := scalar h
  one_smul x := by
    obtain ⟨n, hx⟩ := exists_killing_power h x
    exact (scalar_eq_of_eval h hx (r := 1) (by simp)).trans (one_smul R x)
  mul_smul s t x := by
    obtain ⟨n, hx⟩ := exists_killing_power h x
    let a := representative s n
    let b := representative t n
    have ha : Ideal.Quotient.mk (𝔪 ^ n) a = _ := mk_representative s n
    have hb : Ideal.Quotient.mk (𝔪 ^ n) b = _ := mk_representative t n
    have hy : ∀ c ∈ 𝔪 ^ n, c • (b • x) = 0 := by
      intro c hc
      rw [smul_comm c b x, hx c hc, smul_zero]
    change scalar h (s * t) x = scalar h s (scalar h t x)
    rw [scalar_eq_of_eval h hx hb, scalar_eq_of_eval h hy ha,
      scalar_eq_of_eval h hx (r := a * b) (by simp only [map_mul, ha, hb])]
    exact mul_smul a b x
  smul_zero s :=
    (scalar_eq_of_eval h (n := 0) (x := (0 : T)) (by simp) (mk_representative s 0)).trans
      (smul_zero _)
  smul_add s x y := by
    obtain ⟨m, hx⟩ := exists_killing_power h x
    obtain ⟨n, hy⟩ := exists_killing_power h y
    let k := max m n
    have hx' : ∀ a ∈ 𝔪 ^ k, a • x = 0 :=
      fun a ha => hx a (Ideal.pow_le_pow_right (le_max_left m n) ha)
    have hy' : ∀ a ∈ 𝔪 ^ k, a • y = 0 :=
      fun a ha => hy a (Ideal.pow_le_pow_right (le_max_right m n) ha)
    have hxy : ∀ a ∈ 𝔪 ^ k, a • (x + y) = 0 := by
      intro a ha
      rw [smul_add, hx' a ha, hy' a ha, add_zero]
    have hr := mk_representative s k
    change scalar h s (x + y) = scalar h s x + scalar h s y
    rw [scalar_eq_of_eval h hxy hr, scalar_eq_of_eval h hx' hr, scalar_eq_of_eval h hy' hr,
      smul_add]
  add_smul s t x := by
    obtain ⟨n, hx⟩ := exists_killing_power h x
    have ha := mk_representative s n
    have hb := mk_representative t n
    change scalar h (s + t) x = scalar h s x + scalar h t x
    rw [scalar_eq_of_eval h hx ha, scalar_eq_of_eval h hx hb,
      scalar_eq_of_eval h hx (r := representative s n + representative t n)
        (by simp only [map_add, ha, hb]), add_smul]
  zero_smul x := by
    obtain ⟨n, hx⟩ := exists_killing_power h x
    exact (scalar_eq_of_eval h hx (r := 0) (by simp)).trans (zero_smul R x)

theorem scalar_algebraMap (h : IsPowerTorsion R T) (r : R) (x : T) :
    scalar h (algebraMap R S r) x = r • x := by
  obtain ⟨n, hx⟩ := exists_killing_power h x
  exact scalar_eq_of_eval h hx (by simp [AdicCompletion.algebraMap_apply])

theorem completionScalarTower (h : IsPowerTorsion R T) :
    letI := completionModule h
    IsScalarTower R S T := by
  let := completionModule h
  apply IsScalarTower.of_algebraMap_smul
  exact scalar_algebraMap h

end Action

section Statements

set_option linter.checkUnivs false

variable {T : Type v} [AddCommGroup T] [Module R T]
variable {U : Type w} [AddCommGroup U] [Module R U]

/-- The quotient isomorphism induced by the canonical reduction map. -/
noncomputable def completionQuotientEquiv (n : ℕ) :
    (S ⧸ (IsLocalRing.maximalIdeal S ^ n)) ≃ₐ[R] (R ⧸ (𝔪 ^ n)) :=
  (Ideal.quotientEquivAlgOfEq R (ker_eval n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.surjective_evalₐ 𝔪 n))

/-- Extension means that restriction along the actual algebra map recovers the given action. -/
def Extends (A : Module S T) : Prop :=
  letI := A
  ∀ (r : R) (x : T), algebraMap R S r • x = r • x

/-- The multiplication map for the canonical completed action. -/
noncomputable def completionTensorMap (h : IsPowerTorsion R T) :
    letI := completionModule h
    S ⊗[R] T →ₗ[S] T := by
  letI := completionModule h
  letI := completionScalarTower h
  exact (LinearMap.id : T →ₗ[R] T).liftBaseChange S

def completionQuotientEquivType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ),
    (Completion R ⧸ (IsLocalRing.maximalIdeal (Completion R) ^ n)) ≃ₐ[R]
      (R ⧸ (IsLocalRing.maximalIdeal R ^ n))

def completionQuotientEquivMkType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) (s : Completion R),
    completionQuotientEquiv n (Ideal.Quotient.mk _ s) = AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n s

def completionModuleType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T], IsPowerTorsion R T → Module (Completion R) T

def completionModuleSmulType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] (h : IsPowerTorsion R T),
    letI := completionModule h
    ∀ {n : ℕ} {x : T}, (∀ a ∈ (IsLocalRing.maximalIdeal R) ^ n, a • x = 0) →
      ∀ {s : (Completion R)} {r : R}, Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ n) r = AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n s →
        s • x = r • x

def completionScalarTowerType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] (h : IsPowerTorsion R T),
    letI := completionModule h
    IsScalarTower R (Completion R) T

def completionModuleExtendsType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] (h : IsPowerTorsion R T),
    Extends (completionModule h)

def completionModuleUniqueType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] (h : IsPowerTorsion R T)
    (A : Module (Completion R) T), Extends A → A = completionModule h

def completionTensorMapType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] (h : IsPowerTorsion R T),
    letI := completionModule h
    (Completion R) ⊗[R] T →ₗ[(Completion R)] T

def completionTensorMapTmulType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] (h : IsPowerTorsion R T),
    letI := completionModule h
    ∀ (s : Completion R) (x : T), completionTensorMap h (s ⊗ₜ[R] x) = s • x

def completionTensorMapBijectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] (h : IsPowerTorsion R T),
    Function.Bijective (completionTensorMap h)

def completionTensorMapNaturalityType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T]
    {U : Type w} [AddCommGroup U] [Module R U] (hT : IsPowerTorsion R T) (hU : IsPowerTorsion R U)
    (f : T →ₗ[R] U) (z : (Completion R) ⊗[R] T),
    f (completionTensorMap hT z) = completionTensorMap hU (f.baseChange (Completion R) z)

def completionSubmoduleSmulMemType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] (h : IsPowerTorsion R T),
    letI := completionModule h
    ∀ (P : Submodule R T) (s : Completion R) {x : T}, x ∈ P → s • x ∈ P

def completionLinearMapSmulType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T]
    {U : Type w} [AddCommGroup U] [Module R U] (hT : IsPowerTorsion R T) (hU : IsPowerTorsion R U),
    letI := completionModule hT
    letI := completionModule hU
    ∀ (f : T →ₗ[R] U) (s : Completion R) (x : T), f (s • x) = s • f x

def completionPowerTorsionType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] (h : IsPowerTorsion R T),
    letI := completionModule h
    IsPowerTorsion (Completion R) T

def powerTorsionRestrictScalarsType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] [Module (Completion R) T] [IsScalarTower R (Completion R) T],
    IsPowerTorsion (Completion R) T → IsPowerTorsion R T

end Statements

end Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
