import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite prime filtrations

The filtration is indexed by its stages, from the zero submodule to the full module.
Each step is labelled by the prime of its cyclic quotient.
-/

namespace CommutativeAlgebraNotes

/-- A finite filtration by submodules with prime cyclic factors. -/
structure PrimeFiltration (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] where
  length : ℕ
  stage : Fin (length + 1) → Submodule R M
  first_eq_bot : stage 0 = ⊥
  last_eq_top : stage (Fin.last length) = ⊤
  strictMono_stage : StrictMono stage
  prime : Fin length → PrimeSpectrum R
  factorEquiv : ∀ i : Fin length,
    ((stage i.succ : Submodule R M) ⧸ (stage i.castSucc).submoduleOf (stage i.succ)) ≃ₗ[R]
      R ⧸ (prime i).asIdeal

namespace PrimeFiltration

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The inclusion of an earlier stage in a later stage. -/
def inclusion (F : PrimeFiltration R M) {i j : Fin (F.length + 1)} (h : i ≤ j) :
    F.stage i →ₗ[R] F.stage j :=
  Submodule.inclusion (F.strictMono_stage.monotone h)

/-- The canonical quotient map at step `i`, followed by the chosen identification with
the prime quotient. -/
def projection (F : PrimeFiltration R M) (i : Fin F.length) :
    F.stage i.succ →ₗ[R] R ⧸ (F.prime i).asIdeal :=
  (F.factorEquiv i).toLinearMap.comp
    ((F.stage i.castSucc).submoduleOf (F.stage i.succ)).mkQ

end PrimeFiltration

namespace Specs.FinitePrimeFiltration

universe u v

def existsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    Nonempty (PrimeFiltration R M)

def inclusionInjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M) ⦃i j : Fin (F.length + 1)⦄ (h : i ≤ j),
    Function.Injective (F.inclusion h)

def stepShortExactType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M) (i : Fin F.length),
    Function.Injective (F.inclusion (Fin.castSucc_le_succ i)) ∧
      Function.Exact (F.inclusion (Fin.castSucc_le_succ i)) (F.projection i) ∧
      Function.Surjective (F.projection i)

def memStageSupportType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M) (k : Fin (F.length + 1)) (q : PrimeSpectrum R),
    q ∈ Module.support R (F.stage k) ↔
      ∃ i : Fin F.length, i.val < k.val ∧ q ∈ PrimeSpectrum.zeroLocus (F.prime i).asIdeal

def supportType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M),
    Module.support R M = ⋃ i : Fin F.length, PrimeSpectrum.zeroLocus (F.prime i).asIdeal

def stageSupportSubsetType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M) (k : Fin (F.length + 1)),
    Module.support R (F.stage k) ⊆ Module.support R M

def factorSupportSubsetType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M) (i : Fin F.length),
    Module.support R (R ⧸ (F.prime i).asIdeal) ⊆ Module.support R M

def dimensionType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M),
    Module.supportDim R M = ⨆ i : Fin F.length, ringKrullDim (R ⧸ (F.prime i).asIdeal)

def lengthZeroType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M),
    (F.length = 0 ↔ Subsingleton M) ∧ (F.length = 0 → Module.supportDim R M = ⊥)

def dimensionMaximumType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M), Nontrivial M → ∃ i : Fin F.length,
      Module.supportDim R M = ringKrullDim (R ⧸ (F.prime i).asIdeal) ∧
        ∀ j : Fin F.length, ringKrullDim (R ⧸ (F.prime j).asIdeal) ≤
          ringKrullDim (R ⧸ (F.prime i).asIdeal)

end Specs.FinitePrimeFiltration
end CommutativeAlgebraNotes
