import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Type
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions

/-!
GC-01: socles, type, and local dualizing conditions.

The socle and type reuse DP-05, with exactly its descended residue-field
scalar structures. The Hom comparison is evaluation at the residue class of 1;
its naturality is stated for arbitrary R-linear maps. The local Gorenstein
condition is finite self-injective dimension, without assuming any subsequent
CM/type-one characterization. The global condition quantifies over all prime
localizations (so includes the zero ring vacuously).
-/

universe u
open CategoryTheory

namespace AdvCommAlg.Gorenstein

/-- The elements annihilated by the maximal ideal: `0 :_M maximalIdeal R`. -/
abbrev socle (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] : Submodule R M := Depth.Socle R M

theorem mem_socle_iff (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (x : M) :
    x ∈ socle R M ↔ ∀ a ∈ IsLocalRing.maximalIdeal R, a • x = 0 := by
  rw [Submodule.mem_torsionBySet_iff]
  exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a.val a.property⟩

/-- The canonical identification, linear over the residue field. -/
theorem hom_socle_equiv (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] :
    ∃ e : Depth.ResidueHom R M ≃ₗ[IsLocalRing.ResidueField R] socle R M,
      ∀ g, (e g).val = g 1 :=
  Depth.homSocleEquiv R M

/-- The evaluation identification is natural in every module, with no
finiteness hypothesis. The equality of underlying elements is the commuting
square for the induced map on socles and postcomposition on Hom. -/
theorem hom_socle_natural (R : Type u) [CommRing R] [IsLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (eM : Depth.ResidueHom R M ≃ₗ[IsLocalRing.ResidueField R] socle R M)
    (eN : Depth.ResidueHom R N ≃ₗ[IsLocalRing.ResidueField R] socle R N)
    (hM : ∀ g, (eM g).val = g 1) (hN : ∀ g, (eN g).val = g 1)
    (f : M →ₗ[R] N) (g : Depth.ResidueHom R M) :
    (eN (f.comp g)).val = f (eM g).val := by
  rw [hN, hM]
  rfl

/-- The type of the ring is the canonical finite-module type of its regular module. -/
noncomputable def ringType (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] : ℕ :=
  Depth.moduleType R (ModuleCat.of R R)

/-- We use categorical injective dimension in `WithBot ℕ∞` throughout.
In particular, the zero module has dimension `⊥`, which is finite. -/
noncomputable def FiniteInjectiveDimension (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  injectiveDimension (ModuleCat.of R M) ≠ ⊤

theorem finiteInjectiveDimension_iff_exists_bound (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] :
    FiniteInjectiveDimension R M ↔
      ∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of R M) n :=
  injectiveDimension_ne_top_iff (ModuleCat.of R M)

/-- The local Gorenstein condition is finite injective dimension over itself. -/
noncomputable def LocalGorenstein (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] : Prop :=
  FiniteInjectiveDimension R R

/-- A Noetherian ring is Gorenstein when every prime localization is locally
Gorenstein. No nonzero-ring condition is imposed on the global ring. -/
noncomputable def GorensteinRing (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ p : PrimeSpectrum R, LocalGorenstein (Localization.AtPrime p.asIdeal)

/-- A canonical module over a CM local ring is finite, nonzero, maximal CM,
of type one, and of finite injective dimension. Finiteness is an input
instance, while the CM condition on the base ring is included in the predicate. -/
noncomputable def IsCanonicalModule (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] : Prop :=
  CohenMacaulay.LocalCohenMacaulay R R ∧ Nontrivial M ∧
  CohenMacaulay.MaximalCohenMacaulay R M ∧
  Depth.moduleType R (ModuleCat.of R M) = 1 ∧ FiniteInjectiveDimension R M

theorem isCanonicalModule_iff (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : CohenMacaulay.LocalCohenMacaulay R R) :
    IsCanonicalModule R M ↔ Nontrivial M ∧
      CohenMacaulay.MaximalCohenMacaulay R M ∧
      Depth.moduleType R (ModuleCat.of R M) = 1 ∧ FiniteInjectiveDimension R M :=
  and_iff_right hR

end AdvCommAlg.Gorenstein
