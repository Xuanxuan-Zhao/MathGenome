import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.UniversalEnveloping
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Exact.Basic
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Comparison

/-! HA-A09-Action, source lines 3330–3380.
The independent interface uses the actual exterior-power cochains, their
printed calculus and quotient cohomology, and the invariant/inflation adjunction.
It includes comparison with every ambient injective resolution. -/
noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
universe u v w w'
attribute [local instance 100] LieRing.ofAssociativeRing
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The actual quotient Lie map, with no chosen complement. -/
def quotientMap (h : LieIdeal k g) : g →ₗ⁅k⁆ g ⧸ h :=
  { h.toSubmodule.mkQ with map_lie' := fun {_ _} => rfl }

variable {k g}
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]

/-- Vectors annihilated by the ideal, in the given representation. -/
def invariants (ρ : Representation k g M) : Submodule k M where
  carrier := {m | ∀ a : h, ρ a m = 0}
  zero_mem' := fun _ => map_zero _
  add_mem' := by intro m n hm hn a; simp only [map_add, hm a, hn a, add_zero]
  smul_mem' := by intro r m hm a; simp only [map_smul, hm a, smul_zero]

/-- Fixes the quotient action by its value on every quotient representative. -/
def IsInvariantAction (ρ : Representation k g M)
    (σ : Representation k (g ⧸ h) (invariants h ρ)) : Prop :=
  ∀ y m, (σ (quotientMap k g h y) m : M) = ρ y m

/-- Inflation changes the action, preserving the underlying module and maps. -/
abbrev inflation {N : Type w'} [AddCommGroup N] [Module k N]
    (τ : Representation k (g ⧸ h) N) : Representation k g N :=
  τ.comp (quotientMap k g h)

/-- Morphisms are genuine intertwiners of the specified representations. -/
abbrev Morphism {L : Type*} [LieRing L] [LieAlgebra k L]
    {N : Type w'} [AddCommGroup N] [Module k N]
    (ρ : Representation k L M) (σ : Representation k L N) :=
  {f : M →ₗ[k] N // LieIntertwines ρ σ f}

/-- Inflation on morphisms preserves the actual linear map. -/
def inflateMorphism {N : Type w'} [AddCommGroup N] [Module k N]
    {α : Representation k (g ⧸ h) M} {β : Representation k (g ⧸ h) N}
    (f : Morphism α β) : Morphism (inflation h α) (inflation h β) :=
  ⟨f.val, fun y m => f.property (quotientMap k g h y) m⟩

/-- The original exterior-power cochains, without a finite-rank duality. -/
abbrev Cochains (n : ℕ) := CE.W k h n →ₗ[k] M

/-- The printed all-degree coboundary, with zero-based removal indices. -/
def HasDifferentialFormula (ρ : Representation k g M)
    (δ : ∀ n, Cochains h (M := M) n →ₗ[k] Cochains h (M := M) (n+1)) : Prop :=
  ∀ n f x, δ n f (CE.wedge k h (n+1) x) =
    (∑ i : Fin (n+1), (-1 : ℤ)^i.val •
      (ρ (x i) (f (CE.wedge k h n (i.removeNth x))))) +
    CE.cochainBracketSum k h M n f x

/-- The specified infinitesimal action on the actual cochains. -/
def HasDerivativeFormula (ρ : Representation k g M)
    (L : ∀ n, g → Module.End k (Cochains h (M := M) n)) : Prop :=
  ∀ n y f x, L n y f (CE.wedge k h n x) =
    ρ y (f (CE.wedge k h n x)) -
      ∑ i : Fin n, f (CE.wedge k h n (Function.update x i ⁅y, x i⁆))

/-- Insertion puts the ideal element in the first slot. -/
def HasInsertionFormula
    (I : ∀ n, h → Cochains h (M := M) (n+1) →ₗ[k] Cochains h (M := M) n) : Prop :=
  ∀ n a f x, I n a f (CE.wedge k h n x) =
    f (CE.wedge k h (n+1) (Fin.cons a x))

/-- A cochain differential on the original exterior-power Hom spaces. -/
abbrev Differential :=
  ∀ n, Cochains h (M := M) n →ₗ[k] Cochains h (M := M) (n+1)

/-- Boundaries inside the cycles; degree zero has no incoming differential.
For square-zero differentials the successor term is exactly the image of d. -/
def cocycleBoundaries (δ : Differential h (M := M)) :
    (n : ℕ) → Submodule k (LinearMap.ker (δ n))
  | 0 => ⊥
  | n+1 => (LinearMap.range (δ n)).comap (LinearMap.ker (δ (n+1))).subtype

/-- Ordinary cohomology as cycles modulo boundaries, in every degree. -/
abbrev Cohomology (δ : Differential h (M := M)) (n : ℕ) :=
  LinearMap.ker (δ n) ⧸ cocycleBoundaries h δ n

/-- The class of a cocycle in this actual quotient. -/
abbrev cohomologyClass (δ : Differential h (M := M)) (n : ℕ) :
    LinearMap.ker (δ n) →ₗ[k] Cohomology h δ n :=
  (cocycleBoundaries h δ n).mkQ

/-- All the cochain calculus identities use the same operators and the
same given coefficient representation. -/
structure CochainCalculus (ρ : Representation k g M) where
  d : Differential h (M := M)
  L : ∀ n, Representation k g (Cochains h (M := M) n)
  i : ∀ n, h → Cochains h (M := M) (n+1) →ₗ[k] Cochains h (M := M) n
  d_formula : HasDifferentialFormula h ρ d
  d_squared : ∀ n, (d (n+1)).comp (d n) = 0
  L_formula : HasDerivativeFormula h ρ (fun n => L n)
  i_formula : HasInsertionFormula h i
  commute : ∀ n y f, d n (L n y f) = L (n+1) y (d n f)
  cartan_zero : ∀ a f, i 0 a (d 0 f) = L 0 a f
  cartan_succ : ∀ n a f, d n (i n a f) + i (n+1) a (d (n+1) f) = L (n+1) a f

/-- Applying the cochain action to a cocycle gives a cocycle. -/
def CochainCalculus.cycleAction {ρ : Representation k g M}
    (c : CochainCalculus h ρ) (n : ℕ) (y : g) (f : LinearMap.ker (c.d n)) :
    LinearMap.ker (c.d n) :=
  ⟨c.L n y f, by
    change c.d n (c.L n y f) = 0
    rw [c.commute, f.property, map_zero]⟩

end AdvancedHomologicalAlgebra.LieQuotientAction

namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
universe u v w
variable {k : Type u} [CommRing k]
/-- A compatible unital U-module has its original underlying representation. -/
abbrev moduleRepresentation (L : Type*) [LieRing L] [LieAlgebra k L]
    (P : Type*) [AddCommGroup P] [Module k P] [Module (U k L) P]
    [IsScalarTower k (U k L) P] : Representation k L P :=
  (representationEquiv k L P).symm (Algebra.lsmul k k P)


end AdvancedHomologicalAlgebra.LieQuotientAction

namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie P103.Specs.Ch10.Comparison
universe u v w
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable {M : Type w} [AddCommGroup M] [Module (U k g) M]
/-- Canonical k-module structure on the unaltered terms of the ambient resolution. -/
abbrev resolutionTermModule (I : InjectiveResolution (U k g) M) (n : ℕ) :
    Module k (I.complex.X n) := underlyingModule k g (I.complex.X n)

attribute [local instance] resolutionTermModule

instance resolutionTermTower (I : InjectiveResolution (U k g) M) (n : ℕ) :
    IsScalarTower k (U k g) (I.complex.X n) :=
  IsScalarTower.of_compHom k (U k g) (I.complex.X n)

/-- The ambient representation on each term is the representation of its actual U(g)-action. -/
abbrev resolutionTermRepresentation (I : InjectiveResolution (U k g) M) (n : ℕ) :
    Representation k g (I.complex.X n) := moduleRepresentation g (I.complex.X n)


end AdvancedHomologicalAlgebra.LieQuotientAction

namespace Specs.AdvancedHomologicalAlgebra.LieQuotientAction
open _root_.Shared.Lie _root_.AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
universe u v w w'
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] resolutionTermModule

/-- Existence of the actual quotient representation on the invariant subspace. -/
def invariantActionExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type w) [AddCommGroup M] [Module k M]
    (ρ : Representation k g M),
    ∃ σ : Representation k (g ⧸ h) (invariants h ρ), IsInvariantAction h ρ σ

/-- The right adjunction, on all morphisms, fixes the underlying map in both
 directions. This characterizes the bijection uniquely, and hence naturally. -/
def adjunctionExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type w) [AddCommGroup M] [Module k M]
    (ρ : Representation k g M)
    (σ : Representation k (g ⧸ h) (invariants h ρ)), IsInvariantAction h ρ σ →
    ∀ (N : Type w') [AddCommGroup N] [Module k N]
      (τ : Representation k (g ⧸ h) N),
      ∃ e : Morphism (inflation h τ) ρ ≃ Morphism τ σ,
        (∀ f n, ((e f).val n : M) = f.val n) ∧
        (∀ f n, (e.symm f).val n = (f.val n : M))

/-- The composite of the two invariant operations is g-invariants on vectors. -/
def compositeExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type w) [AddCommGroup M] [Module k M]
    (ρ : Representation k g M)
    (σ : Representation k (g ⧸ h) (invariants h ρ)), IsInvariantAction h ρ σ →
    ∀ m : invariants h ρ, (∀ z, σ z m = 0) ↔ ∀ y, ρ y (m : M) = 0

/-- Actual injectivity over the enveloping algebra of the quotient, from
 actual injectivity over U(g), with no assumed lifting certificate. -/
def injectiveExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type (max u v w)) [AddCommGroup M] [Module k M]
    (ρ : Representation k g M)
    (σ : Representation k (g ⧸ h) (invariants h ρ)), IsInvariantAction h ρ σ →
    letI := actionModule k g M (representationEquiv k g M ρ)
    Module.Injective (U k g) M →
    letI := actionModule k (g ⧸ h) (invariants h ρ)
      (representationEquiv k (g ⧸ h) (invariants h ρ) σ)
    Module.Injective (U k (g ⧸ h)) (invariants h ρ)

/-- Inflation preserves every short exact sequence, including both endpoint
 conditions, on the unchanged underlying maps. -/
def inflationExactExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (X Y Z : Type w)
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    (α : Representation k (g ⧸ h) X) (β : Representation k (g ⧸ h) Y)
    (γ : Representation k (g ⧸ h) Z) (f : Morphism α β) (t : Morphism β γ),
    Function.Injective f.val → Function.Exact f.val t.val → Function.Surjective t.val →
    Function.Injective (inflateMorphism h f).val ∧
      Function.Exact (inflateMorphism h f).val (inflateMorphism h t).val ∧
      Function.Surjective (inflateMorphism h t).val

/-- All-degree construction of the printed operators and Cartan identity,
 including the separate degree-zero identity. -/
def cartanExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type w) [AddCommGroup M] [Module k M]
    (ρ : Representation k g M),
    ∃ (δ : ∀ n, Cochains h (M := M) n →ₗ[k] Cochains h (M := M) (n+1))
      (L : ∀ n, g → Module.End k (Cochains h (M := M) n))
      (I : ∀ n, h → Cochains h (M := M) (n+1) →ₗ[k] Cochains h (M := M) n),
      HasDifferentialFormula h ρ δ ∧
      (∀ n, (δ (n+1)).comp (δ n) = 0) ∧
      HasDerivativeFormula h ρ L ∧ HasInsertionFormula h I ∧
      (∀ a f, I 0 a (δ 0 f) = L 0 a f) ∧
      (∀ n a f, δ n (I n a f) + I (n+1) a (δ (n+1) f) = L (n+1) a f)

/-- The printed all-degree operators form a Lie action by cochain maps
and satisfy Cartan's homotopy formula, with no dimension restriction. -/
def calculusExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type w) [AddCommGroup M] [Module k M]
    (ρ : Representation k g M), Nonempty (CochainCalculus h ρ)

/-- The quotient Lie action is fixed on every cocycle class by the printed
cochain action. Thus this is the actual action on CE cohomology. -/
def quotientCohomologyExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type w) [AddCommGroup M] [Module k M]
    (ρ : Representation k g M),
    ∃ c : CochainCalculus h ρ,
    ∃ σ : ∀ n, Representation k (g ⧸ h) (Cohomology h c.d n),
      ∀ n y f, σ n (quotientMap k g h y) (cohomologyClass h c.d n f) =
        cohomologyClass h c.d n (CochainCalculus.cycleAction h c n y f)


/-- The canonical degree-zero identification evaluates a cocycle on the
empty wedge and respects the quotient actions on cohomology and invariants. -/
def degreeZeroExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type w) [AddCommGroup M] [Module k M]
    (ρ : Representation k g M) (c : CochainCalculus h ρ),
    ∃ (σ : ∀ n, Representation k (g ⧸ h) (Cohomology h c.d n))
      (τ : Representation k (g ⧸ h) (invariants h ρ))
      (e : Cohomology h c.d 0 ≃ₗ[k] invariants h ρ),
      (∀ n y f, σ n (quotientMap k g h y) (cohomologyClass h c.d n f) =
        cohomologyClass h c.d n (CochainCalculus.cycleAction h c n y f)) ∧
      IsInvariantAction h ρ τ ∧
      (∀ f, (e (cohomologyClass h c.d 0 f) : M) =
        f.val (_root_.AdvancedHomologicalAlgebra.CE.wedge k h 0 Fin.elim0)) ∧ LieIntertwines (σ 0) τ e.toLinearMap

/-- Every coefficient intertwiner induces the usual cohomology map by
postcomposition, and this map is a quotient-Lie-module morphism. The class
formula fixes the map uniquely and therefore gives identities and composition. -/
def coefficientNaturalityExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type w) [AddCommGroup M] [Module k M]
    (ρ : Representation k g M) (c : CochainCalculus h ρ)
    (P : Type w') [AddCommGroup P] [Module k P]
    (ρ' : Representation k g P) (c' : CochainCalculus h ρ'),
    ∃ (σ : ∀ n, Representation k (g ⧸ h) (Cohomology h c.d n))
      (σ' : ∀ n, Representation k (g ⧸ h) (Cohomology h c'.d n)),
      (∀ n y f, σ n (quotientMap k g h y) (cohomologyClass h c.d n f) =
        cohomologyClass h c.d n (CochainCalculus.cycleAction h c n y f)) ∧
      (∀ n y f, σ' n (quotientMap k g h y) (cohomologyClass h c'.d n f) =
        cohomologyClass h c'.d n (CochainCalculus.cycleAction h c' n y f)) ∧
      ∀ a : Morphism ρ ρ', ∃ F : ∀ n, Cohomology h c.d n →ₗ[k] Cohomology h c'.d n,
        (∀ n f, ∃ f' : LinearMap.ker (c'.d n),
          f'.val = a.val.comp f.val ∧
          F n (cohomologyClass h c.d n f) = cohomologyClass h c'.d n f') ∧
        ∀ n, LieIntertwines (σ n) (σ' n) (F n)


/-- The printed quotient action agrees with derived ideal invariants on every
actual ambient injective resolution. The term identifications and differential
formula require the actual invariant complex, in all degrees and all ranks. -/
def resolutionComparisonExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type w) [AddCommGroup M] [Module k M]
    [Module (U k g) M] [IsScalarTower k (U k g) M]
    (I : InjectiveResolution (U k g) M),
    ∃ c : CochainCalculus h (moduleRepresentation g M),
    ∃ (σ : ∀ n, Representation k (g ⧸ h) (Cohomology h c.d n))
      (K : CochainComplex (ModuleCat.{max u v w} k) ℕ)
      (term : ∀ n, K.X n ≃ₗ[k] invariants h (resolutionTermRepresentation I n))
      (τ : ∀ n, Representation k (g ⧸ h) (K.X n))
      (χ : ∀ n, Representation k (g ⧸ h) (Homology K n))
      (e : ∀ n, Cohomology h c.d n ≃ₗ[k] Homology K n),
      (∀ n y f, σ n (quotientMap k g h y) (cohomologyClass h c.d n f) =
        cohomologyClass h c.d n (CochainCalculus.cycleAction h c n y f)) ∧
      (∀ n y x, (term n (τ n (quotientMap k g h y) x) : I.complex.X n) =
        inclusion k g y • (term n x : I.complex.X n)) ∧
      (∀ n x, (term (n+1) ((K.d n (n+1)).hom x) : I.complex.X (n+1)) =
        (I.complex.d n (n+1)).hom (term n x : I.complex.X n)) ∧
      (∀ n (y : g ⧸ h) (z : cycles K n), ∃ z' : cycles K n, z'.val = τ n y z.val ∧
        χ n y (homologyClass K n z) = homologyClass K n z') ∧
      (∀ n, LieIntertwines (σ n) (χ n) (e n).toLinearMap)

end Specs.AdvancedHomologicalAlgebra.LieQuotientAction
