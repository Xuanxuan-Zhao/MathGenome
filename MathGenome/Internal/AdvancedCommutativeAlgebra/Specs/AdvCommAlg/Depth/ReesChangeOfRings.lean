import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Torsion.Basic

/-! Independent statements for DP-14, paper.tex:3170–3206.
All modules are arbitrary. `Small` is solely a universe condition for Mathlib's
Ext groups; it imposes no finite generation or cardinal bound on a module.
The two module arguments may be placed in any common universe containing R.
The quotient and its scalar action are the canonical M/IM and R/I actions. -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise ModuleCat.Algebra
universe u v
namespace AdvCommAlg.Depth.Rees
variable {R : Type u} [CommRing R]

/-- The canonical quotient module, as an R/I-module. -/
abbrev quotientModule (I : Ideal R) (M : ModuleCat.{v} R) : ModuleCat.{v} (R ⧸ I) :=
  ModuleCat.of (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))

/-- The ordinary quotient map induced by a coefficient map. -/
def quotientMap (I : Ideal R) {M M' : ModuleCat.{v} R} (f : M ⟶ M') :
    quotientModule I M ⟶ quotientModule I M' :=
  ModuleCat.ofHom
    { toFun := Submodule.mapQ _ _ f.hom (Submodule.smul_top_le_comap_smul_top I f.hom)
      map_add' := map_add _
      map_smul' := by
        intro a q
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        induction q using Submodule.Quotient.induction_on with
        | _ m =>
          change Submodule.Quotient.mk (f.hom (r • m)) =
            Submodule.Quotient.mk (r • f.hom m)
          rw [f.hom.map_smul] }

/-- A family of linear Ext comparisons, natural contravariantly in N and
covariantly in every coefficient homomorphism between modules satisfying P.
`d` counts the actual number of regular elements. -/
structure ExtShiftComparison [Small.{v} R] (I : Ideal R) (d : ℕ)
    (P : ModuleCat.{v} R → Prop) where
  equiv (M : ModuleCat.{v} R) (hM : P M) (N : ModuleCat.{v} (R ⧸ I)) (j : ℕ) :
    Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N) M (j + d) ≃ₗ[R]
      Ext N (quotientModule I M) j
  naturality_source (M : ModuleCat.{v} R) (hM : P M)
    {N N' : ModuleCat.{v} (R ⧸ I)} (f : N ⟶ N') (j : ℕ)
    (a : Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N') M (j + d)) :
    equiv M hM N j
        ((Ext.mk₀ ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map f)).comp a
          (zero_add _)) =
      (Ext.mk₀ f).comp (equiv M hM N' j a) (zero_add _)
  naturality_target {M M' : ModuleCat.{v} R} (hM : P M) (hM' : P M') (f : M ⟶ M')
    (N : ModuleCat.{v} (R ⧸ I)) (j : ℕ)
    (a : Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N) M (j + d)) :
    equiv M' hM' N j (a.comp (Ext.mk₀ f) (add_zero _)) =
      (equiv M hM N j a).comp (Ext.mk₀ (quotientMap I f)) (add_zero _)

end AdvCommAlg.Depth.Rees

namespace Specs.AdvCommAlg.Depth.ReesChangeOfRings
open _root_.AdvCommAlg.Depth.Rees

/-- The Hom conclusion, under the weaker hypotheses actually needed for it. -/
def homVanishing : Prop :=
  ∀ {R : Type u} [CommRing R] (x : R) (M : ModuleCat.{v} R), IsSMulRegular M x →
    ∀ N : ModuleCat.{v} (R ⧸ Ideal.span {x}),
      Subsingleton (((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N) ⟶ M)

/-- The full one-element comparison, including j=0 and naturality in both arguments. -/
def singleChangeOfRings : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (x : R), IsSMulRegular R x →
    Nonempty (ExtShiftComparison (Ideal.span {x}) 1 (fun M => IsSMulRegular M x))

/-- The degree-zero case is recorded separately for incremental construction. -/
def singleDegreeZero : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (x : R) (M : ModuleCat.{v} R),
    IsSMulRegular M x → ∀ N : ModuleCat.{v} (R ⧸ Ideal.span {x}),
      Nonempty (Ext ((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (Ideal.span {x}))).obj N) M 1 ≃ₗ[R]
          Ext N (quotientModule (Ideal.span {x}) M) 0)

/-- The iterated comparison for the actual quotient by the ideal of the whole list.
The empty list is included, and no ring/module finiteness is imposed. -/
def iteratedChangeOfRings : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (xs : List R),
    RingTheory.Sequence.IsRegular R xs →
      Nonempty (ExtShiftComparison (Ideal.ofList xs) xs.length
        (fun M => RingTheory.Sequence.IsRegular M xs))

/-- The degrees strictly below the length vanish for every R/(xs)-module. -/
def regularSequenceVanishing : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (xs : List R),
    RingTheory.Sequence.IsRegular R xs → ∀ M : ModuleCat.{v} R,
      RingTheory.Sequence.IsRegular M xs → ∀ N : ModuleCat.{v} (R ⧸ Ideal.ofList xs),
        ∀ i : ℕ, i < xs.length →
          Subsingleton (Ext ((ModuleCat.restrictScalars
            (Ideal.Quotient.mk (Ideal.ofList xs))).obj N) M i)

/-- The injectivity-and-annihilation form of the lower-degree vanishing proof. -/
def weaklyRegularVanishing : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (M N : ModuleCat.{v} R)
    (xs : List R), RingTheory.Sequence.IsWeaklyRegular M xs →
      (∀ x ∈ xs, ∀ n : N, x • n = 0) →
        ∀ i : ℕ, i < xs.length → Subsingleton (Ext N M i)

end Specs.AdvCommAlg.Depth.ReesChangeOfRings
