import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Homological.MinimalFreeResolution
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Independent statements for the quotient-ring assertion of DP-13,
paper.tex 3117–3118 and 3158–3165. The quotient has its canonical R/(x)-action.
The resolution assertion records actual exactness after reduction. -/

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvCommAlg

/-- Reduction modulo x, with values in modules over the quotient ring. -/
def regularQuotientFunctor {R : Type u} [CommRing R] (x : R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} (R ⧸ Ideal.span {x}) where
  obj M := ModuleCat.of _ (QuotSMulTop x M)
  map f := ModuleCat.ofHom ((QuotSMulTop.map x f.hom).extendScalarsOfSurjective
    (S := R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (x • (⊤ : Submodule R M)) z
    rfl
  map_comp {M N P} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (x • (⊤ : Submodule R M)) z
    rfl

instance {R : Type u} [CommRing R] (x : R) : (regularQuotientFunctor x).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (x • (⊤ : Submodule R M)) z
    exact Submodule.Quotient.mk_add _

end AdvCommAlg

namespace Specs.AdvCommAlg

/-- The original projective dimension is preserved, including e = 0. -/
def regularQuotient_projectiveDimension : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (x : R), x ∈ IsLocalRing.maximalIdeal R →
    IsSMulRegular R x → IsSMulRegular M x → ∀ e : ℕ,
    projectiveDimension M = (e : WithBot ℕ∞) →
    projectiveDimension ((_root_.AdvCommAlg.regularQuotientFunctor x).obj M) =
      (e : WithBot ℕ∞)

/-- Reduction of a minimal free resolution is genuinely a resolution; the
finite projective dimension bound makes this a finite free resolution. -/
def regularQuotient_resolution : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (x : R), x ∈ IsLocalRing.maximalIdeal R →
    IsSMulRegular R x → IsSMulRegular M x →
    ∀ (P : ProjectiveResolution M), _root_.AdvCommAlg.IsMinimalFreeResolution P →
    ∀ e : ℕ, projectiveDimension M = (e : WithBot ℕ∞) →
    ∃ Q : ProjectiveResolution ((_root_.AdvCommAlg.regularQuotientFunctor x).obj M),
      Q.complex = (((_root_.AdvCommAlg.regularQuotientFunctor x).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex) ∧
      HEq (Q.π.f 0) ((_root_.AdvCommAlg.regularQuotientFunctor x).map (P.π.f 0)) ∧
      (∀ i, Module.Finite (R ⧸ Ideal.span {x}) (Q.complex.X i) ∧
        Module.Free (R ⧸ Ideal.span {x}) (Q.complex.X i)) ∧
      (∀ i, e < i → Subsingleton (Q.complex.X i))

end Specs.AdvCommAlg
