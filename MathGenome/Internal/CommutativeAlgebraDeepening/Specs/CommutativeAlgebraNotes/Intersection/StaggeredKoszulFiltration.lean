import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! The degreewise ideal-power subcomplex of the ordinary list Koszul complex,
and its ordinary quotient complex. -/

open CategoryTheory
open AdvCommAlg.Koszul (coefficientComplex listIdeal)

namespace CommutativeAlgebraNotes.Intersection.StaggeredKoszul

noncomputable section

universe u v

variable {A : Type u} [CommRing A] (E : Type v) [AddCommGroup E] [Module A E]
    (z : List A) (n : ℕ)

/-- The degree-`i` part of the filtration at level `n`. -/
def layer (i : ℕ) : Submodule A ((coefficientComplex E z).X i) :=
  listIdeal z ^ (n - i) • ⊤

/-- The Koszul differential preserves the staggered filtration. -/
def DifferentialStable : Prop :=
  ∀ i : ℕ, layer E z n (i + 1) ≤
    (layer E z n i).comap ((coefficientComplex E z).d (i + 1) i).hom

variable {E z n}

/-- The filtered subcomplex, with the restricted Koszul differential. -/
def filtration (h : DifferentialStable E z n) : ChainComplex (ModuleCat.{max u v} A) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of A (layer E z n i))
    (fun i => ModuleCat.ofHom
      ((((coefficientComplex E z).d (i + 1) i).hom.domRestrict _).codRestrict _
        (fun x => h i x.property)))
    (fun i => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact DFunLike.congr_fun
        (congrArg ModuleCat.Hom.hom ((coefficientComplex E z).d_comp_d (i + 2) (i + 1) i)) x.val)

/-- The canonical inclusion into the Koszul complex. -/
def inclusion (h : DifferentialStable E z n) : filtration h ⟶ coefficientComplex E z :=
  ChainComplex.ofHom (fun i => ModuleCat.ofHom (layer E z n i).subtype)
    (fun i => by dsimp only [filtration]; rw [ChainComplex.of_d]; rfl)

/-- The quotient by the filtered subcomplex, with the induced differential. -/
def quotient (h : DifferentialStable E z n) : ChainComplex (ModuleCat.{max u v} A) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of A (((coefficientComplex E z).X i) ⧸ layer E z n i))
    (fun i => ModuleCat.ofHom
      ((layer E z n (i + 1)).mapQ _ ((coefficientComplex E z).d (i + 1) i).hom (h i)))
    (fun i => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro q
      refine Submodule.Quotient.induction_on _ q ?_
      intro x
      change (layer E z n i).mkQ
        (((coefficientComplex E z).d (i + 1) i)
          (((coefficientComplex E z).d (i + 2) (i + 1)) x)) = 0
      rw [← ModuleCat.comp_apply, (coefficientComplex E z).d_comp_d]
      simp)

/-- The degreewise quotient maps, assembled as a chain map. -/
def projection (h : DifferentialStable E z n) : coefficientComplex E z ⟶ quotient h :=
  ChainComplex.ofHom (fun i => ModuleCat.ofHom (layer E z n i).mkQ)
    (fun i => by dsimp only [quotient]; rw [ChainComplex.of_d]; rfl)

end

end CommutativeAlgebraNotes.Intersection.StaggeredKoszul

namespace Specs.CommutativeAlgebraNotes.Intersection.StaggeredKoszul

open _root_.CommutativeAlgebraNotes.Intersection.StaggeredKoszul

universe u v

def differentialStableType : Prop :=
  ∀ {A : Type u} [CommRing A] (E : Type v) [AddCommGroup E] [Module A E]
    (z : List A) (n : ℕ), DifferentialStable E z n

/-- One bound works for all homological degrees. The quasi-isomorphism is
the projection from the original Koszul complex. These conclusions hold
without locality or a finite-length assumption on the coefficient quotient. -/
def eventualAcyclicType : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] (z : List A),
    ∃ N : ℕ, ∀ n ≥ N, z.length < n ∧
      ∀ h : DifferentialStable E z n, (filtration h).Acyclic ∧ QuasiIso (projection h)

def quotientTermType : Prop :=
  ∀ {A : Type u} [CommRing A] (E : Type v) [AddCommGroup E] [Module A E]
    (z : List A) (n : ℕ) (h : DifferentialStable E z n) (i : ℕ),
    Nonempty ((quotient h).X i ≃ₗ[A]
      (Fin (z.length.choose i) → E ⧸ (listIdeal z ^ (n - i) • (⊤ : Submodule A E))))

def quotientFiniteLengthType : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] (z : List A),
    listIdeal z ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (listIdeal z • (⊤ : Submodule A E))) →
    ∀ (n : ℕ), z.length < n → ∀ (h : DifferentialStable E z n) (i : ℕ),
      IsFiniteLength A ((quotient h).X i)

end Specs.CommutativeAlgebraNotes.Intersection.StaggeredKoszul
