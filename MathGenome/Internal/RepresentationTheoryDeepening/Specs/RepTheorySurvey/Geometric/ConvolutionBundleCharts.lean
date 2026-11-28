import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.GrassmannianCharts
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

namespace RepTheorySurvey.Geometric.ConvolutionBundleChartsSpecs

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open scoped TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {b : Module.Basis (Fin 2 × Fin 1) ℂ V} {b₂ : Module.Basis κ ℂ (V × V)}
variable (C : ChartSystem (k := ℂ) (V := V) b 1) (D : ChartSystem (k := ℂ) (V := V × V) b₂ 2)

abbrev Coefficients (R : TestAlgebra ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] :=
  R ⊗[ℂ] V

/-- The two coefficient vectors of the terminal plane in the truncated lattice window. -/
def terminalPlane (R : TestAlgebra ℂ) (p : Points D.scheme R) :
    Submodule R (Coefficients R V × Coefficients R V) :=
  (D.affinePoints.hom.app R p).toSubmodule.map
    (TensorProduct.prodRight ℂ R R V V).toLinearMap

/-- The image of the immersion is the incidence functor on all affine tests. -/
def AffineIncidence {X : SchemeOver ℂ} (j : X ⟶ C.scheme ⨯ D.scheme) : Prop :=
  ∀ (R : TestAlgebra ℂ) (p : Points (C.scheme ⨯ D.scheme) R),
    let S := (C.affinePoints.hom.app R (p ≫ prod.fst)).toSubmodule
    let P := terminalPlane D R (p ≫ prod.snd)
    (∃ q : Points X R, q ≫ j = p) ↔
      (⊥ : Submodule R (Coefficients R V)).prod S ≤ P ∧ P ≤ S.prod ⊤

/-- In the pivot basis the quotient of the upper coefficient submodule has
coordinates `x_i` and `y_k - z * y_i`, with `k` the complementary index. -/
def pivotQuotient (b : Module.Basis (Fin 2 × Fin 1) ℂ V)
    {I : Pivot (Fin 2 × Fin 1) 1} (i : Inside I) (k : Outside I)
    (R : TestAlgebra ℂ) (z : R) (S : Submodule R (Coefficients R V)) :
    (S.prod (⊤ : Submodule R (Coefficients R V))) →ₗ[R] Coefficients R V :=
  let coord (l : Fin 2 × Fin 1) :=
    (LinearMap.proj (R := R) (φ := fun _ : Fin 2 × Fin 1 ↦ R) l).comp
      (coordinates b R).toLinearMap
  let first := (coord i.val).comp (LinearMap.fst R (Coefficients R V) (Coefficients R V))
  let second := (coord k.val - z • coord i.val).comp
    (LinearMap.snd R (Coefficients R V) (Coefficients R V))
  (coordinates b R).symm.toLinearMap.comp
    ((LinearMap.pi fun l ↦ if l = i.val then first else second).comp (S.prod ⊤).subtype)

/-- The first projection is locally the product with the same line
Grassmannian. The isomorphism sends each terminal plane to its quotient line
in the specified coordinates on each affine test. -/
def BundleCharts : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis (Fin 2 × Fin 1) ℂ V) (b₂ : Module.Basis κ ℂ (V × V))
    (C : ChartSystem (k := ℂ) (V := V) b 1) (D : ChartSystem (k := ℂ) (V := V × V) b₂ 2)
    {X : SchemeOver ℂ} (j : X ⟶ C.scheme ⨯ D.scheme),
    IsClosedImmersion j.left → AffineIncidence C D j →
    let f := j ≫ (prod.fst : C.scheme ⨯ D.scheme ⟶ C.scheme)
    (∀ I : Pivot (Fin 2 × Fin 1) 1,
      ∃ e : pullback f (C.chart I) ≅ (chartScheme (k := ℂ) I ⨯ C.scheme),
        e.hom ≫ prod.fst = pullback.snd f (C.chart I) ∧
        ∀ (R : TestAlgebra ℂ) (q : Points (pullback f (C.chart I)) R)
          (i : Inside I) (k : Outside I),
          let p := q ≫ pullback.snd f (C.chart I)
          let S := (C.affinePoints.hom.app R (p ≫ C.chart I)).toSubmodule
          let P := terminalPlane D R (q ≫ pullback.fst f (C.chart I) ≫ j ≫ prod.snd)
          let L := (C.affinePoints.hom.app R (q ≫ e.hom ≫ prod.snd)).toSubmodule
          let Q := pivotQuotient b i k R (matrixOfPoint I R p k i) S
          Function.Surjective Q ∧
            Q.ker = ((⊥ : Submodule R (Coefficients R V)).prod S).comap (S.prod ⊤).subtype ∧
            L = (P.comap (S.prod ⊤).subtype).map Q) ∧
    Smooth X.hom ∧ IsReduced X.left

end

end RepTheorySurvey.Geometric.ConvolutionBundleChartsSpecs
