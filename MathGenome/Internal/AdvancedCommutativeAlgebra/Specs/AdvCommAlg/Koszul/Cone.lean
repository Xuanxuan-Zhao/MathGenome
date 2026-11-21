import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.TensorDecomposition
import Mathlib.Tactic.Abel

/-! RK-05, paper.tex:2208–2234. The cone is nonnegative: its zeroth
term is C₀, and its (n+1)st term is Cₙ₊₁ × Cₙ. This prevents a
spurious second copy of C₀ from appearing in degree zero. -/
open CategoryTheory
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w

namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]

/-- Terms of the cone of scalar multiplication, with absent negative terms zero. -/
@[implicit_reducible] def scalarConeTerm (C : ChainComplex (ModuleCat.{v} R) ℕ) : ℕ → ModuleCat.{v} R
  | 0 => C.X 0
  | n+1 => ModuleCat.of R (C.X (n+1) × C.X n)

/-- The cone boundary (da + yb, -db); at degree one only da+yb remains. -/
def scalarConeDifferential (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R) :
    ∀ n, scalarConeTerm C (n+1) →ₗ[R] scalarConeTerm C n
  | 0 => (C.d 1 0).hom.comp (LinearMap.fst R _ _) + y • LinearMap.snd R _ _
  | n+1 =>
      ((C.d (n+2) (n+1)).hom.comp (LinearMap.fst R _ _) +
        y • LinearMap.snd R _ _).prod
      (-((C.d (n+1) n).hom.comp (LinearMap.snd R _ _)))

private theorem scalarConeDifferential_comp
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R) (n : ℕ) :
    (scalarConeDifferential C y n).comp (scalarConeDifferential C y (n+1)) = 0 := by
  have hd (k : ℕ) (a : C.X (k+2)) :
      (C.d (k+1) k).hom ((C.d (k+2) (k+1)).hom a) = 0 := by
    have h := congrArg ModuleCat.Hom.hom (C.d_comp_d (k+2) (k+1) k)
    exact LinearMap.congr_fun h a
  cases n with
  | zero =>
    apply LinearMap.ext
    rintro ⟨a,b⟩
    change (C.d 1 0).hom ((C.d 2 1).hom a + y • b) +
      y • (-(C.d 1 0).hom b) = 0
    simp [hd]
  | succ n =>
    apply LinearMap.ext
    rintro ⟨a,b⟩
    apply Prod.ext
    · change (C.d (n+2) (n+1)).hom ((C.d (n+3) (n+2)).hom a + y • b) +
        y • (-(C.d (n+2) (n+1)).hom b) = 0
      simp [hd]
    · change -((C.d (n+1) n).hom (-(C.d (n+2) (n+1)).hom b)) = 0
      simp [hd]

/-- The mapping cone of multiplication by y, in the source's coordinates. -/
@[implicit_reducible] def scalarCone (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R) :
    ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (scalarConeTerm C)
    (fun n => ModuleCat.ofHom (scalarConeDifferential C y n))
    (fun n => ModuleCat.hom_ext (scalarConeDifferential_comp C y n))

/-- The inclusion of C in its scalar cone. -/
def scalarConeInclusion (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R) :
    C ⟶ scalarCone C y :=
  ChainComplex.ofHom
    (fun n => match n with
      | 0 => 𝟙 _
      | n+1 => ModuleCat.ofHom (LinearMap.inl R (C.X (n+1)) (C.X n)))
    (fun n => by
      have hd : (scalarCone C y).d (n+1) n =
          ModuleCat.ofHom (scalarConeDifferential C y n) := by
        dsimp only [scalarCone]
        exact ChainComplex.of_d _ _ n
      rw [hd]
      cases n with
      | zero =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change (C.d 1 0).hom a + y • 0 = (C.d 1 0).hom a
        simp
      | succ n =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change ((C.d (n+2) (n+1)).hom a + y • 0, -(C.d (n+1) n).hom 0) =
          ((C.d (n+2) (n+1)).hom a, 0)
        simp)

/-- Multiplication on a homology module. -/
def homologyScalar (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R) (n : ℕ) :
    C.homology n ⟶ C.homology n := ModuleCat.ofHom (y • LinearMap.id)

/-- Inclusion of the old positions when a last entry is appended. -/
def appendOldLinear (x : List R) (y : R) :
    (Fin x.length → R) →ₗ[R] (Fin (x ++ [y]).length → R) where
  toFun a i := if h : i.val < x.length then a ⟨i.val, h⟩ else 0
  map_add' a b := by ext i; dsimp; split <;> simp
  map_smul' r a := by ext i; dsimp; split <;> simp

/-- The new last standard basis vector. -/
def appendLastVector (x : List R) (y : R) : Fin (x ++ [y]).length → R :=
  Pi.single ⟨x.length, by simp⟩ 1

/-- Wedge by the appended vector on the left. -/
def appendWedgeLinear (x : List R) (y : R) (n : ℕ) :
    (⋀[R]^n (Fin x.length → R)) →ₗ[R]
      (⋀[R]^(n+1) (Fin (x ++ [y]).length → R)) where
  toFun b :=
    ⟨ExteriorAlgebra.ι R (appendLastVector x y) *
        ExteriorAlgebra.map (appendOldLinear x y) b, by
      have h := SetLike.mul_mem_graded
        (show ExteriorAlgebra.ι R (appendLastVector x y) ∈
          ⋀[R]^1 (Fin (x ++ [y]).length → R) from by simp)
        (exteriorPower.map n (appendOldLinear x y) b).property
      simpa only [Nat.add_comm 1 n, exteriorPower.coe_map] using h⟩
  map_add' a b := by apply Subtype.ext; simp [mul_add]
  map_smul' r a := by apply Subtype.ext; simp

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Old summand of the appended coefficient complex. -/
def appendCoefficientOld (x : List R) (y : R) (n : ℕ) :
    (coefficientComplex M x).X n →ₗ[R] (coefficientComplex M (x ++ [y])).X n :=
  TensorProduct.map (exteriorPower.map n (appendOldLinear x y)) LinearMap.id

/-- New summand of the appended coefficient complex, in left-wedge coordinates. -/
def appendCoefficientWedge (x : List R) (y : R) (n : ℕ) :
    (coefficientComplex M x).X n →ₗ[R] (coefficientComplex M (x ++ [y])).X (n+1) :=
  TensorProduct.map (appendWedgeLinear x y n) LinearMap.id

/-- The prescribed component of the cone comparison (a,b) ↦ a+e∧b. -/
def appendComparisonComponent (x : List R) (y : R) :
    ∀ n, (scalarCone (coefficientComplex M x) y).X n →ₗ[R]
      (coefficientComplex M (x ++ [y])).X n
  | 0 => appendCoefficientOld M x y 0
  | n+1 =>
      (appendCoefficientOld M x y (n+1)).comp (LinearMap.fst R _ _) +
        (appendCoefficientWedge M x y n).comp (LinearMap.snd R _ _)

/-- The isomorphism uses the source's left-wedge convention in every degree. -/
def IsAppendConeComparison (x : List R) (y : R)
    (e : scalarCone (coefficientComplex M x) y ≅ coefficientComplex M (x ++ [y])) : Prop :=
  ∀ n, e.hom.f n = ModuleCat.ofHom (appendComparisonComponent M x y n)

/-- Change of coefficient modules, acting as the identity on each exterior power. -/
def appendCoefficientMap {N : Type v} [AddCommGroup N] [Module R N]
    (x : List R) (φ : M →ₗ[R] N) : coefficientComplex M x ⟶ coefficientComplex N x :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (TensorProduct.map LinearMap.id φ))
    (fun n => by
      have hd (L : Type v) [AddCommGroup L] [Module R L] :
          (coefficientComplex L x).d (n+1) n =
            ModuleCat.ofHom (coefficientDifferential L x n) := by
        dsimp only [coefficientComplex]
        exact ChainComplex.of_d _ _ n
      rw [hd M, hd N]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro m
      rfl)

/-- Inclusion into the appended Koszul complex using a cone comparison. -/
def appendInclusion (x : List R) (y : R)
    (e : scalarCone (coefficientComplex M x) y ≅ coefficientComplex M (x ++ [y])) :
    coefficientComplex M x ⟶ coefficientComplex M (x ++ [y]) :=
  scalarConeInclusion (coefficientComplex M x) y ≫ e.hom

/-- The full long exact sequence, including its endpoint and its prescribed
map on cycle representatives. Exactness at every multiplication map connects
the adjacent displayed five-term segments. -/
structure AppendConeSequence (x : List R) (y : R) where
  comparison : scalarCone (coefficientComplex M x) y ≅ coefficientComplex M (x ++ [y])
  canonical : IsAppendConeComparison M x y comparison
  projection : ∀ n, homology M (x ++ [y]) (n+1) ⟶ homology M x n
  cycleProjection : ∀ n, (scalarCone (coefficientComplex M x) y).cycles (n+1) ⟶
    (coefficientComplex M x).cycles n
  cycleProjection_i : ∀ n,
    cycleProjection n ≫ (coefficientComplex M x).iCycles n =
      (scalarCone (coefficientComplex M x) y).iCycles (n+1) ≫
        ModuleCat.ofHom (LinearMap.snd R _ _)
  projection_class : ∀ n,
    (scalarCone (coefficientComplex M x) y).homologyπ (n+1) ≫
        HomologicalComplex.homologyMap comparison.hom (n+1) ≫ projection n =
      cycleProjection n ≫ (coefficientComplex M x).homologyπ n
  exact_multiply_inclusion : ∀ n,
    Function.Exact (homologyScalar (coefficientComplex M x) y n).hom
      (HomologicalComplex.homologyMap (appendInclusion M x y comparison) n).hom
  exact_inclusion_projection : ∀ n,
    Function.Exact
      (HomologicalComplex.homologyMap (appendInclusion M x y comparison) (n+1)).hom
      (projection n).hom
  exact_projection_multiply : ∀ n,
    Function.Exact (projection n).hom (homologyScalar (coefficientComplex M x) y n).hom
  surjective_zero : Function.Surjective
    (HomologicalComplex.homologyMap (appendInclusion M x y comparison) 0).hom

end AdvCommAlg.Koszul

namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

/-- Full coefficient comparison, without flatness or characteristic restrictions. -/
def appendConeComparison : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (y : R),
    ∃ e : scalarCone (coefficientComplex M x) y ≅ coefficientComplex M (x ++ [y]),
      IsAppendConeComparison M x y e

/-- RK-05: the stated five-term segments in all positive degrees and the
right-exact degree-zero endpoint, with the canonical cone comparison and signs. -/
def appendLongExactSequence : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (y : R), Nonempty (AppendConeSequence M x y)

/-- Naturality under arbitrary linear changes of coefficient module. The
sequence maps are fixed by their maps on cycles, so this holds for every
choice of data satisfying the complete sequence interface. -/
def appendSequenceNaturality : Prop :=
  ∀ {R : Type u} [CommRing R] (M N : Type v)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : List R) (y : R) (φ : M →ₗ[R] N)
    (S : AppendConeSequence M x y) (T : AppendConeSequence N x y),
    (∀ n, HomologicalComplex.homologyMap (appendCoefficientMap M x φ) n ≫
        HomologicalComplex.homologyMap (appendInclusion N x y T.comparison) n =
      HomologicalComplex.homologyMap (appendInclusion M x y S.comparison) n ≫
        HomologicalComplex.homologyMap (appendCoefficientMap M (x ++ [y]) φ) n) ∧
    (∀ n, HomologicalComplex.homologyMap (appendCoefficientMap M (x ++ [y]) φ) (n+1) ≫
        T.projection n =
      S.projection n ≫ HomologicalComplex.homologyMap (appendCoefficientMap M x φ) n)

end Specs.AdvCommAlg.Koszul
