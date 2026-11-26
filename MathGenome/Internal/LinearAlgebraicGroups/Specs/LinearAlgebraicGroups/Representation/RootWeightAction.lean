import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelPositivity
import Mathlib.Algebra.DirectSum.Module

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj DirectSum

universe u

namespace LinearAlgebraicGroups.Specs.RootWeightAction

open AbstractPairing (Datum Root)
open AdjointRepresentation (GroupPoints)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open CharacterPairing (characterValue)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {G : AffineAlgebraicGroup k}

/-- A rational representation in a finite basis, expressed as the natural homomorphism
to the represented general linear functor. A choice of basis identifies every
finite-dimensional representation with this formulation. -/
abbrev Representation (G : GroupScheme k) (I : Type u) [Fintype I] [DecidableEq I] :=
  (groupPointsFunctor k).obj G ⟶ StandardGroups.generalLinearPoints k I

/-- Extend a vector in the given basis to a test algebra. -/
def extendVector (R : TestAlgebra k) (v : I → k) : I → R :=
  fun i ↦ algebraMap k R (v i)

/-- Matrix action at a point over a commutative test algebra. -/
def act {H : GroupScheme k} (ρ : Representation H I)
    (R : TestAlgebra k) (g : GroupPoints H R) (v : I → R) : I → R :=
  (ρ.app R g : Matrix.GeneralLinearGroup I R).val.mulVec v

/-- Extension of vectors, viewed as a linear map over the base field. -/
def extendLinear (R : TestAlgebra k) : (I → k) →ₗ[k] (I → R) where
  toFun := extendVector R
  map_add' a b := funext fun i ↦ map_add (algebraMap k R) (a i) (b i)
  map_smul' a v := by
    funext i
    change algebraMap k R (a * v i) = a • algebraMap k R (v i)
    rw [Algebra.smul_def, map_mul]

/-- The linear action of one group point over its test algebra. -/
def actLinear {H : GroupScheme k} (ρ : Representation H I)
    (R : TestAlgebra k) (g : GroupPoints H R) : (I → R) →ₗ[R] (I → R) where
  toFun := act ρ R g
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _

/-- The weight space tests the character identity after every scalar extension. -/
def weightSpace (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    (chi : Character T.group) : Submodule k (I → k) :=
  ⨅ (R : TestAlgebra k) (t : GroupPoints T.group R),
    LinearMap.ker (((actLinear ρ R (t ≫ T.inclusion.hom.hom)).restrictScalars k).comp
      (extendLinear R) - (characterValue chi R t) • extendLinear R)

theorem mem_weightSpace {ρ : Representation G.val I} {T : ClosedSubgroup G.val}
    {chi : Character T.group} {v : I → k} :
    v ∈ weightSpace ρ T chi ↔ ∀ (R : TestAlgebra k) (t : GroupPoints T.group R),
      act ρ R (t ≫ T.inclusion.hom.hom) (extendVector R v) =
        characterValue chi R t • extendVector R v := by
  simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    sub_eq_zero, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.smul_apply]
  rfl

/-- Fixed vectors for the subgroup map, tested over all commutative algebras. -/
def fixedSpace (ρ : Representation G.val I) {H : GroupScheme k}
    (f : H ⟶ G.val) : Submodule k (I → k) :=
  ⨅ (R : TestAlgebra k) (g : GroupPoints H R),
    LinearMap.ker (((actLinear ρ R (g ≫ f.hom.hom)).restrictScalars k).comp
      (extendLinear R) - extendLinear R)

theorem mem_fixedSpace {ρ : Representation G.val I} {H : GroupScheme k} {f : H ⟶ G.val}
    {v : I → k} :
    v ∈ fixedSpace ρ f ↔ ∀ (R : TestAlgebra k) (g : GroupPoints H R),
      act ρ R (g ≫ f.hom.hom) (extendVector R v) = extendVector R v := by
  simp only [fixedSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    sub_eq_zero, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rfl

/-- The simple roots are the indecomposable positive roots in the chosen Borel. -/
def SimpleRoot (T B : ClosedSubgroup G.val) :=
  {alpha : Root T // alpha ∈ subgroupRoots T B ∧
    ∀ beta ∈ subgroupRoots T B, ∀ gamma ∈ subgroupRoots T B, alpha.val ≠ beta.val * gamma.val}

/-- Dominance order in the additive notation on the character lattice. -/
def DominanceLE (T B : ClosedSubgroup G.val) (mu lam : Character T.group) : Prop :=
  ∃ c : SimpleRoot T B →₀ ℕ,
    Additive.ofMul (lam / mu) = c.sum (fun alpha n ↦ n • Additive.ofMul alpha.val.val)

/-- A character is dominant when its simple-coroot pairings are nonnegative. -/
def IsDominant {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) (B : ClosedSubgroup G.val) (lam : Character T.group) : Prop :=
  ∀ alpha : SimpleRoot T B,
    0 ≤ D.rootDatum.toLinearMap (Additive.ofMul lam) (D.rootDatum.coroot alpha.val)

/-- A primitive vector is nonzero, fixed by the unipotent radical and of the given weight. -/
def IsPrimitive (ρ : Representation G.val I) (T B : ClosedSubgroup G.val)
    (U : ClosedSubgroup B.group) (mu : Character T.group) (v : I → k) : Prop :=
  v ≠ 0 ∧ v ∈ fixedSpace ρ (U.inclusion ≫ B.inclusion) ∧ v ∈ weightSpace ρ T mu

/-- For a torus-equivariant root coordinate, coefficients of the orbit polynomial
have the specified shifted weights. The identity holds over all commutative test
algebras. There are finitely many coordinates, each with finite polynomial support. -/
def RootOrbit (ρ : Representation G.val I) (T : ClosedSubgroup G.val) : Prop :=
  ∀ (alpha : Root T) (H : ClosedSubgroup G.val), IsRootSubgroup T H alpha.val →
    ∀ (A : AdditiveLine k) (x : A.group ≅ H.group),
    HasScalarAction T alpha.val (x.hom ≫ H.inclusion) →
    ∀ (mu : Character T.group) (v : weightSpace ρ T mu),
      ∃ p : I → Polynomial k,
        (fun i ↦ (p i).coeff 0) = (v : I → k) ∧
        (∀ j : ℕ, 0 < j → (fun i ↦ (p i).coeff j) ∈ weightSpace ρ T (mu * alpha.val ^ j)) ∧
        ∀ (R : TestAlgebra k) (c : R),
          act ρ R (rootPoint (x.hom ≫ H.inclusion) R c) (extendVector R v) =
            fun i ↦ Polynomial.aeval c (p i)

/-- Each rational representative of the Weyl element acts by the indicated
linear isomorphism of weight spaces. -/
def WeylTransport (ρ : Representation G.val I) {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} (e : DatumAndWeyl.Identification D) : Prop :=
  let K := CommAlgCat.of k k
  ∀ (w : D.rootDatum.weylGroup) (n : GroupPoints e.normalizer.group K),
    n ≫ e.quotient.hom.hom =
        toUnit _ ≫ e.image.constantGroup.sectionPoint (e.labelEquiv w) →
    ∀ mu : Character T.group,
      ∃ F : weightSpace ρ T mu ≃ₗ[k] weightSpace ρ T ((e.labelEquiv w).val mu),
        ∀ v, (F v : I → k) = act ρ K (n ≫ e.normalizer.inclusion.hom.hom) v

/-- The fixed subspace is stable over all test algebras, with scalar extension
described as the span of the extended fixed vectors. -/
def TorusStable (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    (M : Submodule k (I → k)) : Prop :=
  ∀ (R : TestAlgebra k) (t : GroupPoints T.group R) (v : M),
    act ρ R (t ≫ T.inclusion.hom.hom) (extendVector R v) ∈
      Submodule.span R (Set.range fun w : M ↦ extendVector R w)

/-- Root orbit weights, Weyl transport, primitive lines, and the decomposition
of the unipotent fixed space for a split Borel pair. -/
def Statement : Prop := by
  classical
  exact ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsSubgroupOf T B →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ (D : Datum T) (e : DatumAndWeyl.Identification D)
          (U : ClosedSubgroup B.group) (q : B.group ⟶ T.group),
          IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U ∧
          (∃ j : T.group ⟶ B.group, j ≫ B.inclusion = T.inclusion ∧ j ≫ q = 𝟙 T.group ∧
            IsPullback U.inclusion.hom.hom (toUnit _) q.hom.hom η[T.group.X]) ∧
          ∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I),
            RootOrbit ρ T ∧ WeylTransport ρ e ∧
            (∀ (mu : Character T.group) (v : I → k), IsPrimitive ρ T B U mu v →
              ∀ (R : TestAlgebra k) (b : GroupPoints B.group R),
                act ρ R (b ≫ B.inclusion.hom.hom) (extendVector R v) =
                  characterValue mu R (b ≫ q.hom.hom) • extendVector R v) ∧
            let M := fixedSpace ρ (U.inclusion ≫ B.inclusion)
            TorusStable ρ T M ∧
              DirectSum.IsInternal (fun mu : Character T.group ↦ (weightSpace ρ T mu).comap M.subtype)

end

end LinearAlgebraicGroups.Specs.RootWeightAction
