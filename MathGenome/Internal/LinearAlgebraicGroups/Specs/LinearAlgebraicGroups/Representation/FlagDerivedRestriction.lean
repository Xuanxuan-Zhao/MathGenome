import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.PolynomialExample

/-! Derived restriction to the origin of an invariant polynomial chart. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped BigOperators TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.FlagDerivedRestriction

open CharacterDescent (Character)
open EquivariantAffineModules
open AdvCommAlg.Koszul
open AdvCommAlg.Koszul.PolynomialExample

noncomputable section
attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}

abbrev polynomialAlgebra (k : Type u) [Field k] (n : ℕ) : TestAlgebra k :=
  CommAlgCat.of k (PolynomialRing k n)

def residueModule (k : Type u) [Field k] (n : ℕ) :
    ModuleCat.{u} (polynomialAlgebra k n) :=
  letI := evaluationAlgebra k n
  ModuleCat.of (PolynomialRing k n) k

abbrev pointScheme (k : Type u) [Field k] : SchemeOver k :=
  affineScheme (CommAlgCat.of k k)

abbrev origin (k : Type u) [Field k] (n : ℕ) :
    pointScheme k ⟶ affineScheme (polynomialAlgebra k n) :=
  (testSpec k).map (CommAlgCat.ofHom (MvPolynomial.aeval (fun _ : Fin n => (0 : k)))).op

/-- An open polynomial chart with its actual action and homogeneous coordinates. -/
structure PolynomialChart (a : ModObj T.X Y) (n : ℕ) where
  action : ModObj T.X (affineScheme (polynomialAlgebra k n))
  inclusion : affineScheme (polynomialAlgebra k n) ⟶ Y
  openImmersion : IsOpenImmersion inclusion.left
  equivariant : IsEquivariantMap a action inclusion
  fixed : IsEquivariantMap action (pointAction T) (origin k n)
  weight : Fin n → Character T
  homogeneous (i : Fin n) :
    HasFunctionWeight action
      ((Scheme.ΓSpecIso (affineRing (polynomialAlgebra k n))).inv (MvPolynomial.X i))
      (weight i)

abbrev PolynomialChart.point {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) :=
  origin k n ≫ U.inclusion

def RestrictsTo {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n)
    (F : EquivariantCoherent a) (H : EquivariantCoherent U.action) : Prop :=
  ∃ e : Pull U.inclusion F.sheaf ≅ H.sheaf, IsEquivariantPullback U.inclusion F H e

/-- Restriction to the open chart has an actual coherent linearization. -/
def ChartPullback : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
    {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) (F : EquivariantCoherent a),
      ∃ H, RestrictsTo U F H

/-- The character of the actual linearized fiber, counted using its
scheme-theoretic weight spaces of global sections. -/
def IsFiberCharacter {a : ModObj T.X Y} (x : pointScheme k ⟶ Y)
    (F : EquivariantCoherent a) (c : CharacterRing T) : Prop :=
  ∃ (H : EquivariantCoherent (pointAction T)) (e : Pull x F.sheaf ≅ H.sheaf)
    (A : WeightGrading k (Character T) ((affineSections (CommAlgCat.of k k)).obj H.sheaf)),
    IsEquivariantPullback x F H e ∧
    (∀ χ s, s ∈ A.piece χ ↔ HasSectionWeight H.lin s χ) ∧
    ∀ χ, c.coeff χ = (Module.finrank k (A.piece χ) : ℤ)

/-- Ordinary pullback to the origin gives an actual point character. -/
def ChartFiberCharacter : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k}, IsSplitTorus T →
    ∀ {Y : SchemeOver k} {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n)
      (F : EquivariantCoherent U.action),
        ∃ c, IsFiberCharacter (origin k n) F c

/-- An actual bounded, augmented equivariant resolution in module sheaves. -/
structure LocallyFreeResolution {a : ModObj T.X Y} (F : EquivariantCoherent a) where
  complex : ChainComplex Y.left.Modules ℕ
  length : ℕ
  coherent (q : ℕ) : (complex.X q).IsFinitePresentation
  linearization (q : ℕ) : Linearization a (complex.X q)
  locallyFree (q : ℕ) : (complex.X q).IsLocallyFree
  equivariantD (i j : ℕ) : IsLinearizedMap (linearization i) (linearization j) (complex.d i j)
  bounded (q : ℕ) : length ≤ q → IsZero (complex.X q)
  augmentation : complex.X 0 ⟶ F.sheaf
  equivariantAugmentation : IsLinearizedMap (linearization 0) F.lin augmentation
  epi : Epi augmentation
  zero : complex.d 1 0 ≫ augmentation = 0
  exact_zero : (ShortComplex.mk (complex.d 1 0) augmentation zero).Exact
  exact_pos (q : ℕ) : IsZero (complex.homology (q + 1))

abbrev LocallyFreeResolution.term {a : ModObj T.X Y} {F : EquivariantCoherent a}
    (C : LocallyFreeResolution F) (q : ℕ) : EquivariantCoherent a :=
  ⟨C.complex.X q, C.coherent q, C.linearization q⟩

/-- A representative for the class of the equivariant direct image of the
trivial line at a fixed point. -/
def IsPointClass {a : ModObj T.X Y} (x : pointScheme k ⟶ Y)
    (F : EquivariantCoherent a) : Prop :=
  ∃ (L : EquivariantCoherent (pointAction T))
    (_ : tilde (ModuleCat.of k k) ≅ L.sheaf)
    (e : F.sheaf ≅ (Scheme.Modules.pushforward x.left).obj L.sheaf),
    L.lin.iso.hom = 𝟙 _ ∧ IsEquivariantPushforward x L F e

section KoszulWeights

variable {n : ℕ}

abbrev WedgeIndex (k : Type u) [Field k] (n q : ℕ) :=
  Set.powersetCard (Fin (variableList k n).length) q

abbrev variableIndex (i : Fin (variableList k n).length) : Fin n :=
  Fin.cast (variableList_length k n) i

def wedgeWeight (ν : Fin n → Character T) {q : ℕ} (s : WedgeIndex k n q) :
    Character T := ∏ i ∈ s.val, ν (variableIndex i)

variable (M : ModuleCat.{u} (polynomialAlgebra k n))

abbrev KoszulCoefficientComplex := coefficientComplex M (variableList k n)

def wedgeCoordinates (q : ℕ) :
    (KoszulCoefficientComplex M).X q ≃ₗ[PolynomialRing k n] (WedgeIndex k n q →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft (N := M) (listBasis (variableList k n) q)

/-- The character-χ subspace in the specified wedge basis. -/
def weightTerm (ν : Fin n → Character T) (G : WeightGrading k (Character T) M)
    (χ : Character T) (q : ℕ) : Submodule k (WedgeIndex k n q →₀ M) where
  carrier := {v | ∀ s, v s ∈ G.piece ((wedgeWeight ν s)⁻¹ * χ)}
  zero_mem' := fun _ => (G.piece _).zero_mem
  add_mem' hv hw s := (G.piece ((wedgeWeight ν s)⁻¹ * χ)).add_mem (hv s) (hw s)
  smul_mem' c _v hv s := (G.piece _).smul_mem c (hv s)

def coordinateD (i j : ℕ) :
    (WedgeIndex k n i →₀ M) →ₗ[PolynomialRing k n] (WedgeIndex k n j →₀ M) :=
  (wedgeCoordinates M j).toLinearMap.comp
    (((KoszulCoefficientComplex M).d i j).hom.comp (wedgeCoordinates M i).symm.toLinearMap)

def coordinateDOverBase (i j : ℕ) :
    (WedgeIndex k n i →₀ M) →ₗ[k] (WedgeIndex k n j →₀ M) where
  toFun := coordinateD M i j
  map_add' := (coordinateD M i j).map_add
  map_smul' c v := by
    change coordinateD M i j (c • v) = c • coordinateD M i j v
    have h (q : ℕ) (w : WedgeIndex k n q →₀ M) :
        c • w = (algebraMap k (polynomialAlgebra k n) c) • w := by
      ext s
      simp only [Finsupp.smul_apply]
      rfl
    rw [h i, h j, map_smul]

def PreservesKoszulWeight (ν : Fin n → Character T)
    (G : WeightGrading k (Character T) M) (χ : Character T) : Prop :=
  ∀ i j v, v ∈ weightTerm M ν G χ i → coordinateD M i j v ∈ weightTerm M ν G χ j

set_option backward.isDefEq.respectTransparency false in
theorem coordinateD_zero_of_shape (i j : ℕ) (h : ¬ (ComplexShape.down ℕ).Rel i j) :
    coordinateD M i j = 0 := by
  unfold coordinateD
  rw [(KoszulCoefficientComplex M).shape i j h]
  simp

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
theorem coordinateD_squared (i j l : ℕ) (v : WedgeIndex k n i →₀ M) :
    coordinateD M j l (coordinateD M i j v) = 0 := by
  simp only [coordinateD, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hd := congrArg (fun f : (KoszulCoefficientComplex M).X i ⟶
      (KoszulCoefficientComplex M).X l => f ((wedgeCoordinates M i).symm v))
    ((KoszulCoefficientComplex M).d_comp_d i j l)
  change ((KoszulCoefficientComplex M).d j l).hom
    (((KoszulCoefficientComplex M).d i j).hom ((wedgeCoordinates M i).symm v)) = 0 at hd
  rw [hd, map_zero]

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Compute the weight space of Tor as homology of the homogeneous
subcomplex of the Koszul complex with coefficients. -/
def weightComplex (ν : Fin n → Character T)
    (G : WeightGrading k (Character T) M) (χ : Character T)
    (h : PreservesKoszulWeight M ν G χ) : ChainComplex (ModuleCat.{u} k) ℕ where
  X q := ModuleCat.of k (weightTerm M ν G χ q)
  d i j := ModuleCat.ofHom ((coordinateDOverBase M i j).restrict (h i j · ·))
  shape i j hs := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change coordinateD M i j v.val = 0
    rw [coordinateD_zero_of_shape _ _ _ hs, LinearMap.zero_apply]
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change coordinateD M j l (coordinateD M i j v.val) = 0
    exact coordinateD_squared M i j l v.val

/-- The full coefficient complex over the base field, in the wedge basis. -/
def coordinateComplex : ChainComplex (ModuleCat.{u} k) ℕ where
  X q := ModuleCat.of k (WedgeIndex k n q →₀ M)
  d i j := ModuleCat.ofHom (coordinateDOverBase M i j)
  shape i j hs := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change coordinateD M i j v = 0
    rw [coordinateD_zero_of_shape _ _ _ hs, LinearMap.zero_apply]
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact coordinateD_squared M i j l

end KoszulWeights

/-- In each degree the homogeneous Koszul terms give an internal direct sum. -/
def KoszulWeightDecomposition : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ}
    (M : ModuleCat.{u} (polynomialAlgebra k n)) (ν : Fin n → Character T)
    (G : WeightGrading k (Character T) M) (q : ℕ),
      DirectSum.IsInternal (fun χ => weightTerm M ν G χ q)

/-- The homology of the full coefficient complex is the direct sum
of the homologies of its homogeneous subcomplexes. -/
def KoszulHomologyDecomposition : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ}
    (M : ModuleCat.{u} (polynomialAlgebra k n)) (ν : Fin n → Character T)
    (G : WeightGrading k (Character T) M)
    (h : ∀ χ, PreservesKoszulWeight M ν G χ) (q : ℕ),
    ∃ P : Character T → Submodule k ((coordinateComplex M).homology q),
      DirectSum.IsInternal P ∧
      ∀ χ, Nonempty (((weightComplex M ν G χ (h χ)).homology q) ≃ₗ[k] P χ)

/-- The homogeneous summands of the coefficient complex are subcomplexes. -/
def KoszulWeightPreservation : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
    {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n)
    (G : AffineGrading (polynomialAlgebra k n) U.action)
    (M : ModuleCat.{u} (polynomialAlgebra k n)),
    letI := moduleOverBaseField_tower (polynomialAlgebra k n) M
    ∀ (H : ModuleGrading (A := ↥(polynomialAlgebra k n)) G.val M) (χ : Character T),
      PreservesKoszulWeight M U.weight H.toWeightGrading χ

/-- The underlying groups are the ordinary Tor groups with the residue field,
using the projective resolution in the residue-field argument. -/
def KoszulComputesTor : Prop :=
  ∀ {k : Type u} [Field k] (n : ℕ)
    (M : ModuleCat.{u} (polynomialAlgebra k n)) (q : ℕ),
    letI := evaluationAlgebra k n
    Nonempty ((KoszulCoefficientComplex M).homology q ≅
      ((tensorCoefficient M).leftDerived q).obj (ModuleCat.of (PolynomialRing k n) k))

abbrev affineBaseRestriction (k : Type u) [Field k] (n : ℕ) :
    ModuleCat.{u} (PolynomialRing k n) ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k (PolynomialRing k n))

/-- The coefficient groups are finite over the ground field for finite modules,
and vanish above the number of variables for all modules. -/
def KoszulFiniteness : Prop :=
  ∀ {k : Type u} [Field k] (n : ℕ) (M : ModuleCat.{u} (polynomialAlgebra k n)) (q : ℕ),
    (Module.Finite (PolynomialRing k n) M →
      Module.Finite k ((affineBaseRestriction k n).obj ((KoszulCoefficientComplex M).homology q))) ∧
    (n < q → IsZero ((KoszulCoefficientComplex M).homology q))

/-- The alternating character will be formed from these actual homogeneous
Koszul homology spaces. The graded module is identified on all sections. -/
def IsTorCharacter {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n)
    (H : EquivariantCoherent U.action) (ch : ℕ → CharacterRing T) : Prop :=
  let M := (affineSections (polynomialAlgebra k n)).obj H.sheaf
  ∃ (G : WeightGrading k (Character T) M)
    (h : ∀ χ, PreservesKoszulWeight M U.weight G χ),
    (∀ χ s, s ∈ G.piece χ ↔ HasSectionWeight H.lin s χ) ∧
    (∀ q χ, Module.Finite k ((weightComplex M U.weight G χ (h χ)).homology q)) ∧
    ∀ q χ, (ch q).coeff χ = (Module.finrank k
      ((weightComplex M U.weight G χ (h χ)).homology q) : ℤ)

/-- Equivariant coherent coefficients on the chart have finite, uniquely
specified characters in every Tor degree. -/
def TorCharacters : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k}, IsSplitTorus T →
    ∀ {Y : SchemeOver k} {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n)
      (H : EquivariantCoherent U.action),
      ∃! ch : ℕ → CharacterRing T, IsTorCharacter U H ch

def cotangentProduct {n : ℕ} (ν : Fin n → Character T) : CharacterRing T :=
  ∏ i, (1 - eChar (ν i))

/-- For the trivially graded residue line, the Koszul homology ranks count
the wedges of the indicated degree and total weight. -/
def ResidueKoszulWeights : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ} (ν : Fin n → Character T)
    (G : WeightGrading k (Character T) (residueModule k n)),
      (∀ χ, G.piece χ = if χ = 1 then ⊤ else ⊥) →
      ∃ h : ∀ χ, PreservesKoszulWeight (residueModule k n) ν G χ,
        ∀ q χ, Module.finrank k ((weightComplex (residueModule k n) ν G χ (h χ)).homology q) =
          Fintype.card {s : WedgeIndex k n q // wedgeWeight ν s = χ}

/-- The alternating exterior character is the cotangent product. -/
def ExteriorCharacterProduct : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ} (ν : Fin n → Character T),
    (∑ q ∈ Finset.range (n + 1), (-1 : ℤ)^q •
      (∑ s : WedgeIndex k n q, eChar (wedgeWeight ν s))) = cotangentProduct ν

/-- Restriction to the chart followed by the alternating Tor character
descends to a linear map on the ambient equivariant coherent class module. -/
def DerivedClassMap : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} (_hT : IsSplitTorus T)
    {Y : SchemeOver k} {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n),
    ∃ res : GZero a →ₗ[CharacterRing T] CharacterRing T,
      ∀ F : EquivariantCoherent a, (∃ H, RestrictsTo U F H) ∧
        ∀ H, RestrictsTo U F H → ∃ ch, IsTorCharacter U H ch ∧
          res (classOf F) = ∑ q ∈ Finset.range (n + 1), (-1 : ℤ)^q • ch q

/-- The derived fiber is character-linear on the ambient coherent class
module and agrees with both computations on the chart. -/
def DerivedRestriction : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} (_hT : IsSplitTorus T)
    {Y : SchemeOver k} {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n),
    ∃ res : GZero a →ₗ[CharacterRing T] CharacterRing T,
      (∀ F : EquivariantCoherent a,
        (∃ H, RestrictsTo U F H) ∧
        ∀ H, RestrictsTo U F H →
          (∃ ch, IsTorCharacter U H ch ∧
            res (classOf F) = ∑ q ∈ Finset.range (n + 1), (-1 : ℤ)^q • ch q) ∧
          Nonempty (LocallyFreeResolution H) ∧
          ∀ C : LocallyFreeResolution H, ∃! ch : ℕ → CharacterRing T,
            (∀ q, IsFiberCharacter (origin k n) (C.term q) (ch q)) ∧
            res (classOf F) = ∑ q ∈ Finset.range C.length, (-1 : ℤ)^q • ch q) ∧
      (∀ F : EquivariantCoherent a, F.sheaf.IsLocallyFree →
        IsFiberCharacter U.point F (res (classOf F))) ∧
      (∀ F : EquivariantCoherent a, IsPointClass U.point F →
        res (classOf F) = cotangentProduct U.weight) ∧
      (∀ (y : pointScheme k ⟶ Y) (F : EquivariantCoherent a),
        IsPointClass y F → IsEmpty (pullback U.point y).left →
        res (classOf F) = 0)

end

end LinearAlgebraicGroups.Specs.FlagDerivedRestriction
