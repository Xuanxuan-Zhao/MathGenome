import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction

/-! RK-04, maps and coordinates (paper.tex, 2182–2202).
Base change is allocated separately. These specifications use the canonical
complexes of RK-03 and impose no flatness, freeness, or nonzero-ring condition. -/
open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

/-- The component condition specifies the actual exterior-power map. -/
def IsExteriorMap {R : Type u} [CommRing R]
    {E : Type v} [AddCommGroup E] [Module R E]
    {F : Type v} [AddCommGroup F] [Module R F]
    {a : E →ₗ[R] R} {b : F →ₗ[R] R}
    (φ : E →ₗ[R] F) (f : complex a ⟶ complex b) : Prop :=
  ∀ n, (f.f n).hom = exteriorPower.map n φ

def differentialNaturality : Prop := ∀ {R : Type u} [CommRing R]
    {E F : Type v} [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    (a : E →ₗ[R] R) (b : F →ₗ[R] R) (φ : E →ₗ[R] F),
  b.comp φ = a → ∀ n,
    (differential b n).comp (exteriorPower.map (n+1) φ) =
      (exteriorPower.map n φ).comp (differential a n)

def chainMapExists : Prop := ∀ {R : Type u} [CommRing R]
    {E : Type v} [AddCommGroup E] [Module R E]
    {F : Type v} [AddCommGroup F] [Module R F]
    (a : E →ₗ[R] R) (b : F →ₗ[R] R) (φ : E →ₗ[R] F),
  b.comp φ = a → ∃ f : complex a ⟶ complex b, IsExteriorMap φ f

def chainMapIdentity : Prop := ∀ {R : Type u} [CommRing R]
    {E : Type v} [AddCommGroup E] [Module R E] (a : E →ₗ[R] R)
    (f : complex a ⟶ complex a),
  IsExteriorMap LinearMap.id f → f = 𝟙 _

def chainMapComposition : Prop := ∀ {R : Type u} [CommRing R]
    {E F G : Type v} [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    {a : E →ₗ[R] R} {b : F →ₗ[R] R} {c : G →ₗ[R] R}
    (φ : E →ₗ[R] F) (ψ : F →ₗ[R] G)
    (f : complex a ⟶ complex b) (g : complex b ⟶ complex c)
    (k : complex a ⟶ complex c),
  IsExteriorMap φ f → IsExteriorMap ψ g → IsExteriorMap (ψ.comp φ) k → f ≫ g = k

/-- All invertible linear coordinate changes, in particular matrices in GL_r(R). -/
def coordinateIso : Prop := ∀ {R : Type u} [CommRing R] (x y : List R)
    (e : (Fin x.length → R) ≃ₗ[R] (Fin y.length → R)),
  (listForm y).comp e.toLinearMap = listForm x →
    ∃ i : listComplex x ≅ listComplex y, IsExteriorMap e.toLinearMap i.hom

def coefficientCoordinateIso : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x y : List R)
    (e : (Fin x.length → R) ≃ₗ[R] (Fin y.length → R)),
  (listForm y).comp e.toLinearMap = listForm x →
    ∃ i : coefficientComplex M x ≅ coefficientComplex M y,
      ∀ n, (i.hom.f n).hom = TensorProduct.map (exteriorPower.map n e.toLinearMap)
        (LinearMap.id : M →ₗ[R] M)

/-- An arbitrary permutation of positions, allowing repeated list entries. -/
def permutationIso : Prop := ∀ {R : Type u} [CommRing R] (x y : List R)
    (p : Fin x.length ≃ Fin y.length),
  (∀ j, y.get (p j) = x.get j) → Nonempty (listComplex x ≅ listComplex y)

def coefficientPermutationIso : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x y : List R)
    (p : Fin x.length ≃ Fin y.length),
  (∀ j, y.get (p j) = x.get j) →
    Nonempty (coefficientComplex M x ≅ coefficientComplex M y)

/-- Entrywise form of an invertible linear change of a generating list.
Here e sends the standard basis vectors to the columns of the invertible matrix. -/
def linearCoordinateChangeIso : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x y : List R)
    (e : (Fin x.length → R) ≃ₗ[R] (Fin y.length → R)),
  (∀ i, x.get i = ∑ j, (e (Pi.basisFun R (Fin x.length) i)) j * y.get j) →
    Nonempty (listComplex x ≅ listComplex y) ∧
      Nonempty (coefficientComplex M x ≅ coefficientComplex M y)

end Specs.AdvCommAlg.Koszul
