import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.PinnedPairDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeWeylScheme
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.NormalizerComparison
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

open AlgebraicGeometry CategoryTheory
open scoped WithZero

namespace LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer

open ValuativeRel

noncomputable section

universe u

/-- The multiplicative integer valuation whose uniformizers have value `exp (-1)`. -/
def normalizedValuation (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Valuation F ℤᵐ⁰ :=
  (valuation F).map
    ⟨(IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toMonoidWithZeroHom,
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).strictMono.monotone⟩

section Torus
open scoped Classical


open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (IntegralAlgebra Integers IntegralMarking IntegralPoints TorusValues
  cocharacter integerAlgebra torusPoint)

variable (D : BasedRootDatum.{u}) {ι : Type u} [Fintype ι]

/-- The character basis dual to a specified basis of the actual cocharacter
lattice of the marked integral torus. -/
def characterBasis (b : Module.Basis ι ℤ D.Y) : Module.Basis ι ℤ D.X :=
  b.dualBasis.map D.datum.toPerfPair.symm

/-- Torus coordinates with respect to an integral cocharacter basis. The
inverse amounts to multiplying the corresponding cocharacters. -/
def TorusBasisCoordinates : Prop :=
  ∀ (D : BasedRootDatum.{u}) {ι : Type u} [Fintype ι] (b : Module.Basis ι ℤ D.Y)
    (R : IntegralAlgebra.{u}),
    ∃ e : TorusValues D R ≃* (ι → Rˣ),
      (∀ t i, e t i = t (Multiplicative.ofAdd (characterBasis D b i))) ∧
      ∀ (u : ι → Rˣ) (x : D.X),
        e.symm u (Multiplicative.ofAdd x) = ∏ i, u i ^ (D.datum.toLinearMap x (b i))

/-- The actual simple coroot basis in the simply connected case. -/
def simpleCorootBasis (h : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    Module.Basis D.base.support ℤ D.Y :=
  Module.Basis.mk D.base.linearIndepOn_coroot <| by
    change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.coroot ∘ ((↑) : D.base.support → D.I)))
    rw [Set.range_comp, Subtype.range_coe, D.base.span_int_coroot_support, h]

/-- The actual fundamental coweight basis in the adjoint case. -/
def fundamentalCoweightBasis (h : Submodule.span ℤ (Set.range D.datum.root) = ⊤) :
    Module.Basis D.base.support ℤ D.Y :=
  let b : Module.Basis D.base.support ℤ D.X :=
    Module.Basis.mk D.base.linearIndepOn_root <| by
      change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.root ∘ ((↑) : D.base.support → D.I)))
      rw [Set.range_comp, Subtype.range_coe, D.base.span_int_root_support, h]
  b.dualBasis.map D.datum.toLinearMap.flip.toPerfPair.symm

/-- The bases used to evaluate the simply connected and adjoint tori. -/
def ExceptionalCocharacterBases : Prop :=
  ∀ D : BasedRootDatum.{u},
    (∀ (h : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) (i : D.base.support),
      simpleCorootBasis D h i = D.datum.coroot i) ∧
    ∀ (h : Submodule.span ℤ (Set.range D.datum.root) = ⊤) (i j : D.base.support),
      D.datum.toLinearMap (D.datum.root j) (fundamentalCoweightBasis D h i) =
        if j = i then 1 else 0

attribute [local instance] integerAlgebra

/-- The normalized apartment translation of a marked split torus surjects
onto its cocharacter lattice. Its kernel is the unit torus. -/
def SplitTorusTranslation : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (D : BasedRootDatum.{u})
    {ι : Type u} [Fintype ι] (b : Module.Basis ι ℤ D.Y),
    ∃ ν : TorusValues D (CommAlgCat.of Integers.{u} K) →* Multiplicative D.Y,
      Function.Surjective ν ∧
      (∀ t x, D.datum.toLinearMap x (ν t).toAdd =
        WithZero.log (normalizedValuation K (t (Multiplicative.ofAdd x) : K))) ∧
      ∀ t, ν t = 1 ↔
        ∀ i, normalizedValuation K (t (Multiplicative.ofAdd (characterBasis D b i)) : K) = 1

/-- Cocharacter scalings and normalizer conjugation on the marked split torus
intertwine the valuation translation with the indicated lattice actions. -/
def SplitTranslationAction : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (D : BasedRootDatum.{u}),
    let R := CommAlgCat.of Integers.{u} K
    ∀ ν : TorusValues D R →* Multiplicative D.Y,
      (∀ t x, D.datum.toLinearMap x (ν t).toAdd =
        WithZero.log (normalizedValuation K (t (Multiplicative.ofAdd x) : K))) →
      (∀ (y : D.Y) (s : Kˣ), (ν (cocharacter D y R s)).toAdd =
        WithZero.log (normalizedValuation K (s : K)) • y) ∧
      ∀ (w : RootPairing.Aut D.datum) (t : TorusValues D R),
        (ν (t.comp w.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative)).toAdd =
          w.coweightEquiv.symm (ν t).toAdd

/-- Extended valuation coordinates for fixed and exchanged torus factors. -/
def FoldedTorusFactorValuations : Prop :=
  ∀ (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [ValuativeRel F] [ValuativeRel L] [TopologicalSpace F] [TopologicalSpace L]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F L],
    (∀ x : F, normalizedValuation L (algebraMap F L x) = (normalizedValuation F x) ^ 2) →
    ∀ (σ : Gal(L/F)), (∀ x, normalizedValuation L (σ x) = normalizedValuation L x) →
      Set.range (fun u : Fˣ ↦
        ((WithZero.log (normalizedValuation L (algebraMap F L (u : F))) : ℤ) : ℚ) / 2) =
          Set.range (fun n : ℤ ↦ (n : ℚ)) ∧
      Set.range (fun u : Lˣ ↦
        (((WithZero.log (normalizedValuation L (u : L)) : ℤ) : ℚ) / 2,
         ((WithZero.log (normalizedValuation L (σ (u : L))) : ℤ) : ℚ) / 2)) =
          Set.range (fun n : ℤ ↦ ((n : ℚ) / 2, (n : ℚ) / 2))

end Torus

section Apartment

open scoped SemidirectProduct

variable {N W Λ V : Type*} [Group N] [Group W] [Group Λ]
  [AddCommGroup V] [Module ℚ V]

/-- Conjugate a torus point by a normalizer element. -/
def conjugateTorus (q : N →* W) (n : N) (t : q.ker) : q.ker :=
  ⟨n * t.val * n⁻¹, by have ht : q t.val = 1 := t.property; simp [ht]⟩

/-- The affine action of a translation lattice and a group of linear automorphisms. -/
def affineTransformation (ρ : W →* MulAut Λ) (j : Λ →* Multiplicative V)
    (w : W →* (V ≃ₗ[ℚ] V))
    (h : ∀ a t, (j (ρ a t)).toAdd = w a (j t).toAdd) :
    Λ ⋊[ρ] W →* (V ≃ᵃ[ℚ] V) where
  toFun g := AffineEquiv.ofLinearEquiv (w g.right) 0 (j g.left).toAdd
  map_one' := by
    ext x
    simp [AffineEquiv.ofLinearEquiv]
  map_mul' a b := by
    ext x
    change (w (a.right * b.right)) (x - 0) + (j (a.left * ρ a.right b.left)).toAdd =
      w a.right (w b.right (x - 0) + (j b.left).toAdd - 0) + (j a.left).toAdd
    simp [h, add_left_comm, add_comm]

/-- A normalizer with integral representatives acts on the apartment. Its integral
torus is the kernel. Representatives with a given label determine the same
translation, and a rational scaling at a point and its image removes the
translation part. -/
def NormalizerApartment : Prop :=
  ∀ {N W Λ V : Type u} [Group N] [Group W] [Group Λ] [AddCommGroup V] [Module ℚ V]
    (q : N →* W) (J : Subgroup N) (ν : q.ker →* Λ)
    (ρ : W →* MulAut Λ) (j : Λ →* Multiplicative V) (w : W →* (V ≃ₗ[ℚ] V))
    (h : ∀ a t, (j (ρ a t)).toAdd = w a (j t).toAdd),
    Function.Injective j → Function.Injective w →
    Function.Surjective ν → Function.Surjective (q.comp J.subtype) →
    (∀ t : q.ker, ν t = 1 ↔ t.val ∈ J) →
    (∀ n t, ν (conjugateTorus q n t) = ρ (q n) (ν t)) →
    ∃ (p : N →* Λ ⋊[ρ] W),
      Function.Surjective p ∧
      p.ker = q.ker ⊓ J ∧
      Function.Injective (affineTransformation ρ j w h) ∧
      (∀ n, (p n).right = q n) ∧
      (∀ t : q.ker, (p t.val).left = ν t) ∧
      (∀ n ∈ J, (p n).left = 1) ∧
      (∀ n m, m ∈ J → ∀ e : q n = q m,
        (p n).left = ν ⟨n * m⁻¹, by simp [e]⟩) ∧
      ∀ (n : N) (x : V) (c d : q.ker),
        let a := affineTransformation ρ j w h
        (j (ν c)).toAdd = -x →
        (j (ν d)).toAdd = -(a (p n) x) →
        d.val * n * c.val⁻¹ ∈ J

end Apartment

section PermutationBasis

open scoped Classical
open Pinning (BasedRootDatum BasedIso)

/-- The diagram action restricted to the simple labels. -/
def simplePermutation (D : BasedRootDatum.{u}) (e : BasedIso D D) :
    Equiv.Perm D.base.support :=
  (e.val.indexEquiv.image (D.base.support : Set D.I)).trans (Set.equivOfEq e.property)

/-- The action on the simple labels is a left action. -/
def simplePermutationHom (D : BasedRootDatum.{u}) : Aut D →* Equiv.Perm D.base.support where
  toFun a := simplePermutation D a.asIso.hom
  map_one' := by ext i; rfl
  map_mul' _ _ := by ext i; rfl

/-- The two integral cocharacter bases and their dual character bases have
the same permutation action as the simple roots. -/
def BasedPermutation : Prop :=
  ∀ (D : BasedRootDatum.{u}) (e : BasedIso D D) (b : Module.Basis D.base.support ℤ D.Y),
    ((∃ h, b = simpleCorootBasis D h) ∨ (∃ h, b = fundamentalCoweightBasis D h)) →
    ∀ i,
      e.val.coweightEquiv.symm (b i) = b (simplePermutation D e i) ∧
      e.val.weightEquiv (characterBasis D b i) = characterBasis D b (simplePermutation D e i)

/-- A regular integral cocharacter in the positive chamber, fixed by any
automorphism of the based datum. -/
def InvariantRegularCocharacter : Prop :=
  ∀ (D : BasedRootDatum.{u}), ∃ y : D.Y,
    (∀ e : BasedIso D D, e.val.coweightEquiv.symm y = y) ∧
    (∀ i, D.datum.toLinearMap (D.datum.root i) y = 2 * D.base.height i) ∧
    ∀ i, D.datum.toLinearMap (D.datum.root i) y ≠ 0

/-- The reflection word for the simple orbit of a diagram involution. -/
def orbitWeylReflection (D : BasedRootDatum.{u}) (e : BasedIso D D) (i : D.base.support) :
    D.datum.weylGroup :=
  if simplePermutation D e i = i then RootPairing.weylGroup.ofIdx D.datum i.val
  else RootPairing.weylGroup.ofIdx D.datum i.val *
    RootPairing.weylGroup.ofIdx D.datum (simplePermutation D e i).val

/-- For orthogonal pairs, the fixed absolute Weyl labels are exactly those
generated by the words for the simple orbits. -/
def FixedWeylGeneration : Prop :=
  ∀ (D : BasedRootDatum.{u}) (e : BasedIso D D), Function.Involutive e.val.indexEquiv →
    (∀ i : D.base.support, simplePermutation D e i ≠ i →
      D.datum.pairing (simplePermutation D e i).val i.val = 0) →
    (∀ w : D.datum.weylGroup,
      w ∈ Subgroup.closure (Set.range (orbitWeylReflection D e)) ↔ Commute e.val w.val) ∧
    ∀ w : D.datum.weylGroup,
      (∀ y : D.Y, e.val.coweightEquiv.symm y = y → w.val.coweightEquiv.symm y = y) → w = 1

/-- The absolute Weyl labels are transported along the isomorphism of marked
data, compatibly with simple reflections and with the character action. -/
def WeylGroupTransport : Prop :=
  ∀ (D E : BasedRootDatum.{u}) (e : BasedIso D E),
    ∃ j : D.datum.weylGroup ≃* E.datum.weylGroup,
      (∀ i, j (RootPairing.weylGroup.ofIdx D.datum i) =
        RootPairing.weylGroup.ofIdx E.datum (e.val.indexEquiv i)) ∧
      ∀ w x, (j w).val.weightEquiv (e.val.weightEquiv x) = e.val.weightEquiv (w.val.weightEquiv x)

end PermutationBasis

section FoldedLattice

/-- The invariant integral cocharacter lattice in permutation coordinates. -/
def invariantLattice {ι : Type*} (τ : Equiv.Perm ι) : Submodule ℤ (ι → ℤ) where
  carrier := {y | ∀ i, y (τ i) = y i}
  zero_mem' := fun _ => rfl
  add_mem' {x} {y} hx hy i := by
    change x (τ i) + y (τ i) = x i + y i
    rw [hx i, hy i]
  smul_mem' c y hy i := by change c • y (τ i) = c • y i; rw [hy i]

/-- Averaging the two translates of an integral cocharacter gives its rational
projection. A singleton retains its coefficient and a pair contributes half
the sum in each of the two coordinate directions. -/
def orbitProjection {ι : Type*} (τ : Equiv.Perm ι) (y : ι → ℤ) : ι → ℚ :=
  fun i => ((y i : ℚ) + (y (τ i) : ℚ)) / 2

/-- The fixed lattice is saturated in the full cocharacter lattice. Its rational
projection admits the same permutation description. -/
def SaturatedInvariantLattice : Prop :=
  ∀ {ι : Type u} (τ : Equiv.Perm ι), Function.Involutive τ →
    (∀ (n : ℤ) (y : ι → ℤ), n ≠ 0 → n • y ∈ invariantLattice τ → y ∈ invariantLattice τ) ∧
    (∀ y i, orbitProjection τ y (τ i) = orbitProjection τ y i) ∧
    ∀ y ∈ invariantLattice τ, orbitProjection τ y = fun i => (y i : ℚ)

/-- With the canonical valuations on a ramified quadratic extension, the
image of the fixed torus coordinates is exactly the projected lattice. The
valuation convention is the one in which a base uniformizer has depth one. -/
def FoldedTranslationLattice : Prop :=
  ∀ {F L : Type u} [Field F] [Field L] [Algebra F L]
    [ValuativeRel F] [ValuativeRel L] [TopologicalSpace F] [TopologicalSpace L]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField L]
    (σ : Gal(L/F)), Function.Involutive σ →
    (∀ x : F, normalizedValuation L (algebraMap F L x) = (normalizedValuation F x) ^ 2) →
    (∀ x : L, normalizedValuation L (σ x) = normalizedValuation L x) →
    (∀ u : Lˣ, σ (u : L) = (u : L) → ∃ a : Fˣ, algebraMap F L (a : F) = (u : L)) →
    ∀ {ι : Type u} [Fintype ι] (τ : Equiv.Perm ι), Function.Involutive τ →
      Set.range (fun u : {u : ι → Lˣ // ∀ i, (u (τ i) : L) = σ (u i : L)} =>
        fun i => ((WithZero.log (normalizedValuation L (u.val i : L)) : ℤ) : ℚ) / 2) =
        Set.range (orbitProjection τ)

end FoldedLattice

section DescendedTorus

open AdjointBorelCohomology (PinnedTwist PermutedCharacterBasis IsOrbitWeilProduct
  extendedCharacterValue)
open AdjointCocharacters (coordinateHopf)
open CharacterDescent (Character)
open Pinning (AttachedDatum PinnedGroup transportCharacter)
open RootGroups (AdditiveLine)
open RationalRealization (Realization)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open Unipotent (closedSubgroupAlgebraicGroup)
open scoped TensorProduct

/-- The permutation basis of the pinned split torus descends to the specified
torus in the pinned Borel pair. Its coordinates are the Weil restriction
factors for the corresponding stabilizer fields. -/
def PinnedPermutationTorus : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := P) K D l B T) {ι : Type u} [Finite ι]
    (b : Module.Basis ι ℤ (Additive (Character P.pair.T.group)))
    (r : Gal(K/k) →* Equiv.Perm ι),
    (∀ σ i, transportCharacter (l (d.outer σ)).asIso.hom.torus (b i).toMul =
      (b (r σ i)).toMul) →
    let H := closedSubgroupAlgebraicGroup T
    ∃ c : PermutedCharacterBasis K ι H r,
      (∀ i, (c.basis i).toMul.val =
        d.torusIso.hom.hom (extendedCharacterValue K
          (closedSubgroupAlgebraicGroup P.pair.T) (b i).toMul)) ∧
      CharacterDescent.IsDiagonalizable (extendedHopf K (coordinateHopf H)) ∧
      IsOrbitWeilProduct K r H

/-- Read a pinned based automorphism in the original marking. -/
def markedDiagramEquiv {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}} {A : AdditiveLine k}
    (P : Realization D A) : Aut P.attached.toBased ≃* Aut D :=
  let i := (Groupoid.isoEquivHom D P.attached.toBased).symm P.datumIso
  Aut.autMulEquivOfIso i.symm

/-- In the simply connected and adjoint cases the permuted characters are
the duals of the indicated integral bases in the chosen model. -/
def MarkedPinnedTorus : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (D : Pinning.BasedRootDatum.{u}) {A : AdditiveLine k} (P : Realization D A)
    {l : Aut P.attached.toBased ≃* Aut P.pinned} {Q : AdjointQuotient P.pinned.pair.G}
    (_ : SplitSequence P.pinned P.attached l Q)
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := P.pinned) K P.attached l B T)
    (b : Module.Basis D.base.support ℤ D.Y),
    ((∃ h, b = simpleCorootBasis D h) ∨ (∃ h, b = fundamentalCoweightBasis D h)) →
    let r := (simplePermutationHom D).comp ((markedDiagramEquiv P).toMonoidHom.comp d.outer)
    let H := closedSubgroupAlgebraicGroup T
    ∃ c : PermutedCharacterBasis K D.base.support H r,
      (∀ i, (c.basis i).toMul.val =
        d.torusIso.hom.hom (extendedCharacterValue K (closedSubgroupAlgebraicGroup P.pinned.pair.T)
          (Additive.toMul (P.datumIso.val.weightEquiv (characterBasis D b i))))) ∧
      CharacterDescent.IsDiagonalizable (extendedHopf K (coordinateHopf H)) ∧
      IsOrbitWeilProduct K r H

/-- The pinned lift in F06 acts on the simple roots and either special torus
basis by the diagram permutation in the original marking. -/
def MarkedPinnedDiagramAction : Prop :=
  ∀ {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}} {A : AdditiveLine k} (P : Realization D A)
    {l : Aut P.attached.toBased ≃* Aut P.pinned} {Q : AdjointQuotient P.pinned.pair.G},
    SplitSequence P.pinned P.attached l Q → ∀ a : Aut P.attached.toBased,
    let e := ((markedDiagramEquiv P) a).asIso.hom
    let s := (l a).asIso.hom
    (∀ i : D.base.support, transportCharacter s.torus (P.simpleRoot i).val.val =
      (P.simpleRoot (simplePermutation D e i)).val.val) ∧
    (∀ b : Module.Basis D.base.support ℤ D.Y,
      ((∃ h, b = simpleCorootBasis D h) ∨ (∃ h, b = fundamentalCoweightBasis D h)) →
      ∀ i : D.base.support, transportCharacter s.torus
        (Additive.toMul (P.datumIso.val.weightEquiv (characterBasis D b i))) =
          Additive.toMul (P.datumIso.val.weightEquiv (characterBasis D b (simplePermutation D e i)))) ∧
    (a * a = 1 → Function.Involutive e.val.indexEquiv)

/-- Unit tuples on the splitting algebra satisfying the coefficient and
index equations of descent. -/
def equivariantUnits {k K : Type u} [Field k] [Field K] [Algebra k K]
    {ι : Type u} (r : Gal(K/k) →* Equiv.Perm ι) (R : TestAlgebra k) :
    Subgroup (ι → (K ⊗[k] R)ˣ) where
  carrier := {v | ∀ (σ : Gal(K/k)) i, v (r σ i) =
    Units.map (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k R)).toMonoidHom (v i)}
  one_mem' σ i := (map_one _).symm
  mul_mem' ha hb σ i := by
    change _ * _ = Units.map _ (_ * _)
    rw [ha σ i, hb σ i, map_mul]
  inv_mem' ha σ i := by
    change _⁻¹ = Units.map _ _⁻¹
    rw [ha σ i, map_inv]

/-- Evaluation on the transported group-like basis identifies points of the
specified torus with the fixed units in its split factors, on every test algebra. -/
def PermutationTorusPoints : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {ι : Type u} {r : Gal(K/k) →* Equiv.Perm ι} {H : AffineAlgebraicGroup k}
    (c : PermutedCharacterBasis K ι H r),
    CharacterDescent.IsDiagonalizable (extendedHopf K (coordinateHopf H)) →
    ∀ R : TestAlgebra k,
      ∃ e : (coordinateHopf H →ₐ[k] R) ≃ equivariantUnits r R,
        ∀ f i, ((e f).val i : K ⊗[k] R) =
          Algebra.TensorProduct.map (AlgHom.id K K) f (c.basis i).toMul.val

/-- On field-valued points the simultaneous index and coefficient equations
are equations in the units of the splitting field itself. -/
def RationalPermutationTorusPoints : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {ι : Type u} {r : Gal(K/k) →* Equiv.Perm ι} {H : AffineAlgebraicGroup k}
    (c : PermutedCharacterBasis K ι H r),
    CharacterDescent.IsDiagonalizable (extendedHopf K (coordinateHopf H)) →
    ∃ e : (coordinateHopf H →ₐ[k] k) ≃
      {v : ι → Kˣ // ∀ (σ : Gal(K/k)) i, (v (r σ i) : K) = σ (v i : K)},
      ∀ f i, ((e f).val i : K) =
        Algebra.TensorProduct.rid k K K
          (Algebra.TensorProduct.map (AlgHom.id K K) f (c.basis i).toMul.val)

/-- The simple indices modulo the actual diagram action. -/
abbrev OrbitIndices {k K : Type u} [Field k] [Field K] [Algebra k K]
    {ι : Type u} (r : Gal(K/k) →* Equiv.Perm ι) :=
  letI := MulAction.compHom ι r
  MulAction.orbitRel.Quotient Gal(K/k) ι

def orbitIndex {k K : Type u} [Field k] [Field K] [Algebra k K]
    {ι : Type u} (r : Gal(K/k) →* Equiv.Perm ι) (i : ι) : OrbitIndices r :=
  Quotient.mk'' i

/-- A split subgroup of the permutation torus, given by the map from the
actual coordinate algebra to the group algebra on the orbit characters. -/
def PermutationSplitSubtorus : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {ι : Type u} [Finite ι] {r : Gal(K/k) →* Equiv.Perm ι} {H : AffineAlgebraicGroup k}
    (c : PermutedCharacterBasis K ι H r),
    CharacterDescent.IsDiagonalizable (extendedHopf K (coordinateHopf H)) →
    let M := Multiplicative (OrbitIndices r →₀ ℤ)
    let A := DiagonalizableGroups.groupAlgebra k M
    ∃ q : coordinateHopf H ⟶ A,
      Function.Surjective q.hom ∧
      IsClosedImmersion (specGroupMap q ≫ (AdjointCocharacters.coordinateHopfIso H).hom).hom.hom.left ∧
      GeometricRadicals.IsSplitTorus (specGroup A) ∧
      ∀ i, (extendedHopfMap K q).hom (c.basis i).toMul.val =
        (1 : K) ⊗ₜ[k] MonoidAlgebra.of k M (Multiplicative.ofAdd (Finsupp.single (orbitIndex r i) 1))

/-- The split orbit torus contains every split subtorus of the specified
permutation torus. This statement gives the factorization on coordinates. -/
def PermutationSplitFactorization : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {ι : Type u} {r : Gal(K/k) →* Equiv.Perm ι} {H : AffineAlgebraicGroup k}
    (c : PermutedCharacterBasis K ι H r),
    CharacterDescent.IsDiagonalizable (extendedHopf K (coordinateHopf H)) →
    let M := Multiplicative (OrbitIndices r →₀ ℤ)
    let A := DiagonalizableGroups.groupAlgebra k M
    ∀ q : coordinateHopf H ⟶ A, Function.Surjective q.hom →
      (∀ i, (extendedHopfMap K q).hom (c.basis i).toMul.val =
        (1 : K) ⊗ₜ[k] MonoidAlgebra.of k M (Multiplicative.ofAdd (Finsupp.single (orbitIndex r i) 1))) →
      ∀ (B : HopfAlgebraCategory k), CharacterDescent.IsDiagonalizable B →
        ∀ f : coordinateHopf H ⟶ B, ∃! g : A ⟶ B, q ≫ g = f

/-- The image of the integral cocharacters of the split orbit torus in the
split character coordinates is precisely the invariant cocharacter lattice. -/
def OrbitTorusCocharacters : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {ι : Type u} {r : Gal(K/k) →* Equiv.Perm ι} {H : AffineAlgebraicGroup k}
    (c : PermutedCharacterBasis K ι H r),
    let M := Multiplicative (OrbitIndices r →₀ ℤ)
    let A := DiagonalizableGroups.groupAlgebra k M
    ∀ q : coordinateHopf H ⟶ A,
      (∀ i, (extendedHopfMap K q).hom (c.basis i).toMul.val =
        (1 : K) ⊗ₜ[k] MonoidAlgebra.of k M (Multiplicative.ofAdd (Finsupp.single (orbitIndex r i) 1))) →
      ∀ y : ι → ℤ, (∀ (σ : Gal(K/k)) i, y (r σ i) = y i) ↔
        ∃ z : A ⟶ DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters.{u},
          ∀ i, (extendedHopfMap K (q ≫ z)).hom (c.basis i).toMul.val =
            (1 : K) ⊗ₜ[k] MonoidAlgebra.of k _ (DiagonalizableGroups.integerGenerator ^ y i)

/-- The orbit torus is a closed subgroup of the original group, contained in
the pinned descended torus. It contains every split subtorus of that torus. -/
def LargestSplitPermutationSubtorus : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {ι : Type u} [Finite ι] {r : Gal(K/k) →* Equiv.Perm ι} {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val),
    let H := closedSubgroupAlgebraicGroup T
    ∀ (c : PermutedCharacterBasis K ι H r),
      CharacterDescent.IsDiagonalizable (extendedHopf K (coordinateHopf H)) →
      let M := Multiplicative (OrbitIndices r →₀ ℤ)
      let A := DiagonalizableGroups.groupAlgebra k M
      ∃ (q : coordinateHopf H ⟶ A)
        (h : IsClosedImmersion (specGroupMap q ≫ (AdjointCocharacters.coordinateHopfIso H).hom).hom.hom.left),
        let S := GeometricBorelConjugacy.subgroupOfSubgroup T
          ⟨specGroup A, specGroupMap q ≫ (AdjointCocharacters.coordinateHopfIso H).hom, h⟩
        GeometricRadicals.IsSplitTorus S.group ∧ SchemeDerivedGroup.IsSubgroupOf S T ∧
        (∀ (U : ClosedSubgroup G.val), GeometricRadicals.IsSplitTorus U.group →
          SchemeDerivedGroup.IsSubgroupOf U T → SchemeDerivedGroup.IsSubgroupOf U S) ∧
        ∀ i, (extendedHopfMap K q).hom (c.basis i).toMul.val =
          (1 : K) ⊗ₜ[k] MonoidAlgebra.of k M (Multiplicative.ofAdd (Finsupp.single (orbitIndex r i) 1))

end DescendedTorus

section PinnedPoints

open AdjointBorelCohomology (PinnedTwist)
open AdjointCocharacters (coordinateHopf coordinateHopfMap)
open Pinning (AttachedDatum PinnedGroup)
open RootGroups (AdditiveLine)
open AutomorphismSequence (forgetPinning)
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open scoped TensorProduct

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
variable {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}

/-- The coefficient action on the original split group after the pinned twist. -/
def pinnedCoordinateAction (d : PinnedTwist K D l B T) (σ : Gal(K/k))
    (x : extendedHopf K (coordinateHopf P.pair.G)) : extendedHopf K (coordinateHopf P.pair.G) :=
  let g := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso.inv
  (extendedHopfMap K (coordinateHopfMap (G := P.pair.G) (H := P.pair.G) g)).hom
    ((SemilinearAction.scalarExtension (K := K) (coordinateHopf P.pair.G)).act σ x)

/-- The coefficient extension of an actual point, evaluated in the split pinning. -/
def pinnedCoordinatePoint (d : PinnedTwist K D l B T) (R : TestAlgebra k)
    (f : coordinateHopf G →ₐ[k] R) :
    extendedHopf K (coordinateHopf P.pair.G) →ₐ[K] K ⊗[k] R :=
  (Algebra.TensorProduct.map (AlgHom.id K K) f).comp d.groupIso.hom.hom.toAlgHom

/-- The points of the specified pinned descent are the coefficient-equivariant
points of the split form. The comparison applies to every test algebra. -/
def PinnedCoordinateFixedPoints : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K D l B T) (R : TestAlgebra k),
    Function.Injective (pinnedCoordinatePoint d R) ∧
    ∀ f : extendedHopf K (coordinateHopf P.pair.G) →ₐ[K] K ⊗[k] R,
      f ∈ Set.range (pinnedCoordinatePoint d R) ↔
        ∀ σ x, f (pinnedCoordinateAction d σ x) =
          (SemilinearAction.scalarExtension (K := K) R).act σ (f x)

end PinnedPoints

section ValuationComparisons

open scoped Classical
open IntegralSemisimpleModel (Integers IntegralMarking IntegralPoints TorusValues integralPointFunctor
  integerAlgebra torusPoint)
open Pinning (BasedRootDatum)
attribute [local instance] integerAlgebra

/-- The unit kernel in basis coordinates is the image of the torus over the
actual valuation ring. -/
def IntegralTorusCoordinates : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (D : BasedRootDatum.{u})
    {ι : Type u} [Fintype ι] (b : Module.Basis ι ℤ D.Y)
    (t : TorusValues D (CommAlgCat.of Integers.{u} K)),
    let O := (valuation K).valuationSubring
    let R := CommAlgCat.of Integers.{u} O
    (∀ i, normalizedValuation K (t (Multiplicative.ofAdd (characterBasis D b i)) : K) = 1) ↔
      ∃ s : TorusValues D R, (Units.map O.subtype.toMonoidHom).comp s = t

/-- A field-valued point of the marked torus is integral in the actual model
exactly when its character basis values are units of the valuation ring. -/
def MarkedIntegralTorusKernel : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (D : BasedRootDatum.{u}) (M : IntegralMarking D)
    {ι : Type u} [Fintype ι] (b : Module.Basis ι ℤ D.Y),
    let O := (valuation K).valuationSubring
    let R := CommAlgCat.of Integers.{u} O
    let S := CommAlgCat.of Integers.{u} K
    let f : R ⟶ S := CommAlgCat.ofHom
      ({ O.subtype with commutes' := fun a ↦ map_intCast O.subtype a.down } : O →ₐ[Integers.{u}] K)
    ∀ t : TorusValues D S,
      (∀ i, normalizedValuation K (t (Multiplicative.ofAdd (characterBasis D b i)) : K) = 1) ↔
        ∃ p : IntegralPoints M.group R, (integralPointFunctor M.group).map f p =
          torusPoint D S t ≫ M.torus.hom.hom

/-- The folded translation pairs with each absolute character as the negative
of its additive valuation in the convention normalized on the base field. -/
def FoldedCharacterTranslation : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (D : BasedRootDatum.{u})
    {ι : Type u} [Fintype ι] (b : Module.Basis ι ℤ D.Y)
    (t : TorusValues D (CommAlgCat.of Integers.{u} K)) (x : D.X),
    (∑ i, ((WithZero.log (normalizedValuation K
          (t (Multiplicative.ofAdd (characterBasis D b i)) : K)) : ℤ) : ℚ) / 2 *
          (D.datum.toLinearMap x (b i) : ℚ)) =
      ((WithZero.log (normalizedValuation K (t (Multiplicative.ofAdd x) : K)) : ℤ) : ℚ) / 2

end ValuationComparisons

section MarkedFibre

open Pinning (BasedRootDatum)
open RationalRealization (Realization)
open AdjointRepresentation (GroupPoints)
open IntegralSemisimpleModel (Integers Model TorusValues fibre forgetFibrePoint integerAlgebra
  splitTorus torusPoint)
open CharacterPairing (characterValue)

attribute [local instance] integerAlgebra

/-- The torus points on the chosen pinned field fibre, with their evaluations on
the full marked lattice and their inclusion in the same integral model. -/
def MarkedFibreTorusCoordinates : Prop :=
  ∀ {k : Type u} [Field k] (D : BasedRootDatum.{u}) (M : Model D)
    {A : RootGroups.AdditiveLine k} (P : Realization D A)
    (g : (fibre k).obj M.group ≅ P.pinned.pair.G.val)
    (s : (fibre k).obj (splitTorus D) ≅ P.pinned.pair.T.group),
    (fibre k).map M.torus ≫ g.hom = s.hom ≫ P.pinned.pair.T.inclusion →
    (∀ (R : TestAlgebra k) (t : GroupPoints ((fibre k).obj (splitTorus D)) R)
      (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
      forgetFibrePoint (splitTorus D) R t = torusPoint D (CommAlgCat.of Integers.{u} R) v →
      ∀ x : D.X, characterValue (Additive.toMul (P.datumIso.val.weightEquiv x)) R
        (t ≫ s.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R)) →
    ∃ e : ∀ R : TestAlgebra k,
        TorusValues D (CommAlgCat.of Integers.{u} R) ≃* GroupPoints P.pinned.pair.T.group R,
      (∀ (R : TestAlgebra k) v x,
        characterValue (Additive.toMul (P.datumIso.val.weightEquiv x)) R (e R v) =
          (v (Multiplicative.ofAdd x) : R)) ∧
      ∀ (R : TestAlgebra k) v,
        forgetFibrePoint M.group R
          (e R v ≫ P.pinned.pair.T.inclusion.hom.hom ≫ g.inv.hom.hom) =
          torusPoint D (CommAlgCat.of Integers.{u} R) v ≫ M.torus.hom.hom

end MarkedFibre

section IntegralReflections

open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (IntegralAlgebra IntegralMarking IntegralPoints TorusValues
  integralPointFunctor torusPoint)
open IntegralRootRelations (upper lower)
open scoped CategoryTheory.MonObj

/-- The integral representative obtained from the linked rank-one maps. -/
def markedWeylWord {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (a : D.I) (R : IntegralAlgebra.{u}) (u : Rˣ) : IntegralPoints M.group R :=
  (M.rankOne a).app R (upper (u : R) * lower (-(↑u⁻¹ : R)) * upper (u : R))

/-- The linked word at parameter one acts on the original character algebra
by the indicated absolute reflection, functorially in the test algebra. -/
def IntegralWeylWordConjugation : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : IntegralMarking D) (a : D.I),
    (∀ {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (u : Rˣ),
      (integralPointFunctor M.group).map f (markedWeylWord M a R u) =
        markedWeylWord M a S (Units.map f.hom.toMonoidHom u)) ∧
    ∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R),
      let x := torusPoint D R t ≫ M.torus.hom.hom
      let n := markedWeylWord M a R 1
      n * x * n⁻¹ = torusPoint D R
        (t.comp (D.datum.reflection a).toLinearMap.toAddMonoidHom.toMultiplicative) ≫ M.torus.hom.hom

end IntegralReflections

section AbsoluteWeyl

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Classical
open Pinning (AttachedDatum PinnedGroup SimpleRoot)
open RootGroups (AdditiveLine)

/-- The absolute rational normalizer maps to the Weyl group of the specified
attached datum, with the marked rank-one words giving their simple labels. -/
def PinnedAbsoluteWeylLabels : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A) (D : AttachedDatum P.pair),
    letI := D.comm
    ∃ (C : DatumAndWeyl.Identification D.datum)
      (q : (𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X) →* D.datum.rootDatum.weylGroup),
      Function.Surjective q ∧
      (∀ n, n ≫ C.quotient.hom.hom = C.image.constantGroup.sectionPoint (C.labelEquiv (q n))) ∧
      (∀ n, q n = 1 ↔ ∃ t : 𝟙_ (SchemeOver k) ⟶ P.pair.T.group.X,
        t ≫ C.torusInclusion.hom.hom = n) ∧
      ∀ (i : SimpleRoot P.pair) (r : NormalizerComparison.SimpleRepresentative P D i) n,
        n ≫ C.normalizer.inclusion.hom.hom = r.reflection.representative →
        q n = RootPairing.weylGroup.ofIdx D.datum.rootDatum i.val

open AdjointRepresentation (GroupPoints)
open CharacterPairing (characterValue)
open IntegralSemisimpleModel (IntegralAlgebra IntegralPoints Integers Model TorusValues fibre
  forgetFibrePoint integerAlgebra integralPointFunctor torusPoint)
open Pinning (BasedRootDatum RootCoordinate)
open RationalRealization (Realization)

attribute [local instance] integerAlgebra

/-- In any of the marked field fibres, the specialization of the same
integral word represents the simple reflection with the marked index. -/
def MarkedFibreSimpleWeylLifts : Prop :=
  ∀ {k : Type u} [Field k] (D : BasedRootDatum.{u}) (M : Model D)
    {A : AdditiveLine k} (P : Realization D A)
    (g : (fibre k).obj M.group ≅ P.pinned.pair.G.val)
    (z : ∀ a : D.I, RootCoordinate A P.pinned.pair.T
      (P.pinned.roots (P.datumIso.val.indexEquiv a)).val (P.datumIso.val.indexEquiv a).val),
    (∀ a : D.base.support, z a.val = P.pinned.pin (P.simpleRoot a)) →
    (∀ (a : D.I) (R : TestAlgebra k) (v : R),
      forgetFibrePoint M.group R
        (RootGroups.rootPoint ((z a).val.hom ≫
          (P.pinned.roots (P.datumIso.val.indexEquiv a)).val.inclusion ≫ g.inv) R v) =
        M.line.point (CommAlgCat.of Integers.{u} R) v ≫ (M.root a).hom.hom) →
    ∀ e : ∀ R : TestAlgebra k,
      TorusValues D (CommAlgCat.of Integers.{u} R) ≃* GroupPoints P.pinned.pair.T.group R,
    (∀ (R : TestAlgebra k) v x,
      characterValue (Additive.toMul (P.datumIso.val.weightEquiv x)) R (e R v) =
        (v (Multiplicative.ofAdd x) : R)) →
    (∀ (R : TestAlgebra k) v,
      forgetFibrePoint M.group R
        (e R v ≫ P.pinned.pair.T.inclusion.hom.hom ≫ g.inv.hom.hom) =
        torusPoint D (CommAlgCat.of Integers.{u} R) v ≫ M.torus.hom.hom) →
    letI := P.attached.comm
    ∃ (C : DatumAndWeyl.Identification P.attached.datum)
      (q : (𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X) →* P.attached.datum.rootDatum.weylGroup),
      Function.Surjective q ∧
      (∀ n, n ≫ C.quotient.hom.hom = C.image.constantGroup.sectionPoint (C.labelEquiv (q n))) ∧
      (∀ n, q n = 1 ↔ ∃ t : 𝟙_ (SchemeOver k) ⟶ P.pinned.pair.T.group.X,
        t ≫ C.torusInclusion.hom.hom = n) ∧
      ∀ a : D.base.support,
        ∃ (r : NormalizerComparison.SimpleRepresentative P.pinned P.attached (P.simpleRoot a))
          (n : 𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X),
          n ≫ C.normalizer.inclusion.hom.hom = r.reflection.representative ∧
          q n = RootPairing.weylGroup.ofIdx P.attached.datum.rootDatum (P.simpleRoot a).val ∧
          ∀ R : TestAlgebra k, forgetFibrePoint M.group R
            (CartesianMonoidalCategory.toUnit ((testSpec k).obj (Opposite.op R)) ≫
              n ≫ C.normalizer.inclusion.hom.hom ≫ g.inv.hom.hom) =
            markedWeylWord M.toIntegralMarking a.val (CommAlgCat.of Integers.{u} R) 1

/-- The pinned simple rank-one words are permuted with their simple labels.
The orbit words are fixed representatives of the singleton or orthogonal
pair of reflections in the actual rational normalizer. -/
def PinnedOrbitWeylLifts : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A) (D : AttachedDatum P.pair),
    letI := D.comm
    ∀ (C : DatumAndWeyl.Identification D.datum)
      (q : (𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X) →* D.datum.rootDatum.weylGroup)
      (r : ∀ i : SimpleRoot P.pair, NormalizerComparison.SimpleRepresentative P D i),
    (∀ (i : SimpleRoot P.pair) n,
      n ≫ C.normalizer.inclusion.hom.hom = (r i).reflection.representative →
      q n = RootPairing.weylGroup.ofIdx D.datum.rootDatum i.val) →
    ∀ (f : Pinning.PinnedIso P P) (τ : Equiv.Perm (SimpleRoot P.pair)),
    (∀ i, Pinning.transportCharacter f.torus i.val.val = (τ i).val.val) →
    Function.Involutive τ →
    (∀ a b, D.datum.rootDatum.pairing a b = D.datum.rootDatum.pairing b a) →
    (∀ i, τ i ≠ i → D.datum.rootDatum.pairing i.val (τ i).val = 0) →
    (∀ i, (r i).reflection.representative ≫ f.group.hom.hom.hom =
      (r (τ i)).reflection.representative) ∧
    ∀ i, ∃ n : 𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X,
      n ≫ C.normalizer.inclusion.hom.hom ≫ f.group.hom.hom.hom =
        n ≫ C.normalizer.inclusion.hom.hom ∧
      if τ i = i then
        (n ≫ C.normalizer.inclusion.hom.hom = (r i).reflection.representative) ∧
        q n = RootPairing.weylGroup.ofIdx D.datum.rootDatum i.val
      else
        (n ≫ C.normalizer.inclusion.hom.hom =
          (r i).reflection.representative * (r (τ i)).reflection.representative) ∧
        q n = RootPairing.weylGroup.ofIdx D.datum.rootDatum i.val *
          RootPairing.weylGroup.ofIdx D.datum.rootDatum (τ i).val

/-- The marked absolute normalizer of a field fibre, with its rational
points as points of the integral model and with their original labels. -/
structure FibreNormalizer {D : BasedRootDatum.{u}} (M : Model D) (k : Type u) [Field k] where
  line : AdditiveLine k
  realization : Realization D line
  fibreIso : (fibre k).obj M.group ≅ realization.pinned.pair.G.val
  [torusComm : IsCommMonObj realization.pinned.pair.T.group.X]
  identification : DatumAndWeyl.Identification realization.attached.datum
  labelIso : D.datum.weylGroup ≃* realization.attached.toBased.datum.weylGroup
  labelIso_simple : ∀ i, labelIso (RootPairing.weylGroup.ofIdx D.datum i) =
    RootPairing.weylGroup.ofIdx realization.attached.toBased.datum (realization.datumIso.val.indexEquiv i)
  labelIso_character : ∀ w x, (labelIso w).val.weightEquiv (realization.datumIso.val.weightEquiv x) =
    realization.datumIso.val.weightEquiv (w.val.weightEquiv x)
  label : (𝟙_ (SchemeOver k) ⟶ identification.normalizer.group.X) →* D.datum.weylGroup
  label_surjective : Function.Surjective label
  projection : ∀ n, n ≫ identification.quotient.hom.hom =
    identification.image.constantGroup.sectionPoint (identification.labelEquiv (labelIso (label n)))
  kernel : ∀ n, label n = 1 ↔ ∃ t : 𝟙_ (SchemeOver k) ⟶ realization.pinned.pair.T.group.X,
    t ≫ identification.torusInclusion.hom.hom = n
  point : (𝟙_ (SchemeOver k) ⟶ identification.normalizer.group.X) →*
    IntegralPoints M.group (CommAlgCat.of Integers.{u} k)
  point_eq : ∀ n, point n = forgetFibrePoint M.group (CommAlgCat.of k k)
    (CartesianMonoidalCategory.toUnit _ ≫ n ≫ identification.normalizer.inclusion.hom.hom ≫ fibreIso.inv.hom.hom)
  torusValues : ∀ R : TestAlgebra k,
    TorusValues D (CommAlgCat.of Integers.{u} R) ≃* GroupPoints realization.pinned.pair.T.group R
  character : ∀ (R : TestAlgebra k) t x,
    characterValue (Additive.toMul (realization.datumIso.val.weightEquiv x)) R (torusValues R t) =
      (t (Multiplicative.ofAdd x) : R)
  torusPoint_eq : ∀ (R : TestAlgebra k) t,
    forgetFibrePoint M.group R
      (torusValues R t ≫ realization.pinned.pair.T.inclusion.hom.hom ≫ fibreIso.inv.hom.hom) =
      torusPoint D (CommAlgCat.of Integers.{u} R) t ≫ M.torus.hom.hom
  simple : ∀ i : D.base.support,
    ∃ (r : NormalizerComparison.SimpleRepresentative realization.pinned realization.attached (realization.simpleRoot i))
      (n : 𝟙_ (SchemeOver k) ⟶ identification.normalizer.group.X),
      n ≫ identification.normalizer.inclusion.hom.hom = r.reflection.representative ∧
      label n = RootPairing.weylGroup.ofIdx D.datum i.val ∧
      point n = markedWeylWord M.toIntegralMarking i.val (CommAlgCat.of Integers.{u} k) 1 ∧
      ∀ R : TestAlgebra k, forgetFibrePoint M.group R
        (CartesianMonoidalCategory.toUnit ((testSpec k).obj (Opposite.op R)) ≫ n ≫
          identification.normalizer.inclusion.hom.hom ≫ fibreIso.inv.hom.hom) =
        markedWeylWord M.toIntegralMarking i.val (CommAlgCat.of Integers.{u} R) 1

def MarkedFibreNormalizer : Prop :=
  ∀ (k : Type u) [Field k] {D : BasedRootDatum.{u}} (M : Model D), Nonempty (FibreNormalizer M k)

/-- The constant absolute Weyl labels and their kernel over an extension
field, with the action of coefficient conjugation fixed on the labels. -/
def NormalizerFieldLabels : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k),
    letI := F.torusComm
    let C := F.identification
    let R := CommAlgCat.of k K
    let Y := (testSpec k).obj (Opposite.op R)
    ∃ q : (Y ⟶ C.normalizer.group.X) →* D.datum.weylGroup,
      Function.Surjective q ∧
      (∀ n, n ≫ C.quotient.hom.hom = CartesianMonoidalCategory.toUnit Y ≫
        C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) ∧
      (∀ n, q n = 1 ↔ ∃ t : Y ⟶ F.realization.pinned.pair.T.group.X,
        t ≫ C.torusInclusion.hom.hom = n) ∧
      (∀ n, q (CartesianMonoidalCategory.toUnit Y ≫ n) = F.label n) ∧
      ∀ (a : R ⟶ R) n, q ((testSpec k).map a.op ≫ n) = q n

/-- A pinned automorphism on the actual field normalizer acts on its
absolute Weyl labels by the induced automorphism of the based datum. -/
def PinnedWeylFieldAction : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k)
    (e : Pinning.BasedIso D D) (s : Pinning.PinnedIso F.realization.pinned F.realization.pinned),
    (∀ i : D.base.support, Pinning.transportCharacter s.torus (F.realization.simpleRoot i).val.val =
      (F.realization.simpleRoot (simplePermutation D e i)).val.val) →
    letI := F.torusComm
    let C := F.identification
    let R := CommAlgCat.of k K
    let Y := (testSpec k).obj (Opposite.op R)
    let N := (Y ⟶ C.normalizer.group.X)
    ∃ (q : N →* D.datum.weylGroup) (a : MulAut N),
      Function.Surjective q ∧
      (∀ n, n ≫ C.quotient.hom.hom = CartesianMonoidalCategory.toUnit Y ≫
        C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) ∧
      (∀ n, q n = 1 ↔ ∃ t : Y ⟶ F.realization.pinned.pair.T.group.X,
        t ≫ C.torusInclusion.hom.hom = n) ∧
      (∀ n, q (CartesianMonoidalCategory.toUnit Y ≫ n) = F.label n) ∧
      (∀ (f : R ⟶ R) n, q ((testSpec k).map f.op ≫ n) = q n) ∧
      (∀ n, a n ≫ C.normalizer.inclusion.hom.hom = n ≫ C.normalizer.inclusion.hom.hom ≫ s.group.hom.hom.hom) ∧
      ∀ n, e.val * (q n).val = (q (a n)).val * e.val

/-- The absolute Weyl elements fixed by the indicated diagram automorphism. -/
def fixedWeylGroup (D : BasedRootDatum.{u}) (e : Pinning.BasedIso D D) : Subgroup D.datum.weylGroup :=
  (Subgroup.centralizer {e.val}).comap D.datum.weylGroup.subtype

/-- Coefficient conjugation on points over the splitting field. -/
def fieldCoefficientAction {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (G : GroupScheme k) :
    (GroupPoints G (CommAlgCat.of k K)) →* GroupPoints G (CommAlgCat.of k K) :=
  ((groupPointsFunctor k).obj G).map (CommAlgCat.ofHom σ.toAlgHom) |>.hom

/-- All fixed labels have integral representatives formed from the paired or
single pinned words, with the same label in the marked residue fibre. -/
def FoldedIntegralNormalizerLifts : Prop :=
  ∀ {k K l : Type u} [Field k] [Field K] [Field l] [Algebra k K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k) (E : FibreNormalizer M l)
    (e : Pinning.BasedIso D D) (s : Pinning.PinnedIso F.realization.pinned F.realization.pinned)
    (σ : K ≃ₐ[k] K),
    (∀ i : D.base.support, Pinning.transportCharacter s.torus (F.realization.simpleRoot i).val.val =
      (F.realization.simpleRoot (simplePermutation D e i)).val.val) →
    Function.Involutive e.val.indexEquiv →
    (∀ a b, D.datum.pairing a b = D.datum.pairing b a) →
    (∀ i : D.base.support, simplePermutation D e i ≠ i → D.datum.pairing (simplePermutation D e i).val i.val = 0) →
    ∀ (R : IntegralAlgebra.{u}) (f : R ⟶ CommAlgCat.of Integers.{u} K) (g : R ⟶ CommAlgCat.of Integers.{u} l),
    letI := F.torusComm
    letI := E.torusComm
    let C := F.identification
    let S := CommAlgCat.of k K
    let Y := (testSpec k).obj (Opposite.op S)
    let N := (Y ⟶ C.normalizer.group.X)
    ∃ (q : N →* D.datum.weylGroup) (a : MulAut N),
      (∀ n, n ≫ C.quotient.hom.hom = CartesianMonoidalCategory.toUnit Y ≫
        C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) ∧
      (∀ n, q n = 1 ↔ ∃ t : Y ⟶ F.realization.pinned.pair.T.group.X,
        t ≫ C.torusInclusion.hom.hom = n) ∧
      (∀ n, a n ≫ C.normalizer.inclusion.hom.hom = n ≫ C.normalizer.inclusion.hom.hom ≫ s.group.hom.hom.hom) ∧
      let B := MonoidHom.eqLocus a.toMonoidHom (fieldCoefficientAction σ C.normalizer.group)
      ∃ q₀ : B →* fixedWeylGroup D e,
        (∀ n, (q₀ n).val = q n.val) ∧
        (∀ n : B, q₀ n = 1 ↔ ∃ t : Y ⟶ F.realization.pinned.pair.T.group.X,
          t ≫ C.torusInclusion.hom.hom = n.val) ∧
        ∀ w : fixedWeylGroup D e,
          ∃ (n : B) (m : 𝟙_ (SchemeOver l) ⟶ E.identification.normalizer.group.X)
            (p : IntegralPoints M.group R),
            q₀ n = w ∧ E.label m = w.val ∧
            (integralPointFunctor M.group).map f p = forgetFibrePoint M.group S
              (n.val ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom) ∧
            (integralPointFunctor M.group).map g p = E.point m

/-- Every split Weyl label has a representative given by the same marked
integral word in the field and in a residue field of the test algebra. -/
def SplitIntegralWeylLifts : Prop :=
  ∀ {k l : Type u} [Field k] [Field l] {D : BasedRootDatum.{u}} (M : Model D)
    (F : FibreNormalizer M k) (E : FibreNormalizer M l) (R : IntegralAlgebra.{u})
    (f : R ⟶ CommAlgCat.of Integers.{u} k) (e : R ⟶ CommAlgCat.of Integers.{u} l),
    letI := F.torusComm
    letI := E.torusComm
    ∀ w : D.datum.weylGroup,
      ∃ (n : 𝟙_ (SchemeOver k) ⟶ F.identification.normalizer.group.X)
        (m : 𝟙_ (SchemeOver l) ⟶ E.identification.normalizer.group.X) (p : IntegralPoints M.group R),
        F.label n = w ∧ E.label m = w ∧
        (integralPointFunctor M.group).map f p = F.point n ∧
        (integralPointFunctor M.group).map e p = E.point m

/-- The torus is the kernel of the actual absolute normalizer label. The
anti-pullback convention on characters agrees with conjugation on its points. -/
def FibreNormalizerTorusAction : Prop :=
  ∀ {k : Type u} [Field k] {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k),
    let R := CommAlgCat.of Integers.{u} k
    ∃ j : TorusValues D R ≃* F.label.ker,
      (∀ v, F.point (j v).val = torusPoint D R v ≫ M.torus.hom.hom) ∧
      ∀ n v, conjugateTorus F.label n (j v) =
        j (v.comp (F.label n).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative)

/-- The same torus-kernel and Weyl-action comparisons over the splitting
field of a pinned descent, using extension-field points of that pinning. -/
def NormalizerFieldTorusAction : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k),
    letI := F.torusComm
    let C := F.identification
    let R := CommAlgCat.of k K
    let Y := (testSpec k).obj (Opposite.op R)
    let S := CommAlgCat.of Integers.{u} K
    ∀ q : (Y ⟶ C.normalizer.group.X) →* D.datum.weylGroup,
      (∀ n, n ≫ C.quotient.hom.hom = CartesianMonoidalCategory.toUnit Y ≫
        C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) →
      (∀ n, q n = 1 ↔ ∃ t : Y ⟶ F.realization.pinned.pair.T.group.X,
        t ≫ C.torusInclusion.hom.hom = n) →
      ∃ j : TorusValues D S ≃* q.ker,
        (∀ v, (j v).val ≫ C.normalizer.inclusion.hom.hom =
          F.torusValues R v ≫ F.realization.pinned.pair.T.inclusion.hom.hom) ∧
        (∀ v, forgetFibrePoint M.group R ((j v).val ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom) =
          torusPoint D S v ≫ M.torus.hom.hom) ∧
        ∀ n v, conjugateTorus q n (j v) =
          j (v.comp (q n).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative)

/-- Fixed torus points in the actual field normalizer satisfy the paired
unit equations in the marked character basis. -/
def FixedNormalizerTorusCoordinates : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k)
    {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y)
    (s : Pinning.PinnedIso F.realization.pinned F.realization.pinned)
    (τ : Equiv.Perm index) (σ : K ≃ₐ[k] K), Function.Involutive σ →
    letI := F.torusComm
    let C := F.identification
    let T := F.realization.pinned.pair.T
    let R := CommAlgCat.of k K
    let Y := (testSpec k).obj (Opposite.op R)
    let S := CommAlgCat.of Integers.{u} K
    let N := (Y ⟶ C.normalizer.group.X)
    let χ (i : index) := Additive.toMul (F.realization.datumIso.val.weightEquiv (characterBasis D b i))
    (∀ i, Pinning.transportCharacter s.torus (χ i) = χ (τ i)) →
    ∀ (q : N →* D.datum.weylGroup) (a : MulAut N),
      (∀ n, n ≫ C.quotient.hom.hom = CartesianMonoidalCategory.toUnit Y ≫
        C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) →
      (∀ n, q n = 1 ↔ ∃ t : Y ⟶ T.group.X, t ≫ C.torusInclusion.hom.hom = n) →
      (∀ n, a n ≫ C.normalizer.inclusion.hom.hom = n ≫ C.normalizer.inclusion.hom.hom ≫ s.group.hom.hom.hom) →
      let B := MonoidHom.eqLocus a.toMonoidHom (fieldCoefficientAction σ C.normalizer.group)
      ∃ j : TorusValues D S ≃* q.ker,
        (∀ v, forgetFibrePoint M.group R ((j v).val ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom) =
          torusPoint D S v ≫ M.torus.hom.hom) ∧
        (∀ n v, conjugateTorus q n (j v) =
          j (v.comp (q n).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative)) ∧
        ∀ v, (j v).val ∈ B ↔
          ∀ i, (v (Multiplicative.ofAdd (characterBasis D b (τ i))) : K) =
            σ (v (Multiplicative.ofAdd (characterBasis D b i)) : K)

open scoped TensorProduct SemidirectProduct

/-- The rational apartment of the largest split subtorus in the diagram case. -/
def invariantApartment (D : BasedRootDatum.{u}) (e : Pinning.BasedIso D D) : Submodule ℚ (ℚ ⊗[ℤ] D.Y) :=
  LinearMap.ker ((e.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y).toLinearMap - LinearMap.id)

/-- The fixed absolute Weyl group acts faithfully on the invariant apartment. -/
def FoldedWeylLinearAction : Prop :=
  ∀ (D : BasedRootDatum.{u}) (e : Pinning.BasedIso D D)
    {index : Type u} [Fintype index] (_ : Module.Basis index ℤ D.Y),
    Function.Involutive e.val.indexEquiv →
    (∀ i : D.base.support, simplePermutation D e i ≠ i → D.datum.pairing (simplePermutation D e i).val i.val = 0) →
    let V := invariantApartment D e
    ∃ w : fixedWeylGroup D e →* (V ≃ₗ[ℚ] V),
      Function.Injective w ∧ ∀ a (x : V), (w a x).val =
        (a.val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y) x.val

/-- The inclusion of the valuation ring, as a map of integral test algebras. -/
def valuationRingInclusion (K : Type u) [Field K] [ValuativeRel K] :
    CommAlgCat.of Integers.{u} (valuation K).valuationSubring ⟶ CommAlgCat.of Integers.{u} K :=
  let O := (valuation K).valuationSubring
  CommAlgCat.ofHom
    ({ O.subtype with commutes' := fun a ↦ map_intCast O.subtype a.down } : O →ₐ[Integers.{u}] K)

/-- The split affine action and the split cocharacter translation lattice
for the actual marked normalizer. The integral subgroup is pulled back from
the original integral model over the valuation ring. -/
def SplitApartmentAction : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M K)
    {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y),
    letI := F.torusComm
    let R := CommAlgCat.of Integers.{u} K
    let N := (𝟙_ (SchemeOver K) ⟶ F.identification.normalizer.group.X)
    let V := ℚ ⊗[ℤ] D.Y
    let J := (((integralPointFunctor M.group).map (valuationRingInclusion K)).hom.range).comap F.point
    ∃ (j : TorusValues D R ≃* F.label.ker) (ν : TorusValues D R →* Multiplicative D.Y)
      (ρ : D.datum.weylGroup →* MulAut (Multiplicative D.Y))
      (p : N →* Multiplicative D.Y ⋊[ρ] D.datum.weylGroup) (a : N →* (V ≃ᵃ[ℚ] V)),
      Function.Surjective ν ∧ Function.Surjective p ∧
      p.ker = F.label.ker ⊓ J ∧ a.ker = p.ker ∧
      (∀ t, F.point (j t).val = torusPoint D R t ≫ M.torus.hom.hom) ∧
      (∀ t x, D.datum.toLinearMap x (ν t).toAdd =
        WithZero.log (normalizedValuation K (t (Multiplicative.ofAdd x) : K))) ∧
      (∀ w y, (ρ w (Multiplicative.ofAdd y)).toAdd = w.val.coweightEquiv.symm y) ∧
      (∀ n, (p n).right = F.label n) ∧
      (∀ t, (p (j t).val).left = ν t) ∧
      (∀ n x, a n x =
        ((F.label n).val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y) x +
          ((1 : ℚ) ⊗ₜ[ℤ] (p n).left.toAdd)) ∧
      (∀ n m, m ∈ J → ∀ h : F.label n = F.label m,
        (p n).left = ν (j.symm ⟨n * m⁻¹, by simp [h]⟩)) ∧
      ∀ (n : N) (x : V) (s t : TorusValues D R),
        (1 : ℚ) ⊗ₜ[ℤ] (ν s).toAdd = -x →
        (1 : ℚ) ⊗ₜ[ℤ] (ν t).toAdd = -(a n x) →
        (j t).val * n * (j s).val⁻¹ ∈ J

/-- The fixed normalizer's affine action on the invariant apartment. The
valuation is that of the splitting field and is divided by two on the apartment. -/
def FoldedApartmentAction : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k)
    (e : Pinning.BasedIso D D) (s : Pinning.PinnedIso F.realization.pinned F.realization.pinned)
    (σ : K ≃ₐ[k] K) (b : Module.Basis D.base.support ℤ D.Y),
    ((∃ h, b = simpleCorootBasis D h) ∨ (∃ h, b = fundamentalCoweightBasis D h)) →
    Function.Involutive σ → Function.Involutive e.val.indexEquiv →
    (∀ a b, D.datum.pairing a b = D.datum.pairing b a) →
    (∀ i : D.base.support, simplePermutation D e i ≠ i → D.datum.pairing (simplePermutation D e i).val i.val = 0) →
    (∀ i : D.base.support, Pinning.transportCharacter s.torus (F.realization.simpleRoot i).val.val =
      (F.realization.simpleRoot (simplePermutation D e i)).val.val) →
    (∀ i : D.base.support, Pinning.transportCharacter s.torus
      (Additive.toMul (F.realization.datumIso.val.weightEquiv (characterBasis D b i))) =
      Additive.toMul (F.realization.datumIso.val.weightEquiv (characterBasis D b (simplePermutation D e i)))) →
    (∀ x : K, normalizedValuation K (σ x) = normalizedValuation K x) →
    letI := F.torusComm
    let C := F.identification
    let R := CommAlgCat.of k K
    let Y := (testSpec k).obj (Opposite.op R)
    let N := (Y ⟶ C.normalizer.group.X)
    let S := CommAlgCat.of Integers.{u} K
    let V := invariantApartment D e
    let W := fixedWeylGroup D e
    ∃ (q : N →* D.datum.weylGroup) (a : MulAut N),
      (∀ n, n ≫ C.quotient.hom.hom = CartesianMonoidalCategory.toUnit Y ≫
        C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) ∧
      (∀ n, q n = 1 ↔ ∃ t : Y ⟶ F.realization.pinned.pair.T.group.X,
        t ≫ C.torusInclusion.hom.hom = n) ∧
      (∀ n, a n ≫ C.normalizer.inclusion.hom.hom = n ≫ C.normalizer.inclusion.hom.hom ≫ s.group.hom.hom.hom) ∧
      let B := MonoidHom.eqLocus a.toMonoidHom (fieldCoefficientAction σ C.normalizer.group)
      ∃ (q₀ : B →* W) (ν : q₀.ker →* Multiplicative D.Y)
        (j : B →* IntegralPoints M.group S),
        (∀ n, (q₀ n).val = q n.val) ∧
        (∀ n, j n = forgetFibrePoint M.group R
          (n.val ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom)) ∧
        (∀ t : q₀.ker, ∃ v : TorusValues D S,
          j t.val = torusPoint D S v ≫ M.torus.hom.hom ∧
          ∀ x, D.datum.toLinearMap x (ν t).toAdd =
            WithZero.log (normalizedValuation K (v (Multiplicative.ofAdd x) : K))) ∧
        (∀ [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
          (∀ x : k, normalizedValuation K (algebraMap k K x) = (normalizedValuation k x) ^ 2) →
          (∀ u : Kˣ, σ (u : K) = (u : K) → ∃ a : kˣ, algebraMap k K (a : k) = (u : K)) →
          Set.range (fun t : q₀.ker => fun i : D.base.support =>
            ((b.repr (ν t).toAdd i : ℤ) : ℚ) / 2) =
            Set.range (orbitProjection (simplePermutation D e))) ∧
        let J := (((integralPointFunctor M.group).map (valuationRingInclusion K)).hom.range).comap j
        let Λ := ν.range
        Function.Surjective (q₀.comp J.subtype) ∧
        ∃ (ρ : W →* MulAut Λ) (p : B →* Λ ⋊[ρ] W) (h : B →* (V ≃ᵃ[ℚ] V)),
          Function.Surjective p ∧ p.ker = q₀.ker ⊓ J ∧ h.ker = p.ker ∧
          (∀ n, (p n).right = q₀ n) ∧ (∀ t : q₀.ker, (p t.val).left.val = ν t) ∧
          (∀ n x, (h n x).val =
            ((q₀ n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y) x.val +
              ((1 / 2 : ℚ) ⊗ₜ[ℤ] (p n).left.val.toAdd)) ∧
          (∀ n m, m ∈ J → ∀ h : q₀ n = q₀ m,
            (p n).left.val = ν ⟨n * m⁻¹, by simp [h]⟩) ∧
          ∀ (n : B) (x : V) (c d : q₀.ker),
            (1 / 2 : ℚ) ⊗ₜ[ℤ] (ν c).toAdd = -x.val →
            (1 / 2 : ℚ) ⊗ₜ[ℤ] (ν d).toAdd = -(h n x).val →
            d.val * n * c.val⁻¹ ∈ J

end AbsoluteWeyl

section Centralizer

open CategoryTheory.MonoidalCategory
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsReductive IsSplitTorus IsTorus)
open SchemeDerivedGroup (IsSubgroupOf)
open RankOneFlag (IsGeometricallyMaximal)
open SubtorusCentralizer (IsCentralizer)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)

/-- A subtorus containing a regular cocharacter over a splitting field
has the marked torus as its scheme centralizer. -/
def RegularSubtorusCentralizer : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T S : ClosedSubgroup G.val), IsTorus T.group →
    ∀ (j : S.group ⟶ T.group), j ≫ T.inclusion = S.inclusion →
      let F := groupBaseChange k K
      ∀ (hT : IsClosedImmersion (F.map T.inclusion).hom.hom.left),
        let TK := scalarExtendedSubgroup K T hT
        IsSplitTorus TK.group → IsGeometricallyMaximal TK →
        ∀ c : Cocharacter (F.obj S.group),
          BorelsAndChambers.IsRegular TK (c ≫ F.map j) → IsCentralizer S T

/-- In the rational Borel pair the largest split subtorus of the pinned
torus has centralizer exactly that torus. -/
def BorelSplitTorusCentralizer : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (B T S : ClosedSubgroup G.val), GeometricBorelConjugacy.IsKBorel B →
      IsTorus T.group → IsGeometricallyMaximal T → IsSubgroupOf T B → IsSubgroupOf S T →
      (∀ U : ClosedSubgroup G.val, IsSplitTorus U.group → IsSubgroupOf U T → IsSubgroupOf U S) →
        IsCentralizer S T

/-- Once the largest split subtorus of the marked torus has centralizer equal
to the marked torus, it is maximal in the group and their rational normalizers
coincide. The containment property is for split subtori of the marked torus. -/
def CentralizingSplitTorusNormalizer : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (T S : ClosedSubgroup G.val),
    IsSplitTorus S.group → IsSubgroupOf S T → IsCentralizer S T →
    (∀ U : ClosedSubgroup G.val, IsSplitTorus U.group → IsSubgroupOf U T → IsSubgroupOf U S) →
    IsMaximalSplitTorus S ∧
      ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
        Normalizes S.inclusion g ↔ Normalizes T.inclusion g

/-- The normalizing condition on a rational point can be tested after
extension to the splitting field, on the actual scalar-extended torus. -/
def RationalNormalizerBaseChange : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X),
    Normalizes T.inclusion g ↔
      Normalizes ((groupBaseChange k K).map T.inclusion) (scalarExtendedRationalPoint K g)

/-- The pinned comparison intertwines the two torus inclusions and hence
recognizes the rational normalizer by the corresponding split normalizer. -/
def PinnedNormalizerComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    {D : Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (_ : AdjointBorelCohomology.PinnedTwist K D l B T),
    let F := groupBaseChange k K
    ∃ (e : F.obj G.val ≅ F.obj P.pair.G.val) (d : F.obj T.group ≅ F.obj P.pair.T.group),
      d.hom ≫ F.map P.pair.T.inclusion = F.map T.inclusion ≫ e.hom ∧
      ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
        Normalizes T.inclusion g ↔ Normalizes (F.map P.pair.T.inclusion)
          (scalarExtendedRationalPoint K g ≫ e.hom.hom.hom)

open CategoryTheory.Limits
open scoped TensorProduct

/-- The rational section of an affine Hopf spectrum specified by an
evaluation of its coordinates in the ground field. -/
def hopfFieldPoint {k : Type u} [Field k] {A : HopfAlgebraCategory k} (p : A →ₐ[k] k) :
    𝟙_ (SchemeOver k) ⟶ (specGroup A).X := by
  refine Over.homMk (Spec.map (CommRingCat.ofHom p.toRingHom)) ?_
  change Spec.map (CommRingCat.ofHom p.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 (Spec (CommRingCat.of k))
  have h : CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom p.toRingHom =
      𝟙 (CommRingCat.of k) := CommRingCat.hom_ext (RingHom.ext fun x => p.commutes x)
  rw [← Spec.map_comp, h]
  exact Spec.map_id _

/-- Compatibility of the Hopf presentation with the projection from the
scalar-extended group. -/
def ExtendsCoordinatePresentation {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k)
    (e : specGroup (extendedHopf K (AdjointCocharacters.coordinateHopf G)) ≅
      (groupBaseChange k K).obj G.val) : Prop :=
  e.hom.hom.hom.left ≫ pullback.fst G.val.X.hom (fieldSpecMap k K) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : AdjointCocharacters.coordinateHopf G →ₐ[k]
        K ⊗[k] AdjointCocharacters.coordinateHopf G).toRingHom) ≫
      (AdjointCocharacters.coordinateHopfIso G).hom.hom.hom.left

open scoped CategoryTheory.MonObj in
/-- The rational normalizer of the pinned descended torus corresponds to
the coefficient-equivariant points of the actual split normalizer. -/
def PinnedFixedRationalNormalizer : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    {D : Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : AdjointBorelCohomology.PinnedTwist K D l B T),
    let F := groupBaseChange k K
    ∃ (a : specGroup (extendedHopf K (AdjointCocharacters.coordinateHopf G)) ≅ F.obj G.val)
      (b : specGroup (extendedHopf K (AdjointCocharacters.coordinateHopf P.pair.G)) ≅ F.obj P.pair.G.val),
      ExtendsCoordinatePresentation G a ∧ ExtendsCoordinatePresentation P.pair.G b ∧
      let e := a.symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso d.groupIso.op ≪≫ b
      ∃ (t : F.obj T.group ≅ F.obj P.pair.T.group)
        (f : (𝟙_ (SchemeOver k) ⟶ G.val.X) →* (𝟙_ (SchemeOver K) ⟶ (F.obj P.pair.G.val).X)),
        t.hom ≫ F.map P.pair.T.inclusion = F.map T.inclusion ≫ e.hom ∧
        Function.Injective f ∧
        (∀ g, f g = scalarExtendedRationalPoint K g ≫ e.hom.hom.hom) ∧
        (∀ g, Normalizes T.inclusion g ↔ Normalizes (F.map P.pair.T.inclusion) (f g)) ∧
        ∀ h : extendedHopf K (AdjointCocharacters.coordinateHopf P.pair.G) →ₐ[K] K,
          let x := hopfFieldPoint h ≫ b.hom.hom.hom
          (Normalizes (F.map P.pair.T.inclusion) x ∧
            ∀ σ y, h (pinnedCoordinateAction d σ y) = σ (h y)) ↔
          ∃ g, Normalizes T.inclusion g ∧ f g = x

/-- The split subtorus of the descended permutation torus gives the actual
relative Weyl quotient and its rational representatives. -/
def DescendedRelativeNormalizer : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    {D : Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {ω : Gal(K/k) →* Aut D.toBased} (d : PinnedPairDescent.DescendedPair K (l := l) ω)
    {ι : Type u} [Finite ι] {r : Gal(K/k) →* Equiv.Perm ι}
    (b : AdjointBorelCohomology.PermutedCharacterBasis K ι
      (Unipotent.closedSubgroupAlgebraicGroup d.torus) r),
    CharacterDescent.IsDiagonalizable (extendedHopf K
      (AdjointCocharacters.coordinateHopf (Unipotent.closedSubgroupAlgebraicGroup d.torus))) →
    ∃ (S : ClosedSubgroup d.group.val) (N : Relative.RelativeWeylScheme.QuotientData S),
      IsMaximalSplitTorus S ∧ IsSubgroupOf S d.torus ∧ IsCentralizer S d.torus ∧
      RankOneFlag.SameSubgroup N.centralizer d.torus ∧
      (∀ n : 𝟙_ (SchemeOver k) ⟶ d.group.val.X,
        Normalizes S.inclusion n ↔ Normalizes d.torus.inclusion n) ∧
      ∀ w : N.splitImage.labels, ∃ n,
        Relative.RelativeWeylScheme.rationalProjection N n = N.splitImage.constantGroup.sectionPoint w

open scoped CategoryTheory.MonObj

/-- The rational normalizer of the descended torus is identified with the
fixed subgroup of the marked split normalizer by the pinned scalar comparison.
The same point map identifies the two torus subgroups. -/
def PinnedQuadraticNormalizer : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : Pinning.BasedRootDatum.{u}} {M : IntegralSemisimpleModel.Model D}
    (E : FibreNormalizer M k)
    {l : Aut E.realization.attached.toBased ≃* Aut E.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : AdjointBorelCohomology.PinnedTwist K E.realization.attached l B T)
    (σ : Gal(K/k)), Module.finrank k K = 2 → σ ≠ 1 →
    letI := E.torusComm
    let C := E.identification
    let P := E.realization.pinned
    let s := (l (d.outer σ)).asIso.hom
    let Y := (testSpec k).obj (Opposite.op (CommAlgCat.of k K))
    let F := groupBaseChange k K
    ∀ (a : MulAut (Y ⟶ C.normalizer.group.X)),
      (∀ n, a n ≫ C.normalizer.inclusion.hom.hom =
        n ≫ C.normalizer.inclusion.hom.hom ≫ s.group.hom.hom.hom) →
      ∀ (N : ClosedSubgroup G.val),
        (∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, Normalizes T.inclusion g ↔
          ∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X, n ≫ N.inclusion.hom.hom = g) →
        let H := MonoidHom.eqLocus a.toMonoidHom (fieldCoefficientAction σ C.normalizer.group)
        ∃ (c₁ : specGroup (extendedHopf K (AdjointCocharacters.coordinateHopf G)) ≅ F.obj G.val)
          (c₂ : specGroup (extendedHopf K (AdjointCocharacters.coordinateHopf P.pair.G)) ≅ F.obj P.pair.G.val),
          ExtendsCoordinatePresentation G c₁ ∧ ExtendsCoordinatePresentation P.pair.G c₂ ∧
          let e := c₁.symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso d.groupIso.op ≪≫ c₂
          ∃ (t : F.obj T.group ≅ F.obj P.pair.T.group)
            (u : (𝟙_ (SchemeOver k) ⟶ N.group.X) ≃* H),
            t.hom ≫ F.map P.pair.T.inclusion = F.map T.inclusion ≫ e.hom ∧
            (∀ n, ((u n).val ≫ C.normalizer.inclusion.hom.hom).left =
              (scalarExtendedRationalPoint K (n ≫ N.inclusion.hom.hom) ≫ e.hom.hom.hom).left ≫
                pullback.fst P.pair.G.val.X.hom (fieldSpecMap k K)) ∧
            ∀ n, (∃ x : 𝟙_ (SchemeOver k) ⟶ T.group.X,
                x ≫ T.inclusion.hom.hom = n ≫ N.inclusion.hom.hom) ↔
              ∃ x : Y ⟶ P.pair.T.group.X,
                x ≫ C.torusInclusion.hom.hom = (u n).val

end Centralizer

section QuadraticFactors

/-- The two kinds of stabilizer fields for the actual quadratic diagram field.
The fixed units in a singleton come from the base field. -/
def QuadraticStabilizerFields : Prop :=
  ∀ {F L : Type u} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L],
    Module.finrank F L = 2 → ∀ (σ : Gal(L/F)), σ ≠ 1 →
      (∀ u : Lˣ, σ (u : L) = (u : L) →
        ∃ a : Fˣ, algebraMap F L (a : F) = (u : L)) ∧
      ∀ {ι : Type u} (r : Gal(L/F) →* Equiv.Perm ι) (i : ι),
        letI := MulAction.compHom ι r
        (r σ i = i → IntermediateField.fixedField (MulAction.stabilizer Gal(L/F) i) = ⊥) ∧
        (r σ i ≠ i → IntermediateField.fixedField (MulAction.stabilizer Gal(L/F) i) = ⊤)

/-- The translation image of the descended torus on rational points, in the
actual permutation basis and with the base field normalization. -/
def DescendedTorusTranslations : Prop :=
  ∀ {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [ValuativeRel F] [ValuativeRel L] [TopologicalSpace F] [TopologicalSpace L]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField L],
    Module.finrank F L = 2 → ∀ (σ : Gal(L/F)), σ ≠ 1 →
    (∀ x : F, normalizedValuation L (algebraMap F L x) = (normalizedValuation F x) ^ 2) →
    (∀ x : L, normalizedValuation L (σ x) = normalizedValuation L x) →
    ∀ {ι : Type u} [Fintype ι] {r : Gal(L/F) →* Equiv.Perm ι} {H : AffineAlgebraicGroup F}
      (c : AdjointBorelCohomology.PermutedCharacterBasis L ι H r),
      let C := AdjointCocharacters.coordinateHopf H
      CharacterDescent.IsDiagonalizable (extendedHopf L C) →
      Set.range (fun f : C →ₐ[F] F ↦ fun i ↦
        ((WithZero.log (normalizedValuation L (Algebra.TensorProduct.rid F L L
          (Algebra.TensorProduct.map (AlgHom.id L L) f (c.basis i).toMul.val))) : ℤ) : ℚ) / 2) =
        Set.range (orbitProjection (r σ))

end QuadraticFactors

section ScalarScaling

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
open WithZero
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Integers IntegralPoints TorusValues Model integerAlgebra
  integralPointFunctor forgetFibrePoint torusPoint cocharacter)

attribute [local instance] integerAlgebra

/-- The extended normalized valuation is invariant under a quadratic coefficient involution. -/
def InvolutiveValuationInvariant : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension k K] (σ : Gal(K/k)), Function.Involutive σ →
    ∀ x, normalizedValuation K (σ x) = normalizedValuation K x

/-- A finite scalar extension containing an indicated root of the base
uniformizer, equipped with the extended valuation. -/
def UniformizerRootExtension : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (m : ℕ), 0 < m → ∀ π : Kˣ, log (normalizedValuation K (π : K)) = -1 →
    ∃ (L : Type u) (h : Field L), letI := h
      ∃ (a : Algebra K L) (v : ValuativeRel L) (t : TopologicalSpace L), letI := a; letI := v; letI := t
      ∃ (_ : FiniteDimensional K L) (_ : ValuativeExtension K L) (_ : IsNonarchimedeanLocalField L)
        (s : Lˣ) (c : ℤ),
          0 < c ∧ s ^ m = Units.map (algebraMap K L).toMonoidHom π ∧
          log (normalizedValuation L (s : L)) = -c ∧
          ∀ x : Kˣ, log (normalizedValuation L (algebraMap K L (x : K))) =
            (m : ℤ) * c * log (normalizedValuation K (x : K))

/-- The marked normalizer point as a point of the original integral model. -/
def markedNormalizerPoint {k : Type u} [Field k] {D : BasedRootDatum.{u}} {M : Model D}
    (F : FibreNormalizer M k) (R : TestAlgebra k) :
    letI := F.torusComm
    Points F.identification.normalizer.group.X R → IntegralPoints M.group (CommAlgCat.of Integers.{u} R) := by
  letI := F.torusComm
  exact fun n => forgetFibrePoint M.group R
    (n ≫ F.identification.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom)

/-- Scaling a marked normalizer point at a rational apartment point and its
affine image leaves an integral Weyl representative times a unit torus point.
The normalization factor is one in the split case and two over the ramified
quadratic splitting field. -/
def ScalarAffineScaling : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k)
    {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y),
    letI := F.torusComm
    let C := F.identification
    let R := CommAlgCat.of k K
    let S := CommAlgCat.of Integers.{u} K
    let Y := (testSpec k).obj (Opposite.op R)
    let N := (Y ⟶ C.normalizer.group.X)
    ∀ (q : N →* D.datum.weylGroup),
      (∀ n, n ≫ C.quotient.hom.hom = toUnit Y ≫ C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) →
      (∀ n, q n = 1 ↔ ∃ t : Y ⟶ F.realization.pinned.pair.T.group.X,
        t ≫ C.torusInclusion.hom.hom = n) →
      ∀ (n m : N), q n = q m →
        (markedNormalizerPoint F R m ∈ ((integralPointFunctor M.group).map (valuationRingInclusion K)).hom.range) →
        ∀ (r : ℕ), 0 < r → ∀ (x : ℚ ⊗[ℤ] D.Y) (π : Kˣ),
          log (normalizedValuation K (π : K)) = -1 →
          ∃ (t : TorusValues D S) (z : D.Y),
            markedNormalizerPoint F R (n * m⁻¹) = torusPoint D S t ≫ M.torus.hom.hom ∧
            (∀ χ, D.datum.toLinearMap χ z =
              log (normalizedValuation K (t (Multiplicative.ofAdd χ) : K))) ∧
            let y := ((q n).val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y) x +
              (((r : ℚ)⁻¹) ⊗ₜ[ℤ] z)
            ∃ (d : ℕ), 0 < d ∧
              ∃ (L : Type u) (h : Field L), letI := h
                ∃ (a : Algebra K L) (v : ValuativeRel L) (t : TopologicalSpace L),
                  letI := a
                  letI := v
                  letI := t
                  ∃ (_ : FiniteDimensional K L) (_ : ValuativeExtension K L) (_ : IsNonarchimedeanLocalField L)
                    (s : Lˣ) (u v : D.Y),
                    s ^ d = Units.map (algebraMap K L).toMonoidHom π ∧
                    (1 : ℚ) ⊗ₜ[ℤ] u = (d : ℚ) • ((r : ℚ) • x) ∧
                    (1 : ℚ) ⊗ₜ[ℤ] v = (d : ℚ) • ((r : ℚ) • y) ∧
                    let SL := CommAlgCat.of Integers.{u} L
                    let f : S ⟶ SL := CommAlgCat.ofHom
                      { (algebraMap K L) with commutes' := fun m ↦ map_intCast (algebraMap K L) m.down }
                    let g : IntegralPoints M.group S →* IntegralPoints M.group SL := ((integralPointFunctor M.group).map f).hom
                    let c : IntegralPoints M.group SL := torusPoint D SL (cocharacter D u SL s) ≫ M.torus.hom.hom
                    let b : IntegralPoints M.group SL := torusPoint D SL (cocharacter D v SL s) ≫ M.torus.hom.hom
                    ∃ w : TorusValues D SL,
                      (∀ χ, normalizedValuation L (w (Multiplicative.ofAdd χ) : L) = 1) ∧
                      b * g (markedNormalizerPoint F R n) * c⁻¹ =
                        (show IntegralPoints M.group SL from torusPoint D SL w ≫ M.torus.hom.hom) * g (markedNormalizerPoint F R m) ∧
                      b * g (markedNormalizerPoint F R n) * c⁻¹ ∈
                        ((integralPointFunctor M.group).map (valuationRingInclusion L)).hom.range

end ScalarScaling

section RelativeLabels

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Relative.RelativeWeylScheme (QuotientData rationalProjection)

/-- A surjective absolute label on the rational relative normalizer with the
descended torus as kernel agrees with the D09 quotient on representatives. -/
def RelativeWeylLabels : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {S T : ClosedSubgroup G.val}
    (N : QuotientData S), RankOneFlag.SameSubgroup N.centralizer T →
    (∀ w : N.splitImage.labels, ∃ n,
      rationalProjection N n = N.splitImage.constantGroup.sectionPoint w) →
    ∀ {W : Type u} [Group W] (q : (𝟙_ (SchemeOver k) ⟶ N.normalizer.group.X) →* W),
      Function.Surjective q →
      (∀ n, q n = 1 ↔ ∃ t : 𝟙_ (SchemeOver k) ⟶ T.group.X,
        t ≫ T.inclusion.hom.hom = n ≫ N.normalizer.inclusion.hom.hom) →
      ∃ e : N.splitImage.labels ≃* W,
        ∀ n, rationalProjection N n = N.splitImage.constantGroup.sectionPoint (e.symm (q n))

end RelativeLabels

end

end LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer
