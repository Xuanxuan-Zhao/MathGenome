import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding

open AlgebraicGeometry CategoryTheory Opposite
open scoped WithZero TensorProduct CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalFaceCongruence

open AdjointRepresentation (GroupPoints)
open ExceptionalAffineBruhat ExceptionalAffineBuilding ExceptionalIwahoriCongruence
open ExceptionalAffineRootSystems (FoldedRootDirection IsLongF4Doubled e6Partner)
open ExceptionalLocalRootCoordinates (normalizedValuation ramificationIndex residueMap)
open ExceptionalValuedTorusNormalizer (invariantApartment)
open IntegralSemisimpleModel
open Pinning (BasedRootDatum)
open IsLocalRing
attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

universe u

noncomputable section

local notation "O(" K ")" => Valuation.valuationSubring (ValuativeRel.valuation K)
local notation "κ(" K ")" => IsLocalRing.ResidueField (O(K))

/-- Data at the fixed finite coefficient level, including the chosen scaling
and its already integral realization on the marked parahoric. -/
structure ScaledFace
    {F L k : Type u} [Field F] [Field L] [Field k]
    [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {σ : Gal(L/F)} (T : DiagramCompositum F L k σ) {A : FoldedApartment (R.diagram σ)}
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
    (J : Set (A.roots.SimpleWall A.basepoint)) (x : invariantApartment D (R.diagram σ)) where
  E : Type u
  [field : Field E]
  [algebra : Algebra T.field E]
  [valuation : ValuativeRel E]
  [topology : TopologicalSpace E]
  [localField : IsNonarchimedeanLocalField E]
  [finite : FiniteDimensional T.field E]
  [extension : ValuativeExtension T.field E]
  d : ℕ
  d_pos : 0 < d
  uniformizer : Lˣ
  uniformizer_value : normalizedValuation L (uniformizer : L) = WithZero.exp (-1 : ℤ)
  xi : O(E)
  xi_uniformizer : (ValuativeRel.valuation E).IsUniformizer (xi : E)
  xi_power : (xi : E) ^ d = algebraMap T.field E (algebraMap L T.field (uniformizer : L))
  unchanged_residue : Nat.card κ(E) = Nat.card κ(T.field)
  cocharacter : D.Y
  cocharacter_eq : (1 : ℚ) ⊗ₜ[ℤ] cocharacter = (2 * (d : ℚ)) • x.val
  coefficient : Gal(k/F) →* (E ≃+* E)
  coefficient_extends (g : Gal(k/F)) (z : T.field) :
    coefficient g (algebraMap T.field E z) = algebraMap T.field E (T.coefficient g z)
  coefficient_fixes_xi (g : Gal(k/F)) : coefficient g (xi : E) = xi
  integralCoefficient : Gal(k/F) →* (O(E) ≃+* O(E))
  integralCoefficient_eq (g : Gal(k/F)) (z : O(E)) :
    (integralCoefficient g z : E) = coefficient g (z : E)
  action : Gal(k/F) →* MulAut (parahoric X.comparison J)
  action_eq (g : Gal(k/F)) (h : parahoric X.comparison J) :
    ((action g h : parahoric X.comparison J) : GroupPoints R.descent.group.val (CommAlgCat.of F k)) =
      coefficientPoints R.descent.group.val g.toAlgHom h
  point : parahoric X.comparison J →* IntegralPoints M.group (localIntegers E)
  point_eq (h : parahoric X.comparison J) :
    changeRingHom M.group (localIntegersInclusion E) (point h) =
      MulAut.conj
        (torusPoint D (integralRing E)
          (IntegralSemisimpleModel.cocharacter D cocharacter (integralRing E)
            (Units.mk0 (xi : E) xi_uniformizer.ne_zero)) ≫ M.torus.hom.hom)
        (scalarPoints M (algebraMap T.field E) (X.points h))
  point_equivariant (g : Gal(k/F)) (h : parahoric X.comparison J) :
    point (action g h) = changeRingHom M.group (integralRingMap (integralCoefficient g).toRingHom)
      (point h)

attribute [instance] ScaledFace.field ScaledFace.algebra ScaledFace.valuation
  ScaledFace.topology ScaledFace.localField ScaledFace.finite ScaledFace.extension

section Layer

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {σ : Gal(L/F)} {T : DiagramCompositum F L k σ} {A : FoldedApartment (R.diagram σ)}
    {X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A}
    {J : Set (A.roots.SimpleWall A.basepoint)} {x : invariantApartment D (R.diagram σ)}

/-- The depth is indexed by powers of the auxiliary maximal ideal, and uses
the same scaled integral point at every depth. -/
def congruenceSubgroup (S : ScaledFace T X J x) (n : ℕ) :
    Subgroup (parahoric X.comparison J) :=
  ((changeRingHom M.group (congruenceHom (localIntegers S.E) n)).comp S.point).ker

/-- When the entry is at depth at least n its leading coefficient is obtained
by dividing by the nth power of the auxiliary uniformizer and reducing. -/
def IsLeading (S : ScaledFace T X J x) (n : ℕ) (entry : O(S.E)) (r : κ(S.E)) : Prop :=
  ∃ w : O(S.E), entry = S.xi ^ n * w ∧ residue _ w = r

/-- An absolute chart tuple over the auxiliary valuation ring obeys the
congruence conditions at depth n. Torus entries are measured from one. -/
def CellDepth (S : ScaledFace T X J x)
    (n : ℕ) (z : CellValues D (localIntegers S.E) X.comparison.chart.negative
      X.comparison.chart.positive) : Prop :=
  (∀ i, z.1 i ∈ maximalIdeal O(S.E) ^ n) ∧
    (∀ χ, (z.2.1 χ : O(S.E)) - 1 ∈ maximalIdeal O(S.E) ^ n) ∧
    ∀ i, z.2.2 i ∈ maximalIdeal O(S.E) ^ n

/-- An unscaled tuple and an integral scaled tuple use the same marked root
coordinates and are related by the fixed cocharacter. -/
def ScaledCoordinates (S : ScaledFace T X J x)
    (z : CellValues D (integralRing T.field) X.comparison.chart.negative
      X.comparison.chart.positive)
    (w : CellValues D (localIntegers S.E) X.comparison.chart.negative
      X.comparison.chart.positive) : Prop :=
  mapCellValues (localIntegersInclusion S.E) w =
    scaleCellValues
      (IntegralSemisimpleModel.cocharacter D S.cocharacter (integralRing S.E)
        (Units.mk0 (S.xi : S.E) S.xi_uniformizer.ne_zero))
      (mapCellValues (integralRingMap (algebraMap T.field S.E)) z)

/-- A representative of each diagram orbit in the standard simple numbering. -/
abbrev TorusOrbits := {i : Fin 6 // i ≤ e6Partner i}

def rootShift (S : ScaledFace T X J x) (a : FoldedRootDirection) : ℤ :=
  D.datum.toLinearMap (D.datum.root ((A.surjective a).choose)) S.cocharacter

def rootStep (S : ScaledFace T X J x) (a : FoldedRootDirection) : ℤ :=
  (S.d : ℤ) * (if IsLongF4Doubled a.val then 2 else 1)

def torusStep (S : ScaledFace T X J x) (a : TorusOrbits) : ℤ :=
  (S.d : ℤ) * (if a.val = e6Partner a.val then 2 else 1)

/-- Each active orbit contributes one residue line. -/
def ActiveSlot (S : ScaledFace T X J x) (n : ℕ) :=
  {a : FoldedRootDirection ⊕ TorusOrbits //
    match a with
    | .inl j => ∃ m : ℤ, (n : ℤ) = rootShift S j + rootStep S j * m
    | .inr i => ∃ m : ℤ, (n : ℤ) = torusStep S i * m}

abbrev LayerVectors (S : ScaledFace T X J x) (n : ℕ) := ActiveSlot S n → κ(S.E)

def torusOrbit (i : Fin 6) : TorusOrbits :=
  ⟨min i (e6Partner i), by fin_cases i <;> decide⟩

def slotValue (S : ScaledFace T X J x) (n : ℕ) (v : LayerVectors S n)
    (a : FoldedRootDirection ⊕ TorusOrbits) : κ(S.E) := by
  classical
  exact if h : ∃ i : ActiveSlot S n, i.val = a then v h.choose else 0

def residueAction (S : ScaledFace T X J x) (g : Gal(k/F)) : κ(S.E) →+* κ(S.E) :=
  let e := S.integralCoefficient g
  letI := IsLocalHom.of_surjective e.toRingHom e.surjective
  ResidueField.map e.toRingHom

/-- The canonical residue field maps transport the coefficient action from
the given unramified field-to-residue Galois comparison. -/
def ResidueComparison (S : ScaledFace T X J x) [ValuativeRel F]
    [ValuativeExtension F k] (galResidue : Gal(k/F) ≃* Gal(κ(k)/κ(F))) : Prop :=
  ∃ (i : κ(k) ≃+* κ(T.field)) (j : κ(T.field) ≃+* κ(S.E)),
    i.toRingHom = residueMap k T.field ∧ j.toRingHom = residueMap T.field S.E ∧
    ∀ (g : Gal(k/F)) (r : κ(k)),
      residueAction S g (j (i r)) = j (i (galResidue g r))

/-- Each line is read at one absolute root slot or at the representative
simple character of a torus orbit. The other entries have fixed unit factors. -/
def leadingMapComparison (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (n : ℕ) (red : congruenceSubgroup S n →* Multiplicative (LayerVectors S n)) : Prop :=
  let C := X.comparison.chart
  ∃ (negativeFactor : Fin C.negative.length → κ(S.E)ˣ)
    (positiveFactor : Fin C.positive.length → κ(S.E)ˣ)
    (torusFactor : Fin 6 → κ(S.E)ˣ),
    (∀ a : FoldedRootDirection,
      (∃ i : Fin C.negative.length, A.direction C.negative[i] = a ∧ negativeFactor i = 1) ∨
      (∃ i : Fin C.positive.length, A.direction C.positive[i] = a ∧ positiveFactor i = 1)) ∧
    (∀ a : TorusOrbits, torusFactor a.val = 1) ∧
    ∀ (g : congruenceSubgroup S n) (w : CellValues D (localIntegers S.E) C.negative C.positive),
      cellValue M.toIntegralMarking (localIntegers S.E) C.negative C.positive w = S.point (g : _) →
      (∀ i : Fin C.negative.length, IsLeading S n (w.1 i)
        (negativeFactor i * slotValue S n (red g).toAdd (.inl (A.direction C.negative[i])))) ∧
      (∀ i : Fin C.positive.length, IsLeading S n (w.2.2 i)
        (positiveFactor i * slotValue S n (red g).toAdd (.inl (A.direction C.positive[i])))) ∧
      ∀ i : Fin 6,
        IsLeading S n ((w.2.1 (Multiplicative.ofAdd (D.datum.root (b i).val)) : O(S.E)) - 1)
          (torusFactor i * slotValue S n (red g).toAdd (.inr (torusOrbit i)))

def ScaledFace.Layers (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support) : Prop :=
  let C := X.comparison.chart
  (∀ n, 0 < n → ∀ (g : GroupPoints R.descent.group.val (CommAlgCat.of F k)),
    (∃ hp : g ∈ parahoric X.comparison J, (⟨g, hp⟩ : parahoric X.comparison J) ∈ congruenceSubgroup S n) ↔
      ∃! z : CellValues D (integralRing T.field) C.negative C.positive,
        cellValue M.toIntegralMarking (integralRing T.field) C.negative C.positive z = X.points g ∧
        ∃ w, ScaledCoordinates S z w ∧ CellDepth S n w) ∧
  (∀ n, 0 < n → ∀ (g : parahoric X.comparison J),
    g ∈ congruenceSubgroup S n ↔
      ∃! w : CellValues D (localIntegers S.E) C.negative C.positive,
        cellValue M.toIntegralMarking (localIntegers S.E) C.negative C.positive w = S.point g ∧
        CellDepth S n w) ∧
  Antitone (congruenceSubgroup S) ∧
  (∀ g : parahoric X.comparison J, (∀ n, 0 < n → g ∈ congruenceSubgroup S n) → g = 1) ∧
  (∀ (B : IntegralAlgebra.{u}) [Algebra.FiniteType Integers.{u} B]
    (iso : integralSpec.obj (op B) ≅ M.group.X),
    letI := TopologicalSpace.induced X.points (markedPointTopology B iso T.field)
    IsCompact (parahoric X.comparison J : Set (GroupPoints R.descent.group.val (CommAlgCat.of F k))) ∧
    ∀ n, IsClosed (congruenceSubgroup S n : Set (parahoric X.comparison J))) ∧
  (∀ n, 0 < n →
    ∃ (stable : ∀ g (h : congruenceSubgroup S n), S.action g h ∈ congruenceSubgroup S n)
      (red : congruenceSubgroup S n →* Multiplicative (LayerVectors S n)),
      leadingMapComparison S b n red ∧ Function.Surjective red ∧
      (∀ h, red h = 1 ↔ (h : parahoric X.comparison J) ∈ congruenceSubgroup S (n + 1)) ∧
      (∀ g (h : congruenceSubgroup S n) i, (red ⟨S.action g h, stable g h⟩).toAdd i =
        residueAction S g ((red h).toAdd i)) ∧
      ∃ e : (congruenceSubgroup S n ⧸ red.ker) ≃* Multiplicative (LayerVectors S n),
        ∀ h, e (QuotientGroup.mk h) = red h) ∧
  ∀ a : Gal(k/F) → parahoric X.comparison J,
    (∀ g h, a (g * h) = a g * S.action g (a h)) →
    (∀ g, a g ∈ congruenceSubgroup S 1) →
    ∃ h : congruenceSubgroup S 1, ∀ g,
      a g = (h : parahoric X.comparison J) * (S.action g h)⁻¹

end Layer

/-- Congruence layers and higher cocycle correction at the fixed finite
unramified coefficient level of the ramified outer adjoint form. -/
def RamifiedFaceCongruenceLayers : Prop :=
  ∀ (F L k : Type u) [Field F] [Field L] [Field k]
    [Algebra F L] [Algebra F k] [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional F k] [IsGalois F k]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeExtension F k],
    IsUnramifiedLocalExtension F k →
    ∀ (σ : Gal(L/F)), Module.finrank F L = 2 → σ ≠ 1 → 1 < ramificationIndex F L →
    ∀ {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M)
      (b : Fin 6 ≃ D.base.support), ExceptionalNumbering D 6 b → D.datum.rootSpan ℤ = ⊤ →
    (∀ i, (R.diagram σ).val.indexEquiv (b i) = b (e6Partner i)) →
    ∀ (T : DiagramCompositum F L k σ) (A : FoldedApartment (R.diagram σ))
      (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A),
    X.Coefficients T →
    ∀ (Y : Building X.comparison) (J : Set (A.roots.SimpleWall A.basepoint)),
    J ≠ Set.univ →
    ∀ (x : invariantApartment D (R.diagram σ)) (t : Weights (A.roots.SimpleWall A.basepoint)),
    IsBarycenter J t → cotype t = J →
    rationalPoint Y.realization.coordinates x =
      simplexPoint Y.realization.coordinates Y.realization.vertex t →
    ∀ (S : ScaledFace T X J x)
      (galResidue : Gal(k/F) ≃* Gal(κ(k)/κ(F))),
    (∀ (g : Gal(k/F)) (z : O(k)) (w : O(k)), (w : k) = g (z : k) →
      galResidue g (residue _ z) = residue _ w) →
    S.Layers b ∧ ResidueComparison S galResidue

end
end LinearAlgebraicGroups.Specs.RamifiedExceptionalFaceCongruence
