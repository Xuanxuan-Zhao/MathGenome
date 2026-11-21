import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.StableCartanVoganData
import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Complement

/-! LA-J06, Lie volume, lines 4867–4953. A compact automorphism is written
as its complex-linear extension, commuting with the compact conjugation. -/

universe u v

namespace Specs.LieAlgebrasAndRepresentations.VoganEquivalence

open _root_.LieAlgebrasAndRepresentations.RealForms
open PolarRealStructures StableCartanVoganData

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

/-- A product in the connected inner group of the fixed compact algebra,
acting on the ambient complex Lie algebra. -/
def FixedInnerProduct (ω : Conjugation L) (a g : L ≃ₗ⁅ℂ⁆ L) : Prop :=
  ∃ xs : List L, (∀ x ∈ xs, ω.map x = x ∧ a x = x) ∧
    g.toLinearMap = (xs.map CartanConjugacy.exponentialOperator).prod

/-- For different choices of stable Cartan the normalizer criterion uses a
transporter from the first Cartan to the second. -/
def CartanConjugates (ω : Conjugation L) (a b : L ≃ₗ⁅ℂ⁆ L)
    (H K : LieSubalgebra ℂ L) : Prop :=
  ∃ g : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω g ∧
    (∀ x, b (g x) = g (a x)) ∧ H.map g.toLieHom = K

def cartanAdjustmentType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (a b : L ≃ₗ⁅ℂ⁆ L), Function.Involutive a → Function.Involutive b →
    Intertwines ω ω a → Intertwines ω ω b →
    ∀ (H K : LieSubalgebra ℂ L), StableCartan ω a H → StableCartan ω b K →
    ∀ g : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω g → (∀ x, b (g x) = g (a x)) →
    ∃ c : L ≃ₗ⁅ℂ⁆ L, FixedInnerProduct ω b c ∧ Intertwines ω ω c ∧
      (∀ x, b (c x) = c (b x)) ∧ H.map (g.trans c).toLieHom = K

def realFormsIffCartanConjugatesType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (a b : L ≃ₗ⁅ℂ⁆ L)
      (ha : Function.Involutive a) (hb : Function.Involutive b)
      (hwa : Intertwines ω ω a) (hwb : Intertwines ω ω b)
      (H K : LieSubalgebra ℂ L),
    StableCartan ω a H → StableCartan ω b K →
    (Nonempty ((involutionConjugation ω a hwa ha).fixed ≃ₗ⁅ℝ⁆
      (involutionConjugation ω b hwb hb).fixed) ↔ CartanConjugates ω a b H K)

open SerreRelations (simple)
open VermaModules (Direction Regular)
open IntegrableHighestWeightQuotient (Normalized)

/-- Every tuple of unit phases on the simple root vectors is realized by an
adjoint exponential of an element of the compact Cartan. -/
def torusCoordinatesType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L) (H : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H → (∀ h ∈ H, ω.map h ∈ H) →
    ∀ (φ : Direction H), Regular H φ →
    ∀ (e f : simple H φ → L), Normalized H φ e f →
    (∀ i, ω.map (e i) = -f i) →
    ∀ z : simple H φ → Circle,
    ∃ h : H, ω.map (h : L) = (h : L) ∧
      ∃ t : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω t ∧
        t.toLinearMap = CartanConjugacy.exponentialOperator (h : L) ∧
        (∀ h' : H, t (h' : L) = (h' : L)) ∧
        (∀ i, t (e i) = (z i : ℂ) • e i ∧
          t (f i) = ((z i : ℂ)⁻¹) • f i)

/-- The kernel of the compact normalizer's root action is precisely
the group of adjoint exponentials from the compact Cartan. -/
def torusKernelType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L) (H : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H → (∀ h ∈ H, ω.map h ∈ H) →
    ∀ (φ : Direction H), Regular H φ →
    ∀ (e f : simple H φ → L), Normalized H φ e f →
    (∀ i, ω.map (e i) = -f i) →
    ∀ g : L ≃ₗ⁅ℂ⁆ L,
      (Intertwines ω ω g ∧ ∀ h : H, g (h : L) = (h : L)) ↔
      ∃ h : H, ω.map (h : L) = (h : L) ∧
        g.toLinearMap = CartanConjugacy.exponentialOperator (h : L)

variable {ι : Type v}

/-- Change of multipliers by a compact diagonal automorphism on the
simple root vectors, using the conjugation convention t⁻¹ a t. -/
noncomputable def multiplierGauge (σ : ι ≃ ι) (z m : ι → Circle) (j : ι) : Circle :=
  z j / z (σ j) * m j

def normalizeMultipliersType : Prop :=
  ∀ {ι : Type v} (σ : ι ≃ ι), Function.Involutive σ →
    ∀ m n : ι → Circle,
    (∀ j, m (σ j) = (m j)⁻¹) → (∀ j, n (σ j) = (n j)⁻¹) →
    ((∃ z, multiplierGauge σ z m = n) ↔ ∀ j, σ j = j → m j = n j)

/-- Given the same root action, comparison of fixed vertex multipliers is
equivalent to conjugacy by an actual element of the compact torus. -/
def torusConjugacyType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L) (H : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H → (∀ h ∈ H, ω.map h ∈ H) →
    ∀ (φ : Direction H), Regular H φ →
    ∀ (e f : simple H φ → L), Normalized H φ e f →
    (∀ i, ω.map (e i) = -f i) →
    ∀ (a b : L ≃ₗ⁅ℂ⁆ L) (σ : simple H φ ≃ simple H φ), Function.Involutive σ →
    ∀ m n : simple H φ → Circle,
    (∀ j, m (σ j) = (m j)⁻¹) → (∀ j, n (σ j) = (n j)⁻¹) →
    (∀ i, a (e i) = (m i : ℂ) • e (σ i) ∧
      a (f i) = ((m i : ℂ)⁻¹) • f (σ i) ∧
      a (RootForm.coroot_value H i.val : L) = (RootForm.coroot_value H (σ i).val : L)) →
    (∀ i, b (e i) = (n i : ℂ) • e (σ i) ∧
      b (f i) = ((n i : ℂ)⁻¹) • f (σ i) ∧
      b (RootForm.coroot_value H i.val : L) = (RootForm.coroot_value H (σ i).val : L)) →
    ((∀ j, σ j = j → m j = n j) ↔
      ∃ t : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω t ∧ (∀ h : H, t (h : L) = (h : L)) ∧
        ∀ x, a (t x) = t (b x))

/-- A sign with exponent in the additive group of integers modulo two. -/
def colorSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

/-- The Cartan matrix convention is aᵢⱼ = αⱼ(hᵢ). -/
def reflectedColors (A : Matrix ι ι ℤ) (i : ι) (b : ι → ZMod 2) (j : ι) : ZMod 2 :=
  b j - (A i j : ZMod 2) * b i

def colorParityType : Prop :=
  ∀ {ι : Type v} (A : Matrix ι ι ℤ) (i j : ι) (b : ι → ZMod 2),
    colorSign (reflectedColors A i b j) =
      colorSign (b j) * colorSign (b i) ^ (-A i j) ∧
    (reflectedColors A i b j ≠ b j ↔ b i = 1 ∧ Odd (A i j))

section RootTransport

open Module (Dual)
open RootDecomposition (rootSet_value)
open RootForm (coroot_value)

/-- The root map of a Cartan transporter is pullback along its inverse. -/
def transportRoots {H K : LieSubalgebra ℂ L} (g : L ≃ₗ⁅ℂ⁆ L)
    (hg : H.map g.toLieHom = K) : Dual ℂ H ≃ₗ[ℂ] Dual ℂ K :=
  (g.ofSubalgebras H K hg).toLinearEquiv.symm.dualMap

/-- Root-system isomorphisms in the complexified duals of the Cartans.
The coroot pairing is the usual integral pairing of the root system. -/
structure RootIsom (H K : LieSubalgebra ℂ L) where
  linear : Dual ℂ H ≃ₗ[ℂ] Dual ℂ K
  roots : ∀ α, linear α ∈ rootSet_value K ↔ α ∈ rootSet_value H
  pairing : ∀ α ∈ rootSet_value H, ∀ β ∈ rootSet_value H,
    linear β (coroot_value K (linear α)) = β (coroot_value H α)

/-- A compact lift of a specified root-system isomorphism. -/
def CompactRootLift (ω : Conjugation L) {H K : LieSubalgebra ℂ L}
    (r : RootIsom H K) (g : L ≃ₗ⁅ℂ⁆ L) : Prop :=
  Intertwines ω ω g ∧ ∃ hg : H.map g.toLieHom = K, transportRoots g hg = r.linear

def compactRootLiftsType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (H K : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H → MaximalTori.IsMaximalToral_value K →
    (∀ x ∈ H, ω.map x ∈ H) → (∀ x ∈ K, ω.map x ∈ K) →
    ∀ (φ : Direction K), Regular K φ →
    Finite (RootIsom H K) ∧ ∀ r : RootIsom H K,
      ∃ g, CompactRootLift ω r g

end RootTransport

section FiniteTest

open RootDecomposition (rootSpace_value)

/-- The conditions checked for a lift: the prescribed simple-root permutation
and the multipliers at its fixed vertices. -/
def PassesRootTest {K : LieSubalgebra ℂ L} {φ : Direction K}
    (a b g : L ≃ₗ⁅ℂ⁆ L) (σ : Equiv.Perm (simple K φ)) (e : simple K φ → L) : Prop :=
  (∀ i, g (a (g.symm (e i))) ∈ rootSpace_value K (σ i).val) ∧
  (∀ i, σ i = i → g (a (g.symm (e i))) = b (e i))

/-- Each compact lift may be chosen independently. A root-system isomorphism
passes exactly when the conjugated action has the same simple-root permutation
and agrees on every fixed simple root line. -/
def finiteEquivalenceTestType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (a b : L ≃ₗ⁅ℂ⁆ L)
      (ha : Function.Involutive a) (hb : Function.Involutive b)
      (hwa : Intertwines ω ω a) (hwb : Intertwines ω ω b)
      (H K : LieSubalgebra ℂ L),
    StableCartan ω a H → ∀ hK : StableCartan ω b K,
    ∀ (z : K), PositiveOrder ω b K hK z →
    ∀ (e f : simple K (evaluation K z) → L),
    Normalized K (evaluation K z) e f → (∀ i, ω.map (e i) = -f i) →
    ∀ (σ : Equiv.Perm (simple K (evaluation K z))),
      Function.Involutive σ →
      (∀ i, rootAction b K hK.stable i.val = (σ i).val) →
    Finite (RootIsom H K) ∧
    (∃ lift : RootIsom H K → L ≃ₗ⁅ℂ⁆ L, ∀ r, CompactRootLift ω r (lift r)) ∧
    ∀ lift : RootIsom H K → L ≃ₗ⁅ℂ⁆ L,
      (∀ r, CompactRootLift ω r (lift r)) →
      (Nonempty ((involutionConjugation ω a hwa ha).fixed ≃ₗ⁅ℝ⁆
          (involutionConjugation ω b hwb hb).fixed) ↔
        ∃ r, PassesRootTest a b (lift r) σ e)

end FiniteTest

section InnerCharacters

open Module (Dual)
open RootDecomposition (rootSet_value rootSpace_value)

/-- The integral lattice generated by the roots in the complex Cartan dual. -/
abbrev voganRootLattice (H : LieSubalgebra ℂ L) :=
  Submodule.span ℤ (rootSet_value H)

def latticeRoot {H : LieSubalgebra ℂ L} (α : rootSet_value H) :
    voganRootLattice H :=
  ⟨α, Submodule.subset_span α.property⟩

def latticeSimple {H : LieSubalgebra ℂ L} {φ : Direction H} (i : simple H φ) :
    voganRootLattice H :=
  latticeRoot ⟨i.val, i.property.1.1⟩

/-- These characters use the additive model of the two signs, identified by
`colorSign` with the values +1 and -1. -/
abbrev SignCharacter (H : LieSubalgebra ℂ L) :=
  voganRootLattice H →+ ZMod 2

/-- For inner Vogan data the character on a root gives the scalar by which
the involution acts on its entire root line. -/
def RealizesCharacter (H : LieSubalgebra ℂ L) (a : L ≃ₗ⁅ℂ⁆ L)
    (χ : SignCharacter H) : Prop :=
  ∀ (α : rootSet_value H) (x : L), x ∈ rootSpace_value H α →
    a x = colorSign (χ (latticeRoot α)) • x

def rootLatticeBasisType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Direction H), Regular H φ →
    ∃ q : Module.Basis (simple H φ) ℤ (voganRootLattice H),
      ∀ i, q i = latticeSimple i

def signCharacterCoordinatesType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Direction H), Regular H φ →
    ∃ e : SignCharacter H ≃ (simple H φ → ZMod 2),
      ∀ χ i, e χ i = χ (latticeSimple i)

def innerCharactersType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L) (H : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H → (∀ h ∈ H, ω.map h ∈ H) →
    ∀ (φ : Direction H), Regular H φ →
    ∀ (e f : simple H φ → L), Normalized H φ e f →
    (∀ i, ω.map (e i) = -f i) →
    (∀ a : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω a → Function.Involutive a →
      (∀ h : H, a (h : L) = (h : L)) →
      ∃! χ : SignCharacter H, RealizesCharacter H a χ) ∧
    (∀ χ : SignCharacter H, ∃! a : L ≃ₗ⁅ℂ⁆ L,
      Intertwines ω ω a ∧ Function.Involutive a ∧
      (∀ h : H, a (h : L) = (h : L)) ∧ RealizesCharacter H a χ)

variable {H K : LieSubalgebra ℂ L}

/-- Restriction of the complex root map to the integral spans of the roots. -/
def latticeTransport (r : RootIsom H K) : voganRootLattice H ≃ₗ[ℤ] voganRootLattice K where
  toFun x := ⟨r.linear x, by
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ x.property
    · intro α hα
      exact Submodule.subset_span ((r.roots α).2 hα)
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro n x _ hx
      rw [map_zsmul]
      exact Submodule.smul_mem _ n hx⟩
  invFun y := ⟨r.linear.symm y, by
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ y.property
    · intro β hβ
      exact Submodule.subset_span ((r.roots _).1 (by simpa using hβ))
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro n x _ hx
      rw [map_zsmul]
      exact Submodule.smul_mem _ n hx⟩
  left_inv x := Subtype.ext (r.linear.symm_apply_apply x)
  right_inv y := Subtype.ext (r.linear.apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add r.linear x.val y.val)
  map_smul' n x := Subtype.ext (map_zsmul r.linear n x.val)

/-- The left action on characters is pullback by the inverse root map. -/
def transportCharacter (r : RootIsom H K) (χ : SignCharacter H) : SignCharacter K :=
  χ.comp (latticeTransport r).symm.toLinearMap.toAddMonoidHom

def innerCharacterTransportType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    ∀ (ω : Conjugation L) (H K : LieSubalgebra ℂ L)
      (r : RootIsom H K) (g a : L ≃ₗ⁅ℂ⁆ L) (χ : SignCharacter H),
    CompactRootLift ω r g → RealizesCharacter H a χ →
    RealizesCharacter K ((g.symm.trans a).trans g) (transportCharacter r χ)

def innerReflectionType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Direction H) (A : Matrix (simple H φ) (simple H φ) ℤ) (i : simple H φ),
    (∀ j, j.val (RootForm.coroot_value H i.val) = (A i j : ℂ)) →
    ∃ r : RootIsom H H,
      (∀ β, r.linear β = RootStrings.reflection_value H i.val β) ∧
      ∀ (χ : SignCharacter H) (j : simple H φ),
        transportCharacter r χ (latticeSimple j) =
          reflectedColors A i (fun k => χ (latticeSimple k)) j

/-- The character orbit criterion for inner Vogan data, also for data
initially based at different stable compact Cartans. -/
def innerCharacterOrbitType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (a b : L ≃ₗ⁅ℂ⁆ L)
      (ha : Function.Involutive a) (hb : Function.Involutive b)
      (hwa : Intertwines ω ω a) (hwb : Intertwines ω ω b)
      (H K : LieSubalgebra ℂ L),
    StableCartan ω a H → StableCartan ω b K →
    (∀ h : H, a (h : L) = (h : L)) → (∀ h : K, b (h : L) = (h : L)) →
    ∀ (φ : Direction K), Regular K φ →
    ∀ (χ : SignCharacter H) (ψ : SignCharacter K),
    RealizesCharacter H a χ → RealizesCharacter K b ψ →
    (Nonempty ((involutionConjugation ω a hwa ha).fixed ≃ₗ⁅ℝ⁆
      (involutionConjugation ω b hwb hb).fixed) ↔
      ∃ r : RootIsom H K, transportCharacter r χ = ψ)

end InnerCharacters

section InnerWeyl

open Module (Dual)
open RootDecomposition (rootSet_value)
open RootForm (coroot_value)
open SerreRelations (positive)

variable (H : LieSubalgebra ℂ L)

/-- The group of linear automorphisms of the Cartan dual preserving roots
and their coroot pairings. -/
def rootAutomorphisms : Subgroup (Dual ℂ H ≃ₗ[ℂ] Dual ℂ H) where
  carrier := {g | (∀ α, g α ∈ rootSet_value H ↔ α ∈ rootSet_value H) ∧
    (∀ α ∈ rootSet_value H, ∀ β ∈ rootSet_value H,
      g β (coroot_value H (g α)) = β (coroot_value H α))}
  one_mem' := ⟨fun _ => Iff.rfl, fun _ _ _ _ => rfl⟩
  mul_mem' {g k} hg hk := by
    refine ⟨fun α => (hg.1 (k α)).trans (hk.1 α), fun α hα β hβ => ?_⟩
    exact (hg.2 (k α) ((hk.1 α).2 hα) (k β) ((hk.1 β).2 hβ)).trans (hk.2 α hα β hβ)
  inv_mem' {g} hg := by
    change (∀ α, g.symm α ∈ rootSet_value H ↔ α ∈ rootSet_value H) ∧ _
    have hex (α : Dual ℂ H) := hg.1 (g.symm α)
    have hs (α : Dual ℂ H) : g.symm α ∈ rootSet_value H ↔ α ∈ rootSet_value H := by
      simpa using (hg.1 (g.symm α)).symm
    refine ⟨hs, fun α hα β hβ => ?_⟩
    change g.symm β (coroot_value H (g.symm α)) = β (coroot_value H α)
    simpa using (hg.2 (g.symm α) ((hs α).2 hα) (g.symm β) ((hs β).2 hβ)).symm

def asRootIsom (g : rootAutomorphisms H) : RootIsom H H :=
  ⟨g.val, g.property.1, g.property.2⟩

/-- The same pullback action on root characters, viewed as a left group action. -/
instance : MulAction (rootAutomorphisms H) (SignCharacter H) where
  smul g χ := transportCharacter (asRootIsom H g) χ
  one_smul χ := by
    ext α
    change χ ((latticeTransport (asRootIsom H 1)).symm α) = χ α
    exact congrArg χ (Subtype.ext rfl)
  mul_smul g k χ := by
    ext α
    change χ ((latticeTransport (asRootIsom H (g * k))).symm α) =
      χ ((latticeTransport (asRootIsom H k)).symm ((latticeTransport (asRootIsom H g)).symm α))
    exact congrArg χ (Subtype.ext rfl)

/-- The Weyl subgroup generated by all ordinary root reflections. -/
def voganWeylGroup : Subgroup (rootAutomorphisms H) :=
  Subgroup.closure {g | ∃ α ∈ rootSet_value H, ∀ β,
    g.val β = RootStrings.reflection_value H α β}

/-- The complement preserves the given positive system and hence the full
Dynkin diagram. -/
def positiveRootStabilizer (φ : Direction H) : Subgroup (rootAutomorphisms H) where
  carrier := {g | ∀ α, g.val α ∈ positive H φ ↔ α ∈ positive H φ}
  one_mem' := fun _ => Iff.rfl
  mul_mem' {g k} hg hk := fun α => (hg (k.val α)).trans (hk α)
  inv_mem' {g} hg := by
    intro α
    change g.val.symm α ∈ positive H φ ↔ α ∈ positive H φ
    simpa using (hg (g.val.symm α)).symm

def weylDiagramDecompositionType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Direction H), Regular H φ →
      (voganWeylGroup H).Normal ∧ (voganWeylGroup H).IsComplement' (positiveRootStabilizer H φ)

end InnerWeyl

section PositiveDiagram

open Module (Dual)
open SerreRelations (simple)
open VermaModules (Direction Regular)
open AutomorphismDecomposition (diagramAutomorphisms)

/-- Restricting to the simple roots identifies the positive-system stabilizer
with the automorphism group of the full oriented Dynkin diagram. -/
def positiveRootStabilizerIsDynkinType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Direction H), Regular H φ →
      ∃ e : positiveRootStabilizer H φ ≃* diagramAutomorphisms H φ,
        ∀ g i, ((e g).val i).val = g.val.val i.val

end PositiveDiagram

section OuterReflection

open RootDecomposition (rootSet_value)
open RootStrings (reflection_value)

/-- Reflecting at a fixed simple root, and renormalizing any paired generators,
gives the indicated sign change on the same invariant positive system. -/
def outerReflectionType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (a : L ≃ₗ⁅ℂ⁆ L), Function.Involutive a → Intertwines ω ω a →
    ∀ (H : LieSubalgebra ℂ L) (hH : StableCartan ω a H)
      (φ : Direction H), Regular H φ →
    ∀ (e f : simple H φ → L), Normalized H φ e f →
    (∀ j, ω.map (e j) = -f j) →
    ∀ (A : Matrix (simple H φ) (simple H φ) ℤ) (d : DiagramData A),
    (∀ j k, (A j k : ℂ) = k.val (RootForm.coroot_value H j.val)) →
    (∀ j, (d.perm j).val = rootAction a H hH.stable j.val) →
    (∀ j, a (e j) = d.sign j • e (d.perm j) ∧
      a (f j) = d.sign j • f (d.perm j) ∧
      a (RootForm.coroot_value H j.val : L) = (RootForm.coroot_value H (d.perm j).val : L)) →
    ∀ i : simple H φ, d.perm i = i →
    ∃ (n : L ≃ₗ⁅ℂ⁆ L) (hn : H.map n.toLieHom = H),
      Intertwines ω ω n ∧
      (∀ α, transportRoots n hn α = reflection_value H i.val α) ∧
      ∃ b : L ≃ₗ⁅ℂ⁆ L, (∀ x, b (n x) = n (a x)) ∧
        (∀ h : H, b (h : L) = a (h : L)) ∧
        Intertwines ω ω b ∧ Function.Involutive b ∧
        ∃ (d' : DiagramData A) (e' f' : simple H φ → L),
          d'.perm = d.perm ∧ Normalized H φ e' f' ∧
          (∀ j, ω.map (e' j) = -f' j) ∧
          (∀ j, d.perm j = j →
            d'.sign j = d.sign j * d.sign i ^ (-A i j) ∧
            (d'.sign j ≠ d.sign j ↔ d.sign i = -1 ∧ Odd (A i j))) ∧
          (∀ j, b (e' j) = d'.sign j • e' (d'.perm j) ∧
            b (f' j) = d'.sign j • f' (d'.perm j) ∧
            b (RootForm.coroot_value H j.val : L) = (RootForm.coroot_value H (d'.perm j).val : L))

end OuterReflection

section InnerSemidirectProduct

open VermaModules (Direction Regular)
open AutomorphismDecomposition (diagramAutomorphisms)

/-- The diagram acts on the Weyl subgroup by conjugation inside root
automorphisms, using its lift fixing the positive system. -/
def weylDiagramAction {H : LieSubalgebra ℂ L} {φ : Direction H}
    (hN : (voganWeylGroup H).Normal)
    (e : positiveRootStabilizer H φ ≃* diagramAutomorphisms H φ) :
    diagramAutomorphisms H φ →* MulAut (voganWeylGroup H) := by
  letI := hN
  let s := (positiveRootStabilizer H φ).subtype.comp e.symm.toMonoidHom
  let lift : rootAutomorphisms H →*
      Subgroup.normalizer (voganWeylGroup H : Set (rootAutomorphisms H)) :=
    { toFun := fun g => ⟨g, by rw [(voganWeylGroup H).normalizer_eq_top]; trivial⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (voganWeylGroup H).normalizerMonoidHom.comp (lift.comp s)

/-- The external semidirect product maps to root automorphisms by multiplying
the Weyl element by the lift that preserves the positive system. Its action
on root-lattice signs is pullback along this automorphism's inverse. -/
def innerSemidirectProductType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Direction H), Regular H φ →
    ∃ (hN : (voganWeylGroup H).Normal)
      (e : positiveRootStabilizer H φ ≃* diagramAutomorphisms H φ),
      (∀ g i, ((e g).val i).val = g.val.val i.val) ∧
      ∃ I : (voganWeylGroup H ⋊[weylDiagramAction hN e] diagramAutomorphisms H φ) ≃*
          rootAutomorphisms H,
        (∀ x, I x = x.left.val * (e.symm x.right).val) ∧
        ∀ x (χ : SignCharacter H),
          I x • χ = x.left.val • ((e.symm x.right).val • χ)

end InnerSemidirectProduct

section InnerWeylDiagramOrbits

open AutomorphismDecomposition (diagramAutomorphisms)

/-- For one Cartan the orbit of an inner character is the orbit under the
Weyl group and the full Dynkin diagram group. -/
def innerWeylDiagramOrbitType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (a b : L ≃ₗ⁅ℂ⁆ L)
      (ha : Function.Involutive a) (hb : Function.Involutive b)
      (hwa : Intertwines ω ω a) (hwb : Intertwines ω ω b)
      (H : LieSubalgebra ℂ L),
    StableCartan ω a H → StableCartan ω b H →
    (∀ h : H, a (h : L) = (h : L)) → (∀ h : H, b (h : L) = (h : L)) →
    ∀ (φ : Direction H), Regular H φ →
    ∃ e : positiveRootStabilizer H φ ≃* diagramAutomorphisms H φ,
      (∀ g i, ((e g).val i).val = g.val.val i.val) ∧
      ∀ (χ ψ : SignCharacter H),
        RealizesCharacter H a χ → RealizesCharacter H b ψ →
        (Nonempty ((involutionConjugation ω a hwa ha).fixed ≃ₗ⁅ℝ⁆
          (involutionConjugation ω b hwb hb).fixed) ↔
          ∃ (w : voganWeylGroup H) (p : diagramAutomorphisms H φ),
            w.val • ((e.symm p).val • χ) = ψ)

end InnerWeylDiagramOrbits

end Specs.LieAlgebrasAndRepresentations.VoganEquivalence
