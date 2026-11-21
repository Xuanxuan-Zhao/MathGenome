import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt

/-! HA-A08, notes/002/advanced-homological-algebra.tex:3273–3299.
The scalar ring is arbitrary, including the zero ring. The coefficient action
is restriction of the given left enveloping-algebra action. Quotients below
are explicit additive groups; cochains remain k-linear. -/
noncomputable section
open CategoryTheory P103.Specs.Ch10.Complexes

namespace AdvancedHomologicalAlgebra.CE.LowDegree
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]

/-- The degree-zero and degree-one coordinates use Λ⁰g=k and Λ¹g=g. -/
def zeroCoord : (W k g 0 →ₗ[k] M) ≃ₗ[k] M :=
  (LinearEquiv.arrowCongr (exteriorPower.zeroEquiv k g) (LinearEquiv.refl k M)).trans
    (LinearMap.ringLmapEquivSelf k k M)

def oneCoord : (W k g 1 →ₗ[k] M) ≃ₗ[k] (g →ₗ[k] M) :=
  LinearEquiv.arrowCongr (exteriorPower.oneEquiv k g) (LinearEquiv.refl k M)

/-- Vectors annihilated by every element of g. -/
def invariants : Submodule ℤ M where
  carrier := {m | ∀ x : g, Shared.Lie.inclusion k g x • m = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb x; simp only [smul_add, ha x, hb x, add_zero]
  smul_mem' := by intro n m hm x; rw [smul_comm, hm x, smul_zero]

/-- k-linear derivations with values in the given Lie module. -/
def derivations : Submodule ℤ (g →ₗ[k] M) where
  carrier := {f | ∀ x y, f ⁅x,y⁆ = Shared.Lie.inclusion k g x • f y -
    Shared.Lie.inclusion k g y • f x}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh x y
    simp only [LinearMap.add_apply, smul_add, hf x y, hh x y]
    abel
  smul_mem' := by
    intro n f hf x y
    simp only [LinearMap.smul_apply, hf x y, smul_sub]
    rw [smul_comm n, smul_comm n]

/-- Inner derivations, inside the actual submodule of derivations. -/
def inner : Submodule ℤ (derivations k g M) where
  carrier := {f | ∃ m : M, ∀ x, f.val x = Shared.Lie.inclusion k g x • m}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro f h ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m+n, by intro x; simpa [smul_add] using congrArg₂ (·+·) (hm x) (hn x)⟩
  smul_mem' := by
    rintro n f ⟨m, hm⟩
    refine ⟨n • m, ?_⟩
    intro x
    change n • f.val x = _
    rw [hm, smul_comm]

abbrev outer := derivations k g M ⧸ inner k g M

/-- A choice of coboundary has the full printed CE formula, in every degree. -/
def HasCochainFormula
    (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)) : Prop :=
  ∀ n f x, δ n f (wedge k g (n+1) x) =
    cochainActionSum k g M n f x + cochainBracketSum k g M n f x

/-- Both identifications are fixed on actual cohomology classes, so that
there is no arbitrary noncanonical choice of an abstract group isomorphism. -/
def Identifies
    (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
    (s : ∀ n, (δ (n+1)).comp (δ n) = 0)
    (e₀ : Homology (Ext.cochain k g M δ s) 0 ≃+ invariants k g M)
    (e₁ : Homology (Ext.cochain k g M δ s) 1 ≃+ outer k g M) : Prop :=
  (∀ z : cycles (Ext.cochain k g M δ s) 0,
    (e₀ (homologyClass _ 0 z)).val = zeroCoord k g M z.val) ∧
  (∀ z : cycles (Ext.cochain k g M δ s) 1,
    ∃ f : derivations k g M, f.val = oneCoord k g M z.val ∧
      e₁ (homologyClass _ 1 z) = (inner k g M).mkQ f)

end AdvancedHomologicalAlgebra.CE.LowDegree

namespace AdvancedHomologicalAlgebra.CE.LowDegree
universe u v w w'
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]
variable (N : Type w') [AddCommGroup N] [Module k N]
  [Module (U k g) N] [IsScalarTower k (U k g) N]

/-- The usual maps on invariant vectors and on derivations. -/
def invariantsMap (h : M →ₗ[U k g] N) : invariants k g M →ₗ[ℤ] invariants k g N where
  toFun m := ⟨h m.val, by
    intro x
    rw [← h.map_smul, m.property x, map_zero]⟩
  map_add' a b := Subtype.ext (h.map_add _ _)
  map_smul' n m := Subtype.ext (map_zsmul h _ _)

def derivationsMap (h : M →ₗ[U k g] N) : derivations k g M →ₗ[ℤ] derivations k g N where
  toFun f := ⟨(h.restrictScalars k).comp f.val, by
    intro x y
    change h (f.val ⁅x,y⁆) = _
    rw [f.property x y, map_sub, h.map_smul, h.map_smul]
    rfl⟩
  map_add' a b := by ext x; exact h.map_add _ _
  map_smul' n f := by ext x; exact map_zsmul h _ _

/-- Postcomposition descends through the actual inner-derivation submodule. -/
def outerMap (h : M →ₗ[U k g] N) : outer k g M →ₗ[ℤ] outer k g N :=
  (inner k g M).mapQ (inner k g N) (derivationsMap k g M N h) (by
    rintro f ⟨m, hm⟩
    refine ⟨h m, ?_⟩
    intro x
    change h (f.val x) = _
    rw [hm, h.map_smul])

end AdvancedHomologicalAlgebra.CE.LowDegree

namespace Specs.AdvancedHomologicalAlgebra.CE.LowDegree
open _root_.AdvancedHomologicalAlgebra.CE _root_.AdvancedHomologicalAlgebra.CE.LowDegree
open P103.Specs.Ch11.ExtTorDefinitions
universe u v w w'
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]

/-- The printed formulas under the canonical degree-zero/one coordinates. -/
def differentialsExpected : Prop :=
  ∀ (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)),
    HasCochainFormula k g M δ →
    (∀ m x, δ 0 ((zeroCoord k g M).symm m) (wedge k g 1 (fun _ => x)) =
      Shared.Lie.inclusion k g x • m) ∧
    (∀ (f : g →ₗ[k] M) x y,
      δ 1 ((oneCoord k g M).symm f) (wedge k g 2 ![x,y]) =
        Shared.Lie.inclusion k g x • f y - Shared.Lie.inclusion k g y • f x - f ⁅x,y⁆)

/-- The cohomology is the project's quotient of cycles by boundaries. -/
def identificationsExpected : Prop :=
  ∀ (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
    (s : ∀ n, (δ (n+1)).comp (δ n) = 0), HasCochainFormula k g M δ →
    ∃ (e₀ : Homology (Ext.cochain k g M δ s) 0 ≃+ invariants k g M)
      (e₁ : Homology (Ext.cochain k g M δ s) 1 ≃+ outer k g M),
      Identifies k g M δ s e₀ e₁

/-- Naturality holds for every U-linear coefficient map and for any
identifications with the prescribed action on cohomology classes. -/
def naturalityExpected : Prop :=
  ∀ (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
    (s : ∀ n, (δ (n+1)).comp (δ n) = 0), HasCochainFormula k g M δ →
  ∀ (N : Type w') [AddCommGroup N] [Module k N] [Module (U k g) N]
    [IsScalarTower k (U k g) N]
    (δN : ∀ n, (W k g n →ₗ[k] N) →ₗ[k] (W k g (n+1) →ₗ[k] N))
    (sN : ∀ n, (δN (n+1)).comp (δN n) = 0), HasCochainFormula k g N δN →
  ∀ (e₀ : Homology (Ext.cochain k g M δ s) 0 ≃+ invariants k g M)
    (e₁ : Homology (Ext.cochain k g M δ s) 1 ≃+ outer k g M)
    (e₀N : Homology (Ext.cochain k g N δN sN) 0 ≃+ invariants k g N)
    (e₁N : Homology (Ext.cochain k g N δN sN) 1 ≃+ outer k g N),
    Identifies k g M δ s e₀ e₁ → Identifies k g N δN sN e₀N e₁N →
  ∀ h : M →ₗ[U k g] N,
    ∃ H : ∀ n, Homology (Ext.cochain k g M δ s) n →ₗ[ℤ]
        Homology (Ext.cochain k g N δN sN) n,
      Ext.InducesCohomologyMap (K := Ext.cochain k g M δ s) (L := Ext.cochain k g N δN sN)
        (fun _ => (P103.HomTensorExactness.post (h.restrictScalars k)).toIntLinearMap) H ∧
      (∀ a, e₀N (H 0 a) = invariantsMap k g M N h (e₀ a)) ∧
      (∀ a, e₁N (H 1 a) = outerMap k g M N h (e₁ a))

/-- The actual free CE resolution and its evaluation comparison identify
these concrete groups with the corresponding Ext groups of the trivial module.
The equations require the isomorphisms to use the upstream comparison on classes. -/
def extExpected [Module.Free k g] : Prop :=
  ∃ (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (he : Ext.AugmentedExact k g d)
    (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
    (s : ∀ n, (δ (n+1)).comp (δ n) = 0)
    (e₀ : Homology (Ext.cochain k g M δ s) 0 ≃+ invariants k g M)
    (e₁ : Homology (Ext.cochain k g M δ s) 1 ≃+ outer k g M),
    HasBoundaryFormula k g d ∧ (∀ n, Module.Free (U k g) (V k g n)) ∧
    HasCochainFormula k g M δ ∧ Identifies k g M δ s e₀ e₁ ∧
    ∃ (e : P103.Specs.Ch11.ExtTorDefinitions.homComplex (Ext.chain k g d hc) M ≅
      Ext.cochain k g M δ s)
      (q₀ : invariants k g M ≃+
        @ExtWith _ _ _ _ (Ext.trivialModule k g) (Ext.resolution k g d hc he) M _ _ 0)
      (q₁ : outer k g M ≃+
        @ExtWith _ _ _ _ (Ext.trivialModule k g) (Ext.resolution k g d hc he) M _ _ 1),
      (∀ n (F : V k g n →ₗ[U k g] M) z,
        (e.hom.f n).hom F z = F ((1 : U k g) ⊗ₜ[k] z)) ∧
      (∀ z : cycles (Ext.cochain k g M δ s) 0,
        q₀ (e₀ (homologyClass _ 0 z)) = homologyClass _ 0 (cyclesMap e.inv 0 z)) ∧
      (∀ z : cycles (Ext.cochain k g M δ s) 1,
        q₁ (e₁ (homologyClass _ 1 z)) = homologyClass _ 1 (cyclesMap e.inv 1 z))

end Specs.AdvancedHomologicalAlgebra.CE.LowDegree

namespace Specs.AdvancedHomologicalAlgebra.CE.LowDegree
open _root_.AdvancedHomologicalAlgebra.CE
universe u v w w'

def differentialsType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M], differentialsExpected k g M

def cohomologyType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M], identificationsExpected k g M

def naturalityType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M], naturalityExpected.{u,v,w,w'} k g M

def extType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M] [Module.Free k g], extExpected k g M

end Specs.AdvancedHomologicalAlgebra.CE.LowDegree
