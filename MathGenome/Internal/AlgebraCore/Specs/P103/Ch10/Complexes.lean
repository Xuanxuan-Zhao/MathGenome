import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
Complexes and quotient homology, paper.tex 2228–2258.
All rings are arbitrary associative unital rings, including the zero ring.
Right S-modules are obtained by setting R = Sᵐᵒᵖ. No boundedness or
finiteness conditions are imposed. The generic complex shape specializes to
both integer chain and integer cochain complexes.
The canonical objects below are shared with the implementation; in particular
homology is the explicit quotient, not an unspecified categorical homology.
-/
namespace P103.Specs.Ch10.Complexes
open CategoryTheory
noncomputable section
universe u v w w'
variable (R : Type u) [Ring R]

abbrev Chain := ChainComplex (ModuleCat.{v} R) ℤ
abbrev Cochain := CochainComplex (ModuleCat.{v} R) ℤ

variable {R} {ι : Type w} {c : ComplexShape ι}

/-- The cycles are exactly the kernel of the outgoing differential. -/
def cycles (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) : Submodule R (C.X n) :=
  LinearMap.ker (C.d n (c.next n)).hom

/-- The boundaries, as a submodule of the ambient term. -/
def boundaries (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) : Submodule R (C.X n) :=
  LinearMap.range (C.d (c.prev n) n).hom

/-- Square zero is the reason the quotient of cycles by boundaries exists. -/
theorem boundaryInclusion (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    boundaries C n ≤ cycles C n := by
  rintro _ ⟨x, rfl⟩
  change (C.d n (c.next n)).hom ((C.d (c.prev n) n).hom x) = 0
  have h := congrArg ModuleCat.Hom.hom (C.d_comp_d (c.prev n) n (c.next n))
  exact DFunLike.congr_fun h x

/-- Boundaries viewed inside the cycles, via the inclusion proved above. -/
def cycleBoundaries (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    Submodule R (cycles C n) :=
  (boundaries C n).comap (cycles C n).subtype

abbrev Homology (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :=
  cycles C n ⧸ cycleBoundaries C n

def homologyClass (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    cycles C n →ₗ[R] Homology C n := (cycleBoundaries C n).mkQ

variable {C D E : HomologicalComplex (ModuleCat.{v} R) c}

/-- Restriction of a chain/cochain map to cycles. -/
def cyclesMap (f : C ⟶ D) (n : ι) : cycles C n →ₗ[R] cycles D n :=
  ((f.f n).hom.comp (cycles C n).subtype).codRestrict (cycles D n) (by
    intro z
    change (D.d n (c.next n)).hom ((f.f n).hom z.val) = 0
    have h := congrArg ModuleCat.Hom.hom (f.comm n (c.next n))
    change (D.d n (c.next n)).hom.comp (f.f n).hom =
      (f.f (c.next n)).hom.comp (C.d n (c.next n)).hom at h
    rw [← LinearMap.comp_apply, h, LinearMap.comp_apply]
    have hz : (C.d n (c.next n)).hom z.val = 0 := z.property
    rw [hz, map_zero])

theorem mapBoundary (f : C ⟶ D) (n : ι) :
    cycleBoundaries C n ≤ (cycleBoundaries D n).comap (cyclesMap f n) := by
  intro z hz
  obtain ⟨x, hx⟩ := hz
  change ∃ y, (D.d (c.prev n) n).hom y = (f.f n).hom z.val
  refine ⟨(f.f (c.prev n)).hom x, ?_⟩
  have h := congrArg ModuleCat.Hom.hom (f.comm (c.prev n) n)
  change (D.d (c.prev n) n).hom.comp (f.f (c.prev n)).hom =
    (f.f n).hom.comp (C.d (c.prev n) n).hom at h
  simpa only [LinearMap.comp_apply, hx, Submodule.coe_subtype] using DFunLike.congr_fun h x

/-- The induced map is the quotient of the restriction to cycles. -/
def homologyMap (f : C ⟶ D) (n : ι) : Homology C n →ₗ[R] Homology D n :=
  (cycleBoundaries C n).mapQ (cycleBoundaries D n) (cyclesMap f n) (mapBoundary f n)

def Acyclic (C : HomologicalComplex (ModuleCat.{v} R) c) : Prop :=
  ∀ n, Subsingleton (Homology C n)

/-- Bijectivity of the linear homology maps is equivalent to their being
linear isomorphisms, without any condition on dimensions. -/
def QuasiIsomorphism (f : C ⟶ D) : Prop :=
  ∀ n, Function.Bijective (homologyMap f n)

/-- A prescribed range imposes no condition inside it; all other terms vanish. -/
def SupportedIn (C : HomologicalComplex (ModuleCat.{v} R) c) (s : Set ι) : Prop :=
  ∀ n, n ∉ s → Subsingleton (C.X n)

variable {ι' : Type w'} {c' : ComplexShape ι'}

/-- Extension by zero along an embedding of degree shapes, for arbitrary ranges. -/
noncomputable def extendByZero (C : HomologicalComplex (ModuleCat.{v} R) c)
    (e : c.Embedding c') : HomologicalComplex (ModuleCat.{v} R) c' := C.extend e

/-- The extension retains each term in the prescribed range up to the
canonical linear equivalence. -/
noncomputable def extendByZeroTermEquiv (C : HomologicalComplex (ModuleCat.{v} R) c)
    (e : c.Embedding c') (i : ι) : (extendByZero C e).X (e.f i) ≃ₗ[R] C.X i :=
  (C.extendXIso e rfl).toLinearEquiv

/-- The degree-preserving embedding for nonnegative chain complexes. -/
def nonnegativeChainEmbedding : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) where
  f n := (n : ℤ)
  injective_f := by
    intro a b h
    change (a : ℤ) = (b : ℤ) at h
    exact_mod_cast h
  rel h := by
    change (↑_ : ℤ) + 1 = ↑_
    exact_mod_cast h

noncomputable def extendNonnegativeChain (C : ChainComplex (ModuleCat.{v} R) ℕ) : Chain R :=
  extendByZero C nonnegativeChainEmbedding

noncomputable def extendNonnegativeCochain (C : CochainComplex (ModuleCat.{v} R) ℕ) : Cochain R :=
  extendByZero C ComplexShape.embeddingUpNat






/-! Expected declaration interfaces. -/

-- Full interface types deliberately quantify arguments unused in their result.
set_option linter.unusedVariables false
set_option linter.checkUnivs false

abbrev ChainValue := @Chain.{u,v}

def ChainType := ∀ (R : Type u) [Ring R], Type (max u (v + 1))

abbrev CochainValue := @Cochain.{u,v}

def CochainType := ∀ (R : Type u) [Ring R], Type (max u (v + 1))

abbrev cyclesValue := @cycles.{u,v,w}

def cyclesType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι), Submodule R (C.X n)

abbrev boundariesValue := @boundaries.{u,v,w}

def boundariesType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι), Submodule R (C.X n)

abbrev cycleBoundariesValue := @cycleBoundaries.{u,v,w}

def cycleBoundariesType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι), Submodule R (cycles C n)

abbrev HomologyValue := @Homology.{u,v,w}

def HomologyType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι), Type v

abbrev homologyClassValue := @homologyClass.{u,v,w}

def homologyClassType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι), cycles C n →ₗ[R] Homology C n

abbrev cyclesMapValue := @cyclesMap.{u,v,w}

def cyclesMapType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) (n : ι), cycles C n →ₗ[R] cycles D n

abbrev homologyMapValue := @homologyMap.{u,v,w}

def homologyMapType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) (n : ι), Homology C n →ₗ[R] Homology D n

abbrev AcyclicValue := @Acyclic.{u,v,w}

def AcyclicType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c), Prop

abbrev QuasiIsomorphismValue := @QuasiIsomorphism.{u,v,w}

def QuasiIsomorphismType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D), Prop

abbrev SupportedInValue := @SupportedIn.{u,v,w}

def SupportedInType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (s : Set ι), Prop

abbrev extendByZeroValue := @extendByZero.{u,v,w,w'}

def extendByZeroType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {ι' : Type w'} {c' : ComplexShape ι'} (C : HomologicalComplex (ModuleCat.{v} R) c) (e : c.Embedding c'), HomologicalComplex (ModuleCat.{v} R) c'

abbrev extendByZeroTermEquivValue := @extendByZeroTermEquiv.{u,v,w,w'}

def extendByZeroTermEquivType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {ι' : Type w'} {c' : ComplexShape ι'} (C : HomologicalComplex (ModuleCat.{v} R) c) (e : c.Embedding c') (i : ι), (extendByZero C e).X (e.f i) ≃ₗ[R] C.X i

abbrev nonnegativeChainEmbeddingValue := @nonnegativeChainEmbedding

def nonnegativeChainEmbeddingType := (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ)

abbrev extendNonnegativeChainValue := @extendNonnegativeChain.{u,v}

def extendNonnegativeChainType := ∀ {R : Type u} [Ring R] (C : ChainComplex (ModuleCat.{v} R) ℕ), Chain.{u,v} R

abbrev extendNonnegativeCochainValue := @extendNonnegativeCochain.{u,v}

def extendNonnegativeCochainType := ∀ {R : Type u} [Ring R] (C : CochainComplex (ModuleCat.{v} R) ℕ), Cochain.{u,v} R

def differential_squaredType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (i j k : ι),
    (C.d j k).hom.comp (C.d i j).hom = 0

def boundaries_le_cyclesType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι),
    boundaries C n ≤ cycles C n

def cycleBoundaries_imageType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι),
    (cycleBoundaries C n).map (cycles C n).subtype = boundaries C n

def map_cyclesType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) (n : ι) {z : C.X n} (hz : z ∈ cycles C n),
    (f.f n).hom z ∈ cycles D n

def map_boundariesType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) (n : ι) {z : C.X n} (hz : z ∈ boundaries C n),
    (f.f n).hom z ∈ boundaries D n

def cyclesMap_applyType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) (n : ι) (z : cycles C n),
    (cyclesMap f n z : D.X n) = (f.f n).hom z.val

def homologyMap_applyType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) (n : ι) (z : cycles C n),
    homologyMap f n (homologyClass C n z) = homologyClass D n (cyclesMap f n z)

def homologyClass_eq_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι)
    (z z' : cycles C n),
    homologyClass C n z = homologyClass C n z' ↔ z.val - z'.val ∈ boundaries C n

def homologyMap_wellDefinedType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) (n : ι) (z z' : cycles C n)
    (h : z.val - z'.val ∈ boundaries C n),
    homologyClass D n (cyclesMap f n z) = homologyClass D n (cyclesMap f n z')

def homologyMap_idType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι),
    homologyMap (𝟙 C) n = LinearMap.id

def homologyMap_compType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D E : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) (g : D ⟶ E) (n : ι),
    homologyMap (f ≫ g) n = (homologyMap g n).comp (homologyMap f n)

def homologyMap_addType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f g : C ⟶ D) (n : ι),
    homologyMap (f + g) n = homologyMap f n + homologyMap g n

def homologyMap_zeroType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C D : HomologicalComplex (ModuleCat.{v} R) c) (n : ι),
    homologyMap (0 : C ⟶ D) n = 0

def acyclic_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c),
    Acyclic C ↔ ∀ n, boundaries C n = cycles C n

def quasiIsomorphism_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D),
    QuasiIsomorphism f ↔ ∀ n, ∃ e : Homology C n ≃ₗ[R] Homology D n,
      e.toLinearMap = homologyMap f n

def cycles_chainType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Chain.{u,v} R) (n : ℤ),
    cycles C n = LinearMap.ker (C.d n (n - 1)).hom

def boundaries_chainType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Chain.{u,v} R) (n : ℤ),
    boundaries C n = LinearMap.range (C.d (n + 1) n).hom

def cycles_cochainType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Cochain.{u,v} R) (n : ℤ),
    cycles C n = LinearMap.ker (C.d n (n + 1)).hom

def boundaries_cochainType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Cochain.{u,v} R) (n : ℤ),
    boundaries C n = LinearMap.range (C.d (n - 1) n).hom

def homology_chainType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Chain.{u,v} R) (n : ℤ),
    Homology C n = (LinearMap.ker (C.d n (n - 1)).hom ⧸
      (LinearMap.range (C.d (n + 1) n).hom).comap
        (LinearMap.ker (C.d n (n - 1)).hom).subtype)

def homology_cochainType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Cochain.{u,v} R) (n : ℤ),
    Homology C n = (LinearMap.ker (C.d n (n + 1)).hom ⧸
      (LinearMap.range (C.d (n - 1) n).hom).comap
        (LinearMap.ker (C.d n (n + 1)).hom).subtype)

def supported_d_fromType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (s : Set ι)
    (h : SupportedIn C s) (i j : ι) (hi : i ∉ s),
    C.d i j = 0

def supported_d_toType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c) (s : Set ι)
    (h : SupportedIn C s) (i j : ι) (hj : j ∉ s),
    C.d i j = 0

def extendByZero_supportedType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {ι' : Type w'} {c' : ComplexShape ι'} (C : HomologicalComplex (ModuleCat.{v} R) c)
    (e : c.Embedding c'),
    SupportedIn (extendByZero C e) (Set.range e.f)

def extendByZero_dType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} {ι' : Type w'} {c' : ComplexShape ι'} (C : HomologicalComplex (ModuleCat.{v} R) c)
    (e : c.Embedding c') (i j : ι),
    (extendByZero C e).d (e.f i) (e.f j) =
      (C.extendXIso e rfl).hom ≫ C.d i j ≫ (C.extendXIso e rfl).inv

def extendNonnegativeChain_supportedType : Prop :=
  ∀ {R : Type u} [Ring R] (C : ChainComplex (ModuleCat.{v} R) ℕ),
    SupportedIn (extendNonnegativeChain C) (Set.Ici (0 : ℤ))

def extendNonnegativeCochain_supportedType : Prop :=
  ∀ {R : Type u} [Ring R] (C : CochainComplex (ModuleCat.{v} R) ℕ),
    SupportedIn (extendNonnegativeCochain C) (Set.Ici (0 : ℤ))

end
end P103.Specs.Ch10.Complexes
