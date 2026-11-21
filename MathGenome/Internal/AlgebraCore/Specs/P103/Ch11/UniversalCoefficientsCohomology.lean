import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtExactSequences
import Mathlib.Algebra.Module.Projective

/-! Cohomological universal coefficients, paper.tex 2939–2946, 2989–3008.
The chain and Hom complexes and their quotient homology are the shared objects.
R is associative and unital, with the zero ring allowed. Right modules mean
left modules over the opposite ring. Splitting is allocated separately. -/
namespace P103.Specs.Ch11.UniversalCoefficientsCohomology
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence P103.Specs.Ch10.Horseshoe
open P103.Specs.Ch11.ExtTorDefinitions
noncomputable section
set_option maxHeartbeats 800000
universe u v w
variable {R : Type u} [Ring R]

abbrev Ordinary (R : Type u) [Ring R] := ChainComplex (ModuleCat.{v} R) ℕ

def ProjectiveTermsAndBoundaries (C : Ordinary R) : Prop :=
  (∀ n, Module.Projective R (C.X n)) ∧ (∀ n, Module.Projective R (boundaries C n))

/-- The boundary inclusion into cycles. -/
def j (C : Ordinary R) (n : ℕ) : boundaries C n →ₗ[R] cycles C n :=
  Submodule.inclusion (boundaryInclusion C n)

/-- The incoming differential with its image as codomain. -/
def incomingProjection (C : Ordinary R) (n : ℕ) : C.X (n+1) →ₗ[R] boundaries C n :=
  (C.d (n+1) n).hom.codRestrict _ (by
    intro x
    change ∃ y, (C.d ((ComplexShape.down ℕ).prev n) n).hom y = _
    rw [ChainComplex.prev]
    exact ⟨x, rfl⟩)

/-- B₋₁=0, with successor terms literally the existing boundary modules. -/
def previousBoundary (C : Ordinary R) : ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R (⊥ : Submodule R (C.X 0))
  | n+1 => ModuleCat.of R (boundaries C n)

def boundaryProjection (C : Ordinary R) : ∀ n, C.X n →ₗ[R] previousBoundary C n
  | 0 => 0
  | n+1 => incomingProjection C n

/-- Z and L have zero differentials, with L₀=im d₀₀=0 and Lₙ₊₁=Bₙ. -/
def zeroCycles (C : Ordinary R) : Ordinary R where
  X n := ModuleCat.of R (cycles C n)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def zeroPreviousBoundaries (C : Ordinary R) : Ordinary R where
  X n := previousBoundary C n
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- The definitional identification of a Hom term with linear maps. -/
def homTerm (C : Ordinary R) (M : ModuleCat.{w} R) (n : ℕ)
    (h : (homComplex C M).X n) : C.X n →ₗ[R] M := h

/-- A functional represents a Hom cocycle exactly when it kills incoming boundaries. -/
def IsRestriction (C : Ordinary R) (M : ModuleCat.{w} R) (n : ℕ)
    (β : Homology (homComplex C M) n →ₗ[ℤ] (Homology C n →ₗ[R] M)) : Prop :=
  ∀ (z : cycles (homComplex C M) n) (x : cycles C n),
    β (homologyClass _ n z) (homologyClass C n x) = homTerm C M n z.val x.val

/-- The raw left map is precomposition with Cₙ₊₁ ↠ Bₙ. -/
def IsBoundaryClass (C : Ordinary R) (M : ModuleCat.{w} R) (n : ℕ)
    (a : (boundaries C n →ₗ[R] M) →ₗ[ℤ] Homology (homComplex C M) (n+1)) : Prop :=
  ∀ (h : boundaries C n →ₗ[R] M) (z : cycles (homComplex C M) (n+1)),
    (z.val : C.X (n+1) →ₗ[R] M) = h.comp (incomingProjection C n) →
      a h = homologyClass _ (n+1) z

abbrev restriction (C : Ordinary R) (M : ModuleCat.{w} R) (n : ℕ) :=
  (P103.HomTensorExactness.pre (Q := M) (j C n)).toIntLinearMap

abbrev BoundaryCoker (C : Ordinary R) (M : ModuleCat.{w} R) (n : ℕ) :=
  (boundaries C n →ₗ[R] M) ⧸ LinearMap.range (restriction C M n)

/-- The edge identification is fixed by the positive Ext connector for the
projective presentation Bₙ → Zₙ → Hₙ, rather than an arbitrary isomorphism. -/
def IsExtCoker (C : Ordinary R) (M : ModuleCat.{w} R) (n : ℕ)
    (N : LeftResolution R (Homology C n))
    (e : ExtWith N M 1 ≃ₗ[ℤ] BoundaryCoker C M n) : Prop :=
  ∃ (L : LeftResolution R (boundaries C n)) (hL : L.IsProjective)
    (H : ProjectiveData (j C n) (homologyClass C n) L N)
    (δ : ExtWith L M 0 →ₗ[ℤ] ExtWith N M 1),
    P103.Specs.Ch11.ExtExactSequences.FirstConnecting
      (i := ModuleCat.ofHom (j C n)) (p := ModuleCat.ofHom (homologyClass C n)) H M 0 δ ∧
    ∀ h : boundaries C n →ₗ[R] M,
      e.symm (Submodule.Quotient.mk h) =
        δ (P103.Specs.Ch11.ExtExactSequences.homClass L M h)

/-- The coker and Hom description of the short exact sequence, in every
positive degree. Its two maps are fixed on all representatives. -/
def CokerSequence (C : Ordinary R) (M : ModuleCat.{w} R) (n : ℕ)
    (α : BoundaryCoker C M n →ₗ[ℤ] Homology (homComplex C M) (n+1))
    (β : Homology (homComplex C M) (n+1) →ₗ[ℤ] (Homology C (n+1) →ₗ[R] M)) : Prop :=
  IsBoundaryClass C M n (α.comp (LinearMap.range (restriction C M n)).mkQ) ∧
  IsRestriction C M (n+1) β ∧
  Function.Injective α ∧ Function.Exact α β ∧ Function.Surjective β

/-- Canonical arrows in the theorem are additive for arbitrary R. -/
def projective_cyclesType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Ordinary.{u,v} R), ProjectiveTermsAndBoundaries C →
    ∀ n, (∃ s : previousBoundary C n →ₗ[R] C.X n,
      (boundaryProjection C n).comp s = LinearMap.id) ∧ Module.Projective R (cycles C n)

def coker_sequenceType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Ordinary.{u,v} R), ProjectiveTermsAndBoundaries C →
    ∀ (M : ModuleCat.{w} R) (n : ℕ),
      ∃ α β, CokerSequence C M n α β

/-- H₋₁=0: the left term vanishes and the restriction map in degree zero is
an isomorphism. There is no spurious incoming boundary at degree zero. -/
def degree_zeroType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Ordinary.{u,v} R),
    ∀ M : ModuleCat.{w} R,
    ∃ e : Homology (homComplex C M) 0 ≃ₗ[ℤ] (Homology C 0 →ₗ[R] M),
      IsRestriction C M 0 e.toLinearMap

def ext_cokerType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Ordinary.{u,v} R), ProjectiveTermsAndBoundaries C →
    ∀ (M : ModuleCat.{w} R) (n : ℕ) (N : LeftResolution R (Homology C n)),
      N.IsProjective → ∃ e, IsExtCoker C M n N e

/-- The actual Ext sequence, linked to the specified cokernel sequence. -/
def universal_coefficientsType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Ordinary.{u,v} R), ProjectiveTermsAndBoundaries C →
    ∀ (M : ModuleCat.{w} R) (n : ℕ) (N : LeftResolution R (Homology C n)),
      N.IsProjective →
      ∃ (e : ExtWith N M 1 ≃ₗ[ℤ] BoundaryCoker C M n)
        (α : BoundaryCoker C M n →ₗ[ℤ] Homology (homComplex C M) (n+1))
        (β : Homology (homComplex C M) (n+1) →ₗ[ℤ] (Homology C (n+1) →ₗ[R] M)),
        IsExtCoker C M n N e ∧ CokerSequence C M n α β ∧
        Function.Injective (α.comp e.toLinearMap) ∧
        Function.Exact (α.comp e.toLinearMap) β ∧ Function.Surjective β

/-- Formula for both naturality squares, with the genuine all-resolution Ext
map in the left square. It also asserts compatibility of all edge choices. -/
def naturalityType : Prop :=
  ∀ {R : Type u} [Ring R] (C D : Ordinary.{u,v} R),
    ProjectiveTermsAndBoundaries C → ProjectiveTermsAndBoundaries D →
    ∀ (f : D ⟶ C) (M M' : ModuleCat.{w} R) (g : M ⟶ M') (n : ℕ)
      (E : ExtMaps.{u,v,w} R 1)
      (N : LeftResolution R (Homology C n)) (N' : LeftResolution R (Homology D n))
      (hN : N.IsProjective) (hN' : N'.IsProjective)
      (e : ExtWith N M 1 ≃ₗ[ℤ] BoundaryCoker C M n)
      (e' : ExtWith N' M' 1 ≃ₗ[ℤ] BoundaryCoker D M' n)
      (α : BoundaryCoker C M n →ₗ[ℤ] Homology (homComplex C M) (n+1))
      (β : Homology (homComplex C M) (n+1) →ₗ[ℤ] (Homology C (n+1) →ₗ[R] M))
      (α' : BoundaryCoker D M' n →ₗ[ℤ] Homology (homComplex D M') (n+1))
      (β' : Homology (homComplex D M') (n+1) →ₗ[ℤ] (Homology D (n+1) →ₗ[R] M')),
      IsExtCoker C M n N e → IsExtCoker D M' n N' e' →
      CokerSequence C M n α β → CokerSequence D M' n α' β' →
      (∀ x, homologyMap (homPreMap f M ≫ homPostMap D g.hom) (n+1)
          (α (e x)) =
        α' (e' (E.map ⟨N,hN⟩ ⟨N',hN'⟩ (ModuleCat.ofHom (homologyMap f n)) g x))) ∧
      (∀ x, β' (homologyMap (homPreMap f M ≫ homPostMap D g.hom) (n+1) x) =
        g.hom.comp ((β x).comp (homologyMap f (n+1))))

/-- The degree-zero naturality square also includes arbitrary coefficient maps. -/
def degree_zero_naturalType : Prop :=
  ∀ {R : Type u} [Ring R] (C D : Ordinary.{u,v} R) (f : D ⟶ C)
    (M M' : ModuleCat.{w} R) (g : M ⟶ M')
    (β : Homology (homComplex C M) 0 →ₗ[ℤ] (Homology C 0 →ₗ[R] M))
    (β' : Homology (homComplex D M') 0 →ₗ[ℤ] (Homology D 0 →ₗ[R] M')),
    IsRestriction C M 0 β → IsRestriction D M' 0 β' →
    ∀ x, β' (homologyMap (homPreMap f M ≫ homPostMap D g.hom) 0 x) =
      g.hom.comp ((β x).comp (homologyMap f 0))

/-- A concrete version of the source's sequence of complexes and connector.
The arrows have their specified components, and the connector restricts h
along jₙ on the displayed zero-complex representatives. -/
def hom_sequenceType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Ordinary.{u,v} R), ProjectiveTermsAndBoundaries C →
  ∃ (i : zeroCycles C ⟶ C) (p : C ⟶ zeroPreviousBoundaries C),
    (∀ n, (i.f n).hom = (cycles C n).subtype) ∧
    (∀ n, (p.f n).hom = boundaryProjection C n) ∧
    DegreewiseExact i p ∧
    ∀ M : ModuleCat.{w} R,
      DegreewiseExact (homPreMap p M) (homPreMap i M) ∧
      ∀ n, ∃ δ : Homology (homComplex (zeroCycles C) M) n →ₗ[ℤ]
          Homology (homComplex (zeroPreviousBoundaries C) M) (n+1),
        Connecting (homPreMap p M) (homPreMap i M) n (n+1) δ ∧
        SequenceExact (homPreMap p M) (homPreMap i M) n (n+1) δ ∧
        ∀ (h : cycles (homComplex (zeroCycles C) M) n)
          (k : cycles (homComplex (zeroPreviousBoundaries C) M) (n+1)),
          (∀ b : previousBoundary C (n+1),
            homTerm (zeroPreviousBoundaries C) M (n+1) k.val b =
              homTerm (zeroCycles C) M n h.val (j C n b)) →
          δ (homologyClass _ n h) = homologyClass _ (n+1) k

/-- Cohomology as an additive functor of the coefficient module. -/
def cohomologyCoefficients (C : Ordinary.{u,v} R) (n : ℕ) :
    ModuleCat.{w} R ⥤ ModuleCat.{max v w} ℤ where
  obj M := ModuleCat.of ℤ (Homology (homComplex C M) n)
  map g := ModuleCat.ofHom (homologyMap (homPostMap C g.hom) n)
  map_id M := by
    apply ModuleCat.hom_ext
    apply (cycleBoundaries (homComplex C M) n).quot_hom_ext
    intro z
    rfl
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply (cycleBoundaries (homComplex C _) n).quot_hom_ext
    intro z
    rfl

instance (C : Ordinary.{u,v} R) (n : ℕ) : (cohomologyCoefficients C n).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply (cycleBoundaries (homComplex C M) n).quot_hom_ext
    intro z
    exact (homologyClass (homComplex C N) n).map_add
      (cyclesMap (homPostMap C f.hom) n z) (cyclesMap (homPostMap C g.hom) n z)

/-- For commutative R, this is the usual action induced by multiplication
on the coefficient M; it is not an arbitrarily transported module structure. -/
@[instance_reducible] def cohomologyModule {K : Type u} [CommRing K]
    (C : Ordinary.{u,v} K) (M : ModuleCat.{w} K) (n : ℕ) :
    Module K (Homology (homComplex C M) n) :=
  coefficientModule (cohomologyCoefficients C n) M

/-- In the commutative case both actual Ext-sequence maps are R-linear for
the standard coefficient actions. Degree zero is included explicitly. -/
def scalar_compatibilityType : Prop :=
  ∀ {K : Type u} [CommRing K] (C : Ordinary.{u,v} K),
    ProjectiveTermsAndBoundaries C →
    ∀ (M : ModuleCat.{w} K) (n : ℕ) (E : ExtMaps.{u,v,w} K 1)
      (N : LeftResolution K (Homology C n)) (hN : N.IsProjective),
    letI := extModule E (A := ModuleCat.of K (Homology C n)) ⟨N,hN⟩ M
    letI := cohomologyModule C M (n+1)
    (∀ (e : ExtWith N M 1 ≃ₗ[ℤ] BoundaryCoker C M n)
      (α : BoundaryCoker C M n →ₗ[ℤ] Homology (homComplex C M) (n+1))
      (β : Homology (homComplex C M) (n+1) →ₗ[ℤ] (Homology C (n+1) →ₗ[K] M)),
      IsExtCoker C M n N e → CokerSequence C M n α β →
      ∃ (a : ExtWith N M 1 →ₗ[K] Homology (homComplex C M) (n+1))
        (b : Homology (homComplex C M) (n+1) →ₗ[K] (Homology C (n+1) →ₗ[K] M)),
        a.toAddMonoidHom = (α.comp e.toLinearMap).toAddMonoidHom ∧
        b.toAddMonoidHom = β.toAddMonoidHom) ∧
    (letI := cohomologyModule C M 0
    ∀ β : Homology (homComplex C M) 0 →ₗ[ℤ] (Homology C 0 →ₗ[K] M),
      IsRestriction C M 0 β →
      ∃ b : Homology (homComplex C M) 0 →ₗ[K] (Homology C 0 →ₗ[K] M),
        b.toAddMonoidHom = β.toAddMonoidHom)

/-- Specializing all arbitrary-ring conclusions to Rᵐᵒᵖ is the right-module version. -/
def right_modulesType : Prop :=
  ∀ (R : Type u) [Ring R] (C : Ordinary.{u,v} Rᵐᵒᵖ),
    ProjectiveTermsAndBoundaries C →
    ∀ (M : ModuleCat.{w} Rᵐᵒᵖ) (n : ℕ)
      (N : LeftResolution Rᵐᵒᵖ (Homology C n)), N.IsProjective →
      ∃ e α β, IsExtCoker C M n N e ∧ CokerSequence C M n α β ∧
        Function.Injective (α.comp e.toLinearMap) ∧
        Function.Exact (α.comp e.toLinearMap) β ∧ Function.Surjective β

end
end P103.Specs.Ch11.UniversalCoefficientsCohomology
