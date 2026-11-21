import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethFlatColumns

/-! The totalized cycle/boundary sequence in paper.tex 3075–3099.
All tensor products, maps and quotient homology use the upstream models.
The endpoint is stated in degree zero, without negative natural indices. -/
namespace P103.Specs.Ch11.KunnethTotalConnector
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.KunnethFlatColumns
noncomputable section
universe u v w
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev inclusion (C : Complex.{u,v} R) (D : ChainComplex (ModuleCat.{w} R) ℕ) :=
  ordinaryTotalMap (cycleInclusion C) (𝟙 D)
abbrev projection (C : Complex.{u,v} R) (D : ChainComplex (ModuleCat.{w} R) ℕ) :=
  ordinaryTotalMap (boundaryProjection C) (𝟙 D)

/-- Induced map of the actual zero-differential cycle complexes. -/
def cycleComplexMap {C C' : Complex.{u,v} R} (f : C ⟶ C') :
    cycleComplex C ⟶ cycleComplex C' :=
  familyMap (fun p => ModuleCat.ofHom (cyclesMap f p))

/-- The degree-zero term is the actual zero module; positive terms use the
upstream boundary map, with no chosen splittings. -/
def shiftedBoundaryComplexMap {C C' : Complex.{u,v} R} (f : C ⟶ C') :
    shiftedBoundaryComplex C ⟶ shiftedBoundaryComplex C' :=
  familyMap (fun p => match p with
    | 0 => 0
    | n+1 => ModuleCat.ofHom
        (((f.f n).hom.comp (boundaries C n).subtype).codRestrict (boundaries C' n) (by
          intro b
          obtain ⟨y,hy⟩ := b.property
          refine ⟨(f.f ((ComplexShape.down ℕ).prev n)).hom y, ?_⟩
          have H := congrArg (fun k => k.hom y) (f.comm ((ComplexShape.down ℕ).prev n) n)
          change (C'.d _ n).hom ((f.f _).hom y) = (f.f n).hom b.val
          exact H.trans (congrArg (f.f n).hom hy))))

/-- The positive connector in normalized flat-column coordinates, specified
for every normalized isomorphism and every homology class. -/
def ConnectorFormula (C : Complex.{u,v} R) (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (n : ℕ) (δ : Homology (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1) →ₗ[ℤ]
      Homology (ordinaryTotal (cycleComplex C) D) n) : Prop :=
  ∀ (eZ : DiagonalTensor (cycleTerms C) D n ≃ₗ[ℤ]
      Homology (ordinaryTotal (cycleComplex C) D) n)
    (eL : DiagonalTensor (shiftedBoundaryTerms C) D (n+1) ≃ₗ[ℤ]
      Homology (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1)),
    DiagonalFormula (cycleTerms C) D n eZ →
    DiagonalFormula (shiftedBoundaryTerms C) D (n+1) eL →
    ∀ (p q : ℕ) (h : p+q=n) (b : boundaries C p) (x : Homology D q),
      δ (eL (DirectSum.lof ℤ _ _ (⟨(p+1,q),by omega⟩ : Diagonal (n+1)) (tmul R b x))) =
        eZ (DirectSum.lof ℤ _ _ (⟨(p,q),h⟩ : Diagonal n) (tmul R (boundaryToCycles C p b) x))

/-- The positive representative formula, expressed on the underlying maps so
it is independent of the two definitionally different integer module instances. -/
def TotalConnecting (C : Complex.{u,v} R) (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (n : ℕ) (δ : Homology (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1) →ₗ[ℤ]
      Homology (ordinaryTotal (cycleComplex C) D) n) : Prop :=
  ∀ (z : cycles (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1))
    (b : (ordinaryTotal C D).X (n+1))
    (a : cycles (ordinaryTotal (cycleComplex C) D) n),
    ((projection C D).f (n+1)).hom b = z.val →
    ((inclusion C D).f n).hom a.val = ((ordinaryTotal C D).d (n+1) n).hom b →
    δ (homologyClass _ (n+1) z) = homologyClass _ n a

def TotalSequenceExact (C : Complex.{u,v} R) (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (n : ℕ) (δ : Homology (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1) →ₗ[ℤ]
      Homology (ordinaryTotal (cycleComplex C) D) n) : Prop :=
  Function.Exact (homologyMap (inclusion C D) (n+1)) (homologyMap (projection C D) (n+1)) ∧
  Function.Exact (homologyMap (projection C D) (n+1)) δ ∧
  Function.Exact δ (homologyMap (inclusion C D) n)

def total_degreewise_exactType : Prop :=
  ∀ (R : Type u) [Ring R] (C : Complex.{u,v} R),
    FlatTermsAndBoundaries.{u,v,w} C → ∀ D : ChainComplex (ModuleCat.{w} R) ℕ,
      DegreewiseExact (inclusion C D) (projection C D)

/-- Full exactness, representative formula for arbitrary lifts, uniqueness,
and normalization. The representative condition includes independence of
choices, rather than only a calculation for selected lifts. -/
def total_connectorType : Prop :=
  ∀ (R : Type u) [Ring R] (C : Complex.{u,v} R),
    FlatTermsAndBoundaries.{u,v,w} C →
    ∀ (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ),
    ∃! δ : Homology (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1) →ₗ[ℤ]
        Homology (ordinaryTotal (cycleComplex C) D) n,
      TotalConnecting C D n δ ∧
      TotalSequenceExact C D n δ ∧
      ConnectorFormula C D n δ

/-- H₀(L ⊗ D)=0 and the right endpoint of the sequence is exact. Together
with total_connector at n=0, this includes every degree-zero exact term. -/
def total_zeroType : Prop :=
  ∀ (R : Type u) [Ring R] (C : Complex.{u,v} R),
    FlatTermsAndBoundaries.{u,v,w} C → ∀ D : ChainComplex (ModuleCat.{w} R) ℕ,
      Subsingleton (Homology (ordinaryTotal (shiftedBoundaryComplex C) D) 0) ∧
      Function.Exact (homologyMap (inclusion C D) 0) (homologyMap (projection C D) 0) ∧
      Function.Surjective (homologyMap (inclusion C D) 0)

/-- Simultaneous naturality of every square, including the connecting square,
for arbitrary connecting maps satisfying the representative formula. -/
def total_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (C C' : Complex.{u,v} R)
    (D D' : ChainComplex (ModuleCat.{w} R) ℕ),
    FlatTermsAndBoundaries.{u,v,w} C → FlatTermsAndBoundaries.{u,v,w} C' →
    ∀ (f : C ⟶ C') (g : D ⟶ D') (n : ℕ)
      (δ : Homology (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1) →ₗ[ℤ]
        Homology (ordinaryTotal (cycleComplex C) D) n)
      (ε : Homology (ordinaryTotal (shiftedBoundaryComplex C') D') (n+1) →ₗ[ℤ]
        Homology (ordinaryTotal (cycleComplex C') D') n),
    TotalConnecting C D n δ →
    TotalConnecting C' D' n ε →
    let α := ordinaryTotalMap (cycleComplexMap f) g
    let β := ordinaryTotalMap f g
    let γ := ordinaryTotalMap (shiftedBoundaryComplexMap f) g
    (homologyMap β (n+1)).comp (homologyMap (inclusion C D) (n+1)) =
      (homologyMap (inclusion C' D') (n+1)).comp (homologyMap α (n+1)) ∧
    (homologyMap γ (n+1)).comp (homologyMap (projection C D) (n+1)) =
      (homologyMap (projection C' D') (n+1)).comp (homologyMap β (n+1)) ∧
    (homologyMap α n).toAddMonoidHom.toIntLinearMap.comp δ =
      ε.comp (homologyMap γ (n+1)).toAddMonoidHom.toIntLinearMap ∧
    (homologyMap β n).comp (homologyMap (inclusion C D) n) =
      (homologyMap (inclusion C' D') n).comp (homologyMap α n) ∧
    (homologyMap γ n).comp (homologyMap (projection C D) n) =
      (homologyMap (projection C' D') n).comp (homologyMap β n)

/-- Naturality also includes the endpoint squares in degree zero. -/
def total_zero_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (C C' : Complex.{u,v} R)
    (D D' : ChainComplex (ModuleCat.{w} R) ℕ) (f : C ⟶ C') (g : D ⟶ D'),
    (homologyMap (ordinaryTotalMap f g) 0).comp (homologyMap (inclusion C D) 0) =
      (homologyMap (inclusion C' D') 0).comp
        (homologyMap (ordinaryTotalMap (cycleComplexMap f) g) 0) ∧
    (homologyMap (ordinaryTotalMap (shiftedBoundaryComplexMap f) g) 0).comp
        (homologyMap (projection C D) 0) =
      (homologyMap (projection C' D') 0).comp (homologyMap (ordinaryTotalMap f g) 0)

end
end P103.Specs.Ch11.KunnethTotalConnector
