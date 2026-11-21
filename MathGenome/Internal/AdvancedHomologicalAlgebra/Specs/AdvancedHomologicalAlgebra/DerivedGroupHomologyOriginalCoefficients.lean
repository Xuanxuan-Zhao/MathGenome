import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedGroupHomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped MonoidAlgebra
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions
namespace AdvancedHomologicalAlgebra.DerivedGroupHomologyOriginal
open DerivedGroupHomology TorBalance
universe u v a b c d e f s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

/-- The two right complexes are fixed before choosing any coefficient carrier. -/
inductive Model where
  | tor
  | bar

abbrev Model.rightComplex : Model → ChainComplex (ModuleCat.{max u v} k[G]ᵐᵒᵖ) ℕ
  | .tor => (canonicalResolution k G).val.complex
  | .bar => barChain k G

abbrev Model.complex (P : Model) (M : ModuleCat.{a} k[G]) :=
  tensorComplex (P.rightComplex k G) M

abbrev Model.homology (P : Model) (M : ModuleCat.{a} k[G]) (n : ℕ) :=
  Homology (P.complex k G M) n

/-- A map of the original modules, with the unchanged group algebra acting. -/
abbrev CoefficientMap (M : ModuleCat.{a} k[G]) (N : ModuleCat.{b} k[G]) :=
  M →ₗ[k[G]] N

abbrev restrictMap {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) :
    RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N :=
  { toAddHom := (RestrictScalars.addEquiv k k[G] N).symm.toAddMonoidHom.comp
      (p.toAddMonoidHom.comp (RestrictScalars.addEquiv k k[G] M).toAddMonoidHom)
    map_smul' := fun r m => by
      apply (RestrictScalars.addEquiv k k[G] N).injective
      exact p.map_smul (algebraMap k k[G] r) (RestrictScalars.addEquiv k k[G] M m) }

abbrev symbolMap {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) (n : ℕ) : RightBar.C k G M n →ₗ[k] RightBar.C k G N n :=
  Finsupp.mapRange.linearMap (restrictMap k G p)

structure ShortExact {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    {Q : ModuleCat.{c} k[G]} (i : CoefficientMap k G M N) (p : CoefficientMap k G N Q) : Prop where
  injective : Function.Injective i
  exact : Function.Exact i p
  surjective : Function.Surjective p

/-- Shift a single carrier into a larger universe, keeping its original action. -/
abbrev Lift (M : ModuleCat.{a} k[G]) : ModuleCat.{max a s} k[G] :=
  ModuleCat.of k[G] (ULift.{s} M)

abbrev up (M : ModuleCat.{a} k[G]) : M →ₗ[k[G]] Lift.{u,v,a,s} k G M :=
  ULift.moduleEquiv.symm.toLinearMap

abbrev down (M : ModuleCat.{a} k[G]) : Lift.{u,v,a,s} k G M →ₗ[k[G]] M :=
  ULift.moduleEquiv.toLinearMap

abbrev liftedMap {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) :
    CoefficientMap k G (Lift.{u,v,a,s} k G M) (Lift.{u,v,b,s} k G N) :=
  (up k G N).comp (p.comp (down k G M))

/-- The sign is fixed by differentiating a lift in the middle complex. -/
def PositiveBoundary
    {R : Type*} [Ring R]
    {A : ChainComplex (ModuleCat.{a} R) ℕ}
    {B : ChainComplex (ModuleCat.{b} R) ℕ}
    {C : ChainComplex (ModuleCat.{c} R) ℕ}
    (i : LinearChainMap A B) (p : LinearChainMap B C) (n : ℕ)
    (δ : Homology C (n+1) →ₗ[R] Homology A n) : Prop :=
  ∀ (z : cycles C (n+1)) (y : B.X (n+1)) (x : cycles A n),
    p.app (n+1) y = z.val → i.app n x.val = (B.d (n+1) n).hom y →
      δ (homologyClass C (n+1) z) = homologyClass A n x

/-- A based identification of the original bar sums with the inverse-twisted
tensor model. The printed differential can be read on each individual symbol. -/
structure BarCoordinates where
  coordinates : ∀ (M : ModuleCat.{a} k[G]) (n : ℕ),
    RightBar.TensorChains k G M n ≃ₗ[k] RightBar.C k G M n
  symbol : ∀ (M : ModuleCat.{a} k[G]) (n : ℕ) (g : Fin n → G)
    (m : RestrictScalars k k[G] M),
    coordinates M n (P103.BalancedTensor.tmul k[G]
      ((RightBar.untwist k G _).symm
        (GroupBar.Large.single.{u,v,0} k G (RightBar.barTuple G g) 1))
      (RestrictScalars.addEquiv k k[G] M m)) = Finsupp.single g m
  differential : ∀ (M : ModuleCat.{a} k[G]) (n : ℕ) (g : Fin (n+1) → G)
    (m : RestrictScalars k k[G] M),
    coordinates M n (((chains k G M).d (n+1) n).hom
      ((coordinates M (n+1)).symm (Finsupp.single g m))) =
      Finsupp.single (Fin.tail g) (GroupCoinvariants.coefficientRepresentation k G M (g 0)⁻¹ m) +
      (∑ j : Fin n, (-1:k)^(j.val+1) •
        Finsupp.single (j.castSucc.contractNth (· * ·) g) m) +
      (-1:k)^(n+1) • Finsupp.single (Fin.init g) m

/-- The induced maps retain the original coefficient carrier on every pure tensor,
cycle and coinvariant representative. -/
structure CoefficientAction {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) where
  chain : ∀ P : Model, LinearChainMap (P.complex k G M) (P.complex k G N)
  tensor : ∀ (P : Model) (n : ℕ) (z : (P.rightComplex k G).X n) (m : M),
    (chain P).app n (P103.BalancedTensor.tmul k[G] z m) =
      P103.BalancedTensor.tmul k[G] z (p m)
  homology : ∀ (P : Model) (n : ℕ), P.homology k G M n →ₗ[ℤ] P.homology k G N n
  on_class : ∀ P, (chain P).InducesHomology (fun n z => homology P n z)
  coinvariants : GroupCoinvariants.Coinvariants k G M →ₗ[k] GroupCoinvariants.Coinvariants k G N
  on_quotient : ∀ m, coinvariants (GroupCoinvariants.quotientMap k G M m) =
    GroupCoinvariants.quotientMap k G N (restrictMap k G p m)

/-- Degreewise exactness makes sense without a common carrier universe. -/
def TermwiseExact
    {R : Type*} [Ring R]
    {A : ChainComplex (ModuleCat.{a} R) ℕ}
    {B : ChainComplex (ModuleCat.{b} R) ℕ}
    {C : ChainComplex (ModuleCat.{c} R) ℕ}
    (i : LinearChainMap A B) (p : LinearChainMap B C) : Prop :=
  ∀ n, Function.Injective (i.app n) ∧ Function.Exact (i.app n) (p.app n) ∧
    Function.Surjective (p.app n)

def ActionsType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} (p : CoefficientMap k G M N),
    Nonempty (CoefficientAction k G p)


/-- Each lift is termwise invertible and acts on homology and coinvariants
by the same map as it does on representatives. -/
structure LiftComparison (M : ModuleCat.{a} k[G]) where
  action : CoefficientAction k G (up.{u,v,a,s} k G M)
  terms : ∀ P n, Function.Bijective ((action.chain P).app n)
  homology : ∀ P n, Function.Bijective (action.homology P n)
  coinvariants : Function.Bijective action.coinvariants

def LiftComparisonType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (M : ModuleCat.{a} k[G]),
    Nonempty (LiftComparison.{u,v,a,s} k G M)

def BarActionType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ (E : BarCoordinates.{u,v,a} k G) (F : BarCoordinates.{u,v,b} k G)
      (A : ∀ {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} (p : CoefficientMap k G M N),
        CoefficientAction k G p),
      ∀ {M N} (p : CoefficientMap k G M N) (n : ℕ) (z : RightBar.TensorChains k G M n),
        F.coordinates N n ((A p).chain .bar |>.app n z) =
          symbolMap k G p n (E.coordinates M n z)

/-- An exact coefficient pair in a fixed adequate common universe. Each map
is conjugated by the up and down maps on its own original source and target. -/
def liftedSequence {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    {Q : ModuleCat.{c} k[G]} {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}
    (h : ShortExact k G i p) : ShortComplex (ModuleCat.{max a b c s} k[G]) :=
  ShortComplex.mk (ModuleCat.ofHom (liftedMap.{u,v,a,b,max a b c s} k G i))
    (ModuleCat.ofHom (liftedMap.{u,v,b,c,max a b c s} k G p)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ULift.up (p (i x.down)) = ULift.up 0
      exact congrArg ULift.up (h.exact.apply_apply_eq_zero x.down))

def LiftedSequenceType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
    {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q} (h : ShortExact k G i p),
    (liftedSequence.{u,v,a,b,c,s} k G h).ShortExact

section ExactSequence

variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}

structure CoefficientSequence (i : CoefficientMap k G M N) (p : CoefficientMap k G N Q) where
  first : CoefficientAction k G i
  second : CoefficientAction k G p
  boundary : ∀ (P : Model) (n : ℕ), P.homology k G Q (n+1) →ₗ[ℤ] P.homology k G M n
  chains_exact : ∀ P, TermwiseExact (first.chain P) (second.chain P)
  positive : ∀ P n, PositiveBoundary (first.chain P) (second.chain P) n (boundary P n)
  exact : ∀ P n, Function.Exact (first.homology P (n+1)) (second.homology P (n+1)) ∧
    Function.Exact (second.homology P (n+1)) (boundary P n) ∧
    Function.Exact (boundary P n) (first.homology P n)
  zero_exact : Function.Exact first.coinvariants second.coinvariants
  zero_surjective : Function.Surjective second.coinvariants

def CoefficientSequenceType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
    {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q},
    ShortExact k G i p → Nonempty (CoefficientSequence k G i p)

/-- The horizontal squares include both degree-zero coinvariant arrows. -/
def SequenceNaturalityType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
    {M' : ModuleCat.{d} k[G]} {N' : ModuleCat.{e} k[G]} {Q' : ModuleCat.{f} k[G]}
    {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}
    {i' : CoefficientMap k G M' N'} {p' : CoefficientMap k G N' Q'}
    (α : CoefficientMap k G M M') (β : CoefficientMap k G N N') (γ : CoefficientMap k G Q Q')
    (_ : i'.comp α = β.comp i) (_ : p'.comp β = γ.comp p)
    (S : CoefficientSequence k G i p) (T : CoefficientSequence k G i' p')
    (A : CoefficientAction k G α) (B : CoefficientAction k G β) (C : CoefficientAction k G γ),
    (∀ (P : Model) (n : ℕ),
      (T.first.homology P n).comp (A.homology P n) =
        (B.homology P n).comp (S.first.homology P n) ∧
      (T.second.homology P n).comp (B.homology P n) =
        (C.homology P n).comp (S.second.homology P n) ∧
      (A.homology P n).comp (S.boundary P n) =
        (T.boundary P n).comp (C.homology P (n+1))) ∧
    T.first.coinvariants.comp A.coinvariants = B.coinvariants.comp S.first.coinvariants ∧
    T.second.coinvariants.comp B.coinvariants = C.coinvariants.comp S.second.coinvariants

end ExactSequence

def LiftNaturalityType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} (p : CoefficientMap k G M N)
    (A : CoefficientAction k G p)
    (B : CoefficientAction k G (liftedMap.{u,v,a,b,s} k G p))
    (U : LiftComparison.{u,v,a,s} k G M) (V : LiftComparison.{u,v,b,s} k G N),
    (∀ P n,
      ((B.chain P).app n).comp ((U.action.chain P).app n) =
        ((V.action.chain P).app n).comp ((A.chain P).app n) ∧
      (B.homology P n).comp (U.action.homology P n) =
        (V.action.homology P n).comp (A.homology P n)) ∧
    B.coinvariants.comp U.action.coinvariants = V.action.coinvariants.comp A.coinvariants

/-- The actual augmentations give the zeroth-degree quotient; the bar
comparison is induced by an augmented map from the canonical resolution. -/
structure NormalizedComparisons where
  bar : ∀ (M : ModuleCat.{a} k[G]) (n : ℕ),
    GroupCoinvariants.GroupHomology k G M n ≃ₗ[ℤ] barHomology k G M n
  zero : ∀ M : ModuleCat.{a} k[G],
    GroupCoinvariants.GroupHomology k G M 0 ≃+ GroupCoinvariants.Coinvariants k G M
  bar_normalized : DerivedGroupHomology.BarCoordinates k G bar
  zero_normalized : CoinvariantCoordinates k G (fun M z => zero M z)

def ComparisonNaturalityType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ (E : NormalizedComparisons.{u,v,a} k G) (F : NormalizedComparisons.{u,v,b} k G),
      ∀ {M N} (p : CoefficientMap k G M N) (A : CoefficientAction k G p),
        (∀ n z, F.bar N n (A.homology .tor n z) = A.homology .bar n (E.bar M n z)) ∧
        (∀ z, F.zero N (A.homology .tor 0 z) = A.coinvariants (E.zero M z))

/-- The endpoint maps are obtained via the normalized zeroth Tor comparison,
and the two boundary formulas agree under the augmented Tor-to-bar map. -/
def SequenceComparisonType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ (E : NormalizedComparisons.{u,v,a} k G) (F : NormalizedComparisons.{u,v,c} k G),
      ∀ {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
        {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}
        (_h : ShortExact k G i p) (S : CoefficientSequence k G i p),
        (∀ n z, E.bar M n (S.boundary .tor n z) =
          S.boundary .bar n (F.bar Q (n+1) z)) ∧
        Function.Exact (S.boundary .tor 0)
          (fun z => S.first.coinvariants (E.zero M z))

/-- The source's differential, on the actual direct-sum chains, is the
transport of the inverse-twisted tensor differential. -/
def BarBoundaryOnSymbolsType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ (E : BarCoordinates.{u,v,a} k G) (F : BarCoordinates.{u,v,b} k G)
      (H : BarCoordinates.{u,v,c} k G),
      ∀ {M N Q} {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}
        (S : CoefficientSequence k G i p) (n : ℕ)
        (z : cycles (chains k G Q) (n+1)) (y : RightBar.C k G N (n+1))
        (x : cycles (chains k G M) n),
        symbolMap k G p (n+1) y = H.coordinates Q (n+1) z.val →
        symbolMap k G i n (E.coordinates M n x.val) =
          F.coordinates N n (((chains k G N).d (n+1) n).hom ((F.coordinates N (n+1)).symm y)) →
        S.boundary .bar n (homologyClass _ _ z) = homologyClass _ _ x


open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open DerivedGroupHomology.Specification

local instance originalCoinvariantsAdditive :
    (GroupCoinvariants.coinvariantsFunctor k G :
      ModuleCat.{a} k[G] ⥤ ModuleCat.{a} k).Additive := by
  letI : (Rep.ofModuleMonoidAlgebra : ModuleCat.{a} k[G] ⥤ Rep.{a} k G).Additive :=
    ⟨by intros; ext x; rfl⟩
  unfold GroupCoinvariants.coinvariantsFunctor
  infer_instance

universe x y

/-- Compare the original connecting map with the actual stalk-triangle
boundary in any adequate common module category. The comparison is fixed
on independent coefficient lifts, including the quotient augmentation. -/
def DerivedAgreementType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    [HasDerivedCategory.{x} (ModuleCat.{max u v a b c s} k[G])]
    [HasDerivedCategory.{y} (ModuleCat.{max u v a b c s} k)]
    (hA : (minus (ModuleCat.{max u v a b c s} k[G])).IsTriangulated)
    (hB : (minus (ModuleCat.{max u v a b c s} k)).IsTriangulated),
    letI := hA
    letI := hB
    let F := ambientCoinvariants.{u,v,max a b c s} k G
    ∀ D : ExactLeftData.{(max u v a b c s)+1,max u v a b c s,
        (max u v a b c s)+1,max u v a b c s,x,y} F,
    ∃ E : ∀ n : ℕ, leftValue F D n ≅ kHomologyFunctor.{u,v,max u v a b c s} k G n,
      (∀ (M : ModuleCat.{max u v a b c s} k[G])
        (a₀ : GroupCoinvariants.TrivialRight k G) (m : M),
        counitZero.{u,v,max a b c s,x,y} k G D M ((E 0).inv.app M
          ((torZero k G M).symm (P103.BalancedTensor.tmul k[G] a₀ m))) =
            GroupCoinvariants.trivialScalar k G a₀ • GroupCoinvariants.quotientMap k G M
              ((RestrictScalars.addEquiv k k[G] M).symm m)) ∧
      (∀ (S : ShortComplex (ModuleCat.{max u v a b c s} k[G])) (hS : S.ShortExact) (n : ℕ),
        P103.Specs.Ch10.HomologySequence.Connecting
          (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n
          (((E (n+1)).inv.app S.X₃ ≫ leftBoundary F D hS n ≫
            (E n).hom.app S.X₁).hom.toAddMonoidHom.toIntLinearMap)) ∧
      ∀ {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
        {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}
        (h : ShortExact k G i p) (O : CoefficientSequence k G i p)
        (U : LiftComparison.{u,v,a,max u v a b c s} k G M)
        (V : LiftComparison.{u,v,c,max u v a b c s} k G Q),
        let S := liftedSequence.{u,v,a,b,c,max u v s} k G h
        ∃ hS : S.ShortExact,
          (∀ n z, U.action.homology .tor n (O.boundary .tor n z) =
            ((E (n+1)).inv.app S.X₃ ≫ leftBoundary F D hS n ≫ (E n).hom.app S.X₁)
              (V.action.homology .tor (n+1) z)) ∧
          ∀ (a₀ : GroupCoinvariants.TrivialRight k G) (m : M),
            counitZero.{u,v,max a b c s,x,y} k G D S.X₁ ((E 0).inv.app S.X₁
              (U.action.homology .tor 0 ((torZero k G M).symm
                (P103.BalancedTensor.tmul k[G] a₀ m)))) =
              U.action.coinvariants
                (GroupCoinvariants.trivialScalar k G a₀ • GroupCoinvariants.quotientMap k G M
                  ((RestrictScalars.addEquiv k k[G] M).symm m))

variable {k G} in
/-- The actual nonhomogeneous chain complex on finitely supported sums.
Its differential is conjugated by the symbol comparison, whose fields give
the source formula with the inverse-action first face. -/
def BarCoordinates.complex (E : BarCoordinates.{u,v,a} k G)
    (M : ModuleCat.{a} k[G]) : ChainComplex (ModuleCat.{max v a} ℤ) ℕ where
  X n := ModuleCat.of ℤ (RightBar.C k G M n)
  d i j := ModuleCat.ofHom <| (E.coordinates M j).toAddEquiv.toAddMonoidHom.toIntLinearMap.comp
    (((chains k G M).d i j).hom.comp (E.coordinates M i).symm.toAddEquiv.toAddMonoidHom.toIntLinearMap)
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change E.coordinates M j (((chains k G M).d i j).hom ((E.coordinates M i).symm z)) = 0
    rw [(chains k G M).shape i j h]
    simp
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change E.coordinates M l (((chains k G M).d j l).hom
      ((E.coordinates M j).symm (E.coordinates M j
        (((chains k G M).d i j).hom ((E.coordinates M i).symm z))))) = 0
    rw [LinearEquiv.symm_apply_apply]
    have H := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      ((chains k G M).d_comp_d i j l)) ((E.coordinates M i).symm z)
    change ((chains k G M).d j l).hom
      (((chains k G M).d i j).hom ((E.coordinates M i).symm z)) = 0 at H
    rw [H, map_zero]

/-- The quotient on the actual sums carries a map taking each cycle to its
pointwise coefficient image. The comparison to inverse-twisted tensor
homology is itself induced by the specified coordinate map on cycles. -/
def ExplicitBarHomologyType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ (E : BarCoordinates.{u,v,a} k G) (F : BarCoordinates.{u,v,b} k G),
      ∃ (J : ∀ (M : ModuleCat.{a} k[G]) (n : ℕ),
          barHomology k G M n ≃ₗ[ℤ] Homology (E.complex M) n)
        (K : ∀ (N : ModuleCat.{b} k[G]) (n : ℕ),
          barHomology k G N n ≃ₗ[ℤ] Homology (F.complex N) n),
        (∀ M n (z : cycles (chains k G M) n), ∃ z' : cycles (E.complex M) n,
          z'.val = E.coordinates M n z.val ∧ J M n (homologyClass _ n z) = homologyClass _ n z') ∧
        (∀ N n (z : cycles (chains k G N) n), ∃ z' : cycles (F.complex N) n,
          z'.val = F.coordinates N n z.val ∧ K N n (homologyClass _ n z) = homologyClass _ n z') ∧
        ∀ {M N} (p : CoefficientMap k G M N) (A : CoefficientAction k G p),
          ∃ (f : LinearChainMap (E.complex M) (F.complex N))
            (g : ∀ n, Homology (E.complex M) n →ₗ[ℤ] Homology (F.complex N) n),
            (∀ n z, f.app n z = symbolMap k G p n z) ∧
            f.InducesHomology (fun n z => g n z) ∧
            ∀ n z, g n (J M n z) = K N n (A.homology .bar n z)

/-- There is a single ambient map of short exact sequences for any map of
six original carriers. Its components are the same conjugated maps used on
tensors and coinvariants. -/
def LiftedSequenceNaturalityType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
    {M' : ModuleCat.{d} k[G]} {N' : ModuleCat.{e} k[G]} {Q' : ModuleCat.{f} k[G]}
    {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}
    {i' : CoefficientMap k G M' N'} {p' : CoefficientMap k G N' Q'}
    (α : CoefficientMap k G M M') (β : CoefficientMap k G N N') (γ : CoefficientMap k G Q Q')
    (_ : i'.comp α = β.comp i) (_ : p'.comp β = γ.comp p)
    (h : ShortExact k G i p) (h' : ShortExact k G i' p'),
    ∃ φ : liftedSequence.{u,v,a,b,c,max u v d e f s} k G h ⟶
        liftedSequence.{u,v,d,e,f,max u v a b c s} k G h',
      φ.τ₁.hom = liftedMap.{u,v,a,d,max u v a b c d e f s} k G α ∧
      φ.τ₂.hom = liftedMap.{u,v,b,e,max u v a b c d e f s} k G β ∧
      φ.τ₃.hom = liftedMap.{u,v,c,f,max u v a b c d e f s} k G γ


/-- The coefficient sequence on the homology of the actual bar sums.
The maps are induced by pointwise coefficient homomorphisms. Its boundary
is positive on the sums and is the same normalized boundary as for Tor. -/
def ExplicitBarSequenceType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ (E : BarCoordinates.{u,v,a} k G) (F : BarCoordinates.{u,v,b} k G)
      (H : BarCoordinates.{u,v,c} k G),
      ∃ (J : ∀ (M : ModuleCat.{a} k[G]) (n : ℕ),
          barHomology k G M n ≃ₗ[ℤ] Homology (E.complex M) n)
        (K : ∀ (Q : ModuleCat.{c} k[G]) (n : ℕ),
          barHomology k G Q n ≃ₗ[ℤ] Homology (H.complex Q) n),
        (∀ M n (z : cycles (chains k G M) n), ∃ z' : cycles (E.complex M) n,
          z'.val = E.coordinates M n z.val ∧ J M n (homologyClass _ n z) = homologyClass _ n z') ∧
        (∀ Q n (z : cycles (chains k G Q) n), ∃ z' : cycles (H.complex Q) n,
          z'.val = H.coordinates Q n z.val ∧ K Q n (homologyClass _ n z) = homologyClass _ n z') ∧
        ∀ {M N Q} {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}
          (S : CoefficientSequence k G i p),
          ∃ (I : LinearChainMap (E.complex M) (F.complex N))
            (P : LinearChainMap (F.complex N) (H.complex Q))
            (Ih : ∀ n, Homology (E.complex M) n →ₗ[ℤ] Homology (F.complex N) n)
            (Ph : ∀ n, Homology (F.complex N) n →ₗ[ℤ] Homology (H.complex Q) n)
            (δ : ∀ n, Homology (H.complex Q) (n+1) →ₗ[ℤ] Homology (E.complex M) n),
            (∀ n x, I.app n x = symbolMap k G i n x) ∧
            (∀ n y, P.app n y = symbolMap k G p n y) ∧
            I.InducesHomology (fun n z => Ih n z) ∧ P.InducesHomology (fun n z => Ph n z) ∧
            TermwiseExact I P ∧
            ∀ n, PositiveBoundary I P n (δ n) ∧
              Function.Exact (Ih (n+1)) (Ph (n+1)) ∧
              Function.Exact (Ph (n+1)) (δ n) ∧
              Function.Exact (δ n) (Ih n) ∧
              (∀ z, δ n (K Q (n+1) z) = J M n (S.boundary .bar n z))

end AdvancedHomologicalAlgebra.DerivedGroupHomologyOriginal
