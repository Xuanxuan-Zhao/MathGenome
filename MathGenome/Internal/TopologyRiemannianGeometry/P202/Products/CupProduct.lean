import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.CupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.EilenbergZilber
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.AlexanderWhitney

/-!
The singular cup product, paper.tex `thm:p202-cup` (1932–1964).
The front/back cochain identities descend to the existing ordinary cohomology.
For graded commutativity, acyclic models construct a natural homotopy between
AW Δ and its Koszul interchange. Positive tensor-model acyclicity follows from
the proved Eilenberg–Zilber equivalence and homotopy invariance on simplices.
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite HomologicalComplex
open scoped TensorProduct DirectSum Simplicial
namespace P202.CupProduct
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CohomologyPairs P202Specs.CupProduct
universe u w
variable (R : Type u) [CommRing R]

@[simp] theorem cup_single (X : TopCat.{w}) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R X q) (s : Simplex X (p+q)) (r : R) :
    cup R X p q a b (Finsupp.single s r) = r *
      (a (Finsupp.single (interval s 0 p (by omega)) 1) *
       b (Finsupp.single (interval s p q (by omega)) 1)) := by
  simp [cup, Finsupp.llift_apply, Finsupp.lift_apply]

@[simp] theorem castCochain_rfl {X : TopCat.{w}} {n : ℕ} (a : Cochain R X n) :
    castCochain R rfl a = a := rfl

lemma cast_cup_single {X : TopCat.{w}} {p q n : ℕ} (h : p+q=n)
    (a : Cochain R X p) (b : Cochain R X q) (s : Simplex X n) :
    castCochain R h (cup R X p q a b) (Finsupp.single s 1) =
      a (Finsupp.single (interval s 0 p (by omega)) 1) *
      b (Finsupp.single (interval s p q (by omega)) 1) := by
  subst n
  simp

lemma interval_interval {X : TopCat.{w}} {n : ℕ} (s : Simplex X n)
    (a k : ℕ) (h : a+k ≤ n) (b l : ℕ) (h' : b+l ≤ k) :
    interval (interval s a k h) b l h' = interval s (a+b) l (by omega) := by
  have hc : intervalInclusion b l k h' ≫ intervalInclusion a k n h =
      intervalInclusion (a+b) l n (by omega) := by
    ext j
    simp [intervalInclusion, Nat.add_assoc]
  simp only [interval, P202.AlexanderWhitney.restrict_comp, hc]

theorem cup_associative (X : TopCat.{w}) (p q r : ℕ)
    (a : Cochain R X p) (b : Cochain R X q) (c : Cochain R X r) :
    castCochain R (Nat.add_assoc p q r) (cup R X (p+q) r (cup R X p q a b) c) =
      cup R X p (q+r) a (cup R X q r b c) := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X (p+(q+r)))).ext
  intro s
  simp only [Finsupp.coe_basisSingleOne]
  rw [cast_cup_single, cup_single, cup_single, cup_single]
  simp only [one_mul, interval_interval, Nat.zero_add, Nat.add_zero, mul_assoc]

theorem cup_unit (X : TopCat.{w}) (p : ℕ) (a : Cochain R X p) :
    castCochain R (Nat.zero_add p) (cup R X 0 p (oneCochain R X) a) = a ∧
    castCochain R (Nat.add_zero p) (cup R X p 0 a (oneCochain R X)) = a := by
  constructor <;>
    apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X p)).ext <;>
    intro s <;>
    simp only [Finsupp.coe_basisSingleOne] <;>
    rw [cast_cup_single] <;>
    simp [oneCochain, P202.SingularChains.augmentationLinear_single,
      P202.AlexanderWhitney.interval_self]

theorem cup_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (p q : ℕ)
    (a : Cochain R Y p) (b : Cochain R Y q) :
    pullback R f (p+q) (cup R Y p q a b) =
      cup R X p q (pullback R f p a) (pullback R f q b) := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X (p+q))).ext
  intro s
  simp only [Finsupp.coe_basisSingleOne]
  change cup R Y p q a b (((chainMap R R f).f (p+q)).hom (Finsupp.single s 1)) = _
  rw [P202.SingularChains.chainMap_single, cup_single, cup_single]
  simp only [one_mul]
  change _ = a (((chainMap R R f).f p).hom _) * b (((chainMap R R f).f q).hom _)
  rw [P202.SingularChains.chainMap_single, P202.SingularChains.chainMap_single]
  rfl

@[simp] lemma tensorPairing_tmul {X Y : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q) (c : Chains R X p) (d : Chains R Y q) :
    tensorPairing R a b (c ⊗ₜ[R] d) = a c * b d := rfl

theorem cup_leibniz (X : TopCat.{w}) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R X q) :
    delta R X (p+q) (cup R X p q a b) =
      castCochain R (by omega) (cup R X (p+1) q (delta R X p a) b) +
        (-1 : ℤ)^p • castCochain R (by omega) (cup R X p (q+1) a (delta R X q b)) := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X (p+q+1))).ext
  intro s
  simp only [Finsupp.coe_basisSingleOne]
  change cup R X p q a b (boundary R R X (p+q) (Finsupp.single s 1)) = _
  rw [P202.SingularChains.boundary_single]
  simp only [map_sum, map_zsmul, cup_single, one_mul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [cast_cup_single, cast_cup_single]
  have h := congrArg (tensorPairing R a b) (P202.AlexanderWhitney.component_identity R X X p q s s)
  simp only [map_add, map_sum, map_zsmul, tensorPairing_tmul] at h
  exact h.symm

theorem cup_diagonal (X : TopCat.{w}) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R X q) (c : Chains R X (p+q)) :
    cup R X p q a b c = tensorPairing R a b
      (chainDiagonal R X (p+q) c ⟨(p,q),rfl⟩) := by
  let ev : Total R X X (p+q) →ₗ[R] Summand R X X p q :=
    LinearMap.proj (⟨(p,q),rfl⟩ : Diagonal (p+q))
  have h : cup R X p q a b = (tensorPairing R a b).comp (ev.comp (chainDiagonal R X (p+q))) := by
    apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X (p+q))).ext
    intro s
    simp only [Finsupp.coe_basisSingleOne]
    change cup R X p q a b (Finsupp.single s 1) = tensorPairing R a b
      (aw R X X (p+q) (((chainMap R R (diagonalMap X)).f (p+q)).hom
        (Finsupp.single s 1)) ⟨(p,q),rfl⟩)
    rw [P202.SingularChains.chainMap_single, P202.AlexanderWhitney.formula]
    simp only [one_smul, awComponent, tensorPairing_tmul, cup_single, one_mul]
    have hf : diagonalMap X ≫ firstProjection X X = 𝟙 X := rfl
    have hg : diagonalMap X ≫ secondProjection X X = 𝟙 X := rfl
    change _ = a (Finsupp.single
      (interval (postSimplex (firstProjection X X) _ (postSimplex (diagonalMap X) _ s)) 0 p _) 1) *
      b (Finsupp.single
        (interval (postSimplex (secondProjection X X) _ (postSimplex (diagonalMap X) _ s)) p q _) 1)
    rw [P202.AlexanderWhitney.post_comp, P202.AlexanderWhitney.post_comp, hf, hg]
    simp [postSimplex]
  exact LinearMap.congr_fun h c

/-- The cochain differential is the dual of a genuine chain complex. -/
theorem delta_squared (X : TopCat.{w}) (n : ℕ) :
    (delta R X (n+1)).comp (delta R X n) = 0 := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro c
  change a (boundary R R X n (boundary R R X (n+1) c)) = 0
  have h := congrArg (fun f : (complex R R X).X (n+2) ⟶ (complex R R X).X n => f c)
    ((complex R R X).d_comp_d (n+2) (n+1) n)
  change boundary R R X n (boundary R R X (n+1) c) = 0 at h
  rw [h, map_zero]

theorem oneCochain_cocycle (X : TopCat.{w}) : delta R X 0 (oneCochain R X) = 0 :=
  P202.SingularChains.augmentationLinear_boundary R R X

theorem cup_cocycle (X : TopCat.{w}) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R X q)
    (ha : delta R X p a = 0) (hb : delta R X q b = 0) :
    delta R X (p+q) (cup R X p q a b) = 0 := by
  rw [cup_leibniz, ha, hb, map_zero, LinearMap.zero_apply, map_zero]
  have hc : ∀ {m n : ℕ} (h : m=n), castCochain R h (0 : Cochain R X m) = 0 := by
    intro m n h; subst n; rfl
  rw [hc, hc, smul_zero, add_zero]

/-- Multiplying a coboundary on the left by a cocycle is a coboundary. -/
theorem cup_boundary_left (X : TopCat.{w}) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R X q) (hb : delta R X q b = 0) :
    castCochain R (by omega) (cup R X (p+1) q (delta R X p a) b) =
      delta R X (p+q) (cup R X p q a b) := by
  rw [cup_leibniz, hb, map_zero]
  have hc : ∀ {m n : ℕ} (h : m=n), castCochain R h (0 : Cochain R X m) = 0 := by
    intro m n h; subst n; rfl
  rw [hc, smul_zero, add_zero]

/-- The diagonal used to define cup is a chain map. -/
theorem chainDiagonal_boundary (X : TopCat.{w}) (n : ℕ) :
    (totalBoundary R X X n).comp (chainDiagonal R X (n+1)) =
      (chainDiagonal R X n).comp (chainBoundary R X n) := by
  apply LinearMap.ext
  intro c
  have h := congrArg (fun f : (complex R R X).X (n+1) ⟶
      (complex R R (productSpace X X)).X n => f c)
    ((chainMap R R (diagonalMap X)).comm (n+1) n)
  change boundary R R (productSpace X X) n
      (((chainMap R R (diagonalMap X)).f (n+1)).hom c) =
    ((chainMap R R (diagonalMap X)).f n).hom (boundary R R X n c) at h
  have haw := LinearMap.congr_fun (P202.AlexanderWhitney.chain_identity R X X n)
    (((chainMap R R (diagonalMap X)).f (n+1)).hom c)
  change totalBoundary R X X n (aw R X X (n+1)
      (((chainMap R R (diagonalMap X)).f (n+1)).hom c)) =
    aw R X X n (((chainMap R R (diagonalMap X)).f n).hom (boundary R R X n c))
  exact haw.trans (congrArg (aw R X X n) h)

/-- Naturality of D uses the actual diagonal map and both-factor AW naturality. -/
theorem chainDiagonal_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    (totalMap R f f n).comp (chainDiagonal R X n) =
      (chainDiagonal R Y n).comp ((chainMap R R f).f n).hom := by
  have htop : diagonalMap X ≫ productMap f f = f ≫ diagonalMap Y := rfl
  have hc : (((chainMap R R (productMap f f)).f n).hom).comp
      (((chainMap R R (diagonalMap X)).f n).hom) =
      (((chainMap R R (diagonalMap Y)).f n).hom).comp (((chainMap R R f).f n).hom) := by
    have h := congrArg (fun F => (F.f n).hom)
      (congrArg (chainMap R R) htop)
    simpa only [P202.SingularChains.chainMap_comp, HomologicalComplex.comp_f,
      ModuleCat.hom_comp] using h
  dsimp only [chainDiagonal]
  rw [← LinearMap.comp_assoc, P202.AlexanderWhitney.naturality, LinearMap.comp_assoc,
    hc, ← LinearMap.comp_assoc]

/-- On every singular basis simplex, D has exactly the usual front/back components. -/
theorem chainDiagonal_single (X : TopCat.{w}) (n : ℕ) (s : Simplex X n)
    (r : R) (i : Diagonal n) :
    chainDiagonal R X n (Finsupp.single s r) i = r •
      (Finsupp.single (interval s 0 i.val.1 (by have := i.property; omega)) 1 ⊗ₜ[R]
        Finsupp.single (interval s i.val.1 i.val.2 (by have := i.property; omega)) 1) := by
  change aw R X X n (((chainMap R R (diagonalMap X)).f n).hom (Finsupp.single s r)) i = _
  rw [P202.SingularChains.chainMap_single, P202.AlexanderWhitney.formula]
  have hf : diagonalMap X ≫ firstProjection X X = 𝟙 X := rfl
  have hg : diagonalMap X ≫ secondProjection X X = 𝟙 X := rfl
  change r • (Finsupp.single (interval
      (postSimplex (firstProjection X X) n (postSimplex (diagonalMap X) n s)) 0 i.val.1 _) 1 ⊗ₜ[R]
    Finsupp.single (interval
      (postSimplex (secondProjection X X) n (postSimplex (diagonalMap X) n s)) i.val.1 i.val.2 _) 1) = _
  rw [P202.AlexanderWhitney.post_comp, P202.AlexanderWhitney.post_comp, hf, hg]
  simp [postSimplex]

/-- The initial degree for acyclic-models induction: the two diagonals agree on vertices. -/
theorem diagonal_interchange_zero (X : TopCat.{w}) :
    chainDiagonal R X 0 - (interchange R X 0).comp (chainDiagonal R X 0) = 0 := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X 0)).ext
  intro s
  funext i
  rcases i with ⟨⟨p,q⟩,hi⟩
  have hp : p=0 := by dsimp at hi; omega
  have hq : q=0 := by dsimp at hi; omega
  subst p; subst q
  simp only [Finsupp.coe_basisSingleOne, LinearMap.sub_apply, Pi.sub_apply,
    LinearMap.comp_apply]
  change chainDiagonal R X 0 (Finsupp.single s 1) ⟨(0,0),rfl⟩ -
    (-1 : ℤ)^(0*0) • TensorProduct.comm R _ _
      (chainDiagonal R X 0 (Finsupp.single s 1) ⟨(0,0),rfl⟩) = 0
  rw [chainDiagonal_single]
  simp only [one_smul, Nat.mul_zero, pow_zero, TensorProduct.comm_tmul, sub_self]

lemma interchange_leftBoundary (X : TopCat.{w}) (p q : ℕ)
    (z : Summand R X X q (p+1)) :
    leftBoundary R X X p q (TensorProduct.comm R _ _ z) =
      TensorProduct.comm R _ _ (rightBoundary R X X q p z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

lemma interchange_rightBoundary (X : TopCat.{w}) (p q : ℕ)
    (z : Summand R X X (q+1) p) :
    rightBoundary R X X p q (TensorProduct.comm R _ _ z) =
      TensorProduct.comm R _ _ (leftBoundary R X X q p z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- The Koszul sign makes interchange a chain map, rather than a sign-free swap. -/
theorem interchange_boundary (X : TopCat.{w}) (n : ℕ) :
    (totalBoundary R X X n).comp (interchange R X (n+1)) =
      (interchange R X n).comp (totalBoundary R X X n) := by
  apply LinearMap.ext
  intro z
  funext i
  rcases i with ⟨⟨p,q⟩,hi⟩
  have hs : (-1 : ℤ)^p * (-1 : ℤ)^p = 1 := by rw [← mul_pow]; norm_num
  change leftBoundary R X X p q ((-1 : ℤ)^((p+1)*q) •
        TensorProduct.comm R _ _ (z ⟨(q,p+1),by omega⟩)) +
      (-1 : ℤ)^p • rightBoundary R X X p q ((-1 : ℤ)^(p*(q+1)) •
        TensorProduct.comm R _ _ (z ⟨(q+1,p),by omega⟩)) =
      (-1 : ℤ)^(p*q) • TensorProduct.comm R _ _
        (leftBoundary R X X q p (z ⟨(q+1,p),by omega⟩) +
          (-1 : ℤ)^q • rightBoundary R X X q p (z ⟨(q,p+1),by omega⟩))
  simp only [map_zsmul, interchange_leftBoundary, interchange_rightBoundary,
    map_add, smul_add, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
    pow_add, mul_smul]
  rw [smul_smul ((-1 : ℤ)^p) ((-1 : ℤ)^(p*q)), mul_comm ((-1 : ℤ)^p),
    mul_smul, smul_smul ((-1 : ℤ)^p), hs, one_smul]
  exact add_comm _ _

theorem interchange_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    (totalMap R f f n).comp (interchange R X n) =
      (interchange R Y n).comp (totalMap R f f n) := by
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map ((chainMap R R f).f i.val.1).hom
      ((chainMap R R f).f i.val.2).hom
      ((-1 : ℤ)^(i.val.1*i.val.2) • TensorProduct.comm R _ _
        (z ⟨(i.val.2,i.val.1),by have := i.property; omega⟩)) =
    (-1 : ℤ)^(i.val.1*i.val.2) • TensorProduct.comm R _ _
      (TensorProduct.map ((chainMap R R f).f i.val.2).hom
        ((chainMap R R f).f i.val.1).hom
        (z ⟨(i.val.2,i.val.1),by have := i.property; omega⟩))
  rw [map_zsmul]
  congr 1
  exact TensorProduct.map_comm ((chainMap R R f).f i.val.1).hom
    ((chainMap R R f).f i.val.2).hom _

theorem interchange_squared (X : TopCat.{w}) (n : ℕ) :
    (interchange R X n).comp (interchange R X n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  funext i
  change (-1 : ℤ)^(i.val.1*i.val.2) • TensorProduct.comm R _ _
    ((-1 : ℤ)^(i.val.2*i.val.1) • TensorProduct.comm R _ _ (z i)) = z i
  rw [map_zsmul, ← TensorProduct.comm_symm R (Chains R X i.val.1) (Chains R X i.val.2),
    LinearEquiv.symm_apply_apply, mul_comm i.val.2,
    smul_smul, ← mul_pow]
  norm_num

/-- Acyclic models for the missing homotopy: arbitrary nonempty contractible
spaces have no positive ordinary singular homology. -/
theorem contractible_positive_homology (X : TopCat.{w}) [Nonempty X]
    [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero ((complex R R X).homology n) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let p : X ⟶ P202Specs.SingularDegreeZero.point.{w} :=
    TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let q : P202Specs.SingularDegreeZero.point.{w} ⟶ X :=
    TopCat.ofHom (ContinuousMap.const _ x)
  have hpq : TopCat.Homotopy (p ≫ q) (𝟙 X) := H.symm
  have hqp : TopCat.Homotopy (q ≫ p) (𝟙 _) := ContinuousMap.Homotopy.refl _
  have := (P202.PrismHomotopy.homologyIso R R p q hpq hqp (n : ℤ)).1
  have hzero : CategoryTheory.Limits.IsZero (homology R R X (n : ℤ)) :=
    (asIso ((homologyFunctor R R (n : ℤ)).map p)).isZero_iff.mpr
      (P202.SingularDegreeZero.pointOrdinaryOther R R (n : ℤ) (by exact_mod_cast hn))
  exact (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).isZero_iff.mp hzero

/-- By Eilenberg–Zilber, the tensor convex models also
have no positive homology. No tensor contraction is assumed as a certificate. -/
theorem contractible_tensor_positive_homology
    (he : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (X Y : TopCat.{w}) [Nonempty X] [Nonempty Y]
    [ContractibleSpace X] [ContractibleSpace Y] (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero ((tensorComplex R X Y).homology n) := by
  have : Nonempty (productSpace X Y) := inferInstanceAs (Nonempty (X × Y))
  have : ContractibleSpace (productSpace X Y) := inferInstanceAs (ContractibleSpace (X × Y))
  obtain ⟨e, _, _⟩ := he R X Y
  exact (e.toHomologyIso n).isZero_iff.mp
    (contractible_positive_homology R (productSpace X Y) n hn)

/-- The precise positive-degree filling operation needed in an acyclic-models
induction. It is deduced from homotopy equivalence, not posited as a new premise. -/
theorem tensor_cycle_fills
    (he : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (X Y : TopCat.{w}) [Nonempty X] [Nonempty Y]
    [ContractibleSpace X] [ContractibleSpace Y] (n : ℕ)
    (z : Total R X Y (n+1)) (hz : totalBoundary R X Y n z = 0) :
    ∃ w : Total R X Y (n+2), totalBoundary R X Y (n+1) w = z := by
  have hex : (tensorComplex R X Y).ExactAt (n+1) :=
    ((tensorComplex R X Y).exactAt_iff_isZero_homology (n+1)).mpr
      (contractible_tensor_positive_homology R he X Y (n+1) (by omega))
  have hsc : ((tensorComplex R X Y).sc' (n+2) (n+1) n).Exact :=
    ((tensorComplex R X Y).exactAt_iff' (n+2) (n+1) n (by simp) (by simp)).mp hex
  have hz' : ((tensorComplex R X Y).sc' (n+2) (n+1) n).g z = 0 := by
    change (tensorComplex R X Y).d (n+1) n z = 0
    simpa [tensorComplex, ChainComplex.of_d] using hz
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp hsc z hz'
  change (tensorComplex R X Y).d (n+2) (n+1) w = z at hw
  change (tensorComplex R X Y).d ((n+1)+1) (n+1) w = z at hw
  exact ⟨w, by simpa [tensorComplex, ChainComplex.of_d] using hw⟩

/-- The front/back product satisfies all cochain identities. -/
theorem cochainLaws : cochainLaws_type.{u,w} := by
  intro R _
  exact ⟨fun X p q a b s => by simp,
    cup_leibniz R, cup_associative R, cup_unit R, cup_natural R, cup_diagonal R⟩

namespace DiagonalModels

/-- The universe-lifted universal simplex, in the same universe as X. -/
abbrev model (n : ℕ) : TopCat.{w} := SimplexCategory.toTop.obj ⦋n⦌

def universal (n : ℕ) : Simplex (model.{w} n) n := ⟨𝟙 _⟩

def evaluation {X : TopCat.{w}} {n : ℕ} (s : Simplex X n) : model n ⟶ X := s.down

@[simp] lemma evaluation_post {X Y : TopCat.{w}} (f : X ⟶ Y) {n : ℕ}
    (s : Simplex X n) : evaluation (postSimplex f n s) = evaluation s ≫ f := rfl

@[simp] lemma post_universal {X : TopCat.{w}} {n : ℕ} (s : Simplex X n) :
    postSimplex (evaluation s) n (universal n) = s := by
  apply ULift.ext
  rfl

instance model_contractible (n : ℕ) : ContractibleSpace (model.{w} n) := by
  have hc : ContractibleSpace (Convexity.StdSimplex ℝ (Fin (n+1))) := by
    apply (contractible_iff_id_nullhomotopic _).mpr
    refine ⟨Convexity.StdSimplex.single 0, ⟨?_⟩⟩
    refine
      { toFun := fun z => Convexity.convexCombPair (R := ℝ)
          (unitInterval.symm z.1) z.1 (unitInterval.nonneg _) (unitInterval.nonneg _)
          (by simp) z.2 (Convexity.StdSimplex.single 0)
        continuous_toFun := ?_
        map_zero_left := by intro x; simp
        map_one_left := by intro x; simp }
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
    apply continuous_pi
    intro i
    simp only [Function.comp_def, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  let : ContractibleSpace (SimplexCategory.toTop₀.obj ⦋n⦌) := hc
  exact (Homeomorph.ulift : model.{w} n ≃ₜ Convexity.StdSimplex ℝ (Fin (n+1))).contractibleSpace

/-- Extend a chosen value at the identity simplex by postcomposition. -/
def extend (n : ℕ) (z : Total R (model.{w} n) (model.{w} n) (n+1))
    (X : TopCat.{w}) : Chains R X n →ₗ[R] Total R X X (n+1) :=
  Finsupp.llift (Total R X X (n+1)) R R (Simplex X n)
    (fun s => totalMap R (evaluation s) (evaluation s) (n+1) z)

@[simp] lemma extend_single (n : ℕ) (z : Total R (model.{w} n) (model.{w} n) (n+1))
    (X : TopCat.{w}) (s : Simplex X n) :
    extend R n z X (Finsupp.single s 1) = totalMap R (evaluation s) (evaluation s) (n+1) z := by
  simp [extend, Finsupp.llift_apply, Finsupp.lift_apply]

lemma extend_natural (n : ℕ) (z : Total R (model.{w} n) (model.{w} n) (n+1))
    {X Y : TopCat.{w}} (f : X ⟶ Y) :
    (totalMap R f f (n+1)).comp (extend R n z X) =
      (extend R n z Y).comp ((chainMap R R f).f n).hom := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X n)).ext
  intro s
  simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply]
  rw [extend_single]
  erw [P202.SingularChains.chainMap_single R R f n s 1]
  change _ = extend R n z Y (Finsupp.single (postSimplex f n s) 1)
  rw [extend_single, evaluation_post, P202.AlexanderWhitney.totalMap_comp]
  rfl

/-- Two natural operations agree if they agree on the universal generator. -/
lemma natural_ext {n m : ℕ}
    (A B : ∀ X : TopCat.{w}, Chains R X n →ₗ[R] Total R X X m)
    (hA : ∀ {X Y : TopCat.{w}} (f : X ⟶ Y),
      (totalMap R f f m).comp (A X) = (A Y).comp ((chainMap R R f).f n).hom)
    (hB : ∀ {X Y : TopCat.{w}} (f : X ⟶ Y),
      (totalMap R f f m).comp (B X) = (B Y).comp ((chainMap R R f).f n).hom)
    (h : A (model n) (Finsupp.single (universal n) 1) =
      B (model n) (Finsupp.single (universal n) 1)) (X : TopCat.{w}) : A X = B X := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X n)).ext
  intro s
  have ha := LinearMap.congr_fun (hA (evaluation s)) (Finsupp.single (universal n) 1)
  have hb := LinearMap.congr_fun (hB (evaluation s)) (Finsupp.single (universal n) 1)
  have hgen : ((chainMap R R (evaluation s)).f n).hom (Finsupp.single (universal n) 1) =
      Finsupp.single s 1 := by
    rw [P202.SingularChains.chainMap_single R R (evaluation s) n (universal n) 1]
    change Finsupp.single (postSimplex (evaluation s) n (universal n)) 1 = _
    rw [post_universal]
  dsimp only [LinearMap.comp_apply] at ha hb
  erw [hgen] at ha hb
  change A X (Finsupp.single s 1) = B X (Finsupp.single s 1)
  exact ha.symm.trans ((congrArg (totalMap R (evaluation s) (evaluation s) m) h).trans hb)

def defect (X : TopCat.{w}) (n : ℕ) : Chains R X n →ₗ[R] Total R X X n :=
  chainDiagonal R X n - (interchange R X n).comp (chainDiagonal R X n)

lemma defect_zero (X : TopCat.{w}) : defect R X 0 = 0 := diagonal_interchange_zero R X

lemma defect_boundary (X : TopCat.{w}) (n : ℕ) :
    (totalBoundary R X X n).comp (defect R X (n+1)) =
      (defect R X n).comp (chainBoundary R X n) := by
  simp only [defect, LinearMap.comp_sub, LinearMap.sub_comp]
  rw [← LinearMap.comp_assoc, interchange_boundary, LinearMap.comp_assoc,
    chainDiagonal_boundary, ← LinearMap.comp_assoc]

lemma defect_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    (totalMap R f f n).comp (defect R X n) =
      (defect R Y n).comp ((chainMap R R f).f n).hom := by
  simp only [defect, LinearMap.comp_sub, LinearMap.sub_comp]
  rw [← LinearMap.comp_assoc, interchange_natural, LinearMap.comp_assoc,
    chainDiagonal_natural, ← LinearMap.comp_assoc]

/-- A stage retains exactly the compatibility needed for the next filling. -/
structure Stage (n : ℕ) where
  hom : ∀ X : TopCat.{w}, Chains R X n →ₗ[R] Total R X X (n+1)
  naturality : ∀ {X Y : TopCat.{w}} (f : X ⟶ Y),
    (totalMap R f f (n+1)).comp (hom X) =
      (hom Y).comp ((chainMap R R f).f n).hom
  boundary_boundary : ∀ X,
    ((totalBoundary R X X n).comp (hom X)).comp (chainBoundary R X n) =
      (defect R X n).comp (chainBoundary R X n)

def initial : Stage.{u,w} R 0 where
  hom _ := 0
  naturality _ := by simp
  boundary_boundary X := by simp [defect_zero]

lemma chainBoundary_squared (X : TopCat.{w}) (n : ℕ) :
    (chainBoundary R X n).comp (chainBoundary R X (n+1)) = 0 := by
  exact congrArg ModuleCat.Hom.hom ((complex R R X).d_comp_d (n+2) (n+1) n)

lemma chainBoundary_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    (chainBoundary R Y n).comp ((chainMap R R f).f (n+1)).hom =
      (((chainMap R R f).f n).hom).comp (chainBoundary R X n) := by
  exact congrArg ModuleCat.Hom.hom ((chainMap R R f).comm (n+1) n)

def residual {n : ℕ} (A : Stage.{u,w} R n) (X : TopCat.{w}) :
    Chains R X (n+1) →ₗ[R] Total R X X (n+1) :=
  defect R X (n+1) - (A.hom X).comp (chainBoundary R X n)

lemma residual_natural {n : ℕ} (A : Stage.{u,w} R n)
    {X Y : TopCat.{w}} (f : X ⟶ Y) :
    (totalMap R f f (n+1)).comp (residual R A X) =
      (residual R A Y).comp ((chainMap R R f).f (n+1)).hom := by
  simp only [residual, LinearMap.comp_sub, LinearMap.sub_comp]
  rw [← LinearMap.comp_assoc, A.naturality, LinearMap.comp_assoc,
    ← chainBoundary_natural, ← LinearMap.comp_assoc, defect_natural]

lemma residual_cycle {n : ℕ} (A : Stage.{u,w} R n) (X : TopCat.{w}) :
    (totalBoundary R X X n).comp (residual R A X) = 0 := by
  simp only [residual, LinearMap.comp_sub]
  rw [← LinearMap.comp_assoc, A.boundary_boundary, defect_boundary]
  exact sub_self ((defect R X n).comp (chainBoundary R X n))

/-- Chosen fillings are only made on universal simplices. -/
def filling (he : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    {n : ℕ} (A : Stage.{u,w} R n) : Total R (model.{w} (n+1)) (model.{w} (n+1)) (n+2) :=
  Classical.choose (tensor_cycle_fills R he (model (n+1)) (model (n+1)) n
    (residual R A (model (n+1)) (Finsupp.single (universal (n+1)) 1))
    (LinearMap.congr_fun (residual_cycle R A (model (n+1))) _))

lemma filling_boundary (he : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    {n : ℕ} (A : Stage.{u,w} R n) :
    totalBoundary R (model (n+1)) (model (n+1)) (n+1) (filling R he A) =
      residual R A (model (n+1)) (Finsupp.single (universal (n+1)) 1) :=
  Classical.choose_spec (tensor_cycle_fills R he (model (n+1)) (model (n+1)) n
    (residual R A (model (n+1)) (Finsupp.single (universal (n+1)) 1))
    (LinearMap.congr_fun (residual_cycle R A (model (n+1))) _))

lemma extend_filling_boundary (he : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    {n : ℕ} (A : Stage.{u,w} R n) (X : TopCat.{w}) :
    (totalBoundary R X X (n+1)).comp (extend R (n+1) (filling R he A) X) =
      residual R A X := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X (n+1))).ext
  intro s
  simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, extend_single]
  have hb := LinearMap.congr_fun (P202.AlexanderWhitney.totalMap_boundary R
    (evaluation s) (evaluation s) (n+1)) (filling R he A)
  dsimp only [LinearMap.comp_apply] at hb
  rw [hb, filling_boundary]
  have hn := LinearMap.congr_fun (residual_natural R A (evaluation s))
    (Finsupp.single (universal (n+1)) 1)
  dsimp only [LinearMap.comp_apply] at hn
  erw [P202.SingularChains.chainMap_single R R (evaluation s) (n+1) (universal (n+1)) 1] at hn
  change _ = residual R A X (Finsupp.single (postSimplex (evaluation s) (n+1) (universal (n+1))) 1) at hn
  rw [post_universal] at hn
  exact hn

def step (he : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    {n : ℕ} (A : Stage.{u,w} R n) : Stage.{u,w} R (n+1) where
  hom := extend R (n+1) (filling R he A)
  naturality := extend_natural R (n+1) (filling R he A)
  boundary_boundary X := by
    rw [extend_filling_boundary]
    simp only [residual, LinearMap.sub_comp, LinearMap.comp_assoc]
    rw [chainBoundary_squared, LinearMap.comp_zero]
    exact sub_zero ((defect R X (n+1)).comp (chainBoundary R X (n+1)))

def stages (he : P202Specs.EilenbergZilber.equivalence_type.{u,w}) (n : ℕ) : Stage.{u,w} R n :=
  match n with
  | 0 => initial R
  | n+1 => step R he (stages he n)

lemma stages_succ (he : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (X : TopCat.{w}) (n : ℕ) :
    defect R X (n+1) =
      (totalBoundary R X X (n+1)).comp ((stages R he (n+1)).hom X) +
        ((stages R he n).hom X).comp (chainBoundary R X n) := by
  change defect R X (n+1) =
    (totalBoundary R X X (n+1)).comp (extend R (n+1) (filling R he (stages R he n)) X) + _
  rw [extend_filling_boundary]
  exact (sub_add_cancel (defect R X (n+1))
    (((stages R he n).hom X).comp (chainBoundary R X n))).symm

/-- The complete natural interchange homotopy, obtained by acyclic models. -/
def diagonalHomotopy (he : P202Specs.EilenbergZilber.equivalence_type.{u,w}) :
    DiagonalHomotopy.{u,w} R where
  hom X n := (stages R he n).hom X
  zero X := by change defect R X 0 = _; simp [stages, initial, defect_zero]
  succ X n := stages_succ R he X n
  naturality f n := (stages R he n).naturality f

end DiagonalModels

/-- The chain diagonal is naturally homotopic to its Koszul interchange. -/
theorem diagonalHomotopy : diagonalHomotopy_type.{u,w} := by
  intro R _
  exact ⟨DiagonalModels.diagonalHomotopy R P202.EilenbergZilber.equivalence⟩

/-- Evaluation of an entire diagonal in fixed bidegree. -/
def totalPairing {X : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R X q) (n : ℕ) (h : p+q=n) :
    Total R X X n →ₗ[R] R :=
  (tensorPairing R a b).comp (LinearMap.proj (R := R)
    (φ := fun i : Diagonal n => Summand R X X i.val.1 i.val.2) ⟨(p,q),h⟩)

lemma tensorPairing_leftBoundary {X : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R X q) (ha : delta R X p a = 0)
    (z : Summand R X X (p+1) q) :
    tensorPairing R a b (leftBoundary R X X p q z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul c d =>
    change a (chainBoundary R X p c) * b d = 0
    have h := LinearMap.congr_fun ha c
    change a (chainBoundary R X p c) = 0 at h
    rw [h, zero_mul]
  | add z z' hz hz' => simp only [map_add, hz, hz', add_zero]

lemma tensorPairing_rightBoundary {X : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R X q) (hb : delta R X q b = 0)
    (z : Summand R X X p (q+1)) :
    tensorPairing R a b (rightBoundary R X X p q z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul c d =>
    change a c * b (chainBoundary R X q d) = 0
    have h := LinearMap.congr_fun hb d
    change b (chainBoundary R X q d) = 0 at h
    rw [h, mul_zero]
  | add z z' hz hz' => simp only [map_add, hz, hz', add_zero]

lemma totalPairing_boundary {X : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R X q)
    (ha : delta R X p a = 0) (hb : delta R X q b = 0)
    (n : ℕ) (h : p+q=n) (z : Total R X X (n+1)) :
    totalPairing R a b n h (totalBoundary R X X n z) = 0 := by
  change tensorPairing R a b
    (leftBoundary R X X p q (z ⟨(p+1,q),by omega⟩) +
      (-1 : ℤ)^p • rightBoundary R X X p q (z ⟨(p,q+1),by omega⟩)) = 0
  rw [map_add, map_zsmul, tensorPairing_leftBoundary R a b ha,
    tensorPairing_rightBoundary R a b hb, smul_zero, add_zero]

lemma tensorPairing_comm {X : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R X q) (z : Summand R X X q p) :
    tensorPairing R a b (TensorProduct.comm R _ _ z) = tensorPairing R b a z := by
  induction z using TensorProduct.inductionOn with
  | tmul c d => exact mul_comm _ _
  | add z z' hz hz' => simp only [map_add, hz, hz']

lemma totalPairing_interchange {X : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R X q) (n : ℕ) (h : p+q=n)
    (z : Total R X X n) :
    totalPairing R a b n h (interchange R X n z) =
      (-1 : ℤ)^(p*q) • totalPairing R b a n (by omega) z := by
  change tensorPairing R a b ((-1 : ℤ)^(p*q) • TensorProduct.comm R _ _
    (z ⟨(q,p),by omega⟩)) = _
  rw [map_zsmul, tensorPairing_comm]
  rfl

lemma totalPairing_diagonal {X : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R X q) (n : ℕ) (h : p+q=n)
    (c : Chains R X n) :
    totalPairing R a b n h (chainDiagonal R X n c) =
      castCochain R h (cup R X p q a b) c := by
  subst n
  exact (cup_diagonal R X p q a b c).symm

/-- The homotopy evaluated by cocycles gives the actual coboundary primitive
for the graded commutator, in every positive total degree. -/
def commutativityPrimitive (H : DiagonalHomotopy.{u,w} R)
    {X : TopCat.{w}} {p q : ℕ} (a : Cochain R X p) (b : Cochain R X q)
    (n : ℕ) (h : p+q=n+1) : Cochain R X n :=
  (totalPairing R a b (n+1) h).comp (H.hom X n)

theorem cup_commutator_positive (H : DiagonalHomotopy.{u,w} R)
    {X : TopCat.{w}} {p q : ℕ} (a : Cochain R X p) (b : Cochain R X q)
    (ha : delta R X p a = 0) (hb : delta R X q b = 0)
    (n : ℕ) (h : p+q=n+1) :
    castCochain R h (cup R X p q a b) -
      (-1 : ℤ)^(p*q) • castCochain R (by omega) (cup R X q p b a) =
        delta R X n (commutativityPrimitive R H a b n h) := by
  apply LinearMap.ext
  intro c
  have he := congrArg (totalPairing R a b (n+1) h) (LinearMap.congr_fun (H.succ X n) c)
  dsimp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply] at he
  rw [map_sub, map_add, totalPairing_interchange, totalPairing_diagonal,
    totalPairing_diagonal, totalPairing_boundary R a b ha hb, zero_add] at he
  exact he

theorem cup_commutator_zero (H : DiagonalHomotopy.{u,w} R)
    {X : TopCat.{w}} (a b : Cochain R X 0)
    (ha : delta R X 0 a = 0) (hb : delta R X 0 b = 0) :
    cup R X 0 0 a b = cup R X 0 0 b a := by
  apply LinearMap.ext
  intro c
  have he := congrArg (totalPairing R a b 0 rfl) (LinearMap.congr_fun (H.zero X) c)
  dsimp only [LinearMap.sub_apply, LinearMap.comp_apply] at he
  rw [map_sub, totalPairing_interchange, totalPairing_diagonal, totalPairing_diagonal,
    totalPairing_boundary R a b ha hb] at he
  simpa only [castCochain_rfl, Nat.mul_zero, pow_zero, one_smul, sub_eq_zero] using he

universe v
section GradedPackaging
variable (R : Type u) [CommRing R] (A : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (μ : ∀ p q, A p →ₗ[R] A q →ₗ[R] A (p+q)) (e : A 0)
variable (hl : ∀ p (a : A p), GradedMonoid.mk (0+p) (μ 0 p e a) = GradedMonoid.mk p a)
variable (hr : ∀ p (a : A p), GradedMonoid.mk (p+0) (μ p 0 a e) = GradedMonoid.mk p a)
variable (ha : ∀ p q r (a : A p) (b : A q) (c : A r),
 GradedMonoid.mk ((p+q)+r) (μ (p+q) r (μ p q a b) c) =
 GradedMonoid.mk (p+(q+r)) (μ p (q+r) a (μ q r b c)))

@[instance_reducible] def gradedRingOfBilinear : DirectSum.GRing A := by
  letI : GradedMonoid.GOne A := ⟨e⟩
  letI : GradedMonoid.GMul A := ⟨fun {i j} a b => μ i j a b⟩
  exact {
  mul {i j} a b := μ i j a b
  one := e
  mul_zero a := map_zero _
  zero_mul b := by simp
  mul_add a b c := map_add _ _ _
  add_mul a b c := by simp
  one_mul a := by rcases a with ⟨p,a⟩; exact hl p a
  mul_one a := by rcases a with ⟨p,a⟩; exact hr p a
  mul_assoc a b c := by rcases a with ⟨p,a⟩; rcases b with ⟨q,b⟩; rcases c with ⟨r,c⟩; exact ha p q r a b c
  natCast n := n • e
  natCast_zero := zero_nsmul e
  natCast_succ n := by simp [add_nsmul]
  intCast z := z • e
  intCast_ofNat n := by simp
  intCast_negSucc_ofNat n := by
    change (-(↑(n+1) : ℤ)) • e = _
    rw [neg_smul, natCast_zsmul]
  }

@[instance_reducible] def gradedAlgebraOfBilinear : letI := gradedRingOfBilinear R A μ e hl hr ha
    DirectSum.GAlgebra R A := by
  letI := gradedRingOfBilinear R A μ e hl hr ha
  have hee : μ 0 0 e e = e := by
    have h := hl 0 e
    exact (Sigma.mk.inj_iff.mp h).2.eq
  refine { toFun := {
             toFun := fun r => r • e
             map_zero' := zero_smul R e
             map_add' := fun r s => add_smul r s e }
           map_one := one_smul R e
           map_mul := ?_
           commutes := ?_
           smul_def := ?_ }
  · intro r s
    change GradedMonoid.mk 0 ((r*s) • e) = GradedMonoid.mk (0+0) (μ 0 0 (r • e) (s • e))
    simp only [map_smul, LinearMap.smul_apply, hee, smul_smul, mul_comm r s]
  · intro r ⟨p,a⟩
    change GradedMonoid.mk (0+p) (μ 0 p (r • e) a) = GradedMonoid.mk (p+0) (μ p 0 a (r • e))
    simp only [map_smul, LinearMap.smul_apply]
    exact (congrArg (fun x : GradedMonoid A => r • x) (hl p a)).trans
      (congrArg (fun x : GradedMonoid A => r • x) (hr p a)).symm
  · intro r ⟨p,a⟩
    change GradedMonoid.mk p (r • a) = GradedMonoid.mk (0+p) (μ 0 p (r • e) a)
    simp only [map_smul, LinearMap.smul_apply]
    exact (congrArg (fun x : GradedMonoid A => r • x) (hl p a)).symm

end GradedPackaging

section GradedMaps
variable (R : Type u) [CommRing R] (A B : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
variable [DirectSum.GRing A] [DirectSum.GAlgebra R A]
variable [DirectSum.GRing B] [DirectSum.GAlgebra R B]

def gradedAlgebraMap (F : ∀ n, A n →ₗ[R] B n)
    (hOne : F 0 GradedMonoid.GOne.one = GradedMonoid.GOne.one)
    (hMul : ∀ p q (a : A p) (b : A q),
      F (p+q) (GradedMonoid.GMul.mul a b) = GradedMonoid.GMul.mul (F p a) (F q b)) :
    (⨁ n, A n) →ₐ[R] ⨁ n, B n :=
  DirectSum.toAlgebra R A (fun n => (DirectSum.lof R ℕ B n).comp (F n))
    (by change DirectSum.of B 0 (F 0 GradedMonoid.GOne.one) = 1; rw [hOne]; rfl)
    (by
      intro p q a b
      change DirectSum.of B (p+q) (F (p+q) (GradedMonoid.GMul.mul a b)) = _
      rw [hMul]
      exact (DirectSum.of_mul_of _ _).symm)

@[simp] theorem gradedAlgebraMap_of (F : ∀ n, A n →ₗ[R] B n) (hOne) (hMul)
    (n : ℕ) (a : A n) :
    gradedAlgebraMap R A B F hOne hMul (DirectSum.of A n a) =
      DirectSum.of B n (F n a) := by
  change DirectSum.toAddMonoid (fun i => ((DirectSum.lof R ℕ B i).comp (F i)).toAddMonoidHom) (DirectSum.of A n a) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

end GradedMaps

lemma ordinaryCochainsEquiv_d (X : TopCat.{w}) (n : ℕ)
    (a : (ordinaryCochains R R X).X (n : ℤ)) :
    ordinaryCochainsEquiv R R X (n+1)
      ((ordinaryCochains R R X).d (n : ℤ) ((n+1 : ℕ) : ℤ) a) =
        delta R X n (ordinaryCochainsEquiv R R X n a) := by
  apply LinearMap.ext
  intro c
  change ordinaryCochainsEquiv R R X (n+1)
      ((ordinaryCochains R R X).d (n : ℤ) ((n+1 : ℕ) : ℤ) a) c =
        ordinaryCochainsEquiv R R X n a (boundary R R X n c)
  exact
    by
      have h := P202.CohomologyPairs.natural_coboundary R R X n (ordinaryCochainsEquiv R R X n a) c
      rw [LinearEquiv.symm_apply_apply] at h
      exact h

lemma cocycleValue_delta (X : TopCat.{w}) (n : ℕ)
    (a : (ordinaryCochains R R X).cycles (n : ℤ)) :
    delta R X n (cocycleValue R X n a) = 0 := by
  rw [cocycleValue, ← ordinaryCochainsEquiv_d]
  have h := congrArg (fun f => f a)
    ((ordinaryCochains R R X).iCycles_d (n : ℤ) ((n+1 : ℕ) : ℤ))
  change (ordinaryCochains R R X).d (n : ℤ) ((n+1 : ℕ) : ℤ)
    ((ordinaryCochains R R X).iCycles (n : ℤ) a) = 0 at h
  rw [h, map_zero]

lemma ordinaryCochainsEquiv_d_zero (X : TopCat.{w}) (n : ℕ)
    (a : Cochain R X n) (ha : delta R X n a = 0) :
    (ordinaryCochains R R X).d (n : ℤ) ((n+1 : ℕ) : ℤ)
      ((ordinaryCochainsEquiv R R X n).symm a) = 0 := by
  apply (ordinaryCochainsEquiv R R X (n+1)).injective
  rw [ordinaryCochainsEquiv_d, LinearEquiv.apply_symm_apply, ha, map_zero]

/-- A cochain cycle gives an actual cycle in ordinary singular cochains. -/
def cycleOfCochain (X : TopCat.{w}) (n : ℕ) (a : Cochain R X n)
    (ha : delta R X n a = 0) : (ordinaryCochains R R X).cycles (n : ℤ) :=
  (((ordinaryCochains R R X).sc (n : ℤ)).moduleCatCyclesIso.inv)
    ⟨(ordinaryCochainsEquiv R R X n).symm a, by
      change (ordinaryCochains R R X).d (n : ℤ) (((ComplexShape.down ℤ).symm).next (n : ℤ))
        ((ordinaryCochainsEquiv R R X n).symm a) = 0
      rw [((ComplexShape.down ℤ).symm).next_eq' (show ((ComplexShape.down ℤ).symm).Rel (n : ℤ) ((n+1 : ℕ) : ℤ) by simp)]
      exact ordinaryCochainsEquiv_d_zero R X n a ha⟩

@[simp] lemma cocycleValue_cycleOfCochain (X : TopCat.{w}) (n : ℕ)
    (a : Cochain R X n) (ha : delta R X n a = 0) :
    cocycleValue R X n (cycleOfCochain R X n a ha) = a := by
  unfold cocycleValue cycleOfCochain
  have h := congrArg (fun f => f
    (⟨(ordinaryCochainsEquiv R R X n).symm a, by
      change (ordinaryCochains R R X).d (n : ℤ) (((ComplexShape.down ℤ).symm).next (n : ℤ))
        ((ordinaryCochainsEquiv R R X n).symm a) = 0
      rw [((ComplexShape.down ℤ).symm).next_eq' (show ((ComplexShape.down ℤ).symm).Rel (n : ℤ) ((n+1 : ℕ) : ℤ) by simp)]
      exact ordinaryCochainsEquiv_d_zero R X n a ha⟩ :
      (((ordinaryCochains R R X).sc (n : ℤ)).g.hom.ker)))
    (((ordinaryCochains R R X).sc (n : ℤ)).moduleCatCyclesIso_inv_iCycles)
  change (ordinaryCochains R R X).iCycles (n : ℤ) _ =
    (ordinaryCochainsEquiv R R X n).symm a at h
  exact (congrArg (ordinaryCochainsEquiv R R X n) h).trans
    ((ordinaryCochainsEquiv R R X n).apply_symm_apply a)

lemma cocycleValue_injective (X : TopCat.{w}) (n : ℕ) :
    Function.Injective (cocycleValue R X n) := by
  intro a b hab
  apply (ModuleCat.mono_iff_injective ((ordinaryCochains R R X).iCycles (n : ℤ))).mp
    inferInstance
  exact (ordinaryCochainsEquiv R R X n).injective hab

lemma shortComplex_homologyπ_eq_zero_iff (S : ShortComplex (ModuleCat.{v} R)) (a : S.cycles) :
    S.homologyπ a = 0 ↔ ∃ x : S.X₁, S.f x = S.iCycles a := by
  let e := S.moduleCatCyclesIso.toLinearEquiv
  have hi : ∀ z : S.cycles, (e z).val = S.iCycles z := by
    intro z
    exact congrArg (fun f : S.cycles ⟶ S.X₂ => f z) S.moduleCatCyclesIso_hom_i
  have hπ : S.moduleCatHomologyIso.hom (S.homologyπ a) =
      S.moduleCatLeftHomologyData.π (e a) := by
    exact congrArg (fun f : S.cycles ⟶ _ => f a) S.π_moduleCatCyclesIso_hom
  constructor
  · intro ha
    rw [ha, map_zero] at hπ
    have hz : Submodule.Quotient.mk (e a) = (0 : S.g.hom.ker ⧸ S.moduleCatToCycles.range) := hπ.symm
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    exact ⟨x, (congrArg Subtype.val hx).trans (hi a)⟩
  · rintro ⟨x, hx⟩
    have he : S.moduleCatToCycles x = e a := by
      apply Subtype.ext
      exact hx.trans (hi a).symm
    have hz : Submodule.Quotient.mk (e a) = (0 : S.g.hom.ker ⧸ S.moduleCatToCycles.range) :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, he⟩
    apply (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).mp inferInstance
    rw [hπ, map_zero]
    exact hz

def cocycleValueLinear (X : TopCat.{w}) (n : ℕ) :
    (ordinaryCochains R R X).cycles (n : ℤ) →ₗ[R] Cochain R X n :=
  (ordinaryCochainsEquiv R R X n).toLinearMap.comp
    ((ordinaryCochains R R X).iCycles (n : ℤ)).hom

def cycleCochainEquiv (X : TopCat.{w}) (n : ℕ) :
    (ordinaryCochains R R X).cycles (n : ℤ) ≃ₗ[R] (delta R X n).ker where
  toFun a := ⟨cocycleValue R X n a, cocycleValue_delta R X n a⟩
  map_add' a b := Subtype.ext ((cocycleValueLinear R X n).map_add a b)
  map_smul' r a := Subtype.ext ((cocycleValueLinear R X n).map_smul r a)
  invFun a := cycleOfCochain R X n a.val a.property
  left_inv a := by
    apply cocycleValue_injective R X n
    exact cocycleValue_cycleOfCochain R X n _ _
  right_inv a := by
    apply Subtype.ext
    exact cocycleValue_cycleOfCochain R X n _ _

/-- The constant degree-zero cochain lifted to the ordinary dual complex. -/
def unitCycle (X : TopCat.{w}) : (ordinaryCochains R R X).cycles 0 :=
  cycleOfCochain R X 0 (oneCochain R X)
    (P202.SingularChains.augmentationLinear_boundary R R X)

@[simp] lemma cocycleValue_unitCycle (X : TopCat.{w}) :
    cocycleValue R X 0 (unitCycle R X) = oneCochain R X :=
  cocycleValue_cycleOfCochain R X 0 _ _

lemma homologyπ_eq_zero_iff_positive (X : TopCat.{w}) (n : ℕ)
    (a : (ordinaryCochains R R X).cycles ((n+1 : ℕ) : ℤ)) :
    (ordinaryCochains R R X).homologyπ ((n+1 : ℕ) : ℤ) a = 0 ↔
      ∃ c : Cochain R X n, delta R X n c = cocycleValue R X (n+1) a := by
  change ((ordinaryCochains R R X).sc ((n+1 : ℕ) : ℤ)).homologyπ a = 0 ↔ _
  rw [shortComplex_homologyπ_eq_zero_iff]
  have hp : ((ComplexShape.down ℤ).symm).prev ((n+1 : ℕ) : ℤ) = (n : ℤ) :=
    ((ComplexShape.down ℤ).symm).prev_eq' (by simp)
  constructor
  · rintro ⟨x, hx⟩
    change (ordinaryCochains R R X).X (((ComplexShape.down ℤ).symm).prev ((n+1 : ℕ) : ℤ)) at x
    change (ordinaryCochains R R X).d _ ((n+1 : ℕ) : ℤ) x =
      (ordinaryCochains R R X).iCycles ((n+1 : ℕ) : ℤ) a at hx
    revert x
    rw [hp]
    intro x hx
    refine ⟨ordinaryCochainsEquiv R R X n x, ?_⟩
    rw [← ordinaryCochainsEquiv_d, hx]
    rfl
  · rintro ⟨c, hc⟩
    have h : (ordinaryCochains R R X).d (n : ℤ) ((n+1 : ℕ) : ℤ)
        ((ordinaryCochainsEquiv R R X n).symm c) =
          (ordinaryCochains R R X).iCycles ((n+1 : ℕ) : ℤ) a := by
      apply (ordinaryCochainsEquiv R R X (n+1)).injective
      rw [ordinaryCochainsEquiv_d, LinearEquiv.apply_symm_apply, hc]
      rfl
    change ∃ x : (ordinaryCochains R R X).X (((ComplexShape.down ℤ).symm).prev ((n+1 : ℕ) : ℤ)),
      (ordinaryCochains R R X).d _ ((n+1 : ℕ) : ℤ) x = _
    rw [hp]
    exact ⟨(ordinaryCochainsEquiv R R X n).symm c, h⟩

lemma homologyπ_eq_zero_of_delta (X : TopCat.{w}) (t n : ℕ)
    (a : (ordinaryCochains R R X).cycles (t : ℤ)) (h : t=n+1)
    (c : Cochain R X n)
    (hc : castCochain R h (cocycleValue R X t a) = delta R X n c) :
    (ordinaryCochains R R X).homologyπ (t : ℤ) a = 0 := by
  subst t
  exact (homologyπ_eq_zero_iff_positive R X n a).mpr ⟨c, hc.symm⟩

section ProductLaws
variable (X : TopCat.{w})

lemma homology_sigma_eq_of_cocycleValue {p q : ℕ} (h : p=q)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R X).cycles (q : ℤ))
    (hab : castCochain R h (cocycleValue R X p a) = cocycleValue R X q b) :
    GradedMonoid.mk (A := H R X) p ((ordinaryCochains R R X).homologyπ (p : ℤ) a) =
      GradedMonoid.mk (A := H R X) q ((ordinaryCochains R R X).homologyπ (q : ℤ) b) := by
  subst q
  have he : a=b := cocycleValue_injective R X p hab
  subst b
  rfl

lemma represented_product_laws
    (μ : ∀ p q, H R X p →ₗ[R] H R X q →ₗ[R] H R X (p+q))
    (e : H R X 0)
    (hrep : ∀ (p q : ℕ) (a : (ordinaryCochains R R X).cycles (p : ℤ))
        (b : (ordinaryCochains R R X).cycles (q : ℤ)),
      ∃ c : (ordinaryCochains R R X).cycles ((p+q : ℕ) : ℤ),
        cocycleValue R X (p+q) c = cup R X p q (cocycleValue R X p a) (cocycleValue R X q b) ∧
        μ p q ((ordinaryCochains R R X).homologyπ (p : ℤ) a)
          ((ordinaryCochains R R X).homologyπ (q : ℤ) b) =
            (ordinaryCochains R R X).homologyπ ((p+q : ℕ) : ℤ) c)
    (he : ∃ a : (ordinaryCochains R R X).cycles 0,
      cocycleValue R X 0 a = oneCochain R X ∧
        e = (ordinaryCochains R R X).homologyπ 0 a) :
    (∀ p (a : H R X p), GradedMonoid.mk (A := H R X) (0+p) (μ 0 p e a) = GradedMonoid.mk (A := H R X) p a) ∧
    (∀ p (a : H R X p), GradedMonoid.mk (A := H R X) (p+0) (μ p 0 a e) = GradedMonoid.mk (A := H R X) p a) ∧
    (∀ p q r (a : H R X p) (b : H R X q) (c : H R X r),
      GradedMonoid.mk (A := H R X) ((p+q)+r) (μ (p+q) r (μ p q a b) c) =
      GradedMonoid.mk (A := H R X) (p+(q+r)) (μ p (q+r) a (μ q r b c))) := by
  have hs (n : ℕ) : Function.Surjective ((ordinaryCochains R R X).homologyπ (n : ℤ)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨one, hone, he⟩ := he
  refine ⟨?_,?_,?_⟩
  · intro p a
    obtain ⟨a,rfl⟩ := hs p a
    rw [he]
    obtain ⟨c,hc,hprod⟩ := hrep 0 p one a
    erw [hprod]
    apply homology_sigma_eq_of_cocycleValue R X (Nat.zero_add p) c a
    rw [hc, hone]
    exact (cup_unit R X p _).1
  · intro p a
    obtain ⟨a,rfl⟩ := hs p a
    rw [he]
    obtain ⟨c,hc,hprod⟩ := hrep p 0 a one
    erw [hprod]
    apply homology_sigma_eq_of_cocycleValue R X (Nat.add_zero p) c a
    rw [hc, hone]
    exact (cup_unit R X p _).2
  · intro p q r a b c
    obtain ⟨a,rfl⟩ := hs p a
    obtain ⟨b,rfl⟩ := hs q b
    obtain ⟨c,rfl⟩ := hs r c
    obtain ⟨ab,hab,hpab⟩ := hrep p q a b
    obtain ⟨bc,hbc,hpbc⟩ := hrep q r b c
    obtain ⟨abc,habc,hpabc⟩ := hrep (p+q) r ab c
    obtain ⟨abc',habc',hpabc'⟩ := hrep p (q+r) a bc
    rw [hpab,hpbc,hpabc,hpabc']
    apply homology_sigma_eq_of_cocycleValue R X (Nat.add_assoc p q r) abc abc'
    rw [habc,habc',hab,hbc]
    exact cup_associative R X p q r _ _ _

end ProductLaws

def castOrdinaryCycle {X : TopCat.{w}} {p q : ℕ} (h : p=q)
    (a : (ordinaryCochains R R X).cycles (p : ℤ)) :
    (ordinaryCochains R R X).cycles (q : ℤ) := h ▸ a

@[simp] lemma cocycleValue_castOrdinaryCycle {X : TopCat.{w}} {p q : ℕ} (h : p=q)
    (a : (ordinaryCochains R R X).cycles (p : ℤ)) :
    cocycleValue R X q (castOrdinaryCycle R h a) = castCochain R h (cocycleValue R X p a) := by
  subst q
  rfl

lemma gradedClass_smul_castOrdinaryCycle {X : TopCat.{w}} {p q : ℕ} (h : p=q)
    (a : (ordinaryCochains R R X).cycles (p : ℤ)) (s : ℤ) :
    GradedMonoid.mk (A := H R X) q (s • (ordinaryCochains R R X).homologyπ (q : ℤ) (castOrdinaryCycle R h a)) =
      GradedMonoid.mk (A := H R X) p (s • (ordinaryCochains R R X).homologyπ (p : ℤ) a) := by
  subst q
  rfl

theorem cup_homology_commute_of_representatives (hD : DiagonalHomotopy.{u,w} R)
    (X : TopCat.{w}) (p q : ℕ)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R X).cycles (q : ℤ))
    (c : (ordinaryCochains R R X).cycles ((p+q : ℕ) : ℤ))
    (d : (ordinaryCochains R R X).cycles ((q+p : ℕ) : ℤ))
    (hc : cocycleValue R X (p+q) c = cup R X p q (cocycleValue R X p a) (cocycleValue R X q b))
    (hd : cocycleValue R X (q+p) d = cup R X q p (cocycleValue R X q b) (cocycleValue R X p a)) :
    GradedMonoid.mk (A := H R X) (p+q) ((ordinaryCochains R R X).homologyπ ((p+q : ℕ) : ℤ) c) =
      GradedMonoid.mk (A := H R X) (q+p) ((-1 : ℤ)^(p*q) • (ordinaryCochains R R X).homologyπ ((q+p : ℕ) : ℤ) d) := by
  let d' := castOrdinaryCycle R (Nat.add_comm q p) d
  have hd' : cocycleValue R X (p+q) d' =
      castCochain R (Nat.add_comm q p) (cup R X q p (cocycleValue R X q b) (cocycleValue R X p a)) := by
    dsimp only [d']
    rw [cocycleValue_castOrdinaryCycle, hd]
  have heq : (ordinaryCochains R R X).homologyπ ((p+q : ℕ) : ℤ) c =
      (-1 : ℤ)^(p*q) • (ordinaryCochains R R X).homologyπ ((p+q : ℕ) : ℤ) d' := by
    by_cases hzero : p+q=0
    · have hp : p=0 := by omega
      have hq : q=0 := by omega
      subst p
      subst q
      have hcd : c=d' := by
        apply cocycleValue_injective R X 0
        rw [hc, hd']
        simpa only [castCochain_rfl] using
          cup_commutator_zero R hD (cocycleValue R X 0 a) (cocycleValue R X 0 b)
            (cocycleValue_delta R X 0 a) (cocycleValue_delta R X 0 b)
      simp only [hcd, Nat.mul_zero, pow_zero, one_smul]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, p+q=n+1 := ⟨p+q-1, by omega⟩
      apply sub_eq_zero.mp
      rw [← map_zsmul, ← map_sub]
      apply homologyπ_eq_zero_of_delta R X (p+q) n _ hn
        (commutativityPrimitive R hD (cocycleValue R X p a) (cocycleValue R X q b) n hn)
      have hv : cocycleValue R X (p+q) (c - (-1 : ℤ)^(p*q) • d') =
          cup R X p q (cocycleValue R X p a) (cocycleValue R X q b) -
            (-1 : ℤ)^(p*q) • castCochain R (Nat.add_comm q p)
              (cup R X q p (cocycleValue R X q b) (cocycleValue R X p a)) := by
        simp only [cocycleValue, map_sub, map_zsmul]
        change cocycleValue R X (p+q) c - (-1 : ℤ)^(p*q) • cocycleValue R X (p+q) d' = _
        rw [hc, hd']
        rfl
      rw [hv]
      have hcast : ∀ {i j : ℕ} (e : i=j) (x y : Cochain R X i) (s : ℤ),
          castCochain R e (x-s • y) = castCochain R e x - s • castCochain R e y := by
        intro i j e x y s
        subst j
        rfl
      rw [hcast]
      have hcastcast : ∀ {i j k : ℕ} (e : i=j) (f : j=k) (x : Cochain R X i),
          castCochain R f (castCochain R e x) = castCochain R (e.trans f) x := by
        intro i j k e f x
        subst k
        subst j
        rfl
      rw [hcastcast]
      exact cup_commutator_positive R hD (cocycleValue R X p a) (cocycleValue R X q b)
        (cocycleValue_delta R X p a) (cocycleValue_delta R X q b) n hn
  exact (congrArg (GradedMonoid.mk (A := H R X) (p+q)) heq).trans
    (gradedClass_smul_castOrdinaryCycle R (Nat.add_comm q p) d ((-1 : ℤ)^(p*q)))

@[simp] lemma cocycleValue_add (X : TopCat.{w}) (n : ℕ)
    (a b : (ordinaryCochains R R X).cycles (n : ℤ)) :
    cocycleValue R X n (a+b) = cocycleValue R X n a + cocycleValue R X n b :=
  (cocycleValueLinear R X n).map_add a b

@[simp] lemma cocycleValue_smul (X : TopCat.{w}) (n : ℕ) (r : R)
    (a : (ordinaryCochains R R X).cycles (n : ℤ)) :
    cocycleValue R X n (r • a) = r • cocycleValue R X n a :=
  (cocycleValueLinear R X n).map_smul r a

@[simp] lemma cocycleValue_zero (X : TopCat.{w}) (n : ℕ) :
    cocycleValue R X n 0 = 0 := (cocycleValueLinear R X n).map_zero

@[simp] lemma cocycleValue_sub (X : TopCat.{w}) (n : ℕ)
    (a b : (ordinaryCochains R R X).cycles (n : ℤ)) :
    cocycleValue R X n (a-b) = cocycleValue R X n a - cocycleValue R X n b :=
  (cocycleValueLinear R X n).map_sub a b

@[simp] lemma cocycleValue_zsmul (X : TopCat.{w}) (n : ℕ) (r : ℤ)
    (a : (ordinaryCochains R R X).cycles (n : ℤ)) :
    cocycleValue R X n (r • a) = r • cocycleValue R X n a :=
  map_zsmul (cocycleValueLinear R X n) r a

lemma homologyπ_eq_zero_iff_zero (X : TopCat.{w})
    (a : (ordinaryCochains R R X).cycles 0) :
    (ordinaryCochains R R X).homologyπ 0 a = 0 ↔ a = 0 := by
  change ((ordinaryCochains R R X).sc 0).homologyπ a = 0 ↔ _
  rw [shortComplex_homologyπ_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hp : ((ComplexShape.down ℤ).symm).prev 0 = -1 :=
      ((ComplexShape.down ℤ).symm).prev_eq' (by simp)
    have hz := (P202.CohomologyPairs.negative R R).1 X
      (((ComplexShape.down ℤ).symm).prev 0) (by rw [hp]; omega)
    have : Subsingleton (((ordinaryCochains R R X).sc 0).X₁) := by
      change Subsingleton ((ordinaryCochains R R X).X _)
      exact ModuleCat.subsingleton_of_isZero hz.1
    have hx0 : x=0 := Subsingleton.elim _ _
    rw [hx0, map_zero] at hx
    apply (ModuleCat.mono_iff_injective ((ordinaryCochains R R X).iCycles 0)).mp inferInstance
    exact hx.symm.trans (((ordinaryCochains R R X).iCycles 0).hom.map_zero).symm
  · intro ha
    subst a
    exact ⟨0, (((ordinaryCochains R R X).sc 0).f.hom.map_zero).trans
      (((ordinaryCochains R R X).sc 0).iCycles.hom.map_zero).symm⟩

lemma ordinary_chainMap_degree {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    (ordinaryNonnegativeIso R R X n).inv ≫ ((ordinaryFunctor R R).map f).f (n : ℤ) =
      (chainMap R R f).f n ≫ (ordinaryNonnegativeIso R R Y n).inv := by
  change (ordinaryNonnegativeIso R R X n).inv ≫
    (HomologicalComplex.extendMap (chainMap R R f) (degreeEmbedding 0)).f (n : ℤ) = _
  rw [HomologicalComplex.extendMap_f _ _ (show (degreeEmbedding 0).f n = (n : ℤ) by simp [degreeEmbedding])]
  simp [ordinaryNonnegativeIso]

lemma ordinaryCochainsEquiv_pullback {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (a : (ordinaryCochains R R Y).X (n : ℤ)) :
    ordinaryCochainsEquiv R R X n
      (((ordinaryCochainFunctor R R).map f.op).f (n : ℤ) a) =
        pullback R f n (ordinaryCochainsEquiv R R Y n a) := by
  apply LinearMap.ext
  intro c
  change (ordinaryComplex R R Y).X (n : ℤ) →ₗ[R] R at a
  change a (((ordinaryFunctor R R).map f).f (n : ℤ)
      ((ordinaryNonnegativeIso R R X n).inv c)) =
    a ((ordinaryNonnegativeIso R R Y n).inv (((chainMap R R f).f n) c))
  exact congrArg a (congrArg (fun ff => ff c) (ordinary_chainMap_degree R f n))

lemma cocycleValue_pullback {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (a : (ordinaryCochains R R Y).cycles (n : ℤ)) :
    cocycleValue R X n (HomologicalComplex.cyclesMap
      ((ordinaryCochainFunctor R R).map f.op) (n : ℤ) a) =
        pullback R f n (cocycleValue R Y n a) := by
  have h := congrArg (fun ff => ff a)
    (HomologicalComplex.cyclesMap_i ((ordinaryCochainFunctor R R).map f.op) (n : ℤ))
  change (ordinaryCochains R R X).iCycles (n : ℤ)
      (HomologicalComplex.cyclesMap ((ordinaryCochainFunctor R R).map f.op) (n : ℤ) a) =
    (((ordinaryCochainFunctor R R).map f.op).f (n : ℤ))
      ((ordinaryCochains R R Y).iCycles (n : ℤ) a) at h
  exact (congrArg (ordinaryCochainsEquiv R R X n) h).trans
    (ordinaryCochainsEquiv_pullback R f n _)

lemma hPullback_homologyπ {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (a : (ordinaryCochains R R Y).cycles (n : ℤ)) :
    hPullback R f n ((ordinaryCochains R R Y).homologyπ (n : ℤ) a) =
      (ordinaryCochains R R X).homologyπ (n : ℤ)
        (HomologicalComplex.cyclesMap ((ordinaryCochainFunctor R R).map f.op) (n : ℤ) a) := by
  exact congrArg (fun ff => ff a)
    (HomologicalComplex.homologyπ_naturality ((ordinaryCochainFunctor R R).map f.op) (n : ℤ))

lemma oneCochain_pullback {X Y : TopCat.{w}} (f : X ⟶ Y) :
    pullback R f 0 (oneCochain R Y) = oneCochain R X := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X 0)).ext
  intro s
  simp only [Finsupp.coe_basisSingleOne]
  change augmentationLinear R R Y (((chainMap R R f).f 0).hom (Finsupp.single s 1)) =
    augmentationLinear R R X (Finsupp.single s 1)
  rw [P202.SingularChains.chainMap_single, P202.SingularChains.augmentationLinear_single,
    P202.SingularChains.augmentationLinear_single]

lemma unitCycle_pullback {X Y : TopCat.{w}} (f : X ⟶ Y) :
    HomologicalComplex.cyclesMap ((ordinaryCochainFunctor R R).map f.op) 0 (unitCycle R Y) =
      unitCycle R X := by
  apply cocycleValue_injective R X 0
  exact (cocycleValue_pullback R f 0 (unitCycle R Y)).trans
    ((congrArg (pullback R f 0) (cocycleValue_unitCycle R Y)).trans
      ((oneCochain_pullback R f).trans (cocycleValue_unitCycle R X).symm))

lemma unitClass_pullback {X Y : TopCat.{w}} (f : X ⟶ Y) :
    hPullback R f 0 ((ordinaryCochains R R Y).homologyπ 0 (unitCycle R Y)) =
      (ordinaryCochains R R X).homologyπ 0 (unitCycle R X) := by
  exact (hPullback_homologyπ R f 0 (unitCycle R Y)).trans
    (congrArg ((ordinaryCochains R R X).homologyπ 0) (unitCycle_pullback R f))

/-- Multiplying a right coboundary by a left cocycle is a signed coboundary. -/
theorem cup_boundary_right (X : TopCat.{w}) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R X q) (ha : delta R X p a = 0) :
    castCochain R (by omega) (cup R X p (q+1) a (delta R X q b)) =
      (-1 : ℤ)^p • delta R X (p+q) (cup R X p q a b) := by
  have h := cup_leibniz R X p q a b
  rw [ha, map_zero, LinearMap.zero_apply] at h
  have hc : ∀ {m n : ℕ} (h : m=n), castCochain R h (0 : Cochain R X m) = 0 := by
    intro m n h; subst n; rfl
  rw [hc, zero_add] at h
  rw [h, smul_smul, ← mul_pow]
  norm_num
/- Descend a bilinear map along two surjective linear maps. -/
section Descent
variable {R}
variable {A B C D E : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
  [Module R A] [Module R B] [Module R C] [Module R D] [Module R E]

def descendBilinear (f : A →ₗ[R] B) (g : C →ₗ[R] D)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (b : A →ₗ[R] C →ₗ[R] E)
    (hleft : ∀ a, f a = 0 → b a = 0)
    (hright : ∀ a c, g c = 0 → b a c = 0) : B →ₗ[R] D →ₗ[R] E :=
  let t : A →ₗ[R] D →ₗ[R] E :=
    { toFun := fun a => g.liftOfSurjective hg ⟨b a, fun c hc => hright a c (show g c = 0 from hc)⟩
      map_add' := by
        intro a a'
        apply LinearMap.ext
        intro d
        obtain ⟨c, rfl⟩ := hg d
        simp only [LinearMap.equivOfSurjective_apply, map_add, LinearMap.add_apply]
      map_smul' := by
        intro r a
        apply LinearMap.ext
        intro d
        obtain ⟨c, rfl⟩ := hg d
        simp only [LinearMap.equivOfSurjective_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  f.liftOfSurjective hf ⟨t, fun a ha => by
    apply LinearMap.ext
    intro d
    obtain ⟨c, rfl⟩ := hg d
    change ((g.liftOfSurjective hg) ⟨b a, _⟩) (g c) = 0
    rw [LinearMap.equivOfSurjective_apply, hleft a (show f a = 0 from ha), LinearMap.zero_apply]⟩

@[simp] lemma descendBilinear_apply (f : A →ₗ[R] B) (g : C →ₗ[R] D)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (b : A →ₗ[R] C →ₗ[R] E)
    (hleft : ∀ a, f a = 0 → b a = 0)
    (hright : ∀ a c, g c = 0 → b a c = 0) (a : A) (c : C) :
    descendBilinear f g hf hg b hleft hright (f a) (g c) = b a c := by
  dsimp only [descendBilinear]
  rw [LinearMap.equivOfSurjective_apply]
  exact LinearMap.equivOfSurjective_apply hg _
end Descent

def cycleCup (X : TopCat.{w}) (p q : ℕ) :
    (ordinaryCochains R R X).cycles (p : ℤ) →ₗ[R]
      (ordinaryCochains R R X).cycles (q : ℤ) →ₗ[R]
        (ordinaryCochains R R X).cycles ((p+q : ℕ) : ℤ) where
  toFun a :=
    { toFun := fun b => cycleOfCochain R X (p+q)
        (cup R X p q (cocycleValue R X p a) (cocycleValue R X q b))
        (cup_cocycle R X p q _ _ (cocycleValue_delta R X p a) (cocycleValue_delta R X q b))
      map_add' := by
        intro b c
        apply cocycleValue_injective R X (p+q)
        simp only [cocycleValue_cycleOfCochain, cocycleValue_add, map_add]
      map_smul' := by
        intro r b
        apply cocycleValue_injective R X (p+q)
        simp only [cocycleValue_cycleOfCochain, cocycleValue_smul, map_smul, RingHom.id_apply] }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    apply cocycleValue_injective R X (p+q)
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, cocycleValue_cycleOfCochain, cocycleValue_add, map_add, LinearMap.add_apply]
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro b
    apply cocycleValue_injective R X (p+q)
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, cocycleValue_cycleOfCochain, cocycleValue_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] lemma cocycleValue_cycleCup (X : TopCat.{w}) (p q : ℕ)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R X).cycles (q : ℤ)) :
    cocycleValue R X (p+q) (cycleCup R X p q a b) =
      cup R X p q (cocycleValue R X p a) (cocycleValue R X q b) :=
  by
    simpa only [cycleCup, LinearMap.coe_mk, AddHom.coe_mk] using
      (cocycleValue_cycleOfCochain R X (p+q) _
        (cup_cocycle R X p q _ _ (cocycleValue_delta R X p a) (cocycleValue_delta R X q b)))

abbrev classMap (X : TopCat.{w}) (n : ℕ) :
    (ordinaryCochains R R X).cycles (n : ℤ) →ₗ[R] H R X n :=
  ((ordinaryCochains R R X).homologyπ (n : ℤ)).hom

lemma classMap_surjective (X : TopCat.{w}) (n : ℕ) :
    Function.Surjective (classMap R X n) :=
  (ModuleCat.epi_iff_surjective ((ordinaryCochains R R X).homologyπ (n : ℤ))).mp inferInstance

def cycleCupClass (X : TopCat.{w}) (p q : ℕ) :
    (ordinaryCochains R R X).cycles (p : ℤ) →ₗ[R]
      (ordinaryCochains R R X).cycles (q : ℤ) →ₗ[R] H R X (p+q) :=
  (LinearMap.llcomp R _ _ _ (classMap R X (p+q))).comp (cycleCup R X p q)

@[simp] lemma cycleCupClass_apply (X : TopCat.{w}) (p q : ℕ)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R X).cycles (q : ℤ)) :
    cycleCupClass R X p q a b = classMap R X (p+q) (cycleCup R X p q a b) := rfl

lemma cycleCupClass_left_zero_positive (X : TopCat.{w}) (p q : ℕ)
    (a : (ordinaryCochains R R X).cycles ((p+1 : ℕ) : ℤ))
    (b : (ordinaryCochains R R X).cycles (q : ℤ))
    (ha : classMap R X (p+1) a = 0) : cycleCupClass R X (p+1) q a b = 0 := by
  obtain ⟨c, hc⟩ := (homologyπ_eq_zero_iff_positive R X p a).mp ha
  apply homologyπ_eq_zero_of_delta R X (p+1+q) (p+q) (cycleCup R X (p+1) q a b) (by omega)
    (cup R X p q c (cocycleValue R X q b))
  rw [cocycleValue_cycleCup, ← hc]
  exact cup_boundary_left R X p q c _ (cocycleValue_delta R X q b)

lemma cycleCupClass_right_zero_positive (X : TopCat.{w}) (p q : ℕ)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R X).cycles ((q+1 : ℕ) : ℤ))
    (hb : classMap R X (q+1) b = 0) : cycleCupClass R X p (q+1) a b = 0 := by
  obtain ⟨c, hc⟩ := (homologyπ_eq_zero_iff_positive R X q b).mp hb
  apply homologyπ_eq_zero_of_delta R X (p+(q+1)) (p+q) (cycleCup R X p (q+1) a b) (by omega)
    ((-1 : ℤ)^p • cup R X p q (cocycleValue R X p a) c)
  rw [cocycleValue_cycleCup, ← hc, map_zsmul]
  exact cup_boundary_right R X p q _ c (cocycleValue_delta R X p a)

lemma cycleCupClass_left_zero (X : TopCat.{w}) (p q : ℕ)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (ha : classMap R X p a = 0) : cycleCupClass R X p q a = 0 := by
  apply LinearMap.ext
  intro b
  cases p with
  | zero =>
    have ha0 : a = 0 := (homologyπ_eq_zero_iff_zero R X a).mp ha
    rw [ha0, map_zero, LinearMap.zero_apply]
  | succ p => exact cycleCupClass_left_zero_positive R X p q a b ha

lemma cycleCupClass_right_zero (X : TopCat.{w}) (p q : ℕ)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R X).cycles (q : ℤ))
    (hb : classMap R X q b = 0) : cycleCupClass R X p q a b = 0 := by
  cases q with
  | zero =>
    have hb0 : b = 0 := (homologyπ_eq_zero_iff_zero R X b).mp hb
    rw [hb0, map_zero]
  | succ q => exact cycleCupClass_right_zero_positive R X p q a b hb

/-- The cup product on the actual ordinary cohomology modules. -/
def hCup (X : TopCat.{w}) (p q : ℕ) : H R X p →ₗ[R] H R X q →ₗ[R] H R X (p+q) :=
  descendBilinear (classMap R X p) (classMap R X q)
    (classMap_surjective R X p) (classMap_surjective R X q)
    (cycleCupClass R X p q) (cycleCupClass_left_zero R X p q) (cycleCupClass_right_zero R X p q)

@[simp] theorem hCup_rep (X : TopCat.{w}) (p q : ℕ)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R X).cycles (q : ℤ)) :
    hCup R X p q (classMap R X p a) (classMap R X q b) =
      classMap R X (p+q) (cycleCup R X p q a b) :=
  descendBilinear_apply _ _ _ _ _ _ _ a b

lemma hCup_represents (X : TopCat.{w}) (p q : ℕ)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R X).cycles (q : ℤ)) :
    ∃ c : (ordinaryCochains R R X).cycles ((p+q : ℕ) : ℤ),
      cocycleValue R X (p+q) c = cup R X p q (cocycleValue R X p a) (cocycleValue R X q b) ∧
      hCup R X p q ((ordinaryCochains R R X).homologyπ (p : ℤ) a)
        ((ordinaryCochains R R X).homologyπ (q : ℤ) b) =
          (ordinaryCochains R R X).homologyπ ((p+q : ℕ) : ℤ) c :=
  ⟨cycleCup R X p q a b, cocycleValue_cycleCup R X p q a b, hCup_rep R X p q a b⟩

def hOne (X : TopCat.{w}) : H R X 0 := classMap R X 0 (unitCycle R X)

lemma represented_product_natural
    (μ : ∀ X : TopCat.{w}, ∀ p q, H R X p →ₗ[R] H R X q →ₗ[R] H R X (p+q))
    (hrep : ∀ (X : TopCat.{w}) (p q : ℕ) (a : (ordinaryCochains R R X).cycles (p : ℤ))
        (b : (ordinaryCochains R R X).cycles (q : ℤ)),
      ∃ c : (ordinaryCochains R R X).cycles ((p+q : ℕ) : ℤ),
        cocycleValue R X (p+q) c = cup R X p q (cocycleValue R X p a) (cocycleValue R X q b) ∧
        μ X p q ((ordinaryCochains R R X).homologyπ (p : ℤ) a)
          ((ordinaryCochains R R X).homologyπ (q : ℤ) b) =
            (ordinaryCochains R R X).homologyπ ((p+q : ℕ) : ℤ) c)
    {X Y : TopCat.{w}} (f : X ⟶ Y) (p q : ℕ) (a : H R Y p) (b : H R Y q) :
    hPullback R f (p+q) (μ Y p q a b) =
      μ X p q (hPullback R f p a) (hPullback R f q b) := by
  have hs (n : ℕ) : Function.Surjective ((ordinaryCochains R R Y).homologyπ (n : ℤ)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨a,rfl⟩ := hs p a
  obtain ⟨b,rfl⟩ := hs q b
  obtain ⟨c,hc,hpc⟩ := hrep Y p q a b
  let a' := HomologicalComplex.cyclesMap ((ordinaryCochainFunctor R R).map f.op) (p : ℤ) a
  let b' := HomologicalComplex.cyclesMap ((ordinaryCochainFunctor R R).map f.op) (q : ℤ) b
  obtain ⟨d,hd,hpd⟩ := hrep X p q a' b'
  rw [hpc]
  simp only [hPullback_homologyπ]
  change (ordinaryCochains R R X).homologyπ ((p+q : ℕ) : ℤ)
    (HomologicalComplex.cyclesMap ((ordinaryCochainFunctor R R).map f.op) ((p+q : ℕ) : ℤ) c) =
      μ X p q ((ordinaryCochains R R X).homologyπ (p : ℤ) a')
        ((ordinaryCochains R R X).homologyπ (q : ℤ) b')
  rw [hpd]
  congr 1
  apply cocycleValue_injective R X (p+q)
  rw [cocycleValue_pullback, hc, cup_natural, hd]
  dsimp only [a',b']
  rw [cocycleValue_pullback,cocycleValue_pullback]

lemma represented_unit_natural
    (e : ∀ X : TopCat.{w}, H R X 0)
    (he : ∀ X : TopCat.{w}, ∃ a : (ordinaryCochains R R X).cycles 0,
      cocycleValue R X 0 a = oneCochain R X ∧
        e X = (ordinaryCochains R R X).homologyπ 0 a)
    {X Y : TopCat.{w}} (f : X ⟶ Y) :
    hPullback R f 0 (e Y) = e X := by
  obtain ⟨a,ha,hea⟩ := he Y
  obtain ⟨b,hb,heb⟩ := he X
  rw [hea,heb]
  have hab : HomologicalComplex.cyclesMap ((ordinaryCochainFunctor R R).map f.op) 0 a = b := by
    apply cocycleValue_injective R X 0
    exact (cocycleValue_pullback R f 0 a).trans
      ((congrArg (pullback R f 0) ha).trans ((oneCochain_pullback R f).trans hb.symm))
  exact (hPullback_homologyπ R f 0 a).trans
    (congrArg ((ordinaryCochains R R X).homologyπ 0) hab)

/-- Bilinear operations descended to the given ordinary cohomology modules,
with the exact cochain representatives, prior to packaging their ring laws. -/
structure RepresentedProduct (X : TopCat.{w}) where
  product : ∀ p q, H R X p →ₗ[R] H R X q →ₗ[R] H R X (p+q)
  unit : H R X 0
  represents : ∀ (p q : ℕ) (a : (ordinaryCochains R R X).cycles (p : ℤ))
      (b : (ordinaryCochains R R X).cycles (q : ℤ)),
    ∃ c : (ordinaryCochains R R X).cycles ((p+q : ℕ) : ℤ),
      cocycleValue R X (p+q) c = cup R X p q (cocycleValue R X p a) (cocycleValue R X q b) ∧
      product p q ((ordinaryCochains R R X).homologyπ (p : ℤ) a)
        ((ordinaryCochains R R X).homologyπ (q : ℤ) b) =
          (ordinaryCochains R R X).homologyπ ((p+q : ℕ) : ℤ) c
  unit_represents : ∃ a : (ordinaryCochains R R X).cycles 0,
    cocycleValue R X 0 a = oneCochain R X ∧
      unit = (ordinaryCochains R R X).homologyπ 0 a

def cohomologyRingOfRepresented (hD : DiagonalHomotopy.{u,w} R)
    (X : TopCat.{w}) (d : RepresentedProduct R X) : CohomologyRing R X := by
  let laws := represented_product_laws R X d.product d.unit d.represents d.unit_represents
  refine {
    gradedRing := gradedRingOfBilinear R (H R X) d.product d.unit laws.1 laws.2.1 laws.2.2
    algebra := gradedAlgebraOfBilinear R (H R X) d.product d.unit laws.1 laws.2.1 laws.2.2
    product := d.product
    product_eq := by intros; rfl
    represents := d.represents
    unit_represents := d.unit_represents
    graded_commutative := ?_ }
  intro p q a b
  have hs (n : ℕ) : Function.Surjective ((ordinaryCochains R R X).homologyπ (n : ℤ)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨a,rfl⟩ := hs p a
  obtain ⟨b,rfl⟩ := hs q b
  obtain ⟨c,hc,hpc⟩ := d.represents p q a b
  obtain ⟨d',hd,hpd⟩ := d.represents q p b a
  rw [hpc,hpd]
  exact cup_homology_commute_of_representatives R hD X p q a b c d' hc hd

def naturalCohomologyRingOfRepresented (hD : DiagonalHomotopy.{u,w} R)
    (d : ∀ X : TopCat.{w}, RepresentedProduct R X)
    (hunit : ∀ {X Y : TopCat.{w}} (f : X ⟶ Y), hPullback R f 0 (d Y).unit = (d X).unit)
    (hproduct : ∀ {X Y : TopCat.{w}} (f : X ⟶ Y) (p q : ℕ) (a : H R Y p) (b : H R Y q),
      hPullback R f (p+q) ((d Y).product p q a b) =
        (d X).product p q (hPullback R f p a) (hPullback R f q b)) :
    NaturalCohomologyRing.{u,w} R where
  ring X := cohomologyRingOfRepresented R hD X (d X)
  pullback {X Y} f := by
    letI := (cohomologyRingOfRepresented R hD X (d X)).gradedRing
    letI := (cohomologyRingOfRepresented R hD X (d X)).algebra
    letI := (cohomologyRingOfRepresented R hD Y (d Y)).gradedRing
    letI := (cohomologyRingOfRepresented R hD Y (d Y)).algebra
    exact gradedAlgebraMap R (H R Y) (H R X) (fun n => hPullback R f n)
      (hunit f) (hproduct f)
  pullback_homogeneous {X Y} f n a := by
    let := (cohomologyRingOfRepresented R hD X (d X)).gradedRing
    let := (cohomologyRingOfRepresented R hD X (d X)).algebra
    let := (cohomologyRingOfRepresented R hD Y (d Y)).gradedRing
    let := (cohomologyRingOfRepresented R hD Y (d Y)).algebra
    exact gradedAlgebraMap_of R _ _ _ _ _ n a

/-- The descended front/back product and its constant unit. -/
def representedCup (X : TopCat.{w}) : RepresentedProduct R X where
  product := hCup R X
  unit := hOne R X
  represents := hCup_represents R X
  unit_represents := ⟨unitCycle R X, cocycleValue_unitCycle R X, rfl⟩

/-- The natural graded algebra on the existing ordinary cohomology modules. -/
def naturalCupRing (he : P202Specs.EilenbergZilber.equivalence_type.{u,w}) :
    NaturalCohomologyRing.{u,w} R :=
  naturalCohomologyRingOfRepresented R (DiagonalModels.diagonalHomotopy R he)
    (representedCup R)
    (fun f => unitClass_pullback R f)
    (represented_product_natural R (hCup R) (hCup_represents R))

/-- Ordinary singular cohomology is a natural unital associative graded
R-algebra, with the stated cup representatives and homogeneous graded sign. -/
theorem cohomologyRing : cohomologyRing_type.{u,w} := by
  intro R _
  exact ⟨naturalCupRing R P202.EilenbergZilber.equivalence⟩

end P202.CupProduct
