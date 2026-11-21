import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
import Mathlib.Algebra.Homology.ConcreteCategory

/-! The actual homogeneous cochains on the original coefficient carrier. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large
open scoped MonoidAlgebra

namespace Specs.AdvancedHomologicalAlgebra.GroupExtensionOriginalCoefficients

universe u v w s x y z
variable {k : Type u} [CommRing k] {G : Type v} [Group G]

/-- Equivariant functions on the original homogeneous tuples. -/
def cochains (M : Rep.{w} k G) (n : ℕ) : Submodule k ((Fin (n + 1) → G) → M) where
  carrier := { f | ∀ g c, f (fun i => g * c i) = M.ρ g (f c) }
  zero_mem' g c := (map_zero (M.ρ g)).symm
  add_mem' hf hg g c := by
    rw [Pi.add_apply, Pi.add_apply, hf g c, hg g c, map_add]
  smul_mem' a f hf g c := by
    rw [Pi.smul_apply, Pi.smul_apply, hf g c, map_smul]

lemma equivariant {M : Rep.{w} k G} {n : ℕ} (f : cochains M n) (g : G)
    (c : Fin (n + 1) → G) :
    f.val (fun i => g * c i) = M.ρ g (f.val c) :=
  f.property g c

/-- Alternating deletion of vertices. -/
def differential (M : Rep.{w} k G) (n : ℕ) :
    cochains M n →ₗ[k] cochains M (n+1) where
  toFun f :=
    ⟨fun c => ∑ i : Fin (n+2), (-1 : k) ^ i.val • f.val (c ∘ i.succAbove),
      fun g c => by simp only [map_sum, map_smul, ← equivariant]; rfl⟩
  map_add' f g := by
    apply Subtype.ext
    funext c
    change (∑ i : Fin (n+2), (-1 : k) ^ i.val • (f.val (c ∘ i.succAbove) + g.val (c ∘ i.succAbove))) =
      (∑ i : Fin (n+2), (-1 : k) ^ i.val • f.val (c ∘ i.succAbove)) +
        (∑ i : Fin (n+2), (-1 : k) ^ i.val • g.val (c ∘ i.succAbove))
    simp only [smul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    apply Subtype.ext
    funext c
    change (∑ i : Fin (n+2), (-1 : k) ^ i.val • (a • f.val (c ∘ i.succAbove))) =
      a • (∑ i : Fin (n+2), (-1 : k) ^ i.val • f.val (c ∘ i.succAbove))
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => smul_comm ((-1 : k) ^ i.val) a _)

lemma differential_apply (M : Rep.{w} k G) (n : ℕ) (f : cochains M n)
    (c : Fin (n+2) → G) :
    (differential M n f).val c =
      ∑ i : Fin (n+2), (-1 : k) ^ i.val • f.val (c ∘ i.succAbove) := rfl

def SquareZero (k : Type u) (G : Type v) [CommRing k] [Group G] : Prop :=
  ∀ (M : Rep.{w} k G) (n : ℕ), (differential M (n+1)).comp (differential M n) = 0

def complex (h : SquareZero.{u,v,w} k G) (M : Rep.{w} k G) :
    CochainComplex (ModuleCat.{max v w} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (cochains M n))
    (fun n => ModuleCat.ofHom (differential M n)) (fun n => ModuleCat.hom_ext (h M n))

variable {H : Type x} [Group H]

/-- A linear coefficient map equivariant along a group homomorphism defines
pullback of homogeneous cochains. -/
def pullbackDegree {M : Rep.{w} k G} {L : Rep k H} (t : H →* G) (b : M →ₗ[k] L)
    (hb : ∀ g m, b (M.ρ (t g) m) = L.ρ g (b m)) (n : ℕ) :
    cochains M n →ₗ[k] cochains L n where
  toFun f := ⟨fun c => b (f.val (t ∘ c)), fun g c => by
    have he : t ∘ (fun i => g * c i) = fun i => t g * (t ∘ c) i := by
      funext i
      exact map_mul t _ _
    change b (f.val (t ∘ (fun i => g * c i))) = L.ρ g (b (f.val (t ∘ c)))
    rw [he, equivariant, hb]⟩
  map_add' f g := by
    apply Subtype.ext
    funext c
    exact map_add b _ _
  map_smul' a f := by
    apply Subtype.ext
    funext c
    exact map_smul b _ _

/-- Pullback when the index and coefficient universes allow the two complexes
to be regarded as objects of the same module category. -/
def cochainPullback {H : Type v} [Group H]
    {hG : SquareZero.{u,v,w} k G} {hH : SquareZero.{u,v,w} k H}
    {M : Rep.{w} k G} {L : Rep.{w} k H} (t : H →* G) (b : M →ₗ[k] L)
    (hb : ∀ g m, b (M.ρ (t g) m) = L.ρ g (b m)) :
    complex hG M ⟶ complex hH L where
  f n := ModuleCat.ofHom (pullbackDegree t b hb n)
  comm' i j hij := by
    have hji : j = i + 1 := hij.symm
    subst j
    simp only [complex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    ext f c
    change (∑ l : Fin (i+2), (-1 : k) ^ l.val • b (f.val ((t ∘ c) ∘ l.succAbove))) =
      b (∑ l : Fin (i+2), (-1 : k) ^ l.val • f.val ((t ∘ c) ∘ l.succAbove))
    simp only [map_sum, map_smul]

def homogeneousFunctor (h : SquareZero.{u,v,w} k G) :
    Rep.{w} k G ⥤ CochainComplex (ModuleCat.{max v w} k) ℕ where
  obj := complex h
  map b := cochainPullback (MonoidHom.id G) b.hom.toLinearMap
    (fun g m => Rep.hom_comm_apply b g m)
  map_id _ := by ext n f; rfl
  map_comp _ _ := by ext n f; rfl

abbrev cohomology (h : SquareZero.{u,v,w} k G) (n : ℕ) :=
  homogeneousFunctor h ⋙ HomologicalComplex.homologyFunctor _ (.up ℕ) n

/-- Exact carrier lift for the scalar complexes, with room for a second coefficient. -/
abbrev scalarLift (k : Type u) [CommRing k] :=
  ModuleCat.uliftFunctor.{max u s,max v w} k

abbrev liftedFunctor (h : SquareZero.{u,v,w} k G) :=
  homogeneousFunctor h ⋙ (scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)

/-- Exact lift of the representation through modules over the same group algebra. -/
abbrev coefficientLift (k : Type u) (G : Type v) [CommRing k] [Group G] :
    Rep.{w} k G ⥤ Rep.{max u v w s} k G :=
  Rep.toModuleMonoidAlgebra ⋙ ModuleCat.uliftFunctor.{max u v s,w} k[G] ⋙ Rep.ofModuleMonoidAlgebra

/-- The pointwise equivalence from the original coefficient to its carrier lift. -/
def liftCoeffEquiv (M : Rep.{w} k G) :
    M ≃ₗ[k] (coefficientLift.{u,v,w,s} k G).obj M where
  toFun m := ULift.up (M.ρ.asModuleEquiv.symm m)
  invFun m := M.ρ.asModuleEquiv m.down
  left_inv := M.ρ.asModuleEquiv.apply_symm_apply
  right_inv m := ULift.ext (M.ρ.asModuleEquiv.symm_apply_apply m.down)
  map_add' m n := ULift.ext (_root_.map_add M.ρ.asModuleEquiv.symm m n)
  map_smul' r m := ULift.ext (Representation.asModuleEquiv_symm_map_smul M.ρ r m)

lemma liftCoeffEquiv_action (M : Rep.{w} k G) (g : G) (m : M) :
    liftCoeffEquiv.{u,v,w,s} M (M.ρ g m) = ((coefficientLift.{u,v,w,s} k G).obj M).ρ g (liftCoeffEquiv.{u,v,w,s} M m) := by
  apply ULift.ext
  exact Representation.asModuleEquiv_symm_map_rho M.ρ g m

instance homogeneousFunctor_preservesZero (h : SquareZero.{u,v,w} k G) :
    (homogeneousFunctor h).PreservesZeroMorphisms where
  map_zero X Y := by
    ext n f
    apply Subtype.ext
    funext c
    rfl

instance coefficientLift_additive (k : Type u) (G : Type v) [CommRing k] [Group G] :
    (coefficientLift.{u,v,w,s} k G).Additive where
  map_add := by
    intros
    ext x
    rfl

/-- The carrier change is exact on the original coefficient category. -/
theorem liftShortExact {S : ShortComplex (Rep.{w} k G)} (hS : S.ShortExact) :
    (S.map (coefficientLift.{u,v,w,s} k G)).ShortExact := by
  let _ := hS.mono_f
  let _ := hS.epi_g
  exact hS.map (coefficientLift.{u,v,w,s} k G)

/-- Pointwise transport to the ambient Hom from the actual bar resolution. -/
def PointwiseComparison (k : Type u) (G : Type v) [CommRing k] [Group G]
    (h : SquareZero.{u,v,w} k G) : Prop :=
  ∃ e : liftedFunctor.{u,v,w,0} h ≅ coefficientLift.{u,v,w,0} k G ⋙ repHomogeneousFunctor.{u,v,w} k G,
    ∀ (M : Rep.{w} k G) (n : ℕ) (f : cochains M n) (c : Fin (n+1) → G),
      ((((e.hom.app M).f n).hom (ULift.up f)).hom
        (GroupBar.Large.single k G c 1)).down = M.ρ.asModuleEquiv.symm (f.val c)

/-- Degree zero is the actual fixed submodule, with a fixed element
represented by the constant homogeneous cochain. -/
def DegreeZero (h : SquareZero.{u,v,w} k G) : Prop :=
  ∃ z : Rep.invariantsFunctor k G ⋙ ModuleCat.uliftFunctor.{v,w} k ≅ cohomology h 0,
    ∀ (M : Rep.{w} k G) (m : M.ρ.invariants),
      ∃ f : (complex h M).cycles 0,
        (∀ c : Fin 1 → G, (((complex h M).iCycles 0).hom f).val c = m.val) ∧
        ((z.hom.app M).hom (ULift.up m)) = ((complex h M).homologyπ 0).hom f

def degreeZeroExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (h : SquareZero.{u,v,w} k G),
    DegreeZero h

/-- The representation lift agrees with the original module lift used by HA-A01. -/
def ModuleLiftComparison (k : Type u) (G : Type v) [CommRing k] [Group G] : Prop :=
  Nonempty ((Rep.ofModuleMonoidAlgebra : ModuleCat.{w} k[G] ⥤ Rep.{w} k G) ⋙
    coefficientLift.{u,v,w,0} k G ≅
    GroupCohomologyOriginalCoefficients.lift.{u,v,w} k G ⋙ Rep.ofModuleMonoidAlgebra)

def moduleLiftComparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], ModuleLiftComparison.{u,v,w} k G

open GroupCohomologyOriginalCoefficients in
/-- Evaluating at the normalized vertices gives the original HA-A01-Carrier
coordinates. Both complexes use the unlifted coefficient carrier. -/
def InhomogeneousComparison (k : Type u) (G : Type v) [CommRing k] [Group G]
    (h : SquareZero.{u,v,w} k G) (h' : GroupCohomologyOriginalCoefficients.SquareZero.{u,v,w} k G) : Prop :=
  ∃ e : Rep.ofModuleMonoidAlgebra ⋙ homogeneousFunctor h ≅ rawFunctor k G h',
    ∀ (M : GroupCohomologyOriginalCoefficients.Coeff.{u,v,w} k G) (n : ℕ) (φ : cochains (Rep.ofModuleMonoidAlgebra.obj M) n)
      (g : Fin n → G), ((e.hom.app M).f n).hom φ g = φ.val (Fin.partialProd g)

def inhomogeneousComparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (h : SquareZero.{u,v,w} k G)
    (h' : GroupCohomologyOriginalCoefficients.SquareZero.{u,v,w} k G),
      InhomogeneousComparison k G h h'

section Extension
variable (N : Subgroup G) [N.Normal]

/-- The conjugation action on homogeneous functions on the subgroup. -/
def conjugation (h : SquareZero.{u,v,w} k N) (M : Rep.{w} k G) (g : G) :
    complex h (Rep.res N.subtype M) ⟶ complex h (Rep.res N.subtype M) :=
  cochainPullback (MulAut.conjNormal g⁻¹).toMonoidHom (M.ρ g) (fun a m => by
    change M.ρ g (M.ρ ((MulAut.conjNormal g⁻¹ a : N) : G) m) =
      M.ρ (a : G) (M.ρ g m)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    rw [MulAut.conjNormal_apply]
    simp [mul_assoc])

lemma conjugation_apply (h : SquareZero.{u,v,w} k N) (M : Rep.{w} k G) (g : G)
    (n : ℕ) (φ : cochains (Rep.res N.subtype M) n) (c : Fin (n+1) → N) :
    (((conjugation N h M g).f n).hom φ).val c =
      M.ρ g (φ.val (fun i => MulAut.conjNormal g⁻¹ (c i))) :=
  rfl

/-- Restriction to the original subgroup tuples. -/
def restriction (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (M : Rep.{w} k G) : complex hG M ⟶ complex hN (Rep.res N.subtype M) :=
  cochainPullback N.subtype LinearMap.id (fun _ _ => rfl)

abbrev fixed (M : Rep.{w} k G) : Rep.{w} k (G ⧸ N) := M.quotientToInvariants N

/-- Inflation pulls back the quotient tuples and includes the fixed coefficients. -/
def inflation (hG : SquareZero.{u,v,w} k G) (hQ : SquareZero.{u,v,w} k (G ⧸ N))
    (M : Rep.{w} k G) : complex hQ (fixed N M) ⟶ complex hG M :=
  cochainPullback (QuotientGroup.mk' N) (Representation.invariants (M.ρ.comp N.subtype)).subtype
    (fun _ _ => rfl)

/-- For a coefficient comparison, its homogeneous-coordinate description
also fixes the comparison on cohomology. -/
structure BarComparison (h : SquareZero.{u,v,w} k G) (M : Rep.{w} k G)
    (L : Rep.{max u v w s} k G) (e : M ≃ₗ[k] L) where
  cochain : ((scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)).obj (complex h M) ≅
      (repHomogeneousFunctor.{u,v,max w s} k G).obj L
  formula : ∀ n (f : cochains M n) (c : Fin (n+1) → G),
    ((cochain.hom.f n).hom (ULift.up f)).hom (GroupBar.Large.single.{u,v,max w s} k G c 1) =
      e (f.val c)

def BarComparison.onHomology {h : SquareZero.{u,v,w} k G} {M : Rep.{w} k G}
    {L : Rep.{max u v w s} k G} {e : M ≃ₗ[k] L}
    (c : BarComparison.{u,v,w,s} h M L e) (n : ℕ) :
    (scalarLift.{u,v,w,s} k).obj ((complex h M).homology n) ≅
      (repHomogeneousCohomology.{u,v,max w s} k G n).obj L :=
  (((complex h M).sc n).mapHomologyIso (scalarLift.{u,v,w,s} k)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℕ) n).mapIso c.cochain

/-- Remove the scalar lift from the original homology carrier. -/
def BarComparison.linearEquiv {h : SquareZero.{u,v,w} k G} {M : Rep.{w} k G}
    {L : Rep.{max u v w s} k G} {e : M ≃ₗ[k] L}
    (c : BarComparison.{u,v,w,s} h M L e) (n : ℕ) :
    (complex h M).homology n ≃ₗ[k] (repHomogeneousCohomology.{u,v,max w s} k G n).obj L :=
  ULift.moduleEquiv.symm.trans (c.onHomology n).toLinearEquiv

/-- The conjugation comparison uses the original coefficient action on
the raw functions and the ambient action on the homogeneous bar Hom. -/
def ActionComparison (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G)
    [N.Normal] (h : SquareZero.{u,v,w} k N) : Prop :=
  ∀ (M : Rep.{w} k G) (L : Rep.{max u v w s} k G) (e : M ≃ₗ[k] L)
    (_ : ∀ g m, e (M.ρ g m) = L.ρ g (e m)),
    ∀ a : G →* End ((repHomogeneousFunctor.{u,v,max w s} k N).obj (Rep.res N.subtype L)),
      Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.ActionFormula.{u,v,max w s} k G N L a →
      ∃ c : BarComparison.{u,v,w,s} h (Rep.res N.subtype M) (Rep.res N.subtype L) e,
        ∀ g, ((scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)).map (conjugation N h M g) ≫
          c.cochain.hom = c.cochain.hom ≫ (a g).asHom

def actionComparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]
    (h : SquareZero.{u,v,w} k N), ActionComparison.{u,v,w,s} k G N h

open Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction in
/-- Agreement with the fixed subcomplex of every ambient injective resolution. -/
def InjectiveActionComparison (k : Type u) (G : Type v) [CommRing k] [Group G]
    (N : Subgroup G) [N.Normal] (h : SquareZero.{u,v,w} k N) : Prop :=
  ∃ (ρ : ∀ (M : Rep.{w} k G) (j : ℕ),
      Representation k (G ⧸ N) ((complex h (Rep.res N.subtype M)).homology j))
    (e : ∀ (M : Rep.{w} k G) (j : ℕ) (I : InjectiveResolution ((coefficientLift.{u,v,w,s} k G).obj M)),
      (complex h (Rep.res N.subtype M)).homology j ≃ₗ[k]
        (invariantResolutionComplex.{u,v,max w s} k G N ((coefficientLift.{u,v,w,s} k G).obj M) I).homology j),
    (∀ M j g, ρ M j (QuotientGroup.mk' N g) =
      (HomologicalComplex.homologyMap (conjugation N h M g) j).hom) ∧
    (∀ M j I q x, e M j I (ρ M j q x) =
      ((invariantResolutionComplex.{u,v,max w s} k G N ((coefficientLift.{u,v,w,s} k G).obj M) I).homology j).ρ q (e M j I x)) ∧
    ∀ (M L : Rep.{w} k G) (f : M ⟶ L) (j : ℕ)
      (I : InjectiveResolution ((coefficientLift.{u,v,w,s} k G).obj M))
      (J : InjectiveResolution ((coefficientLift.{u,v,w,s} k G).obj L))
      (φ : InjectiveResolution.Hom I J ((coefficientLift.{u,v,w,s} k G).map f))
      (x : (complex h (Rep.res N.subtype M)).homology j),
      e L j J ((HomologicalComplex.homologyMap
        ((homogeneousFunctor h).map (Rep.resMap N.subtype f)) j).hom x) =
      (HomologicalComplex.homologyMap
        (((normalInvariants.{u,v,max w s} k G N).mapHomologicalComplex (.up ℕ)).map φ.hom) j).hom
        (e M j I x)

def injectiveActionComparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]
    (h : SquareZero.{u,v,w} k N), InjectiveActionComparison.{u,v,w,s} k G N h

/-- The two ordinary cochain pullbacks commute with the pointwise bar
comparisons, including the comparison of normal-subgroup fixed coefficients. -/
def EdgeCochainComparison (k : Type u) (G : Type v) [CommRing k] [Group G]
    (N : Subgroup G) [N.Normal]
    (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (hQ : SquareZero.{u,v,w} k (G ⧸ N)) : Prop :=
  ∀ (M : Rep.{w} k G) (L : Rep.{max u v w} k G) (e : M ≃ₗ[k] L)
    (_ : ∀ g m, e (M.ρ g m) = L.ρ g (e m))
    (i : (repHomogeneousFunctor.{u,v,w} k (G ⧸ N)).obj (fixed N L) ⟶
      (repHomogeneousFunctor.{u,v,w} k G).obj L)
    (r : (repHomogeneousFunctor.{u,v,w} k G).obj L ⟶
      (repHomogeneousFunctor.{u,v,w} k N).obj (Rep.res N.subtype L)),
    (∀ (n : ℕ) (φ : ((repHomogeneousFunctor.{u,v,w} k (G ⧸ N)).obj (fixed N L)).X n)
      (c : Fin (n+1) → G), (((i.f n).hom φ).hom (GroupBar.Large.single k G c 1)) =
      (φ.hom (GroupBar.Large.single k (G ⧸ N) (QuotientGroup.mk' N ∘ c) 1)).val) →
    (∀ (n : ℕ) (φ : ((repHomogeneousFunctor.{u,v,w} k G).obj L).X n)
      (c : Fin (n+1) → N), (((r.f n).hom φ).hom (GroupBar.Large.single k N c 1)) =
      φ.hom (GroupBar.Large.single k G (N.subtype ∘ c) 1)) →
    ∃ (e₀ : fixed N M ≃ₗ[k] fixed N L)
      (cG : BarComparison.{u,v,w,0} hG M L e)
      (cN : BarComparison.{u,v,w,0} hN (Rep.res N.subtype M) (Rep.res N.subtype L) e)
      (cQ : BarComparison.{u,v,w,0} hQ (fixed N M) (fixed N L) e₀),
    (∀ m, (e₀ m).val = e m.val) ∧
    ((scalarLift.{u,v,w,0} k).mapHomologicalComplex (.up ℕ)).map (inflation N hG hQ M) ≫
      cG.cochain.hom = cQ.cochain.hom ≫ i ∧
    ((scalarLift.{u,v,w,0} k).mapHomologicalComplex (.up ℕ)).map (restriction N hG hN M) ≫
      cN.cochain.hom = cG.cochain.hom ≫ r

def edgeCochainComparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]
    (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (hQ : SquareZero.{u,v,w} k (G ⧸ N)), EdgeCochainComparison k G N hG hN hQ

end Extension

/-- Exact scalar carrier lift respects the boundaries of short exact
sequences of the cochain complexes on the original carriers. -/
def scalarConnectorsExpected : Prop :=
  ∀ (k : Type u) [CommRing k]
    (S : ShortComplex (CochainComplex (ModuleCat.{w} k) ℕ)) (hS : S.ShortExact) (n : ℕ),
    let U := ModuleCat.uliftFunctor.{v,w} k
    ∀ hT : (S.map (U.mapHomologicalComplex (.up ℕ))).ShortExact,
      hT.δ n (n+1) rfl ≫ ((S.X₁.sc (n+1)).mapHomologyIso U).hom =
        ((S.X₃.sc n).mapHomologyIso U).hom ≫ U.map (hS.δ n (n+1) rfl)

/-- The normalized comparison to the original homology is the ambient
normalized comparison followed by the inverse of the pointwise cochain
comparison and the exact scalar-lift comparison. -/
def OriginalConnectors (k : Type u) [CommRing k] {A : Type y} [Category.{z} A] [Abelian A]
    (K : A ⥤ CochainComplex (ModuleCat.{w} k) ℕ) [K.PreservesZeroMorphisms]
    (L : A ⥤ CochainComplex (ModuleCat.{max u w s} k) ℕ) [L.PreservesZeroMorphisms]
    (b : K ⋙ (ModuleCat.uliftFunctor.{max u s,w} k).mapHomologicalComplex (.up ℕ) ≅ L)
    (V : ℕ → A ⥤ ModuleCat.{max u w s} k)
    (δ : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ, (V n).obj S.X₃ ⟶ (V (n+1)).obj S.X₁)
    (e : ∀ n, V n ≅ L ⋙ HomologicalComplex.homologyFunctor _ (.up ℕ) n) : Prop :=
  ∃ hex : ∀ {S : ShortComplex A}, S.ShortExact → (S.map K).ShortExact,
    let U := ModuleCat.uliftFunctor.{max u s,w} k
    let c (n : ℕ) (X : A) := (e n).hom.app X ≫
      HomologicalComplex.homologyMap (b.inv.app X) n ≫ (((K.obj X).sc n).mapHomologyIso U).hom
    ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
      δ hS n ≫ c (n+1) S.X₁ = c n S.X₃ ≫ U.map ((hex hS).δ n (n+1) rfl)

def originalConnectorsExpected : Prop :=
  ∀ (k : Type u) [CommRing k] {A : Type y} [Category.{z} A] [Abelian A]
    (K : A ⥤ CochainComplex (ModuleCat.{w} k) ℕ) [K.PreservesZeroMorphisms]
    (L : A ⥤ CochainComplex (ModuleCat.{max u w s} k) ℕ) [L.PreservesZeroMorphisms]
    (b : K ⋙ (ModuleCat.uliftFunctor.{max u s,w} k).mapHomologicalComplex (.up ℕ) ≅ L)
    (V : ℕ → A ⥤ ModuleCat.{max u w s} k)
    (δ : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ, (V n).obj S.X₃ ⟶ (V (n+1)).obj S.X₁)
    (e : ∀ n, V n ≅ L ⋙ HomologicalComplex.homologyFunctor _ (.up ℕ) n),
    GroupHochschildSerre.PreservesCochainConnectors.{u,0,max w s} k L V δ e →
      OriginalConnectors.{u,w,s} k K L b V δ e

section Pages

open AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
open AdvancedHomologicalAlgebra.GrothendieckEdges
open AdvancedHomologicalAlgebra.G05FilteredEdges
open Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

local instance standardDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

local instance repInjectives (R : Type u) (H : Type v) [CommRing R] [Group H]
    [Small.{w} R[H]] : EnoughInjectives (Rep.{w} R H) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughInjectives_iff.mpr inferInstance

variable (N : Subgroup G) [N.Normal]

open Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction (restriction) in
/-- The three normalized ambient comparisons after restriction to the
original coefficients. Their maps are induced by pointwise cochain isos. -/
def OriginalNormalization (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (hQ : SquareZero.{u,v,w} k (G ⧸ N)) (C : CohomologyModels.{u,v,max w s} k G N) : Prop :=
  let I := coefficientLift.{u,v,w,s} k G
  let IQ := coefficientLift.{u,v,w,s} k (G ⧸ N)
  let r := Rep.resFunctor.{w} N.subtype
  let r' := Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.restriction.{u,v,max w s} k G N
  let U := scalarLift.{u,v,w,s} k
  ∃ (a : homogeneousFunctor hG ⋙ U.mapHomologicalComplex (.up ℕ) ≅ I ⋙ repHomogeneousFunctor.{u,v,max w s} k G)
    (b : (r ⋙ homogeneousFunctor hN) ⋙ U.mapHomologicalComplex (.up ℕ) ≅
      I ⋙ (r' ⋙ repHomogeneousFunctor.{u,v,max w s} k N))
    (c : homogeneousFunctor hQ ⋙ U.mapHomologicalComplex (.up ℕ) ≅
      IQ ⋙ repHomogeneousFunctor.{u,v,max w s} k (G ⧸ N)),
    (∀ (M : Rep.{w} k G) n (f : cochains M n) (t : Fin (n+1) → G),
      (((((a.hom.app M).f n).hom (ULift.up f)).hom (GroupBar.Large.single k G t 1))).down =
        M.ρ.asModuleEquiv.symm (f.val t)) ∧
    (∀ (M : Rep.{w} k G) n (f : cochains (Rep.res N.subtype M) n) (t : Fin (n+1) → N),
      (((((b.hom.app M).f n).hom (ULift.up f)).hom (GroupBar.Large.single k N t 1))).down =
        M.ρ.asModuleEquiv.symm (f.val t)) ∧
    (∀ (M : Rep.{w} k (G ⧸ N)) n (f : cochains M n) (t : Fin (n+1) → G ⧸ N),
      (((((c.hom.app M).f n).hom (ULift.up f)).hom (GroupBar.Large.single k (G ⧸ N) t 1))).down =
        M.ρ.asModuleEquiv.symm (f.val t)) ∧
    OriginalConnectors.{u,max v w,s} k _ _ a
      (fun n => I ⋙ rightValue (totalInvariants.{u,v,max w s} k G N) n)
      (fun h n => rightBoundary (totalInvariants.{u,v,max w s} k G N) (liftShortExact.{u,v,w,s} h) n)
      (fun n => Functor.isoWhiskerLeft I (C.totalDerived n)) ∧
    OriginalConnectors.{u,max v w,s} k _ _ b
      (fun n => I ⋙ rightValue (subgroupInvariants.{u,v,max w s} k G N) n ⋙ forgetQuotient.{u,v,max w s} k G N)
      (fun h n => (forgetQuotient.{u,v,max w s} k G N).map
        (rightBoundary (subgroupInvariants.{u,v,max w s} k G N) (liftShortExact.{u,v,w,s} h) n))
      (fun n => Functor.isoWhiskerLeft I (Functor.isoWhiskerRight (C.subgroupDerived n) _ ≪≫ C.underlying n)) ∧
    OriginalConnectors.{u,max v w,s} k _ _ c
      (fun n => IQ ⋙ rightValue (quotientInvariants.{u,v,max w s} k G N) n)
      (fun h n => rightBoundary (quotientInvariants.{u,v,max w s} k G N) (liftShortExact.{u,v,w,s} h) n)
      (fun n => Functor.isoWhiskerLeft IQ (C.quotientDerived n))

def originalNormalizationExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]
    (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (hQ : SquareZero.{u,v,w} k (G ⧸ N)) (C : CohomologyModels.{u,v,max w s} k G N),
    OriginalNormalization.{u,v,w,s} N hG hN hQ C

/-- The coefficient of the original second page is the homogeneous
subgroup cohomology carrier with its induced quotient action. -/
structure PageCoefficients (hN : SquareZero.{u,v,w} k N)
    (C : CohomologyModels.{u,v,max w s} k G N) where
  action : ∀ (M : Rep.{w} k G) (q : ℕ),
    Representation k (G ⧸ N) ((complex hN (Rep.res N.subtype M)).homology q)
  formula : ∀ M q (g : G), action M q (QuotientGroup.mk' N g) =
    (HomologicalComplex.homologyMap (conjugation N hN M g) q).hom
  subgroup : ∀ (M : Rep.{w} k G) (q : ℕ), Rep.of (action M q) ≃ₗ[k]
    (C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj M)
  subgroup_action : ∀ M q g x, subgroup M q (action M q g x) =
    ((C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj M)).ρ g (subgroup M q x)
  subgroup_naturality : ∀ {M L : Rep.{w} k G} (f : M ⟶ L) (q : ℕ)
    (x : (complex hN (Rep.res N.subtype M)).homology q),
    subgroup L q ((HomologicalComplex.homologyMap
      ((homogeneousFunctor hN).map (Rep.resMap N.subtype f)) q).hom x) =
    ((C.subgroup q).map ((coefficientLift.{u,v,w,s} k G).map f)).hom (subgroup M q x)
  coefficient : ∀ (M : Rep.{w} k G), M ≃ₗ[k] (coefficientLift.{u,v,w,s} k G).obj M
  coefficient_action : ∀ (M : Rep.{w} k G) (g : G) (m : M),
    coefficient M (M.ρ g m) = (((coefficientLift.{u,v,w,s} k G).obj M).ρ g) (coefficient M m)
  coefficient_formula : ∀ (M : Rep.{w} k G) (m : M),
    (coefficient M m).down = M.ρ.asModuleEquiv.symm m
  subgroupBar : ∀ (M : Rep.{w} k G),
    BarComparison.{u,v,w,s} hN (Rep.res N.subtype M)
      (Rep.res N.subtype ((coefficientLift.{u,v,w,s} k G).obj M)) (coefficient M)
  subgroup_coordinates : ∀ M q x,
    ((C.underlying q).hom.app ((coefficientLift.{u,v,w,s} k G).obj M)).hom (subgroup M q x) =
      (subgroupBar M).linearEquiv q x

structure PageComparisons (hG : SquareZero.{u,v,w} k G)
    (hN : SquareZero.{u,v,w} k N) (hQ : SquareZero.{u,v,max v w} k (G ⧸ N))
    (C : CohomologyModels.{u,v,max w s} k G N) extends PageCoefficients.{u,v,w,s} N hN C where
  groupBar : ∀ (M : Rep.{w} k G),
    BarComparison.{u,v,w,s} hG M ((coefficientLift.{u,v,w,s} k G).obj M) (coefficient M)
  quotientPresentation : repHomogeneousFunctor.{u,v,max w s} k (G ⧸ N) ≅
    repHomogeneousFunctor.{u,v,max v w s} k (G ⧸ N)
  quotientPresentation_formula : ∀ (L : Rep.{max u v w s} k (G ⧸ N)) n
    (φ : ((repHomogeneousFunctor.{u,v,max w s} k (G ⧸ N)).obj L).X n) (c : Fin (n+1) → G ⧸ N),
    (((quotientPresentation.hom.app L).f n).hom φ).hom
      (GroupBar.Large.single.{u,v,max v w s} k (G ⧸ N) c 1) =
    φ.hom (GroupBar.Large.single.{u,v,max w s} k (G ⧸ N) c 1)
  quotientBar : ∀ (M : Rep.{w} k G) q,
    BarComparison.{u,v,max v w,s} hQ (Rep.of (action M q))
      ((C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj M)) (subgroup M q)

variable {N}

section
variable {hG : SquareZero.{u,v,w} k G} {hN : SquareZero.{u,v,w} k N}
  {hQ : SquareZero.{u,v,max v w} k (G ⧸ N)}
  {C : CohomologyModels.{u,v,max w s} k G N}
  {P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N)}
  (E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P)
  (A : PageComparisons.{u,v,w,s} N hG hN hQ C) (M : Rep.{w} k G)

/-- Original coordinates for the very same (E_2) and the same filtered
target, by composition with the normalized ambient comparisons. -/
def PageComparisons.second (p q : ℕ) :
    (((objectSequence _ _ P).obj ((coefficientLift.{u,v,w,s} k G).obj M)).page 0 p
      ((p : ℤ) + q)) ≅
      (scalarLift.{u,v,w,s} k).obj ((complex hQ (Rep.of (A.action M q))).homology p) :=
  (displayedSecond C E p q).app ((coefficientLift.{u,v,w,s} k G).obj M) ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℕ) p).mapIso
      (A.quotientPresentation.app ((C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj M))) ≪≫
    ((A.quotientBar M q).onHomology p).symm

def PageComparisons.target (n : ℕ) :
    ((objectSequence _ _ P).obj ((coefficientLift.{u,v,w,s} k G).obj M)).target n ≅
      (scalarLift.{u,v,w,s} k).obj ((complex hG M).homology n) :=
  (displayedTarget C E n).app ((coefficientLift.{u,v,w,s} k G).obj M) ≪≫
    ((A.groupBar M).onHomology n).symm

/-- The map on the quotient coefficient is induced by ordinary
postcomposition of subgroup cochains. -/
def PageComparisons.subgroupMap {M L : Rep.{w} k G} (f : M ⟶ L) (q : ℕ) :
    Rep.of (A.action M q) ⟶ Rep.of (A.action L q) :=
  Rep.ofHom ⟨(HomologicalComplex.homologyMap
    ((homogeneousFunctor hN).map (Rep.resMap N.subtype f)) q).hom, fun g => by
      apply LinearMap.ext
      intro x
      apply (A.subgroup L q).injective
      let b := (C.subgroup q).map ((coefficientLift.{u,v,w,s} k G).map f)
      let t := (HomologicalComplex.homologyMap ((homogeneousFunctor hN).map
        (Rep.resMap N.subtype f)) q).hom
      change A.subgroup L q (t (A.action M q g x)) = A.subgroup L q (A.action L q g (t x))
      calc
        _ = b.hom (A.subgroup M q (A.action M q g x)) := A.subgroup_naturality f q _
        _ = b.hom (((C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj M)).ρ g (A.subgroup M q x)) :=
          congrArg b.hom (A.subgroup_action M q g x)
        _ = ((C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj L)).ρ g (b.hom (A.subgroup M q x)) :=
          Rep.hom_comm_apply b g _
        _ = ((C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj L)).ρ g (A.subgroup L q (t x)) :=
          congrArg (((C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj L)).ρ g) (A.subgroup_naturality f q x).symm
        _ = _ := (A.subgroup_action L q g (t x)).symm⟩

/-- Both displayed identifications respect the original coefficient maps. -/
def PageComparisons.Natural : Prop :=
  ∀ (M L : Rep.{w} k G) (f : M ⟶ L),
    let b := (coefficientLift.{u,v,w,s} k G).map f
    let D := (objectSequence _ _ P).map b
    let U := scalarLift.{u,v,w,s} k
    (∀ p q : ℕ,
      D.page 0 p ((p : ℤ) + q) ≫ (A.second E L p q).hom =
        (A.second E M p q).hom ≫
          U.map (HomologicalComplex.homologyMap
            ((homogeneousFunctor hQ).map (A.subgroupMap f q)) p)) ∧
    (∀ n : ℕ, D.target n ≫ (A.target E L n).hom =
      (A.target E M n).hom ≫ U.map (HomologicalComplex.homologyMap ((homogeneousFunctor hG).map f) n))

end

def pageComparisonsExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]
    (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (hQ : SquareZero.{u,v,max v w} k (G ⧸ N))
    (C : CohomologyModels.{u,v,max w s} k G N), Nonempty (PageComparisons.{u,v,w,s} N hG hN hQ C)

section OriginalEdges

variable {hG : SquareZero.{u,v,w} k G} {hN : SquareZero.{u,v,w} k N}
  {hQ : SquareZero.{u,v,max v w} k (G ⧸ N)} {hQ₀ : SquareZero.{u,v,w} k (G ⧸ N)}
  {C : CohomologyModels.{u,v,max w s} k G N}
  {P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N)}
  {E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P}

structure OriginalEdges (A : PageComparisons.{u,v,w,s} N hG hN hQ C) (e : EdgeIdentifications C P E)
    (hQ₀ : SquareZero.{u,v,w} k (G ⧸ N)) (M : Rep.{w} k G) where
  fixedCompare : fixed N M ≃ₗ[k] fixed N ((coefficientLift.{u,v,w,s} k G).obj M)
  fixed_formula : ∀ m, (fixedCompare m).val = A.coefficient M m.val
  rowBar : BarComparison.{u,v,w,s} hQ₀ (fixed N M) (fixed N ((coefficientLift.{u,v,w,s} k G).obj M)) fixedCompare
  column : ∀ n : ℕ, (A.action M n).invariants ≃ₗ[k]
    (C.subgroup n ⋙ quotientInvariants.{u,v,max w s} k G N).obj ((coefficientLift.{u,v,w,s} k G).obj M)
  column_formula : ∀ n m, (column n m).val = A.subgroup M n m.val
  restrict : ∀ n : ℕ, (complex hG M).homology n ⟶ ModuleCat.of k (A.action M n).invariants
  restrict_formula : ∀ n x, ((restrict n).hom x).val =
    (HomologicalComplex.homologyMap (restriction N hG hN M) n).hom x
  inflation_compare : ∀ n x, (A.groupBar M).linearEquiv n
      ((HomologicalComplex.homologyMap (inflation N hG hQ₀ M) n).hom x) =
    (HomologicalComplex.homologyMap (e.inflationCochain.app ((coefficientLift.{u,v,w,s} k G).obj M)) n).hom
      (rowBar.linearEquiv n x)
  restriction_compare : ∀ n x, column n ((restrict n).hom x) =
    ((e.restriction.map n).app ((coefficientLift.{u,v,w,s} k G).obj M)).hom
      ((A.groupBar M).linearEquiv n x)

/-- The original transgression is the same second differential in the
reduced column and row coordinates. -/
def OriginalEdges.transgression {A : PageComparisons.{u,v,w,s} N hG hN hQ C} {e : EdgeIdentifications C P E}
    {M : Rep.{w} k G} (o : OriginalEdges.{u,v,w,s} A e hQ₀ M) :
    ModuleCat.of k (A.action M 1).invariants ⟶ (complex hQ₀ (fixed N M)).homology 2 :=
  ModuleCat.ofHom (((o.column 1).arrowCongr (o.rowBar.linearEquiv 2)).symm
    (ordinaryTransgression C E ((coefficientLift.{u,v,w,s} k G).obj M)).hom)

section
variable {A : PageComparisons.{u,v,w,s} N hG hN hQ C} {e : EdgeIdentifications C P E}
  {M : Rep.{w} k G} (o : OriginalEdges.{u,v,w,s} A e hQ₀ M)

def OriginalEdges.row (n : ℕ) :
    ((objectSequence _ _ P).obj ((coefficientLift.{u,v,w,s} k G).obj M)).page 0 n n ≅
      (scalarLift.{u,v,w,s} k).obj ((complex hQ₀ (fixed N M)).homology n) :=
  (rowCoordinates C E n).app ((coefficientLift.{u,v,w,s} k G).obj M) ≪≫ (o.rowBar.onHomology n).symm

def OriginalEdges.invariantIso (n : ℕ) :
    (scalarLift.{u,v,w,s} k).obj (ModuleCat.of k (A.action M n).invariants) ≅
      (C.subgroup n ⋙ quotientInvariants.{u,v,max w s} k G N).obj ((coefficientLift.{u,v,w,s} k G).obj M) :=
  (ULift.moduleEquiv.trans (o.column n)).toModuleIso

def OriginalEdges.columnPage (n : ℕ) :
    ((objectSequence _ _ P).obj ((coefficientLift.{u,v,w,s} k G).obj M)).page 0 0 n ≅
      (scalarLift.{u,v,w,s} k).obj (ModuleCat.of k (A.action M n).invariants) :=
  (columnCoordinates C E n).app ((coefficientLift.{u,v,w,s} k G).obj M) ≪≫ (o.invariantIso n).symm

/-- Reduce the second-page bottom row using the degree-zero fixed-coefficient
identification from the same normalized comparison. -/
def OriginalEdges.rowReduction (n : ℕ) :
    (scalarLift.{u,v,w,s} k).obj ((complex hQ₀ (fixed N M)).homology n) ≅
      (scalarLift.{u,v,w,s} k).obj ((complex hQ (Rep.of (A.action M 0))).homology n) :=
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  let F := HomologicalComplex.homologyFunctor _ (.up ℕ) n
  o.rowBar.onHomology n ≪≫
    (Functor.isoWhiskerRight (E.degreeZeroF ≪≫ C.subgroupDerived 0)
      (repHomogeneousCohomology.{u,v,max w s} k (G ⧸ N) n)).app L ≪≫
    F.mapIso (A.quotientPresentation.app ((C.subgroup 0).obj L)) ≪≫ ((A.quotientBar M 0).onHomology n).symm

/-- Reduce the second-page left column using the fixed subgroup cohomology
classes in degree zero of quotient cohomology. -/
def OriginalEdges.columnReduction (n : ℕ) :
    (scalarLift.{u,v,w,s} k).obj (ModuleCat.of k (A.action M n).invariants) ≅
      (scalarLift.{u,v,w,s} k).obj ((complex hQ (Rep.of (A.action M n))).homology 0) :=
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  let F := HomologicalComplex.homologyFunctor _ (.up ℕ) 0
  o.invariantIso n ≪≫
    (Functor.isoWhiskerLeft (C.subgroup n) (E.degreeZero.symm ≪≫ C.quotientDerived 0)).app L ≪≫
    F.mapIso (A.quotientPresentation.app ((C.subgroup n).obj L)) ≪≫ ((A.quotientBar M n).onHomology 0).symm

def OriginalEdges.PageCoordinatesCompatibility : Prop :=
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  (∀ n, A.second E M n 0 =
    (rowIndexIso _ _ P n).app L ≪≫ o.row n ≪≫ o.rowReduction n) ∧
  (∀ n, A.second E M 0 n =
    (columnIndexIso _ _ P n).app L ≪≫ o.columnPage n ≪≫ o.columnReduction n)

def OriginalEdges.FilteredCompatibility : Prop :=
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  let U := scalarLift.{u,v,w,s} k
  (∀ n : ℕ, (o.row n).hom ≫ U.map (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) n) =
    (E.filtered L).row n ≫ (A.target E M n).hom) ∧
  (∀ n : ℕ, (A.target E M n).hom ≫ U.map (o.restrict n) =
    (E.filtered L).column n ≫ (o.columnPage n).hom) ∧
  (o.columnPage 1).hom ≫ U.map o.transgression =
    AdvancedHomologicalAlgebra.G05FilteredEdges.transgression
      ((objectSequence _ _ P).obj L) ≫ (o.row 2).hom

/-- The reductions of the displayed row and column at degree zero send
the original fixed elements to their augmented homogeneous classes. -/
def OriginalEdges.ZeroCoordinates : Prop :=
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  (∀ m : M.ρ.invariants,
    let K := complex hG M
    ∃ (l : (totalInvariants.{u,v,max w s} k G N).obj L) (z : K.cycles 0),
      l.val.val = A.coefficient M m.val ∧
      (∀ c : Fin 1 → G, ((K.iCycles 0).hom z).val c = m.val) ∧
      (A.groupBar M).linearEquiv 0 ((K.homologyπ 0).hom z) =
        ((C.totalDerived 0).hom.app L).hom (((degreeZeroUnit (totalInvariants.{u,v,max w s} k G N)).app L).hom l)) ∧
  (∀ m : fixed N M,
    let K := complex hN (Rep.res N.subtype M)
    ∃ z : K.cycles 0,
      (∀ c : Fin 1 → N, ((K.iCycles 0).hom z).val c = m.val) ∧
      A.subgroup M 0 ((K.homologyπ 0).hom z) =
        ((E.degreeZeroF ≪≫ C.subgroupDerived 0).hom.app L).hom (o.fixedCompare m)) ∧
  (∀ (n : ℕ) (m : (A.action M n).invariants),
    let K := complex hQ (Rep.of (A.action M n))
    let V := (C.subgroup n).obj L
    ∃ z : K.cycles 0,
      (∀ c : Fin 1 → G ⧸ N, ((K.iCycles 0).hom z).val c = m.val) ∧
      (A.quotientBar M n).linearEquiv 0 ((K.homologyπ 0).hom z) =
        (HomologicalComplex.homologyMap (A.quotientPresentation.hom.app V) 0).hom
          (((E.degreeZero.symm ≪≫ C.quotientDerived 0).hom.app V).hom (o.column n m)))

end

end OriginalEdges

/-- The original-coefficient five terms with their filtered edge squares. -/
def SpectralSequenceEdges (k : Type u) (G : Type v) [CommRing k] [Group G]
    (N : Subgroup G) [N.Normal] : Prop :=
  ∃ (P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N))
    (E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P)
    (C : CohomologyModels.{u,v,max w s} k G N) (e : EdgeIdentifications C P E)
    (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (hQ : SquareZero.{u,v,max v w} k (G ⧸ N)) (hQ₀ : SquareZero.{u,v,w} k (G ⧸ N))
    (A : PageComparisons.{u,v,w,s} N hG hN hQ C),
    OriginalNormalization.{u,v,w,s} N hG hN hQ₀ C ∧ PageComparisons.Natural E A ∧
    (∀ (M : Rep.{w} k G) (r : ℕ) (p n : ℤ), p < 0 ∨ n < p →
      IsZero (((objectSequence _ _ P).obj ((coefficientLift.{u,v,w,s} k G).obj M)).page r p n)) ∧
    ∀ M : Rep.{w} k G, ∃ o : OriginalEdges.{u,v,w,s} A e hQ₀ M,
      o.FilteredCompatibility ∧ o.PageCoordinatesCompatibility ∧ o.ZeroCoordinates ∧
      ClassicalFiveTerms (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) 1)
        (o.restrict 1) o.transgression (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) 2)

def spectralSequenceEdgesExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    SpectralSequenceEdges.{u,v,w,s} k G N

namespace Mixed

universe a b t

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Pointwise pullback placed in a common scalar category by exact carrier lifts. -/
def commonPullback {H : Type v} [Group H]
    {hG : SquareZero.{u,v,a} k G} {hH : SquareZero.{u,v,b} k H}
    {M : Rep.{a} k G} {L : Rep.{b} k H}
    (r : H →* G) (f : M →ₗ[k] L)
    (hf : ∀ g m, f (M.ρ (r g) m) = L.ρ g (f m)) :
    ((liftedFunctor.{u,v,a,max v b t} hG).obj M) ⟶
      ((liftedFunctor.{u,v,b,max v a t} hH).obj L) where
  f n := ModuleCat.ofHom (show ULift.{max u v b t} (cochains M n) →ₗ[k]
      ULift.{max u v a t} (cochains L n) from
    ULift.moduleEquiv.symm.toLinearMap.comp
      ((pullbackDegree r f hf n).comp ULift.moduleEquiv.toLinearMap))
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    simp only [liftedFunctor, Functor.comp_obj, Functor.mapHomologicalComplex_obj_d,
      homogeneousFunctor, complex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨φ⟩
    apply ULift.ext
    apply Subtype.ext
    funext c
    change (differential L i (pullbackDegree r f hf i φ)).val c =
      (pullbackDegree r f hf (i+1) (differential M i φ)).val c
    change (∑ l : Fin (i+2), (-1 : k) ^ l.val • f (φ.val ((r ∘ c) ∘ l.succAbove))) =
      f (∑ l : Fin (i+2), (-1 : k) ^ l.val • φ.val ((r ∘ c) ∘ l.succAbove))
    simp only [map_sum, map_smul]

/-- The map on the lifts of the original homology modules uses the two
exact scalar-lift comparisons for the specified chain map. -/
def commonHomologyMap {K : CochainComplex (ModuleCat.{a} k) ℕ}
    {L : CochainComplex (ModuleCat.{b} k) ℕ}
    (φ : ((ModuleCat.uliftFunctor.{max u b t,a} k).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((ModuleCat.uliftFunctor.{max u a t,b} k).mapHomologicalComplex (.up ℕ)).obj L)
    (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u b t,a} k).obj (K.homology n) ⟶
      (ModuleCat.uliftFunctor.{max u a t,b} k).obj (L.homology n) :=
  ((K.sc n).mapHomologyIso (ModuleCat.uliftFunctor.{max u b t,a} k)).inv ≫ HomologicalComplex.homologyMap φ n ≫
    ((L.sc n).mapHomologyIso (ModuleCat.uliftFunctor.{max u a t,b} k)).hom

/-- The induced linear map between the original cohomology carriers. -/
def originalHomologyMap {K : CochainComplex (ModuleCat.{a} k) ℕ}
    {L : CochainComplex (ModuleCat.{b} k) ℕ}
    (φ : ((ModuleCat.uliftFunctor.{max u b t,a} k).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((ModuleCat.uliftFunctor.{max u a t,b} k).mapHomologicalComplex (.up ℕ)).obj L)
    (n : ℕ) : K.homology n →ₗ[k] L.homology n :=
  ULift.moduleEquiv.toLinearMap.comp
    ((commonHomologyMap.{u,a,b,t} φ n).hom.comp ULift.moduleEquiv.symm.toLinearMap)

/-- Carry the given map of representations into the common module category.
The two equivariant carrier identifications are over the unchanged group algebra. -/
def commonCoefficientMap {M : Rep.{a} k G} {L : Rep.{b} k G}
    (f : M.ρ.IntertwiningMap L.ρ) :
    (coefficientLift.{u,v,a,max b t} k G).obj M ⟶
      (coefficientLift.{u,v,b,max a t} k G).obj L := by
  let e := liftCoeffEquiv.{u,v,a,max b t} M
  let e' := liftCoeffEquiv.{u,v,b,max a t} L
  refine Rep.ofHom (ρ := ((coefficientLift.{u,v,a,max b t} k G).obj M).ρ)
    (σ := ((coefficientLift.{u,v,b,max a t} k G).obj L).ρ)
    ⟨e'.toLinearMap.comp (f.toLinearMap.comp e.symm.toLinearMap), ?_⟩
  intro g
  apply LinearMap.ext
  intro y
  obtain ⟨m, rfl⟩ := e.surjective y
  change e' (f (e.symm (((coefficientLift.{u,v,a,max b t} k G).obj M).ρ g (e m)))) =
    ((coefficientLift.{u,v,b,max a t} k G).obj L).ρ g (e' (f (e.symm (e m))))
  change e' (f (e.symm (((coefficientLift.{u,v,a,max b t} k G).obj M).ρ g
    (liftCoeffEquiv.{u,v,a,max b t} M m)))) = _
  rw [← liftCoeffEquiv_action.{u,v,a,max b t}, e.symm_apply_apply, e.symm_apply_apply,
    Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f]
  exact liftCoeffEquiv_action.{u,v,b,max a t} L g (f m)

lemma commonCoefficientMap_apply {M : Rep.{a} k G} {L : Rep.{b} k G}
    (f : M.ρ.IntertwiningMap L.ρ) (m : M) :
    (commonCoefficientMap.{u,v,a,b,t} f).hom (liftCoeffEquiv.{u,v,a,max b t} M m) =
      liftCoeffEquiv.{u,v,b,max a t} L (f m) :=
  congrArg (fun x => liftCoeffEquiv.{u,v,b,max a t} L (f x))
    ((liftCoeffEquiv.{u,v,a,max b t} M).symm_apply_apply m)

-- The extra lift by the group universe in these scalar maps is already
-- present in the types of the original homogeneous function spaces.
abbrev cohomologyMap {H : Type v} [Group H]
    {hG : SquareZero.{u,v,a} k G} {hH : SquareZero.{u,v,b} k H}
    {M : Rep.{a} k G} {L : Rep.{b} k H} (r : H →* G)
    (f : M →ₗ[k] L) (hf : ∀ g m, f (M.ρ (r g) m) = L.ρ g (f m)) (n : ℕ) :=
  originalHomologyMap.{u,max v a,max v b,t}
    (commonPullback.{u,v,a,b,t} (hG := hG) (hH := hH) r f hf) n

/-- The map between the original homologies sends a homogeneous cocycle
to the class of its pointwise pullback along the given group and coefficient maps. -/
def cohomologyMapOnClassesExpected : Prop :=
  ∀ (k : Type u) (G H : Type v) [CommRing k] [Group G] [Group H]
    (hG : SquareZero.{u,v,a} k G) (hH : SquareZero.{u,v,b} k H)
    (M : Rep.{a} k G) (L : Rep.{b} k H)
    (r : H →* G) (f : M →ₗ[k] L)
    (hf : ∀ g m, f (M.ρ (r g) m) = L.ρ g (f m))
    (n : ℕ) (z : (complex hG M).cycles n),
    ∃ z' : (complex hH L).cycles n,
      (∀ c : Fin (n+1) → H,
        (((complex hH L).iCycles n).hom z').val c =
          f ((((complex hG M).iCycles n).hom z).val (r ∘ c))) ∧
      cohomologyMap.{u,v,a,b,t} (hG := hG) (hH := hH) r f hf n
          (((complex hG M).homologyπ n).hom z) = ((complex hH L).homologyπ n).hom z'

/-- Restrict a mixed coefficient map to the given fixed submodules. -/
def onInvariants {V : Type a} {W : Type b} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W)
    (f : ρ.IntertwiningMap σ) : ρ.invariants →ₗ[k] σ.invariants :=
  (f.toLinearMap.comp ρ.invariants.subtype).codRestrict σ.invariants fun z g => by
    change σ g (f z.val) = f z.val
    rw [← Representation.IntertwiningMap.isIntertwining ρ σ f, z.property g]

/-- The map between the original normal-subgroup invariant coefficients
with their original quotient actions. -/
def fixedMap (N : Subgroup G) [N.Normal] {M : Rep.{a} k G} {L : Rep.{b} k G} (f : M.ρ.IntertwiningMap L.ρ) :
    (fixed N M).ρ.IntertwiningMap (fixed N L).ρ where
  toLinearMap := onInvariants (M.ρ.comp N.subtype) (L.ρ.comp N.subtype)
    ⟨f.toLinearMap, fun g => f.isIntertwining' g⟩
  isIntertwining' q := by
    induction q using QuotientGroup.induction_on with
    | H g =>
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f g z.val

section MixedNaturality

variable {hG : SquareZero.{u,v,a} k G} {hN : SquareZero.{u,v,a} k N}
  {hQ : SquareZero.{u,v,max v a} k (G ⧸ N)}
  {hG' : SquareZero.{u,v,b} k G} {hN' : SquareZero.{u,v,b} k N}
  {hQ' : SquareZero.{u,v,max v b} k (G ⧸ N)}
  {C : CohomologyModels.{u,v,max v a b t} k G N}
  {P : Package (subgroupInvariants.{u,v,max v a b t} k G N)
    (quotientInvariants.{u,v,max v a b t} k G N)}
  (E : ObjectEdges (subgroupInvariants.{u,v,max v a b t} k G N)
    (quotientInvariants.{u,v,max v a b t} k G N) P)
  (A : PageComparisons.{u,v,a,max v b t} N hG hN hQ C)
  (B : PageComparisons.{u,v,b,max v a t} N hG' hN' hQ' C)

/-- The map of the same filtered sequence in the common category is
postcomposition on the actual original coefficients, including on the
subgroup cohomology coefficient of the second page. -/
def PageNaturality : Prop :=
  ∀ (M : Rep.{a} k G) (L : Rep.{b} k G) (f : M.ρ.IntertwiningMap L.ρ),
    let D := (objectSequence _ _ P).map (commonCoefficientMap.{u,v,a,b,t} f)
    ∃ (fQ : ∀ q, (A.action M q).IntertwiningMap (B.action L q)),
      (∀ q z, fQ q z =
        cohomologyMap.{u,v,a,b,t} (hG := hN) (hH := hN')
          (M := Rep.res N.subtype M) (L := Rep.res N.subtype L)
          (MonoidHom.id N) f.toLinearMap (fun g x => Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f (g : G) x) q z) ∧
      (∀ p q : ℕ,
        D.page 0 p ((p : ℤ) + q) ≫ (B.second E L p q).hom =
          (A.second E M p q).hom ≫
            commonHomologyMap.{u,max v a,max v b,t}
              (commonPullback.{u,v,max v a,max v b,t} (hG := hQ) (hH := hQ')
                (M := Rep.of (A.action M q)) (L := Rep.of (B.action L q))
                (MonoidHom.id (G ⧸ N)) (fQ q).toLinearMap (Representation.IntertwiningMap.isIntertwining _ _ (fQ q))) p) ∧
      ∀ n : ℕ, D.target n ≫ (B.target E L n).hom =
        (A.target E M n).hom ≫
          commonHomologyMap.{u,max v a,max v b,t}
            (commonPullback.{u,v,a,b,t} (hG := hG) (hH := hG')
              (MonoidHom.id G) f.toLinearMap (Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f)) n

open Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction in
/-- Naturality for all comparison maps between ambient injective resolutions
of the two lifts, with the quotient actions on the original carriers. -/
def InjectiveNaturality : Prop :=
  let liftM := coefficientLift.{u,v,a,max v b t} k G
  let liftL := coefficientLift.{u,v,b,max v a t} k G
  let F := normalInvariants.{u,v,max v a b t} k G N
  let K {X : Rep.{max u v a b t} k G} (I : InjectiveResolution X) :=
    invariantResolutionComplex.{u,v,max v a b t} k G N X I
  ∃ (c : ∀ (M : Rep.{a} k G) (j : ℕ) (I : InjectiveResolution (liftM.obj M)),
        (complex hN (Rep.res N.subtype M)).homology j ≃ₗ[k] (K I).homology j)
    (c' : ∀ (L : Rep.{b} k G) (j : ℕ) (J : InjectiveResolution (liftL.obj L)),
        (complex hN' (Rep.res N.subtype L)).homology j ≃ₗ[k] (K J).homology j),
    (∀ M j I q z, c M j I (A.action M j q z) = ((K I).homology j).ρ q (c M j I z)) ∧
    (∀ L j J q z, c' L j J (B.action L j q z) = ((K J).homology j).ρ q (c' L j J z)) ∧
    ∀ (M : Rep.{a} k G) (L : Rep.{b} k G) (f : M.ρ.IntertwiningMap L.ρ)
      (j : ℕ) (I : InjectiveResolution (liftM.obj M)) (J : InjectiveResolution (liftL.obj L))
      (φ : InjectiveResolution.Hom I J (commonCoefficientMap.{u,v,a,b,t} f))
      (z : (complex hN (Rep.res N.subtype M)).homology j),
      c' L j J (cohomologyMap.{u,v,a,b,t} (hG := hN) (hH := hN')
        (M := Rep.res N.subtype M) (L := Rep.res N.subtype L)
        (MonoidHom.id N) f.toLinearMap (fun g x => Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f (g : G) x) j z) =
        (HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.up ℕ)).map φ.hom) j).hom (c M j I z)

/-- The ordinary edges and transgression commute with the maps of original
cohomologies after the same exact scalar lifts. -/
def EdgesNatural
    {hQ₀ : SquareZero.{u,v,a} k (G ⧸ N)} {hQ₀' : SquareZero.{u,v,b} k (G ⧸ N)}
    (e : EdgeIdentifications C P E) : Prop :=
  ∀ (M : Rep.{a} k G) (L : Rep.{b} k G) (f : M.ρ.IntertwiningMap L.ρ)
    (o : OriginalEdges.{u,v,a,max v b t} A e hQ₀ M)
    (o' : OriginalEdges.{u,v,b,max v a t} B e hQ₀' L),
    ∃ fQ : ∀ q, (A.action M q).IntertwiningMap (B.action L q),
      (∀ q z, fQ q z = cohomologyMap.{u,v,a,b,t} (hG := hN) (hH := hN')
        (M := Rep.res N.subtype M) (L := Rep.res N.subtype L) (MonoidHom.id N)
        f.toLinearMap (fun g x => Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f g x) q z) ∧
      let U := scalarLift.{u,v,a,max v b t} k
      let V := scalarLift.{u,v,b,max v a t} k
      let target := commonHomologyMap.{u,max v a,max v b,t}
        (commonPullback.{u,v,a,b,t} (hG := hG) (hH := hG') (MonoidHom.id G)
          f.toLinearMap (Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f))
      let row := commonHomologyMap.{u,max v a,max v b,t}
        (commonPullback.{u,v,a,b,t} (hG := hQ₀) (hH := hQ₀') (MonoidHom.id (G ⧸ N))
          (fixedMap N f).toLinearMap (Representation.IntertwiningMap.isIntertwining _ _ (fixedMap N f)))
      let column (n : ℕ) :
          U.obj (ModuleCat.of k (A.action M n).invariants) ⟶
            V.obj (ModuleCat.of k (B.action L n).invariants) :=
        ModuleCat.ofHom (show ULift.{max u v b t} (A.action M n).invariants →ₗ[k]
            ULift.{max u v a t} (B.action L n).invariants from
          ULift.moduleEquiv.symm.toLinearMap.comp
            ((onInvariants _ _ (fQ n)).comp ULift.moduleEquiv.toLinearMap))
      (∀ n, row n ≫ V.map (HomologicalComplex.homologyMap (inflation N hG' hQ₀' L) n) =
        U.map (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) n) ≫ target n) ∧
      (∀ n, target n ≫ V.map (o'.restrict n) = U.map (o.restrict n) ≫ column n) ∧
      column 1 ≫ V.map o'.transgression = U.map o.transgression ≫ row 2

end MixedNaturality

/-- Both original carriers have the normalized comparisons and ordinary
edges in one common first-quadrant spectral sequence. -/
def SpectralSequence (k : Type u) (G : Type v) [CommRing k] [Group G]
    (N : Subgroup G) [N.Normal] : Prop :=
  ∃ (P : Package (subgroupInvariants.{u,v,max v a b t} k G N)
      (quotientInvariants.{u,v,max v a b t} k G N))
    (E : ObjectEdges (subgroupInvariants.{u,v,max v a b t} k G N)
      (quotientInvariants.{u,v,max v a b t} k G N) P)
    (C : CohomologyModels.{u,v,max v a b t} k G N) (e : EdgeIdentifications C P E)
    (hG : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,a} k N)
    (hQ : SquareZero.{u,v,max v a} k (G ⧸ N)) (hQ₀ : SquareZero.{u,v,a} k (G ⧸ N))
    (hG' : SquareZero.{u,v,b} k G) (hN' : SquareZero.{u,v,b} k N)
    (hQ' : SquareZero.{u,v,max v b} k (G ⧸ N)) (hQ₀' : SquareZero.{u,v,b} k (G ⧸ N))
    (A : PageComparisons.{u,v,a,max v b t} N hG hN hQ C)
    (B : PageComparisons.{u,v,b,max v a t} N hG' hN' hQ' C),
    OriginalNormalization.{u,v,a,max v b t} N hG hN hQ₀ C ∧
    OriginalNormalization.{u,v,b,max v a t} N hG' hN' hQ₀' C ∧
    PageNaturality.{u,v,a,b,t} E A B ∧ InjectiveNaturality.{u,v,a,b,t} A B ∧
    EdgesNatural.{u,v,a,b,t} E A B (hQ₀ := hQ₀) (hQ₀' := hQ₀') e ∧
    (∀ (X : Rep.{max u v a b t} k G) (r : ℕ) (p n : ℤ), p < 0 ∨ n < p →
      IsZero (((objectSequence _ _ P).obj X).page r p n)) ∧
    (∀ M : Rep.{a} k G, ∃ o : OriginalEdges.{u,v,a,max v b t} A e hQ₀ M,
      o.FilteredCompatibility ∧ o.PageCoordinatesCompatibility ∧ o.ZeroCoordinates ∧
      ClassicalFiveTerms (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) 1)
        (o.restrict 1) o.transgression (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) 2)) ∧
    ∀ L : Rep.{b} k G, ∃ o : OriginalEdges.{u,v,b,max v a t} B e hQ₀' L,
      o.FilteredCompatibility ∧ o.PageCoordinatesCompatibility ∧ o.ZeroCoordinates ∧
      ClassicalFiveTerms (HomologicalComplex.homologyMap (inflation N hG' hQ₀' L) 1)
        (o.restrict 1) o.transgression (HomologicalComplex.homologyMap (inflation N hG' hQ₀' L) 2)

def spectralSequenceExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    SpectralSequence.{u,v,a,b,t} k G N

end Mixed

end Pages

def squareZeroExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], SquareZero.{u,v,w} k G

def pointwiseComparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (h : SquareZero.{u,v,w} k G),
    PointwiseComparison k G h

end Specs.AdvancedHomologicalAlgebra.GroupExtensionOriginalCoefficients
