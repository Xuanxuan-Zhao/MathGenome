import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.BarProjectionKernel
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.LinearAlgebra.Isomorphisms

open CategoryTheory CategoryTheory.Limits Category
open scoped Classical

universe u

namespace ALG02GroupTheory.Transgression

open IntegralBar BarProjectionKernel

noncomputable section

variable {N E Q N' E' Q' : Type u}
variable [Group N] [Group E] [Group Q] [Group N'] [Group E'] [Group Q']

/-- The filtration by the number of entries whose image in the quotient is nonidentity. -/
def barFiltration (S : GroupExtension N E Q) (p n : ℕ) :
    Submodule Integers.{u} (NormalizedModule E n) :=
  Submodule.span _ {x | ∃ t : Fin n → E,
    (Finset.univ.filter (fun j => S.rightHom (t j) ≠ 1)).card ≤ p ∧
    x = normalizedBar n t}

abbrev barBoundary (G : Type u) [Group G] (n : ℕ) :
    NormalizedModule G (n + 1) →ₗ[Integers.{u}] NormalizedModule G n :=
  ((normalizedChains G).d (n + 1) n).hom

/-- The representatives of (E^2_{2,0}). The degree-two chains lie in (F_2),
which is the whole chain group in that degree. -/
abbrev sourceCycles (S : GroupExtension N E Q) :=
  (barFiltration S 0 1).comap (barBoundary E 1)

/-- Degree-two chains in (F_1) with boundary in (F_0). -/
abbrev lowerCycles (S : GroupExtension N E Q) :=
  barFiltration S 1 2 ⊓ sourceCycles S

/-- Relations on (E^2_{2,0}) from (F_1) and the boundaries of degree-three
chains in (F_3), which is the whole chain group in that degree. -/
def sourceRelations (S : GroupExtension N E Q) : Submodule Integers.{u} (sourceCycles S) :=
  (lowerCycles S ⊔ LinearMap.range (barBoundary E 2)).comap (sourceCycles S).subtype

/-- Relations on (E^2_{0,1}). Every degree-one chain is a cycle, and
the relations are the (F_0)-valued boundaries of degree-two chains in (F_1). -/
def targetRelations (S : GroupExtension N E Q) : Submodule Integers.{u} (barFiltration S 0 1) :=
  ((lowerCycles S).map (barBoundary E 1)).comap (barFiltration S 0 1).subtype

/- The filtered-complex representative formula is
   Zᵣ(p,k) = Fₚ Cₖ ∩ d⁻¹(Fₚ₋ᵣ Cₖ₋₁),
   Eʳ(p,k−p) = Zᵣ(p,k) / (Zᵣ₋₁(p−1,k) + d Zᵣ₋₁(p+r−1,k+1)).
   We use it at r=2, (p,k)=(2,2) and (0,1), with Fₚ=0 for p<0. -/
abbrev PageTwoSource (S : GroupExtension N E Q) := sourceCycles S ⧸ sourceRelations S

abbrev PageTwoTarget (S : GroupExtension N E Q) := barFiltration S 0 1 ⧸ targetRelations S

private def boundaryToFiltrationZero (S : GroupExtension N E Q) :
    sourceCycles S →ₗ[Integers.{u}] barFiltration S 0 1 :=
  ((barBoundary E 1).comp (sourceCycles S).subtype).codRestrict _ (fun x => x.property)

/-- The actual boundary induces the second differential between these page-two terms. -/
def pageTwoDifferential (S : GroupExtension N E Q) :
    PageTwoSource S →ₗ[Integers.{u}] PageTwoTarget S :=
  (sourceRelations S).liftQ ((targetRelations S).mkQ.comp (boundaryToFiltrationZero S))
    (by
      intro x hx
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change barBoundary E 1 x.val ∈ (lowerCycles S).map (barBoundary E 1)
      obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (show x.val ∈
        lowerCycles S ⊔ LinearMap.range (barBoundary E 2) from hx)
      obtain ⟨w, rfl⟩ := hz
      refine ⟨y, hy, ?_⟩
      have hdd : barBoundary E 1 (barBoundary E 2 w) = 0 :=
        DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
          ((normalizedChains E).d_comp_d 3 2 1)) w
      rw [← he, map_add, hdd, add_zero])

/-- A cycle constructor for the standard homology associated to a chain complex. -/
def cycleOf (K : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ)
    {n : ℕ} (z : K.X (n + 1)) (hz : K.d (n + 1) n z = 0) : K.cycles (n + 1) :=
  K.cyclesMk z n ((ComplexShape.down ℕ).next_eq' rfl) hz

/-- The homology class of a cycle in positive degree. -/
def classOf (K : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ)
    {n : ℕ} (z : K.X (n + 1)) (hz : K.d (n + 1) n z = 0) : K.homology (n + 1) :=
  K.homologyπ (n + 1) (cycleOf K z hz)

/-- The ordinary connecting map of the short exact sequence of normalized bars. -/
def connecting (S : GroupExtension N E Q) (hS : (projectionSequence S).ShortExact) :
    (normalizedChains Q).homology 2 ⟶ (kernelChains S).homology 1 :=
  hS.δ 2 1 rfl

/-- The boundary of a lift of a normalized two-cycle, regarded as a kernel chain. -/
def liftBoundary (S : GroupExtension N E Q) (z : NormalizedModule Q 2)
    (hz : barBoundary Q 1 z = 0) (x : NormalizedModule E 2)
    (hx : (normalizedChainsMap S.rightHom).f 2 x = z) : KernelModule S 1 :=
  ⟨barBoundary E 1 x, by
    change (normalizedChainsMap S.rightHom).f 1 ((normalizedChains E).d 2 1 x) = 0
    have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      ((normalizedChainsMap S.rightHom).comm 2 1).symm) x
    change (normalizedChainsMap S.rightHom).f 1 ((normalizedChains E).d 2 1 x) =
      (normalizedChains Q).d 2 1 ((normalizedChainsMap S.rightHom).f 2 x) at h
    rw [h, hx]
    exact hz⟩

theorem liftBoundary_isCycle (S : GroupExtension N E Q)
    (hS : (projectionSequence S).ShortExact)
    (z : NormalizedModule Q 2) (hz : barBoundary Q 1 z = 0)
    (x : NormalizedModule E 2) (hx : (normalizedChainsMap S.rightHom).f 2 x = z) :
    (kernelChains S).d 1 0 (liftBoundary S z hz x hx) = 0 :=
  hS.d_eq_zero_of_f_eq_d_apply 2 1 x (liftBoundary S z hz x hx) rfl 0

/-- The integral transgression obtained by transport of the normalized connecting map. -/
def integralConnecting (S : GroupExtension N E Q) (hS : (projectionSequence S).ShortExact)
    (e : Multiplicative ((kernelChains S).homology 1) ≃* KernelQuotient S) :
    Multiplicative (homology Q 2) →* KernelQuotient S :=
  e.toMonoidHom.comp
    ((HomologicalComplex.homologyMap (normalization Q) 2 ≫ connecting S hS).hom.toAddMonoidHom.toMultiplicative)

/-- Conjugation by an element of the middle group on the first homology of the kernel. -/
abbrev conjugationOnH1 (S : GroupExtension N E Q) (a : E) :
    Multiplicative (homology N 1) →* Multiplicative (homology N 1) :=
  (homologyMap (S.conjAct a).toMonoidHom 1).hom.toAddMonoidHom.toMultiplicative

namespace Spec

def IntegralTransgressionType :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
    (projectionSequence S).ShortExact →
    (Multiplicative ((kernelChains S).homology 1) ≃* KernelQuotient S) →
    (Multiplicative (homology Q 2) →* KernelQuotient S)

def integralTransgressionValue : IntegralTransgressionType.{u} :=
  fun S hS e => integralConnecting S hS e

/-- The bar filtration is increasing, exhaustive in each degree, and preserved by
the boundary and by the chain maps induced by morphisms of extensions. -/
def FilteredBar : Prop :=
  (∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
    (∀ n, Monotone (fun p => barFiltration S p n)) ∧
    (∀ n, barFiltration S n n = ⊤) ∧
    (∀ p n, (barFiltration S p (n + 1)).map (barBoundary E n) ≤ barFiltration S p n)) ∧
  (∀ {N E Q N' E' Q' : Type u} [Group N] [Group E] [Group Q]
    [Group N'] [Group E'] [Group Q'] {S : GroupExtension N E Q}
    {T : GroupExtension N' E' Q'} (f : ExtensionHom S T) (p n : ℕ),
    (barFiltration S p n).map ((normalizedChainsMap f.middle).f n).hom ≤ barFiltration T p n)

/-- The sign is the actual boundary of any lifted chain. -/
def ConnectingOnLift : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
    (hS : (projectionSequence S).ShortExact)
    (z : NormalizedModule Q 2) (hz : barBoundary Q 1 z = 0)
    (x : NormalizedModule E 2) (_hx : (normalizedChainsMap S.rightHom).f 2 x = z)
    (y : KernelModule S 1) (_hy : y.val = barBoundary E 1 x)
    (cy : (kernelChains S).d 1 0 y = 0),
    connecting S hS (classOf (normalizedChains Q) z hz) = classOf (kernelChains S) y cy

/-- The signed boundary formula on integral homology. It applies to every normalized
cycle representing the input class and to every chain lift of that cycle. -/
def IntegralLiftFormula : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
    (hS : (projectionSequence S).ShortExact)
    (e : Multiplicative ((kernelChains S).homology 1) ≃* KernelQuotient S)
    (a : homology Q 2) (z : NormalizedModule Q 2) (hz : barBoundary Q 1 z = 0)
    (_ha : HomologicalComplex.homologyMap (normalization Q) 2 a =
      classOf (normalizedChains Q) z hz)
    (x : NormalizedModule E 2) (hx : (normalizedChainsMap S.rightHom).f 2 x = z),
    integralConnecting S hS e (Multiplicative.ofAdd a) =
      e (Multiplicative.ofAdd (classOf (kernelChains S) (liftBoundary S z hz x hx)
        (liftBoundary_isCycle S hS z hz x hx)))

/-- Lifting two homologous cycles, with any choice of lift, gives the same kernel class. -/
def LiftIndependence : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
    (hS : (projectionSequence S).ShortExact)
    (z z' : NormalizedModule Q 2) (hz : barBoundary Q 1 z = 0) (hz' : barBoundary Q 1 z' = 0)
    (_h : classOf (normalizedChains Q) z hz = classOf (normalizedChains Q) z' hz')
    (x x' : NormalizedModule E 2)
    (hx : (normalizedChainsMap S.rightHom).f 2 x = z)
    (hx' : (normalizedChainsMap S.rightHom).f 2 x' = z'),
    classOf (kernelChains S) (liftBoundary S z hz x hx) (liftBoundary_isCycle S hS z hz x hx) =
      classOf (kernelChains S) (liftBoundary S z' hz' x' hx')
        (liftBoundary_isCycle S hS z' hz' x' hx')

/-- The low-degree filtered differential and its projection and inclusion comparisons.
The displayed quotient definitions give the second-page groups in these bidegrees. -/
def FilteredComparison : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
    (hS : (projectionSequence S).ShortExact),
    ∃ (s : PageTwoSource S ≃ₗ[Integers.{u}] (normalizedChains Q).homology 2)
      (t : PageTwoTarget S ≃ₗ[Integers.{u}] (kernelChains S).homology 1),
      (∀ (x : sourceCycles S)
        (hx : barBoundary Q 1 ((normalizedChainsMap S.rightHom).f 2 x.val) = 0),
        s ((sourceRelations S).mkQ x) =
          classOf (normalizedChains Q) ((normalizedChainsMap S.rightHom).f 2 x.val) hx) ∧
      (∀ (x : barFiltration S 0 1) (y : KernelModule S 1) (_hy : y.val = x.val)
        (cy : (kernelChains S).d 1 0 y = 0),
        t ((targetRelations S).mkQ x) = classOf (kernelChains S) y cy) ∧
      (∀ x : PageTwoSource S, t (pageTwoDifferential S x) = connecting S hS (s x))

/-- The two bidegrees of the normalized filtered complex identify directly with
integral second homology of the quotient and the kernel coinvariants. -/
def IntegralFilteredComparison : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
    (hS : (projectionSequence S).ShortExact)
    (e : Multiplicative ((kernelChains S).homology 1) ≃* KernelQuotient S),
    ∃ (s : PageTwoSource S ≃ₗ[Integers.{u}] homology Q 2)
      (t : Multiplicative (PageTwoTarget S) ≃* KernelQuotient S),
      (∀ (x : sourceCycles S)
        (hx : barBoundary Q 1 ((normalizedChainsMap S.rightHom).f 2 x.val) = 0),
        HomologicalComplex.homologyMap (normalization Q) 2 (s ((sourceRelations S).mkQ x)) =
          classOf (normalizedChains Q) ((normalizedChainsMap S.rightHom).f 2 x.val) hx) ∧
      (∀ (x : barFiltration S 0 1) (y : KernelModule S 1) (_hy : y.val = x.val)
        (cy : (kernelChains S).d 1 0 y = 0),
        t (Multiplicative.ofAdd ((targetRelations S).mkQ x)) =
          e (Multiplicative.ofAdd (classOf (kernelChains S) y cy))) ∧
      (∀ x : PageTwoSource S, t (Multiplicative.ofAdd (pageTwoDifferential S x)) =
        integralConnecting S hS e (Multiplicative.ofAdd (s x)))

/-- The chosen family of kernel identifications is characterized on the bar classes
of the kernel elements. With it the transported connecting map is natural. -/
def IntegralNaturality : Prop :=
  ∃ e : ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
        Multiplicative ((kernelChains S).homology 1) ≃* KernelQuotient S,
    (∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
      (n : N) (y : KernelModule S 1) (_hy : y.val = normalizedBar 1 ![S.inl n])
      (cy : (kernelChains S).d 1 0 y = 0),
      e S (Multiplicative.ofAdd (classOf (kernelChains S) y cy)) = QuotientGroup.mk n) ∧
    (∀ {N E Q N' E' Q' : Type u} [Group N] [Group E] [Group Q]
      [Group N'] [Group E'] [Group Q'] {S : GroupExtension N E Q}
      {T : GroupExtension N' E' Q'} (f : ExtensionHom S T)
      (hS : (projectionSequence S).ShortExact) (hT : (projectionSequence T).ShortExact)
      (x : homology Q 2),
      integralConnecting T hT (e T) (Multiplicative.ofAdd (homologyMap f.quotient 2 x)) =
        quotientMap f (integralConnecting S hS (e S) (Multiplicative.ofAdd x)))

/-- The conjugation action on first homology depends only on the quotient element. -/
def ConjugationFactors : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
    (a b : E), S.rightHom a = S.rightHom b → conjugationOnH1 S a = conjugationOnH1 S b

/-- The kernel quotient realizes the conjugation coinvariants of integral first homology. -/
def ConjugationCoinvariants : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
    ∃ c : Multiplicative (homology N 1) →* KernelQuotient S,
      (∀ n : N, c (Multiplicative.ofAdd (generatorClass n)) = QuotientGroup.mk n) ∧
      (∀ a : E, c.comp (conjugationOnH1 S a) = c) ∧
      (∀ {A : Type u} [CommGroup A] (f : Multiplicative (homology N 1) →* A),
        (∀ a : E, f.comp (conjugationOnH1 S a) = f) →
        ∃! g : KernelQuotient S →* A, g.comp c = f)

end Spec
end
end ALG02GroupTheory.Transgression
