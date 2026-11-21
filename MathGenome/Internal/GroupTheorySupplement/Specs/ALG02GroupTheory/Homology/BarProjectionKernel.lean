import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.IntegralBar
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

open CategoryTheory CategoryTheory.Limits Category

universe u

namespace ALG02GroupTheory.BarProjectionKernel

open IntegralBar

noncomputable section

variable {N E Q N' E' Q' : Type u}
variable [Group N] [Group E] [Group Q] [Group N'] [Group E'] [Group Q']

/-- The degreewise kernel of the bar projection. -/
abbrev KernelModule (S : GroupExtension N E Q) (n : ℕ) :=
  LinearMap.ker ((normalizedChainsMap S.rightHom).f n).hom

private def kernelDifferential (S : GroupExtension N E Q) (n : ℕ) :
    KernelModule S (n + 1) →ₗ[Integers.{u}] KernelModule S n :=
  (((normalizedChains E).d (n + 1) n).hom.comp (KernelModule S (n + 1)).subtype).codRestrict _
    (fun x => by
      change (normalizedChainsMap S.rightHom).f n ((normalizedChains E).d (n + 1) n x.val) = 0
      rw [← ModuleCat.comp_apply, ← (normalizedChainsMap S.rightHom).comm, ModuleCat.comp_apply]
      rw [show (normalizedChainsMap S.rightHom).f (n + 1) x.val = 0 from x.property, map_zero])

/-- The kernel complex of the normalized bar projection, realized by linear kernels. -/
def kernelChains (S : GroupExtension N E Q) : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of _ (KernelModule S n))
    (fun n => ModuleCat.ofHom (kernelDifferential S n)) (fun n => by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => Subtype.ext ?_
      change (normalizedChains E).d (n + 1) n
        ((normalizedChains E).d (n + 2) (n + 1) x.val) = 0
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
      rfl)

theorem kernelChains_d (S : GroupExtension N E Q) (n : ℕ) :
    (kernelChains S).d (n + 1) n = ModuleCat.ofHom (kernelDifferential S n) := by
  unfold kernelChains
  change ChainComplex.of.d (fun i => ModuleCat.of Integers.{u} (KernelModule S i))
    (fun i => ModuleCat.ofHom (kernelDifferential S i)) (n + 1) n = _
  exact ChainComplex.of_d _ _ n

/-- The inclusion of the kernel into the normalized bar chains of the middle group. -/
def kernelInclusion (S : GroupExtension N E Q) : kernelChains S ⟶ normalizedChains E :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (KernelModule S n).subtype) (fun n => by
    rw [kernelChains_d]
    rfl)

/-- The bar projection with its kernel inclusion. -/
def projectionSequence (S : GroupExtension N E Q) :
    ShortComplex (ChainComplex (ModuleCat.{u} Integers.{u}) ℕ) :=
  ShortComplex.mk (kernelInclusion S) (normalizedChainsMap S.rightHom) (by
    ext n : 1
    exact ModuleCat.hom_ext (LinearMap.ext fun x => x.property))

/-- A commuting map of extensions with all three group homomorphisms specified. -/
structure ExtensionHom (S : GroupExtension N E Q) (T : GroupExtension N' E' Q') where
  kernel : N →* N'
  middle : E →* E'
  quotient : Q →* Q'
  inl_comm : middle.comp S.inl = T.inl.comp kernel
  right_comm : T.rightHom.comp middle = quotient.comp S.rightHom

/-- Restriction of the middle bar map in a commuting square of bar projections. -/
def restrictKernelMap {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
    {f : E →* E'} {g : Q →* Q'}
    (h : normalizedChainsMap f ≫ normalizedChainsMap T.rightHom =
      normalizedChainsMap S.rightHom ≫ normalizedChainsMap g) :
    kernelChains S ⟶ kernelChains T :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((((normalizedChainsMap f).f n).hom.comp (KernelModule S n).subtype).codRestrict _
      (fun x => by
        have he := DFunLike.congr_fun
          (congrArg (fun k => (k.f n).hom) h) x.val
        change (normalizedChainsMap T.rightHom).f n ((normalizedChainsMap f).f n x.val) = 0
        have hx : (normalizedChainsMap S.rightHom).f n x.val = 0 := x.property
        change (normalizedChainsMap T.rightHom).f n ((normalizedChainsMap f).f n x.val) =
          (normalizedChainsMap g).f n ((normalizedChainsMap S.rightHom).f n x.val) at he
        rw [he, hx, map_zero]))) (fun n => by
      rw [kernelChains_d, kernelChains_d]
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => Subtype.ext ?_
      exact DFunLike.congr_fun
        (congrArg ModuleCat.Hom.hom ((normalizedChainsMap f).comm (n + 1) n)) x.val)

/-- The conjugation coinvariant quotient of the kernel, written multiplicatively. -/
abbrev KernelQuotient (S : GroupExtension N E Q) :=
  N ⧸ pulledBackCommutator S.inl

/-- The induced map on the conjugation coinvariant quotients. -/
def quotientMap {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
    (f : ExtensionHom S T) : KernelQuotient S →* KernelQuotient T :=
  QuotientGroup.map _ _ f.kernel (by
    intro n hn
    change T.inl (f.kernel n) ∈ ⁅(⊤ : Subgroup E'), T.inl.range⁆
    rw [← show f.middle (S.inl n) = T.inl (f.kernel n) from DFunLike.congr_fun f.inl_comm n]
    have hmap : S.inl.range.map f.middle ≤ T.inl.range := by
      rw [MonoidHom.map_range, f.inl_comm]
      rintro _ ⟨a, rfl⟩
      exact ⟨f.kernel a, rfl⟩
    apply Subgroup.commutator_mono le_top hmap
    rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ hn)

namespace Spec

def ProjectionSurjective : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
    (n : ℕ), Function.Surjective ((normalizedChainsMap S.rightHom).f n)

def KernelZero : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
    IsZero ((kernelChains S).X 0)

def ProjectionShortExact : Prop :=
  ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
    (projectionSequence S).ShortExact

/-- The three conditions specify the generator formula, the inclusion and the
commuting square for arbitrary maps of extensions. The normalization comparison
is used in the inclusion condition to land in the prescribed group homology. -/
def NaturalIdentification : Prop :=
  ∃ e : ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
      Multiplicative ((kernelChains S).homology 1) ≃* KernelQuotient S,
    (∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
        (n : N) (x : E),
      ∃ z : (kernelChains S).cycles 1,
        ((kernelChains S).iCycles 1 z).val =
          normalizedBar 1 ![S.inl n * x] - normalizedBar 1 ![x] ∧
        e S (Multiplicative.ofAdd ((kernelChains S).homologyπ 1 z)) = QuotientGroup.mk n) ∧
    (∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
        (n : N),
      HomologicalComplex.homologyMap (kernelInclusion S) 1
          ((e S).symm (QuotientGroup.mk n)).toAdd =
        HomologicalComplex.homologyMap (normalization E) 1
          (homologyMap S.inl 1 (generatorClass n))) ∧
    (∀ {N E Q N' E' Q' : Type u}
        [Group N] [Group E] [Group Q] [Group N'] [Group E'] [Group Q']
        {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
        (f : ExtensionHom S T)
        (h : normalizedChainsMap f.middle ≫ normalizedChainsMap T.rightHom =
          normalizedChainsMap S.rightHom ≫ normalizedChainsMap f.quotient)
        (x : (kernelChains S).homology 1),
      e T (Multiplicative.ofAdd
        (HomologicalComplex.homologyMap (restrictKernelMap h) 1 x)) =
        quotientMap f (e S (Multiplicative.ofAdd x)))

end Spec
end
end ALG02GroupTheory.BarProjectionKernel
