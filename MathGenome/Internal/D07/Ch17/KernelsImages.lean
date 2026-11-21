import MathGenome.Internal.D07.Ch17.IntertwinersEquivalence
import MathGenome.Internal.D07.Ch17.SubrepresentationsQuotients
import MathGenome.Internal.Specs.D07.Ch17.KernelsImages

/-!
K07.17.kernels_images: kernel and image invariance, and the equivariant
linear first isomorphism theorem. No finiteness assumptions are used.
-/
namespace D07.Ch17.KernelsImages

universe u v w x

theorem kernel_invariant :
    Specs.D07.Ch17.KernelsImages.KernelInvariant.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ T hT g v hv
  change T (ρ g v) = 0
  rw [hT.isIntertwining, LinearMap.mem_ker.mp hv, map_zero]

theorem image_invariant :
    Specs.D07.Ch17.KernelsImages.ImageInvariant.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ T hT g w hw
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
  exact LinearMap.mem_range.mpr ⟨ρ g v, hT.isIntertwining g v⟩

/-- Equivariance of the canonical first isomorphism, for the quotient and
restriction actions obtained from any proofs of the two invariance facts. -/
theorem quotKerEquivRange_intertwining
    {K : Type u} {G : Type v} {V : Type w} {W : Type x}
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (T : V →ₗ[K] W)
    (hT : ρ.IsIntertwiningMap σ T)
    (hker : SubrepresentationsQuotients.IsInvariant K G V ρ (LinearMap.ker T))
    (himage : SubrepresentationsQuotients.IsInvariant K G W σ (LinearMap.range T)) :
    (SubrepresentationsQuotients.quotient K G V ρ (LinearMap.ker T) hker).IsIntertwiningMap
      (SubrepresentationsQuotients.restriction K G W σ (LinearMap.range T) himage)
      T.quotKerEquivRange.toLinearMap := by
  constructor
  intro g q
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    apply Subtype.ext
    change T (ρ g v) = σ g (T v)
    exact hT.isIntertwining g v

theorem first_isomorphism_equivariant :
    Specs.D07.Ch17.KernelsImages.FirstIsomorphismEquivariant.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ T hT
  let hker := kernel_invariant K G V W ρ σ T hT
  let himage := image_invariant K G V W ρ σ T hT
  have h := quotKerEquivRange_intertwining ρ σ T hT hker himage
  refine ⟨hker, himage, Representation.Equiv.mk T.quotKerEquivRange
    (fun g => LinearMap.ext (h.isIntertwining g)), rfl, ?_⟩
  intro v
  exact T.quotKerEquivRange_apply_mk v

end D07.Ch17.KernelsImages
