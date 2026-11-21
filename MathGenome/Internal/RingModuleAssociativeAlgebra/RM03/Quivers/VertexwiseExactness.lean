import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.Representations
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.VertexwiseExactness

/-! Vertexwise kernels, cokernels, images and exactness of representations. -/

open CategoryTheory CategoryTheory.Limits

namespace RM03.QuiverRepresentation

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]

variable {F G H : QuiverRepresentation.{u, v, w, d} k Q}

/-- The representation on the kernels of the vertex maps. -/
abbrev kernelRepresentation (f : F ⟶ G) : QuiverRepresentation.{u, v, w, d} k Q :=
  QuiverVertexwiseExactnessSpec.kernelRepresentation f

/-- The inclusion from the vertex kernels. -/
abbrev kernelInclusion (f : F ⟶ G) : kernelRepresentation f ⟶ F :=
  QuiverVertexwiseExactnessSpec.kernelInclusion f

/-- The representation on the vertex quotients by the images of the vertex maps. -/
abbrev cokernelRepresentation (f : F ⟶ G) : QuiverRepresentation.{u, v, w, d} k Q :=
  QuiverVertexwiseExactnessSpec.cokernelRepresentation f

/-- The projection to the vertex quotients. -/
abbrev cokernelProjection (f : F ⟶ G) : G ⟶ cokernelRepresentation f :=
  QuiverVertexwiseExactnessSpec.cokernelProjection f

/-- The representation on the images of the vertex maps. -/
abbrev imageRepresentation (f : F ⟶ G) : QuiverRepresentation.{u, v, w, d} k Q :=
  QuiverVertexwiseExactnessSpec.imageRepresentation f

/-- The inclusion from the vertex images. -/
abbrev imageInclusion (f : F ⟶ G) : imageRepresentation f ⟶ G :=
  QuiverVertexwiseExactnessSpec.imageInclusion f

/-- The vertex maps with codomain restricted to their images. -/
abbrev toImage (f : F ⟶ G) : F ⟶ imageRepresentation f :=
  QuiverVertexwiseExactnessSpec.toImage f

abbrev kernelFork (f : F ⟶ G) : KernelFork f :=
  QuiverVertexwiseExactnessSpec.kernelFork f

abbrev cokernelCofork (f : F ⟶ G) : CokernelCofork f :=
  QuiverVertexwiseExactnessSpec.cokernelCofork f

abbrev imageFactorisation (f : F ⟶ G) : MonoFactorisation f :=
  QuiverVertexwiseExactnessSpec.imageFactorisation f

/-- The concrete vertex kernels give a limit kernel fork. -/
noncomputable def kernelIsLimit (f : F ⟶ G) : IsLimit (kernelFork f) :=
  evaluationJointlyReflectsLimits _ fun i =>
    ((kernelFork f).isLimitMapConeEquiv ((evaluation (Paths Q) (ModuleCat.{d} k)).obj i)).symm
      (ModuleCat.kernelIsLimit (f.app i))

/-- The concrete vertex cokernels give a colimit cokernel cofork. -/
noncomputable def cokernelIsColimit (f : F ⟶ G) : IsColimit (cokernelCofork f) :=
  evaluationJointlyReflectsColimits _ fun i =>
    ((cokernelCofork f).isColimitMapCoconeEquiv
        ((evaluation (Paths Q) (ModuleCat.{d} k)).obj i)).symm
      (ModuleCat.cokernelIsColimit (f.app i))

/-- The vertexwise image factorization has the universal property of the image. -/
noncomputable def imageIsImage (f : F ⟶ G) : IsImage (imageFactorisation f) := by
  letI (i : Paths Q) : Epi ((toImage f).app i) := (ModuleCat.epi_iff_surjective _).2 (by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩)
  letI : Epi (toImage f) := NatTrans.epi_of_epi_app _
  exact StrongEpiMonoFactorisation.toMonoIsImage
    { toMonoFactorisation := imageFactorisation f
      e_strong_epi := strongEpi_of_epi (toImage f) }

theorem kernel_isLimit (f : F ⟶ G) : Nonempty (IsLimit (kernelFork f)) :=
  ⟨kernelIsLimit f⟩

theorem cokernel_isColimit (f : F ⟶ G) : Nonempty (IsColimit (cokernelCofork f)) :=
  ⟨cokernelIsColimit f⟩

theorem image_isImage (f : F ⟶ G) : Nonempty (IsImage (imageFactorisation f)) :=
  ⟨imageIsImage f⟩

/-- Exactness at the middle representation is equivalent to equality of range and kernel
at every vertex. -/
theorem exact_iff_vertexwise (S : ShortComplex (QuiverRepresentation.{u, v, w, d} k Q)) :
    S.Exact ↔ ∀ i : Q, (S.f.app i).hom.range = (S.g.app i).hom.ker := by
  rw [S.exact_iff_of_forks (kernelIsLimit S.g) (cokernelIsColimit S.f)]
  change kernelInclusion S.g ≫ cokernelProjection S.f = 0 ↔ _
  have component_iff (i : Q) :
      ((S.f.app i).hom.range.mkQ).comp (S.g.app i).hom.ker.subtype = 0 ↔
        (S.g.app i).hom.ker ≤ (S.f.app i).hom.range := by
    rw [← LinearMap.range_le_ker_iff, Submodule.range_subtype, Submodule.ker_mkQ]
  have range_le (i : Q) : (S.f.app i).hom.range ≤ (S.g.app i).hom.ker :=
    LinearMap.range_le_ker_iff.mpr
      (congrArg ModuleCat.Hom.hom (NatTrans.congr_app S.zero i))
  constructor
  · intro h i
    exact le_antisymm (range_le i) ((component_iff i).mp
      (congrArg ModuleCat.Hom.hom (NatTrans.congr_app h i)))
  · intro h
    apply hom_ext
    intro i
    exact (component_iff i).mpr (h i).ge

/-- For an arbitrary pair, the vertex equalities also imply that the composite vanishes. -/
theorem exact_pair_iff_vertexwise (f : F ⟶ G) (g : G ⟶ H) :
    (∃ h : f ≫ g = 0, (ShortComplex.mk f g h).Exact) ↔
      ∀ i : Q, (f.app i).hom.range = (g.app i).hom.ker := by
  constructor
  · rintro ⟨h, hex⟩
    exact (exact_iff_vertexwise (ShortComplex.mk f g h)).mp hex
  · intro h
    have hz : f ≫ g = 0 := hom_ext fun i =>
      LinearMap.range_le_ker_iff.mp (h i).le
    exact ⟨hz, (exact_iff_vertexwise (ShortComplex.mk f g hz)).mpr h⟩

end RM03.QuiverRepresentation
