import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FiniteFaceDevissage
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.FieldTheory.Finiteness
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.LocallyConstant.Basic

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology Filter
open TopCat.Presheaf
open scoped ZeroObject

set_option backward.isDefEq.respectTransparency false

namespace RepTheorySurvey.Geometric.FiniteFaceDevissage

open Analytic

private abbrev constantFunctor (X : TopCat.{u}) : Coeff.{u} ⥤ Sheaves X :=
  constantSheaf (Opens.grothendieckTopology X) _

private abbrev constantPresheaf (X : TopCat.{u}) (V : Coeff.{u}) : X.Presheaf Coeff.{u} :=
  (Functor.const _).obj V

private abbrev constantSection (X : TopCat.{u}) (V : Coeff.{u}) (U : Opens X) :
    V ⟶ (constant X V).obj.obj (op U) :=
  (toSheafify (Opens.grothendieckTopology X) (constantPresheaf X V)).app (op U)

private def constantStalkIso (X : TopCat.{u}) (V : Coeff.{u}) (x : X) :
    (Analytic.stalk x).obj (constant X V) ≅ V := by
  let G := TopCat.Presheaf.stalkFunctor Coeff.{u} x
  let η := toSheafify (Opens.grothendieckTopology X) (constantPresheaf X V)
  have : IsIso (G.map η) := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ _
  let J := (OpenNhds x)ᵒᵖ
  exact (asIso (G.map η)).symm ≪≫
    (colimit.isColimit ((Functor.const J).obj V)).coconePointUniqueUpToIso
      (isColimitConstCocone J V)

private theorem constantSection_germ {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X)
    (x : X) (hx : x ∈ U) (v : V) :
    (constantStalkIso X V x).hom (germ (constant X V).obj U x hx (constantSection X V U v)) =
      v := by
  have h : constantSection X V U ≫ germ (constant X V).obj U x hx ≫
      (constantStalkIso X V x).hom = 𝟙 V := by
    let η := toSheafify (Opens.grothendieckTopology X) (constantPresheaf X V)
    change η.app (op U) ≫ germ (sheafify (Opens.grothendieckTopology X)
      (constantPresheaf X V)) U x hx ≫ _ = _
    erw [← stalkFunctor_map_germ_assoc U x hx η]
    rw [constantStalkIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
    exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
      (isColimitConstCocone (OpenNhds x)ᵒᵖ V) (op ⟨U, hx⟩)
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) v

/-- On a nonempty connected space the global sections of a constant sheaf are
its coefficients. -/
private theorem constantGlobalSection_bijective (X : TopCat.{u}) [ConnectedSpace X]
    (V : Coeff.{u}) : Function.Bijective (constantSection X V ⊤) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let U : Opens X := ⊤
  let F := constant X V
  have hx : x ∈ U := trivial
  refine ⟨fun v w h => ?_, fun s => ?_⟩
  · rw [← constantSection_germ V U x hx v, ← constantSection_germ V U x hx w, h]
  let value (y : X) : V := (constantStalkIso X V y).hom (germ F.obj U y trivial s)
  have locallyConstant : IsLocallyConstant value := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hy : y ∈ U := trivial
    obtain ⟨W, hyW, i₁, i₂, h⟩ := germ_eq F.obj y hy hy s
      (constantSection X V U (value y)) (by
        apply (ModuleCat.mono_iff_injective (constantStalkIso X V y).hom).mp inferInstance
        exact (constantSection_germ V U y hy (value y)).symm)
    filter_upwards [W.isOpen.mem_nhds hyW] with z hz
    have hz' : z ∈ U := trivial
    have he := germ_ext F.obj (hxU := hz') (hxV := hz') W hz i₁ i₂ h
    change (constantStalkIso X V z).hom (germ F.obj U z hz' s) = value y
    rw [he, constantSection_germ]
  refine ⟨value x, ?_⟩
  apply section_ext F U
  intro y hy
  apply (ModuleCat.mono_iff_injective (constantStalkIso X V y).hom).mp inferInstance
  rw [constantSection_germ]
  exact locallyConstant.apply_eq_of_preconnectedSpace x y

private def constantFullyFaithful (X : TopCat.{u}) [ConnectedSpace X] :
    (constantFunctor X).FullyFaithful := by
  let a := constantSheafAdj (Opens.grothendieckTopology X) Coeff.{u}
    (isTerminalTop (α := Opens X))
  haveI (V : Coeff.{u}) : IsIso (a.unit.app V) := by
    change IsIso (constantSection X V ⊤)
    exact (ConcreteCategory.isIso_iff_bijective _).2 (constantGlobalSection_bijective X V)
  haveI : IsIso a.unit := NatIso.isIso_of_isIso_app _
  exact a.fullyFaithfulLOfIsIsoUnit

private theorem constantPreservesFiniteLimits (X : TopCat.{u}) :
    PreservesFiniteLimits (constantFunctor X) := by
  let E := (Functor.const (Opens X)ᵒᵖ : Coeff.{u} ⥤ ((Opens X)ᵒᵖ ⥤ Coeff.{u}))
  let T := presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}
  have : PreservesLimits E := preservesLimits_const
  have : T.PreservesHomology := by dsimp only [T]; infer_instance
  have : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  exact comp_preservesFiniteLimits E T

private theorem constantPreservesFiniteColimits (X : TopCat.{u}) :
    PreservesFiniteColimits (constantFunctor X) := by
  let a := constantSheafAdj (Opens.grothendieckTopology X) Coeff.{u}
    (isTerminalTop (α := Opens X))
  have : (constantFunctor X).IsLeftAdjoint := ⟨_, ⟨a⟩⟩
  infer_instance

private def HasFiniteConstantCoefficients {X : TopCat.{u}} (F : Sheaves X) : Prop :=
  ∃ V : Coeff.{u}, Module.Finite ℚ V ∧ Nonempty (F ≅ constant X V)

private theorem HasFiniteConstantCoefficients.of_isZero {X : TopCat.{u}} {F : Sheaves X}
    (hF : IsZero F) : HasFiniteConstantCoefficients F := by
  let C := constantFunctor X
  have : PreservesFiniteLimits C := constantPreservesFiniteLimits X
  have : C.Additive := Functor.additive_of_preserves_binary_products C
  let V : Coeff.{u} := ModuleCat.of ℚ PUnit
  have : Module.Finite ℚ V := Module.Finite.of_finite
  exact ⟨V, inferInstance, ⟨hF.iso (C.map_isZero (ModuleCat.isZero_of_subsingleton V))⟩⟩

private theorem HasFiniteConstantCoefficients.of_iso {X : TopCat.{u}} {F G : Sheaves X}
    (hG : HasFiniteConstantCoefficients G) (p : F ≅ G) : HasFiniteConstantCoefficients F := by
  obtain ⟨V, hV, ⟨q⟩⟩ := hG
  exact ⟨V, hV, ⟨p ≪≫ q⟩⟩

/-- Kernels and cokernels between finite constant sheaves on a connected space
come from the corresponding linear maps on their coefficients. -/
private theorem finiteConstant_kernel_cokernel {X : TopCat.{u}} [ConnectedSpace X]
    {F G : Sheaves X} (f : F ⟶ G) (hF : HasFiniteConstantCoefficients F)
    (hG : HasFiniteConstantCoefficients G) :
    HasFiniteConstantCoefficients (kernel f) ∧ HasFiniteConstantCoefficients (cokernel f) := by
  obtain ⟨V, hV, ⟨p⟩⟩ := hF
  obtain ⟨W, hW, ⟨q⟩⟩ := hG
  let C := constantFunctor X
  have : PreservesFiniteLimits C := constantPreservesFiniteLimits X
  have : PreservesFiniteColimits C := constantPreservesFiniteColimits X
  have : C.Additive := Functor.additive_of_preserves_binary_products C
  let ff : C.FullyFaithful := constantFullyFaithful X
  let g : V ⟶ W := ff.preimage (p.inv ≫ f ≫ q.hom)
  have comm : f ≫ q.hom = p.hom ≫ C.map g := by
    dsimp only [g]
    rw [ff.map_preimage]
    simp
  have hK : Module.Finite ℚ ↥(kernel g) := Module.Finite.of_injective (kernel.ι g).hom
    ((ModuleCat.mono_iff_injective (kernel.ι g)).1 inferInstance)
  have hQ : Module.Finite ℚ ↥(cokernel g) := Module.Finite.of_surjective (cokernel.π g).hom
    ((ModuleCat.epi_iff_surjective (cokernel.π g)).1 inferInstance)
  exact ⟨⟨kernel g, hK, ⟨kernel.mapIso _ _ p q comm ≪≫ (PreservesKernel.iso C g).symm⟩⟩,
    ⟨cokernel g, hQ, ⟨cokernel.mapIso _ _ p q comm ≪≫ (PreservesCokernel.iso C g).symm⟩⟩⟩

set_option maxHeartbeats 800000 in
theorem finiteFaceGeneration : Expected.FiniteFaceGeneration.{u, v} := by
  classical
  intro I _ _ X Z _ e hInducing hCover hElementary P hZero hIso hShort hP
  let restriction (j : I) := inverseImage (e j)
  let : Fintype I := Fintype.ofFinite I
  -- The elementary target at a maximal index is supported within the same lower set.
  have generate : ∀ A : Finset I, (∀ ⦃j k⦄, j ∈ A → k ≤ j → k ∈ A) →
      ∀ F : Sheaves X,
        (∀ j, HasFiniteConstantCoefficients ((restriction j).obj F)) →
        (∀ j, j ∉ A → IsZero ((restriction j).obj F)) → P F := by
    intro A
    induction A using Finset.strongInductionOn with
    | _ A ih =>
      intro hLower F hF hSupport
      by_cases hA : A.Nonempty
      · obtain ⟨i, hi⟩ := A.exists_maximal hA
        obtain ⟨V, hV, ⟨p⟩⟩ := hF i
        let E := (directImage (e i)).obj (constant (Z i) V)
        let adj := inverseDirectAdjunction (e i)
        let f : F ⟶ E := adj.unit.app F ≫ (directImage (e i)).map p.hom
        have hE (j : I) : HasFiniteConstantCoefficients ((restriction j).obj E) := by
          by_cases hj : j ≤ i
          · exact (hElementary i j V hV).2 hj
          · exact HasFiniteConstantCoefficients.of_isZero ((hElementary i j V hV).1 hj)
        have hFinite (j : I) :
            HasFiniteConstantCoefficients ((restriction j).obj (kernel f)) ∧
            HasFiniteConstantCoefficients ((restriction j).obj (cokernel f)) := by
          let R := restriction j
          obtain ⟨hK, hQ⟩ := finiteConstant_kernel_cokernel (R.map f) (hF j) (hE j)
          exact ⟨hK.of_iso (PreservesKernel.iso R f), hQ.of_iso (PreservesCokernel.iso R f)⟩
        have hAtI : IsIso ((restriction i).map f) := by
          have : IsIso (adj.counit.app ((restriction i).obj F)) :=
            inducedCounit_isIso (hInducing i) ((restriction i).obj F)
          have : IsIso ((restriction i).map (adj.unit.app F) ≫
              adj.counit.app ((restriction i).obj F)) := by
            change IsIso ((inverseImage (e i)).map (adj.unit.app F) ≫
              adj.counit.app ((inverseImage (e i)).obj F))
            rw [adj.left_triangle_components F]
            exact IsIso.id _
          have : IsIso ((restriction i).map (adj.unit.app F)) :=
            IsIso.of_isIso_comp_right _ (adj.counit.app ((restriction i).obj F))
          dsimp only [f]
          rw [Functor.map_comp]
          infer_instance
        let B := A.erase i
        have hLowerB : ∀ ⦃j k⦄, j ∈ B → k ≤ j → k ∈ B := by
          intro j k hj hkj
          obtain ⟨hne, hjA⟩ := Finset.mem_erase.mp hj
          refine Finset.mem_erase.mpr ⟨?_, hLower hjA hkj⟩
          rintro rfl
          exact hne (le_antisymm (hi.2 hjA hkj) hkj)
        have hSupportB (j : I) (hj : j ∉ B) :
            IsZero ((restriction j).obj (kernel f)) ∧ IsZero ((restriction j).obj (cokernel f)) := by
          let R := restriction j
          have : IsIso (R.map f) := by
            by_cases hji : j = i
            · subst j
              exact hAtI
            · have hjA : j ∉ A := fun h => hj (Finset.mem_erase.mpr ⟨hji, h⟩)
              have hzE : IsZero (R.obj E) :=
                (hElementary i j V hV).1 (fun h => hjA (hLower hi.1 h))
              exact isIso_of_source_target_iso_zero _ (hSupport j hjA).isoZero hzE.isoZero
          exact ⟨(isZero_kernel_of_mono _).of_iso (PreservesKernel.iso R f),
            (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso R f)⟩
        have hBA : B ⊂ A := Finset.erase_ssubset hi.1
        have hK := ih B hBA hLowerB (kernel f) (fun j => (hFinite j).1)
          (fun j hj => (hSupportB j hj).1)
        have hQ := ih B hBA hLowerB (cokernel f) (fun j => (hFinite j).2)
          (fun j hj => (hSupportB j hj).2)
        let T := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) (kernel.condition _)
        have hT : T.ShortExact := ⟨ShortComplex.exact_kernel _⟩
        have hImage : P (Abelian.image f) := (hShort T hT).2.2 (hP i V hV) hQ
        let S := ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f) (cokernel.condition _)
        have hS : S.ShortExact := ⟨ShortComplex.exact_cokernel _⟩
        exact (hShort S hS).2.1 hK (hIso (Abelian.coimageIsoImage f).symm hImage)
      · have hFzero : IsZero F := by
          apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero F).2
          intro x
          obtain ⟨j, z, rfl⟩ := hCover x
          have hR := hSupport j (fun h => hA ⟨j, h⟩)
          exact ((Analytic.stalk z).map_isZero hR).of_iso (inverseImageStalkIso (e j) F z)
        exact hIso hFzero.isoZero.symm hZero
  intro F hF
  exact generate Finset.univ (by simp) F hF (by simp)

end RepTheorySurvey.Geometric.FiniteFaceDevissage
