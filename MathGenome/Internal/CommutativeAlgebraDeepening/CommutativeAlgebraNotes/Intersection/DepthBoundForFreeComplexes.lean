import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.DepthBoundForFreeComplexes
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Order.SuccPred.ENat

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CommutativeAlgebraNotes.Intersection

universe u

private theorem ringKrullDim_eq_depth {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (h : AdvCommAlg.CohenMacaulay.LocalCohenMacaulay R R) :
    ringKrullDim R = (AdvCommAlg.Depth.depth R R : WithBot ℕ∞) := by
  rw [AdvCommAlg.Depth.depth_eq_libraryDepth (ModuleCat.of R R)]
  exact ((AdvCommAlg.CohenMacaulay.localCohenMacaulay_self_iff R).mp h).symm

variable {R : Type u} [CommRing R] [IsLocalRing R]

private noncomputable abbrev residueModule (R : Type u) [CommRing R] [IsLocalRing R] :
    ModuleCat.{u} R :=
  ModuleCat.of R (Shrink.{u} (R ⧸ IsLocalRing.maximalIdeal R))

/-- Depth bounds pass to any finite direct sum of copies of a module. -/
private theorem depth_le_biproduct {n : ℕ} (U : ModuleCat.{u} R) (b : ℕ∞)
    (hb : b ≤ IsLocalRing.depth U) :
    b ≤ IsLocalRing.depth (⨁ fun _ : Fin n => U) := by
  change b ≤ (residueModule R).depth (⨁ fun _ : Fin n => U)
  apply le_sSup
  intro q hq
  let G := extFunctorObj (residueModule R) q
  apply AddCommGrpCat.isZero_of_iff_subsingleton.mp
  change IsZero (G.obj (⨁ fun _ : Fin n => U))
  apply IsZero.of_iso _ (G.mapBiproduct (fun _ : Fin n => U))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro i
  have hz : IsZero (G.obj U) := AddCommGrpCat.isZero_of_iff_subsingleton.mpr
    (ModuleCat.subsingleton_ext_of_lt_depth (hq.trans_le hb))
  exact hz.eq_of_tgt _ _

private theorem depth_le_tensor_free (X U : ModuleCat.{u} R)
    [Module.Free R X] [Module.Finite R X] (b : ℕ∞) (hb : b ≤ IsLocalRing.depth U) :
    b ≤ IsLocalRing.depth ((tensorRight U).obj X) := by
  let d := Module.finrank R X
  let copies : Fin d → ModuleCat.{u} R := fun _ => U
  let e := (TensorProduct.equivFinsuppOfBasisLeft (N := U) (Module.finBasis R X)).trans
    (Finsupp.linearEquivFunOnFinite R U (Fin d))
  let E : (tensorRight U).obj X ≅ ⨁ copies :=
    e.toModuleIso ≪≫ ((biproduct.isoProduct copies) ≪≫ ModuleCat.piIsoPi copies).symm
  rw [IsLocalRing.depth_eq_of_iso E]
  exact depth_le_biproduct U b hb

/-- A positive-depth target admits no nonzero finite-length submodule. -/
private theorem isZero_of_finiteLength_mono {M N : ModuleCat.{u} R} (f : M ⟶ N)
    [Mono f] (hM : IsFiniteLength R M) (hN : 0 < IsLocalRing.depth N) :
    IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton]
  by_contra! hn
  let : Nontrivial M := hn
  let : IsArtinian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  obtain ⟨S, hS, _⟩ := exists_covBy_le_of_lt (bot_lt_top : (⊥ : Submodule R M) < ⊤)
  have hSimple : IsSimpleModule R S := isSimpleModule_iff_isAtom.mpr hS.isAtom
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hSimple
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  let g : residueModule R →ₗ[R] N :=
    f.hom.comp (S.subtype.comp (e.symm.toLinearMap.comp
      (Shrink.linearEquiv R (R ⧸ IsLocalRing.maximalIdeal R)).toLinearMap))
  have hinj : Function.Injective g :=
    ((ModuleCat.mono_iff_injective f).mp inferInstance).comp
      (Subtype.val_injective.comp (e.symm.injective.comp
        (Shrink.linearEquiv R (R ⧸ IsLocalRing.maximalIdeal R)).injective))
  have hnonzero : g ≠ 0 := by
    intro hg
    have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R) := inferInstance
    have : Nontrivial (residueModule R) :=
      (Shrink.linearEquiv R (R ⧸ IsLocalRing.maximalIdeal R)).symm.injective.nontrivial
    obtain ⟨x, hx⟩ := exists_ne (0 : residueModule R)
    exact hx (hinj (by simp [hg]))
  exact hN.ne' ((ModuleCat.depth_eq_zero_iff_nontrivial_linearMap (residueModule R) N).2
    (nontrivial_of_ne g 0 hnonzero))

section Cokernels

variable {ι : Type*} {c : ComplexShape ι}
variable (K : HomologicalComplex (ModuleCat.{u} R) c) {i j : ι}

omit [IsLocalRing R] in
/-- Vanishing homology identifies the cokernel at the preceding degree with
the image of the incoming differential. -/
private theorem opcycles_shortExact (hp : c.prev i = j) (hn : c.next j = i)
    (hz : IsZero (K.homology j)) :
    (ShortComplex.mk (K.fromOpcycles j i) (K.pOpcycles i)
      (by rw [← cancel_epi (K.pOpcycles j), K.p_fromOpcycles_assoc,
        K.d_pOpcycles, comp_zero])).ShortExact := by
  let S := ShortComplex.mk (K.fromOpcycles j i) (K.pOpcycles i)
    (by rw [← cancel_epi (K.pOpcycles j), K.p_fromOpcycles_assoc,
      K.d_pOpcycles, comp_zero])
  let T := ShortComplex.mk (K.d j i) (K.pOpcycles i) (K.d_pOpcycles j i)
  let φ : T ⟶ S :=
    { τ₁ := K.pOpcycles j
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by change K.pOpcycles j ≫ K.fromOpcycles j i = K.d j i ≫ 𝟙 _; simp
      comm₂₃ := by change K.pOpcycles i ≫ 𝟙 _ = 𝟙 _ ≫ K.pOpcycles i; simp }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (K.pOpcycles j))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (K.X i)))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (K.opcycles i)))
  have hT : T.Exact := T.exact_of_g_is_cokernel (K.opcyclesIsCokernel j i hp)
  have hmono : Mono (K.fromOpcycles j i) :=
    Preadditive.mono_of_isZero_kernel' _ (K.homologyIsKernel j i hn) hz
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hT) hmono inferInstance

/-- A descending induction on the cokernels keeps their depth above the
current degree. The finite-length homology embeds in these cokernels. -/
private theorem isZero_homology_of_depth_bound (idx : ℕ → ι) (s : ℕ)
    (hp : ∀ n, c.prev (idx n) = idx (n + 1))
    (hn : ∀ n, c.next (idx (n + 1)) = idx n)
    (htop : IsZero (K.X (idx (s + 1))))
    (hdepth : ∀ n ≤ s, (s : ℕ∞) + 1 ≤ IsLocalRing.depth (K.X (idx n)))
    (hfinite : ∀ n ≤ s, IsFiniteLength R (K.homology (idx n))) (n : ℕ) (hns : n ≤ s) :
    IsZero (K.homology (idx n)) := by
  have vanish (i : ℕ) (hi : i ≤ s)
      (hd : (i : ℕ∞) + 1 ≤ IsLocalRing.depth (K.opcycles (idx i))) :
      IsZero (K.homology (idx i)) :=
    isZero_of_finiteLength_mono (K.homologyι (idx i)) (hfinite i hi)
      ((by simp : (0 : ℕ∞) < (i : ℕ∞) + 1).trans_le hd)
  apply vanish n hns
  refine Nat.decreasingInduction (motive := fun i _ =>
    (i : ℕ∞) + 1 ≤ IsLocalRing.depth (K.opcycles (idx i))) ?_ ?_ hns
  · intro i hi hd
    have hi' : i ≤ s := Nat.le_of_succ_le hi
    have hz := vanish (i + 1) hi hd
    have hS := opcycles_shortExact K (hp i) (hn i) hz
    have hstep := ModuleCat.depth_min_snd_fst_sub_one_le_trd_right (residueModule R) _ hS
    change min (IsLocalRing.depth (K.X (idx i)))
      (IsLocalRing.depth (K.opcycles (idx (i + 1))) - 1) ≤
      IsLocalRing.depth (K.opcycles (idx i)) at hstep
    refine (le_min ?_ ?_).trans hstep
    · have hs' : (i : ℕ∞) + 1 ≤ (s : ℕ∞) + 1 := by
        exact_mod_cast Nat.succ_le_succ hi'
      exact hs'.trans (hdepth i hi')
    · exact ENat.le_sub_of_add_le_right (by simp) (by simpa [Nat.cast_add] using hd)
  · have e := K.pOpcyclesIso (idx (s + 1)) (idx s) (hp s)
      (htop.eq_zero_of_src (K.d (idx (s + 1)) (idx s)))
    rw [← IsLocalRing.depth_eq_of_iso e]
    exact hdepth s le_rfl

end Cokernels

open Specs.CommutativeAlgebraNotes.Intersection.DepthBoundForFreeComplexes

/-- The length of a finite free complex with nonzero finite-length homology
after tensoring bounds the depth of the coefficient module. -/
theorem depth_le_length_of_finite_free_complex : depthBoundType.{u} := by
  intro R _ _ _ F s U _ _ hfree hfin hs K hlength hhom
  rw [AdvCommAlg.Depth.depth_eq_libraryDepth U]
  by_contra! hdepth
  have hb : (s : ℕ∞) + 1 ≤ IsLocalRing.depth U := by
    simpa only [Order.succ_eq_add_one] using Order.succ_le_of_lt hdepth
  have hout (i : ℕ) (hi : s < i) : IsZero (K.X i) :=
    (tensorRight U).map_isZero (hs i hi)
  obtain ⟨i, hnonzero⟩ := hhom
  let : Nontrivial (K.homology i) := hnonzero
  apply not_subsingleton (K.homology i)
  apply ModuleCat.subsingleton_of_isZero
  by_cases hi : i ≤ s
  · have hrel (n : ℕ) : (ComplexShape.down ℕ).Rel (n + 1) n := rfl
    refine isZero_homology_of_depth_bound K id s
      (fun n => (ComplexShape.down ℕ).prev_eq' (hrel n))
      (fun n => (ComplexShape.down ℕ).next_eq' (hrel n))
      (hout (s + 1) (Nat.lt_succ_self s)) ?_ (fun n _ => hlength n) i hi
    intro n _
    let : Module.Free R (F.X n) := hfree n
    let : Module.Finite R (F.X n) := hfin n
    exact depth_le_tensor_free (F.X n) U _ hb
  · exact (K.sc i).isZero_homology_of_isZero_X₂ (hout i (lt_of_not_ge hi))

/-- Over a Cohen–Macaulay local ring the same bound is its Krull dimension,
for a complex supported in any integer interval of the given length. -/
theorem ringKrullDim_le_length_of_finite_free_complex : dimensionBoundType.{u} := by
  intro R _ _ _ F a s hCM hfree hfin hs hlength hhom
  rw [ringKrullDim_eq_depth hCM, WithBot.coe_le_coe,
    AdvCommAlg.Depth.depth_eq_libraryDepth (ModuleCat.of R R)]
  by_contra! hdepth
  have hb : (s : ℕ∞) + 1 ≤ IsLocalRing.depth (ModuleCat.of R R) := by
    simpa only [Order.succ_eq_add_one] using Order.succ_le_of_lt hdepth
  obtain ⟨i, hnonzero⟩ := hhom
  let : Nontrivial (F.homology i) := hnonzero
  apply not_subsingleton (F.homology i)
  apply ModuleCat.subsingleton_of_isZero
  by_cases hi : i < a ∨ a + (s : ℤ) < i
  · exact (F.sc i).isZero_homology_of_isZero_X₂ (hs i hi)
  · let idx : ℕ → ℤ := fun n => a + (n : ℤ)
    have hrel (n : ℕ) : (ComplexShape.down ℤ).Rel (idx (n + 1)) (idx n) := by
      change a + (n : ℤ) + 1 = a + ((n + 1 : ℕ) : ℤ)
      omega
    let n := (i - a).toNat
    have hidx : idx n = i := by dsimp [idx, n]; omega
    have hn : n ≤ s := by dsimp [n]; omega
    rw [← hidx]
    refine isZero_homology_of_depth_bound F idx s
      (fun j => (ComplexShape.down ℤ).prev_eq' (hrel j))
      (fun j => (ComplexShape.down ℤ).next_eq' (hrel j))
      (hs _ (Or.inr (by dsimp [idx]; omega))) ?_ (fun j _ => hlength (idx j)) n hn
    intro j _
    let : Module.Free R (F.X (idx j)) := hfree (idx j)
    let : Module.Finite R (F.X (idx j)) := hfin (idx j)
    have e : (tensorRight (ModuleCat.of R R)).obj (F.X (idx j)) ≅ F.X (idx j) :=
      ρ_ (F.X (idx j))
    rw [← IsLocalRing.depth_eq_of_iso e]
    exact depth_le_tensor_free (F.X (idx j)) (ModuleCat.of R R) _ hb

end CommutativeAlgebraNotes.Intersection
