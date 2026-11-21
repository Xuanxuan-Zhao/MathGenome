import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertAnnihilatorQuotient
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertSerreLength
import MathGenome.Internal.AlgebraCore.P103.Ch06.LinearGradedNormalization
import Lean.Elab.Tactic.Omega

namespace P103.HilbertAnnihilatorQuotient
open P103.Graded P103.HilbertSerreLength
open P103.Specs.Ch06.LinearGradedNormalization
universe u v w

/-- Projection onto degree i+j of a scalar acting on a homogeneous vector. -/
theorem decompose_smul_homogeneous {A : Type v} {M : Type w}
    [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (i j : ℤ) (a : A) (m : U.piece j) :
    (DirectSum.decompose U.piece (a • (m : M)) (i + j) : M) =
      (DirectSum.decompose G.piece a i : A) • (m : M) := by
  classical
  induction a using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | add a b ha hb =>
    simp only [add_smul, DirectSum.decompose_add]
    change (DirectSum.decompose U.piece (a • (m : M)) (i + j) : M) +
        (DirectSum.decompose U.piece (b • (m : M)) (i + j) : M) =
      ((DirectSum.decompose G.piece a i : A) +
        (DirectSum.decompose G.piece b i : A)) • (m : M)
    rw [add_smul, ha, hb]
  | @homogeneous n a =>
    have hm : (a : A) • (m : M) ∈ U.piece (n + j) :=
      SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) a.2 m.2
    by_cases hn : n = i
    · subst n
      rw [DirectSum.decompose_of_mem_same U.piece hm,
        DirectSum.decompose_of_mem_same G.piece a.2]
    · rw [DirectSum.decompose_of_mem_ne U.piece hm (by omega),
        DirectSum.decompose_of_mem_ne G.piece a.2 hn, zero_smul]

theorem annihilator_homogeneous :
    Specs.P103.HilbertAnnihilatorQuotient.annihilatorHomogeneousType.{v,w} := by
  intro A M _ _ _ G U a ha i
  rw [Module.mem_annihilator] at ha ⊢
  intro m
  induction m using DirectSum.Decomposition.inductionOn U.piece with
  | zero => exact smul_zero _
  | add m n hm hn => rw [smul_add, hm, hn, add_zero]
  | @homogeneous j m =>
    have h := decompose_smul_homogeneous G U i j a m
    rw [ha m] at h
    simpa using h.symm


variable {A : Type v} {M : Type w} [CommRing A] [AddCommGroup M] [Module A M]

/-- The ring's grading, regarded as a grading of its regular module. -/
def regularGrading (G : NonnegativeGrading A) : ModuleGrading G A where
  piece := G.piece
  decomposition := inferInstance
  compatible := ⟨fun _ _ _ _ ha hb => SetLike.mul_mem_graded ha hb⟩

/-- Ring grading on the quotient, whose pieces are images of the original pieces. -/
noncomputable def quotientGrading (G : NonnegativeGrading A) (U : ModuleGrading G M) :
    NonnegativeGrading (A ⧸ Module.annihilator A M) := by
  let I := Module.annihilator A M
  let V := P103.HilbertSerreLength.quotientGrading G (regularGrading G) I
    (fun j a ha => annihilator_homogeneous G U a ha j)
  refine { piece := V.piece, grading := ?_, negative := ?_ }
  · exact
      { V.decomposition with
        one_mem := ⟨1, SetLike.one_mem_graded G.piece, map_one (Ideal.Quotient.mk I)⟩
        mul_mem := by
          intro i j x y hx hy
          obtain ⟨a, ha, rfl⟩ := hx
          obtain ⟨b, hb, rfl⟩ := hy
          exact ⟨a * b, SetLike.mul_mem_graded (A := G.piece) ha hb, map_mul (Ideal.Quotient.mk I) a b⟩ }
  · intro j hj
    change (G.piece j).map I.mkQ.toAddMonoidHom = ⊥
    rw [G.negative j hj, AddSubgroup.map_bot]

@[simp] theorem quotientGrading_piece (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (j : ℤ) : (quotientGrading G U).piece j = (G.piece j).map
      (Ideal.Quotient.mk (Module.annihilator A M)).toAddMonoidHom := rfl

/-- The module grading descends without changing any additive subgroup. -/
def descendedGrading (G : NonnegativeGrading A) (U : ModuleGrading G M) :
    letI := Module.quotientAnnihilator (R := A) (M := M)
    ModuleGrading (quotientGrading G U) M := by
  letI := Module.quotientAnnihilator (R := A) (M := M)
  refine { piece := U.piece, decomposition := U.decomposition, compatible := ?_ }
  constructor
  intro i j c m hc hm
  change c ∈ (G.piece i).map (Ideal.Quotient.mk (Module.annihilator A M)).toAddMonoidHom at hc
  obtain ⟨a, ha, rfl⟩ := hc
  change a • m ∈ U.piece (i + j)
  exact SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) ha hm


/-- The quotient representation is faithful, by its defining kernel. -/
theorem descended_faithful :
    letI := Module.quotientAnnihilator (R := A) (M := M)
    FaithfulSMul (A ⧸ Module.annihilator A M) M := by
  letI := Module.quotientAnnihilator (R := A) (M := M)
  constructor
  intro c d h
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective d
  apply Ideal.Quotient.eq.mpr
  rw [Module.mem_annihilator]
  intro m
  exact sub_smul a b m |>.trans (sub_eq_zero.mpr (h m))

/-- The same finite generators generate after descending the action. -/
theorem descended_finite [Module.Finite A M] :
    letI := Module.quotientAnnihilator (R := A) (M := M)
    Module.Finite (A ⧸ Module.annihilator A M) M := by
  letI := Module.quotientAnnihilator (R := A) (M := M)
  exact Module.Finite.of_surjective
    ((Module.isTorsionBySet_annihilator A M).semilinearMap) Function.surjective_id

/-- The degree-zero map is surjective even without connectedness. -/
def quotientBaseMap (G : NonnegativeGrading A) (U : ModuleGrading G M) :
    Base G →+* Base (quotientGrading G U) where
  toFun b := ⟨Ideal.Quotient.mk (Module.annihilator A M) b, ⟨b, b.2, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' b c := Subtype.ext (map_add (Ideal.Quotient.mk (Module.annihilator A M)) (b : A) (c : A))
  map_mul' b c := Subtype.ext (map_mul (Ideal.Quotient.mk (Module.annihilator A M)) (b : A) (c : A))

theorem quotientBaseMap_surjective (G : NonnegativeGrading A) (U : ModuleGrading G M) :
    Function.Surjective (quotientBaseMap G U) := by
  intro b
  obtain ⟨a, ha, he⟩ := b.2
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

theorem quotient_connected (k : Type u) [Field k] [Algebra k A]
    (G : NonnegativeGrading A) (U : ModuleGrading G M) (hzero : Connected k G) :
    Connected k (quotientGrading G U) := by
  intro c
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨r, rfl⟩ := (hzero a).mp ha
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨algebraMap k A r, (hzero _).mpr ⟨r, rfl⟩, rfl⟩

theorem quotient_standard (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (hstd : Specs.P103.Graded.standardValue G) :
    Specs.P103.Graded.standardValue (quotientGrading G U) := by
  classical
  let I := Module.annihilator A M
  let q := Ideal.Quotient.mk I
  let GC := quotientGrading G U
  obtain ⟨s, hs, hgen⟩ := hstd
  refine ⟨s.image q, ?_, ?_⟩
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨a, hs a ha, rfl⟩
  · apply top_unique
    intro c hc
    clear hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    have ha : a ∈ Algebra.adjoin (Base G) (s : Set A) := by rw [hgen]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact Algebra.subset_adjoin (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    | algebraMap b =>
      exact (Algebra.adjoin (Base GC) (s.image q : Set (A ⧸ I))).algebraMap_mem
        (quotientBaseMap G U b)
    | add a b _ _ ha hb => simpa only [map_add] using add_mem ha hb
    | mul a b _ _ ha hb => simpa only [map_mul] using mul_mem ha hb

/-- Changing from A₀ to its quotient does not change the length of a piece. -/
theorem quotient_hilbertFunction (G : NonnegativeGrading A) (U : ModuleGrading G M) :
    letI := Module.quotientAnnihilator (R := A) (M := M)
    hilbertFunction (quotientGrading G U) (descendedGrading G U) = hilbertFunction G U := by
  letI := Module.quotientAnnihilator (R := A) (M := M)
  let GC := quotientGrading G U
  let UC := descendedGrading G U
  letI : Algebra (Base G) (Base GC) := (quotientBaseMap G U).toAlgebra
  funext j
  letI : Module (Base GC) (component G U j) := (component GC UC j).module
  letI : IsScalarTower (Base G) (Base GC) (component G U j) :=
    IsScalarTower.of_algebraMap_smul (fun b m => by
      apply Subtype.ext
      rfl)
  have h := Module.length_eq_of_surjective (R := Base GC) (M := component G U j)
    (quotientBaseMap_surjective G U)
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) h.symm


/-- The structural field maps onto the actual degree-zero ring. -/
def baseScalarMap (k : Type u) [Field k] [Algebra k A]
    (G : NonnegativeGrading A) (hzero : Connected k G) : k →+* Base G where
  toFun a := ⟨algebraMap k A a, (hzero _).mpr ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem baseScalarMap_surjective (k : Type u) [Field k] [Algebra k A]
    (G : NonnegativeGrading A) (hzero : Connected k G) :
    Function.Surjective (baseScalarMap k G hzero) := by
  intro a
  obtain ⟨b, hb⟩ := (hzero a).mp a.2
  exact ⟨b, Subtype.ext hb⟩

/-- The length coefficients are the dimensions over the structural field. -/
theorem finite_components :
    Specs.P103.HilbertAnnihilatorQuotient.finiteComponentsType.{u,v,w} := by
  intro k A M _ _ _ _ _ _ _ _ G U hzero hstd j
  letI : Algebra k (Base G) := (baseScalarMap k G hzero).toAlgebra
  have hsurj : Function.Surjective (algebraMap k (Base G)) :=
    baseScalarMap_surjective k G hzero
  let : Module.Finite k (Base G) :=
    Module.Finite.of_surjective (Algebra.linearMap k (Base G)) hsurj
  let : IsScalarTower k (Base G) M :=
    IsScalarTower.of_algebraMap_smul fun a m => by
      change (algebraMap k A a) • m = a • m
      exact algebraMap_smul A a m
  let : Algebra.FiniteType k A :=
    P103.Ch06.LinearGradedNormalization.finiteType_of_standard G hzero hstd
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  letI : Module (Base G) (fieldComponent k G U hzero j) :=
    (component G U j).module
  let : IsScalarTower k (Base G) (fieldComponent k G U hzero j) :=
    ⟨fun a b m => Subtype.ext (smul_assoc a b (m : M))⟩
  let : Module.Finite (Base G) (fieldComponent k G U hzero j) :=
    component_finite_of_noetherian G U j
  have hfin : Module.Finite k (fieldComponent k G U hzero j) :=
    Module.Finite.trans (Base G) (fieldComponent k G U hzero j)
  letI := hfin
  refine ⟨hfin, ?_⟩
  have hlength := Module.length_eq_of_surjective
    (R := Base G) (M := fieldComponent k G U hzero j) hsurj
  rw [Module.length_eq_finrank] at hlength
  change ((Module.length (Base G) (fieldComponent k G U hzero j)).toNat : ℤ) = _
  rw [← hlength]
  simp

/-- The complete faithful, standard, connected graded annihilator reduction. -/
theorem quotient : Specs.P103.HilbertAnnihilatorQuotient.quotientType.{u,v,w} := by
  intro k A M _ _ _ _ _ _ _ _ _ _ G U hzero hstd
  let C := A ⧸ Module.annihilator A M
  letI : Module C M := Module.quotientAnnihilator (R := A) (M := M)
  change Nontrivial C ∧ FaithfulSMul C M ∧ Module.Finite C M ∧ IsScalarTower k C M ∧ _
  have hproper : Module.annihilator A M ≠ ⊤ := by
    intro h
    have : Subsingleton M := Module.annihilator_eq_top_iff.mp h
    exact not_nontrivial M inferInstance
  have hnontrivial : Nontrivial C := Submodule.Quotient.nontrivial_iff.mpr hproper
  have htower : IsScalarTower k C M :=
    IsScalarTower.of_algebraMap_smul fun a m => by
      change (algebraMap k A a) • m = a • m
      exact algebraMap_smul A a m
  refine ⟨hnontrivial, descended_faithful, descended_finite, htower, fun a m => rfl,
    quotientGrading G U, descendedGrading G U, quotient_connected k G U hzero,
    quotient_standard G U hstd, fun j => rfl, fun j => rfl,
    quotient_hilbertFunction G U, rfl⟩

end P103.HilbertAnnihilatorQuotient
