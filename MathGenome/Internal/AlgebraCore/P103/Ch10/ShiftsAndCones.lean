import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.ShiftsAndCones
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomologySequence
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomotopyAndContraction

namespace P103.Ch10.ShiftsAndCones
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch10.ShiftsAndCones
open HomologicalComplex.homotopyCofiber
noncomputable section
universe u v w

abbrev shift := @P103.Specs.Ch10.ShiftsAndCones.shift.{u,v,w}
abbrev shiftTermEquiv := @P103.Specs.Ch10.ShiftsAndCones.shiftTermEquiv.{u,v,w}
abbrev cone := @P103.Specs.Ch10.ShiftsAndCones.cone.{u,v,w}
abbrev coneTermEquiv := @P103.Specs.Ch10.ShiftsAndCones.coneTermEquiv.{u,v,w}
abbrev coneInclusion := @P103.Specs.Ch10.ShiftsAndCones.coneInclusion.{u,v,w}
abbrev coneProjection := @P103.Specs.Ch10.ShiftsAndCones.coneProjection.{u,v,w}
abbrev shiftCyclesEquiv := @P103.Specs.Ch10.ShiftsAndCones.shiftCyclesEquiv.{u,v,w}
abbrev shiftHomologyEquiv := @P103.Specs.Ch10.ShiftsAndCones.shiftHomologyEquiv.{u,v,w}
abbrev coneConnecting := @P103.Specs.Ch10.ShiftsAndCones.coneConnecting.{u,v,w}
abbrev chainShift := @P103.Specs.Ch10.ShiftsAndCones.chainShift.{u,v}
abbrev cochainShift := @P103.Specs.Ch10.ShiftsAndCones.cochainShift.{u,v}
abbrev chainShiftTermEquiv := @P103.Specs.Ch10.ShiftsAndCones.chainShiftTermEquiv.{u,v}
abbrev cochainShiftTermEquiv := @P103.Specs.Ch10.ShiftsAndCones.cochainShiftTermEquiv.{u,v}
abbrev chainConeTermEquiv := @P103.Specs.Ch10.ShiftsAndCones.chainConeTermEquiv.{u,v}
abbrev cochainConeTermEquiv := @P103.Specs.Ch10.ShiftsAndCones.cochainConeTermEquiv.{u,v}
abbrev chainShiftHomologyEquiv := @P103.Specs.Ch10.ShiftsAndCones.chainShiftHomologyEquiv.{u,v}
abbrev cochainShiftHomologyEquiv := @P103.Specs.Ch10.ShiftsAndCones.cochainShiftHomologyEquiv.{u,v}
abbrev integerDouble := @P103.Specs.Ch10.ShiftsAndCones.integerDouble
abbrev integerModTwo := @P103.Specs.Ch10.ShiftsAndCones.integerModTwo
abbrev augmentationSource := @P103.Specs.Ch10.ShiftsAndCones.augmentationSource
abbrev augmentationTarget := @P103.Specs.Ch10.ShiftsAndCones.augmentationTarget
abbrev augmentation := @P103.Specs.Ch10.ShiftsAndCones.augmentation


/-- The connecting maps of a long exact homology sequence are bijective
precisely when its middle complex is acyclic. -/
theorem acyclic_iff_bijective_connecting
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C)
    (next prev : ι → ι) (hnextprev : ∀ n, next (prev n) = n)
    (δ : ∀ n, Homology C n →ₗ[R] Homology A (next n))
    (hδ : ∀ n, SequenceExact i p n (next n) (δ n)) :
    Acyclic B ↔ ∀ n, Function.Bijective (δ n) := by
  constructor
  · intro hB n
    have hzero := P103.Ch10.HomologySequence.zero_endpoints i p n (next n) (δ n) (hδ n)
    exact ⟨hzero.2.2.2.1 (hB n), hzero.2.2.2.2 (hB (next n))⟩
  · intro hbij n
    have hpzero : homologyMap p n = 0 :=
      (LinearMap.injective_iff_eq_zero_of_exact (hδ n).2.1).mp (hbij n).1
    have hizero : homologyMap i n = 0 := by
      have hz := (LinearMap.surjective_iff_eq_zero_of_exact (hδ (prev n)).2.2).mp
        (hbij (prev n)).2
      exact (congrArg (fun k => homologyMap i k = 0) (hnextprev n)).mp hz
    refine ⟨fun x y => ?_⟩
    have allzero (z : Homology B n) : z = 0 := by
      obtain ⟨a, ha⟩ := ((hδ n).1 z).mp (by rw [hpzero]; rfl)
      rw [hizero] at ha
      exact ha.symm
    rw [allzero x, allzero y]

section Contraction
open HomologicalComplex
variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
variable [DecidableRel c.Rel]
variable (C : HomologicalComplex (ModuleCat.{v} R) c)
variable (hn : ∀ n, c.Rel n (c.next n)) (hc : ∀ j, ∃ i, c.Rel i j)

noncomputable def identityConeHomotopy :
    Homotopy (𝟙 (homotopyCofiber (𝟙 C))) 0 where
  hom i j := if hij : c.Rel j i then sndX (𝟙 C) i ≫ inlX (𝟙 C) i j hij else 0
  zero _ _ hij := dite_eq_right hij
  comm j := by
    obtain ⟨i, hij⟩ := hc j
    have hj := hn j
    rw [dNext_eq _ hj, prevD_eq _ hij]
    simp only [dite_eq_left hj, dite_eq_left hij, id_f, zero_f, add_zero,
      homotopyCofiber_d]
    apply ext_from_X (𝟙 C) (c.next j) j hj
    · simp only [comp_add, add_comp, assoc, d_sndX_assoc _ _ _ hj,
        inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero,
        inlX_d _ _ _ _ hij hj, comp_neg, comp_add, inlX_sndX_assoc,
        id_f, id_comp, comp_id, neg_zero]
      rfl
    · simp only [comp_add, add_comp, assoc, d_sndX_assoc _ _ _ hj,
        inrX_fstX_assoc, inrX_sndX_assoc, zero_comp, zero_add,
        inlX_d _ _ _ _ hij hj, comp_neg, comp_add,
        id_f, id_comp, comp_id]
      abel

@[simp]
lemma identityConeHomotopy_hom (i j : ι) (hij : c.Rel j i) :
    (identityConeHomotopy C hn hc).hom i j =
      sndX (𝟙 C) i ≫ inlX (𝟙 C) i j hij := by
  exact dite_eq_left hij

@[reassoc (attr := simp)]
lemma identityConeHomotopy_hom_sndX (i j : ι) (hij : c.Rel j i) :
    (identityConeHomotopy C hn hc).hom i j ≫ sndX (𝟙 C) j = 0 := by
  simp [identityConeHomotopy_hom C hn hc i j hij]

@[reassoc (attr := simp)]
lemma identityConeHomotopy_hom_fstX (i j : ι) (hij : c.Rel j i) :
    (identityConeHomotopy C hn hc).hom i j ≫ fstX (𝟙 C) j i hij = sndX (𝟙 C) i := by
  simp [identityConeHomotopy_hom C hn hc i j hij]

include hn hc in
theorem identityCone_contractible :
    P103.Specs.Ch10.HomotopyAndContraction.Contractible (homotopyCofiber (𝟙 C)) :=
  ⟨identityConeHomotopy C hn hc⟩

end Contraction

section Exact
variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
variable [DecidableRel c.Rel]
variable {C D : HomologicalComplex (ModuleCat.{v} R) c}

lemma cone_decomposition (f : C ⟶ D) (n m : ι) (h : c.Rel n m) :
    fstX f n m h ≫ inlX f m n h + sndX f n ≫ inrX f n = 𝟙 _ := by
  apply ext_to_X f n m h <;> simp [Preadditive.add_comp]

lemma cone_degreewise_exact (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n)) :
    DegreewiseExact (coneInclusion f) (coneProjection f hn) := by
  intro n
  have hi : ∀ x : D.X n, (sndX f n).hom ((inrX f n).hom x) = x := by
    intro x
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (inrX_sndX f n)) x
  have hs : ∀ x : C.X (c.next n),
      (fstX f n (c.next n) (hn n)).hom ((inlX f (c.next n) n (hn n)).hom x) = x := by
    intro x
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (inlX_fstX f _ _ (hn n))) x
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    change (inrX f n).hom a = (inrX f n).hom b at hab
    exact (hi a).symm.trans ((congrArg (sndX f n).hom hab).trans (hi b))
  · intro z
    constructor
    · intro hz
      change (fstX f n (c.next n) (hn n)).hom z = 0 at hz
      refine ⟨(sndX f n).hom z, ?_⟩
      change (inrX f n).hom ((sndX f n).hom z) = z
      have hd := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (cone_decomposition f n (c.next n) (hn n))) z
      change (inlX f (c.next n) n (hn n)).hom ((fstX f n (c.next n) (hn n)).hom z) +
        (inrX f n).hom ((sndX f n).hom z) = z at hd
      simpa only [hz, map_zero, zero_add] using hd
    · rintro ⟨a, rfl⟩
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (inrX_fstX f _ _ (hn n))) a
  · intro x
    exact ⟨(inlX f (c.next n) n (hn n)).hom x, hs x⟩

lemma cone_degreewise_split (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n)) :
    ∀ n, ∃ s : (shift C hn).X n →ₗ[R] (cone f).X n,
      ((coneProjection f hn).f n).hom.comp s = LinearMap.id := by
  intro n
  refine ⟨(inlX f (c.next n) n (hn n)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom (inlX_fstX f _ _ (hn n))

end Exact

section Coordinates

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
variable [DecidableRel c.Rel]
variable {C D : HomologicalComplex (ModuleCat.{v} R) c}

private lemma biprodIsoProd_hom_fst (M N : ModuleCat.{v} R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.fst R M N) = biprod.fst := by
  rw [← cancel_epi (ModuleCat.biprodIsoProd M N).inv]
  simp

private lemma biprodIsoProd_hom_snd (M N : ModuleCat.{v} R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.snd R M N) = biprod.snd := by
  rw [← cancel_epi (ModuleCat.biprodIsoProd M N).inv]
  simp

@[simp]
lemma coneTermEquiv_fst (f : C ⟶ D) (n m : ι) (hn : c.Rel n m) (z : (cone f).X n) :
    (coneTermEquiv f n m hn z).1 = (sndX f n).hom z := by
  have H : (XIsoBiprod f n m hn).hom ≫
      (ModuleCat.biprodIsoProd (C.X m) (D.X n)).hom ≫
      ModuleCat.ofHom (LinearMap.snd R (C.X m) (D.X n)) = sndX f n := by
    rw [biprodIsoProd_hom_snd]
    obtain rfl := c.next_eq' hn
    simp only [sndX, dite_eq_left hn]
  exact congrArg (fun t => t.hom z) H

@[simp]
lemma coneTermEquiv_snd (f : C ⟶ D) (n m : ι) (hn : c.Rel n m) (z : (cone f).X n) :
    (coneTermEquiv f n m hn z).2 = (fstX f n m hn).hom z := by
  have H : (XIsoBiprod f n m hn).hom ≫
      (ModuleCat.biprodIsoProd (C.X m) (D.X n)).hom ≫
      ModuleCat.ofHom (LinearMap.fst R (C.X m) (D.X n)) = fstX f n m hn := by
    rw [biprodIsoProd_hom_fst]
    rfl
  exact congrArg (fun t => t.hom z) H

lemma cone_d_coordinates (f : C ⟶ D) (i j k : ι)
    (hij : c.Rel i j) (hjk : c.Rel j k) (z : (cone f).X i) :
    coneTermEquiv f j k hjk (((cone f).d i j).hom z) =
      ((D.d i j).hom (coneTermEquiv f i j hij z).1 +
        (f.f j).hom (coneTermEquiv f i j hij z).2,
      -(C.d j k).hom (coneTermEquiv f i j hij z).2) := by
  apply Prod.ext
  · simp only [coneTermEquiv_fst, coneTermEquiv_snd]
    have H := congrArg (fun t => t.hom z) (d_sndX f i j hij)
    change (sndX f j).hom ((HomologicalComplex.homotopyCofiber.d f i j).hom z) = _
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
      LinearMap.add_apply, add_comm] using H
  · simp only [coneTermEquiv_snd]
    have H := congrArg (fun t => t.hom z) (d_fstX f i j k hij hjk)
    change (fstX f j k hjk).hom ((HomologicalComplex.homotopyCofiber.d f i j).hom z) = _
    simpa using H

@[simp]
lemma coneInclusion_coordinates (f : C ⟶ D) (n m : ι) (hn : c.Rel n m) (y : D.X n) :
    coneTermEquiv f n m hn (((coneInclusion f).f n).hom y) = (y, 0) := by
  apply Prod.ext
  · simp only [coneTermEquiv_fst]
    exact congrArg (fun t => t.hom y) (inrX_sndX f n)
  · simp only [coneTermEquiv_snd]
    exact congrArg (fun t => t.hom y) (inrX_fstX f n m hn)

@[simp]
lemma coneProjection_coordinates (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n))
    (n : ι) (z : (cone f).X n) :
    ((coneProjection f hn).f n).hom z = (coneTermEquiv f n (c.next n) (hn n) z).2 := by
  rw [coneTermEquiv_snd]
  rfl

@[simp]
lemma coneTermEquiv_inlX (f : C ⟶ D) (n m : ι) (hn : c.Rel n m) (x : C.X m) :
    coneTermEquiv f n m hn ((inlX f m n hn).hom x) = (0, x) := by
  apply Prod.ext
  · simp only [coneTermEquiv_fst]
    exact congrArg (fun t => t.hom x) (inlX_sndX f m n hn)
  · simp only [coneTermEquiv_snd]
    exact congrArg (fun t => t.hom x) (inlX_fstX f m n hn)

lemma coneTermEquiv_symm_apply (f : C ⟶ D) (n m : ι) (hn : c.Rel n m)
    (y : D.X n) (x : C.X m) :
    (coneTermEquiv f n m hn).symm (y, x) =
      (inrX f n).hom y + (inlX f m n hn).hom x := by
  apply (coneTermEquiv f n m hn).injective
  rw [LinearEquiv.apply_symm_apply, map_add, coneTermEquiv_inlX]
  have H : coneTermEquiv f n m hn ((inrX f n).hom y) = (y, 0) :=
    coneInclusion_coordinates f n m hn y
  rw [H]
  simp

@[simp]
lemma coneTermEquiv_symm_sndX (f : C ⟶ D) (n m : ι) (hn : c.Rel n m)
    (a : D.X n × C.X m) :
    (sndX f n).hom ((coneTermEquiv f n m hn).symm a) = a.1 := by
  rw [← coneTermEquiv_fst f n m hn, LinearEquiv.apply_symm_apply]

@[simp]
lemma coneTermEquiv_symm_fstX (f : C ⟶ D) (n m : ι) (hn : c.Rel n m)
    (a : D.X n × C.X m) :
    (fstX f n m hn).hom ((coneTermEquiv f n m hn).symm a) = a.2 := by
  rw [← coneTermEquiv_snd f n m hn, LinearEquiv.apply_symm_apply]


end Coordinates

section Connecting
variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
variable [DecidableRel c.Rel]
variable {C D : HomologicalComplex (ModuleCat.{v} R) c}

lemma cone_connecting_of_formula (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n)) (n : ι)
    (e : Homology (shift C hn) n →ₗ[R] Homology C (c.next n))
    (he : ∀ (z : cycles (shift C hn) n) (a : cycles C (c.next n)),
      a.val = z.val → e (homologyClass (shift C hn) n z) = homologyClass C (c.next n) a) :
    Connecting (coneInclusion f) (coneProjection f hn) n (c.next n)
      ((homologyMap f (c.next n)).comp e) := by
  intro z b a hb ha
  let a' : cycles C (c.next n) := ⟨z.val, by
    have hz := z.property
    change (-C.d (c.next n) (c.next (c.next n))).hom z.val = 0 at hz
    change (C.d (c.next n) (c.next (c.next n))).hom z.val = 0
    change -((C.d (c.next n) (c.next (c.next n))).hom z.val) = 0 at hz
    exact neg_eq_zero.mp hz⟩
  rw [LinearMap.comp_apply, he z a' rfl]
  change homologyClass D (c.next n) (cyclesMap f (c.next n) a') =
    homologyClass D (c.next n) a
  apply (P103.Ch10.Complexes.homologyClass_eq_iff D (c.next n) _ _).mpr
  apply (P103.Ch10.HomologySequence.boundary_iff D (hn n) _).mpr
  change (fstX f n (c.next n) (hn n)).hom b = z.val at hb
  change (inrX f (c.next n)).hom a.val =
    (HomologicalComplex.homotopyCofiber.d f n (c.next n)).hom b at ha
  have hi := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (inrX_sndX f (c.next n))) a.val
  have hd := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (d_sndX f n (c.next n) (hn n))) b
  change (sndX f (c.next n)).hom ((inrX f (c.next n)).hom a.val) = a.val at hi
  change (sndX f (c.next n)).hom ((HomologicalComplex.homotopyCofiber.d f n (c.next n)).hom b) =
    (f.f (c.next n)).hom ((fstX f n (c.next n) (hn n)).hom b) +
      (D.d n (c.next n)).hom ((sndX f n).hom b) at hd
  rw [hb, ← ha, hi] at hd
  refine ⟨-(sndX f n).hom b, ?_⟩
  change (D.d n (c.next n)).hom (-(sndX f n).hom b) =
    (f.f (c.next n)).hom z.val - a.val
  rw [map_neg, hd]
  abel


lemma shiftHomologyEquiv_class (hn : ∀ n, c.Rel n (c.next n))
    (hp : ∀ n, c.Rel (c.prev n) n) (n : ι) (z : cycles (shift C hn) n) :
    shiftHomologyEquiv C hn hp n (homologyClass (shift C hn) n z) =
      homologyClass C (c.next n) (shiftCyclesEquiv C hn n z) := rfl

lemma cone_connecting (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n))
    (hp : ∀ n, c.Rel (c.prev n) n) (n : ι) :
    Connecting (coneInclusion f) (coneProjection f hn) n (c.next n)
      ((homologyMap f (c.next n)).comp (shiftHomologyEquiv C hn hp n).toLinearMap) := by
  apply cone_connecting_of_formula
  intro z a ha
  have heq : a = shiftCyclesEquiv C hn n z := Subtype.ext ha
  rw [heq]
  rfl

lemma cone_sequence_exact_of_degreewise_exact (f : C ⟶ D)
    (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n)
    (hs : DegreewiseExact (coneInclusion f) (coneProjection f hn)) (n : ι) :
    SequenceExact (coneInclusion f) (coneProjection f hn) n (c.next n)
      ((homologyMap f (c.next n)).comp (shiftHomologyEquiv C hn hp n).toLinearMap) := by
  have hconn := cone_connecting f hn hp n
  exact ⟨P103.Ch10.HomologySequence.exact_middle _ _ hs (hn n),
    P103.Ch10.HomologySequence.exact_before_connecting _ _ hs (hn n) _ hconn,
    P103.Ch10.HomologySequence.exact_after_connecting _ _ hs (hn n) _ hconn⟩


/-- The cone sequence with its specified positive connecting map. -/
theorem cone_sequence_exact (f : C ⟶ D)
    (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n) (n : ι) :
    SequenceExact (coneInclusion f) (coneProjection f hn) n (c.next n)
      (coneConnecting f hn hp n) :=
  cone_sequence_exact_of_degreewise_exact f hn hp (cone_degreewise_exact f hn) n

/-- The cone criterion for a shape with all adjacent degrees present. -/
theorem cone_criterion (f : C ⟶ D)
    (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n) :
    QuasiIsomorphism f ↔ Acyclic (cone f) := by
  have H := acyclic_iff_bijective_connecting (coneInclusion f) (coneProjection f hn)
    c.next c.prev (fun n => c.next_eq' (hp n)) (coneConnecting f hn hp)
    (cone_sequence_exact f hn hp)
  rw [H]
  constructor
  · intro hf n
    exact (hf (c.next n)).comp (shiftHomologyEquiv C hn hp n).bijective
  · intro hf n
    have h := hf (c.prev n)
    have hbij : Function.Bijective (homologyMap f (c.next (c.prev n))) := by
      exact (Function.Bijective.of_comp_iff _
        (shiftHomologyEquiv C hn hp (c.prev n)).bijective).mp h
    exact (congrArg (fun k => Function.Bijective (homologyMap f k))
      (c.next_eq' (hp n))).mp hbij

lemma identityConeHomotopy_coordinates (C : HomologicalComplex (ModuleCat.{v} R) c)
    (hn : ∀ n, c.Rel n (c.next n)) (hc : ∀ j, ∃ i, c.Rel i j)
    (i j k : ι) (hji : c.Rel j i)
    (hik : c.Rel i k) (z : (cone (𝟙 C)).X i) :
    coneTermEquiv (𝟙 C) j i hji (((identityConeHomotopy C hn hc).hom i j).hom z) =
      (0, (coneTermEquiv (𝟙 C) i k hik z).1) := by
  apply Prod.ext
  · rw [coneTermEquiv_fst]
    exact congrArg (fun t => t.hom z) (identityConeHomotopy_hom_sndX C hn hc i j hji)
  · rw [coneTermEquiv_snd, coneTermEquiv_fst]
    exact congrArg (fun t => t.hom z) (identityConeHomotopy_hom_fstX C hn hc i j hji)
end Connecting

end
end P103.Ch10.ShiftsAndCones

namespace P103.Ch10.ShiftsAndCones
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch10.ShiftsAndCones
noncomputable section
universe u v w
variable {R : Type u} [Ring R]

theorem shift_d_coordinates {ι : Type w} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (hn : ∀ n, c.Rel n (c.next n))
    (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) (z : (shift C hn).X i) :
    shiftTermEquiv C hn j k hjk (((shift C hn).d i j).hom z) =
      -(C.d j k).hom (shiftTermEquiv C hn i j hij z) := by
  obtain rfl := c.next_eq' hij
  obtain rfl := c.next_eq' hjk
  rfl

theorem chain_cone_differential {C D : Chain.{u,v} R} (f : C ⟶ D) (n : ℤ)
    (z : (cone f).X n) :
    chainConeTermEquiv f (n - 1) (((cone f).d n (n - 1)).hom z) =
      ((D.d n (n - 1)).hom (chainConeTermEquiv f n z).1 +
        (f.f (n - 1)).hom (chainConeTermEquiv f n z).2,
      -(C.d (n - 1) ((n - 1) - 1)).hom (chainConeTermEquiv f n z).2) :=
  cone_d_coordinates f n (n - 1) ((n - 1) - 1) _ _ z

theorem cochain_cone_differential {C D : Cochain.{u,v} R} (f : C ⟶ D) (n : ℤ)
    (z : (cone f).X n) :
    cochainConeTermEquiv f (n + 1) (((cone f).d n (n + 1)).hom z) =
      ((D.d n (n + 1)).hom (cochainConeTermEquiv f n z).1 +
        (f.f (n + 1)).hom (cochainConeTermEquiv f n z).2,
      -(C.d (n + 1) ((n + 1) + 1)).hom (cochainConeTermEquiv f n z).2) :=
  cone_d_coordinates f n (n + 1) ((n + 1) + 1) _ _ z

theorem chain_shift_differential (C : Chain.{u,v} R) (n : ℤ)
    (z : (chainShift C).X n) :
    chainShiftTermEquiv C (n - 1) (((chainShift C).d n (n - 1)).hom z) =
      -(C.d (n - 1) ((n - 1) - 1)).hom (chainShiftTermEquiv C n z) :=
  shift_d_coordinates C chainOutgoing n (n - 1) ((n - 1) - 1) _ _ z

theorem cochain_shift_differential (C : Cochain.{u,v} R) (n : ℤ)
    (z : (cochainShift C).X n) :
    cochainShiftTermEquiv C (n + 1) (((cochainShift C).d n (n + 1)).hom z) =
      -(C.d (n + 1) ((n + 1) + 1)).hom (cochainShiftTermEquiv C n z) :=
  shift_d_coordinates C cochainOutgoing n (n + 1) ((n + 1) + 1) _ _ z

theorem chain_cone_criterion {C D : Chain.{u,v} R} (f : C ⟶ D) :
    QuasiIsomorphism f ↔ Acyclic (cone f) :=
  cone_criterion f chainOutgoing chainIncoming

theorem cochain_cone_criterion {C D : Cochain.{u,v} R} (f : C ⟶ D) :
    QuasiIsomorphism f ↔ Acyclic (cone f) :=
  cone_criterion f cochainOutgoing cochainIncoming

/-- A contracting homotopy with the manuscript's (0,y) coordinate formula. -/
theorem identityCone_contraction {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
    (C : HomologicalComplex (ModuleCat.{v} R) c) (hn : ∀ n, c.Rel n (c.next n))
    (hp : ∀ n, c.Rel (c.prev n) n) :
    ∃ h : Homotopy (𝟙 (cone (𝟙 C))) 0,
      ∀ (i j k : ι) (hji : c.Rel j i) (hik : c.Rel i k) (z : (cone (𝟙 C)).X i),
        coneTermEquiv (𝟙 C) j i hji ((h.hom i j).hom z) =
          (0, (coneTermEquiv (𝟙 C) i k hik z).1) := by
  refine ⟨identityConeHomotopy C hn (fun n => ⟨c.prev n, hp n⟩), ?_⟩
  exact identityConeHomotopy_coordinates C hn (fun n => ⟨c.prev n, hp n⟩)

end
end P103.Ch10.ShiftsAndCones
namespace P103.Ch10.ShiftsAndCones
open CategoryTheory CategoryTheory.Limits
open P103.Ch10.Complexes
open P103.Specs.Ch10.ShiftsAndCones
noncomputable section

theorem augmentationSource_d : (augmentationSource.d 1 0).hom = integerDouble := rfl

theorem augmentation_zero : (augmentation.f 0).hom = integerModTwo := rfl

theorem augmentationSource_degree_zero : augmentationSource.X 0 = ModuleCat.of ℤ ℤ := rfl

theorem augmentationSource_degree_one : augmentationSource.X 1 = ModuleCat.of ℤ ℤ := rfl

theorem augmentationTarget_degree_zero : augmentationTarget.X 0 = ModuleCat.of ℤ (ZMod 2) := rfl

theorem augmentationSource_supported : SupportedIn augmentationSource ({0, 1} : Set ℤ) := by
  intro n hn
  have h₀ : n ≠ 0 := by intro h; exact hn (by simp [h])
  have h₁ : n ≠ 1 := by intro h; exact hn (by simp [h])
  change Subsingleton (augmentationSourceTerm n)
  simp only [augmentationSourceTerm, ite_eq_right h₀, ite_eq_right h₁]
  infer_instance

theorem augmentationTarget_supported : SupportedIn augmentationTarget ({0} : Set ℤ) := by
  intro n hn
  have h₀ : n ≠ 0 := by simpa using hn
  change Subsingleton (augmentationTargetTerm n)
  simp only [augmentationTargetTerm, ite_eq_right h₀]
  infer_instance

theorem augmentation_reverse_zero (g : augmentationTarget ⟶ augmentationSource) : g = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  by_cases h : n = 0
  · subst n
    have hx : x + x = 0 := by
      have hh : ∀ t : ZMod 2, t + t = 0 := by decide
      exact hh x
    have hh : (g.f 0).hom x + (g.f 0).hom x = 0 := by rw [← map_add, hx, map_zero]
    change (g.f 0).hom x = (0 : ℤ)
    change (g.f 0).hom x + (g.f 0).hom x = (0 : ℤ) at hh
    let y : ℤ := (g.f 0).hom x
    have hy : y + y = 0 := hh
    change y = 0
    omega
  · let := augmentationTarget_supported n (by simpa using h)
    have hx : x = 0 := Subsingleton.elim _ _
    simp only [hx, map_zero]

theorem augmentationSource_homology_subsingleton (n : ℤ) (hn : n ≠ 0) :
    Subsingleton (Homology augmentationSource n) := by
  by_cases h₁ : n = 1
  · subst n
    have hc : Subsingleton (cycles augmentationSource 1) := by
      refine ⟨fun x y => ?_⟩
      apply Subtype.ext
      let a : ℤ := x.val
      let b : ℤ := y.val
      have hx : a ∈ cycles augmentationSource 1 := x.property
      have hy : b ∈ cycles augmentationSource 1 := y.property
      rw [cycles_chain] at hx hy
      change 2 * a = 0 at hx
      change 2 * b = 0 at hy
      change a = b
      omega
    let := hc
    infer_instance
  · let := augmentationSource_supported n (by simp [hn, h₁])
    infer_instance

theorem augmentationTarget_homology_subsingleton (n : ℤ) (hn : n ≠ 0) :
    Subsingleton (Homology augmentationTarget n) := by
  let := augmentationTarget_supported n (by simpa using hn)
  infer_instance

theorem augmentation_quasiIsomorphism : QuasiIsomorphism augmentation := by
  intro n
  by_cases hn : n = 0
  · subst n
    constructor
    · apply (injective_iff_map_eq_zero (homologyMap augmentation 0)).mpr
      intro q hq
      obtain ⟨z, rfl⟩ := (cycleBoundaries augmentationSource 0).mkQ_surjective q
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have hh := (Submodule.Quotient.mk_eq_zero (cycleBoundaries augmentationTarget 0)).mp hq
      change (cyclesMap augmentation 0 z).val ∈ boundaries augmentationTarget 0 at hh
      rw [boundaries_chain] at hh
      change ∃ t : PUnit, (0 : PUnit →ₗ[ℤ] ZMod 2) t = integerModTwo (z.val : ℤ) at hh
      obtain ⟨t, ht⟩ := hh
      let a : ℤ := z.val
      have hz : (a : ZMod 2) = 0 := ht.symm
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp hz
      change z.val ∈ boundaries augmentationSource 0
      rw [boundaries_chain]
      change ∃ k : ℤ, integerDouble k = z.val
      exact ⟨k, hk.symm⟩
    · intro q
      obtain ⟨z, rfl⟩ := (cycleBoundaries augmentationTarget 0).mkQ_surjective q
      let z' : ZMod 2 := z.val
      let x : cycles augmentationSource 0 := ⟨(z'.val : ℤ), by
        rw [cycles_chain]
        change (0 : ℤ →ₗ[ℤ] PUnit) _ = 0
        rfl⟩
      refine ⟨homologyClass augmentationSource 0 x, ?_⟩
      rw [homologyMap_apply]
      congr 1
      apply Subtype.ext
      change (((z'.val : ℕ) : ℤ) : ZMod 2) = z'
      simp
  · let := augmentationSource_homology_subsingleton n hn
    let := augmentationTarget_homology_subsingleton n hn
    exact Function.bijective_of_subsingleton' _


theorem augmentationTarget_nonzero_homology : ∃ q : Homology augmentationTarget 0, q ≠ 0 := by
  let z : cycles augmentationTarget 0 := ⟨(1 : ZMod 2), by
    rw [cycles_chain]
    change (0 : ZMod 2 →ₗ[ℤ] PUnit) 1 = 0
    rfl⟩
  refine ⟨homologyClass augmentationTarget 0 z, ?_⟩
  intro h
  have hh := (Submodule.Quotient.mk_eq_zero (cycleBoundaries augmentationTarget 0)).mp h
  change z.val ∈ boundaries augmentationTarget 0 at hh
  rw [boundaries_chain] at hh
  change ∃ t : PUnit, (0 : PUnit →ₗ[ℤ] ZMod 2) t = 1 at hh
  obtain ⟨t, ht⟩ := hh
  exact (zero_ne_one : (0 : ZMod 2) ≠ 1) ht

theorem augmentation_not_homotopyEquiv : ¬ Nonempty (HomotopyEquiv augmentationSource augmentationTarget) := by
  rintro ⟨h⟩
  have he := P103.Ch10.HomotopyAndContraction.homotopy_homologyMap h.homotopyInvHomId 0
  rw [augmentation_reverse_zero h.inv, zero_comp, homologyMap_zero, homologyMap_id] at he
  obtain ⟨q, hq⟩ := augmentationTarget_nonzero_homology
  exact hq (LinearMap.congr_fun he q).symm

end
end P103.Ch10.ShiftsAndCones

namespace P103.Ch10.ShiftsAndCones
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch10.ShiftsAndCones
noncomputable section
universe u v w
lemma cone_connecting_at
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
    {C D : HomologicalComplex (ModuleCat.{v} R) c}
    (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n)
    (n m : ι) (h : c.next n = m) :
    Connecting (coneInclusion f) (coneProjection f hn) n m
      ((homologyMap f m).comp ((shiftHomologyEquiv C hn hp n).trans
        (LinearEquiv.cast (M := fun k => Homology C k) h)).toLinearMap) := by
  cases h
  exact cone_connecting f hn hp n

lemma chain_cone_connecting
    {R : Type u} [Ring R] {C D : Chain.{u,v} R} (f : C ⟶ D) (n : ℤ) :
    Connecting (coneInclusion f) (coneProjection f chainOutgoing) n (n - 1)
      ((homologyMap f (n - 1)).comp (chainShiftHomologyEquiv C n).toLinearMap) := by
  exact cone_connecting_at f chainOutgoing chainIncoming n (n - 1) (ChainComplex.next ℤ n)

lemma cochain_cone_connecting
    {R : Type u} [Ring R] {C D : Cochain.{u,v} R} (f : C ⟶ D) (n : ℤ) :
    Connecting (coneInclusion f) (coneProjection f cochainOutgoing) n (n + 1)
      ((homologyMap f (n + 1)).comp (cochainShiftHomologyEquiv C n).toLinearMap) := by
  exact cone_connecting_at f cochainOutgoing cochainIncoming n (n + 1) (CochainComplex.next ℤ n)

end
end P103.Ch10.ShiftsAndCones
