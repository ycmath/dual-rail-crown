/-
Wcy2.Crown -- the resolved-face crown of the dual-rail carrier.
Mechanizes the crown note:
  crown_necessity    : a closed-core term realizing a Boolean face map forces
                       self-duality (from cterm_equivariant);
  crown_sufficiency  : every self-dual face map is realized by an explicit
                       closed-core term (orbit-literal minterm DNF);
  restrictRep/extendSD : the count bijection -- self-dual maps of arity n+1
                       correspond to free assignments on the
                       first-coordinate-TRU representatives;
  maj3_realized / and2_not_selfDual : calibration (kernel decide);
  sdGuard            : one-constant completion -- the self-dualization with
                       one guard variable is self-dual and specializes at
                       guard FAL to any given map.
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import Wcy2.RTerm

namespace Wcy2

/-! ### the face and realization -/

/-- the face environment of a Boolean point of the resolved face. -/
def faceEnv {n : Nat} (y : Fin n → Bool) : Fin n → D4 := fun i => boolToR (y i)

/-- a closed-core term realizes a Boolean face map. -/
def CRealizes {n : Nat} (t : CTerm n) (h : (Fin n → Bool) → Bool) : Prop :=
  ∀ y, ceval t (faceEnv y) = boolToR (h y)

/-- self-duality (the Boolean reading of P-equivariance on the face). -/
def SelfDual {n : Nat} (h : (Fin n → Bool) → Bool) : Prop :=
  ∀ y, h (fun i => !(y i)) = !(h y)

/-! ### necessity -/

/-- ★ crown necessity: a realized face map is self-dual. -/
theorem crown_necessity {n : Nat} (t : CTerm n) (h : (Fin n → Bool) → Bool)
    (hr : CRealizes t h) : SelfDual h := by
  intro y
  have hface : faceEnv (fun i => !(y i)) = fun i => Pd (faceEnv y i) := by
    funext i
    show boolToR (!(y i)) = Pd (boolToR (y i))
    cases y i <;> rfl
  have h1 : ceval t (faceEnv (fun i => !(y i))) = Pd (ceval t (faceEnv y)) := by
    rw [hface]
    exact cterm_equivariant t (faceEnv y)
  rw [hr (fun i => !(y i)), hr y] at h1
  have h2 : Pd (boolToR (h y)) = boolToR (!(h y)) := by
    cases h y <;> rfl
  rw [h2] at h1
  exact boolToR_inj h1

/-! ### orbit literals and minterms -/

/-- orbit literal: the variable if the target bit is TRU, its P-image if
    FAL. -/
def lit {n : Nat} (i : Fin n) : Bool → CTerm n
  | true => .proj i
  | false => .tP (.proj i)

theorem lit_eval {n : Nat} (i : Fin n) (b : Bool) (z : Fin n → Bool) :
    ceval (lit i b) (faceEnv z) = boolToR (z i == b) := by
  cases b
  · show Pd (boolToR (z i)) = boolToR (z i == false)
    cases z i <;> rfl
  · show boolToR (z i) = boolToR (z i == true)
    cases z i <;> rfl

/-- the three-way value of a resolved meet over agreement bits. -/
def meetVal (b : Bool) (bs : List Bool) : D4 :=
  if b && bs.all (fun c => c) then TRUd
  else if !b && bs.all (fun c => !c) then FALd
  else UNK

theorem meetk_meetVal (b c : Bool) (cs : List Bool) :
    meetk (boolToR b) (meetVal c cs) = meetVal b (c :: cs) := by
  cases hA : cs.all (fun x => x) <;> cases hB : cs.all (fun x => !x) <;>
    cases b <;> cases c <;>
    simp only [meetVal, List.all_cons, hA, hB] <;> rfl

/-- orbit-literal minterm over an explicit index chain. -/
def mintermL {n : Nat} (y : Fin n → Bool) : Fin n → List (Fin n) → CTerm n
  | i, [] => lit i (y i)
  | i, j :: js => .tmeet (lit i (y i)) (mintermL y j js)

theorem mintermL_eval {n : Nat} (y z : Fin n → Bool) :
    ∀ (js : List (Fin n)) (i : Fin n),
    ceval (mintermL y i js) (faceEnv z) =
      meetVal (z i == y i) (js.map (fun j => z j == y j)) := by
  intro js
  induction js with
  | nil =>
      intro i
      show ceval (lit i (y i)) (faceEnv z) = _
      rw [lit_eval]
      cases (z i == y i) <;> rfl
  | cons j js ih =>
      intro i
      show meetk (ceval (lit i (y i)) (faceEnv z))
          (ceval (mintermL y j js) (faceEnv z)) = _
      rw [lit_eval, ih j, List.map_cons, meetk_meetVal]

/-- the full minterm of a face point (arity n+1). -/
def minterm {n : Nat} (y : Fin (n + 1) → Bool) : CTerm (n + 1) :=
  mintermL y 0 ((List.finRange n).map Fin.succ)

theorem minterm_eval {n : Nat} (y z : Fin (n + 1) → Bool) :
    ceval (minterm y) (faceEnv z) =
      meetVal (z 0 == y 0)
        (((List.finRange n).map Fin.succ).map (fun j => z j == y j)) :=
  mintermL_eval y z _ 0

/-! ### meetVal inversions -/

theorem meetVal_eq_TRUd (b : Bool) (bs : List Bool) :
    meetVal b bs = TRUd ↔ (b && bs.all (fun c => c)) = true := by
  cases hA : (b && bs.all (fun c => c)) <;>
    cases hB : (!b && bs.all (fun c => !c)) <;>
    simp [meetVal, hA, hB] <;> decide

theorem meetVal_eq_FALd (b : Bool) (bs : List Bool) :
    meetVal b bs = FALd ↔ ((b && bs.all (fun c => c)) = false ∧
      (!b && bs.all (fun c => !c)) = true) := by
  cases hA : (b && bs.all (fun c => c)) <;>
    cases hB : (!b && bs.all (fun c => !c)) <;>
    simp [meetVal, hA, hB] <;> decide

theorem meetVal_cases (b : Bool) (bs : List Bool) :
    meetVal b bs = TRUd ∨ meetVal b bs = FALd ∨ meetVal b bs = UNK := by
  unfold meetVal
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-! ### minterm value classification on the face -/

theorem minterm_self {n : Nat} (y : Fin (n + 1) → Bool) :
    ceval (minterm y) (faceEnv y) = TRUd := by
  rw [minterm_eval, meetVal_eq_TRUd]
  have h0 : (y 0 == y 0) = true := by cases y 0 <;> rfl
  rw [h0]
  refine Bool.true_and _ ▸ List.all_eq_true.mpr ?_
  intro c hc
  rcases List.mem_map.mp hc with ⟨j, _, rfl⟩
  cases y j <;> rfl

theorem minterm_anti {n : Nat} (y : Fin (n + 1) → Bool) :
    ceval (minterm y) (faceEnv (fun i => !(y i))) = FALd := by
  rw [minterm_eval, meetVal_eq_FALd]
  constructor
  · have h0 : ((!(y 0)) == y 0) = false := by cases y 0 <;> rfl
    rw [h0]
    rfl
  · have h0 : (!((!(y 0)) == y 0)) = true := by cases y 0 <;> rfl
    rw [h0]
    refine Bool.true_and _ ▸ List.all_eq_true.mpr ?_
    intro c hc
    rcases List.mem_map.mp hc with ⟨j, _, rfl⟩
    cases y j <;> rfl

theorem minterm_TRUd_inv {n : Nat} (y z : Fin (n + 1) → Bool)
    (h : ceval (minterm y) (faceEnv z) = TRUd) : z = y := by
  rw [minterm_eval, meetVal_eq_TRUd, Bool.and_eq_true] at h
  obtain ⟨h0, hall⟩ := h
  funext i
  refine Fin.cases ?_ ?_ i
  · show z 0 = y 0
    cases hz : z 0 <;> cases hy : y 0 <;> rw [hz, hy] at h0 <;>
      first | rfl | exact absurd h0 (by decide)
  · intro j
    have hj : ((z j.succ == y j.succ) : Bool) = true := by
      refine List.all_eq_true.mp hall _ ?_
      exact List.mem_map.mpr ⟨j.succ,
        List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩, rfl⟩
    exact of_decide_eq_true (by
      cases hzy : z j.succ <;> cases hyy : y j.succ <;>
        rw [hzy, hyy] at hj <;> first | rfl | exact absurd hj (by decide))

theorem minterm_FALd_inv {n : Nat} (y z : Fin (n + 1) → Bool)
    (h : ceval (minterm y) (faceEnv z) = FALd) : z = fun i => !(y i) := by
  rw [minterm_eval, meetVal_eq_FALd] at h
  obtain ⟨-, hB⟩ := h
  rw [Bool.and_eq_true] at hB
  obtain ⟨h0, hall⟩ := hB
  funext i
  refine Fin.cases ?_ ?_ i
  · show z 0 = !(y 0)
    cases hz : z 0 <;> cases hy : y 0 <;> rw [hz, hy] at h0 <;>
      first | rfl | exact absurd h0 (by decide)
  · intro j
    show z j.succ = !(y j.succ)
    have hj : ((!(z j.succ == y j.succ)) : Bool) = true := by
      refine List.all_eq_true.mp hall _ ?_
      exact List.mem_map.mpr ⟨j.succ,
        List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩, rfl⟩
    cases hz : z j.succ <;> cases hy : y j.succ <;> rw [hz, hy] at hj <;>
      first | rfl | exact absurd hj (by decide)

/-! ### join folds over classified values -/

def foldJ : D4 → List D4 → D4
  | v, [] => v
  | v, w :: ws => joink v (foldJ w ws)

theorem foldJ_TU_closed : ∀ (v : D4) (vs : List D4),
    (v = TRUd ∨ v = UNK) → (∀ w ∈ vs, w = TRUd ∨ w = UNK) →
    (foldJ v vs = TRUd ∨ foldJ v vs = UNK)
  | v, [], hv, _ => hv
  | v, w :: ws, hv, hvs => by
      have hrec := foldJ_TU_closed w ws (hvs w (by simp))
        (fun x hx => hvs x (by simp [hx]))
      show (joink v (foldJ w ws) = TRUd ∨ joink v (foldJ w ws) = UNK)
      rcases hv with rfl | rfl <;> rcases hrec with h | h <;> rw [h] <;>
        first | exact Or.inl rfl | exact Or.inr rfl

theorem foldJ_TU : ∀ (v : D4) (vs : List D4),
    (v = TRUd ∨ v = UNK) → (∀ w ∈ vs, w = TRUd ∨ w = UNK) →
    (v = TRUd ∨ TRUd ∈ vs) → foldJ v vs = TRUd
  | v, [], _, _, hex => by
      rcases hex with rfl | hmem
      · rfl
      · cases hmem
  | v, w :: ws, hv, hvs, hex => by
      show joink v (foldJ w ws) = TRUd
      rcases hex with rfl | hmem
      · have hrec := foldJ_TU_closed w ws (hvs w (by simp))
          (fun x hx => hvs x (by simp [hx]))
        rcases hrec with h | h <;> rw [h] <;> rfl
      · have hsub : foldJ w ws = TRUd := by
          rcases List.mem_cons.mp hmem with heq | hmem'
          · exact foldJ_TU w ws (Or.inl heq.symm)
              (fun x hx => hvs x (by simp [hx])) (Or.inl heq.symm)
          · exact foldJ_TU w ws (hvs w (by simp))
              (fun x hx => hvs x (by simp [hx])) (Or.inr hmem')
        rw [hsub]
        rcases hv with rfl | rfl <;> rfl

theorem foldJ_FU_closed : ∀ (v : D4) (vs : List D4),
    (v = FALd ∨ v = UNK) → (∀ w ∈ vs, w = FALd ∨ w = UNK) →
    (foldJ v vs = FALd ∨ foldJ v vs = UNK)
  | v, [], hv, _ => hv
  | v, w :: ws, hv, hvs => by
      have hrec := foldJ_FU_closed w ws (hvs w (by simp))
        (fun x hx => hvs x (by simp [hx]))
      show (joink v (foldJ w ws) = FALd ∨ joink v (foldJ w ws) = UNK)
      rcases hv with rfl | rfl <;> rcases hrec with h | h <;> rw [h] <;>
        first | exact Or.inl rfl | exact Or.inr rfl

theorem foldJ_FU : ∀ (v : D4) (vs : List D4),
    (v = FALd ∨ v = UNK) → (∀ w ∈ vs, w = FALd ∨ w = UNK) →
    (v = FALd ∨ FALd ∈ vs) → foldJ v vs = FALd
  | v, [], _, _, hex => by
      rcases hex with rfl | hmem
      · rfl
      · cases hmem
  | v, w :: ws, hv, hvs, hex => by
      show joink v (foldJ w ws) = FALd
      rcases hex with rfl | hmem
      · have hrec := foldJ_FU_closed w ws (hvs w (by simp))
          (fun x hx => hvs x (by simp [hx]))
        rcases hrec with h | h <;> rw [h] <;> rfl
      · have hsub : foldJ w ws = FALd := by
          rcases List.mem_cons.mp hmem with heq | hmem'
          · exact foldJ_FU w ws (Or.inl heq.symm)
              (fun x hx => hvs x (by simp [hx])) (Or.inl heq.symm)
          · exact foldJ_FU w ws (hvs w (by simp))
              (fun x hx => hvs x (by simp [hx])) (Or.inr hmem')
        rw [hsub]
        rcases hv with rfl | rfl <;> rfl

/-! ### the DNF term -/

def bigJoinT {n : Nat} : CTerm n → List (CTerm n) → CTerm n
  | t, [] => t
  | t, u :: us => .tjoin t (bigJoinT u us)

theorem bigJoinT_eval {n : Nat} (env : Fin n → D4) :
    ∀ (t : CTerm n) (ts : List (CTerm n)),
    ceval (bigJoinT t ts) env = foldJ (ceval t env) (ts.map (ceval · env))
  | t, [] => rfl
  | t, u :: us => by
      show joink (ceval t env) (ceval (bigJoinT u us) env) = _
      rw [bigJoinT_eval env u us]
      rfl

/-- enumeration of all Boolean tuples. -/
def fcons {m : Nat} (b : Bool) (v : Fin m → Bool) : Fin (m + 1) → Bool :=
  fun i => Fin.cases b v i

def boolTuples : (m : Nat) → List (Fin m → Bool)
  | 0 => [fun i => i.elim0]
  | m + 1 => (boolTuples m).flatMap (fun v => [fcons false v, fcons true v])

theorem fcons_self {m : Nat} (y : Fin (m + 1) → Bool) :
    fcons (y 0) (fun i => y i.succ) = y := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [fcons]

theorem mem_boolTuples : ∀ {m : Nat} (y : Fin m → Bool), y ∈ boolTuples m
  | 0, y => by
      have hy : y = fun i => i.elim0 := funext (fun i => i.elim0)
      rw [hy]
      simp [boolTuples]
  | m + 1, y => by
      have hmem := mem_boolTuples (fun i => y i.succ)
      rw [← fcons_self y]
      refine List.mem_flatMap.mpr ⟨fun i => y i.succ, hmem, ?_⟩
      cases h0 : y 0 <;> simp [h0]

/-- the crown DNF term of a face map. -/
def crownTerm {n : Nat} (h : (Fin (n + 1) → Bool) → Bool) : CTerm (n + 1) :=
  match (boolTuples (n + 1)).filter h with
  | [] => .proj 0
  | t :: ts => bigJoinT (minterm t) (ts.map minterm)

/-- ★ crown sufficiency: every self-dual face map is realized by its DNF
    term. -/
theorem crown_sufficiency {n : Nat} (h : (Fin (n + 1) → Bool) → Bool)
    (hsd : SelfDual h) : CRealizes (crownTerm h) h := by
  intro z
  -- h attains the value true
  have hattain : ∃ y, h y = true := by
    by_cases hz0 : h z = true
    · exact ⟨z, hz0⟩
    · refine ⟨fun i => !(z i), ?_⟩
      rw [hsd z]
      cases hz : h z
      · rfl
      · exact absurd hz hz0
  -- the filtered list is nonempty
  unfold crownTerm
  split
  · next hfilt =>
      exfalso
      obtain ⟨y, hy⟩ := hattain
      have : y ∈ (boolTuples (n + 1)).filter h :=
        List.mem_filter.mpr ⟨mem_boolTuples y, hy⟩
      rw [hfilt] at this
      cases this
  · next t ts hfilt =>
      -- facts about members of the filtered list
      have hmemf : ∀ y, y ∈ t :: ts → h y = true := by
        intro y hy
        rw [← hfilt] at hy
        exact (List.mem_filter.mp hy).2
      have hcomplete : ∀ y, h y = true → y ∈ t :: ts := by
        intro y hy
        rw [← hfilt]
        exact List.mem_filter.mpr ⟨mem_boolTuples y, hy⟩
      rw [bigJoinT_eval, List.map_map]
      cases hz : h z
      · -- h z = false: the anti-point is in the list; all values FAL/UNK
        have hanti : (fun i => !(z i)) ∈ t :: ts := by
          refine hcomplete _ ?_
          rw [hsd z, hz]
          rfl
        have hclass : ∀ y, y ∈ t :: ts →
            ceval (minterm y) (faceEnv z) = FALd ∨
            ceval (minterm y) (faceEnv z) = UNK := by
          intro y hy
          rcases meetVal_cases (z 0 == y 0)
              (((List.finRange n).map Fin.succ).map (fun j => z j == y j))
            with hT | hF | hU
          · exfalso
            have := minterm_TRUd_inv y z (by rw [minterm_eval]; exact hT)
            subst this
            rw [hmemf z hy] at hz
            cases hz
          · exact Or.inl (by rw [minterm_eval]; exact hF)
          · exact Or.inr (by rw [minterm_eval]; exact hU)
        have hanti_eval : ceval (minterm (fun i => !(z i))) (faceEnv z) = FALd := by
          have h1 := minterm_anti (fun i => !(z i))
          have h2 : (fun i => !((fun i => !(z i)) i)) = z := by
            funext i
            simp
          rw [h2] at h1
          exact h1
        have hFALdmem : ceval (minterm t) (faceEnv z) = FALd ∨
            FALd ∈ ts.map (fun u => ceval (minterm u) (faceEnv z)) := by
          rcases List.mem_cons.mp hanti with heq | hmem
          · left
            rw [← heq]
            exact hanti_eval
          · right
            exact List.mem_map.mpr ⟨fun i => !(z i), hmem, hanti_eval⟩
        show foldJ (ceval (minterm t) (faceEnv z))
          (ts.map (fun u => ceval (minterm u) (faceEnv z))) = FALd
        exact foldJ_FU (ceval (minterm t) (faceEnv z))
          (ts.map (fun u => ceval (minterm u) (faceEnv z)))
          (hclass t (by simp))
          (by
            intro w hw
            rcases List.mem_map.mp hw with ⟨u, hu, rfl⟩
            exact hclass u (by simp [hu]))
          hFALdmem
      · -- h z = true: z is in the list; all values TRU/UNK
        have hself : z ∈ t :: ts := hcomplete z hz
        have hclass : ∀ y, y ∈ t :: ts →
            ceval (minterm y) (faceEnv z) = TRUd ∨
            ceval (minterm y) (faceEnv z) = UNK := by
          intro y hy
          rcases meetVal_cases (z 0 == y 0)
              (((List.finRange n).map Fin.succ).map (fun j => z j == y j))
            with hT | hF | hU
          · exact Or.inl (by rw [minterm_eval]; exact hT)
          · exfalso
            have := minterm_FALd_inv y z (by rw [minterm_eval]; exact hF)
            -- z = ¬y, so h z = h(¬y) = ¬h y = false, contradiction
            have hy' : h z = false := by
              rw [this, hsd y, hmemf y hy]
              rfl
            rw [hz] at hy'
            cases hy'
          · exact Or.inr (by rw [minterm_eval]; exact hU)
        have hTRUdmem : ceval (minterm t) (faceEnv z) = TRUd ∨
            TRUd ∈ ts.map (fun u => ceval (minterm u) (faceEnv z)) := by
          rcases List.mem_cons.mp hself with heq | hmem
          · left
            rw [← heq]
            exact minterm_self z
          · right
            exact List.mem_map.mpr ⟨z, hmem, minterm_self z⟩
        show foldJ (ceval (minterm t) (faceEnv z))
          (ts.map (fun u => ceval (minterm u) (faceEnv z))) = TRUd
        exact foldJ_TU (ceval (minterm t) (faceEnv z))
          (ts.map (fun u => ceval (minterm u) (faceEnv z)))
          (hclass t (by simp))
          (by
            intro w hw
            rcases List.mem_map.mp hw with ⟨u, hu, rfl⟩
            exact hclass u (by simp [hu]))
          hTRUdmem

/-! ### the count bijection -/

/-- restriction of a face map to the first-coordinate-TRU representatives. -/
def restrictRep {n : Nat} (h : (Fin (n + 1) → Bool) → Bool) :
    (Fin n → Bool) → Bool :=
  fun v => h (fcons true v)

/-- equivariant extension of a free assignment on representatives. -/
def extendSD {n : Nat} (g : (Fin n → Bool) → Bool) :
    (Fin (n + 1) → Bool) → Bool :=
  fun y => if y 0 then g (fun i => y i.succ) else !(g (fun i => !(y i.succ)))

theorem extendSD_selfDual {n : Nat} (g : (Fin n → Bool) → Bool) :
    SelfDual (extendSD g) := by
  intro y
  unfold extendSD
  cases h0 : y 0 <;> simp [h0]

theorem restrictRep_extendSD {n : Nat} (g : (Fin n → Bool) → Bool) :
    restrictRep (extendSD g) = g := by
  funext v
  unfold restrictRep extendSD fcons
  simp

theorem extendSD_restrictRep {n : Nat} (h : (Fin (n + 1) → Bool) → Bool)
    (hsd : SelfDual h) : extendSD (restrictRep h) = h := by
  funext y
  unfold extendSD restrictRep
  cases h0 : y 0
  · -- y 0 = false: use self-duality at ¬y
    simp only [Bool.false_eq_true, if_false]
    have hdual := hsd (fun i => !(y i))
    have hyy : (fun i => !(!(y i))) = y := by
      funext i
      cases y i <;> rfl
    rw [hyy] at hdual
    -- hdual : h y = !(h (fun i => !(y i)))
    have hfc : fcons true (fun i => !(y i.succ)) = fun i => !(y i) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · show true = !(y 0)
        rw [h0]
        rfl
      · intro j
        simp [fcons]
    rw [hfc, hdual]
  · simp only [if_true]
    have hfc : fcons true (fun i => y i.succ) = y := by
      funext i
      refine Fin.cases ?_ ?_ i
      · show true = y 0
        rw [h0]
      · intro j
        simp [fcons]
    rw [hfc]

/-! ### calibration: majority in, AND out -/

def maj3 (y : Fin 3 → Bool) : Bool :=
  (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)

/-- the explicit majority term of the note (agreement detectors + routing). -/
def majTerm : CTerm 3 :=
  let x1 : CTerm 3 := .proj 0
  let x2 : CTerm 3 := .proj 1
  let x3 : CTerm 3 := .proj 2
  let dsame : CTerm 3 → CTerm 3 → CTerm 3 :=
    fun a b => .tjoin (.tmeet a b) (.tmeet (.tP a) (.tP b))
  let dopp : CTerm 3 → CTerm 3 → CTerm 3 := fun a b => dsame a (.tP b)
  let iplus := .tjoin (dsame x1 x2) (dsame x1 x3)
  let iminus := .tmeet (dopp x1 x2) (dopp x1 x3)
  .tjoin (.tmeet x1 iplus) (.tmeet (.tP x1) iminus)

theorem maj3_check :
    ((boolTuples 3).all
      (fun y => decide (ceval majTerm (faceEnv y) = boolToR (maj3 y)))) = true := by
  decide

/-- ★ ternary majority lies in the crown, via the explicit routing term. -/
theorem maj3_realized : CRealizes majTerm maj3 := by
  intro y
  have := List.all_eq_true.mp maj3_check y (mem_boolTuples y)
  exact of_decide_eq_true this

/-- AND is not self-dual (hence not in the crown, by crown_necessity). -/
theorem and2_not_selfDual : ¬ SelfDual (fun y : Fin 2 → Bool => y 0 && y 1) := by
  intro hsd
  have := hsd (fun i => i.val == 0)
  revert this
  decide

/-! ### one-constant completion -/

/-- the self-dualization of an arbitrary face map with one guard variable
    (guard designed for the FAL constant: the guard-FAL branch is g). -/
def sdGuard {n : Nat} (g : (Fin n → Bool) → Bool) :
    (Fin (n + 1) → Bool) → Bool :=
  fun y => if y 0 then !(g (fun i => !(y i.succ))) else g (fun i => y i.succ)

theorem sdGuard_selfDual {n : Nat} (g : (Fin n → Bool) → Bool) :
    SelfDual (sdGuard g) := by
  intro y
  unfold sdGuard
  cases h0 : y 0 <;> simp [h0]

/-- ★ guard specialization: at guard FAL the self-dualization computes g. -/
theorem sdGuard_spec {n : Nat} (g : (Fin n → Bool) → Bool) (v : Fin n → Bool) :
    sdGuard g (fcons false v) = g v := by
  unfold sdGuard fcons
  simp

/-- ★ one-constant completion, term form: for every face map g there is a
    closed-core term of arity n+2 whose restriction, with the guard slot
    held at FAL, computes g. -/
theorem one_constant_completion {n : Nat} (g : (Fin (n + 1) → Bool) → Bool) :
    ∃ t : CTerm (n + 2), ∀ v : Fin (n + 1) → Bool,
      ceval t (faceEnv (fcons false v)) = boolToR (g v) := by
  refine ⟨crownTerm (sdGuard g), ?_⟩
  intro v
  rw [crown_sufficiency (sdGuard g) (sdGuard_selfDual g) (fcons false v),
    sdGuard_spec]

end Wcy2
