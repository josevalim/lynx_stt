module

public import Erlang.program
public import Levels

@[expose] public section

namespace Elixir.STTDescrProofsTest.USort
open Lynx

/-! Abstract layer for `lists:usort/1` and `lists:ukeysort/2`: lists are compared by the
first element of each key (`lk`), and the merge states of OTP's merge sorts are described by
which sources remain and how they relate to the accumulated output. -/

theorem c_swap {a b : Term} : Term.compare (Term.fuel b a) b a = (Term.compare (Term.fuel a b) a b).swap :=
  Lynx.Term.compare_swap b a

theorem c_eq_symm {a b : Term} (h : Term.compare (Term.fuel a b) a b = .eq) : Term.compare (Term.fuel b a) b a = .eq :=
  Lynx.Term.compare_eq_symm h

theorem c_gt_of_lt {a b : Term} (h : Term.compare (Term.fuel a b) a b = .lt) : Term.compare (Term.fuel b a) b a = .gt :=
  Lynx.Term.compare_gt_of_lt h

theorem c_lt_of_gt {a b : Term} (h : Term.compare (Term.fuel a b) a b = .gt) : Term.compare (Term.fuel b a) b a = .lt :=
  Lynx.Term.compare_lt_of_gt h

theorem c_lt_trans {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .lt) (h₂ : Term.compare (Term.fuel b c) b c = .lt) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_trans h₁ h₂

theorem c_eq_trans {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .eq) (h₂ : Term.compare (Term.fuel b c) b c = .eq) :
    Term.compare (Term.fuel a c) a c = .eq := Lynx.Term.compare_eq_trans h₁ h₂

theorem c_lt_eq {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .lt) (h₂ : Term.compare (Term.fuel b c) b c = .eq) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_of_lt_of_eq h₁ h₂

theorem c_eq_lt {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .eq) (h₂ : Term.compare (Term.fuel b c) b c = .lt) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_of_eq_of_lt h₁ h₂

theorem c_lt_le {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .lt) (h₂ : (Term.compare (Term.fuel b c) b c).isLE) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_of_lt_of_isLE h₁ h₂

theorem c_le_lt {a b c : Term} (h₁ : (Term.compare (Term.fuel a b) a b).isLE) (h₂ : Term.compare (Term.fuel b c) b c = .lt) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_of_isLE_of_lt h₁ h₂

theorem c_le_iff {a b : Term} : (Term.compare (Term.fuel a b) a b).isLE ↔ Term.compare (Term.fuel a b) a b ≠ .gt := by
  cases Term.compare (Term.fuel a b) a b <;> simp

theorem c_eq_ne_lt {a b : Term} (h : Term.compare (Term.fuel a b) a b = .eq) : Term.compare (Term.fuel a b) a b ≠ .lt := by
  simp [h]

section
variable (κ : Term → Term)

/-- The first element of `l` whose key compares equal to `s`. -/
def lk (s : Term) : List Term → Option Term
  | [] => none
  | x :: xs => if Term.compare (Term.fuel (κ x) s) (κ x) s = .eq then some x else lk s xs

/-- Two lists agree on the first element of every key. -/
def Eqv (A B : List Term) : Prop := ∀ s, lk κ s A = lk κ s B

/-- Strictly ascending keys. -/
def SA (l : List Term) : Prop := l.Pairwise (fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) = .lt)

/-- Strictly descending keys. -/
def SD (l : List Term) : Prop := l.Pairwise (fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) = .gt)

variable {κ}

@[simp] theorem lk_nil (s : Term) : lk κ s [] = none := rfl

theorem lk_cons (s x : Term) (xs : List Term) :
    lk κ s (x :: xs) = if Term.compare (Term.fuel (κ x) s) (κ x) s = .eq then some x else lk κ s xs := rfl

theorem lk_append (s : Term) (A B : List Term) : lk κ s (A ++ B) = (lk κ s A).or (lk κ s B) := by
  induction A with
  | nil => rfl
  | cons x xs ih => by_cases h : Term.compare (Term.fuel (κ x) s) (κ x) s = .eq <;> simp [lk_cons, h, ih]

theorem lk_none {s : Term} {A : List Term} (h : ∀ x ∈ A, Term.compare (Term.fuel (κ x) s) (κ x) s ≠ .eq) :
    lk κ s A = none := by
  induction A with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [lk_cons, h.1, ih h.2]

theorem lk_some {s y : Term} {A : List Term} (hy : y ∈ A) (h : Term.compare (Term.fuel (κ y) s) (κ y) s = .eq) :
    ∃ z, lk κ s A = some z := by
  induction A with
  | nil => simp at hy
  | cons x xs ih =>
    by_cases hx : Term.compare (Term.fuel (κ x) s) (κ x) s = .eq
    · exact ⟨x, by simp [lk_cons, hx]⟩
    · simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact absurd h hx
      · simpa [lk_cons, hx] using ih hy

theorem Eqv.refl (A : List Term) : Eqv κ A A := fun _ => rfl
theorem Eqv.symm {A B : List Term} (h : Eqv κ A B) : Eqv κ B A := fun s => (h s).symm
theorem Eqv.trans {A B C : List Term} (h₁ : Eqv κ A B) (h₂ : Eqv κ B C) : Eqv κ A C :=
  fun s => (h₁ s).trans (h₂ s)
theorem Eqv.append {A A' B B' : List Term} (h₁ : Eqv κ A A') (h₂ : Eqv κ B B') :
    Eqv κ (A ++ B) (A' ++ B') := fun s => by simp [lk_append, h₁ s, h₂ s]
theorem Eqv.cons (x : Term) {A B : List Term} (h : Eqv κ A B) : Eqv κ (x :: A) (x :: B) :=
  Eqv.append (A := [x]) (A' := [x]) (Eqv.refl _) h

/-- An element can move to the front past elements of other keys. -/
theorem eqv_move {x : Term} {A B : List Term} (h : ∀ y ∈ A, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) ≠ .eq) :
    Eqv κ (A ++ x :: B) (x :: (A ++ B)) := by
  intro s
  by_cases hx : Term.compare (Term.fuel (κ x) s) (κ x) s = .eq
  · have : lk κ s A = none := lk_none fun y hy hys => h y hy (c_eq_trans hys (c_eq_symm hx))
    simp [lk_append, lk_cons, hx, this]
  · simp [lk_append, lk_cons, hx]

/-- An element shadowed by an earlier one of the same key can be dropped. -/
theorem eqv_drop {x y : Term} {A B : List Term} (hy : y ∈ A) (h : Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .eq) :
    Eqv κ (A ++ x :: B) (A ++ B) := by
  intro s
  by_cases hx : Term.compare (Term.fuel (κ x) s) (κ x) s = .eq
  · obtain ⟨z, hz⟩ := lk_some hy (c_eq_trans h hx)
    simp [lk_append, hz]
  · simp [lk_append, lk_cons, hx]

theorem eqv_comm {A B : List Term} (h : ∀ x ∈ A, ∀ y ∈ B, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) ≠ .eq) :
    Eqv κ (A ++ B) (B ++ A) := by
  induction B generalizing A with
  | nil => simpa using Eqv.refl A
  | cons y ys ih =>
    have hy : ∀ x ∈ A, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) ≠ .eq := fun x hx => h x hx y (by simp)
    refine (eqv_move hy).trans (Eqv.cons y (ih fun x hx z hz => h x hx z (by simp [hz]))) |>.trans ?_
    simpa using Eqv.refl (y :: (ys ++ A))

theorem eqv_reverse {A : List Term} (h : A.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) :
    Eqv κ A.reverse A := by
  induction A with
  | nil => exact Eqv.refl _
  | cons x xs ih =>
    rw [List.pairwise_cons] at h
    simp only [List.reverse_cons]
    refine (Eqv.append (ih h.2) (Eqv.refl [x])).trans ?_
    have := eqv_comm (κ := κ) (A := xs) (B := [x])
      (fun y hy z hz => by simp at hz; subst hz; intro e; exact h.1 y hy (c_eq_symm e))
    simpa using this

theorem SA.ne {l : List Term} (h : SA κ l) : l.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq :=
  h.imp fun e => by simp [e]

theorem SD.ne {l : List Term} (h : SD κ l) : l.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq :=
  h.imp fun e => by simp [e]

@[simp] theorem SA_nil : SA κ [] := List.Pairwise.nil
@[simp] theorem SD_nil : SD κ [] := List.Pairwise.nil

theorem SA_cons {x : Term} {l : List Term} :
    SA κ (x :: l) ↔ (∀ y ∈ l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) ∧ SA κ l := List.pairwise_cons

theorem SD_cons {x : Term} {l : List Term} :
    SD κ (x :: l) ↔ (∀ y ∈ l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .gt) ∧ SD κ l := List.pairwise_cons

theorem SA_reverse {l : List Term} : SA κ l.reverse ↔ SD κ l := by
  simp only [SA, SD, List.pairwise_reverse]
  exact ⟨fun h => h.imp c_gt_of_lt, fun h => h.imp c_lt_of_gt⟩

theorem SD_reverse {l : List Term} : SD κ l.reverse ↔ SA κ l := by
  simp only [SA, SD, List.pairwise_reverse]
  exact ⟨fun h => h.imp c_lt_of_gt, fun h => h.imp c_gt_of_lt⟩

/-- Every element of a strictly ascending list after a lower bound of its head. -/
theorem SA.lt_all {x b : Term} {l : List Term} (s : SA κ (b :: l))
    (h : Term.compare (Term.fuel (κ x) (κ b)) (κ x) (κ b) = .lt) : ∀ y ∈ b :: l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h
  · exact c_lt_trans h ((SA_cons.1 s).1 y hy)

theorem SA.le_all {x b : Term} {l : List Term} (s : SA κ (b :: l))
    (h : (Term.compare (Term.fuel (κ x) (κ b)) (κ x) (κ b)).isLE) : ∀ y ∈ b :: l, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h
  · have := c_le_lt h ((SA_cons.1 s).1 y hy); simp [this]

theorem SD.gt_all {x b : Term} {l : List Term} (s : SD κ (b :: l))
    (h : Term.compare (Term.fuel (κ x) (κ b)) (κ x) (κ b) = .gt) : ∀ y ∈ b :: l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .gt := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h
  · exact c_gt_of_lt (c_lt_trans (c_lt_of_gt ((SD_cons.1 s).1 y hy)) (c_lt_of_gt h))

theorem SD.ge_all {x b : Term} {l : List Term} (s : SD κ (b :: l))
    (h : Term.compare (Term.fuel (κ x) (κ b)) (κ x) (κ b) ≠ .lt) : ∀ y ∈ b :: l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) ≠ .lt := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h
  · exact fun e => h (c_lt_trans e (c_lt_of_gt ((SD_cons.1 s).1 y hy)))

end

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable (κ : Term → Term) (Kd : Term → Prop)

/-! Ascending sources merged into a descending accumulator (`ukeymerge*`, `umerge*`). -/

/-- Every key of the accumulator is below `x`. -/
def Above (M : List Term) (x : Term) : Prop := ∀ m ∈ M, Term.compare (Term.fuel (κ m) (κ x)) (κ m) (κ x) = .lt

/-- `x` is above the accumulator or a duplicate of its head. -/
def Up (M : List Term) (x : Term) : Prop :=
  Above κ M x ∨ ∃ m M', M = m :: M' ∧ Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .eq

/-- The tracked head key of the accumulator; when it is empty no source key matches it. -/
def HdOK (M : List Term) (h : Term) (S : List Term) : Prop :=
  match M with
  | [] => ∀ x ∈ S, Term.compare (Term.fuel (κ x) h) (κ x) h ≠ .eq
  | m :: _ => Term.compare (Term.fuel h (κ m)) h (κ m) = .eq

structure Pre (M A B C : List Term) : Prop where
  sm : SD κ M
  sa : SA κ A
  sb : SA κ B
  sc : SA κ C
  ka : ∀ x ∈ A, Kd x
  kb : ∀ x ∈ B, Kd x
  kc : ∀ x ∈ C, Kd x
  ua : ∀ x ∈ A, Above κ M x
  ub : ∀ x ∈ B, Up κ M x
  uc : ∀ x ∈ C, Up κ M x

/-- A descending result with the contents of the state, earlier sources first. -/
def Res (M A B C R : List Term) : Prop := SD κ R ∧ Eqv κ R (M ++ A ++ B ++ C)

variable {κ Kd}

theorem above_lt {M : List Term} {x y : Term} (hx : Above κ M x)
    (h : Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) : Above κ M y :=
  fun m hm => c_lt_trans (hx m hm) h

theorem above_cons {M : List Term} {x y : Term} (hx : Above κ M x)
    (h : Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) : Above κ (x :: M) y := by
  intro m hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact h
  · exact above_lt hx h m hm

theorem up_cons {M : List Term} {x y : Term} (hx : Above κ M x)
    (h : (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE) : Up κ (x :: M) y := by
  cases e : Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)
  · exact Or.inl (above_cons hx e)
  · exact Or.inr ⟨x, M, rfl, c_eq_symm e⟩
  · simp [e] at h

theorem up_of_above {M : List Term} {x : Term} (h : Above κ M x) : Up κ M x := Or.inl h

/-- A tracked head decides whether a source element duplicates the accumulator head. -/
theorem up_split {M S : List Term} {h x : Term} (hd : HdOK κ M h S) (hx : x ∈ S)
    (u : Up κ M x) :
    (Term.compare (Term.fuel (κ x) h) (κ x) h = .eq → ∃ m M', M = m :: M' ∧ Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .eq) ∧
    (Term.compare (Term.fuel (κ x) h) (κ x) h ≠ .eq → Above κ M x) := by
  cases M with
  | nil => exact ⟨fun e => absurd e (hd x hx), fun _ m hm => by simp at hm⟩
  | cons m M' =>
    simp only [HdOK] at hd
    refine ⟨fun e => ⟨m, M', rfl, c_eq_trans e hd⟩, fun ne => ?_⟩
    rcases u with u | ⟨m', M'', e, u⟩
    · exact u
    · cases e; exact absurd (c_eq_trans u (c_eq_symm hd)) ne

theorem hd_self {M S : List Term} {x : Term} : HdOK κ (x :: M) (κ x) S := by
  simp [HdOK]

theorem eqv_mid {M A : List Term} {x : Term} (hm : Above κ M x)
    (ha : ∀ y ∈ A, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) (B' : List Term) :
    Eqv κ (x :: M ++ A ++ B') (M ++ A ++ x :: B') := by
  have := eqv_move (κ := κ) (x := x) (A := M ++ A) (B := B') (by
    intro y hy e
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · exact absurd (hm y hy) (by simp [e])
    · have := ha y hy; rw [c_swap, e] at this; simp at this)
  simpa using this.symm

theorem pushA {M A B C : List Term} {x : Term} (p : Pre κ Kd M (x :: A) B C)
    (hb : ∀ y ∈ B.head?, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE)
    (hc : ∀ y ∈ C.head?, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE) :
    Pre κ Kd (x :: M) A B C ∧ ∀ R, Res κ (x :: M) A B C R → Res κ M (x :: A) B C R := by
  have hx : Above κ M x := p.ua x (by simp)
  have sa := SA_cons.1 p.sa
  have le_all : ∀ {S : List Term}, SA κ S → (∀ y ∈ S.head?, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE) →
      ∀ y ∈ S, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE := by
    intro S s h y hy
    cases S with
    | nil => simp at hy
    | cons b S => exact SA.le_all s (h b (by simp)) y hy
  refine ⟨⟨SD_cons.2 ⟨fun m hm => c_gt_of_lt (hx m hm), p.sm⟩, sa.2, p.sb, p.sc,
    fun y hy => p.ka y (by simp [hy]), p.kb, p.kc,
    fun y hy => above_cons hx (sa.1 y hy),
    fun y hy => up_cons hx (le_all p.sb hb y hy),
    fun y hy => up_cons hx (le_all p.sc hc y hy)⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  simpa using eqv_mid (A := []) hx (fun _ h => by simp at h) (A ++ B ++ C)

theorem pushB {M A B C : List Term} {x : Term} (p : Pre κ Kd M A (x :: B) C) (hx : Above κ M x)
    (ha : ∀ y ∈ A.head?, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt)
    (hc : ∀ y ∈ C.head?, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE) :
    Pre κ Kd (x :: M) A B C ∧ ∀ R, Res κ (x :: M) A B C R → Res κ M A (x :: B) C R := by
  have sb := SA_cons.1 p.sb
  have lt_a : ∀ y ∈ A, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt := by
    intro y hy
    cases A with
    | nil => simp at hy
    | cons b A => exact SA.lt_all p.sa (ha b (by simp)) y hy
  have le_c : ∀ y ∈ C, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE := by
    intro y hy
    cases C with
    | nil => simp at hy
    | cons b C => exact SA.le_all p.sc (hc b (by simp)) y hy
  refine ⟨⟨SD_cons.2 ⟨fun m hm => c_gt_of_lt (hx m hm), p.sm⟩, p.sa, sb.2, p.sc,
    p.ka, fun y hy => p.kb y (by simp [hy]), p.kc,
    fun y hy => above_cons hx (lt_a y hy),
    fun y hy => up_of_above (above_cons hx (sb.1 y hy)),
    fun y hy => up_cons hx (le_c y hy)⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  simpa using eqv_mid hx lt_a (B ++ C)

theorem pushC {M A B C : List Term} {x : Term} (p : Pre κ Kd M A B (x :: C)) (hx : Above κ M x)
    (ha : ∀ y ∈ A.head?, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt)
    (hb : ∀ y ∈ B.head?, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) :
    Pre κ Kd (x :: M) A B C ∧ ∀ R, Res κ (x :: M) A B C R → Res κ M A B (x :: C) R := by
  have sc := SA_cons.1 p.sc
  have lt_all : ∀ {S : List Term}, SA κ S → (∀ y ∈ S.head?, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) →
      ∀ y ∈ S, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt := by
    intro S s h y hy
    cases S with
    | nil => simp at hy
    | cons b S => exact SA.lt_all s (h b (by simp)) y hy
  refine ⟨⟨SD_cons.2 ⟨fun m hm => c_gt_of_lt (hx m hm), p.sm⟩, p.sa, p.sb, sc.2,
    p.ka, p.kb, fun y hy => p.kc y (by simp [hy]),
    fun y hy => above_cons hx (lt_all p.sa ha y hy),
    fun y hy => up_of_above (above_cons hx (lt_all p.sb hb y hy)),
    fun y hy => up_of_above (above_cons hx (sc.1 y hy))⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_mid (A := A ++ B) hx (fun y hy => by
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · exact lt_all p.sa ha y hy
    · exact lt_all p.sb hb y hy) C
  simpa using this

theorem dropB {M A B C : List Term} {x : Term} (p : Pre κ Kd M A (x :: B) C)
    (hd : ∃ m M', M = m :: M' ∧ Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .eq) :
    Pre κ Kd M A B C ∧ (∀ y ∈ B, Above κ M y) ∧
      ∀ R, Res κ M A B C R → Res κ M A (x :: B) C R := by
  have sb := SA_cons.1 p.sb
  obtain ⟨m, M', rfl, e⟩ := hd
  have ab : ∀ y ∈ B, Above κ (m :: M') y := by
    intro y hy m' hm'
    have hmx : (Term.compare (Term.fuel (κ m') (κ x)) (κ m') (κ x)).isLE := by
      simp only [List.mem_cons] at hm'
      rcases hm' with rfl | hm'
      · simp [c_eq_symm e]
      · have := (SD_cons.1 p.sm).1 m' hm'
        have := c_lt_eq (c_lt_of_gt this) (c_eq_symm e); simp [this]
    exact c_le_lt hmx (sb.1 y hy)
  refine ⟨⟨p.sm, p.sa, sb.2, p.sc, p.ka, fun y hy => p.kb y (by simp [hy]), p.kc, p.ua,
    fun y hy => up_of_above (ab y hy), p.uc⟩, ab, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_drop (κ := κ) (A := m :: M' ++ A) (B := B ++ C) (x := x) (y := m) (by simp)
    (c_eq_symm e)
  simpa using this.symm

theorem dropC {M A B C : List Term} {x : Term} (p : Pre κ Kd M A B (x :: C))
    (hd : ∃ m M', M = m :: M' ∧ Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .eq) :
    Pre κ Kd M A B C ∧ (∀ y ∈ C, Above κ M y) ∧
      ∀ R, Res κ M A B C R → Res κ M A B (x :: C) R := by
  have sc := SA_cons.1 p.sc
  obtain ⟨m, M', rfl, e⟩ := hd
  have ac : ∀ y ∈ C, Above κ (m :: M') y := by
    intro y hy m' hm'
    have hmx : (Term.compare (Term.fuel (κ m') (κ x)) (κ m') (κ x)).isLE := by
      simp only [List.mem_cons] at hm'
      rcases hm' with rfl | hm'
      · simp [c_eq_symm e]
      · have := (SD_cons.1 p.sm).1 m' hm'
        have := c_lt_eq (c_lt_of_gt this) (c_eq_symm e); simp [this]
    exact c_le_lt hmx (sc.1 y hy)
  refine ⟨⟨p.sm, p.sa, p.sb, sc.2, p.ka, p.kb, fun y hy => p.kc y (by simp [hy]), p.ua, p.ub,
    fun y hy => up_of_above (ac y hy)⟩, ac, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_drop (κ := κ) (A := m :: M' ++ A ++ B) (B := C) (x := x) (y := m) (by simp)
    (c_eq_symm e)
  simpa using this.symm

theorem res_congr {M A B C M' A' B' C' R : List Term}
    (h : M ++ A ++ B ++ C = M' ++ A' ++ B' ++ C') (r : Res κ M A B C R) : Res κ M' A' B' C' R :=
  ⟨r.1, h ▸ r.2⟩

/-- Reversing the last source onto the accumulator. -/
theorem finish {M T : List Term} (sm : SD κ M) (st : SA κ T) (ht : ∀ y ∈ T, Above κ M y) :
    SD κ (T.reverse ++ M) ∧ Eqv κ (T.reverse ++ M) (M ++ T) := by
  refine ⟨?_, ?_⟩
  · simp only [SD, List.pairwise_append]
    refine ⟨SD_reverse.2 st, sm, fun a ha m hm => c_gt_of_lt (ht a (by simpa using ha) m hm)⟩
  · refine (Eqv.append (eqv_reverse st.ne) (Eqv.refl M)).trans (eqv_comm ?_)
    intro a ha m hm e
    have := ht a ha m hm; rw [c_swap, e] at this; simp at this

/-! Descending sources merged into an ascending accumulator (`rukeymerge*`, `rumerge*`). -/

variable (κ Kd)

def Below (M : List Term) (x : Term) : Prop := ∀ m ∈ M, Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .lt

structure PreD (M A B C : List Term) : Prop where
  sm : SA κ M
  sa : SD κ A
  sb : SD κ B
  sc : SD κ C
  ka : ∀ x ∈ A, Kd x
  kb : ∀ x ∈ B, Kd x
  kc : ∀ x ∈ C, Kd x
  ua : ∀ x ∈ A, Below κ M x
  ub : ∀ x ∈ B, Below κ M x
  uc : ∀ x ∈ C, Below κ M x

def ResD (M A B C R : List Term) : Prop := SA κ R ∧ Eqv κ R (M ++ A ++ B ++ C)

variable {κ Kd}

theorem resD_congr {M A B C M' A' B' C' R : List Term}
    (h : M ++ A ++ B ++ C = M' ++ A' ++ B' ++ C') (r : ResD κ M A B C R) : ResD κ M' A' B' C' R :=
  ⟨r.1, h ▸ r.2⟩

theorem below_cons {M : List Term} {x y : Term} (hx : Below κ M x)
    (h : Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) : Below κ (x :: M) y := by
  intro m hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact h
  · exact c_lt_trans h (hx m hm)

theorem gt_all {S : List Term} {x : Term} (s : SD κ S)
    (h : ∀ y ∈ S.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) : ∀ y ∈ S, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt := by
  intro y hy
  cases S with
  | nil => simp at hy
  | cons b S =>
    have := SD.gt_all s (x := x) (c_gt_of_lt (h b (by simp))) y hy
    exact c_lt_of_gt this

theorem eqv_midD {M A : List Term} {x : Term} (hm : Below κ M x)
    (ha : ∀ y ∈ A, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) (B' : List Term) :
    Eqv κ (x :: M ++ A ++ B') (M ++ A ++ x :: B') := by
  have := eqv_move (κ := κ) (x := x) (A := M ++ A) (B := B') (by
    intro y hy e
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · have := hm y hy; rw [c_swap, e] at this; simp at this
    · exact absurd (ha y hy) (by simp [e]))
  simpa using this.symm

theorem pushDA {M A B C : List Term} {x : Term} (p : PreD κ Kd M (x :: A) B C)
    (hb : ∀ y ∈ B.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt)
    (hc : ∀ y ∈ C.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) :
    PreD κ Kd (x :: M) A B C ∧ ∀ R, ResD κ (x :: M) A B C R → ResD κ M (x :: A) B C R := by
  have hx := p.ua x (by simp)
  have sa := SD_cons.1 p.sa
  refine ⟨⟨SA_cons.2 ⟨fun m hm => hx m hm, p.sm⟩, sa.2, p.sb, p.sc,
    fun y hy => p.ka y (by simp [hy]), p.kb, p.kc,
    fun y hy => below_cons hx (c_lt_of_gt (sa.1 y hy)),
    fun y hy => below_cons hx (gt_all p.sb hb y hy),
    fun y hy => below_cons hx (gt_all p.sc hc y hy)⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  simpa using eqv_midD (A := []) hx (fun _ h => by simp at h) (A ++ B ++ C)

theorem pushDB {M A B C : List Term} {x : Term} (p : PreD κ Kd M A (x :: B) C)
    (ha : ∀ y ∈ A.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt)
    (hc : ∀ y ∈ C.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) :
    PreD κ Kd (x :: M) A B C ∧ ∀ R, ResD κ (x :: M) A B C R → ResD κ M A (x :: B) C R := by
  have hx := p.ub x (by simp)
  have sb := SD_cons.1 p.sb
  have la := gt_all p.sa ha
  refine ⟨⟨SA_cons.2 ⟨fun m hm => hx m hm, p.sm⟩, p.sa, sb.2, p.sc,
    p.ka, fun y hy => p.kb y (by simp [hy]), p.kc,
    fun y hy => below_cons hx (la y hy),
    fun y hy => below_cons hx (c_lt_of_gt (sb.1 y hy)),
    fun y hy => below_cons hx (gt_all p.sc hc y hy)⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  simpa using eqv_midD hx la (B ++ C)

theorem pushDC {M A B C : List Term} {x : Term} (p : PreD κ Kd M A B (x :: C))
    (ha : ∀ y ∈ A.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt)
    (hb : ∀ y ∈ B.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) :
    PreD κ Kd (x :: M) A B C ∧ ∀ R, ResD κ (x :: M) A B C R → ResD κ M A B (x :: C) R := by
  have hx := p.uc x (by simp)
  have sc := SD_cons.1 p.sc
  have la := gt_all p.sa ha
  have lb := gt_all p.sb hb
  refine ⟨⟨SA_cons.2 ⟨fun m hm => hx m hm, p.sm⟩, p.sa, p.sb, sc.2,
    p.ka, p.kb, fun y hy => p.kc y (by simp [hy]),
    fun y hy => below_cons hx (la y hy),
    fun y hy => below_cons hx (lb y hy),
    fun y hy => below_cons hx (c_lt_of_gt (sc.1 y hy))⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_midD (A := A ++ B) hx (fun y hy => by
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · exact la y hy
    · exact lb y hy) C
  simpa using this

/-- A source head equal to the head of an earlier source is shadowed. -/
theorem dropDB {M A B C : List Term} {x a : Term} (p : PreD κ Kd M A (x :: B) C)
    (ha : a ∈ A) (e : Term.compare (Term.fuel (κ a) (κ x)) (κ a) (κ x) = .eq) :
    PreD κ Kd M A B C ∧ ∀ R, ResD κ M A B C R → ResD κ M A (x :: B) C R := by
  refine ⟨⟨p.sm, p.sa, (SD_cons.1 p.sb).2, p.sc, p.ka, fun y hy => p.kb y (by simp [hy]), p.kc,
    p.ua, fun y hy => p.ub y (by simp [hy]), p.uc⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_drop (κ := κ) (A := M ++ A) (B := B ++ C) (x := x) (y := a) (by simp [ha]) e
  simpa using this.symm

theorem dropDC {M A B C : List Term} {x a : Term} (p : PreD κ Kd M A B (x :: C))
    (ha : a ∈ A ++ B) (e : Term.compare (Term.fuel (κ a) (κ x)) (κ a) (κ x) = .eq) :
    PreD κ Kd M A B C ∧ ∀ R, ResD κ M A B C R → ResD κ M A B (x :: C) R := by
  refine ⟨⟨p.sm, p.sa, p.sb, (SD_cons.1 p.sc).2, p.ka, p.kb, fun y hy => p.kc y (by simp [hy]),
    p.ua, p.ub, fun y hy => p.uc y (by simp [hy])⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_drop (κ := κ) (A := M ++ A ++ B) (B := C) (x := x) (y := a)
    (by simp only [List.mem_append] at ha ⊢; rcases ha with ha | ha <;> simp [ha]) e
  simpa using this.symm

theorem finishD {M T : List Term} (sm : SA κ M) (st : SD κ T) (ht : ∀ y ∈ T, Below κ M y) :
    SA κ (T.reverse ++ M) ∧ Eqv κ (T.reverse ++ M) (M ++ T) := by
  refine ⟨?_, ?_⟩
  · simp only [SA, List.pairwise_append]
    refine ⟨SA_reverse.2 st, sm, fun a ha m hm => ht a (by simpa using ha) m hm⟩
  · refine (Eqv.append (eqv_reverse st.ne) (Eqv.refl M)).trans (eqv_comm ?_)
    intro a ha m hm e
    exact absurd (ht a ha m hm) (by simp [e])

end

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem g_if {α : Type} (p : Prop) [Decidable p] (body next : Unit → Except Exception α) :
    Lynx.Except.guard (.ok (if p then Term.atom "true" else Term.atom "false")) body next =
      if p then body () else next () := by
  by_cases h : p <;> simp [h]

theorem eq_ok (a b : Term) : Erlang.erlang.«==/2» a b =
    .ok (if Term.compare (Term.fuel a b) a b = .eq then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«==/2»]

theorem le_ok (a b : Term) : Erlang.erlang.«=</2» a b =
    .ok (if (Term.compare (Term.fuel a b) a b).isLE = true then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«=</2»]

theorem lt_ok (a b : Term) : Erlang.erlang.«</2» a b =
    .ok (if (Term.compare (Term.fuel a b) a b).isLT = true then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«</2»]

theorem gt_ok (a b : Term) : Erlang.erlang.«>/2» a b =
    .ok (if (Term.compare (Term.fuel a b) a b).isGT = true then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«>/2»]

/-- Keyed elements of `ukeysort/2`: `element/2` yields the key, which never equals a cons. -/
def KdK (I : Term) (κ : Term → Term) (x : Term) : Prop :=
  Erlang.erlang.«element/2» I x = .ok (κ x) ∧ ∀ a b, Term.compare (Term.fuel (κ x) (.cons a b)) (κ x) (.cons a b) ≠ .eq

theorem rev2 (l : List Term) : ∀ acc : List Term,
    Erlang.lists.«reverse/2» (Term.list l) (Term.list acc) = .ok (Term.list (l.reverse ++ acc)) := by
  induction l with
  | nil => intro acc; simp [Erlang.lists.«reverse/2»]
  | cons x xs ih => intro acc; simpa [Term.list, Erlang.lists.«reverse/2»] using ih (x :: acc)

theorem not_le_lt {a b : Term} (h : ¬(Term.compare (Term.fuel a b) a b).isLE = true) : Term.compare (Term.fuel b a) b a = .lt := by
  cases e : Term.compare (Term.fuel a b) a b
  · simp [e] at h
  · simp [e] at h
  · exact c_lt_of_gt e

section
variable {κ : Term → Term} {Kd : Term → Prop}

/-- The accumulator plus one ascending source, reversed onto it. -/
theorem res_fin {M T : List Term} (sm : SD κ M) (st : SA κ T) (ht : ∀ y ∈ T, Above κ M y) :
    Res κ M T [] [] (T.reverse ++ M) := by
  obtain ⟨s, e⟩ := finish sm st ht; exact ⟨s, by simpa using e⟩

theorem resD_fin {M T : List Term} (sm : SA κ M) (st : SD κ T) (ht : ∀ y ∈ T, Below κ M y) :
    ResD κ M T [] [] (T.reverse ++ M) := by
  obtain ⟨s, e⟩ := finishD sm st ht; exact ⟨s, by simpa using e⟩

end

section
variable {I : Term} {κ : Term → Term}

theorem ukm2 (n : Nat) :
    (∀ T1 T2 M H2 HdM, List.length T1 + List.length T2 + 1 ≤ n → Pre κ (KdK I κ) M T1 (H2 :: T2) [] →
      HdOK κ M HdM (H2 :: T2) →
      ∃ R, Erlang.lists.«ukeymerge2_1/7» I (Term.list T1) (κ H2) HdM (Term.list T2) (Term.list M) H2 =
        .ok (Term.list R) ∧ Res κ M T1 (H2 :: T2) [] R) ∧
    (∀ T1 H1 T2 M, List.length T1 + 1 + List.length T2 ≤ n → Pre κ (KdK I κ) M (H1 :: T1) T2 [] →
      (∀ y ∈ T2, Above κ M y) →
      ∃ R, Erlang.lists.«ukeymerge2_2/6» I (Term.list T1) (κ H1) H1 (Term.list T2) (Term.list M) =
        .ok (Term.list R) ∧ Res κ M (H1 :: T1) T2 [] R) := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩
  | succ n ih =>
  constructor
  · intro T1 T2 M H2 HdM len p hd
    have u2 := up_split hd (by simp) (p.ub H2 (by simp))
    cases T1 with
    | nil =>
      rw [Erlang.lists.«ukeymerge2_1/7».eq_def]
      simp only [eq_ok, g_if]
      by_cases c2 : Term.compare (Term.fuel (κ H2) HdM) (κ H2) HdM = .eq
      · obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        refine ⟨_, by simp only [c2, ite_true, rev2], tr _ (res_congr (by simp) (res_fin p'.sm p'.sb ab))⟩
      · obtain ⟨p', tr⟩ := pushB p (u2.2 c2) (by simp) (by simp)
        refine ⟨_, by simpa [c2] using rev2 T2 (H2 :: M), tr _ (res_congr (by simp)
          (res_fin p'.sm p'.sb fun y hy => above_cons (u2.2 c2) ((SA_cons.1 p.sb).1 y hy)))⟩
    | cons H1 T1 =>
      have k1 := (p.ka H1 (by simp)).1
      rw [Erlang.lists.«ukeymerge2_1/7».eq_def]
      simp only [k1, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c1 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c1, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.1 T1 T2 (H1 :: M) H2 (κ H1) (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      · simp only [c1]
        have c1' := not_le_lt c1
        by_cases c2 : Term.compare (Term.fuel (κ H2) HdM) (κ H2) HdM = .eq
        · simp only [c2, ↓reduceIte]
          obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
          obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 M (by simp at len; omega) p' ab
          exact ⟨R, run, tr R res⟩
        · simp only [c2, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushB p (u2.2 c2) (by simpa using c1') (by simp)
          obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
            (fun y hy => above_cons (u2.2 c2) ((SA_cons.1 p.sb).1 y hy))
          exact ⟨R, by simpa using run, tr R res⟩
  · intro T1 H1 T2 M len p ab
    cases T2 with
    | nil =>
      rw [Erlang.lists.«ukeymerge2_2/6».eq_def]
      obtain ⟨p', tr⟩ := pushA p (by simp) (by simp)
      refine ⟨_, by simpa using rev2 T1 (H1 :: M), tr _ (res_fin p'.sm p'.sa p'.ua)⟩
    | cons H2 T2 =>
      have k2 := (p.kb H2 (by simp)).1
      rw [Erlang.lists.«ukeymerge2_2/6».eq_def]
      simp only [k2, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c1 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c1, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.1 T1 T2 (H1 :: M) H2 (κ H1) (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      · simp only [c1]
        have hx := ab H2 (by simp)
        obtain ⟨p', tr⟩ := pushB p hx (by simpa using not_le_lt c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
          (fun y hy => above_cons hx ((SA_cons.1 p.sb).1 y hy))
        exact ⟨R, by simpa using run, tr R res⟩

end

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term} {Kd : Term → Prop}

theorem hd_sub {M S S' : List Term} {h : Term} (hd : HdOK κ M h S) (sub : ∀ x ∈ S', x ∈ S) :
    HdOK κ M h S' := by
  cases M with
  | nil => exact fun x hx => hd x (sub x hx)
  | cons m M => exact hd

theorem pre_BC {M B C : List Term} (p : Pre κ Kd M [] B C) (ab : ∀ y ∈ B, Above κ M y) :
    Pre κ Kd M B C [] :=
  ⟨p.sm, p.sb, p.sc, SA_nil, p.kb, p.kc, fun _ h => by simp at h, ab, p.uc, fun _ h => by simp at h⟩

theorem pre_AC {M A C : List Term} (p : Pre κ Kd M A [] C) : Pre κ Kd M A C [] :=
  ⟨p.sm, p.sa, p.sc, SA_nil, p.ka, p.kc, fun _ h => by simp at h, p.ua, p.uc, fun _ h => by simp at h⟩

theorem above_all {M B : List Term} {x : Term} (s : SA κ (x :: B)) (hx : Above κ M x) :
    ∀ y ∈ x :: B, Above κ M y := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact above_lt hx ((SA_cons.1 s).1 y hy)

theorem above_tail {M B : List Term} {x : Term} (s : SA κ (x :: B)) (hx : Above κ M x) :
    ∀ y ∈ B, Above κ (x :: M) y :=
  fun y hy => above_cons hx ((SA_cons.1 s).1 y hy)

end

section
variable {I : Term} {κ : Term → Term}

theorem ukm3 (n : Nat) :
    (∀ T1 T2 T3 M H2 H3 HdM D, List.length T1 + List.length T2 + List.length T3 + 2 ≤ n →
      (Pre κ (KdK I κ)) M T1 (H2 :: T2) (H3 :: T3) → HdOK κ M HdM (H2 :: T2 ++ H3 :: T3) →
      ∃ R, Erlang.lists.«ukeymerge3_1/11» I (Term.list T1) D HdM (κ H2) H2 (Term.list T2) (Term.list M)
        (κ H3) H3 (Term.list T3) = .ok (Term.list R) ∧ Res κ M T1 (H2 :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 T2 H3 T3 M HdM D, List.length T1 + List.length T2 + List.length T3 + 2 ≤ n →
      (Pre κ (KdK I κ)) M (H1 :: T1) T2 (H3 :: T3) → (∀ y ∈ T2, Above κ M y) → HdOK κ M HdM (H3 :: T3) →
      ∃ R, Erlang.lists.«ukeymerge3_2/11» I (κ H1) (Term.list T1) H1 (Term.list T2) HdM D (Term.list M)
        (κ H3) H3 (Term.list T3) = .ok (Term.list R) ∧ Res κ M (H1 :: T1) T2 (H3 :: T3) R) ∧
    (∀ H1 T1 H2 T2 T3 M, List.length T1 + List.length T2 + List.length T3 + 2 ≤ n →
      (Pre κ (KdK I κ)) M (H1 :: T1) (H2 :: T2) T3 → (∀ y ∈ H2 :: T2, Above κ M y) → (∀ y ∈ T3, Above κ M y) →
      (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE →
      ∃ R, Erlang.lists.«ukeymerge3_12_3/9» I (κ H1) (Term.list T1) H1 (κ H2) H2 (Term.list T2)
        (Term.list M) (Term.list T3) = .ok (Term.list R) ∧ Res κ M (H1 :: T1) (H2 :: T2) T3 R) ∧
    (∀ H1 T1 H2 T2 T3 M, List.length T1 + List.length T2 + List.length T3 + 2 ≤ n →
      (Pre κ (KdK I κ)) M (H1 :: T1) (H2 :: T2) T3 → (∀ y ∈ H2 :: T2, Above κ M y) → (∀ y ∈ T3, Above κ M y) →
      Term.compare (Term.fuel (κ H2) (κ H1)) (κ H2) (κ H1) = .lt →
      ∃ R, Erlang.lists.«ukeymerge3_21_3/9» I (κ H1) (Term.list T1) H1 (κ H2) H2 (Term.list T2)
        (Term.list M) (Term.list T3) = .ok (Term.list R) ∧ Res κ M (H1 :: T1) (H2 :: T2) T3 R) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2, ih12, ih21⟩ := ih
  have m2 := ukm2 (I := I) (κ := κ) n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ukeymerge3_1
    intro T1 T2 T3 M H2 H3 HdM D len p hd
    have u2 := up_split hd (by simp) (p.ub H2 (by simp))
    have u3 := up_split hd (by simp) (p.uc H3 (by simp))
    rw [Erlang.lists.«ukeymerge3_1/11».eq_def]
    cases T1 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases c2 : Term.compare (Term.fuel (κ H2) HdM) (κ H2) HdM = .eq
      · simp only [c2, ↓reduceIte]
        obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        obtain ⟨R, run, res⟩ := m2.1 T2 T3 M H3 HdM (by simp at len; omega) (pre_BC p' ab)
          (hd_sub hd fun a ha => List.mem_append_right _ ha)
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c2, ↓reduceIte]
      have a2 := u2.2 c2
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simp) (by simpa using c23)
        obtain ⟨R, run, res⟩ := m2.1 T2 T3 (H2 :: M) H3 (κ H2) (by simp at len; omega)
          (pre_BC p' (above_tail p.sb a2)) hd_self
        exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
      simp only [c23]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := m2.2 T2 H2 T3 M (by simp at len; omega)
          (pre_BC p' (above_all p.sb a2)) ac
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simp) (by simpa using c32)
      obtain ⟨R, run, res⟩ := m2.2 T2 H2 T3 (H3 :: M) (by simp at len; omega)
        (pre_BC p' (above_all p.sb (above_cons a3 c32))) (above_tail p.sc a3)
      exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
    | cons H1 T1 =>
      have k1 := (p.ka H1 (by simp)).1
      have a1 := p.ua H1 (by simp)
      simp only [k1, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
        · simp only [c13, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
          obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 (κ H1) D (by simp at len; omega) p' hd_self
          exact ⟨R, by simpa using run, tr R res⟩
        simp only [c13]
        have c31 := not_le_lt c13
        have b2 : ∀ y ∈ H2 :: T2, Above κ M y := above_all p.sb (by
          cases e : Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)
          · exact above_lt a1 e
          · exact fun m hm => c_lt_eq (a1 m hm) e
          · simp [e] at c12)
        by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
        · simp only [c3, ↓reduceIte]
          obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 M (by simp at len; omega) p' b2 ac c12
          exact ⟨R, run, tr R res⟩
        simp only [c3, ↓reduceIte]
        have a3 := u3.2 c3
        obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
          (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c12]
      have c21 := not_le_lt c12
      by_cases c2 : Term.compare (Term.fuel (κ H2) HdM) (κ H2) HdM = .eq
      · simp only [c2, ↓reduceIte]
        obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 M HdM (Term.list T2) (by simp at len; omega) p' ab
          (hd_sub hd fun a ha => List.mem_append_right _ ha)
        exact ⟨R, run, tr R res⟩
      simp only [c2, ↓reduceIte]
      have a2 := u2.2 c2
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) (κ H2) (Term.list T2)
          (by simp at len; omega) p' (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 M (by simp at len; omega) p'
          (above_all p.sb a2) ac c21
        exact ⟨R, run, tr R res⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_2
    intro H1 T1 T2 H3 T3 M HdM D len p ab hd
    have u3 := up_split hd (by simp) (p.uc H3 (by simp))
    have a1 := p.ua H1 (by simp)
    rw [Erlang.lists.«ukeymerge3_2/11».eq_def]
    cases T2 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simp) (by simpa using c13)
        obtain ⟨R, run, res⟩ := m2.1 T1 T3 (H1 :: M) H3 (κ H1) (by simp at len; omega) (pre_AC p') hd_self
        exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
      simp only [c13]
      have c31 := not_le_lt c13
      by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := m2.2 T1 H1 T3 M (by simp at len; omega) (pre_AC p') ac
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simp)
      obtain ⟨R, run, res⟩ := m2.2 T1 H1 T3 (H3 :: M) (by simp at len; omega) (pre_AC p')
        (above_tail p.sc a3)
      exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
    | cons H2 T2 =>
      have k2 := (p.kb H2 (by simp)).1
      have a2 := ab H2 (by simp)
      simp only [k2, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
        · simp only [c13, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
          obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 (κ H1) (Term.list T1)
            (by simp at len; omega) p' hd_self
          exact ⟨R, by simpa using run, tr R res⟩
        simp only [c13]
        have c31 := not_le_lt c13
        by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
        · simp only [c3, ↓reduceIte]
          obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 M (by simp at len; omega) p' ab ac c12
          exact ⟨R, run, tr R res⟩
        simp only [c3, ↓reduceIte]
        have a3 := u3.2 c3
        obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
          (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c12]
      have c21 := not_le_lt c12
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) (κ H2) D (by simp at len; omega) p'
          (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 M (by simp at len; omega) p' ab ac c21
        exact ⟨R, run, tr R res⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_12_3
    intro H1 T1 H2 T2 T3 M len p ab ac c12
    rw [Erlang.lists.«ukeymerge3_12_3/9».eq_def]
    cases T3 with
    | nil =>
      simp only []
      obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simp)
      obtain ⟨R, run, res⟩ := m2.1 T1 T2 (H1 :: M) H2 (κ H1) (by simp at len; omega) p' hd_self
      exact ⟨R, by simpa using run, tr R res⟩
    | cons H3 T3 =>
      have k3 := (p.kc H3 (by simp)).1
      simp only [k3, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
        obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 (κ H1) (Term.list T1)
          (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c13]
      have c31 := not_le_lt c13
      have a3 := ac H3 (by simp)
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
      obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_21_3
    intro H1 T1 H2 T2 T3 M len p ab ac c21
    have a2 := ab H2 (by simp)
    rw [Erlang.lists.«ukeymerge3_21_3/9».eq_def]
    cases T3 with
    | nil =>
      simp only []
      obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := m2.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
        (above_tail p.sb a2)
      exact ⟨R, by simpa using run, tr R res⟩
    | cons H3 T3 =>
      have k3 := (p.kc H3 (by simp)).1
      simp only [k3, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) (κ H2) (Term.list T2)
          (by simp at len; omega) p' (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23]
      have c32 := not_le_lt c23
      have a3 := ac H3 (by simp)
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩

end

end Elixir.STTDescrProofsTest.USort
