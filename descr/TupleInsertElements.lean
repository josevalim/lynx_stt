module

public import Erlang.program
public import Levels

@[expose] public section

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Inserting elements into tuple types. -/

theorem split3_list : ∀ (l acc : List Term) (i : Nat), i ≤ l.length →
    Erlang.lists.«split/3» (.integer i) (Term.list l) (Term.list acc) =
      .ok (.tuple #[Term.list (acc.reverse ++ l.take i), Term.list (l.drop i)])
  | l, acc, 0, _ => by
    have := reverse_list acc []
    rw [Erlang.lists.«split/3».eq_def]
    simp only [List.append_nil] at this
    simp [Term.list] at this
    simp [this]
  | [], _, _ + 1, h => by simp at h
  | x :: l, acc, j + 1, h => by
    have ih := split3_list l (x :: acc) j (by simp at h; omega)
    rw [Erlang.lists.«split/3».eq_def]
    simp only [Term.list] at ih ⊢
    simp [Erlang.erlang.«-/2_integers», ih]

theorem split3_short : ∀ (l acc : List Term) (i : Nat), l.length < i →
    Erlang.lists.«split/3» (.integer i) (Term.list l) (Term.list acc) = .ok (.atom "badarg")
  | _, _, 0, h => by simp at h
  | [], acc, j + 1, _ => by
    have ne : ¬((j : Int) + 1 = 0) := by omega
    rw [Erlang.lists.«split/3».eq_def]
    split <;> simp_all [Term.list]
  | x :: l, acc, j + 1, h => by
    have ih := split3_short l (x :: acc) j (by simp at h; omega)
    rw [Erlang.lists.«split/3».eq_def]
    simp only [Term.list] at ih ⊢
    simp [Erlang.erlang.«-/2_integers», ih]

theorem is_list_l (l : List Term) : Erlang.erlang.«is_list/1» (Term.list l) = .ok (.atom "true") := by
  cases l <;> rfl

theorem split_list (l : List Term) (i : Nat) (h : i ≤ l.length) :
    Erlang.lists.«split/2» (.integer i) (Term.list l) = .ok (.tuple #[Term.list (l.take i), Term.list (l.drop i)]) := by
  have := split3_list l [] i h
  simp only [List.reverse_nil, List.nil_append] at this
  simp [Erlang.lists.«split/2», Erlang.erlang.«>=/2», Int.isGE_compare,
    is_list_l, Erlang.erlang.«and/2», this]

theorem split_short (l : List Term) (i : Nat) (h : l.length < i) (r : Term) :
    Erlang.lists.«split/2» (.integer i) (Term.list l) ≠ .ok r := by
  have := split3_short l [] i h
  simp [Erlang.lists.«split/2», Erlang.erlang.«>=/2», Int.isGE_compare,
    is_list_l, Erlang.erlang.«and/2», this, Erlang.erlang.«error/2»]

/-- The elements of a literal an element is inserted into: open literals are filled with top types up to the index. -/
def fillT (tag : String) (l : List Term) (i : Nat) : List Term :=
  if tag = "open" ∧ l.length < i then l ++ List.replicate (i - l.length) (Term.atom "term") else l

/-- The elements of a literal with an element inserted at an index. -/
def insL (tag : String) (l : List Term) (i : Nat) (x : Term) : List Term :=
  (fillT tag l i).take i ++ x :: (fillT tag l i).drop i

theorem fillT_len {tag : String} {l : List Term} {i : Nat} (fits : tag = "open" ∨ i ≤ l.length) :
    i ≤ (fillT tag l i).length := by
  unfold fillT
  split
  · simp only [List.length_append, List.length_replicate]; omega
  · rcases fits with rfl | h
    · simp_all
    · exact h

/-- `tuple_insert_leaf/4` inserts an element into a literal, and skips closed literals that are too short. -/
theorem insert_leaf_run {tag : String} (g : tag = "open" ∨ tag = "closed") (l : List Term) (i : Nat) (x : Term) :
    (tag = "closed" ∧ l.length < i ∧ Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l)
        (.integer i) x = .ok (.atom "bdd_bot")) ∨
      ((tag = "open" ∨ i ≤ l.length) ∧ ∃ k : Int, Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l)
        (.integer i) x = .ok (.tuple #[.integer k, .atom tag, Term.list (insL tag l i x)]) ∧
        KeyOk (.tuple #[.integer k, .atom tag, Term.list (insL tag l i x)])) := by
  obtain ⟨k, run, key⟩ := leaf_new_key tag g (insL tag l i x)
  rcases g with rfl | rfl
  · right
    refine ⟨Or.inl rfl, k, ?_, key⟩
    by_cases short : l.length < i
    · have fill := fill_list l i (by omega)
      have sp := split_list (l ++ List.replicate (i - l.length) (.atom "term")) i (by simp; omega)
      have e : fillT "open" l i = l ++ List.replicate (i - l.length) (.atom "term") := by simp [fillT, short]
      rw [insL, e] at run
      simp [Elixir.Module.Types.Descr.«tuple_insert_leaf/4», Lynx.Except.andAlso, length_list, Erlang.erlang.«</2»,
        Int.compare_eq_lt, short, fill, sp, ← list_cons, Erlang.erlang.«==/2», insL, e]
      rw [append_list, Lynx.Except.ok_bind, run]
    · have sp := split_list l i (by omega)
      have e : fillT "open" l i = l := by simp [fillT, short]
      rw [insL, e] at run
      have nlt : ¬(l.length : Int) < i := by omega
      simp [Elixir.Module.Types.Descr.«tuple_insert_leaf/4», Lynx.Except.andAlso, length_list, Erlang.erlang.«</2»,
        Int.compare_eq_lt, nlt, sp, ← list_cons, Erlang.erlang.«==/2», insL, e]
      rw [append_list, Lynx.Except.ok_bind, run]
  · have e : fillT "closed" l i = l := by simp [fillT]
    by_cases short : l.length < i
    · left
      refine ⟨rfl, short, ?_⟩
      have lt : (l.length : Int) < i := by omega
      simp [Elixir.Module.Types.Descr.«tuple_insert_leaf/4», length_list,
        Erlang.erlang.«</2», Int.compare_eq_lt, lt, pure, Except.pure]
    · right
      have sp := split_list l i (by omega)
      rw [insL, e] at run
      refine ⟨Or.inr (by omega), k, ?_, key⟩
      have nlt : ¬(l.length : Int) < i := by omega
      simp [Elixir.Module.Types.Descr.«tuple_insert_leaf/4», Lynx.Except.andAlso, sp, ← list_cons,
        Erlang.erlang.«==/2», insL, e, length_list, Erlang.erlang.«</2»,
        Int.compare_eq_lt, nlt]
      rw [append_list, Lynx.Except.ok_bind, run]

section
variable {V : Type} {den : Term → V → Prop}

/-- Tuples of values with a value inserted at an index. -/
def Ins (P : List V → Prop) (i : Nat) (Q : V → Prop) (w : List V) : Prop :=
  ∃ w₁ y w₂, w = w₁ ++ y :: w₂ ∧ List.length w₁ = i ∧ Q y ∧ P (w₁ ++ w₂)

theorem ins_or {P P' : List V → Prop} {i : Nat} {Q : V → Prop} {w : List V} :
    Ins (fun u => P u ∨ P' u) i Q w ↔ Ins P i Q w ∨ Ins P' i Q w := by
  constructor
  · rintro ⟨w₁, y, w₂, e, len, hy, h | h⟩
    · exact Or.inl ⟨w₁, y, w₂, e, len, hy, h⟩
    · exact Or.inr ⟨w₁, y, w₂, e, len, hy, h⟩
  · rintro (⟨w₁, y, w₂, e, len, hy, h⟩ | ⟨w₁, y, w₂, e, len, hy, h⟩)
    · exact ⟨w₁, y, w₂, e, len, hy, Or.inl h⟩
    · exact ⟨w₁, y, w₂, e, len, hy, Or.inr h⟩

theorem ins_congr {P P' : List V → Prop} {i : Nat} {Q : V → Prop} {w : List V} (h : ∀ u, P u ↔ P' u) :
    Ins P i Q w ↔ Ins P' i Q w := by
  simp only [Ins, h]

/-- The values of a literal with an element inserted. -/
theorem inT_insL (hterm : ∀ y, den (.atom "term") y) {tag : String} (l : List Term) (i : Nat) (x : Term)
    (fits : tag = "open" ∨ i ≤ l.length) (w : List V) :
    InT den (tag == "closed") (insL tag l i x) w ↔ Ins (InT den (tag == "closed") l) i (den x) w := by
  have hL := fillT_len (l := l) fits
  have same : ∀ u : List V, i ≤ u.length → (InT den (tag == "closed") (fillT tag l i) u ↔ InT den (tag == "closed") l u) := by
    intro u lu
    unfold fillT
    split
    · rename_i h
      obtain ⟨rfl, short⟩ := h
      simp only [show ("open" == "closed") = Bool.false from rfl]
      exact ⟨fun h => (InT.fill_open h).1, fun h => inT_fill_open _ h (by omega) hterm⟩
    · exact Iff.rfl
  have sp : fillT tag l i = (fillT tag l i).take i ++ (fillT tag l i).drop i := (List.take_append_drop _ _).symm
  have lt : ((fillT tag l i).take i).length = i := by simp; omega
  constructor
  · intro h
    have len := h.length_le
    simp only [insL, List.length_append, List.length_cons] at len
    obtain ⟨w₁, y, w₂, rfl, l₁⟩ : ∃ w₁ y w₂, w = w₁ ++ y :: w₂ ∧ List.length w₁ = i :=
      ⟨w.take i, w[i]'(by omega), w.drop (i + 1), by simp, by simp; omega⟩
    rw [insL, InT.split _ x _ w₁ y w₂ (by omega), ← sp] at h
    exact ⟨w₁, y, w₂, rfl, l₁, h.1, (same _ (by simp; omega)).mp h.2⟩
  · rintro ⟨w₁, y, w₂, rfl, l₁, hy, h⟩
    rw [insL, InT.split _ x _ w₁ y w₂ (by omega), ← sp]
    exact ⟨hy, (same _ (by simp; omega)).mpr h⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem insL_els {tag : String} {l : List Term} {i : Nat} {x : Term} (ef : EF nd E V den tl K) (hl : ∀ e ∈ l, E e)
    (hx : E x) : ∀ e ∈ insL tag l i x, E e := by
  have hf : ∀ e ∈ fillT tag l i, E e := by
    intro e me
    unfold fillT at me
    split at me
    · rcases List.mem_append.mp me with me | me
      · exact hl e me
      · rw [List.eq_of_mem_replicate me]; exact ef.term
    · exact hl e me
  intro e me
  rcases List.mem_append.mp me with me | me
  · exact hf e (List.mem_of_mem_take me)
  · rcases List.mem_cons.mp me with rfl | me
    · exact hx
    · exact hf e (List.mem_of_mem_drop me)

/-- An inserted literal, as a tuple field, with the values of the literal with a value inserted. -/
theorem insert_leaf (ef : EF nd E V den tl K) {tag : String} (g : tag = "open" ∨ tag = "closed") {l : List Term}
    (hl : ∀ e ∈ l, E e) {x : Term} (hx : E x) (i : Nat) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l) (.integer i) x = .ok r) :
    TField E r ∧ ∀ w, denTF E den r w = Bool.true ↔ Ins (InT den (tag == "closed") l) i (den x) w := by
  rcases insert_leaf_run g l i x with ⟨rfl, short, run'⟩ | ⟨fits, k, run', key⟩
  · rw [run'] at run
    cases run
    refine ⟨Or.inr Bdd.bot, fun w => ?_⟩
    rw [denTF_bot]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨w₁, y, w₂, -, len, -, h⟩
    have := InT.closed_length h
    simp at this; omega
  rw [run'] at run
  cases run
  have hl' := insL_els (i := i) (x := x) (tag := tag) ef hl hx
  refine ⟨tleaf_field g hl' key, fun w => ?_⟩
  rw [denTF_leaf ef g hl', vT_lit ef g hl']
  exact inT_insL ef.den_term l i x fits w

/-- `tuple_insert_leaves/4` inserts an element into the literals of a union of literals, and fails on other BDDs. -/
theorem insert_leaves (ef : EF nd E V den tl K) {x : Term} (hx : E x) (i : Nat) :
    ∀ (ok : Term → Prop) (r : Term), Bdd ok r → (∀ t, ok t → TupleLit E t) → ∀ (acc res : Term), TField E acc →
      Elixir.Module.Types.Descr.«tuple_insert_leaves/4» r (.integer i) x acc = .ok res →
      TField E res ∧ ∀ w, denTF E den res w = Bool.true ↔
        denTF E den acc w = Bool.true ∨ Ins (fun u => eval (valT E den u) r = Bool.true) i (den x) w := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleLit E t) → ∀ (acc res : Term), TField E acc →
      Elixir.Module.Types.Descr.«tuple_insert_leaves/4» r (.integer i) x acc = .ok res →
      TField E res ∧ ∀ w, denTF E den res w = Bool.true ↔
        denTF E den acc w = Bool.true ∨ Ins (fun u => eval (valT E den u) r = Bool.true) i (den x) w) ?_ ?_ ?_ ?_
  · intro ok _ acc res _ run
    simp [Elixir.Module.Types.Descr.«tuple_insert_leaves/4»] at run
  · intro ok _ acc res ha run
    simp only [Elixir.Module.Types.Descr.«tuple_insert_leaves/4», pure, Except.pure, Except.ok.injEq] at run
    subst run
    refine ⟨ha, fun w => ?_⟩
    simp [Ins]
  · intro ok k a b okl okLit acc res ha run
    obtain ⟨k', tag, l, e, g, hl⟩ := okLit _ okl
    rw [e] at run ⊢
    simp only [Elixir.Module.Types.Descr.«tuple_insert_leaves/4»] at run
    cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l) (.integer i) x with
    | error _ => simp [hr] at run
    | ok r =>
      rw [hr, Lynx.Except.ok_bind] at run
      obtain ⟨fr, sr⟩ := insert_leaf (den := den) ef g hl hx i hr
      obtain ⟨u, ru, tu, su, -⟩ := tuple_union_lh (den := den) fr ha
      rw [ru] at run
      cases run
      refine ⟨tu, fun w => ?_⟩
      rw [su, Bool.or_eq_true, sr, or_comm]
      refine or_congr Iff.rfl (ins_congr fun u => ?_)
      rw [eval_leaf, vT_lit ef g hl]
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit acc res ha run
    have okLit' : ∀ t, Above ok lit t → TupleLit E t := fun t ht => okLit t ht.1
    obtain ⟨k', tag, l, rfl, g, hl⟩ := okLit _ okl
    by_cases shape : c = .atom "bdd_top" ∧ d = .atom "bdd_bot"
    · obtain ⟨rfl, rfl⟩ := shape
      simp only [Elixir.Module.Types.Descr.«tuple_insert_leaves/4»] at run
      cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l) (.integer i) x with
      | error _ => simp [hr] at run
      | ok r =>
        rw [hr, Lynx.Except.ok_bind] at run
        obtain ⟨fr, sr⟩ := insert_leaf (den := den) ef g hl hx i hr
        obtain ⟨a, ra, ta, sa, -⟩ := tuple_union_lh (den := den) fr ha
        rw [ra, Lynx.Except.ok_bind] at run
        obtain ⟨tres, sres⟩ := iu okLit' a res ta run
        refine ⟨tres, fun w => ?_⟩
        rw [sres, sa, Bool.or_eq_true, sr]
        have ev : ∀ v : List V, eval (valT E den v) (.tuple #[.integer h, .tuple #[.integer k', .atom tag, Term.list l],
            .atom "bdd_top", u, .atom "bdd_bot"]) = Bool.true ↔
            InT den (tag == "closed") l v ∨ eval (valT E den v) u = Bool.true := fun v => by
          simp [eval, vT_lit ef g hl]
        rw [ins_congr ev, ins_or, or_assoc]
        exact or_left_comm
    · exfalso
      rw [Elixir.Module.Types.Descr.«tuple_insert_leaves/4».eq_def] at run
      split at run
      all_goals first
        | (rename_i heq; simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at heq; simp_all; done)
        | (simp_all; done)
        | skip

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Tuple types as unions of literals without negations. -/

/-- `dedup_contiguous/1` keeps elements of a list, and one equal to each of them. -/
theorem dedup_run : ∀ (n : Nat) (l : List Term), l.length ≤ n → ∃ l',
    Elixir.Module.Types.Descr.«dedup_contiguous/1» (Term.list l) = .ok (Term.list l') ∧ (∀ y ∈ l', y ∈ l) ∧
      ∀ x ∈ l, ∃ y ∈ l', compare (fuel x y) x y = .eq
  | _, [], _ => ⟨[], by rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]; rfl, by simp, by simp⟩
  | n, [x], _ => by
    refine ⟨[x], ?_, by simp, by simp [compare_self]⟩
    rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]
    simp only [Term.list]
    rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]
    rfl
  | 0, _ :: _ :: _, h => by simp at h
  | n + 1, x :: y :: rest, h => by
    by_cases same : compareExact (fuel y x) y x = .eq
    · obtain ⟨l', run, sub, cover⟩ := dedup_run n (x :: rest) (by simp at h ⊢; omega)
      refine ⟨l', ?_, fun z mz => ?_, fun z mz => ?_⟩
      · rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]
        simp only [Term.list] at run ⊢
        simp [Erlang.erlang.«=:=/2», same, run]
      · rcases List.mem_cons.mp (sub z mz) with rfl | mz'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mz')
      · rcases List.mem_cons.mp mz with rfl | mz
        · exact cover z List.mem_cons_self
        rcases List.mem_cons.mp mz with rfl | mz
        · obtain ⟨w, mw, cw⟩ := cover x List.mem_cons_self
          exact ⟨w, mw, Lynx.Term.compare_eq_trans (compare_eq_of_compareExact_eq _ _ same) cw⟩
        · exact cover z (List.mem_cons_of_mem _ mz)
    · obtain ⟨l', run, sub, cover⟩ := dedup_run n (y :: rest) (by simp at h ⊢; omega)
      refine ⟨x :: l', ?_, fun z mz => ?_, fun z mz => ?_⟩
      · rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]
        simp only [Term.list] at run ⊢
        simp [Erlang.erlang.«=:=/2», same, run]
      · rcases List.mem_cons.mp mz with rfl | mz
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (sub z mz)
      · rcases List.mem_cons.mp mz with rfl | mz
        · exact ⟨z, List.mem_cons_self, compare_self z⟩
        · obtain ⟨w, mw, cw⟩ := cover z mz
          exact ⟨w, List.mem_cons_of_mem _ mw, cw⟩

/-- `lists:flatmap/2` with steps that return lists. -/
theorem flatmap1_lists {m : Nat} (f : Term) (h : Term → List Term) :
    ∀ l : List Term, (∀ x ∈ l, (D m).pure f #[x] = .ok (Term.list (h x))) →
      Erlang.lists.«flatmap_1/2» (D m) f (Term.list l) = .ok (Term.list (l.flatMap h)) := by
  intro l
  induction l with
  | nil => intro _; simp [Erlang.lists.«flatmap_1/2»]
  | cons x xs ih =>
    intro step
    have tail := ih (fun y my => step y (List.mem_cons_of_mem _ my))
    rw [Erlang.lists.«flatmap_1/2».eq_def]
    simp only at tail ⊢
    simp only [step x List.mem_cons_self, Lynx.Except.ok_bind, List.flatMap_cons]
    rcases hx : h x with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simpa [Term.list] using tail
    · simp [Term.list, tail]
    · have := append_list (a :: b :: r) (xs.flatMap h)
      simp only [Term.list] at this
      simp [Term.list, tail, this]

theorem flatmap_lists {m : Nat} (mo nm : String) (caps : Array Term) (h : Term → List Term) (l : List Term)
    (step : ∀ x ∈ l, (D m).pure (.function false mo nm 1 caps) #[x] = .ok (Term.list (h x))) :
    Erlang.lists.«flatmap/2» (D m) (.function false mo nm 1 caps) (Term.list l) = .ok (Term.list (l.flatMap h)) := by
  have := flatmap1_lists (.function false mo nm 1 caps) h l step
  simp [Erlang.lists.«flatmap/2», Erlang.erlang.«is_function/2», this]

/-- Folds whose steps may fail, keeping a relation when they succeed. -/
theorem foldl1_ok {m : Nat} (f : Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a a', x ∈ l → R pre a → (D m).pure f #[x, a] = .ok a' → R (pre ++ [x]) a') :
    ∀ (rest pre : List Term) acc r, (∀ x ∈ rest, x ∈ l) → R pre acc →
      Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .ok r → R (pre ++ rest) r := by
  intro rest
  induction rest with
  | nil =>
    intro pre acc r _ h run
    simp [Erlang.lists.«foldl_1/3», pure, Except.pure] at run
    subst run; simpa using h
  | cons x xs ih =>
    intro pre acc r sub h run
    rw [Erlang.lists.«foldl_1/3».eq_def] at run
    simp only at run ih
    cases hs : (D m).pure f #[x, acc] with
    | error _ => rw [hs] at run; cases run
    | ok a' =>
      rw [hs, Lynx.Except.ok_bind] at run
      have := ih (pre ++ [x]) a' r (fun y my => sub y (List.mem_cons_of_mem _ my))
        (step pre x acc a' (sub x List.mem_cons_self) h hs) run
      simpa using this

theorem foldl_ok {m : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a a', x ∈ l → R pre a → (D m).pure (.function false mo nm 2 caps) #[x, a] = .ok a' → R (pre ++ [x]) a')
    (acc : Term) (h : R [] acc) (r : Term)
    (run : Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) acc (Term.list l) = .ok r) : R l r := by
  have := foldl1_ok (.function false mo nm 2 caps) R l step l [] acc r (fun _ h => h) h
  simp only [List.nil_append] at this
  apply this
  cases l with
  | nil => simpa [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Term.list, Erlang.lists.«foldl_1/3»] using run
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only [Term.list] at run ⊢
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2»] using run

section
variable {E : Term → Prop} {V : Type} {den : Term → V → Prop}

/-- Literals without negations or keys: a tag and element types. -/
def Piece (E : Term → Prop) (p : Term) : Prop :=
  ∃ (tag : String) (l : List Term), p = .tuple #[.atom tag, Term.list l] ∧ (tag = "open" ∨ tag = "closed") ∧ ∀ e ∈ l, E e

/-- Tuples of values in a literal without negations. -/
def PieceIn (den : Term → V → Prop) (p : Term) (w : List V) : Prop :=
  ∃ (tag : String) (l : List Term), p = .tuple #[.atom tag, Term.list l] ∧ InT den (tag == "closed") l w

theorem pieceIn_iff {tag : String} {l : List Term} {w : List V} :
    PieceIn den (.tuple #[.atom tag, Term.list l]) w ↔ InT den (tag == "closed") l w := by
  constructor
  · rintro ⟨tag', l', e, h⟩
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, Term.atom.injEq, and_true] at e
    obtain ⟨rfl, e⟩ := e
    rwa [list_inj e]
  · intro h; exact ⟨tag, l, rfl, h⟩

/-- Literals without negations equal up to comparison hold the same tuples. -/
theorem pieceIn_congr {K : Nat} {Safe : List (Term × Term) → Prop} (sem : ElemSem E K V den Safe) {p q : Term}
    (hp : Piece E p) (hq : Piece E q) (c : compare (fuel p q) p q = .eq) {w : List V} (h : PieceIn den q w) : PieceIn den p w := by
  obtain ⟨t₁, l₁, rfl, -, h₁⟩ := hp
  obtain ⟨t₂, l₂, rfl, -, h₂⟩ := hq
  rw [compare_tuple] at c
  simp [List.compareLex] at c
  split at c <;> try cases c
  rename_i e₁
  split at c <;> try cases c
  rename_i e₂
  have t : t₁ = t₂ := by have := (compare_eq_atom (.atom t₁) t₂).mp e₁; simpa using this
  subst t
  rw [pieceIn_iff] at h ⊢
  exact list_compare_inT sem h₁ h₂ e₂ h

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Tuples of values outside element types at some position of both. -/
def Differs (den : Term → V → Prop) : List Term → List V → Prop
  | n :: ns, y :: u => ¬den n y ∨ Differs den ns u
  | _, _ => False

/-- The tuples of a literal: long enough, nowhere outside its elements, and of its size when closed. -/
theorem inT_iff_differs {c : Bool} : ∀ (l : List Term) (w : List V),
    InT den c l w ↔ l.length ≤ w.length ∧ ¬Differs den l w ∧ (c = Bool.true → w.length = l.length)
  | [], [] => by simp [InT, Differs]
  | [], _ :: _ => by cases c <;> simp [InT, Differs]
  | _ :: _, [] => by simp [InT]
  | e :: l, y :: w => by
    have ih := inT_iff_differs (c := c) l w
    simp only [InT, Differs, List.length_cons, ih, not_or, Classical.not_not]
    constructor
    · rintro ⟨hy, a, b, c'⟩; exact ⟨by omega, ⟨hy, b⟩, fun h => by rw [c' h]⟩
    · rintro ⟨a, ⟨hy, b⟩, c'⟩; exact ⟨hy, by omega, b, fun h => by have := c' h; omega⟩

theorem inT_last {x : Term} : ∀ (A : List Term) (v : List V),
    InT den Bool.true (A ++ [x]) v ↔ ∃ v₁ y, v = v₁ ++ [y] ∧ InT den Bool.true A v₁ ∧ den x y := by
  intro A v
  rw [InT.mid]
  constructor
  · rintro ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩
    have : v₂ = [] := by cases v₂ <;> simp_all [InT]
    subst this
    exact ⟨v₁, y, rfl, h₁, hy⟩
  · rintro ⟨v₁, y, rfl, h₁, hy⟩
    exact ⟨v₁, y, [], rfl, h₁, hy, trivial⟩

/-- `zip_empty_intersection?/2` finds a position where two literals have disjoint elements. -/
theorem zip_empty_run (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) :
    ∀ (l₁ l₂ : List Term), (∀ e ∈ l₁, E e) → (∀ e ∈ l₂, E e) → ∃ b : Bool,
      Elixir.Module.Types.Descr.«zip_empty_intersection?/2» (D m) (Term.list l₁) (Term.list l₂) = .ok (boolAtom b) ∧
      (b = Bool.true → ∀ w, InT den Bool.false l₁ w → InT den Bool.false l₂ w → False)
  | [], l₂, _, _ => ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«zip_empty_intersection?/2», boolAtom], by simp⟩
  | x :: l₁, [], _, _ => ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«zip_empty_intersection?/2», boolAtom],
      by simp⟩
  | x :: l₁, y :: l₂, h₁, h₂ => by
    obtain ⟨c, hc, rc, sc, -⟩ := ef.inter (h₁ x List.mem_cons_self) (h₂ y List.mem_cons_self)
    obtain ⟨e, re, se⟩ := empty_bool ef hc hm
    cases e
    · obtain ⟨b, rb, sb⟩ := zip_empty_run ef hm l₁ l₂ (fun e me => h₁ e (List.mem_cons_of_mem _ me))
        (fun e me => h₂ e (List.mem_cons_of_mem _ me))
      refine ⟨b, ?_, fun hb w i₁ i₂ => ?_⟩
      · rw [Elixir.Module.Types.Descr.«zip_empty_intersection?/2».eq_def]
        simp only at rb ⊢
        simp [rc m hm, re, rb, boolAtom]
      · cases w with
        | nil => exact i₁
        | cons z w => exact sb hb w i₁.2 i₂.2
    · refine ⟨Bool.true, ?_, fun _ w i₁ i₂ => ?_⟩
      · rw [Elixir.Module.Types.Descr.«zip_empty_intersection?/2».eq_def]
        simp [rc m hm, re, boolAtom]
      · cases w with
        | nil => exact i₁
        | cons z w => exact se.mp rfl z ((sc z).mpr ⟨i₁.1, i₂.1⟩)

theorem content_nil (d : Dispatcher) (acc tag neg nl : Term) :
    Elixir.Module.Types.Descr.«tuple_elim_content/4» d acc tag .nil (.cons neg nl) =
      Elixir.Module.Types.Descr.«tuple_elim_content/4» d acc tag (Term.list [.atom "term"]) (.cons neg nl) := by
  rw [Elixir.Module.Types.Descr.«tuple_elim_content/4».eq_def]
  conv => rhs; rw [Elixir.Module.Types.Descr.«tuple_elim_content/4».eq_def]

/-- `tuple_elim_content/4` splits the tuples of a literal outside a negated one at the first position outside it. -/
theorem elim_content (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag : String} (g : tag = "open" ∨ tag = "closed") :
    ∀ (nl acc l : List Term), (∀ e ∈ nl, E e) → (∀ e ∈ acc, E e) → (∀ e ∈ l, E e) →
      (tag = "closed" → nl.length ≤ l.length) →
      ∃ P, Elixir.Module.Types.Descr.«tuple_elim_content/4» (D m) (Term.list acc) (.atom tag) (Term.list l) (Term.list nl) =
          .ok (Term.list P) ∧ (∀ p ∈ P, Piece E p) ∧
        ∀ w, (∃ p ∈ P, PieceIn den p w) ↔
          ∃ v₁ u, w = v₁ ++ u ∧ InT den Bool.true acc.reverse v₁ ∧ InT den (tag == "closed") l u ∧ Differs den nl u := by
  intro nl
  induction nl with
  | nil =>
    intro acc l _ _ _ _
    refine ⟨[], ?_, by simp, fun w => by simp [Differs]⟩
    rw [Elixir.Module.Types.Descr.«tuple_elim_content/4».eq_def]
    rfl
  | cons neg nl ih =>
    intro acc l hnl hacc hl fit
    have hneg := hnl neg List.mem_cons_self
    have hnl' : ∀ e ∈ nl, E e := fun e me => hnl e (List.mem_cons_of_mem _ me)
    -- The elements, with a top type past the end of open ones.
    obtain ⟨ty, rest, hty, hrest, run₀, same, fit'⟩ : ∃ ty rest, E ty ∧ (∀ e ∈ rest, E e) ∧
        Elixir.Module.Types.Descr.«tuple_elim_content/4» (D m) (Term.list acc) (.atom tag) (Term.list l)
          (Term.list (neg :: nl)) =
        Elixir.Module.Types.Descr.«tuple_elim_content/4» (D m) (Term.list acc) (.atom tag) (Term.list (ty :: rest))
          (Term.list (neg :: nl)) ∧
        (∀ u, (InT den (tag == "closed") l u ∧ Differs den (neg :: nl) u) ↔
          (InT den (tag == "closed") (ty :: rest) u ∧ Differs den (neg :: nl) u)) ∧
        (tag = "closed" → nl.length ≤ rest.length) := by
      cases l with
      | nil =>
        have op : tag = "open" := by
          rcases g with h | rfl
          · exact h
          · have := fit rfl; simp at this
        subst op
        refine ⟨.atom "term", [], ef.term, by simp, ?_, fun u => ?_, by simp⟩
        · simp only [Term.list]; exact content_nil _ _ _ _ _
        · cases u with
          | nil => simp [Differs]
          | cons y u => simp [InT, ef.den_term y, InT.open_nil]
      | cons ty rest =>
        exact ⟨ty, rest, hl ty List.mem_cons_self, fun e me => hl e (List.mem_cons_of_mem _ me), rfl, fun _ => Iff.rfl,
          fun h => by have := fit h; simp at this; omega⟩
    obtain ⟨df, hdf, rdf, sdf, -⟩ := ef.diff hty hneg
    obtain ⟨mt, hmt, rmt, smt, -⟩ := ef.inter hty hneg
    obtain ⟨ed, red, sed⟩ := empty_bool ef hdf hm
    obtain ⟨em, rem, sem⟩ := empty_bool ef hmt hm
    -- The pieces whose first position outside the negated literal is this one.
    obtain ⟨H, rH, tH, sH⟩ : ∃ H : List Term, (ed = Bool.false ∧ H = [.tuple #[.atom tag, Term.list (acc.reverse ++ df :: rest)]] ∨
        ed = Bool.true ∧ H = []) ∧ (∀ p ∈ H, Piece E p) ∧
        ∀ w, (∃ p ∈ H, PieceIn den p w) ↔ InT den (tag == "closed") (acc.reverse ++ df :: rest) w := by
      cases ed
      · refine ⟨_, Or.inl ⟨rfl, rfl⟩, fun p mp => ?_, fun w => by simp [pieceIn_iff]⟩
        simp at mp; subst mp
        refine ⟨tag, _, rfl, g, fun e me => ?_⟩
        rcases List.mem_append.mp me with me | me
        · exact hacc e (List.mem_reverse.mp me)
        · rcases List.mem_cons.mp me with rfl | me
          · exact hdf
          · exact hrest e me
      · refine ⟨[], Or.inr ⟨rfl, rfl⟩, by simp, fun w => ?_⟩
        simp only [List.not_mem_nil, false_and, exists_false, false_iff]
        intro h
        obtain ⟨v₁, y, v₂, -, -, hy, -⟩ := (InT.mid _ _ _).mp h
        exact sed.mp rfl y hy
    -- The pieces whose first position outside the negated literal is a later one.
    obtain ⟨L, rL, tL, sL⟩ : ∃ L : List Term, (em = Bool.false ∧ Elixir.Module.Types.Descr.«tuple_elim_content/4» (D m)
          (Term.list (mt :: acc)) (.atom tag) (Term.list rest) (Term.list nl) = .ok (Term.list L) ∨ em = Bool.true ∧ L = []) ∧
        (∀ p ∈ L, Piece E p) ∧ ∀ w, (∃ p ∈ L, PieceIn den p w) ↔
          ∃ v₁ y v₂, w = v₁ ++ y :: v₂ ∧ InT den Bool.true acc.reverse v₁ ∧ den mt y ∧ InT den (tag == "closed") rest v₂ ∧
            Differs den nl v₂ := by
      cases em
      · obtain ⟨L, rL, tL, sL⟩ := ih (mt :: acc) rest hnl' (fun e me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact hmt
          · exact hacc e me) hrest fit'
        refine ⟨L, Or.inl ⟨rfl, rL⟩, tL, fun w => ?_⟩
        rw [sL]
        simp only [List.reverse_cons]
        constructor
        · rintro ⟨v₁', u, rfl, h₁, h₂, h₃⟩
          obtain ⟨v₁, y, rfl, h₁, hy⟩ := (inT_last _ _).mp h₁
          exact ⟨v₁, y, u, by simp, h₁, hy, h₂, h₃⟩
        · rintro ⟨v₁, y, v₂, rfl, h₁, hy, h₂, h₃⟩
          exact ⟨v₁ ++ [y], v₂, by simp, (inT_last _ _).mpr ⟨v₁, y, rfl, h₁, hy⟩, h₂, h₃⟩
      · refine ⟨[], Or.inr ⟨rfl, rfl⟩, by simp, fun w => ?_⟩
        simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_exists, not_and]
        intro _ y _ _ _ hy
        exact absurd hy (sem.mp rfl y)
    refine ⟨H ++ L, ?_, fun p mp => ?_, fun w => ?_⟩
    · rw [run₀, Elixir.Module.Types.Descr.«tuple_elim_content/4».eq_def]
      simp only [Term.list]
      rcases rH with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases rL with ⟨rfl, rL⟩ | ⟨rfl, rfl⟩
      · have rev := reverse_list acc (df :: rest)
        have app := append_list [.tuple #[.atom tag, Term.list (acc.reverse ++ df :: rest)]] L
        simp only [Term.list] at rL rev app
        simp [rdf m hm, rmt m hm, red, rem, Lynx.Term.isMember, boolAtom, rev, rL, app]
      · have rev := reverse_list acc (df :: rest)
        have app := append_list [.tuple #[.atom tag, Term.list (acc.reverse ++ df :: rest)]] []
        simp only [Term.list] at rev app
        simp [rdf m hm, rmt m hm, red, rem, Lynx.Term.isMember, boolAtom, rev, app]
      · have app := append_list [] L
        simp only [Term.list] at rL app
        simp [rdf m hm, rmt m hm, red, rem, Lynx.Term.isMember, boolAtom, rL, app]
      · simp [rdf m hm, rmt m hm, red, rem, Lynx.Term.isMember, boolAtom, Erlang.erlang.«++/2»]
    · rcases List.mem_append.mp mp with mp | mp
      · exact tH p mp
      · exact tL p mp
    · have split : (∃ p ∈ H ++ L, PieceIn den p w) ↔ (∃ p ∈ H, PieceIn den p w) ∨ ∃ p ∈ L, PieceIn den p w := by
        simp only [List.mem_append, or_and_right, exists_or]
      rw [split, sH, sL, InT.mid]
      constructor
      · rintro (⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩ | ⟨v₁, y, v₂, rfl, h₁, hy, h₂, h₃⟩)
        · obtain ⟨a, b⟩ := (sdf y).mp hy
          exact ⟨v₁, y :: v₂, rfl, h₁, ((same (y :: v₂)).mpr ⟨⟨a, h₂⟩, Or.inl b⟩).1, ((same (y :: v₂)).mpr ⟨⟨a, h₂⟩, Or.inl b⟩).2⟩
        · obtain ⟨a, b⟩ := (smt y).mp hy
          exact ⟨v₁, y :: v₂, rfl, h₁, ((same (y :: v₂)).mpr ⟨⟨a, h₂⟩, Or.inr h₃⟩).1, ((same (y :: v₂)).mpr ⟨⟨a, h₂⟩, Or.inr h₃⟩).2⟩
      · rintro ⟨v₁, u, rfl, h₁, h₂, h₃⟩
        have := (same u).mp ⟨h₂, h₃⟩
        cases u with
        | nil => exact this.2.elim
        | cons y v₂ =>
          obtain ⟨⟨a, b⟩, c⟩ := this
          by_cases hn : den neg y
          · rcases c with c | c
            · exact absurd hn c
            · exact Or.inr ⟨v₁, y, v₂, rfl, h₁, (smt y).mpr ⟨a, hn⟩, b, c⟩
          · exact Or.inl ⟨v₁, y, v₂, rfl, h₁, (sdf y).mpr ⟨a, hn⟩, b⟩
end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- A closed literal of elements filled with top types up to a size. -/
def closedFill (l : List Term) (j : Nat) : Term :=
  .tuple #[.atom "closed", Term.list (l ++ List.replicate (j - l.length) (Term.atom "term"))]

theorem elim_sizes_run (l : List Term) (m : Nat) : ∀ (k i : Nat), m - i = k → l.length ≤ i → ∀ acc : List Term,
    Elixir.Module.Types.Descr.«tuple_elim_sizes/4» (.integer i) (.integer m) (Term.list l) (Term.list acc) =
      .ok (Term.list (((List.range' i (m - i)).map (closedFill l)).reverse ++ acc))
  | 0, i, hk, _, acc => by
    have : ¬(i : Int) < m := by omega
    rw [Elixir.Module.Types.Descr.«tuple_elim_sizes/4».eq_def]
    simp [Erlang.erlang.«</2», Int.compare_eq_lt, this, hk]
  | k + 1, i, hk, hl, acc => by
    have lt : (i : Int) < m := by omega
    have ih := elim_sizes_run l m k (i + 1) (by omega) (by omega) (closedFill l i :: acc)
    have range : List.range' i (m - i) = i :: List.range' (i + 1) (m - (i + 1)) := by
      rw [show m - i = (m - (i + 1)) + 1 by omega, List.range'_succ]
    rw [Elixir.Module.Types.Descr.«tuple_elim_sizes/4».eq_def]
    rw [show (((i + 1 : Nat) : Int)) = (i : Int) + 1 by omega] at ih
    simp only [Term.list, closedFill] at ih
    simp [Erlang.erlang.«</2», Int.compare_eq_lt, lt, fill_list l i hl, ih, range,
      closedFill]

theorem pieceIn_closedFill {l : List Term} {j : Nat} (hl : l.length ≤ j) (hterm : ∀ y, den (.atom "term") y)
    (w : List V) : PieceIn den (closedFill l j) w ↔ InT den Bool.false l w ∧ w.length = j := by
  rw [closedFill, pieceIn_iff]
  simp only [show ("closed" == "closed") = Bool.true from rfl]
  constructor
  · intro h
    obtain ⟨a, b⟩ := InT.fill h
    exact ⟨a, by omega⟩
  · rintro ⟨h, rfl⟩
    exact inT_fill_closed h hterm

theorem sizes_sem {l : List Term} {i m : Nat} (hl : l.length ≤ i) (hterm : ∀ y, den (.atom "term") y) (w : List V) :
    (∃ p ∈ ((List.range' i (m - i)).map (closedFill l)).reverse, PieceIn den p w) ↔
      InT den Bool.false l w ∧ i ≤ w.length ∧ w.length < m := by
  simp only [List.mem_reverse, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨p, ⟨j, ⟨k, hk, rfl⟩, rfl⟩, hp⟩
    obtain ⟨a, b⟩ := (pieceIn_closedFill (by omega) hterm w).mp hp
    exact ⟨a, by omega, by omega⟩
  · rintro ⟨a, b, c⟩
    exact ⟨_, ⟨w.length, ⟨w.length - i, by omega, by omega⟩, rfl⟩,
      (pieceIn_closedFill (by omega) hterm w).mpr ⟨a, rfl⟩⟩

theorem sizes_piece (ef : EF nd E V den tl K) {l : List Term} (hl : ∀ e ∈ l, E e) {i m : Nat} :
    ∀ p ∈ ((List.range' i (m - i)).map (closedFill l)).reverse, Piece E p := by
  intro p mp
  simp only [List.mem_reverse, List.mem_map] at mp
  obtain ⟨j, -, rfl⟩ := mp
  refine ⟨"closed", _, rfl, Or.inr rfl, fun e me => ?_⟩
  rcases List.mem_append.mp me with me | me
  · exact hl e me
  · rw [List.eq_of_mem_replicate me]; exact ef.term

/-- `tuple_elim_size/5` gives the tuples of an open literal of sizes outside a negated literal. -/
theorem elim_size_open (ef : EF nd E V den tl K) {ntag : String} (ng : ntag = "open" ∨ ntag = "closed") {l : List Term}
    (hl : ∀ e ∈ l, E e) (m : Nat) (fit : ntag = "closed" → l.length ≤ m + 1) :
    ∃ P, Elixir.Module.Types.Descr.«tuple_elim_size/5» (.integer l.length) (.integer m) (.atom "open") (Term.list l)
        (.atom ntag) = .ok (Term.list P) ∧ (∀ p ∈ P, Piece E p) ∧
      ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ InT den Bool.false l w ∧ (List.length w < m ∨ (ntag = "closed" ∧ m + 1 ≤ List.length w)) := by
  have sizes := elim_sizes_run l m (m - l.length) l.length rfl (Nat.le_refl _)
  rcases ng with rfl | rfl
  · refine ⟨((List.range' l.length (m - l.length)).map (closedFill l)).reverse ++ [], ?_, ?_, fun w => ?_⟩
    · have := sizes []
      simp [Elixir.Module.Types.Descr.«tuple_elim_size/5», Erlang.erlang.«==/2», Term.list] at this ⊢
      exact this
    · simpa using sizes_piece ef hl
    · rw [List.append_nil, sizes_sem (Nat.le_refl _) ef.den_term w]
      constructor
      · rintro ⟨a, -, c⟩; exact ⟨a, Or.inl c⟩
      · rintro ⟨a, c | ⟨h, -⟩⟩
        · exact ⟨a, a.length_le, c⟩
        · simp at h
  · have hf := fit rfl
    let top : Term := .tuple #[.atom "open", Term.list (l ++ List.replicate (m + 1 - l.length) (.atom "term"))]
    refine ⟨((List.range' l.length (m - l.length)).map (closedFill l)).reverse ++ [top], ?_, ?_, fun w => ?_⟩
    · have := sizes [top]
      have fl : Elixir.Module.Types.Descr.«tuple_fill/2» (Term.list l) (.integer ((m : Int) + 1)) =
          .ok (Term.list (l ++ List.replicate (m + 1 - l.length) (.atom "term"))) := by
        simpa using fill_list l (m + 1) hf
      simp [Elixir.Module.Types.Descr.«tuple_elim_size/5», Erlang.erlang.«==/2», fl] at this ⊢
      exact this
    · intro p mp
      rcases List.mem_append.mp mp with mp | mp
      · exact sizes_piece ef hl p mp
      · simp at mp; subst mp
        refine ⟨"open", _, rfl, Or.inl rfl, fun e me => ?_⟩
        rcases List.mem_append.mp me with me | me
        · exact hl e me
        · rw [List.eq_of_mem_replicate me]; exact ef.term
    · have split : (∃ p ∈ ((List.range' l.length (m - l.length)).map (closedFill l)).reverse ++ [top], PieceIn den p w) ↔
          (∃ p ∈ ((List.range' l.length (m - l.length)).map (closedFill l)).reverse, PieceIn den p w) ∨
            PieceIn den top w := by
        simp only [List.mem_append, List.mem_singleton, or_and_right, exists_or, exists_eq_left]
      rw [split, sizes_sem (Nat.le_refl _) ef.den_term w, pieceIn_iff]
      simp only [show ("open" == "closed") = Bool.false from rfl, true_and]
      constructor
      · rintro (⟨a, -, c⟩ | h)
        · exact ⟨a, Or.inl c⟩
        · obtain ⟨a, b⟩ := InT.fill_open h
          exact ⟨a, Or.inr (by omega)⟩
      · rintro ⟨a, c | c⟩
        · exact Or.inl ⟨a, a.length_le, c⟩
        · exact Or.inr (inT_fill_open _ a (by omega) ef.den_term)

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem orElse_bool (a : Bool) (x : Except Exception Term) :
    Lynx.Except.orElse (.ok (boolAtom a)) x = if a then .ok (.atom "true") else x := by
  cases a <;> rfl

theorem tag_closed {tag : String} (g : tag = "open" ∨ tag = "closed") :
    Erlang.erlang.«==/2» (.atom tag) (.atom "closed") = .ok (boolAtom (decide (tag = "closed"))) := by
  rcases g with rfl | rfl <;> simp [Erlang.erlang.«==/2», boolAtom]

/-- `tuple_eliminate_single_negation/3` gives literals holding the tuples of a literal outside a negated literal. -/
theorem elim_single (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag ntag : String} (g : tag = "open" ∨ tag = "closed")
    (ng : ntag = "open" ∨ ntag = "closed") {l nl : List Term} (hl : ∀ e ∈ l, E e) (hnl : ∀ e ∈ nl, E e) :
    ∃ P, Elixir.Module.Types.Descr.«tuple_eliminate_single_negation/3» (D m) (.atom tag) (Term.list l)
        (.tuple #[.atom ntag, Term.list nl]) = .ok (Term.list P) ∧ (∀ p ∈ P, Piece E p) ∧
      ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ InT den (tag == "closed") l w ∧ ¬InT den (ntag == "closed") nl w := by
  obtain ⟨zb, rz, sz⟩ := zip_empty_run (den := den) ef hm l nl hl hnl
  have c₁ : Lynx.Except.andAlso (Erlang.erlang.«==/2» (.atom tag) (.atom "closed"))
      (Erlang.erlang.«</2» (.integer l.length) (.integer nl.length)) =
        .ok (boolAtom (decide (tag = "closed" ∧ l.length < nl.length))) := by
    rw [tag_closed g]
    by_cases h₁ : tag = "closed" <;> by_cases h₂ : l.length < nl.length <;>
      simp [Lynx.Except.andAlso, boolAtom, h₁, h₂, Erlang.erlang.«</2», Int.compare_eq_lt]
  have c₂ : Lynx.Except.andAlso (Erlang.erlang.«==/2» (.atom ntag) (.atom "closed"))
      (Erlang.erlang.«>/2» (.integer l.length) (.integer nl.length)) =
        .ok (boolAtom (decide (ntag = "closed" ∧ nl.length < l.length))) := by
    rw [tag_closed ng]
    by_cases h₁ : ntag = "closed" <;> by_cases h₂ : nl.length < l.length <;>
      simp [Lynx.Except.andAlso, boolAtom, h₁, h₂, Erlang.erlang.«>/2», Int.compare_eq_gt]
  have closedLen : ∀ {w : List V}, InT den (tag == "closed") l w → tag = "closed" → w.length = l.length := by
    intro w h c; subst c; exact h.closed_length
  by_cases cond : (tag = "closed" ∧ l.length < nl.length) ∨ (ntag = "closed" ∧ nl.length < l.length) ∨ zb = Bool.true
  · refine ⟨[.tuple #[.atom tag, Term.list l]], ?_, fun p mp => ?_, fun w => ?_⟩
    · simp only [Elixir.Module.Types.Descr.«tuple_eliminate_single_negation/3», length_list, Lynx.Except.ok_bind, c₁, c₂,
        orElse_bool, rz]
      rcases cond with h | h | h
      · simp [h, boolAtom, Lynx.Term.isMember, Term.list]
      · by_cases h' : tag = "closed" ∧ l.length < nl.length
        · simp [h', boolAtom, Lynx.Term.isMember, Term.list]
        · simp [h, h', boolAtom, Lynx.Term.isMember, Term.list]
      · by_cases h' : tag = "closed" ∧ l.length < nl.length
        · simp [h', boolAtom, Lynx.Term.isMember, Term.list]
        by_cases h'' : ntag = "closed" ∧ nl.length < l.length
        · simp [h', h'', boolAtom, Lynx.Term.isMember, Term.list]
        · simp [h, h', h'', boolAtom, Lynx.Term.isMember, Term.list]
    · simp at mp; subst mp; exact ⟨tag, l, rfl, g, hl⟩
    · simp only [List.mem_singleton, exists_eq_left, pieceIn_iff]
      refine ⟨fun h => ⟨h, fun hn => ?_⟩, fun h => h.1⟩
      rcases cond with ⟨c, lt⟩ | ⟨c, lt⟩ | z
      · have := closedLen h c; have := hn.length_le; omega
      · subst c; have := hn.closed_length; have := h.length_le; omega
      · exact sz z w (InT.iff_open.mp h).1 (InT.iff_open.mp hn).1
  · simp only [not_or, not_and, Nat.not_lt, Bool.not_eq_true] at cond
    obtain ⟨n₁, n₂, rfl⟩ := cond
    -- The sizes outside the negated literal.
    obtain ⟨S, rS, tS, sS⟩ : ∃ S, Elixir.Module.Types.Descr.«tuple_elim_size/5» (.integer l.length) (.integer nl.length)
        (.atom tag) (Term.list l) (.atom ntag) = .ok (Term.list S) ∧ (∀ p ∈ S, Piece E p) ∧
        ∀ w, (∃ p ∈ S, PieceIn den p w) ↔ tag = "open" ∧ InT den Bool.false l w ∧
          (List.length w < nl.length ∨ (ntag = "closed" ∧ nl.length + 1 ≤ List.length w)) := by
      rcases g with rfl | rfl
      · obtain ⟨S, rS, tS, sS⟩ := elim_size_open (den := den) ef ng hl nl.length (fun h => by have := n₂ h; omega)
        exact ⟨S, rS, tS, fun w => by rw [sS]; simp⟩
      · exact ⟨[], by simp [Elixir.Module.Types.Descr.«tuple_elim_size/5», Term.list], by simp, by simp⟩
    obtain ⟨C, rC, tC, sC⟩ := elim_content (den := den) ef hm g nl [] l hnl (by simp) hl n₁
    refine ⟨S ++ C, ?_, fun p mp => ?_, fun w => ?_⟩
    · have app := append_list S C
      have d₁ : decide (tag = "closed" ∧ l.length < nl.length) = Bool.false := by
        simp only [decide_eq_false_iff_not, not_and, Nat.not_lt]; exact n₁
      have d₂ : decide (ntag = "closed" ∧ nl.length < l.length) = Bool.false := by
        simp only [decide_eq_false_iff_not, not_and, Nat.not_lt]; exact n₂
      simp only [Elixir.Module.Types.Descr.«tuple_eliminate_single_negation/3», length_list, Lynx.Except.ok_bind, c₁, c₂,
        d₁, d₂, orElse_bool, rz]
      simp [boolAtom, Lynx.Term.isMember, rS, rC, app]
    · rcases List.mem_append.mp mp with mp | mp
      · exact tS p mp
      · exact tC p mp
    · have split : (∃ p ∈ S ++ C, PieceIn den p w) ↔ (∃ p ∈ S, PieceIn den p w) ∨ ∃ p ∈ C, PieceIn den p w := by
        simp only [List.mem_append, or_and_right, exists_or]
      have content : (∃ p ∈ C, PieceIn den p w) ↔ InT den (tag == "closed") l w ∧ Differs den nl w := by
        rw [sC]
        constructor
        · rintro ⟨v₁, u, rfl, h₁, h₂, h₃⟩
          have : v₁ = [] := by cases v₁ <;> simp_all [InT]
          subst this; exact ⟨h₂, h₃⟩
        · rintro ⟨h₂, h₃⟩; exact ⟨[], w, rfl, trivial, h₂, h₃⟩
      rw [split, sS, content, inT_iff_differs nl w]
      constructor
      · rintro (⟨rfl, h, c⟩ | ⟨h, d⟩)
        · refine ⟨h, fun ⟨a, _, b⟩ => ?_⟩
          rcases c with c | ⟨rfl, c⟩
          · omega
          · have := b rfl; omega
        · exact ⟨h, fun hh => hh.2.1 d⟩
      · rintro ⟨h, hn⟩
        by_cases d : Differs den nl w
        · exact Or.inr ⟨h, d⟩
        · left
          have hn' : ¬(nl.length ≤ w.length ∧ ((ntag == "closed") = Bool.true → w.length = nl.length)) :=
            fun ⟨a, b⟩ => hn ⟨a, d, b⟩
          rcases g with rfl | rfl
          · refine ⟨rfl, h, ?_⟩
            by_cases lt : w.length < nl.length
            · exact Or.inl lt
            · rcases ng with rfl | rfl
              · exact absurd ⟨by omega, fun h => by simp at h⟩ hn'
              · exact Or.inr ⟨rfl, by
                  by_cases e : w.length = nl.length
                  · exact absurd ⟨by omega, fun _ => e⟩ hn'
                  · omega⟩
          · exfalso
            have len := closedLen h rfl
            have := n₁ rfl
            rcases ng with rfl | rfl
            · exact hn' ⟨by omega, fun h => by simp at h⟩
            · have := n₂ rfl; exact hn' ⟨by omega, fun _ => by omega⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `tuple_eliminate_negations/3` gives literals holding the tuples of a line. -/
theorem elim_negs (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {tag : String} (g : tag = "open" ∨ tag = "closed")
    {l : List Term} (hl : ∀ e ∈ l, E e) (negs : List Term) (lits : ∀ N ∈ negs, TupleLit E N) :
    ∃ P, Elixir.Module.Types.Descr.«tuple_eliminate_negations/3» (D (n + 2)) (.atom tag) (Term.list l) (Term.list negs) =
        .ok (Term.list P) ∧ (∀ p ∈ P, Piece E p) ∧
      ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ InT den (tag == "closed") l w ∧ ∀ N ∈ negs, ¬LitSem den N w := by
  obtain ⟨r, ⟨P, rfl, tP, sP⟩, run⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr"
    "-tuple_eliminate_negations/3-fun-1-" #[]
    (fun pre a => ∃ P, a = Term.list P ∧ (∀ p ∈ P, Piece E p) ∧
      ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ InT den (tag == "closed") l w ∧ ∀ N ∈ pre, ¬LitSem den N w) negs
    (fun pre x a mx ⟨A, ea, tA, sA⟩ => by
      subst ea
      obtain ⟨k, ntag, nl, rfl, ng, hnl⟩ := lits x mx
      have each : ∀ p ∈ A, ∃ Q, Elixir.Module.Types.Descr.«-tuple_eliminate_negations/3-fun-0-/3» (D n) (Term.list nl)
          (.atom ntag) p = .ok (Term.list Q) ∧ (∀ q ∈ Q, Piece E q) ∧
          ∀ w, (∃ q ∈ Q, PieceIn den q w) ↔ PieceIn den p w ∧ ¬InT den (ntag == "closed") nl w := by
        intro p mp
        obtain ⟨tag', l', rfl, g', hl'⟩ := tA p mp
        obtain ⟨Q, rQ, tQ, sQ⟩ := elim_single (den := den) ef hn g' ng hl' hnl
        refine ⟨Q, ?_, tQ, fun w => by rw [sQ, pieceIn_iff]⟩
        simpa [Elixir.Module.Types.Descr.«-tuple_eliminate_negations/3-fun-0-/3»] using rQ
      classical
      let h : Term → List Term := fun p => if hp : p ∈ A then Classical.choose (each p hp) else []
      have hh : ∀ p ∈ A, Elixir.Module.Types.Descr.«-tuple_eliminate_negations/3-fun-0-/3» (D n) (Term.list nl)
          (.atom ntag) p = .ok (Term.list (h p)) ∧ (∀ q ∈ h p, Piece E q) ∧
          ∀ w, (∃ q ∈ h p, PieceIn den q w) ↔ PieceIn den p w ∧ ¬InT den (ntag == "closed") nl w := by
        intro p mp
        simp only [h, dite_eq_left mp]
        exact Classical.choose_spec (each p mp)
      have fm := flatmap_lists (m := n + 1) "Elixir.Module.Types.Descr" "-tuple_eliminate_negations/3-fun-0-"
        #[Term.list nl, .atom ntag] h A (fun p mp => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_eliminate_negations/3-fun-0-/1».pure]
          exact (hh p mp).1)
      refine ⟨Term.list (A.flatMap h), ⟨A.flatMap h, rfl, fun q mq => ?_, fun w => ?_⟩, ?_⟩
      · obtain ⟨p, mp, mq⟩ := List.mem_flatMap.mp mq
        exact (hh p mp).2.1 q mq
      · have lit : LitSem den (.tuple #[.integer k, .atom ntag, Term.list nl]) w ↔ InT den (ntag == "closed") nl w :=
          ⟨lit_sem, fun h => ⟨k, ntag, nl, rfl, h⟩⟩
        constructor
        · rintro ⟨q, mq, hq⟩
          obtain ⟨p, mp, mq⟩ := List.mem_flatMap.mp mq
          obtain ⟨hp, hn⟩ := ((hh p mp).2.2 w).mp ⟨q, mq, hq⟩
          obtain ⟨a, b⟩ := (sA w).mp ⟨p, mp, hp⟩
          refine ⟨a, fun N mN => ?_⟩
          rcases List.mem_append.mp mN with mN | mN
          · exact b N mN
          · simp at mN; subst mN; rw [lit]; exact hn
        · rintro ⟨a, b⟩
          obtain ⟨p, mp, hp⟩ := (sA w).mpr ⟨a, fun N mN => b N (List.mem_append_left _ mN)⟩
          obtain ⟨q, mq, hq⟩ := ((hh p mp).2.2 w).mpr ⟨hp, fun hn => b _ (by simp) (lit.mpr hn)⟩
          exact ⟨q, List.mem_flatMap.mpr ⟨p, mp, mq⟩, hq⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_eliminate_negations/3-fun-1-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_eliminate_negations/3-fun-1-/2»] using fm)
    (Term.list [.tuple #[.atom tag, Term.list l]])
    ⟨[.tuple #[.atom tag, Term.list l]], rfl, fun p mp => by simp at mp; subst mp; exact ⟨tag, l, rfl, g, hl⟩,
      fun w => by simp [pieceIn_iff]⟩
  exact ⟨P, by simpa [Elixir.Module.Types.Descr.«tuple_eliminate_negations/3»] using run, tP, sP⟩

/-- `tuple_bdd_to_dnf_no_negations/1` gives literals holding the tuples of a BDD. -/
theorem no_negs (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {r : Term} (wr : Bdd (TLit E) r) :
    ∃ P, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1» (D (n + 3)) r = .ok (Term.list P) ∧
      (∀ p ∈ P, Piece E p) ∧ ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ eval (valT E den w) r = Bool.true := by
  obtain ⟨all, run, tl', sl⟩ := dnf_tuple (den := den) ef.opsU ef.msemZ (m := n + 3) (by omega) wr (fun t h => h.1) []
    (.tuple #[.atom "open", .nil]) [] ⟨"open", [], rfl, Or.inl rfl, by simp⟩ (by simp)
  have each : ∀ L ∈ all, ∃ Q, Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1» (D (n + 2)) L =
      .ok (Term.list Q) ∧ (∀ q ∈ Q, Piece E q) ∧ ∀ w, (∃ q ∈ Q, PieceIn den q w) ↔ InLine den L w := by
    intro L mL
    obtain ⟨tag, l, negs, rfl, g, hl, lits⟩ := tl' L mL
    obtain ⟨b, check, -, empty⟩ := elements_exact ef.opsU ef.msemZ rfl l hl
    cases b
    · obtain ⟨Q, rQ, tQ, sQ⟩ := elim_negs (den := den) ef hn g hl negs lits
      refine ⟨Q, ?_, tQ, fun w => by rw [sQ, inLine_iff]⟩
      simp [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1», check (n + 2) (by omega), boolAtom,
        Lynx.Term.isMember, rQ]
    · refine ⟨[], ?_, by simp, fun w => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1», check (n + 2) (by omega), boolAtom,
          Lynx.Term.isMember, Term.list]
      · simp only [List.not_mem_nil, false_and, exists_false, false_iff]
        intro hv
        obtain ⟨hv, -⟩ := inLine_iff.mp hv
        obtain ⟨e, me, he⟩ := empty rfl
        obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem me
        obtain ⟨v₁, y, v₂, -, -, hy, -⟩ := (InT.mid l₁ e l₂).mp hv
        exact he y hy
  classical
  let h : Term → List Term := fun L => if hL : L ∈ all then Classical.choose (each L hL) else []
  have hh : ∀ L ∈ all, Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1» (D (n + 2)) L =
      .ok (Term.list (h L)) ∧ (∀ q ∈ h L, Piece E q) ∧ ∀ w, (∃ q ∈ h L, PieceIn den q w) ↔ InLine den L w := by
    intro L mL
    simp only [h, dite_eq_left mL]
    exact Classical.choose_spec (each L mL)
  have fm := flatmap_lists (m := n + 3) "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_no_negations/1-fun-0-" #[] h all
    (fun L mL => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_to_dnf_no_negations/1-fun-0-/1».pure]
      exact (hh L mL).1)
  obtain ⟨P, rd, sub, cover⟩ := dedup_run _ (all.flatMap h) (Nat.le_refl _)
  have pieces : ∀ q ∈ all.flatMap h, Piece E q := fun q mq => by
    obtain ⟨L, mL, mq⟩ := List.mem_flatMap.mp mq
    exact (hh L mL).2.1 q mq
  refine ⟨P, ?_, fun p mp => pieces p (sub p mp), fun w => ?_⟩
  · have run' : Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D (n + 3)) .nil (.tuple #[.atom "open", .nil]) .nil r =
        .ok (Term.list all) := by simpa using run
    simp [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1», run', fm, rd]
  · have hp : InPos den (.tuple #[.atom "open", .nil]) w := ⟨"open", [], rfl, InT.open_nil w⟩
    rw [← (by simpa [hp] using sl w : (∃ L ∈ all, InLine den L w) ↔ eval (valT E den w) r = Bool.true)]
    constructor
    · rintro ⟨p, mp, hp⟩
      obtain ⟨L, mL, mq⟩ := List.mem_flatMap.mp (sub p mp)
      exact ⟨L, mL, ((hh L mL).2.2 w).mp ⟨p, mq, hp⟩⟩
    · rintro ⟨L, mL, hL⟩
      obtain ⟨q, mq, hq⟩ := ((hh L mL).2.2 w).mpr hL
      have mq' : q ∈ all.flatMap h := List.mem_flatMap.mpr ⟨L, mL, mq⟩
      obtain ⟨p, mp, c⟩ := cover q mq'
      exact ⟨p, mp, pieceIn_congr ef.msemZ (pieces p (sub p mp)) (pieces q mq') (Lynx.Term.compare_eq_symm c) hq⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- `tuple_bdd_positive?/1` answers a boolean on BDDs. -/
theorem positive_run : ∀ (ok : Term → Prop) (b : Term), Bdd ok b →
    ∃ q : Bool, Elixir.Module.Types.Descr.«tuple_bdd_positive?/1» b = .ok (boolAtom q) := by
  refine Bdd.induction (P := fun _ b => ∃ q : Bool, Elixir.Module.Types.Descr.«tuple_bdd_positive?/1» b = .ok (boolAtom q))
    ?_ ?_ ?_ ?_
  · intro _; exact ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», boolAtom]⟩
  · intro _; exact ⟨Bool.true, by simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», boolAtom]⟩
  · intro _ k x y _; exact ⟨Bool.true, by simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», boolAtom]⟩
  · intro ok h lit c u d _ _ _ _ _ _ ⟨q, hq⟩ _
    by_cases shape : c = .atom "bdd_top" ∧ d = .atom "bdd_bot"
    · obtain ⟨rfl, rfl⟩ := shape
      exact ⟨q, by rw [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1».eq_def]; simpa using hq⟩
    · refine ⟨Bool.false, ?_⟩
      rw [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1».eq_def]
      split
      all_goals first
        | (rename_i heq; simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at heq; simp_all; done)
        | (simp_all [boolAtom]; done)
        | rfl

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem ins_exists {P : List Term} {Q : Term → List V → Prop} {i : Nat} {R : V → Prop} {w : List V} :
    Ins (fun u => ∃ p ∈ P, Q p u) i R w ↔ ∃ p ∈ P, Ins (Q p) i R w := by
  constructor
  · rintro ⟨w₁, y, w₂, e, len, hy, p, mp, h⟩; exact ⟨p, mp, w₁, y, w₂, e, len, hy, h⟩
  · rintro ⟨p, mp, w₁, y, w₂, e, len, hy, h⟩; exact ⟨w₁, y, w₂, e, len, hy, p, mp, h⟩

/-- The fold of `tuple_insert_static/3` inserts an element into each literal and unites them. -/
theorem insert_pieces (ef : EF nd E V den tl K) {x : Term} (hx : E x) (i : Nat) (P : List Term) (tP : ∀ p ∈ P, Piece E p)
    {m : Nat} {res : Term}
    (run : Erlang.lists.«foldl/3» (D m) (.function false "Elixir.Module.Types.Descr" "-tuple_insert_static/3-fun-0-" 2
      #[.integer i, x]) (.atom "bdd_bot") (Term.list P) = .ok res) :
    TField E res ∧ ∀ w, denTF E den res w = Bool.true ↔ ∃ p ∈ P, Ins (PieceIn den p) i (den x) w := by
  refine foldl_ok (m := m) _ _ _ (fun pre a => TField E a ∧ ∀ w, denTF E den a w = Bool.true ↔
      ∃ p ∈ pre, Ins (PieceIn den p) i (den x) w) P (fun pre p a a' mp ⟨ta, sa⟩ step => ?_) _
    ⟨Or.inr Bdd.bot, fun w => by simp [denTF_bot]⟩ res run
  obtain ⟨tag, l, rfl, g, hl⟩ := tP p mp
  rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_insert_static/3-fun-0-/2».pure] at step
  simp only [Elixir.Module.Types.Descr.«-tuple_insert_static/3-fun-0-/4»] at step
  cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l) (.integer i) x with
  | error _ => simp [hr] at step
  | ok r =>
    rw [hr, Lynx.Except.ok_bind] at step
    obtain ⟨fr, sr⟩ := insert_leaf (den := den) ef g hl hx i hr
    obtain ⟨u, ru, tu, su, -⟩ := tuple_union_lh (den := den) fr ta
    rw [ru] at step
    cases step
    refine ⟨tu, fun w => ?_⟩
    rw [su, Bool.or_eq_true, sr, sa]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | ⟨q, mq, hq⟩)
      · exact ⟨_, Or.inr rfl, (ins_congr fun u => pieceIn_iff).mpr h⟩
      · exact ⟨q, Or.inl mq, hq⟩
    · rintro ⟨q, mq | rfl, hq⟩
      · exact Or.inr ⟨q, mq, hq⟩
      · exact Or.inl ((ins_congr fun u => pieceIn_iff).mp hq)

/-- `tuple_insert_static/3` inserts an element into the tuple field of a map. -/
theorem insert_static (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "tuple") = some b) (fb : TField E b) {x : Term} (hx : E x) (i : Nat) {res : Term}
    (run : Elixir.Module.Types.Descr.«tuple_insert_static/3» (D (n + 3)) (.map X) (.integer i) x = .ok res) :
    ∃ b', res = .map ((.atom "tuple", b') :: X) ∧ TField E b' ∧
      ∀ w, denTF E den b' w = Bool.true ↔ Ins (fun u => denTF E den b u = Bool.true) i (den x) w := by
  have upd : ∀ b', Erlang.maps.«update/3» (.atom "tuple") b' (.map X) = .ok (.map ((.atom "tuple", b') :: X)) := by
    intro b'
    have : (X.find? fun entry => decide (compareExact (fuel (.atom "tuple") entry.1) (.atom "tuple") entry.1 = .eq)).isSome := by
      have := congrArg Option.isSome hb
      simpa [mapLookup] using this
    simp [Erlang.maps.«update/3», this]
  -- The positive path, on any tuple field.
  have positive : ∀ (ok : Term → Prop), Bdd ok b → (∀ t, ok t → TupleLit E t) → (∀ w, denTF E den b w = eval (valT E den w) b) →
      ∀ r, Elixir.Module.Types.Descr.«tuple_insert_leaves/4» b (.integer i) x (.atom "bdd_bot") = .ok r →
      TField E r ∧ ∀ w, denTF E den r w = Bool.true ↔ Ins (fun u => denTF E den b u = Bool.true) i (den x) w := by
    intro ok wb okT same r hr
    obtain ⟨tr, sr⟩ := insert_leaves (den := den) ef hx i ok b wb okT (.atom "bdd_bot") r (Or.inr Bdd.bot) hr
    refine ⟨tr, fun w => ?_⟩
    rw [sr, denTF_bot]
    simp only [Bool.false_eq_true, false_or]
    exact ins_congr fun u => by rw [same u]
  rcases fb with ⟨k, rfl⟩ | wb
  · simp only [Elixir.Module.Types.Descr.«tuple_insert_static/3», getMapKeys_single, hb, Option.toList_some] at run
    simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», Lynx.Term.isMember, Lynx.Except.guard] at run
    cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaves/4» (.tuple #[.integer k, .atom "open", .nil]) (.integer i) x
        (.atom "bdd_bot") with
    | error _ => simp [hr] at run
    | ok r =>
      simp [hr, Erlang.erlang.«is_map/1», upd] at run
      subst run
      have lit : TupleLit E (.tuple #[.integer k, .atom "open", .nil]) := ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩
      obtain ⟨tr, sr⟩ := positive (TupleLit E) (Bdd.leaf_iff.mpr lit) (fun t h => h) (fun w => by
        rw [denTF_top, eval_leaf]
        have := (vT_lit (den := den) (v := w) ef (Or.inl rfl) (l := []) (k := k) (by simp)).mpr (InT.open_nil w)
        exact this.symm) r hr
      exact ⟨r, rfl, tr, sr⟩
  · obtain ⟨q, rq⟩ := positive_run _ b wb
    have hb' : Lynx.Term.getMapKeys [.atom "tuple"] (.map X) = [b] := by simp [getMapKeys_single, hb]
    cases q
    · obtain ⟨P, rP, tP, sP⟩ := no_negs (den := den) ef hn wb
      unfold Elixir.Module.Types.Descr.«tuple_insert_static/3» at run
      simp only [hb', rq, rP] at run
      simp [Lynx.Term.isMember, Lynx.Except.guard, boolAtom] at run
      cases hr : Erlang.lists.«foldl/3» (D (n + 3))
          (.function false "Elixir.Module.Types.Descr" "-tuple_insert_static/3-fun-0-" 2 #[.integer i, x]) (.atom "bdd_bot")
          (Term.list P) with
      | error _ => simp [hr] at run
      | ok r =>
        simp [hr, Erlang.erlang.«is_map/1», upd] at run
        subst run
        obtain ⟨tr, sr⟩ := insert_pieces (den := den) ef hx i P tP hr
        refine ⟨r, rfl, tr, fun w => ?_⟩
        rw [sr, ← ins_exists]
        exact ins_congr fun u => by rw [sP u, denTF_bdd wb]
    · unfold Elixir.Module.Types.Descr.«tuple_insert_static/3» at run
      simp only [hb', rq] at run
      simp [Lynx.Term.isMember, Lynx.Except.guard, boolAtom] at run
      cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaves/4» b (.integer i) x (.atom "bdd_bot") with
      | error _ => simp [hr] at run
      | ok r =>
        simp [hr, Erlang.erlang.«is_map/1», upd] at run
        subst run
        obtain ⟨tr, sr⟩ := positive (TLit E) wb (fun t h => h.1.1) (fun w => denTF_bdd wb w) r hr
        exact ⟨r, rfl, tr, sr⟩

end

theorem lookup_put (X : List (Term × Term)) (b' : Term) (name : String) :
    mapLookup ((.atom "tuple", b') :: X) (.atom name) = if name = "tuple" then some b' else mapLookup X (.atom name) := by
  by_cases h : name = "tuple" <;> simp [mapLookup, h]

theorem descrC_put {Fn TF LF MF : Term → Prop} {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {b' : Term}
    (tb : TF b') : DescrC Fn TF LF MF ((.atom "tuple", b') :: X) where
  keys q h := by
    by_cases e : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · have : (mapLookup X q).isSome := by simpa [mapLookup, List.find?_cons, e] using h
      exact sX.keys q this
  fields name x h := by
    rw [lookup_put] at h
    split at h
    · rename_i e; subst e
      simp only [Option.some.injEq] at h; subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tb⟩))))
    · exact sX.fields name x h

theorem size_map (d : Dispatcher) {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "tuple") = some b)
    (i : Term) : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» d (.map X) i =
      Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» d (.map [(.atom "tuple", b)]) i := by
  unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
  simp only [getMapKeys_single, hb, Option.toList_some]
  simp [mapLookup]

section
variable {t : Term} {n : Nat}

/-- `tuple_insert_at_checked/3` on static types of the next level: when it gives a type, the input holds only tuples,
all long enough, and the result holds those tuples with a value of the element inserted. -/
theorem insert_tuple {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {x : Term} (hx : (level t n).E x) (i : Nat)
    {m : Nat} (hm : (level t n).K + 25 ≤ m) {Y : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok (.map Y)) :
    TOnly t n X ∧ (∀ w, TT t n X w → i ≤ List.length w) ∧ DE (level t n).E (.map Y) ∧
      (∀ v : PN t n, denD (.map Y) v → v.1.1 = "tuple") ∧ ∀ w, TT t n Y w ↔ Ins (TT t n X) i ((level t n).den x) w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  have ef := (level t n).ef
  unfold Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» at run
  simp only [Erlang.maps.«take/2», sX.static, Lynx.Except.ok_bind] at run
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    exfalso
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
      Lynx.Except.guard] at run
    split at run
    · simp [Erlang.erlang.«/=/2»] at run
    · cases h : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map X) (.integer i) <;>
        simp [h, Erlang.erlang.«/=/2»] at run
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
    obtain ⟨dR, sR⟩ := rest_tuple hX
    have rE := next_empty dR (m := k + 3) (by omega)
    obtain ⟨eb, reb, seb⟩ := tuple_empty_exact (level t n).ef fb []
    have seb := seb (lh b + 1) (by omega) (safeT_nil _)
    have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
    have only : TOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmT X)) v) ∧ eb = Bool.false := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        refine ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), ?_⟩
        cases eb
        · rfl
        · have := seb.mp rfl w; rw [(tt w).mp hw] at this; cases this
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), ?_⟩
        obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt seb.mpr (by simp [h₂]))
        exact ⟨w, (tt w).mpr (by simpa using hw)⟩
    have nonEmpty : Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D (k + 3)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb)) := by
      simp only [Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Erlang.maps.«take/2», hb, equalExact_eq_decide]
      rw [show (List.filter (fun entry => !decide (compareExact (fuel (.atom "tuple") entry.fst) (.atom "tuple") entry.fst = .eq)) X) = rmT X from rfl]
      simp only [Lynx.Except.ok_bind, rE, reb (k + 3) (by omega)]
      cases bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) <;> cases eb <;>
        simp [Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom]
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    -- The size check.
    obtain ⟨sz, rsz, ssz⟩ : ∃ sz : Bool, Lynx.Except.orElse (Erlang.erlang.«==/2» (.integer i) (.integer 0))
        (Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map X) (.integer i)) = .ok (boolAtom sz) ∧
        (sz = Bool.true → ∀ w, TT t n X w → i ≤ List.length w) := by
      by_cases z : i = 0
      · subst z
        exact ⟨Bool.true, by simp [Lynx.Except.orElse, Erlang.erlang.«==/2», boolAtom], fun _ w _ => Nat.zero_le _⟩
      · obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := k + 3) (by omega) fb i (by omega)
        refine ⟨sz, ?_, fun h w hw => ss.mp h w ((tt w).mp hw)⟩
        have eq0 : Erlang.erlang.«==/2» (.integer (i : Int)) (.integer 0) = .ok (.atom "false") := by
          simp [Erlang.erlang.«==/2»]; omega
        rw [size_map _ hb, eq0]
        simpa [Lynx.Except.orElse] using rs
    obtain ⟨c, rc, sc⟩ : ∃ c : Bool, Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D (k + 3)) (.map X) =
        .ok (boolAtom c) ∧ (c = Bool.true → TOnly t n X) := by
      refine ⟨_, nonEmpty, fun h => only.mpr ?_⟩
      simp only [Bool.and_eq_true, bp_true, Bool.not_eq_true'] at h
      exact h
    simp only [key, rc, rsz] at run
    cases c <;> cases sz <;>
      simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure] at run
    have onlyX := sc rfl
    obtain ⟨b', e, tb', sb'⟩ := insert_static (den := (level t n).den) (level t n).ef (n := k) (by omega) hb fb hx i run
    simp only [Term.map.injEq] at e
    subst e
    have ttY : ∀ w, TT t n ((.atom "tuple", b') :: X) w ↔ denTF (level t n).E (level t n).den b' w = Bool.true :=
      fun w => by simp [TT, lookup_put]
    refine ⟨onlyX, ssz rfl, Or.inr ⟨_, rfl, descrC_put sX tb'⟩, fun v hv => ?_, fun w => ?_⟩
    · by_cases h : v.1.1 = "tuple"
      · exact h
      · apply onlyX.1 v
        rw [denD_map] at hv ⊢
        rwa [lookup_put, ite_eq_right h] at hv
    · rw [ttY, sb']
      exact ins_congr fun u => (tt u).symm

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- `tuple_insert_at/3` checks static element types right away. -/
theorem insert_at_static (d : Dispatcher) (X : List (Term × Term)) (i : Nat) {x : Term}
    (sx : x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«tuple_insert_at/3» d (.map X) (.integer i) x =
      Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» d (.map X) (.integer i) x := by
  rcases sx with rfl | ⟨Z, rfl, sZ⟩
  · rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
    simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
      Elixir.Module.Types.Descr.«unfolded_term/0», Erlang.maps.«take/2», mapLookup]
  · rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
    simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
      Erlang.maps.«take/2», sZ]

theorem insert_at_neg (d : Dispatcher) (X : List (Term × Term)) (x : Term) {z : Int} (h : z < 0) :
    Elixir.Module.Types.Descr.«tuple_insert_at/3» d (.map X) (.integer z) x = .ok (.atom "badindex") := by
  have : ¬0 ≤ z := by omega
  rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
  simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare, this]

theorem insert_at_term (d : Dispatcher) (i x : Term) :
    Elixir.Module.Types.Descr.«tuple_insert_at/3» d (.atom "term") i x = .ok (.atom "badtuple") := by
  rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
  rfl

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `equal?/2` holds on element types with the same values. -/
theorem elem_equal (ef : EF nd E V den tl K) {a b : Term} (ha : E a) (hb : E b) (h : ∀ v, den a v ↔ den b v) {m : Nat}
    (hm : K ≤ m) : Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (.atom "true") := by
  have s₁ := ef.subc ha hb (fun v => (h v).mp) m hm
  have s₂ := ef.subc hb ha (fun v => (h v).mpr) m hm
  simp only [Elixir.Module.Types.Descr.«equal?/2», s₁, s₂, Lynx.Except.orElse, Lynx.Except.andAlso, Erlang.erlang.«==/2», equal_eq_decide]
  split <;> simp_all

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Deleting elements from tuple types: the remaining tuples of each line at an index. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `tuple_pair_projection_keeps_full_snd?/2` checks for a value outside every negated pair. -/
theorem keeps_snd (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (P : List Term) (hP : ∀ p ∈ P, PairOk E p)
    {value : Term} (hv : E value) : ∃ s : Bool,
      Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_snd?/2» (D (n + 1)) (Term.list P) value =
        .ok (boolAtom s) ∧
      (s = Bool.true ↔ ∃ y, den value y ∧ ∀ p ∈ P, ∀ f nb, p = .tuple #[f, nb] → ¬den f y) := by
  obtain ⟨u, ⟨hu, su⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr"
    "-tuple_pair_projection_keeps_full_snd?/2-fun-0-" #[]
    (fun pre a => E a ∧ ∀ y, den a y ↔ ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ den f y) P
    (fun pre x a mx ⟨ha, sa⟩ => by
      obtain ⟨f, b, rfl, hf, -⟩ := hP x mx
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hf ha hn
      refine ⟨c, ⟨hc, fun y => ?_⟩, ?_⟩
      · rw [sc, sa]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, by simp, f, b, rfl, h⟩
          · exact ⟨p, by simp [mp], h⟩
        · rintro ⟨p, mp, f', b', e, h⟩
          simp only [List.mem_append, List.mem_singleton] at mp
          rcases mp with mp | rfl
          · exact Or.inr ⟨p, mp, f', b', e, h⟩
          · simp only [Term.tuple.injEq] at e
            obtain ⟨rfl, rfl, -⟩ := e
            exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_pair_projection_keeps_full_snd?/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_pair_projection_keeps_full_snd?/2-fun-0-/2»,
          Elixir.Module.Types.Descr.«opt_union/2»] using rc)
    (.map []) ⟨ef.none, fun y => by simp [ef.den_none y]⟩
  obtain ⟨d, hd, rd, sd⟩ := ef.opt_diff [] hv hu (show K ≤ n + 1 by omega)
  obtain ⟨e, re, se⟩ := empty_bool ef hd (show K ≤ n + 1 by omega)
  refine ⟨!e, ?_, ?_⟩
  · cases e <;> simp [Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_snd?/2», run,
      Elixir.Module.Types.Descr.«opt_difference/2», rd, re, Erlang.erlang.«not/1», boolAtom]
  · cases e
    · simp only [Bool.not_false, true_iff]
      obtain ⟨y, hy⟩ := Classical.not_forall.mp (mt se.mpr (by simp))
      rw [Classical.not_not, sd, su] at hy
      refine ⟨y, hy.1, fun p mp f nb e hf => hy.2 ⟨p, mp, f, nb, e, hf⟩⟩
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro y hy none
      have := (se.mp rfl) y
      rw [sd, su] at this
      apply this ⟨hy, ?_⟩
      rintro ⟨p, mp, f, nb, e, hf⟩
      exact none p mp f nb e hf

/-- The tuples of a line without the element at an index. -/
def Proj (den : Term → V → Prop) (L : Term) (i : Nat) (w : List V) : Prop :=
  ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ List.length v₁ = i ∧ InLine den L (v₁ ++ y :: v₂)

theorem split_at {i : Nat} {w : List V} (h : i ≤ w.length) : ∃ w₁ w₂, w = w₁ ++ w₂ ∧ List.length w₁ = i :=
  ⟨w.take i, w.drop i, by simp, by simp; omega⟩

/-- One step of `tuple_delete_static/2`: a line without the element at an index, united with the accumulator. -/
theorem delete_step (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (i : Nat) {L : Term} (hL : TLine E L)
    (ne : ∃ v, InLine den L v ∧ i < List.length v) {acc : Term} (ha : TField E acc) :
    ∃ r, Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-1-/3» (D (n + 2)) (.integer i) L acc = .ok r ∧
      TField E r ∧ ∀ w, denTF E den r w = Bool.true ↔ denTF E den acc w = Bool.true ∨ Proj den L i w := by
  obtain ⟨tag, l, negs, rfl, g, hl, lits⟩ := hL
  obtain ⟨res, rt, ⟨rfl, none⟩ | ⟨⟨value, rest, rfl, hv, hr⟩, nemp, lng, sem⟩⟩ := take_pair (den := den) ef g hl i
  · -- No tuple of the line is long enough: there are none.
    exfalso
    obtain ⟨v, hv, lt⟩ := ne
    obtain ⟨hv, -⟩ := inLine_iff.mp hv
    obtain ⟨v₁, v₂, rfl, l₁⟩ := split_at (w := v) (i := i) (by omega)
    cases v₂ with
    | nil => simp at lt; omega
    | cons y v₂ => exact none v₁ y v₂ l₁ hv
  -- The values and remaining tuples of the line are not empty.
  obtain ⟨y₀, w₀, hy₀, hw₀⟩ : ∃ y w, den value y ∧ denTF E den rest w = Bool.true := by
    obtain ⟨v, hv, lt⟩ := ne
    obtain ⟨hv, -⟩ := inLine_iff.mp hv
    obtain ⟨v₁, v₂, rfl, l₁⟩ := split_at (w := v) (i := i) (by omega)
    cases v₂ with
    | nil => simp at lt; omega
    | cons y v₂ => exact ⟨y, _, pairIn_iff.mp ((sem v₁ y v₂ l₁).mp hv)⟩
  have restLong : ∀ w, denTF E den rest w = Bool.true → i ≤ List.length w := fun w h => lng y₀ w (pairIn_iff.mpr ⟨hy₀, h⟩)
  cases negs with
  | nil =>
    obtain ⟨r, rr, tr, sr⟩ := opt_tuple_union_sem ef (m := n + 2) (by omega) hr ha
    refine ⟨r, ?_, tr, fun w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-1-/3», rt, rr]
    · rw [sr, Bool.or_eq_true, or_comm]
      refine or_congr Iff.rfl ⟨fun h => ?_, fun ⟨v₁, y, v₂, e, l₁, h⟩ => ?_⟩
      · obtain ⟨w₁, w₂, rfl, l₁⟩ := split_at (restLong w h)
        exact ⟨w₁, y₀, w₂, rfl, l₁, inLine_iff.mpr ⟨(sem w₁ y₀ w₂ l₁).mpr (pairIn_iff.mpr ⟨hy₀, h⟩), by simp⟩⟩
      · subst e
        exact (pairIn_iff.mp ((sem v₁ y v₂ l₁).mp (inLine_iff.mp h).1)).2
  | cons N negs =>
    obtain ⟨P, rP, okP, semP⟩ := split_pairs (den := den) ef (N :: negs) lits i (m := n + 2)
    obtain ⟨s, rs, ss⟩ := keeps_snd (den := den) ef (n := n + 1) (by omega) P okP hv
    have line : ∀ v₁ y v₂, List.length v₁ = i → (InLine den (.tuple #[.atom tag, Term.list l, Term.list (N :: negs)])
        (v₁ ++ y :: v₂) ↔ (den value y ∧ denTF E den rest (v₁ ++ v₂) = Bool.true) ∧
          ¬∃ p ∈ P, PairIn E den p y (v₁ ++ v₂)) := by
      intro v₁ y v₂ l₁
      rw [inLine_iff, sem v₁ y v₂ l₁, pairIn_iff, ← semP v₁ y v₂ l₁]
      simp only [not_exists, not_and]
    cases s
    · obtain ⟨Q, rQ, qQ, sQ, fQ⟩ := project_pairs ef hn P okP hv hr ⟨w₀, hw₀⟩
      have fQ := fQ ⟨y₀, hy₀⟩
      obtain ⟨u, ⟨tu, su⟩, ru⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr" "-tuple_delete_static/2-fun-0-" #[]
        (fun pre a => TField E a ∧ ∀ w, denTF E den a w = Bool.true ↔
          denTF E den acc w = Bool.true ∨ ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ denTF E den b w = Bool.true) Q
        (fun pre x a mx ⟨ta, sa⟩ => by
          obtain ⟨f, b, rfl, -, hb, -⟩ := qQ x mx
          obtain ⟨c, rc, tc, sc⟩ := opt_tuple_union_sem ef (m := n + 1) (by omega) hb ta
          refine ⟨c, ⟨tc, fun w => ?_⟩, ?_⟩
          · rw [sc, Bool.or_eq_true, sa]
            constructor
            · rintro (h | h | ⟨p, mp, h⟩)
              · exact Or.inr ⟨_, by simp, f, b, rfl, h⟩
              · exact Or.inl h
              · exact Or.inr ⟨p, by simp [mp], h⟩
            · rintro (h | ⟨p, mp, f', b', e, h⟩)
              · exact Or.inr (Or.inl h)
              simp only [List.mem_append, List.mem_singleton] at mp
              rcases mp with mp | rfl
              · exact Or.inr (Or.inr ⟨p, mp, f', b', e, h⟩)
              · simp only [Term.tuple.injEq] at e
                obtain ⟨rfl, rfl, -⟩ := e
                exact Or.inl h
          · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_delete_static/2-fun-0-/2».pure]
            simpa [Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-0-/2»] using rc)
        acc ⟨ha, fun w => by simp⟩
      refine ⟨u, ?_, tu, fun w => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-1-/3», Term.list, rt, rP, rs, rQ, ru, boolAtom,
          Lynx.Term.isMember]
      · rw [su]
        refine or_congr Iff.rfl ⟨fun ⟨p, mp, f, b, e, h⟩ => ?_, fun ⟨v₁, y, v₂, e, l₁, h⟩ => ?_⟩
        · subst e
          obtain ⟨f', b', e, y, hy⟩ := fQ _ mp
          simp only [Term.tuple.injEq] at e
          obtain ⟨rfl, rfl, -⟩ := e
          obtain ⟨h₁, h₂, h₃⟩ := (sQ y w).mp ⟨_, mp, pairIn_iff.mpr ⟨hy, h⟩⟩
          obtain ⟨w₁, w₂, rfl, l₁⟩ := split_at (restLong w h₂)
          exact ⟨w₁, y, w₂, rfl, l₁, (line w₁ y w₂ l₁).mpr ⟨⟨h₁, h₂⟩, fun ⟨p, mp, hp⟩ => h₃ p mp hp⟩⟩
        · subst e
          obtain ⟨⟨h₁, h₂⟩, h₃⟩ := (line v₁ y v₂ l₁).mp h
          obtain ⟨p, mp, f, b, rfl, -, hb⟩ := (sQ y (v₁ ++ v₂)).mpr ⟨h₁, h₂, fun p mp hp => h₃ ⟨p, mp, hp⟩⟩
          exact ⟨_, mp, f, b, rfl, hb⟩
    · obtain ⟨y, hy, out⟩ := ss.mp rfl
      obtain ⟨r, rr, tr, sr⟩ := opt_tuple_union_sem ef (m := n + 2) (by omega) hr ha
      refine ⟨r, ?_, tr, fun w => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-1-/3», Term.list, rt, rP, rs, rr, boolAtom,
          Lynx.Term.isMember]
      · rw [sr, Bool.or_eq_true, or_comm]
        refine or_congr Iff.rfl ⟨fun h => ?_, fun ⟨v₁, y', v₂, e, l₁, h'⟩ => ?_⟩
        · obtain ⟨w₁, w₂, rfl, l₁⟩ := split_at (restLong w h)
          refine ⟨w₁, y, w₂, rfl, l₁, (line w₁ y w₂ l₁).mpr ⟨⟨hy, h⟩, fun ⟨p, mp, hp⟩ => ?_⟩⟩
          obtain ⟨f, nb, e, hf, -⟩ := hp
          exact out p mp f nb e hf
        · subst e
          exact ((line v₁ y' v₂ l₁).mp h').1.2

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `tuple_delete_static/2` removes the element at an index from every tuple of a tuple type with long tuples. -/
theorem delete_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) {Y : List (Term × Term)} {b : Term}
    (hb : mapLookup Y (.atom "tuple") = some b) (wb : Bdd (TLit E) b) (i : Nat)
    (long : ∀ v, denTF E den b v = Bool.true → i < List.length v) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_delete_static/2» (D (n + 3)) (.map Y) (.integer i) =
        .ok (.map [(.atom "tuple", r)]) ∧ TField E r ∧
      ∀ w, denTF E den r w = Bool.true ↔ ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ List.length v₁ = i ∧ denTF E den b (v₁ ++ y :: v₂) = Bool.true := by
  obtain ⟨lines, rl, tl', sl⟩ := dnf_neg (den := den) ef.opsU ef.dopsU ef.msemZ rfl (m := n + 3) (by omega) wb
  have inB : ∀ v, denTF E den b v = Bool.true ↔ ∃ L ∈ lines, InLine den L v := fun v => by rw [denTF_bdd wb]; exact sl v
  obtain ⟨r, ⟨tr, sr⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr" "-tuple_delete_static/2-fun-1-"
    #[.integer i] (fun pre a => TField E a ∧ ∀ w, denTF E den a w = Bool.true ↔ ∃ L ∈ pre, Proj den L i w) lines
    (fun pre L a mL ⟨ta, sa⟩ => by
      obtain ⟨hL, v, hv⟩ := tl' L mL
      obtain ⟨c, rc, tc, sc⟩ := delete_step (den := den) ef hn i hL ⟨v, hv, long v ((inB v).mpr ⟨L, mL, hv⟩)⟩ ta
      refine ⟨c, ⟨tc, fun w => ?_⟩, ?_⟩
      · rw [sc, sa]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨L', mL', h⟩ | h)
          · exact ⟨L', Or.inl mL', h⟩
          · exact ⟨L, Or.inr rfl, h⟩
        · rintro ⟨L', mL' | rfl, h⟩
          · exact Or.inl ⟨L', mL', h⟩
          · exact Or.inr h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_delete_static/2-fun-1-/2».pure]
        exact rc)
    (.atom "bdd_bot") ⟨Or.inr Bdd.bot, fun w => by simp [denTF_bot]⟩
  refine ⟨r, ?_, tr, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«tuple_delete_static/2»
    simp [getMapKeys_single, hb, rl, run]
  · rw [sr]
    constructor
    · rintro ⟨L, mL, v₁, y, v₂, rfl, l₁, h⟩
      exact ⟨v₁, y, v₂, rfl, l₁, (inB _).mpr ⟨L, mL, h⟩⟩
    · rintro ⟨v₁, y, v₂, rfl, l₁, h⟩
      obtain ⟨L, mL, hL⟩ := (inB _).mp h
      exact ⟨L, mL, v₁, y, v₂, rfl, l₁, hL⟩

end

section
variable {t : Term} {n : Nat}

/-- `non_empty_tuple_only?/1` decides whether a static type of the next level holds only tuples, and some. -/
theorem only_run {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {b : Term}
    (hb : mapLookup X (.atom "tuple") = some b) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ c : Bool, Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D m) (.map X) = .ok (boolAtom c) ∧
      (c = Bool.true ↔ TOnly t n X) := by
  have sX := de_map hX
  have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
  obtain ⟨dR, sR⟩ := rest_tuple hX
  have rE := next_empty dR (m := m) hm
  obtain ⟨eb, reb, seb⟩ := tuple_empty_exact (level t n).ef fb []
  have seb := seb (lh b + 1) (by omega) (safeT_nil _)
  have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
  have only : TOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmT X)) v) ∧ eb = Bool.false := by
    constructor
    · rintro ⟨h₁, w, hw⟩
      refine ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), ?_⟩
      cases eb
      · rfl
      · have := seb.mp rfl w; rw [(tt w).mp hw] at this; cases this
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), ?_⟩
      obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt seb.mpr (by simp [h₂]))
      exact ⟨w, (tt w).mpr (by simpa using hw)⟩
  refine ⟨bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb, ?_, ?_⟩
  · simp only [Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Erlang.maps.«take/2», hb, equalExact_eq_decide]
    rw [show (List.filter (fun entry => !decide (compareExact (fuel (.atom "tuple") entry.fst) (.atom "tuple") entry.fst = .eq)) X) = rmT X from rfl]
    simp only [Lynx.Except.ok_bind, rE, reb m (by rw [level_K] at hm ⊢; omega)]
    cases bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) <;> cases eb <;>
      simp [Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom]
  · rw [only]
    simp only [Bool.and_eq_true, bp_true, Bool.not_eq_true']

/-- `tuple_delete_at/2` on static types of the next level holding only tuples, all longer than an index: the tuples
without the element at the index. -/
theorem delete_tuple {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) (onlyY : TOnly t n Y) (i : Nat)
    (long : ∀ w, TT t n Y w → i < List.length w) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map Y) (.integer i) = .ok (.map [(.atom "tuple", r)]) ∧
      TField (level t n).E r ∧ ∀ w, denTF (level t n).E (level t n).den r w = Bool.true ↔
        ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ List.length v₁ = i ∧ TT t n Y (v₁ ++ y :: v₂) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sY := de_map hY
  obtain ⟨w₀, b, hb, -⟩ := onlyY.2
  have fb : TField (level t n).E b := fieldC_tuple (sY.fields "tuple" b hb)
  have tt : ∀ w, TT t n Y w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
  have wb : Bdd (TLit (level t n).E) b := by
    rcases fb with ⟨k', rfl⟩ | wb
    · have := long [] ((tt []).mpr (denTF_top _ _)); simp at this
    · exact wb
  obtain ⟨c, rc, sc⟩ := only_run hY hb (m := k + 3) (by omega)
  have c_true : c = Bool.true := sc.mpr onlyY
  subst c_true
  obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := k + 3) (by omega) fb (i + 1) (by omega)
  have sz_true : sz = Bool.true := ss.mpr fun v hv => long v ((tt v).mpr hv)
  subst sz_true
  obtain ⟨r, rr, tr, sr⟩ := delete_static (den := (level t n).den) (level t n).ef (n := k) (by omega) hb wb i
    fun v hv => long v ((tt v).mpr hv)
  have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map Y) (.atom "tuple") = .ok (.atom "true") := by
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
  refine ⟨r, ?_, tr, fun w => by rw [sr]; simp only [tt]⟩
  have rs' : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map [(.atom "tuple", b)])
      (.integer ((i : Int) + 1)) = .ok (boolAtom Bool.true) := by simpa using rs
  rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def]
  simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
    Erlang.maps.«take/2», sY.static, key, rc, size_map _ hb, rs', boolAtom, Erlang.erlang.«/=/2», rr]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Deleting and replacing elements of tuple types, and fetching from the results. -/

section
variable {V : Type}

/-- Lists split around an index are lists with the element at the index erased. -/
theorem split_erase {P : List V → Prop} {i : Nat} {w : List V} :
    (∃ v₁ y v₂, w = v₁ ++ v₂ ∧ List.length v₁ = i ∧ P (v₁ ++ y :: v₂)) ↔ ∃ x, P x ∧ i < List.length x ∧ w = x.eraseIdx i := by
  constructor
  · rintro ⟨v₁, y, v₂, rfl, rfl, h⟩
    refine ⟨_, h, by simp, ?_⟩
    rw [List.eraseIdx_append_of_length_le (Nat.le_refl _)]
    simp
  · rintro ⟨x, h, lx, rfl⟩
    refine ⟨x.take i, x[i], x.drop (i + 1), ?_, by simp; omega, by simpa using h⟩
    rw [List.eraseIdx_eq_take_drop_succ]

/-- Lists with a value inserted at an index. -/
theorem ins_insert {P : List V → Prop} {i : Nat} {Q : V → Prop} {w : List V} :
    Ins P i Q w ↔ ∃ x y, P x ∧ i ≤ List.length x ∧ Q y ∧ w = x.take i ++ y :: x.drop i := by
  constructor
  · rintro ⟨w₁, y, w₂, rfl, rfl, hy, h⟩
    exact ⟨_, y, h, by simp, hy, by simp⟩
  · rintro ⟨x, y, h, lx, hy, rfl⟩
    exact ⟨x.take i, y, x.drop i, rfl, by simp; omega, hy, by simpa using h⟩

theorem insert_length {x : List V} {i : Nat} (lx : i ≤ x.length) (y : V) :
    (x.take i ++ y :: x.drop i).length = x.length + 1 := by
  simp; omega

theorem insert_getElem {x : List V} {i : Nat} (lx : i ≤ x.length) (y : V) (o : Nat) :
    (x.take i ++ y :: x.drop i)[o]? = if o < i then x[o]? else if o = i then some y else x[o - 1]? := by
  have lt : (x.take i).length = i := by simp; omega
  split
  · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt (by omega)]
  · rw [List.getElem?_append_right (by omega), lt]
    split
    · subst_vars; simp
    · obtain ⟨k, hk⟩ : ∃ k, o - i = k + 1 := ⟨o - i - 1, by omega⟩
      rw [hk, List.getElem?_cons_succ, List.getElem?_drop]
      congr 1; omega

/-- Values at an index of lists, through lookups. -/
theorem split_getElem {P : List V → Prop} {i : Nat} {y : V} :
    (∃ v₁ v₂, List.length v₁ = i ∧ P (v₁ ++ y :: v₂)) ↔ ∃ w, P w ∧ w[i]? = some y := by
  constructor
  · rintro ⟨v₁, v₂, rfl, h⟩
    exact ⟨_, h, by simp⟩
  · rintro ⟨w, h, hy⟩
    obtain ⟨lw, e⟩ := List.getElem?_eq_some_iff.mp hy
    refine ⟨w.take i, w.drop (i + 1), by simp; omega, ?_⟩
    rw [← e, ← List.drop_eq_getElem_cons lw]
    simpa using h

/-- Inserting a value where an element was erased sets the element. -/
theorem erase_insert {x : List V} {i : Nat} (lx : i < x.length) (y : V) :
    (x.eraseIdx i).take i ++ y :: (x.eraseIdx i).drop i = x.set i y := by
  have le : i ≤ (x.eraseIdx i).length := by rw [List.length_eraseIdx]; split <;> omega
  apply List.ext_getElem?
  intro o
  rw [insert_getElem le, List.getElem?_set]
  by_cases hoi : o < i
  · simp only [hoi, ↓reduceIte, List.getElem?_eraseIdx_of_lt hoi, show i ≠ o by omega]
  · simp only [hoi, ↓reduceIte]
    by_cases e : o = i
    · subst e; simp [lx]
    · simp only [e, Ne.symm e, ↓reduceIte]
      rw [List.getElem?_eraseIdx_of_ge (show i ≤ o - 1 by omega)]
      congr 1; omega

end


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `tuple_insert_leaf/4` gives a tuple field on any literal. -/
theorem insert_leaf_ok (ef : EF nd E V den tl K) {tag : String} (g : tag = "open" ∨ tag = "closed") {l : List Term}
    (hl : ∀ e ∈ l, E e) {x : Term} (hx : E x) (i : Nat) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l) (.integer i) x = .ok r ∧
      TField E r ∧ ∀ w, denTF E den r w = Bool.true ↔ Ins (InT den (tag == "closed") l) i (den x) w := by
  rcases insert_leaf_run g l i x with ⟨-, -, run⟩ | ⟨-, k, run, -⟩
  · exact ⟨_, run, insert_leaf ef g hl hx i run⟩
  · exact ⟨_, run, insert_leaf ef g hl hx i run⟩

/-- `tuple_insert_leaves/4` gives a type on the unions of literals `tuple_bdd_positive?/1` accepts. -/
theorem insert_leaves_ok (ef : EF nd E V den tl K) {x : Term} (hx : E x) (i : Nat) :
    ∀ (ok : Term → Prop) (r : Term), Bdd ok r → (∀ t, ok t → TupleLit E t) →
      Elixir.Module.Types.Descr.«tuple_bdd_positive?/1» r = .ok (boolAtom Bool.true) → ∀ acc, TField E acc →
      ∃ res, Elixir.Module.Types.Descr.«tuple_insert_leaves/4» r (.integer i) x acc = .ok res := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleLit E t) →
      Elixir.Module.Types.Descr.«tuple_bdd_positive?/1» r = .ok (boolAtom Bool.true) → ∀ acc, TField E acc →
      ∃ res, Elixir.Module.Types.Descr.«tuple_insert_leaves/4» r (.integer i) x acc = .ok res) ?_ ?_ ?_ ?_
  · intro ok _ pos acc _
    simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», boolAtom] at pos
  · intro ok _ _ acc _
    exact ⟨acc, by simp [Elixir.Module.Types.Descr.«tuple_insert_leaves/4», pure, Except.pure]⟩
  · intro ok k a b okl okLit _ acc ha
    obtain ⟨k', tag, l, e, g, hl⟩ := okLit _ okl
    rw [e]
    obtain ⟨r, rr, fr, -⟩ := insert_leaf_ok (den := den) ef g hl hx i
    obtain ⟨u, ru, -⟩ := tuple_union_lh (den := den) fr ha
    exact ⟨u, by simp [Elixir.Module.Types.Descr.«tuple_insert_leaves/4», rr, ru]⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos acc ha
    have okLit' : ∀ t, Above ok lit t → TupleLit E t := fun t ht => okLit t ht.1
    obtain ⟨k', tag, l, rfl, g, hl⟩ := okLit _ okl
    by_cases shape : c = .atom "bdd_top" ∧ d = .atom "bdd_bot"
    · obtain ⟨rfl, rfl⟩ := shape
      rw [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1».eq_def] at pos
      simp only at pos
      obtain ⟨r, rr, fr, -⟩ := insert_leaf_ok (den := den) ef g hl hx i
      obtain ⟨a, ra, ta, -⟩ := tuple_union_lh (den := den) fr ha
      obtain ⟨res, run⟩ := iu okLit' pos a ta
      exact ⟨res, by simp [Elixir.Module.Types.Descr.«tuple_insert_leaves/4», rr, ra, run]⟩
    · exfalso
      rw [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1».eq_def] at pos
      split at pos
      all_goals first
        | (rename_i heq; simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at heq; simp_all [boolAtom]; done)
        | (simp_all [boolAtom]; done)
        | skip

/-- The fold of `tuple_insert_static/3` over literals without negations gives a type. -/
theorem insert_pieces_ok (ef : EF nd E V den tl K) {x : Term} (hx : E x) (i : Nat) (P : List Term)
    (tP : ∀ p ∈ P, Piece E p) {m : Nat} :
    ∃ res, Erlang.lists.«foldl/3» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-tuple_insert_static/3-fun-0-" 2
      #[.integer i, x]) (.atom "bdd_bot") (Term.list P) = .ok res := by
  obtain ⟨r, -, run⟩ := foldl_rel_at (m := m + 1) "Elixir.Module.Types.Descr" "-tuple_insert_static/3-fun-0-"
    #[.integer i, x] (fun _ a => TField E a) P (fun pre p a mp ta => by
      obtain ⟨tag, l, rfl, g, hl⟩ := tP p mp
      obtain ⟨r, rr, fr, -⟩ := insert_leaf_ok (den := den) ef g hl hx i
      obtain ⟨u, ru, tu, -⟩ := tuple_union_lh (den := den) fr ta
      refine ⟨u, tu, ?_⟩
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_insert_static/3-fun-0-/2».pure]
      simp [Elixir.Module.Types.Descr.«-tuple_insert_static/3-fun-0-/4», rr, ru])
    (.atom "bdd_bot") (Or.inr Bdd.bot)
  exact ⟨r, run⟩

/-- `tuple_insert_static/3` gives a type on any tuple field. -/
theorem insert_static_ok (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "tuple") = some b) (fb : TField E b) {x : Term} (hx : E x) (i : Nat) :
    ∃ res, Elixir.Module.Types.Descr.«tuple_insert_static/3» (D (n + 3)) (.map X) (.integer i) x = .ok res := by
  have upd : ∀ b', Erlang.maps.«update/3» (.atom "tuple") b' (.map X) = .ok (.map ((.atom "tuple", b') :: X)) := by
    intro b'
    have : (X.find? fun entry => decide (compareExact (fuel (.atom "tuple") entry.1) (.atom "tuple") entry.1 = .eq)).isSome := by
      have := congrArg Option.isSome hb
      simpa [mapLookup] using this
    simp [Erlang.maps.«update/3», this]
  have hb' : Lynx.Term.getMapKeys [.atom "tuple"] (.map X) = [b] := by simp [getMapKeys_single, hb]
  rcases fb with ⟨k, rfl⟩ | wb
  · have lit : TupleLit E (.tuple #[.integer k, .atom "open", .nil]) := ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩
    obtain ⟨r, run⟩ := insert_leaves_ok (den := den) ef hx i (TupleLit E) _ (Bdd.leaf_iff.mpr lit) (fun t h => h)
      (by simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», boolAtom]) (.atom "bdd_bot") (Or.inr Bdd.bot)
    exact ⟨.map ((.atom "tuple", r) :: X), by simp [Elixir.Module.Types.Descr.«tuple_insert_static/3», getMapKeys_single, hb,
      Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», Lynx.Term.isMember, run,
      Erlang.erlang.«is_map/1», upd]⟩
  · obtain ⟨q, rq⟩ := positive_run _ b wb
    cases q
    · obtain ⟨P, rP, tP, -⟩ := no_negs (den := den) ef hn wb
      obtain ⟨r, run⟩ := insert_pieces_ok (den := den) ef hx i P tP (m := n + 2)
      exact ⟨.map ((.atom "tuple", r) :: X), by
        unfold Elixir.Module.Types.Descr.«tuple_insert_static/3»
        simp [hb', rq, rP, Lynx.Term.isMember, boolAtom, run, Erlang.erlang.«is_map/1», upd]⟩
    · obtain ⟨r, run⟩ := insert_leaves_ok (den := den) ef hx i _ b wb (fun t h => h.1.1) rq (.atom "bdd_bot")
        (Or.inr Bdd.bot)
      exact ⟨.map ((.atom "tuple", r) :: X), by
        unfold Elixir.Module.Types.Descr.«tuple_insert_static/3»
        simp [hb', rq, Lynx.Term.isMember, boolAtom, run, Erlang.erlang.«is_map/1», upd]⟩

end

section
variable {t : Term} {n : Nat}

/-- Values at an index of the tuples of a tuple type. -/
def El (t : Term) (n : Nat) (X : List (Term × Term)) (i : Nat) (y : (level t n).V) : Prop :=
  ∃ v₁ v₂, List.length v₁ = i ∧ TT t n X (v₁ ++ y :: v₂)

/-- Some tuple of a tuple type is no longer than an index. -/
def Short (t : Term) (n : Nat) (X : List (Term × Term)) (i : Nat) : Prop :=
  ∃ w, TT t n X w ∧ List.length w ≤ i

/-- `tuple_delete_at/2` on static types of the next level: types holding only tuples, all of them longer than the index,
give the tuples without the element at the index; types holding a shorter tuple give `:badindex`, and others
`:badtuple`. -/
theorem delete_cases {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) : ∃ res, Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok res ∧
      ((res = .atom "badtuple" ∧ ¬TOnly t n X) ∨ (res = .atom "badindex" ∧ TOnly t n X ∧ Short t n X i) ∨
        (TOnly t n X ∧ ¬Short t n X i ∧ ∃ r, res = .map [(.atom "tuple", r)] ∧ TField (level t n).E r ∧
          ∀ w, denTF (level t n).E (level t n).den r w = Bool.true ↔
            ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ List.length v₁ = i ∧ TT t n X (v₁ ++ y :: v₂))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  by_cases ok : TOnly t n X
  · by_cases short : Short t n X i
    · obtain ⟨w₀, b, hb, -⟩ := ok.2
      have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
      obtain ⟨c, rc, sc⟩ := only_run hX hb (m := k + 3) (by omega)
      have c_true : c = Bool.true := sc.mpr ok
      subst c_true
      obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := k + 3) (by omega) fb (i + 1) (by omega)
      have sz_false : sz = Bool.false := by
        cases sz
        · rfl
        · obtain ⟨w, hw, len⟩ := short
          obtain ⟨b', hb', hw⟩ := hw
          rw [hb] at hb'; cases hb'
          have := ss.mp rfl w hw; omega
      subst sz_false
      have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
      have rs' : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map [(.atom "tuple", b)])
          (.integer ((i : Int) + 1)) = .ok (boolAtom Bool.false) := by simpa using rs
      refine ⟨.atom "badindex", ?_, Or.inr (Or.inl ⟨rfl, ok, short⟩)⟩
      rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def]
      simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
        Erlang.maps.«take/2», sX.static, key, rc, size_map _ hb, rs', boolAtom, Erlang.erlang.«/=/2»]
    · have long : ∀ w, TT t n X w → i < List.length w := fun w hw =>
        Classical.byContradiction fun h => short ⟨w, hw, by omega⟩
      obtain ⟨r, run, tr, sr⟩ := delete_tuple hX ok i long (by omega)
      exact ⟨_, run, Or.inr (Or.inr ⟨ok, short, r, rfl, tr, sr⟩)⟩
  · refine ⟨.atom "badtuple", ?_, Or.inl ⟨rfl, ok⟩⟩
    rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def]
    cases hb : mapLookup X (.atom "tuple") with
    | none =>
      simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
        Erlang.maps.«take/2», sX.static, Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key,
        hb, Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2», Erlang.erlang.«/=/2», getMapKeys_single]
    | some b =>
      have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
      obtain ⟨c, rc, sc⟩ := only_run hX hb (m := k + 3) (by omega)
      have c_false : c = Bool.false := by
        cases c
        · rfl
        · exact absurd (sc.mp rfl) ok
      subst c_false
      obtain ⟨sz, rs, -⟩ := size_at_least (level t n).ef (m := k + 3) (by omega) fb (i + 1) (by omega)
      have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
      have rs' : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map [(.atom "tuple", b)])
          (.integer ((i : Int) + 1)) = .ok (boolAtom sz) := by simpa using rs
      cases sz <;>
      simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
        Erlang.maps.«take/2», sX.static, key, rc, size_map _ hb, rs', boolAtom, Erlang.erlang.«/=/2»]

/-- `same_fetch?/2` holds on fetching from two static types of the next level that agree on holding only tuples, on
holding short tuples, and on their values at the indices. -/
theorem same_fetch {X Y : List (Term × Term)} (hX : DE (level t n).E (.map X)) (hY : DE (level t n).E (.map Y))
    (i j : Nat) {m : Nat} (hm : (level t n).K + 25 ≤ m) (only : TOnly t n X ↔ TOnly t n Y)
    (short : TOnly t n X → (Short t n X i ↔ Short t n Y j))
    (el : TOnly t n X → ¬Short t n X i → ∀ y, El t n X i y ↔ El t n Y j y) :
    ∃ a b, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer i) = .ok a ∧
      Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map Y) (.integer j) = .ok b ∧
      «same_fetch?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨a, ra, ⟨rfl, na⟩ | ⟨rfl, oa, wa, ha, la⟩ | ⟨e, rfl, he, oa, longa, s₁, s₂⟩⟩ := fetch_tuple hX i hm <;>
  obtain ⟨b, rb, ⟨rfl, nb⟩ | ⟨rfl, ob, wb, hb, lb⟩ | ⟨f, rfl, hf, ob, longb, t₁, t₂⟩⟩ := fetch_tuple hY j hm
  · exact ⟨_, _, ra, rb, by simp [«same_fetch?/2», Erlang.erlang.«==/2»]⟩
  · exact absurd (only.mpr ob) na
  · exact absurd (only.mpr ob) na
  · exact absurd (only.mp oa) nb
  · exact ⟨_, _, ra, rb, by simp [«same_fetch?/2», Erlang.erlang.«==/2»]⟩
  · obtain ⟨w, hw, lw⟩ := (short oa).mp ⟨wa, ha, la⟩
    have := longb w hw; omega
  · exact absurd (only.mp oa) nb
  · obtain ⟨w, hw, lw⟩ := (short oa).mpr ⟨wb, hb, lb⟩
    have := longa w hw; omega
  · have ns : ¬Short t n X i := fun ⟨w, hw, lw⟩ => by have := longa w hw; omega
    have sem : ∀ y, (level t n).den e y ↔ (level t n).den f y := fun y => by
      constructor
      · intro hy
        obtain ⟨v₁, v₂, l₁, h⟩ := (el oa ns y).mp (s₂ y hy)
        exact t₁ v₁ y v₂ l₁ h
      · intro hy
        obtain ⟨v₁, v₂, l₁, h⟩ := (el oa ns y).mpr (t₂ y hy)
        exact s₁ v₁ y v₂ l₁ h
    refine ⟨_, _, ra, rb, ?_⟩
    simp only [«same_fetch?/2»]
    exact elem_equal (level t n).ef he hf sem (by omega)

theorem tt_single (r : Term) (w : List (level t n).V) :
    TT t n [(.atom "tuple", r)] w ↔ denTF (level t n).E (level t n).den r w = Bool.true := by
  simp [TT, mapLookup]

theorem single_tuples (r : Term) (v : PN t n) (hv : denD (.map [(.atom "tuple", r)]) v) : v.1.1 = "tuple" := by
  by_cases h : v.1.1 = "tuple"
  · exact h
  · rw [denD_map] at hv
    simp [mapLookup, h, dn_none] at hv

/-- Fetching after deleting the element at an index: the values at the next index from the index on. -/
theorem delete_same_fetch {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {i : Nat} (onlyX : TOnly t n X)
    (shortX : ¬Short t n X i) {r : Term} (tr : TField (level t n).E r)
    (sr : ∀ w, denTF (level t n).E (level t n).den r w = Bool.true ↔ ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ List.length v₁ = i ∧
      TT t n X (v₁ ++ y :: v₂)) (o : Nat) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ a b, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map [(.atom "tuple", r)]) (.integer o) = .ok a ∧
      Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer (if o < i then o else o + 1 : Nat)) = .ok b ∧
      «same_fetch?/2» (D m) a b = .ok (.atom "true") := by
  have long : ∀ x, TT t n X x → i < List.length x := fun x hx =>
    Classical.byContradiction fun h => shortX ⟨x, hx, by omega⟩
  have tz : ∀ w, TT t n [(.atom "tuple", r)] w ↔ ∃ x, TT t n X x ∧ i < List.length x ∧ w = x.eraseIdx i := fun w => by
    rw [tt_single, sr, split_erase]
  have dZ : DE (level t n).E (.map [(.atom "tuple", r)]) := Or.inr ⟨_, rfl, descrC_put descrC_nil tr⟩
  refine same_fetch dZ hX o _ hm ?_ ?_ ?_
  · refine ⟨fun _ => onlyX, fun _ => ⟨single_tuples r, ?_⟩⟩
    obtain ⟨x, hx⟩ := onlyX.2
    exact ⟨_, (tz _).mpr ⟨x, hx, long x hx, rfl⟩⟩
  · intro _
    constructor
    · rintro ⟨w, hw, lw⟩
      obtain ⟨x, hx, lx, rfl⟩ := (tz w).mp hw
      refine ⟨x, hx, ?_⟩
      simp only [List.length_eraseIdx, lx, ite_true] at lw
      split <;> omega
    · rintro ⟨x, hx, lx⟩
      have := long x hx
      refine ⟨_, (tz _).mpr ⟨x, hx, this, rfl⟩, ?_⟩
      simp only [List.length_eraseIdx, this, ite_true]
      split at lx <;> omega
  · intro _ _ y
    simp only [El, split_getElem]
    constructor
    · rintro ⟨w, hw, hy⟩
      obtain ⟨x, hx, -, rfl⟩ := (tz w).mp hw
      refine ⟨x, hx, ?_⟩
      rw [List.getElem?_eraseIdx] at hy
      split at hy <;> split <;> first | exact hy | omega
    · rintro ⟨x, hx, hy⟩
      refine ⟨_, (tz _).mpr ⟨x, hx, long x hx, rfl⟩, ?_⟩
      rw [List.getElem?_eraseIdx]
      split at hy <;> split <;> first | exact hy | omega

/-- Fetching at another index after inserting a value at an index: the values before the index, and those after it
shifted by one. -/
theorem insert_same_fetch {X Y : List (Term × Term)} (hX : DE (level t n).E (.map X)) (hY : DE (level t n).E (.map Y))
    {i : Nat} {x : Term} (onlyX : TOnly t n X) (longX : ∀ w, TT t n X w → i ≤ List.length w)
    (onlyY : ∀ v : PN t n, denD (.map Y) v → v.1.1 = "tuple") (ttY : ∀ w, TT t n Y w ↔ Ins (TT t n X) i ((level t n).den x) w)
    {y₀ : (level t n).V} (hy₀ : (level t n).den x y₀) (o : Nat) (ne : o ≠ i) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ a b, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map Y) (.integer o) = .ok a ∧
      Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer (if o < i then o else o - 1 : Nat)) = .ok b ∧
      «same_fetch?/2» (D m) a b = .ok (.atom "true") := by
  have ty : ∀ w, TT t n Y w ↔ ∃ x' y, TT t n X x' ∧ i ≤ List.length x' ∧ (level t n).den x y ∧
      w = x'.take i ++ y :: x'.drop i := fun w => by rw [ttY, ins_insert]
  refine same_fetch hY hX o _ hm ?_ ?_ ?_
  · refine ⟨fun _ => onlyX, fun _ => ⟨onlyY, ?_⟩⟩
    obtain ⟨w, hw⟩ := onlyX.2
    exact ⟨_, (ty _).mpr ⟨w, y₀, hw, longX w hw, hy₀, rfl⟩⟩
  · intro _
    constructor
    · rintro ⟨w, hw, lw⟩
      obtain ⟨x', y, hx, lx, -, rfl⟩ := (ty w).mp hw
      rw [insert_length lx] at lw
      refine ⟨x', hx, ?_⟩
      split <;> omega
    · rintro ⟨x', hx, lx⟩
      have := longX x' hx
      refine ⟨_, (ty _).mpr ⟨x', y₀, hx, this, hy₀, rfl⟩, ?_⟩
      rw [insert_length this]
      split at lx <;> omega
  · intro _ _ y
    simp only [El, split_getElem]
    constructor
    · rintro ⟨w, hw, hy⟩
      obtain ⟨x', y', hx, lx, -, rfl⟩ := (ty w).mp hw
      refine ⟨x', hx, ?_⟩
      rw [insert_getElem lx] at hy
      by_cases hoi : o < i <;> simpa [hoi, ne] using hy
    · rintro ⟨x', hx, hy⟩
      have lx := longX x' hx
      refine ⟨_, (ty _).mpr ⟨x', y₀, hx, lx, hy₀, rfl⟩, ?_⟩
      rw [insert_getElem lx]
      by_cases hoi : o < i <;> simpa [hoi, ne] using hy

/-- `tuple_replace_at/3` on static types of the next level: it deletes the element at the index, and inserts the value
into the remaining tuples. -/
theorem replace_cases {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat) {x : Term}
    (sx : x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    (Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) (.map X) (.integer i) x = .ok (.atom "badtuple") ∧
        ¬TOnly t n X) ∨
      (Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) (.map X) (.integer i) x = .ok (.atom "badindex") ∧
        TOnly t n X ∧ Short t n X i) ∨
      (TOnly t n X ∧ ¬Short t n X i ∧ ∃ r, TField (level t n).E r ∧
        (∀ w, denTF (level t n).E (level t n).den r w = Bool.true ↔ ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ List.length v₁ = i ∧
          TT t n X (v₁ ++ y :: v₂)) ∧
        Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) (.map X) (.integer i) x =
          Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map [(.atom "tuple", r)]) (.integer i) x) := by
  obtain ⟨res, run, ⟨rfl, nonly⟩ | ⟨rfl, onlyX, short⟩ | ⟨onlyX, short, r, rfl, tr, sr⟩⟩ := delete_cases hX i hm
  · refine Or.inl ⟨?_, nonly⟩
    simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
      Erlang.erlang.«>=/2», Int.isGE_compare, run, Lynx.Except.orElse, Erlang.erlang.«is_map/1»,
      Erlang.erlang.«==/2», pure, Except.pure]
  · refine Or.inr (Or.inl ⟨?_, onlyX, short⟩)
    simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
      Erlang.erlang.«>=/2», Int.isGE_compare, run, Lynx.Except.orElse, Erlang.erlang.«is_map/1»,
      Erlang.erlang.«==/2», pure, Except.pure]
  · refine Or.inr (Or.inr ⟨onlyX, short, r, tr, sr, ?_⟩)
    simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
      Erlang.erlang.«>=/2», Int.isGE_compare, run, Lynx.Except.orElse, Erlang.erlang.«is_map/1»,
      insert_at_static _ _ _ sx]

/-- `tuple_replace_at/3` on static types of the next level, when it gives a type: the input holds only tuples, all
longer than the index, and the result holds those tuples with the element at the index set to a value. -/
theorem replace_tuple {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat) {x : Term} (hx : (level t n).E x)
    (sx : x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) {Y : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) (.map X) (.integer i) x = .ok (.map Y)) :
    TOnly t n X ∧ ¬Short t n X i ∧ DE (level t n).E (.map Y) ∧ (∀ v : PN t n, denD (.map Y) v → v.1.1 = "tuple") ∧
      ∀ w, TT t n Y w ↔ ∃ x' y, TT t n X x' ∧ i < List.length x' ∧ (level t n).den x y ∧ w = x'.set i y := by
  rcases replace_cases hX i sx hm with ⟨e, -⟩ | ⟨e, -⟩ | ⟨onlyX, short, r, tr, sr, e⟩
  · rw [e] at run; cases run
  · rw [e] at run; cases run
  rw [e] at run
  have dZ : DE (level t n).E (.map [(.atom "tuple", r)]) := Or.inr ⟨_, rfl, descrC_put descrC_nil tr⟩
  obtain ⟨-, -, dY, onlyY, ttY⟩ := insert_tuple dZ hx i hm run
  refine ⟨onlyX, short, dY, onlyY, fun w => ?_⟩
  rw [ttY, ins_insert]
  constructor
  · rintro ⟨u, y, hu, lu, hy, rfl⟩
    rw [tt_single, sr, split_erase] at hu
    obtain ⟨x', hx', lx', rfl⟩ := hu
    exact ⟨x', y, hx', lx', hy, erase_insert lx' y⟩
  · rintro ⟨x', y, hx', lx', hy, rfl⟩
    refine ⟨x'.eraseIdx i, y, ?_, ?_, hy, (erase_insert lx' y).symm⟩
    · rw [tt_single, sr, split_erase]; exact ⟨x', hx', lx', rfl⟩
    · rw [List.length_eraseIdx]; split <;> omega

theorem replace_neg (d : Dispatcher) (a x : Term) {z : Int} (h : z < 0) :
    Elixir.Module.Types.Descr.«tuple_replace_at/3» d a (.integer z) x = .ok (.atom "badindex") := by
  have : ¬0 ≤ z := by omega
  simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
    Erlang.erlang.«>=/2», Int.isGE_compare, this, pure, Except.pure]

theorem replace_term (d : Dispatcher) (i : Nat) (x : Term) :
    Elixir.Module.Types.Descr.«tuple_replace_at/3» d (.atom "term") (.integer i) x = .ok (.atom "badtuple") := by
  simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
    Erlang.erlang.«>=/2», Int.isGE_compare, Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def,
    Lynx.Except.orElse, Erlang.erlang.«is_map/1», Erlang.erlang.«==/2», pure, Except.pure]

/-- `tuple_insert_at_checked/3` gives a type on static types of the next level holding only tuples, all long enough. -/
theorem insert_checked_ok {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (onlyX : TOnly t n X) {x : Term}
    (hx : (level t n).E x) (i : Nat) (long : ∀ w, TT t n X w → i ≤ List.length w) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok (.map Y) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  obtain ⟨w₀, b, hb, -⟩ := onlyX.2
  have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
  obtain ⟨c, rc, sc⟩ := only_run hX hb (m := k + 3) (by omega)
  have c_true : c = Bool.true := sc.mpr onlyX
  subst c_true
  have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
  have size : Lynx.Except.orElse (Erlang.erlang.«==/2» (.integer i) (.integer 0))
      (Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map X) (.integer i)) =
        .ok (boolAtom Bool.true) := by
    by_cases z : i = 0
    · subst z; simp [Lynx.Except.orElse, Erlang.erlang.«==/2», boolAtom]
    · obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := k + 3) (by omega) fb i (by omega)
      have sz_true : sz = Bool.true := ss.mpr fun w hw => long w (by simp [TT, hb, hw])
      subst sz_true
      have eq0 : Erlang.erlang.«==/2» (.integer (i : Int)) (.integer 0) = .ok (.atom "false") := by
        simp [Erlang.erlang.«==/2»]; omega
      rw [size_map _ hb, eq0]
      simpa [Lynx.Except.orElse] using rs
  obtain ⟨res, rres⟩ := insert_static_ok (den := (level t n).den) (level t n).ef (n := k) (by omega) hb fb hx i
  obtain ⟨b', rfl, -⟩ := insert_static (den := (level t n).den) (level t n).ef (n := k) (by omega) hb fb hx i rres
  refine ⟨(.atom "tuple", b') :: X, ?_⟩
  unfold Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
  simp only [Erlang.maps.«take/2», sX.static, Lynx.Except.ok_bind]
  simp only [key, rc, size]
  simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure, rres]

/-- `tuple_replace_at/3` gives a type on static types of the next level holding only tuples, all longer than the
index. -/
theorem replace_ok {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat) {x : Term} (hx : (level t n).E x)
    (sx : x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) (onlyX : TOnly t n X) (shortX : ¬Short t n X i) :
    ∃ Y, Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) (.map X) (.integer i) x = .ok (.map Y) := by
  rcases replace_cases hX i sx hm with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, r, tr, sr, e⟩
  · exact absurd onlyX h
  · exact absurd h shortX
  rw [e]
  have long : ∀ w, TT t n X w → i < List.length w := fun w hw =>
    Classical.byContradiction fun h => shortX ⟨w, hw, by omega⟩
  have tz : ∀ w, TT t n [(.atom "tuple", r)] w ↔ ∃ x, TT t n X x ∧ i < List.length x ∧ w = x.eraseIdx i := fun w => by
    rw [tt_single, sr, split_erase]
  have dZ : DE (level t n).E (.map [(.atom "tuple", r)]) := Or.inr ⟨_, rfl, descrC_put descrC_nil tr⟩
  obtain ⟨x₀, hx₀⟩ := onlyX.2
  refine insert_checked_ok dZ ⟨single_tuples r, _, (tz _).mpr ⟨x₀, hx₀, long x₀ hx₀, rfl⟩⟩ hx i (fun w hw => ?_) hm
  obtain ⟨y, hy, ly, rfl⟩ := (tz w).mp hw
  rw [List.length_eraseIdx]; split <;> omega

end

end Elixir.STTDescrProofsTest.Nest
