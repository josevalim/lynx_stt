namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Deleting and replacing elements of tuple types, and fetching from the results. -/

section
variable {V : Type}

/-- Lists split around an index are lists with the element at the index erased. -/
theorem split_erase {P : List V → Prop} {i : Nat} {w : List V} :
    (∃ v₁ y v₂, w = v₁ ++ v₂ ∧ v₁.length = i ∧ P (v₁ ++ y :: v₂)) ↔ ∃ x, P x ∧ i < x.length ∧ w = x.eraseIdx i := by
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
    Ins P i Q w ↔ ∃ x y, P x ∧ i ≤ x.length ∧ Q y ∧ w = x.take i ++ y :: x.drop i := by
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
    (∃ v₁ v₂, v₁.length = i ∧ P (v₁ ++ y :: v₂)) ↔ ∃ w, P w ∧ w[i]? = some y := by
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
  ∃ v₁ v₂, v₁.length = i ∧ TT t n X (v₁ ++ y :: v₂)

/-- Some tuple of a tuple type is no longer than an index. -/
def Short (t : Term) (n : Nat) (X : List (Term × Term)) (i : Nat) : Prop :=
  ∃ w, TT t n X w ∧ w.length ≤ i

/-- `tuple_delete_at/2` on static types of the next level: types holding only tuples, all of them longer than the index,
give the tuples without the element at the index; types holding a shorter tuple give `:badindex`, and others
`:badtuple`. -/
theorem delete_cases {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) : ∃ res, Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok res ∧
      ((res = .atom "badtuple" ∧ ¬TOnly t n X) ∨ (res = .atom "badindex" ∧ TOnly t n X ∧ Short t n X i) ∨
        (TOnly t n X ∧ ¬Short t n X i ∧ ∃ r, res = .map [(.atom "tuple", r)] ∧ TField (level t n).E r ∧
          ∀ w, denTF (level t n).E (level t n).den r w = Bool.true ↔
            ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ v₁.length = i ∧ TT t n X (v₁ ++ y :: v₂))) := by
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
    · have long : ∀ w, TT t n X w → i < w.length := fun w hw =>
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
    (sr : ∀ w, denTF (level t n).E (level t n).den r w = Bool.true ↔ ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ v₁.length = i ∧
      TT t n X (v₁ ++ y :: v₂)) (o : Nat) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ a b, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map [(.atom "tuple", r)]) (.integer o) = .ok a ∧
      Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer (if o < i then o else o + 1 : Nat)) = .ok b ∧
      «same_fetch?/2» (D m) a b = .ok (.atom "true") := by
  have long : ∀ x, TT t n X x → i < x.length := fun x hx =>
    Classical.byContradiction fun h => shortX ⟨x, hx, by omega⟩
  have tz : ∀ w, TT t n [(.atom "tuple", r)] w ↔ ∃ x, TT t n X x ∧ i < x.length ∧ w = x.eraseIdx i := fun w => by
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
    {i : Nat} {x : Term} (onlyX : TOnly t n X) (longX : ∀ w, TT t n X w → i ≤ w.length)
    (onlyY : ∀ v : PN t n, denD (.map Y) v → v.1.1 = "tuple") (ttY : ∀ w, TT t n Y w ↔ Ins (TT t n X) i ((level t n).den x) w)
    {y₀ : (level t n).V} (hy₀ : (level t n).den x y₀) (o : Nat) (ne : o ≠ i) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ a b, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map Y) (.integer o) = .ok a ∧
      Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer (if o < i then o else o - 1 : Nat)) = .ok b ∧
      «same_fetch?/2» (D m) a b = .ok (.atom "true") := by
  have ty : ∀ w, TT t n Y w ↔ ∃ x' y, TT t n X x' ∧ i ≤ x'.length ∧ (level t n).den x y ∧
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
        (∀ w, denTF (level t n).E (level t n).den r w = Bool.true ↔ ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ v₁.length = i ∧
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
      ∀ w, TT t n Y w ↔ ∃ x' y, TT t n X x' ∧ i < x'.length ∧ (level t n).den x y ∧ w = x'.set i y := by
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
    (hx : (level t n).E x) (i : Nat) (long : ∀ w, TT t n X w → i ≤ w.length) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
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
  have long : ∀ w, TT t n X w → i < w.length := fun w hw =>
    Classical.byContradiction fun h => shortX ⟨w, hw, by omega⟩
  have tz : ∀ w, TT t n [(.atom "tuple", r)] w ↔ ∃ x, TT t n X x ∧ i < x.length ∧ w = x.eraseIdx i := fun w => by
    rw [tt_single, sr, split_erase]
  have dZ : DE (level t n).E (.map [(.atom "tuple", r)]) := Or.inr ⟨_, rfl, descrC_put descrC_nil tr⟩
  obtain ⟨x₀, hx₀⟩ := onlyX.2
  refine insert_checked_ok dZ ⟨single_tuples r, _, (tz _).mpr ⟨x₀, hx₀, long x₀ hx₀, rfl⟩⟩ hx i (fun w hw => ?_) hm
  obtain ⟨y, hy, ly, rfl⟩ := (tz w).mp hw
  rw [List.length_eraseIdx]; split <;> omega

end

end Elixir.STTDescrProofsTest.Nest
