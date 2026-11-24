namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The values of the elements of tuple types, as `tuple_values/1` computes them. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The values a literal without negations holds at its positions: none when an element is empty, any for open
literals, and those of its elements for closed ones. -/
def PieceVal (den : Term → V → Prop) (p : Term) (y : V) : Prop :=
  ∃ (tag : String) (l : List Term), p = .tuple #[.atom tag, Term.list l] ∧ (∀ e ∈ l, ∃ y', den e y') ∧
    (tag = "open" ∨ ∃ e ∈ l, den e y)

theorem inT_nonempty {c : Bool} : ∀ {l : List Term} {v : List V}, InT den c l v → ∀ e ∈ l, ∃ y, den e y
  | [], _, _, e, me => by simp at me
  | _ :: _, [], h, _, _ => by simp [InT] at h
  | x :: l, y :: v, h, e, me => by
    simp only [InT] at h
    rcases List.mem_cons.mp me with rfl | me
    · exact ⟨y, h.1⟩
    · exact inT_nonempty h.2 e me

theorem inT_get_closed : ∀ {l : List Term} {v : List V}, InT den Bool.true l v → ∀ (j : Nat) (y : V), v[j]? = some y → ∃ e ∈ l, den e y
  | [], [], _, j, y, hy => by simp at hy
  | [], _ :: _, h, _, _, _ => by simp [InT] at h
  | _ :: _, [], h, _, _, _ => by simp [InT] at h
  | x :: l, z :: v, h, j, y, hy => by
    simp only [InT] at h
    cases j with
    | zero => simp at hy; subst hy; exact ⟨x, List.mem_cons_self, h.1⟩
    | succ j =>
      obtain ⟨e, me, he⟩ := inT_get_closed h.2 j y (by simpa using hy)
      exact ⟨e, List.mem_cons_of_mem _ me, he⟩

/-- The elements of the tuples of a literal without negations are values of its positions. -/
theorem pieceIn_val {p : Term} (tp : Piece E p) {w : List V} (h : PieceIn den p w) {j : Nat} {y : V}
    (hy : w[j]? = some y) : PieceVal den p y := by
  obtain ⟨tag, l, rfl, g, -⟩ := tp
  have h := pieceIn_iff.mp h
  refine ⟨tag, l, rfl, inT_nonempty h, ?_⟩
  rcases g with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (inT_get_closed h j y hy)

theorem inT_exists_closed : ∀ {l : List Term}, (∀ e ∈ l, ∃ y', den e y') → ∃ w : List V, InT den Bool.true l w
  | [], _ => ⟨[], by simp [InT]⟩
  | x :: l, ne => by
    obtain ⟨yx, hx⟩ := ne x List.mem_cons_self
    obtain ⟨w, hw⟩ := inT_exists_closed (fun e me => ne e (List.mem_cons_of_mem _ me))
    exact ⟨yx :: w, by simp [InT, hx, hw]⟩

/-- Closed literals with values in every element hold a tuple with a value of any element. -/
theorem inT_witness_closed : ∀ {l : List Term}, (∀ e ∈ l, ∃ y', den e y') → ∀ {e : Term} {y : V}, e ∈ l → den e y →
    ∃ w, InT den Bool.true l w ∧ ∃ j : Nat, w[j]? = some y
  | [], _, _, _, me, _ => by simp at me
  | x :: l, ne, e, y, me, hy => by
    obtain ⟨y₀, hy₀⟩ := ne x List.mem_cons_self
    have ne' : ∀ e ∈ l, ∃ y', den e y' := fun e me => ne e (List.mem_cons_of_mem _ me)
    rcases List.mem_cons.mp me with rfl | me
    · obtain ⟨w, hw⟩ := inT_exists_closed ne'
      exact ⟨y :: w, by simp [InT, hy, hw], 0, by simp⟩
    · obtain ⟨w, hw, j, hj⟩ := inT_witness_closed ne' me hy
      exact ⟨y₀ :: w, by simp [InT, hy₀, hw], j + 1, by simpa using hj⟩

/-- Open literals with values in every element hold tuples of any length from theirs. -/
theorem inT_witness_open (y₀ : V) : ∀ {l : List Term}, (∀ e ∈ l, ∃ y', den e y') → ∀ N,
    ∃ w, InT den Bool.false l w ∧ N ≤ w.length
  | [], _, N => ⟨List.replicate N y₀, InT.open_nil _, by simp⟩
  | x :: l, ne, N => by
    obtain ⟨yx, hx⟩ := ne x List.mem_cons_self
    obtain ⟨w, hw, lw⟩ := inT_witness_open y₀ (fun e me => ne e (List.mem_cons_of_mem _ me)) N
    exact ⟨yx :: w, by simp [InT, hx, hw], by simp; omega⟩

theorem inT_replicate {e : Term} : ∀ (s : Nat) (w : List V),
    InT den Bool.true (List.replicate s e) w ↔ w.length = s ∧ ∀ y ∈ w, den e y
  | 0, [] => by simp [InT]
  | 0, _ :: _ => by simp [InT]
  | _ + 1, [] => by simp [List.replicate_succ, InT]
  | s + 1, y :: w => by
    simp only [List.replicate_succ, InT, inT_replicate s w, List.length_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨h, rfl, h'⟩; exact ⟨rfl, h, h'⟩
    · rintro ⟨e, h, h'⟩; exact ⟨h, by omega, h'⟩

/-- The fold of `opt_union/2` over element types unites their values. -/
theorem union_elements (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (l : List Term) (hl : ∀ e ∈ l, E e) :
    ∃ r, E r ∧ Erlang.lists.«foldl/3» (D (n + 1)) (.function "Elixir.Module.Types.Descr" "opt_union" 2 #[])
      (.map []) (Term.list l) = .ok r ∧ ∀ y, den r y ↔ ∃ e ∈ l, den e y := by
  obtain ⟨r, ⟨hr, sr⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr" "opt_union" #[]
    (fun pre a => E a ∧ ∀ y, den a y ↔ ∃ e ∈ pre, den e y) l
    (fun pre x a mx ⟨ha, sa⟩ => by
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] (hl x mx) ha hn
      refine ⟨c, ⟨hc, fun y => ?_⟩, ?_⟩
      · rw [sc, sa]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | ⟨e, me, h⟩)
          · exact ⟨x, Or.inr rfl, h⟩
          · exact ⟨e, Or.inl me, h⟩
        · rintro ⟨e, me | rfl, h⟩
          · exact Or.inr ⟨e, me, h⟩
          · exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:opt_union/2».pure]
        simpa [Elixir.Module.Types.Descr.«opt_union/2»] using rc)
    (.map []) ⟨ef.none, fun y => by simp [ef.den_none y]⟩
  exact ⟨r, hr, run, sr⟩

/-- The fold of `process_tuples_values/1` over literals without negations unites the values of their positions. -/
theorem values_pieces (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (P : List Term) (tP : ∀ p ∈ P, Piece E p) :
    ∃ r, E r ∧ Erlang.lists.«foldl/3» (D (n + 2))
      (.function "Elixir.Module.Types.Descr" "-process_tuples_values/1-fun-0-" 2 #[]) (.map []) (Term.list P) = .ok r ∧
      ∀ y, den r y ↔ ∃ p ∈ P, PieceVal den p y := by
  obtain ⟨r, ⟨hr, sr⟩, run⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr" "-process_tuples_values/1-fun-0-" #[]
    (fun pre a => E a ∧ ∀ y, den a y ↔ ∃ p ∈ pre, PieceVal den p y) P
    (fun pre x a mx ⟨ha, sa⟩ => by
      obtain ⟨tag, l, rfl, g, hl⟩ := tP x mx
      -- The value of the literal.
      have empties : ∀ e ∈ l, (D (n + 1)).pure (.function "Elixir.Module.Types.Descr" "empty?" 1 #[]) #[e] =
          .ok (boolAtom (bp (∀ v, ¬den e v))) := by
        intro e me
        obtain ⟨b, rb, sb⟩ := ef.empty_pub (hl e me)
        rw [Erlang.program.«Elixir.Module.Types.Descr:empty?/1».pure, rb n hn]
        congr 2
        cases b <;> cases h : bp (∀ v, ¬den e v) <;> simp_all
      have hany := any_list (D (n + 1)) _ _ _ (fun e => bp (∀ v, ¬den e v)) l empties
      obtain ⟨val, hval, rval, sval⟩ : ∃ val, E val ∧
          Elixir.Module.Types.Descr.«-process_tuples_values/1-fun-0-/2» (D (n + 1)) (.tuple #[.atom tag, Term.list l]) a =
            Elixir.Module.Types.Descr.«opt_union/2» (D (n + 1)) val a ∧
          ∀ y, den val y ↔ PieceVal den (.tuple #[.atom tag, Term.list l]) y := by
        by_cases emp : ∃ e ∈ l, ∀ v, ¬den e v
        · have t : (l.any fun e => bp (∀ v, ¬den e v)) = Bool.true := by
            obtain ⟨e, me, he⟩ := emp
            exact List.any_eq_true.mpr ⟨e, me, bp_true.mpr he⟩
          refine ⟨.map [], ef.none, ?_, fun y => ?_⟩
          · simp [Elixir.Module.Types.Descr.«-process_tuples_values/1-fun-0-/2», hany, t, boolAtom, Lynx.Except.guard,
              Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure]
          · simp only [ef.den_none y, false_iff]
            rintro ⟨tag', l', e, ne, -⟩
            simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, Term.atom.injEq, and_true] at e
            obtain ⟨rfl, e⟩ := e
            obtain rfl := list_inj e
            obtain ⟨e', me', he'⟩ := emp
            obtain ⟨y', hy'⟩ := ne e' me'
            exact he' y' hy'
        · have f : (l.any fun e => bp (∀ v, ¬den e v)) = Bool.false := by
            cases h : l.any fun e => bp (∀ v, ¬den e v)
            · rfl
            · obtain ⟨e, me, he⟩ := List.any_eq_true.mp h
              exact absurd ⟨e, me, bp_true.mp he⟩ emp
          have ne : ∀ e ∈ l, ∃ y', den e y' := fun e me =>
            Classical.byContradiction fun h => emp ⟨e, me, fun v hv => h ⟨v, hv⟩⟩
          have pv : ∀ y, PieceVal den (.tuple #[.atom tag, Term.list l]) y ↔ tag = "open" ∨ ∃ e ∈ l, den e y := by
            intro y
            constructor
            · rintro ⟨tag', l', e, -, h⟩
              simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, Term.atom.injEq, and_true] at e
              obtain ⟨rfl, e⟩ := e
              obtain rfl := list_inj e
              exact h
            · intro h; exact ⟨tag, l, rfl, ne, h⟩
          rcases g with rfl | rfl
          · refine ⟨.atom "term", ef.term, ?_, fun y => by rw [pv]; simp [ef.den_term y]⟩
            simp [Elixir.Module.Types.Descr.«-process_tuples_values/1-fun-0-/2», hany, f, boolAtom, Lynx.Except.guard,
              Lynx.Except.andAlso, Erlang.erlang.«/=/2», Erlang.erlang.«==/2», pure, Except.pure]
          · obtain ⟨u, hu, ru, su⟩ := union_elements ef hn l hl
            refine ⟨u, hu, ?_, fun y => by rw [pv, su]; simp⟩
            simp [Elixir.Module.Types.Descr.«-process_tuples_values/1-fun-0-/2», hany, f, boolAtom, Lynx.Except.guard,
              Lynx.Except.andAlso, Erlang.erlang.«/=/2», Erlang.erlang.«==/2», pure, Except.pure, ru]
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hval ha (show K ≤ n + 1 by omega)
      refine ⟨c, ⟨hc, fun y => ?_⟩, ?_⟩
      · rw [sc, sa, sval]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, Or.inr rfl, h⟩
          · exact ⟨p, Or.inl mp, h⟩
        · rintro ⟨p, mp | rfl, h⟩
          · exact Or.inr ⟨p, mp, h⟩
          · exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-process_tuples_values/1-fun-0-/2».pure, rval]
        simpa [Elixir.Module.Types.Descr.«opt_union/2»] using rc)
    (.map []) ⟨ef.none, fun y => by simp [ef.den_none y]⟩
  exact ⟨r, hr, run, sr⟩

end

section
variable {t : Term} {n : Nat}

theorem dnf_top (k : Int) (m : Nat) : Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1» (D (m + 10))
    (.tuple #[.integer k, .atom "open", .nil]) = .ok (Term.list [.tuple #[.atom "open", .nil]]) := by
  rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1»]
  rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]
  simp [Elixir.Module.Types.Descr.«tuple_line_intersection/2», Erlang.erlang.«length/1»,
    Elixir.Module.Types.Descr.«tuple_sizes_strategy/4», Elixir.Module.Types.Descr.«zip_intersection/4»,
    Erlang.lists.«flatmap/2», Erlang.lists.«flatmap_1/2»,
    Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», Elixir.Module.Types.Descr.«tuple_eliminate_negations/3»,
    Elixir.Module.Types.Descr.«dedup_contiguous/1», Erlang.lists.«reverse/2», Erlang.erlang.«is_function/2»,
    Erlang.lists.«any/2», Erlang.lists.«foldl/3»]

/-- `tuple_values/1` on static types of the next level: `:badtuple` on types not only of tuples, and otherwise the values
of the positions of literals without negations holding the tuples of the type. -/
theorem values_cases {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) : ∃ res, Elixir.Module.Types.Descr.«tuple_values/1» (D m) (.map X) = .ok res ∧
      ((res = .atom "badtuple" ∧ ¬TOnly t n X) ∨
        (TOnly t n X ∧ (level t n).E res ∧ ∃ P : List Term, (∀ p ∈ P, Piece (level t n).E p) ∧
          (∀ w, (∃ p ∈ P, PieceIn (level t n).den p w) ↔ TT t n X w) ∧
          ∀ y, (level t n).den res y ↔ ∃ p ∈ P, PieceVal (level t n).den p y)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  have ef := (level t n).ef
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    have nonly : ¬TOnly t n X := fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h
    refine ⟨.atom "badtuple", ?_, Or.inl ⟨rfl, nonly⟩⟩
    rw [Elixir.Module.Types.Descr.«tuple_values/1».eq_def]
    by_cases e : X = []
    · subst e; simp [Erlang.erlang.«==/2», pure, Except.pure]
    · have ne : Erlang.erlang.«==/2» (.map X) (.map []) = .ok (.atom "false") := by
        simp [Erlang.erlang.«==/2»]; intro h; exact e (by cases X <;> simp_all [compareExact])
      simp [Lynx.Except.guard, ne, Erlang.maps.«take/2», sX.static, hb,
        Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Lynx.Term.isMember, pure, Except.pure]
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
    have ne : Erlang.erlang.«==/2» (.map X) (.map []) = .ok (.atom "false") := by
      have : X ≠ [] := by intro h; subst h; simp [mapLookup] at hb
      simp [Erlang.erlang.«==/2»]; intro h; exact this (by cases X <;> simp_all [compareExact])
    obtain ⟨c, rc, sc⟩ := only_run hX hb (m := k + 4) (by omega)
    have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
    have get : Elixir.Map.«get/3» (.map X) (.atom "tuple") (.atom "bdd_bot") = .ok b := by
      simp [Elixir.Map.«get/3», getMapKeys_single, hb, pure, Except.pure]
    by_cases ok : TOnly t n X
    · have c_true : c = Bool.true := sc.mpr ok
      subst c_true
      -- The literals of the tuple field.
      obtain ⟨P, rP, tP, sP⟩ : ∃ P : List Term, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1» (D (k + 4)) b =
          .ok (Term.list P) ∧ (∀ p ∈ P, Piece (level t n).E p) ∧
          ∀ w, (∃ p ∈ P, PieceIn (level t n).den p w) ↔ TT t n X w := by
        rcases fb with ⟨k', rfl⟩ | wb
        · have e : k - 6 + 10 = k + 4 := by rw [level_K] at hm; omega
          refine ⟨_, by simpa [e] using dnf_top k' (k - 6), fun p mp => ?_, fun w => ?_⟩
          · simp at mp; subst mp; exact ⟨"open", [], rfl, Or.inl rfl, by simp⟩
          · rw [tt, denTF_top]
            simp only [List.mem_singleton, exists_eq_left, iff_true]
            exact ⟨"open", [], rfl, InT.open_nil w⟩
        · obtain ⟨P, rP, tP, sP⟩ := no_negs (den := (level t n).den) ef (n := k + 1) (by rw [level_K] at hm ⊢; omega) wb
          exact ⟨P, rP, tP, fun w => by rw [sP, tt, denTF_bdd wb]⟩
      obtain ⟨r, hr, rr, sr⟩ := values_pieces ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) P tP
      refine ⟨r, ?_, Or.inr ⟨ok, hr, P, tP, sP, sr⟩⟩
      rw [Elixir.Module.Types.Descr.«tuple_values/1».eq_def]
      simp [Lynx.Except.guard, ne, Erlang.maps.«take/2», sX.static, rc, boolAtom, Lynx.Term.isMember, get,
        Elixir.Module.Types.Descr.«process_tuples_values/1», rP, rr, pure, Except.pure]
    · have c_false : c = Bool.false := by
        cases c
        · rfl
        · exact absurd (sc.mp rfl) ok
      subst c_false
      refine ⟨.atom "badtuple", ?_, Or.inl ⟨rfl, ok⟩⟩
      rw [Elixir.Module.Types.Descr.«tuple_values/1».eq_def]
      simp [Lynx.Except.guard, ne, Erlang.maps.«take/2», sX.static, rc, boolAtom, Lynx.Term.isMember, pure, Except.pure]

/-- `sizes?/1` holds of lists of natural numbers. -/
theorem sizes_nat : ∀ {s : Term}, «sizes?/1» s = .ok (.atom "true") → ∃ ns : List Nat, s = Term.list (ns.map fun k : Nat => Term.integer (k : Int))
  | .cons a rest, h => by
    simp only [«sizes?/1», Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨ha, hn⟩, hr⟩ := h
    obtain ⟨z, rfl⟩ : ∃ z : Int, a = .integer z := by
      cases a <;> simp [Erlang.erlang.«is_integer/1»] at ha
      exact ⟨_, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k : Nat, z = k := by
      refine ⟨z.toNat, ?_⟩
      by_cases neg : z < 0
      · simp [Erlang.erlang.«>=/2», Int.isGE_compare, neg] at hn
      · omega
    obtain ⟨ns, rfl⟩ := sizes_nat hr
    exact ⟨k :: ns, rfl⟩
  | .nil, _ => ⟨[], rfl⟩
  | .atom _, h | .integer _, h | .float _, h | .tuple _, h | .map _, h | .bitstring _ _ _, h
  | .function _ _ _ _, h | .pid _, h | .reference _, h => by
    simp [«sizes?/1», Erlang.erlang.«==/2»] at h

/-- `closed_tuples/2` gives closed tuples of the sizes, of values of the type. -/
theorem closed_tuples_sem {v : Term} (hv : (level t n).E v) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∀ ns : List Nat, ∃ C, «closed_tuples/2» (D m) (Term.list (ns.map fun k : Nat => Term.integer (k : Int))) v = .ok C ∧
      DE (level t n).E C ∧ ∀ w, denD C (tpt (t := t) (n := n) w) → w.length ∈ ns ∧ ∀ y ∈ w, (level t n).den v y
  | [] => ⟨.map [], by simp [«closed_tuples/2», Elixir.Module.Types.Descr.«none/0»],
      Or.inr ⟨[], rfl, descrC_nil⟩, fun w h => by rw [denD_map] at h; simp [mapLookup, tpt, dn_none] at h⟩
  | s :: ns => by
    obtain ⟨C', rC, dC, sC⟩ := closed_tuples_sem hv hm ns
    have hl : ∀ e ∈ List.replicate s v, (level t n).E e := fun e me => by rw [List.eq_of_mem_replicate me]; exact hv
    obtain ⟨k, rt, key⟩ := tuple_run (List.replicate s v) fun e me => (level t n).ef.static (hl e me)
    have dT := fused_de (Or.inr rfl) hl key
    obtain ⟨c, tc, rc, sc⟩ := tc_union (L := level t n) dT dC (m := m) (by omega)
    refine ⟨c, ?_, tc, fun w h => ?_⟩
    · simp [«closed_tuples/2», dup_nat, rt, rC, rc]
    · rcases (sc _).mp h with h | h
      · rw [denD_tpt] at h
        simp only [TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some,
          Option.some.injEq, exists_eq_left', denTF_leaf (level t n).ef (Or.inr rfl) hl,
          vT_lit (level t n).ef (Or.inr rfl) hl] at h
        obtain ⟨len, hy⟩ := (inT_replicate s w).mp (by simpa using h)
        exact ⟨by simp [len], hy⟩
      · obtain ⟨len, hy⟩ := sC w h
        exact ⟨List.mem_cons_of_mem _ len, hy⟩

end

end Elixir.STTDescrProofsTest.Nest
