/-! Putting a value at any static key type: the key type splits into atoms, a negated set of atoms, and domain kinds.
Finite atoms give the union of the puts at each, the atoms outside a negated set give the box of the type, where each
key holds what some map holds at a key of its kind or the value, and domain kinds widen each line. Every result is
determined by the maps of the type, so putting is monotone in the type, the keys and the value. -/

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The operation that forces a constant value. -/
abbrev forceOp (v : Term) : Term := .tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]

/-- Forced updates set a key, so they are never empty. -/
@[simp] theorem nonEmpty_force (d : Dispatcher) (v dnf : Term) :
    Elixir.Module.Types.Descr.«map_update_non_empty?/2» d (forceOp v) dnf = .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«map_update_non_empty?/2»]

/-- `map_update_field/2` forcing a constant: the value, when the old field holds a value or may be absent. -/
theorem update_field_force (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {v : Term} (hv : E v) {old : Term}
    (ho : FieldValue E old) :
    ∃ F, Elixir.Module.Types.Descr.«map_update_field/2» (D m) old (forceOp v) = .ok F ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ (∃ x, o = some x ∧ den v x) ∧ ∃ o', FieldSem den old o' := by
  obtain ⟨t, opt, rfl, ht⟩ := ho
  obtain ⟨e, re, se⟩ := ef.empty1 (m := m) hm ht
  -- The present part and the absent part.
  let pt : Term := if e then .map [] else v
  let at' : Term := if opt then v else .map []
  have hpt : E pt := by by_cases h : e = Bool.true <;> simp [pt, h, ef.none, hv]
  have hat : E at' := by by_cases h : opt = Bool.true <;> simp [at', h, ef.none, hv]
  obtain ⟨F, hF, rF, sF⟩ := field_opt_union_val (den := den) ef (m := m) hm (f₁ := .tuple #[pt, boolAtom Bool.false])
    (f₂ := .tuple #[at', boolAtom Bool.false]) rfl rfl hpt hat []
  refine ⟨_, ?_, ⟨F, Bool.false || Bool.false, rfl, hF⟩, fun o => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_update_field/2»
    simp only [Elixir.Module.Types.Descr.«map_update_apply_callback/3», re, Lynx.Except.ok_bind]
    cases e <;> cases opt <;>
      simp [Lynx.Term.isMember, boolAtom, Erlang.program.«Elixir.Module.Types.Descr:-map_update_field/2-fun-0-/2».pure,
        Elixir.Module.Types.Descr.«-map_update_field/2-fun-0-/3», pt, at'] at rF ⊢ <;> exact rF
  · rw [sF]; simp only [fieldSem_mk]
    have nn : ∀ x, ¬den (.map []) x := fun x h => ef.den_none x h
    constructor
    · rintro ((⟨-, h⟩ | ⟨x, rfl, hx⟩) | (⟨-, h⟩ | ⟨x, rfl, hx⟩))
      · cases h
      · by_cases h : e = Bool.true
        · simp [pt, h] at hx; exact absurd hx (nn x)
        · simp only [pt, h, Bool.false_eq_true, ↓reduceIte] at hx
          obtain ⟨y, hy⟩ : ∃ y, den t y := Classical.byContradiction fun ne =>
            h (se.mpr fun y hy => ne ⟨y, hy⟩)
          exact ⟨⟨x, rfl, hx⟩, some y, Or.inr ⟨y, rfl, hy⟩⟩
      · cases h
      · by_cases h : opt = Bool.true
        · simp only [at', h, ↓reduceIte] at hx
          exact ⟨⟨x, rfl, hx⟩, none, Or.inl ⟨rfl, h⟩⟩
        · simp [at', h] at hx; exact absurd hx (nn x)
    · rintro ⟨⟨x, rfl, hx⟩, o', ⟨rfl, ho⟩ | ⟨y, rfl, hy⟩⟩
      · exact Or.inr (Or.inr ⟨x, rfl, by simp [at', ho, hx]⟩)
      · refine Or.inl (Or.inr ⟨x, rfl, ?_⟩)
        have : e = Bool.false := by
          cases e
          · rfl
          · exact absurd hy (se.mp rfl y)
        simp [pt, this, hx]

/-- `map_get_domain/3` from no type unites the types the tags of the lines give a kind. -/
theorem get_domain1 (ef : EF nd E V den tl K) {n : Nat} (hn : K + 3 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (s : String) :
    ∃ c, Elixir.Module.Types.Descr.«map_get_domain/3» (D n) (Term.list lines) (.atom s) (.map []) = .ok c ∧ E c ∧
      ∀ x, den c x ↔ ∃ L ∈ lines, LineTag den L s x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨c, ⟨hc, sc⟩, rc⟩ := foldl_rel_at (m := k + 1) "Elixir.Module.Types.Descr" "-map_get_domain/3-fun-0-"
    #[.atom s] (fun pre a => E a ∧ ∀ x, den a x ↔ ∃ L ∈ pre, LineTag den L s x) lines
    (fun pre L b mL ⟨hb, sb⟩ => by
      obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl L mL
      have hty := tagType_value ef.mopsE g s
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hty hb (m := k) (by omega)
      refine ⟨c, ⟨hc, fun x => ?_⟩, ?_⟩
      · rw [sc, sb]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | ⟨L', m', h⟩)
          · exact ⟨_, Or.inr rfl, tag, l, negs, rfl, h⟩
          · exact ⟨L', Or.inl m', h⟩
        · rintro ⟨L', m' | e, h⟩
          · exact Or.inr ⟨L', m', h⟩
          · subst e
            obtain ⟨tag', l', negs', e', h'⟩ := h
            obtain ⟨rfl, -, -⟩ := tuple3_inj e'
            exact Or.inl h'
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get_domain/3-fun-0-/2».pure,
          tag_type_run g s, Elixir.Module.Types.Descr.«opt_union/2», rc])
    (.map []) ⟨ef.none, fun x => by simp [ef.den_none x]⟩
  exact ⟨c, by simpa [Elixir.Module.Types.Descr.«map_get_domain/3»] using rc, hc, sc⟩


/-- Keys of a dictionary all before a key. -/
def KeysBelow (dl : List (Term × Term)) (d : Term) : Prop := ∀ e ∈ dl, Term.compare (Term.fuel e.1 d) e.1 d = .lt

/-- `orddict:store/3` of a key after every key of a dictionary appends it. -/
theorem store_last (d T : Term) : ∀ (dl : List (Term × Term)), KeysBelow dl d →
    Erlang.orddict.«store/3» d T (fieldsTerm dl) = .ok (fieldsTerm (dl ++ [(d, T)]))
  | [], _ => by rw [Erlang.orddict.«store/3».eq_def]; simp [fieldsTerm, Term.list]
  | (k, t) :: rest, h => by
    have lt : Term.compare (Term.fuel k d) k d = .lt := h _ List.mem_cons_self
    have gt : Term.compare (Term.fuel d k) d k = .gt := Lynx.Term.compare_gt_iff_lt.mpr lt
    have ih := store_last d T rest fun e me => h e (List.mem_cons_of_mem _ me)
    simp only [fieldsTerm] at ih ⊢
    rw [Erlang.orddict.«store/3».eq_def]
    simp [Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», gt, ih]

/-- `orddict:erase/2` of a key after every key of a dictionary leaves it unchanged. -/
theorem erase_last (d : Term) : ∀ (dl : List (Term × Term)), KeysBelow dl d →
    Erlang.orddict.«erase/2» d (fieldsTerm dl) = .ok (fieldsTerm dl)
  | [], _ => by rw [Erlang.orddict.«erase/2».eq_def]; simp [fieldsTerm, Term.list]
  | (k, t) :: rest, h => by
    have lt : Term.compare (Term.fuel k d) k d = .lt := h _ List.mem_cons_self
    have gt : Term.compare (Term.fuel d k) d k = .gt := Lynx.Term.compare_gt_iff_lt.mpr lt
    have ih := erase_last d rest fun e me => h e (List.mem_cons_of_mem _ me)
    simp only [fieldsTerm] at ih ⊢
    rw [Erlang.orddict.«erase/2».eq_def]
    simp [Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», gt, ih]


/-- Tags built in increasing order of kinds: closed, or domains before a kind. -/
def LowTag (E : Term → Prop) (tag d : Term) : Prop :=
  tag = .atom "closed" ∨ ∃ dl, tag = fieldsTerm dl ∧ DomsV E dl ∧ KeysBelow dl d

theorem lowTag_tagV {tag d : Term} (h : LowTag E tag d) : TagV E tag := by
  rcases h with rfl | ⟨dl, rfl, dv, -⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨dl, rfl, dv⟩)

theorem eqq_val (x y : Term) : Erlang.erlang.«==/2» x y = .ok (boolAtom (Term.compare (Term.fuel x y) x y == .eq)) := by
  simp only [Erlang.erlang.«==/2»]; cases Term.compare (Term.fuel x y) x y <;> simp [boolAtom]

/-- `map_replace_domain/3` on a tag built before a kind sets the type of the kind. -/
theorem replace_domain (ef : EF nd E V den tl K) {tag : Term} {d : String} (hd : d ∈ domainKinds)
    (ht : LowTag E tag (.atom d)) {type : Term} (hty : E type) (m : Nat) :
    ∃ T, Elixir.Module.Types.Descr.«map_replace_domain/3» (D m) tag (.atom d) type = .ok T ∧
      (∀ d', Term.compare (Term.fuel (.atom d) d') (.atom d) d' = .lt → LowTag E T d') ∧
      ∀ kind x, den (tagType T kind) x ↔ if kind = d then den type x else den (tagType tag kind) x := by
  have nn : ∀ x, ¬den (.map []) x := fun x h => ef.den_none x h
  -- An empty type is dropped.
  have drop : Term.compare (Term.fuel type (.map [])) type (.map []) = .eq → ∀ x, ¬den type x := fun e x h =>
    nn x (ef.resp ef.none hty (Lynx.Term.compare_eq_symm e) h)
  rcases ht with rfl | ⟨dl, rfl, dv, below⟩
  · by_cases e : Term.compare (Term.fuel type (.map [])) type (.map []) = .eq
    · refine ⟨.atom "closed", ?_, fun _ _ => Or.inl rfl, fun kind x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]; simp [eqq_val, e, boolAtom]
      · by_cases k : kind = d <;> simp [k, tagType, nn, drop e]
    · refine ⟨fieldsTerm [(.atom d, type)], ?_, fun d' lt => Or.inr ⟨_, rfl, ?_, ?_⟩, fun kind x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]
        simp [eqq_val, e, boolAtom, Erlang.lists.«usort/1», Erlang.lists.«map/2», Erlang.lists.«map_1/2», Erlang.erlang.«is_function/2», fieldsTerm, Term.list,
          Erlang.program.«Elixir.Module.Types.Descr:-map_replace_domain/3-anonymous-1-/1».pure,
          Elixir.Module.Types.Descr.«-map_replace_domain/3-anonymous-1-/2»]
      · exact ⟨fun e me => by simp at me; subst me; exact ⟨⟨d, rfl, hd⟩, hty⟩, by simp⟩
      · intro e me; simp at me; subst me; exact lt
      · rw [tagType_dom]
        by_cases k : kind = d
        · subst k; simp [lookup_cons_atom]
        · simp [k, mapLookup, tagType, nn]
  · have keyOf : ∀ e ∈ dl, ∃ s, e.1 = .atom s := fun e me => ⟨_, (dv.1 e me).1.choose_spec.1⟩
    have look_d : mapLookup dl (.atom d) = none := by
      cases h : mapLookup dl (.atom d) with
      | none => rfl
      | some f =>
        exfalso
        unfold mapLookup at h
        obtain ⟨e, he, -⟩ := Option.map_eq_some_iff.mp h
        have me := List.mem_of_find?_eq_some he
        have ex := List.find?_some he
        simp only [decide_eq_true_eq] at ex
        have := below e me
        rw [show e.1 = .atom d from (compareExact_eq_atom _ _).mp (compareExact_eq_symm ex)] at this
        exact cmp_lt_ne this rfl
    have notAtom : ∀ a : String, fieldsTerm dl ≠ .atom a := fun a h => fieldsTerm_ne_atom dl a h
    by_cases e : Term.compare (Term.fuel type (.map [])) type (.map []) = .eq
    · refine ⟨fieldsTerm dl, ?_, fun d' lt => Or.inr ⟨dl, rfl, dv, fun e' me => cmp_lt_trans (below e' me) lt⟩,
        fun kind x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]
        cases dl with
        | nil =>
          simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1», eqq_val, e, boolAtom]
          simpa [fieldsTerm, Term.list] using erase_last (.atom d) [] (by simp [KeysBelow])
        | cons hd tl =>
          simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1», eqq_val, e, boolAtom]
          simpa [fieldsTerm] using erase_last (.atom d) (hd :: tl) below
      · by_cases k : kind = d
        · subst k; rw [tagType_dom, look_d]; simp [nn, drop e]
        · simp [k]
    · refine ⟨fieldsTerm (dl ++ [(.atom d, type)]), ?_, fun d' lt => Or.inr ⟨_, rfl, ?_, ?_⟩, fun kind x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]
        cases dl with
        | nil => simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1», eqq_val, e, boolAtom,
            Erlang.orddict.«store/3».eq_def]
        | cons hd tl =>
          simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1», eqq_val, e, boolAtom]
          simpa [fieldsTerm] using store_last (.atom d) type (hd :: tl) below
      · refine ⟨fun e' me => ?_, List.pairwise_append.mpr ⟨dv.2, by simp, fun a ma b mb => ?_⟩⟩
        · rcases List.mem_append.mp me with me | me
          · exact dv.1 e' me
          · simp at me; subst me; exact ⟨⟨d, rfl, hd⟩, hty⟩
        · simp at mb; subst mb; exact below a ma
      · intro e' me
        rcases List.mem_append.mp me with me | me
        · exact cmp_lt_trans (below e' me) lt
        · simp at me; subst me; exact lt
      · rw [tagType_dom, tagType_dom, lookup_append]
        by_cases k : kind = d
        · subst k; simp [look_d, lookup_cons_atom]
        · simp [k, mapLookup]


theorem foldl1_prefix_at {m : Nat} (f : Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x rest a, pre ++ x :: rest = l → R pre a → ∃ a', R (pre ++ [x]) a' ∧ (D m).pure f #[x, a] = .ok a') :
    ∀ (rest pre : List Term) acc, pre ++ rest = l → R pre acc →
      ∃ r, R l r ∧ Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .ok r := by
  intro rest
  induction rest with
  | nil => intro pre acc e h; exact ⟨acc, by simpa [← e] using h, by simp [Erlang.lists.«foldl_1/3»]⟩
  | cons x xs ih =>
    intro pre acc e h
    obtain ⟨a', h', run⟩ := step pre x xs acc e h
    obtain ⟨r, hr, rest⟩ := ih (pre ++ [x]) a' (by simpa using e) h'
    refine ⟨r, hr, ?_⟩
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only at rest ⊢
    simp only [run, Lynx.Except.ok_bind]
    exact rest

/-- Folds whose steps know the elements folded before and after the current one. -/
theorem foldl_prefix_at {m : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x rest a, pre ++ x :: rest = l → R pre a → ∃ a', R (pre ++ [x]) a' ∧
      (D m).pure (.function mo nm 2 caps) #[x, a] = .ok a') (acc : Term) (h : R [] acc) :
    ∃ r, R l r ∧ Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .ok r := by
  obtain ⟨r, hr, run⟩ := foldl1_prefix_at (.function mo nm 2 caps) R l step l [] acc (by simp) h
  refine ⟨r, hr, ?_⟩
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using run
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at run
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using run

theorem kinds_sorted : (domainKinds.map Term.atom).Pairwise
    (fun a b => Term.compare (Term.fuel a b) a b = .lt) := by
  simp only [domainKinds, List.map, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, atoms_cmp, List.Pairwise.nil, and_true]
  and_intros <;> first | rfl | (intro _ h; exact h.elim)

/-- Domain updates: each with a non-empty new type. -/
def DomUpdates (E : Term → Prop) (den : Term → V → Prop) (U : List Term) : Prop :=
  ∀ u ∈ U, ∃ d o nt, u = .tuple #[d, o, nt] ∧ E nt ∧ ∃ x, den nt x

/-- `orddict:fold/3` consing the keys of fields, with either of the two key-collecting functions of
`map_update_box/5`. -/
theorem box_key_fold (nm : String) (hnm : nm = "-map_update_box/5-fun-0-" ∨ nm = "-map_update_box/5-fun-1-")
    (m : Nat) : ∀ (l : List (Term × Term)), FieldsV E l → ∀ acc : List Term,
    ∃ ks, Erlang.orddict.«fold/3» (D (m + 1)) (.function "Elixir.Module.Types.Descr" nm 3 #[]) (Term.list acc)
        (fieldsTerm l) = .ok (Term.list (ks ++ acc)) ∧ (∀ s ∈ keyStrs l, .atom s ∈ ks) ∧
      ∀ k ∈ ks, ∃ s, k = .atom s ∧ s ∈ keyStrs l
  | [], _, acc => ⟨[], by rw [Erlang.orddict.«fold/3».eq_def]; simp [fieldsTerm, Term.list,
      Erlang.erlang.«is_function/2»], by simp [keyStrs], by simp⟩
  | (k, f) :: t, sl, acc => by
    obtain ⟨⟨b, rfl⟩, -⟩ := sl.1 _ List.mem_cons_self
    obtain ⟨ks, run, hk, ha⟩ := box_key_fold nm hnm m t (fieldsV_tail sl) (.atom b :: acc)
    refine ⟨ks ++ [.atom b], ?_, fun s ms => ?_, fun k mk => ?_⟩
    · rw [Erlang.orddict.«fold/3».eq_def]
      have step : (D (m + 1)).pure (.function "Elixir.Module.Types.Descr" nm 3 #[]) #[.atom b, f, Term.list acc] =
          .ok (Term.list (.atom b :: acc)) := by
        rcases hnm with rfl | rfl
        · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-0-/3».pure]
          simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-0-/3», Term.list]
        · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-1-/3».pure]
          simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-1-/3», Term.list]
      simp [fieldsTerm_cons, step]
      simpa [Term.list] using run
    · simp only [keyStrs, List.filterMap_cons, List.mem_cons] at ms
      rcases ms with rfl | ms
      · simp
      · exact List.mem_append_left _ (hk s ms)
    · rcases List.mem_append.mp mk with mk | mk
      · obtain ⟨s, rfl, hs⟩ := ha k mk
        exact ⟨s, rfl, by simp only [keyStrs, List.filterMap_cons, List.mem_cons] at hs ⊢; exact Or.inr hs⟩
      · simp at mk; exact ⟨b, mk, by simp [keyStrs]⟩


/-- Atoms a line names, in its fields or in those of its negations. -/
def LineNames (L : Term) (s : String) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    (s ∈ keyStrs l ∨ ∃ N ∈ negs, ∃ (k : Int) (t : Term) (l' : List (Term × Term)),
      N = .tuple #[.integer k, t, fieldsTerm l'] ∧ s ∈ keyStrs l')

/-- The fold of `map_update_box/5` collecting the atoms the lines name. -/
theorem box_names (m : Nat) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) (acc : List Term) :
    ∃ X, Erlang.lists.«foldl/3» (D (m + 3)) (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-3-" 2 #[])
        (Term.list acc) (Term.list lines) = .ok (Term.list X) ∧ (∀ a ∈ acc, a ∈ X) ∧
      (∀ L ∈ lines, ∀ s, LineNames L s → .atom s ∈ X) ∧
      ∀ k ∈ X, k ∈ acc ∨ ∃ L ∈ lines, ∃ s, k = .atom s ∧ LineNames L s := by
  obtain ⟨r, ⟨X, rfl, hacc, hn, hk⟩, run⟩ := foldl_rel_at (m := m + 3) "Elixir.Module.Types.Descr"
    "-map_update_box/5-fun-3-" #[]
    (fun pre a => ∃ X, a = Term.list X ∧ (∀ a ∈ acc, a ∈ X) ∧ (∀ L ∈ pre, ∀ s, LineNames L s → .atom s ∈ X) ∧
      ∀ k ∈ X, k ∈ acc ∨ ∃ L ∈ pre, ∃ s, k = .atom s ∧ LineNames L s) lines
    (fun pre L a mL ⟨X, ha, hacc, hn, hk⟩ => by
      subst ha
      obtain ⟨tag, l, negs, rfl, -, sl, lits⟩ := hl L mL
      obtain ⟨ks, rks, hks, aks⟩ := box_key_fold (E := E) _ (Or.inl rfl) (m + 1) l sl X
      -- The negations.
      obtain ⟨Y, ⟨ys, rfl, -, nys, ays⟩, rY⟩ := foldl_rel_at (m := m + 2) "Elixir.Module.Types.Descr"
        "-map_update_box/5-fun-2-" #[]
        (fun pre' a => ∃ ys, a = Term.list (ys ++ ks ++ X) ∧ True ∧
          (∀ N ∈ pre', ∀ (k : Int) (t : Term) (l' : List (Term × Term)), N = .tuple #[.integer k, t, fieldsTerm l'] →
            ∀ s ∈ keyStrs l', .atom s ∈ ys) ∧
          ∀ k ∈ ys, ∃ s, k = .atom s ∧ ∃ N ∈ pre', ∃ (k : Int) (t : Term) (l' : List (Term × Term)),
            N = .tuple #[.integer k, t, fieldsTerm l'] ∧ s ∈ keyStrs l') negs
        (fun pre' N a mN ⟨ys, ha, _, hys, ays⟩ => by
          subst ha
          obtain ⟨k, t, l', rfl, -, sl'⟩ := lits N mN
          obtain ⟨zs, rzs, hzs, azs⟩ := box_key_fold (E := E) _ (Or.inr rfl) m l' sl' (ys ++ ks ++ X)
          refine ⟨Term.list (zs ++ ys ++ ks ++ X), ⟨zs ++ ys, by simp, trivial, fun N' mN' k' t' l'' e s ms => ?_,
            fun k' mk => ?_⟩, ?_⟩
          · rcases List.mem_append.mp mN' with mN' | mN'
            · exact List.mem_append_right _ (hys N' mN' k' t' l'' e s ms)
            · simp at mN'; subst mN'
              obtain ⟨-, -, e₃⟩ := tuple3_inj e
              rw [← fieldsTerm_inj e₃] at ms
              exact List.mem_append_left _ (hzs s ms)
          · rcases List.mem_append.mp mk with mk | mk
            · obtain ⟨s, rfl, hs⟩ := azs k' mk
              exact ⟨s, rfl, _, by simp, k, t, l', rfl, hs⟩
            · obtain ⟨s, rfl, N', mN', h⟩ := ays k' mk
              exact ⟨s, rfl, N', List.mem_append_left _ mN', h⟩
          · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-2-/2».pure]
            simpa [Elixir.Module.Types.Descr.«-map_update_box/5-fun-2-/2»] using rzs)
        (Term.list (ks ++ X)) ⟨[], by simp, trivial, fun N m => by simp at m, by simp⟩
      refine ⟨_, ⟨ys ++ ks ++ X, rfl, fun a ma => by simp [hacc a ma], fun L' mL' s hs => ?_, fun k mk => ?_⟩, ?_⟩
      · rcases List.mem_append.mp mL' with mL' | mL'
        · simp [hn L' mL' s hs]
        · simp at mL'; subst mL'
          obtain ⟨tag', l', negs', e, h⟩ := hs
          obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
          have := fieldsTerm_inj e₂; subst this
          have : negs' = negs := list_inj e₃.symm
          subst this
          rcases h with h | ⟨N, mN, k, t, l'', e', ms⟩
          · simp [hks s h]
          · simp [nys N mN k t l'' e' s ms]
      · simp only [List.mem_append] at mk
        rcases mk with (mk | mk) | mk
        · obtain ⟨s, rfl, N, mN, k, t, l', e, ms⟩ := ays k mk
          exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), s, rfl, tag, l, negs, rfl,
            Or.inr ⟨N, mN, k, t, l', e, ms⟩⟩
        · obtain ⟨s, rfl, ms⟩ := aks k mk
          exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), s, rfl, tag, l, negs, rfl, Or.inl ms⟩
        · rcases hk k mk with h | ⟨L', mL', h⟩
          · exact Or.inl h
          · exact Or.inr ⟨L', List.mem_append_left _ mL', h⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-3-/2».pure]
        simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-3-/2», rks, rY])
    (Term.list acc) ⟨acc, rfl, fun a m => m, fun L m => by simp at m, fun k m => Or.inl m⟩
  exact ⟨X, run, hacc, hn, hk⟩

theorem foldr1_rel_at {m : Nat} (f : Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x suf a, pre ++ x :: suf = l → R suf a → ∃ a', R (x :: suf) a' ∧ (D m).pure f #[x, a] = .ok a')
    (acc : Term) (h : R [] acc) : ∀ (rest pre : List Term), pre ++ rest = l →
      ∃ r, R rest r ∧ Erlang.lists.«foldr_1/3» (D m) f acc (Term.list rest) = .ok r := by
  intro rest
  induction rest with
  | nil => intro _ _; exact ⟨acc, h, by simp [Erlang.lists.«foldr_1/3»]⟩
  | cons x xs ih =>
    intro pre e
    obtain ⟨a, ha, run⟩ := ih (pre ++ [x]) (by simpa using e)
    obtain ⟨a', ha', run'⟩ := step pre x xs a e ha
    refine ⟨a', ha', ?_⟩
    rw [Erlang.lists.«foldr_1/3».eq_def]
    simp only [] at run ⊢
    simp [run, run']

/-- Right folds whose steps keep a relation between the elements folded so far and the accumulator. -/
theorem foldr_rel_at {m : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x suf a, pre ++ x :: suf = l → R suf a → ∃ a', R (x :: suf) a' ∧
      (D m).pure (.function mo nm 2 caps) #[x, a] = .ok a') (acc : Term) (h : R [] acc) :
    ∃ r, R l r ∧ Erlang.lists.«foldr/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .ok r := by
  obtain ⟨r, hr, run⟩ := foldr1_rel_at (.function mo nm 2 caps) R l step acc h l [] rfl
  exact ⟨r, hr, by simpa [Erlang.lists.«foldr/3», Erlang.erlang.«is_function/2»] using run⟩


theorem member_atoms (s : String) : ∀ ks : List String,
    Erlang.lists.«member/2» (.atom s) (Term.list (ks.map Term.atom)) = .ok (if s ∈ ks then Term.true else Term.false)
  | [] => by simp [Term.list, Erlang.lists.«member/2»]
  | k :: t => by
    have ih := member_atoms s t
    by_cases h : s = k
    · subst h; simp [Term.list, Erlang.lists.«member/2»]
    · simp only [Term.list, List.map] at ih ⊢
      simp [Erlang.lists.«member/2», h, ih]

/-- What the tag of the box allows at the keys of a kind: values of the lines' tags, and the value at updated kinds. -/
def BoxTagD (den : Term → V → Prop) (lines : List Term) (v : Term) (Ds : List String) (kind : String) (x : V) : Prop :=
  (∃ L ∈ lines, LineTag den L kind x) ∨ (kind ∈ Ds ∧ den v x)

/-- The fold of `map_update_box/5` over the kinds of keys: the tag, and the updated domains. -/
theorem box_domainsD (ef : EF nd E V den tl K) {n : Nat} (hn : K + 3 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) {v : Term} (hv : E v) (Ds : List String)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∃ T U, Erlang.lists.«foldl/3» (D (n + 1))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-7-" 2 #[Term.list lines, Term.list (Ds.map Term.atom), forceOp v])
        (.tuple #[.atom "closed", .nil]) (Term.list (domainKinds.map Term.atom)) = .ok (.tuple #[T, Term.list U]) ∧
      LowTag E T (.atom "zzz") ∧ (∀ kind ∈ domainKinds, ∀ x, den (tagType T kind) x ↔ BoxTagD den lines v Ds kind x) ∧
      DomUpdates E den U ∧ (U ≠ [] ↔ Ds ≠ [] ∧ ∃ x, den v x) := by
  have nn : ∀ x, ¬den (.map []) x := fun x h => ef.den_none x h
  let R : List Term → Term → Prop := fun pre a => ∃ T U, a = .tuple #[T, Term.list U] ∧
    (∀ d', (∀ p ∈ pre, Term.compare (Term.fuel p d') p d' = .lt) → LowTag E T d') ∧
    (∀ kind x, den (tagType T kind) x ↔ .atom kind ∈ pre ∧ BoxTagD den lines v Ds kind x) ∧
    DomUpdates E den U ∧ (U ≠ [] ↔ (∃ d ∈ Ds, .atom d ∈ pre) ∧ ∃ x, den v x)
  obtain ⟨r, ⟨T, U, rfl, low, sem, du, ne⟩, run⟩ := foldl_prefix_at (m := n + 1) "Elixir.Module.Types.Descr"
    "-map_update_box/5-fun-7-" #[Term.list lines, Term.list (Ds.map Term.atom), forceOp v] R (domainKinds.map Term.atom)
    (fun pre x rest a e ⟨T, U, ha, low, sem, du, ne⟩ => by
      subst ha
      have mx : x ∈ domainKinds.map Term.atom := by rw [← e]; simp
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp mx
      have before : ∀ p ∈ pre, Term.compare (Term.fuel p (.atom d)) p (.atom d) = .lt := by
        have := kinds_sorted; rw [← e, List.pairwise_append] at this
        exact fun p mp => this.2.2 p mp _ List.mem_cons_self
      obtain ⟨old, rold, hold, sold⟩ := get_domain1 ef (n := n) (by omega) lines hl d
      have pureE : ∀ a, (D (n + 1)).pure (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-7-" 2
          #[Term.list lines, Term.list (Ds.map Term.atom), forceOp v]) #[.atom d, a] =
          Elixir.Module.Types.Descr.«-map_update_box/5-fun-7-/5» (D n) (Term.list lines) (Term.list (Ds.map Term.atom)) (forceOp v)
            (.atom d) a := fun a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-7-/2».pure]
      -- The kind's new type and the updates, then the tag.
      have finish : ∀ type U', E type → (∀ x, den type x ↔ den old x ∨ (d ∈ Ds ∧ den v x)) →
          DomUpdates E den U' → (U' ≠ [] ↔ U ≠ [] ∨ (d ∈ Ds ∧ ∃ x, den v x)) →
          ∃ T', Elixir.Module.Types.Descr.«map_replace_domain/3» (D n) T (.atom d) type = .ok T' ∧
            R (pre ++ [.atom d]) (.tuple #[T', Term.list U']) := fun type U' hty stype du' ne' => by
        obtain ⟨T', rT, low', sT'⟩ := replace_domain ef hd (low _ before) hty n
        refine ⟨T', rT, T', U', rfl, fun d' h => low' d' (h _ (by simp)), fun kind x => ?_, du', ?_⟩
        · rw [sT']
          by_cases k : kind = d
          · subst k
            rw [ite_eq_left rfl, stype, sold]
            simp only [BoxTagD, List.mem_append, List.mem_singleton, or_true, true_and]
          · rw [ite_eq_right k, sem]
            simp [k]
        · rw [ne', ne]
          constructor
          · rintro (⟨⟨d', md, hm⟩, hx⟩ | ⟨md, hx⟩)
            · exact ⟨⟨d', md, List.mem_append_left _ hm⟩, hx⟩
            · exact ⟨⟨d, md, by simp⟩, hx⟩
          · rintro ⟨⟨d', md, hm⟩, hx⟩
            rcases List.mem_append.mp hm with hm | hm
            · exact Or.inl ⟨⟨d', md, hm⟩, hx⟩
            · simp at hm; subst hm; exact Or.inr ⟨md, hx⟩
      have mem := member_atoms d Ds
      by_cases up : d ∈ Ds
      · simp only [up, ↓reduceIte] at mem
        obtain ⟨F, rF, hF, sF⟩ := update_field_force ef (m := n) (by omega) hv (old := .tuple #[old, .atom "true"])
          ⟨old, Bool.true, rfl, hold⟩
        obtain ⟨nt, no, rfl, hnt⟩ := hF
        have snt : ∀ x, den nt x ↔ den v x := fun x => by
          have := sF (some x)
          rw [fieldSem_mk] at this
          simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or] at this
          rw [this]
          have hn : FieldSem den (.tuple #[old, .atom "true"]) none := by
            rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; simp
          exact ⟨fun h => h.1, fun h => ⟨h, none, hn⟩⟩
        obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef (m := n) (by omega) ⟨nt, no, rfl, hnt⟩
        by_cases vx : ∃ x, den v x
        · have bf : b = Bool.false := by
            cases b
            · rfl
            · obtain ⟨x, hx⟩ := vx
              exact absurd ((sF (some x)).mpr ⟨⟨x, rfl, hx⟩, none, by
                rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; simp⟩) (sb.mp rfl _)
          subst bf
          obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hold hnt (m := n) (by omega)
          obtain ⟨T', rT, hR⟩ := finish c (.tuple #[.atom d, old, nt] :: U) hc
            (fun x => by rw [sc, snt]; simp [up]) (fun u mu => by
              rcases List.mem_cons.mp mu with rfl | mu
              · obtain ⟨x, hx⟩ := vx; exact ⟨_, _, _, rfl, hnt, x, (snt x).mpr hx⟩
              · exact du u mu) (by simp [vx, up])
          refine ⟨_, hR, ?_⟩
          rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-7-/5», rold, mem, Term.true,
            rF, Elixir.Module.Types.Descr.«opt_union/2», rc]
          rw [rb]
          simp [boolAtom, rT]
        · have bt : b = Bool.true := sb.mpr fun o h => vx (by
            obtain ⟨⟨x, -, hx⟩, -⟩ := (sF o).mp h; exact ⟨x, hx⟩)
          subst bt
          obtain ⟨T', rT, hR⟩ := finish old U hold
            (fun x => ⟨Or.inl, fun h => h.elim id fun ⟨_, hx⟩ => absurd ⟨x, hx⟩ vx⟩) du
            ⟨Or.inl, fun h => h.elim id fun ⟨_, hx⟩ => absurd hx vx⟩
          refine ⟨_, hR, ?_⟩
          rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-7-/5», rold, mem, Term.true, rF]
          rw [rb]
          simp [boolAtom, rT, Elixir.Module.Types.Descr.«-map_update_box/5-fun-6-/3»]
      · obtain ⟨T', rT, hR⟩ := finish old U hold
          (fun x => ⟨Or.inl, fun h => h.elim id fun ⟨a, _⟩ => absurd a up⟩) du
          ⟨Or.inl, fun h => h.elim id fun ⟨a, _⟩ => absurd a up⟩
        refine ⟨_, hR, ?_⟩
        rw [pureE]
        have nm : Erlang.lists.«member/2» (.atom d) (Term.list (Ds.map Term.atom)) = .ok (.atom "false") := by
          simpa [up, Term.false] using mem
        simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-7-/5», rold, nm, rT,
          Elixir.Module.Types.Descr.«-map_update_box/5-fun-6-/3», Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-6-/1».pure])
    _ ⟨.atom "closed", [], rfl, fun _ _ => Or.inl rfl, fun kind x => by simp [tagType, nn], fun u mu => by simp at mu,
      by simp []⟩
  refine ⟨T, U, run, low _ fun p mp => ?_, fun kind mk x => (sem kind x).trans ?_, du, ne.trans ?_⟩
  · simp only [domainKinds, List.map, List.mem_cons, List.not_mem_nil, or_false] at mp
    rcases mp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp [List.mem_map, mk]
  · constructor
    · rintro ⟨⟨d, md, -⟩, hx⟩; exact ⟨List.ne_nil_of_mem md, hx⟩
    · rintro ⟨ne, hx⟩
      obtain ⟨d, md⟩ := List.exists_mem_of_ne_nil Ds ne
      exact ⟨⟨d, md, List.mem_map_of_mem (hD d md)⟩, hx⟩


/-- The key of an update. -/
def updKey : Term → Term
  | .tuple ⟨[k, _, _]⟩ => k
  | _ => .nil

/-- An updated named key: the old field, as the lines hold it, and the new one. -/
def KeyUpd (E : Term → Prop) (den : Term → V → Prop) (lines : List Term) (v : Term) (s : String) (q : Term) : Prop :=
  ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldValue E old ∧ (∀ o, FieldSem den old o ↔ ∃ L ∈ lines, LongM den L s o) ∧
    FieldValue E new ∧ ∀ o, FieldSem den new o ↔ (∃ x, o = some x ∧ den v x) ∧ ∃ o', FieldSem den old o'

/-- The fold of `map_update_box/5` over the named keys: their fields over the lines, and the updates of those
among the updated keys. -/
theorem box_fields (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) {v : Term} (hv : E v) (ks NK : List String)
    (nd : NK.Nodup) :
    ∃ P Q, Erlang.lists.«foldr/3» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-4-" 2
          #[Term.list lines, Term.list (ks.map Term.atom), forceOp v])
        (.tuple #[.nil, .nil]) (Term.list (NK.map Term.atom)) = .ok (.tuple #[fieldsTerm P, Term.list Q]) ∧
      P.map Prod.fst = NK.map Term.atom ∧
      (∀ e ∈ P, ∃ s, e.1 = .atom s ∧ FieldValue E e.2 ∧ ∀ o, FieldSem den e.2 o ↔ ∃ L ∈ lines, LongM den L s o) ∧
      (∀ q ∈ Q, ∃ s, s ∈ ks ∧ KeyUpd E den lines v s q) ∧
      (∀ s ∈ NK, s ∈ ks → ∃ q ∈ Q, KeyUpd E den lines v s q) ∧ (Q.map updKey).Nodup ∧
      ∀ q ∈ Q, updKey q ∈ NK.map Term.atom := by
  obtain ⟨r, ⟨P, Q, rfl, hP, fP, uQ, cQ, kQ, nQ⟩, run⟩ := foldr_rel_at (m := n + 4) "Elixir.Module.Types.Descr"
    "-map_update_box/5-fun-4-" #[Term.list lines, Term.list (ks.map Term.atom), forceOp v]
    (fun suf a => ∃ P Q, a = .tuple #[fieldsTerm P, Term.list Q] ∧ P.map Prod.fst = suf ∧
      (∀ e ∈ P, ∃ s, e.1 = .atom s ∧ FieldValue E e.2 ∧ ∀ o, FieldSem den e.2 o ↔ ∃ L ∈ lines, LongM den L s o) ∧
      (∀ q ∈ Q, ∃ s, s ∈ ks ∧ KeyUpd E den lines v s q) ∧
      (∀ s, .atom s ∈ suf → s ∈ ks → ∃ q ∈ Q, KeyUpd E den lines v s q) ∧ (∀ q ∈ Q, updKey q ∈ suf) ∧
      (Q.map updKey).Nodup) (NK.map Term.atom)
    (fun pre x suf a e ⟨P, Q, ha, hP, fP, uQ, cQ, kQ, nQ⟩ => by
      subst ha
      have mx : x ∈ NK.map Term.atom := by rw [← e]; simp
      have xs : x ∉ suf := by
        have : (NK.map Term.atom).Nodup := List.pairwise_map.mpr (nd.imp fun h e => h (Term.atom.inj e))
        rw [← e] at this
        exact (List.nodup_cons.mp (List.nodup_append.mp this).2.1).1
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp mx
      obtain ⟨old, rold, hold, sold⟩ := mdnf_fetch ef hn s lines hl
      have pureE : ∀ a, (D (n + 4)).pure (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-4-" 2
          #[Term.list lines, Term.list (ks.map Term.atom), forceOp v]) #[.atom s, a] =
          Elixir.Module.Types.Descr.«-map_update_box/5-fun-4-/5» (D (n + 3)) (Term.list lines)
            (Term.list (ks.map Term.atom)) (forceOp v) (.atom s) a := fun a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-4-/2».pure]
      have mem := member_atoms s ks
      by_cases sk : s ∈ ks
      · obtain ⟨F, rF, hF, sF⟩ := update_field_force ef (m := n + 3) (by omega) hv hold
        obtain ⟨ft, fo, rfl, hft⟩ := hF
        refine ⟨_, ⟨(.atom s, old) :: P, .tuple #[.atom s, old, .tuple #[ft, boolAtom fo]] :: Q, rfl, by simp [hP],
          fun e me => ?_, fun q mq => ?_, fun s' ms' hs' => ?_, fun q mq => ?_, ?_⟩, ?_⟩
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨s, rfl, hold, sold⟩
          · exact fP e me
        · rcases List.mem_cons.mp mq with rfl | mq
          · exact ⟨s, sk, old, _, rfl, hold, sold, ⟨ft, fo, rfl, hft⟩, sF⟩
          · exact uQ q mq
        · rcases List.mem_cons.mp ms' with e | ms'
          · cases e; exact ⟨_, List.mem_cons_self, old, _, rfl, hold, sold, ⟨ft, fo, rfl, hft⟩, sF⟩
          · obtain ⟨q, mq, hq⟩ := cQ s' ms' hs'
            exact ⟨q, List.mem_cons_of_mem _ mq, hq⟩
        · rcases List.mem_cons.mp mq with rfl | mq
          · simp [updKey]
          · exact List.mem_cons_of_mem _ (kQ q mq)
        · refine List.nodup_cons.mpr ⟨fun m => ?_, nQ⟩
          obtain ⟨q, mq, eq⟩ := List.mem_map.mp m
          obtain ⟨s', -, old', new', rfl, -⟩ := uQ q mq
          have := kQ _ mq
          simp only [updKey] at eq this
          rw [eq] at this
          exact xs this
        · rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-4-/5», rold, mem, sk, rF, Term.true, fieldsTerm_cons]
      · refine ⟨_, ⟨(.atom s, old) :: P, Q, rfl, by simp [hP], fun e me => ?_, uQ, fun s' ms' hs' => ?_,
          fun q mq => List.mem_cons_of_mem _ (kQ q mq), nQ⟩, ?_⟩
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨s, rfl, hold, sold⟩
          · exact fP e me
        · rcases List.mem_cons.mp ms' with e | ms'
          · cases e; exact absurd hs' sk
          · exact cQ s' ms' hs'
        · rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-4-/5», rold, mem, sk, Term.false, fieldsTerm_cons])
    (.tuple #[.nil, .nil]) ⟨[], [], by simp [fieldsTerm, Term.list], rfl, by simp, by simp, by simp, by simp, by simp⟩
  exact ⟨P, Q, run, hP, fP, uQ, fun s ms hs => cQ s (List.mem_map_of_mem ms) hs, nQ, kQ⟩


/-- The new field of an update. -/
def updNew : Term → Term
  | .tuple ⟨[_, _, new]⟩ => new
  | _ => .nil

/-- The filter of `map_update_box/5` keeps the updates with a non-empty new field. -/
theorem box_filter (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {lines : List Term} {v : Term} {ks : List String}
    (Q : List Term) (uQ : ∀ q ∈ Q, ∃ s, s ∈ ks ∧ KeyUpd E den lines v s q) :
    ∃ Q', Erlang.lists.«filter/2» (D (m + 1)) (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-5-" 1 #[])
        (Term.list Q) = .ok (Term.list Q') ∧ Q'.Sublist Q ∧
      (∀ q ∈ Q, (∃ o, FieldSem den (updNew q) o) → q ∈ Q') ∧ ∀ q ∈ Q', ∃ o, FieldSem den (updNew q) o := by
  classical
  let res : Term → Bool := fun q => decide (∃ o, FieldSem den (updNew q) o)
  refine ⟨Q.filter res, filter_list _ _ _ _ res Q fun q mq => ?_, List.filter_sublist,
    fun q mq h => List.mem_filter.mpr ⟨mq, by simp [res, h]⟩, fun q mq => by
      have := (List.mem_filter.mp mq).2; simpa [res] using this⟩
  obtain ⟨s, -, old, new, rfl, -, -, hnew, -⟩ := uQ q mq
  obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef hm hnew
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-5-/1».pure]
  simp only [Elixir.Module.Types.Descr.«-map_update_box/5-fun-5-/1», rb, Lynx.Except.ok_bind]
  cases b
  · have : ∃ o, FieldSem den new o := Classical.byContradiction fun h => by
      have := sb.mpr fun o ho => h ⟨o, ho⟩; cases this
    simp [Erlang.erlang.«not/1», boolAtom, res, updNew, this]
  · have : ¬∃ o, FieldSem den new o := fun ⟨o, ho⟩ => sb.mp rfl o ho
    simp [Erlang.erlang.«not/1», boolAtom, res, updNew, this]


/-- The fold of `map_update_box/5` storing each update, when not replacing: the old field, the field of the key,
united with the new one. -/
theorem box_store (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {P : List (Term × Term)} (sP : FieldsV E P)
    (Q : List Term) (uQ : ∀ q ∈ Q, ∃ (s : String) (old new : Term), q = .tuple #[.atom s, old, new] ∧
      FieldValue E old ∧ FieldValue E new ∧ ∃ f, mapLookup P (.atom s) = some f ∧ ∀ o, FieldSem den old o ↔ FieldSem den f o)
    (nQ : (Q.map updKey).Nodup) :
    ∃ P2, Erlang.lists.«foldl/3» (D (m + 1)) (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-8-" 2
        #[.atom "false"]) (fieldsTerm P) (Term.list Q) = .ok (fieldsTerm P2) ∧ FieldsV E P2 ∧
      (∀ s, mapLookup P2 (.atom s) = none ↔ mapLookup P (.atom s) = none) ∧
      ∀ s o, (∃ f, mapLookup P2 (.atom s) = some f ∧ FieldSem den f o) ↔
        (∃ f, mapLookup P (.atom s) = some f ∧ FieldSem den f o) ∨
        ∃ q ∈ Q, ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new o := by
  obtain ⟨r, ⟨P2, rfl, sP2, keys, look⟩, run⟩ := foldl_prefix_at (m := m + 1) "Elixir.Module.Types.Descr"
    "-map_update_box/5-fun-8-" #[.atom "false"]
    (fun pre a => ∃ P2, a = fieldsTerm P2 ∧ FieldsV E P2 ∧
      (∀ s, mapLookup P2 (.atom s) = none ↔ mapLookup P (.atom s) = none) ∧ ∀ s o,
      (∃ f, mapLookup P2 (.atom s) = some f ∧ FieldSem den f o) ↔
        (∃ f, mapLookup P (.atom s) = some f ∧ FieldSem den f o) ∨
        ∃ q ∈ pre, ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new o) Q
    (fun pre q rest a e ⟨P2, ha, sP2, keys, look⟩ => by
      subst ha
      have mq : q ∈ Q := by rw [← e]; simp
      obtain ⟨s, old, new, rfl, ⟨t₁, o₁, rfl, h₁⟩, ⟨t₂, o₂, rfl, h₂⟩, f₀, lf₀, sf₀⟩ := uQ _ mq
      -- No update before has the key.
      have fresh : ∀ q' ∈ pre, updKey q' ≠ .atom s := by
        have := nQ; rw [← e, List.map_append, List.map_cons] at this
        intro q' mq' eq
        exact (List.nodup_append.mp this).2.2 _ (List.mem_map_of_mem mq') _ List.mem_cons_self
          (eq.trans (by simp [updKey]))
      obtain ⟨t, ht, rt, st⟩ := field_opt_union_val (den := den) ef (m := m) hm rfl rfl h₁ h₂ []
      obtain ⟨P3, rP3, sP3, -, look3⟩ := store_val s ⟨t, _, rfl, ht⟩ sP2
      refine ⟨_, ⟨P3, rfl, sP3, fun s' => ?_, fun s' o => ?_⟩, ?_⟩
      · rw [look3 s']
        by_cases es : s = s'
        · subst es; simp [lf₀]
        · simp only [es, ↓reduceIte]; exact keys s'
      · rw [look3 s']
        by_cases es : s = s'
        · subst es
          simp only [↓reduceIte, Option.some.injEq, exists_eq_left']
          rw [st, sf₀]
          constructor
          · rintro (h | h)
            · exact Or.inl ⟨f₀, lf₀, h⟩
            · exact Or.inr ⟨.tuple #[.atom s, .tuple #[t₁, boolAtom o₁], .tuple #[t₂, boolAtom o₂]], by simp, _, _, rfl, h⟩
          · rintro (⟨f, lf, h⟩ | ⟨q', mq', old', new', e', h⟩)
            · rw [lf₀] at lf; cases lf; exact Or.inl h
            · rcases List.mem_append.mp mq' with mq' | mq'
              · exact absurd (by rw [e']; simp [updKey]) (fresh q' mq')
              · simp at mq'; subst mq'
                obtain ⟨-, -, e₃⟩ := tuple3_inj e'
                rw [e₃]; exact Or.inr h
        · simp only [es, ↓reduceIte]
          rw [look s' o]
          constructor
          · rintro (h | ⟨q', mq', old', new', e', h⟩)
            · exact Or.inl h
            · exact Or.inr ⟨q', by simp [mq'], old', new', e', h⟩
          · rintro (h | ⟨q', mq', old', new', e', h⟩)
            · exact Or.inl h
            · rcases List.mem_append.mp mq' with mq' | mq'
              · exact Or.inr ⟨q', mq', old', new', e', h⟩
              · simp at mq'; subst mq'
                obtain ⟨e₁, -, -⟩ := tuple3_inj e'
                exact absurd (Term.atom.inj e₁) es
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-8-/2».pure]
        simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-8-/3», Lynx.Term.isMember, rt, rP3])
    (fieldsTerm P) ⟨P, rfl, sP, fun s => Iff.rfl, fun s o => by simp⟩
  exact ⟨P2, run, sP2, keys, look⟩


/-- `opt_difference/2` of two types holding only maps: the maps of the first outside the second. -/
theorem map_opt_diff1 (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {a b : Term} (fa : MField E a)
    (fb : MField E b) :
    ∃ r, Elixir.Module.Types.Descr.«opt_difference/2» (D (m + 2)) (.map [(.atom "map", a)]) (.map [(.atom "map", b)]) =
        .ok r ∧ ((r = .map [] ∧ ∀ w, (denMF E den a w && !denMF E den b w) = Bool.false) ∨
        ∃ c, r = .map [(.atom "map", c), (.atom "map", a)] ∧ MField E c ∧
          ∀ w, denMF E den c w = (denMF E den a w && !denMF E den b w)) := by
  obtain ⟨r, run, k, d⟩ := map_field_opt_diff (den := den) ef hm fa fb []
  let g : Term → Term → Term → Term := fun _ _ _ => r
  have step := difference_step m
    (.function "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-0-" 3 #[.map []]) g [(.atom "map", a)]
    (.atom "map") b (fun v₁ hv => by
      simp [mapLookup] at hv; subst hv
      rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_difference/3-anonymous-0-/3».pure]
      simpa [Elixir.Module.Types.Descr.«-opt_difference/3-anonymous-0-/4»] using run)
  have res : Elixir.Module.Types.Descr.«opt_difference/2» (D (m + 2)) (.map [(.atom "map", a)])
      (.map [(.atom "map", b)]) = .ok (.map (differenceStep g [(.atom "map", a)] (.atom "map", b))) := by
    unfold Elixir.Module.Types.Descr.«opt_difference/2» Elixir.Module.Types.Descr.«opt_difference/3»
    simp [Erlang.erlang.«==/2», unfold_map, Erlang.erlang.«is_map_key/2»]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», Erlang.maps.«fold/3», step]
  refine ⟨_, res, ?_⟩
  cases kr : kept (.atom "map", r)
  · refine Or.inl ⟨by simp [differenceStep, mapLookup, g, kr], d kr⟩
  · obtain ⟨fr, sr⟩ := k kr
    exact Or.inr ⟨r, by simp [differenceStep, mapLookup, g, kr], fr, sr⟩


/-- `map_new/2` makes a map field of the maps of a literal. -/
theorem map_new_leaf (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l) :
    ∃ b, Elixir.Module.Types.Descr.«map_new/2» tag (fieldsTerm l) = .ok b ∧ MField E b ∧
      ∀ w, denMF E den b w = Bool.true ↔ MSem den tag l w := by
  obtain ⟨k, leaf, key⟩ := leaf_new_keyM g (l.map fun e => .tuple #[e.1, e.2])
  refine ⟨_, by simpa [Elixir.Module.Types.Descr.«map_new/2», fieldsTerm] using leaf, ?_, fun w => denMF_leaf ef sl g w⟩
  by_cases top : tag = .atom "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Bdd.leaf_iff.mpr ⟨⟨k, tag, l, rfl, g, sl⟩, fun ⟨_, e⟩ => leaf_not_top top e, key⟩)


/-- `opt_negation/1` of `term()` or a static type of maps. -/
theorem opt_neg_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) :
    ∃ c, Elixir.Module.Types.Descr.«opt_negation/1» (D m) v = .ok c ∧ E c ∧ ∀ x, den c x ↔ ¬den v x := by
  rcases sv with rfl | ⟨Z, rfl⟩
  · refine ⟨.map [], ?_, ef.none, fun x => ⟨fun h => absurd h (ef.den_none x), fun h => absurd (ef.den_term x) h⟩⟩
    rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]; simp
  · obtain ⟨c, hc, run, sem⟩ := ef.opt_diff [] ef.term hv hm
    refine ⟨c, ?_, hc, fun x => by rw [sem]; simp [ef.den_term x]⟩
    rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]
    simpa [Elixir.Module.Types.Descr.«opt_difference/2», Elixir.Module.Types.Descr.«term/0», unfold_map] using run


theorem lk_mem {s z : Term} : ∀ {A : List Term}, USort.lk (fun x : Term => x) s A = some z →
    z ∈ A ∧ Term.compare (Term.fuel z s) z s = .eq
  | [], h => by simp at h
  | x :: xs, h => by
    rw [USort.lk_cons] at h
    by_cases hx : Term.compare (Term.fuel x s) x s = .eq
    · simp only [hx, ↓reduceIte, Option.some.injEq] at h; subst h; exact ⟨List.mem_cons_self, hx⟩
    · simp only [hx, ↓reduceIte] at h
      obtain ⟨m, e⟩ := lk_mem h
      exact ⟨List.mem_cons_of_mem _ m, e⟩

/-- Strictly sorted lists of atoms with the same first element at every key are equal. -/
theorem sa_eqv_eq : ∀ (A B : List String), USort.SA (fun x : Term => x) (A.map Term.atom) →
    USort.SA (fun x : Term => x) (B.map Term.atom) → USort.Eqv (fun x : Term => x) (A.map Term.atom) (B.map Term.atom) →
    A = B
  | [], [], _, _, _ => rfl
  | [], b :: B, _, _, e => by
    have := e (.atom b); simp [USort.lk_cons] at this
  | a :: A, [], _, _, e => by
    have := e (.atom a); simp [USort.lk_cons] at this
  | a :: A, b :: B, sA, sB, e => by
    simp only [List.map_cons] at sA sB e
    have hA := USort.SA_cons.mp sA
    have hB := USort.SA_cons.mp sB
    have ab : a = b := by
      by_cases c : a = b
      · exact c
      · have ea := e (.atom a)
        have eb := e (.atom b)
        simp only [USort.lk_cons, Lynx.Term.compare_self, ↓reduceIte, atom_cmp_eq, c, Ne.symm c] at ea eb
        obtain ⟨ma, -⟩ := lk_mem ea.symm
        obtain ⟨mb, -⟩ := lk_mem eb
        have l₁ := hB.1 _ ma
        have l₂ := hA.1 _ mb
        rw [USort.c_gt_of_lt l₂] at l₁; cases l₁
    subst ab
    congr 1
    refine sa_eqv_eq A B hA.2 hB.2 fun s => ?_
    have es := e s
    simp only [USort.lk_cons] at es
    by_cases c : Term.compare (Term.fuel (.atom a) s) (.atom a) s = .eq
    · have no : ∀ L : List String, (∀ y ∈ L.map Term.atom, Term.compare (Term.fuel (.atom a) y) (.atom a) y = .lt) →
          USort.lk (fun x : Term => x) s (L.map Term.atom) = none := fun L hL =>
        USort.lk_none fun x mx h => by
          have := USort.c_eq_trans c (USort.c_eq_symm h)
          rw [hL x mx] at this; cases this
      rw [no A hA.1, no B hB.1]
    · simpa [c] using es


/-- `lists:usort/1` of a strictly sorted list of atoms is the list. -/
theorem usort_sorted (A : List String) (sA : USort.SA (fun x : Term => x) (A.map Term.atom)) :
    Erlang.lists.«usort/1» (Term.list (A.map Term.atom)) = .ok (Term.list (A.map Term.atom)) := by
  obtain ⟨R, run, sR, eR⟩ := USort.usort_spec (A.map Term.atom) (fun x mx a b => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp mx
    rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep])
  -- The elements of the result are atoms of the list.
  have atoms : ∀ r ∈ R, ∃ s, r = .atom s := fun r mr => by
    obtain ⟨z, hz⟩ := USort.lk_some (κ := fun x : Term => x) mr (Lynx.Term.compare_self r)
    rw [eR] at hz
    obtain ⟨mz, ez⟩ := lk_mem hz
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp mz
    exact ⟨s, ((Lynx.Term.compare_eq_atom r s).mp (USort.c_eq_symm ez))⟩
  obtain ⟨B, rfl⟩ : ∃ B : List String, R = B.map Term.atom := by
    clear run sR eR
    induction R with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := atoms r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => atoms x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  rw [run, sa_eqv_eq B A sR sA eR]


/-- Dictionaries of atoms that compare equal hold equal-comparing values at each key. -/
theorem fields_cmp_lookup : ∀ (A B : List (Term × Term)), (∀ e ∈ A, ∃ s, e.1 = .atom s) →
    Term.compare (Term.fuel (fieldsTerm A) (fieldsTerm B)) (fieldsTerm A) (fieldsTerm B) = .eq →
    ∀ s t, mapLookup B (.atom s) = some t → ∃ t', mapLookup A (.atom s) = some t' ∧ Term.compare (Term.fuel t' t) t' t = .eq
  | [], B, _, e, s, t, h => by
    cases B with
    | nil => simp [mapLookup] at h
    | cons b B => simp [fieldsTerm, Term.list] at e
  | (k, v) :: A, B, hA, e, s, t, h => by
    obtain ⟨s₀, rfl⟩ := hA _ List.mem_cons_self
    obtain ⟨y, ys, ey, c, cs⟩ := cons_cmp (by simpa [fieldsTerm_cons] using e)
    cases B with
    | nil => simp [fieldsTerm, Term.list] at ey
    | cons b B =>
      simp only [fieldsTerm_cons, Term.cons.injEq] at ey
      obtain ⟨rfl, rfl⟩ := ey
      obtain ⟨ck, cv⟩ := tuple2_cmp c
      obtain ⟨k', v'⟩ := b
      have : k' = .atom s₀ := atom_cmp ck
      subst this
      rw [lookup_cons_atom] at h ⊢
      by_cases e₀ : s₀ = s
      · simp only [e₀, ↓reduceIte, Option.some.injEq] at h ⊢; subst h; exact ⟨v, rfl, cv⟩
      · simp only [e₀, ↓reduceIte] at h ⊢
        exact fields_cmp_lookup A B (fun e me => hA e (List.mem_cons_of_mem _ me)) cs s t h


/-- Every kind of keys with `term()`. -/
def allTerm : Term := fieldsTerm (domainKinds.map fun k => (.atom k, .atom "term"))

theorem kinds_sa : USort.SA (fun x : Term => x) (domainKinds.map Term.atom) := kinds_sorted

/-- The map of `fields_from_keys(@domain_key_types, term())` in `map_update_box/5` and `map_replace_domain/3`. -/
theorem all_term_run (nm : String)
    (hnm : nm = "-map_update_box/5-anonymous-0-" ∨ nm = "-map_replace_domain/3-anonymous-0-") (m : Nat) :
    (do
      let l ← Erlang.lists.«usort/1» (Term.list (domainKinds.map Term.atom))
      Erlang.lists.«map/2» (D (m + 1)) (.function "Elixir.Module.Types.Descr" nm 1 #[]) l) = .ok allTerm := by
  rw [usort_sorted _ kinds_sa]
  rcases hnm with rfl | rfl <;>
    simp [domainKinds, Term.list, allTerm, fieldsTerm, Erlang.lists.«map/2», Erlang.lists.«map_1/2»,
      Erlang.erlang.«is_function/2», Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-anonymous-0-/1».pure,
      Erlang.program.«Elixir.Module.Types.Descr:-map_replace_domain/3-anonymous-0-/1».pure,
      Elixir.Module.Types.Descr.«-map_update_box/5-anonymous-0-/1»,
      Elixir.Module.Types.Descr.«-map_replace_domain/3-anonymous-0-/1»]


theorem lookup_term_map {kind : String} : ∀ {L : List String}, kind ∈ L →
    mapLookup (L.map fun k => (Term.atom k, Term.atom "term")) (.atom kind) = some (.atom "term")
  | [], h => by simp at h
  | k :: t, h => by
    rw [List.map_cons, lookup_cons_atom]
    by_cases e : k = kind
    · simp [e]
    · simp only [e, ↓reduceIte]
      exact lookup_term_map (by simpa [Ne.symm e] using h)

/-- Dictionaries of atom keys in increasing order whose entries satisfy a predicate. -/
def DictV (Q : Term × Term → Prop) (l : List (Term × Term)) : Prop :=
  (∀ e ∈ l, (∃ s : String, e.1 = .atom s) ∧ Q e) ∧ l.Pairwise (fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt)

theorem dictV_tail {Q : Term × Term → Prop} {x : Term × Term} {l : List (Term × Term)} (h : DictV Q (x :: l)) : DictV Q l :=
  ⟨fun e me => h.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp h.2).2⟩

theorem dictV_cons {Q : Term × Term → Prop} {k f : Term} {l : List (Term × Term)} (hk : ∃ s : String, k = .atom s)
    (hq : Q (k, f)) (hl : DictV Q l) (lt : ∀ e ∈ l, Term.compare (Term.fuel k e.1) k e.1 = .lt) : DictV Q ((k, f) :: l) := by
  refine ⟨fun e me => ?_, List.pairwise_cons.mpr ⟨lt, hl.2⟩⟩
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨hk, hq⟩
  · exact hl.1 e me

/-- `orddict:store/3` on a sorted dictionary of atoms. -/
theorem store_dict {Q : Term × Term → Prop} (a : String) {f : Term} (hq : Q (.atom a, f)) :
    ∀ {l : List (Term × Term)}, DictV Q l → ∃ l', Erlang.orddict.«store/3» (.atom a) f (fieldsTerm l) = .ok (fieldsTerm l') ∧
      DictV Q l' ∧ (∀ e ∈ l', e = (.atom a, f) ∨ e ∈ l) ∧
      ∀ s, mapLookup l' (.atom s) = if a = s then some f else mapLookup l (.atom s)
  | [], _ => by
    refine ⟨[(.atom a, f)], ?_, dictV_cons ⟨a, rfl⟩ hq ⟨by simp, by simp⟩ (by simp), by simp, fun s => ?_⟩
    · rw [Erlang.orddict.«store/3».eq_def]; simp [fieldsTerm, Term.list]
    · by_cases e : a = s
      · subst e; simp [lookup_cons_atom]
      · rw [lookup_cons_atom, ite_eq_right e]
  | (k, v) :: t, sl => by
    obtain ⟨b, rfl⟩ := (sl.1 _ List.mem_cons_self).1
    have hv := (sl.1 _ List.mem_cons_self).2
    have st := dictV_tail sl
    have hd : ∀ e ∈ t, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := (List.pairwise_cons.mp sl.2).1
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · refine ⟨(.atom a, f) :: (.atom b, v) :: t, ?_, dictV_cons ⟨a, rfl⟩ hq sl fun e me => ?_,
        fun e me => (List.mem_cons.mp me).imp id id, fun s => ?_⟩
      · rw [Erlang.orddict.«store/3».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
      · rcases List.mem_cons.mp me with rfl | me
        · exact cmp
        · exact cmp_lt_trans cmp (hd e me)
      · by_cases e : a = s
        · subst e; simp [lookup_cons_atom]
        · rw [lookup_cons_atom, ite_eq_right e]
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      refine ⟨(.atom a, f) :: t, ?_, dictV_cons ⟨a, rfl⟩ hq st hd,
        fun e me => (List.mem_cons.mp me).imp id (List.mem_cons_of_mem _), fun s => ?_⟩
      · rw [Erlang.orddict.«store/3».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
      · by_cases e : a = s
        · subst e; simp [lookup_cons_atom]
        · simp [lookup_cons_atom, e]
    · obtain ⟨l', run, sl', mem, look⟩ := store_dict a hq st
      have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
      refine ⟨(.atom b, v) :: l', ?_, dictV_cons ⟨b, rfl⟩ hv sl' fun e me => ?_, fun e me => ?_, fun s => ?_⟩
      · rw [Erlang.orddict.«store/3».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
        simp [run]
      · rcases mem e me with rfl | me
        · exact cmp'
        · exact hd e me
      · rcases List.mem_cons.mp me with rfl | me
        · exact Or.inr List.mem_cons_self
        · exact (mem e me).imp id (List.mem_cons_of_mem _)
      · by_cases e : b = s
        · subst e
          have ne : a ≠ b := fun h => by subst h; simp at cmp
          simp [lookup_cons_atom, ne]
        · simp [lookup_cons_atom, e, look]


/-- `orddict:erase/2` on a sorted dictionary of atoms. -/
theorem erase_dict {Q : Term × Term → Prop} (a : String) :
    ∀ {l : List (Term × Term)}, DictV Q l → ∃ l', Erlang.orddict.«erase/2» (.atom a) (fieldsTerm l) = .ok (fieldsTerm l') ∧
      DictV Q l' ∧ (∀ e ∈ l', e ∈ l) ∧
      ∀ s, mapLookup l' (.atom s) = if a = s then none else mapLookup l (.atom s)
  | [], _ => by
    refine ⟨[], ?_, ⟨by simp, by simp⟩, by simp, fun s => by simp [mapLookup]⟩
    rw [Erlang.orddict.«erase/2».eq_def]; simp [fieldsTerm, Term.list]
  | (k, v) :: t, sl => by
    obtain ⟨b, rfl⟩ := (sl.1 _ List.mem_cons_self).1
    have hv := (sl.1 _ List.mem_cons_self).2
    have st := dictV_tail sl
    have hd : ∀ e ∈ t, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := (List.pairwise_cons.mp sl.2).1
    -- Keys after the head are not the head.
    have notIn : ∀ c, Term.compare (Term.fuel (.atom c) (.atom b)) (.atom c) (.atom b) ≠ .gt → mapLookup t (.atom c) = none := by
      intro c hc
      cases h : mapLookup t (.atom c) with
      | none => rfl
      | some f =>
        exfalso
        obtain ⟨e, me, e₁, -⟩ := lookup_some_mem h
        have lt := hd e me
        rw [e₁] at lt
        exact hc (Lynx.Term.compare_gt_iff_lt.mpr lt)
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · refine ⟨(.atom b, v) :: t, ?_, sl, fun e me => me, fun s => ?_⟩
      · rw [Erlang.orddict.«erase/2».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
      · by_cases e : a = s
        · subst e
          have ne : a ≠ b := fun h => by subst h; simp at cmp
          rw [ite_eq_left rfl, lookup_cons_atom, ite_eq_right (Ne.symm ne), notIn a (by rw [cmp]; simp)]
        · rw [ite_eq_right e]
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      refine ⟨t, ?_, st, fun e me => List.mem_cons_of_mem _ me, fun s => ?_⟩
      · rw [Erlang.orddict.«erase/2».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
      · by_cases e : a = s
        · subst e; simp [notIn a (by simp)]
        · simp [lookup_cons_atom, e]
    · obtain ⟨l', run, sl', mem, look⟩ := erase_dict a st
      refine ⟨(.atom b, v) :: l', ?_, dictV_cons ⟨b, rfl⟩ hv sl' fun e me => hd e (mem e me),
        fun e me => ?_, fun s => ?_⟩
      · rw [Erlang.orddict.«erase/2».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
        simp [run]
      · rcases List.mem_cons.mp me with rfl | me
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem e me)
      · by_cases e : b = s
        · subst e
          have ne : a ≠ b := fun h => by subst h; simp at cmp
          simp [lookup_cons_atom, ne]
        · simp [lookup_cons_atom, e, look]


/-- Entries of domain dictionaries. -/
abbrev DomQ (E : Term → Prop) (e : Term × Term) : Prop := (∃ s, e.1 = .atom s ∧ s ∈ domainKinds) ∧ E e.2

theorem domsV_iff {dl : List (Term × Term)} : DomsV E dl ↔ DictV (DomQ E) dl :=
  ⟨fun h => ⟨fun e me => ⟨by obtain ⟨⟨s, e₁, -⟩, -⟩ := h.1 e me; exact ⟨s, e₁⟩, h.1 e me⟩, h.2⟩,
   fun h => ⟨fun e me => (h.1 e me).2, h.2⟩⟩

/-- Every kind with `term()`, as domains. -/
theorem allTerm_doms (ef : EF nd E V den tl K) : DomsV E (domainKinds.map fun k => (.atom k, .atom "term")) := by
  refine ⟨fun e me => ?_, ?_⟩
  · obtain ⟨k, mk, rfl⟩ := List.mem_map.mp me
    exact ⟨⟨k, rfl, mk⟩, ef.term⟩
  · have := kinds_sorted
    simp only [domainKinds, List.map] at this ⊢
    simpa [List.pairwise_map] using this

/-- `map_replace_domain/3` sets the type a tag gives a kind. -/
theorem replace_domain_any (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {d : String} (hd : d ∈ domainKinds)
    {type : Term} (hty : E type) (m : Nat) :
    ∃ T, Elixir.Module.Types.Descr.«map_replace_domain/3» (D (m + 1)) tag (.atom d) type = .ok T ∧ TagV E T ∧
      ∀ kind ∈ domainKinds, ∀ x, den (tagType T kind) x ↔ if kind = d then den type x else den (tagType tag kind) x := by
  have nn : ∀ x, ¬den (.map []) x := fun x h => ef.den_none x h
  have drop : Term.compare (Term.fuel type (.map [])) type (.map []) = .eq → ∀ x, ¬den type x := fun e x h =>
    nn x (ef.resp ef.none hty (Lynx.Term.compare_eq_symm e) h)
  -- Storing into domains.
  have store : ∀ dl, DomsV E dl → ∃ T, Erlang.orddict.«store/3» (.atom d) type (fieldsTerm dl) = .ok T ∧ TagV E T ∧
      ∀ kind ∈ domainKinds, ∀ x, den (tagType T kind) x ↔
        if kind = d then den type x else den (tagType (fieldsTerm dl) kind) x := fun dl dv => by
    obtain ⟨l', run, sl', -, look⟩ := store_dict (Q := DomQ E) d ⟨⟨d, rfl, hd⟩, hty⟩ (domsV_iff.mp dv)
    refine ⟨_, run, Or.inr (Or.inr ⟨l', rfl, domsV_iff.mpr sl'⟩), fun kind mk x => ?_⟩
    rw [tagType_dom, tagType_dom, look]
    by_cases k : kind = d
    · subst k; simp
    · simp [k, Ne.symm k]
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · by_cases tt : type = .atom "term"
    · subst tt
      refine ⟨.atom "open", ?_, Or.inl rfl, fun kind _ x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]; rfl
      · by_cases k : kind = d <;> simp [k, tagType, ef.den_term x]
    · obtain ⟨T, rT, gT, sT⟩ := store _ (allTerm_doms ef)
      refine ⟨T, ?_, gT, fun kind mk x => (sT kind mk x).trans ?_⟩
      · have hA := all_term_run "-map_replace_domain/3-anonymous-0-" (Or.inr rfl) m
        simp only [allTerm] at hA rT
        rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]
        split
        · rename_i h; exact absurd rfl (by cases h; exact tt)
        · simp only [pure_bind] at hA ⊢
          simp only [domainKinds, List.map] at hA rT
          rw [hA, Lynx.Except.ok_bind, rT]
        all_goals simp_all []
      · by_cases k : kind = d
        · simp [k]
        · simp only [k, ↓reduceIte, tagType_dom, lookup_term_map mk]
          simp [tagType, ef.den_term x]
  · by_cases e : Term.compare (Term.fuel type (.map [])) type (.map []) = .eq
    · refine ⟨.atom "closed", ?_, Or.inr (Or.inl rfl), fun kind _ x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]; simp [eqq_val, e, boolAtom]
      · by_cases k : kind = d <;> simp [k, tagType, nn, drop e]
    · refine ⟨fieldsTerm [(.atom d, type)], ?_, Or.inr (Or.inr ⟨_, rfl, ?_⟩), fun kind mk x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]
        simp [eqq_val, e, boolAtom, Erlang.lists.«usort/1», Erlang.lists.«map/2», Erlang.lists.«map_1/2»,
          Erlang.erlang.«is_function/2», fieldsTerm, Term.list,
          Erlang.program.«Elixir.Module.Types.Descr:-map_replace_domain/3-anonymous-1-/1».pure,
          Elixir.Module.Types.Descr.«-map_replace_domain/3-anonymous-1-/2»]
      · exact ⟨fun e me => by simp at me; subst me; exact ⟨⟨d, rfl, hd⟩, hty⟩, by simp⟩
      · rw [tagType_dom]
        by_cases k : kind = d
        · subst k; simp [lookup_cons_atom]
        · simp [k, mapLookup, tagType, nn]
  · have notAtom : ∀ a : String, fieldsTerm dl ≠ .atom a := fun a h => fieldsTerm_ne_atom dl a h
    by_cases e : Term.compare (Term.fuel type (.map [])) type (.map []) = .eq
    · obtain ⟨l', run, sl', -, look⟩ := erase_dict (Q := DomQ E) d (domsV_iff.mp dv)
      refine ⟨fieldsTerm l', ?_, Or.inr (Or.inr ⟨l', rfl, domsV_iff.mpr sl'⟩), fun kind mk x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]
        cases dl with
        | nil =>
          simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1», eqq_val, e, boolAtom]
          simpa [fieldsTerm, Term.list] using run
        | cons hd' tl =>
          simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1», eqq_val, e, boolAtom]
          simpa [fieldsTerm] using run
      · rw [tagType_dom, tagType_dom, look]
        by_cases k : kind = d
        · subst k; simp [nn, drop e]
        · simp [k, Ne.symm k]
    · obtain ⟨T, rT, gT, sT⟩ := store dl dv
      refine ⟨T, ?_, gT, sT⟩
      rw [Elixir.Module.Types.Descr.«map_replace_domain/3».eq_def]
      cases dl with
      | nil =>
        simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1», eqq_val, e, boolAtom]
        simpa [fieldsTerm, Term.list] using rT
      | cons hd' tl =>
        simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1», eqq_val, e, boolAtom]
        simpa [fieldsTerm] using rT


/-- Absent, or a value outside a type. -/
def OutV (den : Term → V → Prop) (v : Term) (o : Option V) : Prop := o = none ∨ ∃ x, o = some x ∧ ¬den v x

/-- The field `map_update_box_unset/4` gives a named key. -/
def unsetField (ks : List String) (nt : Term) (s : String) : Term :=
  if s ∈ ks then .tuple #[nt, .atom "true"] else .tuple #[.atom "term", .atom "true"]

/-- The fields of `map_update_box_unset/4`: the updated keys may hold values outside the type, other named keys
anything. -/
theorem unset_fields (ef : EF nd E V den tl K) (m : Nat) (ks : List String) {nt : Term} (hnt : E nt) (R : List Term)
    (hR : ∀ r ∈ R, ∃ s, r = .atom s) :
    ∃ l, Erlang.lists.«foldl/3» (D (m + 1)) (.function "Elixir.Module.Types.Descr" "-map_update_box_unset/4-fun-1-" 2
        #[Term.list (ks.map Term.atom), nt]) .nil (Term.list R) = .ok (fieldsTerm l) ∧ FieldsV E l ∧
      ∀ s, (.atom s ∈ R → mapLookup l (.atom s) = some (unsetField ks nt s)) ∧
        (.atom s ∉ R → mapLookup l (.atom s) = none) := by
  obtain ⟨r, ⟨l, rfl, sl, look⟩, run⟩ := foldl_rel_at (m := m + 1) "Elixir.Module.Types.Descr"
    "-map_update_box_unset/4-fun-1-" #[Term.list (ks.map Term.atom), nt]
    (fun pre a => ∃ l, a = fieldsTerm l ∧ FieldsV E l ∧ ∀ s, (.atom s ∈ pre → mapLookup l (.atom s) = some (unsetField ks nt s)) ∧
        (.atom s ∉ pre → mapLookup l (.atom s) = none)) R
    (fun pre x a mx ⟨l, ha, sl, look⟩ => by
      subst ha
      obtain ⟨s, rfl⟩ := hR x mx
      have hf : FieldValue E (unsetField ks nt s) := by
        unfold unsetField; split
        · exact ⟨nt, Bool.true, rfl, hnt⟩
        · exact ⟨_, Bool.true, rfl, ef.term⟩
      obtain ⟨l', rl', sl', -, look'⟩ := store_val s hf sl
      refine ⟨_, ⟨l', rfl, sl', fun s' => ⟨fun m' => ?_, fun m' => ?_⟩⟩, ?_⟩
      · rw [look' s']
        by_cases e : s = s'
        · subst e; simp
        · rw [ite_eq_right e]
          exact (look s').1 (by
            rcases List.mem_append.mp m' with m' | m'
            · exact m'
            · simp at m'; exact absurd m'.symm e)
      · rw [look' s']
        have e : s ≠ s' := fun h => m' (by simp [h])
        rw [ite_eq_right e]
        exact (look s').2 (fun h => m' (List.mem_append_left _ h))
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box_unset/4-fun-1-/2».pure]
        have mem := member_atoms s ks
        by_cases sk : s ∈ ks
        · simp [Elixir.Module.Types.Descr.«-map_update_box_unset/4-fun-1-/4», mem, sk, Term.true]
          simpa [unsetField, sk] using rl'
        · simp [Elixir.Module.Types.Descr.«-map_update_box_unset/4-fun-1-/4», mem, sk, Term.false]
          simpa [unsetField, sk] using rl')
    (fieldsTerm []) ⟨[], rfl, ⟨by simp, by simp⟩, fun s => ⟨by simp, fun _ => by simp [mapLookup]⟩⟩
  exact ⟨l, by simpa [fieldsTerm, Term.list] using run, sl, look⟩


/-- What a tag allows at a kind, from the values its type holds. -/
theorem tagSem_iff (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) (kind : String) (o : Option V) :
    TagSem den tag kind o ↔ o = none ∨ ∃ x, o = some x ∧ den (tagType tag kind) x := by
  cases o with
  | none => simp [tagSem_none]
  | some x => simp [tagSem_some ef g]

/-- The maps of `map_update_box_unset/4` with the domains `Ds`: the updated named keys, the atoms that are not named
when the atom domain is updated, and the keys of the other domains, are absent or hold a value outside the type. -/
def UnsetSemD (den : Term → V → Prop) (ks AK Ds : List String) (v : Term) (w : MW V) : Prop :=
  (∀ s, (s ∈ ks ∨ ("atom" ∈ Ds ∧ s ∉ ks ∧ s ∉ AK)) → OutV den v (w (.atom s))) ∧
    ∀ k i, domKind k ∈ Ds → OutV den v (w (.dom k i))

/-- The tag of `map_update_box_unset/4`: the type at the given domains, anything elsewhere. -/
theorem unset_tag (ef : EF nd E V den tl K) (m : Nat) {nt : Term} (hnt : E nt) (Ds : List String)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∃ T, Erlang.lists.«foldl/3» (D (m + 2))
        (.function "Elixir.Module.Types.Descr" "-map_update_box_unset/4-fun-0-" 2 #[nt]) (.atom "open")
        (Term.list (Ds.map Term.atom)) = .ok T ∧ TagV E T ∧
      ∀ kind ∈ domainKinds, ∀ x, den (tagType T kind) x ↔ (kind ∈ Ds → den nt x) := by
  obtain ⟨T, ⟨gT, sT⟩, run⟩ := foldl_rel_at (m := m + 2) "Elixir.Module.Types.Descr"
    "-map_update_box_unset/4-fun-0-" #[nt]
    (fun pre a => TagV E a ∧ ∀ kind ∈ domainKinds, ∀ x, den (tagType a kind) x ↔ (.atom kind ∈ pre → den nt x))
    (Ds.map Term.atom)
    (fun pre x a mx ⟨g, sa⟩ => by
      obtain ⟨d, md, rfl⟩ := List.mem_map.mp mx
      obtain ⟨T', rT', gT', sT'⟩ := replace_domain_any ef g (hD d md) hnt m
      refine ⟨T', ⟨gT', fun kind mk x => ?_⟩, ?_⟩
      · rw [sT' kind mk x]
        by_cases e : kind = d
        · subst e; simp
        · simp only [e, ↓reduceIte]
          rw [sa kind mk x]
          simp [e]
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box_unset/4-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_update_box_unset/4-fun-0-/3»] using rT')
    (.atom "open") ⟨Or.inl rfl, fun kind _ x => by simp [tagType, ef.den_term x]⟩
  exact ⟨T, run, gT, fun kind mk x => by rw [sT kind mk x]; simp⟩

/-- `map_update_box_unset/4` on the updated keys, the updated domains, and the named atoms. -/
theorem box_unsetD (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) (ks AK Ds : List String)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) {v : Term} (hv : E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) :
    ∃ b, Elixir.Module.Types.Descr.«map_update_box_unset/4» (D (m + 2)) (Term.list (ks.map Term.atom))
        (Term.list (Ds.map Term.atom)) (Term.list (AK.map Term.atom)) v = .ok b ∧ MField E b ∧
      ∀ w, denMF E den b w = Bool.true ↔ UnsetSemD den ks AK Ds v w := by
  obtain ⟨nt, rnt, hnt, snt⟩ := opt_neg_val ef (m := m + 2) (by omega) hv sv
  obtain ⟨T, rT, gT, sT⟩ := unset_tag ef m hnt Ds hD
  obtain ⟨R, rR, -, mR⟩ := usort_atoms (ks.map Term.atom ++ AK.map Term.atom) (fun k mk => by
    rcases List.mem_append.mp mk with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;> exact ⟨s, rfl⟩)
  obtain ⟨l, rl, sl, look⟩ := unset_fields ef (m + 1) ks hnt R (fun r mr => by
    have := (mR r).mp mr
    rcases List.mem_append.mp this with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;> exact ⟨s, rfl⟩)
  obtain ⟨b, rb, fb, sb⟩ := map_new_leaf (den := den) ef gT sl
  refine ⟨b, ?_, fb, fun w => (sb w).trans ?_⟩
  · simp [Elixir.Module.Types.Descr.«map_update_box_unset/4», rnt, rT, append_list, rR, rl, rb]
  · have inR : ∀ s, .atom s ∈ R ↔ s ∈ ks ∨ s ∈ AK := fun s => by
      rw [mR]; simp
    rw [msem_keys]
    constructor
    · intro h
      refine ⟨fun s hs => ?_, fun k i dk => ?_⟩
      · have := h (.atom s)
        simp only [KeyAllow, FSem] at this
        by_cases r : .atom s ∈ R
        · rw [(look s).1 r] at this
          have sk : s ∈ ks := by
            rcases hs with hs | ⟨-, hs, ha⟩
            · exact hs
            · exact absurd ((inR s).mp r) (by simp [hs, ha])
          simp only [unsetField, sk, ↓reduceIte] at this
          rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk] at this
          rcases this with ⟨h, -⟩ | ⟨x, h, hx⟩
          · exact Or.inl h
          · exact Or.inr ⟨x, h, (snt x).mp hx⟩
        · rw [(look s).2 r] at this
          simp only at this
          have ua : "atom" ∈ Ds := by
            rcases hs with hs | ⟨hu, -⟩
            · exact absurd ((inR s).mpr (Or.inl hs)) r
            · exact hu
          rcases (tagSem_iff ef gT "atom" _).mp this with h | ⟨x, h, hx⟩
          · exact Or.inl h
          · exact Or.inr ⟨x, h, (snt x).mp ((sT "atom" (by simp [domainKinds]) x).mp hx ua)⟩
      · have := h (.dom k i)
        simp only [KeyAllow] at this
        rcases (tagSem_iff ef gT _ _).mp this with h | ⟨x, h, hx⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, h, (snt x).mp ((sT _ (domKind_mem k) x).mp hx dk)⟩
    · intro ⟨h, hd⟩ q
      cases q with
      | atom s =>
        simp only [KeyAllow, FSem]
        by_cases r : .atom s ∈ R
        · rw [(look s).1 r]
          simp only
          unfold unsetField
          by_cases sk : s ∈ ks
          · simp only [sk, ↓reduceIte]
            rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]
            rcases h s (Or.inl sk) with h | ⟨x, h, hx⟩
            · exact Or.inl ⟨h, rfl⟩
            · exact Or.inr ⟨x, h, (snt x).mpr hx⟩
          · simp only [sk, ↓reduceIte]
            rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]
            cases w (.atom s) with
            | none => exact Or.inl ⟨rfl, rfl⟩
            | some x => exact Or.inr ⟨x, rfl, ef.den_term x⟩
        · rw [(look s).2 r]
          simp only
          rw [tagSem_iff ef gT]
          cases o : w (.atom s) with
          | none => exact Or.inl rfl
          | some x =>
            refine Or.inr ⟨x, rfl, (sT "atom" (by simp [domainKinds]) x).mpr fun hu => ?_⟩
            have nk : s ∉ ks ∧ s ∉ AK := by
              constructor <;> intro m' <;> exact r ((inR s).mpr (by simp [m']))
            rcases h s (Or.inr ⟨hu, nk⟩) with h | ⟨y, h, hy⟩
            · rw [o] at h; cases h
            · rw [o] at h; cases h; exact (snt x).mpr hy
      | dom k i =>
        simp only [KeyAllow]
        rw [tagSem_iff ef gT]
        cases o : w (.dom k i) with
        | none => exact Or.inl rfl
        | some x =>
          refine Or.inr ⟨x, rfl, (sT _ (domKind_mem k) x).mpr fun dk => ?_⟩
          rcases hd k i dk with h | ⟨y, h, hy⟩
          · rw [o] at h; cases h
          · rw [o] at h; cases h; exact (snt x).mpr hy

/-- The named keys of `map_update_box/5`: the atom keys and those the lines name, sorted. -/
theorem box_named (m : Nat) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) (AK : List String) :
    ∃ (X : List Term) (NK : List String), Erlang.lists.«foldl/3» (D (m + 3))
          (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-3-" 2 #[]) (Term.list (AK.map Term.atom))
          (Term.list lines) = .ok (Term.list X) ∧
        Erlang.lists.«usort/1» (Term.list X) = .ok (Term.list (NK.map Term.atom)) ∧ NK.Nodup ∧ SAK (NK.map Term.atom) ∧
      (∀ s ∈ AK, s ∈ NK) ∧ (∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) ∧
      ∀ s ∈ NK, s ∈ AK ∨ ∃ L ∈ lines, LineNames L s := by
  obtain ⟨X, rX, hacc, hn, hk⟩ := box_names (E := E) m lines hl (AK.map Term.atom)
  have atoms : ∀ k ∈ X, ∃ s, k = .atom s := fun k mk => by
    rcases hk k mk with mk | ⟨L, -, s, rfl, -⟩
    · obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk; exact ⟨s, rfl⟩
    · exact ⟨s, rfl⟩
  obtain ⟨R, rR, sR, mR⟩ := usort_atoms X atoms
  obtain ⟨NK, rfl⟩ : ∃ NK : List String, R = NK.map Term.atom := by
    have aR : ∀ r ∈ R, ∃ s, r = .atom s := fun r mr => atoms r ((mR r).mp mr)
    clear rR sR mR
    induction R with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := aR r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => aR x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  refine ⟨X, NK, rX, rR, ?_, sR, fun s ms => ?_, fun L mL s hs => ?_, fun s ms => ?_⟩
  · have := List.Pairwise.imp (fun h e => cmp_lt_ne h e) sR
    exact (List.pairwise_map.mp this).imp fun h e => h (by rw [e])
  · have := (mR (.atom s)).mpr (hacc _ (List.mem_map_of_mem ms))
    simpa using this
  · have := (mR (.atom s)).mpr (hn L mL s hs)
    simpa using this
  · rcases hk _ ((mR (.atom s)).mp (List.mem_map_of_mem ms)) with h | ⟨L, mL, s', e, hs⟩
    · exact Or.inl (by simpa using h)
    · cases e; exact Or.inr ⟨L, mL, hs⟩


/-- A tag that compares equal to every kind with `term()` allows any value at every kind. -/
theorem allTerm_full (ef : EF nd E V den tl K) {T : Term} (g : TagV E T)
    (e : Term.compare (Term.fuel T allTerm) T allTerm = .eq) : ∀ kind ∈ domainKinds, ∀ x, den (tagType T kind) x := by
  intro kind mk x
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · simp [tagType, ef.den_term x]
  · exfalso
    simp only [allTerm, domainKinds, List.map, fieldsTerm, Term.list] at e
    rw [Lynx.Term.compare_step] at e; simp [Lynx.Term.Compare.compareStep] at e
  · obtain ⟨t', lt', ct⟩ := fields_cmp_lookup dl _ (fun e me => ⟨_, (dv.1 e me).1.choose_spec.1⟩) e kind
      (.atom "term") (lookup_term_map mk)
    rw [tagType_dom, lt']
    obtain ⟨e', me', rfl⟩ := lookup_mem lt'
    exact ef.resp (dv.1 e' me').2 ef.term ct (ef.den_term x)


/-! Keys of literal intersections and of DNF lines. -/


/-- The maps of the box: named keys hold their values over the lines, or the value at updated keys, and other keys
what the tags of the lines allow, with the value at atoms. -/
def BoxSynD (den : Term → V → Prop) (lines : List Term) (ks NK Ds : List String) (v : Term) (w : MW V) : Prop :=
  (∀ s ∈ NK, (∃ L ∈ lines, LongM den L s (w (.atom s))) ∨ (s ∈ ks ∧ ∃ x, w (.atom s) = some x ∧ den v x)) ∧
  (∀ s, s ∉ NK → w (.atom s) = none ∨ ∃ x, w (.atom s) = some x ∧ BoxTagD den lines v Ds "atom" x) ∧
  (∀ k i, w (.dom k i) = none ∨ ∃ x, w (.dom k i) = some x ∧ BoxTagD den lines v Ds (domKind k) x)

/-- `map_update_box/5` putting a non-empty static value at the named keys of a type and the domains `Ds`, with atoms. -/
theorem box_runD (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ []) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (ks AK Ds : List String)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) (hA : "atom" ∈ Ds) (hL : Ds.length ≠ 12) :
    ∃ NK res, Elixir.Module.Types.Descr.«map_update_box/5» (D (n + 4)) (Term.list lines) (Term.list (ks.map Term.atom))
        (Term.list (Ds.map Term.atom)) (forceOp v) (Term.list (AK.map Term.atom)) = .ok res ∧ (∀ s ∈ AK, s ∈ NK) ∧
      (∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) ∧ (∀ s ∈ NK, s ∈ AK ∨ ∃ L ∈ lines, LineNames L s) ∧
      ((res = .map [] ∧ ∀ w, ¬(BoxSynD den lines ks NK Ds v w ∧ ¬UnsetSemD den ks AK Ds v w)) ∨
        ∃ c o, res = .map [(.atom "map", c), (.atom "map", o)] ∧ MField E c ∧
          ∀ w, denMF E den c w = Bool.true ↔ BoxSynD den lines ks NK Ds v w ∧ ¬UnsetSemD den ks AK Ds v w) := by
  have hl' : ∀ L ∈ lines, MLine E L := fun L m => (hl L m).1
  obtain ⟨X, NK, rX, rNK, ndNK, saNK, akNK, lnNK, orNK⟩ := box_named (E := E) (n + 1) lines hl' AK
  obtain ⟨P, Q, rPQ, hP, fP, uQ, cQ, nQ, kQ⟩ := box_fields ef hn lines hl hv ks NK ndNK
  obtain ⟨Q', rQ', subQ', supQ', -⟩ := box_filter ef (m := n + 3) (by omega) Q uQ
  obtain ⟨T, U, rTU, lowT, semT, duU, neU⟩ := box_domainsD ef (n := n + 3) (by omega) lines hl' hv Ds hD
  have sP : FieldsV E P := by
    refine ⟨fun e me => ?_, ?_⟩
    · obtain ⟨s, e₁, fe, -⟩ := fP e me; exact ⟨⟨s, e₁⟩, fe⟩
    · have := saNK; rw [← hP] at this; exact List.pairwise_map.mp this
  -- The field of a named key over the lines.
  have lookP : ∀ s ∈ NK, ∃ f, mapLookup P (.atom s) = some f ∧ FieldValue E f ∧
      ∀ o, FieldSem den f o ↔ ∃ L ∈ lines, LongM den L s o := fun s ms => by
    have : Term.atom s ∈ P.map Prod.fst := by rw [hP]; exact List.mem_map_of_mem ms
    obtain ⟨e, me, e₁⟩ := List.mem_map.mp this
    obtain ⟨s', e₁', fe, se⟩ := fP e me
    rw [e₁] at e₁'; cases e₁'
    exact ⟨e.2, lookup_of_mem sP me e₁, fe, se⟩
  obtain ⟨P2, rP2, sP2, keysP2, lookP2⟩ := box_store ef (m := n + 3) (by omega) sP Q' (fun q mq => by
      obtain ⟨s, -, old, new, rfl, hold, sold, hnew, -⟩ := uQ q (subQ'.subset mq)
      have ms : s ∈ NK := by
        have := kQ _ (subQ'.subset mq); simp only [updKey] at this; simpa using this
      obtain ⟨f, lf, -, sf⟩ := lookP s ms
      exact ⟨s, old, new, rfl, hold, hnew, f, lf, fun o => (sold o).trans (sf o).symm⟩)
    ((subQ'.map updKey).nodup nQ)
  -- The tag, open when every kind holds `term()`.
  have gT := lowTag_tagV lowT
  classical
  let T2 := if Term.compare (Term.fuel T allTerm) T allTerm = .eq then Term.atom "open" else T
  have gT2 : TagV E T2 := by
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq
    · simp only [T2, e, ↓reduceIte]; exact Or.inl rfl
    · simp only [T2, e, ↓reduceIte]; exact gT
  have semT2 : ∀ kind ∈ domainKinds, ∀ x, den (tagType T2 kind) x ↔ BoxTagD den lines v Ds kind x := by
    intro kind mk x
    rw [← semT kind mk x]
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq
    · simp only [T2, e, ↓reduceIte, tagType]
      exact ⟨fun _ => allTerm_full ef gT e kind mk x, fun _ => ef.den_term x⟩
    · simp only [T2, e, ↓reduceIte]
  obtain ⟨bo, rbo, fbo, sbo⟩ := map_new_leaf (den := den) ef gT2 sP2
  obtain ⟨bu, rbu, fbu, sbu⟩ := box_unsetD ef (m := n + 2) (by omega) ks AK Ds hD hv sv
  obtain ⟨r, rr, hr⟩ := map_opt_diff1 (den := den) ef (m := n + 2) (by omega) fbo fbu
  -- The output holds the maps of the box.
  have noneP : ∀ s, s ∉ NK → mapLookup P (.atom s) = none := fun s ns => by
    cases h : mapLookup P (.atom s) with
    | none => rfl
    | some f =>
      obtain ⟨e, me, e₁, -⟩ := lookup_some_mem h
      have : Term.atom s ∈ NK.map Term.atom := by rw [← hP]; exact List.mem_map.mpr ⟨e, me, e₁⟩
      exact absurd (by simpa using this) ns
  -- Each key and line has a value or absence.
  have someOld : ∀ s, ∃ o, ∃ L ∈ lines, LongM den L s o := fun s => by
    obtain ⟨L, mL⟩ := List.exists_mem_of_ne_nil lines hne
    obtain ⟨w, hw⟩ := (hl L mL).2
    exact ⟨_, L, mL, w, hw, rfl⟩
  have semNew : ∀ s ∈ NK, ∀ o, (∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new o) ↔
      s ∈ ks ∧ ∃ x, o = some x ∧ den v x := fun s ms o => by
    constructor
    · rintro ⟨q, mq, old, new, rfl, hq⟩
      obtain ⟨s', ks', old', new', e', -, sold', -, snew'⟩ := uQ _ (subQ'.subset mq)
      obtain ⟨e₁, rfl, rfl⟩ := tuple3_inj e'
      cases Term.atom.inj e₁
      exact ⟨ks', ((snew' o).mp hq).1⟩
    · rintro ⟨sk, x, rfl, hx⟩
      obtain ⟨q, mq, old, new, rfl, hold, sold, hnew, snew⟩ := cQ s ms sk
      obtain ⟨o', L, mL, hL⟩ := someOld s
      have hn : FieldSem den new (some x) := (snew _).mpr ⟨⟨x, rfl, hx⟩, o', (sold o').mpr ⟨L, mL, hL⟩⟩
      exact ⟨_, supQ' _ mq ⟨_, hn⟩, old, new, rfl, hn⟩
  have semBo : ∀ w, MSem den T2 P2 w ↔ BoxSynD den lines ks NK Ds v w := fun w => by
    rw [msem_keys]
    constructor
    · intro h
      refine ⟨fun s ms => ?_, fun s ns => ?_, fun k i => ?_⟩
      · have := h (.atom s)
        simp only [KeyAllow, FSem] at this
        obtain ⟨f, lf, -, sf⟩ := lookP s ms
        cases l2 : mapLookup P2 (.atom s) with
        | none => exact absurd ((keysP2 s).mp l2) (by simp [lf])
        | some f2 =>
          rw [l2] at this
          rcases (lookP2 s _).mp ⟨f2, l2, this⟩ with ⟨f', lf', h'⟩ | h'
          · rw [lf] at lf'; cases lf'; exact Or.inl ((sf _).mp h')
          · exact Or.inr ((semNew s ms _).mp h')
      · have := h (.atom s)
        simp only [KeyAllow, FSem] at this
        rw [(keysP2 s).mpr (noneP s ns)] at this
        rcases (tagSem_iff ef gT2 _ _).mp this with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 "atom" (by simp [domainKinds]) x).mp hx⟩
      · have := h (.dom k i)
        simp only [KeyAllow] at this
        rcases (tagSem_iff ef gT2 _ _).mp this with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 _ (domKind_mem k) x).mp hx⟩
    · rintro ⟨hn, hu, hd⟩ q
      cases q with
      | atom s =>
        simp only [KeyAllow, FSem]
        by_cases ms : s ∈ NK
        · obtain ⟨f, lf, -, sf⟩ := lookP s ms
          have hf : (∃ f', mapLookup P (.atom s) = some f' ∧ FieldSem den f' (w (.atom s))) ∨
              ∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new (w (.atom s)) := by
            rcases hn s ms with h' | h'
            · exact Or.inl ⟨f, lf, (sf _).mpr h'⟩
            · exact Or.inr ((semNew s ms _).mpr h')
          obtain ⟨f2, l2, h2⟩ := (lookP2 s _).mpr hf
          rw [l2]; exact h2
        · rw [(keysP2 s).mpr (noneP s ms)]
          simp only
          rw [tagSem_iff ef gT2]
          rcases hu s ms with h' | ⟨x, h', hx⟩
          · exact Or.inl h'
          · exact Or.inr ⟨x, h', (semT2 "atom" (by simp [domainKinds]) x).mpr hx⟩
      | dom k i =>
        simp only [KeyAllow]
        rw [tagSem_iff ef gT2]
        rcases hd k i with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 _ (domKind_mem k) x).mpr hx⟩
  refine ⟨NK, r, ?_, akNK, lnNK, orNK, ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_update_box/5»
    have rTU' := rTU
    simp only [domainKinds, List.map] at rTU'
    have hU : U ≠ [] := neU.mpr ⟨List.ne_nil_of_mem hA, vne⟩
    have eqU : Erlang.erlang.«==/2» (Term.list U) .nil = .ok (.atom "false") := by
      cases U with
      | nil => exact absurd rfl hU
      | cons u us => simp [Term.list, eqq_val, boolAtom]
    -- Whether some updated key or domain holds a value.
    obtain ⟨b9, a9⟩ : ∃ b9 : Bool, Erlang.lists.«any/2» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-9-" 1 #[]) (Term.list Q') = .ok (boolAtom b9) := by
      classical
      refine ⟨_, any_list _ _ _ _ (fun q => decide (∃ t o, updNew q = .tuple #[t, boolAtom o] ∧ ∃ x, den t x)) Q'
        fun q mq => ?_⟩
      obtain ⟨s, -, old, new, rfl, -, -, ⟨t, o, rfl, ht⟩, -⟩ := uQ q (subQ'.subset mq)
      obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-9-/1».pure]
      simp only [Elixir.Module.Types.Descr.«-map_update_box/5-fun-9-/1», boolAtom] at re ⊢
      cases o <;> cases e <;> simp [re, Erlang.erlang.«not/1», updNew] <;>
        first | (exact Classical.byContradiction fun h => by have := se.mpr (by simpa using h); cases this) |
          (intro x hx; exact se.mp rfl x hx)
    have a10 : Erlang.lists.«any/2» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-10-" 1 #[]) (Term.list U) = .ok (.atom "true") := by
      classical
      have := any_list (D (n + 4)) _ _ _ (fun u => decide (∃ d o nt, u = .tuple #[d, o, nt] ∧ ∃ x, den nt x)) U
        fun u mu => by
          obtain ⟨d, o, nt, rfl, hnt, x, hx⟩ := duU u mu
          obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) hnt
          have : e = Bool.false := by cases e; rfl; exact absurd hx (se.mp rfl x)
          subst this
          rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-10-/1».pure]
          simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-10-/1», re, Erlang.erlang.«not/1», boolAtom]
          exact ⟨x, hx⟩
      rw [this]
      obtain ⟨u, us, rfl⟩ : ∃ u us, U = u :: us := by cases U with | nil => exact absurd rfl hU | cons u us => exact ⟨u, us, rfl⟩
      obtain ⟨d, o, nt, rfl, hnt, x, hx⟩ := duU _ List.mem_cons_self
      have : ((Term.tuple #[d, o, nt] :: us).any
          fun u => decide (∃ d o nt, u = .tuple #[d, o, nt] ∧ ∃ x, den nt x)) = Bool.true := by
        rw [List.any_cons, decide_eq_true ⟨d, o, nt, rfl, x, hx⟩, Bool.true_or]
      rw [this]; rfl
    have rAll : Erlang.lists.«map/2» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/5-anonymous-0-" 1 #[])
        (Term.list (domainKinds.map Term.atom)) = .ok allTerm := by
      have := all_term_run _ (Or.inl rfl) (n + 3)
      rwa [usort_sorted _ kinds_sa, Lynx.Except.ok_bind] at this
    have uK := usort_sorted _ kinds_sa
    simp only [domainKinds, List.map] at rAll uK
    have rT2 : Erlang.erlang.«==/2» T allTerm = .ok (boolAtom (Term.compare (Term.fuel T allTerm) T allTerm == .eq)) :=
      eqq_val T allTerm
    simp [rX, rNK, rPQ, rQ', rTU', eqU, Lynx.Except.andAlso, Erlang.erlang.«element/2», rP2, uK, rAll, rT2]
    have eQ := eqq_val (Term.list Q') .nil
    have lenD : Erlang.erlang.«length/1» (Term.list (Ds.map Term.atom)) = .ok (.integer (Ds.length : Int)) := by
      simpa using length_list (Ds.map Term.atom)
    have cmpD : Term.compare (Term.fuel (Term.integer (Ds.length : Int)) (.integer 12)) (.integer (Ds.length : Int))
        (.integer 12) ≠ .eq := by
      rw [Lynx.Term.compare_integers]
      intro h
      have := Std.LawfulEqCmp.eq_of_compare h
      omega
    have hL' : ¬((Ds.length : Int) = 12) := by omega
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
      simp only [T2, e, ↓reduceIte] at rbo <;>
      cases b9 <;>
      simp [eQ, e, boolAtom, rbo, Erlang.erlang.«/=/2», a9, a10, Lynx.Except.orElse, Erlang.erlang.«=:=/2», rbu, rr]
    all_goals by_cases q : Term.list Q' = .nil <;> simp [q, lenD, hL']
  · rcases hr with ⟨rfl, emp⟩ | ⟨c, rfl, fc, sc⟩
    · refine Or.inl ⟨rfl, fun w ⟨hb, hu⟩ => ?_⟩
      have := emp w
      rw [(sbo w).mpr ((semBo w).mpr hb)] at this
      cases h : denMF E den bu w
      · rw [h] at this; cases this
      · exact hu ((sbu w).mp h)
    · refine Or.inr ⟨c, bo, rfl, fc, fun w => ?_⟩
      rw [sc, Bool.and_eq_true, Bool.not_eq_true', sbo, semBo]
      constructor
      · rintro ⟨hb, hu⟩; exact ⟨hb, fun h => by rw [(sbu w).mpr h] at hu; cases hu⟩
      · rintro ⟨hb, hu⟩
        refine ⟨hb, ?_⟩
        cases h : denMF E den bu w
        · rfl
        · exact absurd ((sbu w).mp h) hu


/-! Keys of literal intersections and of DNF lines. -/

section
variable {Safe : List (Term × Term) → Prop}

/-- `LitInterV`, with the keys of the result among those of the literals. -/
def LitInterK (E : Term → Prop) (den : Term → V → Prop) (r : Except Exception Term) (t₁ t₂ : Term)
    (l₁ l₂ : List (Term × Term)) : Prop :=
  (∃ (tR : Term) (l : List (Term × Term)), r = .ok (.tuple #[tR, fieldsTerm l]) ∧ TagV E tR ∧ FieldsV E l ∧
    (∀ e ∈ l, ∃ e' ∈ l₁ ++ l₂, e.1 = e'.1) ∧ ∀ w, MSem den tR l w ↔ MSem den t₁ l₁ w ∧ MSem den t₂ l₂ w) ∨
  ((∀ w, ¬(MSem den t₁ l₁ w ∧ MSem den t₂ l₂ w)) ∧ r = .error (Exception.throw (.atom "empty")))

theorem InterV.litK {r : Except Exception Term} {t₁ t₂ tR : Term} {l₁ l₂ ks : List (Term × Term)}
    (h : InterV E den r t₁ t₂ tR l₁ l₂ ks) (hks : ∀ e ∈ ks, e ∈ l₁ ++ l₂) (g : TagV E tR)
    (dom : ∀ kind o, TagSem den tR kind o ↔ TagSem den t₁ kind o ∧ TagSem den t₂ kind o) :
    LitInterK E den (r >>= fun f => pure (Term.tuple #[tR, f])) t₁ t₂ l₁ l₂ := by
  rcases h with ⟨l, run, sl, keys, sem⟩ | ⟨⟨s, hs⟩, run⟩
  · refine Or.inl ⟨tR, l, by simp [run], g, sl, fun e me => ?_, fun w => ?_⟩
    · obtain ⟨e', me', ee⟩ := keys e me; exact ⟨e', hks e' me', ee⟩
    exact ⟨fun h => ⟨⟨fun s => ((sem s _).mp (h s)).1, fun k i => ((dom _ _).mp (h.doms k i)).1⟩,
        ⟨fun s => ((sem s _).mp (h s)).2, fun k i => ((dom _ _).mp (h.doms k i)).2⟩⟩,
      fun h => ⟨fun s => (sem s _).mpr ⟨h.1 s, h.2 s⟩, fun k i => (dom _ _).mpr ⟨h.1.doms k i, h.2.doms k i⟩⟩⟩
  · exact Or.inr ⟨fun w h => hs (w (.atom s)) ⟨h.1 s, h.2 s⟩, by simp [run]⟩

theorem LitInterK.swap {r : Except Exception Term} {t₁ t₂ : Term} {l₁ l₂ : List (Term × Term)}
    (h : LitInterK E den r t₂ t₁ l₂ l₁) : LitInterK E den r t₁ t₂ l₁ l₂ := by
  rcases h with ⟨tR, l, run, g, sl, keys, sem⟩ | ⟨disj, run⟩
  · refine Or.inl ⟨tR, l, run, g, sl, fun e me => ?_, fun w => (sem w).trans And.comm⟩
    obtain ⟨e', me', ee⟩ := keys e me
    exact ⟨e', List.mem_append.mpr (List.mem_append.mp me').symm, ee⟩
  · exact Or.inr ⟨fun w h => disj w ⟨h.2, h.1⟩, run⟩

/-- `map_literal_intersection/6` on value maps, with the keys of the result. -/
theorem literal_keys (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf m : Nat}
    (hK : Kf + 1 ≤ m) (hm : K + 1 ≤ m) {ifun : Term} (hI : IFun E den Kf ifun)
    {S : List (Term × Term)} (hS : Safe S) {t₁ t₂ : Term} (g₁ : TagV E t₁) (g₂ : TagV E t₂)
    {l₁ l₂ : List (Term × Term)} (h₁ : FieldsV E l₁) (h₂ : FieldsV E l₂) :
    LitInterK E den (Elixir.Module.Types.Descr.«map_literal_intersection/6» (D m) t₁ (fieldsTerm l₁) t₂
      (fieldsTerm l₂) ifun (.map S)) t₁ t₂ l₁ l₂ := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show 1 ≤ m by omega)
  have hK' : Kf ≤ n + 1 := by omega
  have general : (∀ s₁ s₂, ¬(t₁ = .atom s₁ ∧ t₂ = .atom s₂)) → LitInterK E den
      (Elixir.Module.Types.Descr.«map_literal_intersection/6» (D (n + 1)) t₁ (fieldsTerm l₁) t₂ (fieldsTerm l₂)
        ifun (.map S)) t₁ t₂ l₁ l₂ := by
    intro notAtoms
    obtain ⟨tR, runT, gR, semT⟩ := domain_inter_val ops dops esem (show K ≤ n + 1 by omega) hS g₁ g₂
    have merged := (merge_defaults_val ops dops esem (show Kf ≤ n by omega) (by omega) hI hS g₁ g₂ (semT "atom") _ l₁ l₂
      (Nat.le_refl _) h₁ h₂).litK (fun e me => me) gR semT
    unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»
    split <;> try (exfalso; exact notAtoms _ _ ⟨rfl, rfl⟩)
    simpa [key_tag_field g₁, key_tag_field g₂, runT, mergeFunV₁] using merged
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, -⟩ <;> rcases g₂ with rfl | rfl | ⟨dl₂, rfl, -⟩ <;>
    try exact general (fun _ _ h => fieldsTerm_ne_atom _ _ (by first | exact h.1 | exact h.2))
  all_goals unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»; simp only [pure_bind]
  · exact (merge_val ops dops esem (show Kf ≤ n by omega) (by omega) hI hS _ l₁ l₂ (Nat.le_refl _) h₁ h₂).litK
      (fun e me => me) (TagV.atom (Or.inl rfl)) (tagSem_atom_meet (by simp))
  · exact (open_closed_val ops dops esem hK' (by omega) hI hS _ l₁ l₂ (Nat.le_refl _) h₁ h₂).litK
      (fun e me => List.mem_append_right _ me) (TagV.atom (Or.inr rfl)) (tagSem_atom_meet (by simp))
  · exact LitInterK.swap ((open_closed_val ops dops esem hK' (by omega) hI hS _ l₂ l₁ (Nat.le_refl _) h₂ h₁).litK
      (fun e me => List.mem_append_right _ me) (TagV.atom (Or.inr rfl)) (tagSem_atom_meet (by simp)))
  · exact (closed_val ops dops esem hK' (by omega) hI hS _ l₁ l₂ (Nat.le_refl _) h₁ h₂).litK
      (fun e me => List.mem_append_right _ me) (TagV.atom (Or.inr rfl)) (tagSem_atom_meet (by simp))

/-- `map_line_intersection/3`: empty, or a positive literal whose keys are among those of the two. -/
theorem inter_keys (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 2 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {tag : Term} {l : List (Term × Term)} (gt : TagV E tag) (sl : FieldsV E l)
    {k : Int} {ntag : Term} {nl : List (Term × Term)} (gn : TagV E ntag) (snl : FieldsV E nl) :
    Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) (.tuple #[tag, fieldsTerm l])
        (.tuple #[.integer k, ntag, fieldsTerm nl]) (.map S) = .ok (.atom "empty") ∨
    ∃ tR l', Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) (.tuple #[tag, fieldsTerm l])
        (.tuple #[.integer k, ntag, fieldsTerm nl]) (.map S) = .ok (.tuple #[tR, fieldsTerm l']) ∧
      TagV E tR ∧ FieldsV E l' ∧ ∀ e ∈ l', ∃ e' ∈ l ++ nl, e.1 = e'.1 := by
  rcases literal_keys (den := den) ops dops esem (Kf := K + 1) (show K + 1 + 1 ≤ m by omega) (by omega)
      (bare_ifun ops dops esem) hS gt gn sl snl with ⟨tR, l', run, gR, sl', keys, -⟩ | ⟨-, run⟩
  · right
    refine ⟨tR, l', ?_, gR, sl', keys⟩
    unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
    simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
    simp [run]
  · left
    unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
    simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
    simp [run, Lynx.Exception.classTerm, Lynx.Exception.reason]

/-- Literals whose keys satisfy a predicate. -/
def LitIn (Q : String → Prop) (t : Term) : Prop :=
  ∀ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] → ∀ s ∈ keyStrs l, Q s

theorem keyStrs_mem {l : List (Term × Term)} {s : String} : s ∈ keyStrs l ↔ ∃ e ∈ l, e.1 = .atom s := by
  induction l with
  | nil => simp [keyStrs]
  | cons e t ih =>
    obtain ⟨k, v⟩ := e
    simp only [keyStrs, List.filterMap_cons] at ih ⊢
    cases k <;> simp [ih, eq_comm]

/-- `map_bdd_to_dnf/5` gives lines naming only keys of the path and of the BDD's literals. -/
theorem dnf_names (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 2 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) (Q : String → Prop) {ok : Term → Prop} {r : Term} (wr : Bdd ok r)
    (okT : ∀ t, ok t → MapLitV E t ∧ LitIn Q t) :
    ∀ (acc : List Term) (tag : Term) (l : List (Term × Term)) (negs : List Term), TagV E tag → FieldsV E l →
      (∀ t ∈ negs, MapLitV E t ∧ LitIn Q t) → (∀ s ∈ keyStrs l, Q s) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) (Term.list acc)
          (.tuple #[tag, fieldsTerm l]) (Term.list negs) r (.map S) = .ok (Term.list (lines ++ acc)) ∧
        ∀ L ∈ lines, ∀ s, LineNames L s → Q s := by
  -- A line of a path names keys of the path.
  have line : ∀ tag l negs, (∀ t ∈ negs, MapLitV E t ∧ LitIn Q t) → (∀ s ∈ keyStrs l, Q s) →
      ∀ s, LineNames (.tuple #[tag, fieldsTerm l, Term.list negs]) s → Q s := by
    intro tag l negs hn hl s ⟨tag', l', negs', e, h⟩
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    rw [← fieldsTerm_inj e₂] at h
    rw [← list_inj e₃] at h
    rcases h with h | ⟨N, mN, k, t, l'', rfl, ms⟩
    · exact hl s h
    · exact (hn _ mN).2 k t l'' rfl s ms
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLitV E t ∧ LitIn Q t) →
    ∀ (acc : List Term) (tag : Term) (l : List (Term × Term)) (negs : List Term), TagV E tag → FieldsV E l →
      (∀ t ∈ negs, MapLitV E t ∧ LitIn Q t) → (∀ s ∈ keyStrs l, Q s) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) (Term.list acc)
          (.tuple #[tag, fieldsTerm l]) (Term.list negs) r (.map S) = .ok (Term.list (lines ++ acc)) ∧
        ∀ L ∈ lines, ∀ s, LineNames L s → Q s) ?_ ?_ ?_ ?_ ok r wr okT
  · intro ok _ acc tag l negs _ _ hn hl
    refine ⟨[.tuple #[tag, fieldsTerm l, Term.list negs]], ?_, fun L mL => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp [Term.list]
    · simp at mL; subst mL; exact line tag l negs hn hl
  · intro ok _ acc tag l negs _ _ _ _
    refine ⟨[], ?_, by simp⟩
    rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp
  · intro ok k x y okl okLit acc tag l negs gt sl hn hl
    obtain ⟨⟨k', ntag, nl, e, gn, snl⟩, inl⟩ := okLit _ okl
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    cases e₁; subst e₂; subst e₃
    rcases inter_keys (den := den) ops dops esem hm hS gt sl gn snl with empty | ⟨tR, l', run, -, -, keys⟩
    · refine ⟨[], ?_, by simp⟩
      have empty' : Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) (.tuple #[tag, fieldsTerm l])
          (.tuple ⟨[.integer k, x, fieldsTerm nl]⟩) (.map S) = .ok (.atom "empty") := empty
      rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp [empty']
    · refine ⟨[.tuple #[tR, fieldsTerm l', Term.list negs]], ?_, fun L mL => ?_⟩
      · have run' : Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) (.tuple #[tag, fieldsTerm l])
            (.tuple ⟨[.integer k, x, fieldsTerm nl]⟩) (.map S) = .ok (.tuple #[tR, fieldsTerm l']) := run
        rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp [run', Term.list]
      · simp at mL; subst mL
        refine line tR l' negs hn fun s ms => ?_
        obtain ⟨e, me, es⟩ := keyStrs_mem.mp ms
        obtain ⟨e', me', ee⟩ := keys e me
        rcases List.mem_append.mp me' with me' | me'
        · exact hl s (keyStrs_mem.mpr ⟨e', me', ee ▸ es⟩)
        · exact inl k x nl rfl s (keyStrs_mem.mpr ⟨e', me', ee ▸ es⟩)
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit acc tag l negs gt sl hn hl
    have okLit' : ∀ t, Above ok lit t → MapLitV E t ∧ LitIn Q t := fun t ht => okLit t ht.1
    obtain ⟨Lu, ru, nu⟩ := iu okLit' acc tag l negs gt sl hn hl
    obtain ⟨⟨k', ntag, nl, e, gn, snl⟩, inl⟩ := okLit _ okl
    have hn' : ∀ t ∈ lit :: negs, MapLitV E t ∧ LitIn Q t := fun t mt => by
      rcases List.mem_cons.mp mt with rfl | mt
      · exact okLit _ okl
      · exact hn t mt
    obtain ⟨Lc, runC, nc⟩ : ∃ Lc,
        ((Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) (.tuple #[tag, fieldsTerm l]) lit (.map S) =
            .ok (.atom "empty") ∧ Lc = []) ∨
          ∃ tag2 l2, Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) (.tuple #[tag, fieldsTerm l]) lit (.map S) =
              .ok (.tuple #[tag2, fieldsTerm l2]) ∧
            Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) (Term.list (Lu ++ acc)) (.tuple #[tag2, fieldsTerm l2])
              (Term.list negs) c (.map S) = .ok (Term.list (Lc ++ (Lu ++ acc)))) ∧
          ∀ L ∈ Lc, ∀ s, LineNames L s → Q s := by
      subst e
      rcases inter_keys (den := den) ops dops esem hm hS gt sl gn snl with empty | ⟨tR, l', run, gR, sR, keys⟩
      · exact ⟨[], Or.inl ⟨empty, rfl⟩, by simp⟩
      obtain ⟨Lc, rc, nc⟩ := ic okLit' (Lu ++ acc) tR l' negs gR sR hn fun s ms => by
        obtain ⟨e, me, es⟩ := keyStrs_mem.mp ms
        obtain ⟨e', me', ee⟩ := keys e me
        rcases List.mem_append.mp me' with me' | me'
        · exact hl s (keyStrs_mem.mpr ⟨e', me', ee ▸ es⟩)
        · exact inl k' ntag nl rfl s (keyStrs_mem.mpr ⟨e', me', ee ▸ es⟩)
      exact ⟨Lc, Or.inr ⟨tR, l', run, rc⟩, nc⟩
    obtain ⟨Ld, rd, nd⟩ := idd okLit' (Lc ++ (Lu ++ acc)) tag l (lit :: negs) gt sl hn' hl
    rw [list_cons] at rd
    refine ⟨Ld ++ Lc ++ Lu, ?_, fun L mL => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]
      rcases runC with ⟨e', rfl⟩ | ⟨tag2, l2, e', rc⟩
      · simp only [List.nil_append] at rd
        simp [ru, e', rd]
      · simp [ru, e', rc, rd]
    · simp only [List.mem_append] at mL
      rcases mL with (mL | mL) | mL
      · exact nd L mL
      · exact nc L mL
      · exact nu L mL

/-- `map_bdd_to_dnf_remove_empty/1` gives lines naming only keys of the BDD's literals. -/
theorem dnf_neg_names (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    (jsem : ElemDisjSem E K V den Safe) (hS : Safe []) {m : Nat} (hm : K + 4 ≤ m) {r : Term} (Q : String → Prop)
    (wQ : Bdd (fun t => MLit E t ∧ LitIn Q t) r) :
    ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1» (D m) r = .ok (Term.list lines) ∧
      ∀ L ∈ lines, ∀ s, LineNames L s → Q s := by
  obtain ⟨all, run, tl, -⟩ := dnf_map (den := den) ops dops sem (m := m) (by omega) hS wQ (fun t h => h.1.1) []
    (.tuple #[.atom "open", .nil]) [] ⟨.atom "open", [], rfl, Or.inl rfl, by simp [FieldsV]⟩ (by simp)
  obtain ⟨all', run', names⟩ := dnf_names (den := den) ops dops sem (m := m) (by omega) hS Q wQ
    (fun t h => ⟨h.1.1, h.2⟩) [] (.atom "open") [] [] (Or.inl rfl) (by simp [FieldsV]) (by simp) (by simp [keyStrs])
  have same : all' = all := by
    have := run'.symm.trans (by simpa [fieldsTerm, Term.list] using run)
    simpa using list_inj (Except.ok.inj this)
  subst same
  have keeps : ∀ L ∈ all', ∃ keep : Bool, (∀ m acc, K + 4 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ w, InMLine den L w) :=
    fun L mL => mline_keep ops dops sem jops jsem hS (tl L mL)
  classical
  let keep : Term → Bool := fun L => if h : L ∈ all' then Classical.choose (keeps L h) else Bool.false
  have hk : ∀ L ∈ all', ∀ m acc, K + 4 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep L then .cons L acc else acc) := by
    intro L mL
    simp only [keep, dite_eq_left mL]
    exact (Classical.choose_spec (keeps L mL)).1
  have fold := foldl_det (K := K + 4) "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" #[]
    (fun x a => if keep x then .cons x a else a) all' (fun x mx a m hm => hk x mx m a hm) .nil hm
  have e := foldl_filter keep all' []
  simp only [List.append_nil] at e
  simp only [Term.list] at e
  refine ⟨(all'.filter keep).reverse, ?_, fun L mL => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1»
    have run'' : Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) .nil (.tuple #[.atom "open", .nil]) .nil r (.map []) =
        .ok (Term.list all') := by simpa using run
    simp only [run'', Lynx.Except.ok_bind]
    rw [show (do
        let f ← (pure (Term.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) :
          Except Exception Term)
        Erlang.lists.«foldl/3» (D m) f .nil (Term.list all')) =
        Erlang.lists.«foldl/3» (D m) (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[])
          .nil (Term.list all') from rfl, fold, e]
  · simp only [List.mem_reverse, List.mem_filter] at mL
    exact names L mL.1

end


/-- `map_keys_from_negated_set/2` on a map BDD: atoms outside the negated set, among which are the keys its literals
name outside it, and beyond which the maps of the BDD hold the same values at any two atom keys outside the set. -/
theorem neg_keys_lits (ef : EF nd E V den tl K) (N : List (Term × Term)) (m : Nat) {b : Term} (wb : Bdd (MLit E) b) :
    ∃ R, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (m + 1)) (.map N) b = .ok (Term.list R) ∧
      (∀ r ∈ R, ∃ s, r = .atom s ∧ mapLookup N (.atom s) = none) ∧
      Bdd (fun t => MLit E t ∧ LitIn (fun s => mapLookup N (.atom s) ≠ none ∨ .atom s ∈ R) t) b ∧
      ∀ s c, mapLookup N (.atom s) = none → mapLookup N (.atom c) = none → .atom s ∉ R → .atom c ∉ R →
        ∀ w, denMF E den b (swapW s c w) = denMF E den b w := by
  obtain ⟨R, run, hR, swap⟩ := neg_keys (den := den) ef N m (Or.inr wb)
  obtain ⟨new, run', hn, hk⟩ := neg_reduce (E := E) N m wb []
  have e : R = (mapEntries new).map Prod.fst := by
    have r2 : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (m + 1)) (.map N) b =
        .ok (Term.list ((mapEntries new).map Prod.fst)) := by
      simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», run', Erlang.maps.«keys/1»]
    exact list_inj (Except.ok.inj (run.symm.trans r2))
  refine ⟨R, run, hR, hk.mono fun t ⟨lt, nt⟩ => ⟨lt, fun k tag l et s ms => ?_⟩, swap⟩
  by_cases sN : mapLookup N (.atom s) = none
  · right; rw [e]; exact lookup_entries_atom (nt k tag l et s ms sN)
  · exact Or.inl sN


/-- Keys of the negated literals of a line. -/
def litStrs : Term → List String
  | .tuple ⟨[_, _, f]⟩ => keyStrs (domFields f)
  | _ => []

def negStrs (negs : List Term) : List String := negs.flatMap litStrs

theorem negStrs_mem {negs : List Term} {k : Int} {t : Term} {l : List (Term × Term)}
    (h : .tuple #[.integer k, t, fieldsTerm l] ∈ negs) : ∀ s ∈ keyStrs l, s ∈ negStrs negs := fun s ms =>
  List.mem_flatMap.mpr ⟨_, h, by simpa [litStrs, domFields_fieldsTerm] using ms⟩

/-- A line allows at an atom it does not name, in its fields or negations, whatever its tag allows there. -/
theorem line_at {tag : Term} {l : List (Term × Term)} {negs : List Term} {w₀ : MW V}
    (h₀ : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w₀) (lits : ∀ t ∈ negs, MapLitV E t)
    {s : String} (sl : s ∉ keyStrs l) (sn : s ∉ negStrs negs) {o : Option V} (ho : TagSem den tag "atom" o) :
    ∃ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w ∧ w (.atom s) = o := by
  obtain ⟨hm, hn⟩ := inMLine_iff.mp h₀
  let M := ((keyStrs l ++ negStrs negs ++ [s]).map String.length).foldr max 0
  have fr : ∀ c ∈ freshStrs M (negs.length + 1), c ∉ keyStrs l ++ negStrs negs ++ [s] := fun c mc m => by
    have := le_maxLen _ c m; have := freshStrs_len mc; omega
  obtain ⟨κ, mκ, out⟩ := survive_set (den := den) o negs hn ((freshStrs M (negs.length + 1)).map MKey.atom)
    (List.Pairwise.map MKey.atom (fun _ _ ne e => ne (MKey.atom.inj e)) (freshStrs_nodup M _))
    (by simp [freshStrs_length])
  obtain ⟨c, mc, rfl⟩ := List.mem_map.mp mκ
  have cl : c ∉ keyStrs l := fun m => fr c mc (by simp [m])
  have cn : c ∉ negStrs negs := fun m => fr c mc (by simp [m])
  have cs : c ≠ s := fun e => fr c mc (by simp [e])
  -- The map with the value at the fresh key, then swapped to the key.
  have hm' : MSem den tag l (setW (.atom c) o w₀) := msem_keys.mpr fun κ' => by
    by_cases e : κ' = .atom c
    · subst e
      simp only [KeyAllow, FSem, setW, ↓reduceIte, lookup_fresh' cl]
      exact ho
    · simpa [setW, e] using msem_keys.mp hm κ'
  refine ⟨swapW s c (setW (.atom c) o w₀), inMLine_iff.mpr ⟨?_, fun N mN hN => ?_⟩, by simp [swapW, setW]⟩
  · exact (msem_swapW_iff (lookup_fresh' sl) (lookup_fresh' cl)).mpr hm'
  · obtain ⟨k, t, l', rfl, -, -⟩ := lits N mN
    have s' : s ∉ keyStrs l' := fun m => sn (negStrs_mem mN s m)
    have c' : c ∉ keyStrs l' := fun m => cn (negStrs_mem mN c m)
    rw [nsem_lit, msem_swapW_iff (lookup_fresh' s') (lookup_fresh' c'), ← nsem_lit] at hN
    exact out _ mN hN


theorem domKind_inj {k k' : Fin 11} (h : domKind k = domKind k') : k = k' := by
  revert k k'; decide

/-- Values maps hold at a key, or its absence. -/
def Old (M : MW V → Prop) (κ : MKey) (o : Option V) : Prop := ∃ u, M u ∧ u κ = o

/-- The box of a type, updating the atoms outside `S` and the keys of the kinds `P`: every key holds what some map
holds at a key of its kind (at the same key for atoms), or a value of the type where updated. -/
def BoxD (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (P : String → Prop) (v : Term)
    (w : MW V) : Prop :=
  (∀ s, Old M (.atom s) (w (.atom s)) ∨ (s ∉ S ∧ ∃ x, w (.atom s) = some x ∧ den v x)) ∧
  ∀ k i, w (.dom k i) = none ∨ ∃ x, w (.dom k i) = some x ∧
    ((∃ u j, M u ∧ u (.dom k j) = some x) ∨ (P (domKind k) ∧ den v x))

/-- The maps where no updated key holds a value of the type. -/
def UnsetD (den : Term → V → Prop) (S : List String) (P : String → Prop) (v : Term) (w : MW V) : Prop :=
  (∀ s, s ∉ S → OutV den v (w (.atom s))) ∧ ∀ k i, P (domKind k) → OutV den v (w (.dom k i))

/-- The box without the maps where no updated key holds a value of the type. -/
def BoxP (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (P : String → Prop) (v : Term)
    (w : MW V) : Prop :=
  BoxD den M S P v w ∧ ¬UnsetD den S P v w

/-- The box the lines give is the box of their maps. -/
theorem boxSynD_iff (ef : EF nd E V den tl K) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (hne : lines ≠ []) (v : Term) (S ks AK NK Ds : List String) (hA : "atom" ∈ Ds) (hks : ∀ s ∈ ks, s ∉ S)
    (hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ S) (akNK : ∀ s ∈ AK, s ∈ NK)
    (lnNK : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) (orNK : ∀ s ∈ NK, s ∈ AK ∨ ∃ L ∈ lines, LineNames L s)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ S ∨ s ∈ ks) (w : MW V) :
    BoxSynD den lines ks NK Ds v w ↔ BoxD den (fun u => ∃ L ∈ lines, InMLine den L u) S (· ∈ Ds) v w := by
  let M : MW V → Prop := fun u => ∃ L ∈ lines, InMLine den L u
  -- Named keys hold what the lines hold.
  have named : ∀ s o, (∃ L ∈ lines, LongM den L s o) ↔ Old M (.atom s) o := fun s o =>
    ⟨fun ⟨L, mL, u, hu, e⟩ => ⟨u, ⟨L, mL, hu⟩, e⟩, fun ⟨u, ⟨L, mL, hu⟩, e⟩ => ⟨L, mL, u, hu, e⟩⟩
  -- Atoms no line names hold absence or what the tags of the lines allow at atoms.
  have unnamed : ∀ s, s ∉ NK → ∀ o, Old M (.atom s) o ↔
      o = none ∨ ∃ x, o = some x ∧ ∃ L ∈ lines, LineTag den L "atom" x := by
    intro s ns o
    have notIn : ∀ L ∈ lines, ¬LineNames L s := fun L mL h => ns (lnNK L mL s h)
    constructor
    · rintro ⟨u, ⟨L, mL, hu⟩, rfl⟩
      cases ho : u (.atom s) with
      | none => exact Or.inl rfl
      | some x =>
        refine Or.inr ⟨x, rfl, L, mL, ?_⟩
        obtain ⟨tag, l, negs, rfl, g, -, -⟩ := (hl L mL).1
        have sl : s ∉ keyStrs l := fun m => notIn _ mL ⟨tag, l, negs, rfl, Or.inl m⟩
        have := (inMLine_iff.mp hu).1.atoms s
        simp only [FSem, lookup_fresh' sl, ho] at this
        exact ⟨tag, l, negs, rfl, (tagSem_some ef g "atom" x).mp this⟩
    · intro h
      obtain ⟨L, mL, hx⟩ : ∃ L ∈ lines, (o = none ∨ ∃ x, o = some x ∧ LineTag den L "atom" x) := by
        rcases h with rfl | ⟨x, rfl, L, mL, hL⟩
        · obtain ⟨L, mL⟩ := List.exists_mem_of_ne_nil lines hne
          exact ⟨L, mL, Or.inl rfl⟩
        · exact ⟨L, mL, Or.inr ⟨x, rfl, hL⟩⟩
      obtain ⟨⟨tag, l, negs, rfl, g, -, lits⟩, w₀, h₀⟩ := hl L mL
      have sl : s ∉ keyStrs l := fun m => notIn _ mL ⟨tag, l, negs, rfl, Or.inl m⟩
      have sn : s ∉ negStrs negs := fun m => by
        obtain ⟨N, mN, ms⟩ := List.mem_flatMap.mp m
        obtain ⟨k, t, l', rfl, -, -⟩ := lits N mN
        simp only [litStrs, domFields_fieldsTerm] at ms
        exact notIn _ mL ⟨tag, l, negs, rfl, Or.inr ⟨_, mN, k, t, l', rfl, ms⟩⟩
      have ho : TagSem den tag "atom" o := by
        rcases hx with rfl | ⟨x, rfl, tag', l', negs', e, hx⟩
        · exact tagSem_none tag "atom"
        · obtain ⟨rfl, -, -⟩ := tuple3_inj e
          exact (tagSem_some ef g "atom" x).mpr hx
      obtain ⟨u, hu, e⟩ := line_at h₀ lits sl sn ho
      exact ⟨u, ⟨_, mL, hu⟩, e⟩
  -- Domain keys hold what the tags of the lines allow at their kind.
  have doms : ∀ k x, (∃ L ∈ lines, LineTag den L (domKind k) x) ↔ ∃ u j, M u ∧ u (.dom k j) = some x := by
    intro k x
    constructor
    · rintro ⟨L, mL, hx⟩
      obtain ⟨u, hu, κ, hκ, e⟩ := tag_witness ef (hl L mL).1 (hl L mL).2 (domKind_mem k) hx []
      rcases hκ with ⟨h, -⟩ | ⟨k', j, ek, rfl⟩
      · exact absurd h (domKind_ne_atom k)
      · cases domKind_inj ek
        exact ⟨u, j, ⟨L, mL, hu⟩, e⟩
    · rintro ⟨u, j, ⟨L, mL, hu⟩, e⟩
      obtain ⟨tag, l, negs, rfl, g, -, -⟩ := (hl L mL).1
      have := (inMLine_iff.mp hu).1.doms k j
      rw [e] at this
      exact ⟨_, mL, tag, l, negs, rfl, (tagSem_some ef g _ x).mp this⟩
  constructor
  · rintro ⟨hn, hu, hd⟩
    refine ⟨fun s => ?_, fun k i => ?_⟩
    · by_cases ms : s ∈ NK
      · rcases hn s ms with h | ⟨sk, hx⟩
        · exact Or.inl ((named s _).mp h)
        · exact Or.inr ⟨hks s sk, hx⟩
      · have nS : s ∉ S := fun m => ms (akNK s ((hAK s).mpr (Or.inr m)))
        rcases hu s ms with h | ⟨x, h, (hx | ⟨-, hx⟩)⟩
        · exact Or.inl ((unnamed s ms _).mpr (Or.inl h))
        · exact Or.inl ((unnamed s ms _).mpr (Or.inr ⟨x, h, hx⟩))
        · exact Or.inr ⟨nS, x, h, hx⟩
    · rcases hd k i with h | ⟨x, h, (hx | ⟨dk, hx⟩)⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, h, Or.inl ((doms k x).mp hx)⟩
      · exact Or.inr ⟨x, h, Or.inr ⟨dk, hx⟩⟩
  · rintro ⟨hn, hd⟩
    refine ⟨fun s ms => ?_, fun s ms => ?_, fun k i => ?_⟩
    · rcases hn s with h | ⟨nS, hx⟩
      · exact Or.inl ((named s _).mpr h)
      · refine Or.inr ⟨?_, hx⟩
        rcases orNK s ms with h | ⟨L, mL, hL⟩
        · exact ((hAK s).mp h).resolve_right nS
        · exact (lnKS L mL s hL).resolve_left nS
    · rcases hn s with h | ⟨-, x, h, hx⟩
      · rcases (unnamed s ms _).mp h with h | ⟨x, h, hx⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, h, Or.inl hx⟩
      · exact Or.inr ⟨x, h, Or.inr ⟨hA, hx⟩⟩
    · rcases hd k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, h, Or.inl ((doms k x).mpr hx)⟩
      · exact Or.inr ⟨x, h, Or.inr ⟨dk, hx⟩⟩

theorem unsetSemD_iff (den : Term → V → Prop) (v : Term) (S ks AK Ds : List String) (hA : "atom" ∈ Ds)
    (hks : ∀ s ∈ ks, s ∉ S) (hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ S) (w : MW V) :
    UnsetSemD den ks AK Ds v w ↔ UnsetD den S (· ∈ Ds) v w := by
  constructor
  · rintro ⟨h, hd⟩
    refine ⟨fun s nS => ?_, hd⟩
    by_cases sk : s ∈ ks
    · exact h s (Or.inl sk)
    · exact h s (Or.inr ⟨hA, sk, fun m => ((hAK s).mp m).elim sk nS⟩)
  · rintro ⟨h, hd⟩
    refine ⟨?_, hd⟩
    rintro s (sk | ⟨-, -, sA⟩)
    · exact h s (hks s sk)
    · exact h s fun m => sA ((hAK s).mpr (Or.inr m))

/-- The atoms of a negated set, as strings. -/
def setStrs (N : List (Term × Term)) : List String := keyStrs (mapEntries N)

theorem setStrs_mem {N : List (Term × Term)} {s : String} : s ∈ setStrs N ↔ mapLookup N (.atom s) ≠ none := by
  have h := mapLookup_isSome (mapEntries N) (.atom s)
  rw [mapLookup_mapEntries] at h
  rw [setStrs, keyStrs_mem]
  constructor
  · rintro ⟨e, me, ee⟩ hn
    have := h.mpr ⟨e, me, by rw [ee]; exact compareExact_self _⟩
    rw [hn] at this; simp at this
  · intro hn
    obtain ⟨e, me, ee⟩ := h.mp (Option.isSome_iff_ne_none.mpr hn)
    exact ⟨e, me, (compareExact_eq_atom _ _).mp (compareExact_eq_symm ee)⟩

theorem setStrs_keys {N : List (Term × Term)} (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) :
    (mapEntries N).map Prod.fst = (setStrs N).map Term.atom := by
  unfold setStrs
  generalize mapEntries N = es at hNa ⊢
  induction es with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨s, hs⟩ := hNa e List.mem_cons_self
    obtain ⟨k, v⟩ := e
    simp only at hs; subst hs
    simp [keyStrs, ih fun e me => hNa e (List.mem_cons_of_mem _ me)]

/-- `map_update_named_keys/8` without building, forced, without old values: nothing changes. -/
theorem named_keys_skip (m : Nat) (lines : List Term) (ks : List Term) {v : Term} (T Y er : Term) :
    Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) (.tuple #[T, Y, er, .atom "true"]) (Term.list lines)
      (Term.list ks) (forceOp v) (.atom "false") (.atom "true") (.atom "false") (.atom "false") =
      .ok (.tuple #[T, Y, er, .atom "true"]) := by
  have loop : ∀ ks : List Term, Erlang.lists.«foldl_1/3» (D (m + 1))
      (.function "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
        #[Term.list lines, forceOp v, .atom "false", .atom "true", .atom "false", .atom "false", .atom "true"])
      (.tuple #[T, Y, er, .atom "true"]) (Term.list ks) = .ok (.tuple #[T, Y, er, .atom "true"]) := by
    intro ks
    induction ks with
    | nil => simp [Erlang.lists.«foldl_1/3»]
    | cons k t ih =>
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [] at ih ⊢
      simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
        Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», Elixir.Module.Types.Descr.«map_update_named_key/5»,
        Erlang.erlang.«++/2», ih]
  simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
    Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  cases ks with
  | nil => simp []
  | cons k t => have := loop (k :: t); simp only [Term.list] at this ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at this; simpa using this

/-- `map_update_named_keys/8` putting a constant at several required atoms, building and without old values: the
puts at each, and found when there is a key. -/
theorem union_named (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∀ (A : List String) (Y : List Term) (f : Bool), ∃ bdds : List Term,
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[.map [], Term.list Y, .nil, boolAtom f])
        (Term.list lines) (Term.list (A.map Term.atom)) (forceOp v) (.atom "true") (.atom "true") (.atom "false")
        (.atom "true") = .ok (.tuple #[.map [], Term.list (bdds ++ Y), .nil, boolAtom (f || !A.isEmpty)]) ∧
      (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        ∃ a ∈ A, PutAt den v a w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) := by
  -- The fold over the keys.
  have loop : ∀ (A : List String) (Y : List Term) (f : Bool), ∃ bdds : List Term,
      Erlang.lists.«foldl_1/3» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
          #[Term.list lines, forceOp v, .atom "true", .atom "true", .atom "true", .atom "false", .atom "true"])
        (.tuple #[.map [], Term.list Y, .nil, boolAtom f]) (Term.list (A.map Term.atom)) =
        .ok (.tuple #[.map [], Term.list (bdds ++ Y), .nil, boolAtom (f || !A.isEmpty)]) ∧
      (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        ∃ a ∈ A, PutAt den v a w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) := by
    intro A
    induction A with
    | nil => intro Y f; exact ⟨[], by simp [Erlang.lists.«foldl_1/3», Term.list], by simp, by simp⟩
    | cons a rest ih =>
      intro Y f
      obtain ⟨ba, rba, fba, sba⟩ := put_lines ef hn a (leafPut_put ef a hv) lines hl
      have rba : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
          (forceOp v) (.atom "true") (.atom "false") = .ok (.tuple #[Term.list ba, .atom "nil"]) := by
        simpa [boolAtom] using rba Bool.false .nil (by simp)
      obtain ⟨br, rbr, fbr, sbr⟩ := ih (ba ++ Y) Bool.true
      refine ⟨br ++ ba, ?_, fun b mb => ?_, fun w => ?_⟩
      · rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only [Term.list, List.map] at rbr ⊢
        simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
          Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», rba,
          append_list]
        simpa [boolAtom, Term.list] using rbr
      · rcases List.mem_append.mp mb with mb | mb
        · exact fbr b mb
        · exact fba b mb
      · constructor
        · rintro ⟨b, mb, hb⟩
          rcases List.mem_append.mp mb with mb | mb
          · obtain ⟨a', ma', h⟩ := (sbr w).mp ⟨b, mb, hb⟩
            exact ⟨a', List.mem_cons_of_mem _ ma', h⟩
          · exact ⟨a, List.mem_cons_self, (sba w).mp ⟨b, mb, hb⟩⟩
        · rintro ⟨a', ma', h⟩
          rcases List.mem_cons.mp ma' with rfl | ma'
          · obtain ⟨b, mb, hb⟩ := (sba w).mpr h
            exact ⟨b, List.mem_append_right _ mb, hb⟩
          · obtain ⟨b, mb, hb⟩ := (sbr w).mpr ⟨a', ma', h⟩
            exact ⟨b, List.mem_append_left _ mb, hb⟩
  intro A Y f
  obtain ⟨bdds, run, fb, sb⟩ := loop A Y f
  refine ⟨bdds, ?_, fb, sb⟩
  simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
    Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse]
  cases A with
  | nil =>
    simp [Term.list, Erlang.lists.«foldl_1/3»] at run
    obtain rfl : bdds = [] := by simpa using (list_inj run).symm
    simp [Term.list]
  | cons a t => simp only [Term.list, List.map] at run ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at run; simpa using run

/-! Monotonicity of the semantics of puts at atom keys. -/

/-- The union of the puts at a set of atoms of a set of maps. -/
def UnionS (den : Term → V → Prop) (M : MW V → Prop) (A : String → Prop) (v : Term) (w : MW V) : Prop :=
  ∃ a, A a ∧ PutAt den v a w ∧ ∃ o, M (setK a o w)

theorem union_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {A₁ A₂ : String → Prop} (hA : ∀ a, A₁ a → A₂ a)
    {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x) {w : MW V} (h : UnionS den M₁ A₁ v₁ w) : UnionS den M₂ A₂ v₂ w := by
  obtain ⟨a, ha, ⟨x, wa, hx⟩, o, hu⟩ := h
  exact ⟨a, hA a ha, ⟨x, wa, hv x hx⟩, o, hM _ hu⟩

section
variable {t : Term} {n : Nat}

end


/-- The update of one domain by `map_update_widen/3`: the tag's type there, and the new type. -/
theorem widen_update (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    {tag : Term} (g : TagV E tag) (d : String) :
    ∃ nt, Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3» (D m) (forceOp v) tag (.atom d) =
        .ok (Term.list [.tuple #[.atom d, tagType tag d, nt]]) ∧ E nt ∧ ∀ x, den nt x ↔ den v x := by
  obtain ⟨F, rF, hF, sF⟩ := update_field_force ef hm hv (old := .tuple #[tagType tag d, .atom "true"])
    ⟨_, Bool.true, rfl, tagType_value ef.mopsE g d⟩
  obtain ⟨nt, no, rfl, hnt⟩ := hF
  have hn : FieldSem den (.tuple #[tagType tag d, .atom "true"]) none := by
    rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; simp
  have snt : ∀ x, den nt x ↔ den v x := fun x => by
    have := sF (some x)
    rw [fieldSem_mk] at this
    simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or] at this
    rw [this]
    exact ⟨fun h => h.1, fun h => ⟨h, none, hn⟩⟩
  obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef hm ⟨nt, no, rfl, hnt⟩
  have bf : b = Bool.false := by
    cases b
    · rfl
    · obtain ⟨x, hx⟩ := vne
      exact absurd ((sF (some x)).mpr ⟨⟨x, rfl, hx⟩, none, hn⟩) (sb.mp rfl _)
  subst bf
  refine ⟨nt, ?_, hnt, snt⟩
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · simp only [tagType, ↓reduceIte] at rF ⊢
    simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3», rF]
    rw [rb]; simp [boolAtom, Term.list]
  · have tc : tagType (.atom "closed") d = .map [] := by simp [tagType]
    rw [tc] at rF ⊢
    simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3», rF]
    rw [rb]; simp [boolAtom, Term.list]
  · have fd := find_dom d dv
    have ne := fieldsTerm_ne_atom dl
    have il := is_list_fieldsTerm dl
    have gt : Elixir.Module.Types.Descr.«fields_get/3» (fieldsTerm dl) (.atom d) (.map []) = .ok (tagType (fieldsTerm dl) d) := by
      rw [tagType_dom]
      simp [Elixir.Module.Types.Descr.«fields_get/3», fd]
      cases mapLookup dl (.atom d) <;> rfl
    generalize tagType (fieldsTerm dl) d = TT at gt rF ⊢
    generalize fieldsTerm dl = T at fd ne il gt
    rw [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3».eq_def]
    simp only
    split
    · exact absurd rfl (ne _)
    · exact absurd rfl (ne _)
    · simp [il, gt, rF]
      rw [rb]; simp [boolAtom, Term.list]


/-- A domain update of `map_update_widen/3`: a kind, the tag's type there, and the new type, which holds the values of
the value. -/
def DomUpd (E : Term → Prop) (den : Term → V → Prop) (tag v : Term) (d : String) (u : Term) : Prop :=
  ∃ nt, u = .tuple #[.atom d, tagType tag d, nt] ∧ E nt ∧ ∀ x, den nt x ↔ den v x

/-- The domain updates of a line, by `lists:flatmap/2` over the domains. -/
theorem widen_updates (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    {tag : Term} (g : TagV E tag) :
    ∀ Ds : List String, ∃ U : List Term, Erlang.lists.«flatmap_1/2» (D (m + 1))
        (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[forceOp v, tag])
        (Term.list (Ds.map Term.atom)) = .ok (Term.list U) ∧ U.length = Ds.length ∧
      ∀ p ∈ Ds.zip U, DomUpd E den tag v p.1 p.2
  | [] => ⟨[], by simp [Erlang.lists.«flatmap_1/2», Term.list], rfl, by simp⟩
  | d :: Ds => by
    obtain ⟨nt, rnt, hnt, snt⟩ := widen_update ef hm hv vne g d
    obtain ⟨U, rU, lU, fU⟩ := widen_updates ef hm hv vne g Ds
    refine ⟨.tuple #[.atom d, tagType tag d, nt] :: U, ?_, by simp [lU], fun p mp => ?_⟩
    rotate_left
    · rcases List.mem_cons.mp mp with rfl | mp
      · exact ⟨nt, rfl, hnt, snt⟩
      · exact fU p mp
    rw [Erlang.lists.«flatmap_1/2».eq_def]
    simp only [Term.list, List.map] at rU rnt ⊢
    simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-0-/1».pure, rnt, rU]


/-- The step of `map_widen_domains/3`, with the type of the tag at the kind. -/
theorem widen_dom_eval {tag0 : Term} (g0 : TagV E tag0) (dsp : Dispatcher) (negT old new acc : Term) (d : String) :
    Elixir.Module.Types.Descr.«-map_widen_domains/3-fun-0-/4» dsp tag0 negT (.tuple #[.atom d, old, new]) acc = (do
      let s ← Lynx.Except.andAlso (pure negT) (do
        let x ← Elixir.Module.Types.Descr.«subtype?/2» dsp old (tagType tag0 d)
        Erlang.erlang.«not/1» x) true
      let _ok : Term ← Lynx.Except.guard (Except.ok (s.isMember [Term.atom "false", Term.atom "nil"]))
        (fun _ => (pure (Term.atom "ok") : Except Exception Term))
        (fun _ => Except.error (Lynx.Exception.throw (Term.atom "discard")))
      let u ← Elixir.Module.Types.Descr.«opt_union/2» dsp (tagType tag0 d) new
      Elixir.Module.Types.Descr.«map_replace_domain/3» dsp acc (.atom d) u) := by
  rcases g0 with rfl | rfl | ⟨dl, rfl, dv⟩
  · simp [Elixir.Module.Types.Descr.«-map_widen_domains/3-fun-0-/4», tagType]
  · simp [Elixir.Module.Types.Descr.«-map_widen_domains/3-fun-0-/4», tagType]
  · have fd := find_dom d dv
    have ne := fieldsTerm_ne_atom dl
    have il := is_list_fieldsTerm dl
    have gt : Elixir.Module.Types.Descr.«fields_get/3» (fieldsTerm dl) (.atom d) (.map []) = .ok (tagType (fieldsTerm dl) d) := by
      rw [tagType_dom]
      simp [Elixir.Module.Types.Descr.«fields_get/3», fd]
      cases mapLookup dl (.atom d) <;> rfl
    generalize tagType (fieldsTerm dl) d = TT at gt ⊢
    generalize fieldsTerm dl = T at fd ne il gt
    rw [Elixir.Module.Types.Descr.«-map_widen_domains/3-fun-0-/4».eq_def]
    simp only
    split
    · exact absurd rfl (ne _)
    · exact absurd rfl (ne _)
    · simp [il, gt]

/-- Whether a negation's tag contains the line's old values at a kind. -/
def SubAt (den : Term → V → Prop) (tagL tag0 : Term) (d : String) : Prop :=
  ∀ x, den (tagType tagL d) x → den (tagType tag0 d) x

/-- A step of `map_widen_domains/3`: on negations, `discard` when the tag misses some old values, otherwise the kind
widened by the new type. -/
theorem widen_step (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag0 tagL acc : Term} (g0 : TagV E tag0)
    (gL : TagV E tagL) (gA : TagV E acc) {d : String} (hd : d ∈ domainKinds) {v nt : Term} (hnt : E nt)
    (snt : ∀ x, den nt x ↔ den v x) (neg : Bool) :
    (neg = Bool.true ∧ ¬SubAt den tagL tag0 d ∧
      (D (m + 2)).pure (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg])
        #[.tuple #[.atom d, tagType tagL d, nt], acc] = .error (.throw (.atom "discard"))) ∨
    ((neg = Bool.true → SubAt den tagL tag0 d) ∧ ∃ A, (D (m + 2)).pure
        (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg])
        #[.tuple #[.atom d, tagType tagL d, nt], acc] = .ok A ∧ TagV E A ∧
      ∀ kind ∈ domainKinds, ∀ x, den (tagType A kind) x ↔
        if kind = d then den (tagType tag0 d) x ∨ den v x else den (tagType acc kind) x) := by
  have pureE : ∀ a, (D (m + 2)).pure (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2
      #[tag0, boolAtom neg]) #[.tuple #[.atom d, tagType tagL d, nt], a] =
      Elixir.Module.Types.Descr.«-map_widen_domains/3-fun-0-/4» (D (m + 1)) tag0 (boolAtom neg)
        (Term.tuple #[.atom d, tagType tagL d, nt]) a := fun a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_widen_domains/3-fun-0-/2».pure]
  obtain ⟨sb, rsb, hsb⟩ := ef.sub (tagType_value ef.mopsE gL d) (tagType_value ef.mopsE g0 d)
  have sbI : sb = Bool.true ↔ SubAt den tagL tag0 d := ⟨hsb, fun h => by
    have := ef.subc (tagType_value ef.mopsE gL d) (tagType_value ef.mopsE g0 d) h (m + 1) (by omega)
    rw [rsb (m + 1) (by omega)] at this; cases sb <;> simp_all [boolAtom]⟩
  obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] (tagType_value ef.mopsE g0 d) hnt (m := m + 1) (by omega)
  obtain ⟨A, rA, gA', sA⟩ := replace_domain_any ef gA hd hc m
  by_cases bad : neg = Bool.true ∧ sb = Bool.false
  · obtain ⟨rfl, rfl⟩ := bad
    refine Or.inl ⟨rfl, fun h => absurd (sbI.mpr h) (by simp), ?_⟩
    rw [pureE, widen_dom_eval g0]
    simp [Lynx.Except.andAlso, boolAtom, rsb (m + 1) (by omega), Erlang.erlang.«not/1», Lynx.Term.isMember]
  · refine Or.inr ⟨fun hn => sbI.mp (by cases sb <;> simp_all), A, ?_, gA', fun kind mk x => ?_⟩
    · rw [pureE]
      rw [widen_dom_eval g0]
      cases neg <;> cases sb <;> simp_all [Lynx.Except.andAlso, boolAtom, rsb (m + 1) (by omega), Erlang.erlang.«not/1»,
        Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2»]
    · rw [sA kind mk x]
      by_cases k : kind = d
      · subst k; simp [sc, snt]
      · simp [k]


/-- The fold of `map_widen_domains/3` over the updates of some kinds: `discard` on negations missing old values,
otherwise the tag with the kinds widened by the value. -/
theorem widen_fold (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag0 tagL : Term} (g0 : TagV E tag0)
    (gL : TagV E tagL) {v : Term} (neg : Bool) :
    ∀ (Ds : List String) (U : List Term) (done : List String) (acc : Term), U.length = Ds.length →
      (∀ p ∈ Ds.zip U, DomUpd E den tagL v p.1 p.2) → (∀ d ∈ Ds, d ∈ domainKinds) → TagV E acc →
      (∀ kind ∈ domainKinds, ∀ x, den (tagType acc kind) x ↔
        if kind ∈ done then den (tagType tag0 kind) x ∨ den v x else den (tagType tag0 kind) x) →
      ((neg = Bool.true ∧ ∃ d ∈ Ds, ¬SubAt den tagL tag0 d) ∧ Erlang.lists.«foldl_1/3» (D (m + 2))
          (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) acc
          (Term.list U) = .error (.throw (.atom "discard"))) ∨
      ((neg = Bool.true → ∀ d ∈ Ds, SubAt den tagL tag0 d) ∧ ∃ r, Erlang.lists.«foldl_1/3» (D (m + 2))
          (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) acc
          (Term.list U) = .ok r ∧ TagV E r ∧
        ∀ kind ∈ domainKinds, ∀ x, den (tagType r kind) x ↔
          if kind ∈ done ++ Ds then den (tagType tag0 kind) x ∨ den v x else den (tagType tag0 kind) x)
  | [], U, done, acc, lU, _, _, gA, sA => by
    obtain rfl : U = [] := List.eq_nil_of_length_eq_zero (by simpa using lU)
    exact Or.inr ⟨by simp, acc, by simp [Erlang.lists.«foldl_1/3»], gA, by simpa using sA⟩
  | d :: Ds, [], _, _, lU, _, _, _, _ => by simp at lU
  | d :: Ds, u :: U, done, acc, lU, fU, hD, gA, sA => by
    obtain ⟨nt, eu, hnt, snt⟩ := fU (d, u) (by simp)
    simp only at eu
    subst eu
    have hd := hD d (by simp)
    have fU' : ∀ p ∈ Ds.zip U, DomUpd E den tagL v p.1 p.2 := fun p mp => fU p (by simp [mp])
    have hD' : ∀ d ∈ Ds, d ∈ domainKinds := fun d' md => hD d' (by simp [md])
    rcases widen_step ef hm g0 gL gA hd hnt snt neg with ⟨hn, hs, run⟩ | ⟨hs, A, run, gA', sA'⟩
    · refine Or.inl ⟨⟨hn, d, by simp, hs⟩, ?_⟩
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [] at run ⊢
      simp [run]
    · have sA'' : ∀ kind ∈ domainKinds, ∀ x, den (tagType A kind) x ↔
          if kind ∈ done ++ [d] then den (tagType tag0 kind) x ∨ den v x else den (tagType tag0 kind) x := by
        intro kind mk x
        rw [sA' kind mk x]
        by_cases k : kind = d
        · subst k; simp
        · rw [sA kind mk x]; simp [k]
      rcases widen_fold ef hm g0 gL neg Ds U (done ++ [d]) A (by simpa using lU) fU' hD' gA' sA'' with
        ⟨⟨hn, d', md', hs'⟩, rr⟩ | ⟨hs', r, rr, gr, sr⟩
      · refine Or.inl ⟨⟨hn, d', by simp [md'], hs'⟩, ?_⟩
        rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only [] at run rr ⊢
        simp [run, rr]
      · refine Or.inr ⟨fun hn d' md' => ?_, r, ?_, gr, fun kind mk x => by simpa using sr kind mk x⟩
        · rcases List.mem_cons.mp md' with rfl | md'
          · exact hs hn
          · exact hs' hn d' md'
        · rw [Erlang.lists.«foldl_1/3».eq_def]
          simp only [] at run rr ⊢
          simp [run, rr]


/-- `map_widen_domains/3` on the updates of some kinds. -/
theorem widen_tag (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag0 tagL : Term} (g0 : TagV E tag0)
    (gL : TagV E tagL) {v : Term} (neg : Bool) (Ds : List String) (U : List Term) (lU : U.length = Ds.length)
    (fU : ∀ p ∈ Ds.zip U, DomUpd E den tagL v p.1 p.2) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∃ r, Elixir.Module.Types.Descr.«map_widen_domains/3» (D (m + 2)) tag0 (Term.list U) (boolAtom neg) = .ok r ∧
      ((neg = Bool.true ∧ (∃ d ∈ Ds, ¬SubAt den tagL tag0 d) ∧ r = .atom "discard") ∨
       ((neg = Bool.true → ∀ d ∈ Ds, SubAt den tagL tag0 d) ∧ TagV E r ∧
        ∀ kind ∈ domainKinds, ∀ x, den (tagType r kind) x ↔
          if kind ∈ Ds then den (tagType tag0 kind) x ∨ den v x else den (tagType tag0 kind) x)) := by
  -- `lists:foldl/3` from `lists:foldl_1/3`.
  have toFoldl : ∀ res, Erlang.lists.«foldl_1/3» (D (m + 2))
      (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) tag0 (Term.list U) =
        res → Erlang.lists.«foldl/3» (D (m + 2))
      (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) tag0 (Term.list U) =
        res := fun res run => by
    cases U with
    | nil =>
      have e : res = .ok tag0 := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using run.symm
      subst e
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
    | cons x xs =>
      rw [Erlang.lists.«foldl_1/3».eq_def] at run
      simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using run
  rcases widen_fold ef hm g0 gL neg Ds U [] tag0 lU fU hD g0 (fun kind _ x => by simp) with
    ⟨⟨hn, hs⟩, rr⟩ | ⟨hs, r, rr, gr, sr⟩
  · refine ⟨.atom "discard", ?_, Or.inl ⟨hn, hs, rfl⟩⟩
    simp only [Elixir.Module.Types.Descr.«map_widen_domains/3», pure_bind, toFoldl _ rr]
    simp [Lynx.Except.tryWith, Lynx.Exception.classTerm, Lynx.Exception.reason]
  · refine ⟨r, ?_, Or.inr ⟨hs, gr, fun kind mk x => by simpa using sr kind mk x⟩⟩
    simp only [Elixir.Module.Types.Descr.«map_widen_domains/3», pure_bind, toFoldl _ rr]
    simp []


/-- What a widened tag allows at the keys of a kind: what the tag allows, or, at the updated kinds, a value of the
type. -/
def WTag (den : Term → V → Prop) (tag : Term) (Ds : List String) (v : Term) (kind : String) (o : Option V) : Prop :=
  o = none ∨ ∃ x, o = some x ∧ (den (tagType tag kind) x ∨ (kind ∈ Ds ∧ den v x))

/-- Maps of a literal whose tag is widened at some kinds. -/
def WMSem (den : Term → V → Prop) (tag : Term) (l : List (Term × Term)) (Ds : List String) (v : Term) (w : MW V) : Prop :=
  (∀ s, FSem den tag l s (w (.atom s))) ∧ ∀ k i, WTag den tag Ds v (domKind k) (w (.dom k i))

/-- A tag widened at kinds other than atoms holds the maps of the widened literal. -/
theorem msem_widen (ef : EF nd E V den tl K) {tag r : Term} (g : TagV E tag) (gr : TagV E r) {Ds : List String}
    (hA : "atom" ∉ Ds) {v : Term}
    (sr : ∀ kind ∈ domainKinds, ∀ x, den (tagType r kind) x ↔
      if kind ∈ Ds then den (tagType tag kind) x ∨ den v x else den (tagType tag kind) x)
    (l : List (Term × Term)) (w : MW V) : MSem den r l w ↔ WMSem den tag l Ds v w := by
  have atomT : ∀ o, TagSem den r "atom" o ↔ TagSem den tag "atom" o := fun o => by
    rw [tagSem_iff ef gr, tagSem_iff ef g]
    have := sr "atom" (by simp [domainKinds])
    simp only [hA, ↓reduceIte] at this
    simp [this]
  have domT : ∀ k o, TagSem den r (domKind k) o ↔ WTag den tag Ds v (domKind k) o := fun k o => by
    rw [tagSem_iff ef gr, WTag]
    have := sr (domKind k) (domKind_mem k)
    by_cases dk : domKind k ∈ Ds
    · simp only [dk, ↓reduceIte, true_and] at this ⊢; simp [this]
    · simp only [dk, ↓reduceIte, false_and, or_false] at this ⊢; simp [this]
  constructor
  · intro h
    refine ⟨fun s => ?_, fun k i => (domT k _).mp (h.doms k i)⟩
    have := h.atoms s
    unfold FSem at this ⊢
    split at this
    · exact this
    · exact (atomT _).mp this
  · rintro ⟨ha, hd⟩
    refine ⟨fun s => ?_, fun k i => (domT k _).mpr (hd k i)⟩
    have := ha s
    unfold FSem at this ⊢
    split at this
    · exact this
    · exact (atomT _).mpr this


/-- Negations a line keeps when widening some kinds: those whose tags hold its old values at each. -/
def KeptNeg (den : Term → V → Prop) (tagL : Term) (Ds : List String) (N : Term) : Prop :=
  ∃ (k : Int) (nt : Term) (nl : List (Term × Term)), N = .tuple #[.integer k, nt, fieldsTerm nl] ∧ ∀ d ∈ Ds, SubAt den tagL nt d

/-- The maps a kept negation excludes after widening. -/
def NWide (den : Term → V → Prop) (Ds : List String) (v : Term) (N : Term) (w : MW V) : Prop :=
  ∃ (k : Int) (nt : Term) (nl : List (Term × Term)), N = .tuple #[.integer k, nt, fieldsTerm nl] ∧ WMSem den nt nl Ds v w

/-- The fold of `map_update_widen/3` over the negations of a line: kept negations, widened, are removed. -/
theorem widen_negs (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {tagL : Term} (gL : TagV E tagL) {v : Term}
    (Ds : List String) (hA : "atom" ∉ Ds) (U : List Term) (lU : U.length = Ds.length)
    (fU : ∀ p ∈ Ds.zip U, DomUpd E den tagL v p.1 p.2) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∀ (negs : List Term), (∀ N ∈ negs, MapLitV E N) → ∀ (out : Term), MField E out →
      ∃ out', Erlang.lists.«foldl/3» (D (n + 3))
          (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-1-" 2 #[Term.list U]) out (Term.list negs) =
          .ok out' ∧ MField E out' ∧
        ∀ w, denMF E den out' w = Bool.true ↔ denMF E den out w = Bool.true ∧
          ∀ N ∈ negs, KeptNeg den tagL Ds N → ¬NWide den Ds v N w := by
  intro negs lits out fo
  obtain ⟨r, ⟨o', eo, fo', so'⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr"
    "-map_update_widen/3-fun-1-" #[Term.list U]
    (fun pre a => ∃ o', a = o' ∧ MField E o' ∧ ∀ w, denMF E den o' w = Bool.true ↔ denMF E den out w = Bool.true ∧
      ∀ N ∈ pre, KeptNeg den tagL Ds N → ¬NWide den Ds v N w) negs
    (fun pre N acc mN ⟨o', ea, fo', so'⟩ => by
      subst ea
      obtain ⟨k, nt, nl, rfl, gn, snl⟩ := lits _ mN
      obtain ⟨r, rr, hr⟩ := widen_tag ef (m := n) hn gn gL Bool.true Ds U lU fU hD
      replace rr : Elixir.Module.Types.Descr.«map_widen_domains/3» (D (n + 2)) nt (Term.list U) (.atom "true") = .ok r := rr
      have pureE : (D (n + 3)).pure (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-1-" 2
          #[Term.list U]) #[.tuple #[.integer k, nt, fieldsTerm nl], acc] =
          Elixir.Module.Types.Descr.«-map_update_widen/3-fun-1-/3» (D (n + 2)) (Term.list U)
            (.tuple #[.integer k, nt, fieldsTerm nl]) acc := by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-1-/2».pure]
      rcases hr with ⟨-, ⟨d, md, hs⟩, rfl⟩ | ⟨hs, gr, sr⟩
      · -- Discarded: unchanged.
        refine ⟨acc, ⟨acc, rfl, fo', fun w => ?_⟩, ?_⟩
        · rw [so']
          constructor
          · rintro ⟨h, hn'⟩
            refine ⟨h, fun N mN kN => ?_⟩
            rcases List.mem_append.mp mN with mN | mN
            · exact hn' N mN kN
            · simp at mN; subst mN
              obtain ⟨k', nt', nl', e, ks⟩ := kN
              obtain ⟨-, rfl, -⟩ := tuple3_inj e
              exact absurd (ks d md) hs
          · rintro ⟨h, hn'⟩; exact ⟨h, fun N mN => hn' N (List.mem_append_left _ mN)⟩
        · rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-1-/3», rr]
      · obtain ⟨nb, rnb, fnb, snb⟩ := map_new_leaf (den := den) ef gr snl
        obtain ⟨d', rd, fd, sd, -⟩ := map_diff_lh (den := den) fo' fnb
        refine ⟨d', ⟨d', rfl, fd, fun w => ?_⟩, ?_⟩
        · rw [sd, Bool.and_eq_true, so', Bool.not_eq_true']
          have nw : NWide den Ds v (.tuple #[.integer k, nt, fieldsTerm nl]) w ↔ denMF E den nb w = Bool.true := by
            rw [snb, msem_widen ef gn gr hA sr]
            constructor
            · rintro ⟨k', nt', nl', e, h⟩
              obtain ⟨-, rfl, e₃⟩ := tuple3_inj e
              rw [fieldsTerm_inj e₃]; exact h
            · intro h; exact ⟨k, nt, nl, rfl, h⟩
          constructor
          · rintro ⟨⟨h, hn'⟩, hb⟩
            refine ⟨h, fun N mN kN hN => ?_⟩
            rcases List.mem_append.mp mN with mN | mN
            · exact hn' N mN kN hN
            · simp at mN; subst mN
              rw [nw, hb] at hN; cases hN
          · rintro ⟨h, hn'⟩
            refine ⟨⟨h, fun N mN => hn' N (List.mem_append_left _ mN)⟩, ?_⟩
            cases hb : denMF E den nb w
            · rfl
            · exact absurd ((nw).mpr hb) (hn' _ (by simp) ⟨k, nt, nl, rfl, hs rfl⟩)
        · rw [pureE]
          have ne : r ≠ .atom "discard" := by
            rcases gr with rfl | rfl | ⟨dl, rfl, -⟩
            · simp
            · simp
            · exact fieldsTerm_ne_atom dl "discard"
          simp only [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-1-/3», rr, Lynx.Except.ok_bind]
          simp [rnb, rd])
    out ⟨out, rfl, fo, fun w => by simp⟩
  subst eo
  exact ⟨r, run, fo', so'⟩


/-- Fields with a required key. -/
def HasReq (l : List (Term × Term)) : Prop := ∃ e ∈ l, ∃ t, e.2 = .tuple #[t, .atom "false"]

/-- `map_update_domains_add/3`: maps with a required key are unchanged, others updated. -/
theorem domains_add (m : Nat) (out : Term) {l : List (Term × Term)} (sl : FieldsV E l) (Up Un : List Term) :
    Elixir.Module.Types.Descr.«map_update_domains_add/3» (D (m + 1)) out (fieldsTerm l)
        (.tuple #[Term.list Up, Term.list Un]) = .ok (.tuple #[Term.list Up, Term.list (out :: Un)]) ∧ HasReq l ∨
    Elixir.Module.Types.Descr.«map_update_domains_add/3» (D (m + 1)) out (fieldsTerm l)
        (.tuple #[Term.list Up, Term.list Un]) = .ok (.tuple #[Term.list (out :: Up), Term.list Un]) ∧ ¬HasReq l := by
  classical
  let res : Term → Bool := fun e => decide (∃ k t, e = .tuple #[k, .tuple #[t, .atom "false"]])
  have hany := any_list (D (m + 1)) "Elixir.Module.Types.Descr" "-map_update_domains_add/3-fun-0-" #[] res
    (l.map fun e => .tuple #[e.1, e.2]) (fun x mx => by
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      obtain ⟨-, t, o, he, -⟩ := sl.1 e me
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_domains_add/3-fun-0-/1».pure]
      cases o <;> simp [Elixir.Module.Types.Descr.«-map_update_domains_add/3-fun-0-/1», he, boolAtom, res,
        Erlang.erlang.«not/1»])
  have hreq : (l.map (fun e => Term.tuple #[e.1, e.2])).any res = Bool.true ↔ HasReq l := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨x, mx, hx⟩
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      simp only [res, decide_eq_true_eq] at hx
      obtain ⟨k, t, h⟩ := hx
      simp at h
      exact ⟨e, me, t, h.2⟩
    · rintro ⟨e, me, t, h⟩
      exact ⟨_, List.mem_map_of_mem me, by simp only [res, decide_eq_true_eq]; exact ⟨e.1, t, by rw [h]⟩⟩
  simp only [Elixir.Module.Types.Descr.«map_update_domains_add/3», fieldsTerm, pure_bind] at hany ⊢
  rw [hany]
  by_cases h : HasReq l
  · have : (l.map (fun e => Term.tuple #[e.1, e.2])).any res = Bool.true := hreq.mpr h
    exact Or.inl ⟨by simp [this, boolAtom, Lynx.Term.isMember, Term.list], h⟩
  · have : (l.map (fun e => Term.tuple #[e.1, e.2])).any res = Bool.false := by
      cases hh : (l.map (fun e => Term.tuple #[e.1, e.2])).any res
      · rfl
      · exact absurd (hreq.mp hh) h
    exact Or.inr ⟨by simp [this, boolAtom, Lynx.Term.isMember, Term.list], h⟩


/-- The maps a line gives when widening some kinds by a value. -/
def WLine (den : Term → V → Prop) (L : Term) (Ds : List String) (v : Term) (w : MW V) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    WMSem den tag l Ds v w ∧ ∀ N ∈ negs, KeptNeg den tag Ds N → ¬NWide den Ds v N w

/-- A line of `map_update_widen/3` putting a non-empty static value at some kinds other than atoms. -/
theorem widen_line (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    (Ds : List String) (hA : "atom" ∉ Ds) (hD : ∀ d ∈ Ds, d ∈ domainKinds) (neD : Ds ≠ []) {L : Term}
    (hL : MLine E L) (Up Un : List Term) :
    ∃ out, MField E out ∧ (∀ w, denMF E den out w = Bool.true ↔ WLine den L Ds v w) ∧
      (((D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
          #[Term.list (Ds.map Term.atom), forceOp v]) #[L, .tuple #[Term.list Up, Term.list Un]] =
          .ok (.tuple #[Term.list Up, Term.list (out :: Un)]) ∧
          ∃ tag l negs, L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧ HasReq l) ∨
      ((D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
          #[Term.list (Ds.map Term.atom), forceOp v]) #[L, .tuple #[Term.list Up, Term.list Un]] =
          .ok (.tuple #[Term.list (out :: Up), Term.list Un]))) := by
  obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hL
  obtain ⟨U, rU, lU, fU⟩ := widen_updates ef (m := n + 3) (by omega) hv vne g Ds
  obtain ⟨T, rT, hT⟩ := widen_tag ef (m := n + 2) (by omega) g g Bool.false Ds U lU fU hD
  rcases hT with ⟨h, -⟩ | ⟨-, gT, sT⟩
  · cases h
  replace rT : Elixir.Module.Types.Descr.«map_widen_domains/3» (D (n + 4)) tag (Term.list U) (.atom "false") = .ok T := rT
  obtain ⟨b0, rb0, fb0, sb0⟩ := map_new_leaf (den := den) ef gT sl
  obtain ⟨out, rout, fout, sout⟩ := widen_negs ef (n := n + 1) (by omega) g Ds hA U lU fU hD negs lits b0 fb0
  have semOut : ∀ w, denMF E den out w = Bool.true ↔ WLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds v w := by
    intro w
    rw [sout, sb0, msem_widen ef g gT hA sT]
    constructor
    · rintro ⟨h, hn'⟩; exact ⟨tag, l, negs, rfl, h, hn'⟩
    · rintro ⟨tag', l', negs', e, h, hn'⟩
      obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
      obtain rfl := fieldsTerm_inj e₂
      obtain rfl := list_inj e₃
      exact ⟨h, hn'⟩
  -- Some updated kind gets a value.
  have anyU : Erlang.lists.«any/2» (D (n + 4)) (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-2-" 1 #[])
      (Term.list U) = .ok (.atom "true") := by
    classical
    have := any_list (D (n + 4)) "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-2-" #[]
      (fun u => decide (∃ d o nt, u = .tuple #[d, o, nt] ∧ ∃ x, den nt x)) U fun u mu => by
        obtain ⟨p, mp, e⟩ : ∃ p ∈ Ds.zip U, p.2 = u := by
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mu
          exact ⟨(Ds[i]'(by omega), U[i]), List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩, rfl⟩
        obtain ⟨nt, eu, hnt, snt⟩ := fU p mp
        rw [← e, eu]
        obtain ⟨b, rb, sb⟩ := ef.empty1 (m := n + 3) (by omega) hnt
        obtain ⟨x, hx⟩ := vne
        have : b = Bool.false := by cases b; rfl; exact absurd ((snt x).mpr hx) (sb.mp rfl x)
        subst this
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-2-/1».pure]
        simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-2-/1», rb, Erlang.erlang.«not/1», boolAtom]
        exact ⟨x, (snt x).mpr hx⟩
    rw [this]
    obtain ⟨d, Ds', rfl⟩ : ∃ d Ds', Ds = d :: Ds' := by
      cases Ds with
      | nil => exact absurd rfl neD
      | cons d Ds' => exact ⟨d, Ds', rfl⟩
    cases U with
    | nil => simp at lU
    | cons u U' =>
      obtain ⟨nt, eu, hnt, snt⟩ := fU (d, u) (by simp)
      simp only at eu
      subst eu
      obtain ⟨x, hx⟩ := vne
      have : ((Term.tuple #[.atom d, tagType tag d, nt] :: U').any
          fun u => decide (∃ d o nt, u = .tuple #[d, o, nt] ∧ ∃ x, den nt x)) = Bool.true := by
        rw [List.any_cons, decide_eq_true ⟨_, _, _, rfl, x, (snt x).mpr hx⟩, Bool.true_or]
      rw [this]; rfl
  have neU : Erlang.erlang.«==/2» (Term.list U) .nil = .ok (.atom "false") := by
    cases U with
    | nil =>
      cases Ds with
      | nil => exact absurd rfl neD
      | cons _ _ => simp at lU
    | cons u U' => simp [Term.list, eqq_val, boolAtom]
  have pureE : ∀ a, (D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
      #[Term.list (Ds.map Term.atom), forceOp v]) #[.tuple #[tag, fieldsTerm l, Term.list negs], a] =
      Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4» (D (n + 4)) (Term.list (Ds.map Term.atom)) (forceOp v)
        (.tuple #[tag, fieldsTerm l, Term.list negs]) a := fun a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-3-/2».pure]
  have flat : Erlang.lists.«flatmap/2» (D (n + 4))
      (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[forceOp v, tag])
      (Term.list (Ds.map Term.atom)) = .ok (Term.list U) := by
    simpa [Erlang.lists.«flatmap/2», Erlang.erlang.«is_function/2»] using rU
  rcases domains_add (n + 3) out sl Up Un with ⟨ra, hr⟩ | ⟨ra, hr⟩
  · refine ⟨out, fout, semOut, Or.inl ⟨?_, tag, l, negs, rfl, hr⟩⟩
    rw [pureE]
    simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, neU, rT, rb0, rout, anyU,
      Lynx.Except.andAlso, Lynx.Term.isMember, ra]
  · refine ⟨out, fout, semOut, Or.inr ?_⟩
    rw [pureE]
    simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, neU, rT, rb0, rout, anyU,
      Lynx.Except.andAlso, Lynx.Term.isMember, ra]


/-- Types holding only maps, given by entries whose map field holds the maps of a set. -/
def MapsD (E : Term → Prop) (den : Term → V → Prop) (X : List (Term × Term)) (S : MW V → Prop) : Prop :=
  (∀ q, (mapLookup X q).isSome → q = .atom "map") ∧ (∀ c, mapLookup X (.atom "map") = some c → MField E c) ∧
    ∀ w, (∃ c, mapLookup X (.atom "map") = some c ∧ denMF E den c w = Bool.true) ↔ S w

theorem mapsD_static {X : List (Term × Term)} {S : MW V → Prop} (h : MapsD E den X S) :
    mapLookup X (.atom "dynamic") = none := by
  cases e : mapLookup X (.atom "dynamic") with
  | none => rfl
  | some c =>
    have := h.1 _ (by rw [e]; rfl)
    injection this with h'
    exact absurd h' (by decide)

theorem mapsD_field {r : Term} (fr : MField E r) {S : MW V → Prop}
    (sr : ∀ w, denMF E den r w = Bool.true ↔ S w) : MapsD E den [(.atom "map", r)] S :=
  ⟨fun q hq => by
      by_cases e : q = .atom "map"
      · exact e
      · simp [mapLookup] at hq
        exact absurd hq e,
    fun c hc => by simp [mapLookup] at hc; subst hc; exact fr,
    fun w => by simp [mapLookup, sr]⟩

theorem mapsD_nil {S : MW V → Prop} (h : ∀ w, ¬S w) : MapsD E den [] S :=
  ⟨fun q hq => by simp [mapLookup] at hq, fun c hc => by simp [mapLookup] at hc,
    fun w => by simp [mapLookup, h w]⟩

/-- `opt_union/2` of types holding only maps unites their maps. -/
theorem mapsD_union (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {L R : List (Term × Term)}
    {S₁ S₂ : MW V → Prop} (hL : MapsD E den L S₁) (hR : MapsD E den R S₂) :
    ∃ U, Elixir.Module.Types.Descr.«opt_union/2» (D (m + 1)) (.map L) (.map R) = .ok (.map U) ∧
      MapsD E den U (fun w => S₁ w ∨ S₂ w) := by
  obtain ⟨U, run, look, keysU⟩ := opt_union_lookup m L R (.map []) (mapsD_static hL) (mapsD_static hR)
    fun q x y hx hy => by
      have := hL.1 q (by simp [hx]); subst this
      obtain ⟨u, ru, -, -⟩ := map_field_opt_union (den := den) ef hm (hL.2.1 x hx) (hR.2.1 y hy) []
      exact ⟨u, ru⟩
  refine ⟨U, by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using run, fun q hq => ?_, ?_, fun w => ?_⟩
  · rcases keysU q hq with h | h
    · exact hL.1 q h
    · exact hR.1 q h
  · obtain ⟨l₁, l₂, l₃⟩ := look "map"
    intro c hc
    cases hx : mapLookup L (.atom "map") with
    | none =>
      cases hy : mapLookup R (.atom "map") with
      | none => rw [l₁ hy, hx] at hc; cases hc
      | some y => rw [l₂ y hy hx] at hc; cases hc; exact hR.2.1 _ hy
    | some x =>
      cases hy : mapLookup R (.atom "map") with
      | none => rw [l₁ hy, hx] at hc; cases hc; exact hL.2.1 _ hx
      | some y =>
        obtain ⟨u, ru, fu, -⟩ := map_field_opt_union (den := den) ef hm (hL.2.1 x hx) (hR.2.1 y hy) []
        rw [l₃ x y u hx hy ru] at hc; cases hc; exact fu
  · obtain ⟨l₁, l₂, l₃⟩ := look "map"
    show _ ↔ S₁ w ∨ S₂ w
    rw [← hL.2.2 w, ← hR.2.2 w]
    cases hx : mapLookup L (.atom "map") with
    | none =>
      cases hy : mapLookup R (.atom "map") with
      | none => simp [l₁ hy, hx]
      | some y => simp [l₂ y hy hx]
    | some x =>
      cases hy : mapLookup R (.atom "map") with
      | none => simp [l₁ hy, hx]
      | some y =>
        obtain ⟨u, ru, fu, su⟩ := map_field_opt_union (den := den) ef hm (hL.2.1 x hx) (hR.2.1 y hy) []
        simp [l₃ x y u hx hy ru, su]


/-- The map field of `empty_map()`. -/
abbrev emptyLeaf : Term := .tuple #[.integer (-288230376038284242), .atom "closed", .nil]

theorem emptyLeaf_field : MField E emptyLeaf :=
  mleaf_field (l := []) (Or.inr (Or.inl rfl)) ⟨by simp, by simp⟩ fun k tag l e => by
    obtain ⟨e₁, e₂, -⟩ := tuple3_inj e
    simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨fun _ => by omega, fun h => by simp at h⟩

theorem emptyLeaf_sem (ef : EF nd E V den tl K) (w : MW V) : denMF E den emptyLeaf w = Bool.true ↔ w = wNone := by
  show denMF E den (.tuple #[.integer (-288230376038284242), .atom "closed", fieldsTerm []]) w = Bool.true ↔ _
  rw [denMF_leaf ef ⟨by simp, by simp⟩ (Or.inr (Or.inl rfl))]
  constructor
  · intro h
    funext κ
    cases κ with
    | atom s => have := h.atoms s; simp [FSem, mapLookup, tagSem_closed] at this; exact this
    | dom k i => have := h.doms k i; simp [tagSem_closed] at this; exact this
  · rintro rfl
    exact ⟨fun s => by simp [FSem, mapLookup, wNone, tagSem_closed], fun k i => by simp [wNone, tagSem_closed]⟩

/-- `map_update_domains_result/1`: the updated maps other than the empty map, and the unchanged maps. -/
theorem domains_result (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) (Up Un : List Term)
    (fUp : ∀ b ∈ Up, MField E b) (fUn : ∀ b ∈ Un, MField E b) :
    ∃ R, Elixir.Module.Types.Descr.«map_update_domains_result/1» (D (m + 2)) (.tuple #[Term.list Up, Term.list Un]) =
        .ok (.map R) ∧ MapsD E den R (fun w => ((∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone) ∨
          ∃ b ∈ Un, denMF E den b w = Bool.true) := by
  have mu : ∀ (bs : List Term), (∀ b ∈ bs, MField E b) → ∃ r, Elixir.Module.Types.Descr.«map_union_all/1» (D (m + 2))
      (Term.list bs) = .ok r ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔ ∃ b ∈ bs, denMF E den b w = Bool.true :=
    fun bs fb => by
      obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := m + 2) (by omega) (ok := fun _ => True)
        (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bs (Nat.le_refl _) fun b mb => ⟨fb b mb, by
          rcases fb b mb with ⟨k, rfl⟩ | wb
          · exact Or.inl ⟨k, rfl⟩
          · exact Or.inr (wb.mono fun _ _ => trivial)⟩
      exact ⟨r, rr, fr, sr⟩
  obtain ⟨u, ru, fu, su⟩ := mu Up fUp
  obtain ⟨c, rc, fc, sc⟩ := mu Un fUn
  have semU : ∀ w, (denMF E den u w && !denMF E den emptyLeaf w) = Bool.true ↔
      (∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone := fun w => by
    rw [Bool.and_eq_true, Bool.not_eq_true', su]
    constructor
    · rintro ⟨h, he⟩; exact ⟨h, fun e => by rw [(emptyLeaf_sem ef w).mpr e] at he; cases he⟩
    · rintro ⟨h, he⟩
      refine ⟨h, ?_⟩
      cases h' : denMF E den emptyLeaf w
      · rfl
      · exact absurd ((emptyLeaf_sem ef w).mp h') he
  -- The updated part, as a type of maps.
  have upd : u ≠ .atom "bdd_bot" → ∃ R4, Elixir.Module.Types.Descr.«opt_difference/2» (D (m + 2))
      (.map [(.atom "map", u)]) emptyMapT = .ok (.map R4) ∧
      MapsD E den R4 (fun w => (∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone) := fun bot => by
    obtain ⟨r, rr, hr⟩ := map_opt_diff1 (den := den) ef (m := m) (by omega) fu emptyLeaf_field
    rcases hr with ⟨rfl, emp⟩ | ⟨c', rfl, fc', sc'⟩
    · exact ⟨[], by simpa [emptyMapT] using rr,
        mapsD_nil fun w h => by have := (semU w).mpr h; rw [emp w] at this; cases this⟩
    · refine ⟨[(.atom "map", c'), (.atom "map", u)], by simpa [emptyMapT] using rr, fun q hq => ?_, fun c hc => ?_,
        fun w => ?_⟩
      · by_cases e : q = .atom "map"
        · exact e
        · simp [mapLookup] at hq; exact hq
      · simp [mapLookup] at hc; subst hc; exact fc'
      · simp only [mapLookup, List.find?_cons, compareExact_self, decide_true, Option.map_some, Option.some.injEq,
          exists_eq_left']
        rw [sc', semU]
  have noneU : u = .atom "bdd_bot" → ∀ w, ¬((∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone) := by
    rintro rfl w ⟨⟨b, mb, hb⟩, _⟩
    have := (su w).mpr ⟨b, mb, hb⟩; simp [denMF_bot] at this
  have mUn : MapsD E den [(.atom "map", c)] (fun w => ∃ b ∈ Un, denMF E den b w = Bool.true) := mapsD_field fc sc
  have noneC : c = .atom "bdd_bot" → ∀ w, ¬∃ b ∈ Un, denMF E den b w = Bool.true := by
    rintro rfl w ⟨b, mb, hb⟩
    have := (sc w).mpr ⟨b, mb, hb⟩; simp [denMF_bot] at this
  have rEmpty : Elixir.Module.Types.Descr.«empty_map/0» = .ok emptyMapT := rfl
  by_cases bu : u = .atom "bdd_bot" <;> by_cases bc : c = .atom "bdd_bot"
  · refine ⟨[], ?_, mapsD_nil fun w h => h.elim (noneU bu w) (noneC bc w)⟩
    subst bu bc
    simp [Elixir.Module.Types.Descr.«map_update_domains_result/1», ru, rc]
  · obtain ⟨U, rU, mU⟩ := mapsD_union (den := den) ef (m := m + 1) (by omega) mUn (mapsD_nil (S := fun w =>
      (∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone) (noneU bu))
    refine ⟨U, ?_, mU.1, mU.2.1, fun w => (mU.2.2 w).trans ⟨fun h => h.symm, fun h => h.symm⟩⟩
    subst bu
    simp only [Elixir.Module.Types.Descr.«map_update_domains_result/1», ru, rc, Lynx.Except.ok_bind]
    simpa using rU
  · obtain ⟨R4, r4, m4⟩ := upd bu
    refine ⟨R4, ?_, m4.1, m4.2.1, fun w => (m4.2.2 w).trans ⟨Or.inl, fun h => h.elim id fun h' => absurd h' (noneC bc w)⟩⟩
    subst bc
    simp only [Elixir.Module.Types.Descr.«map_update_domains_result/1», ru, rc, Lynx.Except.ok_bind]
    simp [rEmpty, r4]
  · obtain ⟨R4, r4, m4⟩ := upd bu
    obtain ⟨U, rU, mU⟩ := mapsD_union (den := den) ef (m := m + 1) (by omega) mUn m4
    refine ⟨U, ?_, mU.1, mU.2.1, fun w => (mU.2.2 w).trans ⟨fun h => h.symm, fun h => h.symm⟩⟩
    simp only [Elixir.Module.Types.Descr.«map_update_domains_result/1», ru, rc, Lynx.Except.ok_bind]
    simp [rEmpty, r4]
    simpa using rU


/-- A literal with a required field holds no empty map. -/
theorem wmsem_ne_none {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l) (hr : HasReq l) {Ds : List String}
    {v : Term} {w : MW V} (h : WMSem den tag l Ds v w) : w ≠ wNone := by
  rintro rfl
  obtain ⟨e, me, t, he⟩ := hr
  obtain ⟨⟨s, es⟩, -⟩ := sl.1 e me
  have := h.1 s
  unfold FSem at this
  rw [lookup_of_mem sl me es] at this
  simp only at this
  rw [he, show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk] at this
  simp [wNone] at this

/-- `map_update_widen/3` putting a non-empty static value at several kinds other than atoms. -/
theorem widen_run (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    (Ds : List String) (hA : "atom" ∉ Ds) (hD : ∀ d ∈ Ds, d ∈ domainKinds) (neD : Ds ≠ []) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) :
    ∃ R, Elixir.Module.Types.Descr.«map_update_widen/3» (D (n + 5)) (Term.list lines) (Term.list (Ds.map Term.atom))
        (forceOp v) = .ok (.map R) ∧
      MapsD E den R (fun w => (∃ L ∈ lines, WLine den L Ds v w) ∧ w ≠ wNone) := by
  obtain ⟨r, ⟨Up, Un, rfl, fUp, fUn, sU, nU⟩, run⟩ := foldl_rel_at (m := n + 5) "Elixir.Module.Types.Descr"
    "-map_update_widen/3-fun-3-" #[Term.list (Ds.map Term.atom), forceOp v]
    (fun pre a => ∃ Up Un, a = .tuple #[Term.list Up, Term.list Un] ∧ (∀ b ∈ Up, MField E b) ∧ (∀ b ∈ Un, MField E b) ∧
      (∀ w, ((∃ b ∈ Up, denMF E den b w = Bool.true) ∨ ∃ b ∈ Un, denMF E den b w = Bool.true) ↔
        ∃ L ∈ pre, WLine den L Ds v w) ∧
      ∀ b ∈ Un, ∀ w, denMF E den b w = Bool.true → w ≠ wNone) lines
    (fun pre L a mL ⟨Up, Un, ea, fUp, fUn, sU, nU⟩ => by
      subst ea
      obtain ⟨out, fout, sout, h⟩ := widen_line ef hn hv vne Ds hA hD neD (hl L mL) Up Un
      rcases h with ⟨run, tag, l, negs, rfl, hr⟩ | run
      · obtain ⟨tag', l', negs', e, -, sl, -⟩ := hl _ mL
        obtain ⟨-, e₂, -⟩ := tuple3_inj e
        obtain rfl := fieldsTerm_inj e₂
        refine ⟨_, ⟨Up, out :: Un, rfl, fUp, fun b mb => ?_, fun w => ?_, fun b mb w hb => ?_⟩, run⟩
        · rcases List.mem_cons.mp mb with rfl | mb
          · exact fout
          · exact fUn b mb
        · constructor
          · rintro (⟨b, mb, hb⟩ | ⟨b, mb, hb⟩)
            · obtain ⟨L, mL, hL⟩ := (sU w).mp (Or.inl ⟨b, mb, hb⟩)
              exact ⟨L, List.mem_append_left _ mL, hL⟩
            · rcases List.mem_cons.mp mb with rfl | mb
              · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), (sout w).mp hb⟩
              · obtain ⟨L, mL, hL⟩ := (sU w).mp (Or.inr ⟨b, mb, hb⟩)
                exact ⟨L, List.mem_append_left _ mL, hL⟩
          · rintro ⟨L, mL, hL⟩
            rcases List.mem_append.mp mL with mL | mL
            · rcases (sU w).mpr ⟨L, mL, hL⟩ with h | ⟨b, mb, hb⟩
              · exact Or.inl h
              · exact Or.inr ⟨b, List.mem_cons_of_mem _ mb, hb⟩
            · simp at mL; subst mL
              exact Or.inr ⟨out, List.mem_cons_self, (sout w).mpr hL⟩
        · rcases List.mem_cons.mp mb with rfl | mb
          · obtain ⟨tag', l', negs', e', hw, -⟩ := (sout w).mp hb
            obtain ⟨rfl, e₂, -⟩ := tuple3_inj e'
            obtain rfl := fieldsTerm_inj e₂
            exact wmsem_ne_none sl hr hw
          · exact nU b mb w hb
      · refine ⟨_, ⟨out :: Up, Un, rfl, fun b mb => ?_, fUn, fun w => ?_, nU⟩, run⟩
        · rcases List.mem_cons.mp mb with rfl | mb
          · exact fout
          · exact fUp b mb
        · constructor
          · rintro (⟨b, mb, hb⟩ | ⟨b, mb, hb⟩)
            · rcases List.mem_cons.mp mb with rfl | mb
              · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), (sout w).mp hb⟩
              · obtain ⟨L', mL', hL⟩ := (sU w).mp (Or.inl ⟨b, mb, hb⟩)
                exact ⟨L', List.mem_append_left _ mL', hL⟩
            · obtain ⟨L', mL', hL⟩ := (sU w).mp (Or.inr ⟨b, mb, hb⟩)
              exact ⟨L', List.mem_append_left _ mL', hL⟩
          · rintro ⟨L', mL', hL⟩
            rcases List.mem_append.mp mL' with mL' | mL'
            · rcases (sU w).mpr ⟨L', mL', hL⟩ with ⟨b, mb, hb⟩ | h
              · exact Or.inl ⟨b, List.mem_cons_of_mem _ mb, hb⟩
              · exact Or.inr h
            · simp at mL'; subst mL'
              exact Or.inl ⟨out, List.mem_cons_self, (sout w).mpr hL⟩)
    (.tuple #[.nil, .nil]) ⟨[], [], rfl, by simp, by simp, fun w => by simp, by simp⟩
  obtain ⟨R, rR, mR⟩ := domains_result ef (m := n + 3) (by omega) Up Un fUp fUn
  refine ⟨R, ?_, mR.1, mR.2.1, fun w => (mR.2.2 w).trans ?_⟩
  · simp [Elixir.Module.Types.Descr.«map_update_widen/3», run]
    simpa [Term.list] using rR
  · constructor
    · rintro (⟨h, hn'⟩ | ⟨b, mb, hb⟩)
      · exact ⟨(sU w).mp (Or.inl h), hn'⟩
      · exact ⟨(sU w).mp (Or.inr ⟨b, mb, hb⟩), nU b mb w hb⟩
    · rintro ⟨h, hn'⟩
      rcases (sU w).mpr h with h' | h'
      · exact Or.inl ⟨h', hn'⟩
      · exact Or.inr h' 



/-- The update of one domain by `map_update_widen/3` with an empty value: none. -/
theorem widen_update_empty (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {v : Term} (hv : E v)
    (nv : ¬∃ x, den v x) {tag : Term} (g : TagV E tag) (d : String) :
    Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3» (D m) (forceOp v) tag (.atom d) = .ok .nil := by
  obtain ⟨F, rF, hF, sF⟩ := update_field_force ef hm hv (old := .tuple #[tagType tag d, .atom "true"])
    ⟨_, Bool.true, rfl, tagType_value ef.mopsE g d⟩
  obtain ⟨nt, no, rfl, hnt⟩ := hF
  obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef hm ⟨nt, no, rfl, hnt⟩
  have bt : b = Bool.true := sb.mpr fun o h => nv (by
    obtain ⟨⟨x, -, hx⟩, -⟩ := (sF o).mp h; exact ⟨x, hx⟩)
  subst bt
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · simp only [tagType, ↓reduceIte] at rF ⊢
    simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3», rF]
    rw [rb]; simp [boolAtom]
  · have tc : tagType (.atom "closed") d = .map [] := by simp [tagType]
    rw [tc] at rF
    simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3», rF]
    rw [rb]; simp [boolAtom]
  · have fd := find_dom d dv
    have ne := fieldsTerm_ne_atom dl
    have il := is_list_fieldsTerm dl
    have gt : Elixir.Module.Types.Descr.«fields_get/3» (fieldsTerm dl) (.atom d) (.map []) = .ok (tagType (fieldsTerm dl) d) := by
      rw [tagType_dom]
      simp [Elixir.Module.Types.Descr.«fields_get/3», fd]
      cases mapLookup dl (.atom d) <;> rfl
    generalize tagType (fieldsTerm dl) d = TT at gt rF ⊢
    generalize fieldsTerm dl = T at fd ne il gt
    rw [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3».eq_def]
    simp only
    split
    · exact absurd rfl (ne _)
    · exact absurd rfl (ne _)
    · simp [il, gt, rF]
      rw [rb]; simp [boolAtom]

/-- `map_update_widen/3` with an empty value updates no line. -/
theorem widen_run_empty (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {v : Term} (hv : E v)
    (nv : ¬∃ x, den v x) (Ds : List String) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) :
    ∃ R, Elixir.Module.Types.Descr.«map_update_widen/3» (D (n + 5)) (Term.list lines) (Term.list (Ds.map Term.atom))
        (forceOp v) = .ok (.map R) ∧ MapsD E den R (fun _ => False) := by
  have flat : ∀ tag, TagV E tag → Erlang.lists.«flatmap/2» (D (n + 4))
      (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[forceOp v, tag])
      (Term.list (Ds.map Term.atom)) = .ok .nil := fun tag g => by
    have : ∀ Ds : List String, Erlang.lists.«flatmap_1/2» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[forceOp v, tag])
        (Term.list (Ds.map Term.atom)) = .ok .nil := by
      intro Ds
      induction Ds with
      | nil => simp [Erlang.lists.«flatmap_1/2», Term.list]
      | cons d Ds ih =>
        rw [Erlang.lists.«flatmap_1/2».eq_def]
        simp only [List.map_cons, Term.list] at ih ⊢
        simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-0-/1».pure,
          widen_update_empty ef (m := n + 3) (by omega) hv nv g d, ih]
    simpa [Erlang.lists.«flatmap/2», Erlang.erlang.«is_function/2»] using this Ds
  obtain ⟨r, rfl, run⟩ := foldl_rel_at (m := n + 5) "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-"
    #[Term.list (Ds.map Term.atom), forceOp v] (fun _ a => a = .tuple #[.nil, .nil]) lines
    (fun pre L a mL ha => by
      subst ha
      obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl L mL
      refine ⟨_, rfl, ?_⟩
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-3-/2».pure]
      simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat tag g, Erlang.erlang.«==/2»])
    _ rfl
  obtain ⟨R, rR, mR⟩ := domains_result ef (m := n + 3) (by omega) [] [] (by simp) (by simp)
  refine ⟨R, ?_, mR.1, mR.2.1, fun w => (mR.2.2 w).trans (by simp)⟩
  simp [Elixir.Module.Types.Descr.«map_update_widen/3», run]
  simpa [Term.list] using rR

/-- `w` agrees with `u` off the kinds `Ds`, and at the keys of `F` of those kinds is absent, kept, or holds a value of
`v`. -/
def Agree (den : Term → V → Prop) (Ds : List String) (v : Term) (F : List MKey) (w u : MW V) : Prop :=
  (∀ s, w (.atom s) = u (.atom s)) ∧ (∀ k i, domKind k ∉ Ds → w (.dom k i) = u (.dom k i)) ∧
    ∀ k i, .dom k i ∈ F → domKind k ∈ Ds →
      (w (.dom k i) = none ∨ w (.dom k i) = u (.dom k i) ∨ ∃ x, w (.dom k i) = some x ∧ den v x)

theorem Agree.mono {Ds : List String} {v : Term} {F G : List MKey} {w u : MW V} (h : Agree den Ds v G w u)
    (sub : ∀ κ ∈ F, κ ∈ G) : Agree den Ds v F w u :=
  ⟨h.1, h.2.1, fun k i m dk => h.2.2 k i (sub _ m) dk⟩

/-- The maps of a forced put at some kinds other than atoms, from the maps of a type: on every finite set of keys,
some map of the type agrees as `Agree` requires. -/
def DomC (den : Term → V → Prop) (M : MW V → Prop) (Ds : List String) (v : Term) (w : MW V) : Prop :=
  w ≠ wNone ∧ ∀ F : List MKey, ∃ u, M u ∧ Agree den Ds v F w u

/-- The index of a domain key. -/
def domIdx : MKey → Option Nat
  | .dom _ i => some i
  | _ => none

/-- Indices above those of the domain keys of a list. -/
def freshIdx (F : List MKey) : Nat := (F.filterMap domIdx).foldr max 0 + 1

theorem freshIdx_not_mem {F : List MKey} {k : Fin 11} {i : Nat} (h : freshIdx F ≤ i) : MKey.dom k i ∉ F := by
  intro m
  have mi : i ∈ F.filterMap domIdx := List.mem_filterMap.mpr ⟨_, m, rfl⟩
  have le : i ≤ (F.filterMap domIdx).foldr max 0 := (foldr_max_le.mp (Nat.le_refl _)) i mi
  unfold freshIdx at h
  omega


/-- A line producing a map holds, for any finite set of keys, a map agreeing with it as `DomC` requires. -/
theorem wline_witness (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) {Ds : List String} (hA : "atom" ∉ Ds)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) {v : Term} {w : MW V} (hw : WLine den L Ds v w) (F : List MKey) :
    ∃ u, InMLine den L u ∧ (∀ s, w (.atom s) = u (.atom s)) ∧ (∀ k i, domKind k ∉ Ds → w (.dom k i) = u (.dom k i)) ∧
      ∀ k i, .dom k i ∈ F → domKind k ∈ Ds →
        (w (.dom k i) = none ∨ w (.dom k i) = u (.dom k i) ∨ ∃ x, w (.dom k i) = some x ∧ den v x) := by
  classical
  obtain ⟨tag, l, negs, rfl, hwm, hkn⟩ := hw
  obtain ⟨tag', l', negs', e, g, sl, lits⟩ := hL
  obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
  obtain rfl := fieldsTerm_inj e₂
  obtain rfl := list_inj e₃
  -- What escapes a dropped negation.
  let Esc : Term → Fin 11 × V → Prop := fun N p => domKind p.1 ∈ Ds ∧ den (tagType tag (domKind p.1)) p.2 ∧
    ∀ (kN : Int) (nt : Term) (nl : List (Term × Term)), N = .tuple #[.integer kN, nt, fieldsTerm nl] →
      ¬den (tagType nt (domKind p.1)) p.2
  let pick : Term → Option (Fin 11 × V) := fun N => if h : ∃ p, Esc N p then some h.choose else none
  have exDrop : ∀ N ∈ negs, ¬KeptNeg den tag Ds N → ∃ p, Esc N p := by
    intro N mN nk
    obtain ⟨kN, nt, nl, rfl, -, -⟩ := lits N mN
    have : ¬∀ d ∈ Ds, SubAt den tag nt d := fun h => nk ⟨kN, nt, nl, rfl, h⟩
    obtain ⟨d, hd⟩ := Classical.not_forall.mp this
    obtain ⟨md, hd⟩ := Classical.not_imp.mp hd
    obtain ⟨y, hy⟩ := Classical.not_forall.mp hd
    obtain ⟨hy₁, hy₂⟩ := Classical.not_imp.mp hy
    have dA : d ≠ "atom" := fun h => hA (h ▸ md)
    obtain ⟨k, rfl⟩ := domKind_of (hD _ md) dA
    refine ⟨(k, y), md, hy₁, fun kN' nt' nl' e' => ?_⟩
    obtain ⟨-, rfl, -⟩ := tuple3_inj e'
    exact hy₂
  let J := freshIdx F
  let isOld : Fin 11 → Option V → Prop := fun k o => ∃ x, o = some x ∧ den (tagType tag (domKind k)) x
  let u : MW V := fun κ => match κ with
    | .atom s => w (.atom s)
    | .dom k i => if domKind k ∈ Ds then
        (if MKey.dom k i ∈ F then (if isOld k (w (.dom k i)) then w (.dom k i) else none)
         else if J ≤ i then (match negs[i - J]? with
             | some N => (match pick N with | some p => if p.1 = k then some p.2 else none | none => none)
             | none => none)
         else none)
      else w (.dom k i)
  have pickOk : ∀ N p, pick N = some p → Esc N p := by
    intro N p hp
    simp only [pick] at hp
    split at hp
    · rename_i h; cases hp; exact h.choose_spec
    · cases hp
  have uA : ∀ s, u (.atom s) = w (.atom s) := fun s => rfl
  have uN : ∀ k i, domKind k ∉ Ds → u (.dom k i) = w (.dom k i) := fun k i h => by simp [u, h]
  have uF : ∀ k i, MKey.dom k i ∈ F → domKind k ∈ Ds →
      u (.dom k i) = if isOld k (w (.dom k i)) then w (.dom k i) else none := fun k i m h => by simp [u, h, m]
  -- Every value of the witness at a domain key is allowed by the tag.
  have allowed : ∀ k i, TagSem den tag (domKind k) (u (.dom k i)) := by
    intro k i
    rw [tagSem_iff ef g]
    by_cases dk : domKind k ∈ Ds
    · by_cases mF : MKey.dom k i ∈ F
      · rw [uF k i mF dk]
        split
        · rename_i h; obtain ⟨x, e, hx⟩ := h; exact Or.inr ⟨x, e, hx⟩
        · exact Or.inl rfl
      · simp only [u, dk, ↓reduceIte, mF]
        split
        · cases hN : negs[i - J]? with
          | none => exact Or.inl rfl
          | some N =>
            simp only
            cases hp : pick N with
            | none => exact Or.inl rfl
            | some p =>
              simp only
              by_cases e : p.1 = k
              · obtain ⟨-, hy, -⟩ := pickOk N p hp
                rw [e] at hy
                simp only [e, ↓reduceIte]
                exact Or.inr ⟨_, rfl, hy⟩
              · simp [e]
        · exact Or.inl rfl
    · rw [uN k i dk]
      rcases hwm.2 k i with h | ⟨x, e, h | ⟨h, -⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, e, h⟩
      · exact absurd h dk
  refine ⟨u, ⟨tag, l, negs, rfl, ⟨fun s => by rw [uA]; exact hwm.1 s, allowed⟩, fun N mN hN => ?_⟩, fun s => (uA s).symm,
    fun k i h => (uN k i h).symm, fun k i mF dk => ?_⟩
  · obtain ⟨kN, nt, nl, rfl, gN, slN⟩ := lits N mN
    obtain ⟨kN', nt', nl', e', hm⟩ := hN
    obtain ⟨-, rfl, e₃⟩ := tuple3_inj e'
    obtain rfl := fieldsTerm_inj e₃
    by_cases kept : KeptNeg den tag Ds (.tuple #[.integer kN, nt, fieldsTerm nl])
    · -- A kept negation already excludes the line's maps on their non-updated part.
      refine hkn _ mN kept ⟨kN, nt, nl, rfl, fun s => by rw [← uA]; exact hm.atoms s, fun k i => ?_⟩
      obtain ⟨kN'', nt'', nl'', e'', sub⟩ := kept
      obtain ⟨-, rfl, -⟩ := tuple3_inj e''
      by_cases dk : domKind k ∈ Ds
      · rcases hwm.2 k i with h | ⟨x, e, h | ⟨_, h⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, e, Or.inl (sub _ dk x h)⟩
        · exact Or.inr ⟨x, e, Or.inr ⟨dk, h⟩⟩
      · have := hm.doms k i
        rw [uN k i dk, tagSem_iff ef gN] at this
        rcases this with h | ⟨x, e, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, e, Or.inl h⟩
    · -- A dropped negation misses the fresh key holding its escape value.
      obtain ⟨p, hp⟩ := exDrop _ mN kept
      have hpick : ∃ q, pick (.tuple #[.integer kN, nt, fieldsTerm nl]) = some q :=
        ⟨_, by simp only [pick, show ∃ p, Esc (.tuple #[.integer kN, nt, fieldsTerm nl]) p from ⟨p, hp⟩, ↓reduceDIte]; rfl⟩
      obtain ⟨q, hq⟩ := hpick
      obtain ⟨dq, -, nq⟩ := pickOk _ q hq
      obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp mN
      have fresh : MKey.dom q.1 (J + idx) ∉ F := freshIdx_not_mem (by omega)
      have uq : u (.dom q.1 (J + idx)) = some q.2 := by
        simp [u, dq, fresh, hidx, hq]
      have := hm.doms q.1 (J + idx)
      rw [uq, tagSem_iff ef gN] at this
      rcases this with h | ⟨x, e, h⟩
      · cases h
      · cases e; exact nq kN nt nl rfl h
  · rw [uF k i mF dk]
    rcases hwm.2 k i with h | ⟨x, e, h | ⟨_, h⟩⟩
    · exact Or.inl h
    · right; left
      simp only [show isOld k (w (.dom k i)) from ⟨x, e, h⟩, ↓reduceIte]
    · exact Or.inr (Or.inr ⟨x, e, h⟩)


/-- A map agreeing, on every finite set of keys, with some map of a line is a map of the widened line. -/
theorem wline_of_agree (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) {Ds : List String} {v : Term} {w : MW V}
    (h : ∀ F, ∃ u, InMLine den L u ∧ Agree den Ds v F w u) : WLine den L Ds v w := by
  obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hL
  obtain ⟨u₀, hu₀, a₀⟩ := h []
  obtain ⟨m₀, n₀⟩ := inMLine_iff.mp hu₀
  refine ⟨tag, l, negs, rfl, ⟨fun s => by rw [a₀.1 s]; exact m₀.atoms s, fun k i => ?_⟩, fun N mN kept hN => ?_⟩
  · obtain ⟨u, hu, a⟩ := h [.dom k i]
    have t := (inMLine_iff.mp hu).1.doms k i
    rw [tagSem_iff ef g] at t
    by_cases dk : domKind k ∈ Ds
    · rcases a.2.2 k i (List.mem_singleton_self _) dk with e | e | ⟨x, e, hx⟩
      · exact Or.inl e
      · rw [e]
        rcases t with t | ⟨x, t, hx⟩
        · exact Or.inl t
        · exact Or.inr ⟨x, t, Or.inl hx⟩
      · exact Or.inr ⟨x, e, Or.inr ⟨dk, hx⟩⟩
    · rw [a.2.1 k i dk]
      rcases t with t | ⟨x, t, hx⟩
      · exact Or.inl t
      · exact Or.inr ⟨x, t, Or.inl hx⟩
  · -- `u₀` would be a map of the kept negation.
    obtain ⟨kN, nt, nl, rfl, sub⟩ := kept
    obtain ⟨kN', nt', nl', e', hw⟩ := hN
    obtain ⟨-, rfl, e₃⟩ := tuple3_inj e'
    obtain rfl := fieldsTerm_inj e₃
    obtain ⟨kN'', nt'', nl'', e'', gN, -⟩ := lits _ mN
    obtain ⟨-, rfl, -⟩ := tuple3_inj e''
    refine n₀ _ mN ⟨kN, nt, nl, rfl, fun s => by rw [← a₀.1 s]; exact hw.1 s, fun k i => ?_⟩
    rw [tagSem_iff ef gN]
    by_cases dk : domKind k ∈ Ds
    · have t := m₀.doms k i
      rw [tagSem_iff ef g] at t
      rcases t with t | ⟨x, t, hx⟩
      · exact Or.inl t
      · exact Or.inr ⟨x, t, sub _ dk x hx⟩
    · rw [← a₀.2.1 k i dk]
      rcases hw.2 k i with t | ⟨x, t, hx | ⟨hd, _⟩⟩
      · exact Or.inl t
      · exact Or.inr ⟨x, t, hx⟩
      · exact absurd hd dk

/-- The widened lines of a type hold its canonical domain put. -/
theorem wlines_domc (ef : EF nd E V den tl K) {lines : List Term} (hl : ∀ L ∈ lines, MLine E L) {Ds : List String}
    (hA : "atom" ∉ Ds) (hD : ∀ d ∈ Ds, d ∈ domainKinds) {v : Term} (w : MW V) :
    ((∃ L ∈ lines, WLine den L Ds v w) ∧ w ≠ wNone) ↔
      DomC den (fun u => ∃ L ∈ lines, InMLine den L u) Ds v w := by
  classical
  constructor
  · rintro ⟨⟨L, mL, hw⟩, ne⟩
    refine ⟨ne, fun F => ?_⟩
    obtain ⟨u, hu, a⟩ := wline_witness ef (hl L mL) hA hD hw F
    exact ⟨u, ⟨L, mL, hu⟩, a⟩
  · rintro ⟨ne, h⟩
    refine ⟨?_, ne⟩
    -- One refuting set of keys per line failing to hold `w`.
    let FL : Term → List MKey := fun L =>
      if hr : ∃ F, ∀ u, InMLine den L u → ¬Agree den Ds v F w u then hr.choose else []
    obtain ⟨u, ⟨L, mL, hu⟩, a⟩ := h (lines.flatMap FL)
    refine ⟨L, mL, Classical.byContradiction fun nw => ?_⟩
    have hr : ∃ F, ∀ u, InMLine den L u → ¬Agree den Ds v F w u := by
      refine Classical.byContradiction fun nr => nw (wline_of_agree ef (hl L mL) fun F => ?_)
      have : ¬∀ u, InMLine den L u → ¬Agree den Ds v F w u := fun hh => nr ⟨F, hh⟩
      obtain ⟨u', hu'⟩ := Classical.not_forall.mp this
      obtain ⟨i', a'⟩ := Classical.not_imp.mp hu'
      exact ⟨u', i', Classical.not_not.mp a'⟩
    have hF : FL L = hr.choose := by simp only [FL, hr, ↓reduceDIte]
    exact hr.choose_spec u hu (a.mono fun κ m => List.mem_flatMap.mpr ⟨L, mL, hF ▸ m⟩)




theorem msem_req_ne_none {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l) (hr : HasReq l) {w : MW V}
    (h : MSem den tag l w) : w ≠ wNone := by
  rintro rfl
  obtain ⟨e, me, t, he⟩ := hr
  obtain ⟨⟨s, es⟩, -⟩ := sl.1 e me
  have := h.atoms s
  unfold FSem at this
  rw [lookup_of_mem sl me es] at this
  simp only at this
  rw [he, show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk] at this
  simp [wNone] at this

/-- `map_update_box/5` putting a non-empty static value at the named keys of a type and every domain: the box,
without the empty map. -/
theorem box_runAll (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ []) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (ks AK Ds : List String)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) (hA : "atom" ∈ Ds) (hL : Ds.length = 12) :
    ∃ NK R, Elixir.Module.Types.Descr.«map_update_box/5» (D (n + 4)) (Term.list lines) (Term.list (ks.map Term.atom))
        (Term.list (Ds.map Term.atom)) (forceOp v) (Term.list (AK.map Term.atom)) = .ok (.map R) ∧ (∀ s ∈ AK, s ∈ NK) ∧
      (∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) ∧ (∀ s ∈ NK, s ∈ AK ∨ ∃ L ∈ lines, LineNames L s) ∧
      MapsD E den R (fun w => BoxSynD den lines ks NK Ds v w ∧ w ≠ wNone) := by
  have hl' : ∀ L ∈ lines, MLine E L := fun L m => (hl L m).1
  obtain ⟨X, NK, rX, rNK, ndNK, saNK, akNK, lnNK, orNK⟩ := box_named (E := E) (n + 1) lines hl' AK
  obtain ⟨P, Q, rPQ, hP, fP, uQ, cQ, nQ, kQ⟩ := box_fields ef hn lines hl hv ks NK ndNK
  obtain ⟨Q', rQ', subQ', supQ', -⟩ := box_filter ef (m := n + 3) (by omega) Q uQ
  obtain ⟨T, U, rTU, lowT, semT, duU, neU⟩ := box_domainsD ef (n := n + 3) (by omega) lines hl' hv Ds hD
  have sP : FieldsV E P := by
    refine ⟨fun e me => ?_, ?_⟩
    · obtain ⟨s, e₁, fe, -⟩ := fP e me; exact ⟨⟨s, e₁⟩, fe⟩
    · have := saNK; rw [← hP] at this; exact List.pairwise_map.mp this
  -- The field of a named key over the lines.
  have lookP : ∀ s ∈ NK, ∃ f, mapLookup P (.atom s) = some f ∧ FieldValue E f ∧
      ∀ o, FieldSem den f o ↔ ∃ L ∈ lines, LongM den L s o := fun s ms => by
    have : Term.atom s ∈ P.map Prod.fst := by rw [hP]; exact List.mem_map_of_mem ms
    obtain ⟨e, me, e₁⟩ := List.mem_map.mp this
    obtain ⟨s', e₁', fe, se⟩ := fP e me
    rw [e₁] at e₁'; cases e₁'
    exact ⟨e.2, lookup_of_mem sP me e₁, fe, se⟩
  obtain ⟨P2, rP2, sP2, keysP2, lookP2⟩ := box_store ef (m := n + 3) (by omega) sP Q' (fun q mq => by
      obtain ⟨s, -, old, new, rfl, hold, sold, hnew, -⟩ := uQ q (subQ'.subset mq)
      have ms : s ∈ NK := by
        have := kQ _ (subQ'.subset mq); simp only [updKey] at this; simpa using this
      obtain ⟨f, lf, -, sf⟩ := lookP s ms
      exact ⟨s, old, new, rfl, hold, hnew, f, lf, fun o => (sold o).trans (sf o).symm⟩)
    ((subQ'.map updKey).nodup nQ)
  -- The tag, open when every kind holds `term()`.
  have gT := lowTag_tagV lowT
  classical
  let T2 := if Term.compare (Term.fuel T allTerm) T allTerm = .eq then Term.atom "open" else T
  have gT2 : TagV E T2 := by
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq
    · simp only [T2, e, ↓reduceIte]; exact Or.inl rfl
    · simp only [T2, e, ↓reduceIte]; exact gT
  have semT2 : ∀ kind ∈ domainKinds, ∀ x, den (tagType T2 kind) x ↔ BoxTagD den lines v Ds kind x := by
    intro kind mk x
    rw [← semT kind mk x]
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq
    · simp only [T2, e, ↓reduceIte, tagType]
      exact ⟨fun _ => allTerm_full ef gT e kind mk x, fun _ => ef.den_term x⟩
    · simp only [T2, e, ↓reduceIte]
  obtain ⟨bo, rbo, fbo, sbo⟩ := map_new_leaf (den := den) ef gT2 sP2
  -- The box joins the updated maps, without the empty map unless some key is required.
  obtain ⟨Up, Un, ra, fUp, fUn, sU⟩ : ∃ Up Un, Elixir.Module.Types.Descr.«map_update_domains_add/3» (D (n + 4)) bo
      (fieldsTerm P2) (.tuple #[.nil, .nil]) = .ok (.tuple #[Term.list Up, Term.list Un]) ∧
      (∀ b ∈ Up, MField E b) ∧ (∀ b ∈ Un, MField E b) ∧
      ∀ w, (((∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone) ∨ ∃ b ∈ Un, denMF E den b w = Bool.true) ↔
        denMF E den bo w = Bool.true ∧ w ≠ wNone := by
    rcases domains_add (n + 3) bo sP2 [] [] with ⟨ra, hreq⟩ | ⟨ra, -⟩
    · refine ⟨[], [bo], by simpa [Term.list] using ra, by simp, by simpa using fbo, fun w => ?_⟩
      simp only [List.not_mem_nil, false_and, exists_false, false_or, List.mem_singleton, exists_eq_left]
      refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
      have := (sbo w).mp h
      exact msem_req_ne_none sP2 hreq this
    · refine ⟨[bo], [], by simpa [Term.list] using ra, by simpa using fbo, by simp, fun w => ?_⟩
      simp
  obtain ⟨R, rR, mR⟩ := domains_result ef (m := n + 2) (by omega) Up Un fUp fUn
  -- The output holds the maps of the box.
  have noneP : ∀ s, s ∉ NK → mapLookup P (.atom s) = none := fun s ns => by
    cases h : mapLookup P (.atom s) with
    | none => rfl
    | some f =>
      obtain ⟨e, me, e₁, -⟩ := lookup_some_mem h
      have : Term.atom s ∈ NK.map Term.atom := by rw [← hP]; exact List.mem_map.mpr ⟨e, me, e₁⟩
      exact absurd (by simpa using this) ns
  -- Each key and line has a value or absence.
  have someOld : ∀ s, ∃ o, ∃ L ∈ lines, LongM den L s o := fun s => by
    obtain ⟨L, mL⟩ := List.exists_mem_of_ne_nil lines hne
    obtain ⟨w, hw⟩ := (hl L mL).2
    exact ⟨_, L, mL, w, hw, rfl⟩
  have semNew : ∀ s ∈ NK, ∀ o, (∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new o) ↔
      s ∈ ks ∧ ∃ x, o = some x ∧ den v x := fun s ms o => by
    constructor
    · rintro ⟨q, mq, old, new, rfl, hq⟩
      obtain ⟨s', ks', old', new', e', -, sold', -, snew'⟩ := uQ _ (subQ'.subset mq)
      obtain ⟨e₁, rfl, rfl⟩ := tuple3_inj e'
      cases Term.atom.inj e₁
      exact ⟨ks', ((snew' o).mp hq).1⟩
    · rintro ⟨sk, x, rfl, hx⟩
      obtain ⟨q, mq, old, new, rfl, hold, sold, hnew, snew⟩ := cQ s ms sk
      obtain ⟨o', L, mL, hL⟩ := someOld s
      have hn : FieldSem den new (some x) := (snew _).mpr ⟨⟨x, rfl, hx⟩, o', (sold o').mpr ⟨L, mL, hL⟩⟩
      exact ⟨_, supQ' _ mq ⟨_, hn⟩, old, new, rfl, hn⟩
  have semBo : ∀ w, MSem den T2 P2 w ↔ BoxSynD den lines ks NK Ds v w := fun w => by
    rw [msem_keys]
    constructor
    · intro h
      refine ⟨fun s ms => ?_, fun s ns => ?_, fun k i => ?_⟩
      · have := h (.atom s)
        simp only [KeyAllow, FSem] at this
        obtain ⟨f, lf, -, sf⟩ := lookP s ms
        cases l2 : mapLookup P2 (.atom s) with
        | none => exact absurd ((keysP2 s).mp l2) (by simp [lf])
        | some f2 =>
          rw [l2] at this
          rcases (lookP2 s _).mp ⟨f2, l2, this⟩ with ⟨f', lf', h'⟩ | h'
          · rw [lf] at lf'; cases lf'; exact Or.inl ((sf _).mp h')
          · exact Or.inr ((semNew s ms _).mp h')
      · have := h (.atom s)
        simp only [KeyAllow, FSem] at this
        rw [(keysP2 s).mpr (noneP s ns)] at this
        rcases (tagSem_iff ef gT2 _ _).mp this with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 "atom" (by simp [domainKinds]) x).mp hx⟩
      · have := h (.dom k i)
        simp only [KeyAllow] at this
        rcases (tagSem_iff ef gT2 _ _).mp this with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 _ (domKind_mem k) x).mp hx⟩
    · rintro ⟨hn, hu, hd⟩ q
      cases q with
      | atom s =>
        simp only [KeyAllow, FSem]
        by_cases ms : s ∈ NK
        · obtain ⟨f, lf, -, sf⟩ := lookP s ms
          have hf : (∃ f', mapLookup P (.atom s) = some f' ∧ FieldSem den f' (w (.atom s))) ∨
              ∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new (w (.atom s)) := by
            rcases hn s ms with h' | h'
            · exact Or.inl ⟨f, lf, (sf _).mpr h'⟩
            · exact Or.inr ((semNew s ms _).mpr h')
          obtain ⟨f2, l2, h2⟩ := (lookP2 s _).mpr hf
          rw [l2]; exact h2
        · rw [(keysP2 s).mpr (noneP s ms)]
          simp only
          rw [tagSem_iff ef gT2]
          rcases hu s ms with h' | ⟨x, h', hx⟩
          · exact Or.inl h'
          · exact Or.inr ⟨x, h', (semT2 "atom" (by simp [domainKinds]) x).mpr hx⟩
      | dom k i =>
        simp only [KeyAllow]
        rw [tagSem_iff ef gT2]
        rcases hd k i with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 _ (domKind_mem k) x).mpr hx⟩
  refine ⟨NK, R, ?_, akNK, lnNK, orNK, mR.1, mR.2.1, fun w => (mR.2.2 w).trans ((sU w).trans ?_)⟩
  rotate_left
  · rw [sbo, semBo]
  · unfold Elixir.Module.Types.Descr.«map_update_box/5»
    have rTU' := rTU
    simp only [domainKinds, List.map] at rTU'
    have hU : U ≠ [] := neU.mpr ⟨List.ne_nil_of_mem hA, vne⟩
    have eqU : Erlang.erlang.«==/2» (Term.list U) .nil = .ok (.atom "false") := by
      cases U with
      | nil => exact absurd rfl hU
      | cons u us => simp [Term.list, eqq_val, boolAtom]
    -- Whether some updated key or domain holds a value.
    obtain ⟨b9, a9⟩ : ∃ b9 : Bool, Erlang.lists.«any/2» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-9-" 1 #[]) (Term.list Q') = .ok (boolAtom b9) := by
      classical
      refine ⟨_, any_list _ _ _ _ (fun q => decide (∃ t o, updNew q = .tuple #[t, boolAtom o] ∧ ∃ x, den t x)) Q'
        fun q mq => ?_⟩
      obtain ⟨s, -, old, new, rfl, -, -, ⟨t, o, rfl, ht⟩, -⟩ := uQ q (subQ'.subset mq)
      obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-9-/1».pure]
      simp only [Elixir.Module.Types.Descr.«-map_update_box/5-fun-9-/1», boolAtom] at re ⊢
      cases o <;> cases e <;> simp [re, Erlang.erlang.«not/1», updNew] <;>
        first | (exact Classical.byContradiction fun h => by have := se.mpr (by simpa using h); cases this) |
          (intro x hx; exact se.mp rfl x hx)
    have a10 : Erlang.lists.«any/2» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/5-fun-10-" 1 #[]) (Term.list U) = .ok (.atom "true") := by
      classical
      have := any_list (D (n + 4)) _ _ _ (fun u => decide (∃ d o nt, u = .tuple #[d, o, nt] ∧ ∃ x, den nt x)) U
        fun u mu => by
          obtain ⟨d, o, nt, rfl, hnt, x, hx⟩ := duU u mu
          obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) hnt
          have : e = Bool.false := by cases e; rfl; exact absurd hx (se.mp rfl x)
          subst this
          rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/5-fun-10-/1».pure]
          simp [Elixir.Module.Types.Descr.«-map_update_box/5-fun-10-/1», re, Erlang.erlang.«not/1», boolAtom]
          exact ⟨x, hx⟩
      rw [this]
      obtain ⟨u, us, rfl⟩ : ∃ u us, U = u :: us := by cases U with | nil => exact absurd rfl hU | cons u us => exact ⟨u, us, rfl⟩
      obtain ⟨d, o, nt, rfl, hnt, x, hx⟩ := duU _ List.mem_cons_self
      have : ((Term.tuple #[d, o, nt] :: us).any
          fun u => decide (∃ d o nt, u = .tuple #[d, o, nt] ∧ ∃ x, den nt x)) = Bool.true := by
        rw [List.any_cons, decide_eq_true ⟨d, o, nt, rfl, x, hx⟩, Bool.true_or]
      rw [this]; rfl
    have rAll : Erlang.lists.«map/2» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/5-anonymous-0-" 1 #[])
        (Term.list (domainKinds.map Term.atom)) = .ok allTerm := by
      have := all_term_run _ (Or.inl rfl) (n + 3)
      rwa [usort_sorted _ kinds_sa, Lynx.Except.ok_bind] at this
    have uK := usort_sorted _ kinds_sa
    simp only [domainKinds, List.map] at rAll uK
    have rT2 : Erlang.erlang.«==/2» T allTerm = .ok (boolAtom (Term.compare (Term.fuel T allTerm) T allTerm == .eq)) :=
      eqq_val T allTerm
    simp [rX, rNK, rPQ, rQ', rTU', eqU, Lynx.Except.andAlso, Erlang.erlang.«element/2», rP2, uK, rAll, rT2]
    have eQ := eqq_val (Term.list Q') .nil
    have lenD : Erlang.erlang.«length/1» (Term.list (Ds.map Term.atom)) = .ok (.integer (Ds.length : Int)) := by
      simpa using length_list (Ds.map Term.atom)
    have hL' : ((Ds.length : Int) = 12) := by omega
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
      simp only [T2, e, ↓reduceIte] at rbo <;>
      cases b9 <;>
      simp [eQ, e, boolAtom, rbo, Erlang.erlang.«/=/2», a9, a10, Lynx.Except.orElse, Erlang.erlang.«=:=/2»]
    all_goals by_cases q : Term.list Q' = .nil <;> simp [q, lenD, hL', ra, rR]

theorem partition1_atom (m : Nat) : ∀ (Ds : List String) (A B : List Term),
    Erlang.lists.«partition_1/4» (D (m + 1))
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-2-" 1 #[]) (Term.list (Ds.map Term.atom))
      (Term.list A) (Term.list B) =
      .ok (.tuple #[Term.list (A.reverse ++ (Ds.filter (· = "atom")).map Term.atom),
        Term.list (B.reverse ++ (Ds.filter (· ≠ "atom")).map Term.atom)])
  | [], A, B => by simp [Erlang.lists.«partition_1/4», Term.list, reverse1_list]
  | d :: Ds, A, B => by
    rw [Erlang.lists.«partition_1/4».eq_def]
    simp only [List.map_cons, Term.list]
    by_cases h : d = "atom"
    · subst h
      have := partition1_atom m Ds (.atom "atom" :: A) B
      simp only [Term.list] at this
      simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-2-/1».pure,
        Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-2-/1», Erlang.erlang.«==/2», this]
    · have := partition1_atom m Ds A (.atom d :: B)
      simp only [Term.list] at this
      have ne : Erlang.erlang.«==/2» (.atom d) (.atom "atom") = .ok (.atom "false") := by
        simp [Erlang.erlang.«==/2», h]
      simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-2-/1».pure,
        Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-2-/1», ne, this, h]

theorem partition_atom (m : Nat) (Ds : List String) :
    Erlang.lists.«partition/2» (D (m + 1))
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-2-" 1 #[]) (Term.list (Ds.map Term.atom)) =
      .ok (.tuple #[Term.list ((Ds.filter (· = "atom")).map Term.atom),
        Term.list ((Ds.filter (· ≠ "atom")).map Term.atom)]) := by
  have := partition1_atom m Ds [] []
  simp only [Term.list, List.reverse_nil, List.nil_append] at this
  simpa [Erlang.lists.«partition/2», Erlang.erlang.«is_function/2»] using this


/-- `lists:usort/1` on domain kinds: distinct kinds, twelve exactly when every kind is there. -/
theorem kinds_usort (ds : List Term) (hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) :
    ∃ Ks : List String, Erlang.lists.«usort/1» (Term.list ds) = .ok (Term.list (Ks.map Term.atom)) ∧
      (∀ s, s ∈ Ks ↔ .atom s ∈ ds) ∧ Ks.Nodup ∧ (∀ s ∈ Ks, s ∈ domainKinds) ∧
      (Ks.length = 12 ↔ ∀ d ∈ domainKinds, .atom d ∈ ds) := by
  obtain ⟨R, rR, sR, mR⟩ := usort_atoms ds fun d md => by obtain ⟨s, -, rfl⟩ := hds d md; exact ⟨s, rfl⟩
  obtain ⟨Ks, rfl⟩ : ∃ Ks : List String, R = Ks.map Term.atom := by
    have aR : ∀ r ∈ R, ∃ s, r = .atom s := fun r mr => by
      obtain ⟨s, -, rfl⟩ := hds r ((mR r).mp mr); exact ⟨s, rfl⟩
    clear rR sR mR
    induction R with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := aR r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => aR x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  have mem : ∀ s, s ∈ Ks ↔ .atom s ∈ ds := fun s => by
    rw [← mR]; simp
  have nd : Ks.Nodup := by
    have := List.Pairwise.imp (fun h e => cmp_lt_ne h e) sR
    exact (List.pairwise_map.mp this).imp fun h e => h (by rw [e])
  have sub : ∀ s ∈ Ks, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := hds _ ((mem s).mp ms); cases e; exact ms'
  have ndK : domainKinds.Nodup := by decide
  classical
  -- The kinds in `Ks`, in the order of all kinds, have its length.
  let F := domainKinds.filter (fun d => decide (d ∈ Ks))
  have ndF : F.Nodup := List.Pairwise.filter _ ndK
  have pm : F.Perm Ks := (List.perm_ext_iff_of_nodup ndF nd).mpr fun d => by
    simp only [F, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨sub d h, h⟩⟩
  have len : Ks.length = F.length := pm.length_eq.symm
  have twelve : domainKinds.length = 12 := rfl
  refine ⟨Ks, rR, mem, nd, sub, ?_⟩
  rw [len, ← twelve, List.length_filter_eq_length_iff]
  exact ⟨fun h d md => (mem d).mp (by simpa using h d md), fun h d md => by simpa using (mem d).mpr (h d md)⟩


section mono
variable {M₁ M₂ : MW V → Prop} {v₁ v₂ : Term}

theorem not_outV {v : Term} {o : Option V} {x : V} (e : o = some x) (h : den v x) : ¬OutV den v o := by
  rintro (h' | ⟨y, e', ny⟩)
  · rw [e] at h'; cases h'
  · rw [e] at e'; cases e'; exact ny h

theorem union_mono' (hM : ∀ u, M₁ u → M₂ u) {A₁ A₂ : String → Prop} (hA : ∀ a, A₁ a → A₂ a)
    (hv : ∀ x, den v₁ x → den v₂ x) {w : MW V} (h : UnionS den M₁ A₁ v₁ w) : UnionS den M₂ A₂ v₂ w := by
  obtain ⟨a, ha, ⟨x, wa, hx⟩, o, hu⟩ := h
  exact ⟨a, hA a ha, ⟨x, wa, hv x hx⟩, o, hM _ hu⟩

theorem boxP_mono (hM : ∀ u, M₁ u → M₂ u) {S₁ S₂ : List String} (hS : ∀ s, s ∈ S₂ → s ∈ S₁)
    {P₁ P₂ : String → Prop} (hP : ∀ d, P₁ d → P₂ d) (hv : ∀ x, den v₁ x → den v₂ x) {w : MW V}
    (h : BoxP den M₁ S₁ P₁ v₁ w) : BoxP den M₂ S₂ P₂ v₂ w := by
  obtain ⟨⟨ha, hd⟩, nu⟩ := h
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun ⟨ua, ud⟩ => nu ⟨fun s ns => ?_, fun k i pk => ?_⟩⟩
  · rcases ha s with ⟨u, hu, e⟩ | ⟨ns, x, e, hx⟩
    · exact Or.inl ⟨u, hM u hu, e⟩
    · exact Or.inr ⟨fun m => ns (hS s m), x, e, hv x hx⟩
  · rcases hd k i with e | ⟨x, e, ⟨u, j, hu, ej⟩ | ⟨pk, hx⟩⟩
    · exact Or.inl e
    · exact Or.inr ⟨x, e, Or.inl ⟨u, j, hM u hu, ej⟩⟩
    · exact Or.inr ⟨x, e, Or.inr ⟨hP _ pk, hv x hx⟩⟩
  · rcases ua s (fun m => ns (hS s m)) with h | ⟨y, e', ny⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, e', fun hy => ny (hv y hy)⟩
  · rcases ud k i (hP _ pk) with h | ⟨y, e', ny⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, e', fun hy => ny (hv y hy)⟩

theorem union_boxP (hM : ∀ u, M₁ u → M₂ u) {A₁ : String → Prop} {S₂ : List String} (hA : ∀ a, A₁ a → a ∉ S₂)
    {P : String → Prop} (hv : ∀ x, den v₁ x → den v₂ x) {w : MW V} (h : UnionS den M₁ A₁ v₁ w) :
    BoxP den M₂ S₂ P v₂ w := by
  obtain ⟨a, ha, ⟨x, wa, hx⟩, o, hu⟩ := h
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun un => not_outV wa (hv x hx) (un.1 a (hA a ha))⟩
  · by_cases e : s = a
    · subst e; exact Or.inr ⟨hA s ha, x, wa, hv x hx⟩
    · exact Or.inl ⟨_, hM _ hu, by simp [setK, e]⟩
  · cases h : w (.dom k i) with
    | none => exact Or.inl rfl
    | some y => exact Or.inr ⟨y, rfl, Or.inl ⟨_, i, hM _ hu, by simp [setK, h]⟩⟩

theorem boxD_mono (hM : ∀ u, M₁ u → M₂ u) {S₁ S₂ : List String} (hS : ∀ s, s ∈ S₂ → s ∈ S₁)
    {P₁ P₂ : String → Prop} (hP : ∀ d, P₁ d → P₂ d) (hv : ∀ x, den v₁ x → den v₂ x) {w : MW V}
    (h : BoxD den M₁ S₁ P₁ v₁ w) : BoxD den M₂ S₂ P₂ v₂ w := by
  obtain ⟨ha, hd⟩ := h
  refine ⟨fun s => ?_, fun k i => ?_⟩
  · rcases ha s with ⟨u, hu, e⟩ | ⟨ns, x, e, hx⟩
    · exact Or.inl ⟨u, hM u hu, e⟩
    · exact Or.inr ⟨fun m => ns (hS s m), x, e, hv x hx⟩
  · rcases hd k i with e | ⟨x, e, ⟨u, j, hu, ej⟩ | ⟨pk, hx⟩⟩
    · exact Or.inl e
    · exact Or.inr ⟨x, e, Or.inl ⟨u, j, hM u hu, ej⟩⟩
    · exact Or.inr ⟨x, e, Or.inr ⟨hP _ pk, hv x hx⟩⟩

theorem union_boxD (hM : ∀ u, M₁ u → M₂ u) {A₁ : String → Prop} {S₂ : List String} (hA : ∀ a, A₁ a → a ∉ S₂)
    {P : String → Prop} (hv : ∀ x, den v₁ x → den v₂ x) {w : MW V} (h : UnionS den M₁ A₁ v₁ w) :
    BoxD den M₂ S₂ P v₂ w :=
  (union_boxP (P := P) hM hA hv h).1

theorem domC_boxD (hM : ∀ u, M₁ u → M₂ u) {Ds : List String} {S : List String} {P : String → Prop}
    (hP : ∀ d ∈ Ds, P d) (hv : ∀ x, den v₁ x → den v₂ x) {w : MW V}
    (h : DomC den M₁ Ds v₁ w) : BoxD den M₂ S P v₂ w := by
  obtain ⟨u₀, hu₀, a₀⟩ := h.2 []
  refine ⟨fun s => Or.inl ⟨u₀, hM _ hu₀, (a₀.1 s).symm⟩, fun k i => ?_⟩
  obtain ⟨u, hu, a⟩ := h.2 [.dom k i]
  by_cases dk : domKind k ∈ Ds
  · rcases a.2.2 k i (List.mem_singleton_self _) dk with e | e | ⟨x, e, hx⟩
    · exact Or.inl e
    · cases h' : u (.dom k i) with
      | none => exact Or.inl (e.trans h')
      | some y => exact Or.inr ⟨y, e.trans h', Or.inl ⟨u, i, hM u hu, h'⟩⟩
    · exact Or.inr ⟨x, e, Or.inr ⟨hP _ dk, hv x hx⟩⟩
  · rw [a.2.1 k i dk]
    cases h' : u (.dom k i) with
    | none => exact Or.inl rfl
    | some y => exact Or.inr ⟨y, rfl, Or.inl ⟨u, i, hM u hu, h'⟩⟩

end mono

/-- The domain kinds of a split, as strings. -/
def dsStrs (ds : List Term) : List String := ds.filterMap fun d => match d with | .atom s => some s | _ => none

theorem dsStrs_mem {ds : List Term} {s : String} : s ∈ dsStrs ds ↔ .atom s ∈ ds := by
  simp only [dsStrs, List.mem_filterMap]
  constructor
  · rintro ⟨d, md, e⟩
    cases d <;> simp at e
    subst e; exact md
  · intro h; exact ⟨_, h, rfl⟩

/-- Splits whose domains are every kind of key. -/
def FullDs (ds : List Term) : Prop := ∀ d ∈ domainKinds, .atom d ∈ ds

/-- The maps `map_put/3` gives, from the maps of a type and a split of the keys: the puts at its atoms, or the box
at the atoms outside its negated set, and the domains, widened. With every kind, the box takes the domains. -/
def PutSem (den : Term → V → Prop) (M : MW V → Prop) (rs : List Term) (neg : Term) (ds : List Term) (v : Term)
    (w : MW V) : Prop :=
  (neg = .atom "nil" ∧ (UnionS den M (fun a => .atom a ∈ rs) v w ∨
    ((∃ k, .atom (domKind k) ∈ ds) ∧ (∃ x, den v x) ∧ DomC den M (dsStrs ds) v w))) ∨
  ∃ N, neg = .map N ∧
    ((FullDs ds ∧ (∃ x, den v x) ∧ BoxD den M (setStrs N) (fun d => .atom d ∈ ds) v w ∧ w ≠ wNone) ∨
     (¬FullDs ds ∧ (BoxP den M (setStrs N) (fun _ => False) v w ∨
       ((∃ k, .atom (domKind k) ∈ ds) ∧ (∃ x, den v x) ∧ DomC den M (dsStrs ds) v w))))


theorem domC_mono_k {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {Ds₁ Ds₂ : List String}
    (hD : ∀ k : Fin 11, domKind k ∈ Ds₁ → domKind k ∈ Ds₂) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    {w : MW V} (h : DomC den M₁ Ds₁ v₁ w) : DomC den M₂ Ds₂ v₂ w := by
  refine ⟨h.1, fun F => ?_⟩
  obtain ⟨u, hu, a₁, a₂, a₃⟩ := h.2 F
  refine ⟨u, hM u hu, a₁, fun k i nk => a₂ k i fun m => nk (hD k m), fun k i mF dk => ?_⟩
  by_cases d₁ : domKind k ∈ Ds₁
  · rcases a₃ k i mF d₁ with e | e | ⟨x, e, hx⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨x, e, hv x hx⟩)
  · exact Or.inr (Or.inl (a₂ k i d₁))

/-- `map_put/3` is monotone in the type, the keys and the value. -/
theorem put_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    {rs₁ rs₂ ds₁ ds₂ : List Term} {neg₁ neg₂ : Term} (ok₁ : SplitOk rs₁ neg₁ ds₁) (ok₂ : SplitOk rs₂ neg₂ ds₂)
    (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (hK : ∀ κ, SplitKey rs₁ neg₁ ds₁ κ → SplitKey rs₂ neg₂ ds₂ κ) {w : MW V}
    (h : PutSem den M₁ rs₁ neg₁ ds₁ v₁ w) : PutSem den M₂ rs₂ neg₂ ds₂ v₂ w := by
  have kd : ∀ k : Fin 11, .atom (domKind k) ∈ ds₁ → .atom (domKind k) ∈ ds₂ := fun k h => hK (.dom k 0) h
  have kD : ∀ k : Fin 11, domKind k ∈ dsStrs ds₁ → domKind k ∈ dsStrs ds₂ := fun k h =>
    dsStrs_mem.mpr (kd k (dsStrs_mem.mp h))
  have vne : (∃ x, den v₁ x) → ∃ x, den v₂ x := fun ⟨x, hx⟩ => ⟨x, hv x hx⟩
  -- Kinds of the first split other than atoms are kinds of the second.
  have kinds : ∀ d ∈ dsStrs ds₁, d ≠ "atom" → .atom d ∈ ds₂ := fun d md na => by
    obtain ⟨s, ms, e⟩ := ok₁.hds _ (dsStrs_mem.mp md)
    cases e
    obtain ⟨k, rfl⟩ := domKind_of ms na
    exact kd k (dsStrs_mem.mp md)
  -- A negated set of the second split misses the atoms of the first.
  have outside : ∀ N₂, neg₂ = .map N₂ → ∀ s, SplitKey rs₁ neg₁ ds₁ (.atom s) → s ∉ setStrs N₂ := by
    intro N₂ e₂ s hs m
    rcases hK _ hs with h | ⟨N, e, hN⟩
    · rw [nr₂ N₂ e₂] at h; simp at h
    · rw [e₂] at e; cases e
      exact setStrs_mem.mp m hN
  -- The second split negates atoms when the first does.
  have negs : ∀ N₁, neg₁ = .map N₁ → ∃ N₂, neg₂ = .map N₂ := by
    intro N₁ e₁
    rcases ok₂.hneg with e₂ | h
    · exfalso
      obtain ⟨c, hc⟩ := fresh_str (dsStrs rs₂ ++ setStrs N₁)
      have k₁ : SplitKey rs₁ neg₁ ds₁ (.atom c) :=
        Or.inr ⟨N₁, e₁, Classical.byContradiction fun hn => hc (List.mem_append_right _ (setStrs_mem.mpr hn))⟩
      rcases hK _ k₁ with h | ⟨N, e, -⟩
      · exact hc (List.mem_append_left _ (dsStrs_mem.mpr h))
      · rw [e₂] at e; cases e
    · exact h
  have full : FullDs ds₁ → FullDs ds₂ := fun f d md => by
    by_cases na : d = "atom"
    · subst na
      obtain ⟨N₁, e₁⟩ := ok₁.hatom.mp (f _ md)
      exact ok₂.hatom.mpr (negs N₁ e₁)
    · exact kinds d (dsStrs_mem.mpr (f d md)) na
  -- The domain part, into either shape of the second split.
  have domPart : (∃ k, .atom (domKind k) ∈ ds₁) → (∃ x, den v₁ x) → DomC den M₁ (dsStrs ds₁) v₁ w →
      PutSem den M₂ rs₂ neg₂ ds₂ v₂ w := fun ⟨k, mk⟩ hx hc => by
    rcases ok₂.hneg with e₂ | ⟨N₂, e₂⟩
    · exact Or.inl ⟨e₂, Or.inr ⟨⟨k, kd k mk⟩, vne hx, domC_mono_k hM kD hv hc⟩⟩
    · refine Or.inr ⟨N₂, e₂, ?_⟩
      by_cases f₂ : FullDs ds₂
      · refine Or.inl ⟨f₂, vne hx, domC_boxD hM (fun d md => ?_) hv hc, hc.1⟩
        by_cases na : d = "atom"
        · subst na; exact ok₂.hatom.mpr ⟨N₂, e₂⟩
        · exact kinds d md na
      · exact Or.inr ⟨f₂, Or.inr ⟨⟨k, kd k mk⟩, vne hx, domC_mono_k hM kD hv hc⟩⟩
  rcases h with ⟨e₁, hu | ⟨hk, hx, hc⟩⟩ | ⟨N₁, e₁, ⟨f₁, hx, hb, hne⟩ | ⟨f₁, hb | ⟨hk, hx, hc⟩⟩⟩
  · -- Puts at atoms.
    have key : ∀ a, .atom a ∈ rs₁ → SplitKey rs₁ neg₁ ds₁ (.atom a) := fun a h => Or.inl h
    rcases ok₂.hneg with e₂ | ⟨N₂, e₂⟩
    · refine Or.inl ⟨e₂, Or.inl (union_mono' hM (fun a ha => ?_) hv hu)⟩
      rcases hK _ (key a ha) with h | ⟨N, e, -⟩
      · exact h
      · rw [e₂] at e; cases e
    · refine Or.inr ⟨N₂, e₂, ?_⟩
      have out : ∀ a, .atom a ∈ rs₁ → a ∉ setStrs N₂ := fun a ha => outside N₂ e₂ a (key a ha)
      by_cases f₂ : FullDs ds₂
      · obtain ⟨a, -, ⟨x, wa, hx⟩, -⟩ := id hu
        exact Or.inl ⟨f₂, ⟨x, hv x hx⟩, union_boxD hM out hv hu, fun e => by rw [e] at wa; cases wa⟩
      · exact Or.inr ⟨f₂, Or.inl (union_boxP hM out hv hu)⟩
  · exact domPart hk hx hc
  · -- The box with every kind.
    obtain ⟨N₂, e₂⟩ := negs N₁ e₁
    have hS : ∀ s, s ∈ setStrs N₂ → s ∈ setStrs N₁ := fun s m => Classical.byContradiction fun n =>
      outside N₂ e₂ s (Or.inr ⟨N₁, e₁, Classical.byContradiction fun hn => n (setStrs_mem.mpr hn)⟩) m
    refine Or.inr ⟨N₂, e₂, Or.inl ⟨full f₁, vne hx, boxD_mono hM hS (fun d md => ?_) hv hb, hne⟩⟩
    by_cases na : d = "atom"
    · subst na; exact ok₂.hatom.mpr ⟨N₂, e₂⟩
    · exact kinds d (dsStrs_mem.mpr md) na
  · -- The box at atoms.
    obtain ⟨N₂, e₂⟩ := negs N₁ e₁
    have hS : ∀ s, s ∈ setStrs N₂ → s ∈ setStrs N₁ := fun s m => Classical.byContradiction fun n =>
      outside N₂ e₂ s (Or.inr ⟨N₁, e₁, Classical.byContradiction fun hn => n (setStrs_mem.mpr hn)⟩) m
    refine Or.inr ⟨N₂, e₂, ?_⟩
    by_cases f₂ : FullDs ds₂
    · have hx : ∃ x, den v₁ x := Classical.byContradiction fun nx => hb.2 ⟨fun s _ => by
          cases o : w (.atom s) with
          | none => exact Or.inl rfl
          | some x => exact Or.inr ⟨x, rfl, fun hx => nx ⟨x, hx⟩⟩, fun _ _ h => h.elim⟩
      refine Or.inl ⟨f₂, vne hx, boxD_mono hM hS (fun _ h => h.elim) hv hb.1, fun e => hb.2 ⟨fun s _ => ?_,
        fun _ _ h => h.elim⟩⟩
      rw [e]; exact Or.inl rfl
    · exact Or.inr ⟨f₂, Or.inl (boxP_mono hM hS (fun _ h => h) hv hb)⟩
  · exact domPart hk hx hc

theorem mapsD_cases {R : List (Term × Term)} {S : MW V → Prop} (h : MapsD E den R S) :
    (R = [] ∧ ∀ w, ¬S w) ∨ ∃ c, R ≠ [] ∧ mapLookup R (.atom "map") = some c ∧ MField E c ∧
      ∀ w, denMF E den c w = Bool.true ↔ S w := by
  cases R with
  | nil => exact Or.inl ⟨rfl, fun w hw => by obtain ⟨c, hc, -⟩ := (h.2.2 w).mpr hw; simp [mapLookup] at hc⟩
  | cons e R =>
    have he := h.1 e.1 (by simp [mapLookup, compareExact_self])
    obtain ⟨k, c⟩ := e
    simp only at he; subst he
    have lc : mapLookup ((Term.atom "map", c) :: R) (.atom "map") = some c := by simp [mapLookup, compareExact_self]
    exact Or.inr ⟨c, by simp, lc, h.2.1 c lc, fun w => ⟨fun hw => (h.2.2 w).mp ⟨c, lc, hw⟩,
      fun hw => by obtain ⟨c', hc', hw'⟩ := (h.2.2 w).mpr hw; rw [lc] at hc'; cases hc'; exact hw'⟩⟩

theorem filter_eq_single {a : String} : ∀ {l : List String}, l.Nodup → a ∈ l → l.filter (· = a) = [a]
  | [], _, h => by simp at h
  | b :: l, nd, h => by
    rw [List.nodup_cons] at nd
    by_cases e : b = a
    · subst e
      have : l.filter (· = b) = [] := List.filter_eq_nil_iff.mpr fun x mx => by
        simp only [decide_eq_true_eq]; rintro rfl; exact nd.1 mx
      simp [this]
    · have m : a ∈ l := by simpa [Ne.symm e] using h
      simp [e, filter_eq_single nd.2 m]

/-- The result of `map_update_box/5` as a type holding only maps. -/
theorem mapsD_box {res : Term} {S : MW V → Prop}
    (h : (res = .map [] ∧ ∀ w, ¬S w) ∨ ∃ c o, res = .map [(.atom "map", c), (.atom "map", o)] ∧ MField E c ∧
      ∀ w, denMF E den c w = Bool.true ↔ S w) : ∃ R, res = .map R ∧ MapsD E den R S := by
  rcases h with ⟨rfl, emp⟩ | ⟨c, o, rfl, fc, sc⟩
  · exact ⟨[], rfl, mapsD_nil emp⟩
  · refine ⟨_, rfl, fun q hq => ?_, fun c' hc => ?_, fun w => ?_⟩
    · by_cases e : q = .atom "map"
      · exact e
      · simp [mapLookup] at hq; exact hq
    · simp [mapLookup] at hc; subst hc; exact fc
    · simp only [mapLookup, List.find?_cons, compareExact_self, decide_true, Option.map_some, Option.some.injEq,
        exists_eq_left']
      exact sc w

/-- The maps of the updates `map_update_static_dnf/6` makes with keys outside a negated set of atoms. -/
def NegSem (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (ds : List Term) (v : Term) (w : MW V) : Prop :=
  (FullDs ds ∧ BoxD den M S (fun d => .atom d ∈ ds) v w ∧ w ≠ wNone) ∨
    (¬FullDs ds ∧ (BoxP den M S (fun _ => False) v w ∨
      ((∃ k, .atom (domKind k) ∈ ds) ∧ DomC den M (dsStrs ds) v w)))

/-- `map_update_static_dnf/6` putting a non-empty static value at the atoms outside a negated set and the domains. -/
theorem neg_static_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ []) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (N : List (Term × Term))
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (hks : ∀ s ∈ ks, mapLookup N (.atom s) = none)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks)
    (ds : List Term) (hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) (hat : .atom "atom" ∈ ds) :
    ∃ Y, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT [] (.map N) ds) (forceOp v) (.atom "false") (.atom "true") =
        .ok (.tuple #[.map [], Y, .nil, .atom "true"]) ∧
      ((Y = .map [] ∧ ∀ w, ¬NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w) ∨
        ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔
          NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w) := by
  have keysN := setStrs_keys hNa
  obtain ⟨R', rR', -, mR'⟩ := usort_atoms (ks.map Term.atom ++ (setStrs N).map Term.atom) (fun k mk => by
    rcases List.mem_append.mp mk with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;> exact ⟨s, rfl⟩)
  obtain ⟨AK, rfl⟩ : ∃ AK : List String, R' = AK.map Term.atom := by
    have aR : ∀ r ∈ R', ∃ s, r = .atom s := fun r mr => by
      rcases List.mem_append.mp ((mR' r).mp mr) with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;>
        exact ⟨s, rfl⟩
    clear rR' mR'
    induction R' with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := aR r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => aR x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  have hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ setStrs N := fun s => by
    have := mR' (.atom s); simp at this; exact this
  obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort ds hds
  have appNil : ∀ a : List Term, Erlang.erlang.«++/2» (Term.list a) .nil = .ok (Term.list a) := fun a => by
    simpa using append_list a []
  have dsNe : Erlang.erlang.«/=/2» (Term.list ds) .nil = .ok (.atom "true") := by
    cases ds with
    | nil => simp at hat
    | cons d ds => simp [Term.list, Erlang.erlang.«/=/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«--/2»,
    Erlang.erlang.«not/1», Term.properList?, Erlang.sets.«to_list/1»,
    Erlang.maps.«keys/1», keysN, appNil, append_list, rR', rKs]
  have dsCmp : Term.compare ((Term.list ds).fuel .nil) (Term.list ds) .nil ≠ .eq := by
    cases ds with
    | nil => simp at hat
    | cons d ds => rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep]
  have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
    simpa using length_list (Ks.map Term.atom)
  have aK : "atom" ∈ Ks := (mKs _).mpr hat
  have none0 : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) acc
      (Term.list lines) (Term.list []) (forceOp v) (.atom "true") (.atom "true") (.atom "false") (.atom "true") =
      .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»,
      Lynx.Except.orElse]
  have runs := named_keys_skip (n + 5) lines (ks.map Term.atom) (v := v)
  have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
  have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
    (lnKS L mL s h).imp setStrs_mem.mpr id
  simp [dsCmp, lenK]
  by_cases full : FullDs ds
  · have hL : Ks.length = 12 := lenKs.mpr full
    have hL' : ((Ks.length : Int) = 12) := by omega
    obtain ⟨NK, R, rR, akNK, lnNK, orNK, mR⟩ := box_runAll ef (n := n + 2) (by omega) lines hl hne hv vne ks AK Ks
      subKs aK hL
    simp [hL', rR, Erlang.erlang.«element/2»]
    have bridge : ∀ w, (BoxSynD den lines ks NK Ks v w ∧ w ≠ wNone) ↔
        NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w := fun w => by
      rw [boxSynD_iff ef lines hl hne v (setStrs N) ks AK NK Ks aK hks' hAK akNK lnNK orNK lnKS' w]
      have eq : (fun d => d ∈ Ks) = (fun d => Term.atom d ∈ ds) := funext fun d => propext (mKs d)
      simp only [NegSem, full, true_and, not_true_eq_false, false_and, or_false, eq]
    rcases mapsD_cases mR with ⟨rfl, emp⟩ | ⟨c, ne, lc, fc, sc⟩
    · refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w h => emp w ?_⟩⟩
      · simp [none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]
      · exact (bridge w).mpr h
    · by_cases bot : c = .atom "bdd_bot"
      · subst bot
        refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w h => ?_⟩⟩
        · simp [ne, getMapKeys_single, lc, none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]
        · have := (sc w).mpr ((bridge w).mpr h); simp [denMF_bot] at this
      · refine ⟨.map [(.atom "map", c)], ?_, Or.inr ⟨c, rfl, fc, fun w => (sc w).trans ?_⟩⟩
        · simp [ne, getMapKeys_single, lc, none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]
        · exact bridge w
  · have hL : Ks.length ≠ 12 := fun h => full (lenKs.mp h)
    have hL' : ¬((Ks.length : Int) = 12) := by omega
    let Ws := Ks.filter (· ≠ "atom")
    have mWs : ∀ s, s ∈ Ws ↔ s ∈ Ks ∧ s ≠ "atom" := fun s => by simp [Ws]
    have part := partition_atom (n + 5) Ks
    rw [filter_eq_single ndKs aK] at part
    obtain ⟨NK, res, rres, akNK, lnNK, orNK, hres⟩ := box_runD ef (n := n + 2) (by omega) lines hl hne hv sv vne ks AK
      ["atom"] (by simp [domainKinds]) (by simp) (by simp)
    obtain ⟨R₁, rfl, m₁⟩ := mapsD_box hres
    simp only [List.map, Term.list] at rres
    -- The box at atoms is the box updating no other kind.
    have semBox : ∀ w, (BoxSynD den lines ks NK ["atom"] v w ∧ ¬UnsetSemD den ks AK ["atom"] v w) ↔
        BoxP den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (fun _ => False) v w := fun w => by
      rw [boxSynD_iff ef lines hl hne v (setStrs N) ks AK NK ["atom"] (by simp) hks' hAK akNK lnNK orNK lnKS' w,
        unsetSemD_iff den v (setStrs N) ks AK ["atom"] (by simp) hks' hAK w]
      have nk : ∀ k : Fin 11, (domKind k ∈ ["atom"]) ↔ False := fun k => by simp [domKind_ne_atom k]
      simp only [BoxP, BoxD, UnsetD, nk]
    have kindsWs : ∀ k : Fin 11, domKind k ∈ Ws ↔ domKind k ∈ dsStrs ds := fun k => by
      rw [mWs, mKs, dsStrs_mem]; simp [domKind_ne_atom k]
    by_cases wn : Ws = []
    · have noK : ¬∃ k, .atom (domKind k) ∈ ds := fun ⟨k, hk⟩ => by
        have := (kindsWs k).mpr (dsStrs_mem.mpr hk); rw [wn] at this; simp at this
      have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by
        have := wn; simp only [Ws] at this; simpa using this
      simp [hL', part, rres, wn', Erlang.erlang.«element/2»]
      have MM := m₁
      have bridge : ∀ w, (BoxSynD den lines ks NK ["atom"] v w ∧ ¬UnsetSemD den ks AK ["atom"] v w) ↔
          NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w := fun w => by
        rw [semBox w]; simp [NegSem, full, noK]
      rcases mapsD_cases MM with ⟨rfl, emp⟩ | ⟨c, ne, lc, fc, sc⟩
      · refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w h => emp w ((bridge w).mpr h)⟩⟩
        simp [none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]
      · by_cases bot : c = .atom "bdd_bot"
        · subst bot
          refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w h => ?_⟩⟩
          · simp [ne, getMapKeys_single, lc, none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]
          · have := (sc w).mpr ((bridge w).mpr h); simp [denMF_bot] at this
        · refine ⟨.map [(.atom "map", c)], ?_, Or.inr ⟨c, rfl, fc, fun w => (sc w).trans (bridge w)⟩⟩
          simp [ne, getMapKeys_single, lc, none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]
    · have hD' : ∀ d ∈ Ws, d ∈ domainKinds := fun d md => subKs d ((mWs d).mp md).1
      have hA' : "atom" ∉ Ws := fun m => ((mWs _).mp m).2 rfl
      obtain ⟨R₂, rW, m₂⟩ := widen_run ef (n := n + 1) (by omega) hv vne Ws hA' hD' wn lines fun L mL => (hl L mL).1
      obtain ⟨U, rU, MM⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) m₁ m₂
      have wsCmp : Term.compare ((Term.list (Ws.map Term.atom)).fuel .nil) (Term.list (Ws.map Term.atom)) .nil ≠ .eq := by
        cases h : Ws with
        | nil => exact absurd h wn
        | cons d ds => rw [Lynx.Term.compare_step]; simp [Term.list, Lynx.Term.Compare.compareStep]
      simp [hL', part, rres, Erlang.erlang.«element/2»]
      simp [Ws] at wsCmp rW
      simp [wsCmp, rW, rU]
      have someK : ∃ k, .atom (domKind k) ∈ ds := by
        obtain ⟨d, md⟩ := List.exists_mem_of_ne_nil _ wn
        obtain ⟨k, rfl⟩ := domKind_of (hD' d md) ((mWs d).mp md).2
        exact ⟨k, dsStrs_mem.mp ((kindsWs k).mp md)⟩
      have bridge : ∀ w, ((BoxSynD den lines ks NK ["atom"] v w ∧ ¬UnsetSemD den ks AK ["atom"] v w) ∨
          ((∃ L ∈ lines, WLine den L Ws v w) ∧ w ≠ wNone)) ↔
          NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w := fun w => by
        rw [semBox w, wlines_domc ef (fun L mL => (hl L mL).1) hA' hD' w]
        simp only [NegSem, full, false_and, false_or, not_false_eq_true, true_and, someK]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (domC_mono_k (fun u h => h) (fun k m => (kindsWs k).mp m) (fun x h => h) h)
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (domC_mono_k (fun u h => h) (fun k m => (kindsWs k).mpr m) (fun x h => h) h)
      rcases mapsD_cases MM with ⟨rfl, emp⟩ | ⟨c, ne, lc, fc, sc⟩
      · refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w h => emp w ((bridge w).mpr h)⟩⟩
        simp [none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]
      · by_cases bot : c = .atom "bdd_bot"
        · subst bot
          refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w h => ?_⟩⟩
          · simp [ne, getMapKeys_single, lc, none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]
          · have := (sc w).mpr ((bridge w).mpr h); simp [denMF_bot] at this
        · refine ⟨.map [(.atom "map", c)], ?_, Or.inr ⟨c, rfl, fc, fun w => (sc w).trans (bridge w)⟩⟩
          simp [ne, getMapKeys_single, lc, none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]


/-- The maps of the updates `map_update_static_dnf/6` makes with a finite set of atoms and some kinds. -/
def FinSem (den : Term → V → Prop) (M : MW V → Prop) (A : List String) (ds : List Term) (v : Term) (w : MW V) : Prop :=
  UnionS den M (fun a => .atom a ∈ A.map Term.atom) v w ∨
    ((∃ k, .atom (domKind k) ∈ ds) ∧ DomC den M (dsStrs ds) v w)

/-- `map_update_static_dnf/6` putting a non-empty static value at a finite set of atoms and some kinds. -/
theorem fin_static_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (A : List String) (bdd : Term)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (ds : List Term) (hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) (hna : .atom "atom" ∉ ds) :
    ∃ Y f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (A.map Term.atom) (.atom "nil") ds) (forceOp v) (.atom "false") (.atom "true") =
        .ok (.tuple #[.map [], Y, .nil, f]) ∧
      (f = .atom "true" ∨ ∀ w, ¬FinSem den (fun u => ∃ L ∈ lines, InMLine den L u) A ds v w) ∧
      ((Y = .map [] ∧ ∀ w, ¬FinSem den (fun u => ∃ L ∈ lines, InMLine den L u) A ds v w) ∨
        ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔
          FinSem den (fun u => ∃ L ∈ lines, InMLine den L u) A ds v w) := by
  have nk₂ : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) acc (Term.list lines) .nil
      (forceOp v) (.atom "false") (.atom "true") (.atom "false") (.atom "true") = .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have appNil0 : Erlang.erlang.«++/2» Term.nil Term.nil = .ok .nil := by simp [Erlang.erlang.«++/2»]
  have e0 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => compareExact (x.fuel y) x y == .eq) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have nil' : Term.list ([] : List Term) = .nil := rfl
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [splitT, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«==/2», Erlang.erlang.«/=/2»,
    Lynx.Term.isMember, Erlang.erlang.«--/2», Erlang.erlang.«not/1», Term.properList?]
  simp only [e0, nil', appNil0, Lynx.Except.ok_bind]
  have M : ∀ (bs : List Term), (∀ b ∈ bs, MField E b) → ∃ r, Elixir.Module.Types.Descr.«map_union_all/1» (D (n + 6))
      (Term.list bs) = .ok r ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔ ∃ b ∈ bs, denMF E den b w = Bool.true :=
    fun bs fb => by
      obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 6) (by omega) (ok := fun _ => True)
        (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bs (Nat.le_refl _) fun b mb => ⟨fb b mb, by
          rcases fb b mb with ⟨k, rfl⟩ | wb
          · exact Or.inl ⟨k, rfl⟩
          · exact Or.inr (wb.mono fun _ _ => trivial)⟩
      exact ⟨r, rr, fr, sr⟩
  -- The puts at the atoms.
  have unionSem : ∀ w, (∃ a ∈ A, PutAt den v a w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w)) ↔
      UnionS den (fun u => ∃ L ∈ lines, InMLine den L u) (fun a => .atom a ∈ A.map Term.atom) v w := fun w => by
    simp only [UnionS, List.mem_map, Term.atom.injEq, exists_eq_right]
    constructor
    · rintro ⟨a, ma, p, L, mL, o, h⟩; exact ⟨a, ma, p, o, L, mL, h⟩
    · rintro ⟨a, ma, p, o, L, mL, h⟩; exact ⟨a, ma, p, L, mL, o, h⟩
  have appDs : Erlang.erlang.«++/2» (Term.list ds) .nil = .ok (Term.list ds) := by simpa using append_list ds []
  have UN := union_named ef (n := n + 2) (by omega) hv lines hl A
  by_cases dn : ds = []
  · subst dn
    obtain ⟨bs, rbs, fbs, sbs⟩ := UN [] Bool.false
    simp only [List.append_nil] at rbs
    obtain ⟨r, rr, fr, sr⟩ := M bs fbs
    have rbs' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[.map [], .nil, .nil,
        .atom "false"]) (Term.list lines) (Term.list (A.map Term.atom)) (forceOp v) (.atom "true") (.atom "true")
        (.atom "false") (.atom "true") = .ok (.tuple #[.map [], Term.list bs, .nil, boolAtom (!A.isEmpty)]) := by
      simpa [Term.list, boolAtom] using rbs
    have noK : ¬∃ k, Term.atom (domKind k) ∈ ([] : List Term) := by simp
    have sem : ∀ w, denMF E den r w = Bool.true ↔ FinSem den (fun u => ∃ L ∈ lines, InMLine den L u) A [] v w :=
      fun w => by rw [sr, sbs, unionSem]; simp [FinSem]
    have fF : boolAtom (!A.isEmpty) = .atom "true" ∨
        ∀ w, ¬FinSem den (fun u => ∃ L ∈ lines, InMLine den L u) A [] v w := by
      cases A with
      | nil =>
        right; intro w h
        rcases h with ⟨a, ha, -⟩ | ⟨⟨k, hk⟩, -⟩
        · simp at ha
        · simp at hk
      | cons a A => left; rfl
    simp [appDs, Term.list, rbs', nk₂, rr]
    by_cases bot : r = .atom "bdd_bot"
    · subst bot
      exact ⟨.map [], _, rfl, fF, Or.inl ⟨rfl, fun w h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩⟩
    · refine ⟨.map [(.atom "map", r)], boolAtom (!A.isEmpty), ?_, fF, Or.inr ⟨r, rfl, fr, sem⟩⟩
      split
      · exact absurd rfl bot
      · rfl
  · obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort ds hds
    have hA : "atom" ∉ Ks := fun m => hna ((mKs _).mp m)
    have neK : Ks ≠ [] := by
      obtain ⟨d, md⟩ := List.exists_mem_of_ne_nil _ dn
      obtain ⟨s, -, rfl⟩ := hds d md
      exact List.ne_nil_of_mem ((mKs s).mpr md)
    have someK : ∃ k, Term.atom (domKind k) ∈ ds := by
      obtain ⟨d, md⟩ := List.exists_mem_of_ne_nil _ dn
      obtain ⟨s, ms, rfl⟩ := hds d md
      obtain ⟨k, rfl⟩ := domKind_of ms fun e => hna (e ▸ md)
      exact ⟨k, md⟩
    have kindsK : ∀ k : Fin 11, domKind k ∈ Ks ↔ domKind k ∈ dsStrs ds := fun k => by rw [mKs, dsStrs_mem]
    obtain ⟨R, rW, mR⟩ := widen_run ef (n := n + 1) (by omega) hv vne Ks hA subKs neK lines fun L mL => (hl L mL).1
    have dsCmp : Term.compare ((Term.list ds).fuel .nil) (Term.list ds) .nil ≠ .eq := by
      cases ds with
      | nil => exact absurd rfl dn
      | cons d ds => rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep]
    have domSem : ∀ w, ((∃ L ∈ lines, WLine den L Ks v w) ∧ w ≠ wNone) ↔
        DomC den (fun u => ∃ L ∈ lines, InMLine den L u) (dsStrs ds) v w := fun w => by
      rw [wlines_domc ef (fun L mL => (hl L mL).1) hA subKs w]
      exact ⟨domC_mono_k (fun u h => h) (fun k m => (kindsK k).mp m) (fun x h => h),
        domC_mono_k (fun u h => h) (fun k m => (kindsK k).mpr m) (fun x h => h)⟩
    simp [appDs, dsCmp, rKs, rW]
    rcases mapsD_cases mR with ⟨rfl, emp⟩ | ⟨c, ne, lc, fc, sc⟩
    · obtain ⟨bs, rbs, fbs, sbs⟩ := UN [] Bool.true
      simp only [List.append_nil] at rbs
      obtain ⟨r, rr, fr, sr⟩ := M bs fbs
      have rbs' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[.map [], .nil, .nil,
          .atom "true"]) (Term.list lines) (Term.list (A.map Term.atom)) (forceOp v) (.atom "true") (.atom "true")
          (.atom "false") (.atom "true") = .ok (.tuple #[.map [], Term.list bs, .nil, .atom "true"]) := by
        simpa [Term.list, boolAtom] using rbs
      have sem : ∀ w, denMF E den r w = Bool.true ↔ FinSem den (fun u => ∃ L ∈ lines, InMLine den L u) A ds v w :=
        fun w => by
          rw [sr, sbs, unionSem]
          simp only [FinSem, someK, true_and]
          exact ⟨Or.inl, fun h => h.elim id fun h' => absurd ((domSem w).mpr h') (emp w)⟩
      simp [rbs', nk₂, rr]
      by_cases bot : r = .atom "bdd_bot"
      · subst bot
        exact ⟨.map [], _, rfl, Or.inl rfl, Or.inl ⟨rfl, fun w h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩⟩
      · refine ⟨.map [(.atom "map", r)], .atom "true", ?_, Or.inl rfl, Or.inr ⟨r, rfl, fr, sem⟩⟩
        split
        · exact absurd rfl bot
        · rfl
    · obtain ⟨bs, rbs, fbs, sbs⟩ := UN [c] Bool.true
      obtain ⟨r, rr, fr, sr⟩ := M (bs ++ [c]) fun b mb => by
        rcases List.mem_append.mp mb with mb | mb
        · exact fbs b mb
        · simp at mb; subst mb; exact fc
      have rbs' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[.map [], Term.list [c],
          .nil, .atom "true"]) (Term.list lines) (Term.list (A.map Term.atom)) (forceOp v) (.atom "true") (.atom "true")
          (.atom "false") (.atom "true") = .ok (.tuple #[.map [], Term.list (bs ++ [c]), .nil, .atom "true"]) := by
        simpa [boolAtom] using rbs
      have sem : ∀ w, denMF E den r w = Bool.true ↔ FinSem den (fun u => ∃ L ∈ lines, InMLine den L u) A ds v w :=
        fun w => by
          rw [sr]
          simp only [FinSem, someK, true_and, List.mem_append, List.mem_singleton]
          rw [← unionSem, ← sbs, ← domSem, ← sc]
          constructor
          · rintro ⟨b, mb | rfl, hb⟩
            · exact Or.inl ⟨b, mb, hb⟩
            · exact Or.inr hb
          · rintro (⟨b, mb, hb⟩ | hb)
            · exact ⟨b, Or.inl mb, hb⟩
            · exact ⟨c, Or.inr rfl, hb⟩
      have ne' : Term.compare ((Term.map R).fuel (.map [])) (.map R) (.map []) ≠ .eq := by
        rw [ne_eq, Lynx.Term.compare_map_empty]; simpa using ne
      simp [ne, getMapKeys_single, lc, rbs', nk₂, rr]
      by_cases bot : r = .atom "bdd_bot"
      · subst bot
        exact ⟨.map [], _, rfl, Or.inl rfl, Or.inl ⟨rfl, fun w h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩⟩
      · refine ⟨.map [(.atom "map", r)], .atom "true", ?_, Or.inl rfl, Or.inr ⟨r, rfl, fr, sem⟩⟩
        split
        · exact absurd rfl bot
        · rfl

/-- `map_update_box/5` putting an empty value updates nothing. -/
theorem box_run_empty (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) {v : Term} (hv : E v) (nv : ¬∃ x, den v x)
    (ks AK Ds : List String) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    Elixir.Module.Types.Descr.«map_update_box/5» (D (n + 4)) (Term.list lines) (Term.list (ks.map Term.atom))
      (Term.list (Ds.map Term.atom)) (forceOp v) (Term.list (AK.map Term.atom)) = .ok (.map []) := by
  have hl' : ∀ L ∈ lines, MLine E L := fun L m => (hl L m).1
  obtain ⟨X, NK, rX, rNK, ndNK, -, -, -, -⟩ := box_named (E := E) (n + 1) lines hl' AK
  obtain ⟨P, Q, rPQ, -, -, uQ, -, -, -⟩ := box_fields ef hn lines hl hv ks NK ndNK
  obtain ⟨Q', rQ', subQ', -, newQ'⟩ := box_filter ef (m := n + 3) (by omega) Q uQ
  obtain ⟨T, U, rTU, -, -, -, neU⟩ := box_domainsD ef (n := n + 3) (by omega) lines hl' hv Ds hD
  have q0 : Q' = [] := by
    cases Q' with
    | nil => rfl
    | cons q _ =>
      exfalso
      obtain ⟨o, ho⟩ := newQ' q List.mem_cons_self
      obtain ⟨s, -, old, new, rfl, -, -, -, snew⟩ := uQ q (subQ'.subset List.mem_cons_self)
      obtain ⟨⟨x, -, hx⟩, -⟩ := (snew o).mp (by simpa [updNew] using ho)
      exact nv ⟨x, hx⟩
  have u0 : U = [] := Classical.byContradiction fun h => nv (neU.mp h).2
  subst q0 u0
  unfold Elixir.Module.Types.Descr.«map_update_box/5»
  have rTU' := rTU
  simp only [domainKinds, List.map] at rTU'
  simp [rX, rNK, rPQ, rQ', rTU', Lynx.Except.andAlso, Term.list, Erlang.erlang.«==/2»]


/-- `map_update_static_dnf/6` putting an empty value at the atoms outside a negated set: no map. -/
theorem neg_static_dnf_empty (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) {v : Term} (hv : E v) (nv : ¬∃ x, den v x)
    (N : List (Term × Term)) (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (ds : List Term) (hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) (hat : .atom "atom" ∈ ds) :
    ∃ Y, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT [] (.map N) ds) (forceOp v) (.atom "false") (.atom "true") =
        .ok (.tuple #[.map [], Y, .nil, .atom "true"]) ∧
      (Y = .map [] ∨ ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.false) := by
  have keysN := setStrs_keys hNa
  obtain ⟨R', rR', -, mR'⟩ := usort_atoms (ks.map Term.atom ++ (setStrs N).map Term.atom) (fun k mk => by
    rcases List.mem_append.mp mk with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;> exact ⟨s, rfl⟩)
  obtain ⟨AK, rfl⟩ : ∃ AK : List String, R' = AK.map Term.atom := by
    have aR : ∀ r ∈ R', ∃ s, r = .atom s := fun r mr => by
      rcases List.mem_append.mp ((mR' r).mp mr) with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;>
        exact ⟨s, rfl⟩
    clear rR' mR'
    induction R' with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := aR r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => aR x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort ds hds
  have appNil : ∀ a : List Term, Erlang.erlang.«++/2» (Term.list a) .nil = .ok (Term.list a) := fun a => by
    simpa using append_list a []
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«--/2»,
    Erlang.erlang.«not/1», Term.properList?, Erlang.sets.«to_list/1»,
    Erlang.maps.«keys/1», keysN, appNil, append_list, rR', rKs]
  have dsCmp : Term.compare ((Term.list ds).fuel .nil) (Term.list ds) .nil ≠ .eq := by
    cases ds with
    | nil => simp at hat
    | cons d ds => rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep]
  have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
    simpa using length_list (Ks.map Term.atom)
  have none0 : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) acc
      (Term.list lines) (Term.list []) (forceOp v) (.atom "true") (.atom "true") (.atom "false") (.atom "true") =
      .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»,
      Lynx.Except.orElse]
  have runs := named_keys_skip (n + 5) lines (ks.map Term.atom) (v := v)
  have box := fun Ds hD => box_run_empty ef (n := n + 2) (by omega) lines hl hv nv ks AK Ds hD
  simp [dsCmp, lenK]
  by_cases full : FullDs ds
  · have hL' : ((Ks.length : Int) = 12) := by have := lenKs.mpr full; omega
    have MM : MapsD E den [] (fun _ => False) := mapsD_nil fun _ h => h
    simp [hL', box Ks subKs, Erlang.erlang.«element/2»]
    exact ⟨.map [], by simp [none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list], Or.inl rfl⟩
  · have hL' : ¬((Ks.length : Int) = 12) := by
      intro h; exact full (lenKs.mp (by omega))
    let Ws := Ks.filter (· ≠ "atom")
    have part := partition_atom (n + 5) Ks
    rw [filter_eq_single ndKs ((mKs _).mpr hat)] at part
    have rb := box ["atom"] (by simp [domainKinds])
    simp only [List.map, Term.list] at rb
    by_cases wn : Ws = []
    · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by
        have := wn; simp only [Ws] at this; simpa using this
      have MM : MapsD E den [] (fun _ => False) := mapsD_nil fun _ h => h
      simp [hL', part, rb, wn', Erlang.erlang.«element/2»]
      exact ⟨.map [], by simp [none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list], Or.inl rfl⟩
    · obtain ⟨R₂, rW, m₂⟩ := widen_run_empty ef (n := n + 1) (by omega) hv nv Ws lines fun L mL => (hl L mL).1
      obtain ⟨U, rU, MM'⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) (mapsD_nil (S := fun _ => False)
        fun _ h => h) m₂
      have MM : MapsD E den U (fun _ => False) := ⟨MM'.1, MM'.2.1, fun w => (MM'.2.2 w).trans (by simp)⟩
      have wsCmp : Term.compare ((Term.list (Ws.map Term.atom)).fuel .nil) (Term.list (Ws.map Term.atom)) .nil ≠ .eq := by
        cases h : Ws with
        | nil => exact absurd h wn
        | cons d ds => rw [Lynx.Term.compare_step]; simp [Term.list, Lynx.Term.Compare.compareStep]
      simp [hL', part, rb, Erlang.erlang.«element/2»]
      simp [Ws] at wsCmp rW
      simp [wsCmp, rW, rU]
      rcases mapsD_cases MM with ⟨rfl, -⟩ | ⟨c, ne, lc, fc, sc⟩
      · exact ⟨.map [], by simp [none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list], Or.inl rfl⟩
      · by_cases bot : c = .atom "bdd_bot"
        · subst bot
          exact ⟨.map [], by simp [ne, getMapKeys_single, lc, none0, runs, Elixir.Module.Types.Descr.«map_union_all/1»,
            Term.list], Or.inl rfl⟩
        · refine ⟨.map [(.atom "map", c)], ?_, Or.inr ⟨c, rfl, fc, fun w => Bool.eq_false_iff.mpr fun h => (sc w).mp h⟩⟩
          simp [ne, getMapKeys_single, lc, none0, runs, Elixir.Module.Types.Descr.«map_union_all/1», Term.list]


/-- `map_update_static_dnf/6` putting an empty value at a finite set of atoms and some kinds: no map. -/
theorem fin_static_dnf_empty (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (nv : ¬∃ x, den v x) (A : List String) (bdd : Term)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (ds : List Term) (hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) :
    ∃ Y f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (A.map Term.atom) (.atom "nil") ds) (forceOp v) (.atom "false") (.atom "true") =
        .ok (.tuple #[.map [], Y, .nil, f]) ∧
      (Y = .map [] ∨ ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.false) := by
  have nk₂ : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) acc (Term.list lines) .nil
      (forceOp v) (.atom "false") (.atom "true") (.atom "false") (.atom "true") = .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have appNil0 : Erlang.erlang.«++/2» Term.nil Term.nil = .ok .nil := by simp [Erlang.erlang.«++/2»]
  have e0 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => compareExact (x.fuel y) x y == .eq) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have nil' : Term.list ([] : List Term) = .nil := rfl
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [splitT, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«==/2», Erlang.erlang.«/=/2»,
    Lynx.Term.isMember, Erlang.erlang.«--/2», Erlang.erlang.«not/1», Term.properList?]
  simp only [e0, nil', appNil0, Lynx.Except.ok_bind]
  have M : ∀ (bs : List Term), (∀ b ∈ bs, MField E b) → ∃ r, Elixir.Module.Types.Descr.«map_union_all/1» (D (n + 6))
      (Term.list bs) = .ok r ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔ ∃ b ∈ bs, denMF E den b w = Bool.true :=
    fun bs fb => by
      obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 6) (by omega) (ok := fun _ => True)
        (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bs (Nat.le_refl _) fun b mb => ⟨fb b mb, by
          rcases fb b mb with ⟨k, rfl⟩ | wb
          · exact Or.inl ⟨k, rfl⟩
          · exact Or.inr (wb.mono fun _ _ => trivial)⟩
      exact ⟨r, rr, fr, sr⟩
  have appDs : Erlang.erlang.«++/2» (Term.list ds) .nil = .ok (Term.list ds) := by simpa using append_list ds []
  have UN := union_named ef (n := n + 2) (by omega) hv lines hl A
  have noPut : ∀ w, ¬∃ a ∈ A, PutAt den v a w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) :=
    fun w h => by obtain ⟨a, -, ⟨x, -, hx⟩, -⟩ := h; exact nv ⟨x, hx⟩
  by_cases dn : ds = []
  · subst dn
    obtain ⟨bs, rbs, fbs, sbs⟩ := UN [] Bool.false
    simp only [List.append_nil] at rbs
    obtain ⟨r, rr, fr, sr⟩ := M bs fbs
    have rbs' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[.map [], .nil, .nil,
        .atom "false"]) (Term.list lines) (Term.list (A.map Term.atom)) (forceOp v) (.atom "true") (.atom "true")
        (.atom "false") (.atom "true") = .ok (.tuple #[.map [], Term.list bs, .nil, boolAtom (!A.isEmpty)]) := by
      simpa [Term.list, boolAtom] using rbs
    have emp : ∀ w, denMF E den r w = Bool.false := fun w =>
      Bool.eq_false_iff.mpr fun h => noPut w ((sbs w).mp ((sr w).mp h))
    simp [appDs, Term.list, rbs', nk₂, rr]
    by_cases bot : r = .atom "bdd_bot"
    · subst bot; exact ⟨.map [], ⟨_, rfl⟩, Or.inl rfl⟩
    · refine ⟨.map [(.atom "map", r)], ⟨boolAtom (!A.isEmpty), ?_⟩, Or.inr ⟨r, rfl, fr, emp⟩⟩
      split
      · exact absurd rfl bot
      · rfl
  · obtain ⟨Ks, rKs, -, -, -, -⟩ := kinds_usort ds hds
    obtain ⟨R, rW, mR⟩ := widen_run_empty ef (n := n + 1) (by omega) hv nv Ks lines fun L mL => (hl L mL).1
    have dsCmp : Term.compare ((Term.list ds).fuel .nil) (Term.list ds) .nil ≠ .eq := by
      cases ds with
      | nil => exact absurd rfl dn
      | cons d ds => rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep]
    simp [appDs, dsCmp, rKs, rW]
    rcases mapsD_cases mR with ⟨rfl, -⟩ | ⟨c, ne, lc, fc, sc⟩
    · obtain ⟨bs, rbs, fbs, sbs⟩ := UN [] Bool.true
      simp only [List.append_nil] at rbs
      obtain ⟨r, rr, fr, sr⟩ := M bs fbs
      have rbs' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[.map [], .nil, .nil,
          .atom "true"]) (Term.list lines) (Term.list (A.map Term.atom)) (forceOp v) (.atom "true") (.atom "true")
          (.atom "false") (.atom "true") = .ok (.tuple #[.map [], Term.list bs, .nil, .atom "true"]) := by
        simpa [Term.list, boolAtom] using rbs
      have emp : ∀ w, denMF E den r w = Bool.false := fun w =>
        Bool.eq_false_iff.mpr fun h => noPut w ((sbs w).mp ((sr w).mp h))
      simp [rbs', nk₂, rr]
      by_cases bot : r = .atom "bdd_bot"
      · subst bot; exact ⟨.map [], ⟨_, rfl⟩, Or.inl rfl⟩
      · refine ⟨.map [(.atom "map", r)], ⟨.atom "true", ?_⟩, Or.inr ⟨r, rfl, fr, emp⟩⟩
        split
        · exact absurd rfl bot
        · rfl
    · obtain ⟨bs, rbs, fbs, sbs⟩ := UN [c] Bool.true
      obtain ⟨r, rr, fr, sr⟩ := M (bs ++ [c]) fun b mb => by
        rcases List.mem_append.mp mb with mb | mb
        · exact fbs b mb
        · simp at mb; subst mb; exact fc
      have rbs' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[.map [], Term.list [c],
          .nil, .atom "true"]) (Term.list lines) (Term.list (A.map Term.atom)) (forceOp v) (.atom "true") (.atom "true")
          (.atom "false") (.atom "true") = .ok (.tuple #[.map [], Term.list (bs ++ [c]), .nil, .atom "true"]) := by
        simpa [boolAtom] using rbs
      have emp : ∀ w, denMF E den r w = Bool.false := fun w => Bool.eq_false_iff.mpr fun h => by
        obtain ⟨b, mb, hb⟩ := (sr w).mp h
        rcases List.mem_append.mp mb with mb | mb
        · exact noPut w ((sbs w).mp ⟨b, mb, hb⟩)
        · simp at mb; subst mb; exact (sc w).mp hb
      have ne' : Term.compare ((Term.map R).fuel (.map [])) (.map R) (.map []) ≠ .eq := by
        rw [ne_eq, Lynx.Term.compare_map_empty]; simpa using ne
      simp [ne, getMapKeys_single, lc, rbs', nk₂, rr]
      by_cases bot : r = .atom "bdd_bot"
      · subst bot; exact ⟨.map [], ⟨_, rfl⟩, Or.inl rfl⟩
      · refine ⟨.map [(.atom "map", r)], ⟨.atom "true", ?_⟩, Or.inr ⟨r, rfl, fr, emp⟩⟩
        split
        · exact absurd rfl bot
        · rfl

theorem putSem_empty {M : MW V → Prop} {rs : List Term} {neg : Term} {ds : List Term} {v : Term}
    (nv : ¬∃ x, den v x) (w : MW V) : ¬PutSem den M rs neg ds v w := by
  rintro (⟨-, ⟨a, -, ⟨x, -, hx⟩, -⟩ | ⟨-, hx, -⟩⟩ | ⟨N, -, ⟨-, hx, -⟩ | ⟨-, hb | ⟨-, hx, -⟩⟩⟩)
  · exact nv ⟨x, hx⟩
  · exact nv hx
  · exact nv hx
  · exact hb.2 ⟨fun s _ => by
      cases o : w (.atom s) with
      | none => exact Or.inl rfl
      | some x => exact Or.inr ⟨x, rfl, fun hx => nv ⟨x, hx⟩⟩, fun _ _ h => h.elim⟩
  · exact nv hx

theorem putSem_fin {M : MW V → Prop} {A : List String} {ds : List Term} {v : Term} (vne : ∃ x, den v x)
    (w : MW V) : PutSem den M (A.map Term.atom) (.atom "nil") ds v w ↔ FinSem den M A ds v w := by
  simp only [PutSem, FinSem, true_and, vne]
  constructor
  · rintro (h | ⟨N, e, -⟩)
    · exact h
    · cases e
  · intro h; exact Or.inl h

theorem putSem_neg {M : MW V → Prop} {N : List (Term × Term)} {ds : List Term} {v : Term}
    (vne : ∃ x, den v x) (w : MW V) : PutSem den M [] (.map N) ds v w ↔ NegSem den M (setStrs N) ds v w := by
  simp only [PutSem, NegSem, vne, true_and]
  constructor
  · rintro (⟨e, -⟩ | ⟨N', e, h⟩)
    · cases e
    · cases e; exact h
  · intro h; exact Or.inr ⟨N, rfl, h⟩


/-- The puts of `map_update_static_dnf/6` on the lines of a type, for any split of static keys. -/
theorem dnf_put (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ []) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {rs : List Term} {neg : Term} {ds : List Term}
    (ok : SplitOk rs neg ds) (nr : ∀ N, neg = .map N → rs = [])
    (hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
      Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
        .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
      ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks) :
    ∃ Y f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT rs neg ds) (forceOp v) (.atom "false") (.atom "true") = .ok (.tuple #[.map [], Y, .nil, f]) ∧
      (f = .atom "true" ∨ ∀ w, ¬PutSem den (fun u => ∃ L ∈ lines, InMLine den L u) rs neg ds v w) ∧
      ((Y = .map [] ∧ ∀ w, ¬PutSem den (fun u => ∃ L ∈ lines, InMLine den L u) rs neg ds v w) ∨
        ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔
          PutSem den (fun u => ∃ L ∈ lines, InMLine den L u) rs neg ds v w) := by
  rcases ok.hneg with rfl | ⟨N, rfl⟩
  · obtain ⟨A, rfl⟩ : ∃ A : List String, rs = A.map Term.atom := by
      have := ok.hrs
      clear ok nr hneg
      induction rs with
      | nil => exact ⟨[], rfl⟩
      | cons r rs ih =>
        obtain ⟨s, rfl⟩ := this r List.mem_cons_self
        obtain ⟨B, rfl⟩ := ih fun x mx => this x (List.mem_cons_of_mem _ mx)
        exact ⟨s :: B, rfl⟩
    have hna : .atom "atom" ∉ ds := fun m => by obtain ⟨N, e⟩ := ok.hatom.mp m; cases e
    by_cases vne : ∃ x, den v x
    · obtain ⟨Y, f, run, hf, h⟩ := fin_static_dnf ef hn hv vne A bdd lines hl ds ok.hds hna
      refine ⟨Y, f, run, hf.imp id fun e w h => e w ((putSem_fin vne w).mp h), ?_⟩
      rcases h with ⟨rfl, emp⟩ | ⟨r, rfl, fr, sr⟩
      · exact Or.inl ⟨rfl, fun w h => emp w ((putSem_fin vne w).mp h)⟩
      · exact Or.inr ⟨r, rfl, fr, fun w => (sr w).trans (putSem_fin vne w).symm⟩
    · obtain ⟨Y, f, run, h⟩ := fin_static_dnf_empty ef hn hv vne A bdd lines hl ds ok.hds
      refine ⟨Y, f, run, Or.inr (putSem_empty vne), ?_⟩
      rcases h with rfl | ⟨r, rfl, fr, sr⟩
      · exact Or.inl ⟨rfl, putSem_empty vne⟩
      · exact Or.inr ⟨r, rfl, fr, fun w => by rw [sr w]; simp [putSem_empty vne w]⟩
  · obtain rfl := nr N rfl
    have hat : .atom "atom" ∈ ds := ok.hatom.mpr ⟨N, rfl⟩
    obtain ⟨hNa, ks, hR, hks, lnKS⟩ := hneg N rfl
    by_cases vne : ∃ x, den v x
    · obtain ⟨Y, run, h⟩ := neg_static_dnf ef hn bdd lines hl hne hv sv vne N hNa ks hR hks lnKS ds ok.hds hat
      refine ⟨Y, _, run, Or.inl rfl, ?_⟩
      rcases h with ⟨rfl, emp⟩ | ⟨r, rfl, fr, sr⟩
      · exact Or.inl ⟨rfl, fun w h => emp w ((putSem_neg vne w).mp h)⟩
      · exact Or.inr ⟨r, rfl, fr, fun w => (sr w).trans (putSem_neg vne w).symm⟩
    · obtain ⟨Y, run, h⟩ := neg_static_dnf_empty ef hn bdd lines hl hv vne N hNa ks hR ds ok.hds hat
      refine ⟨Y, _, run, Or.inl rfl, ?_⟩
      rcases h with rfl | ⟨r, rfl, fr, sr⟩
      · exact Or.inl ⟨rfl, putSem_empty vne⟩
      · exact Or.inr ⟨r, rfl, fr, fun w => by rw [sr w]; simp [putSem_empty vne w]⟩


/-- Split terms that `map_update_static_dnf/6`, forcing a static value, updates with the maps `P` gives from the maps
of the lines and the value, given the keys outside the negated set `neg`, if any. -/
def DnfPuts (s neg : Term) (P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop) : Prop :=
  ∀ (nd : Term) (E : Term → Prop) (V : Type) (den : Term → V → Prop) (tl : V → Prop) (K : Nat),
    EF nd E V den tl K → ∀ {n : Nat}, K + 4 ≤ n → ∀ (bdd : Term) (lines : List Term),
    (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → lines ≠ [] → ∀ {v : Term}, E v →
    (v = .atom "term" ∨ ∃ Z, v = .map Z) →
    (∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
      Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
        .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
      ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks) →
    ∃ Y f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines) s (forceOp v)
        (.atom "false") (.atom "true") = .ok (.tuple #[.map [], Y, .nil, f]) ∧
      (f = .atom "true" ∨ ∀ w, ¬P den (fun u => ∃ L ∈ lines, InMLine den L u) v w) ∧
      ((Y = .map [] ∧ ∀ w, ¬P den (fun u => ∃ L ∈ lines, InMLine den L u) v w) ∨
        ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔
          P den (fun u => ∃ L ∈ lines, InMLine den L u) v w)

theorem dnfPuts_split {rs : List Term} {neg : Term} {ds : List Term} (ok : SplitOk rs neg ds)
    (nr : ∀ N, neg = .map N → rs = []) :
    DnfPuts (splitT rs neg ds) neg (fun den M v w => PutSem den M rs neg ds v w) :=
  fun _ _ _ _ _ _ ef {_} hn bdd lines hl hne {_} hv sv hneg => dnf_put ef hn bdd lines hl hne hv sv ok nr hneg

/-- `map_update_static/5` putting a static value at a split of keys `map_update_static_dnf/6` updates with `P`. -/
theorem dput_update_static_g {s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts s neg P) (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X) s
        (forceOp v) (.atom "false") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ Y f, res = .tuple #[.map [], Y, .nil, f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          (f = .atom "true" ∨ ∀ w, ¬P den (fun u => denMF E den b u = Bool.true) v w) ∧
          ((Y = .map [] ∧ ∀ w, ¬P den (fun u => denMF E den b u = Bool.true) v w) ∨
            ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔
              P den (fun u => denMF E den b u = Bool.true) v w)) := by
  -- For negated sets, the keys outside the set, and the literals of the field naming only those or the set's.
  have negInfo : ∀ N, neg = .map N → ∃ ks : List String,
      Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) b =
        .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
      ∀ wb : Bdd (MLit E) b, Bdd (fun t => MLit E t ∧ LitIn (fun s => mapLookup N (.atom s) ≠ none ∨ s ∈ ks) t) b := by
    intro N _
    obtain ⟨R, rR, hR, -⟩ := neg_keys (den := den) ef N (n + 5) fb
    obtain ⟨ks, rfl⟩ : ∃ ks : List String, R = ks.map Term.atom := by
      clear rR
      induction R with
      | nil => exact ⟨[], rfl⟩
      | cons r rs ih =>
        obtain ⟨s, rfl, -⟩ := hR r List.mem_cons_self
        obtain ⟨B, rfl⟩ := ih fun x mx => hR x (List.mem_cons_of_mem _ mx)
        exact ⟨s :: B, rfl⟩
    refine ⟨ks, rR, fun s ms => ?_, fun wb => ?_⟩
    · obtain ⟨s', e, h⟩ := hR _ (List.mem_map_of_mem ms); cases e; exact h
    · obtain ⟨R', rR', -, lits, -⟩ := neg_keys_lits (den := den) ef N (n + 5) wb
      have e : R' = ks.map Term.atom := list_inj (Except.ok.inj (rR'.symm.trans rR))
      subst e
      exact lits.mono fun t ⟨lt, it⟩ => ⟨lt, fun k tag l et s ms => (it k tag l et s ms).imp id (by simp)⟩
  -- The semantics over the field.
  have conv : ∀ {lines : List Term}, (∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) →
      (fun u => ∃ L ∈ lines, InMLine den L u) = (fun u => denMF E den b u = Bool.true) := fun h =>
    funext fun u => propext (h u).symm
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 6)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 6) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 6) (by omega) rfl g sl
          (negs := []) (by simp) fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      have inB : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔
          ∃ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], InMLine den L w := fun w => by
        rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
      have hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
          Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N)
            (.tuple #[.integer k, tag, fieldsTerm l]) = .ok (Term.list (ks.map Term.atom)) ∧
          (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧ ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], ∀ s,
            LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
        intro N eN
        obtain ⟨ks, hR, hks, litsQ⟩ := negInfo N eN
        have names : ∀ s ∈ keyStrs l, mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
          rcases fb with ⟨k', e'⟩ | wb
          · intro s ms
            obtain ⟨-, -, e₃⟩ := tuple3_inj e'
            have : l = [] := fieldsTerm_inj (l' := []) e₃
            subst this; simp [keyStrs] at ms
          · exact (Bdd.leaf_iff.mp (litsQ wb)).2 k tag l rfl
        refine ⟨hNa N eN, ks, hR, hks, fun L mL s ⟨tag', l', negs', e', h⟩ => ?_⟩
        rw [List.mem_singleton] at mL; subst mL
        obtain ⟨-, e₂, e₃⟩ := tuple3_inj e'
        rw [← fieldsTerm_inj e₂] at h
        rcases h with h | ⟨N', mN', -⟩
        · exact names s h
        · rw [← list_inj e₃] at mN'; simp at mN'
      obtain ⟨Y, f, rY, hf, hY⟩ := hP _ _ _ _ _ _ ef hn (.tuple #[.integer k, tag, fieldsTerm l]) _ hl (by simp) hv sv hneg
      rw [conv inB] at hY hf
      refine ⟨_, ?_, Or.inr ⟨Y, f, rfl, ⟨w₀, (sem w₀).mpr h₀⟩, hf, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      simpa [Term.list] using rY
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N', mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 6) (by omega) rfl g sl
            (negs := []) (by simp) run w ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
      (m := n + 6) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    have hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
        Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) b =
          .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
        ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
      intro N eN
      obtain ⟨ks, hR, hks, litsQ⟩ := negInfo N eN
      obtain ⟨lines', rl', nl'⟩ := dnf_neg_names (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
        (m := n + 6) (by omega) _ (litsQ wb)
      have e : lines' = lines := list_inj (Except.ok.inj (rl'.symm.trans rl))
      subst e
      exact ⟨hNa N eN, ks, hR, hks, nl'⟩
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      · cases h : denMF E den b w
        · rfl
        · simpa using (inB w).mp h
    | cons L rest =>
      obtain ⟨Y, f, rY, hf, hY⟩ := hP _ _ _ _ _ _ ef hn b (L :: rest) hl (by simp) hv sv hneg
      rw [conv inB] at hY hf
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨Y, f, rfl, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, hf, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY

/-- `map_update_static/5` putting a static value at a split of static keys. -/
theorem dput_update_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {rs : List Term} {neg : Term} {ds : List Term}
    (ok : SplitOk rs neg ds) (nr : ∀ N, neg = .map N → rs = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X) (splitT rs neg ds)
        (forceOp v) (.atom "false") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ Y f, res = .tuple #[.map [], Y, .nil, f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          (f = .atom "true" ∨ ∀ w, ¬PutSem den (fun u => denMF E den b u = Bool.true) rs neg ds v w) ∧
          ((Y = .map [] ∧ ∀ w, ¬PutSem den (fun u => denMF E den b u = Bool.true) rs neg ds v w) ∨
            ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔
              PutSem den (fun u => denMF E den b u = Bool.true) rs neg ds v w)) :=
  dput_update_static_g (P := fun den M v w => PutSem den M rs neg ds v w) (dnfPuts_split ok nr) hNa ef hn hv sv hb fb


section
variable {t : Term} {n : Nat}

/-- `map_update_unchecked/4` putting a static value at a split of static keys, in static types of the next level:
`:badmap` unless the type holds only maps, otherwise the puts at the split of its maps, or an error with none. -/
theorem dput_map_g {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts s neg P)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) (s)
        (forceOp v) (.atom "false") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, (res = .tuple #[.map [], .map Y, .nil] ∨ (∃ er, res = .tuple #[.atom "error", er]) ∧ Y = []) ∧
          MOnly t n X ∧ DE (level t n).E (.map Y) ∧ (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ P (level t n).den (MT t n X) v w) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 6))
      (.function "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure]
  cases hb : mapLookup X (.atom "map") with
  | none =>
    refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso, bad,
      Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
    obtain ⟨dR, sR⟩ := rest_map hX
    have rE := next_empty dR (m := k + 6) (by omega)
    have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have only : MOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmM X)) v) ∧
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), w, (mt w).mp hw⟩
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), w, (mt w).mpr hw⟩
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 6)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
      exact rE
    have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X :=
      funext fun u => propext (mt u).symm
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨Y, f, rfl, ⟨w₀, hw₀⟩, hf, hY⟩⟩ :=
        dput_update_static_g hP hNa (level t n).ef (n := k) (by omega) hv sv hb fb
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      simp only [conv] at hY hf
      have mOnly := only.mpr ⟨restE, w₀, hw₀⟩
      -- The error when nothing is found holds no map, as the puts hold none then.
      by_cases fe : f = .atom "false" ∨ f = .atom "nil"
      · have emp : ∀ w, ¬P (level t n).den (MT t n X) v w := by
          rcases hf with rfl | h
          · rcases fe with h | h <;> simp at h
          · exact h
        refine ⟨.tuple #[.atom "error", .nil], ?_, Or.inr ⟨[], Or.inr ⟨⟨_, rfl⟩, rfl⟩, mOnly, Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_,
          fun w => ?_⟩⟩
        · rcases fe with rfl | rfl <;> simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rw [denD_map] at hq
          simp [mapLookup, dn_none] at hq
        · simp only [MT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff]
          exact emp w
      · have fe' := not_or.mp fe
        have fm : Lynx.Term.isMember f [.atom "false", .atom "nil"] = .atom "false" := by
          simp [Lynx.Term.isMember, compareExact_eq_atom, fe'.1, fe'.2]
        rcases hY with ⟨rfl, emp⟩ | ⟨r, rfl, fr, sr⟩
        · refine ⟨_, ?_, Or.inr ⟨[], Or.inl rfl, mOnly, Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_, fun w => ?_⟩⟩
          · simp [key, mo, run, Lynx.Except.andAlso, fm]
          · rw [denD_map] at hq
            simp [mapLookup, dn_none] at hq
          · simp only [MT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff]
            exact emp w
        · refine ⟨_, ?_, Or.inr ⟨_, Or.inl rfl, mOnly, Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_, fun w => ?_⟩⟩
          · simp [key, mo, run, Lynx.Except.andAlso, fm]
          · rw [denD_map] at hq
            by_cases e : q.1.1 = "map"
            · exact e
            · simp [mapLookup, e, dn_none] at hq
          · rw [← sr]; simp [MT, mapLookup]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]

theorem dput_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {rs : List Term} {neg : Term} {ds : List Term}
    (ok : SplitOk rs neg ds) (nr : ∀ N, neg = .map N → rs = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) (splitT rs neg ds)
        (forceOp v) (.atom "false") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, (res = .tuple #[.map [], .map Y, .nil] ∨ (∃ er, res = .tuple #[.atom "error", er]) ∧ Y = []) ∧
          MOnly t n X ∧ DE (level t n).E (.map Y) ∧ (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutSem (level t n).den (MT t n X) rs neg ds v w) :=
  dput_map_g (P := fun den M v w => PutSem den M rs neg ds v w) hX hv sv (dnfPuts_split ok nr) hNa hm


/-- `map_put/3` of a static value at a static key type, in static types of the next level: `:badmap` unless the type
holds only maps, otherwise the puts at the split of the keys. -/
theorem dput {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key : Term} {rs : List Term} {neg : Term}
    {ds : List Term} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok (splitT rs neg ds))
    (ok : SplitOk rs neg ds) (nr : ∀ N, neg = .map N → rs = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none)
    (hm : (level t n).K + 26 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, res = .tuple #[.atom "ok", .map Y] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutSem (level t n).den (MT t n X) rs neg ds v w) := by
  have sv' : v = .atom "term" ∨ ∃ Z, v = .map Z := sv.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
  have shared : Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v =
      (do
        let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) (splitT rs neg ds)
          (forceOp v) (.atom "false")
        match r with
        | .tuple ⟨[_, d, _]⟩ => pure (.tuple #[.atom "ok", d])
        | .tuple ⟨[.atom "error", _]⟩ => pure (.tuple #[.atom "ok", .map []])
        | .atom "badmap" => pure (.atom "badmap")
        | x => .error (.error (.tuple #[.atom "case_clause", x]))) := by
    unfold Elixir.Module.Types.Descr.«map_put/3» Elixir.Module.Types.Descr.«map_put_shared/3»
    rcases sv with rfl | ⟨Z, rfl, sZ⟩
    · simp [hk]
      rfl
    · simp [hk, getMapKeys_single, sZ]
      rfl
  obtain ⟨res, run, ⟨rfl, h⟩ | ⟨Y, hr, h⟩⟩ := dput_map hX hv sv' ok nr hNa hm
  · exact ⟨_, by rw [shared, run]; rfl, Or.inl ⟨rfl, h⟩⟩
  · rcases hr with rfl | ⟨⟨er, rfl⟩, rfl⟩
    · exact ⟨_, by rw [shared, run]; rfl, Or.inr ⟨Y, rfl, h⟩⟩
    · exact ⟨_, by rw [shared, run]; rfl, Or.inr ⟨[], rfl, h⟩⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

/-- `atom_keys?/1` accepts only atom keys. -/
theorem atom_keys_atoms : ∀ (es : List (Term × Term)),
    «atom_keys?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true → ∀ e ∈ es, ∃ s, e.1 = .atom s
  | [], _ => by simp
  | ⟨k, w⟩ :: rest, h => by
    by_cases hw : w = .nil
    · subst hw
      simp only [List.map_cons, Term.list, «atom_keys?/1», Term.true, Lynx.Except.andAlso_eq_true] at h
      intro e me
      rcases List.mem_cons.mp me with rfl | me
      · cases k <;> simp [Erlang.erlang.«is_atom/1»] at h
        exact ⟨_, rfl⟩
      · exact atom_keys_atoms rest (by simpa [Term.true] using h.2) e me
    · exfalso
      rw [«atom_keys?/1».eq_def] at h
      simp only [List.map_cons, Term.list] at h
      split at h <;> simp_all [Term.true]

/-- The atom sets of the atom fields `valid_fields?/1` accepts hold atoms. -/
theorem valid_union_atoms {S : List (Term × Term)}
    (h : «valid_fields?/1» (Term.list [.tuple #[.atom "atom", .tuple #[.atom "union", .map S]]]) = .ok Term.true) :
    ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s := by
  simp only [Term.list, «valid_fields?/1», «atoms?/1», Erlang.maps.«to_list/1», Term.true,
    Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at h
  exact atom_keys_atoms _ (by simpa [Term.list, Term.true] using h.1.1)

theorem negatable_union_atoms {S : List (Term × Term)} {depth : Term}
    (h : «negatable_field?/2» (.tuple #[.atom "atom", .tuple #[.atom "union", .map S]]) depth = .ok Term.true) :
    ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s := by
  unfold «negatable_field?/2» «nested_field?/2» at h
  simp at h
  exact valid_union_atoms (by simpa [Term.list] using h)

theorem negatable_fields_union_atoms {depth : Term} : ∀ (es : List (Term × Term)),
    «negatable_fields?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true →
    ∀ S, (.atom "atom", .tuple #[.atom "union", .map S]) ∈ es → ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s
  | [], _ => by simp
  | ⟨k, w⟩ :: rest, h => by
    simp only [List.map_cons, Term.list, «negatable_fields?/2», Term.true, Lynx.Except.andAlso_eq_true] at h
    intro S mS
    rcases List.mem_cons.mp mS with e | mS
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact negatable_union_atoms h.1
    · exact negatable_fields_union_atoms rest h.2 S mS

theorem valid_negation_atoms {S : List (Term × Term)}
    (h : «valid_fields?/1» (Term.list [.tuple #[.atom "atom", .tuple #[.atom "negation", .map S]]]) = .ok Term.true) :
    ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s := by
  simp only [Term.list, «valid_fields?/1», «atoms?/1», Erlang.maps.«to_list/1», Term.true,
    Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at h
  exact atom_keys_atoms _ (by simpa [Term.list, Term.true] using h.1)

theorem negatable_negation_atoms {S : List (Term × Term)} {depth : Term}
    (h : «negatable_field?/2» (.tuple #[.atom "atom", .tuple #[.atom "negation", .map S]]) depth = .ok Term.true) :
    ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s := by
  unfold «negatable_field?/2» «nested_field?/2» at h
  simp at h
  exact valid_negation_atoms (by simpa [Term.list] using h)

theorem negatable_fields_negation_atoms {depth : Term} : ∀ (es : List (Term × Term)),
    «negatable_fields?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true →
    ∀ S, (.atom "atom", .tuple #[.atom "negation", .map S]) ∈ es → ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s
  | [], _ => by simp
  | ⟨k, w⟩ :: rest, h => by
    simp only [List.map_cons, Term.list, «negatable_fields?/2», Term.true, Lynx.Except.andAlso_eq_true] at h
    intro S mS
    rcases List.mem_cons.mp mS with e | mS
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact negatable_negation_atoms h.1
    · exact negatable_fields_negation_atoms rest h.2 S mS

/-- The negated atom sets of static types of the laws hold atoms. -/
theorem static_negation_atoms {Y : List (Term × Term)} {d t : Term}
    (h : «arrows_static?/2» (.map Y) (.tuple #[d, t]) = .ok (.atom "true")) :
    ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "negation", .map S]) →
      ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s := by
  intro S hS
  simp only [«arrows_static?/2», «opt_negatable?/2», «negatable?/2», Erlang.maps.«to_list/1»,
    Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at h
  have fields := negatable_fields_negation_atoms (depth := .tuple #[d, t]) (mapEntries Y)
    (by simpa [Term.true] using h.1.1)
  obtain ⟨p, mp, qp, ep⟩ := lookup_found _ _ _ (by rw [mapLookup_mapEntries]; exact hS)
  rw [atom_compareExact_eq] at qp
  obtain ⟨p₁, p₂⟩ := p
  simp only at qp ep
  subst qp ep
  exact fields S mp

/-- The atom unions of static types of the laws hold atoms. -/
theorem static_union_atoms {Y : List (Term × Term)} {d t : Term}
    (h : «arrows_static?/2» (.map Y) (.tuple #[d, t]) = .ok (.atom "true")) :
    ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s := by
  intro S hS q hq
  simp only [«arrows_static?/2», «opt_negatable?/2», «negatable?/2», Erlang.maps.«to_list/1»,
    Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at h
  have fields := negatable_fields_union_atoms (depth := .tuple #[d, t]) (mapEntries Y)
    (by simpa [Term.true] using h.1.1)
  obtain ⟨p, mp, qp, ep⟩ := lookup_found _ _ _ (by rw [mapLookup_mapEntries]; exact hS)
  rw [atom_compareExact_eq] at qp
  obtain ⟨p₁, p₂⟩ := p
  simp only at qp ep
  subst qp ep
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hq
  obtain ⟨e, me, qe, -⟩ := lookup_found _ _ _ (by rw [mapLookup_mapEntries]; exact hw)
  obtain ⟨s, es⟩ := fields S mp e me
  rw [es, compareExact_eq_atom] at qe
  exact ⟨s, qe⟩

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- The keys the points of a key type name. -/
def KeyPt (t : Term) (n : Nat) (k : Term) : MKey → Prop
  | .atom s => denD k (aPt (t := t) (n := n) (.atom s))
  | .dom k' _ => ∃ v : PN t n, denD k v ∧ ptKind v = domKind k'

/-- Atom unions of types holding every atom point hold atoms. -/
theorem all_union_atoms {Y : List (Term × Term)} (all : ∀ v : PN t n, denD (.map Y) v) :
    ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s := by
  intro S hS
  obtain ⟨c, hc⟩ := fresh_str (keyStrs S)
  have := (denD_aPt (t := t) (n := n) (Y := Y) (.atom c)).mp (all _)
  rw [hS] at this
  simp [amemV, lookup_fresh' hc] at this

/-- `map_split_keys_and_domains/1` on a static key type of the laws selects the keys its points name. -/
theorem key_split_any {k : Term} (hk : DE (level t n).E k)
    (hU : ∀ Y, k = .map Y → ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s)
    (hNeg : ∀ Y, k = .map Y → ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "negation", .map S]) →
      ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) k = .ok (splitT rs neg ds) ∧
      SplitOk rs neg ds ∧ (∀ N, neg = .map N → rs = []) ∧
      (∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∀ κ, SplitKey rs neg ds κ ↔ KeyPt t n k κ := by
  have finish : ∀ Y, DE (level t n).E (.map Y) → (∀ S, mapLookup Y (.atom "atom") =
      some (.tuple #[.atom "union", .map S]) → ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s) →
      (∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "negation", .map S]) →
        ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s) →
      ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.map Y) =
        .ok (splitT rs neg ds) ∧ SplitOk rs neg ds ∧ (∀ N, neg = .map N → rs = []) ∧
        (∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧
        ∀ κ, SplitKey rs neg ds κ ↔ KeyPt t n (.map Y) κ := by
    intro Y hY hU hNeg
    obtain ⟨rs, neg, ds, run, ok, nr, nl, sa, sd⟩ := split_map hY hU hm
    refine ⟨rs, neg, ds, run, ok, nr, fun N e => hNeg N (nl N e), fun κ => ?_⟩
    cases κ with
    | atom s => exact sa s
    | dom k' i => exact sd k' i
  rcases hk with rfl | ⟨Y, rfl, sY⟩
  · obtain ⟨T, term, -, dT, -, -, all⟩ := termN t n
    have tA : mapLookup T (.atom "atom") = some (.tuple #[.atom "negation", .map []]) := by
      have := term
      simp [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
      subst this; rfl
    obtain ⟨rs, neg, ds, run, ok, nr, nN, sem⟩ := finish T dT (all_union_atoms all)
      (fun S hS => by rw [tA] at hS; cases hS; simp)
    refine ⟨rs, neg, ds, ?_, ok, nr, nN, fun κ => (sem κ).trans ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
      simpa [term] using run
    · cases κ with
      | atom s => exact ⟨fun _ => denD_term _, fun _ => all _⟩
      | dom k' i =>
        exact ⟨fun ⟨v, _, pv⟩ => ⟨v, denD_term _, pv⟩, fun ⟨v, _, pv⟩ => ⟨v, all v, pv⟩⟩
  · exact finish Y (Or.inr ⟨Y, rfl, sY⟩) (hU Y rfl) (hNeg Y rfl)

theorem keyPt_mono {k₁ k₂ : Term} (sub : ∀ v : PN t n, denD k₁ v → denD k₂ v) {κ : MKey}
    (h : KeyPt t n k₁ κ) : KeyPt t n k₂ κ := by
  cases κ with
  | atom s => exact sub _ h
  | dom k' i => obtain ⟨v, hv, pv⟩ := h; exact ⟨v, sub v hv, pv⟩

end

end Elixir.STTDescrProofsTest.Nest
