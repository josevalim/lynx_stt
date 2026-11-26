namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Map literals without a field at an atom key. -/
def Lacks (a : String) (t : Term) : Prop :=
  ∀ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] →
    mapLookup l (.atom a) = none

/-- A literal without a field at a key holds a map with the key removed exactly when it allows the map at its other
keys. -/
theorem msemExcept_erase {tag : Term} {l : List (Term × Term)} {a : String} (la : mapLookup l (.atom a) = none)
    (w : MW V) : MSemExcept den tag l a w ↔ MSem den tag l (eraseK a w) := by
  constructor
  · rintro ⟨h, hd⟩
    refine ⟨fun s => ?_, fun k i => by simpa [eraseK] using hd k i⟩
    by_cases e : s = a
    · subst e
      simp only [FSem, la, eraseK, ite_true]
      exact tagSem_none tag "atom"
    · have : (MKey.atom s) ≠ .atom a := fun h => e (MKey.atom.inj h)
      simpa [eraseK, this] using h s e
  · intro h
    refine ⟨fun s e => ?_, fun k i => by simpa [eraseK] using h.doms k i⟩
    have : (MKey.atom s) ≠ .atom a := fun h => e (MKey.atom.inj h)
    simpa [eraseK, this] using h s

/-- The field a put stores: a required value of a type. -/
theorem putField_sem {v : Term} (o : Option V) :
    FieldSem den (.tuple #[v, .atom "false"]) o ↔ ∃ x, o = some x ∧ den v x := by
  constructor
  · rintro ⟨t, opt, e, ⟨-, rfl⟩ | ⟨x, rfl, hx⟩⟩
    · simp [boolAtom] at e
    · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
      obtain ⟨rfl, -⟩ := e
      exact ⟨x, rfl, hx⟩
  · rintro ⟨x, rfl, hx⟩
    exact ⟨v, Bool.false, rfl, Or.inr ⟨x, rfl, hx⟩⟩

/-- What a put stores at its key: some value of the type. -/
def PutAt (den : Term → V → Prop) (v : Term) (a : String) (w : MW V) : Prop := ∃ x, w (.atom a) = some x ∧ den v x

theorem putFieldV {v : Term} (hv : E v) : FieldValue E (.tuple #[v, .atom "false"]) := ⟨v, Bool.false, rfl, hv⟩

/-- `map_put_key_leaf/4` stores a required field into a literal without the key: its maps are those of the literal
with the key set to a value of the type. -/
theorem put_leaf (ef : EF nd E V den tl K) (a : String) {v : Term} (hv : E v) {lit : Term} (hl : MLit E lit)
    (la : Lacks a lit) :
    ∃ lit', Elixir.Module.Types.Descr.«map_put_key_leaf/4» lit (.atom a) v (.atom "false") = .ok lit' ∧
      MLit E lit' ∧ IsLeaf lit' ∧
      ∀ w, valM E den w lit' = (valM E den (eraseK a w) lit && bp (PutAt den v a w)) := by
  obtain ⟨⟨k, tag, l, rfl, g, sl⟩, -, -⟩ := hl
  have lka := la k tag l rfl
  obtain ⟨k', l', runS, leaf, ml', sem⟩ := store_leaf (den := den) ef g sl a (putFieldV hv)
  refine ⟨_, ?_, ml', ⟨k', tag, fieldsTerm l', rfl⟩, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
    simp [runS, leaf]
  · apply Bool.eq_iff_iff.mpr
    rw [sem w, Bool.and_eq_true, valM_leaf ef sl g, bp_true, putField_sem, ← msemExcept_erase lka]
    rfl

/-- `map_put_key_leaf/4` stores a required field into the top literal: its maps are those with the key set to a value
of the type. -/
theorem put_top (ef : EF nd E V den tl K) (a : String) {v : Term} (hv : E v) (k : Int := 61102469) :
    ∃ lit', Elixir.Module.Types.Descr.«map_put_key_leaf/4» (.tuple #[.integer k, .atom "open", .nil]) (.atom a)
        v (.atom "false") = .ok lit' ∧ MLit E lit' ∧ IsLeaf lit' ∧ ∀ w, valM E den w lit' = bp (PutAt den v a w) := by
  have sl : FieldsV E [] := ⟨by simp, by simp⟩
  obtain ⟨k', l', runS, leaf, ml', sem⟩ := store_leaf (den := den) ef (Or.inl rfl) sl a (putFieldV hv)
  refine ⟨_, ?_, ml', ⟨k', .atom "open", fieldsTerm l', rfl⟩, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
    have e : fieldsTerm ([] : List (Term × Term)) = .nil := rfl
    rw [e] at runS
    simp [runS, leaf]
  · apply Bool.eq_iff_iff.mpr
    rw [sem w, bp_true, putField_sem]
    exact ⟨fun h => h.2, fun h => ⟨⟨fun s _ => Or.inl rfl, fun k i => Or.inl rfl⟩, h⟩⟩

/-- What `map_put_key_leaf/4` does with a value and an optional flag: on literals without the key, the new literal
holds the maps of the literal with the key removed and that `P` accepts; on the top literal, the maps `P` accepts. -/
structure LeafPut (E : Term → Prop) (den : Term → V → Prop) (a : String) (v ov : Term) (P : MW V → Prop) : Prop where
  leaf : ∀ {lit}, MLit E lit → Lacks a lit → ∃ lit', Elixir.Module.Types.Descr.«map_put_key_leaf/4» lit (.atom a) v ov =
    .ok lit' ∧ MLit E lit' ∧ IsLeaf lit' ∧ ∀ w, valM E den w lit' = (valM E den (eraseK a w) lit && bp (P w))
  top : ∀ k : Int, ∃ lit', Elixir.Module.Types.Descr.«map_put_key_leaf/4» (.tuple #[.integer k, .atom "open", .nil])
    (.atom a) v ov = .ok lit' ∧ MLit E lit' ∧ IsLeaf lit' ∧ ∀ w, valM E den w lit' = bp (P w)

/-- Puts store a required field of a type. -/
theorem leafPut_put (ef : EF nd E V den tl K) (a : String) {v : Term} (hv : E v) :
    LeafPut E den a v (.atom "false") (PutAt den v a) :=
  ⟨fun hl la => put_leaf ef a hv hl la, fun k => put_top ef a hv k⟩

/-- The field a deletion stores: an absent key. -/
theorem delField_sem (ef : EF nd E V den tl K) (o : Option V) :
    FieldSem den (.tuple #[.map [], .atom "true"]) o ↔ o = none := by
  rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]
  constructor
  · rintro (⟨h, -⟩ | ⟨x, rfl, hx⟩)
    · exact h
    · exact absurd (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, hx⟩)
        ((none_field (den := den) ef).2 (some x))
  · intro h; exact Or.inl ⟨h, rfl⟩

/-- Deletions remove the key: closed literals already lack it, others store an absent field. -/
theorem leafPut_del (ef : EF nd E V den tl K) (a : String) :
    LeafPut E den a (.map []) (.atom "true") (fun w => w (.atom a) = none) where
  leaf := by
    intro lit hl la
    obtain ⟨⟨k, tag, l, rfl, g, sl⟩, ntop, key⟩ := hl
    have lka := la k tag l rfl
    have hd : FieldValue E (.tuple #[.map [], .atom "true"]) := ⟨.map [], Bool.true, rfl, ef.none⟩
    by_cases closed : tag = .atom "closed"
    · subst closed
      refine ⟨_, ?_, ⟨⟨k, _, l, rfl, g, sl⟩, ntop, key⟩, ⟨k, _, _, rfl⟩, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
        simp [Erlang.erlang.«==/2»]
      · apply Bool.eq_iff_iff.mpr
        rw [Bool.and_eq_true, valM_leaf ef sl g, valM_leaf ef sl g, bp_true, msem_split_absent ef g lka,
          fieldSem_tagV ef.mopsE ef.mdopsE ef.semR g, tagSem_atom, ← msemExcept_erase lka]
        simp
    · obtain ⟨k', l', runS, leaf, ml', sem⟩ := store_leaf (den := den) ef g sl a hd
      refine ⟨_, ?_, ml', ⟨k', tag, fieldsTerm l', rfl⟩, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
        rcases g with rfl | rfl | ⟨dl, rfl, -⟩
        · simp [runS, leaf]
        · exact absurd rfl closed
        · have ne := fieldsTerm_ne_atom dl "closed"
          generalize fieldsTerm dl = T at ne runS leaf ⊢
          split
          · rename_i h₁ _; exact absurd (tuple3_inj h₁).2.1 ne
          · simp [runS, leaf]
      · apply Bool.eq_iff_iff.mpr
        rw [sem w, Bool.and_eq_true, valM_leaf ef sl g, bp_true, delField_sem ef, ← msemExcept_erase lka]
  top := by
    intro k
    have sl : FieldsV E [] := ⟨by simp, by simp⟩
    have hd : FieldValue E (.tuple #[.map [], .atom "true"]) := ⟨.map [], Bool.true, rfl, ef.none⟩
    obtain ⟨k', l', runS, leaf, ml', sem⟩ := store_leaf (den := den) ef (Or.inl rfl) sl a hd
    refine ⟨_, ?_, ml', ⟨k', .atom "open", fieldsTerm l', rfl⟩, fun w => ?_⟩
    · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
      have e : fieldsTerm ([] : List (Term × Term)) = .nil := rfl
      rw [e] at runS
      simp [runS, leaf]
    · apply Bool.eq_iff_iff.mpr
      rw [sem w, bp_true, delField_sem ef]
      exact ⟨fun h => h.2, fun h => ⟨⟨fun s _ => Or.inl rfl, fun k i => Or.inl rfl⟩, h⟩⟩

/-- `map_put_key_before?/2` checks that a literal comes before every literal of a BDD, by its head. -/
theorem put_before {ok : Term → Prop} {b : Term} (wb : Bdd ok b) (lit : Term) :
    Elixir.Module.Types.Descr.«map_put_key_before?/2» lit b =
      .ok (boolAtom (bp (∀ l, head b = some l → compare (fuel lit l) lit l = .lt))) := by
  unfold Elixir.Module.Types.Descr.«map_put_key_before?/2»
  rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, l, c, u, d, rfl⟩
  · simp [Lynx.Term.isMember, head, boolAtom]
  · simp [Lynx.Term.isMember, head, boolAtom]
  · by_cases e : compare (fuel lit (.tuple #[.integer k, x, y])) lit (.tuple #[.integer k, x, y]) = .lt
    · simp [Lynx.Term.isMember, head, boolAtom, Erlang.erlang.«</2», e, Term.true]
    · simp [Lynx.Term.isMember, head, boolAtom, Erlang.erlang.«</2», e, Term.false,
        Ordering.isLT_iff_eq_lt]
  · by_cases e : compare (fuel lit l) lit l = .lt
    · simp [Lynx.Term.isMember, head, boolAtom, Erlang.erlang.«</2», e, Term.true]
    · simp [Lynx.Term.isMember, head, boolAtom, Erlang.erlang.«</2», e, Term.false,
        Ordering.isLT_iff_eq_lt]

/-- What `map_put_key_bdd/5` guarantees on a BDD: the result is an ordered BDD of literals whose maps, among those
whose key holds a value of the type, are the maps of the BDD with the key removed. Without a positive literal on the
path, it holds no other maps. -/
def PutBdd (E : Term → Prop) (den : Term → V → Prop) (a : String) (v ov : Term) (P : MW V → Prop) (r : Term)
    (p : Bool) : Prop :=
  ∃ r', Elixir.Module.Types.Descr.«map_put_key_bdd/5» r (.atom a) v ov (boolAtom p) = .ok r' ∧
    Bdd (MLit E) r' ∧ ∀ w : MW V,
      (P w → eval (valM E den w) r' = eval (valM E den (eraseK a w)) r) ∧
      (p = Bool.false → ¬P w → eval (valM E den w) r' = Bool.false)

/-- The node `map_put_key_bdd/5` builds from a stored literal and the stored children, either as is or with BDD
operations, holds the propositional node of its parts. -/
theorem put_node {lit c u d : Term} (ml : MLit E lit) (il : IsLeaf lit) (wc : Bdd (MLit E) c) (wu : Bdd (MLit E) u)
    (wd : Bdd (MLit E) d) (B : Term) (hB : B = boolAtom (bp ((∀ l, head c = some l → compare (fuel lit l) lit l = .lt) ∧
      (∀ l, head u = some l → compare (fuel lit l) lit l = .lt) ∧ (∀ l, head d = some l → compare (fuel lit l) lit l = .lt)))) :
    ∃ r, ((fun {lynxValue : Type}
            (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
            (lynxNext : Unit → Except Lynx.Exception lynxValue) => lynxBody lynxNext)
          (fun lynxMatchNext =>
            match B with
            | _v_3 =>
              Lynx.Except.guard (Except.ok (Lynx.Term.isMember B [Lynx.Term.atom "false", Lynx.Term.atom "nil"]))
                (fun _ => do
                  let _17 ← Elixir.Module.Types.Descr.«bdd_intersection/2» lit c
                  let _18 ← Elixir.Module.Types.Descr.«bdd_union/2» _17 u
                  let _16 ← Elixir.Module.Types.Descr.«bdd_difference/2» d lit
                  Elixir.Module.Types.Descr.«bdd_union/2» _18 _16)
                lynxMatchNext)
          (fun (_ : Unit) => match B with | _29 => Elixir.Module.Types.Descr.«bdd_node_new/4» lit c u d)) = .ok r ∧
      Bdd (MLit E) r ∧ ∀ w : MW V, eval (valM E den w) r =
        ((valM E den w lit && eval (valM E den w) c) || eval (valM E den w) u || (!valM E den w lit && eval (valM E den w) d)) := by
  have wl : Bdd (MLit E) lit := by obtain ⟨k, x, y, rfl⟩ := il; exact Bdd.leaf_iff.mpr ml
  by_cases ord : (∀ l, head c = some l → compare (fuel lit l) lit l = .lt) ∧
      (∀ l, head u = some l → compare (fuel lit l) lit l = .lt) ∧ (∀ l, head d = some l → compare (fuel lit l) lit l = .lt)
  · rw [bp_true.mpr ord] at hB
    subst hB
    obtain ⟨h, run⟩ := node_new lit c u d il wc wu wd
    refine ⟨.tuple #[.integer h, lit, c, u, d], ?_, ?_, fun w => by simp⟩
    · simp [Lynx.Term.isMember, boolAtom, run]
    · obtain ⟨k, x, y, rfl⟩ := il
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ml, wc.raise ord.1, wu.raise ord.2.1, wd.raise ord.2.2⟩
  · rw [bp_false.mpr ord] at hB
    subst hB
    obtain ⟨i, ri, oi, si⟩ := inter_ok wl wc
    obtain ⟨j, rj, oj, sj⟩ := union_ok (oi _ wl wc) wu
    obtain ⟨e, re, oe, se⟩ := diff_ok wd wl
    obtain ⟨r, rr, or_, sr⟩ := union_ok (oj _ (oi _ wl wc) wu) (oe _ wd wl)
    refine ⟨r, ?_, or_ _ (oj _ (oi _ wl wc) wu) (oe _ wd wl), fun w => ?_⟩
    · simp [Lynx.Term.isMember, boolAtom, ri, rj, re, rr]
    · have resp := valM_resp (E := E) (den := den) w
      obtain ⟨k, x, y, rfl⟩ := il
      rw [sr _ resp, sj _ resp, si _ resp, se _ resp]
      simp only [eval_leaf]
      cases valM E den w (.tuple #[.integer k, x, y]) <;> simp

/-- `map_put_key_bdd/5` on ordered BDDs of literals without the key. -/
theorem put_bdd (a : String) {v ov : Term} {P : MW V → Prop} (lp : LeafPut E den a v ov P) :
    ∀ (ok : Term → Prop) (r : Term), Bdd ok r → (∀ t, ok t → MLit E t ∧ Lacks a t) → ∀ p,
      PutBdd E den a v ov P r p := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MLit E t ∧ Lacks a t) → ∀ p, PutBdd E den a v ov P r p)
    ?_ ?_ ?_ ?_
  · intro ok _ p
    cases p
    · obtain ⟨lit', run, ml', il', sem⟩ := lp.top 61102469
      refine ⟨lit', ?_, by obtain ⟨k, x, y, rfl⟩ := il'; exact Bdd.leaf_iff.mpr ml', fun w => ⟨fun h => ?_, fun _ h => ?_⟩⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key_bdd/5», boolAtom, run]
      · obtain ⟨k, x, y, rfl⟩ := il'; simp [sem, h]
      · obtain ⟨k, x, y, rfl⟩ := il'; simp [sem, h]
    · refine ⟨.atom "bdd_top", ?_, Bdd.top, fun w => ⟨fun _ => by simp, fun h => by cases h⟩⟩
      simp [Elixir.Module.Types.Descr.«map_put_key_bdd/5», boolAtom]
  · intro ok _ p
    refine ⟨.atom "bdd_bot", ?_, Bdd.bot, fun w => ⟨fun _ => by simp, fun _ _ => by simp⟩⟩
    simp [Elixir.Module.Types.Descr.«map_put_key_bdd/5»]
  · intro ok k x y okl hok p
    obtain ⟨ml, la⟩ := hok _ okl
    obtain ⟨lit', run, ml', il', sem⟩ := lp.leaf ml la
    refine ⟨lit', ?_, by obtain ⟨k, x, y, rfl⟩ := il'; exact Bdd.leaf_iff.mpr ml', fun w => ⟨fun h => ?_, fun _ h => ?_⟩⟩
    · simp [Elixir.Module.Types.Descr.«map_put_key_bdd/5», run]
    · obtain ⟨k, x, y, rfl⟩ := il'; simp [sem, h]
    · obtain ⟨k, x, y, rfl⟩ := il'; simp [sem, h]
  · intro ok h lit c u d il okl _ _ _ ic iu id hok p
    obtain ⟨ml, la⟩ := hok _ okl
    have hok' : ∀ t, Above ok lit t → MLit E t ∧ Lacks a t := fun t ht => hok t ht.1
    obtain ⟨lit', rl, ml', il', sl⟩ := lp.leaf ml la
    obtain ⟨c', rc, wc, sc⟩ := ic hok' Bool.true
    obtain ⟨u', ru, wu, su⟩ := iu hok' p
    obtain ⟨d', rd, wd, sd⟩ := id hok' p
    have bc := put_before wc lit'
    have bu := put_before wu lit'
    have bd := put_before wd lit'
    obtain ⟨r, rr, wr, sr⟩ := put_node (den := den) ml' il' wc wu wd _ rfl
    refine ⟨r, ?_, wr, fun w => ⟨fun hw => ?_, fun hp hw => ?_⟩⟩
    · have rc' : Elixir.Module.Types.Descr.«map_put_key_bdd/5» c (.atom a) v ov (.atom "true") = .ok c' := rc
      rw [Elixir.Module.Types.Descr.«map_put_key_bdd/5».eq_def]
      simp only [rl, rc', ru, rd, bu, bd, bc, Lynx.Except.ok_bind]
      rw [← rr]
      rw [← bp_and, ← bp_and]
      generalize bp (∀ l, head c' = some l → compare (fuel lit' l) lit' l = .lt) = x
      generalize bp (∀ l, head u' = some l → compare (fuel lit' l) lit' l = .lt) = y
      generalize bp (∀ l, head d' = some l → compare (fuel lit' l) lit' l = .lt) = z
      cases x <;> cases y <;> cases z <;> simp [boolAtom]
    · rw [sr w, sl w, (sc w).1 hw, (su w).1 hw, (sd w).1 hw, eval_node]
      simp [bp_true.mpr hw]
    · rw [sr w, sl w, (su w).2 hp hw, (sd w).2 hp hw]
      simp [bp_false.mpr hw]

theorem field_union_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f g : Term} (hf : FieldValue E f)
    (hg : FieldValue E g) : ∃ h, FieldValue E h ∧ Elixir.Module.Types.Descr.«field_union/2» (D m) f g = .ok h ∧
      ∀ o, FieldSem den h o ↔ FieldSem den f o ∨ FieldSem den g o := by
  obtain ⟨t₁, o₁, rfl, h₁⟩ := hf
  obtain ⟨t₂, o₂, rfl, h₂⟩ := hg
  obtain ⟨c, hc, run, sem, -⟩ := ef.union h₁ h₂
  refine ⟨.tuple #[c, boolAtom (o₁ || o₂)], ⟨c, _, rfl, hc⟩, ?_, fun o => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«field_union/2», run m hm]
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.orElse]
  · rw [fieldSem_mk, fieldSem_mk, fieldSem_mk]
    cases o with
    | none => cases o₁ <;> cases o₂ <;> simp
    | some x =>
      simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or, sem x]

/-- `map_pair_projection_keeps_full_snd?/2` checks for a value at the key outside every negated pair. -/
theorem mkeeps_snd (ef : EF nd E V den tl K) {m : Nat} (hm : K + 4 ≤ m) (P : List Term) (hP : ∀ p ∈ P, MPairOk E p)
    {field : Term} (hf : FieldValue E field) : ∃ s : Bool,
      Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (m + 1)) (Term.list P) field =
        .ok (boolAtom s) ∧
      (s = Bool.true ↔ ∃ o, FieldSem den field o ∧ ∀ p ∈ P, ∀ f nb, p = .tuple #[f, nb] → ¬FieldSem den f o) := by
  obtain ⟨u, ⟨tu, su⟩, run⟩ := foldl_rel_at (m := m + 1) "Elixir.Module.Types.Descr"
    "-map_pair_projection_keeps_full_snd?/2-fun-0-" #[]
    (fun pre a => FieldValue E a ∧ ∀ o, FieldSem den a o ↔ ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ FieldSem den f o) P
    (fun pre x a mx ⟨ta, sa⟩ => by
      obtain ⟨f, b, rfl, hf', -⟩ := hP x mx
      obtain ⟨r, tr, run, sr⟩ := field_union_val (den := den) ef (m := m) (by omega) hf' ta
      refine ⟨r, ⟨tr, fun o => ?_⟩, ?_⟩
      · rw [sr, sa]
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
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_pair_projection_keeps_full_snd?/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_pair_projection_keeps_full_snd?/2-fun-0-/2»] using run)
    (.tuple #[.map [], .atom "false"]) ⟨(none_field ef).1, fun o => by simp [(none_field (den := den) ef).2 o]⟩
  obtain ⟨d, td, rd, sd⟩ := field_diff_val (den := den) ef (m := m + 1) (by omega) hf tu
  obtain ⟨e, re, se⟩ := field_empty_val (den := den) ef (m := m + 1) (by omega) td
  refine ⟨!e, ?_, ?_⟩
  · cases e <;> simp [Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2», run, rd, re,
      Erlang.erlang.«not/1», boolAtom]
  · cases e
    · simp only [Bool.not_false, true_iff]
      obtain ⟨o, ho⟩ := Classical.not_forall.mp (mt se.mpr (by simp))
      rw [Classical.not_not, sd, su] at ho
      exact ⟨o, ho.1, fun p mp f nb e hfo => ho.2 ⟨p, mp, f, nb, e, hfo⟩⟩
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro o ho none
      refine (se.mp rfl) o ((sd o).mpr ⟨ho, fun h => ?_⟩)
      obtain ⟨p, mp, f, b, e, hfo⟩ := (su o).mp h
      exact none p mp f b e hfo

/-- Map literals without a key. -/
def LitA (E : Term → Prop) (a : String) (t : Term) : Prop := MLit E t ∧ Lacks a t

theorem lacks_lit {k : Int} {tag : Term} {l : List (Term × Term)} {a : String} (la : mapLookup l (.atom a) = none) :
    Lacks a (.tuple #[.integer k, tag, fieldsTerm l]) := by
  intro k' tag' l' e
  obtain ⟨-, -, e₃⟩ := tuple3_inj e
  rw [← fieldsTerm_inj e₃]
  exact la

/-- Map types of one literal without a key. -/
theorem oField_litA {k : Int} {tag : Term} {l : List (Term × Term)} {a : String}
    (h : MField E (.tuple #[.integer k, tag, fieldsTerm l])) (la : mapLookup l (.atom a) = none) :
    OField (LitA E a) (.tuple #[.integer k, tag, fieldsTerm l]) := by
  rcases h with top | wb
  · exact Or.inl top
  · exact Or.inr (Bdd.leaf_iff.mpr ⟨Bdd.leaf_iff.mp wb, lacks_lit la⟩)

/-- The rest of a pair. -/
def pairSnd : Term → Term
  | .tuple ⟨[_, b]⟩ => b
  | _ => .nil

/-- One step of `map_dnf_pop_key/2`: the map types of the maps of a non-empty line without a key, as maps whose key
may hold anything. -/
theorem mline_pop (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {L : Term} (hL : MLine E L)
    (ne : ∃ w, InMLine den L w) :
    ∃ Bs : List Term, (D (n + 3)).pure (.function false "Elixir.Module.Types.Descr" "-map_dnf_pop_key/2-fun-1-" 1 #[.atom a])
        #[L] = .ok (Term.list Bs) ∧ (∀ b ∈ Bs, MField E b ∧ OField (LitA E a) b) ∧
      ∀ w, (∃ b ∈ Bs, denMF E den b (eraseK a w) = Bool.true) ↔ ∃ o, InMLine den L (setK a o w) := by
  obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hL
  obtain ⟨w₀, hw₀⟩ := ne
  obtain ⟨hm₀, -⟩ := inMLine_iff.mp hw₀
  obtain ⟨k, run, ⟨f, b, ef', hf, hb⟩, rest, -⟩ := pop_pair (den := den) ef g sl a
  simp only [Term.tuple.injEq] at ef'
  obtain ⟨rfl, rfl, -⟩ := ef'
  have split₀ := (msem_at ef g l a w₀).mp hm₀
  have orest := oField_litA hb (a := a) (by simp [lookup_eraseKey])
  have key : ∀ w o, MSem den tag l (setK a o w) ↔
      FieldSem den (fieldAt tag l a) o ∧ denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) (eraseK a w) =
        Bool.true := by
    intro w o
    rw [msem_at ef g l a, rest, eraseK_setK]
    simp [setK]
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_dnf_pop_key/2-fun-1-/1».pure]
  by_cases nn : negs = []
  · subst nn
    refine ⟨[.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]], ?_, by simpa using ⟨hb, orest⟩, fun w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run, Term.list]
    · constructor
      · rintro ⟨b', mb, hb'⟩
        rw [List.mem_singleton] at mb; subst mb
        exact ⟨w₀ (.atom a), inMLine_iff.mpr ⟨(key w _).mpr ⟨split₀.1, hb'⟩, by simp⟩⟩
      · rintro ⟨o, ho⟩
        exact ⟨_, List.mem_singleton_self _, ((key w o).mp (inMLine_iff.mp ho).1).2⟩
  obtain ⟨N₀, negs₀, rfl⟩ : ∃ N₀ negs₀, negs = N₀ :: negs₀ := by
    cases negs with
    | nil => exact absurd rfl nn
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨r, rr, ⟨rfl, N, mN, hN⟩ | ⟨P, rfl, hP, sP⟩⟩ := msplit_negs (den := den) ef a (N₀ :: negs₀) lits []
  all_goals have rr' := rr; simp only [Term.list] at rr'
  · refine ⟨[], ?_, by simp, fun w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
        Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', Term.list]
    · simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_exists]
      intro o hw
      exact (inMLine_iff.mp hw).2 N mN (hN _)
  simp only [List.append_nil] at rr
  have restNe : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
    ⟨_, (rest _).mpr split₀.2⟩
  have hP' : ∀ p ∈ P, MPairOk E p := fun p mp => (hP p mp).1
  have kP : KeepsQ (LitA E a) P := fun p mp => by
    obtain ⟨⟨f, b, e, -, fb⟩, f', k', ntag, nl, e', -, -, na, -⟩ := hP p mp
    subst e'
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨_, _, rfl, oField_litA fb na⟩
  -- Values at the key of maps of the line, with the rest of a map.
  have line : ∀ w o, InMLine den (.tuple #[tag, fieldsTerm l, Term.list (N₀ :: negs₀)]) (setK a o w) ↔
      FieldSem den (fieldAt tag l a) o ∧
        denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) (eraseK a w) = Bool.true ∧
        ∀ p ∈ P, ¬MPairIn E den p o (eraseK a w) := by
    intro w o
    rw [inMLine_iff, key, and_assoc]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h p mp hp => ?_, fun h N mN hN' => ?_⟩)
    · obtain ⟨N, mN, hN'⟩ := (sP (setK a o w)).mpr ⟨p, mp, by simpa [setK, eraseK_setK] using hp⟩
      exact h N mN hN'
    · obtain ⟨p, mp, hp⟩ := (sP (setK a o w)).mp ⟨N, mN, hN'⟩
      exact h p mp (by simpa [setK, eraseK_setK] using hp)
  obtain ⟨s, rs, ss⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' hf
  cases s
  · obtain ⟨Q, rQ, qQ, kQ, fQ, sQ⟩ := mproject_pairs ef hn P hP' hf hb restNe
    have fQ := fQ ⟨_, split₀.1⟩
    refine ⟨Q.map pairSnd, ?_, fun b' mb => ?_, fun w => ?_⟩
    · have rm := map_list (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) "Elixir.Module.Types.Descr"
        "-map_dnf_pop_key/2-fun-0-" #[] pairSnd Q fun q mq => by
          obtain ⟨f', b', rfl, -⟩ := qQ q mq
          rw [Erlang.program.«Elixir.Module.Types.Descr:-map_dnf_pop_key/2-fun-0-/1».pure]
          simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-0-/1», Erlang.erlang.«element/2», pairSnd]
      cases P with
      | nil => simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rs, rQ, rm, Lynx.Term.isMember, boolAtom, Term.list]
      | cons p P => simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rs, rQ, rm, Lynx.Term.isMember, boolAtom, Term.list]
    · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mb
      obtain ⟨f', b'', rfl, -, fb, -⟩ := qQ q mq
      obtain ⟨f₂, b₂, e, ob⟩ := kQ (LitA E a) orest kP _ mq
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
      obtain ⟨-, rfl⟩ := e
      exact ⟨fb, ob⟩
    · constructor
      · rintro ⟨b', mb, hb'⟩
        obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mb
        obtain ⟨f', b'', rfl, o, ho⟩ := fQ q mq
        obtain ⟨hy, hr, hout⟩ := (sQ o (eraseK a w)).mp ⟨_, mq, mpairIn_iff.mpr ⟨ho, hb'⟩⟩
        exact ⟨o, (line w o).mpr ⟨hy, hr, hout⟩⟩
      · rintro ⟨o, ho⟩
        obtain ⟨q, mq, hq⟩ := (sQ o (eraseK a w)).mpr ((line w o).mp ho)
        obtain ⟨f', b'', rfl, -, hb'⟩ := hq
        exact ⟨b'', List.mem_map.mpr ⟨_, mq, rfl⟩, hb'⟩
  · obtain ⟨o₀, ho₀, out₀⟩ := ss.mp rfl
    refine ⟨[.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]], ?_, by simpa using ⟨hb, orest⟩, fun w => ?_⟩
    · cases P with
      | nil => simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rs, Lynx.Term.isMember, boolAtom, Term.list]
      | cons p P => simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rs, Lynx.Term.isMember, boolAtom, Term.list]
    · constructor
      · rintro ⟨b', mb, hb'⟩
        rw [List.mem_singleton] at mb; subst mb
        refine ⟨o₀, (line w o₀).mpr ⟨ho₀, hb', fun p mp hp => ?_⟩⟩
        obtain ⟨f', nb, e, hf', -⟩ := hp
        exact out₀ p mp f' nb e hf'
      · rintro ⟨o, ho⟩
        exact ⟨_, List.mem_singleton_self _, ((line w o).mp ho).2.1⟩

/-- Merging literals at one of their keys keeps literals without another key. -/
theorem mergeOk_litA (a : String) : MergeOk E (LitA E a) := by
  intro k₁ k tag l₁ l s ⟨_, la⟩ hs look ml
  refine ⟨ml, lacks_lit ?_⟩
  have la₁ := la k₁ tag l₁ rfl
  have ne : s ≠ a := fun e => hs (e ▸ la₁)
  rw [look a ne, la₁]

/-- `map_union_pairs/1` unites map types two by two. -/
theorem munion_list (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {ok : Term → Prop} (mok : MergeOk E ok) :
    ∀ Bs : List Term, (∀ b ∈ Bs, MField E b ∧ OField ok b) →
      ∃ Cs : List Term, Elixir.Module.Types.Descr.«map_union_pairs/1» (D m) (Term.list Bs) = .ok (Term.list Cs) ∧
        Cs.length ≤ Bs.length ∧ (2 ≤ Bs.length → Cs.length < Bs.length) ∧
        (∀ c ∈ Cs, MField E c ∧ OField ok c) ∧
        ∀ w : MW V, (∃ c ∈ Cs, denMF E den c w = Bool.true) ↔ ∃ b ∈ Bs, denMF E den b w = Bool.true
  | [] , _ => ⟨[], by simp [Elixir.Module.Types.Descr.«map_union_pairs/1», Term.list], by simp, by simp, by simp,
      fun w => by simp⟩
  | [b], hb => ⟨[b], by simp [Elixir.Module.Types.Descr.«map_union_pairs/1», Term.list], by simp, by simp, hb,
      fun w => Iff.rfl⟩
  | b₁ :: b₂ :: Bs, hB => by
    obtain ⟨f₁, o₁⟩ := hB b₁ (by simp)
    obtain ⟨f₂, o₂⟩ := hB b₂ (by simp)
    obtain ⟨c, rc, fc, kc, sc⟩ := opt_map_union_sem (den := den) ef hm f₁ f₂ []
    obtain ⟨Cs, rCs, len, -, hCs, sCs⟩ := munion_list ef hm mok Bs fun b mb => hB b (by simp [mb])
    refine ⟨c :: Cs, ?_, by simp; omega, fun _ => by simp; omega, fun c' mc => ?_, fun w => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_union_pairs/1».eq_def]
      simp [Term.list, rc, rCs]
    · rcases List.mem_cons.mp mc with rfl | mc
      · exact ⟨fc, kc ok mok o₁ o₂⟩
      · exact hCs c' mc
    · simp only [List.mem_cons, exists_eq_or_imp] at sCs ⊢
      rw [sc, Bool.or_eq_true, sCs]
      exact or_assoc

/-- `map_union_all/1` unites map types. -/
theorem munion_all (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {ok : Term → Prop} (mok : MergeOk E ok) :
    ∀ (n : Nat) (Bs : List Term), Bs.length ≤ n → (∀ b ∈ Bs, MField E b ∧ OField ok b) →
      ∃ r, Elixir.Module.Types.Descr.«map_union_all/1» (D m) (Term.list Bs) = .ok r ∧ MField E r ∧ OField ok r ∧
        ∀ w : MW V, denMF E den r w = Bool.true ↔ ∃ b ∈ Bs, denMF E den b w = Bool.true
  | n, [], _, _ => ⟨.atom "bdd_bot", by rw [Elixir.Module.Types.Descr.«map_union_all/1».eq_def]; rfl, Or.inr Bdd.bot,
      Or.inr Bdd.bot, fun w => by simp [denMF_bot]⟩
  | n, [b], _, hb => by
    obtain ⟨fb, ob⟩ := hb b (by simp)
    exact ⟨b, by rw [Elixir.Module.Types.Descr.«map_union_all/1».eq_def]; rfl, fb, ob, fun w => by simp⟩
  | n + 1, b₁ :: b₂ :: Bs, len, hB => by
    obtain ⟨Cs, rCs, -, shorter, hCs, sCs⟩ := munion_list (den := den) ef hm mok (b₁ :: b₂ :: Bs) hB
    have := shorter (by simp)
    obtain ⟨r, rr, fr, kr, sr⟩ := munion_all ef hm mok n Cs (by simp at len this; omega) hCs
    refine ⟨r, ?_, fr, kr, fun w => (sr w).trans (sCs w)⟩
    rw [Elixir.Module.Types.Descr.«map_union_all/1».eq_def]
    simp only [Term.list] at rCs ⊢
    simp [rCs, rr]
  | 0, _ :: _ :: _, len, _ => by simp at len

/-- `map_dnf_pop_key/2` on non-empty lines: a map type without the key whose maps, with the key removed, are the
maps of the lines with the key changed to anything. -/
theorem mdnf_pop (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ r, Elixir.Module.Types.Descr.«map_dnf_pop_key/2» (D (n + 3)) (Term.list lines) (.atom a) = .ok r ∧
      MField E r ∧ OField (LitA E a) r ∧
      ∀ w, denMF E den r (eraseK a w) = Bool.true ↔ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) := by
  classical
  have each : ∀ L ∈ lines, ∃ Bs : List Term,
      (D (n + 3)).pure (.function false "Elixir.Module.Types.Descr" "-map_dnf_pop_key/2-fun-1-" 1 #[.atom a]) #[L] =
        .ok (Term.list Bs) ∧ (∀ b ∈ Bs, MField E b ∧ OField (LitA E a) b) ∧
      ∀ w, (∃ b ∈ Bs, denMF E den b (eraseK a w) = Bool.true) ↔ ∃ o, InMLine den L (setK a o w) :=
    fun L mL => mline_pop ef hn a (hl L mL).1 (hl L mL).2
  let h : Term → List Term := fun L => if hL : L ∈ lines then Classical.choose (each L hL) else []
  have hh : ∀ L ∈ lines,
      (D (n + 3)).pure (.function false "Elixir.Module.Types.Descr" "-map_dnf_pop_key/2-fun-1-" 1 #[.atom a]) #[L] =
        .ok (Term.list (h L)) ∧ (∀ b ∈ h L, MField E b ∧ OField (LitA E a) b) ∧
      ∀ w, (∃ b ∈ h L, denMF E den b (eraseK a w) = Bool.true) ↔ ∃ o, InMLine den L (setK a o w) := fun L mL => by
    simp only [h, dite_eq_left mL]
    exact Classical.choose_spec (each L mL)
  have fm := flatmap_lists (m := n + 3) "Elixir.Module.Types.Descr" "-map_dnf_pop_key/2-fun-1-" #[.atom a] h lines
    fun L mL => (hh L mL).1
  obtain ⟨r, rr, fr, kr, sr⟩ := munion_all (den := den) ef (m := n + 3) (by omega) (mergeOk_litA a) _
    (lines.flatMap h) (Nat.le_refl _) fun b mb => by
      obtain ⟨L, mL, mb⟩ := List.mem_flatMap.mp mb
      exact (hh L mL).2.1 b mb
  refine ⟨r, ?_, fr, kr, fun w => ?_⟩
  · simp [Elixir.Module.Types.Descr.«map_dnf_pop_key/2», fm, rr]
  · rw [sr]
    constructor
    · rintro ⟨b, mb, hb⟩
      obtain ⟨L, mL, mb⟩ := List.mem_flatMap.mp mb
      exact ⟨L, mL, ((hh L mL).2.2 w).mp ⟨b, mb, hb⟩⟩
    · rintro ⟨L, mL, hL⟩
      obtain ⟨b, mb, hb⟩ := ((hh L mL).2.2 w).mpr hL
      exact ⟨b, List.mem_flatMap.mpr ⟨L, mL, mb⟩, hb⟩

/-- The force clause of `map_update_named_key/5` for a constant: the maps of the lines with the key set to a value of
the type. -/
theorem put_lines (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v ov : Term} {P : MW V → Prop}
    (lp : LeafPut E den a v ov P) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ bdds : List Term, (∀ (ow : Bool) (Fo : Term),
        (ow = Bool.true → Elixir.Module.Types.Descr.«map_dnf_fetch_static/2» (D (n + 3)) (Term.list lines) (.atom a) =
          .ok Fo) →
        Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
          (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "true")
          (boolAtom ow) = .ok (.tuple #[Term.list bdds, if ow then Fo else .atom "nil"])) ∧ (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        P w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) := by
  obtain ⟨r, rr, -, kr, sr⟩ := mdnf_pop ef hn a lines hl
  rcases kr with ⟨k, rfl⟩ | wr
  · obtain ⟨lit', run, ml', il', sem⟩ := lp.top k
    refine ⟨[lit'], fun ow Fo hF => ?_, fun b mb => by
      rw [List.mem_singleton] at mb; subst mb; obtain ⟨k', x, y, rfl⟩ := il'; exact Or.inr (Bdd.leaf_iff.mpr ml'),
      fun w => ?_⟩
    · cases ow
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, Elixir.Module.Types.Descr.«map_put_key_bdd/5»,
          run, Lynx.Term.isMember, Term.list, boolAtom]
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, Elixir.Module.Types.Descr.«map_put_key_bdd/5»,
          run, Lynx.Term.isMember, Term.list, boolAtom, hF rfl]
    · obtain ⟨k', x, y, rfl⟩ := il'
      have top := (sr w).mp (by simp [denMF_top])
      simp only [List.mem_singleton, exists_eq_left]
      rw [denMF_bdd (Bdd.leaf_iff.mpr ml'), eval_leaf, sem, bp_true]
      exact ⟨fun h => ⟨h, top⟩, fun h => h.1⟩
  obtain ⟨r', run, wr', sem⟩ := put_bdd a lp _ r wr (fun _ h => h) Bool.false
  have wr₀ : Bdd (MLit E) r := wr.mono fun _ h => h.1
  by_cases bot : r = .atom "bdd_bot"
  · subst bot
    refine ⟨[], fun ow Fo hF => ?_, by simp, fun w => ?_⟩
    · cases ow
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, Lynx.Term.isMember, Term.list, boolAtom]
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, Lynx.Term.isMember, Term.list, boolAtom, hF rfl]
    · simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and]
      intro _ h
      have := (sr w).mpr h
      simp [denMF_bot] at this
  refine ⟨[r'], fun ow Fo hF => ?_, fun b mb => by rw [List.mem_singleton] at mb; subst mb; exact Or.inr wr',
    fun w => ?_⟩
  · have run' : Elixir.Module.Types.Descr.«map_put_key_bdd/5» r (.atom a) v ov (.atom "false") = .ok r' := run
    rcases wr₀.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · cases ow
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, run', Lynx.Term.isMember, Term.list, boolAtom]
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, run', Lynx.Term.isMember, Term.list, boolAtom,
          hF rfl]
    · exact absurd rfl bot
    all_goals
      cases ow
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, run', Lynx.Term.isMember, Term.list, boolAtom]
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, run', Lynx.Term.isMember, Term.list, boolAtom,
          hF rfl]
  · simp only [List.mem_singleton, exists_eq_left]
    rw [denMF_bdd wr', ← sr, denMF_bdd wr₀]
    by_cases hp : P w
    · rw [(sem w).1 hp]; simp [hp]
    · rw [(sem w).2 rfl hp]; simp [hp]

/-- What a put of a constant gives: a map type of the maps of the lines with the key set to a value of the type, or the
empty type. -/
def PutMaps (E : Term → Prop) (den : Term → V → Prop) (a : String) (P : MW V → Prop) (lines : List Term) (Y : Term) :
    Prop :=
  ∃ r, MField E r ∧ (Y = .map [(.atom "map", r)] ∨ (Y = .map [] ∧ ∀ w, denMF E den r w = Bool.false)) ∧
    ∀ w, denMF E den r w = Bool.true ↔ P w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w)

theorem put_static_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v ov : Term}
    {P : MW V → Prop} (lp : LeafPut E den a v ov P) (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ Y, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 4)) bdd (Term.list lines)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "false") (.atom "true") =
        .ok (.tuple #[.map [], Y, .nil, .atom "true"]) ∧ PutMaps E den a P lines Y := by
  obtain ⟨bdds, rb, fb, sb⟩ := put_lines ef hn a lp lines hl
  have rb : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "true") (.atom "false") =
      .ok (.tuple #[Term.list bdds, .atom "nil"]) := by simpa [boolAtom] using rb Bool.false .nil (by simp)
  have nk₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[.map [], .nil, .nil, .atom "false"])
      (Term.list lines) (.cons (.atom a) .nil) (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"])
      (.atom "true") (.atom "true") (.atom "false") (.atom "true") =
      .ok (.tuple #[.map [], Term.list bdds, .nil, .atom "true"]) := by
    have rb' := rb
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.lists.«foldl_1/3», Erlang.erlang.«is_function/2»,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
      Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», rb']
    rw [show (Term.nil) = Term.list [] from rfl, append_list]
    simp
  have nk₂ : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) acc (Term.list lines) .nil
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"])
      (.atom "false") (.atom "true") (.atom "false") (.atom "true") = .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«==/2», Erlang.erlang.«/=/2»,
    Lynx.Term.isMember, Erlang.erlang.«--/2», Erlang.erlang.«++/2», Erlang.erlang.«not/1», Term.list, Term.properList?, nk₁,
    nk₂]
  obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 4) (by omega) (ok := fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bdds (Nat.le_refl _) fun b mb => ⟨fb b mb, by
      rcases fb b mb with ⟨k, rfl⟩ | wb
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr (wb.mono fun _ _ => trivial)⟩
  have sem : ∀ w, denMF E den r w = Bool.true ↔ P w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) :=
    fun w => (sr w).trans (sb w)
  by_cases bot : r = .atom "bdd_bot"
  · subst bot
    refine ⟨.map [], by simp [rr], .atom "bdd_bot", fr, Or.inr ⟨rfl, fun w => denMF_bot w⟩, sem⟩
  · refine ⟨.map [(.atom "map", r)], ?_, r, fr, Or.inl rfl, sem⟩
    simp only [rr, Lynx.Except.ok_bind]

/-- What a put of a constant gives on a map field: the maps of the field with the key set to a value of the type. -/
def PutField (E : Term → Prop) (den : Term → V → Prop) (a : String) (P : MW V → Prop) (b Y : Term) : Prop :=
  ∃ r, MField E r ∧ (Y = .map [(.atom "map", r)] ∨ (Y = .map [] ∧ ∀ w, denMF E den r w = Bool.false)) ∧
    ∀ w, denMF E den r w = Bool.true ↔ P w ∧ ∃ o, denMF E den b (setK a o w) = Bool.true

theorem putMaps_field {a : String} {P : MW V → Prop} {b Y : Term} {lines : List Term}
    (inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (h : PutMaps E den a P lines Y) :
    PutField E den a P b Y := by
  obtain ⟨r, fr, hY, sr⟩ := h
  refine ⟨r, fr, hY, fun w => (sr w).trans (and_congr Iff.rfl ⟨?_, ?_⟩)⟩
  · rintro ⟨L, mL, o, hL⟩; exact ⟨o, (inB _).mpr ⟨L, mL, hL⟩⟩
  · rintro ⟨o, ho⟩; obtain ⟨L, mL, hL⟩ := (inB _).mp ho; exact ⟨L, mL, o, hL⟩

/-- `map_update_static/5` puts a constant into a map field: `:badmap` when it is empty. -/
theorem put_update_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v ov : Term}
    {P : MW V → Prop} (lp : LeafPut E den a v ov P)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 4)) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "false") (.atom "true") =
        .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ Y, res = .tuple #[.map [], Y, .nil, .atom "true"] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          PutField E den a P b Y) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 4)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 4) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      obtain ⟨Y, rY, pY⟩ := put_static_dnf ef hn a lp (.tuple #[.integer k, tag, fieldsTerm l]) _ hl
      refine ⟨_, ?_, Or.inr ⟨Y, rfl, ⟨w₀, (sem w₀).mpr h₀⟩, putMaps_field (fun w => ?_) pY⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
        simpa [Term.list] using rY
      · rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 4) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl (m := n + 4) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
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
      obtain ⟨Y, rY, pY⟩ := put_static_dnf ef hn a lp b (L :: rest) hl
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨Y, rfl, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, putMaps_field inB pY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY

/-- `map_split_keys_and_domains/1` on a single atom requires it. -/
theorem split_one (s : String) (m : Nat) :
    Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (atomT s) =
      .ok (.tuple #[Term.list [.atom s], .nil, .atom "nil", .nil, .nil]) := by
  rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
  simp [atomT, getMapKeys_single, mapLookup, Erlang.sets.«to_list/1», Erlang.maps.«keys/1», Term.list,
    Elixir.Module.Types.Descr.«to_domain_keys/1», Erlang.maps.«fold/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-to_domain_keys/1-fun-0-/3».pure,
    Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2»]

theorem descrC_map {Fn TF LF MF : Term → Prop} {r : Term} (mr : MF r) : DescrC Fn TF LF MF [(.atom "map", r)] where
  keys q h := by
    by_cases e : compareExact (fuel q (.atom "map")) q (.atom "map") = .eq
    · exact ⟨"map", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · simp [mapLookup, e] at h
  fields name x h := by
    by_cases e : name = "map"
    · subst e
      simp [mapLookup] at h; subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, mr⟩))))
    · simp [mapLookup, e] at h

section
variable {t : Term} {n : Nat}

/-- `map_update_unchecked/4` forcing a constant field at a key of static types of the next level: types holding only
maps, some of them, give the maps the field accepts that agree with one of their maps at the other keys; others give
`:badmap`. -/
theorem update_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v ov : Term}
    {P : MW (level t n).V → Prop} (lp : LeafPut (level t n).E (level t n).den a v ov P) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "false") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, res = .tuple #[.map [], .map Y, .nil] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ P w ∧ ∃ o, MT t n X (setK a o w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 4))
      (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[r] =
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
    have rE := next_empty dR (m := k + 4) (by omega)
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
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 4)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨Y, rfl, ⟨w₀, hw₀⟩, r, fr, hY, sr⟩⟩ :=
        put_update_static (level t n).ef (n := k) (by omega) a lp hb fb
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      have sem : ∀ w, denMF (level t n).E (level t n).den r w = Bool.true ↔
          P w ∧ ∃ o, MT t n X (setK a o w) := fun w => by
        rw [sr]
        exact and_congr Iff.rfl ⟨fun ⟨o, h⟩ => ⟨o, (mt _).mpr h⟩, fun ⟨o, h⟩ => ⟨o, (mt _).mp h⟩⟩
      rcases hY with rfl | ⟨rfl, emp⟩
      · refine ⟨_, ?_, Or.inr ⟨_, rfl, only.mpr ⟨restE, w₀, hw₀⟩, Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_,
          fun w => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rw [denD_map] at hq
          by_cases e : q.1.1 = "map"
          · exact e
          · simp [mapLookup, e, dn_none] at hq
        · rw [← sem]; simp [MT, mapLookup]
      · refine ⟨_, ?_, Or.inr ⟨_, rfl, only.mpr ⟨restE, w₀, hw₀⟩, Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_,
          fun w => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rw [denD_map] at hq
          simp [mapLookup, dn_none] at hq
        · rw [← sem, emp w]; simp [MT, mapLookup]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]


/-- `map_put_key/3` on static types of the next level and a static value: types holding only maps, some of them, give
the maps whose key holds a value of the type and that agree with one of their maps at the other keys; others give
`:badmap`. -/
theorem put_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_put_key/3» (D m) (.map X) (.atom a) v = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, res = .tuple #[.atom "ok", .map Y] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w)) := by
  have shared : Elixir.Module.Types.Descr.«map_put_key/3» (D m) (.map X) (.atom a) v =
      (do
        let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
          (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
          (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "false")
        match r with
        | .tuple ⟨[_, d, _]⟩ => pure (.tuple #[.atom "ok", d])
        | .tuple ⟨[.atom "error", _]⟩ => pure (.tuple #[.atom "ok", .map []])
        | .atom "badmap" => pure (.atom "badmap")
        | x => .error (.error (.tuple #[.atom "case_clause", x]))) := by
    unfold Elixir.Module.Types.Descr.«map_put_key/3» Elixir.Module.Types.Descr.«map_put_shared/3»
    rcases sv with rfl | ⟨Z, rfl, sZ⟩
    · simp [Term.list]
      rfl
    · simp [getMapKeys_single, sZ, Term.list]
      rfl
  obtain ⟨res, run, ⟨rfl, h⟩ | ⟨Y, rfl, h⟩⟩ := update_map hX a (leafPut_put (level t n).ef a hv) hm
  · exact ⟨_, by rw [shared, run]; rfl, Or.inl ⟨rfl, h⟩⟩
  · exact ⟨_, by rw [shared, run]; rfl, Or.inr ⟨Y, rfl, h⟩⟩

/-- `map_update/5` deleting a single atom key of static types of the next level: types holding only maps, some of
them, give the maps without the key that agree with one of their maps at the other keys; others give `:badmap`. -/
theorem del_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) (atomT a) (.atom "delete") (.atom "force")
        (.atom "false") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, res = .tuple #[.map [], .map Y, .nil] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ w (.atom a) = none ∧ ∃ o, MT t n X (setK a o w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨res, run, h⟩ := update_map hX a (leafPut_del (level t n).ef a) hm
  refine ⟨res, ?_, h⟩
  unfold Elixir.Module.Types.Descr.«map_update/5»
  simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem force_static_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (bdd : Term) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ T Y, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 4)) bdd (Term.list lines)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "true") (.atom "true") =
        .ok (.tuple #[T, Y, .nil, .atom "true"]) ∧ E T ∧
      (∀ x, den T x ↔ ∃ L ∈ lines, LongM den L a (some x)) ∧ PutMaps E den a (PutAt den v a) lines Y := by
  obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
  obtain ⟨bdds, rb, fb, sb⟩ := put_lines ef hn a (leafPut_put ef a hv) lines hl
  have rb : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "true") (.atom "true") =
      .ok (.tuple #[Term.list bdds, F]) := by simpa [boolAtom] using rb Bool.true F (fun _ => rF)
  obtain ⟨ty, o, rfl, hty⟩ := hF
  obtain ⟨T, hT, rT, sT⟩ := ef.opt_union [] (m := n + 3) hty ef.none (by omega)
  have nk₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[.map [], .nil, .nil, .atom "false"])
      (Term.list lines) (.cons (.atom a) .nil) (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"])
      (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
      .ok (.tuple #[T, Term.list bdds, .nil, .atom "true"]) := by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.lists.«foldl_1/3», Erlang.erlang.«is_function/2»,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
      Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», rb, Elixir.Module.Types.Descr.«opt_union/2», rT]
    rw [show (Term.nil) = Term.list [] from rfl, append_list]
    simp
  have nk₂ : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) acc (Term.list lines) .nil
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"])
      (.atom "false") (.atom "true") (.atom "true") (.atom "true") = .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«==/2», Erlang.erlang.«/=/2»,
    Lynx.Term.isMember, Erlang.erlang.«--/2», Erlang.erlang.«++/2», Erlang.erlang.«not/1», Term.list, Term.properList?, nk₁,
    nk₂, Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»,
    Erlang.lists.«map/2»]
  have semT : ∀ x, den T x ↔ ∃ L ∈ lines, LongM den L a (some x) := by
    intro x
    rw [sT, ← sF, fieldSem_mk]
    have nx : ¬den (.map []) x := fun h => (none_field (den := den) ef).2 (some x)
      (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, h⟩)
    simp [nx]
  obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 4) (by omega) (ok := fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bdds (Nat.le_refl _) fun b mb => ⟨fb b mb, by
      rcases fb b mb with ⟨k, rfl⟩ | wb
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr (wb.mono fun _ _ => trivial)⟩
  have sem : ∀ w, denMF E den r w = Bool.true ↔ PutAt den v a w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) :=
    fun w => (sr w).trans (sb w)
  by_cases bot : r = .atom "bdd_bot"
  · subst bot
    exact ⟨T, .map [], by simp [rr], hT, semT, .atom "bdd_bot", fr, Or.inr ⟨rfl, fun w => denMF_bot w⟩, sem⟩
  · refine ⟨T, .map [(.atom "map", r)], ?_, hT, semT, r, fr, Or.inl rfl, sem⟩
    simp only [rr, Lynx.Except.ok_bind]

/-- `map_update_static/5` forces a constant into a map field and returns the old values: `:badmap` when it is empty. -/
theorem force_update_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 4)) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "true") (.atom "true") =
        .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ T Y, res = .tuple #[T, Y, .nil, .atom "true"] ∧ (∃ w, denMF E den b w = Bool.true) ∧ E T ∧
          (∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = some x) ∧
          PutField E den a (PutAt den v a) b Y) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 4)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 4) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      obtain ⟨T, Y, rY, hT, sT, pY⟩ := force_static_dnf ef hn a hv (.tuple #[.integer k, tag, fieldsTerm l]) _ hl
      have inB : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔
          ∃ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], InMLine den L w := fun w => by
        rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
      refine ⟨_, ?_, Or.inr ⟨T, Y, rfl, ⟨w₀, (sem w₀).mpr h₀⟩, hT, fun x => ?_, putMaps_field inB pY⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
        simpa [Term.list] using rY
      · rw [sT]
        exact ⟨fun ⟨L, mL, w, hw, wa⟩ => ⟨w, (inB w).mpr ⟨L, mL, hw⟩, wa⟩,
          fun ⟨w, hw, wa⟩ => by obtain ⟨L, mL, hL⟩ := (inB w).mp hw; exact ⟨L, mL, w, hL, wa⟩⟩
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 4) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl (m := n + 4) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
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
      obtain ⟨T, Y, rY, hT, sT, pY⟩ := force_static_dnf ef hn a hv b (L :: rest) hl
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨T, Y, rfl, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, hT, fun x => ?_,
        putMaps_field inB pY⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · rw [sT]
        exact ⟨fun ⟨L', mL, w, hw, wa⟩ => ⟨w, (inB w).mpr ⟨L', mL, hw⟩, wa⟩,
          fun ⟨w, hw, wa⟩ => by obtain ⟨L', mL, hL⟩ := (inB w).mp hw; exact ⟨L', mL, w, hL, wa⟩⟩

section
variable {t : Term} {n : Nat}

/-- `map_update_unchecked/4` forcing a value at a key of static types of the next level and returning the old values:
types holding only maps, some of them, give the values of their maps at the key and the maps whose key holds a value of
the type that agree with one of their maps at the other keys; others give `:badmap`. -/
theorem force_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term}
    (hv : (level t n).E v) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ T Y, res = .tuple #[T, .map Y, .nil] ∧ MOnly t n X ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 4))
      (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[r] =
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
    have rE := next_empty dR (m := k + 4) (by omega)
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
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 4)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨T, Y, rfl, ⟨w₀, hw₀⟩, hT, sT, r, fr, hY, sr⟩⟩ :=
        force_update_static (level t n).ef (n := k) (by omega) a hv hb fb
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      have semT : ∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x := fun x => by
        rw [sT]; exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mpr hw, wa⟩, fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mp hw, wa⟩⟩
      have sem : ∀ w, denMF (level t n).E (level t n).den r w = Bool.true ↔
          PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w) := fun w => by
        rw [sr]
        exact and_congr Iff.rfl ⟨fun ⟨o, h⟩ => ⟨o, (mt _).mpr h⟩, fun ⟨o, h⟩ => ⟨o, (mt _).mp h⟩⟩
      rcases hY with rfl | ⟨rfl, emp⟩
      · refine ⟨_, ?_, Or.inr ⟨T, _, rfl, only.mpr ⟨restE, w₀, hw₀⟩, hT, semT, Or.inr ⟨_, rfl, descrC_map fr⟩,
          fun q hq => ?_, fun w => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rw [denD_map] at hq
          by_cases e : q.1.1 = "map"
          · exact e
          · simp [mapLookup, e, dn_none] at hq
        · rw [← sem]; simp [MT, mapLookup]
      · refine ⟨_, ?_, Or.inr ⟨T, _, rfl, only.mpr ⟨restE, w₀, hw₀⟩, hT, semT, Or.inr ⟨_, rfl, descrC_nil⟩,
          fun q hq => ?_, fun w => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rw [denD_map] at hq
          simp [mapLookup, dn_none] at hq
        · rw [← sem, emp w]; simp [MT, mapLookup]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]

/-- `map_update/5` forcing a static value at a single atom key, returning the old values. -/
theorem update_force {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term}
    (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) (atomT a) v (.atom "force") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ T Y, res = .tuple #[T, .map Y, .nil] ∧ MOnly t n X ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨res, run, h⟩ := force_map hX a hv hm
  refine ⟨res, ?_, h⟩
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rcases sv with rfl | ⟨Z, rfl, sZ⟩
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      Lynx.Term.getMapKeys]
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      getMapKeys_single, sZ]

end

/-- `map_split_key_line/5` on a non-empty line: the field of the key, the rest of the literal without the key, the
negated literals split at the key, and the accumulated field united with the values at the key of the line's maps. -/
theorem split_line (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {tag : Term}
    {l : List (Term × Term)} {negs : List Term} (g : TagV E tag) (sl : FieldsV E l) (lits : ∀ N ∈ negs, MapLitV E N)
    (ne : ∃ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w) {acc : Term} (ha : FieldValue E acc) :
    ∃ (k : Int) (P : List Term) (acc' : Term),
      Elixir.Module.Types.Descr.«map_split_key_line/5» (D (n + 2)) tag (fieldsTerm l) (Term.list negs) (.atom a) acc =
        .ok (.tuple #[acc', fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)], Term.list P]) ∧
      FieldValue E acc' ∧
      (∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨ LongM den (.tuple #[tag, fieldsTerm l, Term.list negs]) a o) ∧
      FieldValue E (fieldAt tag l a) ∧ MField E (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) ∧
      (∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true ↔
        MSem den tag (eraseKey a l) w) ∧
      (∀ p ∈ P, MPairOk E p ∧ RestOk E den a p) ∧
      ∀ w, (∃ N ∈ negs, NSem den N w) ↔ ∃ p ∈ P, MPairIn E den p (w (.atom a)) (eraseK a w) := by
  obtain ⟨w₀, hw₀⟩ := ne
  obtain ⟨hm₀, hn₀⟩ := inMLine_iff.mp hw₀
  obtain ⟨k, run, ⟨f, b, ef', hf, hb⟩, rest, -⟩ := pop_pair (den := den) ef g sl a
  simp only [Term.tuple.injEq] at ef'
  obtain ⟨rfl, rfl, -⟩ := ef'
  have split₀ := (msem_at ef g l a w₀).mp hm₀
  by_cases nn : negs = []
  · subst nn
    obtain ⟨t₁, o₁, e₁, h₁⟩ := hf
    obtain ⟨t₂, o₂, e₂, h₂⟩ := ha
    obtain ⟨c, hc, rc, sc⟩ := field_opt_union_val (den := den) ef (m := n + 2) (by omega) e₁ e₂ h₁ h₂ []
    refine ⟨k, [], .tuple #[c, boolAtom (o₁ || o₂)], ?_, ⟨c, _, rfl, hc⟩, fun o => ?_, ⟨t₁, o₁, e₁, h₁⟩, hb, rest,
      by simp, fun w => by simp⟩
    · simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run, rc, Term.list]
    · rw [sc, or_comm]
      refine or_congr Iff.rfl ⟨fun ho => long_of_rest ef a g (P := []) (by simp) (fun w => by simp) ho split₀.2
        (by simp), ?_⟩
      rintro ⟨w, hw, rfl⟩
      exact ((msem_at ef g l a w).mp (inMLine_iff.mp hw).1).1
  obtain ⟨N₀, negs₀, rfl⟩ : ∃ N₀ negs₀, negs = N₀ :: negs₀ := by
    cases negs with
    | nil => exact absurd rfl nn
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨r, rr, ⟨rfl, N, mN, hN⟩ | ⟨P, rfl, hP, sP⟩⟩ := msplit_negs (den := den) ef a (N₀ :: negs₀) lits []
  · exact absurd (hN w₀) (hn₀ N mN)
  simp only [List.append_nil] at rr
  have rr' := rr; simp only [Term.list] at rr'
  have restNe : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
    ⟨_, (rest _).mpr split₀.2⟩
  obtain ⟨s, acc', rk, hs₁, hs₂, hacc, sacc⟩ := mproj_value ef hn P (fun p mp => (hP p mp).1) hf hb restNe ha
  refine ⟨k, P, acc', ?_, hacc, fun o => ?_, hf, hb, rest, hP, sP⟩
  · cases s
    · obtain ⟨Q, rQ, rf⟩ := hs₂ rfl
      cases P with
      | nil => simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rk, rQ, rf, Lynx.Term.isMember, boolAtom,
          Term.list]
      | cons p P => simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rk, rQ, rf, Lynx.Term.isMember, boolAtom,
          Term.list]
    · cases P with
      | nil => simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rk, hs₁ rfl, Lynx.Term.isMember, boolAtom,
          Term.list]
      | cons p P => simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rk, hs₁ rfl, Lynx.Term.isMember, boolAtom,
          Term.list]
  · rw [sacc]
    refine or_congr Iff.rfl ⟨fun ⟨w', hf', hr', out⟩ => long_of_rest ef a g hP sP hf' ((rest w').mp hr') out, ?_⟩
    rintro ⟨w, hw, rfl⟩
    obtain ⟨hmw, hnw⟩ := inMLine_iff.mp hw
    obtain ⟨hfw, hrw⟩ := (msem_at ef g l a w).mp hmw
    exact ⟨eraseK a w, hfw, (rest _).mpr hrw, fun p mp hp => by
      obtain ⟨N, mN, hN⟩ := (sP w).mpr ⟨p, mp, hp⟩
      exact hnw N mN hN⟩

/-- The field of an absent key. -/
def absF : Term := .tuple #[.map [], .atom "true"]

/-- Maps of rests paired with a field. -/
def WithF (E : Term → Prop) (den : Term → V → Prop) (f : Term) (Q : List Term) (u : MW V) : Prop :=
  ∃ b, Term.tuple #[f, b] ∈ Q ∧ denMF E den b u = Bool.true

/-- Pairs of a new field or the absent field, whose rests have literals without a key. -/
def UpdQ (E : Term → Prop) (a : String) (new : Term) (keep : Bool) (Q : List Term) : Prop :=
  ∀ q ∈ Q, ∃ f b, q = .tuple #[f, b] ∧ (f = new ∨ (keep = Bool.true ∧ f = absF)) ∧ MField E b ∧ OField (LitA E a) b

theorem withF_cons {f g b : Term} {Q : List Term} {u : MW V} :
    WithF E den f (.tuple #[g, b] :: Q) u ↔ (f = g ∧ denMF E den b u = Bool.true) ∨ WithF E den f Q u := by
  constructor
  · rintro ⟨b', mb, hb⟩
    rcases List.mem_cons.mp mb with e | mb
    · obtain ⟨rfl, rfl⟩ : f = g ∧ b' = b := by simpa using e
      exact Or.inl ⟨rfl, hb⟩
    · exact Or.inr ⟨b', mb, hb⟩
  · rintro (⟨rfl, hb⟩ | ⟨b', mb, hb⟩)
    · exact ⟨b, List.mem_cons_self, hb⟩
    · exact ⟨b', List.mem_cons_of_mem _ mb, hb⟩

theorem withF_nil {f : Term} {u : MW V} : ¬WithF E den f [] u := fun ⟨_, m, _⟩ => by simp at m

theorem new_ne_absF {v : Term} : Term.tuple #[v, .atom "false"] ≠ absF := by
  intro h; simp [absF] at h

theorem withF_append {f : Term} {A B : List Term} {u : MW V} :
    WithF E den f (A ++ B) u ↔ WithF E den f A u ∨ WithF E den f B u := by
  constructor
  · rintro ⟨b, mb, hb⟩
    rcases List.mem_append.mp mb with mb | mb
    · exact Or.inl ⟨b, mb, hb⟩
    · exact Or.inr ⟨b, mb, hb⟩
  · rintro (⟨b, mb, hb⟩ | ⟨b, mb, hb⟩)
    · exact ⟨b, List.mem_append_left _ mb, hb⟩
    · exact ⟨b, List.mem_append_right _ mb, hb⟩

theorem withF_single {f g b : Term} {u : MW V} :
    WithF E den f [.tuple #[g, b]] u ↔ f = g ∧ denMF E den b u = Bool.true := by
  rw [withF_cons]; simp [withF_nil]

theorem mInPairs_append {A B : List Term} {y : Option V} {u : MW V} :
    MInPairs E den (A ++ B) y u ↔ MInPairs E den A y u ∨ MInPairs E den B y u := by
  simp only [MInPairs, List.mem_append]
  constructor
  · rintro ⟨p, mp | mp, hp⟩
    · exact Or.inl ⟨p, mp, hp⟩
    · exact Or.inr ⟨p, mp, hp⟩
  · rintro (⟨p, mp, hp⟩ | ⟨p, mp, hp⟩)
    · exact ⟨p, Or.inl mp, hp⟩
    · exact ⟨p, Or.inr mp, hp⟩

/-- The final fold of `map_update_project_pair/5`: pairs whose old type has values give the new field with their rest,
optional ones the absent field. -/
theorem upd_fold (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (a : String) {v : Term} (keep : Bool)
    (Q' : List Term) (hQ : MQOk E den Q') (kQ : KeepsQ (LitA E a) Q')
    (opt : ∀ q ∈ Q', ∀ t b, q = .tuple #[.tuple #[t, .atom "true"], b] → keep = Bool.true)
    (acc : List Term) (ha : UpdQ E a (.tuple #[v, .atom "false"]) keep acc) :
    ∃ Qf, Erlang.lists.«foldl/3» (D (n + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_update_project_pair/5-fun-0-" 2 #[.tuple #[v, .atom "false"]])
        (Term.list acc) (Term.list Q') = .ok (Term.list Qf) ∧ UpdQ E a (.tuple #[v, .atom "false"]) keep Qf ∧
      (∀ u, WithF E den (.tuple #[v, .atom "false"]) Qf u ↔
        WithF E den (.tuple #[v, .atom "false"]) acc u ∨ ∃ x, MInPairs E den Q' (some x) u) ∧
      (∀ u, WithF E den absF Qf u ↔ WithF E den absF acc u ∨ MInPairs E den Q' none u) := by
  obtain ⟨r, ⟨Qf, rfl, uQ, sN, sA⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr"
    "-map_update_project_pair/5-fun-0-" #[.tuple #[v, .atom "false"]]
    (fun pre r => ∃ Qf, r = Term.list Qf ∧ UpdQ E a (.tuple #[v, .atom "false"]) keep Qf ∧
      (∀ u, WithF E den (.tuple #[v, .atom "false"]) Qf u ↔
        WithF E den (.tuple #[v, .atom "false"]) acc u ∨ ∃ x, MInPairs E den pre (some x) u) ∧
      (∀ u, WithF E den absF Qf u ↔ WithF E den absF acc u ∨ MInPairs E den pre none u)) Q'
    (fun pre q r mq ⟨Qf, er, uQ, sN, sA⟩ => by
      subst er
      obtain ⟨f, b, rfl, ⟨t, o, rfl, ht⟩, fb, nb⟩ := hQ q mq
      obtain ⟨f', b', e', ob⟩ := kQ _ mq
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'
      obtain ⟨-, rfl⟩ := e'
      obtain ⟨eb, re, se⟩ := ef.empty1 (m := n) hn ht
      let Q₁ := (if o then [Term.tuple #[absF, b]] else []) ++
        ((if eb then [] else [Term.tuple #[.tuple #[v, .atom "false"], b]]) ++ Qf)
      have keepO : o = Bool.true → keep = Bool.true := fun h => opt _ mq t b (by subst h; rfl)
      refine ⟨Term.list Q₁, ⟨Q₁, rfl, fun q' mq' => ?_, fun u => ?_, fun u => ?_⟩, ?_⟩
      · simp only [Q₁, List.mem_append] at mq'
        rcases mq' with mq' | mq' | mq'
        · cases o
          · simp at mq'
          · simp at mq'; subst mq'; exact ⟨absF, b, rfl, Or.inr ⟨keepO rfl, rfl⟩, fb, ob⟩
        · cases eb
          · simp at mq'; subst mq'; exact ⟨_, b, rfl, Or.inl rfl, fb, ob⟩
          · simp at mq'
        · exact uQ q' mq'
      · have pin : ∀ x, MInPairs E den [.tuple #[.tuple #[t, boolAtom o], b]] (some x) u ↔
            den t x ∧ denMF E den b u = Bool.true := fun x => by
          simp only [MInPairs, List.mem_singleton, exists_eq_left, mpairIn_iff, fieldSem_mk]; simp
        have mid : WithF E den (.tuple #[v, .atom "false"])
            (if eb then [] else [Term.tuple #[.tuple #[v, .atom "false"], b]]) u ↔
            ∃ x, den t x ∧ denMF E den b u = Bool.true := by
          cases eb
          · simp only [Bool.false_eq_true, ↓reduceIte, withF_single]
            obtain ⟨x, hx⟩ : ∃ x, den t x := Classical.byContradiction fun h => by
              have := se.mpr fun v hv => h ⟨v, hv⟩
              cases this
            exact ⟨fun ⟨_, h⟩ => ⟨x, hx, h⟩, fun ⟨_, _, h⟩ => ⟨trivial, h⟩⟩
          · simp only [↓reduceIte]
            exact ⟨fun h => absurd h withF_nil, fun ⟨x, hx, _⟩ => absurd hx (se.mp rfl x)⟩
        have first : ¬WithF E den (.tuple #[v, .atom "false"]) (if o then [Term.tuple #[absF, b]] else []) u := by
          cases o
          · exact withF_nil
          · simp only [↓reduceIte, withF_single]; exact fun ⟨h, _⟩ => new_ne_absF h
        simp only [Q₁, withF_append, sN, mInPairs_append, pin]
        constructor
        · rintro (h | h | h | h)
          · exact absurd h first
          · exact Or.inr ⟨_, Or.inr ((mid.mp h).choose_spec)⟩
          · exact Or.inl h
          · obtain ⟨x, hx⟩ := h; exact Or.inr ⟨x, Or.inl hx⟩
        · rintro (h | ⟨x, h | h⟩)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr ⟨x, h⟩))
          · exact Or.inr (Or.inl (mid.mpr ⟨x, h⟩))
      · have pin : MInPairs E den [.tuple #[.tuple #[t, boolAtom o], b]] none u ↔
            o = Bool.true ∧ denMF E den b u = Bool.true := by
          simp only [MInPairs, List.mem_singleton, exists_eq_left, mpairIn_iff, fieldSem_mk]; simp
        have mid : ¬WithF E den absF (if eb then [] else [Term.tuple #[.tuple #[v, .atom "false"], b]]) u := by
          cases eb
          · simp only [Bool.false_eq_true, ↓reduceIte, withF_single]; exact fun ⟨h, _⟩ => new_ne_absF h.symm
          · exact withF_nil
        have first : WithF E den absF (if o then [Term.tuple #[absF, b]] else []) u ↔
            o = Bool.true ∧ denMF E den b u = Bool.true := by
          cases o
          · simp [withF_nil]
          · simp only [↓reduceIte, withF_single]
        simp only [Q₁, withF_append, sA, mInPairs_append, pin, first]
        constructor
        · rintro (h | h | h | h)
          · exact Or.inr (Or.inr h)
          · exact absurd h mid
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_project_pair/5-fun-0-/2».pure]
        cases o <;> cases eb <;>
          simp [Elixir.Module.Types.Descr.«-map_update_project_pair/5-fun-0-/3», re, Lynx.Term.isMember, boolAtom, Q₁, absF,
            Term.list])
    (Term.list acc) ⟨acc, rfl, ha, fun u => by simp [MInPairs], fun u => by simp [MInPairs]⟩
  exact ⟨Qf, run, uQ, sN, sA⟩

/-- `map_update_project_pair/5` updates the maps of a pair minus negated pairs whose key holds a value, and with
`keep_absent?`, keeps those without the key. -/
theorem project5 (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (P : List Term)
    (hP : ∀ p ∈ P, MPairOk E p ∧ RestOk E den a p) {t : Term} {o : Bool} {rest : Term} (ht : E t)
    (hr : MField E rest) (orest : OField (LitA E a) rest) (nr : ∃ w, denMF E den rest w = Bool.true)
    {v : Term} (hv : E v) (vne : ∃ x, den v x) (keep : Bool) :
    ∃ Q, Elixir.Module.Types.Descr.«map_update_project_pair/5» (D (n + 2)) (Term.list P) (.tuple #[t, boolAtom o]) rest
        (.tuple #[v, .atom "false"]) (boolAtom keep) = .ok (Term.list Q) ∧
      UpdQ E a (.tuple #[v, .atom "false"]) keep Q ∧
      (∀ u, WithF E den (.tuple #[v, .atom "false"]) Q u ↔
        ∃ x, den t x ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p (some x) u) ∧
      (∀ u, WithF E den absF Q u ↔
        keep = Bool.true ∧ o = Bool.true ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p none u) := by
  have hP' : ∀ p ∈ P, MPairOk E p := fun p mp => (hP p mp).1
  have kP : KeepsQ (LitA E a) P := fun p mp => by
    obtain ⟨⟨f, b, e, -, fb⟩, f', k', ntag, nl, e', -, -, na, -⟩ := hP p mp
    subst e'
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨_, _, rfl, oField_litA fb na⟩
  obtain ⟨b₀, rb₀, sb₀⟩ := field_empty_val (den := den) ef (m := n + 2) (by omega) (putFieldV hv)
  have b₀f : b₀ = Bool.false := by
    cases b₀
    · rfl
    · obtain ⟨x, hx⟩ := vne
      exact absurd ((putField_sem (some x)).mpr ⟨x, rfl, hx⟩) (sb₀.mp rfl (some x))
  subst b₀f
  obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 2) (by omega) ht
  obtain ⟨s₁, rs₁, ss₁⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' (field := .tuple #[t, .atom "false"])
    ⟨t, Bool.false, rfl, ht⟩
  have hA : FieldValue E absF := ⟨.map [], Bool.true, rfl, ef.none⟩
  obtain ⟨s₂, rs₂, ss₂⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' hA
  -- The shortcuts: the full rest with the new field, and with the absent field.
  let s₁₇ := !e && s₁
  let s₂₇ := keep && o && s₂
  let t₂ := if s₁₇ then Term.map [] else t
  let o₂ := if s₂₇ then Bool.false else (keep && o)
  let pairs₁ := (if s₂₇ then [Term.tuple #[absF, rest]] else []) ++
    (if s₁₇ then [Term.tuple #[.tuple #[v, .atom "false"], rest]] else [])
  have ht₂ : E t₂ := by simp only [t₂]; split; exact ef.none; exact ht
  obtain ⟨fe, rfe, sfe⟩ := field_empty_val (den := den) ef (m := n + 2) (by omega) (⟨t₂, o₂, rfl, ht₂⟩ : FieldValue E _)
  obtain ⟨Q', rQ', qQ', kQ', fQ', sQ'⟩ := mproject_pairs ef hn P hP' ⟨t₂, o₂, rfl, ht₂⟩ hr nr
  have up₁ : UpdQ E a (.tuple #[v, .atom "false"]) keep pairs₁ := by
    intro q mq
    simp only [pairs₁, List.mem_append] at mq
    rcases mq with mq | mq
    · by_cases h : s₂₇
      · rw [ite_eq_left h] at mq; rw [List.mem_singleton] at mq; subst mq
        refine ⟨absF, rest, rfl, Or.inr ⟨?_, rfl⟩, hr, orest⟩
        simp only [s₂₇, Bool.and_eq_true] at h; exact h.1.1
      · rw [ite_eq_right h] at mq; simp at mq
    · by_cases h : s₁₇
      · rw [ite_eq_left h] at mq; rw [List.mem_singleton] at mq; subst mq
        exact ⟨_, rest, rfl, Or.inl rfl, hr, orest⟩
      · rw [ite_eq_right h] at mq; simp at mq
  have opt : ∀ q ∈ Q', ∀ t' b, q = .tuple #[.tuple #[t', .atom "true"], b] → keep = Bool.true := by
    intro q mq t' b eq
    obtain ⟨f, b', e', -, -, w, hw⟩ := qQ' q mq
    subst eq
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'
    obtain ⟨rfl, rfl⟩ := e'
    have := ((sQ' none w).mp ⟨_, mq, mpairIn_iff.mpr ⟨by
      rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; exact Or.inl ⟨rfl, rfl⟩, hw⟩⟩).1
    rw [fieldSem_mk] at this
    rcases this with ⟨-, h⟩ | ⟨x, h, -⟩
    · simp only [o₂] at h; split at h
      · cases h
      · simp only [Bool.and_eq_true] at h; exact h.1
    · cases h
  obtain ⟨Qf, rQf, uQf, sNf, sAf⟩ := upd_fold ef (n := n + 1) (by omega) a keep Q' qQ' (kQ' _ orest kP) opt pairs₁ up₁
  have nonx : ∀ x, ¬den (.map []) x := fun x h => (none_field (den := den) ef).2 (some x)
    (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, h⟩)
  have pres₁ : ∀ u, WithF E den (.tuple #[v, .atom "false"]) pairs₁ u ↔ s₁₇ = Bool.true ∧
      denMF E den rest u = Bool.true := fun u => by
    simp only [pairs₁, withF_append]
    have h₁ : ¬WithF E den (.tuple #[v, .atom "false"]) (if s₂₇ then [Term.tuple #[absF, rest]] else []) u := by
      by_cases h : s₂₇
      · simp only [h, ↓reduceIte, withF_single]; exact fun ⟨e, _⟩ => new_ne_absF e
      · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact withF_nil
    by_cases h : s₁₇
    · simp only [h, ↓reduceIte, withF_single, true_and]; exact ⟨fun h' => h'.elim (absurd · h₁) id, Or.inr⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
      exact fun h' => h'.elim h₁ withF_nil
  have abs₁ : ∀ u, WithF E den absF pairs₁ u ↔ s₂₇ = Bool.true ∧ denMF E den rest u = Bool.true := fun u => by
    simp only [pairs₁, withF_append]
    have h₂ : ¬WithF E den absF (if s₁₇ then [Term.tuple #[.tuple #[v, .atom "false"], rest]] else []) u := by
      by_cases h : s₁₇
      · simp only [h, ↓reduceIte, withF_single]; exact fun ⟨e, _⟩ => new_ne_absF e.symm
      · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact withF_nil
    by_cases h : s₂₇
    · simp only [h, ↓reduceIte, withF_single, true_and]; exact ⟨fun h' => h'.elim id (absurd · h₂), Or.inl⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
      try exact fun h' => h'.elim withF_nil h₂
  have f₂ : ∀ y, FieldSem den (.tuple #[t₂, boolAtom o₂]) y ↔
      (∃ x, y = some x ∧ s₁₇ = Bool.false ∧ den t x) ∨ (y = none ∧ o₂ = Bool.true) := fun y => by
    rw [fieldSem_mk]
    by_cases h : s₁₇
    · simp only [t₂, h, ↓reduceIte]
      constructor
      · rintro (⟨rfl, h'⟩ | ⟨x, rfl, hx⟩)
        · exact Or.inr ⟨rfl, h'⟩
        · exact absurd hx (nonx x)
      · rintro (⟨x, -, e, -⟩ | ⟨rfl, h'⟩)
        · cases e
        · exact Or.inl ⟨rfl, h'⟩
    · simp only [t₂, h, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (⟨rfl, h'⟩ | ⟨x, rfl, hx⟩)
        · exact Or.inr ⟨rfl, h'⟩
        · exact Or.inl ⟨x, rfl, by simp, hx⟩
      · rintro (⟨x, rfl, -, hx⟩ | ⟨rfl, h'⟩)
        · exact Or.inr ⟨x, rfl, hx⟩
        · exact Or.inl ⟨rfl, h'⟩
  -- The witness of the first shortcut: a value of the old type outside every negated pair.
  have short₁ : s₁₇ = Bool.true → ∃ x, den t x ∧ ∀ u, ∀ p ∈ P, ¬MPairIn E den p (some x) u := fun h => by
    simp only [s₁₇, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨o₀, h₀, out⟩ := ss₁.mp h.2
    obtain ⟨x, rfl, hx⟩ := (putField_sem o₀).mp h₀
    exact ⟨x, hx, fun u p mp ⟨f, nb, e, hf, _⟩ => out p mp f nb e hf⟩
  have short₂ : s₂₇ = Bool.true → keep = Bool.true ∧ o = Bool.true ∧ ∀ u, ∀ p ∈ P, ¬MPairIn E den p none u := by
    intro h
    simp only [s₂₇, Bool.and_eq_true] at h
    obtain ⟨o₀, h₀, out⟩ := ss₂.mp h.2
    rw [absF, delField_sem ef] at h₀
    subst h₀
    exact ⟨h.1.1, h.1.2, fun u p mp ⟨f, nb, e, hf, _⟩ => out p mp f nb e hf⟩
  refine ⟨if fe then pairs₁ else Qf, ?_, ?_, ?_, ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_update_project_pair/5»
    have rs₁ : Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (n + 2)) (Term.list P)
        (.tuple #[t, .atom "false"]) = .ok (boolAtom s₁) := rs₁
    have rs₂ : Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (n + 2)) (Term.list P)
        absF = .ok (boolAtom s₂) := rs₂
    simp only [s₁₇, s₂₇, t₂, o₂, pairs₁, absF] at rfe rQ' rQf rs₂
    clear ss₁ ss₂ sQ' sNf sAf se sfe sb₀ uQf up₁ opt qQ' kQ' fQ' hP hP' kP
    cases fe <;> cases e <;> cases s₁ <;> cases keep <;> cases o <;> cases s₂ <;>
      simp only [Bool.not_false, Bool.not_true, Bool.and_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, boolAtom, s₁₇, s₂₇, pairs₁,
        List.cons_append, Term.list] at rfe rQ' rQf rs₁ rs₂ ⊢ <;>
      simp [rb₀, re, rs₁, rs₂, rfe, rQ', rQf, Lynx.Term.isMember, boolAtom, Lynx.Except.andAlso, absF]
  · cases fe
    · exact uQf
    · exact up₁
  · intro u
    cases fe
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sNf, pres₁]
      constructor
      · rintro (⟨h, hr⟩ | ⟨x, hx⟩)
        · obtain ⟨x, hx, out⟩ := short₁ h
          exact ⟨x, hx, hr, fun p mp => out u p mp⟩
        · obtain ⟨hf, hr, out⟩ := (sQ' _ u).mp hx
          obtain ⟨x', e, -, hx'⟩ | ⟨e, -⟩ := (f₂ _).mp hf
          · obtain rfl : x = x' := Option.some.inj e
            exact ⟨x, hx', hr, out⟩
          · cases e
      · rintro ⟨x, hx, hr, out⟩
        by_cases h : s₁₇
        · exact Or.inl ⟨h, hr⟩
        · exact Or.inr ⟨x, (sQ' _ u).mpr ⟨(f₂ _).mpr (Or.inl ⟨x, rfl, by simpa using h, hx⟩), hr, out⟩⟩
    · simp only [↓reduceIte]
      rw [pres₁]
      constructor
      · rintro ⟨h, hr⟩
        obtain ⟨x, hx, out⟩ := short₁ h
        exact ⟨x, hx, hr, fun p mp => out u p mp⟩
      · rintro ⟨x, hx, hr, out⟩
        by_cases h : s₁₇
        · exact ⟨h, hr⟩
        · exact absurd ((f₂ _).mpr (Or.inl ⟨x, rfl, by simpa using h, hx⟩)) (sfe.mp rfl (some x))
  · intro u
    have o₂e : o₂ = Bool.true ↔ s₂₇ = Bool.false ∧ keep = Bool.true ∧ o = Bool.true := by
      simp only [o₂]
      by_cases h : s₂₇
      · simp [h]
      · simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, true_and]; try simpa using h
    cases fe
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sAf, abs₁]
      constructor
      · rintro (⟨h, hr⟩ | hx)
        · obtain ⟨hk, ho, out⟩ := short₂ h
          exact ⟨hk, ho, hr, fun p mp => out u p mp⟩
        · obtain ⟨hf, hr, out⟩ := (sQ' _ u).mp hx
          obtain ⟨x, e, -⟩ | ⟨-, h⟩ := (f₂ _).mp hf
          · cases e
          · obtain ⟨-, hk, ho⟩ := o₂e.mp h
            exact ⟨hk, ho, hr, out⟩
      · rintro ⟨hk, ho, hr, out⟩
        by_cases h : s₂₇
        · exact Or.inl ⟨h, hr⟩
        · exact Or.inr ((sQ' _ u).mpr ⟨(f₂ _).mpr (Or.inr ⟨rfl, o₂e.mpr ⟨by simpa using h, hk, ho⟩⟩), hr, out⟩)
    · simp only [↓reduceIte]
      rw [abs₁]
      constructor
      · rintro ⟨h, hr⟩
        obtain ⟨hk, ho, out⟩ := short₂ h
        exact ⟨hk, ho, hr, fun p mp => out u p mp⟩
      · rintro ⟨hk, ho, hr, out⟩
        by_cases h : s₂₇
        · exact ⟨h, hr⟩
        · exact absurd ((f₂ _).mpr (Or.inr ⟨rfl, o₂e.mpr ⟨by simpa using h, hk, ho⟩⟩)) (sfe.mp rfl none)

theorem tuple2_exact {a₀ a₁ b : Term} (e : compareExact (fuel (.tuple #[a₀, a₁]) b) (.tuple #[a₀, a₁]) b = .eq) :
    ∃ b₀ b₁, b = .tuple #[b₀, b₁] ∧ compareExact (fuel a₀ b₀) a₀ b₀ = .eq ∧ compareExact (fuel a₁ b₁) a₁ b₁ = .eq := by
  rw [compareExact_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, rest⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, rfl, e.1, e.2⟩

/-- The new field and the absent field are distinct keys. -/
theorem new_absF_apart (v : Term) :
    compareExact (fuel (.tuple #[v, .atom "false"]) absF) (.tuple #[v, .atom "false"]) absF ≠ .eq := by
  intro e
  obtain ⟨b₀, b₁, eb, -, e₁⟩ := tuple2_exact e
  simp only [absF, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eb
  obtain ⟨-, rfl⟩ := eb
  simp at e₁

theorem absF_new_apart (v : Term) :
    compareExact (fuel absF (.tuple #[v, .atom "false"])) absF (.tuple #[v, .atom "false"]) ≠ .eq := by
  intro e
  obtain ⟨b₀, b₁, eb, -, e₁⟩ := tuple2_exact e
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eb
  obtain ⟨-, rfl⟩ := eb
  simp at e₁

/-- Uniting rests without a key and putting a field there: the maps the field accepts whose other keys are those of
one of the rests. -/
theorem put_rests (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a : String) {v ov : Term} {P : MW V → Prop}
    (lp : LeafPut E den a v ov P) (rs : List Term) (hrs : ∀ b ∈ rs, MField E b ∧ OField (LitA E a) b) :
    ∃ r', (do
        let u ← Elixir.Module.Types.Descr.«map_union_all/1» (D m) (Term.list rs)
        Elixir.Module.Types.Descr.«map_put_key_bdd/5» u (.atom a) v ov (.atom "false")) = .ok r' ∧ MField E r' ∧
      ∀ w, denMF E den r' w = Bool.true ↔ P w ∧ ∃ b ∈ rs, denMF E den b (eraseK a w) = Bool.true := by
  obtain ⟨r, rr, -, kr, sr⟩ := munion_all (den := den) ef hm (mergeOk_litA a) _ rs (Nat.le_refl _) hrs
  rcases kr with ⟨k, rfl⟩ | wr
  · obtain ⟨lit', run, ml', il', sem⟩ := lp.top k
    obtain ⟨k', x, y, rfl⟩ := il'
    refine ⟨_, ?_, Or.inr (Bdd.leaf_iff.mpr ml'), fun w => ?_⟩
    · simp [rr, Elixir.Module.Types.Descr.«map_put_key_bdd/5», run]
    · have top := (sr (eraseK a w)).mp (by simp [denMF_top])
      rw [denMF_bdd (Bdd.leaf_iff.mpr ml'), eval_leaf, sem, bp_true]
      exact ⟨fun h => ⟨h, top⟩, fun h => h.1⟩
  obtain ⟨r', run, wr', sem⟩ := put_bdd a lp _ r wr (fun _ h => h) Bool.false
  have wr₀ : Bdd (MLit E) r := wr.mono fun _ h => h.1
  refine ⟨r', ?_, Or.inr wr', fun w => ?_⟩
  · simpa [rr] using run
  · rw [denMF_bdd wr', ← sr, denMF_bdd wr₀]
    by_cases hp : P w
    · rw [(sem w).1 hp]; simp [hp]
    · rw [(sem w).2 rfl hp]; simp [hp]

/-- The fields of updates: the new field or the absent one. -/
def UKey (v f : Term) : Prop := f = .tuple #[v, .atom "false"] ∨ f = absF

theorem keyed_apart {v f g : Term} (hf : UKey v f) (hg : UKey v g) (ne : f ≠ g) :
    compareExact (fuel g f) g f ≠ .eq := by
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
  · exact absurd rfl ne
  · exact absF_new_apart v
  · exact new_absF_apart v
  · exact absurd rfl ne

theorem lookup_same {f val : Term} {es : List (Term × Term)} : mapLookup ((f, val) :: es) f = some val := by
  simp [mapLookup]

theorem lookup_other {v f g val : Term} {es : List (Term × Term)} (hf : UKey v f) (hg : UKey v g) (ne : f ≠ g) :
    mapLookup ((f, val) :: es) g = mapLookup es g := by
  simp [mapLookup, keyed_apart hf hg ne]

/-- Groups of rests by field: every binding names a field of updates and rests of pairs with that field, and every
pair is found by its field. -/
def GInv (v : Term) (pre : List Term) (entries : List (Term × Term)) : Prop :=
  (∀ e ∈ entries, UKey v e.1 ∧ ∃ rs, e.2 = Term.list rs ∧ ∀ b ∈ rs, Term.tuple #[e.1, b] ∈ pre) ∧
  ∀ f b, Term.tuple #[f, b] ∈ pre → ∃ rs, mapLookup entries f = some (Term.list rs) ∧ b ∈ rs

/-- The grouping fold of `map_update_named_key/5`. -/
theorem group_fold {v : Term} (m : Nat) (pairs : List Term)
    (hp : ∀ q ∈ pairs, ∃ f b, q = .tuple #[f, b] ∧ UKey v f) :
    ∃ entries, Erlang.lists.«foldl/3» (D m) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[])
        (.map []) (Term.list pairs) = .ok (.map entries) ∧ GInv v pairs entries := by
  obtain ⟨r, ⟨-, entries, rfl, inv⟩, run⟩ := foldl_rel_at (m := m) "Elixir.Module.Types.Descr"
    "-map_update_named_key/5-fun-1-" #[]
    (fun pre r => (∀ q ∈ pre, ∃ f b, q = .tuple #[f, b] ∧ UKey v f) ∧ ∃ entries, r = .map entries ∧ GInv v pre entries)
    pairs
    (fun pre q r mq ⟨kp, entries, er, ⟨h₁, h₂⟩⟩ => by
      subst er
      obtain ⟨f, b, rfl, kf⟩ := hp q mq
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_key/5-fun-1-/2».pure]
      -- The rests already grouped under the field, if any.
      obtain ⟨rs, hl, hrs⟩ : ∃ rs : List Term, (mapLookup entries f = some (Term.list rs) ∨
          (mapLookup entries f = none ∧ rs = [])) ∧ ∀ b' ∈ rs, Term.tuple #[f, b'] ∈ pre := by
        cases hlk : mapLookup entries f with
        | none => exact ⟨[], Or.inr ⟨rfl, rfl⟩, by simp⟩
        | some val =>
          obtain ⟨e, me, ee, rfl⟩ : ∃ e ∈ entries, compareExact (fuel f e.1) f e.1 = .eq ∧ e.2 = val := by
            simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at hlk
            obtain ⟨e, he, rfl⟩ := hlk
            exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩
          obtain ⟨ke, rs, hv, hb⟩ := h₁ e me
          have : e.1 = f := Classical.byContradiction fun ne => keyed_apart ke kf ne ee
          rw [this] at hb
          exact ⟨rs, Or.inl (by rw [hv]), hb⟩
      refine ⟨Term.map ((f, Term.list (b :: rs)) :: entries), ⟨fun q' mq' => ?_, _, rfl, fun e me => ?_,
        fun g b' mb => ?_⟩, ?_⟩
      · rcases List.mem_append.mp mq' with mq' | mq'
        · exact kp q' mq'
        · rw [List.mem_singleton] at mq'; exact ⟨f, b, mq', kf⟩
      · rcases List.mem_cons.mp me with rfl | me
        · refine ⟨kf, b :: rs, rfl, fun b'' mb'' => ?_⟩
          rcases List.mem_cons.mp mb'' with rfl | mb''
          · exact List.mem_append_right _ (List.mem_singleton_self _)
          · exact List.mem_append_left _ (hrs b'' mb'')
        · obtain ⟨ke, rs', hv, hb⟩ := h₁ e me
          exact ⟨ke, rs', hv, fun b'' mb'' => List.mem_append_left _ (hb b'' mb'')⟩
      · rcases List.mem_append.mp mb with mb | mb
        · obtain ⟨f', b'', e', kg⟩ := kp _ mb
          simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'
          obtain ⟨rfl, rfl⟩ := e'
          obtain ⟨rs₀, hl₀, mb₀⟩ := h₂ g b' mb
          by_cases e : f = g
          · subst e
            rcases hl with hl | ⟨hl, -⟩
            · rw [hl₀] at hl
              have e₁ := congrArg Term.properList? (Option.some.inj hl)
              simp only [Term.properList?_list, Option.some.injEq] at e₁
              exact ⟨b :: rs, lookup_same, List.mem_cons_of_mem _ (e₁ ▸ mb₀)⟩
            · rw [hl₀] at hl; cases hl
          · exact ⟨rs₀, by rw [lookup_other kf kg e, hl₀], mb₀⟩
        · rw [List.mem_singleton] at mb
          simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at mb
          rw [mb.1, mb.2]
          exact ⟨b :: rs, lookup_same, List.mem_cons_self⟩
      · rcases hl with hl | ⟨hl, rfl⟩
        · have found : (entries.find? fun entry => decide (compareExact (fuel f entry.1) f entry.1 = .eq)).isSome := by
            simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at hl
            obtain ⟨e, he, -⟩ := hl
            simp [he]
          simp [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-1-/2», getMapKeys_single, hl,
            Erlang.erlang.«is_map/1», Erlang.maps.«update/3», found, Term.list]
        · simp [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-1-/2», getMapKeys_single, hl,
            Erlang.maps.«put/3», Term.list])
    (.map []) ⟨by simp, [], rfl, by simp, by simp⟩
  exact ⟨entries, run, inv⟩

/-- The puts of `map_update_named_key/5` over groups of rests: the new field into the rests of present keys, and the
absent field into the rests of absent ones. -/
theorem group_bdds (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a : String) {v : Term} (hv : E v)
    {keep : Bool} (pairs : List Term) (hp : UpdQ E a (.tuple #[v, .atom "false"]) keep pairs)
    (entries : List (Term × Term)) (inv : GInv v pairs entries) :
    ∃ bdds, Erlang.lists.«map/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
        #[.atom a]) (Term.list ((mapEntries entries).map fun e => .tuple #[e.1, e.2])) = .ok (Term.list bdds) ∧
      (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        (PutAt den v a w ∧ WithF E den (.tuple #[v, .atom "false"]) pairs (eraseK a w)) ∨
        (w (.atom a) = none ∧ WithF E den absF pairs (eraseK a w)) := by
  classical
  have each : ∀ x ∈ (mapEntries entries).map (fun e => Term.tuple #[e.1, e.2]), ∃ r,
      (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1 #[.atom a]) #[x] =
        .ok r ∧ MField E r ∧ ∃ e ∈ mapEntries entries, x = .tuple #[e.1, e.2] ∧ ∃ rs, e.2 = Term.list rs ∧
          ∀ w, denMF E den r w = Bool.true ↔
            ((e.1 = .tuple #[v, .atom "false"] ∧ PutAt den v a w) ∨ (e.1 = absF ∧ w (.atom a) = none)) ∧
            ∃ b ∈ rs, denMF E den b (eraseK a w) = Bool.true := by
    intro x mx
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
    obtain ⟨ke, rs, hv', hb⟩ := (inv.1 e (mem_of_mem_mapEntries me))
    have hrs : ∀ b ∈ rs, MField E b ∧ OField (LitA E a) b := fun b mb => by
      obtain ⟨f, b', eq, -, fb, ob⟩ := hp _ (hb b mb)
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eq
      obtain ⟨-, rfl⟩ := eq
      exact ⟨fb, ob⟩
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_key/5-fun-2-/1».pure]
    rcases ke with ke | ke
    · obtain ⟨r, rr, fr, sr⟩ := put_rests ef hm a (leafPut_put ef a hv) rs hrs
      refine ⟨r, ?_, fr, e, me, rfl, rs, hv', fun w => ?_⟩
      · rw [ke, hv']; simpa [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-2-/2»] using rr
      · rw [sr]
        exact ⟨fun ⟨h₁, h₂⟩ => ⟨Or.inl ⟨ke, h₁⟩, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.elim (·.2) fun ⟨h, _⟩ =>
          absurd (ke.symm.trans h) new_ne_absF, h₂⟩⟩
    · obtain ⟨r, rr, fr, sr⟩ := put_rests ef hm a (leafPut_del ef a) rs hrs
      refine ⟨r, ?_, fr, e, me, rfl, rs, hv', fun w => ?_⟩
      · rw [ke, hv']; simpa [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-2-/2», absF] using rr
      · rw [sr]
        exact ⟨fun ⟨h₁, h₂⟩ => ⟨Or.inr ⟨ke, h₁⟩, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.elim (fun ⟨h, _⟩ =>
          absurd (h.symm.trans ke) new_ne_absF) (·.2), h₂⟩⟩
  let g : Term → Term := fun x => if hx : x ∈ (mapEntries entries).map (fun e => Term.tuple #[e.1, e.2]) then
    Classical.choose (each x hx) else .nil
  have hg : ∀ x ∈ (mapEntries entries).map (fun e => Term.tuple #[e.1, e.2]),
      (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1 #[.atom a]) #[x] =
        .ok (g x) ∧ MField E (g x) ∧ ∃ e ∈ mapEntries entries, x = .tuple #[e.1, e.2] ∧ ∃ rs, e.2 = Term.list rs ∧
          ∀ w, denMF E den (g x) w = Bool.true ↔
            ((e.1 = .tuple #[v, .atom "false"] ∧ PutAt den v a w) ∨ (e.1 = absF ∧ w (.atom a) = none)) ∧
            ∃ b ∈ rs, denMF E den b (eraseK a w) = Bool.true := fun x hx => by
    simp only [g, dite_eq_left hx]
    exact Classical.choose_spec (each x hx)
  refine ⟨((mapEntries entries).map fun e => Term.tuple #[e.1, e.2]).map g,
    map_list _ _ _ _ g _ fun x hx => (hg x hx).1, fun b mb => ?_, fun w => ?_⟩
  · obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mb
    exact (hg x mx).2.1
  -- The rests of a field, found among the enumerated bindings.
  have find : ∀ f b', UKey v f → Term.tuple #[f, b'] ∈ pairs → ∃ x ∈ (mapEntries entries).map
      (fun e => Term.tuple #[e.1, e.2]), ∃ rs, x = .tuple #[f, Term.list rs] ∧ b' ∈ rs := by
    intro f b' kf mb
    obtain ⟨rs, hl, mr⟩ := inv.2 f b' mb
    rw [← mapLookup_mapEntries] at hl
    simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at hl
    obtain ⟨e, he, ee⟩ := hl
    have me := List.mem_of_find?_eq_some he
    have ce : compareExact (fuel f e.1) f e.1 = .eq := by simpa using List.find?_some he
    have : e.1 = f := Classical.byContradiction fun ne =>
      keyed_apart (inv.1 e (mem_of_mem_mapEntries me)).1 kf ne ce
    exact ⟨_, List.mem_map.mpr ⟨e, me, rfl⟩, rs, by rw [this, ee], mr⟩
  have unlist : ∀ {xs ys : List Term}, Term.list xs = Term.list ys → xs = ys := fun h => by
    have := congrArg Term.properList? h
    simpa [Term.properList?_list] using this
  constructor
  · rintro ⟨b, mb, hb⟩
    obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mb
    obtain ⟨-, -, e, me, rfl, rs, hrs, sem⟩ := hg x mx
    obtain ⟨⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩, b', mb', hb'⟩ := (sem w).mp hb
    all_goals
      obtain ⟨-, rs', hrs', inp⟩ := inv.1 e (mem_of_mem_mapEntries me)
      rw [hrs] at hrs'
      obtain rfl := unlist hrs'
    · exact Or.inl ⟨h₁', b', by rw [← h₁]; exact inp b' mb', hb'⟩
    · exact Or.inr ⟨h₁', b', by rw [← h₁]; exact inp b' mb', hb'⟩
  · have back : ∀ f b', UKey v f → Term.tuple #[f, b'] ∈ pairs → denMF E den b' (eraseK a w) = Bool.true →
        ((f = .tuple #[v, .atom "false"] ∧ PutAt den v a w) ∨ (f = absF ∧ w (.atom a) = none)) →
        ∃ b ∈ ((mapEntries entries).map fun e => Term.tuple #[e.1, e.2]).map g, denMF E den b w = Bool.true := by
      intro f b' kf mb' hb' hf
      obtain ⟨x, mx, rs, rfl, mr⟩ := find f b' kf mb'
      obtain ⟨-, -, e, me, ex, rs', hrs, sem⟩ := hg _ mx
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at ex
      obtain ⟨e₁, e₂⟩ := ex
      rw [← e₂] at hrs
      obtain rfl := unlist hrs
      refine ⟨_, List.mem_map.mpr ⟨_, mx, rfl⟩, (sem w).mpr ⟨?_, b', mr, hb'⟩⟩
      rw [← e₁]; exact hf
    rintro (⟨hp', b', mb', hb'⟩ | ⟨hn, b', mb', hb'⟩)
    · exact back _ b' (Or.inl rfl) mb' hb' (Or.inl ⟨rfl, hp'⟩)
    · exact back _ b' (Or.inr rfl) mb' hb' (Or.inr ⟨rfl, hn⟩)


/-- The mode atom of `:keep` and `:reject`. -/
def modeT (keep : Bool) : Term := .atom (if keep then "keep" else "reject")

/-- One line of the general clause of `map_update_named_key/5` with a constant: the pairs of the line's maps whose
key holds a value, as maps with the key removed, and with `:keep`, of those without the key. -/
theorem line_pairs (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) {tag : Term} {l : List (Term × Term)} {negs : List Term} (g : TagV E tag)
    (sl : FieldsV E l) (lits : ∀ N ∈ negs, MapLitV E N)
    (ne : ∃ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w) {acc : Term} (ha : FieldValue E acc) :
    ∃ (k : Int) (P : List Term) (acc' : Term) (Q : List Term),
      Elixir.Module.Types.Descr.«map_split_key_line/5» (D (n + 2)) tag (fieldsTerm l) (Term.list negs) (.atom a) acc =
        .ok (.tuple #[acc', fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)], Term.list P]) ∧
      Elixir.Module.Types.Descr.«map_update_prepare_pairs/4» (D (n + 2)) (Term.list P) (fieldAt tag l a)
        (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) = .ok (Term.list Q) ∧
      FieldValue E acc' ∧
      (∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨ LongM den (.tuple #[tag, fieldsTerm l, Term.list negs]) a o) ∧
      UpdQ E a (.tuple #[v, .atom "false"]) keep Q ∧
      (∀ w, WithF E den (.tuple #[v, .atom "false"]) Q (eraseK a w) ↔
        ∃ x, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a (some x) w)) ∧
      (∀ w, WithF E den absF Q (eraseK a w) ↔
        keep = Bool.true ∧ InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a none w)) := by
  obtain ⟨k, P, acc', run, hacc, sacc, hf, hb, rest, hP, sP⟩ := split_line ef hn a g sl lits ne ha
  obtain ⟨w₀, hw₀⟩ := ne
  have nr : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
    ⟨_, (rest _).mpr ((msem_at ef g l a w₀).mp (inMLine_iff.mp hw₀).1).2⟩
  have orest := oField_litA hb (a := a) (by simp [lookup_eraseKey])
  obtain ⟨t, o, ef', ht⟩ := hf
  obtain ⟨Q, rQ, uQ, sN, sA⟩ := project5 ef hn a P hP ht hb orest nr hv vne keep
  have line : ∀ w o', InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a o' w) ↔
      FieldSem den (.tuple #[t, boolAtom o]) o' ∧
        denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) (eraseK a w) = Bool.true ∧
        ∀ p ∈ P, ¬MPairIn E den p o' (eraseK a w) := by
    intro w o'
    rw [inMLine_iff, msem_at ef g l a, ← ef', rest, eraseK_setK, and_assoc]
    simp only [setK, ite_true]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h p mp hp => ?_, fun h N mN hN => ?_⟩)
    · obtain ⟨N, mN, hN⟩ := (sP (setK a o' w)).mpr ⟨p, mp, by simpa [setK, eraseK_setK] using hp⟩
      exact h N mN (by simpa [setK] using hN)
    · obtain ⟨p, mp, hp⟩ := (sP (setK a o' w)).mp (by simpa [setK] using ⟨N, mN, hN⟩)
      exact h p mp (by simpa [setK, eraseK_setK] using hp)
  refine ⟨k, P, acc', Q, run, ?_, hacc, sacc, uQ, fun w => ?_, fun w => ?_⟩
  · rw [ef']
    cases keep
    · simpa [Elixir.Module.Types.Descr.«map_update_prepare_pairs/4», modeT, boolAtom] using rQ
    · simpa [Elixir.Module.Types.Descr.«map_update_prepare_pairs/4», modeT, boolAtom] using rQ
  · rw [sN]
    refine ⟨fun ⟨x, hx, hr, out⟩ => ⟨x, (line w (some x)).mpr ⟨?_, hr, out⟩⟩, fun ⟨x, hx⟩ => ?_⟩
    · rw [fieldSem_mk]; exact Or.inr ⟨x, rfl, hx⟩
    · obtain ⟨hf', hr, out⟩ := (line w (some x)).mp hx
      rw [fieldSem_mk] at hf'
      rcases hf' with ⟨h, -⟩ | ⟨x', e, hx'⟩
      · cases h
      · cases e; exact ⟨x, hx', hr, out⟩
  · rw [sA, line, fieldSem_mk]
    constructor
    · rintro ⟨hk, ho, hr, out⟩; exact ⟨hk, Or.inl ⟨rfl, ho⟩, hr, out⟩
    · rintro ⟨hk, ⟨-, ho⟩ | ⟨x, e, -⟩, hr, out⟩
      · exact ⟨hk, ho, hr, out⟩
      · cases e

/-- The line fold of the general clause of `map_update_named_key/5`. -/
theorem keep_fold (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ (pr : List Term) (F : Term), Erlang.lists.«foldl/3» (D (n + 3))
        (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-0-" 2
          #[.atom a, .tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]])
        (.tuple #[.nil, .tuple #[.map [], .atom "false"]]) (Term.list lines) = .ok (.tuple #[Term.list pr, F]) ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) ∧
      UpdQ E a (.tuple #[v, .atom "false"]) keep pr ∧
      (∀ w, WithF E den (.tuple #[v, .atom "false"]) pr (eraseK a w) ↔
        ∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∧
      (∀ w, WithF E den absF pr (eraseK a w) ↔ keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L (setK a none w)) := by
  obtain ⟨r, ⟨pr, F, rfl, hF, sF, uQ, sN, sA⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr"
    "-map_update_named_key/5-fun-0-" #[.atom a, .tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]]
    (fun pre r => ∃ (pr : List Term) (F : Term), r = .tuple #[Term.list pr, F] ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ pre, LongM den L a o) ∧
      UpdQ E a (.tuple #[v, .atom "false"]) keep pr ∧
      (∀ w, WithF E den (.tuple #[v, .atom "false"]) pr (eraseK a w) ↔
        ∃ L ∈ pre, ∃ x, InMLine den L (setK a (some x) w)) ∧
      (∀ w, WithF E den absF pr (eraseK a w) ↔ keep = Bool.true ∧ ∃ L ∈ pre, InMLine den L (setK a none w))) lines
    (fun pre L r mL ⟨pr, F, er, hF, sF, uQ, sN, sA⟩ => by
      subst er
      obtain ⟨⟨tag, l, negs, rfl, g, sl, lits⟩, ne⟩ := hl L mL
      obtain ⟨k, P, acc', Q, rs, rp, hacc, sacc, uQ', sN', sA'⟩ := line_pairs ef hn a hv vne keep g sl lits ne hF
      refine ⟨_, ⟨Q.reverse ++ pr, acc', rfl, hacc, fun o => ?_, fun q mq => ?_, fun w => ?_, fun w => ?_⟩, ?_⟩
      · rw [sacc, sF]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨L', mL', h⟩ | h)
          · exact ⟨L', Or.inl mL', h⟩
          · exact ⟨_, Or.inr rfl, h⟩
        · rintro ⟨L', mL' | rfl, h⟩
          · exact Or.inl ⟨L', mL', h⟩
          · exact Or.inr h
      · rcases List.mem_append.mp mq with mq | mq
        · exact uQ' q (List.mem_reverse.mp mq)
        · exact uQ q mq
      · have : WithF E den (.tuple #[v, .atom "false"]) (Q.reverse ++ pr) (eraseK a w) ↔
            WithF E den (.tuple #[v, .atom "false"]) Q (eraseK a w) ∨
              WithF E den (.tuple #[v, .atom "false"]) pr (eraseK a w) := by
          rw [withF_append]; simp [WithF]
        rw [this, sN', sN]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | ⟨L', mL', h⟩)
          · exact ⟨_, Or.inr rfl, h⟩
          · exact ⟨L', Or.inl mL', h⟩
        · rintro ⟨L', mL' | rfl, h⟩
          · exact Or.inr ⟨L', mL', h⟩
          · exact Or.inl h
      · have : WithF E den absF (Q.reverse ++ pr) (eraseK a w) ↔
            WithF E den absF Q (eraseK a w) ∨ WithF E den absF pr (eraseK a w) := by
          rw [withF_append]; simp [WithF]
        rw [this, sA', sA]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨hk, h⟩ | ⟨hk, L', mL', h⟩)
          · exact ⟨hk, _, Or.inr rfl, h⟩
          · exact ⟨hk, L', Or.inl mL', h⟩
        · rintro ⟨hk, L', mL' | rfl, h⟩
          · exact Or.inr ⟨hk, L', mL', h⟩
          · exact Or.inl ⟨hk, h⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_key/5-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-0-/4», rs, rp, USort.rev2])
    (.tuple #[.nil, .tuple #[.map [], .atom "false"]])
    ⟨[], _, rfl, (none_field ef).1, fun o => by simp [(none_field (den := den) ef).2 o], by simp [UpdQ],
      fun w => by simp [withF_nil], fun w => by simp [withF_nil]⟩
  exact ⟨pr, F, run, hF, sF, uQ, sN, sA⟩


/-- The end of the general clause of `map_update_named_key/5`: grouping the pairs by field and putting each field. -/
theorem keep_tail (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a : String) {v : Term} (hv : E v) (keep : Bool)
    (pairs : List Term) (hp : UpdQ E a (.tuple #[v, .atom "false"]) keep pairs) :
    ∃ bdds, (∀ κ : Term → Except Exception Term, (do
        let p ← Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2» (D (m + 1)) (Term.list pairs)
          (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
        let groups ← Erlang.lists.«foldl/3» (D (m + 1))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[]) (.map []) p
        let l ← Erlang.maps.«to_list/1» groups
        let b ← Erlang.lists.«map/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
          #[.atom a]) l
        κ b) = κ (Term.list bdds)) ∧
      (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        (PutAt den v a w ∧ WithF E den (.tuple #[v, .atom "false"]) pairs (eraseK a w)) ∨
        (w (.atom a) = none ∧ WithF E den absF pairs (eraseK a w)) := by
  have hk : ∀ q ∈ pairs, ∃ f b, q = .tuple #[f, b] ∧ UKey v f := fun q mq => by
    obtain ⟨f, b, rfl, hf, -⟩ := hp q mq
    exact ⟨f, b, rfl, hf.elim Or.inl fun h => Or.inr h.2⟩
  obtain ⟨entries, rg, inv⟩ := group_fold (m + 1) pairs hk
  obtain ⟨bdds, rb, fb, sb⟩ := group_bdds ef hm a hv pairs hp entries inv
  refine ⟨bdds, fun κ => ?_, fb, sb⟩
  simp [Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2», rg, Erlang.maps.«to_list/1», rb]


/-- The general clause of `map_update_named_key/5` with a constant, for `:keep` and `:reject`: the maps of the lines
whose key holds a value, with the key set to a value of the type, and with `:keep`, those without the key. -/
theorem keep_lines (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (ow : Term) :
    ∃ (bdds : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines)
        (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") ow =
        .ok (.tuple #[Term.list bdds, F]) ∧ (∀ b ∈ bdds, MField E b) ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        (PutAt den v a w ∧ ∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ w (.atom a) = none ∧ ∃ L ∈ lines, InMLine den L w) := by
  unfold Elixir.Module.Types.Descr.«map_update_named_key/5»
  simp only [modeT]
  split
  · rename_i h; simp at h
  · rename_i h _; cases keep <;> simp at h
  rotate_left
  · rename_i h₁ h₂ _; exact absurd rfl h₂
  -- Both paths give the pairs of the lines and their old field.
  have tail : ∀ (pairs : List Term) (F : Term), UpdQ E a (.tuple #[v, .atom "false"]) keep pairs →
      FieldValue E F → (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) →
      (∀ w, WithF E den (.tuple #[v, .atom "false"]) pairs (eraseK a w) ↔
        ∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) →
      (∀ w, WithF E den absF pairs (eraseK a w) ↔ keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L (setK a none w)) →
      ∃ bdds, (∀ κ : Term → Except Exception Term, (do
        let p ← Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2» (D (n + 3)) (Term.list pairs)
          (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
        let groups ← Erlang.lists.«foldl/3» (D (n + 3))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[]) (.map []) p
        let l ← Erlang.maps.«to_list/1» groups
        let b ← Erlang.lists.«map/2» (D (n + 3)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
          #[.atom a]) l
        κ b) = κ (Term.list bdds)) ∧ (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        (PutAt den v a w ∧ ∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ w (.atom a) = none ∧ ∃ L ∈ lines, InMLine den L w) := by
    intro pairs F hp hF sF sN sA
    obtain ⟨bdds, rb, fb, sb⟩ := keep_tail ef (m := n + 2) (by omega) a hv keep pairs hp
    refine ⟨bdds, rb, fb, fun w => (sb w).trans ?_⟩
    rw [sN]
    refine or_congr Iff.rfl ⟨fun ⟨hn, h⟩ => ?_, fun ⟨hk, hn, h⟩ => ⟨hn, (sA w).mpr ⟨hk, ?_⟩⟩⟩
    · obtain ⟨hk, L, mL, hL⟩ := (sA w).mp h
      have e : setK a none w = w := by funext κ; by_cases h' : κ = .atom a <;> simp [setK, h', hn]
      rw [e] at hL
      exact ⟨hk, hn, L, mL, hL⟩
    · have e : setK a none w = w := by funext κ; by_cases h' : κ = .atom a <;> simp [setK, h', hn]
      rw [e]; exact h
  split
  · rename_i _ _ f heq
    -- One open line without negations: the shortcut.
    obtain ⟨L, rest, rfl⟩ : ∃ L rest, lines = L :: rest := by
      cases lines with
      | nil => simp [Term.list] at heq
      | cons L rest => exact ⟨L, rest, rfl⟩
    simp only [Term.list, Term.cons.injEq] at heq
    obtain ⟨rfl, hr⟩ := heq
    obtain rfl : rest = [] := by cases rest <;> simp_all [Term.list]
    obtain ⟨⟨tag, l, negs, eL, g, sl, lits⟩, ne⟩ := hl _ List.mem_cons_self
    obtain ⟨rfl, rfl, en⟩ := tuple3_inj eL
    obtain rfl : negs = [] := by
      cases negs with
      | nil => rfl
      | cons x xs => simp [Term.list] at en
    have ne : ∃ w, InMLine den (.tuple #[.atom "open", fieldsTerm l, Term.list []]) w := ne
    obtain ⟨k, rpop, -, rest', -⟩ := pop_pair (den := den) ef g sl a
    obtain ⟨k', P, acc', Q, rs, rp, -, -, uQ, sN, sA⟩ := line_pairs ef (n := n + 1) (by omega) a hv vne keep g sl
      (by simp) ne (none_field ef).1
    have hP : k' = k ∧ P = [] := by
      simp only [Elixir.Module.Types.Descr.«map_split_key_line/5», rpop, Lynx.Except.ok_bind] at rs
      cases hfo : Elixir.Module.Types.Descr.«field_opt_union/3» (D (n + 1 + 2)) (fieldAt (.atom "open") l a)
          (.tuple #[.map [], .atom "false"]) (.map []) with
      | error err => rw [hfo] at rs; cases rs
      | ok c =>
        rw [hfo] at rs
        simp only [Lynx.Except.ok_bind, pure, Except.pure, Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq,
          List.cons.injEq, and_true] at rs
        obtain ⟨-, -, e₁, e₂⟩ := rs
        refine ⟨by simpa using e₁.symm, ?_⟩
        cases P with
        | nil => rfl
        | cons x xs => simp [Term.list] at e₂
    obtain ⟨rfl, rfl⟩ := hP
    obtain ⟨w₀, hw₀⟩ := ne
    have h₀ := (inMLine_iff (negs := []) .. |>.mp hw₀).1
    obtain ⟨bdds, rb, fb, sb⟩ := tail Q (fieldAt (.atom "open") l a) uQ (fieldAt_ok ef g sl a)
      (fun o => by
        rw [lit_values ef g a h₀ o]
        simp only [List.mem_singleton, exists_eq_left, LongM]
        exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (inMLine_iff (negs := [])).mpr ⟨hw, by simp⟩, wa⟩,
          fun ⟨w, hw, wa⟩ => ⟨w, ((inMLine_iff (negs := [])).mp hw).1, wa⟩⟩)
      (fun w => by simpa using sN w) (fun w => by simpa using sA w)
    refine ⟨bdds, _, ?_, fb, fieldAt_ok ef g sl a, fun o => ?_, sb⟩
    · simp only [modeT] at rp rb
      simp only [rpop, rp, Lynx.Except.ok_bind]
      exact rb fun b => pure (.tuple #[b, fieldAt (.atom "open") l a])
    · rw [lit_values ef g a h₀ o]
      simp only [List.mem_singleton, exists_eq_left, LongM]
      exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (inMLine_iff (negs := [])).mpr ⟨hw, by simp⟩, wa⟩,
        fun ⟨w, hw, wa⟩ => ⟨w, ((inMLine_iff (negs := [])).mp hw).1, wa⟩⟩
  · -- Otherwise, the fold over the lines.
    obtain ⟨pr, F, runF, hF, sF, uQ, sN, sA⟩ := keep_fold ef hn a hv vne keep lines hl
    have revW : ∀ f u, WithF E den f pr.reverse u ↔ WithF E den f pr u := fun f u => by
      simp [WithF]
    obtain ⟨bdds, rb, fb, sb⟩ := tail pr.reverse F (fun q mq => uQ q (List.mem_reverse.mp mq)) hF sF
      (fun w => (revW _ _).trans (sN w)) (fun w => (revW _ _).trans (sA w))
    refine ⟨bdds, F, ?_, fb, hF, sF, sb⟩
    simp only [modeT] at runF rb
    simp only [pure_bind, runF, reverse1_list, Lynx.Except.ok_bind]
    exact rb fun b => pure (.tuple #[b, F])


/-- `map_update_static_dnf/6` for `:keep` and `:reject` of a constant at an atom key, returning the old values: when a map
lacks the key, `badkey`, and otherwise the put of the key. -/
theorem keep_static_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (bdd : Term) (lines : List Term) (hne : lines ≠ [])
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 4)) bdd (Term.list lines)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") (.atom "true") =
        .ok res ∧
      ((∃ L ∈ lines, LongM den L a none) → ∃ T Y, res = .tuple #[T, Y, Term.list [.tuple #[.atom "badkey", .atom a]],
        .atom "false"]) ∧
      ((¬∃ L ∈ lines, LongM den L a none) → ∃ T Y, res = .tuple #[T, Y, .nil, .atom "true"] ∧ E T ∧
        (∀ x, den T x ↔ ∃ L ∈ lines, LongM den L a (some x)) ∧ PutMaps E den a (PutAt den v a) lines Y) := by
  classical
  obtain ⟨bdds, F, rb, fb, hF, sF, sb⟩ := keep_lines ef hn a hv vne keep lines hl (.atom "true")
  obtain ⟨t, o, rfl, ht⟩ := hF
  obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
  have optE : o = Bool.true ↔ ∃ L ∈ lines, LongM den L a none := by
    rw [← sF, fieldSem_mk]; simp
  have someE : ∀ x, den t x ↔ ∃ L ∈ lines, LongM den L a (some x) := fun x => by
    rw [← sF, fieldSem_mk]; simp
  obtain ⟨T, hT, rT, sT⟩ := ef.opt_union [] (m := n + 3) ht ef.none (by omega)
  have nonx : ∀ x, ¬den (.map []) x := fun x h => (none_field (den := den) ef).2 (some x)
    (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, h⟩)
  -- The old value and the errors: `badkey` when the old values are empty or a map lacks the key.
  have nk₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4))
      (.tuple #[.map [], .nil, .nil, .atom "false"]) (Term.list lines) (.cons (.atom a) .nil)
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
      (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
      .ok (.tuple #[if e then Term.map [] else T, Term.list bdds,
        if (e || o) then Term.list [.tuple #[.atom "badkey", .atom a]] else .nil, boolAtom (!(e || o))]) := by
    have rb' : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") (.atom "true") =
        .ok (.tuple #[Term.list bdds, .tuple #[t, boolAtom o]]) := rb
    cases keep <;> simp only [modeT, Bool.false_eq_true, ↓reduceIte] at rb' ⊢ <;> cases e <;> cases o <;>
      simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
        Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.lists.«foldl_1/3», Erlang.erlang.«is_function/2»,
        Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
        Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», rb', re, Elixir.Module.Types.Descr.«opt_union/2»,
        rT, Lynx.Term.isMember, boolAtom, Lynx.Except.andAlso, Lynx.Except.orElse]
    all_goals rw [show (Term.nil) = Term.list [] from rfl, append_list]; simp
  have nk₂ : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) acc (Term.list lines) .nil
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
      (.atom "false") (.atom "true") (.atom "true") (.atom "true") = .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 4) (by omega) (ok := fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bdds (Nat.le_refl _) fun b mb => ⟨fb b mb, by
      rcases fb b mb with ⟨k, rfl⟩ | wb
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr (wb.mono fun _ _ => trivial)⟩
  have run : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 4)) bdd (Term.list lines)
      (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") (.atom "true") =
      .ok (.tuple #[if e then Term.map [] else T, if r = .atom "bdd_bot" then Term.map [] else .map [(.atom "map", r)],
        if (e || o) then Term.list [.tuple #[.atom "badkey", .atom a]] else .nil, boolAtom (!(e || o))]) := by
    unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
    cases keep <;> simp only [modeT, Bool.false_eq_true, ↓reduceIte] at nk₁ nk₂ ⊢ <;>
      simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«==/2», Erlang.erlang.«/=/2»,
        Lynx.Term.isMember, Erlang.erlang.«--/2», Erlang.erlang.«++/2», Erlang.erlang.«not/1», Term.list,
        Term.properList?, nk₁, nk₂, Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3»,
        Erlang.erlang.«is_function/2», Erlang.lists.«map/2», rr] <;>
      split
    all_goals simp <;> assumption
  refine ⟨_, run, fun h => ⟨if e then Term.map [] else T,
    if r = .atom "bdd_bot" then Term.map [] else .map [(.atom "map", r)], ?_⟩, fun h => ?_⟩
  · have : (e || o) = Bool.true := by simp [optE.mpr h]
    simp [this]
  have ho : o = Bool.false := by
    cases o
    · rfl
    · exact absurd (optE.mp rfl) h
  have he : e = Bool.false := by
    cases e
    · rfl
    · -- No map holds a value at the key, and none lacks it: there are no maps.
      obtain ⟨L, mL⟩ := List.exists_mem_of_ne_nil lines hne
      obtain ⟨w, hw⟩ := (hl L mL).2
      cases wa : w (.atom a) with
      | none => exact absurd ⟨L, mL, w, hw, wa⟩ h
      | some x => exact absurd ((someE x).mpr ⟨L, mL, w, hw, wa⟩) (se.mp rfl x)
  subst ho he
  refine ⟨T, if r = .atom "bdd_bot" then Term.map [] else .map [(.atom "map", r)], by simp, hT, fun x => by rw [sT, someE]; simp [nonx], r, fr, ?_, fun w => ?_⟩
  · by_cases bot : r = .atom "bdd_bot"
    · subst bot; exact Or.inr ⟨by simp, fun w => denMF_bot w⟩
    · exact Or.inl (by simp [bot])
  · rw [sr, sb]
    constructor
    · rintro (⟨hp, L, mL, x, hL⟩ | ⟨-, hn, L, mL, hL⟩)
      · exact ⟨hp, L, mL, _, hL⟩
      · exact absurd ⟨L, mL, w, hL, hn⟩ h
    · rintro ⟨hp, L, mL, o', hL⟩
      cases o' with
      | some x => exact Or.inl ⟨hp, L, mL, x, hL⟩
      | none => exact absurd ⟨L, mL, _, hL, by simp [setK]⟩ h

theorem longM_iff {b : Term} {lines : List Term}
    (inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (a : String) (o : Option V) :
    (∃ L ∈ lines, LongM den L a o) ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = o :=
  ⟨fun ⟨L, mL, w, hw, wa⟩ => ⟨w, (inB w).mpr ⟨L, mL, hw⟩, wa⟩,
    fun ⟨w, hw, wa⟩ => by obtain ⟨L, mL, hL⟩ := (inB w).mp hw; exact ⟨L, mL, w, hL, wa⟩⟩

/-- `map_update_static/5` for `:keep` and `:reject` of a constant at an atom key, returning the old values. -/
theorem keep_update_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 4)) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") (.atom "true") =
        .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        (∃ w, denMF E den b w = Bool.true) ∧
        ((∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = none) →
          ∃ T Y, res = .tuple #[T, Y, Term.list [.tuple #[.atom "badkey", .atom a]], .atom "false"]) ∧
        ((¬∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = none) →
          ∃ T Y, res = .tuple #[T, Y, .nil, .atom "true"] ∧ E T ∧
          (∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = some x) ∧
          PutField E den a (PutAt den v a) b Y)) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 4)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 4) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      obtain ⟨res, rY, hbad, hgood⟩ := keep_static_dnf ef hn a hv vne keep (.tuple #[.integer k, tag, fieldsTerm l]) _
        (by simp) hl
      have inB : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔
          ∃ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], InMLine den L w := fun w => by
        rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
      refine ⟨res, ?_, Or.inr ⟨⟨w₀, (sem w₀).mpr h₀⟩, fun h => hbad ((longM_iff inB a none).mpr h), fun h => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
        simpa [Term.list] using rY
      · obtain ⟨T, Y, rfl, hT, sT, pY⟩ := hgood fun h' => h ((longM_iff inB a none).mp h')
        exact ⟨T, Y, rfl, hT, fun x => (sT x).trans (longM_iff inB a (some x)), putMaps_field inB pY⟩
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 4) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl (m := n + 4) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
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
      obtain ⟨res, rY, hbad, hgood⟩ := keep_static_dnf ef hn a hv vne keep b (L :: rest) (by simp) hl
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨res, ?_, Or.inr ⟨⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩,
        fun h => hbad ((longM_iff inB a none).mpr h), fun h => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · obtain ⟨T, Y, rfl, hT, sT, pY⟩ := hgood fun h' => h ((longM_iff inB a none).mp h')
        exact ⟨T, Y, rfl, hT, fun x => (sT x).trans (longM_iff inB a (some x)), putMaps_field inB pY⟩


section
variable {t : Term} {n : Nat}

/-- `map_update_unchecked/4` for `:keep` and `:reject` of a static value at an atom key of static types of the next
level, returning the old values: `:badmap` unless the type holds only maps, `badkey` when one of them lacks the key, and
otherwise the put of the key. -/
theorem keep_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term}
    (hv : (level t n).E v) (vne : ∃ x, (level t n).den v x) (keep : Bool) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        MOnly t n X ∧
        ((∃ w, MT t n X w ∧ w (.atom a) = none) →
          res = .tuple #[.atom "error", Term.list [.tuple #[.atom "badkey", .atom a]]]) ∧
        ((¬∃ w, MT t n X w ∧ w (.atom a) = none) →
          ∃ T Y, res = .tuple #[T, .map Y, .nil] ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 4))
      (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[r] =
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
    have rE := next_empty dR (m := k + 4) (by omega)
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
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 4)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    have lack : (∃ w, MT t n X w ∧ w (.atom a) = none) ↔
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true ∧ w (.atom a) = none :=
      ⟨fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mp hw, wa⟩, fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mpr hw, wa⟩⟩
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨⟨w₀, hw₀⟩, hbad, hgood⟩⟩ :=
        keep_update_static (level t n).ef (n := k) (by omega) a hv vne keep hb fb
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      by_cases hl : ∃ w, MT t n X w ∧ w (.atom a) = none
      · obtain ⟨T, Y, rfl⟩ := hbad (lack.mp hl)
        refine ⟨_, ?_, Or.inr ⟨only.mpr ⟨restE, w₀, hw₀⟩, fun _ => rfl, fun h => absurd hl h⟩⟩
        simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
      · obtain ⟨T, Y, rfl, hT, sT, r, fr, hY, sr⟩ := hgood fun h => hl (lack.mpr h)
        have semT : ∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x := fun x => by
          rw [sT]; exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mpr hw, wa⟩, fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mp hw, wa⟩⟩
        have sem : ∀ w, denMF (level t n).E (level t n).den r w = Bool.true ↔
            PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w) := fun w => by
          rw [sr]
          exact and_congr Iff.rfl ⟨fun ⟨o, h⟩ => ⟨o, (mt _).mpr h⟩, fun ⟨o, h⟩ => ⟨o, (mt _).mp h⟩⟩
        rcases hY with rfl | ⟨rfl, emp⟩
        · refine ⟨_, ?_, Or.inr ⟨only.mpr ⟨restE, w₀, hw₀⟩, fun h => absurd h hl, fun _ =>
            ⟨T, _, rfl, hT, semT, Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_, fun w => ?_⟩⟩⟩
          · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
          · rw [denD_map] at hq
            by_cases e : q.1.1 = "map"
            · exact e
            · simp [mapLookup, e, dn_none] at hq
          · rw [← sem]; simp [MT, mapLookup]
        · refine ⟨_, ?_, Or.inr ⟨only.mpr ⟨restE, w₀, hw₀⟩, fun h => absurd h hl, fun _ =>
            ⟨T, _, rfl, hT, semT, Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_, fun w => ?_⟩⟩⟩
          · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
          · rw [denD_map] at hq
            simp [mapLookup, dn_none] at hq
          · rw [← sem, emp w]; simp [MT, mapLookup]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]

/-- `map_update/5` for `:keep` and `:reject` of a static value at a single atom key, returning the old values. -/
theorem update_keep {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term}
    (hv : (level t n).E v) (vne : ∃ x, (level t n).den v x)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) (keep : Bool) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) (atomT a) v (modeT keep) (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        MOnly t n X ∧
        ((∃ w, MT t n X w ∧ w (.atom a) = none) →
          res = .tuple #[.atom "error", Term.list [.tuple #[.atom "badkey", .atom a]]]) ∧
        ((¬∃ w, MT t n X w ∧ w (.atom a) = none) →
          ∃ T Y, res = .tuple #[T, .map Y, .nil] ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨res, run, h⟩ := keep_map hX a hv vne keep hm
  refine ⟨res, ?_, h⟩
  unfold Elixir.Module.Types.Descr.«map_update/5»
  simp only [modeT] at run ⊢
  rcases sv with rfl | ⟨Z, rfl, sZ⟩ <;> cases keep
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at run
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      Lynx.Term.getMapKeys]
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      Lynx.Term.getMapKeys]
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      getMapKeys_single, sZ]
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      getMapKeys_single, sZ]

end

end Elixir.STTDescrProofsTest.Nest
