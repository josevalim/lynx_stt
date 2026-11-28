module

public import Erlang.program
public import MapOptNegationValues
public import MapOptIntersectionNegation
public import TupleDifferencesValues
public import ValueMaps

@[expose] public section

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-! Map literal intersections on value maps. -/

/-- Intersection functions of element types, at every call depth from `Kf`. -/
def IFun (E : Term → Prop) (den : Term → V → Prop) (Kf : Nat) (ifun : Term) : Prop :=
  ∀ m, Kf ≤ m → ∀ a b, E a → E b → ∃ c, E c ∧ (∀ x, den c x ↔ den a x ∧ den b x) ∧
    Lynx.Dispatcher.pure (D m) ifun #[a, b] = .ok c

/-- Results of literal intersections of value maps: sorted fields of keys of either literal allowing, at each key,
what both literals allow, or `:empty` thrown when some key allows nothing in both. -/
def InterV (E : Term → Prop) (den : Term → V → Prop) (r : Except Exception Term) (t₁ t₂ tR : Term)
    (l₁ l₂ ks : List (Term × Term)) : Prop :=
  (∃ l, r = .ok (fieldsTerm l) ∧ FieldsV E l ∧ (∀ e ∈ l, ∃ e' ∈ ks, e.1 = e'.1) ∧
    ∀ s o, FSem den tR l s o ↔ FSem den t₁ l₁ s o ∧ FSem den t₂ l₂ s o) ∨
  ((∃ s, ∀ o, ¬(FSem den t₁ l₁ s o ∧ FSem den t₂ l₂ s o)) ∧ r = .error (Exception.throw (.atom "empty")))

theorem fsem_absent {tag : Term} {s : String} {l : List (Term × Term)} (h : mapLookup l (.atom s) = Option.none) :
    FSem den tag l s Option.none := by
  simp only [FSem, h]; exact tagSem_none tag "atom"


/-- A throw at a key of the tails is a throw for the whole lists. -/
theorem disj_cons₁ {t₁ t₂ : Term} {a : String} {f : Term} {xs l₂ : List (Term × Term)} (s₁ : FieldsV E ((.atom a, f) :: xs))
    (above : ∀ e ∈ l₂, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt)
    (h : ∃ s, ∀ o, ¬(FSem den t₁ xs s o ∧ FSem den t₂ l₂ s o)) :
    ∃ s, ∀ o, ¬(FSem den t₁ ((.atom a, f) :: xs) s o ∧ FSem den t₂ l₂ s o) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun o ho => hs o ?_⟩
  by_cases e : a = s
  · subst e
    exact absurd ⟨fsem_absent (lookup_above (fieldsV_head s₁)), fsem_absent (lookup_above above)⟩ (hs Option.none)
  · exact ⟨(fsem_cons_ne e _ _ _).mp ho.1, ho.2⟩

theorem disj_cons₂ {t₁ t₂ : Term} {a : String} {f : Term} {l₁ ys : List (Term × Term)} (s₂ : FieldsV E ((.atom a, f) :: ys))
    (above : ∀ e ∈ l₁, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt)
    (h : ∃ s, ∀ o, ¬(FSem den t₁ l₁ s o ∧ FSem den t₂ ys s o)) :
    ∃ s, ∀ o, ¬(FSem den t₁ l₁ s o ∧ FSem den t₂ ((.atom a, f) :: ys) s o) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun o ho => hs o ?_⟩
  by_cases e : a = s
  · subst e
    exact absurd ⟨fsem_absent (lookup_above above), fsem_absent (lookup_above (fieldsV_head s₂))⟩ (hs Option.none)
  · exact ⟨ho.1, (fsem_cons_ne e _ _ _).mp ho.2⟩

theorem disj_both {t₁ t₂ : Term} {a : String} {f₁ f₂ : Term} {xs ys : List (Term × Term)} (s₁ : FieldsV E ((.atom a, f₁) :: xs))
    (s₂ : FieldsV E ((.atom a, f₂) :: ys)) (h : ∃ s, ∀ o, ¬(FSem den t₁ xs s o ∧ FSem den t₂ ys s o)) :
    ∃ s, ∀ o, ¬(FSem den t₁ ((.atom a, f₁) :: xs) s o ∧ FSem den t₂ ((.atom a, f₂) :: ys) s o) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun o ho => hs o ?_⟩
  by_cases e : a = s
  · subst e
    exact absurd ⟨fsem_absent (lookup_above (fieldsV_head s₁)), fsem_absent (lookup_above (fieldsV_head s₂))⟩
      (hs Option.none)
  · exact ⟨(fsem_cons_ne e _ _ _).mp ho.1, (fsem_cons_ne e _ _ _).mp ho.2⟩

theorem fsem_nil {tag s : String} {o : Option V} : FSem den (.atom tag) [] s o ↔ (tag = "open" ∨ o = Option.none) :=
  fsem_none rfl o

/-- Fields that are all optional allow absent keys. -/
theorem fsem_optional {tag : String} {l : List (Term × Term)}
    (opt : ∀ e ∈ l, ∃ t, e.2 = .tuple #[t, boolAtom Bool.true]) (s : String) : FSem den (.atom tag) l s Option.none := by
  unfold FSem TagSem
  cases e : mapLookup l (.atom s) with
  | none => exact Or.inr rfl
  | some f =>
    obtain ⟨x, mx, rfl⟩ := lookup_mem e
    obtain ⟨t, ht⟩ := opt x mx
    rw [ht]
    exact (fieldSem_mk).mpr (Or.inl ⟨rfl, rfl⟩)

/-- A required field allows only present keys. -/
theorem fsem_required {tag : String} {l : List (Term × Term)} (sl : FieldsV E l) {e : Term × Term} (me : e ∈ l)
    {t : Term} (he : e.2 = .tuple #[t, boolAtom Bool.false]) {s : String} (ek : e.1 = .atom s) :
    ¬FSem den (.atom tag) l s Option.none := by
  unfold FSem TagSem
  rw [lookup_of_mem sl me ek, he]
  dsimp only
  rw [fieldSem_mk]
  simp

theorem any_optFlag {l : List (Term × Term)} (sl : FieldsV E l) :
    (l.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = Bool.false ↔
      ∀ e ∈ l, ∃ t, e.2 = .tuple #[t, boolAtom Bool.true] := by
  simp only [List.any_eq_false, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Bool.not_eq_true', Bool.not_eq_false]
  refine forall₂_congr fun e me => ?_
  obtain ⟨t, o, ho, -⟩ := (sl.1 e me).2
  rw [ho]
  constructor
  · intro h
    have := optFlag_entry e.1 t o
    rw [h] at this
    exact ⟨t, by rw [← this]⟩
  · rintro ⟨t', e'⟩
    simp only [Term.tuple.injEq] at e'
    have e₁ := congrArg (fun a : Array Term => a[1]?) e'
    simp at e₁
    have : o = Bool.true := by cases o <;> simp_all [boolAtom]
    subst this
    exact optFlag_entry e.1 t Bool.true

theorem closed_tails (m : Nat) (l₁ l₂ : List (Term × Term)) (h₁ : FieldsV E l₁) (h₂ : FieldsV E l₂) :
    Lynx.Except.orElse
      (Erlang.lists.«any/2» (D m)
        (.function false "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-0-" 1 #[]) (fieldsTerm l₁))
      (Erlang.lists.«any/2» (D m)
        (.function false "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-1-" 1 #[]) (fieldsTerm l₂))
      Bool.true = .ok (boolAtom ((l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) ||
        (l₂.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x))) := by
  have r₁ := any_list (D m) _ _ _ (fun x => !optFlag x) _ (optional_list (E := E) (D m) _ _
    (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-0-/1».pure m) (fun o => !o)
    closed_fun₀ l₁ fun e me => (h₁.1 e me).2)
  have r₂ := any_list (D m) _ _ _ (fun x => !optFlag x) _ (optional_list (E := E) (D m) _ _
    (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-1-/1».pure m) (fun o => !o)
    closed_fun₁ l₂ fun e me => (h₂.1 e me).2)
  simp only [fieldsTerm] at r₁ r₂ ⊢
  rw [r₁, r₂]
  cases (l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) <;>
    simp [boolAtom, Lynx.Except.orElse] <;> rfl

theorem any_required {l : List (Term × Term)} (sl : FieldsV E l)
    (h : (l.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = Bool.true) :
    ∃ e ∈ l, ∃ (t : Term) (s : String), e.2 = .tuple #[t, boolAtom Bool.false] ∧ e.1 = .atom s := by
  simp only [List.any_eq_true, List.mem_map] at h
  obtain ⟨x, ⟨e, me, rfl⟩, hx⟩ := h
  obtain ⟨t, o, ho, -⟩ := (sl.1 e me).2
  obtain ⟨s, hs⟩ := (sl.1 e me).1
  rw [ho, optFlag_entry] at hx
  cases o
  · exact ⟨e, me, t, s, ho, hs⟩
  · simp at hx

/-- The intersection of element types at a key, with its emptiness. -/
theorem meet_run (ops : ElemOk E K) (_dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf m : Nat} (hK : Kf ≤ m) (hm : K ≤ m) {ifun : Term} (hI : IFun E den Kf ifun) {S : List (Term × Term)}
    (hS : Safe S) {t₁ t₂ : Term} (h₁ : E t₁) (h₂ : E t₂) :
    ∃ c b, E c ∧ (∀ x, den c x ↔ den t₁ x ∧ den t₂ x) ∧
      Lynx.Dispatcher.pure (D m) ifun #[t₁, t₂] = .ok c ∧
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m) c (.map S) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ∀ x, ¬den c x) := by
  obtain ⟨c, hc, sem, run⟩ := hI m hK t₁ t₂ h₁ h₂
  obtain ⟨b, hb⟩ := ops.empty hc S
  exact ⟨c, b, hc, sem, run, hb m hm, esem.empty hc hS hm (hb m hm)⟩

/-- Fields of a key in both literals: their meet, or nothing when the meet is required and empty. -/
theorem meet_field_sem {t₁ t₂ c : Term} {o₁ o₂ : Bool} (sem : ∀ x, den c x ↔ den t₁ x ∧ den t₂ x)
    (o : Option V) : FieldSem den (.tuple #[c, boolAtom (o₁ && o₂)]) o ↔
      FieldSem den (.tuple #[t₁, boolAtom o₁]) o ∧ FieldSem den (.tuple #[t₂, boolAtom o₂]) o :=
  fieldSem_meet sem o

theorem meet_field_empty {t₁ t₂ c : Term} {o₁ o₂ : Bool} (sem : ∀ x, den c x ↔ den t₁ x ∧ den t₂ x)
    (req : (o₁ && o₂) = Bool.false) (empty : ∀ x, ¬den c x) (o : Option V) :
    ¬(FieldSem den (.tuple #[t₁, boolAtom o₁]) o ∧ FieldSem den (.tuple #[t₂, boolAtom o₂]) o) := by
  rw [← meet_field_sem sem, fieldSem_mk]
  rintro (⟨-, h⟩ | ⟨x, -, hx⟩)
  · rw [req] at h; cases h
  · exact empty x hx

/-- `map_literal_intersection_closed/4` on value maps. -/
theorem closed_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf m : Nat} (hK : Kf ≤ m) (hm : K ≤ m) {ifun : Term} (hI : IFun E den Kf ifun) {S : List (Term × Term)}
    (hS : Safe S) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → FieldsV E l₁ → FieldsV E l₂ →
      InterV E den (Elixir.Module.Types.Descr.«map_literal_intersection_closed/4» (D m) (fieldsTerm l₁) (fieldsTerm l₂)
        ifun (.map S)) (.atom "closed") (.atom "closed") (.atom "closed") l₁ l₂ l₂ := by
  have tailCase : ∀ (l₁ l₂ : List (Term × Term)), FieldsV E l₁ → FieldsV E l₂ → (l₁ = [] ∨ l₂ = []) →
      InterV E den (Elixir.Module.Types.Descr.«map_literal_intersection_closed/4» (D m) (fieldsTerm l₁) (fieldsTerm l₂)
        ifun (.map S)) (.atom "closed") (.atom "closed") (.atom "closed") l₁ l₂ l₂ := by
    intro l₁ l₂ h₁ h₂ empty
    have hb := closed_tails m l₁ l₂ h₁ h₂
    generalize ha₁ : (l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = a₁ at hb
    generalize ha₂ : (l₂.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = a₂ at hb
    have absent : ∀ (l : List (Term × Term)), l = [] → ∀ s o, FSem den (.atom "closed") l s o → o = Option.none := by
      rintro l rfl s o h
      rw [fsem_none (by simp [mapLookup])] at h
      simpa using h
    cases a₁ <;> cases a₂
    · left
      have o₁ := (any_optFlag h₁).mp ha₁
      have o₂ := (any_optFlag h₂).mp ha₂
      refine ⟨[], ?_, ⟨by simp, by simp⟩, by simp, fun s o => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
        rcases empty with rfl | rfl
        · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
        · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
      · constructor
        · intro h
          rw [absent [] rfl s o h]
          exact ⟨fsem_optional o₁ s, fsem_optional o₂ s⟩
        · rintro ⟨g₁, g₂⟩
          have : o = Option.none := by
            rcases empty with rfl | rfl
            · exact absent [] rfl s o g₁
            · exact absent [] rfl s o g₂
          subst this
          exact fsem_absent (by simp [mapLookup])
    all_goals
      right
      refine ⟨?_, ?_⟩
      rotate_left
      · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
        rcases empty with rfl | rfl
        · cases l₂ <;> simp only [fieldsTerm, List.map_nil, List.map_cons] at hb ⊢ <;>
            simp [Term.list, hb, boolAtom, isMember]
        · cases l₁ <;> simp only [fieldsTerm, List.map_nil, List.map_cons] at hb ⊢ <;>
            simp [Term.list, hb, boolAtom, isMember]
    · obtain ⟨e, me, t, s, he, ek⟩ := any_required h₂ ha₂
      have : l₁ = [] := by rcases empty with h | rfl; exact h; simp at me
      exact ⟨s, fun o ⟨g₁, g₂⟩ => fsem_required h₂ me he ek (by rwa [absent l₁ this s o g₁] at g₂)⟩
    all_goals
      obtain ⟨e, me, t, s, he, ek⟩ := any_required h₁ ha₁
      have : l₂ = [] := by rcases empty with rfl | h; simp at me; exact h
      exact ⟨s, fun o ⟨g₁, g₂⟩ => fsem_required h₁ me he ek (by rwa [absent l₂ this s o g₂] at g₁)⟩
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    exact tailCase l₁ l₂ h₁ h₂ (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ => exact tailCase [] l₂ h₁ h₂ (Or.inl rfl)
    | x :: xs, [] => exact tailCase (x :: xs) [] h₁ h₂ (Or.inr rfl)
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨t₁, o₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      obtain ⟨t₂, o₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have sx := fieldsV_tail h₁
      have sy := fieldsV_tail h₂
      have hx := fieldsV_head h₁
      have hy := fieldsV_head h₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · have above : ∀ e ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp
          · exact cmp_lt_trans cmp (hy e me)
        have absent₂ := lookup_above above
        cases o₁
        · right
          refine ⟨⟨a, fun o ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_none absent₂] at g₂
            rw [fsem_cons_self, fieldSem_mk] at g₁
            rcases g₁ with ⟨-, h⟩ | ⟨x, hx, -⟩
            · cases h
            · simp [hx] at g₂
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp [fieldsTerm, Erlang.erlang.«</2», cmp, boolAtom, isMember]
        · rcases ih xs _ (by simp; omega) sx h₂ with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨l, ?_, sl, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using run
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp [me'], ee⟩
            · by_cases e : a = s
              · subst e
                rw [sem, fsem_cons_self, fsem_none (lookup_above hx), fsem_none absent₂, fieldSem_mk]
                constructor
                · rintro ⟨h, -⟩; exact ⟨Or.inl ⟨by simpa using h, rfl⟩, h⟩
                · rintro ⟨-, h⟩; exact ⟨h, h⟩
              · rw [sem, fsem_cons_ne e]
          · right
            refine ⟨disj_cons₁ h₁ above disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using run
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, bc, lc, semc, disp, emp, empSem⟩ := meet_run ops dops esem hK hm hI hS f₁ f₂
        have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
        have notGt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isGT = Bool.true := by simp
        by_cases thrown : (o₁ && o₂) = Bool.false ∧ bc = Bool.true
        · obtain ⟨o, rfl⟩ := thrown
          right
          refine ⟨⟨a, fun o' ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_cons_self] at g₁ g₂
            exact meet_field_empty semc o (empSem.mp rfl) o' ⟨g₁, g₂⟩
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            cases o₁ <;> cases o₂ <;> simp at o <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                isMember, Lynx.Except.andAlso, disp, emp]
        · rcases ih xs ys (by omega) sx sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨(.atom a, .tuple #[c, boolAtom (o₁ && o₂)]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simp only [fieldsTerm] at run
              cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
                simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                  isMember, Lynx.Except.andAlso, disp, emp, run]
            · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
              obtain ⟨e', me', ee⟩ := keys e me
              rw [ee]
              exact hy e' me'
            · rcases List.mem_cons.mp me with rfl | me
              · exact ⟨_, List.mem_cons_self, rfl⟩
              · obtain ⟨e', me', ee⟩ := keys e me
                exact ⟨e', by simp [me'], ee⟩
            · by_cases e : a = s
              · subst e
                rw [fsem_cons_self, fsem_cons_self, fsem_cons_self]
                exact meet_field_sem semc o
              · rw [fsem_cons_ne e, fsem_cons_ne e, fsem_cons_ne e, sem]
          · right
            refine ⟨disj_both h₁ h₂ disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp only [fieldsTerm] at run
            cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                isMember, Lynx.Except.andAlso, disp, emp, run]
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp'
          · exact cmp_lt_trans cmp' (hx e me)
        have absent₁ := lookup_above above
        cases o₂
        · right
          refine ⟨⟨b, fun o ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_none absent₁] at g₁
            rw [fsem_cons_self, fieldSem_mk] at g₂
            rcases g₂ with ⟨-, h⟩ | ⟨x, hx, -⟩
            · cases h
            · simp [hx] at g₁
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom, isMember]
        · rcases ih _ ys (by simp; omega) h₁ sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨l, ?_, sl, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember] using run
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp [me'], ee⟩
            · by_cases e : b = s
              · subst e
                rw [sem, fsem_cons_self, fsem_none (lookup_above hy), fsem_none absent₁, fieldSem_mk]
                constructor
                · rintro ⟨h, -⟩; exact ⟨h, Or.inl ⟨by simpa using h, rfl⟩⟩
                · rintro ⟨h, -⟩; exact ⟨h, h⟩
              · rw [sem, fsem_cons_ne e]
          · right
            refine ⟨disj_cons₂ h₂ above disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember] using run

theorem all_optFlag {l : List (Term × Term)} (sl : FieldsV E l) :
    (l.map fun e => Term.tuple #[e.1, e.2]).all (fun x => optFlag x) = Bool.true ↔
      ∀ e ∈ l, ∃ t, e.2 = .tuple #[t, boolAtom Bool.true] := by
  have := any_optFlag sl
  rw [← this]
  simp [List.all_eq_true, List.any_eq_false]

/-- `map_literal_intersection_open_closed/4` on value maps: the open literal first. -/
theorem open_closed_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf m : Nat} (hK : Kf ≤ m) (hm : K ≤ m) {ifun : Term} (hI : IFun E den Kf ifun)
    {S : List (Term × Term)} (hS : Safe S) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
      FieldsV E l₁ → FieldsV E l₂ →
      InterV E den (Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4» (D m) (fieldsTerm l₁)
        (fieldsTerm l₂) ifun (.map S)) (.atom "open") (.atom "closed") (.atom "closed") l₁ l₂ l₂ := by
  have tailCase : ∀ (l₁ l₂ : List (Term × Term)), FieldsV E l₁ → FieldsV E l₂ → (l₁ = [] ∨ l₂ = []) →
      InterV E den (Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4» (D m) (fieldsTerm l₁)
        (fieldsTerm l₂) ifun (.map S)) (.atom "open") (.atom "closed") (.atom "closed") l₁ l₂ l₂ := by
    intro l₁ l₂ h₁ h₂ empty
    have hb := all_list (D m) _ _ _ (fun x => optFlag x) _ (optional_list (E := E) (D m) _ _
      (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_open_closed/4-fun-0-/1».pure m)
      (fun o => o) open_closed_fun l₁ fun e me => (h₁.1 e me).2)
    cases b : (l₁.map fun e => Term.tuple #[e.1, e.2]).all (fun x => optFlag x)
    · right
      refine ⟨?_, ?_⟩
      · have : (l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = Bool.true := by
          simpa [List.all_eq_true, List.any_eq_true] using b
        obtain ⟨e, me, t, s, he, ek⟩ := any_required h₁ this
        have : l₂ = [] := by rcases empty with rfl | h; simp at me; exact h
        subst this
        refine ⟨s, fun o ⟨g₁, g₂⟩ => fsem_required (den := den) (tag := "open") h₁ me he ek ?_⟩
        rw [fsem_nil] at g₂
        rcases g₂ with h | h
        · exact absurd h (by decide)
        · rwa [h] at g₁
      · rw [b] at hb
        unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
        rcases empty with rfl | rfl
        · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
        · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
    · left
      have opt := (all_optFlag h₁).mp b
      refine ⟨l₂, ?_, h₂, fun e me => ⟨e, me, rfl⟩, fun s o => ?_⟩
      · rw [b] at hb
        unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
        rcases empty with rfl | rfl
        · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
        · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
      · refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
        rcases empty with rfl | rfl
        · exact fsem_nil.mpr (Or.inl rfl)
        · rw [fsem_nil] at h
          rcases h with h | h
          · exact absurd h (by decide)
          · rw [h]; exact fsem_optional opt s
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    exact tailCase l₁ l₂ h₁ h₂ (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ => exact tailCase [] l₂ h₁ h₂ (Or.inl rfl)
    | x :: xs, [] => exact tailCase (x :: xs) [] h₁ h₂ (Or.inr rfl)
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨t₁, o₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      obtain ⟨t₂, o₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have sx := fieldsV_tail h₁
      have sy := fieldsV_tail h₂
      have hx := fieldsV_head h₁
      have hy := fieldsV_head h₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · have above : ∀ e ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp
          · exact cmp_lt_trans cmp (hy e me)
        have absent₂ := lookup_above above
        cases o₁
        · right
          refine ⟨⟨a, fun o ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_none absent₂] at g₂
            rw [fsem_cons_self, fieldSem_mk] at g₁
            rcases g₁ with ⟨-, h⟩ | ⟨x, hx, -⟩
            · cases h
            · simp [hx] at g₂
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp [fieldsTerm, Erlang.erlang.«</2», cmp, boolAtom, isMember]
        · rcases ih xs _ (by simp; omega) sx h₂ with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨l, ?_, sl, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
              simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using run
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp [me'], ee⟩
            · by_cases e : a = s
              · subst e
                rw [sem, fsem_cons_self, fsem_none (lookup_above hx), fsem_none absent₂, fieldSem_mk]
                constructor
                · rintro ⟨-, h⟩; exact ⟨Or.inl ⟨by simpa using h, rfl⟩, h⟩
                · rintro ⟨-, h⟩; exact ⟨Or.inl rfl, h⟩
              · rw [sem, fsem_cons_ne e]
          · right
            refine ⟨disj_cons₁ h₁ above disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using run
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, bc, lc, semc, disp, emp, empSem⟩ := meet_run ops dops esem hK hm hI hS f₁ f₂
        have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
        have notGt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isGT = Bool.true := by simp
        by_cases thrown : (o₁ && o₂) = Bool.false ∧ bc = Bool.true
        · obtain ⟨o, rfl⟩ := thrown
          right
          refine ⟨⟨a, fun o' ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_cons_self] at g₁ g₂
            exact meet_field_empty semc o (empSem.mp rfl) o' ⟨g₁, g₂⟩
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            cases o₁ <;> cases o₂ <;> simp at o <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                isMember, Lynx.Except.andAlso, disp, emp]
        · rcases ih xs ys (by omega) sx sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨(.atom a, .tuple #[c, boolAtom (o₁ && o₂)]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
              simp only [fieldsTerm] at run
              cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
                simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                  isMember, Lynx.Except.andAlso, disp, emp, run]
            · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
              obtain ⟨e', me', ee⟩ := keys e me
              rw [ee]
              exact hy e' me'
            · rcases List.mem_cons.mp me with rfl | me
              · exact ⟨_, List.mem_cons_self, rfl⟩
              · obtain ⟨e', me', ee⟩ := keys e me
                exact ⟨e', by simp [me'], ee⟩
            · by_cases e : a = s
              · subst e
                rw [fsem_cons_self, fsem_cons_self, fsem_cons_self]
                exact meet_field_sem semc o
              · rw [fsem_cons_ne e, fsem_cons_ne e, fsem_cons_ne e, sem]
          · right
            refine ⟨disj_both h₁ h₂ disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp only [fieldsTerm] at run
            cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                isMember, Lynx.Except.andAlso, disp, emp, run]
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp'
          · exact cmp_lt_trans cmp' (hx e me)
        have absent₁ := lookup_above above
        rcases ih _ ys (by simp; omega) h₁ sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
        · left
          refine ⟨(.atom b, .tuple #[t₂, boolAtom o₂]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
            simp [run]
          · refine fieldsV_cons ⟨b, rfl⟩ ⟨t₂, _, rfl, f₂⟩ sl fun e me => ?_
            obtain ⟨e', me', ee⟩ := keys e me
            rw [ee]
            exact hy e' me'
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨_, by simp, rfl⟩
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp [me'], ee⟩
          · by_cases e : b = s
            · subst e
              rw [fsem_cons_self, fsem_cons_self, fsem_none absent₁]
              exact ⟨fun h => ⟨Or.inl rfl, h⟩, fun h => h.2⟩
            · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
        · right
          refine ⟨disj_cons₂ h₂ above disj, ?_⟩
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
          simp [run]

/-- Domains intersect kind by kind, dropping the kinds whose intersection is empty. -/
theorem domain_fields_val (ops : ElemOk E K) (_dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    {S : List (Term × Term)} (hS : Safe S) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
      DomsV E l₁ → DomsV E l₂ → ∃ l : List (Term × Term),
        Elixir.Module.Types.Descr.«map_domain_intersection_fields/3» (D m) (fieldsTerm l₁) (fieldsTerm l₂) (.map S) =
          .ok (fieldsTerm l) ∧ DomsV E l ∧ (∀ e ∈ l, ∃ e' ∈ l₁, e.1 = e'.1) ∧
        ∀ (s : String) v, (∃ T, mapLookup l (.atom s) = some T ∧ den T v) ↔
          (∃ T, mapLookup l₁ (.atom s) = some T ∧ den T v) ∧ (∃ T, mapLookup l₂ (.atom s) = some T ∧ den T v) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size _ _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨[], by rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; simp [fieldsTerm, Term.list],
      ⟨by simp, by simp⟩, by simp, fun s v => by simp [mapLookup]⟩
  | succ N ih =>
    intro l₁ l₂ size d₁ d₂
    have tail : ∀ {x : Term × Term} {xs : List (Term × Term)}, DomsV E (x :: xs) → DomsV E xs :=
      fun d => ⟨fun e me => d.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp d.2).2⟩
    match l₁, l₂ with
    | [], l₂ =>
      exact ⟨[], by rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; cases l₂ <;> simp [fieldsTerm, Term.list],
        ⟨by simp, by simp⟩, by simp, fun s v => by simp [mapLookup]⟩
    | x :: xs, [] =>
      exact ⟨[], by rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; simp [fieldsTerm, Term.list],
        ⟨by simp, by simp⟩, by simp, fun s v => by simp [mapLookup]⟩
    | (k₁, T₁) :: xs, (k₂, T₂) :: ys =>
      obtain ⟨⟨a, rfl, -⟩, E₁⟩ := d₁.1 _ List.mem_cons_self
      obtain ⟨⟨b, rfl, -⟩, E₂⟩ := d₂.1 _ List.mem_cons_self
      have h₁ := (List.pairwise_cons.mp d₁.2).1
      have h₂ := (List.pairwise_cons.mp d₂.2).1
      simp only [List.length_cons] at size
      -- lookups at a key below every key of a list find nothing
      have below : ∀ {c : String} {zs : List (Term × Term)}, (∀ z ∈ zs, Term.compare (Term.fuel (.atom c) z.1) (.atom c) z.1 = .lt) →
          ∀ T v, ¬(mapLookup zs (.atom c) = some T ∧ den T v) := fun hz T v ⟨h, _⟩ => by
        rw [lookup_above hz] at h; cases h
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · obtain ⟨l, run, dl, keys, sem⟩ := ih xs ((.atom b, T₂) :: ys) (by simp; omega) (tail d₁) d₂
        refine ⟨l, ?_, dl, fun e me => ?_, fun s v => ?_⟩
        · rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def, ← run]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
        · obtain ⟨e', me', ee⟩ := keys e me; exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
        · by_cases as : a = s
          · subst as
            have nb : ∀ z ∈ (Term.atom b, T₂) :: ys, Term.compare (Term.fuel (.atom a) z.1) (.atom a) z.1 = .lt := fun z mz => by
              rcases List.mem_cons.mp mz with rfl | mz
              · exact cmp
              · exact cmp_lt_trans cmp (h₂ z mz)
            rw [sem]
            constructor
            · rintro ⟨-, T, h, hv⟩; exact absurd ⟨h, hv⟩ (below nb T v)
            · rintro ⟨-, T, h, hv⟩; exact absurd ⟨h, hv⟩ (below nb T v)
          · have e₁ : mapLookup ((.atom a, T₁) :: xs) (.atom s) = mapLookup xs (.atom s) := by
              rw [lookup_cons_atom, ite_eq_right as]
            rw [e₁]; exact sem s v
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, hc, inter⟩ := ops.inter E₁ E₂
        have semc := esem.inter E₁ E₂ hm (inter m hm)
        obtain ⟨bc, empty⟩ := ops.empty hc S
        have semE := esem.empty hc hS hm (empty m hm)
        obtain ⟨l, run, dl, keys, sem⟩ := ih xs ys (by omega) (tail d₁) (tail d₂)
        have r := run
        simp only [fieldsTerm] at r
        have rest : ∀ z ∈ l, Term.compare (Term.fuel (.atom a) z.1) (.atom a) z.1 = .lt := fun z mz => by
          obtain ⟨e', me', ee⟩ := keys z mz; rw [ee]; exact h₁ e' me'
        cases bc
        · refine ⟨(.atom a, c) :: l, ?_, ⟨fun e me => ?_, List.pairwise_cons.mpr ⟨rest, dl.2⟩⟩, fun e me => ?_,
            fun s v => ?_⟩
          · rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              inter m hm, empty m hm, boolAtom, isMember, r]
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨(d₁.1 _ List.mem_cons_self).1.imp fun _ h => h, hc⟩
            · exact dl.1 e me
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨_, List.mem_cons_self, rfl⟩
            · obtain ⟨e', me', ee⟩ := keys e me; exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
          · by_cases as : a = s
            · subst as
              simp only [lookup_cons_atom]
              simp [semc]
            · have e₁ : mapLookup ((.atom a, T₁) :: xs) (.atom s) = mapLookup xs (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              have e₂ : mapLookup ((.atom a, T₂) :: ys) (.atom s) = mapLookup ys (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              have e₀ : mapLookup ((.atom a, c) :: l) (.atom s) = mapLookup l (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              rw [e₀, e₁, e₂]; exact sem s v
        · refine ⟨l, ?_, dl, fun e me => ?_, fun s v => ?_⟩
          · rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              inter m hm, empty m hm, boolAtom, isMember, r]
          · obtain ⟨e', me', ee⟩ := keys e me; exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
          · by_cases as : a = s
            · subst as
              have l₁' : mapLookup ((.atom a, T₁) :: xs) (.atom a) = some T₁ := by simp [lookup_cons_atom]
              have l₂' : mapLookup ((.atom a, T₂) :: ys) (.atom a) = some T₂ := by simp [lookup_cons_atom]
              rw [l₁', l₂']
              constructor
              · rintro ⟨T, h, hv⟩; exact absurd ⟨h, hv⟩ (below rest T v)
              · rintro ⟨⟨_, e₁, hv₁⟩, ⟨_, e₂, hv₂⟩⟩
                cases e₁; cases e₂
                exact absurd ((semc v).mpr ⟨hv₁, hv₂⟩) (semE.mp rfl v)
            · have e₁ : mapLookup ((.atom a, T₁) :: xs) (.atom s) = mapLookup xs (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              have e₂ : mapLookup ((.atom a, T₂) :: ys) (.atom s) = mapLookup ys (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              rw [e₁, e₂]; exact sem s v
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        obtain ⟨l, run, dl, keys, sem⟩ := ih ((.atom a, T₁) :: xs) ys (by simp; omega) d₁ (tail d₂)
        refine ⟨l, ?_, dl, keys, fun s v => ?_⟩
        · have r := run
          simp only [fieldsTerm] at r
          rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
          exact r
        · by_cases bs : b = s
          · subst bs
            have na : ∀ z ∈ (Term.atom a, T₁) :: xs, Term.compare (Term.fuel (.atom b) z.1) (.atom b) z.1 = .lt := fun z mz => by
              rcases List.mem_cons.mp mz with rfl | mz
              · exact cmp'
              · exact cmp_lt_trans cmp' (h₁ z mz)
            rw [sem]
            constructor
            · rintro ⟨⟨T, h, hv⟩, -⟩; exact absurd ⟨h, hv⟩ (below na T v)
            · rintro ⟨⟨T, h, hv⟩, -⟩; exact absurd ⟨h, hv⟩ (below na T v)
          · have e₂ : mapLookup ((.atom b, T₂) :: ys) (.atom s) = mapLookup ys (.atom s) := by
              rw [lookup_cons_atom, ite_eq_right bs]
            rw [e₂]; exact sem s v

theorem tagSem_closed' {kind : String} {o : Option V} : TagSem den (.atom "closed") kind o ↔ o = Option.none := by
  simp [TagSem]

/-- `map_domain_intersection/3` on tags of value maps: the tag allowing at keys of every kind what both allow. -/
theorem domain_inter_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {t₁ t₂ : Term} (g₁ : TagV E t₁) (g₂ : TagV E t₂) :
    ∃ tR, Elixir.Module.Types.Descr.«map_domain_intersection/3» (D m) t₁ t₂ (.map S) = .ok tR ∧ TagV E tR ∧
      ∀ (kind : String) o, TagSem den tR kind o ↔ TagSem den t₁ kind o ∧ TagSem den t₂ kind o := by
  have hnone := (sem_none ops dops esem).2
  have closedL : ∀ t, ∀ kind (o : Option V), TagSem den (.atom "closed") kind o ↔ TagSem den (.atom "closed") kind o ∧ TagSem den t kind o :=
    fun t kind o => ⟨fun h => ⟨h, by rw [tagSem_closed'.mp h]; exact tagSem_none _ _⟩, fun h => h.1⟩
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, d₁⟩
  · refine ⟨t₂, ?_, g₂, fun kind o => ⟨fun h => ⟨Or.inl rfl, h⟩, fun h => h.2⟩⟩
    rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]
    rcases g₂ with rfl | rfl | ⟨dl₂, rfl, _⟩ <;> simp [fieldsTerm_ne_atom]
  · exact ⟨_, by rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp, Or.inr (Or.inl rfl), closedL t₂⟩
  · rcases g₂ with rfl | rfl | ⟨dl₂, rfl, d₂⟩
    · exact ⟨_, by rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp [fieldsTerm_ne_atom],
        Or.inr (Or.inr ⟨dl₁, rfl, d₁⟩), fun kind o => ⟨fun h => ⟨h, Or.inl rfl⟩, fun h => h.1⟩⟩
    · exact ⟨_, by rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp [fieldsTerm_ne_atom],
        Or.inr (Or.inl rfl), fun kind o => (closedL (fieldsTerm dl₁) kind o).trans And.comm⟩
    · obtain ⟨l, run, dl, -, sem⟩ := domain_fields_val ops dops esem hm hS _ dl₁ dl₂ (Nat.le_refl _) d₁ d₂
      have step : Elixir.Module.Types.Descr.«map_domain_intersection/3» (D m) (fieldsTerm dl₁) (fieldsTerm dl₂)
          (.map S) = (match fieldsTerm l with
            | .nil => Except.ok (Term.atom "closed")
            | t => Except.ok t) := by
        have ne₁ := fieldsTerm_ne_atom dl₁
        have ne₂ := fieldsTerm_ne_atom dl₂
        have r := run
        generalize fieldsTerm dl₁ = T₁ at r ne₁
        generalize fieldsTerm dl₂ = T₂ at r ne₂
        rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]
        split
        · exact absurd rfl (ne₁ "closed")
        · exact absurd rfl (ne₂ "closed")
        · exact absurd rfl (ne₁ "open")
        · exact absurd rfl (ne₂ "open")
        · simp only [r]
          cases fieldsTerm l <;> rfl
      have both : ∀ kind o, (TagSem den (fieldsTerm dl₁) kind o ∧ TagSem den (fieldsTerm dl₂) kind o) ↔
          (o = Option.none ∨ ∃ v T, o = some v ∧ mapLookup l (.atom kind) = some T ∧ den T v) := by
        intro kind o
        rw [tagSem_dom_iff hnone, tagSem_dom_iff hnone]
        rcases o with _ | v
        · simp
        · have := sem kind v
          simp only [reduceCtorEq, false_or, Option.some.injEq] at this ⊢
          simp only [exists_and_left, exists_eq_left'] at this ⊢
          exact this.symm
      cases l with
      | nil =>
        refine ⟨_, by rw [step]; rfl, Or.inr (Or.inl rfl), fun kind o => ?_⟩
        rw [both, tagSem_closed']
        simp [mapLookup]
      | cons x xs =>
        refine ⟨_, by rw [step]; simp [fieldsTerm, Term.list], Or.inr (Or.inr ⟨x :: xs, rfl, dl⟩), fun kind o => ?_⟩
        rw [both, tagSem_dom_iff hnone]

def mergeFunV (ifun : Term) (S : List (Term × Term)) : Term :=
  .function false "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-0-" 3 #[ifun, .map S]

/-- The merge function of open literals meets fields, throwing `:empty` on required empty meets. -/
theorem merge_fun_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf n : Nat} (hK : Kf ≤ n) (hn : K ≤ n) {ifun : Term} (hI : IFun E den Kf ifun) {S : List (Term × Term)}
    (hS : Safe S) (key : Term) {t₁ t₂ : Term} (f₁ : E t₁) (f₂ : E t₂) (o₁ o₂ : Bool) :
    ∃ c, E c ∧ (∀ x, den c x ↔ den t₁ x ∧ den t₂ x) ∧
      ((¬((o₁ && o₂) = Bool.false ∧ ∀ x, ¬den c x) ∧
        Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) key
          (.tuple #[t₁, boolAtom o₁]) (.tuple #[t₂, boolAtom o₂]) = .ok (.tuple #[c, boolAtom (o₁ && o₂)])) ∨
       (((o₁ && o₂) = Bool.false ∧ ∀ x, ¬den c x) ∧
        Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) key
          (.tuple #[t₁, boolAtom o₁]) (.tuple #[t₂, boolAtom o₂]) = .error (Exception.throw (.atom "empty")))) := by
  obtain ⟨c, bc, lc, semc, disp, emp, empSem⟩ := meet_run ops dops esem hK hn hI hS f₁ f₂
  refine ⟨c, lc, semc, ?_⟩
  by_cases thrown : (o₁ && o₂) = Bool.false ∧ bc = Bool.true
  · obtain ⟨o, rfl⟩ := thrown
    right
    refine ⟨⟨o, empSem.mp rfl⟩, ?_⟩
    unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
    cases o₁ <;> cases o₂ <;> simp at o <;>
      simp [boolAtom, Lynx.Except.andAlso, disp, emp, isMember]
  · left
    refine ⟨fun ⟨o, e⟩ => thrown ⟨o, empSem.mpr e⟩, ?_⟩
    unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
    cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
      simp [boolAtom, Lynx.Except.andAlso, disp, emp, isMember]

/-- `orddict:merge/3` of open literals on value maps. -/
theorem merge_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf n : Nat} (hK : Kf ≤ n) (hn : K ≤ n) {ifun : Term} (hI : IFun E den Kf ifun) {S : List (Term × Term)}
    (hS : Safe S) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → FieldsV E l₁ → FieldsV E l₂ →
      InterV E den (Erlang.orddict.«merge/3» (D (n + 1)) (mergeFunV ifun S) (fieldsTerm l₁) (fieldsTerm l₂))
        (Term.atom "open") (Term.atom "open") (Term.atom "open") l₁ l₂ (l₁ ++ l₂) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    left
    refine ⟨[], ?_, h₁, by simp, fun s o => by simp [fsem_nil]⟩
    unfold Erlang.orddict.«merge/3»
    simp [fieldsTerm, mergeFunV, Erlang.erlang.«is_function/2»]
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ =>
      left
      refine ⟨l₂, ?_, h₂, fun e me => ⟨e, by simp [me], rfl⟩, fun s o => by simp [fsem_nil]⟩
      unfold Erlang.orddict.«merge/3»
      cases l₂ <;> simp [fieldsTerm, mergeFunV, Erlang.erlang.«is_function/2»]
    | x :: xs, [] =>
      left
      refine ⟨x :: xs, ?_, h₁, fun e me => ⟨e, by simp at me ⊢; exact me, rfl⟩, fun s o => by simp [fsem_nil]⟩
      unfold Erlang.orddict.«merge/3»
      simp [fieldsTerm, mergeFunV, Erlang.erlang.«is_function/2»]
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨t₁, o₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      obtain ⟨t₂, o₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have sx := fieldsV_tail h₁
      have sy := fieldsV_tail h₂
      have hx := fieldsV_head h₁
      have hy := fieldsV_head h₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · have above : ∀ e ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp
          · exact cmp_lt_trans cmp (hy e me)
        rcases ih xs _ (by simp; omega) sx h₂ with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
        · left
          refine ⟨(.atom a, .tuple #[t₁, boolAtom o₁]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
          · unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», cmp] at run ⊢
            simp [run]
          · refine fieldsV_cons ⟨a, rfl⟩ ⟨t₁, _, rfl, f₁⟩ sl fun e me => ?_
            obtain ⟨e', me', ee⟩ := keys e me
            rw [ee]
            rcases List.mem_append.mp me' with m' | m'
            · exact hx e' m'
            · exact above e' m'
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨_, by simp, rfl⟩
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by rcases List.mem_append.mp me' with h | h <;> simp [h], ee⟩
          · by_cases e : a = s
            · subst e
              rw [fsem_cons_self, fsem_cons_self, fsem_none (lookup_above above)]
              exact ⟨fun h => ⟨h, Or.inl rfl⟩, fun h => h.1⟩
            · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
        · right
          refine ⟨disj_cons₁ h₁ above disj, ?_⟩
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp] at run ⊢
          simp [run]
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, lc, semc, ⟨nt, lam⟩ | ⟨thrown, lam⟩⟩ := merge_fun_val ops dops esem hK hn hI hS (.atom a) f₁ f₂ o₁ o₂
        · rcases ih xs ys (by omega) sx sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨(.atom a, .tuple #[c, boolAtom (o₁ && o₂)]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
            · unfold Erlang.orddict.«merge/3»
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», mergeFunV,
                Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure] at run ⊢
              simp [lam, run]
            · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
              obtain ⟨e', me', ee⟩ := keys e me
              rw [ee]
              rcases List.mem_append.mp me' with m' | m'
              · exact hx e' m'
              · exact hy e' m'
            · rcases List.mem_cons.mp me with rfl | me
              · exact ⟨_, List.mem_cons_self, rfl⟩
              · obtain ⟨e', me', ee⟩ := keys e me
                exact ⟨e', by rcases List.mem_append.mp me' with h | h <;> simp [h], ee⟩
            · by_cases e : a = s
              · subst e
                rw [fsem_cons_self, fsem_cons_self, fsem_cons_self]
                exact meet_field_sem semc o
              · rw [fsem_cons_ne e, fsem_cons_ne e, fsem_cons_ne e, sem]
          · right
            refine ⟨disj_both h₁ h₂ disj, ?_⟩
            unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», mergeFunV,
              Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure] at run ⊢
            simp [lam, run]
        · right
          refine ⟨⟨a, fun o' ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_cons_self] at g₁ g₂
            exact meet_field_empty semc thrown.1 thrown.2 o' ⟨g₁, g₂⟩
          · unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», mergeFunV,
              Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure]
            simp [lam]
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp'
          · exact cmp_lt_trans cmp' (hx e me)
        rcases ih _ ys (by simp; omega) h₁ sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
        · left
          refine ⟨(.atom b, .tuple #[t₂, boolAtom o₂]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
          · unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
            simp [run]
          · refine fieldsV_cons ⟨b, rfl⟩ ⟨t₂, _, rfl, f₂⟩ sl fun e me => ?_
            obtain ⟨e', me', ee⟩ := keys e me
            rw [ee]
            rcases List.mem_append.mp me' with m' | m'
            · exact above e' m'
            · exact hy e' m'
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨_, by simp, rfl⟩
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp only [List.mem_append, List.mem_cons] at me'; rcases me' with (h | h) | h <;> simp [h], ee⟩
          · by_cases e : b = s
            · subst e
              rw [fsem_cons_self, fsem_cons_self, fsem_none (lookup_above above)]
              exact ⟨fun h => ⟨Or.inl rfl, h⟩, fun h => h.2⟩
            · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
        · right
          refine ⟨disj_cons₂ h₂ above disj, ?_⟩
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
          simp [run]

def mergeFunV₁ (ifun : Term) (S : List (Term × Term)) : Term :=
  .function false "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-1-" 3 #[ifun, .map S]

theorem merge_fun₁_call (n : Nat) (ifun : Term) (S : List (Term × Term)) (k v₁ v₂ : Term) :
    Lynx.Dispatcher.pure (D (n + 1)) (mergeFunV₁ ifun S) #[k, v₁, v₂] =
      Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) k v₁ v₂ := by
  simp [mergeFunV₁, Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-1-/3».pure,
    merge_fun₁_eq]

/-- `fields_merge_with_defaults/5` on value maps: the fields of each literal meet the field of the other, or its
default field when absent, so the result allows at atom keys what both literals allow. -/
theorem merge_defaults_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf n : Nat} (hK : Kf ≤ n) (hn : K ≤ n) {ifun : Term} (hI : IFun E den Kf ifun)
    {S : List (Term × Term)} (hS : Safe S) {t₁ t₂ tR : Term} (g₁ : TagV E t₁) (g₂ : TagV E t₂)
    (htag : ∀ o, TagSem den tR "atom" o ↔ TagSem den t₁ "atom" o ∧ TagSem den t₂ "atom" o) :
    ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → FieldsV E l₁ → FieldsV E l₂ →
      InterV E den (Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm l₁) (tagField t₁)
        (fieldsTerm l₂) (tagField t₂) (mergeFunV₁ ifun S)) t₁ t₂ tR l₁ l₂ (l₁ ++ l₂) := by
  have df₁ : tagField t₁ = .tuple #[tagType t₁ "atom", boolAtom Bool.true] := rfl
  have df₂ : tagField t₂ = .tuple #[tagType t₂ "atom", boolAtom Bool.true] := rfl
  have E₁ := tagType_value ops g₁ "atom"
  have E₂ := tagType_value ops g₂ "atom"
  have dsem₁ : ∀ {l : List (Term × Term)} {s : String}, mapLookup l (.atom s) = Option.none → ∀ o,
      FSem den t₁ l s o ↔ FieldSem den (.tuple #[tagType t₁ "atom", boolAtom Bool.true]) o := fun h o => by
    rw [← df₁, fieldSem_tagV ops dops esem g₁]; simp only [FSem, h]
  have dsem₂ : ∀ {l : List (Term × Term)} {s : String}, mapLookup l (.atom s) = Option.none → ∀ o,
      FSem den t₂ l s o ↔ FieldSem den (.tuple #[tagType t₂ "atom", boolAtom Bool.true]) o := fun h o => by
    rw [← df₂, fieldSem_tagV ops dops esem g₂]; simp only [FSem, h]
  -- a key of the first literal only, meeting the default field of the second
  have stepL : ∀ (a : String) (u₁ : Term) (p₁ : Bool) (xs l₂ : List (Term × Term)),
      E u₁ → FieldsV E ((.atom a, .tuple #[u₁, boolAtom p₁]) :: xs) → FieldsV E l₂ →
      (∀ e ∈ l₂, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt) →
      InterV E den (Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm xs) (tagField t₁)
        (fieldsTerm l₂) (tagField t₂) (mergeFunV₁ ifun S)) t₁ t₂ tR xs l₂ (xs ++ l₂) →
      InterV E den (Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) (.atom a)
          (.tuple #[u₁, boolAtom p₁]) (tagField t₂) >>= fun c =>
        Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm xs) (tagField t₁)
          (fieldsTerm l₂) (tagField t₂) (mergeFunV₁ ifun S) >>= fun t => pure (Term.cons (.tuple #[.atom a, c]) t))
        t₁ t₂ tR ((Term.atom a, Term.tuple #[u₁, boolAtom p₁]) :: xs) l₂ (((Term.atom a, Term.tuple #[u₁, boolAtom p₁]) :: xs) ++ l₂) := by
    intro a u₁ p₁ xs l₂ f₁ h₁ h₂ above ih
    obtain ⟨c, lc, semc, ⟨-, lam⟩ | ⟨thrown, lam⟩⟩ := merge_fun_val ops dops esem hK hn hI hS (.atom a) f₁ E₂ p₁ Bool.true <;>
      rw [← df₂] at lam
    · rcases ih with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
      · left
        refine ⟨(.atom a, .tuple #[c, boolAtom (p₁ && Bool.true)]) :: l, by simp [lam, run, fieldsTerm_cons], ?_,
          fun e me => ?_, fun s o => ?_⟩
        · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
          obtain ⟨e', me', ee⟩ := keys e me
          rw [ee]
          rcases List.mem_append.mp me' with m' | m'
          · exact fieldsV_head h₁ e' m'
          · exact above e' m'
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨_, List.mem_cons_self, rfl⟩
          · obtain ⟨e', me', ee⟩ := keys e me
            exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
        · by_cases e : a = s
          · subst e
            rw [fsem_cons_self, fsem_cons_self, dsem₂ (lookup_above above)]
            exact meet_field_sem semc o
          · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
      · right
        exact ⟨disj_cons₁ h₁ above disj, by simp [lam, run]⟩
    · right
      refine ⟨⟨a, fun o ⟨g₁', g₂'⟩ => meet_field_empty semc thrown.1 thrown.2 o
        ⟨(fsem_cons_self _ _ _ _ _).mp g₁', (dsem₂ (lookup_above above) o).mp g₂'⟩⟩, by simp [lam]⟩
  -- a key of the second literal only, meeting the default field of the first
  have stepR : ∀ (b : String) (u₂ : Term) (p₂ : Bool) (l₁ ys : List (Term × Term)),
      E u₂ → FieldsV E l₁ → FieldsV E ((.atom b, .tuple #[u₂, boolAtom p₂]) :: ys) →
      (∀ e ∈ l₁, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt) →
      InterV E den (Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm l₁) (tagField t₁)
        (fieldsTerm ys) (tagField t₂) (mergeFunV₁ ifun S)) t₁ t₂ tR l₁ ys (l₁ ++ ys) →
      InterV E den (Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) (.atom b)
          (tagField t₁) (.tuple #[u₂, boolAtom p₂]) >>= fun c =>
        Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm l₁) (tagField t₁)
          (fieldsTerm ys) (tagField t₂) (mergeFunV₁ ifun S) >>= fun t => pure (Term.cons (.tuple #[.atom b, c]) t))
        t₁ t₂ tR l₁ ((Term.atom b, Term.tuple #[u₂, boolAtom p₂]) :: ys) (l₁ ++ (Term.atom b, Term.tuple #[u₂, boolAtom p₂]) :: ys) := by
    intro b u₂ p₂ l₁ ys f₂ h₁ h₂ above ih
    obtain ⟨c, lc, semc, ⟨-, lam⟩ | ⟨thrown, lam⟩⟩ := merge_fun_val ops dops esem hK hn hI hS (.atom b) E₁ f₂ Bool.true p₂ <;>
      rw [← df₁] at lam
    · rcases ih with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
      · left
        refine ⟨(.atom b, .tuple #[c, boolAtom (Bool.true && p₂)]) :: l, by simp [lam, run, fieldsTerm_cons], ?_,
          fun e me => ?_, fun s o => ?_⟩
        · refine fieldsV_cons ⟨b, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
          obtain ⟨e', me', ee⟩ := keys e me
          rw [ee]
          rcases List.mem_append.mp me' with m' | m'
          · exact above e' m'
          · exact fieldsV_head h₂ e' m'
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨(.atom b, .tuple #[u₂, boolAtom p₂]), by simp, rfl⟩
          · obtain ⟨e', me', ee⟩ := keys e me
            exact ⟨e', by rcases List.mem_append.mp me' with h | h <;> simp [h], ee⟩
        · by_cases e : b = s
          · subst e
            rw [fsem_cons_self, fsem_cons_self, dsem₁ (lookup_above above)]
            exact meet_field_sem semc o
          · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
      · right
        exact ⟨disj_cons₂ h₂ above disj, by simp [lam, run]⟩
    · right
      refine ⟨⟨b, fun o ⟨g₁', g₂'⟩ => meet_field_empty semc thrown.1 thrown.2 o
        ⟨(dsem₁ (lookup_above above) o).mp g₁', (fsem_cons_self _ _ _ _ _).mp g₂'⟩⟩, by simp [lam]⟩
  have lk : ∀ s : String, mapLookup ([] : List (Term × Term)) (.atom s) = Option.none := fun s => by simp [mapLookup]
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size _ _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    left
    refine ⟨[], ?_, ⟨by simp, by simp⟩, by simp, fun s o => by simp only [FSem, lk]; exact htag o⟩
    rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]; simp [fieldsTerm, Term.list]
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], [] =>
      left
      refine ⟨[], ?_, ⟨by simp, by simp⟩, by simp, fun s o => by simp only [FSem, lk]; exact htag o⟩
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]; simp [fieldsTerm, Term.list]
    | [], (k₂, v₂) :: ys =>
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨u₂, p₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have r := stepR b u₂ p₂ [] ys f₂ h₁ h₂ (by simp) (ih [] ys (by simp at size ⊢; omega) h₁ (fieldsV_tail h₂))
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
      simpa [fieldsTerm, Term.list, merge_fun₁_call] using r
    | (k₁, v₁) :: xs, [] =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨u₁, p₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      have r := stepL a u₁ p₁ xs [] f₁ h₁ h₂ (by simp) (ih xs [] (by simp at size ⊢; omega) (fieldsV_tail h₁) h₂)
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
      simpa [fieldsTerm, Term.list, merge_fun₁_call] using r
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨u₁, p₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      obtain ⟨u₂, p₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have sx := fieldsV_tail h₁
      have sy := fieldsV_tail h₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · have above : ∀ e ∈ (Term.atom b, Term.tuple #[u₂, boolAtom p₂]) :: ys, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp
          · exact cmp_lt_trans cmp (fieldsV_head h₂ e me)
        have r := stepL a u₁ p₁ xs _ f₁ h₁ h₂ above (ih xs _ (by simp; omega) sx h₂)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simpa [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», cmp] using r
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, lc, semc, ⟨-, lam⟩ | ⟨thrown, lam⟩⟩ := merge_fun_val ops dops esem hK hn hI hS (.atom a) f₁ f₂ p₁ p₂
        · rcases ih xs ys (by omega) sx sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨(.atom a, .tuple #[c, boolAtom (p₁ && p₂)]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
            · rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
              simp [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», Erlang.erlang.«>/2»] at run ⊢
              simp [lam, run]
            · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
              obtain ⟨e', me', ee⟩ := keys e me
              rw [ee]
              rcases List.mem_append.mp me' with m' | m'
              · exact fieldsV_head h₁ e' m'
              · exact fieldsV_head h₂ e' m'
            · rcases List.mem_cons.mp me with rfl | me
              · exact ⟨_, List.mem_cons_self, rfl⟩
              · obtain ⟨e', me', ee⟩ := keys e me
                exact ⟨e', by rcases List.mem_append.mp me' with h | h <;> simp [h], ee⟩
            · by_cases e : a = s
              · subst e
                rw [fsem_cons_self, fsem_cons_self, fsem_cons_self]
                exact meet_field_sem semc o
              · rw [fsem_cons_ne e, fsem_cons_ne e, fsem_cons_ne e, sem]
          · right
            refine ⟨disj_both h₁ h₂ disj, ?_⟩
            rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
            simp [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», Erlang.erlang.«>/2»] at run ⊢
            simp [lam, run]
        · right
          refine ⟨⟨a, fun o ⟨g₁', g₂'⟩ => ?_⟩, ?_⟩
          · rw [fsem_cons_self] at g₁' g₂'
            exact meet_field_empty semc thrown.1 thrown.2 o ⟨g₁', g₂'⟩
          · rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
            simp [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
            simp [lam]
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ e ∈ (Term.atom a, Term.tuple #[u₁, boolAtom p₁]) :: xs, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp'
          · exact cmp_lt_trans cmp' (fieldsV_head h₁ e me)
        have r := stepR b u₂ p₂ _ ys f₂ h₁ h₂ above (ih _ ys (by simp; omega) h₁ sy)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simpa [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] using r

/-- Map literal intersections on value maps: a literal of the maps of both, or `:empty` when they share none. -/
def LitInterV (E : Term → Prop) (den : Term → V → Prop) (r : Except Exception Term) (t₁ t₂ : Term) (l₁ l₂ : List (Term × Term)) : Prop :=
  (∃ (tR : Term) (l : List (Term × Term)), r = .ok (.tuple #[tR, fieldsTerm l]) ∧ TagV E tR ∧ FieldsV E l ∧
    ∀ w, MSem den tR l w ↔ MSem den t₁ l₁ w ∧ MSem den t₂ l₂ w) ∨
  ((∀ w, ¬(MSem den t₁ l₁ w ∧ MSem den t₂ l₂ w)) ∧ r = .error (Exception.throw (.atom "empty")))

theorem InterV.lit {r : Except Exception Term} {t₁ t₂ tR : Term} {l₁ l₂ ks : List (Term × Term)}
    (h : InterV E den r t₁ t₂ tR l₁ l₂ ks) (g : TagV E tR)
    (dom : ∀ kind o, TagSem den tR kind o ↔ TagSem den t₁ kind o ∧ TagSem den t₂ kind o) :
    LitInterV E den (r >>= fun f => pure (Term.tuple #[tR, f])) t₁ t₂ l₁ l₂ := by
  rcases h with ⟨l, run, sl, -, sem⟩ | ⟨⟨s, hs⟩, run⟩
  · refine Or.inl ⟨tR, l, by simp [run], g, sl, fun w => ?_⟩
    exact ⟨fun h => ⟨⟨fun s => ((sem s _).mp (h s)).1, fun k i => ((dom _ _).mp (h.doms k i)).1⟩,
        ⟨fun s => ((sem s _).mp (h s)).2, fun k i => ((dom _ _).mp (h.doms k i)).2⟩⟩,
      fun h => ⟨fun s => (sem s _).mpr ⟨h.1 s, h.2 s⟩, fun k i => (dom _ _).mpr ⟨h.1.doms k i, h.2.doms k i⟩⟩⟩
  · exact Or.inr ⟨fun w h => hs (w (.atom s)) ⟨h.1 s, h.2 s⟩, by simp [run]⟩

/-- Open and closed tags allow at keys outside fields what both allow when open exactly if both are. -/
theorem tagSem_atom_meet {t₁ t₂ tR : String} (htag : tR = "open" ↔ t₁ = "open" ∧ t₂ = "open") (kind : String)
    (o : Option V) : TagSem den (.atom tR) kind o ↔ TagSem den (.atom t₁) kind o ∧ TagSem den (.atom t₂) kind o := by
  simp only [tagSem_atom]
  constructor
  · rintro (h | h)
    · obtain ⟨h₁, h₂⟩ := htag.mp h
      exact ⟨Or.inl h₁, Or.inl h₂⟩
    · exact ⟨Or.inr h, Or.inr h⟩
  · rintro ⟨h₁ | h₁, h₂ | h₂⟩
    · exact Or.inl (htag.mpr ⟨h₁, h₂⟩)
    all_goals exact Or.inr ‹_›

theorem LitInterV.swap {r : Except Exception Term} {t₁ t₂ : Term} {l₁ l₂ : List (Term × Term)}
    (h : LitInterV E den r t₂ t₁ l₂ l₁) : LitInterV E den r t₁ t₂ l₁ l₂ := by
  rcases h with ⟨tR, l, run, g, sl, sem⟩ | ⟨disj, run⟩
  · exact Or.inl ⟨tR, l, run, g, sl, fun w => (sem w).trans And.comm⟩
  · exact Or.inr ⟨fun w h => disj w ⟨h.2, h.1⟩, run⟩

/-- `map_literal_intersection/6` on value maps. -/
theorem literal_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf m : Nat} (hK : Kf + 1 ≤ m) (hm : K + 1 ≤ m) {ifun : Term} (hI : IFun E den Kf ifun)
    {S : List (Term × Term)} (hS : Safe S) {t₁ t₂ : Term} (g₁ : TagV E t₁) (g₂ : TagV E t₂)
    {l₁ l₂ : List (Term × Term)} (h₁ : FieldsV E l₁) (h₂ : FieldsV E l₂) :
    LitInterV E den (Elixir.Module.Types.Descr.«map_literal_intersection/6» (D m) t₁ (fieldsTerm l₁) t₂
      (fieldsTerm l₂) ifun (.map S)) t₁ t₂ l₁ l₂ := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show 1 ≤ m by omega)
  have hK' : Kf ≤ n + 1 := by omega
  have general : (∀ s₁ s₂, ¬(t₁ = .atom s₁ ∧ t₂ = .atom s₂)) → LitInterV E den
      (Elixir.Module.Types.Descr.«map_literal_intersection/6» (D (n + 1)) t₁ (fieldsTerm l₁) t₂ (fieldsTerm l₂)
        ifun (.map S)) t₁ t₂ l₁ l₂ := by
    intro notAtoms
    obtain ⟨tR, runT, gR, semT⟩ := domain_inter_val ops dops esem (show K ≤ n + 1 by omega) hS g₁ g₂
    have merged := (merge_defaults_val ops dops esem (show Kf ≤ n by omega) (by omega) hI hS g₁ g₂ (semT "atom") _ l₁ l₂
      (Nat.le_refl _) h₁ h₂).lit gR semT
    unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»
    split <;> try (exfalso; exact notAtoms _ _ ⟨rfl, rfl⟩)
    simpa [key_tag_field g₁, key_tag_field g₂, runT, mergeFunV₁] using merged
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, -⟩ <;> rcases g₂ with rfl | rfl | ⟨dl₂, rfl, -⟩ <;>
    try exact general (fun _ _ h => fieldsTerm_ne_atom _ _ (by first | exact h.1 | exact h.2))
  all_goals unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»; simp only [pure_bind]
  · exact (merge_val ops dops esem (show Kf ≤ n by omega) (by omega) hI hS _ l₁ l₂ (Nat.le_refl _) h₁ h₂).lit
      (TagV.atom (Or.inl rfl)) (tagSem_atom_meet (by simp))
  · exact (open_closed_val ops dops esem hK' (by omega) hI hS _ l₁ l₂ (Nat.le_refl _) h₁ h₂).lit
      (TagV.atom (Or.inr rfl)) (tagSem_atom_meet (by simp))
  · exact LitInterV.swap ((open_closed_val ops dops esem hK' (by omega) hI hS _ l₂ l₁ (Nat.le_refl _) h₂ h₁).lit
      (TagV.atom (Or.inr rfl)) (tagSem_atom_meet (by simp)))
  · exact (closed_val ops dops esem hK' (by omega) hI hS _ l₁ l₂ (Nat.le_refl _) h₁ h₂).lit
      (TagV.atom (Or.inr rfl)) (tagSem_atom_meet (by simp))

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-! Map BDD emptiness on value maps. -/

theorem bare_ifun (ops : ElemOk E K) (_dops : ElemDiff E K) (esem : ElemSem E K V den Safe) : IFun E den (K + 1) bareIntersection := by
  intro m hm a b ha hb
  obtain ⟨c, hc, run⟩ := ops.inter ha hb
  refine ⟨c, hc, esem.inter ha hb (Nat.le_refl K) (run K (Nat.le_refl K)), ?_⟩
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show 1 ≤ m by omega)
  rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]
  exact run n (by omega)

/-- Fields that compare equal allow the same values. -/
theorem fields_compare (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) : ∀ {l l' : List (Term × Term)}, FieldsV E l → FieldsV E l' →
    compare (fuel (fieldsTerm l) (fieldsTerm l')) (fieldsTerm l) (fieldsTerm l') = .eq → ∀ (tag : Term) s o, FSem den tag l s o ↔ FSem den tag l' s o
  | [], [], _, _, _, _, _, _ => Iff.rfl
  | [], _ :: _, _, _, e, _, _, _ => by simp [fieldsTerm, Term.list] at e
  | _ :: _, [], _, _, e, _, _, _ => by simp [fieldsTerm, Term.list] at e
  | (k, f) :: l, (k', f') :: l', h, h', e, tag, s, o => by
    simp only [fieldsTerm_cons, compare_cons, Ordering.then_eq_eq] at e
    obtain ⟨e₁, e₂⟩ := e
    obtain ⟨a, rfl⟩ := (h.1 _ List.mem_cons_self).1
    obtain ⟨a', rfl⟩ := (h'.1 _ List.mem_cons_self).1
    obtain ⟨t, o₁, rfl, ht⟩ := (h.1 _ List.mem_cons_self).2
    obtain ⟨t', o₂, rfl, ht'⟩ := (h'.1 _ List.mem_cons_self).2
    simp [compare_tuple, List.compareLex_cons_cons] at e₁
    obtain ⟨rfl, ⟨et, eo, -⟩, -⟩ := e₁
    have oo : o₁ = o₂ := by
      cases o₁ <;> cases o₂ <;> simp_all [boolAtom] <;> simp [Term.compare_step, Compare.compareStep] at eo
    subst oo
    have ih := fields_compare ops dops esem (fieldsV_tail h) (fieldsV_tail h') e₂ tag s o
    by_cases as : a = s
    · subst as
      rw [fsem_cons_self, fsem_cons_self, fieldSem_mk, fieldSem_mk]
      have d : ∀ x, den t x ↔ den t' x := fun x =>
        ⟨esem.resp ht' ht (Lynx.Term.compare_eq_symm et), esem.resp ht ht' et⟩
      simp [d]
    · rw [fsem_cons_ne as, fsem_cons_ne as]
      exact ih

/-- Domains that compare equal have the same kinds, with types that compare equal. -/
theorem doms_compare : ∀ {dl dl' : List (Term × Term)}, DomsV E dl → DomsV E dl' →
    compare (fuel (fieldsTerm dl) (fieldsTerm dl')) (fieldsTerm dl) (fieldsTerm dl') = .eq → ∀ s : String,
      (mapLookup dl (.atom s) = Option.none ∧ mapLookup dl' (.atom s) = Option.none) ∨
      ∃ T T', mapLookup dl (.atom s) = some T ∧ mapLookup dl' (.atom s) = some T' ∧ compare (fuel T T') T T' = .eq
  | [], [], _, _, _, s => Or.inl ⟨by simp [mapLookup], by simp [mapLookup]⟩
  | [], _ :: _, _, _, e, _ => by simp [fieldsTerm, Term.list] at e
  | _ :: _, [], _, _, e, _ => by simp [fieldsTerm, Term.list] at e
  | (k, T) :: l, (k', T') :: l', h, h', e, s => by
    simp only [fieldsTerm_cons, compare_cons, Ordering.then_eq_eq] at e
    obtain ⟨e₁, e₂⟩ := e
    obtain ⟨⟨a, rfl, -⟩, -⟩ := h.1 _ List.mem_cons_self
    obtain ⟨⟨a', rfl, -⟩, -⟩ := h'.1 _ List.mem_cons_self
    have t : DomsV E l := ⟨fun e me => h.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp h.2).2⟩
    have t' : DomsV E l' := ⟨fun e me => h'.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp h'.2).2⟩
    simp [compare_tuple, List.compareLex_cons_cons] at e₁
    obtain ⟨rfl, et, -⟩ := e₁
    by_cases as : a = s
    · subst as
      exact Or.inr ⟨T, T', by simp [lookup_cons_atom], by simp [lookup_cons_atom], et⟩
    · rw [lookup_cons_atom, ite_eq_right as, lookup_cons_atom, ite_eq_right as]
      exact doms_compare t t' e₂ s

/-- Tags that compare equal allow the same values. -/
theorem tagSem_compare (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {tag tag' : Term}
    (g : TagV E tag) (g' : TagV E tag') (e : compare (fuel tag tag') tag tag' = .eq) (kind : String) (o : Option V) :
    TagSem den tag kind o ↔ TagSem den tag' kind o := by
  have hnone := (sem_none ops dops esem).2
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · rw [(compare_eq_atom _ _).mp (Lynx.Term.compare_eq_symm e)]
  · rw [(compare_eq_atom _ _).mp (Lynx.Term.compare_eq_symm e)]
  · rcases g' with rfl | rfl | ⟨dl', rfl, dv'⟩
    · exact absurd ((compare_eq_atom _ _).mp e) (fieldsTerm_ne_atom _ _)
    · exact absurd ((compare_eq_atom _ _).mp e) (fieldsTerm_ne_atom _ _)
    · rw [tagSem_dom_iff hnone, tagSem_dom_iff hnone]
      rcases doms_compare dv dv' e kind with ⟨n, n'⟩ | ⟨T, T', hT, hT', et⟩
      · simp [n, n']
      · have ET : E T := by obtain ⟨x, mx, -, rfl⟩ := lookup_mem_key hT; exact (dv.1 x mx).2
        have ET' : E T' := by obtain ⟨x, mx, -, rfl⟩ := lookup_mem_key hT'; exact (dv'.1 x mx).2
        have d : ∀ v, den T v ↔ den T' v := fun v =>
          ⟨esem.resp ET' ET (Lynx.Term.compare_eq_symm et), esem.resp ET ET' et⟩
        simp [hT, hT', d]

/-- Map lines: a tag and fields of value maps. -/
def MapPosV (E : Term → Prop) (p : Term) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)), p = .tuple #[tag, fieldsTerm l] ∧ TagV E tag ∧ FieldsV E l

def InPosM (den : Term → V → Prop) (p : Term) (w : (MW V)) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)), p = .tuple #[tag, fieldsTerm l] ∧ MSem den tag l w

theorem inPosM_iff {tag : Term} {l : List (Term × Term)} {w : (MW V)} :
    InPosM den (.tuple #[tag, fieldsTerm l]) w ↔ MSem den tag l w := by
  constructor
  · rintro ⟨tag', l', e, h⟩
    simp only [Term.tuple.injEq] at e
    have e₀ := congrArg (fun a : Array Term => a[0]?) e
    have e₁ := congrArg (fun a : Array Term => a[1]?) e
    simp at e₀ e₁
    rw [e₀, fieldsTerm_inj e₁]
    exact h
  · intro h; exact ⟨tag, l, rfl, h⟩

open Classical in
/-- The valuation of map literals that a map of values induces, up to comparison. -/
noncomputable def valM (E : Term → Prop) (den : Term → V → Prop) (w : (MW V)) (t : Term) : Bool := decide (∃ t', compare (fuel t t') t t' = .eq ∧ MapLitV E t' ∧ NSem den t' w)

theorem valM_resp (w : (MW V)) : Resp (valM E den w) := by
  intro a b h
  simp only [valM]
  congr 1
  apply propext
  constructor
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm h) e, rest⟩
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans h e, rest⟩

theorem valM_true {w : (MW V)} {t : Term} (ht : MapLitV E t) (h : NSem den t w) : valM E den w t = Bool.true := by
  simp only [valM, decide_eq_true_eq]
  exact ⟨t, compare_self t, ht, h⟩

theorem valM_lit (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {w : (MW V)} {t : Term} (ht : MapLitV E t) (h : valM E den w t = Bool.true) : NSem den t w := by
  simp only [valM, decide_eq_true_eq] at h
  obtain ⟨t', e, ⟨k', tag', l', rfl, g', sl'⟩, hn⟩ := h
  obtain ⟨k, tag, l, rfl, g, sl⟩ := ht
  simp only [compare_tuple, Array.size, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
    Ordering.eq_then, List.compareLex_cons_cons, Ordering.then_eq_eq] at e
  obtain ⟨-, et, el, -⟩ := e
  rw [nsem_lit] at hn ⊢
  have ts := tagSem_compare ops dops esem g g' et
  refine ⟨fun s => ?_, fun k i => (ts _ _).mpr (hn.doms k i)⟩
  have := (fields_compare ops dops esem sl sl' el tag' s (w (.atom s))).mpr (hn s)
  unfold FSem at this ⊢
  cases h : mapLookup l (.atom s) <;> simp only [h] at this ⊢
  · exact (ts _ _).mpr this
  · exact this

theorem valM_iff (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {w : (MW V)} {t : Term} (ht : MapLitV E t) : valM E den w t = Bool.true ↔ NSem den t w :=
  ⟨valM_lit ops dops esem ht, valM_true ht⟩

/-- `map_line_intersection/3` on value maps. -/
theorem inter_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 2 ≤ m) {S : List (Term × Term)} (hS : Safe S) {pos lit : Term}
    (hp : MapPosV E pos) (hl : MapLitV E lit) :
    (Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) pos lit (.map S) = .ok (.atom "empty") ∧
      ∀ w, InPosM den pos w → ¬NSem den lit w) ∨
    ∃ pos', Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) pos lit (.map S) = .ok pos' ∧ MapPosV E pos' ∧
      ∀ w, InPosM den pos' w ↔ InPosM den pos w ∧ NSem den lit w := by
  obtain ⟨tag, l, rfl, gt, sl⟩ := hp
  obtain ⟨k, ntag, nl, rfl, gn, snl⟩ := hl
  rcases literal_val ops dops esem (Kf := K + 1) (show K + 1 + 1 ≤ m by omega) (by omega) (bare_ifun ops dops esem) hS gt gn sl snl with
    ⟨tR, l', run, gR, sl', sem⟩ | ⟨disj, run⟩
  · right
    refine ⟨_, ?_, ⟨tR, l', rfl, gR, sl'⟩, fun w => ?_⟩
    · unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
      simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
      simp [run]
    · rw [inPosM_iff, inPosM_iff, nsem_lit]; exact sem w
  · left
    refine ⟨?_, fun w hw hn => disj w ⟨inPosM_iff.mp hw, nsem_lit.mp hn⟩⟩
    unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
    simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
    simp [run, Lynx.Exception.classTerm, Lynx.Exception.reason]

/-- No map of values along the path, outside the negated literals, satisfies the BDD. -/
def ValUnsatM (E : Term → Prop) (den : Term → V → Prop) (pos : Term) (negs : List Term) (r : Term) : Prop :=
  ∀ w, InPosM den pos w → (∀ N ∈ negs, ¬NSem den N w) → eval (valM E den w) r = Bool.false

theorem covM_of_unsat {pos : Term} {negs : List Term} {w : (MW V)}
    (h : InPosM den pos w → (∀ N ∈ negs, ¬NSem den N w) → False) (hw : InPosM den pos w) : CovM den negs w :=
  Classical.byContradiction fun none => h hw fun N mN hN => none ⟨N, mN, hN⟩

theorem map_bdd_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    (jsem : ElemDisjSem E K V den Safe) {m : Nat} (hm : K + 4 ≤ m) (S : List (Term × Term)) (hS : Safe S) {ok : Term → Prop} {r : Term}
    (wr : Bdd ok r) :
    (∀ t, ok t → MapLitV E t) → ∀ pos negs, MapPosV E pos → (∀ t ∈ negs, MapLitV E t) → ValUnsatM E den pos negs r →
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true") := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLitV E t) → ∀ pos negs, MapPosV E pos →
    (∀ t ∈ negs, MapLitV E t) → ValUnsatM E den pos negs r →
    Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits g
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    simp only
    exact init_val ops dops esem jops jsem (by omega) hS gt sl lits fun w hw =>
      covM_of_unsat (fun hw' nn => by have := g w hw' nn; simp at this) (inPosM_iff.mpr hw)
  · intro ok _ pos negs _ _ _
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    split <;> simp_all
  · intro ok k x y okl okLit pos negs hp lits g
    have hl := okLit _ okl
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    rcases inter_val ops dops esem (m := m) (by omega) hS hp hl with ⟨empty, -⟩ | ⟨pos', run, hp', sem'⟩
    · simp [empty]
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp'
    simp [run]
    refine init_val ops dops esem jops jsem (by omega) hS gt sl lits fun w hw => ?_
    obtain ⟨hpos, hlit⟩ := (sem' w).mp (inPosM_iff.mpr hw)
    refine covM_of_unsat (fun hw' nn => ?_) hpos
    have := g w hw' nn
    rw [eval_leaf, valM_true hl hlit] at this
    cases this
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits g
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → MapLitV E t := fun t ht => okLit t ht.1
    have dPart : Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list (lit :: negs)) d (.map S) =
        .ok (.atom "true") := by
      refine idd okLit' pos (lit :: negs) hp (fun t m => ?_) fun w hw nn => ?_
      · rcases List.mem_cons.mp m with rfl | m
        · exact hl
        · exact lits t m
      have nl : valM E den w lit = Bool.false := by
        cases e : valM E den w lit
        · rfl
        · exact absurd (valM_lit ops dops esem hl e) (nn lit List.mem_cons_self)
      have := g w hw fun N mN => nn N (List.mem_cons_of_mem _ mN)
      simp only [eval_node, nl] at this
      simp at this
      exact this.2
    have uPart := iu okLit' pos negs hp lits fun w hw nn => by
      have := g w hw nn
      simp only [eval_node] at this
      cases hu' : eval (valM E den w) u
      · rfl
      · simp [hu'] at this
    rw [list_cons] at dPart
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    rcases inter_val ops dops esem (m := m) (by omega) hS ⟨tag, l, rfl, gt, sl⟩ hl with ⟨empty, -⟩ | ⟨pos2, run, hp2, sem2⟩
    · simp [empty, dPart, uPart, Lynx.Except.andAlso]
    have cRes := ic okLit' pos2 negs hp2 lits fun w hw nn => by
      obtain ⟨hpos, hlit⟩ := (sem2 w).mp hw
      have := g w hpos nn
      simp only [eval_node, valM_true hl hlit] at this
      simp at this
      exact this.1
    obtain ⟨tag2, l2, rfl, -⟩ := hp2
    simp [run, dPart, uPart, Lynx.Except.andAlso, cRes]

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Optimized unions of map literals on value maps. -/

/-- `field_subtype?/2` returns a Boolean, and `true` only when the first field allows less. -/
theorem field_sub_bool (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) :
    ∃ s : Bool, Elixir.Module.Types.Descr.«field_subtype?/2» (D m) f₁ f₂ = .ok (boolAtom s) ∧
      (s = Bool.true → ∀ o, FieldSem den f₁ o → FieldSem den f₂ o) := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  obtain ⟨b, run, sound⟩ := sub_bool ef hm ht₁ ht₂
  refine ⟨(!o₁ || o₂) && b, ?_, fun e o h => ?_⟩
  · rw [Elixir.Module.Types.Descr.«field_subtype?/2».eq_def]
    cases o₁ <;> cases o₂ <;> cases b <;> simp [boolAtom, run, Lynx.Except.andAlso]
  · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at e
    obtain ⟨eo, eb⟩ := e
    rw [fieldSem_mk] at h ⊢
    rcases h with ⟨rfl, rfl⟩ | ⟨x, rfl, hx⟩
    · simp at eo; exact Or.inl ⟨rfl, eo⟩
    · exact Or.inr ⟨x, rfl, sound eb x hx⟩

/-- Fields that compare exactly equal allow the same values. -/
theorem fieldSem_exact (ef : EF nd E V den tl K) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂)
    (h : compareExact (fuel f₂ f₁) f₂ f₁ = .eq) (o : Option V) : FieldSem den f₁ o ↔ FieldSem den f₂ o := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  rw [compareExact_tuple] at h
  simp [List.compareLex_cons_cons] at h
  obtain ⟨et, eo, -⟩ := h
  have oo : o₁ = o₂ := by
    cases o₁ <;> cases o₂ <;> simp_all [boolAtom] <;> simp [compareExact_step, Compare.compareStep] at eo
  subst oo
  have same := same_of_exact ef ht₁ ht₂ et
  rw [fieldSem_mk, fieldSem_mk]
  simp [same _]

theorem fsem_tag_mono {t₁ t₂ s : String} {l : List (Term × Term)} (tags : t₁ = "open" → t₂ = "open") {o : Option V}
    (h : FSem den (.atom t₁) l s o) : FSem den (.atom t₂) l s o := by
  unfold FSem TagSem at h ⊢
  cases e : mapLookup l (.atom s) with
  | some f => simpa [e] using h
  | none =>
    simp only [e] at h ⊢
    rcases h with h | h
    · exact Or.inl (tags h)
    · exact Or.inr h

/-- Fields that agree at a key whatever the tag. -/
def EqvK (den : Term → V → Prop) (P₁ P₂ : List (Term × Term)) (s : String) : Prop := ∀ tag o, FSem den (.atom tag) P₁ s o ↔ FSem den (.atom tag) P₂ s o

/-- What the status of a walk over the fields of two map literals says about the walked fields. -/
def MInv (E : Term → Prop) (den : Term → V → Prop) (t₁ t₂ : String) (st : Term) (P₁ P₂ : List (Term × Term)) : Prop :=
  (st = .atom "all_equal" ∧ ∀ s, EqvK den P₁ P₂ s) ∨
  (∃ (a : String) (p₁ p₂ : Term), st = .tuple #[.atom "one_key_difference", .atom a, p₁, p₂] ∧ t₁ = t₂ ∧
    FieldValue E p₁ ∧ FieldValue E p₂ ∧ mapLookup P₁ (.atom a) = some p₁ ∧
    mapLookup P₂ (.atom a) = some p₂ ∧ ∀ s, s ≠ a → EqvK den P₁ P₂ s) ∨
  (st = .atom "left_subtype_of_right" ∧ ((t₁ = "open" → t₂ = "open") → ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o)) ∨
  (st = .atom "right_subtype_of_left" ∧ ((t₂ = "open" → t₁ = "open") → ∀ s o, FSem den (.atom t₂) P₂ s o → FSem den (.atom t₁) P₁ s o)) ∨
  st = .atom "none"

/-- What the result of the walk says about the fields of two map literals. -/
def MRes (E : Term → Prop) (den : Term → V → Prop) (t₁ t₂ : String) (st : Term) (l₁ l₂ : List (Term × Term)) : Prop :=
  (∃ (a : String) (p₁ p₂ : Term), st = .tuple #[.atom "one_key_difference", .atom a, p₁, p₂] ∧ t₁ = t₂ ∧
    FieldValue E p₁ ∧ FieldValue E p₂ ∧ mapLookup l₁ (.atom a) = some p₁ ∧
    mapLookup l₂ (.atom a) = some p₂ ∧ ∀ s, s ≠ a → EqvK den l₁ l₂ s) ∨
  (st = .atom "left_subtype_of_right" ∧ ∀ s o, FSem den (.atom t₁) l₁ s o → FSem den (.atom t₂) l₂ s o) ∨
  (st = .atom "right_subtype_of_left" ∧ ∀ s o, FSem den (.atom t₂) l₂ s o → FSem den (.atom t₁) l₁ s o) ∨
  st = .atom "none"

/-- Appending a key above the walked ones. -/
theorem lookup_snoc {P : List (Term × Term)} {a s : String} {f : Term}
    (below : ∀ e ∈ P, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) :
    mapLookup (P ++ [(Term.atom a, f)]) (Term.atom s) = if a = s then some f else mapLookup P (Term.atom s) := by
  rw [lookup_append]
  by_cases e : a = s
  · subst e; rw [lookup_below below]; simp [lookup_cons_atom]
  · simp [lookup_cons_atom, e]
    cases mapLookup P (.atom s) <;> simp [mapLookup]

theorem fsem_snoc {tag : String} {P : List (Term × Term)} {a s : String} {f : Term}
    (below : ∀ e ∈ P, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) (o : Option V) :
    FSem den (Term.atom tag) (P ++ [(Term.atom a, f)]) s o ↔ if a = s then FieldSem den f o else FSem den (Term.atom tag) P s o := by
  unfold FSem TagSem
  rw [lookup_snoc below]
  by_cases e : a = s <;> simp [e]

theorem tags_open {t₁ t₂ : String} (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed")
    (h : ¬(t₁ = "open" ∧ t₂ = "closed")) : t₁ = "open" → t₂ = "open" := by
  intro e; subst e; rcases g₂ with rfl | rfl
  · rfl
  · exact absurd ⟨rfl, rfl⟩ h

theorem eqv_sub {t₁ t₂ : String} {P₁ P₂ : List (Term × Term)} (eqv : ∀ s, EqvK den P₁ P₂ s)
    (tags : t₁ = "open" → t₂ = "open") : ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o :=
  fun s o h => (eqv s t₂ o).mp (fsem_tag_mono tags h)

/-- The walk ends on both fields at once. -/
theorem mres_end (d : Dispatcher) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed")
    {st : Term} {P₁ P₂ : List (Term × Term)} (inv : MInv E den t₁ t₂ st P₁ P₂) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» d (fieldsTerm []) (fieldsTerm []) (.atom t₁)
      (.atom t₂) st = .ok res ∧ MRes E den t₁ t₂ res P₁ P₂ := by
  rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
  · -- equal fields: the open literal, if any, is the supertype
    rcases g₁ with rfl | rfl
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, eqv_sub (fun s => fun tag o => (h s tag o).symm)
        fun _ => rfl⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
    · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, eqv_sub h fun e => by simp at e⟩)⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
  · refine ⟨_, ?_, Or.inl ⟨a, p₁, p₂, rfl, h⟩⟩
    rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list]
  · by_cases oc : t₁ = "open" ∧ t₂ = "closed"
    · obtain ⟨rfl, rfl⟩ := oc
      refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, h (tags_open g₁ g₂ oc)⟩)⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
        simp_all [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · by_cases oc : t₂ = "open" ∧ t₁ = "closed"
    · obtain ⟨rfl, rfl⟩ := oc
      refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, h (tags_open g₂ g₁ oc)⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
        simp_all [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list]

theorem fsem_append_notin {tag s : String} {A B : List (Term × Term)} (h : mapLookup B (.atom s) = Option.none)
    (o : Option V) : FSem den (Term.atom tag) (A ++ B) s o ↔ FSem den (Term.atom tag) A s o := by
  unfold FSem TagSem
  rw [lookup_append, h]
  cases mapLookup A (.atom s) <;> simp

/-- Fields of the first literal beyond the second, which is open, keep the first a subtype. -/
theorem left_extend {t₁ : String} {P₁ P₂ r₁ : List (Term × Term)}
    (h : ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom "open") P₂ s o)
    (fresh : ∀ e ∈ r₁, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none) :
    ∀ s o, FSem den (Term.atom t₁) (P₁ ++ r₁) s o → FSem den (Term.atom "open") P₂ s o := by
  intro s o hs
  cases e : mapLookup P₂ (.atom s) with
  | none => exact (fsem_none e o).mpr (Or.inl rfl)
  | some f =>
    have notin : mapLookup r₁ (.atom s) = Option.none :=
      lookup_none fun x mx ex => by rw [fresh x mx s ex] at e; cases e
    exact h s o ((fsem_append_notin notin o).mp hs)

/-- Left subtypes from the walked fields of literals equal everywhere but at one key. -/
theorem one_key_sub {t₁ t₂ a : String} {P₁ P₂ : List (Term × Term)} {p₁ p₂ : Term}
    (l₁ : mapLookup P₁ (.atom a) = some p₁) (l₂ : mapLookup P₂ (.atom a) = some p₂)
    (eqv : ∀ s, s ≠ a → EqvK den P₁ P₂ s) (sub : ∀ o, FieldSem den p₁ o → FieldSem den p₂ o) (tags : t₁ = "open" → t₂ = "open") :
    ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o := by
  intro s o h
  by_cases e : s = a
  · subst e
    unfold FSem TagSem at h ⊢
    rw [l₁] at h; rw [l₂]
    exact sub o h
  · exact (eqv s e t₂ o).mp (fsem_tag_mono tags h)

/-- The walk ends on the second fields first. -/
theorem mres_tail₁ (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {st : Term} {P₁ P₂ : List (Term × Term)} (x : Term × Term)
    (xs : List (Term × Term)) (inv : MInv E den t₁ t₂ st P₁ P₂)
    (fresh : ∀ e ∈ x :: xs, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm (x :: xs)) (fieldsTerm [])
      (Term.atom t₁) (Term.atom t₂) st = .ok res ∧ MRes E den t₁ t₂ res (P₁ ++ x :: xs) (P₂ ++ []) := by
  obtain ⟨k, v⟩ := x
  have none : MRes E den t₁ t₂ (Term.atom "none") (P₁ ++ (k, v) :: xs) (P₂ ++ []) := Or.inr (Or.inr (Or.inr rfl))
  rcases g₂ with rfl | rfl
  · rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
    · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, by
        simpa using left_extend (eqv_sub h (fun _ => rfl)) fresh⟩)⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    · obtain ⟨b, run, sound⟩ := field_sub_bool ef hm hp₁ hp₂
      cases b
      · refine ⟨_, ?_, none⟩
        rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
        rcases g₁ with rfl | rfl <;>
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            run, boolAtom, Erlang.erlang.«/=/2»]
      · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, by
          simpa using left_extend (one_key_sub l₁ l₂ eqv (sound rfl) (fun _ => rfl)) fresh⟩)⟩
        rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
        rcases g₁ with rfl | rfl <;>
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            run, boolAtom, Erlang.erlang.«/=/2»]
    · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, by simpa using left_extend (h fun _ => rfl) fresh⟩)⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    all_goals
      refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
  · refine ⟨_, ?_, none⟩
    rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
    rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl <;>
    rcases g₁ with rfl | rfl <;>
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
        Erlang.erlang.«=:=/2», Erlang.erlang.«/=/2»]

theorem EqvK.symm {P₁ P₂ : List (Term × Term)} {s : String} (h : EqvK den P₁ P₂ s) : EqvK den P₂ P₁ s :=
  fun tag o => (h tag o).symm

/-- The walk ends on the first fields first. -/
theorem mres_tail₂ (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {st : Term} {P₁ P₂ : List (Term × Term)} (y : Term × Term)
    (ys : List (Term × Term)) (inv : MInv E den t₁ t₂ st P₁ P₂)
    (fresh : ∀ e ∈ y :: ys, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm []) (fieldsTerm (y :: ys))
      (Term.atom t₁) (Term.atom t₂) st = .ok res ∧ MRes E den t₁ t₂ res (P₁ ++ []) (P₂ ++ y :: ys) := by
  obtain ⟨k, v⟩ := y
  have none : MRes E den t₁ t₂ (Term.atom "none") (P₁ ++ []) (P₂ ++ (k, v) :: ys) := Or.inr (Or.inr (Or.inr rfl))
  rcases g₁ with rfl | rfl
  · rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
        simpa using left_extend (eqv_sub (fun s => (h s).symm) (fun _ => rfl)) fresh⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    · obtain ⟨b, run, sound⟩ := field_sub_bool ef hm hp₂ hp₁
      cases b
      · refine ⟨_, ?_, none⟩
        rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
        rcases g₂ with rfl | rfl <;>
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            run, boolAtom, Erlang.erlang.«/=/2»]
      · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
          simpa using left_extend (one_key_sub l₂ l₁ (fun s ne => (eqv s ne).symm) (sound rfl) (fun _ => rfl))
            fresh⟩))⟩
        rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
        rcases g₂ with rfl | rfl <;>
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            run, boolAtom, Erlang.erlang.«/=/2»]
    · refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
        simpa using left_extend (h fun _ => rfl) fresh⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    · refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · refine ⟨_, ?_, none⟩
    rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
    rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl <;>
    rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
        Erlang.erlang.«=:=/2», Erlang.erlang.«/=/2»]

/-- A key of the first fields only, below the remaining keys of an open second literal. -/
theorem snoc_left {t₁ : String} {P₁ P₂ : List (Term × Term)} {a : String} {v : Term}
    (h : ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom "open") P₂ s o) (fresh : mapLookup P₂ (.atom a) = Option.none)
    (below : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) :
    ∀ s o, FSem den (Term.atom t₁) (P₁ ++ [(Term.atom a, v)]) s o → FSem den (Term.atom "open") P₂ s o := by
  intro s o hs
  rw [fsem_snoc below] at hs
  by_cases e : a = s
  · subst e; exact (fsem_none fresh o).mpr (Or.inl rfl)
  · rw [ite_eq_right e] at hs; exact h s o hs

/-- A key of both fields, the first allowing less. -/
theorem snoc_both {t₁ t₂ : String} {P₁ P₂ : List (Term × Term)} {a : String} {v₁ v₂ : Term}
    (h : ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o) (sub : ∀ o, FieldSem den v₁ o → FieldSem den v₂ o)
    (b₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) (b₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) :
    ∀ s o, FSem den (Term.atom t₁) (P₁ ++ [(Term.atom a, v₁)]) s o → FSem den (Term.atom t₂) (P₂ ++ [(Term.atom a, v₂)]) s o := by
  intro s o hs
  rw [fsem_snoc b₁] at hs
  rw [fsem_snoc b₂]
  by_cases e : a = s
  · rw [ite_eq_left e] at hs ⊢; exact sub o hs
  · rw [ite_eq_right e] at hs ⊢; exact h s o hs

theorem eqv_snoc {P₁ P₂ : List (Term × Term)} {a : String} {v₁ v₂ : Term} {s : String}
    (b₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) (b₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt)
    (h : a ≠ s → EqvK den P₁ P₂ s) (same : a = s → ∀ o, FieldSem den v₁ o ↔ FieldSem den v₂ o) :
    EqvK den (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) s := by
  intro tag o
  rw [fsem_snoc b₁, fsem_snoc b₂]
  by_cases e : a = s
  · rw [ite_eq_left e, ite_eq_left e]; exact same e o
  · rw [ite_eq_right e, ite_eq_right e]; exact h e tag o

theorem lookup_snoc_ne {P : List (Term × Term)} {a c : String} {v : Term} (ne : a ≠ c)
    (below : ∀ e ∈ P, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) :
    mapLookup (P ++ [(Term.atom a, v)]) (Term.atom c) = mapLookup P (Term.atom c) := by
  rw [lookup_snoc below, ite_eq_right ne]

/-- `opt_map_union_strategy/5` walks the fields of two map literals, keeping what its status says. -/
theorem mwalk (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") :
    ∀ N (r₁ r₂ P₁ P₂ : List (Term × Term)) (st : Term), r₁.length + r₂.length ≤ N →
      FieldsV E (P₁ ++ r₁) → FieldsV E (P₂ ++ r₂) → (∀ x ∈ P₁ ++ P₂, ∀ y ∈ r₁ ++ r₂, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt) →
      MInv E den t₁ t₂ st P₁ P₂ →
      ∃ res, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm r₁) (fieldsTerm r₂) (.atom t₁)
        (Term.atom t₂) st = .ok res ∧ MRes E den t₁ t₂ res (P₁ ++ r₁) (P₂ ++ r₂) := by
  intro N
  induction N with
  | zero =>
    intro r₁ r₂ P₁ P₂ st size _ _ _ inv
    have : r₁ = [] ∧ r₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    simpa using mres_end (D m) t₁ t₂ g₁ g₂ inv
  | succ N ih =>
    intro r₁ r₂ P₁ P₂ st size s₁ s₂ below inv
    have fresh₁ : ∀ e ∈ r₁, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    have fresh₂ : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    match r₁, r₂ with
    | [], [] => simpa using mres_end (D m) t₁ t₂ g₁ g₂ inv
    | x :: xs, [] => exact mres_tail₁ ef hm t₁ t₂ g₁ g₂ x xs inv fresh₁
    | [], y :: ys => exact mres_tail₂ ef hm t₁ t₂ g₁ g₂ y ys inv fresh₂
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (s₁.1 (k₁, v₁) (by simp)).1
      obtain ⟨b, rfl⟩ := (s₂.1 (k₂, v₂) (by simp)).1
      have hv₁ : FieldValue E v₁ := (s₁.1 (.atom a, v₁) (by simp)).2
      have hv₂ : FieldValue E v₂ := (s₂.1 (.atom b, v₂) (by simp)).2
      have sx := fieldsV_head (fieldsV_suffix s₁)
      have sy := fieldsV_head (fieldsV_suffix s₂)
      have a₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt := fun e me =>
        below e (by simp [me]) (.atom a, v₁) (by simp)
      have a₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt := fun e me =>
        below e (by simp [me]) (.atom a, v₁) (by simp)
      have b₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt := fun e me =>
        below e (by simp [me]) (.atom b, v₂) (by simp)
      have b₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt := fun e me =>
        below e (by simp [me]) (.atom b, v₂) (by simp)
      simp only [List.length_cons] at size
      have none₀ : MRes E den t₁ t₂ (Term.atom "none") (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) :=
        Or.inr (Or.inr (Or.inr rfl))
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · -- a key only in the first literal
        have above : ∀ y ∈ (Term.atom b, v₂) :: ys, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp
          · exact cmp_lt_trans cmp (sy y my)
        have recur : ∀ st', MInv E den t₁ t₂ st' (P₁ ++ [(Term.atom a, v₁)]) P₂ → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs)
              (fieldsTerm ((.atom b, v₂) :: ys)) (.atom t₁) (.atom t₂) st' = .ok res ∧
            MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) := by
          intro st' inv'
          obtain ⟨res, run, mr⟩ := ih xs _ (P₁ ++ [(Term.atom a, v₁)]) P₂ st' (by simp; omega) (by simpa using s₁) s₂
            (fun x mx y my => by
              simp only [List.mem_append, List.mem_singleton] at mx
              rcases mx with (mx | rfl) | mx
              · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with h | h <;> simp [h])
              · simp only [List.mem_append] at my
                rcases my with my | my
                · exact sx y my
                · exact above y my
              · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with h | h <;> simp [h])) inv'
          exact ⟨res, run, by simpa using mr⟩
        rcases g₂ with rfl | rfl
        · rcases inv with ⟨rfl, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
          · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
              (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ => snoc_left (eqv_sub h fun _ => rfl) (lookup_below a₂) a₁⟩)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2»] at run ⊢
            exact run
          · obtain ⟨bs, runb, sound⟩ := field_sub_bool ef hm hp₁ hp₂
            cases bs
            · refine ⟨_, ?_, none₀⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2», runb,
                boolAtom, isMember]
            · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
                (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ => snoc_left (one_key_sub l₁ l₂ eqv (sound rfl) fun _ => rfl)
                  (lookup_below a₂) a₁⟩)))
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2», runb,
                boolAtom, isMember] at run ⊢
              exact run
          · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
              (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ => snoc_left (h fun _ => rfl) (lookup_below a₂) a₁⟩)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2»] at run ⊢
            exact run
          all_goals
            refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2»]
        · refine ⟨_, ?_, none₀⟩
          rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2»]
      · -- a key of both literals
        have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
        have notGt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isGT = Bool.true := by simp
        have recur : ∀ st', MInv E den t₁ t₂ st' (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs) (fieldsTerm ys) (.atom t₁)
              (.atom t₂) st' = .ok res ∧
            MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
          intro st' inv'
          obtain ⟨res, run, mr⟩ := ih xs ys (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) st' (by omega)
            (by simpa using s₁) (by simpa using s₂)
            (fun x mx y my => by
              simp only [List.mem_append, List.mem_singleton] at mx
              have my' : y ∈ (Term.atom a, v₁) :: xs ++ (Term.atom a, v₂) :: ys := by
                rcases List.mem_append.mp my with h | h <;> simp [h]
              have ka : ∀ y ∈ xs ++ ys, Term.compare (Term.fuel (Term.atom a) y.1) (Term.atom a) y.1 = .lt := fun y my => by
                rcases List.mem_append.mp my with h | h
                · exact sx y h
                · exact sy y h
              rcases mx with (mx | rfl) | (mx | rfl)
              · exact below x (by simp [mx]) y my'
              · exact ka y my
              · exact below x (by simp [mx]) y my'
              · exact ka y my) inv'
          exact ⟨res, run, by simpa using mr⟩
        have left_of : ∀ (h : (t₁ = "open" → t₂ = "open") → ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o),
            (∀ o, FieldSem den v₁ o → FieldSem den v₂ o) →
            MInv E den t₁ t₂ (Term.atom "left_subtype_of_right") (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) :=
          fun h sub => Or.inr (Or.inr (Or.inl ⟨rfl, fun pre => snoc_both (h pre) sub a₁ a₂⟩))
        have right_of : ∀ (h : (t₂ = "open" → t₁ = "open") → ∀ s o, FSem den (.atom t₂) P₂ s o → FSem den (.atom t₁) P₁ s o),
            (∀ o, FieldSem den v₂ o → FieldSem den v₁ o) →
            MInv E den t₁ t₂ (Term.atom "right_subtype_of_left") (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) :=
          fun h sub => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun pre => snoc_both (h pre) sub a₂ a₁⟩)))
        by_cases same : compareExact (fuel v₂ v₁) v₂ v₁ = .eq
        · have sv := fieldSem_exact ef hv₁ hv₂ same
          have inv' : MInv E den t₁ t₂ st (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) := by
            rcases inv with ⟨rfl, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
            · exact Or.inl ⟨rfl, fun s => eqv_snoc a₁ a₂ (fun _ => h s) fun _ => sv⟩
            · have ca : a ≠ c := by
                rintro rfl
                obtain ⟨x, mx, -⟩ := lookup_mem l₁
                have := lookup_below a₁
                rw [this] at l₁; cases l₁
              refine Or.inr (Or.inl ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, by rw [lookup_snoc_ne ca a₁]; exact l₁,
                by rw [lookup_snoc_ne ca a₂]; exact l₂, fun s sc => eqv_snoc a₁ a₂ (fun _ => eqv s sc) fun _ => sv⟩)
            · exact Or.inr (Or.inr (Or.inl ⟨rfl, fun pre => snoc_both (h pre) (fun o => (sv o).mp) a₁ a₂⟩))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun pre => snoc_both (h pre) (fun o => (sv o).mpr) a₂ a₁⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
          obtain ⟨res, run, mr⟩ := recur st inv'
          refine ⟨res, ?_, mr⟩
          rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
            Erlang.erlang.«=:=/2», same] at run ⊢
          exact run
        · obtain ⟨b₁₂, run₁₂, sound₁₂⟩ := field_sub_bool ef hm hv₁ hv₂
          obtain ⟨b₂₁, run₂₁, sound₂₁⟩ := field_sub_bool ef hm hv₂ hv₁
          -- the walk once subtyping decides the status
          have bySub : ∀ (h₁ : (t₁ = "open" → t₂ = "open") → ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o)
              (h₂ : (t₂ = "open" → t₁ = "open") → ∀ s o, FSem den (.atom t₂) P₂ s o → FSem den (.atom t₁) P₁ s o),
              ∃ res, (if b₁₂ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs)
                  (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "left_subtype_of_right")
                else if b₂₁ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs)
                  (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "right_subtype_of_left")
                else .ok (.atom "none")) = .ok res ∧
              MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
            intro h₁ h₂
            cases b₁₂
            · cases b₂₁
              · exact ⟨_, rfl, none₀⟩
              · simpa using recur _ (right_of h₂ (sound₂₁ rfl))
            · simpa using recur _ (left_of h₁ (sound₁₂ rfl))
          rcases inv with ⟨rfl, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
          · by_cases cond : a ≠ "__struct__" ∧ t₁ = t₂
            · obtain ⟨ns, rfl⟩ := cond
              obtain ⟨res, run, mr⟩ := recur (.tuple #[.atom "one_key_difference", .atom a, v₁, v₂])
                (Or.inr (Or.inl ⟨a, v₁, v₂, rfl, rfl, hv₁, hv₂, by rw [lookup_snoc a₁, ite_eq_left rfl],
                  by rw [lookup_snoc a₂, ite_eq_left rfl],
                  fun s sa => eqv_snoc a₁ a₂ (fun _ => h s) fun e => absurd e.symm sa⟩))
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                Erlang.erlang.«/=/2», Erlang.erlang.«=:=/2», same, Erlang.erlang.«==/2», Lynx.Except.andAlso,
                ns] at run ⊢
              exact run
            · obtain ⟨res, run, mr⟩ := bySub (fun pre => eqv_sub h pre) (fun pre => eqv_sub (fun s => (h s).symm) pre)
              refine ⟨res, ?_, mr⟩
              rw [← run, Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              have cond' : (Term.compare (Term.fuel (.atom a) (.atom "__struct__")) (.atom a) (.atom "__struct__") = .eq) ∨ t₁ ≠ t₂ := by
                by_cases e : a = "__struct__"
                · left; subst e; exact compare_self _
                · right; intro ht; exact cond ⟨e, ht⟩
              rcases cond' with c' | c'
              · simp [fieldsTerm, Term.list, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                  Erlang.erlang.«/=/2», Erlang.erlang.«=:=/2», same, Lynx.Except.andAlso, c',
                  run₁₂, run₂₁, boolAtom]
                cases b₁₂ <;> cases b₂₁ <;> simp
              · simp [fieldsTerm, Term.list, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                  Erlang.erlang.«/=/2», Erlang.erlang.«=:=/2», same, Erlang.erlang.«==/2», Lynx.Except.andAlso, c',
                  run₁₂, run₂₁, boolAtom]
                by_cases e : a = "__struct__" <;> cases b₁₂ <;> cases b₂₁ <;> simp [e]
          · obtain ⟨c₁₂, rc₁₂, sc₁₂⟩ := field_sub_bool ef hm hp₁ hp₂
            obtain ⟨c₂₁, rc₂₁, sc₂₁⟩ := field_sub_bool ef hm hp₂ hp₁
            have go : ∃ res, (if c₁₂ && b₁₂ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m)
                  (fieldsTerm xs) (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "left_subtype_of_right")
                else if c₂₁ && b₂₁ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs)
                  (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "right_subtype_of_left")
                else .ok (.atom "none")) = .ok res ∧
                MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
              by_cases l : c₁₂ && b₁₂
              · simp only [Bool.and_eq_true] at l
                obtain ⟨e₁, e₂⟩ := l
                subst e₁ e₂
                simpa using recur _ (left_of (fun pre => one_key_sub l₁ l₂ eqv (sc₁₂ rfl) pre) (sound₁₂ rfl))
              · by_cases r : c₂₁ && b₂₁
                · simp only [Bool.and_eq_true] at r
                  obtain ⟨e₁, e₂⟩ := r
                  subst e₁ e₂
                  simpa [l] using recur _
                    (right_of (fun pre => one_key_sub l₂ l₁ (fun s ne => (eqv s ne).symm) (sc₂₁ rfl) pre) (sound₂₁ rfl))
                · exact ⟨_, by simp [l, r], none₀⟩
            obtain ⟨res, run, mr⟩ := go
            refine ⟨res, ?_, mr⟩
            rw [← run, Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«/=/2», Erlang.erlang.«=:=/2», same, Lynx.Except.andAlso,
              run₁₂, run₂₁, rc₁₂, rc₂₁, boolAtom]
            cases c₁₂ <;> cases b₁₂ <;> cases c₂₁ <;> cases b₂₁ <;> simp
          · have go : ∃ res, (if b₁₂ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m)
                  (fieldsTerm xs) (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "left_subtype_of_right")
                else .ok (.atom "none")) = .ok res ∧
                MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
              cases b₁₂
              · exact ⟨_, rfl, none₀⟩
              · simpa using recur _ (left_of h (sound₁₂ rfl))
            obtain ⟨res, run, mr⟩ := go
            refine ⟨res, ?_, mr⟩
            rw [← run, Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«=:=/2», same,
              run₁₂, boolAtom, isMember]
            cases b₁₂ <;> simp
          · have go : ∃ res, (if b₂₁ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m)
                  (fieldsTerm xs) (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "right_subtype_of_left")
                else .ok (.atom "none")) = .ok res ∧
                MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
              cases b₂₁
              · exact ⟨_, rfl, none₀⟩
              · simpa using recur _ (right_of h (sound₂₁ rfl))
            obtain ⟨res, run, mr⟩ := go
            refine ⟨res, ?_, mr⟩
            rw [← run, Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«=:=/2», same,
              run₂₁, boolAtom, isMember]
            cases b₂₁ <;> simp
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«=:=/2», same]
      · -- a key only in the second literal
        have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ y ∈ (Term.atom a, v₁) :: xs, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp'
          · exact cmp_lt_trans cmp' (sx y my)
        have recur : ∀ st', MInv E den t₁ t₂ st' P₁ (P₂ ++ [(Term.atom b, v₂)]) → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm ((.atom a, v₁) :: xs))
              (fieldsTerm ys) (.atom t₁) (.atom t₂) st' = .ok res ∧
            MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) := by
          intro st' inv'
          obtain ⟨res, run, mr⟩ := ih _ ys P₁ (P₂ ++ [(Term.atom b, v₂)]) st' (by simp; omega) s₁ (by simpa using s₂)
            (fun x mx y my => by
              simp only [List.mem_append, List.mem_singleton] at mx
              rcases mx with mx | (mx | rfl)
              · exact below x (by simp [mx]) y (by
                  simp only [List.mem_append, List.mem_cons] at my; rcases my with (h | h) | h <;> simp [h])
              · exact below x (by simp [mx]) y (by
                  simp only [List.mem_append, List.mem_cons] at my; rcases my with (h | h) | h <;> simp [h])
              · simp only [List.mem_append] at my
                rcases my with my | my
                · exact above y my
                · exact sy y my) inv'
          exact ⟨res, run, by simpa using mr⟩
        rcases g₁ with rfl | rfl
        · rcases inv with ⟨rfl, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
          · obtain ⟨res, run, mr⟩ := recur (.atom "right_subtype_of_left")
              (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ =>
                snoc_left (eqv_sub (fun s => (h s).symm) fun _ => rfl) (lookup_below b₁) b₂⟩))))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2»] at run ⊢
            exact run
          · obtain ⟨bs, runb, sound⟩ := field_sub_bool ef hm hp₂ hp₁
            cases bs
            · refine ⟨_, ?_, none₀⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
                Erlang.erlang.«/=/2», runb, boolAtom, isMember]
            · obtain ⟨res, run, mr⟩ := recur (.atom "right_subtype_of_left")
                (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ =>
                  snoc_left (one_key_sub l₂ l₁ (fun s ne => (eqv s ne).symm) (sound rfl) fun _ => rfl)
                    (lookup_below b₁) b₂⟩))))
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
                Erlang.erlang.«/=/2», runb, boolAtom, isMember] at run ⊢
              exact run
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2»]
          · obtain ⟨res, run, mr⟩ := recur (.atom "right_subtype_of_left")
              (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ => snoc_left (h fun _ => rfl) (lookup_below b₁) b₂⟩))))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2»] at run ⊢
            exact run
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2»]
        · refine ⟨_, ?_, none₀⟩
          rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            Erlang.erlang.«/=/2»]


/-- Storing a key a map has keeps its size. -/
theorem store_len (a : String) {f : Term} (hf : FieldValue E f) :
    ∀ {l : List (Term × Term)}, FieldsV E l → (mapLookup l (.atom a)).isSome →
      ∃ l', Erlang.orddict.«store/3» (.atom a) f (fieldsTerm l) = .ok (fieldsTerm l') ∧ List.length l' = l.length
  | [], _, h => by simp [mapLookup] at h
  | (k, v) :: t, sl, h => by
    obtain ⟨b, rfl⟩ := (sl.1 _ List.mem_cons_self).1
    have hv := (sl.1 _ List.mem_cons_self).2
    have st := fieldsV_tail sl
    have hd := fieldsV_head sl
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · exfalso
      have ne : b ≠ a := fun e => by subst e; exact cmp_lt_ne cmp rfl
      rw [lookup_cons_atom, ite_eq_right ne, lookup_above fun e me => cmp_lt_trans cmp (hd e me)] at h
      simp at h
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      refine ⟨(.atom a, f) :: t, ?_, rfl⟩
      rw [Erlang.orddict.«store/3».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
    · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
      have ne : b ≠ a := fun e => by subst e; exact cmp_lt_ne cmp' rfl
      rw [lookup_cons_atom, ite_eq_right ne] at h
      obtain ⟨l', run, len⟩ := store_len a hf st h
      refine ⟨(.atom b, v) :: l', ?_, by simp [len]⟩
      rw [Erlang.orddict.«store/3».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
      simp [run]

/-- Optimized unions of element types are their unions. -/
def ElemFields (E : Term → Prop) (l : List (Term × Term)) : Prop := ∀ e ∈ l, ∃ (t : Term) (o : Bool), e.2 = .tuple #[t, boolAtom o] ∧ E t

theorem field_opt_union_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f₁ f₂ : Term} {t₁ t₂ : Term} {o₁ o₂ : Bool}
    (e₁ : f₁ = .tuple #[t₁, boolAtom o₁]) (e₂ : f₂ = .tuple #[t₂, boolAtom o₂]) (h₁ : E t₁) (h₂ : E t₂)
    (S : List (Term × Term)) :
    ∃ t, E t ∧ Elixir.Module.Types.Descr.«field_opt_union/3» (D m) f₁ f₂ (.map S) =
      .ok (.tuple #[t, boolAtom (o₁ || o₂)]) ∧
      ∀ o, FieldSem den (.tuple #[t, boolAtom (o₁ || o₂)]) o ↔ FieldSem den f₁ o ∨ FieldSem den f₂ o := by
  subst e₁ e₂
  obtain ⟨c, hc, run, sem⟩ := ef.opt_union S h₁ h₂ hm
  refine ⟨c, hc, ?_, fun o => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«field_opt_union/3», run]
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.orElse]
  · rw [fieldSem_mk, fieldSem_mk, fieldSem_mk]
    cases o with
    | none => cases o₁ <;> cases o₂ <;> simp
    | some x => simp [sem x]

/-- What `opt_map_union_strategy/5` finds for two literals of value maps, and what `opt_map_union/3` makes of it. -/
def StratM (E : Term → Prop) (den : Term → V → Prop) (m : Nat) (S : List (Term × Term)) (t₁ t₂ : String) (l₁ l₂ : List (Term × Term)) (st : Term) : Prop :=
  (∃ (key v₁ v₂ f : Term) (l : List (Term × Term)), st = .tuple #[.atom "one_key_difference", key, v₁, v₂] ∧
    Elixir.Module.Types.Descr.«field_opt_union/3» (D m) v₁ v₂ (.map S) = .ok f ∧
    Erlang.orddict.«store/3» key f (fieldsTerm l₁) = .ok (fieldsTerm l) ∧ FieldsV E l ∧ ElemFields E l ∧
    l.length = l₁.length ∧
    (∃ s, key = .atom s ∧ mapLookup l₁ (.atom s) ≠ none ∧ ∀ s', s ≠ s' → mapLookup l (.atom s') = mapLookup l₁ (.atom s')) ∧
    ∀ w, MSem den (.atom t₁) l w ↔ MSem den (.atom t₁) l₁ w ∨ MSem den (.atom t₂) l₂ w) ∨
  (st = .atom "left_subtype_of_right" ∧ ∀ w, MSem den (.atom t₁) l₁ w → MSem den (.atom t₂) l₂ w) ∨
  (st = .atom "right_subtype_of_left" ∧ ∀ w, MSem den (.atom t₂) l₂ w → MSem den (.atom t₁) l₁ w) ∨
  st = .atom "none"

theorem fieldsTerm_eq_nil {l : List (Term × Term)} : fieldsTerm l = .nil ↔ l = [] := by
  cases l
  · simp [fieldsTerm, Term.list]
  · simp [fieldsTerm, Term.list]

/-- `opt_map_union_strategy/5` on literals of value maps. -/
theorem strat_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₁ t₂ : String} (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {l₁ l₂ : List (Term × Term)} (s₁ : FieldsV E l₁) (s₂ : FieldsV E l₂)
    (e₁ : ElemFields E l₁) (e₂ : ElemFields E l₂) (S : List (Term × Term)) :
    ∃ st, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm l₁) (fieldsTerm l₂) (.atom t₁)
      (.atom t₂) (.atom "all_equal") = .ok st ∧ StratM E den m S t₁ t₂ l₁ l₂ st := by
  obtain ⟨st, run, mres⟩ := mwalk ef hm t₁ t₂ g₁ g₂ _ l₁ l₂ [] [] (.atom "all_equal") (Nat.le_refl _)
    (by simpa using s₁) (by simpa using s₂) (by simp) (Or.inl ⟨rfl, fun s tag o => Iff.rfl⟩)
  simp only [List.nil_append] at mres
  refine ⟨st, by simpa using run, ?_⟩
  · rcases mres with ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, la₁, la₂, eqv⟩ | ⟨rfl, sub⟩ | ⟨rfl, sub⟩ | rfl
    · subst et
      obtain ⟨x₁, mx₁, ex₁⟩ := lookup_mem la₁
      obtain ⟨x₂, mx₂, ex₂⟩ := lookup_mem la₂
      obtain ⟨u₁, o₁, eu₁, hu₁⟩ := e₁ x₁ mx₁
      obtain ⟨u₂, o₂, eu₂, hu₂⟩ := e₂ x₂ mx₂
      rw [ex₁] at eu₁
      rw [ex₂] at eu₂
      obtain ⟨t, ht, runF, semF⟩ := field_opt_union_val ef (show K ≤ m by omega) eu₁ eu₂ hu₁ hu₂ S
      obtain ⟨l', runS, sl', mem, look⟩ := store_val a ⟨t, o₁ || o₂, rfl, ht⟩ s₁
      obtain ⟨l'', runS', len⟩ := store_len a ⟨t, o₁ || o₂, rfl, ht⟩ s₁ (by rw [la₁]; rfl)
      have ll : l' = l'' := by rw [runS] at runS'; exact fieldsTerm_inj (Except.ok.inj runS')
      subst ll
      refine Or.inl ⟨_, _, _, _, l', rfl, runF, runS, sl', fun e me => ?_, len,
        ⟨a, rfl, by rw [la₁]; simp, fun s' ne => by rw [look s', ite_eq_right ne]⟩, fun w => ?_⟩
      · rcases mem e me with rfl | me
        · exact ⟨t, _, rfl, ht⟩
        · exact e₁ e me
      · have fs : ∀ s o, FSem den (.atom t₁) l' s o ↔ if a = s then FieldSem den (.tuple #[t, boolAtom (o₁ || o₂)]) o
            else FSem den (.atom t₁) l₁ s o := by
          intro s o
          unfold FSem TagSem
          rw [look s]
          by_cases e : a = s <;> simp [e]
        have at₁ : ∀ o, FSem den (.atom t₁) l₁ a o ↔ FieldSem den p₁ o := fun o => by unfold FSem TagSem; rw [la₁]
        have at₂ : ∀ o, FSem den (.atom t₁) l₂ a o ↔ FieldSem den p₂ o := fun o => by unfold FSem TagSem; rw [la₂]
        constructor
        · intro h
          have ha := (fs a (w (.atom a))).mp (h a)
          rw [ite_eq_left rfl, semF] at ha
          rcases ha with ha | ha
          · left
            refine ⟨fun s => ?_, h.doms⟩
            by_cases e : a = s
            · subst e; exact (at₁ _).mpr ha
            · have := (fs s (w (.atom s))).mp (h s); rwa [ite_eq_right e] at this
          · right
            refine ⟨fun s => ?_, h.doms⟩
            by_cases e : a = s
            · subst e; exact (at₂ _).mpr ha
            · have := (fs s (w (.atom s))).mp (h s); rw [ite_eq_right e] at this
              exact (eqv s (Ne.symm e) t₁ (w (.atom s))).mp this
        · intro h
          refine ⟨fun s => ?_, fun k i => h.elim (fun h => h.doms k i) (fun h => h.doms k i)⟩
          rw [fs]
          by_cases e : a = s
          · subst e; rw [ite_eq_left rfl, semF]
            rcases h with h | h
            · exact Or.inl ((at₁ _).mp (h a))
            · exact Or.inr ((at₂ _).mp (h a))
          · rw [ite_eq_right e]
            rcases h with h | h
            · exact h s
            · exact (eqv s (Ne.symm e) t₁ (w (.atom s))).mpr (h s)
    · obtain ⟨v⟩ := ef.inhabited
      exact Or.inr (Or.inl ⟨rfl, fun w h₁ => msem_of_atoms v (fun s o => sub s o) h₁⟩)
    · obtain ⟨v⟩ := ef.inhabited
      exact Or.inr (Or.inr (Or.inl ⟨rfl, fun w h₂ => msem_of_atoms v (fun s o => sub s o) h₂⟩))
    · exact Or.inr (Or.inr (Or.inr rfl))

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Optimized unions of map types on value maps. -/

/-- Map literals of element types, other than the top literal, keyed as Descr keys them. -/
def MLit (E : Term → Prop) (t : Term) : Prop := MapLitV E t ∧ ¬IsTop t ∧ KeyOk t

/-- Map types of element types: the top literal or BDDs of other literals. -/
abbrev MField (E : Term → Prop) (x : Term) : Prop := OField (MLit E) x

noncomputable def denMF (E : Term → Prop) (den : Term → V → Prop) (x : Term) (w : MW V) : Bool := denO x (valM E den w)

theorem mlit_not : ∀ t, MLit E t → ¬IsTop t := fun _ h => h.2.1

theorem denMF_exact {x y : Term} (fx : MField E x) (fy : MField E y) (e : compareExact (fuel y x) y x = .eq) (w : MW V) :
    denMF E den y w = denMF E den x w :=
  denO_exact mlit_not fx fy e (valM_resp w)

theorem EF.mopsE (ef : EF nd E V den tl K) : ElemOk E K :=
  ⟨ef.term, fun ha hb => let ⟨c, hc, run, _, _⟩ := ef.inter ha hb; ⟨c, hc, run⟩,
    fun ha S => let ⟨b, run, _⟩ := ef.empty S ha; ⟨b, run⟩, ef.none, ef.pos⟩

theorem EF.mdopsE (ef : EF nd E V den tl K) : ElemDiff E K :=
  ⟨fun ha hb => let ⟨c, hc, run, _, _⟩ := ef.diff ha hb; ⟨c, hc, run⟩⟩

theorem fieldsV_elem {l : List (Term × Term)} (h : FieldsV E l) : ElemFields E l := fun e me => (h.1 e me).2

theorem denMF_bdd {x : Term} (wx : Bdd (MLit E) x) (w : (MW V)) : denMF E den x w = eval (valM E den w) x := denO_bdd mlit_not wx _

theorem denMF_top (k : Term) (w : (MW V)) : denMF E den (.tuple #[k, .atom "open", .nil]) w = Bool.true := denO_top k _

/-- Leaves of map types hold the maps of their literal. -/
theorem denMF_leaf (ef : EF nd E V den tl K) {k : Int} {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l) (g : TagV E tag)
    (w : (MW V)) : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w := by
  have lit : MapLitV E (.tuple #[.integer k, tag, fieldsTerm l]) := ⟨k, tag, l, rfl, g, sl⟩
  unfold denMF denO
  rw [eval_leaf, Bool.or_eq_true, valM_iff ef.mopsE ef.mdopsE ef.semR lit, nsem_lit]
  constructor
  · rintro (h | h)
    · unfold isOpenTop at h
      split at h
      · rename_i e
        simp only [Term.tuple.injEq] at e
        have e₁ := congrArg (fun a : Array Term => a[1]?) e
        have e₂ := congrArg (fun a : Array Term => a[2]?) e
        simp at e₁ e₂
        subst e₁
        rw [fieldsTerm_eq_nil.mp e₂]
        exact ⟨fun s => fsem_nil.mpr (Or.inl rfl), fun k i => Or.inl rfl⟩
      · cases h
    · exact h
  · exact Or.inr

theorem map_union_field {x y : Term} (hx : MField E x) (hy : MField E y) :
    ∃ r, Elixir.Module.Types.Descr.«map_union/2» x y = .ok r ∧ MField E r ∧
      (∀ ok : Term → Prop, OField ok x → OField ok y → OField ok r) ∧
      ∀ w, denMF E den r w = (denMF E den x w || denMF E den y w) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨_, by unfold Elixir.Module.Types.Descr.«map_union/2»; rfl, Or.inl ⟨k, rfl⟩, fun _ ox _ => ox,
      fun w => by simp [denMF_top]⟩
  rcases hy with ⟨k, rfl⟩ | wy
  · refine ⟨_, ?_, Or.inl ⟨k, rfl⟩, fun _ _ oy => oy, fun w => by simp [denMF_top]⟩
    unfold Elixir.Module.Types.Descr.«map_union/2»
    split
    · exact (not_top_of_ok wx mlit_not _ rfl).elim
    · rename_i e; simp at e; subst e; rfl
    · rename_i h; exact (h _ rfl).elim
  obtain ⟨r, hr, okr, semr⟩ := union_ok wx wy
  refine ⟨r, by rw [map_union_bdd (not_top_of_ok wx mlit_not) (not_top_of_ok wy mlit_not), hr],
    Or.inr (okr _ wx wy), fun ok ox oy => ?_, fun w => ?_⟩
  · rcases ox with ⟨k, rfl⟩ | ox
    · exact absurd rfl (not_top_of_ok wx mlit_not (.integer k))
    rcases oy with ⟨k, rfl⟩ | oy
    · exact absurd rfl (not_top_of_ok wy mlit_not (.integer k))
    exact Or.inr (okr _ ox oy)
  rw [denMF_bdd (okr _ wx wy), denMF_bdd wx, denMF_bdd wy, semr _ (valM_resp w)]

/-- Leaves of map types are literals, the top one included. -/
theorem leafE {a b c : Term} (h : MField E (.tuple #[a, b, c])) :
    ∃ (k : Int) (l : List (Term × Term)), a = .integer k ∧ c = fieldsTerm l ∧
      TagV E b ∧ FieldsV E l ∧ KeyOk (.tuple #[a, b, c]) := by
  rcases h with ⟨k, e⟩ | w
  · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
    refine ⟨k, [], rfl, rfl, Or.inl rfl, ⟨by simp, by simp⟩, fun k' tag' l' e' => ?_⟩
    obtain ⟨-, e₂, e₃⟩ := tuple3_eq e'
    simp only [Term.atom.injEq] at e₂
    subst e₂
    exact ⟨fun h => by simp at h, fun _ ne => absurd (list_eq_nil.mp e₃.symm) ne⟩
  · rcases w.shape with e | e | ⟨k, x, y, e⟩ | ⟨_, _, _, _, _, e⟩
    · simp at e
    · simp at e
    · rw [e] at w
      obtain ⟨⟨k', tag, l, e', g, sl⟩, -, key⟩ := Bdd.leaf_iff.mp w
      obtain ⟨e₁, e₂, e₃⟩ := tuple3_eq (e.trans e')
      subst e₂
      exact ⟨k', l, e₁, e₃, g, sl, e ▸ key⟩
    · simp at e

theorem leaf_field {k : Int} {tag : Term} {l : List (Term × Term)} (g : TagV E tag)
    (sl : FieldsV E l) (key : KeyOk (.tuple #[.integer k, tag, fieldsTerm l])) :
    MField E (.tuple #[.integer k, tag, fieldsTerm l]) := by
  by_cases top : tag = .atom "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    exact Or.inl ⟨k, rfl⟩
  · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨k, tag, l, rfl, g, sl⟩, fun ⟨k', e⟩ => top ?_, key⟩)
    obtain ⟨-, e₁, e₂⟩ := tuple3_eq e
    exact ⟨e₁, fieldsTerm_eq_nil.mp e₂⟩

theorem leaf_not_top {k : Int} {t : Term} {l : List (Term × Term)} (n : ¬(t = .atom "open" ∧ l = [])) {a : Term} :
    Term.tuple #[.integer k, t, fieldsTerm l] ≠ .tuple #[a, .atom "open", .nil] := by
  intro e
  simp only [Term.tuple.injEq] at e
  have e₁ := congrArg (fun a : Array Term => a[1]?) e
  have e₂ := congrArg (fun a : Array Term => a[2]?) e
  simp at e₁ e₂
  exact n ⟨e₁, fieldsTerm_eq_nil.mp e₂⟩

theorem tuple3_eq {a b c a' b' c' : Term} (h : Term.tuple #[a, b, c] = .tuple #[a', b', c']) :
    a = a' ∧ b = b' ∧ c = c' := by
  simp only [Term.tuple.injEq] at h
  have e₀ := congrArg (fun x : Array Term => x[0]?) h
  have e₁ := congrArg (fun x : Array Term => x[1]?) h
  have e₂ := congrArg (fun x : Array Term => x[2]?) h
  simp at e₀ e₁ e₂
  exact ⟨e₀, e₁, e₂⟩

/-- Tags of which one has domains are not both atoms. -/
theorem atoms_guard {t₁ t₂ : Term} (g₁ : TagV E t₁) (g₂ : TagV E t₂) (h : ¬∃ s₁ s₂ : String, t₁ = .atom s₁ ∧ t₂ = .atom s₂) :
    Lynx.Except.andAlso (Erlang.erlang.«is_atom/1» t₁) (Erlang.erlang.«is_atom/1» t₂) = .ok (.atom "false") := by
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, -⟩ <;> rcases g₂ with rfl | rfl | ⟨dl₂, rfl, -⟩ <;>
    first
      | exact absurd ⟨_, _, rfl, rfl⟩ h
      | (cases dl₁ <;> simp [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, fieldsTerm, Term.list] <;> done)
      | (cases dl₂ <;> simp [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, fieldsTerm, Term.list] <;> done)
      | (cases dl₁ <;> cases dl₂ <;> simp [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, fieldsTerm, Term.list])

/-- Literal predicates that hold of a literal storing a field into another at one of its atom keys, when they hold of
the other. -/
def MergeOk (E : Term → Prop) (ok : Term → Prop) : Prop :=
  ∀ (k₁ k : Int) (tag : Term) (l₁ l : List (Term × Term)) (s : String),
    ok (.tuple #[.integer k₁, tag, fieldsTerm l₁]) → mapLookup l₁ (.atom s) ≠ none →
    (∀ s', s ≠ s' → mapLookup l (.atom s') = mapLookup l₁ (.atom s')) →
    MLit E (.tuple #[.integer k, tag, fieldsTerm l]) → ok (.tuple #[.integer k, tag, fieldsTerm l])

/-- Optimized unions of map types hold the maps of either, with literals of either or literals merging one into
the other at one key. -/
theorem opt_map_union_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {x y : Term} (hx : MField E x) (hy : MField E y)
    (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_map_union/3» (D m) x y (.map S) = .ok r ∧ MField E r ∧
      (∀ ok : Term → Prop, MergeOk E ok → OField ok x → OField ok y → OField ok r) ∧
      ∀ w, denMF E den r w = (denMF E den x w || denMF E den y w) := by
  obtain ⟨r₀, run₀, f₀, k₀, sem₀⟩ := map_union_field hx hy
  by_cases leaves : (∃ a b c, x = .tuple #[a, b, c]) ∧ (∃ a b c, y = .tuple #[a, b, c])
  · obtain ⟨⟨a₁, b₁, c₁, rfl⟩, ⟨a₂, b₂, c₂, rfl⟩⟩ := leaves
    obtain ⟨k₁, l₁, rfl, rfl, g₁, s₁, el₁⟩ := leafE hx
    obtain ⟨k₂, l₂, rfl, rfl, g₂, s₂, el₂⟩ := leafE hy
    by_cases n₁ : b₁ = .atom "open" ∧ l₁ = []
    · obtain ⟨rfl, rfl⟩ := n₁
      refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_map_union/3»; rfl, hx, fun _ _ ox _ => ox, fun w => ?_⟩
      have top := denMF_top (E := E) (den := den) (.integer k₁) w
      simp only [fieldsTerm, Term.list, List.map] at top ⊢
      rw [top]; rfl
    by_cases n₂ : b₂ = .atom "open" ∧ l₂ = []
    · obtain ⟨rfl, rfl⟩ := n₂
      refine ⟨_, ?_, hy, fun _ _ _ oy => oy, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · simp_all
        · rename_i h; exact (h (.integer k₂) (by simp [fieldsTerm, Term.list])).elim
      · have top := denMF_top (E := E) (den := den) (.integer k₂) w
        simp only [fieldsTerm, Term.list, List.map] at top ⊢
        rw [top]; simp
    have w₁ : Bdd (MLit E) (.tuple #[.integer k₁, b₁, fieldsTerm l₁]) :=
      hx.resolve_left fun ⟨k, e⟩ => leaf_not_top n₁ e
    have w₂ : Bdd (MLit E) (.tuple #[.integer k₂, b₂, fieldsTerm l₂]) :=
      hy.resolve_left fun ⟨k, e⟩ => leaf_not_top n₂ e
    by_cases same : compareExact (fuel (.tuple #[.integer k₂, b₂, fieldsTerm l₂]) (.tuple #[.integer k₁, b₁, fieldsTerm l₁])) (.tuple #[.integer k₂, b₂, fieldsTerm l₂]) (.tuple #[.integer k₁, b₁, fieldsTerm l₁]) = .eq
    · refine ⟨_, ?_, hx, fun _ _ ox _ => ox, fun w => by rw [denMF_exact hx hy same, Bool.or_self]⟩
      unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      split
      · rename_i heq; exact (leaf_not_top n₁ heq).elim
      · rename_i heq _; exact (leaf_not_top n₂ heq).elim
      simp only [leaf_guard]
      rw [ite_eq_left (by simpa using same)]
      rfl
    rcases opt_bdd_seen_map S (.atom "map_union") (.tuple #[.integer k₁, b₁, fieldsTerm l₁])
      (.tuple #[.integer k₂, b₂, fieldsTerm l₂]) with seen | ⟨S', ok⟩
    · refine ⟨r₀, ?_, f₀, fun ok _ => k₀ ok, sem₀⟩
      unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      split
      · rename_i heq; exact (leaf_not_top n₁ heq).elim
      · rename_i heq _; exact (leaf_not_top n₂ heq).elim
      simp only [leaf_guard]
      rw [ite_eq_right (by simpa using same)]
      simp [seen, run₀]
    have d₁ := fun w => denMF_leaf ef (k := k₁) s₁ g₁ w
    have d₂ := fun w => denMF_leaf ef (k := k₂) s₂ g₂ w
    -- leaves with domains are unioned as BDDs
    by_cases atoms : ¬∃ t₁ t₂ : String, b₁ = .atom t₁ ∧ b₂ = .atom t₂
    · refine ⟨r₀, ?_, f₀, fun ok _ => k₀ ok, sem₀⟩
      rw [← run₀, map_union_bdd (not_top_of_ok w₁ mlit_not) (not_top_of_ok w₂ mlit_not)]
      unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      split
      · rename_i heq; exact (leaf_not_top n₁ heq).elim
      · rename_i heq _; exact (leaf_not_top n₂ heq).elim
      simp only [leaf_guard]
      rw [ite_eq_right (by simpa using same)]
      simp [ok, atoms_guard g₁ g₂ atoms]
    obtain ⟨t₁, t₂, rfl, rfl⟩ := Classical.not_not.mp atoms
    replace g₁ := g₁.of_atom
    replace g₂ := g₂.of_atom
    obtain ⟨st, run, strat⟩ := strat_val ef hm g₁ g₂ s₁ s₂ (fieldsV_elem s₁) (fieldsV_elem s₂) S'
    rcases strat with ⟨key, v₁, v₂, f, l, rfl, rf, rs, sl, el, sem⟩ | ⟨rfl, sub⟩ | ⟨rfl, sub⟩ | rfl
    · obtain ⟨len, ⟨s, rfl, ls, look⟩, sem⟩ := sem
      obtain ⟨k, hk, key⟩ := leaf_new_key t₁ g₁ (l.map fun e => .tuple #[e.1, e.2])
      have nt : ¬(Term.atom t₁ = .atom "open" ∧ l = []) := by
        rintro ⟨-, rfl⟩
        cases l₁ with
        | nil => simp [mapLookup] at ls
        | cons _ _ => simp at len
      refine ⟨.tuple #[.integer k, .atom t₁, fieldsTerm l], ?_, leaf_field (TagV.atom g₁) sl key,
        fun ok mok ox _ => ?_, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · rename_i heq _; exact (leaf_not_top n₂ heq).elim
        simp only [leaf_guard]
        rw [ite_eq_right (by simpa using same)]
        have hk' : Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom t₁) (fieldsTerm l) =
            .ok (.tuple #[.integer k, .atom t₁, fieldsTerm l]) := hk
        simp [ok, run, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, rf, rs, hk']
      · have ml : MLit E (.tuple #[.integer k, .atom t₁, fieldsTerm l]) :=
          ⟨⟨k, .atom t₁, l, rfl, TagV.atom g₁, sl⟩, fun ⟨_, e⟩ => leaf_not_top nt e, key⟩
        rcases ox with ⟨k', e⟩ | ox
        · exact absurd e (leaf_not_top n₁)
        exact Or.inr (Bdd.leaf_iff.mpr (mok k₁ k (.atom t₁) l₁ l s (Bdd.leaf_iff.mp ox) ls look ml))
      · apply Bool.eq_iff_iff.mpr
        rw [Bool.or_eq_true, denMF_leaf ef sl (TagV.atom g₁) w, d₁, d₂]
        exact sem w
    · refine ⟨_, ?_, hy, fun _ _ _ oy => oy, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · rename_i heq _; exact (leaf_not_top n₂ heq).elim
        simp only [leaf_guard]
        rw [ite_eq_right (by simpa using same)]
        simp [ok, run, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso]
      · apply Bool.eq_iff_iff.mpr
        rw [Bool.or_eq_true, d₁, d₂]
        exact ⟨Or.inr, fun h => h.elim (sub w) id⟩
    · refine ⟨_, ?_, hx, fun _ _ ox _ => ox, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · rename_i heq _; exact (leaf_not_top n₂ heq).elim
        simp only [leaf_guard]
        rw [ite_eq_right (by simpa using same)]
        simp [ok, run, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso]
      · apply Bool.eq_iff_iff.mpr
        rw [Bool.or_eq_true, d₁, d₂]
        exact ⟨Or.inl, fun h => h.elim id (sub w)⟩
    · obtain ⟨r, hr, okr, semr⟩ := union_ok w₁ w₂
      refine ⟨r, ?_, Or.inr (okr _ w₁ w₂), fun ok _ ox oy => ?_, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · rename_i heq _; exact (leaf_not_top n₂ heq).elim
        simp only [leaf_guard]
        rw [ite_eq_right (by simpa using same)]
        simp [ok, run, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, hr]
      · rcases ox with ⟨k', e⟩ | ox
        · exact absurd e (leaf_not_top n₁)
        rcases oy with ⟨k', e⟩ | oy
        · exact absurd e (leaf_not_top n₂)
        exact Or.inr (okr _ ox oy)
      · rw [denMF_bdd (okr _ w₁ w₂), denMF_bdd w₁, denMF_bdd w₂, semr _ (valM_resp w)]
  · refine ⟨r₀, ?_, f₀, fun ok _ => k₀ ok, sem₀⟩
    rw [opt_map_union_fallback _ _ _ _ (by
      by_cases h : ∃ a b c, x = .tuple #[a, b, c]
      · exact Or.inr fun a b c e => leaves ⟨h, a, b, c, e⟩
      · exact Or.inl fun a b c e => h ⟨a, b, c, e⟩)]
    exact run₀

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized intersections of map types of element types. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Element types decide their emptiness exactly from an empty seen set. -/
theorem EF.msemZ (ef : EF nd E V den tl K) : ElemSem E K V den (fun S => S = []) where
  term := ef.den_term
  inter := ef.semR.inter
  diff := ef.semR.diff
  empty := fun {a S m b} ha hS hm run => by
    subst hS
    obtain ⟨b', run', h⟩ := ef.empty [] ha
    rw [run' _ hm] at run
    have : b' = b := by cases b <;> cases b' <;> simp_all [boolAtom]
    subst this
    exact h (lh a + 1) (Nat.lt_succ_self _) (safeN_nil _)
  inhabited := ef.inhabited
  resp := ef.semR.resp

theorem opt_ifun (ef : EF nd E V den tl K) (S : List (Term × Term)) : IFun E den (K + 1) (optMapIFun (.map S)) := by
  intro m hm a b ha hb
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  obtain ⟨c, hc, run, sem⟩ := ef.opt_inter S ha hb hn
  refine ⟨c, hc, sem, ?_⟩
  rw [optMapIFun, Erlang.program.«Elixir.Module.Types.Descr:-opt_map_leaf_intersection/3-fun-0-/2».pure]
  simpa [Elixir.Module.Types.Descr.«-opt_map_leaf_intersection/3-fun-0-/3»] using run

/-- `map_closed_subtype_of_open?/2` returns a Boolean, and `true` only when the closed fields allow less than the
open ones. -/
theorem cso_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
    FieldsV E l₁ → FieldsV E l₂ → ∃ c : Bool,
      Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2» (D m) (fieldsTerm l₁) (fieldsTerm l₂) =
        .ok (boolAtom c) ∧ (c = Bool.true → ∀ s o, FSem den (.atom "closed") l₁ s o → FSem den (.atom "open") l₂ s o) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size _ _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    refine ⟨Bool.true, ?_, fun _ s o _ => fsem_nil.mpr (Or.inl rfl)⟩
    rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
    simp [fieldsTerm, Term.list, boolAtom]
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₂ with
    | [] =>
      refine ⟨Bool.true, ?_, fun _ s o _ => fsem_nil.mpr (Or.inl rfl)⟩
      rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
      cases l₁ <;> simp [fieldsTerm, Term.list, boolAtom]
    | (k₂, f₂) :: t₂ =>
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨u₂, o₂, rfl, hu₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have s₂ := fieldsV_tail h₂
      have hd₂ := fieldsV_head h₂
      simp only [List.length_cons] at size
      -- the key of the open literal missing from the closed one
      have missing : ∀ (l : List (Term × Term)), (∀ e ∈ l, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt) → FieldsV E l →
          l.length + t₂.length ≤ N →
          (Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2» (D m) (fieldsTerm l) (fieldsTerm t₂) =
            Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2» (D m) (fieldsTerm l)
              (fieldsTerm ((.atom b, .tuple #[u₂, boolAtom o₂]) :: t₂)) →
            True) →
          ∃ c : Bool, Lynx.Except.andAlso (pure (boolAtom o₂))
              (Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2» (D m) (fieldsTerm l) (fieldsTerm t₂))
              Bool.true = .ok (boolAtom c) ∧
            (c = Bool.true → ∀ s o, FSem den (.atom "closed") l s o →
              FSem den (.atom "open") ((.atom b, .tuple #[u₂, boolAtom o₂]) :: t₂) s o) := by
        intro l above sl sz _
        obtain ⟨c, run, sound⟩ := ih l t₂ sz sl s₂
        refine ⟨o₂ && c, ?_, fun e s o h => ?_⟩
        · cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, run]
        · simp only [Bool.and_eq_true] at e
          obtain ⟨rfl, ec⟩ := e
          by_cases bs : b = s
          · subst bs
            rw [fsem_cons_self, fieldSem_mk]
            rw [fsem_none (lookup_above above)] at h
            rcases h with h | h
            · exact absurd h (by decide)
            · exact Or.inl ⟨h, rfl⟩
          · rw [fsem_cons_ne bs]
            exact sound ec s o h
      rcases l₁ with _ | ⟨⟨k₁, f₁⟩, t₁⟩
      · obtain ⟨c, run, sound⟩ := missing [] (by simp) ⟨by simp, by simp⟩ (by simp; omega) (fun _ => trivial)
        refine ⟨c, ?_, sound⟩
        rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
        simpa [fieldsTerm, Term.list] using run
      · simp only [List.length_cons] at size
        obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
        obtain ⟨u₁, o₁, rfl, hu₁⟩ := (h₁.1 _ List.mem_cons_self).2
        have s₁ := fieldsV_tail h₁
        have hd₁ := fieldsV_head h₁
        rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
        · obtain ⟨c, run, sound⟩ := ih t₁ _ (by simp; omega) s₁ h₂
          refine ⟨c, ?_, fun e s o h => ?_⟩
          · rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp] at run ⊢
            exact run
          · by_cases as : a = s
            · subst as
              have above : ∀ y ∈ (Term.atom b, Term.tuple #[u₂, boolAtom o₂]) :: t₂, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
                intro y my
                rcases List.mem_cons.mp my with rfl | my
                · exact cmp
                · exact cmp_lt_trans cmp (hd₂ y my)
              exact (fsem_none (lookup_above above) o).mpr (Or.inl rfl)
            · rw [fsem_cons_ne as] at h
              exact sound e s o h
        · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
          subst ab
          obtain ⟨c₁, run₁, sound₁⟩ := field_sub_bool ef hm ⟨u₁, o₁, rfl, hu₁⟩ ⟨u₂, o₂, rfl, hu₂⟩
          obtain ⟨c, run, sound⟩ := ih t₁ t₂ (by omega) s₁ s₂
          refine ⟨c₁ && c, ?_, fun e s o h => ?_⟩
          · rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
            have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
            simp only [fieldsTerm, Term.list, List.map] at run ⊢
            cases c₁ <;> simp [Erlang.erlang.«</2», Erlang.erlang.«=:=/2», run₁, run]
          · simp only [Bool.and_eq_true] at e
            by_cases as : a = s
            · subst as
              rw [fsem_cons_self] at h ⊢
              exact sound₁ e.1 o h
            · rw [fsem_cons_ne as] at h ⊢
              exact sound e.2 s o h
        · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
          have above : ∀ y ∈ (Term.atom a, Term.tuple #[u₁, boolAtom o₁]) :: t₁, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
            intro y my
            rcases List.mem_cons.mp my with rfl | my
            · exact cmp'
            · exact cmp_lt_trans cmp' (hd₁ y my)
          obtain ⟨c, run, sound⟩ := missing _ above h₁ (by simp; omega) (fun _ => trivial)
          refine ⟨c, ?_, sound⟩
          rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
          have ne : ¬compareExact (fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .eq := by
            intro e
            have := (atom_compareExact_eq b (.atom a)).mp e
            simp at this
            subst this
            exact cmp_lt_ne cmp' rfl
          have ba : ¬b = a := fun h => by subst h; exact cmp_lt_ne cmp' rfl
          simp only [fieldsTerm, Term.list, List.map] at run ⊢
          simp [Erlang.erlang.«</2», Erlang.erlang.«=:=/2», cmp, ba]
          simpa using run

theorem inter_plainM {x y : Term} (wx : Bdd (MLit E) x) (wy : Bdd (MLit E) y) :
    ∃ r, Elixir.Module.Types.Descr.«map_intersection/2» x y = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := by
  obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
  refine ⟨r, by rw [map_intersection_bdd (not_top_of_ok wx mlit_not) (not_top_of_ok wy mlit_not), hr],
    Or.inr (okr _ wx wy), fun w => ?_⟩
  rw [denMF_bdd (okr _ wx wy), denMF_bdd wx, denMF_bdd wy, semr _ (valM_resp w)]

theorem mlit_leaf {k : Int} {a b : Term} (h : MLit E (.tuple #[.integer k, a, b])) :
    ∃ l : List (Term × Term), b = fieldsTerm l ∧ TagV E a ∧ FieldsV E l ∧ ¬(a = .atom "open" ∧ l = []) ∧
      (a = .atom "open" → 0 ≤ k) ∧ (a = .atom "closed" → k < 0) := by
  obtain ⟨⟨k', t, l, e, g, sl⟩, nt, key⟩ := h
  obtain ⟨e₀, e₁, e₂⟩ := tuple3_eq e
  simp only [Term.integer.injEq] at e₀
  subst e₀ e₁ e₂
  refine ⟨l, rfl, g, sl, fun ⟨o, n⟩ => nt ⟨_, by rw [o, n]; rfl⟩, fun o => ?_, fun c => ?_⟩
  · subst o
    have kk := key k "open" (l.map fun e => .tuple #[e.1, e.2]) rfl
    refine kk.2 rfl fun ne => nt ⟨.integer k, ?_⟩
    have : l = [] := by cases l <;> simp_all
    subst this; rfl
  · subst c
    exact (key k "closed" (l.map fun e => .tuple #[e.1, e.2]) rfl).1 rfl

/-- New map leaves get the keys Descr gives them, whatever their tag. -/
theorem leaf_new_keyM {tag : Term} (g : TagV E tag) (l : List Term) :
    ∃ k : Int, Elixir.Module.Types.Descr.«bdd_leaf_new/2» tag (Term.list l) =
      .ok (.tuple #[.integer k, tag, Term.list l]) ∧ KeyOk (.tuple #[.integer k, tag, Term.list l]) := by
  rcases g with rfl | rfl | ⟨dl, rfl, -⟩
  · exact leaf_new_key "open" (Or.inl rfl) l
  · exact leaf_new_key "closed" (Or.inr rfl) l
  · obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (fieldsTerm dl) (Term.list l))
    refine ⟨min (l.length : Int) 2147483647 * 134217728 + hash, ?_, fun k tag l' e => ?_⟩
    · have ne := fieldsTerm_ne_atom dl "closed"
      generalize fieldsTerm dl = T at ne hrun ⊢
      unfold Elixir.Module.Types.Descr.«bdd_leaf_new/2»
      split
      · exact absurd rfl ne
      · simp [hrun, leaf_key_val]
    · obtain ⟨-, e₂, -⟩ := tuple3_eq e
      exact absurd e₂ (fieldsTerm_ne_atom dl tag)

/-- The clause of `opt_map_intersection/3` for two leaves that are not all maps. -/
theorem opt_map_inter_leavesG {d : Dispatcher} {S : Term} {k₁ k₂ : Int} {t₁ t₂ : Term}
    {l₁ l₂ : List (Term × Term)} (n₁ : ¬(t₁ = .atom "open" ∧ l₁ = [])) (n₂ : ¬(t₂ = .atom "open" ∧ l₂ = []))
    (ne : compareExact (fuel (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) (.tuple #[.integer k₁, t₁, fieldsTerm l₁])) (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) (.tuple #[.integer k₁, t₁, fieldsTerm l₁]) ≠ .eq) :
    (Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "map_intersection") (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
        (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) = .ok (.atom "seen") →
      Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
        (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) S =
        Elixir.Module.Types.Descr.«map_intersection/2» (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
          (.tuple #[.integer k₂, t₂, fieldsTerm l₂])) ∧
    (∀ S', Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "map_intersection")
        (.tuple #[.integer k₁, t₁, fieldsTerm l₁]) (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) =
        .ok (.tuple #[.atom "ok", S']) →
      Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
        (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) S =
        Elixir.Module.Types.Descr.«opt_map_leaf_intersection/3» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
          (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) S') := by
  constructor <;> intros <;>
  · unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
    split
    · rename_i heq; exact (leaf_not_top n₁ heq).elim
    · rename_i heq _; exact (leaf_not_top n₂ heq).elim
    simp only [leaf_guard]
    rw [ite_eq_right (by simpa using ne)]
    simp_all

/-- Exactly equal map leaves intersect to the first. -/
theorem opt_map_inter_sameG {d : Dispatcher} {S : Term} {k₁ k₂ : Int} {t₁ t₂ : Term}
    {l₁ l₂ : List (Term × Term)} (n₁ : ¬(t₁ = .atom "open" ∧ l₁ = [])) (n₂ : ¬(t₂ = .atom "open" ∧ l₂ = []))
    (e : compareExact (fuel (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) (.tuple #[.integer k₁, t₁, fieldsTerm l₁])) (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) (.tuple #[.integer k₁, t₁, fieldsTerm l₁]) = .eq) :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
      (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) S = .ok (.tuple #[.integer k₁, t₁, fieldsTerm l₁]) := by
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
  split
  · rename_i heq; exact (leaf_not_top n₁ heq).elim
  · rename_i heq _; exact (leaf_not_top n₂ heq).elim
  simp only [leaf_guard]
  rw [ite_eq_left (by simpa using e)]
  rfl

theorem opt_map_inter_top_eqG {d : Dispatcher} {x S : Term} {k : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d x (.tuple #[k, .atom "open", .nil]) S = .ok x := by
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
  split
  · exact (hx _ rfl).elim
  · rfl
  all_goals rename_i h
  all_goals first | exact (h _ rfl).elim | (exfalso; simp_all)

theorem opt_map_inter_plain_eqG {d : Dispatcher} {x y S : Term} (tx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (ty : ∀ k, y ≠ .tuple #[k, .atom "open", .nil])
    (h3 : ∀ a b c a' b' c', x = .tuple #[a, b, c] → y = .tuple #[a', b', c'] → False)
    (h4 : ∀ k fo a b c u e, x = .tuple #[k, .atom "open", fo] → y = .tuple #[a, b, c, u, e] → False)
    (h5 : ∀ k fo a b c u e, y = .tuple #[k, .atom "open", fo] → x = .tuple #[a, b, c, u, e] → False) :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d x y S = Elixir.Module.Types.Descr.«map_intersection/2» x y := by
  have ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq := by
    rintro a b c rfl e
    obtain ⟨_, _, _, rfl, -⟩ := exact_tuple3 e
    exact h3 _ _ _ _ _ _ rfl rfl
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
  split
  · exact (tx _ rfl).elim
  · exact (ty _ rfl).elim
  · simp only [leaf_guard]
    split
    · rw [ite_eq_right (ne _ _ _ rfl)]
      split
      all_goals first
        | rfl
        | exact (h3 _ _ _ _ _ _ rfl rfl).elim
        | (exfalso; simp_all
           first
             | exact h4 _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
             | exact h5 _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl)
    · split
      all_goals first
        | rfl
        | exact (h3 _ _ _ _ _ _ rfl rfl).elim
        | exact (h4 _ _ _ _ _ _ _ rfl rfl).elim
        | exact (h5 _ _ _ _ _ _ _ rfl rfl).elim

theorem opt_map_inter_push_lG {d : Dispatcher} {S : Term} {k : Term} {fo : Term} (nt : fo ≠ .nil)
    {h lit c u e : Term} :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[k, .atom "open", fo]) (.tuple #[h, lit, c, u, e]) S =
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo])
        (.function false "Elixir.Module.Types.Descr" "map_closed_subtype_of_open?" 2 #[]) := by
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
  split
  all_goals first
    | rfl
    | (simp_all; done)
    | (simp only [leaf_guard, node_ne3, ite_false]
       first
         | rfl
         | (split <;> first | rfl | (simp_all; done)))

theorem opt_map_inter_push_rG {d : Dispatcher} {S : Term} {k : Term} {fo : Term} (nt : fo ≠ .nil)
    {h lit c u e : Term} :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo]) S =
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo])
        (.function false "Elixir.Module.Types.Descr" "map_closed_subtype_of_open?" 2 #[]) := by
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
  split
  all_goals first
    | rfl
    | (simp_all; done)
    | (simp only [leaf_guard, node_ne3, ite_false]
       first
         | rfl
         | (split <;> first | rfl | (simp_all; done)))

/-- Optimized intersections of map literals hold the maps of both. -/
theorem leaf_inter (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) {k₁ k₂ : Int} {a₁ b₁ a₂ b₂ : Term}
    (lx : MLit E (.tuple #[.integer k₁, a₁, b₁])) (ly : MLit E (.tuple #[.integer k₂, a₂, b₂]))
    (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) (.tuple #[.integer k₁, a₁, b₁])
        (.tuple #[.integer k₂, a₂, b₂]) (.map S) = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den (.tuple #[.integer k₁, a₁, b₁]) w &&
        denMF E den (.tuple #[.integer k₂, a₂, b₂]) w) := by
  obtain ⟨l₁, rfl, g₁, s₁, n₁, -, c₁⟩ := mlit_leaf lx
  obtain ⟨l₂, rfl, g₂, s₂, n₂, -, c₂⟩ := mlit_leaf ly
  by_cases same : compareExact (fuel (.tuple #[.integer k₂, a₂, fieldsTerm l₂]) (.tuple #[.integer k₁, a₁, fieldsTerm l₁])) (.tuple #[.integer k₂, a₂, fieldsTerm l₂]) (.tuple #[.integer k₁, a₁, fieldsTerm l₁]) = .eq
  · exact ⟨_, opt_map_inter_sameG n₁ n₂ same, Or.inr (Bdd.leaf_iff.mpr lx), fun w => by
      rw [denMF_exact (Or.inr (Bdd.leaf_iff.mpr lx)) (Or.inr (Bdd.leaf_iff.mpr ly)) same, Bool.and_self]⟩
  rcases opt_bdd_seen_map S (.atom "map_intersection") (.tuple #[.integer k₁, a₁, fieldsTerm l₁])
      (.tuple #[.integer k₂, a₂, fieldsTerm l₂]) with seen | ⟨S', ok⟩
  · obtain ⟨r, hr, fr, sr⟩ := inter_plainM (Bdd.leaf_iff.mpr lx) (Bdd.leaf_iff.mpr ly)
    exact ⟨r, by rw [(opt_map_inter_leavesG n₁ n₂ same).1 seen, hr], fr, sr⟩
  rw [(opt_map_inter_leavesG n₁ n₂ same).2 _ ok]
  rcases literal_val ef.mopsE ef.mdopsE ef.msemZ (Kf := K + 1) (show K + 1 + 1 ≤ m by omega) (by omega)
    (opt_ifun ef S') (S := []) rfl g₁ g₂ s₁ s₂ with ⟨tR, l, run, gR, sl, sem⟩ | ⟨disj, run⟩
  · obtain ⟨k, hk, key⟩ := leaf_new_keyM gR (l.map fun e => .tuple #[e.1, e.2])
    have hk' : Elixir.Module.Types.Descr.«bdd_leaf_new/2» tR (fieldsTerm l) =
        .ok (.tuple #[.integer k, tR, fieldsTerm l]) := hk
    refine ⟨.tuple #[.integer k, tR, fieldsTerm l], ?_, leaf_field gR sl key, fun v => ?_⟩
    · simp only [optMapIFun] at run
      simp [Elixir.Module.Types.Descr.«opt_map_leaf_intersection/3», run, hk']
    · apply Bool.eq_iff_iff.mpr
      rw [Bool.and_eq_true, denMF_leaf ef sl gR, denMF_leaf ef s₁ g₁, denMF_leaf ef s₂ g₂]
      exact sem v
  · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun v => ?_⟩
    · simp only [optMapIFun] at run
      simp [Elixir.Module.Types.Descr.«opt_map_leaf_intersection/3», run, Lynx.Except.tryWith,
        Lynx.Exception.classTerm, Lynx.Exception.reason]
    · rw [denMF_bdd Bdd.bot]
      symm
      apply Bool.eq_false_iff.mpr
      intro h
      rw [Bool.and_eq_true, denMF_leaf ef s₁ g₁, denMF_leaf ef s₂ g₂] at h
      exact disj v h

/-- Pushing an open map literal below closed literals keeps exactly the maps of both. -/
theorem push_open_map (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {H : Int} {lo : List (Term × Term)}
    (hL : MLit E (.tuple #[.integer H, .atom "open", fieldsTerm lo])) (hH : 0 ≤ H) {b : Term} (wb : Bdd (MLit E) b) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» (D m) b (.tuple #[.integer H, .atom "open", fieldsTerm lo])
        (.function false "Elixir.Module.Types.Descr" "map_closed_subtype_of_open?" 2 #[]) = .ok r ∧
      MField E r ∧ ∀ w, denMF E den r w =
        (denMF E den b w && denMF E den (.tuple #[.integer H, .atom "open", fieldsTerm lo]) w) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  have so : FieldsV E lo := by
    obtain ⟨⟨_, _, l', e, -, sl'⟩, -⟩ := hL
    obtain ⟨-, -, e₂⟩ := tuple3_eq e
    rwa [fieldsTerm_inj e₂]
  obtain ⟨r, run, okr, semr⟩ := open_leaf_ok (Val := fun ρ => ∃ w, ρ = valM E den w) (fun ρ ⟨w, e⟩ => e ▸ valM_resp w)
    (ok := MLit E) (d := D (n + 1)) hL
    (fun k cl h => by
      obtain ⟨l, -, -, -, -, -, kc⟩ := mlit_leaf h
      exact closed_lt_openM (kc rfl) hH cl _)
    (fun k cl h => by
      obtain ⟨⟨k', tag, l, e, -, sl⟩, -⟩ := h
      obtain ⟨-, e₁, e₂⟩ := tuple3_eq e
      subst e₂ e₁
      obtain ⟨c, runc, sound⟩ := cso_val ef (m := n) (by omega) _ l _ (Nat.le_refl _) sl so
      refine ⟨c, by
        rw [Erlang.program.«Elixir.Module.Types.Descr:map_closed_subtype_of_open?/2».pure (external := false)]
        exact runc, fun cc ρ ⟨w, hw⟩ hρ => ?_⟩
      subst hw
      have lit : MapLitV E (.tuple #[.integer k, .atom "closed", fieldsTerm l]) := MapLitV.atom (Or.inr rfl) sl
      have ns := nsem_lit.mp ((valM_iff ef.mopsE ef.mdopsE ef.semR lit).mp hρ)
      exact (valM_iff ef.mopsE ef.mdopsE ef.semR hL.1).mpr (nsem_lit.mpr ⟨fun s => sound cc s _ (ns s), fun k i => Or.inl rfl⟩))
    (MLit E) b wb (fun t h => h)
  have wr : Bdd (MLit E) r := okr (MLit E) (fun t h => h) hL
  refine ⟨r, run, Or.inr wr, fun w => ?_⟩
  rw [denMF_bdd wr, semr _ ⟨w, rfl⟩, denMF_bdd wb, denMF_bdd (Bdd.leaf_iff.mpr hL), eval_leaf]

/-- Optimized intersections of map types hold the maps of both. -/
theorem opt_map_inter_val (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) {x y : Term} (fx : MField E x)
    (fy : MField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»; rfl, fy,
      fun w => by rw [denMF_top]; rfl⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨x, opt_map_inter_top_eqG (not_top_of_ok wx mlit_not), Or.inr wx, fun w => by rw [denMF_top]; simp⟩
  have nx := not_top_of_ok wx mlit_not
  have ny := not_top_of_ok wy mlit_not
  have plain : Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) =
      Elixir.Module.Types.Descr.«map_intersection/2» x y →
      ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) = .ok r ∧ MField E r ∧
        ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := by
    intro e
    obtain ⟨r, hr, fr, sr⟩ := inter_plainM wx wy
    exact ⟨r, by rw [e, hr], fr, sr⟩
  have plainEq := fun h3 h4 h5 => plain (opt_map_inter_plain_eqG (d := D m) (S := .map S) nx ny h3 h4 h5)
  have xAtom : ∀ {s : String}, x = .atom s → ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) =
      .ok r ∧ MField E r ∧ ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ e _ => by cases e) (fun _ _ _ _ _ _ _ e _ => by cases e)
      (fun _ _ _ _ _ _ _ _ e => by cases e)
  have yAtom : ∀ {s : String}, y = .atom s → ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) =
      .ok r ∧ MField E r ∧ ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ _ e => by cases e) (fun _ _ _ _ _ _ _ _ e => by cases e)
      (fun _ _ _ _ _ _ _ e _ => by cases e)
  rcases wx.shape with ex | ex | ⟨k₁, a₁, b₁, rfl⟩ | ⟨h₁, lit₁, c₁, u₁, d₁, rfl⟩
  · exact xAtom ex
  · exact xAtom ex
  all_goals rcases wy.shape with ey | ey | ⟨k₂, a₂, b₂, rfl⟩ | ⟨h₂, lit₂, c₂, u₂, d₂, rfl⟩
  all_goals try exact yAtom ey
  -- two leaves
  · exact leaf_inter ef hm ((Bdd.leaf_iff).mp wx) ((Bdd.leaf_iff).mp wy) S
  -- a leaf and a node
  · have lx := (Bdd.leaf_iff).mp wx
    obtain ⟨l, rfl, g, sl, nl, op, -⟩ := mlit_leaf lx
    rcases g with rfl | rfl | ⟨dl, rfl, -⟩
    · have ne : l ≠ [] := fun e => nl ⟨rfl, e⟩
      obtain ⟨r, hr, fr, sr⟩ := push_open_map ef (show K + 1 ≤ m by omega) lx (op rfl) wy
      refine ⟨r, ?_, fr, fun v => by rw [sr v, Bool.and_comm]⟩
      rw [opt_map_inter_push_lG (fun e => ne (fieldsTerm_eq_nil.mp e))]
      exact hr
    all_goals
      exact plainEq (fun _ _ _ _ _ _ _ e => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp [fieldsTerm_ne_atom] at e)
        (fun _ _ _ _ _ _ _ _ e => by simp at e)
  -- a node and a leaf
  · have ly := (Bdd.leaf_iff).mp wy
    obtain ⟨l, rfl, g, sl, nl, op, -⟩ := mlit_leaf ly
    rcases g with rfl | rfl | ⟨dl, rfl, -⟩
    · have ne : l ≠ [] := fun e => nl ⟨rfl, e⟩
      obtain ⟨r, hr, fr, sr⟩ := push_open_map ef (show K + 1 ≤ m by omega) ly (op rfl) wx
      refine ⟨r, ?_, fr, sr⟩
      rw [opt_map_inter_push_rG (fun e => ne (fieldsTerm_eq_nil.mp e))]
      exact hr
    all_goals
      exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
        (fun _ _ _ _ _ _ _ e _ => by simp [fieldsTerm_ne_atom] at e)
  -- two nodes
  · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
      (fun _ _ _ _ _ _ _ e _ => by simp at e)

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized negations of map types of element types. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem msem_one {a : String} {f : Term} {w : MW V} : MSem den (.atom "open") [(.atom a, f)] w ↔ FieldSem den f (w (.atom a)) := by
  constructor
  · intro h; simpa [FSem, TagSem, lookup_cons_atom] using h a
  · intro h
    refine ⟨fun s => ?_, fun k i => Or.inl rfl⟩
    unfold FSem TagSem
    rw [lookup_cons_atom]
    by_cases e : a = s
    · subst e; simpa using h
    · simp [e, mapLookup]

theorem fieldsV_one {a : String} {f : Term} (hf : FieldValue E f) : FieldsV E [(.atom a, f)] :=
  ⟨fun e me => by simp at me; subst me; exact ⟨⟨a, rfl⟩, hf⟩, by simp⟩

theorem denMF_one (ef : EF nd E V den tl K) {H : Int} {a : String} {f : Term} (hf : FieldValue E f) (w : MW V) :
    denMF E den (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, f)]]) w = Bool.true ↔ FieldSem den f (w (.atom a)) := by
  rw [denMF_leaf ef (fieldsV_one hf) (Or.inl rfl), msem_one]

/-- Open maps of one field of an element type, with a key that is not negative. -/
theorem one_field (_ef : EF nd E V den tl K) {H : Int} {a : String} {c : Term} {o : Bool} (hH : 0 ≤ H) (hc : E c) :
    MField E (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, .tuple #[c, boolAtom o])]]) := by
  refine leaf_field (Or.inl rfl) (fieldsV_one ⟨c, o, rfl, hc⟩) fun k tag l e => ?_
  obtain ⟨e₁, e₂, -⟩ := tuple3_eq e
  simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
  subst e₁ e₂
  exact ⟨fun h => by simp at h, fun _ _ => hH⟩

/-- Element types decide their emptiness exactly. -/
theorem EF.empty1 (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {c : Term} (hc : E c) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«empty?/1» (D m) c = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∀ v, ¬den c v) := by
  obtain ⟨b, run, sem⟩ := ef.empty [] hc
  rcases ef.static hc with rfl | ⟨C, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩
  · refine ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«empty?/1», boolAtom], ?_⟩
    obtain ⟨v⟩ := ef.inhabited
    simp only [Bool.false_eq_true, false_iff]
    exact fun h => h v (ef.den_term v)
  · exact ⟨b, by simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm,
      sem (lh (.map C) + 1) (Nat.lt_succ_self _) (safeN_nil _)⟩
  · exact ⟨b, by simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm,
      sem (lh (.tuple #[.reference r₀, .map st₀, g₀]) + 1) (Nat.lt_succ_self _) (safeN_nil _)⟩

theorem fieldSem_compl {t c : Term} {o : Bool} (sem : ∀ v, den c v ↔ ¬den t v) (x : Option V) :
    FieldSem den (.tuple #[c, boolAtom (!o)]) x ↔ ¬FieldSem den (.tuple #[t, boolAtom o]) x := by
  rw [fieldSem_mk, fieldSem_mk]
  cases x with
  | none => cases o <;> simp
  | some y => simp [sem y]

/-- Optimized negations of map types. -/
theorem map_neg_valK (ef : EF nd E V den tl K) (k₀ : Int) {m : Nat} (hm : K + 1 ≤ m) {x : Term}
    (fx : MField E x) (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_map_difference/3» (D m) (.tuple #[.integer k₀, .atom "open", .nil]) x (.map S) = .ok w ∧
      (kept (.atom "map", w) = Bool.true → MField E w ∧ ∀ v, denMF E den w v = !denMF E den x v) ∧
      (kept (.atom "map", w) = Bool.false → ∀ v, denMF E den x v = Bool.true) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«opt_map_difference/3»; rfl,
      fun k => by simp [kept] at k, fun _ v => denMF_top (E := E) (den := den) _ v⟩
  have wE : Bdd (MLit E) x := wx
  -- plain negations
  have plain : ∀ (arr : Array Term), x = .tuple arr →
      (∀ k key f, x ≠ .tuple #[k, .atom "open", .cons (.tuple #[key, f]) .nil]) →
      ∃ w, Elixir.Module.Types.Descr.«opt_map_difference/3» (D m) (.tuple #[.integer k₀, .atom "open", .nil]) x (.map S) = .ok w ∧
        (kept (.atom "map", w) = Bool.true → MField E w ∧ ∀ v, denMF E den w v = !denMF E den x v) ∧
        (kept (.atom "map", w) = Bool.false → ∀ v, denMF E den x v = Bool.true) := by
    intro arr hx none
    obtain ⟨w, run, keep, sem, nl⟩ := neg_okN wx
    have ww := keep _ wx
    refine ⟨w, by rw [opt_neg_plainK k₀ (D m) _ arr hx (not_top_of_ok wE mlit_not) none, run], fun _ => ⟨Or.inr ww, fun v => by
        rw [denMF_bdd ww, denMF_bdd wE, sem _ (valM_resp v)]⟩, fun kw v => ?_⟩
    rw [denMF_bdd wE]
    exact neg_drop (sem _ (valM_resp v)) (drop_bdd ww kw _)
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k, fun _ v => by simp [denMF_bdd wE]⟩
    rcases opt_bdd_seen_map S (.atom "map_difference") (.tuple #[.integer k₀, .atom "open", .nil]) (.atom "bdd_top") with seen | ⟨S', ok⟩
    · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
      simp [seen, Elixir.Module.Types.Descr.«map_difference/2», Elixir.Module.Types.Descr.«bdd_difference/2»,
        Erlang.erlang.«=:=/2»]
    · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
      simp [ok]
      unfold Elixir.Module.Types.Descr.«bdd_difference/3»
      simp [Elixir.Module.Types.Descr.«bdd_difference/2», Erlang.erlang.«=:=/2»]
  · refine ⟨(.tuple #[.integer k₀, .atom "open", .nil]), ?_, fun _ => ⟨Or.inl ⟨_, rfl⟩, fun v => by simp [denMF_top, denMF_bdd wE]⟩,
      fun k => by simp [kept] at k⟩
    rcases opt_bdd_seen_map S (.atom "map_difference") (.tuple #[.integer k₀, .atom "open", .nil]) (.atom "bdd_bot") with seen | ⟨S', ok⟩
    · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
      simp [seen, Elixir.Module.Types.Descr.«map_difference/2», Elixir.Module.Types.Descr.«bdd_difference/2»,
        Erlang.erlang.«=:=/2»]
    · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
      simp [ok]
      unfold Elixir.Module.Types.Descr.«bdd_difference/3»
      simp [Elixir.Module.Types.Descr.«bdd_difference/2», Erlang.erlang.«=:=/2»]
  · obtain ⟨l, rfl, g, sl, nt, -, -⟩ := mlit_leaf (Bdd.leaf_iff.mp wx)
    by_cases one : ∃ key f, a = .atom "open" ∧ l = [(key, f)]
    · obtain ⟨key, f, rfl, rfl⟩ := one
      obtain ⟨a, ka⟩ := (sl.1 (key, f) (by simp)).1
      simp only at ka
      subst ka
      obtain ⟨t, o, eft, ht⟩ := (sl.1 (.atom a, f) (by simp)).2
      simp only at eft
      subst eft
      have fx := denMF_one ef (H := k) (a := a) (f := .tuple #[t, boolAtom o]) ⟨t, o, rfl, ht⟩
      rcases opt_bdd_seen_map S (.atom "map_difference") (.tuple #[.integer k₀, .atom "open", .nil])
        (.tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[t, boolAtom o])]]) with seen | ⟨S', ok⟩
      · obtain ⟨w, run, keep, sem, nl⟩ := neg_okN wx
        have ww := keep _ wx
        refine ⟨w, ?_, fun _ => ⟨Or.inr ww, fun v => by
          rw [denMF_bdd ww, denMF_bdd wE, sem _ (valM_resp v)]⟩, fun kw v => ?_⟩
        · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
          simp only [fieldsTerm, List.map, Term.list] at seen ⊢
          simp only [leaf_guard, cons_ne_top3, ite_false]
          simp [seen]
          exact (map_difference_neg (not_top_of_ok wE mlit_not) _ rfl).trans run
        · rw [denMF_bdd wE]
          exact neg_drop (sem _ (valM_resp v)) (drop_bdd ww kw _)
      · obtain ⟨c, hc, runc, semc'⟩ := ef.opt_diff S' ef.term ht (show K ≤ m by omega)
        have semc : ∀ v, den c v ↔ ¬den t v := fun v => by simp [semc' v, ef.den_term]
        have fd : Elixir.Module.Types.Descr.«field_opt_difference/3» (D m) (.tuple #[.atom "term", .atom "true"])
            (.tuple #[t, boolAtom o]) (.map S') = .ok (.tuple #[c, boolAtom (!o)]) := by
          simp only [Elixir.Module.Types.Descr.«field_opt_difference/3», runc]
          cases o <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
        have compl := fieldSem_compl (o := o) semc
        have leafCase : ∃ H : Int, 0 ≤ H ∧
            Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "open") (Term.list [.tuple #[.atom a, .tuple #[c, boolAtom (!o)]]]) =
              .ok (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, .tuple #[c, boolAtom (!o)])]]) :=
          leaf_one_open _ _
        obtain ⟨H, hH, leaf⟩ := leafCase
        have leafSem : ∀ v, denMF E den (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, .tuple #[c, boolAtom (!o)])]]) v =
            !denMF E den (.tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[t, boolAtom o])]]) v := by
          intro v
          apply Bool.eq_iff_iff.mpr
          rw [denMF_one ef (f := .tuple #[c, boolAtom (!o)]) ⟨c, !o, rfl, hc⟩, Bool.not_eq_true', ← Bool.not_eq_true, fx, compl]
        have leafNeg : MField E (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, .tuple #[c, boolAtom (!o)])]]) :=
          one_field ef hH hc
        simp only [fieldsTerm, List.map, Term.list] at ok leaf
        cases o
        · simp only [boolAtom, Bool.not_false, ite_true, Bool.false_eq_true, ite_false] at ok leaf fd
          refine ⟨_, ?_, fun _ => ⟨leafNeg, leafSem⟩, fun kw => by simp [kept] at kw⟩
          unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
          simp only [fieldsTerm, List.map, Term.list] at ok leaf ⊢
          simp only [leaf_guard, cons_ne_top3, ite_false]
          simp [ok, fd, Elixir.Module.Types.Descr.«field_empty?/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember, leaf]
        · obtain ⟨b, runb, semb⟩ := ef.empty1 (show K ≤ m by omega) hc
          simp only [boolAtom, Bool.not_true, ite_true, Bool.false_eq_true, ite_false] at ok leaf fd
          cases b
          · refine ⟨_, ?_, fun _ => ⟨leafNeg, leafSem⟩, fun kw => by simp [kept] at kw⟩
            unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
            simp only [fieldsTerm, List.map, Term.list] at ok leaf ⊢
            simp only [leaf_guard, cons_ne_top3, ite_false]
            simp [ok, fd, Elixir.Module.Types.Descr.«field_empty?/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember, leaf,
              runb]
          · refine ⟨.atom "bdd_bot", ?_, fun kw => by simp [kept] at kw, fun _ v => ?_⟩
            · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
              simp only [fieldsTerm, List.map, Term.list] at ok ⊢
              simp only [leaf_guard, cons_ne_top3, ite_false]
              simp [ok, fd, Elixir.Module.Types.Descr.«field_empty?/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember, runb]
            · rw [fx, fieldSem_mk]
              cases e : v (.atom a) with
              | none => exact Or.inl ⟨rfl, rfl⟩
              | some y =>
                refine Or.inr ⟨y, rfl, ?_⟩
                exact Classical.byContradiction fun h => (semb.mp rfl) y ((semc y).mpr h)
    · exact plain _ rfl fun k' key f e => one ⟨key, f, by
        simp only [Term.tuple.injEq] at e
        have e₁ := congrArg (fun a : Array Term => a[1]?) e
        have e₂ := congrArg (fun a : Array Term => a[2]?) e
        simp at e₁ e₂
        refine ⟨e₁, ?_⟩
        cases l with
        | nil => simp [fieldsTerm, Term.list] at e₂
        | cons x xs =>
          cases xs with
          | nil =>
            simp [fieldsTerm, Term.list] at e₂ ⊢
            obtain ⟨k₁, k₂⟩ := e₂
            exact Prod.ext k₁ k₂
          | cons y ys => simp [fieldsTerm, Term.list] at e₂⟩
  · exact plain _ rfl fun _ _ _ e => by simp at e

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Optimized differences of map literals: the strategy. -/

theorem field_disj_bool (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) :
    ∃ s : Bool, Elixir.Module.Types.Descr.«field_disjoint?/2» (D m) f₁ f₂ = .ok (boolAtom s) ∧
      (s = Bool.true → ∀ o, FieldSem den f₁ o → FieldSem den f₂ o → False) := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  obtain ⟨b, hb, sound⟩ := ef.disj ht₁ ht₂
  have run := hb m hm
  refine ⟨(!o₁ || !o₂) && b, ?_, fun e o f₁ f₂ => ?_⟩
  · rw [Elixir.Module.Types.Descr.«field_disjoint?/2».eq_def]
    cases o₁ <;> cases o₂ <;> cases b <;>
      simp [boolAtom, run, Erlang.erlang.«not/1»]
  · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at e
    obtain ⟨eo, eb⟩ := e
    subst eb
    rw [fieldSem_mk] at f₁ f₂
    rcases f₁ with ⟨rfl, rfl⟩ | ⟨x, rfl, hx⟩
    · rcases f₂ with ⟨-, rfl⟩ | ⟨x, h, -⟩
      · simp at eo
      · cases h
    · rcases f₂ with ⟨h, -⟩ | ⟨y, h, hy⟩
      · cases h
      · cases h
        exact sound rfl x hx hy

/-- What the status of the difference walk says about the walked fields. -/
def DInv (E : Term → Prop) (den : Term → V → Prop) (t₁ t₂ : String) (st : Term) (P₁ P₂ : List (Term × Term)) : Prop :=
  (st = .atom "all_equal" ∧ (t₁ = t₂ ∨ t₂ = "open") ∧ ∀ s, EqvK den P₁ P₂ s) ∨
  (∃ (a : String) (p₁ p₂ : Term), st = .tuple #[.atom "one_key_difference", .atom a, p₁, p₂] ∧ t₁ = t₂ ∧
    FieldValue E p₁ ∧ FieldValue E p₂ ∧ mapLookup P₁ (.atom a) = some p₁ ∧
    mapLookup P₂ (.atom a) = some p₂ ∧ ∀ s, s ≠ a → EqvK den P₁ P₂ s) ∨
  (st = .atom "left_subtype_of_right" ∧ (t₁ = t₂ ∨ t₂ = "open") ∧ ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o) ∨
  st = .atom "none"

/-- What the result of the difference walk says about the fields of two map literals. -/
def DRes (E : Term → Prop) (den : Term → V → Prop) (t₁ t₂ : String) (st : Term) (l₁ l₂ : List (Term × Term)) : Prop :=
  (st = .atom "disjoint" ∧ ∃ s, ∀ o, FSem den (.atom t₁) l₁ s o → FSem den (.atom t₂) l₂ s o → False) ∨
  (∃ (a : String) (p₁ p₂ : Term), st = .tuple #[.atom "one_key_difference", .atom a, p₁, p₂] ∧ t₁ = t₂ ∧
    FieldValue E p₁ ∧ FieldValue E p₂ ∧ mapLookup l₁ (.atom a) = some p₁ ∧
    mapLookup l₂ (.atom a) = some p₂ ∧ ∀ s, s ≠ a → EqvK den l₁ l₂ s) ∨
  (st = .atom "left_subtype_of_right" ∧ ∀ s o, FSem den (.atom t₁) l₁ s o → FSem den (.atom t₂) l₂ s o) ∨
  st = .atom "none"

theorem tags_mono {t₁ t₂ : String} (h : t₁ = t₂ ∨ t₂ = "open") :
    t₁ = "open" → t₂ = "open" := by
  intro e; rcases h with rfl | h
  · exact e
  · exact h

/-- The status after a key of the second literal only, which is optional, while the first is closed. -/
theorem missing_optional (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₂ : String} {st : Term} {P₁ P₂ : List (Term × Term)} {b : String}
    {v₂ : Term} (inv : DInv E den "closed" t₂ st P₁ P₂) (opt : FieldSem den v₂ Option.none)
    (b₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt) (b₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt) :
    ∃ st', Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1» (D m) st = .ok st' ∧
      DInv E den "closed" t₂ st' P₁ (P₂ ++ [(Term.atom b, v₂)]) := by
  have extend : (∀ s o, FSem den (.atom "closed") P₁ s o → FSem den (.atom t₂) P₂ s o) →
      ∀ s o, FSem den (Term.atom "closed") P₁ s o → FSem den (Term.atom t₂) (P₂ ++ [(Term.atom b, v₂)]) s o := by
    intro h s o hs
    rw [fsem_snoc b₂]
    by_cases e : b = s
    · subst e
      rw [ite_eq_left rfl]
      have := (fsem_none (lookup_below b₁) o).mp hs
      rcases this with h | rfl
      · exact absurd h (by decide)
      · exact opt
    · rw [ite_eq_right e]; exact h s o hs
  rcases inv with ⟨rfl, tags, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
  · exact ⟨_, by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl,
      Or.inr (Or.inr (Or.inl ⟨rfl, tags, extend (eqv_sub h (fun e => absurd e (by decide)))⟩))⟩
  · obtain ⟨bs, runb, sound⟩ := field_sub_bool ef hm hp₁ hp₂
    cases bs
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]
      simp [runb, boolAtom, isMember]
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl et, extend (one_key_sub l₁ l₂ eqv (sound rfl)
        (fun e => absurd e (by decide)))⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]
      simp [runb, boolAtom, isMember]
  · exact ⟨_, by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl,
      Or.inr (Or.inr (Or.inl ⟨rfl, tags, extend h⟩))⟩
  · exact ⟨_, by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl,
      Or.inr (Or.inr (Or.inr rfl))⟩

/-- Required fields: those that do not allow absence. -/
def req (v : Term) : Bool :=
  match v with
  | .tuple ⟨[_, .atom "false"]⟩ => Bool.true
  | _ => Bool.false

theorem req_true {v : Term} (h : FieldValue E v) (r : req v = Bool.true) : ¬FieldSem den v Option.none := by
  obtain ⟨t, o, rfl, -⟩ := h
  rw [fieldSem_mk]
  cases o <;> simp_all [req, boolAtom]

theorem req_false {v : Term} (h : FieldValue E v) (r : req v = Bool.false) : FieldSem den v Option.none := by
  obtain ⟨t, o, rfl, -⟩ := h
  rw [fieldSem_mk]
  cases o <;> simp_all [req, boolAtom]

theorem any_req (m : Nat) (name : String) (hname : name = "-opt_map_difference_strategy/5-fun-0-" ∨
      name = "-opt_map_difference_strategy/5-fun-1-") (l : List (Term × Term)) (hl : ∀ e ∈ l, FieldValue E e.2) :
    Erlang.lists.«any/2» (D m) (.function false "Elixir.Module.Types.Descr" name 1 #[]) (fieldsTerm l) =
      .ok (boolAtom (l.any fun e => req e.2)) := by
  have := any_list (D m) "Elixir.Module.Types.Descr" name #[]
    (fun x => match x with | .tuple ⟨[_, v]⟩ => req v | _ => Bool.false) (l.map fun e => .tuple #[e.1, e.2]) (by
      intro x mx
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      obtain ⟨t, o, ev, -⟩ := hl e me
      rcases hname with rfl | rfl
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_map_difference_strategy/5-fun-0-/1».pure, ev]
        cases o <;> simp [Elixir.Module.Types.Descr.«-opt_map_difference_strategy/5-fun-0-/1», Erlang.erlang.«not/1»,
          boolAtom, req]
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_map_difference_strategy/5-fun-1-/1».pure, ev]
        cases o <;> simp [Elixir.Module.Types.Descr.«-opt_map_difference_strategy/5-fun-1-/1», Erlang.erlang.«not/1»,
          boolAtom, req])
  simpa [fieldsTerm, List.any_map, Function.comp_def] using this

/-- A required field of the first literal at a key the closed second one lacks. -/
theorem disj_left {t₁ s : String} {l₁ l₂ : List (Term × Term)} {v : Term} (hl : mapLookup l₁ (.atom s) = some v)
    (hv : FieldValue E v) (r : req v = Bool.true) (hn : mapLookup l₂ (.atom s) = Option.none) :
    ∀ o, FSem den (.atom t₁) l₁ s o → FSem den (.atom "closed") l₂ s o → False := by
  intro o h₁ h₂
  rcases (fsem_none hn o).mp h₂ with h | rfl
  · exact absurd h (by decide)
  · exact req_true hv r (by simpa [FSem, TagSem, hl] using h₁)

/-- A required field of the second literal at a key the closed first one lacks. -/
theorem disj_right {t₂ s : String} {l₁ l₂ : List (Term × Term)} {v : Term} (hl : mapLookup l₂ (.atom s) = some v)
    (hv : FieldValue E v) (r : req v = Bool.true) (hn : mapLookup l₁ (.atom s) = Option.none) :
    ∀ o, FSem den (.atom "closed") l₁ s o → FSem den (.atom t₂) l₂ s o → False := by
  intro o h₁ h₂
  rcases (fsem_none hn o).mp h₁ with h | rfl
  · exact absurd h (by decide)
  · exact req_true hv r (by simpa [FSem, TagSem, hl] using h₂)

theorem dres_end (d : Dispatcher) (t₁ t₂ : String) (_g₁ : t₁ = "open" ∨ t₁ = "closed")
    {st : Term} {P₁ P₂ : List (Term × Term)} (inv : DInv E den t₁ t₂ st P₁ P₂) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» d (fieldsTerm []) (fieldsTerm []) (.atom t₁)
      (.atom t₂) st = .ok res ∧ DRes E den t₁ t₂ res P₁ P₂ := by
  rcases inv with ⟨rfl, tags, h⟩ | ⟨a, p₁, p₂, rfl, h⟩ | ⟨rfl, tags, h⟩ | rfl
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, eqv_sub h (tags_mono tags)⟩))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
  · refine ⟨_, ?_, Or.inr (Or.inl ⟨a, p₁, p₂, rfl, h⟩)⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]

/-- The walk ends on the second fields first. -/
theorem dres_tail₁ (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {st : Term} {P₁ P₂ : List (Term × Term)} (x : Term × Term)
    (xs : List (Term × Term)) (inv : DInv E den t₁ t₂ st P₁ P₂) (s₁ : FieldsV E (P₁ ++ x :: xs))
    (fresh : ∀ e ∈ x :: xs, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm (x :: xs)) (fieldsTerm [])
      (Term.atom t₁) (Term.atom t₂) st = .ok res ∧ DRes E den t₁ t₂ res (P₁ ++ x :: xs) (P₂ ++ []) := by
  obtain ⟨k, v⟩ := x
  have none : DRes E den t₁ t₂ (Term.atom "none") (P₁ ++ (k, v) :: xs) (P₂ ++ []) := Or.inr (Or.inr (Or.inr rfl))
  rcases g₂ with rfl | rfl
  · rcases inv with ⟨rfl, tags, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
        simpa using left_extend (eqv_sub h (fun _ => rfl)) fresh⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · obtain ⟨b, run, sound⟩ := field_sub_bool ef hm hp₁ hp₂
      cases b
      · refine ⟨_, ?_, none⟩
        rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso, run, boolAtom,
          isMember]
      · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
          simpa using left_extend (one_key_sub l₁ l₂ eqv (sound rfl) (fun _ => rfl)) fresh⟩))⟩
        rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso, run, boolAtom,
          isMember]
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by simpa using left_extend h fresh⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · have fv : ∀ e ∈ (k, v) :: xs, FieldValue E e.2 := fun e me => (s₁.1 e (by simp [me])).2
    have any₁ := any_req m "-opt_map_difference_strategy/5-fun-1-" (Or.inr rfl) _ fv
    simp only [fieldsTerm, Term.list, List.map] at any₁
    cases ar : ((k, v) :: xs).any (fun e => req e.2)
    · refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«/=/2», any₁, ar, boolAtom]
    · obtain ⟨e, me, re⟩ := List.any_eq_true.mp ar
      obtain ⟨s, es⟩ := (s₁.1 e (by simp [me])).1
      refine ⟨_, ?_, Or.inl ⟨rfl, s, fun o h₁ h₂ => disj_left (t₁ := t₁)
        (lookup_of_mem s₁ (by simp [me]) es) (fv e me) re (by simpa using fresh e me s es) o h₁ h₂⟩⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«/=/2», any₁, ar, boolAtom]

theorem lookup_some_mem {l : List (Term × Term)} {s : String} {f : Term} (h : mapLookup l (.atom s) = some f) :
    ∃ e ∈ l, e.1 = .atom s ∧ e.2 = f := by
  unfold mapLookup at h
  simp only [equalExact_eq_decide] at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e, List.mem_of_find?_eq_some he, (atom_compareExact_eq s e.1).mp (by simpa using List.find?_some he), rfl⟩

/-- Optional fields of the second literal beyond the first, which is closed, keep the first a subtype. -/
theorem right_extend {t₂ : String} {P₁ P₂ r₂ : List (Term × Term)}
    (h : ∀ s o, FSem den (.atom "closed") P₁ s o → FSem den (.atom t₂) P₂ s o)
    (fresh₁ : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none)
    (fresh₂ : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none)
    (opt : ∀ e ∈ r₂, FieldSem den e.2 Option.none) :
    ∀ s o, FSem den (Term.atom "closed") P₁ s o → FSem den (Term.atom t₂) (P₂ ++ r₂) s o := by
  intro s o hs
  cases e : mapLookup r₂ (.atom s) with
  | none => exact (fsem_append_notin e o).mpr (h s o hs)
  | some f =>
    obtain ⟨x, mx, kx, fx⟩ := lookup_some_mem e
    have n₁ := fresh₁ x mx s kx
    have n₂ := fresh₂ x mx s kx
    rcases (fsem_none n₁ o).mp hs with c | rfl
    · exact absurd c (by decide)
    · unfold FSem TagSem
      rw [lookup_append, n₂, e]
      simpa [← fx] using opt x mx

/-- The walk ends on the first fields first. -/
theorem dres_tail₂ (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {st : Term} {P₁ P₂ : List (Term × Term)} (y : Term × Term)
    (ys : List (Term × Term)) (inv : DInv E den t₁ t₂ st P₁ P₂) (s₂ : FieldsV E (P₂ ++ y :: ys))
    (fresh₁ : ∀ e ∈ y :: ys, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none)
    (fresh₂ : ∀ e ∈ y :: ys, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm []) (fieldsTerm (y :: ys))
      (Term.atom t₁) (Term.atom t₂) st = .ok res ∧ DRes E den t₁ t₂ res (P₁ ++ []) (P₂ ++ y :: ys) := by
  obtain ⟨k, v⟩ := y
  have none : DRes E den t₁ t₂ (Term.atom "none") (P₁ ++ []) (P₂ ++ (k, v) :: ys) := Or.inr (Or.inr (Or.inr rfl))
  have fv : ∀ e ∈ (k, v) :: ys, FieldValue E e.2 := fun e me => (s₂.1 e (by simp [me])).2
  have any₀ := any_req m "-opt_map_difference_strategy/5-fun-0-" (Or.inl rfl) _ fv
  simp only [fieldsTerm, Term.list, List.map] at any₀
  rcases g₁ with rfl | rfl
  · refine ⟨_, ?_, none⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
        Erlang.erlang.«/=/2»]
  cases ar : ((k, v) :: ys).any (fun e => req e.2)
  · have opt : ∀ e ∈ (k, v) :: ys, FieldSem den e.2 Option.none := fun e me =>
      req_false (fv e me) (by
        have := List.any_eq_false.mp ar e me
        simpa using this)
    have ext := fun h => right_extend (t₂ := t₂) h fresh₁ fresh₂ opt
    have run : ∀ st', Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1» (D m) st = .ok st' →
        Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm []) (fieldsTerm ((k, v) :: ys))
          (.atom "closed") (.atom t₂) st = .ok st' := by
      intro st' h
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«/=/2», any₀, ar, boolAtom, h]
    rcases inv with ⟨rfl, tags, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
    · exact ⟨_, run _ (by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl),
        Or.inr (Or.inr (Or.inl ⟨rfl, by simpa using ext (eqv_sub h (fun e => absurd e (by decide)))⟩))⟩
    · obtain ⟨b, runb, sound⟩ := field_sub_bool ef hm hp₁ hp₂
      cases b
      · exact ⟨_, run _ (by
          rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]
          simp [runb, boolAtom, isMember]), none⟩
      · exact ⟨_, run _ (by
          rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]
          simp [runb, boolAtom, isMember]),
          Or.inr (Or.inr (Or.inl ⟨rfl, by
            simpa using ext (one_key_sub l₁ l₂ eqv (sound rfl) (fun e => absurd e (by decide)))⟩))⟩
    · exact ⟨_, run _ (by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl),
        Or.inr (Or.inr (Or.inl ⟨rfl, by simpa using ext h⟩))⟩
    · exact ⟨_, run _ (by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl), none⟩
  · obtain ⟨e, me, re⟩ := List.any_eq_true.mp ar
    obtain ⟨s, es⟩ := (s₂.1 e (by simp [me])).1
    refine ⟨_, ?_, Or.inl ⟨rfl, s, fun o h₁ h₂ => disj_right (t₂ := t₂)
      (lookup_of_mem s₂ (by simp [me]) es) (fv e me) re (by simpa using fresh₁ e me s es) o h₁ h₂⟩⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
        Erlang.erlang.«/=/2», any₀, ar, boolAtom]

/-- `opt_map_difference_strategy/5` walks the fields of two map literals, keeping what its status says. -/
theorem dwalk (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") :
    ∀ N (r₁ r₂ P₁ P₂ : List (Term × Term)) (st : Term), r₁.length + r₂.length ≤ N →
      FieldsV E (P₁ ++ r₁) → FieldsV E (P₂ ++ r₂) → (∀ x ∈ P₁ ++ P₂, ∀ y ∈ r₁ ++ r₂, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt) →
      DInv E den t₁ t₂ st P₁ P₂ →
      ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm r₁) (fieldsTerm r₂) (.atom t₁)
        (Term.atom t₂) st = .ok res ∧ DRes E den t₁ t₂ res (P₁ ++ r₁) (P₂ ++ r₂) := by
  intro N
  induction N with
  | zero =>
    intro r₁ r₂ P₁ P₂ st size _ _ _ inv
    have : r₁ = [] ∧ r₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    simpa using dres_end (D m) t₁ t₂ g₁ inv
  | succ N ih =>
    intro r₁ r₂ P₁ P₂ st size s₁ s₂ below inv
    have fresh₁ : ∀ e ∈ r₁, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    have fresh₂ : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    have fresh₂' : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    match r₁, r₂ with
    | [], [] => simpa using dres_end (D m) t₁ t₂ g₁ inv
    | x :: xs, [] => exact dres_tail₁ ef hm t₁ t₂ g₁ g₂ x xs inv s₁ fresh₁
    | [], y :: ys => exact dres_tail₂ ef hm t₁ t₂ g₁ g₂ y ys inv s₂ fresh₂ fresh₂'
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (s₁.1 (k₁, v₁) (by simp)).1
      obtain ⟨b, rfl⟩ := (s₂.1 (k₂, v₂) (by simp)).1
      have hv₁ : FieldValue E v₁ := (s₁.1 (.atom a, v₁) (by simp)).2
      have hv₂ : FieldValue E v₂ := (s₂.1 (.atom b, v₂) (by simp)).2
      have sx := fieldsV_head (fieldsV_suffix s₁)
      have sy := fieldsV_head (fieldsV_suffix s₂)
      have a₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt := fun e me =>
        below e (by simp [me]) (.atom a, v₁) (by simp)
      have a₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt := fun e me =>
        below e (by simp [me]) (.atom a, v₁) (by simp)
      have b₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt := fun e me =>
        below e (by simp [me]) (.atom b, v₂) (by simp)
      have b₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt := fun e me =>
        below e (by simp [me]) (.atom b, v₂) (by simp)
      have la₁ : mapLookup (P₁ ++ (Term.atom a, v₁) :: xs) (Term.atom a) = some v₁ :=
        lookup_of_mem s₁ (e := (.atom a, v₁)) (by simp) rfl
      have lb₂ : mapLookup (P₂ ++ (Term.atom b, v₂) :: ys) (Term.atom b) = some v₂ :=
        lookup_of_mem s₂ (e := (.atom b, v₂)) (by simp) rfl
      simp only [List.length_cons] at size
      obtain ⟨u₁, o₁, ev₁, hu₁⟩ := id hv₁
      obtain ⟨u₂, o₂, ev₂, hu₂⟩ := id hv₂
      have none₀ : DRes E den t₁ t₂ (Term.atom "none") (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) :=
        Or.inr (Or.inr (Or.inr rfl))
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · -- a key only in the first literal
        have above : ∀ y ∈ (Term.atom b, v₂) :: ys, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp
          · exact cmp_lt_trans cmp (sy y my)
        have na₂ : mapLookup (P₂ ++ (Term.atom b, v₂) :: ys) (Term.atom a) = Option.none := by
          rw [lookup_append, lookup_below a₂]
          refine lookup_none fun y my eq => ?_
          have := above y my
          rw [eq, compare_self] at this
          cases this
        have recur : ∀ st', DInv E den t₁ t₂ st' (P₁ ++ [(Term.atom a, v₁)]) P₂ → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm xs)
              (fieldsTerm ((.atom b, v₂) :: ys)) (.atom t₁) (.atom t₂) st' = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) := by
          intro st' inv'
          obtain ⟨res, run, mr⟩ := ih xs _ (P₁ ++ [(Term.atom a, v₁)]) P₂ st' (by simp; omega) (by simpa using s₁) s₂
            (fun x mx y my => by
              simp only [List.mem_append, List.mem_singleton] at mx
              rcases mx with (mx | rfl) | mx
              · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with h | h <;> simp [h])
              · simp only [List.mem_append] at my
                rcases my with my | my
                · exact sx y my
                · exact above y my
              · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with h | h <;> simp [h])) inv'
          exact ⟨res, run, by simpa using mr⟩
        rcases g₂ with rfl | rfl
        · rcases inv with ⟨rfl, tags, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
          · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
              (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl,
                snoc_left (eqv_sub h fun _ => rfl) (lookup_below a₂) a₁⟩)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂] at run ⊢
            exact run
          · obtain ⟨bs, runb, sound⟩ := field_sub_bool ef hm hp₁ hp₂
            cases bs
            · refine ⟨_, ?_, none₀⟩
              rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«==/2», runb, ev₁, ev₂,
                boolAtom, isMember]
            · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
                (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl, snoc_left (one_key_sub l₁ l₂ eqv (sound rfl) fun _ => rfl)
                  (lookup_below a₂) a₁⟩)))
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«==/2», runb, ev₁, ev₂,
                boolAtom, isMember] at run ⊢
              exact run
          · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
              (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl, snoc_left h (lookup_below a₂) a₁⟩)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂] at run ⊢
            exact run
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂]
        · cases o₁
          · refine ⟨_, ?_, Or.inl ⟨rfl, a, disj_left la₁ hv₁ (by simp [ev₁, req, boolAtom]) na₂⟩⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂, boolAtom]
          · obtain ⟨res, run, mr⟩ := recur (.atom "none") (Or.inr (Or.inr (Or.inr rfl)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂, boolAtom] at run ⊢
            exact run
      · -- a key of both literals
        have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        have recur : ∀ st', DInv E den t₁ t₂ st' (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm xs) (fieldsTerm ys) (.atom t₁)
              (.atom t₂) st' = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
          intro st' inv'
          obtain ⟨res, run, mr⟩ := ih xs ys (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) st' (by omega)
            (by simpa using s₁) (by simpa using s₂)
            (fun x mx y my => by
              simp only [List.mem_append, List.mem_singleton] at mx
              have my' : y ∈ (Term.atom a, v₁) :: xs ++ (Term.atom a, v₂) :: ys := by
                rcases List.mem_append.mp my with h | h <;> simp [h]
              have ka : ∀ y ∈ xs ++ ys, Term.compare (Term.fuel (Term.atom a) y.1) (Term.atom a) y.1 = .lt := fun y my => by
                rcases List.mem_append.mp my with h | h
                · exact sx y h
                · exact sy y h
              rcases mx with (mx | rfl) | (mx | rfl)
              · exact below x (by simp [mx]) y my'
              · exact ka y my
              · exact below x (by simp [mx]) y my'
              · exact ka y my) inv'
          exact ⟨res, run, by simpa using mr⟩
        have noneR : ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm xs)
            (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "none") = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) :=
          recur _ (Or.inr (Or.inr (Or.inr rfl)))
        by_cases same : compareExact (fuel v₂ v₁) v₂ v₁ = .eq
        · have sv := fieldSem_exact ef hv₁ hv₂ same
          have inv' : DInv E den t₁ t₂ st (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) := by
            rcases inv with ⟨rfl, tags, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
            · exact Or.inl ⟨rfl, tags, fun s => eqv_snoc a₁ a₂ (fun _ => h s) fun _ => sv⟩
            · have ca : a ≠ c := by
                rintro rfl
                have := lookup_below a₁
                rw [this] at l₁; cases l₁
              refine Or.inr (Or.inl ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, by rw [lookup_snoc_ne ca a₁]; exact l₁,
                by rw [lookup_snoc_ne ca a₂]; exact l₂, fun s sc => eqv_snoc a₁ a₂ (fun _ => eqv s sc) fun _ => sv⟩)
            · exact Or.inr (Or.inr (Or.inl ⟨rfl, tags, snoc_both h (fun o => (sv o).mp) a₁ a₂⟩))
            · exact Or.inr (Or.inr (Or.inr rfl))
          obtain ⟨res, run, mr⟩ := recur st inv'
          refine ⟨res, ?_, mr⟩
          rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
            Erlang.erlang.«=:=/2», same] at run ⊢
          exact run
        obtain ⟨bd, rund, soundd⟩ := field_disj_bool ef hm hv₁ hv₂
        cases bd
        rotate_left
        · refine ⟨_, ?_, Or.inl ⟨rfl, a, fun o h₁ h₂ => soundd rfl o (by simpa [FSem, TagSem, la₁] using h₁)
            (by simpa [FSem, TagSem, lb₂] using h₂)⟩⟩
          rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
            Erlang.erlang.«=:=/2», same, rund,
            boolAtom, isMember]
        obtain ⟨b₁₂, run₁₂, sound₁₂⟩ := field_sub_bool ef hm hv₁ hv₂
        have lsrR : (∀ s o, FSem den (Term.atom t₁) (P₁ ++ [(Term.atom a, v₁)]) s o → FSem den (Term.atom t₂) (P₂ ++ [(Term.atom a, v₂)]) s o) →
            (t₁ = t₂ ∨ t₂ = "open") → ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m)
              (fieldsTerm xs) (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "left_subtype_of_right") = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) :=
          fun h tags => recur _ (Or.inr (Or.inr (Or.inl ⟨rfl, tags, h⟩)))
        rcases inv with ⟨rfl, tags, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
        · by_cases et : t₁ = t₂
          · subst et
            obtain ⟨res, run, mr⟩ := recur (.tuple #[.atom "one_key_difference", .atom a, v₁, v₂])
              (Or.inr (Or.inl ⟨a, v₁, v₂, rfl, rfl, hv₁, hv₂, by rw [lookup_snoc a₁, ite_eq_left rfl],
                by rw [lookup_snoc a₂, ite_eq_left rfl], fun s sa => eqv_snoc a₁ a₂ (fun _ => h s) fun e => absurd e.symm sa⟩))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«==/2», Erlang.erlang.«=:=/2», same, rund,
              boolAtom, isMember] at run ⊢
            exact run
          · cases b₁₂
            · obtain ⟨res, run, mr⟩ := noneR
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
                boolAtom, isMember, run₁₂, et] at run ⊢
              exact run
            · obtain ⟨res, run, mr⟩ := lsrR (snoc_both (eqv_sub h (tags_mono tags)) (sound₁₂ rfl) a₁ a₂) tags
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
                boolAtom, isMember, run₁₂, et] at run ⊢
              exact run
        · obtain ⟨c₁₂, rc₁₂, sc₁₂⟩ := field_sub_bool ef hm hp₁ hp₂
          by_cases both : c₁₂ = Bool.true ∧ b₁₂ = Bool.true
          · obtain ⟨rfl, rfl⟩ := both
            obtain ⟨res, run, mr⟩ := lsrR (snoc_both (one_key_sub l₁ l₂ eqv (sc₁₂ rfl) (tags_mono (Or.inl et)))
              (sound₁₂ rfl) a₁ a₂) (Or.inl et)
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
              boolAtom, isMember, run₁₂, rc₁₂] at run ⊢
            exact run
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            cases c₁₂ <;> cases b₁₂
            rotate_right
            · exact absurd ⟨rfl, rfl⟩ both
            all_goals
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
                boolAtom, isMember, rc₁₂, run₁₂]
        · cases b₁₂
          · obtain ⟨res, run, mr⟩ := noneR
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
              boolAtom, isMember, run₁₂] at run ⊢
            exact run
          · obtain ⟨res, run, mr⟩ := lsrR (snoc_both h (sound₁₂ rfl) a₁ a₂) tags
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
              boolAtom, isMember, run₁₂] at run ⊢
            exact run
        · obtain ⟨res, run, mr⟩ := noneR
          refine ⟨res, ?_, mr⟩
          rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
            Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
            boolAtom, isMember] at run ⊢
          exact run
      · -- a key only in the second literal
        have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ y ∈ (Term.atom a, v₁) :: xs, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp'
          · exact cmp_lt_trans cmp' (sx y my)
        have nb₁ : mapLookup (P₁ ++ (Term.atom a, v₁) :: xs) (Term.atom b) = Option.none := by
          rw [lookup_append, lookup_below b₁]
          refine lookup_none fun y my eq => ?_
          have := above y my
          rw [eq, compare_self] at this
          cases this
        have recur : ∀ st', DInv E den t₁ t₂ st' P₁ (P₂ ++ [(Term.atom b, v₂)]) → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm ((.atom a, v₁) :: xs))
              (fieldsTerm ys) (.atom t₁) (.atom t₂) st' = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) := by
          intro st' inv'
          obtain ⟨res, run, mr⟩ := ih _ ys P₁ (P₂ ++ [(Term.atom b, v₂)]) st' (by simp; omega) s₁ (by simpa using s₂)
            (fun x mx y my => by
              simp only [List.mem_append, List.mem_singleton] at mx
              rcases mx with mx | (mx | rfl)
              · exact below x (by simp [mx]) y (by
                  simp only [List.mem_append, List.mem_cons] at my; rcases my with (h | h) | h <;> simp [h])
              · exact below x (by simp [mx]) y (by
                  simp only [List.mem_append, List.mem_cons] at my; rcases my with (h | h) | h <;> simp [h])
              · simp only [List.mem_append] at my
                rcases my with my | my
                · exact above y my
                · exact sy y my) inv'
          exact ⟨res, run, by simpa using mr⟩
        rcases g₁ with rfl | rfl
        · obtain ⟨res, run, mr⟩ := recur (.atom "none") (Or.inr (Or.inr (Or.inr rfl)))
          refine ⟨res, ?_, mr⟩
          rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            Erlang.erlang.«/=/2», ev₁, ev₂] at run ⊢
          exact run
        · cases o₂
          · refine ⟨_, ?_, Or.inl ⟨rfl, b, disj_right lb₂ hv₂ (by simp [ev₂, req, boolAtom]) nb₁⟩⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2», Lynx.Except.andAlso, ev₁, ev₂, boolAtom]
          · obtain ⟨st', runm, inv'⟩ := missing_optional ef (v₂ := v₂) hm inv (by rw [ev₂, fieldSem_mk]; simp) b₁ b₂
            obtain ⟨res, run, mr⟩ := recur st' inv'
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2», Lynx.Except.andAlso, ev₁, ev₂, boolAtom, runm] at run ⊢
            exact run

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Differences of map types on value maps. -/

theorem denMF_botV (v : (MW V)) : denMF E den (.atom "bdd_bot") v = Bool.false := by
  rw [denMF_bdd (Bdd.bot (ok := MLit E))]; rfl

/-- Plain differences of map types hold the maps of the first and not the second. -/
theorem map_diff_val {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ w, Elixir.Module.Types.Descr.«map_difference/2» x y = .ok w ∧ MField E w ∧
      ∀ v, denMF E den w v = (denMF E den x v && !denMF E den y v) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl, Or.inr Bdd.bot,
      fun v => by rw [denMF_botV, denMF_top]; simp⟩
  have ny := not_top_of_ok wy mlit_not
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_difference/2»
        simp [diff_leaf_top]
      · rw [denMF_botV, denMF_bdd wy]; rfl
    · refine ⟨_, ?_, Or.inl ⟨kt, rfl⟩, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_difference/2»
        simp [diff_leaf_bot]
      · rw [denMF_bdd wy]; simp
    all_goals
      obtain ⟨w, run, keep, sem⟩ := neg_ok wy
      have ww := keep _ wy
      refine ⟨w, by rw [map_difference_neg ny _ rfl, run], Or.inr ww, fun v => ?_⟩
      rw [denMF_bdd ww, denMF_bdd wy, denMF_top, sem _ (valM_resp v)]
      simp
  · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
    have ww := keep _ wx wy
    refine ⟨w, by rw [map_difference_bdd (not_top_of_ok wx mlit_not) ny, run], Or.inr ww, fun v => ?_⟩
    rw [denMF_bdd ww, denMF_bdd wx, denMF_bdd wy, sem _ (valM_resp v)]

/-- `orddict:find/2` on sorted fields finds the field of a key. -/
theorem find_val (a : String) : ∀ {l : List (Term × Term)}, FieldsV E l →
    Erlang.orddict.«find/2» (.atom a) (fieldsTerm l) =
      match mapLookup l (.atom a) with
      | some f => .ok (.tuple #[.atom "ok", f])
      | none => .ok (.atom "error")
  | [], _ => by rw [Erlang.orddict.«find/2».eq_def]; simp [fieldsTerm, Term.list, mapLookup]
  | (k, v) :: t, sl => by
    obtain ⟨b, rfl⟩ := (sl.1 _ List.mem_cons_self).1
    have st := fieldsV_tail sl
    have hd := fieldsV_head sl
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have none : mapLookup t (.atom a) = Option.none := lookup_none fun e me eq => by
        have := cmp_lt_trans cmp (hd e me)
        rw [eq, compare_self] at this; cases this
      rw [Erlang.orddict.«find/2».eq_def, lookup_cons_atom, ite_eq_right ne, none]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      rw [Erlang.orddict.«find/2».eq_def, lookup_cons_atom, ite_eq_left rfl]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have ih := find_val a st
      rw [Erlang.orddict.«find/2».eq_def, lookup_cons_atom, ite_eq_right ne, ← ih]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]

theorem field_empty1_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {c : Term} (hc : E c) (o : Bool) :
    ∃ e : Bool, Elixir.Module.Types.Descr.«field_empty?/1» (D m) (.tuple #[c, boolAtom o]) = .ok (boolAtom e) ∧
      (e = Bool.true ↔ ∀ x, ¬FieldSem den (.tuple #[c, boolAtom o]) x) := by
  cases o
  · obtain ⟨b, run, sem⟩ := ef.empty1 hm hc
    refine ⟨b, by simpa [Elixir.Module.Types.Descr.«field_empty?/1», boolAtom] using run, ?_⟩
    rw [sem]
    constructor
    · intro h x hx
      rw [fieldSem_mk] at hx
      rcases hx with ⟨-, h'⟩ | ⟨y, -, hy⟩
      · cases h'
      · exact h y hy
    · intro h y hy
      exact h (some y) ((fieldSem_mk (opt := Bool.false)).mpr (Or.inr ⟨y, rfl, hy⟩))
  · refine ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«field_empty?/1», boolAtom], ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    exact fun h => h Option.none ((fieldSem_mk (opt := Bool.true)).mpr (Or.inl ⟨rfl, rfl⟩))

theorem field_opt_diff_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₁ t₂ : Term} {o₁ o₂ : Bool} (h₁ : E t₁) (h₂ : E t₂)
    (S : List (Term × Term)) :
    ∃ c, E c ∧ Elixir.Module.Types.Descr.«field_opt_difference/3» (D m) (.tuple #[t₁, boolAtom o₁])
        (.tuple #[t₂, boolAtom o₂]) (.map S) = .ok (.tuple #[c, boolAtom (o₁ && !o₂)]) ∧
      ∀ x, FieldSem den (.tuple #[c, boolAtom (o₁ && !o₂)]) x ↔
        FieldSem den (.tuple #[t₁, boolAtom o₁]) x ∧ ¬FieldSem den (.tuple #[t₂, boolAtom o₂]) x := by
  obtain ⟨c, hc, run, sem⟩ := ef.opt_diff S h₁ h₂ hm
  refine ⟨c, hc, ?_, fieldSem_diff sem⟩
  simp only [Elixir.Module.Types.Descr.«field_opt_difference/3», run]
  cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]

theorem field_opt_inter_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₁ t₂ : Term} {o₁ o₂ : Bool} (h₁ : E t₁) (h₂ : E t₂)
    (S : List (Term × Term)) :
    ∃ c, E c ∧ Elixir.Module.Types.Descr.«field_opt_intersection/3» (D m) (.tuple #[t₁, boolAtom o₁])
        (.tuple #[t₂, boolAtom o₂]) (.map S) = .ok (.tuple #[c, boolAtom (o₁ && o₂)]) ∧
      ∀ x, FieldSem den (.tuple #[c, boolAtom (o₁ && o₂)]) x ↔
        FieldSem den (.tuple #[t₁, boolAtom o₁]) x ∧ FieldSem den (.tuple #[t₂, boolAtom o₂]) x := by
  obtain ⟨c, hc, run, sem⟩ := ef.opt_inter S h₁ h₂ hm
  refine ⟨c, hc, ?_, fieldSem_meet sem⟩
  simp only [Elixir.Module.Types.Descr.«field_opt_intersection/3», run]
  cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso]

/-- Maps a literal allows at every key but one atom key. -/
def MSemExcept (den : Term → V → Prop) (tag : Term) (l : List (Term × Term)) (a : String) (w : MW V) : Prop :=
  (∀ s, s ≠ a → FSem den tag l s (w (.atom s))) ∧ ∀ k i, TagSem den tag (domKind k) (w (.dom k i))

theorem msem_split_at {tag : Term} {l : List (Term × Term)} {a : String} {f : Term}
    (at_a : ∀ o, FSem den tag l a o ↔ FieldSem den f o) (w : (MW V)) :
    MSem den tag l w ↔ MSemExcept den tag l a w ∧ FieldSem den f (w (.atom a)) := by
  constructor
  · intro h; exact ⟨⟨fun s _ => h s, h.doms⟩, (at_a _).mp (h a)⟩
  · rintro ⟨⟨h, hd⟩, ha⟩
    refine ⟨fun s => ?_, hd⟩
    by_cases e : s = a
    · subst e; exact (at_a _).mpr ha
    · exact h s e

/-- Literals without an atom key allow there the default field of their tag. -/
theorem msem_split_absent (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} {a : String}
    (la : mapLookup l (.atom a) = Option.none) (w : (MW V)) :
    MSem den tag l w ↔ MSemExcept den tag l a w ∧ FieldSem den (tagField tag) (w (.atom a)) :=
  msem_split_at (fun o => by rw [fieldSem_tagV ef.mopsE ef.mdopsE ef.semR g]; simp only [FSem, la]) w

theorem msem_split {tag : Term} {l : List (Term × Term)} {a : String} {f : Term} (la : mapLookup l (.atom a) = some f)
    (w : (MW V)) : MSem den tag l w ↔ MSemExcept den tag l a w ∧ FieldSem den f (w (.atom a)) := by
  have at_a : FSem den tag l a (w (.atom a)) ↔ FieldSem den f (w (.atom a)) := by unfold FSem; rw [la]
  constructor
  · intro h; exact ⟨⟨fun s _ => h s, h.doms⟩, at_a.mp (h a)⟩
  · rintro ⟨⟨h, hd⟩, ha⟩
    refine ⟨fun s => ?_, hd⟩
    by_cases e : s = a
    · subst e; exact at_a.mpr ha
    · exact h s e

theorem msem_store {tag : Term} {l l' : List (Term × Term)} {a : String} {d : Term}
    (look : ∀ s, mapLookup l' (.atom s) = if a = s then some d else mapLookup l (.atom s)) (w : (MW V)) :
    MSem den tag l' w ↔ MSemExcept den tag l a w ∧ FieldSem den d (w (.atom a)) := by
  have fs : ∀ s o, FSem den tag l' s o ↔ if a = s then FieldSem den d o else FSem den tag l s o := by
    intro s o
    unfold FSem
    rw [look s]
    by_cases e : a = s <;> simp [e]
  constructor
  · intro h
    refine ⟨⟨fun s ne => ?_, h.doms⟩, ?_⟩
    · have := (fs s (w (.atom s))).mp (h s); rwa [ite_eq_right (Ne.symm ne)] at this
    · have := (fs a (w (.atom a))).mp (h a); rwa [ite_eq_left rfl] at this
  · rintro ⟨⟨h, hd⟩, ha⟩
    refine ⟨fun s => ?_, hd⟩
    rw [fs]
    by_cases e : a = s
    · subst e; rw [ite_eq_left rfl]; exact ha
    · rw [ite_eq_right e]; exact h s (Ne.symm e)

/-- Map values. -/
def ValM (E : Term → Prop) (den : Term → V → Prop) (ρ : Term → Bool) : Prop := ∃ w, ρ = valM E den w

theorem valM_respM : ∀ ρ, ValM E den ρ → Resp ρ := fun _ ⟨w, e⟩ => e ▸ valM_resp w

theorem valM_leaf (ef : EF nd E V den tl K) {k : Int} {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l)
    (g : TagV E tag) (w : (MW V)) :
    valM E den w (.tuple #[.integer k, tag, fieldsTerm l]) = Bool.true ↔ MSem den tag l w :=
  (valM_iff ef.mopsE ef.mdopsE ef.semR ⟨k, tag, l, rfl, g, sl⟩).trans nsem_lit

/-- Storing a field into the fields of a literal makes a leaf of the literal's maps with that field. -/
theorem store_leaf (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l)
    (a : String) {d : Term} (hd : FieldValue E d) :
    ∃ (k : Int) (l' : List (Term × Term)), Erlang.orddict.«store/3» (.atom a) d (fieldsTerm l) = .ok (fieldsTerm l') ∧
      Elixir.Module.Types.Descr.«bdd_leaf_new/2» tag (fieldsTerm l') =
        .ok (.tuple #[.integer k, tag, fieldsTerm l']) ∧
      MLit E (.tuple #[.integer k, tag, fieldsTerm l']) ∧
      ∀ w, valM E den w (.tuple #[.integer k, tag, fieldsTerm l']) = Bool.true ↔
        MSemExcept den tag l a w ∧ FieldSem den d (w (.atom a)) := by
  obtain ⟨l', runS, sl', -, look⟩ := store_val a hd sl
  obtain ⟨k, leaf, key⟩ := leaf_new_keyM g (l'.map fun e => .tuple #[e.1, e.2])
  have ne : ¬(tag = .atom "open" ∧ l' = []) := by
    rintro ⟨-, rfl⟩
    have := look a
    simp [mapLookup] at this
  refine ⟨k, l', runS, leaf, ⟨⟨k, tag, l', rfl, g, sl'⟩, fun ⟨_, e⟩ => leaf_not_top ne e, key⟩, fun w => ?_⟩
  rw [valM_leaf ef sl' g, msem_store look]

/-- The one-key difference of a literal and another that agrees with it but at one key. -/
theorem one_key_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {k₁ : Int} {tag : Term} (g : TagV E tag)
    {l : List (Term × Term)} (sl : FieldsV E l) (_ntop : ¬(tag = .atom "open" ∧ l = []))
    (_key₁ : KeyOk (.tuple #[.integer k₁, tag, fieldsTerm l])) (a₂ : Term) {a : String}
    {t₁ t₂ : Term} {o₁ o₂ : Bool} (ht₁ : E t₁) (ht₂ : E t₂)
    (split : ∀ w, MSem den tag l w ↔ MSemExcept den tag l a w ∧ FieldSem den (.tuple #[t₁, boolAtom o₁]) (w (.atom a)))
    (type : Term) (S : List (Term × Term))
    (htype : type = .atom "none" ∨ type = .atom "intersection" ∨ type = .atom "union")
    (rel : ∀ w, MSem den tag l w → (valM E den w a₂ = Bool.true ↔ FieldSem den (.tuple #[t₂, boolAtom o₂]) (w (.atom a))))
    (full : type = .atom "union" → ∀ w, valM E den w a₂ = Bool.true ↔
      MSemExcept den tag l a w ∧ FieldSem den (.tuple #[t₂, boolAtom o₂]) (w (.atom a))) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7» (D m) tag (fieldsTerm l) (.atom a)
        (.tuple #[t₁, boolAtom o₁]) (.tuple #[t₂, boolAtom o₂]) type (.map S) = .ok res ∧
      CmpOk (ValM E den) (MLit E) (.tuple #[.integer k₁, tag, fieldsTerm l]) a₂ type res := by
  have v₁ : ∀ w, valM E den w (.tuple #[.integer k₁, tag, fieldsTerm l]) = Bool.true ↔ MSem den tag l w :=
    valM_leaf ef sl g
  obtain ⟨c, hc, runc, semc⟩ := field_opt_diff_val ef (m := m) (o₁ := o₁) (o₂ := o₂) (by omega) ht₁ ht₂ S
  obtain ⟨e, rune, seme⟩ := field_empty1_val ef (m := m) (by omega) hc (o₁ && !o₂)
  cases e
  rotate_left
  · refine ⟨.atom "subtype", ?_, Or.inr (Or.inl ⟨rfl, fun ρ ⟨w, ew⟩ h => ?_⟩)⟩
    · rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
      simp only [runc, rune, Lynx.Except.ok_bind]
      simp [boolAtom, isMember]
    · subst ew
      have hm₁ := (v₁ w).mp h
      have f₁ := ((split w).mp hm₁).2
      refine (rel w hm₁).mpr (Classical.byContradiction fun nf => ?_)
      exact (seme.mp rfl) (w (.atom a)) ((semc (w (.atom a))).mpr ⟨f₁, nf⟩)
  obtain ⟨kd, ld, runS, leafd, okd, semd⟩ := store_leaf ef g sl a (d := .tuple #[c, boolAtom (o₁ && !o₂)]) ⟨c, _, rfl, hc⟩
  have sad : ∀ ρ, ValM E den ρ → eval ρ (.tuple #[.integer kd, tag, fieldsTerm ld]) =
      (ρ (.tuple #[.integer k₁, tag, fieldsTerm l]) && !ρ a₂) := by
    rintro ρ ⟨w, rfl⟩
    rw [eval_leaf]
    apply Bool.eq_iff_iff.mpr
    rw [semd, Bool.and_eq_true, v₁, Bool.not_eq_true', ← Bool.not_eq_true, split, semc]
    constructor
    · rintro ⟨h, f₁, nf₂⟩
      exact ⟨⟨h, f₁⟩, fun r => nf₂ ((rel w ((split w).mpr ⟨h, f₁⟩)).mp r)⟩
    · rintro ⟨⟨h, f₁⟩, nr⟩
      exact ⟨h, f₁, fun f₂ => nr ((rel w ((split w).mpr ⟨h, f₁⟩)).mpr f₂)⟩
  have ad : LeafOrBot (MLit E) (.tuple #[.integer kd, tag, fieldsTerm ld]) := Or.inr ⟨kd, _, _, rfl, okd⟩
  rcases htype with rfl | rfl | rfl
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨_, .atom "bdd_bot", rfl, ad, Or.inl rfl, sad, fun h => by simp at h,
      fun h => by simp at h, fun _ => rfl⟩))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
    simp only [runc, rune, runS, leafd, Lynx.Except.ok_bind]
    simp [boolAtom, isMember]
  · obtain ⟨ci, hci, runi, semi⟩ := field_opt_inter_val ef (m := m) (o₁ := o₁) (o₂ := o₂) (by omega) ht₁ ht₂ S
    obtain ⟨ei, runei, semei⟩ := field_empty1_val ef (m := m) (by omega) hci (o₁ && o₂)
    cases ei
    · obtain ⟨ki, li, runSi, leafi, oki, semli⟩ := store_leaf ef g sl a (d := .tuple #[ci, boolAtom (o₁ && o₂)])
        ⟨ci, _, rfl, hci⟩
      refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨_, _, rfl, ad, Or.inr ⟨ki, _, _, rfl, oki⟩, sad, fun _ ρ hρ => ?_,
        fun h => by simp at h, fun h => by simp at h⟩))⟩
      · rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
        simp only [runc, rune, runS, leafd, runi, runei, runSi, leafi, Lynx.Except.ok_bind]
        simp [boolAtom, isMember]
      · obtain ⟨w, rfl⟩ := hρ
        rw [eval_leaf]
        apply Bool.eq_iff_iff.mpr
        rw [semli, Bool.and_eq_true, v₁, split, semi]
        constructor
        · rintro ⟨h, f₁, f₂⟩
          exact ⟨⟨h, f₁⟩, (rel w ((split w).mpr ⟨h, f₁⟩)).mpr f₂⟩
        · rintro ⟨⟨h, f₁⟩, r⟩
          exact ⟨h, f₁, (rel w ((split w).mpr ⟨h, f₁⟩)).mp r⟩
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨_, .atom "bdd_bot", rfl, ad, Or.inl rfl, sad, fun _ ρ hρ => ?_,
        fun h => by simp at h, fun h => by simp at h⟩))⟩
      · rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
        simp only [runc, rune, runS, leafd, runi, runei, Lynx.Except.ok_bind]
        simp [boolAtom, isMember]
      · obtain ⟨w, rfl⟩ := hρ
        symm
        apply Bool.eq_false_iff.mpr
        intro h
        rw [Bool.and_eq_true, v₁] at h
        obtain ⟨h₁, h₂⟩ := h
        have f₁ := ((split w).mp h₁).2
        exact (semei.mp rfl) (w (.atom a)) ((semi (w (.atom a))).mpr ⟨f₁, (rel w h₁).mp h₂⟩)
  · obtain ⟨cu, hcu, runu, semu⟩ := field_opt_union_val ef (m := m) (o₁ := o₁) (o₂ := o₂) (by omega) rfl rfl ht₁ ht₂ S
    obtain ⟨ku, lu, runSu, leafu, oku, semlu⟩ := store_leaf ef g sl a (d := .tuple #[cu, boolAtom (o₁ || o₂)])
      ⟨cu, _, rfl, hcu⟩
    refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨_, _, rfl, ad, Or.inr ⟨ku, _, _, rfl, oku⟩, sad, fun h => by simp at h,
      fun _ ρ hρ => ?_, fun h => by simp at h⟩))⟩
    · rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
      simp only [runc, rune, runS, leafd, runu, runSu, leafu, Lynx.Except.ok_bind]
      simp [boolAtom, isMember]
    · obtain ⟨w, rfl⟩ := hρ
      rw [eval_leaf]
      apply Bool.eq_iff_iff.mpr
      rw [semlu, Bool.or_eq_true, v₁, split, full rfl w, semu]
      constructor
      · rintro ⟨h, f₁ | f₂⟩
        · exact Or.inl ⟨h, f₁⟩
        · exact Or.inr ⟨h, f₂⟩
      · rintro (⟨h, f₁⟩ | ⟨h, f₂⟩)
        · exact ⟨h, Or.inl f₁⟩
        · exact ⟨h, Or.inr f₂⟩

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Optimized differences of map literals. -/

/-- `opt_map_difference_strategy/4` on literals of value maps. -/
theorem dstrat_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₁ t₂ : String} (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {l₁ l₂ : List (Term × Term)} (s₁ : FieldsV E l₁) (s₂ : FieldsV E l₂) :
    ∃ st, Elixir.Module.Types.Descr.«opt_map_difference_strategy/4» (D m) (fieldsTerm l₁) (fieldsTerm l₂) (.atom t₁)
      (.atom t₂) = .ok st ∧ DRes E den t₁ t₂ st l₁ l₂ := by
  have walk := fun st inv => dwalk ef hm t₁ t₂ g₁ g₂ _ l₁ l₂ [] [] st (Nat.le_refl _) (by simpa using s₁)
    (by simpa using s₂) (by simp) inv
  by_cases tc : t₁ = t₂ ∨ t₂ = "open"
  · obtain ⟨st, run, res⟩ := walk (.atom "all_equal") (Or.inl ⟨rfl, tc, fun s tag o => Iff.rfl⟩)
    refine ⟨st, ?_, by simpa using res⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/4».eq_def]
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
      simp_all [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, Lynx.Except.orElse, Erlang.erlang.«==/2»]
  · obtain ⟨st, run, res⟩ := walk (.atom "none") (Or.inr (Or.inr (Or.inr rfl)))
    refine ⟨st, ?_, by simpa using res⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/4».eq_def]
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
      simp_all [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, Lynx.Except.orElse, Erlang.erlang.«==/2»]

/-- The general clause of `opt_map_leaf_difference/4`, which the single-key clause does not take. -/
theorem leaf_diff_general {d : Dispatcher} {S type : Term} {k₁ k₂ : Int} {t₁ t₂ : Term}
    {l₁ l₂ : List (Term × Term)} {st r : Term}
    (h : t₂ = .atom "open" → (∃ key f, l₂ = [(key, f)]) → type = .atom "union")
    (hs : Elixir.Module.Types.Descr.«opt_map_difference_strategy/4» d (fieldsTerm l₁) (fieldsTerm l₂) t₁ t₂ = .ok st)
    (hr : st = .atom "disjoint" ∧ r = .atom "disjoint" ∨ st = .atom "left_subtype_of_right" ∧ r = .atom "subtype" ∨
      st = .atom "none" ∧ r = .atom "none" ∨ ∃ key v₁ v₂, st = .tuple #[.atom "one_key_difference", key, v₁, v₂] ∧
        Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7» d t₁ (fieldsTerm l₁) key v₁ v₂ type S =
          .ok r) :
    Elixir.Module.Types.Descr.«opt_map_leaf_difference/4» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
      (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) type S = .ok r := by
  rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
  split
  · rename_i heq₁ heq₂
    obtain ⟨-, e₂, e₃⟩ := tuple3_eq heq₂
    have hl : ∃ key f, l₂ = [(key, f)] := by
      cases l₂ with
      | nil => simp [fieldsTerm, Term.list] at e₃
      | cons x xs =>
        cases xs with
        | nil =>
          simp [fieldsTerm, Term.list] at e₃
          exact ⟨x.1, x.2, by obtain ⟨k, f⟩ := x; simp⟩
        | cons y ys => simp [fieldsTerm, Term.list] at e₃
    have hu := h e₂ hl
    subst hu
    rw [e₃, e₂] at hs
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨key, v₁, v₂, rfl, run⟩ <;>
      simp [Erlang.erlang.«/=/2», *]
  · rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨key, v₁, v₂, rfl, run⟩ <;> simp [*]

theorem lookup_fieldValue {l : List (Term × Term)} (sl : FieldsV E l) {s : String} {f : Term}
    (h : mapLookup l (.atom s) = some f) : FieldValue E f := by
  obtain ⟨e, me, -, fe⟩ := lookup_some_mem h
  rw [← fe]; exact (sl.1 e me).2

/-- `opt_map_leaf_difference/4` compares map literals soundly. -/
theorem map_leaf_cmp (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a₁ a₂ type : Term) (S : List (Term × Term)) (ht : TypeOk type) (h₁ : MLit E a₁)
    (h₂ : MLit E a₂) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_leaf_difference/4» (D m) a₁ a₂ type (.map S) = .ok res ∧
      CmpOk (ValM E den) (MLit E) a₁ a₂ type res := by
  obtain ⟨⟨k₁, t₁, l₁, rfl, g₁, s₁⟩, n₁, key₁⟩ := h₁
  obtain ⟨⟨k₂, t₂, l₂, rfl, g₂, s₂⟩, n₂, key₂⟩ := h₂
  have nt₁ : ¬(t₁ = .atom "open" ∧ l₁ = []) := fun ⟨a, b⟩ => n₁ ⟨_, by rw [a, b]; rfl⟩
  have nt₂ : ¬(t₂ = .atom "open" ∧ l₂ = []) := fun ⟨a, b⟩ => n₂ ⟨_, by rw [a, b]; rfl⟩
  have v₁ := valM_leaf ef (k := k₁) s₁ g₁
  have v₂ := valM_leaf ef (k := k₂) s₂ g₂
  by_cases c1 : (t₂ = .atom "open" ∧ ∃ b f, l₂ = [(.atom b, f)]) ∧ type ≠ .atom "union"
  · obtain ⟨⟨rfl, b, f₂, rfl⟩, nu⟩ := c1
    obtain ⟨u₂, o₂, rfl, hu₂⟩ := (s₂.1 (.atom b, f₂) (by simp)).2
    have rel₂ : ∀ w, valM E den w (.tuple #[.integer k₂, .atom "open", fieldsTerm [(.atom b, .tuple #[u₂, boolAtom o₂])]]) =
        Bool.true ↔ FieldSem den (.tuple #[u₂, boolAtom o₂]) (w (.atom b)) := fun w => by rw [v₂, msem_one]
    have e2 : fieldsTerm [(Term.atom b, Term.tuple #[u₂, boolAtom o₂])] =
        .cons (.tuple #[.atom b, .tuple #[u₂, boolAtom o₂]]) .nil := rfl
    have tyc : type = .atom "none" ∨ type = .atom "intersection" := by
      rcases ht with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h nu
    have fnd := find_val b s₁
    cases hl : mapLookup l₁ (.atom b) with
    | none =>
      rw [hl] at fnd
      rcases g₁ with rfl | rfl | ⟨dl, rfl, dv⟩
      · have nn : fieldsTerm l₁ ≠ .nil := fun e => nt₁ ⟨rfl, fieldsTerm_eq_nil.mp e⟩
        refine ⟨.atom "none", ?_, Or.inr (Or.inr (Or.inr rfl))⟩
        rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
        simp only [e2]
        rcases tyc with rfl | rfl <;>
          simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            Erlang.erlang.«not/1», nn, Elixir.Module.Types.Descr.«map_key_tag_to_field/1»]
      · have absent : ∀ w, MSem den (.atom "closed") l₁ w → w (.atom b) = Option.none := fun w h => by
          rcases (fsem_none hl (w (.atom b))).mp (h b) with c | e
          · exact absurd c (by decide)
          · exact e
        cases o₂
        · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨w, e⟩ => ?_⟩⟩
          · rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
            simp only [e2]
            rcases tyc with rfl | rfl <;>
              simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
                Erlang.erlang.«not/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember]
          · subst e
            apply Bool.eq_false_iff.mpr
            intro h
            rw [Bool.and_eq_true, v₁, rel₂] at h
            rw [absent w h.1, fieldSem_mk] at h
            simp at h
        · refine ⟨.atom "subtype", ?_, Or.inr (Or.inl ⟨rfl, fun ρ ⟨w, e⟩ h => ?_⟩)⟩
          · rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
            simp only [e2]
            rcases tyc with rfl | rfl <;>
              simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
                Erlang.erlang.«not/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember]
          · subst e
            rw [v₁] at h
            rw [rel₂, absent w h, fieldSem_mk]
            simp
      · -- the default field of the domains at the key meets the field of the negated literal
        have gd : TagV E (fieldsTerm dl) := Or.inr (Or.inr ⟨dl, rfl, dv⟩)
        have hu₁ := tagType_value ef.mopsE gd "atom"
        have split := msem_split_absent ef gd hl
        obtain ⟨bd, rund, soundd⟩ := field_disj_bool ef hm (f₁ := tagField (fieldsTerm dl)) ⟨_, Bool.true, rfl, hu₁⟩
          ⟨u₂, o₂, rfl, hu₂⟩
        have ne : ∀ s, Erlang.erlang.«==/2» (fieldsTerm dl) (.atom s) = .ok (.atom "false") := fun s => by
          simp [Erlang.erlang.«==/2», fieldsTerm_ne_atom, Term.false]
        cases bd
        · obtain ⟨res, run, cmp⟩ := one_key_val ef hm gd s₁ nt₁ key₁ (k₁ := k₁) (o₁ := Bool.true)
            (.tuple #[.integer k₂, .atom "open", fieldsTerm [(.atom b, .tuple #[u₂, boolAtom o₂])]]) hu₁ hu₂ split type S
            (by rcases tyc with h | h <;> simp [h]) (fun w _ => rel₂ w) (fun h => absurd h nu)
          refine ⟨res, ?_, cmp⟩
          rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
          simp only [e2]
          simp [tagField, boolAtom] at run rund
          rcases tyc with rfl | rfl <;>
            simp [Erlang.erlang.«/=/2», fnd, ne, Lynx.Except.andAlso, key_tag_field gd, tagField,
              rund, boolAtom, run]
        · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨w, e⟩ => ?_⟩⟩
          · rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
            simp only [e2]
            simp [tagField, boolAtom] at rund
            rcases tyc with rfl | rfl <;>
              simp [Erlang.erlang.«/=/2», fnd, ne, Lynx.Except.andAlso, key_tag_field gd, tagField,
                rund, boolAtom]
          · subst e
            apply Bool.eq_false_iff.mpr
            intro h
            rw [Bool.and_eq_true, v₁, rel₂, split] at h
            exact soundd rfl _ h.1.2 h.2
    | some f₁ =>
      rw [hl] at fnd
      obtain ⟨u₁, o₁, ef₁, hu₁⟩ := lookup_fieldValue s₁ hl
      subst ef₁
      obtain ⟨bd, rund, soundd⟩ := field_disj_bool ef hm ⟨u₁, o₁, rfl, hu₁⟩ ⟨u₂, o₂, rfl, hu₂⟩
      cases bd
      · obtain ⟨res, run, cmp⟩ := one_key_val ef hm g₁ s₁ nt₁ key₁ (k₁ := k₁)
          (.tuple #[.integer k₂, .atom "open", fieldsTerm [(.atom b, .tuple #[u₂, boolAtom o₂])]]) hu₁ hu₂ (msem_split hl) type S
          (by rcases tyc with h | h <;> simp [h]) (fun w _ => rel₂ w) (fun h => absurd h nu)
        refine ⟨res, ?_, cmp⟩
        rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
        simp only [e2]
        simp only [boolAtom] at run rund
        rcases g₁ with rfl | rfl | ⟨dl, rfl, -⟩ <;> rcases tyc with rfl | rfl <;>
          simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            Erlang.erlang.«not/1», rund, boolAtom, run, fieldsTerm_ne_atom]
      · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨w, e⟩ => ?_⟩⟩
        · rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
          simp only [e2]
          simp only [boolAtom] at rund
          rcases g₁ with rfl | rfl | ⟨dl, rfl, -⟩ <;> rcases tyc with rfl | rfl <;>
            simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
              Erlang.erlang.«not/1», rund, boolAtom, fieldsTerm_ne_atom]
        · subst e
          apply Bool.eq_false_iff.mpr
          intro h
          rw [Bool.and_eq_true, v₁, rel₂, msem_split hl] at h
          exact soundd rfl _ h.1.2 h.2
  · have h : t₂ = .atom "open" → (∃ key f, l₂ = [(key, f)]) → type = .atom "union" := by
      rintro ho ⟨key, f, rfl⟩
      obtain ⟨b, rfl⟩ := (s₂.1 (key, f) (by simp)).1
      exact Classical.byContradiction fun nu => c1 ⟨⟨ho, b, f, rfl⟩, nu⟩
    -- literals with domains have no strategy
    by_cases atoms : ¬∃ x₁ x₂ : String, t₁ = .atom x₁ ∧ t₂ = .atom x₂
    · have hs : Elixir.Module.Types.Descr.«opt_map_difference_strategy/4» (D m) (fieldsTerm l₁) (fieldsTerm l₂) t₁ t₂ =
          .ok (.atom "none") := by
        rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/4».eq_def]
        simp [atoms_guard g₁ g₂ atoms]
      exact ⟨_, leaf_diff_general h hs (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), Or.inr (Or.inr (Or.inr rfl))⟩
    obtain ⟨t₁, t₂, rfl, rfl⟩ := Classical.not_not.mp atoms
    have g₁' := g₁.of_atom
    have g₂' := g₂.of_atom
    obtain ⟨st, hs, dres⟩ := dstrat_val ef hm g₁' g₂' s₁ s₂
    rcases dres with ⟨rfl, s, hd⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, la₁, la₂, eqv⟩ | ⟨rfl, sub⟩ | rfl
    · refine ⟨_, leaf_diff_general h hs (Or.inl ⟨rfl, rfl⟩), Or.inl ⟨rfl, fun ρ ⟨w, e⟩ => ?_⟩⟩
      subst e
      apply Bool.eq_false_iff.mpr
      intro hh
      rw [Bool.and_eq_true, v₁, v₂] at hh
      exact hd (w (.atom s)) (hh.1 s) (hh.2 s)
    · obtain ⟨u₁, o₁, rfl, hu₁⟩ := hp₁
      obtain ⟨u₂, o₂, rfl, hu₂⟩ := hp₂
      subst et
      have full : ∀ w, valM E den w (.tuple #[.integer k₂, .atom t₁, fieldsTerm l₂]) = Bool.true ↔
          MSemExcept den (.atom t₁) l₁ a w ∧ FieldSem den (.tuple #[u₂, boolAtom o₂]) (w (.atom a)) := by
        intro w
        rw [v₂, msem_split la₂]
        constructor
        · rintro ⟨⟨hs', hd⟩, ha⟩; exact ⟨⟨fun s ne => (eqv s ne t₁ (w (.atom s))).mpr (hs' s ne), hd⟩, ha⟩
        · rintro ⟨⟨hs', hd⟩, ha⟩; exact ⟨⟨fun s ne => (eqv s ne t₁ (w (.atom s))).mp (hs' s ne), hd⟩, ha⟩
      obtain ⟨res, run, cmp⟩ := one_key_val ef hm g₁ s₁ nt₁ key₁ (k₁ := k₁) _ hu₁ hu₂ (msem_split la₁) type S ht
        (fun w hw => by rw [full w, msem_split la₁] at *; exact ⟨fun h => h.2, fun h => ⟨hw.1, h⟩⟩)
        (fun _ => full)
      exact ⟨res, leaf_diff_general h hs (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl, run⟩))), cmp⟩
    · refine ⟨_, leaf_diff_general h hs (Or.inr (Or.inl ⟨rfl, rfl⟩)), Or.inr (Or.inl ⟨rfl, fun ρ ⟨w, e⟩ hh => ?_⟩)⟩
      subst e
      rw [v₁] at hh
      rw [v₂]
      obtain ⟨v₀⟩ := ef.inhabited
      exact msem_of_atoms v₀ (fun s o => sub s o) hh
    · exact ⟨_, leaf_diff_general h hs (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), Or.inr (Or.inr (Or.inr rfl))⟩

theorem opt_map_seen {d : Dispatcher} {x y S : Term} (nx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) (ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq)
    (hs : Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "map_difference") x y = .ok (.atom "seen")) :
    Elixir.Module.Types.Descr.«opt_map_difference/3» d x y S = Elixir.Module.Types.Descr.«map_difference/2» x y := by
  rw [Elixir.Module.Types.Descr.«opt_map_difference/3».eq_def]
  split
  · exact absurd rfl (ny _)
  simp only [leaf_guard]
  split
  · rw [ite_eq_right (ne _ _ _ rfl)]
    split
    · exfalso; simp_all
    · exfalso; simp_all
    · simp [hs]
  · split
    · exact absurd rfl (nx _)
    · exact absurd rfl (nx _)
    · simp [hs]

theorem opt_map_ok {d : Dispatcher} {x y S S' : Term} (nx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) (ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq)
    (hs : Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "map_difference") x y = .ok (.tuple #[.atom "ok", S'])) :
    Elixir.Module.Types.Descr.«opt_map_difference/3» d x y S = Elixir.Module.Types.Descr.«bdd_difference/3» d x y
      (.function false "Elixir.Module.Types.Descr" "-opt_map_difference/3-fun-0-" 3 #[S']) := by
  rw [Elixir.Module.Types.Descr.«opt_map_difference/3».eq_def]
  split
  · exact absurd rfl (ny _)
  simp only [leaf_guard]
  split
  · rw [ite_eq_right (ne _ _ _ rfl)]
    split
    · exfalso; simp_all
    · exfalso; simp_all
    · simp [hs]
  · split
    · exact absurd rfl (nx _)
    · exact absurd rfl (nx _)
    · simp [hs]

theorem opt_map_diff_same {d : Dispatcher} {S k a b y : Term} (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil])
    (e : compareExact (fuel y (.tuple #[k, a, b])) y (.tuple #[k, a, b]) = .eq) :
    Elixir.Module.Types.Descr.«opt_map_difference/3» d (.tuple #[k, a, b]) y S = .ok (.atom "bdd_bot") := by
  rw [Elixir.Module.Types.Descr.«opt_map_difference/3».eq_def]
  split
  · exact absurd rfl (ny _)
  simp only [leaf_guard]
  rw [ite_eq_left (by simpa using e)]
  rfl

/-- Optimized differences of map types hold the maps of the first and not the second. -/
theorem opt_map_diff_val (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {x y : Term} (fx : MField E x) (fy : MField E y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_map_difference/3» (D (n + 1)) x y (.map S) = .ok w ∧
      (kept (.atom "map", w) = Bool.true → MField E w ∧ ∀ v, denMF E den w v = (denMF E den x v && !denMF E den y v)) ∧
      (kept (.atom "map", w) = Bool.false → ∀ v, (denMF E den x v && !denMF E den y v) = Bool.false) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«opt_map_difference/3»; rfl,
      fun kw => by simp [kept] at kw, fun _ v => by rw [denMF_top]; simp⟩
  rcases fx with ⟨k₀, rfl⟩ | wx
  · obtain ⟨w, run, k, d⟩ := map_neg_valK ef k₀ (m := n + 1) (by omega) (Or.inr wy) S
    exact ⟨w, run, fun kw => ⟨(k kw).1, fun v => by rw [(k kw).2 v, denMF_top]; simp⟩,
      fun kw v => by rw [d kw v]; simp⟩
  have wxV := wx
  have wyV := wy
  have nx := not_top_of_ok wxV mlit_not
  have ny := not_top_of_ok wyV mlit_not
  by_cases same : ∃ a b c, x = .tuple #[a, b, c] ∧ compareExact (fuel y x) y x = .eq
  · obtain ⟨a, b, c, rfl, e⟩ := same
    exact ⟨_, opt_map_diff_same ny e, fun kw => by simp [kept] at kw, fun _ v => by
      rw [denMF_exact (Or.inr wxV) (Or.inr wyV) e, Bool.and_not_self]⟩
  have ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq := fun a b c ex e => same ⟨a, b, c, ex, e⟩
  rcases opt_bdd_seen_map S (.atom "map_difference") x y with seen | ⟨S', ok⟩
  · obtain ⟨w, run, fw, sem⟩ := map_diff_val (Or.inr wxV) (Or.inr wyV)
    refine ⟨w, by rw [opt_map_seen nx ny ne seen, run], fun _ => ⟨fw, sem⟩, fun kw v => ?_⟩
    rw [← sem v]
    rcases fw with ⟨k', rfl⟩ | ww
    · simp [kept] at kw
    · rw [denMF_bdd ww]; exact drop_bdd ww kw _
  · obtain ⟨r, hr, okr, semr⟩ := diff3_ok valM_respM (d := D (n + 1))
      (cmp := .function false "Elixir.Module.Types.Descr" "-opt_map_difference/3-fun-0-" 3 #[.map S'])
      (fun a₁ a₂ type ht h₁ h₂ => by
        obtain ⟨res, run, cmp⟩ := map_leaf_cmp ef (m := n) hn a₁ a₂ type S' ht h₁ h₂
        refine ⟨res, ?_, cmp⟩
        rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_map_difference/3-fun-0-/3».pure]
        simpa [Elixir.Module.Types.Descr.«-opt_map_difference/3-fun-0-/4»] using run)
      _ y wyV (fun _ h => h) x wxV
    have sem : ∀ v, denMF E den r v = (denMF E den x v && !denMF E den y v) := fun v => by
      rw [denMF_bdd okr, denMF_bdd wxV, denMF_bdd wyV, semr _ ⟨v, rfl⟩]
    refine ⟨r, by rw [opt_map_ok nx ny ne ok, hr], fun _ => ⟨Or.inr okr, sem⟩, fun kw v => ?_⟩
    rw [← sem v, denMF_bdd okr]; exact drop_bdd okr kw _

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Map lines found empty have no maps outside their negations: the soundness of map emptiness. -/

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Maps of a line with another field at a key, when they have a value of that field there. -/
theorem msem_swap {tag : Term} {a : String} {A B : List (Term × Term)} (_fresh : mapLookup A (.atom a) = Option.none)
    {f f' : Term} {w : MW V} (hw : MSem den tag (A ++ (Term.atom a, f) :: B) w) (h : FieldSem den f' (w (.atom a))) :
    MSem den tag (A ++ (Term.atom a, f') :: B) w := by
  refine hw.of_atoms fun s hs => ?_
  unfold FSem at hs ⊢
  rw [lookup_append] at hs ⊢
  cases e : mapLookup A (.atom s) with
  | some x => simpa [e] using hs
  | none =>
    rw [e] at hs
    simp only [Option.none_or] at hs ⊢
    rw [lookup_cons_atom] at hs ⊢
    by_cases as : a = s
    · subst as; simpa using h
    · simpa [as] using hs

/-- One aligned field of `map_line_meet_empty?/5`, read from a `true` answer: a map of the line holds the field minus
the negated one, and is covered by the other negations, or holds a field within both, and the walk carries on. -/
theorem meet_step_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K ≤ m) {S : List (Term × Term)} (hS : Safe S) (tag : Term) (negs : List Term)
    (a : String) (f₁ f₂ : Term) (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) (t₁ acc : List (Term × Term))
    (es : List Entry)
    (sorted : FieldsV E (acc.reverse ++ (Term.atom a, f₁) :: t₁)) (fresh : mapLookup acc.reverse (Term.atom a) = Option.none)
    (lineT : ∀ l, FieldsV E l → ∃ b : Bool, Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
      (Term.list negs) (.map S) = .ok (boolAtom b))
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    {Goal : (MW V) → Prop}
    (rec : ∀ f, FieldValue E f → (∀ o, FieldSem den f o → FieldSem den f₁ o ∧ FieldSem den f₂ o) →
      Elixir.Module.Types.Descr.«map_line_meet_empty?/5» (D m) (entriesTerm es) tag
        (fieldsTerm ((.atom a, f) :: acc)) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ w, MSem den tag (acc.reverse ++ (Term.atom a, f) :: t₁) w → Goal w ∨ CovM den negs w)
    (run : Elixir.Module.Types.Descr.«map_line_meet_empty?/5» (D m) (entriesTerm ((.atom a, f₁, some f₂, t₁) :: es))
      tag (fieldsTerm acc) (Term.list negs) (.map S) = .ok (.atom "true")) :
    ∀ w, MSem den tag (acc.reverse ++ (Term.atom a, f₁) :: t₁) w → Goal w ∨ CovM den negs w := by
  obtain ⟨ty, o₁, rfl, hty⟩ := h₁
  obtain ⟨nt, o₂, rfl, hnt⟩ := h₂
  obtain ⟨meet, lmeet, hmeet⟩ := ops.inter hty hnt
  obtain ⟨diff, ldiff, hdiff⟩ := dops.diff hty hnt
  obtain ⟨bd, ed⟩ := field_empty_total ops S ldiff (o₁ && !o₂)
  have semMeet := fieldSem_meet (t := meet) (esem.inter hty hnt hm (hmeet m hm)) (o₁ := o₁) (o₂ := o₂)
  have semDiff := fieldSem_diff (t := diff) (esem.diff hty hnt hm (hdiff m hm)) (o₁ := o₁) (o₂ := o₂)
  have emptyDiff := field_empty_sem ops dops esem ldiff hS hm (ed m hm)
  have flag : Lynx.Except.andAlso (pure (boolAtom o₁)) (Erlang.erlang.«not/1» (boolAtom o₂)) Bool.true =
      .ok (boolAtom (o₁ && !o₂)) := by
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
  have both : Lynx.Except.andAlso (pure (boolAtom o₁)) (pure (boolAtom o₂)) Bool.true =
      .ok (boolAtom (o₁ && o₂)) := by
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso]
  have rev := reverse_fields acc ((.atom a, .tuple #[diff, boolAtom (o₁ && !o₂)]) :: t₁)
  simp only [fieldsTerm_cons] at rev
  have atA : ∀ w f, MSem den tag (acc.reverse ++ (Term.atom a, f) :: t₁) w → FieldSem den f (w (.atom a)) := by
    intro w f hw
    have := hw a
    unfold FSem at this
    rw [lookup_append, fresh] at this
    simpa [lookup_cons_atom] using this
  rw [entriesTerm_cons, Elixir.Module.Types.Descr.«map_line_meet_empty?/5».eq_def] at run
  simp only [entryTerm, Option.getD] at run
  rw [flag] at run
  simp only [Lynx.Except.ok_bind, hdiff m hm, ed m hm] at run
  intro w hw
  have wa := atA w _ hw
  cases bd
  · obtain ⟨bl, hl⟩ := lineT _ (fieldsV_mid sorted ⟨diff, o₁ && !o₂, rfl, ldiff⟩)
    simp only [rev, Lynx.Except.ok_bind, hl] at run
    cases bl
    · simp [boolAtom, isMember] at run
    rw [both] at run
    have recRun : Elixir.Module.Types.Descr.«map_line_meet_empty?/5» (D m) (entriesTerm es) tag
        (fieldsTerm ((.atom a, .tuple #[meet, boolAtom (o₁ && o₂)]) :: acc)) (Term.list negs) (.map S) =
          .ok (.atom "true") := by
      simp only [fieldsTerm_cons]
      simpa [boolAtom, isMember, hmeet m hm] using run
    by_cases f₂a : FieldSem den (.tuple #[nt, boolAtom o₂]) (w (.atom a))
    · exact rec _ ⟨meet, _, rfl, lmeet⟩ (fun o h => (semMeet o).mp h) recRun w
        (msem_swap fresh hw ((semMeet (w (.atom a))).mpr ⟨wa, f₂a⟩))
    · exact Or.inr (lineS _ (fieldsV_mid sorted ⟨diff, o₁ && !o₂, rfl, ldiff⟩) (by simpa [boolAtom] using hl) w
        (msem_swap fresh hw ((semDiff (w (.atom a))).mpr ⟨wa, f₂a⟩)))
  · have sub : ∀ o, FieldSem den (.tuple #[ty, boolAtom o₁]) o → FieldSem den (.tuple #[nt, boolAtom o₂]) o :=
      fun o h => Classical.byContradiction fun nf => (emptyDiff.mp rfl) o ((semDiff o).mpr ⟨h, nf⟩)
    have recRun : Elixir.Module.Types.Descr.«map_line_meet_empty?/5» (D m) (entriesTerm es) tag
        (fieldsTerm ((.atom a, .tuple #[ty, boolAtom o₁]) :: acc)) (Term.list negs) (.map S) = .ok (.atom "true") := by
      simp only [fieldsTerm_cons]
      simpa [boolAtom, isMember] using run
    exact rec _ ⟨ty, o₁, rfl, hty⟩ (fun o h => ⟨h, sub o h⟩) recRun w hw

theorem fsem_lookup {tag : Term} {l : List (Term × Term)} {s : String} {f : Term}
    (h : mapLookup l (.atom s) = some f) (o : Option V) : FSem den tag l s o ↔ FieldSem den f o := by
  simp only [FSem, h]

theorem fsem_default (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {tag : Term}
    (g : TagV E tag) {l : List (Term × Term)} {s : String} (h : mapLookup l (.atom s) = Option.none) (o : Option V) :
    FSem den tag l s o ↔ FieldSem den (tagField tag) o := by
  rw [fieldSem_tagV ops dops esem g]; simp only [FSem, h]

/-- One key of a field walk, read from a `true` answer: a map of the line outside the remaining negations holds
the negated field at the key. -/
theorem recur_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) {tag : Term} {negs : List Term}
    {fields : List (Term × Term)} (sf : FieldsV E fields)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    (a : String) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) {w : MW V}
    (hw : MSemExcept den tag fields a w) (wa : FieldSem den f₁ (w (.atom a))) (nc : ¬CovM den negs w)
    (run : Elixir.Module.Types.Descr.«map_line_fields_empty_recur?/7» (D m) (.atom a) f₁ f₂ tag (fieldsTerm fields)
      (Term.list negs) (.map S) = .ok (.atom "true")) :
    FieldSem den f₂ (w (.atom a)) := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  have hm2 : K ≤ m := by omega
  obtain ⟨diff, ldiff, hdiff⟩ := dops.diff ht₁ ht₂
  obtain ⟨bd, ed⟩ := field_empty_total ops S ldiff (o₁ && !o₂)
  have semDiff := fieldSem_diff (t := diff) (esem.diff ht₁ ht₂ hm2 (hdiff m hm2)) (o₁ := o₁) (o₂ := o₂)
  have emptyDiff := field_empty_sem ops dops esem ldiff hS hm2 (ed m hm2)
  obtain ⟨l', runS, sl', -, look⟩ := store_val a ⟨diff, _, rfl, ldiff⟩ sf
  refine Classical.byContradiction fun nf => ?_
  have wd := (semDiff (w (.atom a))).mpr ⟨wa, nf⟩
  cases bd
  · have flag : Lynx.Except.andAlso (pure (boolAtom o₁)) (Erlang.erlang.«not/1» (boolAtom o₂)) Bool.true =
        .ok (boolAtom (o₁ && !o₂)) := by
      cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
    have e := ed m hm2
    have cover := fun r => nc (lineS l' sl' r w ((msem_store look w).mpr ⟨hw, wd⟩))
    generalize (o₁ && !o₂) = od at e runS flag
    rw [Elixir.Module.Types.Descr.«map_line_fields_empty_recur?/7».eq_def] at run
    simp only [hdiff m hm2, flag] at run
    simp [e, runS] at run
    exact cover run
  · exact (emptyDiff.mp rfl) _ wd

/-- The fields left on the positive side of a field walk, read from a `true` answer. -/
theorem pos_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gn : TagV E ntag) {negs : List Term}
    {fields : List (Term × Term)} (sf : FieldsV E fields)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    {nfields : List (Term × Term)} {w : MW V} (hw : MSem den tag fields w) (nc : ¬CovM den negs w) :
    ∀ (l P : List (Term × Term)), fields = P ++ l →
      (∀ e ∈ l, ∀ s : String, e.1 = .atom s → mapLookup nfields (.atom s) = Option.none) →
      Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6» (D m) (fieldsTerm l) (tagField ntag) tag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ e ∈ l, ∀ s : String, e.1 = .atom s → FSem den ntag nfields s (w (.atom s)) := by
  intro l
  induction l with
  | nil => intro _ _ _ _ e me; simp at me
  | cons x t ih =>
    intro P hP fresh run e me s es
    obtain ⟨k, f⟩ := x
    rw [Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6».eq_def] at run
    simp only [fieldsTerm_cons, Lynx.Except.andAlso_eq_true] at run
    have mem : (k, f) ∈ fields := by rw [hP]; simp
    obtain ⟨a, rfl⟩ := (sf.1 _ mem).1
    rcases List.mem_cons.mp me with rfl | me
    · simp only [Term.atom.injEq] at es
      subst es
      have wa := (fsem_lookup (lookup_of_mem sf mem rfl) _).mp (hw a)
      exact (fsem_default ops dops esem gn (fresh _ List.mem_cons_self _ rfl) _).mpr
        (recur_sound ops dops esem hm hS sf lineS a (sf.1 _ mem).2 (tagFieldV_value ops gn) ⟨fun s _ => hw s, hw.doms⟩
          wa nc run.1)
    · exact ih (P ++ [(Term.atom a, f)]) (by rw [hP]; simp) (fun e me => fresh e (List.mem_cons_of_mem _ me)) run.2 e me s es

/-- The fields left on the negative side of a field walk, read from a `true` answer. -/
theorem neg_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gt : TagV E tag) {negs : List Term}
    {fields : List (Term × Term)} (sf : FieldsV E fields)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    {nfields : List (Term × Term)} (snf : FieldsV E nfields) {w : MW V} (hw : MSem den tag fields w)
    (nc : ¬CovM den negs w) :
    ∀ (l Q : List (Term × Term)), nfields = Q ++ l →
      (∀ e ∈ l, ∀ s : String, e.1 = .atom s → mapLookup fields (.atom s) = Option.none) →
      Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6» (D m) (fieldsTerm l) (tagField tag) tag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ e ∈ l, ∀ s : String, e.1 = .atom s → FSem den ntag nfields s (w (.atom s)) := by
  intro l
  induction l with
  | nil => intro _ _ _ _ e me; simp at me
  | cons x t ih =>
    intro Q hQ fresh run e me s es
    obtain ⟨k, f⟩ := x
    rw [Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6».eq_def] at run
    simp only [fieldsTerm_cons, Lynx.Except.andAlso_eq_true] at run
    have mem : (k, f) ∈ nfields := by rw [hQ]; simp
    obtain ⟨a, rfl⟩ := (snf.1 _ mem).1
    rcases List.mem_cons.mp me with rfl | me
    · simp only [Term.atom.injEq] at es
      subst es
      have wa := (fsem_default ops dops esem gt (fresh _ List.mem_cons_self _ rfl) _).mp (hw a)
      exact (fsem_lookup (lookup_of_mem snf mem rfl) _).mpr
        (recur_sound ops dops esem hm hS sf lineS a (tagFieldV_value ops gt) (snf.1 _ mem).2 ⟨fun s _ => hw s, hw.doms⟩
          wa nc run.1)
    · exact ih (Q ++ [(Term.atom a, f)]) (by rw [hQ]; simp) (fun e me => fresh e (List.mem_cons_of_mem _ me)) run.2 e me s es

/-- `map_line_fields_empty?/7` answers `true` only when every map of the line outside the remaining negations
holds at the walked keys what the negated literal allows. -/
theorem fields_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gt : TagV E tag) (gn : TagV E ntag)
    {negs : List Term} {fields : List (Term × Term)} (sf : FieldsV E fields)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    {nfields : List (Term × Term)} (snf : FieldsV E nfields) {w : MW V} (hw : MSem den tag fields w)
    (nc : ¬CovM den negs w) :
    ∀ N (P l₁ Q l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → fields = P ++ l₁ → nfields = Q ++ l₂ →
      (∀ a ∈ P ++ Q, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) →
      Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag ntag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ e ∈ l₁ ++ l₂, ∀ s : String, e.1 = Term.atom s → FSem den ntag nfields s (w (.atom s)) := by
  have d₁ := key_tag_field gt
  have d₂ := key_tag_field gn
  have recur := fun a {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) (wa : FieldSem den f₁ (w (.atom a))) r =>
    recur_sound ops dops esem hm hS sf lineS a h₁ h₂ (f₂ := f₂) ⟨fun s _ => hw s, hw.doms⟩ wa nc r
  -- lookups at a key of the walk in the walked sides and in the sides before it
  have lookPos : ∀ {P l₁ : List (Term × Term)} {a : String} {f : Term}, fields = P ++ l₁ → (Term.atom a, f) ∈ l₁ →
      mapLookup fields (.atom a) = some f := fun hP me => lookup_of_mem sf (e := (.atom _, _)) (by rw [hP]; simp [me]) rfl
  have lookNeg : ∀ {Q l₂ : List (Term × Term)} {a : String} {f : Term}, nfields = Q ++ l₂ → (Term.atom a, f) ∈ l₂ →
      mapLookup nfields (.atom a) = some f := fun hQ me => lookup_of_mem snf (e := (.atom _, _)) (by rw [hQ]; simp [me]) rfl
  have tails : ∀ P l₁ Q l₂, fields = P ++ l₁ → nfields = Q ++ l₂ →
      (∀ a ∈ P ++ Q, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) → (l₁ = [] ∨ l₂ = []) →
      Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag ntag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ e ∈ l₁ ++ l₂, ∀ s : String, e.1 = Term.atom s → FSem den ntag nfields s (w (.atom s)) := by
    intro P l₁ Q l₂ hP hQ below empty run
    have run' : Lynx.Except.andAlso
        (Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6» (D m) (fieldsTerm l₁) (tagField ntag) tag
          (fieldsTerm fields) (Term.list negs) (.map S))
        (Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6» (D m) (fieldsTerm l₂) (tagField tag) tag
          (fieldsTerm fields) (Term.list negs) (.map S)) Bool.true = .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
      rcases empty with rfl | rfl
      · cases l₂ <;> simpa [fieldsTerm, Term.list, d₁, d₂] using run
      · cases l₁ <;> simpa [fieldsTerm, Term.list, d₁, d₂] using run
    rw [Lynx.Except.andAlso_eq_true] at run'
    intro e me s es
    rcases List.mem_append.mp me with me | me
    · refine pos_sound ops dops esem hm hS gn sf lineS hw nc l₁ P hP (fun x mx s' es' => ?_) run'.1 e me s es
      rcases empty with rfl | rfl
      · simp at mx
      · rw [hQ]
        exact lookup_below fun y my => es' ▸ below y (by simp at my; simp [my]) x (by simp [mx])
    · refine neg_sound ops dops esem hm hS gt sf lineS snf hw nc l₂ Q hQ (fun x mx s' es' => ?_) run'.2 e me s es
      rcases empty with rfl | rfl
      · rw [hP]
        exact lookup_below fun y my => es' ▸ below y (by simp at my; simp [my]) x (by simp [mx])
      · simp at mx
  intro N
  induction N with
  | zero =>
    intro P l₁ Q l₂ size hP hQ below run
    exact tails P l₁ Q l₂ hP hQ below (Or.inl (List.eq_nil_of_length_eq_zero (by omega))) run
  | succ N ih =>
    intro P l₁ Q l₂ size hP hQ below run
    match l₁, l₂ with
    | [], l₂ => exact tails P [] Q l₂ hP hQ below (Or.inl rfl) run
    | x :: xs, [] => exact tails P _ Q [] hP hQ below (Or.inr rfl) run
    | (k₁, f₁) :: xs, (k₂, f₂) :: ys =>
      have m₁ : (k₁, f₁) ∈ fields := by rw [hP]; simp
      have m₂ : (k₂, f₂) ∈ nfields := by rw [hQ]; simp
      obtain ⟨a, rfl⟩ := (sf.1 _ m₁).1
      obtain ⟨b, rfl⟩ := (snf.1 _ m₂).1
      obtain ⟨t₁, o₁, rfl, ht₁⟩ := (sf.1 _ m₁).2
      obtain ⟨t₂, o₂, rfl, ht₂⟩ := (snf.1 _ m₂).2
      have fv₁ : FieldValue E (.tuple #[t₁, boolAtom o₁]) := ⟨t₁, o₁, rfl, ht₁⟩
      have fv₂ : FieldValue E (.tuple #[t₂, boolAtom o₂]) := ⟨t₂, o₂, rfl, ht₂⟩
      have s₁ : FieldsV E ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs) := by rw [hP] at sf; exact fieldsV_suffix sf
      have s₂ : FieldsV E ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys) := by rw [hQ] at snf; exact fieldsV_suffix snf
      have head₁ := fieldsV_head s₁
      have head₂ := fieldsV_head s₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · -- the key is only in the positive map
        have above : ∀ y ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp
          · exact cmp_lt_trans cmp (head₂ y my)
        have nnone : mapLookup nfields (.atom a) = Option.none := by
          rw [hQ, lookup_append, lookup_below fun e me => below e (by simp [me])
            (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) (by simp), lookup_above above]; rfl
        have below' : ∀ x ∈ (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])]) ++ Q, ∀ y ∈ xs ++ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys,
            Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt := by
          intro x mx y my
          simp only [List.mem_append, List.mem_singleton] at mx
          rcases mx with (mx | rfl) | mx
          · exact below x (by simp [mx]) y (by simp at my ⊢; rcases my with my | my <;> simp [my])
          · rcases List.mem_append.mp my with my | my
            · exact head₁ y my
            · exact above y my
          · exact below x (by simp [mx]) y (by simp at my ⊢; rcases my with my | my <;> simp [my])
        have rest := fun r => ih (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])]) xs Q _ (by simp; omega)
          (by rw [hP]; simp) hQ below' r
        have finish : (FSem den ntag nfields a (w (.atom a))) →
            Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm xs)
              (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag ntag (fieldsTerm fields) (Term.list negs)
              (.map S) = .ok (.atom "true") →
            ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys,
              ∀ s : String, e.1 = .atom s → FSem den ntag nfields s (w (.atom s)) := by
          intro ha r e me s es
          rcases List.mem_cons.mp me with rfl | me
          · simp only [Term.atom.injEq] at es; subst es; exact ha
          · exact rest r e me s es
        have wa := (fsem_lookup (lookPos hP (List.mem_cons_self)) _).mp (hw a)
        by_cases no : ntag = .atom "open"
        · subst no
          rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp] at run
          exact finish (by simp only [FSem, nnone]; exact Or.inl rfl) run
        by_cases nc' : ntag = .atom "closed"
        · subst nc'
          cases o₁
          · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«not/1»] at run
          · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
              Erlang.erlang.«not/1», d₂] at run
            exact finish ((fsem_default ops dops esem gn nnone _).mpr
              (recur a fv₁ (tagFieldV_value ops gn) wa run.1)) run.2
        · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, tag_eq_false no,
            tag_eq_false nc', d₂] at run
          exact finish ((fsem_default ops dops esem gn nnone _).mpr
            (recur a fv₁ (tagFieldV_value ops gn) wa run.1)) run.2
      · -- the key is in both maps
        have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»] at run
        have wa := (fsem_lookup (lookPos hP (List.mem_cons_self (a := (Term.atom a, Term.tuple #[t₁, boolAtom o₁])))) _).mp
          (hw a)
        have ha := (fsem_lookup (tag := ntag) (lookNeg hQ (List.mem_cons_self (a := (Term.atom a, Term.tuple #[t₂, boolAtom o₂])))) _).mpr
          (recur a fv₁ fv₂ wa run.1)
        have below' : ∀ x ∈ (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])]) ++ (Q ++ [(Term.atom a, Term.tuple #[t₂, boolAtom o₂])]),
            ∀ y ∈ xs ++ ys, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt := by
          intro x mx y my
          simp only [List.mem_append, List.mem_singleton] at mx
          have hy : Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
            rcases List.mem_append.mp my with my | my
            · exact head₁ y my
            · exact head₂ y my
          rcases mx with (mx | rfl) | (mx | rfl)
          · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with my | my <;> simp [my])
          · exact hy
          · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with my | my <;> simp [my])
          · exact hy
        have rest := ih (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])]) xs (Q ++ [(Term.atom a, Term.tuple #[t₂, boolAtom o₂])]) ys
          (by omega) (by rw [hP]; simp) (by rw [hQ]; simp) below' run.2
        intro e me s es
        simp only [List.mem_append, List.mem_cons] at me
        rcases me with (rfl | me) | (rfl | me)
        · simp only [Term.atom.injEq] at es; subst es; exact ha
        · exact rest e (by simp [me]) s es
        · simp only [Term.atom.injEq] at es; subst es; exact ha
        · exact rest e (by simp [me]) s es
      · -- the key is only in the negative map
        have lt : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact lt
          · exact cmp_lt_trans lt (head₁ y my)
        have pnone : mapLookup fields (.atom b) = Option.none := by
          rw [hP, lookup_append, lookup_below fun e me => below e (by simp [me])
            (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) (by simp), lookup_above above]; rfl
        have below' : ∀ x ∈ P ++ (Q ++ [(Term.atom b, Term.tuple #[t₂, boolAtom o₂])]),
            ∀ y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++ ys, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt := by
          intro x mx y my
          have conv : y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys := by
            simp only [List.mem_append, List.mem_cons] at my ⊢
            rcases my with (my | my) | my
            · exact Or.inl (Or.inl my)
            · exact Or.inl (Or.inr my)
            · exact Or.inr (Or.inr my)
          simp only [List.mem_append, List.mem_singleton] at mx
          rcases mx with mx | (mx | rfl)
          · exact below x (by simp [mx]) y conv
          · exact below x (by simp [mx]) y conv
          · rcases List.mem_append.mp my with my | my
            · exact above y my
            · exact head₂ y my
        have rest := fun r => ih P _ (Q ++ [(Term.atom b, Term.tuple #[t₂, boolAtom o₂])]) ys (by simp; omega)
          hP (by rw [hQ]; simp) below' r
        have finish : FSem den ntag nfields b (w (.atom b)) →
            Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
              (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs)) (fieldsTerm ys) tag ntag (fieldsTerm fields)
              (Term.list negs) (.map S) = .ok (.atom "true") →
            ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys,
              ∀ s : String, e.1 = .atom s → FSem den ntag nfields s (w (.atom s)) := by
          intro hb r e me s es
          simp only [List.mem_append, List.mem_cons] at me
          rcases me with me | (rfl | me)
          · exact rest r e (by simp at me ⊢; rcases me with me | me <;> simp [me]) s es
          · simp only [Term.atom.injEq] at es; subst es; exact hb
          · exact rest r e (by simp [me]) s es
        have nb := lookNeg hQ (List.mem_cons_self (a := (Term.atom b, Term.tuple #[t₂, boolAtom o₂])))
        by_cases tc : tag = .atom "closed"
        · subst tc
          cases o₂
          · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2»,
              Erlang.erlang.«>/2», cmp, boolAtom, isMember] at run
          · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2»,
              Erlang.erlang.«>/2», cmp, boolAtom, isMember] at run
            have wb : w (.atom b) = Option.none := by
              have := hw b
              simp only [FSem, pnone, TagSem] at this
              rcases this with h | h
              · exact absurd h (by decide)
              · exact h
            exact finish ((fsem_lookup nb _).mpr (by rw [wb, fieldSem_mk]; exact Or.inl ⟨rfl, rfl⟩)) run
        · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            tag_eq_false tc, d₁] at run
          have wb := (fsem_default ops dops esem gt pnone _).mp (hw b)
          exact finish ((fsem_lookup nb _).mpr (recur b (tagFieldV_value ops gt) fv₂ wb run.1)) run.2

/-- When the walk is over, the maps of a line whose fields are within those of the negated literal, at the keys of
the line and of the literal, are in the literal. -/
theorem meet_base {tag ntag : Term} (tagOk : tag = .atom "closed" ∨ ntag = .atom "open")
    (nfields pre acc : List (Term × Term)) (hpre : nfields = pre) (sacc : FieldsV E acc.reverse)
    (accN : ∀ e ∈ acc, ∃ s : String, e.1 = .atom s ∧ ∀ o, FieldSem den e.2 o → FSem den ntag nfields s o)
    (preIn : ∀ e ∈ pre, ∃ e' ∈ acc, e.1 = e'.1) :
    ∀ w, MSem den tag acc.reverse w → MSem den ntag nfields w := by
  intro w hw
  refine ⟨fun s => ?_, fun k i => ?_⟩
  rotate_left
  · rcases tagOk with rfl | rfl
    · exact (hw.doms k i).resolve_left (by decide) ▸ tagSem_none _ _
    · exact Or.inl rfl
  by_cases hs : ∃ e ∈ acc, e.1 = .atom s
  · obtain ⟨e, me, es⟩ := hs
    have look := lookup_of_mem sacc (List.mem_reverse.mpr me) es
    have := hw s
    unfold FSem at this
    rw [look] at this
    obtain ⟨s', es', ok⟩ := accN e me
    rw [es] at es'
    simp only [Term.atom.injEq] at es'
    subst es'
    exact ok _ this
  · have none₁ : mapLookup acc.reverse (.atom s) = Option.none :=
      lookup_none fun e me eq => hs ⟨e, List.mem_reverse.mp me, eq⟩
    have none₂ : mapLookup nfields (.atom s) = Option.none := by
      refine lookup_none fun e me eq => hs ?_
      rw [hpre] at me
      obtain ⟨e', me', ee⟩ := preIn e me
      exact ⟨e', me', ee ▸ eq⟩
    have := hw s
    simp only [FSem, none₁] at this
    simp only [FSem, none₂]
    rcases tagOk with rfl | rfl
    · exact (this.resolve_left (by decide)) ▸ tagSem_none _ _
    · exact Or.inl rfl

/-- The meet walk over the aligned entries `es`, read from a `true` answer from any fields `acc` already met within the
negated literal: every map of the line of those and of the positive fields `l₁` left is in the literal or covered by
the other negations. The negated fields `pre` already walked have keys in `acc`. -/
def MeetSound (E : Term → Prop) (den : Term → V → Prop) (m : Nat) (S : List (Term × Term)) (tag ntag : Term)
    (nfields : List (Term × Term)) (negs : List Term) (es : List Entry) (pre l₁ l₂ : List (Term × Term)) : Prop :=
  ∀ acc : List (Term × Term), FieldsV E (acc.reverse ++ l₁) →
    (∀ x ∈ pre ++ acc, ∀ y ∈ l₁ ++ l₂, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt) →
    (∀ e ∈ acc, ∃ s : String, e.1 = .atom s ∧ ∀ o, FieldSem den e.2 o → FSem den ntag nfields s o) →
    (∀ e ∈ pre, ∃ e' ∈ acc, e.1 = e'.1) →
    Elixir.Module.Types.Descr.«map_line_meet_empty?/5» (D m) (entriesTerm es) tag (fieldsTerm acc)
      (Term.list negs) (.map S) = .ok (.atom "true") →
    ∀ w, MSem den tag (acc.reverse ++ l₁) w → MSem den ntag nfields w ∨ CovM den negs w

theorem meetS_nil {m : Nat} {S : List (Term × Term)} {tag ntag : Term} (tagOk : tag = .atom "closed" ∨ ntag = .atom "open")
    {nfields : List (Term × Term)} {negs : List Term} {pre : List (Term × Term)} (hpre : nfields = pre) :
    MeetSound E den m S tag ntag nfields negs [] pre [] [] := fun acc sacc _ accN preIn _ w hw =>
  Or.inl (meet_base tagOk nfields pre acc hpre (by simpa using sacc) accN preIn w (by simpa using hw))

/-- An entry for a key of the line, with the field `f₂` the negated literal allows there. -/
theorem meetS_pos (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    {S : List (Term × Term)} (hS : Safe S) (tag ntag : Term) (nfields : List (Term × Term)) (negs : List Term)
    (lineT : ∀ l, FieldsV E l → ∃ b : Bool, Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
      (Term.list negs) (.map S) = .ok (boolAtom b))
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    (a : String) (f₁ f₂ : Term) (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) (xs : List (Term × Term))
    (es : List Entry) (pre pre' l₂ l₂' : List (Term × Term))
    (neg : ∀ o, FieldSem den f₂ o → FSem den ntag nfields a o)
    (hpre' : ∀ x ∈ pre', x ∈ pre ∨ x.1 = .atom a) (sub : ∀ y ∈ l₂', y ∈ l₂)
    (above : ∀ y ∈ xs ++ l₂', Term.compare (Term.fuel (Term.atom a) y.1) (Term.atom a) y.1 = .lt)
    (rec : MeetSound E den m S tag ntag nfields negs es pre' xs l₂') :
    MeetSound E den m S tag ntag nfields negs ((.atom a, f₁, some f₂, xs) :: es) pre ((.atom a, f₁) :: xs) l₂ := by
  intro acc sacc below accN preIn run
  have memY : ∀ y ∈ xs ++ l₂', y ∈ (Term.atom a, f₁) :: xs ++ l₂ := fun y my => by
    simp only [List.mem_append, List.mem_cons] at my ⊢
    rcases my with my | my
    · exact Or.inl (Or.inr my)
    · exact Or.inr (sub y my)
  have fresh : mapLookup acc.reverse (.atom a) = Option.none :=
    lookup_below fun x mx => below x (by simp [List.mem_reverse.mp mx]) (Term.atom a, f₁) (by simp)
  refine meet_step_sound ops dops esem hm hS tag negs a f₁ f₂ h₁ h₂ xs acc es sacc fresh lineT lineS
    (fun f hf sem r w hw => ?_) run
  refine rec ((.atom a, f) :: acc) (by simpa using fieldsV_mid sacc hf) (fun x mx y my => ?_) (fun e me => ?_)
    (fun e me => ?_) r w (by simpa using hw)
  · simp only [List.mem_append, List.mem_cons] at mx
    rcases mx with mx | rfl | mx
    · rcases hpre' x mx with mx | ka
      · exact below x (by simp [mx]) y (memY y my)
      · rw [ka]; exact above y my
    · exact above y my
    · exact below x (by simp [mx]) y (memY y my)
  · rcases List.mem_cons.mp me with rfl | me
    · exact ⟨a, rfl, fun o ho => neg o (sem o ho).2⟩
    · exact accN e me
  · rcases hpre' e me with me | ka
    · obtain ⟨e', me', ee⟩ := preIn e me
      exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
    · exact ⟨_, List.mem_cons_self, ka⟩

/-- An entry for a key only the negated literal has, where the line has the default field of its tag. -/
theorem meetS_neg (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    {S : List (Term × Term)} (hS : Safe S) (tag ntag : Term) (gt : TagV E tag) (nfields : List (Term × Term))
    (negs : List Term)
    (lineT : ∀ l, FieldsV E l → ∃ b : Bool, Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
      (Term.list negs) (.map S) = .ok (boolAtom b))
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    (b : String) (f₂ : Term) (h₂ : FieldValue E f₂) (l₁ ys : List (Term × Term)) (es : List Entry)
    (pre : List (Term × Term)) (neg : ∀ o, FieldSem den f₂ o → FSem den ntag nfields b o)
    (above : ∀ y ∈ l₁ ++ ys, Term.compare (Term.fuel (Term.atom b) y.1) (Term.atom b) y.1 = .lt)
    (rec : MeetSound E den m S tag ntag nfields negs es (pre ++ [(Term.atom b, f₂)]) l₁ ys) :
    MeetSound E den m S tag ntag nfields negs ((.atom b, tagField tag, some f₂, l₁) :: es) pre l₁
      ((.atom b, f₂) :: ys) := by
  intro acc sacc below accN preIn run w hw
  have memY : ∀ y ∈ l₁ ++ ys, y ∈ l₁ ++ (Term.atom b, f₂) :: ys := fun y my => by
    simp only [List.mem_append, List.mem_cons] at my ⊢
    rcases my with my | my
    · exact Or.inl my
    · exact Or.inr (Or.inr my)
  have accLt : ∀ x ∈ acc.reverse, Term.compare (Term.fuel x.1 (.atom b)) x.1 (.atom b) = .lt :=
    fun x mx => below x (by simp [List.mem_reverse.mp mx]) (Term.atom b, f₂) (by simp)
  have fresh : mapLookup acc.reverse (.atom b) = Option.none := lookup_below accLt
  have none₁ : mapLookup l₁ (.atom b) = Option.none := lookup_above fun y my => above y (List.mem_append_left _ my)
  have sorted : FieldsV E (acc.reverse ++ (Term.atom b, tagField tag) :: l₁) :=
    fieldsV_insert sacc accLt (fun y my => above y (List.mem_append_left _ my)) ⟨b, rfl⟩ (tagFieldV_value ops gt)
  refine meet_step_sound ops dops esem hm hS tag negs b (tagField tag) f₂ (tagFieldV_value ops gt) h₂ l₁ acc es sorted
    fresh lineT lineS (fun f hf sem r w hw => ?_) run w ((msem_defaultV ops dops esem gt none₁ w).mpr hw)
  refine rec ((.atom b, f) :: acc) (by simpa using fieldsV_mid sorted hf) (fun x mx y my => ?_) (fun e me => ?_)
    (fun e me => ?_) r w (by simpa using hw)
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mx
    rcases mx with (mx | rfl) | rfl | mx
    · exact below x (by simp [mx]) y (memY y my)
    · exact above y my
    · exact above y my
    · exact below x (by simp [mx]) y (memY y my)
  · rcases List.mem_cons.mp me with rfl | me
    · exact ⟨b, rfl, fun o ho => neg o (sem o ho).2⟩
    · exact accN e me
  · rcases List.mem_append.mp me with me | me
    · obtain ⟨e', me', ee⟩ := preIn e me
      exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
    · simp at me; subst me; exact ⟨_, List.mem_cons_self, rfl⟩

/-- An entry for a key of the line that the open negated literal covers. -/
theorem meetS_cov {m : Nat} {S : List (Term × Term)} (tag : Term) (nfields : List (Term × Term)) (negs : List Term)
    (a : String) (f₁ : Term) (xs : List (Term × Term)) (es : List Entry) (pre l₂ : List (Term × Term))
    (nnone : mapLookup nfields (.atom a) = Option.none)
    (above : ∀ y ∈ xs ++ l₂, Term.compare (Term.fuel (Term.atom a) y.1) (Term.atom a) y.1 = .lt)
    (rec : MeetSound E den m S tag (.atom "open") nfields negs es pre xs l₂) :
    MeetSound E den m S tag (.atom "open") nfields negs ((.atom a, f₁, Option.none, xs) :: es) pre
      ((.atom a, f₁) :: xs) l₂ := by
  intro acc sacc below accN preIn run w hw
  rw [meet_covered] at run
  refine rec ((.atom a, f₁) :: acc) (by simpa using sacc) (fun x mx y my => ?_) (fun e me => ?_) (fun e me => ?_) run w
    (by simpa using hw)
  · have memY : y ∈ (Term.atom a, f₁) :: xs ++ l₂ := by
      simp only [List.mem_append, List.mem_cons] at my ⊢
      rcases my with my | my
      · exact Or.inl (Or.inr my)
      · exact Or.inr my
    simp only [List.mem_append, List.mem_cons] at mx
    rcases mx with mx | rfl | mx
    · exact below x (by simp [mx]) y memY
    · exact above y my
    · exact below x (by simp [mx]) y memY
  · rcases List.mem_cons.mp me with rfl | me
    · exact ⟨a, rfl, fun o _ => by simp only [FSem, nnone]; exact Or.inl rfl⟩
    · exact accN e me
  · obtain ⟨e', me', ee⟩ := preIn e me
    exact ⟨e', List.mem_cons_of_mem _ me', ee⟩

/-- `map_line_disjoint/9` finds the fields disjoint, or carries on with their entry. -/
theorem align_field_total (jops : ElemDisj E K) {m : Nat} (hm : K + 3 ≤ m) {S : List (Term × Term)}
    {tag ntag : Term} (key : Term) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂)
    (t₁ : List (Term × Term)) (t₂ : Term) (acc : List Entry) :
    Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) key f₁ f₂ (fieldsTerm t₁) t₂ tag ntag (entriesTerm acc)
        (.map S) = .ok (.atom "disjoint") ∨
      Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) key f₁ f₂ (fieldsTerm t₁) t₂ tag ntag (entriesTerm acc)
        (.map S) = Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m) (fieldsTerm t₁) t₂ tag ntag
          (entriesTerm ((key, f₁, some f₂, t₁) :: acc)) (.map S) := by
  obtain ⟨ty, o₁, rfl, hty⟩ := h₁
  obtain ⟨nt, o₂, rfl, hnt⟩ := h₂
  obtain ⟨bd, hd⟩ := jops.disj hty hnt S
  have run := hd m hm
  rw [Elixir.Module.Types.Descr.«map_line_disjoint/9».eq_def]
  cases o₁ <;> cases o₂ <;> cases bd <;>
    simp [run, boolAtom, Lynx.Except.andAlso, isMember, entriesTerm_cons, entryTerm]

/-- `map_line_disjoint/6` finds the negated literal disjoint from the line, or aligns their fields into entries whose
meet walk, when it answers `true`, puts every map of the line in the literal or under the other negations. -/
theorem align_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    {m : Nat} (hm : K + 3 ≤ m) {S : List (Term × Term)} (hS : Safe S) (tag ntag : Term) (gt : TagV E tag)
    (gn : TagV E ntag) (tagOk : tag = .atom "closed" ∨ ntag = .atom "open") (negs : List Term)
    (lineT : ∀ l, FieldsV E l → ∃ b : Bool, Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
      (Term.list negs) (.map S) = .ok (boolAtom b))
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    (nfields : List (Term × Term)) (snf : FieldsV E nfields) :
    ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → FieldsV E l₁ →
    ∀ (pre : List (Term × Term)) (acc : List Entry), nfields = pre ++ l₂ →
      (∀ a ∈ pre, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) →
      Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag ntag
          (entriesTerm acc) (.map S) = .ok (.atom "disjoint") ∨
      ∃ es, Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag ntag
          (entriesTerm acc) (.map S) = .ok (entriesTerm (acc.reverse ++ es)) ∧
        MeetSound E den m S tag ntag nfields negs es pre l₁ l₂ := by
  have hm' : K ≤ m := by omega
  have fd₁ := tagFieldV_value ops gt
  have fd₂ := tagFieldV_value ops gn
  have run₁ := key_tag_field gt
  have run₂ := key_tag_field gn
  have done : ∀ acc : List Entry, Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m) (fieldsTerm [])
      (fieldsTerm []) tag ntag (entriesTerm acc) (.map S) = .ok (entriesTerm (acc.reverse ++ [])) := by
    intro acc
    rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
    simp [fieldsTerm, Term.list, entriesTerm]
    simpa [List.map_reverse] using reverse1_list (acc.map entryTerm)
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size _ pre acc hpre _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    exact Or.inr ⟨[], done acc, meetS_nil tagOk (by simpa using hpre)⟩
  | succ N ih =>
    intro l₁ l₂ size s₁ pre acc hpre below
    have s₂ : FieldsV E l₂ := by rw [hpre] at snf; exact fieldsV_suffix snf
    have lift : ∀ (e : Entry) {pre' l₁' l₂' : List (Term × Term)} {r : Except Exception Term},
        (∀ es, MeetSound E den m S tag ntag nfields negs es pre' l₁' l₂' →
          MeetSound E den m S tag ntag nfields negs (e :: es) pre l₁ l₂) →
        (r = .ok (.atom "disjoint") ∨ ∃ es, r = .ok (entriesTerm ((e :: acc).reverse ++ es)) ∧
            MeetSound E den m S tag ntag nfields negs es pre' l₁' l₂') →
        r = .ok (.atom "disjoint") ∨
          ∃ es, r = .ok (entriesTerm (acc.reverse ++ es)) ∧ MeetSound E den m S tag ntag nfields negs es pre l₁ l₂ := by
      intro e pre' l₁' l₂' r step h
      rcases h with h | ⟨es, hr, ok⟩
      · exact Or.inl h
      · exact Or.inr ⟨e :: es, by rw [hr]; simp, step es ok⟩
    have viaField : ∀ (key f₁ f₂ : Term) (pre' l₁' l₂' : List (Term × Term)), FieldValue E f₁ → FieldValue E f₂ →
        (∀ es, MeetSound E den m S tag ntag nfields negs es pre' l₁' l₂' →
          MeetSound E den m S tag ntag nfields negs ((key, f₁, some f₂, l₁') :: es) pre l₁ l₂) →
        (∀ acc' : List Entry,
          Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m) (fieldsTerm l₁') (fieldsTerm l₂') tag ntag
              (entriesTerm acc') (.map S) = .ok (.atom "disjoint") ∨
          ∃ es, Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m) (fieldsTerm l₁') (fieldsTerm l₂') tag ntag
              (entriesTerm acc') (.map S) = .ok (entriesTerm (acc'.reverse ++ es)) ∧
            MeetSound E den m S tag ntag nfields negs es pre' l₁' l₂') →
        Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) key f₁ f₂ (fieldsTerm l₁') (fieldsTerm l₂') tag ntag
            (entriesTerm acc) (.map S) = .ok (.atom "disjoint") ∨
        ∃ es, Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) key f₁ f₂ (fieldsTerm l₁') (fieldsTerm l₂') tag
            ntag (entriesTerm acc) (.map S) = .ok (entriesTerm (acc.reverse ++ es)) ∧
          MeetSound E den m S tag ntag nfields negs es pre l₁ l₂ := by
      intro key f₁ f₂ pre' l₁' l₂' h₁ h₂ step next
      rcases align_field_total jops hm key h₁ h₂ l₁' (fieldsTerm l₂') acc (S := S) (tag := tag) (ntag := ntag)
        with r | r
      · exact Or.inl r
      · rw [r]; exact lift _ step (next _)
    have key₁ : ∀ x ∈ l₁, ∃ a : String, x.1 = .atom a := fun x mx => (s₁.1 x mx).1
    have key₂ : ∀ x ∈ l₂, ∃ a : String, x.1 = .atom a := fun x mx => (s₂.1 x mx).1
    -- what the negated literal allows at a key only the line has
    have negDefault : ∀ (a : String), (∀ x ∈ pre, Term.compare (Term.fuel x.1 (.atom a)) x.1 (.atom a) = .lt) →
        (∀ y ∈ l₂, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt) →
        mapLookup nfields (.atom a) = Option.none := by
      intro a hpre' hl₂
      rw [hpre, lookup_append, lookup_below hpre', lookup_above hl₂]; rfl
    -- what the negated literal allows at a key of its own
    have negOwn : ∀ (b : String) (f₂ : Term) (ys : List (Term × Term)), l₂ = (.atom b, f₂) :: ys →
        mapLookup nfields (.atom b) = some f₂ := by
      intro b f₂ ys e
      have mem₂ : (Term.atom b, f₂) ∈ l₁ ++ l₂ := by simp [e]
      rw [hpre, e]; exact lookup_head (lookup_below fun x mx => below x mx _ mem₂)
    cases l₁ with
    | nil =>
      cases l₂ with
      | nil => exact Or.inr ⟨[], done acc, meetS_nil tagOk (by simpa using hpre)⟩
      | cons y ys =>
        obtain ⟨k₂, f₂⟩ := y
        obtain ⟨b, rfl⟩ := key₂ _ List.mem_cons_self
        have h₂ := (s₂.1 _ List.mem_cons_self).2
        have e : Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m) (fieldsTerm [])
            (fieldsTerm ((.atom b, f₂) :: ys)) tag ntag (entriesTerm acc) (.map S) =
            Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) (.atom b) (tagField tag) f₂ (fieldsTerm [])
              (fieldsTerm ys) tag ntag (entriesTerm acc) (.map S) := by
          rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
          simp [fieldsTerm, Term.list, run₁]
        rw [e]
        have nsome := negOwn b f₂ ys rfl
        exact viaField _ _ _ (pre ++ [(Term.atom b, f₂)]) [] ys fd₁ h₂
          (fun es ok => meetS_neg ops dops esem hm' hS tag ntag gt nfields negs lineT lineS b f₂ h₂ [] ys es pre
            (fun o ho => (fsem_lookup nsome o).mpr ho) (fun y my => fieldsV_head s₂ y (by simpa using my)) ok)
          fun acc' => ih [] ys (by simp at size ⊢; omega) (by simpa using s₁) (pre ++ [(Term.atom b, f₂)]) acc'
            (by rw [hpre]; simp) (fun x mx y my => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.nil_append] at mx my
              rcases mx with mx | rfl
              · exact below x mx y (by simp [my])
              · exact fieldsV_head s₂ y my)
    | cons x xs =>
      obtain ⟨k₁, f₁⟩ := x
      obtain ⟨a, rfl⟩ := key₁ _ List.mem_cons_self
      have h₁ := (s₁.1 _ List.mem_cons_self).2
      have head₁ := fieldsV_head s₁
      have sxs := fieldsV_tail s₁
      cases l₂ with
      | nil =>
        have e : Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m) (fieldsTerm ((.atom a, f₁) :: xs))
            (fieldsTerm []) tag ntag (entriesTerm acc) (.map S) =
            Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) (.atom a) f₁ (tagField ntag) (fieldsTerm xs)
              (fieldsTerm []) tag ntag (entriesTerm acc) (.map S) := by
          rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
          simp [fieldsTerm, Term.list, run₂]
        rw [e]
        have nnone := negDefault a (fun x mx => below x mx (Term.atom a, f₁) (by simp)) (by simp)
        exact viaField _ _ _ pre xs [] h₁ fd₂
          (fun es ok => meetS_pos ops dops esem hm' hS tag ntag nfields negs lineT lineS a f₁ (tagField ntag) h₁ fd₂
            xs es pre pre [] [] (fun o ho => (fsem_default ops dops esem gn nnone o).mpr ho) (fun x mx => Or.inl mx)
            (fun _ h => h) (fun y my => head₁ y (by simpa using my)) ok)
          fun acc' => ih xs [] (by simp at size ⊢; omega) sxs pre acc' (by simpa using hpre)
            (fun x mx y my => below x mx y (by simp at my ⊢; simp [my]))
      | cons y ys =>
        obtain ⟨k₂, f₂⟩ := y
        obtain ⟨b, rfl⟩ := key₂ _ List.mem_cons_self
        have h₂ := (s₂.1 _ List.mem_cons_self).2
        have head₂ := fieldsV_head s₂
        obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
        obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
        have fv₁ : FieldValue E (.tuple #[t₁, boolAtom o₁]) := ⟨t₁, o₁, rfl, ht₁⟩
        have fv₂ : FieldValue E (.tuple #[t₂, boolAtom o₂]) := ⟨t₂, o₂, rfl, ht₂⟩
        simp only [List.length_cons] at size
        rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
        · -- the key is only in the line
          have above : ∀ y ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys,
              Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
            intro y my
            rcases List.mem_cons.mp my with rfl | my
            · exact cmp
            · exact cmp_lt_trans cmp (head₂ y my)
          have aboveAll : ∀ y ∈ xs ++ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys,
              Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := fun y my => by
            rcases List.mem_append.mp my with my | my
            · exact head₁ y my
            · exact above y my
          have next := fun acc' => ih xs ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys) (by simp; omega) sxs pre acc'
            hpre (fun x mx y my => below x mx y (by
              simp only [List.mem_append, List.mem_cons] at my ⊢
              rcases my with my | my
              · exact Or.inl (Or.inr my)
              · exact Or.inr my))
          have nnone := negDefault a (fun x mx => below x mx (Term.atom a, .tuple #[t₁, boolAtom o₁]) (by simp)) above
          by_cases no : ntag = .atom "open"
          · subst no
            have e : Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag (.atom "open") (entriesTerm acc)
                (.map S) =
                Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m) (fieldsTerm xs)
                  (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag (.atom "open")
                  (entriesTerm ((.atom a, .tuple #[t₁, boolAtom o₁], Option.none, xs) :: acc)) (.map S) := by
              rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, entriesTerm_cons,
                entryTerm]
            rw [e]
            exact lift _ (fun es ok => meetS_cov tag nfields negs a _ xs es pre _ nnone aboveAll ok) (next _)
          by_cases nc : ntag = .atom "closed"
          · subst nc
            cases o₁
            · refine Or.inl ?_
              rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
                Lynx.Except.andAlso, Erlang.erlang.«not/1»]
            · have e : Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m)
                  (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom Bool.true]) :: xs))
                  (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag (.atom "closed") (entriesTerm acc)
                  (.map S) =
                  Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) (.atom a) (.tuple #[t₁, boolAtom Bool.true])
                    (tagField (.atom "closed")) (fieldsTerm xs) (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys))
                    tag (.atom "closed") (entriesTerm acc) (.map S) := by
                rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
                simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
                  Lynx.Except.andAlso, Erlang.erlang.«not/1», run₂]
              rw [e]
              exact viaField _ _ _ pre xs _ fv₁ fd₂
                (fun es ok => meetS_pos ops dops esem hm' hS tag _ nfields negs lineT lineS a _ _ fv₁ fd₂ xs es pre pre _ _
                  (fun o ho => (fsem_default ops dops esem gn nnone o).mpr ho) (fun x mx => Or.inl mx) (fun _ h => h)
                  aboveAll ok) next
          · have e : Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag ntag (entriesTerm acc) (.map S) =
                Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) (.atom a) (.tuple #[t₁, boolAtom o₁])
                  (tagField ntag) (fieldsTerm xs) (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys))
                  tag ntag (entriesTerm acc) (.map S) := by
              rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, tag_eq_false no, tag_eq_false nc,
                Lynx.Except.andAlso, run₂]
            rw [e]
            exact viaField _ _ _ pre xs _ fv₁ fd₂
              (fun es ok => meetS_pos ops dops esem hm' hS tag ntag nfields negs lineT lineS a _ _ fv₁ fd₂ xs es pre pre _ _
                (fun o ho => (fsem_default ops dops esem gn nnone o).mpr ho) (fun x mx => Or.inl mx) (fun _ h => h)
                aboveAll ok) next
        · -- the key is in both
          have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
          subst ab
          have above : ∀ y ∈ xs ++ ys, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
            intro y my
            rcases List.mem_append.mp my with my | my
            · exact head₁ y my
            · exact head₂ y my
          have e : Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m)
              (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
              (fieldsTerm ((.atom a, .tuple #[t₂, boolAtom o₂]) :: ys)) tag ntag (entriesTerm acc) (.map S) =
              Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) (.atom a) (.tuple #[t₁, boolAtom o₁])
                (.tuple #[t₂, boolAtom o₂]) (fieldsTerm xs) (fieldsTerm ys) tag ntag (entriesTerm acc) (.map S) := by
            rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
          rw [e]
          have nsome := negOwn a _ ys rfl
          exact viaField _ _ _ (pre ++ [(Term.atom a, .tuple #[t₂, boolAtom o₂])]) xs ys fv₁ fv₂
            (fun es ok => meetS_pos ops dops esem hm' hS tag ntag nfields negs lineT lineS a _ _ fv₁ fv₂ xs es pre _ _ ys
              (fun o ho => (fsem_lookup nsome o).mpr ho)
              (fun x mx => by
                rcases List.mem_append.mp mx with mx | mx
                · exact Or.inl mx
                · simp at mx; subst mx; exact Or.inr rfl)
              (fun y my => List.mem_cons_of_mem _ my) above ok)
            fun acc' => ih xs ys (by omega) sxs (pre ++ [(Term.atom a, .tuple #[t₂, boolAtom o₂])]) acc'
              (by rw [hpre]; simp) (fun x mx y my => by
                have hy : y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++
                    (Term.atom a, Term.tuple #[t₂, boolAtom o₂]) :: ys := by
                  rcases List.mem_append.mp my with my | my <;> simp [my]
                rcases List.mem_append.mp mx with mx | mx
                · exact below x mx y hy
                · simp at mx; subst mx; exact above y my)
        · -- the key is only in the negated literal
          have lt : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt :=
            Lynx.Term.compare_gt_iff_lt.mp cmp
          have above : ∀ y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs,
              Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
            intro y my
            rcases List.mem_cons.mp my with rfl | my
            · exact lt
            · exact cmp_lt_trans lt (head₁ y my)
          have nsome := negOwn b _ ys rfl
          have next := fun acc' => ih ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs) ys (by simp; omega) s₁
            (pre ++ [(Term.atom b, .tuple #[t₂, boolAtom o₂])]) acc' (by rw [hpre]; simp)
            (fun x mx y my => by
              rcases List.mem_append.mp mx with mx | mx
              · refine below x mx y ?_
                simp only [List.mem_append, List.mem_cons] at my ⊢
                rcases my with my | my
                · exact Or.inl my
                · exact Or.inr (Or.inr my)
              · simp at mx; subst mx
                rcases List.mem_append.mp my with my | my
                · exact above y my
                · exact head₂ y my)
          have step : ∀ es, MeetSound E den m S tag ntag nfields negs es
                (pre ++ [(Term.atom b, .tuple #[t₂, boolAtom o₂])]) ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs) ys →
              MeetSound E den m S tag ntag nfields negs
                ((.atom b, tagField tag, some (.tuple #[t₂, boolAtom o₂]), (.atom a, .tuple #[t₁, boolAtom o₁]) :: xs) :: es)
                pre ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs) ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys) :=
            fun es ok => meetS_neg ops dops esem hm' hS tag ntag gt nfields negs lineT lineS b _ fv₂ _ ys es pre
              (fun o ho => (fsem_lookup nsome o).mpr ho)
              (fun y my => by
                rcases List.mem_append.mp my with my | my
                · exact above y my
                · exact head₂ y my) ok
          by_cases tc : tag = .atom "closed"
          · subst tc
            cases o₂
            · refine Or.inl ?_
              rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
                boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
            · have e : Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m)
                  (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                  (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom Bool.true]) :: ys)) (.atom "closed") ntag
                  (entriesTerm acc) (.map S) =
                  Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) (.atom b) (tagField (.atom "closed"))
                    (.tuple #[t₂, boolAtom Bool.true]) (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                    (fieldsTerm ys) (.atom "closed") ntag (entriesTerm acc) (.map S) := by
                rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
                simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
                  boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1», run₁]
              rw [e]
              exact viaField _ _ _ _ _ ys fd₁ fv₂ step next
          · have e : Elixir.Module.Types.Descr.«map_line_disjoint/6» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag ntag (entriesTerm acc) (.map S) =
                Elixir.Module.Types.Descr.«map_line_disjoint/9» (D m) (.atom b) (tagField tag)
                  (.tuple #[t₂, boolAtom o₂]) (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                  (fieldsTerm ys) tag ntag (entriesTerm acc) (.map S) := by
              rw [Elixir.Module.Types.Descr.«map_line_disjoint/6».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, tag_eq_false tc,
                Lynx.Except.andAlso, run₁]
            rw [e]
            exact viaField _ _ _ _ _ ys fd₁ fv₂ step next

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

theorem domKind_mem (k : Fin 11) : domKind k ∈ domainKinds := by
  revert k; decide

/-- `map_line_empty?/4` answers `true` only when its negations cover every map of the line. -/
theorem line_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    {m : Nat} (hm : K + 3 ≤ m) {S : List (Term × Term)} (hS : Safe S) :
    ∀ negs : List Term, (∀ t ∈ negs, MapLitV E t) → ∀ tag : Term, TagV E tag →
      ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
        (Term.list negs) (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w := by
  intro negs
  induction negs with
  | nil =>
    intro _ tag _ l _ run
    rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def] at run
    simp at run
  | cons N rest ih =>
    intro lits tag gt l sl run w hw
    obtain ⟨k, ntag, nl, rfl, gn, snl⟩ := lits _ List.mem_cons_self
    have lits' : ∀ t ∈ rest, MapLitV E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    have later : CovM den rest w → CovM den (.tuple #[.integer k, ntag, fieldsTerm nl] :: rest) w :=
      fun ⟨N, mN, hN⟩ => ⟨N, List.mem_cons_of_mem _ mN, hN⟩
    by_cases top : ntag = .atom "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      exact ⟨_, List.mem_cons_self, nsem_lit.mpr ⟨fun s => fsem_nil.mpr (Or.inl rfl), fun k i => Or.inl rfl⟩⟩
    by_cases skip : tag = .atom "open" ∧ ntag = .atom "closed"
    · obtain ⟨rfl, rfl⟩ := skip
      rw [list_cons, Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def] at run
      exact later (ih lits' _ gt l sl (by simpa using run) w hw)
    by_cases cov : CovM den rest w
    · exact later cov
    have lineS := fun l' (sl' : FieldsV E l') r w' (hw' : MSem den tag l' w') => ih lits' tag gt l' sl' r w' hw'
    have hl : ∀ e ∈ l, FieldValue E e.2 := fun e me => (sl.1 e me).2
    have hnl : ∀ e ∈ nl, FieldValue E e.2 := fun e me => (snl.1 e me).2
    have ih' := map_line_total ops dops jops S rest fun t mt => (lits' t mt).plain
    have ops' := ops.mono (Nat.le_add_right K 3)
    have dops' := dops.mono (Nat.le_add_right K 3)
    have lineT : ∀ l', FieldsV E l' → ∃ b : Bool, Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag
        (fieldsTerm l') (Term.list rest) (.map S) = .ok (boolAtom b) := fun l' sl' => by
      obtain ⟨b, hb⟩ := ih' tag gt.plain l' fun e me => (sl'.1 e me).2
      exact ⟨b, hb m hm⟩
    obtain ⟨bc, runc, incl⟩ := check_val ops dops esem (m := m) (by omega) hS gt gn skip
    obtain ⟨c, hor, hc⟩ := walk_choice (tag := tag) (ntag := ntag)
    obtain ⟨bk, hk⟩ := ih' tag gt.plain l hl
    have hk' := hk m hm
    dsimp only at hk'
    -- the remaining negations answer `false`, as they do not cover the map
    have nk : bk = Bool.false := by
      cases bk
      · rfl
      · exact absurd (lineS l sl (by simpa [boolAtom] using hk') w hw) cov
    subst nk
    -- so the negated literal holds the map
    refine ⟨_, List.mem_cons_self, ?_⟩
    have falseRun : ∀ (hf : bc = Bool.false → Bool.false = Bool.false) ht hw',
        Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
          (Term.list (.tuple #[.integer k, ntag, fieldsTerm nl] :: rest)) (.map S) = .ok (boolAtom Bool.false) :=
      fun hf ht hw' => line_general top skip runc hor hk' hf ht hw'
    cases bc
    · rw [falseRun (fun _ => rfl) (fun h => nomatch h) (fun h => nomatch h)] at run
      simp [boolAtom] at run
    cases c
    · rcases fields_total ops' dops' S gt.plain gn.plain (Term.list rest) l hl (fun l' hl' => ih' tag gt.plain l' hl') _ l
          nl (Nat.le_refl _) hl hnl with ⟨b, hb⟩ | hb
      · have r := line_general (k := k) (b := b) top skip runc hor hk' (fun h => nomatch h) (fun _ h => nomatch h)
          (fun _ _ => Or.inl (hb m hm))
        rw [r] at run
        cases b
        · simp [boolAtom] at run
        have walk : Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l) (fieldsTerm nl) tag ntag
            (fieldsTerm l) (Term.list rest) (.map S) = .ok (.atom "true") := by simpa [boolAtom] using hb m hm
        have keys := fields_sound ops dops esem (by omega) hS gt gn sl lineS snl hw cov _ [] l [] nl (Nat.le_refl _)
          (by simp) (by simp) (by simp) walk
        have tin := incl.mp rfl
        refine nsem_lit.mpr ⟨fun s => ?_, fun k i => tin _ (domKind_mem k) _ (hw.doms k i)⟩
        by_cases hs : ∃ e ∈ l ++ nl, e.1 = Term.atom s
        · obtain ⟨e, me, es⟩ := hs
          exact keys e me s es
        · have n₁ : mapLookup l (.atom s) = Option.none := lookup_none fun e me eq => hs ⟨e, by simp [me], eq⟩
          have n₂ : mapLookup nl (.atom s) = Option.none := lookup_none fun e me eq => hs ⟨e, by simp [me], eq⟩
          have := hw s
          simp only [FSem, n₁] at this
          simp only [FSem, n₂]
          exact tin "atom" (by simp [domainKinds]) _ this
      · rw [falseRun (fun _ => rfl) (fun _ h => nomatch h) (fun _ _ => Or.inr ⟨hb m hm, rfl⟩)] at run
        simp [boolAtom] at run
    · have tagOk := hc.mp rfl
      rcases disjoint_total ops jops S gt.plain gn.plain _ l nl (Nat.le_refl _) hl hnl [] (by simp) with dis | ⟨es, hes, r6⟩
      · rw [falseRun (fun _ => rfl) (fun _ _ => ⟨_, by simpa [entriesTerm] using dis m hm, Or.inl ⟨rfl, rfl⟩⟩)
          (fun _ h => nomatch h)] at run
        simp [boolAtom] at run
      obtain ⟨b5, h5⟩ := meet5_total ops' dops' S tag (Term.list rest) (fun l' hl' => ih' tag gt.plain l' hl') es hes []
        (by simp)
      have r := line_general (k := k) (b := b5) top skip runc hor hk' (fun h => nomatch h)
        (fun _ _ => ⟨_, by simpa [entriesTerm] using r6 m hm, Or.inr ⟨es, rfl, by simpa [fieldsTerm] using h5 m hm⟩⟩)
        (fun _ h => nomatch h)
      rw [r] at run
      cases b5
      · simp [boolAtom] at run
      have meetRun := h5 m hm
      rcases align_sound ops dops esem jops hm hS tag ntag gt gn tagOk rest lineT lineS nl snl _ l nl (Nat.le_refl _) sl
          [] [] (by simp) (by simp) with dis | ⟨es', r6', ok⟩
      · have := (r6 m hm).symm.trans dis
        simp [entriesTerm] at this
        cases es <;> simp [Term.list] at this
      · have same : entriesTerm es = entriesTerm es' := by
          have := (r6 m hm).symm.trans r6'
          simpa using this
        rcases ok [] (by simpa using sl) (by simp) (by simp) (by simp)
            (by rw [← same]; simpa [fieldsTerm, boolAtom] using meetRun) w (by simpa using hw) with h | h
        · exact nsem_lit.mpr h
        · exact absurd h cov

/-- `init_map_line_empty?/4` answers `true` only when its negations cover every map of the line. -/
theorem init_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    {m : Nat} (hm : K + 4 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {tag : Term} (gt : TagV E tag) {l : List (Term × Term)}
    (sl : FieldsV E l) {negs : List Term} (lits : ∀ t ∈ negs, MapLitV E t)
    (run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true")) :
    ∀ w, MSem den tag l w → CovM den negs w := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show 1 ≤ m by omega)
  have each : ∀ x ∈ l.map (fun e => Term.tuple #[e.1, e.2]),
      Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2» (D n) (.map S) x = .ok (boolAtom (reqEmpty den x)) := by
    intro x mx
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
    obtain ⟨t, o, ho, ht⟩ := (sl.1 e me).2
    rw [ho]
    cases o
    · obtain ⟨b, hb⟩ := ops.empty ht S
      have run := hb n (by omega)
      have sem := esem.empty ht hS (by omega) run
      simp only [Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2», boolAtom, Bool.false_eq_true,
        ite_false, reqEmpty]
      rw [run]
      cases b <;> simp at sem <;> simp [sem, boolAtom]
    · simp [Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2», boolAtom, reqEmpty]
  have anyRun := any_list (D (n + 1)) _ _ _ (reqEmpty den) _ fun x mx => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-init_map_line_empty?/4-fun-0-/1».pure]
    exact each x mx
  rw [Elixir.Module.Types.Descr.«init_map_line_empty?/4».eq_def] at run
  simp only [fieldsTerm] at anyRun run
  simp only [pure_bind, anyRun] at run
  intro w hw
  cases hany : (l.map fun e => Term.tuple #[e.1, e.2]).any (reqEmpty den)
  · rw [hany] at run
    have := line_sound ops dops esem jops (show K + 3 ≤ n + 1 by omega) hS negs lits tag gt l sl
      (by simpa [boolAtom, Lynx.Except.orElse, fieldsTerm] using run) w hw
    exact this
  · exfalso
    obtain ⟨x, mx, rx⟩ := List.any_eq_true.mp hany
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
    obtain ⟨t, o, ho, ht⟩ := (sl.1 e me).2
    obtain ⟨s, es⟩ := (sl.1 e me).1
    have look := lookup_of_mem sl me es
    have := hw s
    unfold FSem at this
    rw [look, ho] at this
    simp only at this
    rw [fieldSem_mk] at this
    rw [ho] at rx
    cases o
    · simp [reqEmpty, boolAtom] at rx
      rcases this with ⟨-, h⟩ | ⟨y, -, hy⟩
      · cases h
      · exact rx y hy
    · simp [reqEmpty] at rx

/-- `map_bdd_empty?/4` answers `true` only when no map along the path, outside the negations, satisfies the BDD. -/
theorem map_bdd_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    {m : Nat} (hm : K + 4 ≤ m) (S : List (Term × Term)) (hS : Safe S) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → MapLitV E t) → ∀ pos negs, MapPosV E pos → (∀ t ∈ negs, MapLitV E t) →
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true") →
      ValUnsatM E den pos negs r := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLitV E t) → ∀ pos negs, MapPosV E pos →
    (∀ t ∈ negs, MapLitV E t) →
    Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true") →
    ValUnsatM E den pos negs r) ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits run w hw nn
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def] at run
    simp only at run
    obtain ⟨N, mN, hN⟩ := init_sound ops dops esem jops (by omega) hS gt sl lits run w (inPosM_iff.mp hw)
    exact (nn N mN hN).elim
  · intro ok _ pos negs _ _ _ w _ _
    rfl
  · intro ok k x y okl okLit pos negs hp lits run w hw nn
    have hl := okLit _ okl
    rw [eval_leaf]
    cases e : valM E den w (.tuple #[.integer k, x, y])
    · rfl
    exfalso
    have hlit := valM_lit ops dops esem hl e
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def] at run
    rcases inter_val ops dops esem (m := m) (by omega) hS hp hl with ⟨empty, disj⟩ | ⟨pos', r', hp', sem'⟩
    · exact disj w hw hlit
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp'
    simp [r'] at run
    obtain ⟨N, mN, hN⟩ := init_sound ops dops esem jops (by omega) hS gt sl lits run w
      (inPosM_iff.mp ((sem' w).mpr ⟨hw, hlit⟩))
    exact nn N mN hN
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits run w hw nn
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → MapLitV E t := fun t ht => okLit t ht.1
    have hp₀ := hp
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def] at run
    rcases inter_val ops dops esem (m := m) (by omega) hS hp₀ hl with ⟨empty, disj⟩ | ⟨pos2, r2, hp2, sem2⟩
    · simp only [empty, Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at run
      obtain ⟨⟨rd, -⟩, ru⟩ := run
      have nl : valM E den w lit = Bool.false := by
        cases e : valM E den w lit
        · rfl
        · exact (disj w hw (valM_lit ops dops esem hl e)).elim
      have ed := idd okLit' _ (lit :: negs) hp₀ (fun t mt => by
        rcases List.mem_cons.mp mt with rfl | mt
        · exact hl
        · exact lits t mt) (by rwa [list_cons]) w hw (fun N mN hN => by
          rcases List.mem_cons.mp mN with rfl | mN
          · rw [valM_true hl hN] at nl; cases nl
          · exact nn N mN hN)
      have eu := iu okLit' _ negs hp₀ lits ru w hw nn
      simp [eval_node, nl, ed, eu]
    · have hp2' := hp2
      obtain ⟨tag2, l2, rfl, -⟩ := hp2
      simp only [r2, Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at run
      obtain ⟨⟨rd, rc⟩, ru⟩ := run
      have eu := iu okLit' _ negs hp₀ lits ru w hw nn
      cases e : valM E den w lit
      · have ed := idd okLit' _ (lit :: negs) hp₀ (fun t mt => by
          rcases List.mem_cons.mp mt with rfl | mt
          · exact hl
          · exact lits t mt) (by rwa [list_cons]) w hw (fun N mN hN => by
            rcases List.mem_cons.mp mN with rfl | mN
            · rw [valM_true hl hN] at e; cases e
            · exact nn N mN hN)
        simp [eval_node, e, ed, eu]
      · have ec := ic okLit' _ negs hp2' lits rc w ((sem2 w).mpr ⟨hw, valM_lit ops dops esem hl e⟩) nn
        simp [eval_node, e, ec, eu]

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Map emptiness is exact under seen sets of higher BDDs. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem lh_pair (a b : Term) : lh (.tuple #[a, b]) = max (lh a) (lh b) := by
  show lh (.tuple ⟨[a, b]⟩) = _
  rw [lh]

theorem lh_fields_mem {l : List (Term × Term)} {e : Term × Term} (me : e ∈ l) {t : Term} {o : Bool}
    (he : e.2 = .tuple #[t, boolAtom o]) : lh t ≤ lh (fieldsTerm l) := by
  have := lh_list_mem (l := l.map fun e => .tuple #[e.1, e.2]) (List.mem_map.mpr ⟨e, me, rfl⟩)
  rw [he, lh_pair, lh_pair] at this
  exact Nat.le_trans (by omega) this

theorem lh_litM {k : Int} {tag : Term} {l : List (Term × Term)} (_g : TagV E tag)
    (top : ¬(tag = .atom "open" ∧ l = [])) :
    lh (.tuple #[.integer k, tag, fieldsTerm l]) = max (lh tag) (lh (fieldsTerm l)) + 1 :=
  lh_leaf _ _ _ (fun ⟨h₁, h₂⟩ => top ⟨h₁, fieldsTerm_eq_nil.mp h₂⟩)
    (fun ⟨_, _, h⟩ => fieldsTerm_ne_atom l "term" h)
    (by rintro ⟨-, r, a, b, h⟩; cases l <;> simp [fieldsTerm, Term.list] at h) (by simp)

/-- Map literals other than the top one are one higher than their parts. -/
theorem mlit_litZ {k a b : Term} (h : MLit E (.tuple #[k, a, b])) : litZ a b = Bool.false := by
  obtain ⟨⟨k', tag, l, e, g, -⟩, nt, -⟩ := h
  obtain ⟨-, rfl, rfl⟩ := tuple3_inj e
  unfold litZ
  split
  · rename_i r a b h; cases l <;> simp [fieldsTerm, Term.list] at h
  · rfl

theorem mlit_lh_eq {k a b : Term} (h : MLit E (.tuple #[k, a, b])) : lh (.tuple #[k, a, b]) = max (lh a) (lh b) + 1 := by
  obtain ⟨⟨k', tag, l, e, g, -⟩, nt, -⟩ := h
  obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
  have top : ¬(tag = .atom "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt ⟨_, by rw [e, h₁, h₂]; rfl⟩
  rw [e, lh_litM g top, ← e₂, ← e₃]

theorem mlit_lh {t : Term} (h : MLit E t) : 1 ≤ lh t ∧ ∀ (k : Int) (tag : Term) (l : List (Term × Term)),
    t = .tuple #[.integer k, tag, fieldsTerm l] →
      (∀ e ∈ l, ∀ u o, e.2 = .tuple #[u, boolAtom o] → lh u < lh t) ∧ ∀ e ∈ domFields tag, lh e.2 < lh t := by
  obtain ⟨⟨k, tag, l, rfl, g, sl⟩, nt, key⟩ := h
  have e₀ := mlit_lh_eq ⟨⟨k, tag, l, rfl, g, sl⟩, nt, key⟩
  refine ⟨by rw [e₀]; omega, fun k' tag' l' e => ?_⟩
  obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
  have := fieldsTerm_inj e₃
  subst this e₂
  refine ⟨fun x mx u o hx => ?_, fun x mx => ?_⟩
  · have := lh_fields_mem mx hx; rw [e₀]; omega
  · rcases g with rfl | rfl | ⟨dl, rfl, -⟩
    · simp [domFields] at mx
    · simp [domFields] at mx
    · rw [domFields_fieldsTerm] at mx
      have := lh_list_mem (l := dl.map fun e => .tuple #[e.1, e.2]) (List.mem_map.mpr ⟨x, mx, rfl⟩)
      rw [lh_pair] at this
      have le : lh x.2 ≤ lh (fieldsTerm dl) := Nat.le_trans (by omega) this
      rw [e₀]; omega

/-- Literals of map BDDs are no higher than the BDD. -/
theorem mbdd_lh_le {ok : Term → Prop} {x : Term} (wx : Bdd ok x) (lits : ∀ t, ok t → MLit E t) :
    ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x := by
  revert lits
  refine Bdd.induction (P := fun ok x => (∀ t, ok t → MLit E t) → ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x)
    ?_ ?_ ?_ ?_ ok x wx
  · intro _ _ _ _; exact Bdd.top
  · intro _ _ _ _; exact Bdd.bot
  · intro ok k x y okl _ M le
    exact Bdd.leaf_iff.mpr ⟨okl, le⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd lits M le
    obtain ⟨k, a, b, rfl⟩ := leaf
    have hl := mlit_lh_eq (lits _ okl)
    have nd := lh_node (.integer h) (.integer k) a b c u d (mlit_litZ (lits _ okl))
    change lh (.tuple ⟨[.integer h, .tuple ⟨[.integer k, a, b]⟩, c, u, d]⟩) ≤ M at le
    have hlit : lh (.tuple #[.integer k, a, b]) ≤ M := by omega
    have hc' : lh c ≤ M ∧ lh u ≤ M ∧ lh d ≤ M := by omega
    have lits' : ∀ t, Above ok (.tuple #[.integer k, a, b]) t → MLit E t := fun t ht => lits t ht.1
    refine Bdd.node_iff.mpr ⟨⟨k, _, _, rfl⟩, ⟨okl, hlit⟩, ?_, ?_, ?_⟩
    · exact (ic lits' M hc'.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (iu lits' M hc'.2.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (idd lits' M hc'.2.2).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩

theorem mbdd_lh {x : Term} (wx : Bdd (MLit E) x) (nt : x ≠ .atom "bdd_top") (nb : x ≠ .atom "bdd_bot") :
    1 ≤ lh x := by
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · exact absurd rfl nt
  · exact absurd rfl nb
  · exact (mlit_lh (Bdd.leaf_iff.mp wx)).1
  · obtain ⟨⟨k, a, b, rfl⟩, okl, -⟩ := Bdd.node_iff.mp wx
    have := mlit_lh_eq okl
    have := lh_node (.integer h) (.integer k) a b c u d (mlit_litZ okl)
    change 1 ≤ lh (.tuple ⟨[.integer h, .tuple ⟨[.integer k, a, b]⟩, c, u, d]⟩)
    omega

theorem map_empty_step {d : Dispatcher} {x : Term} {S : List (Term × Term)}
    (fresh : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "map") x) e.1) (.cons (.atom "map") x) e.1 = .eq)) = Bool.false) :
    Elixir.Module.Types.Descr.«map_empty?/2» d x (.map S) =
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil x
        (.map ((.cons (.atom "map") x, .atom "true") :: S)) := by
  unfold Elixir.Module.Types.Descr.«map_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
    Term.false, Erlang.maps.«put/3»]

theorem mlit_ok {t : Term} (h : MLit E t) : MapOk E t := by
  obtain ⟨⟨k, tag, l, rfl, g, sl⟩, nt, -⟩ := h
  exact ⟨⟨k, tag, l, rfl, g.plain, fun e me => (sl.1 e me).2⟩, nt⟩

theorem init_open_nil (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«init_map_line_empty?/4» d (.atom "open") .nil .nil S = .ok (.atom "false") := by
  rw [Elixir.Module.Types.Descr.«init_map_line_empty?/4».eq_def]
  simp [Erlang.lists.«any/2», Lynx.Except.orElse, Erlang.erlang.«is_function/2»]
  rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
  simp

theorem EF.jopsU (ef : EF nd E V den tl K) : ElemDisj E K :=
  ⟨fun ha hb S => let ⟨s, run, _⟩ := ef.sdisj S ha hb; ⟨s, fun m hm => run m (by omega)⟩⟩

/-- Disjointness under seen BDDs higher than the types is exact. -/
theorem EF.jsem (ef : EF nd E V den tl K) (N : Nat) : ElemDisjSem (EB E N) K V den (SafeN N) :=
  ⟨fun {a b S m s} ha hb hS hm run => by
    obtain ⟨s', run', ex⟩ := ef.sdisj S ha.1 hb.1
    rw [run' m hm] at run
    have : s' = s := by cases s <;> cases s' <;> simp_all [boolAtom]
    subst this
    exact ex N ha.2 hb.2 hS⟩

/-- Disjointness with no seen set is exact. -/
theorem EF.jsemZ (ef : EF nd E V den tl K) : ElemDisjSem E K V den (fun S => S = []) :=
  ⟨fun {a b S m s} ha hb hS hm run => by
    subst hS
    obtain ⟨s', run', ex⟩ := ef.sdisj [] ha hb
    rw [run' m hm] at run
    have : s' = s := by cases s <;> cases s' <;> simp_all [boolAtom]
    subst this
    exact ex (max (lh a) (lh b) + 1) (by omega) (by omega) (safeN_nil _)⟩

/-- Map types decide their emptiness exactly, when the seen BDDs are higher than them. -/
theorem map_empty_exact (ef : EF nd E V den tl K) {x : Term} (fx : MField E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 4 ≤ m → Elixir.Module.Types.Descr.«map_empty?/2» (D m) x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ w, denMF E den x w = Bool.false) := by
  have field : MapField E x := fx.imp id fun w => w.mono fun _ h => mlit_ok h
  obtain ⟨b, hb⟩ := map_total ef.opsU ef.dopsU ef.jopsU S field
  refine ⟨b, hb, fun N hx hS => ?_⟩
  have step := map_empty_step (d := D (K + 4)) (not_seen hS hx "map")
  have run := hb (K + 4) (Nat.le_refl _)
  dsimp only at run
  rw [step] at run
  have pos : ∀ {F : Term → Prop}, MapPosV F (.tuple #[.atom "open", .nil]) :=
    ⟨.atom "open", [], rfl, Or.inl rfl, by simp [FieldsV]⟩
  -- the top literal and BDDs without literals answer directly
  have direct : ∀ (c : Bool), Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D (K + 4)) (.tuple #[.atom "open", .nil]) .nil x
      (.map ((.cons (.atom "map") x, .atom "true") :: S)) = .ok (boolAtom c) →
      (c = Bool.true ↔ ∀ w, denMF E den x w = Bool.false) → (b = Bool.true ↔ ∀ w, denMF E den x w = Bool.false) := by
    intro c hc sem
    rw [hc] at run
    have : b = c := by cases b <;> cases c <;> simp_all [boolAtom]
    rw [this]; exact sem
  have someW : Nonempty (MW V) := ⟨fun _ => Option.none⟩
  rcases fx with ⟨k, rfl⟩ | wx
  · refine direct Bool.false ?_ ⟨fun h => absurd h (by decide), fun h => absurd (h (fun _ => Option.none))
      (by rw [denMF_top]; simp)⟩
    have merge : ∀ (mod name : String) (caps : Array Term),
        Erlang.orddict.«merge/3» (D (K + 4)) (.function false mod name 3 caps) .nil .nil = .ok .nil := by
      intro mod name caps; rw [Erlang.orddict.«merge/3».eq_def]; simp [Erlang.erlang.«is_function/2»]
    simp [Elixir.Module.Types.Descr.«map_bdd_empty?/4», Elixir.Module.Types.Descr.«map_line_intersection/3»,
      Elixir.Module.Types.Descr.«map_literal_intersection/6», boolAtom, merge, init_open_nil]
  by_cases top : x = .atom "bdd_top"
  · subst top
    refine direct Bool.false ?_ ⟨fun h => absurd h (by decide), fun h => absurd (h (fun _ => Option.none))
      (by rw [denMF_bdd wx]; simp)⟩
    simp [Elixir.Module.Types.Descr.«map_bdd_empty?/4», boolAtom, init_open_nil]
  by_cases bot : x = .atom "bdd_bot"
  · subst bot
    refine direct Bool.true ?_ ⟨fun _ w => by rw [denMF_bdd wx]; rfl, fun _ => rfl⟩
    simp [Elixir.Module.Types.Descr.«map_bdd_empty?/4», boolAtom]
  have one := mbdd_lh wx top bot
  have hS' := safe_put hS hx one "map"
  have ops := ef.ops (lh x) (by omega)
  have dops := ef.dops (lh x)
  have sem := ef.sem (lh x)
  have wb := mbdd_lh_le wx (fun _ h => h) (lh x) (Nat.le_refl _)
  have okLit : ∀ t, (MLit E t ∧ lh t ≤ lh x) → MapLitV (EB E (lh x)) t := by
    intro t ⟨ht, le⟩
    have hl := (mlit_lh ht).2
    obtain ⟨⟨k, tag, l, rfl, g, sl⟩, -, -⟩ := ht
    obtain ⟨hf, hd⟩ := hl k tag l rfl
    refine ⟨k, tag, l, rfl, ?_, fun e me => ⟨(sl.1 e me).1, ?_⟩, sl.2⟩
    · rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr ⟨dl, rfl, fun e me => ⟨(dv.1 e me).1, (dv.1 e me).2, ?_⟩, dv.2⟩)
        have := hd e (by rw [domFields_fieldsTerm]; exact me); omega
    · obtain ⟨u, o, he, hu⟩ := (sl.1 e me).2
      exact ⟨u, o, he, hu, by have := hf e me u o he; omega⟩
  have agree : ∀ w, eval (valM (EB E (lh x)) den w) x = eval (valM E den w) x := fun w =>
    eval_ext wb fun t ht => by
      have h₁ := valM_iff ops dops sem (okLit t ht) (w := w)
      have h₂ := valM_iff ef.opsU ef.dopsU ef.semR ht.1.1 (w := w)
      cases e₁ : valM (EB E (lh x)) den w t <;> cases e₂ : valM E den w t <;> simp_all
  constructor
  · intro hbt w
    subst hbt
    rw [denMF_bdd wx]
    have v := map_bdd_sound ops dops sem (ef.jops (lh x)) (Nat.le_refl _) _ hS' wb okLit _ [] pos (by simp)
      (by simpa [boolAtom, Term.list] using run) w (inPosM_iff.mpr ⟨fun s => fsem_nil.mpr (Or.inl rfl), fun k i => Or.inl rfl⟩) (by simp)
    rwa [agree] at v
  · intro unsat
    have t := map_bdd_val ops dops sem (ef.jops (lh x)) (ef.jsem (lh x)) (Nat.le_refl _) _ hS' wb okLit _ [] pos (by simp)
      fun w _ _ => by rw [agree]; have := unsat w; rwa [denMF_bdd wx] at this
    simp only [Term.list] at t
    rw [t] at run
    cases b <;> simp_all [boolAtom]

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Plain operations on map types keep literal heights. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- BDDs of map literals below a positive height are below it. -/
theorem mbdd_lh_bound {ok : Term → Prop} {r : Term} (wr : Bdd ok r) {M : Nat}
    (lits : ∀ t, ok t → MLit E t ∧ lh t ≤ M) (top : 1 ≤ M) : lh r ≤ M := by
  revert lits top
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MLit E t ∧ lh t ≤ M) → 1 ≤ M → lh r ≤ M)
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ top; simpa [lh] using top
  · intro _ _ top; simpa [lh] using top
  · intro ok k x y okl lits _
    exact (lits _ okl).2
  · intro ok h lit c u d leaf okl _ _ _ ic iu idd lits _
    obtain ⟨k, a, b, rfl⟩ := leaf
    have ⟨tl', le⟩ := lits _ okl
    have lits' : ∀ t, Above ok (.tuple #[.integer k, a, b]) t → MLit E t ∧ lh t ≤ M := fun t ht => lits t ht.1
    have hc := ic lits' (by omega)
    have hu := iu lits' (by omega)
    have hd := idd lits' (by omega)
    have hl := mlit_lh_eq tl'
    have hn := lh_node (.integer h) (.integer k) a b c u d (mlit_litZ tl')
    change lh (.tuple ⟨[.integer h, .tuple ⟨[.integer k, a, b]⟩, c, u, d]⟩) ≤ M
    omega

theorem mfield_mono {x : Term} (wx : Bdd (MLit E) x) {M : Nat} (le : lh x ≤ M) :
    Bdd (fun t => MLit E t ∧ lh t ≤ M) x :=
  (mbdd_lh_le wx (fun _ h => h) M le).mono fun _ h => h

/-- BDDs of map literals have a height. -/
theorem mbdd_pos {x : Term} (wx : Bdd (MLit E) x) : 1 ≤ lh x := by
  by_cases t : x = .atom "bdd_top"
  · subst t; simp [lh]
  by_cases b : x = .atom "bdd_bot"
  · subst b; simp [lh]
  · exact mbdd_lh wx t b

theorem mlh_top_leaf (k : Term) : lh (.tuple #[k, .atom "open", .nil]) = 0 := lh_leaf_top k

/-- Plain unions of map types. -/
theorem map_union_lh {x y : Term} (hx : MField E x) (hy : MField E y) :
    ∃ r, Elixir.Module.Types.Descr.«map_union/2» x y = .ok r ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w || denMF E den y w)) ∧ lh r ≤ max (lh x) (lh y) := by
  obtain ⟨r, run, fr, -, sem⟩ := map_union_field (den := den) hx hy
  refine ⟨r, run, fr, sem, ?_⟩
  rcases hx with ⟨k, rfl⟩ | wx
  · have e : Elixir.Module.Types.Descr.«map_union/2» (.tuple #[.integer k, .atom "open", .nil]) y =
        .ok (.tuple #[.integer k, .atom "open", .nil]) := by unfold Elixir.Module.Types.Descr.«map_union/2»; rfl
    rw [e] at run; cases run; rw [mlh_top_leaf]; omega
  rcases hy with ⟨k, rfl⟩ | wy
  · have nx := not_top_of_ok wx mlit_not
    have e : Elixir.Module.Types.Descr.«map_union/2» x (.tuple #[.integer k, .atom "open", .nil]) =
        .ok (.tuple #[.integer k, .atom "open", .nil]) := by
      unfold Elixir.Module.Types.Descr.«map_union/2»
      split
      · exact (nx _ rfl).elim
      · rename_i e; simp at e; subst e; rfl
      · rename_i h; exact (h _ rfl).elim
    rw [e] at run; cases run; rw [mlh_top_leaf]; omega
  obtain ⟨r', hr, okr, semr⟩ := union_ok wx wy
  rw [map_union_bdd (not_top_of_ok wx mlit_not) (not_top_of_ok wy mlit_not), hr] at run
  cases run
  exact mbdd_lh_bound (okr _ (mfield_mono wx (Nat.le_max_left _ _)) (mfield_mono wy (Nat.le_max_right _ _)))
    (fun _ h => h) (by have := mbdd_pos wx; omega)

/-- Plain intersections of map types. -/
theorem map_inter_lh {x y : Term} (hx : MField E x) (hy : MField E y) :
    ∃ r, Elixir.Module.Types.Descr.«map_intersection/2» x y = .ok r ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w && denMF E den y w)) ∧ lh r ≤ max (lh x) (lh y) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«map_intersection/2»; rfl, hy, fun w => by simp [denMF_top],
      by omega⟩
  have nx := not_top_of_ok wx mlit_not
  rcases hy with ⟨k, rfl⟩ | wy
  · refine ⟨x, ?_, Or.inr wx, fun w => by simp [denMF_top], by omega⟩
    unfold Elixir.Module.Types.Descr.«map_intersection/2»
    split
    · exact (nx _ rfl).elim
    · simp_all
    · rename_i h₁ h₂; exact (h₂ _ rfl).elim
  · obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
    have wr := okr _ wx wy
    refine ⟨r, by rw [map_intersection_bdd nx (not_top_of_ok wy mlit_not), hr], Or.inr wr, fun w => ?_, ?_⟩
    · rw [denMF_bdd wr, denMF_bdd wx, denMF_bdd wy, semr _ (valM_resp w)]
    · exact mbdd_lh_bound (okr _ (mfield_mono wx (Nat.le_max_left _ _)) (mfield_mono wy (Nat.le_max_right _ _)))
        (fun _ h => h) (by have := mbdd_pos wx; omega)

/-- Plain differences of map types: non-empty results keep heights. -/
theorem map_diff_lh {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ w, Elixir.Module.Types.Descr.«map_difference/2» x y = .ok w ∧ MField E w ∧
      (∀ v, denMF E den w v = (denMF E den x v && !denMF E den y v)) ∧
      (w ≠ .atom "bdd_bot" → lh w ≤ max (lh x) (lh y)) := by
  obtain ⟨w₀, run₀, fw₀, sem₀⟩ := map_diff_val (den := den) fx fy
  refine ⟨w₀, run₀, fw₀, sem₀, fun nb => ?_⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · have : w₀ = .atom "bdd_bot" := by
      have e : Elixir.Module.Types.Descr.«map_difference/2» x (.tuple #[.integer k, .atom "open", .nil]) =
          .ok (.atom "bdd_bot") := by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl
      rw [e] at run₀; cases run₀; rfl
    exact absurd this nb
  have ny := not_top_of_ok wy mlit_not
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · have e : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
          (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
        unfold Elixir.Module.Types.Descr.«map_difference/2»; simp [diff_leaf_top]
      rw [e] at run₀; cases run₀; exact absurd rfl nb
    · have e : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
          (.atom "bdd_bot") = .ok (.tuple #[.integer kt, .atom "open", .nil]) := by
        unfold Elixir.Module.Types.Descr.«map_difference/2»; simp [diff_leaf_bot]
      rw [e] at run₀; cases run₀; omega
    all_goals
      obtain ⟨w, run, keep, sem⟩ := neg_ok wy
      rw [map_difference_neg ny _ rfl, run] at run₀
      cases run₀
      exact mbdd_lh_bound (keep _ (mfield_mono wy (Nat.le_max_right _ _))) (fun _ h => h)
        (by have := mbdd_lh wy (by simp) (by simp); omega)
  · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
    rw [map_difference_bdd (not_top_of_ok wx mlit_not) ny, run] at run₀
    cases run₀
    exact mbdd_lh_bound (keep _ (mfield_mono wx (Nat.le_max_left _ _)) (mfield_mono wy (Nat.le_max_right _ _)))
      (fun _ h => h) (by have := mbdd_pos wx; omega)

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Map fields of element types: what the descr level needs of them. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Map fields that compare equal hold the same maps. -/
theorem denMF_resp {x x' : Term} (fx : MField E x) (fx' : MField E x') (e : Term.compare (Term.fuel x x') x x' = .eq) (w : MW V) :
    denMF E den x w = denMF E den x' w := by
  rcases fx with ⟨k, rfl⟩ | wx
  · rcases fx' with ⟨k', rfl⟩ | wx'
    · rw [denMF_top, denMF_top]
    · exfalso
      obtain ⟨ys, rfl, ex⟩ : ∃ ys : Array Term, x' = .tuple ys ∧ True := by
        cases x' <;> rw [Term.compare_step] at e <;> simp [Compare.compareStep] at e
        exact ⟨_, rfl, trivial⟩
      rw [compare_tuple] at e
      obtain ⟨l⟩ := ys
      simp only [Ordering.then_eq_eq] at e
      match l, e with
      | [a, b, c], e =>
        simp only [List.compareLex_cons_cons, Ordering.then_eq_eq] at e
        obtain ⟨-, eb, ec, -⟩ := e.2
        obtain rfl := (compare_eq_atom b "open").mp (Lynx.Term.compare_eq_symm eb)
        obtain rfl := (compare_eq_nil c).mp (Lynx.Term.compare_eq_symm ec)
        exact not_top_of_ok wx' mlit_not a rfl
      | [], e => simp at e
      | [_], e => simp at e
      | [_, _], e => simp at e
      | _ :: _ :: _ :: _ :: _, e => simp at e
  · rcases fx' with ⟨k', rfl⟩ | wx'
    · exfalso
      obtain ⟨ys, rfl, -⟩ : ∃ ys : Array Term, x = .tuple ys ∧ True := by
        cases x <;> rw [Term.compare_step] at e <;> simp [Compare.compareStep] at e
        exact ⟨_, rfl, trivial⟩
      rw [compare_tuple] at e
      obtain ⟨l⟩ := ys
      simp only [Ordering.then_eq_eq] at e
      match l, e with
      | [a, b, c], e =>
        simp only [List.compareLex_cons_cons, Ordering.then_eq_eq] at e
        obtain ⟨-, eb, ec, -⟩ := e.2
        obtain rfl := (compare_eq_atom b "open").mp eb
        obtain rfl := (compare_eq_nil c).mp ec
        exact not_top_of_ok wx mlit_not a rfl
      | [], e => simp at e
      | [_], e => simp at e
      | [_, _], e => simp at e
      | _ :: _ :: _ :: _ :: _, e => simp at e
    · rw [denMF_bdd wx, denMF_bdd wx']
      exact eval_congr_cmp wx (valM_resp w) e

/-! Field-level deliverables for maps. -/

/-- F3: plain unions of map fields. -/
theorem map_field_union {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_union/3» d (.atom "map") x y = .ok r) ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w || denMF E den y w)) ∧ lh r ≤ max (lh x) (lh y) := by
  obtain ⟨r, run, fr, sem, le⟩ := map_union_lh (den := den) fx fy
  exact ⟨r, fun d => by simpa [Elixir.Module.Types.Descr.«bare_union/3»] using run, fr, sem, le⟩

/-- F3: plain intersections of map fields. -/
theorem map_field_inter {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "map") x y = .ok r) ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w && denMF E den y w)) ∧ lh r ≤ max (lh x) (lh y) := by
  obtain ⟨r, run, fr, sem, le⟩ := map_inter_lh (den := den) fx fy
  exact ⟨r, fun d => by simpa [Elixir.Module.Types.Descr.«bare_intersection/3»] using run, fr, sem, le⟩

/-- F3: plain differences of map fields. -/
theorem map_field_diff {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map") x y = .ok r) ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w && !denMF E den y w)) ∧
      (r ≠ .atom "bdd_bot" → lh r ≤ max (lh x) (lh y)) := by
  obtain ⟨r, run, fr, sem, le⟩ := map_diff_lh (den := den) fx fy
  exact ⟨r, fun d => by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, fr, sem, le⟩

/-- F4: optimized unions of map fields. -/
theorem map_field_opt_union (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {x y : Term} (fx : MField E x)
    (fy : MField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_union/4» (D m) (.atom "map") x y (.map S) = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w || denMF E den y w) := by
  obtain ⟨r, run, fr, -, sem⟩ := opt_map_union_sem ef hm fx fy S
  exact ⟨r, by simpa [Elixir.Module.Types.Descr.«opt_union/4»] using run, fr, sem⟩

/-- F4: optimized intersections of map fields. -/
theorem map_field_opt_inter (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) {x y : Term} (fx : MField E x)
    (fy : MField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_intersection/4» (D m) (.atom "map") x y (.map S) = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := by
  obtain ⟨r, run, fr, sem⟩ := opt_map_inter_val ef hm fx fy S
  exact ⟨r, by simpa [Elixir.Module.Types.Descr.«opt_intersection/4»] using run, fr, sem⟩

/-- F4: optimized differences of map fields; dropped results have no maps. -/
theorem map_field_opt_diff (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {x y : Term} (fx : MField E x)
    (fy : MField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_difference/4» (D m) (.atom "map") x y (.map S) = .ok r ∧
      (kept (.atom "map", r) = Bool.true → MField E r ∧ ∀ w, denMF E den r w = (denMF E den x w && !denMF E den y w)) ∧
      (kept (.atom "map", r) = Bool.false → ∀ w, (denMF E den x w && !denMF E den y w) = Bool.false) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  obtain ⟨r, run, k, d⟩ := opt_map_diff_val ef hn fx fy S
  exact ⟨r, by simpa [Elixir.Module.Types.Descr.«opt_difference/4»] using run, k, d⟩

/-- F5: map fields decide their emptiness exactly, when the seen BDDs are higher than them. -/
theorem map_field_empty (ef : EF nd E V den tl K) {x : Term} (fx : MField E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 4 ≤ m →
        Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "map") x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ w, denMF E den x w = Bool.false) := by
  obtain ⟨b, run, sem⟩ := map_empty_exact ef fx S
  exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m hm, sem⟩

end Elixir.STTDescrProofsTest.Nest
