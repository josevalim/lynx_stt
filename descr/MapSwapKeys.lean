module

public import Erlang.program
public import ListsRukeymerge

@[expose] public section

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {E : Term → Prop}

theorem dom_lookup_of_mem : ∀ {dl : List (Term × Term)}, DomsV E dl → ∀ {d : String} {v : Term},
    (Term.atom d, v) ∈ dl → mapLookup dl (.atom d) = some v
  | [], _, _, _, me => by simp at me
  | x :: xs, dv, d, v, me => by
    obtain ⟨⟨a, ha, -⟩, -⟩ := dv.1 x List.mem_cons_self
    obtain ⟨k, f⟩ := x
    simp only at ha
    subst ha
    have dv' : DomsV E xs := ⟨fun e me => dv.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp dv.2).2⟩
    rcases List.mem_cons.mp me with e | me
    · simp only [Prod.mk.injEq, Term.atom.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp [lookup_cons_atom]
    · have lt := (List.pairwise_cons.mp dv.2).1 _ me
      have ne : a ≠ d := fun h => by subst h; exact cmp_lt_ne lt rfl
      rw [lookup_cons_atom, ite_eq_right ne]
      exact dom_lookup_of_mem dv' me

theorem dom_mem_of_lookup {dl : List (Term × Term)} {d : String} {v : Term} (h : mapLookup dl (.atom d) = some v) :
    (Term.atom d, v) ∈ dl := by
  rw [mapLookup] at h
  simp only [equalExact_eq_decide] at h
  cases e : dl.find? (fun entry => decide (compareExact (fuel (.atom d) entry.1) (.atom d) entry.1 = .eq)) with
  | none => rw [e] at h; cases h
  | some r =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have mr := List.mem_of_find?_eq_some e
    have := List.find?_some e
    simp only [decide_eq_true_eq] at this
    have e₁ : r.1 = .atom d := (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm this)
    rw [show r = (r.1, r.2) from rfl, e₁, h] at mr
    exact mr

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Map types none of whose literals mention two atom keys hold the same maps with those keys swapped. -/
theorem swap_seen (ef : EF nd E V den tl K) {b : Term} {S : List (Term × Term)}
    (wb : (∃ k : Int, b = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd (fun u => MLit E u ∧ SeenNamed S u) b)
    {s c : String} (hs : (Term.atom s, Term.nil) ∉ S) (hc : (Term.atom c, Term.nil) ∉ S) (w : MW V) :
    denMF E den b (swapW s c w) = denMF E den b w := by
  rcases wb with ⟨k, rfl⟩ | wb
  · rw [denMF_top, denMF_top]
  rw [denMF_bdd (wb.mono fun _ h => h.1), denMF_bdd (wb.mono fun _ h => h.1)]
  refine eval_ext wb fun u ⟨lt, nt⟩ => ?_
  obtain ⟨k, tag, l, rfl, -, -⟩ := lt.1
  have fresh : ∀ a, (Term.atom a, Term.nil) ∉ S → mapLookup l (.atom a) = none := fun a na =>
    lookup_fresh' fun ma => na (nt k tag l rfl a ma)
  have lit : MapLitV E (.tuple #[.integer k, tag, fieldsTerm l]) := lt.1
  rw [Bool.eq_iff_iff, valM_iff ef.mopsE ef.mdopsE ef.semR lit, valM_iff ef.mopsE ef.mdopsE ef.semR lit, nsem_lit,
    nsem_lit, msem_swapW_iff (fresh s hs) (fresh c hc)]

end

section
variable {t : Term} {n : Nat}

/-- `map_to_list_static/3` on the lines of a map type: the pairs of `term()` when a line is open, otherwise the pairs of
the domains of its lines and of its atom keys. -/
theorem mtl_static3 {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) {b : Term} (fb : MField (level t (n + 1)).E b)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) :
    (∃ L ∈ lines, OpenLine L ∧ ∃ P, Elixir.Module.Types.Descr.«map_to_list_static/3» (D (M + 5)) b (Term.list lines) mtlF =
        .ok P ∧ DE (level t (n + 1)).E P ∧ ∀ p, denD P p ↔ PairPt t (n + 1) (.atom "term") (.atom "term") p) ∨
      ((∀ L ∈ lines, ¬OpenLine L) ∧ ∃ S inner,
        Elixir.Module.Types.Descr.«map_to_list_static/3» (D (M + 5)) b (Term.list lines) mtlF = .ok inner ∧
        SeenOk S ∧ ((∃ k : Int, b = .tuple #[.integer k, .atom "open", .nil]) ∨
          Bdd (fun u => MLit (level t (n + 1)).E u ∧ SeenNamed S u) b) ∧ DE (level t (n + 1)).E inner ∧
        ∀ p, denD inner p ↔ (∃ L ∈ lines, LinePairs t n L p) ∨ ∃ s, (Term.atom s, Term.nil) ∈ S ∧ AtomPair t n lines s p) := by
  have hl' : ∀ L ∈ lines, MLine (level t (n + 1)).E L := fun L m => (hl L m).1
  rcases lines_pairs (t := t) (n := n) (M := M + 3) (by omega) lines hl' with ⟨L, mL, o, run⟩ |
    ⟨acc₀, run, no, d₀, s₀⟩
  · obtain ⟨P, rP, dP, sP⟩ := mtl_pair (t := t) (n := n + 1) (level t (n + 1)).ef.term (level t (n + 1)).ef.term
      (Or.inl rfl) (Or.inl rfl) (M + 5)
    refine Or.inl ⟨L, mL, o, P, ?_, dP, sP⟩
    simp only [Elixir.Module.Types.Descr.«map_to_list_static/3», Lynx.Except.tryWith]
    simp [run, Lynx.Exception.classTerm, Lynx.Exception.reason, rP]
  · have ha : AccOk t n lines acc₀ [] acc₀ := ⟨d₀, fun p => by simp⟩
    obtain ⟨S, a, rr, hS, -, ha', named⟩ : ∃ S a, Elixir.Module.Types.Descr.«bdd_reduce/3» (D (M + 5)) b
        (.tuple #[.map [], acc₀])
        (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-3-" 2 #[Term.list lines, mtlF]) =
          .ok (.tuple #[.map S, a]) ∧ SeenOk S ∧ True ∧ AccOk t n lines acc₀ S a ∧
        ((∃ k : Int, b = .tuple #[.integer k, .atom "open", .nil]) ∨
          Bdd (fun u => MLit (level t (n + 1)).E u ∧ SeenNamed S u) b) := by
      rcases fb with ⟨k, rfl⟩ | wb
      · obtain ⟨S, a, run, hS, -, -, ha'⟩ := fetch_leaf hM lines hl acc₀ (lit := .tuple #[.integer k, .atom "open", .nil])
          ⟨k, .atom "open", [], rfl, Or.inl rfl, ⟨by simp, by simp⟩⟩ [] acc₀ (by simp [SeenOk]) ha
        exact ⟨S, a, by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simpa using run, hS, trivial, ha',
          Or.inl ⟨k, rfl⟩⟩
      · obtain ⟨S, a, run, hS, -, ha', named⟩ := fetch_reduce hM lines hl acc₀ wb [] acc₀ (by simp [SeenOk]) ha
        exact ⟨S, a, run, hS, trivial, ha', Or.inr named⟩
    refine Or.inr ⟨no, S, a, ?_, hS, named, ha'.1, fun p => ?_⟩
    · simp only [Elixir.Module.Types.Descr.«map_to_list_static/3», Lynx.Except.tryWith]
      simp [run, rr]
    · rw [ha'.2, s₀]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem any1_sem {m : Nat} (f : Term) (P : Term → Prop) : ∀ (l : List Term),
    (∀ x ∈ l, ∃ b : Bool, (D m).pure f #[x] = .ok (boolAtom b) ∧ (b = Bool.true ↔ P x)) →
    ∃ b : Bool, Erlang.lists.«any_1/2» (D m) f (Term.list l) = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∃ x ∈ l, P x)
  | [], _ => ⟨Bool.false, by rw [Erlang.lists.«any_1/2».eq_def]; simp [boolAtom], by simp⟩
  | x :: rest, each => by
    obtain ⟨b, rb, sb⟩ := each x List.mem_cons_self
    obtain ⟨c, rc, sc⟩ := any1_sem f P rest fun y my => each y (List.mem_cons_of_mem _ my)
    rw [Erlang.lists.«any_1/2».eq_def]
    cases b
    · refine ⟨c, by simpa [rb, boolAtom] using rc, ?_⟩
      rw [sc]
      simp only [List.mem_cons, exists_eq_or_imp]
      exact ⟨Or.inr, fun h => h.elim (fun hx => absurd (sb.mpr hx) (by simp)) id⟩
    · exact ⟨Bool.true, by simp [rb, boolAtom], by simp only [true_iff]; exact ⟨x, List.mem_cons_self, sb.mp rfl⟩⟩

theorem any_sem {m : Nat} (mo nm : String) (caps : Array Term) (P : Term → Prop) (l : List Term)
    (each : ∀ x ∈ l, ∃ b : Bool, (D m).pure (.function false mo nm 1 caps) #[x] = .ok (boolAtom b) ∧ (b = Bool.true ↔ P x)) :
    ∃ b : Bool, Erlang.lists.«any/2» (D m) (.function false mo nm 1 caps) (Term.list l) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ∃ x ∈ l, P x) := by
  obtain ⟨b, rb, sb⟩ := any1_sem (m := m) (.function false mo nm 1 caps) P l each
  refine ⟨b, ?_, sb⟩
  cases l with
  | nil => simpa [Erlang.lists.«any/2», Erlang.erlang.«is_function/2», Term.list, Erlang.lists.«any_1/2»] using rb
  | cons x rest =>
    rw [Erlang.lists.«any_1/2».eq_def] at rb
    simpa [Erlang.lists.«any/2», Erlang.erlang.«is_function/2», Term.list] using rb

section
variable {E : Term → Prop} {V : Type} {den : Term → V → Prop}

/-- Fields that allow the key to be absent. -/
def OptFields (l : List (Term × Term)) : Prop := ∀ e ∈ l, ∃ ty, e.2 = .tuple #[ty, .atom "true"]

theorem opt_fields_all (name : String) (hname : name = "-has_empty_map?/1-fun-0-" ∨ name = "-has_empty_map?/1-fun-1-")
    {l : List (Term × Term)} (hl : ∀ e ∈ l, FieldValue E e.2) {m : Nat} :
    ∃ b : Bool, Erlang.lists.«all/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" name 1 #[]) (fieldsTerm l) =
      .ok (boolAtom b) ∧ (b = Bool.true ↔ OptFields l) := by
  obtain ⟨b, rb, sb⟩ := all_sem (K' := 0) "Elixir.Module.Types.Descr" name #[] (l.map fun e => .tuple #[e.1, e.2])
    (m := m + 1) (by omega) (fun x => ∃ k ty, x = .tuple #[k, .tuple #[ty, .atom "true"]])
    (fun _ x => Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-0-/1» x)
    (fun m x => by
      rcases hname with rfl | rfl
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-has_empty_map?/1-fun-0-/1».pure]
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-has_empty_map?/1-fun-1-/1».pure]
        simp [Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-0-/1», Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-1-/1»])
    (fun x mx => by
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      obtain ⟨ty, o, he, -⟩ := hl e me
      refine ⟨o, fun _ _ => by simp [Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-0-/1», he], ?_⟩
      cases o <;> simp [he, boolAtom])
  refine ⟨b, rb, ?_⟩
  rw [sb]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, OptFields]
  constructor
  · intro h e me
    obtain ⟨k, ty, he⟩ := h e me
    simp only [Term.tuple.injEq] at he
    have := congrArg (fun a : Array Term => a[1]?) he
    simp at this
    exact ⟨ty, this⟩
  · intro h e me
    obtain ⟨ty, he⟩ := h e me
    exact ⟨e.1, ty, by rw [he]⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The empty map of values. -/
def wNone : MW V := fun _ => none

theorem msem_none {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l) :
    MSem den tag l (wNone (V := V)) ↔ OptFields l := by
  constructor
  · intro h e me
    obtain ⟨⟨s, es⟩, ty, o, he, -⟩ := sl.1 e me
    have hs := h.atoms s
    unfold FSem at hs
    rw [lookup_of_mem sl me es, he] at hs
    simp only at hs
    rw [fieldSem_mk] at hs
    rcases hs with ⟨-, rfl⟩ | ⟨x, h, -⟩
    · exact ⟨ty, he⟩
    · cases h
  · intro h
    refine ⟨fun s => ?_, fun k i => tagSem_none _ _⟩
    unfold FSem
    cases hf : mapLookup l (.atom s) with
    | none => exact tagSem_none _ _
    | some f =>
      obtain ⟨e, me, rfl⟩ := entry_of_lookup hf
      obtain ⟨ty, hty⟩ := h e (mem_of_mem_mapEntries me)
      simp only
      rw [hty, show Term.atom "true" = boolAtom Bool.true from rfl, fieldSem_mk]
      exact Or.inl ⟨rfl, rfl⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `has_empty_map?/1` holds exactly when a line holds the empty map. -/
theorem has_empty (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) (m : Nat) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«has_empty_map?/1» (D (m + 3)) (Term.list lines) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ∃ L ∈ lines, InMLine den L (wNone (V := V))) := by
  obtain ⟨b, rb, sb⟩ := any_sem (m := m + 3) "Elixir.Module.Types.Descr" "-has_empty_map?/1-fun-3-" #[]
    (fun L => InMLine den L (wNone (V := V))) lines (fun L mL => by
      obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hl L mL
      obtain ⟨b₁, r₁, s₁⟩ := opt_fields_all (E := E) "-has_empty_map?/1-fun-0-" (Or.inl rfl) (l := l)
        (fun e me => (sl.1 e me).2) (m := m + 1)
      obtain ⟨b₂, r₂, s₂⟩ := all_sem (K' := 1) "Elixir.Module.Types.Descr" "-has_empty_map?/1-fun-2-" #[] negs
        (m := m + 2) (by omega) (fun N => ¬NSem den N (wNone (V := V)))
        (fun m x => Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-2-/1» (D m) x)
        (fun m x => by rw [Erlang.program.«Elixir.Module.Types.Descr:-has_empty_map?/1-fun-2-/1».pure])
        (fun N mN => by
          obtain ⟨k, ntag, nl, rfl, -, snl⟩ := lits N mN
          refine ⟨!bp (OptFields nl), fun m' hm' => ?_, ?_⟩
          · obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
            obtain ⟨c, rc, sc⟩ := opt_fields_all (E := E) "-has_empty_map?/1-fun-1-" (Or.inr rfl) (l := nl)
              (fun e me => (snl.1 e me).2) (m := m'')
            have ec : c = bp (OptFields nl) := by
              cases c
              · exact (bp_false.mpr fun h => absurd (sc.mpr h) (by simp)).symm
              · exact (bp_true.mpr (sc.mp rfl)).symm
            subst ec
            cases h : bp (OptFields nl) <;>
              simp [Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-2-/1», rc, h, Erlang.erlang.«not/1», boolAtom]
          · rw [nsem_lit, msem_none snl]
            cases h : bp (OptFields nl)
            · simp only [Bool.not_false, true_iff]; exact bp_false.mp h
            · simp only [Bool.not_true, Bool.false_eq_true, false_iff, Classical.not_not]; exact bp_true.mp h)
      refine ⟨b₁ && b₂, ?_, ?_⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-has_empty_map?/1-fun-3-/1».pure]
        cases b₁ <;> cases b₂ <;>
          simp [Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-3-/1», r₁, r₂, boolAtom, Lynx.Except.andAlso]
      · rw [inMLine_iff, msem_none sl, Bool.and_eq_true, s₁, s₂])
  exact ⟨b, by simpa [Elixir.Module.Types.Descr.«has_empty_map?/1»] using rb, sb⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- `map_bdd_to_dnf_remove_empty/1` lists the non-empty lines of a map BDD of any literals. -/
theorem dnf_lit_map (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    (jsem : ElemDisjSem E K V den Safe) (hS : Safe []) {m : Nat}
    (hm : K + 4 ≤ m) {r : Term} (wr : Bdd (MapLitV E) r) :
    ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1» (D m) r =
        .ok (Term.list lines) ∧ (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) ∧
      ∀ w, eval (valM E den w) r = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := by
  obtain ⟨all, run, tl, sl⟩ := dnf_map (den := den) ops dops sem (m := m) (by omega) hS wr (fun t h => h) []
    (.tuple #[.atom "open", .nil]) [] ⟨.atom "open", [], rfl, Or.inl rfl, by simp [FieldsV]⟩ (by simp)
  have keeps : ∀ L ∈ all, ∃ keep : Bool, (∀ m acc, K + 4 ≤ m →
      (D m).pure (.function false "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ w, InMLine den L w) :=
    fun L mL => mline_keep ops dops sem jops jsem hS (tl L mL)
  classical
  let keep : Term → Bool := fun L => if h : L ∈ all then Classical.choose (keeps L h) else Bool.false
  have hk : ∀ L ∈ all, (∀ m acc, K + 4 ≤ m →
      (D m).pure (.function false "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep L then .cons L acc else acc)) ∧ (keep L = Bool.true ↔ ∃ w, InMLine den L w) := by
    intro L mL
    simp only [keep, dite_eq_left mL]
    exact Classical.choose_spec (keeps L mL)
  have fold := foldl_det (K := K + 4) "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" #[]
    (fun x a => if keep x then .cons x a else a) all (fun x mx a m hm => (hk x mx).1 m a hm) .nil hm
  have e := foldl_filter keep all []
  simp only [List.append_nil] at e
  simp only [Term.list] at e
  refine ⟨(all.filter keep).reverse, ?_, fun L mL => ?_, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1»
    have run' : Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) .nil (.tuple #[.atom "open", .nil]) .nil r (.map []) =
        .ok (Term.list all) := by simpa using run
    simp only [run', Lynx.Except.ok_bind]
    rw [show (do
        let f ← (pure (Term.function false "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) :
          Except Exception Term)
        Erlang.lists.«foldl/3» (D m) f .nil (Term.list all)) =
        Erlang.lists.«foldl/3» (D m) (.function false "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[])
          .nil (Term.list all) from rfl, fold, e]
  · simp only [List.mem_reverse, List.mem_filter] at mL
    exact ⟨tl L mL.1, (hk L mL.1).2.mp mL.2⟩
  · have hp : InPosM den (.tuple #[.atom "open", .nil]) w := ⟨.atom "open", [], rfl, ⟨fun s => by
      simp [FSem, TagSem, mapLookup], fun k i => by simp [TagSem]⟩⟩
    rw [← (by simpa [hp] using sl w : (∃ L ∈ all, InMLine den L w) ↔ eval (valM E den w) r = Bool.true)]
    constructor
    · rintro ⟨L, mL, hL⟩
      exact ⟨L, by simp [mL, (hk L mL).2.mpr ⟨w, hL⟩], hL⟩
    · rintro ⟨L, mL, hL⟩
      simp only [List.mem_reverse, List.mem_filter] at mL
      exact ⟨L, mL.1, hL⟩

end

section
variable {t : Term} {n : Nat}

/-- The pairs `map_to_list/1` lists for the maps of a map type: each key and value of its maps, for every point of the
type of an atom key and every point of the kind of other keys, and only pairs whose value is at a key of its maps. -/
def InnerSem (t : Term) (n : Nat) (b inner : Term) : Prop :=
  (∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true → ∀ s x, w (.atom s) = some x →
    ∀ k, (level t (n + 1)).den (atomT s) k → denD inner (tpt (t := t) (n := n + 1) [k, x])) ∧
  (∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true → ∀ kk i x, w (.dom kk i) = some x →
    ∀ k : (level t (n + 1)).V, ptKind (toPN k) = domKind kk → denD inner (tpt (t := t) (n := n + 1) [k, x])) ∧
  (∀ p : PN t (n + 1), denD inner p → ∃ w' : List (level t (n + 1)).V,
    (∀ Y, denD (.map Y) p ↔ TT t (n + 1) Y w') ∧ ∃ k x, w' = [k, x] ∧
      ∃ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true ∧ ∃ κ, w κ = some x)

theorem pairPt_tpt {a b : Term} {k x : (level t (n + 1)).V} (ha : (level t (n + 1)).den a k)
    (hb : (level t (n + 1)).den b x) : PairPt t (n + 1) a b (tpt [k, x]) :=
  ⟨[k, x], fun _ => denD_tpt _, k, x, rfl, ha, hb⟩

end

section
variable {t : Term} {n : Nat}

theorem inner_run {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) {b : Term} (fb : MField (level t (n + 1)).E b)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w)
    (sl : ∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true ↔
      ∃ L ∈ lines, InMLine (level t (n + 1)).den L w) :
    ∃ inner, Elixir.Module.Types.Descr.«map_to_list_static/3» (D (M + 5)) b (Term.list lines) mtlF = .ok inner ∧
      DE (level t (n + 1)).E inner ∧ InnerSem t n b inner := by
  have ef := (level t (n + 1)).ef
  have hl' : ∀ L ∈ lines, MLine (level t (n + 1)).E L := fun L m => (hl L m).1
  rcases mtl_static3 hM fb lines hl with ⟨L, mL, ⟨l, negs, rfl⟩, P, rP, dP, sP⟩ |
    ⟨no, S, inner, run, hS, named, dI, sI⟩
  · refine ⟨P, rP, dP, fun w hw s x hx k hk => (sP _).mpr (pairPt_tpt (ef.den_term k) (ef.den_term x)),
      fun w hw kk i x hx k hk => (sP _).mpr (pairPt_tpt (ef.den_term k) (ef.den_term x)), fun p hp => ?_⟩
    obtain ⟨w', hw', k, x, rfl, -, -⟩ := (sP p).mp hp
    refine ⟨[k, x], hw', k, x, rfl, ?_⟩
    obtain ⟨⟨tag, l', negs', e, -, sl', -⟩, w₀, h₀⟩ := hl _ mL
    obtain ⟨-, rfl, rfl⟩ := tuple3_inj e
    let Mx := ((keyStrs l').map String.length).foldr max 0
    have fr : ∀ c ∈ freshStrs Mx (negs'.length + 1), c ∉ keyStrs l' := fun c mc m => by
      have := le_maxLen _ c m; have := freshStrs_len mc; omega
    obtain ⟨κ, -, w, hw, wκ⟩ := line_witness h₀ ((freshStrs Mx (negs'.length + 1)).map MKey.atom)
      (List.Pairwise.map MKey.atom (fun _ _ ne e => ne (MKey.atom.inj e)) (freshStrs_nodup Mx _)) (by simp [freshStrs_length])
      fun κ mκ => by
        obtain ⟨c, mc, rfl⟩ := List.mem_map.mp mκ
        show FSem (level t (n + 1)).den (.atom "open") l' c (some x)
        unfold FSem; rw [lookup_fresh' (fr c mc)]; exact Or.inl rfl
    exact ⟨w, (sl w).mpr ⟨_, mL, hw⟩, κ, wκ⟩
  · have hnone : ∀ x, ¬(level t (n + 1)).den (.map []) x := fun x h => ef.den_none x h
    refine ⟨inner, run, dI, fun w hw s x hx k hk => ?_, fun w hw kk i x hx k hk => ?_, fun p hp => ?_⟩
    · by_cases hs : (Term.atom s, Term.nil) ∈ S
      · obtain ⟨L, mL, hL⟩ := (sl w).mp hw
        exact (sI _).mpr (Or.inr ⟨s, hs, [k, x], fun _ => denD_tpt _, k, x, rfl, hk, L, mL, w, hL, hx⟩)
      have notR : ∀ a, Term.atom a ∈ S.map Prod.fst → (Term.atom a, Term.nil) ∈ S := fun a h => by
        obtain ⟨e, me, he⟩ := List.mem_map.mp h
        obtain ⟨s', rfl⟩ := hS e me
        simp only [Term.atom.injEq] at he
        subst he
        exact me
      obtain ⟨L, mL, tag, l, negs, rfl, hx'⟩ := unnamed_tag ef (N := []) (R := S.map Prod.fst) lines hl' sl
        (fun s' c _ _ ns nc w => swap_seen ef named (fun h => ns (List.mem_map.mpr ⟨_, h, rfl⟩))
          (fun h => nc (List.mem_map.mpr ⟨_, h, rfl⟩)) w) (by simp [mapLookup]) (fun h => hs (notR s h)) hw hx
      obtain ⟨tag', l', negs', e, g, -, -⟩ := hl' _ mL
      obtain ⟨rfl, -, -⟩ := tuple3_inj e
      rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
      · exact absurd ⟨_, _, rfl⟩ (no _ mL)
      · simp [tagType] at hx'; exact absurd hx' (hnone x)
      · rw [tagType_dom] at hx'
        cases hv : mapLookup dl (.atom "atom") with
        | none => rw [hv] at hx'; exact absurd hx' (hnone x)
        | some v =>
          rw [hv] at hx'
          have dT := (dkdT_run (t := t) (n := n) (d := "atom") (by simp [domainKinds])).2
          have hk' := (den_succ (atomT_de s) (toPN k)).mp hk
          rw [atomT_den] at hk'
          have kd := (den_succ dT.de (toPN k)).mpr (dT.atoms rfl _ hk'.1)
          exact (sI _).mpr (Or.inl ⟨_, mL, dl, l, negs, rfl, "atom", v, dom_mem_of_lookup hv, by simp [domainKinds],
            ⟨x, hx'⟩, pairPt_tpt kd hx'⟩)
    · obtain ⟨L, mL, hL⟩ := (sl w).mp hw
      obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl' L mL
      have hd := (inMLine_iff.mp hL).1.doms kk i
      rw [hx] at hd
      rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
      · exact absurd ⟨_, _, rfl⟩ (no _ mL)
      · simp [TagSem] at hd
      · rw [tagSem_dom_iff hnone] at hd
        obtain ⟨v, T, ev, hT, hvT⟩ := hd.resolve_left (by simp)
        cases ev
        have dT := (dkdT_run (t := t) (n := n) (domKind_mem kk)).2
        have kd := (den_succ dT.de (toPN k)).mpr (dT.kinds (domKind_ne_atom kk) _ hk)
        exact (sI _).mpr (Or.inl ⟨_, mL, dl, l, negs, rfl, domKind kk, T, dom_mem_of_lookup hT, domKind_mem kk,
          ⟨_, hvT⟩, pairPt_tpt kd hvT⟩)
    · rcases (sI p).mp hp with ⟨L, mL, dl, l, negs, rfl, d, v, mem, md, -, w', hw', k, x, rfl, -, hvx⟩ |
        ⟨s, -, w', hw', k, x, rfl, -, L, mL, w, hL, hws⟩
      · obtain ⟨tag, l', negs', e, g, -, -⟩ := (hl _ mL).1
        obtain ⟨e₁, -, -⟩ := tuple3_inj e
        have dv : DomsV (level t (n + 1)).E dl := by
          rcases g with rfl | rfl | ⟨dl', rfl, dv⟩
          · exact absurd e₁ (fieldsTerm_ne_atom dl "open")
          · exact absurd e₁ (fieldsTerm_ne_atom dl "closed")
          · rwa [fieldsTerm_inj e₁]
        obtain ⟨w, hw, κ, -, wκ⟩ := tag_witness ef (hl _ mL).1 (hl _ mL).2 md
          ⟨fieldsTerm dl, l, negs, rfl, by rw [tagType_dom, dom_lookup_of_mem dv mem]; exact hvx⟩ []
        exact ⟨[k, x], hw', k, x, rfl, w, (sl w).mpr ⟨_, mL, hw⟩, κ, wκ⟩
      · exact ⟨[k, x], hw', k, x, rfl, w, (sl w).mpr ⟨L, mL, hL⟩, .atom s, hws⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- `map_to_list/2` with the pair function on static map types of the level above: `:badmap` for types other than non-empty
map types, otherwise lists of the pairs of their maps, holding the empty list exactly when they hold the empty map. -/
theorem tolist_map {X : List (Term × Term)} (hX : DE (level t (n + 1)).E (.map X)) {m : Nat}
    (hm : (level t (n + 1)).K + 30 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_to_list/2» (D m) (.map X) mtlF = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t (n + 1) X) ∨
        (MOnly t (n + 1) X ∧ ∃ b inner L, mapLookup X (.atom "map") = some b ∧ res = .tuple #[.atom "ok", L] ∧
          DE (level t (n + 1)).E inner ∧ InnerSem t n b inner ∧
          ((L = nilT ∧ ∀ p : PN t (n + 1), ¬denD inner p) ∨
            ∃ nil k, L = lTy nil k inner ∧ (nil = Bool.true ↔ MT t (n + 1) X wNone)))) := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 5 := ⟨m - 5, by omega⟩
  have sX := de_map hX
  have ef := (level t (n + 1)).ef
  obtain ⟨dR, sR⟩ := rest_map hX
  have rE := next_empty dR (m := M + 5) (by omega)
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (M + 5)) (.map X) =
      .ok (boolAtom (bp (∀ v : PN t (n + 1), ¬denD (.map (rmM X)) v))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
    exact rE
  rw [Elixir.Module.Types.Descr.«map_to_list/2».eq_def]
  simp only [Erlang.maps.«take/2», sX.static, mo]
  by_cases restE : ∀ v : PN t (n + 1), ¬denD (.map (rmM X)) v
  · rw [bp_true.mpr restE]
    have onlyIff : MOnly t (n + 1) X ↔ ∃ w, MT t (n + 1) X w :=
      ⟨fun h => h.2, fun h => ⟨fun v hv => Classical.byContradiction fun ne => restE v ((sR v).mpr ⟨hv, ne⟩), h⟩⟩
    cases hb : mapLookup X (.atom "map") with
    | none =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
      · simp [boolAtom, Lynx.Term.isMember, Elixir.Module.Types.Descr.«map_to_list_static/2», getMapKeys_single, hb]
      · obtain ⟨w, b, hb', -⟩ := (onlyIff.mp h)
        rw [hb] at hb'; cases hb'
    | some b =>
      have fb : MField (level t (n + 1)).E b := fieldC_map (sX.fields "map" b hb)
      have wb : Bdd (MapLitV (level t (n + 1)).E) b := by
        rcases fb with ⟨k, rfl⟩ | wb
        · exact Bdd.leaf_iff.mpr ⟨k, .atom "open", [], rfl, Or.inl rfl, ⟨by simp, by simp⟩⟩
        · exact wb.mono fun _ h => h.1
      obtain ⟨lines, rl, hl, sl⟩ := dnf_lit_map (den := (level t (n + 1)).den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
        (m := M + 5) (by omega) wb
      have inB : ∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true ↔
          ∃ L ∈ lines, InMLine (level t (n + 1)).den L w := by
        intro w
        rw [← sl w]
        rcases fb with ⟨k, rfl⟩ | wb'
        · have lit : MapLitV (level t (n + 1)).E (.tuple #[.integer k, .atom "open", fieldsTerm []]) :=
            ⟨k, .atom "open", [], rfl, Or.inl rfl, ⟨by simp, by simp⟩⟩
          have v := (valM_iff (w := w) ef.mopsE ef.mdopsE ef.semR lit).mpr (nsem_lit.mpr (msem_open_nil w))
          rw [denMF_top, eval_leaf]
          exact ⟨fun _ => v, fun _ => rfl⟩
        · rw [denMF_bdd wb']
      have mt : ∀ w, MT t (n + 1) X w ↔ denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true :=
        fun w => by simp [MT, hb]
      cases lines with
      | nil =>
        refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [boolAtom, Lynx.Term.isMember, Elixir.Module.Types.Descr.«map_to_list_static/2», getMapKeys_single, hb,
            rl, Term.list]
        · obtain ⟨w, hw⟩ := onlyIff.mp h
          simpa using (inB w).mp ((mt w).mp hw)
      | cons L₀ rest =>
        obtain ⟨w₀, h₀⟩ := (hl L₀ List.mem_cons_self).2
        have only : MOnly t (n + 1) X := onlyIff.mpr ⟨w₀, (mt w₀).mpr ((inB w₀).mpr ⟨L₀, List.mem_cons_self, h₀⟩)⟩
        obtain ⟨inner, ri, di, si⟩ := inner_run (M := M) (by omega) fb (L₀ :: rest) hl inB
        by_cases ce : Term.compare (Term.fuel inner (.map [])) inner (.map []) = .eq
        · refine ⟨_, ?_, Or.inr ⟨only, b, inner, nilT, rfl, rfl, di, si, Or.inl ⟨rfl, fun p hp => ?_⟩⟩⟩
          · simp [boolAtom, Lynx.Term.isMember, Elixir.Module.Types.Descr.«map_to_list_static/2», getMapKeys_single, hb,
              rl, ri, Erlang.erlang.«==/2», ce, Elixir.Module.Types.Descr.«empty_list/0», nilT]
          · have := (ef_next t (n + 1)).resp de_none di (Lynx.Term.compare_eq_symm ce) hp
            simp [denD_map, mapLookup, dn_none] at this
        · obtain ⟨hb', rh, sh⟩ := has_empty (den := (level t (n + 1)).den) (L₀ :: rest) (fun L m => (hl L m).1) (M + 2)
          obtain ⟨k, rlist, rnel⟩ := list_run ((ef_next t (n + 1)).static di) (M + 5)
          refine ⟨_, ?_, Or.inr ⟨only, b, inner, lTy hb' k inner, rfl, rfl, di, si, Or.inr ⟨hb', k, rfl, ?_⟩⟩⟩
          · cases hb' <;> simp [boolAtom, Lynx.Term.isMember, Elixir.Module.Types.Descr.«map_to_list_static/2»,
              getMapKeys_single, hb, rl, ri, Erlang.erlang.«==/2», ce, rh, rlist, rnel, lTy]
          · rw [sh, mt, inB]
  · rw [bp_false.mpr restE]
    refine ⟨.atom "badmap", by simp [boolAtom, Lynx.Term.isMember], Or.inl ⟨rfl, fun h => restE fun v hv => ?_⟩⟩
    exact ((sR v).mp hv).2 (h.1 v ((sR v).mp hv).1)

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem tolist_one (d : Dispatcher) (x : Term) :
    Elixir.Module.Types.Descr.«map_to_list/1» d x = Elixir.Module.Types.Descr.«map_to_list/2» d x mtlF := by
  simp [Elixir.Module.Types.Descr.«map_to_list/1», mtlF]

theorem tolist_term (d : Dispatcher) (f : Term) :
    Elixir.Module.Types.Descr.«map_to_list/2» d (.atom "term") f = .ok (.atom "badmap") := by
  rw [Elixir.Module.Types.Descr.«map_to_list/2».eq_def]
  rfl

section
variable {t : Term} {n : Nat}

theorem same_tuple {a : Term} (ha : DE (level t n).E a) {y : PN t n} {w : List (level t n).V}
    (hw : ∀ Y, denD (.map Y) y ↔ TT t n Y w) : denD a y ↔ denD a (tpt w) := by
  rcases ha with rfl | ⟨Z, rfl, -⟩
  · exact ⟨fun _ => denD_term _, fun _ => denD_term _⟩
  · exact (hw Z).trans (denD_tpt w).symm

/-- Lists of a type of pairs are lists of `map_to_list/1` when its pairs are pairs of the map. -/
theorem nel_sub {P inner : Term} (dP : DE (level t (n + 1)).E P) (dI : DE (level t (n + 1)).E inner)
    (incl : ∀ y : PN t (n + 1), denD P y → denD inner y) (nil : Bool) (k k' : Int) :
    SubN t (n + 2) (lTy Bool.false k' P) (lTy nil k inner) := by
  intro q hq
  rw [lTy_den _ _ dP] at hq
  rw [lTy_den _ _ dI]
  rcases hq with ⟨h, -⟩ | ⟨hl, h⟩
  · cases h
  · exact Or.inr ⟨hl, fun v hv => ⟨fun y my => incl _ ((h v hv).1 y my), (h v hv).2⟩⟩

theorem denD_atom_pt {Y : List (Term × Term)} {v : PN t n} (hv : v.1.1 = "atom") :
    denD (.map Y) v ↔ denD (.map Y) (aPt (t := t) (n := n) v.1.2.2.1) := by
  rw [denD_aPt, denD_map, hv]
  cases mapLookup Y (.atom "atom") <;> simp [dn_none, dn_atom, amemV]

/-- The empty map type, as `empty_map/0` builds it. -/
def emptyMapT : Term := .map [(.atom "map", .tuple #[.integer (-288230376038284242), .atom "closed", .nil])]

theorem emptyMap_run : Elixir.Module.Types.Descr.«empty_map/0» = .ok emptyMapT := rfl

theorem emptyMap_field :
    MField (level t n).E (.tuple #[.integer (-288230376038284242), .atom "closed", fieldsTerm []]) :=
  mleaf_field (Or.inr (Or.inl rfl)) ⟨by simp, by simp⟩ fun k tag l e => by
    obtain ⟨e₁, e₂, -⟩ := tuple3_inj e
    simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨fun _ => by omega, fun h => by simp at h⟩

theorem emptyMap_de : DE (level t n).E emptyMapT := mfused_de emptyMap_field

theorem mt_emptyMap (w : MW (level t n).V) : MT t n [(.atom "map", .tuple #[.integer (-288230376038284242), .atom "closed",
    .nil])] w ↔ w = wNone := by
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', equalExact_eq_decide]
  rw [show (Term.nil : Term) = fieldsTerm [] from rfl, denMF_leaf (level t n).ef ⟨by simp, by simp⟩ (Or.inr (Or.inl rfl))]
  constructor
  · intro h
    funext κ
    cases κ with
    | atom s => simpa [FSem, TagSem, mapLookup, wNone] using h.atoms s
    | dom k i => simpa [TagSem, wNone] using h.doms k i
  · rintro rfl
    exact ⟨fun s => by simp [FSem, TagSem, mapLookup, wNone], fun k i => by simp [TagSem, wNone]⟩

/-- A map holding a value at some key gives `map_to_list/1` a pair. -/
theorem inner_of_value {b inner : Term} (sI : InnerSem t n b inner) {w : MW (level t (n + 1)).V}
    (hw : denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true) {κ : MKey} {x : (level t (n + 1)).V}
    (hx : w κ = some x) : ∃ p : PN t (n + 1), denD inner p := by
  cases κ with
  | atom s =>
    exact ⟨_, sI.1 w hw s x hx (aPt (t := t) (n := n) (.atom s))
      ((den_succ (atomT_de s) _).mpr ((atomT_den s _).mpr ⟨rfl, rfl⟩))⟩
  | dom kk i =>
    obtain ⟨T, -, kT⟩ := kind_run (t := t) (n := n) (domKind_mem kk) (m := (level t n).K + 23) (Nat.le_refl _)
    obtain ⟨v, -, pv⟩ := kT.wit (domKind_ne_atom kk)
    exact ⟨_, sI.2.1 w hw kk i x hx v pv⟩

theorem inner_empty_iff {b inner : Term} (sI : InnerSem t n b inner) :
    (∀ p : PN t (n + 1), ¬denD inner p) ↔
      ∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true → w = wNone := by
  constructor
  · intro h w hw
    funext κ
    cases e : w κ with
    | none => rfl
    | some x => obtain ⟨p, hp⟩ := inner_of_value sI hw e; exact absurd hp (h p)
  · intro h p hp
    obtain ⟨-, -, k, x, -, w, hw, κ, wκ⟩ := sI.2.2 p hp
    rw [h w hw] at wκ
    cases wκ

theorem lTy_nil_sub {inner : Term} (dI : DE (level t (n + 1)).E inner) (nil : Bool) (k : Int) :
    SubN t (n + 2) (lTy nil k inner) nilT ↔ ∀ p : PN t (n + 1), ¬denD inner p := by
  constructor
  · intro h y hy
    let v : LV (level t (n + 2)).V := ⟨[y], nilPt (t := t) (n := n + 1)⟩
    have lv : ListVal (level t (n + 2)).tl v := ⟨by simp [v], fun h => by
      change tlD (nilPt (t := t) (n := n + 1)) at h
      simp [tlD, nilPt, bPt] at h⟩
    have hq : denD (lTy nil k inner) (lpt v lv) := by
      rw [lTy_den _ _ dI]
      refine Or.inr ⟨rfl, fun v' hv' => (dn_nil_list dI k hv').mp ((dn_nil_list dI k rfl).mpr ⟨fun y' my' => ?_, ?_⟩)⟩
      · have e : y' = y := List.mem_singleton.mp my'
        rw [e]; exact hy
      · exact nilPt_den
    have := (nilT_den _).mp (h _ hq)
    simp [lpt] at this
  · intro h q hq
    rw [lTy_den _ _ dI] at hq
    rcases hq with ⟨-, hb, h2⟩ | ⟨hl, hv⟩
    · exact (nilT_den q).mpr ⟨hb, h2⟩
    · obtain ⟨v, ⟨ne, -⟩, ev⟩ := list_val q hl
      obtain ⟨y, my⟩ := List.exists_mem_of_ne_nil v.xs ne
      exact absurd ((hv v ev).1 y my) (h _)

theorem nilT_sub_lTy {inner : Term} (dI : DE (level t (n + 1)).E inner) (nil : Bool) (k : Int) :
    SubN t (n + 2) nilT (lTy nil k inner) ↔ nil = Bool.true := by
  constructor
  · intro h
    have := (lTy_den _ _ dI _).mp (h _ (nilPt_den (t := t) (n := n + 2)))
    rcases this with ⟨h, -⟩ | ⟨hl, -⟩
    · exact h
    · simp [nilPt, bPt] at hl
  · intro h q hq
    rw [lTy_den _ _ dI]
    exact Or.inl ⟨h, (nilT_den q).mp hq⟩

/-- `map_split_keys_and_domains/1` on `term()` selects every key. -/
theorem term_split {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.atom "term") =
        .ok (splitT rs neg ds) ∧ SplitOk rs neg ds ∧ ∀ κ, SplitKey rs neg ds κ := by
  obtain ⟨T, rT, sT, -, allT⟩ := termT (level t n)
  have dT : DE (level t n).E (.map T) := Or.inr ⟨T, rfl, sT⟩
  have hU : ∀ S, mapLookup T (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s := by
    intro S hS q hq
    obtain ⟨T', rT', -, hat, -, -⟩ := unfolded_term_fields
    rw [rT] at rT'; cases rT'
    rw [hat] at hS; simp at hS
  obtain ⟨rs, neg, ds, run, ok, -, -, sa, sd⟩ := split_map dT hU hm
  refine ⟨rs, neg, ds, ?_, ok, fun κ => ?_⟩
  · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
    simp [rT, run]
  · cases κ with
    | atom s => exact (sa s).mpr (allT _)
    | dom kk i =>
      obtain ⟨K₀, -, kT⟩ := kind_run (t := t) (n := n) (domKind_mem kk) (m := (level t n).K + 23) (Nat.le_refl _)
      obtain ⟨v, -, pv⟩ := kT.wit (domKind_ne_atom kk)
      exact (sd kk i).mpr ⟨v, allT v, pv⟩

theorem lTy_mono {A B : Term} (dA : DE (level t (n + 1)).E A) (dB : DE (level t (n + 1)).E B)
    (incl : ∀ y : PN t (n + 1), denD A y → denD B y) {nA nB : Bool} (hn : nA = Bool.true → nB = Bool.true) (kA kB : Int) :
    SubN t (n + 2) (lTy nA kA A) (lTy nB kB B) := by
  intro q hq
  rw [lTy_den _ _ dA] at hq
  rw [lTy_den _ _ dB]
  rcases hq with ⟨h, hb⟩ | ⟨hl, h⟩
  · exact Or.inl ⟨hn h, hb⟩
  · exact Or.inr ⟨hl, fun v hv => ⟨fun y my => incl _ ((h v hv).1 y my), (h v hv).2⟩⟩

theorem nilT_sub_true {B : Term} (dB : DE (level t (n + 1)).E B) (kB : Int) : SubN t (n + 2) nilT (lTy Bool.true kB B) :=
  (nilT_sub_lTy dB Bool.true kB).mpr rfl

end

end Elixir.STTDescrProofsTest.Nest
