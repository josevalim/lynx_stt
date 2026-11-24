namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Whether `map_update/5` finds the keys it updates, and the domains it reports missing. -/

/-- `map_update_get_domains/5` finds a domain some line holds, or the atom domain when the callback finds a named atom
key, and reports the domains no line holds missing. -/
theorem upd_found (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (cb : Term) (c : Bool) (hc : (D (n + 3)).pure cb #[] = .ok (boolAtom c))
    (Ds : List String) {acc : Term} (ha : E acc) :
    ∃ (f : Bool) (val mis : List Term) (T : Term),
      Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 4)) (Term.list lines) (Term.list (Ds.map Term.atom))
        acc (.atom "true") cb = .ok (.tuple #[boolAtom f, Term.list val, Term.list mis, T]) ∧
      (f = Bool.true ↔ (∃ s ∈ Ds, ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨ ("atom" ∈ Ds ∧ c = Bool.true)) ∧
      ∀ d, d ∈ mis ↔ ∃ s ∈ Ds, d = .atom s ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s x := by
  obtain ⟨r, ⟨f, val, mis, T, rfl, hT, fD, mD⟩, run⟩ := foldl_rel_at (m := n + 4) "Elixir.Module.Types.Descr"
    "-map_update_get_domains/5-fun-0-" #[Term.list lines, .atom "true", cb]
    (fun pre a => ∃ (f : Bool) (val mis : List Term) (T : Term), a = .tuple #[boolAtom f, Term.list val, Term.list mis, T] ∧
      E T ∧ (f = Bool.true ↔ (∃ s, .atom s ∈ pre ∧ ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨
        (.atom "atom" ∈ pre ∧ c = Bool.true)) ∧
      (∀ d, d ∈ mis ↔ ∃ s, .atom s ∈ pre ∧ d = .atom s ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s x))
    (Ds.map Term.atom) (fun pre x a mx ⟨f, val, mis, T, ea, hT, fD, mD⟩ => by
      subst ea
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp mx
      obtain ⟨g, rg, hg, sg⟩ := get_domain1 ef (n := n + 3) (by omega) lines hl s
      obtain ⟨b, rb, sb⟩ := ef.empty1 (m := n + 3) (by omega) hg
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] hT hg (m := n + 3) (by omega)
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure]
      simp only [Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5», rg, rb, Lynx.Except.ok_bind,
        Elixir.Module.Types.Descr.«opt_union/2», ru, Erlang.erlang.«==/2»]
      have heldI : b = Bool.false ↔ ∃ L ∈ lines, ∃ x, LineTag den L s x := by
        constructor
        · intro hb
          subst hb
          obtain ⟨x, hx⟩ : ∃ x, den g x := Classical.byContradiction fun h => by
            have := sb.mpr fun y hy => h ⟨y, hy⟩; cases this
          obtain ⟨L, mL, hL⟩ := (sg x).mp hx
          exact ⟨L, mL, x, hL⟩
        · rintro ⟨L, mL, x, hx⟩
          cases b
          · rfl
          · exact absurd ((sg x).mpr ⟨L, mL, hx⟩) (sb.mp rfl x)
      -- The facts on the extended prefix.
      have memA : ∀ s', .atom s' ∈ pre ++ [Term.atom s] ↔ .atom s' ∈ pre ∨ s' = s := fun s' => by simp
      have fTrue : (∃ L ∈ lines, ∃ x, LineTag den L s x) → ((∃ s', .atom s' ∈ pre ++ [Term.atom s] ∧
          ∃ L ∈ lines, ∃ x, LineTag den L s' x) ∨ (.atom "atom" ∈ pre ++ [Term.atom s] ∧ c = Bool.true)) :=
        fun h => Or.inl ⟨s, by simp, h⟩
      have fSame : (¬∃ L ∈ lines, ∃ x, LineTag den L s x) → (s ≠ "atom" ∨ c = Bool.false) →
          ((f = Bool.true) ↔ ((∃ s', .atom s' ∈ pre ++ [Term.atom s] ∧ ∃ L ∈ lines, ∃ x, LineTag den L s' x) ∨
            (.atom "atom" ∈ pre ++ [Term.atom s] ∧ c = Bool.true))) := fun nh hc' => by
        rw [fD]
        constructor
        · rintro (⟨s', m', h⟩ | ⟨m', hc''⟩)
          · exact Or.inl ⟨s', by simp [m'], h⟩
          · exact Or.inr ⟨by simp [m'], hc''⟩
        · rintro (⟨s', m', h⟩ | ⟨m', hc''⟩)
          · rcases (memA s').mp m' with m' | rfl
            · exact Or.inl ⟨s', m', h⟩
            · exact absurd h nh
          · rcases (memA "atom").mp m' with m' | e
            · exact Or.inr ⟨m', hc''⟩
            · rcases hc' with h | h
              · exact absurd e.symm h
              · rw [h] at hc''; cases hc''
      have misAdd : (¬∃ L ∈ lines, ∃ x, LineTag den L s x) → ∀ d, d ∈ Term.atom s :: mis ↔
          ∃ s', .atom s' ∈ pre ++ [Term.atom s] ∧ d = .atom s' ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s' x := by
        intro nh d
        rw [List.mem_cons, mD]
        constructor
        · rintro (rfl | ⟨s', m', e, h⟩)
          · exact ⟨s, by simp, rfl, nh⟩
          · exact ⟨s', by simp [m'], e, h⟩
        · rintro ⟨s', m', rfl, h⟩
          rcases (memA s').mp m' with m' | rfl
          · exact Or.inr ⟨s', m', rfl, h⟩
          · exact Or.inl rfl
      have misKeep : (∃ L ∈ lines, ∃ x, LineTag den L s x) → ∀ d, d ∈ mis ↔
          ∃ s', .atom s' ∈ pre ++ [Term.atom s] ∧ d = .atom s' ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s' x := by
        intro hh d
        rw [mD]
        constructor
        · rintro ⟨s', m', e, h⟩
          exact ⟨s', by simp [m'], e, h⟩
        · rintro ⟨s', m', rfl, h⟩
          rcases (memA s').mp m' with m' | rfl
          · exact ⟨s', m', rfl, h⟩
          · exact absurd hh h
      by_cases sa : s = "atom"
      · subst sa
        cases b
        · refine ⟨_, ⟨Bool.true, .atom "atom" :: val, mis, u, rfl, hu, ⟨fun _ => fTrue (heldI.mp rfl), fun _ => rfl⟩,
            misKeep (heldI.mp rfl)⟩, ?_⟩
          simp [boolAtom, Lynx.Term.isMember, Term.list]
        · have nh : ¬∃ L ∈ lines, ∃ x, LineTag den L "atom" x := fun h => by have := heldI.mpr h; cases this
          cases c
          · refine ⟨_, ⟨f, val, .atom "atom" :: mis, T, rfl, hT, fSame nh (Or.inr rfl), misAdd nh⟩, ?_⟩
            simp [boolAtom, Lynx.Term.isMember, Term.list, hc, Erlang.erlang.«/=/2», Lynx.Except.guard]
          · refine ⟨_, ⟨Bool.true, val, .atom "atom" :: mis, T, rfl, hT,
              ⟨fun _ => Or.inr ⟨by simp, rfl⟩, fun _ => rfl⟩, misAdd nh⟩, ?_⟩
            simp [boolAtom, Lynx.Term.isMember, Term.list, hc, Erlang.erlang.«/=/2», Lynx.Except.guard]
      · have ne : Term.compare (Term.fuel (.atom s) (.atom "atom")) (.atom s) (.atom "atom") ≠ .eq := by
          rw [atoms_cmp]; exact fun e => sa (Std.compare_eq_iff_eq.mp e)
        cases b
        · refine ⟨_, ⟨Bool.true, .atom s :: val, mis, u, rfl, hu, ⟨fun _ => fTrue (heldI.mp rfl), fun _ => rfl⟩,
            misKeep (heldI.mp rfl)⟩, ?_⟩
          simp [boolAtom, Lynx.Term.isMember, Term.list, ne]
        · have nh : ¬∃ L ∈ lines, ∃ x, LineTag den L s x := fun h => by have := heldI.mpr h; cases this
          refine ⟨_, ⟨f, val, .atom s :: mis, T, rfl, hT, fSame nh (Or.inl sa), misAdd nh⟩, ?_⟩
          simp [boolAtom, Lynx.Term.isMember, Term.list, ne])
    (.tuple #[.atom "false", .nil, .nil, acc]) ⟨Bool.false, [], [], acc, rfl, ha, by simp, by simp⟩
  refine ⟨f, val, mis, T, ?_, ?_, fun d => ?_⟩
  · simpa [Elixir.Module.Types.Descr.«map_update_get_domains/5», boolAtom, Term.list] using run
  · rw [fD]; simp
  · rw [mD]; simp

/-- `++/2` of a list and any term. -/
theorem append_any (a : List Term) (b : Term) :
    Erlang.erlang.«++/2» (Term.list a) b = .ok (a.foldr Term.cons b) := by
  induction a with
  | nil => simp [Erlang.erlang.«++/2», Term.list]
  | cons h t ih => simp [Term.list, Erlang.erlang.«++/2»] at ih ⊢; simp [ih]

/-- `map_update_named_keys/8` for a constant, asking for the old values on a static type: the errors it adds are
`badkey` errors, and it finds a key when forcing, or when some map holds a value there and no map lacks it. -/
theorem named_flag (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term) (fld : Term) {md : String}
    (hmd : Mode md) (req : Bool) (bd : Term)
    (hk : ∀ a, ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) bd (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) :
    ∀ (ks : List String) (T B : Term) (Er : List Term) (f : Bool), E T →
      ∃ (T' B' : Term) (extra : List Term) (f' : Bool),
        Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[T, B, Term.list Er, boolAtom f])
          (Term.list lines) (Term.list (ks.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
          (boolAtom req) (.atom "true") (.atom "true") bd =
          .ok (.tuple #[T', B', Term.list (extra ++ Er), boolAtom f']) ∧ E T' ∧
        (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧
        (f' = Bool.true ↔ f = Bool.true ∨ (md = "force" ∧ ks ≠ []) ∨
          ∃ a ∈ ks, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ ¬∃ L ∈ lines, LongM den L a none) := by
  have loop : ∀ (ks : List String) (T B : Term) (Er : List Term) (f : Bool), E T →
      ∃ (T' B' : Term) (extra : List Term) (f' : Bool),
        Erlang.lists.«foldl_1/3» (D (n + 4))
          (.function "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, .tuple #[.tuple #[.atom "constant", fld], .atom md], boolAtom req, .atom "true", bd,
              .atom "true", boolAtom (decide (md = "force"))])
          (.tuple #[T, B, Term.list Er, boolAtom f]) (Term.list (ks.map Term.atom)) =
          .ok (.tuple #[T', B', Term.list (extra ++ Er), boolAtom f']) ∧ E T' ∧
        (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧
        (f' = Bool.true ↔ f = Bool.true ∨ (md = "force" ∧ ks ≠ []) ∨
          ∃ a ∈ ks, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ ¬∃ L ∈ lines, LongM den L a none) := by
    intro ks
    induction ks with
    | nil =>
      intro T B Er f hT
      exact ⟨T, B, [], f, by simp [Erlang.lists.«foldl_1/3», Term.list], hT, by simp, by simp⟩
    | cons a rest ih =>
      intro T B Er f hT
      obtain ⟨ba, F, rb, hF, sF⟩ := hk a
      obtain ⟨t, o, rfl, ht⟩ := hF
      obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ht hT (m := n + 3) (by omega)
      have someE : (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ↔ e = Bool.false := by
        constructor
        · rintro ⟨L, mL, x, hx⟩
          cases e
          · rfl
          · exact absurd ((sF (some x)).mpr ⟨L, mL, hx⟩ |> (fieldSem_mk.mp) |>.elim (fun h => by cases h.1)
              (fun ⟨y, ey, hy⟩ => by cases ey; exact hy)) (se.mp rfl x)
        · intro he
          subst he
          obtain ⟨x, hx⟩ : ∃ x, den t x := Classical.byContradiction fun h => by
            have := se.mpr fun y hy => h ⟨y, hy⟩; cases this
          obtain ⟨L, mL, hL⟩ := (sF (some x)).mp (fieldSem_mk.mpr (Or.inr ⟨x, rfl, hx⟩))
          exact ⟨L, mL, x, hL⟩
      have noneE : (∃ L ∈ lines, LongM den L a none) ↔ o = Bool.true := by
        rw [← sF, fieldSem_mk]; simp
      -- One step of the fold.
      let T₁ := if md ≠ "force" ∧ e = Bool.true then T else u
      let e₁ : List Term := if md ≠ "force" ∧ req = Bool.true ∧ (e = Bool.true ∨ o = Bool.true) then
        [.tuple #[.atom "badkey", .atom a]] else []
      let f₁ : Bool := if md = "force" then Bool.true else if e then f else f || !o
      have hT₁ : E T₁ := by simp only [T₁]; split; exact hT; exact hu
      have step : (D (n + 4)).pure (.function "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, .tuple #[.tuple #[.atom "constant", fld], .atom md], boolAtom req, .atom "true", bd,
              .atom "true", boolAtom (decide (md = "force"))]) #[.atom a, .tuple #[T, B, Term.list Er, boolAtom f]] =
          .ok (.tuple #[T₁, ba.foldr Term.cons B, Term.list (e₁ ++ Er), boolAtom f₁]) := by
        have rb' : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
            (.tuple #[.tuple #[.atom "constant", fld], .atom md]) bd (.atom "true") =
            .ok (.tuple #[Term.list ba, .tuple #[t, boolAtom o]]) := rb
        simp only [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
          Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»]
        rw [rb']
        rcases hmd with rfl | rfl | rfl <;> cases e <;> cases o <;> cases req <;> cases f <;>
          simp [T₁, e₁, f₁, re, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2», ru, boolAtom,
            Lynx.Except.andAlso, Lynx.Except.orElse, Erlang.erlang.«not/1», append_list, append_any, Term.list]
      obtain ⟨T', B', extra, f', r₁, hT', hx, hf⟩ := ih T₁ (ba.foldr Term.cons B) (e₁ ++ Er) f₁ hT₁
      refine ⟨T', B', extra ++ e₁, f', ?_, hT', fun x mx => ?_, ?_⟩
      · rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only [Term.list, List.map] at r₁ ⊢
        simp [Term.list] at step
        simp [step, r₁, List.append_assoc]
      · rcases List.mem_append.mp mx with mx | mx
        · exact hx x mx
        · simp only [e₁] at mx; split at mx
          · rw [List.mem_singleton] at mx; exact ⟨a, mx⟩
          · cases mx
      · rw [hf]
        have f₁E : f₁ = Bool.true ↔ f = Bool.true ∨ md = "force" ∨
            ((∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ ¬∃ L ∈ lines, LongM den L a none) := by
          rw [someE, noneE]
          simp only [f₁]
          by_cases hf : md = "force" <;> cases e <;> cases o <;> cases f <;> simp [hf]
        rw [f₁E]
        constructor
        · rintro ((h | h | h) | ⟨h₁, -⟩ | ⟨a', ma, h⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨h, by simp⟩)
          · exact Or.inr (Or.inr ⟨a, List.mem_cons_self, h⟩)
          · exact Or.inr (Or.inl ⟨h₁, by simp⟩)
          · exact Or.inr (Or.inr ⟨a', List.mem_cons_of_mem _ ma, h⟩)
        · rintro (h | ⟨h, -⟩ | ⟨a', ma, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inl h))
          · rcases List.mem_cons.mp ma with rfl | ma
            · exact Or.inl (Or.inr (Or.inr h))
            · exact Or.inr (Or.inr ⟨a', ma, h⟩)
  intro ks T B Er f hT
  obtain ⟨T', B', extra, f', r₁, hT', hx, hf⟩ := loop ks T B Er f hT
  refine ⟨T', B', extra, f', ?_, hT', hx, hf⟩
  rcases hmd with rfl | rfl | rfl
  all_goals
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse, boolAtom]
    rcases ks with _ | ⟨k, t⟩
    · simp [Term.list, Erlang.lists.«foldl_1/3»] at r₁ ⊢
      simpa [boolAtom] using r₁
    · simp only [Term.list, List.map] at r₁ ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at r₁; simpa [boolAtom] using r₁

/-- The type `domain_key_to_descr/1` gives a kind of keys. -/
def domDescr (s : String) : Term :=
  match Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom s) with
  | .ok y => y
  | .error _ => .nil

/-- The error of a missing domain. -/
def bdErr : Term → Term
  | .atom s => .tuple #[.atom "baddomain", domDescr s]
  | _ => .nil

/-- `map_update_any_named_key?/2` finds a named key some map holds a value at. -/
theorem any_named_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (ks : List String) :
    ∃ c : Bool, Elixir.Module.Types.Descr.«map_update_any_named_key?/2» (D (n + 4)) (Term.list lines)
      (Term.list (ks.map Term.atom)) = .ok (boolAtom c) ∧
      (c = Bool.true ↔ ∃ a ∈ ks, ∃ L ∈ lines, ∃ x, LongM den L a (some x)) := by
  classical
  let res : Term → Bool := fun k => match k with
    | .atom a => decide (∃ L ∈ lines, ∃ x, LongM den L a (some x))
    | _ => Bool.false
  refine ⟨(ks.map Term.atom).any res, ?_, ?_⟩
  · simp only [Elixir.Module.Types.Descr.«map_update_any_named_key?/2»]
    refine any_list _ _ _ _ res _ fun x mx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp mx
    obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
    obtain ⟨ty, o, rfl, hty⟩ := hF
    obtain ⟨b, rb, sb⟩ := ef.empty1 (m := n + 3) (by omega) hty
    have e : res (.atom a) = !b := by
      simp only [res]
      cases b
      · obtain ⟨x, hx⟩ : ∃ x, den ty x := Classical.byContradiction fun h => by
          have := sb.mpr fun y hy => h ⟨y, hy⟩; cases this
        obtain ⟨L, mL, hL⟩ := (sF (some x)).mp (fieldSem_mk.mpr (Or.inr ⟨x, rfl, hx⟩))
        simp only [Bool.not_false, decide_eq_true_eq]
        exact ⟨L, mL, x, hL⟩
      · simp only [Bool.not_true, decide_eq_false_iff_not]
        rintro ⟨L, mL, x, hL⟩
        have := (sF (some x)).mpr ⟨L, mL, hL⟩
        rw [fieldSem_mk] at this
        rcases this with ⟨h, -⟩ | ⟨y, ey, hy⟩
        · cases h
        · cases ey; exact sb.mp rfl _ hy
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_any_named_key?/2-fun-0-/1».pure, e]
    cases b <;> simp [Elixir.Module.Types.Descr.«-map_update_any_named_key?/2-fun-0-/2», rF, rb,
      Erlang.erlang.«not/1», boolAtom]
  · simp [res]

/-- `map_update_static_dnf/6` for a constant, asking for the old values: the errors are `badkey` errors and the
missing domains, which are those no line holds, and except when forcing, it finds a domain some line holds, a named
atom key some map holds a value at when updating atoms outside a set, or a named key every map holds a value at. -/
theorem dnf_flag (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) {md : String} (hmd : Mode md)
    (bdd : Term) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (rk : List String)
    (neg : Term) (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (R : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) neg bdd = .ok (Term.list (R.map Term.atom)))
    (hRk : R = [] ∨ rk = [])
    (hk : ∀ (bd : Bool) a, ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
      (.atom "true") (.atom "true") = .ok r) :
    ∃ (T Y : Term) (extra mis : List Term) (f : Bool), r = .tuple #[T, Y, Term.list (extra ++ mis.map bdErr), boolAtom f] ∧
      (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧
      (∀ d, d ∈ mis ↔ ∃ s ∈ Ds, d = .atom s ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s x) ∧
      (md ≠ "force" → (f = Bool.true ↔ (∃ s ∈ Ds, ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨
        ("atom" ∈ Ds ∧ ∃ a ∈ rk ++ R, ∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∨
        ∃ a ∈ rk ++ R, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ ¬∃ L ∈ lines, LongM den L a none)) := by
  classical
  have m₀ : Erlang.erlang.«--/2» (Term.list (R.map Term.atom)) .nil = .ok (Term.list (R.map Term.atom)) := by
    simp [Erlang.erlang.«--/2», Term.properList?]
  have m₁ : Erlang.erlang.«--/2» (Term.list (R.map Term.atom)) (Term.list (rk.map Term.atom)) =
      .ok (Term.list (R.map Term.atom)) := by
    rcases hRk with rfl | rfl
    · have e0 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => compareExact (x.fuel y) x y == .eq) acc)
          ([] : List Term) L = [] := fun L => by induction L <;> simp_all
      simp [Erlang.erlang.«--/2», e0, Term.properList?, Term.list]
    · simp [Erlang.erlang.«--/2», Term.properList?, Term.list]
  have m₂ : Erlang.erlang.«++/2» (Term.list (R.map Term.atom)) .nil = .ok (Term.list (R.map Term.atom)) := by
    simpa using append_list (R.map Term.atom) []
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) .nil = .ok (Term.list (Ds.map Term.atom)) := by
    simpa using append_list (Ds.map Term.atom) []
  obtain ⟨c, hc, sc⟩ := any_named_sem ef (n := n) (by omega) lines hl (rk ++ R)
  have hcb : (D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simpa [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, fD₁, mD₁⟩ := upd_found ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ c hcb Ds ef.none
  obtain ⟨f₁', val₁', mis₁', T₁', r₁', hT₁, -, -, -⟩ := upd_domains ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  have eT : T₁' = T₁ := by
    have := r₁.symm.trans r₁'
    simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at this
    exact this.2.2.2.1.symm
  rw [eT] at hT₁
  clear r₁' eT
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list (mis₁.map bdErr)) := by
    refine map_list _ _ _ _ bdErr _ fun x mx => ?_
    obtain ⟨s, ms, rfl, -⟩ := (mD₁ x).mp mx
    obtain ⟨y, hy⟩ := domain_descr_ok (hDs s ms)
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-1-/1».pure]
    simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-1-/1», hy, bdErr, domDescr]
  have r₁'' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  -- The found flag of the named keys, from the domains.
  have fSem : ∀ f₀ f₂ f₃ : Bool, (f₀ = Bool.true ↔ f₁ = Bool.true) →
      (f₂ = Bool.true ↔ f₀ = Bool.true ∨ (md = "force" ∧ rk ≠ []) ∨
        ∃ a ∈ rk, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ ¬∃ L ∈ lines, LongM den L a none) →
      (f₃ = Bool.true ↔ f₂ = Bool.true ∨ (md = "force" ∧ R ≠ []) ∨
        ∃ a ∈ R, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ ¬∃ L ∈ lines, LongM den L a none) →
      md ≠ "force" → (f₃ = Bool.true ↔ (∃ s ∈ Ds, ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨
        ("atom" ∈ Ds ∧ ∃ a ∈ rk ++ R, ∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∨
        ∃ a ∈ rk ++ R, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ ¬∃ L ∈ lines, LongM den L a none) := by
    intro f₀ f₂ f₃ e₀ e₂ e₃ nf
    rw [e₃, e₂, e₀, fD₁, sc]
    simp only [nf, false_and, false_or, List.mem_append]
    constructor
    · rintro (((h | ⟨ha, a, ma, hh⟩) | ⟨a, ma, hh⟩) | ⟨a, ma, hh⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨ha, a, ma, hh⟩)
      · exact Or.inr (Or.inr ⟨a, Or.inl ma, hh⟩)
      · exact Or.inr (Or.inr ⟨a, Or.inr ma, hh⟩)
    · rintro (h | ⟨ha, a, ma, hh⟩ | ⟨a, ma | ma, hh⟩)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr ⟨ha, a, ma, hh⟩))
      · exact Or.inl (Or.inr ⟨a, ma, hh⟩)
      · exact Or.inr ⟨a, ma, hh⟩
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h
  simp only [splitT] at h
  have hmd₀ := hmd
  obtain ⟨md', hmd'⟩ : ∃ m, m = md := ⟨md, rfl⟩
  rcases hmd with rfl | rfl | rfl <;>
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», hR, m₀, m₁, m₂, m₃, mv,
      r₁'', r₂', rE', Lynx.Except.andAlso] at h
  all_goals
    obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨v44, -, h⟩ := bind_ok h
    obtain ⟨v51, h51, h⟩ := bind_ok h
    -- The found flag the named keys start with.
    obtain ⟨f₀, rfl, ef₀⟩ : ∃ f₀ : Bool, v51 = boolAtom f₀ ∧ (md' ≠ "force" → (f₀ = Bool.true ↔ f₁ = Bool.true)) := by
      subst hmd'
      cases f₁ <;> simp [Lynx.Except.orElse, boolAtom] at hx <;> subst hx <;>
        (split at h51 <;> simp [Lynx.Except.orElse] at h51 <;> subst h51 <;>
          first
          | exact ⟨Bool.true, rfl, by simp⟩
          | exact ⟨Bool.false, rfl, by simp⟩
          | (split at h51 <;> simp at h51 <;> subst h51 <;>
              first | exact ⟨Bool.true, rfl, by simp⟩ | exact ⟨Bool.false, rfl, by simp⟩))
    obtain ⟨X, hX, h⟩ := bind_ok h
    have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
      clear h
      simp only [bind, Except.bind, Except.tryWith] at hX
      repeat' split at hX
      all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
      all_goals done
    obtain ⟨B96, -, h⟩ := bind_ok h
    obtain ⟨r97, h97, h⟩ := bind_ok h
    obtain ⟨T', B', extra, f₂, e97, hT', hx₁, hf₂⟩ := named_flag ef (n := n + 2) (by omega) lines fld hmd₀ Bool.true
      (.atom "true") (fun a => hk Bool.true a) rk T₁ B96 (mis₁.map bdErr) f₀ hT₁
    have e₁ := h97.symm.trans e97
    cases e₁
    obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
      rcases hb with hb | hb
      · exact ⟨Bool.false, hb⟩
      · exact ⟨Bool.true, hb⟩
    rw [ebd] at h
    obtain ⟨r5, h5, h⟩ := bind_ok h
    obtain ⟨T'', B'', extra', f₃, e5, -, hx₂, hf₃⟩ := named_flag ef (n := n + 2) (by omega) lines fld hmd₀ Bool.false
      (boolAtom bd) (fun a => hk bd a) R T' B' (extra ++ mis₁.map bdErr) f₂ hT'
    have e₂ := h5.symm.trans e5
    cases e₂
    obtain ⟨u, -, h⟩ := bind_ok h
    have fin : md' ≠ "force" → (f₃ = Bool.true ↔ (∃ s ∈ Ds, ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨
        ("atom" ∈ Ds ∧ ∃ a ∈ rk ++ R, ∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∨
        ∃ a ∈ rk ++ R, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ ¬∃ L ∈ lines, LongM den L a none) := by
      subst hmd'
      exact fun nf => fSem f₀ f₂ f₃ (ef₀ nf) hf₂ hf₃ nf
    have bk : ∀ e ∈ extra' ++ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a] := fun e me => by
      rcases List.mem_append.mp me with me | me
      · exact hx₂ e me
      · exact hx₁ e me
    subst hmd'
    split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, extra' ++ extra, mis₁, f₃, by rw [List.append_assoc], bk, mD₁, fin⟩)

/-- `dnf_flag` on the lines of a map field: the missing domains other than atoms are the kinds no map holds, and with
no named atoms, except when forcing, it finds a key exactly when some map holds a value at a key of the split. -/
theorem dnf_flag_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) {md : String} (hmd : Mode md)
    (hkL : ∀ lines : List Term, (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → ∀ (bd : Bool) a,
      ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5))
        (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    {b : Term} (fb : MField E b) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Ds : List String}
    {neg : Term} (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = []) (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
      (.atom "true") (.atom "true") = .ok r) :
    ∃ (T Y : Term) (extra mis : List Term) (f : Bool), r = .tuple #[T, Y, Term.list (extra ++ mis.map bdErr), boolAtom f] ∧
      (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧ (∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s) ∧
      (∀ s ∈ Ds, s ≠ "atom" → (.atom s ∈ mis ↔ ¬∃ w, denMF E den b w = Bool.true ∧ HasKind w s)) ∧
      (md ≠ "force" → rk = [] → (f = Bool.true ↔ ∃ x w, denMF E den b w = Bool.true ∧
        ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧ w κ = some x)) := by
  have hDs : ∀ s ∈ Ds, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  obtain ⟨R, rR, hR, swR⟩ := neg_keys_split (den := den) ef fb (n + 5) ok
  obtain ⟨R', rfl⟩ := atoms_of fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩
  have hRk : R' = [] ∨ rk = [] := by
    cases R' with
    | nil => exact Or.inl rfl
    | cons r rs =>
      obtain ⟨s, -, N, eN, -⟩ := hR _ List.mem_cons_self
      exact Or.inr (nr N eN)
  obtain ⟨T, Y, extra, mis, f, rfl, hx, hmis, hf⟩ := dnf_flag ef hn fld hmd b lines hl rk neg Ds hDs R' rR hRk
    (hkL lines hl) r h
  have heldE : ∀ s ∈ Ds, s ≠ "atom" → ((∃ L ∈ lines, ∃ x, LineTag den L s x) ↔
      ∃ w, denMF E den b w = Bool.true ∧ HasKind w s) := fun s ms sa => by
    rw [← kind_held_ne ef hl (hDs s ms) sa]
    exact ⟨fun h => let ⟨u, hu, hk⟩ := h.2 sa; ⟨u, (sl u).mpr hu, hk⟩,
      fun ⟨u, hu, hk⟩ => ⟨fun e => absurd e sa, fun _ => ⟨u, (sl u).mp hu, hk⟩⟩⟩
  refine ⟨T, Y, extra, mis, f, rfl, hx, fun d md' => ?_, fun s ms sa => ?_, fun nf rk0 => ?_⟩
  · obtain ⟨s, ms, e, -⟩ := (hmis d).mp md'; exact ⟨s, ms, e⟩
  · rw [hmis, ← heldE s ms sa]
    constructor
    · rintro ⟨s', ms', e, h⟩; cases e; exact h
    · intro h; exact ⟨s, ms, rfl, h⟩
  · subst rk0
    rw [hf nf]
    have atomR : ∀ a ∈ R', "atom" ∈ Ds := fun a ma => by
      obtain ⟨s, -, N, eN, -⟩ := hR _ (List.mem_map_of_mem ma)
      obtain ⟨s', ms', e⟩ := List.mem_map.mp (ok.hatom.mpr ⟨N, eN⟩)
      cases e; exact ms'
    have pe := fun x => pieces_sem ef lines hl sl ok hR swR x
    simp only [List.map_nil, List.nil_append, List.not_mem_nil, false_and, exists_false, false_or] at pe ⊢
    constructor
    · rintro (⟨s, ms, L, mL, x, hx'⟩ | ⟨-, a, ma, L, mL, x, hx'⟩ | ⟨a, ma, ⟨L, mL, x, hx'⟩, -⟩)
      · exact ⟨x, (pe x).mp (Or.inr ⟨s, List.mem_map_of_mem ms, L, mL, hx'⟩)⟩
      · exact ⟨x, (pe x).mp (Or.inl ⟨a, List.mem_map_of_mem ma, L, mL, hx'⟩)⟩
      · exact ⟨x, (pe x).mp (Or.inl ⟨a, List.mem_map_of_mem ma, L, mL, hx'⟩)⟩
    · rintro ⟨x, hw⟩
      rcases (pe x).mpr hw with ⟨a, ma, L, mL, hx'⟩ | ⟨s, ms, L, mL, hx'⟩
      · obtain ⟨a', ma', e⟩ := List.mem_map.mp ma
        injection e with e; subst e
        exact Or.inr (Or.inl ⟨atomR a' ma', a', ma', L, mL, x, hx'⟩)
      · obtain ⟨s', ms', e⟩ := List.mem_map.mp ms
        injection e with e; subst e
        exact Or.inl ⟨s', ms', L, mL, x, hx'⟩

/-- `map_update_static/5` for a constant at a split of static keys, asking for the old values: `:badmap`, or the
errors and found flag `dnf_flag_sem` gives. -/
theorem flag_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) {md : String} (hmd : Mode md)
    (hkL : ∀ lines : List Term, (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → ∀ (bd : Bool) a,
      ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5))
        (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) (res : Term)
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") = .ok res) :
    res = .atom "badmap" ∨ ∃ (T Y : Term) (extra mis : List Term) (f : Bool),
      res = .tuple #[T, Y, Term.list (extra ++ mis.map bdErr), boolAtom f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
      (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧ (∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s) ∧
      (∀ s ∈ Ds, s ≠ "atom" → (.atom s ∈ mis ↔ ¬∃ w, denMF E den b w = Bool.true ∧ HasKind w s)) ∧
      (md ≠ "force" → rk = [] → (f = Bool.true ↔ ∃ x w, denMF E den b w = Bool.true ∧
        ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧ w κ = some x)) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, ri⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have ri : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 6)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := ri (n + 6) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := ri.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 6) (by omega) rfl g sl
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
      have unf : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) (.tuple #[.integer k, tag, fieldsTerm l])
            (Term.list [Term.tuple #[tag, fieldsTerm l, Term.list []]]) (splitT (rk.map Term.atom) neg (Ds.map Term.atom))
            (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom, Term.list]
      rw [unf] at run
      obtain ⟨T, Y, extra, mis, f, e, hx, hm, hmk, hf⟩ := dnf_flag_sem ef hn fld hmd hkL fb _ hl inB ok nr res run
      exact Or.inr ⟨T, Y, extra, mis, f, e, ⟨w₀, (sem w₀).mpr h₀⟩, hx, hm, hmk, hf⟩
    · left
      unfold Elixir.Module.Types.Descr.«map_update_static/5» at run
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom] at run
      exact run.symm
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
      (m := n + 6) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    cases lines with
    | nil =>
      left
      unfold Elixir.Module.Types.Descr.«map_update_static/5» at run
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simp [getMapKeys_single, hb, rl, Term.list] at run; exact run.symm
      · simp [getMapKeys_single, hb, rl, Term.list] at run; exact run.symm
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simp [getMapKeys_single, hb, rl, Term.list] at run; exact run.symm
    | cons L rest =>
      have unf : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list (L :: rest))
            (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      rw [unf] at run
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      obtain ⟨T, Y, extra, mis, f, e, hx, hm, hmk, hf⟩ := dnf_flag_sem ef hn fld hmd hkL fb _ hl inB ok nr res run
      exact Or.inr ⟨T, Y, extra, mis, f, e, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, hx, hm, hmk, hf⟩



end

section
variable {t : Term} {n : Nat}

/-- `map_update/5` for a constant at a static key type, asking for the old values, on static types of the next
level: `:badmap`, or the errors and found flag `flag_static` gives, an error exactly when nothing is found. -/
theorem flag_update {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key v : Term} {rk Ds : List String}
    {neg : Term} {m : Nat} (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (fld : Term) {md : String} (hmd : Mode md) (hm : (level t n).K + 26 ≤ m)
    (hupd : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (.atom md) (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
        (.atom "true"))
    (hkL : ∀ k, k + 6 = m → ∀ lines : List Term, (∀ L ∈ lines, MLine (level t n).E L ∧ ∃ w, InMLine (level t n).den L w) →
      ∀ (bd : Bool) a, ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (k + 5))
        (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue (level t n).E F ∧
        ∀ o, FieldSem (level t n).den F o ↔ ∃ L ∈ lines, LongM (level t n).den L a o)
    {r : Term} (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (.atom md) (.atom "true") = .ok r) :
    r = .atom "badmap" ∨ ∃ (er : Term) (extra mis : List Term) (f : Bool), MOnly t n X ∧
      er = Term.list (extra ++ mis.map bdErr) ∧
      ((f = Bool.false ∧ r = .tuple #[.atom "error", er]) ∨ (f = Bool.true ∧ ∃ T Y, r = .tuple #[T, Y, er])) ∧
      (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧ (∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s) ∧
      (∀ s ∈ Ds, s ≠ "atom" → (.atom s ∈ mis ↔ ¬∃ w, MT t n X w ∧ HasKind w s)) ∧
      (md ≠ "force" → rk = [] → (f = Bool.true ↔ ∃ x w, MT t n X w ∧
        ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧ w κ = some x)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  rw [hupd] at run
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def] at run
  simp only [Erlang.maps.«take/2», sX.static] at run
  cases hb : mapLookup X (.atom "map") with
  | none =>
    left
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure,
      Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»] at run
    exact run.symm
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
    obtain ⟨dR, sR⟩ := rest_map hX
    have rE := next_empty dR (m := k + 6) (by omega)
    have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 6)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
      exact rE
    have only : MOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmM X)) v) ∧
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), w, (mt w).mp hw⟩
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), w, (mt w).mpr hw⟩
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      cases hs : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true")
          (.atom "true") with
      | error e => simp [key, mo, hs, Lynx.Except.andAlso] at run
      | ok res =>
        rcases flag_static (level t n).ef (n := k) (by omega) fld hmd (hkL k rfl) ok nr hb fb res hs with
          rfl | ⟨T, Y, extra, mis, f, rfl, ⟨w₀, hw₀⟩, hx, hm', hmk, hf⟩
        · left
          simp [key, mo, hs, Lynx.Except.andAlso,
            Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure,
            Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»] at run
          exact run.symm
        · right
          refine ⟨_, extra, mis, f, only.mpr ⟨restE, w₀, hw₀⟩, rfl, ?_, hx, hm', fun s ms sa => by rw [hmk s ms sa]; simp only [mt],
            fun nf rk0 => by rw [hf nf rk0]; simp only [mt]⟩
          cases f
          · left; refine ⟨rfl, ?_⟩
            simp [key, mo, hs, Lynx.Except.andAlso, boolAtom, Lynx.Term.isMember] at run; exact run.symm
          · right; refine ⟨rfl, T, Y, ?_⟩
            simp [key, mo, hs, Lynx.Except.andAlso, boolAtom, Lynx.Term.isMember] at run; exact run.symm
    · rw [bp_false.mpr restE] at mo
      left
      simp [key, mo, Lynx.Except.andAlso, boolAtom,
        Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure,
        Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»] at run
      exact run.symm

end


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_named_key/5` for `:keep` and `:reject` of a value with values gives the maps and the old field. -/
theorem hk_val (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (bd : Bool) (a : String) :
    ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
        (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  cases bd
  · obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
    exact ⟨[], F, by simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember,
      Term.list, rF], hF, sF⟩
  · obtain ⟨ba, F, rb, -, hF, sF, -⟩ := keep_lines ef hn a hv vne keep lines hl (.atom "true")
    exact ⟨ba, F, rb, hF, sF⟩

/-- `map_update_named_key/5` deleting a key gives the maps and the old field. -/
theorem hk_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (bd : Bool) (a : String) :
    ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom md])
        (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  obtain ⟨ba, F, rb, -, -, -⟩ := del_key_sem ef hn lines hl hmd a bd
  obtain ⟨bdds, F', e, hF, sF⟩ := del_key ef hn lines hl md hmd bd a _ rb
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
  obtain ⟨-, rfl⟩ := e
  exact ⟨ba, F, rb, hF, sF⟩

end

section
variable {t : Term} {n : Nat}

/-- A static key type without named atoms splits into no required atoms. -/
theorem unnamed_rs {key : Term} {rs : List Term} {neg : Term} {ds : List Term} (ok : SplitOk rs neg ds)
    (nr : ∀ N, neg = .map N → rs = []) (sk : ∀ κ, SplitKey rs neg ds κ ↔ KeyPt t n key κ) (A : List String)
    (h : (∀ s, ¬KeyPt t n key (.atom s)) ∨ (∀ s, KeyPt t n key (.atom s)) ∨
      ∀ s, ¬KeyPt t n key (.atom s) → s ∈ A) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rest =>
    exfalso
    obtain ⟨a, rfl⟩ := ok.hrs r List.mem_cons_self
    have hneg : neg = .atom "nil" := by
      rcases ok.hneg with e | ⟨N, e⟩
      · exact e
      · cases nr N e
    subst hneg
    have strs : ∀ s, KeyPt t n key (.atom s) ↔ .atom s ∈ Term.atom a :: rest := fun s => by
      rw [← sk]; simp [SplitKey]
    obtain ⟨c, hc⟩ := fresh_str (A ++ ((Term.atom a :: rest).filterMap fun r => match r with
      | .atom s => some s
      | _ => none))
    have nc : ¬KeyPt t n key (.atom c) := fun hk => hc (List.mem_append_right _ (List.mem_filterMap.mpr
      ⟨_, (strs c).mp hk, rfl⟩))
    rcases h with h | h | h
    · exact h a ((strs a).mpr List.mem_cons_self)
    · exact nc (h c)
    · exact hc (List.mem_append_left _ (h c nc))

end

section
variable {t : Term} {n : Nat}

/-- `atom/1` on a non-empty list of atoms: the type of those atoms. -/
theorem atomsY (A : List String) (hA : A ≠ []) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ Y, Elixir.Module.Types.Descr.«atom/1» (Term.list (A.map Term.atom)) = .ok (.map Y) ∧ DE (level t n).E (.map Y) ∧
      ∀ s, denD (.map Y) (aPt (t := t) (n := n) (.atom s)) ↔ s ∈ A := by
  have ha : ∀ a ∈ A.map Term.atom, ∃ s, a = .atom s := fun a ma => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp ma; exact ⟨s, rfl⟩
  obtain ⟨Y, rY, hY⟩ := key_type_run (t := t) (n := n) (A.map Term.atom) [] ha (by simp) (m := m) hm
  refine ⟨Y, ?_, hY.de, fun s => ?_⟩
  · cases A with
    | nil => exact absurd rfl hA
    | cons a A =>
      have := rY
      simp only [Elixir.STTDescrProofsTest.«key_type/2», Term.list, List.map] at this
      simp only [Term.list, List.map]
      cases hr : Elixir.Module.Types.Descr.«atom/1» (Term.cons (.atom a) (Term.list (A.map Term.atom))) with
      | error e => simp [hr] at this
      | ok r => simp [hr, Elixir.STTDescrProofsTest.«kinds_type/2»] at this; rw [this]
  · rw [hY.atoms]; simp

/-- `unnamed_keys?/2` on a static key type: the atoms are a list, and the key type holds no atom, every atom, or every
atom but those of the list. -/
theorem unnamed_ok {key atoms : Term} (dk : DE (level t n).E key) {m : Nat} (hm : (level t n).K + 23 ≤ m)
    (h : Elixir.STTDescrProofsTest.«unnamed_keys?/2» (D m) key atoms = .ok (.atom "true")) :
    ∃ A : List String, atoms = Term.list (A.map Term.atom) ∧ ((∀ s, ¬KeyPt t n key (.atom s)) ∨
      (∀ s, KeyPt t n key (.atom s)) ∨ ∀ s, ¬KeyPt t n key (.atom s) → s ∈ A) := by
  simp only [Elixir.STTDescrProofsTest.«unnamed_keys?/2», Lynx.Except.andAlso_eq_true] at h
  obtain ⟨hk, h⟩ := h
  obtain ⟨as, ks, rfl, -, ha, -⟩ := keys_ok hk
  obtain ⟨A, rfl⟩ := atoms_of ha
  refine ⟨A, rfl, ?_⟩
  have kA := kind_atom (t := t) (n := n)
  simp only [Elixir.Module.Types.Descr.«atom/0», pure, Except.pure, Lynx.Except.ok_bind] at h
  rw [next_disj dk kA.de hm] at h
  by_cases dj : ∀ v : PN t n, denD key v → denD (.map [(.atom "atom", .tuple #[.atom "negation", .map []])]) v → False
  · exact Or.inl fun s hs => dj _ hs (kA.atoms rfl _)
  rw [bp_false.mpr dj] at h
  rw [next_sub kA.de dk hm] at h
  by_cases sb : SubN t n (.map [(.atom "atom", .tuple #[.atom "negation", .map []])]) key
  · exact Or.inr (Or.inl fun s => sb _ (kA.atoms rfl _))
  rw [bp_false.mpr sb] at h
  simp only [boolAtom, Bool.false_eq_true, ↓reduceIte, Lynx.Except.orElse_false] at h
  cases A with
  | nil => simp [Erlang.erlang.«/=/2», Term.list] at h
  | cons a A' =>
    obtain ⟨c, dc, rc, sc⟩ := (ef_next t n).opt_diff [] kA.de dk (m := m) hm
    obtain ⟨Y, rY, dY, sY⟩ := atomsY (t := t) (n := n) (a :: A') (by simp) hm
    have ne : Erlang.erlang.«/=/2» (Term.list ((a :: A').map Term.atom)) .nil = .ok (.atom "true") := by
      simp [Erlang.erlang.«/=/2», Term.list]
    rw [ne, Lynx.Except.andAlso_true] at h
    simp only [Elixir.Module.Types.Descr.«opt_difference/2», rc, rY, Lynx.Except.ok_bind] at h
    rw [next_sub dc dY hm] at h
    by_cases sub : SubN t n c (.map Y)
    · exact Or.inr (Or.inr fun s hs => (sY s).mp (sub _ ((sc _).mpr ⟨kA.atoms rfl _, hs⟩)))
    · rw [bp_false.mpr sub] at h; simp [boolAtom] at h

end


section
variable {t : Term} {n : Nat}

/-- The literal of the list domain holds the points of its two fields. -/
theorem listLit_den (v : PN t n) :
    denD (.map [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) v ↔
      denD (.map [(.atom "bitmap", .integer 4)]) v ∨
        denD (.map [(.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) v := by
  rw [denD_field, denD_field, denD_field]
  simp only [lookup_cons_atom]
  by_cases hb : "bitmap" = v.1.1 <;> by_cases hl : "list" = v.1.1 <;> simp [hb, hl, mapLookup] <;>
    exact absurd (hb.trans hl.symm) (by decide)

/-- The domain type of a kind other than atoms, as `kind_type/1` and `domain_key_to_descr/1` give it: the points of
that kind. -/
theorem kind_exact {k : String} (hk : k ∈ domainKinds) (ka : k ≠ "atom") {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ T, Elixir.STTDescrProofsTest.«kind_type/1» (D m) (.atom k) = .ok (.map T) ∧ DE (level t n).E (.map T) ∧
      (∀ v : PN t n, denD (.map T) v ↔ ptKind v = k) ∧ DE (level t n).E (domDescr k) ∧
      ∀ v : PN t n, denD (domDescr k) v ↔ ptKind v = k := by
  obtain ⟨T, rT, kT⟩ := kind_run (t := t) (n := n) hk hm
  have dD := (dkdT_run (t := t) (n := n) hk).2
  have eD : domDescr k = dkdT k := by
    have r := (dkdT_run (t := t) (n := n) hk).1
    unfold domDescr; rw [r]
  have pT : ∀ v : PN t n, denD (.map T) v → ptKind v = k := fun v hv => by
    rcases kT.pts v hv with ⟨e, -⟩ | ⟨-, h⟩
    · exact absurd e ka
    · exact h
  by_cases kl : k = "list"
  · subst kl
    have eL : dkdT "list" = .map [(.atom "bitmap", .integer 4),
        (.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])] := rfl
    have b2 := kind_bit (t := t) (n := n) 2 (by omega)
    simp only [show ((2 ^ 2 : Nat) : Int) = 4 from rfl] at b2
    have dl : DE (level t n).E (.map [(.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) :=
      single_de (by simp [names]) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Bdd.leaf_iff.mpr
        ⟨46675407, _, _, rfl, (level t n).ef.term, (level t n).ef.term⟩⟩))))
    obtain ⟨U, rU, dU, sU⟩ := union_map b2.de dl hm
    have eU : T = U := by
      have r2 : Elixir.STTDescrProofsTest.«kind_type/1» (D m) (.atom "list") = .ok (.map U) := by
        simp [Elixir.STTDescrProofsTest.«kind_type/1», Elixir.Module.Types.Descr.«empty_list/0»,
          Elixir.Module.Types.Descr.«term/0», non_empty_list_top, rU]
      have := rT.symm.trans r2
      simp only [Except.ok.injEq, Term.map.injEq] at this
      exact this
    subst eU
    have same : ∀ v : PN t n, denD (.map T) v ↔ denD (dkdT "list") v := fun v => by
      rw [sU, eL, listLit_den]
    have full : ∀ v : PN t n, ptKind v = "list" → denD (dkdT "list") v := fun v h => dD.kinds (by simp) v h
    refine ⟨T, rT, dU, fun v => ⟨pT v, fun h => (same v).mpr (full v h)⟩, by rw [eD]; exact dD.de, fun v => ?_⟩
    rw [eD]
    exact ⟨fun h => pT v ((same v).mpr h), full v⟩
  · have eT : dkdT k = .map T := by
      have r2 := (dkdT_run (t := t) (n := n) hk).1
      simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl ka
        | exact absurd rfl kl
        | (simp only [Elixir.STTDescrProofsTest.«kind_type/1»] at rT
           simp only [Elixir.Module.Types.Descr.«domain_key_to_descr/1»] at r2
           rw [rT] at r2
           exact (Except.ok.inj r2).symm)
    have full : ∀ v : PN t n, ptKind v = k → denD (.map T) v := fun v h => by rw [← eT]; exact dD.kinds ka v h
    refine ⟨T, rT, kT.de, fun v => ⟨pT v, full v⟩, by rw [eD, eT]; exact kT.de, fun v => ?_⟩
    rw [eD, eT]
    exact ⟨pT v, full v⟩

end


section
variable {t : Term} {n : Nat}

/-- The error type of a missing domain: the points of its kind, with one. -/
theorem domDescr_kind {s : String} (hs : s ∈ domainKinds) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    DE (level t n).E (domDescr s) ∧ (∃ v : PN t n, denD (domDescr s) v ∧ ptKind v = s) ∧
      ∀ v : PN t n, denD (domDescr s) v → ptKind v = s := by
  by_cases sa : s = "atom"
  · subst sa
    have e : domDescr "atom" = .map [(.atom "atom", .tuple #[.atom "negation", .map []])] := by
      simp [domDescr, Elixir.Module.Types.Descr.«domain_key_to_descr/1», Elixir.Module.Types.Descr.«atom/0»]
    have kA := kind_atom (t := t) (n := n)
    rw [e]
    refine ⟨kA.de, ⟨aPt (.atom "a"), kA.atoms rfl _, by simp [ptKind, aPt]⟩, fun v hv => ?_⟩
    rcases kA.pts v hv with ⟨-, h⟩ | ⟨h, -⟩
    · simp [ptKind, h]
    · exact absurd (((denD_single _ _ v).mp hv).1) h
  · obtain ⟨T, rT, dT, sT, dD, sD⟩ := kind_exact (t := t) (n := n) hs sa hm
    obtain ⟨T', rT', kT⟩ := kind_run (t := t) (n := n) hs hm
    obtain rfl : T' = T := by
      have := rT'.symm.trans rT
      simp only [Except.ok.injEq, Term.map.injEq] at this
      exact this
    obtain ⟨v, hv, pv⟩ := kT.wit sa
    exact ⟨dD, ⟨v, (sD v).mpr pv, pv⟩, fun v hv => (sD v).mp hv⟩

/-- `has_baddomain?/2` skips `badkey` errors. -/
theorem has_bd_keys (m : Nat) (T : Term) : ∀ (extra rest : List Term),
    (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) →
    Elixir.STTDescrProofsTest.«has_baddomain?/2» (D m) (Term.list (extra ++ rest)) T =
      Elixir.STTDescrProofsTest.«has_baddomain?/2» (D m) (Term.list rest) T
  | [], rest, _ => rfl
  | e :: extra, rest, h => by
    obtain ⟨a, rfl⟩ := h e List.mem_cons_self
    rw [← has_bd_keys m T extra rest fun e me => h e (List.mem_cons_of_mem _ me)]
    simp [Term.list, Elixir.STTDescrProofsTest.«has_baddomain?/2»]

/-- `has_baddomain?/2` over the errors of missing domains finds the domain of a kind exactly when it is missing. -/
theorem has_bd_mis {k : String} (hk : k ∈ domainKinds) (ka : k ≠ "atom") {m : Nat} (hm : (level t n).K + 23 ≤ m)
    {T : List (Term × Term)} (dT : DE (level t n).E (.map T)) (sT : ∀ v : PN t n, denD (.map T) v ↔ ptKind v = k) :
    ∀ mis : List Term, (∀ d ∈ mis, ∃ s ∈ domainKinds, d = .atom s) →
      ∃ b : Bool, Elixir.STTDescrProofsTest.«has_baddomain?/2» (D m) (Term.list (mis.map bdErr)) (.map T) =
        .ok (boolAtom b) ∧ (b = Bool.true ↔ .atom k ∈ mis)
  | [], _ => ⟨Bool.false, by simp [Term.list, Elixir.STTDescrProofsTest.«has_baddomain?/2», boolAtom], by simp⟩
  | d :: mis, h => by
    obtain ⟨b, rb, sb⟩ := has_bd_mis hk ka hm dT sT mis fun d md => h d (List.mem_cons_of_mem _ md)
    obtain ⟨s, hs, rfl⟩ := h d List.mem_cons_self
    obtain ⟨dD, ⟨w, hw, pw⟩, sD⟩ := domDescr_kind (t := t) (n := n) hs hm
    by_cases e : s = k
    · subst e
      have s₁ : SubN t n (domDescr s) (.map T) := fun v hv => (sT v).mpr (sD v hv)
      obtain ⟨-, -, -, -, -, sD'⟩ := kind_exact (t := t) (n := n) hk ka hm
      have s₂ : SubN t n (.map T) (domDescr s) := fun v hv => (sD' v).mpr ((sT v).mp hv)
      refine ⟨Bool.true, ?_, by simp⟩
      simp [Term.list, bdErr, Elixir.STTDescrProofsTest.«has_baddomain?/2», next_sub dD dT hm, bp_true.mpr s₁,
        next_sub dT dD hm, bp_true.mpr s₂, boolAtom]
    · have s₁ : ¬SubN t n (domDescr s) (.map T) := fun h' => e (pw.symm.trans ((sT w).mp (h' w hw)))
      refine ⟨b, ?_, ?_⟩
      · simp [Term.list, bdErr, Elixir.STTDescrProofsTest.«has_baddomain?/2», next_sub dD dT hm, bp_false.mpr s₁,
          boolAtom] at rb ⊢
        exact rb
      · rw [sb]; simp [Ne.symm e]

end


section
variable {t : Term} {n : Nat}

/-- A static type of points of a kind other than atoms splits into that kind. -/
theorem kind_keys {k : String} (ka : k ≠ "atom") {T : List (Term × Term)} (dT : DE (level t n).E (.map T))
    (sT : ∀ v : PN t n, denD (.map T) v ↔ ptKind v = k) (wT : ∃ v : PN t n, ptKind v = k) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.map T) = .ok (splitT rs neg ds) ∧
      SplitOk rs neg ds ∧ ∀ κ, SplitKey rs neg ds κ ↔ ∃ k' i, κ = .dom k' i ∧ domKind k' = k := by
  have noAtom : ∀ q, ¬denD (.map T) (aPt (t := t) (n := n) q) := fun q h => by
    have := (sT _).mp h
    simp [ptKind, aPt] at this
    exact ka this.symm
  obtain ⟨rs, neg, ds, rk, ok, -, -, sk⟩ := key_split_any (t := t) (n := n) dT
    (fun Y e S hS q hq => by
      cases e
      exact absurd ((denD_aPt q).mpr (by rw [hS]; simpa [amemV] using hq)) (noAtom q))
    (fun Y e S hS => by
      cases e
      exfalso
      obtain ⟨c, hc⟩ := fresh_str (keyStrs S)
      exact noAtom (.atom c) ((denD_aPt _).mpr (by rw [hS]; simp [amemV, lookup_fresh' hc])))
    hm
  refine ⟨rs, neg, ds, rk, ok, fun κ => ?_⟩
  rw [sk]
  cases κ with
  | atom s => simp only [KeyPt, reduceCtorEq, false_and, exists_false, iff_false]; exact noAtom _
  | dom k' i =>
    simp only [KeyPt, MKey.dom.injEq]
    constructor
    · rintro ⟨v, hv, pv⟩; exact ⟨k', i, ⟨rfl, rfl⟩, pv ▸ ((sT v).mp hv)⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, e⟩
      obtain ⟨v, pv⟩ := wT
      exact ⟨v, (sT v).mpr pv, pv.trans e.symm⟩

/-- `map_get/2` at the type of a kind other than atoms finds nothing exactly when no map holds a key of that kind. -/
theorem get_kind {X : List (Term × Term)} (hX : DE (level t (n + 1)).E (.map X)) (only : MOnly t (n + 1) X)
    {k : String} (ka : k ≠ "atom") {T : List (Term × Term)} (dT : DE (level t n).E (.map T))
    (sT : ∀ v : PN t n, denD (.map T) v ↔ ptKind v = k) (wT : ∃ v : PN t n, ptKind v = k) {m : Nat}
    (hm : (level t (n + 1)).K + 26 ≤ m) :
    ∃ (r g : Term) (b : Bool), Elixir.Module.Types.Descr.«map_get/2» (D m) (.map X) (.map T) = .ok r ∧
      Elixir.STTDescrProofsTest.«got/1» r = .ok g ∧ Elixir.Module.Types.Descr.«empty?/1» (D m) g = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ¬∃ w, MT t (n + 1) X w ∧ HasKind w k) := by
  have hK : (level t (n + 1)).K = (level t n).K + 24 := by rw [level_K, level_K]; omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨rs, neg, ds, rk, ok, sk⟩ := kind_keys ka dT sT wT (m := m') (by omega)
  have ef := (level t (n + 1)).ef
  obtain ⟨res, run, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨T₀, rfl, hT₀, -, ⟨x₀, hx₀⟩, sT₀⟩⟩ :=
    get_map (t := t) (n := n + 1) hX ok (m := m' + 1) (by omega) rk
  · exact absurd only nX
  · obtain ⟨b, rb, sb⟩ := ef.empty1 (m := m' + 1) (by omega) ef.none
    have b1 : b = Bool.true := sb.mpr fun x hx => ef.den_none x hx
    subst b1
    refine ⟨_, _, Bool.true, run, by simp [Elixir.STTDescrProofsTest.«got/1», Elixir.Module.Types.Descr.«none/0»],
      rb, ?_⟩
    constructor
    · rintro - ⟨w, hw, k', i, ek, hi⟩
      exact hi (eX w hw _ ((sk _).mpr ⟨k', i, rfl, ek⟩))
    · intro _; rfl
  · obtain ⟨b, rb, sb⟩ := ef.empty1 (m := m' + 1) (by omega) hT₀
    have b0 : b = Bool.false := by
      cases b
      · rfl
      · exact absurd hx₀ (sb.mp rfl x₀)
    subst b0
    refine ⟨_, _, Bool.false, run, by simp [Elixir.STTDescrProofsTest.«got/1», pure, Except.pure], rb, ?_⟩
    obtain ⟨w, hw, κ, hκ, e⟩ := (sT₀ x₀).mp hx₀
    obtain ⟨k', i, rfl, ek⟩ := (sk _).mp hκ
    exact ⟨fun h => (by cases h), fun h => absurd ⟨w, hw, k', i, ek, by rw [e]; simp⟩ h⟩

/-- `baddomains?/4` holds on the errors of an update, as `flag_update` gives them, over kinds other than atoms. -/
theorem bd_ok {X : List (Term × Term)} (hX : DE (level t (n + 1)).E (.map X)) (only : MOnly t (n + 1) X)
    {key : Term} (dk : DE (level t n).E key) {rs : List Term} {neg : Term} {Ds : List String}
    (skey : ∀ κ, SplitKey rs neg (Ds.map Term.atom) κ ↔ KeyPt t n key κ) (hDs : ∀ s ∈ Ds, s ∈ domainKinds)
    {extra mis : List Term} (hx : ∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a])
    (hmisD : ∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s)
    (hmk : ∀ s ∈ Ds, s ≠ "atom" → (.atom s ∈ mis ↔ ¬∃ w, MT t (n + 1) X w ∧ HasKind w s))
    {m : Nat} (hm : (level t (n + 1)).K + 26 ≤ m) :
    ∀ L : List String, (∀ k ∈ L, k ∈ domainKinds ∧ k ≠ "atom") →
      Elixir.STTDescrProofsTest.«baddomains?/4» (D m) (.map X) key (Term.list (extra ++ mis.map bdErr))
        (Term.list (L.map Term.atom)) = .ok (.atom "true")
  | [], _ => by simp [Term.list, Elixir.STTDescrProofsTest.«baddomains?/4»]
  | k :: L, hL => by
    have hK : (level t (n + 1)).K = (level t n).K + 24 := by rw [level_K, level_K]; omega
    obtain ⟨hk, ka⟩ := hL k List.mem_cons_self
    have ih := bd_ok hX only dk skey hDs hx hmisD hmk hm L fun k' mk => hL k' (List.mem_cons_of_mem _ mk)
    obtain ⟨T, rT, dT, sT, -, -⟩ := kind_exact (t := t) (n := n) hk ka (m := m) (by omega)
    obtain ⟨-, ⟨w₀, -, pw₀⟩, -⟩ := domDescr_kind (t := t) (n := n) hk (m := m) (by omega)
    obtain ⟨r, g, b₂, rg, gg, eg, sb₂⟩ := get_kind hX only ka dT sT ⟨w₀, pw₀⟩ hm
    obtain ⟨b₁, rb₁, sb₁⟩ := has_bd_mis (t := t) (n := n) hk ka (m := m) (by omega) dT sT mis fun d md => by
      obtain ⟨s, ms, rfl⟩ := hmisD d md; exact ⟨s, hDs s ms, rfl⟩
    rw [← has_bd_keys m (.map T) extra (mis.map bdErr) hx] at rb₁
    simp only [Term.list, List.map] at ih ⊢
    rw [Elixir.STTDescrProofsTest.«baddomains?/4».eq_def]
    simp only [rT, Lynx.Except.ok_bind, next_disj (m := m) dT dk (by omega)]
    by_cases dj : ∀ v : PN t n, denD (.map T) v → denD key v → False
    · rw [bp_true.mpr dj]; simp [boolAtom, ih]
    · -- The kind is a domain of the key type.
      obtain ⟨v, hvT, hvk⟩ : ∃ v : PN t n, denD (.map T) v ∧ denD key v := Classical.byContradiction fun h =>
        dj fun v a b => h ⟨v, a, b⟩
      obtain ⟨k', ek⟩ := domKind_of hk ka
      have kD : k ∈ Ds := by
        have := (skey (.dom k' 0)).mpr ⟨v, hvk, by rw [(sT v).mp hvT, ek]⟩
        simp only [SplitKey, ek, List.mem_map, Term.atom.injEq, exists_eq_right] at this
        exact this
      have eb : b₁ = b₂ := by
        cases b₁ <;> cases b₂ <;> first | rfl | (exfalso; simp_all)
      subst eb
      rw [bp_false.mpr dj]
      simp [boolAtom, rb₁, rg, gg, eg, Erlang.erlang.«==/2», ih]

end


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_named_key/5` forcing a value gives the maps and the old field. -/
theorem hk_force (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (bd : Bool) (a : String) :
    ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"])
        (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
  cases bd
  · exact ⟨[], F, by simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember,
      Term.list, rF], hF, sF⟩
  · obtain ⟨ba, rba, -, -⟩ := put_lines ef hn a (leafPut_put ef a hv) lines hl
    exact ⟨ba, F, by simpa [boolAtom] using rba Bool.true F fun _ => rF, hF, sF⟩

end

end Elixir.STTDescrProofsTest.Nest
