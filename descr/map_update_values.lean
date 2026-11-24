namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! The old values and errors of `map_update_static_dnf/6` when the return type is asked. -/

/-- `map_update_get_domains/5` asking for the type: the values the lines' tags give the domains, whether some domain
was found, and the missing domains among them. -/
theorem upd_domains (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (cb : Term) (hcb : ∃ c : Bool, (D (n + 3)).pure cb #[] = .ok (boolAtom c))
    (Ds : List String) {acc : Term} (ha : E acc) :
    ∃ (f : Bool) (val mis : List Term) (T : Term),
      Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 4)) (Term.list lines) (Term.list (Ds.map Term.atom))
        acc (.atom "true") cb = .ok (.tuple #[boolAtom f, Term.list val, Term.list mis, T]) ∧ E T ∧
      (∀ x, den T x ↔ den acc x ∨ ∃ s ∈ Ds, ∃ L ∈ lines, LineTag den L s x) ∧ (Ds = [] → f = Bool.false) ∧
      ∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s := by
  obtain ⟨c, hc⟩ := hcb
  obtain ⟨r, ⟨f, val, mis, T, rfl, hT, sT, fD, mD⟩, run⟩ := foldl_rel_at (m := n + 4) "Elixir.Module.Types.Descr"
    "-map_update_get_domains/5-fun-0-" #[Term.list lines, .atom "true", cb]
    (fun pre a => ∃ (f : Bool) (val mis : List Term) (T : Term), a = .tuple #[boolAtom f, Term.list val, Term.list mis, T] ∧
      E T ∧ (∀ x, den T x ↔ den acc x ∨ ∃ s, .atom s ∈ pre ∧ ∃ L ∈ lines, LineTag den L s x) ∧
      (pre = [] → f = Bool.false) ∧ ∀ d ∈ mis, d ∈ pre)
    (Ds.map Term.atom) (fun pre x a mx ⟨f, val, mis, T, ea, hT, sT, fD, mD⟩ => by
      subst ea
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp mx
      obtain ⟨g, rg, hg, sg⟩ := get_domain1 ef (n := n + 3) (by omega) lines hl s
      obtain ⟨b, rb, sb⟩ := ef.empty1 (m := n + 3) (by omega) hg
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] hT hg (m := n + 3) (by omega)
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure]
      simp only [Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5», rg, rb, Lynx.Except.ok_bind,
        Elixir.Module.Types.Descr.«opt_union/2», ru, Erlang.erlang.«==/2»]
      have semU : ∀ x, den u x ↔ den acc x ∨ ∃ s', .atom s' ∈ pre ++ [.atom s] ∧ ∃ L ∈ lines, LineTag den L s' x :=
        fun x => by
          rw [su, sT, sg]
          simp only [List.mem_append, List.mem_singleton, Term.atom.injEq]
          constructor
          · rintro ((h | ⟨s', m', h⟩) | h)
            · exact Or.inl h
            · exact Or.inr ⟨s', Or.inl m', h⟩
            · exact Or.inr ⟨s, Or.inr rfl, h⟩
          · rintro (h | ⟨s', m' | rfl, h⟩)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr ⟨s', m', h⟩)
            · exact Or.inr h
      have semT : b = Bool.true → ∀ x, den T x ↔ den acc x ∨ ∃ s', .atom s' ∈ pre ++ [.atom s] ∧ ∃ L ∈ lines, LineTag den L s' x :=
        fun eb x => by
          rw [sT]
          simp only [List.mem_append, List.mem_singleton, Term.atom.injEq]
          constructor
          · rintro (h | ⟨s', m', h⟩)
            · exact Or.inl h
            · exact Or.inr ⟨s', Or.inl m', h⟩
          · rintro (h | ⟨s', m' | rfl, h⟩)
            · exact Or.inl h
            · exact Or.inr ⟨s', m', h⟩
            · exact absurd ((sg x).mpr h) (sb.mp eb x)
      by_cases sa : s = "atom"
      · subst sa
        cases b
        · refine ⟨_, ⟨Bool.true, .atom "atom" :: val, mis, u, rfl, hu, semU, by simp, fun d md => by simp [mD d md]⟩, ?_⟩
          simp [boolAtom, Lynx.Term.isMember, Term.list]
        · have mis' : ∀ d ∈ Term.atom "atom" :: mis, d ∈ pre ++ [.atom "atom"] := fun d md => by
            rcases List.mem_cons.mp md with rfl | md
            · simp
            · simp [mD d md]
          cases c
          · refine ⟨_, ⟨f, val, .atom "atom" :: mis, T, rfl, hT, semT rfl, by simp, mis'⟩, ?_⟩
            simp [boolAtom, Lynx.Term.isMember, Term.list, hc, Erlang.erlang.«/=/2», Lynx.Except.guard]
          · refine ⟨_, ⟨Bool.true, val, .atom "atom" :: mis, T, rfl, hT, semT rfl, by simp, mis'⟩, ?_⟩
            simp [boolAtom, Lynx.Term.isMember, Term.list, hc, Erlang.erlang.«/=/2», Lynx.Except.guard]
      · have ne : Term.compare (Term.fuel (.atom s) (.atom "atom")) (.atom s) (.atom "atom") ≠ .eq := by
          rw [atoms_cmp]; exact fun e => sa (Std.compare_eq_iff_eq.mp e)
        cases b
        · refine ⟨_, ⟨Bool.true, .atom s :: val, mis, u, rfl, hu, semU, by simp, fun d md => by simp [mD d md]⟩, ?_⟩
          simp [boolAtom, Lynx.Term.isMember, Term.list, ne]
        · refine ⟨_, ⟨f, val, .atom s :: mis, T, rfl, hT, semT rfl, by simp, fun d md => ?_⟩, ?_⟩
          · rcases List.mem_cons.mp md with rfl | md
            · simp
            · simp [mD d md]
          · simp [boolAtom, Lynx.Term.isMember, Term.list, ne])
    (.tuple #[.atom "false", .nil, .nil, acc]) ⟨Bool.false, [], [], acc, rfl, ha, fun x => by simp, fun _ => rfl, by simp⟩
  refine ⟨f, val, mis, T, ?_, hT, fun x => by rw [sT]; simp, fun e => fD (by simp [e]), fun d md => ?_⟩
  · simpa [Elixir.Module.Types.Descr.«map_update_get_domains/5», boolAtom, Term.list] using run
  · obtain ⟨s, ms, rfl⟩ := List.mem_map.mp (mD d md); exact ⟨s, ms, rfl⟩

theorem any_ok (d : Dispatcher) (m nm : String) (caps : Array Term) (l : List Term)
    (hf : ∀ x ∈ l, ∃ b : Bool, d.pure (.function m nm 1 caps) #[x] = .ok (boolAtom b)) :
    ∃ c : Bool, Erlang.lists.«any/2» d (.function m nm 1 caps) (Term.list l) = .ok (boolAtom c) := by
  classical
  let res : Term → Bool := fun x => if h : ∃ b : Bool, d.pure (.function m nm 1 caps) #[x] = .ok (boolAtom b) then
    Classical.choose h else Bool.false
  refine ⟨l.any res, any_list d m nm caps res l fun x mx => ?_⟩
  have h := hf x mx
  simp only [res, h, dite_true]
  exact Classical.choose_spec h

theorem map_ok (d : Dispatcher) (mo nm : String) (caps : Array Term) (l : List Term)
    (hf : ∀ x ∈ l, ∃ y, d.pure (.function mo nm 1 caps) #[x] = .ok y) :
    ∃ l' : List Term, Erlang.lists.«map/2» d (.function mo nm 1 caps) (Term.list l) = .ok (Term.list l') := by
  classical
  let g : Term → Term := fun x => if h : ∃ y, d.pure (.function mo nm 1 caps) #[x] = .ok y then Classical.choose h
    else .nil
  refine ⟨l.map g, map_list d mo nm caps g l fun x mx => ?_⟩
  have h := hf x mx
  simp only [g, h, dite_true]
  exact Classical.choose_spec h

/-- `domain_key_to_descr/1` on the kinds of keys. -/
theorem domain_descr_ok {s : String} (h : s ∈ domainKinds) :
    ∃ y, Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom s) = .ok y := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, rfl⟩

/-- The errors of the missing domains of `map_update_static_dnf/6`. -/
theorem domain_errors_ok (m : Nat) (mis : List Term) (h : ∀ d ∈ mis, ∃ s ∈ domainKinds, d = .atom s) :
    ∃ errs : List Term, Erlang.lists.«map/2» (D (m + 1))
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis) =
        .ok (Term.list errs) :=
  map_ok _ _ _ _ mis fun x mx => by
    obtain ⟨s, ms, rfl⟩ := h x mx
    obtain ⟨y, hy⟩ := domain_descr_ok ms
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-1-/1».pure]
    exact ⟨.tuple #[.atom "baddomain", y], by simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-1-/1», hy]⟩

/-- `map_update_any_named_key?/2` on the non-empty lines of a map type. -/
theorem any_named_ok (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (ks : List String) :
    ∃ c : Bool, Elixir.Module.Types.Descr.«map_update_any_named_key?/2» (D (n + 4)) (Term.list lines)
      (Term.list (ks.map Term.atom)) = .ok (boolAtom c) := by
  simp only [Elixir.Module.Types.Descr.«map_update_any_named_key?/2»]
  exact any_ok _ _ _ _ _ fun x mx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp mx
    obtain ⟨F, rF, hF, -⟩ := mdnf_fetch ef hn a lines hl
    obtain ⟨ty, o, rfl, hty⟩ := hF
    obtain ⟨b, rb, -⟩ := ef.empty1 (m := n + 3) (by omega) hty
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_any_named_key?/2-fun-0-/1».pure]
    exact ⟨!b, by cases b <;> simp [Elixir.Module.Types.Descr.«-map_update_any_named_key?/2-fun-0-/2», rF, rb,
      Erlang.erlang.«not/1», boolAtom]⟩

/-- `map_update_named_keys/8` forcing a constant: asking for the old values gives the same maps and found flag, the
errors untouched, and the old values united with those at the keys. -/
theorem named_old (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (req : Bool) (st : Term) (bd : Bool) :
    ∀ (ks : List String) (B : List Term) (f : Bool) (T0 Er0 T Er : Term), E T →
      ∃ (B' : List Term) (f' : Bool) (T' : Term),
        Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[T0, Term.list B, Er0, boolAtom f])
          (Term.list lines) (Term.list (ks.map Term.atom)) (forceOp v) (boolAtom req) st (.atom "false") (boolAtom bd) =
          .ok (.tuple #[T0, Term.list B', Er0, boolAtom f']) ∧
        Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[T, Term.list B, Er, boolAtom f])
          (Term.list lines) (Term.list (ks.map Term.atom)) (forceOp v) (boolAtom req) st (.atom "true") (boolAtom bd) =
          .ok (.tuple #[T', Term.list B', Er, boolAtom f']) ∧ E T' ∧
        (∀ x, den T' x ↔ den T x ∨ ∃ a ∈ ks, ∃ L ∈ lines, LongM den L a (some x)) ∧ f' = (f || !ks.isEmpty) := by
  have loop : ∀ (ks : List String) (B : List Term) (f : Bool) (T0 Er0 T Er : Term), E T →
      ∃ (B' : List Term) (f' : Bool) (T' : Term),
        Erlang.lists.«foldl_1/3» (D (n + 4))
          (.function "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, forceOp v, boolAtom req, st, boolAtom bd, .atom "false", .atom "true"])
          (.tuple #[T0, Term.list B, Er0, boolAtom f]) (Term.list (ks.map Term.atom)) =
          .ok (.tuple #[T0, Term.list B', Er0, boolAtom f']) ∧
        Erlang.lists.«foldl_1/3» (D (n + 4))
          (.function "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, forceOp v, boolAtom req, st, boolAtom bd, .atom "true", .atom "true"])
          (.tuple #[T, Term.list B, Er, boolAtom f]) (Term.list (ks.map Term.atom)) =
          .ok (.tuple #[T', Term.list B', Er, boolAtom f']) ∧ E T' ∧
        (∀ x, den T' x ↔ den T x ∨ ∃ a ∈ ks, ∃ L ∈ lines, LongM den L a (some x)) ∧ f' = (f || !ks.isEmpty) := by
    intro ks
    induction ks with
    | nil =>
      intro B f T0 Er0 T Er hT
      exact ⟨B, f, T, by simp [Erlang.lists.«foldl_1/3», Term.list], by simp [Erlang.lists.«foldl_1/3», Term.list], hT,
        by simp, by simp⟩
    | cons a rest ih =>
      intro B f T0 Er0 T Er hT
      obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
      obtain ⟨ty, o, rfl, hty⟩ := hF
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] hty hT (m := n + 3) (by omega)
      obtain ⟨ba, rba⟩ : ∃ ba : List Term, ∀ (ow : Bool),
          Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a) (forceOp v)
            (boolAtom bd) (boolAtom ow) = .ok (.tuple #[Term.list ba, if ow then .tuple #[ty, boolAtom o] else .atom "nil"]) := by
        cases bd
        · refine ⟨[], fun ow => ?_⟩
          cases ow
          · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember, Term.list]
          · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember, Term.list, rF]
        · obtain ⟨ba, rba, -, -⟩ := put_lines ef hn a (leafPut_put ef a hv) lines hl
          exact ⟨ba, fun ow => rba ow _ fun _ => rF⟩
      have rb₀ : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a) (forceOp v)
          (boolAtom bd) (.atom "false") = .ok (.tuple #[Term.list ba, .atom "nil"]) := by simpa using rba Bool.false
      have rb₁ : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a) (forceOp v)
          (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, .tuple #[ty, boolAtom o]]) := by
        simpa using rba Bool.true
      obtain ⟨B', f', T', r₀, r₁, hT', sT', ef'⟩ := ih (ba ++ B) Bool.true T0 Er0 u Er hu
      refine ⟨B', f', T', ?_, ?_, hT', fun x => ?_, by simp [ef']⟩
      · rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only [Term.list, List.map] at r₀ ⊢
        simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
          Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», append_list, rb₀]
        simpa [boolAtom, Term.list] using r₀
      · rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only [Term.list, List.map] at r₁ ⊢
        cases req <;> cases f <;>
        simp [Lynx.Except.orElse, Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
          Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», append_list, rb₁, Lynx.Term.isMember,
          Elixir.Module.Types.Descr.«opt_union/2», ru, Erlang.erlang.«not/1»] <;>
        simpa [boolAtom, Term.list] using r₁
      · rw [sT', su]
        have st : ∀ x, den ty x ↔ ∃ L ∈ lines, LongM den L a (some x) := fun x => by
          rw [← sF, fieldSem_mk]
          simp
        simp only [List.mem_cons, st]
        constructor
        · rintro ((h | h) | ⟨a', m', h⟩)
          · exact Or.inr ⟨a, Or.inl rfl, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨a', Or.inr m', h⟩
        · rintro (h | ⟨a', rfl | m', h⟩)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨a', m', h⟩
  intro ks B f T0 Er0 T Er hT
  obtain ⟨B', f', T', r₀, r₁, hT', sT', ef'⟩ := loop ks B f T0 Er0 T Er hT
  refine ⟨B', f', T', ?_, ?_, hT', sT', ef'⟩
  · simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse]
    cases ks with
    | nil =>
      simp [Term.list, Erlang.lists.«foldl_1/3»] at r₀ ⊢
      exact r₀
    | cons k t => simp only [Term.list, List.map] at r₀ ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at r₀; simpa using r₀
  · simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse]
    cases ks with
    | nil =>
      simp [Term.list, Erlang.lists.«foldl_1/3»] at r₁ ⊢
      exact r₁
    | cons k t => simp only [Term.list, List.map] at r₁ ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at r₁; simpa using r₁

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `map_update_static_dnf/6` forcing a constant at a split of static keys: asking for the old values gives the same
maps and found flag, with the values at the keys, and errors only for missing domains. -/
theorem dnf_old (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (bdd : Term)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (rk : List String) (neg : Term)
    (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (st : Term) (R : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) neg bdd = .ok (Term.list (R.map Term.atom)))
    (hRk : R = [] ∨ rk = []) (Y f : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "false") st =
        .ok (.tuple #[.map [], Y, .nil, f])) :
    ∃ T er, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "true") st =
        .ok (.tuple #[T, Y, er, f]) ∧ E T ∧
      (∀ x, den T x ↔ (∃ s ∈ Ds, ∃ L ∈ lines, LineTag den L s x) ∨
        ∃ a, (a ∈ rk ∨ a ∈ R) ∧ ∃ L ∈ lines, LongM den L a (some x)) ∧ (Ds = [] → er = .nil) ∧
      (rk ≠ [] → f = .atom "true") := by
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
  let OK := R
  have mOK : ∀ a, a ∈ OK ↔ a ∈ R := fun a => Iff.rfl
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (rk ++ OK)
  have hcb : (D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (OK.map Term.atom), Term.list (rk.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simpa [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, fD₁, mD₁⟩ := upd_domains ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨f₂, val₂, mis₂, T₂, r₂, hT₂, sT₂, fD₂, mD₂⟩ := upd_domains ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ [] hT₁
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h ⊢
  simp only [splitT] at h ⊢
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», hR, m₀, m₁, m₂, m₃] at h ⊢
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₂, Term.list val₂, Term.list mis₂, T₂]) := r₂
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have f₂0 : f₂ = Bool.false := fD₂ rfl
  subst f₂0
  simp only [r₁', r₂', rE', Lynx.Except.ok_bind]
  by_cases hD : Ds = []
  · subst hD
    obtain rfl : f₁ = Bool.false := fD₁ rfl
    simp [boolAtom, Lynx.Except.orElse, Term.list] at h ⊢
    obtain ⟨X, hX, h⟩ := bind_ok h
    have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
      clear h
      simp only [bind, Except.bind, Except.tryWith] at hX
      repeat' split at hX
      all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
      all_goals done
    rw [hX]; simp only [Lynx.Except.ok_bind]
    obtain ⟨B96, hB, h⟩ := bind_ok h
    rw [hB]; simp only [Lynx.Except.ok_bind]
    obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
      clear h
      split at hB
      · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
      · cases hB; exact ⟨[], rfl⟩
      · cases hB
    obtain ⟨B', f', T', e0, e1, hT', sT', ef'⟩ := named_old ef (n := n + 2) (by omega) hv lines hl Bool.true st Bool.true rk
      Bl Bool.false (.map []) .nil T₂ (Term.list errs) hT₂
    have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
        (.tuple #[.map [], Term.list Bl, .nil, .atom "false"]) (Term.list lines) (Term.list (rk.map Term.atom))
        (forceOp v) (.atom "true") st (.atom "false") (.atom "true") =
        .ok (.tuple #[.map [], Term.list B', .nil, boolAtom f']) := by simpa using e0
    have e1' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
        (.tuple #[T₂, Term.list Bl, Term.list errs, .atom "false"]) (Term.list lines) (Term.list (rk.map Term.atom))
        (forceOp v) (.atom "true") st (.atom "true") (.atom "true") =
        .ok (.tuple #[T', Term.list B', Term.list errs, boolAtom f']) := by simpa using e1
    rw [e0'] at h; rw [e1']; simp only [Lynx.Except.ok_bind] at h ⊢
    obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
      rcases hb with hb | hb
      · exact ⟨Bool.false, hb⟩
      · exact ⟨Bool.true, hb⟩
    rw [ebd] at h ⊢
    obtain ⟨B'', f'', T'', e2, e3, hT'', sT'', ef''⟩ := named_old ef (n := n + 2) (by omega) hv lines hl Bool.false st bd R
      B' f' (.map []) .nil T' (Term.list errs) hT'
    have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
        (.tuple #[.map [], Term.list B', .nil, boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
        (forceOp v) (.atom "false") st (.atom "false") (boolAtom bd) =
        .ok (.tuple #[.map [], Term.list B'', .nil, boolAtom f'']) := by simpa using e2
    have e3' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
        (.tuple #[T', Term.list B', Term.list errs, boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
        (forceOp v) (.atom "false") st (.atom "true") (boolAtom bd) =
        .ok (.tuple #[T'', Term.list B'', Term.list errs, boolAtom f'']) := by simpa using e3
    rw [e2'] at h; rw [e3']; simp only [Lynx.Except.ok_bind] at h ⊢
    obtain ⟨u, hu, h⟩ := bind_ok h
    rw [hu]; simp only [Lynx.Except.ok_bind]
    have fY : ∀ Y', (Except.ok (Term.tuple #[.map [], Y', .nil, boolAtom f'']) : Except Exception Term) =
        Except.ok (Term.tuple #[.map [], Y, .nil, f]) →
        f = boolAtom f'' := fun Y' e => by simp at e; exact e.2.symm
    refine ⟨T'', Term.list errs, ?_, hT'', fun x => ?_, ?_, fun hk => ?_⟩
    · split at h <;> simp_all
    · rw [sT'', sT', sT₂, sT₁]
      simp only [ef.den_none x, false_or, List.not_mem_nil, false_and, exists_false, or_false]
      constructor
      · rintro (⟨a, ma, hh⟩ | ⟨a, ma, hh⟩)
        · exact ⟨a, Or.inl ma, hh⟩
        · exact ⟨a, Or.inr ma, hh⟩
      · rintro ⟨a, ma | ma, hh⟩
        · exact Or.inl ⟨a, ma, hh⟩
        · exact Or.inr ⟨a, ma, hh⟩
    · obtain rfl : mis₁ = [] := by
        cases mis₁ with
        | nil => rfl
        | cons d ds => obtain ⟨s, ms, -⟩ := mD₁ d List.mem_cons_self; simp at ms
      simp [Erlang.lists.«map/2», Erlang.erlang.«is_function/2», Term.list] at rE'
      cases errs with
      | nil => rfl
      | cons e es => simp [Term.list] at rE'
    · have : f = boolAtom f'' := by split at h <;> exact fY _ h
      rw [this, ef'', ef']
      cases rk with
      | nil => exact absurd rfl hk
      | cons a rk => simp
  · have dsCmp : Term.compare ((Term.list (Ds.map Term.atom)).fuel .nil) (Term.list (Ds.map Term.atom)) .nil ≠ .eq := by
      cases Ds with
      | nil => exact absurd rfl hD
      | cons d ds => rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep, Term.list]
    cases f₁ <;> simp [boolAtom, Lynx.Except.orElse, dsCmp] at h ⊢
    all_goals (
      obtain ⟨X, hX, h⟩ := bind_ok h
      have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
        clear h
        simp only [bind, Except.bind, Except.tryWith] at hX
        repeat' split at hX
        all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
        all_goals done
      rw [hX]; simp only [Lynx.Except.ok_bind]
      obtain ⟨B96, hB, h⟩ := bind_ok h
      rw [hB]; simp only [Lynx.Except.ok_bind]
      obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
        clear h
        split at hB
        · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
        · cases hB; exact ⟨[], rfl⟩
        · cases hB
      obtain ⟨B', f', T', e0, e1, hT', sT', ef'⟩ := named_old ef (n := n + 2) (by omega) hv lines hl Bool.true st Bool.true rk
        Bl Bool.true (.map []) .nil T₂ (Term.list errs) hT₂
      have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
          (.tuple #[.map [], Term.list Bl, .nil, .atom "true"]) (Term.list lines) (Term.list (rk.map Term.atom))
          (forceOp v) (.atom "true") st (.atom "false") (.atom "true") =
          .ok (.tuple #[.map [], Term.list B', .nil, boolAtom f']) := by simpa using e0
      have e1' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
          (.tuple #[T₂, Term.list Bl, Term.list errs, .atom "true"]) (Term.list lines) (Term.list (rk.map Term.atom))
          (forceOp v) (.atom "true") st (.atom "true") (.atom "true") =
          .ok (.tuple #[T', Term.list B', Term.list errs, boolAtom f']) := by simpa using e1
      rw [e0'] at h; rw [e1']; simp only [Lynx.Except.ok_bind] at h ⊢
      obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
        rcases hb with hb | hb
        · exact ⟨Bool.false, hb⟩
        · exact ⟨Bool.true, hb⟩
      rw [ebd] at h ⊢
      obtain ⟨B'', f'', T'', e2, e3, hT'', sT'', ef''⟩ := named_old ef (n := n + 2) (by omega) hv lines hl Bool.false st bd R
        B' f' (.map []) .nil T' (Term.list errs) hT'
      have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
          (.tuple #[.map [], Term.list B', .nil, boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
          (forceOp v) (.atom "false") st (.atom "false") (boolAtom bd) =
          .ok (.tuple #[.map [], Term.list B'', .nil, boolAtom f'']) := by simpa using e2
      have e3' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
          (.tuple #[T', Term.list B', Term.list errs, boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
          (forceOp v) (.atom "false") st (.atom "true") (boolAtom bd) =
          .ok (.tuple #[T'', Term.list B'', Term.list errs, boolAtom f'']) := by simpa using e3
      rw [e2'] at h; rw [e3']; simp only [Lynx.Except.ok_bind] at h ⊢
      obtain ⟨u, hu, h⟩ := bind_ok h
      rw [hu]; simp only [Lynx.Except.ok_bind]
      have fY : ∀ Y', (Except.ok (Term.tuple #[.map [], Y', .nil, boolAtom f'']) : Except Exception Term) =
          Except.ok (Term.tuple #[.map [], Y, .nil, f]) →
          f = boolAtom f'' := fun Y' e => by simp at e; exact e.2.symm
      refine ⟨T'', Term.list errs, ?_, hT'', fun x => ?_, ?_, fun hk => ?_⟩
      · split at h <;> simp_all
      · rw [sT'', sT', sT₂, sT₁]
        simp only [ef.den_none x, false_or, List.not_mem_nil, false_and, exists_false, or_false]
        constructor
        · rintro ((hy | ⟨a, ma, hh⟩) | ⟨a, ma, hh⟩)
          · exact Or.inl hy
          · exact Or.inr ⟨a, Or.inl ma, hh⟩
          · exact Or.inr ⟨a, Or.inr ma, hh⟩
        · rintro (hy | ⟨a, ma | ma, hh⟩)
          · exact Or.inl (Or.inl hy)
          · exact Or.inl (Or.inr ⟨a, ma, hh⟩)
          · exact Or.inr ⟨a, ma, hh⟩
      · intro hD'; exact absurd hD' hD
      · have : f = boolAtom f'' := by split at h <;> exact fY _ h
        rw [this, ef'', ef']
        cases rk with
        | nil => exact absurd rfl hk
        | cons a rk => simp)

-- end dnf_old

theorem atoms_of {l : List Term} (h : ∀ r ∈ l, ∃ s, r = .atom s) : ∃ A : List String, l = A.map Term.atom := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons r rs ih =>
    obtain ⟨s, rfl⟩ := h r List.mem_cons_self
    obtain ⟨B, rfl⟩ := ih fun x mx => h x (List.mem_cons_of_mem _ mx)
    exact ⟨s :: B, rfl⟩

/-- The old values of `map_update_static_dnf/6` on the non-empty lines of a map field are the values `map_get/2`
selects. -/
theorem dnf_old_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) {b : Term}
    (fb : MField E b) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = []) (st Y f : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "false") st =
        .ok (.tuple #[.map [], Y, .nil, f])) :
    ∃ T er, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "true") st =
        .ok (.tuple #[T, Y, er, f]) ∧ E T ∧
      (∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧
        w κ = some x) ∧ (Ds = [] → er = .nil) ∧ (rk ≠ [] → f = .atom "true") := by
  obtain ⟨R, rR, hR, swR⟩ := neg_keys_split (den := den) ef fb (n + 5) ok
  obtain ⟨R', rfl⟩ := atoms_of fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩
  have hRk : R' = [] ∨ rk = [] := by
    cases R' with
    | nil => exact Or.inl rfl
    | cons r rs =>
      obtain ⟨s, -, N, eN, -⟩ := hR _ List.mem_cons_self
      exact Or.inr (nr N eN)
  obtain ⟨T, er, run, hT, sT, hE, hF⟩ := dnf_old ef hn hv b lines hl rk neg Ds
    (fun s ms => by obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms') st R' rR hRk Y f h
  refine ⟨T, er, run, hT, fun x => ?_, hE, hF⟩
  rw [sT, ← pieces_sem ef lines hl sl ok hR swR x]
  simp only [List.mem_map, Term.atom.injEq, exists_eq_right]
  constructor
  · rintro (⟨s, ms, hh⟩ | ⟨a, ma | ma, hh⟩)
    · exact Or.inr ⟨s, ms, hh⟩
    · exact Or.inl (Or.inl ⟨a, ma, hh⟩)
    · exact Or.inl (Or.inr ⟨a, ma, hh⟩)
  · rintro ((⟨a, ma, hh⟩ | ⟨a, ma, hh⟩) | ⟨s, ms, hh⟩)
    · exact Or.inr ⟨a, Or.inl ma, hh⟩
    · exact Or.inr ⟨a, Or.inr ma, hh⟩
    · exact Or.inl ⟨s, ms, hh⟩

/-- `map_update_static/5` forcing a static value at a split of static keys: asking for the old values gives the same
result, with the values `map_get/2` selects as old values. -/
theorem upd_old_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "false") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "true") (.atom "true") =
          .ok (.atom "badmap")) ∨
        ∃ Y f, res = .tuple #[.map [], Y, .nil, f] ∧ ∃ T er, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6))
          (.map X) (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "true") (.atom "true") =
          .ok (.tuple #[T, Y, er, f]) ∧ E T ∧
          (∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧
            w κ = some x) ∧ (Ds = [] → er = .nil) ∧ (rk ≠ [] → f = .atom "true")) := by
  obtain ⟨res, run, hres⟩ := dput_update_static ef hn hv sv ok (fun N e => by rw [nr N e]; rfl) hNa hb fb
  refine ⟨res, run, ?_⟩
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
      have unf : ∀ rt, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) rt (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) (.tuple #[.integer k, tag, fieldsTerm l])
            (Term.list [Term.tuple #[tag, fieldsTerm l, Term.list []]]) (splitT (rk.map Term.atom) neg (Ds.map Term.atom))
            (forceOp v) rt (.atom "true") := fun rt => by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom, Term.list]
      rw [unf] at run
      rcases hres with ⟨rfl, emp⟩ | ⟨Y, f, rfl, -⟩
      · exact absurd ((sem w₀).mpr h₀) (by rw [emp w₀]; simp)
      · obtain ⟨T, er, r₁, hT, sT, hE, hF⟩ := dnf_old_sem ef hn hv fb _ hl inB ok nr _ Y f run
        exact Or.inr ⟨Y, f, rfl, T, er, by rw [unf]; exact r₁, hT, sT, hE, hF⟩
    · rcases hres with ⟨rfl, -⟩ | ⟨Y, f, rfl, ⟨w, hw⟩, -⟩
      · refine Or.inl ⟨rfl, ?_⟩
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom]
      · obtain ⟨N', mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 6) (by omega) rfl g sl
          (negs := []) (by simp) ri w ((sem w).mp hw)
        simp at mN
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
      rcases hres with ⟨rfl, -⟩ | ⟨Y, f, rfl, ⟨w, hw⟩, -⟩
      · refine Or.inl ⟨rfl, ?_⟩
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      · simpa using (inB w).mp hw
    | cons L rest =>
      have unf : ∀ rt, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) rt (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list (L :: rest))
            (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) rt (.atom "true") := fun rt => by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      rw [unf] at run
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      rcases hres with ⟨rfl, emp⟩ | ⟨Y, f, rfl, -⟩
      · exact absurd ((inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩) (by rw [emp w₀]; simp)
      · obtain ⟨T, er, r₁, hT, sT, hE, hF⟩ := dnf_old_sem ef hn hv fb _ hl inB ok nr _ Y f run
        exact Or.inr ⟨Y, f, rfl, T, er, by rw [unf]; exact r₁, hT, sT, hE, hF⟩

end

section
variable {t : Term} {n : Nat}

/-- `map_update_unchecked/4` forcing a static value at a split of static keys, in static types of the next level:
asking for the old values gives the same maps, or the same errors, with the values `map_get/2` selects as old values. -/
theorem upd_old_unchecked {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {v : Term}
    (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "false") = .ok res ∧
      ((res = .atom "badmap" ∧ Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "true") = .ok (.atom "badmap")) ∨
        ((∃ er, res = .tuple #[.atom "error", er]) ∧ (∃ er, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m)
          (.map X) (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "true") =
            .ok (.tuple #[.atom "error", er])) ∧ rk = []) ∨
        ∃ Y, res = .tuple #[.map [], Y, .nil] ∧ ∃ T er, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m)
          (.map X) (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "true") =
            .ok (.tuple #[T, Y, er]) ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧
            w κ = some x) ∧ (Ds = [] → er = .nil)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have sX := de_map hX
  have unf : ∀ rt, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (k + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) rt = _ := fun rt => by
    rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [unf, Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 6))
      (.function "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure]
  cases hb : mapLookup X (.atom "map") with
  | none =>
    refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, ?_⟩⟩ <;>
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso, bad,
      Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
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
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, run'⟩ | ⟨Y, f, rfl, T, er, run', hT, sT, hE, hF⟩⟩ :=
        upd_old_static (level t n).ef (n := k) (by omega) hv sv ok nr hNa hb fb
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
        · simp [key, mo, run', Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
      have sT' : ∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧
          w κ = some x := fun x => by rw [sT]; simp only [mt]
      by_cases fe : f = .atom "false" ∨ f = .atom "nil"
      · have rk0 : rk = [] := by
          cases rk with
          | nil => rfl
          | cons a rk => rcases fe with e | e <;> rw [hF (by simp)] at e <;> simp at e
        refine ⟨.tuple #[.atom "error", .nil], ?_, Or.inr (Or.inl ⟨⟨_, rfl⟩, ⟨er, ?_⟩, rk0⟩)⟩
        · rcases fe with rfl | rfl <;> simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rcases fe with rfl | rfl <;> simp [key, mo, run', Lynx.Except.andAlso, Lynx.Term.isMember]
      · have fe' := not_or.mp fe
        have fm : Lynx.Term.isMember f [.atom "false", .atom "nil"] = .atom "false" := by
          simp [Lynx.Term.isMember, compareExact_eq_atom, fe'.1, fe'.2]
        refine ⟨_, ?_, Or.inr (Or.inr ⟨Y, rfl, T, er, ?_, hT, sT', hE⟩)⟩
        · simp [key, mo, run, Lynx.Except.andAlso, fm]
        · simp [key, mo, run', Lynx.Except.andAlso, fm]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, ?_⟩⟩ <;>
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]

/-- `map_update/5` forcing a static value at a static key type and returning the old values, against `map_put/3`, in
static types of the next level: both give `:badmap`, or an error and no map without atom keys, or the same maps, with
the values `map_get/2` selects as old values. -/
theorem update_put_old {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key : Term} {rk Ds : List String}
    {neg : Term} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key =
      .ok (splitT (rk.map Term.atom) neg (Ds.map Term.atom)))
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none)
    (hm : (level t n).K + 26 ≤ m) :
    ∃ r₁ r₂, Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v = .ok r₁ ∧
      Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (.atom "force") (.atom "true") = .ok r₂ ∧
      ((r₁ = .atom "badmap" ∧ r₂ = .atom "badmap") ∨
        (r₁ = .tuple #[.atom "ok", .map []] ∧ (∃ er, r₂ = .tuple #[.atom "error", er]) ∧ rk = []) ∨
        ∃ Y T er, r₁ = .tuple #[.atom "ok", Y] ∧ r₂ = .tuple #[T, Y, er] ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧
            w κ = some x) ∧ (Ds = [] → er = .nil)) := by
  have sv' : v = .atom "term" ∨ ∃ Z, v = .map Z := sv.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
  have shared : Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v =
      (do
        let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "false")
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
  have upd : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (.atom "force") (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (forceOp v) (.atom "true") := by
    unfold Elixir.Module.Types.Descr.«map_update/5»
    rcases sv with rfl | ⟨Z, rfl, sZ⟩
    · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk, Lynx.Term.getMapKeys]
    · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk, getMapKeys_single, sZ]
  obtain ⟨res, run, ⟨rfl, run'⟩ | ⟨⟨er, rfl⟩, ⟨er', run'⟩, rk0⟩ | ⟨Y, rfl, T, er, run', hT, sT, hE⟩⟩ :=
    upd_old_unchecked hX hv sv' ok nr hNa hm
  · exact ⟨_, _, by rw [shared, run]; rfl, by rw [upd, run'], Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, _, by rw [shared, run]; rfl, by rw [upd, run'], Or.inr (Or.inl ⟨rfl, ⟨er', rfl⟩, rk0⟩)⟩
  · exact ⟨_, _, by rw [shared, run]; rfl, by rw [upd, run'], Or.inr (Or.inr ⟨Y, T, er, rfl, rfl, hT, sT, hE⟩)⟩

/-- `atom/1` on a non-empty list of atoms: a static key type whose split requires exactly those atoms. -/
theorem atoms_split (A : List String) (hA : A ≠ []) {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    ∃ (Y : List (Term × Term)) (rk : List String),
      Elixir.Module.Types.Descr.«atom/1» (Term.list (A.map Term.atom)) = .ok (.map Y) ∧
      DE (level t n).E (.map Y) ∧
      Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) (.map Y) =
        .ok (splitT (rk.map Term.atom) (.atom "nil") (([] : List String).map Term.atom)) ∧
      SplitOk (rk.map Term.atom) (.atom "nil") (([] : List String).map Term.atom) ∧ ∀ s, s ∈ rk ↔ s ∈ A := by
  have ha : ∀ a ∈ A.map Term.atom, ∃ s, a = .atom s := fun a ma => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp ma; exact ⟨s, rfl⟩
  obtain ⟨Y, rY, hY⟩ := key_type_run (t := t) (n := n) (A.map Term.atom) [] ha (by simp) (m := m) (by omega)
  obtain ⟨Y', rs, neg, ds, rY', rS, ok, sk⟩ := key_split (t := t) (n := n) (A.map Term.atom) [] ha (by simp)
    (m := m) hm
  rw [rY] at rY'; cases rY'
  have atomY : Elixir.Module.Types.Descr.«atom/1» (Term.list (A.map Term.atom)) = .ok (.map Y) := by
    cases A with
    | nil => exact absurd rfl hA
    | cons a A =>
      have := rY
      simp only [Elixir.STTDescrProofsTest.«key_type/2», Term.list, List.map] at this
      simp only [Term.list, List.map]
      cases hr : Elixir.Module.Types.Descr.«atom/1» (Term.cons (.atom a) (Term.list (A.map Term.atom))) with
      | error e => simp [hr] at this
      | ok r => simp [hr, Elixir.STTDescrProofsTest.«kinds_type/2»] at this; rw [this]
  -- No domain: the atom kind would select an atom outside the list.
  have ds0 : ds = [] := by
    cases ds with
    | nil => rfl
    | cons d rest =>
      exfalso
      obtain ⟨s, hs, rfl⟩ := ok.hds d List.mem_cons_self
      by_cases sa : s = "atom"
      · subst sa
        obtain ⟨N, rfl⟩ := ok.hatom.mp List.mem_cons_self
        obtain ⟨c, hc⟩ := fresh_str (A ++ keyStrs N)
        have := (sk (.atom c)).mp (Or.inr ⟨N, rfl, lookup_fresh' fun m => hc (List.mem_append_right _ m)⟩)
        simp only [KeysOf, List.mem_map, Term.atom.injEq, exists_eq_right, List.not_mem_nil, or_false] at this
        exact hc (List.mem_append_left _ this)
      · obtain ⟨k, rfl⟩ := domKind_of hs sa
        have := (sk (.dom k 0)).mp List.mem_cons_self
        simp [KeysOf] at this
  subst ds0
  have neg0 : neg = .atom "nil" := by
    rcases ok.hneg with e | ⟨N, e⟩
    · exact e
    · have := ok.hatom.mpr ⟨N, e⟩; simp at this
  subst neg0
  obtain ⟨rk, rfl⟩ := atoms_of ok.hrs
  refine ⟨Y, rk, atomY, hY.de, rS, ok, fun s => ?_⟩
  have := sk (.atom s)
  simp only [SplitKey, KeysOf, List.mem_map, Term.atom.injEq, exists_eq_right, List.not_mem_nil, or_false] at this
  simpa using this

/-- Map types of maps only. -/
theorem map_only_shape {c : Term} (hc : DE (level t n).E c) (h : ∀ q : PN t n, denD c q → q.1.1 = "map") :
    ∃ Z, c = .map Z := by
  rcases hc with rfl | ⟨Z, rfl, -⟩
  · have := h (aPt (.atom "a")) (denD_term _); simp [aPt] at this
  · exact ⟨Z, rfl⟩

/-- `puts/3` unites the puts at each atom of the maps of a type holding only maps. -/
theorem puts_run {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (only : MOnly t n X) {v : Term}
    (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∀ A : List String, ∃ Z, Elixir.STTDescrProofsTest.«puts/3» (D m) (.map X) (Term.list (A.map Term.atom)) v =
        .ok (.map Z) ∧ DE (level t n).E (.map Z) ∧ (∀ q : PN t n, denD (.map Z) q → q.1.1 = "map") ∧
      ∀ w, MT t n Z w ↔ ∃ a ∈ A, PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w) := by
  intro A
  induction A with
  | nil =>
    refine ⟨[], by simp [Elixir.STTDescrProofsTest.«puts/3», Term.list, Elixir.Module.Types.Descr.«none/0»],
      Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_, fun w => ?_⟩
    · rw [denD_map] at hq; simp [mapLookup, dn_none] at hq
    · simp [MT, mapLookup]
  | cons a A ih =>
    obtain ⟨Z', rZ', dZ', oZ', sZ'⟩ := ih
    obtain ⟨res, run, ⟨-, no⟩ | ⟨Ya, rfl, -, dYa, oYa, sYa⟩⟩ := put_map hX a hv sv hm
    · exact absurd only no
    obtain ⟨c, hc, rc, sc, -⟩ := (ef_next t n).union dYa dZ'
    have oc : ∀ q : PN t n, denD c q → q.1.1 = "map" := fun q hq => by
      rcases (sc q).mp hq with h | h
      · exact oYa q h
      · exact oZ' q h
    obtain ⟨Z, rfl⟩ := map_only_shape hc oc
    refine ⟨Z, ?_, hc, oc, fun w => ?_⟩
    · simp only [Term.list, List.map, Elixir.STTDescrProofsTest.«puts/3»] at rZ' ⊢
      simp [run, Erlang.erlang.«element/2», rZ', rc m (by omega)]
    · rw [← denD_mpt, sc, denD_mpt, denD_mpt, sYa, sZ']
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨a', ma, h⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨a', Or.inr ma, h⟩
      · rintro ⟨a', rfl | ma, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨a', ma, h⟩

end

end Elixir.STTDescrProofsTest.Nest
