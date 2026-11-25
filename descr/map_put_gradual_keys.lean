namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- Forcing without the old values, `map_update_static_dnf/6` reads the domains of a split only through their
concatenation. -/
theorem dnf_domains (m : Nat) (bdd dnf rs os neg : Term) (rds ods : List Term) (v st : Term) :
    Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D m) bdd dnf
        (.tuple #[rs, os, neg, Term.list rds, Term.list ods]) (forceOp v) (.atom "false") st =
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D m) bdd dnf
        (.tuple #[rs, os, neg, Term.list (rds ++ ods), .nil]) (forceOp v) (.atom "false") st := by
  have appNil : Erlang.erlang.«++/2» (Term.list (rds ++ ods)) .nil = .ok (Term.list (rds ++ ods)) := by
    simpa using append_list (rds ++ ods) []
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [forceOp, Erlang.erlang.«==/2», Erlang.erlang.«not/1», Lynx.Term.isMember, append_list, appNil]

theorem foldl1_list_append (d : Dispatcher) (f : Term) : ∀ (xs ys : List Term) (acc : Term),
    Erlang.lists.«foldl_1/3» d f acc (Term.list (xs ++ ys)) =
      (Erlang.lists.«foldl_1/3» d f acc (Term.list xs) >>= fun r => Erlang.lists.«foldl_1/3» d f r (Term.list ys))
  | [], ys, acc => by simp [Erlang.lists.«foldl_1/3»]
  | x :: xs, ys, acc => by
    rw [List.cons_append]
    simp only [Term.list]
    rw [Erlang.lists.«foldl_1/3».eq_def, Erlang.lists.«foldl_1/3».eq_def]
    simp only
    cases d.pure f #[x, acc] with
    | error e => rfl
    | ok a => simpa using foldl1_list_append d f xs ys a

theorem foldl_fun (d : Dispatcher) (mo nm : String) (c : Array Term) (acc : Term) (xs : List Term) :
    Erlang.lists.«foldl/3» d (.function false mo nm 2 c) acc (Term.list xs) =
      Erlang.lists.«foldl_1/3» d (.function false mo nm 2 c) acc (Term.list xs) := by
  cases xs with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»]
  | cons x xs =>
    simp only [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Term.list]
    conv => rhs; rw [Erlang.lists.«foldl_1/3».eq_def]
    simp

/-- Forcing without the old values, the step of `map_update_named_keys/8` does not read whether the key is
required. -/
theorem named_step_req (d : Dispatcher) (dnf v st build key acc : Term) :
    Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf (forceOp v) (.atom "true") st build
        (.atom "false") (.atom "true") key acc =
      Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf (forceOp v) (.atom "false") st build
        (.atom "false") (.atom "true") key acc := by
  unfold Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»
  split
  · unfold Elixir.Module.Types.Descr.«map_update_named_key/5»
    by_cases hb : build = .atom "false"
    · subst hb; simp [forceOp, Lynx.Term.isMember]
    by_cases ht : build = .atom "true"
    · subst ht
      simp only [forceOp, Lynx.Term.isMember]
      cases Elixir.Module.Types.Descr.«map_dnf_pop_key/2» d dnf key <;> simp
    · split <;> simp_all [forceOp]
  · rfl

/-- Forcing without the old values, `map_update_named_keys/8` folds the step over the keys. -/
theorem named_keys_fold (m : Nat) (acc dnf v req st build : Term) (keys : List Term) :
    Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf (Term.list keys) (forceOp v) req st
        (.atom "false") build =
      Erlang.lists.«foldl_1/3» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
        #[dnf, forceOp v, req, st, build, .atom "false", .atom "true"]) acc (Term.list keys) := by
  simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», forceOp, Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
    Erlang.erlang.«not/1», Lynx.Except.orElse, foldl_fun]

theorem named_keys_req (m : Nat) (acc dnf v st build : Term) (keys : List Term) :
    Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf (Term.list keys) (forceOp v) (.atom "true")
        st (.atom "false") build =
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf (Term.list keys) (forceOp v)
        (.atom "false") st (.atom "false") build := by
  rw [named_keys_fold, named_keys_fold]
  refine foldl1_congr _ _ _ (fun x a => ?_) _ acc
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
    Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure, named_step_req]

/-- Forcing without the old values and without a negated set, `map_update_static_dnf/6` puts optional keys as
required ones. -/
theorem dnf_optional (m : Nat) (bdd dnf : Term) (rs os ds : List Term) (v st : Term) :
    Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf
        (.tuple #[Term.list rs, Term.list os, .atom "nil", Term.list ds, .nil]) (forceOp v) (.atom "false") st =
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf
        (.tuple #[Term.list (rs ++ os), .nil, .atom "nil", Term.list ds, .nil]) (forceOp v) (.atom "false") st := by
  have app1 : Erlang.erlang.«++/2» (Term.list []) (Term.list os) = .ok (Term.list os) := by
    simpa using append_list [] os
  have app2 : Erlang.erlang.«++/2» (Term.list []) .nil = .ok .nil := by simpa using append_list [] []
  have app3 : Erlang.erlang.«++/2» (Term.list ds) .nil = .ok (Term.list ds) := by simpa using append_list ds []
  have e0 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have nilL : Term.list ([] : List Term) = .nil := rfl
  have nkNil : ∀ acc req build, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf .nil
      (forceOp v) req st (.atom "false") build = .ok acc := fun acc req build => by
    rw [← nilL, named_keys_fold]; simp [Erlang.lists.«foldl_1/3»]
  have req : ∀ acc, Erlang.lists.«foldl_1/3» (D (m + 1)) (.function false "Elixir.Module.Types.Descr"
      "-map_update_named_keys/8-fun-0-" 2 #[dnf, forceOp v, .atom "true", st, .atom "true", .atom "false", .atom "true"])
      acc (Term.list os) = Erlang.lists.«foldl_1/3» (D (m + 1)) (.function false "Elixir.Module.Types.Descr"
      "-map_update_named_keys/8-fun-0-" 2 #[dnf, forceOp v, .atom "false", st, .atom "true", .atom "false",
        .atom "true"]) acc (Term.list os) := fun acc => by
    rw [← named_keys_fold, ← named_keys_fold, named_keys_req]
  have nkNil' : ∀ acc req build, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf .nil
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) req st (.atom "false") build =
      .ok acc := nkNil
  have fold' : ∀ acc req build (keys : List Term), Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc
      dnf (Term.list keys) (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) req st
      (.atom "false") build =
      Erlang.lists.«foldl_1/3» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
        #[dnf, forceOp v, req, st, build, .atom "false", .atom "true"]) acc (Term.list keys) :=
    fun acc req build keys => named_keys_fold m acc dnf v req st build keys
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [forceOp, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Erlang.erlang.«not/1», Lynx.Term.isMember,
    Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«--/2», Term.properList?, e0,
    nkNil', fold', foldl1_list_append, app1, app2, app3]
  cases ds with
  | nil => simp [Term.list, req]
  | cons d ds =>
    have ne : Term.compare ((Term.list (d :: ds)).fuel .nil) (Term.list (d :: ds)) .nil ≠ .eq := by
      rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep]
    simp [ne, req]
  done

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_static_dnf/6` putting a non-empty static value at the atoms outside a negated set and the domains. -/
theorem negreq_static_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ []) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (N : List (Term × Term))
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (hks : ∀ s ∈ ks, mapLookup N (.atom s) = none)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks)
    (ds : List Term) (hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) (hat : .atom "atom" ∈ ds)
    (A : List String) (hA : ∀ a ∈ A, mapLookup N (.atom a) ≠ none) :
    ∃ Y, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (.tuple #[Term.list (A.map Term.atom), .nil, .map N, Term.list ds, .nil]) (forceOp v) (.atom "false") (.atom "true") =
        .ok (.tuple #[.map [], Y, .nil, .atom "true"]) ∧
      ((Y = .map [] ∧ ∀ w, ¬(UnionS den (fun u => ∃ L ∈ lines, InMLine den L u) (fun a => a ∈ A) v w ∨
          NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w)) ∨
        ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔
          UnionS den (fun u => ∃ L ∈ lines, InMLine den L u) (fun a => a ∈ A) v w ∨
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
  have kdA' : List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      (ks.map Term.atom) (A.map Term.atom) = ks.map Term.atom := by
    have : ∀ B : List String, (∀ a ∈ B, a ∈ A) → List.foldl (fun acc y => List.eraseP
        (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc) (ks.map Term.atom) (B.map Term.atom) = ks.map Term.atom := by
      intro B
      induction B with
      | nil => intro _; rfl
      | cons b B ih =>
        intro hB
        simp only [List.map_cons, List.foldl_cons]
        rw [List.eraseP_of_forall_not]
        · exact ih fun a m => hB a (List.mem_cons_of_mem _ m)
        · intro x mx
          obtain ⟨k, mk, rfl⟩ := List.mem_map.mp mx
          simp only [decide_eq_true_eq, compareExact_eq_atom]
          intro e
          injection e with e
          subst e
          exact hA k (hB k List.mem_cons_self) (hks k mk)
    exact this A fun a m => m
  have kdA : Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) (Term.list (A.map Term.atom)) =
      .ok (Term.list (ks.map Term.atom)) := by
    simp [Erlang.erlang.«--/2», kdA']
  have kd0 : Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simp [Erlang.erlang.«--/2», Term.properList?]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, kd0, kdA,
    Erlang.erlang.«not/1», Erlang.sets.«to_list/1»,
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
  have M : ∀ (bs : List Term), (∀ b ∈ bs, MField E b) → ∃ r, Elixir.Module.Types.Descr.«map_union_all/1» (D (n + 6))
      (Term.list bs) = .ok r ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔ ∃ b ∈ bs, denMF E den b w = Bool.true :=
    fun bs fb => by
      obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 6) (by omega) (ok := fun _ => True)
        (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bs (Nat.le_refl _) fun b mb => ⟨fb b mb, by
          rcases fb b mb with ⟨k, rfl⟩ | wb
          · exact Or.inl ⟨k, rfl⟩
          · exact Or.inr (wb.mono fun _ _ => trivial)⟩
      exact ⟨r, rr, fr, sr⟩
  have unionSem : ∀ w, (∃ a ∈ A, PutAt den v a w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w)) ↔
      UnionS den (fun u => ∃ L ∈ lines, InMLine den L u) (fun a => a ∈ A) v w := fun w => by
    simp only [UnionS]
    constructor
    · rintro ⟨a, ma, p, L, mL, o, h⟩; exact ⟨a, ma, p, o, L, mL, h⟩
    · rintro ⟨a, ma, p, o, L, mL, h⟩; exact ⟨a, ma, p, L, mL, o, h⟩
  -- The puts at the required atoms, with the maps of the box and the widened domains.
  have fin : ∀ (bs0 : List Term), (∀ b ∈ bs0, MField E b) → (∀ w, (∃ b ∈ bs0, denMF E den b w = Bool.true) ↔
      NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w) →
      ∃ bs r, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
          (.tuple #[.map [], Term.list bs0, .nil, .atom "true"]) (Term.list lines) (Term.list (A.map Term.atom))
          (forceOp v) (.atom "true") (.atom "true") (.atom "false") (.atom "true") =
          .ok (.tuple #[.map [], Term.list (bs ++ bs0), .nil, .atom "true"]) ∧
        Elixir.Module.Types.Descr.«map_union_all/1» (D (n + 6)) (Term.list (bs ++ bs0)) = .ok r ∧ MField E r ∧
        ∀ w, denMF E den r w = Bool.true ↔
          UnionS den (fun u => ∃ L ∈ lines, InMLine den L u) (fun a => a ∈ A) v w ∨
          NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w := by
    intro bs0 fb0 sb0
    obtain ⟨bs, rbs, fbs, sbs⟩ := union_named ef (n := n + 2) (by omega) hv lines hl A bs0 Bool.true
    obtain ⟨r, rr, fr, sr⟩ := M (bs ++ bs0) fun b mb => by
      rcases List.mem_append.mp mb with mb | mb
      · exact fbs b mb
      · exact fb0 b mb
    refine ⟨bs, r, by simpa [boolAtom] using rbs, rr, fr, fun w => ?_⟩
    rw [sr, ← unionSem, ← sbs, ← sb0]
    simp only [List.mem_append]
    constructor
    · rintro ⟨b, mb | mb, hb⟩
      · exact Or.inl ⟨b, mb, hb⟩
      · exact Or.inr ⟨b, mb, hb⟩
    · rintro (⟨b, mb, hb⟩ | ⟨b, mb, hb⟩)
      · exact ⟨b, Or.inl mb, hb⟩
      · exact ⟨b, Or.inr mb, hb⟩
  simp [dsCmp, lenK]
  by_cases full : FullDs ds
  · have hL : Ks.length = 12 := lenKs.mpr full
    have hL' : ((Ks.length : Int) = 12) := by omega
    obtain ⟨NK, R, rR, akNK, lnNK, orNK, mR⟩ := box_runAll ef (n := n + 2) (by omega) lines bdd hl hne hv vne ks AK Ks
      subKs aK hL
    simp [hL', rR, Erlang.erlang.«element/2»]
    have bridge : ∀ w, (BoxSynD den lines ks NK Ks v w ∧ w ≠ wNone) ↔
        NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w := fun w => by
      rw [boxSynD_iff ef lines hl hne v (setStrs N) ks AK NK Ks aK hks' hAK akNK lnNK orNK lnKS' w]
      have eq : (fun d => d ∈ Ks) = (fun d => Term.atom d ∈ ds) := funext fun d => propext (mKs d)
      simp only [NegSem, full, true_and, not_true_eq_false, false_and, or_false, eq]
    rcases mapsD_cases mR with ⟨rfl, emp⟩ | ⟨c, ne, lc, fc, sc⟩
    · obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [] (by simp) (fun w => ⟨fun ⟨b, mb, _⟩ => by simp at mb, fun h => absurd ((bridge w).mpr h) (emp w)⟩)
      simp only [Term.list, List.append_nil] at rbs rr
      by_cases bot : r = .atom "bdd_bot"
      · subst bot
        refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w => not_or.mp fun h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩⟩
        simp [rbs, runs, rr]
      · refine ⟨.map [(.atom "map", r)], ?_, Or.inr ⟨r, rfl, fr, sem⟩⟩
        simp [rbs, runs, rr]
    · obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [c] (by simpa using fc) (fun w => by simpa using (sc w).trans (bridge w))
      simp only [Term.list] at rbs rr
      by_cases bot : r = .atom "bdd_bot"
      · subst bot
        refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w => not_or.mp fun h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩⟩
        simp [ne, getMapKeys_single, lc, Term.list, rbs, runs, rr]
      · refine ⟨.map [(.atom "map", r)], ?_, Or.inr ⟨r, rfl, fr, sem⟩⟩
        simp [ne, getMapKeys_single, lc, Term.list, rbs, runs, rr]
  · have hL : Ks.length ≠ 12 := fun h => full (lenKs.mp h)
    have hL' : ¬((Ks.length : Int) = 12) := by omega
    let Ws := Ks.filter (· ≠ "atom")
    have mWs : ∀ s, s ∈ Ws ↔ s ∈ Ks ∧ s ≠ "atom" := fun s => by simp [Ws]
    have part := partition_atom (n + 5) Ks
    rw [filter_eq_single ndKs aK] at part
    obtain ⟨NK, res, rres, akNK, lnNK, orNK, hres⟩ := box_runD ef (n := n + 2) (by omega) lines bdd hl hne hv sv vne ks AK
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
      · obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [] (by simp) (fun w => ⟨fun ⟨b, mb, _⟩ => by simp at mb, fun h => absurd ((bridge w).mpr h) (emp w)⟩)
        simp only [Term.list, List.append_nil] at rbs rr
        by_cases bot : r = .atom "bdd_bot"
        · subst bot
          refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w => not_or.mp fun h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩⟩
          simp [rbs, runs, rr]
        · refine ⟨.map [(.atom "map", r)], ?_, Or.inr ⟨r, rfl, fr, sem⟩⟩
          simp [rbs, runs, rr]
      · obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [c] (by simpa using fc) (fun w => by simpa using (sc w).trans (bridge w))
        simp only [Term.list] at rbs rr
        by_cases bot : r = .atom "bdd_bot"
        · subst bot
          refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w => not_or.mp fun h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩⟩
          simp [ne, getMapKeys_single, lc, Term.list, rbs, runs, rr]
        · refine ⟨.map [(.atom "map", r)], ?_, Or.inr ⟨r, rfl, fr, sem⟩⟩
          simp [ne, getMapKeys_single, lc, Term.list, rbs, runs, rr]
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
      · obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [] (by simp) (fun w => ⟨fun ⟨b, mb, _⟩ => by simp at mb, fun h => absurd ((bridge w).mpr h) (emp w)⟩)
        simp only [Term.list, List.append_nil] at rbs rr
        by_cases bot : r = .atom "bdd_bot"
        · subst bot
          refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w => not_or.mp fun h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩⟩
          simp [rbs, runs, rr]
        · refine ⟨.map [(.atom "map", r)], ?_, Or.inr ⟨r, rfl, fr, sem⟩⟩
          simp [rbs, runs, rr]
      · obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [c] (by simpa using fc) (fun w => by simpa using (sc w).trans (bridge w))
        simp only [Term.list] at rbs rr
        by_cases bot : r = .atom "bdd_bot"
        · subst bot
          refine ⟨.map [], ?_, Or.inl ⟨rfl, fun w => not_or.mp fun h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩⟩
          simp [ne, getMapKeys_single, lc, Term.list, rbs, runs, rr]
        · refine ⟨.map [(.atom "map", r)], ?_, Or.inr ⟨r, rfl, fr, sem⟩⟩
          simp [ne, getMapKeys_single, lc, Term.list, rbs, runs, rr]

theorem negreq_static_dnf_empty (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) {v : Term} (hv : E v) (nv : ¬∃ x, den v x)
    (N : List (Term × Term)) (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (hks : ∀ s ∈ ks, mapLookup N (.atom s) = none)
    (ds : List Term) (hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) (hat : .atom "atom" ∈ ds)
    (A : List String) (hA : ∀ a ∈ A, mapLookup N (.atom a) ≠ none) :
    ∃ Y, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (.tuple #[Term.list (A.map Term.atom), .nil, .map N, Term.list ds, .nil]) (forceOp v) (.atom "false") (.atom "true") =
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
  have kdA' : List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      (ks.map Term.atom) (A.map Term.atom) = ks.map Term.atom := by
    have : ∀ B : List String, (∀ a ∈ B, a ∈ A) → List.foldl (fun acc y => List.eraseP
        (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc) (ks.map Term.atom) (B.map Term.atom) = ks.map Term.atom := by
      intro B
      induction B with
      | nil => intro _; rfl
      | cons b B ih =>
        intro hB
        simp only [List.map_cons, List.foldl_cons]
        rw [List.eraseP_of_forall_not]
        · exact ih fun a m => hB a (List.mem_cons_of_mem _ m)
        · intro x mx
          obtain ⟨k, mk, rfl⟩ := List.mem_map.mp mx
          simp only [decide_eq_true_eq, compareExact_eq_atom]
          intro e
          injection e with e
          subst e
          exact hA k (hB k List.mem_cons_self) (hks k mk)
    exact this A fun a m => m
  have kdA : Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) (Term.list (A.map Term.atom)) =
      .ok (Term.list (ks.map Term.atom)) := by
    simp [Erlang.erlang.«--/2», kdA']
  have kd0 : Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simp [Erlang.erlang.«--/2», Term.properList?]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, kd0, kdA,
    Erlang.erlang.«not/1», Erlang.sets.«to_list/1»,
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
  have M : ∀ (bs : List Term), (∀ b ∈ bs, MField E b) → ∃ r, Elixir.Module.Types.Descr.«map_union_all/1» (D (n + 6))
      (Term.list bs) = .ok r ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔ ∃ b ∈ bs, denMF E den b w = Bool.true :=
    fun bs fb => by
      obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 6) (by omega) (ok := fun _ => True)
        (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bs (Nat.le_refl _) fun b mb => ⟨fb b mb, by
          rcases fb b mb with ⟨k, rfl⟩ | wb
          · exact Or.inl ⟨k, rfl⟩
          · exact Or.inr (wb.mono fun _ _ => trivial)⟩
      exact ⟨r, rr, fr, sr⟩
  -- The puts at the required atoms of an empty value hold no map.
  have fin : ∀ (bs0 : List Term), (∀ b ∈ bs0, MField E b) → (∀ b ∈ bs0, ∀ w, denMF E den b w = Bool.false) →
      ∃ bs r, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
          (.tuple #[.map [], Term.list bs0, .nil, .atom "true"]) (Term.list lines) (Term.list (A.map Term.atom))
          (forceOp v) (.atom "true") (.atom "true") (.atom "false") (.atom "true") =
          .ok (.tuple #[.map [], Term.list (bs ++ bs0), .nil, .atom "true"]) ∧
        Elixir.Module.Types.Descr.«map_union_all/1» (D (n + 6)) (Term.list (bs ++ bs0)) = .ok r ∧ MField E r ∧
        ∀ w, denMF E den r w = Bool.false := by
    intro bs0 fb0 sb0
    obtain ⟨bs, rbs, fbs, sbs⟩ := union_named ef (n := n + 2) (by omega) hv lines hl A bs0 Bool.true
    obtain ⟨r, rr, fr, sr⟩ := M (bs ++ bs0) fun b mb => by
      rcases List.mem_append.mp mb with mb | mb
      · exact fbs b mb
      · exact fb0 b mb
    refine ⟨bs, r, by simpa [boolAtom] using rbs, rr, fr, fun w => Bool.eq_false_iff.mpr fun h => ?_⟩
    obtain ⟨b, mb, hb⟩ := (sr w).mp h
    rcases List.mem_append.mp mb with mb | mb
    · obtain ⟨a, -, ⟨x, -, hx⟩, -⟩ := (sbs w).mp ⟨b, mb, hb⟩
      exact nv ⟨x, hx⟩
    · rw [sb0 b mb w] at hb; cases hb
  have box := fun Ds hD => box_run_empty ef (n := n + 2) (by omega) lines bdd hl hv nv ks AK Ds hD
  simp [dsCmp, lenK]
  by_cases full : FullDs ds
  · have hL' : ((Ks.length : Int) = 12) := by have := lenKs.mpr full; omega
    have MM : MapsD E den [] (fun _ => False) := mapsD_nil fun _ h => h
    simp [hL', box Ks subKs, Erlang.erlang.«element/2»]
    obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [] (by simp) (by simp)
    simp only [Term.list, List.append_nil] at rbs rr
    by_cases bot : r = .atom "bdd_bot"
    · subst bot
      exact ⟨.map [], by simp [rbs, runs, rr], Or.inl rfl⟩
    · exact ⟨.map [(.atom "map", r)], by simp [rbs, runs, rr], Or.inr ⟨r, rfl, fr, sem⟩⟩
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
      obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [] (by simp) (by simp)
      simp only [Term.list, List.append_nil] at rbs rr
      by_cases bot : r = .atom "bdd_bot"
      · subst bot
        exact ⟨.map [], by simp [rbs, runs, rr], Or.inl rfl⟩
      · exact ⟨.map [(.atom "map", r)], by simp [rbs, runs, rr], Or.inr ⟨r, rfl, fr, sem⟩⟩
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
      · obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [] (by simp) (by simp)
        simp only [Term.list, List.append_nil] at rbs rr
        by_cases bot : r = .atom "bdd_bot"
        · subst bot
          exact ⟨.map [], by simp [rbs, runs, rr], Or.inl rfl⟩
        · exact ⟨.map [(.atom "map", r)], by simp [rbs, runs, rr], Or.inr ⟨r, rfl, fr, sem⟩⟩
      · obtain ⟨bs, r, rbs, rr, fr, sem⟩ := fin [c] (by simpa using fc) (by simpa using fun w => Bool.eq_false_iff.mpr fun h => (sc w).mp h)
        simp only [Term.list] at rbs rr
        by_cases bot : r = .atom "bdd_bot"
        · subst bot
          exact ⟨.map [], by simp [ne, getMapKeys_single, lc, Term.list, rbs, runs, rr], Or.inl rfl⟩
        · exact ⟨.map [(.atom "map", r)], by simp [ne, getMapKeys_single, lc, Term.list, rbs, runs, rr], Or.inr ⟨r, rfl, fr, sem⟩⟩

end

/-- The puts at required atoms inside a negated set, and at the atoms outside it and some kinds. -/
theorem dnfPuts_req {A : List String} {N : List (Term × Term)} {ds : List Term}
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s)
    (hat : .atom "atom" ∈ ds) (hA : ∀ a ∈ A, mapLookup N (.atom a) ≠ none) :
    DnfPuts (.tuple #[Term.list (A.map Term.atom), .nil, .map N, Term.list ds, .nil]) (.map N)
      (fun den M v w => PutSem den M (A.map Term.atom) (.atom "nil") [] v w ∨ PutSem den M [] (.map N) ds v w) := by
  intro nd E V den tl K ef n hn bdd lines hl hne v hv sv hneg
  obtain ⟨-, ks, hR, hks, lnKS⟩ := hneg N rfl
  have uS : ∀ (M : MW V → Prop) w, PutSem den M (A.map Term.atom) (.atom "nil") [] v w ↔
      UnionS den M (fun a => a ∈ A) v w := fun M w => by
    simp only [PutSem, List.mem_map, Term.atom.injEq, exists_eq_right, true_and, List.not_mem_nil, false_and,
      exists_false, or_false]
    constructor
    · rintro (h | ⟨N', e, -⟩)
      · exact h
      · cases e
    · exact Or.inl
  by_cases vne : ∃ x, den v x
  · obtain ⟨Y, run, h⟩ := negreq_static_dnf ef hn bdd lines hl hne hv sv vne N hNa ks hR hks lnKS ds hds hat A hA
    refine ⟨Y, _, run, Or.inl rfl, ?_⟩
    have conv : ∀ w, (PutSem den (fun u => ∃ L ∈ lines, InMLine den L u) (A.map Term.atom) (.atom "nil") [] v w ∨
        PutSem den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) ds v w) ↔
        (UnionS den (fun u => ∃ L ∈ lines, InMLine den L u) (fun a => a ∈ A) v w ∨
          NegSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) ds v w) := fun w => by
      rw [uS, putSem_neg vne]
    rcases h with ⟨rfl, emp⟩ | ⟨r, rfl, fr, sr⟩
    · exact Or.inl ⟨rfl, fun w hw => emp w ((conv w).mp hw)⟩
    · exact Or.inr ⟨r, rfl, fr, fun w => (sr w).trans (conv w).symm⟩
  · obtain ⟨Y, run, h⟩ := negreq_static_dnf_empty ef hn bdd lines hl hv vne N hNa ks hR hks ds hds hat A hA
    have none : ∀ w, ¬(PutSem den (fun u => ∃ L ∈ lines, InMLine den L u) (A.map Term.atom) (.atom "nil") [] v w ∨
        PutSem den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) ds v w) := fun w h =>
      h.elim (putSem_empty vne w) (putSem_empty vne w)
    refine ⟨Y, _, run, Or.inl rfl, ?_⟩
    rcases h with rfl | ⟨r, rfl, fr, sr⟩
    · exact Or.inl ⟨rfl, none⟩
    · exact Or.inr ⟨r, rfl, fr, fun w => by rw [sr w]; simp only [Bool.false_eq_true, false_iff]; exact none w⟩

/-- Splits updating alike update with the same maps. -/
theorem dnfPuts_eq {s₁ s₂ neg : Term} {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (h : ∀ m bdd dnf v, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf s₁ (forceOp v)
      (.atom "false") (.atom "true") = Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf s₂
        (forceOp v) (.atom "false") (.atom "true")) (hP : DnfPuts s₂ neg P) : DnfPuts s₁ neg P := by
  intro nd E V den tl K ef n hn bdd lines hl hne v hv sv hneg
  obtain ⟨Y, f, run, h₁, h₂⟩ := hP _ _ _ _ _ _ ef hn bdd lines hl hne hv sv hneg
  exact ⟨Y, f, by rw [h (n + 5)]; exact run, h₁, h₂⟩

theorem dnfPuts_iff {s neg : Term} {P Q : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts s neg P) (h : ∀ {V : Type} (den : Term → V → Prop) M v w, P den M v w ↔ Q den M v w) :
    DnfPuts s neg Q := by
  intro nd E V den tl K ef n hn bdd lines hl hne v hv sv hneg
  obtain ⟨Y, f, run, h₁, h₂⟩ := hP _ _ _ _ _ _ ef hn bdd lines hl hne hv sv hneg
  refine ⟨Y, f, run, h₁.imp id fun e w hw => e w ((h den _ v w).mpr hw), ?_⟩
  rcases h₂ with ⟨e, emp⟩ | ⟨r, e, fr, sr⟩
  · exact Or.inl ⟨e, fun w hw => emp w ((h den _ v w).mpr hw)⟩
  · exact Or.inr ⟨r, e, fr, fun w => (sr w).trans (h den _ v w)⟩

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

/-- Sets of atoms, as `atoms?/1` accepts them. -/
def ASet (S : List (Term × Term)) : Prop := ∀ e ∈ mapEntries S, (∃ s, e.1 = .atom s) ∧ e.2 = .nil

theorem atom_keys_aset : ∀ (es : List (Term × Term)),
    «atom_keys?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true →
      ∀ e ∈ es, (∃ s, e.1 = .atom s) ∧ e.2 = .nil
  | [], _ => by simp
  | ⟨k, w⟩ :: rest, h => by
    by_cases hw : w = .nil
    · subst hw
      simp only [List.map_cons, Term.list, «atom_keys?/1», Term.true, Lynx.Except.andAlso_eq_true] at h
      intro e me
      rcases List.mem_cons.mp me with rfl | me
      · cases k <;> simp [Erlang.erlang.«is_atom/1»] at h
        exact ⟨⟨_, rfl⟩, rfl⟩
      · exact atom_keys_aset rest (by simpa [Term.true] using h.2) e me
    · exfalso
      rw [«atom_keys?/1».eq_def] at h
      simp only [List.map_cons, Term.list] at h
      split at h <;> simp_all [Term.true]

theorem negatable_fields_set {depth : Term} : ∀ (es : List (Term × Term)),
    «negatable_fields?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true →
    ∀ tag S, (.atom "atom", .tuple #[.atom tag, .map S]) ∈ es → (tag = "union" ∨ tag = "negation") → ASet S
  | [], _ => by simp
  | ⟨k, w⟩ :: rest, h => by
    simp only [List.map_cons, Term.list, «negatable_fields?/2», Term.true, Lynx.Except.andAlso_eq_true] at h
    intro tag S mS htag
    rcases List.mem_cons.mp mS with e | mS
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have h1 := h.1
      unfold «negatable_field?/2» «nested_field?/2» at h1
      rcases htag with rfl | rfl
      · simp at h1
        simp only [Term.list, «valid_fields?/1», «atoms?/1», Erlang.maps.«to_list/1»,
          Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at h1
        exact fun e me => atom_keys_aset _ (by simpa [Term.list, Term.true] using h1.1.1) e me
      · simp at h1
        simp only [Term.list, «valid_fields?/1», «atoms?/1», Erlang.maps.«to_list/1»,
          Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at h1
        exact fun e me => atom_keys_aset _ (by simpa [Term.list, Term.true] using h1.1) e me
    · exact negatable_fields_set rest h.2 tag S mS htag

/-- The atom sets of static types of the laws are sets of atoms. -/
theorem static_atom_set {Y : List (Term × Term)} {d t : Term}
    (h : «arrows_static?/2» (.map Y) (.tuple #[d, t]) = .ok (.atom "true")) :
    ∀ tag S, mapLookup Y (.atom "atom") = some (.tuple #[.atom tag, .map S]) → (tag = "union" ∨ tag = "negation") →
      ASet S := by
  intro tag S hS htag
  simp only [«arrows_static?/2», «opt_negatable?/2», «negatable?/2», Erlang.maps.«to_list/1»,
    Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at h
  have fields := negatable_fields_set (depth := .tuple #[d, t]) (mapEntries Y)
    (by simpa [Term.true] using h.1.1)
  obtain ⟨p, mp, qp, ep⟩ := lookup_found _ _ _ (by rw [mapLookup_mapEntries]; exact hS)
  rw [atom_compareExact_eq] at qp
  obtain ⟨p₁, p₂⟩ := p
  simp only at qp ep
  subst qp ep
  exact fields tag S mp htag

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem aset_elements {S : List (Term × Term)} (h : ASet S) : Erlang.sets.elements? (.map S) = some S := by
  rw [Erlang.sets.elements_iff]
  intro key value found
  obtain ⟨e, me, -, rfl⟩ := entry_of_lookup_entries found
  exact (h e me).2

theorem aset_atom {S : List (Term × Term)} (h : ASet S) {q : Term} (hq : (mapLookup S q).isSome) :
    ∃ s, q = .atom s := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hq
  obtain ⟨e, me, qe, -⟩ := entry_of_lookup_entries hx
  obtain ⟨s, es⟩ := (h e me).1
  rw [es, compareExact_eq_atom] at qe
  exact ⟨s, qe⟩

/-- Sets of atoms list their atoms. -/
theorem aset_list {S : List (Term × Term)} (h : ASet S) (d : Dispatcher) :
    ∃ A : List String, Erlang.sets.«to_list/1» d (.map S) = .ok (Term.list (A.map Term.atom)) ∧
      ∀ s, s ∈ A ↔ (mapLookup S (.atom s)).isSome := by
  obtain ⟨A, hA⟩ : ∃ A : List String, (mapEntries S).map Prod.fst = A.map Term.atom := by
    have : ∀ es : List (Term × Term), (∀ e ∈ es, ∃ s, e.1 = .atom s) → ∃ A : List String, es.map Prod.fst = A.map Term.atom := by
      intro es
      induction es with
      | nil => exact fun _ => ⟨[], rfl⟩
      | cons e es ih =>
        intro he
        obtain ⟨s, hs⟩ := he e List.mem_cons_self
        obtain ⟨B, hB⟩ := ih fun x mx => he x (List.mem_cons_of_mem _ mx)
        exact ⟨s :: B, by simp [hs, hB]⟩
    exact this _ fun e me => (h e me).1
  refine ⟨A, by simp [Erlang.sets.«to_list/1», Erlang.maps.«keys/1», hA], fun s => ?_⟩
  constructor
  · intro ms
    have : Term.atom s ∈ (mapEntries S).map Prod.fst := by rw [hA]; exact List.mem_map_of_mem ms
    obtain ⟨e, me, he⟩ := List.mem_map.mp this
    rw [← he, mapLookup_of_mem_mapEntries me]; rfl
  · intro hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨e, me, ec, -⟩ := entry_of_lookup_entries hx
    have : e.1 ∈ (mapEntries S).map Prod.fst := List.mem_map_of_mem me
    rw [hA] at this
    obtain ⟨s', ms', es'⟩ := List.mem_map.mp this
    rw [← es', compareExact_eq_atom] at ec
    injection ec with ec; subst ec; exact ms'

/-- Set operations on sets of atoms give sets of atoms. -/
theorem aset_of_elements {R : List (Term × Term)} (hR : Erlang.sets.elements? (.map R) = some R)
    (ha : ∀ q, (mapLookup R q).isSome → ∃ s, q = .atom s) : ASet R := by
  intro e me
  have := (Erlang.sets.elements_iff R).mp hR e.1 e.2 (mapLookup_of_mem_mapEntries me)
  exact ⟨ha e.1 (by rw [mapLookup_of_mem_mapEntries me]; rfl), this⟩

theorem aset_union {S T : List (Term × Term)} (hS : ASet S) (hT : ASet T) :
    ∃ R, Erlang.sets.«union/2» (.map S) (.map T) = .ok (.map R) ∧ ASet R ∧
      ∀ q, (mapLookup R q).isSome = ((mapLookup S q).isSome || (mapLookup T q).isSome) := by
  obtain ⟨R, run, eR, mR⟩ := Erlang.sets.union_member _ _ S T (aset_elements hS) (aset_elements hT)
  refine ⟨R, run, aset_of_elements eR fun q hq => ?_, mR⟩
  rw [mR] at hq
  rcases Bool.or_eq_true_iff.mp hq with h | h
  · exact aset_atom hS h
  · exact aset_atom hT h

theorem aset_inter {S T : List (Term × Term)} (hS : ASet S) (hT : ASet T) :
    ∃ R, Erlang.sets.«intersection/2» (.map S) (.map T) = .ok (.map R) ∧ ASet R ∧
      ∀ q, (mapLookup R q).isSome = ((mapLookup S q).isSome && (mapLookup T q).isSome) := by
  obtain ⟨R, run, eR, mR⟩ := Erlang.sets.intersection_member _ _ S T (aset_elements hS) (aset_elements hT)
  refine ⟨R, run, aset_of_elements eR fun q hq => ?_, mR⟩
  rw [mR] at hq
  exact aset_atom hS (Bool.and_eq_true_iff.mp hq).1

theorem aset_sub {S T : List (Term × Term)} (hS : ASet S) (hT : ASet T) :
    ∃ R, Erlang.sets.«subtract/2» (.map S) (.map T) = .ok (.map R) ∧ ASet R ∧
      ∀ q, (mapLookup R q).isSome = ((mapLookup S q).isSome && !(mapLookup T q).isSome) := by
  obtain ⟨R, run, eR, mR⟩ := Erlang.sets.subtract_member _ _ S T (aset_elements hS) (aset_elements hT)
  refine ⟨R, run, aset_of_elements eR fun q hq => ?_, mR⟩
  rw [mR] at hq
  exact aset_atom hS (Bool.and_eq_true_iff.mp hq).1

theorem aset_hNa {S : List (Term × Term)} (h : ASet S) : ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s :=
  fun e me => (h e me).1

/-- The puts at any of a list of splits of static keys. -/
def PutAny (Ss : List (List Term × Term × List Term)) {V : Type} (den : Term → V → Prop) (M : MW V → Prop) (v : Term)
    (w : MW V) : Prop :=
  ∃ sp ∈ Ss, PutSem den M sp.1 sp.2.1 sp.2.2 v w

theorem putAny_single {sp : List Term × Term × List Term} {V : Type} (den : Term → V → Prop) (M : MW V → Prop)
    (v : Term) (w : MW V) : PutAny [sp] den M v w ↔ PutSem den M sp.1 sp.2.1 sp.2.2 v w := by
  simp [PutAny]

/-- Splits without a negated set put their optional atoms as required ones. -/
theorem dnfPuts_nil {rs os ds ods : List Term} (ok : SplitOk (rs ++ os) (.atom "nil") (ds ++ ods)) :
    DnfPuts (.tuple #[Term.list rs, Term.list os, .atom "nil", Term.list ds, Term.list ods]) (.atom "nil")
      (PutAny [(rs ++ os, .atom "nil", ds ++ ods)]) := by
  have h₁ : DnfPuts (splitT (rs ++ os) (.atom "nil") (ds ++ ods)) (.atom "nil")
      (fun den M v w => PutSem den M (rs ++ os) (.atom "nil") (ds ++ ods) v w) := dnfPuts_split ok fun N e => nomatch e
  have h₂ : DnfPuts (.tuple #[Term.list rs, Term.list os, .atom "nil", Term.list ds, Term.list ods]) (.atom "nil")
      (fun den M v w => PutSem den M (rs ++ os) (.atom "nil") (ds ++ ods) v w) := by
    apply dnfPuts_eq _ h₁
    intro m bdd dnf v
    exact (dnf_domains (m + 1) bdd dnf _ _ _ ds ods v _).trans (dnf_optional m bdd dnf rs os (ds ++ ods) v _)
  apply dnfPuts_iff h₂ fun den M v w => (putAny_single (sp := (rs ++ os, .atom "nil", ds ++ ods)) den M v w).symm

/-- Splits of atoms outside a negated set. -/
theorem dnfPuts_neg {N : List (Term × Term)} {ds ods : List Term} (ok : SplitOk [] (.map N) (ds ++ ods)) :
    DnfPuts (.tuple #[.nil, .nil, .map N, Term.list ds, Term.list ods]) (.map N) (PutAny [([], .map N, ds ++ ods)]) := by
  have h₁ : DnfPuts (splitT [] (.map N) (ds ++ ods)) (.map N)
      (fun den M v w => PutSem den M [] (.map N) (ds ++ ods) v w) := dnfPuts_split ok fun N e => rfl
  have h₂ : DnfPuts (.tuple #[.nil, .nil, .map N, Term.list ds, Term.list ods]) (.map N)
      (fun den M v w => PutSem den M [] (.map N) (ds ++ ods) v w) := by
    apply dnfPuts_eq _ h₁
    intro m bdd dnf v
    exact dnf_domains (m + 1) bdd dnf _ _ _ ds ods v _
  apply dnfPuts_iff h₂ fun den M v w => (putAny_single (sp := ([], .map N, ds ++ ods)) den M v w).symm

/-- Splits of required atoms inside a negated set, and of the atoms outside it. -/
theorem dnfPuts_req' {A : List String} {N : List (Term × Term)} {ds ods : List Term}
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (hds : ∀ d ∈ ds ++ ods, ∃ s ∈ domainKinds, d = .atom s)
    (hat : .atom "atom" ∈ ds ++ ods) (hA : ∀ a ∈ A, mapLookup N (.atom a) ≠ none) :
    DnfPuts (.tuple #[Term.list (A.map Term.atom), .nil, .map N, Term.list ds, Term.list ods]) (.map N)
      (PutAny [(A.map Term.atom, .atom "nil", []), ([], .map N, ds ++ ods)]) := by
  have h₁ : DnfPuts (.tuple #[Term.list (A.map Term.atom), .nil, .map N, Term.list (ds ++ ods), .nil]) (.map N)
      (fun den M v w => PutSem den M (A.map Term.atom) (.atom "nil") [] v w ∨ PutSem den M [] (.map N) (ds ++ ods) v w) :=
    dnfPuts_req hNa hds hat hA
  have h₂ : DnfPuts (.tuple #[Term.list (A.map Term.atom), .nil, .map N, Term.list ds, Term.list ods]) (.map N)
      (fun den M v w => PutSem den M (A.map Term.atom) (.atom "nil") [] v w ∨ PutSem den M [] (.map N) (ds ++ ods) v w) := by
    apply dnfPuts_eq _ h₁
    intro m bdd dnf v
    exact dnf_domains (m + 1) bdd dnf _ _ _ ds ods v _
  refine dnfPuts_iff h₂ ?_
  intro V den M v w
  simp [PutAny]

/-- List differences of atoms keep the atoms the second list misses. -/
theorem diff_atoms (a b : List Term) (ha : ∀ x ∈ a, ∃ s, x = .atom s) :
    ∃ c, Erlang.erlang.«--/2» (Term.list a) (Term.list b) = .ok (Term.list c) ∧ (∀ x ∈ c, x ∈ a) ∧
      ∀ x ∈ a, x ∉ b → x ∈ c := by
  refine ⟨List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc) a b,
    by simp [Erlang.erlang.«--/2»], ?_⟩
  induction b generalizing a with
  | nil => exact ⟨fun x h => h, fun x h _ => h⟩
  | cons y b ih =>
    simp only [List.foldl_cons]
    obtain ⟨h₁, h₂⟩ := ih (List.eraseP _ a) (fun x mx => ha x (List.mem_of_mem_eraseP mx))
    refine ⟨fun x mx => List.mem_of_mem_eraseP (h₁ x mx), fun x mx nb => h₂ x ?_ fun m => nb (List.mem_cons_of_mem _ m)⟩
    obtain ⟨s, rfl⟩ := ha x mx
    refine (List.mem_eraseP_of_neg ?_).mpr mx
    simp only [decide_eq_true_eq, atom_compareExact_eq]
    rintro rfl
    exact nb List.mem_cons_self

section
variable {t : Term} {n : Nat}

/-- The dynamic part of a gradual key type: as a map type, its kinds, and its sets of atoms. -/
theorem dyn_info {Dy : Term} (tD : TC (level t n) Dy)
    (aD : ∀ Y, Dy = .map Y → ∀ tag S, mapLookup Y (.atom "atom") = some (.tuple #[.atom tag, .map S]) →
      (tag = "union" ∨ tag = "negation") → ASet S)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ Yd dds, (Dy = .atom "term" ∧ Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map Yd) ∨ Dy = .map Yd) ∧
      DE (level t n).E (.map Yd) ∧ (∀ v : PN t n, denD Dy v ↔ denD (.map Yd) v) ∧
      Elixir.Module.Types.Descr.«to_domain_keys/1» (D (m + 1)) Dy = .ok (Term.list dds) ∧
      (∀ d ∈ dds, ∃ s ∈ domainKinds, d = .atom s) ∧
      (.atom "atom" ∈ dds ↔ ∃ S, mapLookup Yd (.atom "atom") = some (.tuple #[.atom "negation", .map S])) ∧
      (∀ s, s ≠ "atom" → (.atom s ∈ dds ↔ ∃ v : PN t n, denD (.map Yd) v ∧ ptKind v = s)) ∧
      ∀ tag S, mapLookup Yd (.atom "atom") = some (.tuple #[.atom tag, .map S]) → (tag = "union" ∨ tag = "negation") →
        ASet S := by
  rcases tD with rfl | ⟨Y, rfl, sY⟩
  · obtain ⟨T, term, -, dT, -, -, all⟩ := termN t n
    have tA : mapLookup T (.atom "atom") = some (.tuple #[.atom "negation", .map []]) := by
      have := term
      simp [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
      subst this; rfl
    obtain ⟨dsT, -, hdsT, -, hkT⟩ := dom_kinds dT hm
    refine ⟨T, domainKinds.map Term.atom, Or.inl ⟨rfl, term⟩, dT, fun v => ⟨fun _ => all v, fun _ => denD_term _⟩,
      ?_, fun d md => ?_, ⟨fun _ => ⟨[], tA⟩, fun _ => List.mem_map_of_mem (by simp [domainKinds])⟩, fun s ns => ?_,
      fun tag S h _ => ?_⟩
    · rw [Elixir.Module.Types.Descr.«to_domain_keys/1».eq_def]
      simp [domainKinds, Term.list]
    · obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, ms, rfl⟩
    · constructor
      · intro ms
        obtain ⟨s', ms', e⟩ := List.mem_map.mp ms
        injection e with e
        subst e
        obtain ⟨Y, -, kY⟩ := key_type_run (t := t) (n := n) [] (domainKinds.map Term.atom) (by simp)
          (fun d md => by obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, ms, rfl⟩) (m := m + 1) (by omega)
        obtain ⟨v, -, pv⟩ := kY.wit s' ms ns
        exact ⟨v, all v, pv⟩
      · intro h
        obtain ⟨s', ms', e⟩ := hdsT _ ((hkT s ns).mpr h)
        cases e
        exact List.mem_map_of_mem ms'
    · rw [tA] at h
      cases h
      intro e me
      simp at me
  · obtain ⟨ds, rd, hds, hat, hk⟩ := dom_kinds (Or.inr ⟨Y, rfl, sY⟩ : DE (level t n).E (.map Y)) hm
    exact ⟨Y, ds, Or.inr rfl, Or.inr ⟨Y, rfl, sY⟩, fun v => Iff.rfl, rd, hds, hat, hk, aD Y rfl⟩

end

section
variable {t : Term} {n : Nat}

/-- `map_split_keys_and_domains/1` on a gradual key type of the laws: splits of static keys whose puts give the puts
of the split, and whose keys are those of the dynamic part. -/
theorem gsplit {X : List (Term × Term)} {Dy : Term} (gk : GC (level t n) (.map X))
    (hD : mapLookup X (.atom "dynamic") = some Dy)
    (aS : ∀ tag S, mapLookup X (.atom "atom") = some (.tuple #[.atom tag, .map S]) →
      (tag = "union" ∨ tag = "negation") → ASet S)
    (aD : ∀ Y, Dy = .map Y → ∀ tag S, mapLookup Y (.atom "atom") = some (.tuple #[.atom tag, .map S]) →
      (tag = "union" ∨ tag = "negation") → ASet S)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ s neg Ss, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.map X) = .ok s ∧
      (∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ DnfPuts s neg (PutAny Ss) ∧
      (∀ sp ∈ Ss, SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = []) ∧
      ∀ κ, (∃ sp ∈ Ss, SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
  obtain ⟨tD, dS, incl⟩ : TC (level t n) Dy ∧ DE (level t n).E (.map (rmDyn X)) ∧
      ∀ q : TP (level t n), denD (.map X) q → denD Dy q := by
    rcases gk with tX | ⟨X', Dy', e, hD', tD, dS, incl⟩
    · rcases tX with h | ⟨X', e, sX'⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e
      rw [hD] at hD'; cases hD'
      exact ⟨tD, Or.inr ⟨_, rfl, dS⟩, incl⟩
  obtain ⟨Yd, dds, unf, dY, semY, rdd, hdds, hdat, hdk, aY⟩ := dyn_info tD aD hm
  obtain ⟨rds, rrd, hrds, hrat, hrk⟩ := dom_kinds dS hm
  have lX : mapLookup (rmDyn X) (.atom "atom") = mapLookup X (.atom "atom") := lookup_rmDyn_name X (by decide)
  obtain ⟨odds, rod, sod, ind⟩ := diff_atoms dds rds fun x mx => let ⟨s, _, e⟩ := hdds x mx; ⟨s, e⟩
  have rem : Erlang.maps.«remove/2» (.atom "dynamic") (.map X) = .ok (.map (rmDyn X)) := rfl
  -- Atoms and kinds of the static part are those of the dynamic part.
  have inclA : ∀ s, amemV (mapLookup X (.atom "atom")) (.atom s) = Bool.true →
      amemV (mapLookup Yd (.atom "atom")) (.atom s) = Bool.true := fun s h =>
    (denD_aPt (t := t) (n := n) (Y := Yd) _).mp ((semY _).mp (incl _ ((denD_aPt (t := t) (n := n) (Y := X) _).mpr h)))
  have keyA : ∀ s, KeyPt t n Dy (.atom s) ↔ amemV (mapLookup Yd (.atom "atom")) (.atom s) = Bool.true := fun s =>
    (semY _).trans (denD_aPt _)
  have inclK : ∀ k, Term.atom (domKind k) ∈ rds → Term.atom (domKind k) ∈ dds := fun k h => by
    obtain ⟨v, hv, pv⟩ := (hrk _ (domKind_ne_atom k)).mp h
    exact (hdk _ (domKind_ne_atom k)).mpr ⟨v, (semY v).mp (incl v ((denD_rmDyn X v).mp hv)), pv⟩
  have dsK : ∀ k i, Term.atom (domKind k) ∈ rds ++ odds ↔ KeyPt t n Dy (.dom k i) := fun k i => by
    have : KeyPt t n Dy (.dom k i) ↔ Term.atom (domKind k) ∈ dds :=
      ⟨fun ⟨v, hv, pv⟩ => (hdk _ (domKind_ne_atom k)).mpr ⟨v, (semY v).mp hv, pv⟩, fun h =>
        let ⟨v, hv, pv⟩ := (hdk _ (domKind_ne_atom k)).mp h; ⟨v, (semY v).mpr hv, pv⟩⟩
    rw [this, List.mem_append]
    constructor
    · rintro (h | h)
      · exact inclK k h
      · exact sod _ h
    · intro h
      by_cases r : Term.atom (domKind k) ∈ rds
      · exact Or.inl r
      · exact Or.inr (ind _ h r)
  have hds : ∀ d ∈ rds ++ odds, ∃ s ∈ domainKinds, d = .atom s := fun d md =>
    (List.mem_append.mp md).elim (hrds d) fun h => hdds d (sod d h)
  have datom : Term.atom "atom" ∈ rds ++ odds ↔ Term.atom "atom" ∈ rds ∨ Term.atom "atom" ∈ dds := by
    rw [List.mem_append]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (sod _ h)
    · rintro (h | h)
      · exact Or.inl h
      · by_cases r : Term.atom "atom" ∈ rds
        · exact Or.inl r
        · exact Or.inr (ind _ h r)
  -- Splits with the domains of the dynamic part.
  have single : ∀ rs neg, (∀ s, SplitKey rs neg (rds ++ odds) (.atom s) ↔
      amemV (mapLookup Yd (.atom "atom")) (.atom s) = Bool.true) →
      ∀ κ, (∃ sp ∈ [(rs, neg, rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
    intro rs neg h κ
    simp only [List.mem_singleton, exists_eq_left]
    cases κ with
    | atom s => exact (h s).trans (keyA s).symm
    | dom k i => exact dsK k i
  -- The shapes of the atoms.
  have shapeX : mapLookup X (.atom "atom") = none ∨ ∃ (pos : Bool) (S : List (Term × Term)), ASet S ∧
      mapLookup X (.atom "atom") = some (.tuple #[.atom (if pos then "union" else "negation"), .map S]) := by
    cases h : mapLookup X (.atom "atom") with
    | none => exact Or.inl rfl
    | some x =>
      obtain ⟨⟨pos, S, rfl, -⟩, -⟩ := fieldC_atom ((de_map dS).fields _ _ (lX.trans h))
      exact Or.inr ⟨pos, S, aS _ S h (by cases pos <;> simp), rfl⟩
  have shapeY : mapLookup Yd (.atom "atom") = none ∨ ∃ (pos : Bool) (S : List (Term × Term)), ASet S ∧
      mapLookup Yd (.atom "atom") = some (.tuple #[.atom (if pos then "union" else "negation"), .map S]) := by
    cases h : mapLookup Yd (.atom "atom") with
    | none => exact Or.inl rfl
    | some x =>
      obtain ⟨⟨pos, S, rfl, -⟩, -⟩ := fieldC_atom ((de_map dY).fields _ _ h)
      exact Or.inr ⟨pos, S, aY _ S h (by cases pos <;> simp), rfl⟩
  have noRat : mapLookup X (.atom "atom") = none ∨ (∃ S, mapLookup X (.atom "atom") =
      some (.tuple #[.atom "union", .map S])) → Term.atom "atom" ∉ rds := by
    rintro (h | ⟨S, h⟩) m
    · obtain ⟨S', h'⟩ := hrat.mp m; rw [lX, h] at h'; simp at h'
    · obtain ⟨S', h'⟩ := hrat.mp m; rw [lX, h] at h'; simp at h'
  have noDat : mapLookup Yd (.atom "atom") = none ∨ (∃ S, mapLookup Yd (.atom "atom") =
      some (.tuple #[.atom "union", .map S])) → Term.atom "atom" ∉ dds := by
    rintro (h | ⟨S, h⟩) m
    · obtain ⟨S', h'⟩ := hdat.mp m; rw [h] at h'; simp at h'
    · obtain ⟨S', h'⟩ := hdat.mp m; rw [h] at h'; simp at h'
  have aDs : ∀ d ∈ rds ++ odds, d = .atom "atom" → mapLookup X (.atom "atom") = none ∨
      (∃ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S])) →
      mapLookup Yd (.atom "atom") = none ∨ (∃ S, mapLookup Yd (.atom "atom") =
        some (.tuple #[.atom "union", .map S])) → False := by
    rintro d md rfl hx hy
    rcases datom.mp md with h | h
    · exact noRat hx h
    · exact noDat hy h
  -- Splits without a negated set, or with one, and their domains.
  have okNil : ∀ rs : List Term, (∀ r ∈ rs, ∃ s, r = .atom s) → Term.atom "atom" ∉ rds ++ odds →
      ∀ sp ∈ [(rs, Term.atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
    intro rs hrs na sp msp
    simp only [List.mem_singleton] at msp
    subst msp
    exact ⟨⟨hrs, Or.inl rfl, hds, ⟨fun h => absurd h na, fun ⟨N, e⟩ => nomatch e⟩⟩, fun N e => nomatch e⟩
  have okNeg : ∀ N, Term.atom "atom" ∈ rds ++ odds →
      ∀ sp ∈ [([], Term.map N, rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
    intro N ha sp msp
    simp only [List.mem_singleton] at msp
    subst msp
    exact ⟨⟨by simp, Or.inr ⟨N, rfl⟩, hds, ⟨fun _ => ⟨N, rfl⟩, fun _ => ha⟩⟩, fun _ _ => rfl⟩
  have atomsOf : ∀ A : List String, ∀ r ∈ A.map Term.atom, ∃ s, r = .atom s := fun A r mr => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp mr; exact ⟨s, rfl⟩
  have memA : ∀ (A : List String) (s : String), Term.atom s ∈ A.map Term.atom ↔ s ∈ A := fun A s => by simp
  rcases shapeX with hx | ⟨px, S, aSS, hx⟩ <;> rcases shapeY with hy | ⟨py, Dn, aDD, hy⟩
  · -- No atoms.
    have na : Term.atom "atom" ∉ rds ++ odds := fun m => (datom.mp m).elim (noRat (Or.inl hx)) (noDat (Or.inl hy))
    refine ⟨.tuple #[.nil, .nil, .atom "nil", Term.list rds, Term.list odds], .atom "nil", [([] ++ [], .atom "nil", rds ++ odds)], ?_, ?_, ?_, ?_, ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
      rcases unf with ⟨rfl, ut⟩ | rfl
      · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod]
      · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod]
    · exact fun N e => nomatch e
    · exact dnfPuts_nil (rs := []) (os := []) (okNil _ (by simp) na _ List.mem_cons_self).1
    · exact okNil _ (by simp) na
    · refine single _ _ fun s => ?_
      simp [SplitKey, hy, amemV]
  · cases py <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy
    · -- Atoms outside a dynamic negated set.
      have ha : Term.atom "atom" ∈ rds ++ odds := datom.mpr (Or.inr (hdat.mpr ⟨Dn, hy⟩))
      refine ⟨.tuple #[.nil, .nil, .map Dn, Term.list rds, Term.list odds], .map Dn, [([], .map Dn, rds ++ odds)], ?_, ?_, ?_, ?_, ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod]
      · exact fun N e => by cases e; exact aset_hNa aDD
      · exact dnfPuts_neg (okNeg Dn ha _ List.mem_cons_self).1
      · exact okNeg Dn ha
      · refine single _ _ fun s => ?_
        simp [SplitKey, hy, amemV]
    · -- Dynamic atoms, optional.
      obtain ⟨Dl, rDl, mDl⟩ := aset_list aDD (D (m + 1))
      have na : Term.atom "atom" ∉ rds ++ odds := fun m =>
        (datom.mp m).elim (noRat (Or.inl hx)) (noDat (Or.inr ⟨Dn, hy⟩))
      refine ⟨.tuple #[.nil, Term.list (Dl.map Term.atom), .atom "nil", Term.list rds, Term.list odds], .atom "nil", [([] ++ Dl.map Term.atom, .atom "nil", rds ++ odds)], ?_, ?_, ?_, ?_, ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rDl]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rDl]
      · exact fun N e => nomatch e
      · exact dnfPuts_nil (rs := []) (okNil _ (by simp) na _ List.mem_cons_self).1
      · exact okNil _ (by simp) na
      · refine single _ _ fun s => ?_
        simp [SplitKey, hy, amemV, mDl]
  · cases px <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx
    · -- A static negated set without dynamic atoms: impossible, as some atom outside it would be dynamic.
      obtain ⟨c, hc⟩ := fresh_str (keyStrs S)
      have := inclA c (by simp [hx, amemV, lookup_fresh' hc])
      simp [hy, amemV] at this
    · -- Static atoms without dynamic atoms: none, as they would be dynamic.
      obtain ⟨Sl, rSl, mSl⟩ := aset_list aSS (D (m + 1))
      have na : Term.atom "atom" ∉ rds ++ odds := fun m =>
        (datom.mp m).elim (noRat (Or.inr ⟨S, hx⟩)) (noDat (Or.inl hy))
      refine ⟨.tuple #[Term.list (Sl.map Term.atom), .nil, .atom "nil", Term.list rds, Term.list odds], .atom "nil", [(Sl.map Term.atom ++ [], .atom "nil", rds ++ odds)], ?_, ?_, ?_, ?_, ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rSl]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rSl]
      · exact fun N e => nomatch e
      · exact dnfPuts_nil (os := []) (okNil _ (by simp) na _ List.mem_cons_self).1
      · exact okNil _ (by simp) na
      · refine single _ _ fun s => ?_
        simp only [SplitKey, List.append_nil, memA, mSl, hy, amemV]
        constructor
        · rintro (h | ⟨N, e, -⟩)
          · have := inclA s (by simpa [hx, amemV] using h)
            simp [hy, amemV] at this
          · cases e
        · intro h; cases h
  · cases px <;> cases py <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx hy
    · -- Both negated: the atoms outside both sets.
      obtain ⟨R, rR, aR, mR⟩ := aset_inter aDD aSS
      have ha : Term.atom "atom" ∈ rds ++ odds := datom.mpr (Or.inr (hdat.mpr ⟨Dn, hy⟩))
      refine ⟨.tuple #[.nil, .nil, .map R, Term.list rds, Term.list odds], .map R, [([], .map R, rds ++ odds)], ?_, ?_, ?_, ?_, ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rR]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rR]
      · exact fun N e => by cases e; exact aset_hNa aR
      · exact dnfPuts_neg (okNeg R ha _ List.mem_cons_self).1
      · exact okNeg R ha
      · refine single _ _ fun s => ?_
        have i := inclA s
        simp only [hx, hy, amemV, Bool.not_eq_true'] at i
        simp only [SplitKey, List.not_mem_nil, false_or, hy, amemV, Bool.not_eq_true']
        constructor
        · rintro ⟨N, e, h⟩
          cases e
          have := mR (.atom s)
          rw [h] at this
          cases hd : (mapLookup Dn (.atom s)).isSome
          · rfl
          · cases hs : (mapLookup S (.atom s)).isSome
            · have := i (by simpa using hs); simp [hd] at this
            · simp [hd, hs] at this
        · intro h
          refine ⟨R, rfl, ?_⟩
          have := mR (.atom s)
          cases hR : mapLookup R (.atom s)
          · rfl
          · rw [hR] at this; simp [h] at this
    · -- A static negated set with dynamic atoms: impossible, as some atom outside both would be dynamic.
      obtain ⟨c, hc⟩ := fresh_str (keyStrs S ++ keyStrs Dn)
      have := inclA c (by simp [hx, amemV, lookup_fresh' (fun m => hc (List.mem_append_left _ m))])
      simp [hy, amemV, lookup_fresh' (fun m => hc (List.mem_append_right _ m))] at this
    · -- Static atoms and a dynamic negated set: the static atoms, and the atoms outside both.
      obtain ⟨Sl, rSl, mSl⟩ := aset_list aSS (D (m + 1))
      obtain ⟨R, rR, aR, mR⟩ := aset_union aDD aSS
      have ha : Term.atom "atom" ∈ rds ++ odds := datom.mpr (Or.inr (hdat.mpr ⟨Dn, hy⟩))
      have hA : ∀ a ∈ Sl, mapLookup R (.atom a) ≠ none := fun a ma => by
        have := mR (.atom a)
        rw [(mSl a).mp ma, Bool.or_true] at this
        exact Option.isSome_iff_ne_none.mp this
      refine ⟨.tuple #[Term.list (Sl.map Term.atom), .nil, .map R, Term.list rds, Term.list odds], .map R, [(Sl.map Term.atom, .atom "nil", []), ([], .map R, rds ++ odds)], ?_, ?_, ?_, ?_, ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rSl, rR]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rSl, rR]
      · exact fun N e => by cases e; exact aset_hNa aR
      · exact dnfPuts_req' (aset_hNa aR) hds ha hA
      · intro sp msp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at msp
        rcases msp with rfl | rfl
        · exact ⟨⟨atomsOf Sl, Or.inl rfl, by simp, ⟨by simp, fun ⟨N, e⟩ => nomatch e⟩⟩, fun N e => nomatch e⟩
        · exact (okNeg R ha _ List.mem_cons_self)
      · intro κ
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
        cases κ with
        | atom s =>
          rw [keyA]
          have i := inclA s
          simp only [hx, hy, amemV, Bool.not_eq_true'] at i
          simp only [SplitKey, memA, mSl, List.not_mem_nil, false_or, hy, amemV, Bool.not_eq_true']
          constructor
          · rintro ((h | ⟨N, e, -⟩) | ⟨N, e, h⟩)
            · exact i h
            · cases e
            · cases e
              have := mR (.atom s)
              rw [h] at this
              cases hd : (mapLookup Dn (.atom s)).isSome
              · rfl
              · simp [hd] at this
          · intro h
            by_cases hs : (mapLookup S (.atom s)).isSome = Bool.true
            · exact Or.inl (Or.inl hs)
            · refine Or.inr ⟨R, rfl, ?_⟩
              have := mR (.atom s)
              simp only [h, Bool.false_or] at this
              simp only [Bool.not_eq_true] at hs
              rw [hs] at this
              cases hR : mapLookup R (.atom s)
              · rfl
              · rw [hR] at this; cases this
        | dom k i =>
          simp only [SplitKey, List.not_mem_nil, false_or]
          exact dsK k i
    · -- Static and dynamic atoms: the static ones, and the dynamic ones they miss.
      obtain ⟨Sl, rSl, mSl⟩ := aset_list aSS (D (m + 1))
      obtain ⟨R, rR, aR, mR⟩ := aset_sub aDD aSS
      obtain ⟨Rl, rRl, mRl⟩ := aset_list aR (D (m + 1))
      have na : Term.atom "atom" ∉ rds ++ odds := fun m =>
        (datom.mp m).elim (noRat (Or.inr ⟨S, hx⟩)) (noDat (Or.inr ⟨Dn, hy⟩))
      have hrs : ∀ r ∈ Sl.map Term.atom ++ Rl.map Term.atom, ∃ s, r = .atom s := fun r mr =>
        (List.mem_append.mp mr).elim (atomsOf Sl r) (atomsOf Rl r)
      refine ⟨.tuple #[Term.list (Sl.map Term.atom), Term.list (Rl.map Term.atom), .atom "nil", Term.list rds, Term.list odds], .atom "nil", [(Sl.map Term.atom ++ Rl.map Term.atom, .atom "nil", rds ++ odds)], ?_, ?_, ?_, ?_, ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rSl, rR, rRl]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rSl, rR, rRl]
      · exact fun N e => nomatch e
      · exact dnfPuts_nil (okNil _ hrs na _ List.mem_cons_self).1
      · exact okNil _ hrs na
      · refine single _ _ fun s => ?_
        have i := inclA s
        simp only [hx, hy, amemV] at i
        simp only [SplitKey, List.mem_append, memA, mSl, mRl, mR, hy, amemV]
        constructor
        · rintro ((h | h) | ⟨N, e, -⟩)
          · exact i h
          · exact (Bool.and_eq_true_iff.mp h).1
          · cases e
        · intro h
          by_cases hs : (mapLookup S (.atom s)).isSome = Bool.true
          · exact Or.inl (Or.inl hs)
          · exact Or.inl (Or.inr (by simp [h, hs]))
end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem put_static_value_g {m : Nat} {X : List (Term × Term)} {key v s : Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v = (do
      let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) s (forceOp v) (.atom "false")
      putRes r) := by
  unfold Elixir.Module.Types.Descr.«map_put/3» Elixir.Module.Types.Descr.«map_put_shared/3»
  rcases sv with rfl | ⟨Z, rfl, sZ⟩
  · simp [hk, putRes]
    rfl
  · simp [hk, getMapKeys_single, sZ, putRes]
    rfl

theorem put_gradual_value_g {m : Nat} {X : List (Term × Term)} {key s : Term} {Zv : List (Term × Term)} {Dv : Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s)
    (hZ : mapLookup Zv (.atom "dynamic") = some Dv)
    (hmo : Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) = .ok (.atom "true")) :
    Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key (.map Zv) = (do
      let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map (dynG X)) s (forceOp Dv) (.atom "false")
      putRes r) := by
  have hmo' : Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (X.filter fun entry =>
      !decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic") entry.fst = .eq))) =
      .ok (.atom "true") := hmo
  unfold Elixir.Module.Types.Descr.«map_put/3» Elixir.Module.Types.Descr.«map_put_shared/3»
  rw [Elixir.Module.Types.Descr.«map_gradual/1».eq_def]
  cases hX : mapLookup X (.atom "dynamic") <;>
    simp [hk, getMapKeys_single, hZ, hX, dynG, putRes, Erlang.maps.«remove/2», hmo'] <;> rfl

section
variable {t : Term} {n : Nat}

/-- A gradual value puts into a map type whose static part holds only maps, and otherwise gives `:badmap`. -/
theorem put_gradual_cases {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) {key s : Term} {Zv : List (Term × Term)} {Dv : Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s)
    (hZ : mapLookup Zv (.atom "dynamic") = some Dv) :
    (Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) = .ok (.atom "true") ∧
      ∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∨
    (Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key (.map Zv) = .ok (.atom "badmap") ∧
      ¬∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") := by
  obtain ⟨dR, sR⟩ := rest_map (t := t) (n := n) gX.low_tc
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) =
      .ok (boolAtom (bp (∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
    exact next_empty dR hm
  have iff : (∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q) ↔ ∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map" :=
    ⟨fun h q hq => Classical.byContradiction fun nq => h q ((sR q).mpr ⟨hq, nq⟩),
      fun h q hq => ((sR q).mp hq).2 (h q ((sR q).mp hq).1)⟩
  by_cases h : ∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q
  · rw [bp_true.mpr h] at mo
    exact Or.inl ⟨by simpa [boolAtom] using mo, iff.mp h⟩
  · rw [bp_false.mpr h] at mo
    exact Or.inr ⟨put_gradual_value_bad hk hZ (by simpa [boolAtom] using mo), fun h' => h (iff.mpr h')⟩

/-- `map_only?/1` of the static part of a gradual map type is a boolean. -/
theorem map_only_bool {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) = .ok (.atom "true") ∨
      Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) = .ok (.atom "false") := by
  obtain ⟨dR, -⟩ := rest_map (t := t) (n := n) gX.low_tc
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) =
      .ok (boolAtom (bp (∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
    exact next_empty dR hm
  rw [mo]
  cases bp (∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q) <;> simp [boolAtom]

/-- `map_put/3` of a static value, on a static map type, at a split updating with `P`. -/
theorem dput_g {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hP : DnfPuts s neg P)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none)
    (hm : (level t n).K + 26 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, res = .tuple #[.atom "ok", .map Y] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ P (level t n).den (MT t n X) v w) := by
  have sv' : v = .atom "term" ∨ ∃ Z, v = .map Z := sv.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
  rw [put_static_value_g hk sv]
  obtain ⟨res, run, ⟨rfl, h⟩ | ⟨Y, hr, h⟩⟩ := dput_map_g hX hv sv' hP hNa hm
  · exact ⟨_, by rw [run]; rfl, Or.inl ⟨rfl, h⟩⟩
  · rcases hr with rfl | ⟨⟨er, rfl⟩, rfl⟩
    · exact ⟨_, by rw [run]; rfl, Or.inr ⟨Y, rfl, h⟩⟩
    · exact ⟨_, by rw [run]; rfl, Or.inr ⟨[], rfl, h⟩⟩

/-- `map_split_keys_and_domains/1` on a gradual key type of the laws: splits whose puts give the puts of the split,
and whose keys are those of the split of its upper bound. -/
theorem key_gsplit {k : Term} {m : Nat} (hm : (level t n).K + 23 ≤ m)
    (h : «arrows_gradual?/2» (D (m + 1)) k (.tuple #[.integer n, t]) = .ok (.atom "true")) :
    ∃ s neg Ss, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) k = .ok s ∧
      (∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ DnfPuts s neg (PutAny Ss) ∧
      (∀ sp ∈ Ss, SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = []) ∧
      ∃ rs neg' ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (upper k) =
          .ok (splitT rs neg' ds) ∧ SplitOk rs neg' ds ∧ (∀ N, neg' = .map N → rs = []) ∧
        (∀ N, neg' = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧
        (∀ κ, (∃ sp ∈ Ss, SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ SplitKey rs neg' ds κ) ∧
        ∀ κ, SplitKey rs neg' ds κ ↔ KeyPt t n (upper k) κ := by
  have static : «arrows_static?/2» k (.tuple #[.integer n, t]) = .ok (.atom "true") → ∃ s neg Ss,
      Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) k = .ok s ∧
      (∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ DnfPuts s neg (PutAny Ss) ∧
      (∀ sp ∈ Ss, SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = []) ∧
      ∃ rs neg' ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (upper k) =
          .ok (splitT rs neg' ds) ∧ SplitOk rs neg' ds ∧ (∀ N, neg' = .map N → rs = []) ∧
        (∀ N, neg' = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧
        (∀ κ, (∃ sp ∈ Ss, SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ SplitKey rs neg' ds κ) ∧
        ∀ κ, SplitKey rs neg' ds κ ↔ KeyPt t n (upper k) κ := by
    intro hs
    have dk := arrows_static_ok hs
    obtain ⟨rs, neg, ds, rk, ok, nr, na, skk⟩ :=
      key_split_any dk (fun Y e => by subst e; exact static_union_atoms hs)
        (fun Y e => by subst e; exact static_negation_atoms hs) hm
    have hP : DnfPuts (splitT rs neg ds) neg (fun den M v w => PutSem den M rs neg ds v w) := dnfPuts_split ok nr
    refine ⟨splitT rs neg ds, neg, [(rs, neg, ds)], rk, na, ?_, ?_, rs, neg, ds, by rw [upper_tc dk]; exact rk, ok,
      nr, na, fun κ => by simp, fun κ => by rw [upper_tc dk]; exact skk κ⟩
    · refine dnfPuts_iff hP ?_
      intro V den M v w
      exact (putAny_single (sp := (rs, neg, ds)) den M v w).symm
    · intro sp msp
      simp only [List.mem_singleton] at msp
      subst msp
      exact ⟨ok, nr⟩
  have gk := arrows_gradual_gc (t := t) (n := n) (m := m + 1) (by omega) k (by simpa [Term.true] using h)
  unfold «arrows_gradual?/2» at h
  cases k with
  | map X =>
    cases hD : mapLookup X (.atom "dynamic") with
    | none => simp [getMapKeys_single, hD] at h; exact static h
    | some Dy =>
      simp only [getMapKeys_single, hD, Option.toList, Erlang.maps.«remove/2», Lynx.Except.ok_bind,
        Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨hS, hDy⟩, -⟩ := h
      rw [← rmDyn] at hS
      have lX : mapLookup (rmDyn X) (.atom "atom") = mapLookup X (.atom "atom") := lookup_rmDyn_name X (by decide)
      obtain ⟨s, neg, Ss, rk, na, hP, ok, sk⟩ := gsplit gk hD
        (fun tag S e ht => static_atom_set hS tag S (lX.trans e) ht)
        (fun Y e tag S e' ht => by subst e; exact static_atom_set hDy tag S e' ht) hm
      have dDy := arrows_static_ok hDy
      obtain ⟨rs, neg', ds, rk', ok', nr', na', sk'⟩ :=
        key_split_any dDy (fun Y e => by subst e; exact static_union_atoms hDy)
          (fun Y e => by subst e; exact static_negation_atoms hDy) hm
      exact ⟨s, neg, Ss, rk, na, hP, ok, rs, neg', ds, by rw [upper_dyn hD]; exact rk', ok', nr', na',
        fun κ => (sk κ).trans (sk' κ).symm, fun κ => by rw [upper_dyn hD]; exact sk' κ⟩
  | _ => simp at h; exact static h

end

end Elixir.STTDescrProofsTest.Nest
