namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Updates of gradual types: the dynamic part is updated with errors computed as for gradual types, which change
neither the values nor the maps of the update. -/

/-- Accumulators of updates that agree on their value and maps. -/
def Rel4 (a b : Term) : Prop := ∃ v bd e₁ f₁ e₂ f₂, a = .tuple #[v, bd, e₁, f₁] ∧ b = .tuple #[v, bd, e₂, f₂]

/-- One step of `map_update_named_keys/8` gives the same value and maps whether the type is static or not. -/
theorem named_step_rel (d : Dispatcher) (dnf op req bld ov fo key : Term) (s₁ s₂ : Term)
    {v bd e₁ f₁ e₂ f₂ r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req s₁ bld ov fo key
      (.tuple #[v, bd, e₁, f₁]) = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req s₂ bld ov fo key
      (.tuple #[v, bd, e₂, f₂]) = .ok r₂) : Rel4 r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»] at h₁ h₂
  cases hk : Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov with
  | error e => simp [hk] at h₁
  | ok t =>
    simp only [hk, Lynx.Except.ok_bind] at h₁ h₂
    split at h₁
    case h_2 => simp at h₁
    rename_i bds old
    simp only at h₂
    cases hb : Erlang.erlang.«++/2» bds bd with
    | error e => simp [hb] at h₁
    | ok B =>
      simp only [hb, Lynx.Except.ok_bind] at h₁ h₂
      by_cases hn : old = .atom "nil"
      · subst hn
        simp only [pure, Except.pure, Except.ok.injEq] at h₁ h₂
        subst h₁ h₂
        exact ⟨_, _, _, _, _, _, rfl, rfl⟩
      by_cases ht : ∃ value opt, old = .tuple #[value, opt]
      · obtain ⟨value, opt, rfl⟩ := ht
        simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure] at h₁ h₂
        split at h₁
        · simp at h₁
        rename_i b16 h16
        simp only [h16] at h₂
        simp only [Lynx.Except.tryWith] at h₁ h₂
        split at h₁
        · -- The old value has values: the value is updated.
          rename_i hm
          simp only [hm] at h₂
          cases hu : Elixir.Module.Types.Descr.«opt_union/2» d value v with
          | error e => simp [hu] at h₁
          | ok U =>
            simp only [hu] at h₁ h₂
            obtain ⟨e₁', f₁', rfl⟩ : ∃ e f, r₁ = .tuple #[U, B, e, f] := by
              clear h₂
              repeat' split at h₁
              all_goals first
                | (simp at h₁; done)
                | (simp only [Except.ok.injEq] at h₁; subst h₁; exact ⟨_, _, rfl⟩)
            obtain ⟨e₂', f₂', rfl⟩ : ∃ e f, r₂ = .tuple #[U, B, e, f] := by
              clear h₁
              repeat' split at h₂
              all_goals first
                | (simp at h₂; done)
                | (simp only [Except.ok.injEq] at h₂; subst h₂; exact ⟨_, _, rfl⟩)
            exact ⟨_, _, _, _, _, _, rfl, rfl⟩
        · rename_i hx
          cases hm : b16.isMember [Term.atom "false", Term.atom "nil"] with
          | atom a =>
            by_cases ha : a = "true"
            · subst ha; exact (hx hm).elim
            · simp only [hm] at h₂
              obtain ⟨e₁', f₁', rfl⟩ : ∃ e f, r₁ = .tuple #[v, B, e, f] := by
                clear h₂
                repeat' split at h₁
                all_goals first
                  | (simp at h₁; done)
                  | (simp only [Except.ok.injEq] at h₁; subst h₁; exact ⟨_, _, rfl⟩)
              obtain ⟨e₂', f₂', rfl⟩ : ∃ e f, r₂ = .tuple #[v, B, e, f] := by
                clear h₁
                split at h₂
                · simp_all
                repeat' split at h₂
                all_goals first
                  | (simp at h₂; done)
                  | (simp only [Except.ok.injEq] at h₂; subst h₂; exact ⟨_, _, rfl⟩)
              exact ⟨_, _, _, _, _, _, rfl, rfl⟩
          | _ =>
            simp only [hm] at h₂
            obtain ⟨e₁', f₁', rfl⟩ : ∃ e f, r₁ = .tuple #[v, B, e, f] := by
              clear h₂
              repeat' split at h₁
              all_goals first
                | (simp at h₁; done)
                | (simp only [Except.ok.injEq] at h₁; subst h₁; exact ⟨_, _, rfl⟩)
            obtain ⟨e₂', f₂', rfl⟩ : ∃ e f, r₂ = .tuple #[v, B, e, f] := by
              clear h₁
              repeat' split at h₂
              all_goals first
                | (simp at h₂; done)
                | (simp only [Except.ok.injEq] at h₂; subst h₂; exact ⟨_, _, rfl⟩)
            exact ⟨_, _, _, _, _, _, rfl, rfl⟩
      · split at h₁
        · exact absurd rfl hn
        · exact absurd ⟨_, _, rfl⟩ ht
        · simp at h₁

theorem foldl1_rel4 (d : Dispatcher) (f₁ f₂ : Term)
    (hs : ∀ x a b a' b', Rel4 a b → d.pure f₁ #[x, a] = .ok a' → d.pure f₂ #[x, b] = .ok b' → Rel4 a' b') :
    ∀ (l a b : Term) {r₁ r₂ : Term}, Rel4 a b → Erlang.lists.«foldl_1/3» d f₁ a l = .ok r₁ →
      Erlang.lists.«foldl_1/3» d f₂ b l = .ok r₂ → Rel4 r₁ r₂
  | .cons x l, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only at h₁ h₂
    cases e₁ : d.pure f₁ #[x, a] with
    | error e => rw [e₁] at h₁; cases h₁
    | ok a' =>
      cases e₂ : d.pure f₂ #[x, b] with
      | error e => rw [e₂] at h₂; cases h₂
      | ok b' =>
        rw [e₁] at h₁; rw [e₂] at h₂
        exact foldl1_rel4 d f₁ f₂ hs l a' b' (hs x a b a' b' hab e₁ e₂) (by simpa using h₁) (by simpa using h₂)
  | .nil, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only [pure, Except.pure, Except.ok.injEq] at h₁ h₂
    subst h₁ h₂; exact hab
  | .atom _, _, _, _, _, _, h₁, _ | .integer _, _, _, _, _, _, h₁, _ | .float _, _, _, _, _, _, h₁, _
  | .tuple _, _, _, _, _, _, h₁, _ | .map _, _, _, _, _, _, h₁, _ | .bitstring _ _ _, _, _, _, _, _, h₁, _
  | .function _ _ _ _, _, _, _, _, _, h₁, _ | .pid _, _, _, _, _, _, h₁, _ | .reference _, _, _, _, _, _, h₁, _ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁; simp at h₁

theorem foldl_rel4 (d : Dispatcher) {mo nm : String} {c₁ c₂ : Array Term}
    (hs : ∀ x a b a' b', Rel4 a b → d.pure (.function mo nm 2 c₁) #[x, a] = .ok a' →
      d.pure (.function mo nm 2 c₂) #[x, b] = .ok b' → Rel4 a' b')
    (l a b : Term) {r₁ r₂ : Term} (hab : Rel4 a b)
    (h₁ : Erlang.lists.«foldl/3» d (.function mo nm 2 c₁) a l = .ok r₁)
    (h₂ : Erlang.lists.«foldl/3» d (.function mo nm 2 c₂) b l = .ok r₂) : Rel4 r₁ r₂ := by
  have conv : ∀ c acc r, Erlang.lists.«foldl/3» d (.function mo nm 2 c) acc l = .ok r →
      Erlang.lists.«foldl_1/3» d (.function mo nm 2 c) acc l = .ok r := by
    intro c acc r h
    simp only [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»] at h
    rw [Erlang.lists.«foldl_1/3».eq_def]
    cases l <;> simp_all [Lynx.Except.guard]
  replace h₁ := conv _ _ _ h₁
  replace h₂ := conv _ _ _ h₂
  exact foldl1_rel4 d _ _ hs l a b hab h₁ h₂

theorem named_keys_rel (m : Nat) (dnf keys op req rt bo s₁ s₂ : Term) {a b r₁ r₂ : Term} (hab : Rel4 a b)
    (h₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) a dnf keys op req s₁ rt bo = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) b dnf keys op req s₂ rt bo = .ok r₂) :
    Rel4 r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», bind, Except.bind, pure, Except.pure] at h₁ h₂
  repeat' (split at h₁ <;> (try (simp at h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    refine foldl_rel4 _ (fun x a b a' b' hab e₁ e₂ => ?_) keys a b hab h₁ h₂
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure] at e₁ e₂
    obtain ⟨v, bd, e₁', f₁', e₂', f₂', rfl, rfl⟩ := hab
    exact named_step_rel _ _ _ _ _ _ _ _ _ _ e₁ e₂

/-- `map_update_static_dnf/6` gives the same value and maps whether the type is static or not. -/
theorem dnf_rel (m : Nat) (bdd dnf split op rt s₁ s₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split op rt s₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split op rt s₂ = .ok r₂) :
    Rel4 r₁ r₂ := by
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (simp at h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁
    · simp at h₁
    rename_i v₁ n₁
    split at h₂
    · simp at h₂
    rename_i v₂ n₂
    have r₀ := named_keys_rel _ _ _ _ _ _ _ _ _ ⟨_, _, _, _, _, _, rfl, rfl⟩ n₁ n₂
    split at h₁
    · simp at h₁
    rename_i w₁ n₁'
    split at h₂
    · simp at h₂
    rename_i w₂ n₂'
    obtain ⟨V, BD, e₁, f₁, e₂, f₂, rfl, rfl⟩ := named_keys_rel _ _ _ _ _ _ _ _ _ r₀ n₁' n₂'
    simp only at h₁ h₂
    split at h₁
    · simp at h₁
    rename_i u hu
    simp only [hu] at h₂
    by_cases hbot : u = .atom "bdd_bot"
    · subst hbot
      simp only [Except.ok.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨_, _, _, _, _, _, rfl, rfl⟩
    · split at h₁
      · exact absurd rfl hbot
      split at h₂
      · exact absurd rfl hbot
      simp only [Except.ok.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨_, _, _, _, _, _, rfl, rfl⟩

theorem static_rel_ne (m : Nat) (descr split op rt s₁ s₂ : Term) (hd : descr ≠ .atom "term") {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₂ = .ok r₂) :
    r₁ = r₂ ∨ Rel4 r₁ r₂ := by
  rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.orElse, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (simp at h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals first
    | (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂; exact Or.inl rfl)
    | exact Or.inr (dnf_rel _ _ _ _ _ _ _ _ h₁ h₂)
    | exact absurd rfl hd
    | (split at h₁ <;> split at h₂ <;> simp_all)

/-- `map_update_static/5` gives the same value and maps whether the type is static or not. -/
theorem static_rel (m : Nat) (descr split op rt s₁ s₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₂ = .ok r₂) :
    r₁ = r₂ ∨ Rel4 r₁ r₂ := by
  by_cases h : descr = .atom "term"
  · subst h
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
    simp only at h₁ h₂
    exact static_rel_ne m _ split op rt s₁ s₂ (by simp) h₁ h₂
  · exact static_rel_ne m descr split op rt s₁ s₂ h h₁ h₂

/-- The gradual branch of `map_update_unchecked/4`: the update of the static part united with the dynamic update of the
dynamic part. -/
theorem grad_upd_inv {X : List (Term × Term)} {Dy : Term} (hD : mapLookup X (.atom "dynamic") = some Dy)
    {split op rt : Term} {m : Nat} {T R er : Term}
    (hdyn : ∀ r, Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) Dy split op rt (.atom "false") = .ok r →
      r = .atom "badmap" ∨ ∃ Td Yd ed fd, r = .tuple #[Td, .map Yd, ed, fd] ∧ mapLookup Yd (.atom "dynamic") = none)
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (m + 1)) (.map X) split op rt =
      .ok (.tuple #[T, R, er])) :
    ∃ Yd res sd, (∃ Td ed fd, Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) Dy split op rt (.atom "false") =
        .ok (.tuple #[Td, .map Yd, ed, fd])) ∧ mapLookup Yd (.atom "dynamic") = none ∧
      Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map (rmDyn X)) split op rt (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ sd = .map []) ∨ ∃ a e f, res = .tuple #[a, sd, e, f]) ∧
      Elixir.Module.Types.Descr.«opt_union/2» (D (m + 1)) sd (.map [(.atom "dynamic", .map Yd)]) = .ok R := by
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def] at run
  simp only [Erlang.maps.«take/2», hD] at run
  simp only [filter_dyn, bind, Except.bind, pure, Except.pure] at run
  have fun1 : ∀ x, (D (m + 1)).pure (.function "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-1-" 1 #[]) #[x] ≠
      .ok (.tuple #[T, R, er]) := fun x => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-1-/1».pure]
    unfold Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»
    split <;> simp
  split at run
  · simp at run
  split at run
  rotate_left
  · exact absurd run (fun1 _)
  cases hd₀ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) Dy split op rt (.atom "false") with
  | error e => rw [hd₀] at run; simp at run
  | ok r =>
    rw [hd₀] at run
    rcases hdyn r hd₀ with rfl | ⟨Td, Yd, ed, fd, rfl, sYd⟩
    · exact absurd run (fun1 _)
    generalize fd.isMember [Term.atom "false", Term.atom "nil"] = fm at run
    simp only at run
    cases hs₀ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map (rmDyn X)) split op rt (.atom "true") with
    | error e => rw [hs₀] at run; simp at run
    | ok res =>
      rw [hs₀] at run
      have gk : getMapKeys [Term.atom "dynamic"] (.map Yd) = [] := by simp [getMapKeys_single, sYd]
      obtain ⟨sd, hsd⟩ : ∃ sd, (res = .atom "badmap" ∧ sd = .map []) ∨ ∃ a e f, res = .tuple #[a, sd, e, f] := by
        by_cases hb : res = .atom "badmap"
        · exact ⟨_, Or.inl ⟨hb, rfl⟩⟩
        · by_cases h4 : ∃ a sd e f, res = .tuple #[a, sd, e, f]
          · obtain ⟨a, sd, e, f, rfl⟩ := h4
            exact ⟨sd, Or.inr ⟨a, e, f, rfl⟩⟩
          · exfalso
            simp only at run
            repeat' split at run
            all_goals simp_all
      refine ⟨Yd, res, sd, ⟨Td, ed, fd, rfl⟩, sYd, rfl, hsd, ?_⟩
      cases hR : Elixir.Module.Types.Descr.«opt_union/2» (D (m + 1)) sd (.map [(.atom "dynamic", .map Yd)]) with
      | error err =>
        exfalso
        rcases hsd with ⟨rfl, rfl⟩ | ⟨a, e, f, rfl⟩ <;> simp only [gk, hR] at run <;> (repeat' split at run) <;>
          first
          | (simp at run; done)
          | (simp_all; done)
          | (simp only [Lynx.Except.guard, Lynx.Except.tryWith] at run; split at run <;> simp_all)
      | ok R' =>
        rcases hsd with ⟨rfl, rfl⟩ | ⟨a, e, f, rfl⟩ <;> simp only [gk, hR] at run <;> (repeat' split at run) <;>
          first
          | (simp at run; done)
          | (simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at run
             exact congrArg Except.ok run.2.1.symm)
          | (simp only [Lynx.Except.guard, Lynx.Except.tryWith] at run; split at run <;> simp_all)

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The operations of `map_update/5` with a static value, or deleting. -/
def OpK (E : Term → Prop) (den : Term → V → Prop) (op : Term) : Prop :=
  (∃ v, E v ∧ (v = .atom "term" ∨ ∃ Z, v = .map Z) ∧
    (op = forceOp v ∨ ((∃ x, den v x) ∧ ∃ keep, op = keepOp v keep))) ∨
  ∃ md, Mode md ∧ op = cOp (.map []) Bool.true md

/-- Results of `map_update_static/5` with maps of a single field. -/
def UpdRes (E : Term → Prop) (r : Term) : Prop :=
  r = .atom "badmap" ∨ ∃ T Y e f, r = .tuple #[T, Y, e, f] ∧ (Y = .map [] ∨ ∃ r', Y = .map [(.atom "map", r')] ∧ MField E r')

/-- `map_update_static/5` on a map field, for either flag, gives no map or maps of one field. -/
theorem field_wf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b)
    {op : Term} (hop : OpK E den op) (st : Term) {r : Term}
    (h : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") st = .ok r) : UpdRes E r := by
  -- The update as a static type.
  obtain ⟨r', h', s'⟩ : ∃ r', Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") (.atom "true") = .ok r' ∧ UpdRes E r' := by
    rcases hop with ⟨v, hv, sv, rfl | ⟨vne, keep, rfl⟩⟩ | ⟨md, hmd, rfl⟩
    · obtain ⟨res, run, hres⟩ := dput_update_static ef hn hv sv ok (fun N e => by rw [nr N e]; rfl) hNa hb fb
      obtain ⟨res', run', ⟨rfl, bad⟩ | ⟨Y, f, rfl, T, er, run₂, -⟩⟩ := upd_old_static ef hn hv sv ok nr hNa hb fb
      · exact ⟨_, bad, Or.inl rfl⟩
      · rw [run] at run'; cases run'
        refine ⟨_, run₂, Or.inr ⟨T, Y, er, f, rfl, ?_⟩⟩
        rcases hres with ⟨e, -⟩ | ⟨Y', f', e, -, -, hY⟩
        · cases e
        · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e
          obtain ⟨-, rfl, -, rfl, -⟩ := e
          rcases hY with ⟨rfl, -⟩ | ⟨r', rfl, fr, -⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨r', rfl, fr⟩
    · obtain ⟨res, run, ⟨rfl, -⟩ | ⟨T, Y, er, f, rfl, -, Dm, -, hY⟩⟩ :=
        kr_update_static ef hn hv sv vne keep ok nr hNa hb fb
      · exact ⟨_, run, Or.inl rfl⟩
      · refine ⟨_, run, Or.inr ⟨T, Y, er, f, rfl, ?_⟩⟩
        rcases hY with ⟨rfl, -⟩ | ⟨r', rfl, fr, -⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r', rfl, fr⟩
    · obtain ⟨res, run, ⟨rfl, -⟩ | ⟨T, Y, er, f, rfl, -, Dm, -, hY⟩⟩ := del_update_static ef hn hmd ok nr hNa hb fb
      · exact ⟨_, run, Or.inl rfl⟩
      · refine ⟨_, run, Or.inr ⟨T, Y, er, f, rfl, ?_⟩⟩
        rcases hY with ⟨rfl, -⟩ | ⟨r', rfl, fr, -⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r', rfl, fr⟩
  rcases static_rel (n + 5) _ _ _ _ _ _ h h' with rfl | ⟨v, bd, e₁, f₁, e₂, f₂, rfl, rfl⟩
  · exact s'
  · rcases s' with e | ⟨T, Y, e, f, e', hY⟩
    · cases e
    · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e'
      obtain ⟨rfl, rfl, -⟩ := e'
      exact Or.inr ⟨_, _, _, _, rfl, hY⟩

end

section
variable {t : Term} {n : Nat}

/-- `map_update_static/5` on a static type of the next level, for either flag, gives no map or maps of one field. -/
theorem type_wf {Dy : Term} (hDy : DE (level t n).E Dy) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {op : Term} (hop : OpK (level t n).E (level t n).den op) {m : Nat} (hm : (level t n).K + 10 ≤ m) (st : Term)
    {r : Term} (h : Elixir.Module.Types.Descr.«map_update_static/5» (D m) Dy
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") st = .ok r) :
    UpdRes (level t n).E r := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have ef := (level t n).ef
  rcases hDy with rfl | ⟨DX, rfl, sX⟩
  · rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h
    have gk : getMapKeys [Term.atom "map"] (.atom "term") = [] := by simp [getMapKeys]
    simp only [gk] at h
    exact field_wf ef (n := k) (by omega) ok nr hNa (X := [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])])
      (by simp [mapLookup]) (Or.inl ⟨61102469, rfl⟩) hop st h
  · cases hb : mapLookup DX (.atom "map") with
    | some b => exact field_wf ef (n := k) (by omega) ok nr hNa hb (fieldC_map (sX.fields "map" b hb)) hop st h
    | none =>
      rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h
      simp [getMapKeys_single, hb] at h
      subst h
      exact Or.inr ⟨_, _, _, _, rfl, Or.inl rfl⟩

end

/-- The static branch of `map_update_unchecked/4`. -/
theorem static_upd_inv {S : List (Term × Term)} (hS : mapLookup S (.atom "dynamic") = none)
    {split op rt : Term} {m : Nat} {T Y er : Term}
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (m + 1)) (.map S) split op rt =
      .ok (.tuple #[T, Y, er])) :
    ∃ f, Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map S) split op rt (.atom "true") =
      .ok (.tuple #[T, Y, er, f]) := by
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def] at run
  simp only [Erlang.maps.«take/2», hS] at run
  simp only [bind, Except.bind, pure, Except.pure] at run
  have fun0 : ∀ x, (D (m + 1)).pure (.function "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[x] ≠
      .ok (.tuple #[T, Y, er]) := fun x => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure]
    unfold Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»
    split <;> simp
  split at run
  · simp at run
  split at run
  rotate_left
  · exact absurd run (fun0 _)
  cases hs : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map S) split op rt (.atom "true") with
  | error e => rw [hs] at run; simp at run
  | ok r =>
    rw [hs] at run
    simp only at run
    split at run
    · rename_i T' Y' er' f'
      simp only [Lynx.Except.guard, Lynx.Except.tryWith] at run
      split at run
      · simp at run
      · simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at run
        obtain ⟨rfl, rfl, rfl, -⟩ := run
        exact ⟨f', rfl⟩
    · exact absurd run (fun0 _)

section
variable {t : Term} {n : Nat}

theorem updRes_de {r : Term} (h : UpdRes (level t n).E r) (nb : r ≠ .atom "badmap") :
    ∃ T Y e f, r = .tuple #[T, .map Y, e, f] ∧ DE (level t n).E (.map Y) ∧ mapLookup Y (.atom "dynamic") = none := by
  rcases h with rfl | ⟨T, Y, e, f, rfl, rfl | ⟨r', rfl, fr⟩⟩
  · exact absurd rfl nb
  · exact ⟨T, [], e, f, rfl, Or.inr ⟨_, rfl, descrC_nil⟩, by simp [mapLookup]⟩
  · exact ⟨T, _, e, f, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, by simp [mapLookup]⟩

/-- Updating a gradual type with a static value at static keys gives, as lower bound, the update of its lower bound. -/
theorem lower_core {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {op : Term} (hop : OpK (level t n).E (level t n).den op) {m : Nat} (hm : (level t n).K + 30 ≤ m)
    {T R er T' Y er' : Term}
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") = .ok (.tuple #[T, R, er]))
    (runL : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map (rmDyn X))
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") = .ok (.tuple #[T', Y, er'])) :
    ∃ R₀, Elixir.Module.Types.Descr.«lower_bound/1» (D m) R = .ok R₀ ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) R₀ Y = .ok (.atom "true") := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have sS : mapLookup (rmDyn X) (.atom "dynamic") = none := by simp [lookup_rmDyn]
  have dS : DE (level t n).E (.map (rmDyn X)) := gX.low_tc
  -- The update of the lower bound.
  obtain ⟨fL, hL⟩ := static_upd_inv sS runL
  obtain ⟨T₀, YY, e₀, f₀, eL, dY, -⟩ := updRes_de (type_wf dS ok nr hNa hop (by omega) _ hL) (by simp)
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eL
  obtain ⟨-, rfl, -⟩ := eL
  have ef := ef_next t n
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    rw [rmDyn_static hD] at runL
    rw [runL] at run
    simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at run
    obtain ⟨-, rfl, -⟩ := run
    refine ⟨.map (rmDyn YY), lower_bound_run (Or.inr ⟨_, rfl⟩), ?_⟩
    have dY' : DE (level t n).E (.map (rmDyn YY)) := (GC.tc dY).low_tc
    exact elem_equal ef dY' dY (fun q => denD_rmDyn YY q) (by omega)
  | some Dy =>
    obtain ⟨dDy, -⟩ : DE (level t n).E Dy ∧ True := by
      rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, -, -⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
      · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, trivial⟩
    have hdyn : ∀ r, Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 1)) Dy
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") (.atom "false") = .ok r →
        r = .atom "badmap" ∨ ∃ Td Yd ed fd, r = .tuple #[Td, .map Yd, ed, fd] ∧ mapLookup Yd (.atom "dynamic") = none := by
      intro r h
      by_cases nb : r = .atom "badmap"
      · exact Or.inl nb
      obtain ⟨Td, Yd, ed, fd, rfl, -, sYd⟩ := updRes_de (type_wf dDy ok nr hNa hop (by omega) _ h) nb
      exact Or.inr ⟨Td, Yd, ed, fd, rfl, sYd⟩
    obtain ⟨Yd, res, sd, ⟨Td, ed, fd, hdy⟩, -, hres, hsd, hR⟩ := grad_upd_inv hD hdyn run
    rw [hL] at hres
    cases hres
    rcases hsd with ⟨e, -⟩ | ⟨a, e, f, e'⟩
    · cases e
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e'
    obtain ⟨-, rfl, -⟩ := e'
    obtain ⟨T₁, Yd', e₁, f₁, eD, dYd, -⟩ := updRes_de (type_wf dDy ok nr hNa hop (by omega) _ hdy) (by simp)
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eD
    obtain ⟨-, eYd, -⟩ := eD
    cases eYd
    -- The union of the static update and the dynamic one.
    have gA : GC (level t n) (.map [(.atom "dynamic", .map Yd)]) := by
      refine Or.inr ⟨_, .map Yd, rfl, by simp [mapLookup], dYd, ?_, fun v hv => ?_⟩
      · rw [show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]]; exact descrC_nil
      · rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]] at hv
        simp [denD_map, mapLookup, dn_none] at hv
    have noA : ∀ v : PN t n, ¬denD (.map [(.atom "dynamic", .map Yd)]) v := fun v hv => by
      rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]] at hv
      simp [denD_map, mapLookup, dn_none] at hv
    obtain ⟨c, gc, rc, sc, -⟩ := gc_opt_union (GC.tc dY) gA [] (m := k + 1) (by omega)
    rw [show Elixir.Module.Types.Descr.«opt_union/2» (D (k + 1)) (.map YY) (.map [(.atom "dynamic", .map Yd)]) =
      Elixir.Module.Types.Descr.«opt_union/3» (D (k + 1)) (.map YY) (.map [(.atom "dynamic", .map Yd)]) (.map []) from rfl,
      rc] at hR
    cases hR
    refine ⟨lower R, lower_bound_run gc.shape, ?_⟩
    exact elem_equal ef gc.low_tc dY (fun q => (denD_lower R q).trans ((sc q).trans (or_iff_left (noA q)))) (by omega)

end


/-- `map_update/5` with a static value updates with the value at the split of the keys. -/
theorem upd5_val {m : Nat} (X : Term) {key v mode s : Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s)
    (hmode : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject")
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«map_update/5» (D m) X key v mode (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) X s
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], mode]) (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rcases sv with rfl | ⟨Z, rfl, sZ⟩
  · rcases hmode with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2»,
      hk, Lynx.Term.getMapKeys]
  · rcases hmode with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2»,
      hk, getMapKeys_single, sZ]

/-- `map_update/5` deleting updates with no value at the split of the keys. -/
theorem upd5_del {m : Nat} (X : Term) {key s : Term} {md : String}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hmd : Mode md) :
    Elixir.Module.Types.Descr.«map_update/5» (D m) X key (.atom "delete") (.atom md) (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) X s (cOp (.map []) Bool.true md) (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rcases hmd with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk,
    Elixir.Module.Types.Descr.«none/0»] <;> rfl

end Elixir.STTDescrProofsTest.Nest
