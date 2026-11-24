namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Forced updates do not read whether the type is static, so the dynamic part of a gradual type is put like a
static one. -/

theorem foldl1_congr (d : Dispatcher) (f g : Term) (h : ∀ x a, d.pure f #[x, a] = d.pure g #[x, a]) :
    ∀ (l acc : Term), Erlang.lists.«foldl_1/3» d f acc l = Erlang.lists.«foldl_1/3» d g acc l
  | .cons x l, acc => by
    rw [Erlang.lists.«foldl_1/3».eq_def, Erlang.lists.«foldl_1/3».eq_def]
    simp only [h]
    cases d.pure g #[x, acc] with
    | error e => rfl
    | ok a => simpa using foldl1_congr d f g h l a
  | .nil, acc => by rw [Erlang.lists.«foldl_1/3».eq_def, Erlang.lists.«foldl_1/3».eq_def]
  | .atom _, _ | .integer _, _ | .float _, _ | .tuple _, _ | .map _, _ | .bitstring _ _ _, _
  | .function _ _ _ _, _ | .pid _, _ | .reference _, _ => by
    rw [Erlang.lists.«foldl_1/3».eq_def, Erlang.lists.«foldl_1/3».eq_def]

theorem foldl_congr (d : Dispatcher) {mo nm : String} {c₁ c₂ : Array Term}
    (h : ∀ x a, d.pure (.function mo nm 2 c₁) #[x, a] = d.pure (.function mo nm 2 c₂) #[x, a]) (l acc : Term) :
    Erlang.lists.«foldl/3» d (.function mo nm 2 c₁) acc l = Erlang.lists.«foldl/3» d (.function mo nm 2 c₂) acc l := by
  simp only [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  cases l with
  | cons x l =>
    simp only [h]
    cases d.pure (.function mo nm 2 c₂) #[x, acc] with
    | error e => simp [Lynx.Except.guard]
    | ok a => simpa [Lynx.Except.guard] using foldl1_congr d _ _ h l a
  | _ => simp [Lynx.Except.guard]

/-- The step of `map_update_named_keys/8` does not read whether the type is static when forcing. -/
theorem named_step_static (d : Dispatcher) (dnf op req build ov key acc : Term) :
    Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req (.atom "false") build ov (.atom "true")
        key acc =
      Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req (.atom "true") build ov (.atom "true")
        key acc := by
  simp [Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»]

/-- `map_update_named_keys/8` forcing gives the same result whether the type is static or not. -/
theorem named_keys_static (m : Nat) (acc dnf keys v req rt build : Term) :
    Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf keys (forceOp v) req (.atom "false") rt build =
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf keys (forceOp v) req (.atom "true") rt
        build := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», forceOp, Erlang.erlang.«element/2»,
    Erlang.erlang.«==/2»]
  simp
  congr 1
  funext ov
  refine foldl_congr _ (fun x a => ?_) keys acc
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
    Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure, named_step_static]

/-- `map_update_static_dnf/6` forcing gives the same result whether the type is static or not. -/
theorem dnf_static (m : Nat) (bdd dnf split v rt : Term) :
    Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split (forceOp v) rt (.atom "false") =
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split (forceOp v) rt (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp only [named_keys_static]

theorem update_static_flag_ne (m : Nat) (descr split v rt : Term) (h : descr ≠ .atom "term") :
    Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split (forceOp v) rt (.atom "false") =
      Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split (forceOp v) rt (.atom "true") := by
  rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def, Elixir.Module.Types.Descr.«map_update_static/5».eq_def]
  cases descr with
  | map X =>
    simp only
    cases getMapKeys [.atom "map"] (.map X) with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | cons c rest => rfl
      | nil =>
        simp only
        split <;> rename_i heq <;> simp only [dnf_static] <;> (try rfl) <;> simp_all
  | atom a =>
    by_cases ha : a = "term"
    · subst ha; exact absurd rfl h
    · simp [ha, Lynx.Term.getMapKeys]
  | _ => rfl

/-- `map_update_static/5` forcing gives the same result whether the type is static or not. -/
theorem update_static_flag (m : Nat) (descr split v rt : Term) :
    Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split (forceOp v) rt (.atom "false") =
      Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split (forceOp v) rt (.atom "true") := by
  by_cases h : descr = .atom "term"
  · subst h
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def, Elixir.Module.Types.Descr.«map_update_static/5».eq_def]
    simp only
    exact update_static_flag_ne m _ split v rt (by simp)
  · exact update_static_flag_ne m descr split v rt h

end Elixir.STTDescrProofsTest.Nest
