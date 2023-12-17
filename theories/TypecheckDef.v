(* CRUCIAL NOTE: Typing is not unique: many types could type the same term.
 * So we want typechecking to return `Some` iff it's typeable, but the types themselves may differ. *)

From Coq Require Import
  Lists.List.
Export ListNotations.
From Adam Require Import
  OptionBind
  Subst
  Terms.

(* Semantics:
 * `None` means never typable, no matter the context;
 * `Some (ty, ctx)` means typed with `ctx` left over *)
Fixpoint typecheck ctx (t : term) :=
  match t with
  | TmVarS x => match ctx with [] => None | (s, ty) :: tl => if eqb x s then Some (ty, tl) else None end
  | TmAtom id lvl => Some (TmAtom id (S lvl), ctx)
  (* | TmAtom id lvl => match ctx with [] => Some (TmAtom id (S lvl), ctx) | _ :: _ => None end *)
  | TmPack id arg ty curry =>
      let ectx := match arg with None => ctx | Some s => (s, ty) :: ctx end in
      match atom_id curry with
      | None => None
      | Some aid =>
          if eqb id aid then
            match typecheck ectx curry with
            | Some (ct, etc) => Some (TmForA arg ty ct, etc)
            | _ => None
            end
          else None
      end
  | TmForA arg ty curry =>
      let ectx := match arg with None => ctx | Some s => (s, ty) :: ctx end in
      match typecheck ectx curry with
      | None => None
      | Some (ct, etc) => Some (TmForA arg ty ct, etc)
      end
  | TmAppl f x =>
      match typecheck ctx f with
      | Some (TmForA arg ty curry, leftover) =>
          let if_successful := (fun y => match y with (tx, etc) =>
            if eq_term ty tx then
              match arg with
              | None => Some (curry, etc)
              | Some s =>
                  match subst s x curry with
                  | Unused => None
                  | Used t => Some (t, etc)
                  end
              end
            else None
          end) in option_bind if_successful (typecheck leftover x)
      | _ => None
      end
  | _ => None
  end.
