Definition option_bind {A B} : (A -> option B) -> option A -> option B := fun f opt =>
  match opt with
  | None => None
  | Some x => f x
  end.
Arguments option_bind {A B} f/ opt.
