def strTag (s : String) : Nat :=
  match s with
  | "live" => 1
  | _ => 0

theorem strTag_live : strTag "live" = 1 := rfl
