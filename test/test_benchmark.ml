open Theories
module F = Formula

let assert_bool b msg = if Stdlib.not b then failwith ("FAIL: " ^ msg)

let test_optimization () =
  Printf.printf "Test optimization (balanced vs linear)...\n";
  let open Formula.Syntax in
  let vars = List.init 20 (fun _ -> bool (Theo.Var.fresh ())) in

  (* Re-implement linear fold for comparison *)
  let linear_and = List.fold_left ( && ) F.true_ vars in
  let linear_or = List.fold_left ( || ) F.false_ vars in

  let optimized_and = F.and_list vars in
  let optimized_or = F.or_list vars in

  assert_bool
    (F.equivalent linear_and optimized_and)
    "and_list matches linear fold";
  assert_bool
    (F.equivalent linear_or optimized_or)
    "or_list matches linear fold";

  (* Verify correctness on a mixed list *)
  let mixed = List.map (fun v -> if Random.bool () then v else not v) vars in
  let linear_mixed_and = List.fold_left ( && ) F.true_ mixed in
  let optimized_mixed_and = F.and_list mixed in

  assert_bool
    (F.equivalent linear_mixed_and optimized_mixed_and)
    "mixed and_list matches linear fold";

  Printf.printf "OK\n"

let () = test_optimization ()
