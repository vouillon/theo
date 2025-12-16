open Theo
open Theo.Syntax

let assert_bool b msg = if Stdlib.not b then failwith ("FAIL: " ^ msg)

let test_optimization () =
  Printf.printf "Test optimization (balanced vs linear)...\n";

  let vars = List.init 20 (fun _ -> atom (var Boolean)) in

  (* Re-implement linear fold for comparison *)
  let linear_and = List.fold_left ( && ) true_ vars in
  let linear_or = List.fold_left ( || ) false_ vars in

  let optimized_and = and_list vars in
  let optimized_or = or_list vars in

  assert_bool
    (equivalent linear_and optimized_and)
    "and_list matches linear fold";
  assert_bool (equivalent linear_or optimized_or) "or_list matches linear fold";

  (* Verify correctness on a mixed list *)
  let mixed = List.map (fun v -> if Random.bool () then v else not v) vars in
  let linear_mixed_and = List.fold_left ( && ) true_ mixed in
  let optimized_mixed_and = and_list mixed in

  assert_bool
    (equivalent linear_mixed_and optimized_mixed_and)
    "mixed and_list matches linear fold";

  Printf.printf "OK\n"

let () = test_optimization ()
