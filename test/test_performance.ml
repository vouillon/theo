open Theo

let benchmark name f =
  let t0 = Unix.gettimeofday () in
  let res = f () in
  let t1 = Unix.gettimeofday () in
  Printf.printf "%s: %.4fs\n%!" name (t1 -. t0);
  res

let test_chain_construction () =
  Printf.printf "Testing chain construction performance...\n";
  let var_x = Theo.var String in
  let n = 10000 in

  (* Construct a list of inequalities: x != "0", x != "1", ..., x != "N" *)
  let constraints =
    List.init n string_of_int |> List.map (fun s -> Theo.is_not_equal var_x s)
  in

  (* Use fold_right to force bottom-up construction which triggers simple_node repeatedly *)
  let construct () = Theo.and_list constraints in

  let _ = benchmark (Printf.sprintf "Constructing chain of %d" n) construct in
  ()

let () =
  test_chain_construction ();
  Printf.printf "Performance test passed.\n"
