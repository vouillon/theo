open Theo
open Theo.Syntax

let assert_equal_int i1 i2 msg =
  if i1 <> i2 then (
    Printf.printf "FAIL: %s: expected %d, got %d\n" msg i2 i1;
    failwith msg)

let test_shortest_sat () =
  Printf.printf "Test shortest_sat...\n";

  (* Case 1: (a' & b' & c') || d' 
     Greedy 'sat' might pick d'=T or (a'=T... depending on order).
     Shortest should be length 1 (d'=T).
  *)
  let d' = atom (var Boolean) in
  let a' = atom (var Boolean) in
  let b' = atom (var Boolean) in
  let c' = atom (var Boolean) in

  let expr1 = (a' && b' && c') || d' in

  begin match shortest_sat expr1 with
  | Some assign ->
      Printf.printf "Case 1 Shortest sat length: %d\n" (List.length assign);
      assert_equal_int (List.length assign) 1 "Case 1 Shortest path length"
  | None -> failwith "Shortest sat failed for Case 1"
  end;

  (* Case 2: Greedy trap *)

  (* Variable order: d' < a' < b' < c'.
     Root is d'.
     d' ---high---> True (Length 1 assignment: d'=T)
     d' ---low----> (a' & b' & c')
     
     Greedy 'sat' (pref high) picks d'=T immediately?
     Yes, if d' is top, sat(high) works.
     So greedy = shortest here.
     
     We need a case where High branch is LONG and Low branch leads to SHORT.
     
     Root = x0.
     High -> x1 & x2 & x3 & T. (Len 4)
     Low -> y1 & T. (Len 2)
     
     So we need (x0 & x1 & x2 & x3) \/ (!x0 & y1).
     Order: x0 < x1 < x2 < x3 < y1.
     x0 High -> x1... (len 4)
     x0 Low -> y1 (len 2: x0=F, y1=T)
     
     'sat' usually prefers High, so it picks x0=T, x1=T... (Length 4).
     'shortest_sat' should pick x0=F, y1=T (Length 2).
  *)
  let x0 = atom (var Boolean) in
  let x1 = atom (var Boolean) in
  let x2 = atom (var Boolean) in
  let x3 = atom (var Boolean) in
  let y1 = atom (var Boolean) in

  let long_path = x0 && x1 && x2 && x3 in
  let short_path = (not x0) && y1 in
  let expr = long_path || short_path in

  begin match sat expr with
  | Some assign ->
      Printf.printf "Greedy sat length: %d\n" (List.length assign);
      (* Greedy should explore x0=T branch first *)
      if List.length assign < 4 then
        Printf.printf "Warning: Greedy found short path?\n"
  | None -> failwith "Greedy sat failed"
  end;

  match shortest_sat expr with
  | Some assign ->
      Printf.printf "Shortest sat length: %d\n" (List.length assign);
      assert_equal_int (List.length assign) 2 "Shortest path length"
  | None -> failwith "Shortest sat failed"

let () =
  test_shortest_sat ();
  Printf.printf "OK\n"
