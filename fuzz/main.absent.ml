(* Substituted for main.fuzz.ml by the (select ...) clause in fuzz/dune when
   monolith is not installed, so that plain [dune build] always succeeds. *)
let () =
  prerr_endline "The fuzzing harness requires monolith: opam install monolith";
  exit 2
