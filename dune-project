(lang dune 3.17)

(name theo)

(generate_opam_files true)

(package
 (name theo)
 (synopsis "A BDD library with theory support")
 (description
  "A Boolean Decision Diagram library implemented in OCaml, with built-in support for atomic constraints over specific theories (like strings and semantic versions).")
 (depends
  (ocaml
   (>= 4.08))
  (dune
   (>= 3.17))
  (qcheck
   (and
    :with-test
    (>= 0.18))))
 (authors "Jérôme Vouillon")
 (maintainers "Jérôme Vouillon")
 (license MIT))
