(lang dune 3.17)

(name theo)

(generate_opam_files true)

(source
 (github vouillon/theo))

(homepage "https://github.com/vouillon/theo")

(documentation "https://vouillon.github.io/theo/")

(package
 (name theo)
 (synopsis "A BDD library with theory support")
 (description
  "A Boolean Decision Diagram library implemented in OCaml, with built-in support for atomic constraints over specific theories (like strings and semantic versions).")
 (depends
  (ocaml
   (>= 4.14))
  (qcheck
   (and
    :with-test
    (>= 0.90))))
 (authors "Jérôme Vouillon")
 (maintainers "Jérôme Vouillon")
 (license MIT))
