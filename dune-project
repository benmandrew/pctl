(lang dune 2.9)

(name pctl)

(generate_opam_files true)

(source
 (github benmandrew/pctl))

(authors "Ben Andrew")

(maintainers "Ben Andrew")

(license MIT)

(package
 (name pctl)
 (synopsis "Probabilistic CTL model checker")
 (description "Probabilistic CTL model checker")
 (depends
  (ocaml (>= 4.14.0))
  (dune (>= 2.0.0))
  (sexplib (>= v0.16.0))
  (ppx_inline_test (and (>= v0.16.0) :with-test))
  (ppx_compare (>= v0.16.0))))
