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
  ppx_deriving))

(using menhir 2.1)
