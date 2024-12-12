(lang dune 2.8)

(name ou-lang)

(using menhir 2.1)

(generate_opam_files true)

(source
 (github morusleaf/dzkp))

(authors "Yuyang Sang")

(maintainers "Yuyang Sang")

(license LICENSE)

(documentation https://github.com/morusleaf/dzkp/tree/main/doc)

(package
 (name ou-lang)
 (synopsis "Ou: A distributive zero knowledge Proof language")
 (description "A longer description")
 (depends ocaml dune menhir fmt logs alcotest)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
