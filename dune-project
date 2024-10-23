(lang dune 3.0)
(name "adelfa")
(wrapped_executables false)

(authors
 "Mary Southern"
 "Chase Johnson <joh13266@umn.edu>")
(maintainers "Chase Johnson <joh13266@umn.edu>")
(homepage "https://adelfa-prover.org/")
(documentation "https://adelfa-prover.org/")
(source 
 (github adelfa-prover/adelfa))
(license GPL-3.0)
(generate_opam_files)

(package
 (name adelfa)
 (synopsis "Proof assistant for reasoning about LF specifications")
 (depends
  (ounit2 :with-test)))
