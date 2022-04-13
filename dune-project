(lang dune 3.0)
(name "adelfa")
(wrapped_executables false)

(homepage "http://sparrow.cs.umn.edu/adelfa/index.html")
(documentation "http://sparrow.cs.umn.edu/adelfa/reference-guide.html")

(package
 (name adelfa)
 (synopsis "Proof assistant for reasoning about LF specifications")
 (depends
  (ounit2 :with-test)))
