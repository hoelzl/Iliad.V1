;;;; pttpp.asd

(asdf:defsystem #:pttpp
  :serial t
  :description "The Prolog Technology Theorem Prover for Poem"
  :version "0.0.4"
  :author "Mark E. Stickel, SRI International (original author)"
  :author "Matthias Hoelzl <tc@xantira.com>"
  :license "MIT, see file LICENSE"
  :depends-on (#:alexandria
	       #:fiveam
               #:iterate)
  :components ((:file "package")
	       (:file "bootstrap")
	       (:file "utilities")
               (:file "runtime")
               (:file "compiler")
               (:file "builtins")))
