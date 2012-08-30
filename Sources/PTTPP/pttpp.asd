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
  :components ((:file "packages")
	       (:file "bootstrap")
	       (:file "utilities")
	       (:file "new-runtime")
               (:file "runtime")
	       (:file "syntax-bootstrap")
	       (:file "syntax")
               (:file "compiler")
               (:file "builtins")
	       (:file "golog")))
