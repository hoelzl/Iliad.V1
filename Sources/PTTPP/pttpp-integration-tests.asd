;;; pttpp-integration-tests

(asdf:defsystem #:pttpp-integration-tests
  :serial t
  :description "Integration tests for PTTPP"
  :version "0.0.4"
  :author "Mark E. Stickel, SRI International (original author)"
  :author "Matthias Hoelzl <tc@xantira.com>"
  :license "MIT, see file LICENSE"
  :depends-on (#:alexandria
	       #:fiveam
               #:iterate
	       #:pttpp)
  :components ((:file "package")
	       (:file "integration-tests")))
