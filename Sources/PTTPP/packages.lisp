;;;; package.lisp


(defpackage #:pttpp-utilities
  (:use #:common-lisp #:alexandria #:iterate)
  (:nicknames #:utils)
  (:export
   ;; General utilities
   #:defglobal
   #:gethash*
   #:numbered-letter
   ;; Support for testing
   #:pttpp-suite
   #:pttpp-runtime-suite
   #:pttpp-syntax-suite
   #:pttpp-compiler-suite
   #:pttpp-builtins-suite
   #:pttpp-golog-suite
   #:pttpp-integration-suite))

(defpackage #:pttpp-syntax
  (:use #:common-lisp #:alexandria #:iterate
	#:pttpp-utilities)
  (:nicknames #:syntax)
  (:shadow #:structure
	   #:variable #:atom #:number
	   #:conjoin #:disjoin))

(defpackage #:pttpp
  (:use #:common-lisp #:alexandria #:iterate
	#:pttpp-utilities)
  (:shadow #:conjoin #:disjoin))
