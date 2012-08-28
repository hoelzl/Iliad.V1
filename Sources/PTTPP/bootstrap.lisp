;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 1986 Mark E. Stickel, SRI International, Menlo Park, CA 94025 USA
;;; Copyright (c) 2012 Matthias Hölzl
;;;
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

;;; Stuff that has to be evaluated early.


(in-package #:pttpp)


(setq *print-radix* nil)

;;; name of procedure being compiled
(defvar *name* nil)
;;; compile-procedure option to compile code for tracing
(defvar *traceable*)
;;; compile code to count successful unifications?
(defvar *count-calls* t)


(defstruct (runtime-data (:conc-name rt-))
  (trail-array (make-array 10000) :type simple-vector)
  (trail-index -1 :type fixnum))


;;; QUERY/0 is generated by the PTTPP compiler and not defined in the Lisp
;;; code.  Declare its type to avoid compiler warnings.  We need to add a more
;;; general solution, since the same problem appear for all predicates
;;; generated by the compiler.  Figure out where the best place to add
;;; declarations might be.
;;;
(declaim (ftype (function (t t) t) query/0))

;;; counter for number of inferences
(defvar *ncalls* 0)

(defun wrap-count-calls (form)
  (if (and *count-calls* (not (eq *name* 'query/0)))
      `(progn (incf *ncalls*) ,form)
      form))

(defun head-locs (terms &optional (name 'arg) nth)
  (let* ((prop (if nth 'nth-arguments 'arguments))
         (n (if (numberp terms) terms (length terms)))
         (l (get name prop)))
      (or (cdr (assoc n l))
	  (let (w)
	    (dotimes (i n)
	      (push (if nth
			`(nth ,(1+ i) ,name)
			(intern (concatenate 'string "!" (symbol-name name)
					     (princ-to-string (1+ i)) "!")
				'pttpp))
		    w))
	    (setq w (nreverse w))
	    (setf (get name prop) (cons (cons n w) l))
	    w))))

(defmacro specifier (x)
  `(get ,x 'specifier))
(defmacro precedence (x)
  `(get ,x 'precedence))

(defun wrap-exit-redo-trace (form)
  (if *traceable*
      `(trace-exit-redo ,*name* ,form)
      form))

(defmacro invisible-functor-p (x)
  `(get ,x 'invisible-functor))
