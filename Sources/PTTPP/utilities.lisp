;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 2012 Matthias Hölzl
;;; 
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

(in-package #:pttpp)

;;; General utilities
;;; =================

(defmacro defglobal (name value &optional doc)
  `(#+sbcl sb-ext:defglobal
    #-sbcl defvar
    ,name ,value ,@(if doc (list doc) ())))


;;; Numbering WFFs
;;; --------------

(defun numbered-letter (n)
  (case n
    ( 1 "a") ( 2 "b") ( 3 "c") ( 4 "d") ( 5 "e")
    ( 6 "f") ( 7 "g") ( 8 "h") ( 9 "i") (10 "j")
    (11 "k") (12 "l") (13 "m") (14 "n") (15 "o")
    (16 "p") (17 "q") (18 "r") (19 "s") (20 "t")
    (21 "u") (22 "v") (23 "w") (24 "x") (25 "y")
    (26 "z")))

;;; Testing
;;; =======

#+5am
(5am:def-suite pttpp-suite
  :description "The suite containing all tests for PTTPP.")

#+5am
(5am:def-suite pttpp-runtime-suite
  :in pttpp-suite
  :description "Tests for the PTTPP runtime.")

#+5am
(5am:def-suite pttpp-compiler-suite
  :in pttpp-suite
  :description "Tests for the PTTPP compiler.")

#+5am
(5am:def-suite pttpp-builtins-suite
  :in pttpp-suite
  :description "Tests for the PTTPP built-in Prolog predicates.")

#+5am
(5am:def-suite pttpp-integration-suite
  :in pttpp-suite
  :description "Integration tests for the PTTPP compiler.")

#+5am
(defmacro define-integration-test (name &body body)
  `(5am:test (,name :suite pttpp-integration-suite :compile-at :definition-time)
     (let ((*print-compile-names* nil)
           (*print-compile-times* nil)
           (*print-execution-time* nil)
           (*print-clauses* nil)
           (*traceable* nil)
           (*trace-search* nil)
           (*print-proof* nil)
           (*print-trail* nil)
           (*print-success-notification* nil)
           (*single-solution* t))
       ,@body)))

