;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 2012 Matthias Hölzl
;;; 
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

(in-package #:pttpp)

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
(5am:def-suite pttpp-integration-suite
  :in pttpp-suite
  :description "Integration tests for the PTTPP compiler.")

#+5am
(defmacro define-integration-test (name &body body)
  `(5am:test (,name :suite pttpp-integration-suite)
     (let ((*print-compile-names* nil)
           (*print-compile-times* nil)
           (*print-execution-time* nil)
           (*print-clauses* nil)
           (*trace-search* nil)
           (*print-proof* nil)
           (*print-trail* nil)
           (*print-success-notification* nil)
           (*single-solution* t))
       ,@body)))

