;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 2012 Matthias Hölzl
;;;
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

;;; The runtime of PTTPP.
;;; ====================

;;; This is the new runtime that will (over time) replace the old
;;; runtime in the file runtime.lisp.

(in-package #:pttpp)
;; (declaim (optimize (debug 3)))
;; (declaim (optimize (speed 2) (compilation-speed 0)))

#+5am
(5am:in-suite pttpp-runtime-suite)

;;; Runtime representation of variables
;;; ===================================

(defstruct (logic-variable (:conc-name variable-)
                           (:constructor)
                           (:constructor new-variable (name level))
                           (:predicate variable-p))
  "Runtime representation of logic variables."
  (level 0 :type fixnum)
  value
  name)

(defmethod make-load-form ((var logic-variable) &optional environment)
  (make-load-form-saving-slots var
                               :slot-names '(level value name)
                               :environment environment))

