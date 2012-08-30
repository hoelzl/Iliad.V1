;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 2012 Matthias Hölzl
;;;
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

(in-package #:pttpp-syntax)

(5am:in-suite pttpp-syntax-suite)

;;; Interning instances
;;; ===================

(defvar *compound-term-hash* (make-hash-table))

(defmacro define-interning-make-instance (class-name primary-key &optional secondary-key)
  (let ((accessor (symbolicate '#:lookup- class-name)))
    (if secondary-key
	`(defmethod make-instance ((class (eql (find-class ',class-name)))
				   &key ,primary-key ,secondary-key
                                        (intern t) context)
	   (if (and intern context)
               (let ((instance (,accessor ,primary-key ,secondary-key context nil)))
                 (or instance
                     (setf (,accessor ,primary-key ,secondary-key context)
                           (call-next-method))))
	       (call-next-method)))
	`(defmethod make-instance ((class (eql (find-class ',class-name)))
				   &key ,primary-key (intern t) context)
	   (if (and intern context)
               (let ((instance (,accessor ,primary-key context nil)))
                 (or instance
                     (setf (,accessor ,primary-key context)
                           (call-next-method))))
	       (call-next-method))))))

