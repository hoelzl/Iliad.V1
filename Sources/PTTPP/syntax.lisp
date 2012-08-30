;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 2012 Matthias Hölzl
;;;
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

(in-package #:pttpp-syntax)
(5am:in-suite pttpp-syntax-suite)

;;; Mixins
;;; ======

(defclass name-mixin ()
  ((name :accessor name :initarg :name :initform :<unnamed>
	 :type symbol))
  (:documentation
   "Mixin inherited by all classes that have names."))

(defclass required-name-mixin (name-mixin)
  ((name :initform (required-argument :name)))
  (:documentation
   "Mixin inherited by all classes that require a name."))

(defclass known-term ()
  ()
  (:documentation
   "Mixin inherited by all classes that are known to the compiler."))

(defgeneric is-known-term-p (term)
  (:documentation
   "Returns true if TERM is specialized in the compiler.")
  (:method (term)
    nil)
  (:method ((term known-term))
    t))

;;; Compilation Context
;;; ===================

;;; A compilation context encapsulates the information needed by the
;;; compiler.

(defclass compilation-context ()
  ()
  (:documentation
   "Context needed by the compiler."))

(defgeneric lookup-functor (name arity context &optional create?)
  (:documentation
   "Return the functor with NAME and ARITY for the given CONTEXT if it
   exists. Otherwise, if CREATE? is true, create and return a fresh
   functor, if CREATE? is false return NIL."))

(defgeneric (setf lookup-functor) (new-value name arity context))

(defgeneric lookup-variable (name context &optional create?)
  (:documentation
   "Return the variable NAME for the given CONTEXT if it
   exists. Otherwise, if CREATE? is true, create and return a fresh
   variable, if CREATE? is false return NIL."))

(defgeneric (setf lookup-variable) (new-value name context))

;;; Compilation units
;;; =================

;;; A compilation unit is a long-lasting context.

(defvar *default-known-operators*
  '())

(defun default-known-operators ()
  (plist-hash-table *default-known-operators*))

(defclass compilation-unit (compilation-context)
  ((known-operators
    :accessor known-operators :initarg :known-operators
    :initfunction default-known-operators
    :documentation "Special operators for this compilation unit.")
   (variable-hash-table
    :accessor variable-hash-table :initarg :variable-hash-table
    :initform (make-hash-table)
    :documentation "Hash table for interning variables.")
   (functor-hash-table
    :accessor functor-hash-table :initarg :functor-hash-table
    :initform (make-hash-table)
    :documentation "Hash table for interning functors"))
  (:documentation
   "A single compilation unit."))

(defmethod lookup-variable (name (context compilation-unit) &optional (create? t))
  (let ((hash-table (slot-value context 'variable-hash-table)))
    (multiple-value-bind (variable exists?)
	(gethash name hash-table nil)
      (cond (exists? variable)
	    (create?
	     (setf (lookup-variable name context)
		   (make-instance 'variable :name name :intern nil)))
	    (t nil)))))

(defmethod (setf lookup-variable) (new-value name (context compilation-unit))
  (let ((hash-table (slot-value context 'variable-hash-table)))
    (setf (gethash name hash-table) new-value)))

(defmethod lookup-functor (name arity (context compilation-unit) &optional (create? t))
  (let* ((hash-table-1 (slot-value context 'functor-hash-table))
	 (hash-table-2 (gethash* name hash-table-1 (make-hash-table))))
    (multiple-value-bind (functor exists?)
	(gethash arity hash-table-2 nil)
      (cond (exists? functor)
	    (create?
	     (setf (lookup-functor name arity context)
		   (make-instance 'functor :name name :arity arity :intern nil)))
	    (t nil)))))

(defmethod (setf lookup-functor) (new-value name arity (context compilation-unit))
  (let* ((hash-table-1 (slot-value context 'functor-hash-table))
	 (hash-table-2 (gethash* name hash-table-1 (make-hash-table))))
    (setf (gethash arity hash-table-2) new-value)))

#+(or)
(defmethod lookup-number (value (context compilation-unit) &optional (create? t))
  (let* ((hash-table (slot-value context 'number-hash-table)))
    (multiple-value-bind (number exists?)
	(gethash value hash-table nil)
      (cond (exists? number)
	    (create?
	     (setf (lookup-number value context)
		   (make-instance 'number :value value :intern nil)))
	    (t nil)))))

#+(or)
(defmethod (setf lookup-number) (new-value value (context compilation-unit))
  (let* ((hash-table (slot-value context 'number-hash-table)))
    (setf (gethash value hash-table) new-value)))


;;; We define an ambivalent syntax similar to Prolog.  

(defclass term ()
  ()
  (:documentation
   "Superclass for all (function) terms and atomic predicates."))

(defmethod shared-initialize :before ((term term) slot-names
				      &key (intern nil) context)
  ;; Allow the :context and :intern keywords for all terms.
  (declare (ignore context))
  (when intern
    (cerror "Create the instance without interning it."
	    "Trying to intern term ~A." term)))

(defclass variable (term name-mixin)
  ((runtime-variable :accessor runtime-variable :initarg :runtime-variable
		     :type logic-variable :initform nil))
  (:documentation
   "Representation of variables."))

(define-interning-make-instance variable name)

#+5am
(5am:test test-variable-interning
  (let ((cu (make-instance 'compilation-unit)))
    (5am:is (eq (make-instance 'variable :name 'f :context cu)
		(make-instance 'variable :name 'f :context cu)))
    (5am:is (eq (make-instance 'variable :name 'g :context cu)
		(make-instance 'variable :name 'g :context cu)))
    (5am:is (not (eq (make-instance 'variable :name 'f :context cu)
		     (make-instance 'variable :name 'g :context cu))))))

(defclass constant (term)
  ()
  (:documentation
   "Representation of constants."))

;;; It's not clear that we want to have this class.  Maybe just use
;;; Lisp numbers instead?
#+(or)
(defclass number (constant)
  ((value :accessor value :initarg :value :initform (required-argument :value)
	  :type number))
  (:documentation
   "Representation of numbers."))

#+(or)
(define-interning-make-instance number value)

#+(or)
(5am:test test-number-interning
  (let ((cu (make-instance 'compilation-unit)))
    (5am:is (not (eq (make-instance 'number :value 0)
		     (make-instance 'number :value 0))))
    (5am:is (eq (make-instance 'number :value 0 :context cu)
		(make-instance 'number :value 0 :context cu)))
    (5am:is (eq (make-instance 'number :value 1 :context cu)
		(make-instance 'number :value 1 :context cu)))
    (5am:is (not (eq (make-instance 'number :value 0 :context cu)
		     (make-instance 'number :value 1 :context cu))))))

(defclass atom (constant)
  ()
  (:documentation
   "Representation of atoms, i.e., non-numeric constants."))

(defclass functor (atom required-name-mixin)
  ((arity :accessor arity :initarg :arity :initform (required-argument :arity)
	  :type (or null positive-fixnum))
   (negated-functor :accessor negated-functor :initarg :negated-functor
		    :initform nil :type (or null functor)))
  (:documentation
   "Representation of functors.  Interned, to simplify negation."))

(define-interning-make-instance functor name arity)

#+5am
(5am:test test-functor-interning
  (let ((cu (make-instance 'compilation-unit)))
    (5am:is (not (eq (make-instance 'functor :name 'f :arity 1)
		     (make-instance 'functor :name 'f :arity 1))))
    (5am:is (eq (make-instance 'functor :name 'f :arity 1 :context cu)
		(make-instance 'functor :name 'f :arity 1 :context cu)))
    (5am:is (eq (make-instance 'functor :name 'f :arity 1 :context cu)
		(make-instance 'functor :name 'f :arity 1 :context cu)))
    (5am:is (not (eq (make-instance 'functor :name 'f :arity 0 :context cu)
		     (make-instance 'functor :name 'f :arity 1 :context cu))))))

(defclass compound-term (atom)
  ((arguments :accessor arguments :initarg :arguments :initform '()
	      :type list))
  (:documentation
   "Representation of compound terms, i.e., functions and atomic
   predicates."))

(defgeneric is-compound-term-p (term)
  (:documentation
   "Returns true if TERM is a compound term.")
  (:method (term)
    nil)
  (:method ((term compound-term))
    t))

(defgeneric operator (compound-term)
  (:documentation
   "The operator of COMPOUND-TERM.")
  (:method ((term compound-term))
    (error "No operator defined for compound term ~A." term)))

(defclass application (compound-term)
  ((operator :accessor operator :initarg :operator :initform (required-argument :operator)
	    :type term))
  (:documentation
   "Representation of a compound term about which the compiler has no
   special knowledge."))

(defclass known-compound (compound-term known-term)
  ()
  (:documentation
   "Representation of a compound term that the compiler knows about."))

(defclass conjunction (known-compound)
  ()
  (:documentation
   "Representation of conjunctions."))

(defmethod operator ((term conjunction))
  'and)

(defclass disjunction (known-compound)
  ()
  (:documentation
   "Representation of disjunctions."))

(defmethod operator ((term disjunction))
  'or)
			  
(defclass negation (known-compound)
  ()
  (:documentation
   "Representation of negation."))

(defmethod operator ((term negation))
  'not)

(defclass implication (known-compound)
  ()
  (:documentation
   "Representation of implication"))

(defmethod operator ((term implication))
  '->)

(defclass reverse-implication (known-compound)
  ()
  (:documentation
   "Representation of implication, written the wrong way."))

(defmethod operator ((term reverse-implication))
  '<-)

(defclass equivalence (known-compound)
  ()
  (:documentation
   "Representation of logical equivalence (if and only if)."))

(defclass quantification (known-compound)
  ((bound-variables :accessor bound-variables :initarg :bound-variables
		    :initform (required-argument :bound-variables)))
  (:documentation
   "Representation of all quantifications."))

(defclass universal-quantification (quantification)
  ()
  (:documentation
   "Representation of an universally quantified statement."))

(defmethod operator ((term universal-quantification))
  'foreach)

(defclass existential-quantification (quantification)
  ()
  (:documentation
   "Representation of an existentially quantified statement."))

(defmethod operator ((term existential-quantification))
  'foreach)

(defglobal *logical-operators*
    '(and           conjunction
      &             conjunction
      |,|           conjunction
      or            disjunction
      |;|           disjunction
      not           negation
      |~|           negation
      ->            implication
      implies       implication
      if            implication
      <-            reverse-implication
      only-if       reverse-implication
      implied-by    reverse-implication
      is-implied-by reverse-implication
      <->           equivalence
      eqiv          equivalence
      equivalent    equivalence
      is-equivalent equivalence
      foreach       universal-quantification
      each          universal-quantification
      forall        universal-quantification
      exist         existential-quantification
      exists        existential-quantification))

(setf *default-known-operators* *logical-operators*)
