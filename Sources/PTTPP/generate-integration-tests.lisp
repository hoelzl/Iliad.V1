;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 1986 Mark E. Stickel, SRI International, Menlo Park, CA 94025 USA
;;; Copyright (c) 2012 Matthias Hölzl
;;; 
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

(in-package #:pttpp)
(declaim (optimize (debug 3)))

(eval-when (:compile-toplevel :load-toplevel :execute)
(defvar *integration-test-generators* '())

(when (not (fboundp 'undefine-all-test-predicates))
  (defun undefine-all-test-predicates ()
    (undefine-predicates 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm
                         'n 'o 'p 'q 'r 's 't 'u 'v 'w 'x 'y 'z
                         'member)))

(defmacro generate-integration-test (name &body body)
  (let ((generator-name (let ((*print-case* :upcase))
                          (intern (format nil "~A-GENERATOR" name)))))
    (pushnew generator-name *integration-test-generators*)
    `(defun ,generator-name ()
       (let ((*print-compile-names* nil)
             (*print-compile-times* nil)
             (*print-execution-time* nil)
             (*print-clauses* nil)
             (*trace-search* nil)
             (*print-proof* nil)
             (*print-trail* nil)
             (*print-success-notification* nil)
             (*single-solution* t))
         ,@body
         (let ((bindings '())
               (tests `((5am:is (= ,(rt-trail-index *runtime-data*)
                                   (rt-trail-index *runtime-data*)))))
               (counter 0))
           (labels ((name (prefix)
                      (intern (format nil "~A-~A" prefix (incf counter))))
                    (walk (obj form)
                      (cond ((variable-p obj)
                             (let* ((name (name "VAR"))
                                    (value (variable-value obj)))
                               (push `(,name ,form) bindings)
                               (push `(5am:is (= ',(variable-level obj)
                                                 (variable-level ,name)))
                                     tests)
                               (push `(5am:is (eql ',(variable-name obj)
                                                     (variable-name ,name)))
                                     tests)
                               (when (atom value)
                                 (push `(5am:is (equalp ',value
                                                        (variable-value ,name)))
                                       tests))
                               (walk value `(variable-value ,name))))
                            ((consp obj)
                             (let ((name (name "PRED")))
                               (push `(,name ,form) bindings)
                               (dotimes (i (length obj))
                                 (if (zerop i)
                                     (push `(5am:is (eql ',(nth i obj)
                                                         (first ,name))) tests)
                                     (let ((value (nth i obj)))
                                       (when (atom value)
                                         (push `(5am:is (equalp ',value
                                                                (nth ,i ,name)))
                                               tests))
                                       (walk value `(nth ,i ,name)))))))
                            (t
                             ;; Do nothing
                             nil))))
             (dotimes (i (1+ (rt-trail-index *runtime-data*)))
               (walk (aref (rt-trail-array *runtime-data*) i)
                     `(aref (rt-trail-array *runtime-data*) ,i)))
             `(define-integration-test ,',name
                ,@',body
                (let* (,@(nreverse bindings))
                  ,@(nreverse tests)))))))))

(defun run-all-generators (&optional (output-stream nil))
  (let ((*print-case* :downcase)
        (*print-circle* nil)
        (*print-readably* t))
    (format output-stream "~&~{#+5AM~%~W~2%~}"
            (mapcar (lambda (g)
                      (funcall g))
                    (reverse *integration-test-generators*)))))

(defun generate-integration-test-file (&optional (file-name "integration-tests.lisp"))
  (with-open-file (stream file-name :direction :output :if-exists :supersede)
    (format stream
            "~
;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; THIS FILE IS AUTOMATICALLY GENERATED BY THE INTEGRATION TEST GENERATOR.
;;; Edit generate-integration-tests.lisp instead of this file. 

;;; Copyright (c) 1986 Mark E. Stickel, SRI International, Menlo Park, CA 94025 USA
;;; Copyright (c) 2012 Matthias Hölzl
;;; 
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

(in-package #:pttpp)
(declaim (optimize (debug 3)))

(defun undefine-all-test-predicates ()
  (undefine-predicates 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm
                       'n 'o 'p 'q 'r 's 't 'u 'v 'w 'x 'y 'z
                       'member))

")
    (run-all-generators stream)))
) ;; eval-when

(generate-integration-test simple-integration-test-01
  (undefine-all-test-predicates)
  (program '()
	   '((f a b)
	     (<- (query) (f a b)))
	   :traceable nil)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-02
  (undefine-all-test-predicates)
  (program '(x y)
	   '((g a b)
	     (<- (f x y) (g x y))
	     (<- (query)
              (f x b)))
	   :traceable nil)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-03
  (undefine-all-test-predicates)
  (program '(x y)
	   '((f a b)
	     (<- (query)
	      (and
	       (f x b)))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-04
  (undefine-all-test-predicates)
  (program '(x y)
	   '((g a b)
	     (g c d)
	     (g a d)
	     (h a a)
	     (h a b)
	     (h c c)
	     (<- (f x y) (and (g x y) (h x x)))
	     (<- (query)
	      (and
	       (f x b)
	       (f c y)
	       (f x y)))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-04a
  (undefine-all-test-predicates)
  (program '(x y)
	   '((g a b)
	     (g c d)
	     (g a d)
	     (h a a)
	     (h a b)
	     (h c c)
	     (<- (f x y) (and (g x y) (h x x)))
	     (<- (query)
	      (and
	       (f x d)
	       (f c y)
	       (f x y))))
	   :traceable nil)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-04b
  (undefine-all-test-predicates)
  (program '(x y)
	   '((g a b)
	     (g c d)
	     (g a d)
	     (h a b)
	     (h c c)
	     (<- (f x y) (and (g x y) (h x x)))
	     (<- (query)
	      (and
	       (f x b)
	       (f c y)
	       (f x y)))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-05
  (undefine-all-test-predicates)
  (program '(x y)
	   '((g a b)
	     (g c d)
	     (g a d)
	     (h a a)
	     (h a b)
	     (h c c)
	     (<- (f x y) (or (g x y) (h x x)))
	     (<- (query)
	      (and
	       (f x b)
	       (f c y)
	       (f x y)))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-06
  (undefine-all-test-predicates)
  (program '(x y zs)
	   '((member x (cons x zs))
	     (<- (member x (cons y zs))
	      (and (\\== x y) (member x zs)))
	     (<- (query)
	      (member x (cons a (cons b (cons c nil)))))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-07
  (undefine-all-test-predicates)
  (program '(x y zs)
	   '((member x (cons x zs))
	     (<- (member x (cons y zs))
	      (and (\\== x y) (member x zs)))
	     (<- (query)
	      (search
	       (member x (cons a (cons b (cons c nil))))))))
  (query)
  (undefine-all-test-predicates))


(generate-integration-test simple-integration-test-08
  (undefine-all-test-predicates)
  (program '(x y zs)
	   '((member x (cons x zs))
	     (<- (member x (cons y zs))
	      (member x zs))
	     (<- (query)
	      (search
	       (member x (cons a (cons b (cons c nil))))))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-09
  (undefine-all-test-predicates)
  (program '(x y zs)
	   '((member x (cons x zs))
	     (<- (member x (cons y zs))
	      (member x zs))
	     (<- (query)
	      (search (member x y)
	       5))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-09a
  (undefine-all-test-predicates)
  (program '(x y zs)
	   '((member x (cons x zs))
	     (<- (member x (cons y zs))
	      (member x zs))
	     (<- (query)
	      (search (member x y)
	       1000))))
  (let ((*print-trail* nil))
    (query))
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-10
  (undefine-all-test-predicates)
  (program '(x y zs)
	   '((member x (cons x zs))
	     (<- (member x (cons y zs))
	      (and (\\== x y) (member x zs) !))
	     (<- (query)
	      (member x (cons a (cons b (cons c nil)))))))
  (query)
  (undefine-all-test-predicates))


(generate-integration-test simple-integration-test-10a
  (undefine-all-test-predicates)
  (program '(x y zs)
	   '((member x (cons x zs))
	     (<- (member x (cons y zs))
	      (and (\\== x y) (member x zs) !))
	     (<- (query)
	       (search
		 (member x (cons a (cons b (cons c nil))))))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-11
  (undefine-all-test-predicates)
  (program '(x y)
	   '((<- (query)
	      (and (= x a) (\\= x b)))))
  (query)
  (undefine-all-test-predicates))
	   
(generate-integration-test simple-integration-test-12
  (undefine-all-test-predicates)
  (program '(x y z)
	   '((<- (f x y) (~g x y))
	     (<- (g x y) (~f x y))
	     (<- (~g x y) (g y x))
	     (g a b)
	     (<- (query) (f x y))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-13
  (undefine-all-test-predicates)
  (program '(x y z)
	   '((<- (f x y) (~g x y))
             (<- (g x y) (~f x y))
	     (<- (g x y) (~g y x))
	     (g a b)
	     (<- (query) (f x y)))
	   :traceable nil)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-14
  (undefine-all-test-predicates)
  (program '(x y z)
	   '((<- (f x y) (~g x y))
	     (<- (g x y) (~f x y) )
	     (<- (~g x y) (and (\\= x y) (g y x)))
	     ;; (<- (= x y) (and (g x y) (g y x)))
	     (g a b)
	     (<- (query) (f x y)))
	   :traceable nil)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-14a
  (undefine-all-test-predicates)
  (program '(x y z)
	   '((<- (f x y) (~g x y))
	     (<- (g x y) (~f x y))
	     (<- (~g x y) (and (\\= x y) (g y x)))
	     ;; (<- (= x y) (and (g x y) (g y x)))
	     (g a b)
	     (<- (query) (~g x y)))
	   :traceable nil)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-14b
  (undefine-all-test-predicates)
  (program '(x y z)
	   '((<- (f x y) (~g x y))
             ;; (<- (g x y) (~f x y))
	     (<- (~g x y) (and (g y x) (\\= x y)))
	     ;; (<- (= x y) (and (g x y) (g y x)))
	     (g a b)
	     (<- (query) (f x y)))
	   :traceable nil)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-14c
  (undefine-all-test-predicates)
  (program '(x y z)
	   '((<- (f x y) (~g x y))
	     ;; (<- (g x y) (~f x y))
	     (<- (g x y) (and (~g y x) (\\= x y)))
	     ;; (<- (= x y) (and (g x y) (g y x)))
	     (g a b)
	     (<- (query) (f x y)))
	   :traceable nil)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-15
  (undefine-all-test-predicates)
  (program '()
           '((f a b)
             (<- (query) (f a c))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-16
  (undefine-all-test-predicates)
  (program '()
           '((f a c)
             (f b c)
             (<- (query) (f a b))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-17
  (undefine-all-test-predicates)
  (program '(x)
           '((~some-pred a b)
             (some-pred (f x) (g x))
             (<- (query) (some-pred a b))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-18
  (undefine-all-test-predicates)
  (program '(x y)
           '((~f a b)
             (-> (~f x y) (f y x))
             (-> (f x y) (~f x y))
             (<- (query) (f x y))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-19
  (undefine-all-test-predicates)
  (program '(x y)
           '((f a b)
             (-> (~f x y) (~f y x))
             (-> (f x y) (f y x))
             (<- (query) (f x y))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-20
  (undefine-all-test-predicates)
  (program '(x y)
           '((~f a b)
             (-> (~f x y) (~f y x))
             (-> (f x y) (f y x))
             (<- (query) (~f x y))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-21
  (undefine-all-test-predicates)
  (program '(x y)
           '((f a b)
             (-> (f x y) (~f y x))
             (<- (query) (~f x y))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-22
  (undefine-all-test-predicates)
  (program '(x y)
           '((f a b)
             (-> (f x y) (~f y x))
             (-> (~f x y) (f y x))
             (<- (query) (~f x y))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test simple-integration-test-23
  (undefine-all-test-predicates)
  (program '(x y)
           '((f a b)
             (-> (f x y) (~f y x))
             (-> (~f x y) (f y x))
             (<- (query) (f x y))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test chang&lee-test-1
  (undefine-all-test-predicates)
  (program '(u v w x y z)
	   '((p (g x y) x y)
	     (p x (h x y) y)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p (k x) x (k x))) !)))
	   :incomplete-inference t)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test chang&lee-test-2
  (undefine-all-test-predicates)
  (program '(u v w x y z)
	   '((p e x x)
	     (p x e x)
	     (p x x e)
	     (p a b c)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p b a c)) !)))
	   :incomplete-inference t)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test chang&lee-test-3
  (undefine-all-test-predicates)
  (program '(u v w x y z)
	   '((p e x x)
	     (p (i x) x e)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p a e a)) !)))
	   :incomplete-inference t)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test chang&lee-test-4
  (undefine-all-test-predicates)
  (program '(u v w x y z)
	   '((p e x x)
	     (p (i x) x e)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p a x e)) !)))
	   :incomplete-inference t)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test chang&lee-test-5
  (undefine-all-test-predicates)
  (program '(u v w x y z)
	   '((p e x x)
	     (p x e x)
	     (p x (i x) e)
	     (p (i x) x e)
	     (s a)
	     (-> (and (s x) (s y) (p x (i y) z)) (s z))
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (s e)) !)))
	   :incomplete-inference t)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test chang&lee-test-6
  (undefine-all-test-predicates)
  (program '(u v w x y z)
	   '((p e x x)
	     (p x e x)
	     (p x (i x) e)
	     (p (i x) x e)
	     (s a)
	     (-> (and (s x) (s y) (p x (i y) z)) (s z))
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (s (i a))) !)))
	   :incomplete-inference t)
  (query)
  (undefine-all-test-predicates))

(generate-integration-test chang&lee-test-7
  (undefine-all-test-predicates)
  (program '(u x y z)
	   '((p a)
	     (m a (s c) (s b))
	     (m x x (s x))
	     (or (~m x y z) (m y x z))
	     (or (~m x y z) (d x z))
	     (or (~p x) (~m y z u) (~d x u) (d x y) (d x z))
	     (<- (query) (and (search (d a b)) !))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test chang&lee-test-8
  (undefine-all-test-predicates)
  (program '(x y z)
	   '((l 1 a)
	     (d x x)
	     (or (p x) (d (g x) x))
	     (or (p x) (l 1 (g x)))
	     (or (p x) (l (g x) x))
	     (or (~p x) (~d x a))		; negation of theorem
	     (or (~d x y) (~d y z) (d x z))
	     (or (~l 1 x) (~l x a) (p (f x)))
	     (or (~l 1 x) (~l x a) (d (f x) x))
	     (<- (query) (and (search (and (p x) (d x a))) !))))
  (query)
  (undefine-all-test-predicates))

(generate-integration-test chang&lee-test-9
  (undefine-all-test-predicates)
  (program '(x y)
	   '((l x (f x))
	     (~l x x)
	     (or (~l x y) (~l y x))
	     (or (~d x (f y)) (l y x))
	     (or (p x) (d (h x) x))
	     (or (p x) (p (h x)))
	     (or (p x) (l (h x) x))
	     (or (~p x) (~l a x) (l (f a) x))	; negation of theorem
	     (<- (query) (and (search (and (p x) (l a x) (~l (f a) x))) !))))
  (query)
  (undefine-all-test-predicates))
