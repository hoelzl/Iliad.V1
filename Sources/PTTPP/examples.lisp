;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 1986 Mark E. Stickel, SRI International, Menlo Park,
;;; CA 94025 USA
;;;
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

(in-package #:pttpp)

(defun chang&lee-examples ()
  (print 'chang&lee-examples)
  (chang&lee-example-1)
  (chang&lee-example-2)
  (chang&lee-example-3)
  (chang&lee-example-4)
  (chang&lee-example-5)
  (chang&lee-example-6)
  (chang&lee-example-7)
  (chang&lee-example-8)
  (chang&lee-example-9))

(defun chang&lee-example-1 nil
  (print 'chang&lee-example-1)
  (format t "~&Prove that in an associative system with left and right solutions,~%there is a right identity element.")
  (program '(u v w x y z)
	   '((p (g x y) x y)
	     (p x (h x y) y)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p (k x) x (k x))) !)))
	   :incomplete-inference t)
  (query))

(defun chang&lee-example-2 nil
  (print 'chang&lee-example-2)
  (format t "~&In an associative system with an identity element, if the square~%of every element is the identity, the system~%is commutative.")
  (program '(u v w x y z)
	   '((p e x x)
	     (p x e x)
	     (p x x e)
	     (p a b c)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p b a c)) !)))
	   :incomplete-inference t)
  (query))

(defun chang&lee-example-3 nil
  (print 'chang&lee-example-3)
  (format t "~&In a group the left identity element is also a right identity.")
  (program '(u v w x y z)
	   '((p e x x)
	     (p (i x) x e)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p a e a)) !)))
	   :incomplete-inference t)
  (query))

(defun chang&lee-example-4 nil
  (print 'chang&lee-example-4)
  (format t "~&In a group with left inverse and left identity every element~%has a right inverse.")
  (program '(u v w x y z)
	   '((p e x x)
	     (p (i x) x e)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p a x e)) !)))
	   :incomplete-inference t)
  (query))

(defun chang&lee-example-5 nil
  (print 'chang&lee-example-5)
  (format t "~&If S is a nonempty subset of a group such that if x,y belong to S,~%then x*y^-1 belongs to S, then the identity e belongs to S.")
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
  (query))

(defun chang&lee-example-6 nil
  (print 'chang&lee-example-6)
  (format t "~&If S is a nonempty subset of a group such that if x,y belong to S,~%then x*y^-1 belongs to S, then S contains x^-1 whenever it contains x.")
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
  (query))

(defun chang&lee-example-7 nil
  (print 'chang&lee-example-7)
  (format t "~&If a is a prime and a = b^2/c^2 then a divides b.")
  (program '(u x y z)
	   '((p a)
	     (m a (s c) (s b))
	     (m x x (s x))
	     (or (~m x y z) (m y x z))
	     (or (~m x y z) (d x z))
	     (or (~p x) (~m y z u) (~d x u) (d x y) (d x z))
	     (<- (query) (and (search (d a b)) !))))
  (query))

(defun chang&lee-example-8 nil
  (print 'chang&lee-example-8)
  (format t "~&Any number greater than 1 has a prime divisor.")
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
  (query))

(defun chang&lee-example-9 nil
  (print 'chang&lee-example-9)
  (format t "~&There exist infinitely many primes.")
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
  (query))

