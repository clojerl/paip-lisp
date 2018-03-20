;;; -*- Mode: Lisp; Syntax: Common-Lisp; -*-
;;; Code from Paradigms of Artificial Intelligence Programming
;;; Copyright (c) 1991 Peter Norvig

;;;; File unify.lisp: Unification functions

(ns unify
  (:require [patmatch :refer :all]))

(def ^:dynamic *occurs-check* "Should we do the occurs check?" true)

(declare unify-variable occurs-check)

(defn unify
  "See if x and y match with given bindings."
  ([x y]
   (unify x y {}))
  ([x y bindings]
   (cond
     (nil? bindings) nil
     (= x y) bindings
     (variable? x) (unify-variable x y bindings)
     (variable? y) (unify-variable y x bindings)
     (and (seq? x) (seq? y))
     (unify (rest x) (rest y)
            (unify (first x) (first y) bindings))
     :else nil)))

(defn unify-variable
  "Unify var with x, using (and maybe extending) bindings."
  [var x bindings]
  (cond
    (bindings var)
    (unify (bindings var) x bindings)

    (and (variable? x) (bindings x))
    (unify var (bindings x) bindings)

    (and *occurs-check* (occurs-check var x bindings))
    nil

    :else (assoc bindings var x)))

(defn occurs-check
  "Does var occur anywhere inside x?"
  [var x bindings]
  (cond
    (= var x) true

    (and (variable? x) (bindings x))
    (occurs-check var (bindings x) bindings)

    (seq? x) (or (occurs-check var (first x) bindings)
                 (occurs-check var (rest x) bindings))
    :else nil))

;;; ==============================

(defn reuse-cons
  [x y x-y]
  (if (and (= x (first x-y))
           (= y (rest x-y)))
    x-y
    (cons x y)))

(defn subst-bindings
  "Substitute the value of variables in bindings into x,
  taking recursively bound variables into account."
  [bindings x]
  (cond
    (nil? bindings) nil
    (= bindings {}) x

    (and (variable? x) (bindings x))
    (subst-bindings bindings (bindings x))

    (not (seq? x)) x
    :esle (reuse-cons (subst-bindings bindings (first x))
                      (subst-bindings bindings (rest x))
                      x)))

;;; ==============================

(defn unifier
  "Return something that unifies with both x and y (or fail)."
  [x y]
  (subst-bindings (unify x y) x))

;;------------------------------------------------------------------------------
;; Examples
;;------------------------------------------------------------------------------

(comment)

(def pairs
  [['(:?x + 1) '(2 + :?y)]
   ['(:?x :?x :?x) '(:?y :?y :?y)]
   ['(:?x :?y a) '(:?y :?x :?x)]
   [':?x '(f :?x)]
   ])

(doseq [[x y] pairs]
  (println "----------------")
  (println "unify" x "-" y)
  (println "Result:" (unify x y)))

(doseq [[x y] pairs]
  (println "----------------")
  (println "unifier" x "-" y)
  (println "Result:" (unifier x y)))
