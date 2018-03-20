;;;; -*- Mode: Lisp; Syntax: Common-Lisp -*-
;;;; Code from Paradigms of AI Programming
;;;; Copyright (c) 1991 Peter Norvig

;;;; File prolog.lisp: prolog from (11.3), with interactive backtracking.

(ns prolog                             ; does not require "prolog1"
  (:require [unify :refer :all]
            [patmatch :refer :all]))

;;;; does not include destructive unification (11.6); see prologc.lisp

(declare replace-?-vars variables-in prove)

(def clauses
  "clauses are stored on the predicate's plist"
  (atom {}))

(def db-predicates
  "a list of all predicates stored in the database."
  (atom #{}))

;; clauses are represented as (head . body) cons cells
(defn clause-head [clause] (first clause))
(defn clause-body [clause] (rest clause))

;; clauses are stored on the predicate's plist
(defn get-clauses [pred] (@clauses pred))
(defn predicate [relation] (first relation))
(defn args "The arguments of a relation" [x] (rest x))

(defmacro <-clause
  "add a clause to the data base."
  [& clause]
  `(add-clause ~(replace-?-vars clause)))

(defn add-clause
  "add a clause to the data base, indexed by head's predicate."
  [clause]
  ;; the predicate must be a non-variable symbol.
  (let [pred (predicate (clause-head clause))]
    (assert (and (keyword? pred) (not (variable? pred))))
    (swap! db-predicates conj pred)
    (swap! clauses update-in [pred] conj clause)
    pred))

(defn clear-predicate
  "remove the clauses for a single predicate."
  [predicate]
  (swap! clauses dissoc predicate))

(defn clear-db
  "remove all clauses (for all predicates) from the data base."
  []
  (map clear-predicate @db-predicates))

(defn rename-variables
  "replace all variables in x with new ones."
  [x]
  (replace (reduce #(assoc %1 %2 (gensym (str %2)))
                   {}
                   (variables-in x))
           x))

(defn unique-find-anywhere-if
  "return a list of leaves of tree satisfying predicate,
  with duplicates removed."
  ([predicate tree]
   (unique-find-anywhere-if predicate tree #{}))
  ([predicate tree found-so-far]
   (if (atom tree)
     (if (predicate tree)
       (conj tree found-so-far)
       found-so-far)
     (unique-find-anywhere-if
      predicate
      (first tree)
      (unique-find-anywhere-if predicate (rest tree)
                               found-so-far)))))

(defn find-anywhere-if
  "does predicate apply to any atom in the tree?"
  [predicate tree]
  (if (not (seq? tree))
      (predicate tree)
      (or (find-anywhere-if predicate (first tree))
          (find-anywhere-if predicate (rest tree)))))

(defmacro ?- [& goals]
  `(top-level-prove ~(replace-?-vars goals)))

(defn prove-all
  "Find a solution to the conjunction of goals."
  [goals bindings]
  (cond
    (nil? bindings) nil
    (nil? goals) bindings
    :else (prove (first goals) bindings (rest goals))))

(defn prove
  "Return a list of possible solutions to goal."
  [goal bindings other-goals]
  (let [clauses (get-clauses (predicate goal))]
    (if (seq? clauses)
        (some
         (fn [clause]
           (let [new-clause (rename-variables clause)]
             (prove-all
              (conj (clause-body new-clause) other-goals)
              (unify goal (clause-head new-clause) bindings))))
         clauses)
        ;; The predicate's "clauses" can be an atom:
        ;; a primitive function to call
        (clauses (rest goal) bindings
                 other-goals))))

(defn top-level-prove [goals]
  (prove-all `(~@goals (show-prolog-vars ~@(variables-in goals)))
             {})
  (println "No.")
  @clauses)

(defn continue? []
  "Ask user if we should continue looking for solutions."
  (case (read)
    ";" true
    "." nil
    "\n" (continue?)
    (do
      (println " Type ; to see more or . to stop")
      (continue?))))

(defn show-prolog-vars
  "Print each variable with its binding.
  Then ask the user if more solutions are desired."
  [vars bindings other-goals]

  (if-not vars
    (println "Yes")
    (doseq [x vars]
            (println x " = "
                     (subst-bindings bindings x))))
  (if (continue?)
      nil
      (prove-all other-goals bindings)))

;; (setf (get 'show-prolog-vars 'clauses) 'show-prolog-vars)

(defn non-anon-variable? [x]
  (and (variable? x) (not (= x :?))))

(defn variables-in
  "Return a list of all the variables in EXP."
  [exp]
  (unique-find-anywhere-if non-anon-variable? exp))

(defn replace-?-vars [exp]
  "Replace any ? within exp with a var of the form ?123."
  (cond
    (= exp :?) (gensym "?")
    (not (seq? exp)) exp
    :else (reuse-cons (replace-?-vars (first exp))
                      (replace-?-vars (rest exp))
                      exp)))
