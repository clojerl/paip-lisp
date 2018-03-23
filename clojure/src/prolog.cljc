;;;; Code from Paradigms of AI Programming
;;;; Copyright (c) 1991 Peter Norvig

;;;; File prolog.lisp: prolog from (11.3), with interactive backtracking.

(ns prolog                             ; does not require "prolog1"
  (:require [unify :as u]
            [patmatch :as p]
            [clojure.walk :as walk]
            [clojure.string :as str]))

;;;; does not include destructive unification (11.6); see prologc.lisp

(declare prove-all show-prolog-vars)

(def db-clauses
  "clauses are stored on the predicate's plist"
  (atom {:show-prolog-vars #'show-prolog-vars}))

(def db-predicates
  "a list of all predicates stored in the database."
  (atom #{}))

;; clauses are represented as (head . body) cons cells
(defn clause-head [clause] (first clause))
(defn clause-body [clause] (next clause))

;; clauses are stored on the predicate's plist
(defn get-clauses [pred] (@db-clauses pred))
(defn predicate [relation] (first relation))
(defn args "The arguments of a relation" [x] (next x))

(defn unique-find-anywhere-if
  "return a list of leaves of tree satisfying predicate,
  with duplicates removed."
  ([predicate tree]
   (unique-find-anywhere-if predicate tree #{}))
  ([predicate tree found-so-far]
   (cond
     (seq? tree)
     (unique-find-anywhere-if
      predicate
      (first tree)
      (unique-find-anywhere-if predicate (next tree)
                               found-so-far))

     (predicate tree)
     (conj found-so-far tree)

     :else found-so-far)))

(defn non-anon-variable? [x]
  (and (p/variable? x) (not (= x :?))))

(defn variables-in
  "Return a list of all the variables in EXP."
  [exp]
  (unique-find-anywhere-if non-anon-variable? exp))

(defn replace-?-vars [exp]
  "Replace any ? within exp with a var of the form ?123."
  (cond
    (= exp :?) (keyword (gensym "?"))
    (seq? exp)
    (cons (replace-?-vars (first exp))
          (replace-?-vars (next exp)))
    :else exp))

(defmacro <-
  "add a clause to the data base."
  [& clause]
  `(add-clause '~(replace-?-vars clause)))

(defn add-clause
  "add a clause to the data base, indexed by head's predicate."
  [clause]
  ;; the predicate must be a non-variable keyword.
  (let [pred (predicate (clause-head clause))]
    (assert (and (keyword? pred) (not (p/variable? pred))))
    (swap! db-predicates conj pred)
    (swap! db-clauses update-in [pred] (fnil conj []) clause)
    pred))

(defn clear-predicate
  "remove the clauses for a single predicate."
  [predicate]
  (swap! db-clauses dissoc predicate))

(defn clear-db
  "remove all clauses (for all predicates) from the data base."
  []
  (map clear-predicate @db-predicates))

(defn rename-variables
  "replace all variables in x with new ones."
  [x]
  (walk/prewalk-replace (reduce #(assoc %1 %2 (keyword (gensym (name %2))))
                                {}
                                (variables-in x))
                        x))

(defn find-anywhere-if
  "does predicate apply to any non seq in the tree?"
  [predicate tree]
  (if (seq? tree)
    (or (find-anywhere-if predicate (first tree))
        (find-anywhere-if predicate (next tree)))
    (predicate tree)))

(defn continue? []
  "Ask user if we should continue looking for solutions."
  (case (str/trimr (read-line))
    ";" true
    "." nil
    "\n" (continue?)
    (do
      (println " Type ; to see more or . to stop")
      (continue?))))

(defn prove
  "Return a list of possible solutions to goal."
  [goal bindings other-goals]
  (p/dbg :prove goal bindings other-goals)
  (let [pred    (predicate goal)
        clauses (get-clauses pred)]
    (p/dbg :prove :clauses clauses :predicate pred)
    (if (vector? clauses)
        (some
         (fn [clause]
           (p/dbg :prove :some-fn :clause clause)
           (let [new-clause (rename-variables clause)]
             (p/dbg :prove :some-fn :new-clause new-clause :bindings bindings)
             (p/dbg :prove :unify goal (clause-head new-clause) bindings
                  :result (u/unify goal (clause-head new-clause) bindings))
             (prove-all
              (concat (clause-body new-clause) other-goals)
              (u/unify goal (clause-head new-clause) bindings))))
         clauses)
        ;; The predicate's "clauses" can be an atom:
        ;; a primitive function to call
        (clauses (next goal) bindings
                 other-goals))))

(defn prove-all
  "Find a solution to the conjunction of goals."
  [goals bindings]
  (p/dbg :prove-all goals bindings)
  (cond
    (nil? bindings) nil
    (nil? goals) bindings
    :else (prove (first goals) bindings (next goals))))

(defn show-prolog-vars
  "Print each variable with its binding.
  Then ask the user if more solutions are desired."
  [vars bindings other-goals]

  (if-not vars
    (print "\nYes")
    (doseq [x vars]
      (print "\n" x " = "
             (u/subst-bindings bindings x))))
  (if (continue?)
    nil
    (prove-all other-goals bindings)))

(defn top-level-prove [goals]
  (prove-all `(~@goals (:show-prolog-vars ~@(variables-in goals)))
             {})
  (println "\nNo."))

(defmacro ?- [& goals]
  `(top-level-prove '~(replace-?-vars goals)))

;;------------------------------------------------------------------------------
;; Examples
;;------------------------------------------------------------------------------

(comment

  (<- (:member :?item (:?item & :?rest)))
  (<- (:member :?item (:?x & :?rest)) (:member :?item :?rest))

  (?- (:member 2 (1 2 3)))
  (?- (:member 2 (1 2 3 2 1)))
  (?- (:member 2 :?list))
  )

(comment

  (<- (:likes Kim Robin))
  (<- (:likes Sandy Lee))
  (<- (:likes Sandy Kim))
  (<- (:likes Robin cats))
  (<- (:likes Sandy :?x) (:likes :?x cats))
  (<- (:likes Kim :?x) (:likes :?x Lee) (:likes :?x Kim))
  (<- (:likes :?x :?x))

  (?- (:likes Sandy :?who))
  (?- (:likes :?who Sandy))
  (?- (:likes :?x :?y) (:likes :?y :?x))
  )

(comment

  )
