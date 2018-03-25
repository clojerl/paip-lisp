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

    (and (seq? exp) (seq exp))
    (cons (replace-?-vars (first exp))
          (replace-?-vars (next exp)))

    :else exp))

(defmacro <-
  "add a clause to the data base."
  [& clause]
  (p/dbg :<- clause)
  `(add-clause '~(replace-?-vars clause)))

(defn add-clause
  "add a clause to the data base, indexed by head's predicate."
  [clause]
  ;; the predicate must be a non-variable keyword.
  (p/dbg :add-clause clause)
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

#_(defn find-anywhere-if
  "does predicate apply to any non seq in the tree?"
  [predicate tree]
  (if (and (seq? tree) #_(not (empty? tree)))
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
  (p/dbg :prove :goal goal :bindings bindings :other-goals other-goals)
  (let [pred    (predicate goal)
        clauses (or  (get-clauses pred) [])]
    (p/dbg :prove :clauses clauses :predicate pred)
    (if (vector? clauses)
      (some
       (fn [clause]
         (p/dbg :prove :some-fn :clause clause)
         (let [new-clause (rename-variables clause)
               unification (u/unify goal (clause-head new-clause) bindings)]
           (p/dbg :prove :some-fn :new-clause new-clause :bindings bindings)
           (p/dbg :prove :some-fn :unify goal (clause-head new-clause) bindings
                  :result unification )
           (prove-all
            (concat (clause-body new-clause) other-goals)
            unification)))
       clauses)
      ;; The predicate's "clauses" can be an atom:
      ;; a primitive function to call
      (clauses (next goal) bindings
               other-goals))))

(defn prove-all
  "Find a solution to the conjunction of goals."
  [goals bindings]
  (p/dbg :prove-all :goal goals :bindings bindings)
  (cond
    (nil? bindings) nil
    (nil? goals) bindings
    :else (prove (first goals) bindings (next goals))))

(defn show-prolog-vars
  "Print each variable with its binding.
  Then ask the user if more solutions are desired."
  [vars bindings other-goals]
  (p/dbg :show-prolog-vars :vars vars :bindings bindings :other-goals other-goals)
  (if-not vars
    (print "\nYes")
    (doseq [x vars]
      (print "\n" x " = "
             (u/subst-bindings bindings x))))
  (flush)
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

  (?- (:member 4 (1 2 3)))
  (?- (:member 2 (1 2 3)))
  (?- (:member 2 (1 2 3 2 1)))
  (?- (:member 2 :?list))
  (?- (:member :?x (1 2 3))))

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
  (?- (:likes :?x :?y) (:likes :?y :?x)))

(comment

  (<- (:length () 0))
  (<- (:length (:?x & :?y) (1 + :?n)) (:length :?y :?n))

  (?- (:length (a b c d) :?n))
  (?- (:length :?list (1 + (1 + 0))))
  (?- (:length :?list :?n))
  )

(comment

  (<- (:member :?item (:?item & :?rest)))
  (<- (:member :?item (:?x & :?rest)) (:member :?item :?rest))
  (<- (:nextto :?x :?y :?list) (:iright :?y :?x :?list))
  (<- (:nextto :?x :?y :?list) (:iright :?x :?y :?list))
  (<- (:iright :?left :?right (:?left :?right & :?rest)))
  (<- (:iright :?left :?right (:?x & :?rest))
      (:iright :?left :?right :?rest))
  (<- (:= :?x :?x))

  (<- (:zebra :?h :?w :?z)

      ;; Each house is of the form:
      ;; (house nationality pet cigarette drink house-color)
      (:= :?h ((house norwegian :? :? :? :?)                 ;1,10
               :?
               (house :? :? :? milk :?) :? :?))              ; 9
      (:member (house englishman :? :? :? red) :?h)          ; 2
      (:member (house spaniard dog :? :? :?) :?h)            ; 3
      (:member (house :? :? :? coffee green) :?h)            ; 4
      (:member (house ukrainian :? :? tea :?) :?h)           ; 5
      (:iright (house :? :? :? :? ivory)                     ; 6
               (house :? :? :? :? green) :?h)
      (:member (house :? snails winston :? :?) :?h)          ; 7
      (:member (house :? :? kools :? yellow) :?h)            ; 8
      (:nextto (house :? :? chesterfield :? :?)              ;11
               (house :? fox :? :? :?) :?h)
      (:nextto (house :? :? kools :? :?)                     ;12
               (house :? horse :? :? :?) :?h)
      (:member (house :? :? luckystrike orange-juice :?) :?h);13
      (:member (house japanese :? parliaments :? :?) :?h)    ;14
      (:nextto (house norwegian :? :? :? :?)                 ;15
               (house :? :? :? :? blue) :?h)
      ;; Now for the questions:
      (:member (house :?w :? :? water :?) :?h)                ;Q1
      (:member (house :?z zebra :? :? :?) :?h))               ;Q2

  (?- (:zebra :?houses :?water-drinker :?zebra-owner))
  )
