;;;; Code from Paradigms of AI Programming
;;;; Copyright (c) 1991 Peter Norvig

;;;; File pat-match.lisp: Pattern matcher from section 6.2

;;; Two bug fixes By Richard Fateman, rjf@cs.berkeley.edu  October 92.

;;; The basic are in auxfns.lisp; look for "PATTERN MATCHING FACILITY"

(ns patmatch)

(def debugging false)

(defmacro dbg [& args]
  (when debugging
    `(println ~@args)))

(defn variable?
  "Is x a variable (a symbol beginning with ‘?’)?"
  [x]
  (and (keyword? x) (= "?" (-> x name first))))

(defn extend-binding
  [bindings var value]
  (assoc bindings var value))

(defn match-variable
  "Does VAR match input? Uses (or updates) and returns bindings."
  [var input bindings]
  (let [value (get bindings var)]
    (dbg "match-variable" var input value)
    (dbg "match-variable" bindings)
    (cond (nil? value) (extend-binding bindings var input)
          (= input value) bindings
          :else nil)))

(defn position [element list & {:keys [start test] :or {start 0 test =}}]
  (loop [[x & xs] (drop start list)
         pos start]
    (cond (test element x) pos
          (nil? xs) nil
          :else (recur xs (inc pos)))))

(defn subseq
  ([coll start]
   (drop start coll))
  ([coll start end]
   (->> coll (drop start) (take (- end start)))))

(def single-match? #{:is :or :and :not})
(def segment-match? #{:* :+ :? :if})

(defn segment-pattern?
  "Is this a segment-matching pattern like ((?* var) . pat)?"
  [pattern]
  (and (seq? pattern)
       (seq? (first pattern))
       (let [tag (ffirst pattern)]
         (and (keyword? tag)
              (segment-match? tag)))))

(defn single-pattern? [pattern]
  "Is this a single-matching pattern?
  E.g. (?is x predicate) (?and . patterns) (?or . patterns)."
  (and (seq? pattern)
       (single-match? (first pattern))))

(defmulti single-matcher
  "Call the right function for this kind of segment pattern."
  (fn [pattern _ _] (first pattern)))

(defmulti segment-matcher
  "Call the right function for this kind of single pattern."
  (fn [pattern _ _] (ffirst pattern)))

(defn pat-match
  "Match pattern against input in the context of the bindings"
  ([pattern input] (pat-match pattern input {}))
  ([pattern input & [bindings]]
   (dbg :pat-match
        :pattern pattern
        :input input
        :bindings bindings)
   (cond (nil? bindings)
         nil

         (variable? pattern)
         (match-variable pattern input bindings)

         (= pattern input)
         bindings

         (segment-pattern? pattern)
         (segment-matcher pattern input bindings)

         (single-pattern? pattern)
         (single-matcher pattern input bindings)

         (and (seq? pattern) (seq? input))
         (pat-match (next pattern)
                    (next input)
                    (pat-match (first pattern) (first input) bindings))

         :else nil)))

;; Succeed and bind var if the input satisfies pred,
;; where var-and-pred is the list (var pred).
(defmethod single-matcher :is [[_ & var-and-pred] input bindings]
  (let [var (first var-and-pred)
        pred (second var-and-pred)
        new-bindings (pat-match var input bindings)]
    (if (or (= new-bindings nil)
            (not (pred input)))
        nil
        new-bindings)))

;; Succeed if all the patterns match the input.
(defmethod single-matcher :and [[_ & patterns] input bindings]
  (cond (nil? bindings) nil
        (nil? patterns) bindings
        :else (recur (cons :and (rest patterns)) input
                     (pat-match (first patterns)
                                input
                                bindings))))

;; Succeed if any one of the patterns match the input.
(defmethod single-matcher :or [[_ & patterns] input bindings]
  (if-not patterns
    nil
    (let [new-bindings (pat-match (first patterns) input bindings)]
      (if-not new-bindings
        (single-matcher (cons :or (rest patterns)) input bindings)
        new-bindings))))

;; Succeed if none of the patterns match the input.
;; This will never bind any variables.
(defmethod single-matcher :not [[_ & patterns] input bindings]
  (if (single-matcher (cons :or patterns) input bindings)
    nil
    bindings))

;; (def debugging true)

(defn first-match-pos
  "Find the first position that pat1 could possibly match input,
  starting at position start.  If pat1 is non-constant, then just
  return start."
  [pattern input start]
  (dbg :first-match-pos :pattern pattern :input input :start start)
  (cond (and (not (seq? pattern)) (not (variable? pattern)))
        (position pattern input :start start :test =)

        (<= start (count input)) start ;*** fix, rjf 10/1/92 (was <)

        :else nil))

(defn segment-match
  [pattern input bindings start]
  (dbg :segment-match :pattern pattern :input input :bindings bindings)
  (let [var (second (first pattern))
        pat (next pattern)]
    (if-not pat
      (match-variable var input bindings)
      ;; We assume that pat starts with a constant
      ;; In other words, a pattern can’t have 2 consecutive vars
      (let [pos (first-match-pos (first pat) input start)]
        (if-not pos
          nil
          (let [bindings (match-variable var (subseq input 0 pos) bindings)
                b2 (pat-match pat (subseq input pos) (or bindings {}))]
            ;; If this match failed, try another longer one
            (if-not b2
              (segment-match pattern input bindings (+ pos 1))
              b2)))))))

(defmethod segment-matcher :* [pattern input bindings]
  (segment-match pattern input bindings 0))

(defmethod segment-matcher :+ [pattern input bindings]
  (dbg :+ :pattern pattern :input input :bindings bindings)
  (segment-match pattern input bindings 1))

;; Match zero or one element of input.
(defmethod segment-matcher :? [pattern input bindings]
  (let [var (second (first pattern))
        pat (rest pattern)]
    (or (pat-match (cons var pat) input bindings)
        (pat-match pat input bindings))))

(comment
  ;; Test an arbitrary expression involving variables.
  ;; The pattern looks like ((?if code) . rest).
  (defmethod segment-matcher :if [pattern input bindings]
    ;; *** fix, rjf 10/1/92 (used to eval binding values)
    (and (bindings [(mapcar #'car bindings)
                    (mapcar #'cdr bindings)]
                   (eval (second (first pattern))))
         (pat-match (rest pattern) input bindings)))

  (defn pat-match-abbrev
    "Define symbol as a macro standing for a pat-match pattern."
    [symbol expansion]
    (setf (get symbol 'expand-pat-match-abbrev)
          (expand-pat-match-abbrev expansion)))

  (defn expand-pat-match-abbrev
    "Expand out all pattern matching abbreviations in pat."
    [pat]
    (cond (and (keyword? pat) (get pat 'expand-pat-match-abbrev))
          (atom pat) pat
          :else (cons (expand-pat-match-abbrev (first pat))
                      (expand-pat-match-abbrev (rest pat)))))

  (defn rule-based-translator
    "Find the first rule in rules that matches input,
  and apply the action to that rule."
    [input rules & {:keys [matcher rule-if rule-then action]
                    :or {matcher pat-match
                         rule-if first
                         rule-then rest
                         action subseq}}]
    (some
     (fn [rule]
       (let [result (matcher (rule-if rule) input)]
         (if-not (= result fail)
           (action result (rule-then rule)))))
     rules)))

;;------------------------------------------------------------------------------
;; Examples
;;------------------------------------------------------------------------------

(comment

  (def patterns-inputs
    [['(i need a :?X) '(i need a vacation)]
     ['(i need a :?X) '(i really need a vacation)]
     ['(this is easy) '(this is easy)]
     ['(:?X is :?X) '((2 + 2) is 4)]
     ['(:?X is :?X) '((2 + 2) is (2 + 2))]
     ;; original pattern is '(:P need . :X), which is kind of cheating as well
     ['(:?P need :?X) '(i need (a long vacation))]
     ['((:* :?p) need (:* :?x)) '(Mr Hulot and I need a vacation)]
     ['((:* :?x) is a (:* :?y)) '(what he is a fool)]
     ['((:* :?x) a b (:* :?x)) '(1 2 a b a b 1 2 a b)]
     ['((:* :?x) hello (:* :?y)) '(hello)]
     ['((:+ :?x) hello (:+ :?y)) '(hello)]
     ['(hello (:+ :y)) '(hello world)]
     ['((:? :?x) hello (:+ :?y)) '(hello world)]
     ['((:+ :?x) hello (:+ :?y)) '(hey hello world)]
     ['((:+ :?x) hello (:+ :?y)) '(hey hey hey, hello world people)]
     ])

  (doseq [[p i] patterns-inputs]
    (println "----------------")
    (println "Pattern:" p)
    (println "Input:" i)
    (println "Result:" (pat-match p i))))
