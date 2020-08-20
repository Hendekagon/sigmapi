(ns sigmapi.test.core
  (:require
    [clojure.test :refer [deftest testing is]]
    [sigmapi.core :as sp :refer [fgtree >alg propagate-cycles propagate print-msgs msg-diff
                                 marginals exp->fg msgs-from-leaves message-passing ln- P
                                 normalize random-matrix MAP-config combine can-message?
                                 update-factors]]
    [clojure.core.matrix :as m]
    [loom.graph :as lg]
    [loom.alg :as la]
    [clojure.string :as string]))

(defn e= [e x y] (< (Math/abs (- x y)) e))

(defn figure7
  "Figure 7 in Frey2001 Factor graphs and the sum product algorithm"
  ([]
   {
    :fg
    (fgtree
      [:fc
       [
        [[0.3 0.3 0.3 0.1] [0.3 0.3 0.3 0.1] [0.3 0.3 0.3 0.1]]
        [[0.3 0.3 0.3 0.1] [0.3 0.3 0.3 0.1] [0.3 0.3 0.3 0.1]]
        ]
       (:x1 [:fa [0.1 0.9]])
       (:x2 [:fb [0.2 0.7 0.1]])
       (:x3
         [:fd
          [
           [0.4 0.6]
           [0.6 0.4]
           [0.4 0.6]
           [0.6 0.4]
           ]
          (:x4)]
         [:fe
          [
           [0.5 0.5]
           [0.5 0.5]
           [0.5 0.5]
           [0.5 0.5]
           ]
          (:x5)])])

      :priors {:x1 :fa :x2 :fb}
      }))

(defn test-cbt []
  (let
    [
     s [2 3 4 5]
     f (m/new-array s)
     g (fn ([mat v] (m/add mat v)) ([mat] mat))
     vs (map (fn [d] (m/matrix (repeat d d))) s)
     dfn (into {} (map vector s (range (count s))))
     to 2
     msgs (map (fn [v i] {:value v :id i}) vs s)
     ; do them out-of-order in as messages may not come in dimension order
     reordered-msgs (mapcat (fn [[a b]] [b a]) (partition-all 2 msgs))
     sum (combine f g reordered-msgs to dfn)
     ]
    sum))

; combine-by-tranz [f g messages to dim-for-node]
(deftest test-combine-by-tranz
  (testing "That adding a sequence of vectors containing the value of their length
  to a matrix of the same shape as the sequence of vectors results in a matrix having
  every value equal to the sum of its dimensions"
    (is (m/equals (test-cbt) (m/fill (m/new-array [2 3 4 5]) (reduce + [2 3 4 5]))))))

(defn t0 []
  (fgtree
      (:x1
        [:px1 [0.3 0.3 0.3]]
        [:x1x2
         [
           [0.1 0.8]
           [0.8 0.1]
           [0.1 0.1]
         ]
         (:x2 [:px2 [0.1 0.9]])]
        [:x1x3
         [
           [0.1 0.1 0.8 0.1]
           [0.1 0.8 0.1 0.1]
           [0.8 0.1 0.1 0.8]
         ]
         (:x3 [:px3 [0.1 0.7 0.1 0.1]])])))

(defn t0x []
  (fgtree
      (:x1
        [3]
        [:x1x2 []
         (:x2 [2])]
        [:x1x3 []
         (:x3 [4])])))

(defn t00 []
  '(:x3 [3]
    [:x3x4 []
     (:x4 [4]
       [:x4x5x6 []
         (:x5 [5])
         (:x6 [6])])]
    [:x3x2 []
     (:x2 [2])]))

(defn test-max-configuration
  "That a simple graph (a branch, x2->x1<-x3) returns max config"
  []
  (->>
    (t0)
    (exp->fg :max)
    propagate
    MAP-config))

(defn t1 []
  (->>
      (fgtree
        (:x1
          [:x1x2
           [
            [0.1 0.2 0.7]
            [0.6 0.2 0.2]
            ]
           (:x2 [0.2 0.8])]
          [:x1x3
           [
            [0.5 0.1 0.4]
            [0.8 0.1 0.1]
            ]
           (:x3 [0.3 0.6 0.1])]))
        (exp->fg :sp)
        propagate
        marginals
       ))




(defn MHP
  "
     Suppose you're on a game show,
     and you're given the choice of three doors:
     Behind one door is a car;
     behind the others, goats.
     You pick a door, say No. 1,
     and the host, who knows what's behind the doors,
     opens another door, say No. 3, which has a goat.
     He then says to you,
     'Do you want to pick door No. 2?'
     Is it to your advantage to switch your choice ?

     (MHP {:correct-door 2 :choose-door 0})
  "
  [{door-number :correct-door choose-door-number :choose-door dp :dp cp :cp}]
  (let
    [model
     {:fg (fgtree
       (host's-choice
         [host's-choice|your-1st-choice
          [
           [0 1/2 1/2]
           [1/2 0 1/2]
           [1/2 1/2 0]
           ]
          (your-1st-choice
            [prize|your-1st-choice&door
             [
              [[0 1] [1 0] [1 0]]
              [[1 0] [0 1] [1 0]]
              [[1 0] [1 0] [0 1]]
              ]
             (door-0 [p-door-0 [1/3 1/3 1/3]])
             (prize-0)]
            [p-your-1st-choice [1/3 1/3 1/3]])]
         [host's-choice|door
          [
           [0 1/2 1/2]
           [1/2 0 1/2]
           [1/2 1/2 0]
           ]
          (door [p-door [1/3 1/3 1/3]])]
         [your-2nd-choice|host's-choice
          [
           [0 1/2 1/2]
           [1/2 0 1/2]
           [1/2 1/2 0]
           ]
          (your-2nd-choice
            [your-2nd-choice|your-1st-choice
             [
              [0 1/2 1/2]
              [1/2 0 1/2]
              [1/2 1/2 0]
              ]
             (your-1st-choice-0 [p-your-1st-choice-0 [1/3 1/3 1/3]])]
            [prize|your-2nd-choice&door
             [
              [[0 1] [1 0] [1 0]]
              [[1 0] [0 1] [1 0]]
              [[1 0] [1 0] [0 1]]
              ]
             (door-1 [p-door-1 [1/3 1/3 1/3]])
             (prize-1)])]))
      :priors
      {:door :p-door
       :door-0 :p-door-0
       :door-1 :p-door-1
       :your-1st-choice :p-your-1st-choice
       :your-1st-choice-0 :p-your-1st-choice-0}}
     door (or dp (assoc [0 0 0] door-number 1))
     choice (or cp (assoc [0 0 0] choose-door-number 1))
     {m1 :marginals l :learned :as em0}
       (-> model (assoc :data {:p-door door :p-door-0 door :p-door-1 door :p-your-1st-choice choice :p-your-1st-choice-0 choice}) sp/learn-step)
      m2
       (-> l (>alg :max) propagate MAP-config)
     ]
    {
     :marginals (select-keys m1 [:door :prize-0 :prize-1 :your-1st-choice :host's-choice :your-2nd-choice])
     :configuration m2
     :model l
     :message
     (string/join "\n"
       [
        ""
        (apply str " car is      " (assoc '[🚪 🚪 🚪] (:door m2) '🚗))
        (apply str " you chose   " (assoc '[🚪 🚪 🚪] (:your-1st-choice m2) '🀆))
        (apply str " host opened " (assoc '[🚪 🚪 🚪] (:host's-choice m2) '🐐))
        (apply str " you chose   " (assoc '[🚪 🚪 🚪] (:your-2nd-choice m2) '🀆 (:host's-choice m2) '🐐))
        (apply str "             " (assoc '[🐐 🐐 🐐] (:your-2nd-choice m2) '🀆 (:door m2) '🚗))
        ""
        (str
          (if (== 1 (:prize-1 m2)) " you won! " " you lost ")
          (if (== 1 (:prize-1 m2)) '🚗 '🐐))
        ""
        (str " had you stuck with your first choice you would have " (if (== 1 (:prize-0 m2)) "won" "lost"))
        ""
        ])
     }
    ))

(defn MHP1
  "

  "
  []
  (sp/with-random-factors :sp (fgtree
     (host's-choice [3]
       [host's-choice|your-1st-choice
        []
        (your-1st-choice [3]
          [prize|your-1st-choice&door
           []
           (door-0 [3])
           (prize-0 [2])])]
       [host's-choice|door
        []
        (door [3])]
       [your-2nd-choice|host's-choice
        []
        (your-2nd-choice [3]
          [your-2nd-choice|your-1st-choice
           []
           (your-1st-choice-0 [3])]
          [prize|your-2nd-choice&door
           []
           (door-1 [3])
           (prize-1 [2])])]))))

(defn test-Bayesian-updating
  "
   An example from
   https://ocw.mit.edu/courses/mathematics/18-05-introduction-to-probability-and-statistics-spring-2014/readings/MIT18_05S14_Reading11.pdf
  "
  []
  (let
    [model
     {:fg
      (sp/fgtree
        (:d [:pd [0.5 0.5]]
          [:d|h
           [
            [0.5 0.4 0.1]
            [0.5 0.6 0.9]
            ]
           (:h [:ph [0.4 0.4 0.2]])
           ]))
      :priors
      {:h :ph :d :pd}}
     experiment
       (assoc model :data
         [
          {:pd [0 1]}
          {:pd [0 1]}
          ])
       {h :h} (-> experiment sp/learned-variables :marginals)
       expected [0.2463 0.3547 0.3990]
       result (map (fn [hv ev] [hv ev (e= 10e-5 hv ev)]) h expected)
     ]
     {
       :expected expected
       :result h
       :pass? (every? true? (map last result))
       :experiment experiment
     }))