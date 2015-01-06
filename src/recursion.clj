(ns recursion)

(defn product [coll]
  (if (empty? coll)
    1
    (* (first coll) (product (rest coll)))))

(defn singleton? [coll]
  (and (not (empty? coll)) (empty? (rest coll))))

(defn my-last [coll]
  (cond
    (empty? coll) nil
    (singleton? coll) (first coll)
    :else (my-last (rest coll))))

(defn max-element [a-seq]
  (if (empty? a-seq)
    nil
    (let [x (first a-seq)
          xs (rest a-seq)]
      (if (empty? xs)
        x
        (max-element (cons (max x (first xs)) (rest xs)))))))

(defn seq-max [seq-1 seq-2]
  (if (> (count seq-1) (count seq-2))
    seq-1
    seq-2))

(defn longest-sequence [a-seq]
  (if (empty? a-seq)
    nil
    (let [xs (first a-seq)
          xss (rest a-seq)]
      (if (empty? xss)
        xs
        (longest-sequence (cons (seq-max xs (first xss)) (rest xss)))))))

(defn my-filter [pred? a-seq]
  (if (empty? a-seq)
    '()
    (let [[x & xs] a-seq]
      (if (pred? x)
        (cons x (my-filter pred? xs))
        (my-filter pred? xs)))))

(defn sequence-contains? [elem a-seq]
  (and (not (empty? a-seq))
       (or (= elem (first a-seq))
           (sequence-contains? elem (rest a-seq)))))

(defn my-take-while [pred? a-seq]
  (if (empty? a-seq)
    '()
    (let [[x & xs] a-seq]
      (if (pred? x)
        (cons x (my-take-while pred? xs))
        '()))))

(defn my-drop-while [pred? a-seq]
  (if (empty? a-seq)
    '()
    (let [[x & xs] a-seq]
      (if (pred? x)
        (my-drop-while pred? xs)
        a-seq))))

(defn seq= [a-seq b-seq]
  (or (and (empty? a-seq) (empty? b-seq))
      (and (not (empty? a-seq)) (not (empty? b-seq))
           (= (first a-seq) (first b-seq))
           (seq= (rest a-seq) (rest b-seq)))))

(defn my-map [f seq-1 seq-2]
  (if (or (empty? seq-1) (empty? seq-2))
    '()
    (cons (f (first seq-1) (first seq-2)) (my-map f (rest seq-1) (rest seq-2)))))


(defn power [n k]
  (if (= k 0)
    1
    (* n (power n (- k 1)))))

(defn fib [n]
  (if (< n 2)
    n
    (+ (fib (- n 1)) (fib (- n 2)))))

(defn my-repeat [how-many-times what-to-repeat]
  (if (<= how-many-times 0)
    '()
    (cons what-to-repeat (my-repeat (dec how-many-times) what-to-repeat))))

(defn my-range [up-to]
  (if (<= up-to 0)
    '()
    (let [n (dec up-to)]
      (cons n (my-range n)))))

(defn tails [a-seq]
  (if (empty? a-seq)
    '(())
    (cons (seq a-seq) (tails (rest a-seq)))))

(defn inits [a-seq]
  (if (empty? a-seq)
    '(())
    (let [x (first a-seq) xs (inits (rest a-seq))]
      (cons '() (map #(cons x %) xs)))))

(defn insert [x xs n]
  (cond
    (empty? xs) (list x)
    (= n 0) (cons x xs)
    :else (let [[y & ys] xs]
            (cons y (insert x ys (dec n))))))

(defn rotations [a-seq]
  (if (empty? a-seq) 
    '(())
    (let [x (first a-seq) 
          xss (rotations (rest a-seq))
          xs (first xss)
          n (dec (count a-seq))]
      (letfn [(insert-at [ys i] (insert x ys i))]
        (cons a-seq (map insert-at xss (range n 0 (- 1))))))))


(defn my-frequencies-helper [freqs a-seq]
  (if (empty? a-seq)
    freqs
    (let [x (first a-seq)
          xs (rest a-seq)
          c (get freqs x 0)]
      (my-frequencies-helper (assoc freqs x (inc c)) (rest a-seq)))))

(defn my-frequencies [a-seq]
  (my-frequencies-helper {} a-seq))

(defn un-frequencies [a-map]
  (if (empty? a-map)
    '()
    (let [[k v] (first a-map)]
      (concat (repeat v k) (un-frequencies (rest a-map))))))

(defn my-take [n coll]
  (cond
    (<= n 0) '()
    (>= n (count coll)) coll
    :else (cons (first coll) (my-take (dec n) (rest coll)))))

(defn my-drop [n coll]
  (if (= n 0)
    coll
    (my-drop (dec n) (rest coll))))

(defn halve [a-seq]
  (let [n (int (/ (count a-seq) 2))]
    [(my-take n a-seq) (my-drop n a-seq)]))

(defn seq-merge [a-seq b-seq]
  (cond
    (empty? a-seq) b-seq
    (empty? b-seq) a-seq
    :else (let [[x & xs] a-seq
                [y & ys] b-seq]
            (if (<= x y)
              (cons x (seq-merge xs b-seq))
              (cons y (seq-merge a-seq ys))))))

(defn merge-sort [a-seq]
  (if (< (count a-seq) 2)
    a-seq
    (->> a-seq (halve) (map merge-sort) (apply seq-merge))))

(defn split-into-monotonics [a-seq]
  (letfn [(tbd [a [[b & _ :as xs] & xss]]
            (cond
              (empty? xs) [tbd (list (list a))]
              (= a b) [tbd  (conj xss (conj xs a))]
              (< a b) [incr (conj xss (conj xs a))]
              (> a b) [decr (conj xss (conj xs a))]))
          (incr [a [[b & _ :as xs] & xss :as acc]]
            (if (<= a b) 
              [incr (conj xss (conj xs a))]
              [tbd (conj acc (list a))]))
          (decr [a [[b & _ :as xs] & xss :as acc]]
            (if (>= a b)
              [decr (conj xss (conj xs a))]
              [tbd (conj acc (list a))]))
          (split [state-fn xs acc]
            (if (empty? xs)
              (reverse (map reverse acc))
              (let [[next-fn xss] (state-fn (first xs) acc)]
                (split next-fn (rest xs) xss))))]
    (split tbd a-seq '(()))))

(defn permutations [a-set]
  (if (empty? a-set)
    '(())
    (let [[x & xs] a-set
          xss (permutations xs)]
      (->> (range (count a-set))
           (map (fn [n] (map #(insert x % n) xss)))
           (apply concat)))))

(defn powerset [a-set]
  (if (empty? a-set)
    #{#{}}
    (let [x (first a-set)
          xs (rest a-set)
          xss (powerset xs)]
      (reduce (fn [acc ys] (conj acc (conj ys x))) xss xss))))

