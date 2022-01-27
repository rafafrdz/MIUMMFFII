; Rafael Fernandez Ortiz
; Assigment 2: Proving loop invariants

(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const ip Int)
(declare-const c Int)
(declare-const x Int)
(declare-fun len ((Array Int Int)) Int)

;pre-condition
(assert (and (<= 0 i) (<= i (len arr))))
(assert (and (<= i c) (< c (len arr)) (= (select arr c) x)))
(assert (forall ((j Int)) (=> (and (<= 0 j) (< j i)) (not (= (select arr j) x)))))
(assert (not (= (select arr i) x)))
(assert (= ip (+ i 1))) ;while

; then
(assert (not (and (<= 0 ip) (<= ip (len arr)))))
(assert (not (and (<= ip c) (< c (len arr)) (= (select arr c) x))))
(assert (not (forall ((j Int)) (=> (and (<= 0 j) (< j ip)) (not (= (select arr j) x))))))

(check-sat)
