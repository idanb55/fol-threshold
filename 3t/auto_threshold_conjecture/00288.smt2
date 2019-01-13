(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall B_ba:B. forall B_z:B. B_z & B_ba & ~f != EMPTYSET

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun EMPTYSET () (Set Int))
(declare-fun UNIVERSALSET () (Set Int))
(declare-fun f () (Set Int))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (subset EMPTYSET UNIVERSALSET))
(assert (= (card EMPTYSET) 0))
(assert (subset UNIVERSALSET UNIVERSALSET))
(assert (= (card UNIVERSALSET) n))
(assert (subset f UNIVERSALSET))
(assert (= (card f) t))

(declare-fun B_BA () (Set Int))
(assert (subset B_BA UNIVERSALSET))
(assert (> (* 2 (card B_BA)) (+ n (* 3 t))))

(declare-fun B_Z () (Set Int))
(assert (subset B_Z UNIVERSALSET))
(assert (> (* 2 (card B_Z)) (+ n (* 3 t))))


(assert (= (intersection (intersection B_Z B_BA) (setminus UNIVERSALSET f)) EMPTYSET))

(check-sat)
(get-model)
