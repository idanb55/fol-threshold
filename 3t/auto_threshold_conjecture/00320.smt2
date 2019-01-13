(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall B_bc:B. forall C_bb:C. C_bb & B_bc & ~f != EMPTYSET

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

(declare-fun B_BC () (Set Int))
(assert (subset B_BC UNIVERSALSET))
(assert (> (* 2 (card B_BC)) (+ n (* 3 t))))

(declare-fun C_BB () (Set Int))
(assert (subset C_BB UNIVERSALSET))
(assert (> (* 2 (card C_BB)) (- n t)))


(assert (= (intersection (intersection C_BB B_BC) (setminus UNIVERSALSET f)) EMPTYSET))

(check-sat)
(get-model)
