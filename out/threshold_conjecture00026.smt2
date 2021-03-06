(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_w:A. forall B_v:B. C(B_v & A_w & ~f)

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

(declare-fun A_W () (Set Int))
(assert (subset A_W UNIVERSALSET))
(assert (>= (card A_W) (- n t)))

(declare-fun B_V () (Set Int))
(assert (subset B_V UNIVERSALSET))
(assert (> (* 2 (card B_V)) (+ n (* 3 t))))


(assert (not (> (* 2 (card (intersection B_V (intersection A_W (setminus UNIVERSALSET f))))) (- n t))))

(check-sat)
(get-model)
