; Automatically generated by map2smt

(set-logic HORN)

(declare-datatypes ((pairOfIntInt 0) )
  (((pair-pairOfIntInt (fst-pairOfIntInt Int) (snd-pairOfIntInt Int)) )))
(declare-datatypes ((listOfpairOfIntInt 0) )
(((cons-listOfpairOfIntInt (head-listOfpairOfIntInt pairOfIntInt) (tail-listOfpairOfIntInt listOfpairOfIntInt)) (nil-listOfpairOfIntInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))



(declare-fun adt_eqlistpairs (listOfpairOfIntInt listOfpairOfIntInt Bool) Bool)
(declare-fun leq (Int Int Bool) Bool)
(declare-fun drop (Int listOfInt listOfInt) Bool)
(declare-fun zdrop (Int listOfpairOfIntInt listOfpairOfIntInt) Bool)
(declare-fun zip (listOfInt listOfInt listOfpairOfIntInt) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Bool) )
    (=>
      (= A true)
      (adt_eqlistpairs nil-listOfpairOfIntInt nil-listOfpairOfIntInt A)
    )
  )
)
(assert
  (forall ( (A pairOfIntInt) (B listOfpairOfIntInt) (C Bool) )
    (=>
      (= C false)
      (adt_eqlistpairs nil-listOfpairOfIntInt (cons-listOfpairOfIntInt A B) C)
    )
  )
)
(assert
  (forall ( (A pairOfIntInt) (B listOfpairOfIntInt) (C Bool) )
    (=>
      (= C false)
      (adt_eqlistpairs (cons-listOfpairOfIntInt A B) nil-listOfpairOfIntInt C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfpairOfIntInt) (D Int) (E Int) (F listOfpairOfIntInt) (G Bool) )
    (=>
      (and
        (= G false)
        (>= A (+ D 1))
      )
      (adt_eqlistpairs (cons-listOfpairOfIntInt (pair-pairOfIntInt A B) C) (cons-listOfpairOfIntInt (pair-pairOfIntInt D E) F) G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfpairOfIntInt) (D Int) (E Int) (F listOfpairOfIntInt) (G Bool) )
    (=>
      (and
        (= G false)
        (<= A (- D 1))
      )
      (adt_eqlistpairs (cons-listOfpairOfIntInt (pair-pairOfIntInt A B) C) (cons-listOfpairOfIntInt (pair-pairOfIntInt D E) F) G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfpairOfIntInt) (D Int) (E Int) (F listOfpairOfIntInt) (G Bool) )
    (=>
      (and
        (= G false)
        (>= B (+ E 1))
      )
      (adt_eqlistpairs (cons-listOfpairOfIntInt (pair-pairOfIntInt A B) C) (cons-listOfpairOfIntInt (pair-pairOfIntInt D E) F) G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfpairOfIntInt) (D Int) (E Int) (F listOfpairOfIntInt) (G Bool) )
    (=>
      (and
        (= G false)
        (<= B (- E 1))
      )
      (adt_eqlistpairs (cons-listOfpairOfIntInt (pair-pairOfIntInt A B) C) (cons-listOfpairOfIntInt (pair-pairOfIntInt D E) F) G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfpairOfIntInt) (D listOfpairOfIntInt) (E Bool) )
    (=>
      (adt_eqlistpairs C D E)
      (adt_eqlistpairs (cons-listOfpairOfIntInt (pair-pairOfIntInt A B) C) (cons-listOfpairOfIntInt (pair-pairOfIntInt A B) D) E)
    )
  )
)
(assert
  (forall ( (A Int) )
    (drop A nil-listOfInt nil-listOfInt)
  )
)
(assert
  (forall ( (A Int) (B listOfInt) )
    (=>
      (= A 0)
      (drop A B B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D listOfInt) (E Int) )
    (=>
      (and
        (= A (+ 1 E))
        (>= E 0)
        (drop E C D)
      )
      (drop A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) )
    (zdrop A nil-listOfpairOfIntInt nil-listOfpairOfIntInt)
  )
)
(assert
  (forall ( (A Int) (B listOfpairOfIntInt) )
    (=>
      (= A 0)
      (zdrop A B B)
    )
  )
)
(assert
  (forall ( (A Int) (B pairOfIntInt) (C listOfpairOfIntInt) (D listOfpairOfIntInt) (E Int) )
    (=>
      (and
        (= A (+ 1 E))
        (>= E 0)
        (zdrop E C D)
      )
      (zdrop A (cons-listOfpairOfIntInt B C) D)
    )
  )
)
(assert
  (forall ( (A listOfInt) )
    (zip nil-listOfInt A nil-listOfpairOfIntInt)
  )
)
(assert
  (forall ( (A listOfInt) )
    (zip A nil-listOfInt nil-listOfpairOfIntInt)
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C Int) (D listOfInt) (E listOfpairOfIntInt) )
    (=>
      (zip B D E)
      (zip (cons-listOfInt A B) (cons-listOfInt C D) (cons-listOfpairOfIntInt (pair-pairOfIntInt A C) E))
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C listOfInt) (D listOfInt) (E listOfpairOfIntInt) (F listOfpairOfIntInt) (G listOfInt) (H listOfInt) (I listOfpairOfIntInt) )
    (=>
      (and
        (>= A 0)
        (= B false)
        (zip C D E)
        (zdrop A E F)
        (drop A C G)
        (drop A D H)
        (zip G H I)
        (adt_eqlistpairs F I B)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
