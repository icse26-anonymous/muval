; Automatically generated by map2smt

(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))



(declare-fun adt_new1 (listOfInt Bool) Bool)
(declare-fun leq (Int Int Bool) Bool)
(declare-fun last (listOfInt Int) Bool)
(declare-fun append (listOfInt listOfInt listOfInt) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) (B listOfInt) (C Bool) )
    (=>
      (= C false)
      (adt_new1 (cons-listOfInt A B) C)
    )
  )
)
(assert
  (forall ( (A Bool) )
    (=>
      (= A true)
      (adt_new1 nil-listOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) )
    (last (cons-listOfInt A nil-listOfInt) A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Int) )
    (=>
      (last (cons-listOfInt B C) D)
      (last (cons-listOfInt A (cons-listOfInt B C)) D)
    )
  )
)
(assert
  (forall ( (A listOfInt) )
    (append nil-listOfInt A A)
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C listOfInt) (D listOfInt) )
    (=>
      (append B C D)
      (append (cons-listOfInt A B) C (cons-listOfInt A D))
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D listOfInt) )
    (=>
      (and
        (>= (- A B) 1)
        (append C nil-listOfInt D)
        (last D B)
        (last C A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D listOfInt) )
    (=>
      (and
        (<= (- A B) (- 1))
        (append C nil-listOfInt D)
        (last D B)
        (last C A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Int) (E listOfInt) (F listOfInt) )
    (=>
      (and
        (>= (- A B) 1)
        (append C (cons-listOfInt D E) F)
        (last F B)
        (last (cons-listOfInt D E) A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Int) (E listOfInt) (F listOfInt) )
    (=>
      (and
        (<= (- A B) (- 1))
        (append C (cons-listOfInt D E) F)
        (last F B)
        (last (cons-listOfInt D E) A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
