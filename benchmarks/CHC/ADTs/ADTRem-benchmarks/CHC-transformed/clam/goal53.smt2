; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new2 (Int Int Int) Bool)
(declare-fun new1 (Int Int Int) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= D 0)
        (= C 0)
        (= B (+ 1 D))
      )
      (new2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= C (+ 1 D))
        (= B (+ 1 E))
        (new2 A E D)
      )
      (new2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= D 0)
        (= C 0)
        (= B (+ 1 D))
      )
      (new1 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= C (+ 1 D))
        (= B (+ 1 E))
        (new1 A E D)
      )
      (new1 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (<= (- A B) 0)
        (new1 C A B)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (>= (- A B) 2)
        (new2 C A B)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
