; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new3 (Bool) Bool)
(declare-fun new1 (Bool) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Bool) )
    (=>
      (= A true)
      (new3 A)
    )
  )
)
(assert
  (forall ( (A Bool) )
    (=>
      (new3 A)
      (new3 A)
    )
  )
)
(assert
  (forall ( (A Bool) )
    (=>
      (= A true)
      (new1 A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= B 1)
        (= C 1)
        (>= D 1)
        (>= D 1)
        (new1 A)
      )
      (new1 A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= B 0)
        (= C 0)
        (<= D 0)
        (<= D 0)
        (new3 A)
      )
      (new1 A)
    )
  )
)
(assert
  (forall ( (A Bool) )
    (=>
      (and
        (= A false)
        (new1 A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
