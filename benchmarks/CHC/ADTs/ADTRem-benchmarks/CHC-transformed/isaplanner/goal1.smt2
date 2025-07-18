; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new4 (Bool) Bool)
(declare-fun new2 (Int Bool) Bool)
(declare-fun new1 (Int Int Bool) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Bool) )
    (=>
      (= A true)
      (new4 A)
    )
  )
)
(assert
  (forall ( (A Bool) )
    (=>
      (new4 A)
      (new4 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (= A 0)
      )
      (new2 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= A 0)
        (new4 B)
      )
      (new2 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (>= A 0)
      )
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (>= A 0)
        (= A 0)
      )
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (>= A 0)
        (= A 0)
        (new2 A B)
      )
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) )
    (=>
      (and
        (>= C 0)
        (>= D 0)
        (>= A 0)
        (= A (+ 1 C))
        (= A (+ 1 D))
        (new1 D C B)
      )
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) )
    (=>
      (and
        (= A false)
        (>= B 0)
        (new1 B B A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
