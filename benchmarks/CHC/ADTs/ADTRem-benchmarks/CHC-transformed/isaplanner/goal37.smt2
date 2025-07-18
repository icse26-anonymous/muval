; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new2 (Bool Bool) Bool)
(declare-fun new1 (Int Int Bool) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Bool) (B Bool) )
    (=>
      (and
        (= B false)
        (= A true)
      )
      (new2 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) )
    (=>
      (and
        (= B true)
        (= A false)
      )
      (new2 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B false)
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (new1 A A B)
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) )
    (=>
      (and
        (= B true)
        (>= (- C A) 1)
        (new1 A A B)
      )
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) )
    (=>
      (and
        (= B false)
        (>= (- C A) 1)
        (>= (- C A) 1)
        (new1 A A B)
      )
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) )
    (=>
      (and
        (= B true)
        (<= (- C A) (- 1))
        (new1 A A B)
      )
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) )
    (=>
      (and
        (= B false)
        (<= (- C A) (- 1))
        (<= (- C A) (- 1))
        (new1 A A B)
      )
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) )
    (=>
      (and
        (= A false)
        (new1 B B C)
        (new2 C A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
