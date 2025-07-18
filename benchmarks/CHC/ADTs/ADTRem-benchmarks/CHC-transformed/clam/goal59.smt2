; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new9 (Bool Int) Bool)
(declare-fun new5 (Bool Int Int Bool) Bool)
(declare-fun new2 (Int Int Bool) Bool)
(declare-fun new1 (Int Int Bool) Bool)
(declare-fun diff_new4 (Int Int Int Int Bool Bool) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Bool) (B Int) )
    (=>
      (= A false)
      (new9 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) )
    (=>
      (= A false)
      (new9 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (= A true)
      )
      (new5 A B B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (= A false)
        (>= (- B D) 1)
      )
      (new5 A B B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (= A false)
        (<= (- B D) (- 1))
      )
      (new5 A B B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) )
    (=>
      (and
        (= A false)
        (new9 C B)
      )
      (new5 A B B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D false)
        (= C false)
        (>= (- A B) 1)
      )
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D false)
        (= C false)
        (<= (- A B) (- 1))
      )
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) )
    (=>
      (and
        (= C false)
        (= B false)
      )
      (diff_new4 A A A A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D false)
        (= C false)
        (>= (- A B) 1)
      )
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D false)
        (= C false)
        (<= (- A B) (- 1))
      )
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) )
    (=>
      (and
        (= C false)
        (= B false)
      )
      (diff_new4 A A A A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C false)
        (>= (- A E) 1)
        (>= (- A E) 1)
      )
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C false)
        (<= (- A E) (- 1))
        (<= (- A E) (- 1))
      )
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (new5 C B B D)
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C false)
        (>= (- A E) 1)
        (>= (- A E) 1)
      )
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C false)
        (<= (- A E) (- 1))
        (<= (- A E) (- 1))
      )
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (diff_new4 E E B B C D)
      (diff_new4 A A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B true)
      (new2 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Bool) )
    (=>
      (and
        (diff_new4 A C D E F B)
        (new2 A A F)
      )
      (new2 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (new2 A A B)
      (new1 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Bool) )
    (=>
      (and
        (diff_new4 A C D E F B)
        (new1 A A F)
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
        (new1 B B A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
