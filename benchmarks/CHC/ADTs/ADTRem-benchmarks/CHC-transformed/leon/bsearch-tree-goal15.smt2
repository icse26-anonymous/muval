; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new9 (Int Bool) Bool)
(declare-fun new63 (Int Bool Int Bool) Bool)
(declare-fun new2 (Int Int Bool) Bool)
(declare-fun new15 (Int Int Bool) Bool)
(declare-fun new11 (Int Int Bool) Bool)
(declare-fun new10 (Int Int Bool) Bool)
(declare-fun new1 (Int Bool Int Bool) Bool)
(declare-fun diff_new54 (Int Int Int Bool Bool) Bool)
(declare-fun diff_new4 (Int Int Bool Int Bool) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D false)
        (= B false)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) )
    (=>
      (and
        (= C true)
        (= B true)
      )
      (new63 A B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (new9 C D)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (new9 C D)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D false)
        (= B true)
        (>= (- C A) 1)
        (new9 C D)
        (new9 C D)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D false)
        (= B true)
        (<= (- C A) (- 1))
        (new9 C D)
        (new9 C D)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (new63 C D A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (new9 C D)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B true)
        (>= (- C E) 1)
        (new63 C D A B)
        (new9 C D)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B true)
        (<= (- C E) (- 1))
        (new63 C D A B)
        (new9 C D)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (new9 C D)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (new63 C D A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B true)
        (>= (- C E) 1)
        (new9 C D)
        (new63 C D A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B true)
        (<= (- C E) (- 1))
        (new9 C D)
        (new63 C D A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B false)
        (>= (- A C) 1)
        (new9 A B)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B false)
        (>= (- A E) 1)
        (new63 C D A B)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B false)
        (>= (- A E) 1)
        (new63 C D A B)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B false)
        (>= (- C E) 1)
        (>= (- A E) 1)
        (new63 C D A B)
        (new63 C D A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B false)
        (>= (- A E) 1)
        (<= (- C E) (- 1))
        (new63 C D A B)
        (new63 C D A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B false)
        (<= (- A C) (- 1))
        (new9 A B)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B false)
        (<= (- A E) (- 1))
        (new63 C D A B)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B false)
        (<= (- A E) (- 1))
        (new63 C D A B)
        (new9 A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B false)
        (>= (- C E) 1)
        (<= (- A E) (- 1))
        (new63 C D A B)
        (new63 C D A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B false)
        (<= (- C E) (- 1))
        (<= (- A E) (- 1))
        (new63 C D A B)
        (new63 C D A B)
      )
      (new63 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (= C false)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (= C true)
        (<= B (- A 1))
        (new9 A D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (= C true)
        (<= B (- A 1))
        (new11 A A D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D false)
        (= C true)
        (>= (- A B) 1)
        (<= B (- A 1))
        (new11 A A D)
        (new9 A D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) )
    (=>
      (and
        (= C true)
        (= B true)
        (>= A A)
      )
      (diff_new54 A A A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (= C true)
        (>= B A)
        (new11 A A D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (= C true)
        (>= B A)
        (new9 A D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D false)
        (= C true)
        (>= B A)
        (<= (- A B) (- 1))
        (new11 A A D)
        (new9 A D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C true)
        (<= E (- A 1))
        (new63 A D B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C true)
        (<= E (- A 1))
        (new11 A A D)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C true)
        (>= (- A E) 1)
        (<= E (- A 1))
        (new11 A A D)
        (new63 A D B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (= C true)
        (>= A A)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C true)
        (>= E A)
        (diff_new54 A A B C D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C true)
        (>= E A)
        (new9 A D)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C true)
        (>= E A)
        (<= (- A E) (- 1))
        (diff_new54 A A B C D)
        (new9 A D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C true)
        (<= E (- A 1))
        (new9 A D)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C true)
        (<= E (- A 1))
        (diff_new54 A A B C D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C true)
        (>= (- A E) 1)
        (<= E (- A 1))
        (diff_new54 A A B C D)
        (new9 A D)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (= C true)
        (>= A A)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C true)
        (>= E A)
        (new11 A A D)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C true)
        (>= E A)
        (new63 A D B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C true)
        (>= E A)
        (<= (- A E) (- 1))
        (new11 A A D)
        (new63 A D B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C false)
        (>= (- B E) 1)
        (<= E (- A 1))
        (new63 A D B C)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C false)
        (>= (- B E) 1)
        (<= E (- A 1))
        (diff_new54 A A B C D)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C false)
        (>= (- B E) 1)
        (>= (- A E) 1)
        (<= E (- A 1))
        (diff_new54 A A B C D)
        (new63 A D B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (= C false)
        (>= (- B A) 1)
        (>= A A)
        (new9 B C)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C false)
        (>= (- B E) 1)
        (>= E A)
        (diff_new54 A A B C D)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C false)
        (>= (- B E) 1)
        (>= E A)
        (new63 A D B C)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C false)
        (>= (- B E) 1)
        (>= E A)
        (<= (- A E) (- 1))
        (diff_new54 A A B C D)
        (new63 A D B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C false)
        (<= (- B E) (- 1))
        (<= E (- A 1))
        (new63 A D B C)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C false)
        (<= (- B E) (- 1))
        (<= E (- A 1))
        (diff_new54 A A B C D)
        (new9 B C)
      )
      (diff_new54 A A B C D)
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
        (<= (- B E) (- 1))
        (<= E (- A 1))
        (diff_new54 A A B C D)
        (new63 A D B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (= C false)
        (>= A A)
        (<= (- B A) (- 1))
        (new9 B C)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C false)
        (>= E A)
        (<= (- B E) (- 1))
        (diff_new54 A A B C D)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= C false)
        (>= E A)
        (<= (- B E) (- 1))
        (new63 A D B C)
        (new9 B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C false)
        (>= E A)
        (<= (- B E) (- 1))
        (<= (- A E) (- 1))
        (diff_new54 A A B C D)
        (new63 A D B C)
      )
      (diff_new54 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B true)
      (new15 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C false)
        (= C false)
        (= C false)
        (>= (- B A) 1)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C false)
        (= C false)
        (= C false)
        (<= (- B A) (- 1))
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (<= B (- A 1))
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (<= D (- A 1))
        (new9 B C)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (<= D (- A 1))
        (new15 A B C)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (>= (- B D) 1)
        (<= D (- A 1))
        (new9 B C)
        (new15 A B C)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (<= (- B D) (- 1))
        (<= D (- A 1))
        (new9 B C)
        (new10 A B C)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (>= B A)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (>= D A)
        (new15 A B C)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (>= D A)
        (new9 B C)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (>= (- B D) 1)
        (>= D A)
        (new11 A B C)
        (new9 B C)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (>= D A)
        (<= (- B D) (- 1))
        (new15 A B C)
        (new9 B C)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (<= (- A A) 0)
      )
      (new11 A A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C false)
        (= C false)
        (= C false)
        (>= (- B A) 1)
        (<= (- A B) 0)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (<= (- A B) 0)
        (<= D (- A 1))
        (new9 B C)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (<= (- A B) 0)
        (<= D (- A 1))
        (new11 A B C)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (>= (- B D) 1)
        (<= (- A B) 0)
        (<= D (- A 1))
        (new9 B C)
        (new11 A B C)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (>= B A)
        (<= (- A B) 0)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (>= D A)
        (<= (- A B) 0)
        (new11 A B C)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (>= D A)
        (<= (- A B) 0)
        (new9 B C)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (>= (- B D) 1)
        (>= D A)
        (<= (- A B) 0)
        (new11 A B C)
        (new9 B C)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (>= D A)
        (<= (- B D) (- 1))
        (<= (- A B) 0)
        (new11 A B C)
        (new9 B C)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C false)
        (= C false)
        (= C false)
        (>= (- A B) 1)
        (<= (- B A) (- 1))
      )
      (new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (>= (- A B) 1)
        (<= B (- A 1))
      )
      (new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (>= (- A B) 1)
        (<= D (- A 1))
        (new9 B C)
      )
      (new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (>= (- A B) 1)
        (<= D (- A 1))
        (new10 A B C)
      )
      (new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (>= (- B D) 1)
        (>= (- A B) 1)
        (<= D (- A 1))
        (new9 B C)
        (new10 A B C)
      )
      (new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (>= (- A B) 1)
        (<= (- B D) (- 1))
        (<= D (- A 1))
        (new9 B C)
        (new10 A B C)
      )
      (new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (>= (- A B) 1)
        (>= D A)
        (new10 A B C)
      )
      (new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C true)
        (>= (- A B) 1)
        (>= D A)
        (new9 B C)
      )
      (new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= C false)
        (>= (- A B) 1)
        (>= D A)
        (<= (- B D) (- 1))
        (new10 A B C)
        (new9 B C)
      )
      (new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B false)
      (new9 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B true)
      (new9 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (new9 A B)
      )
      (new9 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (new9 A B)
      )
      (new9 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) )
    (=>
      (and
        (= B false)
        (>= (- A C) 1)
        (new9 A B)
        (new9 A B)
      )
      (new9 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) )
    (=>
      (and
        (= B false)
        (<= (- A C) (- 1))
        (new9 A B)
        (new9 A B)
      )
      (new9 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) )
    (=>
      (and
        (= C true)
        (= B false)
      )
      (diff_new4 A A B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D false)
        (= D false)
        (= D false)
        (= B false)
        (>= (- A C) 1)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D false)
        (= D false)
        (= D false)
        (= B false)
        (<= (- A C) (- 1))
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (<= A (- C 1))
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (<= A (- C 1))
        (new9 A D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (<= A (- C 1))
        (new10 C A D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (>= A C)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (>= A C)
        (new11 C A D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (>= A C)
        (new9 A D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (<= A (- C 1))
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) )
    (=>
      (and
        (= B true)
        (= B true)
        (<= D (- C 1))
        (new9 A B)
      )
      (diff_new4 A A B C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B true)
        (<= E (- C 1))
        (new15 C A D)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (>= A C)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B true)
        (>= E C)
        (diff_new4 A A B C D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B true)
        (>= E C)
        (new9 A D)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B true)
        (>= (- A E) 1)
        (>= E C)
        (diff_new4 A A B C D)
        (new9 A D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B true)
        (>= E C)
        (<= (- A E) (- 1))
        (diff_new4 A A B C D)
        (new9 A D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (<= A (- C 1))
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B true)
        (<= E (- C 1))
        (new9 A D)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B true)
        (<= E (- C 1))
        (diff_new4 A A B C D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B true)
        (>= (- A E) 1)
        (<= E (- C 1))
        (diff_new4 A A B C D)
        (new9 A D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= B true)
        (<= (- A E) (- 1))
        (<= E (- C 1))
        (diff_new4 A A B C D)
        (new9 A D)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (= B true)
        (>= A C)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B true)
        (>= E C)
        (new15 C A D)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) )
    (=>
      (and
        (= B true)
        (= B true)
        (>= D C)
        (new9 A B)
      )
      (diff_new4 A A B C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B false)
        (>= (- A E) 1)
        (<= E (- C 1))
        (diff_new4 A A B C D)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) )
    (=>
      (and
        (= B false)
        (= B false)
        (>= (- A D) 1)
        (>= (- A D) 1)
        (<= D (- C 1))
        (diff_new4 A A B C B)
        (new9 A B)
      )
      (diff_new4 A A B C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B false)
        (>= (- A E) 1)
        (>= E C)
        (diff_new4 A A B C D)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) )
    (=>
      (and
        (= B false)
        (= B false)
        (>= (- A D) 1)
        (>= (- A D) 1)
        (>= D C)
        (diff_new4 A A B C B)
        (new9 A B)
      )
      (diff_new4 A A B C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B false)
        (<= (- A E) (- 1))
        (<= E (- C 1))
        (diff_new4 A A B C D)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) )
    (=>
      (and
        (= B false)
        (= B false)
        (<= (- A D) (- 1))
        (<= (- A D) (- 1))
        (<= D (- C 1))
        (diff_new4 A A B C B)
        (new9 A B)
      )
      (diff_new4 A A B C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= D true)
        (= B false)
        (>= E C)
        (<= (- A E) (- 1))
        (diff_new4 A A B C D)
        (new9 A B)
      )
      (diff_new4 A A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) )
    (=>
      (and
        (= B false)
        (= B false)
        (>= D C)
        (<= (- A D) (- 1))
        (<= (- A D) (- 1))
        (diff_new4 A A B C B)
        (new9 A B)
      )
      (diff_new4 A A B C B)
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
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (diff_new54 A C D E B)
        (new2 D D E)
      )
      (new2 A A B)
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
      (new1 A B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) )
    (=>
      (and
        (= B true)
        (new2 A A C)
      )
      (new1 A B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Int) )
    (=>
      (and
        (= B true)
        (diff_new4 A D E F C)
        (new1 A B A E)
      )
      (new1 A B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Int) (F Bool) )
    (=>
      (and
        (= B false)
        (>= (- D A) 1)
        (diff_new4 A E F D C)
        (new1 A B A F)
      )
      (new1 A B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Int) (F Bool) )
    (=>
      (and
        (= B false)
        (<= (- D A) (- 1))
        (diff_new4 A E F D C)
        (new1 A B A F)
      )
      (new1 A B A C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) )
    (=>
      (and
        (not (= A B))
        (new1 C A C B)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
