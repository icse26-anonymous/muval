; Automatically generated by map2smt

(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))



(declare-fun leq (Int Int Bool) Bool)
(declare-fun mem (Int listOfInt Bool) Bool)
(declare-fun ins1 (Int listOfInt listOfInt) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B false)
      (mem A nil-listOfInt B)
    )
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C Bool) )
    (=>
      (= C true)
      (mem A (cons-listOfInt A B) C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Bool) )
    (=>
      (and
        (= D true)
        (= D true)
        (mem A C D)
      )
      (mem A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (= D false)
        (= D false)
        (>= (- B A) 1)
        (mem A C D)
      )
      (mem A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (= D false)
        (= D false)
        (<= (- B A) (- 1))
        (mem A C D)
      )
      (mem A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) )
    (ins1 A nil-listOfInt (cons-listOfInt A nil-listOfInt))
  )
)
(assert
  (forall ( (A Int) (B listOfInt) )
    (ins1 A (cons-listOfInt A B) (cons-listOfInt A B))
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D listOfInt) )
    (=>
      (and
        (>= (- B A) 1)
        (ins1 A C D)
      )
      (ins1 A (cons-listOfInt B C) (cons-listOfInt B D))
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D listOfInt) )
    (=>
      (and
        (<= (- B A) (- 1))
        (ins1 A C D)
      )
      (ins1 A (cons-listOfInt B C) (cons-listOfInt B D))
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C listOfInt) (D listOfInt) )
    (=>
      (and
        (= A false)
        (ins1 B C D)
        (mem B D A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
